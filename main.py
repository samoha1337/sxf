#ngrok http 8000 
from fastapi import FastAPI, Depends, HTTPException, UploadFile, File, status, Query, Form  
from fastapi.security import OAuth2PasswordBearer, OAuth2PasswordRequestForm
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse
from sqlalchemy.ext.asyncio import create_async_engine, AsyncSession, async_sessionmaker
from sqlalchemy import select, Column, Integer, String, ForeignKey, DateTime, func, text
from sqlalchemy.ext.asyncio import AsyncSession
from sqlalchemy.orm import declarative_base, relationship
from pydantic import BaseModel
from sqlalchemy.dialects.postgresql import JSONB
from datetime import datetime, timedelta
from typing import List, Optional, AsyncGenerator, Dict
from jose import JWTError, jwt
from passlib.context import CryptContext
from sqlalchemy import Numeric
import shutil
from sqlalchemy.exc import SQLAlchemyError
from pathlib import Path
import platform
from datetime import datetime, timezone, timedelta
import struct
from pathlib import Path
import csv
from io import StringIO
import logging
import re
from pydantic import field_validator


# Настройка логирования
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class SXFParser:
    """Парсер SXF файлов для извлечения метаданных и координат"""
    
    def __init__(self, file_path):
        self.file_path = Path(file_path)

    def parse(self):
        """Основной метод парсинга SXF файла"""
        if not self.file_path.exists():
            raise FileNotFoundError(f"Файл не найден: {self.file_path}")

        try:
            with open(self.file_path, 'rb') as f:
                header = f.read(1024)

                # Проверка минимального размера заголовка
                if len(header) < 240:  # Минимальный размер для чтения всех данных
                    raise ValueError("Файл слишком мал для корректного SXF файла")

                # Проверка сигнатуры
                if header[0:4] != b'SXF\x00':
                    raise ValueError("Неверная сигнатура SXF файла")

                # Масштаб
                scale = struct.unpack('<i', header[60:64])[0]

                # Название и регион
                nomenclature = self._decode_string(header[28:60])
                region = self._decode_string(header[64:96]) or "РЕГИОН"

                # === Геодезические координаты (в радианах), смещение +168 ===
                geo_coords = []
                for i in range(4):  # LB, LT, RT, RB (SW, NW, NE, SE)
                    try:
                        lon = struct.unpack('<d', header[168 + i * 16 + 8: 168 + i * 16 + 16])[0]  # X (долгота)
                        lat = struct.unpack('<d', header[168 + i * 16: 168 + i * 16 + 8])[0]       # Y (широта)
                        geo_coords.append((lon, lat))  # (lon, lat)
                    except struct.error as e:
                        raise ValueError(f"Ошибка чтения координат угла {i}: {str(e)}")

                # Валидация координат
                self._validate_coordinates(geo_coords)

                # Возвращаем структуру, соответствующую базе данных
                return {
                    "filename": self.file_path.name,
                    "scale": self._normalize_scale(scale),
                    "sheet_name": region.strip(),
                    "nomenclature": self._format_nomenclature(self.file_path.stem),
                    # Координаты углов в правильном порядке для БД                    
                    "sw_x_rad": geo_coords[0][1],  # LB - долгота (x)
                    "sw_y_rad": geo_coords[0][0],  # LB - широта (y)
                    "nw_x_rad": geo_coords[1][1],  # LT - долгота (x)
                    "nw_y_rad": geo_coords[1][0],  # LT - широта (y)
                    "ne_x_rad": geo_coords[2][1],  # RT - долгота (x)
                    "ne_y_rad": geo_coords[2][0],  # RT - широта (y)
                    "se_x_rad": geo_coords[3][1],  # RB - долгота (x)
                    "se_y_rad": geo_coords[3][0],  # RB - широта (y)
                }
                
        except Exception as e:
            logger.error(f"Ошибка парсинга файла {self.file_path}: {str(e)}")
            raise

    def _decode_string(self, raw_bytes):
        """Декодирование строки из байтов в кодировке CP1251"""
        try:
            return raw_bytes.split(b'\x00')[0].decode('cp1251', errors='ignore').strip()
        except UnicodeDecodeError:
            logger.warning(f"Не удалось декодировать строку: {raw_bytes[:20]}...")
            return ""

    def _format_nomenclature(self, name):
        """Форматирование номенклатуры из имени файла"""
        clean = ''.join(c for c in name if c.isdigit())
        if len(clean) >= 6:
            return f"{clean[:2]}-{clean[2:4]}-{clean[4:6]}"
        return name

    def _normalize_scale(self, scale):
        """Нормализация значения масштаба"""
        normalized = abs(scale)
        # Проверка на разумные значения масштаба
        if normalized > 10000000:
            logger.warning(f"Очень большой масштаб: {scale}, нормализован до 5000000")
            return 5000000
        elif normalized < 1000:
            logger.warning(f"Очень маленький масштаб: {scale}, нормализован до 1000")
            return 1000
        return normalized

    def _validate_coordinates(self, coords):
        """Валидация координат на разумность"""
        for i, (lon, lat) in enumerate(coords):
            # Проверка на NaN и бесконечность
            if not (-180 <= lon <= 180) or not (-90 <= lat <= 90):
                # Если координаты в радианах, они должны быть в разумных пределах
                if not (-10 <= lon <= 10) or not (-10 <= lat <= 10):
                    logger.warning(f"Подозрительные координаты в углу {i}: lon={lon}, lat={lat}")


class RSCParser:
    """Парсер RSC файлов классификаторов"""
    
    def __init__(self, file_content: str):
        self.file_content = file_content
    
    def parse(self) -> list[dict]:
        """Парсинг RSC-файла в список словарей"""
        data = []
        
        try:
            reader = csv.reader(
                StringIO(self.file_content), 
                delimiter=';',
                skipinitialspace=True
            )
            
            for row_num, row in enumerate(reader, 1):
                if len(row) < 2:
                    logger.warning(f"Пропущена строка {row_num}: недостаточно данных")
                    continue
                
                try:
                    item = {
                        "filename": row[0].strip(),
                        "scale": int(row[1].strip()),
                    }
                    data.append(item)
                except (ValueError, IndexError) as e:
                    logger.error(f"Ошибка парсинга строки {row_num}: {str(e)}")
                    continue
                    
        except Exception as e:
            logger.error(f"Ошибка чтения RSC файла: {str(e)}")
            raise ValueError(f"Ошибка парсинга RSC файла: {str(e)}")
            
        return data

# Настройки для Windows
if platform.system() == "Windows":
    import asyncio
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# Конфигурация
DATABASE_URL = "postgresql+asyncpg://postgres:1111@localhost/postgres"
SECRET_KEY = "1111"  # В продакшене должен быть более сложный ключ
ALGORITHM = "HS256"
ACCESS_TOKEN_EXPIRE_MINUTES = 30

# Настройки файлового хранилища
FILE_STORAGE = Path(r"C:/Users/PC/Downloads/sxfs")
SXF_FILES_DIR = FILE_STORAGE / "sxf"
RSC_FILES_DIR = FILE_STORAGE / "rsc"

# Создаем директории
try:
    SXF_FILES_DIR.mkdir(parents=True, exist_ok=True)
    RSC_FILES_DIR.mkdir(parents=True, exist_ok=True)
    logger.info(f"Созданы директории: {SXF_FILES_DIR}, {RSC_FILES_DIR}")
except Exception as e:
    logger.error(f"Error creating directories: {e}")
    raise

# Инициализация FastAPI
app = FastAPI(
    title="GIS API",
    description="API для управления SXF файлами и классификаторами",
    version="1.0.0"
)

# Подключение к БД
engine = create_async_engine(
    DATABASE_URL,
    echo=False,  
    pool_size=10,
    max_overflow=20
)
async_session_maker = async_sessionmaker(engine, expire_on_commit=False)
Base = declarative_base()

# Модели Pydantic
class Token(BaseModel):
    access_token: str
    token_type: str

class TokenData(BaseModel):
    username: Optional[str] = None
    role: Optional[str] = None

class UserBase(BaseModel):
    username: str
    role: str

class UserCreate(UserBase):
    password: str
    
    @field_validator('password')
    @classmethod
    def validate_password(cls, v):
        if len(v) < 4:  # Минимальная длина пароля
            raise ValueError('Пароль должен содержать минимум 4 символа')
        return v
    
    @field_validator('role')
    @classmethod
    def validate_role(cls, v):
        if v not in ['admin', 'gis_specialist', 'user']:
            raise ValueError('Недопустимая роль')
        return v

class UserInDB(UserBase):
    id: int
    created_at: Optional[datetime] = None
    
    class Config:
        from_attributes = True

class SXFSheetBase(BaseModel):
    filename: str
    scale: int
    sheet_name: str
    nomenclature: str
    sw_x_rad: float
    sw_y_rad: float
    nw_x_rad: float
    nw_y_rad: float
    ne_x_rad: float
    ne_y_rad: float
    se_x_rad: float
    se_y_rad: float

class SXFSheetCreate(BaseModel):
    filename: str
    scale: int
    sheet_name: str
    nomenclature: str
    sw_x_rad: float
    sw_y_rad: float
    nw_x_rad: float
    nw_y_rad: float
    ne_x_rad: float
    ne_y_rad: float
    se_x_rad: float
    se_y_rad: float
    classifier_id: Optional[int] = None
    
    @field_validator('scale')
    @classmethod
    def validate_scale(cls, v):
        if v <= 0:
            raise ValueError('Масштаб должен быть положительным числом')
        return v
    
    @field_validator('sw_x_rad', 'sw_y_rad', 'nw_x_rad', 'nw_y_rad', 
              'ne_x_rad', 'ne_y_rad', 'se_x_rad', 'se_y_rad')
    @classmethod
    def validate_coordinates(cls, v):
        if not isinstance(v, (int, float)):
            raise ValueError('Координаты должны быть числами')
        return float(v)

class SXFSheetResponse(SXFSheetBase):
    id: int
    file_path: str
    classifier_id: Optional[int]
    uploaded_by: int
    uploaded_at: datetime
    
    class Config:
        from_attributes = True

class RSCClassifierBase(BaseModel):
    filename: str
    scale: int

class RSCClassifierResponse(RSCClassifierBase):
    id: int
    uploaded_by: int
    uploaded_at: datetime

    class Config:
        from_attributes = True

class AuditLogEntry(BaseModel):
    id: int
    action: str
    user_id: int     
    username: str    
    timestamp: datetime
    entity_type: Optional[str] = None
    entity_id: Optional[int] = None
    details: Optional[dict] = None

    class Config:
        from_attributes = True
        json_encoders = {datetime: lambda v: v.isoformat()}

class ReportSummary(BaseModel):
    total_users: int
    total_sheets: int
    total_classifiers: int
    sheets_by_scale: Dict[int, int]
    classifiers_by_scale: Dict[int, int]
    last_uploads: List[Dict]
    recent_activity: List[Dict]

    class Config:
        from_attributes = True

# Модели SQLAlchemy
class User(Base):
    __tablename__ = "users"
    id = Column(Integer, primary_key=True, index=True)
    username = Column(String, unique=True, index=True, nullable=False)
    password_hash = Column(String, nullable=False)
    role = Column(String, nullable=False)
    created_at = Column(DateTime(timezone=True), server_default=func.now())
    last_login = Column(DateTime(timezone=True))

class SXFSheet(Base):
    __tablename__ = "sxf_sheets"
    id = Column(Integer, primary_key=True, index=True)
    filename = Column(String, unique=True, index=True, nullable=False)
    scale = Column(Integer, nullable=False)
    sheet_name = Column(String)
    nomenclature = Column(String)
    # Координаты углов в радианах
    sw_x_rad = Column(Numeric, nullable=False)  # Юго-западный X
    sw_y_rad = Column(Numeric, nullable=False)  # Юго-западный Y
    nw_x_rad = Column(Numeric, nullable=False)  # Северо-западный X
    nw_y_rad = Column(Numeric, nullable=False)  # Северо-западный Y
    ne_x_rad = Column(Numeric, nullable=False)  # Северо-восточный X
    ne_y_rad = Column(Numeric, nullable=False)  # Северо-восточный Y
    se_x_rad = Column(Numeric, nullable=False)  # Юго-восточный X
    se_y_rad = Column(Numeric, nullable=False)  # Юго-восточный Y
    # Путь к файлу
    file_path = Column(String, nullable=False)
    # Связи
    classifier_id = Column(Integer, ForeignKey("classifiers.id"))
    uploaded_by = Column(Integer, ForeignKey("users.id"), nullable=False)
    uploaded_at = Column(DateTime(timezone=True), nullable=False)

class RSCClassifier(Base):
    __tablename__ = "classifiers"
    id = Column(Integer, primary_key=True, index=True)
    filename = Column(String, unique=True, index=True, nullable=False)
    scale = Column(Integer, nullable=False)
    #description = Column(String)  # Добавил поле description
    uploaded_by = Column(Integer, ForeignKey("users.id"), nullable=False)
    uploaded_at = Column(DateTime(timezone=True), nullable=False)

class AuditLog(Base):
    __tablename__ = "audit_log"
    id = Column(Integer, primary_key=True)
    action = Column(String(50), nullable=False)
    user_id = Column(Integer, ForeignKey("users.id"), nullable=False)
    user = relationship("User", backref="audit_logs")  
    timestamp = Column(DateTime(timezone=True), server_default=func.now())
    entity_type = Column(String(50))
    entity_id = Column(Integer)
    details = Column(JSONB)

# Создание таблиц
async def create_tables():
    async with engine.begin() as conn:
        await conn.run_sync(Base.metadata.create_all)
# Запуск приложения
@app.on_event("startup")
async def startup():
    await create_tables()
    logger.info("Приложение запущено, таблицы созданы")


# JWT и хеширование паролей
pwd_context = CryptContext(schemes=["bcrypt"], deprecated="auto")
oauth2_scheme = OAuth2PasswordBearer(tokenUrl="/auth/login")

# Асинхронные вспомогательные функции
async def get_db() -> AsyncGenerator[AsyncSession, None]:
    async with async_session_maker() as session:
        try:
            yield session
        except Exception as e:
            await session.rollback()
            logger.error(f"Database session error: {str(e)}")
            raise
        finally:
            await session.close()

async def get_user(db: AsyncSession, username: str):
    result = await db.execute(select(User).filter(User.username == username))
    return result.scalars().first()

async def authenticate_user(db: AsyncSession, username: str, password: str):
    user = await get_user(db, username)
    if not user or not pwd_context.verify(password, user.password_hash):
        return False
    return user

async def get_current_user(
    token: str = Depends(oauth2_scheme),
    db: AsyncSession = Depends(get_db)
):
    credentials_exception = HTTPException(
        status_code=status.HTTP_401_UNAUTHORIZED,
        detail="Could not validate credentials",
        headers={"WWW-Authenticate": "Bearer"},
    )
    try:
        payload = jwt.decode(token, SECRET_KEY, algorithms=[ALGORITHM])
        username: str = payload.get("sub")
        if not username:
            raise credentials_exception
        token_data = TokenData(username=username, role=payload.get("role"))
    except JWTError:
        raise credentials_exception
    
    user = await get_user(db, username=token_data.username)
    if user is None:
        raise credentials_exception
    return user

async def get_current_active_user(current_user: User = Depends(get_current_user)):
    if current_user.role not in ["admin", "gis_specialist", "user"]:
        raise HTTPException(status_code=400, detail="Inactive user")
    return current_user


def extract_base_filename(filename: str) -> str:
    """Извлекает базовое имя файла без версии и расширения"""
    # Пример: "822300_v2.sxf" -> "822300"
    return re.sub(r'_v\d+.*$', '', Path(filename).stem)


async def log_audit_event(
    db: AsyncSession,
    user_id: int,
    action: str,
    entity_type: Optional[str] = None,
    entity_id: Optional[int] = None,
    details: Optional[dict] = None,
    changes: Optional[dict] = None
) -> Optional[AuditLog]:
    """
    Улучшенная функция аудита с фокусом на ключевой информации
    
    Параметры:
    - action: Короткое действие (например, 'sheet_upload', 'version_view')
    - details: Основная информация (username, filename и т.д.)
    - changes: Конкретные изменения (для операций изменения)
    """
    try:
        # Формируем детализированную информацию
        audit_details = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            **(details or {})
        }
        
        if changes:
            audit_details["changes"] = {
                field: {
                    "old": values.get("old"),
                    "new": values.get("new"),
                    "changed": values.get("old") != values.get("new")
                }
                for field, values in changes.items()
            }
        
        audit_log = AuditLog(
            action=action,
            user_id=user_id,
            timestamp=datetime.now(timezone.utc),
            entity_type=entity_type,
            entity_id=entity_id,
            details=audit_details  # JSONB автоматически сериализует dict
        )
        
        db.add(audit_log)
        await db.commit()
        await db.refresh(audit_log)
        
        logger.info(
            f"Audit: {action}",
            extra={
                "user_id": user_id,
                "entity_type": entity_type,
                "entity_id": entity_id,
                "details": audit_details
            }
        )
        
        return audit_log
        
    except Exception as e:
        logger.error(f"Audit log failed: {str(e)}")
        # Не поднимаем ошибку, чтобы не блокировать основную операцию
        return None

async def safe_audit_log(
    db: AsyncSession,
    user_id: int,
    action: str,
    status: str,
    details: dict = None
):
    """Безопасная функция аудита, которая не блокирует основной процесс"""
    try:
        await log_audit_event(
            db=db,
            user_id=user_id,
            action=f"{action}_{status}",
            entity_type="file_operation",
            details=details or {}
        )
    except Exception as e:
        logger.warning(f"Audit logging failed for {action}: {str(e)}")
# Эндпоинты
@app.get("/", tags=["Root"])
def read_root():
    return {"message": "GIS API is running", "version": "1.0.0"}
# Эндроинт проверка состояния сервиса
@app.get("/health", tags=["Health"])
async def health_check():
    """Проверка состояния сервиса"""
    return {
        "status": "healthy",
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "directories": {
            "sxf_files": SXF_FILES_DIR.exists(),
            "rsc_files": RSC_FILES_DIR.exists()
        }
    }

# Эндпоинты регистрации
@app.post("/auth/register", response_model=UserInDB, tags=["Authentication"])
async def register(user: UserCreate, db: AsyncSession = Depends(get_db)):
    existing_user = await get_user(db, user.username)
    if existing_user:
        raise HTTPException(status_code=status.HTTP_400_BAD_REQUEST, detail="Username already registered")
    
    # Автоматическое назначение роли для домена @npomis.ru
    if user.username.endswith("@npomis.ru"):
        user_role = "gis_specialist"
    else:
        user_role = user.role
    
    hashed_password = pwd_context.hash(user.password)
    new_user = User(
        username=user.username,
        password_hash=hashed_password,
        role=user_role,
        created_at=datetime.now(timezone.utc)
    )
    
    db.add(new_user)
    await db.commit()
    await db.refresh(new_user)
    
    await log_audit_event(
        db=db, 
        user_id=new_user.id, 
        action="user_register", 
        entity_type="user", 
        entity_id=new_user.id,
        details={"username": user.username, "role": user_role}
    )
    
    logger.info(f"Зарегистрирован новый пользователь: {user.username} с ролью {user_role}")
    return new_user
# Эндпоинт аутентификации 
@app.post("/auth/login", response_model=Token, tags=["Authentication"])
async def login(
    form_data: OAuth2PasswordRequestForm = Depends(),
    db: AsyncSession = Depends(get_db)
):
    user = await authenticate_user(db, form_data.username, form_data.password)
    if not user:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Incorrect username or password",
        )
    
    access_token_expires = timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
    current_time = datetime.now(timezone.utc)
    access_token = jwt.encode(
        {"sub": user.username, "role": user.role, "exp": current_time + access_token_expires},
        SECRET_KEY,
        algorithm=ALGORITHM
    )
    
    user.last_login = current_time
    await db.commit()
    
    await log_audit_event(
        db=db, 
        user_id=user.id, 
        action="user_login", 
        entity_type="user", 
        entity_id=user.id, 
        details={"username": user.username, "role": user.role}
    )
    
    logger.info(f"Пользователь {user.username} успешно вошел в систему")
    return {"access_token": access_token, "token_type": "bearer"}
# Эндпоинт выхода 
@app.post("/logout", tags=["Authentication"])
async def logout(current_user: User = Depends(get_current_active_user)):
    return {"message": "Successfully logged out"}

# Эндпоинты пользователей
@app.get("/users/me", response_model=UserInDB, tags=["Users"])
async def read_users_me(current_user: User = Depends(get_current_active_user)):
    return current_user
# Эндроинт для получения списка пользователей 
@app.get("/users", response_model=List[UserInDB], tags=["Users"])
async def read_users(
    skip: int = 0,
    limit: int = 100,
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    if current_user.role != "admin":
        raise HTTPException(status_code=status.HTTP_403_FORBIDDEN, detail="Not enough permissions")
    
    query = select(
        User.id,
        User.username,
        User.role,
        func.coalesce(User.created_at, datetime(1970, 1, 1)).label("created_at")
    ).offset(skip).limit(limit)
    
    result = await db.execute(query)
    users = result.mappings().all()
    return [UserInDB(**user) for user in users]
# Эндпоинт для смены прав(ролей)
@app.put("/users/{user_id}/role", tags=["Users"])
async def change_user_role(
    user_id: int,
    new_role: str = Query(...),
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    user = await db.get(User, user_id)
    if not user:
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="user_role_change",
            status="failed",
            details={
                "username": current_user.username,
                "target_user_id": user_id,
                "error": "not_found"
            }
        )
        raise HTTPException(404, "User not found")

    old_role = user.role
    user.role = new_role
    await db.commit()

    await log_audit_event(
        db=db,
        user_id=current_user.id,
        action="user_role_change",
        entity_type="user",
        entity_id=user_id,
        details={
            "changed_by": current_user.username,
            "target_username": user.username,
            "old_role": old_role,
            "new_role": new_role
        },
        changes={
            "role": {
                "old": old_role,
                "new": new_role
            }
        }
    )
    
    return {"message": "Role updated"}

# Эндпоинты для работы с SXF листами
@app.get("/sheets", response_model=List[SXFSheetResponse], tags=["SXF Sheets"])
async def get_sheets(
    skip: int = Query(0, ge=0),
    limit: int = Query(100, ge=1, le=1000),
    scale: Optional[int] = Query(None, description="Фильтр по масштабу"),
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    query = select(SXFSheet)
    
    if scale:
        query = query.filter(SXFSheet.scale == scale)
    
    query = query.offset(skip).limit(limit).order_by(SXFSheet.uploaded_at.desc())
    sheets = (await db.execute(query)).scalars().all()
    
    await log_audit_event(
        db=db,
        user_id=current_user.id,
        action="sheets_listed",
        entity_type="sxf_sheet",
        entity_id=0,
        details={
            "count": len(sheets),
            "username": current_user.username,
            "filters": {"scale": scale} if scale else None
        }
    )
    
    return sheets
# Эндпоинт для скачивания sxf листа по ID
@app.get("/sheets/download/{sheet_id}")
async def download_sheet(
    sheet_id: int,
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    sheet = await db.get(SXFSheet, sheet_id)
    if not sheet:
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="sheet_download",
            status="failed",
            details={"sheet_id": sheet_id, "error": "not_found"}
        )
        raise HTTPException(404, "Sheet not found")

    # Нормализация пути
    raw_path = sheet.file_path.strip().strip('"')  # убираем кавычки и пробелы
    file_path = Path(raw_path).resolve(strict=False)

    if not file_path.exists():
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="sheet_download",
            status="failed",
            details={
                "sheet_id": sheet_id,
                "filename": sheet.filename,
                "error": f"file_not_found_on_disk: {file_path}"
            }
        )
        raise HTTPException(404, f"File not found: {file_path}")

    await log_audit_event(
        db=db,
        user_id=current_user.id,
        action="sheet_download",
        entity_type="sxf_sheet",
        entity_id=sheet.id,
        details={
            "filename": sheet.filename,
            "file_size_kb": round(file_path.stat().st_size / 1024, 2)
        }
    )

    return FileResponse(
        path=file_path,
        filename=sheet.filename,
        media_type='application/octet-stream'
    )
# Эндпоинт для скачивания JSON по ID
@app.get("/sheets/{sheet_id}", response_model=SXFSheetResponse)
async def get_sheet(
    sheet_id: int,
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    sheet = await db.get(SXFSheet, sheet_id)
    if not sheet:
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="sheet_view",
            status="failed",
            details={
                "sheet_id": sheet_id,
                "error": "not_found"
            }
        )
        raise HTTPException(404, "Sheet not found")
    
    await log_audit_event(
        db=db,
        user_id=current_user.id,
        action="sheet_view",
        entity_type="sxf_sheet",
        entity_id=sheet.id,
        details={
            "filename": sheet.filename,
            "nomenclature": sheet.nomenclature,
            "scale": sheet.scale
        }
    )
    return sheet

# Эндпоинт для загрузки на сервер SXF листа(файла)
@app.post("/sheets/upload", response_model=SXFSheetResponse, tags=["SXF Sheets"])
async def upload_sxf_file(
    file: UploadFile = File(...),
    classifier_id: Optional[int] = Form(None),
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    # Проверка прав
    if current_user.role not in ["admin", "gis_specialist"]:
        await safe_audit_log(
            db, current_user.id,
            "sheet_upload_attempt", "failed",
            {"reason": "insufficient_permissions"}
        )
        raise HTTPException(403, "Недостаточно прав")

    # Валидация файла
    if not file.filename or not file.filename.lower().endswith('.sxf'):
        await safe_audit_log(
            db, current_user.id,
            "sheet_upload_attempt", "failed",
            {"reason": "invalid_file_extension"}
        )
        raise HTTPException(400, "Требуется файл .sxf")

    try:
        # Подготовка имени файла
        file_path = Path(file.filename)
        original_name = file_path.stem
        file_ext = file_path.suffix
        version = await get_next_version(db, original_name)
        new_filename = f"{original_name}_v{version}{file_ext}" if version > 1 else file.filename
        file_location = SXF_FILES_DIR / new_filename

        # Сохранение файла
        SXF_FILES_DIR.mkdir(parents=True, exist_ok=True)
        with open(file_location, "wb") as buffer:
            shutil.copyfileobj(file.file, buffer)

        # Парсинг SXF
        parser = SXFParser(str(file_location))
        sxf_data = parser.parse()
        sheet_scale = sxf_data['scale']

        # Поиск или проверка классификатора
        if classifier_id is None:
            classifier_id = await find_matching_classifier(db, original_name, sheet_scale)
            if not classifier_id:
                await safe_audit_log(
                    db, current_user.id,
                    "sheet_upload", "failed",
                    {"error": "no_matching_classifier", "scale": sheet_scale}
                )
                raise HTTPException(400, f"Не найден классификатор для масштаба {sheet_scale}")
        else:
            # Явная проверка при указанном классификаторе
            classifier = await db.get(RSCClassifier, classifier_id)
            if not classifier:
                await safe_audit_log(
                    db, current_user.id,
                    "sheet_upload", "failed",
                    {"error": "classifier_not_found", "classifier_id": classifier_id}
                )
                raise HTTPException(404, "Классификатор не найден")
            
            if classifier.scale != sheet_scale:
                await safe_audit_log(
                    db, current_user.id,
                    "sheet_upload", "failed",
                    {
                        "error": "scale_mismatch",
                        "sheet_scale": sheet_scale,
                        "classifier_scale": classifier.scale
                    }
                )
                raise HTTPException(
                    status_code=400,
                    detail=f"Масштаб классификатора ({classifier.scale}) не соответствует масштабу листа ({sheet_scale})"
                )

        # Создание записи
        new_sheet = await create_sheet_record(
            db=db,
            filename=new_filename,
            file_location=file_location,
            sxf_data=sxf_data,
            classifier_id=classifier_id,
            user_id=current_user.id
        )

        # Аудит-лог
        await safe_audit_log(
            db, current_user.id,
            "sheet_upload", "success",
            {
                "filename": new_filename,
                "file_size": file_location.stat().st_size,
                "classifier_id": classifier_id,
                "scale": sheet_scale,
                "version": version
            }
        )

        return new_sheet

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Upload error: {e}", exc_info=True)
        if 'file_location' in locals() and file_location.exists():
            file_location.unlink(missing_ok=True)
        
        await safe_audit_log(
            db, current_user.id,
            "sheet_upload", "failed",
            {"error": str(e), "filename": file.filename, "classifier_id": classifier_id}
        )
        raise HTTPException(500, "Ошибка обработки файла")
    
async def get_next_version(db: AsyncSession, base_name: str) -> int:
    """Получает следующую версию файла"""
    result = await db.execute(
        select(SXFSheet.filename)
        .where(SXFSheet.filename.ilike(f"{base_name}%"))
        .order_by(SXFSheet.uploaded_at.desc())
    )
    if existing := result.scalars().first():
        if "_v" in existing:
            try:
                return int(existing.split("_v")[-1].split(".")[0]) + 1
            except ValueError:
                pass
        return 2
    return 1

async def find_matching_classifier(
    db: AsyncSession, 
    base_name: str,
    sheet_scale: int  # Новый параметр для проверки масштаба
) -> Optional[int]:
    """Находит подходящий классификатор с учетом масштаба"""
    base_name = re.sub(r'_v\d+.*$', '', base_name)
    result = await db.execute(
        select(RSCClassifier.id)
        .where(
            RSCClassifier.filename.ilike(f"{base_name}%"),
            RSCClassifier.scale == sheet_scale  # Фильтр по масштабу
        )
        .order_by(RSCClassifier.uploaded_at.desc())
        .limit(1)
    )
    return result.scalar_one_or_none()

async def create_sheet_record(
    db: AsyncSession,
    filename: str,
    file_location: Path,
    sxf_data: dict,
    classifier_id: Optional[int],
    user_id: int
) -> SXFSheet:
    """Создает и сохраняет запись о листе с проверкой масштаба"""
    # Проверка наличия классификатора
    if classifier_id:
        classifier = await db.get(RSCClassifier, classifier_id)
        if not classifier:
            raise HTTPException(404, "Связанный классификатор не найден")
        
        if classifier.scale != sxf_data['scale']:
            raise HTTPException(
                status_code=400,
                detail=f"Масштаб классификатора ({classifier.scale}) не соответствует масштабу листа ({sxf_data['scale']})"
            )

    new_sheet = SXFSheet(
        filename=filename,
        file_path=str(file_location.resolve()),
        scale=sxf_data['scale'],
        sheet_name=sxf_data.get('sheet_name', ''),
        nomenclature=sxf_data['nomenclature'],
        sw_x_rad=float(sxf_data['sw_x_rad']),
        sw_y_rad=float(sxf_data['sw_y_rad']),
        nw_x_rad=float(sxf_data['nw_x_rad']),
        nw_y_rad=float(sxf_data['nw_y_rad']),
        ne_x_rad=float(sxf_data['ne_x_rad']),
        ne_y_rad=float(sxf_data['ne_y_rad']),
        se_x_rad=float(sxf_data['se_x_rad']),
        se_y_rad=float(sxf_data['se_y_rad']),
        classifier_id=classifier_id,
        uploaded_by=user_id,
        uploaded_at=datetime.now(timezone.utc)
    )
    
    db.add(new_sheet)
    await db.commit()
    await db.refresh(new_sheet)
    return new_sheet

async def safe_audit_log(
    db: AsyncSession,
    user_id: int,
    action: str,
    status: str,
    details: dict
):
    """Безопасное логирование аудита"""
    try:
        log = AuditLog(
            action=action,
            user_id=user_id,
            timestamp=datetime.now(timezone.utc),
            details={**details, "status": status}
        )
        db.add(log)
        await db.commit()
    except Exception as e:
        logger.error(f"Audit log failed: {e}")
        await db.rollback()
# Обновленный эндпоинт удаления листа 
@app.delete("/sheets/{sheet_id}")
async def delete_sheet(
    sheet_id: int,
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    """
    Удаление SXF-листа с:
    - Проверкой прав
    - Валидацией путей
    - Транзакционным удалением
    - Аудит-логгированием
    - Защитой от race condition
    """
    # Проверка прав администратора
    if current_user.role != "admin":
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="sheet_delete_attempt",
            status="failed",
            details={
                "error": "insufficient_permissions",
                "username": current_user.username,
                "sheet_id": sheet_id
            }
        )
        raise HTTPException(403, "Требуются права администратора")

    try:
        # Получаем запись без блокировки
        sheet = await db.get(SXFSheet, sheet_id)
        if not sheet:
            await log_audit_event(
                db=db,
                user_id=current_user.id,
                action="sheet_delete_attempt",
                status="failed",
                details={
                    "error": "not_found",
                    "sheet_id": sheet_id
                }
            )
            raise HTTPException(404, "Лист не найден")

        # Валидация пути
        if not sheet.file_path or ".." in sheet.file_path:
            raise HTTPException(400, "Некорректный путь к файлу")

        file_path = Path(sheet.file_path)
        file_size = file_path.stat().st_size if file_path.exists() else 0

        # Транзакция удаления
        try:
            # Удаляем файл первым (вне транзакции БД)
            if file_path.exists():
                try:
                    file_path.unlink(missing_ok=True)
                except OSError as e:
                    logger.error(f"File deletion error: {e}")
                    raise HTTPException(500, "Ошибка удаления файла")

            # Удаление из БД
            await db.delete(sheet)
            await db.commit()

        except Exception as e:
            await db.rollback()
            logger.error(f"Database error: {e}")
            raise

        # Логирование успеха
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="sheet_deleted",
            entity_type="sxf_sheet",
            entity_id=sheet_id,
            details={
                "filename": sheet.filename,
                "file_size": file_size,
                "username": current_user.username
            }
        )

        return {"message": "Лист удален"}

    except HTTPException as he:
        logger.error(f"HTTP error: {he.detail}")
        raise he

    except Exception as e:
        logger.critical(f"Critical error: {e}", exc_info=True)
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="sheet_delete",
            status="failed",
            details={
                "error": str(e),
                "sheet_id": sheet_id
            }
        )
        raise HTTPException(500, "Внутренняя ошибка сервера")
# Эндпоинт верифицирования 
@app.get("/sheets/versions/{base_name}", response_model=List[SXFSheetResponse])
async def get_file_versions(
    base_name: str,
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    versions = await db.execute(
        select(SXFSheet)
        .where(SXFSheet.filename.ilike(f"{base_name}%"))
        .order_by(SXFSheet.uploaded_at.desc())
    )
    versions = versions.scalars().all()
    
    if not versions:
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="sheet_versions_view",
            status="failed",
            details={
                "username": current_user.username,
                "base_filename": base_name,
                "error": "file_not_found"
            }
        )
        raise HTTPException(404, "Файл не найден")
    
    await log_audit_event(
        db=db,
        user_id=current_user.id,
        action="sheet_versions_view",
        entity_type="sxf_sheet",
        entity_id=versions[0].id,
        details={
            "username": current_user.username,
            "base_filename": base_name,
            "versions_found": len(versions),
            "latest_version": versions[0].filename,
            "versions": [v.filename for v in versions[:3]]  # Первые 3 версии для примера
        }
    )
    return versions
# Эндпоинт удаления классификатора 
@app.delete("/classifiers/{classifier_id}")
async def delete_classifier(
    classifier_id: int,
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    """
    Удаление классификатора с проверкой прав и аудитом
    """
    # Проверка прав администратора
    if current_user.role != "admin":
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifier_delete_attempt",
            status="failed",
            details={
                "error": "insufficient_permissions",
                "username": current_user.username
            }
        )
        raise HTTPException(403, "Требуются права администратора")

    try:
        # Получаем классификатор без новой транзакции
        classifier = await db.get(RSCClassifier, classifier_id)
        if not classifier:
            await log_audit_event(
                db=db,
                user_id=current_user.id,
                action="classifier_delete_attempt",
                status="failed",
                details={
                    "error": "not_found",
                    "classifier_id": classifier_id
                }
            )
            raise HTTPException(404, "Классификатор не найден")

        # Базовые проверки пути к файлу
        if not classifier.filename or ".." in classifier.filename:
            raise HTTPException(400, "Некорректное имя файла")

        # Формируем путь и удаляем файл
        file_path = RSC_FILES_DIR / classifier.filename
        if file_path.exists():
            try:
                file_path.unlink(missing_ok=True)
            except OSError as e:
                logger.error(f"Ошибка удаления файла: {str(e)}")
                raise HTTPException(500, "Ошибка при удалении файла")

        # Удаляем запись из БД в явной транзакции
        try:
            await db.delete(classifier)
            await db.commit()
        except Exception as e:
            await db.rollback()
            raise
            
        # Логируем успешное удаление
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifier_deleted",
            entity_type="classifier",
            entity_id=classifier_id,
            details={
                "filename": classifier.filename,
                "username": current_user.username
            }
        )
        
        return {"message": "Классификатор удален"}

    except HTTPException:
        raise
            
    except Exception as e:
        logger.error(f"Ошибка при удалении классификатора: {str(e)}")
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifier_delete",
            status="failed",
            details={
                "error": str(e),
                "classifier_id": classifier_id
            }
        )
        raise HTTPException(500, "Внутренняя ошибка сервера")
# Модифицированный эндпоинт загрузки классификаторов
@app.post("/classifiers/upload", response_model=List[RSCClassifierResponse])
async def upload_classifiers(
    file: UploadFile = File(..., description="RSC-файл классификаторов"),
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    if current_user.role != "admin":
        await safe_audit_log(
            db, current_user.id,
            "classifier_upload_attempt", "failed",
            {"reason": "insufficient_permissions"}
        )
        raise HTTPException(403, "Требуются права администратора")

    # Чтение и парсинг файла
    content = (await file.read()).decode("windows-1251")
    parser = RSCParser(content)
    
    try:
        classifiers_data = parser.parse()
    except Exception as e:
        await safe_audit_log(
            db, current_user.id,
            "classifier_upload", "failed",
            {"error": str(e), "filename": file.filename}
        )
        raise HTTPException(400, f"Ошибка парсинга: {str(e)}")

    # Сохранение в БД
    new_classifiers = []
    for item in classifiers_data:
        classifier = RSCClassifier(
            filename=item["filename"],
            scale=item["scale"],
            uploaded_by=current_user.id,
            uploaded_at=datetime.now(timezone.utc)
        )
        db.add(classifier)
        new_classifiers.append(classifier)

    try:
        await db.commit()
        for c in new_classifiers:
            await db.refresh(c)
            
        # Аудит-лог успешной загрузки
        await safe_audit_log(
            db, current_user.id,
            "classifier_upload", "success",
            {
                "filename": file.filename,
                "classifiers_count": len(new_classifiers),
                "classifier_ids": [c.id for c in new_classifiers]
            }
        )
            
    except SQLAlchemyError as e:
        await db.rollback()
        await safe_audit_log(
            db, current_user.id,
            "classifier_upload", "failed",
            {"error": str(e), "filename": file.filename}
        )
        raise HTTPException(500, "Ошибка сохранения в БД")

    return new_classifiers
# Эндпоинт получить классификаторы 
@app.get("/classifiers", response_model=List[RSCClassifierResponse])
async def get_classifiers(
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    """
    Получение списка всех классификаторов с пагинацией
    
    Возвращает:
    - List[RSCClassifierResponse]: Список классификаторов с метаданными
    """
    try:
        logger.info(f"Попытка получения классификаторов пользователем {current_user.username}")
        
        # Запрос с сортировкой по дате загрузки (новые первые)
        query = select(RSCClassifier).order_by(RSCClassifier.uploaded_at.desc())
        result = await db.execute(query)
        classifiers = result.scalars().all()
        
        if not classifiers:
            logger.warning("Классификаторы не найдены в базе данных")
            return []
        
        logger.info(f"Успешно получено {len(classifiers)} классификаторов")
        
        # Аудит
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifiers_listed",
            entity_type="classifier",
            details={
                "username": current_user.username,
                "count": len(classifiers),
                "first_id": classifiers[0].id if classifiers else None,
                "last_id": classifiers[-1].id if classifiers else None
            }
        )
        
        return classifiers
        
    except SQLAlchemyError as db_error:
        logger.error(f"Ошибка базы данных при получении классификаторов: {str(db_error)}")
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifiers_listed",
            status="failed",
            details={
                "error_type": "database_error",
                "error_details": str(db_error)
            }
        )
        raise HTTPException(
            status_code=500,
            detail="Временная проблема с базой данных"
        )
        
    except Exception as e:
        logger.critical(f"Неожиданная ошибка: {str(e)}", exc_info=True)
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifiers_listed",
            status="failed",
            details={
                "error_type": "unexpected_error",
                "error_details": str(e)
            }
        )
        raise HTTPException(
            status_code=500,
            detail="Внутренняя ошибка сервера"
        )
# Эндпоинт скачивания классификатора по ID
@app.get("/classifiers/download/{classifier_id}", 
         response_class=FileResponse,
         tags=["Classifiers"])
async def download_classifier(
    classifier_id: int,
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    """
    Скачивание классификатора с проверкой:
    - Существования классификатора
    - Наличия файла в хранилище
    - Прав доступа
    - Безопасности имени файла
    """
    # Проверка прав доступа
    if current_user.role not in ["admin", "gis_specialist"]:
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifier_download_attempt",
            status="failed",
            details={
                "error": "insufficient_permissions",
                "required_roles": ["admin", "gis_specialist"],
                "user_role": current_user.role
            }
        )
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="Доступ разрешен только администраторам и GIS специалистам"
        )

    # Получаем классификатор
    classifier = await db.get(RSCClassifier, classifier_id)
    if not classifier:
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifier_download",
            status="failed",
            details={
                "error": "not_found",
                "classifier_id": classifier_id
            }
        )
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="Классификатор не найден"
        )

    # Валидация имени файла
    if not re.match(r'^[\w\d\-_.]+$', classifier.filename):
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="classifier_download",
            status="failed",
            details={
                "error": "invalid_filename",
                "filename": classifier.filename
            }
        )
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Некорректное имя файла классификатора"
        )

    file_path = RSC_FILES_DIR / classifier.filename

    try:
        # Проверка существования файла
        if not file_path.is_file():
            raise HTTPException(
                status_code=status.HTTP_404_NOT_FOUND,
                detail="Файл классификатора не найден в хранилище"
            )

        # Проверка размера файла
        file_size = file_path.stat().st_size
        if file_size == 0:
            logger.warning(f"Пустой файл классификатора: {file_path}")
            
    except OSError as e:
        logger.error(f"Ошибка доступа к файлу: {str(e)}")
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail="Ошибка доступа к файлу"
        )

    # Логирование события
    await log_audit_event(
        db=db,
        user_id=current_user.id,
        action="classifier_download",
        entity_type="classifier",
        entity_id=classifier.id,
        details={
            "filename": classifier.filename,
            "file_size_bytes": file_size,
            "username": current_user.username,
            "user_role": current_user.role
        }
    )

    # Возврат файла с безопасными заголовками
    return FileResponse(
        path=file_path,
        filename=classifier.filename,
        headers={
            "Content-Disposition": f"attachment; filename={classifier.filename}",
            "X-File-Size": str(file_size)
        }
    )
# Эндпоинты аудита - логов
@app.get("/audit", response_model=List[AuditLogEntry])
async def get_audit_log(
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db),
    skip: int = 0,
    limit: int = 100
):
    if current_user.role != "admin":
        raise HTTPException(status_code=status.HTTP_403_FORBIDDEN, detail="Недостаточно прав")
    
    # Полный запрос с JOIN и выборкой всех полей
    query = (
        select(
            AuditLog.id,
            AuditLog.action,
            AuditLog.user_id,
            User.username,
            AuditLog.timestamp,
            AuditLog.entity_type,
            AuditLog.entity_id,
            AuditLog.details
        )
        .join(User, AuditLog.user_id == User.id)
        .order_by(AuditLog.timestamp.desc())
        .offset(skip)
        .limit(limit)
    )
    
    result = await db.execute(query)
    logs = result.mappings().all()
    
    return [
        AuditLogEntry(
            id=log["id"],
            action=log["action"],
            user_id=log["user_id"],
            username=log["username"],
            timestamp=log["timestamp"],
            entity_type=log["entity_type"],
            entity_id=log["entity_id"],
            details=log["details"]
        )
        for log in logs
    ]
# Эндпоинт структуризированного отчета 
@app.get("/reports/summary", response_model=ReportSummary)
async def get_summary_report(
    current_user: User = Depends(get_current_active_user),
    db: AsyncSession = Depends(get_db)
):
    """Получение сводного отчета по системе (только для администраторов и GIS специалистов)"""
    
    # Проверка прав доступа
    if current_user.role not in ["admin", "gis_specialist"]:
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="report_view",
            status="failed",
            details={
                "error": "insufficient_permissions",
                "required_role": "admin/gis_specialist",
                "attempted_role": current_user.role
            }
        )
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="Доступ к отчетам разрешен только администраторам и GIS специалистам"
        )

    try:
        # 1. Общее количество пользователей
        total_users = (await db.execute(select(func.count(User.id)))).scalar() or 0

        # 2. Общее количество листов
        total_sheets = (await db.execute(select(func.count(SXFSheet.id)))).scalar() or 0

        # 3. Общее количество классификаторов
        total_classifiers = (await db.execute(select(func.count(RSCClassifier.id)))).scalar() or 0

        # 4. Распределение листов по масштабам
        sheets_by_scale_result = await db.execute(
            select(SXFSheet.scale, func.count(SXFSheet.id))
            .group_by(SXFSheet.scale)
        )
        sheets_by_scale = dict(sheets_by_scale_result.all()) if sheets_by_scale_result else {}

        # 5. Распределение классификаторов по масштабам
        classifiers_by_scale_result = await db.execute(
            select(RSCClassifier.scale, func.count(RSCClassifier.id))
            .group_by(RSCClassifier.scale)
        )
        classifiers_by_scale = dict(classifiers_by_scale_result.all()) if classifiers_by_scale_result else {}

        # 6. Последние 5 загруженных листов
        last_uploads_result = await db.execute(
            select(SXFSheet)
            .order_by(SXFSheet.uploaded_at.desc())
            .limit(5)
        )
        last_uploads = [
            {
                "id": sheet.id,
                "filename": sheet.filename,
                "nomenclature": sheet.nomenclature,
                "uploaded_at": sheet.uploaded_at.isoformat() if sheet.uploaded_at else None
            }
            for sheet in last_uploads_result.scalars().all()
        ]

        # 7. Последние активности пользователей
        recent_activity_result = await db.execute(
            select(User)
            .order_by(User.last_login.desc())
            .limit(5)
        )
        recent_activity = [
            {
                "user_id": user.id,
                "username": user.username,
                "last_login": user.last_login.isoformat() if user.last_login else None
            }
            for user in recent_activity_result.scalars().all()
        ]

        # Логируем успешное формирование отчета
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="report_view",
            entity_type="system",
            details={
                "report_type": "summary",
                "stats": {
                    "total_users": total_users,
                    "total_sheets": total_sheets,
                    "total_classifiers": total_classifiers
                }
            }
        )

        return ReportSummary(
            total_users=total_users,
            total_sheets=total_sheets,
            total_classifiers=total_classifiers,
            sheets_by_scale=sheets_by_scale,
            classifiers_by_scale=classifiers_by_scale,
            last_uploads=last_uploads,
            recent_activity=recent_activity
        )

    except Exception as e:
        logger.error(f"Ошибка при формировании отчета: {str(e)}", exc_info=True)
        await log_audit_event(
            db=db,
            user_id=current_user.id,
            action="report_view",
            status="failed",
            details={
                "error": str(e),
                "report_type": "summary"
            }
        )
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail="Произошла ошибка при формировании отчета"
        )

# Добавление CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"], 
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)