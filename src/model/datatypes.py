from enum import Enum


class Types(Enum):
    INT = int
    FLOAT = float
    INTEGER = "integer"
    REAL = "real"
    STRING = str
    BOOL = bool


# this is shorter to use!
INT = Types.INT
FLOAT = Types.FLOAT
INTEGER = Types.INTEGER
REAL = Types.REAL
STRING = Types.STRING
BOOL = Types.BOOL
