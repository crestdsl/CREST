from enum import Enum


class Types(Enum):
    """ An enum holding all datatypes. 
    Sometimes it's better to use ``Types.INT`` to clairfy that you're using a type.
    It might also resolve ambiguities
    """
    INT = int
    FLOAT = float
    INTEGER = "integer"
    REAL = "real"
    STRING = str
    BOOL = bool


# this is shorter to use!
INT = Types.INT
"""
Datatype for int values (computer floats).
This will be translated to the SMT solvers 32 bit Int theory.
"""

FLOAT = Types.FLOAT
"""
Datatype for floating point values (computer floats).
This will be translated to the SMT solvers 32bit Float theory.
"""

INTEGER = Types.INTEGER
"""
Datatype for integer values. (Actual integers, not computer int).
This will be translated to the SMT solvers Integer theory.
"""

REAL = Types.REAL
"""
Datatype for real values. (Actual real, not computer floating points).
This will be translated to the SMT solvers Real theory.
"""

STRING = Types.STRING
"""
Datatype for character sequences.
"""

BOOL = Types.BOOL
"""
Datatype for boolean values.
"""
