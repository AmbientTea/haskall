module Types where
import Values

data VType =
    IntType
    | BoolType
    deriving (Eq, Ord, Show)
    
typeValue (IntVal _)  = IntType
typeValue (BoolVal _) = BoolType


