module Types where
import AbsHaskall
import Values

data VType =
    IntType
    | BoolType
    deriving (Eq, Ord, Show)
    
typeValue (IntVal _)  = IntType
typeValue (BoolVal _) = BoolType

typeToken TInt = IntType
typeToken TBool = BoolType
