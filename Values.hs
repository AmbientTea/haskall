module Values where

data Value =
    IntVal Integer
    | BoolVal Bool
    deriving (Eq, Ord, Show)

int  (IntVal i)  = i
bool (BoolVal b) = b

liftValOp f unp1 unp2 pck v1 v2 = pck $ f (unp1 v1) (unp2 v2)

valAdd = liftValOp (+) int int IntVal
valMul = liftValOp (*) int int IntVal
valSub = liftValOp (-) int int IntVal

valLt = liftValOp (<) int int BoolVal

valIntEq = liftValOp (==) int int BoolVal
valBoolEq = liftValOp (==) bool bool BoolVal
