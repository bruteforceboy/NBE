module Untyped.Simple where

newtype Name = Name String
  deriving (Show, Eq)

newtype Env val = Env [(Name, val)]
  deriving (Show)

newtype Message = Message String
  deriving (Show)

data Expr = Var Name | Lambda Name Expr | App Expr Expr deriving (Show)

data Value = VClosure (Env Value) Name Expr
  deriving (Show)

initEnv :: Env val
failure :: String -> Either Message a
initEnv = Env []

failure msg = Left (Message msg)

lookupVar :: Env val -> Name -> Either Message val
lookupVar (Env []) (Name x) = failure ("Not found" ++ x)
lookupVar (Env ((name, val) : env')) x
  | name == x = Right val
  | otherwise = lookupVar (Env env') x

eval :: Env Value -> Expr -> Either Message Value
eval env (Var x) = lookupVar env x
eval env (Lambda x expr) = Right (VClosure env x expr)
eval env (App operator operand) = do
  fun <- eval env operator
  arg <- eval env operand
  doApply fun arg

extend :: Env val -> Name -> val -> Env val
extend (Env env) x v =
  Env ((x, v) : env)

doApply :: Value -> Value -> Either Message Value
doApply (VClosure env x body) arg =
  eval (extend env x arg) body

addDefs :: Env Value -> [(Name, Expr)] -> Either Message (Env Value)
addDefs env [] = Right env
addDefs env ((x, e) : rem) = do
  v <- eval env e
  addDefs (extend env x v) rem

runProgram :: [(Name, Expr)] -> Expr -> Either Message Value
runProgram defs expr = do
  env <- addDefs initEnv defs
  eval env expr

toChurch :: Integer -> Expr
toChurch n
  | n <= 0 = Var (Name "zero")
  | otherwise = App (Var (Name "add1")) (toChurch (n - 1))

churchDefs :: [(Name, Expr)]
churchDefs =
  [ ( Name "zero",
      Lambda
        (Name "f")
        ( Lambda
            (Name "x")
            (Var (Name "x"))
        )
    ),
    ( Name "add1",
      Lambda
        (Name "n")
        ( Lambda
            (Name "f")
            ( Lambda
                (Name "x")
                ( App
                    (Var (Name "f"))
                    ( App
                        ( App
                            (Var (Name "n"))
                            (Var (Name "f"))
                        )
                        (Var (Name "x"))
                    )
                )
            )
        )
    ),
    ( Name "+",
      Lambda
        (Name "j")
        ( Lambda
            (Name "k")
            ( Lambda
                (Name "f")
                ( Lambda
                    (Name "x")
                    ( App
                        (App (Var (Name "j")) (Var (Name "f")))
                        ( App
                            (App (Var (Name "k")) (Var (Name "f")))
                            (Var (Name "x"))
                        )
                    )
                )
            )
        )
    )
  ]

test :: Either Message Value
test =
  runProgram
    churchDefs
    ( App
        ( App
            (Var (Name "+"))
            (toChurch 2)
        )
        (toChurch 3)
    )