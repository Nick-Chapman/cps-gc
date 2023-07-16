
module Top (main) where

import Control.Monad (ap,liftM)
import Data.Map (Map)
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Data.Set as Set

main :: IO ()
main = do
  runSem (evalToSem _triangleTailRecExample)
  runSem (evalToSem _triangleExample)
  runSem (evalToSem _fibExample)

  where

    returnTo :: Name -> Exp -> Prog
    returnTo k e = Tail (Get c (Var k)) [(k,Var k),(res,e)]

    finish = Def [k,res] (Print (Var res) Halt)

    (n,f,c,acc,k,res,res1) = ("n","f","c","acc","k","res","res1")

    _triangleTailRecExample =
      Tail (LitD triangleTR) [(acc, Lit 0),(n,Lit 6)]
      where
        triangleTR = Def [n,acc]
          (
            If (Less (Var n) (Lit 1)) (Print (Var acc) Halt) $
            Tail (LitD triangleTR) [(acc, Add (Var n) (Var acc))
                                   ,(n, Sub (Var n) (Lit 1))]
          )

    _triangleExample =
      LetAlloc k [(c,LitD finish)] $
      Tail (LitD triangle) [(n,Lit 7),(k,Var k)]
      where
        triangle = Def [n,k]
          (
            If (Less (Var n) (Lit 1)) (returnTo k (Lit 0)) $
            LetAlloc k [(c,LitD cont),(k,Var k),(n,Var n)] $
            Tail (LitD triangle) [(k,Var k),(n,Sub (Var n) (Lit 1))]
          )
        cont = Def [k,res]
          (
            Let n (Get n (Var k)) $
            Let k (Get k (Var k)) $
            returnTo k (Add (Var res) (Var n))
          )

    _fibExample =
      LetAlloc k [(c,LitD finish)] $
      Tail (LitD fib) [(n,Lit 10),(k,Var k)]
      where
        fib = Def [n,k]
          (
            If (Less (Var n) (Lit 2)) (returnTo k (Var n)) $
            LetAlloc k [(c,LitD cont1),(k,Var k),(n,Var n)] $
            Tail (LitD fib) [(k,Var k),(n,Sub (Var n) (Lit 1))]
          )
        cont1 = Def [k,res]
          (
            Let n (Get n (Var k)) $
            Let f (Get f (Var k)) $
            Let k (Get k (Var k)) $
            LetAlloc k [(c,LitD cont2),(k,Var k),(res1,Var res)] $
            Tail (LitD fib) [(k,Var k),(n,Sub (Var n) (Lit 2))]
          )
        cont2 = Def [k,res]
          (
            Let res1 (Get res1 (Var k)) $
            Let k (Get k (Var k)) $
            returnTo k (Add (Var res1) (Var res))
          )

data Def = Def [Name] Prog
  deriving Show

data Prog
  = Halt
  | Print Exp Prog
  | Let Name Exp Prog
  | LetAlloc Name [(Name,Exp)] Prog
  | Tail Exp [(Name,Exp)]
  | If Exp Prog Prog
  deriving Show

data Exp
  = Lit Int
  | LitD Def
  | Less Exp Exp
  | Add Exp Exp
  | Sub Exp Exp
  | Get Name Exp
  | Var Name

  deriving Show

evalToSem :: Prog -> Sem ()
evalToSem prog = exec Map.empty prog

  where
    exec :: Env -> Prog -> Sem ()
    exec q = \case
      Halt -> pure ()
      Print exp prog -> do
        v <- eval q exp
        SemPrint (show (deNum v))
        exec q prog
      Let x rhs body -> do
        v <- eval q rhs
        exec (Map.insert x v q) body
      Tail f args -> do
        fn <- eval q f
        let Def formals body = deDef fn
        let actuals = map fst args
        if (Set.fromList formals /= Set.fromList actuals) then error (show ("Tail,mismatch",formals,actuals)) else do
          args <- evalBinds q args
          let q' = Map.fromList args
          exec q' body
      LetAlloc name binds prog -> do
        binds <- evalBinds q binds
        p <- Alloc binds
        let q' = Map.insert name (P p) q
        exec q' prog
      If cond prog1 prog2 -> do
        n <- deNum <$> eval q cond
        exec q (if (n/=0) then prog1 else prog2)


    eval :: Env -> Exp -> Sem Value
    eval q = \case
      Lit num -> pure (N num)
      LitD def -> pure (D def)
      Less e1 e2 -> do
        v1 <- eval q e1
        v2 <- eval q e2
        N <$> SemLess (deNum v1) (deNum v2)
      Add e1 e2 -> do
        v1 <- eval q e1
        v2 <- eval q e2
        N <$> SemAdd (deNum v1) (deNum v2)
      Sub e1 e2 -> do
        v1 <- eval q e1
        v2 <- eval q e2
        N <$> SemSub (deNum v1) (deNum v2)
      Get x e -> do
        v <- eval q e
        SemGet x (dePointer v)
      Var x ->
        pure (maybe err id $ Map.lookup x q)
        where err = (error (show ("Var,lookup",x)))

    evalBinds :: Env -> [(Name,Exp)] -> Sem [(Name,Value)]
    evalBinds q binds =
      sequence [ do v <- eval q e; pure (x,v) | (x,e) <- binds ]


type Env = Map Name Value

data Value = P Pointer | N Int | D Def

instance Show Value where
  show = \case
    P p -> show p
    N n -> show n
    D (Def _args _) -> "\\" ++ show _args

deDef :: Value -> Def
deDef = \case
  D d -> d
  x -> error (show ("not def",x))

dePointer :: Value -> Pointer
dePointer = \case
  P x -> x
  _ -> error "not a pointer"

deNum :: Value -> Int
deNum = \case
  N x -> x
  _ -> error "not a code"


----------------------------------------------------------------------

instance Functor Sem where fmap = liftM
instance Applicative Sem where pure = Ret; (<*>) = ap
instance Monad Sem where (>>=) = Bind

data Sem a where
  Ret :: a -> Sem a
  Bind :: Sem a -> (a -> Sem b) -> Sem b
  SemPrint :: String -> Sem ()
  SemLess :: Int -> Int -> Sem Int
  SemAdd :: Int -> Int -> Sem Int
  SemSub :: Int -> Int -> Sem Int
  Alloc :: [(Name,Value)] -> Sem Pointer
  SemGet :: Name -> Pointer -> Sem Value
--  JumpWithRoots :: [Pointer] -> Sem () -> Sem ()

type Name = String

data Pointer = POINTER Int deriving (Eq,Ord)
instance Show Pointer where show (POINTER x) = printf "p%d" x

runSem :: Sem () -> IO ()
runSem sem0 = run state0 sem0 k0
  where

    debug = False
    dlog msg = if debug then putStr msg else pure ()

    state0 = State { u = 0, mem = Map.empty }

    k0 :: State -> () -> IO ()
    k0 = \_ () -> pure ()

    run :: State -> Sem a -> (State -> a -> IO ()) -> IO ()
    run s@State{u,mem} sem0 k = case sem0 of
      Ret x -> k s x
      Bind sem f -> run s sem $ \s a -> run s (f a) k
      SemPrint msg -> do
        printf "Print: %s\n" msg
        k s ()
      SemLess n1 n2 -> do
        let res = if (n1 < n2) then 1 else 0
        dlog $ printf "Less: %d < %d --> %d\n" n1 n2 res
        k s res
      SemAdd n1 n2 -> do
        let res = n1 + n2
        dlog $ printf "Add: %d + %d --> %d\n" n1 n2 res
        k s res
      SemSub n1 n2 -> do
        let res = n1 - n2
        dlog $ printf "Sub: %d - %d --> %d\n" n1 n2 res
        k s res
      Alloc xs -> do
        let p = POINTER u
        dlog $ printf "Alloc: %s = %s\n" (show p) (show xs)
        k s { u = u + 1, mem = Map.insert p xs mem} p
      SemGet name p -> do
        let xs = maybe err id $ Map.lookup p mem
              where err = (error (show ("SetGet,mem-lookup",p)))
        k s $ the (show ("Get",name,p,map fst xs)) [ v | (n,v) <- xs, n == name ]


data State = State { u :: Int, mem :: Map Pointer [(Name,Value)] }

the :: String -> [xs] -> xs
the msg = \case
  [] -> error ("the(0):" ++ msg)
  [x] -> x
  _:_:_ -> error ("the(>1):" ++ msg)
