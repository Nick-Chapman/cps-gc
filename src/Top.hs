
module Top (main) where

import Control.Monad (ap,liftM)
import Data.Map (Map)
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Data.Set as Set

main :: IO ()
main = do
  runSem (evalToSem _fib)

  where

    (n,f,c,arg,acc,k,res,res1) = ("n","f","c","arg","acc","k","res","res1")

    _triangleTRa =
      LetFun f [arg]
      (
        Let n (Get n (Var arg)) $
        Let acc (Get acc (Var arg)) $
        If (Less (Var n) (Lit 1)) (Print (Var acc) Halt) $
        LetAlloc arg [(acc, Add (Var n) (Var acc))
                       ,(n, Sub (Var n) (Lit 1))] $
        Tail (Var f) [(arg, Var arg)]
      ) $
      LetAlloc arg [(acc, Lit 0),(n,Lit 6)] $
      Tail (Var f) [(arg, Var arg)]

    _triangleTR =
      LetFun f [n,acc]
      (
        If (Less (Var n) (Lit 1)) (Print (Var acc) Halt) $
        Tail (Var f) [(acc, Add (Var n) (Var acc))
                 ,(n, Sub (Var n) (Lit 1))]
      ) $
      Tail (Var f) [(acc, Lit 0),(n,Lit 6)]

    retK :: Name -> Exp -> Prog
    retK k e =
      Tail (Get c (Var k)) [(k,Var k),(res,e)]

    _triangle =
      LetFun f [n,k]
      (
        If (Less (Var n) (Lit 1)) (
          retK k (Lit 0)
        ) $
        LetFun c [k,res] (
          Let n (Get n (Var k)) $
          Let k (Get k (Var k)) $
          retK k (Add (Var res) (Var n))
        ) $
        LetAlloc k [(c,Var c)
                   ,(k,Var k)
                   ,(n,Var n)
                   ] $
        Tail (Var f) [(k, Var k)
                     ,(n, Sub (Var n) (Lit 1))]
      ) $
      LetFun c [k,res] (Print (Var res) Halt) $
      LetAlloc k [(c,Var c)] $
      Tail (Var f) [(n,Lit 5),(k,Var k)]



    _fib =
      LetFun f [n,k]
      (
        If (Less (Var n) (Lit 2)) (
          retK k (Var n)
        ) $

        LetFun c [k,res] (
          Let n (Get n (Var k)) $
          Let f (Get f (Var k)) $
          Let k (Get k (Var k)) $

          LetFun c [k,res] (
            Let res1 (Get res1 (Var k)) $
            Let k (Get k (Var k)) $
            retK k (Add (Var res1) (Var res))
            ) $
          LetAlloc k [(c,Var c) ,(k,Var k) ,(res1,Var res)] $
          Tail (Var f) [(k, Var k)
                       ,(n, Sub (Var n) (Lit 2))]

        ) $
        LetAlloc k [(c,Var c),(k,Var k),(n,Var n),(f,Var f)] $
        Tail (Var f) [(k, Var k)
                     ,(n, Sub (Var n) (Lit 1))]

      ) $
      LetFun c [k,res] (Print (Var res) Halt) $
      LetAlloc k [(c,Var c)] $
      Tail (Var f) [(n,Lit 10),(k,Var k)]


_ = (triangleTR,triangle)
  where
    triangleTR :: Int -> Int -> Int
    triangleTR n acc =
      if (n==0) then acc else triangleTR (n-1) (acc+n)

    triangle :: Int -> (Int -> r) -> r
    triangle n k =
      if (n==0) then k 0 else triangle (n-1) $ \res -> k (n+res)

data Prog
  = Halt
  | Print Exp Prog
  | Let Name Exp Prog
  | LetFun Name [Name] Prog Prog
  | LetAlloc Name [(Name,Exp)] Prog
  | Tail Exp [(Name,Exp)]
  | If Exp Prog Prog
  deriving Show

data Exp
  = Lit Int
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
      LetFun f formals body prog ->
        exec (Map.insert f (Code f formals body) q) prog
      Tail f args -> do
        fn <- eval q f
        let (self,formals,body) = deCode fn
        let actuals = map fst args
        if (Set.fromList formals /= Set.fromList actuals) then error (show ("Tail,mismatch",f,formals,actuals)) else do
          args <- evalBinds q args
          let q' = Map.fromList ((self,fn):args)
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
      Lit n -> pure (N n)
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

data Value = P Pointer | N Int | Code Name [Name] Prog
  deriving Show

deCode :: Value -> (Name,[Name],Prog)
deCode = \case
  Code fn formals x -> (fn,formals,x)
  x -> error (show ("not code",x))

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

data Pointer = POINTER [(Name,Value)] -- TODO
  deriving Show

runSem :: Sem () -> IO ()
runSem sem0 = run sem0 k0
  where
    k0 :: () -> IO ()
    k0 = \() -> pure ()

    run :: Sem a -> (a -> IO ()) -> IO ()
    run sem0 k = case sem0 of
      Ret x -> k x
      Bind sem f -> run sem $ \a -> run (f a) k
      SemPrint s -> do
        printf "Print: %s\n" s
        k ()
      SemLess n1 n2 -> do
        let res = if (n1 < n2) then 1 else 0
        printf "Less: %d < %d --> %d\n" n1 n2 res
        k res
      SemAdd n1 n2 -> do
        let res = n1 + n2
        printf "Add: %d + %d --> %d\n" n1 n2 res
        k res
      SemSub n1 n2 -> do
        let res = n1 - n2
        printf "Sub: %d - %d --> %d\n" n1 n2 res
        k res
      Alloc xs -> do
        let p = POINTER xs
        --printf "Alloc: %s\n" (show xs)
        printf "Alloc: %s\n" (show (map fst xs))
        k p
      SemGet name (POINTER xs) ->
        k $ the (show ("Get",name,map fst xs)) [ v | (n,v) <- xs, n == name ]


the :: String -> [xs] -> xs
the msg = \case
  [] -> error ("the(0):" ++ msg)
  [x] -> x
  _:_:_ -> error ("the(>1):" ++ msg)
