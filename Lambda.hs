{-# LANGUAGE FlexibleContexts, TemplateHaskell #-}
{-

A Haskell implementation of the pure (untyped) lambda calculus.

-}
module Lambda where

import Prelude hiding ((**), and, snd, fst, head, tail)
import qualified Prelude as P (snd, fst, head, tail)

import Data.List ((\\), nub, delete)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State hiding (fix)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

{- Syntax: -}

data Term
  = Var String
  | Lam String Term
  | App Term Term
  deriving (Eq)

termPrec :: Term -> Int
termPrec (Var _)   = 3
termPrec (App _ _) = 2
termPrec (Lam _ _) = 1

instance Show Term where
   show t = showTerm 0 t ""

showTerm :: Int -> Term -> ShowS
showTerm ctxtPrec (Var x) = (x ++)
showTerm ctxtPrec t@(Lam x t1) = showParen (ctxtPrec > termPrec t) $
  showString ("λ" ++ x ++ ". ") . showTerm (termPrec t) t1
showTerm ctxtPrec t@(App t1 t2) = showTerm (termPrec t) t1 .
  (" " ++) . showParen (isApp t2) (showTerm (termPrec t) t2)
  where isApp (App _ _) = True
        isApp _         = False

parse :: String -> Term
parse = undefined -- should we add this to 'compile' concrete
                  -- λ-programs into their ASTs?

{- Booleans and test: -}

fls, tru :: Term
fls = Lam "t". Lam "f" $ Var "f"
tru = Lam "t". Lam "f" $ Var "t"

test :: Term
test = Lam "c". Lam "t". Lam "e" $ (Var "c" `App` Var "t") `App` Var "e"

and, or, not :: Term
and = Lam "b". Lam "c" $ ((test `App` Var "b") `App` Var "c") `App` fls
or  = Lam "b". Lam "c" $ ((test `App` Var "b") `App` tru) `App` Var "c"
not = Lam "b" $ ((test `App` Var "b") `App` fls) `App` tru

{- Pairs -}

pair, fst, snd :: Term
pair   = Lam "f". Lam "s". Lam "c" $ Var "c" `App` Var "f" `App` Var "s"
fst  = Lam "p" $ Var "p" `App` tru
snd = Lam "p" $ Var "p" `App` fls

{- Numbers: -}

mkChurchNat :: Int -> Term
mkChurchNat n
  | n < 0     = error "mkChurchNat: only applicable on natural numbers."
  | otherwise = Lam "s". Lam "z" $ foldr App (Var "z") (replicate n (Var "s"))

plus, times, power :: Term
plus = Lam "m". Lam "n". Lam "s". Lam "z" $
  App (Var "m") (Var "s") `App` (App (Var "n") (Var "s") `App` (Var "z"))

times = Lam "m". Lam "n" $ Var "m" `App` (plus `App` Var "n") `App` (mkChurchNat 0)
power = Lam "m". Lam "n" $ Var "n" `App` (times `App` Var "m") `App` (mkChurchNat 1)

scc  = Lam "m". Lam "s". Lam "z" $
  Var "s" `App` (Var "m" `App` Var "s" `App` Var "z")
prd = Lam "m" $ fst `App` (Var "m" `App` ss `App` zz)
  where
    zz = pair `App` (mkChurchNat 0) `App` (mkChurchNat 0)
    ss = Lam "p" $ pair `App` (snd `App` Var "p")
                        `App` (scc `App` (snd `App` Var "p"))

-- from now on we'll use the following more convenient notation for
-- specyfing programs in the lambda calculus:

λ :: String -> Term -> Term
λ = Lam

infixl 8 **
(**) :: Term -> Term -> Term
(**) = App

-- predefine variable names a = Var "a", b = Var "b", ..., z = Var
-- "z", using Template Haskell.
sequence [valD (varP (mkName x)) (normalB [| Var x |]) []
         | x <- map (:[]) ['a'..'z']]

-- using the above notation, we can write λ-programs more succinctly:

iszro, equal :: Term
iszro = λ "m" $ m ** (λ "x" fls) ** tru
equal = λ "m". λ "n" $
  and ** (iszro ** (m ** prd ** n))
      ** (iszro ** (n ** prd ** m))

subtract :: Term
subtract = λ "m". λ "n" $ n ** prd ** m

{- Lists: -}

mkList :: [Term] -> Term
mkList = λ "c". λ "n". foldr (\h t -> c ** h ** t) n

nil, cons, isnil, head, tail :: Term
nil   = λ "c". λ "n" $ n
cons  = λ "h". λ "t". λ "c". λ "n" $ c ** h ** (t ** c ** n)
isnil = λ "l" $ l ** (λ "h". λ "t" $ fls) ** tru
head  = λ "l" $ l ** (λ "h". λ "t" $ h) ** nil
tail  = λ "l" $ fst ** (l ** cc ** nn)
  where nn = pair ** nil ** nil
        cc = λ "h". λ "p" $ pair ** (snd ** p)
                                 ** (cons ** h ** (snd ** p))

{- Recursion using (call-by-value) Fixpoints -}

fix = λ "f" $ h ** h
  where h = (λ "x" $ f ** (λ "y" $ x ** x ** y))

-- summing lists of lists of naturals:
sumlists = fix ** (λ "f". λ "l" $
  test ** (isnil ** l)
       ** (λ "n" $  n)
       ** (λ "d" $ plus ** (sumlist ** (head ** l))
                       ** (f ** (tail ** l)))
       ** mkChurchNat 0)
  where sumlist = λ "l" $ l ** plus ** mkChurchNat 0

{- Evaluation: -}

reduce :: Term -> Maybe (Term)
reduce (Var x)    = Nothing
reduce (Lam x t') = Nothing 
reduce (App t1 t2)
  | (Lam x t') <- t1, value t2 = Just (subst x t2 t')
  | (Lam x t') <- t1           = App t1 <$> reduce t2
  | otherwise                  = App <$> reduce t1 <*> pure t2
  where
    value (Lam _ _) = True
    value (Var _)   = True -- for testing!
    value _         = False

free :: Term -> [String]
free (Var x)     = [x]
free (App t1 t2) = nub $ free t1 ++ free t2
free (Lam x t1)  = nub $ delete x (free t1)

type VarSupply a = State [String] String

fresh :: [String] -> String -> String
fresh vars prefix = P.head $ names \\ (nub vars)
  where names = [ prefix ++ "_" ++ show k | k <- [1..]]

subst :: String -> Term -> Term -> Term
subst x s t = evalState (mkSubst x s t) (nub (x:free s))

mkSubst :: String
        -> Term
        -> Term
        -> State [String] (Term)
mkSubst x s (Var y)
  | y == x    = return s
  | otherwise = return (Var y)
mkSubst x s (App t1 t2) =
  App <$> mkSubst x s t1 <*> mkSubst x s t2
mkSubst x s (Lam y t1)
  | y == x || y `elem` free s = do
      vars <- get
      let z = fresh vars y
      modify (z:)
      t1' <- mkSubst y (Var z) t1
      mkSubst x s (Lam z t1')
  | otherwise = do
      modify (y:)
      Lam y <$> mkSubst x s t1
      
eval :: Term -> Term
eval t = step t (reduce t)
  where
    step t Nothing   = t
    step t (Just t') = eval t'

{- Nameless Terms: the untyped lambda calculus with de Brujin indices -}

data TermN
  = VarN Int
  | LamN TermN
  | AppN TermN TermN
  deriving (Eq, Show)

type Context = Map String [Int]

-- | Convert a standard λ-program into nameless λ-program
removeNames :: Map String [Int] -> Term -> TermN
removeNames context t = evalState (remove t) context
  where
    remove (Var x) = do
      ctxt <- get
      case Map.lookup x ctxt of
        Just (n:_) -> return (VarN n)
        _ -> error $ "removeNames: found free variable " ++ show x
    remove (Lam x t1) = do
      modify $ pushIncr x
      t1' <- remove t1
      modify $ popDecr x
      return (LamN t1')
    remove (App t1 t2) = do
      t1' <- remove t1
      t2' <- remove t2
      return (AppN t1' t2')
    
    pushIncr x = Map.insertWith (++) x [0] . fmap (map (+1))
    popDecr  x = Map.adjust P.tail x . fmap (map (\n -> n-1))

-- | Convert a nameless λ-program back into a normal λ-program.
restoreNames :: Map Int String -> TermN -> Term
restoreNames context nt = evalState (restore nt) context
  where
    restore (VarN n) = do
      ctxt <- get
      case Map.lookup n ctxt of
        Just x -> return (Var x)
        _ -> error $ "removeNames: found free variable " ++ show n
    restore (LamN t1) = do
      ctxt <- get
      let x = fresh (values ctxt) "v"
      modify $ pushIncr x
      t1' <- restore t1
      modify $ popDecr x
      return (Lam x t1')
    restore (AppN t1 t2) = do
      t1' <- restore t1
      t2' <- restore t2
      return (App t1' t2')

    values     = map P.snd . Map.toList
    pushIncr x = Map.insert 0 x . Map.mapKeysMonotonic (+1)
    popDecr  x = Map.delete 0 . Map.mapKeysMonotonic (\n -> n-1)

shift :: Int -> TermN -> TermN
shift d = shiftAbove 0 where
  shiftAbove c (VarN k)
    | k >= c    = VarN (k+d)
    | otherwise = VarN k
  shiftAbove c (AppN t1 t2) = AppN (shiftAbove c t1) (shiftAbove c t2)
  shiftAbove c (LamN t1)    = LamN (shiftAbove (c+1) t1)

substN :: Int -> TermN -> TermN -> TermN
substN j s (VarN k) | j == k = s | otherwise = (VarN k)
substN j s (AppN t1 t2) = AppN (substN j s t1) (substN j s t2)
substN j s (LamN t1)    = LamN (substN (j+1) (shift 1 s) t1)
