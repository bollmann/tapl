{-| A Haskell implementation of PCF with subtyping. -}

{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}

module SubLambda where

import Control.Monad.Except hiding (join)
import Control.Monad.State hiding (join)
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

{- Syntax -}

data Nat = Z | S Nat deriving (Eq, Show)
type Label = String

infixr :->:
data Type
  = NatT
  | Type :->: Type
  | RcdT [Label] [Type]
  | TopT
  deriving (Eq, Show)

data Value
  = NatV Nat
  | FuncV String Type Term
  | RcdV [Label] [Value]

data Term where
  Zero :: Term
  Pred :: Term -> Term
  Succ :: Term -> Term
  Ifz  :: Term -> Term -> Term -> Term
  Var  :: String -> Term
  Lam  :: String -> Type -> Term -> Term
  App  :: Term -> Term -> Term
  Let  :: String -> Term -> Term -> Term
  Fix  :: Term -> Term
  Rcd  :: [Label] -> [Term] -> Term
  Proj :: Term -> Label -> Term
  deriving (Eq, Show)

value :: Term -> Bool
value (Lam _ _ _) = True
value t           = number t || record t

number :: Term -> Bool
number Zero      = True
number (Succ t1) = number t1
number _         = False

record :: Term -> Bool
record (Rcd _ ts) = all value ts
record _          = False

{- Evaluation -}

-- | Small-Step call-by-value reduction relation.
reduce :: Term -> Maybe Term
reduce Zero           = Nothing
reduce (Pred t1)
  | Succ nv <- t1
  , number nv         = Just nv
  | otherwise         = Pred <$> reduce t1
reduce (Succ t1)      = Succ <$> reduce t1
reduce (Ifz t1 t2 t3)
  | Zero    <- t1     = Just t2
  | Succ nv <- t1
  , number nv         = Just t3
  | otherwise         = Ifz <$> reduce t1 <*> pure t2 <*> pure t3
reduce (Var _)        = Nothing
reduce (Lam _ _ _)    = Nothing
reduce (App t1 t2)
  | Lam x _ t' <- t1
  , value t2          = Just (subst x t2 t')
  | Lam _ _ _  <- t1  = App t1 <$> reduce t2
  | otherwise         = App <$> reduce t1 <*> pure t2
reduce (Let x t1 t2)
  | value t1          = Just (subst x t1 t2)
  | otherwise         = Let x <$> reduce t1 <*> pure t2
reduce (Fix t1)
  | Lam f _ t' <- t1  = Just (subst f (Fix t1) t')
  | otherwise         = Fix <$> reduce t1
reduce (Rcd ls ts)    = Rcd ls <$> doStep
  where
    doStep = either (const Nothing) Just (foldl tryStep (Left []) ts)
    tryStep (Left ts') t = case reduce t of
      Nothing -> Left  $ ts' ++ [t]
      Just t' -> Right $ ts' ++ [t']
    tryStep (Right ts') t = Right $ ts' ++ [t]
reduce (Proj t1 l)
  | (Rcd ls ts) <- t1
  , value t1          = lookup l (zip ls ts)
  | otherwise         = Proj <$> reduce t1 <*> pure l

-- | Multi-Step call-by-value evaluation which is induced by reduce
-- (i.e., reduce's reflexive, transitive closure).
eval :: Term -> Term
eval tm = fix step tm (reduce tm)
  where
    step _    t Nothing   = t
    step cont _ (Just t') = cont t' (reduce t')

-- | Substitutes all free occurrences of variable x in term t with s,
-- i.e., implements [x |-> s]t.
subst :: String -> Term -> Term -> Term
subst x s t = evalState (mkSubst x s t) (nub (x:free s))

mkSubst :: String -> Term -> Term -> State [String] Term
mkSubst _ _ Zero     = return Zero
mkSubst x s (Succ t1) = Succ <$> mkSubst x s t1
mkSubst x s (Pred t1) = Pred <$> mkSubst x s t1
mkSubst x s (Ifz t1 t2 t3) = do
  t1' <- mkSubst x s t1
  t2' <- mkSubst x s t2
  t3' <- mkSubst x s t3
  return (Ifz t1' t2' t3')
mkSubst x s (Var y)
  | y == x    = return s
  | otherwise = return (Var y)
mkSubst x s (App t1 t2) =
  App <$> mkSubst x s t1 <*> mkSubst x s t2
mkSubst x s (Lam y ty t1)
  | y == x || y `elem` free s = do
      z <- fresh y
      t1' <- mkSubst y (Var z) t1
      mkSubst x s (Lam z ty t1')
  | otherwise = do
      modify (y:)
      Lam y ty <$> mkSubst x s t1
mkSubst x s (Let y t1 t2) = do
  t1' <- mkSubst x s t1
  if y == x || y `elem` free s
    then do
      z    <- fresh y
      t2'  <- mkSubst y (Var z) t2
      t2'' <- mkSubst x s t2'
      return (Let z t1' t2'')
    else do
      t2' <- mkSubst x s t2
      modify (y:)
      return (Let y t1' t2')
mkSubst x s (Fix t1) = Fix <$> mkSubst x s t1
mkSubst x s (Rcd ls ts) = Rcd ls <$> mapM (mkSubst x s) ts
mkSubst x s (Proj t1 l) = Proj <$> mkSubst x s t1 <*> pure l

-- | Extracts the free variables of a λ-term
free :: Term -> [String]
free Zero           = []
free (Pred t1)      = free t1
free (Succ t1)      = free t1
free (Ifz t1 t2 t3) = nub $ free t1 ++ free t2 ++ free t3
free (Var x)        = [x]
free (Lam x _ t1)   = nub $ delete x (free t1)
free (App t1 t2)    = nub $ free t1 ++ free t2
free (Let x t1 t2)  = nub $ free t1 ++ (delete x (free t2))
free (Fix t1)       = nub $ free t1
free (Rcd _ ts)     = nub $ concatMap free ts
free (Proj t1 _)    = free t1

-- | Generate a fresh variable name (starting with prefix) wrt to the
-- used variables 'var'.
fresh :: String -> State [String] String
fresh prefix = do
  usedVars <- get
  let newVar = head $ names \\ usedVars
  modify (newVar:)
  return newVar
  where
    names = [ prefix ++ "_" ++ show k | k <- ([1..] :: [Integer])]

{- Typechecking -}

type Context = Map String Type

data TypeError
  = TypeMismatch { at      :: Term
                 , types   :: [(Term, Type)] }
  | TypeNotFound { term    :: Term }
  | MissingLabel { label   :: Label
                 , at      :: Term
                 , types   :: [(Term, Type)] }
  deriving (Eq, Show)

subtype :: Type -> Type -> Bool
subtype ty1 ty2 | ty1 == ty2          = True
subtype _ TopT                        = True
subtype (s1 :->: s2) (t1 :->: t2)     = subtype t1 s1 && subtype s2 t2
subtype (RcdT ls' tys') (RcdT ls tys) = labelsOk && typesOk
  where
    labelsOk = Set.fromList ls `Set.isSubsetOf` Set.fromList ls'
    typesOk  = case fst <$> uncons (filter isSub allPerms) of
      Just (RcdT _ tys'') -> and (zipWith subtype tys'' tys)
      _                   -> False
    allPerms = fmap (uncurry RcdT . unzip) $ permutations $ zip ls' tys'
    isSub (RcdT ls'' tys'') = ls `isPrefixOf` ls'' && tys `isPrefixOf` tys''
    isSub _                 = False
subtype _ _                           = False

-- | Computes the smallest upper bound for the two given types
join :: Type -> Type -> Type
join TopT _              = TopT
join NatT ty2
  | ty2 == NatT          = NatT
  | otherwise            = TopT
join (s1 :->: s2) ty2
  | t1 :->: t2 <- ty2    = case meet s1 t1 of
                             Nothing -> TopT
                             Just j1 -> j1 :->: join s2 t2
  | otherwise            = TopT
join (RcdT ls1 tys1) ty2
  | RcdT ls2 tys2 <- ty2 = mkRcd ls2 tys2
  | otherwise            = TopT
  where
    mkRcd ls2 tys2 = uncurry RcdT . unzip $ do
      (l1, t1) <- zip ls1 tys1
      (l2, t2) <- zip ls2 tys2
      guard (l1 == l2)
      return (l1, join t1 t2)

-- | Computes the greatest lower bound for the two given types.
meet :: Type -> Type -> Maybe Type
meet ty1  ty2
  | ty1 == ty2           = Just ty1
meet ty1  TopT           = Just ty1
meet TopT ty2            = Just ty2
meet NatT ty2
  | NatT <- ty2          = Just NatT
  | TopT <- ty2          = Just NatT
  | otherwise            = Nothing
meet (s1 :->: s2) ty2
  | t1 :->: t2 <- ty2    = (:->:) (join s1 t1) <$> meet s2 t2
  | otherwise            = Nothing
meet (RcdT ls1 tys1) ty2
  | RcdT ls2 tys2 <- ty2 = do let (ls, tys) = mkRcd ls2 tys2
                              tys' <- sequence tys
                              return (RcdT ls tys')
  | otherwise            = Nothing
  where
    mkRcd ls2 tys2 = unzip $ do
      (l1, t1) <- zip ls1 tys1
      (l2, t2) <- zip ls2 tys2
      if not (l1 `elem` ls2) then
        return (l1, Just t1)
      else if not (l2 `elem` ls1) then
        return (l2, Just t2)
      else guard (l1 == l2) >> return (l1, meet t1 t2)

-- | Typechecks a closed term and returns its type, if any.
typeOf :: Term -> Either TypeError Type
typeOf t = typeof Map.empty t

-- | Typechecks the given term wrt the given typing environment and
-- returns the term's type, if any.
typeof :: Context -> Term -> Either TypeError Type
typeof _   Zero      = return NatT
typeof cxt (Succ t1) = do
  ty1 <- typeof cxt t1
  case ty1 of
    NatT -> return NatT
    _    -> throwError $ TypeMismatch (Succ t1) [(t1, ty1)]
typeof cxt (Pred t1) = do
  ty1 <- typeof cxt t1
  case ty1 of
    NatT -> return NatT
    _    -> throwError $ TypeMismatch (Succ t1) [(t1, ty1)]
typeof cxt (Var x) = do
  case Map.lookup x cxt of
    Nothing -> throwError $ TypeNotFound (Var x)
    Just ty -> return ty
typeof cxt (Lam x ty t1) = do
  ty1 <- typeof (Map.insert x ty cxt) t1
  return (ty :->: ty1)
typeof cxt (App t1 t2) = do
  tyf <- typeof cxt t1
  tyx <- typeof cxt t2
  case tyf of
    ty1 :->: ty2 | subtype tyx ty1 -> return ty2
    _ -> throwError $ TypeMismatch (App t1 t2) [(t1, tyf), (t2, tyx)]
typeof cxt (Ifz t1 t2 t3) = do
  ty1 <- typeof cxt t1
  ty2 <- typeof cxt t2
  ty3 <- typeof cxt t3
  let lubTy = join ty2 ty3
  case ty1 of
    NatT -> return lubTy
    _    -> throwError $ TypeMismatch
              (Ifz t1 t2 t3) [(t1, ty1), (t2, ty2), (t3, ty3)]
typeof cxt (Let x t1 t2) = do
  ty1 <- typeof cxt t1
  ty2 <- typeof (Map.insert x ty1 cxt) t2
  return ty2
typeof cxt (Fix t1) = do
  tyf <- typeof cxt t1
  case tyf of
    (ty1 :->: ty2) | ty1 == ty2 -> return ty1
    _ -> throwError $ TypeMismatch (Fix t1) [(t1, tyf)]
typeof cxt (Rcd ls ts) = do
  tys <- mapM (typeof cxt) ts
  return (RcdT ls tys)
typeof cxt (Proj t1 l) = do
  ty1 <- typeof cxt t1
  case ty1 of
    RcdT ls tys ->
      maybe (throwError (MissingLabel l (Proj t1 l) [(t1, ty1)]))
            return $ lookup l (zip ls tys)
    _ -> throwError $ TypeMismatch (Proj t1 l) [(t1, ty1)]
