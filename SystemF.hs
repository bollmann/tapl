{-# LANGUAGE MultiParamTypeClasses #-}
{-| A Haskell implementation of a PCF-style System F. -}

{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}

module TypedLambda where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

{- Syntax -}

newtype TypeVar = TypeVar String deriving (Eq, Ord, Show)
newtype TermVar = TermVar String deriving (Eq, Ord, Show)

infixr 7 :->:
data Type
  = NatT
  | Type :->: Type
  | VarT TypeVar             -- an underspecified (i.e., variable) type
  | ForallT TypeVar Type
  deriving (Eq, Show)

data Term where
  Zero :: Term
  Pred :: Term -> Term
  Succ :: Term -> Term
  Ifz  :: Term -> Term -> Term -> Term
  Var  :: TermVar -> Term
  Lam  :: TermVar -> Type -> Term -> Term
  App  :: Term -> Term -> Term
  Let  :: TermVar -> Term -> Term -> Term
  Fix  :: Term -> Term
  LamT :: TypeVar -> Term -> Term
  AppT :: Term -> Type -> Term
  deriving (Eq, Show)

value :: Term -> Bool
value (Lam _ _ _) = True
value (LamT _ _)  = True
value t           = number t

number :: Term -> Bool
number Zero      = True
number (Succ t1) = number t1
number _         = False

{- Evaluation (Semantics) -}

-- | Small-Step call-by-value reduction relation.
reduce :: Term -> Maybe Term
reduce Zero           = Nothing
reduce (Pred t1)
  | Succ nv   <- t1
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
reduce (LamT _ _)     = Nothing
reduce (AppT t1 ty)
  | LamT tyV t2 <- t1 = Just (subst tyV ty t2)
  | otherwise         = AppT <$> reduce t1 <*> pure ty

-- | Multi-Step call-by-value evaluation induced by reduce (i.e.,
-- reduce's reflexive and transitive closure).
eval :: Term -> Term
eval tm = fix step tm (reduce tm)
  where
    step _    t Nothing   = t
    step cont _ (Just t') = cont t' (reduce t')

class Eq var => Subst var res where
  substHere :: var -> res -> Term -> State [var] Term
  free  :: res -> [var]

instance Subst TermVar Term where
  substHere x s (Var y)
    | y == x    = return s
    | otherwise = return (Var y)
  substHere x s (Lam y ty t1)
    | y == x || y `elem` free s = do
        z <- fresh termVars
        t1' <- mkSubst y (Var z) t1
        mkSubst x s (Lam z ty t1')
    | otherwise = do
        modify (y:)
        Lam y ty <$> mkSubst x s t1
  substHere x s (Let y t1 t2) = do
    t1' <- mkSubst x s t1
    if y == x || y `elem` free s
      then do z    <- fresh termVars
              t2'  <- mkSubst y (Var z) t2
              t2'' <- mkSubst x s t2'
              return (Let z t1' t2'')
      else do t2' <- mkSubst x s t2
              modify (y:)
              return (Let y t1' t2')
  substHere x s (LamT xT t1) = LamT xT <$> mkSubst x s t1
  substHere x s (AppT t1 xT) = AppT <$> mkSubst x s t1 <*> pure xT
  substHere _ _ _ = error "doSubst: panic! The 'impossible' happened"

  free = freeTermVars

instance Subst TypeVar Type where
  substHere _ _ (Var y) = return (Var y)
  substHere xT sT (Lam y ty t1) = do
    ty' <- substTy xT sT ty
    Lam y ty' <$> mkSubst xT sT t1
  substHere xT sT (Let y t1 t2) = do
    Let y <$> mkSubst xT sT t1 <*> mkSubst xT sT t2
  substHere xT sT (LamT yT t1)
    | yT == xT || yT `elem` free sT = do
        zT  <- fresh typeVars
        t1' <- mkSubst yT (VarT zT) t1
        LamT zT <$> mkSubst xT sT t1'
    | otherwise = do
        modify (yT:)
        LamT yT <$> mkSubst xT sT t1
  substHere xT sT (AppT t1 ty) = do
    ty' <- substTy xT sT ty
    AppT <$> mkSubst xT sT t1 <*> pure ty'
  substHere _ _ _ = error "doSubst: panic! The 'impossible' happened"

  free = freeTyVars

-- | Substitutes all free occurrences of variable x in term t with s,
-- i.e., implements [x |-> s]t.
subst :: Subst var res => var -> res -> Term -> Term
subst x s t = evalState (mkSubst x s t) (nub (x:free s))

mkSubst :: Subst var res => var -> res -> Term -> State [var] Term
mkSubst _ _ Zero           = return Zero
mkSubst x s (Succ t1)      = Succ <$> mkSubst x s t1
mkSubst x s (Pred t1)      = Pred <$> mkSubst x s t1
mkSubst x s (Ifz t1 t2 t3) = do
  t1' <- mkSubst x s t1
  t2' <- mkSubst x s t2
  t3' <- mkSubst x s t3
  return (Ifz t1' t2' t3')
mkSubst x s (Var y)        = substHere x s (Var y)
mkSubst x s (App t1 t2)    = App <$> mkSubst x s t1 <*> mkSubst x s t2
mkSubst x s (Lam y ty t1)  = substHere x s (Lam y ty t1)
mkSubst x s (Let y t1 t2)  = substHere x s (Let y t1 t2)
mkSubst x s (Fix t1)       = Fix <$> mkSubst x s t1
mkSubst x s (LamT xT t1)   = substHere x s (LamT xT t1)
mkSubst x s (AppT t1 xT)   = substHere x s (AppT t1 xT)

-- | Subsitutes xT through sT in ty, i.e., [xT |-> sT]ty
substTy :: TypeVar -> Type -> Type -> State [TypeVar] Type
substTy _ _ NatT = return NatT
substTy xT sT (VarT yT)
  | xT == yT  = return sT
  | otherwise = return (VarT yT)
substTy xT sT (ty1 :->: ty2) = do
  ty1' <- substTy xT sT ty1
  ty2' <- substTy xT sT ty2
  return (ty1' :->: ty2')
substTy xT sT (ForallT yT ty)
  | yT == xT || yT `elem` free sT = do
      zT  <- fresh typeVars
      ty' <- substTy yT (VarT zT) ty
      ForallT zT <$> substTy xT sT ty'
  | otherwise = do
      modify (yT:)
      ForallT yT <$> substTy xT sT ty

-- | Extracts the free variables of a λ-term
freeTermVars :: Term -> [TermVar]
freeTermVars Zero           = []
freeTermVars (Pred t1)      = nub $ freeTermVars t1
freeTermVars (Succ t1)      = nub $ freeTermVars t1
freeTermVars (Ifz t1 t2 t3) = nub $ freeTermVars t1
                                 ++ freeTermVars t2
                                 ++ freeTermVars t3
freeTermVars (Var x)        = [x]
freeTermVars (Lam x _ t1)   = nub $ delete x (freeTermVars t1)
freeTermVars (App t1 t2)    = nub $ freeTermVars t1 ++ freeTermVars t2
freeTermVars (Let x t1 t2)  = nub $ freeTermVars t1
                                 ++ (delete x (freeTermVars t2))
freeTermVars (Fix t1)       = nub $ freeTermVars t1
freeTermVars (LamT _ t1)    = nub $ freeTermVars t1
freeTermVars (AppT t1 _)    = nub $ freeTermVars t1

-- | Extracts the free type variables from a type
freeTyVars :: Type -> [TypeVar]
freeTyVars NatT             = []
freeTyVars (ty1 :->: ty2)   = nub $ freeTyVars ty1 ++ freeTyVars ty2
freeTyVars (VarT tyV)       = [tyV]
freeTyVars (ForallT tyV ty) = nub $ delete tyV (freeTyVars ty)

class Eq var => Var var where
  makeVar :: String -> var
  getVarName :: var -> String

instance Var TermVar where
  makeVar = TermVar
  getVarName (TermVar v) = v

instance Var TypeVar where
  makeVar = TypeVar
  getVarName (TypeVar v) = v

termVars :: [TermVar]
termVars = [ TermVar $ "x_" ++ show k | k <- ([1..] :: [Integer]) ]

typeVars :: [TypeVar]
typeVars = [ TypeVar $ "X_" ++ show k | k <- ([1..] :: [Integer]) ]

-- | Generate a fresh variable name wrt to the used variables 'var'.
fresh :: Eq var => [var] -> State [var] var
fresh varSupply
  = do usedVars <- get
       let newVar = head $ varSupply \\ usedVars
       modify (newVar:)
       return newVar

{- Typechecking -}

data Context
  = Context { store  :: Map TermVar Type
            , tyVars :: [TypeVar] }

emptyCxt :: Context
emptyCxt = Context { store = Map.empty, tyVars = [] }

lookupVar :: TermVar -> Context -> Maybe Type
lookupVar x (Context st _) = Map.lookup x st

insertVar :: TermVar -> Type -> Context -> Context
insertVar x ty (Context st tyVs) = Context st' tyVs
  where st' = Map.insert x ty st

data TypeError
  = TypeMismatch { at      :: Term
                 , reasons :: [(Term, Type)] }
  | TypeNotFound { term    :: Term }
  deriving (Eq, Show)

-- | Typechecks a closed term and returns its type, if any.
typeOf :: Term -> Either TypeError Type
typeOf t = typeof emptyCxt t

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
  case lookupVar x cxt of
    Nothing -> throwError $ TypeNotFound (Var x)
    Just ty -> return ty
typeof cxt (Lam x ty t1) = do
  ty1 <- typeof (insertVar x ty cxt) t1
  return (ty :->: ty1)
typeof cxt (App t1 t2) = do
  tyf <- typeof cxt t1
  tyx <- typeof cxt t2
  case (tyf, tyx) of
    (ty1 :->: ty2, ty1') | ty1 == ty1' -> return ty2
    _ -> throwError $ TypeMismatch (App t1 t2) [(t1, tyf), (t2, tyx)]
typeof cxt (Ifz t1 t2 t3) = do
  ty1 <- typeof cxt t1
  ty2 <- typeof cxt t2
  ty3 <- typeof cxt t3
  case ty1 of
    NatT | ty2 == ty3 -> return ty2
    _ -> throwError $ TypeMismatch
           (Ifz t1 t2 t3) [(t1, ty1), (t2, ty2), (t3, ty3)]
typeof cxt (Let x t1 t2) = do
  ty1 <- typeof cxt t1
  ty2 <- typeof (insertVar x ty1 cxt) t2
  return ty2
typeof cxt (Fix t1) = do
  tyf <- typeof cxt t1
  case tyf of
    (ty1 :->: ty2) | ty1 == ty2 -> return ty1
    _ -> throwError $ TypeMismatch (Fix t1) [(t1, tyf)]
typeof cxt (LamT ty t1) = do
  ty1 <- typeof (cxt { tyVars = (tyVars cxt) ++ [ty] }) t1
  return (ForallT ty ty1)
typeof cxt (AppT t1 ty) = do
  ty1 <- typeof cxt t1
  case ty1 of
    ForallT tyVar ty2 -> return $ evalState (substTy tyVar ty ty2) usedTyVars
    _                 -> throwError $ TypeMismatch (AppT t1 ty) [(t1, ty1)]
  where usedTyVars = tyVar:(tyVars cxt ++ free ty)
