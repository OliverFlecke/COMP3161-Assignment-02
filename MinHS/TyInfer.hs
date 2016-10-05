module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst
unify (TypeVar v1) (TypeVar v2) = 
  if v1 == v2 
    then return emptySubst
    else return (v2 =: (TypeVar v1))
unify (Base t1) (Base t2) = 
  if t1 == t2 
    then return emptySubst 
    else error "No unifer"
unify (Prod t11 t12) (Prod t21 t22) = do
  s <- unify t11 t12
  s' <- unify (substitute s t12) (substitute s t22)
  return $ s <> s'
unify (Sum t11 t12) (Sum t21 t22) = unify (Prod t11 t12) (Prod t21 t22)
unify (Arrow t11 t12) (Arrow t21 t22) = unify (Prod t11 t12) (Prod t21 t22)
-- unify (TypeVar v) 


unify _ _ = error "No unifer found"

generalise :: Gamma -> Type -> QType
generalise g t = error "implement me"



inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)

inferProgram env [Bind name _ [] exp] = do 
  (e, t, s) <- inferExp env exp 
  return ([Bind name (Just $ Ty t) [] e], t, s)


inferProgram env bs = error "implement me! don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g (Num n) = return (Num n, Base Int, emptySubst)
inferExp g (Con var) = 
  case constType var of 
    Just (Ty t)   -> return (Con var, t, emptySubst)
    Nothing       -> error "Could not find a type"
inferExp g (App (Prim Neg) n) = 
  case primOpType Neg of 
    Ty (Base Int `Arrow` Base Int)  
      -> return ((App (Prim Neg) n), Base Int, emptySubst) 
    _ -> error "Type not supported for negation"
inferExp g (App (App (Prim op) n1) n2) = 
  case primOpType op of 
    Ty (Base Int `Arrow` (Base Int `Arrow` Base t))  
      -> return ((App (App (Prim op) n1) n2), Base t, emptySubst)
    _             -> error "Prim operator not yet supported"

inferExp g (Let [Bind n _ [] e] v) = do
  (e, t, s)   <- inferExp g e 
  return ((Let [Bind n (Just $ Ty t) [] e] v), t, s) 

inferExp g (If b e1 e2) = do 
  (b', bt, bs) <- inferExp g b
  case bt of 
    Base Bool -> do
      (e1', e1t, e1s) <- inferExp g e1
      (e2', e2t, e2s) <- inferExp g e2
      t <- unify e1t e2t 
      return ((If b' e1' e2'), e2t, t)
    _         -> error "Type error" 



inferExp g _ = error "Implement me!"
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


