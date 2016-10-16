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
    else typeError $ TypeMismatch (Base t1) (Base t2)
unify (Prod t11 t12) (Prod t21 t22) = do
  s     <- unify t11 t12
  s'    <- unify (substitute s t12) (substitute s t22)
  return $ s <> s'
unify (Sum t11 t12) (Sum t21 t22) = unify (Prod t11 t12) (Prod t21 t22)
unify (Arrow t11 t12) (Arrow t21 t22) = do
  s     <- unify t11 t21 
  s'    <- unify t12 t22
  return $ s <> s'
unify (TypeVar v) t = 
  if elem v (tv t)  -- Should check if v is in the type t
    then typeError $ OccursCheckFailed v t
    else return $ v =: t
unify t (TypeVar v) = unify (TypeVar v) t
unify t1 t2 = typeError $ TypeMismatch t1 t2
 -- error $ "No unifer found between " <> (show t1) <> " and " <> (show t2)


generalise :: Gamma -> Type -> QType
generalise g t = foldl (\t' -> \x -> Forall x t') (Ty t) $ filter (\x -> elem x (tvGamma g)) (tv t)
-- Not enterly sure they do they same, so saved for safety 
-- generalise g t = generaliseHelper (filter (\x -> elem x (tvGamma g)) (tv t)) t
-- generaliseHelper :: [Id] -> Type -> QType
-- generaliseHelper (x:xs) t = Forall x $ generaliseHelper xs t
-- generaliseHelper [] t = Ty t


-- Infer program
inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env [Bind name _ [] exp] = do 
  (e, t, s) <- inferExp env exp 
  case generalise env t of 
    Ty t  -> return ([Bind "main" (Just $ Ty (substitute s t)) [] e], substitute s t, s)
    _     -> error "The type returned to main is not a valid type"
inferProgram env bs = error "implement me! don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"


-- Infer expression
inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g (Num n) = return (Num n, Base Int, emptySubst)

inferExp g (Var v) = do
  case E.lookup g v of 
    Just (Ty t)         -> return (Var v, t, v =: t)
    Just (Forall a t)  -> do
      alpha <- fresh 
      return (Var v, alpha, a =: alpha)
    Nothing             -> error "Varible not in gamma" 

inferExp g (Con var) = do
  case constType var of 
    Just (Ty t)         -> return (Con var, t, var =: t)
    Just (Forall a (Forall b (Ty (Arrow (TypeVar _) (Arrow (TypeVar _) t))))) -> do
      alpha     <- fresh
      beta      <- fresh
      return (Con var, t, a =: alpha <> b =: beta)
    Nothing             -> typeError $ NoSuchVariable var 

inferExp g (App (Prim Neg) n) = 
  case primOpType Neg of 
    Ty (Base Int `Arrow` Base Int)  ->
      case n of 
        Var v   ->
          case E.lookup g v of 
            Just (Ty (TypeVar a)) -> return (e, Base Int, a =: (Base Int))
            Just (Ty alpha)       -> return (e, Base Int, v =: alpha)
            Nothing               -> return (e, Base Int, emptySubst) 
        _  -> return (e, Base Int, emptySubst)
    Ty t  -> typeError $ TypeMismatch (Base Int) t
  where 
    e = App (Prim Neg) n
inferExp g (App (App (Prim op) e1) e2) = 
  case primOpType op of 
    Ty (Base Int `Arrow` (Base Int `Arrow` Base t)) -> 
      case (e1, e2) of 
        (Var x, Var y) | x == y -> 
          case E.lookup g x of 
            Just (Ty (TypeVar a)) -> return (e, Base t, a =: (Base Int))
            Just (Ty alpha)       -> return (e, Base t, x =: alpha)
            Nothing               -> return (e, Base t, x =: (Base Int))
        (Var x, Var y)  -> 
          case (E.lookup g x, E.lookup g y) of 
            (Just (Ty (TypeVar a)), Just (Ty (TypeVar b)))  -> return (e, Base t, a =: (Base Int) <> b =: (Base Int))
            (Just (Ty (TypeVar a)), Nothing)                -> return (e, Base t, a =: (Base Int) <> y =: (Base Int)) 
            (Nothing, Just (Ty (TypeVar b)))                -> return (e, Base t, x =: (Base Int) <> b =: (Base Int))
            (Just (Ty (TypeVar a)), Just (Ty alpha))        -> return (e, Base t, a =: (Base Int) <> y =: alpha)
            (Just (Ty alpha), Just (Ty (TypeVar a)))        -> return (e, Base t, x =: alpha <> a =: (Base Int))
            (Just (Ty t1), Just (Ty t2))                    -> return (e, Base t, x =: t1 <> y =: t2)
            (_, _)                                          -> return (e, Base t, x =: (Base Int) <> y =: (Base Int)) 
        (Var x, _)      -> 
          case E.lookup g x of 
            Just (Ty (TypeVar a)) -> return (e, Base t, a =: (Base Int))
            Just (Ty alpha)       -> return (e, Base t, x =: alpha)
            Nothing               -> return (e, Base t, x =: (Base Int))
        (_, Var x)      -> 
          case E.lookup g x of 
            Just (Ty (TypeVar a)) -> return (e, Base t, a =: (Base Int))
            Just (Ty alpha)       -> return (e, Base t, x =: alpha)
            Nothing               -> return (e, Base t, x =: (Base Int))
        (_, _)          -> return (e, Base t, emptySubst)
    _   -> error "Prim operator not yet supported"
  where 
    e = App (App (Prim op) e1) e2 

inferExp g (Let [Bind x _ [] e1] e2) = do
  (e1', t, s)  <- inferExp g e1 
  let g' = substGamma s $ g `E.add` (x, generalise (substGamma s g) t)
  (e2', t', s')  <- inferExp g' e2 
  return ((Let [Bind x (Just $ Ty t) [] e1'] e2'), t', s <> s')

-- Let function expression
inferExp g (Letfun (Bind f _ (x:[]) e)) = do
  alpha1             <- fresh
  alpha2             <- fresh
  let g' = (g `E.addAll` [(x, Ty alpha1), (f, Ty alpha2)])
  (e', t, s)    <- inferExp g' e 
  u             <- unify (substitute s alpha2) (Arrow (substitute s alpha1) t)
  return (Letfun (Bind f (Just $ Ty $ substitute u $ substitute s alpha1 `Arrow` t) (x:[]) e'), 
     substitute u $ substitute s alpha1 `Arrow` t, s <> u)

inferExp g (App (App (Con "Pair") e1) e2) = do
  (e1', t1, s)  <- inferExp g e1
  (e2', t2, s') <- inferExp g e2
  return (App (App (Con "Pair") e1') e2', Prod t1 t2, emptySubst)



-- Apply expression 
inferExp g (App e1 e2) = do 
  alpha             <- fresh 
  (e1', t1, s)      <- inferExp g e1
  (e2', t2, s')     <- inferExp (substGamma s g) e2
  u                 <- unify (substitute s' t1) (Arrow t2 alpha)
  return (App e1' e2', substitute u alpha, u <> s' <> s)

-- If expression
inferExp g (If e e1 e2) = do 
  (e', t, s)  <- inferExp g e
  u           <- unify t (Base Bool)
  case substitute (u <> s) t of 
    Base Bool   -> do
      (e1', t1, s1)   <- inferExp (substGamma (u <> s) g) e1
      (e2', t2, s2)   <- inferExp (substGamma (u <> s <> s1) g) e2
      u'              <- unify (substitute s2 t1) t2 
      return ((If e' e1' e2'), substitute u' t2, u' <> s2 <> s1 <> u <> s)
    t           -> typeError $ TypeMismatch (Base Bool) t


-- -- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  alphaL          <- fresh
  alphaR          <- fresh
  (e', t, s)      <- inferExp g e
  let gl = g `E.add` (y, Ty alphaL)
  (e1', tl, s1)   <- inferExp gl e1
  let gr = g `E.add` (x, Ty alphaR)
  (e2', tr, s2)   <- inferExp (substGamma s1 gr) e2
  u               <- unify (substitute (s2 <> s1 <> s) (Sum alphaL alphaR)) (substitute (s2 <> s1) t)
  u'              <- unify (substitute (u <> s2) tl) (substitute u tr)
  return (Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2'], substitute (u' <> u) tr, u' <> u <> s2 <> s1 <> s)

inferExp g (Case e _) = typeError MalformedAlternatives

inferExp g _ = error "inferExp: Implement me!"


