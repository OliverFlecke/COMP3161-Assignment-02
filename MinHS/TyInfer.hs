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
      -- error $ "No unifer for the base types " <> (show t1) <> " and " <> (show t2)
unify (Prod t11 t12) (Prod t21 t22) = do
  s     <- unify t11 t12
  s'    <- unify (substitute s t12) (substitute s t22)
  return $ s <> s'
unify (Sum t11 t12) (Sum t21 t22) = unify (Prod t11 t12) (Prod t21 t22)
unify (Arrow t11 t12) (Arrow t21 t22) = do
  s     <- unify t11 t21 
  s'    <- unify t12 t22
  return $ s <> s'
-- Still missing a check to see if v is in t !!!
unify (TypeVar v) t = return $ v =: t
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


-- Helper function 


-- Infer program
inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env [Bind name _ [] exp] = do 
  (e, t, s) <- inferExp env exp 
  return ([Bind name (Just $ Ty t) [] e], t, s)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the entire expression using allTypes from Syntax.hs"


-- Infer expression
inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g (Num n) = return (Num n, Base Int, emptySubst)
inferExp g (Con var) = 
  case constType var of 
    Just (Ty t)   -> return (Con var, t, emptySubst)
    Nothing       -> typeError $ NoSuchVariable var 

inferExp g (Var v) = 
  case E.lookup g v of 
    Just (Ty t)   -> return (Var v, t, emptySubst)
    Nothing       -> error "Varible not in gamma" 
inferExp g (App (Prim Neg) n) = 
  case primOpType Neg of 
    Ty (Base Int `Arrow` Base Int)  
          -> return ((App (Prim Neg) n), Base Int, emptySubst) 
    Ty t  -> typeError $ TypeMismatch (Base Int) t
-- inferExp g (App (App (Prim op) (Var v1)) (Var v2)) = error "We are here"
-- inferExp g (App (App (Prim op) (Var v1)) (Var v2)) = 
--   case primOpType op of 
--     Ty t  -> return (App (App (Prim op) (Var v1) (Var v2)), t, emptySubst)
--     _     -> error "Operator not supported"
inferExp g (App (App (Prim op) e1) e2) = 
  case primOpType op of 
    Ty (Base Int `Arrow` (Base Int `Arrow` Base t)) -> 
      case (e1, e2) of 
        (Var x, Var y) | x == y -> 
          case E.lookup g x of 
            Just (Ty (TypeVar a)) -> return (e, Base t, a =: (Base Int))
            Nothing               -> return (e, Base t, x =: (Base Int))
        (Var x, Var y)  -> 
          case (E.lookup g x, E.lookup g y) of 
            (Just (Ty (TypeVar a)), Just (Ty (TypeVar b)))  -> 
              return (e, Base t, a =: (Base Int) <> b =: (Base Int))
            (Just (Ty (TypeVar a)), Nothing)                -> 
              return (e, Base t, a =: (Base Int) <> y =: (Base Int)) 
            (Nothing, Just (Ty (TypeVar b)))                ->
              return (e, Base t, x =: (Base Int) <> b =: (Base Int))
            (Nothing, Nothing)                              -> 
              return (e, Base t, x =: (Base Int) <> y =: (Base Int)) 
        (Var x, _)      -> 
          case E.lookup g x of 
            Just (Ty (TypeVar a)) -> return (e, Base t, a =: (Base Int))
            Nothing               -> return (e, Base t, x =: (Base Int))
        (_, Var x)      -> 
          case E.lookup g x of 
            Just (Ty (TypeVar a)) -> return (e, Base t, a =: (Base Int))
            Nothing               -> return (e, Base t, x =: (Base Int))
        (_, _)          -> return (e, Base t, emptySubst)
    _   -> error "Prim operator not yet supported"
  where 
    e = App (App (Prim op) e1) e2
        -- case (e1, e2) of 
        --       (Var x, Var y) | x == y -> 
        --         return (App (App (Prim op) e1) e2, Base Int `Arrow` Base t, emptySubst)
        --       (Var _, Var _)    -> 
        --         return (App (App (Prim op) e1) e2, Base Int `Arrow` (Base Int `Arrow` Base t), emptySubst)
        --       (Var _, _)        -> 
        --         return (App (App (Prim op) e1) e2, Base Int `Arrow` Base t, emptySubst)
        --       (_, Var _)        -> 
        --         return (App (App (Prim op) e1) e2, Base Int `Arrow` Base t, emptySubst)
        --       (_, _)            -> 

inferExp g (Let [Bind n _ [] e1] e2) = do
  (e1', t1, s1)  <- inferExp g e1 
  (e2', t2, s2)  <- inferExp (substGamma s1 (E.add g (n, generalise (substGamma s1 g) t1))) e2 
  return ((Let [Bind n (Just $ Ty t1) [] e1'] e2'), t2, s1 <> s2) 

-- Should be working
inferExp g (Letfun (Bind n _ (v:vs) e)) = do
  x             <- fresh
  f             <- fresh
  (e', t, s)    <- inferExp (g `E.addAll` [(v, Ty x), (n, Ty f)]) e 
  un            <- unify (substitute s f) (Arrow (substitute s x) t)
  return (Letfun (Bind n (Just $ Ty (substitute un f)) (v:vs) e'), 
      substitute un f, s <> un)
  -- error $ "Letfun expression type: " 
  --   <> "\nName x: " <> (show v) <> " Type: " <> (show (Arrow x t)) 
  --   <> "\nName f: " <> (show n) <> " Type: " <> (show f)
  --   <> "\nOutput type: " <> (show (substitute (un <> s) f)) 
  --   <> "\n\nEnvironment " <> (show (g `E.addAll` [(v, Ty x), (n, Ty f)]))
  --   <> "\noutput " <> (show (s))
  --   <> "\nun " <> (show un) 
  --   <> "\nX substituted " <> (show (substitute s x))





inferExp g (App e1 e2) = do 
  a                 <- fresh -- Don't know why I can't just put this instead of a at the end (gives wrong type)
  (e1', t1, s)      <- inferExp g e1
  (e2', t2, s')     <- inferExp (substGamma s g) e2
  -- error $ "Apply infering between " <> (show t1) <> " and " <> (show $ Arrow t2 a) 
  s''               <- unify (substitute s' t1) (Arrow t2 a)
  return (App e1' e2', a, s <> s' <> s'')

inferExp g (If b e1 e2) = do 
  (b', bt, bs)  <- inferExp g b
  u             <- unify bt (Base Bool)
  case substitute (u <> bs) bt of 
    Base Bool   -> do
      (e1', t1, s1)   <- inferExp (substGamma (u <> bs) g) e1
      (e2', t2, s2)   <- inferExp (substGamma (u <> bs <> s1) g) e2
      t               <- unify (substitute (s2) t1) t2 
      return ((If b' e1' e2'), t2, t <> s1 <> s2)
    t           -> typeError $ TypeMismatch (Base Bool) bt



inferExp g _ = error "inferExp: Implement me!"
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


