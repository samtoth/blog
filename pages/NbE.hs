{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
import Data.Functor.Identity
import Control.Monad.Reader
import Data.Functor.Constant
import Data.Void
import Data.List.Extra 

data Var where
  Here :: Var
  There :: Var -> Var

data Type b where
  Base :: b -> Type b
  Fun :: Type b -> Type b -> Type b
    deriving Show
data STLC base ax v bind where
    Var   :: v -> STLC base ax v bind
    Lam   :: bind (STLC base ax v bind) -> STLC base ax v bind
    App   :: STLC base ax v bind -> STLC base ax v bind -> STLC base ax v bind
    Axiom :: ax base -> STLC base ax v bind

data VarGen v a = Bind (v -> a)

type ShallowSTLC b a v = STLC b a v (Reader v)

sLam :: (v -> ShallowSTLC b a v) -> ShallowSTLC b a v
sLam f = Lam (ReaderT $ \v -> Identity $ f v)

sExample :: ShallowSTLC () (Constant Void) v
sExample = sLam (\var -> Var var)

-- take a shallowly embeded representation of an STLC term and make it deep
-- sink :: ShallowSTLC base ax v -> DeepSTLC base ax
-- sink = helper 0
--   where
--     helper :: Int -> _ -> _
--     helper lvl (Var v) = _

-- liftVar = _

type DeepSTLC b a = STLC b a Var Identity


instance Show Var where
    show = show . toInt

instance Show (a b) => Show (DeepSTLC b a) where
    show (Var v) = "v" <> show v
    show (Lam (Identity b)) = "(\\. " <> show b <> ")"
    show (App f a) = "(" <> show f <> " " <> show a <> ")"
    show (Axiom a) = show a


dId :: DeepSTLC b a
dId = Lam (Identity $ Var Here)

-- sink sExample should = dExample

type Env b a = [Norm b a]

data Clos b a = Clos { tm :: DeepSTLC b a, env :: Env b a }

data Norm b a where
    Ne   :: Ne b a -> Type b -> Norm b a
    NLam :: Clos b a -> Norm b a
    NAx  :: a b -> Norm b a

data Ne b a where
    NVar :: Int -> Ne b a
    NAp  :: Ne b a -> (Norm b a , Type b) -> Ne b a

toInt :: Var -> Int
toInt Here = 0
toInt (There v) = toInt v + 1

fromInt :: Int -> Var
fromInt 0 = Here
fromInt n = There (fromInt (n-1))

eval :: DeepSTLC b a -> Env b a -> Maybe (Norm b a)
eval (Var v) env = env !? toInt v
eval (Lam (Identity t)) env = Just . NLam $ Clos t env
eval (App f x) env = eval f env >>= (\a -> eval x env >>= evalAp a)
eval (Axiom a) env = Just $ NAx a

evalAp :: Norm b a -> Norm b a -> Maybe (Norm b a)
evalAp f x = case f of
    NLam (Clos tm env) -> eval tm (x : env)
    Ne ne (Fun t1 t2) -> Just $ Ne (NAp ne (x , t1)) t2
    _ -> Nothing

reify :: Int -> (Norm b a , Type b) -> Maybe (DeepSTLC b a)
reify s (t , Fun t1 t2) = do
    x <- evalAp t (Ne (NVar s) t1)
    xrb <- reify (s + 1) (x , t2)
    return . Lam . Identity $ xrb
reify s (Ne ne _ , Base _) = reifyNe s ne
reify s (NAx a , Base _) = Just $ Axiom a
reify _ _ = Nothing

reifyNe :: Int -> Ne b a -> Maybe (DeepSTLC b a)
reifyNe s (NVar n) = Just . Var . fromInt $ (s - n - 1)
reifyNe s (NAp f a) = App <$> reifyNe s f <*> reify s a

-- a base type base : *
base :: DeepSTLC () (Constant ())
base = Axiom (Constant ())

apId :: DeepSTLC () (Constant ())
apId = App dId base

normalise :: DeepSTLC b a -> Type b -> Maybe (DeepSTLC b a)
normalise t ty = eval t [] >>= (\a -> reify 0 (a , ty))

test :: DeepSTLC () (Constant ())
test =  case normalise apId (Base ()) of Just a -> a

data Ans a where
    Yes :: Ans ()
    No :: Ans ()

instance Show (Ans a) where
    show Yes = "yes"
    show No = "no"

yes, no :: STLC () Ans v bind
yes = Axiom Yes
no = Axiom No

class Inhabited b a | b -> a where
    rep     :: STLC b a v bind
    reprTy  :: Type b

instance Inhabited () Ans where
  rep = yes
  reprTy = Base ()

nat :: Inhabited b a => Type b
nat = Fun (Fun reprTy reprTy) (Fun reprTy reprTy)

zero :: Inhabited b a => DeepSTLC b a
zero = Lam . Identity $ (Lam . Identity $ Var Here)

abstractN :: Int -> ([DeepSTLC b a] -> DeepSTLC b a) -> DeepSTLC b a
abstractN 0 f = f []
abstractN n f = help (n - 1) where
    help 0 = Lam . Identity $ f [Var (fromInt (n-a-1)) | a <- [0..n-1] ]
    help k = Lam . Identity $ help (k - 1)

appN :: Int -> DeepSTLC b a -> [DeepSTLC b a] -> DeepSTLC b a
appN 0 f _ = f
appN 1 f [x] = App f x
appN 1 f _ = error "wrong number of arguments to appN"
appN n f (x:xs) = appN (n-1) (App f x) xs
appN n f _ = error "wrong number of arguments to appN"

app2 :: DeepSTLC b a -> DeepSTLC b a -> DeepSTLC b a -> DeepSTLC b a
app2 f x y = appN 2 f [x,y]

suc :: Inhabited b a => DeepSTLC b a
suc = abstractN 3 (\[n,f,x] -> App f (app2 n f x))

plus :: Inhabited b a => DeepSTLC b a
plus = abstractN 4 (\[m,n,f,x] ->  app2 m f (app2 n f x))

mult :: Inhabited b a => DeepSTLC b a
mult = abstractN 4 (\[m,n,f,x] -> app2 m (App n f) x)

stlcFromInt :: (Inhabited b a, Integral n) => n -> DeepSTLC b a
stlcFromInt n = case toInteger n of
    0 -> zero 
    n -> App suc (stlcFromInt (n-1))

stlcToInt :: Inhabited b a => DeepSTLC b a -> Maybe Integer
stlcToInt (Lam (Identity (Lam (Identity b)))) = help 0 b where
    help n (App (Var (There Here)) b) = help (n+1) b
    help n (Var Here) = Just n
    help _ _ = Nothing
stlcToInt _ = Nothing


instance (Inhabited b a) => Num (DeepSTLC b a) where
  (+) = app2 plus
  (*) = app2 mult
  abs = error ""
  signum = error ""
  fromInteger = stlcFromInt
  (-) = error ""
