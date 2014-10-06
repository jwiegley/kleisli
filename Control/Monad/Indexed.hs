{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}

module Control.Monad.Indexed where

type (s :: k -> *) :-> (t :: k -> *) = forall (x :: k). s x -> t x

class IFunctor (f :: (i -> *) -> o -> *) where
    imap :: (s :-> t) -> f s :-> f t

data Path :: ((i,i) -> *) -> (i,i) -> * where
    Stop :: Path g '(i,i)
    (:-:) :: g '(i,j) -> Path g '(j,k) -> Path g '(i,k)

instance IFunctor Path where
    imap f Stop = Stop
    imap f (r :-: rs) = f r :-: imap f rs

data (:=) :: * -> x -> x -> * where
    V :: a -> (a := k) k

type List a = Path (a := '((),())) '((),())

class IFunctor m => IMonad (m :: (i -> *) -> i -> *) where
    iskip :: p :-> m p
    iextend :: (p :-> m q) -> (m p :-> m q)

iseq :: IMonad m => (p :-> m q) -> (q :-> m r) -> p :-> m r
iseq f g = iextend g . f

(?>=) :: IMonad m => m p i -> (p :-> m q) -> m q i
c ?>= f = iextend f c

(=>=) :: IMonad m => m (a := j) i -> (a -> m q j) -> m q i
c =>= f = c ?>= \(V a) -> f a

type Atkey m i j a = m (a := j) i

ireturn :: IMonad m => a -> Atkey m i i a
ireturn a = iskip (V a)

data (p :>>: q) r i = p i :& (q :-> r)

instance IFunctor (p :>>: q) where
    imap h (p :& k) = p :& (h . k)

data (f :+: g) p i = InL (f p i) | InR (g p i)

instance (IFunctor f , IFunctor g) => IFunctor (f :+: g) where
    imap h (InL fp) = InL (imap h fp)
    imap h (InR gp) = InR (imap h gp)

data (:*) :: ((i -> *) -> i -> *) -> (i -> *) -> i -> * where
    Ret :: p i -> (f :* p) i
    Do  :: f (f :* p) i -> (f:* p) i

instance IFunctor f => IMonad ((:*) f) where
    iskip = Ret

    iextend g (Ret p) = g p
    iextend g (Do ffp) = Do (imap (iextend g) ffp)

instance IFunctor f => IFunctor ((:*) f) where
    imap f = iextend (iskip . f)

class IFunctor m => IApplicative (m :: (i -> *) -> i -> *) where
    ipure :: x -> Atkey m k k x
    (<**>) :: Atkey m j k (s -> t) -> Atkey m k l s -> Atkey m j l t

instance IFunctor f => IApplicative ((:*) f) where
    ipure = ireturn
    mf <**> ms = mf =>= \f -> ms =>= \s -> ireturn (f s)

data State :: * where
    Open ::State
    Closed :: State

newtype TConst i j = TConst i

type FH = ((FilePath := 'Closed) :>>: TConst State)
      :+: (() := 'Open :>>: (Maybe Char :='Open))
      :+: (() := 'Open :>>: (() := 'Closed))

-- pattern FOpen p k = Do (InL (V p :& k))
-- pattern FGetC   k = Do (InR (InL (V () :& k)))
-- pattern FClose  k = Do (InR (InR (V () :& k)))

-- fOpen :: FilePath -> (FH :* (TConst State)) 'Closed 
-- fOpen p = FOpen p Ret

-- fGetC :: (FH:* (Maybe Char := 'Open)) 'Open
-- fGetC = FGetC Ret

-- fClose :: (FH:* (() := 'Closed)) 'Open
-- fClose = FClose Ret
