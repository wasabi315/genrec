{-# LANGUAGE ScopedTypeVariables #-}
module GenRec.Direct where

import GHC.Exts (inline)
import GenRec.Class (MonadRec, RecProg')

import GenRec.Class

newtype Direct i o a = Direct{unDirect :: (i -> o) -> a}

runDirect :: forall i o . RecProg' (Direct i o) i o -> i -> o
runDirect f = go
  where
    go :: i -> o
    go x = unDirect (f x) go

{-# INLINE runDirect #-}

runDirectInline :: forall i o . RecProg' (Direct i o) i o -> i -> o
runDirectInline f = go
  where
    go :: i -> o
    go x = unDirect (inline f x) go

{-# INLINE runDirectInline #-}

runDirectOpen ::
              forall i o . RecProg' (Direct i o) i o -> (i -> o) -> i -> o
runDirectOpen f self x = unDirect (f x) self

pureDirect :: a -> Direct i o a
pureDirect x = Direct (\ _ -> x)

bindDirect :: Direct i o a -> (a -> Direct i o b) -> Direct i o b
bindDirect m k
  = Direct (\ self -> unDirect (k (unDirect m self)) self)

instance Functor (Direct i o) where
    fmap = \ f m -> bindDirect m (pureDirect . f)

instance Applicative (Direct i o) where
    pure = pureDirect
    (<*>) = \ mf m -> bindDirect mf (<$> m)

instance Monad (Direct i o) where
    (>>=) = bindDirect

instance MonadRec i o (Direct i o) where
    recurse x = Direct (\ self -> self x)

