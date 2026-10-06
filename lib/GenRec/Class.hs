{-# LANGUAGE MultiParamTypeClasses #-}
module GenRec.Class where

class Monad m => MonadRec i o m where
    recurse :: i -> m o

type RecProg' m i o = i -> m o

