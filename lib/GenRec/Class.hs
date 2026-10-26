{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module GenRec.Class
  (Recurse(..), ApplicativeRec(..), MonadRec(..), RecProg')
where

class Recurse i o m where
    recurse :: i -> m o

class (Applicative m, Recurse i o m) => ApplicativeRec i o m where

class (Monad m, Recurse i o m) => MonadRec i o m where

instance (Applicative m, Recurse i o m) => ApplicativeRec i o m
         where

instance (Monad m, Recurse i o m) => MonadRec i o m where

type RecProg' m i o = i -> m o

