module GenRec.Inline where

open import Haskell.Prelude

--------------------------------------------------------------------------------

-- | compiles to GHC.Exts.inline
inline : a → a
inline x = x
