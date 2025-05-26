{-# OPTIONS --polarity #-}
module PolarFree where

data FreeT (F M : @++ Set → Set) (A : Set) : Set
data FreeF (F M : @++ Set → Set) (A : Set) : Set

data FreeT F M A where
  freeT : M (FreeF F M A) → FreeT F M A

data FreeF F M A where
  freeF : F (FreeT F M A) → FreeF F M A
  pureF : A → FreeF F M A

