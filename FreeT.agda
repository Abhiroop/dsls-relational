module FreeT where

-- There are representations that do not require giving up the positivity checks
-- https://pure.tudelft.nl/admin/files/123355176/RP_Paper.pdf

{-@ A Free Monad Transformer @-}

{-# NO_POSITIVITY_CHECK #-}
mutual
  data FreeT (F : Set → Set) (M : Set → Set) (A : Set) : Set where
    freeT : M (FreeF F M A) → FreeT F M A

  data FreeF (F : Set → Set) (M : Set → Set) (A : Set) : Set where
    pureF : A → FreeF F M A
    freeF : F (FreeT F M A) → FreeF F M A

runFreeT : ∀ {F M A} → FreeT F M A → M (FreeF F M A)
runFreeT (freeT m) = m

