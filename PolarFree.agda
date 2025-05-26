{-# OPTIONS --polarity #-}
module PolarFree where

data FreeT (F M : @++ Set → Set) (A : Set) : Set
data FreeF (F M : @++ Set → Set) (A : Set) : Set

data FreeT F M A where
  freeT : M (FreeF F M A) → FreeT F M A

data FreeF F M A where
  freeF : F (FreeT F M A) → FreeF F M A
  pureF : A → FreeF F M A

record SPosFunctor (F : @++ Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

open SPosFunctor public

record SPosMonad (M : @++ Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

open SPosMonad public

open SPosMonad {{...}} using (_>>=_ ; return)
open SPosFunctor {{...}} using (fmap)

iterT : ∀ {F M : @++ Set → Set} {A : Set}
          {{ functor : SPosFunctor F }}
          {{ monad   : SPosMonad M }}
      → (F (M A) → M A) → FreeT F M A → M A
iterT alg ft = {!!}

-- SPosMonad._>>=_ monad x λ where
--     pure a    → SPosMonad.return monad a
--     free fmfa → alg (fmap (iterT monad alg) fmfa)


--   let
--     open SPosFunctor functor using (fmap)
--     open SPosMonad   monad   using (return; _>>=_)
--   in x >>= λ where
--     pureF x  → ? -- return x
--     freeF fx → ? -- alg (fmap (iterT functor monad alg) fx)
