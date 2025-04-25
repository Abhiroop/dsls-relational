module FreeT where

open import Data.Container
open import Level as L

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Bool using (if_then_else_)
open import Function using (_∘_; id)

open import Map using (Map; lookup; insert; _=ℕ=_; findWithDefault; defaultHead; defaultTail)
import Relation.Binary.PropositionalEquality as PEq
open PEq using (_≡_; refl; cong; cong-app)



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

