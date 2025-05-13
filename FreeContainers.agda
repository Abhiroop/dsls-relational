module FreeContainers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

{-# NO_POSITIVITY_CHECK #-}
-- data Free (F : Set → Set) (A : Set) : Set where
--   pure   : A → Free F A
--   impure : F (Free F A) → Free F A

data Ext (Shape : Set) (Pos : Shape → Set) (A : Set) : Set where
  ext : (s : Shape) → (Pos s → A) → Ext Shape Pos A

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

Zero : Set → Set
Zero A = ⊥

One : Set → Set
One A = ⊤

Shape_One : Set
Shape_One = ⊤

Pos_One : Shape_One → Set
Pos_One s = ⊥

Ext_One : Set → Set
Ext_One A = Ext Shape_One Pos_One A

to_One : ∀ {A : Set} → Ext_One A → One A
to_One _ = tt

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim () -- absurd

from_One : ∀ {A : Set} → One A → Ext_One A
from_One z = ext tt (λ p → ⊥-elim p)

-- to_from_One : ∀ {A : Set} → (ox : One A) → to_One (from_One ox) ≡ ox
-- to_from_One {A} tt = refl

record Container (F : Set → Set) : Set₁ where
  field
    Shape   : Set
    Pos     : Shape → Set
    to      : ∀ {A : Set} → Ext Shape Pos A → F A
    from    : ∀ {A : Set} → F A → Ext Shape Pos A
    to-from : ∀ {A : Set} (fa : F A) → to (from fa) ≡ fa
    from-to : ∀ {A : Set} (e  : Ext Shape Pos A) → from (to e) ≡ e

open Container public

data Free {F : Set → Set} (C : Container F) (A : Set) : Set where
  pure : A → Free C A
  impure : Ext (Shape C) (Pos C) (Free C A) → Free C A
