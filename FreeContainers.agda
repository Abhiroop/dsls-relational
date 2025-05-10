module FreeContainers where

{-# NO_POSITIVITY_CHECK #-}
data Free (F : Set → Set) (A : Set) : Set where
  pure   : A → Free F A
  impure : F (Free F A) → Free F A

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

