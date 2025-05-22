module MoreFree where

-- Martin-Löf's W-type

data General (S : Set) (T : S → Set) (X : Set) : Set where
  !!   : X → General S T X
  _??_ : (s : S ) → (T s → General S T X ) → General S T X

infixr 5 _??_

fold : ∀ {l S T X } {Y : Set l} →
  (X → Y) → ((s : S ) → (T s → Y ) → Y ) → General S T X → Y
fold r c (!! x ) = r x
fold r c (s ?? k ) = c s λ t → fold r c (k t)

_G>=_ : ∀ {S T X Y} -> General S T X ->
      (X -> General S T Y) -> General S T Y
g G>= k  = fold k _??_ g

infixl 4 _G>=_
