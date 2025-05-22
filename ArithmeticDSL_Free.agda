-- Arithmetic DSLs with Free Monad in Agda
-- We define two simple arithmetic DSL signatures, embed them via the Free monad,
-- and prove that their evaluators coincide on all programs.

{-# OPTIONS --without-K --safe #-}
module ArithmeticDSL_Free where

open import Agda.Primitive
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- 1. Free Monad Definition
------------------------------------------------------------------------

-- A minimal Free monad over a signature functor F

record FunctorF (F : Set → Set) : Set₁ where
  field
    map : ∀ {A B} → (A → B) → F A → F B

open FunctorF public

-- Free monad

data Free {ℓ} (F : Set ℓ → Set ℓ) : Set ℓ → Set ℓ where
  pure  : {A : Set ℓ} → A → Free F A
  impure : {A : Set ℓ} → F (Free F A) → Free F A

instance
  functorFree : ∀ {ℓ} {F : Set ℓ → Set ℓ} → FunctorF F → FunctorF (Free F)
  functorFree {F = F} Ff = record { map = λ {A B} f → go f }
    where
      go : ∀ {A B} → (A → B) → Free F A → Free F B
      go _ (pure x)  = pure x
      go f (impure fx) = impure (map Ff (go f) fx) {F = F} Ff = record { map = λ {A B} f → go }
    where
      go : Free F A → Free F B
      go (pure x) = pure (f x)
      go (impure fx) = impure (map Ff (go) fx)

------------------------------------------------------------------------
-- 2. First Arithmetic DSL: Add and Mul
------------------------------------------------------------------------

-- Signature for arithmetic operations

data ArithSig (A : Set) : Set where
  lit  : ℕ → ArithSig A
  add  : A → A → ArithSig A
  mul  : A → A → ArithSig A

-- Functor instance

funArith : FunctorF ArithSig
funArith = record
  { map = λ {A B} f op →
      case op of λ where
        lit n     → lit n
        add x y   → add (f x) (f y)
        mul x y   → mul (f x) (f y)
  }

-- DSL as Free ArithSig

Expr : Set → Set
Expr = Free ArithSig

-- Smart constructors

litF : ∀ {A} → ℕ → Expr A
litF n = impure (lit n)

addF : ∀ {A} → Expr A → Expr A → Expr A
addF x y = impure (add x y)

mulF : ∀ {A} → Expr A → Expr A → Expr A
mulF x y = impure (mul x y)

------------------------------------------------------------------------
-- 3. Second Arithmetic DSL: Church-encoded
------------------------------------------------------------------------

-- Another signature with same semantics but different constructors

data ArithSig₂ (A : Set) : Set where
  const : ℕ → ArithSig₂ A
  plus  : A → A → ArithSig₂ A
  times : A → A → ArithSig₂ A

funArith₂ : FunctorF ArithSig₂
funArith₂ = record
  { map = λ {A B} f op →
      case op of λ where
        const n     → const n
        plus x y    → plus (f x) (f y)
        times x y   → times (f x) (f y)
  }

Expr₂ : Set → Set
Expr₂ = Free ArithSig₂

constF : ∀ {A} → ℕ → Expr₂ A
constF n = impure (const n)

plusF : ∀ {A} → Expr₂ A → Expr₂ A → Expr₂ A
plusF x y = impure (plus x y)

timesF : ∀ {A} → Expr₂ A → Expr₂ A → Expr₂ A
timesF x y = impure (times x y)

------------------------------------------------------------------------
-- 4. Interpreters
------------------------------------------------------------------------

-- Interpreter for Expr

eval : Expr ℕ → ℕ
eval (pure n)       = n
eval (impure op)    =
  case op of λ where
    lit n      → n
    add x y    → eval x + eval y
    mul x y    → eval x * eval y

-- Interpreter for Expr₂

eval₂ : Expr₂ ℕ → ℕ
eval₂ (pure n)      = n
eval₂ (impure op)   =
  case op of λ where
    const n    → n
    plus x y   → eval₂ x + eval₂ y
    times x y  → eval₂ x * eval₂ y

------------------------------------------------------------------------
-- 5. Embedding translation from Expr to Expr₂
------------------------------------------------------------------------

-- Translate signature operations

transOp : ∀ {A} → ArithSig (Free ArithSig A) → Free ArithSig₂ A
transOp (lit n)     = impure (const n)
transOp (add x y)   = impure (plus (translate x) (translate y))
transOp (mul x y)   = impure (times (translate x) (translate y))

-- Translate whole program

translate : ∀ {A} → Expr A → Expr₂ A
translate (pure a)  = pure a
translate (impure op)= transOp op

------------------------------------------------------------------------
-- 6. Equivalence Proof
------------------------------------------------------------------------

-- For all expressions e in Expr ℕ, eval e ≡ eval₂ (translate e)

lem : ∀ (e : Expr ℕ) → eval e ≡ eval₂ (translate e)
lem (pure n) = refl
lem (impure op) with lemArgs op
... | lemma = lemma
  where
  -- Auxiliary lemma on signature operations
  lemArgs : ∀ (op : ArithSig (Expr ℕ)) → eval (impure op) ≡ eval₂ (translate (impure op))
  lemArgs (lit n)  = refl
  lemArgs (add x y) =
    cong₂ _+_ (lem x) (lem y)
  lemArgs (mul x y) =
    cong₂ _×_ (lem x) (lem y)

-- cong₂ helper
cong₂ : ∀ {A B C} {f : A → B → C} → (x ≡ x') → (y ≡ y') → f x y ≡ f x' y'
cong₂ refl refl = refl

-- End of file

