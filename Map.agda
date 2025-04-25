module Map where

open import Data.List using (List; []; _∷_; head; tail)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool.Base
open import Data.String using (String)
open import Data.String.Properties as StringProps
open import Data.Nat.Properties as NatProps
open import Relation.Nullary.Decidable using (does)

-- A key-value pair map as a list of pairs
Map : Set → Set → Set
Map K V = List (K × V)

-- Lookup function
lookup : {K V : Set} → (eq : K → K → Bool) → K → Map K V → Maybe V
lookup eq k [] = nothing
lookup eq k ((k₁ , v) ∷ xs) with eq k k₁
... | true = just v
... | false = lookup eq k xs

insert : {K V : Set} → (eq : K → K → Bool) → K → V → Map K V → Map K V
insert eq k v [] = (k , v) ∷ []
insert eq k v ((k₁ , v₁) ∷ xs) with eq k k₁
... | true  = (k , v) ∷ xs           -- replace existing key
... | false = (k₁ , v₁) ∷ insert eq k v xs  -- recurse

-- Example with Strings and Nat
open import Data.Nat using (ℕ; zero; suc; _≟_)

exampleMap : Map String ℕ
exampleMap = ("foo" , 1) ∷ ("bar" , 2) ∷ []

exampleMap2 : Map ℕ ℕ
exampleMap2 = (5 , 1) ∷ (6 , 2) ∷ []


-- Use a string equality function (not built-in)
stringEq : String → String → Bool
stringEq = _==_

_=ℕ=_ : ℕ → ℕ → Bool
_=ℕ=_ = λ x y → does (NatProps._≟_ x y)


findWithDefault : {K V : Set} → (eq : K → K → Bool) → K → V → Map K V → V
findWithDefault eq k defv m with lookup eq k m
... | just v = v
... | nothing = defv

defaultHead : ℕ → List ℕ → ℕ
defaultHead def l with head l
... | just v = v
... | nothing = def

defaultTail : List ℕ → List ℕ
defaultTail l with tail l
... | just v = v
... | nothing = []

-- Example lookup
exampleLookup : Maybe ℕ
exampleLookup = lookup stringEq "foo" exampleMap

exampleLookup2 : Maybe ℕ
exampleLookup2 = lookup (_=ℕ=_) 5 exampleMap2
