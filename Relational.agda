module Relational where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import FreeT
import State as S
import Identity as I

equivalence : ∀ {A} →
  (stk : I.Stack) → (rs : I.Registers) → (p₁ : FreeT I.AssemblyF I.Identity A) →
  (ms : S.MachineState) → (p₂ : FreeT S.AssemblyF S.MS A) →
  (I.runAssembly p₁ stk rs  ≡ S.evalState (S.runAssembly ms p₂) ms)
equivalence stk rs p₁ ms p₂ = ?

