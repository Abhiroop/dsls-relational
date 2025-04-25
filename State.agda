module State where

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; id)

open import FreeT
open import Map

open import Agda.Primitive        using (Level; lzero; _⊔_)
open import Data.Product          using (_×_; _,_; proj₁; proj₂)
open import Data.Unit             using (⊤; tt)
open import Function              using (id)



-- The type of stateful computations:
--   State S A  ≡ S → A × S
State : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
State S A = S → A × S

returnState : ∀ {ℓ₁ ℓ₂} {S : Set ℓ₁} {A : Set ℓ₂}
            → S → A → State S A
returnState s a = λ _ → a , s

pureState : ∀ {ℓ₁ ℓ₂} {S : Set ℓ₁} {A : Set ℓ₂} → A → State S A
pureState a = λ s → a , s

runState
  : ∀ {ℓ₁ ℓ₂} {S : Set ℓ₁} {A : Set ℓ₂}
  → State S A
  → S
  → A × S
runState m s = m s

evalState
  : ∀ {ℓ₁ ℓ₂} {S : Set ℓ₁} {A : Set ℓ₂}
  → State S A
  → S
  → A
evalState m s = proj₁ (runState m s)


execState
  : ∀ {ℓ₁ ℓ₂} {S : Set ℓ₁} {A : Set ℓ₂}
  → State S A
  → S
  → S
execState m s = proj₂ (runState m s)

_>>=State_ : ∀ {ℓ₁ ℓ₂ ℓ₃}
           {S : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
           → State S A
           → (A → State S B)
           → State S B
m >>=State f = λ s →
  let (a , s′) = m s
  in  f a s′

-- get the current state
get : ∀ {ℓ} {S : Set ℓ} → State S S
get = λ s → s , s

-- set the state to s (and return trivial tt)
put : ∀ {ℓ} {S : Set ℓ} → S → State S ⊤
put s = λ _ → tt , s

infixl 1 _>>=State_

modify : ∀ {ℓ} {S : Set ℓ} → (S → S) → State S ⊤
modify f = get >>=State λ s → put (f s)


Register : Set
Register = ℕ

Stack : Set
Stack = List ℕ

Registers : Set
Registers = Map Register ℕ

data AssemblyF (next : Set) : Set where
  Push  : Register → next → AssemblyF next
  Store : Register → next → AssemblyF next
  Ret   : (ℕ → next) → AssemblyF next
  Add   : Register → Register → Register → next → AssemblyF next
  Mul   : Register → Register → Register → next → AssemblyF next


mapAssemblyF : ∀ {A B} → (A → B) → AssemblyF A → AssemblyF B
mapAssemblyF f (Push r a)       = Push r (f a)
mapAssemblyF f (Store r a)      = Store r (f a)
mapAssemblyF f (Ret g)          = Ret (f ∘ g)
mapAssemblyF f (Add r1 r2 r3 a) = Add r1 r2 r3 (f a)
mapAssemblyF f (Mul r1 r2 r3 a) = Mul r1 r2 r3 (f a)


MachineState : Set
MachineState = Stack × Registers

MS : Set → Set
MS = State MachineState

stack : Stack
stack = []

insertI : ℕ → ℕ → Map ℕ ℕ → Map ℕ ℕ
insertI = insert (_=ℕ=_)

registers : Registers
registers = insertI 2 5 (insertI 1 6 [])

machineSt : MachineState
machineSt = stack , registers

pureT : ∀ {A} → A → FreeT AssemblyF MS A
pureT a = freeT (returnState machineSt (pureF a))


liftF : ∀ {A} → AssemblyF A → FreeT AssemblyF MS A
liftF fa =  freeT (returnState machineSt (freeF (mapAssemblyF pureT fa)))

push : Register → FreeT AssemblyF MS ⊤
push r = liftF (Push r tt)

store : Register → FreeT AssemblyF MS ⊤
store r = liftF (Store r tt)

ret : FreeT AssemblyF MS ℕ
ret = liftF (Ret λ z → z)

add : Register → Register → Register → FreeT AssemblyF MS ⊤
add r1 r2 r3 = liftF (Add r1 r2 r3 tt)

mul : Register → Register → Register → FreeT AssemblyF MS ⊤
mul r1 r2 r3 = liftF (Mul r1 r2 r3 tt)

{-# TERMINATING #-}
_>>=_ : ∀ {A B} → FreeT AssemblyF MS A → (A → FreeT AssemblyF MS B) → FreeT AssemblyF MS B
_>>=_ {A} {B} (freeT x) f = freeT (x >>=State helper)
  where
    helper : FreeF AssemblyF MS A → MS (FreeF AssemblyF MS B)
    helper (pureF a)  = runFreeT (f a)
    helper (freeF fa) = pureState (freeF (mapAssemblyF (λ ft' → ft' >>= f) fa))

_>>_ : ∀ {A B} → FreeT AssemblyF MS A → FreeT AssemblyF MS B → FreeT AssemblyF MS B
_>>_ fa fb = fa >>= (λ _ → fb)


runAssembly : ∀ {A} → FreeT AssemblyF MS A → MS A
runAssembly (freeT x) = {!!}

-- runAssembly : ∀ {A} → FreeT AssemblyF MS A → A
-- runAssembly (freeT x) = runAssembly' x
--   where
--   runAssembly' : ∀ {A} → FreeF AssemblyF MS A → A
--   runAssembly' (pureF x) = x
--   runAssembly' (freeF (Push r k)) =
--     let val = findWithDefault (_=ℕ=_) r 0 regs
--      in runAssembly k (val ∷ stack) regs
--   runAssembly' (freeF (Store r k)) stack regs =
--     let regs' = insert (_=ℕ=_) r (defaultHead 0 stack) regs
--      in runAssembly k (defaultTail stack) regs'
--   runAssembly' (freeF (Ret k)) stack regs =
--     let v = defaultHead 0 stack
--      in runAssembly (k v) stack regs
--   runAssembly' (freeF (Add r₁ r₂ r₃ k)) stack regs =
--     let v₁ = findWithDefault (_=ℕ=_) r₁ 0 regs
--         v₂ = findWithDefault (_=ℕ=_) r₂ 0 regs
--         regs' = insert (_=ℕ=_) r₃ (v₁ + v₂) regs
--      in runAssembly k stack regs'
--   runAssembly' (freeF (Mul r₁ r₂ r₃ k)) stack regs =
--     let v₁ = findWithDefault (_=ℕ=_) r₁ 0 regs
--         v₂ = findWithDefault (_=ℕ=_) r₂ 0 regs
--         regs' = insert (_=ℕ=_) r₃ (v₁ * v₂) regs
--      in runAssembly k stack regs'

prog : FreeT AssemblyF MS ℕ
prog = do
  push 1
  push 2
  add 1 2 3
  push 3
  ret
