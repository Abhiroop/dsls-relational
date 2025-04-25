module Identity where

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; _+_; _*_)
open import Function using (_∘_; id)

open import FreeT
open import Map using (Map; lookup; insert;
                      _=ℕ=_; findWithDefault;
                      defaultHead; defaultTail)

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

Identity : Set → Set
Identity A = A

returnIdentity : ∀ {A} → A → Identity A
returnIdentity = id

_>>=Identity_ : ∀ {A B} → Identity A → (A → Identity B) → Identity B
m >>=Identity f = f m

pureT : ∀ {A} → A → FreeT AssemblyF Identity A
pureT a = freeT (returnIdentity (pureF a))

liftF : ∀ {A} → AssemblyF A → FreeT AssemblyF Identity A
liftF fa = freeT (returnIdentity (freeF (mapAssemblyF pureT fa)))

data ⊤ : Set where
  tt : ⊤

push : Register → FreeT AssemblyF Identity ⊤
push r = liftF (Push r tt)

store : Register → FreeT AssemblyF Identity ⊤
store r = liftF (Store r tt)

ret : FreeT AssemblyF Identity ℕ
ret = liftF (Ret λ z → z)

add : Register → Register → Register → FreeT AssemblyF Identity ⊤
add r1 r2 r3 = liftF (Add r1 r2 r3 tt)

mul : Register → Register → Register → FreeT AssemblyF Identity ⊤
mul r1 r2 r3 = liftF (Mul r1 r2 r3 tt)

{-# TERMINATING #-}
_>>=_ : ∀ {A B} → FreeT AssemblyF Identity A → (A → FreeT AssemblyF Identity B) → FreeT AssemblyF Identity B
_>>=_ {A} {B} (freeT x) f = helper x
  where
    helper : FreeF AssemblyF Identity A → FreeT AssemblyF Identity B
    helper (pureF a) = f a
    helper (freeF fa) = freeT (freeF (mapAssemblyF (λ ft' → ft' >>= f) fa))


_>>_ : ∀ {A B} → FreeT AssemblyF Identity A → FreeT AssemblyF Identity B → FreeT AssemblyF Identity B
_>>_ fa fb = fa >>= (λ _ → fb)

runAssembly : ∀ {A} → FreeT AssemblyF Identity A → Stack → Registers → A
runAssembly (freeT x) stack regs = runAssembly' x stack regs
  where
  runAssembly' : ∀ {A} → FreeF AssemblyF Identity A → Stack → Registers → A
  runAssembly' (pureF x) stack regs = x
  runAssembly' (freeF (Push r k)) stack regs =
    let val = findWithDefault (_=ℕ=_) r 0 regs
     in runAssembly k (val ∷ stack) regs
  runAssembly' (freeF (Store r k)) stack regs =
    let regs' = insert (_=ℕ=_) r (defaultHead 0 stack) regs
     in runAssembly k (defaultTail stack) regs'
  runAssembly' (freeF (Ret k)) stack regs =
    let v = defaultHead 0 stack
     in runAssembly (k v) stack regs
  runAssembly' (freeF (Add r₁ r₂ r₃ k)) stack regs =
    let v₁ = findWithDefault (_=ℕ=_) r₁ 0 regs
        v₂ = findWithDefault (_=ℕ=_) r₂ 0 regs
        regs' = insert (_=ℕ=_) r₃ (v₁ + v₂) regs
     in runAssembly k stack regs'
  runAssembly' (freeF (Mul r₁ r₂ r₃ k)) stack regs =
    let v₁ = findWithDefault (_=ℕ=_) r₁ 0 regs
        v₂ = findWithDefault (_=ℕ=_) r₂ 0 regs
        regs' = insert (_=ℕ=_) r₃ (v₁ * v₂) regs
     in runAssembly k stack regs'

prog : FreeT AssemblyF Identity ℕ
prog = do
  push 1
  push 2
  add 1 2 3
  push 3
  ret

stack : Stack
stack = []

insertI : ℕ → ℕ → Map ℕ ℕ → Map ℕ ℕ
insertI = insert (_=ℕ=_)

registers : Registers
registers = insertI 2 5 (insertI 1 6 [])

runProg : ℕ
runProg = runAssembly prog stack registers
