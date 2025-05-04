module FreeTBohm where


-- Attempting the nightmarish Bohm-Berarducci encoding
data FreeT (F M : Set → Set) (A : Set) : Set₁ where
  runFreeT : ∀ {R}
           → (A → M R) -- pure
           → (∀ {X} → (X → M R) → F X → M R) -- continuation
           → FreeT F M A
