module 0Trinitarianism.Quest3 where

open import 0Trinitarianism.Preambles.P3

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

even+even : (n m : Σ ℕ isEven) → isEven (n .fst + m .fst)
even+even (zero , npar) m = m .snd
even+even (suc (suc n) , npar) m = even+even (n , npar) m

¬_ : Type → Type
¬ A = A → ⊥

data _⊕_ (A : Type) (B : Type) : Type where
  inxl : A → (¬ B) → A ⊕ B
  inxr : B → (¬ A) → A ⊕ B

decIsEven : (n : ℕ) → isEven n ⊕ (¬ isEven n)
decIsEven zero = inxl tt (λ z → z tt)
decIsEven (suc zero) = inxr (λ ()) (λ ())
decIsEven (suc (suc n)) = decIsEven n
