module 0Trinitarianism.Quest2 where

open import 0Trinitarianism.Preambles.P2

isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n


∃even : Σ ℕ isEven
∃even = 0 , tt

_×_ : Type → Type → Type
A × C = Σ A (λ a → C)


div2 : Σ ℕ isEven → ℕ
div2 (zero , parity) = zero
div2 (suc (suc x) , parity) = suc (div2 (x , parity))

private
  postulate
    A B C : Type

uncurry : (A → B → C) → (A × B → C)
uncurry f x = f (x .fst) (x .snd)

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b)
