-- ignore
module 1FundamentalGroup.Quest2 where
open import 1FundamentalGroup.Preambles.P2

isSet→LoopSpace≡⊤ : {A : Type} (x : A) → isSet A → (x ≡ x) ≡ ⊤
isSet→LoopSpace≡⊤ x s = isoToPath (iso (λ _ → tt) (λ _ → refl) (λ{_ → refl}) λ a → s x x (λ _ → x) a)

data _⊔_ (A B : Type) : Type where

     inl : A → A ⊔ B
     inr : B → A ⊔ B

{-
Your definition of ℤ≡ℕ⊔ℕ goes here.
-}
ℤ≡ℕ⊔ℕ : ℤ ≡ ℕ ⊔ ℕ
ℤ≡ℕ⊔ℕ = isoToPath (iso fun inv rightInv leftInv) where

  fun : ℤ → ℕ ⊔ ℕ
  fun (pos n) = inl n
  fun (negsuc n) = inr n

  inv : ℕ ⊔ ℕ → ℤ
  inv (inl x) = pos x
  inv (inr x) = negsuc x

  rightInv : section fun inv
  rightInv (inl x) = refl
  rightInv (inr x) = refl

  leftInv : retract fun inv
  leftInv (pos n) = refl
  leftInv (negsuc n) = refl

⊔NoConfusion : {A B : Type} → (_ _ : A ⊔ B) → Type
⊔NoConfusion (inl xa) (inl ya) = xa ≡ ya
⊔NoConfusion (inr xb) (inr yb) = xb ≡ yb
⊔NoConfusion _ _ = ⊥

⊔disjoint : {A B : Type} (x : A) (y : B) → (inl x ≡ inr y) → ⊥
⊔disjoint x y eq = endPt discriminator eq tt where
  discriminator : {A B : Type} → (A ⊔ B) → Type
  discriminator (inl _) = ⊤
  discriminator (inr _) = ⊥

Path≡⊔NoConfusion : {A B : Type} (x y : A ⊔ B) → (x ≡ y) ≡ ⊔NoConfusion x y
Path≡⊔NoConfusion x y = isoToPath (iso (λ z → fun x y z) (λ z → inv x y z) {!!} {!!}) where
  fun : {A B : Type} → (x y : A ⊔ B) → x ≡ y → ⊔NoConfusion x y
  fun (inl x) (inl y) eq = {!!}
  fun (inl x) (inr y) eq = ⊔disjoint x y eq
  fun (inr x) (inl y) eq = ⊔disjoint y x (sym eq)
  fun (inr x) (inr y) eq = {!!}
  inv : {A B : Type} → (x y : A ⊔ B) → ⊔NoConfusion x y → x ≡ y
  inv (inl x) (inl y) eq = cong inl eq 
  inv (inr x) (inr y) eq = cong inr eq

isSet⊔NoConfusion : {A B : Type} (x y : A ⊔ B) → isSet A → isSet B → isProp (⊔NoConfusion x y)
isSet⊔NoConfusion (inl xa) (inl ya) hA hB eq₁ eq₂ = hA xa ya eq₁ eq₂
isSet⊔NoConfusion (inr xa) (inr yb) hA hB eq₁ eq₂ = hB xa yb eq₁ eq₂

isSet⊔ : {A B : Type} → isSet A → isSet B → isSet (A ⊔ B)
isSet⊔ hA hB x y = endPt isProp (sym (Path≡⊔NoConfusion x y)) (isSet⊔NoConfusion x y hA hB)

isSetℤ : isSet ℤ
isSetℤ = endPt isSet {!!} {!!}

