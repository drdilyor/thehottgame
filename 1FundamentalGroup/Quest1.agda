-- ignore
module 1FundamentalGroup.Quest1 where
open import 1FundamentalGroup.Preambles.P1


loopSpace : (A : Type) (a : A) → Type
loopSpace A a = a ≡ a

loop_times : ℤ → loopSpace S¹ base
loop pos zero times = refl
loop pos (suc n) times = loop pos n times ∙ loop
loop negsuc zero times = sym loop
loop negsuc (suc n) times = loop negsuc n times ∙ sym loop

{-
The definition of sucℤ goes here.
-}
sucℤ : ℤ → ℤ
sucℤ (pos n) = pos (suc n)
sucℤ (negsuc zero) = pos zero
sucℤ (negsuc (suc n)) = negsuc n

{-
The definition of predℤ goes here.
-}
predℤ : ℤ → ℤ
predℤ (pos zero) = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n) = negsuc (suc n)

{-
The definition of sucℤIso goes here.
-}
sucℤIso : ℤ ≅ ℤ
sucℤIso = iso sucℤ predℤ leftInv rightInv where
  leftInv : section sucℤ predℤ
  leftInv (pos zero) = refl
  leftInv (pos (suc n)) = refl
  leftInv (negsuc zero) = refl
  leftInv (negsuc (suc n)) = refl

  rightInv : retract sucℤ predℤ
  rightInv (pos zero) = refl
  rightInv (pos (suc n)) = refl
  rightInv (negsuc zero) = refl
  rightInv (negsuc (suc n)) = refl

{-
The definition of sucℤPath goes here.
-}
sucℤPath : ℤ ≡ ℤ
sucℤPath = isoToPath sucℤIso

helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucℤPath i

windingNumberBase : base ≡ base → ℤ
windingNumberBase p = endPt helix p (pos zero)

windingNumber : (x : S¹) → base ≡ x → helix x
windingNumber base = windingNumberBase
windingNumber (loop i) p = endPt helix p (pos zero)
