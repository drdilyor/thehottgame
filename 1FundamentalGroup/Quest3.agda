module 1FundamentalGroup.Quest3 where

open import 1FundamentalGroup.Preambles.P3

pathToFunPathFibration : {A : Type} {x y z : A} (q : x ≡ y) (p : y ≡ z) →
  pathToFun (λ i → x ≡ p i) q ≡ q ∙ p
pathToFunPathFibration {A} {x} {y} {z} q =
  J (λ z p → pathToFun (λ i → x ≡ p i) q ≡ q ∙ p)
    (
      pathToFun (λ i → x ≡ refl i) q
    ≡⟨ pathToFunRefl q ⟩
      q
    ≡⟨ ∙Refl q ⟩
      q ∙ refl
    ∎)

loopPredTimes∙Loop : (n : ℤ) → loop predℤ n times ∙ loop ≡ loop n times
loopPredTimes∙Loop (pos zero) = sym∙ loop
loopPredTimes∙Loop (pos (suc n)) = refl
loopPredTimes∙Loop (negsuc n) =
    loop negsuc (suc n) times ∙ loop
  ≡⟨ congS (λ g → g ∙ loop) refl ⟩
    (loop negsuc n times ∙ sym loop) ∙ loop
  ≡⟨ sym (assoc (loop negsuc n times) (sym loop) loop) ⟩
    loop negsuc n times ∙ sym loop ∙ loop
  ≡⟨ cong (λ g → loop negsuc n times ∙ g) (sym∙ loop) ⟩
    loop negsuc n times ∙ refl
  ≡⟨ sym (∙Refl loop negsuc n times)  ⟩
    loop negsuc n times
  ∎

rewind : (x : S¹) → helix x → base ≡ x
rewind = outOfS¹D (λ x → helix x → base ≡ x) loop_times
  (
    pathToFun (λ i → sucℤPath i → base ≡ loop i) loop_times
  ≡⟨ refl ⟩
    (λ a → pathToFun (λ i → base ≡ loop i) (loop_times (pathToFun (sym sucℤPath) a)))
  ≡⟨ refl ⟩
    (λ n → pathToFun (λ i → base ≡ loop i) (loop_times (predℤ n)))
  ≡⟨ funExt (λ n → pathToFunPathFibration loop predℤ n times loop) ⟩
    (λ n → loop_times (predℤ n) ∙ loop)
  ≡⟨ funExt loopPredTimes∙Loop ⟩
    loop_times
  ∎)

loopSpace≡ℤ : loopSpace S¹ base ≡ ℤ
loopSpace≡Z = {!!}
