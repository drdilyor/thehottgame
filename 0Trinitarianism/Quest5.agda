module 0Trinitarianism.Quest5 where

open import 0Trinitarianism.Preambles.P5

PathD : {A0 A1 : Type} (A : A0 ≡ A1) → A0 → A1 → Type
PathD A x y = pathToFun A x ≡ y

syntax PathD A x y = x ≡ y along A

example : (x : S¹) → doubleCover x → doubleCover x
example base = Flip
example (loop i) = p i where
  f : (a : Bool) →  pathToFun (λ i₁ → flipPath i₁ → flipPath i₁) Flip a ≡ Flip a
  f false = λ i₁ → true
  f true = λ i₁ → false
  p : PathP (λ i → flipPath i → flipPath i) Flip Flip
  p = _≅_.inv (PathPIsoPathD (λ i → flipPath i → flipPath i) Flip Flip) (funExt f)

elimS¹ : (B : S¹ → Type) (b : B base) (p : PathD (λ i → B (loop i)) b b) → (x : S¹) → B x
elimS¹ B b p base = b
elimS¹ B b p (loop i) = _≅_.inv (PathPIsoPathD (λ i₁ → B (loop i₁)) b b) p i

elimS¹Base : (B : S¹ → Type) (b : B base) (p : PathD (λ i → B (loop i)) b b)
           → elimS¹ B b p base ≡ b
elimS¹Base B b p = refl


square : {A0 A1 B0 B1 : Type} (A : A0 ≡ A1) (B : B0 ≡ B1)
         (f : A0 → B0)
         (a1 : A1) → pathToFun ((λ i → A i → B i)) f a1 ≡ pathToFun B (f (pathToFun (sym A) a1))
square {A0} {A1} {B0} {B1} A B f =
  J
    (λ A1 A → (a1 : A1) → pathToFun ((λ i → A i → B i)) f a1 ≡ pathToFun B (f (pathToFun (sym A) a1)))
    ((J
        (λ B1 B → (a1 : A0) →
                   pathToFun (λ i → refl {_} {_} {A0} i → B i) f a1 ≡
                   pathToFun B (f (pathToFun (sym refl) a1)))
        (λ a1 →
            pathToFun (λ i → A0 → B0) f a1
          ≡⟨ refl ⟩
            pathToFun refl f a1
          ≡⟨  congS (λ g → g a1) (pathToFunReflx f)  ⟩
            f a1
          ≡⟨ congS f (sym (pathToFunReflx a1)) ⟩
            f (pathToFun (λ _ → A0) a1)
          ≡⟨ congS (λ g → f (pathToFun g a1)) (sym symRefl) ⟩
            f (pathToFun (sym (λ _ → A0)) a1)
          ≡⟨ sym (pathToFunReflx (f (pathToFun (sym (λ _ → A0)) a1))) ⟩
            pathToFun refl (f (pathToFun (sym (λ _ → A0)) a1))
          ≡⟨ refl ⟩
            pathToFun (λ _ → B0) (f (pathToFun (sym (λ _ → A0)) a1))
          ∎)
        B))
    A
