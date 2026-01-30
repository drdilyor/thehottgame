module 0Trinitarianism.Quest4 where

open import 0Trinitarianism.Preambles.P4

data Id {A : Type} : (x y : A) → Type where
  rfl : {x : A} → Id x x

idSym : {A : Type} (x y : A) → Id x y → Id y x
idSym x y rfl = rfl

sym : {A : Type} {x y : A} → Id x y → Id y x
sym rfl = rfl

idTrans : {A : Type} {x y z : A} → Id x y → Id y z → Id x z
idTrans rfl p = p

_*_ = idTrans

module AlgebraicPropertiesId where
  private
    variable
      A : Type
      x y : A
  
  rfl* : (p : Id x y) → Id (rfl * p) p
  rfl* _ = rfl
  
  *rfl : (p : Id x y) → Id (p * rfl) p
  *rfl rfl = rfl
  
  sym* : (p : Id x y) → Id (sym p * p) rfl
  sym* rfl = rfl
  
  *sym : (p : Id x y) → Id (p * sym p) rfl
  *sym rfl = rfl
  
  assoc* : {z w : A} (pa : Id x y) (pb : Id y z) (pc : Id z w)
    → Id (pa * (pb * pc)) ((pa * pb) * pc)
  assoc* rfl rfl _ = rfl

outOfId : {A : Type} (x : A) (B : (y : A) (p : Id x y) → Type)
  → B x rfl
  → {y : A} (p : Id x y) → B y p
outOfId x B b rfl = b

pathSym : {A : Type} {x y : A} → (x ≡ y) → (y ≡ x)
pathSym {_} {x} = J (λ y₂ q → y₂ ≡ x) refl

Path≅Id : {A : Type} (x y : A) → (x ≡ y) ≅ (Id x y)
Path≅Id x y = iso fun inv rightInv leftInv where
  fun = J (λ y₁ _ → Id x y₁) rfl
  inv = outOfId x (λ y₁ _ → x ≡ y₁) refl
  rightInv = λ{rfl → JRefl (λ y₁ _ → y₁) rfl}
  leftInv = J (λ y₁ p → inv (fun p) ≡ p)
    let h : rfl ≡ fun refl
        h = pathSym (JRefl (λ y₁ p → y₁) rfl)
        g : inv rfl ≡ refl
        g = refl
    in J (λ y₁ p → inv y₁ ≡ refl) g h

Path→Id : {A : Type} {x y : A} → (x ≡ y) → Id x y
Path→Id = _≅_.fun (Path≅Id _ _)

Id→Path : {A : Type} {x y : A} → Id x y → (x ≡ y)
Id→Path = _≅_.inv (Path≅Id _ _)

_∙_ : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ p q = Id→Path (idTrans (Path→Id p) (Path→Id q))

-- non-dependent version
cong' : {A B : Type} (f : (x : A) → B) → {x y : A} → x ≡ y → f x ≡ f y
cong' f {x} {y} = J (λ y₁ p → f x ≡ f y₁) refl

_≡⟨_⟩_ : {A : Type} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z -- input \< and \>
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

_∎ : {A : Type} (x : A) → x ≡ x -- input \qed
_ ∎ = refl

infixr 30 _∙_
infix  3 _∎
infixr 2 _≡⟨_⟩_

id : {A : Type} → A → A
id a = a

pathToFun : {A B : Type} → A ≡ B → A → B
pathToFun {A} {B} = J (λ y p → A → y) id

pathToFunRefl : {A : Type} → pathToFun {A} refl ≡ id
pathToFunRefl = JRefl (λ y z → y) (λ z → z)

endPt : {A : Type} (B : A → Type) {x y : A} → (x ≡ y) → B x → B y
endPt B {x} = J (λ y _ → B x → B y) id

endPtRefl : {A : Type} (B : A → Type) {x : A} → endPt B (refl {x = x}) ≡ id
endPtRefl B {x} = JRefl (λ y x₁ → B x → B y) id

endPt' : {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) → B x → B y
endPt' B p = pathToFun (cong B p)

data _×_ (A B : Type) : Type where
  _,_ : A → B → A × B

fst : {A B : Type} → A × B → A
fst (a , b) = a
snd : {A B : Type} → A × B → B
snd (a , b) = b

Path× : {A B : Type} (a b : A) (c d : B) → (_≡_ {_} {A × B} (a , c) (b , d)) ≅ ((a ≡ b) × (c ≡ d))
Path× {A} {B} a b c d = iso (fun a b c d) (inv a b c d) (rightInv a b c d) leftInv where
  fun : (a b : A) (c d : B) → _≡_ {_} {A × B} (a , c) (b , d) → ((a ≡ b) × (c ≡ d))
  fun a b c d p = cong' fst p , cong' snd p
  inv : (a b : A) (c d : B) → ((a ≡ b) × (c ≡ d)) → _≡_ {_} {A × B} (a , c) (b , d)
  inv a b c d (p , q) = J (λ x _ → (a , c) ≡ (x , d)) (J (λ x _ → (a , c) ≡ (a , x)) refl q) p
  rightInv : (a b : A) (c d : B) → section (fun a b c d) (inv a b c d)
  rightInv a b c d (p , q) =
    J (λ x r → fun a x c d (inv a x c d (r , q)) ≡ (r , q)) (
    J (λ x r → fun a a c x (inv a a c x (refl , r)) ≡ (refl , r)) (
    J (λ x _ → fun a a c c (J (λ y _ → (a , c) ≡ (y , c)) x refl) ≡ (refl , refl)) (
    J (λ x _ → (cong' fst x , cong' snd x) ≡ (refl , refl)) (
    {!!})
    (let p : refl ≡ J (λ y _ → (a , c) ≡ (y , c)) refl (λ _ → a)
         p = pathSym (JRefl (λ x r → J _ x r) refl) in p))
    (let p : refl ≡ J (λ y _ → (a , c) ≡ (a , y)) refl refl
         p = pathSym (JRefl (λ x r → J _ x r) refl) in p))
    q) p
  leftInv = {!!}


-- Side quests

funExt : {A : Type} {B : A → Type} {f g : (a : A) → B a} →
    ((a : A) → f a ≡ g a) → f ≡ g
funExt h = λ i a → h a i

funExtIso : {A : Type} {B : A → Type} {f g : (a : A) → B a} →
    ((a : A) → f a ≡ g a) ≅ (f ≡ g)
funExtIso = iso funExt inv rightInv leftInv where
  inv = λ h a i → (h i) a
  rightInv = λ h → refl
  leftInv = λ h → refl




