module Logic where

-- Primitive Terms

postulate set : Set
postulate _⇒_ : set → set → Set

postulate prop : Set
postulate Prf : prop → Set

infix 50 _≡_
postulate _≡_ : ∀ {A} {B} → A ⇒ B → A ⇒ B → prop
postulate ¬ : prop → prop
infixr 25 _∧_
postulate _∧_ : prop → prop → prop
postulate _⇛_ : prop → prop → prop
postulate All : (set → prop) → prop
postulate Ex : (set → prop) → prop
postulate all : ∀ {A} {B} → (A ⇒ B → prop) → prop
postulate ∃ : ∀ {A} {B} → (A ⇒ B → prop) → prop

postulate ref : ∀ {A} {B} {x : A ⇒ B} → Prf (x ≡ x)
postulate sub : ∀ {A} {B} {P : A ⇒ B → prop} {x y : A ⇒ B} →
              Prf (x ≡ y) → Prf (P x) → Prf (P y)
postulate ∧I : ∀ {ϕ} {ψ} → Prf ϕ → Prf ψ → Prf (ϕ ∧ ψ)
postulate ∧E1 : ∀ {ϕ} {ψ} → Prf (ϕ ∧ ψ) → Prf ϕ
postulate ∧E2 : ∀ {ϕ} {ψ} → Prf (ϕ ∧ ψ) → Prf ψ
postulate ⇛I : ∀ {ϕ} {ψ} → (Prf ϕ → Prf ψ) → Prf (ϕ ⇛ ψ)
postulate ⇛E : ∀ {ϕ} {ψ} → Prf (ϕ ⇛ ψ) → Prf ϕ → Prf ψ
postulate AllE : ∀ {P : set → prop} {X : set} → Prf (All P) → Prf (P X)
postulate allI : ∀ {A} {B} {P : A ⇒ B → prop} → (∀ x → Prf (P x)) → Prf (all P)
postulate allE : ∀ {A} {B} {P : A ⇒ B → prop} {x : A ⇒ B} → Prf (all P) → Prf (P x)
postulate ∃I : ∀ {A} {B} {P : A ⇒ B → prop} {a : A ⇒ B}
             → Prf (P a) → Prf (∃ P)
postulate ∃E : ∀ {A} {B} {P : A ⇒ B → prop} {ϕ : prop}
             → Prf (∃ P) → (∀ x → Prf (P x) → Prf ϕ) → Prf ϕ

sym : ∀ {A} {B} {x y : A ⇒ B} → Prf (x ≡ y) → Prf (y ≡ x)
sym {A} {B} {x} {y} =
  λ (step11 : Prf (x ≡ y))
  → sub {P = λ z → z ≡ x} step11 ref

trans : ∀ {A} {B} {x y z : A ⇒ B} → Prf (x ≡ y) → Prf (y ≡ z) → Prf (x ≡ z)
trans {A} {B} {x} {y} {z} = λ
  (step11 : Prf (x ≡ y))
  (step12 : Prf (y ≡ z))
  → sub step12 step11

wd : ∀ {A} {B} {C} {D} {t : A ⇒ B → C ⇒ D} {x y : A ⇒ B} →
  Prf (x ≡ y) → Prf (t x ≡ t y)
wd {A} {B} {C} {D} {t} {x} {y} =
  λ (step11 : Prf (x ≡ y))
  → sub {P = λ z → t x ≡ t z} step11 ref

∃! : ∀ {A} {B} → (A ⇒ B → prop) → prop
∃! {A} {B} P = ∃ λ x → P x ∧ all λ y → P y ⇛ x ≡ y

∃!I : ∀ {A} {B} {P : A ⇒ B → prop}
    → Prf (∃ P)
    → (∀ {x} {y} → Prf (P x) → Prf (P y) → Prf (x ≡ y))
    → Prf (∃! P)
∃!I {A} {B} {P} = λ
  (step11 : Prf (∃ P))
  (step12 : ∀ {x} {y} → Prf (P x) → Prf (P y) → Prf (x ≡ y))
  → ∃E step11 (
  λ (a : A ⇒ B)
  (step13 : Prf (P a))
  → let step14 : Prf (all λ y → P y ⇛ a ≡ y)
        step14 =
          allI λ (x : A ⇒ B)
          → ⇛I λ (step21 : Prf (P x))
          → step12 step13 step21
  in ∃I (∧I step13 step14)
  )

∃!E : ∀ {A} {B} {P : A ⇒ B → prop} {ϕ : prop}
  → Prf (∃! P) → (∀ x → Prf (P x) → Prf ϕ) → Prf ϕ
∃!E {A} {B} {P} {ϕ} = λ
  (step11 : Prf (∃! P))
  (step12 : ∀ x → Prf (P x) → Prf ϕ)
  → ∃E step11
  λ (x : A ⇒ B)
    (step13 : Prf (P x ∧ all λ y → P y ⇛ x ≡ y))
  → step12 x (∧E1 step13)

∃!unique : ∀ {A} {B} {P : A ⇒ B → prop} {x y : A ⇒ B}
  → Prf (∃! P) → Prf (P x) → Prf (P y) → Prf (x ≡ y)
∃!unique {A} {B} {P} {x} {y} = λ
  (step11 : Prf (∃! P))
  (step12 : Prf (P x))
  (step13 : Prf (P y))
  → ∃E step11
  λ (a : A ⇒ B)
    (step14 : Prf (P a ∧ all λ y → P y ⇛ a ≡ y))
  → let step15 : ∀ z → Prf (P z) → Prf (a ≡ z)
        step15 = λ (z : A ⇒ B)
                   (step21 : Prf (P z))
                 → ⇛E (allE (∧E2 step14)) step21
  in trans (sym (step15 x step12)) (step15 y step13)

infix  1 begin_
infixr 2 _≡⟨_⟩_ _≡⟪_⟫_
infix  3 _∎

begin_ : ∀ {A} {B} {x y : A ⇒ B}
  → Prf (x ≡ y)
    -----
  → Prf (x ≡ y)
begin x≡y  =  x≡y

_≡⟨_⟩_ : ∀ {A} {B} (x : A ⇒ B) {y z : A ⇒ B}
  → Prf (x ≡ y)
  → Prf (y ≡ z)
    -----
  → Prf (x ≡ z)
x ≡⟨ x≡y ⟩ y≡z  = trans x≡y y≡z

_≡⟪_⟫_ : ∀ {A} {B} (x : A ⇒ B) {y z : A ⇒ B}
  → Prf (y ≡ x)
  → Prf (y ≡ z)
    -----
  → Prf (x ≡ z)
x ≡⟪ y≡x ⟫ y≡z  = trans (sym y≡x) y≡z

_∎ : ∀ {A} {B} (x : A ⇒ B)
     -----
   → Prf (x ≡ x)
x ∎  =  ref
