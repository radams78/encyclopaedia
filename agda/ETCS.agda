module ETCS where

open import Logic

postulate AxAssoc : ∀ {A} {B} {C} {D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
                  Prf (h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f)

postulate id : ∀ A → A ⇒ A
postulate AxUnitL : ∀ {A} {B} {f : A ⇒ B} → Prf (id B ∘ f ≡ f)
postulate AxUnitR : ∀ {A} {B} {f : A ⇒ B} → Prf (f ∘ id A ≡ f)

postulate One : set
postulate ! : ∀ A → A ⇒ One
postulate !-unique : ∀ {A} {f : A ⇒ One} → Prf (f ≡ ! A)

El : set → Set
El A = One ⇒ A

injective : ∀ {A} {B} → A ⇒ B → prop
injective {A} f = all λ (x : El A) → all λ (y : El A) → f ∘ x ≡ f ∘ y ⇛ x ≡ y

postulate ∅ : set
postulate AxEmpty : ∀ (x : El ∅) → Prf (¬ (x ≡ x))

postulate AxExt : ∀ {A} {B} {f g : A ⇒ B} → (∀ (x : El A) → Prf (f ∘ x ≡ g ∘ x)) → Prf (f ≡ g)

infix 75 _×_
postulate _×_ : set → set → set
postulate π₁ : ∀ {A} {B} → A × B ⇒ A
postulate π₂ : ∀ {A} {B} → A × B ⇒ B
postulate _,_ : ∀ {A} {B} {C} → A ⇒ B → A ⇒ C → A ⇒ B × C
postulate AxBeta1 : ∀ {A} {B} {C} {f : A ⇒ B} {g : A ⇒ C} → Prf (π₁ ∘ ( f , g ) ≡ f)
postulate AxBeta2 : ∀ {A} {B} {C} {f : A ⇒ B} {g : A ⇒ C} → Prf (π₂ ∘ ( f , g ) ≡ g)
postulate AxEta : ∀ {A} {B} {C} {f : A ⇒ B × C} → Prf (f ≡ ( π₁ ∘ f , π₂ ∘ f ))

_×f_ : ∀ {A} {B} {C} {D} → A ⇒ B → C ⇒ D → A × C ⇒ B × D
f ×f g = ( f ∘ π₁ , g ∘ π₂ )

infix 60 _⟶_
postulate _⟶_ : set → set → set
postulate ϵ : ∀ {A} {B} → (A ⟶ B) × A ⇒ B
postulate lam : ∀ {A} {B} {C} → A × B ⇒ C → A ⇒ B ⟶ C
postulate AxBetaF : ∀ {A} {B} {C} {f : A × B ⇒ C} → Prf (ϵ ∘ (lam f ×f id B) ≡ f)
postulate AxEtaF : ∀ {A} {B} {C} {f : A ⇒ B ⟶ C} → Prf (lam (ϵ ∘ (f ×f id B)) ≡ f)

is-inverse-image : ∀ {A} {B} I (i : I ⇒ A) (b : El B) (f : A ⇒ B) → prop
is-inverse-image {A} {B} I i b f = f ∘ i ≡ b ∘ ! I ∧ All λ X → all λ (j : X ⇒ A) → f ∘ j ≡ b ∘ ! X ⇛ ∃! λ (jj : X ⇒ I) → i ∘ jj ≡ j

infix 60 _⁻¹_
postulate _⁻¹_ : ∀ {A} {B} → A ⇒ B → El B → set
postulate inc : ∀ {A} {B} {f : A ⇒ B} {b : El B} → f ⁻¹ (b) ⇒ A
postulate AxInvIm : ∀ {A} {B} {f : A ⇒ B} {b : El B} → Prf (is-inverse-image (f ⁻¹ (b)) inc b f)

postulate Two : set
postulate ⊤ : El Two
postulate AxSubsetClassifer : ∀ {X} {A} {j : X ⇒ A} → Prf (injective j) → Prf (∃! λ (χ : A ⇒ Two) → is-inverse-image X j ⊤ χ)

postulate ℕ : set
postulate zero : El ℕ
postulate succ : ℕ ⇒ ℕ
postulate rec : ∀ {X} → El X → X ⇒ X → ℕ ⇒ X
postulate AxRecZero : ∀ {X} {a : El X} {f} → Prf (rec a f ∘ zero ≡ a)
postulate AxRecSucc : ∀ {X} {a : El X} {f} → Prf (rec a f ∘ succ ≡ f ∘ rec a f)
postulate AxRecUnique : ∀ {X} {a : El X} {f} {g} → Prf (g ∘ zero ≡ a) → Prf (g ∘ succ ≡ f ∘ g) → Prf (g ≡ rec a f)
