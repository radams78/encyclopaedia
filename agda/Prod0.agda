module Prod0 where

open import ETCS
open import Id
open import Bijection

prod-unique : ∀ {A} {B} {P} {Q}
  {p₁ : P ⇒ A} {p₂ : P ⇒ B} {q₁ : Q ⇒ A} {q₂ : Q ⇒ B}
  → (∀ {X} {f : X ⇒ A} {g : X ⇒ B} → Prf (∃! λ h → p₁ ∘ h ≡ f ∧ p₂ ∘ h ≡ g))
  → (∀ {X} {f : X ⇒ A} {g : X ⇒ B} → Prf (∃! λ h → q₁ ∘ h ≡ f ∧ q₂ ∘ h ≡ g))
  → Prf (∃! λ (ϕ : P ⇒ Q) → bijection ϕ ∧ q₁ ∘ ϕ ≡ p₁ ∧ q₂ ∘ ϕ ≡ p₂)
prod-unique {A} {B} {P} {Q} {p₁} {p₂} {q₁} {q₂} = λ
  (stepa : ∀ {X} {f : X ⇒ A} {g : X ⇒ B}
    → Prf (∃! λ h → p₁ ∘ h ≡ f ∧ p₂ ∘ h ≡ g))
  (stepb : ∀ {X} {f : X ⇒ A} {g : X ⇒ B}
    → Prf (∃! λ h → q₁ ∘ h ≡ f ∧ q₂ ∘ h ≡ g))
  → ∃!E (stepb {P} {p₁} {p₂})
  λ (ϕ : P ⇒ Q)
    (step11 : Prf (q₁ ∘ ϕ ≡ p₁ ∧ q₂ ∘ ϕ ≡ p₂)) 
  → ∃!E (stepa {Q} {q₁} {q₂})
  λ (ϕ⁻¹ : Q ⇒ P)
    (step12 : Prf (p₁ ∘ ϕ⁻¹ ≡ q₁ ∧ p₂ ∘ ϕ⁻¹ ≡ q₂))
  → let stepc : Prf (q₁ ∘ ϕ ≡ p₁)
        stepc = ∧E1 step11
  in let stepd : Prf (q₂ ∘ ϕ ≡ p₂)
         stepd = ∧E2 step11
  in let stepe : Prf (p₁ ∘ ϕ⁻¹ ≡ q₁)
         stepe = ∧E1 step12
  in let stepf : Prf (p₂ ∘ ϕ⁻¹ ≡ q₂)
         stepf = ∧E2 step12
  in let step13 : Prf (ϕ ∘ ϕ⁻¹ ≡ id Q)
         step13 =
          let step21 : Prf (q₁ ∘ (ϕ ∘ ϕ⁻¹) ≡ q₁)
              step21 = begin
                       q₁ ∘ (ϕ ∘ ϕ⁻¹)
                     ≡⟨ AxAssoc ⟩
                       (q₁ ∘ ϕ) ∘ ϕ⁻¹
                     ≡⟨ wd stepc ⟩
                       p₁ ∘ ϕ⁻¹
                     ≡⟨ stepe ⟩
                       q₁
                     ∎
          in let step22 : Prf (q₂ ∘ (ϕ ∘ ϕ⁻¹) ≡ q₂)
                 step22 = begin
                       q₂ ∘ (ϕ ∘ ϕ⁻¹)
                     ≡⟨ AxAssoc ⟩
                       (q₂ ∘ ϕ) ∘ ϕ⁻¹
                     ≡⟨ wd stepd ⟩
                       p₂ ∘ ϕ⁻¹
                     ≡⟨ stepf ⟩
                       q₂
                     ∎ 
          in let step23 : Prf (p₁ ∘ (ϕ⁻¹ ∘ ϕ) ≡ p₁)
                 step23 = {!begin
                       p₁ ∘ (ϕ⁻¹ ∘ ϕ)
                     ≡⟨ AxAssoc ⟩
                       (p₁ ∘ ϕ⁻¹) ∘ ϕ
                     ≡⟨ wd stepc ⟩
                       p₁ ∘ ϕ⁻¹
                     ≡⟨ stepe ⟩
                       q₁
                     ∎!}
          in let step24 : Prf (p₂ ∘ (ϕ⁻¹ ∘ ϕ) ≡ p₂)
                 step24 = {!!}
          in ∃!unique (stepb {Q} {q₁} {q₂}) {!!} {!!}
  in {!!}
