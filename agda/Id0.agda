module Id0 where

open import ETCS

postulate AxId : ∀ {A} → Prf (∃ λ (i : A ⇒ A) →
                 (All λ B → all λ (f : B ⇒ A) → i ∘ f ≡ f)
               ∧ (All λ B → all λ (f : A ⇒ B) → f ∘ i ≡ f))

id-unique : ∀ {A} → Prf (∃! λ (i : A ⇒ A) →
                 (All λ B → all λ (f : B ⇒ A) → i ∘ f ≡ f)
               ∧ (All λ B → all λ (f : A ⇒ B) → f ∘ i ≡ f))
id-unique {A} =
  let IsIdFunc : (A ⇒ A) → prop
      IsIdFunc i = (All λ B → all λ (f : B ⇒ A) → i ∘ f ≡ f)
                 ∧ (All λ B → all λ (f : A ⇒ B) → f ∘ i ≡ f)
  in let step12 : ∀ {x y} → Prf (IsIdFunc x) → Prf (IsIdFunc y) → Prf (x ≡ y)
         step12 =
           λ {x y : A ⇒ A}
           (step21 : Prf (IsIdFunc x))
           (step21b : Prf (IsIdFunc y))
           → let step22 : Prf (x ∘ y ≡ x)
                 step22 = allE (AllE (∧E2 step21b))
           in let step23 : Prf (x ∘ y ≡ y)
                  step23 = allE (AllE (∧E1 step21))
           in begin
               x
             ≡⟪ step22 ⟫
               x ∘ y
             ≡⟨ step23 ⟩
               y
             ∎
  in ∃!I AxId step12
