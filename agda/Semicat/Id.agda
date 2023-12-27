module Semicat.Id where

open import Semicat

idfunc : ∀ {A} → A ⇒ A → prop
idfunc {A} i = (All λ X → all λ (f : X ⇒ A) → i ∘ f ≡ f) ∧ (All λ X → all λ (f : A ⇒ X) → f ∘ i ≡ f)

idfunc-unique : ∀ {A} {i j : A ⇒ A} → Prf (idfunc i) → Prf (idfunc j) → Prf (i ≡ j)
idfunc-unique {A} {i} {j} = λ
  (step11 : Prf (idfunc i))
  (step12 : Prf (idfunc j))
  → begin
    i
  ≡⟪ allE (AllE (∧E2 step12)) ⟫
    i ∘ j
  ≡⟨ allE (AllE (∧E1 step11)) ⟩
    j
  ∎
