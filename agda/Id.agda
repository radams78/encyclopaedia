module Id where

open import ETCS

postulate id : ∀ A → A ⇒ A
postulate AxUnitL : ∀ {A} {B} {f : A ⇒ B} → Prf (id B ∘ f ≡ f)
postulate AxUnitR : ∀ {A} {B} {f : A ⇒ B} → Prf (f ∘ id A ≡ f)
