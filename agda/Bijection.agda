module Bijection where

open import ETCS
open import Id

bijection : ∀ {A} {B} → A ⇒ B → prop
bijection {A} {B} f = ∃ λ g → f ∘ g ≡ id B ∧ g ∘ f ≡ id A
