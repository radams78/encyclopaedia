module Term0 where

open import ETCS
open import Id
open import Bijection

postulate AxTerm : Prf (Ex λ T → All λ X → ∃ λ (b : X ⇒ T) → all λ (x : X ⇒ T) → x ≡ b)

term-unique : ∀ {T} {T'}
            → (∀ {X} → Prf (∃ λ (b : X ⇒ T) → all λ (x : X ⇒ T) → x ≡ b))
            → (∀ {X} → Prf (∃ λ (b : X ⇒ T') → all λ (x : X ⇒ T') → x ≡ b))
            → Prf (∃! λ (i : T ⇒ T') → bijection i)
term-unique {T} {T'} =
  λ (stepa : ∀ {X} → Prf (∃ λ (b : X ⇒ T) → all λ (x : X ⇒ T) → x ≡ b))
  (stepb : ∀ {X} → Prf (∃ λ (b : X ⇒ T') → all λ (x : X ⇒ T') → x ≡ b))
  → ∃E (stepb {T}) λ (i : T ⇒ T')
  (step11 : Prf (all λ x → x ≡ i))
  → ∃E (stepa {T'}) λ (j : T' ⇒ T)
  (step12 : Prf (all λ x → x ≡ j))
  → let step13 : Prf (i ∘ j ≡ id T')
        step13 = ∃E (stepb {T'}) λ (e : T' ⇒ T')
                    (step21 : Prf (all λ x → x ≡ e))
                 → begin
                     i ∘ j
                   ≡⟨ allE step21 ⟩
                     e
                   ≡⟪ allE step21 ⟫
                     id T'
                   ∎
  in let step14 : Prf (j ∘ i ≡ id T)
         step14 = ∃E (stepa {T}) λ (e : T ⇒ T)
                  (step21 : Prf (all λ x → x ≡ e))
                  → begin
                     j ∘ i
                  ≡⟨ allE step21 ⟩
                     e
                  ≡⟪ allE step21 ⟫
                    id T
                  ∎
  in let step15 : Prf (bijection i)
         step15 = ∃I (∧I step13 step14)
  in let step16 : ∀ {x y : T ⇒ T'} → Prf (bijection x) → Prf (bijection y) → Prf (x ≡ y)
         step16 = λ {x y : T ⇒ T'}
                  (step21 : Prf (bijection x))
                  (step22 : Prf (bijection y))
                  → begin
                    x
                  ≡⟨ allE step11 ⟩
                    i
                  ≡⟪ allE step11 ⟫
                    y
                  ∎
  in ∃!I (∃I step15) step16


