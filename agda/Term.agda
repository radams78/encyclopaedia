module Term where

open import ETCS

postulate One : set
postulate ! : ∀ X → X ⇒ One
postulate !-unique : ∀ {X} {f : X ⇒ One} → Prf (f ≡ ! X)

El : set → Set
El A = One ⇒ A

postulate AxExt : ∀ {A} {B} {f g : A ⇒ B} → (∀ (a : El A) → Prf (f ∘ a ≡ g ∘ a)) → Prf (f ≡ g)
