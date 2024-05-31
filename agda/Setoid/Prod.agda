module Setoid.Prod where

open import Type.Prod public
open import Setoid.Base

Prod : Setoid → Setoid → Setoid
Prod A B = record
  { El = El A × El B
  ; _≡_ = λ x y → A ∋ pi1 x ≡ pi1 y × B ∋ pi2 x ≡ pi2 y
  ; ref = λ {x} → Setoid.ref A , Setoid.ref B
  ; sym = λ x≡y → Setoid.sym A (pi1 x≡y) , Setoid.sym B (pi2 x≡y)
  ; trans = λ x≡y y≡z → Setoid.trans A (pi1 x≡y) (pi1 y≡z) , Setoid.trans B (pi2 x≡y) (pi2 y≡z)
  }
