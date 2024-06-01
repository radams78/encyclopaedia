module Setoid.Function where

open import Setoid.Base
open import Setoid.Prod

record Function (A B : Setoid) : Set where
  field
    ap : El A → El B
    wd : ∀ {x} {y} → A ∋ x ≡ y → B ∋ ap x ≡ ap y

ap : ∀ {A} {B} → Function A B → El A → El B
ap = Function.ap

FUNCTION : Setoid → Setoid → Setoid
FUNCTION A B = record
  { El = Function A B
  ; _≡_ = λ f g → ∀ x → B ∋ ap f x ≡ ap g x
  ; ref = λ x → Setoid.ref B
  ; sym = λ f≡g x → Setoid.sym B (f≡g x)
  ; trans = λ f≡g g≡h x → Setoid.trans B (f≡g x) (g≡h x)
  }

idFunc : ∀ A → Function A A
idFunc A = record
  { ap = λ x → x
  ; wd = λ x≡y → x≡y
  }

_∘_ : ∀ {A} {B} {C} → Function B C → Function A B → Function A C
g ∘ f = record
  { ap = λ x → ap g (ap f x)
  ; wd = λ x≡y → Function.wd g (Function.wd f x≡y)
  }

makeBiProd : ∀ {A} {B} {C} →
  (ap2 : El A → El B → El C) →
  (∀ {x} {x'} {y} → A ∋ x ≡ x' → C ∋ ap2 x y ≡ ap2 x' y) →
  (∀ {x} {y} {y'} → B ∋ y ≡ y' → C ∋ ap2 x y ≡ ap2 x y') →
  Function (Prod A B) C
makeBiProd {A} {B} {C} ap2 wdl wdr = record
  { ap = λ p → ap2 (pi1 p) (pi2 p)
  ; wd = λ p≡q → Setoid.trans C (wdl (pi1 p≡q)) (wdr (pi2 p≡q))
  }

COMP : ∀ {A} {B} {C} → Function (Prod (FUNCTION B C) (FUNCTION A B)) (FUNCTION A C)
COMP {A} {B} {C} = makeBiProd {FUNCTION B C} {FUNCTION A B}
  _∘_
  (λ {_} {_} {f} g≡g' x → g≡g' (ap f x))
  λ {g} f≡f' x → Function.wd g (f≡f' x)

