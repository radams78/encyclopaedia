module Setoid.Base where

record Setoid : Set₁ where
  field
    El : Set
    _≡_ : El → El → Set
    ref : ∀ {x} → x ≡ x
    sym : ∀ {x} {y} → x ≡ y → y ≡ x
    trans : ∀ {x} {y} {z} → x ≡ y → y ≡ z → x ≡ z

El : Setoid → Set
El = Setoid.El

_∋_≡_ : ∀ (A : Setoid) → El A → El A → Set
_∋_≡_ = Setoid._≡_
