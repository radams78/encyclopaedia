module Setoid.Function where

open import Setoid.Base

record Function (A B : Setoid) : Set where
  field
    ap : El A → El B

ap : ∀ {A} {B} → Function A B → El A → El B
ap = Function.ap
