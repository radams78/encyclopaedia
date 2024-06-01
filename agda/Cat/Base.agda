module Cat.Base where

open import Level
open import Setoid

record Cat i : Set (suc i) where
  field
    Obj : Set i
    Hom : Obj → Obj → Setoid
    id : ∀ A → El (Hom A A)
    comp : ∀ {A} {B} {C} → Function (Prod (Hom B C) (Hom A B)) (Hom A C)
    assoc : ∀ {A} {B} {C} {D} {f : El (Hom A B)} {g : El (Hom B C)} {h : El (Hom C D)} →
      Hom A D ∋ ap comp (h , ap comp (g , f)) ≡ ap comp (ap comp (h , g) , f)
    unitl : ∀ {A} {B} {f : El (Hom A B)} → Hom A B ∋ ap comp (id B , f) ≡ f
    unitr : ∀ {A} {B} {f : El (Hom A B)} → Hom A B ∋ ap comp (f , id A) ≡ f
