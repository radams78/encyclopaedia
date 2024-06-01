module Cat.Setoid where

open import Level
open import Setoid
open import Cat.Base

SETOID : Cat (suc zero)
SETOID = record
           { Obj = Setoid
           ; Hom = FUNCTION
           ; id = idFunc
           ; comp = COMP
           ; assoc = λ {A} {B} {C} {D} x → Setoid.ref D
           ; unitl = λ {A} {B} x → Setoid.ref B
           ; unitr = λ {A} {B} x → Setoid.ref B
           }
