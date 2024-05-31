module Type.Prod where

infix 10 _×_
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

pi1 : ∀ {A} {B} → A × B → A
pi1 (x , _) = x

pi2 : ∀ {A} {B} → A × B → B
pi2 (_ , y) = y
