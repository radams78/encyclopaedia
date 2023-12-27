module Empty where

open import ETCS
open import Term

postulate AxEmpty : Prf (Ex λ E → ¬ (∃ λ (e : El E) → e ≡ e))
