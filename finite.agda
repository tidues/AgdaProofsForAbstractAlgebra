module finite where

open import Data.Nat
open import Data.Fin
open import function
open import Level
open import Agda.Builtin.Equality

{-
data Finite (A : Set) : Set where
  fwit : {n : ℕ} → Bijection (Fin n) A → Finite A
-}

Finite : ℕ → Set → Set
Finite n A = Bijection (Fin n) A

finFinite : ∀ {n : ℕ} → Finite n (Fin n)
finFinite {n} = bijt id (bijp id (surjp id λ x → refl))
 
