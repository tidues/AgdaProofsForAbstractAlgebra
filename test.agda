module test where

open import Data.Product
open import Data.Nat
open import Data.Integer.Base as ℤ hiding (_>_)

p1 : ℕ × ℕ 
p1 = 2 , 3
e1 : ∃[ n ] (n > 1)
e1 = 2 , s≤s (s≤s z≤n)

-- test matching
entry1 : {A B : Set} → A × B → A
entry1 (a , b) = a

v1 = entry1 p1
v2 = proj₂ p1

ve1 = proj₁ e1
ve2 = proj₂ e1

val = -[1+ 2 ] ℤ.+ (+ 2)
