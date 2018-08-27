module eq where

open import Agda.Primitive 
open import Agda.Builtin.Equality public

sym-eq : ∀ {ℓ}{A : Set ℓ}{a b : A} -> a ≡ b -> b ≡ a
sym-eq p rewrite p = refl

refl-eq : ∀ {ℓ}{A : Set ℓ}{a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
refl-eq p1 p2 rewrite p1 | p2 = refl
