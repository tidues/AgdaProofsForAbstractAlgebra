module int-props where

open import Data.Integer.Base as Int
open import Agda.Builtin.Equality
open import Data.Nat
open import Relation.Binary.Core
open import logic
open import nat-props

0+ : ∀ (z : ℤ) → (+ 0) Int.+ z ≡ z
0+ (+_ n) = refl
0+ (-[1+_] n) = refl

0≡ : ∀ (n m : ℕ) → n ⊖ m ≡ (+ 0) → n ≡ m
0≡ n zero refl = refl
0≡ zero (ℕ.suc m) ()
0≡ (ℕ.suc n) (ℕ.suc m) p rewrite 0≡ n m p = refl

≢0 : ∀ {n m : ℕ} → n ≢ m → n ⊖ m ≢ (+ 0)
≢0 {n}{m} p = ¬rev (0≡ n m) p

minus2e : ∀ (n : ℕ) → (- (+ n)) ≡ 0 ⊖ n
minus2e zero = refl
minus2e (ℕ.suc n) = refl

+-⊖ : ∀ (n m : ℕ) → (+ n) - (+ m) ≡ n ⊖ m
+-⊖ (n) (zero) rewrite +0 n = refl
+-⊖ (zero) (ℕ.suc m) = refl
+-⊖ (ℕ.suc n) (ℕ.suc m) = refl


{-
≡sym : ∀ {n m : ℕ} → n ≡ m → m ≡ n
≡sym refl = refl

≢sym : ∀ {n m : ℕ} → n ≢ m → m ≢ n
≢sym {n} {m} p = ¬rev (≡sym {m} {n}) p
-}
