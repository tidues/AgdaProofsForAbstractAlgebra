module nat-props where

open import Agda.Primitive
open import Data.Nat
open import logic
open import Agda.Builtin.Equality
open import Data.Sum
open import Relation.Binary.Core using (_≢_)

ℕ≡ : ∀ (n m : ℕ) → n ≡ m → suc n ≡ suc m
ℕ≡ n m p rewrite p = refl

ℕ≡₁ : ∀ (n m : ℕ) → suc n ≡ suc m → n ≡ m
ℕ≡₁ n .n refl = refl

ℕ≢→ : ∀ (n m : ℕ) → n ≢ m → suc n ≢ suc m 
ℕ≢→ n m p q with p (ℕ≡₁ n m q)
... | ()

ℕ≢← : ∀ (n m : ℕ) → suc n ≢ suc m → n ≢ m 
ℕ≢← n m p q with p (ℕ≡ n m q)
... | ()

≢⇒<> : ∀ (n m : ℕ) → n ≢ m → (n < m) ∨ (n > m)
≢⇒<> zero zero p with p refl
... | ()
≢⇒<> zero (suc m) p = inj₁ (s≤s z≤n)
≢⇒<> (suc n) zero p = inj₂ (s≤s z≤n)
≢⇒<> (suc n) (suc m) p with ≢⇒<> n m (ℕ≢← n m p)
≢⇒<> (suc n) (suc m) p | inj₁ x = inj₁ (s≤s x)
≢⇒<> (suc n) (suc m) p | inj₂ y = inj₂ (s≤s y)


-- define the subtraction
{-
_-_ : ℕ → ℕ → ℕ
n - zero = n
zero - suc m = 0
suc n - suc m = n - m

->0 : ∀(n m : ℕ) → n < m → m - n > 0
->0 zero zero ()
->0 zero (suc m) p = p
->0 (suc n) zero ()
->0 (suc n) (suc m) (s≤s p) = ->0 n m p
-}

+0 : ∀ (n : ℕ) → n + 0 ≡ n
+0 zero = refl
+0 (suc n) rewrite +0 n = refl

ℕ+asso : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ℕ+asso zero zero zero = refl
ℕ+asso zero zero (suc c) = refl
ℕ+asso zero (suc b) zero = refl
ℕ+asso zero (suc b) (suc c) = refl
ℕ+asso (suc a) zero zero rewrite +0 a | +0 a = refl
ℕ+asso (suc a) zero (suc c) rewrite +0 a = refl
ℕ+asso (suc a) (suc b) zero rewrite +0 b | +0 (a + suc b) = refl
ℕ+asso (suc a) (suc b) (suc c) rewrite ℕ+asso a (suc b) (suc c) = refl
