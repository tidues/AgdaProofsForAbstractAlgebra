module logic where

open import Data.Sum
open import Data.Product
open import Level
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Equality
open import Relation.Binary.Core

-- logic operator or
_∨_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
_∨_ = _⊎_

-- logic operator and
_∧_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
_∧_ = _×_

-- (A -> B) -> (¬ B → ¬ A)
¬rev : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → ¬ B → ¬ A
¬rev p q r = q (p r)

-- ≡sym
≡sym : ∀ {ℓ}{A : Set ℓ}{a b : A} → a ≡ b → b ≡ a
≡sym p rewrite p = refl

-- ≢sym
≢sym : ∀ {ℓ}{A : Set ℓ}{a b : A} → a ≢ b → b ≢ a
≢sym {a = a} {b = b} p = ¬rev (≡sym {a = b} {b = a}) p

-- preserve rule
≡prsv : ∀ {a b}{A : Set a}{P : A → Set b}{a1 a2 : A} → a1 ≡ a2 → P a1 ≡ P a2
≡prsv p rewrite p = refl

-- substitute rule
≡subst : ∀ {a b}{A : Set a}{P : A → Set b}{a1 a2 : A} → a1 ≡ a2 → P a1 → P a2
≡subst p q rewrite p = q
