module function where

open import Agda.Builtin.Equality

_LeftInverseOf_ : ∀ {A B : Set} → (B → A) → (A → B) → Set
_LeftInverseOf_ {A} f g = ∀ x → f (g x) ≡ x

_RightInverseOf_ : ∀ {A B : Set} → (B → A) → (A → B) → Set
f RightInverseOf g = g LeftInverseOf f

Injective : {A B : Set} → (A → B) → Set
Injective {A} f = ∀ {a1 a2 : A} → f(a1) ≡ f(a2) → a1 ≡ a2

record Injection (A B : Set) : Set  where
  field
    to : A → B
    injective : Injective to

record Surjective {A B : Set} (to : A → B) : Set where
  constructor surjp
  field
    from             : B → A
    right-inverse-of : from RightInverseOf to

record Surjection (A B : Set) : Set where
  field 
    to : A → B
    surjective : Surjective to

record Bijective {A B : Set} (to : A → B) : Set where
  constructor bijp
  field
    injective : Injective to
    surjective : Surjective to

record Bijection (A B : Set) : Set where
  constructor bijt
  field
    to : A → B
    bijective : Bijective to

id : {A : Set} → A → A
id a = a

-- function application
infixr 1 _$_
_$_ : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → A → B
f $ a = f a
