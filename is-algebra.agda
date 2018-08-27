module is-algebra {ℓ} where

open import eq
open import relation {ℓ}

record IsSemigroup {A : Set ℓ}(_·_ : Op₂ {A}) : Set ℓ where
  field
    asso : Associative _·_

record IsMonoid {A : Set ℓ} (e : A) (_·_ : Op₂ {A}) : Set ℓ where
  field
    isSemigroup : IsSemigroup _·_
    identity : Identity {A} {_·_} e

record IsGroup {A : Set ℓ} (e : A)(_⁻¹ : Op₁ {A})(_·_ : Op₂ {A}) : Set ℓ where
  field
    isMonoid : IsMonoid e _·_
    inv : Inverse {A}{e} {_·_} _⁻¹
