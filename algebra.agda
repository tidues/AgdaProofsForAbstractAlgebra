module algebra {ℓ} where

open import Agda.Primitive
open import is-algebra {ℓ}
open import relation {ℓ}

record Group {A : Set ℓ} : Set (lsuc ℓ) where

  field
    e : A
    _⁻¹ : Op₁ {A}
    _·_ : Op₂ {A}
    isGroup : IsGroup {A} e _⁻¹ _·_

  open IsGroup isGroup public
