module relation {ℓ}{A : Set ℓ} where

open import eq
open import Data.Product
open import Agda.Builtin.Equality
open import Relation.Nullary

Op₁ : Set ℓ
Op₁ = A -> A

Op₂ : Set ℓ
Op₂ = A -> A -> A

Associative : Op₂ -> Set _
Associative _·_ = ∀ (a b c : A) -> (a · b) · c ≡ a · (b · c)

Identityₗ : ∀ {_·_ : Op₂} A -> Set _
Identityₗ {_·_} e = ∀ (a : A) -> e · a ≡ a

Identityᵣ : ∀ {_·_ : Op₂} A -> Set _
Identityᵣ {_·_} e = ∀ (a : A) -> a · e ≡ a

Identity : ∀ {_·_ : Op₂} A -> Set _
Identity {·} e = Identityₗ {·} e × Identityᵣ {·} e 

Inverseₗ : ∀ {e : A}{_·_ : Op₂}(_⁻¹ : Op₁) -> Set _
Inverseₗ {e}{_·_} _⁻¹ = ∀ (a : A) -> (a ⁻¹) · a ≡ e

Inverseᵣ : ∀ {e : A}{_·_ : Op₂}(_⁻¹ : Op₁) -> Set _
Inverseᵣ {e}{_·_} _⁻¹ = ∀ (a : A) -> a · (a ⁻¹) ≡ e

Inverse : ∀ {e : A}{_·_ : Op₂}(_⁻¹ : Op₁) -> Set _
Inverse {e}{·} ⁻¹ = Inverseₗ {e}{·} ⁻¹ × Inverseᵣ {e}{·} ⁻¹
