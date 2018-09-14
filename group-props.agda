open import algebra

module group-props {ℓ₀}{A : Set ℓ₀}(g : Group A) where

open import Agda.Builtin.Equality
open import relation {ℓ₀}
open import Data.Product
open import eq

open Group g public

get_idₗ : ∀ {e : A}{_·_ : Op₂ {A}}(id : Identity {A} {_·_} e) -> ∀ (a : A) -> e · a ≡ a
get_idₗ id a =
    let pl = proj₁ id
    in  pl a

get_idᵣ : ∀ {e : A}{_·_ : Op₂ {A}}(id : Identity {A}{_·_} e) -> ∀ (a : A) -> a · e ≡ a
get_idᵣ id a =
    let pr = proj₂ id
    in  pr a

unique_id : ∀ (a b : A) -> Identity {A}{_∙_} a -> Identity {A}{_∙_} b -> a ≡ b
unique_id a b p1 p2 = 
  let ab≡b = get_idₗ {a} {_∙_} p1 b
      ab≡a = get_idᵣ {b} {_∙_} p2 a
  in  refl-eq (sym-eq ab≡a) ab≡b
        
