module algebra {ℓ} where

open import Agda.Primitive
open import is-algebra {ℓ}
open import relation {ℓ}
open import Data.Nat
open import Data.Integer.Base as Int
open import Agda.Builtin.Equality
open import Data.Product
open import int-props
open import logic 
open import function using (_$_)
open import Data.Integer.Properties using (+-assoc; neg-distrib-+; neg-involutive)

record Group (A : Set ℓ) : Set (lsuc ℓ) where

  field
    e : A
    _⁻¹ : Op₁ {A}
    _∙_ : Op₂ {A}
    isGroup : IsGroup {A} e _⁻¹ _∙_

  open IsGroup isGroup public

  invId : ∀ (a b : A) → (a ∙ b) ⁻¹ ≡ (b ⁻¹) ∙ (a ⁻¹)
  invId a b rewrite ≡sym $ (proj₂ identity) ((b ⁻¹) ∙ (a ⁻¹))
    | ≡sym $ (proj₂ inv) (a ∙ b) 
    | asso (b ⁻¹) (a ⁻¹) ((a ∙ b) ∙ ((a ∙ b) ⁻¹))
    | ≡sym $ asso (a ⁻¹) (a ∙ b) ((a ∙ b) ⁻¹)
    | ≡sym $ asso (a ⁻¹) a b
    | (proj₁ inv) a
    | (proj₁ identity) b
    | ≡sym $ asso (b ⁻¹) b ((a ∙ b) ⁻¹)
    | (proj₁ inv) b
    | (proj₁ identity) ((a ∙ b) ⁻¹) = refl

  invinv : ∀ (a : A) → (a ⁻¹) ⁻¹ ≡ a
  invinv a rewrite ≡sym $ (proj₂ identity) ((a ⁻¹) ⁻¹)
    | ≡sym $ (proj₁ inv) a
    | ≡sym $ asso ((a ⁻¹) ⁻¹) (a ⁻¹) a
    | (proj₁ inv) (a ⁻¹) 
    | (proj₁ identity) a = refl

  powh : A → ℕ → A
  powh a zero = e
  powh a (suc n) = a ∙ (powh a n)

  powhMulti : ∀ (a : A)(n m : ℕ) → (powh a n) ∙ (powh a m) ≡ powh a (n Data.Nat.+ m)
  powhMulti a zero m = proj₁ identity (powh a m)
  powhMulti a (ℕ.suc n) m 
    rewrite asso a (powh a n) (powh a m) | powhMulti a n m = refl

  powComm : ∀ (a : A)(n : ℕ) → (powh a n) ∙ (a ⁻¹) ≡ (a ⁻¹) ∙ (powh a n)
  powComm a zero rewrite (proj₁ identity) (a ⁻¹) | (proj₂ identity) (a ⁻¹)  
    = refl
  powComm a (ℕ.suc n) rewrite asso a (powh a n) (a ⁻¹)
    | powComm a n 
      with (a ∙ ((a ⁻¹) ∙ (powh a n))) | asso a (a ⁻¹) (powh a n) 
         | ((a ⁻¹) ∙ (a ∙ powh a n)) | asso (a ⁻¹) a (powh a n)
  powComm a (ℕ.suc n) | .((a ∙ (a ⁻¹)) ∙ (powh a n)) | refl 
    | .(((a ⁻¹) ∙ a) ∙ powh a n) | refl = h
    where h : ((a ∙ (a ⁻¹)) ∙ powh a n) ≡ (((a ⁻¹) ∙ a) ∙ powh a n)
          h rewrite (proj₁ inv) a | (proj₂ inv) a = refl

  powComm1 : ∀ (a : A) (n : ℕ) → (powh a n) ∙ a ≡ a ∙ (powh a n)
  powComm1 a zero rewrite (proj₁ identity) a
   | (proj₂ identity) a = refl
  powComm1 a (ℕ.suc n) rewrite asso a (powh a n) a
   | powComm1 a n = refl

  powhInv : ∀ (a : A)(n : ℕ) → powh (a ⁻¹) n ≡ powh a n ⁻¹
  powhInv a zero rewrite ≡sym $ (proj₁ identity) (e ⁻¹)
    | (proj₂ inv) e = refl
  powhInv a (ℕ.suc n) rewrite invId a (powh a n)
    | ≡sym $ powhInv a n 
    | powComm1 (a ⁻¹) n = refl

  powhCancel : ∀ (a : A)(n : ℕ) → powh a n ∙ powh (a ⁻¹) n ≡ e
  powhCancel a zero rewrite (proj₁ identity) e = refl
  powhCancel a (ℕ.suc n) rewrite asso a (powh a n) ((a ⁻¹) ∙ (powh (a ⁻¹) n)) 
    | ≡sym $ asso (powh a n) (a ⁻¹) (powh (a ⁻¹) n)
    | powComm a n | ≡sym $ asso a ((a ⁻¹) ∙ powh a n) (powh (a ⁻¹) n)
    | ≡sym $ asso a (a ⁻¹) (powh a n) | (proj₂ inv) a 
    | (proj₁ identity) (powh a n) = powhCancel a n

  pow : A → ℤ → A
  pow a (+ n) = powh a n
  pow a (-[1+ n ]) = powh (a ⁻¹) (ℕ.suc n)

  negCancel : ∀ (a : A)(z : ℤ) → (pow a z) ∙ (pow a (- z)) ≡ e
  negCancel a (+_ zero) = proj₁ identity e
  negCancel a (+_ (ℕ.suc n)) rewrite asso a (powh a n) ((a ⁻¹) ∙ powh (a ⁻¹) n)
    with powh a n ∙ ((a ⁻¹) ∙ powh (a ⁻¹) n) | asso (powh a n) (a ⁻¹) (powh (a ⁻¹) n)
  negCancel a (+_ (ℕ.suc n)) | .((powh a n ∙ (a ⁻¹)) ∙ powh (a ⁻¹) n) | refl = h
    where h : (a ∙ ((powh a n ∙ (a ⁻¹)) ∙ powh (a ⁻¹) n)) ≡ e
          h rewrite powComm a n with (a ∙ (((a ⁻¹) ∙ powh a n) ∙ powh (a ⁻¹) n)) | asso a ((a ⁻¹) ∙ powh a n) (powh (a ⁻¹) n)
          h | .((a ∙ ((a ⁻¹) ∙ powh a n)) ∙ powh (a ⁻¹) n)| refl = h1
           where h1 : ((a ∙ ((a ⁻¹) ∙ powh a n)) ∙ powh (a ⁻¹) n) ≡ e
                 h1 with (a ∙ ((a ⁻¹) ∙ powh a n)) | asso a (a ⁻¹) (powh a n)
                 h1 | .((a ∙ (a ⁻¹)) ∙ powh a n) | refl = h2
                  where h2 : (((a ∙ (a ⁻¹)) ∙ powh a n) ∙ powh (a ⁻¹) n) ≡ e
                        h2 rewrite (proj₂ inv) a | (proj₁ identity) (powh a n) = powhCancel a n
  negCancel a (-[1+_] n) rewrite asso (a ⁻¹) (powh (a ⁻¹) n) (a ∙ powh a n)
    | ≡sym $ asso (powh (a ⁻¹) n) a (powh a n) 
    | ≡subst {P = λ x → powh (a ⁻¹) n ∙ x ≡ x ∙ powh (a ⁻¹) n} (invinv a) (powComm (a ⁻¹) n) 
    | ≡sym $ asso (a ⁻¹) (a ∙ powh (a ⁻¹) n) (powh a n)
    | ≡sym $ asso (a ⁻¹) a (powh (a ⁻¹) n)
    | (proj₁ inv) a | (proj₁ identity) (powh (a ⁻¹) n) 
        = ≡subst {P = λ x → _∙_ (powh (_⁻¹ a) n) (powh x n) ≡ e} (invinv a) (powhCancel (_⁻¹ a) n)

  powNegId : ∀ (a : A)(z : ℤ) → (pow a z) ⁻¹ ≡ pow a (- z)
  powNegId a z rewrite ≡sym $ (proj₁ identity) (pow a (- z)) 
    | ≡sym $ (proj₁ inv) (pow a z) 
    | asso (pow a z ⁻¹) (pow a z) (pow a (- z))
    | negCancel a z 
    | (proj₂ identity) (pow a z ⁻¹) = refl

  powInv : ∀ (a : A)(z : ℤ) → pow (a ⁻¹) z ≡ pow a z ⁻¹
  powInv a (+_ n) = powhInv a n
  powInv a (-[1+_] n) rewrite invId (a ⁻¹) (powh (a ⁻¹) n) 
   | ≡sym $ powhInv (a ⁻¹) n 
   | invinv a = ≡sym $ powComm1 a n

  negRule : ∀ (a : A)(z : ℤ) → pow a (- z) ≡ (pow a z) ⁻¹
  negRule a z = ≡sym $ powNegId a z

  powMulti1 : ∀ (a : A)(z : ℤ) → a ∙ pow a z ≡ pow a (Int.suc z)
  powMulti1 a (+_ n) = refl
  powMulti1 a (-[1+_] n) rewrite ≡sym $ asso a (a ⁻¹) (powh (a ⁻¹) n)
   | (proj₂ inv) a | (proj₁ identity) (powh (a ⁻¹) n)
   | powhInv a n 
   | powNegId a (+ n)
   | minus2e n = refl

  powMulti-1 : ∀ (a : A)(z : ℤ) → (a ⁻¹) ∙ pow a z ≡ pow a (Int.pred z)
  powMulti-1 a (+_ zero) = refl
  powMulti-1 a (+_ (ℕ.suc n)) rewrite ≡sym $ asso (a ⁻¹) a (powh a n)
    | (proj₁ inv) a 
    | (proj₁ identity) (powh a n) = refl
  powMulti-1 a (-[1+_] n) = refl

  powMulti : ∀ (a : A)(x y : ℤ) → (pow a x) ∙ (pow a y) ≡ pow a (x Int.+ y)
  powMulti a (+_ zero) y rewrite (proj₁ identity) (pow a y) 
    | 0+ y = refl
  powMulti a (+_ (ℕ.suc n)) y rewrite asso a (powh a n) (pow a y)
    | powMulti a (+ n) y
    | powMulti1 a (+ n Int.+ y) | +-assoc (+ 1) (+ n) y = refl
  powMulti a (-[1+_] zero) y rewrite (proj₂ identity) (a ⁻¹)
    = h1
    where h : ((a ⁻¹) ∙ pow (a ⁻¹) (- y)) ≡ pow a (-[1+ 0 ] Int.+ y)
          h rewrite powMulti1 (a ⁻¹) (- y)
            | powInv a (+ 1 Int.+ - y) 
            | ≡sym $ negRule a (+ 1 Int.+ - y) 
            | neg-distrib-+ (+ 1) (- y) 
            | neg-involutive y = refl
          h1 : ((a ⁻¹) ∙ pow a y) ≡ pow a (-[1+ 0 ] Int.+ y)
          h1 with h
          h1 | p1 rewrite powInv a (- y) 
             | ≡sym $ negRule a (- y) 
             | neg-involutive y = p1
  powMulti a (-[1+_] (ℕ.suc n)) y rewrite asso (a ⁻¹) ((a ⁻¹) ∙ powh (a ⁻¹) n) (pow a y)
    | powMulti a (-[1+ n ]) y 
    | powMulti-1 a (-[1+ n ] Int.+ y) 
    | ≡sym $ +-assoc (-[1+ 0 ]) (-[1+ n ]) y = refl
  
