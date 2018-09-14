module hw1 where

open import algebra
open import finite
open import Relation.Binary.Core using (_≢_)
open import Data.Product
open import Agda.Builtin.Equality
open import Data.Nat
open import Data.Nat.Properties using (<⇒≢)
open import Data.Fin hiding (_<_; _-_)
-- open import nat-props
open import Data.Integer.Base hiding (_<_; _>_)
open import int-props
open import logic
open import function using (_$_)

postulate
  A : Set
  g : Group A
  pigeonhole : ∀{m n : ℕ}{A B : Set}{p : m Data.Nat.> n} → Finite m A → Finite n B → (f : A → B) → ∃[ a1 ] (∃[ a2 ] ( (a1 ≢ a2) × (f a1 ≡ f a2) ))
  pigeonholeℕ : ∀{n : ℕ}{B : Set} → Finite n B → (f : ℕ → B) → ∃[ n1 ] (∃[ n2 ] ((n1 < n2) × (f n1 ≡ f n2)))

open Group g public

-- HW1: p35, 8
-- basic idea
-- 1). prove pigenhole theorm
-- 2). for big enough m, map a^m into Fin n by f
--     by 1), there must be m ≢ n such that f a^m = f a^n = l
--     by biject, map l back, shows a^m = a^n
--     by inverse, a^(m - n) = e
--     set k = m - n
finiteOrd : ∀ {n : ℕ} → Finite n A → (a : A) → ∃[ k ] ((k ≢ (+ 0)) × (pow a k ≡ e))
finiteOrd {n} Afin a = (v2 ⊖ v1) , ≢0 (≢sym (<⇒≢ pneq)) , g1
  where f : ℕ → A
        f m = powh a m
        pair : ∃[ n1 ] (∃[ n2 ] ( (n1 < n2) × (f n1 ≡ f n2) ))
        pair = pigeonholeℕ Afin f
        v1 = proj₁ pair
        res = proj₂ pair
        v2 = proj₁ res
        pfs = proj₂ res
        pneq = proj₁ pfs
        peq = proj₂ pfs
        gtmp0 : (powh a v2) ∙ ((powh a v1) ⁻¹) ≡ (powh a v1) ∙ ((powh a v1) ⁻¹)
        gtmp0 rewrite peq = refl
        g1 : (pow a (v2 ⊖ v1)) ≡ e
        g1 with gtmp0
        g1 | pf rewrite (proj₂ inv) (powh a v1)
              | ≡sym $ negRule a (+ v1) 
              | powMulti a (+ v2) (- (+ v1)) 
              | +-⊖ v2 v1 = pf
        

        

