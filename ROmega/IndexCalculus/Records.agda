{-# OPTIONS --safe #-}
module ROmega.IndexCalculus.Records where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

-- open import Data.Nat using (ℕ; zero; suc)
open import Data.List
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
  hiding (map)
open import Data.Product
  using (_×_; ∃; ∃-syntax; Σ-syntax; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Data.Fin  renaming (zero to fzero; suc to fsuc)
  hiding (fold)  

open import ROmega.IndexCalculus.Rows
open import ROmega.IndexCalculus.Properties

--------------------------------------------------------------------------------
-- Records say: "If you give me an index in range, I can give you a type".

Π : ∀ {ℓ} → Row (Set ℓ) → Set ℓ
Π (n , P) = ∀ (i : Fin n) → P i

--------------------------------------------------------------------------------
-- Projection.

prj : ∀ {ℓ} (z y : Row {lsuc ℓ} (Set ℓ)) (w : z ≲ y) (p : Π y) → Π z
prj {ℓ} z y w p i with w i
... | (n , P) rewrite P = p n

--------------------------------------------------------------------------------
-- Concatenation.

infixl 5 _⊹_
infix  5 _⊹_Using_

_⊹_ : ∀ {ℓ} {x y z : Row {lsuc ℓ} (Set ℓ)} {x·y~z : x · y ~ z} (Πx : Π x) (Πy : Π y) → Π z
_⊹_ {ℓ} {x} {y} {z} {x·y~z} Πx Πy i with fst x·y~z i
... | left (j , x[j]=z[i]) rewrite (sym x[j]=z[i]) = Πx j
... | right (j , y[j]=z[i]) rewrite (sym y[j]=z[i]) = Πy j

_⊹_Using_ : ∀ {ℓ} {x y z : Row {lsuc ℓ} (Set ℓ)} (Πx : Π x) (Πy : Π y) (x·y~z : x · y ~ z) → Π z
Πx ⊹ Πy Using pf = _⊹_ {x·y~z = pf} Πx Πy

--------------------------------------------------------------------------------
-- Folding.

fold : ∀ {ℓ ℓ'} {υ : Set ℓ'}
          (ρ : Row {lsuc ℓ} (Set ℓ))
          (f : ∀ (τ : Set ℓ) (y : Row {lsuc ℓ} (Set ℓ)) →
            (sing {lsuc ℓ} τ) · y ~ ρ → τ  → υ) 
         (_++_ : υ → υ → υ) →
         (e : υ) →
         (r  : Π ρ) →
         υ
fold ρ@(n , P) f _++_ e r =
  foldr _++_ e (map (λ i → f (P i) (ρ delete i) (recombine ρ i) (r i)) (ixs n))
    
