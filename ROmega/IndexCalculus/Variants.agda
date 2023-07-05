{-# OPTIONS --safe #-}
module ROmega.IndexCalculus.Variants where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
  hiding (map)
open import Data.Product
  using (_×_; ∃; ∃-syntax; Σ-syntax; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Data.Fin  renaming (zero to fzero; suc to fsuc)

open import ROmega.IndexCalculus.Rows

--------------------------------------------------------------------------------
-- Variants say: "Of the types in this row, I can give you exactly one."
Σ : ∀ {ℓ} → Row (Set ℓ) → Set ℓ
Σ (n , P) = Σ[ i ∈ Fin n ] (P i)

--------------------------------------------------------------------------------
-- injection.

inj : ∀ {ℓ} (z y : Row {lsuc ℓ} (Set ℓ)) (w : z ≲ y) (s : Σ z) → Σ y
inj {ℓ} z y w (n , P) with w n
... | m , Q rewrite Q = m , P

--------------------------------------------------------------------------------
-- Variant branching.

infixl 5 _▿_
infixl 5 _▿_Using_

_▿_ : ∀ {ℓ} {x y z : Row {lsuc ℓ} (Set ℓ)}
        {C : Set}
        {x·y~z : x · y ~ z}
        (E-Σx : Σ x → C)
        (E-Σy : Σ y → C) →
        Σ z → C

_▿_ {ℓ} {x} {y} {z} {C} {x·y~z} E-Σx E-Σy (iz , Pz) with fst x·y~z iz
... | left (ix , Px) rewrite (sym Px) = E-Σx (ix , Pz)
... | right (iy , Py) rewrite (sym Py) = E-Σy (iy , Pz)

_▿_Using_ :
  ∀ {ℓ} {x y z : Row {lsuc ℓ} (Set ℓ)}
  {C : Set}
  (E-Σx : Σ x → C)
  (E-Σy : Σ y → C)
  (x·y~z : x · y ~ z) →
  Σ z → C

(E-Σx ▿ E-Σy Using x·y~z) = (_▿_) {x·y~z = x·y~z} E-Σx E-Σy
