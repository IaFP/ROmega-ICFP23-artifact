{-# OPTIONS --safe #-}
module ROmega.IndexCalculus.Rows where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
  hiding (map)
open import Data.Product
  using (_×_; ∃; ∃-syntax; Σ-syntax; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Data.Fin  renaming (zero to fzero; suc to fsuc)
  hiding (fold)  

--------------------------------------------------------------------------------
-- Syntax

infixl 5 _≲_
infix  5 _·_~_

--------------------------------------------------------------------------------
-- Rows are maps from indices to types.
Row : ∀ {ℓ : Level} (A : Set ℓ) → Set ℓ
Row A = Σ[ n ∈ ℕ ] (Fin n → A)

-- An index in a Row.
Ix : ∀ {ℓ} {A : Set ℓ} → Row {ℓ} A → Set
Ix (n , _) = Fin n

-- The indices in a row.
ixs : (n : ℕ) → List (Fin n)
ixs zero = []
ixs (suc n) = fromℕ n ∷ Data.List.map inject₁ (ixs n)

--------------------------------------------------------------------------------
-- Empty row.

emptyRow : ∀ {ℓ} {A : Set ℓ} → Row {ℓ} A
emptyRow = 0 , λ ()

--------------------------------------------------------------------------------
-- Singletons.

sing : ∀ {ℓ} {A : Set ℓ} →
       A → Row {ℓ} A
sing a = 1 , λ { fzero → a }

--------------------------------------------------------------------------------
-- Helpers, smart constructers, and syntax.

one = lsuc lzero
two = lsuc one
three = lsuc two

Row₀ = Row {one} Set
Row₁ = Row {two} Set₁
Row₂ = Row {three} Set₂

infix 2 Σi-syntax

Σi-syntax : {ℓ : Level} (n : ℕ) → (Fin n → Set ℓ) → Set ℓ
Σi-syntax {ℓ} n P = ∃ {lzero} {ℓ} (λ (j : Fin n) → P j)

-- The syntax
--   Σi[ i ≤ n ] P at ℓ
-- Says "there exists an index i : Fin n such that P i holds at level ℓ."

syntax Σi-syntax {ℓ} n (λ i → B) = Σi[ i ≤ n ] B at ℓ

--------------------------------------------------------------------------------
-- The row z₁ is "in" row z₂ if all indices of z₁ correspond to some index in z₂.

_≲_ : ∀ {ℓ}{A : Set ℓ} → Row {ℓ} A → Row {ℓ} A → Set ℓ
_≲_ {ℓ} (n , P) (m , Q) = ∀ (i : Fin n) → Σi[ j ≤ m ] (P i ≡ Q j) at ℓ

--------------------------------------------------------------------------------
-- Evidence for x · y ~ z.

_·_~_ : ∀ {ℓ} {A : Set ℓ} →
        Row {ℓ} A →
        Row {ℓ} A →
        Row {ℓ} A →
        Set ℓ
_·_~_ {ℓ} (l , P) (m , Q) (n , R) =

  -- (i) Every index in z corresponds to an index in x _or_ y.
  (∀ (i : Fin n) → 
    _or_ {ℓ} {ℓ} 
      (Σi[ j ≤ l ] (P j ≡ R i) at ℓ) 
      (Σi[ j ≤ m ] (Q j ≡ R i) at ℓ)) 
  -- (ii) Every index in x corresponds to an index in z.
  × (((l , P) ≲ (n , R)) 
  -- (iii) Every index in y corresponds to an index in z.
  × ((m , Q) ≲ (n , R)))

--------------------------------------------------------------------------------
-- x · y ~ z implies x≲z in our (commutative) row theory.

·-to-≲L : ∀ {ℓ} {A : Set ℓ} → {ρ₁ ρ₂ ρ₃  : Row {ℓ} A} →
         ρ₁ · ρ₂ ~ ρ₃ →
         ρ₁ ≲ ρ₃
·-to-≲L (_ , l , _) = l

·-to-≲R : ∀ {ℓ} {A : Set ℓ} → {ρ₁ ρ₂ ρ₃  : Row {ℓ} A} →
         ρ₁ · ρ₂ ~ ρ₃ →
         ρ₂ ≲ ρ₃
·-to-≲R (_ , _ , r) = r

--------------------------------------------------------------------------------
-- "Punching out" an index from ρ.

_pick_ : ∀ {ℓ} {A : Set ℓ} → (ρ : Row {ℓ} A) → Ix {ℓ} ρ → Row {ℓ} A
_pick_ {ℓ} {A} ρ i = sing (snd ρ i)

_delete_ : ∀ {ℓ} {A : Set ℓ} → (ρ : Row {ℓ} A) → Ix {ℓ} ρ → Row {ℓ} A
_delete_ {ℓ} {A} (suc n , f) i = n , (λ j → f (punchIn i j))

--------------------------------------------------------------------------------
-- Lifting functions (and arguments) to rows.

lift₁ : ∀ {ℓ} {A B : Set ℓ} → Row {ℓ} (A → B) → A → Row {ℓ} B
lift₁ {A = A} {B = B} (n , P) a = (n , (λ m → P m a))

lift₂ : ∀ {ℓ} {A B : Set ℓ} → (A → B) → Row {ℓ} A → Row {ℓ} B
lift₂ {A = A} {B = B} f (n , P) = (n , (λ m → f (P m)))

