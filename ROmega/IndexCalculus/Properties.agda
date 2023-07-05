{-# OPTIONS --safe #-}
module ROmega.IndexCalculus.Properties where


open import Agda.Primitive

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
  hiding (map)
open import Data.Product
  using (_×_; ∃; ∃-syntax; Σ-syntax; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
open import Data.Fin  renaming (zero to fzero; suc to fsuc)

open import ROmega.IndexCalculus.Rows

--------------------------------------------------------------------------------
-- Building evidence that ρ pick i · ρ delete i ~ ρ.

pickedIn : ∀ {ℓ} {A : Set ℓ} {ρ : Row {ℓ} A} {i : Ix {ℓ} ρ} → ρ pick i ≲ ρ
pickedIn {ℓ} {A} {suc _ , _} {i} fzero = i , refl

deletedIn : ∀ {ℓ} {A : Set ℓ} {ρ : Row {ℓ} A} {i : Ix {ℓ} ρ} → ρ delete i ≲ ρ
deletedIn {ℓ} {A} {suc _ , f} {fzero} fzero = fsuc fzero , refl
deletedIn {ℓ} {A} {suc _ , f} {fsuc i} fzero = fzero , refl
deletedIn {ℓ} {A} {suc _ , f} {fzero} (fsuc j) = fsuc (fsuc j) , refl
deletedIn {ℓ} {A} {suc _ , f} {fsuc i} (fsuc j) = (fsuc (punchIn i j)) , refl

recombine : ∀ {ℓ} {A : Set ℓ} → (ρ : Row {ℓ} A) → (i : Ix {ℓ} ρ) → ρ pick i · ρ delete i ~ ρ
recombine {ℓ} {A} ρ i = evid ρ i , (pickedIn , deletedIn {i = i}) where
  evid : (ρ : Row {ℓ} A) (i : Ix {ℓ} ρ) (j : Fin (fst ρ)) →
            Σi[ k ≤ fst (ρ pick i) ] (snd (ρ pick i) k ≡ snd ρ j) at ℓ or
            Σi[ k ≤ fst (ρ delete i) ] (snd (ρ delete i) k ≡ snd ρ j) at ℓ
  evid ρ fzero fzero = left (fzero , refl)
  evid ρ fzero (fsuc j) = right (j , refl)
  evid (suc (suc n) , f) (fsuc i) fzero = right (fzero , refl)
  evid (suc zero , f) (fsuc ()) fzero
  evid (suc (suc n) , f) (fsuc i) (fsuc j)
    with evid (suc n , λ x → f (fsuc x)) i j
  ... | left (fzero , g) = left (fzero , g)
  ... | right (i' , g)   = right ((raise 1 i') , g)
