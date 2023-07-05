{-# OPTIONS --safe #-}
module ROmega.Kinds.Syntax where

open import Agda.Primitive
open import Level

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Level → Set where
  ★ : (ℓ : Level) → Kind ℓ
  _`→_ : ∀ {ℓ₁ ℓ₂} → Kind ℓ₁ → Kind ℓ₂ → Kind (ℓ₁ ⊔ ℓ₂)
  L : ∀ {ℓ} → Kind ℓ
  R[_] : ∀ {ℓ} → Kind ℓ → Kind ℓ

-- type synonyms
lone ltwo lthree : Level
lone   = lsuc lzero
ltwo   = lsuc lone
lthree = lsuc ltwo

★₀ = ★ lzero
★₁ = ★ lone
★₂ = ★ ltwo
