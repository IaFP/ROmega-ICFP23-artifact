{-# OPTIONS --safe #-}
module ROmega.Kinds.Semantics where

open import Agda.Primitive
open import Level

open import Data.Unit.Polymorphic

open import ROmega.IndexCalculus using (Row)
open import ROmega.Kinds.Syntax

--------------------------------------------------------------------------------
-- The meaning of kinds.

⟦_⟧k : ∀ {ℓ} → Kind ℓ → Set (lsuc ℓ)
⟦ ★ ℓ ⟧k = Set ℓ
⟦ κ₁ `→ κ₂ ⟧k = ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
⟦ L ⟧k = ⊤
⟦_⟧k {ℓ} R[ k ] = Row ⟦ k ⟧k
