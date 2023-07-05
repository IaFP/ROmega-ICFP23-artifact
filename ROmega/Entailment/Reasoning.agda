{-# OPTIONS --safe #-}
module ROmega.Entailment.Reasoning where

open import Agda.Primitive

open import Function using (id)

open import ROmega.Kinds.Syntax
open import ROmega.Entailment.Syntax
open import ROmega.Types.Syntax

--------------------------------------------------------------------------------
-- Entailment derivations in the style of PLFA equational reasoning.

infixr 2 _⊩⟨_⟩_

private
  variable
    ℓΔ ℓΦ ℓκ : Level
    Δ : KEnv ℓΔ
    Φ : PEnv Δ ℓΦ
    κ : Kind ℓκ
    π : Pred Δ κ

open SimpleRowSyntax

_⊩⟨_⟩_ : ∀ {κ₁ κ₂ κ₃ : Kind ℓκ} {π₂ : Pred Δ κ₂}  {π₃ : Pred Δ κ₃} 
         (π₁ : Pred Δ κ₁) →
         (Ent Δ Φ π₁ → Ent Δ Φ π₂) →
         (Ent Δ Φ π₂ → Ent Δ Φ π₃) →
         Ent Δ Φ π₁ → Ent Δ Φ π₃
_⊩⟨_⟩_ π₁ 1→2 2→3 e₁ = 2→3 (1→2 e₁)         

∎ : Ent Δ Φ π →
     Ent Δ Φ π
∎ = id

--------------------------------------------------------------------------------

