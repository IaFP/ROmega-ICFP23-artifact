{-# OPTIONS --safe #-}
module ROmega.Types.Semantics where

open import Agda.Primitive
open import Level

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)
  hiding (Σ)
open import Data.Unit.Polymorphic
open import Data.Empty.Polymorphic

open import ROmega.Kinds
open import ROmega.Types.Syntax
open import ROmega.IndexCalculus using (Row)
import ROmega.IndexCalculus as Ix

--------------------------------------------------------------------------------
-- The meaning of kinding environments and predicates (mutually recursive).

⟦_⟧ke : ∀ {ℓ} → KEnv ℓ → Set (lsuc ℓ)
⟦_⟧t : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} {κ : Kind ι} →
      Type Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k

⟦_⟧p : ∀ {ℓ ι} {Δ : KEnv ℓ} {κ : Kind ι} → Pred Δ κ → ⟦ Δ ⟧ke → Set (lsuc ι)
⟦ ρ₁ ≲ ρ₂ ⟧p H = ⟦ ρ₁ ⟧t H Ix.≲ ⟦ ρ₂ ⟧t H
⟦ ρ₁ · ρ₂ ~ ρ₃ ⟧p H = Ix._·_~_ (⟦ ρ₁ ⟧t H) (⟦ ρ₂ ⟧t H) (⟦ ρ₃ ⟧t H)

⟦ ε ⟧ke = ⊤
⟦ Δ , κ ⟧ke =  ⟦ Δ ⟧ke × ⟦ κ ⟧k

--------------------------------------------------------------------------------
-- The meaning of type vars.

⟦_⟧tv : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} {κ : Kind ι}
        → TVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦ Z ⟧tv (_ , t) = t
⟦ S v ⟧tv (H , _) = ⟦ v ⟧tv H

--------------------------------------------------------------------------------
-- The meaning of types.

⟦ U ⟧t           H = ⊤
⟦ lab l ⟧t       H = tt
⟦ tvar v ⟧t      H = ⟦ v ⟧tv H
⟦ (t₁ `→ t₂) ⟧t H = ⟦ t₁ ⟧t H → ⟦ t₂ ⟧t H
⟦ `∀ κ v ⟧t      H = (s : ⟦ κ ⟧k) → ⟦ v ⟧t  (H , s)
⟦ t₁ ·[ t₂ ] ⟧t  H = (⟦ t₁ ⟧t H) (⟦ t₂ ⟧t H)
⟦ `λ κ v ⟧t     H =  λ (s : ⟦ κ ⟧k) → ⟦ v ⟧t (H , s)
⟦ _ ▹ v ⟧t       H = ⟦ v ⟧t H
⟦ _R▹_ {ℓ} {ι} {_} {κ} _ τ ⟧t H = Ix.sing (⟦ τ ⟧t H)
⟦ ⌊ τ ⌋ ⟧t H       = ⊤
⟦ Π ρ ⟧t H = Ix.Π (⟦ ρ ⟧t H)
⟦ Σ ρ ⟧t H = Ix.Σ (⟦ ρ ⟧t H)
⟦ ρ ·⌈ τ ⌉ ⟧t H =  Ix.lift₁ (⟦ ρ ⟧t H) (⟦ τ ⟧t H)
⟦ ⌈ τ ⌉· ρ ⟧t H = Ix.lift₂ (⟦ τ ⟧t H) (⟦ ρ ⟧t H)
⟦ π ⇒ τ ⟧t H = ⟦ π ⟧p H → ⟦ τ ⟧t H
⟦ ∅ ⟧t  H = Ix.Π (0 , (λ x → ⊥))
