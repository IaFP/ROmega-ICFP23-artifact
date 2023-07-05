module ROmega.Terms.Semantics where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)

open import Data.Unit.Polymorphic
open import Data.Product
  using (_×_; Σ-syntax; _,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.Fin
  renaming (zero to fzero; suc to fsuc)
  hiding (fold)

open import ROmega.Kinds
open import ROmega.Types
open import ROmega.Types.Substitution
open import ROmega.Types.Substitution.Properties -- extensionality
open import ROmega.Terms.Syntax
open import ROmega.Equivalence -- extensionality
open import ROmega.Entailment -- extensionality
open import ROmega.Lib.Equality
open import ROmega.IndexCalculus
open import ROmega.IndexCalculus.Properties
import ROmega.IndexCalculus as Ix


--------------------------------------------------------------------------------
-- The meaning of environments.

⟦_⟧e : ∀ {ℓΔ} {ℓΓ} {Δ : KEnv ℓΔ} →
       Env Δ ℓΓ → ⟦ Δ ⟧ke → Set ℓΓ
⟦ ε ⟧e H = ⊤
⟦ Γ , τ ⟧e H = ⟦ Γ ⟧e H × ⟦ τ ⟧t H

--------------------------------------------------------------------------------
-- The meaning of variables.

⟦_⟧v : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
       Var Γ τ → (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e H → ⟦ τ ⟧t H
⟦ Z ⟧v H (η , x) = x
⟦ S v ⟧v H (η , x) = ⟦ v ⟧v H η


--------------------------------------------------------------------------------
-- Denotational Weakening Lemma.

weaken⟦_⟧e : ∀ {ℓΔ ℓΓ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Γ : Env Δ ℓΓ) → (H : ⟦ Δ ⟧ke) → (⟦Γ⟧ : ⟦ Γ ⟧e H) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΓ Γ ⟧e (H , X)
weaken⟦ ε ⟧e H ⟦Γ⟧ X = tt
weaken⟦_⟧e {Δ = Δ} {κ = κ} (_,_ {ℓκ = ℓκ} Γ τ) H (⟦Γ⟧ , ⟦τ⟧) X
  rewrite τ-preservation Δ (Δ , κ) H (H , X) S (λ _ → refl) τ = weaken⟦ Γ ⟧e H ⟦Γ⟧ X , ⟦τ⟧

weaken⟦_⟧pe : ∀ {ℓΔ ℓΦ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Φ : PEnv Δ ℓΦ) → (H : ⟦ Δ ⟧ke) → (⟦Φ⟧ : ⟦ Φ ⟧pe H) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΦ Φ ⟧pe (H , X)
weaken⟦ ε ⟧pe H ⟦Φ⟧ X = tt
weaken⟦_⟧pe {Δ = Δ} {κ} (Φ , π) H (⟦Φ⟧ , ⟦π⟧) X
  rewrite π-preservation Δ (Δ , κ) H (H , X) S (λ _ → refl) π = weaken⟦ Φ ⟧pe H ⟦Φ⟧ X , ⟦π⟧

--------------------------------------------------------------------------------
-- -- The meaning of terms.

-- open _↔_
-- open _≃_



module TermSemantics
  (Ent : 
    ∀ {ℓΔ ℓΦ ℓκ}
      {κ : Kind ℓκ}
      (Δ : KEnv ℓΔ) → PEnv Δ ℓΦ → Pred Δ κ → Set)
  (⟦_⟧n : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓκ} {Φ : PEnv Δ ℓΦ} {κ : Kind ℓκ} {π : Pred Δ κ} →
         Ent Δ Φ π → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ π ⟧p H)
  where
  
  open TermSyntax Ent

  ⟦_⟧ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ ℓτ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
          {τ : Type Δ (★ ℓτ)} →
          Term Δ Φ Γ τ →
          (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ Γ ⟧e H → ⟦ τ ⟧t H
  ⟦ var x ⟧ H φ η = ⟦ x ⟧v H η
  ⟦ `λ _ M ⟧ H φ η = λ x → ⟦ M ⟧ H φ (η , x)
  ⟦ M · N ⟧ H φ η = ⟦ M ⟧ H φ η (⟦ N ⟧ H φ η)
  ⟦ (`Λ κ M) ⟧ H φ η = λ (X : ⟦ κ ⟧k) → ⟦ M ⟧ (H , X) (weaken⟦ _ ⟧pe H φ X) (weaken⟦ _ ⟧e H η X)
  ⟦ _·[_] {τ = τ} M υ ⟧ H φ η
    rewrite (sym (Substitution τ υ H)) = ⟦ M ⟧ H φ η (⟦ υ ⟧t H)
  ⟦ `ƛ _ M ⟧ H φ η = λ x → ⟦ M ⟧ H (φ , x) η
  ⟦ M ·⟨ D ⟩ ⟧ H φ η = ⟦ M ⟧ H φ η (⟦ D ⟧n H φ)
  ⟦ (r₁ ⊹ r₂) π ⟧ H φ η i
    with ⟦ π ⟧n H φ | ⟦ r₁ ⟧ H φ η | ⟦ r₂ ⟧ H φ η
  ... | c , _ | r | r' with c i
  ... | left (n , eq) rewrite (sym eq) = r n
  ... | right (n , eq) rewrite (sym eq) = r' n
  ⟦ ∅ ⟧ H φ η ()
  ⟦ lab s ⟧ H φ η  = tt
  ⟦ prj r π ⟧ H φ η i with ⟦ r ⟧ H φ η | ⟦ π ⟧n H φ i
  ... | r' | n , eq rewrite eq = r' n
  ⟦ M ▹ N ⟧ H φ η = ⟦ N ⟧ H φ η
  ⟦ M / N ⟧ H φ η = ⟦ M ⟧ H φ η
  ⟦ t-≡ {τ = τ}{υ = υ} M τ≡υ ⟧ H φ η rewrite sym (⟦ τ≡υ ⟧eq H) = ⟦ M ⟧ H φ η -- (to (bi (⟦ τ≡υ ⟧eq H))) (⟦ M ⟧ H φ η)
  ⟦ inj M π ⟧ H φ η with ⟦ M ⟧ H φ η 
  ... | n , τ with ⟦ π ⟧n H φ n
  ...   | m , eq rewrite eq = m , τ
  ⟦ (M ▿ N) π ⟧ H φ η (p₃-i , P) with ⟦ M ⟧ H φ η | ⟦ N ⟧ H φ η | ⟦ π ⟧n H φ
  ... | ρ₁-elim | ρ₂-elim | (l , r)  with l p₃-i
  ... | left  s@(ρ₁-i , eq) rewrite (sym eq) = ρ₁-elim (ρ₁-i , P)
  ... | right s@(ρ₂-i , eq) rewrite (sym eq) = ρ₂-elim (ρ₂-i , P)
  ⟦ syn {Δ = Δ} {κ = κ} ρ f M ⟧ H₀ φ η i = 
    ≡-elim (sym (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd ⟦ρ⟧ i)))
    (⟦ M ⟧ H₀ φ η tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) evidence tt)
      where
        ⟦ρ⟧ = ⟦ ρ ⟧t H₀
        ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
        ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
        evidence : sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
                   ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
        evidence rewrite sym ⟦ρ⟧≡⟦weaken³ρ⟧ =  recombine ⟦ρ⟧ i
  
  ⟦ ana {Δ = Δ} {κ = κ} ρ f τ M ⟧ H₀ φ η (i , X) =
    ≡-elim (sym ⟦τ⟧≡⟦weaken³τ⟧)
    (⟦ M ⟧ H₀ φ η tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) evidence tt (≡-elim (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd (⟦ ρ ⟧t H₀) i)) X))
      where
        ⟦ρ⟧ = ⟦ ρ ⟧t H₀
        ⟦τ⟧≡⟦weaken³τ⟧ = Weakening₃ τ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
        ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
        ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
        evidence : sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
                   ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
        evidence rewrite sym ⟦ρ⟧≡⟦weaken³ρ⟧ =  recombine ⟦ρ⟧ i
  ⟦ Term.Π s ⟧ H φ η fzero = ⟦ s ⟧ H φ η
  ⟦ Term.Π s ⟧ H φ η (fsuc ())
  ⟦ Π⁻¹ r ⟧ H φ η = ⟦ r ⟧ H φ η fzero
  ⟦ Term.Σ s ⟧ H φ η = fzero , (⟦ s ⟧ H φ η)
  ⟦ Σ⁻¹ v ⟧ H φ η with ⟦ v ⟧ H φ η
  ... | fzero , M = M
  
  ⟦ fold {ℓκ = ℓκ} {ρ = ρ} {υ = υ} M₁ M₂ M₃ N ⟧ H φ η with 
    ⟦ M₁ ⟧ H φ η | ⟦ M₂ ⟧ H φ η | ⟦ M₃ ⟧ H φ η | ⟦ N ⟧ H φ η
  ... | op | _+_ | e | r = Ix.fold ⟦ρ⟧ f _+_ e r
    where
      ⟦ρ⟧ = ⟦ ρ ⟧t H
      ⟦υ⟧ = ⟦ υ ⟧t H
      f : ∀ (τ : Set ℓκ) (y : Row {lsuc ℓκ} (Set ℓκ)) →
                   (Ix._·_~_ (sing τ) y ⟦ρ⟧) → τ → ⟦υ⟧
      f τ y ev t rewrite Weakening₃ υ H tt τ y =
        op tt τ y (≡-elim weak-ev≡ev ev) tt t 
          where
            weak-ev≡ev :
              Ix._·_~_ (sing τ) y ⟦ρ⟧
              ≡
              Ix._·_~_ (sing τ) y (⟦ (weaken (weaken (weaken ρ))) ⟧t (((H , tt) , τ) , y))
            weak-ev≡ev rewrite Weakening₃ ρ H tt τ y = refl
      
  
