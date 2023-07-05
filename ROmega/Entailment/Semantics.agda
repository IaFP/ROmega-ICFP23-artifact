module ROmega.Entailment.Semantics where

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

open import ROmega.Kinds
open import ROmega.Types
open import ROmega.Equivalence -- extensionality
open import ROmega.Terms.Syntax
open import ROmega.Entailment.Syntax

--------------------------------------------------------------------------------
-- The meaning of predicate environments.

⟦_⟧pe : ∀ {ℓΔ} {ℓΦ} {Δ : KEnv ℓΔ} →
          PEnv Δ ℓΦ → ⟦ Δ ⟧ke → Set (lsuc ℓΦ)
⟦ ε ⟧pe H = ⊤
⟦ Φ , π ⟧pe H = ⟦ Φ ⟧pe H × ⟦ π ⟧p H

--------------------------------------------------------------------------------
-- The meaning of predicate variables.

⟦_⟧pv : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ} {Φ : PEnv Δ ℓΦ} {ℓκ} {κ : Kind ℓκ} {π : Pred Δ κ} →
          PVar Φ π → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ π ⟧p H
⟦ Z ⟧pv H (φ , x) = x
⟦ S v ⟧pv H (φ , x) = ⟦ v ⟧pv H φ

--------------------------------------------------------------------------------
-- The meaning of entailment in the "Simple Rows" theory.


module SimpleRowSemantics where
  open SimpleRowSyntax

  ⟦_⟧n : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓκ} {Φ : PEnv Δ ℓΦ} {κ : Kind ℓκ} {π : Pred Δ κ} →
           Ent Δ Φ π → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ π ⟧p H
  ⟦ n-var x ⟧n H φ =  ⟦ x ⟧pv H φ
  ⟦ n-refl ⟧n H φ = λ i → i , refl
  ⟦ n-·≲L π ⟧n H φ with ⟦ π ⟧n H φ
  ... | _ , ρ₁≲ρ₃ , _ = ρ₁≲ρ₃
  ⟦ n-·≲R π ⟧n H φ with ⟦ π ⟧n H φ
  ... | _ , _ , ρ₁≲ρ₂ = ρ₁≲ρ₂
  ⟦ n-≲lift₁ π ⟧n H φ i with ⟦ π ⟧n H φ i
  ... | j , eq rewrite eq = j , refl
  ⟦ n-≲lift₂ π ⟧n H φ i with ⟦ π ⟧n H φ i
  ... | j , eq rewrite eq = j , refl
  ⟦ n-≡ eq π ⟧n H φ rewrite sym (⟦ eq ⟧eq-π H) = ⟦ π ⟧n H φ
  ⟦ n-trans t₁≲t₂ t₂≲t₃ ⟧n H φ i with ⟦ t₁≲t₂ ⟧n H φ i
  ... | j , eq with ⟦ t₂≲t₃ ⟧n H φ j
  ...   | k , eq' = k , trans eq eq'
  ⟦ n-·lift₁ {ρ₁ = ρ₁} {ρ₂} {ρ₃} {τ} π ⟧n H φ with ⟦ π ⟧n H φ
  ... | ρ₃≲ρ₁·ρ₂ , ρ₁≲ρ₃ , ρ₂≲ρ₃ = ρ₃τ≲ρ₁τ·ρ₂τ , ρ₁τ≲ρ₃τ , ρ₂τ≲ρ₃τ
    where
      ρ₃τ≲ρ₁τ·ρ₂τ : (i : Fin (fst (⟦ ρ₃ ⟧t H))) →
                    Data.Product.Σ (Fin (fst (⟦ ρ₁ ⟧t H)))
                    (λ j → snd (⟦ ρ₁ ⟧t H) j (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) i (⟦ τ ⟧t H))
                    or
                    Data.Product.Σ (Fin (fst (⟦ ρ₂ ⟧t H)))
                    (λ j → snd (⟦ ρ₂ ⟧t H) j (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) i (⟦ τ ⟧t H))
      ρ₃τ≲ρ₁τ·ρ₂τ i with ρ₃≲ρ₁·ρ₂ i
      ... | left (j , P) = left (j , cong-app P (⟦ τ ⟧t H))
      ... | right (j , P) = right (j , cong-app P (⟦ τ ⟧t H))
      ρ₁τ≲ρ₃τ : (i : Fin (fst (⟦ ρ₁ ⟧t H))) →
                Data.Product.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
                (λ j → snd (⟦ ρ₁ ⟧t H) i (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) j (⟦ τ ⟧t H))
      ρ₁τ≲ρ₃τ i with ρ₁≲ρ₃ i
      ... | j , P = j , cong-app P (⟦ τ ⟧t H)
  
      ρ₂τ≲ρ₃τ : (i : Fin (fst (⟦ ρ₂ ⟧t H))) →
                Data.Product.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
                (λ j → snd (⟦ ρ₂ ⟧t H) i (⟦ τ ⟧t H) ≡ snd (⟦ ρ₃ ⟧t H) j (⟦ τ ⟧t H))
      ρ₂τ≲ρ₃τ i with ρ₂≲ρ₃ i
      ... | j , P = j , cong-app P (⟦ τ ⟧t H)
  ⟦ n-·lift₂ {ρ₁ = ρ₁} {ρ₂} {ρ₃} {τ} π ⟧n H φ with ⟦ π ⟧n H φ
  ... | ρ₃≲ρ₁·ρ₂ , ρ₁≲ρ₃ , ρ₂≲ρ₃ = τρ₃≲τρ₁·τρ₂ , τρ₁≲τρ₃ , τρ₂τ≲τρ₃
    where
      τρ₃≲τρ₁·τρ₂ : (i : Fin (fst (⟦ ρ₃ ⟧t H))) →
                    Data.Product.Σ (Fin (fst (⟦ ρ₁ ⟧t H)))
                    (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₁ ⟧t H) j)  ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) i))
                    or
                    Data.Product.Σ (Fin (fst (⟦ ρ₂ ⟧t H)))
                    (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₂ ⟧t H) j) ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) i))
      τρ₃≲τρ₁·τρ₂ i with ρ₃≲ρ₁·ρ₂ i
      ... | left (j , P) = left (j , cong (⟦ τ ⟧t H) P)
      ... | right (j , P) = right (j , cong (⟦ τ ⟧t H) P)
      
      τρ₁≲τρ₃ : (i : Fin (fst (⟦ ρ₁ ⟧t H))) →
                Data.Product.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
                (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₁ ⟧t H) i) ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) j))
      τρ₁≲τρ₃ i with ρ₁≲ρ₃ i
      ... | j , P = j , cong (⟦ τ ⟧t H) P
  
      τρ₂τ≲τρ₃ : (i : Fin (fst (⟦ ρ₂ ⟧t H))) →
                Data.Product.Σ (Fin (fst (⟦ ρ₃ ⟧t H)))
                (λ j → (⟦ τ ⟧t H) (snd (⟦ ρ₂ ⟧t H) i) ≡ (⟦ τ ⟧t H) (snd (⟦ ρ₃ ⟧t H) j))
      τρ₂τ≲τρ₃ i with ρ₂≲ρ₃ i
      ... | j , P = j , cong (⟦ τ ⟧t H) P
  
  
