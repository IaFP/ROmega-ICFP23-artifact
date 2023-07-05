{-# OPTIONS --safe #-}
module ROmega.Entailment.Syntax where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Unit.Polymorphic
open import Data.Product renaming (Σ to Sum)

open import ROmega.Kinds
open import ROmega.Types
open import ROmega.Types.Substitution
open import ROmega.Equivalence.Syntax

--------------------------------------------------------------------------------
-- Environments & weakening.

data PEnv : {ℓ : Level} → KEnv ℓ → Level → Set where
  ε : ∀ {ℓΔ} {Δ : KEnv ℓΔ} →
        PEnv Δ lzero
  _,_ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓκ} {κ : Kind ℓκ} →
          PEnv Δ ℓΦ → Pred Δ κ → PEnv Δ (ℓΦ ⊔ ℓκ)


weakΦ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓκ} {κ : Kind ℓκ} →
          PEnv Δ ℓΦ → PEnv (Δ , κ) ℓΦ
weakΦ ε = ε
weakΦ (Φ , π) = weakΦ Φ , renamePred S π

--------------------------------------------------------------------------------
-- Predicate variables.

data PVar : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓκ} {κ : Kind ℓκ} →
              PEnv Δ ℓΦ → Pred Δ κ → Set where
  Z : ∀ {ℓΔ : Level} {Δ : KEnv ℓΔ} {ℓΓ}
        {Φ : PEnv Δ ℓΓ} {ℓκ} {κ : Kind ℓκ} {π : Pred Δ κ} →
        PVar (Φ , π) π
  S : ∀ {ℓΔ : Level} {Δ : KEnv ℓΔ} {ℓΦ} {Φ : PEnv Δ ℓΦ}
        {ℓι ℓκ} {ι : Kind ℓι} {κ : Kind ℓκ}
        {π : Pred Δ ι} {ψ : Pred Δ κ} →
        PVar Φ π → PVar (Φ , ψ) π

--------------------------------------------------------------------------------
-- Entailment in the "Simple Rows" theory.

private
  variable
    ℓΔ ℓΦ ℓκ : Level
    Δ : KEnv ℓΔ
    Φ : PEnv Δ ℓΦ
    κ : Kind ℓκ
    π : Pred Δ κ

module SimpleRowSyntax where
  data Ent : (Δ : KEnv ℓΔ) → PEnv Δ ℓΦ → Pred Δ κ → Set where
  
    n-var : ∀  {π : Pred Δ κ} →
  
             PVar Φ π →
             -------------
             Ent Δ Φ π
  
    n-refl : ∀  {τ : Type Δ R[ κ ]} →
  
            --------------
            Ent Δ Φ (τ ≲ τ)
  
    n-trans : ∀  {τ₁ τ₂ τ₃ : Type Δ R[ κ ]} →
  
            Ent Δ Φ (τ₁ ≲ τ₂) → Ent Δ Φ (τ₂ ≲ τ₃) →
            ---------------------------------------
            Ent Δ Φ (τ₁ ≲ τ₃)
  
    n-≡ : ∀ {π₁ π₂ : Pred Δ κ} →
          
          π₁ ≡p π₂ → Ent Δ Φ π₁ →
          ------------------------
          Ent Δ Φ π₂
  
    n-≲lift₁ : ∀  {κ' : Kind ℓκ}
               {ρ₁ ρ₂ : Type Δ R[ κ `→ κ' ]}
               {τ : Type Δ κ} →
    
               Ent Δ Φ (ρ₁ ≲ ρ₂) →
               ---------------------
               Ent Δ Φ (( ρ₁ ·⌈ τ ⌉) ≲ (ρ₂ ·⌈ τ ⌉))
    
    n-≲lift₂ : ∀  {κ' : Kind ℓκ}
               {ρ₁ ρ₂ : Type Δ R[ κ ]}
               {τ : Type Δ (κ `→ κ')} →
    
               Ent Δ Φ (ρ₁ ≲ ρ₂) →
               ---------------------
               Ent Δ Φ ((⌈ τ ⌉· ρ₁) ≲ (⌈ τ ⌉· ρ₂))
  
    n-·lift₁ : ∀  {κ' : Kind ℓκ}
               {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ `→ κ' ]}
               {τ : Type Δ κ} →
    
               Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
               ---------------------
               Ent Δ Φ ((ρ₁ ·⌈ τ ⌉) · (ρ₂ ·⌈ τ ⌉) ~ (ρ₃ ·⌈ τ ⌉))
  
    n-·lift₂ : ∀  {κ' : Kind ℓκ}
               {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]}
               {τ : Type Δ (κ `→ κ')} →
    
               Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
               ---------------------
               Ent Δ Φ ((⌈ τ ⌉· ρ₁) · (⌈ τ ⌉· ρ₂) ~ (⌈ τ ⌉· ρ₃))
            
    n-·≲L : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]} →
  
          Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
          ---------------------
          Ent Δ Φ (ρ₁ ≲ ρ₃)
          
  
    n-·≲R : ∀  {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]} →
  
          Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
          ---------------------
          Ent Δ Φ (ρ₂ ≲ ρ₃)
