{-# OPTIONS --safe #-}
module ROmega.Terms.Syntax where

open import Agda.Primitive

open import ROmega.Kinds
open import ROmega.Types
open import ROmega.Types.Substitution
open import ROmega.Equivalence.Syntax

open import ROmega.Entailment.Syntax

--------------------------------------------------------------------------------
-- Environments.

data Env : {ℓ : Level} → KEnv ℓ → Level → Set where
  ε : ∀ {ℓΔ} {Δ : KEnv ℓΔ} →
        Env Δ lzero
  _,_ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓκ} →
          Env Δ ℓΓ → Type Δ (★ ℓκ) → Env Δ (ℓΓ ⊔ ℓκ)

-- Weakening of the kinding env.
weakΓ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓκ} {κ : Kind ℓκ} →
        Env Δ ℓΓ → Env (Δ , κ) ℓΓ
weakΓ ε = ε
weakΓ (Γ , τ) = weakΓ Γ , rename S τ

--------------------------------------------------------------------------------
-- Variables.

data Var : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓκ} {κ : Kind ℓκ} →
           Env Δ ℓΓ → Type Δ κ → Set where
  Z : ∀ {ℓΔ : Level} {Δ : KEnv ℓΔ} {ℓΓ}
        {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
        Var (Γ , τ) τ
  S : ∀ {ℓΔ : Level} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ}
        {ℓυ ℓτ} {τ : Type Δ (★ ℓτ)} {υ : Type Δ (★ ℓυ)} →
         Var Γ υ → Var (Γ , τ) υ        

--------------------------------------------------------------------------------
-- Synonyms, used later.

SynT : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} →
       (κ : Kind ℓκ) → (ρ : Type Δ R[ κ ]) →
       (φ : Type Δ (κ `→ ★ ℓκ)) → Type Δ (★ (lsuc ℓκ))
SynT {ℓΔ} {ℓκ} κ ρ φ =
  `∀ (L {lzero}) (`∀ κ (`∀ R[ κ ] ((l R▹ u) · y ~ ρ' ⇒
    (⌊_⌋ {ι = lzero} l `→ φ' ·[ u ]))))
    where
      ρ' = weaken (weaken (weaken ρ))
      φ' = weaken (weaken (weaken φ))
      y = tvar Z
      u = tvar (S Z)
      l = tvar (S (S Z))

AnaT : ∀ {ℓΔ ℓκ ℓτ} {Δ : KEnv ℓΔ} →
       (κ : Kind ℓκ) → (ρ : Type Δ R[ κ ])
       (φ : Type Δ (κ `→ ★ ℓκ)) (τ : Type Δ (★ ℓτ)) →
       Type Δ (★ (ℓτ ⊔ lsuc ℓκ))
AnaT {ℓΔ} {ℓκ} {ℓτ} κ ρ φ τ =
  `∀ (L {lzero}) (`∀ κ (`∀ R[ κ ] ((l R▹ u) · y ~ ρ' ⇒
    ⌊_⌋ {ι = lzero} l `→ φ' ·[ u ] `→ τ')))
    where
      ρ' = weaken (weaken (weaken ρ))
      φ' = weaken (weaken (weaken φ))
      τ' = weaken (weaken (weaken τ))
      y = tvar Z
      u = tvar (S Z)
      l = tvar (S (S Z))

FoldT : ∀ {ℓΔ ℓκ ℓυ} {Δ : KEnv ℓΔ} →
       (ρ : Type Δ R[ ★ ℓκ ])(υ : Type Δ (★ ℓυ)) →
       Type Δ (★ (ℓυ ⊔ lsuc ℓκ))
FoldT {ℓκ = ℓκ} ρ υ =
  `∀ (L {lzero}) (`∀ (★ ℓκ) (`∀ R[ ★ ℓκ ] ((l R▹ t) · y ~ ρ' ⇒
    ⌊_⌋ {ι = lzero} l `→ t `→ υ')))
    where
      ρ' = weaken (weaken (weaken ρ))
      υ' = weaken (weaken (weaken υ))
      y = tvar Z
      t = tvar (S Z)
      l = tvar (S (S Z))

--------------------------------------------------------------------------------
-- Terms.
module TermSyntax 
  (Ent : 
    ∀ {ℓΔ ℓΦ ℓκ}
      {κ : Kind ℓκ}
      (Δ : KEnv ℓΔ) → PEnv Δ ℓΦ → Pred Δ κ → Set) where

  data Term : ∀ {ℓΔ} (Δ : KEnv ℓΔ) {ℓΦ ℓΓ ℓτ} → PEnv Δ ℓΦ → Env Δ ℓΓ → Type Δ (★ ℓτ) → Set where
    ------------------------------------------------------------
    -- System Fω.
  
    var : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ ℓτ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ} {τ : Type Δ (★ ℓτ)} →
  
             Var Γ τ →
             -------------
             Term Δ Φ Γ τ
  
    `λ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ ℓτ ℓυ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ} {υ : Type Δ (★ ℓυ)}
  
             (τ : Type Δ (★ ℓτ)) → Term Δ Φ (Γ , τ) υ →
             -------------------------------------
             Term Δ Φ Γ (τ `→ υ)
  
    _·_ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ ℓτ ℓυ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ} {τ : Type Δ (★ ℓτ)} {υ : Type Δ (★ ℓυ)} →
  
             Term Δ Φ Γ (τ `→ υ) → Term Δ Φ Γ τ →
             ----------------------------
             Term Δ Φ Γ υ
  
    `Λ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
           {ℓκ ℓτ} (κ : Kind ℓκ) {τ : Type (Δ , κ) (★ ℓτ)} →
  
         Term (Δ , κ) (weakΦ Φ) (weakΓ Γ) τ →
         ----------------------------------------------------
         Term Δ Φ Γ (`∀ κ τ)
  
  
    _·[_] : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ} {ℓκ ℓτ}
              {κ : Kind ℓκ} {τ : Type (Δ , κ) (★ ℓτ)} →
  
             Term Δ Φ Γ (`∀ κ τ) → (υ : Type Δ κ) →
             ----------------------------------
             Term Δ Φ Γ (τ β[ υ ])
  
    ------------------------------------------------------------
    -- Qualified types.
  
    `ƛ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
            {ℓκ ℓτ} {κ : Kind ℓκ} {τ : Type Δ (★ ℓτ)} →
  
             (π : Pred Δ κ) → Term Δ (Φ , π) Γ τ →
             -------------------------------------
             Term Δ Φ Γ (π ⇒ τ)
  
    _·⟨_⟩ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΦ ℓΓ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
           {ℓκ ℓτ} {κ : Kind ℓκ} {π : Pred Δ κ} {τ : Type Δ (★ ℓτ)} →
  
           Term Δ Φ Γ (π ⇒ τ) → Ent Δ Φ π →
           ----------------------------------
           Term Δ Φ Γ τ
                
    ------------------------------------------------------------
    -- System Rω.
  
    -- labels.
    lab : ∀ {ℓΔ ℓΓ ℓΦ ℓL ι} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
            (l : Type Δ (L {ℓL})) →
            ----------------------------------------
            Term Δ Φ Γ (⌊_⌋ {ι = ι} l)
    
  
    -- singleton introduction.
    _▹_ : ∀ {ℓΔ ℓΓ ℓΦ ℓL ℓκ ι} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
            {τ : Type Δ (L {ℓL})} {υ : Type Δ (★ ℓκ)} →
            (M₁ : Term Δ Φ Γ (⌊_⌋ {ι = ι} τ)) (M₂ : Term Δ Φ Γ υ) →
            ----------------------------------------
            Term Δ Φ Γ (τ ▹ υ)          
  
    -- singleton elimination.
    _/_ : ∀ {ℓΔ ℓΓ ℓΦ ℓL ℓκ ι} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
            {τ : Type Δ (L {ℓL})} {υ : Type Δ (★ ℓκ)} →
            (M₁ : Term Δ Φ Γ (τ ▹ υ)) (M₂ : Term Δ Φ Γ (⌊_⌋ {ι = ι} τ)) →
            ----------------------------------------
            Term Δ Φ Γ υ
  
    -- The empty record.
    -- (Not a part of pen-and-paper calculus.)
    ∅ : ∀ {ℓΔ ℓΓ ℓΦ ι} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →

          -----------
          Term Δ Φ Γ (∅ {ι = ι})
  
    -- record introduction.
    _⊹_ : ∀ {ℓΔ ℓΓ ℓΦ ℓρ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ℓρ ])} →
        
            (M : Term Δ Φ Γ (Π ρ₁)) (N : Term Δ Φ Γ (Π ρ₂)) →
            (π : Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃)) →
            ------------------------------
            Term Δ Φ Γ (Π ρ₃)
    
    -- record "elimination".
    prj : ∀ {ℓΔ ℓΓ ℓΦ ℓρ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {ρ₁ ρ₂ : Type Δ (R[ ★ ℓρ ])} →
          
            (M : Term Δ Φ Γ (Π ρ₁)) → (π : Ent Δ Φ (ρ₂ ≲ ρ₁)) →
            ------------------------------
            Term Δ Φ Γ (Π ρ₂)
  
    -- Singleton → Singleton Record.
    Π : ∀ {ℓΔ ℓΓ ℓΦ ℓL ℓκ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {τ : Type Δ (L {ℓL})} {υ : Type Δ (★ ℓκ)} →
          
            Term Δ Φ Γ (τ ▹ υ) →
            ---------------------
            Term Δ Φ Γ (Π (τ R▹ υ))
  
    -- Singleton Record → Singleton.
    Π⁻¹ : ∀ {ℓΔ ℓΓ ℓΦ ℓL ℓκ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {τ : Type Δ (L {ℓL})} {υ : Type Δ (★ ℓκ)} →
          
            (M : Term Δ Φ Γ (Π (τ R▹ υ))) →
            ----------------------------------------
            Term Δ Φ Γ (τ ▹ υ)
            
    -- Subsumption.
    t-≡ : ∀ {ℓΔ ℓΦ ℓΓ ℓτ} { Δ : KEnv ℓΔ} {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
          {τ υ : Type Δ (★ ℓτ)}  →
  
            (M : Term Δ Φ Γ τ) → τ ≡t υ →
            ----------------------------
            Term Δ Φ Γ υ
  
    -- Variant introduction.
    inj : ∀ {ℓΔ ℓΓ ℓΦ ℓρ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {ρ₁ ρ₂ : Type Δ (R[ ★ ℓρ ])} →
        
            (M : Term Δ Φ Γ (Σ ρ₁)) → (Ent Δ Φ (ρ₁ ≲ ρ₂)) →
            ----------------------------------------------
            Term Δ Φ Γ (Σ ρ₂)
  
    -- Singleton Record → Singleton.
    Σ : ∀ {ℓΔ ℓΓ ℓΦ ℓL ℓκ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {τ : Type Δ (L {ℓL})} {υ : Type Δ (★ ℓκ)} →
          
            Term Δ Φ Γ (τ ▹ υ) →
            ---------------------
            Term Δ Φ Γ (Σ (τ R▹ υ))
            
    -- Singleton Variant → Singleton.
    Σ⁻¹ : ∀ {ℓΔ ℓΓ ℓΦ ℓL ℓκ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {τ : Type Δ (L {ℓL})} {υ : Type Δ (★ ℓκ)} →
          
            (M : Term Δ Φ Γ (Σ (τ R▹ υ))) →
            ----------------------------------------
            Term Δ Φ Γ (τ ▹ υ)
             
    -- Variant elimination.
    _▿_ : ∀ {ℓΔ ℓΓ ℓΦ ℓρ ℓκ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ℓρ ])} {τ : Type Δ (★ ℓκ)} →
        
            Term Δ Φ Γ ((Σ ρ₁) `→ τ) →
            Term Δ Φ Γ ((Σ ρ₂) `→ τ) →
            Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
            ------------------------------
            Term Δ Φ Γ ((Σ ρ₃) `→ τ)
             
    -- Synthesis.
    syn : ∀ {ℓΔ ℓΓ ℓΦ ℓκ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {κ : Kind ℓκ}
    
           (ρ : Type Δ R[ κ ]) →
           (φ : Type Δ (κ `→ ★ ℓκ)) →
           Term Δ Φ Γ (SynT κ ρ φ) →
           --------------------------
           Term Δ Φ Γ (Π (⌈ φ ⌉· ρ))
  
    -- Analysis.
    ana : ∀ {ℓΔ ℓΓ ℓΦ ℓκ ℓτ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {κ : Kind ℓκ}
    
           (ρ : Type Δ R[ κ ]) →
           (φ : Type Δ (κ `→ ★ ℓκ)) →
           (τ : Type Δ (★ ℓτ)) →
           Term Δ Φ Γ (AnaT κ ρ φ τ) →
           --------------------------
           Term Δ Φ Γ (Σ (⌈ φ ⌉· ρ) `→ τ)
  
    -- Fold.
    fold : ∀ {ℓΔ ℓΓ ℓΦ ℓκ ℓυ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
           {ρ : Type Δ R[ ★ ℓκ ]} {υ : Type Δ (★ ℓυ)} →
           (M₁ : Term Δ Φ Γ (FoldT ρ υ)) →
           (M₂ : Term Δ Φ Γ (υ `→ (υ `→ υ))) →
           (M₃ : Term Δ Φ Γ υ) →
           (N  : Term Δ Φ Γ (Π ρ)) →
           ------------------------
           Term Δ Φ Γ υ
  
  --------------------------------------------------------------------------------
  -- admissable rules.
  
  private
    variable
      ℓΔ ℓΓ ℓΦ ℓκ ℓτ : Level
      Δ : KEnv ℓΔ
      Γ : Env Δ ℓΓ
      Φ : PEnv Δ ℓΦ
      κ : Kind ℓκ
      Ł : Type Δ L
      τ : Type Δ κ
  
  prj▹ : {ρ : Type Δ R[ ★ ℓκ ]} →          
          Term Δ Φ Γ (Π ρ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
          ------------------------------------------
          Term Δ Φ Γ (Ł ▹ τ)
  prj▹ r e = Π⁻¹ (prj r e)          
  
  inj▹ : {ρ : Type Δ R[ ★ ℓκ ]} →          
          Term Δ Φ Γ (Ł ▹ τ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
          ---------------------------------------------
          Term Δ Φ Γ (Σ ρ)
  inj▹ s e = inj (Σ s) e
  
