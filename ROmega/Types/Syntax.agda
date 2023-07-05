{-# OPTIONS --safe #-}
module ROmega.Types.Syntax where

open import Agda.Primitive
open import Level

open import Data.String

open import ROmega.Kinds.Syntax

--------------------------------------------------------------------------------
-- infix OOP.

infixr 9 _`→_
infixr 9 _⇒_
infixr 10 _▹_
infixr 10 _R▹_
infixr 10 _≲_
infix 10 _·_~_
infixl 11 _·[_]

--------------------------------------------------------------------------------
-- Labels are Strings.

Label : Set
Label = String

--------------------------------------------------------------------------------
-- Kinding Environments, types, and predicates.
--
-- Kinding Environments, types, and predicates are tied up together, like so:
--   - Pred references Ty, KEnv
--   - Type   references KEnv
--   - KEnv references Pred

data KEnv : Level → Set
data Type : {ℓ ι : Level} → KEnv ℓ → Kind ι →  Set
data Pred {ℓ ι : Level} (Δ : KEnv ℓ) (κ : Kind ι) : Set

data Pred Δ κ where
  _≲_ : (ρ₁ : Type Δ R[ κ ]) →
        (ρ₂ : Type Δ R[ κ ]) →
        Pred Δ κ

  _·_~_ : (ρ₁ : Type Δ R[ κ ]) →
          (ρ₂ : Type Δ R[ κ ]) →
          (ρ₃ : Type Δ R[ κ ]) →
          Pred Δ κ

data KEnv where
  ε    : KEnv lzero
  _,_  : ∀ {ℓ ι} → KEnv ℓ → Kind ι → KEnv (ℓ ⊔ ι)

--------------------------------------------------------------------------------
-- Type vars.
data TVar : ∀ {ℓ ι} → KEnv ℓ → Kind ι → Set where
  Z : ∀ {ℓ₁ ℓ₂} {Δ : KEnv ℓ₁} {κ : Kind ℓ₂}
      → TVar (Δ , κ) κ
  S : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ : KEnv ℓ₁} {κ : Kind ℓ₂} {κ' : Kind ℓ₃}
      → TVar Δ κ → TVar (Δ , κ') κ

--------------------------------------------------------------------------------
-- Types.

data Type where
  ------------------------------------------------------------
  -- Base types (for mechanization).

  -- Unit (Mechanization.)
  U : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} →

         --------------
         Type Δ (★ ι)

  ------------------------------------------------------------
  -- System Fω.

  tvar : ∀ {ℓ₁ ℓ₂ : Level} {Δ : KEnv ℓ₁} {κ : Kind ℓ₂} →

         TVar Δ κ →
         -----------
         Type Δ κ

  _`→_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {Δ : KEnv ℓ₁} →
          Type Δ (★ ℓ₂) → Type Δ (★ ℓ₃) →
          -----------------------------------
          Type Δ (★ (ℓ₂ ⊔ ℓ₃))

  `∀ :  ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {Δ : KEnv ℓ₁} →
          (κ : Kind ℓ₃) → Type (Δ , κ) (★ ℓ₂) →
          -------------------------------------
          Type Δ (★ (ℓ₂ ⊔ (lsuc ℓ₃)))

  `λ :  ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {Δ : KEnv ℓ₁} (κ₁ : Kind ℓ₂) {κ₂ : Kind ℓ₃} →
          Type (Δ , κ₁) κ₂ →
          -----------------------------------------
          Type Δ (κ₁ `→ κ₂)

  _·[_] : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {Δ : KEnv ℓ₁} {κ₁ : Kind ℓ₂} {κ₂ : Kind ℓ₃} →
          Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          -----------------------------
          Type Δ κ₂
  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {ℓ ℓκ ℓτ} {κ : Kind ℓκ} {Δ : KEnv ℓ}
          → (π : Pred Δ κ) → Type Δ (★ ℓτ) →
         --------------------------------
         Type Δ (★ (lsuc ℓκ ⊔ ℓτ))

  ------------------------------------------------------------
  -- System Rω.

  -- Labels.
  lab : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} →
        Label →
        ----------
        Type Δ (L {ι})

  -- singleton formation.
  _▹_ : ∀ {ℓΔ ℓκ ℓL : Level} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
        Type Δ (L {ℓL}) → Type Δ κ →
        -------------------
        Type Δ κ

  -- Row singleton formation.
  _R▹_ : ∀ {ℓΔ ℓκ ℓL : Level} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
         Type Δ (L {ℓL}) → Type Δ κ →
         -------------------
         Type Δ R[ κ ]

  -- label constant formation.
  ⌊_⌋ : ∀ {ℓΔ ℓL ι : Level} {Δ : KEnv ℓΔ} →
        Type Δ (L {ℓL}) →
        ----------
        Type Δ (★ ι)

  -- The empty record (mechanization only.)
  ∅ : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} →
  
      --------------
      Type Δ (★ ι)

  -- Record formation.
  Π : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} →
      Type Δ R[ ★ ι ] →
      -------------
      Type Δ (★ ι)

  -- Variant formation.
  Σ : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} →
      Type Δ R[ ★ ι ] →
      -------------
      Type Δ (★ ι)

  -- lift₁ (lifting a function argument to row kind).
  _·⌈_⌉ : ∀ {ℓ ι} {Δ : KEnv ℓ}
            {κ₁ κ₂ : Kind ι} →
          Type Δ R[ κ₁ `→ κ₂ ] → Type Δ κ₁ →
          --------------------------------
          Type Δ R[ κ₂ ]

  -- lift₂ (lifting a function to row kind.)
  ⌈_⌉·_ : ∀ {ℓ ι} {Δ : KEnv ℓ}
            {κ₁ κ₂ : Kind ι} →
          Type Δ (κ₁ `→ κ₂) → Type Δ R[ κ₁ ] →
          --------------------------------
          Type Δ R[ κ₂ ]

