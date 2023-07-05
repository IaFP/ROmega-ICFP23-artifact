{-# OPTIONS --safe #-}
module ROmega.Types.Substitution where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ROmega.Kinds
open import ROmega.Types

--------------------------------------------------------------------------------
-- Defs.

-- A Δ-map (renaming) maps type vars in environment Δ₁ to environment Δ₂.
Δ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Δ-map Δ₁ Δ₂ =
  (∀ {ℓ₃} {κ : Kind ℓ₃} → TVar Δ₁ κ → TVar Δ₂ κ)

-- A mapping from types to types.
τ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
τ-map Δ₁ Δ₂ = (∀ {ℓ₃} {κ : Kind ℓ₃} → Type Δ₁ κ → Type Δ₂ κ)

-- A mapping from preds to preds.
π-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
π-map Δ₁ Δ₂ = ∀ {ℓ₃} {κ : Kind ℓ₃} → Pred Δ₁ κ → Pred Δ₂ κ

-- A Context maps type vars to types.
Context : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Context Δ₁ Δ₂ = ∀ {ℓ₃} {κ : Kind ℓ₃} → TVar Δ₁ κ → Type Δ₂ κ

--------------------------------------------------------------------------------
-- Extension.
--
-- Given a map from variables in one Context to variables in another, extension
-- yields a map from the first Context extended to the second Context similarly
-- extended.

ext : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} {ι : Kind ℓ₃} →
         Δ-map Δ₁ Δ₂ →
         Δ-map (Δ₁ , ι) (Δ₂ , ι)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming.
--
-- Renaming is a necessary prelude to substitution, enabling us to “rebase” a
-- type from one Context to another.

rename : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Δ-map Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂
renamePred : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Δ-map Δ₁ Δ₂ →
           π-map Δ₁ Δ₂

rename ρ (tvar v) = tvar (ρ v)
rename ρ (τ `→ υ) = rename ρ τ `→ rename ρ υ
rename ρ (`∀ κ τ) = `∀ κ (rename (ext ρ) τ)
rename ρ (`λ s τ) = `λ s (rename (ext ρ) τ)
rename ρ (τ ·[ υ ]) = rename ρ τ ·[ rename ρ υ ]
rename ρ U = U
rename ρ (lab l) = lab l
rename ρ (t ▹ v) = (rename ρ t) ▹ (rename ρ v)
rename ρ (⌊ t ⌋) = ⌊ rename ρ t ⌋
rename ρ (t R▹ v) = rename ρ t R▹ rename ρ v
rename ρ (Π r) = Π (rename ρ r)
rename ρ (Type.Σ r) = Type.Σ (rename ρ r)
rename ρ (π ⇒ τ) = renamePred ρ π ⇒ rename ρ τ
rename ρ (r ·⌈ τ ⌉) =  (rename ρ r)  ·⌈ (rename ρ τ) ⌉
rename ρ (⌈ τ ⌉· r) = ⌈ (rename ρ τ) ⌉· (rename ρ r)
rename ρ ∅ = ∅

renamePred ρ (ρ₁ ≲ ρ₂) = rename ρ ρ₁ ≲ rename ρ ρ₂
renamePred ρ (ρ₁ · ρ₂ ~ ρ₃) = rename ρ ρ₁ ·  rename ρ ρ₂ ~ rename ρ ρ₃

--------------------------------------------------------------------------------
-- Weakening (of a typing derivation.)

weaken : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
           τ-map Δ (Δ , κ)
weaken = rename S
           
--------------------------------------------------------------------------------
-- Simultaneous Substitution.
--
-- Instead of substituting a closed term for a single variable, we provide a
-- map that takes each free variable of the original type to another
-- tye. Further, the substituted terms are over an arbitrary Context, and need
-- not be closed.


exts : ∀ {ℓ₁ ℓ₂ ℓ₃}
         {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂}
         {ι : Kind ℓ₃} →
         Context Δ₁ Δ₂ →
         Context (Δ₁ , ι) (Δ₂ , ι) 
exts θ Z = tvar Z
exts θ (S x) = rename S (θ x)

--------------------------------------------------------------------------------
-- Substitution.
--

subst : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Context Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂

substPred : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
          Context Δ₁ Δ₂ →
          π-map Δ₁ Δ₂

subst θ (tvar x) = θ x
subst θ (τ `→ υ) = subst θ τ `→ subst θ υ
subst θ (`∀ κ τ) = `∀ κ (subst (exts θ) τ)
subst θ (`λ s τ) = `λ s (subst (exts θ) τ)
subst θ (τ ·[ υ ]) = subst θ τ ·[ subst θ υ ]
subst θ U = U
subst θ (lab l) = lab l
subst θ (t ▹ v) = (subst θ t) ▹ (subst θ v)
subst θ (⌊ t ⌋) = ⌊ subst θ t ⌋
subst θ (t R▹ v) = subst θ t R▹ subst θ v
subst θ (Π r) = Π (subst θ r)
subst θ (Type.Σ r) = Type.Σ (subst θ r)
subst θ (π ⇒ τ) = substPred θ π ⇒ subst θ τ
subst θ ( r ·⌈ τ ⌉) = (subst θ r) ·⌈ (subst θ τ) ⌉
subst θ ( ⌈ τ ⌉· r) = ⌈ (subst θ τ) ⌉· (subst θ r)
subst _ ∅ = ∅

substPred θ (ρ₁ ≲ ρ₂)      = subst θ ρ₁ ≲ subst θ ρ₂
substPred θ (ρ₁ · ρ₂ ~ ρ₃) = subst θ ρ₁ ·  subst θ ρ₂ ~ subst θ ρ₃

--------------------------------------------------------------------------------
-- Single substitution.

-- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
Z↦ : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
        Type Δ κ → Context (Δ , κ) Δ
Z↦ τ Z = τ
Z↦ τ (S x) = tvar x

-- Regular ol' substitution.
_β[_] : ∀ {ℓΔ ℓκ ℓι} {Δ : KEnv ℓΔ} {κ : Kind ℓκ}{ι : Kind ℓι}
         → Type (Δ , ι) κ → Type Δ ι → Type Δ κ
τ β[ υ ] = subst (Z↦ υ) τ

--------------------------------------------------------------------------------
-- examples, to move elsewhere

t0 : Type (ε , ★ lzero) (★ lzero)
t0 = tvar Z `→ tvar Z

_ : subst (Z↦ U) t0 ≡ U `→ U
_ = refl
