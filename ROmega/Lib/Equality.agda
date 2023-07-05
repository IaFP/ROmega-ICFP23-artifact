{-# OPTIONS --safe #-}
module ROmega.Lib.Equality where

open import Relation.Binary.PropositionalEquality using (_≡_; subst)

--------------------------------------------------------------------------------
-- For convenience.

≡-elim : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
≡-elim x = subst (λ x → x) x
