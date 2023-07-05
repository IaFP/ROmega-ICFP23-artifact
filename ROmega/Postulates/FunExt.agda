module ROmega.Postulates.FunExt where

open import Axiom.Extensionality.Propositional public

-- we postulate functional extensionality at all universe levels.
postulate
  extensionality : ∀ {ℓ ι} → Extensionality ℓ ι
