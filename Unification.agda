{-# OPTIONS --allow-unsolved-metas #-}
module Unification where

open import Data.Nat
open import AssocList ℕ _≟_ as AL
open import Syntax

open import Data.Maybe
  -- renaming (_⊎_ to _or_ ; inj₁ to left ; inj₂ to right)
  -- hiding (map)


--------------------------------------------------------------------------------
-- Unification (𝒰).
--
-- N.B.
--   - I am encoding failure as the substitution
--         0 : ⊥ , ε.
--     This saves me the hassle of working within the Maybe monad.

failure : Subst
failure = 0 ⦂ ⊥ , ε

𝒰 : Type → Type → Subst
𝒰 ⊤ ⊤ = ε
𝒰 ⊤ (` α) = (α ⦂ ⊤ , ε)
𝒰 ⊤ _ = failure
𝒰 (` α) ⊤ = (α ⦂ ⊤ , ε)
𝒰 (` α) (` β) = {!!}
𝒰 (` α) (τ₁ `→ τ₂) = {!!}
𝒰 (` α) ⊥ = failure
𝒰 (τ₁ `→ τ₂) (` α) = {!!}
𝒰 (τ₁ `→ τ₂) (τ₃ `→ τ₄) = {!!}
𝒰 (τ₁ `→ τ₂) _ = failure
𝒰 ⊥ _ = failure
