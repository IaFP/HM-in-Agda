{-# OPTIONS --allow-unsolved-metas #-}
module Unification where

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Data.List.Membership.DecPropositional as Membership
open import Data.Nat

open import AssocList ℕ _≟_ as AL
open import Syntax

open import Data.Maybe
  -- renaming (_⊎_ to _or_ ; inj₁ to left ; inj₂ to right)
  -- hiding (map)


--------------------------------------------------------------------------------
-- Unification (𝒰).
--

{-# TERMINATING #-}
𝒰 : Type → Type → Maybe Subst
𝒰 (τ₁ `→ τ₂) (υ₁ `→ υ₂) with 𝒰 τ₁ υ₁
... | nothing = nothing
... | just S₁ with 𝒰 (subst't S₁ τ₂) (subst't S₁ υ₂)
...   | just S₂ = just (subst'S S₂ S₁)
...   | nothing = nothing
𝒰 ⊤ ⊤ = just ε
𝒰 (` α) τ@(` β) with α ≟ β
... | yes p = just ε
... | no p =  just [ α ↦ τ ]
-- Don't think this is right ?
-- Also, need to check if α ∈ ftv x.
𝒰 (` α) τ with occurs α τ
... | yes p = nothing
... | no p = just [ α ↦ τ ]
𝒰 _ _ = nothing
