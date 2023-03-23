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

𝒰 : Type → Type → Subst → Maybe Subst
𝒰 ⊤ ⊤ S = just S
-- Don't think this is right ?
-- Also, need to check if α ∈ ftv x.
𝒰 (` α) x S = just (S ∘' [ α ⦂ x ])
𝒰 x (` α) S = just (S ∘' [ α ⦂ x ])
𝒰 (τ₁ `→ τ₂) (τ₃ `→ τ₄) S = {!!}
𝒰 _ _ _ = nothing
