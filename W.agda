{-# OPTIONS --allow-unsolved-metas #-}
module W where


open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
  hiding (map)

open import Data.String using (String)
open import Data.Nat
open import Data.List
  hiding (or ; lookup ; _─_)
open import Data.List.Extrema.Nat
open import Data.List.Relation.Unary.Any
  hiding (map)
import Data.List.Membership.DecPropositional as Membership
open Membership _≟_

open import Data.Product
  renaming (proj₁ to fst ; proj₂ to snd)
  hiding (map)
  
open import Data.Sum
  renaming (_⊎_ to _or_ ; inj₁ to left ; inj₂ to right)
  hiding (map)

open import Function

-- mine
open import AssocList ℕ _≟_  as AL
open import Syntax
open import Unification

--------------------------------------------------------------------------------
-- Implementation of Algorithm 𝒲, following Lee and Yi (1998) and Jones (1995).
-- Author: Alex Hubers <ahubers@uiowa.edu>

idS : Subst
idS = ε

𝒲 : TypeEnv → Expr → Subst × Type
𝒲 Γ tt =  (idS , ⊤)
𝒲 Γ (` x) with (Γ ∋[ x ] (§ ⊥))
... | § τ    = idS , τ
... | σ@(`∀ T τ) = idS , subst't (freshen (T ++ dom Γ)) τ
𝒲 Γ (ƛ x e) = let
                 β = new Γ
                 (S₁ , τ₁) = 𝒲 (x ⦂ § β , Γ) e
               in S₁ , (subst't S₁ β) `→ τ₁ 
𝒲 Γ (e₁ · e₂) =
  let
    β = new Γ
    (S₁ , τ₁) = 𝒲 Γ e₁
    (S₂ , τ₂) = 𝒲 (subst'Γ S₁ Γ) e₂
    S₃        = 𝒰 (subst't S₂ τ₁) (τ₂ `→ β)
  in S₃ ∘' (S₂ ∘' S₁) , subst't S₃ β
𝒲 Γ (Let x := e₁ In e₂) =
  let
    (S₁ , τ₁) = 𝒲 Γ e₁
    (S₂ , τ₂) = 𝒲 (x ⦂ (gen Γ τ₁ ) , subst'Γ S₁ Γ) e₂
  in (S₂ ∘' S₁) , τ₂

--------------------------------------------------------------------------------
-- Printing.

print : Type → String
print τ = printi τ 0
  where
    chars = "a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ []
    printi : Type → ℕ → String
    printi τ n = {!!}
