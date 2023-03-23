module W where

open import Relation.Binary.PropositionalEquality
  hiding (subst)

open import Data.String using (String)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
  hiding (map)

open import Data.Nat

open import Data.List
  hiding (or ; lookup)
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

open import Data.Fin

--------------------------------------------------------------------------------
-- Implementation of Algorithm 𝒲, following Lee and Yi (1998) and Jones (1995).
-- Author: Alex Hubers <ahubers@uiowa.edu>
--
-- N.B. I do not believe Jones (1995) is available online, but Jones (1994) covers
-- Algorithm 𝒲 in a similar fashion, albeit flavored with qualified types.

--------------------------------------------------------------------------------
-- Variable Representation & substitution.
  
Var = ℕ
Vars = List Var

-- ixs : (n : ℕ) → List (Fin n)
-- ixs zero = []
-- ixs (suc n) = fromℕ n ∷ map inject₁ (ixs n)

-- flatten : Vars → List Var
-- flatten (n , f) = map f (ixs n)

-- sing : Var → Vars
-- sing v = 1 , λ { fzero → v }

new : Vars → Var
new = suc ∘ (max 0)

--------------------------------------------------------------------------------
-- Syntax

-- N.B.
--   - We omit recursive functions for simplicity.
--   - Algorithm 𝒲 (below) may be given nonsensical expressions and contexts.
--     We extend our type system with the bottom type ⊥, so that failures in 𝒲
--     are representable as
--         (λ _ → ⊥ , ⊥)
--     Further, we may represent "empty" substitutions and typing environments
--     as the constant functions mapping to ⊥. This technique is more or less
--     standard, e.g., Reynonds (2000).

data Expr : Set where
  ○    : Expr
  `    : (x : Var) → Expr
  ƛ    : (x : Var) → (e : Expr) → Expr
  _·_  : (e₁ : Expr) → (e₂ : Expr) → Expr
  Let_:=_In_ : (x : Var) → (e₁ : Expr) → (e₂ : Expr) → Expr

data Type : Set where
  ●    : Type
  `    : (α : Var) → Type
  _`→_ : (τ₁ : Type) → (τ₂ : Type) → Type
  ⊥ : Type

data Scheme : Set where
  §  : (τ : Type) → Scheme
  `∀ : (T : Vars) → (τ : Type) → Scheme
  
--------------------------------------------------------------------------------
-- Typing Environments.

TypeEnv : Set
TypeEnv =  Var → Scheme

ε : TypeEnv
ε = λ _ → ⊥


sing : Var → Scheme
sing target source = ⊥

extend : TypeEnv → Var → Scheme → TypeEnv
extend Γ v σ = (λ x → {!!}) ∘ Γ

--------------------------------------------------------------------------------
-- Substitution.

Subst  : Set
Subst = Var → Type

subst : Subst → Scheme → Scheme
subst't : Subst → Type → Type

subst ρ (§ τ)     = § (subst't ρ τ)
subst ρ (`∀ T τ) = `∀ T (subst't ρ τ)

subst't ρ ● = ●
subst't ρ (` x) = (ρ x)
subst't ρ (τ `→ τ') = subst't ρ τ `→ subst't ρ τ'


--------------------------------------------------------------------------------
-- Freshening, i.e.,
--  freshen (∀αᵢ.τ) := [βᵢ/αᵢ]τ
-- with βᵢ each fresh.

freshen : Scheme → Type
freshen't : Vars → Type → Type

freshen (§ τ) = τ
freshen (`∀ T τ) = freshen't T τ
freshen ⊥ = ⊥

freshen't _ ● = ●
freshen't T (` α) = ` (new (α ∷ T))
freshen't T (τ₁ `→ τ₂) = freshen't T τ₁ `→ freshen't T τ₂



--------------------------------------------------------------------------------
-- Generalization, a là Jones (1995) and Damas and Milner (1982).
--

gen : TypeEnv → Type → Scheme
gen = {!!}

--------------------------------------------------------------------------------
-- Algorithm 𝒲.

idS : Subst
idS = λ x → ` x

-- This is a nuisance.
-- Let's just postulate freshness + the annoying bits and leave all contexts as functions.
𝒲 : TypeEnv → Expr → Subst × Type
𝒲 Γ ○ =  (idS , ●)
𝒲 Γ (` x) =  (idS , freshen (Γ x))
𝒲 Γ (ƛ x e) = {!let (S₁, τ₁) = 𝒲 ((x , ?) ∷ Γ , e) in ?!}
𝒲 Γ (e₁ · e₂) = {!!}
𝒲 Γ (Let x := e₁ In e₂) = {!!}
-- 𝒲 Γ (` x) with x ∈? (dom Γ)
-- ... | yes p = succeed {! lookup p!}
-- ... | no  p = fail
-- -- 𝒲 Γ (` x) with lookup Γ ?
-- -- ... | § τ = succeed (id , τ)
-- -- ... | `∀ T τ = succeed (id , (subst't ? τ))
-- -- 𝒲 Γ (ƛ x e) =
-- --   let
-- --     (S₁ , τ₁) = 𝒲 (Γ , e)
-- --     β = ?
-- --   in succeed ({!!} , {!!})
-- -- 𝒲 Γ (e · e₁) = {!!}
-- -- 𝒲 Γ (Let x := e In e₁) = {!!}
