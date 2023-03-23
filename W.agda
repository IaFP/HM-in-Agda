module W where

open import Relation.Binary.PropositionalEquality
  hiding (subst)

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
import AssocList ℕ _≟_  as AL
open AL

--------------------------------------------------------------------------------
-- Implementation of Algorithm 𝒲, following Lee and Yi (1998) and Jones (1995).
-- Author: Alex Hubers <ahubers@uiowa.edu>
--
-- N.B. I do not believe Jones (1995) is available online, but Jones (1994) covers
-- Algorithm 𝒲 in a similar fashion, albeit flavored with qualified types.

--------------------------------------------------------------------------------
-- Variable Representation & substitution.
--
-- N.B.
--  - We use a named representation of variables -- even if they are naturals.
--    So this is *not* DeBruijn. For example, the lambda term
--        λ 3. λ 4. 3 4
--    is α-equivalent to
--        λ x. λ y. x y.
--    This makes implementation easiest, but likely would need to be changed
--    to either DeBruijn or Locally Nameless (see Charguéraud 2012). I personally
--    would recommend locally nameless, as make use of the decidable equality and
--    freshness of the naturals.

Var = ℕ
Vars = List Var

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
  tt    : Expr
  `    : (x : Var) → Expr
  ƛ    : (x : Var) → (e : Expr) → Expr
  _·_  : (e₁ : Expr) → (e₂ : Expr) → Expr
  Let_:=_In_ : (x : Var) → (e₁ : Expr) → (e₂ : Expr) → Expr

data Type : Set where
  ⊤    : Type
  `    : (α : Var) → Type
  _`→_ : (τ₁ : Type) → (τ₂ : Type) → Type
  ⊥ : Type

data Scheme : Set where
  §  : (τ : Type) → Scheme
  `∀ : (T : Vars) → (τ : Type) → Scheme

--------------------------------------------------------------------------------
-- Typing Environments.
--

TypeEnv : Set
TypeEnv = AssocList Scheme

--------------------------------------------------------------------------------
-- Substitutions.

Subst : Set
Subst = AssocList Type

--------------------------------------------------------------------------------
-- Free type variables in types, schemes, and environments.

_╲_ : List Var → List Var → List Var
xs ╲ ys = filter (_∈? ys) xs

ftv : Scheme → Vars
ftv't : Type → Vars

ftv (§ τ) = ftv't τ
ftv (`∀ T τ) = ftv't τ ╲ T

ftv't ⊤ = []
ftv't (` α) = α ∷ []
ftv't (τ₁ `→ τ₂) = ftv't τ₁ ++ ftv't τ₂
ftv't ⊥ = []

ftv'Γ : TypeEnv → Vars
ftv'Γ ε = []
ftv'Γ (α ⦂ σ , Γ) = ftv σ ++ (ftv'Γ Γ)
--------------------------------------------------------------------------------
-- Freshening, i.e.,
--   freshen Γ (∀αᵢ.τ) := [βᵢ/αᵢ]τ
-- with βᵢ fresh in αᵢ ∪ dom Γ for i ≥ 0.

-- Produce fresh β from vars αᵢ.
fresh : Vars → Var
fresh = suc ∘ (max 0)

-- Produce the substitution [βᵢ/αᵢ] fresh βᵢ from vars αᵢ.
freshen : Vars → Subst
freshen as = go as as
  where
    -- "all" accumulates each fresh var we add,
    -- so that we do not produce duplicates.
    go : Vars → Vars → Subst
    go [] all = ε
    go (x ∷ xs) all = let β = fresh all in x ⦂ ` β , (go xs (β ∷ all))
new : TypeEnv → Type
new Γ = ` (fresh (dom Γ))

--------------------------------------------------------------------------------
-- Substitution.

subst : Subst → Scheme → Scheme
subst't : Subst → Type → Type

subst S (§ τ)     = § (subst't S τ)
subst S (`∀ T τ) = `∀ T (subst't S τ)

subst't S ⊤ = ⊤
subst't S ⊥ = ⊥
subst't S (` x) = S ∋[ x ] ⊥
subst't S (τ `→ τ') = subst't S τ `→ subst't S τ'

-- compose : Subst → Subst → Subst

-- --------------------------------------------------------------------------------
-- Substitution over typing environments.

subst'Γ : Subst → TypeEnv → TypeEnv
subst'Γ S Γ = AL.map (subst S) Γ

-- --------------------------------------------------------------------------------
-- Generalization, a là Jones (1995) and Damas and Milner (1982).

gen : TypeEnv → Type → Scheme
gen Γ τ = `∀ ((ftv't τ) ╲ ftv'Γ Γ) τ

-- --------------------------------------------------------------------------------
-- -- Unification (𝒰).

𝒰 : Type → Type → Subst
𝒰 τ₁ τ₂ = {!!}

-- --------------------------------------------------------------------------------
-- -- Algorithm 𝒲.

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
    S₃        = 𝒰 {!!} {!!}
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
