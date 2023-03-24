module Examples where


open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.List hiding (_++_)
open import Data.Nat as N
open import Data.Product using (_,_)

open import Syntax
open import AssocList ℕ N._≟_ as AL
open import Unification
open import W
open import Print

--------------------------------------------------------------------------------
--

id : Expr
id = `λ 0 (` 0)

hmm =
  let
    (S , τ) = 𝒲 ε id
  in gen (subst'Γ S ε) τ

pfft = print hmm
--------------------------------------------------------------------------------


