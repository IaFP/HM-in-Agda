module Print where

--------------------------------------------------------------------------------
-- Pretty Printing of terms.
open import Function

open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.List hiding (_++_)

open import Syntax

print : Scheme → String
print't : Type → String
print (§ τ) = print't τ
print (`∀ T τ) = "∀ {" ++ fromList (intercalate (toList ",") (map (toList ∘ show) T)) ++ "} " ++ print't τ 

print't ⊤ = "⊤"
print't (` α) = show α
print't (τ `→ τ') = print't τ ++ " → " ++ print't τ' 
print't ⊥ = "⊥"
