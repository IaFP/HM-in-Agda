module Print where

--------------------------------------------------------------------------------
-- Pretty Printing of terms.
open import Function

open import Data.String hiding (show)
open import Data.Char hiding (show)
open import Data.Maybe hiding (map)
open import Data.Nat 
open import Data.Nat.Show 
open import Data.List hiding (_++_ ; intersperse; lookup)

open import Syntax

lookup : ∀ {A : Set} → List A → ℕ → Maybe A
lookup [] _ = nothing
lookup (x ∷ xs) zero = just x
lookup (x ∷ xs) (suc n) = lookup xs n

chars = "a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ "f" ∷ "g" ∷ "h" ∷ "i" ∷ "j" ∷ "k" ∷ "l" ∷ "m" ∷ "n" ∷ [] 
name : Var → String
name α with lookup chars α
... | just n = n
... | nothing = "pfft"

print : Scheme → String
print't : Type → String
print (§ τ) = print't τ
print (`∀ T τ) = "∀ {" ++ (intersperse "," (map name T)) ++ "} " ++ print't τ


print't ⊤ = "⊤"
print't (` α) = name α
print't (τ `→ τ') = "(" ++ print't τ ++ " → " ++ print't τ' ++ ")"
