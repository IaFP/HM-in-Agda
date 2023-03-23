open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Data.List hiding (map)
open import Data.Bool using (true ; false ; Bool)

module AssocList (Key : Set) (_≟_ : Decidable {A = Key} _≡_) where

--------------------------------------------------------------------------------
-- Associated lists for typing environments, assignments, and substitutions.

data AssocList (Val : Set)  : Set where
  ε     : AssocList Val
  _⦂_,_ : (k : Key) → (v : Val) → (xs : AssocList Val) → AssocList Val

[_⦂_]  : ∀ {Val : Set} → Key → Val → AssocList Val
[ v ⦂ σ ] = v ⦂ σ , ε
--------------------------------------------------------------------------------
-- Membership.

_In_ : ∀ {Val : Set} →
         Key → AssocList Val → Bool
v In ε = false
x In (y ⦂ σ , Γ) with x ≟ y
... | yes _ = true
... | no _ =  false

--------------------------------------------------------------------------------
-- Lookup.

_∋[_]_ : ∀ {Val : Set} →
         AssocList Val → Key → Val → Val

ε ∋[ v ] ⊥ = ⊥
_∋[_]_ (x ⦂ σ , Γ) y ⊥ with x ≟ y
... | yes _ = σ
... | no _ =  Γ ∋[ y ] ⊥

--------------------------------------------------------------------------------
-- Domain.
dom : ∀ {Val : Set} → AssocList Val → List Key
dom ε = []
dom (v ⦂ _ , Γ) = v ∷ (dom Γ)

--------------------------------------------------------------------------------
-- Map from one Val to another.

map : ∀ {A B : Set} → (A → B) → AssocList A → AssocList B
map f ε = ε
map f (k ⦂ v , xs) = k ⦂ (f v) , (map f xs)
--------------------------------------------------------------------------------
-- "Composition" of assoc lists -- i.e., merge, with precedence given to left.
-- (Named "composition" to align with the use case: composition of
-- substitutions.)

_∘'_ : ∀ {Val : Set} → AssocList Val  → AssocList Val → AssocList Val
xs ∘' ε = xs
xs ∘' (k ⦂ v , ys) with k In xs
... | false = (k ⦂ v , xs) ∘' ys
... | true = xs ∘' ys
