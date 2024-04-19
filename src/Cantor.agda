{-# OPTIONS --type-in-type #-}
module Cantor where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
  using (≡-decSetoid)
open import Data.Bool
open import Data.Product
open import Data.List
  using (List; []; _∷_)
open import Relation.Nullary.Negation using (¬_)

open import Relation.Binary.Bundles using (DecSetoid)



--open import Data.List.Membership.DecSetoid
--  using (_∈_; _∉_)

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
  using (Σ)

--open DecSetoid ≡-decSetoid

open import Relation.Nullary.Decidable
  using (_because_; T?)
open import Data.List.Relation.Unary.Any
  using (Any; index; map; here; there; any?)
open import Relation.Binary.Definitions
  using (Decidable)
open import Relation.Binary.Structures
  using (IsDecEquivalence)

module Membership {c ℓ} (S : DecSetoid c ℓ) (T : Set) where
  open DecSetoid S renaming (Carrier to A)
  open IsDecEquivalence isDecEquivalence renaming (_≟_ to _≈?_)
  infix 4 _∈'_ _∉'_

  _≈'_ : {!IsDecEquivalence !}
  _≈'_ x = {!!}

  _∈'_ : A → List (A × T) → Set _
  x ∈' xs = Any (λ { (y , _) →  x ≈ y}) xs

  _∉'_ : A → List (A × T) → Set _
  x ∉' xs = ¬ x ∈' xs

  _∈'?_ : Decidable _∈'_
  n ∈'? l = any? (λ { (m , _) → {!_≈_!}}) l

open Membership ≡-decSetoid Bool public

data cond? : List (ℕ × Bool) → Set where
  nil : cond? []
  add : (n : ℕ) → (b : Bool) → (l : List (ℕ × Bool)) → (n ∉' l) → cond? l → cond? ((n , b) ∷ l)

record Cond : Set where
  field
    carrier : List (ℕ × Bool)
    is-cond : cond? carrier

open Cond


infix 4 _∈_ _∉_

_∈_ : ℕ → Cond → Set _
n ∈ l = n ∈' carrier l

_∉_ : ℕ → Cond → Set _
x ∉ xs = ¬ x ∈ xs

_∈?_ : Decidable _∈_
n ∈? l = n ∈'? carrier l

‖_‖ : Cond → List (ℕ × Bool)
‖ p ‖ = carrier p

_,_∷_&_ : (n : ℕ) → (b : Bool) → (p : Cond) → (n ∉ p) → Cond
n , b ∷ p & α = record
    { carrier = (n , b) ∷ ‖ p ‖
    ; is-cond = add n b (carrier p) α (is-cond p) }

cond-lookup : (p : Cond) → (n : ℕ) → (n ∈ p) → Bool
cond-lookup record { carrier = (x ∷ _) ; is-cond = _ } .(proj₁ x) (here refl) = proj₂ x
cond-lookup record { carrier = (_ ∷ _) ; is-cond = (add _ _ xs _ p) } n (there α) = cond-lookup (record { carrier = xs ; is-cond = p }) n α

cond-matching : (p q : Cond) → Set
cond-matching p q = (n : ℕ) → (α : n ∈ p) → (β : n ∈ q) → cond-lookup p n α ≡ cond-lookup q n β

cond-union : (p q : Cond) → (α : cond-matching p q) → Cond
cond-union p q α =
  record { carrier = union-carrier ‖ p ‖ ‖ q ‖
         ; is-cond = union-is-cond }
  where
    union-carrier : (p q : List (ℕ × Bool)) → List (ℕ × Bool)
    union-carrier p [] = p
    union-carrier p (y ∷ q) with (proj₁ y) ∈? {!!}
    ... | a = {!!}
  
    union-is-cond : cond? (union-carrier ‖ p ‖ ‖ q ‖)
    union-is-cond = {!!}


