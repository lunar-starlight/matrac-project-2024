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

open import Function
  using (id; _∘_)

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
  using (Σ)

--open DecSetoid ≡-decSetoid

open import Relation.Nullary.Decidable
  using (Dec; _because_; T?; ¬?) renaming (map to decmap)
open import Relation.Nullary.Negation
  using (¬_)
open import Data.List.Relation.Unary.Any
  using (Any; index; map; here; there; any?)
open import Relation.Binary
  using (DecSetoid; Decidable; IsDecEquivalence)

module Membership {c ℓ} (S : DecSetoid c ℓ) (T : Set) where
  open DecSetoid S renaming (Carrier to A)
  open IsDecEquivalence isDecEquivalence renaming (_≟_ to _≈?_)
  infix 4 _∈'_ _∉'_ _∈'?_ _∉'?_

  _≈'_ : A → A × T → Set _
  _≈'_ x = λ { (y , _) →  x ≈ y}

  open import Function.Bundles using (_⇔_)
  ≈⇔≈' : {t : T} → (x y : A) → (x ≈ y) ⇔ (x ≈' (y , t))
  ≈⇔≈' {_} _ _ = record { to = id ; from = id ; to-cong = id ; from-cong = id }

  _≈'?_ : Decidable _≈'_
  x ≈'? (y , t) = decmap (≈⇔≈' {t} x y) (x ≈? y)

  _∈'_ : A → List (A × T) → Set _
  x ∈' xs = Any (x ≈'_) xs

  _∉'_ : A → List (A × T) → Set _
  x ∉' xs = ¬ x ∈' xs

  _∈'?_ : Decidable _∈'_
  x ∈'? xs = any? (x ≈'?_) xs

  _∉'?_ : Decidable _∉'_
  x ∉'? xs = ¬? (x ∈'? xs)
open Membership ≡-decSetoid Bool public

Carrier : Set
Carrier = List (ℕ × Bool)

data cond? : Carrier → Set where
  nil : cond? []
  add : (n : ℕ) → (b : Bool) → (l : Carrier) → (n ∉' l) → cond? l → cond? ((n , b) ∷ l)

record Cond : Set where
  constructor cond
  field
    carrier : Carrier
    is-cond : cond? carrier
open Cond

infix 4 _∈_ _∉_ _∈?_ _∉?_

_∈_ : ℕ → Cond → Set _
n ∈ p = n ∈' carrier p

_∉_ : ℕ → Cond → Set _
n ∉ p = ¬ n ∈ p

_∈?_ : Decidable _∈_
n ∈? p = n ∈'? carrier p

_∉?_ : Decidable _∉_
n ∉? p = ¬? (n ∈? p)

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

cond-union : (p' q' : Cond) → (α' : cond-matching p' q') → Cond
cond-union p' q' α' =
  record { carrier = union-carrier ‖ p' ‖ ‖ q' ‖
         ; is-cond = union-is-cond p' q' α'}
  where
    open import Relation.Nullary.Reflects
    union-carrier : (‖p‖ ‖q‖ : List (ℕ × Bool)) → List (ℕ × Bool)
    union-carrier [] ‖q‖ = ‖q‖
    union-carrier (x ∷ ‖p‖) ‖q‖ with proj₁ x ∈'? ‖q‖
    ... | false because _ = x ∷ union-carrier ‖p‖ ‖q‖
    ... | true  because _ =     union-carrier ‖p‖ ‖q‖ 

    --union-carrier ‖p‖ [] = ‖p‖
    --union-carrier ‖p‖ (y ∷ ‖q‖) with (proj₁ y) ∈'? ‖p‖
    --... | false because _ = y ∷ union-carrier ‖p‖ ‖q‖
    --... | true  because _ =     union-carrier ‖p‖ ‖q‖

    ∉-union-carrier : {n : ℕ} → {‖p‖ ‖q‖ : Carrier} → (n ∉' ‖p‖) → (n ∉' ‖q‖) → n ∉' union-carrier ‖p‖ ‖q‖
    ∉-union-carrier {n} {[]}             {‖q‖} n∉[] n∉q = n∉q
    ∉-union-carrier {n} { (m , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q n∈∪         with m ∈'? ‖q‖
    ∉-union-carrier {n} {.(n , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q (here refl) | false because _ = n∉sp (here refl)
    ∉-union-carrier {n} { (m , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q (there n∈∪) | false because _ = ∉-union-carrier (λ n∈p → n∉sp (there n∈p)) n∉q n∈∪
    ∉-union-carrier {n} { (m , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q n∈∪         | true  because _ = ∉-union-carrier (λ n∈p → n∉sp (there n∈p)) n∉q n∈∪

    union-is-cond' : (‖p‖ : Carrier) → (cond?p : cond? ‖p‖) → (q : Cond)
                   → (α : cond-matching (cond ‖p‖ cond?p) q) → cond? (union-carrier ‖p‖ ‖ q ‖)
    union-is-cond' [] nil q α = is-cond q
    union-is-cond' (.(n , b) ∷ ‖p‖) (add n b .‖p‖ n∉p cond?p) q α with n ∈? q
    ... | true  because _       = union-is-cond' ‖p‖ cond?p q (λ m γ δ → α m (there γ) δ)
    ... | false because ofⁿ n∉q = add n b
                                      (union-carrier ‖p‖ (carrier q))
                                      (∉-union-carrier n∉p n∉q)
                                      (union-is-cond' ‖p‖ cond?p q (λ m γ δ → α m (there γ) δ))

    union-is-cond : (p q : Cond) → (α : cond-matching p q) → cond? (union-carrier ‖ p ‖ ‖ q ‖)
    union-is-cond p = union-is-cond' ‖ p ‖ (is-cond p)
