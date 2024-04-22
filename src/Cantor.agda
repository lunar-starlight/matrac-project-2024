{-# OPTIONS --allow-unsolved-metas --rewriting #-}
module Cantor where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
  using (≡-decSetoid) renaming (_≟_ to _≡?_)
open import Data.Bool
open import Data.Product
open import Data.List
  using (List; []; _∷_; _++_)

open import Function
  using (id; _∘_)

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality as PE
  using (cong; trans; sym; inspect)
--open import Agda.Builtin.Sigma
--  using (Σ)

open import Relation.Nullary.Decidable
  using (Dec; _because_; ¬?; yes; no) renaming (map to decmap)
open import Relation.Nullary.Negation
  using (¬_)
open import Data.List.Relation.Unary.Any
  using (Any; index; map; here; there; any?)
open import Relation.Binary
  using (DecSetoid; Decidable; IsDecEquivalence; Rel)

-- Any decidable setoid may be tagged
module Membership {c ℓ} (S : DecSetoid c ℓ) (T : Set) where
  open DecSetoid S renaming (Carrier to A)
  open IsDecEquivalence isDecEquivalence renaming (_≟_ to _≈?_)
  infix 4 _∈'_ _∉'_ _∈'?_ _∉'?_

  _≈'_ : A → A × T → Set _
  x ≈' (y , _) = x ≈ y

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
  add : (n : ℕ) → (b : Bool) → (l : Carrier) → cond? l → (n ∉' l) → cond? ((n , b) ∷ l)

record Cond : Set where
  constructor cond
  field
    carrier : Carrier
    is-cond : cond? carrier
open Cond

infix 4 _∈_ _∉_ _∈?_ _∉?_

‖_‖ : Cond → Carrier
‖ p ‖ = carrier p

_∈_ : ℕ → Cond → Set _
n ∈ p = n ∈' ‖ p ‖

_∉_ : ℕ → Cond → Set _
n ∉ p = ¬ n ∈ p

_∈?_ : Decidable _∈_
n ∈? p = n ∈'? ‖ p ‖

_∉?_ : Decidable _∉_
n ∉? p = ¬? (n ∈? p)

add-cond : (n : ℕ) → (b : Bool) → (p : Cond) → (n ∉ p) → Cond
add-cond n b p α = record
    { carrier = (n , b) ∷ ‖ p ‖
    ; is-cond = add n b (carrier p) (is-cond p) α }

lookup : (p : Cond) → (n : ℕ) → (n ∈ p) → Bool
lookup record { carrier = ((_ , b) ∷ _) ; is-cond = _ } _ (here refl) = b
lookup record { carrier = _ ; is-cond = (add _ _ xs p _) } n (there α) = lookup (cond xs p) n α

cond-matching : (p q : Cond) → Set
cond-matching p q = (n : ℕ) → (α : n ∈ p) → (β : n ∈ q) → lookup p n α ≡ lookup q n β

cond-union : (p q : Cond) → (α : cond-matching p q) → Cond
cond-union p q α =
  record { carrier = union-carrier ‖ p ‖ ‖ q ‖
         ; is-cond = union-is-cond p q α}
  where
    open import Relation.Nullary.Reflects
    union-carrier : (‖p‖ ‖q‖ : Carrier) → Carrier
    union-carrier []        ‖q‖ = ‖q‖
    union-carrier (x ∷ ‖p‖) ‖q‖ with (proj₁ x) ∈'? ‖q‖
    ... | no  _ = x ∷ union-carrier ‖p‖ ‖q‖
    ... | yes _ =     union-carrier ‖p‖ ‖q‖

    --union-carrier ‖p‖ [] = ‖p‖
    --union-carrier ‖p‖ (y ∷ ‖q‖) with (proj₁ y) ∈'? ‖p‖
    --... | false because _ = y ∷ union-carrier ‖p‖ ‖q‖
    --... | true  because _ =     union-carrier ‖p‖ ‖q‖

    ∉-union-carrier : {n : ℕ} → {‖p‖ ‖q‖ : Carrier} → (n ∉' ‖p‖) → (n ∉' ‖q‖) → n ∉' union-carrier ‖p‖ ‖q‖
    ∉-union-carrier {n} {[]}             {‖q‖} n∉[] n∉q = n∉q
    ∉-union-carrier {n} { (m , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q n∈∪         with m ∈'? ‖q‖
    ∉-union-carrier {n} {.(n , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q (here refl) | no  _ = n∉sp (here refl)
    ∉-union-carrier {n} { (m , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q (there n∈∪) | no  _ = ∉-union-carrier (λ n∈p → n∉sp (there n∈p)) n∉q n∈∪
    ∉-union-carrier {n} { (m , _) ∷ ‖p‖} {‖q‖} n∉sp n∉q n∈∪         | yes _ = ∉-union-carrier (λ n∈p → n∉sp (there n∈p)) n∉q n∈∪

    union-is-cond' : (‖p‖ : Carrier) → (cond?p : cond? ‖p‖) → (q : Cond)
                   → (α : cond-matching (cond ‖p‖ cond?p) q) → cond? (union-carrier ‖p‖ ‖ q ‖)
    union-is-cond' [] nil q α = is-cond q
    union-is-cond' ((n , b) ∷ ‖p‖) (add .n .b .‖p‖ cond?p n∉p) q α with n ∈? q
    ... | yes _  = union-is-cond' ‖p‖ cond?p q (λ m γ δ → α m (there γ) δ)
    ... | no n∉q = add n b
                       (union-carrier ‖p‖ (carrier q))
                       (union-is-cond' ‖p‖ cond?p q (λ m γ δ → α m (there γ) δ))
                       (∉-union-carrier n∉p n∉q)

    union-is-cond : (p q : Cond) → (α : cond-matching p q) → cond? (union-carrier ‖ p ‖ ‖ q ‖)
    union-is-cond p = union-is-cond' ‖ p ‖ (is-cond p)

syntax cond-union p q α = p ∪[ α ] q

data Part : (p : Cond) → Set where
  whole : (p : Cond) → Part p
  split : (p : Cond) → (n : ℕ) → (n∉p : n ∉ p)
        → Part (add-cond n false p n∉p)
        → Part (add-cond n true  p n∉p)
        → Part p

_≼_ : Rel Cond Agda.Primitive.lzero
q ≼ p = (n : ℕ) → (n∈p : n ∈ p) → Σ[ n∈q ∈ (n ∈ q)] lookup p n n∈p ≡ lookup q n n∈q

∈-prop : (p : Cond) → {n : ℕ} → (α β : n ∈ p) → α ≡ β
∈-prop _ (here refl) (here refl) = refl
∈-prop (cond _ (add _ _ _ _ n∉p)) (here refl) (there β)
  = ⊥-elim (n∉p β)
∈-prop (cond _ (add _ _ _ _ n∉p)) (there α) (here refl)
  = ⊥-elim (n∉p α)
∈-prop (cond (_ ∷ xs) (add _ _ .xs cond?xs _)) (there α) (there β)
  = cong there (∈-prop (cond xs cond?xs) α β)

open import Agda.Builtin.Equality.Rewrite
{- REWRITE ∈-prop -}

≼∈ : {p q : Cond} → (q≼p : q ≼ p) → {n : ℕ} → n ∈ p → n ∈ q
≼∈ q≼p {n} n∈p = proj₁ (q≼p n n∈p)

lookup-irrelevance : {p : Cond} → {n : ℕ} → (α β : n ∈ p) → lookup p n α ≡ lookup p n β
lookup-irrelevance {p} {n} α β = cong (lookup p n) (∈-prop p α β)

≼-matching : {p q : Cond} → q ≼ p → cond-matching p q
≼-matching {p} {q} q≼p n n∈p n∈q = begin
  lookup p n n∈p
    ≡⟨ proj₂ (q≼p n n∈p) ⟩
  lookup q n (proj₁ (q≼p n n∈p))
    ≡⟨ lookup-irrelevance (proj₁ (q≼p n n∈p)) n∈q ⟩
  lookup q n n∈q ∎
  where open PE.≡-Reasoning

≼-preserves-lookup : {p q : Cond} → (q≼p : q ≼ p) → {n : ℕ} → (n∈p : n ∈ p)
                   → lookup p n n∈p ≡ lookup q n (≼∈ q≼p n∈p)
≼-preserves-lookup {p} {q} q≼p {n} n∈p = begin
  lookup p n n∈p ≡⟨ proj₂ (q≼p n n∈p) ⟩
  lookup q n (proj₁ (q≼p n n∈p))
    ≡⟨ lookup-irrelevance (proj₁ (q≼p n n∈p)) (≼∈ q≼p n∈p) ⟩
  lookup q n (≼∈ q≼p n∈p) ∎
  where open PE.≡-Reasoning

add-cond-preserves-≼ : {p q : Cond} → {n : ℕ} → {b : Bool}
                     → {n∉p : n ∉ p} → {n∉q : n ∉ q}
                     → q ≼ p → add-cond n b q n∉q ≼ add-cond n b p n∉p
add-cond-preserves-≼ q≼p n (here refl) = here refl , refl
add-cond-preserves-≼ q≼p m (there m∈p) = there (≼∈ q≼p m∈p) , ≼-preserves-lookup q≼p m∈p

add-cond-preserves-≼' : {p q : Cond} → {n : ℕ} → {b : Bool}
                     → {n∉p : n ∉ p} → (n∈q : n ∈ q) → (lookup q n n∈q ≡ b)
                     → q ≼ p → q ≼ add-cond n b p n∉p
add-cond-preserves-≼' n∈q eq q≼p n (here refl) = n∈q , (sym eq)
add-cond-preserves-≼' n∈q eq q≼p m (there m∈p) = ≼∈ q≼p m∈p , ≼-preserves-lookup q≼p m∈p 

≼-trans : {p q r : Cond} → r ≼ q → q ≼ p → r ≼ p
≼-trans {p} {q} {r} r≼q q≼p n n∈p = n∈r , trans-lookup
  where
    n∈r : n ∈ r
    n∈r = proj₁ (r≼q n (proj₁ (q≼p n n∈p)))

    trans-lookup : lookup p n n∈p ≡ lookup r n n∈r
    trans-lookup =
      trans
        (proj₂ (q≼p n n∈p))
        (proj₂ (r≼q n (proj₁ (q≼p n n∈p))))

{-
data _≼_ : (p q : Cond) → Set where
  rfl : (p : Cond) → p ≼ p
  ext : (p : Cond) → (n : ℕ) → (b : Bool) → (q : Cond) → (n∉q : n ∉ q) → q ≼ p
      → add-cond n b q n∉q ≼ p

∈-prop : (p : Cond) → {n : ℕ} → (α β : n ∈ p) → α ≡ β
∈-prop _ (here refl) (here refl) = refl
∈-prop (cond _ (add _ _ _ _ n∉p)) (here refl) (there β)
  = ⊥-elim (n∉p β)
∈-prop (cond _ (add _ _ _ _ n∉p)) (there α) (here refl)
  = ⊥-elim (n∉p α)
∈-prop (cond (_ ∷ xs) (add _ _ .xs cond?xs _)) (there α) (there β)
  = cong there (∈-prop (cond xs cond?xs) α β)

≼∈ : {p q : Cond} → (q≼p : q ≼ p) → {n : ℕ} → n ∈ p → n ∈ q
≼∈ (rfl _) n∈p = n∈p
≼∈ (ext _ _ _ _ _ q≼p) n∈p = there (≼∈ q≼p n∈p)

≼-matching : {p q : Cond} → q ≼ p → cond-matching p q
≼-matching {p} {.p} (rfl .p) = λ n α β → cong (λ γ → lookup p n γ) (∈-prop p α β)
≼-matching (ext _ n _ _ n∉q q≼p) m α β with m ≡? n
...                                          | yes refl = ⊥-elim (n∉q (≼∈ q≼p α))
≼-matching _ _ α (here refl)                 | no ¬⊤ = ⊥-elim (¬⊤ refl)
≼-matching (ext _ _ _ _ _ q≼p) m α (there β) | no _ rewrite ≼-matching q≼p m α β = refl

≼-preserves-lookup : {p q : Cond} → (q≼p : q ≼ p) → (n : ℕ) → (n∈p : n ∈ p)
                   → lookup p n n∈p ≡ lookup q n (≼∈ q≼p n∈p)
≼-preserves-lookup (rfl _) n n∈p = refl
≼-preserves-lookup (ext _ m b q m∉q q≼p) n (here refl)
  with ≼∈ q≼p (here refl)
... | here refl = ≼-matching q≼p n (here refl) (here refl)
... | there n∈q rewrite ≼-matching q≼p n (here refl) (there n∈q) = refl
≼-preserves-lookup (ext _ m b q m∉q q≼p) n (there n∈p)
  = ≼-preserves-lookup q≼p n (there n∈p)

add-cond-preserves-≼ : {p q : Cond} → {n : ℕ} → {b : Bool}
                     → {n∉p : n ∉ p} → {n∉q : n ∉ q}
                     → q ≼ p → add-cond n b q n∉q ≼ add-cond n b p n∉p
add-cond-preserves-≼ (rfl _) = rfl _
add-cond-preserves-≼ (ext _ n b q n∉q q≼p) = {!!}

add-cond-preserves-≼' : {p q : Cond} → {n : ℕ} → {b : Bool}
                     → {n∉p : n ∉ p} → (n∈q : n ∈ q) → (lookup q n n∈q ≡ b)
                     → q ≼ p → q ≼ add-cond n b p n∉p
add-cond-preserves-≼' n∈q eq q≼p = {!!}
-}

part-size : {p : Cond} → Part p → ℕ
part-size (whole _) = 1
part-size (split _ n n∉p I₀ I₁) = part-size I₀ + part-size I₁

part-list : {p : Cond} → Part p → List Cond
part-list (whole p) = p ∷ []
part-list (split _ _ _ I₀ I₁) = part-list I₀ ++ part-list I₁ 

part-res : {p : Cond} (q : Cond) → (I : Part p) → q ≼ p → Part q
part-res q (whole _) q≼p = whole q
part-res q (split _ n n∉p I₀ I₁) q≼p with n ∈? q
... | no n∉q = split q n n∉q
                 (part-res (add-cond n false q n∉q) I₀ (add-cond-preserves-≼ q≼p))
                 (part-res (add-cond n true  q n∉q) I₁ (add-cond-preserves-≼ q≼p))
... | yes n∈q with lookup q n n∈q | inspect (lookup q n) n∈q
...           | false | PE.[ eq ] = part-res q I₀ (add-cond-preserves-≼' n∈q eq q≼p)
...           | true  | PE.[ eq ] = part-res q I₁ (add-cond-preserves-≼' n∈q eq q≼p)
