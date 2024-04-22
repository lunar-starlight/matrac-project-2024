{-# OPTIONS --allow-unsolved-metas --rewriting #-}
module Syntax where

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.List
  using (List; []; _∷_)
open import Data.Product

open import Relation.Nullary.Decidable
  using (Dec; _because_; ¬?; yes; no) renaming (map to decmap)
open import Relation.Nullary.Negation
  using (¬_)
open import Data.List.Relation.Unary.Any
  using (Any; index; map; here; there; any?)
open import Relation.Binary
  using (Rel)
open import Relation.Binary.PropositionalEquality as PE
  using (cong; sym; inspect)

open import Cantor


data Ty : Set where
  N : Ty
  B : Ty
  _⇒_ : Ty → Ty → Ty

_≈_ : Rel Ty Agda.Primitive.lzero
N ≈ N = ⊤
B ≈ B = ⊤
(S ⇒ S') ≈ (T ⇒ T') = (S ≈ T) × (S' ≈ T')
_ ≈ _ = ⊥

Ctx : Set
Ctx = List Ty

infix 4 _c∈_ _⊢_

open import Agda.Builtin.Equality

_c∈_ : Ty → Ctx → Set
S c∈ Γ = Any (S ≡_) Γ

data _⊢_ : Ctx → Ty → Set where

  var : {S : Ty} {Γ : Ctx} -> (S c∈ Γ) -> (Γ ⊢ S)

  lam : {S T : Ty} {Γ : Ctx} -> (S ∷ Γ ⊢ T) -> (Γ ⊢ S ⇒ T)

  app : {S T : Ty} {Γ : Ctx} -> (Γ ⊢ S ⇒ T) -> (Γ ⊢ S) -> (Γ ⊢ T)

  zero : {Γ : Ctx} -> (Γ ⊢ N)

  succ : {Γ : Ctx} -> (Γ ⊢ N) -> (Γ ⊢ N)

  natrec : {S : Ty} {Γ : Ctx} -> (Γ ⊢ S) -> (Γ ⊢ N ⇒ (S ⇒ S)) -> (Γ ⊢ N ⇒ S)

  false : {Γ : Ctx} -> (Γ ⊢ B)

  true : {Γ : Ctx} -> (Γ ⊢ B)

  boolrec : {S : Ty} {Γ : Ctx} -> (Γ ⊢ S) -> (Γ ⊢ S) -> (Γ ⊢ B ⇒ S)

  generic : {Γ : Ctx} -> (Γ ⊢ N ⇒ B)

data ∑ {p : Cond} (T : Ty) (Γ : Ctx) : Part p → Set where
  triv : (Γ ⊢ T) → ∑ T Γ (whole p)
  glue : {n : ℕ} → {n∉p : n ∉ p}
       → {I₀ : Part (add-cond n false p n∉p)} → ∑ T Γ I₀
       → {I₁ : Part (add-cond n true  p n∉p)} → ∑ T Γ I₁
       → ∑ T Γ (split p n n∉p I₀ I₁)

_>>=_ : {p : Cond} {I : Part p} {S T : Ty} {Γ : Ctx}
      → ∑ S Γ I -> ((Γ ⊢ S) -> (Γ ⊢ T)) -> ∑ T Γ I
(triv t)     >>= f = triv (f t)
(glue ∑₀ ∑₁) >>= f = glue (∑₀ >>= f) (∑₁ >>= f)


canon-ℕ : {Γ : Ctx} -> (n : ℕ) -> (Γ ⊢ N)
canon-ℕ zero = zero
canon-ℕ (suc n) = succ (canon-ℕ n)

canon-Bool : {Γ : Ctx} -> (b : Bool) -> (Γ ⊢ B)
canon-Bool true = true
canon-Bool false = false

extend-renaming : {Γ Δ : Ctx}
  → ({S : Ty} → S c∈ Γ → S c∈ Δ)
  ------------------------------------------------------------------------
  → {S T : Ty} → S c∈ (T ∷ Γ) → S c∈ (T ∷ Δ)
extend-renaming ρ (here px) = here px
extend-renaming ρ (there x) = there (ρ x)
rename : {Γ Δ : Ctx}
  → ({S : Ty} → S c∈ Γ → S c∈ Δ)
  ------------------------------------------------------------------------
  → {S : Ty} → Γ ⊢ S → Δ ⊢ S
rename ρ (var x) = var (ρ x)
rename ρ (lam t) = lam (rename (extend-renaming ρ) t)
rename ρ (app t u) = app (rename ρ t) (rename ρ u)
rename ρ zero = zero
rename ρ (succ t) = succ (rename ρ t)
rename ρ (natrec t0 tS) = natrec (rename ρ t0) (rename ρ tS)
rename ρ false = false
rename ρ true = true
rename ρ (boolrec t0 t1) = boolrec (rename ρ t0) (rename ρ t1)
rename ρ generic = generic
extend-subst : {Γ Δ : Ctx}
  → ({S : Ty} → S c∈ Γ → Δ ⊢ S)
  ------------------------------------------------------------------------
  → {S T : Ty} → S c∈ (T ∷ Γ) → (T ∷ Δ) ⊢ S
extend-subst σ (here px) = var (here px)
extend-subst σ (there x) = rename there (σ x)
subst : {Γ Δ : Ctx}
  → ({S : Ty} → S c∈ Γ → Δ ⊢ S)
  ------------------------------------------------------------------------
  → {S : Ty} → Γ ⊢ S → Δ ⊢ S
subst σ (var x) = σ x
subst σ (lam t) = lam (subst (extend-subst σ) t)
subst σ (app t u) = app (subst σ t) (subst σ u)
subst σ zero = zero
subst σ (succ t) = succ (subst σ t)
subst σ (natrec t0 tS) = natrec (subst σ t0) (subst σ tS)
subst σ false = false
subst σ true = true
subst σ (boolrec t0 t1) = boolrec (subst σ t0) (subst σ t1)
subst σ generic = generic

infix 5 _[_]
_[_] : {Γ : Ctx} {S T : Ty}
  → (T ∷ Γ) ⊢ S
  → Γ ⊢ T
  ------------------------------------------------------------------------
  → Γ ⊢ S
_[_] {Γ} {T = T} t u = subst σ t
  where
    σ : {S : Ty} → S c∈ (T ∷ Γ) → Γ ⊢ S
    σ (here refl) = u
    σ (there x) = var x

data computation :
  {T : Ty} → {Γ : Ctx}
  → (p : Cond) → (Γ ⊢ T) → {I : Part p} → ∑ T Γ I → Set where

  app-step :
    {S T : Ty} {Γ : Ctx} {p : Cond} {t : Γ ⊢ S ⇒ T} {u : Γ ⊢ S} {I : Part p} {Σ : ∑ (S ⇒ T) Γ I}
    → computation p t Σ
    ------------------------------------------------------------------------
    → computation p (app t u) (Σ >>= λ ti → app ti u)

  app-lam :
    {S T : Ty} {Γ : Ctx} {p : Cond} {t : (S ∷ Γ) ⊢ T} {u : Γ ⊢ S}
    ------------------------------------------------------------------------
    → computation p (app (lam t) u) (triv (t [ u ]))

  boolrec-false :
    {S : Ty} {Γ : Ctx} {p : Cond} {t0 t1 : Γ ⊢ S}
    ------------------------------------------------------------------------
    → computation p (app (boolrec t0 t1) false) (triv t0)

  boolrec-true :
    {S : Ty} {Γ : Ctx} {p : Cond} {t0 t1 : Γ ⊢ S}
    ------------------------------------------------------------------------
    → computation p (app (boolrec t0 t1) true) (triv t1)

  boolrec-step :
    {S : Ty} {Γ : Ctx} {p : Cond} {t0 t1 : Γ ⊢ S} {t : Γ ⊢ B} {I : Part p} {Σ : ∑ B Γ I}
    → computation p t Σ
    ------------------------------------------------------------------------
    → computation p (app (boolrec t0 t1) t) (Σ >>= app (boolrec t0 t1))

  natrec-zero :
    {S : Ty} {Γ : Ctx} {p : Cond} {t0 : Γ ⊢ S} {tS : Γ ⊢ N ⇒ (S ⇒ S)}
    ------------------------------------------------------------------------
    → computation p (app (natrec t0 tS) zero) (triv t0)

  natrec-succ :
    {S : Ty} {Γ : Ctx} {p : Cond} {t0 : Γ ⊢ S} {t : Γ ⊢ N} {tS : Γ ⊢ N ⇒ (S ⇒ S)}
    ------------------------------------------------------------------------
    → computation p
        (app (natrec t0 tS) (succ t))
        (triv (app (app tS t) (app (natrec t0 tS) t)))

  natrec-step :
    {S : Ty} {Γ : Ctx} {p : Cond} {t0 : Γ ⊢ S} {t : Γ ⊢ N} {tS : Γ ⊢ N ⇒ (S ⇒ S)}
    {I : Part p} {Σ : ∑ N Γ I}
    → computation p t Σ
    ------------------------------------------------------------------------
    → computation p (app (natrec t0 tS) t) (Σ >>= app (natrec t0 tS))

--  app-generic-triv :
--    {Γ : Ctx} {p : Cond} {n : ℕ}
--    → (n∈p : n ∈ p)
--    ------------------------------------------------------------------------
--    → computation {Γ = Γ} p
--      (app generic (canon-ℕ n))
--      (triv (canon-Bool (lookup p n n∈p)))

  app-generic-triv-false :
    {Γ : Ctx} {p : Cond} {n : ℕ}
    → (n∈p : n ∈ p)
    → (lookup p n n∈p ≡ false)
    ------------------------------------------------------------------------
    → computation {Γ = Γ} p
        (app generic (canon-ℕ n))
        (triv false)

  app-generic-triv-true :
    {Γ : Ctx} {p : Cond} {n : ℕ}
    → (n∈p : n ∈ p)
    → (lookup p n n∈p ≡ true)
    ------------------------------------------------------------------------
    → computation {Γ = Γ} p
        (app generic (canon-ℕ n))
        (triv true)

  app-generic-split :
    {Γ : Ctx} {p : Cond} {n : ℕ}
    → (n∉p : n ∉ p)
    ------------------------------------------------------------------------
    → computation {Γ = Γ} p
        (app generic (canon-ℕ n))
        (glue {n = n} {n∉p}
          (triv false)
          (triv true))
          --(triv {add-cond n false p n∉p} false)
          --(triv {add-cond n true  p n∉p} true))

  app-generic-step :
    {Γ : Ctx} {p : Cond} {t : Γ ⊢ N} {I : Part p} {Σ : ∑ N Γ I}
    → computation p t Σ
    ------------------------------------------------------------------------
    → computation p (app generic t) (Σ >>= app generic)


infix 5 computation
syntax computation p t s = p ⊨ t ↝ s


data normal-form :
  {p : Cond} → {Γ : Ctx} → {T : Ty} → (Γ ⊢ T) → {I : Part p} → ∑ T Γ I → Set where

  nf-bool :
    {Γ : Ctx} {p : Cond}
    → (b : Bool)
    ------------------------------------------------------------------------
    → normal-form {p} {Γ} (canon-Bool b) (triv (canon-Bool b))

  --nf-false :
  --  {Γ : Ctx} {p : Cond}
  --  ------------------------------------------------------------------------
  --  → normal-form {p} {Γ} (triv false) (triv false)

  nf-ℕ :
    {Γ : Ctx} {p : Cond}
    → (n : ℕ)
    ------------------------------------------------------------------------
    → normal-form {p} {Γ} (canon-ℕ n) (triv (canon-ℕ n))

  nf-succ-step :
    {Γ : Ctx} {p : Cond}
    → (t : Γ ⊢ N) {I : Part p} {Σ : ∑ N Γ I}
    → normal-form t Σ
    ------------------------------------------------------------------------
    → normal-form (succ t) (Σ >>= succ)

  nf-triv-step :
    {S : Ty} {Γ : Ctx} {p : Cond}
    → {t u : Γ ⊢ S} {I : Part p} {α : ∑ S Γ I}
    → p ⊨ t ↝ triv u
    → normal-form u α
    ------------------------------------------------------------------------
    → normal-form t α

  nf-glue-step :
    {S : Ty} {Γ : Ctx} {p : Cond}
    → (t : Γ ⊢ S) {n : ℕ} {n∉p : n ∉ p} {u₀ : Γ ⊢ S} {u₁ : Γ ⊢ S}
    → p ⊨ t ↝ glue {n = n} {n∉p} (triv u₀) (triv u₁)
    → {I₀ : Part (add-cond n false p n∉p)} {α₀ : ∑ S Γ I₀}
    → normal-form u₀ α₀
    → {I₁ : Part (add-cond n true  p n∉p)} {α₁ : ∑ S Γ I₁}
    → normal-form u₁ α₁
    ------------------------------------------------------------------------
    → normal-form t (glue α₀ α₁)
    
--  nf-glue-step :
--    {S : Ty} {Γ : Ctx} {p : Cond} (t : Γ ⊢ S)
--    {n : ℕ} {n∉p : n ∉ p}
--    → {I₀ J₀ : Part (add-cond n false p n∉p)} → {Σ₀ : ∑ S Γ I₀} → {α₀ : ∑ S Γ I₀}
--    → normal-form {add-cond n false p n∉p} Σ₀ α₀
--    → {I₁ J₁ : Part (add-cond n true  p n∉p)} → {Σ₁ : ∑ S Γ I₁} → {α₁ : ∑ S Γ I₁}
--    → normal-form {add-cond n true p n∉p} Σ₁ α₁
--    → p ⊨ t ↝ (glue Σ₀ Σ₁)
--    ------------------------------------------------------------------------
--    → normal-form (triv t) (glue α₀ α₁)

infix 5 normal-form
syntax normal-form Σ α = Σ ⇓ α


Σres : (q : Cond) → {p : Cond} → {I : Part p} → {S : Ty} → {Γ : Ctx}
     → ∑ S Γ I → (q≼p : q ≼ p) → ∑ S Γ (part-res q I q≼p)
Σres q (triv x) q≼p = triv x
Σres q {p} {I = split _ n _ _ _} (glue Σ₀ Σ₁) q≼p with n ∈? q
... | no  n∉q = glue
                  (Σres (add-cond n false q n∉q) Σ₀ (add-cond-preserves-≼ q≼p))
                  (Σres (add-cond n true  q n∉q) Σ₁ (add-cond-preserves-≼ q≼p))
... | yes n∈q with lookup q n n∈q | inspect (lookup q n) n∈q
...              | false | PE.[ eq ] = Σres q Σ₀ (add-cond-preserves-≼' n∈q eq q≼p)
...              | true  | PE.[ eq ] = Σres q Σ₁ (add-cond-preserves-≼' n∈q eq q≼p)

Σres-bind-comm : {q : Cond} → {p : Cond} → {I : Part p} → {S T : Ty} → {Γ : Ctx}
     → (Σ : ∑ S Γ I) → (f : (Γ ⊢ S) -> (Γ ⊢ T)) → (q≼p : q ≼ p)
     → (Σres q (Σ >>= f) q≼p ≡ (Σres q Σ q≼p) >>= f)
Σres-bind-comm (triv x) f _ = refl
Σres-bind-comm {q} (glue {n} Σ₀ Σ₁) f q≼p with n ∈? q
... | no  n∉q
      rewrite Σres-bind-comm {add-cond n false q n∉q} Σ₀ f (add-cond-preserves-≼ q≼p)
            | Σres-bind-comm {add-cond n true  q n∉q} Σ₁ f (add-cond-preserves-≼ q≼p)
      = refl
... | yes n∈q with lookup q n n∈q | inspect (lookup q n) n∈q
...     | false | PE.[ eq ] = Σres-bind-comm Σ₀ f (add-cond-preserves-≼' n∈q eq q≼p)
...     | true  | PE.[ eq ] = Σres-bind-comm Σ₁ f (add-cond-preserves-≼' n∈q eq q≼p)

open import Agda.Builtin.Equality.Rewrite
{-# REWRITE Σres-bind-comm #-}


lemma2a : {S : Ty} {Γ : Ctx} {p q : Cond} {t : Γ ⊢ S}
        → {I : Part p} {Σ : ∑ S Γ I}
        → p ⊨ t ↝ Σ
        → (q≼p : q ≼ p)
        → q ⊨ t ↝ Σres q Σ q≼p
lemma2a (app-step c) q≼p = app-step (lemma2a c q≼p)
lemma2a app-lam q≼p = app-lam
lemma2a boolrec-false q≼p = boolrec-false
lemma2a boolrec-true q≼p = boolrec-true
lemma2a (boolrec-step c) q≼p = boolrec-step (lemma2a c q≼p)
lemma2a natrec-zero q≼p = natrec-zero
lemma2a natrec-succ q≼p = natrec-succ
lemma2a (natrec-step c) q≼p = natrec-step (lemma2a c q≼p)
lemma2a (app-generic-triv-false n∈p eq) q≼p
  rewrite ≼-preserves-lookup (q≼p) n∈p = app-generic-triv-false (≼∈ q≼p n∈p) eq
lemma2a (app-generic-triv-true  n∈p eq) q≼p
  rewrite ≼-preserves-lookup (q≼p) n∈p = app-generic-triv-true  (≼∈ q≼p n∈p) eq
lemma2a {Γ = Γ} {q = q} (app-generic-split {n = n} n∉p) q≼p with n ∈? q
...  | no  n∉q = app-generic-split n∉q
...  | yes n∈q with lookup q n n∈q | inspect (lookup q n) n∈q
...               | false          | PE.[ eq ] = app-generic-triv-false n∈q eq
...               | true           | PE.[ eq ] = app-generic-triv-true  n∈q eq
lemma2a (app-generic-step c) q≼p = app-generic-step (lemma2a c q≼p)


lemma2b : {S : Ty} {Γ : Ctx} {p q : Cond} {t : Γ ⊢ S}
        → {I : Part p} {α : ∑ S Γ I}
        → t ⇓ α
        → (q≼p : q ≼ p)
        → t ⇓ (Σres q α q≼p)
lemma2b (nf-bool b) q≼p = nf-bool b
lemma2b (nf-ℕ n) q≼p = nf-ℕ n
lemma2b (nf-succ-step t t⇓α) q≼p = nf-succ-step t (lemma2b t⇓α q≼p)
lemma2b (nf-triv-step c u⇓α) q≼p
  = nf-triv-step (lemma2a c q≼p) (lemma2b u⇓α q≼p)
lemma2b {q = q} (nf-glue-step t {n} c u⇓α₀ u⇓α₁) q≼p with n ∈? q | lemma2a c q≼p
... | no  n∉q | c = nf-glue-step t c
                      (lemma2b u⇓α₀ (add-cond-preserves-≼ q≼p))
                      (lemma2b u⇓α₁ (add-cond-preserves-≼ q≼p))
... | yes n∈q | c with lookup q n n∈q | inspect (lookup q n) n∈q
...                  | false          | PE.[ eq ]
      = nf-triv-step c (lemma2b u⇓α₀ (add-cond-preserves-≼' n∈q eq q≼p))
...                  | true           | PE.[ eq ]
      = nf-triv-step c (lemma2b u⇓α₁ (add-cond-preserves-≼' n∈q eq q≼p))

{-
lemma2b' : {S : Ty} {Γ : Ctx} {p q : Cond}
         → {I : Part p} {α : ∑ S Γ I} {Σ : ∑ S Γ I}
         → Σ ⇓ α
         → (q≼p : q ≼ p)
         → (Σres q Σ q≼p) ⇓ (Σres q α q≼p)
lemma2b' (nf-bool b) q≼p = nf-bool b
lemma2b' (nf-succ-step t Σ⇓α) q≼p = nf-succ-step t (lemma2b' Σ⇓α q≼p)
lemma2b' (nf-triv-step t u u⇓α c) q≼p
  = nf-triv-step t u (lemma2b' u⇓α q≼p) (lemma2a t c q≼p)

lemma2b : {S : Ty} {Γ : Ctx} {p q : Cond} (t : Γ ⊢ S)
        → {I : Part p} {α : ∑ S Γ I}
        → triv t ⇓ α
        → (q≼p : q ≼ p)
        → (triv {q} t) ⇓ (Σres q α q≼p)
lemma2b .(canon-Bool b) (nf-bool b) q≼p = nf-bool b
lemma2b .(succ t) (nf-succ-step t t⇓α) q≼p
           = nf-succ-step t (lemma2b t t⇓α q≼p)
lemma2b t (nf-triv-step .t u u⇓α c) q≼p
  = nf-triv-step t u (lemma2b u u⇓α q≼p) (lemma2a t c q≼p)
lemma2b {q = q} t (nf-glue-step .t {n} {I₀ = I₀} {J₀} Σ⇓α₀ Σ⇓α₁ c) q≼p with n ∈? q
... | no  n∉q = nf-glue-step t
                  (lemma2b' Σ⇓α₀ (add-cond-preserves-≼ q≼p))
                  (lemma2b' Σ⇓α₁ (add-cond-preserves-≼ q≼p))
                  {!!}
--... | no  n∉q = nf-glue-step t {J₀ = J₀}
--                  (lemma2b' {I = I₀} t⇓α₀ (add-cond-preserves-≼ q≼p))
--                  (lemma2b' t⇓α₁ (add-cond-preserves-≼ q≼p))
--                  {!lemma2a t c q≼p!}
... | yes n∈q with lookup q n n∈q | inspect (lookup q n) n∈q
...              | false          | PE.[ eq ]
        = nf-triv-step {!!} {!!} {!!} {!!}
...              | true           | PE.[ eq ] = {!!}
-}
