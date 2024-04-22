{-# OPTIONS --allow-unsolved-metas --rewriting #-}
module Forcing where

open import Data.Unit
open import Data.Empty
open import Data.Bool
  using (true; false; Bool)
open import Data.Nat
  --using (zero; suc; ℕ; _≤_)
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
  using (_≡_; refl; cong; sym; inspect)


open import Cantor
open import Syntax


ty-level : Ty → ℕ
ty-level N = zero
ty-level B = zero
ty-level (S ⇒ T) = suc (ty-level S)

ty-level-B : ty-level B ≡ zero
ty-level-B = refl

-- This is stratified by ℕ, so there's (likeley) no paradox here
{-
{-# NO_POSITIVITY_CHECK #-}
data forcing :
  (p : Cond) → {n : ℕ} → {Γ : Ctx} → (S : Ty) → {{ty-level S ≤ n}} → (Γ ⊢ S) → Set where

  false :
    {p : Cond} {n : ℕ} {Γ : Ctx}
    ------------------------------------------------------------------------
    → forcing p {n} {Γ} B {{z≤n}} false

  true :
    {p : Cond} {n : ℕ} {Γ : Ctx}
    ------------------------------------------------------------------------
    → forcing p {n} {Γ} B {{z≤n}} true

  zero :
    {p : Cond} {n : ℕ} {Γ : Ctx}
    ------------------------------------------------------------------------
    → forcing p {n} {Γ} N {{z≤n}} zero

  succ :
    {p : Cond} {Γ : Ctx} {n : ℕ} {t : Γ ⊢ N}
    → forcing p {n} N {{z≤n}} t
    ------------------------------------------------------------------------
    → forcing p {n} N {{z≤n}} (succ t)

  func :
    {p : Cond} {n m : ℕ} {Γ : Ctx} {S T : Ty}
    {S≤n : ty-level S ≤ n} {T≤m : ty-level T ≤ m} {t : Γ ⊢ S ⇒ T}
    → ({q : Cond} → {q ≼ p} → {u : Γ ⊢ S}
      → forcing q {n} S {{S≤n}} u
      → forcing q {m} T {{T≤m}} (app t u))
    ------------------------------------------------------------------------
    → forcing p {suc n} (S ⇒ T) {{s≤s S≤n}} t

  triv-step :
    {p : Cond} {n : ℕ} {Γ : Ctx} {S : Ty} {S≤n : ty-level S ≤ n} {t u : Γ ⊢ S}
    → p ⊨ t ↝ triv u
    → forcing p {n} S {{S≤n}} u
    ------------------------------------------------------------------------
    → forcing p {n} S {{S≤n}} t
  
  glue-step :
    {p : Cond} {ℓ : ℕ} {Γ : Ctx} {S : Ty} {S≤ℓ : ty-level S ≤ ℓ}
    → (t : Γ ⊢ S) {n : ℕ} {n∉p : n ∉ p} {u₀ : Γ ⊢ S} {u₁ : Γ ⊢ S}
    → p ⊨ t ↝ glue {n = n} {n∉p} (triv u₀) (triv u₁)
    → forcing p {ℓ} S {{S≤ℓ}} u₀
    → forcing p {ℓ} S {{S≤ℓ}} u₁
    ------------------------------------------------------------------------
    → forcing p {ℓ} S {{S≤ℓ}} t
-}
{-# NO_POSITIVITY_CHECK #-}
data forcing :
  (p : Cond) → {Γ : Ctx} → (S : Ty) → (Γ ⊢ S) → Set where

  false :
    {p : Cond} {Γ : Ctx}
    ------------------------------------------------------------------------
    → forcing p {Γ} B false

  true :
    {p : Cond} {Γ : Ctx}
    ------------------------------------------------------------------------
    → forcing p {Γ} B true

  zero :
    {p : Cond} {Γ : Ctx}
    ------------------------------------------------------------------------
    → forcing p {Γ} N zero

  succ :
    {p : Cond} {Γ : Ctx} {t : Γ ⊢ N}
    → forcing p N t
      ------------------------------------------------------------------------
    → forcing p N (succ t)

  func :
    {p : Cond} {Γ : Ctx} {S T : Ty} {t : Γ ⊢ S ⇒ T}
    → ({q : Cond} → {u : Γ ⊢ S}
      → (q ≼ p)
      → forcing q S u
      → forcing q T (app t u))
    ------------------------------------------------------------------------
    → forcing p (S ⇒ T) t

  triv-step :
    {p : Cond} {Γ : Ctx} {S : Ty} {t u : Γ ⊢ S}
    → p ⊨ t ↝ triv u
    → forcing p S u
    ------------------------------------------------------------------------
    → forcing p S t
  
  glue-step :
    {p : Cond} {Γ : Ctx} {S : Ty}
    → {t : Γ ⊢ S} {n : ℕ} {n∉p : n ∉ p} {u₀ : Γ ⊢ S} {u₁ : Γ ⊢ S}
    → p ⊨ t ↝ glue {n = n} {n∉p} (triv u₀) (triv u₁)
    → forcing p S u₀
    → forcing p S u₁
    ------------------------------------------------------------------------
    → forcing p S t

infix 5 forcing
syntax forcing p S t = p ⊩ t ∶ S

--lemma3
monotonicity : {q p : Cond} {Γ : Ctx} {S : Ty} {t : Γ ⊢ S}
             → (q≼p : q ≼ p) → (α : p ⊩ t ∶ S) → q ⊩ t ∶ S
monotonicity q≼p false = false
monotonicity q≼p true = true
monotonicity q≼p zero = zero
monotonicity q≼p (succ α) = succ (monotonicity q≼p α)
monotonicity q≼p (func φ) = func (λ {r} r≼q α → φ (≼-trans r≼q q≼p) α)
monotonicity q≼p (triv-step c α) = triv-step (lemma2a c q≼p) (monotonicity q≼p α)
monotonicity {q} q≼p (glue-step {n = n} c α₀ α₁) with n ∈? q | lemma2a c q≼p
... | no  n∉q | c = glue-step c (monotonicity q≼p α₀) (monotonicity q≼p α₁)
... | yes n∈q | c with lookup q n n∈q | inspect (lookup q n) n∈q
...                  | false          | PE.[ eq ] = triv-step c (monotonicity q≼p α₀)
...                  | true           | PE.[ eq ] = triv-step c (monotonicity q≼p α₁)



normal-form-ℕ : (p : Cond) → (t : [] ⊢ N) → Σ[ I ∈ Part p ] Σ[ σ ∈ ∑ N [] I ] normal-form t σ
normal-form-ℕ p (app t u) = {!!} , {!!} , {!!}
normal-form-ℕ p zero = whole p , triv zero , nf-ℕ zero
normal-form-ℕ p (succ t) with normal-form-ℕ p t
... | I , σ , α = I , (σ >>= succ) , nf-succ-step t α


generic-force : (p : Cond) {Γ : Ctx} → p ⊩ (generic {Γ}) ∶ N ⇒ B
generic-force p {Γ} = func φ
  where
    φ : {q : Cond} → {t : Γ ⊢ N} → q ≼ p → forcing q N t → forcing q B (app generic t)
    φ {q} q≼p zero = {!!}
    φ {q} {.(succ _)} q≼p (succ α) = {!!}
    φ q≼p (triv-step c α) = triv-step (app-generic-step c) (φ q≼p α)
    φ q≼p (glue-step c α₀ α₁) = glue-step (app-generic-step c) (φ q≼p α₀) (φ q≼p α₁)


