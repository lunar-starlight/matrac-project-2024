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

open import Function
  using (_∘_)

open import Relation.Nullary.Decidable
  using (Dec; _because_; ¬?; yes; no) renaming (map to decmap)
open import Relation.Nullary.Negation
  using (¬_)
open import Data.List.Relation.Unary.Any
  using (Any; index; map; here; there; any?)
open import Relation.Binary
  using (Rel)
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_; refl; cong; cong₂; resp; sym; trans; inspect)


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

  val :
    {p : Cond} {T : Ty} {Γ : Ctx} {t : Γ ⊢ T}
    → value t
    ------------------------------------------------------------------------
    → forcing p T t
--  false :
--    {p : Cond} {Γ : Ctx}
--    ------------------------------------------------------------------------
--    → forcing p {Γ} B false

--  true :
--    {p : Cond} {Γ : Ctx}
--    ------------------------------------------------------------------------
--    → forcing p {Γ} B true

--  nat :
--    {p : Cond} {Γ : Ctx}
--    → (n : ℕ)
--    ------------------------------------------------------------------------
--    → forcing p {Γ} N (canon-ℕ n)

--  zero :
--    {p : Cond} {Γ : Ctx}
--    ------------------------------------------------------------------------
--    → forcing p {Γ} N zero

--  succ :
--    {p : Cond} {Γ : Ctx} {t : Γ ⊢ N}
--    → forcing p N t
--      ------------------------------------------------------------------------
--    → forcing p N (succ t)

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
    → (c : p ⊨ t ↝ triv u)
    → forcing p S u
    ------------------------------------------------------------------------
    → forcing p S t
  
  glue-step :
    {p : Cond} {Γ : Ctx} {S : Ty}
    → {t : Γ ⊢ S} {n : ℕ} {n∉p : n ∉ p} {u₀ : Γ ⊢ S} {u₁ : Γ ⊢ S}
    → (c : p ⊨ t ↝ glue {n = n} {n∉p} (triv u₀) (triv u₁))
    → (φ₀ : forcing (add-cond n false p n∉p) S u₀)
    → (φ₁ : forcing (add-cond n true  p n∉p) S u₁)
    ------------------------------------------------------------------------
    → forcing p S t

infix 5 forcing
syntax forcing p S t = p ⊩ t ∶ S

--lemma3
monotonicity : {q p : Cond} {Γ : Ctx} {S : Ty} {t : Γ ⊢ S}
             → (q≼p : q ≼ p) → (α : p ⊩ t ∶ S) → q ⊩ t ∶ S
monotonicity q≼p (val v) = {!!}
--monotonicity q≼p false = false
--monotonicity q≼p true = true
--monotonicity q≼p (nat n) = nat n
--monotonicity q≼p zero = zero
--monotonicity q≼p (succ α) = succ (monotonicity q≼p α)
monotonicity q≼p (func φ) = func (λ {r} r≼q α → φ (≼-trans r≼q q≼p) α)
monotonicity q≼p (triv-step c α) = triv-step (lemma2a c q≼p) (monotonicity q≼p α)
monotonicity {q} q≼p (glue-step {n = n} c α₀ α₁) with n ∈? q | lemma2a c q≼p
... | no  n∉q | c = glue-step c (monotonicity (add-cond-preserves-≼ q≼p) α₀) (monotonicity (add-cond-preserves-≼ q≼p) α₁)
... | yes n∈q | c with lookup q n n∈q | inspect (lookup q n) n∈q
...                  | false          | PE.[ eq ] = triv-step c (monotonicity (add-cond-preserves-≼ʳ n∈q eq q≼p) α₀)
...                  | true           | PE.[ eq ] = triv-step c (monotonicity (add-cond-preserves-≼ʳ n∈q eq q≼p) α₁)



{-
normal-form-ℕ : (p : Cond) → (t : [] ⊢ N) → Σ[ I ∈ Part p ] Σ[ σ ∈ ∑ N [] I ] normal-form t σ
normal-form-ℕ p (app t u) = {!!} , {!!} , {!!}
normal-form-ℕ p zero = whole p , triv zero , nf-ℕ zero
normal-form-ℕ p (succ t) with normal-form-ℕ p t
... | I , σ , α = I , (σ >>= succ) , nf-succ-step t α
-}

nf-succ-bind : {Γ : Ctx} {p : Cond} {t : Γ ⊢ N}
             → Σ[ I ∈ Part p ] Σ[ σ ∈ ∑ N Γ I ] normal-form t σ
             → Σ[ I ∈ Part p ] Σ[ σ ∈ ∑ N Γ I ] normal-form (succ t) (σ >>= succ)
nf-succ-bind (I , σ , α) = I , σ , nf-succ-step α

normal-form-ℕ : (p : Cond) → {t : [] ⊢ N} → (p ⊩ t ∶ N) → Σ[ I ∈ Part p ] Σ[ σ ∈ ∑ N [] I ] normal-form t σ
normal-form-ℕ p (val v) = {!!}
--normal-form-ℕ p (nat n) = whole p , triv (canon-ℕ n) , nf-ℕ n
--normal-form-ℕ p zero = whole p , (triv zero) , (nf-ℕ zero)
--normal-form-ℕ p (succ φ) with normal-form-ℕ p φ
--... | I , σ , α = I , (σ >>= succ) , nf-succ-step α
normal-form-ℕ p (triv-step c φ) with normal-form-ℕ p φ
... | I , σ , α = I , σ , nf-triv-step c α
normal-form-ℕ p (glue-step {n = n} {n∉p} c φ₀ φ₁)
  with normal-form-ℕ (add-cond n false p n∉p) φ₀ | normal-form-ℕ (add-cond n true p n∉p) φ₁
... | I₀ , σ₀ , α₀ | I₁ , σ₁ , α₁ = split p n n∉p I₀ I₁ , glue σ₀ σ₁ , nf-glue-step c α₀ α₁ 


generic-force : {p : Cond} → p ⊩ generic ∶ N ⇒ B
generic-force {p} = func Φ
  where

    Φ-canon : (q : Cond) → (n : ℕ) → q ⊩ app generic (canon-ℕ n) ∶ B
    Φ-canon q n with n ∈? q
    ...    | no  n∉q = glue-step {n = n} (app-generic-split n∉q) (val false) (val true)
    ...    | yes n∈q with lookup q n n∈q | inspect (lookup q n) n∈q
    ...              | false | PE.[ eq ] = triv-step (app-generic-triv-false n∈q eq) (val false)
    ...              | true  | PE.[ eq ] = triv-step (app-generic-triv-true  n∈q eq) (val true)

    Φ : {q : Cond} → {t : [] ⊢ N} → q ≼ p → forcing q N t → forcing q B (app generic t)
    Φ {t = t} q≼p φ with progress t
    Φ q≼p (triv-step d φ) | steps _ = triv-step (app-generic-step d) (Φ q≼p φ)
    Φ q≼p (glue-step d φ₀ φ₁) | steps _ =
         glue-step (app-generic-step d)
                   (Φ (add-cond-preserves-≼ˡ q≼p) φ₀)
                   (Φ (add-cond-preserves-≼ˡ q≼p) φ₁)
    Φ {q} _ (val v) | steps (succ-step _) with nat-value-canon v
    ...    | suc n , refl = Φ-canon q (suc n)
    Φ {q} _ φ | is-value v with nat-value-canon v
    ...    |     n , refl = Φ-canon q n


normal-form-Bool : (p : Cond) → {t : [] ⊢ B} → (p ⊩ t ∶ B) → Σ[ I ∈ Part p ] Σ[ σ ∈ ∑ B [] I ] normal-form t σ
normal-form-Bool p (val false) = whole p , triv false , nf-bool false
normal-form-Bool p (val true)  = whole p , triv true  , nf-bool true
normal-form-Bool p (triv-step c φ) with normal-form-Bool p φ
... | I , σ , α = I , σ , nf-triv-step c α
normal-form-Bool p (glue-step {n = n} {n∉p} c φ₀ φ₁)
  with normal-form-Bool (add-cond n false p n∉p) φ₀ | normal-form-Bool (add-cond n true p n∉p) φ₁
... | I₀ , σ₀ , α₀ | I₁ , σ₁ , α₁ = split p n n∉p I₀ I₁ , glue σ₀ σ₁ , nf-glue-step c α₀ α₁ 
{-
normal-form-Σ : (p : Cond) {S : Ty} → {t : [] ⊢ S} → (p ⊩ t ∶ S) → Σ[ I ∈ Part p ] Σ[ σ ∈ ∑ S [] I ] normal-form t σ
normal-form-Σ p false = whole p , triv false , nf-bool false
normal-form-Σ p true  = whole p , triv true  , nf-bool true
normal-form-Σ p (nat n) = whole p , triv (canon-ℕ n) , nf-ℕ n
normal-form-Σ p {t = lam t} (func f) = {!!} , {!!} , {!!}
normal-form-Σ p {t = app t t₁} (func f) = {!!} , {!!} , {!!}
normal-form-Σ p {t = natrec t t₁} (func f) = {!!} , {!!} , {!!}
normal-form-Σ p {t = boolrec t t₁} (func f) = {!!} , {!!} , {!!}
normal-form-Σ p {t = generic} (func f) = {!!} , {!!} , {!!}
normal-form-Σ p (triv-step c φ) with normal-form-Σ p φ
... | I , σ , α = I , σ , nf-triv-step c α
normal-form-Σ p (glue-step {n = n} {n∉p} c φ₀ φ₁)
  with normal-form-Σ (add-cond n false p n∉p) φ₀ | normal-form-Σ (add-cond n true p n∉p) φ₁
... | I₀ , σ₀ , α₀ | I₁ , σ₁ , α₁ = split p n n∉p I₀ I₁ , glue σ₀ σ₁ , nf-glue-step c α₀ α₁ 

mutual

  computable[]' : (p : Cond) → {S : Ty} → (s : [] ⊢ S) → (p ⊩ s ∶ S)
  computable[]' p {N} s = {!!}
  computable[]' p {B} s = {!!}
  computable[]' p {S ⇒ T} s = {!!}

  --{-# TERMINATING #-}
  computable[] : (p : Cond) → {S : Ty} → (s : [] ⊢ S) → (p ⊩ s ∶ S)
  computable[] p (lam {S} {T} s) = func Φ
    where
      Φ : {q : Cond} {u : [] ⊢ S} → q ≼ p → forcing q S u → forcing q T (app (lam s) u)
      Φ {q} {u} q≼p φ = triv-step app-lam (computable[] q (s [ u ]))

  computable[] p (app t u) with computable[] p t
  ... | func f = f ≼-refl (computable[] p u)
  ... | triv-step {u = t'} c φ = triv-step (app-step c) (computable[] p (app t' u))
  ... | glue-step {u₀ = u₀} {u₁} c φ₀ φ₁ = glue-step (app-step c)
                                      (computable[] (add-cond _ false p _) (app u₀ u))
                                      (computable[] (add-cond _ true  p _) (app u₁ u))
  computable[] p zero = nat zero
  computable[] p (succ s) with computable[] p s
  ... | φ = {!!}
  computable[] p (natrec s s₁) = {!!}
  computable[] p false = {!!}
  computable[] p true = {!!}
  computable[] p (boolrec s s₁) = {!!}
  computable[] p generic = {!!}

  computable:: : (p : Cond) → {Γ : Ctx} {S T : Ty} → (s : T ∷ Γ ⊢ S) → (t : Γ ⊢ T)
               → (p ⊩ t ∶ T) → (p ⊩ s [ t ] ∶ S) → (p ⊩ s ∶ S)
  computable:: p s (var x) φ₀ φₛ = {!!}
  computable:: p s (lam t) φ₀ φₛ = {!!}
  computable:: p s (app t t₁) φ₀ φₛ = {!!}
  computable:: p s zero φ₀ φₛ = {!!}
  computable:: p s (succ t) φ₀ φₛ = {!!}
  computable:: p s (natrec t t₁) φ₀ φₛ = {!!}
  computable:: p s false φ₀ φₛ = {!!}
  computable:: p s true φ₀ φₛ = {!!}
  computable:: p s (boolrec t t₁) φ₀ φₛ = {!!}
  computable:: p s generic φ₀ φₛ = {!!}
-}


∅-fam : {S : Ty} {A : S c∈ [] → Set} → (x : S c∈ []) → A x
∅-fam ()

succ-lemma : {Γ : Ctx} {p : Cond} {t : Γ ⊢ N} → (φ : p ⊩ t ∶ N)
           → p ⊩ succ t ∶ N
succ-lemma {t = t} (val v) = val (succ v)
succ-lemma (triv-step c φ) = triv-step (succ-step c) (succ-lemma φ)
succ-lemma (glue-step c φ₀ φ₁) = glue-step (succ-step c) (succ-lemma φ₀) (succ-lemma φ₁)

weaken-⊩ : {Γ : Ctx} {T : Ty} {p q : Cond} {t : Γ ⊢ T} → q ≼ p → (p ⊩ t ∶ T) → (q ⊩ t ∶ T)
weaken-⊩ q≼p (val x) = val x
weaken-⊩ {q = q} q≼p (func Φ) = func (λ {r} r≼q φ → Φ (≼-trans r≼q q≼p) φ)
weaken-⊩ q≼p (triv-step c φ) = triv-step {!!} (weaken-⊩ q≼p φ)
weaken-⊩ q≼p (glue-step c φ₀ φ₁) = {!!}

weaken-⊩' : {Γ : Ctx} {T : Ty} {p : Cond} {t : Γ ⊢ T} → (∅ ⊩ t ∶ T) → (p ⊩ t ∶ T)
weaken-⊩' = weaken-⊩ λ { _ ()}

forcing-step : {T : Ty} {Γ : Ctx} {t u : Γ ⊢ T} {p : Cond} → (c : p ⊨ t ↝ triv u) → (p ⊩ u ∶ T) → p ⊩ t ∶ T
forcing-step c (val v) = triv-step c (val v)
forcing-step c (func Φ) = func (λ q≼p φ → forcing-step (app-step (weaken-comp q≼p c)) (Φ q≼p φ) )
forcing-step c (triv-step c' φ) = triv-step c (forcing-step c' φ)
forcing-step c (glue-step c' φ₀ φ₁) = triv-step c (glue-step c' φ₀ φ₁)

{-# TERMINATING #-}
subst-computable : (Γ : Ctx) {T : Ty} {p : Cond} → (t : Γ ⊢ T)
                 → (σ : {S : Ty} → S c∈ Γ → [] ⊢ S)
                 → (Φ : {S : Ty} → (x : S c∈ Γ) → p ⊩ σ x ∶ S)
                 → p ⊩ subst σ t ∶ T
subst-computable [] t σ Φ with progress t
... | is-value zero = val zero
... | is-value false = val false
... | is-value true = val true
... | is-value lam = val lam
... | is-value natrec = val natrec
... | is-value boolrec = val boolrec
... | is-generic = generic-force
subst-computable [] {p = p} (app t u) σ Φ | steps c with subst-computable [] {p = p} t σ Φ
subst-computable [] {p = _} (app (lam t) u) σ Φ | steps app-lam | val lam = triv-step app-lam (subst-computable [] (t [ u ]) σ Φ)
subst-computable [] {p = p} (app .(boolrec _ _) u) σ Φ | steps _ | val boolrec with normal-form-Bool p (subst-computable [] u σ Φ)
... | .(whole p) , .(triv (canon-Bool false)) , nf-bool false = triv-step boolrec-false (subst-computable [] _ σ Φ)
... | .(whole p) , .(triv (canon-Bool true )) , nf-bool true  = triv-step boolrec-true  (subst-computable [] _ σ Φ)
... | I , Σ , nf-triv-step c α = triv-step (boolrec-step c) (subst-computable [] _ σ Φ)
... | .(split p _ _ _ _) , .(glue _ _) , nf-glue-step c α α₁ =
  glue-step (boolrec-step c)
            (subst-computable [] _ σ (λ x → weaken-⊩ (add-cond-preserves-≼ˡ ≼-refl) (Φ x)))
            (subst-computable [] _ σ (λ x → weaken-⊩ (add-cond-preserves-≼ˡ ≼-refl) (Φ x)))

subst-computable [] {p = p} (app .(natrec _ _) u) σ Φ | steps _ | val natrec with normal-form-ℕ p (subst-computable [] u σ Φ)
... | .(whole p) , .(triv (canon-ℕ zero)) , nf-ℕ zero = triv-step natrec-zero (subst-computable [] _ σ Φ)
... | .(whole p) , .(triv (canon-ℕ (suc n))) , nf-ℕ (suc n) = triv-step natrec-succ (subst-computable [] _ σ Φ)
... | I , .(_ >>= succ) , nf-succ-step α = triv-step natrec-succ (subst-computable [] _ σ Φ)
... | I , Σ , nf-triv-step c α = triv-step (natrec-step c) (subst-computable [] _ σ Φ)
... | .(split p _ _ _ _) , .(glue _ _) , nf-glue-step c α α₁ =
  glue-step (natrec-step c)
            (subst-computable [] _ σ (λ x → weaken-⊩ (add-cond-preserves-≼ˡ ≼-refl) (Φ x)))
            (subst-computable [] _ σ (λ x → weaken-⊩ (add-cond-preserves-≼ˡ ≼-refl) (Φ x)))
subst-computable [] {p = _} (app t u) σ Φ | steps c | func φ = φ ≼-refl (subst-computable [] u σ Φ)
subst-computable [] {T} {p} (app t u) σ Φ | steps c | triv-step {u = t'} c₁ φ
  = triv-step (app-step c₁)
              (resp (λ x → forcing p T (app x (subst σ u)))
                (empty-subst-is-id σ t')
                (subst-computable [] (app t' u) σ Φ ))
subst-computable [] {p = _} (app t u) σ Φ | steps c | glue-step {u₀ = t₀} {t₁} c₁ φ₀ φ₁
  = glue-step (app-step c₁)
              (subst-computable [] (app t₀ u) σ λ {()})
              (subst-computable [] (app t₁ u) σ λ {()})

subst-computable [] (succ t) σ Φ | steps (succ-step c) = succ-lemma (subst-computable [] t σ Φ)
subst-computable [] (succ t) σ Φ | is-value (succ v) with nat-value-canon v
... | n , refl rewrite subst-canon n σ = val (succ v)

subst-computable (S ∷ Γ) t σ Φ with subst-computable Γ (t [ weaken (σ (here refl)) ]) (σ ∘ there) (Φ ∘ there)
... | val v = {!!}
... | func x = {!!}
... | triv-step c φ = {!!}
... | glue-step c φ φ₁ = {!!}

{-
{-# TERMINATING #-}
subst-computable : {Γ : Ctx} {T : Ty} {p : Cond} → (t : Γ ⊢ T)
                 → (σ : {S : Ty} → S c∈ Γ → [] ⊢ S)
                 → (Φ : {S : Ty} → (x : S c∈ Γ) → p ⊩ σ x ∶ S)
                 → p ⊩ subst σ t ∶ T
subst-computable {[]} (lam t) _ Φ = {!!}
subst-computable {[]} {T} {p} (app t u) σ Φ with subst-computable t σ ∅-fam
... | func f = f ≼-refl (subst-computable u σ Φ)
... | triv-step {u = t'} c φ 
                   = triv-step (app-step c)
                                 (resp (λ x → forcing p T (app t' x))
                                   (sym (lemma₁ u))
                                   {!resp (λ x → forcing p T (app x (subst σ u))) (lemma₁ t')!})
                                --(subst-computable {!app t' u!} id-subst ∅))
    where
      lemma₁ : {S : Ty} (s : [] ⊢ S) → subst σ s ≡ s
      lemma₁ s = trans
               (subst-resp (empty-subst-is-prop σ) s)
               (subst-id≡id s)

... | glue-step {u₀ = t₀} {t₁} c φ₀ φ₁ = glue-step (app-step c)
                                                   (subst-computable {[]} {!app t₀ u!} σ ∅-fam)
                                                   (subst-computable {[]} {!app t₁ u!} σ ∅-fam)
subst-computable {[]} zero _ _ = nat zero
subst-computable {[]} (succ t) _ _ = {!!}
subst-computable {[]} (natrec t₀ tₛ) _ _ = {!!}
subst-computable {[]} false _ _ = false
subst-computable {[]} true  _ _ = true
subst-computable {[]} (boolrec t₀ t₁) _ _ = {!!}
subst-computable {[]} generic _ _ = generic-force _
subst-computable {S ∷ Γ} t σ Φ with subst-computable (t [ weaken (σ (here refl)) ]) (σ ∘ there) (Φ ∘ there)
... | φ = {!!}
-}

computable : {p : Cond} {T : Ty} → (t : [] ⊢ T) → p ⊩ t ∶ T
computable {p} {T} t = resp (forcing p T) (subst-id≡id t) (subst-computable [] t id-subst ∅-fam)

bool-force : (p : Cond) → (t : [] ⊢ B) → p ⊩ t ∶ B
bool-force p (app t u) = {!!}
{-
with computable[] p t | computable[] p u
... | func x | ψ = x ≼-refl ψ
... | triv-step c φ | ψ = triv-step (app-step c) {!!}
... | glue-step c φ₀ φ₁ | ψ = {!!}
-}
bool-force p false = val false
bool-force p true  = val true

modulus-of-continuity : (F : [] ⊢ (N ⇒ B) ⇒ B) → ℕ
modulus-of-continuity F = μ
  where
    empty : Cond
    empty = cond [] nil
    ⊩Ff : empty ⊩ app F generic ∶ B
    ⊩Ff = computable (app F generic) -- computable empty (app F generic)

    step₂ : Σ[ I ∈ Part empty ] Σ[ σ ∈ ∑ B [] I ] normal-form (app F generic) σ
    step₂ = normal-form-Bool empty ⊩Ff

    mod-of-cond : Carrier → ℕ
    mod-of-cond [] = zero
    mod-of-cond ((n , _) ∷ ‖p‖) = n ⊔ mod-of-cond ‖p‖
  
    mod-of-tree : {p : Cond} → Part p → ℕ
    mod-of-tree (whole p) = mod-of-cond (Cond.carrier p)
    mod-of-tree (split p n n∉p I₀ I₁) = mod-of-tree I₀ ⊔ mod-of-tree I₁

    μ : ℕ
    μ = mod-of-tree (proj₁ step₂)
