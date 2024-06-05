{-# OPTIONS --allow-unsolved-metas --rewriting #-}
module CompTree where

open import Data.Bool
  using (true; false; Bool)
open import Data.Nat
  using (zero; suc; ℕ; _≤_; _⊔_)
open import Data.List
  using (List; []; _∷_)
open import Data.Product

open import Relation.Nullary.Decidable
  using (yes; no)
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_; refl; cong; cong₂; resp; sym; trans; inspect)


open import Cantor
open import Syntax

data computes {T : Ty} {p : Cond} : {I J : Part p} → (σ : ∑ T [] I) → (τ : ∑ T [] J) →  Set where
  stay : {I : Part p} → (σ : ∑ T [] I) → computes σ σ
  go   : {I J : Part p} → (σ : ∑ T [] I) → (τ : ∑ T [] J)
       → Σ[ K ∈ Part p ] Σ[ κ ∈ ∑ T [] K ] p ⊨' σ ↝ κ × computes κ τ → computes σ τ

glue-comp :
  {T : Ty} {p : Cond}
  {n : ℕ} {n∉p : n ∉ p} 
  {I₀ J₀ : Part (add-cond n false p n∉p)} {σ₀ : ∑ T [] I₀} {τ₀ : ∑ T [] J₀}
  {I₁ J₁ : Part (add-cond n true  p n∉p)} {σ₁ : ∑ T [] I₁} {τ₁ : ∑ T [] J₁}
  → (c₀ : computes σ₀ τ₀)
  → (c₁ : computes σ₁ τ₁)
  ------------------------------------------------------------------------
  → computes (glue σ₀ σ₁) (glue τ₀ τ₁)
glue-comp (stay σ) (stay τ) = stay (glue σ τ)
glue-comp (stay σ) (go _ _ (K , κ , c , γ)) = go (glue σ _) (glue σ _) (split _ _ _ _ K , glue σ κ , glue-stepʳ c , glue-comp (stay σ) γ)
glue-comp (go _ _ (K , κ , c , γ)) x        = go (glue _ _) (glue _ _) (split _ _ _ K _ , glue _ _ , glue-stepˡ c , glue-comp γ x)

weaken-comp-term : {p q : Cond} {T : Ty} {Γ : Ctx} {t : Γ ⊢ T} {I : Part p} {σ : ∑ T Γ I}
                 → (q≼p : q ≼ p) → (c : p ⊨ t ↝ σ) → (q ⊨ t ↝ Σres q σ q≼p)
weaken-comp-term q≼p (succ-step        c) = succ-step        (weaken-comp-term q≼p c)
weaken-comp-term q≼p (app-step         c) = app-step         (weaken-comp-term q≼p c)
weaken-comp-term q≼p app-lam              = app-lam
weaken-comp-term q≼p boolrec-false        = boolrec-false
weaken-comp-term q≼p boolrec-true         = boolrec-true
weaken-comp-term q≼p (boolrec-step     c) = boolrec-step     (weaken-comp-term q≼p c)
weaken-comp-term q≼p natrec-zero          = natrec-zero
weaken-comp-term q≼p natrec-succ          = natrec-succ
weaken-comp-term q≼p (natrec-step      c) = natrec-step      (weaken-comp-term q≼p c)
weaken-comp-term q≼p (app-generic-step c) = app-generic-step (weaken-comp-term q≼p c)
weaken-comp-term q≼p (app-generic-triv-false n∈p eq) rewrite ≼-preserves-lookup q≼p n∈p
  = app-generic-triv-false (≼∈ q≼p n∈p) eq
weaken-comp-term q≼p (app-generic-triv-true  n∈p eq) rewrite ≼-preserves-lookup q≼p n∈p
  = app-generic-triv-true  (≼∈ q≼p n∈p) eq
weaken-comp-term {q = q} q≼p (app-generic-split {n = n} _) with n ∈? q
... | no  n∉q = app-generic-split n∉q
... | yes n∈q with lookup q n n∈q | inspect (lookup q n) n∈q
...     | false | PE.[ eq ] = app-generic-triv-false n∈q eq
...     | true  | PE.[ eq ] = app-generic-triv-true  n∈q eq

weaken-comp : {p : Cond} {T : Ty} {Γ : Ctx} {t : Γ ⊢ T} {I : Part ∅} {σ : ∑ T Γ I}
             → (c : ∅ ⊨ t ↝ σ) → p ⊨ t ↝ Σres p σ p≼∅
weaken-comp = weaken-comp-term p≼∅

-- This is ok because the terms strictly decrease in complexity
{-# TERMINATING #-}
ev : {p : Cond} {T : Ty} {I : Part p} → (σ : ∑ T [] I) → Σ[ J ∈ Part p ] Σ[ τ ∈ ∑ T [] J ] value τ × computes σ τ
ev σ with progress σ
ev {p} (triv t) | triv-prog (is-value v) = whole p , triv t , triv-val v , stay (triv t)
ev {p} (triv t) | triv-prog (steps {I = I} {σ} c) = J , τ , proj₁ IH , go (triv t) τ (K , κ , triv-step (weaken-comp c) , proj₂ IH)
  where κ = Σres p σ p≼∅
        K = part-res p I p≼∅
        IH' = ev κ
        J = proj₁ IH'
        τ = proj₁ (proj₂ IH')
        IH = proj₂ (proj₂ IH')
ev {p} (glue {n} {n∉p} {I₀} σ₀ {I₁} σ₁) | glue-prog _ _ = J , τ , glue-val (proj₁ IH₀) (proj₁ IH₁) , glue-comp (proj₂ IH₀) (proj₂ IH₁)
  where ev₀ = ev σ₀
        J₀  = proj₁ ev₀
        τ₀  = proj₁ (proj₂ ev₀)
        IH₀ = proj₂ (proj₂ ev₀)
        ev₁ = ev σ₁
        J₁  = proj₁ ev₁
        τ₁  = proj₁ (proj₂ ev₁)
        IH₁ = proj₂ (proj₂ ev₁)
        J   = split p n n∉p J₀ J₁
        τ   = glue τ₀ τ₁

modulus-of-continuity : (F : [] ⊢ (N ⇒ B) ⇒ B) → ℕ
modulus-of-continuity F = μ
  where
    --⊩Ff : Σ[ I ∈ Part ∅ ] Σ[ b ∈ ∑ B [] I ] (value b × computes (triv (app F generic)) b)
    ⊩Fgeneric-tree : Part ∅
    ⊩Fgeneric-tree = proj₁ (ev (triv (app F generic)))

    mod-of-cond : Carrier → ℕ
    mod-of-cond [] = zero
    mod-of-cond ((n , _) ∷ ‖p‖) = n ⊔ mod-of-cond ‖p‖
  
    mod-of-tree : {p : Cond} → Part p → ℕ
    mod-of-tree (whole p) = mod-of-cond ‖ p ‖
    mod-of-tree (split _ _ _ I₀ I₁) = mod-of-tree I₀ ⊔ mod-of-tree I₁

    μ : ℕ
    μ = mod-of-tree ⊩Fgeneric-tree
