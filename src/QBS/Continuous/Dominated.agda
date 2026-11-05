{-# OPTIONS --safe --without-K #-}

-- Dominated convergence for tests on any X (plan 03, "Dominated convergence").
--   * `Conv a l`: a sequence of values converges to l when lim inf a ≈ l ≈ lim sup a (convergence in [0, ∞]);
--   * `dct`: if h n → f pointwise and every h n ≤ g with ∫ g finite, then ∫ h n → ∫ f;
--   * `mct-conv`: an increasing sequence of tests has ∫ h n → ∫ ⋃ h (no domination needed);
--   * `dct-prob`: under a probability measure (`ιPre`), uniformly bounded h n → f gives E h n → E f.
-- Route: `dct` chains lim sup ∫ h ≤ ∫ lim sup h ≤ ∫ f ≤ ∫ lim inf h ≤ lim inf ∫ h ≤ lim sup ∫ h (`Fatou.rev-fatou`,
-- `SupTest.∫ᴹ-monoX` with `liminfH-pt`/`limsupH-pt`, `Fatou.fatou`, `LowerRealsInf.liminf-limsup`); `mct-conv` from
-- `SupTest.∫ᴹ-sup` (for increasing a, lim inf a ≈ lim sup a ≈ ⋃ a); `dct-prob` is `dct` with g constant (the
-- integral of a constant c is c times the mass 1).
module QBS.Continuous.Dominated where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using () renaming (+-suc to +ℕ-suc; +-comm to +ℕ-comm; +-identityʳ to +ℕ-identityʳ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst) renaming (sym to ≡sym)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (Cut; unionC; _⊑_; ⊑-refl; ⊑-trans; _≋_; union-ub; union-lub)
open import QBS.Analysis.LowerRealsInf using (liminfC; limsupC; inter-lb; inter-glb; liminf-limsup)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Fatou using (module Fatou)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SupTest using (module SupTest)

-- an increasing sequence of cuts: a m ≤ a (m + k)
inc-add : ∀ (a : ℕ → Cut) → (∀ n → a n ⊑ a (suc n)) → ∀ m k → a m ⊑ a (m +ℕ k)
inc-add a inc m zero = subst (λ i → a m ⊑ a i) (≡sym (+ℕ-identityʳ m)) ⊑-refl
inc-add a inc m (suc k) = ⊑-trans (inc-add a inc m k)
  (subst (λ i → a (m +ℕ k) ⊑ a i) (≡sym (+ℕ-suc m k)) (inc (m +ℕ k)))

-- for an increasing sequence of cuts, lim inf = lim sup = ⋃
liminf-inc : ∀ (a : ℕ → Cut) → (∀ n → a n ⊑ a (suc n)) → liminfC a ≋ unionC a
liminf-inc a inc = union-lub _ (λ n → ⊑-trans (inter-lb _ 0) (union-ub a (n +ℕ 0)))
  , union-lub _ (λ n → ⊑-trans (inter-glb _ (λ k → inc-add a inc n k)) (union-ub _ n))

limsup-inc : ∀ (a : ℕ → Cut) → (∀ n → a n ⊑ a (suc n)) → limsupC a ≋ unionC a
limsup-inc a inc = inter-lb _ 0 , inter-glb _ (λ n → union-lub _ (λ m →
  ⊑-trans (inc-add a inc m n) (subst (λ i → a i ⊑ unionC (λ k → a (n +ℕ k))) (+ℕ-comm n m) (union-ub _ m))))

module Dominated (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J-cong; J-scale; J-fun; J-irrel)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_; refl; trans; *-cong; *-comm; *-identityˡ; ≤-reflexive) renaming (Carrier to ∣A∣)
  open Measurable A using (Fun-const)
  open OmegaSemiring A using (≤-refl; 1#; _*_)
  open Bounded A using (Bnd; nat)
  open Weights (lemOf lem₁) using (WQ; constW)
  open Meas (lemOf lem₁) using (Meas-const; Meas-⊗)
  open LevelSets (lemOf lem₁) using (LS)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ψ; mψ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SupTest (lemOf lem₁) using (supH; liminfH; limsupH; liminfH-pt; limsupH-pt; ∫ᴹ-monoX; ∫ᴹ-sup)
  open Fatou lem₁ using (fatou; rev-fatou)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open C.Pre using (m; ok)
  open QBS
  open Hom

  -- convergence in [0, ∞]
  Conv : (ℕ → ∣A∣) → ∣A∣ → Set₁
  Conv a l = liminfC a ≈ l × limsupC a ≈ l

  module _ {X : QBS S} where

    dct : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) (f g : Hom S X WQ) →
      (∀ x → Conv (λ n → map (h n) ⟨$⟩ x) (map f ⟨$⟩ x)) →
      (∀ n x → map (h n) ⟨$⟩ x ≤ map g ⟨$⟩ x) → Bnd (∫ᴹ {X} p g) →
      Conv (λ n → ∫ᴹ {X} p (h n)) (∫ᴹ {X} p f)
    dct p h f g cv le bg = (⊑-trans (liminf-limsup _) A↑ , B↓) , (A↑ , ⊑-trans B↓ (liminf-limsup _))
      where
        A↑ = ⊑-trans (rev-fatou p h g le bg)
          (∫ᴹ-monoX p {limsupH h} {f} (λ x → ⊑-trans (proj₁ (limsupH-pt h x)) (proj₁ (proj₂ (cv x)))))
        B↓ = ⊑-trans (∫ᴹ-monoX p {f} {liminfH h} (λ x → ⊑-trans (proj₂ (proj₁ (cv x))) (proj₂ (liminfH-pt h x))))
          (fatou p h)

    mct-conv : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → (∀ n x → map (h n) ⟨$⟩ x ≤ map (h (suc n)) ⟨$⟩ x) →
      Conv (λ n → ∫ᴹ {X} p (h n)) (∫ᴹ {X} p (supH h))
    mct-conv p h inc = (⊑-trans (proj₁ (liminf-inc u iu)) (proj₂ e) , ⊑-trans (proj₁ e) (proj₂ (liminf-inc u iu)))
      , (⊑-trans (proj₁ (limsup-inc u iu)) (proj₂ e) , ⊑-trans (proj₁ e) (proj₂ (limsup-inc u iu)))
      where
        u : ℕ → Cut
        u n = ∫ᴹ {X} p (h n)
        iu : ∀ n → u n ⊑ u (suc n)
        iu n = ∫ᴹ-monoX p {h n} {h (suc n)} (inc n)
        e = ∫ᴹ-sup p h inc

    -- a probability measure gives a constant its value
    prob-mass : ∀ (P : Pre X) c → ∫ᴹ {X} (ιPre {X} P) (constW {X} c) ≈ c
    prob-mass P c = trans (J-cong (m P) {ψ {X} (ιPre {X} P) (constW {X} c)} {λ _ → c * 1#}
        (mψ {X} (ιPre {X} P) (constW {X} c)) (Meas-⊗ {λ _ → c} {λ _ → 1#} (Meas-const c) (Meas-const 1#))
        (λ r → *-comm 1# c))
      (trans (J-scale (m P) c {λ _ → 1#} (Meas-const 1#))
        (trans (*-cong refl (trans (J-irrel (m P) {λ _ → 1#} (Meas-const 1#) (LS (Fun-const 1# ≤-refl)))
                              (trans (J-fun (m P) (Fun-const 1# ≤-refl)) (ok P))))
          (trans (*-comm c 1#) (*-identityˡ c))))

    dct-prob : ∀ (P : Pre X) (h : ℕ → Hom S X WQ) (f : Hom S X WQ) N →
      (∀ x → Conv (λ n → map (h n) ⟨$⟩ x) (map f ⟨$⟩ x)) → (∀ n x → map (h n) ⟨$⟩ x ≤ nat N) →
      Conv (λ n → ∫ᴹ {X} (ιPre {X} P) (h n)) (∫ᴹ {X} (ιPre {X} P) f)
    dct-prob P h f N cv bd = dct (ιPre {X} P) h f (constW {X} (nat N)) cv bd
      (N , ≤-reflexive (prob-mass P (nat N)))
