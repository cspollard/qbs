{-# OPTIONS --safe --without-K #-}

-- Truncated subtraction of cuts, x ∸ t, and the tests x ↦ x ∸ t and x ↦ t ∸ x.
--   * `monus x t` is x − t when t ≤ x and 0 otherwise (`monus-add`, `monus-zero`, `monus-+`);
--   * it respects ≈, is increasing in x and decreasing in t, so `subH t = monoH (_∸ t)` and `rsubH t = antiH (t ∸_)` are
--     tests by `MonoTest`.
-- Route: `LebesgueShiftCut.diffC t b` is b − t for t ⊑ b with t bounded by a rational; take b = x ⊔ t (the union of
-- the two lower cuts), so `monus x t = diffC t (x ⊔ t)`, or any other construction with the stated properties.
module QBS.Continuous.Monus where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_)
import Data.Rational.Unnormalised.Properties as P
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; :-_; _:=_)
open import QBS.Analysis.RationalLemmas
  using (ℚᵘ; 0ℚᵘ; ≃-refl; ≃-sym; <-irrefl; ≤-<-trans; ≤-≃; ≃-<ʳ; dense; add-sub; nat; nat-suc*; arch; lt-add;
         neg-or-nonneg; +-mono-<-≤; ≤-refl)
open import QBS.Analysis.LowerReals using (Cut; mk⊑; _⊑_; ⊑-refl)
open Cut using (mem; down; open′; neg)
open _⊑_ using (ap)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Continuous.LebesgueShiftCut using (module LebesgueShiftCut)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.MonoTest using (module MonoTest)

module Monus (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; 0#; refl; sym; trans; +-cong; +-comm; 0-least) renaming (Carrier to ∣A∣; _+_ to _⊕_)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open MonoTest lem₁ using (monoH; antiH)
  open LebesgueShiftCut (lemOf lem₁) using (diffC; diff-sum)
  open LebesgueShiftAlg (lemOf lem₁) using (bnd-rat; t≤x+t)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open BoundedCancel A half hh using (cancel-bnd)
  open QBS
  open Hom

  -- t is bounded by a rational
  BndQ : Cut → Set
  BndQ t = Σ ℚᵘ (λ M → ∀ r → mem t r → r < M)

  -- q ∈ x ∸ t: q < 0, or t is bounded and q′ + s ∈ x for some q′ > q and all s ∈ t
  MemM : Cut → Cut → ℚᵘ → Set
  MemM x t q = q < 0ℚᵘ ⊎ (BndQ t × Σ ℚᵘ (λ q′ → q < q′ × (∀ s → mem t s → mem x (q′ + s))))

  monusC : Cut → Cut → Cut
  monusC x t = record
    { mem = MemM x t
    ; down = λ le → [ (λ lt → inj₁ (≤-<-trans le lt)) , (λ (b , q′ , lt , h) → inj₂ (b , q′ , ≤-<-trans le lt , h)) ]′
    ; open′ = λ {p} → [ (λ lt → let q , a , c = dense lt in q , a , inj₁ c)
                      , (λ (b , q′ , lt , h) → let q , a , c = dense lt in q , a , inj₂ (b , q′ , c , h)) ]′
    ; neg = inj₁ }

  -- x ∸ t
  monus : ∣A∣ → ∣A∣ → ∣A∣
  monus = monusC

  monus-⊑ : ∀ {x x′ t t′} → x ⊑ x′ → t′ ⊑ t → monus x t ⊑ monus x′ t′
  monus-⊑ xx tt = mk⊑ (λ q → [ inj₁ , (λ ((M , bd) , q′ , lt , h) →
    inj₂ ((M , λ r mr → bd r (ap tt r mr)) , q′ , lt , λ s ms → ap xx _ (h s (ap tt s ms)))) ]′)

  monus-cong : ∀ {x x′ t t′} → x ≈ x′ → t ≈ t′ → monus x t ≈ monus x′ t′
  monus-cong (a , b) (c , d) = monus-⊑ a d , monus-⊑ b c

  monus-mono : ∀ {x x′} t → x ≤ x′ → monus x t ≤ monus x′ t
  monus-mono t h = monus-⊑ h ⊑-refl

  monus-anti : ∀ x {t t′} → t ≤ t′ → monus x t′ ≤ monus x t
  monus-anti x h = monus-⊑ ⊑-refl h

  -- for bounded t ⊑ b, b ∸ t is the difference of `LebesgueShiftCut`
  monus-diffC : ∀ t b (tb : t ⊑ b) → BndQ t → monus b t ≈ diffC t b tb
  monus-diffC t b tb bq = mk⊑ (λ q → [ neg (diffC t b tb) , (λ (_ , r) → r) ]′) , mk⊑ (λ q r → inj₂ (bq , r))

  monus-add : ∀ x t → Bnd t → t ≤ x → t ⊕ monus x t ≈ x
  monus-add x t bt tx = trans (+-cong refl (monus-diffC t x tx bq)) (diff-sum t x tx (proj₁ bq) (proj₂ bq))
    where bq = bnd-rat t bt

  monus-+ : ∀ x t → Bnd t → monus (x ⊕ t) t ≈ x
  monus-+ x t bt = cancel-bnd bt (trans (monus-add (x ⊕ t) t bt (t≤x+t x t)) (+-comm x t))

  -- if q′ + s ∈ t for all s ∈ t, then every p < k·q′ is in t
  closure : ∀ t q′ → (∀ s → mem t s → mem t (q′ + s)) → ∀ k p → p < nat k * q′ → mem t p
  closure t q′ f zero p lt = neg t (≃-<ʳ (P.*-zeroˡ q′) lt)
  closure t q′ f (suc k) p lt = down t (≤-≃ (≃-sym (add-sub q′ p))) (f _ (closure t q′ f k _ (step-lt p (nat k * q′) q′
    (≃-<ʳ (nat-suc* k q′) lt))))
    where
      step-lt : ∀ p a q → p < a + q → p + - q < a
      step-lt p a q h = ≃-<ʳ (solve 2 (λ a q → (a :+ q) :+ :- q := a) ≃-refl a q) (+-mono-<-≤ h (≤-refl { - q }))

  -- x ≤ t bounded: no q′ > 0 with q′ + s ∈ x for all s ∈ t
  no-shift : ∀ x t → x ≤ t → BndQ t → ∀ q′ → 0ℚᵘ < q′ → (∀ s → mem t s → mem x (q′ + s)) → ⊥
  no-shift x t xt (M , bd) q′ 0<q h =
    let k , Mk = arch M 0<q
        m = closure t q′ (λ s ms → ap xt _ (h s ms)) (suc k) (nat k * q′) (≃-<ˡ′ k)
    in <-irrefl ≃-refl (≤-<-trans Mk (bd _ m))
    where ≃-<ˡ′ = λ k → ≃-<ʳ (≃-sym (nat-suc* k q′)) (lt-add 0<q)

  monus-zero : ∀ x t → x ≤ t → monus x t ≈ 0#
  monus-zero x t xt = mk⊑ (λ q → [ (λ lt → lt) , (λ (b , q′ , lt , h) →
    [ (λ n → n) , (λ 0≤q → ⊥-elim (no-shift x t xt b q′ (P.≤-<-trans 0≤q lt) h)) ]′ (neg-or-nonneg q)) ]′) , 0-least

  -- x ↦ x ∸ t and x ↦ t ∸ x
  subH rsubH : ∣A∣ → Hom S WQ WQ
  subH t = monoH (λ x → monus x t) (λ e → monus-cong e refl) (monus-mono t)
  rsubH t = antiH (λ x → monus t x) (λ e → monus-cong refl e) (monus-anti t)
