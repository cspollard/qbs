{-# OPTIONS --safe --without-K #-}

-- Markov's and Chebyshev's inequalities and the weak law of large numbers (plan 05 item 50 in `plans/`).  On a probability P on Ω:
--   * `a ≤ᵛ x`: a value a ∈ [0, ∞] below a signed value x, cross-added (a + x⁻ ≤ x⁺); respects `≃` (`≤ᵛ-cong`);
--   * `geW c`, the indicator of [c, ∞] on [0, ∞] (1 when c ≤ x, 0 otherwise), monotone, so a test `geH c`
--     (`MonoTest.monoH`) with no measurability proof;
--   * Markov: c · ∫ χ ≤ ∫ h whenever c χ ≤ h pointwise (`markov`), in particular c · P{h ≥ c} ≤ E h (`markov-ge`);
--   * Chebyshev: for g with E g² finite and any test χ inside {(g − E g)² ≥ e²} (pointwise e² χ ≤ (g − E g)²,
--     cross-added), e² ∫ χ ≤ Var g (`chebyshev`);
--   * the weak law: for F : Fin n → SgT Ω with `SgMoments.Moments P n F μ σ²` and χ inside {(Sₙ − n μ)² ≥ e²},
--     e² ∫ χ ≤ n σ² (`weak-law`, take e = n ε: n² ε² P{|Sₙ − n μ| ≥ n ε} ≤ n σ²), and the rate form
--     n ε² ∫ χ ≤ σ² for χ inside {(Sₙ − n μ)² ≥ (n ε)²}, n ≥ 1 (`weak-law-rate`, P ≤ σ²/(n ε²)).
-- Only the moment hypotheses are used, so the law applies to every iid family (`IID.IID-moments`) and to uncorrelated
-- families.  Events are given by tests χ (a [0, 1]-valued χ is a sub-event); `geH` gives the indicator of {h ≥ c}.
-- Route: helpers in `WeakLawAlg` (order algebra, cancelling n via `Continuous/NatCancel`) and `WeakLawCheb` (Chebyshev about any
-- centre c ≃ E g).  `markov` is `SupTest.∫ᴹ-monoX` with `Product.cmul`; `geW` is the cut {q | q < 0, or c ≤ x and q < 1} (c ≤ x unfolded to
-- inclusion of the cuts, which lives in `Set`); `geW-0` is then direct, excluded middle is used in `markov-ge`; `chebyshev` is `SignedExpect.Ex-mono` on fromW (e² χ) and (g − E g)², then
-- `SignedVar.Var-cen`; `weak-law` is `chebyshev` at Sₙ with `SgSample.Ex-sum` (centre ≃ n μ, `SignedSq.sq-cong`) and
-- `SgSample.Var-sum`; `weak-law-rate` cancels the finite nonzero factor n (a helper on lower reals).
module QBS.Inference.WeakLaw where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Rational.Unnormalised.Base using () renaming (_<_ to _<ℚ_)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Analysis.LowerReals using (Cut; module Cut; _⊑_; mk⊑; module _⊑_)
open import QBS.Analysis.RationalLemmas using (0ℚᵘ; 1ℚᵘ; dense; ≤-<-trans; <-trans; 0<1)
open import QBS.Continuous.MonoTest using (module MonoTest)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SupTest using (module SupTest)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.Dominated using (module Dominated)
open import QBS.Inference.WeakLawAlg using (module WeakLawAlg)
open import QBS.Inference.WeakLawCheb using (module WeakLawCheb)
open import QBS.Continuous.SgSample using (module SgSample)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SgMoments using (module SgMoments)

open Cut using (mem)
open _⊑_ using (ap)

module WeakLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; *-identityʳ; zeroʳ; 0-least; ≤-trans; ≤-reflexive; ≤-refl; ≤-antisym)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Sg; _≃_; _*S_; nat; ≃-sym; ≃-refl)
  open Bounded.Sg A using (pos; neg)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open SupTest (lemOf lem₁) using (∫ᴹ-monoX)
  open Product (lemOf lem₁) using (cmul)
  open WeakLawAlg lem₁ using (cong-≤; rate-alg)
  open WeakLawCheb lem₁ using (chebyshev-at)
  open SgSample lem₁ using (Int₂-sum; Var-sum; Ex-sum)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open MonoTest lem₁ using (monoH)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _*T_)
  open SignedExpect lem₁ using (Ex)
  open SignedVar lem₁ using (Int₂; Var; cen)
  open SgMoments lem₁ using (natS; sumT; Moments)
  open QBS
  open Hom

  -- a value below a signed value
  infix 4 _≤ᵛ_
  _≤ᵛ_ : ∣A∣ → Sg → Set₁
  a ≤ᵛ x = a + neg x ≤ pos x

  ≤ᵛ-cong : ∀ {a x y} → a ≤ᵛ x → x ≃ y → a ≤ᵛ y
  ≤ᵛ-cong h e = cong-≤ h e

  -- the indicator of [c, ∞]
  geW : ∣A∣ → ∣A∣ → ∣A∣
  geW c x = record
    { mem = λ q → q <ℚ 0ℚᵘ ⊎ ((∀ r → mem c r → mem x r) × q <ℚ 1ℚᵘ)
    ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt) ; le (inj₂ (h , lt)) → inj₂ (h , ≤-<-trans le lt) }
    ; open′ = λ { (inj₁ lt) → let r , q<r , r<0 = dense lt in r , q<r , inj₁ r<0
                ; (inj₂ (h , lt)) → let r , q<r , r<1 = dense lt in r , q<r , inj₂ (h , r<1) }
    ; neg = inj₁ }

  geW-⊑ : ∀ c {x y} → x ≤ y → geW c x ≤ geW c y
  geW-⊑ c le = mk⊑ (λ q → [ inj₁ , (λ { (h , lt) → inj₂ ((λ r m → ap le r (h r m)) , lt) }) ]′)

  geW-cong : ∀ c {x y} → x ≈ y → geW c x ≈ geW c y
  geW-cong c (le , ge) = geW-⊑ c le , geW-⊑ c ge

  geW-mono : ∀ c {x y} → x ≤ y → geW c x ≤ geW c y
  geW-mono = geW-⊑

  geW-1 : ∀ {c x} → c ≤ x → geW c x ≈ 1#
  geW-1 h = mk⊑ (λ q → [ (λ lt → <-trans lt 0<1) , proj₂ ]′) , mk⊑ (λ q lt → inj₂ ((λ r m → ap h r m) , lt))

  geW-0 : ∀ {c x} → (c ≤ x → ⊥) → geW c x ≈ 0#
  geW-0 n = mk⊑ (λ q → [ (λ lt → lt) , (λ { (h , _) → ⊥-elim (n (mk⊑ h)) }) ]′) , mk⊑ (λ q lt → inj₁ lt)

  geH : ∣A∣ → Hom S WQ WQ
  geH c = monoH (geW c) (geW-cong c) (geW-mono c)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    -- the squared deviation (g − c)²
    dev : SgT Ω → Sg → SgT Ω
    dev g c = cen P g c *T cen P g c

    -- Markov
    markov : ∀ (h χ : Hom S Ω WQ) c → (∀ ω → c * (map χ ⟨$⟩ ω) ≤ map h ⟨$⟩ ω) →
      c * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ ∫ᴹ {Ω} (ιPre {Ω} P) h
    markov h χ c le = ≤-trans (≤-reflexive (sym (cmul {Ω} (ιPre {Ω} P) c χ)))
      (∫ᴹ-monoX (ιPre {Ω} P) {mulH {Ω} (constW {Ω} c) χ} {h} le)

    markov-ge : ∀ (h : Hom S Ω WQ) c → c * ∫ᴹ {Ω} (ιPre {Ω} P) (_∘H_ S (geH c) h) ≤ ∫ᴹ {Ω} (ιPre {Ω} P) h
    markov-ge h c = markov h (_∘H_ S (geH c) h) c pw
      where pw : ∀ ω → c * geW c (map h ⟨$⟩ ω) ≤ map h ⟨$⟩ ω
            pw ω with lem₁ (c ≤ (map h ⟨$⟩ ω))
            ... | inj₁ le = ≤-trans (≤-reflexive (trans (*-cong refl (geW-1 le)) (*-identityʳ c))) le
            ... | inj₂ n = ≤-trans (≤-reflexive (trans (*-cong refl (geW-0 n)) (zeroʳ c))) 0-least

    -- Chebyshev
    chebyshev : ∀ (g : SgT Ω) (ij : Int₂ P g) (χ : Hom S Ω WQ) e →
      (∀ ω → (e * e) * (map χ ⟨$⟩ ω) + at⁻ (dev g (Ex {Ω} (ιPre {Ω} P) g (proj₁ ij))) ω
        ≤ at⁺ (dev g (Ex {Ω} (ιPre {Ω} P) g (proj₁ ij))) ω) →
      (e * e) * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ᵛ Var P g ij
    chebyshev g ij χ e hyp = chebyshev-at P g ij χ e (Ex {Ω} (ιPre {Ω} P) g (proj₁ ij)) ≃-refl hyp

    -- the weak law of large numbers
    weak-law : ∀ n F μ σ² → Moments P n F μ σ² → ∀ (χ : Hom S Ω WQ) e →
      (∀ ω → (e * e) * (map χ ⟨$⟩ ω) + at⁻ (dev (sumT n F) (natS n *S μ)) ω ≤ at⁺ (dev (sumT n F) (natS n *S μ)) ω) →
      (e * e) * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ᵛ natS n *S σ²
    weak-law n F μ σ² M χ e hyp = ≤ᵛ-cong ch (Var-sum P n F μ σ² M)
      where ch : (e * e) * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ᵛ Var P (sumT n F) (Int₂-sum P n F μ σ² M)
            ch = chebyshev-at P (sumT n F) (Int₂-sum P n F μ σ² M) χ e (natS n *S μ) (≃-sym (Ex-sum P n F μ σ² M)) hyp

    weak-law-rate : ∀ m (F : Fin (suc m) → SgT Ω) μ σ² → Moments P (suc m) F μ σ² → ∀ (χ : Hom S Ω WQ) e →
      (∀ ω → ((nat (suc m) * e) * (nat (suc m) * e)) * (map χ ⟨$⟩ ω) + at⁻ (dev (sumT (suc m) F) (natS (suc m) *S μ)) ω
        ≤ at⁺ (dev (sumT (suc m) F) (natS (suc m) *S μ)) ω) →
      (nat (suc m) * (e * e)) * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ᵛ σ²
    weak-law-rate m F μ σ² M χ e hyp = rate-alg m e (∫ᴹ {Ω} (ιPre {Ω} P) χ) σ² (weak-law (suc m) F μ σ² M χ (nat (suc m) * e) hyp)
