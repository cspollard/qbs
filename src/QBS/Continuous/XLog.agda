{-# OPTIONS --safe --without-K #-}

-- The pointwise inequalities behind Gibbs' inequality (plan 03, "Information quantities", helper for `KLDiv`).
--   * `small` : for x ≤ 1, x + x log⁻ x ≤ 1 (so x log⁻ x ≤ 1);
--   * `big` : for 1 ≤ x, x ≤ x log⁺ x + 1.
-- Route: `small` by cases on `PosQ x`: `LogNeg.UD` gives x · e^{log⁻ x} ≈ e^{log⁺ x} = 1 and 1 + y ≤ e^y (`1+≤expC`)
-- bounds x (1 + y); otherwise x ≈ 0.  `big` by cases on `BndQ x`: with y = log⁺ x, e^y ≈ x (`logP-ge`), and either
-- y ≤ 1, where e^y ≤ 1 + (y + y²) (`expC≤quad`) and 1 + y ≤ e^y give x ≤ 1 + (1 + y) y ≤ 1 + x y, or 1 ≤ y and
-- x ≤ x y; if x is unbounded then 1 ≤ log⁺ x, since every e^1 element is below 3 (`LogRat.E-hi`).
module QBS.Continuous.XLog where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (case_of_)
open import Data.Rational.Unnormalised.Base using (_<_; _≤_; _+_; _*_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.RationalLemmas using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; 0<1; ≤-refl; ≤-<-trans; pos-or-nonpos; <-≤-trans; ≤-or->)
open import QBS.Analysis.LowerReals using (Cut; _⊑_; _≋_; oneC; zeroC; mk⊑)
open Cut using (mem; open′)
open _⊑_ using (ap)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC; expC≤quad; expC-cong; expC-zero)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Continuous.MonusAlg using (module MonusAlg)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.LogNeg using (module LogNeg)
open import QBS.Continuous.LogRat using (module LogRat)

module XLog (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; refl; sym; trans; +-cong; *-cong; +-comm; *-comm; *-identityʳ; *-identityˡ;
    +-identityˡ; zeroˡ; ≤-trans; ≤-reflexive; ≤-+ʳ; +-mono; *-mono; distribˡ; distribʳ; 0-least)
  open OmegaSemiring A using () renaming (_≤_ to _≤ᶜ_; _+_ to _+ᶜ_; _*_ to _*ᶜ_; 0# to 0ᶜ; 1# to 1ᶜ)
  open MonusAlg lem₁ using (cut-total)
  open SignedLog lem₁ using (logP; logN; PosQ; logP-le; logN-ge; logP-ge)
  open LogRat (lemOf lem₁) using (E-hi)
  module LN = LogNeg (lemOf lem₁)
  eC = expC (lemOf lem₁)

  -- a cut with no positive rational is below 0
  nonpos : ∀ x → (PosQ x → ⊥) → x ≤ᶜ 0ᶜ
  nonpos x np = mk⊑ f
    where
      f : ∀ q → mem x q → mem zeroC q
      f q m with open′ x m
      ... | q′ , q<q′ , mq′ with pos-or-nonpos q′
      ...   | inj₁ 0<q′ = ⊥-elim (np (q′ , 0<q′ , mq′))
      ...   | inj₂ q′≤0 = <-≤-trans q<q′ q′≤0

  small : ∀ x → x ≤ᶜ 1ᶜ → x +ᶜ x *ᶜ logN x ≤ᶜ 1ᶜ
  small x xo = small′ x xo (lemOf lem₁ (PosQ x))
    where
      small′ : ∀ x → x ≤ᶜ 1ᶜ → (PosQ x ⊎ (PosQ x → ⊥)) → x +ᶜ x *ᶜ logN x ≤ᶜ 1ᶜ
      small′ x xo (inj₁ px) = ≤-trans (≤-reflexive (sym (trans (distribˡ x 1ᶜ (logN x)) (+-cong (*-identityʳ x) refl))))
        (≤-trans (*-mono x (1+≤expC (lemOf lem₁) (logN x)))
          (≤-reflexive (trans ud (trans (expC-cong (lemOf lem₁) lp) (expC-zero (lemOf lem₁))))))
        where
          ud = LN.UD {x} px (1ℚᵘ , λ r m → ap xo r m)
          lp = logP-le x xo
      small′ x xo (inj₂ np) = ≤-trans (+-mono nz (≤-trans (≤-reflexive (*-comm x (logN x))) (≤-trans (*-mono (logN x) nz)
        (≤-reflexive (trans (*-comm (logN x) 0ᶜ) (zeroˡ (logN x))))))) (≤-trans (≤-reflexive (+-identityˡ 0ᶜ)) 0-least)
        where nz = nonpos x np

  -- x ≤ x y ≤ x y + 1 once 1 ≤ y
  big1 : ∀ x → 1ᶜ ≤ᶜ logP x → x ≤ᶜ x *ᶜ logP x +ᶜ 1ᶜ
  big1 x oy = ≤-trans (≤-reflexive (sym (*-identityʳ x))) (≤-trans (*-mono x oy) (≤-+ʳ {x *ᶜ logP x} {1ᶜ}))

  -- the bounded case, y = log⁺ x ≤ 1
  big2 : ∀ x → 1ᶜ ≤ᶜ x → BndQ x → logP x ≤ᶜ 1ᶜ → x ≤ᶜ x *ᶜ logP x +ᶜ 1ᶜ
  big2 x ox bx y1 = ≤-trans (≤-reflexive (sym ex)) (≤-trans (expC≤quad (lemOf lem₁) y1)
    (≤-trans (≤-reflexive (+-cong refl (sym (trans (distribˡ y 1ᶜ y) (+-cong (*-identityʳ y) refl)))))
    (≤-trans (+-mono (≤-reflexive refl) (*-mono y (1+≤expC (lemOf lem₁) y)))
    (≤-trans (+-mono (≤-reflexive refl) (≤-reflexive (*-cong refl ex)))
    (≤-reflexive (trans (+-cong refl (*-comm y x)) (+-comm 1ᶜ (x *ᶜ y))))))))
    where
      y = logP x
      ex = logP-ge x ox bx

  -- an unbounded x has 1 ≤ log⁺ x
  unb : ∀ x → (BndQ x → ⊥) → 1ᶜ ≤ᶜ logP x
  unb x nb = mk⊑ (λ q q<1 → f q q<1 (lemOf lem₁ (Σ ℚᵘ (λ s → mem x s × (s < M → ⊥)))))
    where
      M = 1ℚᵘ + (1ℚᵘ + 1ℚᵘ * 1ℚᵘ)
      ge : ∀ {s} → (s < M → ⊥) → M ≤ s
      ge {s} ns = case ≤-or-> M s of λ { (inj₁ h) → h ; (inj₂ h) → ⊥-elim (ns h) }
      go : ∀ r → mem x r → (r < M ⊎ (r < M → ⊥)) → (Σ ℚᵘ (λ s → mem x s × (s < M → ⊥)) → ⊥) → r < M
      go r mr (inj₁ h) none = h
      go r mr (inj₂ h) none = ⊥-elim (none (r , mr , h))
      f : ∀ q → mem oneC q → (Σ ℚᵘ (λ s → mem x s × (s < M → ⊥)) ⊎ (Σ ℚᵘ (λ s → mem x s × (s < M → ⊥)) → ⊥)) → mem (logP x) q
      f q q<1 (inj₁ (s , ms , ns)) = inj₂ (1ℚᵘ , q<1 , s , ms , λ t mt → <-≤-trans (E-hi 0<1 ≤-refl t mt) (ge ns))
      f q q<1 (inj₂ none) = ⊥-elim (nb (M , λ r mr → go r mr (lemOf lem₁ (r < M)) none))

  big : ∀ x → 1ᶜ ≤ᶜ x → x ≤ᶜ x *ᶜ logP x +ᶜ 1ᶜ
  big x ox = big′ (lemOf lem₁ (BndQ x))
    where
      big′ : (BndQ x ⊎ (BndQ x → ⊥)) → x ≤ᶜ x *ᶜ logP x +ᶜ 1ᶜ
      big′ (inj₂ nb) = big1 x (unb x nb)
      big′ (inj₁ bx) = big″ (cut-total (logP x) 1ᶜ)
        where
          big″ : (logP x ≤ᶜ 1ᶜ ⊎ 1ᶜ ≤ᶜ logP x) → x ≤ᶜ x *ᶜ logP x +ᶜ 1ᶜ
          big″ (inj₁ y1) = big2 x ox bx y1
          big″ (inj₂ oy) = big1 x oy
