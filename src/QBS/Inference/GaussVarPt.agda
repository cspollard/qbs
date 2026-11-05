{-# OPTIONS --safe --without-K #-}

-- Pointwise and N(0, s²) facts behind `GaussVar` (plan 03, "Information quantities"), for finite s, l (s l ≈ 1) and
-- finite μ ≥ 0.
--   * `Lq`: Q2 ∘ shift ∘ refl ∘ shift ≈ Q2 pointwise on RQ (so (x ↦ x − μ) ∘ (x ↦ x + μ) is the identity for Q2), by cases on
--     the point and on x ≤ μ with `Monus.monus-add`, `monus-zero`, `monus-+` and `BoundedCancel.cancel-bnd`;
--   * `sh≐`, `shn≐`: idT ∘ shift ≐ idT + μ and idT ∘ (x ↦ x − μ) ≐ idT − μ (`GaussShift.shift-id` and its mirror image);
--   * under N(0, s²): `ij0` (idT and idT² integrable), `e0` (E X ≃ 0, `sym-X`) and `v0` (Var X ≃ s², `second`).
-- Route: see `GaussVarAux` for the transfer along the shifts.
module QBS.Inference.GaussVarPt where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.AffineAlg using (module AlgAff)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealShift using (module RealShift)
open import QBS.Continuous.RealScale using (module RealScale)
open import QBS.Continuous.Monus using (module Monus)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Inference.Domination using (module Domination)
open import QBS.Inference.GaussReal using (module GaussReal)
open import QBS.Inference.GaussScale using (module GaussScale)
open import QBS.Inference.GaussShift using (module GaussShift)
open import QBS.Inference.GaussVarAux using (module GaussVarAux)

module GaussVarPt (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; +-comm; +-identityˡ;
    +-identityʳ; zeroˡ;
    ≤-trans; ≤-reflexive; ≤-+ʳ; ≤-antisym; commutativeSemiring) renaming (Carrier to ∣A∣)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring using (solve; _:+_; _:*_; _:=_; con)
  open Bounded A using (Bnd; Sg; _≃_; mk≃; finite; 0S; ι; -S_)
  open SubSemiring finite using (Is-0; Is-*)
  open AlgAff A using (var-core)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open BoundedCancel A half hh using (cancel-bnd)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open RealLine lem₁ using (RQ)
  open RealShift lem₁ using (shiftRH; shiftNegRH; shift-inl; shift-inr-le; shift-inr-gt)
  open RealScale lem₁ using (reflRH)
  open Monus lem₁ using (monus; monus-add; monus-zero; monus-+; monus-cong)
  open LebesgueShiftAlg (lemOf lem₁) using (total)
  open Domination lem₁ using (Bnd-≤)
  open Weights (lemOf lem₁) using (constW)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _≐_; _+T_; _*T_; _∘T_; constT; idT)
  open SignedExpect lem₁ using (Int; Ex; bnd≈)
  open SignedVar lem₁ using (Var; Int₂)
  open GaussReal lem₁ using (Q2; Xp; Xn)
  open GaussScale lem₁ using (second)
  open GaussShift lem₁ using (N₀; gaussμ; gaussμ⁻; ∫-gaussμ; ∫-gaussμ⁻; fin-X; sym-X; shift-id; Xp-refl; Xn-refl; ∫-const)
  open GaussVarAux lem₁ using (idT-norm; sq-pos; sq-neg)
  open QBS
  open Hom

  module _ (s l : ∣A∣) (sl : s * l ≈ 1#) (sB : Bnd s) (lB : Bnd l) (μ : ∣A∣) (μB : Bnd μ) where
    -- Q2 is invariant under reflection, and x ↦ (x − μ) ∘ (x ↦ x + μ) is the identity for it
    Q2-refl : ∀ v → map Q2 ⟨$⟩ (map reflRH ⟨$⟩ v) ≈ map Q2 ⟨$⟩ v
    Q2-refl (inj₁ x) = refl
    Q2-refl (inj₂ x) = refl

    private
      sh = shiftRH μ μB
      q2 = Func.cong (map Q2)
      shc = Func.cong (map sh)
      rfc = Func.cong (map reflRH)

    Lq-l : ∀ x → map Q2 ⟨$⟩ (map sh ⟨$⟩ (map reflRH ⟨$⟩ (map sh ⟨$⟩ inj₁ x))) ≈ x * x
    Lq-l x = trans (q2 (shc (rfc (shift-inl μ μB x)))) (go (lem₁ (x + μ ≤ μ)))
      where
        go : ((x + μ ≤ μ) ⊎ ((x + μ ≤ μ) → ⊥)) → map Q2 ⟨$⟩ (map sh ⟨$⟩ inj₂ (x + μ)) ≈ x * x
        go (inj₁ le) = trans (q2 (shift-inr-le μ μB (x + μ) le)) (trans (*-cong m0 m0) (sym (*-cong x0 x0)))
          where m0 = monus-zero μ (x + μ) (≤-trans (≤-+ʳ {μ} {x}) (≤-reflexive (+-comm μ x)))
                x0 = cancel-bnd μB (≤-antisym
                       (≤-trans (≤-reflexive (+-comm μ x)) (≤-trans le (≤-reflexive (sym (+-identityʳ μ)))))
                       (≤-trans (≤-reflexive (+-identityʳ μ)) (≤-+ʳ {μ} {x})))
        go (inj₂ n) = trans (q2 (shift-inr-gt μ μB (x + μ) n)) (*-cong (monus-+ x μ μB) (monus-+ x μ μB))

    Lq-r : ∀ x → map Q2 ⟨$⟩ (map sh ⟨$⟩ (map reflRH ⟨$⟩ (map sh ⟨$⟩ inj₂ x))) ≈ x * x
    Lq-r x = go (lem₁ (x ≤ μ))
      where
        go : ((x ≤ μ) ⊎ ((x ≤ μ) → ⊥)) → map Q2 ⟨$⟩ (map sh ⟨$⟩ (map reflRH ⟨$⟩ (map sh ⟨$⟩ inj₂ x))) ≈ x * x
        go (inj₁ le) = trans (q2 (shc (rfc (shift-inr-le μ μB x le)))) (trans (q2 (shift-inr-le μ μB m mle))
          (*-cong (sym k) (sym k)))
          where m = monus μ x
                bx = Bnd-≤ le μB
                mx : m + x ≈ μ
                mx = trans (+-comm m x) (monus-add μ x bx le)
                mle : m ≤ μ
                mle = ≤-trans (≤-+ʳ {m} {x}) (≤-reflexive mx)
                bm = Bnd-≤ mle μB
                k : x ≈ monus μ m
                k = cancel-bnd bm (trans mx (sym (monus-add μ m bm mle)))
        go (inj₂ n) = trans (q2 (shc (rfc (shift-inr-gt μ μB x n)))) (trans (q2 (shift-inl μ μB (monus x μ)))
          (*-cong (trans (+-comm _ _) (monus-add x μ μB μx)) (trans (+-comm _ _) (monus-add x μ μB μx))))
          where μx = [ (λ xl → ⊥-elim (n xl)) , (λ h → h) ]′ (total x μ)

    Lq : ∀ z → map Q2 ⟨$⟩ (map sh ⟨$⟩ (map reflRH ⟨$⟩ (map sh ⟨$⟩ z))) ≈ map Q2 ⟨$⟩ z
    Lq (inj₁ x) = Lq-l x
    Lq (inj₂ x) = Lq-r x

    cvar : ∫ᴹ {RQ} (ιPre {RQ} (gaussμ s l sl sB lB μ μB)) (_∘H_ S Q2 (shiftNegRH μ μB)) ≈ s * s
    cvar = trans (∫-gaussμ s l sl sB lB μ μB (_∘H_ S Q2 (shiftNegRH μ μB)))
      (trans (∫ᴹ-cong {RQ} (ιPre {RQ} (N₀ s l sl sB lB μ μB)) {_∘H_ S (_∘H_ S Q2 (shiftNegRH μ μB)) sh} {Q2}
        (λ y → trans (Q2-refl (map sh ⟨$⟩ (map reflRH ⟨$⟩ (map sh ⟨$⟩ y)))) (Lq y))) (second s l sl sB lB))

    cvar⁻ : ∫ᴹ {RQ} (ιPre {RQ} (gaussμ⁻ s l sl sB lB μ μB)) (_∘H_ S Q2 sh) ≈ s * s
    cvar⁻ = trans (∫-gaussμ⁻ s l sl sB lB μ μB (_∘H_ S Q2 sh))
      (trans (∫ᴹ-cong {RQ} (ιPre {RQ} (N₀ s l sl sB lB μ μB)) {_∘H_ S (_∘H_ S Q2 sh) (shiftNegRH μ μB)} {Q2}
        (λ y → trans (Lq (map reflRH ⟨$⟩ y)) (Q2-refl y))) (second s l sl sB lB))

    -- idT against the positive and negative parts Xp, Xn of GaussReal
    idp : ∀ w → at⁺ idT w ≈ map Xp ⟨$⟩ w
    idp (inj₁ x) = refl
    idp (inj₂ x) = refl

    idn : ∀ w → at⁻ idT w ≈ map Xn ⟨$⟩ w
    idn (inj₁ x) = refl
    idn (inj₂ x) = refl

    -- idT ∘ (x ↦ x + μ) ≐ idT + μ, and idT ∘ (x ↦ x − μ) ≐ idT − μ
    sh≐ : (idT ∘T sh) ≐ (idT +T constT (ι μB))
    sh≐ y = trans (+-cong (idp (map sh ⟨$⟩ y)) (trans (+-identityʳ _) (idn y)))
      (trans (shift-id s l sl sB lB μ μB y)
        (trans (solve 3 (λ a b m → (a :+ b) :+ m := (a :+ m) :+ b) refl (map Xp ⟨$⟩ y) (map Xn ⟨$⟩ (map sh ⟨$⟩ y)) μ)
          (+-cong (+-cong (sym (idp y)) refl) (sym (idn (map sh ⟨$⟩ y))))))

    shn≐ : (idT ∘T shiftNegRH μ μB) ≐ (idT +T constT (-S (ι μB)))
    shn≐ y = trans (+-cong (trans (idp (map reflRH ⟨$⟩ v)) (Xp-refl s l sl sB lB μ μB v)) (+-cong (idn y) (refl {μ})))
      (trans (solve 3 (λ a b m → a :+ (b :+ m) := (b :+ a) :+ m) refl (map Xn ⟨$⟩ v) (map Xn ⟨$⟩ y) μ)
        (trans (sym E) (trans (solve 2 (λ a b → a :+ b := (b :+ con 0) :+ a) refl (map Xp ⟨$⟩ v) (map Xp ⟨$⟩ y))
          (+-cong (+-cong (sym (idp y)) refl) (sym (trans (idn (map reflRH ⟨$⟩ v)) (Xn-refl s l sl sB lB μ μB v)))))))
      where w0 = map reflRH ⟨$⟩ y
            v = map sh ⟨$⟩ w0
            E : (map Xp ⟨$⟩ v) + (map Xp ⟨$⟩ y) ≈ ((map Xn ⟨$⟩ y) + (map Xn ⟨$⟩ v)) + μ
            E = trans (+-cong refl (sym (Xn-refl s l sl sB lB μ μB y))) (trans (shift-id s l sl sB lB μ μB w0)
              (+-cong (+-cong (Xp-refl s l sl sB lB μ μB y) refl) refl))

    -- under N(0, s²): idT and idT² are integrable, E X ≃ 0 and Var X ≃ s²
    private
      E0 = ιPre {RQ} (N₀ s l sl sB lB μ μB)
      ss = Is-* sB sB

    idp-int : ∫ᴹ {RQ} E0 (posT idT) ≈ ∫ᴹ {RQ} E0 Xn
    idp-int = trans (∫ᴹ-cong {RQ} E0 {posT idT} {Xp} idp) (sym-X s l sl sB lB μ μB)

    idn-int : ∫ᴹ {RQ} E0 (negT idT) ≈ ∫ᴹ {RQ} E0 Xn
    idn-int = ∫ᴹ-cong {RQ} E0 {negT idT} {Xn} idn

    sqp : ∫ᴹ {RQ} E0 (posT (idT *T idT)) ≈ s * s
    sqp = trans (∫ᴹ-cong {RQ} E0 {posT (idT *T idT)} {Q2} sq-pos) (second s l sl sB lB)

    sqn : ∫ᴹ {RQ} E0 (negT (idT *T idT)) ≈ 0#
    sqn = trans (∫ᴹ-cong {RQ} E0 {negT (idT *T idT)} {constW {RQ} 0#} sq-neg) (∫-const s l sl sB lB μ μB 0#)

    ij0 : Int₂ {RQ} (N₀ s l sl sB lB μ μB) idT
    ij0 = (bnd≈ {RQ} idp-int (fin-X s l sl sB lB μ μB) , bnd≈ {RQ} idn-int (fin-X s l sl sB lB μ μB))
        , (bnd≈ {RQ} sqp ss , bnd≈ {RQ} sqn Is-0)

    e0 : Ex E0 idT (proj₁ ij0) ≃ 0S
    e0 = mk≃ (∫ᴹ {RQ} E0 Xn) (fin-X s l sl sB lB μ μB)
      (+-cong (trans (trans (+-identityʳ _) (trans idp-int (sym idn-int))) (sym (+-identityˡ _))) refl)

    e2 : Ex E0 (idT *T idT) (proj₂ ij0) ≃ ι ss
    e2 = mk≃ 0# Is-0 (+-cong (trans (+-identityʳ _) (trans sqp (trans (sym (+-identityʳ _)) (+-cong refl (sym sqn))))) refl)

    v0 : Var (N₀ s l sl sB lB μ μB) idT ij0 ≃ ι ss
    v0 = var-core Is-0 ss ss (sym (trans (+-cong refl (zeroˡ 0#)) (+-identityʳ _))) _ _ e0 e2
