{-# OPTIONS --safe --without-K #-}

-- Scaled symmetric distributions on the real line, and N(0, s²) (plan 03, "Tests and the real line").
-- For s, l finite with s l ≈ 1 (l = 1/s):
--   * `push-sym`: the pushforward of `RealDensity.Sym.symDist d` along x ↦ s x (`RealScale.scaleRH s`) integrates every
--     test like the symmetric distribution with the scaled density `scD d = y ↦ l d(l y)` (`ScaleDensity.scD`), with the
--     same mass c (`scD-int`) and normaliser n;
--   * `gaussσ = mapPre (scaleRH s) gaussR`, the Gaussian of standard deviation s, with its density form (`gauss-dens`)
--     and second moment `second : ∫ x² dN(0, s²) ≈ s²`.
-- Route for `push-sym`: `SFiniteIncl.ι-nat` and `SFinite.∫ᴹ-map` move the scaling into the test, `Sym.∫-sym` gives two
-- half-line integrals, and on each half ∫ d(x) f(s x) dx = s ∫ l d(l s x) f(s x) dx = ∫ l d(l y) f(y) dy
-- (`LebesgueScale.∫-scale`, as in `ScaleDensity.push-dens`).  `second`: x² ∘ (s ·) = s² x² and `GaussReal.sqint`.
module QBS.Inference.GaussScale where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealDensity using (module RealDensity)
open import QBS.Continuous.RealScale using (module RealScale)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.LebesgueScale using (module LebesgueScale)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.ExpDistSq using (module ExpDistSq)
open import QBS.Inference.Domination using (module Domination)
open import QBS.Inference.ScaleDensity using (module ScaleDensity)
open import QBS.Inference.GaussReal using (module GaussReal)

module GaussScale (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#; refl; sym; trans; *-cong; +-cong; *-assoc; *-identityˡ; *-identityʳ)
    renaming (Carrier to ∣A∣)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default (OmegaSemiring.commutativeSemiring A)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong; ∫ᴹ-map; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ι-nat)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open RealLine lem₁ using (RQ; inlH; inrH)
  open RealDensity lem₁ using (module Sym)
  open RealScale lem₁ using (scaleRH)
  open GaussHalfLine lem₁ using (phiH)
  open GaussMoment lem₁ using (Z)
  open ScaleDensity lem₁ using (scD; scD-pt; lc)
  open HalfLineRate lem₁ using (scaleH; ∫-scaleH)
  open LebesgueScale lem₁ using (∫-scale)
  open ExpDist lem₁ using (idW)
  open ExpDistSq lem₁ using (sqW)
  open Domination lem₁ using (∫ᴹ-scale)
  open Weights (lemOf lem₁) using (constW)
  open GaussReal lem₁ using (gaussR; n′; Q2; nn; sqint)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open QBS
  open Hom

  module _ (s l : ∣A∣) (sl : s * l ≈ 1#) (sB : Bnd s) (lB : Bnd l) where

    -- the density y ↦ l d(l y) of the scaled variable
    scDs : Hom S WQ WQ → Hom S WQ WQ
    scDs = scD s l sl sB lB

    -- ∫ d(x) k(x) dx ≈ ∫ (scD d) g, when k = g ∘ (s ·) pointwise
    half : ∀ (d g k : Hom S WQ WQ) → (∀ x → map k ⟨$⟩ x ≈ map g ⟨$⟩ (s * x)) →
      ∫ᴹ {WQ} lebPre (mulH {WQ} d k) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} (scDs d) g)
    half d g k e = trans (sym (*-identityˡ _)) (trans (*-cong (sym sl) refl) (trans (*-assoc s l _)
      (trans (*-cong refl (sym (∫-scaleH l (mulH {WQ} d k))))
        (trans (*-cong refl (∫ᴹ-cong {WQ} lebPre {scaleH l (mulH {WQ} d k)}
                               {_∘H_ S (mulH {WQ} (scDs d) g) (scaleH s idW)}
          (λ x → sym (trans (*-cong (scD-pt s l sl sB lB d x) (sym (e x))) (*-assoc l _ _)))))
          (∫-scale s l sl sB lB (mulH {WQ} (scDs d) g))))))

    scD-int : ∀ (d : Hom S WQ WQ) c → ∫ᴹ {WQ} lebPre d ≈ c → ∫ᴹ {WQ} lebPre (scDs d) ≈ c
    scD-int d c hc = trans (∫-scaleH l (_∘H_ S d (scaleH l idW))) (trans (∫-scale l s lc′ lB sB d) hc)
      where lc′ = lc s l sl sB lB

    push-sym : ∀ (d : Hom S WQ WQ) c (hc : ∫ᴹ {WQ} lebPre d ≈ c) n (nn : (c + c) * n ≈ 1#) (f : Hom S RQ WQ) →
      ∫ᴹ {RQ} (ιPre {RQ} (C.mapPre {RQ} {RQ} (scaleRH s) (Sym.symDist d c hc n nn))) f
        ≈ ∫ᴹ {RQ} (ιPre {RQ} (Sym.symDist (scDs d) c (scD-int d c hc) n nn)) f
    push-sym d c hc n nn′ f = trans (ι-nat {RQ} {RQ} (scaleRH s) (Sym.symDist d c hc n nn′) f)
      (trans (∫ᴹ-map {RQ} {RQ} (scaleRH s) (ιPre {RQ} (Sym.symDist d c hc n nn′)) f)
        (trans (Sym.∫-sym d c hc n nn′ (_∘H_ S f (scaleRH s)))
          (trans (*-cong refl (+-cong (half d (_∘H_ S f inlH) _ (λ x → refl)) (half d (_∘H_ S f inrH) _ (λ x → refl))))
            (sym (Sym.∫-sym (scDs d) c (scD-int d c hc) n nn′ f)))))

    -- the Gaussian with standard deviation s
    gaussσ : Pre RQ
    gaussσ = C.mapPre {RQ} {RQ} (scaleRH s) gaussR

    gauss-dens : ∀ (f : Hom S RQ WQ) → ∫ᴹ {RQ} (ιPre {RQ} gaussσ) f
      ≈ n′ * (∫ᴹ {WQ} lebPre (mulH {WQ} (scDs phiH) (_∘H_ S f inlH))
            + ∫ᴹ {WQ} lebPre (mulH {WQ} (scDs phiH) (_∘H_ S f inrH)))
    gauss-dens f = trans (push-sym phiH Z refl n′ nn f) (Sym.∫-sym (scDs phiH) Z (scD-int phiH Z refl) n′ nn f)

    sq2 : ∀ a x → (a * a) * (x * x) ≈ (a * x) * (a * x)
    sq2 = solve 2 (λ a x → (a :* a) :* (x :* x) := (a :* x) :* (a :* x)) refl

    cm : ∀ p a x → p * ((a * a) * (x * x)) ≈ (a * a) * (p * (x * x))
    cm = solve 3 (λ p a x → p :* ((a :* a) :* (x :* x)) := (a :* a) :* (p :* (x :* x))) refl

    -- ∫ x² (scD φ)(x) dx ≈ s² Z
    sqhalf : ∀ (g : Hom S WQ WQ) → (∀ x → map g ⟨$⟩ x ≈ x * x) →
      ∫ᴹ {WQ} lebPre (mulH {WQ} (scDs phiH) g) ≈ (s * s) * Z
    sqhalf g e = trans (sym (half phiH g k (λ x → trans (sq2 s x) (sym (e (s * x))))))
      (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH k} {mulH {WQ} (constW (s * s)) (mulH {WQ} phiH sqW)}
                (λ x → cm (map phiH ⟨$⟩ x) s x))
        (trans (∫ᴹ-scale lebPre (s * s) (mulH {WQ} phiH sqW)) (*-cong refl sqint)))
      where k = mulH {WQ} (constW (s * s)) sqW

    fin : ∀ a z n → n * ((a * z) + (a * z)) ≈ a * ((z + z) * n)
    fin = solve 3 (λ a z n → n :* ((a :* z) :+ (a :* z)) := a :* ((z :+ z) :* n)) refl

    second : ∫ᴹ {RQ} (ιPre {RQ} gaussσ) Q2 ≈ s * s
    second = trans (gauss-dens Q2) (trans (*-cong refl (+-cong (sqhalf (_∘H_ S Q2 inlH) (λ x → refl))
      (sqhalf (_∘H_ S Q2 inrH) (λ x → refl)))) (trans (fin (s * s) Z n′) (trans (*-cong refl nn) (*-identityʳ _))))
