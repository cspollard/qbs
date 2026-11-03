{-# OPTIONS --safe --without-K #-}

-- The Gaussian N(μ, s²) on the real line for every finite mean μ and scale s, and its mean (plan 03, "Translation and
-- products").  `gaussμ = mapPre (x ↦ x + μ) (GaussScale.gaussσ)` for μ ≥ 0 and `gaussμ⁻` with x ↦ x − μ, so
--   * `∫-gaussμ f : ∫ f dN(μ, s²) ≈ ∫ f(x + μ) dN(0, s²)` (`SFiniteIncl.ι-nat`, `SFinite.∫ᴹ-map`);
--   * the mean without subtraction: `mean : E[X⁺] ≈ μ + E[X⁻]` (X⁺ = `Xp`, X⁻ = `Xn` of `GaussReal`), and
--     `mean⁻ : μ + E[X⁺] ≈ E[X⁻]` for N(−μ, s²).
-- Route for `mean`: pointwise X⁺(y + μ) + X⁻(y) ≈ X⁺(y) + X⁻(y + μ) + μ on RQ (`shift-id`, by cases on y with
-- `RealShift.shift-inl`/`shift-inr-le`/`shift-inr-gt`), integrate (`UniquenessRQAlg.∫ᴹ-addX`), use the symmetry
-- E[X⁺] ≈ E[X⁻] under N(0, s²) (`sym-X`) and cancel the finite E[X⁻] (`fin-X`, `BoundedCancel.cancel-bnd`).
module QBS.Inference.GaussShift where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)

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
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealShift using (module RealShift)
open import QBS.Continuous.UniquenessRQAlg using (module UniquenessRQAlg)
open import QBS.Inference.GaussReal using (module GaussReal)
open import QBS.Inference.GaussScale using (module GaussScale)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealScale using (module RealScale)
open import QBS.Continuous.RealDensity using (module RealDensity)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Continuous.Monus using (module Monus)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Inference.Domination using (module Domination)
open import QBS.Continuous.RealShiftNull using (module RealShiftNull)

module GaussShift (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; +-comm; +-identityˡ; +-identityʳ;
    *-comm; *-identityʳ; distribʳ; +-assoc) renaming (Carrier to ∣A∣)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default (OmegaSemiring.commutativeSemiring A)
    using (solve; _:+_; _:*_; _:=_; con)
  open Bounded A using (Bnd; finite)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong; ∫ᴹ-map; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ι-nat)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open ExpDist lem₁ using (idW)
  open RealScale lem₁ using (reflRH; scaleRH)
  open RealDensity lem₁ using (module Sym)
  open GaussHalfLine lem₁ using (phiH)
  open GaussMoment lem₁ using (Z)
  open LebesgueShiftAlg (lemOf lem₁) using (total)
  open Monus lem₁ using (monus; monus-add)
  open Domination lem₁ using (Bnd-≤; Bnd-scale; ∫ᴹ-scale)
  open Intervals (lemOf lem₁) using (Ge)
  open RealShiftNull lem₁ using (toGe; toLe)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open BoundedCancel A half hh using (cancel-bnd)
  open SubSemiring using (Is-resp)
  open RealLine lem₁ using (RQ; inlH; inrH)
  open RealShift lem₁ using (shiftRH; shiftNegRH; shift-inr-le; shift-inr-gt)
  open UniquenessRQAlg (lemOf lem₁) using (addX; ∫ᴹ-addX)
  open GaussReal lem₁ using (Xp; Xn; n′; nn; zint; A1; bXn; gaussR; zeroW)
  open GaussScale lem₁ using (gaussσ; scDs; scD-int; gauss-dens)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open QBS
  open Hom

  module _ (s l : ∣A∣) (sl : s * l ≈ 1#) (sB : Bnd s) (lB : Bnd l) (μ : ∣A∣) (μB : Bnd μ) where

    N₀ : Pre RQ
    N₀ = gaussσ s l sl sB lB

    -- the density form of N(0, s²), and the Gaussian halves
    d : Hom S WQ WQ
    d = scDs s l sl sB lB phiH

    dens : ∀ (f : Hom S RQ WQ) → ∫ᴹ {RQ} (ιPre {RQ} N₀) f ≈ n′ * (∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S f inlH))
      + ∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S f inrH)))
    dens = gauss-dens s l sl sB lB

    -- symmetry and finiteness of the halves of the identity under N(0, s²)
    sym-X : ∫ᴹ {RQ} (ιPre {RQ} N₀) Xp ≈ ∫ᴹ {RQ} (ιPre {RQ} N₀) Xn
    sym-X = trans (dens Xp) (trans (*-cong (refl {n′}) (trans (+-comm _ _) (+-cong
      (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (_∘H_ S Xp inrH)} {mulH {WQ} d (_∘H_ S Xn inlH)} (λ x → refl))
      (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (_∘H_ S Xp inlH)} {mulH {WQ} d (_∘H_ S Xn inrH)} (λ x → refl)))))
      (sym (dens Xn)))

    -- the Gaussian halves of a test, and the test x ↦ X⁻(s x)
    RH : Hom S RQ WQ → ∣A∣
    RH g = n′ * (∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S g inlH)) + ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S g inrH)))

    X′ : Hom S RQ WQ
    X′ = _∘H_ S Xn (scaleRH s)

    X′-pt : ∀ x → map (mulH {WQ} phiH (_∘H_ S X′ inrH)) ⟨$⟩ x ≈ map (mulH {WQ} (constW {WQ} s) (mulH {WQ} phiH idW)) ⟨$⟩ x
    X′-pt x = solve 3 (λ p s x → p :* (s :* x) := s :* (p :* x)) refl (map phiH ⟨$⟩ x) s x

    RH-X′ : RH X′ ≈ n′ * (0# + s * A1)
    RH-X′ = *-cong (refl {n′}) (+-cong
      (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S X′ inlH)} {mulH {WQ} phiH zeroW} (λ x → refl)) zint)
      (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S X′ inrH)} {mulH {WQ} (constW {WQ} s) (mulH {WQ} phiH idW)} X′-pt)
        (∫ᴹ-scale lebPre s (mulH {WQ} phiH idW))))

    RH-Xn : RH Xn ≈ n′ * (0# + A1)
    RH-Xn = *-cong (refl {n′}) (+-cong
      (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S Xn inlH)} {mulH {WQ} phiH zeroW} (λ x → refl)) zint)
      (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S Xn inrH)} {mulH {WQ} phiH idW} (λ x → refl)))

    alg-X : n′ * (0# + s * A1) ≈ s * (n′ * (0# + A1))
    alg-X = solve 3 (λ n s a → n :* (con 0 :+ s :* a) := s :* (n :* (con 0 :+ a))) refl n′ s A1

    scale-X : ∫ᴹ {RQ} (ιPre {RQ} N₀) Xn ≈ s * RH Xn
    scale-X = trans (ι-nat {RQ} {RQ} (scaleRH s) gaussR Xn) (trans (∫ᴹ-map {RQ} {RQ} (scaleRH s) (ιPre {RQ} gaussR) Xn)
      (trans (Sym.∫-sym phiH Z refl n′ nn X′) (trans RH-X′ (trans alg-X (*-cong (refl {s}) (sym RH-Xn))))))

    fin-X : Bnd (∫ᴹ {RQ} (ιPre {RQ} N₀) Xn)
    fin-X = Is-resp finite (sym scale-X) (Bnd-scale sB bXn)

    -- N(μ, s²) and N(−μ, s²)
    gaussμ gaussμ⁻ : Pre RQ
    gaussμ = C.mapPre {RQ} {RQ} (shiftRH μ μB) N₀
    gaussμ⁻ = C.mapPre {RQ} {RQ} (shiftNegRH μ μB) N₀

    ∫-gaussμ : ∀ (f : Hom S RQ WQ) → ∫ᴹ {RQ} (ιPre {RQ} gaussμ) f ≈ ∫ᴹ {RQ} (ιPre {RQ} N₀) (_∘H_ S f (shiftRH μ μB))
    ∫-gaussμ f = trans (ι-nat {RQ} {RQ} (shiftRH μ μB) N₀ f) (∫ᴹ-map {RQ} {RQ} (shiftRH μ μB) (ιPre {RQ} N₀) f)

    ∫-gaussμ⁻ : ∀ (f : Hom S RQ WQ) →
      ∫ᴹ {RQ} (ιPre {RQ} gaussμ⁻) f ≈ ∫ᴹ {RQ} (ιPre {RQ} N₀) (_∘H_ S f (shiftNegRH μ μB))
    ∫-gaussμ⁻ f = trans (ι-nat {RQ} {RQ} (shiftNegRH μ μB) N₀ f) (∫ᴹ-map {RQ} {RQ} (shiftNegRH μ μB) (ιPre {RQ} N₀) f)

    -- the right-hand side of `shift-id` on the negative half, when X⁺ ∘ shift is a (resp. X⁻ ∘ shift is a)
    rhs-le : ∀ {a b : ∣A∣} → a ≈ 0# → b ≈ 0# → (0# + b) + μ ≈ μ
    rhs-le ea eb = trans (+-cong (+-cong (refl {0#}) eb) (refl {μ})) (trans (+-cong (+-identityˡ 0#) (refl {μ})) (+-identityˡ μ))

    rhs-gt : ∀ x → μ ≤ x → ∀ {b : ∣A∣} → b ≈ monus x μ → (0# + b) + μ ≈ x
    rhs-gt x μx eb = trans (+-cong (+-cong (refl {0#}) eb) (refl {μ})) (trans (+-cong (+-identityˡ (monus x μ)) (refl {μ}))
      (trans (+-comm _ _) (monus-add x μ μB μx)))

    -- X⁺(y + μ) + X⁻(y) = X⁺(y) + X⁻(y + μ) + μ on the negative half: x ≤ μ and μ ≤ x
    shift-id-le : ∀ x → Ge x μ → map (addX {RQ} (_∘H_ S Xp (shiftRH μ μB)) Xn) ⟨$⟩ inj₂ x
      ≈ (map (addX {RQ} Xp (_∘H_ S Xn (shiftRH μ μB))) ⟨$⟩ inj₂ x) + μ
    shift-id-le x g = trans (+-cong (Func.cong (map Xp) e) (refl {x})) (trans (+-comm _ _)
      (trans (monus-add μ x (Bnd-≤ xle μB) xle) (sym (rhs-le (refl {0#}) (Func.cong (map Xn) e)))))
      where xle = toLe {x} {μ} g
            e = shift-inr-le μ μB x xle

    shift-id-gt : ∀ x → (Ge x μ → ⊥) → map (addX {RQ} (_∘H_ S Xp (shiftRH μ μB)) Xn) ⟨$⟩ inj₂ x
      ≈ (map (addX {RQ} Xp (_∘H_ S Xn (shiftRH μ μB))) ⟨$⟩ inj₂ x) + μ
    shift-id-gt x n = trans (+-cong (Func.cong (map Xp) e) (refl {x})) (trans (+-identityˡ x)
      (sym (rhs-gt x μx (Func.cong (map Xn) e))))
      where e = shift-inr-gt μ μB x (λ xl → n (toGe xl))
            μx = [ (λ xl → ⊥-elim (n (toGe xl))) , (λ h → h) ]′ (total x μ)

    -- X⁺(y + μ) + X⁻(y) ≈ X⁺(y) + X⁻(y + μ) + μ
    shift-id : ∀ y → map (addX {RQ} (_∘H_ S Xp (shiftRH μ μB)) Xn) ⟨$⟩ y
      ≈ (map (addX {RQ} Xp (_∘H_ S Xn (shiftRH μ μB))) ⟨$⟩ y) + μ
    shift-id (inj₁ x) = trans (+-identityʳ _) (sym (+-cong (+-identityʳ x) (refl {μ})))
    shift-id (inj₂ x) = [ shift-id-le x , shift-id-gt x ]′ (lemOf lem₁ (Ge x μ))

    -- N(0, s²) has mass 1, and is symmetric
    half-c : ∀ c (h : Hom S WQ RQ) → ∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S (constW {RQ} c) h)) ≈ c * Z
    half-c c h = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (_∘H_ S (constW {RQ} c) h)} {mulH {WQ} (constW {WQ} c) d}
      (λ x → *-comm _ _)) (trans (∫ᴹ-scale lebPre c d) (*-cong (refl {c}) (scD-int s l sl sB lB phiH Z refl)))

    ∫-const : ∀ c → ∫ᴹ {RQ} (ιPre {RQ} N₀) (constW {RQ} c) ≈ c
    ∫-const c = trans (dens (constW {RQ} c)) (trans (*-cong (refl {n′}) (+-cong (half-c c inlH) (half-c c inrH)))
      (trans (solve 3 (λ n c z → n :* (c :* z :+ c :* z) := c :* ((z :+ z) :* n)) refl n′ c Z)
        (trans (*-cong (refl {c}) nn) (*-identityʳ c))))

    sym0 : ∀ (f : Hom S RQ WQ) → ∫ᴹ {RQ} (ιPre {RQ} N₀) (_∘H_ S f reflRH) ≈ ∫ᴹ {RQ} (ιPre {RQ} N₀) f
    sym0 f = trans (dens (_∘H_ S f reflRH)) (trans (*-cong (refl {n′}) (trans (+-cong
      (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (_∘H_ S (_∘H_ S f reflRH) inlH)} {mulH {WQ} d (_∘H_ S f inrH)} (λ x → refl))
      (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (_∘H_ S (_∘H_ S f reflRH) inrH)} {mulH {WQ} d (_∘H_ S f inlH)} (λ x → refl)))
      (+-comm _ _))) (sym (dens f)))

    Xp-refl : ∀ z → map Xp ⟨$⟩ (map reflRH ⟨$⟩ z) ≈ map Xn ⟨$⟩ z
    Xp-refl (inj₁ x) = refl {0#}
    Xp-refl (inj₂ x) = refl {x}

    Xn-refl : ∀ z → map Xn ⟨$⟩ (map reflRH ⟨$⟩ z) ≈ map Xp ⟨$⟩ z
    Xn-refl (inj₁ x) = refl {x}
    Xn-refl (inj₂ x) = refl {0#}

    -- E[X⁺(Y + μ)] = μ + E[X⁻(Y + μ)] under N(0, s²)
    P′ N′ : ∣A∣
    P′ = ∫ᴹ {RQ} (ιPre {RQ} N₀) (_∘H_ S Xp (shiftRH μ μB))
    N′ = ∫ᴹ {RQ} (ιPre {RQ} N₀) (_∘H_ S Xn (shiftRH μ μB))

    sum-id : P′ + ∫ᴹ {RQ} (ιPre {RQ} N₀) Xn ≈ (∫ᴹ {RQ} (ιPre {RQ} N₀) Xp + N′) + μ
    sum-id = trans (sym (∫ᴹ-addX {RQ} (ιPre {RQ} N₀) (_∘H_ S Xp (shiftRH μ μB)) Xn))
      (trans (∫ᴹ-cong {RQ} (ιPre {RQ} N₀) {addX {RQ} (_∘H_ S Xp (shiftRH μ μB)) Xn}
        {addX {RQ} (addX {RQ} Xp (_∘H_ S Xn (shiftRH μ μB))) (constW {RQ} μ)} shift-id)
        (trans (∫ᴹ-addX {RQ} (ιPre {RQ} N₀) (addX {RQ} Xp (_∘H_ S Xn (shiftRH μ μB))) (constW {RQ} μ))
          (+-cong (∫ᴹ-addX {RQ} (ιPre {RQ} N₀) Xp (_∘H_ S Xn (shiftRH μ μB))) (∫-const μ))))

    key : P′ ≈ μ + N′
    key = cancel-bnd fin-X (trans (+-comm _ _) (trans sum-id (trans (+-cong (+-cong sym-X (refl {N′})) (refl {μ}))
      (trans (+-assoc _ _ _) (+-cong (refl {∫ᴹ {RQ} (ιPre {RQ} N₀) Xn}) (+-comm _ _))))))

    -- E[X] = μ and E[X] = −μ, without subtraction
    mean : ∫ᴹ {RQ} (ιPre {RQ} gaussμ) Xp ≈ μ + ∫ᴹ {RQ} (ιPre {RQ} gaussμ) Xn
    mean = trans (∫-gaussμ Xp) (trans key (+-cong (refl {μ}) (sym (∫-gaussμ Xn))))

    mean⁻ : μ + ∫ᴹ {RQ} (ιPre {RQ} gaussμ⁻) Xp ≈ ∫ᴹ {RQ} (ιPre {RQ} gaussμ⁻) Xn
    mean⁻ = trans (+-cong (refl {μ}) (trans (∫-gaussμ⁻ Xp) (trans (∫ᴹ-cong {RQ} (ιPre {RQ} N₀) {_∘H_ S Xp (shiftNegRH μ μB)}
      {_∘H_ S (_∘H_ S Xn (shiftRH μ μB)) reflRH} (λ y → Xp-refl _)) (sym0 (_∘H_ S Xn (shiftRH μ μB))))))
      (trans (sym key) (sym (trans (∫-gaussμ⁻ Xn) (trans (∫ᴹ-cong {RQ} (ιPre {RQ} N₀) {_∘H_ S Xn (shiftNegRH μ μB)}
      {_∘H_ S (_∘H_ S Xp (shiftRH μ μB)) reflRH} (λ y → Xn-refl _)) (sym0 (_∘H_ S Xp (shiftRH μ μB)))))))
