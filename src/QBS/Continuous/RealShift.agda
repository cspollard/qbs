{-# OPTIONS --safe --without-K #-}

-- Translation of the whole real line `RQ = WQ +Q WQ` by a finite t ≥ 0, and translation invariance of `lebR`
-- (plan 03, "Translation and products").
--   * `shiftRH t : RQ ⇒ RQ`, x ↦ x + t: `inl x ↦ inl (x + t)`; `inr x ↦ inl (t ∸ x)` if x ≤ t, else `inr (x ∸ t)`
--     (`shift-inl`, `shift-inr-le`, `shift-inr-gt`; the case split is excluded middle);
--   * `∫-reflIv : ∫_{[0,t)} h(t ∸ x) dx ≈ ∫_{[0,t)} h` (reflection of an interval);
--   * `∫-shiftR : ∫ h(x + t) dx ≈ ∫ h` over the real line, and `shiftNegRH t = refl ∘ shift t ∘ refl` (x ↦ x − t) with
--     `∫-shiftNegR`.
-- Route for `shiftRH`: on a random element of RQ (glued from `inl ∘ α` and `inr ∘ β` pieces, `Colimits`), split the
-- `inr` pieces along the Borel set {r | β r ≤ t} (`LipTestAlg.le-borel`) and glue `inl ∘ rsubH t ∘ β` and
-- `inr ∘ subH t ∘ β` (`Monus`).  `∫-shiftR`: by `RealLine.∫ᴹ-lebR` the left side is
-- ∫ h(inl (x + t)) + ∫_{[0,t)} h(inl (t ∸ x)) + ∫_{[t,∞)} h(inr (x ∸ t)); the first two give ∫ h∘inl by `∫-reflIv` and
-- `LebesgueShift.∫-shift`, the last gives ∫ h∘inr by `∫-shift` (the point x = t is null).  `∫-reflIv`: the reflected
-- measure has the interval masses of Lebesgue measure on [0,t) (`LebesgueInterval.leb-unique`), or any other route.
-- Helpers: `RealShiftNull` (null points, splitting at t) and `RealShiftRefl` (`reflMeas`, reflection of [0,t)).
module QBS.Continuous.RealShift where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (lift)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; _×_)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealScale using (module RealScale)
open import QBS.Continuous.Monus using (module Monus)
open import QBS.Colimits using (Piece; ev; copair)
open import QBS.Borel.Core using (Pred; Partition; resp; compl; ⊥-borel; Borel)
open import QBS.Borel.Source using (idxₛ)
open import QBS.Continuous.LipTestAlg using (module LipAlg)
open import QBS.Continuous.LebesgueShift using (module LebesgueShift)
open import QBS.Continuous.RealShiftNull using (module RealShiftNull)
open import QBS.Continuous.RealShiftRefl using (module RealShiftRefl)
open import QBS.Analysis.Meas using (module Meas)

module RealShift (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; +-assoc; zeroˡ) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open RealLine lem₁ using (RQ; lebR)
  open RealScale lem₁ using (reflRH)
  open Monus lem₁ using (monus; monus-cong; rsubH; subH)
  open RealScale lem₁ using (∫-reflR)
  open RealLine lem₁ using (inlH; inrH; ∫ᴹ-lebR)
  open LipAlg lem₁ using (le-borel)
  open LebesgueShift lem₁ using (shiftH; ∫-shift)
  open RealShiftNull lem₁ using (I; leH; gtH; split; le-lt; gt-shift; toLe; toGe; Ge-resp)
  open RealShiftRefl lem₁ using () renaming (∫-reflIv to ∫-reflIv′)
  open Intervals (lemOf lem₁) using (Ge; χIv; tv-out)
  open RandomSource S using (Rˢ)
  open Meas (lemOf lem₁) using (Meas)
  open QBS
  open Hom

  -- equality of points of RQ
  infix 4 _≈ᴿ_
  _≈ᴿ_ : ∣ RQ ∣ → ∣ RQ ∣ → Set _
  _≈ᴿ_ = _≈ˣ_ RQ

  inl≈ : ∀ {a b : ∣A∣} → a ≈ b → _≈ᴿ_ (inj₁ a) (inj₁ b)
  inl≈ = ⊎ʳ.inj₁

  inr≈ : ∀ {a b : ∣A∣} → a ≈ b → _≈ᴿ_ (inj₂ a) (inj₂ b)
  inr≈ = ⊎ʳ.inj₂

  -- the glued translation on the inr half: x ↦ inl (t ∸ x) if x ≤ t, else inr (x ∸ t)
  Dec : ∣A∣ → ∣A∣ → Set
  Dec t x = Ge x t ⊎ (Ge x t → ⊥)

  dec : ∀ t x → Dec t x
  dec t x = lemOf lem₁ (Ge x t)

  pick : ∀ t x → Dec t x → ∣ RQ ∣
  pick t x (inj₁ _) = inj₁ (monus t x)
  pick t x (inj₂ _) = inj₂ (monus x t)

  pick-cong : ∀ t {x y} → x ≈ y → ∀ d e → pick t x d ≈ᴿ pick t y e
  pick-cong t e (inj₁ _) (inj₁ _) = inl≈ (monus-cong (refl {t}) e)
  pick-cong t {x} {y} e (inj₁ a) (inj₂ nb) = ⊥-elim (nb (Ge-resp {x} {y} {t} e a))
  pick-cong t {x} {y} e (inj₂ na) (inj₁ b) = ⊥-elim (na (Ge-resp {y} {x} {t} (sym e) b))
  pick-cong t e (inj₂ _) (inj₂ _) = inr≈ (monus-cong e (refl {t}))

  gFun : ∣A∣ → Func (Carrier WQ) (Carrier RQ)
  gFun t = record { to = λ x → pick t x (dec t x) ; cong = λ {x} {y} e → pick-cong t e (dec t x) (dec t y) }

  -- the index of the piece
  flg : ∀ {P : Set} → P ⊎ (P → ⊥) → ℕ
  flg (inj₁ _) = 0
  flg (inj₂ _) = 1

  flg-0 : ∀ {P : Set} (d : P ⊎ (P → ⊥)) → (P → flg d ≡ 0) × (flg d ≡ 0 → P)
  flg-0 (inj₁ p) = (λ _ → ≡.refl) , (λ _ → p)
  flg-0 (inj₂ np) = (λ p → ⊥-elim (np p)) , (λ ())

  flg-1 : ∀ {P : Set} (d : P ⊎ (P → ⊥)) → ((P → ⊥) → flg d ≡ 1) × (flg d ≡ 1 → P → ⊥)
  flg-1 (inj₁ p) = (λ np → ⊥-elim (np p)) , (λ ())
  flg-1 (inj₂ np) = (λ _ → ≡.refl) , (λ _ → np)

  flg-big : ∀ {P : Set} (d : P ⊎ (P → ⊥)) k → flg d ≡ suc (suc k) → ⊥
  flg-big (inj₁ _) k ()
  flg-big (inj₂ _) k ()

  flg-part : ∀ {U : Pred} → Borel U → (d : ∀ x → U x ⊎ (U x → ⊥)) → Partition (λ x → flg (d x))
  flg-part bU d zero = resp (λ x → flg-0 (d x)) bU
  flg-part bU d (suc zero) = resp (λ x → flg-1 (d x)) (compl bU)
  flg-part bU d (suc (suc k)) = resp (λ x → (λ ()) , flg-big (d x) k) ⊥-borel

  -- the pieces: t ∸ x on {x ≤ t} and x ∸ t on its complement
  pieces : ∀ t {α : Func Rˢ (Carrier WQ)} → Meas (α ⟨$⟩_) → ℕ → Piece S WQ WQ
  pieces t {α} m zero = inj₁ (map (rsubH t) ∘ₛ α , map-random (rsubH t) {α} m)
  pieces t {α} m (suc _) = inj₂ (map (subH t) ∘ₛ α , map-random (subH t) {α} m)

  pieces-ev : ∀ t {α : Func Rˢ (Carrier WQ)} (m : Meas (α ⟨$⟩_)) r d →
    pick t (α ⟨$⟩ r) d ≈ᴿ ev S WQ WQ (pieces t {α} m (flg d)) r
  pieces-ev t {α} m r (inj₁ _) = inl≈ (refl {monus t (α ⟨$⟩ r)})
  pieces-ev t {α} m r (inj₂ _) = inr≈ (refl {monus (α ⟨$⟩ r) t})

  gRand : ∀ t {α : Func Rˢ (Carrier WQ)} → Meas (α ⟨$⟩_) → QBS.Random RQ (gFun t ∘ₛ α)
  gRand t {α} m = idxₛ (λ r → flg (dec t (α ⟨$⟩ r))) pt , pt , pieces t {α} m , λ r → pieces-ev t {α} m r (dec t (α ⟨$⟩ r))
    where pt = flg-part (le-borel t m) (λ c → dec t (α ⟨$⟩ lift c))

  gH : ∣A∣ → Hom S WQ RQ
  gH t = record { map = gFun t ; map-random = λ {α} m → gRand t {α} m }

  pick-le : ∀ t x → x ≤ t → ∀ d → pick t x d ≈ᴿ inj₁ (monus t x)
  pick-le t x xt (inj₁ _) = inl≈ refl
  pick-le t x xt (inj₂ n) = ⊥-elim (n (toGe xt))

  pick-gt : ∀ t x → (x ≤ t → ⊥) → ∀ d → pick t x d ≈ᴿ inj₂ (monus x t)
  pick-gt t x nx (inj₁ a) = ⊥-elim (nx (toLe a))
  pick-gt t x nx (inj₂ _) = inr≈ refl

  module _ (t : ∣A∣) (bt : Bnd t) where

    -- x ↦ x + t
    shiftRH : Hom S RQ RQ
    shiftRH = copair S (_∘H_ S inlH (shiftH t)) (gH t)

    shift-inl : ∀ x → map shiftRH ⟨$⟩ inj₁ x ≈ᴿ inj₁ (x + t)
    shift-inl x = inl≈ refl

    shift-inr-le : ∀ x → x ≤ t → map shiftRH ⟨$⟩ inj₂ x ≈ᴿ inj₁ (monus t x)
    shift-inr-le x xt = pick-le t x xt (dec t x)

    shift-inr-gt : ∀ x → (x ≤ t → ⊥) → map shiftRH ⟨$⟩ inj₂ x ≈ᴿ inj₂ (monus x t)
    shift-inr-gt x nx = pick-gt t x nx (dec t x)

    -- reflection of [0, t)
    ∫-reflIv : ∀ (h : Hom S WQ WQ) →
      ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) (_∘H_ S h (rsubH t))) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h)
    ∫-reflIv = ∫-reflIv′ t bt

    -- the pieces of ∫ h(x + t) dx: the left half, and the right half split at t
    shiftR-inl : ∀ (h : Hom S RQ WQ) →
      I (_∘H_ S (_∘H_ S h shiftRH) inlH) ≈ I (_∘H_ S (_∘H_ S h inlH) (shiftH t))
    shiftR-inl h = ∫ᴹ-cong {WQ} lebPre {_∘H_ S (_∘H_ S h shiftRH) inlH} {_∘H_ S (_∘H_ S h inlH) (shiftH t)}
      (λ x → Func.cong (map h) (shift-inl x))

    shiftR-le : ∀ (h : Hom S RQ WQ) → I (mulH {WQ} (leH t) (_∘H_ S (_∘H_ S h shiftRH) inrH)) ≈
      I (mulH {WQ} (leH t) (_∘H_ S (_∘H_ S h inlH) (rsubH t)))
    shiftR-le h = ∫ᴹ-cong {WQ} lebPre {mulH {WQ} (leH t) (_∘H_ S (_∘H_ S h shiftRH) inrH)}
      {mulH {WQ} (leH t) (_∘H_ S (_∘H_ S h inlH) (rsubH t))} pt
      where
        pt : ∀ x → (map (leH t) ⟨$⟩ x) * (map h ⟨$⟩ (map shiftRH ⟨$⟩ inj₂ x)) ≈ (map (leH t) ⟨$⟩ x) * (map h ⟨$⟩ inj₁ (monus t x))
        pt x = [ (λ g → *-cong (refl {map (leH t) ⟨$⟩ x}) (Func.cong (map h) (shift-inr-le x (toLe {x} {t} g))))
               , (λ n → trans (*-cong (tv-out n) (refl {map h ⟨$⟩ (map shiftRH ⟨$⟩ inj₂ x)})) (trans (zeroˡ _)
                   (sym (trans (*-cong (tv-out n) (refl {map h ⟨$⟩ inj₁ (monus t x)})) (zeroˡ _))))) ]′ (lemOf lem₁ (Ge x t))

    shiftR-gt : ∀ (h : Hom S RQ WQ) → I (mulH {WQ} (gtH t) (_∘H_ S (_∘H_ S h shiftRH) inrH)) ≈
      I (mulH {WQ} (gtH t) (_∘H_ S (_∘H_ S h inrH) (subH t)))
    shiftR-gt h = ∫ᴹ-cong {WQ} lebPre {mulH {WQ} (gtH t) (_∘H_ S (_∘H_ S h shiftRH) inrH)}
      {mulH {WQ} (gtH t) (_∘H_ S (_∘H_ S h inrH) (subH t))} pt
      where
        pt : ∀ x → (map (gtH t) ⟨$⟩ x) * (map h ⟨$⟩ (map shiftRH ⟨$⟩ inj₂ x)) ≈ (map (gtH t) ⟨$⟩ x) * (map h ⟨$⟩ inj₂ (monus x t))
        pt x = [ (λ g → trans (*-cong (tv-out (λ n → n g)) (refl {map h ⟨$⟩ (map shiftRH ⟨$⟩ inj₂ x)})) (trans (zeroˡ _)
                   (sym (trans (*-cong (tv-out (λ n → n g)) (refl {map h ⟨$⟩ inj₂ (monus x t)})) (zeroˡ _)))))
               , (λ n → *-cong (refl {map (gtH t) ⟨$⟩ x}) (Func.cong (map h) (shift-inr-gt x (λ xt → n (toGe xt))))) ]′
               (lemOf lem₁ (Ge x t))

    -- the right half
    shiftR-inr : ∀ (h : Hom S RQ WQ) → I (_∘H_ S (_∘H_ S h shiftRH) inrH) ≈
      I (mulH {WQ} (χIv 0# t) (_∘H_ S h inlH)) + I (_∘H_ S h inrH)
    shiftR-inr h = trans (split t f) (+-cong
      (trans (shiftR-le h) (trans (le-lt t bt (_∘H_ S (_∘H_ S h inlH) (rsubH t))) (∫-reflIv (_∘H_ S h inlH))))
      (trans (shiftR-gt h) (gt-shift t bt (_∘H_ S h inrH))))
      where f = _∘H_ S (_∘H_ S h shiftRH) inrH

    ∫-shiftR : ∀ (h : Hom S RQ WQ) → ∫ᴹ {RQ} lebR (_∘H_ S h shiftRH) ≈ ∫ᴹ {RQ} lebR h
    ∫-shiftR h = trans (∫ᴹ-lebR (_∘H_ S h shiftRH)) (trans (+-cong (shiftR-inl h) (shiftR-inr h))
      (trans (sym (+-assoc _ _ _)) (trans (+-cong (∫-shift t bt (_∘H_ S h inlH)) (refl {I (_∘H_ S h inrH)})) (sym (∫ᴹ-lebR h)))))

    -- x ↦ x − t
    shiftNegRH : Hom S RQ RQ
    shiftNegRH = _∘H_ S reflRH (_∘H_ S shiftRH reflRH)

    ∫-shiftNegR : ∀ (h : Hom S RQ WQ) → ∫ᴹ {RQ} lebR (_∘H_ S h shiftNegRH) ≈ ∫ᴹ {RQ} lebR h
    ∫-shiftNegR h = trans (∫ᴹ-cong {RQ} lebR {_∘H_ S h shiftNegRH}
      {_∘H_ S (_∘H_ S (_∘H_ S h reflRH) shiftRH) reflRH} (λ x → refl))
      (trans (∫-reflR (_∘H_ S (_∘H_ S h reflRH) shiftRH)) (trans (∫-shiftR (_∘H_ S h reflRH)) (∫-reflR h)))
