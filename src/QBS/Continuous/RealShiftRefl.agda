{-# OPTIONS --safe --without-K #-}

-- Reflection of the interval [0, t) (helper for `RealShift.∫-reflIv`).
--   * `reflMeas t`, the measure h ↦ ∫_{[0,t)} h(t ∸ x) dx + ∫ h(x + t) dx (a `sumPre` of two pushforwards and zero measures);
--   * `refl-Iv`: ∫_{[0,t)} χ[0,b)(t ∸ x) dx ≈ ∫_{[0,t)} χ[0,b) for finite b.  For t ≤ b the integrands agree off x = 0
--     (`RealShiftNull.pt0-eq`); for b ≤ t, χ[0,b)(t ∸ x) = [x ≰ t ∸ b] on [0,t) (`gal←`, `gal→`), so the integral is t − (t ∸ b)
--     (`RealShiftNull.split`, `le-lt`) and equals b by cancellation;
--   * so `reflMeas t` gives [0,b) the mass b (with `LebesgueShift.F-above`, `F-below`), no mass to ∞, and is Lebesgue
--     measure (`LebesgueInterval.leb-unique`); testing it against [0,t) h gives `∫-reflIv`.
module QBS.Continuous.RealShiftRefl where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (_⊑_; module Cut)
open Cut using (mem)
open _⊑_ using (ap)
open import QBS.Analysis.RationalLemmas using (<-irrefl; ≃-refl)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Series using (module Series)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.LebesgueInterval using (module LebesgueInterval)
open import QBS.Continuous.LebesgueDyadic using (module LebesgueDyadic)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)
open import QBS.Continuous.LebesgueShift using (module LebesgueShift)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Inference.Domination using (module Domination)
open import QBS.Continuous.Monus using (module Monus)
open import QBS.Continuous.RealShiftNull using (module RealShiftNull)

module RealShiftRefl (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive; +-identityˡ;
    +-identityʳ; ≤-refl; zeroˡ; zeroʳ; *-identityˡ; *-identityʳ; *-comm; +-mono; ≤-+ʳ; 0-least; +-comm) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open Series A using (∑ᶠ; ∑ᶠ-shift; ∑ᶠ-zero)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; mapM; ∫ᴹ-map; module C)
  open C using (Pre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open SFiniteSum (lemOf lem₁) using (sumPre; scalePre; ∫ᴹ-sum; ∫ᴹ-scale)
  open HalfLine lem₁ using (lebPre)
  open Intervals (lemOf lem₁) using (Ge; InIv; InInf; χIv; χInf; χIv-in; χIv-out; χInf-out; tv-cong; tv-in; tv-out)
  open LebesgueInterval lem₁ using (leb-Iv; leb-unique)
  open LebesgueDyadic lem₁ using (leb-inf)
  open LebesgueIntervalAlg (lemOf lem₁) using (F; ∫ᴹ-zero′)
  open LebesgueShift lem₁ using (shiftH; F-above; F-below)
  open LebesgueShiftAlg (lemOf lem₁) using (Iv-from-F; total; t≤x+t; below-zero; prod-≤; prod-≥; inf-shift; bnd-rat; top-of)
  open Domination lem₁ using (Bnd-≤)
  open Monus lem₁ using (monus; monus-add; monus-+; monus-mono; rsubH)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open BoundedCancel A half hh using (cancel-bnd)
  open RealShiftNull lem₁ using (I; toGe; toLe; leH; gtH; split; le-lt; pt0-eq; shift-le; zz; zz′)
  open QBS
  open Hom

  -- the measure h ↦ ∫_{[0,t)} h(t ∸ x) dx + ∫ h(x + t) dx
  fam : ∣A∣ → ℕ → Pre (XW WQ)
  fam t zero = mapM {WQ} {WQ} (rsubH t) (reweightPre {WQ} (χIv 0# t) lebPre)
  fam t (suc zero) = mapM {WQ} {WQ} (shiftH t) lebPre
  fam t (suc (suc _)) = scalePre {WQ} 0# lebPre

  reflMeas : ∣A∣ → Pre (XW WQ)
  reflMeas t = sumPre {WQ} (fam t)

  ∫-reflMeas : ∀ t (h : Hom S WQ WQ) → ∫ᴹ {WQ} (reflMeas t) h ≈
    I (mulH {WQ} (χIv 0# t) (_∘H_ S h (rsubH t))) + I (_∘H_ S h (shiftH t))
  ∫-reflMeas t h = trans (∫ᴹ-sum {WQ} (fam t) h) (trans (∑ᶠ-shift a) (+-cong first rest))
    where
      a = λ n → ∫ᴹ {WQ} (fam t n) h
      first : a 0 ≈ I (mulH {WQ} (χIv 0# t) (_∘H_ S h (rsubH t)))
      first = trans (∫ᴹ-map {WQ} {WQ} (rsubH t) (reweightPre {WQ} (χIv 0# t) lebPre) h)
        (∫ᴹ-reweight {WQ} (χIv 0# t) lebPre (_∘H_ S h (rsubH t)))
      tail₂ : ∑ᶠ (λ n → a (suc (suc n))) ≈ 0#
      tail₂ = ∑ᶠ-zero (λ n → trans (∫ᴹ-scale {WQ} 0# lebPre h) (zeroˡ _))
      rest : ∑ᶠ (λ n → a (suc n)) ≈ I (_∘H_ S h (shiftH t))
      rest = trans (∑ᶠ-shift (λ n → a (suc n))) (trans (+-cong (∫ᴹ-map {WQ} {WQ} (shiftH t) lebPre h) tail₂) (+-identityʳ _))

  module _ (t : ∣A∣) (bt : Bnd t) where

    -- x in [0,t) is below t
    in-le : ∀ x → InIv 0# t x → x ≤ t
    in-le x i = [ (λ tx → ⊥-elim (proj₂ i (toGe tx))) , (λ xt → xt) ]′ (total t x)

    -- for x ∈ (0,t) and t ≤ b: t ∸ x ∈ [0,b)
    mt-in : ∀ b x → t ≤ b → InIv 0# t x → (Ge x 0# → ⊥) → InIv 0# b (monus t x)
    mt-in b x tb i nz = toGe (0-least {monus t x}) , λ h →
      nz (toGe (shift-le t bt x (≤-trans (+-mono (≤-refl {x}) (≤-trans tb (toLe h)))
        (≤-reflexive (monus-add t x (Bnd-≤ (in-le x i) bt) (in-le x i))))))

    -- Galois connection: b ≤ t ∸ x iff x ≤ t ∸ b (x, b ≤ t)
    gal→ : ∀ x b → Bnd x → Bnd b → x ≤ t → Ge b (monus t x) → Ge x (monus t b)
    gal→ x b bx bb xt g = toGe (≤-trans (≤-reflexive (sym (monus-+ x b bb))) (monus-mono b xb))
      where xb : x + b ≤ t
            xb = ≤-trans (+-mono (≤-refl {x}) (toLe g)) (≤-reflexive (monus-add t x bx xt))

    gal← : ∀ x b → Bnd x → Bnd b → b ≤ t → Ge x (monus t b) → Ge b (monus t x)
    gal← x b bx bb bt′ g = toGe (≤-trans (≤-reflexive (sym (monus-+ b x bx))) (monus-mono x bx′))
      where bx′ : b + x ≤ t
            bx′ = ≤-trans (+-mono (≤-refl {b}) (toLe g)) (≤-reflexive (monus-add t b bb bt′))

    -- shorthand: the indicator of [0,b) at x, and the two sides of the reflection identity
    ind : ∣A∣ → ∣A∣ → ∣A∣
    ind b x = map (χIv 0# b) ⟨$⟩ x

    RF LF : ∣A∣ → ∣A∣
    RF b = I (mulH {WQ} (χIv 0# t) (_∘H_ S (χIv 0# b) (rsubH t)))
    LF b = I (mulH {WQ} (χIv 0# t) (χIv 0# b))

    -- reflection of [0,b) for t ≤ b
    refl-ge-pt : ∀ b → t ≤ b → ∀ x → (Ge x 0# → ⊥) → ind t x * ind b (monus t x) ≈ ind t x
    refl-ge-pt b tb x nz = [ (λ i → trans (*-cong (refl {ind t x}) (χIv-in 0# b _ (mt-in b x tb i nz))) (*-identityʳ _))
      , (λ o → trans (*-cong (χIv-out 0# t x o) (refl {ind b (monus t x)})) (trans (zeroˡ _) (sym (χIv-out 0# t x o)))) ]′
      (lemOf lem₁ (InIv 0# t x))

    refl-ge : ∀ b → t ≤ b → RF b ≈ LF b
    refl-ge b tb = pt0-eq _ _ (λ x nz → trans (refl-ge-pt b tb x nz) (sym (prod-≥ b t x tb)))

    I-Iv : ∀ b → Bnd b → I (χIv 0# b) ≈ b
    I-Iv b bb = trans (sym (+-identityˡ _)) (leb-Iv 0# b 0-least bb)

    -- ∫ [x ≰ c] χ[0,t) = b, for c = t ∸ b
    gt-mass : ∀ b → Bnd b → b ≤ t → I (mulH {WQ} (gtH (monus t b)) (χIv 0# t)) ≈ b
    gt-mass b bb bt′ = cancel-bnd bc (trans c+X (sym (trans (+-comm c b) e)))
      where
        c = monus t b
        X = I (mulH {WQ} (gtH c) (χIv 0# t))
        e : b + c ≈ t
        e = monus-add t b bb bt′
        c≤t : c ≤ t
        c≤t = ≤-trans (t≤x+t b c) (≤-reflexive e)
        bc : Bnd c
        bc = Bnd-≤ c≤t bt
        lc : I (mulH {WQ} (leH c) (χIv 0# t)) ≈ c
        lc = trans (le-lt c bc (χIv 0# t)) (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (χIv 0# c) (χIv 0# t)} {χIv 0# c}
          (λ x → trans (*-comm _ _) (prod-≤ c t x c≤t))) (I-Iv c bc))
        c+X : c + X ≈ t
        c+X = trans (+-cong (sym lc) (refl {X})) (trans (sym (split c (χIv 0# t))) (I-Iv t bt))

    -- χ[0,b)(t ∸ x) = [x ≰ t ∸ b] for x ≤ t, b ≤ t
    tv-gal : ∀ b → Bnd b → b ≤ t → ∀ x → x ≤ t → ind b (monus t x) ≈ map (gtH (monus t b)) ⟨$⟩ x
    tv-gal b bb bt′ x xt = tv-cong (λ (_ , nb) gx → nb (gal← x b bx bb bt′ gx))
      (λ ng → toGe (0-least {monus t x}) , λ gb → ng (gal→ x b bx bb xt gb))
      where bx = Bnd-≤ xt bt

    refl-le-pt : ∀ b → Bnd b → b ≤ t → ∀ x →
      ind t x * ind b (monus t x) ≈ (map (gtH (monus t b)) ⟨$⟩ x) * ind t x
    refl-le-pt b bb bt′ x = [ (λ i → trans (*-cong (χIv-in 0# t x i) (tv-gal b bb bt′ x (in-le x i))) (trans (*-identityˡ _)
        (sym (trans (*-cong (refl {map (gtH (monus t b)) ⟨$⟩ x}) (χIv-in 0# t x i)) (*-identityʳ _)))))
      , (λ o → zz (ind b (monus t x)) (map (gtH (monus t b)) ⟨$⟩ x) (χIv-out 0# t x o)
        (χIv-out 0# t x o)) ]′ (lemOf lem₁ (InIv 0# t x))

    refl-le : ∀ b → Bnd b → b ≤ t → RF b ≈ LF b
    refl-le b bb bt′ = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (χIv 0# t) (_∘H_ S (χIv 0# b) (rsubH t))}
      {mulH {WQ} (gtH (monus t b)) (χIv 0# t)} (refl-le-pt b bb bt′)) (trans (gt-mass b bb bt′) (sym lf))
      where lf = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (χIv 0# t) (χIv 0# b)} {χIv 0# b} (λ x → prod-≤ b t x bt′)) (I-Iv b bb)

    refl-Iv : ∀ b → Bnd b → RF b ≈ LF b
    refl-Iv b bb = [ refl-ge b , refl-le b bb ]′ (total t b)

    refl-F : ∀ b → Bnd b → F (reflMeas t) b ≈ b
    refl-F b bb = trans (∫-reflMeas t (χIv 0# b)) (trans (+-cong (refl-Iv b bb) (refl {I (_∘H_ S (χIv 0# b) (shiftH t))}))
      (trans (+-comm _ _) ([ F-above t bt b bb , F-below t bt b bb ]′ (total t b))))

    -- t ∸ x is finite
    mt-fin : ∀ x → x ≤ t → InInf (monus t x) → ⊥
    mt-fin x xt inf = let M , bd = bnd-rat t bt in <-irrefl ≃-refl (bd M (ap mt≤t M (top-of (monus t x) inf M)))
      where mt≤t : monus t x ≤ t
            mt≤t = ≤-trans (t≤x+t x (monus t x)) (≤-reflexive (monus-add t x (Bnd-≤ xt bt) xt))

    inf-pt : ∀ x → ind t x * (map χInf ⟨$⟩ monus t x) ≈ 0#
    inf-pt x = [ (λ i → trans (*-cong (refl {ind t x}) (χInf-out _ (mt-fin x (in-le x i)))) (zeroʳ _))
      , (λ o → trans (*-cong (χIv-out 0# t x o) (refl {map χInf ⟨$⟩ monus t x})) (zeroˡ _)) ]′ (lemOf lem₁ (InIv 0# t x))

    inf0 : ∫ᴹ {WQ} (reflMeas t) χInf ≈ 0#
    inf0 = trans (∫-reflMeas t χInf) (trans (+-cong first second) (+-identityˡ 0#))
      where
        first : I (mulH {WQ} (χIv 0# t) (_∘H_ S χInf (rsubH t))) ≈ 0#
        first = ∫ᴹ-zero′ lebPre (mulH {WQ} (χIv 0# t) (_∘H_ S χInf (rsubH t))) inf-pt
        second : I (_∘H_ S χInf (shiftH t)) ≈ 0#
        second = trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S χInf (shiftH t)} {χInf} (inf-shift t bt)) leb-inf

    uniq : ∀ (h : Hom S WQ WQ) → ∫ᴹ {WQ} (reflMeas t) h ≈ I h
    uniq = leb-unique (reflMeas t) (λ a b ab bb → Iv-from-F (reflMeas t) refl-F a b ab bb) inf0

    -- the integrand χ[0,t)(x) (χ[0,t) h)(t ∸ x) agrees with χ[0,t)(x) h(t ∸ x) off 0
    refl-pt : ∀ (h : Hom S WQ WQ) x → (Ge x 0# → ⊥) →
      ind t x * (ind t (monus t x) * (map h ⟨$⟩ monus t x)) ≈ ind t x * (map h ⟨$⟩ monus t x)
    refl-pt h x nz = [ (λ i → *-cong (refl {ind t x}) (trans (*-cong (χIv-in 0# t _ (mt-in t x (≤-refl {t}) i nz))
        (refl {map h ⟨$⟩ monus t x})) (*-identityˡ _)))
      , (λ o → zz′ (ind t (monus t x) * (map h ⟨$⟩ monus t x)) (map h ⟨$⟩ monus t x) (χIv-out 0# t x o) (χIv-out 0# t x o)) ]′
      (lemOf lem₁ (InIv 0# t x))

    -- reflection of [0,t)
    ∫-reflIv : ∀ (h : Hom S WQ WQ) →
      ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) (_∘H_ S h (rsubH t))) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h)
    ∫-reflIv h = trans (sym m) (trans (sym (+-identityʳ _)) (trans (+-cong (refl {I g′}) (sym z))
      (trans (sym (∫-reflMeas t g)) (uniq g))))
      where
        g = mulH {WQ} (χIv 0# t) h
        g′ = mulH {WQ} (χIv 0# t) (_∘H_ S g (rsubH t))
        z : I (_∘H_ S g (shiftH t)) ≈ 0#
        z = ∫ᴹ-zero′ lebPre (_∘H_ S g (shiftH t))
          (λ x → trans (*-cong (below-zero t t x (≤-refl {t})) (refl {map h ⟨$⟩ (x + t)})) (zeroˡ _))
        m : I g′ ≈ I (mulH {WQ} (χIv 0# t) (_∘H_ S h (rsubH t)))
        m = pt0-eq g′ (mulH {WQ} (χIv 0# t) (_∘H_ S h (rsubH t))) (refl-pt h)
