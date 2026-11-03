{-# OPTIONS --safe --without-K #-}

-- Helpers for `RealShift`: null points of Lebesgue measure on the half-line, and splitting at a point.
--   * `leH c`, `gtH c`: the indicators of {x ≤ c} and {x ≰ c} (`Intervals.indH`, Borel by `LipTestAlg.le-borel`);
--     `split : ∫ f ≈ ∫ [x ≤ c] f + ∫ [x ≰ c] f`;
--   * `E0 : ∫ [x ≤ 0] ≈ 0` (the point 0 is null): by scaling, 2 m = m for m = ∫ [x ≤ 0] ≤ 1, and m is finite, so m = 0;
--     `Z`, `drop0`, `pt0-eq`: tests that agree off 0 have the same integral;
--   * `shift-le : y + t ≤ t → y ≤ 0` for finite t (from `Monus`);
--   * `le-lt : ∫ [x ≤ t] k ≈ ∫ [0,t) k` (the point t is null; `LebesgueShift.∫-shift` applied to [x ≤ t] k, whose translate
--     is k(t) [y ≤ 0]) and `gt-shift : ∫ [x ≰ t] h(x ∸ t) dx ≈ ∫ h`.
module QBS.Continuous.RealShiftNull where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (mk⊑; _⊑_)
open _⊑_ using (ap)
open import QBS.Analysis.RationalLemmas using (0<1; <-irrefl; ≃-refl)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Borel.Core using (compl)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.LipTestAlg using (module LipAlg)
open import QBS.Continuous.LebesgueInterval using (module LebesgueInterval)
open import QBS.Continuous.LebesgueScale using (module LebesgueScale)
open import QBS.Continuous.LebesgueShift using (module LebesgueShift)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)
open import QBS.Inference.Domination using (module Domination)
open import QBS.Continuous.Monus using (module Monus)

module RealShiftNull (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive;
    +-identityˡ; +-identityʳ; ≤-refl; zeroˡ; zeroʳ; *-identityˡ; *-identityʳ; +-mono;
    distribʳ; ≤-+ʳ; 0-least; +-comm) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineRate lem₁ using (scaleH)
  open ExpDist lem₁ using (idW)
  open Intervals (lemOf lem₁) using (Ge; InIv; χIv; χIv-in; χIv-out; indH; tv-in; tv-out; tv-cong)
  open LipAlg lem₁ using (le-borel)
  open LebesgueInterval lem₁ using (leb-Iv)
  open LebesgueScale lem₁ using (∫-scale)
  open LebesgueShift lem₁ using (shiftH; ∫-shift)
  open LebesgueShiftAlg (lemOf lem₁) using (total; t≤x+t)
  open LebesgueIntervalAlg (lemOf lem₁) using (∫ᴹ-zero′)
  open Domination lem₁ using (addH; ∫ᴹ-add; ∫ᴹ-mono; ∫ᴹ-scale; Bnd-≤; Bnd-add)
  open Monus lem₁ using (monus; monus-+; monus-zero; subH)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open HalfOrder A (lowerRealsArch (lemOf lem₁)) using (half≤1)
  open BoundedCancel A half hh using (cancel-bnd)
  open QBS
  open Hom

  I : Hom S WQ WQ → ∣A∣
  I f = ∫ᴹ {WQ} lebPre f

  toGe : ∀ {a b} → a ≤ b → Ge a b
  toGe h = ap h

  toLe : ∀ {a b} → Ge a b → a ≤ b
  toLe {a} {b} g = mk⊑ {a} {b} g

  Ge-resp : ∀ {x y c} → x ≈ y → Ge x c → Ge y c
  Ge-resp e p q mq = p q (ap (proj₂ e) q mq)

  Ge-respʳ : ∀ {x c c′} → c ≈ c′ → Ge x c → Ge x c′
  Ge-respʳ e p q mq = ap (proj₁ e) q (p q mq)

  -- the indicators of {x ≤ c} and {x ≰ c}
  leH gtH : ∣A∣ → Hom S WQ WQ
  leH c = indH (λ x → Ge x c) (λ {x} {y} e → Ge-resp {x} {y} {c} e) (λ m → le-borel c m)
  gtH c = indH (λ x → Ge x c → ⊥) (λ {x} {y} e np g → np (Ge-resp {y} {x} {c} (sym e) g)) (λ m → compl (le-borel c m))

  mulH-pt : ∀ d f x → map (mulH {WQ} d f) ⟨$⟩ x ≈ (map d ⟨$⟩ x) * (map f ⟨$⟩ x)
  mulH-pt d f x = refl

  sel₁ : ∀ {u v} a → u ≈ 1# → v ≈ 0# → a ≈ u * a + v * a
  sel₁ a eu ev = sym (trans (+-cong (*-cong eu (refl {a})) (*-cong ev (refl {a})))
    (trans (+-cong (*-identityˡ a) (zeroˡ a)) (+-identityʳ a)))

  sel₂ : ∀ {u v} a → u ≈ 0# → v ≈ 1# → a ≈ u * a + v * a
  sel₂ a eu ev = sym (trans (+-cong (*-cong eu (refl {a})) (*-cong ev (refl {a})))
    (trans (+-cong (zeroˡ a) (*-identityˡ a)) (+-identityˡ a)))

  split : ∀ c f → I f ≈ I (mulH {WQ} (leH c) f) + I (mulH {WQ} (gtH c) f)
  split c f = trans (∫ᴹ-cong {WQ} lebPre {f} {addH (mulH {WQ} (leH c) f) (mulH {WQ} (gtH c) f)} pt)
    (∫ᴹ-add lebPre (mulH {WQ} (leH c) f) (mulH {WQ} (gtH c) f))
    where
      pt : ∀ x → map f ⟨$⟩ x ≈ (map (mulH {WQ} (leH c) f) ⟨$⟩ x) + (map (mulH {WQ} (gtH c) f) ⟨$⟩ x)
      pt x = [ (λ g → sel₁ (map f ⟨$⟩ x) (tv-in g) (tv-out (λ n → n g)))
             , (λ n → sel₂ (map f ⟨$⟩ x) (tv-out (λ g → n g)) (tv-in n)) ]′ (lemOf lem₁ (Ge x c))

  ----------------------------------------------------------------------------
  -- the point 0 is null

  E : Hom S WQ WQ
  E = leH 0#

  two : ∣A∣
  two = 1# + 1#

  two-x : ∀ x → two * x ≈ x + x
  two-x x = trans (distribʳ x 1# 1#) (+-cong (*-identityˡ x) (*-identityˡ x))

  E-dbl : ∀ x → map E ⟨$⟩ (two * x) ≈ map E ⟨$⟩ x
  E-dbl x = tv-cong f g
    where
      f : Ge (two * x) 0# → Ge x 0#
      f h = toGe (≤-trans (≤-trans (≤-+ʳ {x} {x}) (≤-reflexive (sym (two-x x)))) (toLe {two * x} {0#} h))
      g : Ge x 0# → Ge (two * x) 0#
      g h = toGe (≤-trans (≤-reflexive (two-x x)) (≤-trans (+-mono (toLe h) (toLe h)) (≤-reflexive (+-identityˡ 0#))))

  Bnd-1 : Bnd 1#
  Bnd-1 = 1 , ≤-reflexive (sym (+-identityʳ 1#))

  E-in : ∀ x → Ge x 0# → InIv 0# 1# x
  E-in x g = toGe (0-least {x}) , λ h → <-irrefl ≃-refl (ap (≤-trans (toLe {1#} {x} h) (toLe {x} {0#} g)) _ 0<1)

  E≤χ : ∀ x → map E ⟨$⟩ x ≤ map (χIv 0# 1#) ⟨$⟩ x
  E≤χ x = [ (λ g → ≤-reflexive (trans (tv-in g) (sym (χIv-in 0# 1# x (E-in x g)))))
          , (λ n → ≤-trans (≤-reflexive (tv-out n)) 0-least) ]′ (lemOf lem₁ (Ge x 0#))

  E-fin : Bnd (I E)
  E-fin = Bnd-≤ (≤-trans (∫ᴹ-mono lebPre {E} {χIv 0# 1#} E≤χ)
    (≤-reflexive (trans (sym (+-identityˡ _)) (leb-Iv 0# 1# 0-least Bnd-1)))) Bnd-1

  E0 : I E ≈ 0#
  E0 = cancel-bnd E-fin (trans two-m (sym (+-identityʳ _)))
    where
      sc : two * I (_∘H_ S E (scaleH two idW)) ≈ I E
      sc = ∫-scale two half (trans (distribʳ half 1# 1#) (trans (+-cong (*-identityˡ half) (*-identityˡ half)) hh))
        (Bnd-add Bnd-1 Bnd-1) (1 , ≤-trans half≤1 (≤-reflexive (sym (+-identityʳ 1#)))) E
      cg : I (_∘H_ S E (scaleH two idW)) ≈ I E
      cg = ∫ᴹ-cong {WQ} lebPre {_∘H_ S E (scaleH two idW)} {E} E-dbl
      two-m : I E + I E ≈ I E
      two-m = trans (sym (two-x _)) (trans (*-cong refl (sym cg)) sc)

  x≈0 : ∀ {x} → Ge x 0# → x ≈ 0#
  x≈0 {x} g = toLe {x} {0#} g , 0-least {x}

  Z : ∀ f → I (mulH {WQ} (leH 0#) f) ≈ 0#
  Z f = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (leH 0#) f} {mulH {WQ} (constW {WQ} f0) E} pt)
    (trans (∫ᴹ-scale lebPre f0 E) (trans (*-cong (refl {f0}) E0) (zeroʳ f0)))
    where
      f0 = map f ⟨$⟩ 0#
      pt : ∀ x → (map (leH 0#) ⟨$⟩ x) * (map f ⟨$⟩ x) ≈ f0 * (map E ⟨$⟩ x)
      pt x = [ (λ g → trans (*-cong (tv-in g) (refl {map f ⟨$⟩ x})) (trans (*-identityˡ _) (trans (Func.cong (map f) (x≈0 g))
                 (trans (sym (*-identityʳ f0)) (*-cong (refl {f0}) (sym (tv-in g)))))))
             , (λ n → trans (*-cong (tv-out n) (refl {map f ⟨$⟩ x})) (trans (zeroˡ _)
                 (trans (sym (zeroʳ f0)) (*-cong (refl {f0}) (sym (tv-out n)))))) ]′ (lemOf lem₁ (Ge x 0#))

  drop0 : ∀ f → I f ≈ I (mulH {WQ} (gtH 0#) f)
  drop0 f = trans (split 0# f) (trans (+-cong (Z f) (refl {I (mulH {WQ} (gtH 0#) f)})) (+-identityˡ _))

  -- tests that agree off 0 have the same integral
  pt0-eq : ∀ f g → (∀ x → (Ge x 0# → ⊥) → map f ⟨$⟩ x ≈ map g ⟨$⟩ x) → I f ≈ I g
  pt0-eq f g e = trans (drop0 f) (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (gtH 0#) f} {mulH {WQ} (gtH 0#) g} pt) (sym (drop0 g)))
    where
      pt : ∀ x → (map (gtH 0#) ⟨$⟩ x) * (map f ⟨$⟩ x) ≈ (map (gtH 0#) ⟨$⟩ x) * (map g ⟨$⟩ x)
      pt x = [ (λ h → trans (*-cong (tv-out (λ n → n h)) (refl {map f ⟨$⟩ x})) (trans (zeroˡ _)
                 (sym (trans (*-cong (tv-out (λ n → n h)) (refl {map g ⟨$⟩ x})) (zeroˡ _)))))
             , (λ n → *-cong (refl {map (gtH 0#) ⟨$⟩ x}) (e x n)) ]′ (lemOf lem₁ (Ge x 0#))

  ----------------------------------------------------------------------------
  -- translation by a finite t

  shift-le : ∀ t → Bnd t → ∀ y → y + t ≤ t → y ≤ 0#
  shift-le t bt y h = proj₁ (trans (sym (monus-+ y t bt)) (monus-zero (y + t) t h))

  shift-ge : ∀ t y → y ≤ 0# → y + t ≤ t
  shift-ge t y h = ≤-trans (+-mono h (≤-refl {t})) (≤-reflexive (+-identityˡ t))

  yt≈t : ∀ t y → y ≤ 0# → y + t ≈ t
  yt≈t t y h = shift-ge t y h , t≤x+t y t

  -- products with indicators
  zz : ∀ {u v : ∣A∣} (a b : ∣A∣) → u ≈ 0# → v ≈ 0# → u * a ≈ b * v
  zz a b eu ev = trans (*-cong eu (refl {a})) (trans (zeroˡ a) (sym (trans (*-cong (refl {b}) ev) (zeroʳ b))))

  oo : ∀ {u v : ∣A∣} (a b : ∣A∣) → u ≈ 1# → v ≈ 1# → a ≈ b → u * a ≈ b * v
  oo a b eu ev e = trans (*-cong eu (refl {a})) (trans (*-identityˡ a)
    (trans e (sym (trans (*-cong (refl {b}) ev) (*-identityʳ b)))))

  zz′ : ∀ {u v : ∣A∣} (a b : ∣A∣) → u ≈ 0# → v ≈ 0# → u * a ≈ v * b
  zz′ a b eu ev = trans (*-cong eu (refl {a})) (trans (zeroˡ a) (sym (trans (*-cong ev (refl {b})) (zeroˡ b))))

  -- the point t is null: ∫ [x ≤ t] k ≈ ∫ [0,t) k
  leT-pt : ∀ t → Bnd t → ∀ (k : Hom S WQ WQ) y →
    (map (leH t) ⟨$⟩ (y + t)) * (map k ⟨$⟩ (y + t)) ≈ (map k ⟨$⟩ t) * (map E ⟨$⟩ y)
  leT-pt t bt k y = [ (λ gy → let yt = yt≈t t y (toLe {y} {0#} gy) in
                        oo (map k ⟨$⟩ (y + t)) (map k ⟨$⟩ t) (tv-in (toGe (proj₁ yt))) (tv-in gy) (Func.cong (map k) yt))
                    , (λ n → zz (map k ⟨$⟩ (y + t)) (map k ⟨$⟩ t)
                        (tv-out (λ h → n (toGe (shift-le t bt y (toLe {y + t} {t} h))))) (tv-out n)) ]′ (lemOf lem₁ (Ge y 0#))

  leT-first : ∀ t → Bnd t → ∀ (k : Hom S WQ WQ) → I (_∘H_ S (mulH {WQ} (leH t) k) (shiftH t)) ≈ 0#
  leT-first t bt k = trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S (mulH {WQ} (leH t) k) (shiftH t)}
    {mulH {WQ} (constW {WQ} (map k ⟨$⟩ t)) E} (leT-pt t bt k))
    (trans (∫ᴹ-scale lebPre (map k ⟨$⟩ t) E) (trans (*-cong (refl {map k ⟨$⟩ t}) E0) (zeroʳ (map k ⟨$⟩ t))))

  in-ge : ∀ t x → InIv 0# t x → Ge x t
  in-ge t x i = [ (λ tx → ⊥-elim (proj₂ i (toGe tx))) , toGe ]′ (total t x)

  leT-second : ∀ t (k : Hom S WQ WQ) x → (map (χIv 0# t) ⟨$⟩ x) * ((map (leH t) ⟨$⟩ x) * (map k ⟨$⟩ x))
    ≈ (map (χIv 0# t) ⟨$⟩ x) * (map k ⟨$⟩ x)
  leT-second t k x = [ (λ i → *-cong (refl {map (χIv 0# t) ⟨$⟩ x}) (trans (*-cong (tv-in (in-ge t x i)) (refl {map k ⟨$⟩ x}))
                          (*-identityˡ _)))
                     , (λ o → zz′ ((map (leH t) ⟨$⟩ x) * (map k ⟨$⟩ x)) (map k ⟨$⟩ x) (χIv-out 0# t x o) (χIv-out 0# t x o)) ]′
                     (lemOf lem₁ (InIv 0# t x))

  le-lt : ∀ t → Bnd t → ∀ (k : Hom S WQ WQ) → I (mulH {WQ} (leH t) k) ≈ I (mulH {WQ} (χIv 0# t) k)
  le-lt t bt k = trans (sym (∫-shift t bt g)) (trans (+-cong (leT-first t bt k) second) (+-identityˡ _))
    where
      g = mulH {WQ} (leH t) k
      second : I (mulH {WQ} (χIv 0# t) g) ≈ I (mulH {WQ} (χIv 0# t) k)
      second = ∫ᴹ-cong {WQ} lebPre {mulH {WQ} (χIv 0# t) g} {mulH {WQ} (χIv 0# t) k} (leT-second t k)

  -- ∫ [x ≰ t] h(x ∸ t) dx ≈ ∫ h
  gtT-pt : ∀ t → Bnd t → ∀ (h : Hom S WQ WQ) y →
    (map (gtH t) ⟨$⟩ (y + t)) * (map h ⟨$⟩ monus (y + t) t) ≈ (map (gtH 0#) ⟨$⟩ y) * (map h ⟨$⟩ y)
  gtT-pt t bt h y = [ (λ gy → zz′ (map h ⟨$⟩ monus (y + t) t) (map h ⟨$⟩ y)
                        (tv-out (λ n → n (toGe (shift-ge t y (toLe {y} {0#} gy))))) (tv-out (λ n → n gy)))
                    , (λ n → oo′ n) ]′ (lemOf lem₁ (Ge y 0#))
    where
      oo′ : (Ge y 0# → ⊥) → _ ≈ _
      oo′ n = trans (*-cong (tv-in nt) (refl {map h ⟨$⟩ monus (y + t) t})) (trans (*-identityˡ _)
        (trans (Func.cong (map h) (monus-+ y t bt)) (sym (trans (*-cong (tv-in n) (refl {map h ⟨$⟩ y})) (*-identityˡ _)))))
        where nt : Ge (y + t) t → ⊥
              nt h′ = n (toGe (shift-le t bt y (toLe {y + t} {t} h′)))

  gtT-second : ∀ t (h : Hom S WQ WQ) x →
    (map (χIv 0# t) ⟨$⟩ x) * ((map (gtH t) ⟨$⟩ x) * (map h ⟨$⟩ monus x t)) ≈ 0#
  gtT-second t h x = [ (λ i → trans (*-cong (refl {map (χIv 0# t) ⟨$⟩ x}) (trans (*-cong (tv-out (λ n → n (in-ge t x i)))
                         (refl {map h ⟨$⟩ monus x t})) (zeroˡ _))) (zeroʳ _))
                     , (λ o → trans (*-cong (χIv-out 0# t x o) (refl {(map (gtH t) ⟨$⟩ x) * (map h ⟨$⟩ monus x t)})) (zeroˡ _)) ]′
                     (lemOf lem₁ (InIv 0# t x))

  gt-shift : ∀ t → Bnd t → ∀ (h : Hom S WQ WQ) → I (mulH {WQ} (gtH t) (_∘H_ S h (subH t))) ≈ I h
  gt-shift t bt h = trans (sym (∫-shift t bt g)) (trans (+-cong first second) (trans (+-identityʳ _) (sym (drop0 h))))
    where
      g = mulH {WQ} (gtH t) (_∘H_ S h (subH t))
      first : I (_∘H_ S g (shiftH t)) ≈ I (mulH {WQ} (gtH 0#) h)
      first = ∫ᴹ-cong {WQ} lebPre {_∘H_ S g (shiftH t)} {mulH {WQ} (gtH 0#) h} (gtT-pt t bt h)
      second : I (mulH {WQ} (χIv 0# t) g) ≈ 0#
      second = ∫ᴹ-zero′ lebPre (mulH {WQ} (χIv 0# t) g) (gtT-second t h)
