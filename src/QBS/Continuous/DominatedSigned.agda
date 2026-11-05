{-# OPTIONS --safe --without-K #-}

-- Dominated convergence for signed tests (plan 03, "Signed dominated convergence").  A signed test is a pair (h⁺, h⁻)
-- standing for h⁺ − h⁻, and its expectation the pair of integrals (`SignedIntegral`, `ExpectationInt.E-atᴵ`).
--   * `dct-signed`: if h⁺ n − h⁻ n → f⁺ − f⁻ pointwise wherever g is finite (`ConvEps.SConv`), with h⁺ n + h⁻ n ≤ g,
--     f⁺ + f⁻ ≤ g and ∫ g finite, then ∫ h⁺ n − ∫ h⁻ n → ∫ f⁺ − ∫ f⁻;
--   * `dct-signed-prob`: under a probability measure, with a uniform bound N in place of g.
-- Route: d n = h⁺ n + f⁻ and e n = h⁻ n + f⁺ (`FatouAux.addX`), cut to where g is finite (`NullInf.finχ`, so values are
-- pointwise bounded); `pn n = d n ∸ e n`, `qn n = e n ∸ d n` (`FatouAux.monusH`).  Pointwise d n + qn n ≈ e n + pn n
-- (`MonusAlg.monus-swap`: lower reals are comparable by excluded middle), pn n, qn n → 0 pointwise (`ConvEps.econv-conv`,
-- `MonusAlg.monus-small`), dominated by g + g, so ∫ pn n, ∫ qn n → 0 (`Dominated.dct`, `ConvEps.conv-econv`).  Integrate,
-- drop the cut (`NullInf.∫-fin-cut`) and cross-add: ∫h⁺ n + ∫f⁻ + ∫qn n ≈ ∫h⁻ n + ∫f⁺ + ∫pn n (`final-alg`), which is
-- the claim up to ∫pn n, ∫qn n ≤ ½ᵏ; `ConvEps.sconv-shift` is not needed.
module QBS.Continuous.DominatedSigned where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.ConvEps using (module ConvEps)
open import QBS.Continuous.Dominated using (module Dominated)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.Monus using (module Monus)
open import QBS.Continuous.MonusAlg using (module MonusAlg)
open import QBS.Continuous.NullInf using (module NullInf)

module DominatedSigned (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; refl; sym; trans; +-cong; +-comm; +-identityˡ; +-mono; *-cong; *-identityˡ;
    zeroˡ; ≤-trans; ≤-reflexive; ≤-refl; ≤-+ʳ; 0-least) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat; nat-+)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open Product (lemOf lem₁) using (cmul)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX; monusH)
  open Monus lem₁ using (monus; monus-cong; monus-zero)
  open MonusAlg lem₁ using (BndQ-≤; BndQ-≈; BndQ-add; BndQ-0; rat-bnd; monus-le; monus-small; monus-swap)
  open ConvEps lem₁ using (EConv; SConv; conv-econv; econv-conv)
  open Dominated lem₁ using (Conv; dct; prob-mass)
  open NullInf lem₁ using (finχ; finχ-in; finχ-out; ∫-fin-cut)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open QBS
  open Hom

  -- cross-adding: (a + v) + Q ≈ (b + u) + P with P, Q ≤ ½ᵏ gives both halves of the convergence of a − b to u − v
  final-alg : ∀ (a b u v P Q : ∣A∣) k → (a + v) + Q ≈ (b + u) + P → P ≤ 0# + hp k → Q ≤ 0# + hp k →
    (a + v ≤ u + b + hp k) × (u + b ≤ a + v + hp k)
  final-alg a b u v P Q k e hP hQ = lhs , rhs
    where
      hP′ : P ≤ hp k
      hP′ = ≤-trans hP (≤-reflexive (+-identityˡ _))
      hQ′ : Q ≤ hp k
      hQ′ = ≤-trans hQ (≤-reflexive (+-identityˡ _))
      lhs : a + v ≤ (u + b) + hp k
      lhs = ≤-trans (≤-+ʳ {a + v} {Q}) (≤-trans (≤-reflexive e)
        (≤-trans (+-mono ≤-refl hP′) (≤-reflexive (+-cong (+-comm b u) refl))))
      rhs : u + b ≤ (a + v) + hp k
      rhs = ≤-trans (≤-reflexive (+-comm u b)) (≤-trans (≤-+ʳ {b + u} {P})
        (≤-trans (≤-reflexive (sym e)) (+-mono ≤-refl hQ′)))

  conv-≈ : ∀ {a : ℕ → ∣A∣} {l l′} → Conv a l → l ≈ l′ → Conv a l′
  conv-≈ c e = trans (proj₁ c) e , trans (proj₂ c) e

  module _ {X : QBS S} where

    zero-int : ∀ (p : C.Pre (XW X)) → ∫ᴹ {X} p (constW {X} 0#) ≈ 0#
    zero-int p = trans (∫ᴹ-cong p {constW {X} 0#} {mulH {X} (constW {X} 0#) (constW {X} 0#)} (λ x → sym (zeroˡ 0#)))
      (trans (cmul p 0# (constW {X} 0#)) (zeroˡ _))

    -- cut a test to the points where g is finite
    cutH : Hom S X WQ → Hom S X WQ → Hom S X WQ
    cutH g t = mulH {X} (finχ g) t

    cut-in : ∀ (g t : Hom S X WQ) x → BndQ (map g ⟨$⟩ x) → map (cutH g t) ⟨$⟩ x ≈ map t ⟨$⟩ x
    cut-in g t x b = trans (*-cong (finχ-in g x b) refl) (*-identityˡ _)

    cut-out : ∀ (g t : Hom S X WQ) x → (BndQ (map g ⟨$⟩ x) → ⊥) → map (cutH g t) ⟨$⟩ x ≈ 0#
    cut-out g t x nb = trans (*-cong (finχ-out g x nb) refl) (zeroˡ _)

    bnd-cut : ∀ (g t : Hom S X WQ) x → (BndQ (map g ⟨$⟩ x) → BndQ (map t ⟨$⟩ x)) → BndQ (map (cutH g t) ⟨$⟩ x)
    bnd-cut g t x f with lemOf lem₁ (BndQ (map g ⟨$⟩ x))
    ... | inj₁ b = BndQ-≈ {map (cutH g t) ⟨$⟩ x} {map t ⟨$⟩ x} (cut-in g t x b) (f b)
    ... | inj₂ nb = BndQ-≈ {map (cutH g t) ⟨$⟩ x} {0#} (cut-out g t x nb) BndQ-0

    cut-le : ∀ (g t G : Hom S X WQ) x → (BndQ (map g ⟨$⟩ x) → map t ⟨$⟩ x ≤ map G ⟨$⟩ x) → map (cutH g t) ⟨$⟩ x ≤ map G ⟨$⟩ x
    cut-le g t G x f with lemOf lem₁ (BndQ (map g ⟨$⟩ x))
    ... | inj₁ b = ≤-trans (≤-reflexive (cut-in g t x b)) (f b)
    ... | inj₂ nb = ≤-trans (≤-reflexive (cut-out g t x nb)) 0-least

    -- d ∸ e on the cut tests
    pnH : ∀ (g : Hom S X WQ) (dd ee : ℕ → Hom S X WQ) → (∀ n x → BndQ (map g ⟨$⟩ x) → BndQ (map (ee n) ⟨$⟩ x)) →
      ℕ → Hom S X WQ
    pnH g dd ee be n = monusH {X} (cutH g (dd n)) (cutH g (ee n)) (λ x → bnd-cut g (ee n) x (be n x))

    pn-le : ∀ (g G : Hom S X WQ) (dd ee : ℕ → Hom S X WQ) be → (∀ n x → BndQ (map g ⟨$⟩ x) → map (dd n) ⟨$⟩ x ≤ map G ⟨$⟩ x) →
      ∀ n x → map (pnH g dd ee be n) ⟨$⟩ x ≤ map G ⟨$⟩ x
    pn-le g G dd ee be dom n x = ≤-trans
      (monus-le (map (cutH g (dd n)) ⟨$⟩ x) (map (cutH g (ee n)) ⟨$⟩ x) (rat-bnd _ (bnd-cut g (ee n) x (be n x))))
      (cut-le g (dd n) G x (dom n x))

    -- pointwise, d n ∸ e n is eventually below ½ᵏ
    pn-ec : ∀ (g : Hom S X WQ) (dd ee : ℕ → Hom S X WQ) be → (∀ x → BndQ (map g ⟨$⟩ x) → ∀ k →
      Σ ℕ (λ N → ∀ n → N ≤ℕ n → map (dd n) ⟨$⟩ x ≤ (map (ee n) ⟨$⟩ x) + hp k)) →
      ∀ x → EConv (λ n → map (pnH g dd ee be n) ⟨$⟩ x) 0#
    pn-ec g dd ee be cl x k with lemOf lem₁ (BndQ (map g ⟨$⟩ x))
    ... | inj₂ nb = 0 , λ n _ → ≤-trans (≤-reflexive (trans (monus-cong (cut-out g (dd n) x nb) (cut-out g (ee n) x nb))
        (monus-zero 0# 0# ≤-refl))) ≤-+ʳ , 0-least
    ... | inj₁ b = proj₁ (cl x b k) , λ n le → ≤-trans (monus-small (map (cutH g (dd n)) ⟨$⟩ x) (map (cutH g (ee n)) ⟨$⟩ x) k
        (rat-bnd _ (bnd-cut g (ee n) x (be n x))) (≤-trans (≤-reflexive (cut-in g (dd n) x b))
          (≤-trans (proj₂ (cl x b k) n le) (≤-reflexive (+-cong (sym (cut-in g (ee n) x b)) refl)))))
        (≤-reflexive (sym (+-identityˡ _))) , 0-least

    -- the integrals of d n ∸ e n tend to 0
    diff-econv : ∀ (p : C.Pre (XW X)) (g G : Hom S X WQ) (dd ee : ℕ → Hom S X WQ) → Bnd (∫ᴹ {X} p G) →
      (∀ n x → BndQ (map g ⟨$⟩ x) → map (dd n) ⟨$⟩ x ≤ map G ⟨$⟩ x) →
      (be : ∀ n x → BndQ (map g ⟨$⟩ x) → BndQ (map (ee n) ⟨$⟩ x)) →
      (∀ x → BndQ (map g ⟨$⟩ x) → ∀ k → Σ ℕ (λ N → ∀ n → N ≤ℕ n → map (dd n) ⟨$⟩ x ≤ (map (ee n) ⟨$⟩ x) + hp k)) →
      EConv (λ n → ∫ᴹ {X} p (pnH g dd ee be n)) 0#
    diff-econv p g G dd ee bG dom be cl = conv-econv _ 0# (0 , 0-least) (conv-≈
      (dct p (pnH g dd ee be) (constW {X} 0#) G (λ x → econv-conv _ 0# (pn-ec g dd ee be cl x)) (pn-le g G dd ee be dom) bG)
      (zero-int p))

    module Sg (p : C.Pre (XW X)) (h⁺ h⁻ : ℕ → Hom S X WQ) (f⁺ f⁻ g : Hom S X WQ)
      (sc : ∀ x → BndQ (map g ⟨$⟩ x) →
        SConv (λ n → map (h⁺ n) ⟨$⟩ x) (λ n → map (h⁻ n) ⟨$⟩ x) (map f⁺ ⟨$⟩ x) (map f⁻ ⟨$⟩ x))
      (dom : ∀ n x → (map (h⁺ n) ⟨$⟩ x) + (map (h⁻ n) ⟨$⟩ x) ≤ (map g ⟨$⟩ x))
      (domf : ∀ x → (map f⁺ ⟨$⟩ x) + (map f⁻ ⟨$⟩ x) ≤ (map g ⟨$⟩ x)) (bg : Bnd (∫ᴹ {X} p g)) where

      G : Hom S X WQ
      G = addX {X} g g

      dd ee : ℕ → Hom S X WQ
      dd n = addX {X} (h⁺ n) f⁻
      ee n = addX {X} (h⁻ n) f⁺

      -- every part is below g
      le-h⁺ : ∀ n x → map (h⁺ n) ⟨$⟩ x ≤ map g ⟨$⟩ x
      le-h⁺ n x = ≤-trans ≤-+ʳ (dom n x)

      le-h⁻ : ∀ n x → map (h⁻ n) ⟨$⟩ x ≤ map g ⟨$⟩ x
      le-h⁻ n x = ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (+-comm _ _))) (dom n x)

      le-f⁺ : ∀ x → map f⁺ ⟨$⟩ x ≤ map g ⟨$⟩ x
      le-f⁺ x = ≤-trans ≤-+ʳ (domf x)

      le-f⁻ : ∀ x → map f⁻ ⟨$⟩ x ≤ map g ⟨$⟩ x
      le-f⁻ x = ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (+-comm _ _))) (domf x)

      dom-d : ∀ n x → BndQ (map g ⟨$⟩ x) → map (dd n) ⟨$⟩ x ≤ map G ⟨$⟩ x
      dom-d n x _ = +-mono (le-h⁺ n x) (le-f⁻ x)

      dom-e : ∀ n x → BndQ (map g ⟨$⟩ x) → map (ee n) ⟨$⟩ x ≤ map G ⟨$⟩ x
      dom-e n x _ = +-mono (le-h⁻ n x) (le-f⁺ x)

      bnd-d : ∀ n x → BndQ (map g ⟨$⟩ x) → BndQ (map (dd n) ⟨$⟩ x)
      bnd-d n x b = BndQ-≤ {map (dd n) ⟨$⟩ x} {map G ⟨$⟩ x} (dom-d n x b) (BndQ-add {map g ⟨$⟩ x} {map g ⟨$⟩ x} b b)

      bnd-e : ∀ n x → BndQ (map g ⟨$⟩ x) → BndQ (map (ee n) ⟨$⟩ x)
      bnd-e n x b = BndQ-≤ {map (ee n) ⟨$⟩ x} {map G ⟨$⟩ x} (dom-e n x b) (BndQ-add {map g ⟨$⟩ x} {map g ⟨$⟩ x} b b)

      close-d : ∀ x → BndQ (map g ⟨$⟩ x) → ∀ k →
        Σ ℕ (λ N → ∀ n → N ≤ℕ n → map (dd n) ⟨$⟩ x ≤ (map (ee n) ⟨$⟩ x) + hp k)
      close-d x b k = proj₁ (sc x b k) , λ n le →
        ≤-trans (proj₁ (proj₂ (sc x b k) n le)) (≤-reflexive (+-cong (+-comm _ _) refl))

      close-e : ∀ x → BndQ (map g ⟨$⟩ x) → ∀ k →
        Σ ℕ (λ N → ∀ n → N ≤ℕ n → map (ee n) ⟨$⟩ x ≤ (map (dd n) ⟨$⟩ x) + hp k)
      close-e x b k = proj₁ (sc x b k) , λ n le →
        ≤-trans (≤-reflexive (+-comm _ _)) (proj₂ (proj₂ (sc x b k) n le))

      bG : Bnd (∫ᴹ {X} p G)
      bG = proj₁ bg +ℕ proj₁ bg , ≤-trans (≤-reflexive (∫ᴹ-addX p g g))
        (≤-trans (+-mono (proj₂ bg) (proj₂ bg)) (≤-reflexive (sym (nat-+ (proj₁ bg) (proj₁ bg)))))

      -- the pointwise identity d + (e ∸ d) ≈ e + (d ∸ e) on the cut tests, and its integral
      pn qn : ℕ → Hom S X WQ
      pn = pnH g dd ee bnd-e
      qn = pnH g ee dd bnd-d

      pt-id : ∀ n x → (map (cutH g (dd n)) ⟨$⟩ x) + (map (qn n) ⟨$⟩ x) ≈ (map (cutH g (ee n)) ⟨$⟩ x) + (map (pn n) ⟨$⟩ x)
      pt-id n x = monus-swap (map (cutH g (dd n)) ⟨$⟩ x) (map (cutH g (ee n)) ⟨$⟩ x)
        (rat-bnd _ (bnd-cut g (dd n) x (bnd-d n x))) (rat-bnd _ (bnd-cut g (ee n) x (bnd-e n x)))

      int-id : ∀ n → ∫ᴹ {X} p (cutH g (dd n)) + ∫ᴹ {X} p (qn n) ≈ ∫ᴹ {X} p (cutH g (ee n)) + ∫ᴹ {X} p (pn n)
      int-id n = trans (sym (∫ᴹ-addX p (cutH g (dd n)) (qn n))) (trans
        (∫ᴹ-cong p {addX {X} (cutH g (dd n)) (qn n)} {addX {X} (cutH g (ee n)) (pn n)} (pt-id n))
        (∫ᴹ-addX p (cutH g (ee n)) (pn n)))

      -- the cut does not change the integrals
      cut-d : ∀ n → ∫ᴹ {X} p (cutH g (dd n)) ≈ ∫ᴹ {X} p (h⁺ n) + ∫ᴹ {X} p f⁻
      cut-d n = trans (∫-fin-cut p g (dd n) bg) (∫ᴹ-addX p (h⁺ n) f⁻)

      cut-e : ∀ n → ∫ᴹ {X} p (cutH g (ee n)) ≈ ∫ᴹ {X} p (h⁻ n) + ∫ᴹ {X} p f⁺
      cut-e n = trans (∫-fin-cut p g (ee n) bg) (∫ᴹ-addX p (h⁻ n) f⁺)

      result : SConv (λ n → ∫ᴹ {X} p (h⁺ n)) (λ n → ∫ᴹ {X} p (h⁻ n)) (∫ᴹ {X} p f⁺) (∫ᴹ {X} p f⁻)
      result k = N₁ +ℕ N₂ , λ n le → final-alg _ _ _ _ _ _ k
        (trans (+-cong (sym (cut-d n)) refl) (trans (int-id n) (+-cong (cut-e n) refl)))
        (proj₁ (proj₂ Pk n (ℕP.≤-trans (ℕP.m≤m+n N₁ N₂) le))) (proj₁ (proj₂ Qk n (ℕP.≤-trans (ℕP.m≤n+m N₂ N₁) le)))
        where
          Pk = diff-econv p g G dd ee bG dom-d bnd-e close-d k
          Qk = diff-econv p g G ee dd bG dom-e bnd-d close-e k
          N₁ = proj₁ Pk
          N₂ = proj₁ Qk

    dct-signed : ∀ (p : C.Pre (XW X)) (h⁺ h⁻ : ℕ → Hom S X WQ) (f⁺ f⁻ g : Hom S X WQ) →
      (∀ x → BndQ (map g ⟨$⟩ x) →
        SConv (λ n → map (h⁺ n) ⟨$⟩ x) (λ n → map (h⁻ n) ⟨$⟩ x) (map f⁺ ⟨$⟩ x) (map f⁻ ⟨$⟩ x)) →
      (∀ n x → (map (h⁺ n) ⟨$⟩ x) + (map (h⁻ n) ⟨$⟩ x) ≤ (map g ⟨$⟩ x)) →
      (∀ x → (map f⁺ ⟨$⟩ x) + (map f⁻ ⟨$⟩ x) ≤ (map g ⟨$⟩ x)) →
      Bnd (∫ᴹ {X} p g) →
      SConv (λ n → ∫ᴹ {X} p (h⁺ n)) (λ n → ∫ᴹ {X} p (h⁻ n)) (∫ᴹ {X} p f⁺) (∫ᴹ {X} p f⁻)
    dct-signed p h⁺ h⁻ f⁺ f⁻ g sc dom domf bg = Sg.result p h⁺ h⁻ f⁺ f⁻ g sc dom domf bg

    dct-signed-prob : ∀ (P : Pre X) (h⁺ h⁻ : ℕ → Hom S X WQ) (f⁺ f⁻ : Hom S X WQ) N →
      (∀ x → SConv (λ n → map (h⁺ n) ⟨$⟩ x) (λ n → map (h⁻ n) ⟨$⟩ x) (map f⁺ ⟨$⟩ x) (map f⁻ ⟨$⟩ x)) →
      (∀ n x → (map (h⁺ n) ⟨$⟩ x) + (map (h⁻ n) ⟨$⟩ x) ≤ nat N) → (∀ x → (map f⁺ ⟨$⟩ x) + (map f⁻ ⟨$⟩ x) ≤ nat N) →
      SConv (λ n → ∫ᴹ {X} (ιPre {X} P) (h⁺ n)) (λ n → ∫ᴹ {X} (ιPre {X} P) (h⁻ n))
        (∫ᴹ {X} (ιPre {X} P) f⁺) (∫ᴹ {X} (ιPre {X} P) f⁻)
    dct-signed-prob P h⁺ h⁻ f⁺ f⁻ N sc dom domf = dct-signed (ιPre {X} P) h⁺ h⁻ f⁺ f⁻ (constW {X} (nat N))
      (λ x _ → sc x) dom domf (N , ≤-reflexive (prob-mass P (nat N)))
