{-# OPTIONS --safe --without-K #-}

-- Signed tests, weights and product measures for exponential families (plan 07, item 59; helper for
-- `Continuous/ExpFamily`).
--   * `f ≈T g`: both parts agree pointwise (`≈` on [0, ∞], so transitive even where the parts are infinite); it gives
--     `f ≐ g` (`≈T⇒≐`) and equal weights `expWT f`, `expWT g` with no finiteness (`expWT-≈T`);
--   * `scaleT` distributes over `+T` and commutes with precomposition, and kills the zero test (`scaleT-+T`, `scaleT-∘T`,
--     `scaleT-0`), and the zero scalar kills every test (`scaleT-0S`), all up to `≈T`;
--   * weights of sums: `expWT-+T` (e^{f + g} ≈ e^{f} e^{g} pointwise, for `FinT f`, `FinT g`) and `expWT-0`;
--   * re-exported from `Continuous/ProdReweight`: `prod-reweight`, `prod-scale`, `reweight-cong`; and from
--     `Continuous/FinTest`: `FinT-+T`, `FinT-scaleT`, `FinT-constT`, `FinT-∘T`;
--   * logarithms: `PosQ-resp`, `BndQ-resp`, `logS-cong` (any proofs), and `logS-∏ⁿ`, log xᴺ ≃ N · log x
--     (`ExpFamAlg.scaleA`), with `PosQ-∏ⁿ`, `BndQ-∏ⁿ`.
-- Route: the part identities are `ExpFamilyAlg.scale-+-alg` pointwise; `expWT-+T` is `ExpWeight.expW-+` at the
-- pointwise signed values `ExpWeight.atSg`; `+T-interchange` is `Algebra.Properties.CommutativeSemigroup.interchange`;
-- `logS-cong` from `SignedLog.logP-cong` and `logN-cong`; `logS-∏ⁿ` by induction on N from `SignedLog.log-mul` and
-- `log-one`.
module QBS.Continuous.ExpFamilyAux where

open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Algebra.Properties.CommutativeSemigroup using (interchange)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut; _⊑_)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.ExpFamAlg using (module ExpFamAlg)
open import QBS.Analysis.ExpLower using (expC-cong)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.ExpWeight using (module ExpWeight)
open import QBS.Continuous.ExpFamilyAlg using (module ExpFamilyAlg)
open import QBS.Continuous.ProdReweight using (module ProdReweight)
open import QBS.Continuous.FinTest using (module FinTest)

module ExpFamilyAux (lem₁ : LEM₁) where
  private
    lem = lemOf lem₁
    A = Lebesgue.A lem
  open OmegaSemiring A using (_≈_; _*_; 1#; refl; sym; trans; +-cong; *-cong; commutativeSemiring;
    +-commutativeSemigroup)
  open Bounded A using (Sg; _≃_; 0S; signedRing; finite; ≃-refl; ≃-trans; +S-cong; mk≃)
  open Sg
  open SubSemiring finite using (Is-0)
  open NegExp lem using (negExp; negExp-anti)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; FinT; _≐_; _+T_; scaleT; constT; _∘T_)
  open SignedLog lem₁ using (PosQ; logS; logP-cong; logN-cong; log-mul; log-one; PosQ-mul; BndQ-mul; PosQ-one;
    BndQ-one)
  open FinProd lem₁ using (∏ⁿ)
  open ExpWeight lem₁ using (expWT; expW-+; expW-0; atSg)
  open ExpFamAlg signedRing using (scaleA)
  open ExpFamilyAlg commutativeSemiring using (scale-+-alg; scale-0-alg; zero-scale-alg; +-0-alg)
  open ProdReweight lem public using (reweight-cong; prod-reweight; prod-scale)
  open FinTest lem₁ public using (FinT-+T; FinT-scaleT; FinT-constT; FinT-∘T)
  open Hom
  open _⊑_

  ----------------------------------------------------------------------------
  -- equality of both parts

  infix 4 _≈T_
  _≈T_ : ∀ {X : QBS S} → SgT X → SgT X → Set₁
  f ≈T g = ∀ x → (at⁺ f x ≈ at⁺ g x) × (at⁻ f x ≈ at⁻ g x)

  ≈T-refl : ∀ {X : QBS S} {f : SgT X} → f ≈T f
  ≈T-refl x = refl , refl

  ≈T-sym : ∀ {X : QBS S} {f g : SgT X} → f ≈T g → g ≈T f
  ≈T-sym e x = sym (proj₁ (e x)) , sym (proj₂ (e x))

  ≈T-trans : ∀ {X : QBS S} {f g h : SgT X} → f ≈T g → g ≈T h → f ≈T h
  ≈T-trans e e′ x = trans (proj₁ (e x)) (proj₁ (e′ x)) , trans (proj₂ (e x)) (proj₂ (e′ x))

  ≈T⇒≐ : ∀ {X : QBS S} {f g : SgT X} → f ≈T g → f ≐ g
  ≈T⇒≐ e x = +-cong (proj₁ (e x)) (sym (proj₂ (e x)))

  +T-≈T : ∀ {X : QBS S} {f f′ g g′ : SgT X} → f ≈T f′ → g ≈T g′ → f +T g ≈T f′ +T g′
  +T-≈T e e′ x = +-cong (proj₁ (e x)) (proj₁ (e′ x)) , +-cong (proj₂ (e x)) (proj₂ (e′ x))

  +T-interchange : ∀ {X : QBS S} (a b c d : SgT X) → (a +T b) +T (c +T d) ≈T (a +T c) +T (b +T d)
  +T-interchange a b c d x = interchange +-commutativeSemigroup (at⁺ a x) (at⁺ b x) (at⁺ c x) (at⁺ d x)
                           , interchange +-commutativeSemigroup (at⁻ a x) (at⁻ b x) (at⁻ c x) (at⁻ d x)

  +T-0 : ∀ {X : QBS S} → constT {X} 0S ≈T constT {X} 0S +T constT {X} 0S
  +T-0 x = +-0-alg , +-0-alg

  ----------------------------------------------------------------------------
  -- scaling by a signed constant

  scaleT-+T : ∀ {X : QBS S} (c : Sg) (f g : SgT X) → scaleT c (f +T g) ≈T scaleT c f +T scaleT c g
  scaleT-+T c f g x = scale-+-alg (pos c) (neg c) (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x)
                    , scale-+-alg (pos c) (neg c) (at⁻ f x) (at⁺ f x) (at⁻ g x) (at⁺ g x)

  scaleT-∘T : ∀ {X Y : QBS S} (c : Sg) (f : SgT Y) (φ : Hom S X Y) → scaleT c (f ∘T φ) ≈T scaleT c f ∘T φ
  scaleT-∘T c f φ x = refl , refl

  scaleT-0 : ∀ {X : QBS S} (c : Sg) → scaleT c (constT {X} 0S) ≈T constT {X} 0S
  scaleT-0 c x = scale-0-alg (pos c) (neg c) , scale-0-alg (pos c) (neg c)

  scaleT-0S : ∀ {X : QBS S} (f : SgT X) → scaleT 0S f ≈T constT {X} 0S
  scaleT-0S f x = zero-scale-alg (at⁺ f x) (at⁻ f x) , zero-scale-alg (at⁻ f x) (at⁺ f x)

  ----------------------------------------------------------------------------
  -- weights

  expWT-≈T : ∀ {X : QBS S} {f g : SgT X} → f ≈T g → _≈H_ S (expWT f) (expWT g)
  expWT-≈T e {x} = *-cong (expC-cong lem (proj₁ (e x))) (negExp-anti (proj₂ (proj₂ (e x))) , negExp-anti (proj₁ (proj₂ (e x))))

  expWT-+T : ∀ {X : QBS S} {f g : SgT X} → FinT f → FinT g → ∀ x →
    Func.to (map (expWT (f +T g))) x ≈ Func.to (map (expWT f)) x * Func.to (map (expWT g)) x
  expWT-+T {f = f} {g} ff fg x = expW-+ (atSg f ff x) (atSg g fg x)

  expWT-0 : ∀ {X : QBS S} x → Func.to (map (expWT (constT {X} 0S))) x ≈ 1#
  expWT-0 x = expW-0

  ----------------------------------------------------------------------------
  -- logarithms

  PosQ-resp : ∀ {x y : Cut} → x ≈ y → PosQ x → PosQ y
  PosQ-resp e (q , 0<q , m) = q , 0<q , ap (proj₁ e) q m

  BndQ-resp : ∀ {x y : Cut} → x ≈ y → BndQ x → BndQ y
  BndQ-resp e (M , f) = M , λ r m → f r (ap (proj₂ e) r m)

  logS-cong : ∀ {x y : Cut} (px : PosQ x) (bx : BndQ x) (py : PosQ y) (by : BndQ y) → x ≈ y → logS x px bx ≃ logS y py by
  logS-cong px bx py by e = mk≃ _ Is-0 (+-cong (+-cong (logP-cong e) (sym (logN-cong e))) refl)

  PosQ-∏ⁿ : ∀ N {x : Cut} → PosQ x → PosQ (∏ⁿ N (λ _ → x))
  PosQ-∏ⁿ zero px = PosQ-one
  PosQ-∏ⁿ (suc N) {x} px = PosQ-mul {x} {∏ⁿ N (λ _ → x)} px (PosQ-∏ⁿ N px)

  BndQ-∏ⁿ : ∀ N {x : Cut} → BndQ x → BndQ (∏ⁿ N (λ _ → x))
  BndQ-∏ⁿ zero bx = BndQ-one
  BndQ-∏ⁿ (suc N) {x} bx = BndQ-mul {x} {∏ⁿ N (λ _ → x)} bx (BndQ-∏ⁿ N bx)

  logS-∏ⁿ : ∀ N {x : Cut} (px : PosQ x) (bx : BndQ x) (pN : PosQ (∏ⁿ N (λ _ → x))) (bN : BndQ (∏ⁿ N (λ _ → x))) →
    logS (∏ⁿ N (λ _ → x)) pN bN ≃ scaleA N (logS x px bx)
  logS-∏ⁿ zero px bx pN bN = ≃-trans (logS-cong pN bN PosQ-one BndQ-one refl) log-one
  logS-∏ⁿ (suc N) {x} px bx pN bN =
    ≃-trans (logS-cong pN bN (PosQ-mul px pN′) (BndQ-mul bx bN′) refl)
      (≃-trans (log-mul x _ px pN′ bx bN′) (+S-cong ≃-refl (logS-∏ⁿ N px bx pN′ bN′)))
    where
      pN′ = PosQ-∏ⁿ N px
      bN′ = BndQ-∏ⁿ N bx
