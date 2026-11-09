{-# OPTIONS --safe --without-K #-}

-- Bernoulli(½) on a genuine Boolean QBS (`QBS.BoolQ`, `BoolQ = 1Q +Q 1Q`), in which indicators are measurable.
--
--   * `bitB : Func Rˢ ∣ BoolQ ∣`, the first bit of the fair coin, is random: the partition of Cantor space by the first bit
--     realises it as `trueQ` on one piece and `falseQ` on the other (`bitB-random`);
--   * `bernB : Pre BoolQ` is the fair coin pushed along it (the carrier is the first bit);
--   * `ifT a b : STest BoolQ` for `a, b ∈ [0,1]`, positive part `ifQ a b` (`QBS.BoolQ`), and the indicator `indT = ifT 1 0`;
--   * `E-at bernB (ifT a b) ≃ ½·a + ½·b` (`E-at-bernB-if`), in particular `E-at bernB indT ≃ ι ½` (`E-at-bernB-ind`),
--     (the bound arguments are only for the `Bnd` witnesses of `ι`);
--   * `toAQ : Hom BoolQ AQ` (`true ↦ 1`, `false ↦ 0`) pushes `bernB` to the earlier `bern : Pre AQ`
--     (`Inference/ExpectationExamples`): `mapPre toAQ bernB ≈ᵖ bern` (`bernB≈bern`), and `E-at-bernB-id` recovers `E-at-bern`;
--   * a biased coin `bernθ θ : Pre BoolQ` for every `θ ≤ 1`, the indicator `[expansion r ≤ θ]` of the uniform draw
--     (`indB` realises the indicator of any decidable Borel set as a random element of `BoolQ`; `Analysis/Threshold` gives the
--     Borel set), with `E-at (bernθ θ) indT ≃ ι θ` (`E-at-bernθ`) from `UniformCDF.cdf`.
module QBS.Inference.BoolDist where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂; _×_; swap)
open import Data.Unit.Polymorphic using (tt)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (lower)
open import Relation.Binary.Bundles using (Setoid)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (1Q)
open import QBS.Colimits using (Piece; ev)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import QBS.BoolQ as BQ
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Borel.Core using (gen; resp; compl; ⊥-borel; Partition; Pred; Borel; borel-≗)
open import QBS.Borel.Source using (R₁; idxₛ)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Analysis.Threshold using (module Threshold)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.Monad
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
import QBS.Inference.Expectation as EX
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.ExpectationExamples as EE
import QBS.Continuous.UniformCDF as UC
open BQ.BoolOn S

----------------------------------------------------------------------------
-- the first bit as a random element of BoolQ (needs no analysis)

private
  idx : Bool → ℕ
  idx true = 0
  idx false = 1

  idx-0 : ∀ b → idx b ≡ 0 → b ≡ true
  idx-0 true _ = ≡.refl

  idx-1 : ∀ b → idx b ≡ 1 → b ≡ false
  idx-1 false _ = ≡.refl

  idx-big : ∀ b k → idx b ≡ suc (suc k) → ⊥
  idx-big true k ()
  idx-big false k ()

  idx-part : Partition (λ x → idx (x 0))
  idx-part zero = resp (λ x → (λ e → ≡.trans (≡.cong idx e) ≡.refl) , idx-0 (x 0)) (gen 0 true)
  idx-part (suc zero) = resp (λ x → (λ e → ≡.cong idx e) , idx-1 (x 0)) (gen 0 false)
  idx-part (suc (suc k)) = resp (λ x → (λ ()) , idx-big (x 0) k) ⊥-borel

  cP : ℕ → Piece S (1Q S) (1Q S)
  cP zero = inj₁ (constₛ tt , QBS.const-random (1Q S) tt)
  cP (suc _) = inj₂ (constₛ tt , QBS.const-random (1Q S) tt)

  cP-ev : ∀ b r → Setoid._≈_ (QBS.Carrier BoolQ) (boolQ b) (ev S (1Q S) (1Q S) (cP (idx b)) r)
  cP-ev true r = ⊎ʳ.inj₁ ≡.refl
  cP-ev false r = ⊎ʳ.inj₂ ≡.refl

-- the first bit of Cantor space, valued in `BoolQ`
bitB-cong : ∀ {r s : R₁} → Setoid._≈_ (RandomSource.Rˢ S) r s →
  Setoid._≈_ (QBS.Carrier BoolQ) (boolQ (lower r 0)) (boolQ (lower s 0))
bitB-cong {r} {s} e = boolQ-cong {lower r 0} {lower s 0} (lower e 0)

bitB : Func (RandomSource.Rˢ S) (QBS.Carrier BoolQ)
bitB = record { to = λ r → boolQ (lower r 0) ; cong = bitB-cong }

bitB-random : QBS.Random BoolQ bitB
bitB-random = idxₛ (λ r → idx (lower r 0)) idx-part , idx-part , cP , λ r → cP-ev (lower r 0) r

----------------------------------------------------------------------------
-- the indicator of a decidable Borel set of Cantor space, as a random element of BoolQ

flag : ∀ {P : Set} → P ⊎ (P → ⊥) → Bool
flag (inj₁ _) = true
flag (inj₂ _) = false

flag-resp : ∀ {P Q : Set} (d : P ⊎ (P → ⊥)) (e : Q ⊎ (Q → ⊥)) → (P → Q) → (Q → P) → flag d ≡ flag e
flag-resp (inj₁ p) (inj₁ q) f g = ≡.refl
flag-resp (inj₁ p) (inj₂ nq) f g = ⊥-elim (nq (f p))
flag-resp (inj₂ np) (inj₁ q) f g = ⊥-elim (np (g q))
flag-resp (inj₂ np) (inj₂ nq) f g = ≡.refl

private
  flag-0 : ∀ {P : Set} (d : P ⊎ (P → ⊥)) → (idx (flag d) ≡ 0 → P) × (P → idx (flag d) ≡ 0)
  flag-0 (inj₁ p) = (λ _ → p) , (λ _ → ≡.refl)
  flag-0 (inj₂ np) = (λ ()) , (λ p → ⊥-elim (np p))

  flag-1 : ∀ {P : Set} (d : P ⊎ (P → ⊥)) → (idx (flag d) ≡ 1 → P → ⊥) × ((P → ⊥) → idx (flag d) ≡ 1)
  flag-1 (inj₁ p) = (λ ()) , (λ np → ⊥-elim (np p))
  flag-1 (inj₂ np) = (λ _ → np) , (λ _ → ≡.refl)

  flag-big : ∀ {P : Set} (d : P ⊎ (P → ⊥)) k → idx (flag d) ≡ suc (suc k) → ⊥
  flag-big (inj₁ _) k ()
  flag-big (inj₂ _) k ()

  flag-part : ∀ {U : Pred} → Borel U → (dec : ∀ x → U x ⊎ (U x → ⊥)) → Partition (λ x → idx (flag (dec x)))
  flag-part bU dec zero = resp (λ x → swap (flag-0 (dec x))) bU
  flag-part bU dec (suc zero) = resp (λ x → swap (flag-1 (dec x))) (compl bU)
  flag-part bU dec (suc (suc k)) = resp (λ x → (λ ()) , flag-big (dec x) k) ⊥-borel

indB-cong : ∀ {U : Pred} (bU : Borel U) (dec : ∀ x → U x ⊎ (U x → ⊥)) {r s : R₁} → Setoid._≈_ (RandomSource.Rˢ S) r s →
  Setoid._≈_ (QBS.Carrier BoolQ) (boolQ (flag (dec (lower r)))) (boolQ (flag (dec (lower s))))
indB-cong bU dec {r} {s} e = boolQ-cong (flag-resp (dec (lower r)) (dec (lower s))
  (proj₁ (borel-≗ bU (lower e))) (proj₂ (borel-≗ bU (lower e))))

-- `r ↦ true` if the point lies in `U`, else `false`
indB : ∀ {U : Pred} → Borel U → (∀ x → U x ⊎ (U x → ⊥)) → Func (RandomSource.Rˢ S) (QBS.Carrier BoolQ)
indB bU dec = record { to = λ r → boolQ (flag (dec (lower r))) ; cong = indB-cong bU dec }

indB-random : ∀ {U : Pred} (bU : Borel U) (dec : ∀ x → U x ⊎ (U x → ⊥)) → QBS.Random BoolQ (indB bU dec)
indB-random bU dec =
  idxₛ (λ r → idx (flag (dec (lower r)))) (flag-part bU dec) , flag-part bU dec , cP ,
  λ r → cP-ev (flag (dec (lower r))) r

----------------------------------------------------------------------------
-- Bernoulli(½) and its expectations

module BoolDist (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-fun; J-irrel)
  open Integration A using (probClass; I; I-cong)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_; _*_; _+_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-refl;
    ≤-trans; ≤-reflexive; 0-least; *-identityʳ; +-identityʳ; zeroʳ; +-comm; +-identityˡ)
  open Bounded A using (Sg; Bnd; _≃_; ≃-trans; ≃-sym; _+S_; _*S_; finite; ι; ι-+; ι-*; +S-cong)
  open BoundedSignedTests (lemOf lem₁) using (CutQ; STest)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; mk; mk-cong; mapPre; _≈ᵖ_)
  open Pre
  open Measurable A using (Fun; Fun-const; Fun-pre; Fun-ext; sumF; complF; Fun-scale)
  open LevelSets (lemOf lem₁) using (LS)
  open Daniell lem₁ using (L-one)
  open Indicators A (lemOf lem₁) using (I-const; χ-in; χ-out)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open HalfOrder A (lowerRealsArch (lemOf lem₁)) using (half≤1)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open ER.ExpectationResp lem₁ using (E-at; E-resp)
  open EX.Expectation lem₁ using (precompT; E-at-map)
  open EE.ExpectationExamples lem₁ using (E-at-ι; zeroJ; fh; bit; Fun-bit; bit≤1; bern; idT; E-at-bern; sel; bernProbe; b1)

  -- the fair coin pushed along the first bit, as a measure on `BoolQ`
  bernB : Pre BoolQ
  bernB = mk bitB bitB-random fairCoin L-one

  ----------------------------------------------------------------------------
  -- tests on BoolQ: `ifT a b` is `a` on true and `b` on false

  ifT : (a b : ∣A∣) → a ≤ 1# → b ≤ 1# → STest BoolQ
  ifT a b a≤1 b≤1 = record
    { pos = ifQ {CutQ} a b ; neg = constQ {BoolQ} {CutQ} 0# ; bound = 1
    ; pos-bdd = λ { (inj₁ _) → bd a≤1 ; (inj₂ _) → bd b≤1 }
    ; neg-bdd = λ _ → 0-least }
    where bd = λ {c} (le : c ≤ 1#) → ≤-trans le (≤-reflexive (sym (+-identityʳ 1#)))

  -- the indicator of `true`
  indT : STest BoolQ
  indT = ifT 1# 0# ≤-refl 0-least

  -- the values of the indicator
  valT-ind-true : Hom.map (STest.pos indT) ⟨$⟩ trueQ ≡ 1#
  valT-ind-true = ≡.refl

  valT-ind-false : Hom.map (STest.pos indT) ⟨$⟩ falseQ ≡ 0#
  valT-ind-false = ≡.refl

  ----------------------------------------------------------------------------
  -- the integrand `a` after `true`, `b` after `false`

  hB : ∣A∣ → ∣A∣ → R₁ → ∣A∣
  hB a b r = Hom.map (ifQ {CutQ} a b) ⟨$⟩ (bitB ⟨$⟩ r)

  cbit : R₁ → ∣A∣
  cbit r = Hom.map (ifQ {CutQ} 0# 1#) ⟨$⟩ (bitB ⟨$⟩ r)

  bit-cbit : ∀ r → cbit r + bit r ≈ 1#
  bit-cbit r with lower r 0
  ... | true = trans (+-cong refl refl) (trans (+-comm 0# 1#) (+-identityʳ 1#))
  ... | false = +-identityʳ 1#

  -- hB a b = a·bit + b·(1 - bit)
  hB-split : ∀ a b r → hB a b r ≈ a * bit r + b * cbit r
  hB-split a b r with lower r 0
  ... | true = trans (sym (+-identityʳ a)) (+-cong (sym (*-identityʳ a)) (sym (zeroʳ b)))
  ... | false = trans (sym (*-identityʳ b)) (trans (sym (+-identityˡ (b * 1#))) (+-cong (sym (zeroʳ a)) refl))

  hB≤1 : ∀ a b → a ≤ 1# → b ≤ 1# → ∀ r → hB a b r ≤ 1#
  hB≤1 a b a≤1 b≤1 r with lower r 0
  ... | true = a≤1
  ... | false = b≤1

  Fun-hB : ∀ a b → a ≤ 1# → b ≤ 1# → Fun (hB a b)
  Fun-hB a b a≤1 b≤1 = sumF (Fun-scale a a≤1 Fun-bit) (Fun-scale b b≤1 (complF {h = cbit} Fun-bit bit-cbit))
    (hB-split a b) (hB≤1 a b a≤1 b≤1)

  -- the integrand is constant after fixing the first bit
  FB : ∀ a b (a≤1 : a ≤ 1#) (b≤1 : b ≤ 1#) c → Fun (λ x → hB a b (consR c x))
  FB a b a≤1 b≤1 c = Fun-pre {f = consR c} (Fun-hB a b a≤1 b≤1) (measurable-cons c)

  I-after : ∀ a b (a≤1 : a ≤ 1#) (b≤1 : b ≤ 1#) →
    I fairCoin (λ x → hB a b (consR true x)) (FB a b a≤1 b≤1 true) ≈ a
  I-after a b a≤1 b≤1 = trans
    (I-cong fairCoin {h = λ x → hB a b (consR true x)} {h′ = λ _ → a} (λ r → refl)
      (FB a b a≤1 b≤1 true) (Fun-const a a≤1))
    (I-const fairCoin L-one a a≤1)

  I-after′ : ∀ a b (a≤1 : a ≤ 1#) (b≤1 : b ≤ 1#) →
    I fairCoin (λ x → hB a b (consR false x)) (FB a b a≤1 b≤1 false) ≈ b
  I-after′ a b a≤1 b≤1 = trans
    (I-cong fairCoin {h = λ x → hB a b (consR false x)} {h′ = λ _ → b} (λ r → refl)
      (FB a b a≤1 b≤1 false) (Fun-const b b≤1))
    (I-const fairCoin L-one b b≤1)

  -- ∫ hB a b = ½a + ½b
  I-hB : ∀ a b (a≤1 : a ≤ 1#) (b≤1 : b ≤ 1#) → I fairCoin (hB a b) (Fun-hB a b a≤1 b≤1) ≈ half * a + half * b
  I-hB a b a≤1 b≤1 = trans (firstBit-fun (Fun-hB a b a≤1 b≤1))
    (+-cong (*-cong refl (I-after a b a≤1 b≤1)) (*-cong refl (I-after′ a b a≤1 b≤1)))

  J-hB : ∀ a b (a≤1 : a ≤ 1#) (b≤1 : b ≤ 1#) →
    J (m bernB) (λ r → Hom.map (STest.pos (ifT a b a≤1 b≤1)) ⟨$⟩ (α bernB ⟨$⟩ r))
      (Hom.map-random (STest.pos (ifT a b a≤1 b≤1)) {α bernB} (α-random bernB)) ≈ half * a + half * b
  J-hB a b a≤1 b≤1 = trans (J-irrel fairCoin _ (LS (Fun-hB a b a≤1 b≤1)))
    (trans (J-fun fairCoin (Fun-hB a b a≤1 b≤1)) (I-hB a b a≤1 b≤1))

  ----------------------------------------------------------------------------
  -- the expectations

  E-at-bernB-if : ∀ a b (a≤1 : a ≤ 1#) (b≤1 : b ≤ 1#) (fa : Bnd a) (fb : Bnd b) →
    E-at bernB (ifT a b a≤1 b≤1) ≃ ι fh *S ι fa +S ι fh *S ι fb
  E-at-bernB-if a b a≤1 b≤1 fa fb =
    ≃-trans (E-at-ι bernB (ifT a b a≤1 b≤1) (SubSemiring.Is-+ finite (SubSemiring.Is-* finite fh fa) (SubSemiring.Is-* finite fh fb))
      (J-hB a b a≤1 b≤1) (zeroJ bernB))
      (≃-trans (ι-+ (SubSemiring.Is-* finite fh fa) (SubSemiring.Is-* finite fh fb))
        (+S-cong (ι-* fh fa) (ι-* fh fb)))

  -- E[1_true] = ½
  E-at-bernB-ind : E-at bernB indT ≃ ι fh
  E-at-bernB-ind = E-at-ι bernB indT fh
    (trans (J-hB 1# 0# ≤-refl 0-least)
      (trans (+-cong (*-identityʳ half) (zeroʳ half)) (+-identityʳ half)))
    (zeroJ bernB)

  ----------------------------------------------------------------------------
  -- comparison with the earlier `bern : Pre AQ`

  -- `true ↦ 1`, `false ↦ 0`
  toAQ : Hom S BoolQ AQ
  toAQ = ifQ {AQ} (1# , ≤-refl) (0# , 0-least)

  toAQ-bit : ∀ b → proj₁ (Hom.map toAQ ⟨$⟩ boolQ b) ≈ sel b
  toAQ-bit true = refl
  toAQ-bit false = refl

  bernB≈bern : mapPre toAQ bernB ≈ᵖ bern
  bernB≈bern = mk-cong {X = AQ} {α₁ = Hom.map toAQ ∘ₛ bitB} {α₂ = bernProbe}
    (Hom.map-random toAQ {bitB} bitB-random) Fun-bit fairCoin L-one (λ s → toAQ-bit (lower s 0))

  -- the Boolean indicator pulled back along `toAQ` is the identity statistic, so the two expectations agree
  E-at-bernB-toAQ : E-at (mapPre toAQ bernB) idT ≃ E-at bern idT
  E-at-bernB-toAQ = E-resp bernB≈bern idT

  E-at-bernB-id : E-at bernB (precompT toAQ idT) ≃ ι fh
  E-at-bernB-id = ≃-trans (≃-sym step) (≃-trans E-at-bernB-toAQ E-at-bern)
    where
    step : E-at (mapPre toAQ bernB) idT ≃ E-at bernB (precompT toAQ idT)
    step = E-at-map {X = AQ} {Y = BoolQ} toAQ bernB idT

  ----------------------------------------------------------------------------
  -- a biased coin: Bernoulli(θ) for any θ ≤ 1, the indicator `[expansion r ≤ θ]` of the uniform draw

  open UC.UniformCDF lem₁ using (cdf; cdfTest; ι-χ; z₀) renaming (ι to ιP)
  open Threshold (lemOf lem₁) using (Below; Below-borel)
  open Expansion A half hh using (expansion; Fun-expansion; expansion≤1)
  open Uniform lem₁ using (expansionProbe)

  -- the threshold set {x | expansion x ≤ θ} is Borel and decidable (classically)
  belowθ : ∣A∣ → Pred
  belowθ θ = Below expansion θ

  decθ : ∀ θ x → belowθ θ x ⊎ (belowθ θ x → ⊥)
  decθ θ x = lemOf lem₁ (belowθ θ x)

  indθ : ∣A∣ → Func (RandomSource.Rˢ S) (QBS.Carrier BoolQ)
  indθ θ = indB (Below-borel Fun-expansion θ) (decθ θ)

  bernθ : ∣A∣ → Pre BoolQ
  bernθ θ = mk (indθ θ) (indB-random (Below-borel Fun-expansion θ) (decθ θ)) fairCoin L-one

  -- the value of the Boolean indicator is `ι (expansion ≤ θ)` (`ι P` is 1 if P holds, else 0)
  val-flag : ∀ {P : Set} (d : P ⊎ (P → ⊥)) → Hom.map (ifQ {CutQ} 1# 0#) ⟨$⟩ boolQ (flag d) ≈ ιP P
  val-flag (inj₁ p) = sym (χ-in (λ _ → _) z₀ p)
  val-flag (inj₂ np) = sym (χ-out (λ _ → _) z₀ np)

  cdfVal : ∣A∣ → R₁ → ∣A∣
  cdfVal θ r = proj₁ (Hom.map (cdfTest θ) ⟨$⟩ (expansionProbe ⟨$⟩ r))

  Fun-cdfVal : ∀ θ → Fun (cdfVal θ)
  Fun-cdfVal θ = Hom.map-random (cdfTest θ) {expansionProbe} Fun-expansion

  cdfVal≈ind : ∀ θ r → cdfVal θ r ≈ Hom.map (STest.pos indT) ⟨$⟩ (indθ θ ⟨$⟩ r)
  cdfVal≈ind θ r = sym (val-flag (decθ θ (lower r)))

  J-indθ : ∀ θ → θ ≤ 1# →
    J (m (bernθ θ)) (λ r → Hom.map (STest.pos indT) ⟨$⟩ (α (bernθ θ) ⟨$⟩ r))
      (Hom.map-random (STest.pos indT) {α (bernθ θ)} (α-random (bernθ θ))) ≈ θ
  J-indθ θ θ≤1 = trans (J-irrel fairCoin _ (LS Fe))
    (trans (J-fun fairCoin Fe) (trans (I-cong fairCoin (λ r → sym (cdfVal≈ind θ r)) Fe (Fun-cdfVal θ)) (cdf θ θ≤1)))
    where Fe = Fun-ext (cdfVal≈ind θ) (Fun-cdfVal θ)

  -- E[1_true] = θ under Bernoulli(θ)
  E-at-bernθ : ∀ θ (θ≤1 : θ ≤ 1#) → E-at (bernθ θ) indT ≃ ι (b1 θ≤1)
  E-at-bernθ θ θ≤1 = E-at-ι (bernθ θ) indT (b1 θ≤1) (J-indθ θ θ≤1) (zeroJ (bernθ θ))
