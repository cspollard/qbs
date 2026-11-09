{-# OPTIONS --safe --without-K #-}

-- The decoding of the digit code of `[0,∞]` (`Continuous/DigitCode`): `decPt r = A r + E r`, where
--   * `A r = ∑ᵢ [the first i+1 bits of r are true]` is the length of the leading run of `true`s (∞ on the all-true point);
--   * `E r` is the binary expansion of the bits after the first `false` (`Borel/Lead.lead` finds it).
-- `Meas-dec`: it is threshold-measurable (a sum, and a gluing of the expansions along the partition `lead`).
-- `decode-digits`: `decPt (digits x) ≈ x`.  For finite x ∈ [k, k+1) the code is `trueᵏ false c`, with `k + expansion c ≈ x`
-- (`expansion-claim`: the partial sums of c are the dyadic points `mN c k N / 2ᴺ`, all ≤ x and within 2⁻ᴺ of x, by
-- `DigitCut.below-dec` and the Archimedean closure); for infinite x the run is infinite and both sides are `[0,∞]`.
module QBS.Continuous.DigitDecode where

open import Level using (lift; lower)
open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; zero; suc; s≤s)
import Data.Nat.Base as ℕ
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁)
import Data.Sum.Base as Sum
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; subst)

open import QBS.Classical using (LEM₀)
open import QBS.Borel.Core using (Cantor; gen)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cells using (Ones; dropC)
open import QBS.Borel.Lead using (Pre; module Lead)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (_⊑_; mk⊑; ⊑-refl)
open _⊑_ using (ap)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.DigitCut using (module DigitCut)
open import QBS.Continuous.DigitStream using (module DigitStream)

module DigitDecode (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; 1#; ≤-refl; ≤-trans; ≤-reflexive; ≤-antisym; ≤-+ʳ; +-mono; +-cong; +-comm)
  open OmegaSemiring A using (+-identityʳ; *-identityʳ; ⨆-const-from; +-⨆; ⨆-lub; ⨆-ub; ⨆-cong; Increasing)
    renaming (Carrier to ∣A∣)
  open Meas lem using (Meas; Meas-⊕; Meas-const; Meas-⨆; Meas-glue; Meas-pre)
  open LevelSets lem using (LS)
  open Indicators A lem using (χ; χ-in; χ-out; Fun-χ)
  open Series A using (psum; ∑ᶠ; psum≤∑ᶠ; psum-inc)
  open Exp A using (natE)
  open Arch (lowerRealsArch lem) using (half; arch) renaming (half+half to hh)
  open Expansion A half hh using (expansion; Fun-expansion; part; part-inc; expansion≤1)
  open AlgDigit A half hh using (part-mN; part-resp; dy-succ; mN)
  open Intervals lem using (Ge; dy)
  open DigitCut lem using (below-dec; nat-big)
  open DigitStream lem
  open Lead lem using (lead; leadW-back; Ex; borelPre; lead-partition)

  ----------------------------------------------------------------------------
  -- the decoding and its measurability

  aPt : R₁ → ∣A∣
  aPt r = ∑ᶠ (λ i → χ (Pre (suc i)) r)

  ePt : R₁ → ∣A∣
  ePt r = expansion (lift (dropC (suc (lead (lower r))) (lower r)))

  decPt : R₁ → ∣A∣
  decPt r = aPt r + ePt r

  Meas-psum : ∀ N → Meas (λ r → psum (λ i → χ (Pre (suc i)) r) N)
  Meas-psum zero = Meas-const 0#
  Meas-psum (suc N) =
    Meas-⊕ {λ r → psum (λ i → χ (Pre (suc i)) r) N} {λ r → χ (Pre (suc N)) r}
           (Meas-psum N) (LS (Fun-χ (borelPre (suc N))))

  Meas-aPt : Meas aPt
  Meas-aPt = Meas-⨆ {aPt} (λ N r → psum (λ i → χ (Pre (suc i)) r) N) Meas-psum (λ r → ⊑-refl , ⊑-refl)

  Meas-ePt : Meas ePt
  Meas-ePt = Meas-glue {λ r → lead (lower r)} {λ k r → expansion (lift (dropC (suc k) (lower r)))} lead-partition
    (λ k → Meas-pre {expansion} {λ r → lift (dropC (suc k) (lower r))} (LS Fun-expansion) (λ n b → gen (ℕ._+_ (suc k) n) b))

  Meas-dec : Meas decPt
  Meas-dec = Meas-⊕ {aPt} {ePt} Meas-aPt Meas-ePt

  ----------------------------------------------------------------------------
  -- the expansion of the digits after the integer part

  expansion-resp : ∀ {c d : Cantor} → (∀ n → c n ≡ d n) → expansion (lift c) ≈ expansion (lift d)
  expansion-resp {c} {d} e = ⨆-cong (part-inc (lift c)) (part-inc (lift d)) (part-resp e)

  expansion-claim : ∀ x k → Tgt 0 k x → natE k + expansion (lift (out x (fr zero k))) ≈ x
  expansion-claim x k T = ≤-antisym le ge
    where
      c = out x (fr zero k)
      r = lift c
      incK : Increasing (λ N → natE k + part N r)
      incK N = +-mono ≤-refl (part-inc r N)
      inv : ∀ N → Tgt N (mN c k N) x
      inv N = fr-inv x N zero k N (sym (ℕ.+-identityʳ N)) T
      le : natE k + expansion r ≤ x
      le = ≤-trans (≤-reflexive (+-⨆ (natE k) (λ N → part N r) (part-inc r) incK))
        (⨆-lub _ incK (λ N → ≤-trans (≤-reflexive (part-mN N k c)) (mk⊑ (proj₁ (inv N)))))
      ge : x ≤ natE k + expansion r
      ge = arch (λ n → ≤-trans (below-dec (mN c k n) n x (proj₂ (inv n)))
        (≤-trans (≤-reflexive (dy-succ (mN c k n) n))
          (≤-trans (+-mono (≤-reflexive (OmegaSemiring.sym A (part-mN n k c))) ≤-refl)
            (+-mono (+-mono ≤-refl (⨆-ub (λ N → part N r) (part-inc r) n)) ≤-refl))))

  ----------------------------------------------------------------------------
  -- the leading run

  ones-pre : ∀ k y → Ones k y → Pre k y
  ones-pre zero y _ i ()
  ones-pre (suc k) y (e , o) zero _ = e
  ones-pre (suc k) y (e , o) (suc i) (s≤s lt) = ones-pre k (dropC 1 y) o i lt

  -- a run of exactly k ones: the sum is `natE k`
  A-fin : ∀ (y : Cantor) k → Pre k y → y k ≡ false → aPt (lift y) ≈ natE k
  A-fin y k pre yk = ⨆-const-from (psum t) (psum-inc t) k ps-ge
    where
      t : ℕ → ∣A∣
      t i = χ (Pre (suc i)) (lift y)
      t-in : ∀ i → suc i ℕ.≤ k → t i ≈ 1#
      t-in i le = χ-in (Pre (suc i)) (lift y) (λ j j<si → pre j (ℕ.<-≤-trans j<si le))
      t-out : ∀ i → k ℕ.≤ i → t i ≈ 0#
      t-out i le = χ-out (Pre (suc i)) (lift y) (λ p → bad (trans (sym (p k (s≤s le))) yk))
        where bad : true ≡ false → ⊥
              bad ()
      ps-lt : ∀ N → N ℕ.≤ k → psum t N ≈ natE N
      ps-lt zero le = OmegaSemiring.refl A
      ps-lt (suc N) le = +-cong (ps-lt N (ℕ.≤-trans (ℕ.n≤1+n N) le)) (t-in N le)
      ps-ge : ∀ n → k ℕ.≤′ n → psum t n ≈ natE k
      ps-ge n ℕ.≤′-refl = ps-lt k ℕ.≤-refl
      ps-ge (suc n) (ℕ.≤′-step h) = OmegaSemiring.trans A (+-cong (ps-ge n h) (t-out n (ℕ.≤′⇒≤ h))) (+-identityʳ _)

  -- the all-true point: the partial sums are `natE N`
  A-top : ∀ (y : Cantor) → (∀ i → y i ≡ true) → ∀ N → psum (λ i → χ (Pre (suc i)) (lift y)) N ≈ natE N
  A-top y top zero = OmegaSemiring.refl A
  A-top y top (suc N) = +-cong (A-top y top N) (χ-in (Pre (suc N)) (lift y) (λ j _ → top j))

  ----------------------------------------------------------------------------
  -- decoding the code

  dec-le : ∀ x → (∀ k → Ge (natE k) x) → decPt (lift (digits x)) ≤ x
  dec-le x top =
    ≤-trans (+-mono ≤-refl (expansion≤1 _)) (≤-trans (≤-reflexive (+-comm (aPt (lift y)) 1#))
      (≤-trans (≤-reflexive (+-⨆ 1# (psum t) (psum-inc t) inc′))
        (⨆-lub _ inc′ (λ N → ≤-trans (≤-reflexive (step N)) (mk⊑ (top (suc N)))))))
    where
      y = digits x
      t : ℕ → ∣A∣
      t i = χ (Pre (suc i)) (lift y)
      ps = A-top y (top-un x top zero)
      inc′ : Increasing (λ N → 1# + psum t N)
      inc′ N = +-mono ≤-refl (psum-inc t N)
      step : ∀ N → 1# + psum t N ≈ natE (suc N)
      step N = OmegaSemiring.trans A (+-cong (OmegaSemiring.refl A) (ps N)) (+-comm 1# (natE N))

  dec-ge : ∀ x → (∀ k → Ge (natE k) x) → x ≤ decPt (lift (digits x))
  dec-ge x top = ≤-trans xA ≤-+ʳ
    where
      y = digits x
      t : ℕ → ∣A∣
      t i = χ (Pre (suc i)) (lift y)
      ps = A-top y (top-un x top zero)
      xA : x ≤ aPt (lift y)
      xA = mk⊑ (λ q _ → fin q (nat-big q))
        where fin : ∀ q → Σ ℕ (λ k → _) → _
              fin q (k , qk) = ap (psum≤∑ᶠ t k) q (ap (≤-reflexive (OmegaSemiring.sym A (ps k))) q qk)

  decode-top : ∀ x → (∀ k → Ge (natE k) x) → decPt (lift (digits x)) ≈ x
  decode-top x top = ≤-antisym (dec-le x top) (dec-ge x top)

  decode-fin : ∀ x k → Ge (natE k) x → (Ge (natE (suc k)) x → ⊥) → decPt (lift (digits x)) ≈ x
  decode-fin x k gk ng = OmegaSemiring.trans A (+-cong A≈ E≈) (expansion-claim x k T0)
    where
      y = digits x
      ur = un-run x k zero k refl (ge0 x) gk ng
      pre = ones-pre k y (proj₁ (proj₁ ur))
      yk = proj₂ (proj₁ ur)
      eq : lead y ≡ k
      eq = leadW-back k y (lem (Ex y)) (inj₁ (pre , yk))
      A≈ : aPt (lift y) ≈ natE k
      A≈ = A-fin y k pre yk
      E≈ : ePt (lift y) ≈ expansion (lift (out x (fr zero k)))
      E≈ = expansion-resp (λ i → subst (λ t → y (ℕ._+_ (suc t) i) ≡ out x (fr zero k) i) (sym eq) (proj₂ ur i))
      T0 : Tgt 0 k x
      T0 = (λ q m → gk q (ap (≤-reflexive (*-identityʳ (natE k))) q m))
         , (λ g → ng (λ q m → g q (ap (≤-reflexive (OmegaSemiring.sym A (*-identityʳ (natE k + 1#)))) q m)))

  decode-digits : ∀ x → decPt (lift (digits x)) ≈ x
  decode-digits x = Sum.[ decode-top x , (λ ntop → fin (floor-ex x ntop)) ]′ (lem (∀ k → Ge (natE k) x))
    where fin : Σ ℕ (λ k → Ge (natE k) x × (Ge (natE (suc k)) x → ⊥)) → decPt (lift (digits x)) ≈ x
          fin (k , gk , ng) = decode-fin x k gk ng
