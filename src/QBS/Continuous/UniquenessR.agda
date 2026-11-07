{-# OPTIONS --safe --without-K #-}

-- Uniqueness of s-finite measures on Cantor space `ℛ = Probes.ℛQ S`, in the σ-finite form.  (The main result `uniqR` is the last
-- definition of the file; the module is about Cantor space ℛ, not the real line.)  Cantor space is the disjoint union of the blocks `Blk k = {trueᵏ false …}` and
-- the all-true point `Top` (`Borel/Cells`).  Two measures `μ ν : Pre (XW ℛ)` are equal (`uniqR : μ ≈ᴹ ν`) when
--   * they agree on every cell `Cell k w` (`agreeCell`),
--   * each block has finite μ-mass (`finBlk`), and
--   * they agree on `Top` (`agreeTop`).
-- Route.
--   * `∫ᴹ-split`: every test splits as its part on `Top` plus the series of its parts on the blocks.
--   * `agree-blkCyl`: on a block, agreement on cells gives agreement on every cylinder (`Cells.cyl-refine`).
--   * `agree-blk`: on a block, agreement on cylinders gives agreement on every test.  The part of `p` on the block is
--     the weighted pushforward of `m p` with weight `w · χ Blk` along the probe of p, which has finite mass, so
--     `Analysis/UniquenessWeighted.uniqW` applies.
--   * `agree-top`: `Top` is a single point, so the part of a test g on it is `g(all-true)` times the mass of `Top`.
module QBS.Continuous.UniquenessR where

open import Level using (lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.List.Base using (_∷_; []; length)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
import QBS.Probes as Probes
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Core using (Borel; Cantor; Pred; Measurable)
open import QBS.Borel.Source using (R₁) renaming (down to downR)
open import QBS.Borel.PiLambda using (Cyl; cylTop; Cyl-∩; _∩ᵖ_)
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Borel.Cells using (Word; Blk; Cell; Top; cylBlk; borelBlk; borelCell; borelTop; Ones; Match; dropC;
  blk-unique; top-blk; true≢false; cyl-refine; cylCell)
open import QBS.Borel.Lead using (module Lead)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.JSum using (module JSum)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.UniquenessWeighted using (module UniquenessWeighted)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)

module UniquenessR (lem : LEM₀) where
  open Lebesgue lem using (A; J; J-add; J-scale; J-cong)
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; *-assoc; *-comm; *-identityˡ;
    *-identityʳ; zeroˡ; zeroʳ; +-identityˡ; +-identityʳ; *-commutativeSemigroup; ≤-resp) renaming (Carrier to ∣A∣)
  open Series A using (∑ᶠ; ∑ᶠ-zero; ∑ᶠ-single; ∑ᶠ-cong)
  open Meas lem using (Meas; Meas-⊕; Meas-⊗; Meas-const; Meas-pre; Meas-resp)
  open LevelSets lem using (LS)
  open JSum lem using (J-∑; Meas-∑)
  open Lead lem using (lead; Fib; Ex; leadW-fwd)
  open Bounded A using (Bnd)
  open Indicators A lem using (χ; Fun-χ; χ-in; χ-out; χ-cong; case)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; _≈ᴹ_; ψ; mψ; ∫ᴹ-cong; module C)
  open C using (Pre)
  open C.Pre
  open SFiniteReweight lem using (mulH)
  open UniquenessWeighted lem using (uniqW; Jw; Mw; χM)
  open QBS
  open Hom

  ℛ : QBS S
  ℛ = Probes.ℛQ S

  -- the indicator test of a Borel set of Cantor space
  χR : ∀ {U} → Borel U → Hom S ℛ WQ
  χR {U} b = Probes.probe S {WQ} {record { to = χ U ; cong = λ e → Meas-resp {χ U} (LS (Fun-χ b)) (lower e) }} (LS (Fun-χ b))

  χR-pt : ∀ {U} (b : Borel U) r → map (χR b) ⟨$⟩ r ≈ χ U r
  χR-pt b r = refl

  -- the part of a test on the all-true point, and on the k-th block
  onTop : Hom S ℛ WQ → Hom S ℛ WQ
  onTop g = mulH {ℛ} (χR borelTop) g

  onBlk : ℕ → Hom S ℛ WQ → Hom S ℛ WQ
  onBlk k g = mulH {ℛ} (χR (borelBlk k)) g

  ----------------------------------------------------------------------------
  -- a sequence is all-true or in a block

  pre⇒ones : ∀ n (x : Cantor) → (∀ i → i < n → x i ≡.≡ true) → Ones n x
  pre⇒ones zero x h = tt
  pre⇒ones (suc n) x h = h zero z<s , pre⇒ones n (dropC 1 x) (λ i lt → h (suc i) (s<s lt))

  top-or-blk : ∀ c → Top c ⊎ Σ ℕ (λ k → Blk k c)
  top-or-blk c = conv (leadW-fwd (lead c) c (lem (Ex c)) ≡.refl)
    where
      conv : Fib (lead c) c → Top c ⊎ Σ ℕ (λ k → Blk k c)
      conv (inj₁ (p , f)) = inj₂ (lead c , pre⇒ones _ c p , f)
      conv (inj₂ (_ , z)) = inj₁ z

  -- the pointwise value of a weighted test
  onTop-pt : ∀ g x → map (onTop g) ⟨$⟩ x ≈ χ Top x * (map g ⟨$⟩ x)
  onTop-pt g x = *-cong (χR-pt borelTop x) refl

  onBlk-pt : ∀ k g x → map (onBlk k g) ⟨$⟩ x ≈ χ (Blk k) x * (map g ⟨$⟩ x)
  onBlk-pt k g x = *-cong (χR-pt (borelBlk k) x) refl

  split-pt : ∀ (w gx : ∣A∣) (x : R₁) →
    w * gx ≈ w * (χ Top x * gx) + ∑ᶠ (λ k → w * (χ (Blk k) x * gx))
  split-pt w gx x = go (top-or-blk (lower x))
    where
      z0 : ∀ {a} → a ≈ 0# → w * (a * gx) ≈ 0#
      z0 e = trans (*-cong refl (trans (*-cong e refl) (zeroˡ gx))) (zeroʳ w)
      go : Top (lower x) ⊎ Σ ℕ (λ k → Blk k (lower x)) → _
      go (inj₁ t) = sym (trans (+-cong (*-cong refl (*-cong (χ-in Top x t) refl)) (∑ᶠ-zero
        (λ k → z0 (χ-out (Blk k) x (λ b → top-blk t b))))) (trans (+-identityʳ _) (*-cong refl (*-identityˡ gx))))
      go (inj₂ (j , b)) = sym (trans (+-cong (z0 (χ-out Top x (λ t → top-blk t b))) (∑ᶠ-single j
        (λ n ne → z0 (χ-out (Blk n) x (λ bn → ne (blk-unique bn b)))))) (trans (+-identityˡ _)
        (*-cong refl (trans (*-cong (χ-in (Blk j) x b) refl) (*-identityˡ gx)))))

  -- a pointwise sum over the words of a given length
  sumW : ℕ → (Word → ∣A∣) → ∣A∣
  sumW zero f = f []
  sumW (suc n) f = sumW n (λ u → f (true ∷ u)) + sumW n (λ u → f (false ∷ u))

  Meas-sumW : ∀ n (F : Word → R₁ → ∣A∣) → (∀ u → Meas (F u)) → Meas (λ r → sumW n (λ u → F u r))
  Meas-sumW zero F mF = mF []
  Meas-sumW (suc n) F mF = Meas-⊕ {λ r → sumW n (λ u → F (true ∷ u) r)} {λ r → sumW n (λ u → F (false ∷ u) r)}
    (Meas-sumW n (λ u → F (true ∷ u)) (λ u → mF (true ∷ u))) (Meas-sumW n (λ u → F (false ∷ u)) (λ u → mF (false ∷ u)))

  J-sumW : ∀ mm n (F : Word → R₁ → ∣A∣) (mF : ∀ u → Meas (F u)) →
    J mm (λ r → sumW n (λ u → F u r)) (Meas-sumW n F mF) ≈ sumW n (λ u → J mm (F u) (mF u))
  J-sumW mm zero F mF = refl
  J-sumW mm (suc n) F mF = trans
    (J-add mm {λ r → sumW n (λ u → F (true ∷ u) r)} {λ r → sumW n (λ u → F (false ∷ u) r)}
      (Meas-sumW n (λ u → F (true ∷ u)) (λ u → mF (true ∷ u))) (Meas-sumW n (λ u → F (false ∷ u)) (λ u → mF (false ∷ u))))
    (+-cong (J-sumW mm n (λ u → F (true ∷ u)) (λ u → mF (true ∷ u)))
            (J-sumW mm n (λ u → F (false ∷ u)) (λ u → mF (false ∷ u))))

  sumW-cong : ∀ n {f g} → (∀ u → length u ≡.≡ n → f u ≈ g u) → sumW n f ≈ sumW n g
  sumW-cong zero e = e [] ≡.refl
  sumW-cong (suc n) e = +-cong (sumW-cong n (λ u l → e (true ∷ u) (≡.cong suc l)))
                               (sumW-cong n (λ u l → e (false ∷ u) (≡.cong suc l)))

  sumW-zero : ∀ n {f} → (∀ u → length u ≡.≡ n → f u ≈ 0#) → sumW n f ≈ 0#
  sumW-zero zero e = e [] ≡.refl
  sumW-zero (suc n) e = trans (+-cong (sumW-zero n (λ u l → e (true ∷ u) (≡.cong suc l)))
    (sumW-zero n (λ u l → e (false ∷ u) (≡.cong suc l)))) (+-identityˡ 0#)

  -- exactly one word of each length matches the sequence z
  sumW-unique : ∀ n {f} (z : Cantor) c → (∀ u → length u ≡.≡ n → Match u z → f u ≈ c) →
    (∀ u → length u ≡.≡ n → (Match u z → ⊥) → f u ≈ 0#) → sumW n f ≈ c
  sumW-unique zero z c e₁ e₂ = e₁ [] ≡.refl tt
  sumW-unique (suc n) {f} z c e₁ e₂ with z zero in eq
  ... | true = trans (+-cong
        (sumW-unique n (dropC 1 z) c (λ u l m → e₁ (true ∷ u) (≡.cong suc l) (eq , m))
                                     (λ u l nm → e₂ (true ∷ u) (≡.cong suc l) (λ (_ , m) → nm m)))
        (sumW-zero n (λ u l → e₂ (false ∷ u) (≡.cong suc l) (λ (p , _) → true≢false (≡.trans (≡.sym eq) p)))))
      (+-identityʳ c)
  ... | false = trans (+-cong
        (sumW-zero n (λ u l → e₂ (true ∷ u) (≡.cong suc l) (λ (p , _) → true≢false (≡.trans (≡.sym p) eq))))
        (sumW-unique n (dropC 1 z) c (λ u l m → e₁ (false ∷ u) (≡.cong suc l) (eq , m))
                                     (λ u l nm → e₂ (false ∷ u) (≡.cong suc l) (λ (_ , m) → nm m))))
      (+-identityˡ c)

  -- every test splits along the all-true point and the blocks (excluded middle: a sequence is all-true or in a block)
  ∫ᴹ-split : ∀ (p : Pre (XW ℛ)) (g : Hom S ℛ WQ) → ∫ᴹ {ℛ} p g ≈ ∫ᴹ {ℛ} p (onTop g) + ∑ᶠ (λ k → ∫ᴹ {ℛ} p (onBlk k g))
  ∫ᴹ-split p g = trans
    (J-cong (m p) (mψ {ℛ} p g) (Meas-⊕ {ψ {ℛ} p (onTop g)} {λ r → ∑ᶠ (λ k → ψ {ℛ} p (onBlk k g) r)}
      (mψ {ℛ} p (onTop g)) (Meas-∑ (λ k → ψ {ℛ} p (onBlk k g)) (λ k → mψ {ℛ} p (onBlk k g)))) pt)
    (trans (J-add (m p) {ψ {ℛ} p (onTop g)} {λ r → ∑ᶠ (λ k → ψ {ℛ} p (onBlk k g) r)} (mψ {ℛ} p (onTop g))
      (Meas-∑ (λ k → ψ {ℛ} p (onBlk k g)) (λ k → mψ {ℛ} p (onBlk k g))))
      (+-cong refl (J-∑ (m p) (λ k → ψ {ℛ} p (onBlk k g)) (λ k → mψ {ℛ} p (onBlk k g)))))
    where
      pt : ∀ r → ψ {ℛ} p g r ≈ ψ {ℛ} p (onTop g) r + ∑ᶠ (λ k → ψ {ℛ} p (onBlk k g) r)
      pt r = trans (split-pt (proj₁ (α p ⟨$⟩ r)) (map g ⟨$⟩ proj₂ (α p ⟨$⟩ r)) (proj₂ (α p ⟨$⟩ r)))
        (sym (+-cong (*-cong refl (onTop-pt g _)) (∑ᶠ-cong (λ k → *-cong refl (onBlk-pt k g _)))))

  ----------------------------------------------------------------------------
  -- small facts about integrals

  ∫ᴹ-zero : ∀ p (f : Hom S ℛ WQ) → (∀ x → map f ⟨$⟩ x ≈ 0#) → ∫ᴹ {ℛ} p f ≈ 0#
  ∫ᴹ-zero p f e = trans
    (J-cong (m p) (mψ {ℛ} p f) (Meas-⊗ {λ _ → 0#} {λ _ → 0#} (Meas-const 0#) (Meas-const 0#))
      (λ r → trans (trans (*-cong refl (e _)) (zeroʳ _)) (sym (zeroˡ 0#))))
    (trans (J-scale (m p) 0# {λ _ → 0#} (Meas-const 0#)) (zeroˡ _))

  -- the test on the all-true point is a constant
  ⊤pt : R₁
  ⊤pt = lift (λ _ → true)

  topPt : ∀ p g r → ψ {ℛ} p (onTop g) r ≈ (map g ⟨$⟩ ⊤pt) * ψ {ℛ} p (χR borelTop) r
  topPt p g r = case {Top (lower x)}
    (λ t → trans
      (trans (*-cong refl (trans (onTop-pt g x) (trans (*-cong (χ-in Top x t) refl) (*-identityˡ _))))
             (*-cong refl (Func.cong (map g) (lift (λ i → t i)))))
      (sym (trans (*-cong refl (trans (*-cong refl (trans (χR-pt borelTop x) (χ-in Top x t))) (*-identityʳ _)))
                  (*-comm _ _))))
    (λ nt → trans
      (trans (*-cong refl (trans (onTop-pt g x) (trans (*-cong (χ-out Top x nt) refl) (zeroˡ _)))) (zeroʳ _))
      (sym (trans (*-cong refl (trans (*-cong refl (trans (χR-pt borelTop x) (χ-out Top x nt))) (zeroʳ _)))
                  (zeroʳ _))))
    where x = proj₂ (α p ⟨$⟩ r)

  topEq : ∀ p g → ∫ᴹ {ℛ} p (onTop g) ≈ (map g ⟨$⟩ ⊤pt) * ∫ᴹ {ℛ} p (χR borelTop)
  topEq p g = trans
    (J-cong (m p) (mψ {ℛ} p (onTop g)) (Meas-⊗ {λ _ → map g ⟨$⟩ ⊤pt} {ψ {ℛ} p (χR borelTop)}
      (Meas-const (map g ⟨$⟩ ⊤pt)) (mψ {ℛ} p (χR borelTop))) (topPt p g))
    (J-scale (m p) (map g ⟨$⟩ ⊤pt) {ψ {ℛ} p (χR borelTop)} (mψ {ℛ} p (χR borelTop)))

  χ-mul : ∀ U V x → χ U x * χ V x ≈ χ (U ∩ᵖ V) x
  χ-mul U V x = case {U (lower x)}
    (λ u → case {V (lower x)}
      (λ v → trans (*-cong (χ-in U x u) (χ-in V x v)) (trans (*-identityˡ 1#) (sym (χ-in (U ∩ᵖ V) x (u , v)))))
      (λ nv → trans (*-cong (χ-in U x u) (χ-out V x nv)) (trans (zeroʳ 1#) (sym (χ-out (U ∩ᵖ V) x (λ (_ , v) → nv v))))))
    (λ nu → trans (*-cong (χ-out U x nu) refl) (trans (zeroˡ _) (sym (χ-out (U ∩ᵖ V) x (λ (u , _) → nu u)))))

  -- the intersection of a block with a cylinder is the disjoint union of the cells of depth n inside it
  pt-sum : ∀ n k (C : Pred) (w : ∣A∣) (x : R₁) →
    sumW n (λ u → w * χ (Cell k u ∩ᵖ C) x) ≈ w * χ (Blk k ∩ᵖ C) x
  pt-sum n k C w x = case {Blk k (lower x) × C (lower x)}
    (λ (b , cx) → sumW-unique n (dropC (suc k) (lower x)) (w * χ (Blk k ∩ᵖ C) x)
      (λ u l m → *-cong refl (trans (χ-in (Cell k u ∩ᵖ C) x ((b , m) , cx)) (sym (χ-in (Blk k ∩ᵖ C) x (b , cx)))))
      (λ u l nm → trans (*-cong refl (χ-out (Cell k u ∩ᵖ C) x (λ ((_ , m) , _) → nm m))) (zeroʳ w)))
    (λ nbc → trans
      (sumW-zero n (λ u l → trans (*-cong refl (χ-out (Cell k u ∩ᵖ C) x (λ ((b , _) , cx) → nbc (b , cx)))) (zeroʳ w)))
      (sym (trans (*-cong refl (χ-out (Blk k ∩ᵖ C) x nbc)) (zeroʳ w))))

  blkPt : ∀ p n k {C} (c : Cyl C) r → ψ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylBlk k) c))) r ≈
    sumW n (λ u → ψ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylCell k u) c))) r)
  blkPt p n k {C} c r = sym (trans (sumW-cong n (λ u _ → *-cong refl (χR-pt (Cyl-borel (Cyl-∩ (cylCell k u) c)) x)))
    (trans (pt-sum n k C (proj₁ (α p ⟨$⟩ r)) x) (*-cong refl (sym (χR-pt (Cyl-borel (Cyl-∩ (cylBlk k) c)) x)))))
    where x = proj₂ (α p ⟨$⟩ r)

  blkSum : ∀ p k {C} (c : Cyl C) n → ∫ᴹ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylBlk k) c))) ≈
    sumW n (λ u → ∫ᴹ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylCell k u) c))))
  blkSum p k {C} c n = trans
    (J-cong (m p) (mψ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylBlk k) c)))) (Meas-sumW n F mF) (blkPt p n k c))
    (J-sumW (m p) n F mF)
    where
      F : Word → R₁ → ∣A∣
      F u = ψ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylCell k u) c)))
      mF : ∀ u → Meas (F u)
      mF u = mψ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylCell k u) c)))

  ----------------------------------------------------------------------------
  -- the part of a measure on a block, as a weighted pushforward

  mxP : ∀ (p : Pre (XW ℛ)) → Measurable (downR (λ r → proj₂ (α p ⟨$⟩ r)))
  mxP p = proj₂ (α-random p)

  mwB : ∀ (p : Pre (XW ℛ)) k → Meas (λ r → proj₁ (α p ⟨$⟩ r) * χ (Blk k) (proj₂ (α p ⟨$⟩ r)))
  mwB p k = Meas-⊗ {λ r → proj₁ (α p ⟨$⟩ r)} {λ r → χ (Blk k) (proj₂ (α p ⟨$⟩ r))} (proj₁ (α-random p))
    (Meas-pre {χ (Blk k)} {λ r → proj₂ (α p ⟨$⟩ r)} (LS (Fun-χ (borelBlk k))) (mxP p))

  -- `Jw` of a pointwise-equal integrand
  JwC : ∀ mm {w} (mw : Meas w) {x} (mx : Measurable (downR x)) {g} (mg : Meas g) {φ} (pφ : Meas φ) →
    (∀ r → φ r ≈ w r * g (x r)) → J mm φ pφ ≈ Jw mm mw mx g mg
  JwC mm {w} mw {x} mx {g} mg pφ e = J-cong mm pφ (Meas-⊗ {w} {λ r → g (x r)} mw (Meas-pre {g} {x} mg mx)) e

  gM : ∀ (g : Hom S ℛ WQ) → Meas (λ r → map g ⟨$⟩ r)
  gM g = Probes.unprobe S g

  blkJ : ∀ p k g → ∫ᴹ {ℛ} p (onBlk k g) ≈ Jw (m p) (mwB p k) (mxP p) (λ r → map g ⟨$⟩ r) (gM g)
  blkJ p k g = JwC (m p) (mwB p k) (mxP p) (gM g) (mψ {ℛ} p (onBlk k g))
    (λ r → trans (*-cong refl (onBlk-pt k g _)) (sym (*-assoc _ _ _)))

  blkMass : ∀ p k → Mw (m p) (mwB p k) (mxP p) ≈ ∫ᴹ {ℛ} p (χR (borelBlk k))
  blkMass p k = sym (JwC (m p) (mwB p k) (mxP p) (Meas-const 1#) (mψ {ℛ} p (χR (borelBlk k)))
    (λ r → trans (*-cong refl (χR-pt (borelBlk k) _)) (sym (*-identityʳ _))))

  blkCylJ : ∀ p k {C} (c : Cyl C) → Jw (m p) (mwB p k) (mxP p) (χ C) (χM c) ≈
    ∫ᴹ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylBlk k) c)))
  blkCylJ p k {C} c = sym (JwC (m p) (mwB p k) (mxP p) (χM c) (mψ {ℛ} p (χR (Cyl-borel (Cyl-∩ (cylBlk k) c))))
    (λ r → trans (*-cong refl (χR-pt (Cyl-borel (Cyl-∩ (cylBlk k) c)) _))
      (trans (*-cong refl (sym (χ-mul (Blk k) C _))) (sym (*-assoc _ _ _)))))

  module _ (μ ν : Pre (XW ℛ))
           (agreeCell : ∀ k w → ∫ᴹ {ℛ} μ (χR (borelCell k w)) ≈ ∫ᴹ {ℛ} ν (χR (borelCell k w)))
           (finBlk : ∀ k → Bnd (∫ᴹ {ℛ} μ (χR (borelBlk k))))
           (agreeTop : ∫ᴹ {ℛ} μ (χR borelTop) ≈ ∫ᴹ {ℛ} ν (χR borelTop)) where

    cellDec : ∀ k {C} (c : Cyl C) u → ((∀ x → Cell k u x → C x) ⊎ (∀ x → Cell k u x → C x → ⊥)) →
      ∫ᴹ {ℛ} μ (χR (Cyl-borel (Cyl-∩ (cylCell k u) c))) ≈ ∫ᴹ {ℛ} ν (χR (Cyl-borel (Cyl-∩ (cylCell k u) c)))
    cellDec k {C} c u (inj₁ h) = trans (∫ᴹ-cong μ pt) (trans (agreeCell k u) (sym (∫ᴹ-cong ν pt)))
      where
        pt : ∀ x → map (χR (Cyl-borel (Cyl-∩ (cylCell k u) c))) ⟨$⟩ x ≈ map (χR (borelCell k u)) ⟨$⟩ x
        pt x = χ-cong (λ y → (λ (cl , _) → cl) , (λ cl → cl , h y cl)) x
    cellDec k {C} c u (inj₂ h) = trans (∫ᴹ-zero μ _ pt) (sym (∫ᴹ-zero ν _ pt))
      where
        pt : ∀ x → map (χR (Cyl-borel (Cyl-∩ (cylCell k u) c))) ⟨$⟩ x ≈ 0#
        pt x = χ-out (Cell k u ∩ᵖ C) x (λ (cl , cx) → h _ cl cx)

    -- on a block, agreement on the cells gives agreement on every cylinder
    agree-blkCyl : ∀ k {C} (c : Cyl C) →
      ∫ᴹ {ℛ} μ (χR (Cyl-borel (Cyl-∩ (cylBlk k) c))) ≈ ∫ᴹ {ℛ} ν (χR (Cyl-borel (Cyl-∩ (cylBlk k) c)))
    agree-blkCyl k {C} c = trans (blkSum μ k c n) (trans (sumW-cong n cellAgree) (sym (blkSum ν k c n)))
      where
        n = proj₁ (cyl-refine c k)
        cellAgree : ∀ u → length u ≡.≡ n →
          ∫ᴹ {ℛ} μ (χR (Cyl-borel (Cyl-∩ (cylCell k u) c))) ≈ ∫ᴹ {ℛ} ν (χR (Cyl-borel (Cyl-∩ (cylCell k u) c)))
        cellAgree u l = cellDec k c u (proj₂ (cyl-refine c k) u l)

    -- on a block, every test (by `UniquenessWeighted.uniqW`)
    agree-blk : ∀ k (g : Hom S ℛ WQ) → ∫ᴹ {ℛ} μ (onBlk k g) ≈ ∫ᴹ {ℛ} ν (onBlk k g)
    agree-blk k g = trans (blkJ μ k g) (trans
      (uniqW (m μ) (m ν) (mwB μ k) (mwB ν k) (mxP μ) (mxP ν) fin masses agree (gM g)) (sym (blkJ ν k g)))
      where
        fin = proj₁ (finBlk k) , ≤-resp (sym (blkMass μ k)) refl (proj₂ (finBlk k))
        pt : ∀ x → map (χR (borelBlk k)) ⟨$⟩ x ≈ map (χR (Cyl-borel (Cyl-∩ (cylBlk k) cylTop))) ⟨$⟩ x
        pt x = χ-cong (λ y → (λ b → b , tt) , (λ (b , _) → b)) x
        masses = trans (blkMass μ k) (trans (∫ᴹ-cong μ pt)
          (trans (agree-blkCyl k cylTop) (trans (sym (∫ᴹ-cong ν pt)) (sym (blkMass ν k)))))
        agree : ∀ {C} (c : Cyl C) → Jw (m μ) (mwB μ k) (mxP μ) (χ C) (χM c) ≈ Jw (m ν) (mwB ν k) (mxP ν) (χ C) (χM c)
        agree c = trans (blkCylJ μ k c) (trans (agree-blkCyl k c) (sym (blkCylJ ν k c)))

    -- on the all-true point, every test
    agree-top : ∀ (g : Hom S ℛ WQ) → ∫ᴹ {ℛ} μ (onTop g) ≈ ∫ᴹ {ℛ} ν (onTop g)
    agree-top g = trans (topEq μ g) (trans (*-cong refl agreeTop) (sym (topEq ν g)))

    uniqR : _≈ᴹ_ {ℛ} μ ν
    uniqR f = trans (∫ᴹ-split μ f) (trans (+-cong (agree-top f) (∑ᶠ-cong (λ k → agree-blk k f))) (sym (∫ᴹ-split ν f)))
