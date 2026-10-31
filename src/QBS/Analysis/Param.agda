{-# OPTIONS --safe --without-K #-}

-- Parametric measurability: if g is a kernel (its integrals of measurable functions are
-- measurable in the parameter) and h is measurable on Cantor space, then
--   r ↦ ∫ g(r)(s ↦ h(merge r s))
-- is measurable.  Dynkin's theorem on sets (rectangles are the base case) and induction on h.
module QBS.Analysis.Param where

open import Level using (zero; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down; downℕ)
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda
open import QBS.Borel.Merge
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators
open import QBS.Analysis.Series using (module Series)
open import QBS.Classical using (LEM₀)

module Param (A : OmegaSemiring (suc zero)) (lem : LEM₀)
             (m : Cantor → Cantor → Cantor) (m₁ : ∀ a → Measurable (m a))
             (rect : ∀ {U} → Cyl U → Rect m U) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Indicators A lem
  open Series A using (psum; psum-inc)
  open SetoidReasoning setoid
  open Dynkin lem using (dynkin)
  private R = R₁

  mergeR : R → R → R
  mergeR a b = lift (m (lower a) (lower b))

  -- sections of Borel sets
  Sec : Pred → Cantor → Pred
  Sec U a s = U (m a s)

  Bsec : ∀ {U} → Borel U → ∀ a → Borel (Sec U a)
  Bsec bU a = preimage (m₁ a) bU

  -- the indicator of a section is the indicator composed with the merge
  χ-sec : ∀ C a s → χ C (mergeR (lift a) s) ≈ χ (Sec C a) s
  χ-sec C a s = case {C (m a (lower s))}
    (λ v → trans (χ-in C (mergeR (lift a) s) v) (sym (χ-in (Sec C a) s v)))
    (λ nv → trans (χ-out C (mergeR (lift a) s) nv) (sym (χ-out (Sec C a) s nv)))

  Sec-≐ : ∀ {U V} → U ≐ V → ∀ a → Sec U a ≐ Sec V a
  Sec-≐ e a s = e (m a s)

  module _ (g : R → Measure) (kg : KernelOk g) where

    -- the measure of the section at r
    Φ : ∀ {U} → Borel U → R → ∣A∣
    Φ {U} bU r = I (g r) (χ (Sec U (lower r))) (Fun-χ (Bsec bU (lower r)))

    DP : Pred → Set₁
    DP U = Σ (Borel U) (λ bU → Fun (Φ bU))

    DP-resp : ∀ {U V} → U ≐ V → DP U → DP V
    DP-resp {U} {V} e (bU , φ) = resp e bU ,
      Fun-ext (λ r → I-cong (g r) (χ-cong (Sec-≐ e (lower r))) (Fun-χ (Bsec bU (lower r))) (Fun-χ (Bsec (resp e bU) (lower r)))) φ

    -- the mass of g r and its defect 1 − mass are measurable in r
    massF : Fun (λ r → mass (g r))
    massF = kg (Fun-const 1# ≤-refl)

    defect : R → ∣A∣
    defect r = proj₁ (complement (I-sub (g r) (Fun-const 1# ≤-refl)))

    defect-eq : ∀ r → mass (g r) + defect r ≈ 1#
    defect-eq r = proj₂ (complement (I-sub (g r) (Fun-const 1# ≤-refl)))

    defectF : Fun defect
    defectF = complF massF (λ r → trans (+-comm _ _) (defect-eq r))

    -- if k is measurable and j + k = mass then j is measurable: j = 1 − (k + defect)
    Fun-co : ∀ {k j : R → ∣A∣} → Fun k → (∀ r → k r ≤ mass (g r)) → (∀ r → j r + k r ≈ mass (g r)) → Fun j
    Fun-co {k} {j} φ le e = complF {h = j} {h′ = λ r → k r + defect r}
      (sumF φ defectF (λ r → refl) (λ r → ≤-trans (+-mono (le r) ≤-refl) (≤-reflexive (defect-eq r))))
      (λ r → trans (sym (+-assoc (j r) (k r) (defect r))) (trans (+-cong (e r) refl) (defect-eq r)))

    DP-compl : ∀ {U} → DP U → DP (∁ U)
    DP-compl {U} (bU , φ) = compl bU ,
      Fun-co φ (λ r → I-mono (g r) (Fun-χ (Bsec bU (lower r))) (Fun-const 1# ≤-refl) (χ-≤1 (Sec U (lower r))))
             (λ r → I-χ-compl (g r) (Bsec bU (lower r)))

    DP-disj : ∀ {U : ℕ → Pred} → (∀ n → DP (U n)) → Disjoint U → DP (λ x → Σ ℕ (λ n → U n x))
    DP-disj {U} ag dj = ⋃ bs , supF (λ N r → psum (λ n → Φ (bs n) r) N)
        (Fun-psum (λ n → Φ (bs n)) (λ n → proj₂ (ag n)) bound)
        (λ r → psum-inc _)
        (λ r → I-⋃ (g r) (λ n → Bsec (bs n) (lower r)) (djs (lower r)))
      where
        bs = λ n → proj₁ (ag n)
        djs : ∀ a → Disjoint (λ n → Sec (U n) a)
        djs a s i j ui uj = dj (m a s) i j ui uj
        bound : ∀ N r → psum (λ n → Φ (bs n) r) N ≤ 1#
        bound N r = ≤-resp (I-PS (g r) (λ n → Bsec (bs n) (lower r)) (djs (lower r)) N) refl
                      (I-≤1 (g r) (Fun-PS (λ n → Bsec (bs n) (lower r)) (djs (lower r)) N))

    -- components of the rectangle decomposition of a finite cylinder
    rC₁ : ∀ {U} → Cyl U → Pred
    rC₁ c = proj₁ (rect c)

    rC₂ : ∀ {U} → Cyl U → Pred
    rC₂ c = proj₁ (proj₂ (rect c))

    rc₁ : ∀ {U} (c : Cyl U) → Cyl (rC₁ c)
    rc₁ c = proj₁ (proj₂ (proj₂ (rect c)))

    rc₂ : ∀ {U} (c : Cyl U) → Cyl (rC₂ c)
    rc₂ c = proj₁ (proj₂ (proj₂ (proj₂ (rect c))))

    rfw : ∀ {U} (c : Cyl U) a s → U (m a s) → rC₁ c a × rC₂ c s
    rfw c = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (rect c)))))

    rbw : ∀ {U} (c : Cyl U) a s → rC₁ c a → rC₂ c s → U (m a s)
    rbw c = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (rect c)))))

    -- the integral of the section of a rectangle: ∫ g(r)(χ C₂) · χ_{C₁}(r)
    Φ-rect : ∀ {U} (c : Cyl U) r →
      Φ (Cyl-borel c) r ≈ I (g r) (χ (rC₂ c)) (Fun-χ (Cyl-borel (rc₂ c))) * χ (rC₁ c) r
    Φ-rect {U} c r = case {rC₁ c (lower r)}
      (λ v → trans (I-cong (g r) (χ-cong (≐-sym (inside (lower r) v))) (Fun-χ (Bsec bU (lower r))) (Fun-χ bC₂))
                   (sym (trans (*-cong refl (χ-in (rC₁ c) r v)) (*-identityʳ _))))
      (λ nv → trans (I-cong (g r) (χ-cong (≐-sym (outside (lower r) nv))) (Fun-χ (Bsec bU (lower r))) (Fun-χ ⊥-borel))
                (trans (I-χ-⊥ (g r) ⊥-borel)
                       (sym (trans (*-cong refl (χ-out (rC₁ c) r nv)) (zeroʳ _)))))
      where
        bU = Cyl-borel c
        bC₂ = Cyl-borel (rc₂ c)
        inside : ∀ a → rC₁ c a → rC₂ c ≐ Sec U a
        inside a v s = (λ p → rbw c a s v p) , (λ u → proj₂ (rfw c a s u))
        outside : ∀ a → (rC₁ c a → ⊥) → (λ (_ : Cantor) → ⊥) ≐ Sec U a
        outside a nv s = (λ b → ⊥-elim b) , (λ u → nv (proj₁ (rfw c a s u)))

    -- rectangles: the section is C₂ when the first coordinate is in C₁, and empty otherwise
    DP-cyl : ∀ {U} → Cyl U → DP U
    DP-cyl {U} c =
      Cyl-borel c , Fun-ext (λ r → trans (mask≈ r) (sym (Φ-rect c r))) (Fun-mask (kg (Fun-χ (Cyl-borel (rc₂ c)))))
      where
        open Mask {rC₁ c} (Cyl-borel (rc₁ c)) (Cyl-dec (rc₁ c))
        ψ : R → ∣A∣
        ψ r = I (g r) (χ (rC₂ c)) (Fun-χ (Cyl-borel (rc₂ c)))
        mask≈ : ∀ r → mask ψ r ≈ ψ r * χ (rC₁ c) r
        mask≈ r = dec′ r
          (λ v → trans (mask-in ψ r v) (sym (trans (*-cong refl (χ-in (rC₁ c) r v)) (*-identityʳ _))))
          (λ nv → trans (mask-out ψ r nv) (sym (trans (*-cong refl (χ-out (rC₁ c) r nv)) (zeroʳ _))))

    -- all Borel sets
    param-sets : ∀ {U} → Borel U → DP U
    param-sets = dynkin DP DP-resp DP-cyl DP-compl DP-disj

    -- from sets to functions: the integral against the kernel of a measurable function is measurable in the parameter
    PFT : ∀ {h} → Fun h → Set₁
    PFT {h} fh = Fun (λ r → I (g r) (λ s → h (mergeR r s)) (Fun-pre fh (m₁ (lower r))))

    PF-ind : ∀ {U k} (c : ∣A∣) (c≤1 : c ≤ 1#) (bU : Borel U) e₀ e₁ b → PFT (ind {U} {k} c c≤1 bU e₀ e₁ b)
    PF-ind {U} {k} c c≤1 bU e₀ e₁ b = Fun-ext (λ r → sym (iscale r)) (Fun-scale c c≤1 φ)
      where
        φ : Fun (Φ bU)
        φ with param-sets bU
        ... | bU′ , φ′ = Fun-ext (λ r → I-cong (g r) (λ x → refl) (Fun-χ (Bsec bU′ (lower r))) (Fun-χ (Bsec bU (lower r)))) φ′
        fk = ind c c≤1 bU e₀ e₁ b
        pw : ∀ r s → k (mergeR r s) ≈ c * χ (Sec U (lower r)) s
        pw r s = case {U (m (lower r) (lower s))}
          (λ u → trans (e₀ _ u) (sym (trans (*-cong refl (χ-in (Sec U (lower r)) s u)) (*-identityʳ c))))
          (λ nu → trans (e₁ _ nu) (sym (trans (*-cong refl (χ-out (Sec U (lower r)) s nu)) (zeroʳ c))))
        iscale : ∀ r → I (g r) (λ s → k (mergeR r s)) (Fun-pre fk (m₁ (lower r))) ≈ c * Φ bU r
        iscale r = I-scale (g r) c (Fun-χ (Bsec bU (lower r))) (Fun-pre fk (m₁ (lower r))) (pw r)
    PF-sum : ∀ {h h₁ h₂} (f₁ : Fun h₁) (f₂ : Fun h₂) q b → PFT f₁ → PFT f₂ → PFT (sumF {h} f₁ f₂ q b)
    PF-sum {h} f₁ f₂ q b p₁ p₂ =
      sumF p₁ p₂
        (λ r → I-add (g r) (Fun-pre (sumF f₁ f₂ q b) (m₁ (lower r)))
                 (Fun-pre f₁ (m₁ (lower r))) (Fun-pre f₂ (m₁ (lower r)))
                 (λ s → q (mergeR r s)))
        (λ r → I-≤1 (g r) _)

    PF-sup : ∀ {h} (hs : ℕ → R → ∣A∣) (fs : ∀ n → Fun (hs n)) inc q → (∀ n → PFT (fs n)) → PFT (supF {h} hs fs inc q)
    PF-sup {h} hs fs inc q ps =
      supF (λ n r → I (g r) (λ s → hs n (mergeR r s)) (Fun-pre (fs n) (m₁ (lower r))))
        ps
        (λ r n → I-mono (g r) _ _ (λ s → inc (mergeR r s) n))
        (λ r → I-sup (g r) (λ n s → hs n (mergeR r s)) (λ n → Fun-pre (fs n) (m₁ (lower r)))
                 (λ s → inc (mergeR r s)) (Fun-pre (supF hs fs inc q) (m₁ (lower r)))
                 (λ s → q (mergeR r s)))

    PF-compl : ∀ {h h′} (f : Fun h′) q → PFT f → PFT (complF {h} f q)
    PF-compl {h} {h′} f q p =
      Fun-co p
        (λ r → I-mono (g r) (Fun-pre f (m₁ (lower r))) (Fun-const 1# ≤-refl) (λ s → Fun-≤1 f (mergeR r s)))
        (λ r → sym (I-add (g r) (Fun-const 1# ≤-refl) (Fun-pre (complF f q) (m₁ (lower r)))
                      (Fun-pre f (m₁ (lower r))) (λ s → sym (q (mergeR r s)))))

    PF : ∀ {h} (fh : Fun h) → PFT fh
    PF (ind c c≤1 bU e₀ e₁ b) = PF-ind c c≤1 bU e₀ e₁ b
    PF (sumF f₁ f₂ q b) = PF-sum f₁ f₂ q b (PF f₁) (PF f₂)
    PF (supF hs fs inc q) = PF-sup hs fs inc q (λ n → PF (fs n))
    PF (complF f q) = PF-compl f q (PF f)

  -- push the parameter into the section: the kernel r ↦ (merge r)_* g(r)
  pushMerge : (R → Measure) → R → Measure
  pushMerge g r = push {mergeR r} (m₁ (lower r)) (g r)

  KernelOk-pushMerge : ∀ {g} → KernelOk g → KernelOk (pushMerge g)
  KernelOk-pushMerge {g} kg fh = PF g kg fh
