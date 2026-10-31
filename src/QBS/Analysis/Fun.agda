{-# OPTIONS --safe --without-K #-}

-- Measurable functions R → A on Cantor space with values in an `OmegaSemiring`: the class
-- generated from weighted indicators of Borel sets by sums, suprema of increasing sequences
-- and complements (x ↦ 1 - h x).  Every constructor is stated relationally, so no decision on
-- membership in a Borel set is needed.
module QBS.Analysis.Fun where

open import Level using (zero; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Nat.Base using () renaming (suc to suc′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
import Data.Sum.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down; downℕ)
open import QBS.Analysis.Omega

module Measurable (A : OmegaSemiring (suc zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  private R = R₁

  data Fun : (R → ∣A∣) → Set₁ where
    ind : ∀ {U h} (c : ∣A∣) → c ≤ 1# → Borel U →
      (∀ x → U (lower x) → h x ≈ c) → (∀ x → (U (lower x) → ⊥) → h x ≈ 0#) →
      (∀ x → h x ≤ 1#) → Fun h
    sumF : ∀ {h h₁ h₂} → Fun h₁ → Fun h₂ → (∀ x → h x ≈ h₁ x + h₂ x) → (∀ x → h x ≤ 1#) → Fun h
    supF : ∀ {h} (hs : ℕ → R → ∣A∣) → (∀ n → Fun (hs n)) →
      (inc : ∀ x → Increasing (λ n → hs n x)) →
      (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) → Fun h
    complF : ∀ {h h′} → Fun h′ → (∀ x → h x + h′ x ≈ 1#) → Fun h

  -- the class depends only on values
  Fun-ext : ∀ {h h′} → (∀ x → h x ≈ h′ x) → Fun h → Fun h′
  Fun-ext e (ind c c≤1 bU e₀ e₁ b) = ind c c≤1 bU (λ x u → trans (sym (e x)) (e₀ x u))
                                        (λ x n → trans (sym (e x)) (e₁ x n))
                                        (λ x → ≤-resp (e x) refl (b x))
  Fun-ext e (sumF f₁ f₂ q b) = sumF f₁ f₂ (λ x → trans (sym (e x)) (q x)) (λ x → ≤-resp (e x) refl (b x))
  Fun-ext e (supF hs fs inc q) = supF hs fs inc (λ x → trans (sym (e x)) (q x))
  Fun-ext e (complF f q) = complF f (λ x → trans (+-cong (sym (e x)) refl) (q x))

  Fun-const : ∀ c → c ≤ 1# → Fun (const c)
  Fun-const c c≤1 = ind c c≤1 ⊤-borel (λ _ _ → refl) (λ _ n → ⊥-elim (n tt)) (λ _ → c≤1)

  -- every measurable function is bounded by 1
  Fun-≤1 : ∀ {h} → Fun h → ∀ x → h x ≤ 1#
  Fun-≤1 (ind c c≤1 bU e₀ e₁ b) x = b x
  Fun-≤1 (sumF f₁ f₂ q b) x = b x
  Fun-≤1 (supF hs fs inc q) x =
    ≤-resp (sym (q x)) refl (⨆-lub (λ n → hs n x) (inc x) (λ n → Fun-≤1 (fs n) x))
  Fun-≤1 (complF {h} {h′} f q) x = ≤-trans ≤-+ʳ (≤-reflexive (q x))

  -- precomposition with a measurable map
  Fun-pre : ∀ {h f} → Fun h → Measurable (down f) → Fun (h ∘ f)
  Fun-pre (ind c c≤1 bU e₀ e₁ b) mf = ind c c≤1 (preimage mf bU) (λ x u → e₀ _ u) (λ x n → e₁ _ n) (λ x → b _)
  Fun-pre (sumF f₁ f₂ q b) mf = sumF (Fun-pre f₁ mf) (Fun-pre f₂ mf) (λ x → q _) (λ x → b _)
  Fun-pre (supF hs fs inc q) mf = supF (λ n x → hs n (_)) (λ n → Fun-pre (fs n) mf) (λ x → inc _) (λ x → q _)
  Fun-pre (complF f q) mf = complF (Fun-pre f mf) (λ x → q _)

  -- measurable functions do not distinguish points that agree everywhere (classically: `ind` is stated relationally)
  Fun-resp : (∀ (P : Set) → P ⊎ (P → ⊥)) → ∀ {h} → Fun h → ∀ {x y} → ≡._≗_ (lower x) (lower y) → h x ≈ h y
  Fun-resp lem (ind {U} c c≤1 bU e₀ e₁ b) {x} {y} e with lem (U (lower x))
  ... | inj₁ u = trans (e₀ x u) (sym (e₀ y (proj₁ (borel-≗ bU e) u)))
  ... | inj₂ nu = trans (e₁ x nu) (sym (e₁ y (λ v → nu (proj₂ (borel-≗ bU e) v))))
  Fun-resp lem (sumF f₁ f₂ q b) {x} {y} e =
    trans (q x) (trans (+-cong (Fun-resp lem f₁ e) (Fun-resp lem f₂ e)) (sym (q y)))
  Fun-resp lem (supF hs fs inc q) {x} {y} e =
    trans (q x) (trans (⨆-cong (inc x) (inc y) (λ n → Fun-resp lem (fs n) e)) (sym (q y)))
  Fun-resp lem (complF {h} {h′} f q) {x} {y} e = cancel (Fun-≤1 f x)
    (trans (+-comm _ _) (trans (q x) (trans (sym (q y)) (trans (+-comm _ _) (+-cong (sym (Fun-resp lem f e)) refl)))))

  ----------------------------------------------------------------------------
  -- restriction to a decidable Borel set

  module Mask {V : Pred} (bV : Borel V) (dec : ∀ y → V y ⊎ (V y → ⊥)) where

    mask : (R → ∣A∣) → R → ∣A∣
    mask h x with dec (lower x)
    ... | inj₁ _ = h x
    ... | inj₂ _ = 0#

    mask-in : ∀ h x → V (lower x) → mask h x ≈ h x
    mask-in h x v with dec (lower x)
    ... | inj₁ _ = refl
    ... | inj₂ nv = ⊥-elim (nv v)

    mask-out : ∀ h x → (V (lower x) → ⊥) → mask h x ≈ 0#
    mask-out h x nv with dec (lower x)
    ... | inj₁ v = ⊥-elim (nv v)
    ... | inj₂ _ = refl

    -- the indicator of the complement
    cmask : R → ∣A∣
    cmask x with dec (lower x)
    ... | inj₁ _ = 0#
    ... | inj₂ _ = 1#

    cmask-in : ∀ x → V (lower x) → cmask x ≈ 0#
    cmask-in x v with dec (lower x)
    ... | inj₁ _ = refl
    ... | inj₂ nv = ⊥-elim (nv v)

    cmask-out : ∀ x → (V (lower x) → ⊥) → cmask x ≈ 1#
    cmask-out x nv with dec (lower x)
    ... | inj₁ v = ⊥-elim (nv v)
    ... | inj₂ _ = refl

    -- case analysis on membership without abstracting over the goal
    dec′ : ∀ {P : Set₁} (x : R) → (V (lower x) → P) → ((V (lower x) → ⊥) → P) → P
    dec′ x k₁ k₂ = Data.Sum.Base.[ k₁ , k₂ ]′ (dec (lower x))

    Fun-cmask : Fun cmask
    Fun-cmask = ind 1# ≤-refl (compl bV) cmask-out
      (λ x nnv → dec′ x (cmask-in x) (λ nv → ⊥-elim (nnv nv)))
      (λ x → dec′ x (λ v → ≤-resp (sym (cmask-in x v)) refl 0-least) (λ nv → ≤-resp (sym (cmask-out x nv)) refl ≤-refl))

    -- masking commutes with each way of building a function
    mask-≤1 : ∀ h → (∀ x → h x ≤ 1#) → ∀ x → mask h x ≤ 1#
    mask-≤1 h b x = dec′ x (λ v → ≤-resp (sym (mask-in h x v)) refl (b x))
                           (λ nv → ≤-resp (sym (mask-out h x nv)) refl 0-least)

    mask-+ : ∀ {h h₁ h₂} → (∀ x → h x ≈ h₁ x + h₂ x) → ∀ x → mask h x ≈ mask h₁ x + mask h₂ x
    mask-+ {h} {h₁} {h₂} q x = dec′ x
      (λ v → trans (mask-in h x v) (trans (q x) (+-cong (sym (mask-in h₁ x v)) (sym (mask-in h₂ x v)))))
      (λ nv → trans (mask-out h x nv) (sym (trans (+-cong (mask-out h₁ x nv) (mask-out h₂ x nv)) (+-identityˡ 0#))))

    mask-inc : ∀ (hs : ℕ → R → ∣A∣) → (∀ x → Increasing (λ n → hs n x)) → ∀ x → Increasing (λ n → mask (hs n) x)
    mask-inc hs inc x n = dec′ x
      (λ v → ≤-resp (sym (mask-in (hs n) x v)) (sym (mask-in (hs (suc′ n)) x v)) (inc x n))
      (λ nv → ≤-resp (sym (mask-out (hs n) x nv)) (sym (mask-out (hs (suc′ n)) x nv)) ≤-refl)

    mask-⨆ : ∀ {h} (hs : ℕ → R → ∣A∣) (inc : ∀ x → Increasing (λ n → hs n x)) →
      (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) → ∀ x → mask h x ≈ ⨆ (λ n → mask (hs n) x) (mask-inc hs inc x)
    mask-⨆ {h} hs inc q x = dec′ x
      (λ v → trans (mask-in h x v) (trans (q x) (⨆-cong (inc x) (mask-inc hs inc x) (λ n → sym (mask-in (hs n) x v)))))
      (λ nv → trans (mask-out h x nv)
                (sym (trans (⨆-cong (mask-inc hs inc x) (λ _ → ≤-refl) (λ n → mask-out (hs n) x nv))
                            (⨆-const 0# (λ _ → ≤-refl)))))

    mask-compl : ∀ {h h′} → (∀ x → h x + h′ x ≈ 1#) → ∀ x → mask h x + (mask h′ x + cmask x) ≈ 1#
    mask-compl {h} {h′} q x = dec′ x
      (λ v → trans (+-cong (mask-in h x v) (+-cong (mask-in h′ x v) (cmask-in x v))) (trans (+-cong refl (+-identityʳ _)) (q x)))
      (λ nv → trans (+-cong (mask-out h x nv) (+-cong (mask-out h′ x nv) (cmask-out x nv)))
                (trans (+-cong refl (+-identityˡ 1#)) (+-identityˡ 1#)))

    Fun-mask : ∀ {h} → Fun h → Fun (mask h)
    Fun-mask (ind {U} {h} c c≤1 bU e₀ e₁ b) = ind c c≤1 (inter₂ bU bV)
      (λ x (u , v) → trans (mask-in h x v) (e₀ x u))
      (λ x n → dec′ x (λ v → trans (mask-in h x v) (e₁ x (λ u → n (u , v)))) (mask-out h x))
      (mask-≤1 h b)
    Fun-mask (sumF {h} {h₁} {h₂} f₁ f₂ q b) = sumF (Fun-mask f₁) (Fun-mask f₂) (mask-+ q) (mask-≤1 h b)
    Fun-mask (supF hs fs inc q) = supF (λ n → mask (hs n)) (λ n → Fun-mask (fs n)) (mask-inc hs inc) (mask-⨆ hs inc q)
    Fun-mask (complF {h} {h′} f q) =
      complF (sumF (Fun-mask f) Fun-cmask (λ x → refl)
          (λ x → ≤-trans ≤-+ʳ (≤-reflexive (trans (+-comm _ _) (mask-compl q x))))) (mask-compl q)

  ----------------------------------------------------------------------------
  -- gluing along a measurable countable partition

  module Glue (i : R → ℕ) (pi : Partition (downℕ i)) (hs : ℕ → R → ∣A∣) (fs : ∀ n → Fun (hs n)) where

    V : ℕ → Pred
    V k y = i (lift y) ≡ k

    decK : ∀ k y → V k y ⊎ (V k y → ⊥)
    decK k y with i (lift y) Data.Nat.Properties.≟ k
    ... | yes p = inj₁ p
    ... | no ¬p = inj₂ ¬p

    module M (k : ℕ) = Mask {V k} (pi k) (decK k)

    -- partial sums of the pieces h_k · 1_{i = k}
    S : ℕ → R → ∣A∣
    S ℕ.zero x = 0#
    S (suc′ N) x = S N x + M.mask N (hs N) x

    -- before the index of x the sum is 0, after it the sum is h_{i x} x
    S-before : ∀ N x → N ℕ.≤ i x → S N x ≈ 0#
    S-before ℕ.zero x h = refl
    S-before (suc′ N) x h =
      trans (+-cong (S-before N x (Data.Nat.Properties.<⇒≤ h))
                    (M.mask-out N (hs N) x (λ e → Data.Nat.Properties.<⇒≢ h (≡.sym e))))
            (+-identityˡ 0#)

    S-after : ∀ N x → i x ℕ.< N → S N x ≈ hs (i x) x
    S-after ℕ.zero x ()
    S-after (suc′ N) x h with Data.Nat.Properties.<-cmp (i x) N
    ... | tri< lt _ _ = trans (+-cong (S-after N x lt) (M.mask-out N (hs N) x (λ e → Data.Nat.Properties.<⇒≢ lt e)))
                          (+-identityʳ _)
    ... | tri≈ _ eq _ = trans (+-cong (S-before N x (Data.Nat.Properties.≤-reflexive (≡.sym eq))) (M.mask-in N (hs N) x eq′))
                          (trans (+-identityˡ _) (reflexive (≡.cong (λ n → hs n x) (≡.sym eq))))
      where eq′ : V N (lower x)
            eq′ = eq
    ... | tri> _ _ gt = ⊥-elim (Data.Nat.Properties.<⇒≱ gt (Data.Nat.Properties.≤-pred h))

    S-bounded : ∀ N x → S N x ≤ 1#
    S-bounded N x with Data.Nat.Properties.≤-<-connex N (i x)
    ... | inj₁ h = ≤-resp (sym (S-before N x h)) refl 0-least
    ... | inj₂ h = ≤-resp (sym (S-after N x h)) refl (Fun-≤1 (fs (i x)) x)

    Fun-S : ∀ N → Fun (S N)
    Fun-S ℕ.zero = Fun-const 0# 0-least
    Fun-S (suc′ N) = sumF (Fun-S N) (M.Fun-mask N (fs N)) (λ x → refl) (λ x → S-bounded (suc′ N) x)

    inc-S : ∀ x → Increasing (λ N → S N x)
    inc-S x N = ≤-+ʳ

    Fun-glue : Fun (λ x → hs (i x) x)
    Fun-glue = supF S Fun-S inc-S eq
      where
        eq : ∀ x → hs (i x) x ≈ ⨆ (λ N → S N x) (inc-S x)
        eq x = sym (⨆-const-from (λ N → S N x) (inc-S x) (suc′ (i x))
                 (λ n h → S-after n x (Data.Nat.Properties.≤′⇒≤ h)))

  ----------------------------------------------------------------------------
  -- scaling by a constant c ≤ 1

  -- the complement case of `Fun-scale`: c·(1 - h′) = c·1 - c·h′ is the sum of `c·h′` and the constant `1 - c`
  Fun-scale-compl : ∀ {h₀ h′ : R → ∣A∣} c → c ≤ 1# → (f : Fun h′) → (∀ x → h₀ x + h′ x ≈ 1#) →
    Fun (λ x → c * h′ x) → Fun (λ x → c * h₀ x)
  Fun-scale-compl {h₀} {h′} c c≤1 f q sf =
    complF {h = λ x → c * h₀ x} {h′ = λ x → c * h′ x + d}
      (sumF {h = λ x → c * h′ x + d} {h₁ = λ x → c * h′ x} {h₂ = const d} sf (Fun-const d d≤1) (λ x → refl) bd) pw
    where
      d : ∣A∣
      d = proj₁ (complement c≤1)
      cd : c + d ≈ 1#
      cd = proj₂ (complement c≤1)
      d≤1 : d ≤ 1#
      d≤1 = ≤-trans ≤-+ʳ (≤-reflexive (trans (+-comm d c) cd))
      bd : ∀ x → c * h′ x + d ≤ 1#
      bd x = ≤-trans (+-mono (*-mono c (Fun-≤1 f x)) ≤-refl)
          (≤-resp refl cd (≤-resp (sym (+-cong (*-identityʳ c) refl)) refl ≤-refl))
      pw : ∀ x → c * h₀ x + (c * h′ x + d) ≈ 1#
      pw x = trans (sym (+-assoc _ _ _)) (trans (+-cong (sym (distribˡ c (h₀ x) (h′ x))) refl)
               (trans (+-cong (*-cong refl (q x)) refl) (trans (+-cong (*-identityʳ c) refl) cd)))

  Fun-scale : ∀ {h} c → c ≤ 1# → Fun h → Fun (λ x → c * h x)
  Fun-scale {h} c c≤1 (ind {U} d d≤1 bU e₀ e₁ b) = ind (c * d) cd≤1 bU
    (λ x u → trans (*-cong refl (e₀ x u)) refl)
    (λ x nu → trans (*-cong refl (e₁ x nu)) (zeroʳ c))
    (λ x → ≤-trans (*-mono c (b x)) (≤-resp (sym (*-identityʳ c)) refl c≤1))
    where cd≤1 = ≤-trans (*-mono c d≤1) (≤-resp (sym (*-identityʳ c)) refl c≤1)
  Fun-scale c c≤1 (sumF {h} {h₁} {h₂} f₁ f₂ q b) = sumF (Fun-scale c c≤1 f₁) (Fun-scale c c≤1 f₂)
    (λ x → trans (*-cong refl (q x)) (distribˡ c (h₁ x) (h₂ x)))
    (λ x → ≤-trans (*-mono c (b x)) (≤-resp (sym (*-identityʳ c)) refl c≤1))
  Fun-scale c c≤1 (supF {h} hs fs inc q) = supF (λ n x → c * hs n x) (λ n → Fun-scale c c≤1 (fs n))
    (λ x n → *-mono c (inc x n))
    (λ x → trans (*-cong refl (q x)) (*-⨆ c (λ n → hs n x) (inc x) (λ n → *-mono c (inc x n))))
  Fun-scale c c≤1 (complF {h₀} {h′} f q) = Fun-scale-compl {h₀} {h′} c c≤1 f q (Fun-scale c c≤1 f)
