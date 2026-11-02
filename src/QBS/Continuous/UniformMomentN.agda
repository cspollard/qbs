{-# OPTIONS --safe --without-K #-}

-- All moments of the uniform distribution (part 1: the algebra).
--
-- Splitting off the first bit of the binary expansion e gives, for t = e(true :: ·) = ½ + ½ e,
--   M j := E[eʲ],  G j k := E[eʲ tᵏ]   with   G j 0 = M j,  G j (k+1) = ½ (G j k + G (j+1) k),
--   M j = ½ G 0 j + ½ (½ʲ M j)
-- (`eʲ(false :: s) = ½ʲ eʲ(s)`).  The expected values `M j = 1/(j+1)` are recovered, multiplied out, by strong
-- induction on `j` without binomial coefficients:
--   * with y i = (i+1) M i and the Pascal triangle `Z ν j k` on a base sequence ν (`Z ν j 0 = ν j`,
--     `Z ν j (k+1) = ½ (Z ν j k + Z ν (j+1) k)`), integration by parts reads, additively,
--     (j+1) G j k + ½ k G (j+1) (k-1) = Z y j k   (`inv`);
--   * from it, (k+2) G 0 (k+1) = ½ (k+1) G 0 k + Z y 0 (k+1), and `Z y 0 k + ½ᵏ = 1 + ½ᵏ y k` when y i = 1 below k (`S`);
--   * together with the equation for M j this gives `w + s = 1 + s w` for w = y j, s = ½ʲ, whence w = 1 (`final`: w ≤ 2,
--     iterate `cancel≤` to get w ≤ 1 + ½ᵐ, `arch`, then the complement d of w is ≤ ½ʲ d, hence 0).
-- The module is over an abstract Archimedean ω-semiring (the solver is slow on the concrete cut semiring).
module QBS.Continuous.UniformMomentN where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Data.Bool.Base using (true; false)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Classical using (LEM₁)

module AlgN (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; arch; cancel≤; hp; hp-≤; half-twice) renaming (half+half to hh)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open SetoidReasoning setoid

  -- natural numbers in the semiring
  # : ℕ → ∣A∣
  # zero = 0#
  # (suc n) = 1# + # n

  -- the Pascal triangle on a base sequence
  Z : (ℕ → ∣A∣) → ℕ → ℕ → ∣A∣
  Z ν j zero = ν j
  Z ν j (suc k) = half * (Z ν j k + Z ν (suc j) k)

  -- the shift of a base sequence
  Z-shift : ∀ ν k j → Z ν (suc j) k ≈ Z (λ i → ν (suc i)) j k
  Z-shift ν zero j = refl
  Z-shift ν (suc k) j = *-cong refl (+-cong (Z-shift ν k j) (Z-shift ν k (suc j)))

  hp≤1 : ∀ n → hp n ≤ 1#
  hp≤1 zero = ≤-refl
  hp≤1 (suc n) = ≤-trans (hp-≤ n) (hp≤1 n)

  half≤1 : half ≤ 1#
  half≤1 = ≤-trans ≤-+ʳ (≤-reflexive hh)

  hm : ∀ x → half * x + half * x ≈ x
  hm x = trans (sym (distribˡ half x x)) (half-twice x)

  ----------------------------------------------------------------------------
  -- Z ν 0 k when ν is 1 below k:  Z ν 0 k + ½ᵏ = 1 + ½ᵏ ν k

  S-step : ∀ {a b c p} → half * p ≤ 1# → a + p ≈ 1# + p → b + p ≈ 1# + p * c →
    half * (a + b) + half * p ≈ 1# + half * p * c
  S-step {a} {b} {c} {p} le ea eb = cancel le (begin
    half * p + (half * (a + b) + half * p)   ≈⟨ solve 3 (λ q x r → q :+ (x :+ r) := x :+ (q :+ r)) refl (half * p) _ (half * p) ⟩
    half * (a + b) + (half * p + half * p)   ≈⟨ +-cong refl (hm p) ⟩
    half * (a + b) + p                       ≈⟨ +-cong refl (sym (half-twice p)) ⟩
    half * (a + b) + half * (p + p)          ≈⟨ solve 4 (λ h x y q → h :* (x :+ y) :+ h :* (q :+ q) := h :* ((x :+ q) :+ (y :+ q))) refl half a b p ⟩
    half * ((a + p) + (b + p))               ≈⟨ *-cong refl (+-cong ea eb) ⟩
    half * ((1# + p) + (1# + p * c))         ≈⟨ solve 3 (λ h q c′ → h :* ((con 1 :+ q) :+ (con 1 :+ q :* c′)) := h :* (con 1 :+ con 1) :+ (h :* q :+ h :* q :* c′)) refl half p c ⟩
    half * (1# + 1#) + (half * p + half * p * c) ≈⟨ +-cong (half-twice 1#) refl ⟩
    1# + (half * p + half * p * c)           ≈⟨ solve 3 (λ o q x → o :+ (q :+ x) := q :+ (o :+ x)) refl 1# (half * p) _ ⟩
    half * p + (1# + half * p * c) ∎)

  S : ∀ k ν → (∀ i → i ℕ.< k → ν i ≈ 1#) → Z ν 0 k + hp k ≈ 1# + hp k * ν k
  S zero ν h = trans (+-comm _ _) (+-cong refl (sym (*-identityˡ _)))
  S (suc k) ν h = S-step {c = ν (suc k)} (≤-trans (*-mono half (hp≤1 k)) (≤-trans (≤-reflexive (*-identityʳ half)) half≤1)) ea eb
    where
    ea = trans (S k ν (λ i lt → h i (ℕ.m<n⇒m<1+n lt))) (+-cong refl (trans (*-cong refl (h k (ℕ.n<1+n k))) (*-identityʳ _)))
    eb = trans (+-cong (Z-shift ν k 0) refl) (S k (λ i → ν (suc i)) (λ i lt → h (suc i) (ℕ.s<s lt)))

  ----------------------------------------------------------------------------
  -- the last step: w + s = 1 + s w with s ≤ ½ and w ≤ 2 gives w = 1

  -- s w ≤ s ≤ 1
  final-sw : ∀ {s w} → s ≤ half → w ≤ 1# → s * w ≤ 1#
  final-sw {s} sh wle = ≤-trans (*-mono s wle) (≤-trans (≤-reflexive (*-identityʳ s)) (≤-trans sh half≤1))

  -- s·½ᵐ ≤ ½·½ᵐ
  final-sm : ∀ {s} m → s ≤ half → s * hp m ≤ half * hp m
  final-sm {s} m sh = ≤-trans (≤-reflexive (*-comm s (hp m))) (≤-trans (*-mono (hp m) sh) (≤-reflexive (*-comm (hp m) half)))

  -- one iteration: w ≤ 1 + ½ᵐ gives w ≤ 1 + ½ᵐ⁺¹
  final-iter : ∀ {s w} → s ≤ half → w + s ≈ 1# + s * w → ∀ m → w ≤ 1# + hp m → w ≤ 1# + hp (suc m)
  final-iter {s} {w} sh eq m lt = cancel≤ (≤-trans sh half≤1) (≤-trans (≤-reflexive (+-comm s w))
    (≤-trans (≤-reflexive eq) (≤-trans (+-mono ≤-refl (*-mono s lt))
    (≤-trans (≤-reflexive (solve 2 (λ s′ p → con 1 :+ s′ :* (con 1 :+ p) := s′ :+ (con 1 :+ s′ :* p)) refl s (hp m)))
    (+-mono ≤-refl (+-mono ≤-refl (final-sm m sh)))))))

  -- the complement d of w satisfies d = s d
  final-d : ∀ {s w d} → s ≤ half → w ≤ 1# → w + d ≈ 1# → w + s ≈ 1# + s * w → d ≈ s * d
  final-d {s} {w} {d} sh wle wd eq = cancel (final-sw sh wle) (trans (+-comm _ d) (trans i (sym sd)))
    where
    i : d + s * w ≈ s
    i = sym (cancel wle (trans eq (trans (+-cong (sym wd) refl) (+-assoc w d (s * w)))))
    sd : s * w + s * d ≈ s
    sd = trans (sym (distribˡ s w d)) (trans (*-cong refl wd) (*-identityʳ s))

  final : ∀ {s w} → s ≤ half → w ≤ 1# + 1# → w + s ≈ 1# + s * w → w ≈ 1#
  final {s} {w} sh w2 eq = trans (sym (+-identityʳ w)) (trans (+-cong refl (sym d0)) wd)
    where
    wle : w ≤ 1#
    wle = arch (λ m → go m)
      where go : ∀ m → w ≤ 1# + hp m
            go zero = w2
            go (suc m) = final-iter sh eq m (go m)
    d = proj₁ (complement wle)
    wd : w + d ≈ 1#
    wd = proj₂ (complement wle)
    dd : d ≈ s * d
    dd = final-d sh wle wd eq
    dle : ∀ m → d ≤ hp m
    dle zero = ≤-trans ≤-+ʳ (≤-trans (≤-reflexive (+-comm d w)) (≤-reflexive wd))
    dle (suc m) = ≤-trans (≤-reflexive dd) (≤-trans (*-mono s (dle m)) (final-sm m sh))
    d0 : d ≈ 0#
    d0 = ≤-antisym (arch (λ m → ≤-trans (dle m) (≤-reflexive (sym (+-identityˡ _))))) 0-least

  ----------------------------------------------------------------------------
  -- the moments, from the Pascal structure of G and the equation for M

  module Mom (M : ℕ → ∣A∣) (G : ℕ → ℕ → ∣A∣) (Gb : ∀ j → G j 0 ≈ M j)
    (Pas : ∀ j k → G j (suc k) ≈ half * (G j k + G (suc j) k))
    (E : ∀ j → M j ≈ half * G 0 j + half * (hp j * M j)) (M0 : M 0 ≈ 1#) (Mle : ∀ j → M (suc j) ≤ M j) where

    -- y j = (j+1) M j, and the correction ½ k G (j+1) (k-1) of the integration by parts
    y : ℕ → ∣A∣
    y i = # (suc i) * M i

    Rr : ℕ → ℕ → ∣A∣
    Rr j zero = 0#
    Rr j (suc k) = half * (# (suc k) * G (suc j) k)

    kG : ∀ k j → # k * G (suc j) k ≈ Rr j k + Rr (suc j) k
    kG zero j = trans (zeroˡ _) (sym (+-identityˡ 0#))
    kG (suc k) j = trans (*-cong refl (Pas (suc j) k))
      (solve 4 (λ n h g₁ g₂ → n :* (h :* (g₁ :+ g₂)) := h :* (n :* g₁) :+ h :* (n :* g₂)) refl (# (suc k)) half _ _)

    inv-step : ∀ {h pj g₀ g₁ pk r₁ r₂ : ∣A∣} → pk * g₁ ≈ r₁ + r₂ →
      pj * (h * (g₀ + g₁)) + h * ((1# + pk) * g₁) ≈ h * ((pj * g₀ + r₁) + ((1# + pj) * g₁ + r₂))
    inv-step {h} {pj} {g₀} {g₁} {pk} {r₁} {r₂} e = begin
      pj * (h * (g₀ + g₁)) + h * ((1# + pk) * g₁)   ≈⟨ solve 5 (λ h′ p a b k → p :* (h′ :* (a :+ b)) :+ h′ :* ((con 1 :+ k) :* b)
                                                                   := h′ :* ((p :* a :+ (con 1 :+ p) :* b) :+ k :* b)) refl h pj g₀ g₁ pk ⟩
      h * ((pj * g₀ + (1# + pj) * g₁) + pk * g₁)    ≈⟨ *-cong refl (+-cong refl e) ⟩
      h * ((pj * g₀ + (1# + pj) * g₁) + (r₁ + r₂))  ≈⟨ *-cong refl (solve 6 (λ a b c d e′ f → (a :* b :+ c :* d) :+ (e′ :+ f) := (a :* b :+ e′) :+ (c :* d :+ f)) refl pj g₀ (1# + pj) g₁ r₁ r₂) ⟩
      h * ((pj * g₀ + r₁) + ((1# + pj) * g₁ + r₂)) ∎

    inv : ∀ k j → # (suc j) * G j k + Rr j k ≈ Z y j k
    inv zero j = trans (+-cong (*-cong refl (Gb j)) refl) (+-identityʳ _)
    inv (suc k) j = trans (+-cong (*-cong refl (Pas j k)) refl)
      (trans (inv-step (kG k j)) (*-cong refl (+-cong (inv k j) (inv k (suc j)))))

    -- (k+2) G 0 (k+1) = ½ (k+1) G 0 k + Z y 0 (k+1)
    V : ∀ k → # (suc (suc k)) * G 0 (suc k) ≈ half * (# (suc k) * G 0 k) + Z y 0 (suc k)
    V k = trans (solve 2 (λ p x → (con 1 :+ p) :* x := (con 1 :+ con 0) :* x :+ p :* x) refl (# (suc k)) (G 0 (suc k)))
      (trans (+-cong refl (trans (*-cong refl (Pas 0 k))
        (solve 4 (λ p h a b → p :* (h :* (a :+ b)) := h :* (p :* b) :+ h :* (p :* a)) refl (# (suc k)) half _ _)))
      (trans (sym (+-assoc _ _ _)) (trans (+-cong (inv (suc k) 0) refl) (+-comm _ _))))

    -- the moments below n are known
    Ih : ℕ → Set₁
    Ih n = ∀ i → i ℕ.≤ n → y i ≈ 1#

    Y1 : ∀ {n} → Ih n → ∀ k → k ℕ.≤ n → Z y 0 k ≈ 1#
    Y1 {n} ih k kle = cancel (hp≤1 k) (trans (+-comm (hp k) _) (trans (S k y below)
      (trans (+-cong refl (trans (*-cong refl (ih k kle)) (*-identityʳ _))) (+-comm 1# (hp k)))))
      where below : ∀ i → i ℕ.< k → y i ≈ 1#
            below i lt = ih i (ℕ.≤-trans (ℕ.<⇒≤ lt) kle)

    U : ∀ {n} → Ih n → ∀ k → k ℕ.≤ n → # (suc k) * G 0 k + hp k ≈ 1# + 1#
    U ih zero le = +-cong (trans (*-cong refl (Gb 0)) (ih 0 ℕ.z≤n)) refl
    U ih (suc k) le = trans (+-cong (trans (V k) (+-cong refl (Y1 ih (suc k) le))) refl)
      (trans (solve 4 (λ h x z p → (h :* x :+ z) :+ h :* p := z :+ h :* (x :+ p)) refl half (# (suc k) * G 0 k) 1# (hp k))
      (+-cong refl (trans (*-cong refl (U ih k (ℕ.≤-trans (ℕ.n≤1+n k) le))) (half-twice 1#))))

    -- the equation for the unknown level N = n+1: Q = (N+2) G 0 N,  s = ½ᴺ,  w = y N
    r1 : ∀ {n} → Ih n → # (suc (suc n)) * G 0 (suc n) + hp (suc n) ≈ 1# + Z y 0 (suc n)
    r1 {n} ih = trans (+-cong (V n) refl) (trans
      (solve 4 (λ h p y′ q → (h :* p :+ y′) :+ h :* q := (h :* (p :+ q)) :+ y′) refl half (# (suc n) * G 0 n) (Z y 0 (suc n)) (hp n))
      (trans (+-cong (*-cong refl (U ih n ℕ.≤-refl)) refl) (+-cong (half-twice 1#) refl)))

    r2 : ∀ {n} → Ih n → (# (suc (suc n)) * G 0 (suc n) + hp (suc n)) + hp (suc n)
      ≈ (1# + 1#) + hp (suc n) * y (suc n)
    r2 {n} ih = trans (+-cong (r1 ih) refl) (trans (+-assoc _ _ _) (trans (+-cong refl (S (suc n) y below))
      (sym (+-assoc 1# 1# _))))
      where below : ∀ i → i ℕ.< suc n → y i ≈ 1#
            below i lt = ih i (ℕ.s≤s⁻¹ lt)

    r3 : ∀ {n} → Ih n → half * (# (suc (suc n)) * G 0 (suc n)) + hp (suc n) ≈ 1# + half * (hp (suc n) * y (suc n))
    r3 {n} ih = trans (+-cong refl (sym (half-twice (hp (suc n))))) (trans
      (solve 3 (λ h q s′ → h :* q :+ h :* (s′ :+ s′) := h :* ((q :+ s′) :+ s′)) refl half (# (suc (suc n)) * G 0 (suc n)) (hp (suc n)))
      (trans (*-cong refl (r2 ih)) (trans (distribˡ half _ _) (+-cong (half-twice 1#) refl))))

    r4 : ∀ {n} → y (suc n) ≈ half * (# (suc (suc n)) * G 0 (suc n)) + half * (hp (suc n) * y (suc n))
    r4 {n} = trans (*-cong refl (E (suc n)))
      (solve 5 (λ p h g s′ m → p :* (h :* g :+ h :* (s′ :* m)) := h :* (p :* g) :+ h :* (s′ :* (p :* m))) refl
        (# (suc (suc n))) half (G 0 (suc n)) (hp (suc n)) (M (suc n)))

    r5 : ∀ {n} → Ih n → y (suc n) + hp (suc n) ≈ 1# + hp (suc n) * y (suc n)
    r5 {n} ih = trans (+-cong r4 refl) (trans
      (solve 3 (λ q x s′ → (q :+ x) :+ s′ := (q :+ s′) :+ x) refl (half * (# (suc (suc n)) * G 0 (suc n))) _ (hp (suc n)))
      (trans (+-cong (r3 ih) refl) (trans (+-assoc _ _ _) (+-cong refl (hm _)))))

    -- w = y (n+1) ≤ 2, from M (n+1) ≤ M n and y n = 1
    w≤2 : ∀ {n} → Ih n → y (suc n) ≤ 1# + 1#
    w≤2 {n} ih = ≤-trans (*-mono (# (suc (suc n))) (Mle n)) (≤-trans (≤-reflexive (solve 2 (λ p m → (con 1 :+ p) :* m := m :+ p :* m) refl (# (suc n)) (M n)))
      (+-mono Mn≤1 (≤-reflexive (ih n ℕ.≤-refl))))
      where
      Mn≤1 : M n ≤ 1#
      Mn≤1 = ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (sym (solve 2 (λ p m → (con 1 :+ p) :* m := m :+ p :* m) refl (# n) (M n)))))
               (≤-reflexive (ih n ℕ.≤-refl))

    step : ∀ {n} → Ih n → y (suc n) ≈ 1#
    step {n} ih = final (≤-trans (*-mono half (hp≤1 n)) (≤-reflexive (*-identityʳ half))) (w≤2 ih) (r5 ih)

    extend : ∀ {n} → Ih n → Ih (suc n)
    extend {n} ih i le with ℕ.m≤n⇒m<n∨m≡n le
    ... | inj₁ lt = ih i (ℕ.s≤s⁻¹ lt)
    ... | inj₂ ≡.refl = step ih

    all : ∀ n → Ih n
    all zero zero _ = trans (*-cong refl M0) (trans (*-identityʳ _) (+-identityʳ 1#))
    all (suc n) = extend (all n)

    -- (n+1) M n = 1
    moment : ∀ n → # (suc n) * M n ≈ 1#
    moment n = all n n ℕ.≤-refl


-- the measure side: the moments `E[eʲ]` of the binary expansion, `G j k = E[eʲ tᵏ]` with `t = e(true :: ·)`
module UniformMomentN (lem₁ : LEM₁) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  R = lowerRealsArch (lemOf lem₁)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-≤) renaming (half+half to hh)
  open Integration A
  open Meas (lemOf lem₁)
  open Expansion A half hh
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Measurable A using (Fun; Fun-const; Fun-scale; Fun-pre; sumF; Fun-≤1)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open LevelSets (lemOf lem₁) using (LS)
  open ExpansionCons A half hh using (expansion-cons)
  open HalfOrder A R using (half≤1)
  open Indicators A (lemOf lem₁) using (I-const)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open AlgN A R using (#; hp≤1)

  -- powers
  pw : ∣A∣ → ℕ → ∣A∣
  pw x zero = 1#
  pw x (suc n) = x * pw x n

  pw≤1 : ∀ {x} → x ≤ 1# → ∀ n → pw x n ≤ 1#
  pw≤1 le zero = ≤-refl
  pw≤1 {x} le (suc n) = ≤-trans (*-mono x (pw≤1 le n)) (≤-trans (≤-reflexive (*-identityʳ x)) le)

  -- (½x)ⁿ = ½ⁿ xⁿ
  pw-half : ∀ x n → pw (half * x) n ≈ hp n * pw x n
  pw-half x zero = sym (*-identityˡ 1#)
  pw-half x (suc n) = trans (*-cong refl (pw-half x n))
    (solve 4 (λ h x′ p q → h :* x′ :* (p :* q) := h :* p :* (x′ :* q)) refl half x (hp n) (pw x n))

  -- t = e(true :: ·)
  t : R₁ → ∣A∣
  t r = expansion (consR true r)

  ET : Fun t
  ET = Fun-pre {f = consR true} Fun-expansion (measurable-cons true)

  Meas-pw : ∀ {f} → Meas f → ∀ n → Meas (λ r → pw (f r) n)
  Meas-pw mf zero = Meas-const 1#
  Meas-pw {f} mf (suc n) = Meas-⊗ {f} {λ r → pw (f r) n} mf (Meas-pw mf n)

  -- the functions eʲ tᵏ
  gf : ℕ → ℕ → R₁ → ∣A∣
  gf j k r = pw (expansion r) j * pw (t r) k

  gf≤1 : ∀ j k r → gf j k r ≤ 1#
  gf≤1 j k r = ≤-trans (*-mono _ (pw≤1 (Fun-≤1 ET r) k)) (≤-trans (≤-reflexive (*-identityʳ _)) (pw≤1 (expansion≤1 r) j))

  Meas-gf : ∀ j k → Meas (gf j k)
  Meas-gf j k = Meas-⊗ {λ r → pw (expansion r) j} {λ r → pw (t r) k} (Meas-pw (LS Fun-expansion) j) (Meas-pw (LS ET) k)

  Fgf : ∀ j k → Fun (gf j k)
  Fgf j k = Meas→Fun (gf≤1 j k) (Meas-gf j k)

  pw-cong : ∀ {x y} → x ≈ y → ∀ n → pw x n ≈ pw y n
  pw-cong e zero = refl
  pw-cong e (suc n) = *-cong e (pw-cong e n)

  G : ℕ → ℕ → ∣A∣
  G j k = I fairCoin (gf j k) (Fgf j k)

  M : ℕ → ∣A∣
  M j = G j 0

  -- t = ½ + ½ e:  eʲ tᵏ⁺¹ = ½ eʲ tᵏ + ½ eʲ⁺¹ tᵏ
  gf-pas : ∀ j k r → gf j (suc k) r ≈ half * gf j k r + half * gf (suc j) k r
  gf-pas j k r = trans (*-cong refl (*-cong (expansion-cons true r) refl))
    (solve 4 (λ h x P Q → P :* ((h :+ h :* x) :* Q) := h :* (P :* Q) :+ h :* ((x :* P) :* Q)) refl
      half (expansion r) (pw (expansion r) j) (pw (t r) k))

  Pas : ∀ j k → G j (suc k) ≈ half * (G j k + G (suc j) k)
  Pas j k = trans (I-add fairCoin (Fgf j (suc k)) F₁ F₂ (gf-pas j k))
    (trans (+-cong (I-scale fairCoin half (Fgf j k) F₁ (λ _ → refl)) (I-scale fairCoin half (Fgf (suc j) k) F₂ (λ _ → refl)))
      (sym (distribˡ half _ _)))
    where
    F₁ = Fun-scale half half≤1 (Fgf j k)
    F₂ = Fun-scale half half≤1 (Fgf (suc j) k)

  -- the two branches of the first bit
  FT : ∀ j → Fun (λ x → gf j 0 (consR true x))
  FT j = Fun-pre {f = consR true} (Fgf j 0) (measurable-cons true)
  FF : ∀ j → Fun (λ x → gf j 0 (consR false x))
  FF j = Fun-pre {f = consR false} (Fgf j 0) (measurable-cons false)

  I-true : ∀ j → I fairCoin (λ x → gf j 0 (consR true x)) (FT j) ≈ G 0 j
  I-true j = I-cong fairCoin (λ r → trans (*-identityʳ _) (sym (*-identityˡ _))) (FT j) (Fgf 0 j)

  gf-false : ∀ j r → gf j 0 (consR false r) ≈ hp j * gf j 0 r
  gf-false j r = trans (*-cong (pw-cong (trans (expansion-cons false r) (+-identityˡ _)) j) refl)
    (trans (*-cong (pw-half (expansion r) j) refl) (solve 2 (λ p q → p :* q :* con 1 := p :* (q :* con 1)) refl (hp j) (pw (expansion r) j)))

  I-false : ∀ j → I fairCoin (λ x → gf j 0 (consR false x)) (FF j) ≈ hp j * M j
  I-false j = I-scale fairCoin (hp j) (Fgf j 0) (FF j) (gf-false j)

  E : ∀ j → M j ≈ half * G 0 j + half * (hp j * M j)
  E j = trans (firstBit-fun (Fgf j 0)) (+-cong (*-cong refl (I-true j)) (*-cong refl (I-false j)))

  M0 : M 0 ≈ 1#
  M0 = trans (I-cong fairCoin (λ r → *-identityˡ 1#) (Fgf 0 0) (Fun-const 1# ≤-refl)) (I-const fairCoin L-one 1# ≤-refl)

  Mle : ∀ j → M (suc j) ≤ M j
  Mle j = I-mono fairCoin (Fgf (suc j) 0) (Fgf j 0) (λ r → ≤-trans (≤-reflexive (*-identityʳ _))
    (≤-trans (≤-reflexive (*-comm _ _)) (≤-trans (*-mono (pw (expansion r) j) (expansion≤1 r))
      (≤-trans (≤-reflexive (*-identityʳ _)) (≤-reflexive (sym (*-identityʳ _)))))))

  open AlgN.Mom A R M G (λ j → refl) Pas E M0 Mle using (moment)

  -- (n+1) ∫ eⁿ = 1, where `# (suc n)` is the natural number n+1 in the semiring
  moment-N : ∀ n → # (suc n) * M n ≈ 1#
  moment-N = moment

  M≤1 : ∀ n → M n ≤ 1#
  M≤1 n = ≤-trans (I-mono fairCoin (Fgf n 0) (Fun-const 1# ≤-refl) (gf≤1 n 0))
    (≤-reflexive (I-const fairCoin L-one 1# ≤-refl))

  -- the function eⁿ itself, with `∫ eⁿ = M n`
  Fpow : ∀ n → Fun (λ r → pw (expansion r) n)
  Fpow n = Meas→Fun (λ r → pw≤1 (expansion≤1 r) n) (Meas-pw (LS Fun-expansion) n)

  I-pow : ∀ n → I fairCoin (λ r → pw (expansion r) n) (Fpow n) ≈ M n
  I-pow n = I-cong fairCoin (λ r → sym (*-identityʳ _)) (Fpow n) (Fgf n 0)
