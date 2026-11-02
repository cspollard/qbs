{-# OPTIONS --safe --without-K #-}

-- The algebra behind `∫₀^∞ e^{−x} dx = 1`, in an abstract `OmegaSemiring` with an Archimedean structure
-- (`Arch`).  There is no subtraction and no division, so every statement is multiplied or added out.
--   * `Geo`: if `I + g ≈ 1` and `gᴺ (N+1) ≤ 1` for all N, then `(∑ gⁿ) I ≈ 1`.  The telescoping partial sums
--     satisfy `(∑_{n<N} gⁿ) I + gᴺ = 1`; the upper bound is direct, and the lower bound uses `gᴺ ≤ ½ⁿ` for
--     `N = 2ⁿ`, then `arch`.
--   * `norm`: the self-similar half of `∫₀¹ e^{−u} du + e^{−1} = 1`.  Let `q m = e^{−2⁻ᵐ}` (so
--     `q m = q (m+1)²`), `x m = 2⁻ᵐ ∫₀¹ e^{−2⁻ᵐ u} du`.  Splitting off the first bit gives
--     `x m = (1 + q (m+1)) x (m+1)`, so `x 0 = ss q k · x k` where `ss q k = ∏ (1 + q ·)` is the geometric
--     sum `∑_{l<2ᵏ} q_k^l`.  The estimates `h y s + q 0 ≤ 1 + 2ε` and `1 ≤ h y s + q 0 + ε`
--     (`h = 2⁻ᵏ`, `ε = 2ᵏ h² = h`, `y = q k`) are proved by induction on the depth (the error doubles at
--     each level, which `2ᵏ h² = h` absorbs), from the one-step facts `y + h y ≤ 1 ≤ y + h y + h²`
--     (these are `1 + h ≤ eʰ ≤ 1 + h + h²`).  `arch` then pins `x 0 + q 0 ≈ 1`.
--   * `norm-s`: the same pin at every offset, `x j + q j ≈ 1` (the estimates run from the shifted sequences, with
--     tolerances `hs j i = ½ⁱ⁺ʲ` and error `½ʲ hs j i ≤ ½ⁱ`).
--   * `GeoMean`: if `I + g ≈ 1` and `K + 2g ≈ 1` then `(∑ gⁿ (n I + K)) ≈ 1`; the partial sums satisfy
--     `∑_{n<N} gⁿ (n I + K) + (N+1) gᴺ = 1`, and `(2s+1) g²ˢ ≤ 2 gˢ` makes the error small.
--   * the ring identities for the first-bit split of `K = ∫₀¹ u e^{−hu} du` (`w-alg`, `K-rec-alg`, ...), proved here
--     over the abstract semiring because the solver is slow on the concrete cut semiring.
module QBS.Analysis.GeometricNorm where

open import Level using (suc) renaming (zero to lzero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_; _,_)
open import QBS.Analysis.Omega
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Exp using (module Exp)

module GeometricNorm (A : OmegaSemiring (suc lzero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-zero; hp-double; hp-≤; half-twice; arch)
  open Series A using (psum; ∑ᶠ; ∑ᶠ-scale; ∑ᶠ-lub; psum≤∑ᶠ; psum-scale)
  open Exp A using (pw; natE)
  open import Relation.Binary.Reasoning.PartialOrder poset
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
    using (solve; _:+_; _:*_; _:=_; con)

  ----------------------------------------------------------------------------
  -- small order lemmas

  *-monoˡ : ∀ {a b} c → a ≤ b → a * c ≤ b * c
  *-monoˡ {a} {b} c h = ≤-trans (≤-reflexive (*-comm a c)) (≤-trans (*-mono c h) (≤-reflexive (*-comm c b)))

  ≤1-mul : ∀ {a} c → a ≤ 1# → a * c ≤ c
  ≤1-mul {a} c h = ≤-trans (*-monoˡ c h) (≤-reflexive (*-identityˡ c))

  ----------------------------------------------------------------------------
  -- the product `∏ (1 + q ·)` and its factorisation of `x`

  ss : (ℕ → ∣A∣) → ℕ → ∣A∣
  ss q ℕ.zero = 1#
  ss q (ℕ.suc i) = (1# + q 1) * ss (λ m → q (ℕ.suc m)) i

  ss-prod : ∀ (q x : ℕ → ∣A∣) → (∀ m → x m ≈ (1# + q (ℕ.suc m)) * x (ℕ.suc m)) → ∀ i → x 0 ≈ ss q i * x i
  ss-prod q x hx ℕ.zero = sym (*-identityˡ _)
  ss-prod q x hx (ℕ.suc i) = trans (hx 0)
    (trans (*-cong refl (ss-prod (λ m → q (ℕ.suc m)) (λ m → x (ℕ.suc m)) (λ m → hx (ℕ.suc m)) i))
           (sym (*-assoc _ _ _)))

  hp≤1 : ∀ n → hp n ≤ 1#
  hp≤1 ℕ.zero = ≤-reflexive hp-zero
  hp≤1 (ℕ.suc n) = ≤-trans (hp-≤ n) (hp≤1 n)

  -- 2ⁱ, with `hpⁱ 2ⁱ = 1`
  two : ℕ → ∣A∣
  two ℕ.zero = 1#
  two (ℕ.suc i) = two i + two i

  hp-two : ∀ i → hp i * two i ≈ 1#
  hp-two ℕ.zero = trans (*-identityʳ _) hp-zero
  hp-two (ℕ.suc i) = begin-equality
    (half * hp i) * (two i + two i)  ≈⟨ *-assoc _ _ _ ⟩
    half * (hp i * (two i + two i))  ≈⟨ *-cong refl (*-comm _ _) ⟩
    half * ((two i + two i) * hp i)  ≈⟨ sym (*-assoc _ _ _) ⟩
    (half * (two i + two i)) * hp i  ≈⟨ *-cong (half-twice (two i)) refl ⟩
    two i * hp i                     ≈⟨ *-comm _ _ ⟩
    hp i * two i                     ≈⟨ hp-two i ⟩
    1# ∎

  -- the error `2ⁱ h²` is `h`
  E : (ℕ → ∣A∣) → ℕ → ∣A∣
  E hh i = two i * (hh i * hh i)

  E-hp : ∀ i → E hp i ≈ hp i
  E-hp i = begin-equality
    two i * (hp i * hp i)  ≈⟨ solve 2 (λ t h → t :* (h :* h) := (h :* t) :* h) refl (two i) (hp i) ⟩
    (hp i * two i) * hp i  ≈⟨ *-cong (hp-two i) refl ⟩
    1# * hp i              ≈⟨ *-identityˡ _ ⟩
    hp i ∎

  ----------------------------------------------------------------------------
  -- the one-step algebra

  U-step : ∀ {W q0 q1 e} → q0 ≈ q1 * q1 → q1 ≤ 1# → W + q1 ≤ 1# + (e + e) →
    W + (q1 * W + q0) ≤ 1# + ((e + e) + (e + e))
  U-step {W} {q0} {q1} {e} hq q1≤1 ih = begin
    W + (q1 * W + q0)                  ≈⟨ +-cong refl (+-cong refl hq) ⟩
    W + (q1 * W + q1 * q1)             ≈⟨ +-cong refl (sym (distribˡ q1 W q1)) ⟩
    W + q1 * (W + q1)                  ≤⟨ +-mono ≤-refl (*-mono q1 ih) ⟩
    W + q1 * (1# + (e + e))            ≈⟨ solve 3 (λ W q e → W :+ q :* (con 1 :+ e) := (W :+ q) :+ q :* e) refl W q1 (e + e) ⟩
    (W + q1) + q1 * (e + e)            ≤⟨ +-mono ih (≤1-mul (e + e) q1≤1) ⟩
    (1# + (e + e)) + (e + e)           ≈⟨ +-assoc _ _ _ ⟩
    1# + ((e + e) + (e + e)) ∎

  L-step : ∀ {V q0 q1 e} → q0 ≈ q1 * q1 → q1 ≤ 1# → 1# ≤ V + (q1 + e) →
    1# ≤ ((1# + q1) * V) + (q0 + (e + e))
  L-step {V} {q0} {q1} {e} hq q1≤1 ih = begin
    1#                                                  ≤⟨ ih ⟩
    V + (q1 + e)                                        ≈⟨ +-cong refl (+-cong (sym (*-identityʳ q1)) refl) ⟩
    V + (q1 * 1# + e)                                   ≤⟨ +-mono ≤-refl (+-mono (*-mono q1 ih) ≤-refl) ⟩
    V + (q1 * (V + (q1 + e)) + e)                       ≈⟨ solve 3 (λ V q e → V :+ (q :* (V :+ (q :+ e)) :+ e)
                                                              := ((con 1 :+ q) :* V) :+ (q :* q :+ (q :* e :+ e))) refl V q1 e ⟩
    ((1# + q1) * V) + (q1 * q1 + (q1 * e + e))          ≤⟨ +-mono ≤-refl (+-mono ≤-refl (+-mono (≤1-mul e q1≤1) ≤-refl)) ⟩
    ((1# + q1) * V) + (q1 * q1 + (e + e))               ≈⟨ +-cong refl (+-cong (sym hq) refl) ⟩
    ((1# + q1) * V) + (q0 + (e + e)) ∎

  ----------------------------------------------------------------------------
  -- the invariants, by induction on the depth (sequences are shifted instead of indexed by an offset)

  HU HL : (ℕ → ∣A∣) → (ℕ → ∣A∣) → Set (suc lzero)
  HU q hh = ∀ m → hh m * 1# + q m ≤ 1# + ((1# * (hh m * hh m)) + (1# * (hh m * hh m)))
  HL q hh = ∀ m → 1# ≤ (hh m * q m) * 1# + (q m + 1# * (hh m * hh m))

  Hq H1 : (ℕ → ∣A∣) → Set (suc lzero)
  Hq q = ∀ m → q m ≈ q (ℕ.suc m) * q (ℕ.suc m)
  H1 q = ∀ m → q m ≤ 1#

  U-inv : ∀ q hh → Hq q → H1 q → HU q hh → ∀ i → hh i * ss q i + q 0 ≤ 1# + (E hh i + E hh i)
  U-inv q hh hq q1 hu ℕ.zero = hu 0
  U-inv q hh hq q1 hu (ℕ.suc i) = ≤-trans
    (≤-reflexive (solve 4 (λ h q1 s q0 → h :* ((con 1 :+ q1) :* s) :+ q0 := h :* s :+ (q1 :* (h :* s) :+ q0)) refl
                   (hh (ℕ.suc i)) (q 1) (ss (λ m → q (ℕ.suc m)) i) (q 0)))
    (≤-trans (U-step {hh (ℕ.suc i) * ss (λ m → q (ℕ.suc m)) i} {q 0} {q 1} {E (λ m → hh (ℕ.suc m)) i}
                (hq 0) (q1 1)
                (U-inv (λ m → q (ℕ.suc m)) (λ m → hh (ℕ.suc m)) (λ m → hq (ℕ.suc m)) (λ m → q1 (ℕ.suc m))
                   (λ m → hu (ℕ.suc m)) i))
      (≤-reflexive (+-cong refl (solve 2 (λ t h → (t :* (h :* h) :+ t :* (h :* h)) :+ (t :* (h :* h) :+ t :* (h :* h))
                                           := ((t :+ t) :* (h :* h)) :+ ((t :+ t) :* (h :* h))) refl
                                   (two i) (hh (ℕ.suc i))))))

  L-inv : ∀ q hh → Hq q → H1 q → HL q hh → ∀ i → 1# ≤ (hh i * q i) * ss q i + (q 0 + E hh i)
  L-inv q hh hq q1 hl ℕ.zero = hl 0
  L-inv q hh hq q1 hl (ℕ.suc i) = ≤-trans
    (L-step {(hh (ℕ.suc i) * q (ℕ.suc i)) * ss (λ m → q (ℕ.suc m)) i} {q 0} {q 1} {E (λ m → hh (ℕ.suc m)) i}
       (hq 0) (q1 1)
       (L-inv (λ m → q (ℕ.suc m)) (λ m → hh (ℕ.suc m)) (λ m → hq (ℕ.suc m)) (λ m → q1 (ℕ.suc m))
          (λ m → hl (ℕ.suc m)) i))
    (≤-reflexive (solve 6 (λ h y s q0 q1 t →
        ((con 1 :+ q1) :* ((h :* y) :* s)) :+ (q0 :+ (t :* (h :* h) :+ t :* (h :* h)))
        := ((h :* y) :* ((con 1 :+ q1) :* s)) :+ (q0 :+ ((t :+ t) :* (h :* h)))) refl
        (hh (ℕ.suc i)) (q (ℕ.suc i)) (ss (λ m → q (ℕ.suc m)) i) (q 0) (q 1) (two i)))

  eqU : ∀ y h → y + h * (y + (h * y + h * h)) ≈ (y + h * y) + (h * (h * y) + h * (h * h))
  eqU y h = solve 3 (λ y h hh → y :+ h :* (y :+ (h :* y :+ hh)) := (y :+ h :* y) :+ (h :* (h :* y) :+ h :* hh))
              refl y h (h * h)

  small-sq : ∀ {y h} → y ≤ 1# → h ≤ 1# → h * (h * y) + h * (h * h) ≤ h * h + h * h
  small-sq {y} {h} y≤1 h≤1 = +-mono (*-mono h (≤-trans (≤-reflexive (*-comm h y)) (≤1-mul h y≤1))) (≤1-mul (h * h) h≤1)

  -- the one-step facts `y + h y ≤ 1 ≤ y + h y + h²` give the base cases
  baseU : ∀ {y h} → y ≤ 1# → h ≤ 1# → y + h * y ≤ 1# → 1# ≤ y + (h * y + h * h) →
    h * 1# + y ≤ 1# + ((1# * (h * h)) + (1# * (h * h)))
  baseU {y} {h} y≤1 h≤1 b c = begin
    h * 1# + y                                 ≈⟨ +-comm _ _ ⟩
    y + h * 1#                                 ≈⟨ +-cong refl (*-identityʳ h) ⟩
    y + h                                      ≈⟨ +-cong refl (sym (*-identityʳ h)) ⟩
    y + h * 1#                                 ≤⟨ +-mono ≤-refl (*-mono h c) ⟩
    y + h * (y + (h * y + h * h))              ≈⟨ eqU y h ⟩
    (y + h * y) + (h * (h * y) + h * (h * h))  ≤⟨ +-mono b (small-sq y≤1 h≤1) ⟩
    1# + (h * h + h * h)                       ≈⟨ +-cong refl (+-cong (sym (*-identityˡ _)) (sym (*-identityˡ _))) ⟩
    1# + ((1# * (h * h)) + (1# * (h * h))) ∎

  eqL : ∀ y h → y + (h * y + h * h) ≈ (h * y) * 1# + (y + 1# * (h * h))
  eqL y h = solve 3 (λ y h hh → y :+ (h :* y :+ hh) := (h :* y) :* con 1 :+ (y :+ con 1 :* hh)) refl y h (h * h)

  baseL : ∀ {y h} → 1# ≤ y + (h * y + h * h) → 1# ≤ (h * y) * 1# + (y + 1# * (h * h))
  baseL {y} {h} c = ≤-trans c (≤-reflexive (eqL y h))

  -- the base facts, from `y e = 1`, `1 + h ≤ e ≤ 1 + h + h²` (`e = eʰ`, `y = e^{−h}`)
  base : ∀ {y h e} → y * e ≈ 1# → 1# + h ≤ e → e ≤ 1# + (h + h * h) → y ≤ 1# → h ≤ 1# →
    (h * 1# + y ≤ 1# + ((1# * (h * h)) + (1# * (h * h)))) × (1# ≤ (h * y) * 1# + (y + 1# * (h * h)))
  base {y} {h} {e} ye lo hi y≤1 h≤1 = baseU y≤1 h≤1 b c , baseL c
    where
      b : y + h * y ≤ 1#
      b = begin
        y + h * y        ≈⟨ solve 2 (λ y h → y :+ h :* y := y :* (con 1 :+ h)) refl y h ⟩
        y * (1# + h)     ≤⟨ *-mono y lo ⟩
        y * e            ≈⟨ ye ⟩
        1# ∎
      c : 1# ≤ y + (h * y + h * h)
      c = begin
        1#                           ≈⟨ sym ye ⟩
        y * e                        ≤⟨ *-mono y hi ⟩
        y * (1# + (h + h * h))       ≈⟨ solve 3 (λ y h hh → y :* (con 1 :+ (h :+ hh)) := y :+ (h :* y :+ y :* hh)) refl y h (h * h) ⟩
        y + (h * y + y * (h * h))    ≤⟨ +-mono ≤-refl (+-mono ≤-refl (≤1-mul (h * h) y≤1)) ⟩
        y + (h * y + h * h) ∎

  -- one step of the self-similar recursion: `hⱼ (½ (q F) + ½ F) = (1 + q) (½ hⱼ F)`
  rec-alg : ∀ hj q F → hj * (half * (q * F) + half * F) ≈ (1# + q) * ((half * hj) * F)
  rec-alg hj q F = solve 4 (λ h q F hf → h :* (hf :* (q :* F) :+ hf :* F) := (con 1 :+ q) :* ((hf :* h) :* F)) refl hj q F half

  -- shifting the argument by the first bit: `hⱼ (½ + ½ e) = ½ hⱼ + (½ hⱼ) e` and `hⱼ (½ e) = (½ hⱼ) e`
  true-alg : ∀ hj e → hj * (half + half * e) ≈ half * hj + (half * hj) * e
  true-alg hj e = solve 3 (λ h e hf → h :* (hf :+ hf :* e) := hf :* h :+ (hf :* h) :* e) refl hj e half

  false-alg : ∀ hj e → hj * (half * e) ≈ (half * hj) * e
  false-alg hj e = solve 3 (λ h e hf → h :* (hf :* e) := (hf :* h) :* e) refl hj e half

  -- the recursion for `w = (hⱼ)² K + hⱼ q` (`K = ∫₀¹ u e^{−hⱼu} du`), from `x' + q' = 1` where `x' = a F'`,
  -- `a = ½ hⱼ`, `hⱼ = a + a`:  `(a a)(q F' + q K' + K') + (a + a) q q = (1 + q)((a a) K' + a q)`
  w-alg : ∀ a q F K → (a * F) + q ≈ 1# → (a * a) * (q * F + q * K + K) + (a + a) * (q * q) ≈ (1# + q) * ((a * a) * K + a * q)
  w-alg a q F K s = begin-equality
    (a * a) * (q * F + q * K + K) + (a + a) * (q * q)
      ≈⟨ solve 4 (λ a q F K → (a :* a) :* (q :* F :+ q :* K :+ K) :+ (a :+ a) :* (q :* q)
                              := (a :* q) :* ((a :* F) :+ q) :+ ((a :* a) :* (q :* K) :+ (a :* a) :* K :+ a :* (q :* q))) refl a q F K ⟩
    (a * q) * ((a * F) + q) + ((a * a) * (q * K) + (a * a) * K + a * (q * q))
      ≈⟨ +-cong (*-cong refl s) refl ⟩
    (a * q) * 1# + ((a * a) * (q * K) + (a * a) * K + a * (q * q))
      ≈⟨ solve 4 (λ a q F K → (a :* q) :* con 1 :+ ((a :* a) :* (q :* K) :+ (a :* a) :* K :+ a :* (q :* q))
                              := (con 1 :+ q) :* ((a :* a) :* K :+ a :* q)) refl a q F K ⟩
    (1# + q) * ((a * a) * K + a * q) ∎

  -- the first-bit algebra for `K = ∫₀¹ u e^{−hⱼu} du`: with `c = q ½` (`q = e^{−½hⱼ}`),
  --   `(½ + ½e)(q G) = c G + c (e G)`,  `(½e) G = ½ (e G)`,
  --   `hⱼ² (½ (c F + c K) + ½ (½ K)) = (a a)(q F + q K + K)`  for `a = ½ hⱼ`
  K-true-alg : ∀ e q G → (half + half * e) * (q * G) ≈ (q * half) * G + (q * half) * (e * G)
  K-true-alg e q G = solve 4 (λ h e q G → (h :+ h :* e) :* (q :* G) := (q :* h) :* G :+ (q :* h) :* (e :* G)) refl half e q G

  K-false-alg : ∀ e G → (half * e) * G ≈ half * (e * G)
  K-false-alg e G = solve 3 (λ h e G → (h :* e) :* G := h :* (e :* G)) refl half e G

  K-rec-alg : ∀ hj q F K → (hj * hj) * (half * ((q * half) * F + (q * half) * K) + half * (half * K))
    ≈ ((half * hj) * (half * hj)) * (q * F + q * K + K)
  K-rec-alg hj q F K = solve 5 (λ hj h q F K → (hj :* hj) :* (h :* ((q :* h) :* F :+ (q :* h) :* K) :+ h :* (h :* K))
    := ((h :* hj) :* (h :* hj)) :* (q :* F :+ q :* K :+ K)) refl hj half q F K

  -- `h (e G) + G = G (1 + h e)` (the pointwise bound `(1 + t) e^{−t} ≤ 1`), `h² K + h F = h (h K + F)`, and
  -- the scale-one form `(1·1) K + 1·q + q = K + 2q`
  KG-alg : ∀ h e G → h * (e * G) + G ≈ G * (1# + h * e)
  KG-alg h e G = solve 3 (λ h e G → h :* (e :* G) :+ G := G :* (con 1 :+ h :* e)) refl h e G

  ww-alg : ∀ h K F → (h * h) * K + h * F ≈ h * (h * K + F)
  ww-alg h K F = solve 3 (λ h K F → (h :* h) :* K :+ h :* F := h :* (h :* K :+ F)) refl h K F

  K-fin-alg : ∀ K q → ((1# * 1#) * K + 1# * q) + q ≈ K + (q + q)
  K-fin-alg K q = solve 2 (λ K q → ((con 1 :* con 1) :* K :+ con 1 :* q) :+ q := K :+ (q :+ q)) refl K q

  -- `(n + e)(P (n' ...))`: `(n + e)(P N) = P (n N + e N)`
  shift-alg : ∀ n e P N → (n + e) * (P * N) ≈ P * (n * N + e * N)
  shift-alg n e P N = solve 4 (λ n e P N → (n :+ e) :* (P :* N) := P :* (n :* N :+ e :* N)) refl n e P N

  ----------------------------------------------------------------------------
  -- the pinned value: `x 0 + q 0 ≈ 1`

  Rec : (ℕ → ∣A∣) → (ℕ → ∣A∣) → Set (suc lzero)
  Rec q x = ∀ m → x m ≈ (1# + q (ℕ.suc m)) * x (ℕ.suc m)

  norm-up : ∀ q x → Hq q → H1 q → HU q hp → Rec q x → (∀ m → x m ≤ hp m) → ∀ n → x 0 + q 0 ≤ 1# + hp n
  norm-up q x hq q1 hu hx hi n = begin
    x 0 + q 0                  ≈⟨ +-cong (ss-prod q x hx k) refl ⟩
    ss q k * x k + q 0         ≤⟨ +-mono (≤-trans (*-mono (ss q k) (hi k)) (≤-reflexive (*-comm _ _))) ≤-refl ⟩
    hp k * ss q k + q 0        ≤⟨ U-inv q hp hq q1 hu k ⟩
    1# + (E hp k + E hp k)     ≈⟨ +-cong refl (+-cong (E-hp k) (E-hp k)) ⟩
    1# + (hp k + hp k)         ≈⟨ +-cong refl (hp-double n) ⟩
    1# + hp n ∎
    where k = ℕ.suc n

  norm-low : ∀ q x → Hq q → H1 q → HL q hp → Rec q x → (∀ m → hp m * q m ≤ x m) → ∀ k → 1# ≤ (x 0 + q 0) + hp k
  norm-low q x hq q1 hl hx lo k = begin
    1#                                      ≤⟨ L-inv q hp hq q1 hl k ⟩
    (hp k * q k) * ss q k + (q 0 + E hp k)  ≤⟨ +-mono (≤-trans (*-monoˡ (ss q k) (lo k)) (≤-reflexive (*-comm _ _)))
                                                 (+-mono ≤-refl (≤-reflexive (E-hp k))) ⟩
    ss q k * x k + (q 0 + hp k)             ≈⟨ +-cong (sym (ss-prod q x hx k)) refl ⟩
    x 0 + (q 0 + hp k)                      ≈⟨ sym (+-assoc _ _ _) ⟩
    (x 0 + q 0) + hp k ∎

  norm : ∀ (q x : ℕ → ∣A∣) → Hq q → H1 q → HU q hp → HL q hp → Rec q x →
    (∀ m → hp m * q m ≤ x m) → (∀ m → x m ≤ hp m) → x 0 + q 0 ≈ 1#
  norm q x hq q1 hu hl hx lo hi = ≤-antisym (arch (norm-up q x hq q1 hu hx hi)) (arch (norm-low q x hq q1 hl hx lo))

  ----------------------------------------------------------------------------
  -- the pinned value at every offset: `x j + q j ≈ 1#`.  The same estimates run from the shifted sequences
  -- `q (i + j)`, `x (i + j)` with tolerances `hs j i = ½ⁱ⁺ʲ`: the error `2ⁱ (hs j i)²` is `½ʲ hs j i ≤ ½ⁱ`.

  hs : ℕ → ℕ → ∣A∣
  hs j i = hp (i ℕ.+ j)

  hs-two : ∀ j i → hs j i * two i ≈ hp j
  hs-two j ℕ.zero = *-identityʳ _
  hs-two j (ℕ.suc i) = begin-equality
    (half * hs j i) * (two i + two i)  ≈⟨ *-assoc _ _ _ ⟩
    half * (hs j i * (two i + two i))  ≈⟨ *-cong refl (*-comm _ _) ⟩
    half * ((two i + two i) * hs j i)  ≈⟨ sym (*-assoc _ _ _) ⟩
    (half * (two i + two i)) * hs j i  ≈⟨ *-cong (half-twice (two i)) refl ⟩
    two i * hs j i                     ≈⟨ *-comm _ _ ⟩
    hs j i * two i                     ≈⟨ hs-two j i ⟩
    hp j ∎

  hs≤hp : ∀ j i → hs j i ≤ hp i
  hs≤hp j ℕ.zero = ≤-trans (hp≤1 j) (≤-reflexive (sym hp-zero))
  hs≤hp j (ℕ.suc i) = *-mono half (hs≤hp j i)

  E-hs : ∀ j i → E (hs j) i ≤ hp i
  E-hs j i = ≤-trans (≤-reflexive (solve 2 (λ t h → t :* (h :* h) := (h :* t) :* h) refl (two i) (hs j i)))
    (≤-trans (≤-reflexive (*-cong (hs-two j i) refl)) (≤-trans (≤1-mul (hs j i) (hp≤1 j)) (hs≤hp j i)))

  norm-up-s : ∀ q x → Hq q → H1 q → HU q hp → Rec q x → (∀ m → x m ≤ hp m) → ∀ j n → x j + q j ≤ 1# + hp n
  norm-up-s q x hq q1 hu hx hi j n = begin
    x j + q j                       ≈⟨ +-cong (ss-prod q′ x′ (λ m → hx (m ℕ.+ j)) k) refl ⟩
    ss q′ k * x′ k + q j            ≤⟨ +-mono (≤-trans (*-mono (ss q′ k) (hi (k ℕ.+ j))) (≤-reflexive (*-comm _ _))) ≤-refl ⟩
    hs j k * ss q′ k + q j          ≤⟨ U-inv q′ (hs j) (λ m → hq (m ℕ.+ j)) (λ m → q1 (m ℕ.+ j)) (λ m → hu (m ℕ.+ j)) k ⟩
    1# + (E (hs j) k + E (hs j) k)  ≤⟨ +-mono ≤-refl (+-mono (E-hs j k) (E-hs j k)) ⟩
    1# + (hp k + hp k)              ≈⟨ +-cong refl (hp-double n) ⟩
    1# + hp n ∎
    where
      k = ℕ.suc n
      q′ = λ i → q (i ℕ.+ j)
      x′ = λ i → x (i ℕ.+ j)

  norm-low-s : ∀ q x → Hq q → H1 q → HL q hp → Rec q x → (∀ m → hp m * q m ≤ x m) → ∀ j k → 1# ≤ (x j + q j) + hp k
  norm-low-s q x hq q1 hl hx lo j k = begin
    1#                                         ≤⟨ L-inv q′ (hs j) (λ m → hq (m ℕ.+ j)) (λ m → q1 (m ℕ.+ j)) (λ m → hl (m ℕ.+ j)) k ⟩
    (hs j k * q′ k) * ss q′ k + (q j + E (hs j) k)
                                               ≤⟨ +-mono (≤-trans (*-monoˡ (ss q′ k) (lo (k ℕ.+ j))) (≤-reflexive (*-comm _ _)))
                                                    (+-mono ≤-refl (E-hs j k)) ⟩
    ss q′ k * x′ k + (q j + hp k)              ≈⟨ +-cong (sym (ss-prod q′ x′ (λ m → hx (m ℕ.+ j)) k)) refl ⟩
    x j + (q j + hp k)                         ≈⟨ sym (+-assoc _ _ _) ⟩
    (x j + q j) + hp k ∎
    where
      q′ = λ i → q (i ℕ.+ j)
      x′ = λ i → x (i ℕ.+ j)

  -- `x j + q j ≈ 1#` for every `j`
  norm-s : ∀ (q x : ℕ → ∣A∣) → Hq q → H1 q → HU q hp → HL q hp → Rec q x →
    (∀ m → hp m * q m ≤ x m) → (∀ m → x m ≤ hp m) → ∀ j → x j + q j ≈ 1#
  norm-s q x hq q1 hu hl hx lo hi j =
    ≤-antisym (arch (norm-up-s q x hq q1 hu hx hi j)) (arch (norm-low-s q x hq q1 hl hx lo j))

  ----------------------------------------------------------------------------
  -- the geometric sum: `I + g = 1` gives `(∑ gⁿ) I = 1`

  natE-+ : ∀ a b → natE (a ℕ.+ b) ≈ natE a + natE b
  natE-+ ℕ.zero b = sym (+-identityˡ _)
  natE-+ (ℕ.suc a) b = begin-equality
    natE (a ℕ.+ b) + 1#          ≈⟨ +-cong (natE-+ a b) refl ⟩
    (natE a + natE b) + 1#       ≈⟨ solve 3 (λ a b o → (a :+ b) :+ o := (a :+ o) :+ b) refl (natE a) (natE b) 1# ⟩
    (natE a + 1#) + natE b ∎

  twoN : ℕ → ℕ
  twoN ℕ.zero = 1
  twoN (ℕ.suc n) = twoN n ℕ.+ twoN n

  two≈ : ∀ n → two n ≈ natE (twoN n)
  two≈ ℕ.zero = sym (+-identityˡ 1#)
  two≈ (ℕ.suc n) = trans (+-cong (two≈ n) (two≈ n)) (sym (natE-+ (twoN n) (twoN n)))

  tele-alg : ∀ P G I g → (P + G) * I + g * G ≈ P * I + G * (I + g)
  tele-alg P G I g = solve 4 (λ P G I g → (P :+ G) :* I :+ g :* G := P :* I :+ G :* (I :+ g)) refl P G I g

  module Geo (g I : ∣A∣) (h : I + g ≈ 1#) (gb : ∀ N → pw g N * natE (ℕ.suc N) ≤ 1#) where

    tele : ∀ N → psum (pw g) N * I + pw g N ≈ 1#
    tele ℕ.zero = trans (+-cong (zeroˡ I) refl) (+-identityˡ 1#)
    tele (ℕ.suc N) = begin-equality
      (psum (pw g) N + pw g N) * I + g * pw g N  ≈⟨ tele-alg (psum (pw g) N) (pw g N) I g ⟩
      psum (pw g) N * I + pw g N * (I + g)       ≈⟨ +-cong refl (trans (*-cong refl h) (*-identityʳ _)) ⟩
      psum (pw g) N * I + pw g N                 ≈⟨ tele N ⟩
      1# ∎

    upper : ∑ᶠ (pw g) * I ≤ 1#
    upper = ≤-trans (≤-reflexive (trans (*-comm _ _) (∑ᶠ-scale I (pw g))))
      (∑ᶠ-lub (λ N → ≤-trans (≤-reflexive (psum-scale I (pw g) N))
        (≤-trans (≤-reflexive (*-comm I _)) (≤-trans ≤-+ʳ (≤-reflexive (tele N))))))

    -- `gᴺ ≤ ½ⁿ` for `N = 2ⁿ`
    small : ∀ n → pw g (twoN n) ≤ hp n
    small n = begin
      pw g t                                  ≈⟨ sym (*-identityʳ _) ⟩
      pw g t * 1#                             ≈⟨ *-cong refl (sym (trans (*-cong refl (sym (two≈ n))) (hp-two n))) ⟩
      pw g t * (hp n * natE t)                ≈⟨ solve 3 (λ G h N → G :* (h :* N) := h :* (G :* N)) refl (pw g t) (hp n) (natE t) ⟩
      hp n * (pw g t * natE t)                ≤⟨ *-mono (hp n) (*-mono (pw g t) ≤-+ʳ) ⟩
      hp n * (pw g t * natE (ℕ.suc t))        ≤⟨ *-mono (hp n) (gb t) ⟩
      hp n * 1#                               ≈⟨ *-identityʳ _ ⟩
      hp n ∎
      where t = twoN n

    lower : 1# ≤ ∑ᶠ (pw g) * I
    lower = arch (λ n → begin
      1#                                                ≈⟨ sym (tele (twoN n)) ⟩
      psum (pw g) (twoN n) * I + pw g (twoN n)          ≤⟨ +-mono (*-monoˡ I (psum≤∑ᶠ (pw g) (twoN n))) (small n) ⟩
      ∑ᶠ (pw g) * I + hp n ∎)

    total : ∑ᶠ (pw g) * I ≈ 1#
    total = ≤-antisym upper lower

  ----------------------------------------------------------------------------
  -- the series `∑ gⁿ (n I + K)`: `I + g = 1` and `K + 2g = 1` give `∑ gⁿ (n I + K) = 1`.  The partial sums
  -- telescope, `∑_{n<N} gⁿ (n I + K) + (N+1) gᴺ = 1`, and `(2s+1) g²ˢ ≤ 2 gˢ` makes the error small.

  pw-add : ∀ g a b → pw g (a ℕ.+ b) ≈ pw g a * pw g b
  pw-add g ℕ.zero b = sym (*-identityˡ _)
  pw-add g (ℕ.suc a) b = trans (*-cong refl (pw-add g a b)) (sym (*-assoc _ _ _))

  step-ring : ∀ P n I K g → P * (n * I + K) + ((n + 1#) + 1#) * (g * P) ≈ P * (n * (I + g) + (K + (g + g)))
  step-ring P n I K g = solve 5 (λ P n I K g → P :* (n :* I :+ K) :+ ((n :+ con 1) :+ con 1) :* (g :* P)
    := P :* (n :* (I :+ g) :+ (K :+ (g :+ g)))) refl P n I K g

  step-one : ∀ P n → P * (n * 1# + 1#) ≈ (n + 1#) * P
  step-one P n = solve 2 (λ P n → P :* (n :* con 1 :+ con 1) := (n :+ con 1) :* P) refl P n

  module GeoMean (g I K : ∣A∣) (h : I + g ≈ 1#) (k : K + (g + g) ≈ 1#) (gb : ∀ N → pw g N * natE (ℕ.suc N) ≤ 1#) where
    open Geo g I h gb using (small)

    term : ℕ → ∣A∣
    term n = pw g n * (natE n * I + K)

    -- `gⁿ (n I + K) + (n + 2) gⁿ⁺¹ = (n + 1) gⁿ`
    step-alg : ∀ N → term N + natE (ℕ.suc (ℕ.suc N)) * pw g (ℕ.suc N) ≈ natE (ℕ.suc N) * pw g N
    step-alg N = begin-equality
      pw g N * (natE N * I + K) + ((natE N + 1#) + 1#) * (g * pw g N)
        ≈⟨ step-ring (pw g N) (natE N) I K g ⟩
      pw g N * (natE N * (I + g) + (K + (g + g)))  ≈⟨ *-cong refl (+-cong (*-cong refl h) k) ⟩
      pw g N * (natE N * 1# + 1#)                  ≈⟨ step-one (pw g N) (natE N) ⟩
      (natE N + 1#) * pw g N ∎

    tele : ∀ N → psum term N + natE (ℕ.suc N) * pw g N ≈ 1#
    tele ℕ.zero = trans (+-cong refl (trans (*-cong (+-identityˡ 1#) refl) (*-identityˡ 1#))) (+-identityˡ 1#)
    tele (ℕ.suc N) = begin-equality
      (psum term N + term N) + natE (ℕ.suc (ℕ.suc N)) * pw g (ℕ.suc N)  ≈⟨ +-assoc _ _ _ ⟩
      psum term N + (term N + natE (ℕ.suc (ℕ.suc N)) * pw g (ℕ.suc N))  ≈⟨ +-cong refl (step-alg N) ⟩
      psum term N + natE (ℕ.suc N) * pw g N                            ≈⟨ tele N ⟩
      1# ∎

    upper : ∑ᶠ term ≤ 1#
    upper = ∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-reflexive (tele N)))

    -- `(2s+1) g²ˢ ≤ 2 gˢ`
    natE-dbl : ∀ s → natE (ℕ.suc (s ℕ.+ s)) ≤ natE (ℕ.suc s) + natE (ℕ.suc s)
    natE-dbl s = ≤-trans (≤-reflexive (+-cong (natE-+ s s) refl))
      (≤-trans ≤-+ʳ (≤-reflexive (solve 2 (λ n o → ((n :+ n) :+ o) :+ o := (n :+ o) :+ (n :+ o)) refl (natE s) 1#)))

    err : ∀ s → natE (ℕ.suc (s ℕ.+ s)) * pw g (s ℕ.+ s) ≤ pw g s + pw g s
    err s = begin
      natE (ℕ.suc (s ℕ.+ s)) * pw g (s ℕ.+ s)
        ≤⟨ *-mono′ (natE-dbl s) (pw-add g s s) ⟩
      (natE (ℕ.suc s) + natE (ℕ.suc s)) * (pw g s * pw g s)
        ≈⟨ solve 3 (λ N P Q → (N :+ N) :* (P :* Q) := (N :* P) :* Q :+ (N :* P) :* Q) refl (natE (ℕ.suc s)) (pw g s) (pw g s) ⟩
      (natE (ℕ.suc s) * pw g s) * pw g s + (natE (ℕ.suc s) * pw g s) * pw g s
        ≤⟨ +-mono (≤1-mul (pw g s) b) (≤1-mul (pw g s) b) ⟩
      pw g s + pw g s ∎
      where
        b = ≤-trans (≤-reflexive (*-comm _ _)) (gb s)
        *-mono′ : ∀ {a b c d} → a ≤ b → c ≈ d → a * c ≤ b * d
        *-mono′ {a} {b} {c} {d} ab cd = ≤-trans (*-monoˡ c ab) (*-mono b (≤-reflexive cd))

    lower-at : ∀ n → 1# ≤ ∑ᶠ term + hp n
    lower-at n = begin
      1#                                                       ≈⟨ sym (tele (twoN (ℕ.suc (ℕ.suc n)))) ⟩
      psum term M + natE (ℕ.suc M) * pw g M                    ≤⟨ +-mono (psum≤∑ᶠ term M) (err s) ⟩
      ∑ᶠ term + (pw g s + pw g s)                              ≤⟨ +-mono ≤-refl (+-mono (small (ℕ.suc n)) (small (ℕ.suc n))) ⟩
      ∑ᶠ term + (hp (ℕ.suc n) + hp (ℕ.suc n))                  ≈⟨ +-cong refl (hp-double n) ⟩
      ∑ᶠ term + hp n ∎
      where
        s = twoN (ℕ.suc n)
        M = s ℕ.+ s

    lower : 1# ≤ ∑ᶠ term
    lower = arch lower-at

    total : ∑ᶠ term ≈ 1#
    total = ≤-antisym upper lower
