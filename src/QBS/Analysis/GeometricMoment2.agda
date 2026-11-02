{-# OPTIONS --safe --without-K #-}

-- The algebra behind the second moment `∫₀^∞ x² e^{−x} dx = 2` (in an abstract `OmegaSemiring` with an Archimedean
-- structure), the sequel to `GeometricNorm`.  No subtraction and no division, so everything is multiplied out.
-- With `h = 2⁻ʲ`, `q = e^{−h}`, `F = ∫₀¹ e^{−hu}`, `K = ∫₀¹ u e^{−hu}`, `L = ∫₀¹ u² e^{−hu}` (all at scale `j`):
--   * first-bit split of `L`: `(½ + ½e)² (q G) = d G + (q ½)(e G) + d (e² G)` (`d = q ¼`) and `(½e)² G = ¼ (e² G)`;
--   * `x j = ½ h³ L + (h + ½h²) q` has the recursion `x j = (1 + q (j+1)) x (j+1)` (`x2-rec-alg`) given the pins
--     `a F + q = 1` and `a² K + a q + q = 1` at the next scale (`a = h/2`; the true values are `x j = 1 − q j`);
--   * the bounds `h q ≤ x j ≤ h` (`x2-lo`, `x2-hi`; the latter from `h L ≤ F`, `q ≤ F` and `h F + q = 1`), so that
--     `GeometricNorm.norm` pins `x 0 + q 0 = 1`, i.e. `L + 5g = 2` (`L5-alg`);
--   * `GeoMom2`: `I + g = 1`, `K + 2g = 1`, `L + 5g = 2` give `∑ gⁿ (n² I + 2n K + L) = 2`.  The partial sums
--     telescope against `pol N = N² + 2N + 2`, and `pol N gᴺ` is small for `N = 4t`: with `T = t`, `P = gᵗ` it is
--     `16 (T P)² P² + 8 (T P) P³ + 2 P⁴ ≤ 26 P ≤ 32 P`, using `T P ≤ 1` and `P ≤ 1` (from `gᵗ (t + 1) ≤ 1`), and
--     `P ≤ ½ⁿ⁺⁵`.
module QBS.Analysis.GeometricMoment2 where

open import Level using (suc) renaming (zero to lzero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import QBS.Analysis.Omega
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.GeometricNorm using (module GeometricNorm)

module GeometricMoment2 (A : OmegaSemiring (suc lzero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-≤; hp-double; arch; half+half)
  open Series A using (psum; ∑ᶠ; ∑ᶠ-lub; psum≤∑ᶠ)
  open Exp A using (pw; natE)
  open GeometricNorm A R using (hp≤1; natE-+; twoN; pw-add; ≤1-mul; *-monoˡ; module Geo)
  open import Relation.Binary.Reasoning.PartialOrder poset
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
    using (solve; _:+_; _:*_; _:=_; con)

  ----------------------------------------------------------------------------
  -- first-bit split of `u² e^{−hu}`: with `d = q ¼`, `(½ + ½e)² (q G) = d G + ((q ½)(e G) + d (e² G))`

  L-true-alg : ∀ e q G → ((half + half * e) * (half + half * e)) * (q * G)
    ≈ (q * (half * half)) * G + ((q * half) * (e * G) + (q * (half * half)) * ((e * e) * G))
  L-true-alg e q G = begin-equality
    ((half + half * e) * (half + half * e)) * (q * G)
      ≈⟨ solve 4 (λ z e q G → ((z :+ z :* e) :* (z :+ z :* e)) :* (q :* G)
            := (q :* (z :* z)) :* G :+ ((q :* z) :* ((z :+ z) :* (e :* G)) :+ (q :* (z :* z)) :* ((e :* e) :* G))) refl half e q G ⟩
    (q * (half * half)) * G + ((q * half) * ((half + half) * (e * G)) + (q * (half * half)) * ((e * e) * G))
      ≈⟨ +-cong refl (+-cong (*-cong refl (trans (*-cong half+half refl) (*-identityˡ _))) refl) ⟩
    (q * (half * half)) * G + ((q * half) * (e * G) + (q * (half * half)) * ((e * e) * G)) ∎

  L-false-alg : ∀ e G → ((half * e) * (half * e)) * G ≈ (half * half) * ((e * e) * G)
  L-false-alg e G = solve 3 (λ z e G → ((z :* e) :* (z :* e)) :* G := (z :* z) :* ((e :* e) :* G)) refl half e G

  ----------------------------------------------------------------------------
  -- the recursion for `x j = a h² L + (h + a h) q`, `h = a + a`

  -- the first-bit split of `L`
  Lsplit : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣
  Lsplit q F K L = half * ((q * (half * half)) * F + ((q * half) * K + (q * (half * half)) * L)) + half * ((half * half) * L)

  -- the `q²` part of `(h + a h) q²`, with `h = a + a` and (in `a h`) `h = a + ½a + ½a`
  S2 : ∣A∣ → ∣A∣ → ∣A∣
  S2 a q = ((a + a) + a * (a + (half + half) * a)) * (q * q)

  h-alt : ∀ a h → a + a ≈ h → h ≈ a + (half + half) * a
  h-alt a h ah = trans (sym ah) (+-cong refl (sym (trans (*-cong half+half refl) (*-identityˡ a))))

  -- the `L`-part: `a (2a)² Lsplit = a³ (½ (q F + q L + L) + q K)`
  Lfirst : ∀ a q F K L → (a * ((a + a) * (a + a))) * Lsplit q F K L
    ≈ (a * (a * a)) * (half * (q * F + (q * L + L)) + q * K)
  Lfirst a q F K L = trans (solve 6 (λ a z q F K L → (a :* ((a :+ a) :* (a :+ a)))
      :* (z :* ((q :* (z :* z)) :* F :+ ((q :* z) :* K :+ (q :* (z :* z)) :* L)) :+ z :* ((z :* z) :* L))
      := (a :* (a :* a)) :* (((z :+ z) :* (z :+ z)) :* (z :* (q :* F :+ (q :* L :+ L)))
                            :+ ((z :+ z) :* (z :+ z)) :* (q :* K))) refl a half q F K L)
    (trans (*-cong refl (+-cong (*-cong (*-cong half+half half+half) refl) (*-cong (*-cong half+half half+half) refl)))
      (*-cong refl (solve 5 (λ z q F K L → (con 1 :* con 1) :* (z :* (q :* F :+ (q :* L :+ L))) :+ (con 1 :* con 1) :* (q :* K)
        := z :* (q :* F :+ (q :* L :+ L)) :+ q :* K) refl half q F K L)))

  -- the `F`, `K` part, with the remainder `S2`
  REM : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣
  REM a q F K = ((half * (a * (a * a))) * (q * F) + (a * (a * a)) * (q * K)) + S2 a q

  R1 : ∀ a q F K L → (a * (a * a)) * (half * (q * F + (q * L + L)) + q * K) + S2 a q
    ≈ ((half * (a * (a * a))) * L + (half * (a * (a * a))) * (q * L)) + REM a q F K
  R1 a q F K L = solve 6 (λ a z q F K L → (a :* (a :* a)) :* (z :* (q :* F :+ (q :* L :+ L)) :+ q :* K)
      :+ ((a :+ a) :+ a :* (a :+ (z :+ z) :* a)) :* (q :* q)
    := ((z :* (a :* (a :* a))) :* L :+ (z :* (a :* (a :* a))) :* (q :* L))
      :+ (((z :* (a :* (a :* a))) :* (q :* F) :+ (a :* (a :* a)) :* (q :* K))
         :+ ((a :+ a) :+ a :* (a :+ (z :+ z) :* a)) :* (q :* q))) refl a half q F K L

  -- the two pins turn the remainder into `½a²q + a q + a q² + ½a²q²`
  Lrem : ∀ a q F K → a * F + q ≈ 1# → ((a * a) * K + a * q) + q ≈ 1# →
    REM a q F K ≈ ((half * (a * a)) * q) * 1# + ((a * q) * 1# + (a * (q * q) + (half * (a * a)) * (q * q)))
  Lrem a q F K s1 s2 = trans (solve 5 (λ a z q F K →
      ((z :* (a :* (a :* a))) :* (q :* F) :+ (a :* (a :* a)) :* (q :* K)) :+ ((a :+ a) :+ a :* (a :+ (z :+ z) :* a)) :* (q :* q)
    := ((z :* (a :* a)) :* q) :* (a :* F :+ q)
      :+ ((a :* q) :* ((a :* a) :* K :+ a :* q :+ q) :+ (a :* (q :* q) :+ (z :* (a :* a)) :* (q :* q)))) refl a half q F K)
    (+-cong (*-cong refl s1) (+-cong (*-cong refl s2) refl))

  R3 : ∀ a q L → ((half * (a * (a * a))) * L + (half * (a * (a * a))) * (q * L))
      + (((half * (a * a)) * q) * 1# + ((a * q) * 1# + (a * (q * q) + (half * (a * a)) * (q * q))))
    ≈ (1# + q) * (((half * a) * (a * a)) * L + (a + (half * a) * a) * q)
  R3 a q L = solve 4 (λ a z q L → ((z :* (a :* (a :* a))) :* L :+ (z :* (a :* (a :* a))) :* (q :* L))
      :+ (((z :* (a :* a)) :* q) :* con 1 :+ ((a :* q) :* con 1 :+ (a :* (q :* q) :+ (z :* (a :* a)) :* (q :* q))))
    := (con 1 :+ q) :* (((z :* a) :* (a :* a)) :* L :+ (a :+ (z :* a) :* a) :* q)) refl a half q L

  x2-rec-alg : ∀ a h q F K L → a + a ≈ h → (a * F) + q ≈ 1# → ((a * a) * K + a * q) + q ≈ 1# →
    (a * (h * h)) * Lsplit q F K L + (h + a * h) * (q * q)
      ≈ (1# + q) * (((half * a) * (a * a)) * L + (a + (half * a) * a) * q)
  x2-rec-alg a h q F K L ah s1 s2 =
    trans (+-cong (*-cong (*-cong refl (*-cong (sym ah) (sym ah))) refl) (*-cong (+-cong (sym ah) (*-cong refl (h-alt a h ah))) refl))
      (trans (+-cong (Lfirst a q F K L) refl)
        (trans (R1 a q F K L) (trans (+-cong refl (Lrem a q F K s1 s2)) (R3 a q L))))

  -- the bounds `h q ≤ x` and `x ≤ h` (from `h L ≤ F`, `q ≤ F` and `h F + q = 1`)
  x2-lo : ∀ a h q L → h * q ≤ (a * (h * h)) * L + (h + a * h) * q
  x2-lo a h q L = ≤-trans ≤-+ʳ (≤-reflexive (solve 4
    (λ a h q L → h :* q :+ ((a :* (h :* h)) :* L :+ (a :* h) :* q) := (a :* (h :* h)) :* L :+ (h :+ a :* h) :* q) refl a h q L))

  x2-hi : ∀ a h q F L → a + a ≈ h → h * F + q ≈ 1# → h * L ≤ F → q ≤ F →
    (a * (h * h)) * L + (h + a * h) * q ≤ h
  x2-hi a h q F L ah pin hL qF = begin
    (a * (h * h)) * L + (h + a * h) * q
      ≈⟨ solve 4 (λ a h q L → (a :* (h :* h)) :* L :+ (h :+ a :* h) :* q := (a :* h) :* (h :* L :+ q) :+ h :* q) refl a h q L ⟩
    (a * h) * (h * L + q) + h * q
      ≤⟨ +-mono (*-mono (a * h) (+-mono hL qF)) ≤-refl ⟩
    (a * h) * (F + F) + h * q
      ≈⟨ solve 4 (λ a h q F → (a :* h) :* (F :+ F) :+ h :* q := (a :+ a) :* h :* F :+ h :* q) refl a h q F ⟩
    ((a + a) * h) * F + h * q
      ≈⟨ +-cong (*-cong (*-cong ah refl) refl) refl ⟩
    (h * h) * F + h * q
      ≈⟨ solve 3 (λ h F q → (h :* h) :* F :+ h :* q := h :* (h :* F :+ q)) refl h F q ⟩
    h * (h * F + q)
      ≈⟨ *-cong refl pin ⟩
    h * 1#
      ≈⟨ *-identityʳ h ⟩
    h ∎

  -- the shift split: `(n + e)² (P N) = P (n² N + 2n (e N) + e² N)`
  shift-alg2 : ∀ n e P N → ((n + e) * (n + e)) * (P * N) ≈ P * ((n * n) * N + ((n + n) * (e * N) + (e * e) * N))
  shift-alg2 n e P N = solve 4 (λ n e P N → ((n :+ e) :* (n :+ e)) :* (P :* N)
    := P :* ((n :* n) :* N :+ ((n :+ n) :* (e :* N) :+ (e :* e) :* N))) refl n e P N

  ----------------------------------------------------------------------------
  -- pinning at scale one: `x 0 + q 0 = 1` is `L + 5g = 2`  (`x 0 = (½·1)(1·1) L + (1 + ½·1) g`)

  X0 : ∣A∣ → ∣A∣ → ∣A∣
  X0 L g = (((half * 1#) * (1# * 1#)) * L + (1# + (half * 1#) * 1#) * g) + g

  L5-alg : ∀ L g → X0 L g ≈ 1# → L + (((g + g) + (g + g)) + g) ≈ 1# + 1#
  L5-alg L g e = begin-equality
    L + (((g + g) + (g + g)) + g)
      ≈⟨ solve 2 (λ L g → L :+ (((g :+ g) :+ (g :+ g)) :+ g)
            := (con 1 :* L :+ ((con 1 :+ con 1) :+ con 1) :* g) :+ (g :+ g)) refl L g ⟩
    (1# * L + ((1# + 1#) + 1#) * g) + (g + g)
      ≈⟨ +-cong (+-cong (*-cong (sym half+half) refl) (*-cong (+-cong refl (sym half+half)) refl)) refl ⟩
    ((half + half) * L + ((1# + 1#) + (half + half)) * g) + (g + g)
      ≈⟨ solve 3 (λ z L g → ((z :+ z) :* L :+ ((con 1 :+ con 1) :+ (z :+ z)) :* g) :+ (g :+ g)
            := (((z :* con 1) :* (con 1 :* con 1)) :* L :+ (con 1 :+ (z :* con 1) :* con 1) :* g :+ g)
              :+ (((z :* con 1) :* (con 1 :* con 1)) :* L :+ (con 1 :+ (z :* con 1) :* con 1) :* g :+ g)) refl half L g ⟩
    X0 L g + X0 L g
      ≈⟨ +-cong e e ⟩
    1# + 1# ∎

  ----------------------------------------------------------------------------
  -- doubling, and the small-error estimate `16 P + (8 P + 2 P) ≤ ½ⁿ` for `P ≤ ½ⁿ⁺⁵`

  dbl : ∣A∣ → ∣A∣
  dbl x = x + x

  dbl-mono : ∀ {x y} → x ≤ y → dbl x ≤ dbl y
  dbl-mono h = +-mono h h

  dbl-cong : ∀ {x y} → x ≈ y → dbl x ≈ dbl y
  dbl-cong e = +-cong e e

  dbl3-mono : ∀ {x y} → x ≤ y → dbl (dbl (dbl x)) ≤ dbl (dbl (dbl y))
  dbl3-mono h = dbl-mono (dbl-mono (dbl-mono h))

  dbl4-mono : ∀ {x y} → x ≤ y → dbl (dbl (dbl (dbl x))) ≤ dbl (dbl (dbl (dbl y)))
  dbl4-mono h = dbl-mono (dbl3-mono h)

  dbl3-cong : ∀ {x y} → x ≈ y → dbl (dbl (dbl x)) ≈ dbl (dbl (dbl y))
  dbl3-cong e = dbl-cong (dbl-cong (dbl-cong e))

  dbl4-cong : ∀ {x y} → x ≈ y → dbl (dbl (dbl (dbl x))) ≈ dbl (dbl (dbl (dbl y)))
  dbl4-cong e = dbl-cong (dbl3-cong e)

  -- iterated successors
  s² s³ s⁴ s⁵ : ℕ → ℕ
  s² n = ℕ.suc (ℕ.suc n)
  s³ n = ℕ.suc (s² n)
  s⁴ n = ℕ.suc (s³ n)
  s⁵ n = ℕ.suc (s⁴ n)

  dbl-hp3 : ∀ m → dbl (dbl (dbl (hp (s³ m)))) ≈ hp m
  dbl-hp3 m = trans (dbl-cong (dbl-cong (hp-double (s² m)))) (trans (dbl-cong (hp-double (ℕ.suc m))) (hp-double m))

  dbl-hp4 : ∀ m → dbl (dbl (dbl (dbl (hp (s⁴ m))))) ≈ hp m
  dbl-hp4 m = trans (dbl-cong (dbl-hp3 (ℕ.suc m))) (hp-double m)

  err-final : ∀ P n → P ≤ hp (s⁵ n) → dbl (dbl (dbl (dbl P))) + (dbl (dbl (dbl P)) + dbl P) ≤ hp n
  err-final P n h = begin
    dbl (dbl (dbl (dbl P))) + (dbl (dbl (dbl P)) + dbl P)
      ≤⟨ +-mono (dbl4-mono h) (+-mono (dbl3-mono h) (dbl-mono h)) ⟩
    dbl (dbl (dbl (dbl (hp (s⁵ n))))) + (dbl (dbl (dbl (hp (s⁵ n)))) + dbl (hp (s⁵ n)))
      ≈⟨ +-cong (dbl-hp4 (ℕ.suc n)) (+-cong (dbl-hp3 (s² n)) (hp-double (s⁴ n))) ⟩
    hp (ℕ.suc n) + (hp (s² n) + hp (s⁴ n))
      ≤⟨ +-mono ≤-refl (+-mono ≤-refl (≤-trans (hp-≤ (s³ n)) (hp-≤ (s² n)))) ⟩
    hp (ℕ.suc n) + (hp (s² n) + hp (s² n))
      ≈⟨ +-cong refl (hp-double (ℕ.suc n)) ⟩
    hp (ℕ.suc n) + hp (ℕ.suc n)
      ≈⟨ hp-double n ⟩
    hp n ∎

  -- multiplying a doubled sum
  dm : ∀ a b → dbl a * b ≈ dbl (a * b)
  dm a b = distribʳ b a a

  md : ∀ a b → a * dbl b ≈ dbl (a * b)
  md a b = distribˡ a b b

  dm3 : ∀ a b → dbl (dbl (dbl a)) * b ≈ dbl (dbl (dbl (a * b)))
  dm3 a b = trans (dm _ b) (dbl-cong (trans (dm _ b) (dbl-cong (dm a b))))

  dm4 : ∀ a b → dbl (dbl (dbl (dbl a))) * b ≈ dbl (dbl (dbl (dbl (a * b))))
  dm4 a b = trans (dm _ b) (dbl-cong (dm3 a b))

  dd4 : ∀ a b → dbl (dbl a) * dbl (dbl b) ≈ dbl (dbl (dbl (dbl (a * b))))
  dd4 a b = trans (dm (dbl a) _) (dbl-cong (trans (dm a _) (dbl-cong (trans (md a (dbl b)) (dbl-cong (md a b))))))

  q2 : ∀ y → (1# + 1#) * y ≈ dbl y
  q2 y = solve 1 (λ y → (con 1 :+ con 1) :* y := y :+ y) refl y

  -- `pol (4t) · P⁴ = 16 (T P)² P² + 8 (T P) P³ + 2 P⁴` (`T = t`, `P = gᵗ`), with `4T` written as `dbl (dbl T)`
  err-ring : ∀ T P → ((dbl (dbl T) * dbl (dbl T) + (dbl (dbl T) + dbl (dbl T))) + (1# + 1#)) * (P * (P * (P * P)))
    ≈ dbl (dbl (dbl (dbl (((T * P) * (T * P)) * (P * P))))) + (dbl (dbl (dbl ((T * P) * (P * (P * P))))) + dbl (P * (P * (P * P))))
  err-ring T P = trans (distribʳ Q _ _) (trans (+-cong (distribʳ Q _ _) refl) (trans (+-assoc _ _ _)
    (+-cong (trans (*-cong (dd4 T T) refl) (trans (dm4 _ Q) (dbl4-cong (solve 2 (λ T P →
                (T :* T) :* (P :* (P :* (P :* P))) := ((T :* P) :* (T :* P)) :* (P :* P)) refl T P))))
      (+-cong (trans (dm3 T Q) (dbl3-cong (solve 2 (λ T P →
                T :* (P :* (P :* (P :* P))) := (T :* P) :* (P :* (P :* P))) refl T P)))
        (q2 Q)))))
    where Q = P * (P * (P * P))

  ----------------------------------------------------------------------------
  -- the series `∑ gⁿ (n² I + 2n K + L) = 2`

  module GeoMom2 (g I K L : ∣A∣) (h : I + g ≈ 1#) (k : K + (g + g) ≈ 1#) (l : L + (((g + g) + (g + g)) + g) ≈ 1# + 1#)
      (gb : ∀ N → pw g N * natE (ℕ.suc N) ≤ 1#) where
    open Geo g I h gb using (small)

    pol : ℕ → ∣A∣
    pol n = (natE n * natE n + (natE n + natE n)) + (1# + 1#)

    term : ℕ → ∣A∣
    term n = pw g n * ((natE n * natE n) * I + ((natE n + natE n) * K + L))

    step-ring : ∀ P n I K L g → P * ((n * n) * I + ((n + n) * K + L))
      + (((n + 1#) * (n + 1#) + ((n + 1#) + (n + 1#))) + (1# + 1#)) * (g * P)
      ≈ P * ((n * n) * (I + g) + ((n + n) * (K + (g + g)) + (L + (((g + g) + (g + g)) + g))))
    step-ring P n I K L g = solve 6 (λ P n I K L g → P :* ((n :* n) :* I :+ ((n :+ n) :* K :+ L))
      :+ (((n :+ con 1) :* (n :+ con 1) :+ ((n :+ con 1) :+ (n :+ con 1))) :+ (con 1 :+ con 1)) :* (g :* P)
      := P :* ((n :* n) :* (I :+ g) :+ ((n :+ n) :* (K :+ (g :+ g)) :+ (L :+ (((g :+ g) :+ (g :+ g)) :+ g))))) refl P n I K L g

    step-one : ∀ P n → P * ((n * n) * 1# + ((n + n) * 1# + (1# + 1#))) ≈ ((n * n + (n + n)) + (1# + 1#)) * P
    step-one P n = solve 2 (λ P n → P :* ((n :* n) :* con 1 :+ ((n :+ n) :* con 1 :+ (con 1 :+ con 1)))
      := ((n :* n :+ (n :+ n)) :+ (con 1 :+ con 1)) :* P) refl P n

    -- `gⁿ (n² I + 2n K + L) + pol (n+1) gⁿ⁺¹ = pol n gⁿ`
    step-alg : ∀ N → term N + pol (ℕ.suc N) * pw g (ℕ.suc N) ≈ pol N * pw g N
    step-alg N = begin-equality
      term N + pol (ℕ.suc N) * pw g (ℕ.suc N)
        ≈⟨ step-ring (pw g N) (natE N) I K L g ⟩
      pw g N * ((natE N * natE N) * (I + g) + ((natE N + natE N) * (K + (g + g)) + (L + (((g + g) + (g + g)) + g))))
        ≈⟨ *-cong refl (+-cong (*-cong refl h) (+-cong (*-cong refl k) l)) ⟩
      pw g N * ((natE N * natE N) * 1# + ((natE N + natE N) * 1# + (1# + 1#)))
        ≈⟨ step-one (pw g N) (natE N) ⟩
      pol N * pw g N ∎

    pol0 : pol 0 * pw g 0 ≈ 1# + 1#
    pol0 = solve 0 (((con 0 :* con 0 :+ (con 0 :+ con 0)) :+ (con 1 :+ con 1)) :* con 1 := con 1 :+ con 1) refl

    tele : ∀ N → psum term N + pol N * pw g N ≈ 1# + 1#
    tele ℕ.zero = trans (+-identityˡ _) pol0
    tele (ℕ.suc N) = begin-equality
      (psum term N + term N) + pol (ℕ.suc N) * pw g (ℕ.suc N)  ≈⟨ +-assoc _ _ _ ⟩
      psum term N + (term N + pol (ℕ.suc N) * pw g (ℕ.suc N))  ≈⟨ +-cong refl (step-alg N) ⟩
      psum term N + pol N * pw g N                             ≈⟨ tele N ⟩
      1# + 1# ∎

    upper : ∑ᶠ term ≤ 1# + 1#
    upper = ∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-reflexive (tele N)))

    ----------------------------------------------------------------------------
    -- the error `pol N gᴺ` for `N = 4t` (`T = t`, `P = gᵗ`; `P ≤ 1`, `T P ≤ 1` from `P (T + 1) ≤ 1`)

    P≤1 : ∀ t → pw g t ≤ 1#
    P≤1 t = ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (solve 2 (λ P T → P :+ P :* T := P :* (T :+ con 1)) refl (pw g t) (natE t)))) (gb t)

    w≤1 : ∀ t → natE t * pw g t ≤ 1#
    w≤1 t = ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (solve 2 (λ P T → T :* P :+ P := P :* (T :+ con 1)) refl (pw g t) (natE t)))) (gb t)

    -- `4t` as a sum and a product
    nat4 : ∀ t → natE (t ℕ.+ (t ℕ.+ (t ℕ.+ t))) ≈ dbl (dbl (natE t))
    nat4 t = trans (trans (natE-+ t _) (+-cong refl (trans (natE-+ t _) (+-cong refl (natE-+ t t)))))
      (solve 1 (λ T → T :+ (T :+ (T :+ T)) := (T :+ T) :+ (T :+ T)) refl (natE t))

    pw4 : ∀ t → pw g (t ℕ.+ (t ℕ.+ (t ℕ.+ t))) ≈ pw g t * (pw g t * (pw g t * pw g t))
    pw4 t = trans (pw-add g t _) (*-cong refl (trans (pw-add g t _) (*-cong refl (pw-add g t t))))

    pol4 : ∀ t → pol (t ℕ.+ (t ℕ.+ (t ℕ.+ t))) ≈
      (dbl (dbl (natE t)) * dbl (dbl (natE t)) + (dbl (dbl (natE t)) + dbl (dbl (natE t)))) + (1# + 1#)
    pol4 t = +-cong (+-cong (*-cong (nat4 t) (nat4 t)) (+-cong (nat4 t) (nat4 t))) refl

    -- the three monomials are at most `P`
    PP≤P : ∀ t → pw g t * pw g t ≤ pw g t
    PP≤P t = ≤1-mul {pw g t} (pw g t) (P≤1 t)

    PPP≤P : ∀ t → pw g t * (pw g t * pw g t) ≤ pw g t
    PPP≤P t = ≤-trans (≤1-mul {pw g t} (pw g t * pw g t) (P≤1 t)) (PP≤P t)

    A≤P : ∀ t → ((natE t * pw g t) * (natE t * pw g t)) * (pw g t * pw g t) ≤ pw g t
    A≤P t = ≤-trans (*-monoˡ (pw g t * pw g t) (≤1-mul {natE t * pw g t} (natE t * pw g t) (w≤1 t)))
      (≤-trans (≤1-mul {natE t * pw g t} (pw g t * pw g t) (w≤1 t)) (PP≤P t))

    B≤P : ∀ t → (natE t * pw g t) * (pw g t * (pw g t * pw g t)) ≤ pw g t
    B≤P t = ≤-trans (≤1-mul {natE t * pw g t} (pw g t * (pw g t * pw g t)) (w≤1 t)) (PPP≤P t)

    C≤P : ∀ t → pw g t * (pw g t * (pw g t * pw g t)) ≤ pw g t
    C≤P t = ≤-trans (≤1-mul {pw g t} (pw g t * (pw g t * pw g t)) (P≤1 t)) (PPP≤P t)

    err : ∀ t → pol (t ℕ.+ (t ℕ.+ (t ℕ.+ t))) * pw g (t ℕ.+ (t ℕ.+ (t ℕ.+ t)))
      ≤ dbl (dbl (dbl (dbl (pw g t)))) + (dbl (dbl (dbl (pw g t))) + dbl (pw g t))
    err t = ≤-trans (≤-reflexive (trans (*-cong (pol4 t) (pw4 t)) (err-ring (natE t) (pw g t))))
      (+-mono (dbl4-mono (A≤P t)) (+-mono (dbl3-mono (B≤P t)) (dbl-mono (C≤P t))))

    lower-at : ∀ n → 1# + 1# ≤ ∑ᶠ term + hp n
    lower-at n = begin
      1# + 1#                        ≈⟨ sym (tele N) ⟩
      psum term N + pol N * pw g N   ≤⟨ +-mono (psum≤∑ᶠ term N) (≤-trans (err t) (err-final (pw g t) n (small (s⁵ n)))) ⟩
      ∑ᶠ term + hp n ∎
      where
        t = twoN (s⁵ n)
        N = t ℕ.+ (t ℕ.+ (t ℕ.+ t))

    total : ∑ᶠ term ≈ 1# + 1#
    total = ≤-antisym upper (arch lower-at)
