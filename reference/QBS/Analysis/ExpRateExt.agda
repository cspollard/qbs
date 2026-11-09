{-# OPTIONS --safe --without-K #-}

-- Legacy: the halving extension that a future `Deriv.Daff` for rates `l > 1` would absorb (see `Analysis/ExpRate`); kept for
-- `Continuous/ExpRateInt`.
--
-- From small widths to all widths: the extension step that removes the restriction `λ ≤ 1` of the exponential with a rate.
-- The rate-1 data of `Analysis/PolyExpCert` is evaluated at the width `λ t`, which is at most 1 only for `t ≤ ½ᴷ` when
-- `λ ≤ 2ᴷ`.  Over an abstract Archimedean ω-semiring (halving needs only `½ + ½ = 1`), three statements pass from the
-- widths `t ≤ ½ᴷ` to all widths `t ≤ 1` by halving a piece `[a, a + t]` at `a + ½t`, `K` times:
--   * `Plain`: the plain certificate `G (a+t) + t h(a+t) ≤ G a ≤ G (a+t) + t h a` for an antitone `h` (no error term);
--   * `Lip`: a Lipschitz bound `u (a+t) ≤ u a + t E` and `u a ≤ u (a+t) + t E`;
--   * `Cert2`: the certificates up to `t² E` of `Analysis/ExpRate`, given the Lipschitz bounds of `h` and `k` at every
--     width (`alg1`, `alg2` are the algebra of one halving step: the errors add up to `4 (½t)² E = t² E`).
module QBS.Analysis.ExpRateExt where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)

module AlgExt (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; half+half; hp)
  open AlgT A R using (hp≤1)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  -- ½ t + ½ t = t
  hh2 : ∀ t → half * t + half * t ≈ t
  hh2 t = trans (sym (distribʳ t half half)) (trans (*-cong half+half refl) (*-identityˡ t))

  -- (x + x) E = t E for x = ½ t
  hh2E : ∀ t E → (half * t) * E + (half * t) * E ≈ t * E
  hh2E t E = trans (sym (distribʳ E (half * t) (half * t))) (*-cong (hh2 t) refl)

  -- `a + (w + w) = (a + w) + w`
  at-eq : ∀ a w → a + (w + w) ≈ (a + w) + w
  at-eq a w = sym (+-assoc a w w)

  -- halving the piece `[a, a + t]` at the level k: both halves are pieces of width ≤ ½ᵏ⁺¹ inside the domain `a + t ≤ Mo`
  halve : ∀ {Mo a t} k → a + t ≤ Mo → t ≤ hp k →
    ((a + half * t) ≤ Mo) × (((a + half * t) + half * t ≤ Mo) × (half * t ≤ hp (suc k)))
  halve {Mo} {a} {t} k at tk = a1 , a2 , *-mono half tk
    where
    hw≤t : half * t ≤ t
    hw≤t = ≤-trans (≤-+ʳ {half * t} {half * t}) (≤-reflexive (hh2 t))
    a1 : a + half * t ≤ Mo
    a1 = ≤-trans (+-mono (≤-refl {a}) hw≤t) at
    a2 : (a + half * t) + half * t ≤ Mo
    a2 = ≤-trans (≤-reflexive (trans (+-assoc a (half * t) (half * t)) (+-cong refl (hh2 t)))) at

  hw≤1 : ∀ {t} k → t ≤ hp k → half * t ≤ 1#
  hw≤1 {t} k tk = ≤-trans (≤-trans (*-mono half tk) (≤-reflexive (refl {half * hp k}))) (hp≤1 (suc k))

  ----------------------------------------------------------------------------
  -- the plain certificate

  module Plain (Mo : ∣A∣) (h G : ∣A∣ → ∣A∣) (h-anti : ∀ {x y} → x ≤ y → h y ≤ h x)
    (h-cong : ∀ {x y} → x ≈ y → h x ≈ h y) (G-cong : ∀ {x y} → x ≈ y → G x ≈ G y) where

    Cert : ∣A∣ → ∣A∣ → Set₁
    Cert a t = (G (a + t) + t * h (a + t) ≤ G a) × (G a ≤ G (a + t) + t * h a)

    Cert-cong : ∀ {a t t′} → t ≈ t′ → Cert a t → Cert a t′
    Cert-cong {a} e (lo , hi) =
      ≤-resp (+-cong (G-cong (+-cong refl e)) (*-cong e (h-cong (+-cong refl e)))) refl lo ,
      ≤-resp refl (+-cong (G-cong (+-cong refl e)) (*-cong e refl)) hi

    -- two adjacent pieces of width w make one of width w + w
    Cert-add : ∀ {a w} → Cert a w → Cert (a + w) w → Cert a (w + w)
    Cert-add {a} {w} (lo1 , hi1) (lo2 , hi2) = lo , hi
      where
      eb : a + (w + w) ≈ (a + w) + w
      eb = at-eq a w
      ee : ∀ g y → g + (w + w) * y ≈ (g + w * y) + w * y
      ee g y = solve 3 (λ g′ w′ y′ → g′ :+ (w′ :+ w′) :* y′ := (g′ :+ w′ :* y′) :+ w′ :* y′) refl g w y
      hb : h ((a + w) + w) ≤ h (a + w)
      hb = h-anti (≤-+ʳ {a + w} {w})
      hm : h (a + w) ≤ h a
      hm = h-anti (≤-+ʳ {a} {w})
      lo : G (a + (w + w)) + (w + w) * h (a + (w + w)) ≤ G a
      lo = ≤-trans (≤-reflexive (trans (+-cong (G-cong eb) (*-cong refl (h-cong eb))) (ee (G ((a + w) + w)) (h ((a + w) + w)))))
        (≤-trans (+-mono (≤-refl {G ((a + w) + w) + w * h ((a + w) + w)}) (*-mono w hb))
        (≤-trans (+-mono lo2 (≤-refl {w * h (a + w)})) lo1))
      hi : G a ≤ G (a + (w + w)) + (w + w) * h a
      hi = ≤-trans hi1 (≤-trans (+-mono (≤-trans hi2 (+-mono (≤-refl {G ((a + w) + w)}) (*-mono w hm))) (≤-refl {w * h a}))
        (≤-reflexive (sym (trans (+-cong (G-cong eb) refl) (ee (G ((a + w) + w)) (h a))))))

    Q : ℕ → Set₁
    Q k = ∀ {a t} → a + t ≤ Mo → t ≤ hp k → Cert a t

    down : ∀ k → Q (suc k) → Q k
    down k q {a} {t} at tk = Cert-cong (hh2 t) (Cert-add (q (proj₁ hv) (proj₂ (proj₂ hv))) (q (proj₁ (proj₂ hv)) (proj₂ (proj₂ hv))))
      where
      hv = halve {Mo} {a} {t} k at tk

    -- all widths from the widths ≤ ½ᴷ
    ext : ∀ K → Q K → ∀ {a t} → a + t ≤ Mo → t ≤ 1# → Cert a t
    ext zero q = q
    ext (suc K) q = ext K (down K q)

  ----------------------------------------------------------------------------
  -- Lipschitz bounds

  module Lip (Mo : ∣A∣) (u : ∣A∣ → ∣A∣) (E : ∣A∣) (u-cong : ∀ {x y} → x ≈ y → u x ≈ u y) where

    UpQ DnQ : ℕ → Set₁
    UpQ k = ∀ {a t} → a + t ≤ Mo → t ≤ hp k → u (a + t) ≤ u a + t * E
    DnQ k = ∀ {a t} → a + t ≤ Mo → t ≤ hp k → u a ≤ u (a + t) + t * E

    ae : ∀ a t → a + t ≈ (a + half * t) + half * t
    ae a t = trans (+-cong refl (sym (hh2 t))) (sym (+-assoc a (half * t) (half * t)))

    up-down : ∀ k → UpQ (suc k) → UpQ k
    up-down k q {a} {t} at tk = ≤-trans (≤-reflexive (u-cong (ae a t)))
      (≤-trans (q (proj₁ (proj₂ hv)) (proj₂ (proj₂ hv)))
      (≤-trans (+-mono (q (proj₁ hv) (proj₂ (proj₂ hv))) (≤-refl {(half * t) * E}))
        (≤-reflexive (trans (+-assoc (u a) ((half * t) * E) ((half * t) * E)) (+-cong refl (hh2E t E))))))
      where
      hv = halve {Mo} {a} {t} k at tk

    dn-down : ∀ k → DnQ (suc k) → DnQ k
    dn-down k q {a} {t} at tk = ≤-trans (q (proj₁ hv) (proj₂ (proj₂ hv)))
      (≤-trans (+-mono (q (proj₁ (proj₂ hv)) (proj₂ (proj₂ hv))) (≤-refl {(half * t) * E}))
        (≤-reflexive (trans (+-assoc (u ((a + half * t) + half * t)) ((half * t) * E) ((half * t) * E))
          (+-cong (u-cong (sym (ae a t))) (hh2E t E)))))
      where
      hv = halve {Mo} {a} {t} k at tk

    up-ext : ∀ K → UpQ K → ∀ {a t} → a + t ≤ Mo → t ≤ 1# → u (a + t) ≤ u a + t * E
    up-ext zero q = q
    up-ext (suc K) q = up-ext K (up-down K q)

    dn-ext : ∀ K → DnQ K → ∀ {a t} → a + t ≤ Mo → t ≤ 1# → u a ≤ u (a + t) + t * E
    dn-ext zero q = q
    dn-ext (suc K) q = dn-ext K (dn-down K q)

  ----------------------------------------------------------------------------
  -- the certificates up to the error `t² E`: the algebra of one halving step

  module Alg1 (Gb Gm Ga ha hm ka km w E : ∣A∣)
    (c1m : Gb + w * hm ≤ (Gm + w * km) + (w * w) * E) (c1a : Gm + w * ha ≤ (Ga + w * ka) + (w * w) * E)
    (hD : ha ≤ hm + w * E) (kU : km ≤ ka + w * E) where
    e0 : Gb + (w + w) * ha ≈ (Gb + w * ha) + w * ha
    e0 = solve 3 (λ g w′ y → g :+ (w′ :+ w′) :* y := (g :+ w′ :* y) :+ w′ :* y) refl Gb w ha
    s1 : (Gb + w * ha) + w * ha ≤ (Gb + w * (hm + w * E)) + w * ha
    s1 = +-mono (+-mono (≤-refl {Gb}) (*-mono w hD)) (≤-refl {w * ha})
    e1 : (Gb + w * (hm + w * E)) + w * ha ≈ (Gb + w * hm) + (w * ha + (w * w) * E)
    e1 = solve 5 (λ g w′ m y e → (g :+ w′ :* (m :+ w′ :* e)) :+ w′ :* y
        := (g :+ w′ :* m) :+ (w′ :* y :+ (w′ :* w′) :* e)) refl Gb w hm ha E
    s2 : (Gb + w * hm) + (w * ha + (w * w) * E) ≤ ((Gm + w * km) + (w * w) * E) + (w * ha + (w * w) * E)
    s2 = +-mono c1m (≤-refl {w * ha + (w * w) * E})
    e2 : ((Gm + w * km) + (w * w) * E) + (w * ha + (w * w) * E) ≈ (Gm + w * ha) + (w * km + ((w * w) * E + (w * w) * E))
    e2 = solve 5 (λ g w′ k y e → ((g :+ w′ :* k) :+ (w′ :* w′) :* e) :+ (w′ :* y :+ (w′ :* w′) :* e)
        := (g :+ w′ :* y) :+ (w′ :* k :+ ((w′ :* w′) :* e :+ (w′ :* w′) :* e))) refl Gm w km ha E
    s3 : (Gm + w * ha) + (w * km + ((w * w) * E + (w * w) * E))
      ≤ ((Ga + w * ka) + (w * w) * E) + (w * (ka + w * E) + ((w * w) * E + (w * w) * E))
    s3 = +-mono c1a (+-mono (*-mono w kU) (≤-refl {(w * w) * E + (w * w) * E}))
    e3 : ((Ga + w * ka) + (w * w) * E) + (w * (ka + w * E) + ((w * w) * E + (w * w) * E))
      ≈ (Ga + (w + w) * ka) + ((w + w) * (w + w)) * E
    e3 = solve 4 (λ g w′ k e → ((g :+ w′ :* k) :+ (w′ :* w′) :* e) :+ (w′ :* (k :+ w′ :* e) :+ ((w′ :* w′) :* e :+ (w′ :* w′) :* e))
        := (g :+ (w′ :+ w′) :* k) :+ ((w′ :+ w′) :* (w′ :+ w′)) :* e) refl Ga w ka E

    result : Gb + (w + w) * ha ≤ (Ga + (w + w) * ka) + ((w + w) * (w + w)) * E
    result = ≤-trans (≤-reflexive e0) (≤-trans s1 (≤-trans (≤-reflexive e1) (≤-trans s2 (≤-trans (≤-reflexive e2)
      (≤-trans s3 (≤-reflexive e3))))))

  alg1 : ∀ Gb Gm Ga ha hm ka km w E →
    Gb + w * hm ≤ (Gm + w * km) + (w * w) * E → Gm + w * ha ≤ (Ga + w * ka) + (w * w) * E →
    ha ≤ hm + w * E → km ≤ ka + w * E →
    Gb + (w + w) * ha ≤ (Ga + (w + w) * ka) + ((w + w) * (w + w)) * E
  alg1 Gb Gm Ga ha hm ka km w E c1m c1a hD kU = Alg1.result Gb Gm Ga ha hm ka km w E c1m c1a hD kU

  module Alg2 (Gb Gm Ga ha hm ka km w E : ∣A∣)
    (c2a : Ga + w * ka ≤ (Gm + w * ha) + (w * w) * E) (c2m : Gm + w * km ≤ (Gb + w * hm) + (w * w) * E)
    (kD : ka ≤ km + w * E) (hU : hm ≤ ha + w * E) where
    e0 : Ga + (w + w) * ka ≈ (Ga + w * ka) + w * ka
    e0 = solve 3 (λ g w′ y → g :+ (w′ :+ w′) :* y := (g :+ w′ :* y) :+ w′ :* y) refl Ga w ka
    s1 : (Ga + w * ka) + w * ka ≤ (Ga + w * ka) + w * (km + w * E)
    s1 = +-mono (≤-refl {Ga + w * ka}) (*-mono w kD)
    e1 : (Ga + w * ka) + w * (km + w * E) ≈ (Ga + w * ka) + (w * km + (w * w) * E)
    e1 = solve 5 (λ g w′ k m e → (g :+ w′ :* k) :+ w′ :* (m :+ w′ :* e)
        := (g :+ w′ :* k) :+ (w′ :* m :+ (w′ :* w′) :* e)) refl Ga w ka km E
    s2 : (Ga + w * ka) + (w * km + (w * w) * E) ≤ ((Gm + w * ha) + (w * w) * E) + (w * km + (w * w) * E)
    s2 = +-mono c2a (≤-refl {w * km + (w * w) * E})
    e2 : ((Gm + w * ha) + (w * w) * E) + (w * km + (w * w) * E) ≈ (Gm + w * km) + (w * ha + ((w * w) * E + (w * w) * E))
    e2 = solve 5 (λ g w′ k y e → ((g :+ w′ :* y) :+ (w′ :* w′) :* e) :+ (w′ :* k :+ (w′ :* w′) :* e)
        := (g :+ w′ :* k) :+ (w′ :* y :+ ((w′ :* w′) :* e :+ (w′ :* w′) :* e))) refl Gm w km ha E
    s3 : (Gm + w * km) + (w * ha + ((w * w) * E + (w * w) * E))
      ≤ ((Gb + w * hm) + (w * w) * E) + (w * ha + ((w * w) * E + (w * w) * E))
    s3 = +-mono c2m (≤-refl {w * ha + ((w * w) * E + (w * w) * E)})
    e3 : ((Gb + w * hm) + (w * w) * E) + (w * ha + ((w * w) * E + (w * w) * E))
      ≈ (Gb + w * hm) + (w * ha + ((w * w) * E + ((w * w) * E + (w * w) * E)))
    e3 = solve 5 (λ g w′ m y e → ((g :+ w′ :* m) :+ (w′ :* w′) :* e) :+ (w′ :* y :+ ((w′ :* w′) :* e :+ (w′ :* w′) :* e))
        := (g :+ w′ :* m) :+ (w′ :* y :+ ((w′ :* w′) :* e :+ ((w′ :* w′) :* e :+ (w′ :* w′) :* e)))) refl Gb w hm ha E
    s4 : (Gb + w * hm) + (w * ha + ((w * w) * E + ((w * w) * E + (w * w) * E)))
      ≤ (Gb + w * (ha + w * E)) + (w * ha + ((w * w) * E + ((w * w) * E + (w * w) * E)))
    s4 = +-mono (+-mono (≤-refl {Gb}) (*-mono w hU)) (≤-refl {w * ha + ((w * w) * E + ((w * w) * E + (w * w) * E))})
    e4 : (Gb + w * (ha + w * E)) + (w * ha + ((w * w) * E + ((w * w) * E + (w * w) * E)))
      ≈ (Gb + (w + w) * ha) + ((w + w) * (w + w)) * E
    e4 = solve 4 (λ g w′ y e → (g :+ w′ :* (y :+ w′ :* e)) :+ (w′ :* y :+ ((w′ :* w′) :* e :+ ((w′ :* w′) :* e :+ (w′ :* w′) :* e)))
        := (g :+ (w′ :+ w′) :* y) :+ ((w′ :+ w′) :* (w′ :+ w′)) :* e) refl Gb w ha E

    result : Ga + (w + w) * ka ≤ (Gb + (w + w) * ha) + ((w + w) * (w + w)) * E
    result = ≤-trans (≤-reflexive e0) (≤-trans s1 (≤-trans (≤-reflexive e1) (≤-trans s2 (≤-trans (≤-reflexive e2)
      (≤-trans s3 (≤-trans (≤-reflexive e3) (≤-trans s4 (≤-reflexive e4))))))))

  alg2 : ∀ Gb Gm Ga ha hm ka km w E →
    Ga + w * ka ≤ (Gm + w * ha) + (w * w) * E → Gm + w * km ≤ (Gb + w * hm) + (w * w) * E →
    ka ≤ km + w * E → hm ≤ ha + w * E →
    Ga + (w + w) * ka ≤ (Gb + (w + w) * ha) + ((w + w) * (w + w)) * E
  alg2 Gb Gm Ga ha hm ka km w E c2a c2m kD hU = Alg2.result Gb Gm Ga ha hm ka km w E c2a c2m kD hU

  ----------------------------------------------------------------------------
  -- the certificates for all widths

  module Cert2 (Mo : ∣A∣) (h k G : ∣A∣ → ∣A∣) (E : ∣A∣)
    (G-cong : ∀ {x y} → x ≈ y → G x ≈ G y)
    (hU : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → h (a + t) ≤ h a + t * E)
    (hD : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → h a ≤ h (a + t) + t * E)
    (kU : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → k (a + t) ≤ k a + t * E)
    (kD : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → k a ≤ k (a + t) + t * E) where

    C1 C2 : ∣A∣ → ∣A∣ → Set₁
    C1 a t = G (a + t) + t * h a ≤ (G a + t * k a) + (t * t) * E
    C2 a t = G a + t * k a ≤ (G (a + t) + t * h a) + (t * t) * E

    ee : ∀ t t′ → t ≈ t′ → (t * t) * E ≈ (t′ * t′) * E
    ee t t′ e = *-cong (*-cong e e) refl

    C1-cong : ∀ {a t t′} → t ≈ t′ → C1 a t → C1 a t′
    C1-cong {a} {t} {t′} e = ≤-resp (+-cong (G-cong (+-cong refl e)) (*-cong e refl))
      (+-cong (+-cong refl (*-cong e refl)) (ee t t′ e))

    C2-cong : ∀ {a t t′} → t ≈ t′ → C2 a t → C2 a t′
    C2-cong {a} {t} {t′} e = ≤-resp (+-cong refl (*-cong e refl))
      (+-cong (+-cong (G-cong (+-cong refl e)) (*-cong e refl)) (ee t t′ e))

    C1-add : ∀ {a w} → C1 a w → C1 (a + w) w → h a ≤ h (a + w) + w * E → k (a + w) ≤ k a + w * E → C1 a (w + w)
    C1-add {a} {w} c1a c1m hd ku = ≤-resp (+-cong (G-cong (sym (at-eq a w))) refl) refl
      (alg1 (G ((a + w) + w)) (G (a + w)) (G a) (h a) (h (a + w)) (k a) (k (a + w)) w E c1m c1a hd ku)

    C2-add : ∀ {a w} → C2 a w → C2 (a + w) w → k a ≤ k (a + w) + w * E → h (a + w) ≤ h a + w * E → C2 a (w + w)
    C2-add {a} {w} c2a c2m kd hu = ≤-resp refl (+-cong (+-cong (G-cong (sym (at-eq a w))) refl) refl)
      (alg2 (G ((a + w) + w)) (G (a + w)) (G a) (h a) (h (a + w)) (k a) (k (a + w)) w E c2a c2m kd hu)

    Q1 Q2 : ℕ → Set₁
    Q1 n = ∀ {a t} → a + t ≤ Mo → t ≤ hp n → C1 a t
    Q2 n = ∀ {a t} → a + t ≤ Mo → t ≤ hp n → C2 a t

    down1 : ∀ n → Q1 (suc n) → Q1 n
    down1 n q {a} {t} at tn = C1-cong (hh2 t) (C1-add (q (proj₁ hv) (proj₂ (proj₂ hv))) (q (proj₁ (proj₂ hv)) (proj₂ (proj₂ hv)))
      (hD (proj₁ hv) (hw≤1 n tn)) (kU (proj₁ hv) (hw≤1 n tn)))
      where
      hv = halve {Mo} {a} {t} n at tn

    down2 : ∀ n → Q2 (suc n) → Q2 n
    down2 n q {a} {t} at tn = C2-cong (hh2 t) (C2-add (q (proj₁ hv) (proj₂ (proj₂ hv))) (q (proj₁ (proj₂ hv)) (proj₂ (proj₂ hv)))
      (kD (proj₁ hv) (hw≤1 n tn)) (hU (proj₁ hv) (hw≤1 n tn)))
      where
      hv = halve {Mo} {a} {t} n at tn

    ext1 : ∀ K → Q1 K → ∀ {a t} → a + t ≤ Mo → t ≤ 1# → C1 a t
    ext1 zero q = q
    ext1 (suc K) q = ext1 K (down1 K q)

    ext2 : ∀ K → Q2 K → ∀ {a t} → a + t ≤ Mo → t ≤ 1# → C2 a t
    ext2 zero q = q
    ext2 (suc K) q = ext2 K (down2 K q)
