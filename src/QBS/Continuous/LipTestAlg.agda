{-# OPTIONS --safe --without-K #-}

-- Helper for `LipTest`: arithmetic of the tolerances ½ⁿ against a bounded Lipschitz constant, and the difference of cuts.
--   * `hp-le1`, `hp-add`, `hp-nat`, `two-small`: ½ⁿ ≤ 1, ½ʲ⁺ᵏ = ½ʲ ½ᵏ, ½ᵏ k ≤ 1, and 2 ½ⁿ⁺¹ c ≤ ½ʲ for c ≤ k;
--   * `sub-le`: for a ≤ x ≤ a + ε with a bounded there is w ≤ ε with a + w = x (`LebesgueShiftCut.diffC`);
--   * `Cell`: for x ∈ [a, a + ½ⁿ) below N + 1, F x and F a differ by ½ⁿ c; `nec`/`suf`: Q ≤ F x iff for every n the cell
--     of x has Q ≤ F a + ½ⁿ c (`suf` by `arch`);
--   * `Fam`/`Probe`: Q ≤ F x iff x = ∞ with Q ≤ F ∞, or x ≤ N + 1 and the cell condition; a countable union/intersection
--     of Borel sets along a measurable probe, and q ∈ F x iff (−∞, ρ) ≤ F x for some ρ > q (`Meas-lip′`).
module QBS.Continuous.LipTestAlg where

open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Level using (lift)
open import Function.Base using (case_of_)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Rational.Unnormalised.Base using (ℚᵘ; _<_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerReals using (mk⊑; _⊑_; infC; module Cut)
open Cut using (mem; down; open′; neg)
open import QBS.Analysis.RationalLemmas using (<-≤)
open import QBS.Analysis.MeasFun using (ratC)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Borel.Core using (Borel; compl; inter₂; union₂; resp; ⋃; ⋂; ⊤-borel)
open import QBS.Borel.Source using (R₁)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Continuous.LebesgueShiftCut using (module LebesgueShiftCut)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.DigitCut using (module DigitCut)
open import QBS.Continuous.DigitStream using (module DigitStream)
open import QBS.Continuous.LebesgueScaleAlg using (module LebesgueScaleAlg)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)
open import QBS.Continuous.ChangeOfVariablesAlg using (module ChangeOfVariablesAlg)

module LipAlg (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive; +-mono;
    *-mono; ≤-+ʳ; 0-least; +-comm; distribˡ; distribʳ; *-identityˡ; *-identityʳ; *-comm; *-assoc;
    +-assoc; zeroʳ) renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Bounded A using (Bnd)
  open Arch R using (half; hp; hp-zero; hp-≤; hp-double; arch) renaming (half+half to hh)
  open LebesgueShiftCut (lemOf lem₁) using (diffC; diff-sum; diff-⇐)
  open LebesgueShiftAlg (lemOf lem₁) using (bnd-rat)
  open AlgDigit A half hh using (dy-succ)
  open Intervals (lemOf lem₁) using (Ge; dy)
  open DigitCut (lemOf lem₁) using (below-dec)
  open DigitStream (lemOf lem₁) using (Tgt)
  open LebesgueScaleAlg (lemOf lem₁) using (ge⇒≤; ≤⇒ge)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat)
  open LebesgueIntervalAlg (lemOf lem₁) using (tgt-ex)
  open ChangeOfVariablesAlg lem₁ using (inf-bnd)
  open DigitCut (lemOf lem₁) using (nat-big)
  open Intervals (lemOf lem₁) using (InInf; ge-borel)
  open Meas (lemOf lem₁) using (Meas; all-enum; ex-enum)
  open LevelSets (lemOf lem₁) using (borel-prop)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE-mono)
  open AlgT A R using (P)
  open AlgP A R using (pnat; natE-pnat)

  ----------------------------------------------------------------------------
  -- tolerances

  hp-le1 : ∀ n → hp n ≤ 1#
  hp-le1 zero = ≤-reflexive hp-zero
  hp-le1 (suc n) = ≤-trans (hp-≤ n) (hp-le1 n)

  hp-half : ∀ n → hp (suc n) ≤ half
  hp-half n = ≤-trans (*-mono half (hp-le1 n)) (≤-reflexive (*-identityʳ half))

  hp-add : ∀ j k → hp (j ℕ.+ k) ≈ hp j * hp k
  hp-add zero k = trans (sym (*-identityˡ (hp k))) (*-cong (sym hp-zero) refl)
  hp-add (suc j) k = trans (*-cong refl (hp-add j k)) (sym (*-assoc half (hp j) (hp k)))

  hp-nat : ∀ k → hp k * natE k ≤ 1#
  hp-nat zero = ≤-trans (≤-reflexive (zeroʳ _)) 0-least
  hp-nat (suc k) = ≤-trans (≤-reflexive (distribˡ (hp (suc k)) (natE k) 1#))
    (≤-trans (+-mono (≤-trans (≤-reflexive (*-assoc half (hp k) (natE k))) (≤-trans (*-mono half (hp-nat k))
      (≤-reflexive (*-identityʳ half)))) (≤-trans (≤-reflexive (*-identityʳ _)) (hp-half k))) (≤-reflexive hh))

  -- ½ʲ⁺ᵏ c ≤ ½ʲ for c ≤ k
  hp-small : ∀ {c k} → c ≤ natE k → ∀ j → hp (j ℕ.+ k) * c ≤ hp j
  hp-small {c} {k} ck j = ≤-trans (≤-reflexive (trans (*-cong (hp-add j k) refl) (*-assoc (hp j) (hp k) c)))
    (≤-trans (*-mono (hp j) (≤-trans (*-mono (hp k) ck) (hp-nat k))) (≤-reflexive (*-identityʳ (hp j))))

  two-small : ∀ {c k} → c ≤ natE k → ∀ j → hp (suc (j ℕ.+ k)) * c + hp (suc (j ℕ.+ k)) * c ≤ hp j
  two-small {c} ck j = ≤-trans (≤-reflexive (trans (sym (distribʳ c _ _)) (*-cong (hp-double _) refl))) (hp-small ck j)

  ----------------------------------------------------------------------------
  -- the difference of cuts

  sub-le : ∀ a x ε → a ≤ x → x ≤ a + ε → Bnd a → Σ ∣A∣ (λ w → (a + w ≈ x) × (w ≤ ε))
  sub-le a x ε ax xe ba = diffC a x ax , diff-sum a x ax (proj₁ M) (proj₂ M)
    , diff-⇐ a x ax (proj₁ M) (proj₂ M) ε (≤-trans xe (≤-reflexive (+-comm a ε)))
    where M = bnd-rat a ba

  -- finiteness certificates (`Deriv`) give bounds by naturals
  fin-bnd : ∀ {x} → Σ ℕ (λ S → x ≤ P S) → Bnd x
  fin-bnd (S , h) = pnat S , ≤-trans h (≤-trans (≤-reflexive (sym (natE-pnat S))) (≤-reflexive (natE≈nat _)))

  ----------------------------------------------------------------------------
  -- one dyadic cell: F x and F a differ by at most ½ⁿ c, for x ∈ [a, a + ½ⁿ)

  le-bnd : ∀ {a x N} → a ≤ x → x ≤ natE (suc N) → Bnd a
  le-bnd {N = N} ax xN = suc N , ≤-trans ax (≤-trans xN (≤-reflexive (natE≈nat (suc N))))

  mono-ʳ : ∀ {w e} c → w ≤ e → w * c ≤ e * c
  mono-ʳ {w} {e} c we = ≤-trans (≤-reflexive (*-comm w c)) (≤-trans (*-mono c we) (≤-reflexive (*-comm c e)))

  module Cell (F : ∣A∣ → ∣A∣) (cF : ∀ {x y} → x ≈ y → F x ≈ F y) (N : ℕ) (c : ∣A∣)
    (U : ∀ a w → a + w ≤ natE (suc N) → w ≤ 1# → F (a + w) ≤ F a + w * c)
    (D : ∀ a w → a + w ≤ natE (suc N) → w ≤ 1# → F a ≤ F (a + w) + w * c) where

    -- the difference w = x − a
    cellw : ∀ {n m x} → Tgt n m x → x ≤ natE (suc N) → Σ ∣A∣ (λ w → (dy n m + w ≈ x) × (w ≤ hp n))
    cellw {n} {m} {x} (g , ng) xN = sub-le (dy n m) x (hp n) (ge⇒≤ _ x g)
      (≤-trans (below-dec m n x ng) (≤-reflexive (dy-succ m n))) (le-bnd (ge⇒≤ _ x g) xN)

    cell↑′ : ∀ {n x w} {a} → a + w ≈ x → w ≤ hp n → x ≤ natE (suc N) → F x ≤ F a + hp n * c
    cell↑′ {n} {w = w} {a} e we xN = ≤-trans (≤-reflexive (cF (sym e)))
      (≤-trans (U a w (≤-trans (≤-reflexive e) xN) (≤-trans we (hp-le1 n))) (+-mono (≤-reflexive refl) (mono-ʳ c we)))

    cell↓′ : ∀ {n x w} {a} → a + w ≈ x → w ≤ hp n → x ≤ natE (suc N) → F a ≤ F x + hp n * c
    cell↓′ {n} {w = w} {a} e we xN = ≤-trans (D a w (≤-trans (≤-reflexive e) xN) (≤-trans we (hp-le1 n)))
      (+-mono (≤-reflexive (cF e)) (mono-ʳ c we))

    cell↑ : ∀ {n m x} → Tgt n m x → x ≤ natE (suc N) → F x ≤ F (dy n m) + hp n * c
    cell↑ t xN = cell↑′ (proj₁ (proj₂ (cellw t xN))) (proj₂ (proj₂ (cellw t xN))) xN

    cell↓ : ∀ {n m x} → Tgt n m x → x ≤ natE (suc N) → F (dy n m) ≤ F x + hp n * c
    cell↓ t xN = cell↓′ (proj₁ (proj₂ (cellw t xN))) (proj₂ (proj₂ (cellw t xN))) xN

    -- the pointwise characterisation of `Q ≤ F x` by the cells, for x ≤ N + 1
    Kc : ∣A∣ → ℕ → ℕ → Set
    Kc Q n m = Ge Q (F (dy n m) + hp n * c)

    nec : ∀ Q x → Ge Q (F x) → x ≤ natE (suc N) → ∀ n → Σ ℕ (λ m → Tgt n m x × Kc Q n m)
    nec Q x g xN n = proj₁ (tgt-ex x bx n) , proj₂ (tgt-ex x bx n)
      , ≤⇒ge Q _ (≤-trans (ge⇒≤ Q (F x) g) (cell↑ (proj₂ (tgt-ex x bx n)) xN))
      where bx = suc N , ≤-trans xN (≤-reflexive (natE≈nat (suc N)))

    suf-j : ∀ {Q x k n m} → Tgt n m x → x ≤ natE (suc N) → Kc Q n m → hp n * c + hp n * c ≤ hp k →
      Q ≤ F x + hp k
    suf-j t xN kc le = ≤-trans (ge⇒≤ _ _ kc) (≤-trans (+-mono (cell↓ t xN) (≤-reflexive refl))
      (≤-trans (≤-reflexive (+-assoc _ _ _)) (+-mono (≤-reflexive refl) le)))

    suf : ∀ {kc} → c ≤ natE kc → ∀ Q x → x ≤ natE (suc N) →
      (∀ n → Σ ℕ (λ m → Tgt n m x × Kc Q n m)) → Ge Q (F x)
    suf {kc} ck Q x xN f = ≤⇒ge Q (F x) (arch (λ j → suf-j (proj₁ (proj₂ (f (suc (j ℕ.+ kc))))) xN
      (proj₂ (proj₂ (f (suc (j ℕ.+ kc))))) (two-small ck j)))

  ----------------------------------------------------------------------------
  -- infinite points, and the threshold sets along a measurable probe

  inf-≈ : ∀ {x} → InInf x → x ≈ infC
  inf-≈ {x} f = mk⊑ (λ _ _ → tt) , mk⊑ (λ q _ → let k , mk = nat-big q in f k q mk)

  -- `x ≤ y` for a constant y is Borel along a measurable probe (`Ge x y`, in the other direction from `ge-borel`)
  le-borel : ∀ y {h : R₁ → ∣A∣} → Meas h → Borel (λ c → Ge (h (lift c)) y)
  le-borel y {h} m = all-enum (λ ρ c → mem (h (lift c)) ρ → mem y ρ) bimp
    where
      bimp : ∀ ρ → Borel (λ c → mem (h (lift c)) ρ → mem y ρ)
      bimp ρ = case lemOf lem₁ (mem y ρ) of λ
        { (inj₁ e) → resp (λ c → (λ _ _ → e) , (λ _ → tt)) ⊤-borel
        ; (inj₂ ne) → resp (λ c → (λ n mm → ⊥-elim (n mm)) , (λ f mm → ne (f mm))) (compl (m ρ)) }

  ----------------------------------------------------------------------------
  -- the whole family of cells, for a locally Lipschitz F

  LL : (∣A∣ → ∣A∣) → Set₁
  LL F = ∀ N → Σ ∣A∣ λ c → Bnd c
    × (∀ a w → a + w ≤ natE (suc N) → w ≤ 1# → F (a + w) ≤ F a + w * c)
    × (∀ a w → a + w ≤ natE (suc N) → w ≤ 1# → F a ≤ F (a + w) + w * c)

  module Fam (F : ∣A∣ → ∣A∣) (cF : ∀ {x y} → x ≈ y → F x ≈ F y) (lF : LL F) where
    cN : ℕ → ∣A∣
    cN N = proj₁ (lF N)

    ckN : ∀ N → cN N ≤ natE (proj₁ (proj₁ (proj₂ (lF N))))
    ckN N = ≤-trans (proj₂ (proj₁ (proj₂ (lF N)))) (≤-reflexive (sym (natE≈nat _)))

    module CN N = Cell F cF N (cN N) (proj₁ (proj₂ (proj₂ (lF N)))) (proj₂ (proj₂ (proj₂ (lF N))))

    -- the points of the threshold set, as a union over N of cell conditions, plus the point ∞
    Fin′ : ∣A∣ → ℕ → ∣A∣ → Set
    Fin′ Q N x = Ge x (natE (suc N)) × (∀ n → Σ ℕ (λ m → Tgt n m x × CN.Kc N Q n m))

    VV : ∣A∣ → ∣A∣ → Set
    VV Q x = (InInf x × Ge Q (F infC)) ⊎ Σ ℕ (λ N → Fin′ Q N x)

    -- a finite point is bounded by some N + 1
    fin-N : ∀ {x} → (InInf x → ⊥) → Σ ℕ (λ N → x ≤ natE (suc N))
    fin-N {x} ni = proj₁ (inf-bnd x ni) ,
      ≤-trans (proj₂ (inf-bnd x ni)) (≤-trans (≤-reflexive (sym (natE≈nat _))) (natE-mono (ℕ.n≤1+n _)))

    fwd-fin : ∀ Q x → Ge Q (F x) → ∀ {N} → x ≤ natE (suc N) → Fin′ Q N x
    fwd-fin Q x g xN = ≤⇒ge x _ xN , CN.nec _ Q x g xN

    fwd : ∀ Q x → Ge Q (F x) → VV Q x
    fwd Q x g = case lemOf lem₁ (InInf x) of λ
      { (inj₁ i) → inj₁ (i , ≤⇒ge Q _ (≤-trans (ge⇒≤ Q _ g) (≤-reflexive (cF (inf-≈ i)))))
      ; (inj₂ ni) → inj₂ (proj₁ (fin-N ni) , fwd-fin Q x g (proj₂ (fin-N ni))) }

    bwd : ∀ Q x → VV Q x → Ge Q (F x)
    bwd Q x (inj₁ (i , g)) = ≤⇒ge Q _ (≤-trans (ge⇒≤ Q _ g) (≤-reflexive (cF (sym (inf-≈ i)))))
    bwd Q x (inj₂ (N , le , f)) = CN.suf N (ckN N) Q x (ge⇒≤ x _ le) f

    module Probe {α : R₁ → ∣A∣} (m : Meas α) where
      cellB : ∀ n k → Borel (λ c → Tgt n k (α (lift c)))
      cellB n k = inter₂ (ge-borel (dy n k) m) (compl (ge-borel (dy n (suc k)) m))

      finB : ∀ Q N → Borel (λ c → Fin′ Q N (α (lift c)))
      finB Q N = inter₂ (le-borel (natE (suc N)) m)
        (⋂ (λ n → ⋃ (λ k → inter₂ (cellB n k) (borel-prop (CN.Kc N Q n k)))))

      geB : ∀ Q → Borel (λ c → Ge Q (F (α (lift c))))
      geB Q = resp (λ c → bwd Q _ , fwd Q _)
        (union₂ (inter₂ (⋂ (λ k → ge-borel (natE k) m)) (borel-prop (Ge Q (F infC)))) (⋃ (finB Q)))

      -- from the cuts `Q = (−∞, ρ)` to membership
      ge-rat : ∀ (y : ∣A∣) ρ → mem y ρ → Ge (ratC ρ) y
      ge-rat y ρ mρ s (inj₁ s<ρ) = down y (<-≤ s<ρ) mρ
      ge-rat y ρ mρ s (inj₂ s<0) = neg y s<0

      to-rat : ∀ (y : ∣A∣) q → mem y q → Σ ℚᵘ (λ ρ → (q < ρ) × Ge (ratC ρ) y)
      to-rat y q mq = proj₁ (open′ y mq) , proj₁ (proj₂ (open′ y mq)) , ge-rat y _ (proj₂ (proj₂ (open′ y mq)))

      Meas-lip′ : Meas (λ r → F (α r))
      Meas-lip′ q = resp (λ c → (λ (ρ , lt , g) → g q (inj₁ lt))
        , (to-rat (F (α (lift c))) q))
        (ex-enum (λ ρ c → (q < ρ) × Ge (ratC ρ) (F (α (lift c))))
          (λ ρ → inter₂ (borel-prop (q < ρ)) (geB (ratC ρ))))
