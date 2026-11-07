{-# OPTIONS --safe --without-K #-}

-- Downward monotone convergence and Fatou's lemma in both directions, for tests on any X.
-- Main results: `fatou` and `rev-fatou` (the last two definitions of the module; the truncation machinery before them
-- proves `∫ᴹ-inf`).  They are the only primitive convergence statements: `Dominated.dct` and `mct-conv` follow from them.
--   * `∫ᴹ-inf`: for a decreasing sequence h with ∫ h 0 finite, ∫ ⋂ₙ h n ≈ ⋂ₙ ∫ h n;
--   * `fatou`: ∫ lim inf h ≤ lim inf ∫ h;
--   * `rev-fatou`: if every h n ≤ g with ∫ g finite, lim sup ∫ h ≤ ∫ lim sup h.
-- Route for `∫ᴹ-inf`, by truncation (no pointwise finiteness of h 0 is assumed, so h 0 may be ∞ on a null set):
--   1. `∫ᴹ-inf-fin`: the case h 0 ≤ N pointwise.  Pointwise h 0 ≈ h n + (h 0 ∸ h n) (`Monus.monus-add`, h n x ≤ N is
--      bounded); the differences increase, so `SupTest.∫ᴹ-sup` gives ∫ h 0 ≈ ∫ ⋂ h + ⋃ₙ ∫ (h 0 ∸ h n), and
--      ∫ h 0 ≈ ∫ h n + ∫ (h 0 ∸ h n); cancel the finite ∫ h 0 terms (`BoundedCancel.cancel-bnd`).
--   2. `minH N f = f ⊓ N` (`LowerRealsMin._⊓_`); `min-split-⊑` (`LowerRealsNear`): f = (f ⊓ N) + (f ∸ N) pointwise, so ∫ h n ≤
--      ∫ (h n ⊓ N) + ∫ (h 0 ∸ N).
--   3. `tail-small`: ∫ (f ∸ N) gets below every ½ᵏ for finite ∫ f (∫ (f ⊓ N) increases to ∫ f by `∫ᴹ-sup` and
--      `LowerRealsMin.min-sup`; a finite lower real is approached from below, by excluded middle).
--   4. ⋂ ∫ h n ≤ ∫ ⋂ (h ⊓ N) + ½ᵏ ≤ ∫ ⋂ h + ½ᵏ for every k (`approx`), hence ≤ ∫ ⋂ h; the other direction is
--      monotonicity.
-- `fatou`: n ↦ ⋂ₖ h (n + k) increases, so `∫ᴹ-sup`, then ∫ ⋂ₖ h (n + k) ≤ ⋂ₖ ∫ h (n + k) by monotonicity.
-- `rev-fatou`: n ↦ ⋃ₖ h (n + k) decreases and is ≤ g, so `∫ᴹ-inf`, then ⋃ₖ ∫ h (n + k) ≤ ∫ ⋃ₖ h (n + k).
module QBS.Continuous.Fatou where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (n≤1+n) renaming (+-suc to +ℕ-suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst) renaming (sym to ≡sym)
import QBS.Analysis.RationalLemmas as Q

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (Cut; module Cut; unionC; _⊑_; mk⊑; module _⊑_; _≋_; ⊑-refl; ⊑-trans; ⊕-mono; ⊕-union; ⊕-assoc; ⊕-comm⊑; union-ub; union-lub)
open import QBS.Analysis.LowerRealsMin using (_⊓_)
open import QBS.Analysis.LowerRealsInf using (interC; liminfC; limsupC; inter-lb; inter-glb; inter-mono; union-mono)
open import QBS.Analysis.LowerRealsNear using (BndQ; module Near)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LowerRealsArch using (tp; tp-pos; tp-lt; hpC≈)
open import QBS.Continuous.DigitCut using (module DigitCut)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SupTest using (module SupTest)
open import QBS.Continuous.Monus using (module Monus)

open Cut using (mem; open′)
open _⊑_ using (ap)

-- the minimum respects ≋ and lies below both arguments
⊓-cong : ∀ {x x′ y y′} → x ≋ x′ → y ≋ y′ → (x ⊓ y) ≋ (x′ ⊓ y′)
⊓-cong (a , b) (c , d) = mk⊑ (λ q (m₁ , m₂) → ap a q m₁ , ap c q m₂) , mk⊑ (λ q (m₁ , m₂) → ap b q m₁ , ap d q m₂)

⊓-lb : ∀ x y → (x ⊓ y) ⊑ x
⊓-lb x y = mk⊑ (λ q m → proj₁ m)

module Fatou (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; refl; sym; trans; ≤-trans; ≤-reflexive) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half; arch) renaming (half+half to hh)
  open Half A half hh using (hp)
  open BoundedCancel A half hh using (nat-mono)
  open Weights (lemOf lem₁) using (WQ)
  open Meas (lemOf lem₁) using (Meas-⊓; Meas-const)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; module C)
  open SupTest (lemOf lem₁) using (supH; infH; liminfH; limsupH; supH-pt; infH-pt; ∫ᴹ-monoX; ∫ᴹ-sup)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX; monusH)
  open Near (lemOf lem₁) using (near-sup-bnd; cancel-bnd-⊑; inter-add; min-split-⊑)
  open LebesgueShiftAlg (lemOf lem₁) using (bnd-rat; t≤x+t)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat)
  open DigitCut (lemOf lem₁) using (nat-big)
  open Monus lem₁ using (monus; monus-add; monus-anti)
  open QBS
  open Hom

  -- finiteness is downward closed
  Bnd-≤′ : ∀ {a b} → a ≤ b → Bnd b → Bnd a
  Bnd-≤′ le (n , h) = n , ≤-trans le h

  -- the tolerance ½ᵏ is the set of rationals below 2⁻ᵏ
  hp-in : ∀ k s → s Q.<ᵘ tp k → mem (hp k) s
  hp-in k s lt = ap (proj₁ (hpC≈ (lemOf lem₁) k)) s lt

  BndQ-hp : ∀ k → BndQ (hp k)
  BndQ-hp k = tp k , λ r m → ap (proj₂ (hpC≈ (lemOf lem₁) k)) r m

  -- a cut is the union of its truncations
  min-sup′ : ∀ (c : Cut) → c ⊑ unionC (λ n → c ⊓ nat n)
  min-sup′ c = mk⊑ (λ q m → let k , mk = nat-big q in k , (m , ap (proj₁ (natE≈nat k)) q mk))

  sup-min : ∀ (c : Cut) → unionC (λ n → c ⊓ nat n) ≈ c
  sup-min c = union-lub _ (λ n → ⊓-lb c (nat n)) , min-sup′ c

  module _ {X : QBS S} where

    Decr : (ℕ → Hom S X WQ) → Set₁
    Decr h = ∀ n x → map (h (suc n)) ⟨$⟩ x ≤ map (h n) ⟨$⟩ x

    -- x ↦ f x ⊓ N
    minH : ℕ → Hom S X WQ → Hom S X WQ
    minH N f = record
      { map = record { to = λ x → (map f ⟨$⟩ x) ⊓ nat N ; cong = λ e → ⊓-cong (Func.cong (map f) e) refl }
      ; map-random = λ {γ} m → Meas-⊓ {λ r → map f ⟨$⟩ (γ ⟨$⟩ r)} {λ _ → nat N}
          (map-random f {γ} m) (Meas-const (nat N)) }

    minH-pt : ∀ N f x → map (minH N f) ⟨$⟩ x ≈ (map f ⟨$⟩ x) ⊓ nat N
    minH-pt N f x = refl

    -- a ≤ b + ½ᵏ for every k gives a ≤ b
    approx : ∀ {a b} → (∀ k → a ≤ b + hp k) → a ≤ b
    approx = arch

    -- the truncations increase to f
    minH-inc : ∀ (f : Hom S X WQ) n x → map (minH n f) ⟨$⟩ x ≤ map (minH (suc n) f) ⟨$⟩ x
    minH-inc f n x = mk⊑ (λ q (m₁ , m₂) → m₁ , ap (nat-mono (n≤1+n n)) q m₂)

    supMin : ∀ (f : Hom S X WQ) x → map (supH (λ n → minH n f)) ⟨$⟩ x ≈ map f ⟨$⟩ x
    supMin f x = trans (supH-pt (λ n → minH n f) x) (sup-min (map f ⟨$⟩ x))

    decr-le : ∀ (h : ℕ → Hom S X WQ) → Decr h → ∀ n x → map (h n) ⟨$⟩ x ≤ map (h 0) ⟨$⟩ x
    decr-le h d zero x = ⊑-refl
    decr-le h d (suc n) x = ≤-trans (d n x) (decr-le h d n x)

    -- the case h 0 ≤ N: the differences h 0 ∸ h n increase to E, and h 0 ≈ ⋂ h n + E
    module Fin (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) (N : ℕ) (d : Decr h) (b0 : ∀ x → map (h 0) ⟨$⟩ x ≤ nat N)
        (bT : Bnd (∫ᴹ {X} p (h 0))) where
      bnd-pt : ∀ n x → Bnd (map (h n) ⟨$⟩ x)
      bnd-pt n x = N , ≤-trans (decr-le h d n x) (b0 x)

      D : ℕ → Hom S X WQ
      D n = monusH (h 0) (h n) (λ x → bnd-rat _ (bnd-pt n x))

      D-add : ∀ n x → (map (h n) ⟨$⟩ x) + (map (D n) ⟨$⟩ x) ≈ map (h 0) ⟨$⟩ x
      D-add n x = monus-add (map (h 0) ⟨$⟩ x) (map (h n) ⟨$⟩ x) (bnd-pt n x) (decr-le h d n x)

      D-inc : ∀ n x → map (D n) ⟨$⟩ x ≤ map (D (suc n)) ⟨$⟩ x
      D-inc n x = monus-anti (map (h 0) ⟨$⟩ x) (d n x)

      E : Hom S X WQ
      E = supH D

      D≤E : ∀ n x → map (D n) ⟨$⟩ x ≤ map E ⟨$⟩ x
      D≤E n x = ⊑-trans (union-ub _ n) (proj₂ (supH-pt D x))

      E≤h0 : ∀ x → map E ⟨$⟩ x ≤ map (h 0) ⟨$⟩ x
      E≤h0 x = ⊑-trans (proj₁ (supH-pt D x)) (union-lub _ (λ n →
        ⊑-trans (t≤x+t (map (h n) ⟨$⟩ x) (map (D n) ⟨$⟩ x)) (≤-reflexive (D-add n x))))

      h0≤gE : ∀ x → map (h 0) ⟨$⟩ x ≤ (map (infH h) ⟨$⟩ x) + (map E ⟨$⟩ x)
      h0≤gE x = ⊑-trans (inter-add {b = λ n → map (h n) ⟨$⟩ x} (bnd-rat _ (N , ≤-trans (E≤h0 x) (b0 x)))
                  (λ n → ⊑-trans (≤-reflexive (sym (D-add n x))) (⊕-mono ⊑-refl (D≤E n x))))
                (⊕-mono (proj₂ (infH-pt h x)) ⊑-refl)

      s2 : ∀ n → ∫ᴹ {X} p (h n) + ∫ᴹ {X} p (D n) ≈ ∫ᴹ {X} p (h 0)
      s2 n = trans (sym (∫ᴹ-addX p (h n) (D n))) (∫ᴹ-cong p {addX (h n) (D n)} {h 0} (D-add n))

      s4 : interC (λ n → ∫ᴹ {X} p (h n)) + ∫ᴹ {X} p E ≤ ∫ᴹ {X} p (h 0)
      s4 = ⊑-trans (⊕-mono ⊑-refl (proj₁ (∫ᴹ-sup p D D-inc))) (⊑-trans (proj₁ (⊕-union _ _))
        (union-lub _ (λ n → ⊑-trans (⊕-mono (inter-lb _ n) ⊑-refl) (≤-reflexive (s2 n)))))

      bE : BndQ (∫ᴹ {X} p E)
      bE = bnd-rat _ (Bnd-≤′ (∫ᴹ-monoX p {E} {h 0} E≤h0) bT)

      s5 : ∫ᴹ {X} p (h 0) ≤ ∫ᴹ {X} p E + ∫ᴹ {X} p (infH h)
      s5 = ⊑-trans (∫ᴹ-monoX p {h 0} {addX (infH h) E} h0≤gE) (⊑-trans (proj₁ (∫ᴹ-addX p (infH h) E)) (⊕-comm⊑ _ _))

      s6 : interC (λ n → ∫ᴹ {X} p (h n)) ≤ ∫ᴹ {X} p (infH h)
      s6 = cancel-bnd-⊑ bE (⊑-trans (⊕-comm⊑ _ _) (⊑-trans s4 s5))

    ∫ᴹ-inf-fin : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) N → Decr h → (∀ x → map (h 0) ⟨$⟩ x ≤ nat N) →
      Bnd (∫ᴹ {X} p (h 0)) → ∫ᴹ {X} p (infH h) ≈ interC (λ n → ∫ᴹ {X} p (h n))
    ∫ᴹ-inf-fin p h N d b0 bT = inter-glb _ (λ n → ∫ᴹ-monoX p {infH h} {h n}
      (λ x → ⊑-trans (proj₁ (infH-pt h x)) (inter-lb _ n))) , Fin.s6 p h N d b0 bT

    tail-small : ∀ (p : C.Pre (XW X)) (f : Hom S X WQ) → Bnd (∫ᴹ {X} p f) →
      ∀ k → Σ ℕ (λ N → ∫ᴹ {X} p f ≤ ∫ᴹ {X} p (minH N f) + hp k)
    tail-small p f bnd k =
      let M , bdM = bnd-rat _ bnd
          r , mr , hr = near-sup-bnd (∫ᴹ {X} p f) M {tp (suc k)} bdM (tp-pos (suc k))
          U = ⊑-trans (proj₂ (∫ᴹ-cong p {supH (λ n → minH n f)} {f} (supMin f)))
                      (proj₁ (∫ᴹ-sup p (λ n → minH n f) (minH-inc f)))
          N , rN = ap U r mr
      in N , mk⊑ (λ q mq → let q′ , q<q′ , mq′ = open′ (∫ᴹ {X} p f) mq
                           in r , tp (suc k) , rN , hp-in k _ (tp-lt k) , Q.≤-trans (Q.<-≤ q<q′) (hr q′ mq′))

    -- ∫ h n + ∫ (h 0 ⊓ N) ≤ ∫ (h n ⊓ N) + ∫ h 0
    split-ineq : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) N → Decr h → ∀ n →
      ∫ᴹ {X} p (h n) + ∫ᴹ {X} p (minH N (h 0)) ≤ ∫ᴹ {X} p (minH N (h n)) + ∫ᴹ {X} p (h 0)
    split-ineq p h N d n = ⊑-trans (proj₂ (∫ᴹ-addX p (h n) (minH N (h 0))))
      (⊑-trans (∫ᴹ-monoX p {addX (h n) (minH N (h 0))} {addX (minH N (h n)) (h 0)}
                  (λ x → min-split-⊑ (nat N) (decr-le h d n x)))
        (proj₁ (∫ᴹ-addX p (minH N (h n)) (h 0))))

    -- ∫ h n ≤ ∫ (h n ⊓ N) + ½ᵏ, uniformly in n, from the tail of h 0
    step-A : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) N k → Decr h → Bnd (∫ᴹ {X} p (h 0)) →
      ∫ᴹ {X} p (h 0) ≤ ∫ᴹ {X} p (minH N (h 0)) + hp k → ∀ n → ∫ᴹ {X} p (h n) ≤ ∫ᴹ {X} p (minH N (h n)) + hp k
    step-A p h N k d bT ts n = cancel-bnd-⊑ bC (⊑-trans (⊕-comm⊑ C I) (⊑-trans (split-ineq p h N d n)
        (⊑-trans (⊕-mono ⊑-refl ts) (⊑-trans (proj₂ (⊕-assoc Hn C (hp k)))
          (⊑-trans (⊕-mono (⊕-comm⊑ Hn C) ⊑-refl) (proj₁ (⊕-assoc C Hn (hp k))))))))
      where
        I = ∫ᴹ {X} p (h n)
        C = ∫ᴹ {X} p (minH N (h 0))
        Hn = ∫ᴹ {X} p (minH N (h n))
        bC : BndQ C
        bC = bnd-rat _ (Bnd-≤′ (∫ᴹ-monoX p {minH N (h 0)} {h 0} (λ x → ⊓-lb _ _)) bT)

    -- truncating a decreasing sequence keeps it decreasing, bounded and below the original
    dec-min : ∀ (h : ℕ → Hom S X WQ) N → Decr h → Decr (λ n → minH N (h n))
    dec-min h N d n x = mk⊑ (λ q (m₁ , m₂) → ap (d n x) q m₁ , m₂)

    inf-min : ∀ (h : ℕ → Hom S X WQ) N x → map (infH (λ n → minH N (h n))) ⟨$⟩ x ≤ map (infH h) ⟨$⟩ x
    inf-min h N x = ⊑-trans (proj₁ (infH-pt (λ n → minH N (h n)) x))
      (⊑-trans (inter-mono (λ n → ⊓-lb _ _)) (proj₂ (infH-pt h x)))

    -- ∫ ⋂ h n is within ½ᵏ of the limit
    inf-k : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → Decr h → Bnd (∫ᴹ {X} p (h 0)) → ∀ k →
      interC (λ n → ∫ᴹ {X} p (h n)) ≤ ∫ᴹ {X} p (infH h) + hp k
    inf-k p h d bT k = ⊑-trans (inter-add {b = λ n → ∫ᴹ {X} p (minH N (h n))} (BndQ-hp k)
        (λ n → ⊑-trans (inter-lb _ n) (step-A p h N k d bT ts n)))
      (⊕-mono (⊑-trans (proj₂ fin) (∫ᴹ-monoX p {infH hN} {infH h} (inf-min h N))) ⊑-refl)
      where
        N = proj₁ (tail-small p (h 0) bT k)
        ts = proj₂ (tail-small p (h 0) bT k)
        hN : ℕ → Hom S X WQ
        hN n = minH N (h n)
        bTN : Bnd (∫ᴹ {X} p (hN 0))
        bTN = Bnd-≤′ (∫ᴹ-monoX p {hN 0} {h 0} (λ x → ⊓-lb _ _)) bT
        fin = ∫ᴹ-inf-fin p hN N (dec-min h N d) (λ x → mk⊑ (λ q m → proj₂ m)) bTN

    -- downward monotone convergence
    ∫ᴹ-inf : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → Decr h → Bnd (∫ᴹ {X} p (h 0)) →
      ∫ᴹ {X} p (infH h) ≈ interC (λ n → ∫ᴹ {X} p (h n))
    ∫ᴹ-inf p h d bT = inter-glb _ (λ n → ∫ᴹ-monoX p {infH h} {h n}
      (λ x → ⊑-trans (proj₁ (infH-pt h x)) (inter-lb _ n))) , approx (inf-k p h d bT)

    -- Fatou's lemma and its reverse
    shift : ∀ (h : ℕ → Hom S X WQ) n k x → map (h (n +ℕ suc k)) ⟨$⟩ x ≤ map (h (suc n +ℕ k)) ⟨$⟩ x
    shift h n k x = mk⊑ (λ q m → subst (λ i → mem (map (h i) ⟨$⟩ x) q) (+ℕ-suc n k) m)

    shift′ : ∀ (h : ℕ → Hom S X WQ) n k x → map (h (suc n +ℕ k)) ⟨$⟩ x ≤ map (h (n +ℕ suc k)) ⟨$⟩ x
    shift′ h n k x = mk⊑ (λ q m → subst (λ i → mem (map (h i) ⟨$⟩ x) q) (≡sym (+ℕ-suc n k)) m)

    fatou : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → ∫ᴹ {X} p (liminfH h) ≤ liminfC (λ n → ∫ᴹ {X} p (h n))
    fatou p h = ⊑-trans (proj₁ (∫ᴹ-sup p I inc)) (union-mono (λ n → inter-glb _ (λ k →
        ∫ᴹ-monoX p {I n} {h (n +ℕ k)} (λ x → ⊑-trans (proj₁ (infH-pt (λ j → h (n +ℕ j)) x)) (inter-lb _ k)))))
      where
        I : ℕ → Hom S X WQ
        I n = infH (λ k → h (n +ℕ k))
        inc : ∀ n x → map (I n) ⟨$⟩ x ≤ map (I (suc n)) ⟨$⟩ x
        inc n x = ⊑-trans (proj₁ (infH-pt (λ k → h (n +ℕ k)) x)) (⊑-trans
          (inter-glb _ (λ k → ⊑-trans (inter-lb _ (suc k)) (shift h n k x)))
          (proj₂ (infH-pt (λ k → h (suc n +ℕ k)) x)))

    rev-fatou : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) (g : Hom S X WQ) →
      (∀ n x → map (h n) ⟨$⟩ x ≤ map g ⟨$⟩ x) → Bnd (∫ᴹ {X} p g) →
      limsupC (λ n → ∫ᴹ {X} p (h n)) ≤ ∫ᴹ {X} p (limsupH h)
    rev-fatou p h g le bT = ⊑-trans (inter-mono (λ n → union-lub _ (λ k →
        ∫ᴹ-monoX p {h (n +ℕ k)} {J n} (λ x → ⊑-trans (union-ub _ k) (proj₂ (supH-pt (λ j → h (n +ℕ j)) x))))))
      (proj₂ (∫ᴹ-inf p J dJ (Bnd-≤′ (∫ᴹ-monoX p {J 0} {g} (λ x → ⊑-trans (proj₁ (supH-pt (λ j → h (0 +ℕ j)) x))
          (union-lub _ (λ k → le k x)))) bT)))
      where
        J : ℕ → Hom S X WQ
        J n = supH (λ k → h (n +ℕ k))
        dJ : Decr J
        dJ n x = ⊑-trans (proj₁ (supH-pt (λ k → h (suc n +ℕ k)) x)) (⊑-trans
          (union-lub _ (λ k → ⊑-trans (shift′ h n k x) (union-ub _ (suc k))))
          (proj₂ (supH-pt (λ k → h (n +ℕ k)) x)))
