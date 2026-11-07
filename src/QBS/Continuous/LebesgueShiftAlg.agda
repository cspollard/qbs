{-# OPTIONS --safe --without-K #-}

-- The interval computations for the translation of Lebesgue measure (`LebesgueShift`), at the level of the integrals of
-- the tests `χ[a,b)` and `χ{∞}` against a pre-measure.
--   * `Iv-from-F`: if `∫ μ χ[0,b) ≈ b` for every bounded b then `a + ∫ μ χ[a,b) ≈ b` (a ≤ b, b bounded);
--   * `bnd-rat`: a bounded cut lies below a rational;
--   * pointwise facts for a bounded t: `χ[0,b)(x + t) = 0` when b ≤ t (`below-zero`), `χ[0,b)(x + t) = χ[0,d)(x)` for the
--     difference d of `LebesgueShiftCut` (`shift-eq`), `χ{∞}(x + t) = χ{∞}(x)` (`inf-shift`), and the products
--     `χ[0,t) · χ[0,b)` for b ≤ t and t ≤ b, and `χ[0,t) · χ{∞} = 0`.
module QBS.Continuous.LebesgueShiftAlg where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Rational.Unnormalised.Base as ℚ
import Data.Nat.Properties as ℕP

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut; mk⊑; _⊑_; ⊕-comm⊑; ⊑-refl; ⊕-mono; ⊑-trans)
open Cut using (mem; down)
open _⊑_ using (ap)
open import QBS.Analysis.ExpLower using (natE≋)
import QBS.Analysis.RationalLemmas as RL
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.DigitCut using (module DigitCut)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)

-- The difference of two lower cuts, for the translation of Lebesgue measure (`LebesgueShift`).  For cuts t ⊑ b with t
-- bounded by a rational, `diffC t b` is the cut of q such that q′ + s ∈ b for some q′ > q and all s ∈ t, and
--   * `diff-sum`: `t ⊕ diffC t b ≋ b`;
--   * `diff-⇐`: `b ⊑ x ⊕ t` gives `diffC t b ⊑ x`, for every x (also x = ∞), without cancellation;
--   * `top-sub`: if x ⊕ t contains every rational then so does x.
module LebesgueShiftCut (lem : LEM₀) where
  open import Data.Rational.Unnormalised.Base using (_+_; _<_; -_)
  open import QBS.Analysis.RationalLemmas
  open import QBS.Analysis.LowerReals
  open Cut using (mem; down; open′; neg)
  open _⊑_ using (ap)
  open import QBS.Analysis.LowerInverse using (module InvClassical)
  open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
  open +-*-Solver using (solve; _:+_; :-_; _:=_)
  open InvClassical lem using (near-sup′)

  diffC : ∀ t b → t ⊑ b → Cut
  diffC t b tb = record
    { mem = λ q → Σ ℚᵘ (λ q′ → q < q′ × (∀ s → mem t s → mem b (q′ + s)))
    ; down = λ le (q′ , lt , h) → q′ , ≤-<-trans le lt , h
    ; open′ = λ {q} (q′ , lt , h) → let q″ , a , c = dense lt in q″ , a , q′ , c , h
    ; neg = λ {p} p<0 → 0ℚᵘ , p<0 , (λ s ms → down b (≤-≃ (+-identityˡ s)) (ap tb s ms)) }

  -- t ⊕ diffC ⊑ b
  diff-⊑ : ∀ t b tb → t ⊕ diffC t b tb ⊑ b
  diff-⊑ t b tb = mk⊑ (λ q (r , s , mr , (s′ , lt , h) , le) →
    down b (≤-trans le (≤-trans (+-mono-≤ (≤-refl {r}) (<-≤ lt)) (≤-≃ (+-comm r s′)))) (h r mr))

  -- b ⊑ t ⊕ diffC, for t bounded
  diff-⊒ : ∀ t b tb M → (∀ r → mem t r → r < M) → b ⊑ t ⊕ diffC t b tb
  diff-⊒ t b tb M bd = mk⊑ (λ q mq →
    let q₁ , q<q₁ , m₁ = open′ b mq
        q₂ , q₁<q₂ , m₂ = open′ b m₁
        ε = q₂ + - q₁
        r , mr , hr = near-sup′ t M bd (pos-diff q₁<q₂)
        s = q + - r
        s′ = q₁ + - r
        s<s′ : s < s′
        s<s′ = +-mono-<-≤ q<q₁ (≤-refl {(- r)})
        ok : ∀ u → mem t u → mem b (s′ + u)
        ok u mu = down b (≤-trans (+-mono-≤ (≤-refl {s′}) (hr u mu))
          (≤-≃ (solve 3 (λ q₁ r q₂ → (q₁ :+ :- r) :+ (r :+ (q₂ :+ :- q₁)) := q₂) ≃-refl q₁ r q₂))) m₂
    in r , s , mr , (s′ , s<s′ , ok) , ≤-≃ (≃-sym (add-sub r q)))

  diff-sum : ∀ t b tb M → (∀ r → mem t r → r < M) → t ⊕ diffC t b tb ≋ b
  diff-sum t b tb M bd = diff-⊑ t b tb , diff-⊒ t b tb M bd

  -- b ⊑ x ⊕ t gives diffC ⊑ x
  diff-⇐ : ∀ t b tb M → (∀ r → mem t r → r < M) → ∀ x → b ⊑ x ⊕ t → diffC t b tb ⊑ x
  diff-⇐ t b tb M bd x f = mk⊑ (λ q (q′ , lt , h) →
    [ (λ y → y) , (λ n → ⊥-elim (contra q q′ lt h n)) ]′ (lem (mem x q)))
    where
      contra : ∀ q q′ → q < q′ → (∀ s → mem t s → mem b (q′ + s)) → (mem x q → ⊥) → ⊥
      contra q q′ lt h n =
        let u , mu , hu = near-sup′ t M bd (pos-diff lt)
            r , s , mr , ms , le = ap f (q′ + u) (h u mu)
            r<q : r < q
            r<q = [ (λ q≤r → ⊥-elim (n (down x q≤r mr))) , (λ r<q → r<q) ]′ (≤-or-> q r)
            chain : (q′ + u) < (q′ + u)
            chain = <-≤-trans (≤-<-trans le (+-mono-<-≤ r<q (≤-refl {s})))
              (≤-trans (+-mono-≤ (≤-refl {q}) (hu s ms))
                (≤-≃ (solve 3 (λ q u q′ → q :+ (u :+ (q′ :+ :- q)) := q′ :+ u) ≃-refl q u q′)))
        in <-irrefl ≃-refl chain

  -- ⊤ ⊕ t: if every rational lies in x ⊕ t then in x
  top-sub : ∀ t M → (∀ r → mem t r → r < M) → ∀ x → (∀ q → mem (x ⊕ t) q) → ∀ q → mem x q
  top-sub t M bd x all q =
    let r , s , mr , ms , le = all (q + M)
    in [ (λ q≤r → down x q≤r mr)
       , (λ r<q → ⊥-elim (<-irrefl ≃-refl (≤-<-trans le (+-mono-< r<q (bd s ms))))) ]′ (≤-or-> q r)

module LebesgueShiftAlg (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive; +-comm;
    ≤-+ʳ; 0-least; +-identityˡ; zeroˡ; zeroʳ; *-identityˡ; *-comm) renaming (Carrier to ∣A∣)
  open Bounded A using (nat; Bnd)
  open Exp A using (natE)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; module C)
  open C using (Pre)
  open SFiniteReweight lem using (mulH)
  open Intervals lem using (Ge; InIv; InInf; χIv; χInf; χIv-in; χIv-out; χInf-in; χInf-out; tv-cong; split-iv)
  open DigitCut lem using (nat-big)
  open LebesgueDyadicAlg lem using (natE≈nat; natE-mono)
  open LebesgueIntervalAlg lem using (∫ᴹ-split-iv; F)
  open LebesgueShiftCut lem
  open QBS
  open Hom

  -- the reduction to intervals starting at 0
  Iv-from-F : ∀ p → (∀ b → Bnd b → F p b ≈ b) → ∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} p (χIv a b) ≈ b
  Iv-from-F p Feq a b ab (k , bk) = trans
    (+-cong (sym (Feq a (k , ≤-trans ab bk))) refl)
    (trans (sym (∫ᴹ-split-iv p 0# a b (ap (0-least {a})) (ap ab))) (Feq b (k , bk)))

  -- a bounded cut lies below a rational
  bnd-rat : ∀ t → Bnd t → Σ ℚ.ℚᵘ (λ M → ∀ r → mem t r → r ℚ.< M)
  bnd-rat t (n , h) = RL.nat (suc n) , λ r mr →
    ap (proj₁ (natE≋ lem n)) r (ap (≤-trans h (≤-trans (≤-reflexive (sym (natE≈nat n))) (natE-mono (ℕP.n≤1+n n)))) r mr)

  0≤ : ∀ x → Ge 0# x
  0≤ x = ap (0-least {x})

  t≤x+t : ∀ x t → t ≤ x + t
  t≤x+t x t = ≤-trans (≤-+ʳ {t} {x}) (≤-reflexive (+-comm t x))

  -- below a bounded t the translated test vanishes
  below-zero : ∀ b t x → b ≤ t → map (χIv 0# b) ⟨$⟩ (x + t) ≈ 0#
  below-zero b t x bt = χIv-out 0# b (x + t) (λ (_ , nb) → nb (ap (≤-trans bt (t≤x+t x t))))

  -- the product of two interval tests when one interval is inside the other
  prod-⊆ : ∀ u v x → (InIv 0# u x → InIv 0# v x) → map (mulH {WQ} (χIv 0# v) (χIv 0# u)) ⟨$⟩ x ≈ map (χIv 0# u) ⟨$⟩ x
  prod-⊆ u v x sub = [ (λ i → trans (*-cong (χIv-in 0# v x (sub i)) (χIv-in 0# u x i))
        (trans (*-identityˡ 1#) (sym (χIv-in 0# u x i))))
    , (λ n → trans (*-cong refl (χIv-out 0# u x n)) (trans (zeroʳ _) (sym (χIv-out 0# u x n)))) ]′ (lem (InIv 0# u x))

  prod-≤ : ∀ b t x → b ≤ t → map (mulH {WQ} (χIv 0# t) (χIv 0# b)) ⟨$⟩ x ≈ map (χIv 0# b) ⟨$⟩ x
  prod-≤ b t x bt = prod-⊆ b t x (λ (_ , nb) → 0≤ x , λ gt → nb (ap (≤-trans bt (mk⊑ {t} {x} gt))))

  prod-≥ : ∀ b t x → t ≤ b → map (mulH {WQ} (χIv 0# t) (χIv 0# b)) ⟨$⟩ x ≈ map (χIv 0# t) ⟨$⟩ x
  prod-≥ b t x tb = trans (*-comm _ _) (prod-⊆ t b x (λ (_ , nt) → 0≤ x , λ gb → nt (ap (≤-trans tb (mk⊑ {b} {x} gb)))))

  -- a bounded t: `χ[0,t) · χ{∞} = 0`
  prod-inf : ∀ t → Bnd t → ∀ x → map (mulH {WQ} (χIv 0# t) χInf) ⟨$⟩ x ≈ 0#
  prod-inf t (n , h) x = [ (λ inf → trans (*-cong (χIv-out 0# t x (λ (_ , nt) → nt (ap (le inf)))) refl) (zeroˡ _))
    , (λ ninf → trans (*-cong refl (χInf-out x ninf)) (zeroʳ _)) ]′ (lem (InInf x))
    where le = λ inf → ≤-trans h (≤-trans (≤-reflexive (sym (natE≈nat n))) (mk⊑ {natE n} {x} (inf n)))

  -- ∞ is fixed by translation by a bounded t, and only by it
  top-of : ∀ x → InInf x → ∀ q → mem x q
  top-of x inf q = let k , mk = nat-big q in inf k q mk

  inf-shift : ∀ t → Bnd t → ∀ x → map χInf ⟨$⟩ (x + t) ≈ map χInf ⟨$⟩ x
  inf-shift t bt x = tv-cong f g
    where
      M = bnd-rat t bt
      f : InInf (x + t) → InInf x
      f inf k q _ = top-sub t (proj₁ M) (proj₂ M) x (top-of (x + t) inf) q
      g : InInf x → InInf (x + t)
      g inf k q mq = ap (≤-+ʳ {x} {t}) q (inf k q mq)

  -- the translated test below a difference
  shift-eq : ∀ t b → (tb : t ≤ b) → Bnd t → ∀ x → map (χIv 0# b) ⟨$⟩ (x + t) ≈ map (χIv 0# (diffC t b tb)) ⟨$⟩ x
  shift-eq t b tb bt x = tv-cong f g
    where
      M = bnd-rat t bt
      ds = diff-sum t b tb (proj₁ M) (proj₂ M)
      f : InIv 0# b (x + t) → InIv 0# (diffC t b tb) x
      f (_ , nb) = 0≤ x , λ gd → nb (ap (⊑-trans (proj₂ ds) (⊑-trans (⊕-mono ⊑-refl (mk⊑ gd)) (⊕-comm⊑ t x))))
      g : InIv 0# (diffC t b tb) x → InIv 0# b (x + t)
      g (_ , nd) = 0≤ (x + t) , λ gb → nd (ap (diff-⇐ t b tb (proj₁ M) (proj₂ M) x (mk⊑ gb)))

  -- cuts are totally ordered (classically)
  total : ∀ t b → t ≤ b ⊎ b ≤ t
  total t b = [ (λ (q , mt , nb) → inj₂ (mk⊑ (λ p mp → down t (RL.<-≤ (lt p q mp nb)) mt)))
    , (λ none → inj₁ (mk⊑ (λ q mt → [ (λ y → y) , (λ nb → ⊥-elim (none (q , mt , nb))) ]′ (lem (mem b q))))) ]′
    (lem (Σ ℚ.ℚᵘ (λ q → mem t q × (mem b q → ⊥))))
    where
      lt : ∀ p q → mem b p → (mem b q → ⊥) → p ℚ.< q
      lt p q mp nb = [ (λ q≤p → ⊥-elim (nb (down b q≤p mp))) , (λ p<q → p<q) ]′ (RL.≤-or-> q p)
