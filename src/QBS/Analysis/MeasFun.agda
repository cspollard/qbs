{-# OPTIONS --safe --without-K #-}

-- Every threshold-measurable function R → [0,1] (`Analysis/Meas`) is in the inductive class `Fun`.
-- The approximants are the running maxima M N x = max {qₖ | k < N, qₖ ∈ h x} of the enumerated
-- rationals below h x; each is built from masks of constants by Borel sets, and h = ⨆ M N.
module QBS.Analysis.MeasFun where

open import Level using (lift; lower)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
open import Data.Rational.Unnormalised.Base using (_<_; _≤_)

open import QBS.Analysis.RationalLemmas
open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LowerRealsMin using (_⊓_)
open import QBS.Analysis.LevelSets using (enumQ; enumQ-surj; module LevelSets)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Classical using (LEM₀)
open Cut
open _⊑_

-- the cut of a rational: everything strictly below r (and the negatives)
ratC : ℚᵘ → Cut
ratC r = record
  { mem = λ s → (s < r) ⊎ (s < 0ℚᵘ)
  ; down = λ { le (inj₁ p<r) → inj₁ (≤-<-trans le p<r) ; le (inj₂ p<0) → inj₂ (≤-<-trans le p<0) }
  ; open′ = λ { (inj₁ p<r) → let t , p<t , t<r = dense p<r in t , p<t , inj₁ t<r
              ; (inj₂ p<0) → let t , p<t , t<0 = dense p<0 in t , p<t , inj₂ t<0 }
  ; neg = inj₂
  }

ratC-mono : ∀ {r r′} → r ≤ r′ → ratC r ⊑ ratC r′
ratC-mono le = mk⊑ (λ { s (inj₁ s<r) → inj₁ (<-≤-trans s<r le) ; s (inj₂ s<0) → inj₂ s<0 })

-- the candidate q replaces the running maximum b when it is a point of h x above b
pickQ : ∀ (q b : ℚᵘ) {P : Set} → (P ⊎ (P → ⊥)) → (q ≤ b ⊎ b < q) → ℚᵘ
pickQ q b (inj₁ _) (inj₂ _) = q
pickQ q b _ _ = b

pick-cases : ∀ q b {P : Set} (s₁ : P ⊎ (P → ⊥)) (s₂ : q ≤ b ⊎ b < q) →
  (pickQ q b s₁ s₂ ≡ b) ⊎ (P × ((b < q) × (pickQ q b s₁ s₂ ≡ q)))
pick-cases q b (inj₁ p) (inj₂ lt) = inj₂ (p , lt , ≡.refl)
pick-cases q b (inj₁ p) (inj₁ _) = inj₁ ≡.refl
pick-cases q b (inj₂ _) _ = inj₁ ≡.refl

pick-≥ : ∀ q b {P : Set} (s₁ : P ⊎ (P → ⊥)) (s₂ : q ≤ b ⊎ b < q) → b ≤ pickQ q b s₁ s₂
pick-≥ q b s₁ s₂ with pick-cases q b s₁ s₂
... | inj₁ e = ≡.subst (b ≤_) (≡.sym e) ≤-refl
... | inj₂ (_ , lt , e) = ≡.subst (b ≤_) (≡.sym e) (<-≤ lt)

-- a point of h x (P) is always below the new maximum
pick-covers : ∀ q b {P : Set} (s₁ : P ⊎ (P → ⊥)) (s₂ : q ≤ b ⊎ b < q) → P → q ≤ pickQ q b s₁ s₂
pick-covers q b (inj₁ _) (inj₁ le) p = le
pick-covers q b (inj₁ _) (inj₂ _) p = ≤-refl
pick-covers q b (inj₂ np) _ p = ⊥-elim (np p)

pick-W : ∀ q b {P : Set} (s₁ : P ⊎ (P → ⊥)) (s₂ : q ≤ b ⊎ b < q) → P → (q ≤ b → ⊥) → pickQ q b s₁ s₂ ≡ q
pick-W q b (inj₁ _) (inj₁ le) p nle = ⊥-elim (nle le)
pick-W q b (inj₁ _) (inj₂ _) p nle = ≡.refl
pick-W q b (inj₂ np) _ p nle = ⊥-elim (np p)

pick-nW : ∀ q b {P : Set} (s₁ : P ⊎ (P → ⊥)) (s₂ : q ≤ b ⊎ b < q) →
  ((P × (q ≤ b → ⊥)) → ⊥) → pickQ q b s₁ s₂ ≡ b
pick-nW q b (inj₁ p) (inj₂ lt) nw = ⊥-elim (nw (p , λ le → <-irrefl ≃-refl (≤-<-trans le lt)))
pick-nW q b (inj₁ p) (inj₁ _) nw = ≡.refl
pick-nW q b (inj₂ _) _ nw = ≡.refl

module MeasFun (lem : LEM₀) where
  A = LowerRealsOmega lem
  open Measurable A using (Fun; supF; sumF; Fun-const; Fun-ext; module Mask)
  open Meas lem using (Meas; all-enum; imp-borel)
  open LevelSets lem using (borel-prop)
  module OA = OmegaSemiring A

  module _ (h : R₁ → Cut) (bd : ∀ x → h x ⊑ oneC) (mh : Meas h) where

    -- the running maximum of the enumerated rationals below h x
    best : ℕ → R₁ → ℚᵘ

    sel : ∀ N x → mem (h x) (enumQ N) ⊎ (mem (h x) (enumQ N) → ⊥)
    sel N x = lem (mem (h x) (enumQ N))

    cmp : ∀ N x → enumQ N ≤ best N x ⊎ best N x < enumQ N
    cmp N x = ≤-or-> (enumQ N) (best N x)

    best zero x = 0ℚᵘ
    best (suc N) x = pickQ (enumQ N) (best N x) (sel N x) (cmp N x)

    best-≥ : ∀ N x → best N x ≤ best (suc N) x
    best-≥ N x = pick-≥ (enumQ N) (best N x) (sel N x) (cmp N x)

    pW : ∀ N x → mem (h x) (enumQ N) → (enumQ N ≤ best N x → ⊥) → best (suc N) x ≡ enumQ N
    pW N x = pick-W (enumQ N) (best N x) (sel N x) (cmp N x)

    pnW : ∀ N x → ((mem (h x) (enumQ N) × (enumQ N ≤ best N x → ⊥)) → ⊥) → best (suc N) x ≡ best N x
    pnW N x = pick-nW (enumQ N) (best N x) (sel N x) (cmp N x)

    below : ∀ N x s → s < best N x → mem (h x) s
    below zero x s s<0 = neg (h x) s<0
    below (suc N) x s s<b with pick-cases (enumQ N) (best N x) (sel N x) (cmp N x)
    ... | inj₁ e = below N x s (≡.subst (s <_) e s<b)
    ... | inj₂ (p , lt , e) = down (h x) (<-≤ (≡.subst (s <_) e s<b)) p

    covers : ∀ N x k → k ℕ.< N → mem (h x) (enumQ k) → enumQ k ≤ best N x
    covers zero x k () m
    covers (suc N) x k k<N m with ℕ.m<1+n⇒m<n∨m≡n k<N
    ... | inj₁ k<N′ = ≤-trans (covers N x k k<N′ m) (best-≥ N x)
    ... | inj₂ ≡.refl = pick-covers (enumQ N) (best N x) (sel N x) (cmp N x) m

    M : ℕ → R₁ → Cut
    M N x = ratC (best N x)

    M⊑h : ∀ N x → M N x ⊑ h x
    M⊑h N x = mk⊑ (λ { s (inj₁ s<b) → below N x s s<b ; s (inj₂ s<0) → neg (h x) s<0 })

    inc : ∀ x → OA.Increasing (λ N → M N x)
    inc x N = ratC-mono (best-≥ N x)

    eq : ∀ x → h x ≋ unionC (λ N → M N x)
    eq x = mk⊑ fwd , union-lub (λ N → M N x) (λ N → M⊑h N x)
      where
        fwd : ∀ s → mem (h x) s → Σ ℕ (λ N → mem (M N x) s)
        fwd s m with open′ (h x) m
        ... | q′ , s<q′ , mq′ with enumQ-surj q′
        ... | k , ≡.refl = suc k , inj₁ (<-≤-trans s<q′ (covers (suc k) x k (ℕ.n<1+n k) mq′))

    ----------------------------------------------------------------------------
    -- the events {s < best N} and {t ≤ best N} are Borel

    W : ℕ → Pred
    W N c = mem (h (lift c)) (enumQ N) × (enumQ N ≤ best N (lift c) → ⊥)

    -- the two set identities used below
    BB-eq : ∀ N s → (λ c → (W N c × (s < enumQ N)) ⊎ ((W N c → ⊥) × (s < best N (lift c)))) ≐ (λ c → s < best (suc N) (lift c))
    BB-eq N s c = fwd , bwd
      where
        fwd : (W N c × (s < enumQ N)) ⊎ ((W N c → ⊥) × (s < best N (lift c))) → s < best (suc N) (lift c)
        fwd (inj₁ ((p , nle) , lt)) = ≡.subst (s <_) (≡.sym (pW N (lift c) p nle)) lt
        fwd (inj₂ (nw , lt)) = ≡.subst (s <_) (≡.sym (pnW N (lift c) nw)) lt
        bwd : s < best (suc N) (lift c) → (W N c × (s < enumQ N)) ⊎ ((W N c → ⊥) × (s < best N (lift c)))
        bwd lt with lem (W N c)
        ... | inj₁ w@(p , nle) = inj₁ (w , ≡.subst (s <_) (pW N (lift c) p nle) lt)
        ... | inj₂ nw = inj₂ (nw , ≡.subst (s <_) (pnW N (lift c) nw) lt)

    bGE-eq : ∀ N t → (λ c → ∀ ρ → ρ < t → ρ < best N (lift c)) ≐ (λ c → t ≤ best N (lift c))
    bGE-eq N t c = fwd , (λ le ρ ρ<t → <-≤-trans ρ<t le)
      where
        fwd : (∀ ρ → ρ < t → ρ < best N (lift c)) → t ≤ best N (lift c)
        fwd f with ≤-or-> t (best N (lift c))
        ... | inj₁ le = le
        ... | inj₂ b<t = let ρ , b<ρ , ρ<t = dense b<t in ⊥-elim (<-irrefl ≃-refl (<-trans b<ρ (f ρ ρ<t)))

    mutual
      BB : ∀ N s → Borel (λ c → s < best N (lift c))
      BB zero s = borel-prop (s < 0ℚᵘ)
      BB (suc N) s = resp (BB-eq N s) (union₂ (inter₂ (bW N) (borel-prop (s < enumQ N))) (inter₂ (compl (bW N)) (BB N s)))

      bGE : ∀ N t → Borel (λ c → t ≤ best N (lift c))
      bGE N t = resp (bGE-eq N t) (all-enum (λ ρ c → ρ < t → ρ < best N (lift c)) (λ ρ → imp-borel (ρ < t) (BB N ρ)))

      bW : ∀ N → Borel (W N)
      bW N = inter₂ (mh (enumQ N)) (compl (bGE N (enumQ N)))

    ----------------------------------------------------------------------------
    -- each approximant is a Fun

    cN : ℕ → Cut
    cN N = ratC (enumQ N) ⊓ oneC

    cN-ratC : ∀ N → mem oneC (enumQ N) → cN N ≋ ratC (enumQ N)
    cN-ratC N lt = mk⊑ (λ s m → proj₁ m) , mk⊑
        (λ { s (inj₁ s<q) → inj₁ s<q , <-trans s<q lt ; s (inj₂ s<0) → inj₂ s<0 , <-trans s<0 0<1 })

    -- the step from `M N` to `M (suc N)`: on `W N` the approximant is the constant `cN N`, elsewhere it is `M N`
    module Step N (FMN : Fun (M N)) where
      module MW = Mask {W N} (bW N) (λ y → lem (W N y))
      module MN = Mask {λ c → W N c → ⊥} (compl (bW N)) (λ y → lem (W N y → ⊥))

      F₁ : Fun (MW.mask (λ _ → cN N))
      F₁ = MW.Fun-mask (Fun-const (cN N) (mk⊑ (λ s m → proj₂ m)))

      F₂ : Fun (MN.mask (M N))
      F₂ = MN.Fun-mask FMN

      pw-in : ∀ x → W N (lower x) → M (suc N) x OA.≈ MW.mask (λ _ → cN N) x OA.+ MN.mask (M N) x
      pw-in x w@(p , nle) = OA.trans (≡.subst (λ r → ratC r ≋ ratC (enumQ N)) (≡.sym (pW N x p nle)) ≋-refl)
        (OA.trans (OA.sym (cN-ratC N (ap (bd x) (enumQ N) p)))
          (OA.trans (OA.sym (OA.+-identityʳ _))
            (OA.sym (OA.+-cong (MW.mask-in (λ _ → cN N) x w) (MN.mask-out (M N) x (λ nw → nw w))))))

      pw-out : ∀ x → (W N (lower x) → ⊥) → M (suc N) x OA.≈ MW.mask (λ _ → cN N) x OA.+ MN.mask (M N) x
      pw-out x nw = OA.trans (≡.subst (λ r → ratC (best (suc N) x) ≋ ratC r) (pnW N x nw) ≋-refl)
        (OA.sym (OA.trans (OA.+-cong (MW.mask-out (λ _ → cN N) x nw) (MN.mask-in (M N) x nw)) (OA.+-identityˡ _)))

      pw : ∀ x → M (suc N) x OA.≈ MW.mask (λ _ → cN N) x OA.+ MN.mask (M N) x
      pw x = MW.dec′ x (pw-in x) (pw-out x)

      bound : ∀ x → M (suc N) x OA.≤ OA.1#
      bound x = ⊑-trans (M⊑h (suc N) x) (bd x)

    FM : ∀ N → Fun (M N)
    FM zero = Fun-ext (λ x → mk⊑ (λ s s<0 → inj₁ s<0) , mk⊑ (λ { s (inj₁ s<0) → s<0 ; s (inj₂ s<0) → s<0 }))
                      (Fun-const zeroC 0-least)
    FM (suc N) = sumF F₁ F₂ pw bound
      where open Step N (FM N)

    measFun : Fun h
    measFun = supF M FM inc eq

  Meas→Fun : ∀ {h} → (∀ x → h x ⊑ oneC) → Meas h → Fun h
  Meas→Fun {h} bd mh = measFun h bd mh
