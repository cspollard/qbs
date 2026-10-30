{-# OPTIONS --safe --without-K #-}

-- Sums of lower cuts over an arbitrary index set `I : Set₁`.
--
-- `Mem f q` says that q lies below a finite sum of members of the cuts `f i` over DISTINCT
-- indices.  It is inductive, with no lists: a step picks an index `i` and a member `r` of `f i`,
-- and continues with any `g` that is below `f` away from `i` and below zero at `i` (so `i` can
-- only contribute negatives afterwards).  No decidability of equality is needed to state it.  The
-- sum cut is `Mem` resized from `Set₁` to the `Set` carrier predicate with classical `lem₁`.
module QBS.Analysis.CutSum where

import Level as L
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_

data Mem {I : Set₁} : (I → Cut) → ℚᵘ → Set₁ where
  m-neg : ∀ {f q} → q < 0ℚᵘ → Mem f q
  m-step : ∀ {f q q′} (i : I) (r : ℚᵘ) (g : I → Cut) → mem (f i) r →
    (∀ j → (i ≡ j → ⊥) → g j ⊑ f j) → g i ⊑ zeroC → Mem g q′ → q ≤ r + q′ → Mem f q

module Basic {I : Set₁} where

  Mem-mono : ∀ {f f′ : I → Cut} {q} → (∀ j → f j ⊑ f′ j) → Mem f q → Mem f′ q
  Mem-mono fl (m-neg lt) = m-neg lt
  Mem-mono fl (m-step i r g mr ex gz mg le) =
    m-step i r g (ap (fl i) r mr) (λ j ne → ⊑-trans (ex j ne) (fl j)) gz mg le

  Mem-down : ∀ {f : I → Cut} {p q} → q ≤ p → Mem f p → Mem f q
  Mem-down le (m-neg lt) = m-neg (≤-<-trans le lt)
  Mem-down le (m-step i r g mr ex gz mg le′) = m-step i r g mr ex gz mg (≤-trans le le′)

  Mem-open : ∀ {f : I → Cut} {p} → Mem f p → Σ ℚᵘ (λ p′ → p < p′ × Mem f p′)
  Mem-open (m-neg lt) = let p′ , p<p′ , p′<0 = dense lt in p′ , p<p′ , m-neg p′<0
  Mem-open (m-step {f} {q′ = q′} i r g mr ex gz mg le) =
    let r′ , r<r′ , mr′ = open′ (f i) mr
    in r′ + q′ , ≤-<-trans le (+-mono-<-≤ r<r′ (≤-refl {q′})) , m-step i r′ g mr′ ex gz mg ≤-refl

open import Data.Empty.Polymorphic as E⊥ using ()
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open Basic

private
  add-neg-le : ∀ {r q′} → q′ < 0ℚᵘ → r + q′ ≤ r
  add-neg-le {r} lt = ≤-trans (+-mono-≤ (≤-refl {r}) (<-≤ lt)) (≤-≃ (+-identityʳ r))

  add-neg-le′ : ∀ {a b} → a < 0ℚᵘ → a + b ≤ b
  add-neg-le′ {a} {b} lt = ≤-trans (+-mono-≤ (<-≤ lt) (≤-refl {b})) (≤-≃ (+-identityˡ b))

----------------------------------------------------------------------------
-- the empty index set and the one-point index set

Mem-empty : ∀ {f : E⊥.⊥ {L.suc L.zero} → Cut} {q} → Mem f q → q < 0ℚᵘ
Mem-empty (m-neg lt) = lt
Mem-empty (m-step () r g mr ex gz mg le)

Mem-unit : ∀ {f : ⊤ {L.suc L.zero} → Cut} {q} → Mem f q → mem (f tt) q
Mem-unit {f} (m-neg lt) = neg (f tt) lt
Mem-unit {f} (m-step i r g mr ex gz mg le) =
  down (f tt) (≤-trans le (add-neg-le (ap gz _ (Mem-unit mg)))) mr

Mem-unit⁻ : ∀ {f : ⊤ {L.suc L.zero} → Cut} {q} → mem (f tt) q → Mem f q
Mem-unit⁻ {f} {q} m =
  let q′ , q<q′ , mq′ = open′ (f tt) m
  in m-step tt q′ (λ _ → zeroC) mq′ (λ j ne → ⊥-elim (ne refl)) ⊑-refl (m-neg (neg-diff q<q′))
       (≤-≃ (≃-sym (add-sub q′ q)))

----------------------------------------------------------------------------
-- disjoint unions

open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
import Data.Rational.Unnormalised.Properties as P
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

module Sum {I J : Set₁} where

  copair : (I → Cut) → (J → Cut) → I ⊎ J → Cut
  copair F G (inj₁ i) = F i
  copair F G (inj₂ j) = G j

  inl-inj : ∀ {x y : I} → _≡_ {A = I ⊎ J} (inj₁ x) (inj₁ y) → x ≡ y
  inl-inj refl = refl

  inr-inj : ∀ {x y : J} → _≡_ {A = I ⊎ J} (inj₂ x) (inj₂ y) → x ≡ y
  inr-inj refl = refl

  lift-r : ∀ {G : J → Cut} {b} → Mem G b → ∀ (H : I → Cut) → Mem (copair H G) b
  lift-r (m-neg lt) H = m-neg lt
  lift-r {G} (m-step j r g mr ex gz mg le) H =
    m-step (inj₂ j) r (copair H g) mr ex′ gz (lift-r mg H) le
    where
      ex′ : ∀ k → (inj₂ j ≡ k → ⊥) → copair H g k ⊑ copair H G k
      ex′ (inj₁ i) _ = ⊑-refl
      ex′ (inj₂ j′) ne = ex j′ (λ e → ne (cong inj₂ e))

  combine : ∀ {F : I → Cut} {a} → Mem F a → ∀ (G : J → Cut) {b} → Mem G b → Mem (copair F G) (a + b)
  combine {F} (m-neg lt) G mb = Mem-down (add-neg-le′ lt) (lift-r mb F)
  combine {F} (m-step {q′ = q′} i r F′ mr ex gz mF′ le) G {b} mb =
    m-step (inj₁ i) r (copair F′ G) mr ex′ gz (combine mF′ G mb)
      (≤-trans (+-mono-≤ le (≤-refl {b})) (≤-≃ (+-assoc r q′ b)))
    where
      ex′ : ∀ k → (inj₁ i ≡ k → ⊥) → copair F′ G k ⊑ copair F G k
      ex′ (inj₁ j) ne = ex j (λ e → ne (cong inj₁ e))
      ex′ (inj₂ j) _ = ⊑-refl

  split : ∀ {f : I ⊎ J → Cut} {q} → Mem f q →
    Σ ℚᵘ (λ a → Σ ℚᵘ (λ b → Mem (λ i → f (inj₁ i)) a × Mem (λ j → f (inj₂ j)) b × q ≤ a + b))
  split (m-neg lt) = let a , b , a<0 , b<0 , le = split-neg lt in a , b , m-neg a<0 , m-neg b<0 , le
  split {f} (m-step {q′ = q′} (inj₁ i) r g mr ex gz mg le) =
    let a , b , ma , mb , le′ = split mg
    in r + a , b
       , m-step i r (λ j → g (inj₁ j)) mr (λ j ne → ex (inj₁ j) (λ e → ne (inl-inj e))) gz ma ≤-refl
       , Mem-mono (λ j → ex (inj₂ j) (λ ())) mb
       , ≤-trans le (≤-trans (+-mono-≤ (≤-refl {r}) le′) (≤-≃ (≃-sym (+-assoc r a b))))
  split {f} (m-step {q′ = q′} (inj₂ j) r g mr ex gz mg le) =
    let a , b , ma , mb , le′ = split mg
    in a , r + b
       , Mem-mono (λ i → ex (inj₁ i) (λ ())) ma
       , m-step j r (λ k → g (inj₂ k)) mr (λ k ne → ex (inj₂ k) (λ e → ne (inr-inj e))) gz mb ≤-refl
       , ≤-trans le (≤-trans (+-mono-≤ (≤-refl {r}) le′)
           (≤-≃ (solve 3 (λ r a b → r :+ (a :+ b) := a :+ (r :+ b)) ≃-refl r a b)))

  join : ∀ {f : I ⊎ J → Cut} {a b q} → Mem (λ i → f (inj₁ i)) a → Mem (λ j → f (inj₂ j)) b → q ≤ a + b → Mem f q
  join {f} ma mb le = Mem-down le
    (Mem-mono (λ { (inj₁ i) → ⊑-refl ; (inj₂ j) → ⊑-refl }) (combine ma (λ j → f (inj₂ j)) mb))

----------------------------------------------------------------------------
-- reindexing along a bijection

module Reindex {I J : Set₁} where
  open import Relation.Binary.PropositionalEquality.Core using (subst)

  reidx : ∀ (φ : I → J) (ψ : J → I) → (∀ i → ψ (φ i) ≡ i) → (∀ j → φ (ψ j) ≡ j) →
    ∀ {g : I → Cut} {q} → Mem g q → Mem (λ j → g (ψ j)) q
  reidx φ ψ ψφ φψ (m-neg lt) = m-neg lt
  reidx φ ψ ψφ φψ {g} (m-step i r g′ mr ex gz mg le) =
    m-step (φ i) r (λ j → g′ (ψ j)) (subst (λ u → mem (g u) r) (sym (ψφ i)) mr)
      (λ k ne → ex (ψ k) (λ e → ne (trans (cong φ e) (φψ k))))
      (subst (λ u → g′ u ⊑ zeroC) (sym (ψφ i)) gz) (reidx φ ψ ψφ φψ mg) le

----------------------------------------------------------------------------
-- classical part: the sum cut, killing entries

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP; UIP)
open import Data.Product.Properties using (,-injectiveʳ-UIP)
open import Relation.Nullary using (Dec; yes; no)

module CSum (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) where

  -- with excluded middle for `Set₁`, equality on `Set₁`-types is decidable, hence proof-irrelevant
  dec≡ : ∀ {A : Set₁} (a b : A) → Dec (a ≡ b)
  dec≡ a b with lem₁ (a ≡ b)
  ... | inj₁ e = yes e
  ... | inj₂ n = no n

  uip : ∀ {A : Set₁} → UIP A
  uip {A} = Decidable⇒UIP.≡-irrelevant dec≡

  -- the second component of a dependent pair determines the pair
  ι-inj : ∀ {I : Set₁} {J : I → Set₁} {i : I} {j j′ : J i} → _≡_ {A = Σ I J} (i , j) (i , j′) → j ≡ j′
  ι-inj = ,-injectiveʳ-UIP uip

  private
    dec : Set₁ → Bool
    dec P with lem₁ P
    ... | inj₁ _ = true
    ... | inj₂ _ = false

    dec-true : ∀ {P} → P → dec P ≡ true
    dec-true {P} p with lem₁ P
    ... | inj₁ _ = refl
    ... | inj₂ np with np p
    ...   | ()

    from-true : ∀ {P} → dec P ≡ true → P
    from-true {P} e with lem₁ P
    ... | inj₁ p = p

  -- the sum of a family of cuts
  sumC : ∀ {I : Set₁} → (I → Cut) → Cut
  sumC {I} f = record
    { mem = λ q → dec (Mem f q) ≡ true
    ; down = λ le d → dec-true (Mem-down le (from-true d))
    ; open′ = λ d → let p′ , lt , m = Mem-open (from-true d) in p′ , lt , dec-true m
    ; neg = λ lt → dec-true (m-neg lt) }

  Mem⇒sum : ∀ {I : Set₁} {f : I → Cut} {q} → Mem f q → mem (sumC f) q
  Mem⇒sum = dec-true

  sum⇒Mem : ∀ {I : Set₁} {f : I → Cut} {q} → mem (sumC f) q → Mem f q
  sum⇒Mem = from-true

  sum-mono : ∀ {I : Set₁} {f f′ : I → Cut} → (∀ j → f j ⊑ f′ j) → sumC f ⊑ sumC f′
  sum-mono fl = mk⊑ (λ q d → dec-true (Mem-mono fl (from-true d)))

  -- kill the entries satisfying a predicate
  killP : ∀ {I : Set₁} → (I → Set₁) → (I → Cut) → I → Cut
  killP P f j with lem₁ (P j)
  ... | inj₁ _ = zeroC
  ... | inj₂ _ = f j

  killP-⊑ : ∀ {I : Set₁} (P : I → Set₁) (f : I → Cut) j → killP P f j ⊑ f j
  killP-⊑ P f j with lem₁ (P j)
  ... | inj₁ _ = 0-least
  ... | inj₂ _ = ⊑-refl

  killP-on : ∀ {I : Set₁} (P : I → Set₁) (f : I → Cut) {j} → P j → killP P f j ⊑ zeroC
  killP-on P f {j} p with lem₁ (P j)
  ... | inj₁ _ = ⊑-refl
  ... | inj₂ np = ⊥-elim (np p)

  killP-off : ∀ {I : Set₁} (P : I → Set₁) (f : I → Cut) {j} → (P j → ⊥) → f j ⊑ killP P f j
  killP-off P f {j} np with lem₁ (P j)
  ... | inj₁ p = ⊥-elim (np p)
  ... | inj₂ _ = ⊑-refl

  killP-mono : ∀ {I : Set₁} (P : I → Set₁) {f f′ : I → Cut} → (∀ j → f j ⊑ f′ j) → ∀ j → killP P f j ⊑ killP P f′ j
  killP-mono P fl j with lem₁ (P j)
  ... | inj₁ _ = ⊑-refl
  ... | inj₂ _ = fl j

  -- what a step leaves is below the original everywhere (it is zero at the used index)
  step-below : ∀ {I : Set₁} {f g : I → Cut} {i : I} → (∀ j → (i ≡ j → ⊥) → g j ⊑ f j) → g i ⊑ zeroC →
    ∀ j → g j ⊑ f j
  step-below {f = f} {g} {i} ex gz j with dec≡ i j
  ... | yes refl = ⊑-trans gz 0-least
  ... | no ne = ex j ne

  killP-pt : ∀ {I : Set₁} (P : I → Set₁) {f f′ : I → Cut} {j} →
    ((P j → ⊥) → f j ⊑ f′ j) → killP P f j ⊑ killP P f′ j
  killP-pt P {f} {f′} {j} h with lem₁ (P j)
  ... | inj₁ _ = ⊑-refl
  ... | inj₂ np = h np

  killP-mono-off : ∀ {I : Set₁} (P : I → Set₁) {f f′ : I → Cut} → (∀ j → (P j → ⊥) → f j ⊑ f′ j) →
    ∀ j → killP P f j ⊑ killP P f′ j
  killP-mono-off P h j = killP-pt P (h j)

  -- peel one index off a sum: Σ g = (a ∈ g i₀) + (the rest, with i₀ killed)
  split1 : ∀ {I : Set₁} {g : I → Cut} {q} → Mem g q → ∀ (i₀ : I) →
    Σ ℚᵘ (λ a → Σ ℚᵘ (λ b → mem (g i₀) a × Mem (killP (λ j → i₀ ≡ j) g) b × q ≤ a + b))
  split1 {g = g} (m-neg lt) i₀ =
    let a , b , a<0 , b<0 , le = split-neg lt in a , b , neg (g i₀) a<0 , m-neg b<0 , le
  split1 {g = g} (m-step {q′ = q′} i r g′ mr ex gz mg le) i₀ with dec≡ i₀ i
  ... | yes refl =
    let a , b , ma , mb , le′ = split1 mg i₀
        a<0 = ap gz a ma
    in r , b , mr
       , Mem-mono (killP-mono-off (λ j → i₀ ≡ j) (λ j np → ex j (λ e → np e))) mb
       , ≤-trans le (≤-trans (+-mono-≤ (≤-refl {r}) le′) (+-mono-≤ (≤-refl {r}) (add-neg-le′ a<0)))
  ... | no ne =
    let a , b , ma , mb , le′ = split1 mg i₀
    in a , r + b
       , ap (ex i₀ (λ e → ne (sym e))) a ma
       , m-step i r (killP (λ j → i₀ ≡ j) g′) (ap (killP-off (λ j → i₀ ≡ j) g ne) r mr)
           (λ j ne′ → killP-pt (λ j → i₀ ≡ j) (λ _ → ex j ne′)) (⊑-trans (killP-⊑ (λ j → i₀ ≡ j) g′ i) gz) mb ≤-refl
       , ≤-trans le (≤-trans (+-mono-≤ (≤-refl {r}) le′)
           (≤-≃ (solve 3 (λ r a b → r :+ (a :+ b) := a :+ (r :+ b)) ≃-refl r a b)))

  Mem-single : ∀ {I : Set₁} {f : I → Cut} {i s} → mem (f i) s → Mem f s
  Mem-single {f = f} {i} {s} ms =
    let s′ , s<s′ , ms′ = open′ (f i) ms
    in m-step i s′ (killP (λ j → i ≡ j) f) ms′ (λ j _ → killP-⊑ (λ j → i ≡ j) f j)
         (killP-on (λ j → i ≡ j) f refl) (m-neg (neg-diff s<s′)) (≤-≃ (≃-sym (add-sub s′ s)))

  ----------------------------------------------------------------------------
  -- multiplication distributes over sums

  private
    neg-mul : ∀ {r s} → 0ℚᵘ < r → s < 0ℚᵘ → r * s < 0ℚᵘ
    neg-mul {r} 0<r s<0 = ≃-<ʳ (P.*-zeroʳ r) (*-mono-<-pos 0<r s<0)

    pos-add : ∀ {a b} → 0ℚᵘ < a → 0ℚᵘ < b → 0ℚᵘ < a + b
    pos-add 0<a 0<b = ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<a 0<b)

    neg-add : ∀ {a b} → a < 0ℚᵘ → b < 0ℚᵘ → a + b < 0ℚᵘ
    neg-add a<0 b<0 = ≃-<ʳ (+-identityˡ 0ℚᵘ) (+-mono-< a<0 b<0)

    ⊗-zeroʳ : ∀ x → x ⊗ zeroC ⊑ zeroC
    ⊗-zeroʳ x = ⊑-trans (proj₁ (⊗-comm x zeroC)) (proj₁ (⊗-zeroˡ x))

  module Dist (x : Cut) where

    dist1 : ∀ {I : Set₁} {f : I → Cut} {s} → Mem f s → ∀ {r} → 0ℚᵘ < r → mem x r →
      Mem (λ i → x ⊗ f i) (r * s)
    dist1 (m-neg lt) 0<r mr = m-neg (neg-mul 0<r lt)
    dist1 {f = f} (m-step {q = s} {q′ = q′} i ρ g mρ ex gz mg le) {r} 0<r mr with pos-or-nonpos ρ
    ... | inj₁ 0<ρ =
      m-step i (r * ρ) (λ j → x ⊗ g j) (inj₂ (r , ρ , 0<r , 0<ρ , mr , mρ , ≤-refl))
        (λ j ne → ⊗-mono ⊑-refl (ex j ne)) (⊑-trans (⊗-mono ⊑-refl gz) (⊗-zeroʳ x))
        (dist1 mg 0<r mr)
        (≤-trans (*-mono-≤-nn (<-≤ 0<r) le) (≤-≃ (*-distribˡ-+ r ρ q′)))
    ... | inj₂ ρ≤0 =
      Mem-down (*-mono-≤-nn (<-≤ 0<r) (≤-trans le (≤-trans (+-mono-≤ ρ≤0 (≤-refl {q′})) (≤-≃ (+-identityˡ q′)))))
        (Mem-mono (λ j → ⊗-mono ⊑-refl (step-below ex gz j)) (dist1 mg 0<r mr))

    -- the witnesses for `q` in `x ⊗ f`: `q` is negative, or `q ≤ R * σ` with `R` in `x` and `σ` in `f`
    DW : ∀ {I : Set₁} → (I → Cut) → ℚᵘ → Set₁
    DW f q = q < 0ℚᵘ ⊎ Σ ℚᵘ (λ R → Σ ℚᵘ (λ σ → 0ℚᵘ < R × mem x R × 0ℚᵘ < σ × Mem f σ × q ≤ R * σ))

    -- one step of `dist2`: combine the witness for the rest (coordinate `i` killed) with the one for `x ⊗ f i`
    dist2-go : ∀ {I : Set₁} (f : I → Cut) (i : I) {q q′ ρ : ℚᵘ} → q ≤ ρ + q′ →
      DW (killP (λ j → i ≡ j) f) q′ → mem (x ⊗ f i) ρ → DW f q
    dist2-go f i le (inj₁ q′<0) (inj₁ ρ<0) = inj₁ (≤-<-trans le (neg-add ρ<0 q′<0))
    dist2-go f i le (inj₂ (R , σ , 0<R , mR , 0<σ , mσ , le′)) (inj₁ ρ<0) =
      inj₂ (R , σ , 0<R , mR , 0<σ , Mem-mono (killP-⊑ (λ j → i ≡ j) f) mσ , ≤-trans le (≤-trans (add-neg-le′ ρ<0) le′))
    dist2-go f i le (inj₁ q′<0) (inj₂ (r₁ , s₁ , 0<r₁ , 0<s₁ , mr₁ , ms₁ , le₁)) =
      inj₂ (r₁ , s₁ , 0<r₁ , mr₁ , 0<s₁ , Mem-single ms₁ , ≤-trans le (≤-trans (add-neg-le q′<0) le₁))
    dist2-go f i le (inj₂ (R , σ , 0<R , mR , 0<σ , mσ , le′)) (inj₂ (r₁ , s₁ , 0<r₁ , 0<s₁ , mr₁ , ms₁ , le₁)) with total r₁ R
    ... | inj₁ r₁≤R =
      inj₂ (R , s₁ + σ , 0<R , mR , pos-add 0<s₁ 0<σ
           , m-step i s₁ (killP (λ j → i ≡ j) f) ms₁ (λ j _ → killP-⊑ (λ j → i ≡ j) f j) (killP-on (λ j → i ≡ j) f refl) mσ ≤-refl
           , ≤-trans le (≤-trans (+-mono-≤ le₁ le′)
               (≤-trans (+-mono-≤ (*-mono-≤-nnʳ (<-≤ 0<s₁) r₁≤R) (≤-refl {R * σ}))
                        (≤-≃ (≃-sym (*-distribˡ-+ R s₁ σ))))))
    ... | inj₂ R≤r₁ =
      inj₂ (r₁ , s₁ + σ , 0<r₁ , mr₁ , pos-add 0<s₁ 0<σ
           , m-step i s₁ (killP (λ j → i ≡ j) f) ms₁ (λ j _ → killP-⊑ (λ j → i ≡ j) f j) (killP-on (λ j → i ≡ j) f refl) mσ ≤-refl
           , ≤-trans le (≤-trans (+-mono-≤ le₁ le′)
               (≤-trans (+-mono-≤ (≤-refl {r₁ * s₁}) (*-mono-≤-nnʳ (<-≤ 0<σ) R≤r₁))
                        (≤-≃ (≃-sym (*-distribˡ-+ r₁ s₁ σ))))))

    dist2 : ∀ {I : Set₁} {h f : I → Cut} {q} → (∀ i → h i ⊑ x ⊗ f i) → Mem h q →
      DW f q
    dist2 H (m-neg lt) = inj₁ lt
    dist2 {f = f} H (m-step {q = q} {q′ = q′} i ρ g mρ ex gz mg le) =
      dist2-go f i le (dist2 H′ mg) (ap (H i) ρ mρ)
      where
        P : _ → Set₁
        P = λ j → i ≡ j
        f′ = killP P f
        H′ : ∀ j → g j ⊑ x ⊗ f′ j
        H′ j with dec≡ i j
        ... | yes refl = ⊑-trans gz 0-least
        ... | no ne = ⊑-trans (ex j ne) (⊑-trans (H j) (⊗-mono ⊑-refl (killP-off P f ne)))

  -- ∑ is homogeneous
  sum-distribˡ : ∀ {I : Set₁} (x : Cut) (f : I → Cut) → x ⊗ sumC f ≋ sumC (λ i → x ⊗ f i)
  sum-distribˡ x f = fwd , bwd
    where
      open Dist x
      fwd : x ⊗ sumC f ⊑ sumC (λ i → x ⊗ f i)
      fwd = mk⊑ (λ { q (inj₁ lt) → Mem⇒sum (m-neg lt)
                   ; q (inj₂ (r , s , 0<r , 0<s , mr , ms , le)) → Mem⇒sum (Mem-down le (dist1 (sum⇒Mem ms) 0<r mr)) })
      bwd : sumC (λ i → x ⊗ f i) ⊑ x ⊗ sumC f
      bwd = mk⊑ (λ q d → go (dist2 (λ i → ⊑-refl) (sum⇒Mem d)))
        where
          go : ∀ {q} → DW f q → mem (x ⊗ sumC f) q
          go (inj₁ lt) = inj₁ lt
          go (inj₂ (R , σ , 0<R , mx , 0<σ , mσ , le)) = inj₂ (R , σ , 0<R , 0<σ , mx , Mem⇒sum mσ , le)

  ----------------------------------------------------------------------------
  -- partition associativity: the sum over Σ I J is the iterated sum

  -- replace the entry at k₀ of F′ by that of F
  repl : ∀ {K : Set₁} (F F′ : K → Cut) (k₀ : K) → K → Cut
  repl F F′ k₀ k with dec≡ k k₀
  ... | yes _ = F k
  ... | no _ = F′ k

  repl-off : ∀ {K : Set₁} (F F′ : K → Cut) {k₀ k} → (k ≡ k₀ → ⊥) → F′ k ⊑ repl F F′ k₀ k
  repl-off F F′ {k₀} {k} ne with dec≡ k k₀
  ... | yes e = ⊥-elim (ne e)
  ... | no _ = ⊑-refl

  repl-below : ∀ {K : Set₁} {F F′ : K → Cut} {k₀} → (∀ k → F′ k ⊑ F k) → ∀ k → repl F F′ k₀ k ⊑ F k
  repl-below {F = F} {F′} {k₀} h k with dec≡ k k₀
  ... | yes _ = ⊑-refl
  ... | no _ = h k

  repl-on : ∀ {K : Set₁} (F F′ : K → Cut) {k₀ k} → k ≡ k₀ → F k ⊑ repl F F′ k₀ k
  repl-on F F′ {k₀} {k} e with dec≡ k k₀
  ... | yes _ = ⊑-refl
  ... | no ne = ⊥-elim (ne e)

  repl-at : ∀ {K : Set₁} (F F′ : K → Cut) {k₀ k} → (k ≡ k₀ → ⊥) → repl F F′ k₀ k ⊑ F′ k
  repl-at F F′ {k₀} {k} ne with dec≡ k k₀
  ... | yes e = ⊥-elim (ne e)
  ... | no _ = ⊑-refl

  module SigmaSum {I : Set₁} {J : I → Set₁} where

    -- add the sum over a row to the sum over the rest
    row-add : ∀ {i₀ : I} {H : J i₀ → Cut} {ρ} → Mem H ρ →
      ∀ (F F′ : Σ I J → Cut) {q′} → (∀ j → H j ⊑ F (i₀ , j)) → (∀ k → F′ k ⊑ F k) →
      (∀ j → (F′ (i₀ , j) ⊑ zeroC) ⊎ (H j ⊑ zeroC)) → Mem F′ q′ → Mem F (ρ + q′)
    row-add (m-neg lt) F F′ hH hF dj mF′ = Mem-down (add-neg-le′ lt) (Mem-mono hF mF′)
    row-add {i₀} {H} (m-step {q = ρ} {q′ = ρ′} j r H′ mr ex gz mH′ le) F F′ {q′} hH hF dj mF′ with dj j
    ... | inj₂ Hj≤0 =
      Mem-down (≤-trans (+-mono-≤ le (≤-refl {q′})) (≤-trans (+-mono-≤ (≤-trans (+-mono-≤ (<-≤ r<0) (≤-refl {ρ′})) (≤-≃ (+-identityˡ ρ′))) (≤-refl {q′})) (≤-refl {ρ′ + q′})))
        (row-add mH′ F F′ hH′ hF dj′ mF′)
      where
        r<0 : r < 0ℚᵘ
        r<0 = ap Hj≤0 r mr
        hH′ : ∀ j′ → H′ j′ ⊑ F (i₀ , j′)
        hH′ j′ = ⊑-trans (step-below ex gz j′) (hH j′)
        dj′ : ∀ j′ → (F′ (i₀ , j′) ⊑ zeroC) ⊎ (H′ j′ ⊑ zeroC)
        dj′ j′ with dj j′
        ... | inj₁ z = inj₁ z
        ... | inj₂ z = inj₂ (⊑-trans (step-below ex gz j′) z)
    ... | inj₁ F′j≤0 =
      Mem-down (≤-trans (+-mono-≤ le (≤-refl {q′})) (≤-≃ (solve 3 (λ r ρ′ q′ → (r :+ ρ′) :+ q′ := ρ′ :+ (r :+ q′)) ≃-refl r ρ′ q′)))
        (row-add mH′ F F″ hH′ (repl-below hF) dj″ mF″)
      where
        k₀ = i₀ , j
        F″ = repl F F′ k₀
        hH′ : ∀ j′ → H′ j′ ⊑ F (i₀ , j′)
        hH′ j′ = ⊑-trans (step-below ex gz j′) (hH j′)
        mF″ : Mem F″ (r + q′)
        mF″ = m-step k₀ r F′ (ap (repl-on F F′ refl) r (ap (hH j) r mr))
                (λ k ne → repl-off F F′ (λ e → ne (sym e))) (⊑-trans F′j≤0 ⊑-refl) mF′ ≤-refl
        dj″ : ∀ j′ → (F″ (i₀ , j′) ⊑ zeroC) ⊎ (H′ j′ ⊑ zeroC)
        dj″ j′ with dec≡ j′ j
        ... | yes refl = inj₂ gz
        ... | no ne with dj j′
        ...   | inj₁ z = inj₁ (⊑-trans (repl-at F F′ (λ e → ne (ι-inj e))) z)
        ...   | inj₂ z = inj₂ (⊑-trans (ex j′ (λ e → ne (sym e))) z)

    -- from the iterated sum to the sum over the pairs
    nested⇒flat : ∀ {g : I → Cut} {q} → Mem g q → ∀ (F : Σ I J → Cut) →
      (∀ i → g i ⊑ sumC (λ j → F (i , j))) → Mem F q
    nested⇒flat (m-neg lt) F hyp = m-neg lt
    nested⇒flat {g} (m-step {q′ = q′} i ρ g′ mρ ex gz mg le) F hyp =
      Mem-down le
        (row-add (sum⇒Mem (ap (hyp i) ρ mρ)) F F′ (λ j → ⊑-refl) (killP-⊑ P F)
           (λ j → inj₁ (killP-on P F refl)) (nested⇒flat mg F′ hyp′))
      where
        P : Σ I J → Set₁
        P k = i ≡ proj₁ k
        F′ = killP P F
        hyp′ : ∀ k₁ → g′ k₁ ⊑ sumC (λ j → F′ (k₁ , j))
        hyp′ k₁ with dec≡ i k₁
        ... | yes refl = ⊑-trans gz 0-least
        ... | no ne = ⊑-trans (ex k₁ ne) (⊑-trans (hyp k₁) (sum-mono (λ j → killP-off P F (λ p → ne p))))

    -- from the sum over the pairs to the iterated sum
    flat⇒nested : ∀ {F : Σ I J → Cut} {q} → Mem F q → Mem (λ i → sumC (λ j → F (i , j))) q
    flat⇒nested (m-neg lt) = m-neg lt
    flat⇒nested {F} (m-step {q′ = q′} (i₀ , j) r F′ mr ex gz mF′ le) =
      let a , b , ma , mb , le′ = split1 (flat⇒nested mF′) i₀
          mrow : Mem (λ j′ → F (i₀ , j′)) (r + a)
          mrow = m-step j r (λ j′ → F′ (i₀ , j′)) mr (λ j′ ne → ex (i₀ , j′) (λ e → ne (ι-inj e))) gz (sum⇒Mem ma) ≤-refl
      in m-step i₀ (r + a) (killP (λ k → i₀ ≡ k) (λ k₁ → sumC (λ j′ → F′ (k₁ , j′)))) (Mem⇒sum mrow)
           (λ k₁ ne → ⊑-trans (killP-⊑ (λ k → i₀ ≡ k) _ k₁) (sum-mono (λ j′ → ex (k₁ , j′) (λ e → ne (cong proj₁ e)))))
           (killP-on (λ k → i₀ ≡ k) _ refl) mb
           (≤-trans le (≤-trans (+-mono-≤ (≤-refl {r}) le′) (≤-≃ (≃-sym (+-assoc r a b)))))

  sum-Σ : ∀ {I : Set₁} {J : I → Set₁} (f : Σ I J → Cut) →
    sumC f ≋ sumC (λ i → sumC (λ j → f (i , j)))
  sum-Σ {I} {J} f =
    mk⊑ (λ q d → Mem⇒sum (SigmaSum.flat⇒nested (sum⇒Mem d))) ,
    mk⊑ (λ q d → Mem⇒sum (SigmaSum.nested⇒flat (sum⇒Mem d) f (λ i → ⊑-refl)))
