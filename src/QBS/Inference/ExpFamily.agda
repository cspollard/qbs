{-# OPTIONS --safe --without-K #-}

-- Multiplicative exponential families in the discrete model (plan ExpFam, item 57; generalising `Bayesian.Bernoulli`).
-- For parameters θ in Θ with natural parameters θⱼ, normaliser c(θ), base weight h(x), and statistic T(x) : Fin k → ℕ:
--   * `lik1 x θ = h x * (∏ⱼ θⱼ^{Tⱼ(x)} * c(θ))`, the likelihood of a single draw;
--   * `likSeq xs`, product likelihood of independent draws;
--   * `likSeq-factor`: product likelihood factorises through the sufficient statistic sumT xs = Σᵢ T(xᵢ) and length xs;
--   * `kernel (χ, ν) θ = ∏ⱼ θⱼ^{χⱼ} * c(θ)^ν`, the unnormalised natural conjugate prior;
--   * `posterior-update`: updating kernel (χ, ν) with data xs yields kernel (χ + sumT xs, ν + length xs),
--     via `Bayesian.sequential` and `Analysis/ExpFamAlg.ExpFamNat`;
--   * `posterior-sufficient`: datasets with equal (sumT xs, length xs) and equal base weight yield equal posteriors;
--   * `Bernoulli`: recovering `Bayesian.Bernoulli.likSeq-counts` as a 2-parameter exponential family.
-- Route: induction on xs for `likSeq-factor` with `∏-*` and `x^[m+n]`; `posterior-update` by `likSeq-factor` and
-- `sequential`; `Bernoulli` instantiates k = 2 with statistics counting true and false.
module QBS.Inference.ExpFamily where

open import Algebra.Properties.CommutativeSemigroup using (interchange)
import Algebra.Properties.Semiring.Exp as Exp
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
import Data.Nat.Base as Nat
open Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.WeightClasses using (allClass)
open import QBS.Model.Monad
open import QBS.Example.Bayes using (posteriorU; evidence; _·_; bayes-numerator)
open import QBS.Inference.Bayesian using (module Bayesian)
open import QBS.Analysis.ExpFamAlg using (module ExpFamNat)

module ExpFamily {ℓ} (Norm : NormalizableSemiring ℓ) where
  open Bayesian Norm
  open CompleteSemiring A using (_≈_; _+_; _*_; 0#; 1#; +-cong; *-cong; *-assoc; *-comm; *-identityˡ; *-identityʳ;
    distribˡ; distribʳ; refl; sym; trans; *-commutativeSemigroup; semiring; ∑-cong; reflexive) renaming (Carrier to ∣A∣; setoid to Aˢ)
  open MA using (Pre; mk; ∫; _≈ᵖ_)
  open Exp semiring using (_^_)
  open ExpFamNat using (Vecℕ; _+Vℕ_; sumList; Paramℕ; updateList)
  open import Relation.Binary.Reasoning.Setoid Aˢ

  -- products over Fin k
  ∏ : ∀ k → (Fin k → ∣A∣) → ∣A∣
  ∏ zero f = 1#
  ∏ (suc k) f = f zero * ∏ k (λ j → f (suc j))

  ∏-cong : ∀ k {f g : Fin k → ∣A∣} → (∀ j → f j ≈ g j) → ∏ k f ≈ ∏ k g
  ∏-cong zero eq = refl
  ∏-cong (suc k) eq = *-cong (eq zero) (∏-cong k (λ j → eq (suc j)))

  ∏-1 : ∀ k → ∏ k (λ _ → 1#) ≈ 1#
  ∏-1 zero = refl
  ∏-1 (suc k) = trans (*-identityˡ _) (∏-1 k)

  ∏-* : ∀ k (f g : Fin k → ∣A∣) → ∏ k (λ j → f j * g j) ≈ ∏ k f * ∏ k g
  ∏-* zero f g = sym (*-identityˡ 1#)
  ∏-* (suc k) f g = trans (*-cong refl (∏-* k (λ j → f (suc j)) (λ j → g (suc j))))
    (sym (interchange *-commutativeSemigroup (f zero) _ (g zero) _))

  -- power identities
  ^-cong : ∀ x y → x ≈ y → ∀ n → x ^ n ≈ y ^ n
  ^-cong x y eq zero = refl
  ^-cong x y eq (suc n) = *-cong eq (^-cong x y eq n)

  x^[m+n] : ∀ x m n → x ^ (m Nat.+ n) ≈ x ^ m * x ^ n
  x^[m+n] x zero n = sym (*-identityˡ (x ^ n))
  x^[m+n] x (suc m) n = trans (*-cong refl (x^[m+n] x m n)) (sym (*-assoc x _ _))

  ----------------------------------------------------------------------------
  -- Multiplicative exponential family
  module Family {Θ : QBS (discreteSource ℓ)} {X : Set} {k : ℕ}
      (θs : Fin k → Func (QBS.Carrier Θ) Aˢ)
      (c : Func (QBS.Carrier Θ) Aˢ)
      (h : X → ∣A∣)
      (T : X → Vecℕ k) where

    one : Func (QBS.Carrier Θ) Aˢ
    one = record { to = λ _ → 1# ; cong = λ _ → refl }

    powProd : (Fin k → ∣A∣) → Vecℕ k → ∣A∣
    powProd θ n = ∏ k (λ j → θ j ^ n j)

    powProd-* : ∀ θ n m → powProd θ (n +Vℕ m) ≈ powProd θ n * powProd θ m
    powProd-* θ n m = trans
      (∏-cong k (λ j → x^[m+n] (θ j) (n j) (m j)))
      (∏-* k (λ j → θ j ^ n j) (λ j → θ j ^ m j))

    -- unnormalised conjugate kernel
    kernel : Paramℕ k → Func (QBS.Carrier Θ) Aˢ
    kernel (χ , ν) = record
      { to = λ θ → powProd (λ j → θs j ⟨$⟩ θ) χ * (c ⟨$⟩ θ) ^ ν
      ; cong = λ {θ₁} {θ₂} eq → *-cong
          (∏-cong k (λ j → ^-cong (θs j ⟨$⟩ θ₁) (θs j ⟨$⟩ θ₂) (Func.cong (θs j) eq) (χ j)))
          (^-cong (c ⟨$⟩ θ₁) (c ⟨$⟩ θ₂) (Func.cong c eq) ν)
      }

    kernel-* : ∀ p q θ →
      (kernel p ⟨$⟩ θ) * (kernel q ⟨$⟩ θ) ≈ (kernel (proj₁ p +Vℕ proj₁ q , proj₂ p Nat.+ proj₂ q) ⟨$⟩ θ)
    kernel-* (χ₁ , ν₁) (χ₂ , ν₂) θ = trans
      (interchange *-commutativeSemigroup _ _ _ _)
      (*-cong (sym (powProd-* (λ j → θs j ⟨$⟩ θ) χ₁ χ₂)) (sym (x^[m+n] (c ⟨$⟩ θ) ν₁ ν₂)))

    -- single-draw likelihood
    lik1 : X → Func (QBS.Carrier Θ) Aˢ
    lik1 x = record
      { to = λ θ → h x * (kernel (T x , 1) ⟨$⟩ θ)
      ; cong = λ eq → *-cong refl (Func.cong (kernel (T x , 1)) eq)
      }

    -- sequence likelihood
    likSeq : List X → Func (QBS.Carrier Θ) Aˢ
    likSeq [] = one
    likSeq (x ∷ xs) = _·_ Norm {Θ} (lik1 x) (likSeq xs)

    hSeq : List X → ∣A∣
    hSeq [] = 1#
    hSeq (x ∷ xs) = h x * hSeq xs

    sumT : List X → Vecℕ k
    sumT = sumList T

    kernel-0 : ∀ θ → (kernel ((λ _ → 0) , 0) ⟨$⟩ θ) ≈ 1#
    kernel-0 θ = trans (*-cong (∏-1 k) refl) (*-identityˡ 1#)

    -- product likelihood factorisation
    likSeq-factor : ∀ xs θ → (likSeq xs ⟨$⟩ θ) ≈ hSeq xs * (kernel (sumT xs , length xs) ⟨$⟩ θ)
    likSeq-factor [] θ = sym (trans (*-cong refl (kernel-0 θ)) (*-identityˡ 1#))
    likSeq-factor (x ∷ xs) θ = trans (*-cong refl (likSeq-factor xs θ))
      (trans (interchange *-commutativeSemigroup (h x) _ (hSeq xs) _)
        (*-cong refl (kernel-* (T x , 1) (sumT xs , length xs) θ)))

    lik-update : ∀ p xs θ →
      ((kernel p ⟨$⟩ θ) * (likSeq xs ⟨$⟩ θ)) ≈
      (hSeq xs * (kernel (updateList p T xs) ⟨$⟩ θ))
    lik-update p xs θ = trans (*-cong refl (likSeq-factor xs θ))
      (trans (*-comm (kernel p ⟨$⟩ θ) _)
        (trans (*-assoc (hSeq xs) _ _)
          (*-cong refl (trans (*-comm _ _) (kernel-* p (sumT xs , length xs) θ)))))

    lik-cong : ∀ (prior : Pre Θ) (w₁ w₂ : Func (QBS.Carrier Θ) Aˢ) →
      (∀ θ → (w₁ ⟨$⟩ θ) ≈ (w₂ ⟨$⟩ θ)) → posteriorU Norm prior w₁ ≈ᵖ posteriorU Norm prior w₂
    lik-cong prior w₁ w₂ same f = trans (bayes-numerator Norm prior w₁ f)
      (trans (∑-cong (λ r → *-cong refl (*-cong (same (MA.α prior r)) refl)))
        (sym (bayes-numerator Norm prior w₂ f)))

    -- posterior update
    posterior-update : ∀ (prior : Pre Θ) (p : Paramℕ k) xs →
      posteriorU Norm (posteriorU Norm prior (kernel p)) (likSeq xs) ≈ᵖ
      posteriorU Norm prior (_·_ Norm {Θ} (record { to = λ _ → hSeq xs ; cong = λ _ → refl })
                                          (kernel (updateList p T xs)))
    posterior-update prior p xs f = trans (sequential prior (kernel p) (likSeq xs) f)
      (lik-cong prior (_·_ Norm {Θ} (kernel p) (likSeq xs))
                      (_·_ Norm {Θ} (record { to = λ _ → hSeq xs ; cong = λ _ → refl })
                                    (kernel (updateList p T xs)))
                      (lik-update p xs) f)

    -- Bayesian sufficiency: equal sufficient statistics and equal base weight give equal posteriors
    posterior-sufficient : ∀ (prior : Pre Θ) xs ys →
      (∀ j → sumT xs j ≡ sumT ys j) → length xs ≡ length ys →
      hSeq xs ≈ hSeq ys →
      posteriorU Norm prior (likSeq xs) ≈ᵖ posteriorU Norm prior (likSeq ys)
    posterior-sufficient prior xs ys hT hlen hh = lik-cong prior (likSeq xs) (likSeq ys) same
      where
        same : ∀ θ → (likSeq xs ⟨$⟩ θ) ≈ (likSeq ys ⟨$⟩ θ)
        same θ = trans (likSeq-factor xs θ)
          (trans (*-cong hh (*-cong (∏-cong k (λ j → reflexive (≡.cong (λ n → (θs j ⟨$⟩ θ) ^ n) (hT j))))
                                   (reflexive (≡.cong (λ n → (c ⟨$⟩ θ) ^ n) hlen))))
            (sym (likSeq-factor ys θ)))

  ----------------------------------------------------------------------------
  -- Bernoulli as an instance
  module BernoulliInstance {Θ : QBS (discreteSource ℓ)}
      (p q : Func (QBS.Carrier Θ) Aˢ)
      (pq : ∀ θ → (p ⟨$⟩ θ) + (q ⟨$⟩ θ) ≈ 1#) where

    θBernoulli : Fin 2 → Func (QBS.Carrier Θ) Aˢ
    θBernoulli zero = p
    θBernoulli (suc zero) = q

    TBernoulli : Bool → Vecℕ 2
    TBernoulli true zero = 1
    TBernoulli true (suc zero) = 0
    TBernoulli false zero = 0
    TBernoulli false (suc zero) = 1

    open Family {Θ = Θ} θBernoulli (record { to = λ _ → 1# ; cong = λ _ → refl }) (λ _ → 1#) TBernoulli public

    open Bayesian.Bernoulli Norm {Θ = Θ} p q pq using (successes; failures)

    sumT-successes : ∀ xs → sumT xs zero ≡ successes xs
    sumT-successes [] = ≡.refl
    sumT-successes (true ∷ xs) = ≡.cong suc (sumT-successes xs)
    sumT-successes (false ∷ xs) = sumT-successes xs

    sumT-failures : ∀ xs → sumT xs (suc zero) ≡ failures xs
    sumT-failures [] = ≡.refl
    sumT-failures (true ∷ xs) = sumT-failures xs
    sumT-failures (false ∷ xs) = ≡.cong suc (sumT-failures xs)

    hSeq-1 : ∀ xs → hSeq xs ≈ 1#
    hSeq-1 [] = refl
    hSeq-1 (x ∷ xs) = trans (*-identityˡ _) (hSeq-1 xs)

    1^n : ∀ n → 1# ^ n ≈ 1#
    1^n zero = refl
    1^n (suc n) = trans (*-identityˡ _) (1^n n)

    powProd-Bernoulli : ∀ xs θ →
      powProd (λ j → θBernoulli j ⟨$⟩ θ) (sumT xs) ≈
      (p ⟨$⟩ θ) ^ successes xs * (q ⟨$⟩ θ) ^ failures xs
    powProd-Bernoulli xs θ = trans
      (*-cong (reflexive (≡.cong (λ s → (p ⟨$⟩ θ) ^ s) (sumT-successes xs)))
        (*-cong (reflexive (≡.cong (λ f → (q ⟨$⟩ θ) ^ f) (sumT-failures xs))) refl))
      (*-cong refl (*-identityʳ _))

    likSeq-recovers-counts : ∀ xs θ → (likSeq xs ⟨$⟩ θ) ≈ (p ⟨$⟩ θ) ^ successes xs * (q ⟨$⟩ θ) ^ failures xs
    likSeq-recovers-counts xs θ = begin
      likSeq xs ⟨$⟩ θ
        ≈⟨ likSeq-factor xs θ ⟩
      hSeq xs * (powProd (λ j → θBernoulli j ⟨$⟩ θ) (sumT xs) * 1# ^ length xs)
        ≈⟨ *-cong (hSeq-1 xs) (*-cong (powProd-Bernoulli xs θ) (1^n (length xs))) ⟩
      1# * ((p ⟨$⟩ θ) ^ successes xs * (q ⟨$⟩ θ) ^ failures xs * 1#)
        ≈⟨ trans (*-identityˡ _) (*-identityʳ _) ⟩
      (p ⟨$⟩ θ) ^ successes xs * (q ⟨$⟩ θ) ^ failures xs ∎
