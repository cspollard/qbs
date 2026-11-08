{-# OPTIONS --safe --without-K #-}

-- Conjugacy for multiplicative exponential families in the discrete model, generalising `Bayesian.Bernoulli`
-- (plan 07 item 57 in `plans/`).
-- For parameters θ in Θ with natural parameters θⱼ, normaliser c(θ), base weight h(x), and statistic T(x) : Fin k → ℕ:
--   * `lik1 x θ = h x * (∏ⱼ θⱼ^{Tⱼ(x)} * c(θ))`, the likelihood of a single draw;
--   * `likSeq xs`, product likelihood of independent draws;
--   * `likSeq-factor`: product likelihood factorises through the sufficient statistic sumT xs = Σᵢ T(xᵢ) and length xs,
--     with the constant factor `hSeq xs = ∏ᵢ h(xᵢ)`;
--   * `kernel (χ, ν) θ = ∏ⱼ θⱼ^{χⱼ} * c(θ)^ν`, the unnormalised natural conjugate prior;
--   * `posterior-update`: updating kernel (χ, ν) with data xs yields kernel (χ + sumT xs, ν + length xs), up to the
--     constant factor `hSeq xs` (unnormalised posteriors, `Example/Bayes.posteriorU`);
--   * `posterior-sufficient`: datasets with equal (sumT xs, length xs) and equal base weight yield equal unnormalised
--     posteriors;
--   * `posterior-update-norm`, `posterior-sufficient-norm`: the normalised posteriors (`Example/Bayes.posterior`, any
--     inverses of the evidences): after xs the posterior of the conjugate prior at p is the normalised conjugate
--     posterior at `updateList p T xs`, and equal (sumT, length) alone give equal posteriors (the constant cancels);
--   * `Bernoulli`: recovering `Bayesian.Bernoulli.likSeq-counts` as a 2-parameter exponential family.
-- Route: induction on xs for `likSeq-factor` with `∏-*` and `x^[m+n]`; `posterior-update` by `likSeq-factor` and
-- `sequential`; the normalised forms by `posterior-prop` (normalised posteriors of weights proportional to a common
-- one agree), from `Example/Bayes.bayes`, `∫-factor` and uniqueness of inverses (`inv-unique`: x n ≈ 1 ≈ x m ⇒ n ≈ m);
-- `Bernoulli` instantiates k = 2 with statistics counting true and false.
module QBS.Inference.ExpFamily where

open import Algebra.Properties.CommutativeSemigroup using (interchange)
import Algebra.Properties.Semiring.Exp as Exp
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
import Data.Nat.Base as Nat
open Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.Semiring
open import QBS.Model.Sums using (module Sums)
open import QBS.Model.WeightClasses using (probClass)
open import QBS.Model.Monad
open import QBS.Example.Bayes using (posteriorU; posterior; evidence; _·_; bayes-numerator; bayes)
open import QBS.Inference.Bayesian using (module Bayesian)
open import QBS.Analysis.ExpFamAlg using (module ExpFamNat)

module ExpFamily {ℓ} (Norm : NormalizableSemiring ℓ) where
  open Bayesian Norm
  open CompleteSemiring A using (_≈_; _+_; _*_; 1#; *-cong; *-assoc; *-comm; *-identityˡ; *-identityʳ;
    refl; sym; trans; *-commutativeSemigroup; semiring; ∑; ∑-cong; reflexive) renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A using (∑-scale)
  open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup using (x∙yz≈y∙xz; xy∙z≈y∙xz)
  open MA using (Pre; _≈ᵖ_)
  module MP = Measures A (probClass A)
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

    -- constant functions on Θ
    constF : ∣A∣ → Func (QBS.Carrier Θ) Aˢ
    constF a = record { to = λ _ → a ; cong = λ _ → refl }

    one : Func (QBS.Carrier Θ) Aˢ
    one = constF 1#

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
    likSeq-factor (x ∷ xs) θ = begin
      h x * (kernel (T x , 1) ⟨$⟩ θ) * (likSeq xs ⟨$⟩ θ)
        ≈⟨ *-cong refl (likSeq-factor xs θ) ⟩
      h x * (kernel (T x , 1) ⟨$⟩ θ) * (hSeq xs * (kernel q ⟨$⟩ θ))
        ≈⟨ interchange *-commutativeSemigroup (h x) _ (hSeq xs) _ ⟩
      hSeq (x ∷ xs) * ((kernel (T x , 1) ⟨$⟩ θ) * (kernel q ⟨$⟩ θ))
        ≈⟨ *-cong refl (kernel-* (T x , 1) q θ) ⟩
      hSeq (x ∷ xs) * (kernel (sumT (x ∷ xs) , length (x ∷ xs)) ⟨$⟩ θ) ∎
      where
        q : Paramℕ k
        q = (sumT xs , length xs)

    lik-update : ∀ p xs θ →
      ((kernel p ⟨$⟩ θ) * (likSeq xs ⟨$⟩ θ)) ≈
      (hSeq xs * (kernel (updateList p T xs) ⟨$⟩ θ))
    lik-update p xs θ = begin
      (kernel p ⟨$⟩ θ) * (likSeq xs ⟨$⟩ θ)          ≈⟨ *-cong refl (likSeq-factor xs θ) ⟩
      (kernel p ⟨$⟩ θ) * (hSeq xs * (kernel q ⟨$⟩ θ))  ≈⟨ *-comm (kernel p ⟨$⟩ θ) _ ⟩
      (hSeq xs * (kernel q ⟨$⟩ θ)) * (kernel p ⟨$⟩ θ)  ≈⟨ *-assoc (hSeq xs) _ _ ⟩
      hSeq xs * ((kernel q ⟨$⟩ θ) * (kernel p ⟨$⟩ θ))  ≈⟨ *-cong refl (*-comm _ _) ⟩
      hSeq xs * ((kernel p ⟨$⟩ θ) * (kernel q ⟨$⟩ θ))  ≈⟨ *-cong refl (kernel-* p q θ) ⟩
      hSeq xs * (kernel (updateList p T xs) ⟨$⟩ θ)     ∎
      where
        q : Paramℕ k
        q = (sumT xs , length xs)

    lik-cong : ∀ (prior : Pre Θ) (w₁ w₂ : Func (QBS.Carrier Θ) Aˢ) →
      (∀ θ → (w₁ ⟨$⟩ θ) ≈ (w₂ ⟨$⟩ θ)) → posteriorU Norm prior w₁ ≈ᵖ posteriorU Norm prior w₂
    lik-cong prior w₁ w₂ same f = begin
      MA.∫ (posteriorU Norm prior w₁) f  ≈⟨ bayes-numerator Norm prior w₁ f ⟩
      MA.∫ prior (_·_ Norm {Θ} w₁ f)     ≈⟨ ∑-cong (λ r → *-cong refl (*-cong (same (MA.α prior r)) refl)) ⟩
      MA.∫ prior (_·_ Norm {Θ} w₂ f)     ≈⟨ sym (bayes-numerator Norm prior w₂ f) ⟩
      MA.∫ (posteriorU Norm prior w₂) f  ∎

    -- the integral of a weight proportional to another
    ∫-factor : ∀ (prior : Pre Θ) (a : ∣A∣) (w v : Func (QBS.Carrier Θ) Aˢ) → (∀ θ → (w ⟨$⟩ θ) ≈ a * (v ⟨$⟩ θ)) →
      MA.∫ prior w ≈ a * MA.∫ prior v
    ∫-factor prior a w v hw = begin
      MA.∫ prior w                                             ≈⟨ ∑-cong (λ r → *-cong refl (hw (MA.α prior r))) ⟩
      ∑ (λ r → MA.Pre.μ prior r * (a * (v ⟨$⟩ MA.α prior r))) ≈⟨ ∑-cong (λ r → x∙yz≈y∙xz _ a _) ⟩
      ∑ (λ r → a * (MA.Pre.μ prior r * (v ⟨$⟩ MA.α prior r))) ≈⟨ ∑-scale a _ ⟩
      a * MA.∫ prior v                                         ∎

    -- uniqueness of inverses, and moving a factor of the evidence onto the normaliser
    inv-unique : ∀ {x a b} → x * a ≈ 1# → x * b ≈ 1# → a ≈ b
    inv-unique {x} {a} {b} ha hb = begin
      a            ≈⟨ sym (*-identityˡ a) ⟩
      1# * a       ≈⟨ *-cong (sym hb) refl ⟩
      (x * b) * a  ≈⟨ xy∙z≈y∙xz x b a ⟩
      b * (x * a)  ≈⟨ *-cong refl ha ⟩
      b * 1#       ≈⟨ *-identityʳ b ⟩
      b            ∎

    inv-shift : ∀ {a E E′ n} → E′ ≈ a * E → E′ * n ≈ 1# → E * (a * n) ≈ 1#
    inv-shift {a} {E} {E′} {n} he h = begin
      E * (a * n)  ≈⟨ sym (xy∙z≈y∙xz a E n) ⟩
      (a * E) * n  ≈⟨ *-cong (sym he) refl ⟩
      E′ * n       ≈⟨ h ⟩
      1#           ∎

    -- kernels at equal parameters
    kernel-≡ : ∀ {χ₁ χ₂ : Vecℕ k} {ν₁ ν₂ : ℕ} → (∀ j → χ₁ j ≡ χ₂ j) → ν₁ ≡ ν₂ → ∀ θ →
      (kernel (χ₁ , ν₁) ⟨$⟩ θ) ≈ (kernel (χ₂ , ν₂) ⟨$⟩ θ)
    kernel-≡ hχ hν θ = *-cong (∏-cong k (λ j → reflexive (≡.cong (λ n → (θs j ⟨$⟩ θ) ^ n) (hχ j))))
                              (reflexive (≡.cong (λ n → (c ⟨$⟩ θ) ^ n) hν))

    -- posterior update (unnormalised): the constant factor hSeq xs remains
    posterior-update : ∀ (prior : Pre Θ) (p : Paramℕ k) xs →
      posteriorU Norm (posteriorU Norm prior (kernel p)) (likSeq xs) ≈ᵖ
      posteriorU Norm prior (_·_ Norm {Θ} (constF (hSeq xs)) (kernel (updateList p T xs)))
    posterior-update prior p xs f = trans (sequential prior (kernel p) (likSeq xs) f)
      (lik-cong prior (_·_ Norm {Θ} (kernel p) (likSeq xs))
                      (_·_ Norm {Θ} (constF (hSeq xs)) (kernel (updateList p T xs)))
                      (lik-update p xs) f)

    -- equal sufficient statistics give proportional likelihoods
    likSeq-stat : ∀ xs ys → (∀ j → sumT xs j ≡ sumT ys j) → length xs ≡ length ys → ∀ θ →
      hSeq ys * (likSeq xs ⟨$⟩ θ) ≈ hSeq xs * (likSeq ys ⟨$⟩ θ)
    likSeq-stat xs ys hT hlen θ = begin
      hSeq ys * (likSeq xs ⟨$⟩ θ)                                ≈⟨ *-cong refl (likSeq-factor xs θ) ⟩
      hSeq ys * (hSeq xs * (kernel (sumT xs , length xs) ⟨$⟩ θ)) ≈⟨ x∙yz≈y∙xz (hSeq ys) (hSeq xs) _ ⟩
      hSeq xs * (hSeq ys * (kernel (sumT xs , length xs) ⟨$⟩ θ))
        ≈⟨ *-cong refl (*-cong refl (kernel-≡ hT hlen θ)) ⟩
      hSeq xs * (hSeq ys * (kernel (sumT ys , length ys) ⟨$⟩ θ)) ≈⟨ *-cong refl (sym (likSeq-factor ys θ)) ⟩
      hSeq xs * (likSeq ys ⟨$⟩ θ)                                ∎

    -- Bayesian sufficiency (unnormalised): equal sufficient statistics and equal base weight give equal posteriors
    posterior-sufficient : ∀ (prior : Pre Θ) xs ys →
      (∀ j → sumT xs j ≡ sumT ys j) → length xs ≡ length ys →
      hSeq xs ≈ hSeq ys →
      posteriorU Norm prior (likSeq xs) ≈ᵖ posteriorU Norm prior (likSeq ys)
    posterior-sufficient prior xs ys hT hlen hh = lik-cong prior (likSeq xs) (likSeq ys) same
      where
        same : ∀ θ → (likSeq xs ⟨$⟩ θ) ≈ (likSeq ys ⟨$⟩ θ)
        same θ = begin
          likSeq xs ⟨$⟩ θ                                  ≈⟨ likSeq-factor xs θ ⟩
          hSeq xs * (kernel (sumT xs , length xs) ⟨$⟩ θ)  ≈⟨ *-cong hh (kernel-≡ hT hlen θ) ⟩
          hSeq ys * (kernel (sumT ys , length ys) ⟨$⟩ θ)  ≈⟨ sym (likSeq-factor ys θ) ⟩
          likSeq ys ⟨$⟩ θ                                  ∎

    -- a weight proportional to another, times a test
    ·-factor : ∀ (z u f : Func (QBS.Carrier Θ) Aˢ) {c} → (∀ θ → (z ⟨$⟩ θ) ≈ c * (u ⟨$⟩ θ)) →
      ∀ θ → (_·_ Norm {Θ} z f ⟨$⟩ θ) ≈ c * (_·_ Norm {Θ} u f ⟨$⟩ θ)
    ·-factor z u f h θ = trans (*-cong (h θ) refl) (*-assoc _ _ _)

    -- normalisers of weights proportional to a common one: a n ≈ b m
    norm-ratio : ∀ (prior : Pre Θ) (w v u : Func (QBS.Carrier Θ) Aˢ) {a b n m : ∣A∣} →
      (∀ θ → (w ⟨$⟩ θ) ≈ a * (u ⟨$⟩ θ)) → (∀ θ → (v ⟨$⟩ θ) ≈ b * (u ⟨$⟩ θ)) →
      evidence Norm prior w * n ≈ 1# → evidence Norm prior v * m ≈ 1# → a * n ≈ b * m
    norm-ratio prior w v u {a} {b} hw hv hn hm =
      inv-unique (inv-shift (∫-factor prior a w u hw) hn) (inv-shift (∫-factor prior b v u hv) hm)

    -- normalised posteriors of weights proportional to a common one agree, for any normalisers
    posterior-prop : ∀ (prior : Pre Θ) (w v u : Func (QBS.Carrier Θ) Aˢ) (a b n m : ∣A∣) →
      (∀ θ → (w ⟨$⟩ θ) ≈ a * (u ⟨$⟩ θ)) → (∀ θ → (v ⟨$⟩ θ) ≈ b * (u ⟨$⟩ θ)) →
      (hn : evidence Norm prior w * n ≈ 1#) (hm : evidence Norm prior v * m ≈ 1#) →
      MP._≈ᵖ_ (posterior Norm prior w n hn) (posterior Norm prior v m hm)
    posterior-prop prior w v u a b n m hw hv hn hm f = begin
      MP.∫ (posterior Norm prior w n hn) f ≈⟨ bayes Norm prior w f n hn ⟩
      n * MA.∫ prior wf ≈⟨ *-cong refl (∫-factor prior a wf uf (·-factor w u f hw)) ⟩
      n * (a * MA.∫ prior uf) ≈⟨ sym (xy∙z≈y∙xz a n _) ⟩
      (a * n) * MA.∫ prior uf ≈⟨ *-cong (norm-ratio prior w v u hw hv hn hm) refl ⟩
      (b * m) * MA.∫ prior uf ≈⟨ xy∙z≈y∙xz b m _ ⟩
      m * (b * MA.∫ prior uf) ≈⟨ *-cong refl (sym (∫-factor prior b vf uf (·-factor v u f hv))) ⟩
      m * MA.∫ prior vf ≈⟨ sym (bayes Norm prior v f m hm) ⟩
      MP.∫ (posterior Norm prior v m hm) f ∎
      where uf = _·_ Norm {Θ} u f
            wf = _·_ Norm {Θ} w f
            vf = _·_ Norm {Θ} v f

    -- the normalised posterior of an unnormalised posterior is the normalised posterior of the product weight
    seq-inv : ∀ (prior : Pre Θ) (w v : Func (QBS.Carrier Θ) Aˢ) {n} →
      evidence Norm (posteriorU Norm prior w) v * n ≈ 1# → evidence Norm prior (_·_ Norm {Θ} w v) * n ≈ 1#
    seq-inv prior w v hn = trans (*-cong (sym (bayes-numerator Norm prior w v)) refl) hn

    posterior-seq : ∀ (prior : Pre Θ) (w v : Func (QBS.Carrier Θ) Aˢ) n
      (hn : evidence Norm (posteriorU Norm prior w) v * n ≈ 1#) →
      MP._≈ᵖ_ (posterior Norm (posteriorU Norm prior w) v n hn)
              (posterior Norm prior (_·_ Norm {Θ} w v) n (seq-inv prior w v hn))
    posterior-seq prior w v n hn f = begin
      MP.∫ (posterior Norm (posteriorU Norm prior w) v n hn) f  ≈⟨ bayes Norm (posteriorU Norm prior w) v f n hn ⟩
      n * MA.∫ (posteriorU Norm prior w) vf                      ≈⟨ *-cong refl (bayes-numerator Norm prior w vf) ⟩
      n * MA.∫ prior (_·_ Norm {Θ} w vf)
        ≈⟨ *-cong refl (∑-cong (λ r → *-cong refl (sym (*-assoc _ _ _)))) ⟩
      n * MA.∫ prior (_·_ Norm {Θ} wv f)                         ≈⟨ sym (bayes Norm prior wv f n h′) ⟩
      MP.∫ (posterior Norm prior wv n h′) f                      ∎
      where wv = _·_ Norm {Θ} w v
            vf = _·_ Norm {Θ} v f
            h′ = seq-inv prior w v hn

    -- posterior update (normalised): the posterior of the conjugate prior at p after xs is the normalised
    -- conjugate posterior at updateList p T xs, for any inverses n, m of the two evidences
    posterior-update-norm : ∀ (prior : Pre Θ) (p : Paramℕ k) xs (n m : ∣A∣)
      (hn : evidence Norm (posteriorU Norm prior (kernel p)) (likSeq xs) * n ≈ 1#)
      (hm : evidence Norm prior (kernel (updateList p T xs)) * m ≈ 1#) →
      MP._≈ᵖ_ (posterior Norm (posteriorU Norm prior (kernel p)) (likSeq xs) n hn)
              (posterior Norm prior (kernel (updateList p T xs)) m hm)
    posterior-update-norm prior p xs n m hn hm f = trans (posterior-seq prior K (likSeq xs) n hn f)
      (posterior-prop prior (_·_ Norm {Θ} K (likSeq xs)) K′ K′ (hSeq xs) 1# n m (lik-update p xs)
        (λ θ → sym (*-identityˡ _)) (seq-inv prior K (likSeq xs) hn) hm f)
      where
        K = kernel p
        K′ = kernel (updateList p T xs)

    -- Bayesian sufficiency (normalised): equal (sumT, length) alone give equal posteriors, for any prior and any
    -- inverses n, m of the two evidences
    posterior-sufficient-norm : ∀ (prior : Pre Θ) xs ys (n m : ∣A∣) →
      (∀ j → sumT xs j ≡ sumT ys j) → length xs ≡ length ys →
      (hn : evidence Norm prior (likSeq xs) * n ≈ 1#) (hm : evidence Norm prior (likSeq ys) * m ≈ 1#) →
      MP._≈ᵖ_ (posterior Norm prior (likSeq xs) n hn) (posterior Norm prior (likSeq ys) m hm)
    posterior-sufficient-norm prior xs ys n m hT hlen hn hm =
      posterior-prop prior (likSeq xs) (likSeq ys) (kernel (sumT xs , length xs)) (hSeq xs) (hSeq ys) n m
        (likSeq-factor xs) (λ θ → trans (likSeq-factor ys θ) (*-cong refl (sym (kernel-≡ hT hlen θ)))) hn hm

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

    private
      oneΘ : Func (QBS.Carrier Θ) Aˢ
      oneΘ = record { to = λ _ → 1# ; cong = λ _ → refl }

    open Family {Θ = Θ} θBernoulli oneΘ (λ _ → 1#) TBernoulli public

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
