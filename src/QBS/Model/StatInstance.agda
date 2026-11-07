{-# OPTIONS --safe --without-K #-}

-- The discrete measure monad is a model of `StatisticalInterface`: assembles `StatWeights` (weights, inclusion,
-- score, countable sums) and `StatNormalize` (`normH`) and proves the laws; packaged at `discreteStat`.
module QBS.Model.StatInstance where

open import Level using (Lift; lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Function.Construct.Composition as Comp

open import Categories.Category.Core using (Category)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import Categories.Monad using (Monad)
import Categories.Monad.Strong as CMS
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (cocartesian; _+Q_; Piece; ev)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; !Q)
open import QBS.Exponential using (cartesianClosed)
open import QBS.Probes using (ℛQ; probe)
open import QBS.Probability
open import QBS.Statistical
open import QBS.Model.Pairing
open import QBS.Model.DiscreteSource
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad
open import QBS.Model.WeightClasses
open import QBS.Model.Strong
open import QBS.Model.ProbInstance
open import QBS.Model.Cantor
open import QBS.Model.StatWeights
open import QBS.Model.StatNormalize

module _ {ℓ} (N : NormalizableSemiring ℓ) where
  open StatWeights N
  open StatNormalize N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  private
    open DS ℓ using (S)
    R = Lift ℓ ℕ
    r₀ : R
    r₀ = lift 0
  open Cantor A
  open QBS
  open Hom
  open MA using (Pre; mk; α; ∫; ∫ᶠ; mapPre; ηPre; joinPre; ∫-η; ∫-join; TQ; TH; TM; TF)
  open MA.Pre

  module SA = Strength A (allClass A)

  -- the laws of the instance, stated in the notation of `StatisticalInterface`
  module Laws where
    open Category (QBSCat S) using () renaming (_≈_ to _≈ᵏ_; _∘_ to _∘ᵏ_; _⇒_ to _⇒ᵏ_)
    open Canonical.CartesianClosed (cartesianClosed S) using (!; ⟨_,_⟩) renaming (⊤ to 𝟙)
    open Cocartesian.BinaryCoproducts (Cocartesian.Cocartesian.coproducts (cocartesian S)) using (i₁; i₂)
    module M = Monad (CMS.StrongMonad.M SA.strongMonad)
    -- chains of equalities in the weights: transitivity and symmetry
    open Setoid Aˢ using () renaming (trans to infixr 5 _⟫_; sym to infix 8 ~_)

    zero-bind-law : ∀ (k : 𝟙 ⇒ᵏ M.F.F₀ 𝟙) → M.μ.η 𝟙 ∘ᵏ M.F.F₁ k ∘ᵏ constE zeroP ≈ᵏ constE zeroP
    zero-bind-law k {pt} f =
      ∫-join (mapPre k zeroP) f ⟫ ∑-zero _ (λ _ → zeroˡ _) ⟫ ~ ∫-zero f

    score-zero-law : scoreE ∘ᵏ constH 0# ≈ᵏ constE zeroP
    score-zero-law {pt} f = ∫-score 0# f ⟫ zeroˡ _ ⟫ ~ ∫-zero f

    score-mul-law : ∀ (a b : 𝟙 ⇒ᵏ WQ) → scoreE ∘ᵏ mulH ∘ᵏ ⟨ a , b ⟩ ≈ᵏ M.μ.η 𝟙 ∘ᵏ M.F.F₁ (scoreE ∘ᵏ b ∘ᵏ !) ∘ᵏ scoreE ∘ᵏ a
    score-mul-law a b {pt} f =
      let x = map a ⟨$⟩ pt
          y = map b ⟨$⟩ pt
          c = f ⟨$⟩ tt
          g = _∘H_ S scoreE (_∘H_ S b (!Q S))
      in ∫-score (x * y) f ⟫ *-assoc x y c ⟫ *-cong refl (~ ∫-score y f)
         ⟫ ~ weight-sum x (∫ (scoreP y) f) ⟫ ~ ∫-join (mapPre g (scoreP x)) f

    bind-sumK-law : ∀ {X Y} (ks : ℕ → X ⇒ᵏ M.F.F₀ Y) (t : 𝟙 ⇒ᵏ M.F.F₀ X) →
      M.μ.η Y ∘ᵏ M.F.F₁ (sumKH ks) ∘ᵏ t ≈ᵏ sumE (λ n → M.μ.η Y ∘ᵏ M.F.F₁ (ks n) ∘ᵏ t)
    bind-sumK-law {X} {Y} ks t {pt} f =
      let p = map t ⟨$⟩ pt
      in ∫-join (mapPre (sumKH ks) p) f
         ⟫ ∑-cong (λ r → *-cong (Setoid.refl Aˢ) (∫-sum (λ n → map (ks n) ⟨$⟩ α p r) f))
         ⟫ ∑-cong (λ r → ~ ∑-scale (μ p r) (λ n → ∫ (map (ks (lower n)) ⟨$⟩ α p r) f))
         ⟫ ∑-swap (λ r n → μ p r * ∫ (map (ks (lower n)) ⟨$⟩ α p r) f)
         ⟫ ~ (∫-sum (λ n → joinPre (mapPre (ks n) p)) f ⟫ ∑-cong (λ n → ∫-join (mapPre (ks (lower n)) p) f))

    score-one-law : scoreE ∘ᵏ constH 1# ≈ᵏ M.η.η 𝟙
    score-one-law {pt} f = ∫-score 1# f ⟫ *-identityˡ _ ⟫ ~ ∫-η {1Q S} pt f

    -- scaling a measure by a weight is a bind through `score`
    scale-def : ∀ {X} (a : 𝟙 ⇒ᵏ WQ) (t : 𝟙 ⇒ᵏ M.F.F₀ X) → scaleE a t ≈ᵏ M.μ.η X ∘ᵏ M.F.F₁ t ∘ᵏ scoreE ∘ᵏ a
    scale-def {X} a t {pt} f =
      ∫-scale {X} (map a ⟨$⟩ pt) (map t ⟨$⟩ pt) f
      ⟫ ~ (∫-join (mapPre t (scoreP (map a ⟨$⟩ pt))) f ⟫ ∫-score (map a ⟨$⟩ pt) (Comp.function (map t) (∫ᶠ f)))

    sum-join-law : ∀ {X} (ts : ℕ → 𝟙 ⇒ᵏ M.F.F₀ (M.F.F₀ X)) → M.μ.η X ∘ᵏ sumE ts ≈ᵏ sumE (λ n → M.μ.η X ∘ᵏ ts n)
    sum-join-law {X} ts {pt} f =
      let t = λ n → map (ts n) ⟨$⟩ tt
      in ∫-join (sumP t) f ⟫ ∫-sum t (∫ᶠ f) ⟫ ∑-cong (λ n → ~ ∫-join (t (lower n)) f) ⟫ ~ ∫-sum (λ n → joinPre (t n)) f

    normalize-prob-law : ∀ X → normH X ∘ᵏ Monad⇒-id.α.η inclusion X ≈ᵏ i₁
    normalize-prob-law X {p} = normProb p (NormalizableSemiring.invertible? N (mass (forgetPre p)))

    normalize-zero-law : ∀ {X} (x : 𝟙 ⇒ᵏ X) → normH X ∘ᵏ M.F.F₁ x ∘ᵏ constE zeroP ≈ᵏ i₂
    normalize-zero-law {X} x {pt} =
      normZero (mapPre x zeroP) (∑-zero _ (λ _ → refl))
      (NormalizableSemiring.invertible? N (mass (mapPre x zeroP)))

  open Laws

  discreteWeights : CommutativeMonoidWithZero (QBSCat S) (cartesianClosed S)
  discreteWeights = record
    { W = WQ
    ; mulW = mulH
    ; oneW = constH 1#
    ; zero⇒ = constH 0#
    ; mul-assoc = λ a b c {z} → *-assoc _ _ _
    ; mul-comm = λ a b {z} → *-comm _ _
    ; mul-one = λ a {z} → *-identityʳ _
    ; mul-zero = λ a {z} → zeroʳ _
    }

  discreteMeasures : SubMonad (discreteProb A)
  discreteMeasures = record
    { commutativeMonad = record { strongMonad = SA.strongMonad ; commutative = SA.commutative }
    ; inclusion = inclusion
    ; inclusion-strong = λ _ _ {_} _ → Setoid.refl Aˢ
    }

  discreteScore : Score discreteWeights discreteMeasures
  discreteScore = record
    { zero = constE zeroP
    ; zero-bind = zero-bind-law
    ; score = scoreE
    ; score-zero = score-zero-law
    ; score-one = score-one-law
    ; score-mul = score-mul-law
    }

  discreteSums : CountableSums discreteMeasures
  discreteSums = record
    { sumK = sumKH
    ; sumK-point = λ ks x {pt} f → Setoid.refl Aˢ
    ; bind-sumK = bind-sumK-law
    ; sum-nat = λ {X} {Y} f ts {pt} g →
        Setoid.trans Aˢ (∫-sum (λ n → map (ts n) ⟨$⟩ tt) (Comp.function (map f) g))
          (Setoid.sym Aˢ (∫-sum (λ n → mapPre f (map (ts n) ⟨$⟩ tt)) g))
    ; sum-join = sum-join-law
    }

  module DS′ = Score discreteScore
  module DM′ = CountableSums discreteSums

  -- the laws involving the derived `scaleM`, bridged to the direct `scaleE` by `scale-def`
  module Laws₂ where
    open Category (QBSCat S) using () renaming (_≈_ to _≈ᵏ_; _∘_ to _∘ᵏ_; _⇒_ to _⇒ᵏ_)
    open Canonical.CartesianClosed (cartesianClosed S) using (!; ⟨_,_⟩) renaming (⊤ to 𝟙)
    open Setoid Aˢ using () renaming (trans to infixr 5 _⟫_; sym to infix 8 ~_)

    scaled-laws-law : ∀ {X} (t : 𝟙 ⇒ᵏ M.F.F₀ X) →
      Σ (ℕ → ℛQ S ⇒ᵏ X) λ a → Σ (ℕ → 𝟙 ⇒ᵏ WQ) λ w → Σ (ℕ → ProbabilityInterface.Measure (discreteProb A)) λ μ →
        t ≈ᵏ DM′.sumM
            (λ n → DS′.scaleM (w n) (Monad⇒-id.α.η inclusion X ∘ᵏ ProbabilityInterface.law (discreteProb A) (a n) (μ n)))
    -- a countable sum of global measures is, pointwise in the integrals, the sum of the pre-measures
    sumM-∫ : ∀ {X} (D : ℕ → 𝟙 ⇒ᵏ M.F.F₀ X) (fam : ℕ → Pre X) →
      (∀ n f → ∫ (map (D n) ⟨$⟩ tt) f ≈ ∫ (fam n) f) → ∀ f → ∫ (map (DM′.sumM D) ⟨$⟩ tt) f ≈ ∫ (sumP fam) f
    sumM-∫ D fam h f = ∫-sum (λ n → map (D n) ⟨$⟩ tt) f ⟫ ∑-cong (λ n → h (lower n) f) ⟫ ~ ∫-sum fam f

    scaled-laws-law {X} t =
      let p = map t ⟨$⟩ tt
          lawA = λ (n : ℕ) → mk {X} (αₛ p) (α-random p) (dirac (lift n)) tt
          fam = λ (n : ℕ) → scaleP (μ p (lift n)) (lawA n)
          aN = λ (n : ℕ) → probe S (α-random p)
          wN = λ (n : ℕ) → constH (μ p (lift n))
          μN = λ (n : ℕ) → dirac (lift n) , WeightClass.ok-dirac (probClass A) (lift n)
          D = λ (n : ℕ) → DS′.scaleM (wN n) (Monad⇒-id.α.η inclusion X ∘ᵏ ProbabilityInterface.law (discreteProb A) (aN n) (μN n))
      in aN , wN , μN
       , (λ {pt} f → ~
           (sumM-∫ D fam
           (λ n f′ → ~ scale-def (wN n)
           (Monad⇒-id.α.η inclusion X ∘ᵏ ProbabilityInterface.law (discreteProb A) (aN n) (μN n)) {tt} f′) f
                      ⟫ ∫-sum fam f ⟫ ∑-cong (λ n → ∫-scale (μ p n) (lawA (lower n)) f
                                       ⟫ *-cong refl (dirac-∑ n (λ k → f ⟨$⟩ α p k)))))

    normalize-scale-law : ∀ {X} (a b : 𝟙 ⇒ᵏ WQ) → mulH ∘ᵏ ⟨ a , b ⟩ ≈ᵏ constH 1# →
      ∀ (t : 𝟙 ⇒ᵏ M.F.F₀ X) → normH X ∘ᵏ DS′.scaleM a t ≈ᵏ normH X ∘ᵏ t
    normalize-scale-law {X} a b hab t {pt} =
      Setoid.trans (⊎ʳ.⊎-setoid (Carrier (MP.TQ X)) (Carrier (1Q S)))
        (Func.cong (map (normH X)) (λ f → ~ scale-def a t {pt} f))
        (normScale (map a ⟨$⟩ pt) (map b ⟨$⟩ pt) (hab {pt}) (map t ⟨$⟩ pt)
          (NormalizableSemiring.invertible? N (mass (scaleP (map a ⟨$⟩ pt) (map t ⟨$⟩ pt))))
          (NormalizableSemiring.invertible? N (mass (map t ⟨$⟩ pt))))

  open Laws₂

  discreteStat : StatisticalInterface ℓ (QBSCat S) (ℛQ S) (cartesianClosed S) (discreteProb A)
    (Cocartesian.Cocartesian.coproducts (cocartesian S))
  discreteStat = record
    { weights = discreteWeights
    ; measures = discreteMeasures
    ; scoring = discreteScore
    ; sums = discreteSums
    ; scaled-laws = scaled-laws-law
    ; normalization = record
        { normalize = normH
        ; normalize-prob = normalize-prob-law
        ; normalize-zero = normalize-zero-law
        ; normalize-scale = normalize-scale-law
        }
    }
