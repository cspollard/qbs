{-# OPTIONS --safe --without-K #-}

-- The measure monad on QBS over the discrete random source R = ℕ, for a class
-- K of admissible weights (probability measures, or all measures).
--
-- A measure on a QBS X is a pair (α, μ) of a random element α : R → X and a
-- weight function μ : R → A.  Following HKSV (Def. 10) and Hirata–Minamide–Sato
-- (Def. 4) pairs are identified when they have the same push-forward; we use the
-- equivalent description "same integral against every test function X → A",
-- which needs no grouping of points into classes (and so no quotients).
module QBS.Model.Monad where

open import Level using (Level; suc; _⊔_; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
import Function.Construct.Composition as Comp
open import QBS.Category using (QBSCat)
open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Model.Pairing
open import QBS.Model.DiscreteSource
open import QBS.Model.Semiring
open import QBS.Model.Sums

-- Classes of admissible weights on R.
record WeightClass {ℓ} (A : CompleteSemiring ℓ) : Set (suc ℓ) where
  open CompleteSemiring A
  open Sums A
  private R = Lift ℓ ℕ
  field
    Ok : (R → Carrier) → Set ℓ
    ok-resp : ∀ {μ ν} → (∀ r → μ r ≈ ν r) → Ok μ → Ok ν
    ok-dirac : ∀ r₀ → Ok (dirac r₀)
    ok-push : ∀ {μ} (f : R → R) → Ok μ → Ok (push f μ)
    ok-bind : ∀ {ν} {g : R → R → Carrier} → Ok ν → (∀ r → Ok (g r)) →
      Ok (λ k → ∑ (λ r → ν r * g r k))

module Measures {ℓ} (A : CompleteSemiring ℓ) (K : WeightClass A) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open WeightClass K
  private
    open DS ℓ using (S)
    R = Lift ℓ ℕ
  open RandomSource S using (Rˢ) renaming (pair to pairᴺ; unpair to unpairᴺ; unpair-pair to unpair-pairᴺ)
  open QBS

  -- A measure on X, before identification.
  record Pre (X : QBS S) : Set ℓ where
    constructor mk
    field
      αₛ : Func Rˢ (Carrier X)
      α-random : Random X αₛ
      μ : R → ∣A∣
      μ-ok : Ok μ
  open Pre

  α : ∀ {X} → Pre X → R → ∣ X ∣
  α p r = αₛ p ⟨$⟩ r

  -- integration against a test function
  ∫ : ∀ {X} → Pre X → Func (Carrier X) Aˢ → ∣A∣
  ∫ p f = ∑ (λ r → μ p r * (f ⟨$⟩ α p r))

  _≈ᵖ_ : ∀ {X} → Pre X → Pre X → Set ℓ
  p ≈ᵖ q = ∀ f → ∫ p f ≈ ∫ q f

  PreS : QBS S → Setoid ℓ ℓ
  PreS X = record
    { Carrier = Pre X
    ; _≈_ = _≈ᵖ_
    ; isEquivalence = record
        { refl = λ _ → Setoid.refl Aˢ
        ; sym = λ e f → Setoid.sym Aˢ (e f)
        ; trans = λ e e′ f → Setoid.trans Aˢ (e f) (e′ f)
        }
    }

  -- The witness that β : R → Pre X is a random element of the measure space.
  record Wit {X : QBS S} (β : R → Pre X) : Set ℓ where
    field
      wαₛ : Func Rˢ (Carrier X)
      wα-random : Random X wαₛ
      wg : R → R → ∣A∣
      wg-ok : ∀ r → Ok (wg r)
      w-eq : ∀ r → β r ≈ᵖ mk wαₛ wα-random (wg r) (wg-ok r)

  open Wit

  wα : ∀ {X} {β : R → Pre X} → Wit β → R → ∣ X ∣
  wα w r = wαₛ w ⟨$⟩ r

  private
    -- the pushforward index map R → R, m ↦ ⟨n, m⟩
    φ : ℕ → R → R
    φ n m = lift (pairᴺ n (lower m))

    r₀ : R
    r₀ = lift 0

    ι : R → ℕ
    ι r = proj₁ (unpairᴺ (lower r))

    ρ : R → R
    ρ r = lift (proj₂ (unpairᴺ (lower r)))

  TQ : QBS S → QBS S
  TQ X = record
    { Carrier = PreS X
    ; probes = record
        { Random = λ β → Wit (β ⟨$⟩_)
        ; random-resp = λ e w → record
            { wαₛ = wαₛ w ; wα-random = wα-random w ; wg = wg w ; wg-ok = wg-ok w
            ; w-eq = λ r f → Setoid.trans Aˢ (Setoid.sym Aˢ (e r f)) (w-eq w r f) }
        ; const-random = λ x → record
            { wαₛ = αₛ x ; wα-random = α-random x ; wg = λ _ → μ x ; wg-ok = λ _ → μ-ok x
            ; w-eq = λ _ f → Setoid.refl Aˢ }
        ; pre-random = λ {_} {h} w _ → record
            { wαₛ = wαₛ w ; wα-random = wα-random w ; wg = λ r → wg w (h ⟨$⟩ r)
            ; wg-ok = λ r → wg-ok w (h ⟨$⟩ r) ; w-eq = λ r → w-eq w (h ⟨$⟩ r) }
        }
    ; glue-random = λ {i} _ β w → record
        { wαₛ = glueₛ (⇑ ι) (λ n → wαₛ (w n) ∘ₛ ⇑ ρ)
        ; wα-random = QBS.glue-random X {⇑ ι} tt (λ n → wαₛ (w n) ∘ₛ ⇑ ρ)
            (λ n → QBS.pre-random X (wα-random (w n)) tt)
        ; wg = λ r → push (φ (i ⟨$⟩ r)) (wg (w (i ⟨$⟩ r)) r)
        ; wg-ok = λ r → ok-push (φ (i ⟨$⟩ r)) (wg-ok (w (i ⟨$⟩ r)) r)
        ; w-eq = λ r f →
            Setoid.trans Aˢ (w-eq (w (i ⟨$⟩ r)) r f)
              (Setoid.sym Aˢ (Setoid.trans Aˢ
                (push-∑ (φ (i ⟨$⟩ r)) (wg (w (i ⟨$⟩ r)) r) (λ k → f ⟨$⟩ B w (unpairᴺ (lower k))))
                (∑-cong (λ m → *-cong (Setoid.refl Aˢ)
                  (Func.cong f (Setoid.reflexive (Carrier X)
                    (≡.cong (B w) (unpair-pairᴺ (i ⟨$⟩ r) (lower m)))))))))
        }
    }
    where
      B : ∀ {β : ℕ → R → Pre X} → (∀ n → Wit (β n)) → ℕ × ℕ → ∣ X ∣
      B w u = wα (w (proj₁ u)) (lift (proj₂ u))

  open Hom

  ----------------------------------------------------------------------------
  -- functor action

  mapPre : ∀ {X Y} → Hom S X Y → Pre X → Pre Y
  mapPre {Y = Y} f p =
    mk (map f ∘ₛ αₛ p) (map-random f (α-random p)) (μ p) (μ-ok p)

  -- ∫ (mapPre f p) g ≡ ∫ p (g ∘ f)   (definitionally)

  TH : ∀ {X Y} → Hom S X Y → Hom S (TQ X) (TQ Y)
  TH {X} {Y} f = record
    { map = record
        { to = mapPre f
        ; cong = λ e g → e (Comp.function (map f) g)
        }
    ; map-random = λ w → record
        { wαₛ = map f ∘ₛ wαₛ w
        ; wα-random = map-random f (wα-random w)
        ; wg = wg w
        ; wg-ok = wg-ok w
        ; w-eq = λ r g → w-eq w r (Comp.function (map f) g)
        }
    }

  ----------------------------------------------------------------------------
  -- unit

  ηPre : ∀ {X} → ∣ X ∣ → Pre X
  ηPre {X} x = mk (constₛ x) (QBS.const-random X x) (dirac r₀) (ok-dirac r₀)

  -- ∫ (ηPre x) f ≈ f x
  ∫-η : ∀ {X} (x : ∣ X ∣) (f : Func (Carrier X) Aˢ) → ∫ {X} (ηPre {X} x) f ≈ f ⟨$⟩ x
  ∫-η {X} x f = dirac-∑ r₀ (λ _ → f ⟨$⟩ x)

  ηH : ∀ X → Hom S X (TQ X)
  ηH X = record
    { map = record
        { to = ηPre
        ; cong = λ {x} {y} e f → Setoid.trans Aˢ (∫-η {X} x f)
            (Setoid.trans Aˢ (Func.cong f e) (Setoid.sym Aˢ (∫-η {X} y f)))
        }
    ; map-random = λ {a} p → record
        { wαₛ = a
        ; wα-random = p
        ; wg = λ r → dirac r
        ; wg-ok = λ r → ok-dirac r
        ; w-eq = λ r f → Setoid.trans Aˢ (∫-η {X} (a ⟨$⟩ r) f)
            (Setoid.sym Aˢ (dirac-∑ r (λ k → f ⟨$⟩ (a ⟨$⟩ k))))
        }
    }

  ----------------------------------------------------------------------------
  -- join

  joinPre : ∀ {X} → Pre (TQ X) → Pre X
  joinPre p = mk (wαₛ w) (wα-random w)
                 (λ k → ∑ (λ r → μ p r * wg w r k)) (ok-bind (μ-ok p) (wg-ok w))
    where w = α-random p

  -- the integral of f, as a test function on the measure space
  ∫ᶠ : ∀ {X} → Func (Carrier X) Aˢ → Func (Carrier (TQ X)) Aˢ
  ∫ᶠ f = record { to = λ t → ∫ t f ; cong = λ e → e f }

  -- ∫ (join p) f ≈ ∫ p (∫ – f)    (Tonelli)
  ∫-join : ∀ {X} (p : Pre (TQ X)) (f : Func (Carrier X) Aˢ) → ∫ (joinPre p) f ≈ ∫ p (∫ᶠ f)
  ∫-join {X} p f = begin
    ∑ (λ k → (∑ (λ r → μ p r * wg w r k)) * z k)
      ≈⟨ ∑-cong (λ k → ∑-distribʳ (λ r → μ p r * wg w r k) (z k)) ⟩
    ∑ (λ k → ∑ (λ r → (μ p r * wg w r k) * z k))
      ≈⟨ ∑-swap (λ k r → (μ p r * wg w r k) * z k) ⟩
    ∑ (λ r → ∑ (λ k → (μ p r * wg w r k) * z k))
      ≈⟨ ∑-cong (λ r → ∑-cong (λ k → *-assoc (μ p r) (wg w r k) (z k))) ⟩
    ∑ (λ r → ∑ (λ k → μ p r * (wg w r k * z k)))
      ≈⟨ ∑-cong (λ r → ∑-scale (μ p r) (λ k → wg w r k * z k)) ⟩
    ∑ (λ r → μ p r * ∑ (λ k → wg w r k * z k))
      ≈⟨ ∑-cong (λ r → *-cong (Setoid.refl Aˢ) (Setoid.sym Aˢ (w-eq w r f))) ⟩
    ∑ (λ r → μ p r * ∫ (α p r) f)
      ∎
    where
      open SetoidReasoning Aˢ
      w = α-random p
      z = λ k → f ⟨$⟩ wα w k

  joinH : ∀ X → Hom S (TQ (TQ X)) (TQ X)
  joinH X = record
    { map = record
        { to = joinPre
        ; cong = λ {p} {q} e f →
            Setoid.trans Aˢ (∫-join p f)
              (Setoid.trans Aˢ (e (∫ᶠ f)) (Setoid.sym Aˢ (∫-join q f)))
        }
    ; map-random = λ {β} w →
        let w₂ = wα-random w in record
          { wαₛ = wαₛ w₂
          ; wα-random = wα-random w₂
          ; wg = λ r k → ∑ (λ r′ → wg w r r′ * wg w₂ r′ k)
          ; wg-ok = λ r → ok-bind (wg-ok w r) (wg-ok w₂)
          ; w-eq = λ r f →
              Setoid.trans Aˢ (∫-join (β ⟨$⟩ r) f)
                (Setoid.trans Aˢ (w-eq w r (∫ᶠ f))
                  (Setoid.sym Aˢ (∫-join (mk (wαₛ w) (wα-random w) (wg w r) (wg-ok w r)) f)))
          }
    }

  ----------------------------------------------------------------------------
  -- the monad

  TF : Endofunctor (QBSCat S)
  TF = record
    { F₀ = TQ
    ; F₁ = TH
    ; identity = λ _ → Setoid.refl Aˢ
    ; homomorphism = λ _ → Setoid.refl Aˢ
    ; F-resp-≈ = λ {_} {Y} {f} {g} e {p} h →
        ∑-cong (λ r → *-cong (Setoid.refl Aˢ) (Func.cong h (e {α p r})))
    }

  ηN : NaturalTransformation idF TF
  ηN = record
    { η = ηH
    ; commute = λ {X} {Y} f {x} g →
        Setoid.trans Aˢ (∫-η {Y} (map f ⟨$⟩ x) g) (Setoid.sym Aˢ (∫-η {X} x (Comp.function (map f) g)))
    ; sym-commute = λ {X} {Y} f {x} g →
        Setoid.trans Aˢ (∫-η {X} x (Comp.function (map f) g)) (Setoid.sym Aˢ (∫-η {Y} (map f ⟨$⟩ x) g))
    }

  μN : NaturalTransformation (TF ∘F TF) TF
  μN = record
    { η = joinH
    ; commute = λ {X} {Y} f {p} g →
        Setoid.trans Aˢ (∫-join (mapPre (TH f) p) g) (Setoid.sym Aˢ (∫-join p (Comp.function (map f) g)))
    ; sym-commute = λ {X} {Y} f {p} g →
        Setoid.trans Aˢ (∫-join p (Comp.function (map f) g)) (Setoid.sym Aˢ (∫-join (mapPre (TH f) p) g))
    }

  TM : Monad (QBSCat S)
  TM = record
    { F = TF
    ; η = ηN
    ; μ = μN
    ; assoc = λ {X} {p} f →
        Setoid.trans Aˢ (∫-join (mapPre (joinH X) p) f)
          (Setoid.trans Aˢ (∑-cong (λ r → *-cong (Setoid.refl Aˢ) (∫-join (α p r) f)))
            (Setoid.sym Aˢ (Setoid.trans Aˢ (∫-join (joinPre p) f) (∫-join p (∫ᶠ f)))))
    ; sym-assoc = λ {X} {p} f →
        Setoid.trans Aˢ (Setoid.trans Aˢ (∫-join (joinPre p) f) (∫-join p (∫ᶠ f)))
          (Setoid.sym Aˢ (Setoid.trans Aˢ (∫-join (mapPre (joinH X) p) f)
            (∑-cong (λ r → *-cong (Setoid.refl Aˢ) (∫-join (α p r) f)))))
    ; identityˡ = λ {X} {p} f →
        Setoid.trans Aˢ (∫-join (mapPre (ηH X) p) f)
          (∑-cong (λ r → *-cong (Setoid.refl Aˢ) (∫-η {X} (α p r) f)))
    ; identityʳ = λ {X} {p} f →
        Setoid.trans Aˢ (∫-join (ηPre p) f) (∫-η {TQ X} p (∫ᶠ f))
    }
