{-# OPTIONS --safe --without-K #-}

-- The probability monad on quasi-Borel spaces over Cantor space (HKSV, §V): a measure on X is a
-- pair [α, m] of a random element α : R → X and a probability measure m on R, identified when
-- all integrals of [0,1]-valued test functions agree.  A map R → T X is random when it is
-- given by a *joint* probe ℛ × ℛ ⇒ X and a measurable kernel.
module QBS.Continuous.Monad where

open import Level using (Lift; lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Bool.Base using (false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ; _×-function_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
import Function.Construct.Identity as Id
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Function.Construct.Composition as Comp

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)

open import QBS.Core
open import QBS.IntegralMonad using (Integral; MonadData; module Laws)
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q)
import QBS.Probes as Probes
open import QBS.Borel.Core
open import QBS.Borel.Source
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators
open import QBS.Analysis.Param
open import QBS.Analysis.Tensor
open import QBS.Continuous.Sample
open import QBS.Classical using (LEM₀)

module Continuous (A : OmegaSemiring (L.suc L.zero)) (lem : LEM₀) (K : Integration.MeasureClass A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open MeasureClass K
  open Indicators A lem
  open Tensor A lem using (constK)
  open UnitInterval A
  module P₁ = Param A lem mergeC measurable-merge₁ Cyl-rect
  open RandomSource S using (Rˢ; Meas; Idx) renaming (meas-id to measId; meas-const to measConst; idx-pre to idxPre; meas-∘ to measComp)
  open QBS
  open Hom

  r₀ : R
  r₀ = lift (λ _ → false)

  -- a measure on X before identification
  record Pre (X : QBS S) : Set₁ where
    constructor mk
    field
      α : Func Rˢ (Carrier X)
      α-random : Random X α
      m : Measure
      ok : Ok m
  open Pre

  -- integral of a [0,1]-valued test function
  ∫ : ∀ {X : QBS S} → Pre X → Hom S X AQ → ∣A∣
  ∫ {X} p f = I (m p) (λ r → proj₁ (map f ⟨$⟩ (α p ⟨$⟩ r))) (map-random f (α-random p))

  _≈ᵖ_ : ∀ {X : QBS S} → Pre X → Pre X → Set₁
  _≈ᵖ_ {X} p q = ∀ f → ∫ p f ≈ ∫ q f

  PreS : QBS S → Setoid (L.suc L.zero) (L.suc L.zero)
  PreS X = record
    { Carrier = Pre X
    ; _≈_ = _≈ᵖ_
    ; isEquivalence = record
        { refl = λ _ → Setoid.refl Aˢ
        ; sym = λ e f → Setoid.sym Aˢ (e f)
        ; trans = λ e e′ f → Setoid.trans Aˢ (e f) (e′ f)
        }
    }

  -- the proof that α is random does not affect the integrals
  rand-irrel : ∀ {X : QBS S} {α : Func Rˢ (Carrier X)} (r₁ r₂ : Random X α) (n : Measure) (o : Ok n) →
    _≈ᵖ_ {X} (mk {X} α r₁ n o) (mk {X} α r₂ n o)
  rand-irrel {X} {α} r₁ r₂ n o f = I-cong n (λ x → Setoid.refl Aˢ) (map-random f r₁) (map-random f r₂)

  -- pre-measures with pointwise equivalent probes and the same measure are equivalent
  mk-cong : ∀ {X : QBS S} {α₁ α₂ : Func Rˢ (Carrier X)} (r₁ : Random X α₁) (r₂ : Random X α₂) (n : Measure) (o : Ok n) →
    (∀ s → Setoid._≈_ (Carrier X) (α₁ ⟨$⟩ s) (α₂ ⟨$⟩ s)) → _≈ᵖ_ {X} (mk {X} α₁ r₁ n o) (mk {X} α₂ r₂ n o)
  mk-cong {X} r₁ r₂ n o e f = I-cong n (λ s → Func.cong (map f) (e s)) (map-random f r₁) (map-random f r₂)

  -- joint probes and their sections
  Joint : QBS S → Set₁
  Joint X = Hom S (_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)) X

  -- the section s ↦ (r , s)
  at : R → Func Rˢ (Rˢ ×ₛ Rˢ)
  at r = < constₛ r , Id.function Rˢ >ₛ

  sec : ∀ {X : QBS S} → Joint X → R → Func Rˢ (Carrier X)
  sec a r = map a ∘ₛ at r

  sec-random : ∀ {X : QBS S} (a : Joint X) r → Random X (sec a r)
  sec-random a r = map-random a {at r} (measConst r , measId)

  -- witness that β : R → Pre X is a random family of measures, up to an equivalence ≋ of
  -- pre-measures containing `≈ᵖ` (`≈ᵖ` here, the weighted `≈ᴹ` in `Continuous/SFinite`)
  record Wit {X : QBS S} (_≋_ : Pre X → Pre X → Set₁) (β : R → Pre X) : Set₁ where
    field
      a : Joint X
      g : R → Measure
      g-ok : KernelOk g
      g-pr : ∀ r → Ok (g r)
      w-eq : ∀ r → β r ≋ mk (sec a r) (sec-random a r) (g r) (g-pr r)

  open Wit

  -- a witness for a finer equivalence is a witness for a coarser one
  Wit-mono : ∀ {X : QBS S} {_≋₁_ _≋₂_ : Pre X → Pre X → Set₁} {β : R → Pre X} →
    (∀ {p q} → p ≋₁ q → p ≋₂ q) → Wit _≋₁_ β → Wit _≋₂_ β
  Wit-mono sub w = record
    { a = a w ; g = g w ; g-ok = g-ok w ; g-pr = g-pr w ; w-eq = λ r → sub (w-eq w r) }

  -- joint probes from simple data
  sndJ : ∀ {X : QBS S} (α : Func Rˢ (Carrier X)) → Random X α → Joint X
  sndJ {X} α rα = record
    { map = α ∘ₛ proj₂ₛ
    ; map-random = λ {γ} (m₁ , m₂) → pre-random X rα m₂
    }

  fstJ : ∀ {X : QBS S} (α : Func Rˢ (Carrier X)) → Random X α → Joint X
  fstJ {X} α rα = record
    { map = α ∘ₛ proj₁ₛ
    ; map-random = λ {γ} (m₁ , m₂) → pre-random X rα m₁
    }

  -- reparametrise the first coordinate by a measurable map
  preJ : ∀ {X : QBS S} {f : Func Rˢ Rˢ} → Meas f → Joint X → Joint X
  preJ {X} {f} mf a = record
    { map = map a ∘ₛ (f ×-function Id.function Rˢ)
    ; map-random = λ {γ} (m₁ , m₂) → map-random a {(f ×-function Id.function Rˢ) ∘ₛ γ} (measComp {f} {proj₁ₛ ∘ₛ γ} mf m₁ , m₂)
    }

  -- glue a family of joint probes along a measurable partition of the first coordinate
  glueJ : ∀ {X : QBS S} {i : Func Rˢ ℕˢ} → Idx i → (ℕ → Joint X) → Joint X
  glueJ {X} {i} pi a = record
    { map = glueₛ (i ∘ₛ proj₁ₛ) (λ n → map (a n))
    ; map-random = λ {γ} (m₁ , m₂) → random-glue-pre X (λ n → map (a n)) γ
        (glue-random X {i ∘ₛ (proj₁ₛ ∘ₛ γ)} (idxPre {i} {proj₁ₛ ∘ₛ γ} pi m₁) (λ n → map (a n) ∘ₛ γ) (λ n → map-random (a n) (m₁ , m₂)))
    }

  const-eq : ∀ {X : QBS S} (p : Pre X) r →
    _≈ᵖ_ {X} p (mk {X} (sec {X} (sndJ {X} (α p) (α-random p)) r) (sec-random {X} (sndJ {X} (α p) (α-random p)) r) (m p) (ok p))
  const-eq {X} p r h = rand-irrel {X} {α p} (α-random p) (sec-random {X} (sndJ {X} (α p) (α-random p)) r) (m p) (ok p) h

  -- the probes of `TQ`, for any equivalence ≋ on pre-measures of Y that contains `≈ᵖ`
  -- (`Continuous/SFinite` re-exports them behind `abstract`, for compile time)
  module WitProbes {Y : QBS S} (_≋_ : Pre Y → Pre Y → Set₁)
    (≋-sym : ∀ {p q} → p ≋ q → q ≋ p) (≋-trans : ∀ {p q r} → p ≋ q → q ≋ r → p ≋ r)
    (incl : ∀ {p q} → _≈ᵖ_ {Y} p q → p ≋ q) where

    TQ-resp : ∀ {α β : R → Pre Y} → (∀ r → α r ≋ β r) → Wit _≋_ α → Wit _≋_ β
    TQ-resp e w = record
      { a = a w ; g = g w ; g-ok = g-ok w ; g-pr = g-pr w
      ; w-eq = λ r → ≋-trans (≋-sym (e r)) (w-eq w r) }

    TQ-const : (p : Pre Y) → Wit _≋_ (const p)
    TQ-const p = record
      { a = sndJ (α p) (α-random p)
      ; g = λ _ → m p
      ; g-ok = constK (m p)
      ; g-pr = λ _ → ok p
      ; w-eq = λ r → incl (const-eq p r) }

    TQ-pre : ∀ {β : R → Pre Y} {f : Func Rˢ Rˢ} → Wit _≋_ β → Meas f → Wit _≋_ (λ r → β (f ⟨$⟩ r))
    TQ-pre {β} {f} w mf = record
      { a = preJ mf (a w)
      ; g = λ r → g w (f ⟨$⟩ r)
      ; g-ok = λ fh → Fun-pre (g-ok w fh) mf
      ; g-pr = λ r → g-pr w (f ⟨$⟩ r)
      ; w-eq = λ r → ≋-trans (w-eq w (f ⟨$⟩ r))
          (incl (mk-cong {Y} (sec-random (a w) (f ⟨$⟩ r)) (sec-random (preJ {f = f} mf (a w)) r)
            (g w (f ⟨$⟩ r)) (g-pr w (f ⟨$⟩ r)) (λ s → Setoid.refl (Carrier Y)))) }

    TQ-glue : ∀ {i : Func Rˢ ℕˢ} → Idx i → (β : ℕ → R → Pre Y) →
      (∀ n → Wit _≋_ (β n)) → Wit _≋_ (λ r → β (i ⟨$⟩ r) r)
    TQ-glue {i} pi β ws = record
      { a = glueJ {i = i} pi (λ n → a (ws n))
      ; g = λ r → g (ws (i ⟨$⟩ r)) r
      ; g-ok = λ {h} fh → Glue.Fun-glue (i ⟨$⟩_) pi (λ n r → I (g (ws n) r) h fh) (λ n → g-ok (ws n) fh)
      ; g-pr = λ r → g-pr (ws (i ⟨$⟩ r)) r
      ; w-eq = λ r → ≋-trans (w-eq (ws (i ⟨$⟩ r)) r)
          (incl (mk-cong {Y} (sec-random (a (ws (i ⟨$⟩ r))) r) (sec-random (glueJ {i = i} pi (λ n → a (ws n))) r)
            (g (ws (i ⟨$⟩ r)) r) (g-pr (ws (i ⟨$⟩ r)) r) (λ s → Setoid.refl (Carrier Y)))) }

  module WitP (X : QBS S) = WitProbes {X} _≈ᵖ_ (λ {p q} e → Setoid.sym (PreS X) {p} {q} e)
    (λ {p q r} e e′ → Setoid.trans (PreS X) {p} {q} {r} e e′) (λ {p q} e → e)

  -- a random family of measures does not distinguish equal parameters, so it is a setoid map
  Wit-cong : ∀ {X : QBS S} {β : R → Pre X} → Wit _≈ᵖ_ β → ∀ {r r′} → r R≈.≈ r′ → _≈ᵖ_ {X} (β r) (β r′)
  Wit-cong {X} w {r} {r′} e f =
    Setoid.trans Aˢ (w-eq w r f)
      (Setoid.trans Aˢ
        (mk-cong {X} (sec-random (a w) r) (sec-random (a w) r′) (g w r) (g-pr w r)
           (λ s → Func.cong (map (a w)) (e , R≈.refl)) f)
        (Setoid.trans Aˢ
          (Fun-resp lem (g-ok w (map-random f (sec-random (a w) r′))) (lower e))
          (Setoid.sym Aˢ (w-eq w r′ f))))

  witₛ : ∀ {X : QBS S} {β : R → Pre X} → Wit _≈ᵖ_ β → Func Rˢ (PreS X)
  witₛ {X} {β} w = record { to = β ; cong = Wit-cong {X} w }

  TQ : QBS S → QBS S
  TQ X = record
    { Carrier = PreS X
    ; probes = record
        { Random = λ β → Wit _≈ᵖ_ (β ⟨$⟩_)
        ; random-resp = λ e w → WitP.TQ-resp X e w
        ; const-random = WitP.TQ-const X
        ; pre-random = λ {β} {f} w mf → WitP.TQ-pre X {β ⟨$⟩_} {f} w mf
        }
    ; glue-random = λ {i} pi β ws → WitP.TQ-glue X {i} pi (λ n → β n ⟨$⟩_) ws
    }

  ----------------------------------------------------------------------------
  -- functor action, unit, join

  mapPre : ∀ {X Y : QBS S} → Hom S X Y → Pre X → Pre Y
  mapPre f p = mk (map f ∘ₛ α p) (map-random f (α-random p)) (m p) (ok p)

  ∫-map : ∀ {X Y : QBS S} (f : Hom S X Y) (p : Pre X) (g : Hom S Y AQ) →
    ∫ {Y} (mapPre f p) g ≈ ∫ {X} p (_∘H_ S g f)
  ∫-map {X} {Y} f p g = I-cong (m p) (λ r → Setoid.refl Aˢ) _ _

  TH : ∀ {X Y : QBS S} → Hom S X Y → Hom S (TQ X) (TQ Y)
  TH {X} {Y} f = record
    { map = record
        { to = mapPre f
        ; cong = λ {p} {q} e g →
            Setoid.trans Aˢ (∫-map f p g) (Setoid.trans Aˢ (e (_∘H_ S g f)) (Setoid.sym Aˢ (∫-map f q g)))
        }
    ; map-random = λ {β} w → record
        { a = _∘H_ S f (a w)
        ; g = g w
        ; g-ok = g-ok w
        ; g-pr = g-pr w
        ; w-eq = λ r h →
            Setoid.trans Aˢ (∫-map f (β ⟨$⟩ r) h)
              (Setoid.trans Aˢ (w-eq w r (_∘H_ S h f))
                (I-cong (g w r) (λ s → Setoid.refl Aˢ) _ _))
        }
    }

  -- the unit: a Dirac-like measure
  ηPre : ∀ {X : QBS S} → ∣ X ∣ → Pre X
  ηPre {X} x = mk (constₛ x) (const-random X x) (dirac r₀) (ok-dirac r₀)

  ηH : ∀ X → Hom S X (TQ X)
  ηH X = record
    { map = record
        { to = ηPre {X}
        ; cong = λ {x} {y} e g → Func.cong (map g) e }
    ; map-random = λ {α} rα → record
        { a = fstJ {X} α rα
        ; g = λ _ → dirac r₀
        ; g-ok = constK (dirac r₀)
        ; g-pr = λ _ → ok-dirac r₀
        ; w-eq = λ r h → Setoid.refl Aˢ }
    }

  -- the integral over the section at r, rewritten through the bit-splitting
  section-eq : ∀ {X : QBS S} {β : R → Pre X} (w : Wit _≈ᵖ_ β) (f : Hom S X AQ) (r : R) →
    I (g w r) (λ s → proj₁ (map f ⟨$⟩ (map (a w) ⟨$⟩ (evensR (mergeR r s) , oddsR (mergeR r s)))))
      (Fun-pre {f = mergeR r} (Probes.unprobe S (_∘H_ S f (_∘H_ S (a w) fromH))) (measurable-merge₁ (lower r)))
      ≈ ∫ (β r) f
  section-eq {X} {β} w f r = Setoid.trans Aˢ
    (I-cong (g w r) (λ s → Func.cong (map f) (Func.cong (map (a w)) (merge-evens r s , merge-odds r s))) _ _)
    (Setoid.sym Aˢ (w-eq w r f))

  -- integration as a test function on measures
  ∫ᶠ : ∀ {X : QBS S} → Hom S X AQ → Hom S (TQ X) AQ
  ∫ᶠ {X} f = record
    { map = record
        { to = λ p → ∫ {X} p f , I-≤1 (m p) (map-random f (α-random p))
        ; cong = λ e → e f }
    ; map-random = λ {β} w →
        Fun-ext (λ r → section-eq {β = β ⟨$⟩_} w f r)
          (P₁.PF (g w) (g-ok w) (Probes.unprobe S (_∘H_ S f (_∘H_ S (a w) fromH))))
    }

  joinPre : ∀ {X : QBS S} → Pre (TQ X) → Pre X
  joinPre {X} p = mk (map (_∘H_ S (a w) fromH))
                     (Probes.unprobe S (_∘H_ S (a w) fromH))
                     (bind (m p) (P₁.pushMerge (g w)) (P₁.KernelOk-pushMerge {g w} (g-ok w)))
                     (ok-bind (ok p) (λ r → ok-push (measurable-merge₁ (lower r)) (g-pr w r)))
    where w = α-random p

  -- ∫ (join p) f = ∫ p (∫ – f)
  ∫-join : ∀ {X : QBS S} (p : Pre (TQ X)) (f : Hom S X AQ) → ∫ {X} (joinPre p) f ≈ ∫ {TQ X} p (∫ᶠ f)
  ∫-join {X} p f = I-cong (m p)
    (λ r → Setoid.trans Aˢ (I-cong (g w r) (λ s → Setoid.refl Aˢ) _ _) (section-eq w f r)) _ _
    where w = α-random p

  -- the witness for a random family of joins
  module JoinWit {X : QBS S} {β : R → Pre (TQ X)} (w : Wit _≈ᵖ_ β) where
    -- a witness for the two-parameter family (r , s) ↦ a (r , s), via the splitting
    w₂ : Wit _≈ᵖ_ (map (_∘H_ S (a w) fromH) ⟨$⟩_)
    w₂ = Probes.unprobe S (_∘H_ S (a w) fromH)

    a₂ : Joint X
    a₂ = a w₂

    -- the inner measure on u = merge s t, given the merged parameter k = merge r s
    K′ : R → Measure
    K′ k = push {mergeR (oddsR k)} (measurable-merge₁ (lower (oddsR k))) (g w₂ k)

    kK′ : KernelOk K′
    kK′ {h} fh = Fun-ext
      (λ k → I-cong (g w₂ k)
               (λ t → Fun-resp lem fh (lower (mergeR-cong (oddsR-cong (merge-evens k t)) (merge-odds k t)))) _ _)
      (P₁.PF (g w₂) (g-ok w₂) {λ x → h (φ x)} (Fun-pre {h} {φ} fh mφ))
      where
        φ : R → R
        φ x = mergeR (oddsR (evensR x)) (oddsR x)
        mφ : Measurable (down φ)
        mφ = measurable-merge (measurable-∘ measurable-evens measurable-odds) measurable-odds

    g′ : R → Measure
    g′ r = bind (g w r) (λ s → K′ (mergeR r s)) (λ fh → Fun-pre (kK′ fh) (measurable-merge₁ (lower r)))

    gok′ : KernelOk g′
    gok′ fh = P₁.PF (g w) (g-ok w) (kK′ fh)

    gpr′ : ∀ r → Ok (g′ r)
    gpr′ r = ok-bind (g-pr w r) (λ s → ok-push (measurable-merge₁ (lower (oddsR (mergeR r s)))) (g-pr w₂ (mergeR r s)))

    a′ : Joint X
    a′ = record
      { map = map a₂ ∘ₛ reassocR
      ; map-random = λ {γ} (m₁ , m₂) → map-random a₂ {reassocR ∘ₛ γ}
          (measurable-merge m₁ (measurable-∘ m₂ measurable-evens) , measurable-∘ m₂ measurable-odds)
      }

    eq′ : ∀ r → joinPre (β r) ≈ᵖ mk (sec a′ r) (sec-random a′ r) (g′ r) (gpr′ r)
    eq′ r f =
      Setoid.trans Aˢ (∫-join (β r) f)
        (Setoid.trans Aˢ (w-eq w r (∫ᶠ f))
          (I-cong (g w r) (λ s →
             Setoid.trans Aˢ
               (Func.cong (map (a w)) (R≈.sym (merge-evens r s) , R≈.sym (merge-odds r s)) f)
               (Setoid.trans Aˢ (w-eq w₂ (mergeR r s) f)
                 (I-cong (g w₂ (mergeR r s))
                    (λ t → Func.cong (map f) (Func.cong (map a₂)
                       (R≈.sym (R≈.trans (mergeR-cong (R≈.refl {r}) (merge-evens (oddsR (mergeR r s)) t))
                                         (mergeR-cong (R≈.refl {r}) (merge-odds r s)))
                         , R≈.sym (merge-odds (oddsR (mergeR r s)) t)))) _ _))) _ _))

  joinH : ∀ X → Hom S (TQ (TQ X)) (TQ X)
  joinH X = record
    { map = record
        { to = joinPre
        ; cong = λ {p} {q} e f →
            Setoid.trans Aˢ (∫-join p f) (Setoid.trans Aˢ (e (∫ᶠ f)) (Setoid.sym Aˢ (∫-join q f)))
        }
    ; map-random = λ {β} w → record
        { a = JoinWit.a′ w ; g = JoinWit.g′ w ; g-ok = JoinWit.gok′ w ; g-pr = JoinWit.gpr′ w ; w-eq = JoinWit.eq′ w }
    }

  ----------------------------------------------------------------------------
  -- the monad

  -- the monad laws follow from the integral equations (`QBS.IntegralMonad`)
  integral : Integral S Aˢ (L.suc L.zero)
  integral = record
    { tests = record
        { Test = λ X → Hom S X AQ
        ; eval = λ f x → proj₁ (map f ⟨$⟩ x)
        ; eval-cong = λ f e → Func.cong (map f) e
        ; _∘ᵗ_ = _∘H_ S
        ; eval-∘ = λ _ _ _ → Setoid.refl Aˢ
        }
    ; TQ = TQ
    ; ∫ = λ X p f → ∫ {X} p f
    ; ∫-ext = λ _ e → e
    ; ∫-cong = λ X p e → I-cong (m p) (λ r → e (α p ⟨$⟩ r)) _ _
    ; ∫ᶠ = λ X f → ∫ᶠ {X} f
    ; eval-∫ᶠ = λ _ _ _ → Setoid.refl Aˢ
    }

  monadData : MonadData integral
  monadData = record
    { TH = TH
    ; ηH = ηH
    ; joinH = joinH
    ; ∫-map = λ f p g → ∫-map f p g
    ; ∫-η = λ _ _ _ → Setoid.refl Aˢ
    ; ∫-join = λ X → ∫-join {X}
    }

  open Laws integral monadData public using (TF; ηN; μN)

  -- `TM` is written out (not `Laws.TM`): with the generic `TM`, `Continuous/Strong` was ~17 % slower to check
  TM : Monad (QBSCat S)
  TM = record
    { F = TF
    ; η = ηN
    ; μ = μN
    ; assoc = λ {X} {p} f →
        Setoid.trans Aˢ (∫-join (mapPre (joinH X) p) f)
          (Setoid.trans Aˢ (I-cong (m p) (λ r → ∫-join (α p ⟨$⟩ r) f) _ _)
            (Setoid.sym Aˢ (Setoid.trans Aˢ (∫-join (joinPre p) f) (∫-join p (∫ᶠ f)))))
    ; sym-assoc = λ {X} {p} f →
        Setoid.trans Aˢ (Setoid.trans Aˢ (∫-join (joinPre p) f) (∫-join p (∫ᶠ f)))
          (Setoid.sym Aˢ (Setoid.trans Aˢ (∫-join (mapPre (joinH X) p) f)
            (I-cong (m p) (λ r → ∫-join (α p ⟨$⟩ r) f) _ _)))
    ; identityˡ = λ {X} {p} f →
        Setoid.trans Aˢ (∫-join (mapPre (ηH X) p) f) (I-cong (m p) (λ r → Setoid.refl Aˢ) _ _)
    ; identityʳ = λ {X} {p} f → ∫-join (ηPre p) f
    }
