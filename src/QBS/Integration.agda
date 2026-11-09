{-# OPTIONS --safe --without-K #-}

-- Integration as one natural transformation.
-- On the category 𝕄 of measurable maps (the one-object sub-category `subcat` of a random source):
--   * `Test : 𝕄ᵒᵖ ⇒ Setoids` is the presheaf of test functions (precomposition with measurable maps);
--   * `M : 𝕄 ⇒ Setoids` is the covariant functor of measures (pushforward);
--   * `Dual Test V : 𝕄 ⇒ Setoids`, `R ↦ (Test R ⇒ V)`, is the double dual: covariant, because `Test` is
--     contravariant and `Hom(–, V)` flips it back.
-- An integration is a natural transformation `∫ : M ⇒ Dual Test V`.  Naturality is exactly
--   ∫ (f_* μ) h = ∫ μ (h ∘ f),
-- so a measure is a generalised element of the double dual of the test functions.  By Yoneda this is the same
-- as a family `M R × Test R → V` that is dinatural in `R`, i.e. a cowedge `Test × M ⇒ ΔV`.
module QBS.Integration where

open import Level using (Level; suc; _⊔_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Construct.On as On

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom using (module Hom)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

-- the double dual of a presheaf of test functions, with values in `V`
module _ {o ℓ e} {𝕄 : Category o ℓ e} {c} (Test : Presheaf 𝕄 (Setoids c c)) (V : Setoid c c) where
  open Hom (Setoids c c) using (Hom[-,_])

  Dual : Functor 𝕄 (Setoids c c)
  Dual = Hom[-, V ] ∘F Functor.op Test

  record Integration : Set (o ⊔ ℓ ⊔ e ⊔ suc c) where
    field
      M : Functor 𝕄 (Setoids c c)
      ∫ : NaturalTransformation M Dual

  -- Raw measures with an integral map into the double dual.  Given a pushforward on raw measures that the integral
  -- intertwines with the action of `Dual`, the raw measures modulo equal integrals form a functor `M` (its laws are
  -- those of `Dual`) and `∫` is the inclusion, natural by `⟦⟧-push`.  Only the intertwining law has to be proved
  -- for a model; the functor laws of the measures are never stated.
  record RawIntegration : Set (o ⊔ ℓ ⊔ e ⊔ suc c) where
    private module D = Functor Dual
    field
      Raw : Category.Obj 𝕄 → Set c
      push : ∀ {A B} → Category._⇒_ 𝕄 A B → Raw A → Raw B
      ⟦_⟧ : ∀ {A} → Raw A → Setoid.Carrier (D.F₀ A)
      ⟦⟧-push : ∀ {A B} (f : Category._⇒_ 𝕄 A B) (μ : Raw A) →
        Setoid._≈_ (D.F₀ B) ⟦ push f μ ⟧ (D.F₁ f ⟨$⟩ ⟦ μ ⟧)

  fromRaw : RawIntegration → Integration
  fromRaw R = record
    { M = record
        { F₀ = λ A → On.setoid (D.F₀ A) ⟦_⟧
        ; F₁ = λ f → record
            { to = push f
            ; cong = λ {μ} {ν} e {h} →
                tr (⟦⟧-push f μ {h}) (tr (Func.cong (D.F₁ f) {⟦ μ ⟧} {⟦ ν ⟧} (λ {k} → e {k}) {h}) (sy (⟦⟧-push f ν {h})))
            }
        ; identity = λ {_} {μ} {h} → tr (⟦⟧-push _ μ {h}) (D.identity {x = ⟦ μ ⟧} {h})
        ; homomorphism = λ {_} {_} {_} {f} {g} {μ} {h} →
            tr (⟦⟧-push _ μ {h}) (tr (D.homomorphism {f = f} {g = g} {⟦ μ ⟧} {h})
              (tr (Func.cong (D.F₁ g) {D.F₁ f ⟨$⟩ ⟦ μ ⟧} {⟦ push f μ ⟧}
                (λ {k} → sy (⟦⟧-push f μ {k})) {h}) (sy (⟦⟧-push g (push f μ) {h}))))
        ; F-resp-≈ = λ {_} {_} {f} {g} e {μ} {h} →
            tr (⟦⟧-push f μ {h}) (tr (D.F-resp-≈ e {⟦ μ ⟧} {h}) (sy (⟦⟧-push g μ {h})))
        }
    ; ∫ = ntHelper record { η = λ _ → record { to = ⟦_⟧ ; cong = λ e → e } ; commute = λ f {μ} → ⟦⟧-push f μ }
    }
    where
      open RawIntegration R
      module D = Functor Dual
      tr = Setoid.trans V
      sy = Setoid.sym V

  -- Measures on a space `X` that is not itself an object of 𝕄, described through the object `ℛ`.
  -- Parameters:
  --   * `R`     : the raw measures and their integral on every object of 𝕄;
  --   * `ℛ`     : the object of 𝕄 on which the measures live (the sample space);
  --   * `Probe` : the ways of seeing `X` from `ℛ` (the probes `ℛ → X`);
  --   * `Tst`   : the test functions on `X`;
  --   * `comp`  : `comp α f` is the test function `f ∘ α` on `ℛ`, the pullback of `f` along the probe `α`.
  -- A `Pre` is a pair `(α, μ)` of a probe and a raw measure on `ℛ`.  It stands for the pushforward `α_* μ`, a measure
  -- on `X`, and integrates a test `f` to `∫ μ (f ∘ α)`, which is `∫ᵖ`.  This is the map out of the coend
  -- `∫^ℛ Raw ℛ × Probe`, dinatural in `ℛ` by associativity of `∘`.
  -- Why it is useful: `X` has no σ-algebra, so `α_* μ` cannot be formed as a measure on `X`.  A `Pre` is its recipe,
  -- and equal integrals (`_≈ᵖ_`) decide when two recipes are the same measure, so `PreS` is the setoid of measures on
  -- `X`: the image of the pairs in the double dual of the tests on `X`.  Functoriality in `X` (`α ↦ g ∘ α`), the
  -- unit and the bind are all defined on pairs and respect `_≈ᵖ_`, which is how the monad `T X` is built.
  module Pairs (R : RawIntegration) (ℛ : Category.Obj 𝕄) (Probe Tst : Set c)
      (comp : Probe → Tst → Setoid.Carrier (Functor.F₀ Test ℛ)) where
    open RawIntegration R

    -- a measure on `X` before identification: a probe and a raw measure on `ℛ`
    record Pre : Set c where
      constructor _,ᵖ_
      field
        probe : Probe
        raw : Raw ℛ

    abstract
      ∫ᵖ : Pre → Tst → Setoid.Carrier V
      ∫ᵖ p f = ⟦ Pre.raw p ⟧ ⟨$⟩ comp (Pre.probe p) f

      ∫ᵖ-def : ∀ p f → Setoid._≈_ V (∫ᵖ p f) (⟦ Pre.raw p ⟧ ⟨$⟩ comp (Pre.probe p) f)
      ∫ᵖ-def p f = Setoid.refl V

    _≈ᵖ_ : Pre → Pre → Set c
    p ≈ᵖ q = ∀ f → Setoid._≈_ V (∫ᵖ p f) (∫ᵖ q f)

    PreS : Setoid c c
    PreS = record
      { Carrier = Pre
      ; _≈_ = _≈ᵖ_
      ; isEquivalence = record
          { refl = λ _ → Setoid.refl V
          ; sym = λ e f → Setoid.sym V (e f)
          ; trans = λ e e′ f → Setoid.trans V (e f) (e′ f)
          }
      }
