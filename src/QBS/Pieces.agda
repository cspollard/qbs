{-# OPTIONS --safe --without-K #-}

-- Smart constructors for `Probes` from pieces: a set of pieces read off as maps Rˢ → X (`fromPieces`), and the
-- special case of a predicate on those maps (`fromPred`).  They depend only on `MeasurableMaps`, so the random
-- sources themselves can use them.
module QBS.Pieces where

open import Level using (Level)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat)
open import Data.Unit.Polymorphic.Base using (⊤)

import Categories.Category.SubCategory.SubHom as SH

open import QBS.Core

module _ {ℓ} {sc : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})} (M : MeasurableMaps sc) where
  open MeasurableMaps M
  open SH (Setoids ℓ ℓ) using (mem)

  -- probes from a set `P` of pieces with a reading `ι` as maps Rˢ → X, precomposition `pre` by measurable maps
  -- (compatible with `ι`) and every constant a piece.  Pieces are equal when their readings are, so `ι` is
  -- injective and hence a mono.
  fromPieces : (X : Setoid ℓ ℓ) (P : Set ℓ) (ι : P → Func Rˢ X) (pre : ∀ {f} → P → Meas₀ f → P) →
    (pre-ι : ∀ {f} (c : P) (m : Meas₀ f) r → Setoid._≈_ X (ι (pre c m) ⟨$⟩ r) (ι c ⟨$⟩ (f ⟨$⟩ r))) →
    (pt : ∀ x → Σ P λ c → ∀ r → Setoid._≈_ X (ι c ⟨$⟩ r) x) → Probes M X
  fromPieces X P ι pre pre-ι pt = record
    { subhom = record
        { F = record
            { F₀ = λ _ → record
                { Carrier = P
                ; _≈_ = λ a b → ∀ {r : Setoid.Carrier Rˢ} → (ι a ⟨$⟩ r) ≈ᵖ (ι b ⟨$⟩ r)
                ; isEquivalence = record
                    { refl = Setoid.refl X ; sym = λ e → Setoid.sym X e ; trans = λ e e′ → Setoid.trans X e e′ }
                }
            ; F₁ = λ (f , mf) → record
                { to = λ c → pre c mf
                ; cong = λ {c} {c′} e {r} →
                    Setoid.trans X (pre-ι c mf r) (Setoid.trans X (e {f ⟨$⟩ r}) (Setoid.sym X (pre-ι c′ mf r)))
                }
            ; identity = λ {_} {c} → pre-ι c (SubCat.Rid sc) _
            ; homomorphism = λ {_} {_} {_} {f} {g} {c} {r} →
                Setoid.trans X (pre-ι c (SubCat._∘R_ sc (proj₂ f) (proj₂ g)) r)
                  (Setoid.sym X (Setoid.trans X (pre-ι (pre c (proj₂ f)) (proj₂ g) r)
                    (pre-ι c (proj₂ f) (proj₁ g ⟨$⟩ r))))
            ; F-resp-≈ = λ {_} {_} {f} {g} e {c} {r} →
                Setoid.trans X (pre-ι c (proj₂ f) r)
                  (Setoid.trans X (Func.cong (ι c) e) (Setoid.sym X (pre-ι c (proj₂ g) r)))
            }
        ; ι = record
            { η = λ _ → record { to = ι ; cong = λ e → e }
            ; commute = λ (f , mf) {c} {r} → pre-ι c mf r
            ; sym-commute = λ (f , mf) {c} {r} → Setoid.sym X (pre-ι c mf r)
            }
        ; ι-mono = SH.inj⇒mono _ _ _ _ (λ e → e)
        }
    ; const-image = λ x → mem (proj₁ (pt x)) (λ {r} → proj₂ (pt x) r)
    }
    where _≈ᵖ_ = Setoid._≈_ X

  -- probes from a predicate on the maps Rˢ → X containing the constants and closed under measurable precomposition
  -- (closure under ≈ is derived: the random elements are the image of `ι`)
  fromPred : (X : Setoid ℓ ℓ) (Random₀ : Func Rˢ X → Set ℓ) →
    (∀ x → Random₀ (constₛ x)) → (∀ {α f} → Random₀ α → Meas₀ f → Random₀ (α ∘ₛ f)) → Probes M X
  fromPred X Random₀ const₀ pre₀ = fromPieces X (Σ (Func Rˢ X) Random₀) proj₁
    (λ {f} (α , p) m → α ∘ₛ f , pre₀ p m) (λ _ _ _ → Setoid.refl X)
    (λ x → (constₛ x , const₀ x) , λ _ → Setoid.refl X)
