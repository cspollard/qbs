{-# OPTIONS --safe --without-K #-}

module QBS.Exponential where

open import Level using (Level; suc)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Categories.Category.Core using (Category)
open import Categories.Category.CartesianClosed.Canonical using (CartesianClosed)
open import Categories.Object.Product using (Product)

open import QBS.Core
open import QBS.Category
open import QBS.Limits
open import QBS.Probes using (ℛQ; probe)

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom
  open Product

  module _ (X Y : QBS S) where
    HomS : Setoid ℓ ℓ
    HomS = record
      { Carrier = Hom S X Y
      ; _≈_ = _≈H_ S
      ; isEquivalence = Category.equiv (QBSCat S)
      }

    private
      RX : QBS S
      RX = _×Q_ S (ℛQ S) X

      -- the measurable map R → R as a morphism ℛ ⇒ ℛ
      measHom : ∀ {f} → Meas f → Hom S (ℛQ S) (ℛQ S)
      measHom {f} m = record
        { map = record { to = f ; cong = λ { refl → refl } }
        ; map-random = meas-∘ m
        }

      -- f × id : ℛ × X ⇒ ℛ × X
      preRX : ∀ {f} → Meas f → Hom S RX RX
      preRX m = ⟨_,_⟩ (product S {ℛQ S} {X}) (_∘H_ S (measHom m) (π₁ (product S {ℛQ S} {X})))
                                           (π₂ (product S {ℛQ S} {X}))

      -- glue a family of morphisms ℛ × X ⇒ Y along a measurable partition
      glueRX : ∀ {j} → Idx j → (u : ℕ → Hom S RX Y) → Hom S RX Y
      glueRX {j} ij u = record
        { map = record
            { to = λ (r , x) → map (u (j r)) ⟨$⟩ (r , x)
            ; cong = λ { {r , x} {.r , y} (refl , e) → Func.cong (map (u (j r))) (refl , e) }
            }
        ; map-random = λ {α} (pβ , pγ) →
            glue-random Y (idx-pre ij pβ) (λ n s → map (u n) ⟨$⟩ (proj₁ (α s) , proj₂ (α s)))
              (λ n → map-random (u n) (pβ , pγ))
        }

    -- Y^X: a map R → Y^X is random when it uncurries to a morphism ℛ × X → Y.
    _⇨Q_ : QBS S
    _⇨Q_ = record
      { Carrier = HomS
      ; Random = λ α → Σ (Hom S RX Y) λ u →
          ∀ r x → Setoid._≈_ (Carrier Y) (map u ⟨$⟩ (r , x)) (map (α r) ⟨$⟩ x)
      ; random-resp = λ e (u , q) →
          u , λ r x → Setoid.trans (Carrier Y) (q r x) (e r x)
      ; const-random = λ φ →
          _∘H_ S φ (π₂ (product S {ℛQ S} {X})) , λ r x → Setoid.refl (Carrier Y)
      ; pre-random = λ (u , q) m →
          _∘H_ S u (preRX m) , λ r x → q _ x
      ; glue-random = λ {j} ij α p →
          glueRX ij (λ n → proj₁ (p n)) , λ r x → proj₂ (p (j r)) r x
      }

  open Category (QBSCat S)

  evalQ : ∀ {X Y} → Hom S (_×Q_ S (_⇨Q_ X Y) X) Y
  evalQ {X} {Y} = record
    { map = record
        { to = λ (φ , x) → map φ ⟨$⟩ x
        ; cong = λ { {φ , x} {φ′ , x′} (e , ex) →
            Setoid.trans (Carrier Y) (e x) (Func.cong (map φ′) ex) }
        }
    ; map-random = λ {α} ((u , q) , pγ) →
        random-resp Y (λ r → q r (proj₂ (α r))) (map-random u (meas-id , pγ))
    }

  curryQ : ∀ {C X Y} → Hom S (_×Q_ S C X) Y → Hom S C (_⇨Q_ X Y)
  curryQ {C} {X} {Y} g = record
    { map = record
        { to = λ c → record
            { map = record
                { to = λ x → map g ⟨$⟩ (c , x)
                ; cong = λ e → Func.cong (map g) (Setoid.refl (Carrier C) , e)
                }
            ; map-random = λ p → map-random g (const-random C c , p)
            }
        ; cong = λ e x → Func.cong (map g) (e , Setoid.refl (Carrier X))
        }
    ; map-random = λ {α} p →
        _∘H_ S g (pairQ S {_×Q_ S (ℛQ S) X} {C} {X} (_∘H_ S (probe S p) (fstQ S {ℛQ S} {X})) (sndQ S {ℛQ S} {X}))
        , λ r x → Setoid.refl (Carrier Y)
    }

  curry-uniq : ∀ {C X Y : QBS S} (f : Hom S C (_⇨Q_ X Y)) (g : Hom S (_×Q_ S C X) Y) →
    _≈H_ S (_∘H_ S evalQ (pairQ S (_∘H_ S f (fstQ S {C} {X})) (_∘H_ S (idH S) (sndQ S {C} {X})))) g →
    _≈H_ S f (curryQ g)
  curry-uniq f g p c x = p (c , x)

  cartesianClosed : CartesianClosed (QBSCat S)
  cartesianClosed = record
    { ⊤ = 1Q S
    ; _×_ = _×Q_ S
    ; ! = !Q S
    ; π₁ = λ {A} {B} → fstQ S {A} {B}
    ; π₂ = λ {A} {B} → sndQ S {A} {B}
    ; ⟨_,_⟩ = λ f g → pairQ S f g
    ; !-unique = λ _ _ → refl
    ; π₁-comp = λ {_} {A} _ → Setoid.refl (Carrier A)
    ; π₂-comp = λ {_} {_} {_} {B} {_} _ → Setoid.refl (Carrier B)
    ; ⟨,⟩-unique = λ {_} {A} {B} p q x → Setoid.sym (Carrier A) (p x) , Setoid.sym (Carrier B) (q x)
    ; _^_ = λ B A → _⇨Q_ A B
    ; eval = λ {B} {A} → evalQ {A} {B}
    ; curry = λ {C} {A} {B} g → curryQ {C} {A} {B} g
    ; eval-comp = λ {B} _ → Setoid.refl (Carrier B)
    ; curry-unique = λ {C} {B} {A} {f} {g} → curry-uniq {C} {A} {B} f g
    }
