{-# OPTIONS --safe --without-K #-}

-- Function spaces `Y^X` (random elements: maps R → Y^X that uncurry to a hom ℛ × X ⇒ Y) and the canonical `CartesianClosed (QBSCat S)`.
module QBS.Exponential where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (lower)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
import Function.Construct.Identity as Id
open import Categories.Category.Instance.Setoids using (Setoids)
import Categories.Category.SubCategory.SubHom as SH
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.CartesianClosed.Canonical using (CartesianClosed)
open import Categories.Object.Product using (Product)

open import QBS.Core
open import QBS.Category
open import QBS.Limits
open import QBS.Probes using (ℛQ; probe)
open import QBS.Pieces

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open SH (Setoids ℓ ℓ) using (mem; reads) renaming (probe to witness)
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
      measHom {f} m = record { map = f ; map-random = meas-∘ m }

      -- f × id : ℛ × X ⇒ ℛ × X
      preRX : ∀ {f} → Meas f → Hom S RX RX
      preRX m = ⟨_,_⟩ (product S {ℛQ S} {X}) (_∘H_ S (measHom m) (π₁ (product S {ℛQ S} {X})))
                                           (π₂ (product S {ℛQ S} {X}))

      -- glue a family of morphisms ℛ × X ⇒ Y along a measurable partition
      glueRX : ∀ {j} → Idx j → (u : ℕ → Hom S RX Y) → Hom S RX Y
      glueRX {j} ij u = record
        { map = glueₛ (j ∘ₛ proj₁ₛ) (λ n → map (u n))
        ; map-random = λ {α} m →
            let pβ = rand-fst S {ℛQ S} {X} {α} m
                pγ = rand-snd S {ℛQ S} {X} {α} m in
            random-resp Y (glueₛ-pre {j = j ∘ₛ proj₁ₛ} (λ n → map (u n)) α)
              (glue-random Y (idx-pre ij pβ) (λ n → map (u n) ∘ₛ α)
                (λ n → map-random (u n) (rand-pair S {ℛQ S} {X} {α} pβ pγ)))
        }

    -- Y^X: a map R → Y^X is random when it uncurries to a morphism ℛ × X → Y.
    _⇨Q_ : QBS S
    _⇨Q_ = record
      { Carrier = HomS
      ; probes = fromPred measurable HomS
          (λ α → Σ (Hom S RX Y) λ u →
              ∀ r x → Setoid._≈_ (Carrier Y) (map u ⟨$⟩ (r , x)) (map (α ⟨$⟩ r) ⟨$⟩ x))
          (λ φ → _∘H_ S φ (π₂ (product S {ℛQ S} {X})) , λ r x → Setoid.refl (Carrier Y))
          (λ (u , q) m → _∘H_ S u (preRX (meas₀ m)) , λ r x → q _ x)
      ; glue-random = λ {j} ij α p →
          let q = λ n → witness (p n) in
          mem (glueₛ j (λ n → proj₁ (q n))
              , glueRX ij (λ n → proj₁ (proj₂ (q n)))
              , λ r x → proj₂ (proj₂ (q (lower (j ⟨$⟩ r)))) r x)
            (λ {r} → reads (p (lower (j ⟨$⟩ r))) {r})
      }

  open Category (QBSCat S)

  evalQ : ∀ {X Y} → Hom S (_×Q_ S (_⇨Q_ X Y) X) Y
  evalQ {X} {Y} = record
    { map = record
        { to = λ (φ , x) → map φ ⟨$⟩ x
        ; cong = λ { {φ , x} {φ′ , x′} (e , ex) →
            Setoid.trans (Carrier Y) (e {x}) (Func.cong (map φ′) ex) }
        }
    ; map-random = λ {α} m →
        let a = rand-fst S {_⇨Q_ X Y} {X} m
            pγ = rand-snd S {_⇨Q_ X Y} {X} m
            u = proj₁ (proj₂ (witness a))
            q = proj₂ (proj₂ (witness a)) in
        random-resp Y
          (λ r → Setoid.trans (Carrier Y) (q r (proj₂ (α ⟨$⟩ r))) (reads a {r} {proj₂ (α ⟨$⟩ r)}))
          (map-random u {< Id.function Rˢ , proj₂ₛ ∘ₛ α >ₛ} (rand-pair S {ℛQ S} {X} meas-id pγ))
    }

  curryQ : ∀ {C X Y} → Hom S (_×Q_ S C X) Y → Hom S C (_⇨Q_ X Y)
  curryQ {C} {X} {Y} g = record { map = curryF ; map-random = curryR }
    where
      curryF : Func (Carrier C) (HomS X Y)
      curryF = record
        { to = λ c → record
            { map = record
                { to = λ x → map g ⟨$⟩ (c , x)
                ; cong = λ e → Func.cong (map g) (Setoid.refl (Carrier C) , e)
                }
            ; map-random = λ {α} p → map-random g (rand-pair S {C} {X} {< constₛ c , α >ₛ} (const-random C c) p)
            }
        ; cong = λ e {x} → Func.cong (map g) (e , Setoid.refl (Carrier X))
        }

      curryR : ∀ {α} → Random C α → Random (_⇨Q_ X Y) (curryF ∘ₛ α)
      curryR {α} p =
        mem ( curryF ∘ₛ α
            , _∘H_ S g (pairQ S {_×Q_ S (ℛQ S) X} {C} {X} (_∘H_ S (probe S p) (fstQ S {ℛQ S} {X})) (sndQ S {ℛQ S} {X}))
            , λ r x → Setoid.refl (Carrier Y))
          (λ {r} {x} → Setoid.refl (Carrier Y))

  curry-uniq : ∀ {C X Y : QBS S} (f : Hom S C (_⇨Q_ X Y)) (g : Hom S (_×Q_ S C X) Y) →
    _≈H_ S (_∘H_ S evalQ (pairQ S (_∘H_ S f (fstQ S {C} {X})) (_∘H_ S (idH S) (sndQ S {C} {X})))) g →
    _≈H_ S f (curryQ g)
  curry-uniq f g p {c} {x} = p {c , x}

  cartesianClosed : CartesianClosed (QBSCat S)
  cartesianClosed = record
    { ⊤ = 1Q S
    ; _×_ = _×Q_ S
    ; ! = !Q S
    ; π₁ = λ {A} {B} → fstQ S {A} {B}
    ; π₂ = λ {A} {B} → sndQ S {A} {B}
    ; ⟨_,_⟩ = λ f g → pairQ S f g
    ; !-unique = λ _ → refl
    ; π₁-comp = λ {_} {A} → Setoid.refl (Carrier A)
    ; π₂-comp = λ {_} {_} {_} {B} {_} → Setoid.refl (Carrier B)
    ; ⟨,⟩-unique = λ {_} {A} {B} p q → Setoid.sym (Carrier A) p , Setoid.sym (Carrier B) q
    ; _^_ = λ B A → _⇨Q_ A B
    ; eval = λ {B} {A} → evalQ {A} {B}
    ; curry = λ {C} {A} {B} g → curryQ {C} {A} {B} g
    ; eval-comp = λ {B} → Setoid.refl (Carrier B)
    ; curry-unique = λ {C} {B} {A} {f} {g} → curry-uniq {C} {A} {B} f g
    }
