{-# OPTIONS --safe --without-K #-}

module QBS.Limits where

open import Level using (Level; suc; _⊔_; Lift; lift)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)
open import Categories.Diagram.Equalizer using (Equalizer)

open import QBS.Core
open import QBS.Category

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  -- Terminal object: every element is random.
  1Q : QBS S
  1Q = record
    { Carrier = setoid (⊤ {ℓ})
    ; Random = λ _ → ⊤
    ; random-resp = λ _ _ → tt
    ; const-random = λ _ → tt
    ; pre-random = λ _ _ → tt
    ; glue-random = λ _ _ _ → tt
    }

  !Q : ∀ {X} → Hom S X 1Q
  !Q = record { map = record { to = λ _ → tt ; cong = λ _ → refl } ; map-random = λ _ → tt }

  -- Binary products: a pair is random iff both components are.
  _×Q_ : QBS S → QBS S → QBS S
  X ×Q Y = record
    { Carrier = ×-setoid (Carrier X) (Carrier Y)
    ; Random = λ α → Random X (proj₁ ∘ α) × Random Y (proj₂ ∘ α)
    ; random-resp = λ e (p , q) →
        random-resp X (λ r → proj₁ (e r)) p , random-resp Y (λ r → proj₂ (e r)) q
    ; const-random = λ _ → const-random X _ , const-random Y _
    ; pre-random = λ (p , q) m → pre-random X p m , pre-random Y q m
    ; glue-random = λ i α p →
        glue-random X i (λ n → proj₁ ∘ α n) (λ n → proj₁ (p n)) ,
        glue-random Y i (λ n → proj₂ ∘ α n) (λ n → proj₂ (p n))
    }

  -- Equalizers: the subspace on which two maps agree.
  EqQ : ∀ {X Y} → Hom S X Y → Hom S X Y → QBS S
  EqQ {X} {Y} f g = record
    { Carrier = record
        { Carrier = Σ ∣ X ∣ (λ x → Setoid._≈_ (Carrier Y) (map f ⟨$⟩ x) (map g ⟨$⟩ x))
        ; _≈_ = λ a b → Setoid._≈_ (Carrier X) (proj₁ a) (proj₁ b)
        ; isEquivalence = record
            { refl = Setoid.refl (Carrier X)
            ; sym = Setoid.sym (Carrier X)
            ; trans = Setoid.trans (Carrier X)
            }
        }
    ; Random = λ α → Random X (proj₁ ∘ α)
    ; random-resp = λ e → random-resp X e
    ; const-random = λ (x , _) → const-random X x
    ; pre-random = pre-random X
    ; glue-random = λ i α p → glue-random X i (λ n → proj₁ ∘ α n) p
    }

  fstQ : ∀ {X Y} → Hom S (X ×Q Y) X
  fstQ = record { map = record { to = proj₁ ; cong = proj₁ } ; map-random = proj₁ }

  sndQ : ∀ {X Y} → Hom S (X ×Q Y) Y
  sndQ = record { map = record { to = proj₂ ; cong = proj₂ } ; map-random = proj₂ }

  pairQ : ∀ {C X Y} → Hom S C X → Hom S C Y → Hom S C (X ×Q Y)
  pairQ f g = record
    { map = record
        { to = λ x → map f ⟨$⟩ x , map g ⟨$⟩ x
        ; cong = λ e → Func.cong (map f) e , Func.cong (map g) e
        }
    ; map-random = λ p → map-random f p , map-random g p
    }

  open Category (QBSCat S)

  terminal : Terminal (QBSCat S)
  terminal = record
    { ⊤ = 1Q
    ; ⊤-is-terminal = record { ! = !Q ; !-unique = λ _ _ → refl }
    }

  product : ∀ {X Y} → Product (QBSCat S) X Y
  product {X} {Y} = record
    { A×B = X ×Q Y
    ; π₁ = fstQ {X} {Y}
    ; π₂ = sndQ {X} {Y}
    ; ⟨_,_⟩ = λ f g → pairQ f g
    ; project₁ = λ _ → Setoid.refl (Carrier X)
    ; project₂ = λ _ → Setoid.refl (Carrier Y)
    ; unique = λ p q x → Setoid.sym (Carrier X) (p x) , Setoid.sym (Carrier Y) (q x)
    }

  equalizer : ∀ {X Y} (f g : Hom S X Y) → Equalizer (QBSCat S) f g
  equalizer {X} f g = record
    { obj = EqQ f g
    ; arr = record
        { map = record { to = proj₁ ; cong = λ e → e }
        ; map-random = λ p → p
        }
    ; isEqualizer = record
        { equality = λ x → proj₂ x
        ; equalize = λ {_} {h} eq → record
            { map = record
                { to = λ x → map h ⟨$⟩ x , eq x
                ; cong = Func.cong (map h)
                }
            ; map-random = map-random h
            }
        ; universal = λ {_} {h} {eq} x → Setoid.refl (Carrier X)
        ; unique = λ {_} {h} {i} {eq} p x → Setoid.sym (Carrier X) (p x)
        }
    }

  finitelyComplete : FinitelyComplete (QBSCat S)
  finitelyComplete = record
    { cartesian = record
        { terminal = terminal
        ; products = record { product = product }
        }
    ; equalizer = equalizer
    }
