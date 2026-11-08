{-# OPTIONS --safe --without-K #-}

-- Finite limits in QBSCat S: terminal object, binary products, equalizers (`FinitelyComplete`).
module QBS.Limits where

open import Level using (lower)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Object.Product using (Product)
open import Categories.Diagram.Equalizer using (Equalizer)

import Categories.Category.SubCategory.SubHom as SH

open import QBS.Core
open import QBS.Pieces
open import QBS.Category

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)
  open QBS
  open Hom

  -- The codiscrete QBS on a setoid: every sequence is random (the pieces are the maps themselves).
  CodiscQ : Setoid ℓ ℓ → QBS S
  CodiscQ A = record
    { Carrier = A
    ; probes = record
        { subhom = record
            { F = record
                { F₀ = λ _ → FuncS
                ; F₁ = λ (f , _) → record { to = λ α → α ∘ₛ f ; cong = λ e {r} → e {f ⟨$⟩ r} }
                ; identity = Setoid.refl A
                ; homomorphism = Setoid.refl A
                ; F-resp-≈ = λ e {α} → Func.cong α e
                }
            ; ι = record { η = λ _ → Id.function FuncS ; commute = λ _ → Setoid.refl A ; sym-commute = λ _ → Setoid.refl A }
            ; ι-mono = SH.inj⇒mono _ _ _ _ (λ e → e)
            }
        ; const-image = λ x → mem (constₛ x) (Setoid.refl A)
        }
    ; glue-random = λ {i} _ α _ → mem (glueₛ i α) (Setoid.refl A)
    }
    where
      _≈ᵃ_ = Setoid._≈_ A
      FuncS : Setoid ℓ ℓ
      FuncS = record
        { Carrier = Func Rˢ A
        ; _≈_ = λ α β → ∀ {r} → (α ⟨$⟩ r) ≈ᵃ (β ⟨$⟩ r)
        ; isEquivalence = record
            { refl = Setoid.refl A
            ; sym = λ e → Setoid.sym A e
            ; trans = λ e e′ → Setoid.trans A e e′
            }
        }

  -- every sequence is random in a codiscrete QBS
  codisc-random : ∀ (A : Setoid ℓ ℓ) (α : Func Rˢ A) → Random (CodiscQ A) α
  codisc-random A α = mem α (Setoid.refl A)


  -- Terminal object: every element is random.
  1Q : QBS S
  1Q = CodiscQ (setoid (⊤ {ℓ}))

  !Q : ∀ {X} → Hom S X 1Q
  !Q = record
    { map = record { to = λ _ → tt ; cong = λ _ → refl }
    ; map-random = λ _ → codisc-random (setoid (⊤ {ℓ})) _
    }

  -- Binary products: a pair is random iff both components are.
  _×Q_ : QBS S → QBS S → QBS S
  _×Q_ X Y .QBS.Carrier = ×-setoid (Carrier X) (Carrier Y)
  _×Q_ X Y .QBS.probes = fromPred measurable (×-setoid (Carrier X) (Carrier Y))
    (λ α → Random X (proj₁ₛ ∘ₛ α) × Random Y (proj₂ₛ ∘ₛ α))
    (λ _ → const-random X _ , const-random Y _)
    (λ (p , q) m → pre-random X p (meas₀ m) , pre-random Y q (meas₀ m))
  _×Q_ X Y .QBS.glue-random {i} = λ ii α p →
    let q = λ n → probe (p n)
        β = λ n → proj₁ (q n) in
    mem
      ( glueₛ i β
      , random-resp X (glueₛ-∘ {j = i} proj₁ₛ β)
          (glue-random X ii (λ n → proj₁ₛ ∘ₛ β n) (λ n → proj₁ (proj₂ (q n))))
      , random-resp Y (glueₛ-∘ {j = i} proj₂ₛ β)
          (glue-random Y ii (λ n → proj₂ₛ ∘ₛ β n) (λ n → proj₂ (proj₂ (q n)))) )
      (λ {r} → reads (p (lower (i ⟨$⟩ r))) {r})

  -- Equalizers: the subspace on which two maps agree.
  EqQ : ∀ {X Y} → Hom S X Y → Hom S X Y → QBS S
  EqQ {X} {Y} f g = record
    { Carrier = EqS
    ; probes = fromPred measurable EqS (λ α → Random X (ι ∘ₛ α))
        (λ (x , _) → const-random X x) (λ p m → pre-random X p (meas₀ m))
    ; glue-random = λ {i} ii α p →
        let q = λ n → probe (p n)
            β = λ n → proj₁ (q n) in
        mem (glueₛ i β , random-resp X (glueₛ-∘ {j = i} ι β)
               (glue-random X ii (λ n → ι ∘ₛ β n) (λ n → proj₂ (q n))))
          (λ {r} → reads (p (lower (i ⟨$⟩ r))) {r})
    }
    where
      EqS : Setoid ℓ ℓ
      EqS = On.setoid (Carrier X) (proj₁ {B = λ x → Setoid._≈_ (Carrier Y) (map f ⟨$⟩ x) (map g ⟨$⟩ x)})
      ι : Func EqS (Carrier X)
      ι = record { to = proj₁ ; cong = λ e → e }

  -- a map into a product is random iff both components are
  rand-fst : ∀ {X Y} {α} → Random (X ×Q Y) α → Random X (proj₁ₛ ∘ₛ α)
  rand-fst {X} a = random-resp X (λ r → proj₁ (reads a {r})) (proj₁ (proj₂ (probe a)))

  rand-snd : ∀ {X Y} {α} → Random (X ×Q Y) α → Random Y (proj₂ₛ ∘ₛ α)
  rand-snd {Y = Y} a = random-resp Y (λ r → proj₂ (reads a {r})) (proj₂ (proj₂ (probe a)))

  rand-pair : ∀ {X Y} {α} → Random X (proj₁ₛ ∘ₛ α) → Random Y (proj₂ₛ ∘ₛ α) → Random (X ×Q Y) α
  rand-pair {X} {Y} {α} p q = mem (α , p , q) (Setoid.refl (Carrier X) , Setoid.refl (Carrier Y))

  fstQ : ∀ {X Y} → Hom S (X ×Q Y) X
  fstQ = record { map = record { to = proj₁ ; cong = proj₁ } ; map-random = rand-fst }

  sndQ : ∀ {X Y} → Hom S (X ×Q Y) Y
  sndQ = record { map = record { to = proj₂ ; cong = proj₂ } ; map-random = rand-snd }

  pairQ : ∀ {C X Y} → Hom S C X → Hom S C Y → Hom S C (X ×Q Y)
  pairQ f g = record
    { map = record
        { to = λ x → map f ⟨$⟩ x , map g ⟨$⟩ x
        ; cong = λ e → Func.cong (map f) e , Func.cong (map g) e
        }
    ; map-random = λ p → rand-pair (map-random f p) (map-random g p)
    }

  open Category (QBSCat S)

  terminal : Terminal (QBSCat S)
  terminal = record
    { ⊤ = 1Q
    ; ⊤-is-terminal = record { ! = !Q ; !-unique = λ _ → refl }
    }

  product : ∀ {X Y} → Product (QBSCat S) X Y
  product {X} {Y} = record
    { A×B = X ×Q Y
    ; π₁ = fstQ {X} {Y}
    ; π₂ = sndQ {X} {Y}
    ; ⟨_,_⟩ = λ f g → pairQ f g
    ; project₁ = Setoid.refl (Carrier X)
    ; project₂ = Setoid.refl (Carrier Y)
    ; unique = λ p q → Setoid.sym (Carrier X) p , Setoid.sym (Carrier Y) q
    }

  equalizer : ∀ {X Y} (f g : Hom S X Y) → Equalizer (QBSCat S) f g
  equalizer {X} {Y} f g = record
    { obj = EqQ f g
    ; arr = record
        { map = record { to = proj₁ ; cong = λ e → e }
        ; map-random = λ {α} a → random-resp X (λ r → reads a {r}) (proj₂ (probe a))
        }
    ; isEqualizer = record
        { equality = λ {x} → proj₂ x
        ; equalize = λ {_} {h} eq → record
            { map = record
                { to = λ x → map h ⟨$⟩ x , eq {x}
                ; cong = Func.cong (map h)
                }
            ; map-random = λ {α} p →
                mem
                  ( record { to = λ r → map h ⟨$⟩ (α ⟨$⟩ r) , eq {α ⟨$⟩ r}
                           ; cong = λ e → Func.cong (map h) (Func.cong α e) }
                  , map-random h p)
                  (Setoid.refl (Carrier X))
            }
        ; universal = λ {_} {h} {eq} → Setoid.refl (Carrier X)
        ; unique = λ {_} {h} {i} {eq} p → Setoid.sym (Carrier X) p
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
