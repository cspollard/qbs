{-# OPTIONS --safe --without-K #-}

-- Indexed products and coproducts over any `I : Set ℓ`; with equalizers/coequalizers, `Complete` and `Cocomplete` (all small limits and colimits).
-- The index type is a plain `Set`, not a setoid, because agda-categories quantifies over `I : Set` in
-- `AllProductsOf`/`AllCoproductsOf`; `≡` on `I` in `ΣEq` is then the equality of the indexing type itself.
module QBS.Complete where

open import Level using (Level; suc; _⊔_; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; subst)
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.Complete using (Complete)
open import Categories.Category.Cocomplete using (Cocomplete)
open import Categories.Category.Complete.Properties.Construction using (AllProducts×Equalizer⇒Complete)
open import Categories.Category.Cocomplete.Properties.Construction using (AllCoproducts×Coequalizer⇒Cocomplete)
open import Categories.Object.Product.Indexed using (IndexedProductOf; AllProductsOf)
open import Categories.Object.Coproduct.Indexed using (IndexedCoproductOf; AllCoproductsOf)

open import QBS.Core
open import QBS.Category
open import QBS.Limits
open import QBS.Colimits

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  module _ {I : Set ℓ} (P : I → QBS S) where

    -- Indexed product: an element is random iff each coordinate is.
    ΠS : Setoid ℓ ℓ
    ΠS = record
      { Carrier = ∀ i → ∣ P i ∣
      ; _≈_ = λ a b → ∀ i → Setoid._≈_ (Carrier (P i)) (a i) (b i)
      ; isEquivalence = record
          { refl = λ i → Setoid.refl (Carrier (P i))
          ; sym = λ e i → Setoid.sym (Carrier (P i)) (e i)
          ; trans = λ e e′ i → Setoid.trans (Carrier (P i)) (e i) (e′ i)
          }
      }

    πₛ : ∀ i → Func ΠS (Carrier (P i))
    πₛ i = record { to = λ a → a i ; cong = λ e → e i }

    ΠQ : QBS S
    ΠQ = record
      { Carrier = ΠS
      ; probes = record
          { Random = λ α → ∀ i → Random (P i) (πₛ i ∘ₛ α)
          ; random-resp = λ e p i → random-resp (P i) (λ r → e r i) (p i)
          ; const-random = λ x i → const-random (P i) (x i)
          ; pre-random = λ p m i → pre-random (P i) (p i) m
          }
      ; glue-random = λ ij α p i →
          random-glue-∘ (P i) (πₛ i) α (glue-random (P i) ij (λ n → πₛ i ∘ₛ α n) (λ n → p n i))
      }

    indexedProduct : IndexedProductOf (QBSCat S) P
    indexedProduct = record
      { X = ΠQ
      ; π = λ i → record
          { map = πₛ i
          ; map-random = λ p → p i
          }
      ; ⟨_⟩ = λ f → record
          { map = record
              { to = λ x i → map (f i) ⟨$⟩ x
              ; cong = λ e i → Func.cong (map (f i)) e
              }
          ; map-random = λ p i → map-random (f i) p
          }
      ; commute = λ {_} {f} {i} → Setoid.refl (Carrier (P i))
      ; unique = λ p {x} i → Setoid.sym (Carrier (P i)) (p {i} {x})
      }

    -- Indexed coproduct: locally on a measurable countable partition, a
    -- random element of a single summand.
    ΣEq : (Σ I (λ i → ∣ P i ∣)) → (Σ I (λ i → ∣ P i ∣)) → Set ℓ
    ΣEq (i , x) (j , y) = Σ (i ≡ j) λ e → Setoid._≈_ (Carrier (P j)) (subst (λ k → ∣ P k ∣) e x) y

    ΣS : Setoid ℓ ℓ
    ΣS = record
      { Carrier = Σ I (λ i → ∣ P i ∣)
      ; _≈_ = ΣEq
      ; isEquivalence = record
          { refl = λ {(i , x)} → refl , Setoid.refl (Carrier (P i))
          ; sym = λ { {i , x} {.i , y} (refl , e) → refl , Setoid.sym (Carrier (P i)) e }
          ; trans = λ { {i , x} {.i , y} {.i , z} (refl , e) (refl , e′) →
              refl , Setoid.trans (Carrier (P i)) e e′ }
          }
      }

    PieceΣ : Set ℓ
    PieceΣ = Σ I λ i → Σ (Func Rˢ (Carrier (P i))) (Random (P i))

    evΣ : PieceΣ → R → Σ I (λ i → ∣ P i ∣)
    evΣ (i , a , _) r = i , a ⟨$⟩ r

    preΣ : ∀ {f} → PieceΣ → Meas f → PieceΣ
    preΣ {f} (i , a , p) m = i , a ∘ₛ f , pre-random (P i) p m

    ΣQ : QBS S
    ΣQ = record
      { Carrier = ΣS
      ; probes = record
          { Random = λ α → Σ (Func Rˢ ℕˢ) λ i → Idx i ×
              Σ (ℕ → PieceΣ) λ c → ∀ r → Setoid._≈_ ΣS (α ⟨$⟩ r) (evΣ (c (i ⟨$⟩ r)) r)
          ; random-resp = λ e (i , ii , c , q) →
              i , ii , c , λ r → Setoid.trans ΣS (Setoid.sym ΣS (e r)) (q r)
          ; const-random = λ (i , x) →
              constₛ 0 , idx-const 0 , const (i , constₛ x , const-random (P i) x) ,
              λ _ → Setoid.refl ΣS
          ; pre-random = λ {_} {f} (i , ii , c , q) m →
              i ∘ₛ f , idx-pre ii m , (λ n → preΣ (c n) m) , λ r → q (f ⟨$⟩ r)
          }
      ; glue-random = λ {j} ij α p →
          let i = λ n → proj₁ (p n)
              c = λ n → proj₁ (proj₂ (proj₂ (p n)))
              c′ = λ k → c (proj₁ (unpair k)) (proj₂ (unpair k))
          in refineₛ j i
           , idx-glue ij (λ n → proj₁ (proj₂ (p n)))
           , c′
           , λ r → subst (λ u → Setoid._≈_ ΣS (α (j ⟨$⟩ r) ⟨$⟩ r) (evΣ (c (proj₁ u) (proj₂ u)) r))
                         (sym (unpair-pair (j ⟨$⟩ r) (i (j ⟨$⟩ r) ⟨$⟩ r)))
                         (proj₂ (proj₂ (proj₂ (p (j ⟨$⟩ r)))) r)
      }

    pmΣ : ∀ {Y} → (∀ i → Hom S (P i) Y) → PieceΣ → Func Rˢ (Carrier Y)
    pmΣ f (i , a , _) = map (f i) ∘ₛ a

    pmΣ-random : ∀ {Y} (f : ∀ i → Hom S (P i) Y) c → Random Y (pmΣ f c)
    pmΣ-random f (i , _ , p) = map-random (f i) p

    copairΣ-fun : ∀ {Y} → (∀ i → Hom S (P i) Y) → Func ΣS (Carrier Y)
    copairΣ-fun {Y} f = record
      { to = λ (i , x) → map (f i) ⟨$⟩ x
      ; cong = λ { {i , x} {.i , y} (refl , e) → Func.cong (map (f i)) e }
      }

    copairΣ : ∀ {Y} → (∀ i → Hom S (P i) Y) → Hom S ΣQ Y
    copairΣ {Y} f = record
      { map = copairΣ-fun f
      ; map-random = λ (i , ii , c , q) →
          random-resp Y
            (λ r → Setoid.sym (Carrier Y) (Func.cong (copairΣ-fun f) (q r)))
            (glue-random Y ii (λ n → pmΣ f (c n)) (λ n → pmΣ-random f (c n)))
      }

    indexedCoproduct : IndexedCoproductOf (QBSCat S) P
    indexedCoproduct = record
      { X = ΣQ
      ; ι = λ i → record
          { map = record { to = i ,_ ; cong = λ e → refl , e }
          ; map-random = λ {α} p →
              constₛ 0 , idx-const 0 , const (i , α , p) , λ _ → Setoid.refl ΣS
          }
      ; [_] = copairΣ
      ; commute = λ {Y} {f} {i} → Setoid.refl (Carrier Y)
      ; unique = λ {Y} p → λ { {i , x} → Setoid.sym (Carrier Y) (p {i} {x}) }
      }

  -- All small (co)limits, from indexed (co)products and (co)equalizers.
  complete : Complete ℓ ℓ ℓ (QBSCat S)
  complete = AllProducts×Equalizer⇒Complete (QBSCat S) (λ P → indexedProduct P) (equalizer S)

  cocomplete : Cocomplete ℓ ℓ ℓ (QBSCat S)
  cocomplete = AllCoproducts×Coequalizer⇒Cocomplete (QBSCat S) (λ P → indexedCoproduct P) (coequalizer S)

  -- ℕ-indexed products and coproducts, by reindexing along ℕ ≅ Lift ℓ ℕ.
  countableProduct : (P : ℕ → QBS S) → IndexedProductOf (QBSCat S) P
  countableProduct P = record
    { X = IP.X
    ; π = λ i → IP.π (lift i)
    ; ⟨_⟩ = λ f → IP.⟨ (λ { (lift i) → f i }) ⟩
    ; commute = λ {_} {f} {i} → IP.commute {f = λ { (lift j) → f j }} {lift i}
    ; unique = λ {_} {h} {f} p → IP.unique {h = h} {f = λ { (lift i) → f i }} (λ { {lift i} → p })
    }
    where module IP = IndexedProductOf (indexedProduct (λ (i : Lift ℓ ℕ) → P (lower i)))

  countableCoproduct : (P : ℕ → QBS S) → IndexedCoproductOf (QBSCat S) P
  countableCoproduct P = record
    { X = IC.X
    ; ι = λ i → IC.ι (lift i)
    ; [_] = λ f → IC.[ (λ { (lift i) → f i }) ]
    ; commute = λ {_} {f} {i} → IC.commute {f = λ { (lift j) → f j }} {lift i}
    ; unique = λ {_} {h} {f} p → IC.unique {h = h} {f = λ { (lift i) → f i }} (λ { {lift i} → p })
    }
    where module IC = IndexedCoproductOf (indexedCoproduct (λ (i : Lift ℓ ℕ) → P (lower i)))
