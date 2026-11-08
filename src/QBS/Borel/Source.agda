{-# OPTIONS --safe --without-K #-}

-- Cantor space with its Borel σ-algebra is a random source: quasi-Borel spaces over it are
-- quasi-Borel spaces in the sense of Heunen–Kammar–Staton–Yang (Def. 7; by their remark after
-- Def. 11 any uncountable standard Borel space serves as the sample space).
module QBS.Borel.Source where

open import Level using (zero; suc; Lift; lift; lower)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (tt)
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≗_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles using (Func; _⟨$⟩_)

open import Data.Unit.Polymorphic.Base using (⊤)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat)
import Categories.Category.SubCategory.SubHom as SH

open import QBS.Core using (RandomSource; MeasurableMaps; Probes; ℕˢ)
open import QBS.Pieces
open import QBS.Model.Pairing
open import QBS.Borel.Core

-- the sample space: Cantor space, lifted so that the σ-algebra (which lives in Set₁) is
-- a predicate in the same universe as R
R₁ : Set₁
R₁ = Lift (suc zero) Cantor

down : (R₁ → R₁) → Cantor → Cantor
down f x = lower (f (lift x))

downℕ : (R₁ → ℕ) → Cantor → ℕ
downℕ i x = i (lift x)

private
  -- a constant proposition about ℕ is Borel
  borel-eq : ∀ (a k : ℕ) → Borel (λ (_ : Cantor) → a ≡ k)
  borel-eq a k with a ≟ k
  ... | yes p = resp (λ x → (λ _ → p) , (λ _ → tt)) ⊤-borel
  ... | no ¬p = resp (λ x → (λ ()) , (λ e → ¬p e)) ⊥-borel

  idx-glue-borel : ∀ (j : Cantor → ℕ) (i : ℕ → Cantor → ℕ) →
    Partition j → (∀ n → Partition (i n)) → Partition (λ x → pair (j x) (i (j x) x))
  idx-glue-borel j i pj pi k = resp e (inter₂ (pj a) (pi a b))
    where
      a = proj₁ (unpair k)
      b = proj₂ (unpair k)
      e : (λ x → (j x ≡ a) × (i a x ≡ b)) ≐ (λ x → pair (j x) (i (j x) x) ≡ k)
      e x = fwd , bwd
        where
          fwd : (j x ≡ a) × (i a x ≡ b) → pair (j x) (i (j x) x) ≡ k
          fwd (p , q) = trans (cong₂ pair p (trans (cong (λ t → i t x) p) q)) (pair-unpair k)
          bwd : pair (j x) (i (j x) x) ≡ k → (j x ≡ a) × (i a x ≡ b)
          bwd h = sym (cong proj₁ e₁) , trans (cong (λ t → i t x) (cong proj₁ e₁)) (sym (cong proj₂ e₁))
            where e₁ : unpair k ≡ (j x , i (j x) x)
                  e₁ = trans (cong unpair (sym h)) (unpair-pair (j x) (i (j x) x))

-- points of Cantor space are equal when they agree everywhere: no function extensionality is needed
R₁ˢ : Setoid (suc zero) (suc zero)
R₁ˢ = record
  { Carrier = R₁
  ; _≈_ = λ x y → Lift (suc zero) (lower x ≗ lower y)
  ; isEquivalence = record
      { refl = lift (λ _ → refl)
      ; sym = λ e → lift (λ n → sym (lower e n))
      ; trans = λ e e′ → lift (λ n → trans (lower e n) (lower e′ n))
      }
  }

-- measurable maps and partitions respect pointwise equality (Borel sets do), so they are setoid maps
measₛ : (f : R₁ → R₁) → Measurable (down f) → Func R₁ˢ R₁ˢ
measₛ f mf = record { to = f ; cong = λ e → lift (measurable-≗ {down f} mf (lower e)) }

idxₛ : (i : R₁ → ℕ) → Partition (downℕ i) → Func R₁ˢ (ℕˢ {suc zero})
idxₛ i pi = record
  { to = λ r → lift (i r)
  ; cong = λ {r} {r′} e → cong lift (sym (proj₁ (borel-≗ (pi (i r)) {lower r} {lower r′} (lower e)) refl))
  }

-- Partitions respect pointwise equality of the index map
part-resp : ∀ {a b : Func R₁ˢ (ℕˢ {suc zero})} → (∀ r → Setoid._≈_ ℕˢ (a ⟨$⟩ r) (b ⟨$⟩ r)) →
  Partition (downℕ (λ r → lower (a ⟨$⟩ r))) → Partition (downℕ (λ r → lower (b ⟨$⟩ r)))
part-resp e pi k =
  resp (λ x → (λ q → trans (sym (cong lower (e (lift x)))) q) , (λ q → trans (cong lower (e (lift x))) q)) (pi k)

cantorSource : RandomSource (suc zero)
cantorSource = record
  { subcat = sc
  ; isRandomSource = record
    { measurable = M
    ; covering = record
      { partitions = P
      ; Meas₀-glue = λ {j} {f} pj mf →
          measurable-glue {downℕ (λ r → lower (j ⟨$⟩ r))} {λ k → down (f k ⟨$⟩_)} (part pj) mf
      }
    ; common-refinement = λ {j} {i} pj pi →
        let jℕ = λ r → lower (j ⟨$⟩ r)
            iℕ = λ n r → lower (i n ⟨$⟩ r)
            k = λ r → pair (jℕ r) (iℕ (jℕ r) r)
            pk = idx-glue-borel (downℕ jℕ) (λ n → downℕ (iℕ n)) (part pj) (λ n → part (pi n))
        in idxₛ k pk , mem (idxₛ k pk , pk) (Setoid.refl (ℕˢ {suc zero}))
             , unpair , λ r → unpair-pair (jℕ r) (iℕ (jℕ r) r)
    }
  }
  where
    open SH (Setoids (suc zero) (suc zero)) using (_∈_; mem; probe; reads)
    sc : SubCat (Setoids (suc zero) (suc zero)) {ℓ′ = suc zero} (⊤ {suc zero})
    sc = record
      { U = λ _ → R₁ˢ
      ; R = λ f → Measurable (down (f ⟨$⟩_))
      ; Rid = measurable-id
      ; _∘R_ = λ mf mg → measurable-∘ mg mf
      }
    M : MeasurableMaps sc
    M = record { Meas₀-const = λ r → measurable-const (lower r) }
    P : Probes M (ℕˢ {suc zero})
    P = fromPred M (ℕˢ {suc zero}) (λ i → Partition (downℕ (λ r → lower (i ⟨$⟩ r))))
      (λ n k → borel-eq (lower n) k) (λ pi mf k → preimage mf (pi k))
    part : ∀ {j} → j ∈ Probes.subhom P → Partition (downℕ (λ r → lower (j ⟨$⟩ r)))
    part {j} m = part-resp {a = proj₁ (probe m)} {b = j} (λ r → reads m {r}) (proj₂ (probe m))
