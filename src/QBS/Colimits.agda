{-# OPTIONS --safe --without-K #-}

-- Finite colimits in QBSCat S: initial object, binary coproducts, coequalizers (`FinitelyCocomplete`).
module QBS.Colimits where

open import Level using (Level; suc; Lift; lift)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
import Relation.Binary.Construct.Closure.Equivalence as EqC
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (subst; sym)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Categories.Object.Initial using (Initial)
open import Categories.Object.Coproduct using (Coproduct)
open import Categories.Diagram.Coequalizer using (Coequalizer)

open import QBS.Core
open import QBS.Category

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  -- Initial object: the empty space.
  0Q : QBS S
  0Q = record
    { Carrier = setoid (⊥ {ℓ})
    ; probes = record
        { Random = λ _ → ⊥ {ℓ}
        ; random-resp = λ _ p → p
        ; const-random = λ ()
        ; pre-random = λ p _ → p
        }
    ; glue-random = λ _ α p → p 0
    }

  module _ (X Y : QBS S) where
    -- A random element of X + Y is, locally on a measurable countable
    -- partition, a random element of X or of Y.
    Piece : Set ℓ
    Piece = Σ (Func Rˢ (Carrier X)) (Random X) ⊎ Σ (Func Rˢ (Carrier Y)) (Random Y)

    ev : Piece → R → ∣ X ∣ ⊎ ∣ Y ∣
    ev (inj₁ (a , _)) r = inj₁ (a ⟨$⟩ r)
    ev (inj₂ (b , _)) r = inj₂ (b ⟨$⟩ r)

    pre : ∀ {f} → Piece → Meas f → Piece
    pre {f} (inj₁ (a , p)) m = inj₁ (a ∘ₛ f , pre-random X p m)
    pre {f} (inj₂ (b , p)) m = inj₂ (b ∘ₛ f , pre-random Y p m)

    ⊎S : Setoid ℓ ℓ
    ⊎S = ⊎ʳ.⊎-setoid (Carrier X) (Carrier Y)

    ev-pre : ∀ {f} (c : Piece) (m : Meas f) r → Setoid._≈_ ⊎S (ev (pre c m) r) (ev c (f ⟨$⟩ r))
    ev-pre (inj₁ (a , _)) _ r = ⊎ʳ.inj₁ (Setoid.refl (Carrier X))
    ev-pre (inj₂ (b , _)) _ r = ⊎ʳ.inj₂ (Setoid.refl (Carrier Y))

  _+Q_ : QBS S → QBS S → QBS S
  X +Q Y = record
    { Carrier = ⊎S X Y
    ; probes = record
        { Random = λ α → Σ (Func Rˢ ℕˢ) λ i → Idx i ×
            Σ (ℕ → Piece X Y) λ c → ∀ r → Setoid._≈_ (⊎S X Y) (α ⟨$⟩ r) (ev X Y (c (i ⟨$⟩ r)) r)
        ; random-resp = λ e (i , ii , c , q) →
            i , ii , c , λ r → Setoid.trans (⊎S X Y) (Setoid.sym (⊎S X Y) (e r)) (q r)
        ; const-random = λ where
            (inj₁ a) → constₛ 0 , idx-const 0 , const (inj₁ (constₛ a , const-random X a)) ,
                       λ _ → ⊎ʳ.inj₁ (Setoid.refl (Carrier X))
            (inj₂ b) → constₛ 0 , idx-const 0 , const (inj₂ (constₛ b , const-random Y b)) ,
                       λ _ → ⊎ʳ.inj₂ (Setoid.refl (Carrier Y))
        ; pre-random = λ {_} {f} (i , ii , c , q) m →
            i ∘ₛ f , idx-pre ii m , (λ n → pre X Y (c n) m) ,
            λ r → Setoid.trans (⊎S X Y) (q (f ⟨$⟩ r))
                    (Setoid.sym (⊎S X Y) (ev-pre X Y (c (i ⟨$⟩ (f ⟨$⟩ r))) m r))
        }
    ; glue-random = λ {j} ij α p →
        let i = λ n → proj₁ (p n)
            c = λ n → proj₁ (proj₂ (proj₂ (p n)))
            c′ = λ k → c (proj₁ (unpair k)) (proj₂ (unpair k))
        in refineₛ j i
         , idx-glue ij (λ n → proj₁ (proj₂ (p n)))
         , c′
         , λ r → subst (λ u → Setoid._≈_ (⊎S X Y) (α (j ⟨$⟩ r) ⟨$⟩ r) (ev X Y (c (proj₁ u) (proj₂ u)) r))
                       (sym (unpair-pair (j ⟨$⟩ r) (i (j ⟨$⟩ r) ⟨$⟩ r)))
                       (proj₂ (proj₂ (proj₂ (p (j ⟨$⟩ r)))) r)
    }


  initial : Initial (QBSCat S)
  initial = record
    { ⊥ = 0Q
    ; ⊥-is-initial = record
        { ! = record { map = record { to = λ () ; cong = λ {} } ; map-random = λ () }
        ; !-unique = λ _ ()
        }
    }

  module _ {X Y Z : QBS S} (f : Hom S X Z) (g : Hom S Y Z) where
    pm : Piece X Y → Func Rˢ (Carrier Z)
    pm (inj₁ (a , _)) = map f ∘ₛ a
    pm (inj₂ (b , _)) = map g ∘ₛ b

    pm-random : ∀ c → Random Z (pm c)
    pm-random (inj₁ (_ , p)) = map-random f p
    pm-random (inj₂ (_ , p)) = map-random g p

    copair-fun : Func (⊎S X Y) (Carrier Z)
    copair-fun = record
      { to = [ map f ⟨$⟩_ , map g ⟨$⟩_ ]′
      ; cong = λ { (⊎ʳ.inj₁ e) → Func.cong (map f) e ; (⊎ʳ.inj₂ e) → Func.cong (map g) e }
      }

    pm-ev : ∀ c r → Setoid._≈_ (Carrier Z) (copair-fun ⟨$⟩ ev X Y c r) (pm c ⟨$⟩ r)
    pm-ev (inj₁ _) _ = Setoid.refl (Carrier Z)
    pm-ev (inj₂ _) _ = Setoid.refl (Carrier Z)

    -- Copairing: apply f or g to each piece of a random element.
    copair : Hom S (X +Q Y) Z
    copair = record
      { map = copair-fun
      ; map-random = λ {α} (i , ii , c , q) →
          random-resp Z
            (λ r → Setoid.sym (Carrier Z)
              (Setoid.trans (Carrier Z) (Func.cong copair-fun (q r)) (pm-ev (c (i ⟨$⟩ r)) r)))
            (glue-random Z ii (λ n → pm (c n)) (λ n → pm-random (c n)))
      }

  coproduct : ∀ {X Y} → Coproduct (QBSCat S) X Y
  coproduct {X} {Y} = record
    { A+B = X +Q Y
    ; i₁ = record
        { map = record { to = inj₁ ; cong = ⊎ʳ.inj₁ }
        ; map-random = λ {α} p →
            constₛ 0 , idx-const 0 , const (inj₁ (α , p)) , λ _ → ⊎ʳ.inj₁ (Setoid.refl (Carrier X))
        }
    ; i₂ = record
        { map = record { to = inj₂ ; cong = ⊎ʳ.inj₂ }
        ; map-random = λ {α} p →
            constₛ 0 , idx-const 0 , const (inj₂ (α , p)) , λ _ → ⊎ʳ.inj₂ (Setoid.refl (Carrier Y))
        }
    ; [_,_] = copair
    ; inject₁ = λ {C} _ → Setoid.refl (Carrier C)
    ; inject₂ = λ {C} _ → Setoid.refl (Carrier C)
    ; unique = λ {C} p q → λ { (inj₁ x) → Setoid.sym (Carrier C) (p x) ; (inj₂ y) → Setoid.sym (Carrier C) (q y) }
    }

  cocartesian : Cocartesian (QBSCat S)
  cocartesian = record
    { initial = initial
    ; coproducts = record { coproduct = coproduct }
    }

  module _ {X Y : QBS S} (f g : Hom S X Y) where
    -- Y modulo f x ~ g x: the equivalence closure of Y's equality plus the
    -- identifications f x ~ g x.
    gen : Rel ∣ Y ∣ ℓ
    gen y y′ = Setoid._≈_ (Carrier Y) y y′
             ⊎ Σ ∣ X ∣ λ x → Setoid._≈_ (Carrier Y) y (map f ⟨$⟩ x)
                           × Setoid._≈_ (Carrier Y) y′ (map g ⟨$⟩ x)

    CoeqS : Setoid ℓ ℓ
    CoeqS = EqC.setoid gen

    -- Locally on a measurable countable partition, a random element of Y.
    CoeqQ : QBS S
    CoeqQ = record
      { Carrier = CoeqS
      ; probes = record
          { Random = λ α → Σ (Func Rˢ ℕˢ) λ i → Idx i ×
              Σ (ℕ → Σ (Func Rˢ (Carrier Y)) (Random Y)) λ c →
                ∀ r → Setoid._≈_ CoeqS (α ⟨$⟩ r) (proj₁ (c (i ⟨$⟩ r)) ⟨$⟩ r)
          ; random-resp = λ e (i , ii , c , q) →
              i , ii , c , λ r → Setoid.trans CoeqS (Setoid.sym CoeqS (e r)) (q r)
          ; const-random = λ x →
              constₛ 0 , idx-const 0 , const (constₛ x , const-random Y x) , λ _ → Setoid.refl CoeqS
          ; pre-random = λ {_} {m} (i , ii , c , q) mm →
              i ∘ₛ m , idx-pre ii mm , (λ n → proj₁ (c n) ∘ₛ m , pre-random Y (proj₂ (c n)) mm) ,
              λ r → q (m ⟨$⟩ r)
          }
      ; glue-random = λ {j} ij α p →
          let i = λ n → proj₁ (p n)
              c = λ n → proj₁ (proj₂ (proj₂ (p n)))
              c′ = λ k → c (proj₁ (unpair k)) (proj₂ (unpair k))
          in refineₛ j i
           , idx-glue ij (λ n → proj₁ (proj₂ (p n)))
           , c′
           , λ r → subst (λ u → Setoid._≈_ CoeqS (α (j ⟨$⟩ r) ⟨$⟩ r) (proj₁ (c (proj₁ u) (proj₂ u)) ⟨$⟩ r))
                         (sym (unpair-pair (j ⟨$⟩ r) (i (j ⟨$⟩ r) ⟨$⟩ r)))
                         (proj₂ (proj₂ (proj₂ (p (j ⟨$⟩ r)))) r)
      }

    coeq-arr : Hom S Y CoeqQ
    coeq-arr = record
      { map = record { to = id ; cong = λ e → fwd (inj₁ e) ◅ ε }
      ; map-random = λ {α} p →
          constₛ 0 , idx-const 0 , const (α , p) , λ _ → Setoid.refl CoeqS
      }

    module _ {Z : QBS S} (h : Hom S Y Z) (eq : _≈H_ S (_∘H_ S h f) (_∘H_ S h g))
      where
      lift-gen : ∀ {y y′} → EqClosure gen y y′ → Setoid._≈_ (Carrier Z) (map h ⟨$⟩ y) (map h ⟨$⟩ y′)
      lift-gen = EqC.gfold (Setoid.isEquivalence (Carrier Z)) (map h ⟨$⟩_) λ
        { (inj₁ e) → Func.cong (map h) e
        ; (inj₂ (x , e , e′)) → Setoid.trans (Carrier Z) (Func.cong (map h) e)
            (Setoid.trans (Carrier Z) (eq x) (Setoid.sym (Carrier Z) (Func.cong (map h) e′)))
        }

      coeq-fun : Func CoeqS (Carrier Z)
      coeq-fun = record { to = map h ⟨$⟩_ ; cong = lift-gen }

      coeq-hom : Hom S CoeqQ Z
      coeq-hom = record
        { map = coeq-fun
        ; map-random = λ {α} (i , ii , c , q) →
            random-resp Z (λ r → Setoid.sym (Carrier Z) (lift-gen (q r)))
              (glue-random Z ii (λ n → map h ∘ₛ proj₁ (c n)) (λ n → map-random h (proj₂ (c n))))
        }

  coequalizer : ∀ {X Y} (f g : Hom S X Y) → Coequalizer (QBSCat S) f g
  coequalizer {X} {Y} f g = record
    { obj = CoeqQ f g
    ; arr = coeq-arr f g
    ; isCoequalizer = record
        { equality = λ x → fwd (inj₂ (x , Setoid.refl (Carrier Y) , Setoid.refl (Carrier Y))) ◅ ε
        ; coequalize = λ {_} {h} eq → coeq-hom f g h eq
        ; universal = λ {C} _ → Setoid.refl (Carrier C)
        ; unique = λ {C} p x → Setoid.sym (Carrier C) (p x)
        }
    }

  finitelyCocomplete : FinitelyCocomplete (QBSCat S)
  finitelyCocomplete = record { cocartesian = cocartesian ; coequalizer = coequalizer }
