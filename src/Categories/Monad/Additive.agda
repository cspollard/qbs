{-# OPTIONS --safe --without-K #-}

-- Additive monads: a monad `M` whose Kleisli category `K` is enriched over commutative monoids, so that kernels
-- `X ⇒ M Y` can be added (for a measure monad, `⊕` is the sum of measures and `𝟘` the zero measure).
--   `IsAdditive M`  the structure: `𝟘`, `⊕` on every `K [ X , Y ]`, with bilinear composition; derived: `⊕-cong`,
--                   `⊕-distribˡ`, `⊕-distribʳ`, and the semiring `End X` of endomorphisms
--   `AdditiveMonad` a monad with `IsAdditive`
--   `KleisliCM`     the `CM-Category` (agda-categories) of an additive monad, with underlying category `Kleisli M`
-- The free commutative monoid monad is not constructed: as in `CMonoidEnriched`, the additive structure is axiomatic.
-- Route: `KleisliCM` reuses `Kleisli M` for the category structure and takes the monoid on `K [ X , Y ]` from
-- `isCommutativeMonoid`; `⊕-resp-∘` and `𝟘-resp-∘` are the laws of `CM-Category`, the latter for `B = C`.
open import Categories.Category.Core using (Category)

module Categories.Monad.Additive {o h e} {C : Category o h e} where

open import Level using (_⊔_)
open import Data.Product.Base using (_,_)
open import Algebra.Bundles using (Semiring)
open import Algebra.Structures using (IsCommutativeMonoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category using (_[_,_])
open import Categories.Category.CMonoidEnriched using (CM-Category; Underlying)
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Monad using (Monad)

-- An additive monad: the Kleisli category `K` of `M` is enriched over commutative monoids.  Equivalently, on the hom
-- functor `Kᵒᵖ × K → Setoids`, `⊕ : Hom × Hom ⇒ Hom` and `𝟘 : 1 ⇒ Hom` are natural transformations making each
-- hom-setoid a commutative monoid.  `isCommutativeMonoid` is the monoid laws on each `K [ X , Y ]`; `⊕-resp-∘` and
-- `𝟘-resp-∘` are the naturality of `⊕` and `𝟘`, i.e. composition (bind) commutes with them in each argument.
record IsAdditive (M : Monad C) : Set (o ⊔ h ⊔ e) where

  private
    K = Kleisli M
    module K = Category K

  infixl 6 _⊕_
  field
    -- A zero morphism in the kleisli category that is the unit of ⊕
    𝟘 : ∀ {X Y} → K [ X , Y ]
    _⊕_ : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → K [ X , Y ]
    isCommutativeMonoid : ∀ {X Y} → IsCommutativeMonoid (K._≈_ {X} {Y}) _⊕_ 𝟘

    -- bind (Kleisli _∘_) is linear in the kernel run before,
    -- the kernel run after, and the continuation
    ⊕-resp-∘
      : ∀ {A B C D}
      → (k : K [ C , D ]) (f g : K [ B , C ]) (h : K [ A , B ])
      → k K.∘ (f ⊕ g) K.∘ h K.≈ (k K.∘ f K.∘ h) ⊕ (k K.∘ g K.∘ h)

    𝟘-resp-∘
      : ∀ {A B C D}
      → (k : K [ C , D ]) (h : K [ A , B ])
      → k K.∘ 𝟘 {B} {C} K.∘ h K.≈ 𝟘

  open K.HomReasoning

  ⊕-cong : ∀ {X Y} {a b c d : K [ X , Y ]} → a K.≈ b → c K.≈ d → (a ⊕ c) K.≈ (b ⊕ d)
  ⊕-cong = IsCommutativeMonoid.∙-cong isCommutativeMonoid

  -- composition on one side distributes over `⊕` (`⊕-resp-∘` with the other kernel the identity)
  ⊕-distribˡ
    : ∀ {A B D} (k : K [ B , D ]) (f g : K [ A , B ])
    → k K.∘ (f ⊕ g) K.≈ (k K.∘ f) ⊕ (k K.∘ g)
  ⊕-distribˡ k f g = begin
    k K.∘ (f ⊕ g)              ≈⟨ K.∘-resp-≈ʳ (⟺ K.identityʳ) ⟩
    k K.∘ (f ⊕ g) K.∘ K.id     ≈⟨ ⊕-resp-∘ k f g K.id ⟩
    (k K.∘ f K.∘ K.id) ⊕ (k K.∘ g K.∘ K.id)
                               ≈⟨ ⊕-cong (K.∘-resp-≈ʳ K.identityʳ) (K.∘-resp-≈ʳ K.identityʳ) ⟩
    (k K.∘ f) ⊕ (k K.∘ g)      ∎

  ⊕-distribʳ
    : ∀ {A C D} (f g : K [ C , D ]) (h : K [ A , C ])
    → (f ⊕ g) K.∘ h K.≈ (f K.∘ h) ⊕ (g K.∘ h)
  ⊕-distribʳ f g h = begin
    (f ⊕ g) K.∘ h              ≈⟨ ⟺ K.identityˡ ⟩
    K.id K.∘ (f ⊕ g) K.∘ h     ≈⟨ ⊕-resp-∘ K.id f g h ⟩
    (K.id K.∘ f K.∘ h) ⊕ (K.id K.∘ g K.∘ h) ≈⟨ ⊕-cong K.identityˡ K.identityˡ ⟩
    (f K.∘ h) ⊕ (g K.∘ h)      ∎

  -- The endomorphism semiring of an object `X` of the Kleisli category: `(⊕, 𝟘)` and `(K.∘, K.id)`, distributing by
  -- `⊕-resp-∘` and annihilating by `𝟘-resp-∘`.  At `X = ⊤` these are the scalars of `SoftConditioning`.
  End : Category.Obj C → Semiring h e
  End X = record
    { Carrier = K [ X , X ] ; _≈_ = K._≈_ ; _+_ = _⊕_ ; _*_ = K._∘_ ; 0# = 𝟘 ; 1# = K.id
    ; isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = isCommutativeMonoid
        ; *-cong = K.∘-resp-≈
        ; *-assoc = λ _ _ _ → K.assoc
        ; *-identity = (λ _ → K.identityˡ) , (λ _ → K.identityʳ)
        ; distrib = ⊕-distribˡ , (λ h f g → ⊕-distribʳ f g h)
        }
      ; zero = (λ x → K.Equiv.trans (K.Equiv.sym K.identityˡ) (𝟘-resp-∘ K.id x))
             , (λ x → K.Equiv.trans (K.∘-resp-≈ʳ (K.Equiv.sym K.identityʳ)) (𝟘-resp-∘ x K.id))
      }
    }

-- an additive monad: a monad with additive kernels
record AdditiveMonad : Set (o ⊔ h ⊔ e) where
  field
    M : Monad C
    isAdditive : IsAdditive M
  open IsAdditive isAdditive public

-- the Kleisli category of an additive monad, with commutative monoids as hom-sets
KleisliCM : ∀ {M : Monad C} → IsAdditive M → CM-Category o h e
KleisliCM {M} AK = record
  { Category K
  ; Hom = λ X Y → record
    { Carrier = K [ X , Y ] ; _≈_ = K._≈_ ; _∙_ = _⊕_ ; ε = 𝟘 ; isCommutativeMonoid = isCommutativeMonoid }
  ; +-resp-∘ = ⊕-resp-∘ _ _ _ _
  ; 0-resp-∘ = 𝟘-resp-∘ _ _
  }
  where
    K = Kleisli M
    module K = Category K
    open IsAdditive AK

-- the bridge does not change the category
underlying : ∀ {M : Monad C} (AK : IsAdditive M) → Underlying (KleisliCM AK) ≡ Kleisli M
underlying AK = refl
