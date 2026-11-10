{-# OPTIONS --safe --without-K #-}

-- The global elements `⊤ ⇒ X` of an internal commutative monoid in a cartesian category form a commutative monoid, with
-- the pointwise product `w ∙ w′ = μ ∘ ⟨ w , w′ ⟩` (`Hom(⊤, –)` is lax monoidal for the cartesian product), and likewise the
-- global elements of a commutative semiring form a semiring (`globalSemiring`).
-- Route: each law is the internal law applied to `⟨ a , b ⟩` or `⟨ a , ⟨ b , c ⟩ ⟩`, rewritten by `⁂∘⟨⟩`; `distribˡ` and
-- `zeroʳ` are stated with the comonoid, which is the diagonal (`Δ≈diag`, from the counit laws), and `distribʳ`, `zeroˡ`
-- follow from commutativity.
open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian)

module Categories.Category.Cartesian.GlobalElements {o h e} {C : Category o h e} (cart : Cartesian C) where

open import Data.Product.Base using (_,_)
open import Algebra.Bundles using (Semiring)
open import Algebra.Structures using (IsCommutativeMonoid)

open import Categories.Category.BinaryProducts C using (module BinaryProducts)
open import Categories.Object.Terminal C using (module Terminal)
import Categories.Category.Cartesian.SymmetricMonoidal C cart as CSM
import Categories.Category.Monoidal.Symmetric.Algebra CSM.symmetric as Algebra

open Category C
open HomReasoning
open Cartesian cart using (terminal; products)
open Terminal terminal using (⊤)
open BinaryProducts products using
  (π₁; π₂; ⟨_,_⟩; _⁂_; ⟨⟩-cong₂; ⟨⟩∘; unique; π₁∘⁂; π₂∘⁂;
   assocʳ; assocʳ∘⟨⟩; ⁂∘⟨⟩; project₂; project₁; swap; swap∘⟨⟩; assocˡ; assocˡ∘⟨⟩)

module _ {X : Obj} (K : Algebra.IsCommutativeMonoid X) where
  open Algebra.IsCommutativeMonoid K renaming (assoc to μ-assoc; identityˡ to μ-identityˡ; identityʳ to μ-identityʳ)

  _∙_ : (⊤ ⇒ X) → (⊤ ⇒ X) → ⊤ ⇒ X
  w ∙ w′ = μ ∘ ⟨ w , w′ ⟩

  -- `μ` applied to a pair `⟨ f ∘ a , g ∘ b ⟩` is `μ ∘ (f ⁂ g)` applied to `⟨ a , b ⟩`
  ⁂-point : ∀ {Y Z} (f : Y ⇒ X) (g : Z ⇒ X) (a : ⊤ ⇒ Y) (b : ⊤ ⇒ Z) → μ ∘ ⟨ f ∘ a , g ∘ b ⟩ ≈ (μ ∘ (f ⁂ g)) ∘ ⟨ a , b ⟩
  ⁂-point f g a b = ⟺ (assoc ○ ∘-resp-≈ʳ ⁂∘⟨⟩)

  assoc-pt : ∀ a b c → (a ∙ b) ∙ c ≈ a ∙ (b ∙ c)
  assoc-pt a b c = begin
    μ ∘ ⟨ μ ∘ ⟨ a , b ⟩ , c ⟩        ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ Equiv.refl (⟺ identityˡ) ⟩
    μ ∘ ⟨ μ ∘ ⟨ a , b ⟩ , id ∘ c ⟩  ≈⟨ ⁂-point μ id ⟨ a , b ⟩ c ⟩
    (μ ∘ (μ ⁂ id)) ∘ ⟨ ⟨ a , b ⟩ , c ⟩ ≈⟨ μ-assoc ⟩∘⟨refl ⟩
    (μ ∘ (id ⁂ μ) ∘ assocˡ) ∘ ⟨ ⟨ a , b ⟩ , c ⟩
                                     ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
    μ ∘ (id ⁂ μ) ∘ (assocˡ ∘ ⟨ ⟨ a , b ⟩ , c ⟩)
                                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
    μ ∘ (id ⁂ μ) ∘ ⟨ a , ⟨ b , c ⟩ ⟩ ≈⟨ refl⟩∘⟨ ⁂∘⟨⟩ ⟩
    μ ∘ ⟨ id ∘ a , μ ∘ ⟨ b , c ⟩ ⟩   ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ Equiv.refl ⟩
    μ ∘ ⟨ a , μ ∘ ⟨ b , c ⟩ ⟩        ∎

  idˡ-pt : ∀ w → η ∙ w ≈ w
  idˡ-pt w = begin
    μ ∘ ⟨ η , w ⟩                   ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟺ identityʳ) (⟺ identityˡ) ⟩
    μ ∘ ⟨ η ∘ id , id ∘ w ⟩         ≈⟨ ⁂-point η id id w ⟩
    (μ ∘ (η ⁂ id)) ∘ ⟨ id , w ⟩     ≈⟨ ⟺ μ-identityˡ ⟩∘⟨refl ⟩
    π₂ ∘ ⟨ id , w ⟩                 ≈⟨ project₂ ⟩
    w                               ∎

  idʳ-pt : ∀ w → w ∙ η ≈ w
  idʳ-pt w = begin
    μ ∘ ⟨ w , η ⟩                   ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟺ identityˡ) (⟺ identityʳ) ⟩
    μ ∘ ⟨ id ∘ w , η ∘ id ⟩         ≈⟨ ⁂-point id η w id ⟩
    (μ ∘ (id ⁂ η)) ∘ ⟨ w , id ⟩     ≈⟨ ⟺ μ-identityʳ ⟩∘⟨refl ⟩
    π₁ ∘ ⟨ w , id ⟩                 ≈⟨ project₁ ⟩
    w                               ∎

  comm-pt : ∀ w w′ → w ∙ w′ ≈ w′ ∙ w
  comm-pt w w′ = begin
    μ ∘ ⟨ w , w′ ⟩                  ≈⟨ ⟺ comm ⟩∘⟨refl ⟩
    (μ ∘ swap) ∘ ⟨ w , w′ ⟩           ≈⟨ assoc ⟩
    μ ∘ (swap ∘ ⟨ w , w′ ⟩)           ≈⟨ refl⟩∘⟨ swap∘⟨⟩ ⟩
    μ ∘ ⟨ w′ , w ⟩                  ∎

  globalMonoid : IsCommutativeMonoid _≈_ _∙_ η
  globalMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record { isEquivalence = equiv ; ∙-cong = λ x y → ∘-resp-≈ʳ (⟨⟩-cong₂ x y) }
        ; assoc = assoc-pt
        }
      ; identity = idˡ-pt , idʳ-pt
      }
    ; comm = comm-pt
    }

-- The global elements of an internal commutative semiring `S` form a semiring, with the pointwise sum and product.  The
-- comonoid of `S` is the diagonal (`Δ≈diag`), so the diagonal-relative `distribˡ` and `zeroʳ` become their usual forms.
module _ (S : Algebra.CommutativeSemiring) where
  open Algebra.CommutativeSemiring S renaming (Carrier to X)
  open Terminal terminal using (!; !-unique₂)

  private
    _+_ _*_ : (⊤ ⇒ X) → (⊤ ⇒ X) → ⊤ ⇒ X
    _+_ = _∙_ +-isCommutativeMonoid
    _*_ = _∙_ *-isCommutativeMonoid

  π₁Δ : π₁ ∘ Δ ≈ id
  π₁Δ = begin
    π₁ ∘ Δ                  ≈⟨ ⟺ identityˡ ⟩∘⟨refl ⟩
    (id ∘ π₁) ∘ Δ           ≈⟨ ⟺ π₁∘⁂ ⟩∘⟨refl ⟩
    (π₁ ∘ (id ⁂ δ)) ∘ Δ     ≈⟨ assoc ⟩
    π₁ ∘ (id ⁂ δ) ∘ Δ       ≈⟨ refl⟩∘⟨ ⟺ δ-identityʳ ⟩
    π₁ ∘ ⟨ id , ! ⟩         ≈⟨ project₁ ⟩
    id                      ∎

  π₂Δ : π₂ ∘ Δ ≈ id
  π₂Δ = begin
    π₂ ∘ Δ                  ≈⟨ ⟺ identityˡ ⟩∘⟨refl ⟩
    (id ∘ π₂) ∘ Δ           ≈⟨ ⟺ π₂∘⁂ ⟩∘⟨refl ⟩
    (π₂ ∘ (δ ⁂ id)) ∘ Δ     ≈⟨ assoc ⟩
    π₂ ∘ (δ ⁂ id) ∘ Δ       ≈⟨ refl⟩∘⟨ ⟺ δ-identityˡ ⟩
    π₂ ∘ ⟨ ! , id ⟩         ≈⟨ project₂ ⟩
    id                      ∎

  Δ≈diag : Δ ≈ ⟨ id , id ⟩
  Δ≈diag = ⟺ (unique π₁Δ π₂Δ)

  -- the middle step of `swap-mid`: `⟨ b , ⟨ c , d ⟩ ⟩ ↦ ⟨ c , ⟨ b , d ⟩ ⟩`
  swap-point : ∀ (b c d : ⊤ ⇒ X) → (assocˡ ∘ (swap {X} {X} ⁂ id {X}) ∘ assocʳ) ∘ ⟨ b , ⟨ c , d ⟩ ⟩ ≈ ⟨ c , ⟨ b , d ⟩ ⟩
  swap-point b c d = begin
    (assocˡ ∘ (swap ⁂ id) ∘ assocʳ) ∘ ⟨ b , ⟨ c , d ⟩ ⟩ ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
    assocˡ ∘ (swap ⁂ id) ∘ (assocʳ ∘ ⟨ b , ⟨ c , d ⟩ ⟩)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assocʳ∘⟨⟩ ⟩
    assocˡ ∘ (swap ⁂ id) ∘ ⟨ ⟨ b , c ⟩ , d ⟩              ≈⟨ refl⟩∘⟨ ⁂∘⟨⟩ ⟩
    assocˡ ∘ ⟨ swap ∘ ⟨ b , c ⟩ , id ∘ d ⟩                ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ swap∘⟨⟩ identityˡ ⟩
    assocˡ ∘ ⟨ ⟨ c , b ⟩ , d ⟩                            ≈⟨ assocˡ∘⟨⟩ ⟩
    ⟨ c , ⟨ b , d ⟩ ⟩                                      ∎

  swap-mid-point : ∀ (a b c d : ⊤ ⇒ X)
    → Algebra.swap-mid ∘ ⟨ ⟨ a , b ⟩ , ⟨ c , d ⟩ ⟩ ≈ ⟨ ⟨ a , c ⟩ , ⟨ b , d ⟩ ⟩
  swap-mid-point a b c d = begin
    Algebra.swap-mid ∘ ⟨ ⟨ a , b ⟩ , ⟨ c , d ⟩ ⟩
      ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
    assocʳ ∘ (id {X} ⁂ (assocˡ ∘ (swap {X} {X} ⁂ id {X}) ∘ assocʳ)) ∘ (assocˡ ∘ ⟨ ⟨ a , b ⟩ , ⟨ c , d ⟩ ⟩)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
    assocʳ ∘ (id {X} ⁂ (assocˡ ∘ (swap {X} {X} ⁂ id {X}) ∘ assocʳ)) ∘ ⟨ a , ⟨ b , ⟨ c , d ⟩ ⟩ ⟩
      ≈⟨ refl⟩∘⟨ ⁂∘⟨⟩ ⟩
    assocʳ ∘ ⟨ id ∘ a , (assocˡ ∘ (swap {X} {X} ⁂ id {X}) ∘ assocʳ) ∘ ⟨ b , ⟨ c , d ⟩ ⟩ ⟩
      ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (swap-point b c d) ⟩
    assocʳ ∘ ⟨ a , ⟨ c , ⟨ b , d ⟩ ⟩ ⟩ ≈⟨ assocʳ∘⟨⟩ ⟩
    ⟨ ⟨ a , c ⟩ , ⟨ b , d ⟩ ⟩          ∎

  Δ-point : ∀ (a : ⊤ ⇒ X) → Δ ∘ a ≈ ⟨ a , a ⟩
  Δ-point a = ∘-resp-≈ˡ Δ≈diag ○ ⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ identityˡ

  distribˡ-pt : ∀ a b c → a * (b + c) ≈ (a * b) + (a * c)
  distribˡ-pt a b c = begin
    μ* ∘ ⟨ a , μ⁺ ∘ ⟨ b , c ⟩ ⟩       ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟺ identityˡ) Equiv.refl ⟩
    μ* ∘ ⟨ id ∘ a , μ⁺ ∘ ⟨ b , c ⟩ ⟩  ≈⟨ ⁂-point *-isCommutativeMonoid id μ⁺ a ⟨ b , c ⟩ ⟩
    (μ* ∘ (id ⁂ μ⁺)) ∘ ⟨ a , ⟨ b , c ⟩ ⟩
                                      ≈⟨ distribˡ ⟩∘⟨refl ⟩
    (μ⁺ ∘ (μ* ⁂ μ*) ∘ Algebra.swap-mid ∘ (Δ ⁂ id)) ∘ ⟨ a , ⟨ b , c ⟩ ⟩
                                      ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ assoc) ⟩
    μ⁺ ∘ (μ* ⁂ μ*) ∘ Algebra.swap-mid ∘ ((Δ ⁂ id) ∘ ⟨ a , ⟨ b , c ⟩ ⟩)
                                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ (Δ-point a) identityˡ) ⟩
    μ⁺ ∘ (μ* ⁂ μ*) ∘ Algebra.swap-mid ∘ ⟨ ⟨ a , a ⟩ , ⟨ b , c ⟩ ⟩
                                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swap-mid-point a a b c ⟩
    μ⁺ ∘ (μ* ⁂ μ*) ∘ ⟨ ⟨ a , b ⟩ , ⟨ a , c ⟩ ⟩
                                      ≈⟨ refl⟩∘⟨ ⁂∘⟨⟩ ⟩
    μ⁺ ∘ ⟨ μ* ∘ ⟨ a , b ⟩ , μ* ∘ ⟨ a , c ⟩ ⟩ ∎

  zeroʳ-pt : ∀ a → a * η⁺ ≈ η⁺
  zeroʳ-pt a = begin
    μ* ∘ ⟨ a , η⁺ ⟩                   ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟺ identityˡ) (⟺ identityʳ) ⟩
    μ* ∘ ⟨ id ∘ a , η⁺ ∘ id ⟩         ≈⟨ ⁂-point *-isCommutativeMonoid id η⁺ a id ⟩
    (μ* ∘ (id ⁂ η⁺)) ∘ ⟨ a , id ⟩     ≈⟨ zeroʳ ⟩∘⟨refl ⟩
    (η⁺ ∘ δ ∘ π₁) ∘ ⟨ a , id ⟩        ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ project₁) ⟩
    η⁺ ∘ δ ∘ a                        ≈⟨ refl⟩∘⟨ !-unique₂ ⟩
    η⁺ ∘ id                           ≈⟨ identityʳ ⟩
    η⁺                                ∎

  module G+ = IsCommutativeMonoid (globalMonoid +-isCommutativeMonoid)
  module G* = IsCommutativeMonoid (globalMonoid *-isCommutativeMonoid)

  zeroˡ-pt : ∀ a → η⁺ * a ≈ η⁺
  zeroˡ-pt a = G*.comm η⁺ a ○ zeroʳ-pt a

  distribʳ-pt : ∀ a b c → (b + c) * a ≈ (b * a) + (c * a)
  distribʳ-pt a b c = G*.comm (b + c) a ○ distribˡ-pt a b c ○ G+.∙-cong (G*.comm a b) (G*.comm a c)

  -- the semiring of global elements of `S`
  globalSemiring : Semiring h e
  globalSemiring = record
    { Carrier = ⊤ ⇒ X ; _≈_ = _≈_ ; _+_ = _+_ ; _*_ = _*_ ; 0# = η⁺ ; 1# = η*
    ; isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = globalMonoid +-isCommutativeMonoid
        ; *-cong = G*.∙-cong
        ; *-assoc = G*.assoc
        ; *-identity = G*.identity
        ; distrib = distribˡ-pt , distribʳ-pt
        }
      ; zero = zeroˡ-pt , zeroʳ-pt
      }
    }
