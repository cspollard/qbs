{-# OPTIONS --safe --without-K #-}

-- Subpresheaves of a Hom functor, along a functor `J : D ⇒ C` (the inclusion of a sub-category).
--   * `homPresheaf J X`, the Hom functor `Hom[-,X]` of `C` pulled back along `J`; for `J = id` it is `Hom[-,X]`;
--   * `SubHom J X`, a subpresheaf of it: a `Setoids`-valued presheaf `F` on `D` with a natural map
--     `ι : F ⇒ homPresheaf J X` that is a monomorphism in the category of presheaves (`inj⇒mono`
--     builds one from injectivity at each object);
--   * `repSubHom`, `repRepresentable`: for a faithful `J` the hom-presheaf `Hom_D[-,j]` of `D` is a `SubHom J (J j)`, and it is
--     `Representable` (agda-categories);
-- Route: everything is built from `Hom[-,X]`, `Functor.op` and `Faithful` of agda-categories.
-- The levels of `D` are those of the homs of `C`, so that all probe sets live in `Setoids h e`.
open import Categories.Category.Core using (Category)

module Categories.Category.SubCategory.SubHom {o h e} (C : Category o h e) where

open import Level using (suc; _⊔_)
open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.Presheaves using (Presheaves′)
open import Categories.Category.Instance.Setoids using (Setoids)
import Categories.Morphism as Morphism
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom using (module Hom)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Properties using (Faithful)
open import Categories.Functor.Representable using (Representable)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; refl)

open Category C
open Hom C using (Hom[-,_])

module _ {o′} {D : Category o′ h e} (J : Functor D C) (X : Obj) where
  private
    module D = Category D
    module J = Functor J

  -- `Hom[-,X]` pulled back along `J`
  homPresheaf : Presheaf D (Setoids h e)
  homPresheaf = Hom[-, X ] ∘F Functor.op J

  -- a natural map that is injective at each object is a monomorphism of presheaves (a tool to build instances)
  inj⇒mono : ∀ {F : Presheaf D (Setoids h e)} (ι : NaturalTransformation F homPresheaf) →
    (∀ {j} {a b} → NaturalTransformation.η ι j ⟨$⟩ a ≈ NaturalTransformation.η ι j ⟨$⟩ b →
      Setoid._≈_ (Functor.F₀ F j) a b) →
    Morphism.Mono (Presheaves′ h e D) {A = F} {B = homPresheaf} ι
  inj⇒mono ι inj g₁ g₂ eq = inj eq

  -- a subpresheaf of the homs `J j ⇒ X`
  record SubHom : Set (o ⊔ o′ ⊔ suc h ⊔ suc e) where
    field
      F : Presheaf D (Setoids h e)
      ι : NaturalTransformation F homPresheaf
    open NaturalTransformation ι public
    field
      ι-mono : Morphism.Mono (Presheaves′ h e D) {A = F} {B = homPresheaf} ι

-- membership in the subpresheaf: a map `x : J j ⇒ X` is a member of `S` when it is the image `ι a` of some probe `a`
-- (the point-membership relation of a subobject: `x` factors through `ι`).  A record, so that `x` is recovered from
-- a proof of membership by unification.  The object `j` is implicit; it is solved automatically for a one-object
-- site (`⊤` has eta), and otherwise given as `_∈_ {j}` or with the explicit form `S ∋[ j ] x`.
module _ {o′} {D : Category o′ h e} {J : Functor D C} {X : Obj} where
  private
    module D = Category D
    module J = Functor J

  infix 4 _∈_ _∋[_]_

  record _∈_ {j} (x : J.F₀ j ⇒ X) (S : SubHom J X) : Set (h ⊔ e) where
    constructor mem
    open SubHom S
    field
      witness : Setoid.Carrier (Functor.F₀ F j)
      agrees : η j ⟨$⟩ witness ≈ x

  -- the same with the object given explicitly
  _∋[_]_ : (S : SubHom J X) (j : D.Obj) → J.F₀ j ⇒ X → Set (h ⊔ e)
  S ∋[ j ] x = _∈_ {j = j} x S

  -- the probe and the proof that it reads as `x`
  probe : ∀ {S j x} → _∈_ {j = j} x S → Setoid.Carrier (Functor.F₀ (SubHom.F S) j)
  probe = _∈_.witness

  reads : ∀ {S j} {x : J.F₀ j ⇒ X} (m : x ∈ S) → NaturalTransformation.η (SubHom.ι S) j ⟨$⟩ probe m ≈ x
  reads = _∈_.agrees

  -- membership respects equality of maps
  ∈-resp : ∀ {S j} {x y : J.F₀ j ⇒ X} → x ≈ y → x ∈ S → y ∈ S
  ∈-resp e (mem a ea) = mem a (Equiv.trans ea e)

  -- membership is stable under precomposition by `J f` (naturality of `ι`)
  ∈-pre : ∀ {S j k} (f : Category._⇒_ D k j) {x : J.F₀ j ⇒ X} → x ∈ S → (x ∘ J.F₁ f) ∈ S
  ∈-pre {S} f (mem a ea) =
    mem (Functor.F₁ (SubHom.F S) f ⟨$⟩ a)
      (Equiv.trans (NaturalTransformation.commute (SubHom.ι S) f {a})
        (Equiv.trans identityˡ (∘-resp-≈ˡ ea)))

-- for a faithful `J` the hom-presheaf of `D` at `j` is a subpresheaf of the homs into `J j`, and it is representable
module _ {o′} {D : Category o′ h e} {J : Functor D C} (faithful : Faithful J) (X : Category.Obj D) where
  private
    module D = Category D
    module J = Functor J
    module H = Functor (Hom.Hom[-,_] D X)

  repSubHom : SubHom J (J.F₀ X)
  repSubHom = record
    { F = Hom.Hom[-,_] D X
    ; ι = record
        { η = λ _ → record { to = J.F₁ ; cong = J.F-resp-≈ }
        ; commute = λ _ → Equiv.trans J.homomorphism (∘-resp-≈ J.identity J.homomorphism)
        ; sym-commute = λ _ → Equiv.sym (Equiv.trans J.homomorphism (∘-resp-≈ J.identity J.homomorphism))
        }
    ; ι-mono = inj⇒mono J (J.F₀ X) _ faithful
    }

  repRepresentable : Representable (SubHom.F repSubHom)
  repRepresentable = record { A = X ; Iso = refl }
