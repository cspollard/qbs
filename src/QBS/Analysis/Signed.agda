{-# OPTIONS --safe --without-K #-}

-- Signed values: the ring of differences of "finite" elements of a commutative semiring.
--
-- A signed value is a pair `(p, n)` of finite elements, standing for `p − n`; `(p, n) ≃ (p′, n′)` when
-- `p + n′ + c ≈ p′ + n + c` for some finite `c`.  This is the Grothendieck construction, which needs no
-- cancellation (and no classical principle): the witness `c` replaces cancellation.  It must be restricted to
-- a subsemiring of finite elements, since in `[0,∞]` the witness `c = ∞` would identify everything.
-- The result is a commutative ring (`signedRing`) with the embedding `ι` of the finite elements.
-- Generic in the semiring: for the extended non-negative reals take the elements bounded by a natural number.
module QBS.Analysis.Signed where

open import Level using (Level; _⊔_)
open import Algebra.Bundles using (CommutativeSemiring; CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing; IsRing; IsAbelianGroup; IsGroup; IsMonoid; IsMagma; IsCommutativeMonoid; IsSemigroup)
open import Function.Base using (_$_)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- a subsemiring: the "finite" elements
record SubSemiring {c ℓ} (R : CommutativeSemiring c ℓ) (p : Level) : Set (c ⊔ ℓ ⊔ Level.suc p) where
  open CommutativeSemiring R
  field
    Is : Carrier → Set p
    Is-resp : ∀ {a b} → a ≈ b → Is a → Is b
    Is-0 : Is 0#
    Is-1 : Is 1#
    Is-+ : ∀ {a b} → Is a → Is b → Is (a + b)
    Is-* : ∀ {a b} → Is a → Is b → Is (a * b)

module Signed {c ℓ p} (R : CommutativeSemiring c ℓ) (F : SubSemiring R p) where
  open CommutativeSemiring R
  open SubSemiring F
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R
  open SetoidReasoning setoid

  ----------------------------------------------------------------------------
  -- the carrier

  record Sg : Set (c ⊔ p) where
    constructor _−_[_,_]
    field
      pos neg : Carrier
      pos-fin : Is pos
      neg-fin : Is neg
  open Sg

  infix 4 _≃_
  record _≃_ (x y : Sg) : Set (c ⊔ ℓ ⊔ p) where
    constructor mk≃
    field
      k : Carrier
      k-fin : Is k
      eq : pos x + neg y + k ≈ pos y + neg x + k

  ≃-refl : ∀ {x} → x ≃ x
  ≃-refl {x} = mk≃ 0# Is-0 $ +-comm-lhs
    where +-comm-lhs = trans (+-cong (+-comm (pos x) (neg x)) refl) (+-cong (+-comm (neg x) (pos x)) refl)

  ≃-sym : ∀ {x y} → x ≃ y → y ≃ x
  ≃-sym (mk≃ k fk e) = mk≃ k fk (sym e)

  ≃-trans : ∀ {x y z} → x ≃ y → y ≃ z → x ≃ z
  ≃-trans {x} {y} {z} (mk≃ k₁ f₁ e₁) (mk≃ k₂ f₂ e₂) =
    mk≃ (k₁ + k₂ + pos y + neg y)
    (Is-+ (Is-+ (Is-+ f₁ f₂) (pos-fin y)) (neg-fin y))
    (begin
        pos x + neg z + (k₁ + k₂ + pos y + neg y)
          ≈⟨ solve 6 (λ px nz k1 k2 py ny → px :+ nz :+ (k1 :+ k2 :+ py :+ ny) := (px :+ ny :+ k1) :+ (py :+ nz :+ k2)) refl (pos x) (neg z) k₁ k₂ (pos y) (neg y) ⟩
        (pos x + neg y + k₁) + (pos y + neg z + k₂)
          ≈⟨ +-cong e₁ e₂ ⟩
        (pos y + neg x + k₁) + (pos z + neg y + k₂)
          ≈⟨ solve 6 (λ py nx k1 pz ny k2 → (py :+ nx :+ k1) :+ (pz :+ ny :+ k2) := pz :+ nx :+ (k1 :+ k2 :+ py :+ ny)) refl (pos y) (neg x) k₁ (pos z) (neg y) k₂ ⟩
        pos z + neg x + (k₁ + k₂ + pos y + neg y) ∎)

  Sgˢ : Setoid (c ⊔ p) (c ⊔ ℓ ⊔ p)
  Sgˢ = record { Carrier = Sg ; _≈_ = _≃_
               ; isEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans } }

  ----------------------------------------------------------------------------
  -- operations

  0S 1S : Sg
  0S = 0# − 0# [ Is-0 , Is-0 ]
  1S = 1# − 0# [ Is-1 , Is-0 ]

  infixl 6 _+S_
  infixl 7 _*S_
  _+S_ _*S_ : Sg → Sg → Sg
  x +S y = (pos x + pos y) − (neg x + neg y) [ Is-+ (pos-fin x) (pos-fin y) , Is-+ (neg-fin x) (neg-fin y) ]
  x *S y = (pos x * pos y + neg x * neg y) − (pos x * neg y + neg x * pos y)
    [ Is-+ (Is-* (pos-fin x) (pos-fin y)) (Is-* (neg-fin x) (neg-fin y))
    , Is-+ (Is-* (pos-fin x) (neg-fin y)) (Is-* (neg-fin x) (pos-fin y)) ]

  -S_ : Sg → Sg
  -S x = neg x − pos x [ neg-fin x , pos-fin x ]

  -- the finite elements embed
  ι : ∀ {a} → Is a → Sg
  ι {a} fa = a − 0# [ fa , Is-0 ]

  ----------------------------------------------------------------------------
  -- congruence

  +S-cong : ∀ {x x′ y y′} → x ≃ x′ → y ≃ y′ → x +S y ≃ x′ +S y′
  +S-cong {x} {x′} {y} {y′} (mk≃ k₁ f₁ e₁) (mk≃ k₂ f₂ e₂) = mk≃ (k₁ + k₂) (Is-+ f₁ f₂) (begin
    (pos x + pos y) + (neg x′ + neg y′) + (k₁ + k₂)
      ≈⟨ solve 6 (λ a b c d e f → (a :+ b) :+ (c :+ d) :+ (e :+ f) := (a :+ c :+ e) :+ (b :+ d :+ f)) refl (pos x) (pos y) (neg x′) (neg y′) k₁ k₂ ⟩
    (pos x + neg x′ + k₁) + (pos y + neg y′ + k₂)
      ≈⟨ +-cong e₁ e₂ ⟩
    (pos x′ + neg x + k₁) + (pos y′ + neg y + k₂)
      ≈⟨ solve 6 (λ a b c d e f → (a :+ b :+ c) :+ (d :+ e :+ f) := (a :+ d) :+ (b :+ e) :+ (c :+ f)) refl (pos x′) (neg x) k₁ (pos y′) (neg y) k₂ ⟩
    (pos x′ + pos y′) + (neg x + neg y) + (k₁ + k₂) ∎)

  -S-cong : ∀ {x x′} → x ≃ x′ → -S x ≃ -S x′
  -S-cong {x} {x′} (mk≃ k f e) = mk≃ k f (begin
    neg x + pos x′ + k ≈⟨ solve 3 (λ a b c → a :+ b :+ c := b :+ a :+ c) refl (neg x) (pos x′) k ⟩
    pos x′ + neg x + k ≈⟨ sym e ⟩
    pos x + neg x′ + k ≈⟨ solve 3 (λ a b c → a :+ b :+ c := b :+ a :+ c) refl (pos x) (neg x′) k ⟩
    neg x′ + pos x + k ∎)

  -- multiplication, in the first argument
  *S-congˡ : ∀ {x x′} y → x ≃ x′ → x *S y ≃ x′ *S y
  *S-congˡ {x} {x′} y (mk≃ k f e) =
    mk≃ ((pos y + neg y) * k)
    (Is-* (Is-+ (pos-fin y) (neg-fin y)) f)
    (begin
        (pos x * pos y + neg x * neg y) + (pos x′ * neg y + neg x′ * pos y) + (pos y + neg y) * k
          ≈⟨ solve 7 (λ px py nx ny px′ nx′ k0 → (px :* py :+ nx :* ny) :+ (px′ :* ny :+ nx′ :* py) :+ (py :+ ny) :* k0
                       := py :* (px :+ nx′ :+ k0) :+ ny :* (px′ :+ nx :+ k0))
                refl (pos x) (pos y) (neg x) (neg y) (pos x′) (neg x′) k ⟩
        pos y * (pos x + neg x′ + k) + neg y * (pos x′ + neg x + k)
          ≈⟨ +-cong (*-cong refl e) refl ⟩
        pos y * (pos x′ + neg x + k) + neg y * (pos x′ + neg x + k)
          ≈⟨ +-cong refl (*-cong refl (sym e)) ⟩
        pos y * (pos x′ + neg x + k) + neg y * (pos x + neg x′ + k)
          ≈⟨ solve 7 (λ px py nx ny px′ nx′ k0 → py :* (px′ :+ nx :+ k0) :+ ny :* (px :+ nx′ :+ k0)
                       := (px′ :* py :+ nx′ :* ny) :+ (px :* ny :+ nx :* py) :+ (py :+ ny) :* k0)
                refl (pos x) (pos y) (neg x) (neg y) (pos x′) (neg x′) k ⟩
        (pos x′ * pos y + neg x′ * neg y) + (pos x * neg y + neg x * pos y) + (pos y + neg y) * k ∎)

  *S-comm : ∀ x y → x *S y ≃ y *S x
  *S-comm x y = mk≃ 0# Is-0 $ solve 4 (λ px nx py ny →
      (px :* py :+ nx :* ny) :+ (py :* nx :+ ny :* px) :+ con 0 := (py :* px :+ ny :* nx) :+ (px :* ny :+ nx :* py) :+ con 0)
      refl (pos x) (neg x) (pos y) (neg y)

  *S-congʳ : ∀ x {y y′} → y ≃ y′ → x *S y ≃ x *S y′
  *S-congʳ x {y} {y′} e = ≃-trans (*S-comm x y) (≃-trans (*S-congˡ x e) (*S-comm y′ x))

  *S-cong : ∀ {x x′ y y′} → x ≃ x′ → y ≃ y′ → x *S y ≃ x′ *S y′
  *S-cong ex ey = ≃-trans (*S-congˡ _ ex) (*S-congʳ _ ey)

  ----------------------------------------------------------------------------
  -- ring laws (all with witness 0)

  +S-assoc : ∀ x y z → (x +S y) +S z ≃ x +S (y +S z)
  +S-assoc x y z = mk≃ 0# Is-0 $ solve 6 (λ px nx py ny pz nz →
      (px :+ py :+ pz) :+ (nx :+ (ny :+ nz)) :+ con 0 := (px :+ (py :+ pz)) :+ (nx :+ ny :+ nz) :+ con 0)
      refl (pos x) (neg x) (pos y) (neg y) (pos z) (neg z)

  +S-comm : ∀ x y → x +S y ≃ y +S x
  +S-comm x y = mk≃ 0# Is-0 $ solve 4 (λ px nx py ny →
      (px :+ py) :+ (ny :+ nx) :+ con 0 := (py :+ px) :+ (nx :+ ny) :+ con 0) refl (pos x) (neg x) (pos y) (neg y)

  +S-identityˡ : ∀ x → 0S +S x ≃ x
  +S-identityˡ x = mk≃ 0# Is-0 $ solve 2 (λ px nx → (con 0 :+ px) :+ nx :+ con 0 := px :+ (con 0 :+ nx) :+ con 0) refl (pos x) (neg x)

  +S-inverseˡ : ∀ x → (-S x) +S x ≃ 0S
  +S-inverseˡ x = mk≃ 0# Is-0 $ solve 2 (λ px nx → (nx :+ px) :+ con 0 :+ con 0 := con 0 :+ (px :+ nx) :+ con 0) refl (pos x) (neg x)

  +S-inverseʳ : ∀ x → x +S (-S x) ≃ 0S
  +S-inverseʳ x = mk≃ 0# Is-0 $ solve 2 (λ px nx → (px :+ nx) :+ con 0 :+ con 0 := con 0 :+ (nx :+ px) :+ con 0) refl (pos x) (neg x)

  *S-assoc : ∀ x y z → (x *S y) *S z ≃ x *S (y *S z)
  *S-assoc x y z = mk≃ 0# Is-0 $ solve 6 (λ px nx py ny pz nz →
      ((px :* py :+ nx :* ny) :* pz :+ (px :* ny :+ nx :* py) :* nz) :+
        (px :* (py :* nz :+ ny :* pz) :+ nx :* (py :* pz :+ ny :* nz)) :+ con 0
      :=
      (px :* (py :* pz :+ ny :* nz) :+ nx :* (py :* nz :+ ny :* pz)) :+
        ((px :* py :+ nx :* ny) :* nz :+ (px :* ny :+ nx :* py) :* pz) :+ con 0)
      refl (pos x) (neg x) (pos y) (neg y) (pos z) (neg z)

  *S-identityˡ : ∀ x → 1S *S x ≃ x
  *S-identityˡ x = mk≃ 0# Is-0 $ solve 2 (λ px nx →
      (con 1 :* px :+ con 0 :* nx) :+ nx :+ con 0 := px :+ (con 1 :* nx :+ con 0 :* px) :+ con 0) refl (pos x) (neg x)

  *S-identityʳ : ∀ x → x *S 1S ≃ x
  *S-identityʳ x = ≃-trans (*S-comm x 1S) (*S-identityˡ x)

  *S-distribˡ : ∀ x y z → x *S (y +S z) ≃ (x *S y) +S (x *S z)
  *S-distribˡ x y z = mk≃ 0# Is-0 $ solve 6 (λ px nx py ny pz nz →
      (px :* (py :+ pz) :+ nx :* (ny :+ nz)) :+ ((px :* ny :+ nx :* py) :+ (px :* nz :+ nx :* pz)) :+ con 0
      := ((px :* py :+ nx :* ny) :+ (px :* pz :+ nx :* nz)) :+ (px :* (ny :+ nz) :+ nx :* (py :+ pz)) :+ con 0)
      refl (pos x) (neg x) (pos y) (neg y) (pos z) (neg z)

  *S-distribʳ : ∀ x y z → (y +S z) *S x ≃ (y *S x) +S (z *S x)
  *S-distribʳ x y z = ≃-trans (*S-comm (y +S z) x)
    (≃-trans (*S-distribˡ x y z) (+S-cong (*S-comm x y) (*S-comm x z)))

  ----------------------------------------------------------------------------
  -- the ring

  isCommutativeRing : IsCommutativeRing _≃_ _+S_ _*S_ -S_ 0S 1S
  isCommutativeRing = record
    { isRing = record
        { +-isAbelianGroup = record
            { isGroup = record
                { isMonoid = record
                    { isSemigroup = record
                        { isMagma = record { isEquivalence = Setoid.isEquivalence Sgˢ ; ∙-cong = +S-cong }
                        ; assoc = +S-assoc }
                    ; identity = +S-identityˡ , (λ x → ≃-trans (+S-comm x 0S) (+S-identityˡ x)) }
                ; inverse = +S-inverseˡ , +S-inverseʳ
                ; ⁻¹-cong = -S-cong }
            ; comm = +S-comm }
        ; *-cong = *S-cong
        ; *-assoc = *S-assoc
        ; *-identity = *S-identityˡ , *S-identityʳ
        ; distrib = *S-distribˡ , *S-distribʳ }
    ; *-comm = *S-comm }

  signedRing : CommutativeRing (c ⊔ p) (c ⊔ ℓ ⊔ p)
  signedRing = record { Carrier = Sg ; _≈_ = _≃_ ; _+_ = _+S_ ; _*_ = _*S_ ; -_ = -S_ ; 0# = 0S ; 1# = 1S
                      ; isCommutativeRing = isCommutativeRing }

  -- the embedding of the finite elements is a semiring homomorphism
  ι-+ : ∀ {a b} (fa : Is a) (fb : Is b) → ι (Is-+ fa fb) ≃ ι fa +S ι fb
  ι-+ {a} {b} fa fb = mk≃ 0# Is-0 $ solve 2 (λ a b → (a :+ b) :+ (con 0 :+ con 0) :+ con 0 := (a :+ b) :+ con 0 :+ con 0) refl a b

  ι-* : ∀ {a b} (fa : Is a) (fb : Is b) → ι (Is-* fa fb) ≃ ι fa *S ι fb
  ι-* {a} {b} fa fb = mk≃ 0# Is-0 $ solve 2 (λ a b → a :* b :+ (a :* con 0 :+ con 0 :* b) :+ con 0
                                           := (a :* b :+ con 0 :* con 0) :+ con 0 :+ con 0) refl a b
