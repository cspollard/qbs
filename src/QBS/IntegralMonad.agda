{-# OPTIONS --safe --without-K #-}

-- A monad on quasi-Borel spaces presented by its integral.  In each model of the measure monad
-- (`Model/Monad`, `Continuous/Monad`, `Continuous/SFinite`) a measure is a representative, and two
-- measures are equal when all their integrals against test functions agree.  Then T X embeds in the
-- continuation (expectation) monad (X → V) → V, equality in T X is the kernel of that embedding, and
-- the functor and monad laws are transported along it: each is a chain of the equations `∫-map`,
-- `∫-η`, `∫-join` and `∫-cong` below.  See Kock, "Commutative monads as a theory of distributions"
-- (TAC 2012) for the embedding into the double dual, Jacobs' expectation monad, and Ścibior et al.,
-- "Denotational validation of higher-order Bayesian inference" (POPL 2018) for the QBS monad
-- presented this way.  No library has the continuation monad on setoids, so the record is local.
module QBS.IntegralMonad where

open import Level using (Level; suc; _⊔_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Endofunctor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (Strength; StrongMonad)
import Categories.Category.Cartesian.Monoidal as CM
import Categories.Category.CartesianClosed.Canonical as Canonical

open import QBS.Core
open import QBS.Category using (QBSCat)
open import QBS.Limits using (_×Q_)
open import QBS.Exponential using (cartesianClosed)

-- Tests: the functions that are integrated, with values in the setoid V, and their precomposition with maps.
record Tests {ℓ c e} (S : RandomSource ℓ) (V : Setoid c e) (t : Level) : Set (suc ℓ ⊔ c ⊔ e ⊔ suc t) where
  open QBS
  open Hom
  private module V = Setoid V
  field
    Test : QBS S → Set t
    eval : ∀ {X} → Test X → ∣ X ∣ → V.Carrier
    eval-cong : ∀ {X} (f : Test X) {x y} → Setoid._≈_ (Carrier X) x y → eval f x V.≈ eval f y
    _∘ᵗ_ : ∀ {X Y} → Test Y → Hom S X Y → Test X
    eval-∘ : ∀ {X Y} (g : Test Y) (f : Hom S X Y) x → eval (g ∘ᵗ f) x V.≈ eval g (map f ⟨$⟩ x)

-- A type constructor T on QBS with integration against tests: equality in T X is equality of all integrals,
-- and integration is itself a test on T X.
record Integral {ℓ c e} (S : RandomSource ℓ) (V : Setoid c e) (t : Level) : Set (suc ℓ ⊔ c ⊔ e ⊔ suc t) where
  open QBS
  private module V = Setoid V
  field
    tests : Tests S V t
  open Tests tests public
  field
    TQ : QBS S → QBS S
    ∫ : ∀ X → ∣ TQ X ∣ → Test X → V.Carrier
    ∫-ext : ∀ X {p q} → (∀ f → ∫ X p f V.≈ ∫ X q f) → Setoid._≈_ (Carrier (TQ X)) p q
    ∫-cong : ∀ X p {f g} → (∀ x → eval f x V.≈ eval g x) → ∫ X p f V.≈ ∫ X p g
    ∫ᶠ : ∀ X → Test X → Test (TQ X)
    eval-∫ᶠ : ∀ X (f : Test X) p → eval (∫ᶠ X f) p V.≈ ∫ X p f

-- The functorial action, unit and join, with their integral equations.
record MonadData {ℓ c e t} {S : RandomSource ℓ} {V : Setoid c e} (I : Integral S V t) : Set (suc ℓ ⊔ c ⊔ e ⊔ t) where
  open Integral I
  open QBS
  open Hom
  private module V = Setoid V
  field
    TH : ∀ {X Y} → Hom S X Y → Hom S (TQ X) (TQ Y)
    ηH : ∀ X → Hom S X (TQ X)
    joinH : ∀ X → Hom S (TQ (TQ X)) (TQ X)
    ∫-map : ∀ {X Y} (f : Hom S X Y) p g → ∫ Y (map (TH f) ⟨$⟩ p) g V.≈ ∫ X p (g ∘ᵗ f)
    ∫-η : ∀ X x f → ∫ X (map (ηH X) ⟨$⟩ x) f V.≈ eval f x
    ∫-join : ∀ X p f → ∫ X (map (joinH X) ⟨$⟩ p) f V.≈ ∫ (TQ X) p (∫ᶠ X f)

-- The functor and monad laws.
module Laws {ℓ c e t} {S : RandomSource ℓ} {V : Setoid c e} (I : Integral S V t) (M : MonadData I) where
  open Integral I
  open MonadData M
  open QBS
  open Hom
  private module V = Setoid V
  open V using () renaming (sym to ≈ˢ)
  infixr 5 _⟨≈⟩_
  _⟨≈⟩_ : ∀ {a b d} → a V.≈ b → b V.≈ d → a V.≈ d
  _⟨≈⟩_ = V.trans

  -- the test ∫ – f at a map of measures
  ∫ᶠ-map : ∀ {X Y} (f : Hom S X Y) (g : Test Y) q →
    eval (∫ᶠ Y g ∘ᵗ TH f) q V.≈ eval (∫ᶠ X (g ∘ᵗ f)) q
  ∫ᶠ-map {X} {Y} f g q =
    eval-∘ (∫ᶠ Y g) (TH f) q ⟨≈⟩ eval-∫ᶠ Y g (map (TH f) ⟨$⟩ q) ⟨≈⟩ ∫-map f q g ⟨≈⟩ ≈ˢ (eval-∫ᶠ X (g ∘ᵗ f) q)

  ∫ᶠ-join : ∀ X (f : Test X) q →
    eval (∫ᶠ X f ∘ᵗ joinH X) q V.≈ eval (∫ᶠ (TQ X) (∫ᶠ X f)) q
  ∫ᶠ-join X f q =
    eval-∘ (∫ᶠ X f) (joinH X) q ⟨≈⟩ eval-∫ᶠ X f (map (joinH X) ⟨$⟩ q) ⟨≈⟩ ∫-join X q f
      ⟨≈⟩ ≈ˢ (eval-∫ᶠ (TQ X) (∫ᶠ X f) q)

  ∫ᶠ-η : ∀ X (f : Test X) x → eval (∫ᶠ X f ∘ᵗ ηH X) x V.≈ eval f x
  ∫ᶠ-η X f x = eval-∘ (∫ᶠ X f) (ηH X) x ⟨≈⟩ eval-∫ᶠ X f (map (ηH X) ⟨$⟩ x) ⟨≈⟩ ∫-η X x f

  TF : Endofunctor (QBSCat S)
  TF = record
    { F₀ = TQ
    ; F₁ = TH
    ; identity = λ {X} {p} → ∫-ext X (λ g → ∫-map (idH S) p g ⟨≈⟩ ∫-cong X p (eval-∘ g (idH S)))
    ; homomorphism = λ {X} {Y} {Z} {f} {h} {p} → ∫-ext Z (λ k →
        ∫-map (_∘H_ S h f) p k ⟨≈⟩
          (∫-cong X p (λ x → eval-∘ k (_∘H_ S h f) x ⟨≈⟩ ≈ˢ (eval-∘ (k ∘ᵗ h) f x ⟨≈⟩ eval-∘ k h (map f ⟨$⟩ x)) ) ⟨≈⟩
            ≈ˢ (∫-map h (map (TH f) ⟨$⟩ p) k ⟨≈⟩ ∫-map f p (k ∘ᵗ h))))
    ; F-resp-≈ = λ {X} {Y} {f} {h} e {p} → ∫-ext Y (λ k →
        ∫-map f p k ⟨≈⟩ ∫-cong X p (λ x → eval-∘ k f x ⟨≈⟩ eval-cong k (e {x}) ⟨≈⟩ ≈ˢ (eval-∘ k h x)) ⟨≈⟩ ≈ˢ (∫-map h p k))
    }

  ηN : NaturalTransformation idF TF
  ηN = ntHelper record
    { η = ηH
    ; commute = λ {X} {Y} f {x} → ∫-ext Y (λ g →
        ∫-η Y (map f ⟨$⟩ x) g ⟨≈⟩ ≈ˢ (eval-∘ g f x) ⟨≈⟩ ≈ˢ (∫-η X x (g ∘ᵗ f)) ⟨≈⟩ ≈ˢ (∫-map f (map (ηH X) ⟨$⟩ x) g))
    }

  μN : NaturalTransformation (TF ∘F TF) TF
  μN = ntHelper record
    { η = joinH
    ; commute = λ {X} {Y} f {p} → ∫-ext Y (λ g →
        ∫-join Y (map (TH (TH f)) ⟨$⟩ p) g ⟨≈⟩ ∫-map (TH f) p (∫ᶠ Y g) ⟨≈⟩
          ∫-cong (TQ X) p (λ q → ∫ᶠ-map f g q) ⟨≈⟩
          ≈ˢ (∫-map f (map (joinH X) ⟨$⟩ p) g ⟨≈⟩ ∫-join X p (g ∘ᵗ f)))
    }

  TM : Monad (QBSCat S)
  TM = record
    { F = TF
    ; η = ηN
    ; μ = μN
    ; assoc = λ {X} {p} → ∫-ext X (λ f →
        ∫-join X (map (TH (joinH X)) ⟨$⟩ p) f ⟨≈⟩ ∫-map (joinH X) p (∫ᶠ X f) ⟨≈⟩
          ∫-cong (TQ (TQ X)) p (∫ᶠ-join X f) ⟨≈⟩
          ≈ˢ (∫-join X (map (joinH (TQ X)) ⟨$⟩ p) f ⟨≈⟩ ∫-join (TQ X) p (∫ᶠ X f)))
    ; sym-assoc = λ {X} {p} → ∫-ext X (λ f →
        ∫-join X (map (joinH (TQ X)) ⟨$⟩ p) f ⟨≈⟩ ∫-join (TQ X) p (∫ᶠ X f) ⟨≈⟩
          ≈ˢ (∫-join X (map (TH (joinH X)) ⟨$⟩ p) f ⟨≈⟩ ∫-map (joinH X) p (∫ᶠ X f) ⟨≈⟩
            ∫-cong (TQ (TQ X)) p (∫ᶠ-join X f)))
    ; identityˡ = λ {X} {p} → ∫-ext X (λ f →
        ∫-join X (map (TH (ηH X)) ⟨$⟩ p) f ⟨≈⟩ ∫-map (ηH X) p (∫ᶠ X f) ⟨≈⟩ ∫-cong X p (∫ᶠ-η X f))
    ; identityʳ = λ {X} {p} → ∫-ext X (λ f →
        ∫-join X (map (ηH (TQ X)) ⟨$⟩ p) f ⟨≈⟩ ∫-η (TQ X) p (∫ᶠ X f) ⟨≈⟩ eval-∫ᶠ X f p)
    }

-- The left strength σ_{X,Y} : X × T Y → T (X × Y), (x , q) ↦ T (x , –) q, is determined by its integral:
-- integrating against a test f over X × Y is integrating q against the test y ↦ f (x , y).
record IntegralStrength {ℓ c e t} {S : RandomSource ℓ} {V : Setoid c e} (I : Integral S V t) :
    Set (suc ℓ ⊔ c ⊔ e ⊔ t) where
  open Integral I
  open QBS
  open Hom
  private module V = Setoid V
  field
    σH : ∀ X Y → Hom S (_×Q_ S X (TQ Y)) (TQ (_×Q_ S X Y))
    -- the test y ↦ f (x , y)
    fixᵗ : ∀ {X Y} → ∣ X ∣ → Test (_×Q_ S X Y) → Test Y
    eval-fix : ∀ {X Y} x (f : Test (_×Q_ S X Y)) y → eval (fixᵗ x f) y V.≈ eval f (x , y)
    ∫-σ : ∀ X Y x q (f : Test (_×Q_ S X Y)) →
      ∫ (_×Q_ S X Y) (map (σH X Y) ⟨$⟩ (x , q)) f V.≈ ∫ Y q (fixᵗ x f)

-- The strength laws, and so the strong monad.
module StrongLaws {ℓ c e t} {S : RandomSource ℓ} {V : Setoid c e} (I : Integral S V t) (M : MonadData I)
    (J : IntegralStrength I) where
  open Integral I
  open MonadData M
  open IntegralStrength J
  open Laws I M
  open QBS
  open Hom
  private module V = Setoid V
  open V using () renaming (sym to ≈ˢ)

  private
    cartesian = Canonical.CartesianClosed.isCartesian (cartesianClosed S)
    Vm = CM.CartesianMonoidal.monoidal cartesian
    {-# INLINE cartesian #-}
    {-# INLINE Vm #-}

  -- naturality of σ along a map F that is f₁ × f₂
  σ-nat : ∀ {X Y X′ Y′} (F : Hom S (_×Q_ S X Y) (_×Q_ S X′ Y′)) (f₁ : Hom S X X′) (f₂ : Hom S Y Y′) →
    (∀ x y → Setoid._≈_ (Carrier (_×Q_ S X′ Y′)) (map F ⟨$⟩ (x , y)) (map f₁ ⟨$⟩ x , map f₂ ⟨$⟩ y)) →
    ∀ x q (h : Test (_×Q_ S X′ Y′)) →
    ∫ (_×Q_ S X′ Y′) (map (σH X′ Y′) ⟨$⟩ (map f₁ ⟨$⟩ x , map (TH f₂) ⟨$⟩ q)) h
      V.≈ ∫ (_×Q_ S X′ Y′) (map (TH F) ⟨$⟩ (map (σH X Y) ⟨$⟩ (x , q))) h
  σ-nat {X} {Y} {X′} {Y′} F f₁ f₂ ex x q h =
    ∫-σ X′ Y′ (map f₁ ⟨$⟩ x) (map (TH f₂) ⟨$⟩ q) h ⟨≈⟩ ∫-map f₂ q (fixᵗ (map f₁ ⟨$⟩ x) h) ⟨≈⟩
      ∫-cong Y q (λ y → eval-∘ (fixᵗ (map f₁ ⟨$⟩ x) h) f₂ y ⟨≈⟩ eval-fix (map f₁ ⟨$⟩ x) h (map f₂ ⟨$⟩ y)
        ⟨≈⟩ eval-cong h (Setoid.sym (Carrier (_×Q_ S X′ Y′)) (ex x y))
        ⟨≈⟩ ≈ˢ (eval-fix x (h ∘ᵗ F) y ⟨≈⟩ eval-∘ h F (x , y))) ⟨≈⟩
      ≈ˢ (∫-map F (map (σH X Y) ⟨$⟩ (x , q)) h ⟨≈⟩ ∫-σ X Y x q (h ∘ᵗ F))

  strength : Strength Vm TM
  strength = record
    { strengthen = record
        { η = λ { (X , Y) → σH X Y }
        ; commute = λ { {X₁ , X₂} {Y₁ , Y₂} (f₁ , f₂) {(x , q)} →
            ∫-ext (_×Q_ S Y₁ Y₂) (σ-nat _ f₁ f₂ (λ x y → Setoid.refl (Carrier (_×Q_ S Y₁ Y₂))) x q) }
        ; sym-commute = λ { {X₁ , X₂} {Y₁ , Y₂} (f₁ , f₂) {(x , q)} →
            ∫-ext (_×Q_ S Y₁ Y₂) (λ h → ≈ˢ (σ-nat _ f₁ f₂ (λ x y → Setoid.refl (Carrier (_×Q_ S Y₁ Y₂))) x q h)) }
        }
    ; identityˡ = λ {A} {(t , q)} → ∫-ext A (λ h →
        ∫-map _ (map (σH _ A) ⟨$⟩ (t , q)) h ⟨≈⟩ ∫-σ _ A t q _ ⟨≈⟩
          ∫-cong A q (λ y → eval-fix t _ y ⟨≈⟩ eval-∘ h _ (t , y)))
    ; η-comm = λ {A} {B} {(a , b)} → ∫-ext (_×Q_ S A B) (λ h →
        ∫-σ A B a (map (ηH B) ⟨$⟩ b) h ⟨≈⟩ ∫-η B b (fixᵗ a h) ⟨≈⟩ eval-fix a h b ⟨≈⟩ ≈ˢ (∫-η (_×Q_ S A B) (a , b) h))
    ; μ-η-comm = λ {A} {B} {(a , P)} → ∫-ext (_×Q_ S A B) (λ g →
        ∫-join (_×Q_ S A B) (map (TH (σH A B)) ⟨$⟩ (map (σH A (TQ B)) ⟨$⟩ (a , P))) g ⟨≈⟩
          ∫-map (σH A B) (map (σH A (TQ B)) ⟨$⟩ (a , P)) (∫ᶠ (_×Q_ S A B) g) ⟨≈⟩
          ∫-σ A (TQ B) a P (∫ᶠ (_×Q_ S A B) g ∘ᵗ σH A B) ⟨≈⟩
          ∫-cong (TQ B) P (λ ν → eval-fix a (∫ᶠ (_×Q_ S A B) g ∘ᵗ σH A B) ν ⟨≈⟩
             eval-∘ (∫ᶠ (_×Q_ S A B) g) (σH A B) (a , ν) ⟨≈⟩ eval-∫ᶠ (_×Q_ S A B) g (map (σH A B) ⟨$⟩ (a , ν)) ⟨≈⟩
             ∫-σ A B a ν g ⟨≈⟩ ≈ˢ (eval-∫ᶠ B (fixᵗ a g) ν)) ⟨≈⟩
          ≈ˢ (∫-σ A B a (map (joinH B) ⟨$⟩ P) g ⟨≈⟩ ∫-join B P (fixᵗ a g)))
    ; strength-assoc = λ {A} {B} {C} {((x , y) , q)} → ∫-ext (_×Q_ S A (_×Q_ S B C)) (λ h →
        ∫-map _ (map (σH (_×Q_ S A B) C) ⟨$⟩ ((x , y) , q)) h ⟨≈⟩ ∫-σ (_×Q_ S A B) C (x , y) q _ ⟨≈⟩
          ∫-cong C q (λ z → eval-fix (x , y) _ z ⟨≈⟩ eval-∘ h _ ((x , y) , z) ⟨≈⟩
            ≈ˢ (eval-fix y (fixᵗ x h) z ⟨≈⟩ eval-fix x h (y , z))) ⟨≈⟩
          ≈ˢ (∫-σ A (_×Q_ S B C) x (map (σH B C) ⟨$⟩ (y , q)) h ⟨≈⟩ ∫-σ B C y q (fixᵗ x h)))
    }

  strongMonad : StrongMonad Vm
  strongMonad = record { M = TM ; strength = strength }
  {-# INLINE strongMonad #-}
