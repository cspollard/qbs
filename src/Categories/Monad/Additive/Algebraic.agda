{-# OPTIONS --safe --without-K #-}

-- Additive monads are the algebraic monads for the theory of commutative monoids (`Theory.Equational.CommutativeMonoid`):
-- `IsAdditive M` and `IsAlgebraic CommMonoid M` carry the same structure.
--   `toAlgebraic`    `IsAdditive M → IsAlgebraic CommMonoid M`   (`op unit = 𝟘`, `op plus = ⊕`)
--   `fromAlgebraic`  `IsAlgebraic CommMonoid M → IsAdditive M`
open import Categories.Category.Core using (Category)

module Categories.Monad.Additive.Algebraic {o h e} {C : Category o h e} where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (proj₁; _,_)
open import Algebra.Structures using (IsCommutativeMonoid)

open import Categories.Category using (_[_,_])
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Monad using (Monad)
open import Categories.Monad.Additive using (IsAdditive)
open import Categories.Monad.Algebraic using (IsAlgebraic; Operations)
open import Categories.Theory.Equational.CommutativeMonoid

toAlgebraic : ∀ {M : Monad C} → IsAdditive M → IsAlgebraic CommMonoid M
toAlgebraic {M} AK = record { operations = ops ; laws = laws }
  where
    K = Kleisli M
    module K = Category K
    open IsAdditive AK

    op : ∀ (f : CMOp) {X Y} → (Fin (cm-arity f) → K [ X , Y ]) → K [ X , Y ]
    op unit _ = 𝟘
    op plus gs = gs zero ⊕ gs (suc zero)

    ops : Operations CommMonoid M
    ops = record { op = op ; op-cong = op-cong ; op-resp-∘ = op-resp-∘ }
      where
        op-cong : ∀ (f : CMOp) {X Y} {gs hs : Fin (cm-arity f) → K [ X , Y ]}
          → (∀ i → gs i K.≈ hs i) → op f gs K.≈ op f hs
        op-cong unit eq = K.Equiv.refl
        op-cong plus eq = ⊕-cong (eq zero) (eq (suc zero))

        op-resp-∘ : ∀ (f : CMOp) {A B D E} (k : K [ D , E ]) (gs : Fin (cm-arity f) → K [ B , D ]) (h : K [ A , B ])
          → k K.∘ op f gs K.∘ h K.≈ op f (λ i → k K.∘ gs i K.∘ h)
        op-resp-∘ unit k gs h = 𝟘-resp-∘ k h
        op-resp-∘ plus k gs h = ⊕-resp-∘ k (gs zero) (gs (suc zero)) h

    module CM {X Y} = IsCommutativeMonoid (isCommutativeMonoid {X} {Y})

    laws : ∀ (q : CMEqn) {X Y} (ρ : Fin (cm-vars q) → K [ X , Y ])
      → Operations.eval ops (cm-lhs q) ρ K.≈ Operations.eval ops (cm-rhs q) ρ
    laws assoc ρ = CM.assoc _ _ _
    laws comm ρ = CM.comm _ _
    laws identity ρ = proj₁ CM.identity _

fromAlgebraic : ∀ {M : Monad C} → IsAlgebraic CommMonoid M → IsAdditive M
fromAlgebraic {M} AL = record
  { 𝟘 = 𝟘
  ; _⊕_ = _⊕_
  ; isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record { isEquivalence = K.equiv ; ∙-cong = ⊕-cong }
        ; assoc = ⊕-assoc
        }
      ; identity = ⊕-identityˡ , λ x → K.Equiv.trans (⊕-comm x 𝟘) (⊕-identityˡ x)
      }
    ; comm = ⊕-comm
    }
  ; ⊕-resp-∘ = λ k f g h → K.Equiv.trans (op-resp-∘ plus k (pair f g) h) (plus-ext K.Equiv.refl K.Equiv.refl)
  ; 𝟘-resp-∘ = λ k h → op-resp-∘ unit k (λ ()) h ○ op-cong unit λ ()
  }
  where
    K = Kleisli M
    module K = Category K
    open IsAlgebraic AL
    open K.HomReasoning using (_○_)

    pair : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → Fin 2 → K [ X , Y ]
    pair f g zero = f
    pair f g (suc zero) = g

    𝟘 : ∀ {X Y} → K [ X , Y ]
    𝟘 = op unit (λ ())

    _⊕_ : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → K [ X , Y ]
    f ⊕ g = op plus (pair f g)

    plus-ext : ∀ {X Y} {gs hs : Fin 2 → K [ X , Y ]}
      → gs zero K.≈ hs zero → gs (suc zero) K.≈ hs (suc zero) → op plus gs K.≈ op plus hs
    plus-ext a b = op-cong plus λ { zero → a ; (suc zero) → b }

    ⊕-cong : ∀ {X Y} {a b c d : K [ X , Y ]} → a K.≈ b → c K.≈ d → (a ⊕ c) K.≈ (b ⊕ d)
    ⊕-cong = plus-ext

    open K.HomReasoning

    ⊕-comm : ∀ {X Y} (a b : K [ X , Y ]) → (a ⊕ b) K.≈ (b ⊕ a)
    ⊕-comm a b = plus-ext K.Equiv.refl K.Equiv.refl ○ laws comm (pair a b) ○ plus-ext K.Equiv.refl K.Equiv.refl

    ⊕-identityˡ : ∀ {X Y} (a : K [ X , Y ]) → (𝟘 ⊕ a) K.≈ a
    ⊕-identityˡ a = plus-ext (op-cong unit λ ()) K.Equiv.refl ○ laws identity (λ _ → a)

    ⊕-assoc : ∀ {X Y} (a b c : K [ X , Y ]) → ((a ⊕ b) ⊕ c) K.≈ (a ⊕ (b ⊕ c))
    ⊕-assoc a b c = plus-ext (plus-ext K.Equiv.refl K.Equiv.refl) K.Equiv.refl
      ○ laws assoc (λ { zero → a ; (suc zero) → b ; (suc (suc zero)) → c })
      ○ plus-ext K.Equiv.refl (plus-ext K.Equiv.refl K.Equiv.refl)
