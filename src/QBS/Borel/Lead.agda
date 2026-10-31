{-# OPTIONS --safe --without-K #-}

-- A countable Borel partition of Cantor space with infinitely many pieces: `lead k` is the number
-- of leading `true`s (0 for the constant `true` sequence, where it is a classical default).  The
-- fibre `{lead = n}` is the cylinder `trueⁿ false …`, together with the all-true sequence for n = 0.
module QBS.Borel.Lead where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (_<?_; <-irrefl; ≮⇒≥; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)

open import QBS.Borel.Core
open import QBS.Classical using (LEM₀)

-- the first n bits are true
Pre : ℕ → Cantor → Set
Pre n k = ∀ i → i < n → k i ≡ true

private
  step : Bool → ℕ → ℕ
  step true m = suc m
  step false m = zero

-- the number of leading trues among the first N bits
leadF : ℕ → Cantor → ℕ
leadF zero k = zero
leadF (suc N) k = step (k zero) (leadF N (λ i → k (suc i)))

private
  preCons : ∀ n (k : Cantor) → k zero ≡ true → Pre n (λ i → k (suc i)) → Pre (suc n) k
  preCons n k k0 p zero _ = k0
  preCons n k k0 p (suc i) (s<s i<n) = p i i<n

  preUncons : ∀ n (k : Cantor) → Pre (suc n) k → (k zero ≡ true) × Pre n (λ i → k (suc i))
  preUncons n k p = p zero z<s , (λ i i<n → p (suc i) (s<s i<n))

  Spec : ℕ → ℕ → Cantor → Set
  Spec N n k = ((n < N) × Pre n k × (k n ≡ false)) ⊎ ((n ≡ N) × Pre N k)

  ¬<0 : ∀ {n} → n < zero → ⊥
  ¬<0 ()

  false≢true : false ≡ true → ⊥
  false≢true ()

  F-fwd : ∀ N n k → leadF N k ≡ n → Spec N n k
  F-fwd zero n k e = inj₂ (sym e , λ i i<0 → ⊥-elim (¬<0 i<0))
  F-fwd (suc N) n k e with k zero in eq
  F-fwd (suc N) _ k refl | false = inj₁ (z<s , (λ i ()) , eq)
  F-fwd (suc N) _ k refl | true with F-fwd N (leadF N (λ i → k (suc i))) (λ i → k (suc i)) refl
  ... | inj₁ (n″<N , pre , kn) = inj₁ (s<s n″<N , preCons _ k eq pre , kn)
  ... | inj₂ (n″≡N , pre) = inj₂ (cong suc n″≡N , preCons N k eq pre)

  F-back : ∀ N n k → Spec N n k → leadF N k ≡ n
  F-back zero n k (inj₁ (n<0 , _)) = ⊥-elim (¬<0 n<0)
  F-back zero n k (inj₂ (n≡0 , _)) = sym n≡0
  F-back (suc N) n k s with k zero in eq
  F-back (suc N) n k (inj₁ (n<N , pre , kn)) | false with n
  ... | zero = refl
  ... | suc n′ = ⊥-elim (false≢true (trans (sym eq) (proj₁ (preUncons n′ k pre))))
  F-back (suc N) n k (inj₂ (n≡N , pre)) | false = ⊥-elim (false≢true (trans (sym eq) (proj₁ (preUncons N k pre))))
  F-back (suc N) n k (inj₁ (n<N , pre , kn)) | true with n
  ... | zero = ⊥-elim (false≢true (trans (sym kn) eq))
  ... | suc n′ = cong suc (F-back N n′ (λ i → k (suc i)) (inj₁ (pred< n<N , proj₂ (preUncons n′ k pre) , kn)))
    where pred< : ∀ {a b} → suc a < suc b → a < b
          pred< (s<s p) = p
  F-back (suc N) n k (inj₂ (n≡N , pre)) | true =
    trans (cong suc (F-back N N (λ i → k (suc i)) (inj₂ (refl , proj₂ (preUncons N k pre))))) (sym n≡N)

  -- the sequence trueⁿ false false …
decBool : ∀ {A : Set} → Dec A → Bool
decBool (yes _) = true
decBool (no _) = false

pt : ℕ → Cantor
pt n i = decBool (i <? n)

module Lead (lem : LEM₀) where
  Ex : Cantor → Set
  Ex k = Σ ℕ (λ m → k m ≡ false)

  leadW : ∀ k → Ex k ⊎ (Ex k → ⊥) → ℕ
  leadW k (inj₁ (m , _)) = leadF (suc m) k
  leadW k (inj₂ _) = zero

  lead : Cantor → ℕ
  lead k = leadW k (lem (Ex k))

  Z : Cantor → Set
  Z k = ∀ m → k m ≡ true

  Fib : ℕ → Cantor → Set
  Fib n k = (Pre n k × (k n ≡ false)) ⊎ ((n ≡ zero) × Z k)

  private
    notFalse : ∀ b → (b ≡ false → ⊥) → b ≡ true
    notFalse true _ = refl
    notFalse false f = ⊥-elim (f refl)

  leadW-fwd : ∀ n k s → leadW k s ≡ n → Fib n k
  leadW-fwd n k (inj₁ (m , km)) e with F-fwd (suc m) n k e
  ... | inj₁ (_ , pre , kn) = inj₁ (pre , kn)
  ... | inj₂ (_ , pre) = ⊥-elim (false≢true (trans (sym km) (pre m (s<s′ m))))
    where s<s′ : ∀ m → m < suc m
          s<s′ zero = z<s
          s<s′ (suc m) = s<s (s<s′ m)
  leadW-fwd n k (inj₂ ¬ex) e = inj₂ (sym e , λ m → notFalse (k m) (λ km → ¬ex (m , km)))

  leadW-back : ∀ n k s → Fib n k → leadW k s ≡ n
  leadW-back n k (inj₁ (m , km)) (inj₁ (pre , kn)) with n <? suc m
  ... | yes n<sm = F-back (suc m) n k (inj₁ (n<sm , pre , kn))
  ... | no ¬p = ⊥-elim (false≢true (trans (sym km) (pre m (≮⇒≥ ¬p))))
  leadW-back n k (inj₁ (m , km)) (inj₂ (_ , z)) = ⊥-elim (false≢true (trans (sym km) (z m)))
  leadW-back n k (inj₂ ¬ex) (inj₁ (_ , kn)) = ⊥-elim (¬ex (n , kn))
  leadW-back n k (inj₂ ¬ex) (inj₂ (n≡0 , _)) = sym n≡0

  ----------------------------------------------------------------------------
  -- Borel fibres

  impl-borel : ∀ {P : Set} {B : Pred} → Dec P → Borel B → Borel (λ x → P → B x)
  impl-borel (yes p) bb = resp (λ x → (λ t _ → t) , (λ f → f p)) bb
  impl-borel (no ¬p) bb = resp (λ x → (λ _ q → ⊥-elim (¬p q)) , (λ _ → tt)) ⊤-borel

  borelPre : ∀ n → Borel (Pre n)
  borelPre n = ⋂ (λ i → impl-borel (i <? n) (gen i true))

  borelFib : ∀ n → Borel (Fib n)
  borelFib n = union₂ (inter₂ (borelPre n) (gen n false)) (inter₂ cst (⋂ (λ m → gen m true)))
    where
      cst : Borel (λ (_ : Cantor) → n ≡ zero)
      cst with n ≟ zero
      ... | yes p = resp (λ x → (λ _ → p) , (λ _ → tt)) ⊤-borel
      ... | no ¬p = resp (λ x → (λ ()) , (λ e → ¬p e)) ⊥-borel

  lead-partition : Partition lead
  lead-partition n = resp (λ k → (λ f → leadW-back n k (lem (Ex k)) f) , (λ e → leadW-fwd n k (lem (Ex k)) e)) (borelFib n)

  -- the point trueⁿ false false … lies in the n-th piece
  lead-pt : ∀ n → lead (pt n) ≡ n
  lead-pt n = leadW-back n (pt n) (lem (Ex (pt n))) (inj₁ (pre , kn))
    where
      yesT : ∀ {A : Set} (d : Dec A) → A → decBool d ≡ true
      yesT (yes _) _ = refl
      yesT (no ¬a) a = ⊥-elim (¬a a)
      noF : ∀ {A : Set} (d : Dec A) → (A → ⊥) → decBool d ≡ false
      noF (yes a) ¬a = ⊥-elim (¬a a)
      noF (no _) _ = refl
      pre : Pre n (pt n)
      pre i i<n = yesT (i <? n) i<n
      kn : pt n n ≡ false
      kn = noF (n <? n) (λ p → <-irrefl refl p)
