{-# OPTIONS --safe --without-K #-}

-- The strict level sets {x | q < h x} of a measurable function h : R → [0,1] (values lower
-- cuts) are Borel, by induction on the derivation that h is measurable.
module QBS.Analysis.LevelSets where

import Level as L
open import Level using (lift; lower)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import Data.Rational.Unnormalised.Base using (mkℚᵘ; _+_; _*_; -_; _<_; _≤_; _≃_)
open import QBS.Analysis.RationalLemmas
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Model.Pairing
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.LowerReals
open Cut
open _⊑_

-- an enumeration of the rationals
enumSign : ℕ → ℕ → ℤ
enumSign zero a = + a
enumSign (suc _) a = -[1+ a ]

enumQ : ℕ → ℚᵘ
enumQ k = mkℚᵘ (enumSign (proj₁ (unpair (proj₁ (unpair k)))) (proj₂ (unpair (proj₁ (unpair k))))) (proj₂ (unpair k))

enumQ-surj : ∀ q → Σ ℕ (λ k → enumQ k ≡ q)
enumQ-surj (mkℚᵘ (+ a) b) = pair (pair 0 a) b , go
  where go : enumQ (pair (pair 0 a) b) ≡ mkℚᵘ (+ a) b
        go rewrite unpair-pair (pair 0 a) b | unpair-pair 0 a = ≡.refl
enumQ-surj (mkℚᵘ -[1+ a ] b) = pair (pair 1 a) b , go
  where go : enumQ (pair (pair 1 a) b) ≡ mkℚᵘ -[1+ a ] b
        go rewrite unpair-pair (pair 1 a) b | unpair-pair 1 a = ≡.refl

module LevelSets (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  A : OmegaSemiring (L.suc L.zero)
  A = LowerRealsOmega lem
  open Measurable A using (Fun; ind; sumF; supF; complF)
  open OmegaSemiring A using (_≈_; 0#; 1#; ⨆; Increasing)

  -- a constant proposition is a Borel set
  borel-prop : ∀ (P : Set) → Borel (λ (_ : Cantor) → P)
  borel-prop P with lem P
  ... | inj₁ p = resp (λ x → (λ _ → p) , (λ _ → tt)) ⊤-borel
  ... | inj₂ np = resp (λ x → (λ ()) , (λ p → np p)) ⊥-borel

  -- the level set of h at q
  Lvl : (R₁ → Cut) → ℚᵘ → Pred
  Lvl h q c = mem (h (lift c)) q

  -- the indicator-like case
  LS-ind : ∀ {U h} c → Borel U → (∀ x → U (lower x) → h x ≈ c) → (∀ x → (U (lower x) → ⊥) → h x ≈ 0#) →
    ∀ q → Borel (Lvl h q)
  LS-ind {U} {h} c bU e₀ e₁ q = resp e (union₂ (inter₂ bU (borel-prop (mem c q)))
                                              (inter₂ (compl bU) (borel-prop (q < 0ℚᵘ))))
    where
      e : (λ x → (U x × mem c q) ⊎ ((U x → ⊥) × q < 0ℚᵘ)) ≐ Lvl h q
      e x = (λ { (inj₁ (u , m)) → ap (proj₂ (e₀ (lift x) u)) q m
               ; (inj₂ (nu , lt)) → ap (proj₂ (e₁ (lift x) nu)) q lt })
          , (λ m → dec (lem (U x)) m)
        where
          dec : (U x ⊎ (U x → ⊥)) → mem (h (lift x)) q → (U x × mem c q) ⊎ ((U x → ⊥) × q < 0ℚᵘ)
          dec (inj₁ u) m = inj₁ (u , ap (proj₁ (e₀ (lift x) u)) q m)
          dec (inj₂ nu) m = inj₂ (nu , ap (proj₁ (e₁ (lift x) nu)) q m)

  LS-sup : ∀ {h} (hs : ℕ → R₁ → Cut) → (∀ n → Fun (hs n)) →
    (∀ n q → Borel (Lvl (hs n) q)) → (inc : ∀ x → Increasing (λ n → hs n x)) →
    (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) → ∀ q → Borel (Lvl h q)
  LS-sup {h} hs fs ih inc e q = resp e′ (⋃ (λ n → ih n q))
    where
      e′ : (λ c → Σ ℕ (λ n → Lvl (hs n) q c)) ≐ Lvl h q
      e′ c = (λ { (n , m) → ap (proj₂ (e (lift c))) q (n , m) })
           , (λ m → ap (proj₁ (e (lift c))) q m)

  LS-sum : ∀ {h h₁ h₂} → (∀ q → Borel (Lvl h₁ q)) → (∀ q → Borel (Lvl h₂ q)) →
    (∀ x → h x ≈ h₁ x ⊕ h₂ x) → ∀ q → Borel (Lvl h q)
  LS-sum {h} {h₁} {h₂} b₁ b₂ e q = resp e′ (⋃ cells)
    where
      r s : ℕ → ℚᵘ
      r k = enumQ (proj₁ (unpair k))
      s k = enumQ (proj₂ (unpair k))
      cells : ∀ k → Borel (λ c → (q ≤ r k + s k) × (Lvl h₁ (r k) c × Lvl h₂ (s k) c))
      cells k = inter₂ (borel-prop (q ≤ r k + s k)) (inter₂ (b₁ (r k)) (b₂ (s k)))
      e′ : (λ c → Σ ℕ (λ k → (q ≤ r k + s k) × (Lvl h₁ (r k) c × Lvl h₂ (s k) c))) ≐ Lvl h q
      e′ c = (λ { (k , le , m₁ , m₂) → ap (proj₂ (e (lift c))) q (r k , s k , m₁ , m₂ , le) })
           , (λ m → let ρ , σ , m₁ , m₂ , le = ap (proj₁ (e (lift c))) q m
                        k₁ , p₁ = enumQ-surj ρ
                        k₂ , p₂ = enumQ-surj σ
                        eq : (enumQ (proj₁ (unpair (pair k₁ k₂))) , enumQ (proj₂ (unpair (pair k₁ k₂)))) ≡ (ρ , σ)
                        eq = ≡.trans (≡.cong₂ _,_ (≡.cong (λ u → enumQ (proj₁ u)) (unpair-pair k₁ k₂)) (≡.cong (λ u → enumQ (proj₂ u)) (unpair-pair k₁ k₂)))
                                     (≡.cong₂ _,_ p₁ p₂)
                    in pair k₁ k₂ , ≡.subst (λ pr → (q ≤ proj₁ pr + proj₂ pr) × (mem (h₁ (lift c)) (proj₁ pr) × mem (h₂ (lift c)) (proj₂ pr)))
                                            (≡.sym eq) (le , m₁ , m₂))

  -- a member of a cut lies below every non-member
  mem-<-of-¬ : ∀ (c : Cut) {q r} → (mem c q → ⊥) → mem c r → r < q
  mem-<-of-¬ c {q} {r} nm m with ≤-or-> q r
  ... | inj₁ q≤r = ⊥-elim (nm (down c q≤r m))
  ... | inj₂ lt = lt

  -- complements: h + h′ = 1.  Pointwise, `q ∈ h x` iff some rational k > q has `1 − k ∉ h′ x`.
  compl-contra : ∀ {h h′ : R₁ → Cut} → (∀ x → h x ⊕ h′ x ≈ 1#) → ∀ q x k →
    q < enumQ k → (mem (h′ x) (1ℚᵘ + - enumQ k) → ⊥) → (mem (h x) q → ⊥) → ⊥
  compl-contra {h} {h′} e q x k q<ek nm no = go (ap (proj₂ (e x)) s s<1)
    where
      s : ℚᵘ
      s = 1ℚᵘ + - (enumQ k + - q)
      s<1 : s < 1ℚᵘ
      s<1 = ≃-<ʳ (solve 1 (λ d → (con 1ℚᵘ :+ :- d) :+ d := con 1ℚᵘ) ≃-refl (enumQ k + - q))
                 (lt-add {s} {enumQ k + - q} (pos-diff q<ek))
      go : Σ ℚᵘ (λ r → Σ ℚᵘ (λ t → mem (h x) r × mem (h′ x) t × s ≤ r + t)) → ⊥
      go (r , t , mr , mt , le) = <-irrefl ≃-refl (≤-<-trans le r+t<s)
        where
          r<q : r < q
          r<q = mem-<-of-¬ (h x) no mr
          t<u : t < 1ℚᵘ + - enumQ k
          t<u = mem-<-of-¬ (h′ x) nm mt
          r+t<s : r + t < s
          r+t<s = ≃-<ʳ (solve 2 (λ q ek → q :+ (con 1ℚᵘ :+ :- ek) := con 1ℚᵘ :+ :- (ek :+ :- q)) ≃-refl q (enumQ k))
                       (+-mono-< r<q t<u)

  compl-bwd : ∀ {h h′ : R₁ → Cut} → (∀ x → h x ⊕ h′ x ≈ 1#) → ∀ q x → mem (h x) q →
    Σ ℕ (λ k → (q < enumQ k) × (mem (h′ x) (1ℚᵘ + - enumQ k) → ⊥))
  compl-bwd {h} {h′} e q x m with open′ (h x) m
  ... | q′ , q<q′ , mq′ with enumQ-surj q′
  ... | k , p = k , ≡.subst (q <_) (≡.sym p) q<q′ , λ m′ →
      <-irrefl ≃-refl (ap (proj₁ (e x)) 1ℚᵘ (q′ , 1ℚᵘ + - q′ , mq′ ,
        ≡.subst (λ z → mem (h′ x) (1ℚᵘ + - z)) p m′ ,
        ≤-≃ (≃-sym (solve 1 (λ u → u :+ (con 1ℚᵘ :+ :- u) := con 1ℚᵘ) ≃-refl q′))))

  LS-compl : ∀ {h h′} → (∀ q → Borel (Lvl h′ q)) → (∀ x → h x ⊕ h′ x ≈ 1#) → ∀ q → Borel (Lvl h q)
  LS-compl {h} {h′} b e q = resp e′ (⋃ cells)
    where
      cells : ∀ k → Borel (λ c → (q < enumQ k) × (Lvl h′ (1ℚᵘ + - enumQ k) c → ⊥))
      cells k = inter₂ (borel-prop (q < enumQ k)) (compl (b (1ℚᵘ + - enumQ k)))

      fwd : ∀ x → Σ ℕ (λ k → (q < enumQ k) × (mem (h′ x) (1ℚᵘ + - enumQ k) → ⊥)) → mem (h x) q
      fwd x (k , q<ek , nm) with lem (mem (h x) q)
      ... | inj₁ yes = yes
      ... | inj₂ no = ⊥-elim (compl-contra {h} {h′} e q x k q<ek nm no)

      e′ : (λ c → Σ ℕ (λ k → (q < enumQ k) × (Lvl h′ (1ℚᵘ + - enumQ k) c → ⊥))) ≐ Lvl h q
      e′ c = fwd (lift c) , compl-bwd {h} {h′} e q (lift c)

  -- every measurable function has Borel level sets
  LS : ∀ {h} → Fun h → ∀ q → Borel (Lvl h q)
  LS {h} (ind c c≤1 bU e₀ e₁ bd) = LS-ind {h = h} c bU e₀ e₁
  LS (sumF {h} {h₁} {h₂} f₁ f₂ e bd) = LS-sum {h} {h₁} {h₂} (LS f₁) (LS f₂) e
  LS (supF {h} hs fs inc e) = LS-sup {h} hs fs (λ n → LS (fs n)) inc e
  LS (complF {h} {h′} f e) = LS-compl {h} {h′} (LS f) e
