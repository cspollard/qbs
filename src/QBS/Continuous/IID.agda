{-# OPTIONS --safe --without-K #-}

-- Independent and identically distributed families (functions of iid families are iid; moments feed `SgMoments`).  On a probability P on Ω, for an s-finite
-- measure μ on Y (a probability law in the theorems: ∫ 1 dμ ≈ 1):
--   * `IID μ n Xs`: the law of the tuple (X₀, …, X_{n−1}) is ≈ᴹ μ^{⊗n} (`FinProd.prodⁿ`); `IIDSeq μ Xs`: every finite
--     prefix of a sequence is iid;
--   * each Xᵢ has law μ (`IID-law`), and the family is mutually independent (`IID-indep`, `Independence.Indep`);
--   * functions of an iid family are iid, with the push-forward law (`IID-map`);
--   * for a signed test f with ∫ f, ∫ f² finite under μ, the observations f ∘ Xᵢ satisfy `SgMoments.Moments` with the
--     mean and variance of f under μ (`IID-moments`); `Continuous/SgSample` then gives the unbiased sample mean and
--     sample variance for every iid family.
-- Route: `IID-law` from `FinProd.margⁿ` with `ProdMap.mapM-comp` and `FinProd.proj-tuple`; `IID-indep` is
-- `FinProd.prodⁿ-cong` with `IID-law`; `IID-map` from `mapM-comp` and push-forward of `prodⁿ` along the coordinatewise
-- map (by induction on n, `ProdMap.map-prod`); `IID-moments` transports integrals along the law
-- (`SignedTransport.Int-map`, `Ex-map`) and uses `Independence.Indep-pair`, `Int-indep`, `Ex-indep` for i ≢ j.
module QBS.Continuous.IID where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; toℕ; zero; suc)

open import QBS.Core
open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_,_; Σ)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Data.Unit.Polymorphic.Base using (tt)
open import QBS.Limits using (1Q)
open import Relation.Binary.Bundles using (Setoid)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.SignedTransport using (module SignedTransport)
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.Independence using (module Independence)
open import QBS.Continuous.SgMoments using (module SgMoments)

module IID (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 1#)
  open Bounded A using (Sg; _≃_; _+S_; _*S_)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-η; _≈ᴹ_; mapM; module C)
  open Product (lemOf lem₁) using (prod-cong)
  open SignedTest lem₁ using (SgT; _∘T_; _*T_)
  open SignedExpect lem₁ using (Int; Ex; bnd≈; Ex-cong)
  open SignedTransport lem₁ using (Int-map; Ex-map)
  open SignedVarAlg lem₁ using (Int-via)
  open Bounded A using (mk≃; finite; ≃-trans; ≃-sym; *S-cong)
  open import QBS.Analysis.Signed using (SubSemiring)
  open SubSemiring finite using (Is-0)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; prodⁿ; proj-tuple; margⁿ; prodⁿ-cong)
  open ProdMap (lemOf lem₁) using (mapM-comp; mapM-cong; mapM-ext; _×H_; map-prod)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open OmegaSemiring A using (refl; sym; trans; +-cong; 0#)
  open Independence lem₁ using (law; Indep; Indep-pair; Int-indep; Ex-indep)
  open SgMoments lem₁ using (Moments)
  open QBS
  open Hom

  ≈ᴹ-trans : ∀ {X : QBS S} {p q r : C.Pre (XW X)} → _≈ᴹ_ {X} p q → _≈ᴹ_ {X} q r → _≈ᴹ_ {X} p r
  ≈ᴹ-trans e e′ h = trans (e h) (e′ h)

  ≈ᴹ-sym : ∀ {X : QBS S} {p q : C.Pre (XW X)} → _≈ᴹ_ {X} p q → _≈ᴹ_ {X} q p
  ≈ᴹ-sym e h = sym (e h)

  -- integrability and expectations respect ≈ᴹ
  Int-≈ : ∀ {X : QBS S} {p q : C.Pre (XW X)} {f : SgT X} → _≈ᴹ_ {X} p q → Int {X} p f → Int {X} q f
  Int-≈ {X} e (i⁺ , i⁻) = bnd≈ {X} (sym (e _)) i⁺ , bnd≈ {X} (sym (e _)) i⁻

  Ex-≈ : ∀ {X : QBS S} {p q : C.Pre (XW X)} (e : _≈ᴹ_ {X} p q) (f : SgT X) (i : Int {X} p f) (j : Int {X} q f) →
    Ex {X} p f i ≃ Ex {X} q f j
  Ex-≈ e f i j = mk≃ 0# Is-0 (+-cong (+-cong (e _) (sym (e _))) refl)

  -- the coordinatewise map Yⁿ ⇒ Zⁿ and its action on tuples and on product measures
  fⁿ : ∀ {Y Z : QBS S} → Hom S Y Z → ∀ n → Hom S (ΠQ n (λ _ → Y)) (ΠQ n (λ _ → Z))
  fⁿ f zero = idH S {1Q S}
  fⁿ {Y} {Z} f (suc n) = _×H_ {Y} {ΠQ n (λ _ → Y)} {Z} {ΠQ n (λ _ → Z)} f (fⁿ f n)

  tuple-fⁿ : ∀ {Ω Y Z : QBS S} (f : Hom S Y Z) n (Xs : Fin n → Hom S Ω Y) ω →
    Setoid._≈_ (Carrier (ΠQ n (λ _ → Z))) (map (tupleQ n (λ _ → Z) (λ i → _∘H_ S f (Xs i))) ⟨$⟩ ω)
      (map (fⁿ f n) ⟨$⟩ (map (tupleQ n (λ _ → Y) Xs) ⟨$⟩ ω))
  tuple-fⁿ {Ω} {Y} {Z} f zero Xs ω = Setoid.refl (Carrier (ΠQ zero (λ _ → Z)))
  tuple-fⁿ {Ω} {Y} {Z} f (suc n) Xs ω = Setoid.refl (Carrier Z) , tuple-fⁿ f n (λ i → Xs (suc i)) ω

  mapM-prodⁿ : ∀ {Y Z : QBS S} (f : Hom S Y Z) (μ : C.Pre (XW Y)) n →
    _≈ᴹ_ {ΠQ n (λ _ → Z)} (mapM {ΠQ n (λ _ → Y)} {ΠQ n (λ _ → Z)} (fⁿ f n) (prodⁿ n (λ _ → Y) (λ _ → μ)))
      (prodⁿ n (λ _ → Z) (λ _ → mapM {Y} {Z} f μ))
  mapM-prodⁿ f μ zero h = trans (∫ᴹ-map {1Q S} {1Q S} (idH S {1Q S}) (C.ηPre {XW (1Q S)} (1# , tt)) h)
    (trans (∫ᴹ-η {1Q S} tt (_∘H_ S h (idH S {1Q S}))) (sym (∫ᴹ-η {1Q S} tt h)))
  mapM-prodⁿ {Y} {Z} f μ (suc n) = ≈ᴹ-trans {ΠQ (suc n) (λ _ → Z)}
    (map-prod {Y} {ΠQ n (λ _ → Y)} {Z} {ΠQ n (λ _ → Z)} f (fⁿ f n) μ (prodⁿ n (λ _ → Y) (λ _ → μ)))
    (prod-cong {Z} {ΠQ n (λ _ → Z)} (λ _ → refl) (mapM-prodⁿ f μ n))

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    IID : ∀ {Y : QBS S} → C.Pre (XW Y) → ∀ n → (Fin n → Hom S Ω Y) → Set₁
    IID {Y} μ n Xs = _≈ᴹ_ {ΠQ n (λ _ → Y)} (law P (tupleQ n (λ _ → Y) Xs)) (prodⁿ n (λ _ → Y) (λ _ → μ))

    IIDSeq : ∀ {Y : QBS S} → C.Pre (XW Y) → (ℕ → Hom S Ω Y) → Set₁
    IIDSeq μ Xs = ∀ n → IID μ n (λ i → Xs (toℕ i))

    -- identically distributed, and mutually independent
    IID-law : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs → IID μ n Xs → ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1# →
      ∀ i → _≈ᴹ_ {Y} (law P (Xs i)) μ
    IID-law {Y} μ n Xs d h i f = trans
      (mapM-ext {Ω} {Y} (Xs i) (_∘H_ S (projQ n (λ _ → Y) i) (tupleQ n (λ _ → Y) Xs)) (ιPre {Ω} P)
        (λ ω → Setoid.sym (Carrier Y) (proj-tuple n (λ _ → Y) Xs i ω)) f)
      (trans (sym (mapM-comp {Ω} {ΠQ n (λ _ → Y)} {Y} (tupleQ n (λ _ → Y) Xs) (projQ n (λ _ → Y) i) (ιPre {Ω} P) f))
        (trans (mapM-cong {ΠQ n (λ _ → Y)} {Y} (projQ n (λ _ → Y) i) d f)
          (margⁿ n (λ _ → Y) (λ _ → μ) (λ _ → h) i f)))

    IID-indep : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs → IID μ n Xs → ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1# →
      Indep P n (λ _ → Y) Xs
    IID-indep {Y} μ n Xs d h f = trans (d f)
      (sym (prodⁿ-cong n (λ _ → Y) (λ i → law P (Xs i)) (λ _ → μ) (λ i → IID-law μ n Xs d h i) f))

    -- functions of an iid family
    IID-map : ∀ {Y Z : QBS S} (μ : C.Pre (XW Y)) n Xs (f : Hom S Y Z) → IID μ n Xs →
      IID (mapM {Y} {Z} f μ) n (λ i → _∘H_ S f (Xs i))
    IID-map {Y} {Z} μ n Xs f d h = trans
      (mapM-ext {Ω} {ΠQ n (λ _ → Z)} (tupleQ n (λ _ → Z) (λ i → _∘H_ S f (Xs i)))
        (_∘H_ S (fⁿ f n) (tupleQ n (λ _ → Y) Xs)) (ιPre {Ω} P) (tuple-fⁿ f n Xs) h)
      (trans (sym (mapM-comp {Ω} {ΠQ n (λ _ → Y)} {ΠQ n (λ _ → Z)} (tupleQ n (λ _ → Y) Xs) (fⁿ f n) (ιPre {Ω} P) h))
        (trans (mapM-cong {ΠQ n (λ _ → Y)} {ΠQ n (λ _ → Z)} (fⁿ f n) d h) (mapM-prodⁿ f μ n h)))

    -- the observations of a signed test satisfy the moment hypotheses
    module Mom {Y : QBS S} (μ : C.Pre (XW Y)) n Xs (f : SgT Y) (m s : Sg) (d : IID μ n Xs)
      (h : ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1#) (i : Int {Y} μ f) (j : Int {Y} μ (f *T f)) (em : Ex {Y} μ f i ≃ m)
      (es : Ex {Y} μ (f *T f) j ≃ s +S m *S m) where
      E = ιPre {Ω} P
      ℓ₁ : ∀ k → Int {Y} (law P (Xs k)) f
      ℓ₁ k = Int-≈ {Y} (≈ᴹ-sym {Y} (IID-law μ n Xs d h k)) i
      ℓ₂ : ∀ k → Int {Y} (law P (Xs k)) (f *T f)
      ℓ₂ k = Int-≈ {Y} (≈ᴹ-sym {Y} (IID-law μ n Xs d h k)) j
      a : ∀ k → Int {Ω} E (f ∘T Xs k)
      a k = Int-map (Xs k) E f (ℓ₁ k)
      b : ∀ k → Int {Ω} E ((f ∘T Xs k) *T (f ∘T Xs k))
      b k = Int-via {Ω} E _ ((f *T f) ∘T Xs k) (Int-map (Xs k) E (f *T f) (ℓ₂ k)) (λ x → refl)
      exm : ∀ k → Ex {Ω} E (f ∘T Xs k) (a k) ≃ m
      exm k = ≃-trans (≃-sym (Ex-map (Xs k) E f (ℓ₁ k))) (≃-trans (Ex-≈ {Y} (IID-law μ n Xs d h k) f (ℓ₁ k) i) em)
      exs : ∀ k → Ex {Ω} E ((f ∘T Xs k) *T (f ∘T Xs k)) (b k) ≃ s +S m *S m
      exs k = ≃-trans (Ex-cong {Ω} E _ ((f *T f) ∘T Xs k) (b k) _ (λ x → refl))
        (≃-trans (≃-sym (Ex-map (Xs k) E (f *T f) (ℓ₂ k)))
          (≃-trans (Ex-≈ {Y} (IID-law μ n Xs d h k) (f *T f) (ℓ₂ k) j) es))
      ind : ∀ k l → k ≢ l → Σ (Int {Ω} E ((f ∘T Xs k) *T (f ∘T Xs l)))
        (λ q → Ex {Ω} E ((f ∘T Xs k) *T (f ∘T Xs l)) q ≃ m *S m)
      ind k l ne = Int-indep {Ω} P (Xs k) (Xs l) dd f f (a k) (a l) ,
        ≃-trans (Ex-indep {Ω} P (Xs k) (Xs l) dd f f (a k) (a l)) (*S-cong (exm k) (exm l))
        where dd = Indep-pair {Ω} P n (λ _ → Y) Xs (IID-indep μ n Xs d h) k l ne

    IID-moments : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs (f : SgT Y) (m s : Sg) → IID μ n Xs →
      ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1# → (i : Int {Y} μ f) (j : Int {Y} μ (f *T f)) → Ex {Y} μ f i ≃ m →
      Ex {Y} μ (f *T f) j ≃ s +S m *S m → Moments P n (λ k → f ∘T Xs k) m s
    IID-moments {Y} μ n Xs f m s d h i j em es = (λ k → a k , b k) , exm , exs , ind
      where open Mom μ n Xs f m s d h i j em es
