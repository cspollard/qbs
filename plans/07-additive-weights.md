# Plan 07: additive kernels, weights and soft conditioning (proposed 2026-11-10)

Goal: state `IsAdditive` (`Categories.Monad.Additive`) and `SoftConditioning` (`QBS.Statistical`) as instances of standard categorical
structure, so that proofs reuse known results and the interface says what it means: the weights form a semiring `W`,
the monad `M` is additive, and `score` is the unit of an adjunction.  The measure-theoretic layer (Bayes' rule,
evidence, normalisation, Tonelli) must not get harder.  Item numbers continue plan 05/06 (last seen: 55); the labels
below are local until the plan is scheduled.

## Literature (in `lit/`, read in part)

- Coumans, Jacobs, *Scalars, Monads, and Categories* (arXiv 1003.0585; read sections 3–5).
  - Lemmas 4–6: for a monoid `W`, the writer monad `W × –` is left adjoint to `E(T) = T(1)`.  It is the free monad on
    the multiplicative monoid.
  - Def. 16, Lemma 17: a monad on a category with finite products and coproducts is *additive* if `T(0) ≅ 1` and
    `bc : T(X+Y) → T X × T Y` is an isomorphism.  Then `T X` is a commutative monoid (`+ = T(∇) ∘ bc⁻¹`) preserved by
    `T f` and `μ`, and `Kℓ(T)` has biproducts.  Additivity is a property.
  - Lemmas 22–27: the finite-support (multiset) monad `M_S` of a commutative semiring `S` is commutative and additive,
    and `M ⊣ E : CSRng ⇄ ACMnd` with `E(T) = T(1)`, a reflection.  So monad morphisms `M_S ⇒ T` correspond to
    semiring homomorphisms `S → T(1)`; `T X` is a `T(1)`-module (Lemma 26).  Stated for `Sets`, commutative monads.
- Hyland, Plotkin, Power, *Combining effects: sum and tensor* (read the monad–theory correspondence, the tensor, and
  Theorem 12).  Theorem 12 (it "can be generalised readily to an arbitrary strong monad"): for a monoid `W` and a
  theory `L`, `T_L(W × –)` with the distributive law from the strength is the monad of `L_W ⊗ L`.  With `L` the theory
  of commutative monoids this builds `Sum(W × –)`, the free module over the monoid semiring of `W`.  The semiring
  `M_W` is a quotient of it by `(w + w′)·x = w·x + w′·x` (our inference, not stated in the paper).

## What agda-categories provides

- `CMonoidEnriched.CM-Category`: hom-sets are commutative monoids, with `+-resp-∘` and `0-resp-∘` (our laws).  Its header
  says the free commutative monoid monad (`Bag`) is very hard in type theory, so the structure is axiomatic.
- `Object.Biproduct` (Karvonen), `Theory.Lawvere` (finitary, `Nat^op` version, models in a cartesian category,
  `LT-Models`; only the trivial and identity theories are instances), `Construction.EilenbergMoore` (`Module`,
  `Module⇒`, `Free ⊣ Forgetful`, `ComparisonF`), `Monad.Morphism`.
- Missing: additive monads, semimodule monads, a theory-to-monad construction, `Bag`.

## What exists

- `Categories.Monad.Additive` [step 1, done]: `IsAdditive M` (moved from `Statistical`; the Kleisli category is enriched over
  commutative monoids, with the semiring `End X`) and `KleisliCM : IsAdditive M → CM-Category o h e`, with underlying
  category `Kleisli M` (`underlying`, by `refl`).
- `Statistical`: `SoftConditioning` with `score`, universal `score-add` (an equation in
  `K [ W × W , ⊤ ]`), universal `score-mul` (uses a strength `S : CartStrength CC M`), `score-one`, `score-zero`.
- `AdditiveModule` (experiment, uncommitted): `AdditiveObjects M` (each `M X` a commutative monoid object, `M f` and `μ`
  additive, bind additive in the continuation) is equivalent to `IsAdditive M`, both directions, with round
  trips on `⊕` and `plus`.  `bind-+` (linearity in the continuation) is a hypothesis there: it is not a module-map
  condition.  `Categories.Category.Monoidal.Opposite` supports the comonoid structure of `Symmetric.Algebra`.

## Measure-theoretic needs

| Need | Where it shows up | What the plan provides |
|---|---|---|
| linearity of `∫` in the measure and in the integrand | sums of measures; additivity of `J` (`Analysis/Lebesgue`) | the two bilinearity laws `⊕-resp-∘` are exactly these |
| weighting a prior by a likelihood, evidence | `bayes` in `Inference/CoinPosterior`, `Example/Bayes` | `scale`, `zero-bind`, `score` laws; no commutativity needed |
| products, iid, Tonelli | `Continuous/Product`, `IID` | commutativity of `M` (Tonelli); optional extra: makes `End ⊤` commutative |
| countable sums, monotone convergence | s-finite = countable sums of finite measures; `mct-conv`, `fatou` | not captured by finite additivity; stays in the concrete layer (`J`) |
| normalisation | `Normalization`, `IsNormalizedInclusion` | `Prob` is not additive; needs `score` injective (part of `M 1 ≅ W`) |
| both models | `discreteStatisticalQBSLike`, `continuousStat` | discrete: `M_S` for a semiring `S` (Lemma 23); continuous: `M(1) ≅ [0,∞]` |

## Decisions (proposed)

- **Finite, strong, not necessarily commutative.**  The interface needs a strength (for `score-mul`), not commutativity;
  Tonelli fails for non-s-finite measures, and nondeterministic effects are not commutative.  Countable additivity
  is out of scope for the abstract layer.
- **Keep the data form `IsAdditive`** as the interface: for measures `⊕` is the sum of measures, whereas
  `T(0) ≅ 1` and `bc` need a decomposition of measures on `X + Y`.  The property form is a bridge theorem (item B).
- **`SoftConditioning` is the unfolded universal property**: `score` plus laws, equivalent to a strong additive monad
  morphism `M_W ⇒ M` (reflection, Lemma 27).  `M_W` is not constructed for general `C`.
- **No single `Module`.**  Over a sum monad `S`, `Module S` gives the monoid on `M X` and linearity in the measure;
  `bind-+` is that `+_Y` is a morphism of `M`-algebras (`EilenbergMoore M`), a distributive-law condition.  Revisit only
  if `S` is constructed.
- **The ambient category is a category of monads, not of algebras.**  `EilenbergMoore S` is the algebras of one fixed
  monad: it says where each `M X` lives, but "initial" is about morphisms between monads.  The category is `AMnd(C)`:
  additive (strong) monads and monad morphisms preserving `⊕` and `𝟘`; the scalars functor `E M = End ⊤` goes to
  semirings; "`M_W` is free on `W`" is a universal-arrow statement for `E`.  A coslice under a sum monad is not the
  same category: a morphism `Sum ⇒ M` does not make `M X` additive.
- **Axiomatic, as in agda-categories.**  No free construction (`Bag`, `M_W`) and no Lawvere theory `Mat(W)`: the latter
  gives `W`-semimodule objects (`ModelsOf Mat(W) In C`) but no monad, and costs sums over `Fin n`.

## Items

- 1 `Categories.Monad.Additive` [done]: `KleisliCM`, the `CM-Category` of an `IsAdditive M`.
- 2 `AMnd(C)` [done], generic and QBS-free, mirroring `Morphism.Strong`: `Categories.Category.Instance.Monads` (monads on `C`,
  arrows `Monad⇒-id`, reusing `Monad⇒-id-id`/`-∘`); `Categories.Monad.Morphism.Additive` (`IsAdditive⇒`, `AdditiveMonad⇒`,
  identity, composition); `Categories.Category.Instance.AdditiveMonads` (the category, with `Forget` to `Monads`);
  `AdditiveMonad` (a monad with `IsAdditive`) is in `Categories.Monad.Additive`.  Plain monads, not strong: strong
  morphisms (`IsStrong`) can be a second layer when `score-mul` needs them.
- 3 `Scalars` (needs 2): the functor `E M = End ⊤` to semirings (`IsAdditive.End` exists); a morphism `σ` induces
  `σ_⊤`, which preserves Kleisli composition and `⊕`.  Then `IsFreeOn W T`, the universal-arrow statement for `E`, as
  a hypothesis record until some `T` inhabits it (the discrete weighted monad).
- A (small, no deps).  Derive the global forms from the universal laws (`score-add-global` done, `score-mul-global`
  pending: naturality of `τ`, `S.identityˡ`, `!-unique`); update the header of `Statistical` and Guide §4–5.
- B (research).  the property form of additivity (Def. 16, with `Object.Biproduct` in `Kleisli M`) ⇒ `AdditiveObjects`; check whether
  `bind-+` then follows without a hypothesis.  Not started.
- C (tidy).  Bring `AdditiveModule` to style (130 columns, 18 lines), decide whether it stays a bridge module,
  regenerate `Modules.md`; optional: `Global SW` and `IsSemiringHomomorphism` for `w ↦ score ∘ w`.
- D (instances).  Provide the strength and the universal `score-add`/`score-mul` for `continuousStat` and the discrete
  model; check `Instance` and `IsStatisticalQBSLike`.  The current working tree is partial (32 modules), so the
  instances cannot be checked until the full tree is back.
- E (optional strengthening).  `ScoreIso : score` an isomorphism `W ≅ M 1` (the counit of Lemma 27), used by
  `Normalization`; true for both models.
- F (only if needed).  Construct `Sum` or `M_W` as a monad on `QBSCat` (HPP Theorem 12), prove the universal property, and
  restate `SoftConditioning` as "a morphism out of `M_W`".

Order: 1, 2, 3; then A, C, D; E after D.  B and F are independent research items.

## Open questions

- Is `QBSCat` locally countably presentable (needed for the Lawvere-theory constructions in HPP)?  Not checked.
- Does the adjunction of Lemma 27 hold without commutativity, with `End ⊤` a possibly non-commutative semiring?
- Is `Object.Biproduct` (Karvonen) enough to state the property form for `Kleisli M` without a `CM-Category`?  Not checked.
