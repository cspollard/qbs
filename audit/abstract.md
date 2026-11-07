# Audit: `abstract` domain (20 modules, 2137 lines)

## 1. Summary

The abstract layer builds the category of quasi-Borel spaces over an abstract random source, then states the
probability and statistical interfaces over *any* cartesian closed category.

- **Concrete half (`Core`, `Category*`, `Exponential`, `Limits`, `Colimits`, `Complete`, `Probes`, `BoolQ`).**
  - A QBS is a setoid with probes, and a `Hom` is a probe-preserving setoid map.
  - `QBSCat S` is an agda-categories `Category`, and it carries `CartesianClosed`, `FinitelyComplete`, `Cocartesian`,
    `Complete` and `Cocomplete` structures.
  - `Forget` is faithful, with the adjoint triple Disc ⊣ Forget ⊣ Codisc, and the Yoneda embedding of the
    measurable-map site is full and faithful.
- **Abstract half (`Probability`, `Statistical`, `IsQBSLike`, `IsStatisticalQBSLike`, `Instance`, `IntegralMonad`).**
  - `ProbabilityInterface` is a `CommutativeMonad` on a cartesian closed `C`, plus laws of probes, plus Fubini.
  - `StatisticalInterface` adds weights, a measure monad containing Prob via `Monad⇒-id`, `score`, countable sums and
    normalisation.

The library already uses agda-categories heavily and in the right places. There are no bespoke category, functor or
monad records, and the reasoning combinators are used. The main costs are:

- the braided-structure boilerplate is repeated;
- generic strong-monad facts are buried inside `Fubini`;
- the doc entry points for the abstract layer are thin;
- bind is spelled out as `μ ∘ M k ∘ t` throughout.

Top recommendations:

1. Use `ProbMonad` (already defined, used once) everywhere `CommutativeMonad braided` is spelled out, and share one
   `braided` definition between `Probability`, `Statistical` and `Category.Cartesian`. This is a small, safe gain.
2. Move the strong-monad point lemmas (`σ-unit`, `τ-unit`, `σ-point`, `τ-point`, `ψ`, `ψ-point`) out of `Fubini` into
   a generic module. They do not mention ℛ or Measure.
3. Introduce a Kleisli/bind vocabulary (`bind k t = μ ∘ M k ∘ t`) as a local abbreviation, or use
   `Categories.Category.Construction.Kleisli`, to shorten `Statistical*` and the `Fubini` proofs.
4. Add a short "Abstract layer overview" to `Interface.md` or `Guide.md` that explains the `IsQBSLike` stack.
   `Instance`, `IsQBSLike` and `Core` need better headers.
5. State plainly in the docs that `Statistical`'s local `CommutativeMonoidWithZero` is the right choice, and add the
   one-line reason. Consider whether `sum-nat` and `sum-join` are derivable from `bind-sumK`.

## 2. Main results

| Name (file:line) | Plain statement | Mathematical statement | Findable and documented? |
|---|---|---|---|
| `QBS` / `Hom` (`Core.agda:135`, `:194`) | A QBS is a setoid with probes satisfying the sheaf condition. A hom preserves probes. | An 𝕄-sheaf on the measurable-map site (module header says so). | Header is good. Interface.md covers it. |
| `QBSCat` (`Category.agda`) | The category of QBS and homs. | A `Category` with homs equal when pointwise equal. | Yes. Header is one line and fine. |
| `cartesianClosed` (`Exponential.agda:114`) | QBSCat is cartesian closed. | The exponential `Y^X` has as random elements the maps R → Y^X that uncurry to a probe. | Yes (header). Interface.md lists it. |
| `finitelyComplete` (`Limits.agda:124`) | Finite limits. | Terminal, products and equalizers. | Yes. |
| `cocartesian` (`Colimits.agda:134`) and `finitelyCocomplete` (`:197`) | Finite colimits. | Initial, coproducts and coequalizers. | Yes. |
| `complete`, `cocomplete`, `countableProduct`, `countableCoproduct` (`Complete.agda:147`–`:164`) | All small limits and colimits. | Via `AllProducts×Equalizer⇒Complete`. | Yes. |
| `Forget`, `Forget-faithful` (`Category/Forget.agda`) | The forgetful functor is faithful. | QBSCat is concrete over Setoids. | Yes. |
| `Disc ⊣ Forget ⊣ Codisc`, `Forget-continuous`, `Forget-cocontinuous` (`Category/Concrete.agda:118`–`:179`) | Forget preserves all limits and colimits. | By adjoints on both sides (`rapl′`, `lapc′`). | Header is excellent. Not clearly signposted in Interface.md. |
| `yoneda`, `yoneda-full`, `yoneda-faithful` (`Category/Measurable.agda:37`–`:50`) | The measurable-map site embeds fully faithfully. | Ties to the "sheaf" slogan. | Yes (header). |
| `ProbabilityInterface` (`Probability.agda:261`) | The abstract probability monad. | A commutative strong monad T on a cartesian closed C with an object ℛ, measures on ℛ, law-surjectivity and Fubini over ℛ ≅ ℛ × ℛ. | Header and Interface.md are good. |
| `law-join` (`Probability.agda:246`) | Bind is Fubini. | μ ∘ T(kernel γ ν) ∘ law μ = law (γ ∘ split) (μ⊗ν). | Listed in Interface.md as derived. Statement is crisp. |
| `StatisticalInterface` (`Statistical.agda:203`) | Abstract soft conditioning. | A weights monoid W, measure monad M ⊇ Prob, `score : W ⇒ M 1`, countable sums, every measure a sum of scaled laws, and normalisation M X ⇒ Prob X + 1. | Header is good. Interface.md lists the five structures. |
| `scale-one`, `scale-mul`, `scale-nat`, `scale-join` (`Statistical.agda`, in `Score`) | `scaleM` is an action of the weights, natural and join-compatible. | `scaleM a t = μ ∘ M t ∘ score ∘ a`. | Listed. |
| `bind-sum`, `bind-scale` (`StatisticalLemmas`) | Bind is linear in the measure. | Follows from `sum-nat` plus `sum-join`, and from `scale-nat` plus `scale-join`. | Listed in one line. |
| `IsQBSLike`, `IsStatisticalQBSLike`, `isQBSLike`, `isStatisticalQBSLike` (`IsQBSLike.agda`, `Instance.agda`) | The packaged "this category supports Bayesian programming" structure, and the instance for QBSCat. | Cartesian closure, ℕ-indexed (co)products, binary coproducts and a `ProbabilityInterface`. | Interface.md has two lines, but no explanation of why this bundle. |
| `IntegralMonad` (`TM`, `strongMonad`, `IntegralMonad.agda:128`, `:219`) | A monad on QBS is determined by its integrals. | T X embeds in the continuation monad (X→V)→V, and the laws are transported. | Header is excellent (Kock, Ścibior). |
| `BoolQ`, `ifQ` (`BoolQ.agda`) | Boolean QBS with measurable case analysis. | 1 + 1 as a coproduct. | Header is good. |

Nothing important is hard to find. The weak spots are the `IsQBSLike` stack and `Core`'s proof-heavy tail (see §3).

## 3. Documentation

1. **`IsQBSLike.agda` header.** It says "minimal structure for probability the QBS way". It does not say who
   instantiates it, that it is the *only* place the discrete and continuous models are assembled into the form the
   examples consume, or that `ℛ` appears in the record only through the `ProbabilityInterface`. Proposed replacement:
   > `IsQBSLike ℓ C`: what a category `C` must provide for QBS-style probabilistic programming — cartesian closure
   > (higher-order programs), binary and ℕ-indexed coproducts (branching, discrete data), ℕ-indexed products (infinite
   > families), a probe object ℛ, and a `ProbabilityInterface` on ℛ (a commutative strong monad of laws).  `QBSCat S` is
   > the intended instance (`QBS.Instance`) given a monad as hypothesis; `Model.ProbInstance` (discrete) and
   > `Continuous.ProbInstance` supply the monads.

2. **`Instance.agda` header.** The phrase "given the probability monad as a hypothesis" is accurate but unexplained.
   Add: "Every random source gives the category structure for free; the monad is the only modelling input. Consumers:
   `Model.ProbInstance`, `Model.StatInstance`, `Continuous.ProbInstance`, `Continuous.SFiniteStat`."

3. **`Core.agda` header.** The sheaf-on-a-site story is excellent, but the first sentence of the header should state,
   for non-experts, the elementary definition. Suggested opening line:
   > A QBS is a setoid X together with a set of "random elements" ℛ → X, closed under precomposition with measurable
   > maps, constants, and countable measurable case splits.
   The existing paragraph then explains why this is a sheaf.

4. **`Interface.md`: add a short "Abstract layer map" paragraph** before `QBS.Probability`. It should show the
   dependency stack in one block:
   `Core → Category → {Exponential, Limits, Colimits, Complete} → Probability → Statistical → IsQBSLike →
   IsStatisticalQBSLike → Instance`.
   Say that the abstract interfaces are stated over an arbitrary category `C`, and that `QBSCat` is just the primary
   instance. Today Interface.md lists modules but never says that `Probability` and `Statistical` do not mention QBS.

5. **`Statistical.agda` header.** The module comment is good. Add that `W`'s `zero⇒` is an absorbing element, not a
   zero object (this is already said at the record, but it is also easy to misread from the header). Also add a
   sentence saying that `scaled-laws` is the only field outside the five sub-records, which is where s-finiteness
   lives. Interface.md already says this.

6. **`StatisticalLemmas`.** The name is vague. Since `bind-sum` and `bind-scale` are the whole content, either rename to
   `BindLinearity` (low-churn rename; see §6) or merge into `Statistical` as a `module BindLinear` at the end. It has 42
   lines and 4 importers.

7. **`Category/Cartesian.agda`.** The header is good. It should add an `open import` hint: "import this module as
   `module CC = QBS.Category.Cartesian S`". It currently relies on `{-# INLINE #-}` pragmas whose purpose is not
   explained. Add one line: "INLINE keeps the cartesian-structure projections reducing during type-checking of the
   models".

8. **`Probability.agda`.** The ψ, σ, τ block in `Fubini` is about 100 lines of generic strong-monad calculation with no
   pointer saying that it is generic. Add a comment: "the next five lemmas hold for any commutative monad on a cartesian
   category; they do not use ℛ or Measure" (and see §4.2).

## 4. Simplification

1. **Repeated braided-structure plumbing.**
   - Evidence: `Probability.agda:41` (`braided = Symmetric.braided (CSM.symmetric C cartesian)`), `Statistical.agda:58`
     and `Category/Cartesian.agda:20` define the same braided monoidal structure. `Probability.agda:25`–`26` already
     defines `ProbMonad CC = CommutativeMonad braided`, but it is used only at `Continuous/ProbInstance.agda:81`.
     Meanwhile `ProbLaws`, `Fubini`, `ProbabilityInterface` and `SubMonad` all spell out `CommutativeMonad braided`.
   - Proposal: export `braidedOf CC` (the `Symmetric.braided …` expression) from `Probability` and use `ProbMonad CC`
     for every field and parameter of that type. `Statistical` and `Category.Cartesian` would import `braidedOf`.
   - Gain: about ten lines less, and one name for the notion.
   - Risk: low. Changes are definitional unfoldings, but check that `ProbMonad CC` unfolds to the same neutral term. It
     may need `{-# INLINE #-}` or an `abstract`-free definition for the inference of implicit `braided` arguments.
     Interface churn is zero because it is all internal.

2. **Generic strong-monad lemmas are inside `Fubini`.**
   - Evidence: `Probability.agda:110` (`ψ`), `σ-unit`/`τ-unit`/`σ-point`/`τ-point`/`ψ-point` (about `:116`–`:215`,
     roughly 100 lines, each used once in this file). They talk about arbitrary global elements `⊤ ⇒ T A` and not about
     ℛ or `Measure`.
   - Proposal: move them into `QBS.StrongPoint` (or `QBS.Probability.StrongPoint`), parametrised by a
     `CommutativeMonad braided`. `Fubini` would then just `open` them.
   - Gain: `Fubini` becomes readable (the axiom, `kernel`, `kernel-law`, `law-join`); the lemmas become reusable by the
     models that currently re-derive strength at points (`Model.Strong`, `Continuous.Strong`,
     `Continuous.SFiniteCommute`; I did not read their proofs, so this is a hypothesis to check by grep for
     `σ-point`-like statements).
   - Risk: compile time is neutral. Module parameters would need to carry `C`, `CC`, `cm` explicitly.
   - Also worth checking: whether agda-categories has `Monad.Strong.Properties` statements that already give
     `σ-unit`/`τ-unit` in a general form (`Categories/Monad/Strong/Properties.agda` exists). I did not verify the exact
     match.

3. **Bind is spelled as `μ ∘ M k ∘ t` throughout.**
   - Evidence: `Statistical.agda` `scaleM` (line 86 `M.μ.η X ∘ M.F.F₁ t ∘ score ∘ a`), `bind-sumK` (`:170`), the
     `StatisticalLemmas` statements, and `Probability.agda` `join-kernel` and `law-join`. The bind-reasoning in
     `scale-mul` (about 25 lines of chained `pullˡ (⟺ M.F.homomorphism)`) is exactly the associativity of Kleisli
     composition.
   - Proposal: define `bindK : (X ⇒ M Y) → (⊤ ⇒ M X) → (⊤ ⇒ M Y)` once, with `bind-assoc`, `bind-η`, `bind-natural`,
     and restate `scaleM` as `bindK (score ∘ a) …`. Or use `Categories.Category.Construction.Kleisli` (exists in
     agda-categories) so that Kleisli composition is `_∘_` and associativity is `Kleisli.assoc`.
   - Gain: `scale-mul`, `scale-join`, `scale-nat` and `bind-scale` shrink to one or two steps; the Fubini proofs read as
     Kleisli identities.
   - Risk: the Kleisli category is built from a `Monad` and brings its own `_≈_` setoid. Statements about global
     elements `⊤ ⇒ M X` become Kleisli maps `⊤ ⇒ X`, which is exactly what you want (global measures are Kleisli
     points). Cost is moderate: a one-off wrapper module plus restating about ten lemmas. I would try it on `scale-mul`
     first.

   Note that this is only worthwhile if the models also use the lemmas; a local `bindK` abbreviation is enough if they
   do not.

4. **`CountableSums`: derivability.**
   - Evidence: `Statistical.agda:168`–`:174`. `sum-nat` (`M f ∘ sumK ts ≈ sumK (M f ∘ ts n)`) and `sum-join`
     (`μ ∘ sumK ts ≈ sumK (μ ∘ ts n)`) are both instances of `bind-sumK` once bind is written as `μ ∘ M k ∘ t`, with the
     kernel varying over `ts n : ⊤ ⇒ M X` and the measure fixed. They are the "linear in the measure" direction while
     `bind-sumK` is the "linear in the kernel" direction. They are two separate axioms and are *not* mutually derivable
     without a unit measure.
   - Proposal: no change to the axioms, but state in the record comment which direction each one covers: "`bind-sumK`:
     linear in the kernel; `sum-nat`/`sum-join`: linear in the measure". This is a documentation fix, not a
     simplification, so I would not remove any field.

5. **`law-surjective` returns a Σ of three components.** `Probability.agda:60`. It is used only through `scaled-laws`
   and the models. Fine as is. Low-value to change.

6. **`IsStatisticalQBSLike` wrapper.** It adds only `base` and `statistical` (20 lines). It can stay.
   `IsQBSLike.countableProducts`/`countableCoproducts` are used only through `Instance`; fine.

7. **Equality proofs in `QBSCat`.** `Category.agda` builds `equiv` and the unit laws by hand with
   `Setoid.refl (Carrier _)`. That is already minimal; the record could use `Setoid.isEquivalence`-style helpers but the
   gain is about 3 lines. Not worth it.

8. **Unused parameters.** `ProbabilityInterface` takes `ℓ` as an explicit parameter because `Measure : Set ℓ`. `ℛ`
   appears in `StatisticalInterface`'s type but `Score`/`CountableSums`/`Normalization` carry `{ℛ} {CC} {P}` implicit
   arguments only to name `SM`. These are noise in the signatures, but fixing it means making `SubMonad` independent of
   `P` (it needs P only for `inclusion`). I would not touch it; the repeated implicit telescope is the main readability
   cost of `Statistical` and could be reduced with a `module _` parameter block, which is purely cosmetic (cost: 20
   lines of edits).

## 5. Categorical language

Already categorical (keep as is):

- `QBSCat : Category` (`Category.agda`); `Forget : Functor` with `Faithful` (`Category/Forget.agda`).
- `CartesianClosed` in the canonical presentation (`Exponential.agda:114`), `Cartesian`, `Cocartesian`,
  `FinitelyComplete`, `Complete` through `AllProducts×Equalizer⇒Complete` (`Complete.agda:147`).
- The adjoint triple and (co)continuity via `rapl′` and `lapc′` (`Category/Concrete.agda`).
- `ProbabilityInterface.commutativeMonad : CommutativeMonad braided` (`Probability.agda`), `StrongMonad`, `Strength`,
  `RightStrength` and `Monad⇒-id` for the sub-monad inclusion (`Statistical.agda:68`).
- `HomReasoning` and `Categories.Morphism.Reasoning` (`MR`) in the proofs (`pullˡ`, `cancelˡ`, `extendʳ`, `introˡ`,
  `elimˡ`).

Candidates, in order of value:

1. **Kleisli category for bind** (see §4.3). Current: `μ ∘ M k ∘ t` everywhere. Categorical: `Kleisli M` from
   `Categories.Category.Construction.Kleisli`. Worth doing in a trial form on `Score`, because `scale-mul` is literally
   associativity of Kleisli composition. Costs: a new wrapper module, and a possible slowdown from unfolding the Kleisli
   `_∘_` (`μ ∘ M g ∘ f`); global elements in `Kleisli` are maps `⊤ ⇒ X`, a nice reading.

2. **Double strength / monoidal monad.** `ψ` (`Probability.agda:110`) is Kock's double strength, the lax monoidal
   structure of a commutative monad. I found no ready-made definition in `Categories/Monad/` (only `Commutative.agda`
   and `Strong.agda`), and `ψ` is defined by hand through `μ`, `σ` and `τ`. Keep the bespoke definition; but it should
   be exported with a name (`CommutativeMonad.ψ` or `doubleStrength`) in the generic module of §4.2 so that the models
   can use it. Fixing the statement `measure-tensor : T split.from ∘ measure (tensor μ ν) ≈ ψ ∘ ⟨measure μ , measure ν⟩`
   is already as categorical as it gets: it says `measure` is a lax-monoidal map from measures to global elements of T.

3. **`CommutativeMonoidWithZero` as a monoid object.** `Statistical.agda:38`. agda-categories has
   `Categories.Object.Monoid` (the record comment already says it has no commutativity field and no absorbing zero). The
   bespoke version is the better choice: its laws are stated at generalised elements `Z ⇒ W`, which is what the proofs
   consume, and a monoid object in a cartesian monoidal category needs `V.⊗` unfolding. Keep. Optionally restate it as
   "a commutative monoid object together with an absorbing zero" in the header.

4. **Sub-monad as monad morphism.** Already `Monad⇒-id` (`Statistical.agda:68`). `inclusion-strong` is the
   strength-compatibility condition for a *strong* monad morphism. agda-categories has no `StrongMonad⇒`, so the
   bespoke field is right. If agda-categories adds one, switch.

5. **Probability and measure monads as one construction.** `ProbabilityInterface` and `SubMonad` both carry a
   `CommutativeMonad`. `SubMonad` is "a commutative monad `M` and a strong monad morphism `Prob ⇒ M`". It could be
   factored as `SubMonad = Σ M . (StrongMonad⇒ Prob M)` if a strong monad morphism record existed; today this is the
   right local choice.

6. **Normalisation as a natural transformation.** `Normalization.normalize : ∀ X → M X ⇒ Prob X + 1`
   (`Statistical.agda:190`) is stated pointwise, without naturality. It is natural in X in the models (probably);
   stating it as a `NaturalTransformation M (Prob + 1)` would add a naturality proof obligation to every model, so the
   pointwise form is the better choice unless a consumer needs naturality. Question for the maintainer (§6).

7. **Concrete category language.** `Category/Concrete.agda` shows equivalence with `SubCategory` rather than defining
   QBS as one, for compile-time reasons (header explains). This is the right call.

8. **`IntegralMonad` and the continuation monad.** The header says no library has the continuation monad on setoids,
   so the record is local. Correct; agda-categories has `Categories.Monad.Construction.Kleisli`/`Adjoint` pieces only.
   Keep.

9. **ℛ as a "probe object".** `IsQBSLike.ℛ` is a plain `Obj`. In QBSCat it is `ℛQ`, the representable presheaf.
   `Category.Measurable.yoneda` already gives the functor. Nothing to add.

## 6. Open questions

1. Are `Model.Strong`, `Continuous.Strong` and `Continuous.SFiniteCommute` re-proving any of `σ-point`, `τ-point` or
   `ψ-point`? If yes, §4.2 pays for itself immediately; if no, it is only a readability change.
2. Would you accept renaming `StatisticalLemmas` to `BindLinearity` (4 importers), or merging it into `Statistical`?
3. Is `normalize` natural in X in all models? If so, a `NaturalTransformation` form might be wanted for the interface.
4. Do you want `ProbMonad CC` to become the canonical way to say "commutative monad on a cartesian closed category" in
   `Probability`, `Statistical` and `IsQBSLike`? It would shorten about ten signatures.
5. Is the Kleisli trial (§4.3) worth a branch? It is the only simplification with real proof-length savings.
6. `Probability.agda` and `Statistical.agda` import many agda-categories modules. Are they compile-time-sensitive? If
   so, the INLINE pragma approach in `Category.Cartesian` should be extended to `braidedOf`.

Note: the agent did not read `Core.agda` proofs, `Limits`, `Colimits`, `Complete` or `Exponential` bodies, and did not
check proofs inside `IntegralMonad` beyond the header and top-level records. Findings on those are from headers and
signatures only.
