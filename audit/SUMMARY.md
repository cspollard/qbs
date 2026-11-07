# Audit summary (2026-11-07)

Ten reports, one per domain (see `README.md` for the brief and the module lists). Each agent did a reading audit
(headers, statements, some proofs; no Agda run), so every "duplicate" or "derivable" claim needs checking against the
proofs before acting. The spot checks below were made from the CLI on 2026-11-07.

| Report | Headline |
|---|---|
| [abstract](abstract.md) | agda-categories already used well; share `braided`/`ProbMonad`, move generic strong-monad lemmas out of `Fubini`, add bind vocabulary |
| [discrete](discrete.md) | share the classical `dec*` toolkit; split `StatInstance` (565 lines); one entry point for the three weight models |
| [lower-reals](lower-reals.md) | document the Ω → Arch/Min → Series → instances layering; shrink `RationalLemmas` wrappers; merge micro-modules |
| [measure-construction](measure-construction.md) | rename the generic `Coin*` pipeline; delete dead `Borel.Measure` record; one Dynkin-class combinator; roadmap entry |
| [analysis-real](analysis-real.md) | retire hand-written certificate packs superseded by `Deriv*`; rebase `SgLinAlg`/`ExpFamAlg` sums on stdlib |
| [continuous-core](continuous-core.md) | index the s-finite monad/product/IID results; dedupe `JoinWit`, `fixH`, `mapM-id`; generic double-strength module |
| [continuous-lebesgue](continuous-lebesgue.md) | prove "ν is Lebesgue" once and derive shift/scale/CoV; derive MCT/DCT from Fatou; rename theorem-hiding modules |
| [continuous-distributions](continuous-distributions.md) | ∫xⁿe⁻ˣ = n! proved five ways, uniform moments four ways; one density recipe; one location–scale law |
| [continuous-signed-info](continuous-signed-info.md) | merge ~20 `*Alg`/`*Aux` helpers; bundle `FinTs`; one shared `withDensity`/reweighting operation |
| [inference](inference.md) | state Bayes once at the abstract layer; named kernel composition; split the flat 60-module directory; shared prelude |

## Cross-cutting themes

1. **Findability is the biggest problem for outsiders.** Every report found headline theorems with no entry in
   `Interface.md`/`Guide.md` (π–λ, Riesz, Fubini, Fatou/DCT, change of variables, the s-finite monad, IID,
   exponential families, random vectors). Proposed fix: one "roadmap" paragraph per domain in `Interface.md`, with the
   text drafted in each report's §3. About 120 modules mention "plan N" in their comments; module headers should state
   the mathematics instead, since outsiders cannot read the plans.
2. **Theorem-hiding names.** For example `CoinIntegral`/`CoinFacts`, which are generic in any `BorelMeasure`,
   `UniquenessR`, `RQArith`, `NullInf`, `SignedTests` next to `SignedTest`, `Analysis.Measure` against
   `Probability.Measure`, and `GeometricNorm`. Each report lists its renames.
3. **The same result proved several ways.**
   - The exponential moments, by five routes.
   - The uniform moments, by four.
   - The certificate packs against the `Deriv*` calculus.
   - Two tail-FTC glues.
   - The bounded/unbounded twins `I`/`J` and `Fun`/`Meas`, where every law is stated twice.
   - Three π–λ applications with the same shape.
   - Bayes' rule, proved separately in four places.

   Keep one route each, preferably the `Deriv*`/generic one, and mark the others legacy. The analysis-real and
   distributions reports each estimate 800–1,100 lines here.
4. **Duplicated small helpers.**
   - Classical decision lemmas (`dec-true` and others) in 4 modules.
   - `negExp-cong` in 6, `two` in 7, `fixH`/`fixH₂` in 3, `mapM-id` in 2, `bd1`/`hm`/`half≤1`, and the exp
     inequalities.
   - Shared homes would help: `QBS.Classical.Decide`, one `Dyadic`/constants module, and an `Inference.Prelude` for
     the long `open` preamble repeated in about 54 modules.
5. **Helper-module sprawl.** Many `*Alg`/`*Aux`/`*Post` modules have a single parent. The project's convention is to
   split solver-heavy algebra for compile time and memory, so merge only where timings allow (time each merge, as
   with the canary rule), and prefer folding single-importer wrappers such as `CoinSets`, `Mixture`,
   `UnboundedLowerReals` and `CutSplit`.
6. **Generic constructions stated once.**
   - Density/reweighting (`withDensity`) is shared by `ExpDist`, `DensityDist`, `Entropy`, `ProdReweight` and
     `ExpFamilyPost`.
   - The location–scale/pushforward law would cover uniform, exponential rate, Gaussian, and real shift and scale.
   - The rule "Lebesgue is the unique translation-invariant measure" would give shift, scale and change of variables.
   - A generic double-strength module over any `CommutativeMonad`.

## Categorical language: consensus

- The abstract layer already uses agda-categories records (`Category`, `CartesianClosed`, `CommutativeMonad`,
  `Monad⇒-id`). There are no bespoke category, functor or monad records to replace.
- **Worth doing:**
  - A single bind/Kleisli-composition vocabulary (`bind k t = μ ∘ M k ∘ t`, or a named `_>>=ᵖ_` with `∫-bind`). It
    would shorten `Statistical*`, `Fubini` and the inference proofs. Opinions differ on importing
    `Categories.Category.Construction.Kleisli` directly: the inference agent found no current use for it.
  - A generic strong/commutative-monad lemma module (`σ-unit`, `ψ-point`, double strength).
  - A setoid `_≈ₘ_` on `Measure` for equational reasoning.
  - Documentation that names the structures: Ω is an ω-cpo with Scott-continuous + and ×; `Signed` is the Grothendieck
    ring completion, and its signed integral is the Jordan-decomposition integral; `Measure` with `dirac`/`push`/`bind`
    is the concrete model of `ProbabilityInterface` (a relative monad on kernels); `tensor₁ ≈ tensor₂` is
    commutativity of the strength; `WeightClass` is a sub-monad.
- **Not worth it:**
  - Colimits for `⨆` or the Daniell supremum (size and universe costs, plus LEM).
  - Recasting `Measure` as a `Categories.Monad`.
  - A `Semimodule` bundle for the measure cone.
  - Rewriting `Deriv` certificates categorically, which would lose the explicit constants.
  - A Markov-category Bayes statement, except possibly for dominated kernels.

## Spot checks (CLI, 2026-11-07)

These claims were confirmed by grep:
- All 12 importers of `QBS.Borel.Measure` import only `Disjoint`.
- `dec-true` is defined in `CutSum`, `CoinIntegral`, `BoolSemiring` and `ViterbiSemiring`.
- `mapM-id` is defined in `FinProdPair` and `CoinCoordsJoint`.
- `fixH`/`fixH₂` are defined in `Strong`, `SFiniteStrong` and `SFiniteCommute`.
- `negExp-cong` is defined in 6 modules and `two` in 7.
- `ProbMonad` appears only 3 times.

Everything else is unchecked.

## Suggested order

1. Documentation only, with no code risk: write the roadmap entries in `Interface.md`, rewrite the "plan N" headers,
   and fix the `fairCoin` pointer.
2. Dead code and exact duplicates: remove the `Borel.Measure` record, and share `dec*`, `fixH`, `mapM-id`,
   `negExp-cong` and `two`.
3. Retire superseded routes, after checking that each has no remaining importers: the certificate packs, the extra
   moment proofs and the tail-FTC glue.
4. Generic constructions: `withDensity`, location–scale, Lebesgue uniqueness, Bayes at the abstract layer, and
   double strength.
5. Renames and module merges, last, because they churn imports. Time each merge.

## Questions for the maintainer

Each report's §6 lists its own questions. These come up across reports:
- May modules be renamed (`Coin*`, `UniquenessR`, `RQArith`, `SignedTests`, `Analysis.Measure`) despite the import
  churn?
- Is the `Fun`/`Meas` (`I`/`J`) duality permanent, or is `Fun` scaffolding?
- Should the legacy proof routes be deleted, or kept as cross-checks?
- Should Kleisli composition come from agda-categories or be a local `bind`?
