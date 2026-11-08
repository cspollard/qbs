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

## Global cleanup status (2026-11-07)

Agent 0 (`global-cleanup`), one commit per item or group.  Every module touched was checked from the CLI with exit 0.

1. **Classical decision toolkit: done.**  New `QBS.Classical.Decide` with `module Decide (lem : LEM ℓ)` (`dec`, `dec-true`,
   `dec-false`, `from-true`, `dec-iff`) and `fromLEM₁ : LEM₁ → LEM 1`.  `BoolSemiring`, `ViterbiSemiring`, `CutSum` and
   `CoinIntegral` open it privately.  (`dec-or`/`dec-bool` stay in `BoolSemiring`: used there only.)
2. **Small helpers: partly done.**
   - Done: `negExp-cong` is now in `Analysis.NegExp` (6 copies removed: `TailFTCExp`, `TailFTCExpHalf`, `HalfLineUnit`,
     `HalfLineMomentN`, `GaussMean`, `ExpFamily`); `bd1` in `Analysis.Exp` (4 copies); `half≤1` reused from `HalfOrder`
     (`GaussExp`, `GaussInverse`, `UniformMomentN`); `hm` moved to `HalfOrder` (`TailFTC`, `UniformMomentN`).  Importers of the
     removed copies (`ExpRateInt`, `GaussHalfLine`, `HalfLineMean`, `HalfLineMoment2`, `ExpRateMoment`, `HalfLineMomentFact`,
     `HalfLineRate`, `DerivMoment`, `ExpRateOne`) now take the names from `NegExp`/`Exp`.
   - Skipped, not duplicates: `two` (the exact copies are one-liners `1# + 1#` in `DyadicAlg`, `RealShiftNull` and
     `CoinPosterior`; the others are ℚ, ℕ → ∣A∣ or `Bnd` statements; the only common home would be the `OmegaSemiring` record, which
     would rebuild the whole library); `fact` (`BetaIntegral` uses `#`, `HalfLineMomentFact` uses `natE`: different functions);
     `half≤1` in `Mixture` (it has no `Arch`, only `half` and `hh` parameters) and `hm` in `UniformMean` (generic
     `CommutativeSemiring`, no `Arch`); the exponential inequalities (the copies differ in hypothesis: `t ≤ 1#`, `t ≤ P s`,
     `hp n`; only the two `facts n` are identical, and sharing them would make `TailFTCExpHalf` import `TailFTCExp` and
     `HalfLineUnit`).
3. **Strength helpers: partly done.**  `mapM-id` now lives in `ProdMap` (copies in `FinProdPair`, `CoinCoordsJoint` removed).
   `fixH` is already one copy per codomain: `Strong.fixH` is into `AQ` and `SFiniteStrong.fixH` into `WQ`, so the statements differ;
   `SFiniteCommute` only defines the mirror `fixH₂` and imports `fixH`.  A generic-codomain `fixH` is left for `continuous-core`.
4. **Dead record: done.**  `QBS.Borel.Measure` is deleted; `Disjoint` is in `QBS.Borel.Core`; the 12 `using (Disjoint)`
   imports are removed (all opened `Borel.Core` already).
5. **Signed duplicates: wrong.**  `RandomVectorDefs.Int-mul` is an adapter taking `Int₂` pairs and passing the second components
   to `RandomVectorAlg.Int-mul`, not a re-statement.  `RandomVectorLawAux.Ex-law` is about `ιPre (mapPre h P)`, while
   `SignedTransport.Ex-map` is about `mapM h p`; they differ and linking them needs `ι-nat` and `Ex-≈`.  Both left for
   `continuous-signed-info`, which confirmed the same and left both alone (see `continuous-signed-info.md`, status).
6. **`smallprod`: done**, now in `RationalLemmas`.
