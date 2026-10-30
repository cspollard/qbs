# Guide: using the library

Task-oriented tour. For the full list of public names see [Interface.md](Interface.md); for how the modules fit
together see [Architecture.md](Architecture.md); for one line per module see [Modules.md](Modules.md).
Code blocks that start with `-- from: path` are verbatim excerpts of that file; `scripts/doccheck.py` checks
that they are still there (run `make doccheck`).

## 0. Which model do I use?

There is one abstract interface and two concrete models of it.

| I want to… | Use | Random source | Values | Hypotheses |
|---|---|---|---|---|
| prove something for *any* probability/measure monad | `IsStatisticalQBSLike` (`QBS.IsStatisticalQBSLike`) | any `RandomSource` | abstract weights `W` | none: the monad is an argument |
| write and run small probabilistic programs (`do`-notation), discrete distributions, Bayes' rule, rejection | discrete model: `Example.Program`, `Model.*` | `ℕ` (`discreteSource`) | any complete semiring: Boolean, Viterbi, ℕ∞, additive `[0,∞]` | `lem` only for the real-valued semirings (at `Set₁` for the additive one) |
| continuous distributions (uniform, fair coin), integrals of measurable functions, soft conditioning, normalisation | continuous model: `Continuous.*`, `Analysis.*` | Cantor space `2^ℕ` | `[0,∞]` as lower cuts of ℚ | `lem` and `lem₁` (excluded middle at `Set`, `Set₁`) and `funext`; see [Classical.md](Classical.md) |

Rules of thumb:
- A theorem about *estimators and inference* should be stated generically (over `IsStatisticalQBSLike` or over a
  semiring), then instantiated. That is how `Example.Bayes` and `Example.Probability` are written, and it also keeps
  compile times down (at the concrete lower-cut semiring Agda unfolds the cuts; see Architecture.md, "Compile time").
- All values are non-negative (`[0,∞]`). There are no signed reals yet (see "Not available" below).

## 1. Write a probabilistic program and compute an expectation (discrete model)

`Example.Program` has `Programs A K ok1` (a complete semiring `A`, a weight class `K` such as `probClass A`),
giving `Prog T` (a measure on Agda values of type `T`), `pure`, `_>>=_` (so `do` works), and the expectation
`∫ p (test g)` of a function `g : T → A`. The rules `∫-pure` and `∫-bind` let you unfold it. `Flip` adds a fair coin.

```agda
-- from: src/QBS/Example/Program.agda
    both : Prog B
    both = do
      a ← flip
      b ← flip
      pure (a ∧B b)
```

```agda
-- from: src/QBS/Example/Program.agda
    ∫-flip : ∀ (g : B → ∣A∣) → ∫ flip (test g) ≈ half * g tB + half * g fB
```

A complete set-up (also a checked module, `Example.Recipes.Bernoulli`) for a Boolean coin over any complete
semiring `A` with `half + half ≈ 1`, including the weight class and the `Lift ℓ Bool` outcome type:

```agda
-- from: src/QBS/Example/Recipes.agda
  open Programs A (WC.probClass A) (λ p → p)          -- weight class: probability measures; `ok1` is the identity
```

```agda
-- from: src/QBS/Example/Recipes.agda
  flip-mean : ∫ flip (test isTrue) ≈ half
```

Notes: `flip : Prog B` is the coin itself; `isTrue` (in `Recipes`) is the indicator of `true` as a test function;
import `QBS.Model.WeightClasses` qualified, because `QBS.Analysis.Measure` also exports a `probClass` (a different one,
for the continuous model).

Workflow: `open Programs A K ok1`, `open Flip half half+half B tB fB _∧B_`, write your program, then prove its
expectation by rewriting with `∫-bind` / `∫-flip->>=` / `∫-pure` (see `∫-both`). `Example.Probability` shows the
same program with real probabilities:

```agda
-- from: src/QBS/Example/Probability.agda
  both-true : ∫ both (test isTrue) ≈ half * half
```

## 2. Condition on data

Three tools, in increasing generality:

1. **Hard rejection** (`Example.Conditioning`): `guard : Bool → Prog ⊤`, `reject`. The lost mass is the probability of
   rejection and `∫` is the unnormalised expectation. `∫-guard` computes `E[guard c >> k]`.
2. **Hard conditioning as a transformer** (`Example.HardConditioning`): `condition p c` keeps the runs where the
   observation `c` holds; `condition-split` is the law of total expectation.

   ```agda
   -- from: src/QBS/Example/HardConditioning.agda
     condition : ∀ {X : QBS (discreteSource ℓ)} → Pre X → Obs X → Pre X
   ```
3. **Soft conditioning / Bayes' rule** (`Example.Bayes`, generic in a `NormalizableSemiring`): reweight the prior by
   a likelihood `w`, then normalise by the inverse `n` of the evidence.

   ```agda
   -- from: src/QBS/Example/Bayes.agda
     bayes : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (w f : Func (QBS.Carrier X) Aˢ) (n : ∣A∣)
       (h : evidence p w * n ≈ 1#) → MP.∫ (posterior p w n h) f ≈ n * ∫ p (_·_ {X} w f)
   ```

   Abstractly, the same operations are the fields `score`, `scaleM` and `normalize` of `StatisticalInterface`
   (Interface.md, §Abstract layer).

## 3. Continuous distributions and integrals

The continuous model has the fair coin on Cantor space (`Continuous.FairCoin`), the uniform distribution on
`[0,1]`, and an integral of any measurable function.

- The whole set-up is one checked module, `Example.Recipes.UniformSetup lem₁ funext`: it fixes the value semiring `A`
  (lower cuts, via `lemOf lem₁`), the unit interval `AQ`, `∫`, `half`, and `uniform : Pre AQ`.

```agda
-- from: src/QBS/Example/Recipes.agda
  open Continuous A (lemOf lem₁) funext probClass public using (∫)
```

- `∫ p f` (`Continuous.Monad`) is the integral of a morphism `f : Hom S X AQ` (values in `[0,1]`) against `p`.
  `Hom` is a record (a function plus a proof that it preserves random elements): get morphisms from the library
  (e.g. `idH S {AQ}` from `QBS.Core`, with `S = cantorSource` explicit), not from raw functions.
- `mean` below is stated for the underlying Daniell integral `I` of the fair coin along the binary expansion, i.e. for
  the integrand `expansion`; it is what `∫ uniform (idH S {AQ})` unfolds to, but that restatement is not proved
  as a named lemma yet.
- Facts proved so far: `E[u] = ½` and the CDF, `P(u ≤ t) = t`:

```agda
-- from: src/QBS/Continuous/UniformMean.agda
  mean : I fairCoin expansion Fun-expansion ≈ half
```

```agda
-- from: src/QBS/Continuous/UniformCDF.agda
  cdf : ∀ (t : ∣A∣) → t ≤ OmegaSemiring.1# A → ∫ uniformSub (cdfTest t) ≈ t
```

- Unbounded and weighted integrals use `J` (`Analysis.Lebesgue`), which integrates any threshold-measurable
  `[0,∞]`-valued function (`Meas`). The s-finite monad `TM` (`Continuous.SFinite*`) is built on `J`; its
  statistical structure is `continuousStat` in `Continuous.SFiniteStat`
  (`open SFiniteStat lem funext`), so every result stated over `StatisticalInterface` applies to it.

## 4. Prove something generic

State your theorem over a record of the interface, then supply a model:

- `StatisticalInterface` (`QBS.Statistical`) is a record over a category with a `ProbabilityInterface`;
- the discrete instance is `discreteStatisticalQBSLike N` for a `NormalizableSemiring N` (`Model.Discrete`);
- the continuous one is `continuousStat` (`Continuous.SFiniteStat`).

Generic lemmas already available: `bind-sum` and `bind-scale` (`StatisticalLemmas`).

## 5. Not available yet

| Missing | Needed for | Plan |
|---|---|---|
| Signed values (`E[X] = ∫X⁺ − ∫X⁻`, subtraction) | variance, bias, estimators | `plans/02-uniform-integrals.md` |
| Moments beyond the mean (`E[u²]`) | variance of the uniform distribution | `plans/02-uniform-integrals.md` |
| iid products `X^n` with independence of n coordinates | sampling distributions | `plans/02-uniform-integrals.md` |
| Gaussian (exp, π, the Gaussian integral) | Gaussian inference | `plans/03-bayesian-frequentist.md` |
| Statistical models `Θ ⇒ M X`, estimators, priors/posteriors over continuous parameters | both inference styles | `plans/03-bayesian-frequentist.md` |
| Constructive foundations | removing `lem`/`funext` | `docs/ConstructiveLit.md` |
