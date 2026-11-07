# Audit: `continuous-signed-info`

Reading audit (no Agda run). Line counts and headers are from `src/QBS/Continuous/*.agda`; modules named without the `QBS.Continuous.` prefix.

## 1. Summary

The domain builds, on the cut-valued ([0,∞] as lower cuts) integral of an s-finite measure, a *signed* integration layer and uses it for second-moment statistics and information theory in the continuous model.

- Signed layer: a signed test `SgT X` is a pair `(f⁺, f⁻) : (X ⇒ WQ)²` (`SignedTest`). `Int p f` means both `∫ f⁺` and `∫ f⁻` are finite and `Ex p f = ∫f⁺ − ∫f⁻` lives in the signed ring `Sg` (`SignedExpect`). `SignedInf` adds values in (−∞,∞], and `SignedFubini`, `SignedLimits` and `SignedTransport` give Fubini, dominated convergence and push-forward.
- Logarithm: `LogRat`/`LogCore`/`LogNeg`/`LogRecip` build log⁺ and log⁻ as cuts. `SignedLog` packages `log = log⁺ − log⁻`, and `XLog` proves x log x ≥ x − 1.
- Information: `Entropy`, `KLDiv` (Gibbs' inequality) and `InfoProduct` (additivity over products).
- Statistics: `SignedVar`; `SgMoments`/`SgSample` (unbiased sample mean and variance); `RandomVector*` (mean vector, covariance matrix, affine images).
- Exponential families: `ExpWeight`, `ExpFamily*`, `FinTest`.

Signed integration is, in fact, the standard construction (the Jordan decomposition f = f⁺ − f⁻ with both integrals finite). It is never presented as the linear extension of the positive integral, and a reader has to infer that from the code.

Top recommendations:

1. **Merge the nine Alg/Ring/Aux helper layers** (details in section 4). Roughly 25 of the 45 modules are ≤ 160-line helpers used by exactly one parent, so they could be `private`/`where` submodules or merged files. The "pointwise cross-added identity via ring solver" pattern is repeated across seven modules and should be one generic combinator.
2. **Bundle the finiteness side conditions.** `FinT` is defined in `SignedTest:80` but its closure lemmas are in a separate module `FinTest`. `Int`, `Int₂`, `FinT`, `Moments` and `RV` are each re-threaded by hand. Move `FinTest` into `SignedTest` and introduce a small `L¹`/`L²` record (or at least alias) for `Int`/`Int₂`.
3. **Fix duplicated definitions:** `Int-mul` is stated in both `RandomVectorAlg` and `RandomVectorDefs`, `comm-sums` appears in `RandomVectorAlg` and `RandomVectorRing`, and `SgSampleAlg`/`RandomVectorAlg`/`SignedVarAlg` all repeat the `via-cross`/`via-sums` transport.
4. **Share the reweighting operation.** `densPre μ p = reweightPre p μ` (`Entropy:68`) is a synonym for the operation also used in `ExpDist:48`, `DensityDist:37`, `ChangeOfVariables:124` and `ExpFamilyPostAux:62`. Provide one `_·ᴹ_` / `withDensity` with its laws (composition, congruence, product) in `SFiniteReweight`, and move `ProdReweight` and the reweight-composition lemma at `ExpFamilyPostAux:123` there.
5. **Documentation.** `SignedTests` (bounded tests, discrete-probability bridge) has a name that collides with `SignedTest`. `ExpFamily*` and `RandomVector*` have no Interface.md/Guide.md entries. Plan numbers in module headers ("plan 07, item 59") mean nothing to outsiders.

## 2. Main results

Legend: I = in Interface.md, G = Guide.md, H = module header. "Crisp" = a reader can see the mathematical statement from the header.

| Name | Location | Plain statement | Findable? |
|---|---|---|---|
| `SgT`, `_≐_` | `SignedTest` (header; `_≐_` at line 84) | signed test f⁺ − f⁻; equality by cross-adding | H, partly G. Crisp. |
| `Int`, `Ex`, `Ex-+`, `Ex-scale`, `Int-dom` | `SignedExpect:64-103` | expectation ∫f⁺ − ∫f⁻ when both finite; linear, monotone, dominated | I, G, H. Good. |
| `Ex∞`, `Sg∞` | `SignedExpect`, `SignedInf` | (−∞,∞]-valued expectation when only ∫f⁻ is finite | H only (in Guide?). Mark: not in Interface. |
| `Ex-fubini`, `Ex-⊗` | `SignedFubini` | signed Fubini; E(f⊗g) = Ef·Eg | I. OK. |
| `dct-Ex` | `SignedLimits` | signed dominated convergence | H; Interface? Check. |
| `Ex-map`, `Ex-ofITest` | `SignedTransport` | change of variables for pushforward; bridge from discrete-monad tests | I. Bridge is buried (header bullet 3). |
| `logS`, `log-mul`, `logP-ge`, `logN-le` | `SignedLog`, `LogCore`, `LogNeg` | log as a signed value; log xy = log x + log y | H. The `Log*` header lemmas are crisp but there is no Interface entry for `logS`/`log-mul`. |
| `xlog` bounds `small`, `big` | `XLog` | x + x log⁻x ≤ 1, x ≤ x log⁺x + 1 | H. Names `small`/`big` are opaque. |
| `Ent`, `ent-const` | `Entropy:68ff` | entropy of p·μ | I, G. |
| `KL`, `KL-nonneg` (Gibbs) | `KLDiv` | KL = ∫p log p dQ ≥ 0 | I, G. Best-documented result. |
| `KL-⊗`, `Ent-⊗` | `InfoProduct` | additivity over products | I, G. |
| `Var`, `Var-cen`, `Var-shift`, `Var-scale` | `SignedVar` | Var f = E f² − (E f)² | I, G. |
| `Ex-sum`, `Var-sum`, `Ex-ss` | `SgSample` | unbiased sample mean/variance | H only; no Interface entry (not seen). |
| `meanV`, `covM`, `cov-aff′`, `cov-indep`, `RV-law` | `RandomVector*` | mean vector, covariance of AX+b is A Cov Aᵀ | H only; names with primes (`cov-aff′`) are the real results and the unprimed are not obvious. |
| `expW`, `expWT`, `log-expW` | `ExpWeight` | e^{s} as weight; log∘exp = id | H only. |
| `probPre`, `partition`, `weight-sumTⁿ` | `ExpFamily` | natural exponential family, N-draw sufficiency | H only; not in Interface/Guide. |
| conjugate updating `priorPre`, `likWeight` | `ExpFamilyPost` | prior × likelihood is again conjugate | H only. |

The two headline results of the exponential-family block (conjugacy and N-draw sufficiency) are the least discoverable.

## 3. Documentation

- **Module names.**
  - `SignedTests` should be `BoundedSignedTests` (or `STest`): it is the bounded pull-back to the ring of random variables used by the discrete-style `Inference.Expectation*`, not the general `SignedTest`. Its header ("See plans/03 ...") should say so.
  - `SgSample`, `SgMoments` should read `SampleMoments*`/`UnbiasedEstimators`.
  - `XLog` should be `GibbsPointwise`.
  - `ProdReweight` belongs to the reweighting API (`SFiniteReweight`) not to `core`.
- **Interface.md** needs three new sections:

  > **Exponential families.** `ExpWeight.expW s = e^{s⁺}·e^{−s⁻}`; `ExpFamily.partition h k η T = ∫ e^{⟨η,T⟩} dh`, `probPre` its normalisation; `weight-sumTⁿ` — the weight of N i.i.d. draws is the product of weights (finite statistics). `ExpFamilyPost` — conjugate prior `priorPre (χ,ν)` times likelihood `likWeight T` is `priorPre (χ+ΣT, ν+N)`.

  > **Random vectors.** `RV n X`: square-integrable coordinates; `meanV`, `covM`; `cov-aff′`: Cov(AX+b) = A Cov(X) Aᵀ; `cov-indep`; `RV-law` for push-forward.

  > **Sample estimators.** `Moments P n F μ σ²`; `Ex-sum`, `Var-sum`, `Ex-ss`: unbiasedness.
- **Guide.md** has a section on KL but none on exponential families or random vectors; add one worked statement each (the conjugate-update equation above).
- **Plan numbers** ("plan 07, item 59; enabler for ExpFamilyKL") should be removed from headers: `ExpFamilyKL` does not exist in the domain, and every "helper for X" can be replaced by the parent link only. Proposed header for `FinTest`: "Closure of the finiteness predicate `FinT` (both parts of a signed test are finite at every point) under +, −, scaling, constants and precomposition."
- **Headers of the Ring modules** repeat "over an abstract commutative semiring, so the solver normalises small terms". Put that once in `docs/Contributing.md` (it is a library-wide idiom) and cut it from `RandomVectorRing`, `SgSampleRing`, `SignedVarRing`, `ExpFamilyAlg`, `ExpFamilyPostAlg`.
- `SignedExpect`'s header should lead with the idea "signed integration = integral of the positive part minus integral of the negative part, defined exactly when both are finite", the standard construction, so an outsider is oriented before the Route line.

## 4. Simplification

1. **Helper-module sprawl (evidence: line counts).** 20 modules are ≤ 160 lines and used by one parent: `ExpFamilyAlg` (52), `ExpFamilyAux` (154), `ExpFamilyPostAlg` (73), `ExpFamilyPostAux` (152), `ExpWeightAlg` (78), `FinTest` (46), `InfoProductAux` (52), `RandomVectorAlg` (94), `RandomVectorRing` (51), `RandomVectorSumRing` (89), `RandomVectorLawAux` (50), `RandomVectorDefs` (63), `SgSampleAlg` (52), `SgSampleRing` (92), `SignedVarAlg` (154), `SignedVarRing` (111), `SignedLimitsAlg` (90), `LogRat/LogRecip` (162/129).
   - Proposed merges:
     - `ExpFamilyAlg` + `ExpFamilyPostAlg` + `ExpWeightAlg` into one `ExpFamilyAlg` (all abstract-ring/monoid identities for exponentials, ≈ 200 lines). `ExpFamilyAux` + `ExpFamilyPostAux` + `FinTest` into `ExpFamilyAux` (≈ 350 lines; both start from `FinT` and `atSg`).
     - `SgSampleRing` + `SgSampleAlg` + `SignedVarRing` + `SignedVarAlg` + `RandomVectorRing` + `RandomVectorAlg` into `SignedAlg`. All are "polynomial identities on parts, transported by `via-cross`/`via-sums`" (`SgSampleAlg` and `RandomVectorAlg` headers say so literally). One `SignedAlg` module would define the pair-of-parts operations `_⊕ᵃ_`, `_⊗ᵃ_`, `ngᵃ` once (currently `SignedVarRing`) and the transport once.
     - `InfoProductAux` into `InfoProduct` as a `private` block; `RandomVectorLawAux` into `RandomVectorLaw`; `RandomVectorDefs` + `RandomVector` + `RandomVectorAff` into two modules (defs+main, affine).
   - Gain: about 10 fewer files, one place for solver idiom, simpler dependency graph. Cost: Modules.md/Interface.md refs, and the stated reason for splitting is compile time (records in parameterised modules; solver calls are slow). Splits that isolate `solve` calls should stay separate: keep `*Ring` modules, merge only `Alg`/`Aux` shells. Measure with the per-module timing rule before merging.
2. **`Int-mul` defined twice** (`RandomVectorDefs:51` wraps `RandomVectorAlg.Int-mul`; the header of `RandomVectorDefs` says so). Delete the wrapper and import the Alg one (or state it in `SignedExpect` where it belongs: `Int-mul` is a general fact "L² · L² ⊆ L¹", and is needed by `SgSample` through `Moments`).
3. **`comm-sums` duplicates.** `RandomVectorAlg` and `RandomVectorRing` both list `comm-sums`. Check for exact duplication; if the Alg one is a transport of the Ring one, rename (`comm-sums-pt`).
4. **Bundle finiteness.**
   - `FinT f = ∀ x → Bnd (at⁺ f x) × Bnd (at⁻ f x)` (`SignedTest:80`). The ExpFamily files carry `(∀ j → FinT (T j))` in `FinT-sumTⁿ` (`ExpFamily:234`), `weight-sumTⁿ` (`:244`) and `FinT-dotT` (`:189`); `ExpFamilyPost` has 17 and `ExpFamilyPostAux` 19 mentions. Introduce `FinTs k T = ∀ j → FinT (T j)` and lemmas `FinTs-∘`, `FinTs-sum` (the three `FinT-…` lemmas then become one, pointwise `Fin`-induction).
   - Move `FinTest` into `SignedTest` (they are one concept; `FinTest` is 46 lines and imports `SignedTest`).
   - `Int p f` (`SignedExpect:65`) and `Int₂` (`SignedVar`) are repeated: define `L2 p f = Int p (f *T f)` with `Int-mul`, and `Moments`/`RV` become records over it. The `Moments` comment says it is a Σ type for compile speed; keep the type but give projections names.
5. **Reweighting.**
   - `densPre μ p = reweightPre p μ` (`Entropy:68`) is a synonym, `ExpDist:48 expW = reweightPre negExpH lebPre`, `DensityDist:37 densW d = reweightPre d lebPre`, `ChangeOfVariables:124`, `ExpFamilyPostAux:123` (reweight composes: `reweightPre d (reweightPre e μ) ≈ᴹ reweightPre (mulH e d) μ`). All of these are the one operation "measure with density", whose laws (`∫ᴹ-reweight`, congruence `reweight-cong` in `ProdReweight`, composition, product `prod-reweight`, scaling) are scattered over `SFiniteReweight`, `ProdReweight`, `ExpFamilyPostAux`. Gather them as a single module with the name `withDensity`, and make `Entropy.densPre`, `ExpFamily.probPre` and `priorPre` reuse it. Gain: one API for distributions and information; cost: moving ProdReweight (core domain) and renaming imports.
   - Exponential tilting is just `withDensity` with density `expWT f`. `ExpFamily.probPre` should be stated as `normPre (withDensity (expWT ⟨η,T⟩) h)`, and its mass lemma as the existing `normPre` mass lemma instantiated, rather than a separate `probPre-mass` with the normaliser `n` (`Z·n ≈ 1`) threaded by hand.
6. **Signed integral as linear extension.** `SignedExpect` already proves linearity piecewise (`Ex-+`, `Ex-neg`, `Ex-scale`, each with a cross-added witness). That is the content of "integral on the vector space of integrable differences of positive functions". The cost of presenting this as `Ex : L¹ → Sg` with `L¹` a quotient is large here (setoid-of-pairs, `≐` transitive only through pointwise-finite middles, as `SignedTest` notes). Recommendation: keep ad hoc but state in the header that it is the Jordan-decomposition integral, and note `Ex-irr` is "well-definedness".
7. **Dead hypotheses to check.** `KL-nonneg` requires both `∫ 1 ≈ 1` and `∫ p ≈ 1` (Guide:198); the first could be stated through an `IsProb` bundle used also in `InfoProduct` (`∫ pᵢ dQᵢ ≈ 1`). `Ex∞-+` requires neither a witness. Cannot confirm unused hypotheses without reading proofs; flag for the maintainer.
8. **`SignedSq` and `SignedMul`.** `sq-cong` is a special case of `mul-cong` (`SignedMul` header: "the twin of `SignedSq`"). `SignedSq` (119 lines) should be derived as `sq-cong f g e = mul-cong e e` and deleted if `SignedVar` can import `SignedMul` instead (the only reason to keep it is compile time of the 8-case `mul-alg`). Gain: one fewer 119-line proof. Risk: `SignedMul` is heavier for `SignedVar`.
9. **Log modules.** `LogRat` (162), `LogCore` (279), `LogNeg` (154), `LogRecip` (129), `SignedLog` (149) all concern the single function log on cuts. `LogRecip` (`recC`) is the reciprocal `1/w` that also appears as `NegExp` in `analysis-real`; `recC (expC x) = negExp x` is stated in its header as definitional. Move `recC` and `recC-mul` into `Analysis.NegExp` (it already contains the `near-max`/`reach` it borrows) to remove `near-maxG` as a parametrised copy of `NegExp.near-max`.
10. **Local naming.** Primed-name families (`Var-sumV′`, `Int₂-sumV′`, `mean-aff′`, `cov-aff′`, `RV-aff′` in `RandomVectorAff`; `RandomVector` has the unprimed versions) read as drafts. Pick one set, re-export under the clean name.

## 5. Categorical language

- **Measure with density as an endofunctor action.** `reweightPre` is the action of the commutative monoid `(X ⇒ WQ, ·, 1)` on `Pre (XW X)` (right action: `reweight d (reweight e μ) = reweight (e·d) μ`). Stating it as `Action` of a monoid (agda-categories has `Categories.Category.Monoidal.*` actions but nothing as light as needed) is not worth it: the three laws are all that is used. Keep bespoke.
- **Signed expectation as a natural transformation.** `Ex-map` (`SignedTransport`) is naturality of `Ex` along `mapM h`. `Int-map`/`Int-unmap` and `RandomVectorLawAux.Int-law` (also `∫-law`, `Ex-law`) restate it: `Ex-law` is literally `Ex-map` for `ιPre ∘ mapPre`. Delete the Law version and import `SignedTransport`; the header of `RandomVectorLawAux` already admits it duplicates `GaussVarAux.∫-map`. This is the most valuable categorical simplification here.
- **Product of densities.** `prod-reweight` is "reweight is monoidal for ⊗": the lax-monoidal structure of the density action. Worth stating in `Product` only if the Kleisli ⊗ is already there; not necessary.
- **KL/Entropy as Kleisli.** KL of p·Q relative to Q is the expectation of a log-likelihood ratio, a functorial quantity only after disintegration (listed out-of-reach in Guide:223).
- **Reasoning combinators.** Proofs of `Var-cen`, `ExBil` use `≈⟨_⟩`-chains by hand over `Sg`. `Sg`'s ring structure (`Bounded.signedRing`) is a `CommutativeRing`, so agda-stdlib's `Algebra.Solver.Ring` is correct; the repeated "parts of signed operations are polynomials in the parts" argument is the construction `Sg = Grothendieck group of the semiring of bounded cuts`. That could be one generic lemma: *for an additive-inverse completion, a ring identity on completions holds iff its cross-added form holds on the semiring* (the transport `via-cross`). If `Analysis.Signed` already provides this, delete the copies in `SgSampleAlg`/`RandomVectorAlg`/`SignedVarAlg`.
- Bespoke is the better choice for: `Sg∞` (a partial group completion; no categorical form), and `FinT`/`Int` predicates (plain Σ-types).

## 6. Open questions

1. Are the `*Alg`/`*Ring` splits still needed for compile time, or were they first-draft shapes? A per-module timing table would settle which can be merged.
2. Is `ExpFamilyKL` (promised in `ExpFamily`'s header) still planned? If not, drop the mention; if so, `ExpFamilyPost`'s `FinT` hypotheses on `A-stat` should be designed with it.
3. Should `Int p f` be a record with fields `fin⁺`, `fin⁻` (named projections, better error messages) given the compile-time note?
4. May `SignedSq` be removed in favour of `SignedMul`, and `RandomVectorLawAux` in favour of `SignedTransport.Ex-map`?
5. Does anything outside the domain need `Entropy.densPre` by that name (so a rename to `withDensity` is cheap)?
6. `SignedTests` vs `SignedTest`: rename now, before more `Inference.*` modules import it?
