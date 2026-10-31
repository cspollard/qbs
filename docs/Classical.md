# Where the development is non-constructive

A survey of the classical assumptions in `src/QBS`, taken from the source (greps for `lem`, `lem₁`,
`lemOf`, `Dec`, `invertible?`, plus reading the modules that use them). Paths are relative to
`src/QBS/`.

## 1. How classical logic enters

Every module is `--safe --without-K`, and `make check` allows no postulates. Classical principles are
therefore never axioms. They are **module parameters**, threaded through the modules that need them.
Every theorem that depends on one is a conditional statement ("for any `lem`, …"). It cannot be
instantiated inside Agda itself.

| Parameter | Statement | Where |
|---|---|---|
| `lem` | `∀ (P : Set) → P ⊎ (P → ⊥)` | about 70 modules, mostly `Analysis/`, `Borel/PiLambda`, `Borel/Lead`, `Continuous/*` |
| `lem₁` | the same at `Set₁` | 13 modules (`Analysis/CutSum`, `CoinIntegral`, `Functional`, `Riesz`, `Model/AdditiveSemiring`, `Continuous/FairCoin`, `Uniform*`, `CoinIndep`, `FirstBit`, `SubModel`, `Example/Probability`) |
| `lemOf` | `lem₁ ⇒ lem` (by `Lift`) | `Analysis/CoinIntegral` |
| `NormalizableSemiring.invertible?` | a decision `(Σ n, m·n ≈ 1) ⊎ ¬(…)` as a record field | `Model/Semiring.agda:42`, consumed in `Model/StatInstance.agda` |
| `dec` argument to `Mask` | a decision procedure for a Borel set | `Analysis/Fun.agda` (`module Mask`) |

Not assumed anywhere: the axiom of choice (countable or dependent), propositional extensionality,
UIP, Markov's principle, or a resizing axiom. Resizing is derived from `lem₁` (§3.6) and UIP at `Set₁`
is derived from `lem₁` (§3.7).

Two points about the form of `lem`:

* **It is stated for all types, not only propositions.** Because `Σ` is proof-relevant and nothing is
  truncated, `lem (Σ A B)` returns an actual witness. Calling `lem` on a `Σ`-type is therefore an
  epsilon operator (global choice for inhabited types), and the proofs use it that way: `Clopen.choice`,
  `Borel/Lead.lead`, `Pieces.find`, `LowerReals.near-sup`, `CoinGrid.find`. This is stronger than
  classical logic for h-propositions. It is consistent with `--without-K` (set-like models) but not
  with univalence or `--cubical`.
* **Mentioning `lem` is not using it.** Many modules take `lem` only to pass it to
  `LowerRealsOmega lem` or `BM lem` (for example `LowerRealsMin`, `CoinSets`, `Continuous/ProbInstance`,
  `Continuous/Monad`). The places that call it are listed in §3.

## 2. The part with no classical hypotheses

Of 140 modules, about 50 do not mention `lem`:

* the abstract layer: `Core`, `Category`, `Limits`, `Colimits`, `Complete`, `Exponential`, `Probes`,
  `Probability`, `Statistical`, `StatisticalLemmas`, `IsQBSLike`, `IsStatisticalQBSLike`, `Instance`;
* the whole discrete model: `Model/{Semiring, Sums, Monad, Strong, ProbInstance, StatInstance, SubProb,
  WeightClasses, Cantor, Pairing, DiscreteSource, Discrete}`;
* `Borel/{Core, Source, Category, Measure, Merge, Cons}` (the Borel σ-algebra is inductive and closed
  under logical equivalence, so it needs no excluded middle);
* `Analysis/{Omega, Series, SeriesSup, Measure, Fun, Unbounded, Archimedean, ClopenMeasure, …}`;
* `Example/{Bayes, Conditioning, HardConditioning}`.

"No classical parameter" is weaker than "constructively fine". These modules take their hypotheses as
structure fields, and some of those fields cannot hold constructively (§4.1, §4.2). Examples are
`OmegaSemiring.complement` and `cancel`, `NormalizableSemiring.invertible?`, and `Mask.dec`.

## 3. Where `lem` is actually used

### 3.1 Arithmetic of `[0,∞]` as lower cuts

* `Analysis/LowerReals.agda`, `module Classical`. `near-sup` says a bounded cut has an element within ε
  of its supremum. It is proved by a double use of `lem` plus the Archimedean property. It feeds the
  `OmegaSemiring` fields `complement` (`1 − c`) and `cancel`, so `LowerRealsOmega lem` is classical.
* `Analysis/LowerInverse.agda`, `InvClassical`. The multiplicative inverse of a cut with `0 < c < ∞`
  (`near-sup′` and the boundary approximation).
* `Analysis/LowerRealsArch.agda` (`lowerRealsArch lem`). The `Arch` structure (tolerances, `arch`,
  `cancel≤`) is built on `near-sup`.
* `Analysis/Threshold.agda`. Totality of comparison with ½ (`tot-half`), and decisions `q < ½`.
* `Analysis/Pieces.agda`. Splitting `[0,∞]` into the pieces `{∞}` and `{k < w ≤ k+1}`. `lem` decides
  `q ∈ w`, `∀ k, k ∈ w`, `∃ k, k ∉ w`, and `0 ∈ w` (`find`, `piece-of`).
* `Analysis/ExtNat.agda`, `Sups`. `sup-exists`: every increasing sequence in `ℕ∞` has a supremum
  (attained, or unbounded). This is LPO-strength.

### 3.2 Deciding membership in Borel sets

The Borel σ-algebra is an inductive predicate, so membership of a point is not decidable. Many
constructions case-split on it anyway, using `lem` (or a `Dec` argument):

* `Analysis/Indicators.agda`. The indicator `χ V x` is defined by `with lem (V x)`.
* `Analysis/Fun.agda`, `Mask`. Restriction to a Borel set takes `dec` as an argument; callers such as
  `Analysis/Restrict.agda` (hard rejection) supply it from `lem`.
* `Analysis/Meas.agda` (`imp-borel`), `Analysis/LevelSets.agda` (`borel-prop`, the level sets of a
  measurable function), `Analysis/CoinFacts.agda`, `Analysis/Regular.agda` (`cov x with lem (U x)`).
* `Borel/PiLambda.agda`. Dynkin's π–λ theorem decides membership in `P`, `A`, `B` and `Fin∪ U n` in
  order to take disjoint refinements and differences.
* `Borel/Lead.agda`. `lead : Cantor → ℕ` decides `∃ m, k m = false`, which is an LPO-style decision. The
  all-`true` sequence gets a classical default of `0`. It is used for the countable Borel partition with
  infinitely many pieces.

### 3.3 Compactness of Cantor space

`Analysis/Clopen.agda`, `module Fan`. A decreasing sequence of clopens with empty intersection is
eventually empty. The proof is König's lemma, with an infinite path chosen by `lem`
(`not-all`, `bad-split`, `choice`, `choice-ok`). This is weak König's lemma / the fan theorem, which
implies LLPO. It is essential to the construction of the fair coin: `OpenMeasure`, `Regular` and
`CoinSets` rest on it.

### 3.4 The Carathéodory extension and the integral

* `Analysis/Regular.agda`. Carathéodory regularity, with the case splits above and Dynkin from §3.2.
* `Analysis/CoinCont.agda`, `CoinGrid.agda`, `CoinSimple.agda`, `MeasFun.agda`, `CoinFacts.agda`. Dyadic
  grid approximations (the largest grid point strictly below `h x`, found by `lem`), completion of a
  partial simple function to a total one (`dec x w with lem (W n x)`), and intersections of cells
  (`term i j with lem (Σ Cantor …)`).
* `Analysis/CoinIntegral.agda`, `Functional.agda`. The Lebesgue integral as a supremum over simple
  minorants. See §3.6 for the resizing it needs.
* `Analysis/Tonelli.agda`, `Lebesgue.agda`, `JSum.agda`, `JFubini.agda`, `JParam.agda`, `Density.agda`,
  `Restrict.agda`, `Uniqueness.agda`, `Param.agda`, `Tensor.agda`. These mostly inherit the above
  through `lem` parameters.

### 3.5 Normalisation and s-finite decomposition

* `Model/Semiring.agda`, `NormalizableSemiring.invertible?`. A decision "is the mass invertible?", used
  by `StatInstance.normC` and its congruence and compatibility lemmas. It is instantiated classically in
  `Model/BoolSemiring` (sums are `∃`, decided by `lem`), `Model/AdditiveSemiring` and
  `Model/ViterbiSemiring` (`case lem₁ (Σ Cut …) of …`).
* `Continuous/SFiniteNorm.agda`. `invDec` (via `inv-fin`, which proves `FinC` by `lem`). `normC`,
  `normZero` and `normScale` are defined by case analysis on it.
* `Continuous/SFiniteDecomp.agda`. Banding the weight (`find-band`, `bands-case`) and
  invertible-or-null for each piece (`pieceProb`, with `lem (Pos (pieceMass p n))`). This yields
  `scaled-laws`.

### 3.6 Resizing `Set₁` to `Set` (via `lem₁`)

* `Analysis/CutSum.agda`. The sum of a family of cuts indexed by `I : Set₁` is `Mem f q` (an inductive
  `Set₁` predicate) resized to `Set` by `dec : Set₁ → Bool`. This is `sumC`, and all the
  `CompleteSemiring` laws for `Model/AdditiveSemiring` and `ViterbiSemiring` rest on it.
* `Analysis/CoinIntegral.agda`. `Lmem h q = Σ Sf (…)` is a `Set₁`-level membership, resized to a cut.
* `lemOf` pushes `lem₁` down to `Set` (`Lift`).

This is propositional resizing in disguise. It does not use `lem₁` for its logical content, only to turn
`Set₁` predicates into `Bool`s.

### 3.7 Proof-irrelevant identity at `Set₁`

`Analysis/CutSum.agda`. `lem₁` gives `Dec (a ≡ b)` for every `a b : A : Set₁`, hence `uip`
(`Decidable⇒UIP`). This makes `(i , j) ≡ (i , j′) ⇒ j ≡ j′` hold (`ι-inj`), which `Reindex` and
`sum-Σ` need. It is a way around not having K.

### 3.8 Function extensionality (removed)

Earlier versions needed `funext`: `R = ℕ → Bool` carried propositional equality, so the isomorphism
`R ≅ R × R` (`split-merge`, `merge-evens`, `merge-odds`) was a `≡` of sequences. Now the random source carries
a setoid on `R` (`RandomSource.Rˢ`), `cantorSource` uses pointwise equality (`Borel/Source.R₁ˢ`), and those
three laws are pointwise proofs (`Continuous/Sample.agda`). Measurable functions respect pointwise-equal
points (`Borel/Core.borel-≗`; `Analysis/Fun.Fun-resp` and `Analysis/Meas.Meas-resp`, which use `lem`).

## 4. Which uses are inherent and which are artifacts

### 4.1 Inherent to the mathematics (constructively false or equivalent to a non-constructive principle)

* **`normalize : M X → Prob X + 1`.** Deciding whether a real-valued mass is invertible (positive and
  finite, versus 0 or ∞) is not constructively decidable. Any total `normalize` needs a decision principle
  at the level of WLPO or LLPO. The interface asks for it (`StatisticalInterface.normalize`,
  `normalize-zero`, `normalize-prob`), so the concrete models cannot avoid it. A constructive version
  would be partial, or conditioned on a proof that `0 < mass < ∞`.
* **`OmegaSemiring.complement` and `cancel`.** `1 − c` for a lower real `c ≤ 1` needs `c` to be located
  (equivalently, an upper cut). Lower reals in general are not located, so `LowerRealsOmega` needs
  `lem`.
* **`lead : Cantor → ℕ` and the pieces partition.** These are discontinuous total functions. A measurable
  partition by "first false" is only defined classically (or on a set of full measure).
* **Fan theorem / WKL.** Compactness of Cantor space is independent of BISH. It is a valid axiom in
  Brouwer's intuitionism and in classical mathematics, but not provable constructively.
* **`ℕ∞` suprema and `Boolean`-valued sums.** These need LPO (`Sups.sup-exists`, `BoolSemiring` `∃`).

### 4.2 Presentation artifacts (likely avoidable)

* **Indicator functions via `lem (V x)`.** The indicator of a Borel set is a perfectly good lower real
  without excluded middle: `χ_V(x) = {q | q < 0} ∪ {q | q < 1 ∧ V x}`. The classical decision is only
  needed for the complement (`1 − χ`), `Mask` and `cmask`.
* **Resizing and UIP at `Set₁`.** `sumC`'s `dec : Set₁ → Bool` and `uip` could be replaced by an
  explicit assumption of propositional resizing or an impredicative `Prop`. Alternatively, restrict the
  indexing to countable families (the `Series` module already does all the work for `ℕ`-indexed
  sums). The `Set₁` index is only needed for the discrete model's arbitrary index sets.
* **Dynkin π–λ.** The `lem` uses are case splits on membership. Dynkin has a constructive proof for
  decidable π-systems and for the cylinder algebra (Bishop–Cheng style), but it would have to be
  restructured.
* **Grid approximations, `find` and simple-function completion.** These pick the largest grid point
  below `h x` by repeated `lem`. With located reals they would be a bounded search.
* **`inv-fin` and `PosC × FinC`.** These are decisions on the shape of a cut that follow from
  `invertible?` and could be threaded as hypotheses.

## 5. Where classicality comes in, as a dependency chain

```
lem (Set), lem₁ (Set₁)
  └─ LowerReals.Classical (near-sup)          → complement, cancel → LowerRealsOmega
  └─ Clopen.Fan (König, `choice`)             → OpenMeasure → Regular (Carathéodory) → CoinSets
  └─ PiLambda (Dynkin), Indicators, Meas      → Uniqueness, Param, Tensor (Fubini)
  └─ CutSum (resizing, UIP at Set₁)           → AdditiveSemiring, ViterbiSemiring
  └─ CoinIntegral / CoinGrid / CoinSimple     → Functional → Riesz
  └─ SFiniteNorm / SFiniteDecomp (invDec)     → SFiniteStat (`normalize`, `scaled-laws`)
```

The abstract layer (`Probability`, `Statistical`, `IsQBSLike`, `Instance`) and the discrete model are
independent of the classical parameters except through the `invertible?` field of the semiring that
instantiates them.

## 6. Suggested priorities, if we want less classical logic

1. **Indicators.** Define `χ` as a lower real with no decision. This removes `lem` from many
   Borel-set case splits, though `Mask`, restriction and complements still need decisions.
2. **Resizing.** Isolate the `Set₁ → Set` step (§3.6) and the `uip` step (§3.7) behind a named
   assumption, so that `lem₁` is no longer required for their sake.
4. **Normalisation.** Replace the total `invertible?` field with a partial `normalize`, or an
   interface that takes a proof of `0 < mass < ∞`. Any `normalize` into `Prob X + 1` stays classical.
5. **Compactness and `complement`/`cancel`.** Leave these as explicit hypotheses (a `FanTheorem`
   record, and `Located` on cuts) rather than a blanket `lem`. This documents the real dependency without
   removing it.
