# Literature for a constructive version

What exists that we could build on to remove the classical assumptions listed in `Docs/Classical.md`.
PDFs are in `lit/` (index in `lit/README.md`).

**Reading status.** Only Vickers, *A monad of valuation locales*, was read in full. Everything else is
characterised from abstracts and search summaries, and the notes below say so where it matters. Treat
those entries as leads to check, not as verified claims about the papers' contents.

## Summary

* There is a well-developed constructive replacement for the measure theory we use: **valuations on
  locales** (open sets, Scott-continuous, values in the *lower reals*) with the **lower integral**.
  Vickers proves, constructively (geometric logic, no choice), a Riesz theorem, a **commutative strong
  monad** of valuations, and **Fubini**. These are the same results our `Continuous/` layer proves
  classically.
* Our `Analysis/` layer already has the same shape: lower cuts of ℚ, Daniell functionals, sums and sups
  of increasing sequences. The theory we would port to is therefore close to what we have. What changes
  is what we take as *points* and which parts we drop (σ-algebras, Carathéodory, Dynkin).
* **Cartesian closure is the obstacle.** Locales and valuation monads are not cartesian closed, and no
  known category of domains is both cartesian closed and closed under the probabilistic powerdomain (the
  Jung–Tix problem). QBS exist precisely to get higher-order functions. I found no constructive
  treatment of QBS themselves.
* The most promising routes to a fully constructive QBS development are in §4. The first is the most
  direct: keep QBS as the higher-order layer, and replace the Borel/Carathéodory/Dynkin analysis
  underneath by valuations on the Cantor locale.
* **Inherent non-constructivity stays.** `normalize` (deciding invertibility of a mass), `lead`, and
  total complements of lower reals cannot be made constructive by any choice of foundation. The
  literature tells us how to restate them (§3), not how to prove them.

## 1. Constructive integration and measure theory

### Coquand and Spitters, *Integrals and valuations* (2009), `coquand-spitters-integrals-and-valuations.pdf`
Constructive Riesz representation: for a compact regular locale, the locale of integrals on a Riesz
space is homeomorphic to the locale of (probability) valuations on its spectrum. Elementary, in
geometric theories, close to Daniell. The integrands are Dedekind-real-valued continuous functions, so
this needs compactness and finite (probability) valuations. Vickers (below) reports that their valuation
locale is the probability-valuation subspace of his.
*For us:* the "simple functions" algebra (the modular monoid) is the constructive counterpart of
`Analysis/CoinSimple` and `CoinGrid`.

### Coquand and Spitters, *Formal topology and constructive mathematics: the Gelfand and Stone–Yosida representation theorems* (2005), `coquand-spitters-gelfand-stone-yosida.pdf`
Constructive Stone–Yosida for Riesz spaces. Per the search summary, it avoids countable choice, and
dependent choice is needed only to construct *points* of the formal spectrum. Constructive content lives
at the level of formal points, not of points.

### Vickers, *A monad of valuation locales* (2011), `vickers-monad-of-valuation-locales.pdf` (read in full)
Most relevant single paper. For any locale `X`:

* `𝔙X` is the locale of valuations: `m : ΩX → [0,∞]` into the **lower reals**, with `m(⊥)=0`,
  modularity `m U + m V = m(U∪V) + m(U∩V)`, and Scott continuity (no σ-additivity).
* **Riesz theorem** (Thm 33): valuations are equivalent to linear functionals on maps `X → [0,∞]`. The
  integrals are *lower integrals*.
* `(𝔙, δ, μ)` is a **monad** (Thm 41), with `μ(M)` defined as an integral. `𝔙(1)` and `𝔙(≤1)`
  (probability and sub-probability) are commutative strong monads too (Thm 53).
* **Commutative strong monad**, product valuations, and **Fubini** (Thms 51, 52). The uniqueness of
  product valuations goes through inclusion–exclusion in the modular monoid and a cancellation lemma
  for lower reals (Lemma 48), which only needs a side condition `uᵢ ≤ y`.
* All constructions are *geometric*, so they hold in any topos and fibrewise. The paper states that
  its work conforms with the constraints of geometric logic. Predicativity is only discussed in a
  footnote, which says the status of frames is foundationally questionable in a predicative setting.
* **Limitations.** It uses lower reals and lower integrals (no subtraction, and no `1 − f`). The paper
  says it is not a true localic form of the classical theory or of the Coquand–Spitters theorem, and
  that the "upper" theory is messier. There is no σ-additivity or measurability, so it covers only
  measures determined by their values on opens.

*For us:* this is a blueprint for `Analysis/Measure`, `Tensor`, `Param` and `Continuous/Monad`,
`Strong`. Its monad is what we call `Continuous`/`SFinite`, and its Fubini replaces our `Tensor`
(which goes through π–λ and uniqueness). Our `OmegaSemiring` already works with lower reals but also
asks for `complement` and `cancel`; Vickers avoids both by proving the cancellation lemma only in the
restricted form it needs.

### Vickers, *A localic theory of lower and upper integrals* (2008)
Defines valuation locales and covaluation locales, shows Riemann and Choquet integrals can be computed
from lower and upper integrals. Constructive in the sense of geometric logic (from the abstract only;
the full text was not available to me, and Birmingham's copy returned only a stub).

### Petrakis and Zeuner, *Pre-measure spaces and pre-integration spaces in predicative Bishop–Cheng measure theory* (LMCS 2024), `petrakis-zeuner-bishop-cheng-predicative.pdf`
A predicative reformulation of Bishop–Cheng measure theory in Bishop set theory. Bishop–Cheng starts
from an integral on a class of functions and extends it Daniell-style, and is described there as highly
impredicative. They give predicative pre-measure and pre-integration spaces and a predicative
construction of the canonical L¹ as a completion. The series builds on Zeuner, *Families of sets in
constructive measure theory* (arXiv 2207.04000). Bishop–Cheng uses complemented subsets as primitive.
*For us:* this is the closest match to our *functional* (Daniell) approach, and it is about
predicativity, which is what our `Set₁ → Set` resizing hack (`lem₁`) ran into. It is a different
framework (Bishop sets rather than type theory with setoids), so porting would be real work.

### Lehner, *Measure theory via locales* (2025), `lehner-measure-theory-via-locales.pdf`
Builds measure algebras for Radon measures (including Lebesgue measure) from Grothendieck topologies
derived from valuations. Abstract only checked: it says nothing about constructivity, Cantor space or
Riesz, so it is background rather than a source for us.

## 2. Randomness, sample spaces, QBS-adjacent work

### Simpson, *Measure, randomness and sublocales* (APAL 2012)
Measures on σ-locales extend to all σ-sublocales. For the uniform measure on Cantor space there is a
canonical **locale of random sequences**: the intersection of all measure-1 opens, pointless, countably
based. Which results are constructive was **not verified** (I couldn't get the full text).
*For us:* relevant to our random source `R = 2^ℕ`: a pointless sample space is a natural home for
`lead`-style partitions, which are defined classically only on points.

### Simpson, *Probability sheaves and the Giry monad* (CALCO 2017), `simpson-probability-sheaves-giry-monad.pdf`
Probability sheaves: sheaves over probability spaces and measure-preserving maps, with the Giry monad
extended to the sheaf topos by a simple category-theoretic definition. Closest in spirit to QBS (random
elements as sheaf sections). Constructivity was not checked.

### Vákár, Kammar, Staton, *A domain theory for statistical probabilistic programming* (POPL 2019), `vakar-kammar-staton-omega-qbs-domain-theory.pdf`
ω-quasi-Borel spaces: QBS combined with ωCPOs, giving a commutative probabilistic powerdomain together
with higher-order functions (a combination not known for traditional cpo-based powerdomains). The
powerdomain is built by factorising the Lebesgue integral. Fits Fiore's axiomatic domain theory and
Kock's synthetic measure theory. Constructivity was not checked.
*For us:* a model of the combination we want (QBS + a domain-theoretic measure monad), though in
classical set theory.

### Heunen, Kammar, Staton, Yang, *A convenient category for higher-order probability theory* (LICS 2017), `hkss-quasi-borel-spaces.pdf`
Our source. Classical throughout (standard Borel spaces, Giry monad on measurable spaces). Nothing in
the search suggested a constructive treatment, and the nLab table lists the probability monad on QBS as
an open question. I found no constructive QBS paper.

### Jung and Tix, *The troublesome probabilistic powerdomain* (1998), `jung-tix-troublesome-powerdomain.pdf`
The reason valuations alone don't give a full replacement: no known cartesian-closed category of
continuous dcpos is closed under the probabilistic powerdomain. Goubault-Larrecq's QRB-domains
(countably based) are closed under it, but are not cartesian closed. A recent arXiv preprint (2608.03073)
claims a solution via finite-valuation approximable structures; **not verified**.

## 3. The principles we saw in `Classical.md`, and how the literature treats them

| Our classical assumption | Status in the literature |
|---|---|
| Fan theorem / weak König (`Clopen.Fan`) | Equivalent to compactness of Cantor space and of `[0,1]` (Veldman, `veldman-fan-theorem-axiom-kleene-alternative.pdf`); variants FAN_Δ (decidable bars), FAN_c, FAN_Π⁰₁, FAN_full separated by Kripke models. WKL is the classical analogue, and Berger and Schuster's Dini theorem is equivalent to FAN_Δ (via search summary). **Not provable in BISH.** In *locale* form, compactness of the Cantor locale is constructive (valuation/locale route). The Coquand–Spitters papers use compact regular locales as a base. |
| `lem (Σ …)` as witness extraction / epsilon | Escardó (`escardo-omniscient-sets.pdf`): searchable sets (e.g. Cantor space, with continuity assumptions) satisfy the principle of omniscience; in any variety of constructive mathematics, without fan theorem, choice or Markov. Useful for deciding `∃ x ∈ C. P x` for *decidable* P on well-behaved C, but the assumption is on the predicate, not on all of `Set`. |
| Decidable Borel membership | Replaced by *lower semicontinuity*: Vickers integrates `X → [0,∞]` where indicators of opens are fine, and complements are not available. Bishop–Cheng keeps complemented subsets as primitives. |
| `OmegaSemiring.complement`, `cancel` | Not available for lower reals. Vickers proves a restricted cancellation (`Lemma 48`) and does not use `1 − f`. Coquand–Spitters use Dedekind reals and compactness to get negation. |
| Carathéodory extension + Dynkin π–λ | Replaced by *presenting* the measure on a lattice of opens (`Thm 7`): a valuation on the frame is determined by a valuation on the generating lattice respecting covers. |
| Resizing (`Set₁ → Set`) | Predicative treatments: Petrakis–Zeuner. Vickers: footnote on arithmetic universes (Maietti–Vickers) as a predicative setting for geometric logic. |
| `normalize` (invertible?) | Not addressed: no source gives a total constructive normalisation of arbitrary measures. |
| `funext` | Removed: Cantor space carries pointwise equality (`Borel/Source.R₁ˢ`), so no function extensionality is needed. |

## 4. Routes to a constructive version

### A. Valuations on the Cantor locale, QBS on top (most direct)
Replace `Borel/` and the Carathéodory/Dynkin/Uniqueness analysis by **valuations on the Cantor locale**
(presented by the lattice of clopens with the finite-binary-tree covers; our `Clopen` already has this
lattice). Valuations, lower integral, Riesz, bind, product and Fubini are all in Vickers. Keep
`Core`, `Exponential` and the QBS layer; the random source stays `2^ℕ` as a *locale*, or as its points
with the valuation structure as extra data.
*Gains:* no `Fan`, no `PiLambda`, no `Indicators`/`Mask`, no `lem` in the lower-integral layer, and no
resizing if we index sums by ℕ.
*Cost / risk:* (a) QBS random elements are functions `R → X` of *points*, so measurability needs a
constructive replacement (e.g. "random element = continuous/valuation-preserving map from the locale");
this is the main design question and I found no precedent. (b) The lower-real theory has no `1 − f`;
our `Fun` class is defined using complements, so it would need rework. (c) Sub-probability measures are
fine (`𝔙(≤1)`), but `normalize` is not (§3).

### B. Predicative Bishop–Cheng Daniell integration
Port the Petrakis–Zeuner pre-integration spaces. Closest to our current functional style, and handles
the `Set₁` resizing issue by design. Costs: a different foundation than our type-theoretic setoids,
and the framework is not a probability monad.

### C. Keep classical, make dependencies explicit
Not literature-driven, but worth stating as the baseline: replace the blanket `lem` with named
hypotheses (`FanTheorem`, `Located`, `DecidableBorel`, `Normalisable`). This documents the dependency
without removing it, and can be done first so that later constructivisation steps are measured against
it. Suggested in `Classical.md` §6.

### D. A domain-theoretic route for higher-order
ω-QBS (Vákár–Kammar–Staton) and QRB-domains are the places to look for a probabilistic powerdomain that
coexists with higher-order functions. Both are classical as far as I checked, and constructive versions
would be research.

## 5. What I could not find

* A constructive (or predicative) treatment of quasi-Borel spaces.
* A mechanised constructive Lebesgue or Daniell integral in Agda. The Coq libraries I found (Boldo et
  al.; Affeldt–Cohen's MathComp-Analysis measure construction) are built over classical reals.
* Constructive proofs of Simpson's randomness results, Vákár–Kammar–Staton's powerdomain, or of
  Escardó's searchability without a continuity assumption: not verified.
* A reading of Coquand's inductive proofs of the fan theorem in formal topology: the search returned
  nothing, so I can't cite it here.

## 6. Suggested next steps

1. Read Coquand–Spitters *Integrals and valuations* §§1–4, and Vickers §§3–7 against our
   `Analysis/Measure`, `Tensor`, `Param` (the second is already read, the first is in `lit/`).
2. Decide the design question in route A(a): what is a "random element" when the sample space is a
   locale. Check Simpson's *Probability sheaves* and the locale-of-randoms paper for guidance.
3. Prototype a small module for a valuation on the Cantor frame of clopens and its lower integral to see
   how much of `Fun`/`Series` can be reused.
4. In parallel, do route C: it is cheap and gives a precise to-do list of what route A must discharge.

## Sources

* Coquand, Spitters. [Integrals and valuations](https://arxiv.org/abs/0808.1522).
* Coquand, Spitters. [Formal topology and constructive mathematics](https://users-cs.au.dk/spitters/expanded.html) (arXiv 0808.2705).
* Vickers. [A monad of valuation locales](https://sjvickers.github.io/Riesz.pdf);
  [A localic theory of lower and upper integrals](https://research.birmingham.ac.uk/en/publications/a-localic-theory-of-lower-and-upper-integrals/).
* Petrakis, Zeuner. [Pre-measure spaces and pre-integration spaces](https://lmcs.episciences.org/14409);
  Zeuner, [Families of sets in constructive measure theory](https://arxiv.org/pdf/2207.04000).
* Lehner. [Measure theory via locales](https://arxiv.org/abs/2510.08826).
* Simpson. [Measure, randomness and sublocales](https://doi.org/10.1016/j.apal.2011.12.014);
  [Probability sheaves and the Giry monad](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CALCO.2017.1).
* Vákár, Kammar, Staton. [A domain theory for statistical probabilistic programming](https://arxiv.org/pdf/1811.04196).
* Heunen, Kammar, Staton, Yang. [A convenient category for higher-order probability theory](https://arxiv.org/abs/1701.02547).
* Jung, Tix. [The troublesome probabilistic powerdomain](https://achimjungbham.github.io/pub/papers/Jung-Tix-1998-The-troublesome-probabilistic-powerdomain.pdf).
* Veldman. [Brouwer's Fan Theorem as an axiom and as a contrast to Kleene's Alternative](https://arxiv.org/pdf/1106.2738).
* Escardó. [Infinite sets that satisfy the principle of omniscience](https://martinescardo.github.io/papers/omniscient-journal-revised.pdf).
* [nLab: monads of probability, measures, and valuations](https://ncatlab.org/nlab/show/probability+monad).
