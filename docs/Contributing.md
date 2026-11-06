# Contributing

How code in this library is written, checked and documented.  Read [Architecture.md](Architecture.md) first for the
layers and what is slow to compile; [Guide.md](Guide.md) shows the library in use, [Interface.md](Interface.md) lists
the public names and [Modules.md](Modules.md) has one line per module.  The last section is for LLM agents.

## Philosophy

- **Safe and honest.**  Every file is `{-# OPTIONS --safe --without-K #-}` with no postulates.  Classical principles
  are explicit module parameters (`lem`, `lem₁`), used only where needed; [Classical.md](Classical.md) says where
  and why.  A statement that needs a hypothesis takes it as an argument.
- **General theorems.**  State the general result, not the instance you need today: any probability measure rather
  than the uniform one, any iid family rather than coin draws, any commutative ring rather than `Sg`.  Instances
  come afterwards as corollaries.  When a general statement is out of reach, say so in the plan, with the reason,
  rather than quietly specialising.
- **Generic first, instantiate last.**  Algebra is proved over an abstract (semi)ring with the ring solver
  (`*Ring`, `*Alg` modules) and bridged to the concrete lower cuts by short lemmas, often `refl`.  At the concrete
  cut semiring Agda unfolds the cuts and check times explode (`SignedVarAlg` went from 82 s to 9.6 s this way;
  [Architecture.md](Architecture.md), "Compile time").
- **True at the edges.**  Values are lower reals in [0, ∞]; signed values are pairs of them.  Statements must hold at
  ∞ and with 0 · ∞ = 0.  Cross-added equalities such as `_≐_` are not transitive once ∞ appears ((1, 0) ≐ (∞, ∞) ≐
  (2, 0)) and do not transfer integrability.  Check a new statement against these cases before proving it.
- **Small pieces.**  Small modules, short declarations, named lemmas.  A long proof is a missing lemma.
- **Compile time is part of the design.**  Recent modules check in 3–30 s and under 2 GB each.  If a module is
  slower, restructure it rather than accept it.
- **Documentation is part of the code.**  Every module has a header comment that states what it proves and how;
  `make doccheck` keeps the docs in step with the code.
- **Plan larger work.**  Multi-module work starts as a plan in [plans/](../plans/) (see "Plans" below).

## Where things go

The areas and their dependencies are in the [README](../README.md) and [Architecture.md](Architecture.md); the table
"Where to add things" in Architecture.md names the module to copy for each kind of addition.  In short:

- `Analysis/` for model-independent algebra and analysis over abstract structures; `Continuous/` for the continuous
  model (measures, tests, integrals, the signed layer); `Inference/` for statistics and named distributions;
  `Example/` for small worked programs; the abstract layer for theorems over the interfaces.
- One topic per module.  Helpers go in their own modules named after the client: `XRing` (ring identities),
  `XAlg` (algebra on tests or values), `XAux` (anything else).  Don't grow an unrelated module to host a helper.
- A module that needs excluded middle is parameterised at the top: `module X (lem₁ : LEM₁) where`.  Open other
  modules with explicit `using` lists: `open SignedExpect lem₁ using (Int; Ex)`.
- Avoid records inside parameterised modules (they are slow to check); use Σ types or top-level records.

## Header comments

Every module starts with the options line and a header comment, then `module`.  The header says what the module
provides (names in backticks, as bullets) and ends with a `Route:` paragraph that says how the proofs go, naming the
lemmas used from other modules.  It mentions the plan item it belongs to.  For example:

```agda
-- from: src/QBS/Continuous/FinProdProb.agda
-- Finite products of probability measures (plan 05, item 53a; enabler for `Inference/GaussVector`).  For probability
-- measures pᵢ on Xᵢ (`Continuous/Monad`):
--   * `prodPⁿ n Xs p = p₀ ⊗ᵖ (p₁ ⊗ᵖ (… ⊗ᵖ δ))`, a probability measure on `FinProd.ΠQ n Xs`, by the recursion of
--     `FinProd.prodⁿ` with `ExpectationProduct._⊗ᵖ_`;
```

The first sentence of the header becomes the module's line in [Modules.md](Modules.md) (`python3 scripts/modindex.py`
regenerates it).  If the proof ends up taking a different route, update the `Route:` paragraph.  While a module still
has holes, its header carries the line `--   Skeleton: holes first.`, removed when the last hole is filled.

## Style

- **Lines and declarations.**  At most 130 columns.  A declaration (signature and body) is at most 18 lines and 1000
  characters: the defaults of `scripts/longdecls.py`, run by `make longcheck`.  `scripts/longdecls.baseline` lists the
  known exceptions; a new one fails the check.  Split long proofs into named lemmas: one per case of an induction, one
  per witness step, an algebra lemma for each identity (see "Long proofs" below).
- **Imports.**  Import exactly what you use, with `using`, from the stdlib `.Base` modules where they exist.  Standard
  library imports come first, then `QBS.*`.  `make import-check` finds unused imports (it reads the HTML from
  `make html`).
- **Names follow the mathematics**, in Unicode: `∫ᴹ`, `prodⁿ`, `meanV`, `covM`, `Nᴬ`.  Recurring conventions:
  - suffixes for the kind of object: `Q` a quasi-Borel space or operation on them (`ΠQ`, `projQ`), `H` a morphism
    (`inlH`, `addRH`), `T` a signed test (`idT`, `constT`, `_*T_`), `W` a weight, `S` a signed value (`_+S_`), `V`/`M`
    vectors and matrices (`_≈V_`, `_*M_`), `Pre` a probability measure, `ᴹ` the s-finite layer;
  - suffixes for the kind of lemma: `-cong`, `-sym`, `-trans`, `-mono`, `-irr` (independent of a proof argument),
    `-map` (along a push-forward), `-law`, `-alg` (the algebraic core of a lemma);
  - a prime for a variant (`∫-prod′`), `ⁿ` for the n-ary form, `₂` for a two-argument form.
- **Comments** are sentences, with mathematics in plain Unicode (`E[f g] ≃ E f · E g`).  British spelling
  (normalise, factorise), as in the existing docs.
- **Proofs.**
  - Give every `where` helper a type signature and annotate lambda binders whose types are not obvious: an
    unannotated binder can leave unsolved metas that only show up when the module is checked from the command line.
  - Pass implicit arguments explicitly (`{Ω}`, `{X}`, the arguments of `Bnd`) when inference is slow or ambiguous.
  - Don't use `with` on large goals or on cut terms; it has hung Agda for minutes.  Use a helper lemma instead.
  - Make heavy definitions `abstract` when their unfolding is never needed (as `J`, `mapM`, `joinPre`).
  - Prefer short equational steps; use the ring solver only over an abstract ring.
  - No `rewrite` (`make doccheck` rejects it; [plans/04-equality.md](../plans/04-equality.md)): it is `with` plus a
    `refl` match, so it is never needed.  Use `cong`/`cong₂`, `subst` with a one-line motive, a reasoning chain, or
    `with … in eq`.

### Chains of equalities and inequalities

A proof that is more than two steps of `trans` is written as a reasoning chain, with every intermediate term shown
and each step justified by one named lemma.  Nested `trans (trans … ) (…)` hides the terms, is hard to read, and
breaks badly when a statement changes.  The chain shows the reader the calculation, and Agda checks each term.

- **Setoids** (most of the library: lower reals, signed values, integrals, `_≈ᴹ_`): `Relation.Binary.Reasoning.Setoid`,
  opened at the module's setoid (`open SetoidReasoning setoid`, or `Aˢ` for the abstract semiring of `Lebesgue`).
- **Orders**: `Relation.Binary.Reasoning.PartialOrder`, which mixes `≤⟨ ⟩` and `≈⟨ ⟩` steps (start with `begin` for
  ≤, `begin-equality` for ≈).  Use this rather than `≤-trans` chains.
- **Morphisms in a category** (the abstract layer: `Statistical`, `Probability`): `HomReasoning` of the category with
  `Categories.Morphism.Reasoning` (`MR`): `refl⟩∘⟨ … ⟩`, `pullˡ`, `pushʳ`, `extendʳ`, `cancelˡ`, `assoc`/`sym-assoc`
  instead of composing congruence and associativity proofs by hand.  Search `agda-categories` before writing a
  categorical lemma: most rearrangements of compositions are already there.
- **`_≡_`**: `≡-Reasoning`, or `cong` for one step.

For example, a calculation in an ordered semiring, with one solver step:

```agda
-- from: src/QBS/Analysis/GeometricNorm.agda
  E-hp i = begin-equality
    two i * (hp i * hp i)  ≈⟨ solve 2 (λ t h → t :* (h :* h) := (h :* t) :* h) refl (two i) (hp i) ⟩
    (hp i * two i) * hp i  ≈⟨ *-cong (hp-two i) refl ⟩
    1# * hp i              ≈⟨ *-identityˡ _ ⟩
    hp i ∎
```

and naturality of a monad's multiplication, in the categorical syntax:

```agda
-- from: src/QBS/Statistical.agda
  scale-nat {X} {Y} f a t = begin
    M.F.F₁ f ∘ M.μ.η X ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ extendʳ (M.μ.sym-commute f) ⟩
    M.μ.η Y ∘ M.F.F₁ (M.F.F₁ f) ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ refl⟩∘⟨ pullˡ (⟺ M.F.homomorphism) ⟩
    M.μ.η Y ∘ M.F.F₁ (M.F.F₁ f ∘ t) ∘ score ∘ a  ∎
```

Align the `≈⟨` columns when the terms are short.  A chain is still a declaration under the 18-line limit: when it
grows longer, it has a natural middle term; prove each half as a lemma.  Intermediate terms are elaborated, so on the
concrete cuts write them over abstract variables (in an `XAlg` or `XRing` module) rather than as large unfolded
expressions.

### Long proofs

A long proof is a sign of a missing lemma.  Split it:

- by case, one lemma per case of an induction;
- by step: in a chain, each step whose justification is more than a line or two becomes a lemma;
- by kind: algebra (ring identities, rearrangements) goes in an `XRing`/`XAlg` module stated over abstract variables,
  while the main module keeps the analysis (integrals, limits, witnesses).

Name the lemmas for what they say (`mean-chain`, `cov-chain`, `tuple-proj`), not `aux1`, `aux2`, and give them
signatures.  When a proof needs a large term in several places, give it a name (and make it `abstract` if its
unfolding is never needed) rather than repeating it.

## Checking

| Command | When |
|---|---|
| `agda src/QBS/…/X.agda` | after every change to X; this checks X and anything it imports that changed |
| `make doccheck` | before committing; headers, [Modules.md](Modules.md), excerpts in the docs, [Interface.md](Interface.md), no `rewrite` |
| `make longcheck` | before committing; declaration length |
| `make import-check` | occasionally, after `make html` |
| `make progress` | to check modules with holes (it builds an overlay in `_build/progress` that allows unsolved metas) |
| `make check` | rarely; a cold run of every module takes a long time |

Work module by module: check the modules you touched, not the whole library.  To time a module, delete its
interface (`_build/2.7.0.1/agda/src/QBS/…/X.agdai`) and run `/usr/bin/time -l agda +RTS -M3G -RTS src/QBS/…/X.agda`
with its dependencies already built; `make profile-QBS.X.Y` gives a per-definition profile.  Record the time and memory
of new modules in the plan's outcome paragraph.  A change to a widely imported module (`Core`, `Omega`, `LowerReals`,
`SFinite`) rebuilds much of the library, even for a comment; batch such edits ([Architecture.md](Architecture.md),
"What rebuilds when you change X").

## Documentation to update

- [Modules.md](Modules.md): regenerate with `python3 scripts/modindex.py` after adding a module or changing a header.
- [Interface.md](Interface.md): new public names, by module, one line each.
- [Guide.md](Guide.md): for a new kind of task; code excerpts start with `-- from: path` and are checked verbatim.
- [README](../README.md) "Headline results" and [Architecture.md](Architecture.md) when a major result or layer lands.
- [History.md](History.md) and [TODO.md](../TODO.md) for lessons learnt (especially performance) and open work.

## Plans

Plans in [plans/](../plans/) are numbered (`05-independence-multidim.md` is a good model).  A plan has a goal, "What
exists", "Decisions", numbered items (numbers continue across plans) with their dependencies, an order of rounds, and
a log: a "Skeletons, round N" paragraph when the statements are written and an "Outcome, round N" paragraph when
they are proved (what changed from the route, helpers, timings).  Items are marked `[done]` when filled.  Ideas that
are out of reach stay in the plan with the reason, so they can be picked up later.

Work on a plan goes in rounds: first **skeletons** (headers, imports, statements with `?` holes, checked with
`make progress`), reviewed for truth and generality; then **fills**.  Agda refuses to import a module with holes, so
order the rounds so that each module's dependencies are complete before it is filled.

## Commits

One topic per commit, with a message that says what and why ("Fill FinProdProb and GaussVector holes (plan 05,
round 4)").  Skeletons, fills and plan updates are separate commits.  Don't commit scratch files, stubs or `.bak`
files.

## For LLM agents

These rules come from what has gone wrong in practice.  They apply in addition to everything above.

**Before writing code**
- Read this file, the relevant plan in [plans/](../plans/), and the headers of the modules you will use.  Search
  for an existing lemma before writing one: [Interface.md](Interface.md), [Modules.md](Modules.md), `grep` over
  `src/`, or the Agda MCP tools (`agda_search_library`, `agda_get_module_summary`) when they are available.
- Check that a statement is true before proving it, including at ∞, at 0 · ∞ = 0, and where `_≐_` is not transitive.
  A brute-force search over a small grid of values (say {0, 1, 2, 3, ∞}) in Python is cheap and has caught false
  statements.

**Never**
- Add a postulate, change the `OPTIONS` line, or use `--allow-unsolved-metas`, `--lossy-unification` and the like in
  committed code.
- Change a statement or a non-hole definition to make a proof go through.  If a statement is false or unprovable,
  stop and report it with a counterexample or a reason.
- Edit modules outside your task, or ones another agent is working on.  Put helpers in new modules with headers and
  run `python3 scripts/modindex.py`.
- Edit sources with `sed -i` or other in-place stream edits; use an editor tool.  Don't run `find /`.
- Run a cold `make check` or `make progress` over the whole library to check your work; check your own modules.
- Commit stubs, scratch modules, or work developed against a postulated stand-in.  (Developing against a stub of a
  module that is still being filled is fine, as long as the stub is deleted before committing.)

**Checking your work**
- Check every module you touched from the command line, and look at both the exit status and the output: no
  `Unsolved`, no `error`.  An interactive load that looks clean is not enough, and a timing loop prints plausible
  times for a module that failed.
- Keep within the limits from the start (130 columns, 18 lines, 1000 characters per declaration); splitting
  afterwards is harder.
- Then run `make doccheck` and `make longcheck`.

**Common Agda pitfalls here**
- Unannotated binders in `where` clauses and lambdas leave unsolved metas.
- `with` on cut terms hangs; use a helper.  `rewrite` is not allowed at all.
- Write chains as `begin … ∎` (setoid, order or `HomReasoning` syntax), not nested `trans`; split chains over 18 lines.
- Give `{Ω}`, `{X}` and the implicit arguments of `Bnd`/`BndQ` explicitly; write `mk⊑` explicitly.
- Parenthesise applications in sums: `(map f ⟨$⟩ x) + …`.
- Comparing large concrete terms (for example two covariance matrices) can exhaust a 3 GB heap; go through abstract
  lemmas so that the large terms are never compared directly.

**Reporting**
- Say what you verified and how, what you did not, and any deviation from the planned route (and update the header's
  `Route:` paragraph).  Report time and memory for each new module checked alone.  If you broke one of these rules,
  say so.
