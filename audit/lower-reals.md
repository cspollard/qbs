# Audit: lower-reals (21 modules, about 3.6k lines)

## 1. Summary

The domain provides the value semiring Ω. `Omega.agda` defines the abstract `OrderedSemiring` and `OmegaSemiring`
records: a commutative semiring, a partial order, suprema of increasing ℕ-sequences, + and × continuous along them, and
cancellation below 1. The concrete model is the extended non-negative reals as lower cuts of ℚᵘ (`LowerReals.agda`).
The same file proves the semiring laws, `unionC` as the supremum and `Classical.cancel`, and packages them as
`cutSemiring` and `LowerRealsOmega lem`.

Further structure is layered on top as separate records, each with its own cut instance:

- `Arch` (`Archimedean.agda`, instance `LowerRealsArch.agda`): a half, tolerances ½ⁿ, an Archimedean closure and tails.
- `Min` (`Min.agda`, instance `LowerRealsMin.agda`).
- `Series`/`SeriesSup`: countable sums as the supremum of partial sums.
- `Unbounded`: unbounded integration by dyadic truncation, with its instance in `UnboundedLowerReals.agda`.

The algebra is already stated with stdlib bundles: `CommutativeSemiring`, `Poset`/`IsPartialOrder`, and the stdlib
`_^_` for `hp`. The main weaknesses are naming and the abstract-record/instance split, not the algebra.

Top recommendations:

1. Rename and merge the LowerReals* family so the instance layout is predictable.
2. Document the three-layer abstraction (`OmegaSemiring` ⊂ `Arch`/`Min`, then instances) in one place.
3. Shrink `RationalLemmas` (and the `ring₁..₇` family) to stdlib calls or inline `solve`.
4. Optionally bundle the ω-chain supremum as a stated "ω-cpo / ω-continuous semiring" layer, and do not push it to
   agda-categories.
5. Merge the micro-modules `Min`, `CutSplit`, `UnboundedLowerReals` and `Threshold` into their neighbours.

## 2. Main results

Line numbers are approximate. They come from grepping top-level declarations and the agent did not check every one.

- `OrderedSemiring` and `OmegaSemiring` (`Omega.agda:27`, `:70`): a commutative semiring with an `IsPartialOrder`,
  `0-least`, monotone + and ×, and complements below 1. `OmegaSemiring` adds `⨆` of increasing sequences,
  `⨆-ub`/`⨆-lub`, `+-⨆`/`*-⨆` and `cancel`. This is an ω-continuous semiring. It is listed in Interface.md (line 91),
  but only by the name `OmegaSemiring` with an informal gloss.
- `Cut`, `_⊑_`, `_≋_` (`LowerReals.agda:16-30`): a downward-closed, open, all-negatives-included set of ℚᵘ. Order is
  inclusion. The `Cut` header is good, but the Interface.md entry does not mention the encoding ("strictly below"),
  and `Set₁` records are used for `⊑`.
- `cutSemiring` (`:388`) and `LowerRealsOmega lem` (`:402`): the cut instance of the semiring. The only entry point is
  `LowerRealsOmega (lemOf lem₁)`, mentioned in Interface.md line 90.
- `unionC`, `union-ub`, `union-lub`, `⊕-union`, `⊗-union` (`:255-272`): suprema of chains are unions, and + and × are
  continuous. They are buried between the distributivity proofs and the `Classical` module.
- `Classical.near-sup`, `complC`, `cancel` (`:288-372`): classical lemmas (LEM₀) for complements and cancellation.
  These are the only places `lem` enters the basic file. This is a good design, but the header does not say so.
- `Arch` (`Archimedean.agda:17`): `half`, `hp n`, `arch`, `cancel≤`, `way-below`, plus the derived `∑hp≈1`. The header
  calls it "the extra structure", but `way-below` is the real content and is not described.
- `Series.∑ᶠ` and `SeriesSup` (`Series.agda:33`, `SeriesSup.agda`): countable sums as the supremum of partial sums,
  with additivity, shifting and Tonelli. This is the user-facing form of the sup, but is documented only in the module
  headers.
- `Min` (`Min.agda:24`): `mn` with glb, `mn-⨆`, `mn-add` and `mn-sup`. It is tailored to `Unbounded`, and the header
  says so well.
- `invC` (`LowerInverse.agda:26`): the inverse of a cut, with `1/0 = ∞`.
- `interC`, `liminfC`, `limsupC` (`LowerRealsInf.agda`): infima and lim inf/lim sup of cut sequences. The header cites
  "plan 03", which means nothing to outsiders.
- ExtNat (`ExtNat.agda`): ℕ∞ as `fin n | ∞`, with its `Instance` as an `OmegaSemiring`. Its non-usage of Escardó's ℕ∞
  is documented well.
- Unbounded (`Unbounded.agda:28`): `FunInf`, `Iinf`, monotone convergence, abstract in `(OmegaSemiring, Arch, Min)`.
  The header is good.

## 3. Documentation

- Add one overview paragraph to `Omega.agda`, and a "Number foundations" entry in Interface.md, saying:
  `OmegaSemiring` → `Arch` → `Min` → `Series` → `Unbounded`, each abstract in the previous one, with
  `LowerReals`/`LowerRealsArch`/`LowerRealsMin`/`UnboundedLowerReals` as the lower-cut instances. Proposed text:
  "Numbers come in three layers. (1) `Omega`: an ω-continuous ordered semiring of values.
  (2) `Archimedean`/`Min`/`Series`/`SeriesSup`: constructions and extra axioms stated abstractly in an `OmegaSemiring`.
  (3) `LowerReals*`: the instance by lower cuts of ℚ, which is the only place the rationals appear."
- `LowerRealsInf.agda`, `LowerRealsNear.agda` and `Threshold.agda` all cite "plan 03" in their headers. Replace this
  with a mathematical description, for example "Infima and lim inf / lim sup of sequences of cuts, used by dominated
  convergence".
- The module name `UnboundedLowerReals` hides the fact that it is a 14-line instance. Say so in the header, or fold it
  in.
- `Cone.agda` and `Threshold.agda` do not belong under "number foundations". Cone is a measure-level module, and
  Threshold concerns measurable functions. Move them to the measure-construction domain, or name them accordingly.
- In `LowerReals.agda`, add a short table of contents at the top. The file mixes basic cut algebra, the Classical module
  and the bundles.
- `RationalLemmas.agda` says "plain statements without instance arguments". State why: the `Positive`/`NonNegative`
  instance arguments of stdlib are hard to use inside lower-cut proofs. Without that reason, readers will see it as a
  re-implementation.

## 4. Simplification

1. **Rational wrappers vs stdlib** (`RationalLemmas.agda:40-76`). `pos`, `nonneg`, `*-pos`, `*-mono-<-pos`,
   `*-mono-≤-nn` and `inv` wrap stdlib lemmas that take `{{Positive p}}` or `{{NonNegative p}}` instances. This is
   legitimate, as the wrappers turn the instance form into a `0 < p` hypothesis. But `*-pos` and `inv` are one-liners
   over `P.*`, so check which dependents can use stdlib directly. The 46 importers suggest inlining is high churn. Keep
   the module, but document it as an adapter layer rather than "Ordered-field facts".
2. **`nat-bound` and `arch`** (`:68`, `:78`). They reprove the Archimedean property by hand with ℤ arithmetic. Check
   `Data.Rational.Unnormalised.Properties` for a `fromℕ`-style lemma. Stdlib 2.3 does not seem to have one, so the hand
   proof is probably justified. Replace the ℤ-level `nat-bound` proof with a short reasoning chain, or confirm it is
   minimal.
3. **`ring₁..ring₇`** (`:195-214`). These are seven one-line `solve` instances with opaque names. Inline them as
   `solve` calls at the use sites, or give each a descriptive name. The gain is readability, and the risk is only
   compile time at 7 sites.
4. **`add-sub` and `sub-add`** (`:94-98`). These duplicate `+-inverse`-derived lemmas in stdlib (for example
   `Data.Rational.Unnormalised.Properties` has `+-inverseʳ`, and `ring₅` is `add-sub` in another order). Merge
   `add-sub`/`sub-add`/`ring₅` into one named lemma.
5. **Min, CutSplit, UnboundedLowerReals, Threshold are tiny** (35, 27, 14 and 73 lines). Merge `Min` into
   `Archimedean`'s neighbour (or into `Omega`), `CutSplit` into `LowerRealsNear`, and `UnboundedLowerReals` into
   `LowerRealsMin` or `Unbounded`'s instances module. Gain: 4 fewer modules in Modules.md. Cost: some dependents change
   imports (`LowerRealsNear` has 17, `Threshold` 6).
6. **`Omega.agda` internals.** `≤-resp` is already derivable from `≤-resp-≈` (stdlib `IsPartialOrder`), which is
   exported through `public`. Check whether `≤-resp` can be the stdlib combined form. `⨆-const-from` and `≤′-total` do
   `ℕ.≤′` plumbing by hand. Replace `Increasing`/`inc-mono` with stdlib `Data.Nat.Properties`' `≤-induction` or
   `<-wellFounded`, or define `Increasing` via `∀ {n m} → n ℕ.≤ m → c n ≤ c m` for easier use (the current `≤′` choice
   looks historical).
7. **Duplicate cut lemmas for min/inf.** `LowerRealsInf` (`inter-lb`, `inter-glb`, `inter-mono`) and `LowerRealsMin`
   (`⊓`, `add-⊓`) both establish glb structure. `⊓` is a binary `interC`. Consider defining
   `x ⊓ y = interC (two-element sequence)` so that `Min` follows from `Inf`, or the converse. If direct proofs are
   shorter, keep both and cross-reference.
8. **Hypotheses in `Arch`.** `cancel≤` (order cancellation) is derivable from `OmegaSemiring.cancel` plus `arch` in the
   model, and the abstract interface needs both only because cancel is stated for `≈`. Check whether `cancel≤` can be
   derived from `cancel` and `arch` in the abstract record, which would shorten `LowerRealsArch`/`LowerRealsNear`'s
   `cancel-⊑`.
9. **`ExtNat` against `Cut`.** Both are `OmegaSemiring` instances proved from scratch. `ExtNat` is used only by
   `Borel.Lead` and `Continuous.ExtNatModel`. Consider a generic "semiring with ∞" lemma instead of proving `0·∞ = 0`,
   `cancel` and `distribʳ` twice. This looks high effort and low gain, so the agent would not do it.
10. **Duplicated "tolerance" definitions.** `LowerRealsArch` defines `tp n = 2⁻ⁿ` and `hpC`, `Half` defines
    `hp = half ^ n`, and `LowerRealsMin` defines `ntwo`. Confirm that `tp n` is not duplicated again by `hpC`: they
    should be linked by one lemma (`hpC n ≋ qC (tp n)`) rather than reproved at each use.

## 5. Categorical language

- **Suprema as ω-colimits.** `⨆ c inc` with `⨆-ub` and `⨆-lub` is the colimit of the diagram `ℕ → Poset` for a thin
  category. agda-categories has `Categories.Category.Instance.Posets` and general `Colimit`, but stating Ω as "a poset
  with ω-colimits preserved by + and ×" would cost a universe-level and setoid-bridge layer for no new theorems. The
  bespoke record is the better choice. A better and cheaper route is documentation: say in `Omega.agda`'s header that
  `⨆` is the supremum of an ω-chain, so Ω is an ω-cpo (pointed, with bottom 0) and + and × are Scott-continuous.
- **ω-cpo bundle.** If the maintainer wants reuse, extract a `record ωCPO` with `Carrier`, `_≤_`, `⨆` and the three
  supremum laws, and have `OmegaSemiring` extend it. This gives `⨆-cong`, `⨆-const` and `⨆-const-from` a home
  independent of the semiring, and `Series` and `SeriesSup` would use only `+-⨆`. It is moderate effort, and the gain is
  conceptual clarity and a place for the supremum lemmas to sit. Complete lattice is a poor fit: Ω has arbitrary
  suprema only classically, and the library only needs ω-chains.
- **Semiring bundles.** The library already uses `CommutativeSemiring` for the algebra and `Poset` for the order.
  `OrderedSemiring` is local because stdlib 2.3 has no ordered-semiring bundle, which `Omega.agda`'s header says. Fine
  as it is.
- **`∑ᶠ` as a colimit of finite sums.** The partial-sum chain `psum` is the colimit over finite subsets, but ℕ-indexed
  series with a specified order are more concrete, and Tonelli along the Cantor enumeration shows why. Keep the bespoke
  formulation.
- **Cuts as a (co)limit or frame.** `Cut` is the usual presentation of lower reals as Dedekind-style cuts, and
  `unionC`, `interC` are the join and meet in the lattice of ℚ-subsets. Phrase `unionC`/`interC` in the header as
  "joins/meets of the frame of downsets", but there is no reason to import a frame structure.
- **Monad/measure side.** Not in this domain.

## 6. Open questions for the maintainer

1. Are `Cone.agda` and `Threshold.agda` intended to stay in this domain, or should they move to measure-construction?
2. May `RationalLemmas` be shrunk and its importers (46) edited, or is stable names a priority?
3. Is `Increasing` via `ℕ.≤′` deliberate (for `inc-mono`'s induction), or would `ℕ.≤` and a monotone-sequence form be
   acceptable?
4. Is `Arch.cancel≤` independent of `cancel` in the abstract setting, or just an unproved convenience?
5. Is the ω-cpo extraction (a record under `OmegaSemiring`) wanted for readers, given the extra module, or is the header
   remark enough?
6. Would you accept merging `Min`, `CutSplit` and `UnboundedLowerReals` into neighbouring modules, accepting import
   churn across `LowerRealsNear` and `Unbounded` dependents?

Limits of this audit: the agent read the headers and top-level statements of all 21 modules but proofs only in
`Omega.agda`, `RationalLemmas.agda` and the tops of `LowerReals`/`Series`. Findings 4, 7 and 8 depend on proofs it did
not read, so confirm them against the code before acting.

## Implementation status (2026-11-07)

Tier A (documentation)
- Three-layer overview and the ω-cpo remark (pointed ω-cpo, `+`/`×` Scott-continuous): done, in the `Omega.agda` header.
- "Number foundations" entry in `Interface.md`: done.
- "plan 03" headers: done for `LowerRealsInf` and `LowerRealsNear` (`Threshold` had no such reference).
- `UnboundedLowerReals` header says it is a short instance module: done.
- `RationalLemmas` header explains the adapter layer over stdlib instance arguments: done.
- `LowerReals.agda` contents summary at the top, and the join/meet-of-downsets remark: done.

Tier B (simplification)
- `ring₁..ring₇`: done, renamed (no inlining, to keep each `solve` shared): `add-neg-pad`, `add-shift`, `add-telescope`,
  `sub-recover`, `add-sub-cancelʳ` (was `ring₅`), `neg-add-double`, `add-assoc-shift`. Importers updated in `LowerReals`,
  `LowerRealsNear`, `LowerInverse`.
- Merge `add-sub`/`sub-add`/`ring₅`: wrong. The three are different statements (`r + (q - r) = q`, `(q - q′) + q′ = q`,
  `(a + s) - a = s`), so they are kept; `ring₅` is documented as the right-cancellation form.
- `hpC`/`tp` link: already one lemma by construction (`hpC n = qC (tp n) (tp-pos n)`, and `hpC-double` is `qC-add` plus `tp-double`);
  nothing to change. `ntwo` in `LowerRealsMin` is a separate (doubling, not halving) sequence.

Tier E (merges): skipped, with reasons.
- `Min` into `LowerRealsMin`: `Min` is the abstract layer, `LowerRealsMin` the instance; merging would break the three layers.
- `CutSplit` into `LowerRealsNear`: `split1` is unrelated to `Near`, and its Gaussian importers (`PolyDominationOdd`,
  `GaussReal`, `GaussHalfLine`) would then depend on `LowerRealsMin`/`LowerRealsInf` for nothing.
- `UnboundedLowerReals`: it has no importers (a documented instance witness). Merging it into `LowerRealsMin` would make every
  cut-minimum importer depend on `Unbounded`. Kept.

Left alone as instructed: `ExtNat` unification, ω-cpo record, moving `Cone`/`Threshold`. Findings 2, 6, 7, 8, 9 of §4 not attempted.
