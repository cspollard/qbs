# Audit: `analysis-real` (32 modules, about 7,400 lines)

Reading audit only: module headers, docs/Interface.md entries and selected proofs were read; nothing was compiled.

## 1. Summary

This domain is the constructive real analysis that sits between the lower reals (`[0,∞]`-valued cuts) and the
probability-level results. It has four layers.

1. **Signed values.** `Signed` builds the ring of differences of "finite" elements of a commutative semiring, with
   `SignedOmega` specialising to elements bounded by a natural number. On top come signed integrals
   (`SignedIntegral`), bounded signed random variables with expectation (`BoundedRing`, `BoundedCancel`), variance
   (`Variance`), the generic estimator theorem (`Estimator`) and linear algebra over a ring (`SgLinAlg`, `ExpFamAlg`).
2. **Exponentials.** `Exp` is the power-series exponential, `ExpLower` its lower-real instance and `NegExp` the cut
   `e^{−x}`. `GeometricNorm` and `GeometricMoment2` carry the hand proofs of `∫e^{−x}=1` and `∫x²e^{−x}=2`.
   `ExpRate*` and `ExpTail` handle rates and tails.
3. **Tail FTC.** `TailFTC` and `TailFTCLip` hold the dyadic-piece algebra of a derivative-free fundamental theorem of
   calculus.
4. **Certificates.** `PolyExpCert`, `GaussExp`, `GaussCert`, `GaussCertM1` and `ExpRate` are hand-written pointwise
   certificates. `Deriv*` is a later certificate calculus (sum, scale, shift, product and chain rules) that
   subsumes them.

What is already good: `Signed` is a genuine Grothendieck construction, generic in a `SubSemiring` and delivered as
a stdlib `CommutativeRing`. Everything certificate-shaped is parameterised over an abstract `OmegaSemiring` plus `Arch`
(for solver speed), which is documented and consistent.

Top recommendations:

1. **Retire the hand-written certificate packs.** `PolyExpCert.Ex.pack`, `GaussCert.Gs.pack`, `GaussCertM1.pack1` and
   most of `ExpRate` (about 1,100 lines) are superseded by `DerivExp.xjE`, `DerivGauss.DFgauss/DFgauss1` and
   `Deriv.Daff` (see 4.1). Rewire their few dependants to `Deriv` and delete, or demote to a regression test. This is
   the biggest readability win in the domain.
2. **Replace the bespoke `Σ`, `Vec`, `Mat` in `SgLinAlg` and `ExpFamAlg`** by stdlib `Data.Vec.Functional` and
   `Algebra.Properties.CommutativeMonoid.Sum` (`∑-comm`, `sum-++`-style lemmas), keeping only matrix products (see 4.3).
3. **Rename and regroup** so the three families are visible: `Analysis/Signed/*`, `Analysis/Exp/*`, `Analysis/FTC/*`
   (see section 3). Module names such as `GeometricNorm`, `GaussTail` and `SignedOmega` do not say what they hold.
4. **State the `Deriv` calculus once as a record or category-flavoured interface** (see 4.2 and 5). Do not go further
   than that.
5. **Split the expectation story out of `BoundedRing`/`Variance`/`SignedIntegral`.** The `Estimator` theorem is stated
   against an abstract ring and expectation, but only one instance exists, and the glue is spread over three modules.

## 2. Main results

| Name | Location | Plain statement | Findable? |
|---|---|---|---|
| `Signed.signedRing` | Signed.agda:230 | signed values form a commutative ring | Yes (module header). Not in Guide.md as "the Grothendieck construction". |
| `SubSemiring` | Signed.agda:22 | the "finite elements" data | Yes, but the name hides that it is the cancellation-replacement device. |
| `Bounded` (ι, `Bnd`, `Sg`) | SignedOmega.agda | instance of `Signed` at `OmegaSemiring` bounded by ℕ | Header is one line; misses the exported names. |
| `Exp.exp-add` (`exp (x+y) ≈ exp x * exp y`) | Exp.agda (module `Exp`, Cauchy product) | the exponential law over any ω-semiring with inverse naturals | Header good; Interface entry should state it as the headline. |
| `ExpLower.expC`, `Add.exp-add`, `expC-bound` | ExpLower.agda | the exponential on `[0,∞]` | Yes. |
| `NegExp.negExp`, `negExp-expC` | NegExp.agda | `e^{−x}` as a cut, with `e^{−x}e^{x}=1` for bounded x | Yes. The header is long and buries the definition. |
| `Estimator` main theorem | Estimator.agda header | `E Sₙ = nμ`, `E Sₙ² = nσ²+n²μ²`, `E(nQₙ−Sₙ²)=n(n−1)σ²` | Header excellent. Make sure Interface.md lists it under "Statistics". |
| `BoundedRing.BSF` and `E` | BoundedRing.agda | bounded signed r.v.s form a ring and `E` is additive | Header good. |
| `Variance` (`Bdd`, `Var`) | Variance.agda | `Var f = E f² − (E f)²` | Header thin: say what is proved. |
| `Geo`, `norm` | GeometricNorm.agda | `∫₀^∞ e^{−x} dx = 1` algebra | Name opaque. |
| `GeoMom2` | GeometricMoment2.agda | `∫ x² e^{−x} = 2` algebra | Name opaque. |
| `D`, `Deriv`, rules `Dsum Dscale Dshift Daff` | Deriv.agda | certificate that `G′ = k − h` | Header excellent; Interface.md entry too dense. |
| `DFprod`, `DFexp`, `DFgauss` | DerivProd/Chain/Gauss | product and chain rules, Gaussian derivative | In Interface.md. |
| `ftc-lip` algebra (`UpL`, `LoL`, `up-stepL`) | TailFTCLip.agda | glue of two halves of a dyadic piece | Interface.md line 196: good. |
| `exp-facts`, `tail` | TailFTC.agda, ExpTail.agda | first-order facts of `e^{−x}`, `Nᵉe^{−N} ≤ ½ᵐ` | `exp-facts` is inside `AlgT`, so easy to miss. |

## 3. Documentation

1. **Module names that do not say what they hold.**
   - `GeometricNorm` → `ExpIntegralOne` (or `GeoExpNorm`): "the algebra of `∫e^{−x}=1`".
   - `GeometricMoment2` → `ExpIntegralSecondMoment`.
   - `GaussTail` (42 lines) → fold into `GaussExp`.
   - `SignedOmega` → `SignedBounded`.
   - `AffineAlg`, `ExpRateSigned` and `SgLinAlg` (despite the name, it is ring-generic) → `RingLinAlg`.
   - `ExpFamAlg` → `ExpFamilyAlgebra` (it is also referenced by name from `Inference/ExpFamily`).
   Renames cost churn, so a `docs/Modules.md` table of one-line descriptions is the cheap alternative.
2. **Subdirectories.** Proposed grouping (path-only moves, no content change):
   - `Analysis/Signed/{Core,Bounded,Integral,Variance,Estimator,BoundedRing,BoundedCancel,LinAlg}`;
   - `Analysis/Exp/{Series,Cauchy,Lower,Neg,Rate,RateExt,Tail,Geometric}`;
   - `Analysis/FTC/{Core,Lip,Deriv,DerivProd,DerivExp,DerivChain,DerivGauss}`;
   - `Analysis/Cert/{PolyExp,Gauss,GaussM1}` (legacy).
   `Cauchy` is a generic series theorem and belongs with `Series`, which is in the lower-reals domain.
3. **`Signed.agda` header.** Add the sentence the file lacks: "`Sg R F` is the Grothendieck group completion of the
   additive monoid of `F`, extended to a ring; for `F` closed under cancellation it is the usual `p − n` quotient."
   Also say why `SubSemiring.Is` (rather than a sub-record) is used. Name the universal property if it is not proved
   (see Q1).
4. **`Deriv.agda` header and Interface.md** (lines 253–260). The Interface entry for `AlgD` is one 900-character
   line. Proposed replacement is a three-line preface followed by one bullet per rule:
   > *Certificate calculus.* `D M c G h k` (`Deriv M G h k` hides `c`) certifies `G′ = k − h` on `[0,M]` by Lipschitz
   > bounds and a two-sided first-order certificate. Rules: constants/identity, `Dsum`, `Dscale`, `Dshift`, `Daff`
   > (compose with `l ≤ 1`), `DFprod`, `DFexp` (chain), plus `D-resp`. Hand-written packs in `PolyExpCert`,
   > `GaussCert` and `ExpRate` are legacy.
5. **Mark legacy.** `PolyExpCert`, `GaussCert`, `GaussCertM1` and `ExpRate` headers should begin "Superseded by
   `Deriv*` for new work; kept because `Continuous/{HalfLineMomentN,GaussHalfLine,GaussMeanUnit,ExpRateInt}` still use
   `pack`". Today a newcomer reads about 1,100 lines before learning there is a shorter route (`DerivExp.agda:11`
   says "instead of a 300-line pack", but only in the later file).
6. **`NegExp.agda` header** is a 15-line paragraph. Lead with: "`negExp : Cut → Cut` is `e^{−x}` as a lower cut,
   `q ∈ negExp x ⇔ ∃ p>q, ∀ s ∈ expC x, p·s<1`. Main facts: `negExp-zero`, `negExp-anti`, `negExp-expC`
   (`e^{−x}e^{x}=1` for `x ≤ N`), `Meas-negExp`." Move the openness rationale to a comment at the definition.
7. **`Variance.agda` header**: state the headline `Var f = E f² − (E f)²` as a named lemma and say which file
   consumes it.
8. **`BoundedRing`/`Estimator` bridge.** Add a short example to the Guide ("sample mean of n coin flips is unbiased")
   that instantiates `Estimator` through `BoundedRing`. Currently the generic theorem is only discoverable from the
   header.

## 4. Simplification

### 4.1 Hand-written certificate packs vs `Deriv*` (largest item)

Evidence:
- `PolyExpCert.agda` (369 lines) builds `Ex.pack` for `xʲ e^{−x}`. `DerivExp.xjE` (91-line module) gives the same
  `Deriv M (xʲ⁺¹ e^{−x}) …` from the rules.
- `GaussCert` (299) and `GaussCertM1` (123) give `pack`/`pack1` for `xʲΦ`; `DerivGauss` (64 lines) gives `DFgauss`
  and `DFgauss1` and `Continuous/DerivGaussMoment` validates them against the same integrals.
- `Continuous/DerivMoment` revalidates `∫ xⁿ e^{−x} = n!`, the statement `HalfLineMomentN` proves via `pack`.
- Importers of the legacy packs (from the grep): `GaussHalfLine`, `GaussMeanUnit`, `HalfLineMomentN`.
  `ExpRateInt` and `HalfLineRate` use `ExpRate`.
- `Deriv.Daff` "generalises `AlgRate`", so `ExpRate.Rate` (412 lines) plus `ExpRateExt` (268) plus `ExpRateSigned` are
  candidates too. The real obstruction is that `Daff` requires `l ≤ 1`; `ExpRateExt`'s halving extension could be
  absorbed once into `Daff` (a width-`t` piece with `l t` of any size is split `K` times) rather than carried as a
  separate 268-line module.

Proposal: migrate the four Continuous dependants to `Deriv`, then delete the three packs, keeping `pw`/`dpw`/`yt` and
`exp-facts` (which `Deriv*` import). Expected gain: about 800–1,100 fewer lines and one documented route. Cost: each
migration changes the type of the certificate input and rechecks heavy `Continuous` modules (the `HalfLineMomentN`
header already shows eight nested `proj₂`; that destructuring disappears). Risk: compile time of `Deriv*`-based proofs
(they carry larger constants, `Cp`, `Cx`). Mitigation: do it moment by moment, timing each.

### 4.2 The `D` constant-hiding wrapper repeats across modules

`Deriv`, `DerivProd` (`Cp`/`Fin-Cp`), `DerivChain` (`Cx`/`Fin-Cx`) and `DerivGauss` (`Fin-half`) each hand-prove "the
resulting constant is finite". Proposal: `Deriv` carries `Fin c` as a field of a record `Cert`; each rule states only
its constant function `c ↦ c′` together with a monotonicity lemma `Fin c → Fin (c′ c)`. Equivalent to the current
`Deriv` but about 30–40 lines shorter per module. Low risk, since it is a purely local refactor.

### 4.3 `SgLinAlg` and `ExpFamAlg` duplicate the standard library

- `SgLinAlg.agda:41–70` defines `Σ n f = f 0 + (… + 0)`, `Σ-cong`, `Σ-0`, `Σ-+`, `Σ-scale`, `Σ-swap`. Stdlib has
  `Data.Vec.Functional` (`Fin n → A`), `Algebra.Properties.CommutativeMonoid.Sum` (`∑-comm`, `sum-cong-≈`, sum over
  `Table`), and `Algebra.Module` bundles. `Σ-swap` is `∑-comm`; `Σ-+` is `sum` additivity over a commutative monoid.
- `ExpFamAlg.Σ-concat` is stdlib `sum-++`-style (via `Data.Vec.Functional._++_`).
- Matrix laws (`*M-assoc`, `ᵀ-*M`) are not in stdlib; keep, but state them via `Data.Vec.Functional` types so that
  `Mat m n = Vec m (Vec n R)` costs nothing.
- Proposal: re-base on `Data.Vec.Functional` and stdlib sums; keep matrix products. Expected gain: 50–80 lines and
  fewer helper names in `ExpFamilyAlg`, `RandomVectorAlg`, `SgSampleAlg` (all import these `Σ` lemmas).
  Cost: `Σ` is defined recursively here, so definitional unfolding in downstream `RandomVector*` proofs may break;
  these are the same modules audited under continuous-signed-info.

### 4.4 `AffineAlg`, `ExpRateSigned`, `GaussTail`, `ExpTail`: tiny `Alg` modules

Four modules are 40–90 lines of pure algebra over `OmegaSemiring` and `Arch` for one caller each (`GaussTail` 42,
`ExpRateSigned` 39). The "no concrete cuts, to keep the solver fast" rule justifies the *abstraction*, not a separate
file each. Merge `GaussTail` into `GaussExp`, `ExpRateSigned` into `AffineAlg` (the variance of Exp(λ) is the
`var-core` case of `AffineAlg`, header says so), and give `AffineAlg` the name `SignedMomentAlg`.
Gain: four fewer files and one place for "moment algebra". Cost: negligible.

### 4.5 `Signed`/`SignedOmega`/`BoundedCancel`

- `Signed.agda:35`: `≃-refl` is proved by two `+-comm`s and a `trans`; `solve` is already open in the module (line 35).
  `≃-refl {x} = mk≃ 0# Is-0 (solve …)` is shorter. Micro, but representative: many equality steps in `Signed`
  (lines 120–200) are `begin … ∎` chains that `solve` can do in one line over the abstract semiring.
- The ring structure is proved from first principles (lines 211–232). The alternative of defining `Sg` as a quotient of
  `R×R` by a congruence is not cheaper. Keep the direct presentation.
- `BoundedCancel`: header says `a ≤ n`, `a+x=a+y ⇒ x=y` by halving. This is exactly "bounded elements are cancellative",
  the reason `Signed` needs a witness `k`. Use it to prove `Signed.≃` coincides with naive `p+n′ ≈ p′+n` on
  bounded elements. Then `BoundedRing`'s equality (pointwise `≃`) and its use of `cancel-bnd` can be stated once as
  "ι is injective on bounded elements".

### 4.6 `BoundedRing` / `SignedIntegral` / `Variance` / `Estimator`

`BoundedRing` re-exports operations "of `Analysis/SignedIntegral` and `Analysis/Variance`"; `Variance` defines `+SF`,
`*SF`, `Bdd`; `SignedIntegral` defines `SF`. The ring `BSF` is therefore assembled from three modules. Consolidate
`SF`, `Bdd`, `+SF`, `-SF`, `*SF`, `constSF` into `SignedIntegral` (or a new `SignedFunction`), keeping `Variance`
for the `Var` lemma and `BoundedRing` for the quotient and expectation. Expected gain: a reader finds the ring in one place.

### 4.7 `GeometricNorm` and `GeometricMoment2`

Together 830 lines for `∫e^{−x}=1` and `∫x²e^{−x}=2`, proved by self-similarity of the first bit. With the `Deriv`
calculus these are derived from `DE` plus `Dsum` and `tail`. `Continuous/TailFTCExp` already re-derives
`I-negExp-unit` from `ftc-unit`, and `DerivMoment` gives `∫xⁿe^{−x}=n!`. Proposal: make the `Deriv` route the primary
proof of the normalisation facts and keep `Geometric*` only as an independent check, or remove them. This is gated on
whether `HalfLineUnit`/`HalfLineMoment2`, which import them, are still needed once `ExpRate` goes. Gain: up to about
800 lines. Cost: three downstream modules.

### 4.8 `Exp` module parameter style

`Exp.agda` takes `inv : ℕ → A` as bare function parameters, "not a record, expensive". Fine, but `ExpLower` then
re-proves positivity of reciprocals and `qC-mul` (about 60 lines of rational cut lemmas, `P-id`, …). Check whether
`LowerRealsInf`/`RationalLemmas` already export `qC-mul`; if so, delete the local copy.

## 5. Categorical language

- **Grothendieck ring.** `Signed.Sg` is the free-ring-completion of a semiring restricted to a sub-semiring.
  stdlib has no ring or group completion of a semiring (grep for "Grothendieck" there: none), and agda-categories was not
  checked for one (not verified; its Grothendieck, if present, is the fibration construction, a different notion). The bespoke construction is therefore correct; do not replace it. What
  would improve it: prove the universal property once ("any additive map `F → G` into an abelian group extends
  uniquely along `ι`") so that consumers such as `SignedIntegral.E` and `Estimator` get linearity from it rather than
  by hand. This is about 60 lines and removes proofs `E-+`, `E-neg` repeated in `SignedIntegral` and `BoundedRing`.
- **Ring solver.** Already used; the abstract-semiring trick (solve over `OmegaSemiring`, not over cuts) is right and
  should be documented as a pattern in Contributing.md.
- **Certificates as one interface.** `Deriv` is already the generic interface. A categorical rewrite ("functions
  `[0,M] → A` with derivative data form a category/CRing-object; `DFprod` is the ring multiplication") adds
  structure but not proofs: the Lipschitz and certificate constants differ per rule, so a bundled `CommutativeRing`
  of "differentiable functions" would need an existential on the constant and would lose the explicit `Cp`, `Cx`
  bounds that downstream finiteness proofs rely on. Bespoke is better here. The one worthwhile move is 4.2.
- **Estimator.** An additive map `E : R → S` of commutative rings is a (non-multiplicative) `Algebra.Morphism`
  (`IsAbelianGroupMorphism`); `Estimator`'s `E` could be taken as stdlib `IsGroupHomomorphism`. Easy; only a tidy-up.
- **Linear algebra.** Stdlib `Algebra.Module` (left and right modules over a ring) can name `Vec n R` as a module,
  and a matrix as a linear map; worth it only if `SgLinAlg` is re-based as in 4.3. Do not use agda-categories
  `Matrix`-style categories: universe levels and setoid equalities make `Mat` the simpler choice.

## 6. Open questions for the maintainer

1. Is the universal property of `Signed` (extension of additive maps along `ι`) proved anywhere? If not, would you
   accept 60 lines for it, to be reused by `SignedIntegral.E` and the `SgLimits` modules?
2. May the legacy `pack`s (`PolyExpCert`, `GaussCert`, `GaussCertM1`, `ExpRate`) be retired? Do `HalfLineMomentN`,
   `GaussHalfLine`, `GaussMeanUnit` and `ExpRateInt` have to keep their current checked types because of Guide or
   Interface text?
3. `Daff` needs `l ≤ 1`. Is folding `ExpRateExt`'s halving extension into `Deriv` acceptable (it would let `ExpRate`
   be deleted entirely)?
4. Is the `Σ` of `SgLinAlg` defined recursively on purpose (definitional unfolding in `RandomVector*`)? That decides
   whether 4.3 is a drop-in replacement.
5. Directory regrouping (section 3, item 2): is a one-off rename tolerable with dependent plans/ files and docs links?
6. Does `Cauchy` belong with `Series` (lower-reals domain)? It is generic over `OmegaSemiring` and only `Exp` uses it.

## Implementation status (2026-11-07)

Agent 5 (`analysis-real`), tiers A, C and part of E; tiers B and D not started (out of budget).

- **A. `Signed` header: done.** It now names the Grothendieck group completion delivered as a stdlib `CommutativeRing`, and says why `SubSemiring` is a predicate plus closure fields.
- **A. `Interface.md` Deriv entry: done.** A preface plus one bullet per rule; the packs are named legacy there.
- **C. `PolyExpCert.Ex.pack` (exponential moments): partly done.** `HalfLineMomentFact.moment-succ` now uses `OnHalfLine.glue-D` with `dvn` (formerly `DerivMoment.dvn`) from `DerivExp.xjE`.  `HalfLineMomentN.AtInterval` (the only consumer of `pack` there) and `DerivMoment` (now a duplicate) are deleted.  `Ex.pack` itself stays: `ExpRate` builds its rate-λ certificate from it.  `HalfLineMomentN` 49.6 s to 5.5 s, `HalfLineMomentFact` 26.6 s to 6.2 s.
- **C. `GaussCert.pack` and `GaussCertM1.pack1`: done, both modules deleted.**  New rule `DerivGauss.Gx.DFgaussJ` (all powers `(xʲ⁺¹Φ)′ = (j+1)xʲΦ − xʲ⁺²Φ`; `DFgauss1` is its j = 0 case and is removed).  `GaussMoment.moment-succ` uses it via `glue-D`; `GaussMean.∫-xφ` uses `DFgauss` via `glue-D0` (the hand-written telescoping sum is gone).  Deleted: `GaussCert`, `GaussCertM1`, `GaussMeanUnit`, `DerivGaussMoment` (duplicate), `GaussHalfLine.AtInterval`, and the now unused `Gauss` module of `GaussExp`.  `GaussHalfLine` 11.7 s to 5.6 s; `GaussMoment` 6.1 s and `GaussMean` 6.4 s unchanged.  `Ea`/`Eb`/`Ec` moved from `DerivGaussMoment` to `GaussHalfLine`.
- **C. `ExpRate`, `ExpRateExt` (and `ExpRateSigned`): skipped, marked legacy in headers.**  `ExpRateInt` and `ExpRateMoment` need rates `l > 1` through `ExpRateExt`'s halving extension; `Daff` requires `l ≤ 1`, so folding that extension into `Deriv` is new development (open question 3), not a migration.
- **E. Merge `GaussTail` into `GaussExp`: done** (`AlgGT` now lives in `GaussExp`; three importers updated).
- **E. Merge `ExpRateSigned` into `AffineAlg`; consolidate `SF` and `Bdd`; renames of `GeometricNorm`, `GeometricMoment2`, `SignedOmega`: not done.**
- **B/D. Σ machinery on stdlib; universal property of `Signed`; "constant is finite" boilerplate: not done.**
- **Not reached (no finding disproved):** report items 4.2, 4.3, 4.5 to 4.8 and the Signed `≃-refl` micro-simplification.
