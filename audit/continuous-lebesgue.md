# Audit: `continuous-lebesgue`

Reading audit; no Agda was run.  Line numbers are those of the working tree at 2026-11-07.  Paths are under `src/QBS/Continuous/`.

## 1. Summary

The domain builds, on the weight space `WQ = [0,∞]` (lower cuts of ℚ) and the real line `RQ = WQ +Q WQ`, everything one expects from
one-dimensional Lebesgue integration: `lebPre`, the measure whose integral of `h : WQ ⇒ WQ` is the fair-coin sum of unit pieces,
has the expected mass on every interval (`LebesgueInterval`), is characterised by those masses (`UniquenessWQ`, `UniquenessR`,
`UniquenessRQ`: a π-λ style uniqueness theorem for s-finite measures), is translation and scale invariant (`LebesgueShift`,
`LebesgueScale`, `RealShift`, `RealScale`), obeys the fundamental theorem of calculus on dyadic intervals from `Deriv` data
(`FTCDyadic`), and so satisfies monotone change of variables (`ChangeOfVariables`).  Separately, it proves the convergence
theorems for the Daniell integral `∫ᴹ` over any source `X` (monotone, Fatou, reverse Fatou, dominated, and signed dominated),
with their helper layers (`SupTest`, `Fatou`, `Dominated`, `ConvEps`, `NullInf`, `MonusAlg`, `InfAlg`).  The library is about
24.6k lines in the whole `Continuous/` directory; this domain is 44 modules.

Top recommendations:

1. Rename or re-head the modules whose names hide their content (`UniquenessR` is uniqueness on Cantor space; `RealModel` is
   the model instance; `RQArith` is affine maps on ℝⁿ; `Monus` holds truncated subtraction tests; `LebPlane` is the product
   Lebesgue measure) and add the missing Interface.md entries: **there is no Interface.md or Guide.md entry for Fatou, `dct`,
   `mct-conv`, `uniqWQ`/`uniqRQ`, `leb-Iv`, `cov`/`covF`, `ftc-dy`, `RealShift` invariance or `ConvEps`**.
2. Merge the 12 "`…Alg`/`…Cut`/`…Nat`/`…Aux`" helper modules into their parents, or at least into one `Continuous/Lebesgue/`
   directory with a public façade; the sprawl is the main obstacle for a reader (section 4.4).
3. State the convergence theorems once: `Conv`/`EConv` (convergence in `[0,∞]`) is defined in `Dominated` yet `ConvEps`
   re-derives liminf/limsup tolerance lemmas that `DominatedSigned` consumes; one `Convergence` module with `Conv`, `EConv`
   and the single "integral commutes with a limit under a bound" schema would shorten both (4.2).
4. Phrase `cov`, the scale/shift theorems and `ChangeOfVariablesFn` as one statement, "`mapM ψ lebPre ≈ reweightPre φ′ lebPre`",
   i.e. pushforward functoriality of `mapM` plus reweighting; `LebesgueShift`, `LebesgueScale`, `RealShift`, `RealScale` are all
   instances of "`mapM f lebPre` is again `lebPre` up to a weight" proved four times by the same route (4.3, 5).
5. Move the pure-ℚ lemmas that sit in `RQArithAlg`, `LebesgueShiftCut`, `NullInf` (`nat-2`, `pow-hp`, `tiny`, `zero-of`) and
   `ConvEps` (`tail`, `at-tail`, `not-all`, `close`) into `Analysis/RationalLemmas` / `Analysis/HalfOrder` / a shared `Tolerance`
   module (4.1).

## 2. Main results

Legend: Doc = easy to find (module header H, Interface I, Guide G) and crisply stated.

| Name | file:line | Plain statement | Mathematics | Doc |
|---|---|---|---|---|
| `leb-Iv` | LebesgueInterval:67 | Lebesgue mass of `[a,b)` | `a + λ[a,b) ≈ b` for `a ≤ b`, `b` finite | H only; not in I.  Stated additively (no subtraction on `[0,∞]`): say so |
| `leb-unique` | LebesgueInterval:70 | Interval masses determine Lebesgue measure | `μ[a,b) = b−a ∀ a≤b<∞ ⇒ μ = λ` | H only; not in I |
| `ftc-dy` | FTCDyadic:126 | FTC on each dyadic interval | `∫_{[m/2ⁿ,(m+1)/2ⁿ)} h + G(right) ≈ G(left) + ∫ k` where `G′ = k` with slack `h` | H only; the statement of what `Deriv` gives is hard to parse |
| `cov`, `cov-inv` | ChangeOfVariables:166,163 | Monotone change of variables | `∫ g(φx) φ′(x) dx = ∫ g(y) dy`; `∫ h(ψ y) dy = ∫ h φ′` | H good; not in I/G |
| `covF`, `covF-inv` | ChangeOfVariablesFn:70,66 | same, from plain functions on cuts | same | H; not in I |
| `uniqWQ` | UniquenessWQ:84 | Measures on `[0,∞]` agreeing on intervals are equal | π-λ uniqueness, s-finite | H good; not in I (Guide has docs/UniquenessLit.md?) |
| `uniqR` | UniquenessR:324 | Uniqueness on Cantor space (σ-finite form) | agree on clopens ⇒ equal | H good; module name hides it |
| `uniqRQ` | UniquenessRQ:100 | Uniqueness on ℝ | agree on both half-lines ⇒ equal | H; not in I |
| `∫ᴹ-lebR-shift` etc. | RealShift:~200 | Translation invariance of `lebR` by finite `t` | `∫ f(x+t)dx = ∫ f` | H; I lists `lebR` only |
| `lebR` scale/reflection | RealScale | `∫ f(cx) c dx = ∫ f`, `x ↦ −x` | | H |
| `fatou`, `rev-fatou` | Fatou:252,263 | Fatou, and its reverse under a bound | `∫ liminf h ≤ liminf ∫ h`; `limsup ∫ h ≤ ∫ limsup h` if `h ≤ g`, `∫ g<∞` | H; not in I/G |
| `dct` | Dominated:80 | Dominated convergence on `[0,∞]` | `h n → f` pointwise, `h n ≤ g`, `∫g<∞ ⇒ ∫ h n → ∫ f` | not in I/G (G cites only the signed one) |
| `mct-conv` | Dominated:91 | Monotone convergence as `Conv` | `∫ h n ↑ ∫ sup h n` | not in I/G |
| signed `dct` | DominatedSigned (consumed by SignedLimits `dct-Ex`) | Dominated convergence for signed tests | as above for `h⁺−h⁻` | G line 171, I line 305; good |
| `ConvEps` `EConv` | ConvEps:80,91 | ε-form of convergence implies `Conv` | `∀k ∃N ∀n≥N |a n − l| ≤ 2⁻ᵏ ⇒ a n → l` | module header only |
| `NullInf` | NullInf | Integrable ⇒ a.e. finite | `∫ g < ∞ ⇒ λ{g=∞}=0` | H; name `NullInf` says neither theorem nor hypothesis |
| `monus` tests | Monus | `x ↦ x ∸ t`, `t ∸ x` are tests | | H; not in I |

## 3. Documentation

- **Interface.md gap.**  Lines 164–199 of Interface.md document the half-line *distributions* but nothing of this domain apart from
  `RealLine`/`RealDensity` (240–241).  Add a section after "Lebesgue measure on [0,∞)":

  > ### Lebesgue measure and its uniqueness (`LebesgueInterval`, `UniquenessWQ`, `UniquenessR`, `UniquenessRQ`)
  > - `leb-Iv` — `a + λ[a,b) ≈ b` for finite `b ≥ a` (the additive form of `λ[a,b) = b − a`);  `leb-unique` — the converse:
  >   a measure with these masses is `lebPre`.
  > - `uniqR`, `uniqWQ`, `uniqRQ` — two s-finite measures on Cantor space, on `[0,∞]`, on ℝ that agree on clopen cells,
  >   dyadic intervals, respectively half-line intervals, are equal (σ-finite π-λ theorem, `docs/UniquenessLit.md`).
  > - `shift-inv`, `scale-inv`, `lebR` shift/scale/reflection (`LebesgueShift`, `LebesgueScale`, `RealShift`, `RealScale`).
  > ### Change of variables (`ChangeOfVariables`, `ChangeOfVariablesFn`, `FTCDyadic`)
  > - `cov`, `cov-inv` — for an increasing bijection φ of `[0,∞]` with inverse ψ and a derivative certificate φ′:
  >   `∫ g(φ x) φ′(x) dx ≈ ∫ g(y) dy` and `∫ h(ψ y) dy ≈ ∫ h(x) φ′(x) dx`.
  > ### Convergence theorems (`SupTest`, `Fatou`, `Dominated`, `DominatedSigned`)
  > - `Conv a l` — `liminf a ≈ l ≈ limsup a` in `[0,∞]`; `mct-conv`, `fatou`, `rev-fatou`, `dct` for `∫ᴹ p` over any `X`.

  and extend the Guide.md table at line 171 with `Dominated` (unsigned, with `mct-conv`) and `Fatou`.
- **Module names that hide content** (propose renames or at least first-line headers):
  - `UniquenessR` → `UniquenessCantor` (it is about `ℛ`, not ℝ; `UniquenessRQ` is the real-line one).
  - `RQArith` (inside it a nested `module RQArith`, line 75) → `RealAffine`; header: "addition, signed scaling and affine maps `RQⁿ ⇒ RQᵐ`
    as QBS morphisms".  Its "(plan 05, item 55)" reference means nothing to outsiders.
  - `Monus`/`MonusAlg` → `Truncated`/…; `NullInf` → `IntegrableFinite` (header already says what it is).
  - `RealModel` (20 lines) is the continuous model's `IsQBSLike` instance; header should state "the main entry point for the
    continuous model", and I.120 already groups it correctly.
  - `LebPlane` → `LebesgueProduct`; `TopMulPos` (47 lines) belongs in `InfAlg`.
- **"plan 03/05" parentheticals** appear in every header of the domain (`grep -c 'plan 0[35]'` ≈ 44); outsiders cannot resolve them.
  Replace by the mathematical topic ("Lebesgue measure", "dominated convergence") and keep the plan reference at the end.
- **Buried results.**  `Fatou.agda` (276 lines) spends lines 90–250 on `minH`, `Decr`, `split-ineq`, `step-A` before `fatou` (252) and
  `rev-fatou` (263); the header lists them but add `-- Main results: fatou (252), rev-fatou (263)`.  `UniquenessR` (325) buries `uniqR` on the last
  line.  `RealShift` (220) is mostly the choice machinery `Dec/pick/flg/pieces` (88–150) for a one-line statement of invariance.
- Proposed header for `Dominated`:

  > -- Monotone and dominated convergence for the Daniell integral `∫ᴹ p` on any source `X`.  `Conv a l` means
  > -- `liminf a ≈ l ≈ limsup a` in `[0,∞]`.  Main results: `mct-conv` (increasing `h n ↑ f`), `dct` (pointwise convergence, an integrable
  > -- bound), `dct-prob` (the probability-measure version with constants).  Fatou is in `Fatou`; the signed version in `DominatedSigned`.

## 4. Simplification

### 4.1 Arithmetic helpers duplicated or misplaced

- `NullInf.agda:80-99` (`nat-2`, `pow-hp`, `pow-hp0`, `tiny`, `zero-of`) are statements about `nat` and `hp` (`2⁻ᵏ`) in an arbitrary
  ordered cone; the only other lower-reals home is `Analysis.HalfOrder`/`Archimedean` (lower-reals domain).  `zero-of` ("`∀k. k·E ≤ N ⇒ E = 0`")
  is the Archimedean property and should live next to `RationalLemmas.arch` (RationalLemmas:78) as a generic cone lemma.
  Gain: ~25 lines, a reusable name.  Risk: low.
- `ConvEps.agda:63-71` (`tail`, `at-tail`, `not-all`) are purely ℕ/logic and have nothing to do with `[0,∞]`; `tail` is stdlib
  `Data.Nat.Properties` (`m≤n⇒∃[o]m+o≡n`, spelt `≤⇒∃`/`m≤n⇒m+o≡n` depending on version).  Replace.
- `ConvEps.agda:100-123` (`close`, `low-step`, `low-tail`, `no-all`): four lemmas that each unfold `mem l r` with
  `r′ ≤ r + 2⁻⁽ᵏ⁺²⁾`; they are the single fact "a bounded lower real is within ε of a member".  Check whether
  `Analysis.LowerRealsNear` (lower-reals domain) already has it; if so `ConvEps` shrinks by half.
- `LebesgueShiftCut` (80), `MonusAlg` (106) and `InfAlg` (96) all open `RationalLemmas` with overlapping `using` lists
  (`≃-<ʳ; lt-add; 0<1; nat-suc; nat-bound` appear verbatim in `InfAlg:27` and `MonusAlg:32`), and each re-proves
  small `Bnd` facts (`bnd-rat`).  A single `Analysis/BoundedCuts` module for `Bnd`, `bnd-rat`, `monus`, `monus-add`,
  `monus-anti`, `inter-add` would serve `Monus`, `Fatou`, `NullInf`, `ConvEps`, `DominatedSigned`.
- `RQArithAlg` (194 lines, "value-level algebra behind the `idT` laws") is over a generic `[0,∞]` carrier; see the analysis-real and
  continuous-signed-info reports (`SgLinAlg`, `AffineAlg`, `BoundedRing`) for the same affine algebra stated a third time.  Coordinate with them.

### 4.2 Convergence theorems: one shape

All of `mct-conv`, `fatou`, `rev-fatou`, `dct`, signed `dct` and `inf-k`/`tail-small` follow one pattern:

  hypothesis: pointwise inequality/convergence of `h n` against `f`  ⇒  `∫ᴹ p` of the liminf/limsup is bounded by the liminf/limsup of the `∫ᴹ p`.

`dct` (Dominated:80) is already two lines from `fatou` + `rev-fatou` + `∫ᴹ-monoX`; the signed version (DominatedSigned, 247 lines)
reproves the same through `cutH`, `pnH`, `pn-ec` and the final algebra `final-alg` (72).  Concrete steps:
1. Keep `fatou` and `rev-fatou` as the only primitive statements; derive `mct-conv` from `fatou` + `∫ᴹ-mono` (currently 25 lines
   at Dominated:91-100, using its own `u`, `iu`).  Gain ≈ 15 lines.
2. Make the signed theorem a corollary of the unsigned via the splitting `h = h⁺ − h⁻` plus the generic lemma
   "if `a n + c n ≈ b n + d n` with `a n → a`, … then ...".  `final-alg` is exactly this and takes `P ≤ hp k` hypotheses that look
   unavoidable only because convergence is expressed with ε (`hp k`); with `Conv` (liminf/limsup) the algebra is the easy case.  This is the
   reason `ConvEps` exists; check whether `EConv` is needed outside `DominatedSigned` (grep shows no use in Dominated or Fatou).  If it
   is not, inline the needed half into `DominatedSigned` (ConvEps is 201 lines for one consumer).
3. `FatouAux` (86 lines) is imported only by `Fatou`; merge (Fatou would be ~360 lines, within the library's norm).

The cost is risk to `SignedLimits`/`SignedLimitsAlg` (continuous-signed-info) which consume `dct`; keep the exported names.

### 4.3 Lebesgue invariance proved four times

`LebesgueShift` (126), `LebesgueScale` (83), `RealShift` (220), `RealScale` (72), and `ChangeOfVariables` (168) all follow
"build a measure `ν` from `lebPre` and an operation; show `ν[a,b) = b − a` using `leb-Iv`; conclude by `leb-unique`".
`LebesgueScale.agda:6-7` and `ChangeOfVariables.agda:7-14` say so in their headers.  Make this one lemma:

  `leb-char : ∀ (ν : Pre (XW WQ)) → (∀ a b → a ≤ b → Bnd b → a + ∫ᴹ ν (χIv a b) ≈ b) → ∫ᴹ ν (χInf) ≈ 0# → ν ≈ᴹ lebPre`

(`LebesgueInterval.leb-unique` already is this with `χInf` omitted; the `χInf`-null clause is re-proved as `χInf-scale`,
`χInf-pull`, `inf-null`, `inf-sp`, `inf-ptL`… in at least five modules).  Move the `χInf` clause into `leb-unique` (derive it from
finiteness on `[k,k+1)`, as `ChangeOfVariables` does at `finI`) so that scale/shift/φ are each ~15 lines.  Gain: 100–150 lines
in `LebesgueScale*`, `LebesgueShift*`, `ChangeOfVariablesAlg`.  Risk: moderate (names propagate to `Continuous/Uniform*`,
`Gauss*`, which import `∫-scale`, `shift-inv`).

### 4.4 Helper-module sprawl

Twelve of the 44 modules are helpers: `ChangeOfVariablesAlg`, `FatouAux`, `InfAlg`, `LebesgueDyadicAlg` (234 lines, the largest helper in the domain),
`LebesgueDyadicNat` (67), `LebesgueIntervalAlg`, `LebesgueScaleAlg`, `LebesgueShiftAlg`, `LebesgueShiftCut`, `LipTestAlg`, `MonoTestAlg`
(this one is not in `Modules.md` by that name check), `MonusAlg`, `RQArithAlg`, `UniquenessRQAlg`, `TopMulPos`, `FTCDyadicPiece`.  The `Alg` suffix means
"value-level lemmas over the abstract carrier, to keep the module with the QBS morphisms fast to typecheck" (Contributing.md); that is a
compile-time device and should be said once.  For readers: (a) merge `LebesgueDyadicNat` (67 lines of ℕ arithmetic) into `LebesgueDyadicAlg`;
(b) merge `LebesgueShiftCut` into `LebesgueShiftAlg`; (c) merge `TopMulPos` into `InfAlg`; (d) keep the rest but state in each header
which public module it serves (some do not).  Net: 4 fewer modules without compile-time risk, since the merged files are all `Alg`-class.

### 4.5 Smaller items

- `UniquenessRQ.agda:122-137`: `inf-sp`, `inf-ptL`, `inf-ptR`, `inf-cL`, `inf-cR` — five lemmas for left and right versions
  of the same statement.  Parameterise by `Side` or use a symmetry `lebR-sym`-style reflection (`RealScale`'s reflection) to halve it.
- `UniquenessRQ.agda:77,86,96`: `pt` proofs repeat `copairH g zeroW` / `copairH zeroW g`; define `onL g = copairH g zeroW`, `onR g = copairH zeroW g`.
- `ChangeOfVariablesFn` (70 lines) is a re-packaging of `cov` to take Φ,Ψ,k as functions; fine, but nothing in the repo imports it
  (check: grep `ChangeOfVariablesFn` in `src/`), in which case it is a demonstration and could be marked as such or merged into `ChangeOfVariables` as a final submodule.
- `Dominated.agda:41-51`: `inc-add`, `liminf-inc`, `limsup-inc` are lemmas about `liminfC`/`limsupC` of increasing sequences of cuts, not integrals; they belong to
  the module defining `liminfC` (`Analysis.Unbounded*`/`Series*`; lower-reals domain).
- `Fatou.agda:97-100` (`min-sup′`, `sup-min`: `c = ⊔ₙ c ⊓ n`) are cone facts; move beside `LowerRealsMin` (lower-reals).
- `RealShift.agda:108-120` `flg`, `flg-0`, `flg-1`, `flg-big`: encode a decision as a numeral in order to use a `Partition` of ℕ-valued
  functions; the choice of `ℕ` flag over `Bool ⊎` is idiosyncratic; document or replace with `Partition` on `Bool` if one exists (`Analysis/Pieces`).

## 5. Categorical language

- **Change of variables as pushforward functoriality.**  Current: `ChangeOfVariables.agda:7-9` proves `mapM ψ lebPre ≈ reweightPre φ′ lebPre`
  (`push-eq`) and then restates it as two integral identities `cov`, `cov-inv`.  The integral identities are the change-of-variables formula for
  `mapM` (`∫ᴹ-map : ∫ (mapM f p) h ≈ ∫ p (h ∘ f)`), so `cov` is `∫ᴹ-map` + `push-eq`.  The better headline is *push-eq itself*: "the
  pushforward of Lebesgue measure along ψ is Lebesgue measure with density φ′".  State that in the header and Interface.md, and
  show the two integral forms as corollaries.  Likewise, scale/shift: `mapM (shiftH t) lebPre ≈ lebPre`.  Cost: documentation only; the proofs are already organised so.
- **Stating invariance via `mapM`'s functoriality.**  `mapM` is a functor on `Pre` (strictness is `∫ᴹ-map`); `lebR` invariance under the group of
  affine maps could be given as "`lebR` is a fixed point of `mapM (affine a b)` weighted by `|a|`".  A group action formulation would
  collapse `RealShift`+`RealScale` (292 lines) only if `RQArith`'s affine maps are made a type (`Aff1` with composition); the
  existing `RQArith` (398 lines) already has the composition `idT` laws.  Worth doing together with section 4.3, not alone.
- **Convergence.**  The convergence theorems are about the *integral functional* `∫ᴹ p : Hom X WQ → [0,∞]` being (i) monotone, (ii) sup-continuous
  (`mct`), (iii) Fatou.  They are properties of a **monotone continuous functional on the ω-cpo of tests**, not of Lebesgue measure.  The `IntegralMonad`
  interface (abstract domain) is the natural place: state `mct`, `fatou`, `dct` for any `IsIntegral` model once, and instantiate for `Continuous`.
  Evidence this would help: `Dominated.dct` uses only `∫ᴹ-monoX`, `fatou`, `rev-fatou`, `liminfH-pt`, `limsupH-pt`.  Cost: moves 600+ lines
  to the abstract layer, adds a parameter to every user; the discrete model (Σ over a set) would then get convergence for free.  Raise with the abstract-domain
  auditor; the cheaper step is 4.2.
- **Coproduct on ℝ.**  `RQ = WQ +Q WQ` with `copairH`, `inlH`, `inrH`, `restrL`, `restrR` (UniquenessRQ:56-100) is a categorical coproduct; use the
  `Coproduct` universal property from `Category.Cartesian`/`Limits` for `[f,0]`/`[0,g]` uniqueness (`pt` lemmas at 77, 86, 96 are `inject₁/inject₂`
  and `unique`).  agda-categories: `Categories.Object.Coproduct` (`inject₁`, `inject₂`, `unique`, `g-η`).  Worth doing for `UniquenessRQ`'s
  `pt` lemmas only if `QBSCat` already provides `Coproduct` instances for `+Q` (check `Colimits`); otherwise bespoke is simpler.
- **Not worth it:** monad/Kleisli phrasing of `LebesgueShift` (the `fam` construction at LebesgueShift:66 is an explicit s-finite decomposition,
  and the Kleisli composition would add universe-level and setoid overhead for no shorter proof).

## 6. Open questions

1. Is `ChangeOfVariablesFn` used anywhere in `src/`?  If not, should it be an example under `Example/` rather than a library module?
2. Is `EConv`/`ConvEps` used outside `DominatedSigned`?  If not, inline (4.2).
3. Would you accept renames (`UniquenessR → UniquenessCantor`, `RQArith → RealAffine`, `NullInf → IntegrableFinite`)?  Dependents are inside `Continuous/` and `Inference/`; I did not count them.
4. Should the convergence theorems move to the abstract `IntegralMonad` layer (section 5) so the discrete model inherits them?
5. Is `leb-unique` meant to be the public characterisation of Lebesgue measure (then add the `χInf` clause, 4.3), or an internal step?
6. Does the library want a single-variable change of variables for decreasing maps (reflection exists in `RealScale`; no `cov` for decreasing φ) and for non-surjective φ?  The domain's title promises "change of variables" but only the increasing bijection on `[0,∞]` is proved; say so in the header.
