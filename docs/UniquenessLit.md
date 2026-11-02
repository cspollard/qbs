# Uniqueness of measures on the half-line: literature and route

Status: planning note (2026-11-02). It records the classical route to "measures that agree on intervals agree on every
test", for `WQ = [0,∞]`, and how that route maps onto what the library already has. `docs/ConstructiveLit.md` covers
constructive alternatives (valuations, locales), but it does not cover this result.

## Classical statements

1. **π–λ uniqueness, finite case.** Let μ and ν be finite measures on (Ω, σ(P)), where the class P is closed under
   finite intersection. If μ and ν agree on P, and Ω is a countable union of sets in P, then μ = ν.
   Sources: Billingsley, *Probability and Measure*, Thm 3.3; Kallenberg, *Foundations of Modern Probability*,
   Lemma 1.17.
2. **σ-finite case.** Suppose Ω = ⋃ₖ Bₖ with Bₖ ∈ P disjoint, μ(Bₖ) = ν(Bₖ) < ∞, and μ and ν agree on {C ∩ Bₖ}.
   Then μ = ν: apply (1) to each restriction μ(· ∩ Bₖ) and sum (Billingsley Thm 10.3).
3. **Lebesgue measure.** Lebesgue measure on ℝ is the unique measure with λ[a,b) = b − a. The half-open dyadic
   intervals form a π-system that generates the Borel sets, and ℝ is the disjoint union of the intervals [k,k+1),
   each of finite mass. Translation invariance and the scaling law λ(cA) = c·λ(A) follow at once: both sides are
   measures that agree on intervals (Billingsley §12).
4. **Change of variables.** For φ increasing and C¹, the pushforward of the density ρ under φ has density
   ρ(φ⁻¹y)/φ′(φ⁻¹y). Proof: both sides give the same mass to every interval [φ(a), φ(b)) (FTC). Then apply (2).
   This is the step that the certificate calculus (`Analysis/Deriv*`, `Continuous/DerivBridge`) can feed.
5. **QBS side.** In HKSS (Heunen–Kammar–Staton–Yang, LICS 2017, `lit/hkss-quasi-borel-spaces.pdf`) the functor
   from standard Borel spaces to QBS is full and faithful. So for ℝ, or [0,∞], the QBS morphisms into the weights are
   exactly the Borel functions, and "agree on Borel sets" means "agree on every test". The concrete form of that
   proof is a **Borel isomorphism with Cantor space** (or with ℝ). A test h on X becomes the test h∘e on Cantor
   space, where e∘d = id.

## The route in this library

The library has uniqueness on Cantor space only (`Analysis/Uniqueness`, via `Borel/PiLambda`, which is classical
`lem`). It has no σ-algebra on `WQ`: a test `h : Hom S WQ WQ` is known to be measurable only after precomposing with a
probe (`Meas (h ∘ α)`). Point 5 is therefore the bridge.

* **Code and decode.**
  * The code d : WQ → ℛQ is a QBS morphism. It sends x to the unary integer part (`true^⌊x⌋ false`, matching
    `Borel/Lead`), followed by the binary digits of the fractional part. It sends ∞ to the all-`true` sequence.
  * d is a morphism because each output bit, as a function of a probe α, is a finite Boolean combination of the
    sets {ω | α ω ≥ q}, q dyadic. Each such set is a countable intersection of threshold sets {q′ ∈ α ω}, so it is
    Borel. Deciding the digits needs `LEM₁`.
  * The decode e : ℛQ → WQ satisfies e (d x) ≈ x. e is a probe of `WQ`, being a `Meas` function built from
    `lead` and `expansion`.
  * Then for every test h, `h ≈ (h ∘ e) ∘ d` pointwise, and `∫ᴹ μ h ≈ ∫ᴹ (mapPre d μ) (h ∘ e)`.
* **Preimages of cylinders are intervals.** The cylinder `{lead = k} ∩ {fractional prefix = c}`, with c a word of
  length n, pulls back under d to the dyadic interval [k + c/2ⁿ, k + (c+1)/2ⁿ). So uniqueness on `WQ` becomes
  uniqueness on Cantor space, in the σ-finite form (2), along the partition by `lead`.
* **Lebesgue measure on dyadic intervals.** We need `fair{expansion ∈ [c/2ⁿ, (c+1)/2ⁿ)} = 2^{-n}`. This follows by
  induction on n, using the first-bit split (`Continuous/FirstBit`) and self-similarity (`Analysis/ExpansionCons`:
  expansion (b ∷ r) = b/2 + expansion r / 2). An affine bijection maps half-open intervals exactly onto half-open
  intervals, so the induction step has no null sets. The only null set is the base case,
  fair{all-true} = 0, since this is ≤ 2^{-n} for every n.

## What this replaces

* The digit-transducer estimate (≥ 1500 lines) in plan 03, "Change of variables, general c". That estimate
  re-proved uniqueness separately for each scaling. With the route above, each change of variables is a check on
  intervals (point 4).
* Particular-density theorems: two densities with the same interval masses are equal as measures, and every family
  that is a monotone pushforward gets its density by (4).
