# Uniqueness of measures on the half-line: literature and route

**Why this file exists.** The library needs to know that two measures on `WQ = [0,∞]` are equal when they agree on
intervals. That one fact gives Lebesgue measure its scaling and shifting laws and drives every change of variables.
This note records the classical proof, and how the library follows it. The proof was first a plan; it is now
implemented (plan 03, "Uniqueness on the half-line", done 2026-11-03). `docs/ConstructiveLit.md` covers
constructive alternatives (valuations, locales), which this note does not.

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
   The certificate calculus (`Analysis/Deriv*`, `Continuous/DerivBridge`) supplies the FTC step.
5. **QBS side.** In HKSS (Heunen–Kammar–Staton–Yang, LICS 2017) the functor from standard Borel spaces to QBS is
   full and faithful. So for ℝ, or [0,∞], the QBS morphisms into the weights are exactly the Borel functions, and
   "agree on Borel sets" means "agree on every test". The concrete form of the proof is a **Borel isomorphism with
   Cantor space**: a test h on X becomes the test h∘e on Cantor space, where e∘d = id.

## The route in this library

The library has no σ-algebra on `WQ`: a test `h : Hom S WQ WQ` is known to be measurable only after precomposing
with a probe (`Meas (h ∘ α)`). Uniqueness is therefore proved on Cantor space first (`Analysis/Uniqueness`, via
`Borel/PiLambda`, classical `lem`), and transported to `WQ` along a digit code. Point 5 is the bridge.

* **Code and decode** (`Continuous/DigitCode`, engine in `DigitStream`, `DigitDecode`, `Analysis/DigitAlg`).
  * The code `code : Hom S WQ ℛ` sends x to the unary integer part (`true^⌊x⌋ false`, matching `Borel/Lead`),
    followed by the binary digits of the fractional part. It sends ∞ to the all-`true` sequence.
  * `code` is a morphism because each output bit, as a function of a probe α, is a finite Boolean combination of
    the sets {ω | α ω ≥ q}, q dyadic. Each such set is Borel (`Continuous/Intervals.ge-borel`). Deciding the digits
    needs excluded middle.
  * The decode `decode : Hom S ℛ WQ` satisfies `decode (code x) ≈ x` (`decode-code`).
  * Then every test h equals `(h ∘ decode) ∘ code`, and `∫ᴹ μ h ≈ ∫ᴹ (mapM code μ) (h ∘ decode)`.
* **Cantor space, σ-finite form** (`Continuous/UniquenessCantor`, `Borel/Cells`, `Analysis/UniquenessWeighted`).
  Cantor space is the disjoint union of the blocks `{trueᵏ false …}` and the all-true point. Measures that agree on
  every cell, have finite mass on each block and agree on the all-true point are equal (`uniqR`). This is (2) above.
* **Half-line** (`Continuous/UniquenessWQ`, `uniqWQ`). Under `code`, the cell `{lead = k} ∩ {fractional prefix = c}`
  with c a word of length n is the dyadic interval [k + c/2ⁿ, k + (c+1)/2ⁿ). So two measures on `WQ` that agree on
  dyadic intervals and on {∞}, and are finite on each [k, k+1), are equal.
* **Lebesgue measure** (`Continuous/LebesgueDyadic`, `LebesgueInterval`, `LebesgueScale`, `LebesgueShift`). The fair
  coin gives `fair{expansion ∈ [c/2ⁿ, (c+1)/2ⁿ)} = 2^{-n}`, by induction on n using the first-bit split
  (`Continuous/FirstBit`) and self-similarity (`Analysis/ExpansionCons`: expansion (b ∷ r) = b/2 + expansion r / 2).
  An affine bijection maps half-open intervals exactly onto half-open intervals, so the induction step has no null
  sets. The only null set is the base case, fair{all-true} = 0. The interval masses then characterise Lebesgue
  measure (`leb-unique`), and scaling and translation follow as in (3).

## What this replaced

* A digit-transducer estimate of at least 1500 lines, which would have re-proved uniqueness separately for each
  scaling. With the route above each change of variables (`Continuous/ChangeOfVariables`) is a check on intervals.
* Particular-density theorems: two densities with the same interval masses are equal as measures, and every family
  that is a monotone pushforward gets its density by (4).

## Sources

Billingsley and Kallenberg are textbook references and are not in the repository. The HKSS paper is in `lit/`
(a local folder that the repository does not track; index in `lit/README.md`). The proofs in the library follow
the outline above, not the books' text.
