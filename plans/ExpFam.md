# Plan: Exponential-Family Distributions, Sufficiency, PAIRS, and Density Approximation

## Goal

Extend `qbs` with the theory of **exponential families**, **sufficient statistics**, the **PAIRS theorem** (extrapolating amortized inference from pairs to arbitrary set sizes via Cauchy functional equations), and **Barron–Sheu density approximation** (exponential sieves and relative entropy bounds).

---

## 1. Literature & Theoretical Foundation

This plan synthesizes two foundational lines of research:

### 1.1 Manuscripts in `lit/`

1. **Antoine Wehenkel, Michael Kagan, Lukas Heinrich, and Chris Pollard (2026)**
   *It Just Takes Two: Scaling Amortized Inference to Large Sets*
   arXiv:2605.07972 [cs.LG]
   Stored in: `lit/wehenkel2026pairs.pdf` (source in `lit/wehenkel2026pairs_src/`, text in `lit/wehenkel2026pairs.txt`).

2. **Andrew R. Barron and Chyong-Hwa Sheu (1991)**
   *Approximation of Density Functions by Sequences of Exponential Families*
   *The Annals of Statistics*, 19(3):1347–1369. DOI: 10.1214/aos/1176348252.
   Summary and mathematical notes stored in: `lit/barron_sheu1991.md`.

---

### 1.2 Theoretical Synthesis

In modern amortized Bayesian inference (such as Neural Posterior Estimation, NPE), observation sets $X_N = \{x_1, \dots, x_N\}$ often share latent parameters $\theta$ (and shared nuisance factors $\psi$). Deep Set architectures aggregate observations via permutation-invariant mean pooling:
$$M_t(X_N) = \frac{1}{N} \sum_{i=1}^N t(x_i).$$

The theoretical foundations of this architecture rest on exponential families through two complementary mechanisms:

```
     Arbitrary Smooth Likelihood / Prior p(X | θ)
                         │
                         │  Barron & Sheu (1991)
                         │  Exponential family sieve: D_KL(f ‖ f_k) ≤ O(k^{−2r})
                         ▼
     k-dimensional Exponential Family
     p(x | θ) = h(x) exp(⟨η(θ), T(x)⟩ − A(θ))
                         │
                         │  Fisher–Neyman Factorization:
                         │  p(X_N | θ) factorizes through (1/N) ∑_{i=1}^N T(x_i)
                         ▼
     Mean-Pool Representation Learning: PAIRS (Wehenkel et al. 2026)
     • Cauchy functional equation on pairs {1, 2} forces t*(x) = A t_ω(x) + b
     • Training on N ∈ {1, 2} guarantees sufficiency for all N ≥ 1
```

* **PAIRS (Theorem 1 & Corollaries 2–3)**:
  1. *Sufficiency on Pairs Extrapolates to All $N$ (Theorem 1)*: Under mild regularity, if an embedder $t_\omega$ is sufficient for $\theta$ at $N=1$ ($t^\star = g \circ t_\omega$) and its mean pool is sufficient at $N=2$, the aggregation map satisfies Cauchy's additive functional equation:
     $$g(y_1) + g(y_2) = \tilde{h}(y_1 + y_2) \implies g(y) = A y + b.$$
     Consequently, the mean pool $(M_{t_\omega}(X_N), N)$ is sufficient for *every* cardinality $N \ge 1$.
  2. *Characterization by Exponential Families (Corollary 2)*: By the Koopman–Pitman–Darmois (KPD) theorem, admitting a fixed finite-dimensional mean-pool sufficient statistic at every $N \ge 1$ holds *if and only if* the marginal likelihood factorizes as an exponential family with canonical statistic $t^\star(x)$.
  3. *Cardinality Invariance (Corollary 3)*: Training on $\{1, M\}$ for any $M \ge 2$ recovers the exact same affine equivalence class.

* **Barron & Sheu (1991)**:
  * Why does mean pooling succeed even when the underlying process is not strictly in the exponential family? Barron & Sheu prove that sequences of exponential families $f_k(x; \theta) = \exp(\sum_{j=1}^k \theta_j \phi_j(x) - \psi_k(\theta))$ (with polynomial, trigonometric, or spline bases) form a universal approximation sieve for densities whose log-density is smooth ($H^r$).
  * The approximation error in Kullback–Leibler divergence drops as $\mathcal{O}(k^{-2r})$. Thus, increasing the embedding dimension $l$ enables the mean-pool representation to approximate arbitrary complex posteriors.

---

## 2. Existing Foundations in `qbs`

The repository already provides core components that this plan builds on:

1. **Discrete Sufficiency & Bayesian Updating** ([`src/QBS/Inference/Bayesian.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Inference/Bayesian.agda)):
   * Sequential Bayes updating: `sequential`, `evidence-sequential`, `predictive-chain`.
   * Bernoulli model: `likSeq-counts : (likSeq xs θ ⟨$⟩ θ) ≈ p^(successes xs) * q^(failures xs)`.
   * This is the 1D discrete exponential family instance.

2. **Algebra of Sample Statistics & Unbiasedness** ([`src/QBS/Analysis/Estimator.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Analysis/Estimator.agda), [`src/QBS/Inference/Frequentist.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Inference/Frequentist.agda)):
   * Formal term algebra for sample statistics (`sumT`, `sqT`).
   * Evaluator in any commutative ring using `Algebra.Solver.Ring.NaturalCoefficients.Default`.
   * Unbiasedness of sample mean $\frac{1}{n} \sum X_i$ and sample variance $s^2$.

3. **Affine Transformations** ([`src/QBS/Analysis/AffineAlg.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Analysis/AffineAlg.agda)):
   * Algebraic identities for affine shifts and scales: `mean-aff`, `var-aff`, `var-core`.

4. **Information Quantities** ([`src/QBS/Continuous/KLDiv.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Continuous/KLDiv.agda), [`src/QBS/Continuous/Entropy.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Continuous/Entropy.agda), [`src/QBS/Continuous/InfoProduct.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Continuous/InfoProduct.agda)):
   * Relative entropy $D_{\mathrm{KL}}(p \cdot Q \parallel Q)$ via `Ex∞`.
   * Gibbs' inequality: `KL-nonneg`.
   * Additivity over independent product measures: `KL-⊗`, `Ent-⊗`.

5. **Parametric Continuous Distributions**:
   * Exponential distribution ([`Continuous/ExpDist.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Continuous/ExpDist.agda), [`Inference/ExpRateDist.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Inference/ExpRateDist.agda)): $\text{Exp}(\lambda)$ with all moments $n! / \lambda^{n+1}$.
   * Gaussian distribution ([`Inference/GaussReal.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Inference/GaussReal.agda), [`Inference/GaussVar.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Inference/GaussVar.agda)): $\mathcal{N}(\mu, \sigma^2)$ with mean and variance.
   * Beta–Binomial conjugacy ([`Continuous/BetaIntegral.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Continuous/BetaIntegral.agda), [`Inference/CoinPosterior.agda`](file:///Users/cspollard/Programming/qbs/src/QBS/Inference/CoinPosterior.agda)).

---

## 3. Results to Add

The additions are structured into four progressive phases:

### Phase 1: The General Exponential Family in `qbs`
* **Goal**: Define exponential families abstractly (both over discrete semirings and continuous s-finite measures), prove Fisher–Neyman factorization over i.i.d. draws, and establish general conjugate updating.
* **Modules**:
  * `src/QBS/Analysis/ExpFamAlg.agda`
  * `src/QBS/Inference/ExpFamily.agda`
  * `src/QBS/Continuous/ExpFamily.agda`
* **Key Results**:
  1. Record `ExponentialFamily` containing:
     * Sample space $X$, parameter space $\Theta$.
     * Base measure $h$ on $X$.
     * Sufficient statistic vector $T : X \to \mathbb{R}^k$ and natural parameter $\eta : \Theta \to \mathbb{R}^k$.
     * Log-partition function $A : \Theta \to \mathbb{R}$ with normalisation $\int \exp(\langle \eta(\theta), T(x) \rangle - A(\theta)) h(dx) = 1$.
  2. `product-expFam`: For $N$ independent draws on $X^N$, the joint distribution is an exponential family with canonical statistic $T^{(N)}(X_N) = \sum_{i=1}^N T(x_i)$, base measure $\prod_{i=1}^N h(x_i)$, and log-partition $N \cdot A(\theta)$.
  3. `conjugate-update`: For a natural conjugate prior $p(\theta \mid \chi_0, \nu_0) \propto \exp(\langle \eta(\theta), \chi_0 \rangle - \nu_0 A(\theta))$, the posterior after observing $X_N$ is conjugate with updated parameters:
     $$\chi_{post} = \chi_0 + \sum_{i=1}^N T(x_i), \qquad \nu_{post} = \nu_0 + N.$$
  4. Instances: Bernoulli (generalizing `Inference/Bayesian.agda`), Exponential ($\lambda$), and Gaussian ($\mu$).

---

### Phase 2: Information Geometry & Relative Entropy
* **Goal**: Relate exponential families to the information quantities in `Continuous/KLDiv.agda`.
* **Modules**:
  * `src/QBS/Continuous/ExpFamilyKL.agda`
* **Key Results**:
  1. `KL-expFam`: The Kullback–Leibler divergence between two distributions in the same exponential family is the Bregman divergence generated by $A$:
     $$D_{\mathrm{KL}}(P_{\eta_1} \parallel P_{\eta_2}) = A(\eta_2) - A(\eta_1) - \langle \eta_2 - \eta_1, \mathbb{E}_{\eta_1}[T(X)] \rangle.$$
  2. `convex-A`: By Gibbs' inequality (`KL-nonneg`), $A$ is strictly convex:
     $$A(\eta_2) \ge A(\eta_1) + \langle \eta_2 - \eta_1, \mathbb{E}_{\eta_1}[T(X)] \rangle.$$
  3. `pythagorean-expFam`: For an exponential subfamily, the Pythagorean identity for relative entropy:
     $$D_{\mathrm{KL}}(P \parallel Q) = D_{\mathrm{KL}}(P \parallel P^\star) + D_{\mathrm{KL}}(P^\star \parallel Q),$$
     where $P^\star$ is the information projection.

---

### Phase 3: The PAIRS Theorem and Cauchy Functional Equations
* **Goal**: Formalize the mathematical engine of the PAIRS algorithm (Wehenkel et al. 2026).
* **Modules**:
  * `src/QBS/Analysis/CauchyAlg.agda`
  * `src/QBS/Inference/PairsTheorem.agda`
* **Key Results**:
  1. `cauchy-reduction`: From the functional equation $g(y_1) + g(y_2) = \tilde{h}(y_1 + y_2)$ on an open neighborhood:
     * Setting $y_2 = 0$ gives $\tilde{h}(y) = g(y) + g(0)$.
     * The centered map $\bar{g}(u) = g(u) - g(0)$ satisfies the Cauchy additive equation $\bar{g}(u_1 + u_2) = \bar{g}(u_1) + \bar{g}(u_2)$.
  2. `cauchy-affine`: Additive continuous (or monotonic/Lipschitz) maps on $\mathbb{R}^k$ are linear ($\bar{g}(u) = A u$), so $g(y) = A y + b$ is affine.
  3. `pairs-theorem` (Theorem 1 formalization):
     * Given an embedder $t_\omega : X \to \mathbb{R}^l$ that is sufficient at $N=1$ for a target minimal sufficient statistic $t^\star$ ($t^\star = g \circ t_\omega$).
     * Given that the mean-pool statistic $\frac{1}{2}(t_\omega(x_1) + t_\omega(x_2))$ is sufficient at $N=2$.
     * Then $g$ satisfies the additive functional equation and is affine: $t^\star(x) = A t_\omega(x) + b$.
     * Consequently, the mean pool $(M_{t_\omega}(X_N), N)$ is sufficient for $\theta$ at *every* cardinality $N \ge 1$.
  4. `cardinality-invariance` (Corollary 3 formalization):
     * Training at $\{1, M\}$ for any $M \ge 2$ recovers embedders in the same affine equivalence class.

---

### Phase 4: Barron–Sheu Sieve and Polynomial Log-Densities
* **Goal**: Formalize exponential sieves and moment matching over compact domains.
* **Modules**:
  * `src/QBS/Continuous/ExpSieve.agda`
* **Key Results**:
  1. `poly-expFam`: Over $[0, 1]$, the polynomial exponential family with canonical statistics $T_k(x) = (x, x^2, \dots, x^k)$.
  2. `moment-matching-opt`: Minimizing $D_{\mathrm{KL}}(f \parallel f_k(\cdot; \theta))$ equates model moments to true moments:
     $$\mathbb{E}_{\theta^\star}[X^j] = \mathbb{E}_f[X^j], \quad j = 1, \dots, k.$$
  3. Theoretical link to PAIRS: a $k$-dimensional mean-pool embedder tracks empirical moments, which by Barron & Sheu approximate the true posterior at rate $\mathcal{O}(k^{-2r})$.

---

## 4. Staging and Module Map

```
  Analysis/
    CauchyAlg.agda          -- Cauchy functional equation and affine reduction
    ExpFamAlg.agda          -- Ring algebra of exponential factorization & statistics
       │
       ▼
  Continuous/
    ExpFamily.agda          -- Exponential family over s-finite measures
    ExpFamilyKL.agda        -- Bregman divergence, convexity of A, Pythagorean identity
    ExpSieve.agda           -- Polynomial log-density sieve and moment matching
       │
       ▼
  Inference/
    ExpFamily.agda          -- Conjugate prior updating & likelihood factorization
    PairsTheorem.agda       -- "It Just Takes Two": pair training implies arbitrary-N sufficiency
```

### Detailed Staging:

| Stage | Target Module | Dependencies | What it does | Hypotheses |
|---|---|---|---|---|
| **1a** | `Analysis/ExpFamAlg.agda` | `Algebra.Bundles`, `Algebra.Solver.Ring` | Abstract algebra of additive sufficient statistics and log-partition sums $N \cdot A$. | None (constructive) |
| **1b** | `Inference/ExpFamily.agda` | `ExpFamAlg`, `Inference/Bayesian` | Discrete exponential family, product factorization $T^{(N)}$, conjugate updating rule. | None |
| **1c** | `Continuous/ExpFamily.agda` | `Continuous/SFiniteReweight`, `Continuous/ExpDist`, `Inference/GaussReal` | Continuous exponential family, normalizer integral, Exp and Gauss instances. | `lem₁` |
| **2**  | `Continuous/ExpFamilyKL.agda` | `Continuous/KLDiv`, `Continuous/InfoProduct`, `Continuous/ExpFamily` | Bregman divergence form of KL, convexity of $A$, Pythagorean identity. | `lem₁` |
| **3a** | `Analysis/CauchyAlg.agda` | `Algebra.Bundles`, `Analysis/AffineAlg` | Elimination of $\tilde{h}$, reduction to Cauchy's additive equation, affine solutions. | None |
| **3b** | `Inference/PairsTheorem.agda` | `Analysis/CauchyAlg`, `Inference/ExpFamily` | Theorem 1 and Corollary 3 of PAIRS: sufficiency on $\{1, 2\}$ implies sufficiency for all $N$. | None |
| **4**  | `Continuous/ExpSieve.agda` | `Continuous/BetaIntegral`, `Continuous/PolyTest`, `Continuous/ExpFamilyKL` | Polynomial exponential family on $[0,1]$ and moment-matching stationarity. | `lem₁` |

---

## 5. Architectural & Performance Guardrails

From the performance and design history of `qbs` (`docs/Architecture.md` and `docs/History.md`):

1. **Avoid Unfolding Lower Cuts**:
   * State all algebraic identities in `Analysis/CauchyAlg.agda` and `Analysis/ExpFamAlg.agda` over abstract commutative rings using `Algebra.Solver.Ring.NaturalCoefficients.Default`.
   * Unfolding concrete cut operations in the goal type previously degraded check times by orders of magnitude; keep them abstract and connect via bridge lemmas.

2. **Declaration Budget**:
   * All declarations must pass `make longcheck` (fewer than 25 lines, 1500 characters, 160 columns).
   * Break multi-step derivations (such as the Cauchy centering and elimination of $\tilde{h}$) into named helper lemmas with explicit signatures.

3. **Constructive Foundations**:
   * Keep `Analysis/CauchyAlg.agda`, `Analysis/ExpFamAlg.agda`, and `Inference/PairsTheorem.agda` purely constructive (no `lem` / `lem₁`).
   * Confine `lem₁` strictly to modules requiring continuous measure integration (`Continuous/ExpFamily`, `Continuous/ExpFamilyKL`, `Continuous/ExpSieve`).

4. **Safety & Verification**:
   * Maintain `--safe --without-K` and zero postulates.
   * Verify each addition incrementally using `make progress`, `make check`, and `make doccheck`.

