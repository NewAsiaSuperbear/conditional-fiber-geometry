# Conditional Fiber Geometry Lean Formalization

Date: 2026-09-07

Branch: `formal/cfg-core-v1`

Upstream baseline: `77e2203e6d5df42b457823eebe6626f1b1c3ded1` (`v0.3.0`)

## Scope

This report records the verified Lean formalization under `formal/`. The planning specification is stored under `formal/specs/`, and [`CFG.lean`](../CFG.lean) is the production import root.

The production tree contains no `sorry`, `admit`, project-level `axiom`, or `opaque` placeholders. Incomplete targets remain documented in the status ledgers and are not imported as unproved declarations.

Current size:

- 46 Lean source files;
- 6,269 lines under `CFG/**/*.lean`;
- approximately 287 top-level declarations;
- a successful full build comprising 8,928 jobs.

## Reproducible Environment

- Lean: `leanprover/lean4:v4.34.0-rc2`
- mathlib: `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`
- Lake options: `autoImplicit = false`, `warningAsError = true`

Verification commands:

```bash
cd formal
lake build
python3 -m json.tool PROOF_STATUS.json >/dev/null
rg -n '^\s*(axiom|opaque)\b|\b(sorry|admit)\b' CFG CFG.lean
```

The final full build succeeded. The placeholder scan returned no matches. The declarations audited in `CFG/Audit/AxiomAudit.lean` depend only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project-defined research axiom is present.

## Verified Results

### Fibers, rank, and covering

- Defined the observed map as the genuine composition `H = P ∘ F`, together with parameter fibers and image fibers.
- Proved fiber disjointness, closedness, compactness, and compactness of continuous image fibers.
- Proved the restricted-image rank decomposition for genuine linear maps and the derivative chain rule for the observed map.
- Constructed finite-dimensional integer grids, finite-union covering bounds, Lipschitz image bounds, and qualitative finite covers of compact sets.
- Constructed local projected implicit charts from strict Fréchet derivatives and rank lower bounds.
- Aggregated the local charts into a finite image-fiber atlas with a common target radius and explicit degree-`d-r` inverse-power and logarithmic covering certificates.
- Proved finiteness of compact fibers in the full-domain-rank branch.

The full constant-rank manifold theorem and the M04 restricted-image-rank refinement are not claimed.

### Conditional distributions and masks

- Used mathlib's genuine conditional-distribution and conditional-kernel APIs to prove almost-sure concentration on the corresponding parameter fiber.
- Pushed conditional laws through a continuous complete-data map to obtain support containment in compact image fibers.
- Covered arbitrary dependent parameter-mask laws.
- Constructed measurable tagged observations and fiber relations for countable mask families with varying observation dimensions.

All conditional conclusions are stated almost everywhere with respect to the actual observation pushforward law. No independence assumption or pointwise conclusion at null observations is introduced.

### Spectral tubes, pseudoinverses, and certificates

- Constructed an anisotropic live/kernel grid for the explicit diagonal spectral tube and proved the exact ceiling-product covering bound.
- Constructed the canonical right inverse `B*(BB*)⁻¹` for surjective continuous linear maps.
- Proved its right-inverse, minimum-norm, orthogonal-projection, and operator-norm properties.
- Differentiated the pseudoinverse family and proved the formula `-AEA + (I-AB)E†A†A`.
- Derived the bounds `2‖E‖s⁻²` and the corresponding chain-ready Lipschitz estimate from a lower singular inequality on the orthogonal complement of the kernel.
- Converted approximate right inverses, finite Frobenius-square bounds, and closed-ball derivative-error estimates into genuine surjectivity and right-inverse certificates via a Neumann-series construction.

General SVD-frame transport, SPD whitening, and certificates from actual FEM data remain open.

### Measure transport and smoothing

- Proved the sharp half-`L¹`/hyperbolic-tangent bound for normalized densities with exponential ratio control.
- Connected this result to genuine `withDensity` probability measures.
- Proved that the event `{f ≥ 1}` attains the half-`L¹` deviation and that the supremum over measurable event deviations equals it.
- Proved one-dimensional and finite-dimensional `L¹` translation bounds for Banach-valued kernels using Fréchet derivatives, interval integration, Fubini, and translation invariance.
- Proved a finite-coupling kernel-mixture bound controlled by expected displacement cost.

The optimal-coupling/Wasserstein wrapper, geometric weight path, and explicit finite-dimensional Gaussian constants remain open.

### Projection, MMSE, discrete CEM, and statistics

- Proved compatible affine orthogonal projection is non-expansive relative to the truth.
- Proved that the square-root-two weighted upper-triangular coordinates of a symmetric matrix are exactly Frobenius-isometric.
- Proved that safe background normalization preserves the weighted zero-row-sum constraint.
- Proved posterior precision/covariance inverse identities and symmetry.
- Used the genuine `condExpL2` Hilbert projection to prove the Pythagorean risk decomposition and minimum-risk property.
- Proved symmetry, energy positivity, gauge-kernel, and zero-row-sum properties of the discrete Schur response under explicit block-matrix assumptions.
- Proved the exact V-statistic/U-statistic pair-term factor.
- Formalized the complete two-point counterexample for truth-norm-normalized energy score.
- Proved the finite-PMF exchangeability/no-ties uniform-rank theorem and the interior-rank probability `(n-1)/(n+1)`, including `15/17` for `n = 16`.
- Proved that an atomless finite iid product has exact two-coordinate marginal `μ.prod μ` and almost-surely injective coordinates.
- Proved that the finite iid product measure is invariant under every coordinate permutation.

The remaining M20 bridge is the measure-level composition from iid exchangeability and almost-sure no ties to uniformity of the finite-valued rank pushforward. The Gaussian conditional-covariance and trace-risk theorem, continuous CEM/PDE theory, FEM assembly derivation, and shape derivative remain open.

## Trust Boundary

All production declarations are checked by the pinned Lean kernel and mathlib revision. External tools may generate proof candidates, but their output is accepted only after local compilation and axiom auditing.

The formalization does not claim:

- the full M04 constant-rank and image-rank-refined geometry;
- the M07-M08 quantitative fixed-point graph and uniform covering theorem;
- the M10-M13 ODE, coarea, transport, moving-manifold, and curvature chain;
- the Gaussian smoothing and Gaussian conditioning formulas;
- continuous CEM well-posedness or shape calculus;
- correctness of external FEM matrices or numerical error estimates;
- a local proof of the external DDPM convergence theorem.

M15 currently formalizes only the exact entropy-scale substitution. M19 supplies a mathematical certificate checker, but actual numerical certification still requires immutable input data, interval bounds, truncation-error estimates, and provenance.

## Status Records

- [`THEOREM_MAP.md`](../THEOREM_MAP.md): theorem-level scope and completion state.
- [`ASSUMPTION_LEDGER.md`](../ASSUMPTION_LEDGER.md): explicit hypotheses and prohibited extrapolations.
- [`API_INVENTORY.md`](../API_INVENTORY.md): APIs verified against the pinned mathlib revision.
- [`PROOF_STATUS.json`](../PROOF_STATUS.json): machine-readable proof status.
- [`FAILURE_LOG.md`](../FAILURE_LOG.md): failed approaches and version-specific findings.
- [`BUILD_LOGS/2026-09-07_extended_formalization.md`](../BUILD_LOGS/2026-09-07_extended_formalization.md): latest full-build record.
