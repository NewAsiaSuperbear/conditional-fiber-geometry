# Public release audit

Audit date: 4 September 2026  
Release candidate: `v0.2.0-rc1`  
Audited content baseline: `566a5076146f0999fcf90db46dccfa7deea3dbdc`  
Repository visibility during this audit: private

The release-candidate tag identifies the commit containing this record. The
content baseline above is the clean root commit examined before this audit
record was added.

## Release-gate summary

| Gate | Result | Verification |
|---|---|---|
| Secret scan | Pass | Gitleaks 8.30.1 found no leaks in the release tree or clean Git history. |
| Personal-data scan | Pass | No private path, machine name, local account name, IP address, or unintended identifier was found. The author name and Git commit email are intentional public metadata. |
| Git-history scan | Pass | The public candidate has a clean root history. The superseded development history is retained only in an offline bundle outside the repository. |
| GitHub-side historical state | Pass | The obsolete release, tag, Actions runs, and release asset were removed while the repository was private. No historical Actions artifacts existed. |
| Third-party copyright | Pass | No third-party source code, figure, mesh, or dataset is redistributed. The KTC2023-derived diagnostic is scoped and attributed in `THIRD_PARTY_NOTICES.md`. |
| Repository licenses | Pass | Original software uses MIT; author-owned manuscript, documentation, figures, and numerical results use CC BY 4.0. Third-party material is not relicensed. |
| Dependency licenses | Pass | Direct software and CI dependencies are inventoried with upstream license links. Dependencies are installed, not vendored. |
| Mathematical claims | Pass | The theorem statements, assumptions, proofs, claims matrix, README, and limitations were checked for consistency. No known false release claim remains. |
| Correctness tests | Pass | All 16 pytest tests passed in both a supported clean environment and the pinned release environment. |
| Analytic examples | Pass | The deterministic toy validation completed with the expected projection, transport, critical-rank, and spectral-cover outputs. |
| Figure reproduction | Pass | The validation figure rebuilt byte-for-byte in the pinned environment; its SHA-256 manifest entry was verified. |
| Result integrity | Pass | All 20 entries in `experiments/results/SHA256SUMS` were verified. |
| Manuscript build | Pass | A forced clean LaTeX build produced a 17-page PDF with resolved citations and references and no reported box warnings. |
| PDF metadata | Pass | Metadata contain only the intended title, author, subject, keywords, and standard producers; no local path or machine identifier was found. |
| PDF visual review | Pass | Every page and the principal theorem, figure, and bibliography pages were inspected for layout damage. |
| Local links and structured files | Pass | All 17 local Markdown links resolve; JSON, workflow YAML, and CFF 1.2 metadata parse successfully. |
| External links | Pass with transition check | All non-repository public links resolved. Repository and security-reporting URLs are rechecked after visibility changes because a private repository returns HTTP 404 to anonymous clients. |
| Reproducibility scope | Pass | Self-contained and non-self-contained parts are explicitly separated in `docs/REPRODUCIBILITY.md`. |

## Mathematical dependency review

The release uses the following dependency structure.

```text
constant-rank theorem + compact chart covering
└── Theorem 3.1: compact regular-fiber entropy
    └── Corollary 3.3: random-mask conditional entropy
        └── Corollary 8.1: pointwise external DDPM consequence
            (also requires Liang--Huang--Chen v2, Assumptions 1--3
             and Theorem 2)

deterministic observation constraint
└── Proposition 3.2: random-mask conditional support
    └── Corollary 3.3

singular-value decomposition + ellipsoid covering
└── Theorem 4.1: linear full-spectrum tube
    └── Corollary 4.2: noise-whitened tube

quantitative contraction argument in singular coordinates
└── Lemma 4.3: quantitative implicit graph
    └── Theorem 4.4: local nonlinear spectral tube
        └── Corollary 4.5: uniform exact-fiber covering

Definition 5.1: bidirectional no-exit
+ Assumption 5.2: full row rank, boundary submersion, density bounds,
  derivative bounds, and convex observation paths
+ Lemma 5.3: derivative of the full-row-rank right inverse
└── Theorem 5.4: quantitative transport of neat fibers
    ├── Theorem 6.1: conditional-measure transport
    │   └── Corollary 6.2: complete-data-law Wasserstein regularity
    └── Theorem 7.1: motion and curvature of conditional image manifolds
        (also requires tangent noncollapse and fiberwise injectivity)

conditional-law Wasserstein control + Gaussian kernel estimates
└── Proposition 7.2: smoothed density and gradient-density regularity
```

The dependency review preserves the following scope restrictions:

- boundary submersion and bidirectional no-exit are assumptions, not global
  conclusions about the EIT polygon prior;
- covering estimates are upper bounds and do not assert image-dimension
  equality;
- numerical rank and finite-cloud PCA are diagnostics rather than proofs;
- Proposition 7.2 does not imply conditional-score regularity; and
- Corollary 8.1 is pointwise, version-pinned, non-uniform, and conditional on
  an external diffusion theorem.

## GitHub transition controls

Immediately after changing visibility, the maintainer must:

1. inspect the repository, commit history, Actions page, Releases page,
   license detection, citation rendering, and manuscript download as an
   unauthenticated visitor;
2. enable and verify GitHub private vulnerability reporting so that the route
   in `SECURITY.md` resolves;
3. verify the public repository description and six research topics; and
4. return the repository to private visibility if any unexpected historical
   object, private metadata, or broken security route appears.

## Known open mathematical issues

- global EIT boundary transversality and bidirectional no-exit;
- observation-uniform conditional entropy constants;
- positive uniform reach for the complete conditional image family;
- conditional-score regularity and finite-sample score estimation;
- adaptation to external diffusion-theorem versions other than the pinned
  arXiv v2 result; and
- continuum finite-element convergence for the reported discretized tests.

These are stated as open problems and are not release blockers.

## Blocking issues

None at the release-candidate gate. Publication remains conditional on the
transition controls above; failure of any transition check requires immediate
reversion to private visibility.
