# Public release audit

- Audit date: 5 September 2026
- Candidate: `v0.3.0` pre-tag working tree
- Audited baseline: `783d3837e182a9d462db332cd029c1b97382ce79`
- Remote default branch at audit time: the same baseline on public `main`

This record audits the complete intended candidate, including modified and
previously untracked files, before its release commit is created. No `v0.3.0`
tag, GitHub release, or push was made as part of this audit. The existing
`v0.2.0` tag and release remain unchanged.

## Release-gate summary

| Gate | Result | Verification |
|---|---|---|
| Secret scan | Pass | The official Gitleaks 8.30.1 Linux archive was checked against its published SHA-256 (`551f6fc83ea457d62a0d98237cbad105af8d557003051f41f3e7ca7b3f2470eb`). `gitleaks git` scanned both historical commits and `gitleaks dir` scanned the candidate tree with no leaks. Independent pattern scans also covered binary strings and archive string arrays. |
| Personal-data scan | Pass | No private absolute path, local account name, machine name, IP address, unintended email address, or credential pattern occurs in the candidate files, PDFs, or NPZ string arrays. The author name and the existing Git commit email are intentional public metadata. |
| Candidate inventory | Pass | The intended tree contains 74 files and 10,919,727 bytes. The largest file is 4,540,108 bytes; no file reaches 5 MB, and there are no symlinks. |
| Git-history integrity | Pass | `git fsck --full` and `git diff --check` passed. The two-commit history and its 55 historical blobs were scanned for private paths and secrets with zero findings. |
| Current GitHub state | Pass | The repository is public, unarchived, and enabled; `main` resolves to the audited baseline; GitHub detects MIT; all six intended research topics are present; private vulnerability reporting is enabled; and all four existing Actions runs completed successfully. The only GitHub release is the unchanged `v0.2.0` release. |
| Third-party copyright | Pass | No upstream KTC source, measurement data, mesh, archive, or figure is redistributed. The retained CEM entries are author-generated aggregate diagnostics and are scoped in `THIRD_PARTY_NOTICES.md`. |
| Repository licenses | Pass | Original software uses MIT. Author-owned manuscript, documentation, figures, and numerical results use CC BY 4.0. Third-party material is not relicensed. |
| Dependency licenses | Pass | Runtime, test, plotting, build, and pinned CI dependencies are inventoried with upstream license links. Dependencies are installed rather than vendored. |
| Mathematical claims | Pass | Two independent read-only reviews found no P0 mathematical or numerical blocker. The image-rank theorem, regular-tube bootstrap, `tanh` TV bound, boundary/corner scope, positive external entropy exponent, and learned-study limits are synchronized across the manuscript and scope documents. |
| Reused-experiment boundary | Pass | Acceptance accounting, the 360-Jacobian image-rank audit, per-scale saturation diagnostics, and the three-seed learned endpoint are incorporated with source hashes and explicit selection limits. Missing nonlinear-tube, horizontal-flow, coarea, rank-ablation, and noisy-posterior studies remain plans rather than results. |
| Experiment tracking | Pass | Post-hoc curation and reanalysis are recorded as MLflow experiment `conditional-fiber-geometry-release-integration`, run `623028254fa7415a969b1912449bab07`, with canonical nested artifacts and `FINISHED` status. This record is not presented as the historical training run. |
| Python correctness tests | Pass | All 34 pytest tests passed in both the project test environment and an isolated installed release environment. No test was removed or weakened. |
| Package build and install | Pass | A `0.3.0` wheel was built without dependency resolution using setuptools 80.9.0 and wheel 0.45.1, then installed and imported from a separate temporary environment. |
| Analytic examples | Pass | The deterministic toy validation completed with the expected projection, transport, critical-rank, and spectral-cover values. |
| Result integrity | Pass | All 29 entries in `experiments/results/SHA256SUMS` verify. Four NPZ files containing 48 arrays load with `allow_pickle=False`; no array has object dtype, and no ZIP member is encrypted or path-traversing. |
| Result regeneration | Pass | The image-rank summary, acceptance table, cover-scale tables, learned summary, and both public figures were regenerated from their declared public or hashed sources. The two figures reproduced byte-for-byte in the pinned plotting environment. |
| Manuscript build | Pass | LaTeX produced a 22-page PDF with all 17 bibliography entries cited, 45 labels and 53 references resolved, and no warning, undefined-reference, overfull/underfull box, or error line in the final log. |
| PDF safety and visual review | Pass | All three PDFs are readable, unencrypted, and free of attachments, JavaScript, date metadata, private paths, email addresses, IP addresses, and unresolved `??` text. Fonts in the manuscript are embedded. Pages 15--20 and both experiment figures were visually rechecked after the final edits. |
| Structured files and local links | Pass | Ten JSON files, 13 CSV files, one TOML file, and two YAML/CFF files parse successfully. All 30 local Markdown file links resolve. |
| External links | Pass | All 22 distinct public URLs returned HTTP 200 after redirects. The repository, issue tracker, security-report route, scholarly sources, licenses, and dependency pages were included. |
| Reproducibility scope | Pass | Self-contained analyses, post-hoc curation, historical experiments, omitted large artifacts, and proposed future experiments are separated in `docs/REPRODUCIBILITY.md`, `experiments/PROVENANCE.md`, and the experiment gap plan. |

## Mathematical dependency and scope review

The audited logical structure is:

```text
regular level set + compact chart covering
└── compact regular-fiber entropy (ambient exponent d - r)
    ├── constant restricted image rank
    │   └── image-fiber entropy (exponent ell = rank(DF|ker DH))
    └── deterministic random-mask support
        └── fixed-pair conditional entropy
            └── version-pinned external DDPM entropy input

SVD + ellipsoid covering
└── linear full-spectrum tube
    └── noise-whitened tube

quantitative contraction in truncated singular coordinates
└── quantitative implicit graph
    └── local nonlinear full-spectrum tube
        └── uniform exact-fiber cover on an assumed regular region

regular-tube bootstrap + ambient C1 flow
+ boundary submersion + bidirectional no-exit + coarea density bounds
└── quantitative complete-fiber transport
    ├── conditional-measure transport with TV <= tanh(C0 Delta)
    │   └── complete-data-law Wasserstein continuity
    └── C1 motion and curvature bounds for noncollapsed image manifolds

conditional-law Wasserstein control + Gaussian kernel estimates
└── smoothed density and gradient-density L1 regularity
```

The following restrictions remain mandatory:

- the image-rank exponent requires constant restricted rank on a relative
  neighborhood of the complete compact fiber; the 360 sampled Jacobians are
  only a negative pointwise diagnostic and gave no empirical improvement over
  `8 - r`;
- the full inequality-defined polygon admissibility set is naturally cornered
  or stratified and is not globally covered by the smooth-boundary Assumption
  Q;
- boundary submersion, a uniform singular-value lower bound, complete nonempty
  fibers, and bidirectional no-exit remain assumptions rather than established
  properties of the full polygon prior;
- finite-difference rank, accepted/base-point re-differentiation, local PCA,
  and constrained-search return are numerical evidence rather than analytic
  proofs;
- the learned controls were sampled from the middle 80% of a 2,000-candidate
  score ordering, numerical rank was not controlled, and the bootstrap does
  not resample masks or the already aggregated 16-sample Monte Carlo axis;
- the learned conditional EDM is not the DDPM chain in the external theorem;
  its held-out error improvement does not establish a `d-r` learning rate,
  conditional-score approximation, posterior calibration, or finite-sample
  theory; and
- the DDPM corollary is pointwise in a fixed regular pair, requires a positive
  selected entropy exponent and the pinned external hypotheses, and is not a
  uniform conditional-network theorem.

## Reused results and missing experiments

The v0.3.0 candidate reuses completed local evidence only where the archived
outputs and current claims align:

- continuation acceptance and survivorship accounting;
- complete-map numerical spectra for the image-rank refinement;
- scale-resolved linear-cover saturation diagnostics; and
- a held-out conditional EDM/U-Net comparison under a frozen, path-free
  protocol.

The prioritized missing-experiment protocols are recorded in
`docs/EXPERIMENT_REUSE_AND_GAP_PLAN.md`: nonlinear constrained residual-tube
optimization (P0), EIT horizontal flow and no-exit diagnostics (P1), an
explicit-prior coarea-law study (P2), matched-rank diffusion ablation (P3), and
a noisy-posterior study after a corresponding theorem (P4). They are not
release blockers because the candidate does not claim their conclusions.

## Publication handoff

The local content candidate has no known release blocker. Publication still
requires explicit maintainer authorization for the external-state changes:

1. review and create the v0.3.0 content commit;
2. push `main` and require both Python 3.11 and 3.12 CI jobs to pass;
3. create a new annotated `v0.3.0` tag without moving either v0.2.0 tag;
4. create the GitHub release and attach the audited manuscript PDF if desired;
5. verify the release page, asset hash, citation rendering, license detection,
   security-report route, and manuscript download as an unauthenticated user.

Because the repository is already public, no visibility transition is needed.
