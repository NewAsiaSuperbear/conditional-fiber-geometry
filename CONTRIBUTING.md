# Contributing

Contributions are welcome when they preserve the repository's distinction
between proved mathematics, numerical evidence, external conditional results,
and open problems.

## Preparing a contribution

Before opening a pull request:

1. State all assumptions, quantifiers, locality conditions, and constant
   dependencies for any mathematical change.
2. Do not identify thresholded numerical rank with exact differential rank or
   describe a numerical experiment as a proof.
3. Add focused correctness tests for nontrivial code changes and a regression
   test when fixing a reproducible defect.
4. Run `python -m pytest -q` and, when the manuscript changes, compile it from
   a clean LaTeX build.
5. Document the seed, parameters, input provenance, and expected output of a
   new scientific experiment.
6. Remove credentials, absolute local paths, hostnames, account identifiers,
   and private experiment metadata from code, logs, notebooks, and artifacts.
7. Update the claims matrix and limitations when a change affects scientific
   scope.

Repository maintainers may use MLflow for experiment provenance when it is
available. External contributors are **not** required to operate or connect to
an MLflow server. A pull request may instead provide a sanitized parameter
record, deterministic seed, commands, metrics, and artifact checksums. Tests,
linting, and document builds should not create experiment-tracking runs.

## Licensing and provenance

By submitting a contribution, you represent that you have the right to submit
it and agree that it may be distributed under the license assigned to its
destination in `LICENSES/README.md`: MIT for software and software
configuration, or CC BY 4.0 for author-owned research materials. Identify any
third-party source, license, and modification explicitly. Do not submit copied
code, data, meshes, figures, or prose whose redistribution terms are unknown
or incompatible.

Dependency code should normally remain external rather than be vendored. If
vendoring is necessary, preserve every upstream notice and explain the need in
the pull request.

## Security and sensitive information

Do not disclose a suspected credential or sensitive-data exposure in a public
issue. Follow `SECURITY.md` for private reporting. Mathematical questions and
non-sensitive reproducibility defects may be reported through ordinary GitHub
issues.
