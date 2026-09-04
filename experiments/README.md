# Numerical experiments

This directory contains compact numerical evidence for the local mechanisms
studied in the manuscript. The experiments are complementary to the
mathematical results: they examine finite-dimensional discretizations and do
not verify the manuscript assumptions over an entire EIT parameter class.

## Contents

| Path | Purpose |
|---|---|
| `run_toy_validation.py` | Deterministic analytic checks of transport and covering formulas. |
| `plot_spectral_validation.py` | Rebuilds the manuscript's four-panel validation figure from committed CSV tables. |
| `results/fiber_mechanisms_seed20260903/` | Finite-difference, fiber-continuation, local tube, projection, Gaussian-MMSE, whitening, and CEM-interface results. |
| `results/spectral_validation/` | Replicated fiber, rank-along-fiber, full-spectrum tube, covering-calibration, near-critical, and mesh-sensitivity results. |
| `results/whitened_mask_design_seed20260902/` | Independent comparison of whitened, unweighted, and random mask designs. |
| `PROVENANCE.md` | Origins, attribution boundaries, seeds, curation policy, and data limitations. |
| `results/SHA256SUMS` | Integrity manifest for the committed result artifacts. |

The full synthetic forward dataset and the programs used for the original
large result generation are not included. The committed numeric tables and
arrays permit inspection of the reported diagnostics, while the displayed
four-panel figure can be regenerated independently from those tables.

## Rebuild the manuscript figure

Install the optional plotting dependency and run:

```bash
python -m pip install -e ".[figures]"
python experiments/plot_spectral_validation.py
```

The output is:

```text
experiments/results/spectral_validation/conditional_geometry_validation.pdf
```

The plotting program uses NumPy and Matplotlib only. It computes Spearman
correlations internally with average ranks, embeds TrueType fonts in the PDF,
uses redundant color/marker/line encodings, and omits timestamp and local-path
metadata. Panel (c) displays the explicit deviation
`sigma_i * width_i / delta - 1`, rather than relying on an axis offset around
one.

## Run the self-contained analytic checks

After installing the package:

```bash
python experiments/run_toy_validation.py
```

These checks are deterministic examples, not scientific experiments and not
proofs of the manuscript's theorems.

## Verify artifact integrity

From the repository root:

```bash
cd experiments/results
sha256sum -c SHA256SUMS
```

See [PROVENANCE.md](PROVENANCE.md) before reusing or interpreting the result
files.
