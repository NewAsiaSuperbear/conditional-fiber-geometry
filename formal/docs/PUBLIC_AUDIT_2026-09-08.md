# Public Lean audit update — 8 September 2026

This update extends the formal development at audit base
`8501264e5a4837f43fa83afdf683e3c9d544761e`. The results below are local
correctness checks of Lean statements and audit tooling. They do not certify
that the full manuscript or a concrete EIT model has been formalized.

## Published material

| Category | Location | Completed content |
| --- | --- | --- |
| Calculus and model interfaces | `formal/CFG/Calculus/` | Actual first and second derivative interfaces, pointwise pseudoinverse derivative bounds, open-domain regularity bridges, and compact fibers |
| Conditional probability and entropy | `formal/CFG/Probability/ConditionalEntropy.lean`, `formal/CFG/External/EntropyScale.lean` | Model-facing conditional-support covering certificates, identity/Dirac instance, and entropy substitution within the stated radius range |
| Statistics | `formal/CFG/Statistics/` | Actual two-point PMF score expectations, an independent forecast-pair bridge, continuous exchangeable no-ties uniform rank, and the real atomless iid extrema-interval probability, including 15/17 for 16 samples |
| Concrete finite-dimensional example | `formal/CFG/Examples/CompactModelToy.lean` | A 3-2-1 linear observation model on a compact closed ball with a polynomial covering certificate |
| Reproducibility tooling | `formal/audit_tools/` | Original imported-environment declaration inventory, validator, and regression tests |
| Scope and evidence | `formal/THEOREM_MAP.md`, `formal/ASSUMPTION_LEDGER.md`, `formal/PROOF_STATUS.json`, `formal/verification/2026-09-08/` | Assumptions, theorem mapping, machine-readable local check summaries, and verified source hashes |

Paths in the table are repository-relative. Source and documentation are in
English. Original software follows the repository's MIT license; author-owned
research prose and metadata follow CC BY 4.0, as allocated in
[LICENSES/README.md](../../LICENSES/README.md). Dependencies retain their own
licenses and are not bundled. AI assistance was used for implementation and
review; the verification claims below rely on the stated checks, not model
endorsement or a guarantee of mathematical completeness.

## Verification evidence

The local snapshot used Lean `leanprover/lean4:v4.34.0-rc2` and mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, without dependency upgrades.

| Check | Local result |
| --- | --- |
| `lake build` with warnings treated as errors | Passed; 8,935 jobs |
| Project source coverage | 54 modules; no orphan modules reported |
| Explicit axiom targets | 219 passed, including 61 critical targets |
| `LEAN_NUM_THREADS=2 lake env leanchecker --verbose CFG` | Passed; 54 modules replayed |
| Namespace axiom audit | 736 declarations passed |
| Source-module inventory | 736 declarations across 54 modules; no unresolved dependencies |
| Python audit-tool regression tests | 25 local tests passed; the published inventory subset has 5 tests, also rerun successfully |
| Shell and CI YAML syntax | Passed locally |

The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The inventory includes 16 declarations outside the `CFG` name prefix and 13
private declarations. Its broader private/internal-name flag marks 211 names;
it is a conservative name-based flag, not an exhaustive classification of
all generated declarations. Coverage is of kernel declarations imported from
project source modules, not compiler-only artifacts or declarations generated
later. A namespace audit alone cannot establish that coverage.

The [machine-readable result](../verification/2026-09-08/final_status.json)
records the historical local snapshot. Its `uncommitted_worktree` and
`remote_ci_run` fields describe the time of that check, before publication.
The [source hashes](../verification/2026-09-08/source_hashes.json) identify the
64 locally verified source/configuration/tool files, including locally retained
audit scripts and a workflow whose redistribution permission is pending; it
is not a manifest of only the published files. The aggregate digest is
`67907b6e205bada0db52a1bde234fbb679541655ddcd047b8369e5ddbd8e5dff`.
Publication documentation is outside that source digest. The existing GitHub Actions workflow provides separate Python CI evidence;
the new Lean workflow is retained locally pending its template provenance
confirmation. No remote Lean CI success is claimed.

Nine dependency checkouts matched the lock file and had no tracked changes.
Dependency binaries were reused from local caches; project sources were
rebuilt. An initial baseline download failed because of DNS access, and the
baseline was subsequently checked with the pinned local cache. The complete
workstation logs remain local; the published JSON files are selected check
summaries, not a claim of a fresh network-isolated rebuild. No numerical
research experiment was run, so no MLflow run was created.

## Reproduce

From `formal/`, with the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=2 lake env leanchecker CFG
python3 -m unittest discover -s audit_tools -p 'test_check_inventory.py' -v
lake env lean audit_tools/DeclarationInventory.lean > /tmp/cfg-inventory.log
python3 audit_tools/check_inventory.py /tmp/cfg-inventory.log --formal-root . \
  -o /tmp/cfg-inventory-gate.json
```

See [audit tool instructions](../audit_tools/README.md) for the published
inventory and validator. The local selected-target scanner, snapshot script,
and associated workflow were adapted from a user-supplied audit package with
no independent license notice. Those files are withheld pending confirmation
of redistribution rights; the local results above remain historical evidence.

## Remaining mathematical obligations

- Sharper constant-rank image-covering exponents, SVD/whitening interfaces,
  and the full quantitative nonlinear/uniform-covering argument.
- ODE existence, no-exit and transport flow, coarea and conditional-density
  formulas, and explicit coupling/Wasserstein constructions.
- Manifold curvature, full Gaussian constants, external diffusion results,
  and Gaussian risk statements.
- Actual FEM/PDE shape derivatives and numerical certificates for a concrete
  EIT model.
- IID V/U estimator expectation bridges and verification of the assumptions
  for a concrete conditional sampler.
- A radial joint example, more general local-domain/countable-mask support
  interfaces, and a complete manual manuscript-to-Lean semantic audit.

In particular, conditional-covering constants are pointwise; measurability
and integrability are not established. Some wrappers retain global continuity
as an explicit hypothesis. The pseudoinverse result is pointwise and does not
assert a global Lipschitz estimate on a nonconvex region. The closed-ball toy
example does not establish the sharper image-rank exponent.

## Material retained locally

The original audit archive, Chinese working report, raw workstation logs,
model conversations and service responses, dependency caches, and local
archive checksum manifest, and the audit-package scripts awaiting license
confirmation are excluded from this publication. They are not
needed to build the public sources. The input archive and local evidence have
been preserved without deleting or rewriting them.
