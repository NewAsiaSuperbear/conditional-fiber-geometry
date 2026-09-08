# First verified build

Timestamp: `2026-09-07T15:09:07+08:00`

## Locked environment

```text
project HEAD
77e2203e6d5df42b457823eebe6626f1b1c3ded1

Lean
Lean 4.34.0-rc2 (commit 6a10ac8c22beadecabdbb0919c2b50214762f91d)

mathlib HEAD
71a80585ee495fc24472fd0eaffc89d94e4fd8d6
```

`lake update` generated `lake-manifest.json` and the mathlib cache was
downloaded. The first configuration attempt failed because this Lake version
requires `LeanOption` constructors rather than string/Boolean pairs. The first
source attempt also found that the guessed module
`Mathlib.Topology.Sets.Compact` does not exist at the fixed revision. Both
configuration/import issues were corrected without changing mathematical
statements.

## Final command and result

```text
lake build
Build completed successfully (2435 jobs).
```

The root imports the audit module. `#print` confirmed the actual declaration
types, and `#print axioms` reported exactly the allowed logical foundations
`propext`, `Classical.choice`, and `Quot.sound` for every audited declaration.
No `sorry`, custom `axiom`, or proof-placeholder `opaque` command occurs in
the production Lean sources.

Verified scope in this build:

- M00 foundational model/fiber membership, disjointness, closedness, and
  compact-image lemmas;
- M01 kernel inclusion, the explicit equivalence between the two kernel
  subtypes, the additive restricted-rank identity, rank inequality, natural
  subtraction form, and the pointwise derivative bridge for the genuine
  observed map `H=P∘F`.

No M02 covering theorem, M03 implicit-chart bridge, M05 disintegration result,
or paper-level theorem is claimed by this build.
