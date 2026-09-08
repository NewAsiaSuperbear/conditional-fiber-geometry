# CFG declaration inventory tools

This directory publishes the original declaration-inventory exporter,
validator, and regression tests developed for the CFG audit update. The
software is covered by the repository MIT license.

The separate user-supplied audit package contained a selected-target scanner,
tests, a snapshot shell script, and a CI template. Their redistribution
license has not yet been confirmed, so those adapted files and the associated
Lean workflow are retained locally and are not part of this publication.
The local verification summary includes checks performed with those tools;
that is historical evidence, not a claim that every local tool is published.

## Run the published tools

Use the pinned toolchain in `formal/lean-toolchain` and mathlib revision in
`formal/lake-manifest.json`; do not run `lake update` for reproduction.
From the repository root:

```sh
python3 -m unittest discover -s formal/audit_tools -p 'test_check_inventory.py' -v
cd formal
lake build
lake env lean audit_tools/DeclarationInventory.lean > /tmp/cfg-inventory.log
python3 audit_tools/check_inventory.py /tmp/cfg-inventory.log --formal-root . \
  -o /tmp/cfg-inventory-gate.json
LEAN_NUM_THREADS=2 lake env leanchecker CFG
```

The exporter selects imported kernel declarations by project source module,
not by declaration-name prefix. It reports readable types, recursive axioms,
private/internal-name flags, and unresolved direct dependencies. Pretty-printed
types can hide implicit parameters; the conservative internal-name flag does
not identify every generated declaration. Compiler-only artifacts absent from
the imported environment and later declarations are outside its coverage.

The validator fails on missing modules, duplicate declarations, malformed
schema values, unresolved dependencies, or axioms outside `propext`,
`Classical.choice`, and `Quot.sound`. It does not establish that the formal
statements correctly capture the manuscript or apply to a concrete EIT model.
Use `--preserve PATH` to retain a copy of the raw inventory input.
