# Complete Lean proof package

This directory is the complete local import closure of `CombinedAudit`:
189 original proof modules, 25 several-generator modules, and the combined
audit entry point. It does not depend on a separate local project.

`source-to-statement.tsv` maps the manuscript claims to formal endpoints and
records their hypotheses and proof scope. `multi_symmetric_coverage.json`
identifies all 15 required extension theorems. `formalization_scope.txt`
explains the source-to-statement review, the actual-rank and zero-seed cases,
the staged shared circuit, and the limits of the formalization.

## Verification and reproduction

Requirements: Python 3.11 or later, Lean **4.33.0**, Lake, and the dependencies
pinned by `lake-manifest.json`. To check the distributed source and saved audit
evidence without installing Lean or its dependencies:

```text
python -B run_audit.py --verify-only
```

This mode can also check inputs before the first build. An empty
`verified_audit_reports` list then means that no completed evidence was checked;
source integrity alone is not proof-audit success. The published snapshot must
list `provenance/integrated_audit/rebuild_report.json`. The repository-root
manifest additionally requires this report and all of its module logs.

To freshly compile every local module:

```text
lake exe cache get
python -B run_audit.py --jobs 2
```

`--jobs` controls the number of dependency-ready compiler processes and defaults
to one. `--lean /path/to/lean` selects a native compiler explicitly. The runner
verifies the required compiler version and each dependency's clean pinned Git
revision. It uses only this project's source tree and downloaded dependencies.

By default every local module is freshly compiled. An interrupted build may be
continued with `--resume`. A checkpoint is reusable only if the compiler,
complete input manifest, source closure, prior successful logs, compiled
artifacts, and their local dependency hashes still match. A changed source or
configuration requires a fresh build. Historical compiled artifacts are never
required for a clean rebuild.

The three audit entries check the original environment, the extension
environment, and their union. The final scan includes private helpers and
rejects project-local axioms and all transitive axioms other than `propext`,
`Classical.choice`, and `Quot.sound`. It also requires every extension endpoint
to be a theorem. The extension source disables automatic implicit variables.
All compiler warnings are rejected. Every source, compiled artifact, and log is
hashed again before a successful report is finalized.

## Evidence files

- `provenance/integrated_audit/rebuild_report.json`: the complete integrated
  build, source and dependency snapshots, per-module results, and measured
  declaration counts. Its per-module logs are in the same directory.
- `provenance/rebuild_20261025/`: the earlier fresh build of all 189 distributed
  original modules, with 4,704 declarations and 4,639 bodies checked.
- `provenance/frozen_audit.json`, `axiom_audit.log`, and `circuit_exports.log`:
  historical original audit evidence. The original identifiers were
  standardized for distribution; the frozen record distinguishes audited and
  distributed source hashes. The later complete builds check the distributed
  sources directly.
- `audit_manifest.json`: frozen proof inputs and compiler configuration used by
  the runner. `freeze_audit_manifest.py` is a maintainer helper, not a required
  reproduction step. Regenerating this manifest is not itself verification.
- `artifact_manifest.json`: all distributed files in this directory, except
  the manifest itself. The repository-root manifest also covers these files.

New build records go to `rebuild_logs/`; they do not overwrite the distributed
evidence. A source-and-evidence integrity check is distinct from recompiling
the proofs. Cross-platform reproduction requires renewed kernel acceptance,
not byte-identical `.olean` files.

## Scope

The original package formalizes differential spanning, the matrix-circuit
compiler and resource bounds, the PSD construction, and the trace-degree
lower bound. It uses the formalized finite-tree principal-moment reconstruction
theorem of Zhipeng Lu and Pengxiang Li, *Adjacency-degree algebras and spectral
determination of graphs*, Theorem 5.4. The full-representation formal proof
uses the all-one polynomial and that reconstruction theorem; the written
appendix uses McKay's theorem and Newton identities. The mapping records this
difference in proof routes.

The extension proves multiple-pole rigidity and real descent, the literal
integer recurrence and its matrix evaluation, spanning of the actual cyclic
space by its rank prefix, the indexed count and word-degree bound, exact
specialization to the original recurrence, and the finite shared circuit's
outputs, gates, and actually used scalar constants. It imposes no spectral
bound on H and includes zero seeds and proper cyclic spaces.

It does not claim a bit bound on evaluated entries for arbitrary real input,
does not include an unbounded-spectrum homogenization, and does not substitute
s=0 into kappa=s*N^2. The fixed-word lower bound in manuscript Remark 1.4 is
proved in the text and is not part of this formalization. The additional exact
tests supplement these proofs and are not substitutes for universal theorems.
