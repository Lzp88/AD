# Lean proof audit

This directory contains exactly the local import closure of
`PaperVerifier.ADComplete.PaperAxiomAudit`.
`source-to-statement.tsv` records the manuscript statements, their formal
endpoints, hypotheses, and proof scope. The source files use consistent public
module names; module identities were standardized for this distribution and the
completed original kernel audit is reused. Preparation verified that all proof
sources differ only in these identifiers. The artifact does not claim a new
complete compilation after name standardization.

`PrincipalMomentAudit` reuses the audited finite-tree principal-moment
reconstruction theorem from Zhipeng Lu and Pengxiang Li,
*Adjacency-degree algebras and spectral determination of graphs*,
[arXiv:2607.21494v1, Theorem 5.4](https://arxiv.org/abs/2607.21494v1).
The complete declaration audit checks its transitive axiom dependencies together
with the new results. The formal full-representation reconstruction uses the
actual all-one polynomial and this pointed reconstruction input. The mapping
explains its relation to the written classical reconstruction argument.

Requirements: Python 3.10 or later, Lean **4.33.0**, Lake, and the dependencies
pinned by `lake-manifest.json`. From this directory run:

```text
lake exe cache get
python -B run_audit.py
```

The runner checks the distributed file hashes and freshly compiles all local
modules in dependency order. It requires successful kernel checks without
warnings and the final declaration-audit success marker. The transitive axiom
allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
It also checks that every dependency has its pinned Git revision and no tracked
source modifications.
Use `--lean /path/to/lean` to select a native executable, or `--verify-only`
to check package integrity without compiling.
Independent modules can be checked concurrently with `--jobs 3`; dependents
wait for all their imports to pass. The default uses one process.

`provenance/frozen_audit.json` records the completed original audit with separate
audited-source and distributed-source hashes. Its module names are standardized;
original compiled artifact hashes describe that earlier audit only.
`provenance/axiom_audit.log` is the original complete declaration scan with a
header identifying its standardized names. `provenance/circuit_exports.log`
preserves the original instruction exports unchanged. Rebuilds write a new
report and these two logs to `rebuild_logs/`.
Compiled local artifacts and downloaded dependencies are excluded from Git.

`artifact_manifest.json` hashes every distributed file in this directory except
itself. Compiled artifact hashes record the observed build provenance; another
platform need not reproduce byte-identical `.olean` files. Reproduction requires
the frozen sources and pinned dependencies to pass the kernel checks again.
