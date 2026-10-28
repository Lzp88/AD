# Uniform adjacency-degree probes from differential rigidity

Manuscript and reproducibility materials by Zhipeng Lu.

This version includes the direct extension to several real symmetric generators.
The main tree invariant and the original two-generator spanning theorem are
unchanged. The introduction and the spanning section explain the extension;
Appendix D gives its recurrence and complete proof.

## Contents

- `paper/uniform_ad_probes.pdf` and `.tex`: the manuscript and self-contained
  LaTeX source.
- `lean/`: the complete local proof package, pinned dependencies, a portable
  rebuild script, the statement correspondence, and recorded audit evidence.
  It includes the original 189 modules, 25 extension modules, and one combined
  declaration-audit entry point.
- `verification/`: the original integer circuit emitters and finite checks,
  their recorded results, and 43 exact tests of the several-generator extension.

The extension preserves the degree bound N-1 and the prefix determined by the
actual cyclic-space dimension. Its fixed family has N+s*N*(N-1)/2 indexed
outputs and a shared division-free circuit of O(s^2*N^2) gates. The hypotheses
are real symmetry and spectral diameter at most N-1 for each of the s residue
generators; the remaining generator H has no spectral bound. This is a direct
extension of the same rigidity argument, without a matrix-order enlargement.

## Recorded integrated audit

The recorded integrated build freshly compiled all 215 modules, with no reused steps or warnings, and replayed every declaration of every module through the Lean kernel with `leanchecker`. It also replayed the complete import closure, including the Lean core library and mathlib, from an empty environment. The combined scan checked 5,390 project declarations and 5,297 bodies, including 685 extension declarations. All 15 required extension endpoints passed.

## Check the distributed snapshot

Use Python 3.11 or later. From the repository root:

```text
python -B verify_artifacts.py
python -B lean/run_audit.py --verify-only
```

The first command verifies the distributed files against the root manifest.
The second verifies all proof inputs and the complete recorded build evidence,
including the combined declaration scan, the per-module kernel replays, and
the recorded replay of the complete import closure, without downloading Lean
dependencies. It also repeats the source scan described below. Neither
command is a new kernel build. Run them before regenerating results.

The Lean integrity command can also be used before a first build. In that case
an empty `verified_audit_reports` list means that no completed evidence was
checked, not that the audit passed. For this published snapshot the list must
include `provenance/integrated_audit/rebuild_report.json`; the root manifest
also requires that report and all its logs to be present.

## Build the manuscript

With a LaTeX installation providing the packages named in the source, run from
`paper/`:

```text
pdflatex -interaction=nonstopmode -halt-on-error uniform_ad_probes.tex
pdflatex -interaction=nonstopmode -halt-on-error uniform_ad_probes.tex
```

No external bibliography, figures, or input files are required. Different TeX
installations may produce different PDF bytes.

## Rebuild all Lean proofs

Install Lean 4.33.0 through elan. From `lean/`:

```text
lake exe cache get
python -B run_audit.py --jobs 2
```

The runner freshly compiles all 215 local modules in dependency order and checks
the original, extension, and combined declaration-audit markers. The original
214 proof source files are unchanged from their prior checked versions. The
only added Lean file for integration is `CombinedAudit.lean`.

The allowed transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Project-local axioms, incomplete proofs, compiler failures, and warnings are
rejected. The dependency Git revisions and all source, output, and log hashes
are checked. The extension's 15 required endpoints have explicit type checks.

After compiling each module, the runner replays all of its declarations,
including private and auxiliary ones, through the Lean kernel with the
toolchain's `leanchecker`. A successful compilation and the axiom scan cannot
by themselves detect a declaration that entered the environment without kernel
checking, for example under `debug.skipKernelTC`; the replay rechecks every
such declaration. Before building, a source scan admits only the options
`autoImplicit`, `maxHeartbeats`, and `backward.isDefEq.respectTransparency`.
It permits `run_cmd` only in the three declaration-audit entry points and
`#eval` only in the instruction export, and rejects other metaprogramming
commands, environment-modifying functions, axioms, `sorry`, and
`native_decide`. The scan is a supplementary safeguard; the kernel replay is
the decisive check.

With `--fresh-replay`, the runner also replays the complete import closure of
`CombinedAudit`, including the Lean core library and mathlib, from an empty
environment, so that their compiled artifacts need not be trusted either. On
the machine used for the recorded audit this step took about 15 minutes and
less than 9 GB of memory. The distributed report includes it.

The fresh report and per-module logs are written under `lean/rebuild_logs/`.
The distributed completed report is under `lean/provenance/integrated_audit/`.
No historical `.olean` file or private directory is needed. Compiled artifact
hashes describe an observed build; different platforms need not reproduce the
same compiled bytes. See `lean/README.md` for scope and recovery options.

## Reproduce the finite checks

From the repository root, preferably in a Python virtual environment:

```text
python -m pip install -r verification/requirements.txt
python -B verification/verify_current.py
python -B verification/verify_exports.py
python -B verification/verify_exact.py
```

The original checks cover 14 small trees, boundary inputs, 42 seeded symmetric
pairs, and circuit syntax for bounds 1 through 15. The export checks compare
actual Lean instruction exports with the Python implementation and evaluate
the PSD factory on trees and symmetric pairs. The extension tests compare the
literal and factored recurrences, an independently generated word span, and the
actual-rank prefix over exact rational arithmetic, including zero seeds, proper
cyclic spaces, strict dimension bounds, and large scalar spectral shifts.

By default the export checks read the instruction log of the recorded
integrated build,
`lean/provenance/integrated_audit/PaperVerifier.ADComplete.CircuitExports.log`.
They write their outputs with LF line endings, so the recorded hashes do not
depend on the platform. After a fresh Lean build, use its instruction export
log with:

```text
python -B verification/verify_exports.py --export-log lean/rebuild_logs/PaperVerifier.ADComplete.CircuitExports.log
```

Finite tests supplement the universal proofs. They do not prove universal
equality of separately implemented emitters. Regenerating check results can
change recorded files, so verify snapshot integrity first.
