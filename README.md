# Uniform adjacency-degree probes from differential rigidity

Manuscript and reproducibility materials by Zhipeng Lu.

- `paper/` contains the latest manuscript source and its PDF. The introduction
  is revised; the mathematical body matches the audited version.
- `lean/` contains the exact 189-module local dependency closure of the final
  declaration audit, pinned dependencies, the source-to-statement mapping,
  a portable runner, and the completed kernel-audit provenance.
- `verification/` contains the integer circuit emitter, independent finite
  checks, their recorded results, and the manuscript's circuit example.

The manuscript source and PDF are preserved byte for byte. The completed Lean
audit is reused; proof-source changes consist only of consistent public module
identities, verified against the audited source. The provenance distinguishes
the audited source hashes from the distributed source hashes. Public module names
are consistent throughout the proof sources and Python reference metadata.
The manuscript links directly to this repository for the Lean audit and
reproduction materials. The proof project is distributed as `lean/`.

## Verify the distributed snapshot

Use Python 3.11 or later for the pinned numerical dependencies.

```text
python -B verify_artifacts.py
```

This checks every distributed file against `artifact_manifest.json`, including
the manuscript, proof sources, dependency pins, and recorded results.

## Build the paper

With a LaTeX installation providing the packages named in the self-contained
source, run from `paper/`:

```text
pdflatex -interaction=nonstopmode -halt-on-error uniform_ad_probes.tex
pdflatex -interaction=nonstopmode -halt-on-error uniform_ad_probes.tex
```

No separate bibliography, figures, or input files are required. Different TeX
installations may produce different PDF bytes.

## Rebuild the Lean audit

Install Lean 4.33.0 through elan. From `lean/`:

```text
lake exe cache get
python -B run_audit.py
```

Every local module is freshly compiled. The final audit permits only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms. Fresh results are saved
under `lean/rebuild_logs/`. See `lean/README.md` and the statement mapping for
the formal endpoints, hypotheses, and reused reconstruction theorem.

## Reproduce the finite checks

From the repository root, preferably in a Python virtual environment:

```text
python -m pip install -r verification/requirements.txt
python -B verification/verify_current.py
python -B verification/verify_exports.py
```

The export checks use the actual Lean factory instructions in
`lean/provenance/circuit_exports.log`. To check a fresh Lean rebuild instead:

```text
python -B verification/verify_exports.py --export-log lean/rebuild_logs/circuit_exports.log
```

The first check covers 14 trees with common bound six, three boundary inputs,
42 symmetric pairs, and circuit syntax for bounds one through fifteen.
The second compares the Python and Lean linear instructions for bounds one
through fifteen and checks the exported PSD factory on 11 tree cases and
12 symmetric pairs. These finite checks supplement the proofs; they do not
establish universal equality of separately implemented emitters.

Reproduction rewrites the recorded results, so snapshot integrity should be
checked before running it. Build products and auxiliary regenerated exports
are ignored by Git.
