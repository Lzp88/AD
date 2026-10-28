"""Check actual Lean instructions and independent finite matrix semantics.

These finite regressions do not prove universal equality of Python and Lean
emitters. The PSD instructions are exported from the actual Lean factory.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import math
import time
import sympy as sp
import quadratic_ad_circuit as circuit
import verify_current as checks

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def independent_psd(N, a, d):
    n = len(a)
    if N == 1:
        return sp.eye(n)
    family = [sp.Matrix(p.tolist()) for p in checks.probes(a, d, N)]
    m = len(family)-1
    R = (3*N**3)**(N-1)
    H0 = m*R*2**((N-2)*(m-1))
    tau = math.factorial(N)*H0**(N-1)+2
    seed = sp.ones(n, 1)
    z = [seed] + [sum((((2**j*tau)**i)*(p*seed) for i, p in enumerate(family[1:])),
                       sp.zeros(n, 1)) for j in range(N-1)]
    residuals = [seed]
    for k in range(1, N):
        K = sp.Matrix.hstack(*z[:k])
        G = K.T*K
        b = K.T*z[k]
        delta = G.det()
        cofactors = []
        for i in range(k):
            replacement = G.copy()
            replacement[:, i] = b
            cofactors.append(replacement.det())
        residuals.append(delta*z[k]-sum((cofactors[i]*z[i] for i in range(k)),
                                        sp.zeros(n, 1)))
    t = [n**max(k-1, 0)*u for k, u in enumerate(residuals)]
    out = t[0]*t[0].T
    for k in range(N-1):
        v = t[k]+t[k+1]
        out += v*v.T
    return n*out


def psd_minors(C):
    for k in range(1, C.rows+1):
        for ix in itertools.combinations(range(C.rows), k):
            assert C.extract(ix, ix).det() >= 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--export-log', type=Path, default=ROOT.parent/'lean'/'provenance'/
                        'integrated_audit'/'PaperVerifier.ADComplete.CircuitExports.log')
    args = parser.parse_args()
    start = time.monotonic()
    raw = args.export_log.read_text(encoding='utf-8')
    rows = [json.loads(line) for line in raw.splitlines() if line.startswith('{')]
    linear = [r for r in rows if r['kind'] == 'linear']
    psd = [r for r in rows if r['kind'] == 'psd']
    assert [r['N'] for r in linear] == list(range(1, 16))
    assert [r['N'] for r in psd] == list(range(1, 5))
    for r in linear:
        emitted = circuit.Builder(r['N']).build()
        for key in ('nodes', 'output', 'reverse_output'):
            assert r[key] == emitted[key], (r['N'], key)
    for N in (1, 5):
        circuit.write_circuit(circuit.Builder(N).build(), ROOT/f'p{N}.quadratic.circuit.json.gz')
    # Fixed LF bytes keep reference_sha256 independent of the platform.
    (ROOT/'lean_circuit_reference.jsonl').write_text(
        ''.join(json.dumps(r, separators=(',', ':'))+'\n' for r in rows), encoding='utf-8', newline='\n')
    records = []
    for r in psd:
        N = r['N']
        for n in range(1, N+1):
            for g in checks.trees(n):
                a, d = checks.matrices(g)
                result, stats = circuit.evaluate_generic(r, a.tolist(), d.tolist())
                C = sp.Matrix(result)
                expected = independent_psd(N, a, d)
                assert C == expected
                assert C == C.T
                psd_minors(C)
                family = [sp.Matrix(p.tolist()) for p in checks.probes(a, d, N)]
                seed = sp.ones(n, 1)
                source = sp.Matrix.hstack(*(p*seed for p in family))
                image = C.columnspace()
                powers = [seed]
                for k in range(1, N):
                    powers.append(C*powers[-1])
                cyclic = sp.Matrix.hstack(*powers)
                rank = source.rank()
                assert C.rank() == rank == cyclic.rank()
                assert sp.Matrix.hstack(C, source).rank() == rank
                assert sp.Matrix.hstack(cyclic, source).rank() == rank
                records.append({'N': N, 'n': n, 'edges': sorted(map(list, g.edges())),
                                'rank': rank, 'gates': len(r['nodes']),
                                'peak_entry_bits': stats['peak_entry_bits']})
        print(f'Actual exported PSD factory N={N}: graph cases passed', flush=True)
    generic = []
    samples = [([[0,1],[1,0]], [[1,2],[2,-1]]),
               ([[2,-1],[-1,3]], [[0,0],[0,0]]),
               ([[0,0],[0,0]], [[-3,1],[1,4]])]
    for r in psd:
        for a, d in samples:
            out, stats = circuit.evaluate_generic(r, a, d)
            C = sp.Matrix(out)
            assert C == C.T
            psd_minors(C)
            generic.append({'N': r['N'], 'peak_entry_bits': stats['peak_entry_bits']})
    report = {'all_assertions_passed': True, 'finite_checks_only': True,
              'linear_instruction_matches': list(range(1, 16)),
              'psd_graph_cases': records, 'psd_symmetric_pair_cases': generic,
              'export_log_sha256': digest(args.export_log),
              'source_sha256': {p: digest(ROOT/p) for p in
                  ('verify_exports.py', 'verify_current.py', 'quadratic_ad_circuit.py', 'ad_circuit.py')},
              'reference_sha256': digest(ROOT/'lean_circuit_reference.jsonl'),
              'sympy_version': sp.__version__, 'elapsed_seconds': round(time.monotonic()-start, 3)}
    (ROOT/'export_checks.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps({'passed': True, 'linear_cases': len(linear),
                      'psd_trees': len(records), 'psd_pairs': len(generic),
                      'seconds': report['elapsed_seconds']}), flush=True)


if __name__ == '__main__':
    main()
