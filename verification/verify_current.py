"""Exact finite regression checks for the current integer AD constructions.

Finite checks are not general proofs. Small determinant expansions below test
matrix identities; they do not implement the polynomial-size determinant DAG.
"""
from pathlib import Path
from collections import Counter
import hashlib
import itertools
import json
import math
import random
import time
import networkx as nx
import numpy as np
import sympy as sp
import ad_circuit as matrix
import quadratic_ad_circuit as compiler

ROOT = Path(__file__).resolve().parent
MODULUS = 1000000007

def fingerprint(value):
    value = int(value)
    raw = abs(value).to_bytes(max(1, (abs(value).bit_length()+7)//8), "big")
    return hashlib.sha256((b"-" if value < 0 else b"+")+raw).hexdigest()

def rank(a):
    return int(sp.Matrix(a.tolist()).rank())

def rank_mod(a):
    a = [[int(x) % MODULUS for x in row] for row in a.tolist()]
    n, m, r = len(a), len(a[0]), 0
    for j in range(m):
        pivot = next((i for i in range(r, n) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inverse = pow(a[r][j], MODULUS-2, MODULUS)
        a[r] = [x*inverse % MODULUS for x in a[r]]
        for i in range(n):
            if i != r and a[i][j]:
                scale = a[i][j]
                a[i] = [(x-scale*y) % MODULUS for x, y in zip(a[i], a[r])]
        r += 1
        if r == n:
            break
    return r

def eye(n):
    return np.array(matrix.eye(n), dtype=object)

def probes(a, d, bound):
    n = len(a)
    rows = [[eye(n)]]
    z = np.zeros((n, n), dtype=object)
    for k in range(bound-1):
        previous = rows[-1]
        rows.append([(d+bound**2*(j-k)*eye(n)) @
                     (previous[j] if j <= k else z) + bound**2*a @
                     (previous[j-1] if j > 0 else z) for j in range(k+2)])
    return [p for row in rows for p in row]

def trees(n):
    return [nx.empty_graph(1)] if n == 1 else nx.nonisomorphic_trees(n)

def matrices(graph):
    n = len(graph)
    a = np.array(nx.to_numpy_array(graph, nodelist=range(n), dtype=int), dtype=object)
    d = np.diag(np.array([graph.degree(i) for i in range(n)], dtype=object))
    return a, d

def rooted_code(graph, u, parent=-1):
    return "("+"".join(sorted(rooted_code(graph, v, u) for v in graph[u] if v != parent))+")"

def syntax_check(circuit):
    degrees = []
    for i, gate in enumerate(circuit["nodes"]):
        assert all(0 <= j < i for j in gate.get("args", []))
        op = gate["op"]
        if op in ("I", "zero"):
            degree = 0
        elif op in ("A", "D"):
            degree = 1
        elif op == "scale":
            assert str(int(gate["constant"])) == gate["constant"]
            degree = degrees[gate["args"][0]]
        elif op == "add":
            degree = max(degrees[j] for j in gate["args"])
        else:
            assert op == "mul"
            degree = sum(degrees[j] for j in gate["args"])
        degrees.append(degree)
    n = circuit["N"]
    assert len(degrees) <= 61*n*n
    assert max(degrees) <= 3*n-2
    assert degrees[circuit["output"]] == circuit["formal_degree"]
    return {"N": n, "gates": len(degrees), "output_degree": degrees[circuit["output"]],
            "maximum_register_degree": max(degrees)}

def tree_check(graph, bound, circuit):
    a, d = matrices(graph)
    n = len(graph)
    u = probes(a, d, bound)
    one = np.ones(n, dtype=object)
    frame = np.column_stack([p @ one for p in u])
    r = rank(frame)
    assert r == len({rooted_code(graph, i) for i in graph})
    assert rank(frame[:, :r*(r+1)//2]) == r
    distance = [eye(n)]
    if bound >= 2:
        distance.append(a)
    if bound >= 3:
        distance.append(a @ a-d)
    for k in range(3, bound):
        distance.append(a @ distance[-1]-(d-eye(n)) @ distance[-2])
    actual_distances = dict(nx.all_pairs_shortest_path_length(graph))
    for k, value in enumerate(distance):
        assert np.array_equal(value, np.array([[int(actual_distances[i][j] == k)
                              for j in range(n)] for i in range(n)], dtype=object))
    j = sum(distance, np.zeros((n, n), dtype=object))
    assert np.array_equal(j, np.ones((n, n), dtype=object))
    digits = [int(x) for s in (eye(n), a, d) for x in (frame.T @ s @ frame).flat]
    height = bound**2*(3*bound**3)**(2*bound-2)
    base = 2*height+1
    assert digits[0] == n and all(abs(x) <= height for x in digits)
    encoded = matrix.encode_digits(digits, base)//2
    output, resources = compiler.evaluate_generic(circuit, a.tolist(), d.tolist())
    trace = sum(output[i][i] for i in range(n))
    if bound == 1:
        assert output == matrix.eye(n) and trace == 1
    else:
        assert trace == 2*encoded
        residual, decoded = encoded, []
        for _ in digits:
            digit = residual % base
            if digit > height:
                digit -= base
            decoded.append(digit)
            residual = (residual-digit)//base
        assert residual == 0 and decoded == digits
    return {"order": n, "bound": bound, "module_rank": r,
            "trace_sha256": fingerprint(trace), "trace_bits": abs(trace).bit_length(),
            "peak_entry_bits": resources["peak_entry_bits"]}

def joint_rank(h, k, v):
    basis = sp.Matrix(v.tolist()).columnspace()
    while True:
        if not basis:
            return 0
        b = sp.Matrix.hstack(*basis)
        new = b.row_join(sp.Matrix(h.tolist())*b).row_join(sp.Matrix(k.tolist())*b).columnspace()
        if len(new) == len(basis):
            return len(basis)
        basis = new

def symmetric_checks():
    rng, count = random.Random(91005), 0
    for n in range(1, 7):
        for mode in range(7):
            bound = max(n, 5) if mode in (3, 4) else n
            h = np.array([[rng.randrange(-3, 4) for _ in range(n)] for _ in range(n)], dtype=object)
            h = h+h.T
            k = np.diag(np.array([rng.randrange(bound) for _ in range(n)], dtype=object))
            v = np.array([rng.randrange(-2, 3) for _ in range(n)], dtype=object)
            if mode == 1:
                k += 10**15*eye(n)
            if mode == 2:
                h *= 10**20
            if mode in (3, 4):
                k = np.zeros((n, n), dtype=object)
                for i in range(n-1):
                    k[i, i+1] = k[i+1, i] = 1
                if mode == 4:
                    k += 10**15*eye(n)
            if mode == 5:
                v = np.zeros(n, dtype=object)
                v[0] = 1
                for i in range(1, n):
                    h[0, i] = h[i, 0] = 0
            if mode == 6:
                v = np.zeros(n, dtype=object)
            frame = np.column_stack([p @ v for p in probes(h, k, bound)])
            r = rank(frame)
            assert r == joint_rank(h, k, v)
            assert rank(frame[:, :r*(r+1)//2]) == r
            count += 1
    return count

def main():
    start = time.monotonic()
    syntax = [syntax_check(compiler.Builder(n).build()) for n in range(1, 16)]
    circuit = compiler.Builder(6).build()
    records = [tree_check(g, 6, circuit) for n in range(1, 7) for g in trees(n)]
    assert len({r["trace_sha256"] for r in records}) == len(records)
    boundary = [tree_check(g, bound, compiler.Builder(bound).build())
                for bound in (1, 2) for n in range(1, bound+1) for g in trees(n)]
    print(f"Actual DAG/tree semantics passed on {len(records)} common-bound trees and {len(boundary)} boundary inputs", flush=True)
    pairs = symmetric_checks()
    print(f"Exact symmetric-pair frame checks passed: {pairs}", flush=True)
    report = {"finite_checks_only": True, "all_assertions_passed": True,
              "syntax": syntax, "common_tree_bound": 6, "trees": records,
              "boundary": boundary, "symmetric_pair_cases": pairs,
              "versions": {"networkx": nx.__version__, "numpy": np.__version__, "sympy": sp.__version__},
              "source_sha256": {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                  for name in ("verify_current.py", "ad_circuit.py", "quadratic_ad_circuit.py")},
              "elapsed_seconds": round(time.monotonic()-start, 3)}
    (ROOT/"current_checks.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"passed": True, "trees": len(records), "pairs": pairs,
                      "max_trace_bits": max(r["trace_bits"] for r in records),
                      "elapsed_seconds": report["elapsed_seconds"]}), flush=True)

if __name__ == "__main__":
    main()
