"""Independent finite exact-arithmetic checks, supplementary to Lean proofs."""
from pathlib import Path
import hashlib, json, random
import sympy as S

ROOT = Path(__file__).resolve().parent

def coefficient(p, j, n):
    return p[j] if 0 <= j < len(p) else S.zeros(n)

def derivative(p):
    return [(j + 1) * p[j + 1] for j in range(len(p) - 1)]

def factor(p, a, n):
    return [coefficient(p, j - 1, n) - a * coefficient(p, j, n)
            for j in range(len(p) + 1)]

def factors(p, poles, n):
    for a in poles:
        p = factor(p, a, n)
    return p

def quotient(g, a, n):
    q = [S.zeros(n) for _ in range(len(g) - 1)]
    last = S.zeros(n)
    for j in range(len(q) - 1, -1, -1):
        last = g[j + 1] + a * last
        q[j] = last
    assert g[0] + a * last == S.zeros(n)
    return q

def direct_step(p, k, N, H, A):
    n, s = H.rows, len(A)
    poles, kap = list(range(s)), s * N * N
    dp = factors(derivative(p), poles, n)
    hp = factors([H * x for x in p], poles, n)
    residues = [factors([a * x for x in p], [b for b in poles if b != i], n)
                for i, a in enumerate(A)]
    # D' p = sum_i Q_i p, using the derivative of a product of monic factors.
    correction = [factors(p, [b for b in poles if b != i], n) for i in poles]
    return [kap * coefficient(dp, j, n) + kap * coefficient(hp, j, n)
            + sum((coefficient(q, j, n) for q in residues), S.zeros(n))
            - k * kap * sum((coefficient(q, j, n) for q in correction), S.zeros(n))
            for j in range(s * (k + 1) + 1)]

def optimized_step(p, k, N, H, A):
    n, s = H.rows, len(A)
    poles, kap = list(range(s)), s * N * N
    g = factors(p, poles, n)
    t = factors(derivative(p), poles, n)
    dg = derivative(g)
    q = [quotient(g, a, n) for a in poles]
    return [kap * (k + 1) * coefficient(t, j, n) + kap * H * g[j]
            + sum((A[b] * coefficient(q[b], j, n) for b in poles), S.zeros(n))
            - k * kap * coefficient(dg, j, n) for j in range(len(g))]

def independent_word_span(generators, seed):
    n = seed.rows
    columns = [seed] if seed != S.zeros(n, 1) else []
    for _ in range(n):
        current = list(columns)
        old_rank = len(columns)
        for g in generators:
            for z in current:
                x = g * z
                if S.Matrix.hstack(*(columns + [x])).rank() > len(columns):
                    columns.append(x)
        if len(columns) == old_rank:
            break
    return S.Matrix.hstack(*columns) if columns else S.zeros(n, 0)

def run_case(N, s, H, A, seed, tag):
    n = H.rows
    word_basis = independent_word_span([H] + A, seed)
    rho = word_basis.cols
    p, rows = [S.eye(n)], []
    for k in range(N):
        rows.append([x * seed for x in p])
        if k + 1 < N:
            q = direct_step(p, k, N, H, A)
            r = optimized_step(p, k, N, H, A)
            assert q == r, (tag, 'optimized recurrence', k)
            p = r
    all_columns = sum(rows, [])
    prefix_columns = sum(rows[:rho], [])
    full = S.Matrix.hstack(*all_columns)
    prefix = S.Matrix.hstack(*prefix_columns) if prefix_columns else S.zeros(n, 0)
    assert full.rank() == prefix.rank() == rho, (tag, 'rank')
    assert S.Matrix.hstack(word_basis, full).rank() == rho, (tag, 'module')
    assert len(all_columns) == N + s * N * (N - 1) // 2
    return dict(tag=tag, N=N, s=s, n=n, rank=rho, outputs=len(all_columns))

def main():
    rng = random.Random(20261027)
    records = []
    for N in range(1, 6):
        for s in range(1, 4):
            n = N
            h = S.Matrix(n, n, lambda i, j: rng.randrange(-30, 31))
            H = 100 * (h + h.T)
            A = []
            for b in range(s):
                x = S.Matrix(n, n, lambda i, j: rng.randrange(-2, 3))
                x = x + x.T
                norm = max(1, max(sum(abs(x[i, j]) for j in range(n)) for i in range(n)))
                # Gershgorin gives diameter <= N-1, despite large scalar shifts.
                A.append(S.Rational(N - 1, 2 * norm) * x + (1000 + b) * S.eye(n))
            for mode in ('nonzero', 'zero'):
                seed = S.Matrix([rng.randrange(-2, 3) for _ in range(n)]) if mode == 'nonzero' else S.zeros(n, 1)
                records.append(run_case(N, s, H, A, seed, f'random-{N}-{s}-{mode}'))
    for N in range(2, 7):
        H = S.zeros(N)
        for i in range(N - 1):
            H[i, i + 1] = H[i + 1, i] = 1
        records.append(run_case(N, 2, H, [S.zeros(N), S.eye(N)], S.eye(N)[:, 0], f'path-degree-{N}'))
        H[N - 2, N - 1] = H[N - 1, N - 2] = 0
        records.append(run_case(N, 2, H, [S.zeros(N), S.eye(N)], S.eye(N)[:, 0], f'proper-module-{N}'))
    records.append(run_case(4, 3, S.Matrix([[400, 700], [700, -200]]),
                           [S.Matrix([[1000, 1], [1, 1000]]), S.diag(0, 3), S.eye(2)],
                           S.Matrix([1, -2]), 'strict-order-bound-2-of-4'))
    records.append(run_case(6, 1, S.Matrix([[3, 7, 0], [7, 1, -4], [0, -4, 20]]),
                           [S.diag(0, 2, 5)], S.Matrix([1, 0, 0]), 'strict-order-bound-3-of-6'))
    records.append(run_case(5, 3, S.Matrix([[99999]]),
                           [S.Matrix([[1000]]), S.Matrix([[-2000]]), S.Matrix([[3000]])],
                           S.Matrix([[2]]), 'scalar-input-1-of-5'))
    report = dict(status='passed', exact_arithmetic=True, cases=len(records),
                  scope='finite checks only; universal proof is the separate Lean audit', records=records,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'exact_checks.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:report[k] for k in ('status','exact_arithmetic','cases')}))

if __name__ == '__main__':
    main()
