#!/usr/bin/env python3
"""Uniform integer AD compiler with an identity branch at N=1.

The builder takes N alone. For N>=2 it emits the paired instruction reference,
including explicit reversed products for formal adjoints.
It performs no zero simplification, common-subexpression optimization, or
graph-dependent choice. Only b is supplied as a large scale-gate label.
"""
from __future__ import annotations

import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
from typing import Any

import ad_circuit as ordinary

Pair = tuple[int, int]


class Builder:
    def __init__(self, N: int):
        if isinstance(N, bool) or not isinstance(N, int) or N < 1:
            raise ValueError("N must be a positive integer.")
        self.N = N
        self.nodes: list[dict[str, Any]] = []
        self.degrees: list[int] = []
        for operation, degree in (("zero", 0), ("I", 0), ("A", 1), ("D", 1)):
            self._emit({"op": operation}, degree)
        self.zero, self.one, self.a, self.d = (0, 0), (1, 1), (2, 2), (3, 3)

    def _emit(self, instruction: dict[str, Any], degree: int) -> int:
        index = len(self.nodes)
        self.nodes.append(instruction)
        self.degrees.append(degree)
        return index

    def pair_add(self, p: Pair, q: Pair) -> Pair:
        forward = self._emit({"op": "add", "args": [p[0], q[0]]},
                             max(self.degrees[p[0]], self.degrees[q[0]]))
        reverse = self._emit({"op": "add", "args": [p[1], q[1]]},
                             max(self.degrees[p[1]], self.degrees[q[1]]))
        return forward, reverse

    def pair_mul(self, p: Pair, q: Pair) -> Pair:
        forward = self._emit({"op": "mul", "args": [p[0], q[0]]},
                             self.degrees[p[0]] + self.degrees[q[0]])
        reverse = self._emit({"op": "mul", "args": [q[1], p[1]]},
                             self.degrees[q[1]] + self.degrees[p[1]])
        return forward, reverse

    def pair_scale(self, constant: int, p: Pair) -> Pair:
        forward = self._emit({"op": "scale", "constant": str(constant), "args": [p[0]]},
                             self.degrees[p[0]])
        reverse = self._emit({"op": "scale", "constant": str(constant), "args": [p[1]]},
                             self.degrees[p[1]])
        return forward, reverse

    def pair_zero(self) -> Pair:
        index = self._emit({"op": "zero"}, 0)
        return index, index

    def scalar_base(self, b: int) -> Pair:
        index = self._emit({"op": "scale", "constant": str(b), "args": [self.one[0]]}, 0)
        return index, index

    def pair_power(self, base: Pair, exponent: int) -> Pair:
        result = self.one
        for _ in range(exponent):
            result = self.pair_mul(base, result)
        return result

    def pair_horner(self, base: Pair, probes: list[Pair]) -> Pair:
        result = self.pair_zero()
        for p in reversed(probes):
            product = self.pair_mul(base, result)
            result = self.pair_add(p, product)
        return result

    def probes(self) -> tuple[list[Pair], list[tuple[int, int]]]:
        previous, probes, labels = [self.one], [self.one], [(0, 0)]
        kappa = self.N**2
        for k in range(self.N-1):
            row = []
            for j in range(k+2):
                x = self.pair_scale(kappa*(j-k), self.one)
                y = self.pair_add(self.d, x)
                left = self.pair_mul(y, previous[j] if j <= k else self.zero)
                right = self.pair_mul(self.a, previous[j-1] if j > 0 else self.zero)
                scaled_right = self.pair_scale(kappa, right)
                row.append(self.pair_add(left, scaled_right))
                labels.append((k+1, j))
            probes.extend(row)
            previous = row
        return probes, labels

    def all_ones(self) -> Pair:
        aa = self.pair_mul(self.a, self.a)
        negative_d = self.pair_scale(-1, self.d)
        p2 = self.pair_add(aa, negative_d)
        first_sum = self.pair_add(self.one, self.a)
        total = self.pair_add(first_sum, p2)
        negative_identity = self.pair_scale(-1, self.one)
        d_minus_identity = self.pair_add(self.d, negative_identity)
        previous, current = self.a, p2
        for _ in range(max(self.N-3, 0)):
            ac = self.pair_mul(self.a, current)
            dp = self.pair_mul(d_minus_identity, previous)
            negative_product = self.pair_scale(-1, dp)
            following = self.pair_add(ac, negative_product)
            total = self.pair_add(total, following)
            previous, current = current, following
        if self.N == 1:
            return self.one
        if self.N == 2:
            return first_sum
        return total

    def compress(self, probes: list[Pair], j: Pair, b: int) -> tuple[Pair, dict[str, Pair]]:
        m = len(probes)
        base = self.scalar_base(b)
        stride = self.pair_power(base, m)
        block = self.pair_power(stride, m)
        block_squared = self.pair_mul(block, block)
        y = self.pair_horner(base, probes)
        z = self.pair_horner(stride, probes)
        sa = self.pair_mul(block, self.a)
        sd = self.pair_mul(block_squared, self.d)
        s1 = self.pair_add(self.one, sa)
        packed_slot = self.pair_add(s1, sd)
        q1 = self.pair_mul(j, (z[1], z[0]))
        q2 = self.pair_mul(q1, packed_slot)
        q = self.pair_mul(q2, y)
        output = self.pair_add(q, (q[1], q[0]))
        return output, {"base": base, "stride": stride, "block": block,
                        "block_squared": block_squared, "Y": y, "Z": z,
                        "slot": packed_slot, "q": q}

    def build(self) -> dict[str, Any]:
        if len(self.nodes) != 4:
            raise ValueError("Each builder instance emits exactly one circuit.")
        if self.N == 1:
            return {
                "format": "integer-AD-DAG-v1", "N": 1, "kappa": 1,
                "radix": "3", "digit_bound": "1",
                "digit_order": "identity branch (no packing)",
                "probe_labels": [(0, 0)], "probe_nodes": [1],
                "probe_reverse_nodes": [1],
                "all_ones_node": 1, "all_ones_reverse_node": 1,
                "nodes": self.nodes, "output": 1, "reverse_output": 1,
                "formal_degree": 0, "maximum_register_degree": 1,
                "exact_gate_count": 4, "gate_upper_bound": 61,
                "stage_counts": {"probe_prefix": 4, "distance_extra": 0,
                                 "compression_extra": 0},
                "packing_references": {},
                "matrix_register_dimension": "input order n (no lift)",
                "final_readout": "trace(identity), equal to the tree order",
                "emission_policy": "N=1 identity branch; fixed from N alone",
            }
        probes, labels = self.probes()
        probe_length = len(self.nodes)
        j = self.all_ones()
        distance_length = len(self.nodes)-probe_length
        height = self.N**2*(3*self.N**3)**(2*self.N-2)
        radix = 2*height+1
        before_compression = len(self.nodes)
        output, packed = self.compress(probes, j, radix)
        compression_length = len(self.nodes)-before_compression
        expected = 12*self.N**2+12*self.N+27+10*max(self.N-3, 0)
        assert len(self.nodes) == expected <= 61*self.N**2
        assert compression_length == 12*len(probes)+21
        assert self.degrees[output[0]] == self.degrees[output[1]] <= 3*self.N-2
        assert max(self.degrees) <= 3*self.N-2
        return {
            "format": "integer-AD-DAG-v1", "N": self.N, "kappa": self.N**2,
            "radix": str(radix), "digit_bound": str(height),
            "digit_order": "S in [I,A,D], then i, then j",
            "probe_labels": labels, "probe_nodes": [p[0] for p in probes],
            "probe_reverse_nodes": [p[1] for p in probes],
            "all_ones_node": j[0], "all_ones_reverse_node": j[1],
            "nodes": self.nodes, "output": output[0], "reverse_output": output[1],
            "formal_degree": self.degrees[output[0]],
            "maximum_register_degree": max(self.degrees),
            "exact_gate_count": expected, "gate_upper_bound": 61*self.N**2,
            "stage_counts": {"probe_prefix": probe_length,
                             "distance_extra": distance_length,
                             "compression_extra": compression_length},
            "packing_references": packed,
            "matrix_register_dimension": "input order n (no lift)",
            "final_readout": "trace(output), equal to twice the balanced-radix encoding",
            "lean_reference": "CircuitAudit.FullCompression.full",
            "emission_policy": "literal paired reference; no simplification or common-subexpression cache",
        }


def evaluate_generic(circuit: dict[str, Any], a: ordinary.Matrix,
                     d: ordinary.Matrix) -> tuple[ordinary.Matrix, dict[str, int]]:
    """Evaluate ordinary gates on arbitrary integer matrices; no tree premise."""
    n = len(a)
    if n < 1 or len(d) != n or any(len(row) != n for row in a+d):
        raise ValueError("A,D must be square matrices of the same positive order.")
    nodes, output = circuit["nodes"], circuit["output"]
    uses = Counter(argument for node in nodes for argument in node.get("args", []))
    uses[output] += 1
    values, peak_bits, peak_live = {}, 0, 0
    for index, instruction in enumerate(nodes):
        operation, arguments = instruction["op"], instruction.get("args", [])
        if any(argument < 0 or argument >= index for argument in arguments):
            raise ValueError(f"Invalid backwards reference at node {index}.")
        if operation == "zero":
            value = [[0]*n for _ in range(n)]
        elif operation == "I":
            value = ordinary.eye(n)
        elif operation == "A":
            value = [row[:] for row in a]
        elif operation == "D":
            value = [row[:] for row in d]
        elif operation == "add":
            value = ordinary.add(values[arguments[0]], values[arguments[1]])
        elif operation == "mul":
            value = ordinary.mul(values[arguments[0]], values[arguments[1]])
        elif operation == "scale":
            value = ordinary.scale(int(instruction["constant"]), values[arguments[0]])
        else:
            raise ValueError(f"Unsupported operation {operation}.")
        values[index] = value
        peak_bits = max(peak_bits, max(abs(entry).bit_length() for row in value for entry in row))
        for argument in arguments:
            uses[argument] -= 1
            if uses[argument] == 0:
                values.pop(argument, None)
        if uses[index] == 0:
            values.pop(index, None)
        peak_live = max(peak_live, len(values))
    return values[output], {"gates": len(nodes), "peak_entry_bits": peak_bits,
                            "peak_live_registers": peak_live}


def write_circuit(data: dict[str, Any], destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    raw = (json.dumps(data, separators=(",", ":"))+"\n").encode("utf-8")
    if destination.suffix == ".gz":
        with destination.open("wb") as stream:
            with gzip.GzipFile(filename="", mode="wb", fileobj=stream, mtime=0) as compressed:
                compressed.write(raw)
    else:
        destination.write_bytes(raw)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("N", type=int)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = Builder(args.N).build()
    write_circuit(data, args.output)
    print(json.dumps({"N": args.N, "nodes": len(data["nodes"]),
                      "formal_degree": data["formal_degree"], "output": str(args.output)}))


if __name__ == "__main__":
    main()
