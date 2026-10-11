import PaperVerifier.ADComplete.InstructionSharpBits
import PaperVerifier.ADComplete.CompiledReadout

/-! Explicit sharp binary lengths for every actual scalar label and the
literal final trace. These statements include the N=1 identity branch. -/
namespace ADComplete.MainResourceEndpoints
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.InstructionDegrees (compiled)
open ADComplete.InstructionHeights ADComplete.IntegerBounds
open scoped BigOperators Matrix.Norms.Operator

theorem compiled_output_valid (N : ℕ) (b : ℤ) :
    (compiled N b).2.valid (compiled N b).1 := by
  unfold compiled
  split
  · exact initial_ready.1
  · exact CircuitAudit.FullCompression.full_valid N b

/-- Binary lengths of all scalar labels actually stored in the main compiler,
including the radix input; the bound is O(N log(N+1)). -/
theorem main_scalar_label_bits (N : ℕ) (hN : 1 ≤ N) :
    (compiled N (radixNat N)).1.constantsAllowed
      {z | Nat.size z.natAbs ≤ 8*N*(ell N+1)+5} := by
  apply constants_mono (compiled_constants_bound N hN)
  intro z hz
  have hn : z.natAbs ≤ KNat N := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact_mod_cast hz
  have hp := hn.trans (KNat_log_bound N hN)
  change Nat.size z.natAbs ≤ 8*N*(ell N+1)+5
  simpa only [Nat.size_pow, KBits, Nat.add_assoc] using Nat.size_le_size hp

/-- Every scalar label of the literal shared triangular probe prefix has
O(log(N+1)) bits; no evaluated-input bound is assumed. -/
theorem probe_prefix_scalar_label_bits (N : ℕ) (hN : 1 ≤ N) :
    (probePrefix N).circuit.constantsAllowed
      {z | Nat.size z.natAbs ≤ 3*ell N+1} := by
  apply constants_mono (prefix_constants N)
  intro z hz
  have hn : z.natAbs ≤ N^3 := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    simpa only [Nat.cast_pow] using probeConstants_abs_bound N hN hz
  have hp : N^3 ≤ 2^(3*ell N) := by
    have hh := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num : 1 < 2) N) 3
    simpa only [← pow_mul, ell, Nat.mul_comm] using hh
  change Nat.size z.natAbs ≤ 3*ell N+1
  simpa only [Nat.size_pow] using Nat.size_le_size (hn.trans hp)

theorem actual_output_norm_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) :
    ‖CompiledReadout.output N (radixNat N) G‖ ≤
      (2 : ℝ)^(20*N^4*KBits N) := by
  have hv := (compiled_output_valid N (radixNat N)).1
  have hh := actual_register_symbolic_norm G N hN hn _ hv
  have hK : (KNat N : ℝ) ≤ (2 : ℝ)^(KBits N) := by
    exact_mod_cast KNat_log_bound N hN
  change ‖(compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ)
      (compiled N (radixNat N)).2.forward‖ ≤ _
  apply hh.trans
  calc
    _ ≤ ((2 : ℝ)^(KBits N))^(20*N^4) := pow_le_pow_left₀ (by positivity) hK _
    _ = _ := by rw [← pow_mul]; congr 1; ring

/-- The literal final trace, rather than only the final matrix entries,
has O(N^5 log(N+1)) bits on every actual nonempty simple graph of order ≤N. -/
theorem actual_graph_final_trace_bits {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) :
    Nat.size (CompiledReadout.trace N (radixNat N) G).natAbs ≤
      20*N^4*(8*N*(ell N+1)+4)+ell N+1 := by
  let X := CompiledReadout.output N (radixNat N) G
  let E := 20*N^4*KBits N
  have he (v : V) : (X v v).natAbs ≤ 2^E := by
    have hh := (entry_norm_le_opNorm X v v).trans (actual_output_norm_bound G N hN hn)
    rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs] at hh
    exact_mod_cast hh
  have ht : (Matrix.trace X).natAbs ≤ Fintype.card V * 2^E := by
    change (∑ v : V, X v v).natAbs ≤ _
    calc
      _ ≤ ∑ v : V, (X v v).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _v : V, 2^E := Finset.sum_le_sum (fun v _ => he v)
      _ = _ := by simp
  have hc : Fintype.card V ≤ 2^(ell N) :=
    hn.trans (Nat.le_pow_clog (by norm_num : 1 < 2) N)
  have hb : (Matrix.trace X).natAbs ≤ 2^(E+ell N) := by
    calc
      _ ≤ Fintype.card V * 2^E := ht
      _ ≤ 2^(ell N) * 2^E := Nat.mul_le_mul_right _ hc
      _ = _ := by rw [← pow_add, Nat.add_comm]
  have hs := Nat.size_le_size hb
  simpa only [Nat.size_pow, E, KBits, X, CompiledReadout.trace] using hs

/-- Public tree specialization discharges nonemptiness from the actual tree. -/
theorem actual_tree_final_trace_bits {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (N : ℕ) (hN : 1 ≤ N) (hn : Fintype.card V ≤ N) :
    Nat.size (CompiledReadout.trace N (radixNat N) G).natAbs ≤
      20*N^4*(8*N*(ell N+1)+4)+ell N+1 := by
  let : Nonempty V := hG.connected.nonempty
  exact actual_graph_final_trace_bits G N hN hn

#print axioms main_scalar_label_bits
#print axioms probe_prefix_scalar_label_bits
#print axioms actual_tree_final_trace_bits
end ADComplete.MainResourceEndpoints
