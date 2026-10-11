import PaperVerifier.ADComplete.FullRepresentationResources
import PaperVerifier.ADComplete.FullTraceReadout

/-! Polynomial bit bound for the actual final integer scalar observation. -/
namespace ADComplete.FullRepresentationCompiler
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit ADComplete.IntegerBounds
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem compiled_valid (N : ℕ) (b : ℤ) : (compiled N b).2.valid (compiled N b).1 :=
  compress_valid _ _ _ _ _ _ _ _

theorem trace_bits_of_registers {V : Type*} [Fintype V] [DecidableEq V]
    (N E : ℕ) (c : Circuit) (p : PairRef) (hp : p.valid c) (a d : Matrix V V ℤ)
    (hreg : ∀ i, i<c.length → ∀ u v, Nat.size (c.value a d i u v).natAbs≤E)
    (hn : Fintype.card V≤N) : Nat.size ((p.value c a d).1.trace).natAbs≤E+N+1 := by
  have hentry (u v : V) : ((p.value c a d).1 u v).natAbs≤2^E :=
    (Nat.size_le.mp (hreg p.forward hp.1 u v)).le
  have habs : ((p.value c a d).1.trace).natAbs≤2^(E+N) := by
    change (∑ i : V, (p.value c a d).1 i i).natAbs≤_
    calc
      _ ≤ ∑ i : V, ((p.value c a d).1 i i).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _i : V, 2^E := Finset.sum_le_sum (fun i _ => hentry i i)
      _ = Fintype.card V*2^E := by simp
      _ ≤ N*2^E := Nat.mul_le_mul_right _ hn
      _ ≤ 2^N*2^E := Nat.mul_le_mul_right _ N.lt_two_pow_self.le
      _ = 2^(E+N) := by rw [←pow_add]; congr 1; omega
  have hh := Nat.size_le_size habs
  simpa only [Nat.size_pow] using hh

theorem actual_final_trace_bits {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1≤N) (hn : Fintype.card V≤N) :
    Nat.size (trace N G).natAbs≤320*N^12+N+2 := by
  have hh := trace_bits_of_registers N (320*N^12+1)
    (compiled N (radixNat (N^2))).1 (compiled N (radixNat (N^2))).2
    (compiled_valid N (radixNat (N^2))) (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (actual_register_entry_bits G N hN hn) hn
  change Nat.size (trace N G).natAbs≤320*N^12+1+N+1 at hh
  omega

#print axioms actual_final_trace_bits
end ADComplete.FullRepresentationCompiler
