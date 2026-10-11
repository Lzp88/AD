import PaperVerifier.ADComplete.InstructionCompressionHeights
import PaperVerifier.ADComplete.InstructionNormBridge
import PaperVerifier.ADComplete.IntegerBitBounds

/-! Actual shared-DAG resources for the public compiler. The height exponent
is deliberately coarse; it proves polynomial bit complexity for every
intermediate matrix register, rather than just the final output. -/
namespace ADComplete.InstructionHeights
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.InstructionDegrees (compiled)
open ADComplete.IntegerBounds
open scoped Matrix.Norms.Operator NNReal

theorem prefix_count_le_square (N : ℕ) (hN : 1 ≤ N) :
    (probePrefix N).probes.length ≤ N^2 := by
  have hm := build_twice_probe_count N (N-1)
  have he : N-1+1=N := by omega
  rw [he] at hm
  have he2 : N-1+2=N+1 := by omega
  rw [he2] at hm
  change 2*(probePrefix N).probes.length = N*(N+1) at hm
  nlinarith

theorem compiled_all_weights (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    AllBound (compiled N b).1 (20*N^4) := by
  by_cases he : N=1
  · subst N
    simpa only [compiled, ite_true, Nat.one_pow, Nat.mul_one] using
      all_mono initial_all (show 1 ≤ 20 by norm_num)
  · have h2 : 2 ≤ N := by omega
    let M := (probePrefix N).probes.length
    let T := 4*N+2*(3*(N-1))+3*(M*M)+3*M+4
    have gp := probe_build_grade N (N-1)
    have hi := initial_grade_extend initial_grade (build_extends N (N-1))
    have hp : AllBound (probePrefix N).circuit T := all_mono gp.1 (by dsimp [T]; omega)
    have gj := distance_build_grade N h2 hp hi (by dsimp [T]; omega)
    have ex := CircuitAudit.DistanceCircuit.build_extends N (probePrefix N).circuit
    have hh := initial_grade_extend hi ex
    have gf := compress_grade gj.1 hh.1 hh.2.1 hh.2.2.1 gj.2
      (probePrefix N).probes rfl (fun p h => pair_extend (gp.2.2 p h) ex) b
    have hM : M ≤ N^2 := prefix_count_le_square N hN
    have hM2 : M*M ≤ (N^2)*(N^2) := Nat.mul_le_mul hM hM
    have hn2 : N ≤ N^2 := by nlinarith
    have hn4 : N^2 ≤ N^4 := by nlinarith [sq_nonneg (N^2-1 : ℤ)]
    have hT : T ≤ 20*N^4 := by
      dsimp [T]
      nlinarith [Nat.sub_le N 1]
    unfold compiled
    rw [if_neg he]
    exact all_mono gf.1 hT

theorem compiled_gate_bound (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    (compiled N b).1.length ≤ 61*N^2 := by
  unfold compiled
  split
  · subst N; norm_num [initial_length]
  · exact CircuitAudit.FullCompression.full_gate_bound N hN b

theorem constants_mono {c : Circuit} {S T : Set ℤ}
    (hc : c.constantsAllowed S) (h : S ⊆ T) : c.constantsAllowed T := by
  induction c with
  | empty => trivial
  | snoc c g ih =>
    refine ⟨ih hc.1, ?_⟩
    cases g <;> try trivial
    exact h hc.2

def KNat (N : ℕ) : ℕ := radixNat N+N^3+2

theorem KNat_two_le (N : ℕ) : 2 ≤ KNat N := by unfold KNat; omega

theorem compiled_constants_bound (N : ℕ) (hN : 1 ≤ N) :
    (compiled N (radixNat N)).1.constantsAllowed {z | |(z : ℝ)| ≤ (KNat N : ℝ)} := by
  unfold compiled
  split
  · simp [initial, Circuit.constantsAllowed, Gate.constantsAllowed]
  · apply constants_mono (CircuitAudit.FullCompression.full_constants N (radixNat N))
    intro z hz
    have hzB := CircuitAudit.FullCompression.scalarConstants_abs_bound N hN (radixNat N) hz
    have hc : |z| ≤ (KNat N : ℤ) := by
      apply hzB.trans
      have hb0 : 0 ≤ (radixNat N : ℤ) := Nat.cast_nonneg _
      have hcub0 : 0 ≤ (N : ℤ)^3 := by positivity
      apply max_le
      · simp only [KNat, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, abs_of_nonneg hb0]
        linarith
      · simp only [KNat, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
        linarith
    exact_mod_cast hc

theorem KNat_binary_bound (N : ℕ) (hN : 1 ≤ N) : KNat N ≤ 2^(16*N^2) := by
  have hb : radixNat N ≤ 2^(14*N^2) :=
    (radixNat_binary_bound N hN).trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hn : N^3 ≤ 2^(14*N^2) := by
    have hl : N^3 ≤ LNat N := by unfold LNat; omega
    exact (hl.trans (LNat_binary_bound N hN)).trans
      (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have h2 : 2 ≤ 2^(14*N^2) := by
    have he : 1 ≤ 14*N^2 := by nlinarith
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) he
  calc
    KNat N = radixNat N+N^3+2 := rfl
    _ ≤ 4*2^(14*N^2) := by omega
    _ = 2^(14*N^2+2) := by rw [pow_add]; ring
    _ ≤ 2^(16*N^2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem actual_register_norm_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) (i : ℕ) (hi : i < (compiled N (radixNat N)).1.length) :
    ‖(compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i‖ ≤
      (2 : ℝ)^(320*N^6) := by
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hNK : N ≤ KNat N := by unfold KNat; omega
  have hNKR : (N : ℝ) ≤ KNat N := by exact_mod_cast hNK
  have hK2 : (2 : ℝ) ≤ KNat N := by exact_mod_cast KNat_two_le N
  have hK1 : (1 : ℝ) ≤ KNat N := by linarith
  have h := every_register_norm_bound (KNat N) hK2 (G.adjMatrix ℤ) (G.degMatrix ℤ)
    ((adjacency_norm_bound G N hn).trans hNKR) ((degree_norm_bound G N hn).trans hNKR)
    (compiled N (radixNat N)).1 (compiled_constants_bound N hN) i
  have hw := compiled_all_weights N hN (radixNat N) i hi
  have hKB : (KNat N : ℝ) ≤ (2 : ℝ)^(16*N^2) := by exact_mod_cast KNat_binary_bound N hN
  calc
    _ ≤ (KNat N : ℝ)^(weight (compiled N (radixNat N)).1 i) := h
    _ ≤ (KNat N : ℝ)^(20*N^4) := pow_le_pow_right₀ hK1 hw
    _ ≤ ((2 : ℝ)^(16*N^2))^(20*N^4) := pow_le_pow_left₀ (by positivity) hKB _
    _ = (2 : ℝ)^(320*N^6) := by rw [← pow_mul]; congr 1; ring

theorem entry_norm_le_opNorm {V : Type*} [Fintype V]
    (X : Matrix V V ℤ) (i j : V) : ‖X i j‖ ≤ ‖X‖ := by
  calc
    _ ≤ ∑ k : V, ‖X i k‖ := Finset.single_le_sum (fun k _ => norm_nonneg (X i k)) (Finset.mem_univ j)
    _ ≤ ‖X‖ := row_abs_sum_le_opNorm X i

theorem actual_register_entry_binary_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) (i : ℕ) (hi : i < (compiled N (radixNat N)).1.length)
    (u v : V) :
    ((compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs ≤
      2^(320*N^6) := by
  have h := (entry_norm_le_opNorm _ u v).trans (actual_register_norm_bound G N hN hn i hi)
  rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem actual_register_entry_bits {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) (i : ℕ) (hi : i < (compiled N (radixNat N)).1.length)
    (u v : V) :
    Nat.size ((compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs ≤
      320*N^6+1 := by
  have h := Nat.size_le_size (actual_register_entry_binary_bound G N hN hn i hi u v)
  simpa only [Nat.size_pow] using h

#print axioms compiled_all_weights
#print axioms actual_register_norm_bound
#print axioms actual_register_entry_bits
end ADComplete.InstructionHeights
