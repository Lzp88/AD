import PaperVerifier.ADComplete.FullRepresentationCompiler
import PaperVerifier.ADComplete.FrobeniusTreeReconstruction

/-! Exact integer radix decoding of the original-order no-J compiler. -/
namespace ADComplete.FullRepresentationCompiler
open Matrix CircuitAudit.Degrees CircuitAudit.RadixFactorization
open CircuitAudit.ProbeCircuit
open ADComplete.IntegerBounds ADComplete.InstructionHeights
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def integerProbes (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :=
  CompiledReadout.integerProbes (N^2) G

def output (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℤ :=
  ((compiled N (radixNat (N^2))).2.value (compiled N (radixNat (N^2))).1
    (G.adjMatrix ℤ) (G.degMatrix ℤ)).1

def trace (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ := (output N G).trace

omit [Fintype W] [DecidableEq W] in
theorem output_source (N : ℕ) (hN : 1≤N) (G : SimpleGraph V) [DecidableRel G.Adj] :
    output N G=sourcePolynomial (radixNat (N^2)) (1 : Matrix V V ℤ)
      (integerProbes N G) (coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ)) := by
  rw [output,compiled_value N hN]
  simp only [exprPair,expression]
  rw [CircuitAudit.WrittenPolynomialBridge.factored_eq_source (radixNat (N^2))
    (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (G.isHermitian_adjMatrix ℤ) (G.isHermitian_degMatrix ℤ) .one (probeList (N^2) (N^2))]
  simp only [Expr.eval]
  rw [CompiledReadout.sourcePolynomial_reindex_length (List.length_map ..)]
  congr 1
  funext i
  simp only [integerProbes,CompiledReadout.integerProbes,List.get_eq_getElem,List.getElem_map,Fin.val_cast]

omit [Fintype W] [DecidableEq W] in
theorem trace_norm_bound (X : Matrix V V ℤ) : ‖X.trace‖≤(Fintype.card V : ℝ)*‖X‖ := by
  calc
    _ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : V, ‖X‖ := Finset.sum_le_sum (fun i _ => entry_norm_le_opNorm X i i)
    _ = _ := by simp

omit [Fintype W] [DecidableEq W] in
theorem actual_trace_digit_bound (N : ℕ) (hN : 1≤N)
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hn : Fintype.card V≤N)
    (s : Fin 3) (i j : Fin (probeList (N^2) (N^2)).length) :
    |((star (integerProbes N G i)*coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s)*
      integerProbes N G j).trace|≤(HNat (N^2) : ℤ) := by
  have hS : 1≤N^2 := by nlinarith
  have hnS : Fintype.card V≤N^2 := hn.trans (by nlinarith)
  have hi := probe_norm_uniform (N^2) hS (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (adjacency_norm_bound G (N^2) hnS) (degree_norm_bound G (N^2) hnS)
    ((probeList (N^2) (N^2)).get i) (List.get_mem _ i)
  have hj := probe_norm_uniform (N^2) hS (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (adjacency_norm_bound G (N^2) hnS) (degree_norm_bound G (N^2) hnS)
    ((probeList (N^2) (N^2)).get j) (List.get_mem _ j)
  have hrev := reverse_eval (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (G.isHermitian_adjMatrix ℤ) (G.isHermitian_degMatrix ℤ) ((probeList (N^2) (N^2)).get i)
  have hu : ‖star (integerProbes N G i)‖≤(RNat (N^2) : ℝ) := by
    simpa only [integerProbes,CompiledReadout.integerProbes,←hrev] using hi.2
  have hv : ‖integerProbes N G j‖≤(RNat (N^2) : ℝ) := hj.1
  have hcore := core_slot_norm_bound G (N^2) hS hnS s
  have hab := mul_bound hu hcore (by positivity) (by positivity)
  have hx := mul_bound hab hv (by positivity) (by positivity)
  have hc : (Fintype.card V : ℝ)≤(N^2 : ℕ) := by exact_mod_cast hnS
  have ht := trace_norm_bound ((star (integerProbes N G i)*coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s)*integerProbes N G j)
  have hh : ‖((star (integerProbes N G i)*coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s)*integerProbes N G j).trace‖≤
      ((N^2 : ℕ) : ℝ)^2*(RNat (N^2) : ℝ)^2 := by
    apply ht.trans
    calc
      _ ≤ ((N^2 : ℕ) : ℝ)*((RNat (N^2) : ℝ)*(N^2 : ℕ)*RNat (N^2)) :=
        mul_le_mul hc hx (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [Int.norm_eq_abs] at hh
  unfold HNat
  exact_mod_cast hh

omit [Fintype W] [DecidableEq W] in
theorem sourceCode_trace_identity {Q : ℕ} (b : ℤ) (X : Fin Q → Matrix V V ℤ) :
    (TreeSeparation.sourceCode b (1 : Matrix V V ℤ) X).trace=
      2*Radix.encode b (List.ofFn (fun i => (X i).trace)) := by
  rw [TreeSeparation.sourceCode,Matrix.trace_sum,TreeSeparation.encode_ofFn_eq_sum]
  simp_rw [Matrix.trace_smul,TreeSeparation.trace_symmetrized,Matrix.one_mul]
  simp only [zsmul_eq_mul,Int.cast_id]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem source_trace_recovers_tables {M : ℕ} {H b : ℤ} (hH : 0≤H) (hb : 2*H<b)
    (U : Fin M → Matrix V V ℤ) (T : Fin M → Matrix W W ℤ)
    (S : Fin 3 → Matrix V V ℤ) (R : Fin 3 → Matrix W W ℤ)
    (hU : ∀ s i j, |((star (U i)*S s)*U j).trace|≤H)
    (hT : ∀ s i j, |((star (T i)*R s)*T j).trace|≤H)
    (ht : (sourcePolynomial b (1 : Matrix V V ℤ) U S).trace=
      (sourcePolynomial b (1 : Matrix W W ℤ) T R).trace) :
    ∀ s i j, ((star (U i)*S s)*U j).trace=((star (T i)*R s)*T j).trace := by
  rw [TreeSeparation.sourcePolynomial_eq_sourceCode,TreeSeparation.sourcePolynomial_eq_sourceCode,
    sourceCode_trace_identity,sourceCode_trace_identity] at ht
  have he : Radix.encode b (List.ofFn (fun q => (TreeSeparation.indexedTable U S q).trace))=
      Radix.encode b (List.ofFn (fun q => (TreeSeparation.indexedTable T R q).trace)) :=
    mul_left_cancel₀ (by norm_num : (2 : ℤ)≠0) ht
  have hBU : Radix.Bounded H (List.ofFn (fun q => (TreeSeparation.indexedTable U S q).trace)) := by
    intro a ha
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp ha
    exact hU _ _ _
  have hBT : Radix.Bounded H (List.ofFn (fun q => (TreeSeparation.indexedTable T R q).trace)) := by
    intro a ha
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp ha
    exact hT _ _ _
  have hh := List.ofFn_injective (Radix.encode_injective_of_bounded hH hb (by simp) hBU hBT he)
  intro s i j
  simpa only [TreeSeparation.indexedTable_index] using congrFun hh (TreeSeparation.tableIndex M ((s,i),j))

theorem actual_trace_recovers_tables (N : ℕ) (hN : 1≤N)
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (H : SimpleGraph W) [DecidableRel H.Adj] [Nonempty W]
    (hnG : Fintype.card V≤N) (hnH : Fintype.card W≤N) (ht : trace N G=trace N H) :
    ∀ s i j, ((star (integerProbes N G i)*coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s)*integerProbes N G j).trace=
      ((star (integerProbes N H i)*coreSlots (H.adjMatrix ℤ) (H.degMatrix ℤ) s)*integerProbes N H j).trace := by
  unfold trace at ht
  rw [output_source N hN G,output_source N hN H] at ht
  exact source_trace_recovers_tables (Nat.cast_nonneg _) (actual_radix_large (N^2)) _ _ _ _
    (actual_trace_digit_bound N hN G hnG) (actual_trace_digit_bound N hN H hnH) ht

#print axioms actual_trace_digit_bound
#print axioms actual_trace_recovers_tables
end
end ADComplete.FullRepresentationCompiler
