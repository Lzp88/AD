import PaperVerifier.ADComplete.FrameSemantics
import PaperVerifier.ADComplete.MatrixSemantics
import PaperVerifier.ADComplete.IntegerBitBounds
import PaperVerifier.ADComplete.InstructionDegrees

/-!
# The actual compiled readout

The degree-safe public compiler returns the identity in its N=1 branch.
For N>1 its forward output is exactly the symmetrized source polynomial.
The two branches are kept literal, including their factor-of-two difference.
-/

namespace ADComplete.CompiledReadout
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix CircuitAudit.Degrees PrincipalMomentAudit

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def integerProbes (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (probeList N N).length → Matrix V V ℤ :=
  fun i => ((probeList N N).get i).eval (G.adjMatrix ℤ) (G.degMatrix ℤ)

def output (N : ℕ) (b : ℤ) (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℤ :=
  ((InstructionDegrees.compiled N b).2.value (InstructionDegrees.compiled N b).1
    (G.adjMatrix ℤ) (G.degMatrix ℤ)).1

def trace (N : ℕ) (b : ℤ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  Matrix.trace (output N b G)

theorem output_one (b : ℤ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    output 1 b G = 1 :=
  congrArg Prod.fst (InstructionDegrees.compiled_one_value b (G.adjMatrix ℤ) (G.degMatrix ℤ))

theorem trace_one (b : ℤ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    trace 1 b G = (Fintype.card V : ℤ) := by
  rw [trace, output_one, Matrix.trace_one]

theorem output_eq_expression (N : ℕ) (hN : 1 ≤ N) (b : ℤ)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    output N b G = if N = 1 then 1 else
      (factored b (allOnes N) (probeList N N)).eval (G.adjMatrix ℤ) (G.degMatrix ℤ) := by
  by_cases h : N = 1
  · subst N
    simp only [output_one, if_true]
  · simp only [output, InstructionDegrees.compiled, h, if_false]
    exact congrArg Prod.fst
      (CircuitAudit.FullCompression.full_output_expr N hN b (G.adjMatrix ℤ) (G.degMatrix ℤ))

theorem sourcePolynomial_reindex_length {R : Type*} [Ring R] [StarRing R]
    {M L : ℕ} (h : M = L) (b : ℤ) (J : R) (U : Fin M → R) (S : Fin 3 → R) :
    CircuitAudit.RadixFactorization.sourcePolynomial b J U S =
      CircuitAudit.RadixFactorization.sourcePolynomial b J (fun i : Fin L => U (Fin.cast h.symm i)) S := by
  subst L
  rfl

theorem output_eq_source (N : ℕ) (hN : 1 ≤ N) (hne : N ≠ 1) (b : ℤ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (hn : Fintype.card V ≤ N) :
    output N b G = CircuitAudit.RadixFactorization.sourcePolynomial b
      (TreeDistance.onesMatrix (V := V)) (integerProbes N G)
      (CircuitAudit.RadixFactorization.coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ)) := by
  rw [output_eq_expression N hN b G, if_neg hne,
    CircuitAudit.WrittenPolynomialBridge.factored_eq_source b (G.adjMatrix ℤ) (G.degMatrix ℤ)
      (G.isHermitian_adjMatrix ℤ) (G.isHermitian_degMatrix ℤ) (allOnes N) (probeList N N),
    TreeDistance.actual_allOnes_expression_identity G hG hn]
  rw [sourcePolynomial_reindex_length (List.length_map ..)]
  congr 1
  funext i
  simp only [integerProbes, List.get_eq_getElem, List.getElem_map, Fin.val_cast]

theorem actual_digit_bound (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (hn : Fintype.card V ≤ N) (s : Fin 3) (i j : Fin (probeList N N).length) :
    |TreeSeparation.doubleSum ((star (integerProbes N G i) *
      CircuitAudit.RadixFactorization.coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s) *
        integerProbes N G j)| ≤ (IntegerBounds.HNat N : ℤ) := by
  let : Nonempty V := hG.connected.nonempty
  exact IntegerBounds.actual_probe_digit_bound G N hN hn _ _
    (List.get_mem _ i) (List.get_mem _ j) s

/-- No digit-bound or all-ones premise: these are derived from the actual trees. -/
theorem actual_trace_recovers_tables (N : ℕ) (hN : 1 ≤ N) (hne : N ≠ 1)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N)
    (ht : trace N (IntegerBounds.radixNat N) G = trace N (IntegerBounds.radixNat N) H) :
    ∀ s i j, TreeSeparation.doubleSum ((star (integerProbes N G i) *
        CircuitAudit.RadixFactorization.coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s) *
          integerProbes N G j) =
      TreeSeparation.doubleSum ((star (integerProbes N H i) *
        CircuitAudit.RadixFactorization.coreSlots (H.adjMatrix ℤ) (H.degMatrix ℤ) s) *
          integerProbes N H j) := by
  unfold trace at ht
  rw [output_eq_source N hN hne _ G hG hnG,
    output_eq_source N hN hne _ H hH hnH] at ht
  exact TreeSeparation.sourcePolynomial_trace_recovers_tables (Nat.cast_nonneg _)
    (IntegerBounds.actual_radix_large N) _ _ _ _
    (actual_digit_bound N hN G hG hnG) (actual_digit_bound N hN H hH hnH) ht

theorem reindex_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (e : G ≃g H) :
    Matrix.reindexAlgEquiv ℤ ℤ e.toEquiv (G.degMatrix ℤ) = H.degMatrix ℤ := by
  ext i j
  change (G.degMatrix ℤ) (e.symm i) (e.symm j) = (H.degMatrix ℤ) i j
  simp only [SimpleGraph.degMatrix, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [if_true]
    exact_mod_cast e.symm.degree_eq i
  · have hne : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simp only [hij, hne, if_false]

theorem expression_reindex (e : V ≃ W) (p : Expr) (A D : Matrix V V ℤ) :
    Matrix.reindexAlgEquiv ℤ ℤ e (p.eval A D) =
      p.eval (Matrix.reindexAlgEquiv ℤ ℤ e A) (Matrix.reindexAlgEquiv ℤ ℤ e D) := by
  induction p <;> simp only [Expr.eval, map_zero, map_one, map_zsmul, map_add, map_mul, *]

theorem trace_reindex (e : V ≃ W) (X : Matrix V V ℤ) :
    Matrix.trace (Matrix.reindexAlgEquiv ℤ ℤ e X) = Matrix.trace X := by
  change (∑ i : W, X (e.symm i) (e.symm i)) = ∑ i : V, X i i
  exact e.symm.sum_comp (fun i => X i i)

/-- Relabeling preserves the actual compiled trace, including its identity branch. -/
theorem graphIso_preserves_trace (N : ℕ) (hN : 1 ≤ N) (b : ℤ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) : trace N b G = trace N b H := by
  have hr : Matrix.reindexAlgEquiv ℤ ℤ e.toEquiv (output N b G) = output N b H := by
    rw [output_eq_expression N hN b G, output_eq_expression N hN b H]
    split_ifs
    · exact map_one _
    · rw [expression_reindex, reindex_degree G H e]
      congr 1
      exact e.reindex_adjMatrix ℤ
  unfold trace
  rw [← hr, trace_reindex]

#print axioms output_eq_source
#print axioms actual_trace_recovers_tables
#print axioms graphIso_preserves_trace
end
end ADComplete.CompiledReadout
