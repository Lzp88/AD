import PaperVerifier.ADComplete.FullTraceReadout
import PaperVerifier.ADComplete.FrobeniusTreeTables

/-! Actual graph-isomorphism endpoint for the original-order full trace DAG.
The formal reconstruction bridge uses the audited pointed theorem. -/
namespace ADComplete.FullRepresentationCompiler
open Matrix CircuitAudit.Degrees CircuitAudit.RadixFactorization ADComplete.MatrixSemantics
open CircuitAudit.ProbeCircuit
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
theorem trace_cast (X : Matrix V V ℤ) : (X.trace : ℝ)=(realMatrix X).trace := by
  simp [Matrix.trace,Matrix.diag]

omit [Fintype W] [DecidableEq W] in
theorem probe_cast (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin (probeList (N^2) (N^2)).length) :
    realMatrix (integerProbes N G i)=FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i := by
  simp [integerProbes,CompiledReadout.integerProbes,FrameSemantics.probeMatrices]

omit [Fintype W] [DecidableEq W] in
theorem digit_cast (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Fin 3) (i j : Fin (probeList (N^2) (N^2)).length) :
    (((star (integerProbes N G i)*coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s)*integerProbes N G j).trace : ℝ)=
      ((FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i).transpose*
        coreSlots (G.adjMatrix ℝ) (G.degMatrix ℝ) s*
        FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) j).trace := by
  rw [trace_cast,realMatrix_mul,realMatrix_mul,realMatrix_star,probe_cast,probe_cast]
  fin_cases s <;> simp [coreSlots]

theorem actual_trace_implies_full_tables (N : ℕ) (hN : 1≤N)
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (H : SimpleGraph W) [DecidableRel H.Adj] [Nonempty W]
    (hnG : Fintype.card V≤N) (hnH : Fintype.card W≤N) (ht : trace N G=trace N H) :
    Frobenius.fullThreeTablesEqual N G H := by
  have hh := actual_trace_recovers_tables N hN G H hnG hnH ht
  have hr (s : Fin 3) (i j : Fin (probeList (N^2) (N^2)).length) :=
    congrArg (fun z : ℤ => (z : ℝ)) (hh s i j)
  simp_rw [digit_cast] at hr
  constructor
  · intro i j
    simpa [coreSlots] using hr 0 i j
  · intro b i j
    cases b
    · simpa [coreSlots,PrincipalMomentAudit.GraphSemantics.generatorMatrix,
        Matrix.mul_assoc] using hr 1 i j
    · simpa [coreSlots,PrincipalMomentAudit.GraphSemantics.generatorMatrix,
        Matrix.mul_assoc] using hr 2 i j

theorem graphIso_preserves_trace (N : ℕ) (hN : 1≤N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) : trace N G=trace N H := by
  have hr := CompiledReadout.expression_reindex e.toEquiv (expression N (ADComplete.IntegerBounds.radixNat (N^2)))
    (G.adjMatrix ℤ) (G.degMatrix ℤ)
  have ha : Matrix.reindexAlgEquiv ℤ ℤ e.toEquiv (G.adjMatrix ℤ)=H.adjMatrix ℤ := e.reindex_adjMatrix ℤ
  rw [CompiledReadout.reindex_degree G H e,ha] at hr
  unfold trace output
  rw [compiled_value N hN,compiled_value N hN]
  simp only [exprPair]
  rw [←hr,CompiledReadout.trace_reindex]

theorem actual_compiled_trace_iff_graphIso (N : ℕ) (hN : 1≤N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V≤N) (hnH : Fintype.card W≤N) :
    trace N G=trace N H ↔ Nonempty (G ≃g H) := by
  let : Nonempty V := hG.connected.nonempty
  let : Nonempty W := hH.connected.nonempty
  constructor
  · intro ht
    exact (Frobenius.public_full_three_tables_classify_trees N hN G H hG hH hnG hnH).mp
      (actual_trace_implies_full_tables N hN G H hnG hnH ht)
  · rintro ⟨e⟩
    exact graphIso_preserves_trace N hN G H e

#print axioms actual_compiled_trace_iff_graphIso
end
end ADComplete.FullRepresentationCompiler
