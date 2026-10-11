import PaperVerifier.ADComplete.CompiledReadout

/-! Composition from the actual compiler through the actual polynomial frame.
The intermediate theorem displays the sole remaining spanning premise explicitly;
the uniform-frame theorem discharges this premise in the final integration. -/

namespace ADComplete.TraceMomentBridge
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix CircuitAudit.Degrees PrincipalMomentAudit

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem integerFrame_eq_probeFrame (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    MatrixSemantics.intFrame (CompiledReadout.integerProbes N G) =
      FrameSemantics.probeFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) := by
  funext i
  simp only [MatrixSemantics.intFrame, CompiledReadout.integerProbes,
    MatrixSemantics.realMatrix_eval, MatrixSemantics.realMatrix_adjacency,
    MatrixSemantics.realMatrix_degree, FrameSemantics.probeFrame, FrameSemantics.probeMatrices]

theorem one_mem_probeList (N : ℕ) (hN : 1 ≤ N) : Expr.one ∈ probeList N N := by
  apply (FrameSemantics.probeList_members N N _).mpr
  exact ⟨0, by omega, 0, le_rfl, rfl⟩

theorem integerFrame_seed (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin (probeList N N).length) (hi : (probeList N N).get i = .one) :
    MatrixSemantics.intFrame (CompiledReadout.integerProbes N G) i =
      GraphSemantics.oneSeed (V := V) := by
  simp only [MatrixSemantics.intFrame, CompiledReadout.integerProbes, hi, Expr.eval,
    MatrixSemantics.realMatrix_one, Matrix.one_mulVec, GraphSemantics.oneSeed]

theorem integerFrame_range (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hspan : Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
      z = Spanning.probeVector ((N : ℝ)^2) (G.adjMatrix ℝ) (G.degMatrix ℝ)
        (fun _ => 1) k j} =
      Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1)) :
    LinearMap.range (combination (MatrixSemantics.intFrame (CompiledReadout.integerProbes N G))) =
      principal (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) := by
  rw [integerFrame_eq_probeFrame]
  have hgen : FrameSemantics.generators (G.adjMatrix ℝ) (G.degMatrix ℝ) =
      GraphSemantics.generators G := by
    funext b
    cases b <;> rfl
  simpa only [hgen, GraphSemantics.oneSeed] using
      FrameSemantics.probeFrame_range_eq_principal N (G.adjMatrix ℝ) (G.degMatrix ℝ)
        (fun _ => 1) hspan

/-- Exact composition: only uniform spanning remains a mathematical premise. -/
theorem actual_trace_implies_moments_of_spanning (N : ℕ) (hN : 1 ≤ N) (hne : N ≠ 1)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N)
    (hspanG : Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
      z = Spanning.probeVector ((N : ℝ)^2) (G.adjMatrix ℝ) (G.degMatrix ℝ)
        (fun _ => 1) k j} =
      Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1))
    (hspanH : Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
      z = Spanning.probeVector ((N : ℝ)^2) (H.adjMatrix ℝ) (H.degMatrix ℝ)
        (fun _ => 1) k j} =
      Spanning.jointModule (H.adjMatrix ℝ) (H.degMatrix ℝ) (fun _ => 1))
    (ht : CompiledReadout.trace N (IntegerBounds.radixNat N) G =
      CompiledReadout.trace N (IntegerBounds.radixNat N) H) :
    ∀ w, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) w =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) w := by
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp (one_mem_probeList N hN)
  exact MatrixSemantics.integer_three_tables_determine_graph_moments G H
    (CompiledReadout.integerProbes N G) (CompiledReadout.integerProbes N H)
    (integerFrame_range N G hspanG) (integerFrame_range N H hspanH)
    i₀ (integerFrame_seed N G i₀ hi₀) (integerFrame_seed N H i₀ hi₀)
    (CompiledReadout.actual_trace_recovers_tables N hN hne G H hG hH hnG hnH ht)

omit [DecidableEq V] [DecidableEq W] in
/-- The identity branch at N=1 classifies its only nonempty tree order directly. -/
theorem singleton_trees_isomorphic
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ 1) (hnH : Fintype.card W ≤ 1) :
    Nonempty (G ≃g H) := by
  let : Nonempty V := hG.connected.nonempty
  let : Nonempty W := hH.connected.nonempty
  let : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hnG
  let : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp hnH
  have hc : Fintype.card V = Fintype.card W := by
    have hV : 0 < Fintype.card V := Fintype.card_pos
    have hW : 0 < Fintype.card W := Fintype.card_pos
    omega
  let e := Fintype.equivOfCardEq hc
  refine ⟨{ e with map_rel_iff' := ?_ }⟩
  intro x y
  rw [Subsingleton.elim x y]
  simp

#print axioms actual_trace_implies_moments_of_spanning
#print axioms singleton_trees_isomorphic
end
end ADComplete.TraceMomentBridge
