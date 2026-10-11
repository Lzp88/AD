import PaperVerifier.ADComplete.FrobeniusTreeReconstruction

/-! Actual Frobenius tables classify trees. The graph endpoint reuses the
audited pointed reconstruction theorem through the literal all-one expression. -/

namespace ADComplete.Frobenius

open Matrix CircuitAudit.Degrees PrincipalMomentAudit
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def fullThreeTablesEqual (N : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  (∀ i j : Fin (probeList (N^2) (N^2)).length,
    ((FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i).transpose *
      FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) j).trace =
    ((FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) i).transpose *
      FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) j).trace) ∧
  (∀ b i j,
    ((FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i).transpose *
      (GraphSemantics.generatorMatrix G b *
        FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) j)).trace =
    ((FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) i).transpose *
      (GraphSemantics.generatorMatrix H b *
        FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) j)).trace)

lemma real_expression_reindex (e : V ≃ W) (p : Expr) (A D : Matrix V V ℝ) :
    Matrix.reindexAlgEquiv ℝ ℝ e (p.eval A D) =
      p.eval (Matrix.reindexAlgEquiv ℝ ℝ e A) (Matrix.reindexAlgEquiv ℝ ℝ e D) := by
  induction p <;> simp only [Expr.eval, map_zero, map_one, map_zsmul, map_add, map_mul, *]

lemma real_reindex_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (e : G ≃g H) :
    Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv (G.degMatrix ℝ) = H.degMatrix ℝ := by
  ext i j
  change (G.degMatrix ℝ) (e.symm i) (e.symm j) = (H.degMatrix ℝ) i j
  simp only [SimpleGraph.degMatrix, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [if_true]
    exact_mod_cast e.symm.degree_eq i
  · have hne : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simp only [hij, hne, if_false]

lemma real_trace_reindex (e : V ≃ W) (X : Matrix V V ℝ) :
    Matrix.trace (Matrix.reindexAlgEquiv ℝ ℝ e X) = Matrix.trace X := by
  change (∑ i : W, X (e.symm i) (e.symm i)) = ∑ i : V, X i i
  exact e.symm.sum_comp (fun i => X i i)

theorem graphIso_preserves_real_expression_trace
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) (p : Expr) :
    (p.eval (G.adjMatrix ℝ) (G.degMatrix ℝ)).trace =
      (p.eval (H.adjMatrix ℝ) (H.degMatrix ℝ)).trace := by
  have hr := real_expression_reindex e.toEquiv p (G.adjMatrix ℝ) (G.degMatrix ℝ)
  have ha : Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv (G.adjMatrix ℝ) = H.adjMatrix ℝ :=
    e.reindex_adjMatrix ℝ
  rw [real_reindex_degree G H e, ha] at hr
  rw [← hr, real_trace_reindex]

omit [Fintype W] [DecidableEq W] in
lemma graph_expression_reverse (G : SimpleGraph V) [DecidableRel G.Adj] (p : Expr) :
    p.reverse.eval (G.adjMatrix ℝ) (G.degMatrix ℝ) =
      (p.eval (G.adjMatrix ℝ) (G.degMatrix ℝ)).transpose := by
  rw [reverse_eval (G.adjMatrix ℝ) (G.degMatrix ℝ)
    (G.isHermitian_adjMatrix ℝ) (G.isHermitian_degMatrix ℝ) p]
  exact Matrix.conjTranspose_eq_transpose_of_trivial _

theorem graphIso_preserves_full_three_tables (N : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) : fullThreeTablesEqual N G H := by
  constructor
  · intro i j
    have ht := graphIso_preserves_real_expression_trace G H e
      (.mul ((probeList (N^2) (N^2)).get i).reverse ((probeList (N^2) (N^2)).get j))
    simpa only [Expr.eval, graph_expression_reverse, FrameSemantics.probeMatrices] using ht
  · intro b i j
    have ht := graphIso_preserves_real_expression_trace G H e
      (.mul ((probeList (N^2) (N^2)).get i).reverse
        (.mul (if b then .d else .a) ((probeList (N^2) (N^2)).get j)))
    cases b <;>
      simpa only [Bool.false_eq_true, if_false, if_true, Expr.eval,
        graph_expression_reverse, FrameSemantics.probeMatrices,
        GraphSemantics.generatorMatrix] using ht

theorem public_full_three_tables_classify_trees (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N) :
    fullThreeTablesEqual N G H ↔ Nonempty (G ≃g H) := by
  constructor
  · rintro ⟨hGram, hGen⟩
    exact full_word_traces_determine_trees N G H hG hH hnG hnH
      (full_three_trace_tables_determine_word_traces N hN G H hnG hnH hGram hGen)
  · rintro ⟨e⟩
    exact graphIso_preserves_full_three_tables N G H e

#print axioms graphIso_preserves_full_three_tables
#print axioms public_full_three_tables_classify_trees

end
end ADComplete.Frobenius
