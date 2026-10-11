import PaperVerifier.ADComplete.FrobeniusTables
import PaperVerifier.ADComplete.MatrixSemantics
import PaperVerifier.PrincipalMomentAudit.WrittenProof

/-! A formal tree endpoint for the full-representation trace route.
The last reconstruction step reuses the audited pointed word-moment theorem. -/

namespace ADComplete.Frobenius

open Matrix CircuitAudit.Degrees PrincipalMomentAudit
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def realOnesMatrix : Matrix V V ℝ := fun _ _ => 1

def wordExpression : List Bool → Expr
  | [] => .one
  | b :: w => .mul (if b then .d else .a) (wordExpression w)

omit [Fintype W] [DecidableEq W] in
lemma wordExpression_eval (A D : Matrix V V ℝ) (w : List Bool) :
    (wordExpression w).eval A D = matrixWord A D w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [wordExpression, Expr.eval, matrixWord, ih]

omit [Fintype W] [DecidableEq W] in
lemma graph_matrixWord (G : SimpleGraph V) [DecidableRel G.Adj] (w : List Bool) :
    matrixWord (G.adjMatrix ℝ) (G.degMatrix ℝ) w = GraphSemantics.wordMatrix G w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [matrixWord, GraphSemantics.wordMatrix,
      GraphSemantics.generatorMatrix, ih]

omit [Fintype W] [DecidableEq W] in
theorem real_allOnes_expression (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (hn : Fintype.card V ≤ N) :
    (allOnes N).eval (G.adjMatrix ℝ) (G.degMatrix ℝ) = realOnesMatrix := by
  calc
    _ = MatrixSemantics.realMatrix ((allOnes N).eval (G.adjMatrix ℤ) (G.degMatrix ℤ)) := by simp
    _ = MatrixSemantics.realMatrix (TreeDistance.onesMatrix (V := V)) :=
      congrArg MatrixSemantics.realMatrix (TreeDistance.actual_allOnes_expression_identity G hG hn)
    _ = _ := by ext i j; norm_num [MatrixSemantics.realMatrix_apply, TreeDistance.onesMatrix, realOnesMatrix]

omit [Fintype W] [DecidableEq W] in
theorem graph_moment_trace_allOnes (G : SimpleGraph V) [DecidableRel G.Adj] (w : List Bool) :
    moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) w =
      (matrixWord (G.adjMatrix ℝ) (G.degMatrix ℝ) w * realOnesMatrix).trace := by
  rw [GraphSemantics.graph_moment_double_sum, graph_matrixWord]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, realOnesMatrix]

theorem full_word_traces_imply_pointed_moments (N : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N)
    (ht : ∀ w, (matrixWord (G.adjMatrix ℝ) (G.degMatrix ℝ) w).trace =
      (matrixWord (H.adjMatrix ℝ) (H.degMatrix ℝ) w).trace) :
    ∀ w, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) w =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) w := by
  intro w
  have hh := trace_expression_equal (G.adjMatrix ℝ) (G.degMatrix ℝ)
    (H.adjMatrix ℝ) (H.degMatrix ℝ) ht (Expr.mul (wordExpression w) (allOnes N))
  rw [Expr.eval, Expr.eval, wordExpression_eval, wordExpression_eval,
    real_allOnes_expression N G hG hnG, real_allOnes_expression N H hH hnH] at hh
  rw [graph_moment_trace_allOnes, graph_moment_trace_allOnes]
  exact hh

theorem full_word_traces_determine_trees (N : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N)
    (ht : ∀ w, (matrixWord (G.adjMatrix ℝ) (G.degMatrix ℝ) w).trace =
      (matrixWord (H.adjMatrix ℝ) (H.degMatrix ℝ) w).trace) : Nonempty (G ≃g H) :=
  WrittenProof.public_theorem_5_4_word_version G H hG hH
    (full_word_traces_imply_pointed_moments N G H hG hH hnG hnH ht)

#print axioms full_word_traces_imply_pointed_moments
#print axioms full_word_traces_determine_trees

end
end ADComplete.Frobenius
