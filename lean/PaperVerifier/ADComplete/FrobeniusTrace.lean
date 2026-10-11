import PaperVerifier.ADComplete.FrobeniusProbes
import PaperVerifier.ADComplete.GramTables

/-! Word traces, actual polynomial evaluation, and Frobenius pointed moments. -/

namespace ADComplete.Frobenius

open Matrix Polynomial CircuitAudit.Degrees PrincipalMomentAudit
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
lemma matrixWord_append (H K : Matrix ι ι ℝ) (v w : List Bool) :
    matrixWord H K (v++w) = matrixWord H K v * matrixWord H K w := by
  induction v with
  | nil => simp [matrixWord]
  | cons b v ih => simp only [List.cons_append, matrixWord, ih, Matrix.mul_assoc]

theorem expression_equal_of_word_functionals (H K : Matrix ι ι ℝ)
    (H' K' : Matrix κ κ ℝ) (p : Expr) :
    ∀ (L : Matrix ι ι ℝ →ₗ[ℝ] ℝ) (L' : Matrix κ κ ℝ →ₗ[ℝ] ℝ),
      (∀ w, L (matrixWord H K w) = L' (matrixWord H' K' w)) →
      L (p.eval H K) = L' (p.eval H' K') := by
  induction p with
  | zero => intro L L' _; simp [Expr.eval]
  | one => intro L L' h; exact h []
  | a => intro L L' h; simpa [Expr.eval, matrixWord] using h [false]
  | d => intro L L' h; simpa [Expr.eval, matrixWord] using h [true]
  | scale c p ih =>
      intro L L' h
      simpa only [Expr.eval, map_zsmul] using congrArg (fun t : ℝ => c • t) (ih L L' h)
  | add p q ihp ihq =>
      intro L L' h
      simp only [Expr.eval, map_add, ihp L L' h, ihq L L' h]
  | mul p q ihp ihq =>
      intro L L' h
      apply ihq (L.comp (LinearMap.mulLeft ℝ (p.eval H K)))
        (L'.comp (LinearMap.mulLeft ℝ (p.eval H' K')))
      intro w
      apply ihp (L.comp (LinearMap.mulRight ℝ (matrixWord H K w)))
        (L'.comp (LinearMap.mulRight ℝ (matrixWord H' K' w)))
      intro v
      simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply, ← matrixWord_append] using h (v++w)

theorem trace_expression_equal (H K : Matrix ι ι ℝ) (H' K' : Matrix κ κ ℝ)
    (h : ∀ w, (matrixWord H K w).trace = (matrixWord H' K' w).trace) (p : Expr) :
    (p.eval H K).trace = (p.eval H' K').trace :=
  expression_equal_of_word_functionals H K H' K' p
    (Matrix.traceLinearMap ι ℝ ℝ) (Matrix.traceLinearMap κ ℝ ℝ) h

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
theorem inner_flatten (P Q : Matrix ι ι ℝ) :
    ⟪WithLp.toLp 2 (flatten P), WithLp.toLp 2 (flatten Q)⟫_ℝ = (P.transpose * Q).trace := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, flatten,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change Q i j * P i j = P i j * Q i j
  exact mul_comm _ _

omit [Fintype κ] [DecidableEq κ] in
theorem moment_trace (H K : Matrix ι ι ℝ) (w : List Bool) :
    moment (FrameSemantics.generators (leftMatrix H) (leftMatrix K))
      (WithLp.toLp 2 (flatten (1 : Matrix ι ι ℝ))) w = (matrixWord H K w).trace := by
  unfold moment
  rw [FrameSemantics.wordEval_eq_wordVector, word_flatten, inner_flatten,
    Matrix.transpose_one, Matrix.one_mul]

#print axioms trace_expression_equal
#print axioms moment_trace

end
end ADComplete.Frobenius
