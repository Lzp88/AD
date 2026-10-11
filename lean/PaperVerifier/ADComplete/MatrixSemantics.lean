import PaperVerifier.ADComplete.GramTables
import PaperVerifier.ADComplete.TreeSeparation

/-! Exact integer-matrix to Euclidean Gram-table interpretation. -/

namespace ADComplete.MatrixSemantics
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix PrincipalMomentAudit

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def realMatrix (X : Matrix V V ℤ) : Matrix V V ℝ :=
  (Int.castRingHom ℝ).mapMatrix X

@[simp] theorem realMatrix_apply (X : Matrix V V ℤ) (u v : V) :
    realMatrix X u v = (X u v : ℝ) := rfl

@[simp] theorem realMatrix_zero : realMatrix (0 : Matrix V V ℤ) = 0 := map_zero _
@[simp] theorem realMatrix_one : realMatrix (1 : Matrix V V ℤ) = 1 := map_one _
@[simp] theorem realMatrix_intCast (c : ℤ) :
    realMatrix (c : Matrix V V ℤ) = (c : Matrix V V ℝ) := map_intCast _ _
@[simp] theorem realMatrix_add (X Y : Matrix V V ℤ) :
    realMatrix (X + Y) = realMatrix X + realMatrix Y := map_add _ _ _
@[simp] theorem realMatrix_mul (X Y : Matrix V V ℤ) :
    realMatrix (X * Y) = realMatrix X * realMatrix Y := map_mul _ _ _
@[simp] theorem realMatrix_zsmul (c : ℤ) (X : Matrix V V ℤ) :
    realMatrix (c • X) = c • realMatrix X := map_zsmul _ _ _
@[simp] theorem realMatrix_star (X : Matrix V V ℤ) :
    realMatrix (star X) = (realMatrix X).transpose := by
  ext i j
  change ((star (X j i) : ℤ) : ℝ) = (X j i : ℝ)
  simp only [star_trivial]

@[simp] theorem realMatrix_eval (p : CircuitAudit.Degrees.Expr) (A D : Matrix V V ℤ) :
    realMatrix (p.eval A D) = p.eval (realMatrix A) (realMatrix D) := by
  induction p <;> simp_all [CircuitAudit.Degrees.Expr.eval]

@[simp] theorem realMatrix_adjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    realMatrix (G.adjMatrix ℤ) = G.adjMatrix ℝ := by
  ext i j
  simp only [realMatrix_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

@[simp] theorem realMatrix_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    realMatrix (G.degMatrix ℤ) = G.degMatrix ℝ := by
  ext i j
  simp only [realMatrix_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply]
  split_ifs <;> norm_num

theorem doubleSum_cast (X : Matrix V V ℤ) :
    (TreeSeparation.doubleSum X : ℝ) = ∑ u, ∑ v, realMatrix X u v := by
  simp [TreeSeparation.doubleSum]

theorem real_doubleSum_gram (U B T : Matrix V V ℝ) :
    (∑ u, ∑ v, ((U.transpose * B) * T) u v) =
      ⟪WithLp.toLp 2 (U *ᵥ (fun _ => (1 : ℝ))),
        B.toEuclideanLin (WithLp.toLp 2 (T *ᵥ (fun _ => (1 : ℝ))))⟫_ℝ := by
  change _ = ⟪WithLp.toLp 2 (U *ᵥ (fun _ => (1 : ℝ))),
    WithLp.toLp 2 (B *ᵥ (T *ᵥ (fun _ => (1 : ℝ))))⟫_ℝ
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  calc
    _ = (fun _ => (1 : ℝ)) ⬝ᵥ (((U.transpose * B) * T) *ᵥ (fun _ => 1)) := by
      simp [Matrix.mulVec, dotProduct]
    _ = (fun _ => (1 : ℝ)) ⬝ᵥ (U.transpose *ᵥ (B *ᵥ (T *ᵥ (fun _ => 1)))) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = _ := Matrix.dotProduct_transpose_mulVec U _ _

def intFrame {M : ℕ} (U : Fin M → Matrix V V ℤ) : Fin M → EuclideanSpace ℝ V :=
  fun i => WithLp.toLp 2 (realMatrix (U i) *ᵥ (fun _ => (1 : ℝ)))

theorem digit_eq_inner {M : ℕ} (U : Fin M → Matrix V V ℤ)
    (B : Matrix V V ℤ) (i j : Fin M) :
    (TreeSeparation.doubleSum ((star (U i) * B) * U j) : ℝ) =
      ⟪intFrame U i, (realMatrix B).toEuclideanLin (intFrame U j)⟫_ℝ := by
  rw [doubleSum_cast]
  simp only [realMatrix_mul, realMatrix_star]
  exact real_doubleSum_gram _ _ _

theorem integer_three_tables_determine_graph_moments
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    {M : ℕ} (U : Fin M → Matrix V V ℤ) (T : Fin M → Matrix W W ℤ)
    (hU : LinearMap.range (combination (intFrame U)) =
      principal (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)))
    (hT : LinearMap.range (combination (intFrame T)) =
      principal (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)))
    (i₀ : Fin M) (hU₀ : intFrame U i₀ = GraphSemantics.oneSeed (V := V))
    (hT₀ : intFrame T i₀ = GraphSemantics.oneSeed (V := W))
    (hTable : ∀ s i j, TreeSeparation.doubleSum ((star (U i) *
        CircuitAudit.RadixFactorization.coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s) * U j) =
      TreeSeparation.doubleSum ((star (T i) *
        CircuitAudit.RadixFactorization.coreSlots (H.adjMatrix ℤ) (H.degMatrix ℤ) s) * T j)) :
    ∀ w, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) w =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) w := by
  have hR (s : Fin 3) (i j : Fin M) := congrArg (fun z : ℤ => (z : ℝ)) (hTable s i j)
  simp_rw [digit_eq_inner] at hR
  apply GramTables.frame_three_tables_determine_moments _ _ _ _ _ _ hU hT
    ?_ ?_ i₀ hU₀ hT₀
  · intro i j
    simpa [CircuitAudit.RadixFactorization.coreSlots] using hR 0 i j
  · intro b i j
    cases b
    · simpa [CircuitAudit.RadixFactorization.coreSlots, GraphSemantics.generators,
        GraphSemantics.generatorMatrix] using hR 1 i j
    · simpa [CircuitAudit.RadixFactorization.coreSlots, GraphSemantics.generators,
        GraphSemantics.generatorMatrix] using hR 2 i j

#print axioms digit_eq_inner
#print axioms integer_three_tables_determine_graph_moments
end
end ADComplete.MatrixSemantics
