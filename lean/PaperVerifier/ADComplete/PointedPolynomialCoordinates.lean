import PaperVerifier.ADComplete.PointedCoordinateDegree
import PaperVerifier.ADComplete.FixedPointedTables

/-! The literal three pointed tables are joint coordinate polynomials.
Every monomial has matrix-variable degree at most 2*N-1 and seed-variable
degree at most two. Evaluation agrees with the actual Euclidean tables. -/

namespace ADComplete.PointedPolynomialCoordinates
open Matrix MvPolynomial CircuitAudit.Degrees PrincipalMomentAudit PointedCoordinateDegree
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Coordinate (V : Type*) := Sum (Bool × V × V) V

def matrixWeight : Coordinate V → ℕ
  | .inl _ => 1
  | .inr _ => 0

def seedWeight : Coordinate V → ℕ
  | .inl _ => 0
  | .inr _ => 1

def variableMatrix (b : Bool) : Matrix V V (MvPolynomial (Coordinate V) ℝ) :=
  fun i j => X (.inl (b,i,j))

def variableSeed : V → MvPolynomial (Coordinate V) ℝ := fun i => X (.inr i)

def tablePolynomial (N : ℕ) (i j : Fin (probeList N N).length) (s : Expr) :
    MvPolynomial (Coordinate V) ℝ :=
  scalarTable (variableMatrix false) (variableMatrix true) variableSeed
    ((probeList N N).get i) s ((probeList N N).get j)

theorem tablePolynomial_bidegree (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin (probeList N N).length) (s : Expr) (hs : s.degree ≤ 1) :
    DegreeBound matrixWeight (tablePolynomial (V := V) N i j s) (2*N-1) ∧
      DegreeBound seedWeight (tablePolynomial (V := V) N i j s) 2 := by
  have hmat (b : Bool) (i j : V) : DegreeBound matrixWeight (variableMatrix b i j) 1 :=
    bound_X matrixWeight (.inl (b,i,j))
  have hseed (i : V) : DegreeBound matrixWeight (variableSeed i) 0 :=
    bound_X matrixWeight (.inr i)
  have hm := bound_scalarTable matrixWeight (variableMatrix false) (variableMatrix true)
    variableSeed 1 0 (hmat false) (hmat true) hseed
    ((probeList N N).get i) s ((probeList N N).get j)
  have hi := probeList_degree N N _ (List.get_mem (probeList N N) i)
  have hj := probeList_degree N N _ (List.get_mem (probeList N N) j)
  have hmat' (b : Bool) (i j : V) : DegreeBound seedWeight (variableMatrix b i j) 0 :=
    bound_X seedWeight (.inl (b,i,j))
  have hseed' (i : V) : DegreeBound seedWeight (variableSeed i) 1 :=
    bound_X seedWeight (.inr i)
  have hz := bound_scalarTable seedWeight (variableMatrix false) (variableMatrix true)
    variableSeed 0 1 (hmat' false) (hmat' true) hseed'
    ((probeList N N).get i) s ((probeList N N).get j)
  refine ⟨bound_mono hm ?_, ?_⟩
  · omega
  · simpa only [tablePolynomial, Nat.mul_zero, Nat.zero_add, Nat.mul_one] using hz

def coordinateEvaluation (H K : Matrix V V ℝ) (v : V → ℝ) :
    MvPolynomial (Coordinate V) ℝ →+* ℝ :=
  MvPolynomial.eval₂Hom (RingHom.id ℝ)
    (Sum.elim (fun x => if x.1 then K x.2.1 x.2.2 else H x.2.1 x.2.2) v)

lemma expression_mapMatrix {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (H K : Matrix V V R) (p : Expr) :
    φ.mapMatrix (p.eval H K) = p.eval (φ.mapMatrix H) (φ.mapMatrix K) := by
  induction p <;> simp only [Expr.eval, map_zero, map_one, map_zsmul, map_add, map_mul, *]

lemma variableMatrix_eval (H K : Matrix V V ℝ) (v : V → ℝ) (b : Bool) :
    (coordinateEvaluation H K v).mapMatrix (variableMatrix b) = if b then K else H := by
  ext i j
  cases b <;> simp [coordinateEvaluation, variableMatrix, RingHom.mapMatrix,
    Matrix.map_apply]

omit [Fintype V] [DecidableEq V] in
lemma variableSeed_eval (H K : Matrix V V ℝ) (v : V → ℝ) (i : V) :
    coordinateEvaluation H K v (variableSeed i) = v i := by
  simp [coordinateEvaluation, variableSeed, MvPolynomial.eval₂Hom_X']

lemma expression_entry_eval (H K : Matrix V V ℝ) (v : V → ℝ) (p : Expr) (i j : V) :
    coordinateEvaluation H K v
      ((p.eval (variableMatrix false) (variableMatrix true)) i j) = (p.eval H K) i j := by
  have he := expression_mapMatrix (coordinateEvaluation H K v)
    (variableMatrix false) (variableMatrix true) p
  rw [variableMatrix_eval, variableMatrix_eval] at he
  exact congrFun (congrFun he i) j

theorem tablePolynomial_evaluation (N : ℕ) (H K : Matrix V V ℝ) (v : V → ℝ)
    (i j : Fin (probeList N N).length) (s : Expr) :
    coordinateEvaluation H K v (tablePolynomial (V := V) N i j s) =
      ⟪FrameSemantics.probeFrame N H K v i,
        (s.eval H K).toEuclideanLin (FrameSemantics.probeFrame N H K v j)⟫_ℝ := by
  simp only [tablePolynomial, scalarTable, Matrix.mulVec, dotProduct, map_sum, map_mul,
    expression_entry_eval, variableSeed_eval, FrameSemantics.probeFrame,
    FrameSemantics.probeMatrices, Matrix.toLpLin_toLp, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem actual_three_tables_have_bidegree (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin (probeList N N).length) :
    ∀ s ∈ ([Expr.one, Expr.a, Expr.d] : List Expr),
      DegreeBound matrixWeight (tablePolynomial (V := V) N i j s) (2*N-1) ∧
        DegreeBound seedWeight (tablePolynomial (V := V) N i j s) 2 := by
  intro s hs
  apply tablePolynomial_bidegree N hN i j s
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> simp [Expr.degree]

#print axioms tablePolynomial_bidegree
#print axioms tablePolynomial_evaluation
#print axioms actual_three_tables_have_bidegree

end
end ADComplete.PointedPolynomialCoordinates
