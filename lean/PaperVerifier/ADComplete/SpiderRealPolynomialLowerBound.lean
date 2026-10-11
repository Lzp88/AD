import PaperVerifier.ADComplete.SpiderTraceWords

/-! The actual spider witnesses give the trace-degree obstruction for arbitrary
real coefficients, with no integrality or circuit-syntax restriction. -/
namespace ADComplete.SpiderGraph
noncomputable section
open ADClosedWalks
open scoped BigOperators

abbrev RealNCPolynomial := List Bool →₀ ℝ

def realFormalDegree (c : RealNCPolynomial) : ℕ := c.support.sup List.length

def realWordMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (A D : Matrix V V ℝ) : List Bool → Matrix V V ℝ
  | [] => 1
  | false :: w => A * realWordMatrix A D w
  | true :: w => D * realWordMatrix A D w

def realPolynomialMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : RealNCPolynomial) : Matrix V V ℝ :=
  c.sum (fun w a => a • realWordMatrix (G.adjMatrix ℝ) (G.degMatrix ℝ) w)

def realPolynomialTrace {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : RealNCPolynomial) : ℝ :=
  Matrix.trace (realPolynomialMatrix G c)

theorem cast_adjacency {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Int.castRingHom ℝ).mapMatrix (G.adjMatrix ℤ) = G.adjMatrix ℝ := by
  ext i j
  change (((G.adjMatrix ℤ) i j : ℤ) : ℝ) = (G.adjMatrix ℝ) i j
  simp only [SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp_all

theorem cast_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Int.castRingHom ℝ).mapMatrix (G.degMatrix ℤ) = G.degMatrix ℝ := by
  ext i j
  change (((G.degMatrix ℤ) i j : ℤ) : ℝ) = (G.degMatrix ℝ) i j
  simp only [SimpleGraph.degMatrix, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem cast_word_matrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : List Bool) :
    (Int.castRingHom ℝ).mapMatrix (wordMatrix G w) =
      realWordMatrix (G.adjMatrix ℝ) (G.degMatrix ℝ) w := by
  induction w with
  | nil => exact map_one _
  | cons b w ih =>
      cases b <;> simp only [wordMatrix, generator, Bool.false_eq_true, if_false,
        if_true, map_mul, cast_adjacency, cast_degree, ih, realWordMatrix]

theorem real_word_trace_cast {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : List Bool) :
    Matrix.trace (realWordMatrix (G.adjMatrix ℝ) (G.degMatrix ℝ) w) =
      ((Matrix.trace (wordMatrix G w) : ℤ) : ℝ) := by
  rw [← cast_word_matrix]
  simp [Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply]

theorem realPolynomialTrace_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : RealNCPolynomial) :
    realPolynomialTrace G c =
      ∑ w ∈ c.support, c w * ((Matrix.trace (wordMatrix G w) : ℤ) : ℝ) := by
  unfold realPolynomialTrace realPolynomialMatrix Finsupp.sum
  rw [Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Matrix.trace_smul, real_word_trace_cast]
  rfl

/-- Every arbitrary real-coefficient polynomial of total degree below `2*m`
has identical literal matrix trace on the two explicit spider trees. -/
theorem witness_real_polynomial_trace_eq (m : ℕ) (hm : 2 ≤ m)
    (c : RealNCPolynomial) (hc : realFormalDegree c < 2 * m) :
    realPolynomialTrace (graph (leftLengths m)) c =
      realPolynomialTrace (graph (rightLengths m)) c := by
  rw [realPolynomialTrace_sum, realPolynomialTrace_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hlen : w.length ≤ realFormalDegree c := Finset.le_sup (f := List.length) hw
  have hcount : adjacencyCount w ≤ w.length := List.count_le_length
  rw [witness_short_word_trace_eq m hm w (lt_of_le_of_lt (hcount.trans hlen) hc)]

theorem degree_le_three (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) (v : Vertex L) :
    (graph L).degree v ≤ 3 := by
  cases v with
  | none => rw [root_degree L hL]
  | some y => rw [arm_degree]; split_ifs <;> omega

/-- One complete explicit witness package: actual trees, exact order, bounded
degree, genuine nonisomorphism, and indistinguishability for every real polynomial. -/
theorem actual_spider_polynomial_obstruction (m : ℕ) (hm : 2 ≤ m) :
    (graph (leftLengths m)).IsTree ∧ (graph (rightLengths m)).IsTree ∧
    Fintype.card (Vertex (leftLengths m)) = 3 * m + 3 ∧
    Fintype.card (Vertex (rightLengths m)) = 3 * m + 3 ∧
    (∀ v, (graph (leftLengths m)).degree v ≤ 3) ∧
    (∀ v, (graph (rightLengths m)).degree v ≤ 3) ∧
    ¬ Nonempty (graph (leftLengths m) ≃g graph (rightLengths m)) ∧
    ∀ c : RealNCPolynomial, realFormalDegree c < 2 * m →
      realPolynomialTrace (graph (leftLengths m)) c =
        realPolynomialTrace (graph (rightLengths m)) c := by
  exact ⟨isTree _, isTree _, witness_card_left m, witness_card_right m,
    degree_le_three _ (left_positive m hm), degree_le_three _ (right_positive m hm),
    witness_nonisomorphic m hm, witness_real_polynomial_trace_eq m hm⟩

def SeparatesTrees (N : ℕ) (c : RealNCPolynomial) : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
    G.IsTree → H.IsTree → Fintype.card V ≤ N → Fintype.card W ≤ N →
    realPolynomialTrace G c = realPolynomialTrace H c → Nonempty (G ≃g H)

/-- The manuscript's lower bound for a single trace separating all actual trees
of order at most `N`, for every real-coefficient noncommutative polynomial. -/
theorem single_trace_degree_lower_bound (N : ℕ) (hN : 9 ≤ N)
    (c : RealNCPolynomial) (hsep : SeparatesTrees N c) :
    2 * ((N - 3) / 3) ≤ realFormalDegree c := by
  by_contra hc
  have hm : 2 ≤ (N - 3) / 3 := by omega
  have hn : 3 * ((N - 3) / 3) + 3 ≤ N := by omega
  apply witness_nonisomorphic ((N - 3) / 3) hm
  apply hsep (Vertex (leftLengths ((N - 3) / 3)))
    (Vertex (rightLengths ((N - 3) / 3))) _ _ (isTree _) (isTree _)
  · rw [witness_card_left]; exact hn
  · rw [witness_card_right]; exact hn
  · exact witness_real_polynomial_trace_eq _ hm c (by omega)

#print axioms witness_real_polynomial_trace_eq
#print axioms actual_spider_polynomial_obstruction
#print axioms single_trace_degree_lower_bound
end
end ADComplete.SpiderGraph
