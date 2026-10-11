import PaperVerifier.PrincipalMomentAudit.Transport
import PaperVerifier.PrincipalMomentAudit.ForestPruning
import PaperVerifier.PrincipalMomentAudit.PruningExpressions
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Literal selector evaluation on actual finite graphs

This module evaluates the same expression syntax used by `PruningExpressions`
on ordinary graph matrices.  The finite Lagrange product is identified exactly
with its integer-level diagonal selector before it is applied to graph degree
and selected-leaf count diagonals.
-/

namespace PrincipalMomentAudit.SelectorEvaluation

open Matrix Finset PrincipalMomentAudit.Transport

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary matrix interpretation of the literal expression syntax. -/
def matrixEval (A D : Matrix V V ℝ) : Expression → Matrix V V ℝ
  | .scalar c => c • 1
  | .adjacency => A
  | .degree => D
  | .add p q => matrixEval A D p + matrixEval A D q
  | .mul p q => matrixEval A D p * matrixEval A D q

/-- Matrix interpretation commutes with every algebra representation;
thus these are precisely the same literal expressions as the transported ones. -/
theorem matrixEval_algHom {E : Type*} [AddCommGroup E] [Module ℝ E]
    (φ : Matrix V V ℝ →ₐ[ℝ] Module.End ℝ E) (A D : Matrix V V ℝ) (p : Expression) :
    φ (matrixEval A D p) = p.eval (φ A) (φ D) := by
  induction p with
  | scalar c => simp [matrixEval, Expression.eval]
  | adjacency => rfl
  | degree => rfl
  | add p q hp hq => simp [matrixEval, Expression.eval, hp, hq]
  | mul p q hp hq => simp [matrixEval, Expression.eval, hp, hq]

/-- Specialization to the actual Euclidean graph representations used by GNS. -/
theorem matrixEval_toEuclideanLin (A D : Matrix V V ℝ) (p : Expression) :
    (matrixEval A D p).toEuclideanLin = p.eval A.toEuclideanLin D.toEuclideanLin := by
  exact matrixEval_algHom
    (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℝ V)).toAlgHom A D p

@[simp]
theorem matrixEval_sub (A D : Matrix V V ℝ) (p q : Expression) :
    matrixEval A D (p.sub q) = matrixEval A D p - matrixEval A D q := by
  simp [Expression.sub, Expression.neg, matrixEval, sub_eq_add_neg]

/-- Products of diagonal expression values stay diagonal, with the literal
ordered list product retained on the scalar entries. -/
theorem matrixEval_listProduct_diagonal {ι : Type*} (xs : List ι)
    (p : ι → Expression) (d : ι → V → ℝ) (A D : Matrix V V ℝ)
    (h : ∀ i ∈ xs, matrixEval A D (p i) = Matrix.diagonal (d i)) :
    matrixEval A D (Expression.listProduct (xs.map p)) =
      Matrix.diagonal (fun v => (xs.map (fun i => d i v)).prod) := by
  induction xs with
  | nil => simp [Expression.listProduct, Expression.one, matrixEval]
  | cons i xs ih =>
      simp only [List.map_cons, Expression.listProduct, matrixEval]
      rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]
      simp [Matrix.diagonal_mul_diagonal]

/-- Exact evaluation of the paper's literal Lagrange product on a diagonal. -/
theorem levelSelector_matrixEval_diagonal (A D : Matrix V V ℝ) (p : Expression)
    (d : V → ℝ) (hp : matrixEval A D p = Matrix.diagonal d) (N k : ℕ) :
    matrixEval A D (levelSelector N k p) =
      Matrix.diagonal (fun v => scalarSelector N k (d v)) := by
  let xs := (List.range (N + 1)).filter (fun r => r ≠ k)
  let factors := fun (r : ℕ) => Expression.mul
    (.scalar (((k : ℝ) - (r : ℝ))⁻¹)) (p.sub (.scalar (r : ℝ)))
  let weights := fun (r : ℕ) (v : V) => ((k : ℝ) - (r : ℝ))⁻¹ * (d v - (r : ℝ))
  have hf (r : ℕ) : matrixEval A D (factors r) = Matrix.diagonal (weights r) := by
    simp only [factors, matrixEval, matrixEval_sub, hp, weights]
    ext u v
    by_cases huv : u = v
    · subst v
      simp
    · simp [huv]
  unfold levelSelector
  simp only [bind_pure_comp]
  change matrixEval A D (Expression.listProduct
    ((xs.map (fun r : ℕ => (r : ℝ))).map
      (fun r : ℝ => Expression.mul (.scalar (((k : ℝ) - r)⁻¹))
        (p.sub (.scalar r))))) = _
  rw [List.map_map]
  dsimp only [Function.comp_def, xs]
  have hprod := matrixEval_listProduct_diagonal xs factors weights A D (fun r _ => hf r)
  dsimp only [xs, factors] at hprod
  rw [hprod]
  congr 1
  funext v
  have hn : xs.Nodup := (List.nodup_range (n := N + 1)).filter _
  rw [← List.prod_toFinset (fun r => weights r v) hn]
  have hxs : xs.toFinset = (Finset.range (N + 1)).erase k := by
    ext r
    simp [xs, and_comm]
  rw [hxs]
  simp [weights, scalarSelector, div_eq_mul_inv, mul_comm]

/-- Bounded integer diagonal values are selected exactly, not approximately. -/
theorem levelSelector_matrixEval_integer (A D : Matrix V V ℝ) (p : Expression)
    (d : V → ℕ) (hp : matrixEval A D p = Matrix.diagonal (fun v => (d v : ℝ)))
    (N k : ℕ) (hd : ∀ v, d v ≤ N) :
    matrixEval A D (levelSelector N k p) =
      PrincipalMomentAudit.vertexSelector (Finset.univ.filter (fun v => d v = k)) := by
  rw [levelSelector_matrixEval_diagonal A D p _ hp N k]
  ext u v
  by_cases huv : u = v
  · subst v
    simp [PrincipalMomentAudit.vertexSelector, scalarSelector_integer N k (d u) (hd u)]
  · simp [PrincipalMomentAudit.vertexSelector, huv]

theorem matrixEval_listSum (A D : Matrix V V ℝ) (xs : List Expression) :
    matrixEval A D (Expression.listSum xs) = (xs.map (matrixEval A D)).sum := by
  induction xs with
  | nil => simp [Expression.listSum, matrixEval]
  | cons p xs ih => simp [Expression.listSum, matrixEval, ih]

theorem matrixEval_sumExpressions {ι : Type*} [Fintype ι]
    (A D : Matrix V V ℝ) (p : ι → Expression) :
    matrixEval A D (sumExpressions p) = ∑ i, matrixEval A D (p i) := by
  classical
  rw [sumExpressions, matrixEval_listSum, List.map_map]
  exact Finset.sum_map_toList _ _

theorem matrixEval_productExpressions_diagonal {ι : Type*} [Fintype ι]
    (A D : Matrix V V ℝ) (p : ι → Expression) (d : ι → V → ℝ)
    (h : ∀ i, matrixEval A D (p i) = Matrix.diagonal (d i)) :
    matrixEval A D (productExpressions p) = Matrix.diagonal (fun v => ∏ i, d i v) := by
  classical
  rw [productExpressions, matrixEval_listProduct_diagonal _ p d A D (fun i _ => h i)]
  congr 1
  funext v
  exact Finset.prod_map_toList _ _

@[simp] theorem vertexSelector_mul (S T : Finset V) :
    PrincipalMomentAudit.vertexSelector S * PrincipalMomentAudit.vertexSelector T = PrincipalMomentAudit.vertexSelector (S ∩ T) := by
  rw [PrincipalMomentAudit.vertexSelector, PrincipalMomentAudit.vertexSelector, Matrix.diagonal_mul_diagonal]
  ext u v
  by_cases huv : u = v
  · subst v
    by_cases huS : u ∈ S <;> by_cases huT : u ∈ T <;> simp [PrincipalMomentAudit.vertexSelector, huS, huT]
  · simp [PrincipalMomentAudit.vertexSelector, huv]

@[simp] theorem one_sub_vertexSelector (S : Finset V) :
    1 - PrincipalMomentAudit.vertexSelector S = PrincipalMomentAudit.vertexSelector Sᶜ := by
  ext u v
  by_cases huv : u = v
  · subst v
    by_cases hu : u ∈ S <;> simp [PrincipalMomentAudit.vertexSelector, hu]
  · simp [PrincipalMomentAudit.vertexSelector, huv]

/-- The actual active type cell, with one shared finite label set. -/
def typeCell {ρ : Type*} (S : Finset V) (label : V → ρ) (r : ρ) : Finset V := by
  classical
  exact S.filter (fun v => label v = r)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_typeCell {ρ : Type*} (S : Finset V) (label : V → ρ) (r : ρ) (v : V) :
    v ∈ typeCell S label r ↔ v ∈ S ∧ label v = r := by
  classical
  simp [typeCell]

omit [Fintype V] in
theorem sum_typeCell {ρ : Type*} [Fintype ρ] (S : Finset V) (label : V → ρ) :
    ∑ r, PrincipalMomentAudit.vertexSelector (typeCell S label r) = PrincipalMomentAudit.vertexSelector S := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    by_cases hu : u ∈ S <;> simp [Matrix.sum_apply, PrincipalMomentAudit.vertexSelector, typeCell, hu]
  · simp [Matrix.sum_apply, PrincipalMomentAudit.vertexSelector, huv]

open PrincipalMomentAudit.ForestPruning

/-- A literal state represents the ordinary matrices and the actual disjoint
active type partition of a masked graph. -/
structure Realizes {ρ : Type*} (A D : Matrix V V ℝ) (s : PruningState ρ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (label : V → ρ) : Prop where
  adjacency : matrixEval A D s.adjacency = (mask G S).adjMatrix ℝ
  degree : matrixEval A D s.degree = (mask G S).degMatrix ℝ
  typeSelector : ∀ r, matrixEval A D (s.typeSelector r) = PrincipalMomentAudit.vertexSelector (typeCell S label r)

theorem initialState_realizes (G : SimpleGraph V) [DecidableRel G.Adj] :
    Realizes (G.adjMatrix ℝ) (G.degMatrix ℝ) initialState G Finset.univ (fun _ => ()) := by
  constructor
  · change G.adjMatrix ℝ = (mask G Finset.univ).adjMatrix ℝ
    ext u v
    simp [SimpleGraph.adjMatrix]
  · change G.degMatrix ℝ = (mask G Finset.univ).degMatrix ℝ
    have hd (v : V) : (mask G Finset.univ).degree v = G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext u
      simp [SimpleGraph.mem_neighborFinset]
    simp only [SimpleGraph.degMatrix, hd]
  · intro r
    cases r
    ext u v
    by_cases huv : u = v <;> simp [initialState, Expression.one, matrixEval, PrincipalMomentAudit.vertexSelector, typeCell, huv]

theorem active_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    matrixEval A D s.active = PrincipalMomentAudit.vertexSelector S := by
  rw [PruningState.active, matrixEval_sumExpressions]
  simp_rw [h.typeSelector]
  exact sum_typeCell S label

/-- The exact degree-one set of the current ordinary graph. -/
def leafSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 1)

omit [DecidableEq V] in
@[simp] theorem mem_leafSet (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ leafSet G ↔ G.degree v = 1 := by simp [leafSet]

theorem leaves_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    matrixEval A D (s.leaves (Fintype.card V)) = PrincipalMomentAudit.vertexSelector (leafSet (mask G S)) := by
  rw [PruningState.leaves, matrixEval, active_matrixEval A D s G S label h]
  rw [levelSelector_matrixEval_integer A D s.degree (fun v => (mask G S).degree v)
    h.degree (Fintype.card V) 1 (fun v => Nat.le_of_lt ((mask G S).degree_lt_card_verts v))]
  rw [vertexSelector_mul]
  congr 1
  ext v
  simp only [Finset.mem_inter, mem_leafSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hv => hv.2
  · intro hv
    refine ⟨?_, hv⟩
    by_contra hnot
    have hz := mask_degree_zero_of_not_mem G S hnot
    omega

theorem leafCounts_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    matrixEval A D (s.leafCounts (Fintype.card V)) = Matrix.diagonal
      (fun v => (removedNeighbors (mask G S) (leafSet (mask G S)) v : ℝ)) := by
  simp only [PruningState.leafCounts, matrixEval, h.adjacency,
    leaves_matrixEval A D s G S label h]
  rw [PrincipalMomentAudit.leaf_diagonal_identity (mask G S) _ (fun w hw => (mem_leafSet _ w).mp hw)]
  congr 1
  funext v
  rw [removedNeighbors_eq_filter]

theorem removedNeighbors_le_order (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (v : V) : removedNeighbors G W v ≤ Fintype.card V := by
  exact (Finset.card_le_card (Finset.inter_subset_left)).trans
    (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Nat.le_of_lt (G.degree_lt_card_verts v))

theorem selector_adj_selector (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    PrincipalMomentAudit.vertexSelector S * G.adjMatrix ℝ * PrincipalMomentAudit.vertexSelector S =
      (mask G S).adjMatrix ℝ := by
  ext u v
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [PrincipalMomentAudit.vertexSelector, Matrix.diagonal_mul, Matrix.mul_diagonal,
      SimpleGraph.adjMatrix, hu, hv]

theorem step_degree_update_real (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((step G).degree v : ℝ) = (G.degree v : ℝ) -
      (if v ∈ peelable G then 1 else 0) - removedNeighbors G (peelable G) v := by
  exact_mod_cast step_degree_update G v

/-- Actual children of type r that are removed in this guarded round. -/
def peeledCell {ρ : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (r : ρ) : Finset V :=
  typeCell (peelable (mask G S)) label r

def childCount {ρ : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (r : ρ) (v : V) : ℕ :=
  removedNeighbors (mask G S) (peeledCell G S label r) v

/-- The next label is formed by actual incident counts in every old type cell. -/
def nextLabel {ρ : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (v : V) : ρ × (ρ → Fin (Fintype.card V + 1)) :=
  (label v, fun r => ⟨childCount G S label r v,
    Nat.lt_succ_of_le (removedNeighbors_le_order (mask G S) _ v)⟩)

theorem product_levelSelectors_childCount {ρ : Type*} [Fintype ρ]
    (A D : Matrix V V ℝ) (s : PruningState ρ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (label : V → ρ)
    (hc : ∀ r, matrixEval A D (s.childCounts (Fintype.card V) r) =
      Matrix.diagonal (fun v => (childCount G S label r v : ℝ)))
    (k : ρ → Fin (Fintype.card V + 1)) :
    matrixEval A D (productExpressions (fun r =>
      levelSelector (Fintype.card V) (k r).val (s.childCounts (Fintype.card V) r))) =
      PrincipalMomentAudit.vertexSelector (Finset.univ.filter (fun v => ∀ r, childCount G S label r v = (k r).val)) := by
  classical
  have hr (r : ρ) : matrixEval A D
      (levelSelector (Fintype.card V) (k r).val (s.childCounts (Fintype.card V) r)) =
      Matrix.diagonal (fun v => if childCount G S label r v = (k r).val then 1 else 0) := by
    rw [levelSelector_matrixEval_integer A D _ _ (hc r) _ _
      (fun v => removedNeighbors_le_order (mask G S) _ v)]
    simp [PrincipalMomentAudit.vertexSelector]
  rw [matrixEval_productExpressions_diagonal A D _ _ hr]
  ext u v
  by_cases huv : u = v
  · subst v
    simp [PrincipalMomentAudit.vertexSelector, Finset.prod_boole]
  · simp [PrincipalMomentAudit.vertexSelector, huv]

def centerEdgeSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  (leafSet G).filter (fun v => removedNeighbors G (leafSet G) v = 1)

theorem centerEdges_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    matrixEval A D (s.centerEdges (Fintype.card V)) =
      PrincipalMomentAudit.vertexSelector (centerEdgeSet (mask G S)) := by
  rw [PruningState.centerEdges, matrixEval, leaves_matrixEval A D s G S label h]
  rw [levelSelector_matrixEval_integer A D _ _ (leafCounts_matrixEval A D s G S label h)
    _ _ (fun v => removedNeighbors_le_order (mask G S) _ v), vertexSelector_mul]
  congr 1
  ext v
  simp [centerEdgeSet]

theorem peeledType_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) (r : ρ) :
    matrixEval A D (s.peeledType (Fintype.card V) r) =
      PrincipalMomentAudit.vertexSelector (peeledCell G S label r) := by
  classical
  simp only [PruningState.peeledType, matrixEval, h.typeSelector, matrixEval_sub,
    Expression.one, one_smul, leaves_matrixEval A D s G S label h,
    centerEdges_matrixEval A D s G S label h, one_sub_vertexSelector, vertexSelector_mul]
  congr 1
  ext v
  have hleaf : (mask G S).degree v = 1 → v ∈ S := by
    intro hv
    by_contra hn
    have hz := mask_degree_zero_of_not_mem G S hn
    omega
  simp only [Finset.mem_inter, Finset.mem_compl, mem_typeCell, mem_leafSet,
    centerEdgeSet, Finset.mem_filter, peeledCell, mem_peelable_iff_leaf_count]
  change ((v ∈ S ∧ label v = r) ∧ (mask G S).degree v = 1) ∧
    ¬ ((mask G S).degree v = 1 ∧ removedNeighbors (mask G S) (leafSet (mask G S)) v = 1) ↔
    ((mask G S).degree v = 1 ∧ removedNeighbors (mask G S) (leafSet (mask G S)) v ≠ 1) ∧ label v = r
  tauto

theorem peeled_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    matrixEval A D (s.peeled (Fintype.card V)) = PrincipalMomentAudit.vertexSelector (peelable (mask G S)) := by
  rw [PruningState.peeled, matrixEval_sumExpressions]
  simp_rw [peeledType_matrixEval A D s G S label h]
  exact sum_typeCell _ label

theorem childCounts_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) (r : ρ) :
    matrixEval A D (s.childCounts (Fintype.card V) r) =
      Matrix.diagonal (fun v => (childCount G S label r v : ℝ)) := by
  simp only [PruningState.childCounts, matrixEval, h.adjacency,
    peeledType_matrixEval A D s G S label h]
  have hW : ∀ w ∈ peeledCell G S label r, (mask G S).degree w = 1 := by
    intro w hw
    exact peelable_degree (mask G S) ((mem_typeCell _ label r w).mp hw).1
  rw [PrincipalMomentAudit.leaf_diagonal_identity (mask G S) (peeledCell G S label r) hW]
  congr 1
  funext v
  exact_mod_cast (removedNeighbors_eq_filter (mask G S) (peeledCell G S label r) v).symm

theorem sum_childCounts_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    matrixEval A D (sumExpressions (s.childCounts (Fintype.card V))) = Matrix.diagonal
      (fun v => (removedNeighbors (mask G S) (peelable (mask G S)) v : ℝ)) := by
  rw [matrixEval_sumExpressions]
  simp only [PruningState.childCounts, matrixEval, h.adjacency]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [← matrixEval_sumExpressions, ← PruningState.peeled, peeled_matrixEval A D s G S label h]
  rw [PrincipalMomentAudit.leaf_diagonal_identity (mask G S) _ (fun w hw => peelable_degree (mask G S) hw)]
  congr 1
  funext v
  rw [removedNeighbors_eq_filter]

omit [DecidableEq V] in
theorem graph_degree_congr (G H : SimpleGraph V) [hG : DecidableRel G.Adj]
    [hH : DecidableRel H.Adj] (h : G = H) (v : V) : G.degree v = H.degree v := by
  subst H
  cases Subsingleton.elim hG hH
  rfl

omit [Fintype V] [DecidableEq V] in
theorem graph_adjacency_congr (G H : SimpleGraph V) [hG : DecidableRel G.Adj]
    [hH : DecidableRel H.Adj] (h : G = H) : G.adjMatrix ℝ = H.adjMatrix ℝ := by
  subst H
  cases Subsingleton.elim hG hH
  rfl

theorem next_realizes {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    Realizes A D (s.next (Fintype.card V)) G (nextActive G S) (nextLabel G S label) := by
  classical
  constructor
  · simp only [PruningState.next, matrixEval, matrixEval_sub, Expression.one, one_smul,
      peeled_matrixEval A D s G S label h, h.adjacency, one_sub_vertexSelector]
    rw [selector_adj_selector]
    exact graph_adjacency_congr _ _ (mask_nextActive_eq_step G S).symm
  · simp only [PruningState.next, matrixEval_sub, h.degree,
      peeled_matrixEval A D s G S label h, sum_childCounts_matrixEval A D s G S label h]
    have hd (v : V) : (mask G (nextActive G S)).degree v = (step (mask G S)).degree v := by
      exact graph_degree_congr _ _ (mask_nextActive_eq_step G S) v
    ext u v
    by_cases huv : u = v
    · subst v
      simp only [SimpleGraph.degMatrix, Matrix.sub_apply, PrincipalMomentAudit.vertexSelector, Matrix.diagonal_apply_eq, hd]
      exact (step_degree_update_real (mask G S) u).symm
    · simp [SimpleGraph.degMatrix, PrincipalMomentAudit.vertexSelector, huv]
  · intro μ
    simp only [PruningState.next, matrixEval, matrixEval_sub, h.typeSelector, Expression.one,
      one_smul, peeled_matrixEval A D s G S label h, one_sub_vertexSelector]
    rw [product_levelSelectors_childCount A D s G S label
      (childCounts_matrixEval A D s G S label h) μ.2]
    rw [vertexSelector_mul, vertexSelector_mul]
    congr 1
    ext v
    simp only [Finset.mem_inter, mem_typeCell, Finset.mem_compl, Finset.mem_filter,
      Finset.mem_univ, true_and, nextActive, Finset.mem_sdiff, nextLabel]
    have hc : (fun r => (⟨childCount G S label r v,
        Nat.lt_succ_of_le (removedNeighbors_le_order (mask G S) _ v)⟩ : Fin (Fintype.card V + 1))) = μ.2 ↔
        ∀ r, childCount G S label r v = (μ.2 r).val := by
      simp only [funext_iff, Fin.ext_iff]
    rw [Prod.ext_iff, hc]
    tauto

/-- The finite literal type sets are fixed solely by the common order bound. -/
def StageType (N : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => StageType N t × (StageType N t → Fin (N + 1))

instance stageTypeFintype (N t : ℕ) : Fintype (StageType N t) := by
  classical
  induction t with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ t ih =>
      letI : Fintype (StageType N t) := ih
      exact inferInstanceAs (Fintype (StageType N t × (StageType N t → Fin (N + 1))))

def literalState (N : ℕ) : (t : ℕ) → PruningState (StageType N t)
  | 0 => initialState
  | t + 1 => (literalState N t).next N

def stageActive (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ → Finset V
  | 0 => Finset.univ
  | t + 1 => nextActive G (stageActive G t)

def stageLabel (G : SimpleGraph V) [DecidableRel G.Adj] :
    (t : ℕ) → V → StageType (Fintype.card V) t
  | 0 => fun _ => ()
  | t + 1 => nextLabel G (stageActive G t) (stageLabel G t)

/-- Every literal recursive state really evaluates to the graph and type
partition generated by guarded pruning. No state-realization premise remains. -/
theorem all_stages_realizes (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) :
    Realizes (G.adjMatrix ℝ) (G.degMatrix ℝ) (literalState (Fintype.card V) t)
      G (stageActive G t) (stageLabel G t) := by
  induction t with
  | zero => exact initialState_realizes G
  | succ t ih => exact next_realizes _ _ _ G _ _ ih

theorem activeFrom_succ_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (t : ℕ) : activeFrom G S (t + 1) = nextActive G (activeFrom G S t) := by
  induction t generalizing S with
  | zero => rfl
  | succ t ih => exact ih (nextActive G S)

theorem stageActive_eq_activeFrom (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) :
    stageActive G t = activeFrom G Finset.univ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [stageActive, ih, activeFrom_succ_right]

/-- The actual shared literal algorithm reaches the proven terminal forest
core within the order bound. This closes the selector-evaluation obligation. -/
theorem literal_forest_pruning_terminates (G : SimpleGraph V) [DecidableRel G.Adj]
    (hForest : G.IsAcyclic) :
    ∃ t, t ≤ Fintype.card V ∧
      Realizes (G.adjMatrix ℝ) (G.degMatrix ℝ) (literalState (Fintype.card V) t)
        G (stageActive G t) (stageLabel G t) ∧
      ∀ v, (mask G (stageActive G t)).degree v ≤ 1 := by
  obtain ⟨t, ht, hterm⟩ := forest_pruning_terminates G hForest Finset.univ
  refine ⟨t, by simpa using ht, all_stages_realizes G t, ?_⟩
  intro v
  rw [graph_degree_congr _ _ (congrArg (mask G) (stageActive_eq_activeFrom G t)) v]
  exact hterm v

def centerVertexSet (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S.filter (fun v => G.degree v = 0)

theorem centerVertices_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) :
    matrixEval A D (s.centerVertices (Fintype.card V)) =
      PrincipalMomentAudit.vertexSelector (centerVertexSet (mask G S) S) := by
  rw [PruningState.centerVertices, matrixEval, active_matrixEval A D s G S label h]
  rw [levelSelector_matrixEval_integer A D s.degree _ h.degree _ 0
    (fun v => Nat.le_of_lt ((mask G S).degree_lt_card_verts v)), vertexSelector_mul]
  congr 1
  ext v
  simp [centerVertexSet]

theorem centerVertexType_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) (r : ρ) :
    matrixEval A D (s.centerVertexType (Fintype.card V) r) =
      PrincipalMomentAudit.vertexSelector (typeCell (centerVertexSet (mask G S) S) label r) := by
  rw [PruningState.centerVertexType, matrixEval, centerVertices_matrixEval A D s G S label h,
    h.typeSelector, vertexSelector_mul]
  congr 1
  ext v
  simp only [Finset.mem_inter, mem_typeCell, centerVertexSet, Finset.mem_filter]
  tauto

/-- Actual oriented type cells on the protected leaf-pair components. -/
def centerEdgeTypeSet {ρ : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (r q : ρ) : Finset V :=
  (typeCell S label r ∩ centerEdgeSet G).filter (fun v =>
    removedNeighbors G (typeCell S label q ∩ centerEdgeSet G) v = 1)

theorem centerEdgeType_matrixEval {ρ : Type*} [Fintype ρ] (A D : Matrix V V ℝ)
    (s : PruningState ρ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (h : Realizes A D s G S label) (r q : ρ) :
    matrixEval A D (s.centerEdgeType (Fintype.card V) r q) =
      PrincipalMomentAudit.vertexSelector (centerEdgeTypeSet (mask G S) S label r q) := by
  have hc : matrixEval A D
      (.mul (.mul (.mul s.adjacency (s.typeSelector q)) (s.centerEdges (Fintype.card V))) s.adjacency) =
      Matrix.diagonal (fun v => (removedNeighbors (mask G S)
        (typeCell S label q ∩ centerEdgeSet (mask G S)) v : ℝ)) := by
    simp only [matrixEval, h.adjacency, h.typeSelector, centerEdges_matrixEval A D s G S label h]
    rw [mul_assoc ((mask G S).adjMatrix ℝ), vertexSelector_mul]
    have hW : ∀ w ∈ typeCell S label q ∩ centerEdgeSet (mask G S), (mask G S).degree w = 1 := by
      intro w hw
      exact (mem_leafSet _ w).mp ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).1)
    rw [PrincipalMomentAudit.leaf_diagonal_identity (mask G S) _ hW]
    congr 1
    funext v
    rw [removedNeighbors_eq_filter]
  rw [PruningState.centerEdgeType, matrixEval, matrixEval, h.typeSelector,
    centerEdges_matrixEval A D s G S label h]
  rw [levelSelector_matrixEval_integer A D _ _ hc _ 1
    (fun v => removedNeighbors_le_order (mask G S) _ v), vertexSelector_mul, vertexSelector_mul]
  congr 1
  ext v
  simp [centerEdgeTypeSet, and_assoc]

theorem mem_centerEdgeTypeSet {ρ : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (label : V → ρ) (r q : ρ) (v : V) :
    v ∈ centerEdgeTypeSet G S label r q ↔
      v ∈ typeCell S label r ∧ v ∈ centerEdgeSet G ∧
        ∃ u, G.Adj v u ∧ u ∈ typeCell S label q ∧ u ∈ centerEdgeSet G := by
  classical
  by_cases hv : v ∈ centerEdgeSet G
  · have hd : G.degree v = 1 := (mem_leafSet G v).mp (Finset.mem_filter.mp hv).1
    simp only [centerEdgeTypeSet, Finset.mem_filter, Finset.mem_inter,
      leaf_selected_neighbor_count_one_iff G _ hd]
    tauto
  · simp [centerEdgeTypeSet, hv]

theorem centerEdgeSet_is_leaf_pair (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hv : v ∈ centerEdgeSet G) : ∃ u, G.Adj v u ∧ G.degree v = 1 ∧ G.degree u = 1 ∧
      ∀ z, G.Reachable v z ↔ z = v ∨ z = u := by
  obtain ⟨hvleaf, hvcount⟩ := Finset.mem_filter.mp hv
  have hd := (mem_leafSet G v).mp hvleaf
  obtain ⟨u, hvu, hu⟩ := (leaf_neighbor_count_one_iff G hd).mp hvcount
  refine ⟨u, hvu, hd, hu, fun z => ⟨fun hz => reachable_leaf_pair G hd hu hvu hz, ?_⟩⟩
  rintro (rfl | rfl)
  · exact SimpleGraph.Reachable.refl _
  · exact hvu.reachable

theorem matrixEval_mem (S : Subalgebra ℝ (Matrix V V ℝ)) (A D : Matrix V V ℝ)
    (hA : A ∈ S) (hD : D ∈ S) (p : Expression) : matrixEval A D p ∈ S := by
  induction p with
  | scalar c => exact S.smul_mem S.one_mem c
  | adjacency => exact hA
  | degree => exact hD
  | add p q hp hq => exact S.add_mem hp hq
  | mul p q hp hq => exact S.mul_mem hp hq

theorem graph_matrixEval_mem (G : SimpleGraph V) [DecidableRel G.Adj] (p : Expression) :
    matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p ∈ PrincipalMomentAudit.adjacencyDegreeAlgebra G := by
  apply matrixEval_mem
  · apply Algebra.subset_adjoin
    simp
  · apply Algebra.subset_adjoin
    simp

theorem all_stage_typeSelector_mem (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ)
    (r : StageType (Fintype.card V) t) :
    PrincipalMomentAudit.vertexSelector (typeCell (stageActive G t) (stageLabel G t) r) ∈
      PrincipalMomentAudit.adjacencyDegreeAlgebra G := by
  rw [← (all_stages_realizes G t).typeSelector r]
  exact graph_matrixEval_mem G _

def vertexIndicator (W : Finset V) : V → ℝ := fun v => if v ∈ W then 1 else 0

theorem vertexSelector_mulVec_ones (W : Finset V) :
    PrincipalMomentAudit.vertexSelector W *ᵥ (fun _ => 1) = vertexIndicator W := by
  ext v
  simp [PrincipalMomentAudit.vertexSelector, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, vertexIndicator]

/-- Every actual recursive type-cell indicator belongs to the graph's
principal AD module, using the literal selector already proved above. -/
theorem all_stage_typeIndicator_mem (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ)
    (r : StageType (Fintype.card V) t) :
    vertexIndicator (typeCell (stageActive G t) (stageLabel G t) r) ∈
      PrincipalMomentAudit.principalADModule G := by
  rw [← vertexSelector_mulVec_ones]
  exact (PrincipalMomentAudit.MatrixPrincipal.mem_cyclicModule _ _ _).mpr
    ⟨_, all_stage_typeSelector_mem G t r, rfl⟩

theorem matrixEval_mulVec_ones_mem (G : SimpleGraph V) [DecidableRel G.Adj] (p : Expression) :
    matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p *ᵥ (fun _ => 1) ∈ PrincipalMomentAudit.principalADModule G := by
  exact (PrincipalMomentAudit.MatrixPrincipal.mem_cyclicModule _ _ _).mpr ⟨_, graph_matrixEval_mem G p, rfl⟩

theorem all_stage_centerVertexIndicator_mem (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ)
    (r : StageType (Fintype.card V) t) :
    vertexIndicator (typeCell (centerVertexSet (mask G (stageActive G t)) (stageActive G t)) (stageLabel G t) r) ∈
      PrincipalMomentAudit.principalADModule G := by
  have h := matrixEval_mulVec_ones_mem G ((literalState (Fintype.card V) t).centerVertexType (Fintype.card V) r)
  rw [centerVertexType_matrixEval _ _ _ G _ _ (all_stages_realizes G t) r, vertexSelector_mulVec_ones] at h
  exact h

theorem all_stage_centerEdgeIndicator_mem (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ)
    (r q : StageType (Fintype.card V) t) :
    vertexIndicator (centerEdgeTypeSet (mask G (stageActive G t)) (stageActive G t) (stageLabel G t) r q) ∈
      PrincipalMomentAudit.principalADModule G := by
  have h := matrixEval_mulVec_ones_mem G ((literalState (Fintype.card V) t).centerEdgeType (Fintype.card V) r q)
  rw [centerEdgeType_matrixEval _ _ _ G _ _ (all_stages_realizes G t) r q, vertexSelector_mulVec_ones] at h
  exact h

#print axioms levelSelector_matrixEval_integer
#print axioms next_realizes
#print axioms all_stages_realizes
#print axioms literal_forest_pruning_terminates
#print axioms centerEdgeType_matrixEval
#print axioms centerEdgeSet_is_leaf_pair
#print axioms all_stage_typeIndicator_mem
#print axioms all_stage_centerVertexIndicator_mem
#print axioms all_stage_centerEdgeIndicator_mem

end

end PrincipalMomentAudit.SelectorEvaluation
