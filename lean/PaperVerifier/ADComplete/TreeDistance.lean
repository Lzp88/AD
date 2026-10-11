import Mathlib
import PaperVerifier.CircuitAudit.Degrees

/-!
# Actual finite-tree distance matrices

This file uses the actual adjacency relation, neighbor count and graph
distance of a finite simple tree. The distance-polynomial recurrence is
proved at these matrices rather than imposed as a semantic hypothesis.
-/

namespace ADComplete.TreeDistance
noncomputable section
open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def distanceMatrix (k : ℕ) : Matrix V V ℤ :=
  fun u v => if G.dist u v = k then 1 else 0

def onesMatrix : Matrix V V ℤ := fun _ _ => 1

omit [Fintype V] [DecidableRel G.Adj] in
theorem distanceMatrix_zero (hG : G.IsTree) : distanceMatrix G 0 = 1 := by
  ext u v
  simp only [distanceMatrix, Matrix.one_apply]
  simp only [hG.connected.dist_eq_zero_iff]

omit [Fintype V] [DecidableEq V] in
theorem distanceMatrix_one : distanceMatrix G 1 = G.adjMatrix ℤ := by
  ext u v
  simp only [distanceMatrix, SimpleGraph.adjMatrix_apply,
    SimpleGraph.dist_eq_one_iff_adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A nontrivial tree path has exactly one first neighbor closer to its target. -/
theorem unique_predecessor (hG : G.IsTree) {u v : V} (huv : u ≠ v) :
    ∃! w, G.Adj u w ∧ G.dist w v + 1 = G.dist u v := by
  obtain ⟨p, hp, hplen⟩ := hG.connected.exists_path_of_dist u v
  obtain ⟨w, huw, q, rfl⟩ := Walk.exists_eq_cons_of_ne huv p
  have hfirst : G.dist w v + 1 = G.dist u v := by
    have hlow := G.dist_le q
    have hhigh : G.dist u v ≤ G.dist u w + G.dist w v := hG.connected.dist_triangle
    have huwlen : G.dist u w = 1 := G.dist_eq_one_iff_adj.mpr huw
    simp only [Walk.length_cons] at hplen
    rw [huwlen] at hhigh
    omega
  refine ⟨w, ⟨huw, hfirst⟩, ?_⟩
  intro z hz
  obtain ⟨r, hr, hrlen⟩ := hG.connected.exists_path_of_dist z v
  have hu : u ∉ r.support := by
    intro hu
    have h₁ := G.dist_le (r.dropUntil u hu)
    have h₂ := r.length_dropUntil_le_length hu
    omega
  have hcons : (Walk.cons hz.1 r).IsPath := hr.cons hu
  have heq : Walk.cons hz.1 r = Walk.cons huw q :=
    congrArg Subtype.val ((hG.isAcyclic.subsingleton_path u v).elim
      ⟨Walk.cons hz.1 r, hcons⟩ ⟨Walk.cons huw q, hp⟩)
  simpa only [Walk.snd_cons] using congrArg Walk.snd heq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem other_neighbor_distance (hG : G.IsTree) {u v p w : V}
    (hunique : ∀ z, G.Adj u z ∧ G.dist z v + 1 = G.dist u v → z = p)
    (hw : G.Adj u w) (hwp : w ≠ p) : G.dist w v = G.dist u v + 1 := by
  have hdist := hG.dist_eq_dist_add_one_of_adj v hw
  rw [G.dist_comm (u := v) (v := u), G.dist_comm (u := v) (v := w)] at hdist
  rcases hdist with hdist | hdist
  · exact False.elim (hwp (hunique w ⟨hw, hdist.symm⟩))
  · exact hdist

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem distance_lt_card (hG : G.IsTree) (u v : V) :
    G.dist u v < Fintype.card V := by
  obtain ⟨p, hp, hplen⟩ := hG.connected.exists_path_of_dist u v
  rw [← hplen]
  exact hp.length_lt

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Summing all distance indicators below an order bound gives the literal all-ones matrix. -/
theorem sum_distanceMatrix_eq_ones (hG : G.IsTree) {N : ℕ}
    (hN : Fintype.card V ≤ N) :
    ∑ k ∈ Finset.range N, distanceMatrix G k = onesMatrix (V := V) := by
  ext u v
  have hdist : G.dist u v < N := lt_of_lt_of_le (distance_lt_card G hG u v) hN
  simp [Matrix.sum_apply, distanceMatrix, onesMatrix, Finset.mem_range, hdist]

omit [DecidableEq V] in
theorem adjacency_mul_distance_apply (k : ℕ) (u v : V) :
    (G.adjMatrix ℤ * distanceMatrix G k) u v =
      ∑ w ∈ G.neighborFinset u, distanceMatrix G k w v := by
  exact G.adjMatrix_mulVec_apply u (fun w => distanceMatrix G k w v)

omit [DecidableEq V] in
theorem adjacency_distance_self (k : ℕ) (u : V) :
    (G.adjMatrix ℤ * distanceMatrix G k) u u =
      if k = 1 then (G.degree u : ℤ) else 0 := by
  rw [adjacency_mul_distance_apply]
  have hs : (∑ w ∈ G.neighborFinset u, distanceMatrix G k w u) =
      ∑ w ∈ G.neighborFinset u, (if k = 1 then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro w hw
    have hdist : G.dist w u = 1 :=
      G.dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset u w).mp hw).symm
    simp [distanceMatrix, hdist, eq_comm]
  rw [hs]
  split_ifs <;> simp [SimpleGraph.card_neighborFinset_eq_degree]

theorem adjacency_distance_of_ne (hG : G.IsTree) (k : ℕ) {u v : V} (huv : u ≠ v) :
    (G.adjMatrix ℤ * distanceMatrix G k) u v =
      if G.dist u v + 1 = k then (G.degree u : ℤ) - 1
      else if G.dist u v = k + 1 then 1 else 0 := by
  obtain ⟨p, hp, huniq⟩ := unique_predecessor G hG huv
  have hpmem : p ∈ G.neighborFinset u := (G.mem_neighborFinset u p).mpr hp.1
  have hrest : (∑ w ∈ (G.neighborFinset u).erase p, distanceMatrix G k w v) =
      (((G.neighborFinset u).erase p).card : ℤ) *
        (if G.dist u v + 1 = k then 1 else 0) := by
    calc
      _ = ∑ w ∈ (G.neighborFinset u).erase p,
          (if G.dist u v + 1 = k then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        obtain ⟨hwp, hwm⟩ := Finset.mem_erase.mp hw
        have hdist := other_neighbor_distance G hG huniq
          ((G.mem_neighborFinset u w).mp hwm) hwp
        simp only [distanceMatrix, hdist]
      _ = _ := by simp
  have hcard : (((G.neighborFinset u).erase p).card : ℤ) = (G.degree u : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem hpmem, SimpleGraph.card_neighborFinset_eq_degree]
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hp.1.degree_pos_left), Nat.cast_one]
  have hind : distanceMatrix G k p v = if G.dist u v = k + 1 then 1 else 0 := by
    have heq : (G.dist p v = k) ↔ (G.dist u v = k + 1) := by omega
    simp only [distanceMatrix, heq]
  rw [adjacency_mul_distance_apply,
    ← Finset.add_sum_erase (G.neighborFinset u) (fun w => distanceMatrix G k w v) hpmem,
    hrest, hcard, hind]
  by_cases h : G.dist u v + 1 = k
  · have hnot : G.dist u v ≠ k + 1 := by omega
    simp [h, hnot]
  · simp [h]

theorem distanceMatrix_two (hG : G.IsTree) :
    distanceMatrix G 2 = G.adjMatrix ℤ * G.adjMatrix ℤ - G.degMatrix ℤ := by
  ext u v
  have hA : G.adjMatrix ℤ * G.adjMatrix ℤ =
      G.adjMatrix ℤ * distanceMatrix G 1 := by rw [distanceMatrix_one]
  rw [hA]
  simp only [Matrix.sub_apply]
  by_cases huv : u = v
  · subst v
    rw [adjacency_distance_self]
    simp [distanceMatrix, SimpleGraph.degMatrix]
  · rw [adjacency_distance_of_ne G hG 1 huv]
    have hreach : G.Reachable u v := hG.connected u v
    simp [distanceMatrix, SimpleGraph.degMatrix, huv, hreach]

theorem distanceMatrix_next (hG : G.IsTree) (k : ℕ) :
    distanceMatrix G (k + 3) =
      G.adjMatrix ℤ * distanceMatrix G (k + 2) -
        (G.degMatrix ℤ - 1) * distanceMatrix G (k + 1) := by
  ext u v
  rw [sub_mul, one_mul]
  simp only [Matrix.sub_apply, SimpleGraph.degMatrix, Matrix.diagonal_mul]
  by_cases huv : u = v
  · subst v
    rw [adjacency_distance_self]
    simp [distanceMatrix]
  · rw [adjacency_distance_of_ne G hG (k + 2) huv]
    by_cases hsmall : G.dist u v = k + 1
    · simp [distanceMatrix, hsmall]
    · simp [distanceMatrix, hsmall]

def distancePolynomial : ℕ → Matrix V V ℤ
  | 0 => 1
  | 1 => G.adjMatrix ℤ
  | 2 => G.adjMatrix ℤ * G.adjMatrix ℤ - G.degMatrix ℤ
  | k + 3 => G.adjMatrix ℤ * distancePolynomial (k + 2) -
      (G.degMatrix ℤ - 1) * distancePolynomial (k + 1)

theorem distancePolynomial_eq_distanceMatrix (hG : G.IsTree) (k : ℕ) :
    distancePolynomial G k = distanceMatrix G k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 => exact (distanceMatrix_zero G hG).symm
      | 1 => exact (distanceMatrix_one G).symm
      | 2 => exact (distanceMatrix_two G hG).symm
      | k + 3 =>
          rw [distancePolynomial, ih (k + 2) (by omega), ih (k + 1) (by omega)]
          exact (distanceMatrix_next G hG k).symm

/-- The actual tree polynomial J_N evaluates to 11ᵀ, with no graph-semantic premise. -/
theorem tree_allOnes_identity (hG : G.IsTree) {N : ℕ}
    (hN : Fintype.card V ≤ N) :
    ∑ k ∈ Finset.range N, distancePolynomial G k = onesMatrix (V := V) := by
  simp_rw [distancePolynomial_eq_distanceMatrix G hG]
  exact sum_distanceMatrix_eq_ones G hG hN

/-- The literal expression emitted by the compiler has the same distance recurrence. -/
theorem distance_expression_eval (k : ℕ) :
    (CircuitAudit.Degrees.distance k).eval (G.adjMatrix ℤ) (G.degMatrix ℤ) =
      distancePolynomial G k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      match k with
      | 0 => simp [CircuitAudit.Degrees.distance, CircuitAudit.Degrees.Expr.eval,
          distancePolynomial]
      | 1 => simp [CircuitAudit.Degrees.distance, CircuitAudit.Degrees.Expr.eval,
          distancePolynomial]
      | 2 => simp [CircuitAudit.Degrees.distance, CircuitAudit.Degrees.Expr.eval,
          distancePolynomial, sub_eq_add_neg]
      | k + 3 =>
          simp only [CircuitAudit.Degrees.distance, CircuitAudit.Degrees.Expr.eval,
            ih (k + 2) (by omega), ih (k + 1) (by omega), distancePolynomial]
          simp [sub_eq_add_neg]

theorem expressionSum_eval {R : Type*} [Ring R] (a d : R)
    (ps : List CircuitAudit.Degrees.Expr) :
    (CircuitAudit.Degrees.expressionSum ps).eval a d =
      (ps.map (fun p => p.eval a d)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [CircuitAudit.Degrees.expressionSum, CircuitAudit.Degrees.Expr.eval,
        List.map_cons, List.sum_cons, ih]

theorem allOnes_expression_eval (N : ℕ) :
    (CircuitAudit.Degrees.allOnes N).eval (G.adjMatrix ℤ) (G.degMatrix ℤ) =
      ∑ k ∈ Finset.range N, distancePolynomial G k := by
  simp only [CircuitAudit.Degrees.allOnes, expressionSum_eval, List.map_map,
    Function.comp_def]
  simp_rw [distance_expression_eval]
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, Finset.sum_range_succ, ih]

/-- Graph-semantic endpoint for the actual all-ones AST used by the allowed-gate compiler. -/
theorem actual_allOnes_expression_identity (hG : G.IsTree) {N : ℕ}
    (hN : Fintype.card V ≤ N) :
    (CircuitAudit.Degrees.allOnes N).eval (G.adjMatrix ℤ) (G.degMatrix ℤ) =
      onesMatrix (V := V) := by
  rw [allOnes_expression_eval]
  exact tree_allOnes_identity G hG hN

#print axioms unique_predecessor
#print axioms sum_distanceMatrix_eq_ones
#print axioms distancePolynomial_eq_distanceMatrix
#print axioms tree_allOnes_identity
#print axioms actual_allOnes_expression_identity
end
end ADComplete.TreeDistance
