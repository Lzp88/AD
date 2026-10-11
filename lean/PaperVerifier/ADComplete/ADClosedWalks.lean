import Mathlib

/-! Literal trace words as degree-weighted closed walks on actual finite graphs. -/
namespace ADComplete.ADClosedWalks
noncomputable section
open scoped BigOperators
open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

def generator (G : SimpleGraph V) [DecidableRel G.Adj] (b : Bool) : Matrix V V ℤ :=
  if b then G.degMatrix ℤ else G.adjMatrix ℤ

def wordMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : List Bool → Matrix V V ℤ
  | [] => 1
  | b :: w => generator G b * wordMatrix G w

def chainWeight (G : SimpleGraph V) [DecidableRel G.Adj] :
    (w : List Bool) → V → V → (Fin w.length → V) → ℤ
  | [], u, v, _ => if u = v then 1 else 0
  | b :: w, u, v, x => generator G b u (x 0) * chainWeight G w (x 0) v (Fin.tail x)

theorem wordMatrix_chain_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : List Bool) (u v : V) :
    wordMatrix G w u v = ∑ x : Fin w.length → V, chainWeight G w u v x := by
  induction w generalizing u v with
  | nil => simp [wordMatrix, chainWeight, Matrix.one_apply]
  | cons b w ih =>
      rw [wordMatrix, Matrix.mul_apply]
      simp_rw [ih]
      trans ∑ p : V × (Fin w.length → V),
        generator G b u p.1 * chainWeight G w p.1 v p.2
      · simp only [Fintype.sum_prod_type, Finset.mul_sum]
      · exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (w.length + 1) => V))
          (fun p => generator G b u p.1 * chainWeight G w p.1 v p.2)
          (fun x => chainWeight G (b :: w) u v x) (fun p => by
            simp only [Fin.consEquiv, Equiv.coe_fn_mk, chainWeight, Fin.cons_zero, Fin.tail_cons])

theorem trace_word_as_closed_chain_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : List Bool) :
    Matrix.trace (wordMatrix G w) = ∑ u : V, ∑ x : Fin w.length → V,
      chainWeight G w u u x := by
  simp only [Matrix.trace, Matrix.diag, wordMatrix_chain_sum]

def valid (G : SimpleGraph V) : (w : List Bool) → V → V → (Fin w.length → V) → Prop
  | [], u, v, _ => u = v
  | false :: w, u, v, x => G.Adj u (x 0) ∧ valid G w (x 0) v (Fin.tail x)
  | true :: w, u, v, x => u = x 0 ∧ valid G w (x 0) v (Fin.tail x)

def degreeWeight (G : SimpleGraph V) [DecidableRel G.Adj] :
    (w : List Bool) → V → (Fin w.length → V) → ℤ
  | [], _, _ => 1
  | false :: w, _, x => degreeWeight G w (x 0) (Fin.tail x)
  | true :: w, u, x => G.degree u * degreeWeight G w (x 0) (Fin.tail x)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (w : List Bool) (u v : V)
    (x : Fin w.length → V) : Decidable (valid G w u v x) := Classical.propDecidable _

theorem chainWeight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : List Bool) (u v : V) (x : Fin w.length → V) :
    chainWeight G w u v x = if valid G w u v x then degreeWeight G w u x else 0 := by
  induction w generalizing u v with
  | nil => by_cases h : u = v <;> simp [chainWeight, valid, degreeWeight, h]
  | cons b w ih =>
      cases b
      · simp only [chainWeight, generator, Bool.false_eq_true, if_false,
          SimpleGraph.adjMatrix_apply, ih, valid, degreeWeight]
        split_ifs <;> simp_all
      · simp only [chainWeight, generator, if_true,
          SimpleGraph.degMatrix, Matrix.diagonal_apply, ih, valid, degreeWeight]
        split_ifs <;> simp_all

/-- D steps are literal stays with degree weights; only A steps traverse an edge. -/
theorem trace_word_as_weighted_closed_walks (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : List Bool) :
    Matrix.trace (wordMatrix G w) = ∑ u : V, ∑ x : Fin w.length → V,
      if valid G w u u x then degreeWeight G w u x else 0 := by
  rw [trace_word_as_closed_chain_sum]
  simp_rw [chainWeight_eq]

def adjacencyCount (w : List Bool) : ℕ := w.count false

def toWalk (G : SimpleGraph V) :
    (w : List Bool) → (u v : V) → (x : Fin w.length → V) →
      valid G w u v x → G.Walk u v
  | [], _, _, _, h => h ▸ .nil
  | false :: w, _, v, x, h => .cons h.1 (toWalk G w (x 0) v (Fin.tail x) h.2)
  | true :: w, _, v, x, h => h.1 ▸ toWalk G w (x 0) v (Fin.tail x) h.2

omit [Fintype V] [DecidableEq V] in
theorem toWalk_length (G : SimpleGraph V) (w : List Bool) (u v : V)
    (x : Fin w.length → V) (h : valid G w u v x) :
    (toWalk G w u v x h).length = adjacencyCount w := by
  induction w generalizing u v with
  | nil => cases h; rfl
  | cons b w ih =>
      cases b
      · simp only [toWalk, SimpleGraph.Walk.length_cons, ih, adjacencyCount,
          List.count_cons_self]
      · obtain ⟨hu, hv⟩ := h
        subst u
        simp only [toWalk, ih, adjacencyCount, List.count_cons_of_ne (by decide : true ≠ false)]

omit [Fintype V] [DecidableEq V] in
theorem positions_mem_support (G : SimpleGraph V) (w : List Bool) (u v : V)
    (x : Fin w.length → V) (h : valid G w u v x) (i : Fin (w.length + 1)) :
    (Fin.cons u x : Fin (w.length + 1) → V) i ∈ (toWalk G w u v x h).support := by
  induction w generalizing u v with
  | nil =>
      cases h
      fin_cases i
      simp [toWalk]
  | cons b w ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (toWalk G (b :: w) u v x h).start_mem_support
      · cases b
        · simp only [Fin.cons_succ, toWalk, SimpleGraph.Walk.support_cons,
            List.mem_cons]
          apply Or.inr
          simpa only [Fin.cons_self_tail] using ih (x 0) v (Fin.tail x) h.2 j
        · obtain ⟨hu, hv⟩ := h
          subst u
          simpa only [Fin.cons_succ, toWalk, Fin.cons_self_tail] using
            ih (x 0) v (Fin.tail x) hv j

#print axioms trace_word_as_weighted_closed_walks
#print axioms toWalk_length
#print axioms positions_mem_support
end
end ADComplete.ADClosedWalks
