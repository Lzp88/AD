import PaperVerifier.ADComplete.DeterminantDerivation

/-! The connection induced on actual rectangular-matrix Pluecker coordinates. -/

namespace ADComplete.PluckerConnection

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

variable {R F ι σ : Type*} [CommRing R] [CommRing F] [Algebra R F]
  [Fintype ι] [Fintype σ] [DecidableEq σ]

noncomputable section

def plucker (P : Matrix ι σ F) (s : σ → ι) : F := (P.submatrix s id).det

def tensorAction (A : Matrix ι ι F) (w : (σ → ι) → F) : (σ → ι) → F :=
  fun s => ∑ k, ∑ j, A (s k) j * w (Function.update s k j)

omit [Algebra R F] [Fintype ι] in
lemma plucker_update (P : Matrix ι σ F) (s : σ → ι) (k : σ) (j : ι) :
    plucker P (Function.update s k j) = ((P.submatrix s id).updateRow k (P j)).det := by
  unfold plucker
  congr 1
  ext a b
  by_cases h : a = k
  · subst a
    simp [Matrix.submatrix, Matrix.updateRow]
  · simp [Matrix.submatrix, Matrix.updateRow, h]

omit [Algebra R F] in
lemma det_updateRow_sum_vectors {τ : Type*} [Fintype τ]
    (M : Matrix σ σ F) (k : σ) (c : τ → F) (u : τ → σ → F) :
    (M.updateRow k (∑ j, c j • u j)).det =
      ∑ j, c j * (M.updateRow k (u j)).det := by
  simp_rw [← Matrix.cramer_transpose_apply]
  simp [map_sum, map_smul, Finset.sum_apply]

omit [Algebra R F] in
lemma tensorAction_plucker (A : Matrix ι ι F) (P : Matrix ι σ F) (s : σ → ι) :
    tensorAction A (plucker P) s =
      ∑ k, ((P.submatrix s id).updateRow k ((A * P) (s k))).det := by
  unfold tensorAction
  apply Finset.sum_congr rfl
  intro k _
  have hrow : (A * P) (s k) = ∑ j, A (s k) j • P j := by
    ext b
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow, det_updateRow_sum_vectors]
  apply Finset.sum_congr rfl
  intro j _
  rw [plucker_update]

omit [Algebra R F] in
lemma det_updateRow_cofactor (M : Matrix σ σ F) (k : σ) (u : σ → F) :
    (M.updateRow k u).det = ∑ j, M.adjugate j k * u j := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  rfl

omit [Algebra R F] in
lemma sum_det_updateRow_right (M C : Matrix σ σ F) :
    (∑ k, (M.updateRow k ((M * C) k)).det) = M.det * C.trace := by
  simp_rw [det_updateRow_cofactor]
  rw [Finset.sum_comm]
  change (M.adjugate * (M * C)).trace = M.det * C.trace
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul]

/-- Invariance of the column span induces an invariant Pluecker line. The
matrix equation is the explicit coordinate equation for the original
connection; the induced scalar is the trace of its coefficient matrix. -/
theorem induced_connection_line (D : Derivation R F F)
    (A : Matrix ι ι F) (P : Matrix ι σ F) (C : Matrix σ σ F)
    (h : ∀ i j, D (P i j) + (A * P) i j = (P * C) i j) (s : σ → ι) :
    D (plucker P s) + tensorAction A (plucker P) s = C.trace * plucker P s := by
  rw [tensorAction_plucker]
  unfold plucker
  rw [ADComplete.DeterminantDerivation.derivation_det_rows,
    ← Finset.sum_add_distrib]
  have hsum : (∑ k, (((P.submatrix s id).updateRow k
      (fun j => D (P (s k) j))).det +
      ((P.submatrix s id).updateRow k ((A * P) (s k))).det)) =
      ∑ k, ((P.submatrix s id).updateRow k ((P * C) (s k))).det := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← Matrix.det_updateRow_add]
    congr 2
    ext j
    exact h (s k) j
  change (∑ k, (((P.submatrix s id).updateRow k
      (fun j => D (P (s k) j))).det +
      ((P.submatrix s id).updateRow k ((A * P) (s k))).det)) =
      C.trace * (P.submatrix s id).det
  rw [hsum]
  have hprod : (P * C).submatrix s id = (P.submatrix s id) * C := by
    ext i j
    rfl
  change (∑ k, ((P.submatrix s id).updateRow k
      (((P * C).submatrix s id) k)).det) = C.trace * (P.submatrix s id).det
  rw [hprod, sum_det_updateRow_right, mul_comm]

#print axioms induced_connection_line

end
end ADComplete.PluckerConnection
