import Mathlib

/-! Algebraic determinant differentiation for the Pluecker-coordinate proof. -/

namespace ADComplete.DeterminantDerivation

open Matrix
open scoped BigOperators

variable {R A κ : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem derivation_prod_update [DecidableEq κ] (D : Derivation R A A)
    (s : Finset κ) (f : κ → A) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih,
        Finset.sum_insert ha]
      have hfirst : (∏ j ∈ insert a s, Function.update f a (D (f a)) j) =
          D (f a) * ∏ j ∈ s, f j := by
        rw [Finset.prod_insert ha, Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        exact Function.update_of_ne (by intro h; subst j; exact ha hj) _ _
      have hrest : (∑ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j) =
          f a * ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.prod_insert ha, Function.update_of_ne (by intro h; subst i; exact ha hi)]
      rw [hfirst, hrest]
      ring

theorem derivation_det_columns {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ j, (M.updateCol j (fun i => D (M i j))).det := by
  classical
  rw [Matrix.det_apply']
  simp only [map_sum, Derivation.leibniz, Derivation.map_intCast, smul_eq_mul,
    mul_zero, add_zero]
  simp_rw [derivation_prod_update]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = j
  · subst k
    simp [Matrix.updateCol]
  · simp [Matrix.updateCol, h]

theorem derivation_det_rows {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ j, (M.updateRow j (fun i => D (M j i))).det := by
  simpa only [Matrix.det_transpose, Matrix.updateCol_transpose,
    Matrix.transpose_apply] using derivation_det_columns D M.transpose

#print axioms derivation_det_columns
#print axioms derivation_det_rows

end ADComplete.DeterminantDerivation
