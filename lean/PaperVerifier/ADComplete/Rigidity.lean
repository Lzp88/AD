import Mathlib

/-!
Coefficient-level rigidity for the differential proof of uniform matrix probes.
All statements below use finite real coordinate spaces and ordinary polynomials.
-/

namespace ADComplete.Rigidity

open Polynomial Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Real coordinate pairing, with no normalization. -/
def pairing (u v : ι → ℝ) : ℝ := ∑ i, u i * v i

lemma pairing_self_pos {u : ι → ℝ} (hu : u ≠ 0) : 0 < pairing u u := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  have hi' : 0 < u i * u i := mul_self_pos.mpr hi
  exact lt_of_lt_of_le hi' (Finset.single_le_sum
    (fun j _ => mul_self_nonneg (u j)) (Finset.mem_univ i))

lemma pairing_smul (u v : ι → ℝ) (a : ℝ) :
    pairing u (a • v) = a * pairing u v := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (u _) a, mul_assoc]
  exact (Finset.mul_sum _ _ _).symm

lemma pairing_add (u v w : ι → ℝ) :
    pairing u (v + w) = pairing u v + pairing u w := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

lemma pairing_mulVec_swap (A : Matrix ι ι ℝ) (hA : A.IsSymm) (u v : ι → ℝ) :
    pairing u (A.mulVec v) = pairing v (A.mulVec u) := by
  simp only [pairing, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := congrFun (congrFun hA j) i
  simp only [Matrix.transpose_apply] at h
  rw [h]
  ring

/-- The integer-degree contradiction, before any exterior-power specialization.
The hypotheses are the three actual coefficient equations of a polynomial
connection line, together with a quadratic-form interval for its residue.
This is a coefficient lemma, not the invariant-subspace theorem. -/
theorem coefficient_rigidity
    (B H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi α β : ℝ) (hgap : hi - lo < 1)
    (hB : ∀ u : ι → ℝ,
      lo * pairing u u ≤ pairing u (B.mulVec u) ∧
      pairing u (B.mulVec u) ≤ hi * pairing u u)
    (ell : ℕ) (w₀ wₗ wprev : ι → ℝ)
    (hw₀ : w₀ ≠ 0) (hwₗ : wₗ ≠ 0)
    (hzero : B.mulVec w₀ = α • w₀)
    (htop : H.mulVec wₗ = β • wₗ)
    (hnext : (ell : ℝ) • wₗ + B.mulVec wₗ + H.mulVec wprev =
      α • wₗ + β • wprev) : ell = 0 := by
  have hp₀ := pairing_self_pos hw₀
  have hpₗ := pairing_self_pos hwₗ
  have halpha : α ≤ hi := by
    have hx := (hB w₀).2
    rw [hzero, pairing_smul] at hx
    nlinarith
  have hlower := (hB wₗ).1
  have hcross : pairing wₗ (H.mulVec wprev) = β * pairing wₗ wprev := by
    rw [pairing_mulVec_swap H hH, htop, pairing_smul]
    congr 1
    unfold pairing
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heq := congrArg (pairing wₗ) hnext
  simp only [pairing_add, pairing_smul] at heq
  rw [hcross] at heq
  have hell : (ell : ℝ) < 1 := by nlinarith
  have hell_nat : ell < 1 := by exact_mod_cast hell
  omega

#print axioms coefficient_rigidity

end ADComplete.Rigidity
