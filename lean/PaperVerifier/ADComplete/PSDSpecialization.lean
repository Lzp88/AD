import Mathlib

/-! Integer polynomial coefficient length and a prescribed Cauchy specialization. -/

namespace ADComplete.PSDSpecialization

open Polynomial Matrix NNReal
open scoped BigOperators
noncomputable section

def length (p : ℤ[X]) : ℝ := p.sum (fun _ a => ‖a‖)

lemma length_nonneg (p : ℤ[X]) : 0 ≤ length p := by
  simp only [length, Polynomial.sum_def]
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma length_eq_sum (p : ℤ[X]) (S : Finset ℕ) (hS : p.support ⊆ S) :
    length p = ∑ j ∈ S, ‖p.coeff j‖ := by
  exact Polynomial.sum_eq_of_subset (fun _ a => ‖a‖) (by simp) hS

lemma coeff_norm_le_length (p : ℤ[X]) (j : ℕ) : ‖p.coeff j‖ ≤ length p := by
  by_cases hj : j ∈ p.support
  · exact Finset.single_le_sum (fun _ _ => norm_nonneg _) hj
  · have hz : p.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
    simpa [hz] using length_nonneg p

@[simp] lemma length_zero : length 0 = 0 := by simp [length]

@[simp] lemma length_monomial (j : ℕ) (a : ℤ) : length (monomial j a) = ‖a‖ := by
  simp [length, Polynomial.sum_monomial_index]

@[simp] lemma length_C (a : ℤ) : length (C a) = ‖a‖ := by
  rw [← Polynomial.monomial_zero_left, length_monomial]

lemma length_add_le (p q : ℤ[X]) : length (p + q) ≤ length p + length q := by
  rw [length_eq_sum (p+q) (p.support ∪ q.support) Polynomial.support_add,
    length_eq_sum p _ Finset.subset_union_left,
    length_eq_sum q _ Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => by simpa using norm_add_le (p.coeff j) (q.coeff j)

lemma length_sum_le {α : Type*} (S : Finset α) (p : α → ℤ[X]) :
    length (∑ j ∈ S, p j) ≤ ∑ j ∈ S, length (p j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (length_add_le _ _).trans (add_le_add_right ih _)

lemma length_mul_le (p q : ℤ[X]) : length (p*q) ≤ length p * length q := by
  have hp : p = ∑ i ∈ p.support, monomial i (p.coeff i) := by
    rw [← Polynomial.sum_def, Polynomial.sum_monomial_eq]
  have hq : q = ∑ j ∈ q.support, monomial j (q.coeff j) := by
    rw [← Polynomial.sum_def, Polynomial.sum_monomial_eq]
  conv_lhs => rw [hp, hq]
  rw [Finset.sum_mul]
  apply (length_sum_le _ _).trans
  simp_rw [Finset.mul_sum]
  calc
    (∑ i ∈ p.support, length (∑ j ∈ q.support,
      monomial i (p.coeff i) * monomial j (q.coeff j)))
        ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
          length (monomial i (p.coeff i) * monomial j (q.coeff j)) := by
      apply Finset.sum_le_sum
      intro i _
      exact length_sum_le _ _
    _ = length p * length q := by
      simp only [Polynomial.monomial_mul_monomial, length_monomial, norm_mul]
      simp only [length, Polynomial.sum_def, Finset.sum_mul_sum]

lemma length_prod_le {α : Type*} (S : Finset α) (p : α → ℤ[X]) :
    length (∏ j ∈ S, p j) ≤ ∏ j ∈ S, length (p j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact le_of_eq (by simpa only [Polynomial.C_1, norm_one] using length_C 1)
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (length_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ih (length_nonneg _))

/-- A nonzero integer polynomial whose coefficients are bounded by H cannot
vanish at the prescribed integer H+2. -/
theorem eval_height_plus_two_ne_zero (p : ℤ[X]) (hp : p ≠ 0) (H : ℕ)
    (hcoeff : ∀ j, ‖p.coeff j‖ ≤ H) : p.eval ((H : ℤ) + 2) ≠ 0 := by
  let pr := p.map (Int.castRingHom ℝ)
  have hpr : pr ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hlead : (1 : ℝ≥0) ≤ ‖pr.leadingCoeff‖₊ := by
    have hl : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have ha : (1 : ℝ) ≤ |(p.leadingCoeff : ℝ)| := by
      exact_mod_cast Int.one_le_abs hl
    dsimp only [pr]
    rw [Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
    apply NNReal.coe_le_coe.mp
    change (1 : ℝ) ≤ ‖(p.leadingCoeff : ℝ)‖
    exact ha
  let b : ℝ≥0 := H
  have hsup : (Finset.range pr.natDegree).sup (fun j => ‖pr.coeff j‖₊) ≤ b := by
    apply Finset.sup_le
    intro j _
    have hc := hcoeff j
    rw [show pr.coeff j = (p.coeff j : ℝ) from Polynomial.coeff_map _ _]
    apply NNReal.coe_le_coe.mp
    change ‖(p.coeff j : ℝ)‖ ≤ (H : ℝ)
    exact hc
  have hcb : pr.cauchyBound ≤ b + 1 := by
    unfold Polynomial.cauchyBound
    apply add_le_add _ le_rfl
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hlead)).mpr
    exact hsup.trans (le_mul_of_one_le_right (show 0 ≤ b from zero_le) hlead)
  intro heval
  have hr : pr.IsRoot ((H : ℝ) + 2) := by
    change pr.eval ((H : ℝ) + 2) = 0
    dsimp only [pr]
    have hx : (H : ℝ) + 2 = (Int.castRingHom ℝ) ((H : ℤ) + 2) := by simp
    rw [hx, Polynomial.eval_map_apply, heval, map_zero]
  have hh := (Polynomial.IsRoot.norm_lt_cauchyBound hpr hr).trans_le hcb
  dsimp only [b] at hh
  have hreal : ‖(H : ℝ) + 2‖ < (H : ℝ) + 1 := by exact_mod_cast hh
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hreal
  linarith

theorem eval_length_plus_two_ne_zero (p : ℤ[X]) (hp : p ≠ 0) (H : ℕ)
    (hH : length p ≤ H) : p.eval ((H : ℤ) + 2) ≠ 0 :=
  eval_height_plus_two_ne_zero p hp H fun j => (coeff_norm_le_length p j).trans hH

#print axioms length_mul_le
#print axioms eval_height_plus_two_ne_zero
#print axioms eval_length_plus_two_ne_zero

end
end ADComplete.PSDSpecialization
