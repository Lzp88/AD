import PaperVerifier.ADComplete.PSDSpecialization

/-! Actual coefficient length bounds for folded entries and coordinate minors. -/

namespace ADComplete.PSDSpecialization

open Matrix Polynomial
open scoped BigOperators
noncomputable section

lemma length_zsmul (c : ℤ) (p : ℤ[X]) : length (c • p) = ‖c‖ * length p := by
  rw [length_eq_sum _ p.support (Polynomial.support_smul c p)]
  simp only [Polynomial.coeff_smul, smul_eq_mul, norm_mul, length,
    Polynomial.sum_def, Finset.mul_sum]

lemma length_perm_sign {σ : Type*} [Fintype σ] [DecidableEq σ]
    (s : Equiv.Perm σ) (p : ℤ[X]) : length ((s.sign : ℤ) • p) = length p := by
  rw [length_zsmul]
  have hs : ‖(s.sign : ℤ)‖ = 1 := by
    rcases Int.units_eq_one_or s.sign with h | h <;> rw [h] <;> simp
  rw [hs, one_mul]

theorem length_det_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    (M : Matrix σ σ ℤ[X]) (h : σ → ℝ) (_hn : ∀ j, 0 ≤ h j)
    (hM : ∀ i j, length (M i j) ≤ h j) :
    length M.det ≤ (Fintype.card σ).factorial * ∏ j, h j := by
  rw [Matrix.det_apply']
  simp_rw [← zsmul_eq_mul]
  apply (length_sum_le _ _).trans
  calc
    (∑ s : Equiv.Perm σ, length ((s.sign : ℤ) • ∏ j, M (s j) j))
        ≤ ∑ s : Equiv.Perm σ, ∏ j, h j := by
      apply Finset.sum_le_sum
      intro s _
      rw [length_perm_sign]
      exact (length_prod_le _ _).trans
        (Finset.prod_le_prod (fun j _ => length_nonneg _) (fun j _ => hM (s j) j))
    _ = (Fintype.card σ).factorial * ∏ j, h j := by
      simp [Fintype.card_perm, nsmul_eq_mul]

def foldedEntry (m : ℕ) (a : Fin m → ℤ) (j : ℕ) : ℤ[X] :=
  ∑ i : Fin m, monomial i.val ((2 : ℤ) ^ (j*i.val) * a i)

theorem foldedEntry_length (m j J : ℕ) (hj : j ≤ J)
    (a : Fin m → ℤ) (R : ℕ) (hR : ∀ i, ‖a i‖ ≤ R) :
    length (foldedEntry m a j) ≤ m * R * (2 : ℝ) ^ (J*(m-1)) := by
  unfold foldedEntry
  apply (length_sum_le _ _).trans
  calc
    (∑ i : Fin m, length (monomial i.val ((2 : ℤ) ^ (j*i.val) * a i)))
        ≤ ∑ _ : Fin m, (R : ℝ) * (2 : ℝ) ^ (J*(m-1)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [length_monomial, norm_mul, norm_pow]
      have he : j*i.val ≤ J*(m-1) := Nat.mul_le_mul hj (by omega)
      have hp : (2 : ℝ) ^ (j*i.val) ≤ (2 : ℝ) ^ (J*(m-1)) :=
        pow_le_pow_right₀ (by norm_num) he
      have hr := hR i
      have h2 : ‖(2 : ℤ)‖ = (2 : ℝ) := by norm_num [Int.norm_eq_abs]
      rw [h2]
      calc
        (2 : ℝ) ^ (j*i.val) * ‖a i‖
            ≤ (2 : ℝ) ^ (J*(m-1)) * R := by gcongr
        _ = (R : ℝ) * (2 : ℝ) ^ (J*(m-1)) := mul_comm _ _
    _ = m * R * (2 : ℝ) ^ (J*(m-1)) := by simp [nsmul_eq_mul, mul_assoc]

#print axioms length_det_le
#print axioms foldedEntry_length

end
end ADComplete.PSDSpecialization
