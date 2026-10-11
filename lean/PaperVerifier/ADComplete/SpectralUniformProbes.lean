import PaperVerifier.ADComplete.SpectralBands
import PaperVerifier.ADComplete.UniformProbeBounds

/-! The prescribed N-squared recurrence under the actual spectral-diameter hypothesis. -/
namespace ADComplete.Spanning

open Matrix
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem uniform_probes_of_spectral_diameter
    (N : ℕ) (hN : 1 ≤ N) (hcard : Fintype.card ι ≤ N)
    (H K : Matrix ι ι ℝ) (hH : H.IsSymm) (hK : K.IsSymm) (v : ι → ℝ)
    (hdiam : SpectralBands.eigenMax K (Matrix.isHermitian_iff_isSymm.mpr hK) -
      SpectralBands.eigenMin K (Matrix.isHermitian_iff_isSymm.mpr hK) ≤ (N : ℝ)-1) :
    Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
      z = probeVector ((N : ℝ)^2) H K v k j} = jointModule H K v := by
  let hKh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  let lo := SpectralBands.eigenMin K hKh
  let hi := SpectralBands.eigenMax K hKh
  let κ : ℝ := (N : ℝ)^2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hκp : 0 < κ := sq_pos_of_pos hNp
  have hκ : κ ≠ 0 := ne_of_gt hκp
  have hband := SpectralBands.spectral_quadratic_interval K hKh
  have hp (u : ι → ℝ) : Rigidity.pairing u ((κ⁻¹ • K).mulVec u) =
      κ⁻¹ * Rigidity.pairing u (K.mulVec u) := by
    simp [Rigidity.pairing, Matrix.smul_mulVec, Finset.mul_sum, mul_left_comm]
  have hb (u : ι → ℝ) :
      (κ⁻¹*lo) * Rigidity.pairing u u ≤ Rigidity.pairing u ((κ⁻¹ • K).mulVec u) ∧
        Rigidity.pairing u ((κ⁻¹ • K).mulVec u) ≤ (κ⁻¹*hi) * Rigidity.pairing u u := by
    rw [hp]
    have hl := mul_le_mul_of_nonneg_left (hband u).1 (inv_nonneg.mpr hκp.le)
    have hh := mul_le_mul_of_nonneg_left (hband u).2 (inv_nonneg.mpr hκp.le)
    constructor
    · simpa only [mul_assoc] using hl
    · simpa only [mul_assoc] using hh
  have hwidth : κ*(κ⁻¹*hi - κ⁻¹*lo) = hi-lo := by
    rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hκ, one_mul, one_mul]
  have hd0 : 0 ≤ hi-lo := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hl : lo ≤ hKh.eigenvalues i := Finset.inf'_le _ (Finset.mem_univ i)
    have hh : hKh.eigenvalues i ≤ hi := Finset.le_sup' _ (Finset.mem_univ i)
    linarith
  have hc : (Fintype.card ι : ℝ) ≤ N := by exact_mod_cast hcard
  have hd : hi-lo ≤ (N : ℝ)-1 := hdiam
  have hprod : (Fintype.card ι : ℝ)*(hi-lo) ≤ (N : ℝ)*((N : ℝ)-1) :=
    (mul_le_mul_of_nonneg_right hc hd0).trans (mul_le_mul_of_nonneg_left hd hNp.le)
  have hgap : (Fintype.card ι : ℝ)*(κ⁻¹*hi - κ⁻¹*lo) < 1 := by
    apply (mul_lt_mul_iff_of_pos_left hκp).mp
    calc
      κ*((Fintype.card ι : ℝ)*(κ⁻¹*hi - κ⁻¹*lo)) =
          (Fintype.card ι : ℝ)*(κ*(κ⁻¹*hi - κ⁻¹*lo)) := by ring
      _ = (Fintype.card ι : ℝ)*(hi-lo) := by rw [hwidth]
      _ ≤ (N : ℝ)*((N : ℝ)-1) := hprod
      _ < κ*1 := by dsimp [κ]; nlinarith
  exact uniform_probe_spanning_of_card_le κ hκ H K hH v
    (κ⁻¹*lo) (κ⁻¹*hi) hb hgap N hcard

#print axioms uniform_probes_of_spectral_diameter

end
end ADComplete.Spanning
