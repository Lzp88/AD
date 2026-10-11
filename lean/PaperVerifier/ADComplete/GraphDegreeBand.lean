import PaperVerifier.ADComplete.Rigidity
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! Actual degree-matrix band for the common selector N and scale N². -/
namespace ADComplete.GraphDegreeBand
noncomputable section
open scoped BigOperators
open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem selector_scale_ne_zero (N : ℕ) (hN : 1 ≤ N) : (N : ℝ)^2 ≠ 0 := by
  have h : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  positivity

theorem actual_degree_band (N : ℕ) (hN : 1 ≤ N) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : Fintype.card V ≤ N) (u : V → ℝ) :
    0 * Rigidity.pairing u u ≤
        Rigidity.pairing u ((((N : ℝ)^2)⁻¹ • G.degMatrix ℝ).mulVec u) ∧
      Rigidity.pairing u ((((N : ℝ)^2)⁻¹ • G.degMatrix ℝ).mulVec u) ≤
        (((N : ℝ) - 1) / (N : ℝ)^2) * Rigidity.pairing u u := by
  have hInv : (0 : ℝ) ≤ ((N : ℝ)^2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hdeg (i : V) : (G.degree i : ℝ) ≤ (N : ℝ) - 1 := by
    have hd : G.degree i + 1 ≤ N := (G.degree_lt_card_verts i).trans_le hn |>.succ_le
    have hd' : (G.degree i : ℝ) + 1 ≤ N := by exact_mod_cast hd
    linarith
  simp only [Rigidity.pairing, Matrix.smul_mulVec, Pi.smul_apply,
    smul_eq_mul, G.degMatrix_mulVec_apply, zero_mul]
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    have hh : u i * (((N : ℝ)^2)⁻¹ * ((G.degree i : ℝ) * u i)) =
        (((N : ℝ)^2)⁻¹ * (G.degree i : ℝ)) * (u i)^2 := by ring
    rw [hh]
    positivity
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hcoeff : ((N : ℝ)^2)⁻¹ * (G.degree i : ℝ) ≤
        ((N : ℝ) - 1) / (N : ℝ)^2 := by
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left (hdeg i) hInv
    have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u i))
    convert hm using 1 <;> ring

omit [DecidableEq V] in
theorem actual_degree_gap (N : ℕ) (hN : 1 ≤ N) (hn : Fintype.card V ≤ N) :
    (Fintype.card V : ℝ) * ((((N : ℝ) - 1) / (N : ℝ)^2) - 0) < 1 := by
  have hn' : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast hn
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ)^2 := by positivity
  rw [sub_zero, ← mul_div_assoc, div_lt_one hpos]
  nlinarith

#print axioms actual_degree_band
#print axioms actual_degree_gap
end
end ADComplete.GraphDegreeBand
