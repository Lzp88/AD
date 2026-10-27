import MultiSymmetric.Spanning
import MultiSymmetric.RecurrenceBridge
import MultiSymmetric.RecurrenceDegree
set_option autoImplicit false

namespace MultiSymmetric.Public
open Matrix Module Polynomial
open scoped BigOperators
open ADComplete
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def response (s N : ℕ) (H : Matrix ι ι ℝ) (A : Fin s → Matrix ι ι ℝ)
    (v : ι → ℝ) (k j : ℕ) : ι → ℝ :=
  ((FreeAlgebra.lift ℤ (Fin.cases H A))
    ((Recurrence.universalRow s N k).coeff j)).mulVec v

omit [Nonempty ι] in
theorem response_eq (s N : ℕ) (H : Matrix ι ι ℝ) (A : Fin s → Matrix ι ι ℝ)
    (v : ι → ℝ) (k j : ℕ) :
    response s N H A v k j = Spanning.coefficientVector (fun b : Fin s => (b.val : ℝ))
      ((s : ℝ)*(N : ℝ)^2) H A v k j := by
  have he : FreeAlgebra.lift ℤ (Fin.cases H A)
      ((Recurrence.universalRow s N k).coeff j) =
      (Recurrence.row s ((s : ℤ)*(N : ℤ)^2) H A k).coeff j := by
    simpa using congrArg (fun p : (Matrix ι ι ℝ)[X] => p.coeff j)
      (Recurrence.universalRow_evaluate s N k (Fin.cases H A))
  ext i
  dsimp only [response,Spanning.coefficientVector]
  rw [he,Recurrence.row_coeff_mulVec]
  norm_cast

/-- Literal spectral assumptions imply the exact rank-sensitive span statement
for evaluations of fixed integer free-algebra coefficients. -/
theorem spectral_rank_prefix (s N : ℕ) (hs : 1 ≤ s) (hN : 1 ≤ N)
    (hcard : Fintype.card ι ≤ N) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (A : Fin s → Matrix ι ι ℝ) (hA : ∀ b, (A b).IsSymm) (v : ι → ℝ)
    (hdiam : ∀ b, SpectralBands.eigenMax (A b) (Matrix.isHermitian_iff_isSymm.mpr (hA b)) -
      SpectralBands.eigenMin (A b) (Matrix.isHermitian_iff_isSymm.mpr (hA b)) ≤ (N : ℝ)-1) :
    let r := finrank ℝ (Cyclic.jointModule H A v)
    Submodule.span ℝ {z | ∃ k < r, ∃ j ≤ s*k, z = response s N H A v k j} =
      Cyclic.jointModule H A v := by
  classical
  let : Nonempty (Fin s) := ⟨⟨0,by omega⟩⟩
  let lo (b : Fin s) := SpectralBands.eigenMin (A b) (Matrix.isHermitian_iff_isSymm.mpr (hA b))
  let hi (b : Fin s) := SpectralBands.eigenMax (A b) (Matrix.isHermitian_iff_isSymm.mpr (hA b))
  let κ : ℝ := (s : ℝ)*(N : ℝ)^2
  have hsp : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hκp : 0 < κ := mul_pos hsp (sq_pos_of_pos hNp)
  have hκ : κ ≠ 0 := ne_of_gt hκp
  have hb (b : Fin s) (u : ι → ℝ) :
      (κ⁻¹*lo b) * ADComplete.Rigidity.pairing u u ≤
          ADComplete.Rigidity.pairing u ((κ⁻¹ • A b).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((κ⁻¹ • A b).mulVec u) ≤
          (κ⁻¹*hi b) * ADComplete.Rigidity.pairing u u := by
    have hband := SpectralBands.spectral_quadratic_interval (A b)
      (Matrix.isHermitian_iff_isSymm.mpr (hA b)) u
    have hp : ADComplete.Rigidity.pairing u ((κ⁻¹ • A b).mulVec u) =
        κ⁻¹ * ADComplete.Rigidity.pairing u ((A b).mulVec u) := by
      simp [ADComplete.Rigidity.pairing,Matrix.smul_mulVec,Finset.mul_sum,mul_left_comm]
    rw [hp]
    constructor
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hband.1 (inv_nonneg.mpr hκp.le)
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hband.2 (inv_nonneg.mpr hκp.le)
  have hc : (Fintype.card ι : ℝ) ≤ N := by exact_mod_cast hcard
  have hprod (b : Fin s) : (Fintype.card ι : ℝ)*(hi b-lo b) ≤ (N : ℝ)*((N : ℝ)-1) := by
    have hd0 : 0 ≤ hi b-lo b := by
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hl : lo b ≤ (Matrix.isHermitian_iff_isSymm.mpr (hA b)).eigenvalues i :=
        Finset.inf'_le _ (Finset.mem_univ i)
      have hh : (Matrix.isHermitian_iff_isSymm.mpr (hA b)).eigenvalues i ≤ hi b :=
        Finset.le_sup' _ (Finset.mem_univ i)
      linarith
    exact (mul_le_mul_of_nonneg_right hc hd0).trans
      (mul_le_mul_of_nonneg_left (hdiam b) hNp.le)
  have hgap : (Fintype.card ι : ℝ)*(∑ b, (κ⁻¹*hi b-κ⁻¹*lo b))<1 := by
    apply (mul_lt_mul_iff_of_pos_left hκp).mp
    calc
      κ*((Fintype.card ι : ℝ)*(∑ b, (κ⁻¹*hi b-κ⁻¹*lo b))) =
          ∑ b,(Fintype.card ι : ℝ)*(hi b-lo b) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            field_simp
      _ ≤ ∑ b : Fin s,(N : ℝ)*((N : ℝ)-1) := Finset.sum_le_sum (fun b _ => hprod b)
      _ = (s : ℝ)*((N : ℝ)*((N : ℝ)-1)) := by simp
      _ < κ*1 := by dsimp [κ]; nlinarith
  have ha : Function.Injective (fun b : Fin s => (b.val : ℝ)) := by
    intro b c hbc
    apply Fin.ext
    change (b.val : ℝ) = (c.val : ℝ) at hbc
    exact_mod_cast hbc
  have h := (Spanning.rank_sensitive_spanning (fun b : Fin s => (b.val : ℝ)) ha
    κ hκ H hH A v (fun b => κ⁻¹*lo b) (fun b => κ⁻¹*hi b) hb hgap).1
  simpa only [κ,Fintype.card_fin,← response_eq] using h

theorem spectral_full_family (s N : ℕ) (hs : 1 ≤ s) (hN : 1 ≤ N)
    (hcard : Fintype.card ι ≤ N) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (A : Fin s → Matrix ι ι ℝ) (hA : ∀ b, (A b).IsSymm) (v : ι → ℝ)
    (hdiam : ∀ b, SpectralBands.eigenMax (A b) (Matrix.isHermitian_iff_isSymm.mpr (hA b)) -
      SpectralBands.eigenMin (A b) (Matrix.isHermitian_iff_isSymm.mpr (hA b)) ≤ (N : ℝ)-1) :
    Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ s*k, z = response s N H A v k j} =
      Cyclic.jointModule H A v := by
  have hr : finrank ℝ (Cyclic.jointModule H A v) ≤ N :=
    (by simpa using (Cyclic.jointModule H A v).finrank_le :
      finrank ℝ (Cyclic.jointModule H A v) ≤ Fintype.card ι) |>.trans hcard
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨k,hk,j,hj,rfl⟩
    rw [response_eq]
    exact Cyclic.polynomialVector_coeff_mem _ _ H A v k j
  · rw [← spectral_rank_prefix s N hs hN hcard H hH A hA v hdiam]
    apply Submodule.span_mono
    rintro z ⟨k,hk,j,hj,rfl⟩
    exact ⟨k,lt_of_lt_of_le hk hr,j,hj,rfl⟩

#print axioms spectral_rank_prefix
#print axioms spectral_full_family
end
end MultiSymmetric.Public
