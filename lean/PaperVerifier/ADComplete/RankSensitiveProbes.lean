import PaperVerifier.ADComplete.SmallResidueRigidity
import PaperVerifier.ADComplete.ConstantFrame
import PaperVerifier.ADComplete.ScalarExtension
import PaperVerifier.ADComplete.ProbeKrylov
import PaperVerifier.ADComplete.DifferentialRank

/-! Rank-sensitive spanning and the actual first dependence of the fixed probes. -/

namespace ADComplete.Spanning

open Matrix Polynomial Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/-- The fixed triangular family spans the actual joint cyclic module for
every prescribed seed. The real-frame conclusion and all differential
Krylov stability used in the proof are proved, not assumed. -/
theorem rank_sensitive_probe_spanning (κ : ℝ) (hκ : κ ≠ 0)
    (H K : Matrix ι ι ℝ) (hH : H.IsSymm) (v : ι → ℝ)
    (lo hi : ℝ)
    (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u ((κ⁻¹ • K).mulVec u) ∧
      Rigidity.pairing u ((κ⁻¹ • K).mulVec u) ≤ hi * Rigidity.pairing u u)
    (hgap : (Fintype.card ι : ℝ) * (hi - lo) < 1) :
    let r := finrank ℝ (jointModule H K v)
    Submodule.span ℝ {z | ∃ k < r, ∃ j ≤ k,
      z = probeVector κ H K v k j} = jointModule H K v ∧
      LinearIndependent F (fun j : Fin r => rationalKrylov κ H K v j.val) ∧
      (∀ k, rationalKrylov κ H K v k ∈
        DifferentialKrylov.krylovSpan (rationalKrylov κ H K v) r) := by
  let D := RationalDerivative.derivative
  let A := RationalLineNormalization.rationalConnection (κ⁻¹ • K) H
  let q := rationalKrylov κ H K v
  obtain ⟨n, _, hind, hInv, hAll⟩ :=
    DifferentialKrylov.exists_independent_stable_prefix D A (rationalSeed v)
  let V := DifferentialKrylov.krylovSpan q n
  let U := Submodule.span ℝ {z | ∃ k < n, ∃ j ≤ k,
    z = probeVector κ H K v k j}
  change LinearIndependent F (fun j : Fin n => q j.val) at hind
  have hq (k : ℕ) : q k ∈ V := hAll k
  have hV : ∀ z ∈ V, DifferentialKrylov.connection D A z ∈ V := hInv
  obtain ⟨R, s₀, hR, hVR⟩ := SmallResidueRigidity.invariant_subspace_constant
    (κ⁻¹ • K) H hH lo hi hB hgap V hV
  let W := LinearMap.range R.mulVecLin
  have hRInv : ∀ z ∈ LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin,
      DifferentialKrylov.connection RationalDerivative.derivative A z ∈
        LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin := by
    intro z hz
    rw [← hVR] at hz ⊢
    exact hV z hz
  have hpres (z : ι → ℝ) (hz : z ∈ W) :
      (κ⁻¹ • K).mulVec z ∈ W ∧ H.mulVec z ∈ W :=
    ConstantFrame.real_invariance R s₀ hR (κ⁻¹ • K) H hRInv z hz
  have hK (z : ι → ℝ) (hz : z ∈ W) : K.mulVec z ∈ W := by
    have hm : K.mulVec z = κ • (κ⁻¹ • K).mulVec z := by
      rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hκ, one_smul]
    rw [hm]
    exact W.smul_mem κ (hpres z hz).1
  have hseed : v ∈ W := by
    apply ConstantFrame.real_mem_of_embed_mem R s₀ hR v
    rw [← hVR]
    have hzero : q 0 = ConstantFrame.embed v := rfl
    rw [← hzero]
    exact hq 0
  have hjoint : jointModule H K v ≤ W := by
    apply Submodule.span_le.mpr
    rintro z ⟨w, rfl⟩
    induction w with
    | nil => exact hseed
    | cons b w ih =>
        cases b with
        | false => exact (hpres _ ih).2
        | true => exact hK _ ih
  have hVU : V ≤ ScalarExtension.extension (F := F) U := by
    apply Submodule.span_le.mpr
    rintro z ⟨k, rfl⟩
    have hpoly : (fun i => algebraMap ℝ[X] F (probePolynomial κ H K v k.val i)) ∈
        ScalarExtension.extension (F := F) U := by
      have hsum : (∑ j ∈ Finset.range (k.val + 1),
          (algebraMap ℝ[X] F X) ^ j •
            ScalarExtension.embed (F := F) (probeVector κ H K v k.val j)) ∈
          ScalarExtension.extension (F := F) U := by
        apply Submodule.sum_mem
        intro j hj
        apply Submodule.smul_mem
        apply ScalarExtension.embed_mem
        exact Submodule.subset_span ⟨k.val, k.isLt, j,
          (by have := Finset.mem_range.mp hj; omega), rfl⟩
      have heq : (fun i => algebraMap ℝ[X] F (probePolynomial κ H K v k.val i)) =
          ∑ j ∈ Finset.range (k.val + 1),
            (algebraMap ℝ[X] F X) ^ j •
              ScalarExtension.embed (F := F) (probeVector κ H K v k.val j) := by
        ext i
        simp only [probePolynomial, ← Polynomial.C_mul_X_pow_eq_monomial,
          map_sum, map_mul, map_pow, rational_map_C, ScalarExtension.embed,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      rw [heq]
      exact hsum
    rw [probePolynomial_rationalKrylov κ hκ H K v k.val] at hpoly
    have ha : algebraMap ℝ F κ * algebraMap ℝ[X] F X ≠ 0 :=
      mul_ne_zero ((_root_.map_ne_zero _).mpr hκ)
        (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)
    have hm := (ScalarExtension.extension (F := F) U).smul_mem
      (((algebraMap ℝ F κ * algebraMap ℝ[X] F X) ^ k.val)⁻¹) hpoly
    change rationalKrylov κ H K v k.val ∈ ScalarExtension.extension (F := F) U
    simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ha), one_smul] using hm
  have hWU : W ≤ U := by
    intro z hz
    apply ScalarExtension.reflect_mem (F := F) U z
    have hz' := ConstantFrame.embed_mem R z hz
    rw [← hVR] at hz'
    exact hVU hz'
  have hspan : U = jointModule H K v :=
    le_antisymm (triangular_span_le κ H K v n) (hjoint.trans hWU)
  have hWJoint : W = jointModule H K v :=
    le_antisymm (hWU.trans hspan.le) hjoint
  have hRi : Function.Injective R.mulVec := by
    intro a b hab
    have hh := congrArg (fun z : ι → ℝ => z ∘ s₀) hab
    change (R.submatrix s₀ id).mulVec a = (R.submatrix s₀ id).mulVec b at hh
    rwa [hR, Matrix.one_mulVec, Matrix.one_mulVec] at hh
  have hrankW : finrank ℝ W = finrank F V := by
    rw [LinearMap.finrank_range_of_inj hRi]
    simp only [Module.finrank_pi, Fintype.card_fin]
  have hrankV : finrank F V = n := by
    simpa only [V, DifferentialKrylov.krylovSpan, Fintype.card_fin] using
      finrank_span_eq_card hind
  have hnrank : n = finrank ℝ (jointModule H K v) := by
    rw [← hWJoint, hrankW, hrankV]
  exact ⟨hnrank ▸ hspan, hnrank ▸ hind, fun k => hnrank ▸ hq k⟩

#print axioms rank_sensitive_probe_spanning

end
end ADComplete.Spanning
