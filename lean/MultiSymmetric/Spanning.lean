import MultiSymmetric.Rigidity
import MultiSymmetric.Cyclic
import PaperVerifier.ADComplete.RankSensitiveProbes
set_option autoImplicit false

namespace MultiSymmetric.Spanning
open Matrix Polynomial Module
open scoped BigOperators
open ADComplete
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev RF := RatFunc ℝ
variable {τ ι : Type*} [Fintype τ] [Nonempty τ] [Fintype ι]

def coefficientVector (a : τ → ℝ) (κ : ℝ) (H : Matrix ι ι ℝ)
    (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k j : ℕ) : ι → ℝ :=
  fun i => (Krylov.polynomialVector a κ H A v k i).coeff j

omit [Nonempty τ] in
theorem polynomialVector_expansion (a : τ → ℝ) (κ : ℝ)
    (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) :
    (fun i => algebraMap ℝ[X] RF (Krylov.polynomialVector a κ H A v k i)) =
      ∑ j ∈ Finset.range (Fintype.card τ * k + 1),
        (algebraMap ℝ[X] RF X)^j •
          ScalarExtension.embed (F := RF) (coefficientVector a κ H A v k j) := by
  classical
  ext i
  have he : Krylov.polynomialVector a κ H A v k i =
      ∑ j ∈ Finset.range (Fintype.card τ * k + 1),
        C ((Krylov.polynomialVector a κ H A v k i).coeff j) * X^j := by
    simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
      Polynomial.as_sum_range' (Krylov.polynomialVector a κ H A v k i)
        (Fintype.card τ * k + 1) (by
          have h := Krylov.polynomialVector_natDegree_le a κ H A v k i
          omega)
  rw [he]
  simp only [map_sum, map_mul, map_pow, ADComplete.Spanning.rational_map_C,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ScalarExtension.embed, coefficientVector]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- The literal multipole coefficient vectors span the actual cyclic module.
The invariant rational subspace and its constant frame are derived internally. -/
theorem rank_sensitive_spanning (a : τ → ℝ) (ha : Function.Injective a)
    (κ : ℝ) (hκ : κ ≠ 0) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (lo hi : τ → ℝ)
    (hB : ∀ b u,
      lo b * ADComplete.Rigidity.pairing u u ≤
        ADComplete.Rigidity.pairing u ((κ⁻¹ • A b).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((κ⁻¹ • A b).mulVec u) ≤
        hi b * ADComplete.Rigidity.pairing u u)
    (hgap : (Fintype.card ι : ℝ) * (∑ b, (hi b-lo b)) < 1) :
    let r := finrank ℝ (Cyclic.jointModule H A v)
    Submodule.span ℝ {z | ∃ k < r, ∃ j ≤ Fintype.card τ*k,
      z = coefficientVector a κ H A v k j} = Cyclic.jointModule H A v ∧
      LinearIndependent RF (fun j : Fin r => Krylov.rationalKrylov a κ H A v j.val) ∧
      (∀ k, Krylov.rationalKrylov a κ H A v k ∈
        DifferentialKrylov.krylovSpan (Krylov.rationalKrylov a κ H A v) r) := by
  classical
  let D := RationalDerivative.derivative
  let Cn := MultiSymmetric.Rigidity.rationalConnection a (fun b => κ⁻¹ • A b) H
  let q := Krylov.rationalKrylov a κ H A v
  obtain ⟨n, _, hind, hInv, hAll⟩ :=
    DifferentialKrylov.exists_independent_stable_prefix D Cn (ConstantFrame.embed v)
  let V := DifferentialKrylov.krylovSpan q n
  let U := Submodule.span ℝ {z | ∃ k < n, ∃ j ≤ Fintype.card τ*k,
    z = coefficientVector a κ H A v k j}
  change LinearIndependent RF (fun j : Fin n => q j.val) at hind
  have hq (k : ℕ) : q k ∈ V := hAll k
  have hV : ∀ z ∈ V, DifferentialKrylov.connection D Cn z ∈ V := hInv
  have hgapV : (finrank RF V : ℝ) * (∑ b, (hi b-lo b)) < 1 := by
    have hd : (finrank RF V : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast (show finrank RF V ≤ Fintype.card ι from by simpa using V.finrank_le)
    by_cases hw : 0 ≤ ∑ b, (hi b-lo b)
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hd hw) hgap
    · have hh : (finrank RF V : ℝ) * (∑ b, (hi b-lo b)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_ge hw)
      linarith
  obtain ⟨R,s₀,hR,hVR,hpres⟩ := MultiSymmetric.Rigidity.constant_and_invariant_rank
    a ha (fun b => κ⁻¹ • A b) H hH lo hi hB V hgapV hV
  let W := LinearMap.range R.mulVecLin
  have hA (b : τ) (z : ι → ℝ) (hz : z ∈ W) : (A b).mulVec z ∈ W := by
    have hm : (A b).mulVec z = κ • (κ⁻¹ • A b).mulVec z := by
      rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hκ, one_smul]
    rw [hm]
    exact W.smul_mem κ ((hpres z hz).2 b)
  have hseed : v ∈ W := by
    apply ConstantFrame.real_mem_of_embed_mem R s₀ hR v
    rw [← hVR]
    have hzero : q 0 = ConstantFrame.embed v := rfl
    rw [← hzero]
    exact hq 0
  have hjoint : Cyclic.jointModule H A v ≤ W := by
    apply Submodule.span_le.mpr
    rintro z ⟨w,rfl⟩
    induction w with
    | nil => exact hseed
    | cons b w ih =>
        cases b with
        | none => exact (hpres _ ih).1
        | some b => exact hA b _ ih
  have hVU : V ≤ ScalarExtension.extension (F := RF) U := by
    apply Submodule.span_le.mpr
    rintro z ⟨k,rfl⟩
    have hpoly : (fun i => algebraMap ℝ[X] RF
        (Krylov.polynomialVector a κ H A v k.val i)) ∈
        ScalarExtension.extension (F := RF) U := by
      rw [polynomialVector_expansion]
      apply Submodule.sum_mem
      intro j hj
      apply Submodule.smul_mem
      apply ScalarExtension.embed_mem
      exact Submodule.subset_span ⟨k.val,k.isLt,j,
        (by have := Finset.mem_range.mp hj; omega),rfl⟩
    rw [Krylov.polynomialVector_rationalKrylov a κ hκ H A v k.val] at hpoly
    have ha' : algebraMap ℝ RF κ * algebraMap ℝ[X] RF (MultiSymmetric.Rigidity.denom a) ≠ 0 :=
      mul_ne_zero ((_root_.map_ne_zero _).mpr hκ)
        (RatFunc.algebraMap_ne_zero (MultiSymmetric.Rigidity.denom_monic a).ne_zero)
    have hm := (ScalarExtension.extension (F := RF) U).smul_mem
      (((algebraMap ℝ RF κ * algebraMap ℝ[X] RF (MultiSymmetric.Rigidity.denom a))^k.val)⁻¹) hpoly
    change Krylov.rationalKrylov a κ H A v k.val ∈ ScalarExtension.extension (F := RF) U
    simpa only [smul_smul,inv_mul_cancel₀ (pow_ne_zero _ ha'),one_smul] using hm
  have hWU : W ≤ U := by
    intro z hz
    apply ScalarExtension.reflect_mem (F := RF) U z
    have hz' := ConstantFrame.embed_mem R z hz
    rw [← hVR] at hz'
    exact hVU hz'
  have hUjoint : U ≤ Cyclic.jointModule H A v := by
    apply Submodule.span_le.mpr
    rintro z ⟨k,hk,j,hj,rfl⟩
    exact Cyclic.polynomialVector_coeff_mem a κ H A v k j
  have hspan : U = Cyclic.jointModule H A v := le_antisymm hUjoint (hjoint.trans hWU)
  have hWjoint : W = Cyclic.jointModule H A v := le_antisymm (hWU.trans hUjoint) hjoint
  have hRi : Function.Injective R.mulVec := by
    intro x y hxy
    have hh := congrArg (fun z : ι → ℝ => z ∘ s₀) hxy
    change (R.submatrix s₀ id).mulVec x = (R.submatrix s₀ id).mulVec y at hh
    rwa [hR,Matrix.one_mulVec,Matrix.one_mulVec] at hh
  have hrankW : finrank ℝ W = finrank RF V := by
    rw [LinearMap.finrank_range_of_inj hRi]
    simp only [Module.finrank_pi,Fintype.card_fin]
  have hrankV : finrank RF V = n := by
    simpa only [V,DifferentialKrylov.krylovSpan,Fintype.card_fin] using finrank_span_eq_card hind
  have hnrank : n = finrank ℝ (Cyclic.jointModule H A v) := by
    rw [← hWjoint,hrankW,hrankV]
  exact ⟨hnrank ▸ hspan,hnrank ▸ hind,fun k => hnrank ▸ hq k⟩

#print axioms rank_sensitive_spanning
end
end MultiSymmetric.Spanning
