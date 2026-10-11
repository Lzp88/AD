import PaperVerifier.ADComplete.PSDFoldedSubspace
import PaperVerifier.ADComplete.PSDFoldedPrefix
import PaperVerifier.ADComplete.PSDScalarExtension
import PaperVerifier.ADComplete.ConstantFrame

/-! Genuine rank condensation for a constant seed and a vector polynomial. -/

namespace ADComplete.PSDFoldedRank

open Matrix Polynomial Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev F := RatFunc ℝ
variable {ι : Type*} [Fintype ι]

def sourceModule (s : ι → ℝ) (p : ι → ℝ[X]) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ (insert s (Set.range (fun k : ℕ => fun i => (p i).coeff k)))

def polynomialVector (s : ι → ℝ) (p : ι → ℝ[X]) : ℕ → ι → ℝ[X]
  | 0 => fun i => C (s i)
  | j+1 => fun i => PSDFoldedScaling.polynomialScale^[j] (p i)

def rationalVector (s : ι → ℝ) (p : ι → ℝ[X]) : ℕ → ι → F :=
  PSDFoldedPrefix.vector PSDFoldedScaling.scale
    (ScalarExtension.embed (F := F) s) (fun i => algebraMap ℝ[X] F (p i))

omit [Fintype ι] in
theorem rationalVector_polynomial (s : ι → ℝ) (p : ι → ℝ[X]) (k : ℕ) :
    rationalVector s p k = fun i => algebraMap ℝ[X] F (polynomialVector s p k i) := by
  cases k with
  | zero =>
      ext i
      exact (IsScalarTower.algebraMap_apply ℝ ℝ[X] F (s i))
  | succ j =>
      change PSDFoldedKrylov.vector PSDFoldedScaling.scale
        (fun i => algebraMap ℝ[X] F (p i)) j = _
      induction j with
      | zero => rfl
      | succ j ih =>
          rw [PSDFoldedKrylov.vector_succ, ih]
          ext i
          change PSDFoldedScaling.scale
            (algebraMap ℝ[X] F (PSDFoldedScaling.polynomialScale^[j] (p i))) = _
          rw [PSDFoldedScaling.scale_polynomial]
          change _ = algebraMap ℝ[X] F
            (PSDFoldedScaling.polynomialScale^[j+1] (p i))
          rw [Function.iterate_succ_apply']

/-- The first r columns are independent over the rational-function field,
where r is the actual dimension of the real coefficient span including the
constant seed. No condenser rank or polynomial row reduction is assumed. -/
theorem independent_rank_prefix (s : ι → ℝ) (p : ι → ℝ[X]) (hs : s ≠ 0) :
    let r := finrank ℝ (sourceModule s p)
    0 < r ∧ LinearIndependent F (fun j : Fin r =>
      fun i => algebraMap ℝ[X] F (polynomialVector s p j.val i)) := by
  classical
  let U := sourceModule s p
  let q := rationalVector s p
  have hfix : PSDFoldedKrylov.action PSDFoldedScaling.scale
      (ScalarExtension.embed (F := F) s) = ScalarExtension.embed (F := F) s := by
    ext i
    exact PSDFoldedScaling.scale_real (s i)
  have hsF : ScalarExtension.embed (F := F) s ≠ 0 := by
    intro hz
    apply hs
    ext i
    apply (algebraMap ℝ F).injective
    simpa only [ScalarExtension.embed, Pi.zero_apply, map_zero] using congrFun hz i
  obtain ⟨n, hn₀, hn, hli, hInv, hAll⟩ := PSDFoldedPrefix.exists_independent_stable_prefix
    PSDFoldedScaling.scale (ScalarExtension.embed (F := F) s)
      (fun i => algebraMap ℝ[X] F (p i)) hfix hsF
  let V := DifferentialKrylov.krylovSpan q n
  change LinearIndependent F (fun j : Fin n => q j.val) at hli
  change (∀ z ∈ V, PSDFoldedKrylov.action PSDFoldedScaling.scale z ∈ V) at hInv
  change (∀ k, q k ∈ V) at hAll
  obtain ⟨R, s₀, hR, hVR⟩ := PSDFoldedSubspace.scaling_invariant_subspace_constant V hInv
  let W := LinearMap.range R.mulVecLin
  have hsU : s ∈ U := Submodule.subset_span (Set.mem_insert _ _)
  have hcU (k : ℕ) : (fun i => (p i).coeff k) ∈ U :=
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hqU (k : ℕ) : q k ∈ ScalarExtension.extension (F := F) U := by
    cases k with
    | zero => exact ScalarExtension.embed_mem U s hsU
    | succ j =>
        change PSDFoldedKrylov.vector PSDFoldedScaling.scale
          (fun i => algebraMap ℝ[X] F (p i)) j ∈ _
        induction j with
        | zero => exact PSDScalarExtension.polynomial_mem_extension U p hcU
        | succ j ih =>
            rw [PSDFoldedKrylov.vector_succ]
            exact PSDScalarExtension.scale_preserves_extension U _ ih
  have hVU : V ≤ ScalarExtension.extension (F := F) U := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact hqU j.val
  have hsW : s ∈ W := by
    apply ConstantFrame.real_mem_of_embed_mem R s₀ hR s
    rw [← hVR]
    have heq : q 0 = ConstantFrame.embed s := rfl
    rw [← heq]
    exact hAll 0
  have hpW : (fun i => algebraMap ℝ[X] F (p i)) ∈
      LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin := by
    rw [← hVR]
    exact hAll 1
  have hUW : U ≤ W := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with hseed | hcoeff
    · subst z
      exact hsW
    · obtain ⟨k, rfl⟩ := hcoeff
      exact ConstantFrame.polynomial_coeff_mem R s₀ hR p hpW k
  have hWU : W ≤ U := by
    intro z hz
    apply ScalarExtension.reflect_mem (F := F) U z
    have hz' := ConstantFrame.embed_mem R z hz
    rw [← hVR] at hz'
    exact hVU hz'
  have hWeq : W = U := le_antisymm hWU hUW
  have hRi : Function.Injective R.mulVec := by
    intro a b hab
    have hh := congrArg (fun v : ι → ℝ => v ∘ s₀) hab
    change (R.submatrix s₀ id).mulVec a = (R.submatrix s₀ id).mulVec b at hh
    rwa [hR, Matrix.one_mulVec, Matrix.one_mulVec] at hh
  have hrankW : finrank ℝ W = finrank F V := by
    rw [LinearMap.finrank_range_of_inj hRi]
    simp only [Module.finrank_pi, Fintype.card_fin]
  have hrankV : finrank F V = n := by
    simpa only [V, DifferentialKrylov.krylovSpan, Fintype.card_fin] using
      finrank_span_eq_card hli
  have hnrank : n = finrank ℝ U := by
    rw [← hWeq, hrankW, hrankV]
  constructor
  · simpa only [hnrank] using hn₀
  · have hli' : LinearIndependent F (fun j : Fin (finrank ℝ U) => q j.val) := by
      exact hnrank ▸ hli
    have heq : (fun j : Fin (finrank ℝ U) => q j.val) =
        fun j i => algebraMap ℝ[X] F (polynomialVector s p j.val i) := by
      ext j i
      exact congrFun (rationalVector_polynomial s p j.val) i
    rw [heq] at hli'
    exact hli'

#print axioms independent_rank_prefix

end
end ADComplete.PSDFoldedRank
