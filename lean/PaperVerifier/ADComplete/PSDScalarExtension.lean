import PaperVerifier.ADComplete.PSDFoldedScaling
import PaperVerifier.ADComplete.PSDFoldedKrylov
import PaperVerifier.ADComplete.ScalarExtension

/-! Polynomial coefficient spans and their actual rational scalar extensions. -/

namespace ADComplete.PSDScalarExtension

open Polynomial
open scoped BigOperators
noncomputable section
abbrev F := RatFunc ℝ
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem scale_preserves_extension (U : Submodule ℝ (ι → ℝ)) (z : ι → F)
    (hz : z ∈ ScalarExtension.extension (F := F) U) :
    PSDFoldedKrylov.action PSDFoldedScaling.scale z ∈ ScalarExtension.extension (F := F) U := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      have heq : PSDFoldedKrylov.action PSDFoldedScaling.scale
          (ScalarExtension.embed (F := F) u) = ScalarExtension.embed (F := F) u := by
        ext i
        exact PSDFoldedScaling.scale_real (u i)
      rw [heq]
      exact ScalarExtension.embed_mem U u hu
  | zero => rw [PSDFoldedKrylov.action_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [PSDFoldedKrylov.action_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [PSDFoldedKrylov.action_smul]; exact Submodule.smul_mem _ _ hy

theorem polynomial_mem_extension (U : Submodule ℝ (ι → ℝ)) (p : ι → ℝ[X])
    (hp : ∀ k, (fun i => (p i).coeff k) ∈ U) :
    (fun i => algebraMap ℝ[X] F (p i)) ∈ ScalarExtension.extension (F := F) U := by
  classical
  let ell := Finset.univ.sup (fun i => (p i).natDegree)
  have hd (i : ι) : (p i).natDegree < ell+1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i))
  have hsum : (∑ k ∈ Finset.range (ell+1), (algebraMap ℝ[X] F X)^k •
      ScalarExtension.embed (F := F) (fun i => (p i).coeff k)) ∈
      ScalarExtension.extension (F := F) U := by
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (ScalarExtension.embed_mem U _ (hp k))
  have heq : (fun i => algebraMap ℝ[X] F (p i)) =
      ∑ k ∈ Finset.range (ell+1), (algebraMap ℝ[X] F X)^k •
        ScalarExtension.embed (F := F) (fun i => (p i).coeff k) := by
    ext i
    rw [(p i).as_sum_range_C_mul_X_pow' (hd i)]
    simp only [map_sum, map_mul, map_pow, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ScalarExtension.embed]
    apply Finset.sum_congr rfl
    intro k _
    rw [show algebraMap ℝ[X] F (C ((p i).coeff k)) = algebraMap ℝ F ((p i).coeff k)
      from (IsScalarTower.algebraMap_apply ℝ ℝ[X] F _).symm]
    exact mul_comm _ _
  rw [heq]
  exact hsum

#print axioms polynomial_mem_extension

end
end ADComplete.PSDScalarExtension
