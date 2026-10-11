import Mathlib

/-! Faithful scalar extension of finite real coordinate subspaces. -/

namespace ADComplete.ScalarExtension

open Matrix Polynomial
open scoped BigOperators
noncomputable section

variable {F ι : Type*} [Field F] [Algebra ℝ F] [Fintype ι]

def embed (v : ι → ℝ) : ι → F := fun i => algebraMap ℝ F (v i)

def extension (U : Submodule ℝ (ι → ℝ)) : Submodule F (ι → F) :=
  Submodule.span F {z | ∃ u ∈ U, z = embed u}

omit [Fintype ι] in
theorem embed_mem (U : Submodule ℝ (ι → ℝ)) (u : ι → ℝ) (hu : u ∈ U) :
    embed u ∈ extension (F := F) U := Submodule.subset_span ⟨u, hu, rfl⟩

def extendFunctional (f : (ι → ℝ) →ₗ[ℝ] ℝ) : (ι → F) →ₗ[F] F := by
  classical
  exact {
    toFun := fun v => ∑ i, algebraMap ℝ F (f (Pi.single i 1)) * v i
    map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm] }

theorem extendFunctional_embed (f : (ι → ℝ) →ₗ[ℝ] ℝ) (u : ι → ℝ) :
    extendFunctional (F := F) f (embed u) = algebraMap ℝ F (f u) := by
  classical
  have hu : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hf : f u = ∑ i, u i * f (Pi.single i 1) := by
    conv_lhs => rw [hu]
    simp [map_sum, map_smul]
  rw [hf]
  simp only [extendFunctional, LinearMap.coe_mk, AddHom.coe_mk, embed, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- A real vector belongs to a real subspace exactly when its constant
rational image belongs to the scalar extension. -/
theorem reflect_mem (U : Submodule ℝ (ι → ℝ)) (u : ι → ℝ)
    (hu : embed u ∈ extension (F := F) U) : u ∈ U := by
  classical
  by_contra hnu
  obtain ⟨f, hfu, hUf⟩ := U.exists_le_ker_of_notMem hnu
  have hker : extension (F := F) U ≤ LinearMap.ker (extendFunctional (F := F) f) := by
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, rfl⟩
    change extendFunctional (F := F) f (embed v) = 0
    rw [extendFunctional_embed, show f v = 0 from hUf hv, map_zero]
  have hz : algebraMap ℝ F (f u) = 0 := by
    rw [← extendFunctional_embed]
    exact hker hu
  exact hfu ((algebraMap ℝ F).injective (by simpa using hz))

omit [Fintype ι] in
theorem extension_mono {U V : Submodule ℝ (ι → ℝ)} (h : U ≤ V) :
    extension (F := F) U ≤ extension (F := F) V := by
  apply Submodule.span_le.mpr
  rintro z ⟨u, hu, rfl⟩
  exact embed_mem V u (h hu)

#print axioms reflect_mem

end
end ADComplete.ScalarExtension
