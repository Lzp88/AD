import PaperVerifier.ADComplete.DifferentialKrylov

/-! First dependence for actual semilinear scaling iterates. -/

namespace ADComplete.PSDFoldedKrylov

open Matrix
noncomputable section
variable {F ι : Type*} [Field F] [Algebra ℝ F] [Fintype ι]

def action (sigma : F →ₐ[ℝ] F) (v : ι → F) : ι → F := fun i => sigma (v i)
def vector (sigma : F →ₐ[ℝ] F) (v : ι → F) (k : ℕ) : ι → F :=
  (action sigma)^[k] v

omit [Fintype ι] in
lemma action_zero (sigma : F →ₐ[ℝ] F) : action (ι := ι) sigma 0 = 0 := by
  ext i
  simp [action]

omit [Fintype ι] in
lemma action_add (sigma : F →ₐ[ℝ] F) (v w : ι → F) :
    action sigma (v+w) = action sigma v + action sigma w := by
  ext i
  simp [action]

omit [Fintype ι] in
lemma action_smul (sigma : F →ₐ[ℝ] F) (c : F) (v : ι → F) :
    action sigma (c • v) = sigma c • action sigma v := by
  ext i
  simp [action, smul_eq_mul]

omit [Fintype ι] in
lemma vector_succ (sigma : F →ₐ[ℝ] F) (v : ι → F) (k : ℕ) :
    vector sigma v (k+1) = action sigma (vector sigma v k) := by
  exact Function.iterate_succ_apply' _ _ _

omit [Fintype ι] in
theorem prefix_invariant (sigma : F →ₐ[ℝ] F) (v : ι → F) (n : ℕ)
    (hn : vector sigma v n ∈ DifferentialKrylov.krylovSpan (vector sigma v) n)
    (z : ι → F) (hz : z ∈ DifferentialKrylov.krylovSpan (vector sigma v) n) :
    action sigma z ∈ DifferentialKrylov.krylovSpan (vector sigma v) n := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [← vector_succ]
      by_cases hk : k.val + 1 < n
      · exact DifferentialKrylov.prefix_mem _ hk
      · have heq : k.val + 1 = n := by omega
        simpa only [heq] using hn
  | zero => rw [action_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [action_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [action_smul]; exact Submodule.smul_mem _ _ hy

omit [Fintype ι] in
theorem later_vectors_mem (sigma : F →ₐ[ℝ] F) (v : ι → F) (n : ℕ)
    (hn : vector sigma v n ∈ DifferentialKrylov.krylovSpan (vector sigma v) n)
    (k : ℕ) : vector sigma v k ∈ DifferentialKrylov.krylovSpan (vector sigma v) n := by
  induction k with
  | zero =>
      by_cases hn₀ : n = 0
      · simpa only [hn₀] using hn
      · exact DifferentialKrylov.prefix_mem _ (by omega)
  | succ k ih => rw [vector_succ]; exact prefix_invariant sigma v n hn _ ih

theorem exists_independent_stable_prefix (sigma : F →ₐ[ℝ] F) (v : ι → F) :
    ∃ n ≤ Fintype.card ι,
      LinearIndependent F (fun j : Fin n => vector sigma v j.val) ∧
      (∀ z ∈ DifferentialKrylov.krylovSpan (vector sigma v) n,
        action sigma z ∈ DifferentialKrylov.krylovSpan (vector sigma v) n) ∧
      (∀ k, vector sigma v k ∈ DifferentialKrylov.krylovSpan (vector sigma v) n) := by
  classical
  have hex : ∃ n, vector sigma v n ∈ DifferentialKrylov.krylovSpan (vector sigma v) n :=
    (DifferentialKrylov.exists_dependence (vector sigma v)).imp fun _ h => h.2
  let n := Nat.find hex
  have hn : vector sigma v n ∈ DifferentialKrylov.krylovSpan (vector sigma v) n :=
    Nat.find_spec hex
  have hsmall (k : ℕ) (hk : k < n) :
      vector sigma v k ∉ DifferentialKrylov.krylovSpan (vector sigma v) k :=
    Nat.find_min hex hk
  have hli := DifferentialKrylov.independent_before_first_dependence (vector sigma v) n hsmall
  have hbound : n ≤ Fintype.card ι := by
    obtain ⟨m, hm, hdep⟩ := DifferentialKrylov.exists_dependence (vector sigma v)
    exact (Nat.find_min' hex hdep).trans hm
  exact ⟨n, hbound, hli, fun z hz => prefix_invariant sigma v n hn z hz,
    fun k => later_vectors_mem sigma v n hn k⟩

#print axioms exists_independent_stable_prefix

end
end ADComplete.PSDFoldedKrylov
