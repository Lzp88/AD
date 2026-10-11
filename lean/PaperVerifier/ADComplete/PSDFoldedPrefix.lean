import PaperVerifier.ADComplete.PSDFoldedKrylov

/-! Independent stable prefixes with a fixed constant first column. -/

namespace ADComplete.PSDFoldedPrefix

open Matrix
noncomputable section
variable {F ι : Type*} [Field F] [Algebra ℝ F] [Fintype ι]

def vector (sigma : F →ₐ[ℝ] F) (s f : ι → F) : ℕ → ι → F
  | 0 => s
  | k+1 => PSDFoldedKrylov.vector sigma f k

omit [Fintype ι] in
theorem prefix_invariant (sigma : F →ₐ[ℝ] F) (s f : ι → F)
    (hs : PSDFoldedKrylov.action sigma s = s) (n : ℕ) (hn₀ : 0 < n)
    (hn : vector sigma s f n ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n)
    (z : ι → F) (hz : z ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n) :
    PSDFoldedKrylov.action sigma z ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      cases hk : k.val with
      | zero =>
          simp only [hk, vector, hs]
          exact DifferentialKrylov.prefix_mem _ hn₀
      | succ l =>
          simp only [hk, vector]
          rw [← PSDFoldedKrylov.vector_succ]
          by_cases hl : l+2 < n
          · exact DifferentialKrylov.prefix_mem _ hl
          · have heq : l+2 = n := by have := k.isLt; omega
            have hh : vector sigma s f (l+2) ∈
                DifferentialKrylov.krylovSpan (vector sigma s f) n := by simpa only [heq] using hn
            exact hh
  | zero => rw [PSDFoldedKrylov.action_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [PSDFoldedKrylov.action_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [PSDFoldedKrylov.action_smul]; exact Submodule.smul_mem _ _ hy

theorem exists_independent_stable_prefix (sigma : F →ₐ[ℝ] F) (s f : ι → F)
    (hs : PSDFoldedKrylov.action sigma s = s) (hsn : s ≠ 0) :
    ∃ n, 0 < n ∧ n ≤ Fintype.card ι ∧
      LinearIndependent F (fun j : Fin n => vector sigma s f j.val) ∧
      (∀ z ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n,
        PSDFoldedKrylov.action sigma z ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n) ∧
      (∀ k, vector sigma s f k ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n) := by
  classical
  have hex : ∃ n, vector sigma s f n ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n :=
    (DifferentialKrylov.exists_dependence (vector sigma s f)).imp fun _ h => h.2
  let n := Nat.find hex
  have hn : vector sigma s f n ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n :=
    Nat.find_spec hex
  have hsmall (k : ℕ) (hk : k < n) :
      vector sigma s f k ∉ DifferentialKrylov.krylovSpan (vector sigma s f) k :=
    Nat.find_min hex hk
  have hn₀ : 0 < n := by
    by_contra hz
    have hnzero : n = 0 := by omega
    have hn' : vector sigma s f 0 ∈ DifferentialKrylov.krylovSpan (vector sigma s f) 0 := by
      simpa only [hnzero] using hn
    have hspan : DifferentialKrylov.krylovSpan (vector sigma s f) 0 = ⊥ := by
      unfold DifferentialKrylov.krylovSpan
      have hempty : (Set.range (fun i : Fin 0 => vector sigma s f i.val)) = ∅ :=
        Set.range_eq_empty _
      rw [hempty, Submodule.span_empty]
    rw [hspan] at hn'
    have hsz : s = 0 := hn'
    exact hsn hsz
  have hli := DifferentialKrylov.independent_before_first_dependence (vector sigma s f) n hsmall
  have hbound : n ≤ Fintype.card ι := by
    obtain ⟨m, hm, hdep⟩ := DifferentialKrylov.exists_dependence (vector sigma s f)
    exact (Nat.find_min' hex hdep).trans hm
  have hInv := prefix_invariant sigma s f hs n hn₀ hn
  have hf : f ∈ DifferentialKrylov.krylovSpan (vector sigma s f) n := by
    by_cases hn1 : n = 1
    · simpa [hn1, vector, PSDFoldedKrylov.vector] using hn
    · have hq1 : vector sigma s f 1 = f := rfl
      rw [← hq1]
      exact DifferentialKrylov.prefix_mem _ (by omega)
  have hIter (k : ℕ) : PSDFoldedKrylov.vector sigma f k ∈
      DifferentialKrylov.krylovSpan (vector sigma s f) n := by
    induction k with
    | zero => exact hf
    | succ k ih => rw [PSDFoldedKrylov.vector_succ]; exact hInv _ ih
  refine ⟨n, hn₀, hbound, hli, hInv, ?_⟩
  intro k
  cases k with
  | zero => exact DifferentialKrylov.prefix_mem _ hn₀
  | succ k => exact hIter k

#print axioms exists_independent_stable_prefix

end
end ADComplete.PSDFoldedPrefix
