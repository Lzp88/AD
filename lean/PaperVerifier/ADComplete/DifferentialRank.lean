import PaperVerifier.ADComplete.DifferentialKrylov

/-! The actual first dependence and rank of a differential Krylov sequence. -/

namespace ADComplete.DifferentialKrylov

open Matrix
noncomputable section
variable {F ι : Type*} [Field F] [Algebra ℝ F] [Fintype ι]

theorem exists_independent_stable_prefix (D : Derivation ℝ F F)
    (A : Matrix ι ι F) (v : ι → F) :
    ∃ n ≤ Fintype.card ι,
      LinearIndependent F (fun j : Fin n => vector D A v j.val) ∧
      (∀ z ∈ krylovSpan (vector D A v) n,
        connection D A z ∈ krylovSpan (vector D A v) n) ∧
      (∀ k, vector D A v k ∈ krylovSpan (vector D A v) n) := by
  classical
  have hex : ∃ n, vector D A v n ∈ krylovSpan (vector D A v) n := by
    obtain ⟨n, _, hn⟩ := exists_dependence (vector D A v)
    exact ⟨n, hn⟩
  let n := Nat.find hex
  have hdep : vector D A v n ∈ krylovSpan (vector D A v) n := Nat.find_spec hex
  have hn : n ≤ Fintype.card ι := by
    obtain ⟨m, hm, hmem⟩ := exists_dependence (vector D A v)
    exact (Nat.find_min' hex hmem).trans hm
  refine ⟨n, hn, independent_before_first_dependence _ n ?_, ?_, ?_⟩
  · intro k hk
    exact Nat.find_min hex hk
  · exact prefix_invariant D A v n hdep
  · exact later_vectors_mem D A v n hdep

#print axioms exists_independent_stable_prefix

end
end ADComplete.DifferentialKrylov
