import PaperVerifier.ADComplete.RealPolynomialDegreeLowerBound

/-! The member-wise real polynomial degree statement, including N=1. -/
namespace ADComplete.ProbeDegreeLowerBound
noncomputable section

theorem exists_probe_of_degree_at_least {N : ℕ} (hN : 1≤N) {ι : Type*}
    (ps : ι → RealNCPolynomial)
    (hspan : Submodule.span ℝ (Set.range (fun i =>
      realPolynomialVector (fun j : Fin N => (j.val : ℝ)) (ps i))) =
        Spanning.jointModule (Matrix.diagonal (fun j : Fin N => (j.val : ℝ))) 0 (fun _ => 1)) :
    ∃ i, N-1 ≤ realFormalDegree (ps i) := by
  classical
  have hseed : (fun _ : Fin N => (1 : ℝ)) ∈
      Spanning.jointModule (Matrix.diagonal (fun j : Fin N => (j.val : ℝ))) 0 (fun _ => 1) :=
    Spanning.wordVector_mem _ _ _ []
  have hne : Set.range (fun i => realPolynomialVector (fun j : Fin N => (j.val : ℝ)) (ps i)) ≠ ∅ := by
    intro he
    rw [← hspan,he,Submodule.span_empty] at hseed
    have hz : (fun _ : Fin N => (1 : ℝ))=0 := hseed
    have hh := congrFun hz ⟨0,by omega⟩
    norm_num at hh
  obtain ⟨_,i,_⟩ := Set.nonempty_iff_ne_empty.mpr hne
  by_cases h1 : N=1
  · exact ⟨i,by omega⟩
  · by_contra h
    push Not at h
    have hlow : ∀ j, realFormalDegree (ps j) ≤ N-2 := by intro j; have := h j; omega
    have hd := explicit_real_diagonal_degree_lower_bound ps (N-2) hlow hspan
    omega

#print axioms exists_probe_of_degree_at_least
end
end ADComplete.ProbeDegreeLowerBound
