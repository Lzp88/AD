import PaperVerifier.ADComplete.UniformProbes

/-! A common external selector size may exceed either ambient dimension. -/

namespace ADComplete.Spanning

open Matrix
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem uniform_probe_spanning_of_card_le (κ : ℝ) (hκ : κ ≠ 0)
    (H K : Matrix ι ι ℝ) (hH : H.IsSymm) (v : ι → ℝ)
    (lo hi : ℝ)
    (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u ((κ⁻¹ • K).mulVec u) ∧
      Rigidity.pairing u ((κ⁻¹ • K).mulVec u) ≤ hi * Rigidity.pairing u u)
    (hgap : (Fintype.card ι : ℝ) * (hi - lo) < 1)
    (N : ℕ) (hN : Fintype.card ι ≤ N) :
    Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
      z = probeVector κ H K v k j} = jointModule H K v := by
  apply le_antisymm
  · exact triangular_span_le κ H K v N
  · rw [← uniform_probe_spanning κ hκ H K hH v lo hi hB hgap]
    apply Submodule.span_mono
    rintro z ⟨k, hk, j, hj, rfl⟩
    exact ⟨k, hk.trans_le hN, j, hj, rfl⟩

#print axioms uniform_probe_spanning_of_card_le

end
end ADComplete.Spanning
