import PaperVerifier.ADComplete.PSDResidualPrefix

/-! Independent prefix columns supply the precise hypotheses for residuals. -/
namespace ADComplete.PSDResidual

open Matrix
noncomputable section

variable {ι : Type*}

theorem outside_prefix_of_independent (z : ℕ → ι → ℝ) (r : ℕ)
    (h : LinearIndependent ℝ (fun j : Fin r => z j.val)) (k : ℕ) (hk : k < r) :
    z k ∉ PSDCyclic.prefixSpan k z := by
  let v : Fin (k+1) → ι → ℝ := fun j => z j.val
  have hv : LinearIndependent ℝ v := by
    exact h.comp (Fin.castLE (Nat.succ_le_of_lt hk))
      (Fin.castLE_injective (Nat.succ_le_of_lt hk))
  have hs : Set.range (Fin.init v) = {w | ∃ j < k, w = z j} := by
    ext w
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.isLt,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
  have hn := (linearIndependent_finSucc'.mp hv).2
  rw [hs] at hn
  exact hn

#print axioms outside_prefix_of_independent

end
end ADComplete.PSDResidual
