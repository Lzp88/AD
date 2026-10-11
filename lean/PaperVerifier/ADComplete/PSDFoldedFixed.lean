import PaperVerifier.ADComplete.PSDFoldedSpecialization
import PaperVerifier.ADComplete.PSDFoldedBound

/-! The prescribed integer specialization, with its actual rank-sensitive prefix. -/

namespace ADComplete.PSDFoldedFrame

open Matrix Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- Every rank and span assertion is derived from the source coordinates.
The integer specialization is the prescribed function of N, m, and R. -/
theorem fixed_folded_prefix (N m R : ℕ) (s : ι → ℤ) (u : Fin m → ι → ℤ)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (hR : 1 ≤ R) (hcard : Fintype.card ι ≤ N)
    (hs0 : castVector s ≠ 0)
    (hs : ∀ i, ‖s i‖ ≤ (1 : ℝ)) (hu : ∀ a i, ‖u a i‖ ≤ (R : ℝ)) :
    let r := finrank ℝ (sourceModule s u)
    let z := foldedVector s u (tau N m R)
    0 < r ∧ r ≤ N ∧ LinearIndependent ℝ (fun j : Fin r => z j.val) ∧
      PSDCyclic.prefixSpan r z = sourceModule s u ∧
      (∀ k < r, z k ∉ PSDCyclic.prefixSpan k z) := by
  classical
  let r := finrank ℝ (sourceModule s u)
  obtain ⟨hr0, rows, hp⟩ := folded_prefix_nonzero_minor s u hs0
  have hr : r ≤ N := by
    have hh := (sourceModule s u).finrank_le
    simp only [Module.finrank_pi] at hh
    exact hh.trans hcard
  have heval := folded_minor_tau_ne_zero N m R s u rows hr0 hr hN hm hR hs hu hp
  have hli := folded_prefix_independent_of_minor_eval s u rows (tau N m R) heval
  exact ⟨hr0, hr, hli, folded_prefix_span s u _ hli,
    folded_prefix_not_mem s u _ hli⟩

#print axioms fixed_folded_prefix

end
end ADComplete.PSDFoldedFrame
