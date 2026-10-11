import PaperVerifier.ADComplete.PSDRescaling

/-! Image, positive semidefiniteness, and cyclicity with every dimension factor. -/
namespace ADComplete.PSDCyclic

open Matrix
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem residual_full_span (N r : ℕ) (hr : r ≤ N) (z : ℕ → ι → ℝ)
    (hprefix : ∀ k < r, z k ∉ prefixSpan k z)
    (hspan : ∀ k, z k ∈ prefixSpan r z) :
    prefixSpan N (PSDResidual.residualSequence z) = prefixSpan r z := by
  let u := PSDResidual.residualSequence z
  have heq : prefixSpan N u = prefixSpan r u := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨k,_,rfl⟩
      by_cases hk : k < r
      · exact prefix_mem u hk
      · rw [show u k = 0 from PSDResidual.residualSequence_tail_zero z r hspan k (by omega)]
        exact Submodule.zero_mem _
    · exact PSDResidual.prefix_mono u hr
  exact heq.trans (PSDResidual.residualSequence_prefix_span z r r le_rfl hprefix)

omit [DecidableEq ι] in
theorem scaled_residual_image (N r : ℕ) (hr : r ≤ N) (z : ℕ → ι → ℝ)
    (hprefix : ∀ k < r, z k ∉ prefixSpan k z)
    (hspan : ∀ k, z k ∈ prefixSpan r z) (n : ℝ) (hn : n ≠ 0) :
    let u := PSDResidual.residualSequence z
    let t := fun k => n^(k-1) • u k
    LinearMap.range (n • squareMatrix N t).mulVecLin = prefixSpan r z := by
  dsimp only
  rw [scalar_matrix_range n hn, square_range,
    prefix_span_rescale N (PSDResidual.residualSequence z) (fun k => n^(k-1))
      (fun _ => pow_ne_zero _ hn)]
  exact residual_full_span N r hr z hprefix hspan

/-- This is the exact real matrix computed after the homogeneous integer
determinant lift. The frame hypotheses are separate from the matrix
conclusions; the final tree theorem discharges them by the fixed condenser. -/
theorem residual_principal_matrix (N r : ℕ) (hN : 1 ≤ N)
    (hcard : Fintype.card ι ≤ N) (hr : r ≤ N) (z : ℕ → ι → ℝ)
    (hind : LinearIndependent ℝ (fun k : Fin r => z k.val))
    (hspan : ∀ k, z k ∈ prefixSpan r z) (n : ℝ) (hn : 0 < n) :
    let u := PSDResidual.residualSequence z
    let t := fun k => n^(k-1) • u k
    let C := n • squareMatrix N t
    C.PosSemidef ∧ LinearMap.range C.mulVecLin = prefixSpan r z ∧
      Submodule.span ℝ (Set.range (fun k : Fin N => (C^k.val).mulVec (z 0))) =
        prefixSpan r z := by
  dsimp only
  have hprefix (k : ℕ) (hk : k < r) : z k ∉ prefixSpan k z :=
    PSDResidual.outside_prefix_of_independent z r hind k hk
  refine ⟨?_, scaled_residual_image N r hr z hprefix hspan n (ne_of_gt hn),
    scaled_residual_cyclic N r hN hcard hr z hprefix hspan n (ne_of_gt hn)⟩
  exact (square_posSemidef N (fun k => n^(k-1) • PSDResidual.residualSequence z k)).smul hn.le

#print axioms residual_full_span
#print axioms scaled_residual_image
#print axioms residual_principal_matrix

end
end ADComplete.PSDCyclic
