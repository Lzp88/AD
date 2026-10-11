import PaperVerifier.ADComplete.PSDFoldedFixed
import PaperVerifier.ADComplete.PSDRepresentative

/-! Fixed integer folded coordinates to the exact rescaled PSD representative. -/

namespace ADComplete.PSDFoldedFrame

open Matrix Module
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def foldedPrincipalMatrix (N m R : ℕ) (s : ι → ℤ) (u : Fin m → ι → ℤ)
    (n : ℝ) : Matrix ι ι ℝ :=
  n • PSDCyclic.squareMatrix N (fun k => n^(k-1) •
    PSDResidual.residualSequence (foldedVector s u (tau N m R)) k)

/-- No rank, successful parameter, residual nonvanishing, image, or cyclicity
assumption occurs: they follow from the actual bounded integer coordinates. -/
theorem fixed_folded_principal_matrix (N m R : ℕ) (s : ι → ℤ)
    (u : Fin m → ι → ℤ) (n : ℝ)
    (hN : 2 ≤ N) (hm : 1 ≤ m) (hR : 1 ≤ R) (hcard : Fintype.card ι ≤ N)
    (hs0 : castVector s ≠ 0) (hs : ∀ i, ‖s i‖ ≤ (1 : ℝ))
    (hu : ∀ a i, ‖u a i‖ ≤ (R : ℝ)) (hn : 0 < n) :
    let C := foldedPrincipalMatrix N m R s u n
    C.PosSemidef ∧ LinearMap.range C.mulVecLin = sourceModule s u ∧
      Submodule.span ℝ (Set.range (fun k : Fin N =>
        (C^k.val).mulVec (castVector s))) = sourceModule s u := by
  classical
  let r := finrank ℝ (sourceModule s u)
  let z := foldedVector s u (tau N m R)
  obtain ⟨_, hr, hind, heq, _⟩ := fixed_folded_prefix N m R s u hN hm hR hcard hs0 hs hu
  have hspan (k : ℕ) : z k ∈ PSDCyclic.prefixSpan r z := by
    rw [heq]
    exact foldedVector_mem_source s u _ k
  have hh := PSDCyclic.residual_principal_matrix N r (by omega) hcard hr z hind hspan n hn
  dsimp only at hh ⊢
  change (foldedPrincipalMatrix N m R s u n).PosSemidef ∧ _ ∧ _
  rw [heq] at hh
  simpa only [foldedPrincipalMatrix, z, foldedVector_zero] using hh

#print axioms fixed_folded_principal_matrix

end
end ADComplete.PSDFoldedFrame
