import PaperVerifier.ADComplete.PluckerConnection

/-! Nonzero Pluecker coordinates are constructed from an actual injective column map. -/

namespace ADComplete.PluckerConnection

open Matrix Module
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {F ι : Type*} [Field F] [Fintype ι] [LinearOrder ι]

theorem exists_nonzero_plucker (r : ℕ) (P : Matrix ι (Fin r) F)
    (hP : Function.Injective P.mulVec) :
    ∃ s : Fin r → ι, plucker P s ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := P.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hP)
  let v : Fin r → (ι → F) := P.col
  let f : Fin r → Module.Dual F (ι → F) := fun j => (LinearMap.proj j).comp g
  have hcol (i : Fin r) : g (P.col i) = Pi.single i 1 := by
    have h := LinearMap.congr_fun hg (Pi.single i 1)
    simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, LinearMap.id_apply] using h
  have hmat : (Matrix.of (fun i j : Fin r => f j (v i))) = (1 : Matrix (Fin r) (Fin r) F) := by
    ext i j
    change g (P.col i) j = (1 : Matrix (Fin r) (Fin r) F) i j
    rw [hcol]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  have hpair : exteriorPower.pairingDual F (ι → F) r
      (exteriorPower.ιMulti F r f) (exteriorPower.ιMulti F r v) = 1 := by
    rw [exteriorPower.pairingDual_ιMulti_ιMulti, hmat, Matrix.det_one]
  have hv : exteriorPower.ιMulti F r v ≠ 0 := by
    intro hv₀
    simp only [hv₀, map_zero] at hpair
    exact zero_ne_one hpair
  by_contra h
  push Not at h
  apply hv
  apply Module.Basis.ext_elem ((Pi.basisFun F ι).exteriorPower r)
  intro t
  rw [map_zero, Finsupp.zero_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, Pi.basisFun_repr]
  change ((P.submatrix (fun j => Set.powersetCard.ofFinEmbEquiv.symm t j) id).transpose).det = 0
  rw [Matrix.det_transpose]
  exact h (fun j => Set.powersetCard.ofFinEmbEquiv.symm t j)

#print axioms exists_nonzero_plucker

end
end ADComplete.PluckerConnection
