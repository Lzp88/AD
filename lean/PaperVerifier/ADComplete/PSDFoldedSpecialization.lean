import PaperVerifier.ADComplete.PSDFoldedInteger
import PaperVerifier.ADComplete.PSDCyclic

/-! Real independence, span, and prefix nonmembership from an actual evaluated minor. -/

namespace ADComplete.PSDFoldedFrame

open Matrix Polynomial Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*}

theorem folded_prefix_independent_of_minor_eval {m r : ℕ}
    (s : ι → ℤ) (u : Fin m → ι → ℤ) (rows : Fin r → ι) (t : ℕ)
    (h : (foldedMinor s u rows).det.eval (t : ℤ) ≠ 0) :
    LinearIndependent ℝ (fun j : Fin r => foldedVector s u t j.val) := by
  classical
  let A : Matrix ι (Fin r) ℝ := fun i j => foldedVector s u t j.val i
  let Q := A.submatrix rows id
  have hdet : Q.det ≠ 0 := by
    let f : ℤ[X] →+* ℝ := (Int.castRingHom ℝ).comp (Polynomial.evalRingHom (t : ℤ))
    have heq : Q.det = f (foldedMinor s u rows).det := by
      rw [RingHom.map_det]
      rfl
    rw [heq]
    change (((foldedMinor s u rows).det.eval (t : ℤ) : ℤ) : ℝ) ≠ 0
    exact_mod_cast h
  have hQi : Function.Injective Q.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Q.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  apply (Matrix.mulVec_injective_iff (M := A)).mp
  intro a b hab
  apply hQi
  have hh := congrArg (fun z : ι → ℝ => z ∘ rows) hab
  exact hh

theorem folded_prefix_span [Fintype ι] {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) (t : ℕ)
    (h : LinearIndependent ℝ (fun j : Fin (finrank ℝ (sourceModule s u)) =>
      foldedVector s u t j.val)) :
    PSDCyclic.prefixSpan (finrank ℝ (sourceModule s u)) (foldedVector s u t) =
      sourceModule s u := by
  classical
  let r := finrank ℝ (sourceModule s u)
  have heq : PSDCyclic.prefixSpan r (foldedVector s u t) =
      Submodule.span ℝ (Set.range (fun j : Fin r => foldedVector s u t j.val)) := by
    unfold PSDCyclic.prefixSpan
    congr 1
    ext v
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.isLt,rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro v ⟨j,_,rfl⟩
    exact foldedVector_mem_source s u t j
  · rw [heq]
    simpa only [Fintype.card_fin] using finrank_span_eq_card h

theorem folded_prefix_not_mem {m r : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) (t : ℕ)
    (h : LinearIndependent ℝ (fun j : Fin r => foldedVector s u t j.val)) :
    ∀ k < r, foldedVector s u t k ∉ PSDCyclic.prefixSpan k (foldedVector s u t) := by
  classical
  intro k hk hmem
  apply (linearIndependent_iff_notMem_span.mp h ⟨k,hk⟩)
  apply Submodule.span_mono (t :=
    (fun j : Fin r => foldedVector s u t j.val) '' (Set.univ \ {⟨k,hk⟩})) ?_ hmem
  rintro z ⟨j,hj,rfl⟩
  refine ⟨⟨j,hj.trans hk⟩, ?_, rfl⟩
  simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  intro heq
  have hv : j = k := congrArg (fun a : Fin r => a.val) heq
  exact (Nat.ne_of_lt hj) hv

#print axioms folded_prefix_independent_of_minor_eval
#print axioms folded_prefix_span
#print axioms folded_prefix_not_mem

end
end ADComplete.PSDFoldedFrame
