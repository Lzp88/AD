import PaperVerifier.ADComplete.PSDFoldedFrame
import PaperVerifier.ADComplete.PSDFoldedRank

/-! Integer coordinates and a genuine nonzero minor for the folded prefix. -/

namespace ADComplete.PSDFoldedFrame

open Matrix Polynomial Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*}

def realPolynomial (p : ℤ[X]) : ℝ[X] := p.map (Int.castRingHom ℝ)

lemma foldedEntry_coeff {m : ℕ} (a : Fin m → ℤ) (j : ℕ) (b : Fin m) :
    (PSDSpecialization.foldedEntry m a j).coeff b.val = 2^(j*b.val)*a b := by
  classical
  unfold PSDSpecialization.foldedEntry
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    have hv : c.val ≠ b.val := fun h => hc (Fin.ext h)
    simp [Polynomial.coeff_monomial, hv]
  · simp

lemma foldedEntry_coeff_outside {m : ℕ} (a : Fin m → ℤ) (j k : ℕ) (hk : m ≤ k) :
    (PSDSpecialization.foldedEntry m a j).coeff k = 0 := by
  classical
  simp only [PSDSpecialization.foldedEntry, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro c _
  have hv : c.val ≠ k := by omega
  simp [Polynomial.coeff_monomial, hv]

lemma foldedEntry_scale {m : ℕ} (a : Fin m → ℤ) (j : ℕ) :
    PSDFoldedScaling.polynomialScale (realPolynomial (PSDSpecialization.foldedEntry m a j)) =
      realPolynomial (PSDSpecialization.foldedEntry m a (j+1)) := by
  ext k
  rw [PSDFoldedScaling.polynomialScale_coeff]
  by_cases hk : k < m
  · let b : Fin m := ⟨k, hk⟩
    have hk' : k = b.val := rfl
    rw [hk', realPolynomial, realPolynomial, Polynomial.coeff_map, Polynomial.coeff_map,
      foldedEntry_coeff, foldedEntry_coeff]
    rw [Nat.add_mul, pow_add]
    simp only [map_mul, map_pow]
    norm_num
    ring
  · rw [realPolynomial, realPolynomial, Polynomial.coeff_map, Polynomial.coeff_map,
      foldedEntry_coeff_outside _ _ _ (Nat.le_of_not_gt hk),
      foldedEntry_coeff_outside _ _ _ (Nat.le_of_not_gt hk)]
    simp

theorem foldedPolynomial_real {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) (k : ℕ) :
    (fun i => realPolynomial (foldedPolynomial s u k i)) =
      PSDFoldedRank.polynomialVector (castVector s)
        (fun i => realPolynomial (PSDSpecialization.foldedEntry m (fun a => u a i) 0)) k := by
  cases k with
  | zero => ext i; simp [foldedPolynomial, PSDFoldedRank.polynomialVector, realPolynomial, castVector]
  | succ j =>
      induction j with
      | zero => rfl
      | succ j ih =>
          funext i
          change realPolynomial (PSDSpecialization.foldedEntry m (fun a => u a i) (j+1)) = _
          rw [← foldedEntry_scale]
          have hi := congrFun ih i
          change realPolynomial (PSDSpecialization.foldedEntry m (fun a => u a i) j) = _ at hi
          rw [hi]
          change _ = PSDFoldedScaling.polynomialScale^[j+1]
            (realPolynomial (PSDSpecialization.foldedEntry m (fun a => u a i) 0))
          rw [Function.iterate_succ_apply']
          rfl

theorem real_sourceModule {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) :
    PSDFoldedRank.sourceModule (castVector s)
      (fun i => realPolynomial (PSDSpecialization.foldedEntry m (fun a => u a i) 0)) =
      sourceModule s u := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_insert_iff.mp hv with h | h
    · subst v; exact Submodule.subset_span (Set.mem_insert _ _)
    · obtain ⟨k, rfl⟩ := h
      by_cases hk : k < m
      · let b : Fin m := ⟨k, hk⟩
        have heq : (fun i => (realPolynomial
            (PSDSpecialization.foldedEntry m (fun a => u a i) 0)).coeff k) = castVector (u b) := by
          ext i
          change _ = (u b i : ℝ)
          rw [realPolynomial, Polynomial.coeff_map]
          change (((PSDSpecialization.foldedEntry m (fun a => u a i) 0).coeff b.val : ℤ) : ℝ) = _
          rw [foldedEntry_coeff]
          simp
        change (fun i => (realPolynomial
          (PSDSpecialization.foldedEntry m (fun a => u a i) 0)).coeff k) ∈ sourceModule s u
        rw [heq]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨b, rfl⟩)
      · have heq : (fun i => (realPolynomial
            (PSDSpecialization.foldedEntry m (fun a => u a i) 0)).coeff k) = 0 := by
          ext i
          rw [realPolynomial, Polynomial.coeff_map,
            foldedEntry_coeff_outside _ _ _ (Nat.le_of_not_gt hk)]
          simp
        change (fun i => (realPolynomial
          (PSDSpecialization.foldedEntry m (fun a => u a i) 0)).coeff k) ∈ sourceModule s u
        rw [heq]; exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_insert_iff.mp hv with h | h
    · subst v; exact Submodule.subset_span (Set.mem_insert _ _)
    · obtain ⟨b, rfl⟩ := h
      have heq : castVector (u b) = fun i => (realPolynomial
          (PSDSpecialization.foldedEntry m (fun a => u a i) 0)).coeff b.val := by
        ext i
        rw [realPolynomial, Polynomial.coeff_map, foldedEntry_coeff]
        simp [castVector]
      change castVector (u b) ∈ _
      rw [heq]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨b.val, rfl⟩)

def polynomialToRational : ℤ[X] →+* F :=
  (algebraMap ℝ[X] F).comp (Polynomial.mapRingHom (Int.castRingHom ℝ))

variable [Fintype ι]

theorem folded_prefix_nonzero_minor {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ)
    (hs : castVector s ≠ 0) :
    let r := finrank ℝ (sourceModule s u)
    0 < r ∧ ∃ rows : Fin r → ι,
      (foldedMinor s u rows).det ≠ 0 := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let r := finrank ℝ (sourceModule s u)
  obtain ⟨hr, hi⟩ := PSDFoldedRank.independent_rank_prefix (castVector s)
    (fun i => realPolynomial (PSDSpecialization.foldedEntry m (fun a => u a i) 0)) hs
  rw [real_sourceModule] at hr hi
  have hp : LinearIndependent F (fun j : Fin r =>
      fun i => polynomialToRational (foldedPolynomial s u j.val i)) := by
    have heq : (fun j : Fin r => fun i => polynomialToRational (foldedPolynomial s u j.val i)) =
        (fun j : Fin r => fun i => algebraMap ℝ[X] F
          (PSDFoldedRank.polynomialVector (castVector s)
            (fun i => realPolynomial (PSDSpecialization.foldedEntry m (fun a => u a i) 0)) j.val i)) := by
      ext j i
      exact congrArg (algebraMap ℝ[X] F) (congrFun (foldedPolynomial_real s u j.val) i)
    rw [heq]
    exact hi
  let P : Matrix ι (Fin r) F := fun i j => polynomialToRational (foldedPolynomial s u j.val i)
  obtain ⟨rows, hrows⟩ := PluckerConnection.exists_nonzero_plucker r P
    (Matrix.mulVec_injective_iff.mpr hp)
  refine ⟨hr, rows, ?_⟩
  intro hz
  apply hrows
  change Matrix.det (fun i j : Fin r => polynomialToRational (foldedPolynomial s u j.val (rows i))) = 0
  have hh := congrArg polynomialToRational hz
  rw [map_zero, RingHom.map_det] at hh
  exact hh

#print axioms folded_prefix_nonzero_minor

end
end ADComplete.PSDFoldedFrame
