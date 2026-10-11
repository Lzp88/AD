import PaperVerifier.ADComplete.PSDResidual
import PaperVerifier.ADComplete.PSDCyclicAction

/-! Every rank case of the actual fraction-free residual sequence. -/
namespace ADComplete.PSDResidual

open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

def prefixColumns (z : ℕ → ι → ℝ) (k : ℕ) : Matrix ι (Fin k) ℝ :=
  fun i j => z j.val i

def residualSequence (z : ℕ → ι → ℝ) (k : ℕ) : ι → ℝ :=
  residual (prefixColumns z k) (z k)

omit [Fintype ι] in
lemma prefix_range (z : ℕ → ι → ℝ) (k : ℕ) :
    LinearMap.range (prefixColumns z k).mulVecLin = PSDCyclic.prefixSpan k z := by
  classical
  rw [Matrix.range_mulVecLin]
  congr 1
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨j.val,j.isLt,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨⟨j,hj⟩,rfl⟩

omit [Fintype ι] in
lemma prefix_mono (z : ℕ → ι → ℝ) {m n : ℕ} (h : m ≤ n) :
    PSDCyclic.prefixSpan m z ≤ PSDCyclic.prefixSpan n z := by
  apply Submodule.span_mono
  rintro v ⟨j,hj,rfl⟩
  exact ⟨j,hj.trans_le h,rfl⟩

theorem residualSequence_zero (z : ℕ → ι → ℝ) : residualSequence z 0 = z 0 := by
  ext i
  simp [residualSequence, residual, gram]

theorem residualSequence_mem_prefix (z : ℕ → ι → ℝ) (k : ℕ) :
    residualSequence z k ∈ PSDCyclic.prefixSpan (k+1) z := by
  apply residual_in_span _ _ _
  · rw [prefix_range]
    exact prefix_mono z (by omega)
  · exact PSDCyclic.prefix_mem z (by omega)

theorem residualSequence_orthogonal (z : ℕ → ι → ℝ) (i j : ℕ) (hij : i ≠ j) :
    dotProduct (residualSequence z i) (residualSequence z j) = 0 := by
  have hlt (a b : ℕ) (h : a < b) :
      dotProduct (residualSequence z a) (residualSequence z b) = 0 := by
    apply residual_pairing
    rw [prefix_range]
    exact prefix_mono z (by omega) (residualSequence_mem_prefix z a)
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · rw [dotProduct_comm]
    exact hlt j i h

theorem residualSequence_tail_zero (z : ℕ → ι → ℝ) (r : ℕ)
    (hspan : ∀ k, z k ∈ PSDCyclic.prefixSpan r z) (k : ℕ) (hk : r ≤ k) :
    residualSequence z k = 0 := by
  apply residual_zero_of_mem_range
  rw [prefix_range]
  exact prefix_mono z hk (hspan k)

omit [Fintype ι] in
theorem prefixColumns_injective (z : ℕ → ι → ℝ) (k : ℕ)
    (h : ∀ j < k, z j ∉ PSDCyclic.prefixSpan j z) :
    Function.Injective (prefixColumns z k).mulVec := by
  apply Matrix.mulVec_injective_iff.mpr
  apply DifferentialKrylov.independent_before_first_dependence
  intro j hj
  have heq : DifferentialKrylov.krylovSpan z j = PSDCyclic.prefixSpan j z := by
    unfold PSDCyclic.prefixSpan DifferentialKrylov.krylovSpan
    congr 1
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a.val,a.isLt,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  rw [heq]
  exact h j hj

theorem residualSequence_nonzero (z : ℕ → ι → ℝ) (r : ℕ)
    (h : ∀ j < r, z j ∉ PSDCyclic.prefixSpan j z) (k : ℕ) (hk : k < r) :
    residualSequence z k ≠ 0 := by
  apply residual_nonzero
  · exact prefixColumns_injective z k (fun j hj => h j (hj.trans hk))
  · rw [prefix_range]
    exact h k hk

theorem residualSequence_prefix_span (z : ℕ → ι → ℝ) (r n : ℕ) (hn : n ≤ r)
    (h : ∀ j < r, z j ∉ PSDCyclic.prefixSpan j z) :
    PSDCyclic.prefixSpan n (residualSequence z) = PSDCyclic.prefixSpan n z := by
  have hz (j : ℕ) (hj : j < n) : z j ∈ PSDCyclic.prefixSpan n (residualSequence z) := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      let S := PSDCyclic.prefixSpan n (residualSequence z)
      have hp : LinearMap.range (prefixColumns z j).mulVecLin ≤ S := by
        rw [prefix_range]
        apply Submodule.span_le.mpr
        rintro v ⟨k,hk,rfl⟩
        exact ih k hk (hk.trans hj)
      have hu : residualSequence z j ∈ S := PSDCyclic.prefix_mem _ hj
      have ht : (prefixColumns z j).mulVec
          ((gram (prefixColumns z j)).adjugate.mulVec ((prefixColumns z j).transpose.mulVec (z j)))
          ∈ S := hp ⟨_,rfl⟩
      have hs := S.add_mem hu ht
      change residual (prefixColumns z j) (z j) + _ ∈ S at hs
      rw [residual, sub_add_cancel] at hs
      have hd := gram_det_nonzero (prefixColumns z j)
        (prefixColumns_injective z j (fun k hk => h k (hk.trans_le (hj.le.trans hn))))
      have hm := S.smul_mem (gram (prefixColumns z j)).det⁻¹ hs
      simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using hm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨j,hj,rfl⟩
    exact prefix_mono z (by omega) (residualSequence_mem_prefix z j)
  · apply Submodule.span_le.mpr
    rintro v ⟨j,hj,rfl⟩
    exact hz j hj

#print axioms residualSequence_orthogonal
#print axioms residualSequence_tail_zero
#print axioms residualSequence_nonzero
#print axioms residualSequence_prefix_span

end
end ADComplete.PSDResidual
