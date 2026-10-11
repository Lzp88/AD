import PaperVerifier.ADComplete.PSDCyclicPowers
import PaperVerifier.ADComplete.PSDResidualIndependence

/-! The actual powers and images under the compiler's dimension factors. -/
namespace ADComplete.PSDCyclic

open Matrix
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalar_matrix_power (a : ℝ) (C : Matrix ι ι ℝ) (k : ℕ) :
    (a • C)^k = a^k • C^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ', ← pow_succ']

omit [DecidableEq ι] in
theorem scalar_matrix_range (a : ℝ) (ha : a ≠ 0) (C : Matrix ι ι ℝ) :
    LinearMap.range (a • C).mulVecLin = LinearMap.range C.mulVecLin := by
  apply le_antisymm
  · rintro v ⟨x,rfl⟩
    refine ⟨a • x, ?_⟩
    change C.mulVec (a • x) = (a • C).mulVec x
    rw [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · rintro v ⟨x,rfl⟩
    refine ⟨a⁻¹ • x, ?_⟩
    change (a • C).mulVec (a⁻¹ • x) = C.mulVec x
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem span_range_rescale {J : Type*} (v : J → ι → ℝ) (c : J → ℝ)
    (hc : ∀ j, c j ≠ 0) :
    Submodule.span ℝ (Set.range (fun j => c j • v j)) =
      Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨j,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro z ⟨j,rfl⟩
    have h := (Submodule.span ℝ (Set.range (fun j => c j • v j))).smul_mem
      (c j)⁻¹ (Submodule.subset_span ⟨j,rfl⟩)
    change v j ∈ Submodule.span ℝ (Set.range (fun j => c j • v j))
    simpa only [smul_smul, inv_mul_cancel₀ (hc j), one_smul] using h

theorem scalar_finite_powers_span (a : ℝ) (ha : a ≠ 0) (C : Matrix ι ι ℝ)
    (v : ι → ℝ) (N : ℕ) :
    Submodule.span ℝ (Set.range (fun k : Fin N => ((a • C)^k.val).mulVec v)) =
      Submodule.span ℝ (Set.range (fun k : Fin N => (C^k.val).mulVec v)) := by
  simp_rw [scalar_matrix_power, Matrix.smul_mulVec]
  exact span_range_rescale _ _ (fun k => pow_ne_zero k.val ha)

omit [Fintype ι] [DecidableEq ι] in
theorem prefix_span_rescale (N : ℕ) (u : ℕ → ι → ℝ) (c : ℕ → ℝ)
    (hc : ∀ k, c k ≠ 0) :
    prefixSpan N (fun k => c k • u k) = prefixSpan N u := by
  have he (v : ℕ → ι → ℝ) : prefixSpan N v =
      Submodule.span ℝ (Set.range (fun j : Fin N => v j.val)) := by
    unfold prefixSpan
    congr 1
    ext z
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,hj⟩,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,j.isLt,rfl⟩
  rw [he, he]
  exact span_range_rescale _ _ (fun j => hc j.val)

omit [DecidableEq ι] in
theorem rescaled_orthogonal (u : ℕ → ι → ℝ) (c : ℕ → ℝ)
    (horth : ∀ i j : ℕ, i ≠ j → dotProduct (u i) (u j) = 0) :
    ∀ i j : ℕ, i ≠ j → dotProduct (c i • u i) (c j • u j) = 0 := by
  intro i j hij
  rw [smul_dotProduct, dotProduct_smul, horth i j hij]
  simp

theorem scaled_residual_cyclic (N r : ℕ) (hN : 1 ≤ N)
    (hcard : Fintype.card ι ≤ N) (hr : r ≤ N)
    (z : ℕ → ι → ℝ) (hprefix : ∀ k < r, z k ∉ prefixSpan k z)
    (hspan : ∀ k, z k ∈ prefixSpan r z) (n : ℝ) (hn : n ≠ 0) :
    let u := PSDResidual.residualSequence z
    let t := fun k => n^(k-1) • u k
    Submodule.span ℝ (Set.range (fun k : Fin N =>
      ((n • squareMatrix N t)^k.val).mulVec (z 0))) = prefixSpan r z := by
  dsimp only
  let u := PSDResidual.residualSequence z
  let c : ℕ → ℝ := fun k => n^(k-1)
  let t := fun k => c k • u k
  have hc (k : ℕ) : c k ≠ 0 := pow_ne_zero _ hn
  have ht0 : t 0 = z 0 := by simp [t,c,u,PSDResidual.residualSequence_zero]
  have htnz (k : ℕ) (hk : k < r) : t k ≠ 0 := by
    exact smul_ne_zero (hc k) (PSDResidual.residualSequence_nonzero z r hprefix k hk)
  have httail (k : ℕ) (hk : r ≤ k) : t k = 0 := by
    simp [t,u,PSDResidual.residualSequence_tail_zero z r hspan k hk]
  change Submodule.span ℝ (Set.range (fun k : Fin N =>
    ((n • squareMatrix N t)^k.val).mulVec (z 0))) = prefixSpan r z
  rw [scalar_finite_powers_span n hn, ← ht0,
    finite_cyclic_square N r hN hcard hr t
      (rescaled_orthogonal u c (PSDResidual.residualSequence_orthogonal z)) htnz httail,
    prefix_span_rescale N u c hc]
  have heq : prefixSpan N u = prefixSpan r u := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨k,_,rfl⟩
      by_cases hk : k < r
      · exact prefix_mem u hk
      · rw [show u k = 0 from PSDResidual.residualSequence_tail_zero z r hspan k (by omega)]
        exact Submodule.zero_mem _
    · exact PSDResidual.prefix_mono u hr
  rw [heq]
  exact PSDResidual.residualSequence_prefix_span z r r le_rfl hprefix

#print axioms scalar_matrix_range
#print axioms scalar_finite_powers_span
#print axioms scaled_residual_cyclic

end
end ADComplete.PSDCyclic
