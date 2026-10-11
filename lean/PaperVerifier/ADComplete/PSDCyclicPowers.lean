import PaperVerifier.ADComplete.PSDCyclicAction

/-! Actual powers of the adjacent-sum square matrix generate its full image. -/
namespace ADComplete.PSDCyclic

open Matrix
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def powersSpan (C : Matrix ι ι ℝ) (v : ι → ℝ) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ (Set.range (fun k : ℕ => (C^k).mulVec v))

lemma power_mem (C : Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) :
    (C^k).mulVec v ∈ powersSpan C v := Submodule.subset_span ⟨k,rfl⟩

lemma powers_invariant (C : Matrix ι ι ℝ) (v x : ι → ℝ) (hx : x ∈ powersSpan C v) :
    C.mulVec x ∈ powersSpan C v := by
  have hh : powersSpan C v ≤ (powersSpan C v).comap C.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro z ⟨k,rfl⟩
    change C.mulVec ((C^k).mulVec v) ∈ powersSpan C v
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    exact power_mem C v (k+1)
  exact hh hx

/-- Orthogonality and a nonzero prefix are properties of the supplied
residuals. The actual square matrix and its cyclicity are computed here;
neither a tridiagonal formula nor a cyclicity conclusion is assumed. -/
theorem powers_span_square (N r : ℕ) (hN : 1 ≤ N) (hr : r ≤ N)
    (u : ℕ → ι → ℝ)
    (horth : ∀ i j : ℕ, i ≠ j → dotProduct (u i) (u j) = 0)
    (hnz : ∀ k < r, u k ≠ 0) (htail : ∀ k, r ≤ k → u k = 0) :
    powersSpan (squareMatrix N u) (u 0) = prefixSpan N u := by
  let C := squareMatrix N u
  let S := powersSpan C (u 0)
  have hu (k : ℕ) (hk : k < r) : u k ∈ S := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simpa [S, C] using power_mem C (u 0) 0
      | succ k =>
        have hprev : u k ∈ S := ih k (by omega) (by omega)
        have hp : prefixSpan (k+1) u ≤ S := by
          apply Submodule.span_le.mpr
          rintro z ⟨j,hj,rfl⟩
          exact ih j (by omega) (by omega)
        have hd : C.mulVec (u k) - dotProduct (u k) (u k) • u (k+1) ∈ S :=
          hp (square_next_mod_prefix N u horth k (by omega))
        have hm : dotProduct (u k) (u k) • u (k+1) ∈ S := by
          have hs := S.sub_mem (powers_invariant C (u 0) (u k) hprev) hd
          simpa only [sub_sub_cancel] using hs
        have hc : dotProduct (u k) (u k) ≠ 0 := by
          intro hz
          exact hnz k (by omega) (dotProduct_self_eq_zero.mp hz)
        have hs := S.smul_mem (dotProduct (u k) (u k))⁻¹ hm
        simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨k,rfl⟩
    cases k with
    | zero => simpa using prefix_mem u (show 0 < N by omega)
    | succ k =>
      have hh : (C^(k+1)).mulVec (u 0) ∈ LinearMap.range C.mulVecLin := by
        refine ⟨(C^k).mulVec (u 0), ?_⟩
        change C.mulVec ((C^k).mulVec (u 0)) = (C^(k+1)).mulVec (u 0)
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      exact (square_range N u) ▸ hh
  · apply Submodule.span_le.mpr
    rintro z ⟨k,_,rfl⟩
    by_cases hk : k < r
    · exact hu k hk
    · rw [htail k (by omega)]
      exact Submodule.zero_mem _

lemma derivative_zero_vector (C : Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) :
    DifferentialKrylov.vector (0 : Derivation ℝ ℝ ℝ) C v k = (C^k).mulVec v := by
  induction k with
  | zero => simp [DifferentialKrylov.vector]
  | succ k ih =>
    rw [DifferentialKrylov.vector_succ, ih, pow_succ', ← Matrix.mulVec_mulVec]
    ext i
    simp only [DifferentialKrylov.connection, Derivation.zero_apply, zero_add]

theorem finite_powers_span (C : Matrix ι ι ℝ) (v : ι → ℝ) (N : ℕ)
    (hcard : Fintype.card ι ≤ N) :
    Submodule.span ℝ (Set.range (fun k : Fin N => (C^k.val).mulVec v)) = powersSpan C v := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro z ⟨k,rfl⟩
    exact ⟨k.val,rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨k,rfl⟩
    have hh := DifferentialKrylov.ambient_prefix_spans (0 : Derivation ℝ ℝ ℝ) C v k
    have hm := DifferentialKrylov.prefix_mono
      (DifferentialKrylov.vector (0 : Derivation ℝ ℝ ℝ) C v) hcard hh
    change (C^k).mulVec v ∈ Submodule.span ℝ (Set.range (fun j : Fin N => (C^j.val).mulVec v))
    simpa only [DifferentialKrylov.krylovSpan, derivative_zero_vector] using hm

theorem finite_cyclic_square (N r : ℕ) (hN : 1 ≤ N)
    (hcard : Fintype.card ι ≤ N) (hr : r ≤ N) (u : ℕ → ι → ℝ)
    (horth : ∀ i j : ℕ, i ≠ j → dotProduct (u i) (u j) = 0)
    (hnz : ∀ k < r, u k ≠ 0) (htail : ∀ k, r ≤ k → u k = 0) :
    Submodule.span ℝ (Set.range (fun k : Fin N =>
      ((squareMatrix N u)^k.val).mulVec (u 0))) = prefixSpan N u := by
  rw [finite_powers_span _ _ N hcard, powers_span_square N r hN hr u horth hnz htail]

#print axioms powers_span_square
#print axioms finite_cyclic_square

end
end ADComplete.PSDCyclic
