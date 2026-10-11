import PaperVerifier.ADComplete.Spanning
import PaperVerifier.CircuitAudit.Degrees

/-!
# The exact degree obstruction for a uniform polynomial frame

For H diagonal with N distinct real entries, K=0 and the all-ones seed,
the joint cyclic module has dimension N. All evaluated expressions of
formal degree at most d lie in an explicitly defined d+1 dimensional image.
Thus a spanning polynomial frame must have maximum degree at least N-1.
-/

namespace ADComplete.ProbeDegreeLowerBound
noncomputable section
open scoped BigOperators
open Matrix CircuitAudit.Degrees

theorem expr_map_eval {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (p : Expr) (H K : R) :
    f (p.eval H K) = p.eval (f H) (f K) := by
  induction p <;> simp only [Expr.eval, map_zero, map_one, map_zsmul, map_add, map_mul, *]

def univariate (p : Expr) : Polynomial ℝ := p.eval Polynomial.X 0

theorem univariate_natDegree_le (p : Expr) : (univariate p).natDegree ≤ p.degree := by
  induction p with
  | zero => simp [univariate, Expr.eval, Expr.degree]
  | one => simp [univariate, Expr.eval, Expr.degree]
  | a => simp [univariate, Expr.eval, Expr.degree]
  | d => simp [univariate, Expr.eval, Expr.degree]
  | scale c p ih =>
      exact (Polynomial.natDegree_smul_le c (univariate p)).trans ih
  | add p q ihp ihq =>
      exact (Polynomial.natDegree_add_le _ _).trans (max_le_max ihp ihq)
  | mul p q ihp ihq =>
      exact Polynomial.natDegree_mul_le.trans (add_le_add ihp ihq)

theorem eval_univariate (p : Expr) (x : ℝ) :
    (univariate p).eval x = p.eval x 0 := by
  simpa only [univariate, Polynomial.coe_evalRingHom, Polynomial.eval_X,
    Polynomial.eval_zero] using expr_map_eval (Polynomial.evalRingHom x) p Polynomial.X 0

theorem eval_function_apply {ι : Type*} (p : Expr) (eigenvalues : ι → ℝ) (i : ι) :
    p.eval eigenvalues 0 i = p.eval (eigenvalues i) 0 := by
  induction p <;> simp_all [Expr.eval]

theorem eval_diagonal {N : ℕ} (p : Expr) (eigenvalues : Fin N → ℝ) :
    p.eval (Matrix.diagonal eigenvalues) 0 =
      Matrix.diagonal (fun i => (univariate p).eval (eigenvalues i)) := by
  have h := expr_map_eval (diagonalRingHom (Fin N) ℝ) p eigenvalues 0
  simp only [diagonalRingHom_apply] at h
  have hz : Matrix.diagonal (0 : Fin N → ℝ) = 0 := by
    ext i j
    simp [Matrix.diagonal_apply]
  rw [hz] at h
  rw [← h]
  congr 1
  ext i
  rw [eval_function_apply, eval_univariate]

theorem eval_diagonal_seed {N : ℕ} (p : Expr) (eigenvalues : Fin N → ℝ) :
    p.eval (Matrix.diagonal eigenvalues) 0 *ᵥ (fun _ => (1 : ℝ)) =
      fun i => (univariate p).eval (eigenvalues i) := by
  rw [eval_diagonal]
  ext i
  simp [Matrix.mulVec_diagonal]

theorem word_repeat_diagonal {N : ℕ} (eigenvalues : Fin N → ℝ) (k : ℕ) :
    Spanning.wordVector (Matrix.diagonal eigenvalues) 0 (fun _ => (1 : ℝ))
      (List.replicate k false) = fun i => eigenvalues i ^ k := by
  induction k with
  | zero => simp [Spanning.wordVector]
  | succ k ih =>
      ext i
      simp only [List.replicate_succ, Spanning.wordVector, ih,
        Matrix.mulVec_diagonal, pow_succ']

theorem diagonal_jointModule_top {N : ℕ} (eigenvalues : Fin N → ℝ)
    (heigenvalues : Function.Injective eigenvalues) :
    Spanning.jointModule (Matrix.diagonal eigenvalues) 0 (fun _ => (1 : ℝ)) = ⊤ := by
  have hunit : IsUnit (Matrix.vandermonde eigenvalues) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr heigenvalues))
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨c, rfl⟩ := hsurj x
  have hcomb : Matrix.vandermonde eigenvalues *ᵥ c =
      ∑ k : Fin N, c k • Spanning.wordVector (Matrix.diagonal eigenvalues) 0
        (fun _ => (1 : ℝ)) (List.replicate k.val false) := by
    ext i
    simp only [word_repeat_diagonal, Matrix.mulVec, dotProduct, Matrix.vandermonde,
      Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcomb]
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (Spanning.wordVector_mem _ _ _ _)

def powerEvaluation {N : ℕ} (eigenvalues : Fin N → ℝ) (d : ℕ) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  (Matrix.of (fun (i : Fin N) (j : Fin (d + 1)) => eigenvalues i ^ (j : ℕ))).mulVecLin

theorem low_degree_mem_range {N : ℕ} (eigenvalues : Fin N → ℝ) (p : Expr) (d : ℕ)
    (hd : p.degree ≤ d) :
    p.eval (Matrix.diagonal eigenvalues) 0 *ᵥ (fun _ => (1 : ℝ)) ∈
      LinearMap.range (powerEvaluation eigenvalues d) := by
  have hp : univariate p ∈ Polynomial.degreeLT ℝ (d + 1) := by
    apply Polynomial.mem_degreeLT.mpr
    exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr
      (Nat.lt_succ_of_le ((univariate_natDegree_le p).trans hd)))
  refine ⟨Polynomial.degreeLTEquiv ℝ (d + 1) ⟨univariate p, hp⟩, ?_⟩
  rw [eval_diagonal_seed]
  ext i
  change (∑ j : Fin (d + 1), eigenvalues i ^ j.val * _) = (univariate p).eval (eigenvalues i)
  rw [Polynomial.eval_eq_sum_degreeLTEquiv hp]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A fixed family of actual integer-coefficient expression trees that spans
this diagonal witness has formal degree at least N-1. -/
theorem polynomial_frame_degree_lower_bound {N : ℕ} {ι : Type*}
    (eigenvalues : Fin N → ℝ) (heigenvalues : Function.Injective eigenvalues) (ps : ι → Expr) (d : ℕ)
    (hdegree : ∀ i, (ps i).degree ≤ d)
    (hspan : Submodule.span ℝ (Set.range (fun i =>
      (ps i).eval (Matrix.diagonal eigenvalues) 0 *ᵥ (fun _ => (1 : ℝ)))) =
        Spanning.jointModule (Matrix.diagonal eigenvalues) 0 (fun _ => (1 : ℝ))) :
    N - 1 ≤ d := by
  have hle : Submodule.span ℝ (Set.range (fun i =>
      (ps i).eval (Matrix.diagonal eigenvalues) 0 *ᵥ (fun _ => (1 : ℝ)))) ≤
        LinearMap.range (powerEvaluation eigenvalues d) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact low_degree_mem_range eigenvalues (ps i) d (hdegree i)
  rw [hspan, diagonal_jointModule_top eigenvalues heigenvalues] at hle
  have htop : LinearMap.range (powerEvaluation eigenvalues d) = ⊤ := top_le_iff.mp hle
  have hdim : Module.finrank ℝ (LinearMap.range (powerEvaluation eigenvalues d)) = N := by
    rw [htop, finrank_top, Module.finrank_pi, Fintype.card_fin]
  have hr : Module.finrank ℝ (LinearMap.range (powerEvaluation eigenvalues d)) ≤ d + 1 := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      LinearMap.finrank_range_le (powerEvaluation eigenvalues d)
  rw [hdim] at hr
  omega

/-- The entries 0,1,...,N-1 give a concrete real-symmetric witness. -/
theorem explicit_diagonal_degree_lower_bound {N : ℕ} {ι : Type*} (ps : ι → Expr) (d : ℕ)
    (hdegree : ∀ i, (ps i).degree ≤ d)
    (hspan : Submodule.span ℝ (Set.range (fun i =>
      (ps i).eval (Matrix.diagonal (fun j : Fin N => (j.val : ℝ))) 0 *ᵥ
        (fun _ => (1 : ℝ)))) =
      Spanning.jointModule (Matrix.diagonal (fun j : Fin N => (j.val : ℝ))) 0
        (fun _ => (1 : ℝ))) : N - 1 ≤ d := by
  apply polynomial_frame_degree_lower_bound _ ?_ ps d hdegree hspan
  intro i j hij
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at hij
  exact_mod_cast hij

#print axioms diagonal_jointModule_top
#print axioms polynomial_frame_degree_lower_bound
#print axioms explicit_diagonal_degree_lower_bound
end
end ADComplete.ProbeDegreeLowerBound
