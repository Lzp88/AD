import PaperVerifier.ADComplete.ProbeDegreeLowerBound

/-! The unrestricted real-coefficient noncommutative polynomial degree obstruction.
Polynomials are their canonical finitely supported word coefficients; no integer
coefficient or circuit-syntax restriction is imposed. -/
namespace ADComplete.ProbeDegreeLowerBound
noncomputable section
open scoped BigOperators
open Matrix

abbrev RealNCPolynomial := List Bool →₀ ℝ

def realFormalDegree (c : RealNCPolynomial) : ℕ := c.support.sup List.length

def realPolynomialVector {N : ℕ} (eigenvalues : Fin N → ℝ)
    (c : RealNCPolynomial) : Fin N → ℝ :=
  c.sum (fun w a => a • Spanning.wordVector (Matrix.diagonal eigenvalues) 0 (fun _ => 1) w)

def wordPolynomial : List Bool → Polynomial ℝ
  | [] => 1
  | false :: w => Polynomial.X * wordPolynomial w
  | true :: _ => 0

theorem wordPolynomial_natDegree (w : List Bool) : (wordPolynomial w).natDegree ≤ w.length := by
  induction w with
  | nil => simp [wordPolynomial]
  | cons b w ih =>
      cases b
      · have hh : ((Polynomial.X : Polynomial ℝ) * wordPolynomial w).natDegree ≤
            1 + (wordPolynomial w).natDegree := by
          simpa only [Polynomial.natDegree_X] using
            (Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℝ)) (q := wordPolynomial w))
        exact hh.trans (by simpa only [List.length_cons] using (show 1 + (wordPolynomial w).natDegree ≤ w.length + 1 by omega))
      · simp [wordPolynomial]

theorem diagonal_word_eval {N : ℕ} (eigenvalues : Fin N → ℝ) (w : List Bool) :
    Spanning.wordVector (Matrix.diagonal eigenvalues) 0 (fun _ => 1) w =
      fun i => (wordPolynomial w).eval (eigenvalues i) := by
  induction w with
  | nil => simp [Spanning.wordVector, wordPolynomial]
  | cons b w ih =>
      cases b
      · ext i
        simp only [Spanning.wordVector, ih, Matrix.mulVec_diagonal, wordPolynomial,
          Polynomial.eval_mul, Polynomial.eval_X]
      · ext i
        simp [Spanning.wordVector, wordPolynomial]

theorem polynomial_eval_mem_powerRange {N : ℕ} (eigenvalues : Fin N → ℝ)
    (p : Polynomial ℝ) (d : ℕ) (hd : p.natDegree ≤ d) :
    (fun i => p.eval (eigenvalues i)) ∈ LinearMap.range (powerEvaluation eigenvalues d) := by
  have hp : p ∈ Polynomial.degreeLT ℝ (d + 1) := Polynomial.mem_degreeLT.mpr
    (Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hd)))
  refine ⟨Polynomial.degreeLTEquiv ℝ (d + 1) ⟨p, hp⟩, ?_⟩
  ext i
  change (∑ j : Fin (d + 1), eigenvalues i ^ j.val * _) = p.eval (eigenvalues i)
  rw [Polynomial.eval_eq_sum_degreeLTEquiv hp]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem realPolynomialVector_mem_powerRange {N : ℕ} (eigenvalues : Fin N → ℝ)
    (c : RealNCPolynomial) (d : ℕ) (hd : realFormalDegree c ≤ d) :
    realPolynomialVector eigenvalues c ∈ LinearMap.range (powerEvaluation eigenvalues d) := by
  unfold realPolynomialVector Finsupp.sum
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  rw [diagonal_word_eval]
  apply polynomial_eval_mem_powerRange
  exact (wordPolynomial_natDegree w).trans
    ((Finset.le_sup (f := List.length) hw).trans hd)

/-- Exact N-1 lower bound for all real-coefficient noncommutative polynomial frames. -/
theorem real_polynomial_frame_degree_lower_bound {N : ℕ} {ι : Type*}
    (eigenvalues : Fin N → ℝ) (hinj : Function.Injective eigenvalues)
    (ps : ι → RealNCPolynomial) (d : ℕ)
    (hdegree : ∀ i, realFormalDegree (ps i) ≤ d)
    (hspan : Submodule.span ℝ (Set.range (fun i => realPolynomialVector eigenvalues (ps i))) =
      Spanning.jointModule (Matrix.diagonal eigenvalues) 0 (fun _ => 1)) : N - 1 ≤ d := by
  have hle : Submodule.span ℝ (Set.range (fun i => realPolynomialVector eigenvalues (ps i))) ≤
      LinearMap.range (powerEvaluation eigenvalues d) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact realPolynomialVector_mem_powerRange eigenvalues (ps i) d (hdegree i)
  rw [hspan, diagonal_jointModule_top eigenvalues hinj] at hle
  have htop : LinearMap.range (powerEvaluation eigenvalues d) = ⊤ := top_le_iff.mp hle
  have hdim : Module.finrank ℝ (LinearMap.range (powerEvaluation eigenvalues d)) = N := by
    rw [htop, finrank_top, Module.finrank_pi, Fintype.card_fin]
  have hr : Module.finrank ℝ (LinearMap.range (powerEvaluation eigenvalues d)) ≤ d + 1 := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      LinearMap.finrank_range_le (powerEvaluation eigenvalues d)
  rw [hdim] at hr
  omega

theorem explicit_real_diagonal_degree_lower_bound {N : ℕ} {ι : Type*}
    (ps : ι → RealNCPolynomial) (d : ℕ) (hdegree : ∀ i, realFormalDegree (ps i) ≤ d)
    (hspan : Submodule.span ℝ (Set.range (fun i =>
      realPolynomialVector (fun j : Fin N => (j.val : ℝ)) (ps i))) =
        Spanning.jointModule (Matrix.diagonal (fun j : Fin N => (j.val : ℝ))) 0 (fun _ => 1)) :
    N - 1 ≤ d := by
  apply real_polynomial_frame_degree_lower_bound _ ?_ ps d hdegree hspan
  intro i j hij
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at hij
  exact_mod_cast hij

#print axioms realPolynomialVector_mem_powerRange
#print axioms real_polynomial_frame_degree_lower_bound
#print axioms explicit_real_diagonal_degree_lower_bound
end
end ADComplete.ProbeDegreeLowerBound
