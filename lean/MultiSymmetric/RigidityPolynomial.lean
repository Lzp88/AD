import MultiSymmetric.RigidityBasic

namespace MultiSymmetric.Rigidity
open Polynomial Matrix
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
variable {τ ι : Type*} [Fintype τ] [Fintype ι]

/-- The next-to-leading coefficient formula with upper degree bounds. -/
theorem coeff_mul_next (f g : ℝ[X]) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ e) :
    (f*g).coeff (d+e-1) = f.coeff d * g.coeff (e-1) +
      f.coeff (d-1) * g.coeff e := by
  classical
  let S : Finset (ℕ × ℕ) := {(d,e-1), (d-1,e)}
  have hs : S ⊆ Finset.HasAntidiagonal.antidiagonal (d+e-1) := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> rw [Finset.HasAntidiagonal.mem_antidiagonal] <;> omega
  rw [Polynomial.coeff_mul]
  have hreduce : ∑ z ∈ Finset.HasAntidiagonal.antidiagonal (d+e-1), f.coeff z.1 * g.coeff z.2 =
      ∑ z ∈ S, f.coeff z.1 * g.coeff z.2 := by
    symm
    apply Finset.sum_subset hs
    intro z hz hn
    have hz' := Finset.HasAntidiagonal.mem_antidiagonal.mp hz
    by_cases hzd : d < z.1
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hf.trans_lt hzd), zero_mul]
    by_cases hze : e < z.2
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hg.trans_lt hze), mul_zero]
    have hh : z = (d,e-1) ∨ z = (d-1,e) := by
      rcases z with ⟨j,k⟩
      simp only [Prod.mk.injEq] at *
      omega
    exact False.elim (hn (by simpa [S] using hh))
  rw [hreduce]
  have hne : (d,e-1) ≠ (d-1,e) := by intro h; have := congrArg Prod.fst h; simp at this; omega
  simp [S, hne]

/-- Polynomial partial fractions, obtained by interpolation at the distinct poles. -/
theorem polynomial_partial_fractions [Nonempty τ]
    (a : τ → ℝ) (ha : Function.Injective a) (q : ℝ[X])
    (hq : q.natDegree ≤ Fintype.card τ) :
    q = C (q.coeff (Fintype.card τ)) * denom a +
      ∑ k, C (q.eval (a k) / (cofactor a k).eval (a k)) * cofactor a k := by
  classical
  let s := Fintype.card τ
  have hs : 0 < s := Fintype.card_pos
  let β := q.coeff s
  let α : τ → ℝ := fun k => q.eval (a k) / (cofactor a k).eval (a k)
  let r := q - C β * denom a - ∑ k, C (α k) * cofactor a k
  have hDc : (denom a).coeff s = 1 := by
    change (denom a).coeff (Fintype.card τ) = 1
    rw [← denom_natDegree a]
    exact (denom_monic a).coeff_natDegree
  have hQc (k : τ) (n : ℕ) (hn : s ≤ n) : (cofactor a k).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [cofactor_natDegree]
    change s-1<n
    omega
  have hr : r.natDegree ≤ s-1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hsn : s ≤ n := by omega
    simp only [r, coeff_sub, coeff_C_mul, Polynomial.finsetSum_coeff]
    have hsum : ∑ k, α k * (cofactor a k).coeff n = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [hQc k n hsn, mul_zero]
    rw [hsum, sub_zero]
    by_cases hns : n=s
    · subst n
      simp [β, hDc]
    · have hlt : s<n := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [denom_natDegree]; exact hlt)]
      ring
  have hre (k : τ) : r.eval (a k) = 0 := by
    simp only [r, eval_sub, eval_mul, eval_C, eval_denom, mul_zero, sub_zero, eval_finsetSum]
    have hsum : ∑ l, α l * (cofactor a l).eval (a k) =
        α k * (cofactor a k).eval (a k) := by
      apply Finset.sum_eq_single k
      · intro l _ hl
        rw [eval_cofactor_other a l k hl, mul_zero]
      · simp
    rw [hsum]
    dsimp [α]
    rw [div_mul_cancel₀ _ (eval_cofactor_ne a ha k), sub_self]
  have hrzero : r = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    r ha hre (by change r.natDegree < s; omega)
  dsimp [r] at hrzero
  linear_combination hrzero

/-- Degree bound for the numerator of the cleared multi-pole connection. -/
theorem cleared_line_degree (a : τ → ℝ) (B : τ → Matrix ι ι ℝ)
    (H : Matrix ι ι ℝ) (w : ι → ℝ[X]) (ell : ℕ)
    (hw : ∀ i, (w i).natDegree ≤ ell) (i : ι) :
    (denom a * (w i).derivative + denom a * ADComplete.Rigidity.polynomialAction H w i +
      ∑ k, cofactor a k * ADComplete.Rigidity.polynomialAction (B k) w i).natDegree ≤
        ell + Fintype.card τ := by
  classical
  have hm (p : ℝ[X]) (hp : p.natDegree ≤ ell) :
      (denom a*p).natDegree ≤ ell+Fintype.card τ := by
    have hh := Polynomial.natDegree_mul_le (p := denom a) (q := p)
    rw [denom_natDegree] at hh
    omega
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact hm _ ((Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (hw i)))
    · exact hm _ (ADComplete.PrimitiveLine.action_natDegree_le H w ell hw i)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    have hh := Polynomial.natDegree_mul_le (p := cofactor a k)
      (q := ADComplete.Rigidity.polynomialAction (B k) w i)
    have hh' := ADComplete.PrimitiveLine.action_natDegree_le (B k) w ell hw i
    rw [cofactor_natDegree] at hh
    omega

end
end MultiSymmetric.Rigidity
