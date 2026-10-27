import MultiSymmetric.RigidityPolynomial

namespace MultiSymmetric.Rigidity
open Polynomial Matrix
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {τ ι : Type*} [Fintype τ] [Fintype ι] [Nonempty τ]

theorem polynomial_line_degree_zero
    (a : τ → ℝ) (ha : Function.Injective a)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : τ → ℝ) (hgap : ∑ k, (hi k-lo k)<1)
    (hB : ∀ k u,
      lo k * ADComplete.Rigidity.pairing u u ≤ ADComplete.Rigidity.pairing u ((B k).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((B k).mulVec u) ≤ hi k * ADComplete.Rigidity.pairing u u)
    (w : ι → ℝ[X]) (hw : ADComplete.PolynomialPrimitivity.Primitive w)
    (ell : ℕ) (hdegree : ∀ i, (w i).natDegree ≤ ell)
    (hleading : ADComplete.Rigidity.coefficientVector w ell ≠ 0)
    (q : ℝ[X]) (hq : q.natDegree ≤ Fintype.card τ)
    (hline : ∀ i, denom a * (w i).derivative +
      denom a * ADComplete.Rigidity.polynomialAction H w i +
      ∑ k, cofactor a k * ADComplete.Rigidity.polynomialAction (B k) w i = q*w i) :
    ell=0 := by
  classical
  by_cases hell : ell=0
  · exact hell
  have hellp : 0<ell := Nat.pos_of_ne_zero hell
  let s := Fintype.card τ
  have hs : 0<s := Fintype.card_pos
  let β := q.coeff s
  let α : τ → ℝ := fun k => q.eval (a k) / (cofactor a k).eval (a k)
  have hqform : q=C β*denom a+∑ k,C (α k)*cofactor a k :=
    polynomial_partial_fractions a ha q hq
  have hDc : (denom a).coeff s=1 := by
    change (denom a).coeff (Fintype.card τ)=1
    rw [← denom_natDegree a]
    exact (denom_monic a).coeff_natDegree
  have hQc (k : τ) : (cofactor a k).coeff (s-1)=1 := by
    change (cofactor a k).coeff (Fintype.card τ-1)=1
    rw [← cofactor_natDegree a k]
    exact (cofactor_monic a k).coeff_natDegree
  have hDdeg : (denom a).natDegree ≤ s := (denom_natDegree a).le
  have hQdeg (k : τ) : (cofactor a k).natDegree ≤ s-1 := (cofactor_natDegree a k).le
  have hHd (i : ι) : (ADComplete.Rigidity.polynomialAction H w i).natDegree ≤ ell :=
    ADComplete.PrimitiveLine.action_natDegree_le H w ell hdegree i
  have hBd (k : τ) (i : ι) :
      (ADComplete.Rigidity.polynomialAction (B k) w i).natDegree ≤ ell :=
    ADComplete.PrimitiveLine.action_natDegree_le (B k) w ell hdegree i
  have hwd (i : ι) : (w i).derivative.natDegree ≤ ell-1 :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right (hdegree i) 1)
  have hdertop (i : ι) : (denom a*(w i).derivative).coeff (s+ell)=0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hh := Polynomial.natDegree_mul_le (p := denom a) (q := (w i).derivative)
    have := hwd i
    omega
  have hrestop (k : τ) (i : ι) :
      (cofactor a k*ADComplete.Rigidity.polynomialAction (B k) w i).coeff (s+ell)=0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hh := Polynomial.natDegree_mul_le (p := cofactor a k)
      (q := ADComplete.Rigidity.polynomialAction (B k) w i)
    have := hBd k i
    have := hQdeg k
    omega
  have hres : ∀ k, (B k).mulVec (fun i => (w i).eval (a k)) =
      α k • (fun i => (w i).eval (a k)) := by
    intro k
    ext i
    have he := congrArg (Polynomial.eval (a k)) (hline i)
    simp only [eval_add, eval_mul, eval_denom, zero_mul, zero_add, eval_finsetSum] at he
    have hsum : ∑ l, (cofactor a l).eval (a k) *
        (ADComplete.Rigidity.polynomialAction (B l) w i).eval (a k) =
      (cofactor a k).eval (a k) *
        (ADComplete.Rigidity.polynomialAction (B k) w i).eval (a k) := by
      apply Finset.sum_eq_single k
      · intro l _ hl
        rw [eval_cofactor_other a l k hl, zero_mul]
      · simp
    rw [hsum] at he
    have hact (T : Matrix ι ι ℝ) :
        (ADComplete.Rigidity.polynomialAction T w i).eval (a k) =
          T.mulVec (fun j => (w j).eval (a k)) i := by
      simp [ADComplete.Rigidity.polynomialAction, Polynomial.eval_finsetSum, Matrix.mulVec, dotProduct]
    rw [hact] at he
    change (B k).mulVec _ i = α k * (w i).eval (a k)
    dsimp [α]
    apply mul_left_cancel₀ (eval_cofactor_ne a ha k)
    calc
      (cofactor a k).eval (a k) * (B k).mulVec (fun j => (w j).eval (a k)) i =
          q.eval (a k) * (w i).eval (a k) := he
      _ = (cofactor a k).eval (a k) *
          (q.eval (a k) / (cofactor a k).eval (a k) * (w i).eval (a k)) := by
        field_simp [eval_cofactor_ne a ha k]
  have htop : H.mulVec (ADComplete.Rigidity.coefficientVector w ell) =
      β • ADComplete.Rigidity.coefficientVector w ell := by
    rw [← ADComplete.Rigidity.coefficient_polynomialAction]
    ext i
    have he := congrArg (fun p : ℝ[X] => p.coeff (s+ell)) (hline i)
    simp only [coeff_add, Polynomial.finsetSum_coeff, hdertop, hrestop,
      Finset.sum_const_zero, zero_add, add_zero] at he
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hDdeg (hHd i),
      Polynomial.coeff_mul_add_eq_of_natDegree_le hq (hdegree i), hDc, one_mul] at he
    exact he
  have hnext : (ell : ℝ) • ADComplete.Rigidity.coefficientVector w ell +
      H.mulVec (ADComplete.Rigidity.coefficientVector w (ell-1)) +
        ∑ k, (B k).mulVec (ADComplete.Rigidity.coefficientVector w ell) =
      β • ADComplete.Rigidity.coefficientVector w (ell-1) +
        (∑ k,α k) • ADComplete.Rigidity.coefficientVector w ell := by
    ext i
    have he := congrArg (fun p : ℝ[X] => p.coeff (s+ell-1)) (hline i)
    have hder : (denom a*(w i).derivative).coeff (s+ell-1) =
        (ell : ℝ)*(w i).coeff ell := by
      have hn : s+ell-1=s+(ell-1) := by omega
      rw [hn, Polynomial.coeff_mul_add_eq_of_natDegree_le hDdeg (hwd i), hDc, one_mul,
        Polynomial.coeff_derivative]
      have he' : ell-1+1=ell := by omega
      rw [he']
      have hcast : (ell : ℝ) = ((ell-1 : ℕ) : ℝ)+1 := by exact_mod_cast he'.symm
      rw [hcast]
      ring
    have hbt (k : τ) :
        (cofactor a k * ADComplete.Rigidity.polynomialAction (B k) w i).coeff (s+ell-1) =
          (B k).mulVec (ADComplete.Rigidity.coefficientVector w ell) i := by
      have hn : s+ell-1=(s-1)+ell := by omega
      rw [hn, Polynomial.coeff_mul_add_eq_of_natDegree_le (hQdeg k) (hBd k i), hQc k, one_mul]
      exact congrFun (ADComplete.Rigidity.coefficient_polynomialAction (B k) w ell) i
    have hHnext := coeff_mul_next (denom a) (ADComplete.Rigidity.polynomialAction H w i)
      s ell hs hellp hDdeg (hHd i)
    have hqnext := coeff_mul_next q (w i) s ell hs hellp hq (hdegree i)
    have hqcoef : q.coeff (s-1)=β*(denom a).coeff (s-1)+∑ k,α k := by
      rw [hqform]
      simp only [coeff_add, coeff_C_mul, Polynomial.finsetSum_coeff, hQc, mul_one]
    simp only [coeff_add, Polynomial.finsetSum_coeff, hder, hbt] at he
    rw [hHnext, hqnext, hqcoef, hDc, one_mul] at he
    have ht := congrFun htop i
    have ha1 := congrFun (ADComplete.Rigidity.coefficient_polynomialAction H w (ell-1)) i
    have ha2 := congrFun (ADComplete.Rigidity.coefficient_polynomialAction H w ell) i
    simp only [ADComplete.Rigidity.coefficientVector, Pi.smul_apply, smul_eq_mul,
      Pi.add_apply, Finset.sum_apply] at he ht ha1 ha2 ⊢
    rw [ha1, ha2, ht] at he
    dsimp [β] at *
    nlinarith [he]
  exact coefficient_rigidity B H hH lo hi α β hgap hB ell
    (fun k i => (w i).eval (a k)) (ADComplete.Rigidity.coefficientVector w ell)
    (ADComplete.Rigidity.coefficientVector w (ell-1))
    (fun k => primitive_eval_ne_zero w hw (a k)) hleading hres htop hnext

theorem primitive_rational_line_constant
    (a : τ → ℝ) (ha : Function.Injective a)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : τ → ℝ) (hgap : ∑ k,(hi k-lo k)<1)
    (hB : ∀ k u,
      lo k * ADComplete.Rigidity.pairing u u ≤ ADComplete.Rigidity.pairing u ((B k).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((B k).mulVec u) ≤ hi k * ADComplete.Rigidity.pairing u u)
    (w : ι → ℝ[X]) (hw : ADComplete.PolynomialPrimitivity.Primitive w)
    (c : RF)
    (hline : ∀ i, algebraMap ℝ[X] RF
      (denom a * (w i).derivative + denom a * ADComplete.Rigidity.polynomialAction H w i +
        ∑ k, cofactor a k * ADComplete.Rigidity.polynomialAction (B k) w i) =
      c*algebraMap ℝ[X] RF (w i)) :
    ∀ i, w i=C ((w i).coeff 0) := by
  obtain ⟨ell, hd, hl⟩ := ADComplete.PrimitiveLine.primitive_degree_witness w hw
  have hwl : ∃ i,(w i).coeff ell≠0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hl
    exact ⟨i,hi⟩
  obtain ⟨q,hq,hqd⟩ := rational_factor_degree_le w _ hw c ell (Fintype.card τ)
    hd hwl (cleared_line_degree a B H w ell hd) hline
  have hp (i : ι) : denom a*(w i).derivative + denom a*ADComplete.Rigidity.polynomialAction H w i +
      ∑ k,cofactor a k*ADComplete.Rigidity.polynomialAction (B k) w i = q*w i := by
    apply RatFunc.algebraMap_injective ℝ
    rw [map_mul,hq]
    exact hline i
  have hz := polynomial_line_degree_zero a ha B H hH lo hi hgap hB w hw ell hd hl q hqd hp
  intro i
  exact Polynomial.eq_C_of_natDegree_eq_zero (by simpa [hz] using hd i)

theorem primitive_representative_constant
    (a : τ → ℝ) (ha : Function.Injective a)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : τ → ℝ) (hgap : ∑ k,(hi k-lo k)<1)
    (hB : ∀ k u,
      lo k * ADComplete.Rigidity.pairing u u ≤ ADComplete.Rigidity.pairing u ((B k).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((B k).mulVec u) ≤ hi k * ADComplete.Rigidity.pairing u u)
    (v : ι → RF) (w : ι → ℝ[X]) (q gamma : RF) (hq : q≠0)
    (hw : ADComplete.PolynomialPrimitivity.Primitive w)
    (hrep : ∀ i,v i=q*algebraMap ℝ[X] RF (w i))
    (hline : ∀ i, ADComplete.RationalDerivative.derivative (v i) +
      (rationalConnection a B H).mulVec v i=gamma*v i) :
    ∀ i,w i=C ((w i).coeff 0) := by
  have hn := ADComplete.RationalLineNormalization.normalize_connection_line
    ADComplete.RationalDerivative.derivative (rationalConnection a B H) v
    (fun i=>algebraMap ℝ[X] RF (w i)) gamma q hq hrep hline
  apply primitive_rational_line_constant a ha B H hH lo hi hgap hB w hw
    (algebraMap ℝ[X] RF (denom a)*(gamma-ADComplete.RationalDerivative.derivative q/q))
  intro i
  rw [scaled_polynomial_connection, hn i, mul_assoc]

#print axioms primitive_representative_constant
end
end MultiSymmetric.Rigidity
