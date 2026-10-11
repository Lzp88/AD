import PaperVerifier.ADComplete.PolynomialPrimitivity
import PaperVerifier.ADComplete.PolynomialLine

/-! Primitive rational polynomial connection lines are constant. -/
namespace ADComplete.PrimitiveLine

open Polynomial Matrix
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem action_natDegree_le (B : Matrix ι ι ℝ) (w : ι → ℝ[X]) (ell : ℕ)
    (hw : ∀ i, (w i).natDegree ≤ ell) (i : ι) :
    (Rigidity.polynomialAction B w i).natDegree ≤ ell := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le (B i j) (w j)).trans (hw j)

theorem primitive_rational_line_degree_zero
    (B H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : ℝ) (hgap : hi - lo < 1)
    (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u (B.mulVec u) ∧
      Rigidity.pairing u (B.mulVec u) ≤ hi * Rigidity.pairing u u)
    (w : ι → ℝ[X]) (hw : PolynomialPrimitivity.Primitive w)
    (ell : ℕ) (hdegree : ∀ i, (w i).natDegree ≤ ell)
    (hleading : Rigidity.coefficientVector w ell ≠ 0)
    (c : RatFunc ℝ)
    (hline : ∀ i, algebraMap ℝ[X] (RatFunc ℝ)
      (X * (w i).derivative + Rigidity.polynomialAction B w i +
        X * Rigidity.polynomialAction H w i) =
      c * algebraMap ℝ[X] (RatFunc ℝ) (w i)) : ell = 0 := by
  classical
  let p : ι → ℝ[X] := fun i => X * (w i).derivative +
    Rigidity.polynomialAction B w i + X * Rigidity.polynomialAction H w i
  have hp : ∀ i, (p i).natDegree ≤ ell + 1 := by
    intro i
    have hd : (X * (w i).derivative).natDegree ≤ ell + 1 := by
      have h := Polynomial.natDegree_mul_le (p := (X : ℝ[X]))
        (q := (w i).derivative)
      have hd' := Polynomial.natDegree_derivative_le (w i)
      have hwdeg := hdegree i
      have hx : (X : ℝ[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
      omega
    have hbp := action_natDegree_le B w ell hdegree i
    have hhp := action_natDegree_le H w ell hdegree i
    have hxhp : (X * Rigidity.polynomialAction H w i).natDegree ≤ ell + 1 := by
      have h := Polynomial.natDegree_mul_le (p := (X : ℝ[X]))
        (q := Rigidity.polynomialAction H w i)
      have hx : (X : ℝ[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
      omega
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le ((Polynomial.natDegree_add_le _ _).trans
        (max_le hd (by omega))) hxhp)
  have hwl : ∃ i, (w i).coeff ell ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hleading
    exact ⟨i, hi⟩
  obtain ⟨q, hq, hqd⟩ := PolynomialPrimitivity.rational_factor_degree_le_one
    w p hw c ell hdegree hwl hp hline
  have hqform : q = C (q.coeff 0) + X * C (q.coeff 1) := by
    calc
      q = C (q.coeff 1) * X + C (q.coeff 0) :=
        Polynomial.eq_X_add_C_of_natDegree_le_one hqd
      _ = _ := by ring
  have hconstant : Rigidity.coefficientVector w 0 ≠ 0 := by
    obtain ⟨i, hi⟩ := PolynomialPrimitivity.primitive_has_nonzero_constant w hw
    intro hz
    exact hi (congrFun hz i)
  apply Rigidity.affine_polynomial_line_degree_zero B H hH lo hi
    (q.coeff 0) (q.coeff 1) hgap hB w ell hdegree hconstant hleading
  intro i
  have hpi : p i = q * w i := by
    apply RatFunc.algebraMap_injective ℝ
    rw [map_mul, hq]
    exact hline i
  rw [hqform] at hpi
  exact hpi

#print axioms primitive_rational_line_degree_zero

/-- The maximal degree and nonzero leading coefficient needed above exist
for every primitive finite coordinate vector; they are not extra hypotheses. -/
theorem primitive_degree_witness (w : ι → ℝ[X])
    (hw : PolynomialPrimitivity.Primitive w) :
    ∃ ell : ℕ, (∀ i, (w i).natDegree ≤ ell) ∧
      Rigidity.coefficientVector w ell ≠ 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := PolynomialPrimitivity.primitive_has_nonzero_constant w hw
  let ell := Finset.univ.sup (fun i => (w i).natDegree)
  have hb : ∀ i, (w i).natDegree ≤ ell := fun i =>
    Finset.le_sup (f := fun i => (w i).natDegree) (Finset.mem_univ i)
  refine ⟨ell, hb, ?_⟩
  by_cases hz : ell = 0
  · intro heq
    exact hi₀ (by simpa [hz, Rigidity.coefficientVector] using congrFun heq i₀)
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
      (show (Finset.univ : Finset ι).Nonempty from ⟨i₀, Finset.mem_univ i₀⟩)
      (fun i => (w i).natDegree)
    have hwi : w i ≠ 0 := by
      intro hwz
      have hn : (w i).natDegree = 0 := by rw [hwz]; simp
      exact hz (hi.trans hn)
    intro heq
    have hc : (w i).coeff (w i).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hwi
    have hcoef : (w i).coeff ell = 0 := congrFun heq i
    have hi' : ell = (w i).natDegree := hi
    rw [hi'] at hcoef
    exact hc hcoef

theorem primitive_rational_line_constant
    (B H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : ℝ) (hgap : hi - lo < 1)
    (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u (B.mulVec u) ∧
      Rigidity.pairing u (B.mulVec u) ≤ hi * Rigidity.pairing u u)
    (w : ι → ℝ[X]) (hw : PolynomialPrimitivity.Primitive w) (c : RatFunc ℝ)
    (hline : ∀ i, algebraMap ℝ[X] (RatFunc ℝ)
      (X * (w i).derivative + Rigidity.polynomialAction B w i +
        X * Rigidity.polynomialAction H w i) =
      c * algebraMap ℝ[X] (RatFunc ℝ) (w i)) :
    ∀ i, w i = C ((w i).coeff 0) := by
  obtain ⟨ell, hd, hl⟩ := primitive_degree_witness w hw
  have hz := primitive_rational_line_degree_zero B H hH lo hi hgap hB
    w hw ell hd hl c hline
  intro i
  exact Polynomial.eq_C_of_natDegree_eq_zero (by simpa [hz] using hd i)

#print axioms primitive_degree_witness
#print axioms primitive_rational_line_constant

end
end ADComplete.PrimitiveLine
