import Mathlib

/-! Primitive polynomial coordinate vectors and their rational scalar factors. -/
namespace ADComplete.PolynomialPrimitivity

open Polynomial
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Coprime finite coordinates are expressed by the unit ideal they generate. -/
def Primitive (w : ι → ℝ[X]) : Prop := Ideal.span (Set.range w) = ⊤

theorem primitive_bezout (w : ι → ℝ[X]) (hw : Primitive w) :
    ∃ a : ι → ℝ[X], ∑ i, a i * w i = 1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  rw [hw]
  trivial

/-- If a rational scalar times every primitive coordinate is polynomial, then
the scalar itself is polynomial. No polynomiality premise is imposed on it. -/
theorem rational_factor_is_polynomial
    (w p : ι → ℝ[X]) (hw : Primitive w) (c : RatFunc ℝ)
    (h : ∀ i, algebraMap ℝ[X] (RatFunc ℝ) (p i) =
      c * algebraMap ℝ[X] (RatFunc ℝ) (w i)) :
    ∃ q : ℝ[X], algebraMap ℝ[X] (RatFunc ℝ) q = c := by
  classical
  obtain ⟨a, ha⟩ := primitive_bezout w hw
  refine ⟨∑ i, a i * p i, ?_⟩
  calc
    algebraMap ℝ[X] (RatFunc ℝ) (∑ i, a i * p i) =
        ∑ i, algebraMap ℝ[X] (RatFunc ℝ) (a i) *
          algebraMap ℝ[X] (RatFunc ℝ) (p i) := by simp
    _ = c * ∑ i, algebraMap ℝ[X] (RatFunc ℝ) (a i) *
          algebraMap ℝ[X] (RatFunc ℝ) (w i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [h i]
        ring
    _ = c * algebraMap ℝ[X] (RatFunc ℝ) (∑ i, a i * w i) := by simp
    _ = c := by rw [ha]; simp

theorem primitive_has_nonzero_constant
    (w : ι → ℝ[X]) (hw : Primitive w) : ∃ i, (w i).coeff 0 ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := primitive_bezout w hw
  have heq := congrArg (fun p : ℝ[X] => p.coeff 0) ha
  simp [Polynomial.coeff_mul, h] at heq

theorem primitive_of_gcd_one (w : ι → ℝ[X])
    (hw : Finset.univ.gcd w = 1) : Primitive w := by
  classical
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul Finset.univ w
  rw [hw] at ha
  apply (Ideal.eq_top_iff_one _).mpr
  rw [ha]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))

/-- Every nonzero finite polynomial coordinate vector admits a common factor
and primitive coordinates. This constructs the normalization used in the proof. -/
theorem extract_primitive (w : ι → ℝ[X]) (hw : ∃ i, w i ≠ 0) :
    ∃ g : ℝ[X], g ≠ 0 ∧ ∃ w' : ι → ℝ[X],
      Primitive w' ∧ ∀ i, w i = g * w' i := by
  classical
  obtain ⟨i, hi⟩ := hw
  obtain ⟨w', he, hg⟩ := Finset.extract_gcd w
    (show (Finset.univ : Finset ι).Nonempty from ⟨i, Finset.mem_univ i⟩)
  refine ⟨Finset.univ.gcd w, ?_, w', primitive_of_gcd_one w' hg, ?_⟩
  · intro hz
    have heq := he i (Finset.mem_univ i)
    rw [hz, zero_mul] at heq
    exact hi heq
  · intro j
    exact he j (Finset.mem_univ j)

/-- One maximal nonzero coordinate bounds the polynomial multiplier degree. -/
theorem multiplier_natDegree_le_one
    (q w p : ℝ[X]) (ell : ℕ) (hw : w ≠ 0)
    (hd : w.natDegree = ell) (hp : p.natDegree ≤ ell + 1)
    (h : q * w = p) : q.natDegree ≤ 1 := by
  by_cases hq : q = 0
  · simp [hq]
  have heq := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_mul hq hw, hd] at heq
  omega

theorem rational_factor_degree_le_one
    (w p : ι → ℝ[X]) (hw : Primitive w) (c : RatFunc ℝ) (ell : ℕ)
    (hwd : ∀ i, (w i).natDegree ≤ ell)
    (hwl : ∃ i, (w i).coeff ell ≠ 0)
    (hpd : ∀ i, (p i).natDegree ≤ ell + 1)
    (h : ∀ i, algebraMap ℝ[X] (RatFunc ℝ) (p i) =
      c * algebraMap ℝ[X] (RatFunc ℝ) (w i)) :
    ∃ q : ℝ[X], algebraMap ℝ[X] (RatFunc ℝ) q = c ∧ q.natDegree ≤ 1 := by
  obtain ⟨q, hq⟩ := rational_factor_is_polynomial w p hw c h
  obtain ⟨i, hi⟩ := hwl
  have hwi : w i ≠ 0 := by
    intro hz
    simp [hz] at hi
  have heq : q * w i = p i := by
    apply RatFunc.algebraMap_injective ℝ
    rw [map_mul, hq, h i]
  refine ⟨q, hq, multiplier_natDegree_le_one q (w i) (p i) ell hwi ?_ (hpd i) heq⟩
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (hwd i) hi

#print axioms rational_factor_is_polynomial
#print axioms primitive_has_nonzero_constant
#print axioms extract_primitive
#print axioms multiplier_natDegree_le_one
#print axioms rational_factor_degree_le_one

end
end ADComplete.PolynomialPrimitivity
