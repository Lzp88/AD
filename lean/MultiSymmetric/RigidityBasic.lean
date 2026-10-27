import PaperVerifier.ADComplete.SpectralRigidity
import PaperVerifier.ADComplete.PrimitiveLine

namespace MultiSymmetric.Rigidity
open Polynomial Matrix
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
abbrev RF := RatFunc ℝ
variable {τ ι : Type*} [Fintype τ] [Fintype ι]

def rationalConnection (a : τ → ℝ) (B : τ → Matrix ι ι ℝ)
    (H : Matrix ι ι ℝ) : Matrix ι ι RF := fun i j =>
  algebraMap ℝ RF (H i j) + ∑ k,
    algebraMap ℝ RF (B k i j) / algebraMap ℝ[X] RF (X - C (a k))

def denom (a : τ → ℝ) : ℝ[X] := ∏ k, (X - C (a k))
def cofactor (a : τ → ℝ) (k : τ) : ℝ[X] := by
  classical
  exact ∏ l ∈ Finset.univ.erase k, (X - C (a l))

theorem factor_mul_cofactor (a : τ → ℝ) (k : τ) :
    (X - C (a k)) * cofactor a k = denom a := by
  classical
  exact Finset.mul_prod_erase _ _ (Finset.mem_univ k)

theorem denom_monic (a : τ → ℝ) : (denom a).Monic :=
  Polynomial.monic_prod_X_sub_C a Finset.univ

theorem cofactor_monic (a : τ → ℝ) (k : τ) : (cofactor a k).Monic := by
  classical
  exact Polynomial.monic_prod_X_sub_C a (Finset.univ.erase k)

theorem denom_natDegree (a : τ → ℝ) : (denom a).natDegree = Fintype.card τ := by
  classical
  simp [denom, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]

theorem cofactor_natDegree (a : τ → ℝ) (k : τ) :
    (cofactor a k).natDegree = Fintype.card τ - 1 := by
  classical
  simp [cofactor, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]

theorem eval_denom (a : τ → ℝ) (k : τ) : (denom a).eval (a k) = 0 := by
  rw [← factor_mul_cofactor a k]
  simp

theorem eval_cofactor_ne (a : τ → ℝ) (ha : Function.Injective a) (k : τ) :
    (cofactor a k).eval (a k) ≠ 0 := by
  classical
  simp only [cofactor, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hi).1 (ha h).symm)

theorem eval_cofactor_other (a : τ → ℝ) (k l : τ) (h : k ≠ l) :
    (cofactor a k).eval (a l) = 0 := by
  classical
  simp only [cofactor, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ l⟩)
  simp

theorem scaled_polynomial_connection (a : τ → ℝ)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (w : ι → ℝ[X]) (i : ι) :
    algebraMap ℝ[X] RF
      (denom a * (w i).derivative + denom a * ADComplete.Rigidity.polynomialAction H w i +
        ∑ k, cofactor a k * ADComplete.Rigidity.polynomialAction (B k) w i) =
      algebraMap ℝ[X] RF (denom a) *
        (ADComplete.RationalDerivative.derivative (algebraMap ℝ[X] RF (w i)) +
          (rationalConnection a B H).mulVec
            (fun j => algebraMap ℝ[X] RF (w j)) i) := by
  classical
  have hf (k : τ) : algebraMap ℝ[X] RF (X - C (a k)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (monic_X_sub_C (a k)).ne_zero
  have hq (k : τ) : algebraMap ℝ[X] RF (cofactor a k) =
      algebraMap ℝ[X] RF (denom a) / algebraMap ℝ[X] RF (X-C (a k)) := by
    apply (eq_div_iff (hf k)).mpr
    rw [← map_mul, mul_comm, factor_mul_cofactor]
  rw [ADComplete.RationalDerivative.derivative_polynomial]
  simp only [ADComplete.Rigidity.polynomialAction, map_add, map_mul, map_sum,
    rationalConnection, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul, ADComplete.ConstantFrame.map_C]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, ← add_assoc]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hq]
  ring

theorem primitive_eval_ne_zero (w : ι → ℝ[X])
    (hw : ADComplete.PolynomialPrimitivity.Primitive w) (a : ℝ) :
    (fun i => (w i).eval a) ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := ADComplete.PolynomialPrimitivity.primitive_bezout w hw
  intro hz
  have he := congrArg (Polynomial.eval a) hb
  have hzi (i : ι) : (w i).eval a = 0 := congrFun hz i
  simp [Polynomial.eval_finsetSum, hzi] at he

theorem rational_factor_degree_le
    (w p : ι → ℝ[X]) (hw : ADComplete.PolynomialPrimitivity.Primitive w)
    (c : RF) (ell d : ℕ)
    (hwd : ∀ i, (w i).natDegree ≤ ell)
    (hwl : ∃ i, (w i).coeff ell ≠ 0)
    (hpd : ∀ i, (p i).natDegree ≤ ell+d)
    (h : ∀ i, algebraMap ℝ[X] RF (p i) = c * algebraMap ℝ[X] RF (w i)) :
    ∃ q : ℝ[X], algebraMap ℝ[X] RF q = c ∧ q.natDegree ≤ d := by
  obtain ⟨q, hq⟩ := ADComplete.PolynomialPrimitivity.rational_factor_is_polynomial
    w p hw c h
  refine ⟨q, hq, ?_⟩
  by_cases hz : q = 0
  · simp [hz]
  obtain ⟨i, hi⟩ := hwl
  have hwi : w i ≠ 0 := by intro hh; simp [hh] at hi
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (hwd i) hi
  have heq : q * w i = p i := by
    apply RatFunc.algebraMap_injective ℝ
    rw [map_mul, hq, h i]
  have hh := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_mul hz hwi, hdeg] at hh
  have := hpd i
  omega

theorem pairing_sum (u : ι → ℝ) (v : τ → ι → ℝ) :
    ADComplete.Rigidity.pairing u (∑ k, v k) =
      ∑ k, ADComplete.Rigidity.pairing u (v k) := by
  classical
  simp only [ADComplete.Rigidity.pairing, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- The finite-residue coefficient contradiction. Later lemmas derive these
coefficient equations from an actual primitive rational connection line. -/
theorem coefficient_rigidity
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi α : τ → ℝ) (β : ℝ)
    (hgap : ∑ k, (hi k - lo k) < 1)
    (hB : ∀ k u,
      lo k * ADComplete.Rigidity.pairing u u ≤ ADComplete.Rigidity.pairing u ((B k).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((B k).mulVec u) ≤ hi k * ADComplete.Rigidity.pairing u u)
    (ell : ℕ) (wAt : τ → ι → ℝ) (wTop wPrev : ι → ℝ)
    (hwAt : ∀ k, wAt k ≠ 0) (hwTop : wTop ≠ 0)
    (hres : ∀ k, (B k).mulVec (wAt k) = α k • wAt k)
    (htop : H.mulVec wTop = β • wTop)
    (hnext : (ell : ℝ) • wTop + H.mulVec wPrev + ∑ k, (B k).mulVec wTop =
      β • wPrev + (∑ k, α k) • wTop) : ell = 0 := by
  classical
  have hp := ADComplete.Rigidity.pairing_self_pos hwTop
  have halpha (k : τ) : α k ≤ hi k := by
    have hx := (hB k (wAt k)).2
    rw [hres k, ADComplete.Rigidity.pairing_smul] at hx
    have hk := ADComplete.Rigidity.pairing_self_pos (hwAt k)
    nlinarith
  have hcross : ADComplete.Rigidity.pairing wTop (H.mulVec wPrev) =
      β * ADComplete.Rigidity.pairing wTop wPrev := by
    rw [ADComplete.Rigidity.pairing_mulVec_swap H hH, htop,
      ADComplete.Rigidity.pairing_smul]
    congr 1
    unfold ADComplete.Rigidity.pairing
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heq := congrArg (ADComplete.Rigidity.pairing wTop) hnext
  simp only [ADComplete.Rigidity.pairing_add, ADComplete.Rigidity.pairing_smul,
    pairing_sum] at heq
  rw [hcross] at heq
  have hlow : (∑ k, lo k) * ADComplete.Rigidity.pairing wTop wTop ≤
      ∑ k, ADComplete.Rigidity.pairing wTop ((B k).mulVec wTop) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => (hB k wTop).1)
  have hu : ∑ k, α k ≤ ∑ k, hi k :=
    Finset.sum_le_sum (fun k _ => halpha k)
  have hgap' : (∑ k, hi k) - (∑ k, lo k) < 1 := by
    simpa [Finset.sum_sub_distrib] using hgap
  have hell : (ell : ℝ) < 1 := by nlinarith
  have hell' : ell < 1 := by exact_mod_cast hell
  omega

end
end MultiSymmetric.Rigidity
