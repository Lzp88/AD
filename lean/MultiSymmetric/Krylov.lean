import MultiSymmetric.RigidityBasic
import PaperVerifier.ADComplete.ProbeKrylov
set_option autoImplicit false

namespace MultiSymmetric.Krylov
open Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
abbrev RF := RatFunc ℝ
variable {τ ι : Type*} [Fintype τ] [Fintype ι]

def polynomialVector (a : τ → ℝ) (κ : ℝ) (H : Matrix ι ι ℝ)
    (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) : ℕ → ι → ℝ[X]
  | 0 => fun i => C (v i)
  | k + 1 => fun i =>
      C κ * Rigidity.denom a * (polynomialVector a κ H A v k i).derivative +
      C κ * Rigidity.denom a * ADComplete.Rigidity.polynomialAction H
        (polynomialVector a κ H A v k) i +
      (∑ b, Rigidity.cofactor a b * ADComplete.Rigidity.polynomialAction (A b)
        (polynomialVector a κ H A v k) i) -
      C ((k : ℝ) * κ) * (Rigidity.denom a).derivative * polynomialVector a κ H A v k i

def rationalKrylov (a : τ → ℝ) (κ : ℝ) (H : Matrix ι ι ℝ)
    (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) : ι → RF :=
  ADComplete.DifferentialKrylov.vector ADComplete.RationalDerivative.derivative
    (Rigidity.rationalConnection a (fun b => κ⁻¹ • A b) H)
    (ADComplete.ConstantFrame.embed v) k

theorem polynomialVector_connection_step (a : τ → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) (i : ι) :
    algebraMap ℝ[X] RF (polynomialVector a κ H A v (k+1) i) =
      (algebraMap ℝ RF κ * algebraMap ℝ[X] RF (Rigidity.denom a)) *
        ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
          (Rigidity.rationalConnection a (fun b => κ⁻¹ • A b) H)
          (fun j => algebraMap ℝ[X] RF (polynomialVector a κ H A v k j)) i -
      (k : RF) * algebraMap ℝ RF κ *
        algebraMap ℝ[X] RF (Rigidity.denom a).derivative *
        algebraMap ℝ[X] RF (polynomialVector a κ H A v k i) := by
  classical
  let p := polynomialVector a κ H A v k
  have hs := Rigidity.scaled_polynomial_connection a (fun b => κ⁻¹ • A b) H p i
  have hs' := congrArg (fun z : RF => algebraMap ℝ RF κ * z) hs
  have hκF : algebraMap ℝ RF κ ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  have hsum : algebraMap ℝ RF κ *
      (∑ b, algebraMap ℝ[X] RF (Rigidity.cofactor a b) *
        algebraMap ℝ[X] RF (ADComplete.Rigidity.polynomialAction (κ⁻¹ • A b) p i)) =
      ∑ b, algebraMap ℝ[X] RF (Rigidity.cofactor a b) *
        algebraMap ℝ[X] RF (ADComplete.Rigidity.polynomialAction (A b) p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [ADComplete.Spanning.polynomialAction_smul, map_mul,
      ADComplete.Spanning.rational_map_C, map_inv₀]
    calc
      _ = (algebraMap ℝ RF κ * (algebraMap ℝ RF κ)⁻¹) *
          (algebraMap ℝ[X] RF (Rigidity.cofactor a b) *
            algebraMap ℝ[X] RF (ADComplete.Rigidity.polynomialAction (A b) p i)) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ hκF,one_mul]
  simp only [map_add, map_mul, map_sum, mul_add] at hs'
  rw [hsum] at hs'
  change algebraMap ℝ[X] RF
    (C κ * Rigidity.denom a * (p i).derivative +
      C κ * Rigidity.denom a * ADComplete.Rigidity.polynomialAction H p i +
      (∑ b, Rigidity.cofactor a b * ADComplete.Rigidity.polynomialAction (A b) p i) -
      C ((k : ℝ)*κ) * (Rigidity.denom a).derivative * p i) = _
  simp only [map_sub, map_add, map_mul, map_sum,
    ADComplete.Spanning.rational_map_C, map_natCast]
  change _ = (algebraMap ℝ RF κ * algebraMap ℝ[X] RF (Rigidity.denom a)) *
    ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
      (Rigidity.rationalConnection a (fun b => κ⁻¹ • A b) H)
      (fun j => algebraMap ℝ[X] RF (p j)) i - _
  unfold ADComplete.DifferentialKrylov.connection
  linear_combination hs'

theorem polynomialVector_rationalKrylov (a : τ → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) :
    (fun i => algebraMap ℝ[X] RF (polynomialVector a κ H A v k i)) =
      (algebraMap ℝ RF κ * algebraMap ℝ[X] RF (Rigidity.denom a)) ^ k •
        rationalKrylov a κ H A v k := by
  induction k with
  | zero =>
      ext i
      simp [polynomialVector, rationalKrylov, ADComplete.DifferentialKrylov.vector,
        ADComplete.ConstantFrame.embed]
  | succ k ih =>
      let b : RF := algebraMap ℝ RF κ * algebraMap ℝ[X] RF (Rigidity.denom a)
      let db : RF := algebraMap ℝ RF κ * algebraMap ℝ[X] RF (Rigidity.denom a).derivative
      have hDb : ADComplete.RationalDerivative.derivative b = db := by
        have hk : ADComplete.RationalDerivative.derivative (algebraMap ℝ RF κ) = 0 :=
          Derivation.map_algebraMap ADComplete.RationalDerivative.derivative κ
        dsimp only [b, db]
        rw [Derivation.leibniz]
        change algebraMap ℝ RF κ * ADComplete.RationalDerivative.derivative
          (algebraMap ℝ[X] RF (Rigidity.denom a)) + algebraMap ℝ[X] RF (Rigidity.denom a) *
          ADComplete.RationalDerivative.derivative (algebraMap ℝ RF κ) = _
        rw [hk,ADComplete.RationalDerivative.derivative_polynomial,mul_zero,add_zero]
      have hpow : ADComplete.RationalDerivative.derivative (b ^ k) * b =
          (k : RF) * db * b ^ k := by
        cases k with
        | zero => simp
        | succ k =>
            rw [Derivation.leibniz_pow, hDb]
            simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul, Nat.cast_succ]
            ring
      ext i
      rw [polynomialVector_connection_step a κ hκ H A v k i, ih,
        ADComplete.DifferentialKrylov.connection_smul]
      have hi := congrArg (fun y : ι → RF => y i) ih
      rw [hi]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hstep : rationalKrylov a κ H A v (k+1) =
          ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
            (Rigidity.rationalConnection a (fun c => κ⁻¹ • A c) H)
            (rationalKrylov a κ H A v k) := ADComplete.DifferentialKrylov.vector_succ _ _ _ _
      rw [hstep]
      change b * (ADComplete.RationalDerivative.derivative (b^k) * _ + b^k * _) -
        (k : RF) * algebraMap ℝ RF κ * algebraMap ℝ[X] RF (Rigidity.denom a).derivative *
          (b^k * _) = b^(k+1) * _
      rw [pow_succ]
      dsimp only [db] at hpow
      linear_combination (rationalKrylov a κ H A v k i) * hpow

#print axioms polynomialVector_rationalKrylov

theorem polynomialVector_natDegree_le (a : τ → ℝ) (κ : ℝ)
    (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) (i : ι) :
    (polynomialVector a κ H A v k i).natDegree ≤ Fintype.card τ * k := by
  classical
  induction k generalizing i with
  | zero => simp [polynomialVector]
  | succ k ih =>
      have ih' (i : ι) : (polynomialVector a κ H A v k i).natDegree ≤ Fintype.card τ * k := by
        exact ih i
      have hd : (Rigidity.denom a).natDegree ≤ Fintype.card τ :=
        le_of_eq (Rigidity.denom_natDegree a)
      have hq (b : τ) : (Rigidity.cofactor a b).natDegree ≤ Fintype.card τ := by
        rw [Rigidity.cofactor_natDegree]
        omega
      have hact (M : Matrix ι ι ℝ) :
          (ADComplete.Rigidity.polynomialAction M (polynomialVector a κ H A v k) i).natDegree ≤
            Fintype.card τ * k := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro j hj
        simpa using Polynomial.natDegree_mul_le_of_le (show (C (M i j)).natDegree ≤ 0 by simp) (ih' j)
      have hp' : (polynomialVector a κ H A v k i).derivative.natDegree ≤ Fintype.card τ*k :=
        (Polynomial.natDegree_derivative_le _).trans (by have := ih i; omega)
      have hd' : (Rigidity.denom a).derivative.natDegree ≤ Fintype.card τ :=
        (Polynomial.natDegree_derivative_le _).trans (by omega)
      have hC (c : ℝ) : (C c).natDegree ≤ 0 := by simp
      rw [polynomialVector]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · apply Polynomial.natDegree_add_le_of_degree_le
        · apply Polynomial.natDegree_add_le_of_degree_le
          · simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_succ, Nat.add_comm] using Polynomial.natDegree_mul_le_of_le
              (Polynomial.natDegree_mul_le_of_le (hC κ) hd) hp'
          · simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_succ, Nat.add_comm] using Polynomial.natDegree_mul_le_of_le
              (Polynomial.natDegree_mul_le_of_le (hC κ) hd) (hact H)
        · apply Polynomial.natDegree_sum_le_of_forall_le
          intro b hb
          simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_succ, Nat.add_comm] using Polynomial.natDegree_mul_le_of_le (hq b) (hact (A b))
      · simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_succ, Nat.add_comm] using Polynomial.natDegree_mul_le_of_le
          (Polynomial.natDegree_mul_le_of_le (hC ((k : ℝ)*κ)) hd') (ih i)

theorem polynomialVector_coeff_outside (a : τ → ℝ) (κ : ℝ)
    (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k j : ℕ)
    (hj : Fintype.card τ * k < j) (i : ι) :
    (polynomialVector a κ H A v k i).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((polynomialVector_natDegree_le a κ H A v k i).trans_lt hj)

end
end MultiSymmetric.Krylov
