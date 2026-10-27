import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-! Literal universal integer recurrence for the multipole candidate.
No spanning assertion is assumed or encoded in these definitions. -/
namespace MultiSymmetric.Recurrence
open scoped BigOperators
open Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def poleProduct (s : ℕ) : ℤ[X] :=
  ∏ i : Fin s, (X - C (i.val : ℤ))

def poleQuotient (s : ℕ) (i : Fin s) : ℤ[X] :=
  ∏ j ∈ (Finset.univ.erase i), (X - C (j.val : ℤ))

theorem pole_factor (s : ℕ) (i : Fin s) :
    (X - C (i.val : ℤ)) * poleQuotient s i = poleProduct s := by
  classical
  unfold poleQuotient poleProduct
  exact Finset.mul_prod_erase Finset.univ (fun j : Fin s => X - C (j.val : ℤ))
    (Finset.mem_univ i)

theorem poleProduct_natDegree (s : ℕ) : (poleProduct s).natDegree = s := by
  classical
  simpa [poleProduct] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card (Finset.univ : Finset (Fin s))
      (fun i : Fin s => (i.val : ℤ)))

theorem poleQuotient_natDegree_le (s : ℕ) (i : Fin s) :
    (poleQuotient s i).natDegree ≤ s := by
  classical
  have h := Polynomial.natDegree_finsetProd_X_sub_C_eq_card
    ((Finset.univ : Finset (Fin s)).erase i) (fun j : Fin s => (j.val : ℤ))
  simp only [poleQuotient, h, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]
  omega

variable {R : Type*} [Ring R]

def scalarPolynomial (p : ℤ[X]) : R[X] := p.map (Int.castRingHom R)

def step (s : ℕ) (κ : ℤ) (H : R) (A : Fin s → R) (k : ℕ) (p : R[X]) : R[X] :=
  C (κ : R) * scalarPolynomial (poleProduct s) * p.derivative +
  C (κ : R) * scalarPolynomial (poleProduct s) * C H * p +
  (∑ i : Fin s, scalarPolynomial (poleQuotient s i) * C (A i) * p) -
  C (((k : ℤ) * κ : ℤ) : R) * (scalarPolynomial (poleProduct s)).derivative * p

def row (s : ℕ) (κ : ℤ) (H : R) (A : Fin s → R) : ℕ → R[X]
  | 0 => 1
  | k + 1 => step s κ H A k (row s κ H A k)

@[simp] theorem row_zero (s : ℕ) (κ : ℤ) (H : R) (A : Fin s → R) :
    row s κ H A 0 = 1 := rfl

theorem row_succ (s : ℕ) (κ : ℤ) (H : R) (A : Fin s → R) (k : ℕ) :
    row s κ H A (k + 1) = step s κ H A k (row s κ H A k) := rfl

theorem scalarPolynomial_natDegree_le (p : ℤ[X]) :
    (scalarPolynomial (R := R) p).natDegree ≤ p.natDegree :=
  Polynomial.natDegree_map_le

theorem row_natDegree_le (s : ℕ) (κ : ℤ) (H : R) (A : Fin s → R) (k : ℕ) :
    (row s κ H A k).natDegree ≤ s * k := by
  induction k with
  | zero => simp [row]
  | succ k ih =>
      have hd : (scalarPolynomial (R := R) (poleProduct s)).natDegree ≤ s := by
        exact (scalarPolynomial_natDegree_le _).trans (le_of_eq (poleProduct_natDegree s))
      have hq (i : Fin s) :
          (scalarPolynomial (R := R) (poleQuotient s i)).natDegree ≤ s :=
        (scalarPolynomial_natDegree_le _).trans (poleQuotient_natDegree_le s i)
      have hp' : (row s κ H A k).derivative.natDegree ≤ s * k :=
        (Polynomial.natDegree_derivative_le _).trans (by omega)
      have hd' : (scalarPolynomial (R := R) (poleProduct s)).derivative.natDegree ≤ s :=
        (Polynomial.natDegree_derivative_le _).trans (by omega)
      have hconst (c : R) : (C c).natDegree ≤ 0 := by simp
      rw [row_succ, step]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · apply Polynomial.natDegree_add_le_of_degree_le
        · apply Polynomial.natDegree_add_le_of_degree_le
          · have hh := Polynomial.natDegree_mul_le_of_le
              (Polynomial.natDegree_mul_le_of_le (hconst (κ : R)) hd) hp'
            simpa [Nat.mul_succ, Nat.add_comm] using hh
          · have hh := Polynomial.natDegree_mul_le_of_le
              (Polynomial.natDegree_mul_le_of_le
                (Polynomial.natDegree_mul_le_of_le (hconst (κ : R)) hd) (hconst H)) ih
            simpa [Nat.mul_succ, Nat.add_comm] using hh
        · apply Polynomial.natDegree_sum_le_of_forall_le
          intro i hi
          have hh := Polynomial.natDegree_mul_le_of_le
            (Polynomial.natDegree_mul_le_of_le (hq i) (hconst (A i))) ih
          simpa [Nat.mul_succ, Nat.add_comm] using hh
      · have hh := Polynomial.natDegree_mul_le_of_le
          (Polynomial.natDegree_mul_le_of_le (hconst (((k : ℤ) * κ : ℤ) : R)) hd') ih
        simpa [Nat.mul_succ, Nat.add_comm] using hh

theorem row_coeff_outside (s : ℕ) (κ : ℤ) (H : R) (A : Fin s → R)
    (k j : ℕ) (hj : s * k < j) : (row s κ H A k).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((row_natDegree_le s κ H A k).trans_lt hj)

abbrev Index (s N : ℕ) := (k : Fin N) × Fin (s * k.val + 1)

theorem twice_index_card (s N : ℕ) :
    2 * Fintype.card (Index s N) = 2 * N + s * N * (N - 1) := by
  classical
  have hsum : ∀ n : ℕ, 2 * (∑ k ∈ Finset.range n, (s * k + 1)) =
      2 * n + s * n * (n - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      cases n with
      | zero => simp
      | succ n =>
          simp only [Nat.add_sub_cancel] at *
          nlinarith
  simp only [Index, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun k => s * k + 1)]
  exact hsum N

theorem index_card (s N : ℕ) :
    Fintype.card (Index s N) = N + s * N * (N - 1) / 2 := by
  have h := twice_index_card s N
  omega

abbrev NC (s : ℕ) := FreeAlgebra ℤ (Fin (s + 1))

def generator (s : ℕ) (i : Fin (s + 1)) : NC s := FreeAlgebra.ι ℤ i

def universalRow (s N : ℕ) (k : ℕ) : (NC s)[X] :=
  row s ((s : ℤ) * (N : ℤ)^2) (generator s 0) (fun i => generator s i.succ) k

def probe (s N : ℕ) (i : Index s N) : NC s :=
  (universalRow s N i.1.val).coeff i.2.val

variable {S : Type*} [Ring S]

theorem scalarPolynomial_map (f : R →+* S) (p : ℤ[X]) :
    (scalarPolynomial (R := R) p).map f = scalarPolynomial (R := S) p := by
  ext j
  simp [scalarPolynomial]

theorem row_map (f : R →+* S) (s : ℕ) (κ : ℤ) (H : R) (A : Fin s → R) (k : ℕ) :
    (row s κ H A k).map f = row s κ (f H) (fun i => f (A i)) k := by
  induction k with
  | zero => simp [row]
  | succ k ih =>
      simp only [row_succ, step, Polynomial.map_add, Polynomial.map_sub,
        Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_C, map_intCast,
        ← Polynomial.derivative_map, scalarPolynomial_map, ih,
        Polynomial.map_intCast]

theorem universalRow_evaluate [Algebra ℤ R] (s N k : ℕ) (Xv : Fin (s + 1) → R) :
    (universalRow s N k).map (FreeAlgebra.lift ℤ Xv).toRingHom =
      row s ((s : ℤ) * (N : ℤ)^2) (Xv 0) (fun i => Xv i.succ) k := by
  simpa [universalRow, generator] using
    row_map (FreeAlgebra.lift ℤ Xv).toRingHom s ((s : ℤ) * (N : ℤ)^2)
      (generator s 0) (fun i => generator s i.succ) k

#print axioms row_natDegree_le
#print axioms index_card
end
end MultiSymmetric.Recurrence
