import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Free
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! Exact radix factoring in an arbitrary, possibly noncommutative ring.
The only scalars used below are integers, acting by repeated addition. -/

namespace CircuitAudit.RadixFactorization

open scoped BigOperators

variable {R : Type*} [Ring R]

def weightedSum {K : ℕ} (b : ℤ) (w : Fin K → ℕ) (X : Fin K → R) : R :=
  ∑ i, b ^ w i • X i

theorem weighted_mul (b : ℤ) (u v : ℕ) (x y : R) :
    (b ^ u • x) * (b ^ v • y) = b ^ (u + v) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]

theorem weighted_triple_factorization {I K J : ℕ} (b : ℤ)
    (u : Fin I → ℕ) (v : Fin K → ℕ) (w : Fin J → ℕ)
    (X : Fin I → R) (S : Fin K → R) (Y : Fin J → R) :
    (∑ s, ∑ i, ∑ j, b ^ (u i + v s + w j) • ((X i * S s) * Y j)) =
      (weightedSum b u X * weightedSum b v S) * weightedSum b w Y := by
  unfold weightedSum
  rw [Finset.sum_comm]
  symm
  rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum, ← mul_assoc, weighted_mul]

variable [StarRing R]

theorem star_weightedSum {K : ℕ} (b : ℤ) (w : Fin K → ℕ) (X : Fin K → R) :
    star (weightedSum b w X) = weightedSum b w (fun i => star (X i)) := by
  simp only [weightedSum, star_sum, star_zsmul]

def tablePolynomial {M : ℕ} (b : ℤ) (J : R) (U : Fin M → R) (S : Fin 3 → R) : R :=
  ∑ s, ∑ i, ∑ j, b ^ (s.val * M ^ 2 + i.val * M + j.val) •
    (((J * star (U i)) * S s) * U j + ((star (U j) * S s) * U i) * star J)

/-- The manuscript's literal `J X + X* J*` summands. -/
def sourcePolynomial {M : ℕ} (b : ℤ) (J : R) (U : Fin M → R) (S : Fin 3 → R) : R :=
  ∑ s, ∑ i, ∑ j, b ^ (s.val * M ^ 2 + i.val * M + j.val) •
    (J * ((star (U i) * S s) * U j) +
      star ((star (U i) * S s) * U j) * star J)

theorem sourcePolynomial_eq_tablePolynomial {M : ℕ} (b : ℤ) (J : R)
    (U : Fin M → R) (S : Fin 3 → R) (hS : ∀ s, star (S s) = S s) :
    sourcePolynomial b J U S = tablePolynomial b J U S := by
  simp only [sourcePolynomial, tablePolynomial, star_mul, star_star, hS, mul_assoc]

def packedPolynomial {M : ℕ} (b : ℤ) (J : R) (U : Fin M → R) (S : Fin 3 → R) : R :=
  let Y := weightedSum b (fun j : Fin M => j.val) U
  let Z := weightedSum b (fun i : Fin M => i.val * M) U
  let P := weightedSum b (fun s : Fin 3 => s.val * M ^ 2) S
  ((J * star Z) * P) * Y + ((star Y * P) * Z) * star J

theorem exact_table_factorization {M : ℕ} (b : ℤ) (J : R)
    (U : Fin M → R) (S : Fin 3 → R) :
    tablePolynomial b J U S = packedPolynomial b J U S := by
  have hleft :
      (∑ s : Fin 3, ∑ i : Fin M, ∑ j : Fin M,
        b ^ (s.val * M ^ 2 + i.val * M + j.val) • ((star (U i) * S s) * U j)) =
      (weightedSum b (fun i : Fin M => i.val * M) (fun i => star (U i)) *
        weightedSum b (fun s : Fin 3 => s.val * M ^ 2) S) *
          weightedSum b (fun j : Fin M => j.val) U := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      weighted_triple_factorization b
        (fun i : Fin M => i.val * M) (fun s : Fin 3 => s.val * M ^ 2)
        (fun j : Fin M => j.val) (fun i => star (U i)) S U
  have hright :
      (∑ s : Fin 3, ∑ i : Fin M, ∑ j : Fin M,
        b ^ (s.val * M ^ 2 + i.val * M + j.val) • ((star (U j) * S s) * U i)) =
      (weightedSum b (fun j : Fin M => j.val) (fun j => star (U j)) *
        weightedSum b (fun s : Fin 3 => s.val * M ^ 2) S) *
          weightedSum b (fun i : Fin M => i.val * M) U := by
    calc
      _ = ∑ s : Fin 3, ∑ j : Fin M, ∑ i : Fin M,
          b ^ (s.val * M ^ 2 + i.val * M + j.val) • ((star (U j) * S s) * U i) := by
        apply Finset.sum_congr rfl
        intro s _
        exact Finset.sum_comm
      _ = _ := by
        simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          weighted_triple_factorization b
            (fun j : Fin M => j.val) (fun s : Fin 3 => s.val * M ^ 2)
            (fun i : Fin M => i.val * M) (fun j => star (U j)) S U
  unfold tablePolynomial packedPolynomial
  calc
    _ = J * (∑ s : Fin 3, ∑ i : Fin M, ∑ j : Fin M,
          b ^ (s.val * M ^ 2 + i.val * M + j.val) • ((star (U i) * S s) * U j)) +
        (∑ s : Fin 3, ∑ i : Fin M, ∑ j : Fin M,
          b ^ (s.val * M ^ 2 + i.val * M + j.val) • ((star (U j) * S s) * U i)) *
            star J := by
      simp only [smul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
        mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
      rw [hleft, hright]
      simp only [star_weightedSum, mul_assoc]

def coreSlots (a d : R) : Fin 3 → R := ![1, a, d]

omit [StarRing R] in
theorem weighted_coreSlots (b : ℤ) (M : ℕ) (a d : R) :
    weightedSum b (fun s : Fin 3 => s.val * M ^ 2) (coreSlots a d) =
      1 + b ^ (M ^ 2) • a + b ^ (2 * M ^ 2) • d := by
  simp [weightedSum, coreSlots, Fin.sum_univ_succ, add_assoc]

/-- The expanded table formula, with the three literal slots `1`, `a`, and `d`.
The source-to-table bridge separately requires self-adjoint slots. -/
theorem exact_three_slot_factorization {M : ℕ} (b : ℤ) (J : R)
    (U : Fin M → R) (a d : R) :
    tablePolynomial b J U (coreSlots a d) =
      let Y := weightedSum b (fun j : Fin M => j.val) U
      let Z := weightedSum b (fun i : Fin M => i.val * M) U
      let P := 1 + b ^ (M ^ 2) • a + b ^ (2 * M ^ 2) • d
      ((J * star Z) * P) * Y + ((star Y * P) * Z) * star J := by
  rw [exact_table_factorization]
  simp only [packedPolynomial, weighted_coreSlots]

/-- Integer polynomials in two noncommuting letters, with word reversal as star. -/
abbrev IntegerNCPolynomial := FreeAlgebra ℤ Bool

def adjacencyGenerator : IntegerNCPolynomial := FreeAlgebra.ι ℤ false

def degreeGenerator : IntegerNCPolynomial := FreeAlgebra.ι ℤ true

theorem coreSlots_self_adjoint (a d : R) (ha : star a = a) (hd : star d = d) :
    ∀ s, star (coreSlots a d s) = coreSlots a d s := by
  simp [coreSlots, Fin.forall_fin_succ, ha, hd]

/-- The original manuscript formula equals its compressed form for arbitrary
noncommuting inputs; only the literal slots `a` and `d` are self-adjoint. -/
theorem exact_source_factorization {M : ℕ} (b : ℤ) (J : R)
    (U : Fin M → R) (a d : R) (ha : star a = a) (hd : star d = d) :
    sourcePolynomial b J U (coreSlots a d) =
      let Y := weightedSum b (fun j : Fin M => j.val) U
      let Z := weightedSum b (fun i : Fin M => i.val * M) U
      let P := 1 + b ^ (M ^ 2) • a + b ^ (2 * M ^ 2) • d
      ((J * star Z) * P) * Y + ((star Y * P) * Z) * star J := by
  rw [sourcePolynomial_eq_tablePolynomial b J U _ (coreSlots_self_adjoint a d ha hd)]
  exact exact_three_slot_factorization b J U a d

theorem adjacencyGenerator_self_adjoint : star adjacencyGenerator = adjacencyGenerator := by
  simp [adjacencyGenerator]

theorem degreeGenerator_self_adjoint : star degreeGenerator = degreeGenerator := by
  simp [degreeGenerator]

/-- Literal integer noncommutative-polynomial equality, independent of any
chosen graph or matrix dimension. -/
theorem integer_polynomial_exact_factorization {M : ℕ} (b : ℤ)
    (J : IntegerNCPolynomial) (U : Fin M → IntegerNCPolynomial) :
    sourcePolynomial b J U (coreSlots adjacencyGenerator degreeGenerator) =
      let Y := weightedSum b (fun j : Fin M => j.val) U
      let Z := weightedSum b (fun i : Fin M => i.val * M) U
      let P := 1 + b ^ (M ^ 2) • adjacencyGenerator + b ^ (2 * M ^ 2) • degreeGenerator
      ((J * star Z) * P) * Y + ((star Y * P) * Z) * star J := by
  rw [sourcePolynomial_eq_tablePolynomial b J U _
    (coreSlots_self_adjoint _ _ adjacencyGenerator_self_adjoint degreeGenerator_self_adjoint)]
  exact exact_three_slot_factorization b J U adjacencyGenerator degreeGenerator

#print axioms integer_polynomial_exact_factorization

end CircuitAudit.RadixFactorization
