import PaperVerifier.CircuitAudit.RadixFactorization
import Mathlib.Data.List.OfFn

namespace CircuitAudit.HornerBridge

open scoped BigOperators

open RadixFactorization

variable {R : Type*} [Ring R]

/-- Sequential Horner evaluation, using the central integer scalar `b`. -/
def horner (b : ℤ) : List R → R
  | [] => 0
  | x :: xs => x + b • horner b xs

theorem horner_eq_foldr (b : ℤ) (xs : List R) :
    horner b xs = xs.foldr (fun p r => p + (b : R) * r) 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [horner, List.foldr_cons, ih, zsmul_eq_mul]

theorem weightedSum_succ {M : ℕ} (b : ℤ) (U : Fin (M + 1) → R) :
    weightedSum b (fun i : Fin (M + 1) => i.val) U =
      U 0 + b • weightedSum b (fun i : Fin M => i.val) (fun i => U i.succ) := by
  simp [weightedSum, Fin.sum_univ_succ, pow_succ', Finset.mul_sum, mul_assoc]

/-- The literal finite-index weights are exactly a sequential Horner fold. -/
theorem horner_ofFn {M : ℕ} (b : ℤ) (U : Fin M → R) :
    horner b (List.ofFn U) = weightedSum b (fun i : Fin M => i.val) U := by
  induction M with
  | zero => simp [horner, weightedSum]
  | succ M ih =>
    rw [List.ofFn_succ, horner, ih, weightedSum_succ]

/-- With stride `b^M`, the weights are exactly `b^(i*M)`; no numerical
power is supplied as an extra input to the algebraic identity. -/
theorem horner_ofFn_stride {M : ℕ} (b : ℤ) (U : Fin M → R) :
    horner (b ^ M) (List.ofFn U) = weightedSum b (fun i : Fin M => i.val * M) U := by
  rw [horner_ofFn]
  simp only [weightedSum, ← pow_mul, Nat.mul_comm]

theorem horner_list (b : ℤ) (xs : List R) :
    horner b xs = weightedSum b (fun i : Fin xs.length => i.val) xs.get := by
  simpa only [List.ofFn_get] using horner_ofFn b xs.get

/-- The direct list form allows a stride independent of the list length. -/
theorem horner_list_stride (b : ℤ) (stride : ℕ) (xs : List R) :
    horner (b ^ stride) xs =
      weightedSum b (fun i : Fin xs.length => i.val * stride) xs.get := by
  simpa only [List.ofFn_get, weightedSum, ← pow_mul, Nat.mul_comm] using
    horner_ofFn (b ^ stride) xs.get

#print axioms horner_ofFn_stride

end CircuitAudit.HornerBridge
