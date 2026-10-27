import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.Linarith
set_option autoImplicit false

/-! A literal shared Horner scan for division by a monic linear polynomial.
The scan stores every previously obtained coefficient; its two arithmetic
instructions per step are multiplication by the prescribed scalar and addition.
No division is executed. The semantic theorem is over arbitrary rings. -/
namespace MultiSymmetric.Circuit
open Polynomial
noncomputable section
variable {R : Type*} [Ring R]

structure ScanState (R : Type*) where
  current : R
  history : List R
  gates : ℕ

def syntheticScan (a : R) (g : ℕ → R) (d : ℕ) : ℕ → ScanState R
  | 0 => ⟨0, [0], 1⟩
  | r + 1 =>
    let previous := syntheticScan a g d r
    let next := g (d-r) + a * previous.current
    ⟨next, next :: previous.history, previous.gates + 2⟩

@[simp] theorem syntheticScan_gates (a : R) (g : ℕ → R) (d r : ℕ) :
    (syntheticScan a g d r).gates = 2*r+1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [syntheticScan, ih]; omega

@[simp] theorem syntheticScan_history_length (a : R) (g : ℕ → R) (d r : ℕ) :
    (syntheticScan a g d r).history.length = r+1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [syntheticScan, List.length_cons, ih]

theorem syntheticScan_retains (a : R) (g : ℕ → R) (d r k : ℕ) (hk : k≤r) :
    (syntheticScan a g d k).current ∈ (syntheticScan a g d r).history := by
  induction r with
  | zero =>
      have : k=0 := by omega
      subst k
      simp [syntheticScan]
  | succ r ih =>
    by_cases hkr : k=r+1
    · subst k; simp [syntheticScan]
    · exact List.mem_cons_of_mem _ (ih (by omega))

theorem syntheticScan_history_getD (a : R) (g : ℕ → R) (d r j : ℕ) (hj : j≤r) :
    (syntheticScan a g d r).history.getD j 0 =
      (syntheticScan a g d (r-j)).current := by
  induction r generalizing j with
  | zero =>
      have : j=0 := by omega
      subst j
      simp [syntheticScan]
  | succ r ih =>
      cases j with
      | zero => simp [syntheticScan]
      | succ j => simpa [syntheticScan] using ih j (by omega)

theorem factor_coeff_succ (a : R) (q : R[X]) (j : ℕ) :
    ((X-C a)*q).coeff (j+1) = q.coeff j - a*q.coeff (j+1) := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]

/-- Every stored Horner output is the corresponding coefficient of the exact
quotient, proved from the supplied dividend identity and degree bound. -/
theorem syntheticScan_correct (a : R) (q : R[X]) (d : ℕ)
    (hq : q.natDegree < d) (r : ℕ) (hr : r≤d) :
    (syntheticScan a (((X-C a)*q).coeff) d r).current = q.coeff (d-r) := by
  induction r with
  | zero =>
      simp only [syntheticScan, Nat.sub_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt hq).symm
  | succ r ih =>
      have hrd : r<d := by omega
      have hi := ih (by omega)
      have hn : d-r=(d-(r+1))+1 := by omega
      simp only [syntheticScan]
      rw [hi, hn, factor_coeff_succ]
      exact sub_add_cancel _ _

theorem syntheticScan_all_coefficients (a : R) (q : R[X]) (d : ℕ)
    (hq : q.natDegree<d) (j : ℕ) (hj : j<d) :
    q.coeff j ∈ (syntheticScan a (((X-C a)*q).coeff) d d).history := by
  have hr : d-j≤d := Nat.sub_le _ _
  have hcorrect := syntheticScan_correct a q d hq (d-j) hr
  have hn : d-(d-j)=j := by omega
  rw [hn] at hcorrect
  rw [← hcorrect]
  exact syntheticScan_retains a _ d d (d-j) hr

#print axioms syntheticScan_correct
#print axioms syntheticScan_all_coefficients
end
end MultiSymmetric.Circuit
