import MultiSymmetric.CircuitRow
import MultiSymmetric.CircuitScalars
set_option autoImplicit false

/-! The complete fixed shared circuit retains every row; output extraction is
free wiring from the stored coefficient registers. -/
namespace MultiSymmetric.Circuit
open Polynomial
noncomputable section
variable {R : Type*} [Ring R]

structure FamilyRun (R : Type*) [Ring R] where
  current : R[X]
  rows : List R[X]
  gates : ℕ
  usedScalars : Finset ℤ

def familyRun (s : ℕ) (κ : ℤ) (gen : Fin (s+1) → R) : ℕ → FamilyRun R
  | 0 => ⟨1,[1],2,{0,1}⟩
  | k+1 =>
      let previous := familyRun s κ gen k
      let next := rowRun s κ gen k previous.current
      ⟨next.value, next.value :: previous.rows, previous.gates+next.gates,
        previous.usedScalars ∪ next.usedScalars⟩

theorem familyRun_semantics (s : ℕ) (hs : 0<s) (κ : ℤ) (gen : Fin (s+1) → R)
    (k : ℕ) : (familyRun s κ gen k).current =
      Recurrence.row s κ (gen 0) (fun i => gen i.succ) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (rowRun s κ gen k (familyRun s κ gen k).current).value = _
      rw [ih, rowRun_semantics s hs κ gen k _ (Recurrence.row_natDegree_le _ _ _ _ _)]
      rfl

theorem familyRun_cost (s : ℕ) (κ : ℤ) (gen : Fin (s+1) → R) (k : ℕ) :
    (familyRun s κ gen k).gates ≤ 2+30*(s+1)^2*k*(k+1) := by
  induction k with
  | zero => simp [familyRun]
  | succ k ih =>
      have hnext := rowRun_cost s κ gen k (familyRun s κ gen k).current
      change (familyRun s κ gen k).gates +
        (rowRun s κ gen k (familyRun s κ gen k).current).gates ≤ _
      nlinarith [Nat.zero_le (30*(s+1)^2*(k+1))]

theorem familyRun_rows_length (s : ℕ) (κ : ℤ) (gen : Fin (s+1) → R) (k : ℕ) :
    (familyRun s κ gen k).rows.length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [familyRun, ih]

theorem familyRun_rows_getD (s : ℕ) (κ : ℤ) (gen : Fin (s+1) → R)
    (k j : ℕ) (hj : j≤k) :
    (familyRun s κ gen k).rows.getD j 0 = (familyRun s κ gen (k-j)).current := by
  induction k generalizing j with
  | zero =>
      have : j=0 := by omega
      subst j
      simp [familyRun]
  | succ k ih =>
      cases j with
      | zero => simp [familyRun]
      | succ j => simpa [familyRun] using ih j (by omega)

theorem familyRun_scalars_bound (s N : ℕ) (gen : Fin (s+1) → R)
    (k : ℕ) (hk : k<N) (c : ℤ)
    (hc : c ∈ (familyRun s ((s:ℤ)*(N:ℤ)^2) gen k).usedScalars) :
    c.natAbs≤constantBudget s N := by
  induction k generalizing c with
  | zero =>
      have hc' : c=0 ∨ c=1 := by simpa [familyRun] using hc
      rcases hc' with rfl | rfl
      · simp
      · have h := linear_le_budget s N
        simp only [Int.natAbs_one]
        omega
  | succ k ih =>
      change c ∈ (familyRun s ((s:ℤ)*(N:ℤ)^2) gen k).usedScalars ∪
        (rowRun s ((s:ℤ)*(N:ℤ)^2) gen k
          (familyRun s ((s:ℤ)*(N:ℤ)^2) gen k).current).usedScalars at hc
      rcases Finset.mem_union.mp hc with hp | hn
      · exact ih (by omega) c hp
      · exact rowRun_scalars_bound s N k (by omega) gen _ c hn

theorem complete_family_circuit (s N : ℕ) (hs : 0<s) (hN : 0<N)
    (gen : Fin (s+1) → R) :
    let run := familyRun s ((s:ℤ)*(N:ℤ)^2) gen (N-1)
    run.gates+(s+1) ≤ s+3+30*(s+1)^2*N^2 ∧ run.rows.length=N ∧
      (∀ i : Recurrence.Index s N,
        (run.rows.getD (N-1-i.1.val) 0).coeff i.2.val =
          (Recurrence.row s ((s:ℤ)*(N:ℤ)^2) (gen 0)
            (fun j => gen j.succ) i.1.val).coeff i.2.val) ∧
      ∀ c ∈ run.usedScalars, c.natAbs.size+1≤3+(s+1).size+3*(N+1).size := by
  dsimp only
  have hN' : 1≤N := hN
  have htop := familyRun_cost s ((s:ℤ)*(N:ℤ)^2) gen (N-1)
  rw [Nat.sub_add_cancel hN'] at htop
  constructor
  · have hg : (familyRun s ((s:ℤ)*(N:ℤ)^2) gen (N-1)).gates ≤
        2+30*(s+1)^2*N^2 := by
      calc
        _ ≤ 2+30*(s+1)^2*(N-1)*N := htop
        _ ≤ 2+30*(s+1)^2*N*N := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_right N (Nat.mul_le_mul_left _ (Nat.sub_le N 1))) 2
        _ = _ := by ring
    omega
  constructor
  · rw [familyRun_rows_length, Nat.sub_add_cancel hN']
  constructor
  · intro i
    rw [familyRun_rows_getD _ _ _ _ _ (Nat.sub_le _ _)]
    have hn : N-1-(N-1-i.1.val)=i.1.val := by omega
    rw [hn, familyRun_semantics s hs]
  · intro c hc
    exact scalar_bit_bound s N c
      (familyRun_scalars_bound s N gen (N-1) (by omega) c hc)

#print axioms complete_family_circuit
#print axioms familyRun_scalars_bound
end
end MultiSymmetric.Circuit
