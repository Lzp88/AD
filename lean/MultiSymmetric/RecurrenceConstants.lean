import MultiSymmetric.CircuitMerge
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Size
set_option autoImplicit false

namespace MultiSymmetric.Circuit
open scoped BigOperators
noncomputable section

theorem factorStage_scalar {σ : Type*} (a : ℤ) (b : ℕ) (c : ℤ)
    (hc : c ∈ (factorStage σ a b).usedScalars) : c = 0 ∨ c = -a := by
  obtain ⟨j, hj, hc⟩ := Finset.mem_biUnion.mp hc
  by_cases hz : j = 0
  · simpa [factorStage, CoeffExpr.usedScalars, hz] using hc
  · exact Or.inr (by simpa [factorStage, CoeffExpr.usedScalars, hz] using hc)

theorem derivativeStage_scalar {σ : Type*} (b : ℕ) (c : ℤ)
    (hc : c ∈ (derivativeStage σ b).usedScalars) :
    ∃ j ≤ b, c = (j+1 : ℤ) := by
  obtain ⟨j, hj, hc⟩ := Finset.mem_biUnion.mp hc
  refine ⟨j, ?_, ?_⟩
  · simpa [derivativeStage] using (Finset.mem_range.mp hj)
  · simpa [derivativeStage, CoeffExpr.usedScalars] using hc

theorem generatorStage_scalars {σ : Type*} (g : σ) (b : ℕ) :
    (generatorStage σ g b).usedScalars = ∅ := by
  ext c
  simp [Stage.usedScalars, generatorStage, CoeffExpr.usedScalars]

theorem sumReferences_scalar {ι σ : Type*} (xs : List ι) :
    (sumReferences (σ := σ) xs).usedScalars = {0} := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [sumReferences, CoeffExpr.usedScalars] using ih

theorem mergeStage_scalar (s d k : ℕ) (κ c : ℤ)
    (hc : c ∈ (mergeStage s d k κ).usedScalars) :
    c = 0 ∨ c = κ * (k+1) ∨ c = κ ∨ c = -((k : ℤ)*κ) := by
  obtain ⟨j, hj, hc⟩ := Finset.mem_biUnion.mp hc
  simp only [mergeStage, CoeffExpr.usedScalars, sumReferences_scalar,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    or_false] at hc
  tauto

def constantBudget (s N : ℕ) : ℕ := 2*(s+1)*(N+1)^3

theorem constantBudget_large (s N : ℕ) :
    (s+1)*(N+1)^3 ≤ constantBudget s N := by
  unfold constantBudget
  rw [Nat.mul_assoc]
  omega

theorem cubic_le_budget (s N : ℕ) : s*N^3 ≤ constantBudget s N := by
  have hh : s*N^3 ≤ (s+1)*(N+1)^3 :=
    Nat.mul_le_mul (Nat.le_succ s) (Nat.pow_le_pow_left (Nat.le_succ N) 3)
  exact hh.trans (constantBudget_large s N)

theorem quadratic_le_budget (s N : ℕ) : s*N^2 ≤ constantBudget s N := by
  have hp : N^2 ≤ (N+1)^3 :=
    (Nat.pow_le_pow_left (Nat.le_succ N) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_pos N) (by omega : 2 ≤ 3))
  exact (Nat.mul_le_mul (Nat.le_succ s) hp).trans (constantBudget_large s N)

theorem linear_le_budget (s N : ℕ) : s*(N+1)+1 ≤ constantBudget s N := by
  have hp : N+1 ≤ (N+1)^3 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos N) (by omega : 1 ≤ 3)
  have hh := Nat.mul_le_mul_left (s+1) hp
  have hm : s*(N+1)+1 ≤ (s+1)*(N+1) := by nlinarith
  exact (hm.trans hh).trans (constantBudget_large s N)

theorem pole_constant_bound (s N i : ℕ) (hi : i < s) :
    ((i : ℤ)).natAbs ≤ constantBudget s N ∧ (-((i : ℤ))).natAbs ≤ constantBudget s N := by
  have hh := linear_le_budget s N
  have hm : i ≤ s*(N+1)+1 := by nlinarith
  simpa using And.intro (hm.trans hh) (hm.trans hh)

theorem derivative_constant_bound (s N k b : ℕ) (hk : k < N)
    (hb : b ≤ s*(k+1)) (c : ℤ)
    (hc : c ∈ (derivativeStage Empty b).usedScalars) :
    c.natAbs ≤ constantBudget s N := by
  obtain ⟨j, hj, rfl⟩ := derivativeStage_scalar b c hc
  have hm : j+1 ≤ s*(N+1)+1 := by nlinarith
  simpa only [← Nat.cast_add_one, Int.natAbs_natCast] using
    hm.trans (linear_le_budget s N)

theorem merge_constant_bound (s N d k : ℕ) (hk : k < N) (c : ℤ)
    (hc : c ∈ (mergeStage s d k ((s : ℤ)*(N : ℤ)^2)).usedScalars) :
    c.natAbs ≤ constantBudget s N := by
  rcases mergeStage_scalar s d k ((s : ℤ)*(N : ℤ)^2) c hc with h | h | h | h
  · subst c; simp
  · subst c
    have hm : s*N^2*(k+1) ≤ s*N^3 := by
      have hmul := Nat.mul_le_mul_left (s*N^2) (show k+1≤N by omega)
      simpa [pow_succ, Nat.mul_assoc] using hmul
    simpa only [Int.natAbs_mul, Int.natAbs_pow, ← Nat.cast_add_one,
      Int.natAbs_natCast] using hm.trans (cubic_le_budget s N)
  · subst c
    simpa [Int.natAbs_mul, Int.natAbs_pow] using quadratic_le_budget s N
  · subst c
    have hm : k*(s*N^2) ≤ s*N^3 := by
      have hmul := Nat.mul_le_mul_right (s*N^2) (show k≤N by omega)
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hm.trans (cubic_le_budget s N)

theorem factor_constant_bound (s N i b : ℕ) (hi : i < s) (c : ℤ)
    (hc : c ∈ (factorStage Empty (i : ℤ) b).usedScalars) :
    c.natAbs ≤ constantBudget s N := by
  rcases factorStage_scalar (i : ℤ) b c hc with rfl | rfl
  · simp
  · exact (pole_constant_bound s N i hi).2

/-- One sign bit plus ordinary binary magnitude length. -/
theorem scalar_bit_bound (s N : ℕ) (c : ℤ)
    (hc : c.natAbs ≤ constantBudget s N) :
    c.natAbs.size + 1 ≤ 3 + (s+1).size + 3*(N+1).size := by
  have hu : s+1 ≤ 2^(s+1).size := (Nat.lt_size_self _).le
  have hv : N+1 ≤ 2^(N+1).size := (Nat.lt_size_self _).le
  have hb : constantBudget s N ≤ 2^(1+(s+1).size+(N+1).size*3) := by
    calc
      constantBudget s N = 2*(s+1)*(N+1)^3 := rfl
      _ ≤ (2*2^(s+1).size)*(2^(N+1).size)^3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hu) (Nat.pow_le_pow_left hv 3)
      _ = 2^(1+(s+1).size+(N+1).size*3) := by
        simp [pow_add, pow_mul, Nat.mul_assoc]
  have hh := Nat.size_le_size (hc.trans hb)
  rw [Nat.size_pow] at hh
  omega

#print axioms merge_constant_bound
#print axioms derivative_constant_bound
#print axioms factor_constant_bound
#print axioms scalar_bit_bound
end
end MultiSymmetric.Circuit

