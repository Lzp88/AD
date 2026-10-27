import MultiSymmetric.RecurrenceConstants
import MultiSymmetric.CircuitRow
set_option autoImplicit false

/-! Bounds for the inventories carried by the actual executed program. -/
namespace MultiSymmetric.Circuit
open scoped BigOperators
noncomputable section

variable {R : Type*} [Ring R]

theorem factorRun_scalars_bound (s N b : ℕ) (p : Polynomial R)
    (k : ℕ) (hk : k≤s) (c : ℤ)
    (hc : c ∈ (factorRun (fun j => (j:ℤ)) b p k).usedScalars) :
    c.natAbs≤constantBudget s N := by
  induction k generalizing c with
  | zero => simp [factorRun] at hc
  | succ k ih =>
      change c ∈ (factorRun (fun j => (j:ℤ)) b p k).usedScalars ∪
        (factorStage Empty (k:ℤ) (b+k)).usedScalars at hc
      rcases Finset.mem_union.mp hc with hp | hs'
      · exact ih (by omega) c hp
      · exact factor_constant_bound s N k (b+k) (by omega) c hs'

theorem rowRun_scalars_bound (s N k : ℕ) (hk : k<N)
    (gen : Fin (s+1) → R) (p : Polynomial R) (c : ℤ)
    (hc : c ∈ (rowRun s ((s:ℤ)*(N:ℤ)^2) gen k p).usedScalars) :
    c.natAbs≤constantBudget s N := by
  simp only [rowRun, generatorStage_scalars, Finset.union_empty,
    Finset.mem_union] at hc
  rcases hc with ((((hG | hder) | hT) | hgder) | hquot) | hmerge
  · exact factorRun_scalars_bound s N _ _ s le_rfl c hG
  · exact derivative_constant_bound s N k (s*k) hk (by nlinarith) c hder
  · exact factorRun_scalars_bound s N _ _ s le_rfl c hT
  · exact derivative_constant_bound s N k (s*(k+1)) hk le_rfl c hgder
  · obtain ⟨i,hi,hc⟩ := Finset.mem_biUnion.mp hquot
    change c ∈ (integerScan (i.val:ℤ) _ _ _).usedScalars at hc
    rcases integerScan_scalar (i.val:ℤ) _ _ _ c hc with rfl | rfl
    · simp
    · exact (pole_constant_bound s N i.val i.isLt).1
  · exact merge_constant_bound s N (s*(k+1)) k hk c hmerge

#print axioms factorRun_scalars_bound
#print axioms rowRun_scalars_bound
end
end MultiSymmetric.Circuit
