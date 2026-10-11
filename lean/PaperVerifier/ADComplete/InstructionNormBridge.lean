import PaperVerifier.ADComplete.InstructionHeights
import PaperVerifier.ADComplete.IntegerBounds

/-! Soundness of the actual instruction weight interpreter. Every actual
register is bounded, including temporary registers and radix powers. -/
namespace ADComplete.InstructionHeights
open CircuitAudit.CircuitCosts

theorem gate_norm_bound {R : Type*} [NormedRing R] [NormOneClass R]
    (K : ℝ) (hK : 2 ≤ K) (a d : R) (ha : ‖a‖ ≤ K) (hd : ‖d‖ ≤ K)
    (c : Circuit) (g : Gate)
    (hc : ∀ i, ‖c.value a d i‖ ≤ K^(weight c i))
    (hg : g.constantsAllowed {z | |(z : ℝ)| ≤ K}) :
    ‖g.eval a d (c.eval a d)‖ ≤ K^(gateWeight (weights c) g) := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  cases g with
  | zero => simp [Gate.eval, gateWeight]
  | ident => simp [Gate.eval, gateWeight]
  | atomA => simpa [Gate.eval, gateWeight] using ha
  | atomD => simpa [Gate.eval, gateWeight] using hd
  | add i j =>
    change ‖c.value a d i+c.value a d j‖ ≤ K^(max (weight c i) (weight c j)+1)
    have hi := (hc i).trans (pow_le_pow_right₀ hK1 (Nat.le_max_left (weight c i) (weight c j)))
    have hj := (hc j).trans (pow_le_pow_right₀ hK1 (Nat.le_max_right (weight c i) (weight c j)))
    calc
      _ ≤ ‖c.value a d i‖+‖c.value a d j‖ := norm_add_le _ _
      _ ≤ K^(max (weight c i) (weight c j))+K^(max (weight c i) (weight c j)) := add_le_add hi hj
      _ ≤ K^(max (weight c i) (weight c j)+1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg hK0 (max (weight c i) (weight c j))]
  | mul i j =>
    change ‖c.value a d i*c.value a d j‖ ≤ K^(weight c i+weight c j)
    rw [pow_add]
    exact ADComplete.IntegerBounds.mul_bound (hc i) (hc j) (pow_nonneg hK0 _) (pow_nonneg hK0 _)
  | scale z i =>
    change ‖z • c.value a d i‖ ≤ K^(weight c i+1)
    rw [pow_succ']
    exact ADComplete.IntegerBounds.scale_bound z (hc i) hg (pow_nonneg hK0 _)

theorem every_register_norm_bound {R : Type*} [NormedRing R] [NormOneClass R]
    (K : ℝ) (hK : 2 ≤ K) (a d : R) (ha : ‖a‖ ≤ K) (hd : ‖d‖ ≤ K)
    (c : Circuit) (hc : c.constantsAllowed {z | |(z : ℝ)| ≤ K}) (i : ℕ) :
    ‖c.value a d i‖ ≤ K^(weight c i) := by
  induction c generalizing i with
  | empty => simp [Circuit.value, Circuit.eval, weight, weights]
  | snoc c g ih =>
    by_cases hi : i < c.length
    · rw [old_value a d c g i hi, old_weight c g i hi]
      exact ih hc.1 i
    · by_cases he : i=c.length
      · subst i
        rw [new_value, new_weight]
        exact gate_norm_bound K hK a d ha hd c g (fun i => ih hc.1 i) hc.2
      · have hlast : (c.snoc g).length ≤ i := by simp only [Circuit.length]; omega
        have hvalue : (c.snoc g).value a d i=0 :=
          List.getD_eq_default _ _ (by simpa using hlast)
        rw [hvalue, norm_zero]
        positivity

#print axioms every_register_norm_bound
end ADComplete.InstructionHeights
