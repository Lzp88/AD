import PaperVerifier.ADComplete.PSDFactoryConstants

/-! Explicit scalar-label and stored-entry bit bounds. These statements range
over every actual gate and every stored register of the literal shared DAG. -/
namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts ADComplete.InstructionHeights ADComplete.IntegerBounds
open scoped Matrix.Norms.Operator

def baseNat (N : ℕ) : ℕ := 2^(12*N^4)

theorem baseNat_two_le (N : ℕ) (hN : 1≤N) : 2≤baseNat N := by
  have h14 : 1≤N^4 := Nat.one_le_pow _ _ hN
  simpa [baseNat] using Nat.pow_le_pow_right (n := 2) (by decide) (show 1≤12*N^4 by omega)

theorem original_inputs_le_base (N : ℕ) (hN : 1≤N) : N≤baseNat N := by
  have h14 : N≤N^4 := by simpa using Nat.pow_le_pow_right hN (show 1≤4 by decide)
  exact N.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (show N≤12*N^4 by omega))

theorem compiled_real_constants (N : ℕ) (hN : 1≤N) :
    (compiled N).1.constantsAllowed {z | |(z : ℝ)|≤(baseNat N : ℝ)} := by
  apply constants_mono (compiled_constantsAllowed N hN)
  intro z hz
  change z.natAbs≤baseNat N at hz
  change |(z : ℝ)|≤(baseNat N : ℝ)
  rw [←Int.cast_abs,←Int.natCast_natAbs]
  exact_mod_cast hz

theorem compiled_scalar_labels_bits (N : ℕ) (hN : 1≤N) :
    (compiled N).1.constantsAllowed {z | Nat.size z.natAbs≤12*N^4+1} := by
  apply constants_mono (compiled_constantsAllowed N hN)
  intro z hz
  change z.natAbs≤2^(12*N^4) at hz
  change Nat.size z.natAbs≤12*N^4+1
  simpa only [Nat.size_pow] using Nat.size_le_size hz

theorem actual_register_norm_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1≤N)
    (hn : Fintype.card V≤N) (i : ℕ) (hi : i<(compiled N).1.length) :
    ‖(compiled N).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i‖≤(2 : ℝ)^(1200*N^7) := by
  have hk2 : (2 : ℝ)≤baseNat N := by exact_mod_cast baseNat_two_le N hN
  have hnk : (N : ℝ)≤baseNat N := by exact_mod_cast original_inputs_le_base N hN
  have hh := every_register_norm_bound (baseNat N) hk2 (G.adjMatrix ℤ) (G.degMatrix ℤ)
    ((adjacency_norm_bound G N hn).trans hnk) ((degree_norm_bound G N hn).trans hnk)
    (compiled N).1 (compiled_real_constants N hN) i
  have hw := compiled_weight_bound N hN i hi
  have hb : (baseNat N : ℝ)=(2 : ℝ)^(12*N^4) := by simp [baseNat]
  calc
    _ ≤ (baseNat N : ℝ)^(weight (compiled N).1 i) := hh
    _ ≤ (baseNat N : ℝ)^(100*N^3) := pow_le_pow_right₀ (by linarith) hw
    _ = (2 : ℝ)^(1200*N^7) := by rw [hb,←pow_mul]; congr 1; ring

theorem actual_register_entry_bits {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1≤N)
    (hn : Fintype.card V≤N) (i : ℕ) (hi : i<(compiled N).1.length) (u v : V) :
    Nat.size ((compiled N).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs≤1200*N^7+1 := by
  have hh := (entry_norm_le_opNorm _ u v).trans (actual_register_norm_bound G N hN hn i hi)
  rw [Int.norm_eq_abs,←Int.cast_abs,←Int.natCast_natAbs] at hh
  have hn' : ((compiled N).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs≤2^(1200*N^7) := by
    exact_mod_cast hh
  simpa only [Nat.size_pow] using Nat.size_le_size hn'

#print axioms compiled_scalar_labels_bits
#print axioms actual_register_entry_bits
end ADComplete.PSDFactory
