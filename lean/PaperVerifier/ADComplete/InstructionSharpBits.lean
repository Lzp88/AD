import PaperVerifier.ADComplete.InstructionResources

/-! Symbolic base-height bounds retaining the logarithmic dependence.
The explicit final bound certifies O(N^5 log N) stored entry bits. -/
namespace ADComplete.InstructionHeights
open CircuitAudit.CircuitCosts
open ADComplete.InstructionDegrees (compiled)
open ADComplete.IntegerBounds
open scoped Matrix.Norms.Operator

def ell (N : ℕ) : ℕ := Nat.clog 2 N
def KBits (N : ℕ) : ℕ := 8*N*(ell N+1)+4

theorem LNat_log_bound (N : ℕ) : LNat N ≤ 2^(3*ell N+2) := by
  have h : N ≤ 2^(ell N) := Nat.le_pow_clog (by norm_num) N
  calc
    LNat N = 3*N^3 := rfl
    _ ≤ 2^2*(2^(ell N))^3 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left h 3)
    _ = 2^(3*ell N+2) := by rw [← pow_mul, ← pow_add]; congr 1; ring

theorem RNat_log_bound (N : ℕ) : RNat N ≤ 2^((3*ell N+2)*N) := by
  calc
    RNat N = (LNat N)^(N-1) := rfl
    _ ≤ (2^(3*ell N+2))^(N-1) := Nat.pow_le_pow_left (LNat_log_bound N) (N-1)
    _ = 2^((3*ell N+2)*(N-1)) := by rw [← pow_mul]
    _ ≤ 2^((3*ell N+2)*N) := Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.sub_le N 1))

theorem HNat_log_bound (N : ℕ) (hN : 1 ≤ N) : HNat N ≤ 2^(8*N*(ell N+1)) := by
  have h : N ≤ 2^(ell N) := Nat.le_pow_clog (by norm_num) N
  calc
    HNat N = N^2*(RNat N)^2 := rfl
    _ ≤ (2^(ell N))^2*(2^((3*ell N+2)*N))^2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left h 2) (Nat.pow_le_pow_left (RNat_log_bound N) 2)
    _ = 2^(2*ell N+2*(3*ell N+2)*N) := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ 2^(8*N*(ell N+1)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith [Nat.mul_le_mul_left (ell N) hN]

theorem radixNat_log_bound (N : ℕ) (hN : 1 ≤ N) :
    radixNat N ≤ 2^(8*N*(ell N+1)+2) := by
  have h := HNat_log_bound N hN
  have h1 := Nat.one_le_two_pow (n := 8*N*(ell N+1))
  calc
    radixNat N = 2*HNat N+1 := rfl
    _ ≤ 4*2^(8*N*(ell N+1)) := by omega
    _ = 2^(8*N*(ell N+1)+2) := by rw [pow_add]; ring

theorem KNat_log_bound (N : ℕ) (hN : 1 ≤ N) : KNat N ≤ 2^(KBits N) := by
  let E := 8*N*(ell N+1)+2
  have hb : radixNat N ≤ 2^E := radixNat_log_bound N hN
  have hn : N^3 ≤ 2^E := by
    have hl : N^3 ≤ LNat N := by unfold LNat; omega
    apply (hl.trans (LNat_log_bound N)).trans
    apply Nat.pow_le_pow_right (by norm_num)
    dsimp [E]
    nlinarith [Nat.mul_le_mul_left (ell N) hN]
  have h2 : 2 ≤ 2^E := by
    have he : 1 ≤ E := by dsimp [E]; omega
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) he
  calc
    KNat N = radixNat N+N^3+2 := rfl
    _ ≤ 4*2^E := by omega
    _ = 2^(KBits N) := by
      have he : E+2=KBits N := by dsimp [E, KBits]
      rw [← he, pow_add]
      ring

theorem actual_register_symbolic_norm {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) (i : ℕ) (hi : i < (compiled N (radixNat N)).1.length) :
    ‖(compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i‖ ≤
      (KNat N : ℝ)^(20*N^4) := by
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N ≤ N^3 := by nlinarith [Nat.mul_le_mul_left N hN2]
  have hNK : N ≤ KNat N := by unfold KNat; omega
  have hNKR : (N : ℝ) ≤ KNat N := by exact_mod_cast hNK
  have hK2 : (2 : ℝ) ≤ KNat N := by exact_mod_cast KNat_two_le N
  have hK1 : (1 : ℝ) ≤ KNat N := by linarith
  have h := every_register_norm_bound (KNat N) hK2 (G.adjMatrix ℤ) (G.degMatrix ℤ)
    ((adjacency_norm_bound G N hn).trans hNKR) ((degree_norm_bound G N hn).trans hNKR)
    (compiled N (radixNat N)).1 (compiled_constants_bound N hN) i
  exact h.trans (pow_le_pow_right₀ hK1 (compiled_all_weights N hN (radixNat N) i hi))

theorem actual_register_sharp_bits {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) (i : ℕ) (hi : i < (compiled N (radixNat N)).1.length)
    (u v : V) :
    Nat.size ((compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs ≤
      20*N^4*(8*N*(ell N+1)+4)+1 := by
  have hK : (KNat N : ℝ) ≤ (2 : ℝ)^(KBits N) := by exact_mod_cast KNat_log_bound N hN
  have h := (entry_norm_le_opNorm _ u v).trans (actual_register_symbolic_norm G N hN hn i hi)
  have hbin : ‖(compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v‖ ≤
      (2 : ℝ)^(20*N^4*KBits N) := by
    apply h.trans
    calc
      _ ≤ ((2 : ℝ)^(KBits N))^(20*N^4) := pow_le_pow_left₀ (by positivity) hK _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs] at hbin
  have hnat : ((compiled N (radixNat N)).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs ≤
      2^(20*N^4*KBits N) := by exact_mod_cast hbin
  have hs := Nat.size_le_size hnat
  simpa only [Nat.size_pow, KBits] using hs

#print axioms actual_register_sharp_bits
end ADComplete.InstructionHeights
