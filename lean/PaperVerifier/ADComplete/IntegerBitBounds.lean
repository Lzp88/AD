import PaperVerifier.ADComplete.IntegerBounds

/-! Explicit coarse polynomial bit bounds for the actual radix parameters.
These inequalities concern integers, not numerical experiments. -/
namespace ADComplete.IntegerBounds

def HNat (N : ℕ) : ℕ := N^2*(RNat N)^2
def radixNat (N : ℕ) : ℕ := 2*HNat N+1

theorem LNat_binary_bound (N : ℕ) (hN : 1 ≤ N) : LNat N ≤ 2^(5*N) := by
  have hn : N ≤ 2^N := N.lt_two_pow_self.le
  calc
    LNat N = 3*N^3 := rfl
    _ ≤ 2^2*(2^N)^3 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hn 3)
    _ = 2^(2+N*3) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2^(5*N) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem RNat_binary_bound (N : ℕ) (hN : 1 ≤ N) : RNat N ≤ 2^(5*N^2) := by
  calc
    RNat N = (LNat N)^(N-1) := rfl
    _ ≤ (2^(5*N))^(N-1) := Nat.pow_le_pow_left (LNat_binary_bound N hN) (N-1)
    _ = 2^((5*N)*(N-1)) := by rw [← pow_mul]
    _ ≤ 2^(5*N^2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith [Nat.sub_le N 1]

theorem HNat_binary_bound (N : ℕ) (hN : 1 ≤ N) : HNat N ≤ 2^(12*N^2) := by
  have hn : N ≤ 2^N := N.lt_two_pow_self.le
  calc
    HNat N = N^2*(RNat N)^2 := rfl
    _ ≤ (2^N)^2*(2^(5*N^2))^2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) (Nat.pow_le_pow_left (RNat_binary_bound N hN) 2)
    _ = 2^(2*N+10*N^2) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ 2^(12*N^2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith

theorem radixNat_binary_bound (N : ℕ) (hN : 1 ≤ N) : radixNat N ≤ 2^(12*N^2+2) := by
  have h := HNat_binary_bound N hN
  have hpow : 1 ≤ 2^(12*N^2) := Nat.one_le_two_pow
  calc
    radixNat N = 2*HNat N+1 := rfl
    _ ≤ 4*2^(12*N^2) := by omega
    _ = 2^(12*N^2+2) := by rw [pow_add]; ring

theorem actual_radix_large (N : ℕ) : 2*(HNat N : ℤ) < (radixNat N : ℤ) := by
  simp [radixNat]

#print axioms LNat_binary_bound
#print axioms radixNat_binary_bound
end ADComplete.IntegerBounds
