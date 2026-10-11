import PaperVerifier.ADComplete.PSDFactoryDefinition
import PaperVerifier.ADComplete.IntegerBitBounds

/-! Polynomial binary bounds for the prescribed original-coordinate height
and folded-frame scalar labels. These are inequalities for the actual factory
parameters, not existence of some sufficiently large specialization. -/
namespace ADComplete.PSDFactory
open ADComplete.IntegerBounds ADComplete.PSDFoldedFrame

theorem M_le_square (N : ℕ) (hN : 1≤N) : M N ≤ N^2 := by
  unfold M
  apply (Nat.div_le_div_right (show N*(N+1)≤2*N^2 by nlinarith)).trans
  simp

theorem H0_binary_bound (N : ℕ) (hN : 1≤N) :
    PSDFoldedFrame.H0 N (M N-1) (RNat N) ≤ 2^(8*N^3) := by
  have hm : M N-1 ≤ N^2 := (Nat.sub_le _ _).trans (M_le_square N hN)
  have hn : N ≤ 2^N := N.lt_two_pow_self.le
  have hm2 : M N-1 ≤ 2^(2*N) := by
    apply hm.trans
    calc
      N^2 ≤ (2^N)^2 := Nat.pow_le_pow_left hn 2
      _ = 2^(2*N) := by rw [← pow_mul]; congr 1; omega
  have hex : (N-2)*((M N-1)-1) ≤ N^3 := by
    calc
      (N-2)*((M N-1)-1) ≤ N*N^2 :=
        Nat.mul_le_mul (Nat.sub_le _ _) ((Nat.sub_le _ _).trans hm)
      _ = N^3 := by ring
  have h12 : N ≤ N^2 := by simpa using Nat.pow_le_pow_right hN (show 1≤2 by decide)
  have h23 : N^2 ≤ N^3 := Nat.pow_le_pow_right hN (by decide)
  calc
    PSDFoldedFrame.H0 N (M N-1) (RNat N)
        ≤ 2^(2*N)*2^(5*N^2)*2^(N^3) :=
      Nat.mul_le_mul (Nat.mul_le_mul hm2 (RNat_binary_bound N hN))
        (Nat.pow_le_pow_right (by decide) hex)
    _ = 2^(2*N+5*N^2+N^3) := by rw [← pow_add,← pow_add]
    _ ≤ 2^(8*N^3) := Nat.pow_le_pow_right (by decide) (by omega)

theorem H1_binary_bound (N : ℕ) (hN : 1≤N) :
    PSDFoldedFrame.H1 N (M N-1) (RNat N) ≤ 2^(9*N^4) := by
  have hn : N ≤ 2^N := N.lt_two_pow_self.le
  have hf : N.factorial ≤ 2^(N^2) := by
    calc
      N.factorial ≤ N^N := Nat.factorial_le_pow N
      _ ≤ (2^N)^N := Nat.pow_le_pow_left hn N
      _ = 2^(N^2) := by rw [← pow_mul,pow_two]
  have h24 : N^2 ≤ N^4 := Nat.pow_le_pow_right hN (by decide)
  have hp : 8*N^3*(N-1) ≤ 8*N^4 := by
    calc
      8*N^3*(N-1) ≤ 8*N^3*N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 8*N^4 := by ring
  calc
    PSDFoldedFrame.H1 N (M N-1) (RNat N)
        ≤ 2^(N^2)*(2^(8*N^3))^(N-1) :=
      Nat.mul_le_mul hf (Nat.pow_le_pow_left (H0_binary_bound N hN) (N-1))
    _ = 2^(N^2+8*N^3*(N-1)) := by rw [← pow_mul,← pow_add]
    _ ≤ 2^(9*N^4) := Nat.pow_le_pow_right (by decide) (by omega)

theorem tau_binary_bound (N : ℕ) (hN : 1≤N) : PSDFactory.tau N ≤ 2^(11*N^4) := by
  have hh := H1_binary_bound N hN
  have hp : 1≤2^(9*N^4) := Nat.one_le_two_pow
  have h14 : 1≤N^4 := Nat.one_le_pow _ _ hN
  calc
    PSDFactory.tau N ≤ 4*2^(9*N^4) := by unfold PSDFactory.tau PSDFoldedFrame.tau; omega
    _ = 2^(9*N^4+2) := by rw [pow_add]; ring
    _ ≤ 2^(11*N^4) := Nat.pow_le_pow_right (by decide) (by omega)

theorem folded_scalar_binary_bound (N i : ℕ) (hN : 1≤N) (hi : i≤N) :
    (ADComplete.PSDFoldCompiler.scalar (PSDFactory.tau N) i).natAbs ≤ 2^(12*N^4) := by
  have h14 : N≤N^4 := by simpa using Nat.pow_le_pow_right hN (show 1≤4 by decide)
  have he : i-1≤N := (Nat.sub_le _ _).trans hi
  calc
    (ADComplete.PSDFoldCompiler.scalar (PSDFactory.tau N) i).natAbs
        = 2^(i-1)*PSDFactory.tau N := by
          simp [ADComplete.PSDFoldCompiler.scalar, Int.natAbs_mul]
    _ ≤ 2^N*2^(11*N^4) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) he) (tau_binary_bound N hN)
    _ = 2^(N+11*N^4) := by rw [← pow_add]
    _ ≤ 2^(12*N^4) := Nat.pow_le_pow_right (by decide) (by omega)

#print axioms H0_binary_bound
#print axioms tau_binary_bound
#print axioms folded_scalar_binary_bound
end ADComplete.PSDFactory
