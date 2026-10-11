import PaperVerifier.ADComplete.InstructionSyntaxBridge
import Mathlib.Analysis.Matrix.Normed

/-! Exact operator-norm probe and scalar-word bounds. Reversal is bounded
by its own recurrence; transpose is not treated as norm preserving. -/
namespace ADComplete.IntegerBounds
open CircuitAudit.Degrees
open scoped Matrix.Norms.Operator NNReal

theorem mul_bound {R : Type*} [NormedRing R] {x y : R} {X Y : ℝ}
    (hx : ‖x‖ ≤ X) (hy : ‖y‖ ≤ Y) (hX : 0 ≤ X) (_hY : 0 ≤ Y) :
    ‖x*y‖ ≤ X*Y :=
  (norm_mul_le x y).trans (mul_le_mul hx hy (norm_nonneg y) hX)

theorem scale_bound {R : Type*} [NormedRing R]
    {x : R} {X C : ℝ} (c : ℤ) (hx : ‖x‖ ≤ X) (hc : |(c : ℝ)| ≤ C)
    (_hX : 0 ≤ X) : ‖c • x‖ ≤ C*X := by
  apply (norm_zsmul_le c x).trans
  simp only [Int.norm_eq_abs]
  exact mul_le_mul hc hx (norm_nonneg x) (le_trans (abs_nonneg _) hc)

theorem coefficient_bound (N k j : ℕ) (hj : j ≤ k) (hk : k ≤ N) :
    |((((N : ℤ)^2 * ((j : ℤ)-k)) : ℤ) : ℝ)| ≤ (N : ℝ)^3 := by
  have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  push_cast
  rw [abs_mul, abs_of_nonneg (sq_nonneg (N : ℝ)), abs_of_nonpos (sub_nonpos.mpr hj')]
  have hn : 0 ≤ (N : ℝ)^2 := sq_nonneg _
  have hdiff : -((j : ℝ)-k) ≤ N := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  nlinarith [mul_le_mul_of_nonneg_left hdiff hn]

theorem factor_bound {R : Type*} [NormedRing R] [NormOneClass R]
    (N k j : ℕ) (d : R) (hd : ‖d‖ ≤ N) (hj : j ≤ k) (hk : k ≤ N) :
    ‖d + (((N : ℤ)^2*((j : ℤ)-k)) • (1 : R))‖ ≤ (N : ℝ)+(N : ℝ)^3 := by
  apply (norm_add_le _ _).trans
  apply add_le_add hd
  simpa using scale_bound (((N : ℤ)^2*((j : ℤ)-k))) (x := (1 : R))
    (X := 1) (C := (N : ℝ)^3) (by simp) (coefficient_bound N k j hj hk) (by norm_num)

def L (N : ℕ) : ℝ := 3*(N : ℝ)^3

theorem L_nonneg (N : ℕ) : 0 ≤ L N := by unfold L; positivity
theorem L_one_le (N : ℕ) (hN : 1 ≤ N) : 1 ≤ L N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold L
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 3]

theorem recurrence_bound {R : Type*} [NormedRing R]
    [NormOneClass R] (N k j : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (a d x y : R) (ha : ‖a‖ ≤ N) (hd : ‖d‖ ≤ N)
    {B : ℝ} (hB : 0 ≤ B) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    ‖(if j ≤ k then (d+((N : ℤ)^2*((j : ℤ)-k))•1)*x else 0) +
      (if 0 < j then (N : ℤ)^2 • (a*y) else 0)‖ ≤ L N*B ∧
    ‖(if j ≤ k then x*(d+((N : ℤ)^2*((j : ℤ)-k))•1) else 0) +
      (if 0 < j then (N : ℤ)^2 • (y*a) else 0)‖ ≤ L N*B := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn3 : (N : ℝ) ≤ (N : ℝ)^3 := by nlinarith [sq_nonneg ((N : ℝ)-1)]
  have left (x : R) (hx : ‖x‖ ≤ B) :
      ‖if j ≤ k then (d+((N : ℤ)^2*((j : ℤ)-k))•1)*x else 0‖ ≤
        ((N : ℝ)+(N : ℝ)^3)*B := by
    split_ifs with hj
    · exact mul_bound (factor_bound N k j d hd hj hk) hx (by positivity) hB
    · simp only [norm_zero]; positivity
  have leftRev (x : R) (hx : ‖x‖ ≤ B) :
      ‖if j ≤ k then x*(d+((N : ℤ)^2*((j : ℤ)-k))•1) else 0‖ ≤
        ((N : ℝ)+(N : ℝ)^3)*B := by
    split_ifs with hj
    · simpa [mul_comm B] using mul_bound hx (factor_bound N k j d hd hj hk) hB (by positivity)
    · simp only [norm_zero]; positivity
  have right (z : R) (hz : ‖z‖ ≤ (N : ℝ)*B) :
      ‖if 0 < j then (N : ℤ)^2 • z else 0‖ ≤ (N : ℝ)^3*B := by
    split_ifs
    · have hs := scale_bound ((N : ℤ)^2) hz (C := (N : ℝ)^2)
        (by simp [abs_of_nonneg (sq_nonneg (N : ℝ))]) (by positivity)
      convert hs using 1
      ring
    · simp only [norm_zero]; positivity
  have hr := right (a*y) (mul_bound ha hy hn hB)
  have hr' := right (y*a) (by simpa [mul_comm B] using mul_bound hy ha hB hn)
  constructor
  · calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ ((N : ℝ)+(N : ℝ)^3)*B+(N : ℝ)^3*B := add_le_add (left x hx) hr
      _ ≤ L N*B := by unfold L; nlinarith [mul_le_mul_of_nonneg_right hn3 hB]
  · calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ ((N : ℝ)+(N : ℝ)^3)*B+(N : ℝ)^3*B := add_le_add (leftRev x hx) hr'
      _ ≤ L N*B := by unfold L; nlinarith [mul_le_mul_of_nonneg_right hn3 hB]

theorem probe_norm_pair {R : Type*} [NormedRing R]
    [NormOneClass R] (N : ℕ) (hN : 1 ≤ N) (a d : R)
    (ha : ‖a‖ ≤ N) (hd : ‖d‖ ≤ N) (k : ℕ) (hk : k ≤ N-1) (j : ℕ) :
    ‖(probe N k j).eval a d‖ ≤ (L N)^k ∧
    ‖(probe N k j).reverse.eval a d‖ ≤ (L N)^k := by
  induction k generalizing j with
  | zero =>
    simp only [probe]
    split_ifs <;> simp [Expr.reverse, Expr.eval]
  | succ k ih =>
    have hk' : k ≤ N-1 := by omega
    have hp := ih hk' j
    have hq := ih hk' (j-1)
    have h := recurrence_bound N k j hN (by omega) a d
      ((probe N k j).eval a d) ((probe N k (j-1)).eval a d)
      ha hd (pow_nonneg (L_nonneg N) _) hp.1 hq.1
    have hr := recurrence_bound N k j hN (by omega) a d
      ((probe N k j).reverse.eval a d) ((probe N k (j-1)).reverse.eval a d)
      ha hd (pow_nonneg (L_nonneg N) _) hp.2 hq.2
    simpa only [probe, Expr.reverse, Expr.eval, apply_ite, pow_succ',
      Expr.eval, Expr.reverse] using And.intro h.1 hr.2

def LNat (N : ℕ) : ℕ := 3*N^3
def RNat (N : ℕ) : ℕ := (LNat N)^(N-1)

theorem cast_LNat (N : ℕ) : ((LNat N : ℕ) : ℝ) = L N := by
  simp [LNat, L]

theorem probe_norm_uniform {R : Type*} [NormedRing R] [NormOneClass R]
    (N : ℕ) (hN : 1 ≤ N) (a d : R) (ha : ‖a‖ ≤ N) (hd : ‖d‖ ≤ N)
    (p : Expr) (hp : p ∈ probeList N N) :
    ‖p.eval a d‖ ≤ (RNat N : ℝ) ∧ ‖p.reverse.eval a d‖ ≤ (RNat N : ℝ) := by
  suffices ∀ k ≤ N, ∀ p ∈ probeList N k,
      ‖p.eval a d‖ ≤ (L N)^(N-1) ∧ ‖p.reverse.eval a d‖ ≤ (L N)^(N-1) by
    simpa only [RNat, Nat.cast_pow, cast_LNat] using this N le_rfl p hp
  intro k hk
  induction k with
  | zero => simp [probeList]
  | succ k ih =>
    intro p hp
    simp only [probeList, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ih (by omega) p hp
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
      have hb := probe_norm_pair N hN a d ha hd k (by omega) j
      have he : (L N)^k ≤ (L N)^(N-1) :=
        pow_le_pow_right₀ (L_one_le N hN) (by omega)
      exact ⟨hb.1.trans he, hb.2.trans he⟩

theorem row_abs_sum_le_opNorm {V : Type*} [Fintype V]
    (X : Matrix V V ℤ) (i : V) : (∑ j, ‖X i j‖) ≤ ‖X‖ := by
  have h : (∑ j, ‖X i j‖₊) ≤ ‖X‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i)
  have h' : ((∑ j, ‖X i j‖₊ : ℝ≥0) : ℝ) ≤ (‖X‖₊ : ℝ) := h
  simpa only [NNReal.coe_sum, coe_nnnorm] using h'

theorem double_sum_norm_bound {V : Type*} [Fintype V]
    (X : Matrix V V ℤ) : ‖∑ i, ∑ j, X i j‖ ≤ (Fintype.card V : ℝ)*‖X‖ := by
  calc
    _ ≤ ∑ i, ‖∑ j, X i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : V, ‖X‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (norm_sum_le _ _).trans (row_abs_sum_le_opNorm X i)
    _ = _ := by simp

theorem matrix_word_digit_bound {V : Type*} [Fintype V] [DecidableEq V]
    (N R : ℕ) (hn : Fintype.card V ≤ N) (U B W : Matrix V V ℤ)
    (hU : ‖U‖ ≤ R) (hB : ‖B‖ ≤ N) (hW : ‖W‖ ≤ R) :
    |∑ i, ∑ j, ((U*B)*W) i j| ≤ (N^2*R^2 : ℕ) := by
  have hUB : ‖U*B‖ ≤ (R : ℝ)*N := mul_bound hU hB (by positivity) (by positivity)
  have hX : ‖(U*B)*W‖ ≤ (R : ℝ)*N*R := mul_bound hUB hW (by positivity) (by positivity)
  have hn' : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast hn
  have h : ‖∑ i, ∑ j, ((U*B)*W) i j‖ ≤ (N : ℝ)^2*(R : ℝ)^2 := by
    calc
      _ ≤ (Fintype.card V : ℝ)*‖(U*B)*W‖ := double_sum_norm_bound _
      _ ≤ (N : ℝ)*((R : ℝ)*N*R) :=
        mul_le_mul hn' hX (norm_nonneg _) (Nat.cast_nonneg N)
      _ = _ := by ring
  rw [Int.norm_eq_abs] at h
  exact_mod_cast h

theorem adjacency_norm_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hn : Fintype.card V ≤ N) :
    ‖G.adjMatrix ℤ‖ ≤ (N : ℝ) := by
  have h : ‖G.adjMatrix ℤ‖₊ ≤ (N : ℝ≥0) := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i hi
    calc
      ∑ j, ‖(G.adjMatrix ℤ) i j‖₊ ≤ ∑ _j : V, (1 : ℝ≥0) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [SimpleGraph.adjMatrix_apply]
        split_ifs <;> simp
      _ = (Fintype.card V : ℝ≥0) := by simp
      _ ≤ N := by exact_mod_cast hn
  exact h

theorem degree_norm_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hn : Fintype.card V ≤ N) :
    ‖G.degMatrix ℤ‖ ≤ (N : ℝ) := by
  rw [SimpleGraph.degMatrix, Matrix.linfty_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg N)).mpr
  intro v
  simp only [Int.norm_natCast]
  exact_mod_cast (G.degree_lt_card_verts v).le.trans hn

theorem core_slot_norm_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) (s : Fin 3) :
    ‖CircuitAudit.RadixFactorization.coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s‖ ≤ (N : ℝ) := by
  fin_cases s
  · change ‖(1 : Matrix V V ℤ)‖ ≤ (N : ℝ)
    rw [norm_one]
    exact_mod_cast hN
  · simpa [CircuitAudit.RadixFactorization.coreSlots] using adjacency_norm_bound G N hn
  · simpa [CircuitAudit.RadixFactorization.coreSlots] using degree_norm_bound G N hn

/-- The actual three-slot probe digits on every graph of at most N vertices.
Tree-specific hypotheses are not needed for this height estimate. -/
theorem actual_probe_digit_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1 ≤ N)
    (hn : Fintype.card V ≤ N) (p q : Expr)
    (hp : p ∈ probeList N N) (hq : q ∈ probeList N N) (s : Fin 3) :
    |∑ i, ∑ j, ((star (p.eval (G.adjMatrix ℤ) (G.degMatrix ℤ)) *
      CircuitAudit.RadixFactorization.coreSlots (G.adjMatrix ℤ) (G.degMatrix ℤ) s) *
      q.eval (G.adjMatrix ℤ) (G.degMatrix ℤ)) i j| ≤ (N^2*(RNat N)^2 : ℕ) := by
  have hpB := probe_norm_uniform N hN (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (adjacency_norm_bound G N hn) (degree_norm_bound G N hn) p hp
  have hqB := probe_norm_uniform N hN (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (adjacency_norm_bound G N hn) (degree_norm_bound G N hn) q hq
  have hr := reverse_eval (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (G.isHermitian_adjMatrix ℤ) (G.isHermitian_degMatrix ℤ) p
  apply matrix_word_digit_bound N (RNat N) hn _ _ _
  · rw [← hr]
    exact hpB.2
  · exact core_slot_norm_bound G N hN hn s
  · exact hqB.1

#print axioms probe_norm_pair
#print axioms probe_norm_uniform
#print axioms matrix_word_digit_bound
#print axioms actual_probe_digit_bound
end ADComplete.IntegerBounds
