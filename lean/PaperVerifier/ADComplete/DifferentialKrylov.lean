import Mathlib

/-! Finite stabilization of a genuine differential Krylov chain. -/

namespace ADComplete.DifferentialKrylov

open Matrix Module

variable {F ι : Type*} [Field F] [Algebra ℝ F] [Fintype ι]

/-- A coordinate derivation plus ordinary matrix multiplication. -/
def connection (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F) : ι → F :=
  fun i => D (v i) + A.mulVec v i

lemma connection_zero (D : Derivation ℝ F F) (A : Matrix ι ι F) :
    connection D A (0 : ι → F) = 0 := by
  ext i
  change D 0 + (A.mulVec 0) i = 0
  rw [map_zero, Matrix.mulVec_zero]
  simp

lemma connection_add (D : Derivation ℝ F F) (A : Matrix ι ι F) (u v : ι → F) :
    connection D A (u + v) = connection D A u + connection D A v := by
  ext i
  simp only [connection, Pi.add_apply, map_add, Matrix.mulVec_add]
  ring

lemma connection_smul (D : Derivation ℝ F F) (A : Matrix ι ι F) (c : F) (v : ι → F) :
    connection D A (c • v) = (D c) • v + c • connection D A v := by
  ext i
  simp only [connection, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
    Matrix.mulVec_smul, Pi.add_apply]
  ring

/-- The prefix contains indices strictly smaller than its length. -/
def krylovSpan (q : ℕ → ι → F) (n : ℕ) : Submodule F (ι → F) :=
  Submodule.span F (Set.range (fun i : Fin n => q i.val))

omit [Algebra ℝ F] [Fintype ι] in
lemma prefix_mem (q : ℕ → ι → F) {n i : ℕ} (hi : i < n) : q i ∈ krylovSpan q n :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

omit [Algebra ℝ F] [Fintype ι] in
lemma prefix_mono (q : ℕ → ι → F) {m n : ℕ} (hmn : m ≤ n) : krylovSpan q m ≤ krylovSpan q n := by
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩

omit [Algebra ℝ F] [Fintype ι] in
lemma independent_before_first_dependence (q : ℕ → ι → F) (n : ℕ)
    (h : ∀ k < n, q k ∉ krylovSpan q k) :
    LinearIndependent F (fun i : Fin n => q i.val) := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      apply linearIndependent_finSucc'.mpr
      constructor
      · exact ih (fun k hk => h k (by omega))
      · exact h n (Nat.lt_succ_self n)

omit [Algebra ℝ F] in
/-- Dimension alone locates a first dependence; it does not by itself assert
stability. Stability is proved separately with the actual Leibniz rule. -/
theorem exists_dependence (q : ℕ → ι → F) :
    ∃ n ≤ Fintype.card ι, q n ∈ krylovSpan q n := by
  classical
  by_contra h
  push Not at h
  have hind := independent_before_first_dependence q (Fintype.card ι + 1)
    (fun k hk => h k (by omega))
  have hcard := hind.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_pi] at hcard
  omega

/-- The chain consists of actual repeated connection applications. -/
def vector (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F) (n : ℕ) : ι → F :=
  (connection D A)^[n] v

lemma vector_succ (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F) (n : ℕ) :
    vector D A v (n + 1) = connection D A (vector D A v n) := by
  simp only [vector, Function.iterate_succ_apply']

theorem prefix_invariant (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F)
    (n : ℕ) (hn : vector D A v n ∈ krylovSpan (vector D A v) n)
    (x : ι → F) (hx : x ∈ krylovSpan (vector D A v) n) :
    connection D A x ∈ krylovSpan (vector D A v) n := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [← vector_succ]
      by_cases hi : i.val + 1 < n
      · exact prefix_mem _ hi
      · have hlast : i.val + 1 = n := by omega
        simpa only [hlast] using hn
  | zero => simpa only [connection_zero] using (krylovSpan (vector D A v) n).zero_mem
  | add y z _ _ hy hz =>
      simpa only [connection_add] using (krylovSpan (vector D A v) n).add_mem hy hz
  | smul c y hy hcy =>
      rw [connection_smul]
      exact (krylovSpan (vector D A v) n).add_mem
        ((krylovSpan (vector D A v) n).smul_mem (D c) hy)
        ((krylovSpan (vector D A v) n).smul_mem c hcy)

theorem later_vectors_mem (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F)
    (n : ℕ) (hn : vector D A v n ∈ krylovSpan (vector D A v) n) (k : ℕ) :
    vector D A v k ∈ krylovSpan (vector D A v) n := by
  induction k with
  | zero =>
      by_cases hn₀ : n = 0
      · simpa only [hn₀] using hn
      · exact prefix_mem _ (by omega)
  | succ k ih =>
      rw [vector_succ]
      exact prefix_invariant D A v n hn _ ih

/-- Every differential Krylov vector is spanned by the first ambient-dimension
vectors. No assumption of stability or spanning appears in the statement. -/
theorem ambient_prefix_spans (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F)
    (k : ℕ) : vector D A v k ∈ krylovSpan (vector D A v) (Fintype.card ι) := by
  obtain ⟨n, hn, hdep⟩ := exists_dependence (vector D A v)
  exact prefix_mono _ hn (later_vectors_mem D A v n hdep k)

#print axioms ambient_prefix_spans

end ADComplete.DifferentialKrylov
