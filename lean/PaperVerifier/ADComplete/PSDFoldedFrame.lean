import PaperVerifier.ADComplete.PSDFoldedSubspace
import PaperVerifier.ADComplete.PSDFoldedPrefix
import PaperVerifier.ADComplete.PSDPolynomialHeight
import PaperVerifier.ADComplete.ConstantFrame
import PaperVerifier.ADComplete.ScalarExtension

/-! The prescribed integer folded frame and its rank-sensitive first positions. -/

namespace ADComplete.PSDFoldedFrame

open Matrix Polynomial Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]
abbrev F := RatFunc ℝ

def castVector (s : ι → ℤ) : ι → ℝ := fun i => (s i : ℝ)

def sourceModule {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ (insert (castVector s) (Set.range (fun j => castVector (u j))))

def H0 (N m R : ℕ) : ℕ := m * R * 2 ^ ((N-2)*(m-1))
def H1 (N m R : ℕ) : ℕ := N.factorial * (H0 N m R) ^ (N-1)
def tau (N m R : ℕ) : ℕ := H1 N m R + 2

def foldedPolynomial {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) : ℕ → ι → ℤ[X]
  | 0 => fun i => C (s i)
  | j+1 => fun i => PSDSpecialization.foldedEntry m (fun a => u a i) j

def foldedVector {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) (t : ℕ)
    (k : ℕ) : ι → ℝ := fun i => (((foldedPolynomial s u k i).eval (t : ℤ) : ℤ) : ℝ)

def foldedMinor {m r : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ)
    (rows : Fin r → ι) : Matrix (Fin r) (Fin r) ℤ[X] :=
  fun i j => foldedPolynomial s u j.val (rows i)

omit [Fintype ι] in
theorem foldedVector_zero {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ) (t : ℕ) :
    foldedVector s u t 0 = castVector s := by
  ext i
  simp [foldedVector, foldedPolynomial, castVector]

omit [Fintype ι] in
theorem foldedVector_succ {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ)
    (t j : ℕ) : foldedVector s u t (j+1) =
      ∑ a : Fin m, (((2^j*t : ℕ) : ℝ)^a.val) • castVector (u a) := by
  ext i
  simp only [foldedVector, foldedPolynomial, PSDSpecialization.foldedEntry,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, Int.cast_natCast, Finset.sum_apply,
    Pi.smul_apply, castVector, smul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_pow, ← pow_mul]
  ring

omit [Fintype ι] in
theorem foldedVector_mem_source {m : ℕ} (s : ι → ℤ) (u : Fin m → ι → ℤ)
    (t k : ℕ) : foldedVector s u t k ∈ sourceModule s u := by
  cases k with
  | zero => rw [foldedVector_zero]; exact Submodule.subset_span (Set.mem_insert _ _)
  | succ j =>
      rw [foldedVector_succ]
      apply Submodule.sum_mem
      intro a _
      apply Submodule.smul_mem
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a, rfl⟩)

end
end ADComplete.PSDFoldedFrame
