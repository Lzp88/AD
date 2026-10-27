import MultiSymmetric.Krylov
set_option autoImplicit false

namespace MultiSymmetric.Cyclic
open Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {τ ι : Type*} [Fintype τ] [Fintype ι]

def wordVector (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) :
    List (Option τ) → (ι → ℝ)
  | [] => v
  | none :: w => H.mulVec (wordVector H A v w)
  | some b :: w => (A b).mulVec (wordVector H A v w)

def jointModule (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) :
    Submodule ℝ (ι → ℝ) := Submodule.span ℝ (Set.range (wordVector H A v))

omit [Fintype τ] in
theorem word_mem (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ)
    (v : ι → ℝ) (w : List (Option τ)) : wordVector H A v w ∈ jointModule H A v :=
  Submodule.subset_span ⟨w, rfl⟩

omit [Fintype τ] in
theorem generator_mem (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ)
    (v z : ι → ℝ) (hz : z ∈ jointModule H A v) (b : Option τ) :
    (match b with | none => H | some b => A b).mulVec z ∈ jointModule H A v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      cases b with
      | none => exact word_mem H A v (none :: w)
      | some b => exact word_mem H A v (some b :: w)
  | zero => simp
  | add x y _ _ hx hy => simpa only [Matrix.mulVec_add] using (jointModule H A v).add_mem hx hy
  | smul c x _ hx => simpa only [Matrix.mulVec_smul] using (jointModule H A v).smul_mem c hx

def CoeffMem (W : Submodule ℝ (ι → ℝ)) (p : ι → ℝ[X]) : Prop :=
  ∀ j, (fun i => (p i).coeff j) ∈ W

omit [Fintype ι] in
theorem coeffMem_const (W : Submodule ℝ (ι → ℝ)) (v : ι → ℝ) (hv : v ∈ W) :
    CoeffMem W (fun i => C (v i)) := by
  intro j
  by_cases hj : j = 0
  · simpa [hj] using hv
  · simp only [Polynomial.coeff_C, if_neg hj]
    exact W.zero_mem

omit [Fintype ι] in
theorem coeffMem_add (W : Submodule ℝ (ι → ℝ)) (p q : ι → ℝ[X])
    (hp : CoeffMem W p) (hq : CoeffMem W q) : CoeffMem W (fun i => p i + q i) := by
  intro j
  simpa only [Polynomial.coeff_add, ← Pi.add_def] using W.add_mem (hp j) (hq j)

omit [Fintype ι] in
theorem coeffMem_sub (W : Submodule ℝ (ι → ℝ)) (p q : ι → ℝ[X])
    (hp : CoeffMem W p) (hq : CoeffMem W q) : CoeffMem W (fun i => p i - q i) := by
  intro j
  simpa only [Polynomial.coeff_sub, ← Pi.sub_def] using W.sub_mem (hp j) (hq j)

omit [Fintype ι] in
theorem coeffMem_scalar (W : Submodule ℝ (ι → ℝ)) (f : ℝ[X]) (p : ι → ℝ[X])
    (hp : CoeffMem W p) : CoeffMem W (fun i => f * p i) := by
  intro j
  have hm : (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal j, f.coeff kl.1 •
      (fun i => (p i).coeff kl.2)) ∈ W := by
    apply W.sum_mem
    intro kl hkl
    exact W.smul_mem _ (hp kl.2)
  convert hm using 1
  ext i
  simp only [Polynomial.coeff_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

omit [Fintype ι] in
theorem coeffMem_derivative (W : Submodule ℝ (ι → ℝ)) (p : ι → ℝ[X])
    (hp : CoeffMem W p) : CoeffMem W (fun i => (p i).derivative) := by
  intro j
  convert W.smul_mem (j + 1 : ℝ) (hp (j + 1)) using 1
  ext i
  simp only [Polynomial.coeff_derivative, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem coeffMem_action (W : Submodule ℝ (ι → ℝ)) (M : Matrix ι ι ℝ)
    (hM : ∀ u ∈ W, M.mulVec u ∈ W) (p : ι → ℝ[X]) (hp : CoeffMem W p) :
    CoeffMem W (ADComplete.Rigidity.polynomialAction M p) := by
  intro j
  convert hM _ (hp j) using 1
  ext i
  simp only [ADComplete.Rigidity.polynomialAction, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Matrix.mulVec, dotProduct]

omit [Fintype ι] in
theorem coeffMem_sum (W : Submodule ℝ (ι → ℝ)) (p : τ → ι → ℝ[X])
    (hp : ∀ b, CoeffMem W (p b)) : CoeffMem W (fun i => ∑ b, p b i) := by
  intro j
  have h : (∑ b, (fun i => (p b i).coeff j)) ∈ W := W.sum_mem (fun b _ => hp b j)
  convert h using 1
  ext i
  simp only [Polynomial.finsetSum_coeff, Finset.sum_apply]

theorem polynomialVector_coeff_mem (a : τ → ℝ) (κ : ℝ)
    (H : Matrix ι ι ℝ) (A : τ → Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) :
    CoeffMem (jointModule H A v) (Krylov.polynomialVector a κ H A v k) := by
  induction k with
  | zero => exact coeffMem_const _ v (word_mem H A v [])
  | succ k ih =>
      let W := jointModule H A v
      apply coeffMem_sub
      · apply coeffMem_add
        · apply coeffMem_add
          · exact coeffMem_scalar W _ _ (coeffMem_derivative W _ ih)
          · exact coeffMem_scalar W _ _ (coeffMem_action W H
              (fun u hu => generator_mem H A v u hu none) _ ih)
        · exact coeffMem_sum W _ (fun b => coeffMem_scalar W _ _
            (coeffMem_action W (A b) (fun u hu => generator_mem H A v u hu (some b)) _ ih))
      · exact coeffMem_scalar W _ _ ih

end
end MultiSymmetric.Cyclic
