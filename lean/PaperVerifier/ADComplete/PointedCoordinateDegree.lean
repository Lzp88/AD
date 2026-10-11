import PaperVerifier.CircuitAudit.Degrees

/-! Actual multivariate coordinate polynomials, with separate matrix and seed degrees.
Degree bounds are on every monomial of the literal polynomial support, so they
cannot be inferred from cancellations after a specialization. -/

namespace ADComplete.PointedCoordinateDegree
open Matrix MvPolynomial CircuitAudit.Degrees
open scoped BigOperators Pointwise
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {σ V : Type*} [Fintype V] [DecidableEq V]

def DegreeBound (w : σ → ℕ) (p : MvPolynomial σ ℝ) (d : ℕ) : Prop :=
  ∀ m ∈ p.support, Finsupp.weight w m ≤ d

lemma bound_mono {w : σ → ℕ} {p : MvPolynomial σ ℝ} {d e : ℕ}
    (h : DegreeBound w p d) (he : d ≤ e) : DegreeBound w p e :=
  fun m hm => (h m hm).trans he

lemma bound_zero (w : σ → ℕ) (d : ℕ) : DegreeBound w (0 : MvPolynomial σ ℝ) d := by
  intro m hm
  simp at hm

lemma bound_one (w : σ → ℕ) : DegreeBound w (1 : MvPolynomial σ ℝ) 0 := by
  intro m hm
  simp only [support_one, Finset.mem_singleton] at hm
  subst m
  simp

lemma bound_X (w : σ → ℕ) (s : σ) : DegreeBound w (X s : MvPolynomial σ ℝ) (w s) := by
  classical
  intro m hm
  simp only [support_X, Finset.mem_singleton] at hm
  subst m
  simp only [Finsupp.weight_single, one_smul, le_refl]

lemma bound_add {w : σ → ℕ} {p q : MvPolynomial σ ℝ} {d e : ℕ}
    (hp : DegreeBound w p d) (hq : DegreeBound w q e) : DegreeBound w (p+q) (max d e) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact (hp m hm).trans (le_max_left _ _)
  · exact (hq m hm).trans (le_max_right _ _)

lemma bound_mul {w : σ → ℕ} {p q : MvPolynomial σ ℝ} {d e : ℕ}
    (hp : DegreeBound w p d) (hq : DegreeBound w q e) : DegreeBound w (p*q) (d+e) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul p q hm)
  subst m
  rw [map_add]
  exact Nat.add_le_add (hp a ha) (hq b hb)

lemma bound_zsmul {w : σ → ℕ} {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : DegreeBound w p d) (c : ℤ) : DegreeBound w (c • p) d := by
  intro m hm
  exact hp m (support_smul hm)

lemma bound_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (h : ∀ i ∈ s, DegreeBound w (f i) d) :
    DegreeBound w (∑ i ∈ s, f i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using bound_zero w d
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simpa only [max_self] using bound_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

omit [Fintype V] in
lemma bound_matrix_one (w : σ → ℕ) (i j : V) :
    DegreeBound w ((1 : Matrix V V (MvPolynomial σ ℝ)) i j) 0 := by
  by_cases hij : i = j
  · subst j; simpa only [Matrix.one_apply_eq] using bound_one w
  · simpa only [Matrix.one_apply_ne hij] using bound_zero w 0

omit [DecidableEq V] in
lemma bound_matrix_product (w : σ → ℕ) (A B : Matrix V V (MvPolynomial σ ℝ))
    (a b : ℕ) (hA : ∀ i j, DegreeBound w (A i j) a)
    (hB : ∀ i j, DegreeBound w (B i j) b) (i j : V) :
    DegreeBound w ((A*B) i j) (a+b) := by
  rw [Matrix.mul_apply]
  exact bound_sum Finset.univ _ w _ (fun k _ => bound_mul (hA i k) (hB k j))

lemma bound_expression (w : σ → ℕ) (H K : Matrix V V (MvPolynomial σ ℝ))
    (a : ℕ) (hH : ∀ i j, DegreeBound w (H i j) a)
    (hK : ∀ i j, DegreeBound w (K i j) a) (p : Expr) (i j : V) :
    DegreeBound w ((p.eval H K) i j) (p.degree*a) := by
  induction p generalizing i j with
  | zero => simpa only [Expr.eval, Expr.degree, zero_mul, Matrix.zero_apply] using bound_zero w 0
  | one => simpa only [Expr.eval, Expr.degree, zero_mul] using bound_matrix_one w i j
  | a => simpa only [Expr.eval, Expr.degree, one_mul] using hH i j
  | d => simpa only [Expr.eval, Expr.degree, one_mul] using hK i j
  | scale c p ih =>
    simpa only [Expr.eval, Expr.degree, Matrix.smul_apply] using bound_zsmul (ih i j) c
  | add p q ihp ihq =>
    apply bound_mono (bound_add (ihp i j) (ihq i j))
    exact max_le (Nat.mul_le_mul_right a (le_max_left _ _))
      (Nat.mul_le_mul_right a (le_max_right _ _))
  | mul p q ihp ihq =>
    simpa only [Expr.eval, Expr.degree, Nat.add_mul] using
      bound_matrix_product w (p.eval H K) (q.eval H K) _ _ ihp ihq i j

omit [DecidableEq V] in
lemma bound_mulVec (w : σ → ℕ) (A : Matrix V V (MvPolynomial σ ℝ))
    (v : V → MvPolynomial σ ℝ) (a b : ℕ)
    (hA : ∀ i j, DegreeBound w (A i j) a) (hv : ∀ j, DegreeBound w (v j) b) (i : V) :
    DegreeBound w (A.mulVec v i) (a+b) := by
  rw [Matrix.mulVec, dotProduct]
  exact bound_sum Finset.univ _ w _ (fun j _ => bound_mul (hA i j) (hv j))

def scalarTable (H K : Matrix V V (MvPolynomial σ ℝ)) (v : V → MvPolynomial σ ℝ)
    (p s q : Expr) : MvPolynomial σ ℝ :=
  ∑ i, ((p.eval H K).mulVec v i) *
    ((s.eval H K).mulVec ((q.eval H K).mulVec v) i)

lemma bound_scalarTable (w : σ → ℕ) (H K : Matrix V V (MvPolynomial σ ℝ))
    (v : V → MvPolynomial σ ℝ) (a b : ℕ)
    (hH : ∀ i j, DegreeBound w (H i j) a) (hK : ∀ i j, DegreeBound w (K i j) a)
    (hv : ∀ j, DegreeBound w (v j) b) (p s q : Expr) :
    DegreeBound w (scalarTable H K v p s q) ((p.degree+s.degree+q.degree)*a+2*b) := by
  have hp (i) := bound_mulVec w (p.eval H K) v (p.degree*a) b
    (bound_expression w H K a hH hK p) hv i
  have hq (i) := bound_mulVec w (q.eval H K) v (q.degree*a) b
    (bound_expression w H K a hH hK q) hv i
  have hs (i) := bound_mulVec w (s.eval H K) ((q.eval H K).mulVec v)
    (s.degree*a) (q.degree*a+b) (bound_expression w H K a hH hK s) hq i
  have ht := bound_sum Finset.univ _ w ((p.degree*a+b)+(s.degree*a+(q.degree*a+b)))
    (fun i _ => bound_mul (hp i) (hs i))
  have he : (p.degree*a+b)+(s.degree*a+(q.degree*a+b)) =
    (p.degree+s.degree+q.degree)*a+2*b := by ring
  rw [he] at ht
  exact ht

#print axioms bound_scalarTable

end
end ADComplete.PointedCoordinateDegree
