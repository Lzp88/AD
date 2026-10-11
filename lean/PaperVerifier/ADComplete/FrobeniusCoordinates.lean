import PaperVerifier.ADComplete.UniformProbeBounds
import PaperVerifier.ADComplete.FrameSemantics

/-! Actual Frobenius coordinates and symmetric left multiplication. -/

namespace ADComplete.Frobenius

open Matrix
open scoped BigOperators Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def flatten : Matrix ι ι ℝ →ₗ[ℝ] ((ι × ι) → ℝ) where
  toFun := Function.uncurry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inflate : ((ι × ι) → ℝ) →ₗ[ℝ] Matrix ι ι ℝ where
  toFun := Function.curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma flatten_injective : Function.Injective (flatten (ι := ι)) := by
  intro a b h
  funext i j
  exact congrFun h (i,j)

def leftMatrix (a : Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ := a ⊗ₖ 1

def leftHom : Matrix ι ι ℝ →+* Matrix (ι × ι) (ι × ι) ℝ where
  toFun := leftMatrix
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' := fun a b => Matrix.add_kronecker a b _
  map_mul' := by
    intro a b
    simpa only [leftMatrix, Matrix.one_mul] using
      Matrix.mul_kronecker_mul a b (1 : Matrix ι ι ℝ) (1 : Matrix ι ι ℝ)

lemma leftMatrix_mulVec (a p : Matrix ι ι ℝ) :
    (leftMatrix a).mulVec (flatten p) = flatten (a*p) := by
  ext ⟨i,j⟩
  simp [leftMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, flatten, Matrix.mul_apply]

omit [Fintype ι] in
lemma leftMatrix_symmetric (a : Matrix ι ι ℝ) (ha : a.IsSymm) :
    (leftMatrix a).IsSymm := by
  change (a ⊗ₖ (1 : Matrix ι ι ℝ)).transpose = _
  apply Matrix.ext
  rintro ⟨i,j⟩ ⟨k,l⟩
  change a k i * (1 : Matrix ι ι ℝ) l j = a i k * (1 : Matrix ι ι ℝ) j l
  have hh := congrFun (congrFun ha.eq i) k
  change a k i = a i k at hh
  rw [hh]
  simp [Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
lemma pairing_columns (u v : (ι × ι) → ℝ) :
    Rigidity.pairing u v = ∑ j : ι,
      Rigidity.pairing (fun i => u (i,j)) (fun i => v (i,j)) := by
  unfold Rigidity.pairing
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem leftMatrix_interval (a : Matrix ι ι ℝ) (lo hi : ℝ)
    (h : ∀ v : ι → ℝ,
      lo * Rigidity.pairing v v ≤ Rigidity.pairing v (a.mulVec v) ∧
      Rigidity.pairing v (a.mulVec v) ≤ hi * Rigidity.pairing v v)
    (v : (ι × ι) → ℝ) :
    lo * Rigidity.pairing v v ≤ Rigidity.pairing v ((leftMatrix a).mulVec v) ∧
      Rigidity.pairing v ((leftMatrix a).mulVec v) ≤ hi * Rigidity.pairing v v := by
  have heq : (leftMatrix a).mulVec v = flatten (a * inflate v) :=
    leftMatrix_mulVec a (inflate v)
  rw [heq, pairing_columns, pairing_columns]
  have hcol (j : ι) : (fun i => flatten (a * inflate v) (i,j)) =
      a.mulVec (fun i => v (i,j)) := rfl
  simp_rw [hcol]
  simp only [Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (h (fun i => v (i,j))).1)
  · exact Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (h (fun i => v (i,j))).2)

#print axioms leftMatrix_interval

end
end ADComplete.Frobenius
