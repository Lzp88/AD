import PaperVerifier.ADComplete.PSDResidualScanClosed
import PaperVerifier.ADComplete.PSDFoldedRepresentative

namespace ADComplete.PSDFactory
open Matrix ADComplete.PSDBird ADComplete.PSDHomogeneousLift
open scoped BigOperators
noncomputable section

def rankOne (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i _ => v i

theorem mul_smul_J (Z : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) :
    Z*(x • J n)=x • rankOne (Z.mulVec (fun _ => 1)) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.smul_apply,PSDHomogeneousLift.J,rankOne,Matrix.mulVec,dotProduct,smul_eq_mul,mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem residualValue_rankOne {N n : ℕ} (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (v : ℕ → Fin n → ℝ) (hv : ∀ i, (z i).mulVec (fun _ => 1)=v i.val)
    (r : Fin (N-1)) :
    residualValue z (fun i j => gramScalar n (z i) (z j)) r =
      (n : ℝ)^r.val • rankOne (PSDResidual.residualSequence v (r.val+1)) := by
  let K := PSDResidual.prefixColumns v (r.val+1)
  let A := Matrix.submatrix (fun i j => gramScalar n (z i) (z j)) (prefixIndex r) (prefixIndex r)
  let b := fun i => gramScalar n (z (prefixIndex r i)) (z (nextIndex r))
  have hA : A=PSDResidual.gram K := by
    ext i j
    change dotProduct ((z (prefixIndex r i)).mulVec (fun _ => 1))
      ((z (prefixIndex r j)).mulVec (fun _ => 1))=∑ x, v i.val x*v j.val x
    rw [hv,hv]
    rfl
  have hb : b=K.transpose.mulVec (v (r.val+1)) := by
    ext i
    change dotProduct ((z (prefixIndex r i)).mulVec (fun _ => 1))
      ((z (nextIndex r)).mulVec (fun _ => 1))=∑ x, v i.val x*v (r.val+1) x
    rw [hv,hv]
    rfl
  have hc : ∀ i, Matrix.det (A.updateCol i b)=((PSDResidual.gram K).adjugate.mulVec
      (K.transpose.mulVec (v (r.val+1)))) i := by
    intro i
    rw [← Matrix.cramer_apply,Matrix.cramer_eq_adjugate_mulVec,hA,hb]
  unfold residualValue
  change z (nextIndex r) * (((n : ℝ)^r.val*A.det) • J n) -
    ∑ i, z (prefixIndex r i) * (((n : ℝ)^r.val*(A.updateCol i b).det) • J n) = _
  simp_rw [mul_smul_J,hv,hc]
  rw [hA]
  ext i j
  simp only [Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,rankOne,PSDResidual.residualSequence,
    PSDResidual.residual,PSDResidual.prefixColumns,PSDResidual.gram,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct,K,prefixIndex,nextIndex,Fin.val_castLE]
  rw [mul_sub,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _
    ring

theorem rankOne_add (v w : Fin n → ℝ) : rankOne v+rankOne w=rankOne (v+w) := rfl

theorem rankOne_square (v : Fin n → ℝ) :
    rankOne v*(rankOne v).transpose=(n : ℝ) • Matrix.vecMulVec v v := by
  ext i j
  simp only [Matrix.mul_apply,rankOne,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
  simp

#print axioms residualValue_rankOne
#print axioms rankOne_square
end
end ADComplete.PSDFactory
