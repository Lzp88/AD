import PaperVerifier.ADComplete.PSDCramerBridge

namespace ADComplete.PSDFactory
open Matrix ADComplete.PSDBird ADComplete.PSDHomogeneousLift
open scoped BigOperators
noncomputable section

theorem rankOne_smul (x : ℝ) (v : Fin n → ℝ) : x • rankOne v=rankOne (x • v) := rfl

theorem writtenResiduals_rankOne {N n : ℕ} (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (v : ℕ → Fin n → ℝ) (hv : ∀ i, (z i).mulVec (fun _ => 1)=v i.val)
    (h0 : v 0=fun _ => 1) :
    writtenResiduals z (fun i j => gramScalar n (z i) (z j))=
      fun i => rankOne ((n : ℝ)^(i.val-1) • PSDResidual.residualSequence v i.val) := by
  funext i
  unfold writtenResiduals
  split_ifs with hi
  · rw [hi,PSDResidual.residualSequence_zero,h0]
    simp only [Nat.zero_sub,pow_zero,one_smul]
    rfl
  · let r : Fin (N-1) := ⟨i.val-1,by have := i.isLt; omega⟩
    have hh := residualValue_rankOne z v hv r
    have he : r.val+1=i.val := by simp only [r]; omega
    rw [he,rankOne_smul] at hh
    exact hh

theorem sosValue_rankOne {N n : ℕ} (hN : 0<N) (u : ℕ → Fin n → ℝ) :
    sosValue hN (fun i => rankOne (u i.val))=(n : ℝ) • PSDCyclic.squareMatrix N u := by
  cases N with
  | zero => omega
  | succ k =>
    simp only [sosValue]
    simp_rw [rankOne_add,rankOne_square]
    ext i j
    simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul,
      PSDCyclic.squareMatrix,Matrix.mul_apply,PSDCyclic.chainMatrix,Matrix.transpose_apply,
      Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,PSDCyclic.chainColumn,
      Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,
      Pi.add_apply,currentIndex,nextIndex]
    rw [mul_add,Finset.mul_sum]
    simp

theorem sosValue_residuals {N n : ℕ} (hN : 0<N) (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (v : ℕ → Fin n → ℝ) (hv : ∀ i, (z i).mulVec (fun _ => 1)=v i.val)
    (h0 : v 0=fun _ => 1) :
    sosValue hN (writtenResiduals z (fun i j => gramScalar n (z i) (z j)))=
      (n : ℝ) • PSDCyclic.squareMatrix N (fun k => (n : ℝ)^(k-1) • PSDResidual.residualSequence v k) := by
  rw [writtenResiduals_rankOne z v hv h0]
  exact sosValue_rankOne (n := n) hN (fun k => (n : ℝ)^(k-1) • PSDResidual.residualSequence v k)

/-- Exact equality to the representative whose image and cyclicity have
already been proved; all Cramer variants and singular ranks are covered. -/
theorem sosValue_foldedPrincipalMatrix {N n : ℕ} (hN : 0<N) (m R : ℕ)
    (s : Fin n → ℤ) (u : Fin m → Fin n → ℤ) (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (hv : ∀ i, (z i).mulVec (fun _ => 1)=PSDFoldedFrame.foldedVector s u (PSDFoldedFrame.tau N m R) i.val)
    (hs : PSDFoldedFrame.castVector s=fun _ => 1) :
    sosValue hN (writtenResiduals z (fun i j => gramScalar n (z i) (z j)))=
      PSDFoldedFrame.foldedPrincipalMatrix N m R s u (n : ℝ) := by
  exact sosValue_residuals hN z _ hv (by simpa only [PSDFoldedFrame.foldedVector_zero] using hs)

#print axioms sosValue_foldedPrincipalMatrix
end
end ADComplete.PSDFactory
