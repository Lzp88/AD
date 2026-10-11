import PaperVerifier.ADComplete.PSDBirdCompiler
import PaperVerifier.ADComplete.BirdCertificate

/-! The actual shared AD DAG computes the homogeneous Gram determinant
corner. Bird correctness is used only as a proof, not as an oracle gate. -/
namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts
open ADComplete.PSDHomogeneousLift

def augmented (n : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) ℝ)
    (f : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (n : ℝ)*BirdDet.Spec.stepEntry g f i j

theorem iterate_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {A F : Matrix (Fin k) (Fin k) PairRef} {g f : Matrix (Fin k) (Fin k) ℝ}
    (hA : Corners n a d c A g) (hF : Corners n a d c F f) (t : ℕ) :
    Corners n a d (iterate A t c F).1 (iterate A t c F).2 ((augmented n g)^[t] f) := by
  induction t generalizing c F f with
  | zero => simpa only [iterate, Function.iterate_zero_apply] using hF
  | succ t ih =>
    have hs := stage_corner hA hF
    have he := stage_extends A F c
    have ht := ih (corners_extend hA he) hs
    change Corners n a d (iterate A t (stage A F c).1 (stage A F c).2).1
      (iterate A t (stage A F c).1 (stage A F c).2).2 ((augmented n g)^[t+1] f)
    rw [Function.iterate_succ_apply]
    exact ht

theorem step_linear {k : ℕ} (g f : Matrix (Fin k) (Fin k) ℝ) (s : ℝ) :
    BirdDet.Spec.stepEntry g (fun i j => s*f i j) =
      fun i j => s*BirdDet.Spec.stepEntry g f i j := by
  ext i j
  simp only [BirdDet.Spec.stepEntry, Matrix.of_apply]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem augmented_iterate {k : ℕ} (n : ℕ) (g f : Matrix (Fin k) (Fin k) ℝ) (t : ℕ) :
    (augmented n g)^[t] f =
      fun i j => (n : ℝ)^t*((BirdDet.Spec.stepEntry g)^[t] f) i j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    unfold augmented
    rw [step_linear]
    ext i j
    rw [pow_succ']
    ring

/-- k is determinant order minus one; the output pair consists of the
same corner in both orientations. The theorem remains valid at n=0. -/
theorem compiler_determinant {n : ℕ} (k : ℕ)
    {a d : Matrix (Fin n) (Fin n) ℝ} {c : Circuit}
    {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    {g : Matrix (Fin (k+1)) (Fin (k+1)) ℝ} (hA : Corners n a d c A g) :
    Corner n a d (compiler k A c).1 (compiler k A c).2 ((n : ℝ)^k*g.det) := by
  have ht := iterate_corner hA hA k
  rw [augmented_iterate] at ht
  have hc := corner_scale (ht 0 0) ((-1 : ℤ)^k)
  have he : (((-1 : ℤ)^k : ℤ) : ℝ)*((n : ℝ)^k*((BirdDet.Spec.stepEntry g)^[k] g) 0 0) =
      (n : ℝ)^k*g.det := by
    rw [ADComplete.BirdCertificate.birdDetSpec_eq_det, BirdDet.Spec.birdDetSpec_succ]
    push_cast
    ring
  simpa only [compiler, he] using hc

#print axioms compiler_determinant
end ADComplete.PSDBird
