import PaperVerifier.ADComplete.PSDFrameSemantics
import PaperVerifier.ADComplete.PSDSOSBridge
import PaperVerifier.ADComplete.PSDFoldedLiteral
import PaperVerifier.ADComplete.MatrixSemantics

/-! Literal factory semantics, including all determinant scans and SOS gates.
The all-ones hypothesis below is a matrix identity, not a supplied Gram or
residual output. The graph specialization derives it from the tree. -/
namespace ADComplete.PSDFactory
open Matrix CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit CircuitAudit.Degrees
open ADComplete.PSDBird ADComplete.PSDHomogeneousLift
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem expression_adjoint {n : ℕ} (a d : Matrix (Fin n) (Fin n) ℝ)
    (ha : star a=a) (hd : star d=d) (p : Expr) :
    exprPair a d p=(p.eval a d,(p.eval a d).transpose) := by
  simp only [exprPair,reverse_eval a d ha hd p]
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]

theorem compiled_adjoint_value {N n : ℕ} (hN : 2≤N)
    (a d : Matrix (Fin n) (Fin n) ℝ) (ha : star a=a) (hd : star d=d)
    (hj : (allOnes N).eval a d=J n) :
    AdjointValue n a d (compiled N).1 (compiled N).2
      (sosValue (show 0<N by omega)
        (writtenResiduals (fun i => (frameExpr N i).eval a d)
          (fun i j => gramScalar n ((frameExpr N i).eval a d) ((frameExpr N j).eval a d)))) := by
  let z : Fin N → Matrix (Fin n) (Fin n) ℝ := fun i => (frameExpr N i).eval a d
  have hf := frame_values N (show 1≤N by omega) a d
  have hJ : Corner n a d (frame N).circuit (frame N).j 1 := by
    refine ⟨hf.1.1,?_⟩
    rw [hf.1.2,expression_adjoint a d ha hd,hj]
    simp only [one_smul]
    rfl
  have hZ : ∀ i, AdjointValue n a d (frame N).circuit ((frame N).z i) (z i) := by
    intro i
    exact ⟨(hf.2 i).1,(hf.2 i).2.trans (expression_adjoint a d ha hd _)⟩
  have hg := gramStage_corner hJ hZ
  have eg := gramStage_extends (frame N).j (frame N).z (frame N).circuit
  have hv := residualScan_value (fun i => adjoint_extend (hZ i) eg) hg
    (fun _ => corner_adjoint (corner_extend hJ eg)) (List.finRange (N-1))
  have hs := sos_value (show 0<N by omega) hv
  simp only [one_smul] at hs
  rw [residualVectorScan_complete (show 0<N by omega)] at hs
  simpa only [compiled,dif_neg (show ¬N≤1 by omega),residualStage,z] using hs

theorem compiled_value_folded {N n : ℕ} (hN : 2≤N)
    (a d : Matrix (Fin n) (Fin n) ℝ) (ha : star a=a) (hd : star d=d)
    (hj : (allOnes N).eval a d=J n) (m R : ℕ) (s : Fin n → ℤ)
    (u : Fin m → Fin n → ℤ) (hs : PSDFoldedFrame.castVector s=fun _ => 1)
    (hv : ∀ i : Fin N, ((frameExpr N i).eval a d).mulVec (fun _ => 1)=
      PSDFoldedFrame.foldedVector s u (PSDFoldedFrame.tau N m R) i.val) :
    ((compiled N).2.value (compiled N).1 a d).1=
      PSDFoldedFrame.foldedPrincipalMatrix N m R s u (n : ℝ) := by
  have hc := compiled_adjoint_value hN a d ha hd hj
  have he := congrArg Prod.fst hc.2
  exact he.trans (sosValue_foldedPrincipalMatrix (show 0<N by omega) m R s u _ hv hs)

theorem compiled_one_value {R : Type*} [Ring R] (a d : R) :
    (compiled 1).2.value (compiled 1).1 a d=(1,1) := by
  simp [compiled_one,unitRef,unitCircuit,PairRef.value,Circuit.value,Circuit.eval,Gate.eval]

#print axioms compiled_adjoint_value
#print axioms compiled_value_folded
#print axioms compiled_one_value
end
end ADComplete.PSDFactory
