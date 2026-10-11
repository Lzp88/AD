import PaperVerifier.ADComplete.PSDFactoryDegrees

namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit CircuitAudit.Degrees
open ADComplete.PSDFoldCompiler

def frameExpr (N : ℕ) (i : Fin N) : Expr :=
  foldExpr (tau N) ((probeList N N).drop 1) i

theorem frame_values {R : Type*} [Ring R] (N : ℕ) (hN : 1≤N) (a d : R) :
    PairValue a d (frame N).circuit (frame N).j (exprPair a d (allOnes N)) ∧
      ∀ i, PairValue a d (frame N).circuit ((frame N).z i) (exprPair a d (frameExpr N i)) := by
  let p := probePrefix N
  let j := CircuitAudit.DistanceCircuit.build N p.circuit
  have hp := CircuitAudit.FullCompression.prefix_ready_empty N
  have ep : Extends initial p.circuit := CircuitAudit.FullCompression.prefix_extends_initial N
  have ej : Extends p.circuit j.1 := CircuitAudit.DistanceCircuit.build_extends _ _
  have hj : PairValue a d j.1 j.2 (exprPair a d (allOnes N)) :=
    ⟨CircuitAudit.DistanceCircuit.build_valid N hp,CircuitAudit.DistanceCircuit.build_value N a d hp ep⟩
  have ho : PairValue a d j.1 oneRef (1,1) :=
    ⟨PairRef.valid_extend hp.1 ej,one_value a d (ep.trans ej)⟩
  have hpp : ∀ q∈p.probes.drop 1, q.valid j.1 := by
    intro q hq
    exact PairRef.valid_extend (build_probes_valid N (N-1) q (List.mem_of_mem_drop hq)) ej
  have hv := prefix_probe_values N hN a d
  have hm : p.probes.map (fun q => q.value j.1 a d)=(probeList N N).map (exprPair a d) := by
    rw [← hv]
    apply List.map_congr_left
    intro q hq
    exact PairRef.value_extend (build_probes_valid N (N-1) q hq) ej a d
  have hd : (p.probes.drop 1).map (fun q => q.value j.1 a d)=
      ((probeList N N).drop 1).map (exprPair a d) := by
    rw [List.map_drop,List.map_drop,hm]
  have hf := stage_value (N := N) (τ := tau N) a d ho hpp hd
  have ef := stage_extends N (tau N) oneRef (p.probes.drop 1) j.1
  exact ⟨pairValue_extend hj ef,hf⟩

@[simp] theorem frameExpr_zero (N : ℕ) (hN : 0<N) : frameExpr N ⟨0,hN⟩=.one := by
  simp [frameExpr,foldExpr]

#print axioms frame_values
end ADComplete.PSDFactory
