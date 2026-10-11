import PaperVerifier.ADComplete.PSDPairStar
import PaperVerifier.ADComplete.PSDFactoryDegrees
import PaperVerifier.ADComplete.InstructionPolynomial

/-! The full fixed factory has actual adjoint companions on every symmetric
input and on the free generators. No tree-specific identity is assumed. -/

namespace ADComplete.PSDPairStar
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit ADComplete.PSDBird
open ADComplete.PSDFactory

variable {R : Type*} [Ring R] [StarRing R] {a d : R} {c : Circuit}

theorem residualStep_star {N : ℕ} {Z : Fin N → PairRef}
    {G : Matrix (Fin N) (Fin N) PairRef}
    (hZ : ∀ i, StarPair a d c (Z i)) (hG : ∀ i j, StarPair a d c (G i j))
    (r : Fin (N-1)) :
    StarPair a d (residualStep Z G r c).1 (residualStep Z G r c).2 := by
  let A := G.submatrix (prefixIndex r) (prefixIndex r)
  let b := fun i => G (prefixIndex r i) (nextIndex r)
  have hA : ∀ i j, StarPair a d c (A i j) := fun i j => hG _ _
  have hb : ∀ i, StarPair a d c (b i) := fun i => hG _ _
  have hd := determinantBatch_star (cramerVariants_star hA hb)
  have he := determinantBatch_extends (cramerVariants A b) c
  exact residual_star (extend (hZ _) he) (hd 0)
    (fun i => extend (hZ _) he) (fun i => hd i.succ)

theorem residualScan_star {N : ℕ} {Z V : Fin N → PairRef}
    {G : Matrix (Fin N) (Fin N) PairRef}
    (hZ : ∀ i, StarPair a d c (Z i)) (hG : ∀ i j, StarPair a d c (G i j))
    (hV : ∀ i, StarPair a d c (V i)) (rs : List (Fin (N-1))) :
    ∀ i, StarPair a d (residualScan Z G c V rs).1 ((residualScan Z G c V rs).2 i) := by
  induction rs generalizing c V with
  | nil => exact hV
  | cons r rs ih =>
      have he := residualStep_extends Z G r c
      have hr := residualStep_star hZ hG r
      have hw : ∀ i, StarPair a d (residualStep Z G r c).1
          (vectorWrite V (nextIndex r) (residualStep Z G r c).2 i) := by
        intro i
        unfold vectorWrite
        split
        · exact hr
        · exact extend (hV i) he
      exact ih (fun i => extend (hZ i) he) (fun i j => extend (hG i j) he) hw

theorem residualStage_star {N : ℕ} {Z : Fin N → PairRef} {j : PairRef}
    {G : Matrix (Fin N) (Fin N) PairRef} (hj : StarPair a d c j)
    (hZ : ∀ i, StarPair a d c (Z i)) (hG : ∀ i l, StarPair a d c (G i l)) :
    ∀ i, StarPair a d (residualStage j Z G c).1 ((residualStage j Z G c).2 i) :=
  residualScan_star hZ hG (fun _ => hj) _

theorem square_star {p : PairRef} (hp : StarPair a d c p) :
    StarPair a d (square p c).1 (square p c).2 := mul hp (swap hp)

theorem chainSquare_star {N : ℕ} {V : Fin N → PairRef}
    (hV : ∀ i, StarPair a d c (V i)) (r : Fin (N-1)) :
    StarPair a d (chainSquare V r c).1 (chainSquare V r c).2 :=
  square_star (add (hV _) (hV _))

theorem chainSquareSum_star {N : ℕ} {V : Fin N → PairRef}
    (hV : ∀ i, StarPair a d c (V i)) (rs : List (Fin (N-1))) :
    StarPair a d (chainSquareSum V c rs).1 (chainSquareSum V c rs).2 := by
  induction rs with
  | nil => exact zero a d c
  | cons r rs ih =>
      have es := chainSquareSum_extends V c rs
      have hw := chainSquare_star (fun i => extend (hV i) es) r
      exact add hw (extend ih (chainSquare_extends _ _ _))

theorem sos_star {N : ℕ} (hN : 0<N) {V : Fin N → PairRef}
    (hV : ∀ i, StarPair a d c (V i)) :
    StarPair a d (sos hN V c).1 (sos hN V c).2 := by
  have hs := chainSquareSum_star hV (List.finRange (N-1))
  have es := chainSquareSum_extends V c (List.finRange (N-1))
  have hv := square_star (extend (hV ⟨0,hN⟩) es)
  exact add hv (extend hs (square_extends _ _))

theorem expression_pair_star (ha : star a=a) (hd : star d=d)
    {p : PairRef} {e : CircuitAudit.Degrees.Expr} (hp : p.valid c)
    (he : p.value c a d=exprPair a d e) : StarPair a d c p := by
  refine ⟨hp, ?_⟩
  rw [he]
  exact CircuitAudit.Degrees.reverse_eval a d ha hd e

theorem frame_star (N : ℕ) (hN : 1≤N) (ha : star a=a) (hd : star d=d) :
    StarPair a d (frame N).circuit (frame N).j ∧
      ∀ i, StarPair a d (frame N).circuit ((frame N).z i) := by
  let p := probePrefix N
  let j := CircuitAudit.DistanceCircuit.build N p.circuit
  let f := ADComplete.PSDFoldCompiler.stage N (PSDFactory.tau N) oneRef
    (p.probes.drop 1) j.1
  have hready := CircuitAudit.FullCompression.prefix_ready_empty N
  have hep := CircuitAudit.FullCompression.prefix_extends_initial N
  have hej : Extends p.circuit j.1 := CircuitAudit.DistanceCircuit.build_extends _ _
  have hef : Extends j.1 f.1 := ADComplete.PSDFoldCompiler.stage_extends _ _ _ _ _
  have hj := expression_pair_star ha hd (CircuitAudit.DistanceCircuit.build_valid N hready)
    (CircuitAudit.DistanceCircuit.build_value N a d hready hep)
  have ho : ADComplete.PSDFoldCompiler.PairValue a d j.1 oneRef (1,1) :=
    ⟨PairRef.valid_extend hready.1 hej, one_value a d (hep.trans hej)⟩
  have hp : ∀ q ∈ p.probes.drop 1, q.valid j.1 := by
    intro q hq
    exact PairRef.valid_extend (build_probes_valid N (N-1) q (List.mem_of_mem_drop hq)) hej
  have hx : (p.probes.drop 1).map (fun q => q.value j.1 a d)=
      ((CircuitAudit.Degrees.probeList N N).drop 1).map (exprPair a d) := by
    have hh := prefix_probe_values N hN a d
    have hh' := congrArg (List.drop 1) hh
    rw [← List.map_drop, ← List.map_drop] at hh'
    rw [← hh']
    apply List.map_congr_left
    intro q hq
    exact PairRef.value_extend (build_probes_valid N (N-1) q (List.mem_of_mem_drop hq)) hej a d
  have hf := ADComplete.PSDFoldCompiler.stage_value (N := N) (τ := PSDFactory.tau N)
    a d ho hp hx
  exact ⟨extend hj hef, fun i => expression_pair_star ha hd (hf i).1 (hf i).2⟩

theorem compiled_star (N : ℕ) (ha : star a=a) (hd : star d=d) :
    StarPair a d (PSDFactory.compiled N).1 (PSDFactory.compiled N).2 := by
  unfold PSDFactory.compiled
  split_ifs with hN
  · exact ⟨by simp [unitRef,unitCircuit,PairRef.valid,Circuit.length],
      by simp [unitRef,unitCircuit,PairRef.value,Circuit.value,Circuit.eval,Gate.eval]⟩
  · have hf := frame_star N (by omega) ha hd
    have hg := gramStage_star hf.1 hf.2
    have eg := gramStage_extends (frame N).j (frame N).z (frame N).circuit
    have hv := residualStage_star (extend hf.1 eg)
      (fun i => extend (hf.2 i) eg) hg
    exact sos_star (by omega) hv

#print axioms frame_star
#print axioms compiled_star

end ADComplete.PSDPairStar
