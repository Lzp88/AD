import PaperVerifier.ADComplete.InstructionCompressionDegrees
import PaperVerifier.ADComplete.InstructionResources
import PaperVerifier.ADComplete.CompiledReadout

/-! The full-representation fallback uses the original-order matrix inputs
and the literal shared probe/Horner DAG. The compression unit is I. -/
namespace ADComplete.FullRepresentationCompiler
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit CircuitAudit.Degrees
open ADComplete.InstructionDegrees
noncomputable section
set_option backward.isDefEq.respectTransparency false

def compiled (N : ℕ) (b : ℤ) : Result :=
  let p := probePrefix (N^2)
  compress p.circuit oneRef aRef dRef oneRef b p.probes.length p.probes

def expression (N : ℕ) (b : ℤ) : Expr := factored b .one (probeList (N^2) (N^2))

theorem compiled_safe (N : ℕ) (b : ℤ) : (compiled N b).1.safe := by
  have hp := CircuitAudit.FullCompression.prefix_ready_empty (N^2)
  exact compress_safe b _ (prefix_safe (N^2)) hp.1 hp.2.1 hp.2.2.1 hp.1
    (build_probes_valid (N^2) (N^2-1))

theorem compiled_value {R : Type*} [Ring R] (N : ℕ) (hN : 1≤N) (b : ℤ) (a d : R) :
    (compiled N b).2.value (compiled N b).1 a d=exprPair a d (expression N b) := by
  have hS : 1≤N^2 := by nlinarith
  have hp := CircuitAudit.FullCompression.prefix_ready_empty (N^2)
  have ep := CircuitAudit.FullCompression.prefix_extends_initial (N^2)
  have hv := compress_value a d b (probePrefix (N^2)).probes.length hp.1 hp.2.1
    hp.2.2.1 hp.1 (build_probes_valid (N^2) (N^2-1))
  apply hv.trans
  have hpv := prefix_probe_values (N^2) hS a d
  change (build (N^2) (N^2-1)).probes.map (fun p => p.value (probePrefix (N^2)).circuit a d)=
    (probeList (N^2) (N^2)).map (exprPair a d) at hpv
  rw [one_value a d ep,a_value a d ep,d_value a d ep,
    hpv,prefix_probe_count (N^2) hS]
  have he := CircuitAudit.FullCompression.compression_expr_pair a d b .one (probeList (N^2) (N^2))
  rw [probeList_length] at he
  exact he

theorem compiled_gate_bound (N : ℕ) (hN : 1≤N) (b : ℤ) :
    (compiled N b).1.length≤49*N^4 := by
  have hS : 1≤N^2 := by nlinarith
  have hp := prefix_gate_bound (N^2) hS
  have hm := ADComplete.InstructionHeights.prefix_count_le_square (N^2) hS
  simp only [compiled,compress_length]
  have he : (N^2)^2=N^4 := by ring
  rw [he] at hp hm
  have h14 : 1≤N^4 := Nat.one_le_pow _ _ hN
  omega

theorem compress_identity_grade {c : Circuit} {one a d : PairRef} {k : ℕ}
    (hc : AllBound c (2*k+1)) (ho : PairBound c one 0)
    (ha : PairBound c a 1) (hd : PairBound c d 1) (probes : List PairRef)
    (hp : ∀ p∈probes, PairBound c p k) (b : ℤ) (M : ℕ) :
    AllBound (compress c one a d one b M probes).1 (2*k+1) ∧
      PairBound (compress c one a d one b M probes).1
        (compress c one a d one b M probes).2 (2*k+1) := by
  let base := scalarBase c one b
  let stride := pairPow base.1 base.2 one M
  let block := pairPow stride.1 stride.2 one M
  let blockSq := pairMul block.1 block.2 block.2
  let y := pairHorner blockSq.1 base.2 probes
  let z := pairHorner y.1 stride.2 probes
  let sa := pairMul z.1 block.2 a
  let sd := pairMul sa.1 blockSq.2 d
  let s1 := pairAdd sd.1 one sa.2
  let s := pairAdd s1.1 s1.2 sd.2
  let q1 := pairMul s.1 one z.2.swap
  let q2 := pairMul q1.1 q1.2 s.2
  let q := pairMul q2.1 q2.2 y.2
  have eb := scalarBase_extends c one b
  have ebs : Extends base.1 stride.1 := pairPow_extends _ _ _ _
  have es : Extends c stride.1 := eb.trans ebs
  have esbl : Extends stride.1 block.1 := pairPow_extends _ _ _ _
  have ebl : Extends c block.1 := es.trans esbl
  have ebq : Extends block.1 blockSq.1 := pairMul_extends _ _ _
  have eq : Extends c blockSq.1 := ebl.trans ebq
  have eqy : Extends blockSq.1 y.1 := pairHorner_extends _ _ _
  have ey : Extends c y.1 := eq.trans eqy
  have eyz : Extends y.1 z.1 := pairHorner_extends _ _ _
  have ez : Extends c z.1 := ey.trans eyz
  have ezsa : Extends z.1 sa.1 := pairMul_extends _ _ _
  have esa : Extends c sa.1 := ez.trans ezsa
  have easd : Extends sa.1 sd.1 := pairMul_extends _ _ _
  have esd : Extends c sd.1 := esa.trans easd
  have eds1 : Extends sd.1 s1.1 := pairAdd_extends _ _ _
  have es1s : Extends s1.1 s.1 := pairAdd_extends _ _ _
  have ecS : Extends c s.1 := esd.trans (eds1.trans es1s)
  have esq1 : Extends s.1 q1.1 := pairMul_extends _ _ _
  have eq12 : Extends q1.1 q2.1 := pairMul_extends _ _ _
  have gb := scalar_grade hc ho b
  have gst := power_grade M gb.1 gb.2 (pair_extend ho eb)
  have gbl := power_grade M gst.1 gst.2 (pair_extend ho es)
  have gbq := pair_mul gbl.1 gbl.2 gbl.2 (by omega)
  have gy := horner_grade probes gbq.1 (pair_extend gb.2 (ebs.trans (esbl.trans ebq)))
    (fun p h => pair_extend (hp p h) eq) (by omega)
  have gz := horner_grade probes gy.1 (pair_extend gst.2 (esbl.trans (ebq.trans eqy)))
    (fun p h => pair_extend (hp p h) ey) (by omega)
  have gsa := pair_mul gz.1 (pair_extend gbl.2 (ebq.trans (eqy.trans eyz)))
    (pair_extend ha ez) (by omega)
  have gsd := pair_mul gsa.1 (pair_extend gbq.2 (eqy.trans (eyz.trans ezsa)))
    (pair_extend hd esa) (by omega)
  have gs1 := pair_add gsd.1 (pair_extend ho esd) (pair_extend gsa.2 easd) (by omega)
  have gs := pair_add gs1.1 gs1.2 (pair_extend gsd.2 eds1) (by omega)
  have gq1 := pair_mul gs.1 (pair_extend ho ecS)
    (pair_swap (pair_extend gz.2 (ezsa.trans (easd.trans (eds1.trans es1s))))) (by omega)
  have gq2 := pair_mul gq1.1 gq1.2 (pair_extend gs.2 esq1) (by omega)
  have gq := pair_mul gq2.1 gq2.2 (pair_extend gy.2
    (eyz.trans (ezsa.trans (easd.trans (eds1.trans (es1s.trans (esq1.trans eq12))))))) (by omega)
  have gf := pair_add gq.1 gq.2 (pair_swap gq.2) (by omega)
  exact ⟨gf.1,pair_mono gf.2 (by omega)⟩

theorem compiled_all_degrees (N : ℕ) (hN : 1≤N) (b : ℤ) :
    AllBound (compiled N b).1 (2*N^2-1) ∧ PairBound (compiled N b).1 (compiled N b).2 (2*N^2-1) := by
  have hS : 1≤N^2 := by nlinarith
  have gp := probe_build_grade (N^2) (N^2-1)
  have hi := initial_grade_extend initial_grade (build_extends (N^2) (N^2-1))
  have hp : AllBound (probePrefix (N^2)).circuit (2*(N^2-1)+1) := all_mono gp.1 (by omega)
  have hg := compress_identity_grade hp hi.1 hi.2.1 hi.2.2.1
    (probePrefix (N^2)).probes gp.2.2 b (probePrefix (N^2)).probes.length
  simpa only [compiled,show 2*(N^2-1)+1=2*N^2-1 by omega] using hg

#print axioms compiled_value
#print axioms compiled_gate_bound
#print axioms compiled_all_degrees
end
end ADComplete.FullRepresentationCompiler
