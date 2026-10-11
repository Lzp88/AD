import PaperVerifier.ADComplete.PSDFactoryDefinition
import PaperVerifier.ADComplete.InstructionDistanceDegrees

namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDBird ADComplete.InstructionDegrees

def residualDegree (N : ℕ) : ℕ := (4*N-3)*(N-1)
def degreeBound (N : ℕ) : ℕ := 2*residualDegree N

theorem frame_extends (N : ℕ) : Extends (probePrefix N).circuit (frame N).circuit :=
  (CircuitAudit.DistanceCircuit.build_extends _ _).trans (PSDFoldCompiler.stage_extends _ _ _ _ _)

theorem frame_safe_grade (N : ℕ) (hN : 2≤N) {B : ℕ} (hB : 3*(N-1)+1≤B) :
    (frame N).circuit.safe ∧ AllBound (frame N).circuit B ∧
      PairBound (frame N).circuit (frame N).j (N-1) ∧
      ∀ i, PairBound (frame N).circuit ((frame N).z i) (N-1) := by
  have gp := probe_build_grade N (N-1)
  have hi := initial_grade_extend initial_grade (build_extends N (N-1))
  have hp : AllBound (probePrefix N).circuit B := all_mono gp.1 (by omega)
  have gj := distance_build_grade N hp hi (by omega) (by omega)
  have ex := CircuitAudit.DistanceCircuit.build_extends N (probePrefix N).circuit
  have hh := initial_grade_extend hi ex
  have hs := CircuitAudit.DistanceCircuit.build_safe N (prefix_safe N)
    (CircuitAudit.FullCompression.prefix_ready_empty N)
  have gf := PSDFoldCompiler.stage_safe_grade (N := N) (τ := tau N) (ps := (probePrefix N).probes.drop 1) hs gj.1 hh.1
    (fun p h => pair_extend (gp.2.2 p (List.mem_of_mem_drop h)) ex) (by omega)
  have ef := PSDFoldCompiler.stage_extends N (tau N) oneRef ((probePrefix N).probes.drop 1)
    (CircuitAudit.DistanceCircuit.build N (probePrefix N).circuit).1
  exact ⟨gf.1,gf.2.1,pair_extend gj.2 ef,gf.2.2⟩

theorem residualStep_extends {N : ℕ} (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (r : Fin (N-1)) (c : Circuit) :
    Extends c (residualStep Z G r c).1 :=
  (determinantBatch_extends _ _).trans (residual_extends _ _ _ _ _)

theorem residualStep_safe_grade {N : ℕ} {Z : Fin N → PairRef}
    {G : Matrix (Fin N) (Fin N) PairRef} {c : Circuit} {B H : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hZ : ∀ i, PairBound c (Z i) H)
    (hG : GradedRefs c G (4*H)) (r : Fin (N-1))
    (hB : H+(r.val+1)*(4*H)≤B) :
    (residualStep Z G r c).1.safe ∧ AllBound (residualStep Z G r c).1 B ∧
      PairBound (residualStep Z G r c).1 (residualStep Z G r c).2 (H+(r.val+1)*(4*H)) := by
  let A := G.submatrix (prefixIndex r) (prefixIndex r)
  let b := fun i => G (prefixIndex r i) (nextIndex r)
  have hA : GradedRefs c A (4*H) := fun i j => hG _ _
  have hbr : ∀ i, PairBound c (b i) (4*H) := fun i => hG _ _
  have hd := determinantBatch_safe_grade hc hb (cramerVariants_grade hA hbr) (by omega)
  have he := determinantBatch_extends (cramerVariants A b) c
  exact residual_safe_grade hd.1 hd.2.1 (pair_extend (hZ _) he) (hd.2.2 0)
    (fun i => pair_extend (hZ _) he) (fun i => hd.2.2 i.succ) hB

theorem residualStep_degree_le {N : ℕ} (r : Fin (N-1)) :
    (N-1)+(r.val+1)*(4*(N-1))≤residualDegree N := by
  have h : 4*(r.val+1)+1≤4*N-3 := by have := r.isLt; omega
  have hm := Nat.mul_le_mul_right (N-1) h
  unfold residualDegree
  convert hm using 1
  ring

theorem residualScan_extends {N : ℕ} (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (c : Circuit) (V : Fin N → PairRef)
    (rs : List (Fin (N-1))) : Extends c (residualScan Z G c V rs).1 := by
  induction rs generalizing c V with
  | nil => exact .refl _
  | cons r rs ih => exact (residualStep_extends _ _ _ _).trans (ih _ _)

theorem residualScan_safe_grade {N : ℕ} {Z : Fin N → PairRef}
    {G : Matrix (Fin N) (Fin N) PairRef} {c : Circuit} {V : Fin N → PairRef} {B : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hZ : ∀ i, PairBound c (Z i) (N-1))
    (hG : GradedRefs c G (4*(N-1))) (hV : ∀ i, PairBound c (V i) (residualDegree N))
    (hB : residualDegree N≤B) (rs : List (Fin (N-1))) :
    (residualScan Z G c V rs).1.safe ∧ AllBound (residualScan Z G c V rs).1 B ∧
      ∀ i, PairBound (residualScan Z G c V rs).1 ((residualScan Z G c V rs).2 i) (residualDegree N) := by
  induction rs generalizing c V with
  | nil => exact ⟨hc,hb,hV⟩
  | cons r rs ih =>
    have he := residualStep_extends Z G r c
    have hr := residualStep_safe_grade hc hb hZ hG r ((residualStep_degree_le r).trans hB)
    have hw : ∀ i, PairBound (residualStep Z G r c).1
        (vectorWrite V (nextIndex r) (residualStep Z G r c).2 i) (residualDegree N) := by
      intro i
      unfold vectorWrite
      split
      · exact pair_mono hr.2.2 (residualStep_degree_le r)
      · exact pair_extend (hV i) he
    exact ih hr.1 hr.2.1 (fun i => pair_extend (hZ i) he) (gradedRefs_extend hG he) hw

theorem square_extends (p : PairRef) (c : Circuit) : Extends c (square p c).1 := pairMul_extends _ _ _

theorem square_safe_grade {p : PairRef} {c : Circuit} {B P : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hp : PairBound c p P) (hB : 2*P≤B) :
    (square p c).1.safe ∧ AllBound (square p c).1 B ∧
      PairBound (square p c).1 (square p c).2 (2*P) := by
  have hd := pair_mul hb hp (pair_swap hp) (by omega)
  exact ⟨pairMul_safe hc hp.1 (PairRef.swap_valid hp.1),hd.1,by simpa only [square,two_mul] using hd.2⟩

theorem chainSquare_extends {N : ℕ} (V : Fin N → PairRef) (r : Fin (N-1)) (c : Circuit) :
    Extends c (chainSquare V r c).1 := (pairAdd_extends _ _ _).trans (square_extends _ _)

theorem chainSquare_safe_grade {N : ℕ} {V : Fin N → PairRef} {c : Circuit} {B P : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hV : ∀ i, PairBound c (V i) P) (hB : 2*P≤B)
    (r : Fin (N-1)) :
    (chainSquare V r c).1.safe ∧ AllBound (chainSquare V r c).1 B ∧
      PairBound (chainSquare V r c).1 (chainSquare V r c).2 (2*P) := by
  have hd := pair_add hb (hV (currentIndex r)) (hV (nextIndex r)) (by simpa only [max_self] using (show P≤B by omega))
  have hs := pairAdd_safe hc (hV (currentIndex r)).1 (hV (nextIndex r)).1
  simp only [max_self] at hd
  exact square_safe_grade hs hd.1 hd.2 hB

theorem chainSquareSum_extends {N : ℕ} (V : Fin N → PairRef) (c : Circuit) (rs : List (Fin (N-1))) :
    Extends c (chainSquareSum V c rs).1 := by
  induction rs with
  | nil => exact pairZero_extends c
  | cons r rs ih => exact ih.trans ((chainSquare_extends _ _ _).trans (pairAdd_extends _ _ _))

theorem chainSquareSum_safe_grade {N : ℕ} {V : Fin N → PairRef} {c : Circuit} {B P : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hV : ∀ i, PairBound c (V i) P) (hB : 2*P≤B)
    (rs : List (Fin (N-1))) :
    (chainSquareSum V c rs).1.safe ∧ AllBound (chainSquareSum V c rs).1 B ∧
      PairBound (chainSquareSum V c rs).1 (chainSquareSum V c rs).2 (2*P) := by
  induction rs with
  | nil => have hz := pair_zero hb; exact ⟨pairZero_safe hc,hz.1,pair_mono hz.2 (Nat.zero_le _)⟩
  | cons r rs ih =>
    have es := chainSquareSum_extends V c rs
    have hw := chainSquare_safe_grade ih.1 ih.2.1 (fun i => pair_extend (hV i) es) hB r
    have ew := chainSquare_extends V r (chainSquareSum V c rs).1
    have hf := pair_add hw.2.1 hw.2.2 (pair_extend ih.2.2 ew) (by simpa only [max_self] using hB)
    exact ⟨pairAdd_safe hw.1 hw.2.2.1 (PairRef.valid_extend ih.2.2.1 ew),hf.1,by simpa only [chainSquareSum,max_self] using hf.2⟩

theorem sos_safe_grade {N : ℕ} (hN : 0<N) {V : Fin N → PairRef} {c : Circuit} {P : ℕ}
    (hc : c.safe) (hb : AllBound c (2*P)) (hV : ∀ i, PairBound c (V i) P) :
    (sos hN V c).1.safe ∧ AllBound (sos hN V c).1 (2*P) ∧
      PairBound (sos hN V c).1 (sos hN V c).2 (2*P) := by
  have hs := chainSquareSum_safe_grade hc hb hV (le_refl _) (List.finRange (N-1))
  have es := chainSquareSum_extends V c (List.finRange (N-1))
  have hv := square_safe_grade hs.1 hs.2.1 (pair_extend (hV ⟨0,hN⟩) es) (le_refl _)
  have ev := square_extends (V ⟨0,hN⟩) (chainSquareSum V c (List.finRange (N-1))).1
  have hf := pair_add hv.2.1 hv.2.2 (pair_extend hs.2.2 ev) (by simp)
  exact ⟨pairAdd_safe hv.1 hv.2.2.1 (PairRef.valid_extend hs.2.2.1 ev),hf.1,by simpa only [sos,max_self] using hf.2⟩

/-- Complete N-only factory: safety and a degree bound for every register,
including the eager distance recurrence and all Bird temporary matrices. -/
theorem compiled_safe_degree (N : ℕ) (hN : 1≤N) :
    (compiled N).1.safe ∧ AllBound (compiled N).1 (degreeBound N) ∧
      PairBound (compiled N).1 (compiled N).2 (degreeBound N) := by
  by_cases h2 : N≤1
  · have h1 : N=1 := by omega
    subst N
    simp only [compiled_one,degreeBound,residualDegree]
    have hu : AllBound unitCircuit 0 := by
      apply snoc_bound (c := .empty)
      · intro i hi; simp [Circuit.length] at hi
      · simp [gateDegree]
    refine ⟨?_,hu,?_,?_,?_⟩
    · simp [unitCircuit,Circuit.safe,Gate.valid]
    · simp [unitRef,unitCircuit,PairRef.valid,Circuit.length]
    · simpa [unitRef] using hu 0 (by simp [unitCircuit,Circuit.length])
    · simpa [unitRef] using hu 0 (by simp [unitCircuit,Circuit.length])
  · have hn : 2≤N := by omega
    have hQ : N-1≤residualDegree N := by
      unfold residualDegree
      have hm := Nat.mul_le_mul_right (N-1) (show 1≤4*N-3 by omega)
      simpa only [Nat.one_mul] using hm
    have h4 : 4*(N-1)≤degreeBound N := by
      unfold degreeBound residualDegree
      have hm := Nat.mul_le_mul_right (N-1) (show 4≤2*(4*N-3) by omega)
      simpa only [Nat.mul_assoc] using hm
    have hf := frame_safe_grade N hn (B := degreeBound N) (by omega)
    have hg := gramStage_safe_grade hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 h4
    have eg := gramStage_extends (frame N).j (frame N).z (frame N).circuit
    have hv := residualScan_safe_grade hg.1 hg.2.1 (fun i => pair_extend (hf.2.2.2 i) eg) hg.2.2
      (fun _ => pair_mono (pair_extend hf.2.2.1 eg) hQ) (by unfold degreeBound; omega) (List.finRange (N-1))
    have hs := sos_safe_grade (show 0<N by omega) hv.1 hv.2.1 hv.2.2
    simpa only [compiled,dif_neg h2,residualStage,degreeBound] using hs

#print axioms compiled_safe_degree
end ADComplete.PSDFactory
