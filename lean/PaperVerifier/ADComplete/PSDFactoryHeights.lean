import PaperVerifier.ADComplete.PSDOperationHeights
import PaperVerifier.ADComplete.PSDFactoryCounts

namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit ADComplete.PSDBird
open ADComplete.InstructionHeights ADComplete.PSDBirdHeight ADComplete.PSDOperationHeight

def frameWeight (N : ℕ) : ℕ := 6*N^2
def detWeight (N : ℕ) : ℕ := 28*N^3
def residualWeight (N : ℕ) : ℕ := 35*N^3
def weightBound (N : ℕ) : ℕ := 100*N^3

theorem frame_height (N : ℕ) (hN : 2≤N) {B : ℕ} (hB : frameWeight N≤B) :
    AllBound (frame N).circuit B ∧ PairBound (frame N).circuit (frame N).j (frameWeight N) ∧
      ∀ i, PairBound (frame N).circuit ((frame N).z i) (frameWeight N) := by
  have hf : 4*N≤frameWeight N := by unfold frameWeight; nlinarith
  have gp := probe_build_grade N (N-1)
  have hi := initial_grade_extend initial_grade (build_extends N (N-1))
  have hp : AllBound (probePrefix N).circuit B := all_mono gp.1 (by
    apply max_le
    · unfold frameWeight at hB; nlinarith
    · unfold frameWeight at hB; nlinarith [Nat.sub_le N 1])
  have gj := distance_build_grade N hN hp hi (hf.trans hB)
  have ej := CircuitAudit.DistanceCircuit.build_extends N (probePrefix N).circuit
  have ih := initial_grade_extend hi ej
  have hm : M N≤N^2 := by unfold M; apply Nat.div_le_of_le_mul; nlinarith
  have hlen : ((probePrefix N).probes.drop 1).length=M N-1 := by
    rw [List.length_drop,prefix_probe_count N (by omega)]
    rfl
  have hz := foldStage_height (N := N) (τ := tau N) (ps := (probePrefix N).probes.drop 1)
    gj.1 ih.1 (fun p h => pair_extend (gp.2.2 p (List.mem_of_mem_drop h)) ej)
    (show 3*(N-1)+2*((probePrefix N).probes.drop 1).length≤frameWeight N by rw [hlen]; unfold frameWeight; nlinarith [Nat.sub_le N 1,Nat.sub_le (M N) 1])
    (by unfold frameWeight at hB; nlinarith) hB
  have ez := PSDFoldCompiler.stage_extends N (tau N) oneRef ((probePrefix N).probes.drop 1)
    (CircuitAudit.DistanceCircuit.build N (probePrefix N).circuit).1
  exact ⟨hz.1,pair_mono (pair_extend gj.2 ez) hf,hz.2⟩

theorem detHeight_bound {N : ℕ} (hN : 1≤N) (r : Fin (N-1)) :
    detHeight r.val (4*frameWeight N)≤detWeight N := by
  have hk : r.val+1≤N := by have := r.isLt; omega
  unfold detHeight frameWeight detWeight
  have hm := Nat.mul_le_mul (show r.val≤N-1 by omega)
    (show 4*(6*N^2)+(r.val+1)+2≤24*N^2+N+2 by omega)
  have he : N-1+1=N := by omega
  nlinarith

theorem residualStep_height {N : ℕ} {Z : Fin N → PairRef} {G : Matrix (Fin N) (Fin N) PairRef}
    {c : Circuit} {B : ℕ} (hN : 1≤N) (hb : AllBound c B)
    (hZ : ∀ i, PairBound c (Z i) (frameWeight N)) (hG : WeightedRefs c G (4*frameWeight N))
    (hB : residualWeight N≤B) (r : Fin (N-1)) :
    AllBound (residualStep Z G r c).1 B ∧
      PairBound (residualStep Z G r c).1 (residualStep Z G r c).2 (residualWeight N) := by
  have hD := detHeight_bound hN r
  have hDB : detWeight N≤residualWeight N := by unfold detWeight residualWeight; omega
  let A := G.submatrix (prefixIndex r) (prefixIndex r)
  let b := fun i => G (prefixIndex r i) (nextIndex r)
  have hd := determinantBatch_height hb (cramerVariants_height
    (show WeightedRefs c A (4*frameWeight N) from fun i j => hG _ _)
    (show ∀ i, PairBound c (b i) (4*frameWeight N) from fun i => hG _ _)) (hD.trans (hDB.trans hB))
  have ed := determinantBatch_extends (cramerVariants A b) c
  have hR : frameWeight N+detHeight r.val (4*frameWeight N)+(r.val+1)+2≤residualWeight N := by
    have hk : r.val+1≤N := by have := r.isLt; omega
    have hn : 2≤N := by have := r.isLt; omega
    have h23 : N^2≤N^3 := pow_le_pow_right₀ hN (by omega)
    have h13 : N≤N^3 := by simpa only [pow_one] using pow_le_pow_right₀ hN (show 1≤3 by omega)
    have hbig := Nat.pow_le_pow_left hn 3
    unfold frameWeight detWeight residualWeight at *
    nlinarith
  have hr := residual_height hd.1 (pair_extend (hZ (nextIndex r)) ed) (hd.2 0)
    (fun i => pair_extend (hZ (prefixIndex r i)) ed) (fun i => hd.2 i.succ) (hR.trans hB)
  exact ⟨hr.1,pair_mono hr.2 hR⟩

theorem residualScan_height {N : ℕ} {Z : Fin N → PairRef} {G : Matrix (Fin N) (Fin N) PairRef}
    {c : Circuit} {V : Fin N → PairRef} {B : ℕ} (hN : 1≤N) (hb : AllBound c B)
    (hZ : ∀ i, PairBound c (Z i) (frameWeight N)) (hG : WeightedRefs c G (4*frameWeight N))
    (hV : ∀ i, PairBound c (V i) (residualWeight N)) (hB : residualWeight N≤B) (rs : List (Fin (N-1))) :
    AllBound (residualScan Z G c V rs).1 B ∧
      ∀ i, PairBound (residualScan Z G c V rs).1 ((residualScan Z G c V rs).2 i) (residualWeight N) := by
  induction rs generalizing c V with
  | nil => exact ⟨hb,hV⟩
  | cons r rs ih =>
    have he := residualStep_extends Z G r c
    have hr := residualStep_height hN hb hZ hG hB r
    have hw : ∀ i, PairBound (residualStep Z G r c).1
        (vectorWrite V (nextIndex r) (residualStep Z G r c).2 i) (residualWeight N) := by
      intro i
      unfold vectorWrite
      split
      · exact hr.2
      · exact pair_extend (hV i) he
    exact ih hr.1 (fun i => pair_extend (hZ i) he) (weighted_extend hG he) hw

theorem square_height {p : PairRef} {c : Circuit} {B P : ℕ}
    (hb : AllBound c B) (hp : PairBound c p P) (hB : 2*P≤B) :
    AllBound (square p c).1 B ∧ PairBound (square p c).1 (square p c).2 (2*P) := by
  simpa only [square,two_mul] using pair_mul hb hp (pair_swap hp) (by omega)

theorem chainSquare_height {N : ℕ} {V : Fin N → PairRef} {c : Circuit} {B P : ℕ}
    (hb : AllBound c B) (hV : ∀ i, PairBound c (V i) P) (hB : 2*P+2≤B) (r : Fin (N-1)) :
    AllBound (chainSquare V r c).1 B ∧ PairBound (chainSquare V r c).1 (chainSquare V r c).2 (2*P+2) := by
  have ha := pair_add hb (hV (currentIndex r)) (hV (nextIndex r)) (by omega)
  simp only [max_self] at ha
  have hs := square_height ha.1 ha.2 (by omega)
  simpa only [chainSquare,Nat.mul_add,Nat.mul_one] using hs

theorem chainSquareSum_height {N : ℕ} {V : Fin N → PairRef} {c : Circuit} {B P : ℕ}
    (hb : AllBound c B) (hV : ∀ i, PairBound c (V i) P) (rs : List (Fin (N-1)))
    (hB : 2*P+2+rs.length≤B) :
    AllBound (chainSquareSum V c rs).1 B ∧
      PairBound (chainSquareSum V c rs).1 (chainSquareSum V c rs).2 (2*P+2+rs.length) := by
  induction rs with
  | nil => have hz := pair_zero hb; exact ⟨hz.1,pair_mono hz.2 (by omega)⟩
  | cons r rs ih =>
    have hs := ih (by simp only [List.length_cons] at hB; omega)
    have es := chainSquareSum_extends V c rs
    have hw := chainSquare_height hs.1 (fun i => pair_extend (hV i) es) (by simp only [List.length_cons] at hB; omega) r
    have ew := chainSquare_extends V r (chainSquareSum V c rs).1
    have hf := pair_add hw.1 hw.2 (pair_extend hs.2 ew) (by simp only [List.length_cons] at hB; omega)
    exact ⟨hf.1,pair_mono hf.2 (by simp only [List.length_cons]; omega)⟩

theorem sos_height {N : ℕ} (hN : 0<N) {V : Fin N → PairRef} {c : Circuit} {B P : ℕ}
    (hb : AllBound c B) (hV : ∀ i, PairBound c (V i) P) (hB : 2*P+N+2≤B) :
    AllBound (sos hN V c).1 B ∧ PairBound (sos hN V c).1 (sos hN V c).2 (2*P+N+2) := by
  have hs := chainSquareSum_height hb hV (List.finRange (N-1)) (by simp only [List.length_finRange]; omega)
  have es := chainSquareSum_extends V c (List.finRange (N-1))
  have hv := square_height hs.1 (pair_extend (hV ⟨0,hN⟩) es) (by omega)
  have ev := square_extends (V ⟨0,hN⟩) (chainSquareSum V c (List.finRange (N-1))).1
  have hf := pair_add hv.1 hv.2 (pair_extend hs.2 ev) (by simp only [List.length_finRange]; omega)
  exact ⟨hf.1,pair_mono hf.2 (by simp only [List.length_finRange]; omega)⟩

theorem compiled_weight_bound (N : ℕ) (hN : 1≤N) : AllBound (compiled N).1 (weightBound N) := by
  by_cases h2 : N≤1
  · have he : N=1 := by omega
    subst N
    rw [compiled_one]
    apply snoc_bound (c := .empty)
    · intro i hi; simp [Circuit.length] at hi
    · simp [gateWeight]
  · have hn : 2≤N := by omega
    have hF : frameWeight N≤weightBound N := by unfold frameWeight weightBound; nlinarith
    have hFR : frameWeight N≤residualWeight N := by unfold frameWeight residualWeight; nlinarith
    have h4 : 4*frameWeight N≤weightBound N := by unfold frameWeight weightBound; nlinarith
    have hR : residualWeight N≤weightBound N := by unfold residualWeight weightBound; omega
    have hf := frame_height N hn hF
    have hg := gramStage_height hf.1 hf.2.1 hf.2.2 h4
    have eg := gramStage_extends (frame N).j (frame N).z (frame N).circuit
    have hv := residualScan_height hN hg.1 (fun i => pair_extend (hf.2.2 i) eg) hg.2
      (fun _ => pair_mono (pair_extend hf.2.1 eg) hFR) hR (List.finRange (N-1))
    have h13 : N≤N^3 := by simpa only [pow_one] using pow_le_pow_right₀ hN (show 1≤3 by omega)
    have hbig := Nat.pow_le_pow_left hn 3
    have hs := sos_height (show 0<N by omega) hv.1 hv.2
      (show 2*residualWeight N+N+2≤weightBound N by unfold residualWeight weightBound; nlinarith)
    simpa only [compiled,dif_neg h2,residualStage] using hs.1

#print axioms compiled_weight_bound
end ADComplete.PSDFactory
