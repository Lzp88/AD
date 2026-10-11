import PaperVerifier.ADComplete.PSDFactoryHeights
import PaperVerifier.ADComplete.PSDFoldedBitBounds
import PaperVerifier.ADComplete.InstructionResources

/-! Scalar-label bounds for every instruction of the literal PSD factory. -/
namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDBird ADComplete.PSDFoldCompiler

namespace ScalarBounds
variable (S : Set ℤ)

theorem diagSum_constants {k : ℕ} (F : Matrix (Fin k) (Fin k) PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (ls : List (Fin k)) :
    (diagSum F c ls).1.constantsAllowed S := by
  induction ls with
  | nil => exact pairZero_constants S hc
  | cons l ls ih => exact pairAdd_constants S _ _ ih

theorem offSum_constants {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) {c : Circuit} (hc : c.constantsAllowed S) (ls : List (Fin k)) :
    (offSum A F i j c ls).1.constantsAllowed S := by
  induction ls with
  | nil => exact pairZero_constants S hc
  | cons l ls ih => exact pairAdd_constants S _ _ (pairMul_constants S _ _ ih)

theorem entry_constants {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S) :
    (entry A F i j c).1.constantsAllowed S := by
  exact pairAdd_constants S _ _ (offSum_constants S A F i j
    (pairMul_constants S _ _ (CircuitAudit.ProbeCircuit.pairScale_constants S _ _
      (diagSum_constants S F hc _) hneg)) _)

theorem birdScan_constants {k : ℕ} (A F O : Matrix (Fin k) (Fin k) PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S)
    (es : List (Fin k×Fin k)) : (PSDBird.scan A F c O es).1.constantsAllowed S := by
  induction es generalizing c O with
  | nil => exact hc
  | cons e es ih => exact ih _ (entry_constants S A F e.1 e.2 hc hneg)

theorem birdStage_constants {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S) :
    (PSDBird.stage A F c).1.constantsAllowed S :=
  birdScan_constants S A F _ (pairZero_constants S hc) hneg _

theorem birdIterate_constants {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (t : ℕ) {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S) :
    (PSDBird.iterate A t c F).1.constantsAllowed S := by
  induction t generalizing c F with
  | zero => exact hc
  | succ t ih => exact ih _ (birdStage_constants S A F hc hneg)

theorem birdCompiler_constants (k : ℕ) (A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S)
    (hsign : (-1 : ℤ)^k∈S) : (PSDBird.compiler k A c).1.constantsAllowed S :=
  CircuitAudit.ProbeCircuit.pairScale_constants S _ _ (birdIterate_constants S A A k hc hneg) hsign

theorem gramEntry_constants (j z w : PairRef) {c : Circuit} (hc : c.constantsAllowed S) :
    (gramEntry j z w c).1.constantsAllowed S :=
  pairMul_constants S _ _ (pairMul_constants S _ _ (pairMul_constants S _ _ hc))

theorem gramScan_constants {k : ℕ} (j : PairRef) (Z : Fin k → PairRef)
    (O : Matrix (Fin k) (Fin k) PairRef) {c : Circuit} (hc : c.constantsAllowed S)
    (es : List (Fin k×Fin k)) : (gramScan j Z c O es).1.constantsAllowed S := by
  induction es generalizing c O with
  | nil => exact hc
  | cons e es ih => exact ih _ (gramEntry_constants S j (Z e.1) (Z e.2) hc)

theorem gramStage_constants {k : ℕ} (j : PairRef) (Z : Fin k → PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) : (gramStage j Z c).1.constantsAllowed S :=
  gramScan_constants S j Z _ (pairZero_constants S hc) _

theorem determinantScan_constants {k m : ℕ}
    (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef) (O : Fin m → PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S)
    (hsign : (-1 : ℤ)^k∈S) (is : List (Fin m)) :
    (determinantScan A c O is).1.constantsAllowed S := by
  induction is generalizing c O with
  | nil => exact hc
  | cons i is ih => exact ih _ (birdCompiler_constants S k (A i) hc hneg hsign)

theorem determinantBatch_constants {k m : ℕ}
    (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S)
    (hsign : (-1 : ℤ)^k∈S) : (determinantBatch A c).1.constantsAllowed S :=
  determinantScan_constants S A _ (pairZero_constants S hc) hneg hsign _

theorem productSum_constants {ι : Type*} (Z D : ι → PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (is : List ι) :
    (productSum Z D c is).1.constantsAllowed S := by
  induction is with
  | nil => exact pairZero_constants S hc
  | cons i is ih => exact pairAdd_constants S _ _ (pairMul_constants S _ _ ih)

theorem residual_constants {k : ℕ} (z δ : PairRef) (Z D : Fin k → PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S) :
    (residual z δ Z D c).1.constantsAllowed S :=
  pairAdd_constants S _ _ (pairMul_constants S _ _
    (CircuitAudit.ProbeCircuit.pairScale_constants S _ _ (productSum_constants S Z D hc _) hneg))

theorem residualStep_constants {N : ℕ} (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (r : Fin (N-1))
    {c : Circuit} (hc : c.constantsAllowed S) (hneg : (-1 : ℤ)∈S)
    (hsign : (-1 : ℤ)^r.val∈S) : (residualStep Z G r c).1.constantsAllowed S :=
  residual_constants S _ _ _ _ (determinantBatch_constants S _ hc hneg hsign) hneg

theorem residualScan_constants {N : ℕ} (Z V : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) {c : Circuit} (hc : c.constantsAllowed S)
    (hneg : (-1 : ℤ)∈S) (hsign : ∀ k, (-1 : ℤ)^k∈S) (rs : List (Fin (N-1))) :
    (residualScan Z G c V rs).1.constantsAllowed S := by
  induction rs generalizing c V with
  | nil => exact hc
  | cons r rs ih => exact ih _ (residualStep_constants S Z G r hc hneg (hsign r.val))

theorem chainSquare_constants {N : ℕ} (V : Fin N → PairRef) (r : Fin (N-1))
    {c : Circuit} (hc : c.constantsAllowed S) : (chainSquare V r c).1.constantsAllowed S :=
  pairMul_constants S _ _ (pairAdd_constants S _ _ hc)

theorem chainSquareSum_constants {N : ℕ} (V : Fin N → PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (rs : List (Fin (N-1))) :
    (chainSquareSum V c rs).1.constantsAllowed S := by
  induction rs with
  | nil => exact pairZero_constants S hc
  | cons r rs ih => exact pairAdd_constants S _ _ (chainSquare_constants S V r ih)

theorem sos_constants {N : ℕ} (hN : 0<N) (V : Fin N → PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) : (sos hN V c).1.constantsAllowed S :=
  pairAdd_constants S _ _ (pairMul_constants S _ _ (chainSquareSum_constants S V hc _))

theorem foldOne_constants (τ : ℕ) (one : PairRef) (ps : List PairRef) (i : ℕ)
    {c : Circuit} (hc : c.constantsAllowed S) (hs : scalar τ i∈S) :
    (foldOne τ one ps i c).1.constantsAllowed S := by
  unfold foldOne
  split
  · exact hc
  · apply pairHorner_constants
    change c.constantsAllowed S ∧ scalar τ i∈S
    exact ⟨hc,hs⟩

theorem foldScan_constants {N : ℕ} (τ : ℕ) (one : PairRef) (ps : List PairRef)
    (O : Fin N → PairRef) {c : Circuit} (hc : c.constantsAllowed S)
    (hs : ∀ i : Fin N, scalar τ i.val∈S) (is : List (Fin N)) :
    (PSDFoldCompiler.scan τ one ps c O is).1.constantsAllowed S := by
  induction is generalizing c O with
  | nil => exact hc
  | cons i is ih => exact ih _ (foldOne_constants S τ one ps i.val hc (hs i))

theorem foldStage_constants (N τ : ℕ) (one : PairRef) (ps : List PairRef)
    {c : Circuit} (hc : c.constantsAllowed S) (hs : ∀ i : Fin N, scalar τ i.val∈S) :
    (PSDFoldCompiler.stage N τ one ps c).1.constantsAllowed S :=
  foldScan_constants S τ one ps _ hc hs _
end ScalarBounds

def scalarAllowed (N : ℕ) : Set ℤ := {z | z.natAbs≤2^(12*N^4)}

theorem compiled_constantsAllowed (N : ℕ) (hN : 1≤N) :
    (compiled N).1.constantsAllowed (scalarAllowed N) := by
  have hneg : (-1 : ℤ)∈scalarAllowed N := by
    simpa [scalarAllowed] using (Nat.one_le_two_pow (n := 12*N^4))
  have hsign : ∀ k, (-1 : ℤ)^k∈scalarAllowed N := by
    intro k
    simpa [scalarAllowed,Int.natAbs_pow] using (Nat.one_le_two_pow (n := 12*N^4))
  by_cases h2 : N≤1
  · simp only [compiled,dif_pos h2]
    simp [unitCircuit,Circuit.constantsAllowed,Gate.constantsAllowed]
  · have hp : (probePrefix N).circuit.constantsAllowed (scalarAllowed N) := by
      apply ADComplete.InstructionHeights.constants_mono (prefix_constants N)
      intro z hz
      have hz' := probeConstants_abs_bound N hN hz
      have h14 : N≤N^4 := by simpa using Nat.pow_le_pow_right hN (show 1≤4 by decide)
      have hNpow : N≤2^N := N.lt_two_pow_self.le
      have hb : N^3≤2^(12*N^4) := by
        calc
          N^3≤(2^N)^3 := Nat.pow_le_pow_left hNpow 3
          _ = 2^(3*N) := by rw [← pow_mul]; congr 1; omega
          _ ≤ 2^(12*N^4) := Nat.pow_le_pow_right (by decide) (by omega)
      have ha : z.natAbs≤N^3 := by
        rw [←Int.natCast_natAbs] at hz'
        exact_mod_cast hz'
      exact ha.trans hb
    have hj := CircuitAudit.DistanceCircuit.build_constants N (scalarAllowed N) hp hneg
    have hf := ScalarBounds.foldStage_constants (scalarAllowed N) N (tau N) oneRef
      ((probePrefix N).probes.drop 1) hj
      (fun i => folded_scalar_binary_bound N i.val hN i.isLt.le)
    change (frame N).circuit.constantsAllowed (scalarAllowed N) at hf
    have hg := ScalarBounds.gramStage_constants (scalarAllowed N) (frame N).j (frame N).z hf
    have hv := ScalarBounds.residualScan_constants (scalarAllowed N) (frame N).z
      (fun _ => (frame N).j) (gramStage (frame N).j (frame N).z (frame N).circuit).2 hg hneg hsign
      (List.finRange (N-1))
    have hs := ScalarBounds.sos_constants (scalarAllowed N) (show 0<N by omega)
      (residualStage (frame N).j (frame N).z
        (gramStage (frame N).j (frame N).z (frame N).circuit).2
        (gramStage (frame N).j (frame N).z (frame N).circuit).1).2 hv
    simpa only [compiled,dif_neg h2,residualStage] using hs

#print axioms compiled_constantsAllowed
end ADComplete.PSDFactory
