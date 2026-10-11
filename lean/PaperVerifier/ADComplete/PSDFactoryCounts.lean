import PaperVerifier.ADComplete.PSDFactoryDegrees

namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit ADComplete.PSDBird

theorem residualStep_length {N : ℕ} (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (r : Fin (N-1)) (c : Circuit) :
    (residualStep Z G r c).1.length≤c.length+1+(r.val+2)*(15*(r.val+1)^4+2)+4*(r.val+1)+7 := by
  have hd := determinantBatch_length (cramerVariants
    (G.submatrix (prefixIndex r) (prefixIndex r)) (fun i => G (prefixIndex r i) (nextIndex r))) c
  simp only [residualStep,residual_length]
  omega

def stepCost (N : ℕ) : ℕ := 1+(N+1)*(15*N^4+2)+4*N+7

theorem residualStep_cost {N : ℕ} (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (r : Fin (N-1)) (c : Circuit) :
    (residualStep Z G r c).1.length≤c.length+stepCost N := by
  have h := residualStep_length Z G r c
  have hk : r.val+1≤N := by have := r.isLt; omega
  have hp := Nat.pow_le_pow_left hk 4
  have hm := Nat.mul_le_mul (show r.val+2≤N+1 by omega) (show 15*(r.val+1)^4+2≤15*N^4+2 by omega)
  unfold stepCost
  omega

theorem residualScan_length {N : ℕ} (Z : Fin N → PairRef)
    (G : Matrix (Fin N) (Fin N) PairRef) (c : Circuit) (V : Fin N → PairRef)
    (rs : List (Fin (N-1))) :
    (residualScan Z G c V rs).1.length≤c.length+rs.length*stepCost N := by
  induction rs generalizing c V with
  | nil => simp [residualScan]
  | cons r rs ih =>
    have hr := residualStep_cost Z G r c
    have ht := ih (residualStep Z G r c).1 (vectorWrite V (nextIndex r) (residualStep Z G r c).2)
    simp only [residualScan,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

@[simp] theorem square_length (p : PairRef) (c : Circuit) : (square p c).1.length=c.length+2 :=
  pairMul_length _ _ _

@[simp] theorem chainSquare_length {N : ℕ} (V : Fin N → PairRef) (r : Fin (N-1)) (c : Circuit) :
    (chainSquare V r c).1.length=c.length+4 := by
  simp only [chainSquare,square_length,pairAdd_length]

@[simp] theorem chainSquareSum_length {N : ℕ} (V : Fin N → PairRef) (c : Circuit) (rs : List (Fin (N-1))) :
    (chainSquareSum V c rs).1.length=c.length+1+6*rs.length := by
  induction rs with
  | nil => simp [chainSquareSum]
  | cons r rs ih => simp only [chainSquareSum,pairAdd_length,chainSquare_length,ih,List.length_cons]; omega

@[simp] theorem sos_length {N : ℕ} (hN : 0<N) (V : Fin N → PairRef) (c : Circuit) :
    (sos hN V c).1.length=c.length+5+6*(N-1) := by
  simp only [sos,pairAdd_length,square_length,chainSquareSum_length,List.length_finRange]
  omega

theorem frame_length (N : ℕ) (hN : 1≤N) :
    (frame N).circuit.length≤4+6*(N-1)*(N+2)+14+10*(N-3)+N*(2+4*(M N-1)) := by
  have h := PSDFoldCompiler.stage_length N (tau N) oneRef ((probePrefix N).probes.drop 1)
    (CircuitAudit.DistanceCircuit.build N (probePrefix N).circuit).1
  rw [List.length_drop,prefix_probe_count N hN,CircuitAudit.DistanceCircuit.build_length] at h
  have hp := build_exact_length N (N-1)
  have he : N-1+3=N+2 := by omega
  rw [he] at hp
  simpa only [frame,M,probePrefix,hp] using h

/-- An explicit polynomial-size bound for the full N-only program, not
an arithmetic expression expanded along permutation enumeration. -/
theorem compiled_gate_bound (N : ℕ) (hN : 1≤N) : (compiled N).1.length≤100*N^6 := by
  by_cases h2 : N≤1
  · have he : N=1 := by omega
    subst N
    simp [compiled_one,unitCircuit,Circuit.length]
  · have hn : 2≤N := by omega
    have hf := frame_length N hN
    have hm : M N≤N^2 := by
      unfold M
      apply Nat.div_le_of_le_mul
      nlinarith
    have hv := residualScan_length (frame N).z (gramStage (frame N).j (frame N).z (frame N).circuit).2
      (gramStage (frame N).j (frame N).z (frame N).circuit).1 (fun _ => (frame N).j) (List.finRange (N-1))
    rw [List.length_finRange,gramStage_length] at hv
    have hs := sos_length (show 0<N by omega)
      (residualStage (frame N).j (frame N).z (gramStage (frame N).j (frame N).z (frame N).circuit).2
        (gramStage (frame N).j (frame N).z (frame N).circuit).1).2
      (residualStage (frame N).j (frame N).z (gramStage (frame N).j (frame N).z (frame N).circuit).2
        (gramStage (frame N).j (frame N).z (frame N).circuit).1).1
    simp only [compiled,dif_neg h2]
    rw [hs]
    have hcost : stepCost N≤40*N^5 := by
      unfold stepCost
      have h4 : 1≤N^4 := one_le_pow₀ (by omega)
      have hpow : N^5=N*N^4 := by ring
      nlinarith
    have hmul := Nat.mul_le_mul (Nat.sub_le N 1) hcost
    have hframe : (frame N).circuit.length≤30*N^3 := by
      have hmp := Nat.mul_le_mul_left N (show 2+4*(M N-1)≤4*N^2+2 by omega)
      have hsmall := Nat.mul_le_mul (Nat.sub_le N 1) (le_refl (N+2))
      have ht := Nat.sub_le N 3
      nlinarith
    have h36 : N^3≤N^6 := pow_le_pow_right₀ (by omega) (by omega)
    have h26 : N^2≤N^6 := pow_le_pow_right₀ (by omega) (by omega)
    have h16 : N≤N^6 := by simpa only [pow_one] using pow_le_pow_right₀ (show 1≤N by omega) (show 1≤6 by omega)
    have h6 : 1≤N^6 := one_le_pow₀ (by omega)
    have hpow : N*N^5=N^6 := by ring
    have ht := Nat.sub_le N 1
    unfold residualStage
    nlinarith

#print axioms compiled_gate_bound
end ADComplete.PSDFactory
