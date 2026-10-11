import PaperVerifier.ADComplete.InstructionHeights

namespace ADComplete.InstructionHeights
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open CircuitAudit.DistanceCircuit

def DistanceGrade (s : CircuitAudit.DistanceCircuit.State) (t : ℕ) : Prop :=
  InitialGrade s.circuit ∧ PairBound s.circuit s.previous (4*(t-1)) ∧
  PairBound s.circuit s.current (4*t) ∧ PairBound s.circuit s.total (4*t) ∧
  PairBound s.circuit s.dm 2 ∧ PairBound s.circuit s.firstSum 2

theorem distance_seed_grade {c : Circuit} {B : ℕ} (hc : AllBound c B)
    (hi : InitialGrade c) (hB : 8 ≤ B) :
    AllBound (seed c).circuit B ∧ DistanceGrade (seed c) 2 := by
  let aa := pairMul c aRef aRef
  let nd := pairScale aa.1 (-1) dRef
  let p2 := pairAdd nd.1 aa.2 nd.2
  let s1 := pairAdd p2.1 oneRef aRef
  let s2 := pairAdd s1.1 s1.2 p2.2
  let ni := pairScale s2.1 (-1) oneRef
  let dm := pairAdd ni.1 dRef ni.2
  have eaa := pairMul_extends c aRef aRef
  have endr : Extends c nd.1 := eaa.trans (pairScale_extends _ _ _)
  have ep2 : Extends c p2.1 := endr.trans (pairAdd_extends _ _ _)
  have es1 : Extends c s1.1 := ep2.trans (pairAdd_extends _ _ _)
  have es2 : Extends c s2.1 := es1.trans (pairAdd_extends _ _ _)
  have eni : Extends c ni.1 := es2.trans (pairScale_extends _ _ _)
  have e := seed_extends c
  have gaa := pair_mul hc hi.2.1 hi.2.1 (show 1+1 ≤ B by omega)
  have gnd := pair_scale gaa.1 (pair_extend hi.2.2.1 eaa) (show 1+1 ≤ B by omega) (-1)
  have gp2 := pair_add gnd.1 (pair_extend gaa.2 (pairScale_extends _ _ _)) gnd.2
    (show max (1+1) (1+1)+1 ≤ B by omega)
  have gs1 := pair_add gp2.1 (pair_extend hi.1 ep2) (pair_extend hi.2.1 ep2)
    (show max 0 1+1 ≤ B by omega)
  have gs2 := pair_add gs1.1 gs1.2 (pair_extend gp2.2 (pairAdd_extends _ _ _))
    (show max (max 0 1+1) (max (1+1) (1+1)+1)+1 ≤ B by omega)
  have gni := pair_scale gs2.1 (pair_extend hi.1 es2) (show 0+1 ≤ B by omega) (-1)
  have gdm := pair_add gni.1 (pair_extend hi.2.2.1 eni) gni.2
    (show max 1 (0+1)+1 ≤ B by omega)
  refine ⟨gdm.1, initial_grade_extend hi e, pair_mono (pair_extend hi.2.1 e) (by norm_num), ?_, ?_, ?_, ?_⟩
  · exact pair_mono (pair_extend gp2.2
      ((pairAdd_extends _ _ _).trans ((pairAdd_extends _ _ _).trans
        ((pairScale_extends _ _ _).trans (pairAdd_extends _ _ _))))) (by omega)
  · exact pair_mono (pair_extend gs2.2
      ((pairScale_extends _ _ _).trans (pairAdd_extends _ _ _))) (by omega)
  · exact pair_mono gdm.2 (by omega)
  · exact pair_mono (pair_extend gs1.2 ((pairAdd_extends _ _ _).trans
      ((pairScale_extends _ _ _).trans (pairAdd_extends _ _ _)))) (by omega)

theorem distance_step_grade {s : CircuitAudit.DistanceCircuit.State} {t B : ℕ}
    (hc : AllBound s.circuit B) (h : DistanceGrade s t) (ht : 1 ≤ t) (hB : 4*(t+1) ≤ B) :
    AllBound (step s).circuit B ∧ DistanceGrade (step s) (t+1) := by
  let ac := pairMul s.circuit aRef s.current
  let dp := pairMul ac.1 s.dm s.previous
  let nd := pairScale dp.1 (-1) dp.2
  let nx := pairAdd nd.1 ac.2 nd.2
  have eac := pairMul_extends s.circuit aRef s.current
  have edp : Extends s.circuit dp.1 := eac.trans (pairMul_extends _ _ _)
  have endr : Extends ac.1 nd.1 := (pairMul_extends _ _ _).trans (pairScale_extends _ _ _)
  have enx : Extends s.circuit nx.1 := edp.trans
    ((pairScale_extends _ _ _).trans (pairAdd_extends _ _ _))
  have e := step_extends s
  have gac := pair_mul hc h.1.2.1 h.2.2.1 (show 1+4*t ≤ B by omega)
  have gdp := pair_mul gac.1 (pair_extend h.2.2.2.2.1 eac)
    (pair_extend h.2.1 eac) (show 2+4*(t-1) ≤ B by omega)
  have gnd := pair_scale gdp.1 gdp.2 (show 2+4*(t-1)+1 ≤ B by omega) (-1)
  have gnx := pair_add gnd.1 (pair_extend gac.2 endr) gnd.2
    (show max (1+4*t) (2+4*(t-1)+1)+1 ≤ B by omega)
  have gsu := pair_add gnx.1 (pair_extend h.2.2.2.1 enx) gnx.2
    (show max (4*t) (max (1+4*t) (2+4*(t-1)+1)+1)+1 ≤ B by omega)
  refine ⟨gsu.1, initial_grade_extend h.1 e, ?_, ?_, ?_,
    pair_extend h.2.2.2.2.1 e, pair_extend h.2.2.2.2.2 e⟩
  · change PairBound (step s).circuit s.current (4*(t+1-1))
    simpa only [Nat.add_sub_cancel] using pair_extend h.2.2.1 e
  · exact pair_mono (pair_extend gnx.2 (pairAdd_extends _ _ _)) (by omega)
  · exact pair_mono gsu.2 (by omega)

theorem distance_iterate_grade (n : ℕ) {s : CircuitAudit.DistanceCircuit.State} {t B : ℕ}
    (hc : AllBound s.circuit B) (h : DistanceGrade s t) (ht : 1 ≤ t) (hB : 4*(t+n) ≤ B) :
    AllBound (iterate n s).circuit B ∧ DistanceGrade (iterate n s) (t+n) := by
  induction n generalizing s t with
  | zero => simpa only [iterate, Nat.add_zero] using And.intro hc h
  | succ n ih =>
    have hs := distance_step_grade hc h ht (by omega)
    have hv := ih hs.1 hs.2 (by omega) (by omega)
    simpa only [iterate, Nat.add_assoc, Nat.add_comm 1 n] using hv

theorem distance_build_grade (N : ℕ) (hN : 2 ≤ N) {c : Circuit} {B : ℕ}
    (hc : AllBound c B) (hi : InitialGrade c) (hB : 4*N ≤ B) :
    AllBound (CircuitAudit.DistanceCircuit.build N c).1 B ∧
      PairBound (CircuitAudit.DistanceCircuit.build N c).1
        (CircuitAudit.DistanceCircuit.build N c).2 (4*N) := by
  have hs := distance_seed_grade hc hi (by omega)
  have ht := distance_iterate_grade (N-3) hs.1 hs.2 (by norm_num) (by omega)
  refine ⟨ht.1, ?_⟩
  unfold CircuitAudit.DistanceCircuit.build
  split
  · exact pair_mono ht.2.1.2.2.2 (by omega)
  · split
    · exact pair_mono ht.2.1.1 (by omega)
    · split
      · exact pair_mono ht.2.2.2.2.2.2 (by omega)
      · exact pair_mono ht.2.2.2.2.1 (by omega)

#print axioms distance_build_grade
end ADComplete.InstructionHeights
