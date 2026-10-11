import PaperVerifier.ADComplete.InstructionDistanceHeights

namespace ADComplete.InstructionHeights
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit

theorem pair_swap {c : Circuit} {p : PairRef} {B : ℕ} (h : PairBound c p B) :
    PairBound c p.swap B := ⟨PairRef.swap_valid h.1, h.2.2, h.2.1⟩

theorem pair_zero {c : Circuit} {B : ℕ} (hc : AllBound c B) :
    AllBound (pairZero c).1 B ∧ PairBound (pairZero c).1 (pairZero c).2 0 := by
  refine ⟨snoc_bound hc .zero (Nat.zero_le _), pairZero_valid _, ?_, ?_⟩ <;>
    simp only [pairZero, new_weight, gateWeight, le_refl]

theorem scalar_grade {c : Circuit} {one : PairRef} {B : ℕ}
    (hc : AllBound c B) (ho : PairBound c one 0) (he : 1 ≤ B) (b : ℤ) :
    AllBound (scalarBase c one b).1 B ∧ PairBound (scalarBase c one b).1
      (scalarBase c one b).2 1 := by
  have h : gateWeight (weights c) (.scale b one.forward) ≤ 1 := by
    change weight c one.forward+1 ≤ 1
    have ho' := ho.2.1
    omega
  refine ⟨snoc_bound hc _ (h.trans he), scalarBase_valid _ _ _, ?_, ?_⟩
  all_goals change weight (c.snoc (.scale b one.forward)) c.length ≤ 1
  all_goals rw [new_weight]; exact h

theorem power_grade (n : ℕ) {c : Circuit} {base one : PairRef} {B K : ℕ}
    (hc : AllBound c B) (hb : PairBound c base K) (ho : PairBound c one 0)
    (he : n*K ≤ B) :
    AllBound (pairPow c base one n).1 B ∧ PairBound (pairPow c base one n).1
      (pairPow c base one n).2 (n*K) := by
  induction n with
  | zero => simpa only [pairPow, Nat.zero_mul] using And.intro hc ho
  | succ n ih =>
    have ht := ih ((Nat.mul_le_mul_right K (Nat.le_succ n)).trans he)
    have h := pair_mul ht.1 (pair_extend hb (pairPow_extends _ _ _ _)) ht.2
      (by simpa only [Nat.succ_mul, Nat.add_comm K] using he)
    simpa only [pairPow, Nat.succ_mul, Nat.add_comm K] using h

theorem horner_grade (ps : List PairRef) {c : Circuit} {base : PairRef} {B K P : ℕ}
    (hc : AllBound c B) (hb : PairBound c base K)
    (hp : ∀ p ∈ ps, PairBound c p P) (he : P+ps.length*(K+1) ≤ B) :
    AllBound (pairHorner c base ps).1 B ∧ PairBound (pairHorner c base ps).1
      (pairHorner c base ps).2 (P+ps.length*(K+1)) := by
  induction ps with
  | nil =>
    have h := pair_zero hc
    exact ⟨h.1, pair_mono h.2 (Nat.zero_le _)⟩
  | cons p ps ih =>
    simp only [List.length_cons, Nat.succ_mul] at he ⊢
    have ht := ih (fun p h => hp p (List.mem_cons_of_mem _ h)) (by omega)
    have er := pairHorner_extends c base ps
    have gm := pair_mul ht.1 (pair_extend hb er) ht.2 (by omega)
    have em := er.trans (pairMul_extends (pairHorner c base ps).1 base (pairHorner c base ps).2)
    have ga := pair_add gm.1 (pair_extend (hp p (List.mem_cons_self)) em) gm.2 (by omega)
    exact ⟨ga.1, pair_mono ga.2 (by omega)⟩

theorem compress_grade {c : Circuit} {one a d j : PairRef} {P J M : ℕ}
    (hc : AllBound c (J+2*P+3*(M*M)+3*M+4))
    (ho : PairBound c one 0) (ha : PairBound c a 1) (hd : PairBound c d 1)
    (hj : PairBound c j J) (probes : List PairRef) (hM : probes.length = M)
    (hp : ∀ p ∈ probes, PairBound c p P) (b : ℤ) :
    AllBound (compress c one a d j b M probes).1 (J+2*P+3*(M*M)+3*M+4) ∧
      PairBound (compress c one a d j b M probes).1
        (compress c one a d j b M probes).2 (J+2*P+3*(M*M)+3*M+4) := by
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
  let q1 := pairMul s.1 j z.2.swap
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
  have eq2q : Extends q2.1 q.1 := pairMul_extends _ _ _
  have gb := scalar_grade hc ho (by omega) b
  have gst := power_grade M gb.1 gb.2 (pair_extend ho eb) (by simp only [Nat.mul_one]; nlinarith)
  have gbl := power_grade M gst.1 gst.2 (pair_extend ho es) (by simp only [Nat.mul_one]; nlinarith)
  have gbq := pair_mul gbl.1 gbl.2 gbl.2 (by simp only [Nat.mul_add, Nat.mul_succ]; omega)
  have gy := horner_grade probes gbq.1 (pair_extend gb.2 (ebs.trans (esbl.trans ebq)))
    (fun p h => pair_extend (hp p h) eq) (by simp only [hM, Nat.mul_succ]; omega)
  have gz := horner_grade probes gy.1 (pair_extend gst.2 (esbl.trans (ebq.trans eqy)))
    (fun p h => pair_extend (hp p h) ey) (by simp only [hM, Nat.mul_add, Nat.mul_succ]; omega)
  have gsa := pair_mul gz.1 (pair_extend gbl.2 (ebq.trans (eqy.trans eyz)))
    (pair_extend ha ez) (by simp only [Nat.mul_add, Nat.mul_succ]; omega)
  have gsd := pair_mul gsa.1 (pair_extend gbq.2 (eqy.trans (eyz.trans ezsa)))
    (pair_extend hd esa) (by simp only [Nat.mul_add, Nat.mul_succ]; omega)
  have gs1 := pair_add gsd.1 (pair_extend ho esd) (pair_extend gsa.2 easd) (by simp only [Nat.mul_add, Nat.mul_succ]; omega)
  have gs := pair_add gs1.1 gs1.2 (pair_extend gsd.2 eds1) (by simp only [Nat.mul_add, Nat.mul_succ]; omega)
  have gq1 := pair_mul gs.1 (pair_extend hj ecS)
    (pair_swap (pair_extend gz.2 (ezsa.trans (easd.trans (eds1.trans es1s))))) (by simp only [hM, Nat.mul_add, Nat.mul_succ]; omega)
  have gq2 := pair_mul gq1.1 gq1.2 (pair_extend gs.2 esq1) (by simp only [hM, Nat.mul_add, Nat.mul_succ]; omega)
  have gq := pair_mul gq2.1 gq2.2 (pair_extend gy.2
    (eyz.trans (ezsa.trans (easd.trans (eds1.trans (es1s.trans (esq1.trans eq12))))))) (by simp only [hM, Nat.mul_add, Nat.mul_succ]; omega)
  have gf := pair_add gq.1 gq.2 (pair_swap gq.2) (by simp only [hM, Nat.mul_add, Nat.mul_succ]; omega)
  exact ⟨gf.1, pair_mono gf.2 (by simp only [hM, Nat.mul_add, Nat.mul_succ]; omega)⟩

#print axioms compress_grade
end ADComplete.InstructionHeights
