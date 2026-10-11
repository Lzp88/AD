import PaperVerifier.CircuitAudit.DistanceCircuit

namespace CircuitAudit.DistanceCircuit

open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit

variable {R : Type*} [Ring R]

def pairExpr (a d : R) (p : Degrees.Expr) : R × R :=
  (p.eval a d, p.reverse.eval a d)

theorem pairScale_value_later (a d : R) {c t : Circuit} {p : PairRef}
    (hp : p.valid c) (k : ℤ) (h : Extends (pairScale c k p).1 t) :
    (pairScale c k p).2.value t a d =
      (k • (p.value t a d).1, k • (p.value t a d).2) := by
  rw [PairRef.value_extend (pairScale_valid _ _ _) h a d, pairScale_value a d hp k]
  rw [PairRef.value_extend hp ((pairScale_extends c k p).trans h) a d]

theorem expressionSum_append_eval (a d : R) (ps qs : List Degrees.Expr) :
    (Degrees.expressionSum (ps ++ qs)).eval a d =
      (Degrees.expressionSum ps).eval a d + (Degrees.expressionSum qs).eval a d := by
  induction ps with
  | nil => simp [Degrees.expressionSum, Degrees.Expr.eval]
  | cons p ps ih => simp [Degrees.expressionSum, Degrees.Expr.eval, ih, add_assoc]

theorem expressionSum_append_reverse_eval (a d : R) (ps qs : List Degrees.Expr) :
    (Degrees.expressionSum (ps ++ qs)).reverse.eval a d =
      (Degrees.expressionSum ps).reverse.eval a d +
        (Degrees.expressionSum qs).reverse.eval a d := by
  induction ps with
  | nil => simp [Degrees.expressionSum, Degrees.Expr.reverse, Degrees.Expr.eval]
  | cons p ps ih =>
    simp [Degrees.expressionSum, Degrees.Expr.reverse, Degrees.Expr.eval, ih, add_assoc]

theorem allOnes_succ_pair (n : ℕ) (a d : R) :
    pairExpr a d (Degrees.allOnes (n+1)) =
      addValue (pairExpr a d (Degrees.allOnes n)) (pairExpr a d (Degrees.distance n)) := by
  apply Prod.ext
  · simp [pairExpr, Degrees.allOnes, List.range_succ, List.map_append,
      expressionSum_append_eval, Degrees.expressionSum, Degrees.Expr.eval, addValue]
  · simp [pairExpr, Degrees.allOnes, List.range_succ, List.map_append,
      expressionSum_append_reverse_eval, Degrees.expressionSum, Degrees.Expr.reverse,
      Degrees.Expr.eval, addValue]

theorem distance_next_pair (k : ℕ) (a d : R) :
    pairExpr a d (Degrees.distance (k+3)) =
      addValue (mulValue (a,a) (pairExpr a d (Degrees.distance (k+2))))
        ((-1 : ℤ) • (mulValue (d-1,d-1) (pairExpr a d (Degrees.distance (k+1)))).1,
         (-1 : ℤ) • (mulValue (d-1,d-1) (pairExpr a d (Degrees.distance (k+1)))).2) := by
  simp [pairExpr, Degrees.distance, Degrees.Expr.eval, Degrees.Expr.reverse,
    addValue, mulValue, sub_eq_add_neg]

def Values (s : State) (k : ℕ) (a d : R) : Prop :=
  s.previous.value s.circuit a d = pairExpr a d (Degrees.distance (k+1)) ∧
  s.current.value s.circuit a d = pairExpr a d (Degrees.distance (k+2)) ∧
  s.total.value s.circuit a d = pairExpr a d (Degrees.allOnes (k+3)) ∧
  s.dm.value s.circuit a d = (d-1,d-1) ∧
  s.firstSum.value s.circuit a d = (1+a,1+a)

theorem seed_values (a d : R) {c : Circuit} (h : ProbeCircuit.Ready c [])
    (he : Extends initial c) : Values (seed c) 0 a d := by
  let aa := pairMul c aRef aRef
  let nd := pairScale aa.1 (-1) dRef
  let p2 := pairAdd nd.1 aa.2 nd.2
  let s1 := pairAdd p2.1 oneRef aRef
  let s2 := pairAdd s1.1 s1.2 p2.2
  let ni := pairScale s2.1 (-1) oneRef
  let dm := pairAdd ni.1 dRef ni.2
  have eni : Extends ni.1 dm.1 := pairAdd_extends _ _ _
  have es2 : Extends s2.1 dm.1 := (pairScale_extends _ _ _).trans eni
  have es1 : Extends s1.1 dm.1 := (pairAdd_extends _ _ _).trans es2
  have ep2 : Extends p2.1 dm.1 := (pairAdd_extends _ _ _).trans es1
  have endRef : Extends nd.1 dm.1 := (pairAdd_extends _ _ _).trans ep2
  have eaa : Extends aa.1 dm.1 := (pairScale_extends _ _ _).trans endRef
  have ec : Extends c dm.1 := (pairMul_extends _ _ _).trans eaa
  have hf := he.trans ec
  have vaa := pairMul_value_later a d h.2.1 h.2.1 eaa
  rw [a_value a d hf] at vaa
  have vnd := pairScale_value_later a d
    (PairRef.valid_extend h.2.2.1 (pairMul_extends _ _ _)) (-1) endRef
  rw [d_value a d hf] at vnd
  have vp2 := pairAdd_value_later a d
    (PairRef.valid_extend (pairMul_valid _ _ _) (pairScale_extends _ _ _))
    (pairScale_valid _ _ _) ep2
  rw [vaa, vnd] at vp2
  have vs1 := pairAdd_value_later a d
    (PairRef.valid_extend h.1 ((pairMul_extends _ _ _).trans
      ((pairScale_extends _ _ _).trans (pairAdd_extends _ _ _))))
    (PairRef.valid_extend h.2.1 ((pairMul_extends _ _ _).trans
      ((pairScale_extends _ _ _).trans (pairAdd_extends _ _ _)))) es1
  rw [one_value a d hf, a_value a d hf] at vs1
  have vs2 := pairAdd_value_later a d (pairAdd_valid _ _ _)
    (PairRef.valid_extend (pairAdd_valid _ _ _) (pairAdd_extends _ _ _)) es2
  rw [vs1, vp2] at vs2
  have vni := pairScale_value_later a d
    (PairRef.valid_extend h.1
      ((pairMul_extends _ _ _).trans ((pairScale_extends _ _ _).trans
      ((pairAdd_extends _ _ _).trans ((pairAdd_extends _ _ _).trans
      (pairAdd_extends _ _ _)))))) (-1) eni
  rw [one_value a d hf] at vni
  have vdm := pairAdd_value_later a d (PairRef.valid_extend h.2.2.1
      ((pairMul_extends _ _ _).trans ((pairScale_extends _ _ _).trans
      ((pairAdd_extends _ _ _).trans ((pairAdd_extends _ _ _).trans
      ((pairAdd_extends _ _ _).trans (pairScale_extends _ _ _)))))))
    (pairScale_valid _ _ _) (Extends.refl dm.1)
  rw [d_value a d hf, vni] at vdm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [seed, pairExpr, Degrees.distance, Degrees.Expr.eval, Degrees.Expr.reverse]
      using a_value a d hf
  · simpa [seed, Values, pairExpr, Degrees.distance, Degrees.Expr.eval,
      Degrees.Expr.reverse, addValue, mulValue] using vp2
  · simpa [seed, pairExpr, Degrees.allOnes, List.range_succ, Degrees.expressionSum,
      Degrees.distance, Degrees.Expr.eval, Degrees.Expr.reverse,
      addValue, mulValue, add_assoc] using vs2
  · simpa [seed, sub_eq_add_neg, addValue] using vdm
  · simpa [seed, addValue] using vs1

theorem step_values (a d : R) {s : State} {k : ℕ} (h : Ready s)
    (he : Extends initial s.circuit) (hv : Values s k a d) : Values (step s) (k+1) a d := by
  rcases h with ⟨ho, ha, hd, hz, hp, hc, ht, hm, hf⟩
  rcases hv with ⟨vp, vc, vt, vm, vf⟩
  let ac := pairMul s.circuit aRef s.current
  let dp := pairMul ac.1 s.dm s.previous
  let nd := pairScale dp.1 (-1) dp.2
  let nx := pairAdd nd.1 ac.2 nd.2
  let su := pairAdd nx.1 s.total nx.2
  have enx : Extends nx.1 su.1 := pairAdd_extends _ _ _
  have endRef : Extends nd.1 su.1 := (pairAdd_extends _ _ _).trans enx
  have edp : Extends dp.1 su.1 := (pairScale_extends _ _ _).trans endRef
  have eac : Extends ac.1 su.1 := (pairMul_extends _ _ _).trans edp
  have ec : Extends s.circuit su.1 := (pairMul_extends _ _ _).trans eac
  have hinitial := he.trans ec
  have vc' := PairRef.value_extend hc ec a d
  rw [vc] at vc'
  have vp' := PairRef.value_extend hp ec a d
  rw [vp] at vp'
  have vt' := PairRef.value_extend ht ec a d
  rw [vt] at vt'
  have vm' := PairRef.value_extend hm ec a d
  rw [vm] at vm'
  have vf' := PairRef.value_extend hf ec a d
  rw [vf] at vf'
  have vac := pairMul_value_later a d ha hc eac
  rw [a_value a d hinitial, vc'] at vac
  have vdp := pairMul_value_later a d (PairRef.valid_extend hm (pairMul_extends _ _ _))
    (PairRef.valid_extend hp (pairMul_extends _ _ _)) edp
  rw [vm', vp'] at vdp
  have vnd := pairScale_value_later a d (pairMul_valid _ _ _) (-1) endRef
  rw [vdp] at vnd
  have vnx := pairAdd_value_later a d
    (PairRef.valid_extend (pairMul_valid _ _ _)
      ((pairMul_extends _ _ _).trans (pairScale_extends _ _ _)))
    (pairScale_valid _ _ _) enx
  rw [vac, vnd, ← distance_next_pair k a d] at vnx
  have vsu := pairAdd_value_later a d (PairRef.valid_extend ht
      ((pairMul_extends _ _ _).trans ((pairMul_extends _ _ _).trans
      ((pairScale_extends _ _ _).trans (pairAdd_extends _ _ _)))))
    (pairAdd_valid _ _ _) (Extends.refl su.1)
  rw [vt', vnx, ← allOnes_succ_pair (k+3) a d] at vsu
  exact ⟨vc', vnx, vsu, vm', vf'⟩

theorem iterate_values (n k : ℕ) (a d : R) {s : State} (h : Ready s)
    (he : Extends initial s.circuit) (hv : Values s k a d) :
    Values (iterate n s) (k+n) a d := by
  induction n generalizing k s with
  | zero => simpa [iterate] using hv
  | succ n ih =>
      have hv' := step_values a d h he hv
      have hx := ih (k+1) (step_ready h) (he.trans (step_extends s)) hv'
      simpa [iterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx

theorem build_value (N : ℕ) (a d : R) {c : Circuit} (h : ProbeCircuit.Ready c [])
    (he : Extends initial c) :
    (build N c).2.value (build N c).1 a d = pairExpr a d (Degrees.allOnes N) := by
  have hs := seed_values a d h he
  have hf := he.trans (seed_extends c)
  rcases N with _ | N
  · simpa [build, iterate, pairExpr, Degrees.allOnes, List.range_succ, Degrees.expressionSum,
      Degrees.Expr.eval, Degrees.Expr.reverse] using zero_value a d hf
  rcases N with _ | N
  · simpa [build, iterate, pairExpr, Degrees.allOnes, List.range_succ, Degrees.expressionSum,
      Degrees.distance, Degrees.Expr.eval, Degrees.Expr.reverse] using one_value a d hf
  rcases N with _ | k
  · simpa [build, iterate, pairExpr, Degrees.allOnes, List.range_succ, Degrees.expressionSum,
      Degrees.distance, Degrees.Expr.eval, Degrees.Expr.reverse] using hs.2.2.2.2
  · have hv := iterate_values k 0 a d (seed_ready h) hf hs
    simpa [build, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hv.2.2.1

#print axioms build_value

end CircuitAudit.DistanceCircuit
