import PaperVerifier.ADComplete.PSDBirdCompiler

namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit

theorem diagSum_valid {k : ℕ} (F : Matrix (Fin k) (Fin k) PairRef)
    (c : Circuit) (ls : List (Fin k)) : (diagSum F c ls).2.valid (diagSum F c ls).1 := by
  cases ls
  · exact pairZero_valid _
  · exact pairAdd_valid _ _ _

theorem offSum_valid {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) (ls : List (Fin k)) :
    (offSum A F i j c ls).2.valid (offSum A F i j c ls).1 := by
  cases ls
  · exact pairZero_valid _
  · exact pairAdd_valid _ _ _

theorem entry_valid {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) : (entry A F i j c).2.valid (entry A F i j c).1 :=
  pairAdd_valid _ _ _

def ValidRefs {k : ℕ} (c : Circuit) (F : Matrix (Fin k) (Fin k) PairRef) : Prop :=
  ∀ i j, (F i j).valid c

theorem validRefs_extend {k : ℕ} {c t : Circuit} {F : Matrix (Fin k) (Fin k) PairRef}
    (h : ValidRefs c F) (he : Extends c t) : ValidRefs t F :=
  fun i j => PairRef.valid_extend (h i j) he

theorem diagSum_safe {k : ℕ} {F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit}
    (hc : c.safe) (hF : ValidRefs c F) (ls : List (Fin k)) : (diagSum F c ls).1.safe := by
  induction ls with
  | nil => exact pairZero_safe hc
  | cons l ls ih =>
    exact pairAdd_safe ih (PairRef.valid_extend (hF l l) (diagSum_extends F c ls)) (diagSum_valid F c ls)

theorem offSum_safe {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit}
    (hc : c.safe) (hA : ValidRefs c A) (hF : ValidRefs c F)
    (i j : Fin k) (ls : List (Fin k)) : (offSum A F i j c ls).1.safe := by
  induction ls with
  | nil => exact pairZero_safe hc
  | cons l ls ih =>
    have ex := offSum_extends A F i j c ls
    have hm := pairMul_safe ih (PairRef.valid_extend (hF i l) ex) (PairRef.valid_extend (hA l j) ex)
    exact pairAdd_safe hm (pairMul_valid _ _ _)
      (PairRef.valid_extend (offSum_valid A F i j c ls) (pairMul_extends _ _ _))

theorem entry_safe {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit}
    (hc : c.safe) (hA : ValidRefs c A) (hF : ValidRefs c F) (i j : Fin k) :
    (entry A F i j c).1.safe := by
  let ds := diagSum F c (upper k i)
  let neg := pairScale ds.1 (-1) ds.2
  let l := pairMul neg.1 neg.2 (A i j)
  let r := offSum A F i j l.1 (upper k i)
  have eds : Extends c ds.1 := diagSum_extends F c _
  have eneg : Extends c neg.1 := eds.trans (pairScale_extends _ _ _)
  have el : Extends c l.1 := eneg.trans (pairMul_extends _ _ _)
  have hsds := diagSum_safe hc hF (upper k i)
  have hsneg := pairScale_safe hsds (diagSum_valid F c _) (-1)
  have hsl := pairMul_safe hsneg (pairScale_valid _ _ _) (PairRef.valid_extend (hA i j) eneg)
  have hsr := offSum_safe hsl (validRefs_extend hA el) (validRefs_extend hF el) i j (upper k i)
  exact pairAdd_safe hsr (PairRef.valid_extend (pairMul_valid _ _ _) (offSum_extends A F i j _ _))
    (offSum_valid A F i j _ _)

theorem scan_safe_valid {k : ℕ} {A F O : Matrix (Fin k) (Fin k) PairRef} {c : Circuit}
    (hc : c.safe) (hA : ValidRefs c A) (hF : ValidRefs c F) (hO : ValidRefs c O)
    (es : List (Fin k × Fin k)) :
    (scan A F c O es).1.safe ∧ ValidRefs (scan A F c O es).1 (scan A F c O es).2 := by
  induction es generalizing c O with
  | nil => exact ⟨hc,hO⟩
  | cons e es ih =>
    have he := entry_extends A F e.1 e.2 c
    have hr := entry_safe hc hA hF e.1 e.2
    have hw : ValidRefs (entry A F e.1 e.2 c).1 (write O e (entry A F e.1 e.2 c).2) := by
      intro i j
      unfold write
      split
      · exact entry_valid A F e.1 e.2 c
      · exact PairRef.valid_extend (hO i j) he
    exact ih hr (validRefs_extend hA he) (validRefs_extend hF he) hw

theorem stage_safe_valid {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit}
    (hc : c.safe) (hA : ValidRefs c A) (hF : ValidRefs c F) :
    (stage A F c).1.safe ∧ ValidRefs (stage A F c).1 (stage A F c).2 :=
  scan_safe_valid (pairZero_safe hc) (validRefs_extend hA (pairZero_extends c))
    (validRefs_extend hF (pairZero_extends c)) (fun _ _ => pairZero_valid c) _

theorem iterate_safe_valid {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit}
    (hc : c.safe) (hA : ValidRefs c A) (hF : ValidRefs c F) (t : ℕ) :
    (iterate A t c F).1.safe ∧ ValidRefs (iterate A t c F).1 (iterate A t c F).2 := by
  induction t generalizing c F with
  | zero => exact ⟨hc,hF⟩
  | succ t ih =>
    have hs := stage_safe_valid hc hA hF
    exact ih hs.1 (validRefs_extend hA (stage_extends A F c)) hs.2

theorem compiler_safe_valid (k : ℕ) {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {c : Circuit}
    (hc : c.safe) (hA : ValidRefs c A) :
    (compiler k A c).1.safe ∧ (compiler k A c).2.valid (compiler k A c).1 := by
  have h := iterate_safe_valid hc hA hA k
  exact ⟨pairScale_safe h.1 (h.2 0 0) ((-1 : ℤ)^k), pairScale_valid _ _ _⟩

#print axioms compiler_safe_valid
end ADComplete.PSDBird
