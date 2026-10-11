import PaperVerifier.ADComplete.PSDBirdCompiler

namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.InstructionDegrees

def GradedRefs {k : ℕ} (c : Circuit) (F : Matrix (Fin k) (Fin k) PairRef) (D : ℕ) : Prop :=
  ∀ i j, PairBound c (F i j) D

theorem gradedRefs_extend {k : ℕ} {c t : Circuit} {F : Matrix (Fin k) (Fin k) PairRef} {D : ℕ}
    (h : GradedRefs c F D) (he : Extends c t) : GradedRefs t F D :=
  fun i j => pair_extend (h i j) he

theorem diagSum_grade {k : ℕ} {F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P : ℕ}
    (hc : AllBound c B) (hF : GradedRefs c F P) (hP : P ≤ B) (ls : List (Fin k)) :
    AllBound (diagSum F c ls).1 B ∧ PairBound (diagSum F c ls).1 (diagSum F c ls).2 P := by
  induction ls with
  | nil =>
    have h := pair_zero hc
    exact ⟨h.1, pair_mono h.2 (Nat.zero_le _)⟩
  | cons l ls ih =>
    have h := pair_add ih.1 (pair_extend (hF l l) (diagSum_extends F c ls)) ih.2
      (by simpa only [max_self] using hP)
    simpa only [diagSum, max_self] using h

theorem offSum_grade {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : GradedRefs c A D) (hF : GradedRefs c F P)
    (hPD : P+D ≤ B) (i j : Fin k) (ls : List (Fin k)) :
    AllBound (offSum A F i j c ls).1 B ∧
      PairBound (offSum A F i j c ls).1 (offSum A F i j c ls).2 (P+D) := by
  induction ls with
  | nil =>
    have h := pair_zero hc
    exact ⟨h.1, pair_mono h.2 (Nat.zero_le _)⟩
  | cons l ls ih =>
    have ex := offSum_extends A F i j c ls
    have hm := pair_mul ih.1 (pair_extend (hF i l) ex) (pair_extend (hA l j) ex) hPD
    have hs := pair_add hm.1 hm.2 (pair_extend ih.2 (pairMul_extends _ _ _))
      (by simpa only [max_self] using hPD)
    simpa only [offSum, max_self] using hs

theorem entry_grade {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : GradedRefs c A D) (hF : GradedRefs c F P)
    (hPD : P+D ≤ B) (i j : Fin k) :
    AllBound (entry A F i j c).1 B ∧ PairBound (entry A F i j c).1 (entry A F i j c).2 (P+D) := by
  let ds := diagSum F c (upper k i)
  let neg := pairScale ds.1 (-1) ds.2
  let l := pairMul neg.1 neg.2 (A i j)
  let r := offSum A F i j l.1 (upper k i)
  have eds : Extends c ds.1 := diagSum_extends F c _
  have eneg : Extends c neg.1 := eds.trans (pairScale_extends _ _ _)
  have el : Extends c l.1 := eneg.trans (pairMul_extends _ _ _)
  have hds := diagSum_grade hc hF (by omega) (upper k i)
  have hn := pair_scale hds.1 hds.2 (by omega) (-1)
  have hl := pair_mul hn.1 hn.2 (pair_extend (hA i j) eneg) hPD
  have hr := offSum_grade hl.1 (gradedRefs_extend hA el) (gradedRefs_extend hF el) hPD i j (upper k i)
  have hs := pair_add hr.1 (pair_extend hl.2 (offSum_extends A F i j _ _)) hr.2
    (by simpa only [max_self] using hPD)
  simpa only [entry, ds, neg, l, r, max_self] using hs

theorem scan_grade {k : ℕ} {A F O : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : GradedRefs c A D) (hF : GradedRefs c F P)
    (hO : GradedRefs c O (P+D)) (hPD : P+D ≤ B) (es : List (Fin k × Fin k)) :
    AllBound (scan A F c O es).1 B ∧ GradedRefs (scan A F c O es).1 (scan A F c O es).2 (P+D) := by
  induction es generalizing c O with
  | nil => exact ⟨hc,hO⟩
  | cons e es ih =>
    have he := entry_extends A F e.1 e.2 c
    have hr := entry_grade hc hA hF hPD e.1 e.2
    have hw : GradedRefs (entry A F e.1 e.2 c).1 (write O e (entry A F e.1 e.2 c).2) (P+D) := by
      intro i j
      unfold write
      split
      · exact hr.2
      · exact pair_extend (hO i j) he
    exact ih hr.1 (gradedRefs_extend hA he) (gradedRefs_extend hF he) hw

theorem stage_grade {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : GradedRefs c A D) (hF : GradedRefs c F P) (hPD : P+D ≤ B) :
    AllBound (stage A F c).1 B ∧ GradedRefs (stage A F c).1 (stage A F c).2 (P+D) := by
  have hz := pair_zero hc
  have he := pairZero_extends c
  exact scan_grade hz.1 (gradedRefs_extend hA he) (gradedRefs_extend hF he)
    (fun _ _ => pair_mono hz.2 (Nat.zero_le _)) hPD _

theorem iterate_grade {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : GradedRefs c A D) (hF : GradedRefs c F P)
    (t : ℕ) (hPD : P+t*D ≤ B) :
    AllBound (iterate A t c F).1 B ∧ GradedRefs (iterate A t c F).1 (iterate A t c F).2 (P+t*D) := by
  induction t generalizing c F P with
  | zero => simpa only [iterate, Nat.zero_mul, Nat.add_zero] using And.intro hc hF
  | succ t ih =>
    have hs := stage_grade hc hA hF (by rw [Nat.add_mul, Nat.one_mul] at hPD; omega)
    have he := stage_extends A F c
    have ht := ih hs.1 (gradedRefs_extend hA he) hs.2 (by rw [Nat.add_mul, Nat.one_mul] at hPD; omega)
    simpa only [iterate, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm D] using ht

/-- The final determinant order is k+1. Every newly emitted register obeys
the same degree bound as the determinant; preexisting registers are included. -/
theorem compiler_grade (k D : ℕ) {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {c : Circuit}
    (hc : AllBound c ((k+1)*D)) (hA : GradedRefs c A D) :
    AllBound (compiler k A c).1 ((k+1)*D) ∧
      PairBound (compiler k A c).1 (compiler k A c).2 ((k+1)*D) := by
  have ht := iterate_grade hc hA hA k (by rw [Nat.add_mul, Nat.one_mul]; omega)
  have hs := pair_scale ht.1 (ht.2 0 0) (by rw [Nat.add_mul, Nat.one_mul]; omega) ((-1 : ℤ)^k)
  exact ⟨hs.1, pair_mono hs.2 (by rw [Nat.add_mul, Nat.one_mul]; omega)⟩

#print axioms compiler_grade

theorem compiler_grade_global (k D : ℕ) {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    {c : Circuit} {B : ℕ} (hc : AllBound c B) (hA : GradedRefs c A D)
    (hB : (k+1)*D ≤ B) :
    AllBound (compiler k A c).1 B ∧
      PairBound (compiler k A c).1 (compiler k A c).2 ((k+1)*D) := by
  have ht := iterate_grade hc hA hA k (by rw [Nat.add_mul, Nat.one_mul] at hB; omega)
  have hs := pair_scale ht.1 (ht.2 0 0) (by rw [Nat.add_mul, Nat.one_mul] at hB; omega) ((-1 : ℤ)^k)
  exact ⟨hs.1, pair_mono hs.2 (by rw [Nat.add_mul, Nat.one_mul]; omega)⟩

#print axioms compiler_grade_global
end ADComplete.PSDBird
