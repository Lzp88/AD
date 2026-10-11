import PaperVerifier.ADComplete.PSDBirdCompiler
import PaperVerifier.ADComplete.InstructionCompressionHeights

namespace ADComplete.PSDBirdHeight
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit ADComplete.PSDBird
open ADComplete.InstructionHeights

def WeightedRefs {k : ℕ} (c : Circuit) (F : Matrix (Fin k) (Fin k) PairRef) (D : ℕ) : Prop :=
  ∀ i j, PairBound c (F i j) D

theorem weighted_extend {k : ℕ} {c t : Circuit} {F : Matrix (Fin k) (Fin k) PairRef} {D : ℕ}
    (h : WeightedRefs c F D) (he : Extends c t) : WeightedRefs t F D :=
  fun i j => pair_extend (h i j) he

theorem diagSum_height {k : ℕ} {F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P : ℕ}
    (hc : AllBound c B) (hF : WeightedRefs c F P) (ls : List (Fin k)) (hB : P+ls.length≤B) :
    AllBound (diagSum F c ls).1 B ∧ PairBound (diagSum F c ls).1 (diagSum F c ls).2 (P+ls.length) := by
  induction ls with
  | nil =>
    have hz := pair_zero hc
    exact ⟨hz.1,pair_mono hz.2 (by omega)⟩
  | cons l ls ih =>
    have ht := ih (by simp only [List.length_cons] at hB; omega)
    have hr := pair_add ht.1 (pair_extend (hF l l) (diagSum_extends F c ls)) ht.2
      (by simp only [List.length_cons] at hB; omega)
    exact ⟨hr.1,pair_mono hr.2 (by simp only [List.length_cons]; omega)⟩

theorem offSum_height {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : WeightedRefs c A D) (hF : WeightedRefs c F P)
    (i j : Fin k) (ls : List (Fin k)) (hB : P+D+ls.length≤B) :
    AllBound (offSum A F i j c ls).1 B ∧
      PairBound (offSum A F i j c ls).1 (offSum A F i j c ls).2 (P+D+ls.length) := by
  induction ls with
  | nil => have hz := pair_zero hc; exact ⟨hz.1,pair_mono hz.2 (by omega)⟩
  | cons l ls ih =>
    have ht := ih (by simp only [List.length_cons] at hB; omega)
    have he := offSum_extends A F i j c ls
    have hm := pair_mul ht.1 (pair_extend (hF i l) he) (pair_extend (hA l j) he) (by simp only [List.length_cons] at hB; omega)
    have hs := pair_add hm.1 hm.2 (pair_extend ht.2 (pairMul_extends _ _ _))
      (by simp only [List.length_cons] at hB; omega)
    exact ⟨hs.1,pair_mono hs.2 (by simp only [List.length_cons]; omega)⟩

theorem entry_height {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : WeightedRefs c A D) (hF : WeightedRefs c F P)
    (hB : P+D+k+2≤B) (i j : Fin k) :
    AllBound (entry A F i j c).1 B ∧ PairBound (entry A F i j c).1 (entry A F i j c).2 (P+D+k+2) := by
  have hu : (upper k i).length≤k := by
    simpa [upper] using List.length_filter_le (fun l : Fin k => decide (i<l)) (List.finRange k)
  let ds := diagSum F c (upper k i)
  let neg := pairScale ds.1 (-1) ds.2
  let l := pairMul neg.1 neg.2 (A i j)
  let r := offSum A F i j l.1 (upper k i)
  have eds : Extends c ds.1 := diagSum_extends F c _
  have eneg : Extends c neg.1 := eds.trans (pairScale_extends _ _ _)
  have el : Extends c l.1 := eneg.trans (pairMul_extends _ _ _)
  have hds := diagSum_height hc hF (upper k i) (by omega)
  have hn := pair_scale hds.1 hds.2 (by omega) (-1)
  have hl := pair_mul hn.1 hn.2 (pair_extend (hA i j) eneg) (by omega)
  have hr := offSum_height hl.1 (weighted_extend hA el) (weighted_extend hF el) i j (upper k i) (by omega)
  have hs := pair_add hr.1 (pair_extend hl.2 (offSum_extends A F i j _ _)) hr.2 (by omega)
  exact ⟨hs.1,pair_mono hs.2 (by omega)⟩

theorem scan_height {k : ℕ} {A F O : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : WeightedRefs c A D) (hF : WeightedRefs c F P)
    (hO : WeightedRefs c O (P+D+k+2)) (hB : P+D+k+2≤B) (es : List (Fin k×Fin k)) :
    AllBound (scan A F c O es).1 B ∧ WeightedRefs (scan A F c O es).1 (scan A F c O es).2 (P+D+k+2) := by
  induction es generalizing c O with
  | nil => exact ⟨hc,hO⟩
  | cons e es ih =>
    have he := entry_extends A F e.1 e.2 c
    have hr := entry_height hc hA hF hB e.1 e.2
    have hw : WeightedRefs (entry A F e.1 e.2 c).1 (write O e (entry A F e.1 e.2 c).2) (P+D+k+2) := by
      intro i j
      unfold write
      split
      · exact hr.2
      · exact pair_extend (hO i j) he
    exact ih hr.1 (weighted_extend hA he) (weighted_extend hF he) hw

theorem stage_height {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : WeightedRefs c A D) (hF : WeightedRefs c F P) (hB : P+D+k+2≤B) :
    AllBound (stage A F c).1 B ∧ WeightedRefs (stage A F c).1 (stage A F c).2 (P+D+k+2) := by
  have hz := pair_zero hc
  have he := pairZero_extends c
  exact scan_height hz.1 (weighted_extend hA he) (weighted_extend hF he)
    (fun _ _ => pair_mono hz.2 (Nat.zero_le _)) hB _

theorem iterate_height {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef} {c : Circuit} {B P D : ℕ}
    (hc : AllBound c B) (hA : WeightedRefs c A D) (hF : WeightedRefs c F P)
    (t : ℕ) (hB : P+t*(D+k+2)≤B) :
    AllBound (iterate A t c F).1 B ∧ WeightedRefs (iterate A t c F).1 (iterate A t c F).2 (P+t*(D+k+2)) := by
  induction t generalizing c F P with
  | zero => simpa only [iterate,Nat.zero_mul,Nat.add_zero] using And.intro hc hF
  | succ t ih =>
    have hs := stage_height hc hA hF (by rw [Nat.add_mul,Nat.one_mul] at hB; omega)
    have he := stage_extends A F c
    have ht := ih hs.1 (weighted_extend hA he) hs.2 (by rw [Nat.add_mul,Nat.one_mul] at hB; omega)
    have eq : P+D+k+2+t*(D+k+2)=P+(t+1)*(D+k+2) := by ring
    simpa only [iterate,eq] using ht

theorem compiler_height (k D : ℕ) {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    {c : Circuit} {B : ℕ} (hc : AllBound c B) (hA : WeightedRefs c A D)
    (hB : D+k*(D+(k+1)+2)+1≤B) :
    AllBound (compiler k A c).1 B ∧
      PairBound (compiler k A c).1 (compiler k A c).2 (D+k*(D+(k+1)+2)+1) := by
  have ht := iterate_height hc hA hA k (by omega)
  exact pair_scale ht.1 (ht.2 0 0) hB ((-1 : ℤ)^k)

#print axioms compiler_height
end ADComplete.PSDBirdHeight
