import PaperVerifier.ADComplete.PSDGramCompiler

namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts
open ADComplete.InstructionDegrees

def vectorWrite {m : ℕ} {α : Type*} (O : Fin m → α) (i : Fin m) (v : α) : Fin m → α :=
  fun j => if j=i then v else O j

def determinantScan {k m : ℕ} (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef) :
    Circuit → (Fin m → PairRef) → List (Fin m) → Circuit × (Fin m → PairRef)
  | c,O,[] => (c,O)
  | c,O,i::is =>
    let r := compiler k (A i) c
    determinantScan A r.1 (vectorWrite O i r.2) is

theorem determinantScan_extends {k m : ℕ}
    (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef)
    (c : Circuit) (O : Fin m → PairRef) (is : List (Fin m)) :
    Extends c (determinantScan A c O is).1 := by
  induction is generalizing c O with
  | nil => exact .refl _
  | cons i is ih => exact (compiler_extends _ _ _).trans (ih _ _)

theorem determinantScan_length {k m : ℕ}
    (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef)
    (c : Circuit) (O : Fin m → PairRef) (is : List (Fin m)) :
    (determinantScan A c O is).1.length ≤ c.length+is.length*(15*(k+1)^4+2) := by
  induction is generalizing c O with
  | nil => simp [determinantScan]
  | cons i is ih =>
    have hr := compiler_gate_bound k (A i) c
    have ht := ih (compiler k (A i) c).1 (vectorWrite O i (compiler k (A i) c).2)
    simp only [determinantScan, List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem determinantScan_corner {k m n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    {g : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) ℝ} {c : Circuit}
    {O : Fin m → PairRef} {h : Fin m → ℝ}
    (hA : ∀ i, Corners n a d c (A i) (g i)) (hO : ∀ i, Corner n a d c (O i) (h i))
    (is : List (Fin m)) :
    ∀ i, Corner n a d (determinantScan A c O is).1 ((determinantScan A c O is).2 i)
      (if i∈is then (n : ℝ)^k*Matrix.det (g i) else h i) := by
  induction is generalizing c O h with
  | nil => simpa only [determinantScan, List.not_mem_nil, ite_false] using hO
  | cons i is ih =>
    let r := compiler k (A i) c
    have he : Extends c r.1 := compiler_extends _ _ _
    have hr := compiler_determinant k (hA i)
    have hw : ∀ j, Corner n a d r.1 (vectorWrite O i r.2 j)
        (vectorWrite h i ((n : ℝ)^k*Matrix.det (g i)) j) := by
      intro j
      unfold vectorWrite
      split
      · subst j; exact hr
      · exact corner_extend (hO j) he
    have hs := ih (fun i j l => corner_extend (hA i j l) he) hw
    intro j
    have hv := hs j
    by_cases hm : j∈is
    · simpa only [determinantScan, List.mem_cons, hm, or_true, ite_true] using hv
    · by_cases hji : j=i
      · subst j
        simpa only [determinantScan, List.mem_cons, hm, or_false, ite_false, vectorWrite, ite_true] using hv
      · simpa only [determinantScan, List.mem_cons, hm, hji, or_self, ite_false, vectorWrite] using hv

theorem determinantScan_safe_grade {k m : ℕ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {c : Circuit}
    {O : Fin m → PairRef} {B D : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hA : ∀ i, GradedRefs c (A i) D)
    (hO : ∀ i, PairBound c (O i) ((k+1)*D)) (hB : (k+1)*D≤B) (is : List (Fin m)) :
    (determinantScan A c O is).1.safe ∧ AllBound (determinantScan A c O is).1 B ∧
      ∀ i, PairBound (determinantScan A c O is).1 ((determinantScan A c O is).2 i) ((k+1)*D) := by
  induction is generalizing c O with
  | nil => exact ⟨hc,hb,hO⟩
  | cons i is ih =>
    have he := compiler_extends k (A i) c
    have hr := compiler_grade_global k D hb (hA i) hB
    have hs := compiler_safe_valid k hc (fun j l => (hA i j l).1)
    have hw : ∀ j, PairBound (compiler k (A i) c).1
        (vectorWrite O i (compiler k (A i) c).2 j) ((k+1)*D) := by
      intro j
      unfold vectorWrite
      split
      · exact hr.2
      · exact pair_extend (hO j) he
    exact ih hs.1 hr.1 (fun i => gradedRefs_extend (hA i) he) hw

def determinantBatch {k m : ℕ}
    (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef) (c : Circuit) :
    Circuit × (Fin m → PairRef) :=
  let z := pairZero c
  determinantScan A z.1 (fun _ => z.2) (List.finRange m)

theorem determinantBatch_extends {k m : ℕ}
    (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef) (c : Circuit) :
    Extends c (determinantBatch A c).1 :=
  (pairZero_extends c).trans (determinantScan_extends _ _ _ _)

theorem determinantBatch_length {k m : ℕ}
    (A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef) (c : Circuit) :
    (determinantBatch A c).1.length≤c.length+1+m*(15*(k+1)^4+2) := by
  have h := determinantScan_length A (pairZero c).1 (fun _ => (pairZero c).2) (List.finRange m)
  simpa only [determinantBatch, pairZero_length, List.length_finRange] using h

theorem determinantBatch_corner {k m n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    {g : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) ℝ} {c : Circuit}
    (hA : ∀ i, Corners n a d c (A i) (g i)) :
    ∀ i, Corner n a d (determinantBatch A c).1 ((determinantBatch A c).2 i)
      ((n : ℝ)^k*Matrix.det (g i)) := by
  have he := pairZero_extends c
  have h := determinantScan_corner (fun i j l => corner_extend (hA i j l) he)
    (fun _ => corner_zero n a d c) (List.finRange m)
  simpa only [determinantBatch, List.mem_finRange, ite_true] using h

theorem determinantBatch_safe_grade {k m : ℕ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {c : Circuit} {B D : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hA : ∀ i, GradedRefs c (A i) D) (hB : (k+1)*D≤B) :
    (determinantBatch A c).1.safe ∧ AllBound (determinantBatch A c).1 B ∧
      ∀ i, PairBound (determinantBatch A c).1 ((determinantBatch A c).2 i) ((k+1)*D) := by
  have hz := pair_zero hb
  have he := pairZero_extends c
  exact determinantScan_safe_grade (pairZero_safe hc) hz.1
    (fun i => gradedRefs_extend (hA i) he) (fun _ => pair_mono hz.2 (Nat.zero_le _)) hB _

/-- Index zero is the ordinary minor; successor indices are Cramer's
column-replacement variants. These are reference views, not new gates. -/
def cramerVariants {k : ℕ} {α : Type*}
    (A : Matrix (Fin (k+1)) (Fin (k+1)) α) (b : Fin (k+1) → α) :
    Fin (k+2) → Matrix (Fin (k+1)) (Fin (k+1)) α :=
  Fin.cases A (fun i => A.updateCol i b)

theorem cramerVariants_corners {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    {b : Fin (k+1) → PairRef} {g : Matrix (Fin (k+1)) (Fin (k+1)) ℝ} {v : Fin (k+1) → ℝ}
    (hA : Corners n a d c A g) (hb : ∀ i, Corner n a d c (b i) (v i)) :
    ∀ r, Corners n a d c (cramerVariants A b r) (cramerVariants g v r) := by
  intro r
  induction r using Fin.cases with
  | zero => exact hA
  | succ r =>
    intro i j
    by_cases hj : j=r
    · subst j; simpa [cramerVariants] using hb i
    · simpa [cramerVariants,Matrix.updateCol_apply,hj] using hA i j

theorem cramerVariants_grade {k : ℕ} {c : Circuit}
    {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {b : Fin (k+1) → PairRef} {D : ℕ}
    (hA : GradedRefs c A D) (hb : ∀ i, PairBound c (b i) D) :
    ∀ r, GradedRefs c (cramerVariants A b r) D := by
  intro r
  induction r using Fin.cases with
  | zero => exact hA
  | succ r =>
    intro i j
    by_cases hj : j=r
    · subst j; simpa [cramerVariants] using hb i
    · simpa [cramerVariants,Matrix.updateCol_apply,hj] using hA i j

#print axioms determinantBatch_corner
#print axioms determinantBatch_safe_grade
end ADComplete.PSDBird
