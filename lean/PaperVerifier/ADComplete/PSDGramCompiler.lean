import PaperVerifier.ADComplete.PSDGramEntry

namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts
open ADComplete.PSDHomogeneousLift ADComplete.InstructionDegrees

def gramScan {k : ℕ} (j : PairRef) (Z : Fin k → PairRef) :
    Circuit → Matrix (Fin k) (Fin k) PairRef → List (Fin k × Fin k) →
      Circuit × Matrix (Fin k) (Fin k) PairRef
  | c, O, [] => (c,O)
  | c, O, e::es =>
    let r := gramEntry j (Z e.1) (Z e.2) c
    gramScan j Z r.1 (write O e r.2) es

theorem gramScan_extends {k : ℕ} (j : PairRef) (Z : Fin k → PairRef)
    (c : Circuit) (O : Matrix (Fin k) (Fin k) PairRef) (es : List (Fin k × Fin k)) :
    Extends c (gramScan j Z c O es).1 := by
  induction es generalizing c O with
  | nil => exact .refl _
  | cons e es ih => exact (gramEntry_extends _ _ _ _).trans (ih _ _)

@[simp] theorem gramScan_length {k : ℕ} (j : PairRef) (Z : Fin k → PairRef)
    (c : Circuit) (O : Matrix (Fin k) (Fin k) PairRef) (es : List (Fin k × Fin k)) :
    (gramScan j Z c O es).1.length = c.length+6*es.length := by
  induction es generalizing c O with
  | nil => simp [gramScan]
  | cons e es ih => simp only [gramScan, ih, gramEntry_length, List.length_cons]; omega

theorem gramScan_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {j : PairRef} {Z : Fin k → PairRef} {O : Matrix (Fin k) (Fin k) PairRef}
    {z : Fin k → Matrix (Fin n) (Fin n) ℝ} {h : Matrix (Fin k) (Fin k) ℝ}
    (hj : Corner n a d c j 1) (hZ : ∀ i, AdjointValue n a d c (Z i) (z i))
    (hO : Corners n a d c O h) (es : List (Fin k × Fin k)) :
    Corners n a d (gramScan j Z c O es).1 (gramScan j Z c O es).2
      (fun i l => if (i,l) ∈ es then gramScalar n (z i) (z l) else h i l) := by
  induction es generalizing c O h with
  | nil => simpa only [gramScan, List.not_mem_nil, ite_false] using hO
  | cons e es ih =>
    let r := gramEntry j (Z e.1) (Z e.2) c
    have he : Extends c r.1 := gramEntry_extends _ _ _ _
    have hr := gramEntry_corner hj (hZ e.1) (hZ e.2)
    have hw : Corners n a d r.1 (write O e r.2) (write h e (gramScalar n (z e.1) (z e.2))) := by
      intro i l
      by_cases hil : (i,l)=e
      · obtain rfl : e=(i,l) := hil.symm
        simpa only [write, ite_true] using hr
      · simpa only [write, hil, ite_false] using corner_extend (hO i l) he
    have hs := ih (corner_extend hj he) (fun i => adjoint_extend (hZ i) he) hw
    intro i l
    have hv := hs i l
    by_cases hm : (i,l) ∈ es
    · simpa only [gramScan, List.mem_cons, hm, or_true, ite_true] using hv
    · by_cases hil : (i,l)=e
      · obtain rfl : e=(i,l) := hil.symm
        simpa only [gramScan, List.mem_cons, hm, or_false, ite_false, write, ite_true] using hv
      · simpa only [gramScan, List.mem_cons, hm, hil, or_self, ite_false, write] using hv

def gramStage {k : ℕ} (j : PairRef) (Z : Fin k → PairRef) (c : Circuit) :
    Circuit × Matrix (Fin k) (Fin k) PairRef :=
  let b := pairZero c
  gramScan j Z b.1 (fun _ _ => b.2) (allPairs k)

theorem gramStage_extends {k : ℕ} (j : PairRef) (Z : Fin k → PairRef) (c : Circuit) :
    Extends c (gramStage j Z c).1 :=
  (pairZero_extends c).trans (gramScan_extends _ _ _ _ _)

@[simp] theorem gramStage_length {k : ℕ} (j : PairRef) (Z : Fin k → PairRef) (c : Circuit) :
    (gramStage j Z c).1.length = c.length+1+6*(k*k) := by
  have h := gramScan_length j Z (pairZero c).1 (fun _ _ => (pairZero c).2) (allPairs k)
  rw [pairZero_length, allPairs_length] at h
  exact h

theorem gramStage_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {j : PairRef} {Z : Fin k → PairRef} {z : Fin k → Matrix (Fin n) (Fin n) ℝ}
    (hj : Corner n a d c j 1) (hZ : ∀ i, AdjointValue n a d c (Z i) (z i)) :
    Corners n a d (gramStage j Z c).1 (gramStage j Z c).2
      (fun i l => gramScalar n (z i) (z l)) := by
  have he := pairZero_extends c
  have h := gramScan_corner (corner_extend hj he) (fun i => adjoint_extend (hZ i) he)
    (fun _ _ => corner_zero n a d c) (allPairs k)
  simpa only [gramStage, allPairs_mem, ite_true] using h

theorem gramScan_safe_grade {k : ℕ} {c : Circuit} {j : PairRef} {Z : Fin k → PairRef}
    {O : Matrix (Fin k) (Fin k) PairRef} {B H : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hj : PairBound c j H)
    (hZ : ∀ i, PairBound c (Z i) H) (hO : GradedRefs c O (4*H))
    (hB : 4*H ≤ B) (es : List (Fin k × Fin k)) :
    (gramScan j Z c O es).1.safe ∧ AllBound (gramScan j Z c O es).1 B ∧
      GradedRefs (gramScan j Z c O es).1 (gramScan j Z c O es).2 (4*H) := by
  induction es generalizing c O with
  | nil => exact ⟨hc,hb,hO⟩
  | cons e es ih =>
    have he := gramEntry_extends j (Z e.1) (Z e.2) c
    have hr := gramEntry_grade hb hj (hZ e.1) (hZ e.2) hB
    have hs := gramEntry_safe hc hj.1 (hZ e.1).1 (hZ e.2).1
    have hw : GradedRefs (gramEntry j (Z e.1) (Z e.2) c).1
        (write O e (gramEntry j (Z e.1) (Z e.2) c).2) (4*H) := by
      intro i l
      unfold write
      split
      · exact hr.2
      · exact pair_extend (hO i l) he
    exact ih hs hr.1 (pair_extend hj he) (fun i => pair_extend (hZ i) he) hw

theorem gramStage_safe_grade {k : ℕ} {c : Circuit} {j : PairRef} {Z : Fin k → PairRef} {B H : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hj : PairBound c j H)
    (hZ : ∀ i, PairBound c (Z i) H) (hB : 4*H ≤ B) :
    (gramStage j Z c).1.safe ∧ AllBound (gramStage j Z c).1 B ∧
      GradedRefs (gramStage j Z c).1 (gramStage j Z c).2 (4*H) := by
  have hz := pair_zero hb
  have he := pairZero_extends c
  exact gramScan_safe_grade (pairZero_safe hc) hz.1 (pair_extend hj he)
    (fun i => pair_extend (hZ i) he) (fun _ _ => pair_mono hz.2 (Nat.zero_le _)) hB _

def gramDetCompiler (k : ℕ) (j : PairRef) (Z : Fin (k+1) → PairRef) (c : Circuit) : Result :=
  let g := gramStage j Z c
  compiler k g.2 g.1

theorem gramDetCompiler_value {n : ℕ} (k : ℕ) {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {j : PairRef} {Z : Fin (k+1) → PairRef}
    {z : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ}
    (hj : Corner n a d c j 1) (hZ : ∀ i, AdjointValue n a d c (Z i) (z i)) :
    Corner n a d (gramDetCompiler k j Z c).1 (gramDetCompiler k j Z c).2
      ((n : ℝ)^k*(Matrix.det (fun i l => gramScalar n (z i) (z l)))) :=
  compiler_determinant k (gramStage_corner hj hZ)

theorem corners_submatrix {r k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {A : Matrix (Fin k) (Fin k) PairRef} {g : Matrix (Fin k) (Fin k) ℝ}
    (hA : Corners n a d c A g) (e f : Fin r → Fin k) :
    Corners n a d c (A.submatrix e f) (g.submatrix e f) := fun i l => hA (e i) (f l)

theorem gramDetCompiler_gate_bound (k : ℕ) (j : PairRef) (Z : Fin (k+1) → PairRef) (c : Circuit) :
    (gramDetCompiler k j Z c).1.length ≤ c.length+6*(k+1)^2+15*(k+1)^4+3 := by
  have h := compiler_gate_bound k (gramStage j Z c).2 (gramStage j Z c).1
  rw [gramStage_length] at h
  simp only [gramDetCompiler, pow_two]
  omega

theorem gramDetCompiler_safe_grade (k H : ℕ) {c : Circuit} {j : PairRef} {Z : Fin (k+1) → PairRef}
    (hc : c.safe) (hb : AllBound c ((k+1)*(4*H))) (hj : PairBound c j H)
    (hZ : ∀ i, PairBound c (Z i) H) :
    (gramDetCompiler k j Z c).1.safe ∧ AllBound (gramDetCompiler k j Z c).1 ((k+1)*(4*H)) ∧
      PairBound (gramDetCompiler k j Z c).1 (gramDetCompiler k j Z c).2 ((k+1)*(4*H)) := by
  have hs := gramStage_safe_grade hc hb hj hZ (by rw [Nat.add_mul, Nat.one_mul]; omega)
  have hf := compiler_safe_valid k hs.1 (fun i l => (hs.2.2 i l).1)
  have hd := compiler_grade k (4*H) hs.2.1 hs.2.2
  exact ⟨hf.1,hd⟩

#print axioms gramDetCompiler_value
#print axioms gramStage_safe_grade
#print axioms gramDetCompiler_safe_grade
end ADComplete.PSDBird
