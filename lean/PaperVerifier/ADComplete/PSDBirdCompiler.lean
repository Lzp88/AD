import PaperVerifier.ADComplete.PSDBirdEntry

/-! Shared Bird determinant DAG. Every iteration materializes one complete
matrix of register references before the next iteration starts. -/
namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDHomogeneousLift

def allPairs (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap (fun i => (List.finRange k).map (fun j => (i,j)))

@[simp] theorem allPairs_mem (k : ℕ) (i j : Fin k) : (i,j) ∈ allPairs k := by
  simp [allPairs]

@[simp] theorem allPairs_length (k : ℕ) : (allPairs k).length = k*k := by
  simp [allPairs, List.length_flatMap]

def write {k : ℕ} {α : Type*} (O : Matrix (Fin k) (Fin k) α)
    (e : Fin k × Fin k) (p : α) : Matrix (Fin k) (Fin k) α :=
  fun i j => if (i,j)=e then p else O i j

def scan {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef) :
    Circuit → Matrix (Fin k) (Fin k) PairRef → List (Fin k × Fin k) →
      Circuit × Matrix (Fin k) (Fin k) PairRef
  | c, O, [] => (c,O)
  | c, O, e::es =>
    let r := entry A F e.1 e.2 c
    scan A F r.1 (write O e r.2) es

theorem scan_extends {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (c : Circuit) (O : Matrix (Fin k) (Fin k) PairRef) (es : List (Fin k × Fin k)) :
    Extends c (scan A F c O es).1 := by
  induction es generalizing c O with
  | nil => exact .refl _
  | cons e es ih => exact (entry_extends A F e.1 e.2 c).trans (ih _ _)

theorem scan_length_bound {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (c : Circuit) (O : Matrix (Fin k) (Fin k) PairRef) (es : List (Fin k × Fin k)) :
    (scan A F c O es).1.length ≤ c.length+es.length*(8+6*k) := by
  induction es generalizing c O with
  | nil => simp [scan]
  | cons e es ih =>
    have h := ih (entry A F e.1 e.2 c).1 (write O e (entry A F e.1 e.2 c).2)
    have he := entry_length_bound A F e.1 e.2 c
    simp only [scan, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem scan_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {A F O : Matrix (Fin k) (Fin k) PairRef}
    {g f h : Matrix (Fin k) (Fin k) ℝ}
    (hA : Corners n a d c A g) (hF : Corners n a d c F f)
    (hO : Corners n a d c O h) (es : List (Fin k × Fin k)) :
    Corners n a d (scan A F c O es).1 (scan A F c O es).2
      (fun i j => if (i,j) ∈ es then (n : ℝ)*BirdDet.Spec.stepEntry g f i j else h i j) := by
  induction es generalizing c O h with
  | nil => simpa only [scan, List.not_mem_nil, ite_false] using hO
  | cons e es ih =>
    let r := entry A F e.1 e.2 c
    have he : Extends c r.1 := entry_extends A F e.1 e.2 c
    have hr := entry_corner hA hF e.1 e.2
    have hw : Corners n a d r.1 (write O e r.2)
        (write h e ((n : ℝ)*BirdDet.Spec.stepEntry g f e.1 e.2)) := by
      intro i j
      by_cases hij : (i,j)=e
      · obtain rfl : e=(i,j) := hij.symm
        simpa only [write, ite_true] using hr
      · simpa only [write, hij, ite_false] using corner_extend (hO i j) he
    have hs := ih (corners_extend hA he) (corners_extend hF he) hw
    intro i j
    have hv := hs i j
    by_cases hm : (i,j) ∈ es
    · simpa only [scan, List.mem_cons, hm, or_true, ite_true] using hv
    · by_cases hij : (i,j)=e
      · obtain rfl : e=(i,j) := hij.symm
        simpa only [scan, List.mem_cons, hm, or_false, ite_false, write, ite_true] using hv
      · simpa only [scan, List.mem_cons, hm, hij, or_self, ite_false, write] using hv

def stage {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef) (c : Circuit) :
    Circuit × Matrix (Fin k) (Fin k) PairRef :=
  let z := pairZero c
  scan A F z.1 (fun _ _ => z.2) (allPairs k)

theorem stage_extends {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef) (c : Circuit) :
    Extends c (stage A F c).1 :=
  (pairZero_extends c).trans (scan_extends A F _ _ _)

theorem stage_length_bound {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef) (c : Circuit) :
    (stage A F c).1.length ≤ c.length+1+k*k*(8+6*k) := by
  have h := scan_length_bound A F (pairZero c).1 (fun _ _ => (pairZero c).2) (allPairs k)
  simpa only [stage, pairZero_length, allPairs_length] using h

theorem stage_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {A F : Matrix (Fin k) (Fin k) PairRef} {g f : Matrix (Fin k) (Fin k) ℝ}
    (hA : Corners n a d c A g) (hF : Corners n a d c F f) :
    Corners n a d (stage A F c).1 (stage A F c).2
      (fun i j => (n : ℝ)*BirdDet.Spec.stepEntry g f i j) := by
  have he := pairZero_extends c
  have h := scan_corner (corners_extend hA he) (corners_extend hF he)
    (fun _ _ => corner_zero n a d c) (allPairs k)
  simpa only [stage, allPairs_mem, ite_true] using h

def iterate {k : ℕ} (A : Matrix (Fin k) (Fin k) PairRef) :
    ℕ → Circuit → Matrix (Fin k) (Fin k) PairRef → Circuit × Matrix (Fin k) (Fin k) PairRef
  | 0, c, F => (c,F)
  | t+1, c, F =>
    let s := stage A F c
    iterate A t s.1 s.2

theorem iterate_extends {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (t : ℕ) (c : Circuit) : Extends c (iterate A t c F).1 := by
  induction t generalizing c F with
  | zero => exact .refl _
  | succ t ih => exact (stage_extends A F c).trans (ih _ _)

theorem iterate_length_bound {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (t : ℕ) (c : Circuit) :
    (iterate A t c F).1.length ≤ c.length+t*(1+k*k*(8+6*k)) := by
  induction t generalizing c F with
  | zero => simp [iterate]
  | succ t ih =>
    have hs := stage_length_bound A F c
    have ht := ih (stage A F c).2 (stage A F c).1
    simp only [iterate]
    rw [Nat.add_mul, Nat.one_mul]
    omega

def compiler (k : ℕ) (A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef) (c : Circuit) : Result :=
  let s := iterate A k c A
  pairScale s.1 ((-1 : ℤ)^k) (s.2 0 0)

theorem compiler_extends (k : ℕ) (A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef) (c : Circuit) :
    Extends c (compiler k A c).1 :=
  (iterate_extends A A k c).trans (pairScale_extends _ _ _)

theorem compiler_gate_bound (k : ℕ) (A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef) (c : Circuit) :
    (compiler k A c).1.length ≤ c.length+15*(k+1)^4+2 := by
  have h := iterate_length_bound A A k c
  simp only [compiler, pairScale_length]
  have hb : k*(1+(k+1)*(k+1)*(8+6*(k+1))) ≤ 15*(k+1)^4 := by
    ring_nf
    omega
  omega

#print axioms stage_corner
#print axioms compiler_gate_bound
end ADComplete.PSDBird
