import PaperVerifier.ADComplete.PSDHomogeneousLift
import PaperVerifier.ADComplete.InstructionCompressionDegrees
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness

/-! An actual division-free Bird entry compiler, with shared register
references. Inputs are existing Gram registers; no determinant gate is used. -/
namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDHomogeneousLift

def upper (k : ℕ) (i : Fin k) : List (Fin k) :=
  (List.finRange k).filter (fun l => i < l)

def diagSum {k : ℕ} (F : Matrix (Fin k) (Fin k) PairRef) (c : Circuit) :
    List (Fin k) → Result
  | [] => pairZero c
  | l::ls => let r := diagSum F c ls; pairAdd r.1 (F l l) r.2

def offSum {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef) (i j : Fin k)
    (c : Circuit) : List (Fin k) → Result
  | [] => pairZero c
  | l::ls =>
    let r := offSum A F i j c ls
    let t := pairMul r.1 (F i l) (A l j)
    pairAdd t.1 t.2 r.2

def entry {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) : Result :=
  let ds := diagSum F c (upper k i)
  let neg := pairScale ds.1 (-1) ds.2
  let l := pairMul neg.1 neg.2 (A i j)
  let r := offSum A F i j l.1 (upper k i)
  pairAdd r.1 l.2 r.2

theorem diagSum_extends {k : ℕ} (F : Matrix (Fin k) (Fin k) PairRef)
    (c : Circuit) (ls : List (Fin k)) : Extends c (diagSum F c ls).1 := by
  induction ls with
  | nil => exact pairZero_extends c
  | cons l ls ih => exact ih.trans (pairAdd_extends _ _ _)

theorem offSum_extends {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) (ls : List (Fin k)) : Extends c (offSum A F i j c ls).1 := by
  induction ls with
  | nil => exact pairZero_extends c
  | cons l ls ih => exact ih.trans ((pairMul_extends _ _ _).trans (pairAdd_extends _ _ _))

theorem entry_extends {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) : Extends c (entry A F i j c).1 :=
  (diagSum_extends F c _).trans ((pairScale_extends _ _ _).trans
    ((pairMul_extends _ _ _).trans ((offSum_extends A F i j _ _).trans (pairAdd_extends _ _ _))))

@[simp] theorem diagSum_length {k : ℕ} (F : Matrix (Fin k) (Fin k) PairRef)
    (c : Circuit) (ls : List (Fin k)) : (diagSum F c ls).1.length = c.length+1+2*ls.length := by
  induction ls with
  | nil => simp [diagSum]
  | cons l ls ih => simp only [diagSum, pairAdd_length, ih, List.length_cons]; omega

@[simp] theorem offSum_length {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) (ls : List (Fin k)) :
    (offSum A F i j c ls).1.length = c.length+1+4*ls.length := by
  induction ls with
  | nil => simp [offSum]
  | cons l ls ih => simp only [offSum, pairAdd_length, pairMul_length, ih, List.length_cons]; omega

theorem entry_length {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) :
    (entry A F i j c).1.length = c.length+8+6*(upper k i).length := by
  simp only [entry, pairAdd_length, offSum_length, pairMul_length, pairScale_length, diagSum_length]
  omega

theorem entry_length_bound {k : ℕ} (A F : Matrix (Fin k) (Fin k) PairRef)
    (i j : Fin k) (c : Circuit) : (entry A F i j c).1.length ≤ c.length+8+6*k := by
  rw [entry_length]
  have h : (upper k i).length ≤ k := by
    simpa [upper] using List.length_filter_le (fun l : Fin k => decide (i<l)) (List.finRange k)
  omega

def Corner (n : ℕ) (a d : Matrix (Fin n) (Fin n) ℝ) (c : Circuit)
    (p : PairRef) (f : ℝ) : Prop :=
  p.valid c ∧ p.value c a d = (f • J n, f • J n)

theorem corner_extend {n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c t : Circuit} {p : PairRef} {f : ℝ} (hp : Corner n a d c p f) (he : Extends c t) :
    Corner n a d t p f := by
  exact ⟨PairRef.valid_extend hp.1 he, (PairRef.value_extend hp.1 he a d).trans hp.2⟩

theorem corner_zero (n : ℕ) (a d : Matrix (Fin n) (Fin n) ℝ) (c : Circuit) :
    Corner n a d (pairZero c).1 (pairZero c).2 0 := by
  exact ⟨pairZero_valid _, by simp⟩

theorem corner_add {n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p q : PairRef} {f g : ℝ}
    (hp : Corner n a d c p f) (hq : Corner n a d c q g) :
    Corner n a d (pairAdd c p q).1 (pairAdd c p q).2 (f+g) := by
  refine ⟨pairAdd_valid _ _ _, ?_⟩
  rw [pairAdd_value a d hp.1 hq.1, hp.2, hq.2]
  simp only [add_smul]

theorem corner_scale {n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p : PairRef} {f : ℝ} (hp : Corner n a d c p f) (z : ℤ) :
    Corner n a d (pairScale c z p).1 (pairScale c z p).2 ((z : ℝ)*f) := by
  refine ⟨pairScale_valid _ _ _, ?_⟩
  rw [pairScale_value a d hp.1, hp.2]
  apply Prod.ext <;> ext i j <;> simp [J, zsmul_eq_mul]

theorem corner_mul {n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p q : PairRef} {f g : ℝ}
    (hp : Corner n a d c p f) (hq : Corner n a d c q g) :
    Corner n a d (pairMul c p q).1 (pairMul c p q).2 ((n : ℝ)*f*g) := by
  refine ⟨pairMul_valid _ _ _, ?_⟩
  rw [pairMul_value a d hp.1 hq.1, hp.2, hq.2]
  simp only [scaled_mul]
  congr 2
  ring

def Corners {k : ℕ} (n : ℕ) (a d : Matrix (Fin n) (Fin n) ℝ) (c : Circuit)
    (F : Matrix (Fin k) (Fin k) PairRef) (f : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ i j, Corner n a d c (F i j) (f i j)

theorem corners_extend {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c t : Circuit} {F : Matrix (Fin k) (Fin k) PairRef} {f : Matrix (Fin k) (Fin k) ℝ}
    (h : Corners n a d c F f) (he : Extends c t) : Corners n a d t F f :=
  fun i j => corner_extend (h i j) he

theorem diagSum_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {F : Matrix (Fin k) (Fin k) PairRef} {f : Matrix (Fin k) (Fin k) ℝ}
    (hF : Corners n a d c F f) (ls : List (Fin k)) :
    Corner n a d (diagSum F c ls).1 (diagSum F c ls).2 ((ls.map (fun l => f l l)).sum) := by
  induction ls with
  | nil => simpa only [diagSum, List.map_nil, List.sum_nil] using corner_zero n a d c
  | cons l ls ih =>
    simpa only [diagSum, List.map_cons, List.sum_cons] using
      corner_add (corner_extend (hF l l) (diagSum_extends F c ls)) ih

theorem offSum_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {A F : Matrix (Fin k) (Fin k) PairRef} {g f : Matrix (Fin k) (Fin k) ℝ}
    (hA : Corners n a d c A g) (hF : Corners n a d c F f)
    (i j : Fin k) (ls : List (Fin k)) :
    Corner n a d (offSum A F i j c ls).1 (offSum A F i j c ls).2
      ((n : ℝ)*(ls.map (fun l => f i l*g l j)).sum) := by
  induction ls with
  | nil => simpa only [offSum, List.map_nil, List.sum_nil, mul_zero] using corner_zero n a d c
  | cons l ls ih =>
    have ex := offSum_extends A F i j c ls
    have hm := corner_mul (corner_extend (hF i l) ex) (corner_extend (hA l j) ex)
    have hs := corner_add hm (corner_extend ih (pairMul_extends _ _ _))
    have he : (n : ℝ)*f i l*g l j+(n : ℝ)*(ls.map (fun l => f i l*g l j)).sum =
        (n : ℝ)*((f i l*g l j)+(ls.map (fun l => f i l*g l j)).sum) := by ring
    simpa only [offSum, List.map_cons, List.sum_cons, he] using hs

theorem upper_sum (k : ℕ) (i : Fin k) (f : Fin k → ℝ) :
    ((upper k i).map f).sum = ∑ l ∈ Finset.Ioi i, f l := by
  have hn : (upper k i).Nodup := (List.nodup_finRange k).filter _
  rw [← List.sum_toFinset f hn]
  have he : (upper k i).toFinset = Finset.Ioi i := by
    ext l
    simp [upper]
  rw [he]

theorem entry_corner {k n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {A F : Matrix (Fin k) (Fin k) PairRef} {g f : Matrix (Fin k) (Fin k) ℝ}
    (hA : Corners n a d c A g) (hF : Corners n a d c F f) (i j : Fin k) :
    Corner n a d (entry A F i j c).1 (entry A F i j c).2
      ((n : ℝ)*BirdDet.Spec.stepEntry g f i j) := by
  let ds := diagSum F c (upper k i)
  let neg := pairScale ds.1 (-1) ds.2
  let l := pairMul neg.1 neg.2 (A i j)
  let r := offSum A F i j l.1 (upper k i)
  have eds : Extends c ds.1 := diagSum_extends F c _
  have eneg : Extends c neg.1 := eds.trans (pairScale_extends _ _ _)
  have el : Extends c l.1 := eneg.trans (pairMul_extends _ _ _)
  have er : Extends l.1 r.1 := offSum_extends A F i j _ _
  have hds := diagSum_corner hF (upper k i)
  have hneg := corner_scale hds (-1)
  have hl := corner_mul hneg (corner_extend (hA i j) eneg)
  have hr := offSum_corner (corners_extend hA el) (corners_extend hF el) i j (upper k i)
  have hs := corner_add (corner_extend hl er) hr
  have he : (n : ℝ)*(((-1 : ℤ) : ℝ)*((upper k i).map (fun l => f l l)).sum)*g i j+
      (n : ℝ)*((upper k i).map (fun l => f i l*g l j)).sum =
      (n : ℝ)*BirdDet.Spec.stepEntry g f i j := by
    rw [upper_sum, upper_sum]
    simp only [BirdDet.Spec.stepEntry, Matrix.of_apply, Int.cast_neg, Int.cast_one]
    ring
  simpa only [entry, ds, neg, l, r, he] using hs

#print axioms entry_corner
#print axioms entry_length_bound
end ADComplete.PSDBird
