import PaperVerifier.ADComplete.PSDResidualCompiler

namespace ADComplete.PSDFoldCompiler
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit CircuitAudit.Degrees
open ADComplete.InstructionDegrees

def scalar (τ i : ℕ) : ℤ := (2 : ℤ)^(i-1)*(τ : ℤ)

def foldExpr (τ : ℕ) (xs : List Expr) (i : ℕ) : Expr :=
  if i=0 then .one else CircuitAudit.Degrees.horner (.scale (scalar τ i) .one) xs

def foldOne (τ : ℕ) (one : PairRef) (ps : List PairRef) (i : ℕ) (c : Circuit) : Result :=
  if i=0 then (c,one) else
    let b := scalarBase c one (scalar τ i)
    pairHorner b.1 b.2 ps

def PairValue {R : Type*} [Ring R] (a d : R) (c : Circuit) (p : PairRef) (v : R×R) : Prop :=
  p.valid c ∧ p.value c a d=v

theorem pairValue_extend {R : Type*} [Ring R] {a d : R} {c t : Circuit} {p : PairRef} {v : R×R}
    (h : PairValue a d c p v) (he : Extends c t) : PairValue a d t p v :=
  ⟨PairRef.valid_extend h.1 he, (PairRef.value_extend h.1 he a d).trans h.2⟩

theorem foldOne_extends (τ : ℕ) (one : PairRef) (ps : List PairRef) (i : ℕ) (c : Circuit) :
    Extends c (foldOne τ one ps i c).1 := by
  unfold foldOne
  split
  · exact .refl _
  · exact (scalarBase_extends _ _ _).trans (pairHorner_extends _ _ _)

theorem foldOne_length (τ : ℕ) (one : PairRef) (ps : List PairRef) (i : ℕ) (c : Circuit) :
    (foldOne τ one ps i c).1.length ≤ c.length+2+4*ps.length := by
  unfold foldOne
  split
  · change c.length ≤ c.length+2+4*ps.length
    omega
  · simp only [pairHorner_length, scalarBase_length]
    omega

theorem foldOne_safe_grade {τ i : ℕ} {one : PairRef} {ps : List PairRef} {c : Circuit} {B H : ℕ}
    (hc : c.safe) (hb : AllBound c B) (ho : PairBound c one 0)
    (hp : ∀ p ∈ ps, PairBound c p H) (hH : H ≤ B) :
    (foldOne τ one ps i c).1.safe ∧ AllBound (foldOne τ one ps i c).1 B ∧
      PairBound (foldOne τ one ps i c).1 (foldOne τ one ps i c).2 H := by
  unfold foldOne
  split
  · exact ⟨hc,hb,pair_mono ho (Nat.zero_le _)⟩
  · have ex := scalarBase_extends c one (scalar τ i)
    have hg := scalar_grade hb ho (scalar τ i)
    have hf := horner_grade ps hg.1 hg.2 (fun p h => pair_extend (hp p h) ex) hH
    have hs := pairHorner_safe (scalarBase_safe hc ho.1 _) hg.2.1
      (fun p h => PairRef.valid_extend (hp p h).1 ex)
    exact ⟨hs,hf⟩

theorem foldOne_value {R : Type*} [Ring R] (a d : R) (τ : ℕ) (i : ℕ)
    {c : Circuit} {one : PairRef} {ps : List PairRef} {xs : List Expr}
    (ho : PairValue a d c one (1,1)) (hp : ∀ p ∈ ps, p.valid c)
    (hx : ps.map (fun p => p.value c a d)=xs.map (exprPair a d)) :
    PairValue a d (foldOne τ one ps i c).1 (foldOne τ one ps i c).2
      (exprPair a d (foldExpr τ xs i)) := by
  unfold foldOne foldExpr
  split_ifs with hi
  · simpa only [exprPair, Expr.eval, Expr.reverse] using ho
  · let b := scalarBase c one (scalar τ i)
    have ex : Extends c b.1 := scalarBase_extends _ _ _
    have hv := pairHorner_value a d (scalarBase_valid c one _) (fun p h => PairRef.valid_extend (hp p h) ex)
    have hb := scalarBase_value a d c one (scalar τ i)
    rw [ho.2] at hb
    have hm : ps.map (fun p => p.value b.1 a d)=xs.map (exprPair a d) := by
      rw [← hx]
      apply List.map_congr_left
      intro p h
      exact PairRef.value_extend (hp p h) ex a d
    rw [hb,hm] at hv
    have he : (scalar τ i • (1 : R), scalar τ i • (1 : R)) =
        exprPair a d (.scale (scalar τ i) .one) := by
      simp only [exprPair, Expr.eval, Expr.reverse]
    rw [he, CircuitAudit.FullCompression.horner_expr_pair] at hv
    exact ⟨pairHorner_valid _ _ _,hv⟩

def write {N : ℕ} {α : Type*} (O : Fin N → α) (i : Fin N) (p : α) : Fin N → α :=
  fun j => if j=i then p else O j

def scan {N : ℕ} (τ : ℕ) (one : PairRef) (ps : List PairRef) :
    Circuit → (Fin N → PairRef) → List (Fin N) → Circuit × (Fin N → PairRef)
  | c,O,[] => (c,O)
  | c,O,i::is =>
    let r := foldOne τ one ps i.val c
    scan τ one ps r.1 (write O i r.2) is

theorem scan_extends {N : ℕ} (τ : ℕ) (one : PairRef) (ps : List PairRef)
    (c : Circuit) (O : Fin N → PairRef) (is : List (Fin N)) :
    Extends c (scan τ one ps c O is).1 := by
  induction is generalizing c O with
  | nil => exact .refl _
  | cons i is ih => exact (foldOne_extends _ _ _ _ _).trans (ih _ _)

theorem scan_length {N : ℕ} (τ : ℕ) (one : PairRef) (ps : List PairRef)
    (c : Circuit) (O : Fin N → PairRef) (is : List (Fin N)) :
    (scan τ one ps c O is).1.length ≤ c.length+is.length*(2+4*ps.length) := by
  induction is generalizing c O with
  | nil => simp [scan]
  | cons i is ih =>
    have hr := foldOne_length τ one ps i c
    have ht := ih (foldOne τ one ps i c).1 (write O i (foldOne τ one ps i c).2)
    simp only [scan, List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem scan_safe_grade {N τ : ℕ} {one : PairRef} {ps : List PairRef}
    {c : Circuit} {O : Fin N → PairRef} {B H : ℕ}
    (hc : c.safe) (hb : AllBound c B) (ho : PairBound c one 0)
    (hp : ∀ p ∈ ps, PairBound c p H) (hO : ∀ i, PairBound c (O i) H) (hH : H ≤ B)
    (is : List (Fin N)) :
    (scan τ one ps c O is).1.safe ∧ AllBound (scan τ one ps c O is).1 B ∧
      ∀ i, PairBound (scan τ one ps c O is).1 ((scan τ one ps c O is).2 i) H := by
  induction is generalizing c O with
  | nil => exact ⟨hc,hb,hO⟩
  | cons i is ih =>
    have hr := foldOne_safe_grade (τ := τ) (i := i) hc hb ho hp hH
    have he := foldOne_extends τ one ps i c
    have hw : ∀ j, PairBound (foldOne τ one ps i c).1 (write O i (foldOne τ one ps i c).2 j) H := by
      intro j
      unfold write
      split
      · exact hr.2.2
      · exact pair_extend (hO j) he
    exact ih hr.1 hr.2.1 (pair_extend ho he) (fun p h => pair_extend (hp p h) he) hw

theorem scan_value {R : Type*} [Ring R] {N τ : ℕ} (a d : R)
    {one : PairRef} {ps : List PairRef} {xs : List Expr} {c : Circuit}
    {O : Fin N → PairRef} {e : Fin N → Expr}
    (ho : PairValue a d c one (1,1)) (hp : ∀ p∈ps, p.valid c)
    (hx : ps.map (fun p => p.value c a d)=xs.map (exprPair a d))
    (hO : ∀ i, PairValue a d c (O i) (exprPair a d (e i))) (is : List (Fin N)) :
    ∀ i, PairValue a d (scan τ one ps c O is).1 ((scan τ one ps c O is).2 i)
      (exprPair a d (if i∈is then foldExpr τ xs i else e i)) := by
  induction is generalizing c O e with
  | nil => simpa only [scan, List.not_mem_nil, ite_false] using hO
  | cons i is ih =>
    let r := foldOne τ one ps i c
    have he : Extends c r.1 := foldOne_extends _ _ _ _ _
    have hr := foldOne_value a d τ i ho hp hx
    have hw : ∀ j, PairValue a d r.1 (write O i r.2 j)
        (exprPair a d (write e i (foldExpr τ xs i) j)) := by
      intro j
      unfold write
      split
      · subst j; exact hr
      · exact pairValue_extend (hO j) he
    have hx' : ps.map (fun p => p.value r.1 a d)=xs.map (exprPair a d) := by
      rw [← hx]
      apply List.map_congr_left
      intro p h
      exact PairRef.value_extend (hp p h) he a d
    have hs := ih (pairValue_extend ho he) (fun p h => PairRef.valid_extend (hp p h) he) hx' hw
    intro j
    have hv := hs j
    by_cases hm : j∈is
    · simpa only [scan,List.mem_cons,hm,or_true,ite_true] using hv
    · by_cases hji : j=i
      · subst j
        simpa only [scan,List.mem_cons,hm,or_false,ite_false,write,ite_true] using hv
      · simpa only [scan,List.mem_cons,hm,hji,or_self,ite_false,write] using hv

def stage (N τ : ℕ) (one : PairRef) (ps : List PairRef) (c : Circuit) :
    Circuit × (Fin N → PairRef) := scan τ one ps c (fun _ => one) (List.finRange N)

theorem stage_extends (N τ : ℕ) (one : PairRef) (ps : List PairRef) (c : Circuit) :
    Extends c (stage N τ one ps c).1 := scan_extends _ _ _ _ _ _

theorem stage_length (N τ : ℕ) (one : PairRef) (ps : List PairRef) (c : Circuit) :
    (stage N τ one ps c).1.length≤c.length+N*(2+4*ps.length) := by
  simpa only [stage,List.length_finRange] using scan_length τ one ps c (fun _ => one) (List.finRange N)

theorem stage_safe_grade {N τ : ℕ} {one : PairRef} {ps : List PairRef} {c : Circuit} {B H : ℕ}
    (hc : c.safe) (hb : AllBound c B) (ho : PairBound c one 0)
    (hp : ∀ p∈ps, PairBound c p H) (hH : H≤B) :
    (stage N τ one ps c).1.safe ∧ AllBound (stage N τ one ps c).1 B ∧
      ∀ i, PairBound (stage N τ one ps c).1 ((stage N τ one ps c).2 i) H :=
  scan_safe_grade hc hb ho hp (fun _ => pair_mono ho (Nat.zero_le _)) hH _

theorem stage_value {R : Type*} [Ring R] {N τ : ℕ} (a d : R)
    {one : PairRef} {ps : List PairRef} {xs : List Expr} {c : Circuit}
    (ho : PairValue a d c one (1,1)) (hp : ∀ p∈ps, p.valid c)
    (hx : ps.map (fun p => p.value c a d)=xs.map (exprPair a d)) :
    ∀ i, PairValue a d (stage N τ one ps c).1 ((stage N τ one ps c).2 i)
      (exprPair a d (foldExpr τ xs i)) := by
  have hv := scan_value (N := N) (τ := τ) (O := fun _ => one) (e := fun _ => .one)
    a d ho hp hx (fun _ => (by simpa only [exprPair,Expr.eval,Expr.reverse] using ho))
    (List.finRange N)
  simpa only [stage,List.mem_finRange,ite_true] using hv

#print axioms stage_value
#print axioms foldOne_value
#print axioms scan_safe_grade
end ADComplete.PSDFoldCompiler
