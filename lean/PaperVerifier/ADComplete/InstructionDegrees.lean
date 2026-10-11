import PaperVerifier.CircuitAudit.FullCompression

/-! Syntactic degrees of the actual scalar/add/multiply instruction DAG.
No output cancellation is used. The public one-vertex compiler branch is
different from the legacy compiler, which eagerly generated A² at N=1. -/
namespace ADComplete.InstructionDegrees
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit

def gateDegree (ds : List ℕ) : Gate → ℕ
  | .zero | .ident => 0
  | .atomA | .atomD => 1
  | .add i j => max (ds.getD i 0) (ds.getD j 0)
  | .mul i j => ds.getD i 0 + ds.getD j 0
  | .scale _ i => ds.getD i 0

def degrees : Circuit → List ℕ
  | .empty => []
  | .snoc c g => degrees c ++ [gateDegree (degrees c) g]

def degree (c : Circuit) (i : ℕ) : ℕ := (degrees c).getD i 0

@[simp] theorem degrees_length (c : Circuit) : (degrees c).length = c.length := by
  induction c with
  | empty => rfl
  | snoc c g ih => simp [degrees, Circuit.length, ih]

theorem old_degree (c : Circuit) (g : Gate) (i : ℕ) (hi : i < c.length) :
    degree (c.snoc g) i = degree c i := by
  exact List.getD_append _ _ _ _ (by simpa using hi)

@[simp] theorem new_degree (c : Circuit) (g : Gate) :
    degree (c.snoc g) c.length = gateDegree (degrees c) g := by
  change (degrees c ++ [gateDegree (degrees c) g]).getD c.length 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem extends_degree {c t : Circuit} (h : Extends c t) (i : ℕ)
    (hi : i < c.length) : degree t i = degree c i := by
  induction h with
  | refl => rfl
  | @snoc t h g ih => rw [old_degree t g i (lt_of_lt_of_le hi h.length_le)]; exact ih

def AllBound (c : Circuit) (B : ℕ) : Prop := ∀ i < c.length, degree c i ≤ B

def PairBound (c : Circuit) (p : PairRef) (B : ℕ) : Prop :=
  p.valid c ∧ degree c p.forward ≤ B ∧ degree c p.reverse ≤ B

theorem all_mono {c : Circuit} {B C : ℕ} (h : AllBound c B) (he : B ≤ C) :
    AllBound c C := fun i hi => (h i hi).trans he

theorem pair_mono {c : Circuit} {p : PairRef} {B C : ℕ}
    (h : PairBound c p B) (he : B ≤ C) : PairBound c p C :=
  ⟨h.1, h.2.1.trans he, h.2.2.trans he⟩

theorem pair_extend {c t : Circuit} {p : PairRef} {B : ℕ}
    (h : PairBound c p B) (he : Extends c t) : PairBound t p B := by
  exact ⟨PairRef.valid_extend h.1 he,
    by rw [extends_degree he _ h.1.1]; exact h.2.1,
    by rw [extends_degree he _ h.1.2]; exact h.2.2⟩

theorem snoc_bound {c : Circuit} {B : ℕ} (h : AllBound c B) (g : Gate)
    (hg : gateDegree (degrees c) g ≤ B) : AllBound (c.snoc g) B := by
  intro i hi
  by_cases he : i < c.length
  · rw [old_degree c g i he]; exact h i he
  · have eq : i = c.length := by simp only [Circuit.length] at hi; omega
    rw [eq, new_degree]; exact hg

theorem pair_add {c : Circuit} {p q : PairRef} {B P Q : ℕ}
    (hc : AllBound c B) (hp : PairBound c p P) (hq : PairBound c q Q)
    (hmax : max P Q ≤ B) :
    AllBound (pairAdd c p q).1 B ∧ PairBound (pairAdd c p q).1 (pairAdd c p q).2 (max P Q) := by
  have h1 : gateDegree (degrees c) (.add p.forward q.forward) ≤ max P Q :=
    max_le_max hp.2.1 hq.2.1
  have h2 : gateDegree (degrees (c.snoc (.add p.forward q.forward))) (.add p.reverse q.reverse) ≤ max P Q := by
    change max (degree (c.snoc _) p.reverse) (degree (c.snoc _) q.reverse) ≤ _
    rw [old_degree _ _ _ hp.1.2, old_degree _ _ _ hq.1.2]
    exact max_le_max hp.2.2 hq.2.2
  refine ⟨snoc_bound (snoc_bound hc _ (h1.trans hmax)) _ (h2.trans hmax), pairAdd_valid _ _ _, ?_, ?_⟩
  · change degree ((c.snoc (.add p.forward q.forward)).snoc (.add p.reverse q.reverse)) c.length ≤ _
    rw [old_degree _ _ _ (by simp [Circuit.length]), new_degree]; exact h1
  · change degree ((c.snoc (.add p.forward q.forward)).snoc (.add p.reverse q.reverse)) (c.length+1) ≤ _
    change degree ((c.snoc (.add p.forward q.forward)).snoc (.add p.reverse q.reverse))
      (c.snoc (.add p.forward q.forward)).length ≤ _
    rw [new_degree]; exact h2

theorem pair_mul {c : Circuit} {p q : PairRef} {B P Q : ℕ}
    (hc : AllBound c B) (hp : PairBound c p P) (hq : PairBound c q Q)
    (hsum : P + Q ≤ B) :
    AllBound (pairMul c p q).1 B ∧ PairBound (pairMul c p q).1 (pairMul c p q).2 (P+Q) := by
  have h1 : gateDegree (degrees c) (.mul p.forward q.forward) ≤ P+Q := Nat.add_le_add hp.2.1 hq.2.1
  have h2 : gateDegree (degrees (c.snoc (.mul p.forward q.forward))) (.mul q.reverse p.reverse) ≤ P+Q := by
    change degree (c.snoc _) q.reverse + degree (c.snoc _) p.reverse ≤ _
    rw [old_degree _ _ _ hq.1.2, old_degree _ _ _ hp.1.2]
    exact (Nat.add_le_add hq.2.2 hp.2.2).trans_eq (Nat.add_comm Q P)
  refine ⟨snoc_bound (snoc_bound hc _ (h1.trans hsum)) _ (h2.trans hsum), pairMul_valid _ _ _, ?_, ?_⟩
  · change degree ((c.snoc (.mul p.forward q.forward)).snoc (.mul q.reverse p.reverse)) c.length ≤ _
    rw [old_degree _ _ _ (by simp [Circuit.length]), new_degree]; exact h1
  · change degree ((c.snoc (.mul p.forward q.forward)).snoc (.mul q.reverse p.reverse)) (c.length+1) ≤ _
    change degree ((c.snoc (.mul p.forward q.forward)).snoc (.mul q.reverse p.reverse))
      (c.snoc (.mul p.forward q.forward)).length ≤ _
    rw [new_degree]; exact h2

theorem pair_scale {c : Circuit} {p : PairRef} {B P : ℕ}
    (hc : AllBound c B) (hp : PairBound c p P) (he : P ≤ B) (k : ℤ) :
    AllBound (pairScale c k p).1 B ∧ PairBound (pairScale c k p).1 (pairScale c k p).2 P := by
  have h2 : degree (c.snoc (.scale k p.forward)) p.reverse ≤ P := by
    rw [old_degree _ _ _ hp.1.2]; exact hp.2.2
  refine ⟨snoc_bound (snoc_bound hc (.scale k p.forward) (hp.2.1.trans he))
    (.scale k p.reverse) (h2.trans he), pairScale_valid _ _ _, ?_, ?_⟩
  · change degree ((c.snoc (.scale k p.forward)).snoc (.scale k p.reverse)) c.length ≤ _
    rw [old_degree _ _ _ (by simp [Circuit.length]), new_degree]; exact hp.2.1
  · change degree ((c.snoc (.scale k p.forward)).snoc (.scale k p.reverse)) (c.length+1) ≤ _
    change degree ((c.snoc (.scale k p.forward)).snoc (.scale k p.reverse))
      (c.snoc (.scale k p.forward)).length ≤ _
    rw [new_degree]; exact h2

def InitialGrade (c : Circuit) : Prop :=
  PairBound c oneRef 0 ∧ PairBound c aRef 1 ∧ PairBound c dRef 1 ∧ PairBound c zeroRef 0

theorem initial_grade : InitialGrade initial := by
  norm_num [InitialGrade, PairBound, PairRef.valid, oneRef, aRef, dRef, zeroRef,
    initial, degrees, degree, gateDegree, Circuit.length]

theorem initial_all : AllBound initial 1 := by
  intro i hi
  simp only [initial_length] at hi
  interval_cases i <;> norm_num [degree, degrees, initial, gateDegree]

theorem initial_grade_extend {c t : Circuit} (h : InitialGrade c) (he : Extends c t) :
    InitialGrade t :=
  ⟨pair_extend h.1 he, pair_extend h.2.1 he, pair_extend h.2.2.1 he, pair_extend h.2.2.2 he⟩

theorem getD_grade {c : Circuit} {ps : List PairRef} {k : ℕ}
    (hz : PairBound c zeroRef 0) (hps : ∀ p ∈ ps, PairBound c p k) (j : ℕ) :
    PairBound c (ps.getD j zeroRef) k := by
  by_cases hj : j < ps.length
  · rw [List.getD_eq_getElem _ _ hj]; exact hps _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; exact pair_mono hz (Nat.zero_le k)

theorem cell_grade (N k j : ℕ) {c : Circuit} {prev : List PairRef} {B : ℕ}
    (hc : AllBound c B) (hi : InitialGrade c)
    (hp : ∀ p ∈ prev, PairBound c p k) (hB : k+1 ≤ B) :
    AllBound (cell N k j c prev).1 B ∧
      PairBound (cell N k j c prev).1 (cell N k j c prev).2 (k+1) := by
  let x := pairScale c ((N : ℤ)^2 * ((j : ℤ)-k)) oneRef
  let y := pairAdd x.1 dRef x.2
  let p := if j ≤ k then prev.getD j zeroRef else zeroRef
  let q := if 0 < j then prev.getD (j-1) zeroRef else zeroRef
  let l := pairMul y.1 y.2 p
  let r := pairMul l.1 aRef q
  let s := pairScale r.1 ((N : ℤ)^2) r.2
  have gp : PairBound c p k := by
    dsimp only [p]; split
    · exact getD_grade hi.2.2.2 hp j
    · exact pair_mono hi.2.2.2 (Nat.zero_le k)
  have gq : PairBound c q k := by
    dsimp only [q]; split
    · exact getD_grade hi.2.2.2 hp (j-1)
    · exact pair_mono hi.2.2.2 (Nat.zero_le k)
  have ex : Extends c x.1 := pairScale_extends _ _ _
  have ey : Extends c y.1 := ex.trans (pairAdd_extends _ _ _)
  have el : Extends c l.1 := ey.trans (pairMul_extends _ _ _)
  have er : Extends l.1 r.1 := pairMul_extends _ _ _
  have es : Extends l.1 s.1 := er.trans (pairScale_extends _ _ _)
  have gx := pair_scale hc hi.1 (Nat.zero_le B) ((N : ℤ)^2 * ((j : ℤ)-k))
  have gy := pair_add gx.1 (pair_extend hi.2.2.1 ex) gx.2
    (show max 1 0 ≤ B by omega)
  have gl := pair_mul gy.1 gy.2 (pair_extend gp ey) (show max 1 0 + k ≤ B by omega)
  have gr := pair_mul gl.1 (pair_extend hi.2.1 el) (pair_extend gq el)
    (show 1+k ≤ B by omega)
  have gs := pair_scale gr.1 gr.2 (show 1+k ≤ B by omega) ((N : ℤ)^2)
  have gf := pair_add gs.1 (pair_extend gl.2 es) gs.2
    (show max (max 1 0+k) (1+k) ≤ B by omega)
  exact ⟨gf.1, pair_mono gf.2 (by omega)⟩

theorem cells_grade (N k : ℕ) (js : List ℕ) {c : Circuit} {prev : List PairRef} {B : ℕ}
    (hc : AllBound c B) (hi : InitialGrade c)
    (hp : ∀ p ∈ prev, PairBound c p k) (hB : k+1 ≤ B) :
    AllBound (cells N k prev c js).1 B ∧
      ∀ p ∈ (cells N k prev c js).2, PairBound (cells N k prev c js).1 p (k+1) := by
  induction js generalizing c with
  | nil => exact ⟨hc, by simp [cells]⟩
  | cons j js ih =>
    have gx := cell_grade N k j hc hi hp hB
    have ex := cell_extends N k j c prev
    have gt := ih gx.1 (initial_grade_extend hi ex)
      (fun p h => pair_extend (hp p h) ex)
    refine ⟨gt.1, ?_⟩
    intro p h
    simp only [cells, List.mem_cons] at h
    rcases h with rfl | h
    · exact pair_extend gx.2 (cells_extends N k prev _ js)
    · exact gt.2 p h

theorem probe_build_grade (N k : ℕ) :
    AllBound (build N k).circuit (max 1 k) ∧
    (∀ p ∈ (build N k).lastRow, PairBound (build N k).circuit p k) ∧
    (∀ p ∈ (build N k).probes, PairBound (build N k).circuit p k) := by
  induction k with
  | zero =>
    refine ⟨initial_all, ?_, ?_⟩ <;> intro p hp
    all_goals simp only [build, List.mem_singleton] at hp
    all_goals subst p; exact initial_grade.1
  | succ k ih =>
    have hg : InitialGrade (build N k).circuit := initial_grade_extend initial_grade (build_extends N k)
    have hc : AllBound (build N k).circuit (k+1) := all_mono ih.1 (by omega)
    have cg := cells_grade N k (List.range (k+2)) hc hg ih.2.1 (le_refl _)
    have ex := cells_extends N k (build N k).lastRow (build N k).circuit (List.range (k+2))
    refine ⟨all_mono cg.1 (by omega), cg.2, ?_⟩
    intro p hp
    simp only [build, List.mem_append] at hp
    rcases hp with hp | hp
    · exact pair_mono (pair_extend (ih.2.2 p hp) ex) (by omega)
    · exact cg.2 p hp

#print axioms probe_build_grade

def compiled (N : ℕ) (b : ℤ) : Result :=
  if N = 1 then (initial, oneRef) else CircuitAudit.FullCompression.full N b

theorem compiled_safe (N : ℕ) (b : ℤ) : (compiled N b).1.safe := by
  unfold compiled
  split
  · exact initial_safe
  · exact CircuitAudit.FullCompression.full_safe N b

theorem compiled_one_degrees (b : ℤ) : AllBound (compiled 1 b).1 1 := by
  simp only [compiled, ite_true]
  intro i hi
  simp only [initial_length] at hi
  interval_cases i <;> norm_num [degree, degrees, initial, gateDegree]

theorem compiled_one_value {R : Type*} [Ring R] (b : ℤ) (a d : R) :
    (compiled 1 b).2.value (compiled 1 b).1 a d = (1,1) := by
  simp only [compiled, ite_true]
  exact one_value a d (.refl initial)

/-- The eager legacy prefix has a degree-two register at N=1. -/
theorem legacy_one_counterexample :
    ∃ i < (CircuitAudit.FullCompression.full 1 0).1.length,
      degree (CircuitAudit.FullCompression.full 1 0).1 i = 2 := by
  refine ⟨4, ?_, ?_⟩ <;>
    norm_num [CircuitAudit.FullCompression.full, probePrefix, build, initial,
      CircuitAudit.DistanceCircuit.build, CircuitAudit.DistanceCircuit.iterate,
      CircuitAudit.DistanceCircuit.seed, compress, scalarBase, pairPow, pairHorner,
      pairMul, pairAdd, pairScale, pairZero, degrees, degree, gateDegree,
      oneRef, aRef, dRef, zeroRef, Circuit.length]

#print axioms compiled_safe
#print axioms compiled_one_degrees
#print axioms legacy_one_counterexample
end ADComplete.InstructionDegrees
