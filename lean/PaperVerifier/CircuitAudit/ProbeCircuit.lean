import PaperVerifier.CircuitAudit.CircuitCosts
import PaperVerifier.CircuitAudit.Degrees

/-! The actual shared triangular probe DAG, starting at the empty circuit.
Every cell emits twelve allowed scalar/add/multiply instructions, including
zero branches. This module does not assume a quadratic-size input prefix. -/
namespace CircuitAudit.ProbeCircuit

open CircuitAudit.CircuitCosts

def oneRef : PairRef := ⟨1, 1⟩
def aRef : PairRef := ⟨2, 2⟩
def dRef : PairRef := ⟨3, 3⟩
def zeroRef : PairRef := ⟨0, 0⟩

def initial : Circuit :=
  (((Circuit.empty.snoc .zero).snoc .ident).snoc .atomA).snoc .atomD

@[simp] theorem initial_length : initial.length = 4 := rfl
theorem initial_safe : initial.safe := by simp [initial, Circuit.safe, Gate.valid]

def Ready (c : Circuit) (ps : List PairRef) : Prop :=
  oneRef.valid c ∧ aRef.valid c ∧ dRef.valid c ∧ zeroRef.valid c ∧
    ∀ p ∈ ps, p.valid c

theorem ready_extend {c t : Circuit} {ps : List PairRef}
    (h : Ready c ps) (he : Extends c t) : Ready t ps :=
  ⟨PairRef.valid_extend h.1 he, PairRef.valid_extend h.2.1 he,
    PairRef.valid_extend h.2.2.1 he, PairRef.valid_extend h.2.2.2.1 he,
    fun p hp => PairRef.valid_extend (h.2.2.2.2 p hp) he⟩

theorem initial_ready : Ready initial [oneRef] := by
  simp [Ready, oneRef, aRef, dRef, zeroRef, PairRef.valid, initial, Circuit.length]

theorem getD_valid {c : Circuit} {ps : List PairRef} (h : Ready c ps) (j : ℕ) :
    (ps.getD j zeroRef).valid c := by
  by_cases hj : j < ps.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h.2.2.2.2 _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact h.2.2.2.1

def pairScale (c : Circuit) (k : ℤ) (p : PairRef) : Result :=
  ((c.snoc (.scale k p.forward)).snoc (.scale k p.reverse),
    ⟨c.length, c.length + 1⟩)

@[simp] theorem pairScale_length (c : Circuit) (k : ℤ) (p : PairRef) :
    (pairScale c k p).1.length = c.length + 2 := by
  simp [pairScale, Circuit.length]

theorem pairScale_extends (c : Circuit) (k : ℤ) (p : PairRef) :
    Extends c (pairScale c k p).1 := (Extends.refl c).snoc _ |>.snoc _

theorem pairScale_valid (c : Circuit) (k : ℤ) (p : PairRef) :
    (pairScale c k p).2.valid (pairScale c k p).1 := by
  simp only [PairRef.valid, pairScale, Circuit.length]; omega

theorem pairScale_safe {c : Circuit} {p : PairRef}
    (hc : c.safe) (hp : p.valid c) (k : ℤ) : (pairScale c k p).1.safe := by
  refine ⟨⟨hc, hp.1⟩, ?_⟩
  have := hp.2
  simp only [Gate.valid, Circuit.length]; omega

theorem pairScale_value {R : Type*} [Ring R] (a d : R) {c : Circuit}
    {p : PairRef} (hp : p.valid c) (k : ℤ) :
    (pairScale c k p).2.value (pairScale c k p).1 a d =
      (k • (p.value c a d).1, k • (p.value c a d).2) := by
  apply Prod.ext
  · change ((c.snoc (.scale k p.forward)).snoc (.scale k p.reverse)).value
      a d c.length = _
    rw [old_value a d _ _ _ (by simp [Circuit.length]), new_value]
    rfl
  · change ((c.snoc (.scale k p.forward)).snoc (.scale k p.reverse)).value
      a d (c.snoc (.scale k p.forward)).length = _
    rw [new_value]
    change k • (c.snoc (.scale k p.forward)).value a d p.reverse = _
    rw [old_value a d _ _ _ hp.2]
    rfl

def cell (N k j : ℕ) (c : Circuit) (prev : List PairRef) : Result :=
  let x := pairScale c ((N : ℤ)^2 * ((j : ℤ) - k)) oneRef
  let y := pairAdd x.1 dRef x.2
  let l := pairMul y.1 y.2 (if j ≤ k then prev.getD j zeroRef else zeroRef)
  let r := pairMul l.1 aRef (if 0 < j then prev.getD (j-1) zeroRef else zeroRef)
  let s := pairScale r.1 ((N : ℤ)^2) r.2
  pairAdd s.1 l.2 s.2

@[simp] theorem cell_length (N k j : ℕ) (c : Circuit) (prev : List PairRef) :
    (cell N k j c prev).1.length = c.length + 12 := by
  simp only [cell, pairAdd_length, pairMul_length, pairScale_length]

theorem cell_extends (N k j : ℕ) (c : Circuit) (prev : List PairRef) :
    Extends c (cell N k j c prev).1 := by
  let x := pairScale c ((N : ℤ)^2 * ((j : ℤ) - k)) oneRef
  let y := pairAdd x.1 dRef x.2
  let l := pairMul y.1 y.2 (if j ≤ k then prev.getD j zeroRef else zeroRef)
  let r := pairMul l.1 aRef (if 0 < j then prev.getD (j-1) zeroRef else zeroRef)
  let s := pairScale r.1 ((N : ℤ)^2) r.2
  exact (((((pairScale_extends c _ oneRef).trans (pairAdd_extends x.1 dRef x.2)).trans
    (pairMul_extends y.1 y.2 _)).trans (pairMul_extends l.1 aRef _)).trans
      (pairScale_extends r.1 _ r.2)).trans (pairAdd_extends s.1 l.2 s.2)

theorem cell_valid (N k j : ℕ) (c : Circuit) (prev : List PairRef) :
    (cell N k j c prev).2.valid (cell N k j c prev).1 :=
  pairAdd_valid _ _ _

theorem cell_safe {N k j : ℕ} {c : Circuit} {prev : List PairRef}
    (hc : c.safe) (h : Ready c prev) : (cell N k j c prev).1.safe := by
  let x := pairScale c ((N : ℤ)^2 * ((j : ℤ) - k)) oneRef
  let y := pairAdd x.1 dRef x.2
  let l := pairMul y.1 y.2 (if j ≤ k then prev.getD j zeroRef else zeroRef)
  let r := pairMul l.1 aRef (if 0 < j then prev.getD (j-1) zeroRef else zeroRef)
  let s := pairScale r.1 ((N : ℤ)^2) r.2
  have ex : Extends c x.1 := pairScale_extends _ _ _
  have ey : Extends c y.1 := ex.trans (pairAdd_extends _ _ _)
  have el : Extends c l.1 := ey.trans (pairMul_extends _ _ _)
  have es : Extends l.1 s.1 :=
    (pairMul_extends l.1 aRef _).trans (pairScale_extends r.1 _ r.2)
  have hp : (if j ≤ k then prev.getD j zeroRef else zeroRef).valid c := by
    split
    · exact getD_valid h _
    · exact h.2.2.2.1
  have hq : (if 0 < j then prev.getD (j-1) zeroRef else zeroRef).valid c := by
    split
    · exact getD_valid h _
    · exact h.2.2.2.1
  have hx : x.1.safe := pairScale_safe hc h.1 _
  have hy : y.1.safe := pairAdd_safe hx (PairRef.valid_extend h.2.2.1 ex)
    (pairScale_valid _ _ _)
  have hl : l.1.safe := pairMul_safe hy (pairAdd_valid _ _ _) (PairRef.valid_extend hp ey)
  have hr : r.1.safe := pairMul_safe hl (PairRef.valid_extend h.2.1 el)
    (PairRef.valid_extend hq el)
  have hs : s.1.safe := pairScale_safe hr (pairMul_valid _ _ _) _
  have hv : l.2.valid l.1 := pairMul_valid _ _ _
  exact pairAdd_safe hs (PairRef.valid_extend hv es) (pairScale_valid _ _ _)

def cells (N k : ℕ) (prev : List PairRef) (c : Circuit) : List ℕ → Circuit × List PairRef
  | [] => (c, [])
  | j :: js =>
      let x := cell N k j c prev
      let r := cells N k prev x.1 js
      (r.1, x.2 :: r.2)

@[simp] theorem cells_length (N k : ℕ) (prev : List PairRef) (c : Circuit)
    (js : List ℕ) : (cells N k prev c js).1.length = c.length + 12 * js.length := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih => simp only [cells, List.length_cons, ih, cell_length]; omega

@[simp] theorem cells_refs_length (N k : ℕ) (prev : List PairRef) (c : Circuit)
    (js : List ℕ) : (cells N k prev c js).2.length = js.length := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih => simp [cells, ih]

theorem cells_extends (N k : ℕ) (prev : List PairRef) (c : Circuit) (js : List ℕ) :
    Extends c (cells N k prev c js).1 := by
  induction js generalizing c with
  | nil => exact .refl c
  | cons j js ih => exact (cell_extends _ _ _ _ _).trans (ih _)

theorem cells_safe {N k : ℕ} {prev : List PairRef} {c : Circuit}
    (hc : c.safe) (h : Ready c prev) (js : List ℕ) :
    (cells N k prev c js).1.safe := by
  induction js generalizing c with
  | nil => exact hc
  | cons j js ih =>
    exact ih (cell_safe hc h) (ready_extend h (cell_extends _ _ _ _ _))

theorem cells_valid (N k : ℕ) (prev : List PairRef) (c : Circuit) (js : List ℕ) :
    ∀ p ∈ (cells N k prev c js).2, p.valid (cells N k prev c js).1 := by
  induction js generalizing c with
  | nil => simp [cells]
  | cons j js ih =>
    intro p hp
    simp only [cells, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact PairRef.valid_extend (cell_valid _ _ _ _ _) (cells_extends _ _ _ _ _)
    · exact ih _ p hp

structure State where
  circuit : Circuit
  lastRow : List PairRef
  probes : List PairRef

def build (N : ℕ) : ℕ → State
  | 0 => ⟨initial, [oneRef], [oneRef]⟩
  | k + 1 =>
      let s := build N k
      let r := cells N k s.lastRow s.circuit (List.range (k+2))
      ⟨r.1, r.2, s.probes ++ r.2⟩

theorem build_extends (N k : ℕ) : Extends initial (build N k).circuit := by
  induction k with
  | zero => exact .refl initial
  | succ k ih => exact ih.trans (cells_extends _ _ _ _ _)

@[simp] theorem build_lastRow_length (N k : ℕ) : (build N k).lastRow.length = k+1 := by
  cases k with
  | zero => rfl
  | succ k => simp [build, cells_refs_length]

theorem build_ready (N k : ℕ) : Ready (build N k).circuit (build N k).lastRow := by
  induction k with
  | zero => exact initial_ready
  | succ k ih =>
    have h := ready_extend ih (cells_extends N k (build N k).lastRow
      (build N k).circuit (List.range (k+2)))
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, cells_valid _ _ _ _ _⟩

theorem build_safe (N k : ℕ) : (build N k).circuit.safe := by
  induction k with
  | zero => exact initial_safe
  | succ k ih => exact cells_safe ih (build_ready N k) _

theorem build_probes_valid (N k : ℕ) :
    ∀ p ∈ (build N k).probes, p.valid (build N k).circuit := by
  induction k with
  | zero =>
    intro p hp
    simp only [build, List.mem_singleton] at hp
    subst p
    exact initial_ready.1
  | succ k ih =>
    intro p hp
    simp only [build, List.mem_append] at hp
    rcases hp with hp | hp
    · exact PairRef.valid_extend (ih p hp) (cells_extends _ _ _ _ _)
    · exact cells_valid _ _ _ _ _ p hp

theorem build_twice_probe_count (N k : ℕ) :
    2 * (build N k).probes.length = (k+1)*(k+2) := by
  induction k with
  | zero => simp [build]
  | succ k ih =>
    simp only [build, List.length_append, cells_refs_length, List.length_range]
    nlinarith

theorem build_exact_length (N k : ℕ) :
    (build N k).circuit.length = 4 + 6*k*(k+3) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [build, cells_length, List.length_range, ih]
    ring

def probePrefix (N : ℕ) : State := build N (N-1)

theorem prefix_safe (N : ℕ) : (probePrefix N).circuit.safe := build_safe _ _

theorem prefix_gate_bound (N : ℕ) (hN : 1 ≤ N) :
    (probePrefix N).circuit.length ≤ 12*N^2 + 4 := by
  rw [probePrefix, build_exact_length]
  have h : N-1+1=N := by omega
  nlinarith

theorem prefix_probe_count (N : ℕ) (hN : 1 ≤ N) :
    (probePrefix N).probes.length = N*(N+1)/2 := by
  change (build N (N-1)).probes.length = N*(N+1)/2
  have h := build_twice_probe_count N (N-1)
  have hs : N-1+1=N := by omega
  have ht : N-1+2=N+1 := by omega
  rw [hs, ht] at h
  omega

/-! These are the literal integer scalar labels used by the triangle. -/
def probeConstants (N : ℕ) : Set ℤ :=
  {z | z = (N : ℤ)^2 ∨ ∃ k j : ℕ,
    k < N-1 ∧ j < k+2 ∧ z = (N : ℤ)^2 * ((j : ℤ)-k)}

theorem initial_constants (allowed : Set ℤ) : initial.constantsAllowed allowed := by
  simp [initial, Circuit.constantsAllowed, Gate.constantsAllowed]

theorem pairScale_constants {c : Circuit} (allowed : Set ℤ) (k : ℤ) (p : PairRef)
    (hc : c.constantsAllowed allowed) (hk : k ∈ allowed) :
    (pairScale c k p).1.constantsAllowed allowed := ⟨⟨hc, hk⟩, hk⟩

theorem cell_constants {N k j : ℕ} {c : Circuit} {prev : List PairRef}
    (allowed : Set ℤ) (hc : c.constantsAllowed allowed)
    (hκ : (N : ℤ)^2 ∈ allowed) (hco : (N : ℤ)^2 * ((j : ℤ)-k) ∈ allowed) :
    (cell N k j c prev).1.constantsAllowed allowed := by
  unfold cell
  apply pairAdd_constants
  apply pairScale_constants
  · apply pairMul_constants
    apply pairMul_constants
    apply pairAdd_constants
    exact pairScale_constants allowed _ _ hc hco
  · exact hκ

theorem cells_constants {N k : ℕ} {prev : List PairRef} {c : Circuit}
    (allowed : Set ℤ) (hc : c.constantsAllowed allowed)
    (hκ : (N : ℤ)^2 ∈ allowed) (js : List ℕ)
    (hco : ∀ j ∈ js, (N : ℤ)^2 * ((j : ℤ)-k) ∈ allowed) :
    (cells N k prev c js).1.constantsAllowed allowed := by
  induction js generalizing c with
  | nil => exact hc
  | cons j js ih =>
    exact ih (cell_constants allowed hc hκ (hco j (List.mem_cons_self)))
      (fun i hi => hco i (List.mem_cons_of_mem _ hi))

theorem build_constants (N k : ℕ) (hk : k ≤ N-1) (allowed : Set ℤ)
    (hκ : (N : ℤ)^2 ∈ allowed)
    (hco : ∀ i < N-1, ∀ j < i+2, (N : ℤ)^2 * ((j : ℤ)-i) ∈ allowed) :
    (build N k).circuit.constantsAllowed allowed := by
  induction k with
  | zero => exact initial_constants allowed
  | succ k ih =>
    exact cells_constants allowed (ih (by omega)) hκ _
      (fun j hj => hco k (by omega) j (List.mem_range.mp hj))

theorem prefix_constants_of (N : ℕ) (allowed : Set ℤ)
    (hκ : (N : ℤ)^2 ∈ allowed)
    (hco : ∀ k < N-1, ∀ j < k+2, (N : ℤ)^2 * ((j : ℤ)-k) ∈ allowed) :
    (probePrefix N).circuit.constantsAllowed allowed :=
  build_constants N (N-1) (le_refl _) allowed hκ hco

theorem prefix_constants (N : ℕ) :
    (probePrefix N).circuit.constantsAllowed (probeConstants N) := by
  apply prefix_constants_of
  · exact Or.inl rfl
  · intro k hk j hj
    exact Or.inr ⟨k, j, hk, hj, rfl⟩

theorem probeConstants_abs_bound (N : ℕ) (hN : 1 ≤ N) {z : ℤ}
    (hz : z ∈ probeConstants N) : |z| ≤ (N : ℤ)^3 := by
  have hn : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hκ : |(N : ℤ)^2| = (N : ℤ)^2 := abs_of_nonneg (sq_nonneg _)
  rcases hz with rfl | ⟨k, j, hk, hj, rfl⟩
  · rw [hκ]
    nlinarith [sq_nonneg ((N : ℤ)-1)]
  · have hlo : -(N : ℤ) ≤ (j : ℤ)-k := by omega
    have hhi : (j : ℤ)-k ≤ (N : ℤ) := by omega
    have hdiff : |(j : ℤ)-k| ≤ (N : ℤ) := abs_le.mpr ⟨hlo, hhi⟩
    rw [abs_mul, hκ]
    nlinarith [sq_nonneg (N : ℤ)]

#print axioms prefix_gate_bound
#print axioms prefix_safe

section Semantics

variable {R : Type*} [Ring R]

theorem one_value (a d : R) {c : Circuit} (h : Extends initial c) :
    oneRef.value c a d = (1, 1) := by
  rw [PairRef.value_extend initial_ready.1 h a d]
  simp [oneRef, PairRef.value, Circuit.value, initial, Circuit.eval, Gate.eval]

theorem a_value (a d : R) {c : Circuit} (h : Extends initial c) :
    aRef.value c a d = (a, a) := by
  rw [PairRef.value_extend initial_ready.2.1 h a d]
  simp [aRef, PairRef.value, Circuit.value, initial, Circuit.eval, Gate.eval]

theorem d_value (a d : R) {c : Circuit} (h : Extends initial c) :
    dRef.value c a d = (d, d) := by
  rw [PairRef.value_extend initial_ready.2.2.1 h a d]
  simp [dRef, PairRef.value, Circuit.value, initial, Circuit.eval, Gate.eval]

theorem zero_value (a d : R) {c : Circuit} (h : Extends initial c) :
    zeroRef.value c a d = (0, 0) := by
  rw [PairRef.value_extend initial_ready.2.2.2.1 h a d]
  simp [zeroRef, PairRef.value, Circuit.value, initial, Circuit.eval, Gate.eval]

def stepValue (N k j : ℕ) (a d : R) (c : Circuit) (prev : List PairRef) : R × R :=
  let p := (if j ≤ k then prev.getD j zeroRef else zeroRef).value c a d
  let q := (if 0 < j then prev.getD (j-1) zeroRef else zeroRef).value c a d
  let coefficient : ℤ := (N : ℤ)^2 * ((j : ℤ)-k)
  ((d + coefficient • 1) * p.1 + (N : ℤ)^2 • (a * q.1),
    p.2 * (d + coefficient • 1) + (N : ℤ)^2 • (q.2 * a))

theorem stepValue_extend (N k j : ℕ) (a d : R) {c t : Circuit}
    {prev : List PairRef} (h : Ready c prev) (he : Extends c t) :
    stepValue N k j a d t prev = stepValue N k j a d c prev := by
  have hp : (if j ≤ k then prev.getD j zeroRef else zeroRef).valid c := by
    split
    · exact getD_valid h _
    · exact h.2.2.2.1
  have hq : (if 0 < j then prev.getD (j-1) zeroRef else zeroRef).valid c := by
    split
    · exact getD_valid h _
    · exact h.2.2.2.1
  simp only [stepValue, PairRef.value_extend hp he a d,
    PairRef.value_extend hq he a d]

theorem cell_value (N k j : ℕ) (a d : R) {c : Circuit} {prev : List PairRef}
    (h : Ready c prev) (he : Extends initial c) :
    (cell N k j c prev).2.value (cell N k j c prev).1 a d =
      stepValue N k j a d c prev := by
  let coefficient : ℤ := (N : ℤ)^2 * ((j : ℤ)-k)
  let p := if j ≤ k then prev.getD j zeroRef else zeroRef
  let q := if 0 < j then prev.getD (j-1) zeroRef else zeroRef
  let x := pairScale c coefficient oneRef
  let y := pairAdd x.1 dRef x.2
  let l := pairMul y.1 y.2 p
  let r := pairMul l.1 aRef q
  let s := pairScale r.1 ((N : ℤ)^2) r.2
  have ex : Extends c x.1 := pairScale_extends _ _ _
  have ey : Extends c y.1 := ex.trans (pairAdd_extends _ _ _)
  have el : Extends c l.1 := ey.trans (pairMul_extends _ _ _)
  have es : Extends l.1 s.1 :=
    (pairMul_extends l.1 aRef q).trans (pairScale_extends r.1 _ r.2)
  have hp : p.valid c := by
    dsimp only [p]; split
    · exact getD_valid h _
    · exact h.2.2.2.1
  have hq : q.valid c := by
    dsimp only [q]; split
    · exact getD_valid h _
    · exact h.2.2.2.1
  have vx : x.2.value x.1 a d = (coefficient • (1 : R), coefficient • (1 : R)) := by
    rw [pairScale_value a d h.1 coefficient, one_value a d he]
  have vy : y.2.value y.1 a d =
      (d + coefficient • (1 : R), d + coefficient • (1 : R)) := by
    rw [pairAdd_value a d (PairRef.valid_extend h.2.2.1 ex) (pairScale_valid _ _ _)]
    rw [PairRef.value_extend h.2.2.1 ex a d, d_value a d he, vx]
  have vl : l.2.value l.1 a d =
      ((d + coefficient • 1) * (p.value c a d).1,
        (p.value c a d).2 * (d + coefficient • 1)) := by
    rw [pairMul_value a d (pairAdd_valid _ _ _) (PairRef.valid_extend hp ey)]
    rw [vy, PairRef.value_extend hp ey a d]
  have vr : r.2.value r.1 a d =
      (a * (q.value c a d).1, (q.value c a d).2 * a) := by
    rw [pairMul_value a d (PairRef.valid_extend h.2.1 el) (PairRef.valid_extend hq el)]
    rw [PairRef.value_extend h.2.1 el a d, a_value a d he,
      PairRef.value_extend hq el a d]
  have vs : s.2.value s.1 a d =
      ((N : ℤ)^2 • (a * (q.value c a d).1), (N : ℤ)^2 • ((q.value c a d).2 * a)) := by
    rw [pairScale_value a d (pairMul_valid _ _ _) ((N : ℤ)^2), vr]
  change (pairAdd s.1 l.2 s.2).2.value (pairAdd s.1 l.2 s.2).1 a d = _
  rw [pairAdd_value a d (PairRef.valid_extend (pairMul_valid _ _ _) es)
    (pairScale_valid _ _ _)]
  rw [PairRef.value_extend (pairMul_valid _ _ _) es a d, vl, vs]
  rfl

theorem cells_values (N k : ℕ) (a d : R) {c : Circuit} {prev : List PairRef}
    (h : Ready c prev) (he : Extends initial c) (js : List ℕ) :
    (cells N k prev c js).2.map (fun p => p.value (cells N k prev c js).1 a d) =
      js.map (fun j => stepValue N k j a d c prev) := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih =>
    simp only [cells, List.map_cons]
    congr 1
    · rw [PairRef.value_extend (cell_valid _ _ _ _ _) (cells_extends _ _ _ _ _) a d]
      exact cell_value N k j a d h he
    · rw [ih (ready_extend h (cell_extends _ _ _ _ _))
        (he.trans (cell_extends _ _ _ _ _))]
      apply List.map_congr_left
      intro i _
      exact stepValue_extend N k i a d h (cell_extends _ _ _ _ _)

def exprPair (a d : R) (p : Degrees.Expr) : R × R := (p.eval a d, p.reverse.eval a d)

def rowValues (N k : ℕ) (a d : R) : List (R × R) :=
  (Degrees.row N k).map (exprPair a d)

theorem rowValues_getD (N k j : ℕ) (a d : R) (hj : j ≤ k) :
    (rowValues N k a d).getD j (0, 0) = exprPair a d (Degrees.probe N k j) := by
  have hj' : j < (rowValues N k a d).length := by
    simp only [rowValues, List.length_map, Degrees.row_length]; omega
  rw [List.getD_eq_getElem _ _ hj']
  simp only [rowValues, Degrees.row, List.getElem_map, List.getElem_ofFn]

theorem stepValue_row (N k j : ℕ) (a d : R) {c : Circuit} {prev : List PairRef}
    (he : Extends initial c)
    (hv : prev.map (fun p => p.value c a d) = rowValues N k a d) (hj : j < k+2) :
    stepValue N k j a d c prev = exprPair a d (Degrees.probe N (k+1) j) := by
  have hg (i : ℕ) (hi : i ≤ k) :
      (prev.getD i zeroRef).value c a d = exprPair a d (Degrees.probe N k i) := by
    rw [← List.getD_map prev zeroRef (fun p => p.value c a d)]
    rw [zero_value a d he, hv, rowValues_getD N k i a d hi]
  by_cases hleft : j ≤ k <;> by_cases hright : 0 < j
  · simp only [stepValue, hleft, hright, ite_true]
    rw [hg j hleft, hg (j-1) (by omega)]
    simp [exprPair, Degrees.probe, Degrees.Expr.eval, Degrees.Expr.reverse, hleft, hright]
  · simp only [stepValue, hleft, hright, ite_true, ite_false]
    rw [hg j hleft, zero_value a d he]
    simp [exprPair, Degrees.probe, Degrees.Expr.eval, Degrees.Expr.reverse, hleft, hright]
  · simp only [stepValue, hleft, hright, ite_true, ite_false]
    rw [zero_value a d he, hg (j-1) (by omega)]
    simp [exprPair, Degrees.probe, Degrees.Expr.eval, Degrees.Expr.reverse, hleft, hright]
  · simp only [stepValue, hleft, hright, ite_false]
    rw [zero_value a d he]
    simp [exprPair, Degrees.probe, Degrees.Expr.eval, Degrees.Expr.reverse, hleft, hright]

theorem build_row_values (N k : ℕ) (a d : R) :
    (build N k).lastRow.map (fun p => p.value (build N k).circuit a d) =
      rowValues N k a d := by
  induction k with
  | zero => simp [build, rowValues, Degrees.row, Degrees.probe, exprPair,
      Degrees.Expr.eval, Degrees.Expr.reverse, one_value a d (.refl initial)]
  | succ k ih =>
    change (cells N k (build N k).lastRow (build N k).circuit (List.range (k+2))).2.map
      (fun p => p.value (cells N k (build N k).lastRow (build N k).circuit
        (List.range (k+2))).1 a d) = _
    rw [cells_values N k a d (build_ready N k) (build_extends N k)]
    have hm : (List.range (k+2)).map (fun j => stepValue N k j a d (build N k).circuit
        (build N k).lastRow) = (List.range (k+2)).map
        (fun j => exprPair a d (Degrees.probe N (k+1) j)) := by
      apply List.map_congr_left
      intro j hj
      exact stepValue_row N k j a d (build_extends N k) ih (List.mem_range.mp hj)
    rw [hm]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, rowValues, Degrees.row_length]
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range, rowValues, Degrees.row,
        List.getElem_ofFn]

theorem build_probe_values (N k : ℕ) (a d : R) :
    (build N k).probes.map (fun p => p.value (build N k).circuit a d) =
      (Degrees.probeList N (k+1)).map (exprPair a d) := by
  induction k with
  | zero => simp [build, Degrees.probeList, Degrees.row, Degrees.probe, exprPair,
      Degrees.Expr.eval, Degrees.Expr.reverse, one_value a d (.refl initial)]
  | succ k ih =>
    have hold : (build N k).probes.map (fun p => p.value (build N (k+1)).circuit a d) =
        (build N k).probes.map (fun p => p.value (build N k).circuit a d) := by
      apply List.map_congr_left
      intro p hp
      exact PairRef.value_extend (build_probes_valid N k p hp) (cells_extends _ _ _ _ _) a d
    have hrow := build_row_values N (k+1) a d
    change ((build N k).probes ++ (build N (k+1)).lastRow).map _ = _
    rw [List.map_append, hold, ih, hrow]
    simp only [rowValues, Degrees.probeList, List.map_append]

theorem prefix_probe_values (N : ℕ) (hN : 1 ≤ N) (a d : R) :
    (probePrefix N).probes.map (fun p => p.value (probePrefix N).circuit a d) =
      (Degrees.probeList N N).map (exprPair a d) := by
  have h := build_probe_values N (N-1) a d
  have hs : N-1+1=N := by omega
  simpa only [hs, probePrefix] using h

end Semantics

#print axioms prefix_probe_values

end CircuitAudit.ProbeCircuit
