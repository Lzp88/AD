import Mathlib

/-! Executable instruction DAGs. Adjoint companions are compiled by reversing
products; there is no transpose or adjoint instruction. -/
namespace CircuitAudit.CircuitCosts

inductive Gate where
  | zero | ident | atomA | atomD
  | add (left right : ℕ)
  | mul (left right : ℕ)
  | scale (constant : ℤ) (input : ℕ)
  deriving DecidableEq, Repr

def Gate.valid (n : ℕ) : Gate → Prop
  | .zero | .ident | .atomA | .atomD => True
  | .add i j | .mul i j => i < n ∧ j < n
  | .scale _ i => i < n

def Gate.eval {R : Type*} [Ring R] (a d : R) (values : List R) : Gate → R
  | .zero => 0
  | .ident => 1
  | .atomA => a
  | .atomD => d
  | .add i j => values.getD i 0 + values.getD j 0
  | .mul i j => values.getD i 0 * values.getD j 0
  | .scale k i => k • values.getD i 0

inductive Circuit where
  | empty
  | snoc (previous : Circuit) (instruction : Gate)
  deriving Repr

def Circuit.length : Circuit → ℕ
  | .empty => 0
  | .snoc c _ => c.length + 1

def Circuit.safe : Circuit → Prop
  | .empty => True
  | .snoc c g => c.safe ∧ g.valid c.length

def Circuit.eval {R : Type*} [Ring R] (a d : R) : Circuit → List R
  | .empty => []
  | .snoc c g => c.eval a d ++ [g.eval a d (c.eval a d)]

def Circuit.value {R : Type*} [Ring R] (c : Circuit) (a d : R) (i : ℕ) : R :=
  (c.eval a d).getD i 0

@[simp] theorem eval_length {R : Type*} [Ring R] (a d : R) (c : Circuit) :
    (c.eval a d).length = c.length := by
  induction c with
  | empty => rfl
  | snoc c g ih => simp [Circuit.eval, Circuit.length, ih]

theorem old_value {R : Type*} [Ring R] (a d : R) (c : Circuit) (g : Gate)
    (i : ℕ) (hi : i < c.length) :
    (c.snoc g).value a d i = c.value a d i := by
  exact List.getD_append _ _ _ _ (by simpa using hi)

@[simp] theorem new_value {R : Type*} [Ring R] (a d : R) (c : Circuit) (g : Gate) :
    (c.snoc g).value a d c.length = g.eval a d (c.eval a d) := by
  change (c.eval a d ++ [g.eval a d (c.eval a d)]).getD c.length 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

inductive Extends : Circuit → Circuit → Prop where
  | refl (c) : Extends c c
  | snoc {c t} (h : Extends c t) (g) : Extends c (t.snoc g)

theorem Extends.trans {c t u : Circuit} (h : Extends c t) (k : Extends t u) :
    Extends c u := by
  induction k with
  | refl => exact h
  | snoc k g ih => exact ih.snoc g

theorem Extends.length_le {c t : Circuit} (h : Extends c t) : c.length ≤ t.length := by
  induction h with
  | refl => exact le_rfl
  | snoc h g ih => simp only [Circuit.length]; omega

theorem Extends.value_eq {R : Type*} [Ring R] {c t : Circuit} (h : Extends c t)
    (a d : R) (i : ℕ) (hi : i < c.length) : t.value a d i = c.value a d i := by
  induction h with
  | refl => rfl
  | @snoc t h g ih =>
    rw [old_value a d t g i (lt_of_lt_of_le hi h.length_le)]
    exact ih

structure PairRef where
  forward : ℕ
  reverse : ℕ
  deriving Repr

def PairRef.valid (p : PairRef) (c : Circuit) : Prop :=
  p.forward < c.length ∧ p.reverse < c.length

def PairRef.value {R : Type*} [Ring R] (p : PairRef) (c : Circuit) (a d : R) : R × R :=
  (c.value a d p.forward, c.value a d p.reverse)

theorem PairRef.valid_extend {p : PairRef} {c t : Circuit}
    (hp : p.valid c) (h : Extends c t) : p.valid t :=
  ⟨lt_of_lt_of_le hp.1 h.length_le, lt_of_lt_of_le hp.2 h.length_le⟩

theorem PairRef.valid_length {p : PairRef} {c t : Circuit}
    (hp : p.valid c) (h : c.length ≤ t.length) : p.valid t :=
  ⟨lt_of_lt_of_le hp.1 h, lt_of_lt_of_le hp.2 h⟩

theorem PairRef.value_extend {R : Type*} [Ring R] {p : PairRef} {c t : Circuit}
    (hp : p.valid c) (h : Extends c t) (a d : R) :
    p.value t a d = p.value c a d := by
  simp only [PairRef.value, h.value_eq a d p.forward hp.1,
    h.value_eq a d p.reverse hp.2]

abbrev Result := Circuit × PairRef

def pairAdd (c : Circuit) (p q : PairRef) : Result :=
  ((c.snoc (.add p.forward q.forward)).snoc (.add p.reverse q.reverse),
    ⟨c.length, c.length + 1⟩)

def pairMul (c : Circuit) (p q : PairRef) : Result :=
  ((c.snoc (.mul p.forward q.forward)).snoc (.mul q.reverse p.reverse),
    ⟨c.length, c.length + 1⟩)

def pairZero (c : Circuit) : Result := (c.snoc .zero, ⟨c.length, c.length⟩)

@[simp] theorem pairAdd_length (c : Circuit) (p q : PairRef) :
    (pairAdd c p q).1.length = c.length + 2 := by simp [pairAdd, Circuit.length]
@[simp] theorem pairMul_length (c : Circuit) (p q : PairRef) :
    (pairMul c p q).1.length = c.length + 2 := by simp [pairMul, Circuit.length]
@[simp] theorem pairZero_length (c : Circuit) :
    (pairZero c).1.length = c.length + 1 := rfl

theorem pairAdd_extends (c : Circuit) (p q : PairRef) :
    Extends c (pairAdd c p q).1 := (Extends.refl c).snoc _ |>.snoc _
theorem pairMul_extends (c : Circuit) (p q : PairRef) :
    Extends c (pairMul c p q).1 := (Extends.refl c).snoc _ |>.snoc _
theorem pairZero_extends (c : Circuit) :
    Extends c (pairZero c).1 := (Extends.refl c).snoc _

theorem pairAdd_valid (c : Circuit) (p q : PairRef) :
    (pairAdd c p q).2.valid (pairAdd c p q).1 := by
  simp only [PairRef.valid, pairAdd, Circuit.length]; omega
theorem pairMul_valid (c : Circuit) (p q : PairRef) :
    (pairMul c p q).2.valid (pairMul c p q).1 := by
  simp only [PairRef.valid, pairMul, Circuit.length]; omega
theorem pairZero_valid (c : Circuit) :
    (pairZero c).2.valid (pairZero c).1 := by
  simp only [PairRef.valid, pairZero, Circuit.length]; omega

theorem pairAdd_safe {c : Circuit} {p q : PairRef}
    (hc : c.safe) (hp : p.valid c) (hq : q.valid c) : (pairAdd c p q).1.safe := by
  refine ⟨⟨hc, hp.1, hq.1⟩, ?_⟩
  have hp' := hp.2
  have hq' := hq.2
  simp only [Gate.valid, Circuit.length]; constructor <;> omega
theorem pairMul_safe {c : Circuit} {p q : PairRef}
    (hc : c.safe) (hp : p.valid c) (hq : q.valid c) : (pairMul c p q).1.safe := by
  refine ⟨⟨hc, hp.1, hq.1⟩, ?_⟩
  have hp' := hp.2
  have hq' := hq.2
  simp only [Gate.valid, Circuit.length]; constructor <;> omega
theorem pairZero_safe {c : Circuit} (hc : c.safe) : (pairZero c).1.safe := ⟨hc, trivial⟩

theorem pairAdd_value {R : Type*} [Ring R] (a d : R) {c : Circuit} {p q : PairRef}
    (hp : p.valid c) (hq : q.valid c) :
    (pairAdd c p q).2.value (pairAdd c p q).1 a d =
      ((p.value c a d).1 + (q.value c a d).1,
       (p.value c a d).2 + (q.value c a d).2) := by
  apply Prod.ext
  · change ((c.snoc (.add p.forward q.forward)).snoc (.add p.reverse q.reverse)).value
      a d c.length = _
    rw [old_value a d _ _ _ (by simp [Circuit.length]), new_value]
    rfl
  · change ((c.snoc (.add p.forward q.forward)).snoc (.add p.reverse q.reverse)).value
      a d (c.snoc (.add p.forward q.forward)).length = _
    rw [new_value]
    change (c.snoc (.add p.forward q.forward)).value a d p.reverse +
      (c.snoc (.add p.forward q.forward)).value a d q.reverse = _
    rw [old_value a d _ _ _ hp.2, old_value a d _ _ _ hq.2]
    rfl

theorem pairMul_value {R : Type*} [Ring R] (a d : R) {c : Circuit} {p q : PairRef}
    (hp : p.valid c) (hq : q.valid c) :
    (pairMul c p q).2.value (pairMul c p q).1 a d =
      ((p.value c a d).1 * (q.value c a d).1,
       (q.value c a d).2 * (p.value c a d).2) := by
  apply Prod.ext
  · change ((c.snoc (.mul p.forward q.forward)).snoc (.mul q.reverse p.reverse)).value
      a d c.length = _
    rw [old_value a d _ _ _ (by simp [Circuit.length]), new_value]
    rfl
  · change ((c.snoc (.mul p.forward q.forward)).snoc (.mul q.reverse p.reverse)).value
      a d (c.snoc (.mul p.forward q.forward)).length = _
    rw [new_value]
    change (c.snoc (.mul p.forward q.forward)).value a d q.reverse *
      (c.snoc (.mul p.forward q.forward)).value a d p.reverse = _
    rw [old_value a d _ _ _ hq.2, old_value a d _ _ _ hp.2]
    rfl

@[simp] theorem pairZero_value {R : Type*} [Ring R] (a d : R) (c : Circuit) :
    (pairZero c).2.value (pairZero c).1 a d = (0, 0) := by
  simp [pairZero, PairRef.value, new_value, Gate.eval]

/-- Each scalar-power step emits one multiplication pair. -/
def pairPow (c : Circuit) (base one : PairRef) : ℕ → Result
  | 0 => (c, one)
  | n + 1 => let r := pairPow c base one n; pairMul r.1 base r.2

@[simp] theorem pairPow_length (c : Circuit) (base one : PairRef) (n : ℕ) :
    (pairPow c base one n).1.length = c.length + 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairPow, ih]; omega

theorem pairPow_extends (c : Circuit) (base one : PairRef) (n : ℕ) :
    Extends c (pairPow c base one n).1 := by
  induction n with
  | zero => exact .refl c
  | succ n ih => exact ih.trans (pairMul_extends _ _ _)

theorem pairPow_valid {c : Circuit} {base one : PairRef}
    (hone : one.valid c) (n : ℕ) :
    (pairPow c base one n).2.valid (pairPow c base one n).1 := by
  cases n with
  | zero => exact hone
  | succ n => exact pairMul_valid _ _ _

theorem pairPow_safe {c : Circuit} {base one : PairRef}
    (hc : c.safe) (hb : base.valid c) (ho : one.valid c) (n : ℕ) :
    (pairPow c base one n).1.safe := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    exact pairMul_safe ih
      (PairRef.valid_extend hb (pairPow_extends c base one n)) (pairPow_valid ho n)

/-- Listed-order Horner: u₀ + base (u₁ + base (...)). -/
def pairHorner (c : Circuit) (base : PairRef) : List PairRef → Result
  | [] => pairZero c
  | p :: ps =>
      let r := pairHorner c base ps
      let t := pairMul r.1 base r.2
      pairAdd t.1 p t.2

@[simp] theorem pairHorner_length (c : Circuit) (base : PairRef) (ps : List PairRef) :
    (pairHorner c base ps).1.length = c.length + 4 * ps.length + 1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [pairHorner, ih]; omega

theorem pairHorner_extends (c : Circuit) (base : PairRef) (ps : List PairRef) :
    Extends c (pairHorner c base ps).1 := by
  induction ps with
  | nil => exact pairZero_extends c
  | cons p ps ih => exact (ih.trans (pairMul_extends _ _ _)).trans (pairAdd_extends _ _ _)

theorem pairHorner_valid (c : Circuit) (base : PairRef) (ps : List PairRef) :
    (pairHorner c base ps).2.valid (pairHorner c base ps).1 := by
  cases ps with
  | nil => exact pairZero_valid _
  | cons p ps => exact pairAdd_valid _ _ _

theorem pairHorner_safe {c : Circuit} {base : PairRef} (hc : c.safe)
    (hb : base.valid c) {ps : List PairRef} (hp : ∀ p ∈ ps, p.valid c) :
    (pairHorner c base ps).1.safe := by
  induction ps with
  | nil => exact pairZero_safe hc
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q.valid c := fun q hq => hp q (by simp [hq])
    have hp' := PairRef.valid_extend (hp p (by simp))
      ((pairHorner_extends c base ps).trans
        (pairMul_extends (pairHorner c base ps).1 base (pairHorner c base ps).2))
    exact pairAdd_safe (pairMul_safe (ih htail)
      (PairRef.valid_extend hb (pairHorner_extends c base ps)) (pairHorner_valid _ _ _)) hp'
      (pairMul_valid _ _ _)

def mulValue {R : Type*} [Ring R] (p q : R × R) : R × R :=
  (p.1 * q.1, q.2 * p.2)

def powerValue {R : Type*} [Ring R] (base one : R × R) : ℕ → R × R
  | 0 => one
  | n + 1 => mulValue base (powerValue base one n)

theorem pairPow_value {R : Type*} [Ring R] (a d : R) {c : Circuit}
    {base one : PairRef} (hb : base.valid c) (ho : one.valid c) (n : ℕ) :
    (pairPow c base one n).2.value (pairPow c base one n).1 a d =
      powerValue (base.value c a d) (one.value c a d) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairPow, powerValue]
    rw [pairMul_value a d
      (PairRef.valid_extend hb (pairPow_extends c base one n)) (pairPow_valid ho n)]
    rw [PairRef.value_extend hb (pairPow_extends c base one n) a d, ih]
    rfl

theorem powerValue_one {R : Type*} [Ring R] (base : R × R) (n : ℕ) :
    powerValue base (1, 1) n = (base.1 ^ n, base.2 ^ n) := by
  induction n with
  | zero => simp [powerValue]
  | succ n ih =>
    simp only [powerValue, mulValue, ih]
    exact Prod.ext (pow_succ' _ _).symm (pow_succ _ _).symm

def hornerValue {R : Type*} [Ring R] (base : R × R) : List (R × R) → R × R
  | [] => (0, 0)
  | p :: ps =>
      (p.1 + base.1 * (hornerValue base ps).1,
       p.2 + (hornerValue base ps).2 * base.2)

theorem pairHorner_value {R : Type*} [Ring R] (a d : R) {c : Circuit}
    {base : PairRef} (hb : base.valid c) {ps : List PairRef}
    (hp : ∀ p ∈ ps, p.valid c) :
    (pairHorner c base ps).2.value (pairHorner c base ps).1 a d =
      hornerValue (base.value c a d) (ps.map (fun p => p.value c a d)) := by
  induction ps with
  | nil => exact pairZero_value a d c
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q.valid c := fun q hq => hp q (by simp [hq])
    have hext := (pairHorner_extends c base ps).trans
      (pairMul_extends (pairHorner c base ps).1 base (pairHorner c base ps).2)
    simp only [pairHorner, List.map_cons, hornerValue]
    rw [pairAdd_value a d (PairRef.valid_extend (hp p (by simp)) hext)
      (pairMul_valid _ _ _)]
    rw [PairRef.value_extend (hp p (by simp)) hext a d]
    rw [pairMul_value a d
      (PairRef.valid_extend hb (pairHorner_extends c base ps)) (pairHorner_valid _ _ _)]
    rw [PairRef.value_extend hb (pairHorner_extends c base ps) a d, ih htail]

def PairRef.swap (p : PairRef) : PairRef := ⟨p.reverse, p.forward⟩

theorem PairRef.swap_valid {p : PairRef} {c : Circuit} (hp : p.valid c) :
    p.swap.valid c := ⟨hp.2, hp.1⟩

@[simp] theorem PairRef.swap_value {R : Type*} [Ring R]
    (p : PairRef) (c : Circuit) (a d : R) :
    p.swap.value c a d = ((p.value c a d).2, (p.value c a d).1) := rfl

/-- Only b is used as a newly introduced integer scale constant. -/
def scalarBase (c : Circuit) (one : PairRef) (b : ℤ) : Result :=
  (c.snoc (.scale b one.forward), ⟨c.length, c.length⟩)

@[simp] theorem scalarBase_length (c : Circuit) (one : PairRef) (b : ℤ) :
    (scalarBase c one b).1.length = c.length + 1 := rfl

theorem scalarBase_extends (c : Circuit) (one : PairRef) (b : ℤ) :
    Extends c (scalarBase c one b).1 := (Extends.refl c).snoc _

theorem scalarBase_valid (c : Circuit) (one : PairRef) (b : ℤ) :
    (scalarBase c one b).2.valid (scalarBase c one b).1 := by
  simp only [scalarBase, PairRef.valid, Circuit.length]; omega

theorem scalarBase_safe {c : Circuit} {one : PairRef} (hc : c.safe)
    (ho : one.valid c) (b : ℤ) : (scalarBase c one b).1.safe := ⟨hc, ho.1⟩

theorem scalarBase_value {R : Type*} [Ring R]
    (a d : R) (c : Circuit) (one : PairRef) (b : ℤ) :
    (scalarBase c one b).2.value (scalarBase c one b).1 a d =
      (b • (one.value c a d).1, b • (one.value c a d).1) := by
  change ((c.snoc (.scale b one.forward)).value a d c.length,
    (c.snoc (.scale b one.forward)).value a d c.length) = _
  rw [new_value]
  rfl

/-- The actual compressed DAG. All powers use shared multiplication nodes.
    Inputs are existing paired references, and the only new scale input is b. -/
def compress (c : Circuit) (one a d j : PairRef) (b : ℤ) (M : ℕ)
    (probes : List PairRef) : Result :=
  let base := scalarBase c one b
  let stride := pairPow base.1 base.2 one M
  let block := pairPow stride.1 stride.2 one M
  let blockSq := pairMul block.1 block.2 block.2
  let y := pairHorner blockSq.1 base.2 probes
  let z := pairHorner y.1 stride.2 probes
  let sa := pairMul z.1 block.2 a
  let sd := pairMul sa.1 blockSq.2 d
  let s1 := pairAdd sd.1 one sa.2
  let s := pairAdd s1.1 s1.2 sd.2
  let q1 := pairMul s.1 j z.2.swap
  let q2 := pairMul q1.1 q1.2 s.2
  let q := pairMul q2.1 q2.2 y.2
  pairAdd q.1 q.2 q.2.swap

theorem compress_length (c : Circuit) (one a d j : PairRef) (b : ℤ) (M : ℕ)
    (probes : List PairRef) :
    (compress c one a d j b M probes).1.length =
      c.length + 4 * M + 8 * probes.length + 21 := by
  simp only [compress, pairAdd_length, pairMul_length, pairHorner_length,
    pairPow_length, scalarBase_length]
  omega

theorem compress_length_equal (c : Circuit) (one a d j : PairRef) (b : ℤ) (M : ℕ)
    (probes : List PairRef) (h : probes.length = M) :
    (compress c one a d j b M probes).1.length = c.length + 12 * M + 21 := by
  rw [compress_length, h]; omega

theorem compress_valid (c : Circuit) (one a d j : PairRef) (b : ℤ) (M : ℕ)
    (probes : List PairRef) :
    (compress c one a d j b M probes).2.valid (compress c one a d j b M probes).1 := by
  unfold compress
  exact pairAdd_valid _ _ _

theorem compress_extends (c : Circuit) (one a d j : PairRef) (b : ℤ) (M : ℕ)
    (probes : List PairRef) : Extends c (compress c one a d j b M probes).1 := by
  unfold compress
  apply Extends.trans (scalarBase_extends c one b)
  apply Extends.trans (pairPow_extends _ _ _ M)
  apply Extends.trans (pairPow_extends _ _ _ M)
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairHorner_extends _ _ _)
  apply Extends.trans (pairHorner_extends _ _ _)
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairAdd_extends _ _ _)
  apply Extends.trans (pairAdd_extends _ _ _)
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairMul_extends _ _ _)
  exact pairAdd_extends _ _ _

theorem compress_safe {c : Circuit} {one a d j : PairRef} (b : ℤ) (M : ℕ)
    {probes : List PairRef} (hc : c.safe) (ho : one.valid c) (ha : a.valid c)
    (hd : d.valid c) (hj : j.valid c) (hp : ∀ p ∈ probes, p.valid c) :
    (compress c one a d j b M probes).1.safe := by
  let base := scalarBase c one b
  let stride := pairPow base.1 base.2 one M
  let block := pairPow stride.1 stride.2 one M
  let blockSq := pairMul block.1 block.2 block.2
  let y := pairHorner blockSq.1 base.2 probes
  let z := pairHorner y.1 stride.2 probes
  let sa := pairMul z.1 block.2 a
  let sd := pairMul sa.1 blockSq.2 d
  let s1 := pairAdd sd.1 one sa.2
  let s := pairAdd s1.1 s1.2 sd.2
  let q1 := pairMul s.1 j z.2.swap
  let q2 := pairMul q1.1 q1.2 s.2
  let q := pairMul q2.1 q2.2 y.2
  have lb : base.1.length = c.length + 1 := scalarBase_length _ _ _
  have ls : stride.1.length = base.1.length + 2 * M := pairPow_length _ _ _ _
  have lk : block.1.length = stride.1.length + 2 * M := pairPow_length _ _ _ _
  have lk2 : blockSq.1.length = block.1.length + 2 := pairMul_length _ _ _
  have ly : y.1.length = blockSq.1.length + 4 * probes.length + 1 := pairHorner_length _ _ _
  have lz : z.1.length = y.1.length + 4 * probes.length + 1 := pairHorner_length _ _ _
  have lsa : sa.1.length = z.1.length + 2 := pairMul_length _ _ _
  have lsd : sd.1.length = sa.1.length + 2 := pairMul_length _ _ _
  have ls1 : s1.1.length = sd.1.length + 2 := pairAdd_length _ _ _
  have lS : s.1.length = s1.1.length + 2 := pairAdd_length _ _ _
  have lq1 : q1.1.length = s.1.length + 2 := pairMul_length _ _ _
  have lq2 : q2.1.length = q1.1.length + 2 := pairMul_length _ _ _
  have vb := scalarBase_valid c one b
  have vs : stride.2.valid stride.1 := pairPow_valid
    (PairRef.valid_length ho (by omega)) M
  have vk : block.2.valid block.1 := pairPow_valid
    (PairRef.valid_length ho (by omega)) M
  have vk2 := pairMul_valid block.1 block.2 block.2
  have vy := pairHorner_valid blockSq.1 base.2 probes
  have vz := pairHorner_valid y.1 stride.2 probes
  have vsa := pairMul_valid z.1 block.2 a
  have vsd := pairMul_valid sa.1 blockSq.2 d
  have vs1 := pairAdd_valid sd.1 one sa.2
  have vS := pairAdd_valid s1.1 s1.2 sd.2
  have vq1 := pairMul_valid s.1 j z.2.swap
  have vq2 := pairMul_valid q1.1 q1.2 s.2
  have vq := pairMul_valid q2.1 q2.2 y.2
  have hb : base.1.safe := scalarBase_safe hc ho b
  have hs : stride.1.safe := pairPow_safe hb vb (PairRef.valid_length ho (by omega)) M
  have hk : block.1.safe := pairPow_safe hs vs (PairRef.valid_length ho (by omega)) M
  have hk2 : blockSq.1.safe := pairMul_safe hk vk vk
  have hy : y.1.safe := pairHorner_safe hk2 (PairRef.valid_length vb (by
    simp only [scalarBase_length]; omega))
    (fun p hm => PairRef.valid_length (hp p hm) (by omega))
  have hz : z.1.safe := pairHorner_safe hy (PairRef.valid_length vs (by omega))
    (fun p hm => PairRef.valid_length (hp p hm) (by omega))
  have hsa : sa.1.safe := pairMul_safe hz (PairRef.valid_length vk (by omega))
    (PairRef.valid_length ha (by omega))
  have hsd : sd.1.safe := pairMul_safe hsa (PairRef.valid_length vk2 (by
    simp only [pairMul_length]; omega))
    (PairRef.valid_length hd (by omega))
  have hs1 : s1.1.safe := pairAdd_safe hsd (PairRef.valid_length ho (by omega))
    (PairRef.valid_length vsa (by simp only [pairMul_length]; omega))
  have hS : s.1.safe := pairAdd_safe hs1 vs1 (PairRef.valid_length vsd (by
    simp only [pairMul_length]; omega))
  have hq1 : q1.1.safe := pairMul_safe hS (PairRef.valid_length hj (by omega))
    (PairRef.swap_valid (PairRef.valid_length vz (by simp only [pairHorner_length]; omega)))
  have hq2 : q2.1.safe := pairMul_safe hq1 vq1 (PairRef.valid_length vS (by
    simp only [pairAdd_length]; omega))
  have hq : q.1.safe := pairMul_safe hq2 vq2 (PairRef.valid_length vy (by
    simp only [pairHorner_length]; omega))
  exact pairAdd_safe hq vq (PairRef.swap_valid vq)

def Gate.constantsAllowed (allowed : Set ℤ) : Gate → Prop
  | .scale k _ => k ∈ allowed
  | _ => True

def Circuit.constantsAllowed (allowed : Set ℤ) : Circuit → Prop
  | .empty => True
  | .snoc c g => c.constantsAllowed allowed ∧ g.constantsAllowed allowed

theorem pairAdd_constants {c : Circuit} (allowed : Set ℤ) (p q : PairRef)
    (hc : c.constantsAllowed allowed) : (pairAdd c p q).1.constantsAllowed allowed :=
  ⟨⟨hc, trivial⟩, trivial⟩
theorem pairMul_constants {c : Circuit} (allowed : Set ℤ) (p q : PairRef)
    (hc : c.constantsAllowed allowed) : (pairMul c p q).1.constantsAllowed allowed :=
  ⟨⟨hc, trivial⟩, trivial⟩
theorem pairZero_constants {c : Circuit} (allowed : Set ℤ)
    (hc : c.constantsAllowed allowed) : (pairZero c).1.constantsAllowed allowed := ⟨hc, trivial⟩

theorem pairPow_constants {c : Circuit} (allowed : Set ℤ) (base one : PairRef)
    (hc : c.constantsAllowed allowed) (n : ℕ) :
    (pairPow c base one n).1.constantsAllowed allowed := by
  induction n with
  | zero => exact hc
  | succ n ih => exact pairMul_constants allowed _ _ ih

theorem pairHorner_constants {c : Circuit} (allowed : Set ℤ) (base : PairRef)
    (hc : c.constantsAllowed allowed) (ps : List PairRef) :
    (pairHorner c base ps).1.constantsAllowed allowed := by
  induction ps with
  | nil => exact pairZero_constants allowed hc
  | cons p ps ih => exact pairAdd_constants allowed _ _ (pairMul_constants allowed _ _ ih)

/-- No scalar power is introduced as a scale-gate label. -/
theorem compress_constants {c : Circuit} (allowed : Set ℤ) (one a d j : PairRef)
    (b : ℤ) (M : ℕ) (probes : List PairRef) (hc : c.constantsAllowed allowed)
    (hb : b ∈ allowed) : (compress c one a d j b M probes).1.constantsAllowed allowed := by
  unfold compress
  apply pairAdd_constants
  apply pairMul_constants
  apply pairMul_constants
  apply pairMul_constants
  apply pairAdd_constants
  apply pairAdd_constants
  apply pairMul_constants
  apply pairMul_constants
  apply pairHorner_constants
  apply pairHorner_constants
  apply pairMul_constants
  apply pairPow_constants
  apply pairPow_constants
  exact ⟨hc, hb⟩

def addValue {R : Type*} [Ring R] (p q : R × R) : R × R :=
  (p.1 + q.1, p.2 + q.2)

def swapValue {R : Type*} (p : R × R) : R × R := (p.2, p.1)

theorem pairMul_value_later {R : Type*} [Ring R] (a d : R)
    {c t : Circuit} {p q : PairRef} (hp : p.valid c) (hq : q.valid c)
    (h : Extends (pairMul c p q).1 t) :
    (pairMul c p q).2.value t a d = mulValue (p.value t a d) (q.value t a d) := by
  rw [PairRef.value_extend (pairMul_valid _ _ _) h a d, pairMul_value a d hp hq]
  rw [PairRef.value_extend hp ((pairMul_extends c p q).trans h) a d,
    PairRef.value_extend hq ((pairMul_extends c p q).trans h) a d]
  rfl

theorem pairAdd_value_later {R : Type*} [Ring R] (a d : R)
    {c t : Circuit} {p q : PairRef} (hp : p.valid c) (hq : q.valid c)
    (h : Extends (pairAdd c p q).1 t) :
    (pairAdd c p q).2.value t a d = addValue (p.value t a d) (q.value t a d) := by
  rw [PairRef.value_extend (pairAdd_valid _ _ _) h a d, pairAdd_value a d hp hq]
  rw [PairRef.value_extend hp ((pairAdd_extends c p q).trans h) a d,
    PairRef.value_extend hq ((pairAdd_extends c p q).trans h) a d]
  rfl

theorem pairPow_value_later {R : Type*} [Ring R] (a d : R)
    {c t : Circuit} {base one : PairRef} (hb : base.valid c) (ho : one.valid c)
    (n : ℕ) (h : Extends (pairPow c base one n).1 t) :
    (pairPow c base one n).2.value t a d =
      powerValue (base.value t a d) (one.value t a d) n := by
  rw [PairRef.value_extend (pairPow_valid ho n) h a d, pairPow_value a d hb ho n]
  rw [PairRef.value_extend hb ((pairPow_extends c base one n).trans h) a d,
    PairRef.value_extend ho ((pairPow_extends c base one n).trans h) a d]

theorem map_values_extend {R : Type*} [Ring R] (a d : R) {c t : Circuit}
    (h : Extends c t) {ps : List PairRef} (hp : ∀ p ∈ ps, p.valid c) :
    ps.map (fun p => p.value t a d) = ps.map (fun p => p.value c a d) := by
  apply List.map_congr_left
  intro p hm
  exact PairRef.value_extend (hp p hm) h a d

theorem pairHorner_value_later {R : Type*} [Ring R] (a d : R)
    {c t : Circuit} {base : PairRef} (hb : base.valid c) {ps : List PairRef}
    (hp : ∀ p ∈ ps, p.valid c) (h : Extends (pairHorner c base ps).1 t) :
    (pairHorner c base ps).2.value t a d =
      hornerValue (base.value t a d) (ps.map (fun p => p.value t a d)) := by
  rw [PairRef.value_extend (pairHorner_valid _ _ _) h a d, pairHorner_value a d hb hp]
  rw [PairRef.value_extend hb ((pairHorner_extends c base ps).trans h) a d,
    map_values_extend a d ((pairHorner_extends c base ps).trans h) hp]

theorem scalarBase_value_later {R : Type*} [Ring R] (a d : R)
    {c t : Circuit} {one : PairRef} (ho : one.valid c) (b : ℤ)
    (h : Extends (scalarBase c one b).1 t) :
    (scalarBase c one b).2.value t a d =
      (b • (one.value t a d).1, b • (one.value t a d).1) := by
  rw [PairRef.value_extend (scalarBase_valid _ _ _) h a d,
    scalarBase_value a d c one b,
    PairRef.value_extend ho ((scalarBase_extends c one b).trans h) a d]

def compressionValue {R : Type*} [Ring R] (one a d j : R × R)
    (b : ℤ) (M : ℕ) (probes : List (R × R)) : R × R :=
  let base := (b • one.1, b • one.1)
  let stride := powerValue base one M
  let block := powerValue stride one M
  let blockSq := mulValue block block
  let y := hornerValue base probes
  let z := hornerValue stride probes
  let s := addValue (addValue one (mulValue block a)) (mulValue blockSq d)
  let q := mulValue (mulValue (mulValue j (swapValue z)) s) y
  addValue q (swapValue q)

theorem compress_value {R : Type*} [Ring R] (A D : R) {c : Circuit}
    {one a d j : PairRef} (b : ℤ) (M : ℕ) {probes : List PairRef}
    (ho : one.valid c) (ha : a.valid c) (hd : d.valid c) (hj : j.valid c)
    (hp : ∀ p ∈ probes, p.valid c) :
    (compress c one a d j b M probes).2.value (compress c one a d j b M probes).1 A D =
      compressionValue (one.value c A D) (a.value c A D) (d.value c A D)
        (j.value c A D) b M (probes.map (fun p => p.value c A D)) := by
  let base := scalarBase c one b
  let stride := pairPow base.1 base.2 one M
  let block := pairPow stride.1 stride.2 one M
  let blockSq := pairMul block.1 block.2 block.2
  let y := pairHorner blockSq.1 base.2 probes
  let z := pairHorner y.1 stride.2 probes
  let sa := pairMul z.1 block.2 a
  let sd := pairMul sa.1 blockSq.2 d
  let s1 := pairAdd sd.1 one sa.2
  let s := pairAdd s1.1 s1.2 sd.2
  let q1 := pairMul s.1 j z.2.swap
  let q2 := pairMul q1.1 q1.2 s.2
  let q := pairMul q2.1 q2.2 y.2
  let f := pairAdd q.1 q.2 q.2.swap
  have lb : base.1.length = c.length + 1 := scalarBase_length _ _ _
  have ls : stride.1.length = base.1.length + 2 * M := pairPow_length _ _ _ _
  have lk : block.1.length = stride.1.length + 2 * M := pairPow_length _ _ _ _
  have lk2 : blockSq.1.length = block.1.length + 2 := pairMul_length _ _ _
  have ly : y.1.length = blockSq.1.length + 4 * probes.length + 1 := pairHorner_length _ _ _
  have lz : z.1.length = y.1.length + 4 * probes.length + 1 := pairHorner_length _ _ _
  have lsa : sa.1.length = z.1.length + 2 := pairMul_length _ _ _
  have lsd : sd.1.length = sa.1.length + 2 := pairMul_length _ _ _
  have ls1 : s1.1.length = sd.1.length + 2 := pairAdd_length _ _ _
  have lS : s.1.length = s1.1.length + 2 := pairAdd_length _ _ _
  have lq1 : q1.1.length = s.1.length + 2 := pairMul_length _ _ _
  have lq2 : q2.1.length = q1.1.length + 2 := pairMul_length _ _ _
  have vb : base.2.valid base.1 := scalarBase_valid c one b
  have vs : stride.2.valid stride.1 := pairPow_valid
    (PairRef.valid_length ho (by omega)) M
  have vk : block.2.valid block.1 := pairPow_valid
    (PairRef.valid_length ho (by omega)) M
  have vk2 : blockSq.2.valid blockSq.1 := pairMul_valid _ _ _
  have vy : y.2.valid y.1 := pairHorner_valid _ _ _
  have vz : z.2.valid z.1 := pairHorner_valid _ _ _
  have vsa : sa.2.valid sa.1 := pairMul_valid _ _ _
  have vsd : sd.2.valid sd.1 := pairMul_valid _ _ _
  have vs1 : s1.2.valid s1.1 := pairAdd_valid _ _ _
  have vS : s.2.valid s.1 := pairAdd_valid _ _ _
  have vq1 : q1.2.valid q1.1 := pairMul_valid _ _ _
  have vq2 : q2.2.valid q2.1 := pairMul_valid _ _ _
  have vq : q.2.valid q.1 := pairMul_valid _ _ _
  have eqf : Extends q.1 f.1 := pairAdd_extends _ _ _
  have eq2 : Extends q2.1 f.1 := (pairMul_extends q2.1 q2.2 y.2).trans eqf
  have eq1 : Extends q1.1 f.1 := (pairMul_extends q1.1 q1.2 s.2).trans eq2
  have eS : Extends s.1 f.1 := (pairMul_extends s.1 j z.2.swap).trans eq1
  have es1 : Extends s1.1 f.1 := (pairAdd_extends s1.1 s1.2 sd.2).trans eS
  have esd : Extends sd.1 f.1 := (pairAdd_extends sd.1 one sa.2).trans es1
  have esa : Extends sa.1 f.1 := (pairMul_extends sa.1 blockSq.2 d).trans esd
  have ez : Extends z.1 f.1 := (pairMul_extends z.1 block.2 a).trans esa
  have ey : Extends y.1 f.1 := (pairHorner_extends y.1 stride.2 probes).trans ez
  have ek2 : Extends blockSq.1 f.1 := (pairHorner_extends blockSq.1 base.2 probes).trans ey
  have ek : Extends block.1 f.1 := (pairMul_extends block.1 block.2 block.2).trans ek2
  have estride : Extends stride.1 f.1 := (pairPow_extends stride.1 stride.2 one M).trans ek
  have ebase : Extends base.1 f.1 := (pairPow_extends base.1 base.2 one M).trans estride
  have ec : Extends c f.1 := (scalarBase_extends c one b).trans ebase
  have vone := PairRef.value_extend ho ec A D
  have va := PairRef.value_extend ha ec A D
  have vd := PairRef.value_extend hd ec A D
  have vj := PairRef.value_extend hj ec A D
  have vp := map_values_extend A D ec hp
  have valueBase := scalarBase_value_later A D ho b ebase
  rw [vone] at valueBase
  have valueStride := pairPow_value_later A D vb (PairRef.valid_length ho (by omega))
    M estride
  rw [valueBase, vone] at valueStride
  have valueBlock := pairPow_value_later A D vs (PairRef.valid_length ho (by omega)) M ek
  rw [valueStride, vone] at valueBlock
  have valueBlockSq := pairMul_value_later A D vk vk ek2
  rw [valueBlock] at valueBlockSq
  have valueY := pairHorner_value_later A D (PairRef.valid_length vb (by omega))
    (fun p hm => PairRef.valid_length (hp p hm) (by omega)) ey
  rw [valueBase, vp] at valueY
  have valueZ := pairHorner_value_later A D (PairRef.valid_length vs (by omega))
    (fun p hm => PairRef.valid_length (hp p hm) (by omega)) ez
  rw [valueStride, vp] at valueZ
  have valueSA := pairMul_value_later A D (PairRef.valid_length vk (by omega))
    (PairRef.valid_length ha (by omega)) esa
  rw [valueBlock, va] at valueSA
  have valueSD := pairMul_value_later A D (PairRef.valid_length vk2 (by omega))
    (PairRef.valid_length hd (by omega)) esd
  rw [valueBlockSq, vd] at valueSD
  have valueS1 := pairAdd_value_later A D (PairRef.valid_length ho (by omega))
    (PairRef.valid_length vsa (by omega)) es1
  rw [vone, valueSA] at valueS1
  have valueS := pairAdd_value_later A D vs1 (PairRef.valid_length vsd (by omega)) eS
  rw [valueS1, valueSD] at valueS
  have valueQ1 := pairMul_value_later A D (PairRef.valid_length hj (by omega))
    (PairRef.swap_valid (PairRef.valid_length vz (by omega))) eq1
  rw [vj, PairRef.swap_value, valueZ] at valueQ1
  have valueQ2 := pairMul_value_later A D vq1 (PairRef.valid_length vS (by omega)) eq2
  rw [valueQ1, valueS] at valueQ2
  have valueQ := pairMul_value_later A D vq2 (PairRef.valid_length vy (by omega)) eqf
  rw [valueQ2, valueY] at valueQ
  have valueF := pairAdd_value_later A D vq (PairRef.swap_valid vq) (Extends.refl f.1)
  rw [PairRef.swap_value, valueQ] at valueF
  exact valueF

end CircuitAudit.CircuitCosts
