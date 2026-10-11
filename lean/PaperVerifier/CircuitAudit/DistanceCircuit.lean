import PaperVerifier.CircuitAudit.ProbeCircuit
import PaperVerifier.CircuitAudit.Degrees

/-! A shared implementation of the literal McKay distance recurrence and
its partial sums. No matrix all-ones input is supplied to this circuit. -/
namespace CircuitAudit.DistanceCircuit

open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit

structure State where
  circuit : Circuit
  previous : PairRef
  current : PairRef
  total : PairRef
  dm : PairRef
  firstSum : PairRef

def Ready (s : State) : Prop :=
  oneRef.valid s.circuit ∧ aRef.valid s.circuit ∧ dRef.valid s.circuit ∧
  zeroRef.valid s.circuit ∧ s.previous.valid s.circuit ∧
  s.current.valid s.circuit ∧ s.total.valid s.circuit ∧
  s.dm.valid s.circuit ∧ s.firstSum.valid s.circuit

def seed (c : Circuit) : State :=
  let aa := pairMul c aRef aRef
  let nd := pairScale aa.1 (-1) dRef
  let p2 := pairAdd nd.1 aa.2 nd.2
  let s1 := pairAdd p2.1 oneRef aRef
  let s2 := pairAdd s1.1 s1.2 p2.2
  let ni := pairScale s2.1 (-1) oneRef
  let dm := pairAdd ni.1 dRef ni.2
  ⟨dm.1, aRef, p2.2, s2.2, dm.2, s1.2⟩

@[simp] theorem seed_length (c : Circuit) : (seed c).circuit.length = c.length + 14 := by
  simp only [seed, pairMul_length, pairScale_length, pairAdd_length]

theorem seed_extends (c : Circuit) : Extends c (seed c).circuit := by
  unfold seed
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairScale_extends _ _ _)
  apply Extends.trans (pairAdd_extends _ _ _)
  apply Extends.trans (pairAdd_extends _ _ _)
  apply Extends.trans (pairAdd_extends _ _ _)
  apply Extends.trans (pairScale_extends _ _ _)
  exact pairAdd_extends _ _ _

theorem seed_ready {c : Circuit} (h : ProbeCircuit.Ready c []) : Ready (seed c) := by
  let aa := pairMul c aRef aRef
  let nd := pairScale aa.1 (-1) dRef
  let p2 := pairAdd nd.1 aa.2 nd.2
  let s1 := pairAdd p2.1 oneRef aRef
  let s2 := pairAdd s1.1 s1.2 p2.2
  let ni := pairScale s2.1 (-1) oneRef
  have e := seed_extends c
  have haa := pairMul_valid c aRef aRef
  have hnd := pairScale_valid aa.1 (-1) dRef
  have hp2 := pairAdd_valid nd.1 aa.2 nd.2
  have hs1 := pairAdd_valid p2.1 oneRef aRef
  have hs2 := pairAdd_valid s1.1 s1.2 p2.2
  have l1 : s1.1.length = c.length + 8 := by simp [s1, p2, nd, aa]
  have l2 : p2.1.length = c.length + 6 := by simp [p2, nd, aa]
  have l3 : s2.1.length = c.length + 10 := by simp [s2, s1, p2, nd, aa]
  refine ⟨PairRef.valid_extend h.1 e, PairRef.valid_extend h.2.1 e,
    PairRef.valid_extend h.2.2.1 e, PairRef.valid_extend h.2.2.2.1 e,
    PairRef.valid_extend h.2.1 e, ?_, ?_, pairAdd_valid _ _ _, ?_⟩
  · exact PairRef.valid_length hp2 (by rw [l2, seed_length]; omega)
  · exact PairRef.valid_length hs2 (by rw [l3, seed_length]; omega)
  · exact PairRef.valid_length hs1 (by rw [l1, seed_length]; omega)

theorem seed_safe {c : Circuit} (hc : c.safe) (h : ProbeCircuit.Ready c []) :
    (seed c).circuit.safe := by
  let aa := pairMul c aRef aRef
  let nd := pairScale aa.1 (-1) dRef
  let p2 := pairAdd nd.1 aa.2 nd.2
  let s1 := pairAdd p2.1 oneRef aRef
  let s2 := pairAdd s1.1 s1.2 p2.2
  let ni := pairScale s2.1 (-1) oneRef
  have eaa : Extends c aa.1 := pairMul_extends _ _ _
  have endRef : Extends c nd.1 := eaa.trans (pairScale_extends _ _ _)
  have ep2 : Extends c p2.1 := endRef.trans (pairAdd_extends _ _ _)
  have es1 : Extends c s1.1 := ep2.trans (pairAdd_extends _ _ _)
  have es2 : Extends c s2.1 := es1.trans (pairAdd_extends _ _ _)
  have eni : Extends c ni.1 := es2.trans (pairScale_extends _ _ _)
  have haa : aa.1.safe := pairMul_safe hc h.2.1 h.2.1
  have hnd : nd.1.safe := pairScale_safe haa (PairRef.valid_extend h.2.2.1 eaa) _
  have hp2 : p2.1.safe := pairAdd_safe hnd
    (PairRef.valid_extend (pairMul_valid _ _ _) (pairScale_extends _ _ _))
    (pairScale_valid _ _ _)
  have hs1 : s1.1.safe := pairAdd_safe hp2 (PairRef.valid_extend h.1 ep2)
    (PairRef.valid_extend h.2.1 ep2)
  have hs2 : s2.1.safe := pairAdd_safe hs1 (pairAdd_valid _ _ _)
    (PairRef.valid_extend (pairAdd_valid _ _ _) (pairAdd_extends _ _ _))
  have hni : ni.1.safe := pairScale_safe hs2 (PairRef.valid_extend h.1 es2) _
  exact pairAdd_safe hni (PairRef.valid_extend h.2.2.1 eni) (pairScale_valid _ _ _)

def step (s : State) : State :=
  let ac := pairMul s.circuit aRef s.current
  let dp := pairMul ac.1 s.dm s.previous
  let nd := pairScale dp.1 (-1) dp.2
  let nx := pairAdd nd.1 ac.2 nd.2
  let su := pairAdd nx.1 s.total nx.2
  ⟨su.1, s.current, nx.2, su.2, s.dm, s.firstSum⟩

@[simp] theorem step_length (s : State) : (step s).circuit.length = s.circuit.length + 10 := by
  simp only [step, pairMul_length, pairScale_length, pairAdd_length]

theorem step_extends (s : State) : Extends s.circuit (step s).circuit := by
  unfold step
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairMul_extends _ _ _)
  apply Extends.trans (pairScale_extends _ _ _)
  apply Extends.trans (pairAdd_extends _ _ _)
  exact pairAdd_extends _ _ _

theorem step_ready {s : State} (h : Ready s) : Ready (step s) := by
  let ac := pairMul s.circuit aRef s.current
  let dp := pairMul ac.1 s.dm s.previous
  let nd := pairScale dp.1 (-1) dp.2
  let nx := pairAdd nd.1 ac.2 nd.2
  have e := step_extends s
  refine ⟨PairRef.valid_extend h.1 e, PairRef.valid_extend h.2.1 e,
    PairRef.valid_extend h.2.2.1 e, PairRef.valid_extend h.2.2.2.1 e,
    PairRef.valid_extend h.2.2.2.2.2.1 e,
    ?_, pairAdd_valid _ _ _, PairRef.valid_extend h.2.2.2.2.2.2.2.1 e,
    PairRef.valid_extend h.2.2.2.2.2.2.2.2 e⟩
  exact PairRef.valid_extend (pairAdd_valid _ _ _) (pairAdd_extends nx.1 s.total nx.2)

theorem step_safe {s : State} (hc : s.circuit.safe) (h : Ready s) :
    (step s).circuit.safe := by
  let ac := pairMul s.circuit aRef s.current
  let dp := pairMul ac.1 s.dm s.previous
  let nd := pairScale dp.1 (-1) dp.2
  let nx := pairAdd nd.1 ac.2 nd.2
  have eac : Extends s.circuit ac.1 := pairMul_extends _ _ _
  have edp : Extends s.circuit dp.1 := eac.trans (pairMul_extends _ _ _)
  have endRef : Extends s.circuit nd.1 := edp.trans (pairScale_extends _ _ _)
  have enx : Extends s.circuit nx.1 := endRef.trans (pairAdd_extends _ _ _)
  have hac : ac.1.safe := pairMul_safe hc h.2.1 h.2.2.2.2.2.1
  have hdp : dp.1.safe := pairMul_safe hac
    (PairRef.valid_extend h.2.2.2.2.2.2.2.1 eac)
    (PairRef.valid_extend h.2.2.2.2.1 eac)
  have hnd : nd.1.safe := pairScale_safe hdp (pairMul_valid _ _ _) _
  have hnx : nx.1.safe := pairAdd_safe hnd
    (PairRef.valid_extend (pairMul_valid _ _ _)
      ((pairMul_extends _ _ _).trans (pairScale_extends _ _ _)))
    (pairScale_valid _ _ _)
  exact pairAdd_safe hnx (PairRef.valid_extend h.2.2.2.2.2.2.1 enx) (pairAdd_valid _ _ _)

def iterate : ℕ → State → State
  | 0, s => s
  | n+1, s => iterate n (step s)

theorem iterate_extends (n : ℕ) (s : State) :
    Extends s.circuit (iterate n s).circuit := by
  induction n generalizing s with
  | zero => exact .refl _
  | succ n ih => exact (step_extends s).trans (ih (step s))

theorem iterate_ready (n : ℕ) {s : State} (h : Ready s) : Ready (iterate n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih (step_ready h)

theorem iterate_safe (n : ℕ) {s : State} (hc : s.circuit.safe) (h : Ready s) :
    (iterate n s).circuit.safe := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (step_safe hc h) (step_ready h)

theorem iterate_length (n : ℕ) (s : State) :
    (iterate n s).circuit.length = s.circuit.length + 10*n := by
  induction n generalizing s with
  | zero => simp [iterate]
  | succ n ih => simp only [iterate, ih, step_length]; omega

def build (N : ℕ) (c : Circuit) : Result :=
  let s := iterate (N-3) (seed c)
  (s.circuit, if N = 0 then zeroRef else if N = 1 then oneRef
    else if N = 2 then s.firstSum else s.total)

theorem build_extends (N : ℕ) (c : Circuit) : Extends c (build N c).1 :=
  (seed_extends c).trans (iterate_extends _ _)

theorem build_length (N : ℕ) (c : Circuit) :
    (build N c).1.length = c.length + 14 + 10*(N-3) := by
  simp [build, iterate_length]

theorem build_safe (N : ℕ) {c : Circuit} (hc : c.safe)
    (h : ProbeCircuit.Ready c []) : (build N c).1.safe :=
  iterate_safe _ (seed_safe hc h) (seed_ready h)

theorem build_valid (N : ℕ) {c : Circuit} (h : ProbeCircuit.Ready c []) :
    (build N c).2.valid (build N c).1 := by
  have hs := iterate_ready (N-3) (seed_ready h)
  unfold build
  split
  · exact hs.2.2.2.1
  · split
    · exact hs.1
    · split
      · exact hs.2.2.2.2.2.2.2.2
      · exact hs.2.2.2.2.2.2.1

theorem pairScale_constants {c : Circuit} (allowed : Set ℤ) (p : PairRef) (k : ℤ)
    (hc : c.constantsAllowed allowed) (hk : k ∈ allowed) :
    (pairScale c k p).1.constantsAllowed allowed := ⟨⟨hc, hk⟩, hk⟩

theorem seed_constants {c : Circuit} (allowed : Set ℤ)
    (hc : c.constantsAllowed allowed) (hn : (-1 : ℤ) ∈ allowed) :
    (seed c).circuit.constantsAllowed allowed := by
  unfold seed
  apply pairAdd_constants
  apply pairScale_constants _ _ _ _ hn
  apply pairAdd_constants
  apply pairAdd_constants
  apply pairAdd_constants
  apply pairScale_constants _ _ _ _ hn
  exact pairMul_constants _ _ _ hc

theorem step_constants {s : State} (allowed : Set ℤ)
    (hc : s.circuit.constantsAllowed allowed) (hn : (-1 : ℤ) ∈ allowed) :
    (step s).circuit.constantsAllowed allowed := by
  unfold step
  apply pairAdd_constants
  apply pairAdd_constants
  apply pairScale_constants _ _ _ _ hn
  apply pairMul_constants
  exact pairMul_constants _ _ _ hc

theorem iterate_constants (n : ℕ) {s : State} (allowed : Set ℤ)
    (hc : s.circuit.constantsAllowed allowed) (hn : (-1 : ℤ) ∈ allowed) :
    (iterate n s).circuit.constantsAllowed allowed := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (step_constants allowed hc hn)

theorem build_constants (N : ℕ) {c : Circuit} (allowed : Set ℤ)
    (hc : c.constantsAllowed allowed) (hn : (-1 : ℤ) ∈ allowed) :
    (build N c).1.constantsAllowed allowed :=
  iterate_constants _ allowed (seed_constants allowed hc hn) hn

#print axioms build_safe
#print axioms build_length

end CircuitAudit.DistanceCircuit
