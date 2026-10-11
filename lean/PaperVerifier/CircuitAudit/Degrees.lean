import Mathlib

/-! Literal integer AD syntax and formal-degree preservation for radix factoring.
Gate counts belong to CircuitCosts: these syntax trees are not a shared DAG. -/
namespace CircuitAudit.Degrees

inductive Expr where
  | zero | one | a | d
  | scale (c : ℤ) (p : Expr)
  | add (p q : Expr)
  | mul (p q : Expr)
  deriving Repr

def Expr.eval {R : Type*} [Ring R] (a d : R) : Expr → R
  | .zero => 0
  | .one => 1
  | .a => a
  | .d => d
  | .scale c p => c • p.eval a d
  | .add p q => p.eval a d + q.eval a d
  | .mul p q => p.eval a d * q.eval a d

def Expr.degree : Expr → ℕ
  | .zero | .one => 0
  | .a | .d => 1
  | .scale _ p => p.degree
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree

def Expr.reverse : Expr → Expr
  | .zero => .zero
  | .one => .one
  | .a => .a
  | .d => .d
  | .scale c p => .scale c p.reverse
  | .add p q => .add p.reverse q.reverse
  | .mul p q => .mul q.reverse p.reverse

@[simp] theorem reverse_degree (p : Expr) : p.reverse.degree = p.degree := by
  induction p <;> simp_all [Expr.reverse, Expr.degree, Nat.add_comm]

theorem reverse_eval {R : Type*} [Ring R] [StarRing R] (a d : R)
    (ha : star a = a) (hd : star d = d) (p : Expr) :
    p.reverse.eval a d = star (p.eval a d) := by
  induction p <;> simp_all [Expr.reverse, Expr.eval]
  exact Int.cast_commute _ _

/-- The written triangular recurrence; out-of-range factors are literal zero. -/
def probe (N : ℕ) : ℕ → ℕ → Expr
  | 0, j => if j = 0 then .one else .zero
  | k + 1, j =>
      .add
        (if j ≤ k then
          .mul (.add .d (.scale ((N : ℤ)^2 * ((j : ℤ) - k)) .one)) (probe N k j)
         else .zero)
        (if 0 < j then .scale ((N : ℤ)^2) (.mul .a (probe N k (j - 1)))
         else .zero)

theorem probe_degree (N k j : ℕ) : (probe N k j).degree ≤ k := by
  induction k generalizing j with
  | zero => simp [probe]; split <;> simp [Expr.degree]
  | succ k ih =>
      simp only [probe, Expr.degree]
      apply max_le
      · split
        · simp only [Expr.degree]; have := ih j; omega
        · simp [Expr.degree]
      · split
        · simp only [Expr.degree]; have := ih (j - 1); omega
        · simp [Expr.degree]

def row (N k : ℕ) : List Expr := List.ofFn (fun j : Fin (k + 1) => probe N k j)

def probeList (N : ℕ) : ℕ → List Expr
  | 0 => []
  | k + 1 => probeList N k ++ row N k

@[simp] theorem row_length (N k : ℕ) : (row N k).length = k + 1 := by
  simp [row]

theorem probeList_twice_length (N k : ℕ) :
    2 * (probeList N k).length = k * (k + 1) := by
  induction k with
  | zero => simp [probeList]
  | succ k ih => simp only [probeList, List.length_append, row_length]; nlinarith

theorem probeList_length (N : ℕ) :
    (probeList N N).length = N * (N + 1) / 2 := by
  have := probeList_twice_length N N
  omega

theorem probeList_degree (N k : ℕ) (p : Expr) (hp : p ∈ probeList N k) :
    p.degree ≤ k - 1 := by
  induction k with
  | zero => simp [probeList] at hp
  | succ k ih =>
      simp only [probeList, List.mem_append] at hp
      rcases hp with hp | hp
      · have h := ih hp; omega
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
        simpa using probe_degree N k j

def power (base : Expr) : ℕ → Expr
  | 0 => .one
  | n + 1 => .mul base (power base n)

theorem power_eval {R : Type*} [Ring R] (a d : R) (base : Expr) (n : ℕ) :
    (power base n).eval a d = (base.eval a d)^n := by
  induction n with
  | zero => simp [power, Expr.eval]
  | succ n ih => simp [power, Expr.eval, ih, pow_succ']

theorem power_degree_zero (base : Expr) (h : base.degree = 0) (n : ℕ) :
    (power base n).degree = 0 := by
  induction n <;> simp_all [power, Expr.degree]

def horner (base : Expr) : List Expr → Expr
  | [] => .zero
  | p :: ps => .add p (.mul base (horner base ps))

theorem horner_degree (base : Expr) (hb : base.degree = 0) (ps : List Expr)
    (k : ℕ) (hp : ∀ p ∈ ps, p.degree ≤ k) : (horner base ps).degree ≤ k := by
  induction ps with
  | nil => simp [horner, Expr.degree]
  | cons p ps ih =>
      have htail : ∀ q ∈ ps, q.degree ≤ k := fun q hq => hp q (by simp [hq])
      simp only [horner, Expr.degree, hb, zero_add]
      exact max_le (hp p (by simp)) (ih htail)

def factored (b : ℤ) (J : Expr) (ps : List Expr) : Expr :=
  let base := Expr.scale b .one
  let beta := power base ps.length
  let gamma := power beta ps.length
  let Y := horner base ps
  let Z := horner beta ps
  let S := Expr.add (Expr.add .one (.mul gamma .a)) (.mul (.mul gamma gamma) .d)
  let q := Expr.mul (Expr.mul (Expr.mul J Z.reverse) S) Y
  .add q q.reverse

theorem factored_degree (b : ℤ) (J : Expr) (ps : List Expr) (k : ℕ)
    (hJ : J.degree ≤ k) (hp : ∀ p ∈ ps, p.degree ≤ k) :
    (factored b J ps).degree ≤ 3 * k + 1 := by
  have hbase : (Expr.scale b .one).degree = 0 := rfl
  have hbeta := power_degree_zero _ hbase ps.length
  have hgamma := power_degree_zero _ hbeta ps.length
  have hY := horner_degree _ hbase ps k hp
  have hZ := horner_degree _ hbeta ps k hp
  simp only [factored, Expr.degree, reverse_degree, hgamma, zero_add, add_zero,
    Nat.max_self, Nat.max_eq_right (by omega : (0 : ℕ) ≤ 1)]
  omega

theorem factored_probe_degree (N : ℕ) (hN : 1 ≤ N) (b : ℤ) (J : Expr)
    (hJ : J.degree ≤ N - 1) :
    (factored b J (probeList N N)).degree ≤ 3 * N - 2 := by
  have h := factored_degree b J (probeList N N) (N - 1) hJ
    (fun p hp => probeList_degree N N p hp)
  omega

/-- The literal McKay distance-polynomial recurrence used in the manuscript. -/
def distance (n : ℕ) : Expr :=
  match n with
  | 0 => .one
  | 1 => .a
  | 2 => .add (.mul .a .a) (.scale (-1) .d)
  | k + 3 => .add (.mul .a (distance (k + 2)))
      (.scale (-1) (.mul (.add .d (.scale (-1) .one)) (distance (k + 1))))
termination_by n
decreasing_by all_goals omega

theorem distance_degree (n : ℕ) : (distance n).degree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [distance, Expr.degree]
      | succ n =>
          cases n with
          | zero => simp [distance, Expr.degree]
          | succ n =>
              cases n with
              | zero => simp [distance, Expr.degree]
              | succ n =>
                  have h1 := ih (n + 2) (by omega)
                  have h2 := ih (n + 1) (by omega)
                  simp only [distance, Expr.degree]
                  omega

def expressionSum : List Expr → Expr
  | [] => .zero
  | p :: ps => .add p (expressionSum ps)

theorem expressionSum_degree (ps : List Expr) (k : ℕ)
    (hp : ∀ p ∈ ps, p.degree ≤ k) : (expressionSum ps).degree ≤ k := by
  induction ps with
  | nil => simp [expressionSum, Expr.degree]
  | cons p ps ih =>
      apply max_le
      · exact hp p (by simp)
      · exact ih (fun q hq => hp q (by simp [hq]))

def allOnes (N : ℕ) : Expr := expressionSum ((List.range N).map distance)

theorem allOnes_degree (N : ℕ) : (allOnes N).degree ≤ N - 1 := by
  apply expressionSum_degree
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  have hk' : k < N := List.mem_range.mp hk
  have := distance_degree k
  omega

theorem literal_packed_degree (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    (factored b (allOnes N) (probeList N N)).degree ≤ 3 * N - 2 :=
  factored_probe_degree N hN b (allOnes N) (allOnes_degree N)

#print axioms factored_probe_degree
#print axioms literal_packed_degree

end CircuitAudit.Degrees
