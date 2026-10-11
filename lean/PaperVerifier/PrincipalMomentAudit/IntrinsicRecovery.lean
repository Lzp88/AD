import PaperVerifier.PrincipalMomentAudit.SelectorEvaluation
import PaperVerifier.PrincipalMomentAudit.Quotient
import PaperVerifier.PrincipalMomentAudit.OrbitQuotient

/-!
# Shared literal coordinate recovery

The expression family in this file depends only on the common vertex bound.
It starts with the actual typed terminal seeds and applies the same reverse
support polynomial for every old type and every previously recovered parent.
Empty labels are retained and evaluate to zero.
-/

namespace PrincipalMomentAudit.IntrinsicRecovery

open Matrix Finset PrincipalMomentAudit.Transport PrincipalMomentAudit.SelectorEvaluation

noncomputable section

/-- On the integer spectrum 0..N, one minus the zero-level selector is the
same positive-support extractor as the sum of the positive levels. -/
def positiveExpression (N : ℕ) (p : Expression) : Expression :=
  Expression.one.sub (levelSelector N 0 p)

def terminalSeeds (N : ℕ) : List Expression :=
  (Finset.univ.toList.map (fun r : StageType N N =>
    (literalState N N).centerVertexType N r)) ++
  (Finset.univ.toList.map (fun rq : StageType N N × StageType N N =>
    (literalState N N).centerEdgeType N rq.1 rq.2))

def reverseSeeds (N t : ℕ) (parents : List Expression) : List Expression :=
  Finset.univ.toList.flatMap (fun r : StageType N t => parents.map (fun p =>
    positiveExpression N ((literalState N t).reverseQuotient N r p)))

def recoverySteps (N : ℕ) : ℕ → List Expression
  | 0 => terminalSeeds N
  | k + 1 => recoverySteps N k ++ reverseSeeds N (N - (k + 1)) (recoverySteps N k)

/-- This finite list is literally identical for every pair with the same N. -/
def recoveryFamily (N : ℕ) : List Expression := recoverySteps N N

theorem terminal_vertex_mem (N : ℕ) (r : StageType N N) :
    (literalState N N).centerVertexType N r ∈ terminalSeeds N := by
  classical
  simp [terminalSeeds]

theorem terminal_edge_mem (N : ℕ) (r q : StageType N N) :
    (literalState N N).centerEdgeType N r q ∈ terminalSeeds N := by
  classical
  simp [terminalSeeds]

theorem reverse_seed_mem (N t : ℕ) (parents : List Expression)
    (r : StageType N t) (p : Expression) (hp : p ∈ parents) :
    positiveExpression N ((literalState N t).reverseQuotient N r p) ∈ reverseSeeds N t parents := by
  classical
  simp only [reverseSeeds, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.mem_map]
  exact ⟨r, p, hp, rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveExpression_zero (A D : Matrix ι ι ℝ) (p : Expression) (N : ℕ)
    (hp : matrixEval A D p = 0) : matrixEval A D (positiveExpression N p) = 0 := by
  have hz : matrixEval A D p = Matrix.diagonal (fun _ => ((0 : ℕ) : ℝ)) := by simpa using hp
  rw [positiveExpression, matrixEval_sub, levelSelector_matrixEval_integer A D p _ hz N 0
    (fun _ => Nat.zero_le N)]
  ext i j
  by_cases hij : i = j <;> simp [Expression.one, matrixEval, PrincipalMomentAudit.vertexSelector, hij]

theorem positiveExpression_coordinate (A D : Matrix ι ι ℝ) (p : Expression)
    (N j : ℕ) (c : ι) (hp : matrixEval A D p = (j : ℝ) • PrincipalMomentAudit.Quotient.coordinate c)
    (hj : j ≤ N) (hjpos : 0 < j) :
    matrixEval A D (positiveExpression N p) = PrincipalMomentAudit.Quotient.coordinate c := by
  let d : ι → ℕ := fun i => if i = c then j else 0
  have hd : matrixEval A D p = Matrix.diagonal (fun i => (d i : ℝ)) := by
    rw [hp]
    ext i l
    by_cases hil : i = l
    · subst l
      by_cases hic : i = c <;> simp [PrincipalMomentAudit.Quotient.coordinate, d, hic]
    · simp [PrincipalMomentAudit.Quotient.coordinate, d, hil]
  rw [positiveExpression, matrixEval_sub, levelSelector_matrixEval_integer A D p d hd N 0
    (fun i => by dsimp [d]; split_ifs <;> omega)]
  ext i l
  by_cases hil : i = l
  · subst l
    by_cases hic : i = c <;>
      simp [Expression.one, matrixEval, PrincipalMomentAudit.vertexSelector, PrincipalMomentAudit.Quotient.coordinate,
        d, hic, Nat.ne_of_gt hjpos]
  · simp [Expression.one, matrixEval, PrincipalMomentAudit.vertexSelector, PrincipalMomentAudit.Quotient.coordinate, hil]

omit [Fintype ι] in
theorem coordinate_ne_zero (i : ι) : PrincipalMomentAudit.Quotient.coordinate i ≠ 0 := by
  intro h
  have hi := congrArg (fun M : Matrix ι ι ℝ => M i i) h
  simp [PrincipalMomentAudit.Quotient.coordinate] at hi

/-- One literal reverse expression recovers a child from actual integer
counts. Parent support, the reverse column support, positivity and the
integer spectral value are all consequences of these count identities. -/
theorem reverseExpression_coordinate {ρ : Type*} [Fintype ρ]
    (A D : Matrix ι ι ℝ) (s : PruningState ρ) (N : ℕ) (r : ρ) (ep : Expression)
    (b : Matrix ι ι ℕ) (S : Finset ι) (parent : ι → ι) (sizes : ι → ℝ) (p c : ι)
    (hB : matrixEval A D s.adjacency = fun i j => (b i j : ℝ))
    (hX : matrixEval A D (s.peeledType N r) = PrincipalMomentAudit.Quotient.selectedDiagonal S)
    (hEp : matrixEval A D ep = PrincipalMomentAudit.Quotient.coordinate p)
    (hdegree : ∀ a ∈ S, ∑ q, b a q = 1)
    (hparent : ∀ a ∈ S, 0 < b a (parent a))
    (hsizes : ∀ a, 0 < sizes a)
    (hbalance : ∀ a q, sizes a * (b a q : ℝ) = sizes q * (b q a : ℝ))
    (hunique : ∀ a ∈ S, ∀ d ∈ S, parent a = parent d → a = d)
    (hc : c ∈ S) (hcp : parent c = p) (hbound : b p c ≤ N) :
    matrixEval A D (positiveExpression N (s.reverseQuotient N r ep)) =
      PrincipalMomentAudit.Quotient.coordinate c := by
  let B : Matrix ι ι ℝ := fun i j => (b i j : ℝ)
  have hrow : ∀ a ∈ S, ∀ q, q ≠ parent a → B a q = 0 := by
    intro a ha q hq
    have hz := (PrincipalMomentAudit.Quotient.degree_one_parent_count b a (parent a)
      (hdegree a ha) (hparent a ha)).2 q hq
    simp [B, hz]
  have hundirected : ∀ a q, B a q = 0 → B q a = 0 :=
    PrincipalMomentAudit.Quotient.undirected_support_of_balance B sizes hsizes hbalance
  have hcol := PrincipalMomentAudit.Quotient.column_parent_support_of_undirected B S parent hrow hundirected
  have hcpone : b c p = 1 := by
    rw [← hcp]
    exact (PrincipalMomentAudit.Quotient.degree_one_parent_count b c (parent c)
      (hdegree c hc) (hparent c hc)).1
  have hpcpos : 0 < b p c := by
    by_contra hn
    have hz : b p c = 0 := by omega
    have hcz := hundirected p c (by simp [B, hz])
    simp [B, hcpone] at hcz
  have heval : matrixEval A D (s.reverseQuotient N r ep) =
      (b p c : ℝ) • PrincipalMomentAudit.Quotient.coordinate c := by
    simp only [PruningState.reverseQuotient, matrixEval, hX, hB, hEp]
    change PrincipalMomentAudit.Quotient.reverseProduct B S p = _
    rw [PrincipalMomentAudit.Quotient.reverseProduct_eq_coordinate B S parent p c hrow hcol hunique hc hcp]
    simp [B, hcpone]
  exact positiveExpression_coordinate A D _ N (b p c) c heval hbound hpcpos

theorem reverseExpression_empty {ρ : Type*} [Fintype ρ]
    (A D : Matrix ι ι ℝ) (s : PruningState ρ) (N : ℕ) (r : ρ) (ep : Expression)
    (B : Matrix ι ι ℝ) (S : Finset ι) (parent : ι → ι) (p : ι)
    (hB : matrixEval A D s.adjacency = B)
    (hX : matrixEval A D (s.peeledType N r) = PrincipalMomentAudit.Quotient.selectedDiagonal S)
    (hEp : matrixEval A D ep = PrincipalMomentAudit.Quotient.coordinate p)
    (hrow : ∀ a ∈ S, ∀ q, q ≠ parent a → B a q = 0)
    (hcol : ∀ a ∈ S, ∀ q, q ≠ parent a → B q a = 0)
    (hempty : ∀ a ∈ S, parent a ≠ p) :
    matrixEval A D (positiveExpression N (s.reverseQuotient N r ep)) = 0 := by
  apply positiveExpression_zero
  simp only [PruningState.reverseQuotient, matrixEval, hX, hB, hEp]
  exact PrincipalMomentAudit.Quotient.reverseProduct_empty B S parent p hrow hcol hempty

#print axioms positiveExpression_coordinate
#print axioms reverseExpression_coordinate

end

end PrincipalMomentAudit.IntrinsicRecovery
