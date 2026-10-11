import PaperVerifier.PrincipalMomentAudit.Transport

/-!
Literal, shared expressions for the guarded pruning in the public source
arXiv:2607.21494v1, lines 490--625, and reverse quotient extraction in
lines 770--800. Types are shared recursive labels, not graph-chosen vectors.
This file proves algebraic naturality. Proving that the evaluated states
describe every finite forest is a separate graph-theoretic obligation.
-/

namespace PrincipalMomentAudit.Transport

noncomputable section

def Expression.listSum : List Expression → Expression
  | [] => .scalar 0
  | p :: ps => .add p (Expression.listSum ps)

def sumExpressions {ι : Type*} [Fintype ι] (p : ι → Expression) : Expression :=
  Expression.listSum (Finset.univ.toList.map p)

def productExpressions {ι : Type*} [Fintype ι] (p : ι → Expression) : Expression :=
  Expression.listProduct (Finset.univ.toList.map p)

structure PruningState (ρ : Type*) where
  adjacency : Expression
  degree : Expression
  typeSelector : ρ → Expression

def initialState : PruningState Unit :=
  ⟨.adjacency, .degree, fun _ => .one⟩

namespace PruningState

variable {ρ : Type*} [Fintype ρ]

def active (s : PruningState ρ) : Expression := sumExpressions s.typeSelector

def leaves (N : ℕ) (s : PruningState ρ) : Expression :=
  .mul s.active (levelSelector N 1 s.degree)

def leafCounts (N : ℕ) (s : PruningState ρ) : Expression :=
  .mul (.mul s.adjacency (s.leaves N)) s.adjacency

def centerEdges (N : ℕ) (s : PruningState ρ) : Expression :=
  .mul (s.leaves N) (levelSelector N 1 (s.leafCounts N))

def peeledType (N : ℕ) (s : PruningState ρ) (r : ρ) : Expression :=
  .mul (.mul (s.typeSelector r) (s.leaves N)) (Expression.one.sub (s.centerEdges N))

def peeled (N : ℕ) (s : PruningState ρ) : Expression :=
  sumExpressions (s.peeledType N)

def childCounts (N : ℕ) (s : PruningState ρ) (r : ρ) : Expression :=
  .mul (.mul s.adjacency (s.peeledType N r)) s.adjacency

/-- μ=(σ,(k_ρ)_ρ), with the same fixed range 0..N in both represented pairs. -/
def next (N : ℕ) (s : PruningState ρ) : PruningState (ρ × (ρ → Fin (N + 1))) where
  adjacency := .mul (.mul (Expression.one.sub (s.peeled N)) s.adjacency) (Expression.one.sub (s.peeled N))
  degree := (s.degree.sub (s.peeled N)).sub (sumExpressions (s.childCounts N))
  typeSelector μ := .mul (.mul (s.typeSelector μ.1) (Expression.one.sub (s.peeled N)))
    (productExpressions (fun r => levelSelector N (μ.2 r).val (s.childCounts N r)))

def centerVertices (N : ℕ) (s : PruningState ρ) : Expression :=
  .mul s.active (levelSelector N 0 s.degree)

def centerVertexType (N : ℕ) (s : PruningState ρ) (r : ρ) : Expression :=
  .mul (s.centerVertices N) (s.typeSelector r)

def centerEdgeType (N : ℕ) (s : PruningState ρ) (r q : ρ) : Expression :=
  .mul (.mul (s.typeSelector r) (s.centerEdges N))
    (levelSelector N 1
      (.mul (.mul (.mul s.adjacency (s.typeSelector q)) (s.centerEdges N)) s.adjacency))

/-- The vector reverse step in Section 3.4: η_(t,ρ) A_t applied to the parent vector. -/
def reverseVector (N : ℕ) (s : PruningState ρ) (r : ρ) (parent : Expression) : Expression :=
  .mul (.mul (s.peeledType N r) s.adjacency) parent

/-- The quotient reverse step uses stored η_(t,ρ) and B_t from the same old stage. -/
def reverseQuotient (N : ℕ) (s : PruningState ρ) (r : ρ)
    (parentProjection : Expression) : Expression :=
  .mul (.mul (.mul (.mul (s.peeledType N r) s.adjacency) parentProjection)
    s.adjacency) (s.peeledType N r)

theorem next_state_transport {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (A D : Module.End ℝ E) (A' D' : Module.End ℝ F)
    (hA : Intertwines L A A') (hD : Intertwines L D D')
    (N : ℕ) (s : PruningState ρ) :
    Intertwines L ((s.next N).adjacency.eval A D) ((s.next N).adjacency.eval A' D') ∧
    Intertwines L ((s.next N).degree.eval A D) ((s.next N).degree.eval A' D') ∧
    ∀ μ, Intertwines L ((s.next N).typeSelector μ |>.eval A D)
      ((s.next N).typeSelector μ |>.eval A' D') := by
  exact ⟨expression_transport L A D A' D' hA hD _,
    expression_transport L A D A' D' hA hD _,
    fun _ => expression_transport L A D A' D' hA hD _⟩

theorem reverse_quotient_transport {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (A D : Module.End ℝ E) (A' D' : Module.End ℝ F)
    (hA : Intertwines L A A') (hD : Intertwines L D D')
    (N : ℕ) (s : PruningState ρ) (r : ρ) (parent : Expression) :
    Intertwines L ((s.reverseQuotient N r parent).eval A D)
      ((s.reverseQuotient N r parent).eval A' D') :=
  expression_transport L A D A' D' hA hD _

end PruningState

#print axioms PruningState.next_state_transport
#print axioms PruningState.reverse_quotient_transport

end

end PrincipalMomentAudit.Transport
