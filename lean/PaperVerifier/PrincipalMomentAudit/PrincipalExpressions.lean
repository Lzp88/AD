import PaperVerifier.PrincipalMomentAudit.GraphSemantics
import PaperVerifier.PrincipalMomentAudit.OrbitQuotient
import PaperVerifier.PrincipalMomentAudit.SelectorEvaluation

/-!
Every literal AD expression acts on the actual word-generated principal
module. In particular the actual type-cell indicators supplied by the
pruning expressions belong to that module and are constant on genuine
automorphism orbits. No classification of those cells as orbits is assumed.
-/

namespace PrincipalMomentAudit.PrincipalExpressions
noncomputable section
open Matrix PrincipalMomentAudit.Transport PrincipalMomentAudit.SelectorEvaluation

theorem expression_preserves_principal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Bool → Module.End ℝ E) (seed : E) (p : Expression) (x : E)
    (hx : x ∈ principal T seed) : p.eval (T false) (T true) x ∈ principal T seed := by
  induction p generalizing x with
  | scalar r =>
      change r • x ∈ principal T seed
      exact Submodule.smul_mem _ r hx
  | adjacency => exact principal_invariant T seed false x hx
  | degree => exact principal_invariant T seed true x hx
  | add p q hp hq =>
      exact Submodule.add_mem _ (hp x hx) (hq x hx)
  | mul p q hp hq => exact hp _ (hq x hx)

theorem expression_seed_mem_principal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Bool → Module.End ℝ E) (seed : E) (p : Expression) :
    p.eval (T false) (T true) seed ∈ principal T seed :=
  expression_preserves_principal T seed p seed (seed_mem_principal T seed)

theorem restricted_expression_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Bool → Module.End ℝ E) (seed : E) (p : Expression) (x : principal T seed) :
    (p.eval (restricted T seed false) (restricted T seed true) x : E) =
      p.eval (T false) (T true) (x : E) := by
  induction p generalizing x with
  | scalar _ => rfl
  | adjacency => rfl
  | degree => rfl
  | add p q hp hq =>
      change (p.eval (restricted T seed false) (restricted T seed true) x : E) +
        (q.eval (restricted T seed false) (restricted T seed true) x : E) = _
      rw [hp, hq]
      rfl
  | mul p q hp hq =>
      change (p.eval (restricted T seed false) (restricted T seed true)
        (q.eval (restricted T seed false) (restricted T seed true) x) : E) = _
      rw [hp, hq]
      rfl

def expressionVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Bool → Module.End ℝ E) (seed : E) (p : Expression) : principal T seed :=
  ⟨p.eval (T false) (T true) seed, expression_seed_mem_principal T seed p⟩

theorem restricted_expression_seed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Bool → Module.End ℝ E) (seed : E) (p : Expression) :
    p.eval (restricted T seed false) (restricted T seed true) ⟨seed, seed_mem_principal T seed⟩ =
      expressionVector T seed p := by
  apply Subtype.ext
  exact restricted_expression_apply T seed p _

theorem expressionVector_transport
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F)
    (Φ : principal T seed ≃ₗᵢ[ℝ] principal U target)
    (hseed : Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩)
    (hgen : ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x))
    (p : Expression) : Φ (expressionVector T seed p) = expressionVector U target p := by
  have h := expression_transport Φ.toLinearEquiv.toLinearMap
    (restricted T seed false) (restricted T seed true)
    (restricted U target false) (restricted U target true)
    (hgen false) (hgen true) p ⟨seed, seed_mem_principal T seed⟩
  change Φ (p.eval (restricted T seed false) (restricted T seed true)
    ⟨seed, seed_mem_principal T seed⟩) =
    p.eval (restricted U target false) (restricted U target true)
      (Φ ⟨seed, seed_mem_principal T seed⟩) at h
  rw [restricted_expression_seed, hseed, restricted_expression_seed] at h
  exact h

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def setIndicator (S : Finset V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun v => if v ∈ S then (1 : ℝ) else 0)

theorem selector_seed (S : Finset V) :
    (vertexSelector S).toEuclideanLin (GraphSemantics.oneSeed (V := V)) =
      setIndicator S := by
  change WithLp.toLp 2 (vertexSelector S *ᵥ (fun _ => 1)) = _
  unfold setIndicator
  congr 1
  funext v
  simp [vertexSelector, Matrix.mulVec_diagonal]

/-- A matrix selector constructed by a literal polynomial supplies its
actual indicator in the actual principal module. -/
theorem literal_selector_indicator_mem (p : Expression) (S : Finset V)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = vertexSelector S) :
    setIndicator S ∈ principal (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) := by
  have h := expression_seed_mem_principal (GraphSemantics.generators G)
    (GraphSemantics.oneSeed (V := V)) p
  change p.eval (G.adjMatrix ℝ).toEuclideanLin (G.degMatrix ℝ).toEuclideanLin
    (GraphSemantics.oneSeed (V := V)) ∈ _ at h
  rw [← matrixEval_toEuclideanLin, hp, selector_seed] at h
  exact h

theorem all_stage_type_indicators_mem (t : ℕ) (r : StageType (Fintype.card V) t) :
    setIndicator (typeCell (stageActive G t) (stageLabel G t) r) ∈
      principal (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) := by
  exact literal_selector_indicator_mem G _ _ ((all_stages_realizes G t).typeSelector r)

/-- This is actual automorphism invariance, derived from membership, not a
new hypothesis in the type-classification argument. -/
theorem all_stage_type_indicators_orbit_constant (t : ℕ)
    (r : StageType (Fintype.card V) t) :
    setIndicator (typeCell (stageActive G t) (stageLabel G t) r) ∈
      OrbitQuotient.orbitConstantModule G :=
  OrbitQuotient.principal_le_orbitConstantModule G (all_stage_type_indicators_mem G t r)

#print axioms literal_selector_indicator_mem
#print axioms all_stage_type_indicators_orbit_constant
end
end PrincipalMomentAudit.PrincipalExpressions
