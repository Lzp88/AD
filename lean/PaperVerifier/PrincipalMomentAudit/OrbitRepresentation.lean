import PaperVerifier.PrincipalMomentAudit.OrbitQuotient
import PaperVerifier.PrincipalMomentAudit.SelectorEvaluation

/-!
Literal original-orbit coordinate representation used by public arXiv:2607.21494v1 §4--5.
Coordinates are coefficients of unnormalized orbit indicators. In particular
the quotient adjacency B need not be symmetric in the ordinary dot product;
the inner product comes from the actual vertex-space orbit indicator basis.
The cyclic all-ones seed maps to the all-ones coefficient vector.
-/

namespace PrincipalMomentAudit.OrbitRepresentation
noncomputable section
open Matrix PrincipalMomentAudit.OrbitQuotient PrincipalMomentAudit.Transport PrincipalMomentAudit.SelectorEvaluation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def quotientLift : (Orbit G → ℝ) →ₗ[ℝ] EuclideanSpace ℝ V where
  toFun z := WithLp.toLp 2 (fun v => z (classOf G v))
  map_add' _x _y := rfl
  map_smul' _r _x := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem quotientLift_apply (z : Orbit G → ℝ) (v : V) :
    (quotientLift G z) v = z (classOf G v) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem quotientLift_mem (z : Orbit G → ℝ) : quotientLift G z ∈ orbitConstantModule G := by
  intro u v huv
  change z (classOf G u) = z (classOf G v)
  rw [huv]

def quotientEquiv : (Orbit G → ℝ) ≃ₗ[ℝ] orbitConstantModule G where
  toFun z := ⟨quotientLift G z, quotientLift_mem G z⟩
  invFun x i := (x : EuclideanSpace ℝ V) i.out
  left_inv z := by
    funext i
    change z (classOf G i.out) = z i
    rw [show classOf G i.out = i from Quotient.out_eq i]
  right_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro v
    change (x : EuclideanSpace ℝ V) (classOf G v).out = (x : EuclideanSpace ℝ V) v
    exact x.property _ _ (Quotient.out_eq (classOf G v))
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' r x := by apply Subtype.ext; rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem quotientLift_single (i : Orbit G) :
    quotientLift G (Pi.single i 1) = indicator G i := by
  apply PiLp.ext
  intro v
  rw [quotientLift_apply]
  simp [indicator, Pi.single_apply, eq_comm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem quotientLift_one : quotientLift G (fun _ => 1) = GraphSemantics.oneSeed (V := V) := rfl

def adjacencyQuotient : Matrix (Orbit G) (Orbit G) ℝ := fun i j => quotientEntry G i j
def degreeQuotient : Matrix (Orbit G) (Orbit G) ℝ := Matrix.diagonal (fun i => G.degree i.out)

omit [DecidableEq V] in
theorem degree_at_vertex (v : V) : G.degree (classOf G v).out = G.degree v := by
  obtain ⟨e, he⟩ := (classOf_eq_iff G _ v).mp (Quotient.out_eq (classOf G v))
  have hdeg := e.degree_eq (classOf G v).out
  rw [he] at hdeg
  exact hdeg.symm

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem quotientLift_expansion (z : Orbit G → ℝ) :
    quotientLift G z = ∑ i : Orbit G, z i • indicator G i := by
  apply PiLp.ext
  intro v
  simp [quotientLift_apply, indicator]

theorem adjacency_indicator_quotient (j : Orbit G) :
    GraphSemantics.generators G false (indicator G j) =
      quotientLift G (fun i => adjacencyQuotient G i j) := by
  apply PiLp.ext
  intro v
  rw [adjacency_indicator_apply]
  change ((orbitNeighbors G v j).card : ℝ) = (quotientEntry G (classOf G v) j : ℝ)
  rw [quotientEntry_at_vertex]

theorem adjacency_quotient_intertwines (z : Orbit G → ℝ) :
    GraphSemantics.generators G false (quotientLift G z) =
      quotientLift G (adjacencyQuotient G *ᵥ z) := by
  rw [quotientLift_expansion, map_sum]
  simp_rw [map_smul, adjacency_indicator_quotient]
  apply PiLp.ext
  intro v
  simp [quotientLift_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem degree_quotient_intertwines (z : Orbit G → ℝ) :
    GraphSemantics.generators G true (quotientLift G z) =
      quotientLift G (degreeQuotient G *ᵥ z) := by
  apply PiLp.ext
  intro v
  change (G.degMatrix ℝ *ᵥ (fun v => z (classOf G v))) v =
    (degreeQuotient G *ᵥ z) (classOf G v)
  rw [SimpleGraph.degMatrix_mulVec_apply, degreeQuotient, Matrix.mulVec_diagonal,
    degree_at_vertex]

theorem expression_quotient_intertwines (p : Expression) (z : Orbit G → ℝ) :
    quotientLift G (p.eval (adjacencyQuotient G).toLin' (degreeQuotient G).toLin' z) =
      p.eval (GraphSemantics.generators G false) (GraphSemantics.generators G true)
        (quotientLift G z) := by
  apply expression_transport (quotientLift G)
    (adjacencyQuotient G).toLin' (degreeQuotient G).toLin'
    (GraphSemantics.generators G false) (GraphSemantics.generators G true)
    (fun z => (adjacency_quotient_intertwines G z).symm)
    (fun z => (degree_quotient_intertwines G z).symm) p z

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem matrixEval_toLin' (A D : Matrix (Orbit G) (Orbit G) ℝ) (p : Expression) :
    (matrixEval A D p).toLin' = p.eval A.toLin' D.toLin' := by
  exact matrixEval_algHom (Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Orbit G))).toAlgHom A D p

/-- Every actual shared expression commutes with passing to the weighted quotient. -/
theorem matrixEval_quotient_compatibility (p : Expression) (z : Orbit G → ℝ) :
    quotientLift G ((matrixEval (adjacencyQuotient G) (degreeQuotient G) p) *ᵥ z) =
      (matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p).toEuclideanLin (quotientLift G z) := by
  rw [matrixEval_toEuclideanLin]
  change quotientLift G ((matrixEval (adjacencyQuotient G) (degreeQuotient G) p).toLin' z) = _
  rw [matrixEval_toLin']
  exact expression_quotient_intertwines G p z

#print axioms quotientEquiv
#print axioms adjacency_quotient_intertwines
#print axioms matrixEval_quotient_compatibility
end
end PrincipalMomentAudit.OrbitRepresentation
