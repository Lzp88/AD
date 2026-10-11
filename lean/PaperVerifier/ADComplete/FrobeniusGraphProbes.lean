import PaperVerifier.ADComplete.FrobeniusTrace
import PaperVerifier.ADComplete.GraphDegreeBand

/-! The actual N-squared Frobenius probe frame on every graph of order at most N. -/

namespace ADComplete.Frobenius

open Matrix Module PrincipalMomentAudit
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem actual_full_graph_probe_spanning (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ N) :
    Submodule.span ℝ {P | ∃ k < N^2, ∃ j ≤ k,
      P = (CircuitAudit.Degrees.probe (N^2) k j).eval (G.adjMatrix ℝ) (G.degMatrix ℝ)} =
      algebraModule (G.adjMatrix ℝ) (G.degMatrix ℝ) := by
  have hS : 1 ≤ N^2 := by nlinarith
  have hc : (Fintype.card V)^2 ≤ N^2 := Nat.pow_le_pow_left hn 2
  have hnS : Fintype.card V ≤ N^2 := hn.trans (by nlinarith)
  have hg := GraphDegreeBand.actual_degree_gap (V := V×V) (N^2) hS
    (by simpa only [Fintype.card_prod, pow_two] using hc)
  apply full_probe_spanning (N^2) (by omega) (G.adjMatrix ℝ) (G.degMatrix ℝ)
    G.isSymm_adjMatrix 0 ((((N^2 : ℕ) : ℝ)-1) / (((N^2 : ℕ) : ℝ)^2))
    (GraphDegreeBand.actual_degree_band (N^2) hS G hnS) ?_ hc
  simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hg

theorem actual_full_lifted_probe_spanning (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ N) :
    Submodule.span ℝ {z | ∃ k < N^2, ∃ j ≤ k,
      z = Spanning.probeVector (((N^2 : ℕ) : ℝ)^2)
        (leftMatrix (G.adjMatrix ℝ)) (leftMatrix (G.degMatrix ℝ))
        (flatten (1 : Matrix V V ℝ)) k j} =
      Spanning.jointModule (leftMatrix (G.adjMatrix ℝ)) (leftMatrix (G.degMatrix ℝ))
        (flatten (1 : Matrix V V ℝ)) := by
  have hS : 1 ≤ N^2 := by nlinarith
  have hc : Fintype.card (V×V) ≤ N^2 := by
    simpa only [Fintype.card_prod, pow_two] using Nat.pow_le_pow_left hn 2
  have hnS : Fintype.card V ≤ N^2 := hn.trans (by nlinarith)
  have hb := GraphDegreeBand.actual_degree_band (N^2) hS G hnS
  have hb' := leftMatrix_interval ((((N^2 : ℕ) : ℝ)^2)⁻¹ • G.degMatrix ℝ)
    0 ((((N^2 : ℕ) : ℝ)-1) / (((N^2 : ℕ) : ℝ)^2)) hb
  have hg := GraphDegreeBand.actual_degree_gap (V := V×V) (N^2) hS hc
  apply Spanning.uniform_probe_spanning_of_card_le (((N^2 : ℕ) : ℝ)^2)
    (GraphDegreeBand.selector_scale_ne_zero (N^2) hS)
    (leftMatrix (G.adjMatrix ℝ)) (leftMatrix (G.degMatrix ℝ))
    (leftMatrix_symmetric _ G.isSymm_adjMatrix) (flatten 1)
    0 ((((N^2 : ℕ) : ℝ)-1) / (((N^2 : ℕ) : ℝ)^2)) ?_ hg (N^2) hc
  simpa only [leftMatrix, Matrix.smul_kronecker] using hb'

def fullFrame (N : ℕ) (H K : Matrix V V ℝ) :
    Fin (CircuitAudit.Degrees.probeList (N^2) (N^2)).length → EuclideanSpace ℝ (V×V) :=
  FrameSemantics.probeFrame (N^2) (leftMatrix H) (leftMatrix K) (flatten 1)

lemma fullFrame_apply (N : ℕ) (H K : Matrix V V ℝ)
    (i : Fin (CircuitAudit.Degrees.probeList (N^2) (N^2)).length) :
    fullFrame N H K i = WithLp.toLp 2
      (flatten (FrameSemantics.probeMatrices (N^2) H K i)) := by
  unfold fullFrame FrameSemantics.probeFrame FrameSemantics.probeMatrices
  rw [← expr_leftMatrix, leftMatrix_mulVec, Matrix.mul_one]

theorem actual_full_frame_range (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ N) :
    LinearMap.range (combination (fullFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ))) =
      principal (FrameSemantics.generators (leftMatrix (G.adjMatrix ℝ))
        (leftMatrix (G.degMatrix ℝ))) (WithLp.toLp 2 (flatten (1 : Matrix V V ℝ))) :=
  FrameSemantics.probeFrame_range_eq_principal (N^2) _ _ _
    (actual_full_lifted_probe_spanning N hN G hn)

#print axioms actual_full_graph_probe_spanning
#print axioms actual_full_frame_range

end
end ADComplete.Frobenius
