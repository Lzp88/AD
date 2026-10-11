import PaperVerifier.ADComplete.TraceMomentBridge
import PaperVerifier.ADComplete.GraphDegreeBand
import PaperVerifier.ADComplete.UniformProbeBounds
import PaperVerifier.PrincipalMomentAudit.WrittenProof

/-!
# Complete semantics of the public compiled tree invariant

The source-sink object here is the actual allowed-gate instruction program,
with the identity branch at N=1. Every spanning, height, all-ones, and Gram
condition is discharged. The predecessor's audited reconstruction theorem is
used through its existing public word-moment interface.
-/

namespace ADComplete.FinalTreeSeparation
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix PrincipalMomentAudit

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The exact fixed probe frame spans on every graph of at most N vertices. -/
theorem actual_graph_probe_spanning (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ N) :
    Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
      z = Spanning.probeVector ((N : ℝ)^2) (G.adjMatrix ℝ) (G.degMatrix ℝ)
        (fun _ => 1) k j} =
      Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) :=
  Spanning.uniform_probe_spanning_of_card_le ((N : ℝ)^2)
    (GraphDegreeBand.selector_scale_ne_zero N hN) (G.adjMatrix ℝ) (G.degMatrix ℝ)
    G.isSymm_adjMatrix (fun _ => 1) 0 (((N : ℝ) - 1) / (N : ℝ)^2)
    (GraphDegreeBand.actual_degree_band N hN G hn)
    (GraphDegreeBand.actual_degree_gap N hN hn) N hn

/-- All moments from the actual compiled trace; no frame conclusion is a premise. -/
theorem actual_tree_trace_implies_moments (N : ℕ) (hN : 1 ≤ N) (hne : N ≠ 1)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N)
    (ht : CompiledReadout.trace N (IntegerBounds.radixNat N) G =
      CompiledReadout.trace N (IntegerBounds.radixNat N) H) :
    ∀ w, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) w =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) w :=
  TraceMomentBridge.actual_trace_implies_moments_of_spanning N hN hne G H hG hH hnG hnH
    (actual_graph_probe_spanning N hN G hnG) (actual_graph_probe_spanning N hN H hnH) ht

/-- Complete classification by the actual public program, including N=1. -/
theorem public_compiled_trace_classifies_trees (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hG : G.IsTree) (hH : H.IsTree) (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N) :
    CompiledReadout.trace N (IntegerBounds.radixNat N) G =
      CompiledReadout.trace N (IntegerBounds.radixNat N) H ↔ Nonempty (G ≃g H) := by
  constructor
  · intro ht
    by_cases h : N = 1
    · subst N
      exact TraceMomentBridge.singleton_trees_isomorphic G H hG hH hnG hnH
    · exact WrittenProof.public_theorem_5_4_word_version G H hG hH
        (actual_tree_trace_implies_moments N hN h G H hG hH hnG hnH ht)
  · rintro ⟨e⟩
    exact CompiledReadout.graphIso_preserves_trace N hN _ G H e

#print axioms actual_graph_probe_spanning
#print axioms actual_tree_trace_implies_moments
#print axioms public_compiled_trace_classifies_trees
end
end ADComplete.FinalTreeSeparation
