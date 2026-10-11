import PaperVerifier.PrincipalMomentAudit.SharedCoordinateFamily
import PaperVerifier.PrincipalMomentAudit.WeightedQuotientRigidity

/-!
The public arXiv:2607.21494v1 Theorem 5.4 via the literal written proof route:
all polynomial moments -> actual pointed GNS isometry (Lemma 5.2)
-> common literal quotient idempotents recover actual s,b (Lemma 5.3)
-> actual tree graph isomorphism (Theorem 5.1).
No geometric, spanning, selector, or reconstruction conclusion is a premise.
-/
namespace PrincipalMomentAudit.WrittenProof
noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

theorem public_theorem_5_4_word_version
    (hG : G.IsTree) (hH : H.IsTree)
    (hμ : ∀ word, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) word =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) word) :
    Nonempty (G ≃g H) := by
  obtain ⟨Φ, hseed, hgen⟩ := GraphSemantics.graph_cyclic_moment_realization G H hμ
  obtain ⟨e, hs, hB⟩ := SharedCoordinateFamily.pointed_intrinsic_recovery G H hG hH Φ hseed hgen
  exact WeightedQuotientRigidity.actual_weighted_orbit_quotient_determines_tree G H hG hH e hs hB

/-- The exact public all-real-polynomials premise, not just an informal AST input. -/
theorem public_theorem_5_4
    (hG : G.IsTree) (hH : H.IsTree)
    (hμ : ∀ c : Word →₀ ℝ,
      polynomialMoment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) c =
      polynomialMoment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) c) :
    Nonempty (G ≃g H) := by
  apply public_theorem_5_4_word_version G H hG hH
  exact (word_moments_iff_polynomial_moments _ _ _ _).mpr hμ

#print axioms public_theorem_5_4_word_version
#print axioms public_theorem_5_4
end
end PrincipalMomentAudit.WrittenProof
