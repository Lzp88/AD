import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Hermitian
import PaperVerifier.PrincipalMomentAudit.GNS

/-!
Exact graph interpretation of the GNS development.
The two generators below are the ordinary 0/1 adjacency matrix and the
diagonal matrix of actual neighbor counts of a finite simple graph.
The all-ones seed has no normalization. The moment is 1^T w(A,D) 1.
No tree reconstruction assertion is assumed or proved in this file.
-/

namespace PrincipalMomentAudit.GraphSemantics

noncomputable section

open scoped InnerProductSpace
open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `false` names adjacency; `true` names degree. -/
def generatorMatrix (b : Bool) : Matrix V V ℝ :=
  if b then G.degMatrix ℝ else G.adjMatrix ℝ

def generators (b : Bool) : Module.End ℝ (EuclideanSpace ℝ V) :=
  (generatorMatrix G b).toEuclideanLin

def oneSeed : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ => (1 : ℝ))

theorem generators_symmetric (b : Bool) : (generators G b).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  cases b
  · exact G.isHermitian_adjMatrix ℝ
  · exact G.isHermitian_degMatrix ℝ

def wordMatrix : Word → Matrix V V ℝ
  | [] => 1
  | b :: w => generatorMatrix G b * wordMatrix w

theorem wordEval_matrix (w : Word) (x : V → ℝ) :
    wordEval (generators G) w (WithLp.toLp 2 x) =
      WithLp.toLp 2 (wordMatrix G w *ᵥ x) := by
  induction w with
  | nil => simp [wordMatrix]
  | cons b w ih =>
      rw [wordEval_cons, ih]
      change WithLp.toLp 2 (generatorMatrix G b *ᵥ (wordMatrix G w *ᵥ x)) =
        WithLp.toLp 2 ((generatorMatrix G b * wordMatrix G w) *ᵥ x)
      rw [Matrix.mulVec_mulVec]

/-- Literal double-sum form of the paper's unnormalized scalar moment. -/
theorem graph_moment_double_sum (w : Word) :
    moment (generators G) (oneSeed (V := V)) w =
      ∑ u : V, ∑ v : V, wordMatrix G w u v := by
  unfold moment oneSeed
  rw [wordEval_matrix]
  rw [PiLp.inner_apply]
  simp [Matrix.mulVec, dotProduct]

/-- The empty-word moment is the vertex count, including the zero-dimensional case. -/
theorem empty_word_moment :
    moment (generators G) (oneSeed (V := V)) [] = (Fintype.card V : ℝ) := by
  unfold moment
  rw [wordEval_nil, PiLp.inner_apply]
  simp [oneSeed]

section TwoGraphs

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Equal moments give a common selector bound N because they give the same order. -/
theorem equal_moments_same_order
    (h : ∀ w, moment (generators G) (oneSeed (V := V)) w =
      moment (generators H) (oneSeed (V := W)) w) :
    Fintype.card V = Fintype.card W := by
  have hempty := h []
  rw [empty_word_moment, empty_word_moment] at hempty
  exact_mod_cast hempty

/-- Public arXiv:2607.21494v1 Lemma 5.2 instantiated on actual graph matrices.
The result is a pointed isometry, not a vertex permutation or graph isomorphism. -/
theorem graph_cyclic_moment_realization
    (h : ∀ w, moment (generators G) (oneSeed (V := V)) w =
      moment (generators H) (oneSeed (V := W)) w) :
    ∃ Φ : principal (generators G) (oneSeed (V := V)) ≃ₗᵢ[ℝ]
        principal (generators H) (oneSeed (V := W)),
      Φ ⟨oneSeed (V := V), seed_mem_principal _ _⟩ =
        ⟨oneSeed (V := W), seed_mem_principal _ _⟩ ∧
      ∀ b x, Φ (restricted (generators G) (oneSeed (V := V)) b x) =
        restricted (generators H) (oneSeed (V := W)) b (Φ x) :=
  cyclic_moment_realization _ _ (generators_symmetric G) (generators_symmetric H) _ _ h

end TwoGraphs

#print axioms graph_moment_double_sum
#print axioms empty_word_moment
#print axioms equal_moments_same_order
#print axioms graph_cyclic_moment_realization

end

end PrincipalMomentAudit.GraphSemantics
