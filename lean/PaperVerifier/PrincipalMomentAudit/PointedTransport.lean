import PaperVerifier.PrincipalMomentAudit.GNS

/-! Converse of GNS realization: actual pointed intertwining implies all moments agree. -/
namespace PrincipalMomentAudit.PointedTransport
noncomputable section
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def wordVector (T : Bool → Module.End ℝ E) (seed : E) (w : Word) : principal T seed :=
  ⟨wordEval T w seed, word_mem_principal T seed w⟩

theorem wordVector_cons (T : Bool → Module.End ℝ E) (seed : E) (b : Bool) (w : Word) :
    wordVector T seed (b :: w) = restricted T seed b (wordVector T seed w) := by
  apply Subtype.ext
  rfl

theorem pointed_isometry_transports_words
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F)
    (Φ : principal T seed ≃ₗᵢ[ℝ] principal U target)
    (hseed : Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩)
    (hgen : ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x))
    (w : Word) : Φ (wordVector T seed w) = wordVector U target w := by
  induction w with
  | nil => exact hseed
  | cons b w ih => rw [wordVector_cons, hgen, ih, ← wordVector_cons]

theorem pointed_isometry_implies_equal_word_moments
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F)
    (Φ : principal T seed ≃ₗᵢ[ℝ] principal U target)
    (hseed : Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩)
    (hgen : ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x)) :
    ∀ w, moment T seed w = moment U target w := by
  intro w
  have h := Φ.inner_map_map ⟨seed, seed_mem_principal T seed⟩ (wordVector T seed w)
  rw [hseed, pointed_isometry_transports_words T U seed target Φ hseed hgen w] at h
  exact h.symm

#print axioms pointed_isometry_transports_words
#print axioms pointed_isometry_implies_equal_word_moments
end
end PrincipalMomentAudit.PointedTransport
