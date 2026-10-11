import PaperVerifier.ADComplete.FrobeniusCoordinates

/-! Original-order matrix probes span the full generated algebra by left multiplication. -/

namespace ADComplete.Frobenius

open Matrix Polynomial CircuitAudit.Degrees
open scoped BigOperators Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixWord (H K : Matrix ι ι ℝ) : List Bool → Matrix ι ι ℝ
  | [] => 1
  | b :: w => (if b then K else H) * matrixWord H K w

def algebraModule (H K : Matrix ι ι ℝ) : Submodule ℝ (Matrix ι ι ℝ) :=
  Submodule.span ℝ (Set.range (matrixWord H K))

lemma word_flatten (H K : Matrix ι ι ℝ) (w : List Bool) :
    Spanning.wordVector (leftMatrix H) (leftMatrix K) (flatten 1) w =
      flatten (matrixWord H K w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b <;> simpa only [Spanning.wordVector, matrixWord, Bool.false_eq_true,
        if_false, if_true, ih] using leftMatrix_mulVec _ (matrixWord H K w)

lemma expr_leftMatrix (H K : Matrix ι ι ℝ) (p : Expr) :
    leftMatrix (p.eval H K) = p.eval (leftMatrix H) (leftMatrix K) := by
  change leftHom (p.eval H K) = p.eval (leftHom H) (leftHom K)
  induction p <;> simp_all [Expr.eval]

lemma probe_flatten (S k j : ℕ) (H K : Matrix ι ι ℝ) :
    Spanning.probeVector ((S : ℝ)^2) (leftMatrix H) (leftMatrix K) (flatten 1) k j =
      flatten ((probe S k j).eval H K) := by
  rw [← FrameSemantics.probe_eval_mulVec, ← expr_leftMatrix, leftMatrix_mulVec,
    Matrix.mul_one]

theorem full_probe_spanning (S : ℕ) (hS : 0 < S)
    (H K : Matrix ι ι ℝ) (hH : H.IsSymm) (lo hi : ℝ)
    (hB : ∀ v : ι → ℝ,
      lo * Rigidity.pairing v v ≤
        Rigidity.pairing v ((((S : ℝ)^2)⁻¹ • K).mulVec v) ∧
      Rigidity.pairing v ((((S : ℝ)^2)⁻¹ • K).mulVec v) ≤ hi * Rigidity.pairing v v)
    (hgap : ((Fintype.card ι : ℝ)^2) * (hi-lo) < 1)
    (hcard : (Fintype.card ι)^2 ≤ S) :
    Submodule.span ℝ {P | ∃ k < S, ∃ j ≤ k, P = (probe S k j).eval H K} =
      algebraModule H K := by
  classical
  have hκ : (S : ℝ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hS)
  have hb (v : (ι × ι) → ℝ) :
      lo * Rigidity.pairing v v ≤
        Rigidity.pairing v ((((S : ℝ)^2)⁻¹ • leftMatrix K).mulVec v) ∧
      Rigidity.pairing v ((((S : ℝ)^2)⁻¹ • leftMatrix K).mulVec v) ≤ hi * Rigidity.pairing v v := by
    simpa only [leftMatrix, Matrix.smul_kronecker] using
      leftMatrix_interval (((S : ℝ)^2)⁻¹ • K) lo hi hB v
  have hg : (Fintype.card (ι × ι) : ℝ) * (hi-lo) < 1 := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hgap
  have hc : Fintype.card (ι × ι) ≤ S := by
    simpa only [Fintype.card_prod, pow_two] using hcard
  have hspan := Spanning.uniform_probe_spanning_of_card_le ((S : ℝ)^2) hκ
    (leftMatrix H) (leftMatrix K) (leftMatrix_symmetric H hH) (flatten 1) lo hi hb hg S hc
  apply Submodule.map_injective_of_injective flatten_injective
  rw [Submodule.map_span, algebraModule, Submodule.map_span]
  have hp : flatten '' {P | ∃ k < S, ∃ j ≤ k, P = (probe S k j).eval H K} =
      {z | ∃ k < S, ∃ j ≤ k,
        z = Spanning.probeVector ((S : ℝ)^2) (leftMatrix H) (leftMatrix K) (flatten 1) k j} := by
    ext z
    constructor
    · rintro ⟨p, ⟨k,hk,j,hj,rfl⟩,rfl⟩
      exact ⟨k,hk,j,hj,(probe_flatten S k j H K).symm⟩
    · rintro ⟨k,hk,j,hj,rfl⟩
      exact ⟨_,⟨k,hk,j,hj,rfl⟩,(probe_flatten S k j H K).symm⟩
  have hw : flatten '' Set.range (matrixWord H K) =
      Set.range (Spanning.wordVector (leftMatrix H) (leftMatrix K) (flatten 1)) := by
    ext z
    constructor
    · rintro ⟨p,⟨w,rfl⟩,rfl⟩
      exact ⟨w,word_flatten H K w⟩
    · rintro ⟨w,rfl⟩
      exact ⟨_,⟨w,rfl⟩,(word_flatten H K w).symm⟩
  rw [hp, hw]
  exact hspan

#print axioms full_probe_spanning

end
end ADComplete.Frobenius
