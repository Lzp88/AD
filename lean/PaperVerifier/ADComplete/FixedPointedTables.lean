import PaperVerifier.ADComplete.PolynomialFrameIsometry
import PaperVerifier.ADComplete.FrameSemantics
import PaperVerifier.ADComplete.SpectralUniformProbes

/-! Complete pointed invariants from the actual fixed triangular expressions.
The hypotheses are the literal spectral diameters and ambient cardinalities;
frame spanning, nonzero seeds, and equality of the two cyclic ranks are not premises. -/

namespace ADComplete.FixedPointedTables

open Matrix CircuitAudit.Degrees PrincipalMomentAudit
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

section Abstract
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def expressionOnPrincipal (T : Bool → Module.End ℝ E) (seed : E) (p : Expr) :
    Module.End ℝ (principal T seed) :=
  p.eval (restricted T seed false) (restricted T seed true)

lemma expressionOnPrincipal_coe (T : Bool → Module.End ℝ E) (seed : E)
    (p : Expr) (x : principal T seed) :
    (expressionOnPrincipal T seed p x : E) = p.eval (T false) (T true) (x : E) := by
  unfold expressionOnPrincipal
  induction p generalizing x <;>
    simp [Expr.eval, Module.End.mul_apply, *]
  all_goals rfl

lemma pointed_isometry_expression_intertwines
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F)
    (Φ : principal T seed ≃ₗᵢ[ℝ] principal U target)
    (hgen : ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x))
    (p : Expr) (x : principal T seed) :
    Φ (expressionOnPrincipal T seed p x) = expressionOnPrincipal U target p (Φ x) := by
  unfold expressionOnPrincipal
  induction p generalizing x <;>
    simp [Expr.eval, Module.End.mul_apply, *]

end Abstract

section Matrices
variable {V W : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]
variable [Fintype W] [DecidableEq W] [Nonempty W]

omit [Fintype W] [DecidableEq W] [Nonempty W] [Nonempty V] in
lemma expression_toEuclideanLin (H K : Matrix V V ℝ) (p : Expr) :
    (p.eval H K).toEuclideanLin = p.eval H.toEuclideanLin K.toEuclideanLin := by
  change (Matrix.toLpLinAlgEquiv 2) (p.eval H K) =
    p.eval ((Matrix.toLpLinAlgEquiv 2) H) ((Matrix.toLpLinAlgEquiv 2) K)
  induction p <;> simp only [Expr.eval, map_zero, map_one, map_zsmul, map_add, map_mul, *]

omit [Fintype W] [DecidableEq W] [Nonempty W] [Nonempty V] in
lemma expression_seed_coe (H K : Matrix V V ℝ) (v : V → ℝ) (p : Expr) :
    (expressionOnPrincipal (FrameSemantics.generators H K) (WithLp.toLp 2 v) p
      ⟨WithLp.toLp 2 v, seed_mem_principal _ _⟩ : EuclideanSpace ℝ V) =
    WithLp.toLp 2 ((p.eval H K).mulVec v) := by
  rw [expressionOnPrincipal_coe]
  change p.eval H.toEuclideanLin K.toEuclideanLin (WithLp.toLp 2 v) = _
  rw [← expression_toEuclideanLin]
  rfl

def fixedThreeTablesEqual (N : ℕ) (H K : Matrix V V ℝ) (v : V → ℝ)
    (H' K' : Matrix W W ℝ) (v' : W → ℝ) : Prop :=
  (∀ i j, ⟪FrameSemantics.probeFrame N H K v i, FrameSemantics.probeFrame N H K v j⟫_ℝ =
    ⟪FrameSemantics.probeFrame N H' K' v' i, FrameSemantics.probeFrame N H' K' v' j⟫_ℝ) ∧
  (∀ b i j, ⟪FrameSemantics.probeFrame N H K v i,
      FrameSemantics.generators H K b (FrameSemantics.probeFrame N H K v j)⟫_ℝ =
    ⟪FrameSemantics.probeFrame N H' K' v' i,
      FrameSemantics.generators H' K' b (FrameSemantics.probeFrame N H' K' v' j)⟫_ℝ)

theorem public_fixed_three_tables_iff_pointed_isometry
    (N : ℕ) (hN : 1 ≤ N) (hcard : Fintype.card V ≤ N) (hcard' : Fintype.card W ≤ N)
    (H K : Matrix V V ℝ) (hH : H.IsSymm) (hK : K.IsSymm) (v : V → ℝ)
    (H' K' : Matrix W W ℝ) (hH' : H'.IsSymm) (hK' : K'.IsSymm) (v' : W → ℝ)
    (hdiam : SpectralBands.eigenMax K (Matrix.isHermitian_iff_isSymm.mpr hK) -
      SpectralBands.eigenMin K (Matrix.isHermitian_iff_isSymm.mpr hK) ≤ (N : ℝ)-1)
    (hdiam' : SpectralBands.eigenMax K' (Matrix.isHermitian_iff_isSymm.mpr hK') -
      SpectralBands.eigenMin K' (Matrix.isHermitian_iff_isSymm.mpr hK') ≤ (N : ℝ)-1) :
    fixedThreeTablesEqual N H K v H' K' v' ↔
    ∃ Φ : principal (FrameSemantics.generators H K) (WithLp.toLp 2 v) ≃ₗᵢ[ℝ]
        principal (FrameSemantics.generators H' K') (WithLp.toLp 2 v'),
      Φ ⟨WithLp.toLp 2 v, seed_mem_principal _ _⟩ =
        ⟨WithLp.toLp 2 v', seed_mem_principal _ _⟩ ∧
      ∀ b x, Φ (restricted (FrameSemantics.generators H K) (WithLp.toLp 2 v) b x) =
        restricted (FrameSemantics.generators H' K') (WithLp.toLp 2 v') b (Φ x) := by
  let T := FrameSemantics.generators H K
  let U := FrameSemantics.generators H' K'
  let s := WithLp.toLp 2 v
  let t := WithLp.toLp 2 v'
  let f := FrameSemantics.probeFrame N H K v
  let g := FrameSemantics.probeFrame N H' K' v'
  have hf := FrameSemantics.probeFrame_range_eq_principal N H K v
    (Spanning.uniform_probes_of_spectral_diameter N hN hcard H K hH hK v hdiam)
  have hg := FrameSemantics.probeFrame_range_eq_principal N H' K' v'
    (Spanning.uniform_probes_of_spectral_diameter N hN hcard' H' K' hH' hK' v' hdiam')
  constructor
  · rintro ⟨hGram, hGen⟩
    have hone : Expr.one ∈ probeList N N :=
      (FrameSemantics.probeList_members N N .one).mpr
        ⟨0, by omega, 0, by omega, by simp [probe]⟩
    obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hone
    have hs : f i₀ = s := by
      change WithLp.toLp 2 ((((probeList N N).get i₀).eval H K).mulVec v) = WithLp.toLp 2 v
      rw [hi₀]
      simp [Expr.eval]
    have ht : g i₀ = t := by
      change WithLp.toLp 2 ((((probeList N N).get i₀).eval H' K').mulVec v') = WithLp.toLp 2 v'
      rw [hi₀]
      simp [Expr.eval]
    refine ⟨GramTables.frameIsometry T U s t f g hf hg hGram, ?_, ?_⟩
    · exact GramTables.frameIsometry_seed T U s t f g hf hg hGram i₀ hs ht
    · exact GramTables.frameIsometry_intertwines T U s t f g hf hg hGram hGen
  · rintro ⟨Φ, hseed, hgen⟩
    let x (i : Fin (probeList N N).length) : principal T s :=
      expressionOnPrincipal T s ((probeList N N).get i) ⟨s, seed_mem_principal T s⟩
    let y (i : Fin (probeList N N).length) : principal U t :=
      expressionOnPrincipal U t ((probeList N N).get i) ⟨t, seed_mem_principal U t⟩
    have hx (i) : (x i : EuclideanSpace ℝ V) = f i := expression_seed_coe H K v _
    have hy (i) : (y i : EuclideanSpace ℝ W) = g i := expression_seed_coe H' K' v' _
    have hxy (i) : Φ (x i) = y i := by
      dsimp [x, y]
      rw [pointed_isometry_expression_intertwines T U s t Φ hgen, hseed]
    constructor
    · intro i j
      have he := Φ.inner_map_map (x i) (x j)
      rw [hxy i, hxy j] at he
      simpa only [Submodule.coe_inner, hx, hy] using he.symm
    · intro b i j
      have he := Φ.inner_map_map (x i) (restricted T s b (x j))
      rw [hxy i, hgen, hxy j] at he
      simpa only [Submodule.coe_inner, restricted, LinearMap.restrict_apply, hx, hy] using he.symm

#print axioms public_fixed_three_tables_iff_pointed_isometry

end Matrices
end
end ADComplete.FixedPointedTables
