import PaperVerifier.ADComplete.PSDCompiledValue
import PaperVerifier.ADComplete.PSDGraphFrame
import PaperVerifier.ADComplete.PSDFactorySOS

/-! Complete literal PSD factory semantics on actual trees, including N=1. -/
namespace ADComplete.PSDFactory
open Matrix CircuitAudit.CircuitCosts CircuitAudit.Degrees
noncomputable section
set_option backward.isDefEq.respectTransparency false

def treeCompiledMatrix (N : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℝ :=
  ((compiled N).2.value (compiled N).1 (G.adjMatrix ℝ) (G.degMatrix ℝ)).1

theorem actual_tree_compiled_value {N n : ℕ} (hN : 2 ≤ N)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsTree) (hn : n ≤ N) :
    treeCompiledMatrix N G = PSDFoldedFrame.graphFoldedMatrix N G := by
  have hc : Fintype.card (Fin n) ≤ N := by simpa only [Fintype.card_fin] using hn
  have hj0 := TreeDistance.actual_allOnes_expression_identity G hG hc
  have hj := congrArg MatrixSemantics.realMatrix hj0
  rw [MatrixSemantics.realMatrix_eval, MatrixSemantics.realMatrix_adjacency,
    MatrixSemantics.realMatrix_degree] at hj
  have hJ : (allOnes N).eval (G.adjMatrix ℝ) (G.degMatrix ℝ) = PSDHomogeneousLift.J n := by
    rw [hj]
    ext i j
    norm_num [MatrixSemantics.realMatrix, TreeDistance.onesMatrix, PSDHomogeneousLift.J]
  have ht : tau N = PSDFoldedFrame.tau N ((probeList N N).drop 1).length
      (IntegerBounds.RNat N) := by
    rw [PSDFoldedFrame.graph_tail_length]
    rfl
  have hv (i : Fin N) : ((frameExpr N i).eval (G.adjMatrix ℝ) (G.degMatrix ℝ)).mulVec
      (fun _ => 1) = PSDFoldedFrame.foldedVector (fun _ => 1) (PSDFoldedFrame.graphTail N G)
        (PSDFoldedFrame.tau N ((probeList N N).drop 1).length (IntegerBounds.RNat N)) i.val := by
    have hh := PSDFoldedFrame.literal_fold_vector_real (tau N) ((probeList N N).drop 1)
      (G.adjMatrix ℤ) (G.degMatrix ℤ) (fun _ => 1) i.val
    change (PSDFoldCompiler.foldExpr (tau N) ((probeList N N).drop 1) i.val).eval
      (MatrixSemantics.realMatrix (G.adjMatrix ℤ)) (MatrixSemantics.realMatrix (G.degMatrix ℤ))
        *ᵥ PSDFoldedFrame.castVector (fun _ => 1) = _ at hh
    rw [MatrixSemantics.realMatrix_adjacency, MatrixSemantics.realMatrix_degree,
      PSDFoldedFrame.castVector_one, ht] at hh
    simpa only [frameExpr, ht, PSDFoldedFrame.graphTail] using hh
  simpa only [treeCompiledMatrix, PSDFoldedFrame.graphFoldedMatrix, Fintype.card_fin] using
    compiled_value_folded hN (G.adjMatrix ℝ) (G.degMatrix ℝ)
    (G.isHermitian_adjMatrix ℝ) (G.isHermitian_degMatrix ℝ) hJ
    ((probeList N N).drop 1).length (IntegerBounds.RNat N) (fun _ => 1)
    (PSDFoldedFrame.graphTail N G) PSDFoldedFrame.castVector_one hv

theorem singleton_submodule_top {V : Type*} [Fintype V] [Nonempty V] [Subsingleton V]
    (W : Submodule ℝ (V → ℝ)) (hw : (fun _ => (1 : ℝ)) ∈ W) : W = ⊤ := by
  classical
  apply le_antisymm le_top
  intro z _
  let i : V := Classical.choice inferInstance
  have hz : z = (z i) • (fun _ => (1 : ℝ)) := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    exact congrArg z (Subsingleton.elim j i)
  rw [hz]
  exact W.smul_mem _ hw

/-- No successful fold, rank, Gram nonsingularity, image or cyclicity premise
is supplied. The source is the fixed allowed-gate factory on the actual graph. -/
theorem public_psd_factory_on_trees {N n : ℕ} (hN : 1 ≤ N)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsTree) (hn : n ≤ N) :
    (treeCompiledMatrix N G).PosSemidef ∧
      LinearMap.range (treeCompiledMatrix N G).mulVecLin =
        Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) ∧
      Submodule.span ℝ (Set.range (fun k : Fin N =>
        ((treeCompiledMatrix N G)^k.val).mulVec (fun _ => 1))) =
        Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) := by
  let : Nonempty (Fin n) := hG.connected.nonempty
  by_cases he : N = 1
  · subst N
    let : Subsingleton (Fin n) := Fintype.card_le_one_iff_subsingleton.mp
      (by simpa only [Fintype.card_fin] using hn)
    have hC : treeCompiledMatrix 1 G = 1 :=
      congrArg Prod.fst (compiled_one_value (G.adjMatrix ℝ) (G.degMatrix ℝ))
    have hm : Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) = ⊤ :=
      singleton_submodule_top _ (Spanning.seed_mem _ _ _)
    rw [hC, hm]
    refine ⟨Matrix.PosSemidef.one, ?_, ?_⟩
    · rw [Matrix.mulVecLin_one, LinearMap.range_id]
    · apply singleton_submodule_top
      apply Submodule.subset_span
      exact ⟨0, by simp⟩
  · rw [actual_tree_compiled_value (by omega) G hG hn]
    exact PSDFoldedFrame.graph_folded_matrix N (by omega) G
      (by simpa only [Fintype.card_fin] using hn)

#print axioms actual_tree_compiled_value
#print axioms public_psd_factory_on_trees
end
end ADComplete.PSDFactory
