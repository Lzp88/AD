import PaperVerifier.ADComplete.FrobeniusGraphProbes

/-! Three actual Frobenius trace tables determine every full-representation word trace. -/

namespace ADComplete.Frobenius

open Matrix CircuitAudit.Degrees PrincipalMomentAudit
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem full_three_trace_tables_determine_word_traces (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hnG : Fintype.card V ≤ N) (hnH : Fintype.card W ≤ N)
    (hGram : ∀ i j : Fin (probeList (N^2) (N^2)).length,
      ((FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i).transpose *
        FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) j).trace =
      ((FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) i).transpose *
        FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) j).trace)
    (hGen : ∀ b i j,
      ((FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i).transpose *
        (GraphSemantics.generatorMatrix G b *
          FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) j)).trace =
      ((FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) i).transpose *
        (GraphSemantics.generatorMatrix H b *
          FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) j)).trace) :
    ∀ w, (matrixWord (G.adjMatrix ℝ) (G.degMatrix ℝ) w).trace =
      (matrixWord (H.adjMatrix ℝ) (H.degMatrix ℝ) w).trace := by
  classical
  have hone : Expr.one ∈ probeList (N^2) (N^2) := by
    apply (FrameSemantics.probeList_members (N^2) (N^2) .one).mpr
    exact ⟨0, by nlinarith, 0, by omega, by simp [probe]⟩
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hone
  have hseedG : fullFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ) i₀ =
      WithLp.toLp 2 (flatten (1 : Matrix V V ℝ)) := by
    rw [fullFrame_apply]
    simp only [FrameSemantics.probeMatrices, hi₀, Expr.eval]
  have hseedH : fullFrame N (H.adjMatrix ℝ) (H.degMatrix ℝ) i₀ =
      WithLp.toLp 2 (flatten (1 : Matrix W W ℝ)) := by
    rw [fullFrame_apply]
    simp only [FrameSemantics.probeMatrices, hi₀, Expr.eval]
  have hg : ∀ i j, ⟪fullFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ) i,
      fullFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ) j⟫_ℝ =
      ⟪fullFrame N (H.adjMatrix ℝ) (H.degMatrix ℝ) i,
        fullFrame N (H.adjMatrix ℝ) (H.degMatrix ℝ) j⟫_ℝ := by
    intro i j
    rw [fullFrame_apply, fullFrame_apply, fullFrame_apply, fullFrame_apply,
      inner_flatten, inner_flatten]
    exact hGram i j
  have ht : ∀ b i j,
      ⟪fullFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ) i,
        FrameSemantics.generators (leftMatrix (G.adjMatrix ℝ))
          (leftMatrix (G.degMatrix ℝ)) b
          (fullFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ) j)⟫_ℝ =
      ⟪fullFrame N (H.adjMatrix ℝ) (H.degMatrix ℝ) i,
        FrameSemantics.generators (leftMatrix (H.adjMatrix ℝ))
          (leftMatrix (H.degMatrix ℝ)) b
          (fullFrame N (H.adjMatrix ℝ) (H.degMatrix ℝ) j)⟫_ℝ := by
    intro b i j
    rw [fullFrame_apply, fullFrame_apply, fullFrame_apply, fullFrame_apply]
    cases b
    · simp only [FrameSemantics.generators, Bool.false_eq_true, if_false,
        Matrix.toLpLin_toLp]
      change ⟪WithLp.toLp 2 (flatten (FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i)),
          WithLp.toLp 2 ((leftMatrix (G.adjMatrix ℝ)).mulVec
            (flatten (FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) j)))⟫_ℝ =
        ⟪WithLp.toLp 2 (flatten (FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) i)),
          WithLp.toLp 2 ((leftMatrix (H.adjMatrix ℝ)).mulVec
            (flatten (FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) j)))⟫_ℝ
      rw [leftMatrix_mulVec, leftMatrix_mulVec, inner_flatten, inner_flatten]
      exact hGen false i j
    · simp only [FrameSemantics.generators, if_true, Matrix.toLpLin_toLp]
      change ⟪WithLp.toLp 2 (flatten (FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) i)),
          WithLp.toLp 2 ((leftMatrix (G.degMatrix ℝ)).mulVec
            (flatten (FrameSemantics.probeMatrices (N^2) (G.adjMatrix ℝ) (G.degMatrix ℝ) j)))⟫_ℝ =
        ⟪WithLp.toLp 2 (flatten (FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) i)),
          WithLp.toLp 2 ((leftMatrix (H.degMatrix ℝ)).mulVec
            (flatten (FrameSemantics.probeMatrices (N^2) (H.adjMatrix ℝ) (H.degMatrix ℝ) j)))⟫_ℝ
      rw [leftMatrix_mulVec, leftMatrix_mulVec, inner_flatten, inner_flatten]
      exact hGen true i j
  have hm := GramTables.frame_three_tables_determine_moments
    (FrameSemantics.generators (leftMatrix (G.adjMatrix ℝ)) (leftMatrix (G.degMatrix ℝ)))
    (FrameSemantics.generators (leftMatrix (H.adjMatrix ℝ)) (leftMatrix (H.degMatrix ℝ)))
    (WithLp.toLp 2 (flatten (1 : Matrix V V ℝ)))
    (WithLp.toLp 2 (flatten (1 : Matrix W W ℝ)))
    (fullFrame N (G.adjMatrix ℝ) (G.degMatrix ℝ))
    (fullFrame N (H.adjMatrix ℝ) (H.degMatrix ℝ))
    (actual_full_frame_range N hN G hnG) (actual_full_frame_range N hN H hnH)
    hg ht i₀ hseedG hseedH
  intro w
  simpa only [moment_trace] using hm w

#print axioms full_three_trace_tables_determine_word_traces

end
end ADComplete.Frobenius
