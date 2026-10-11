import PaperVerifier.ADComplete.PSDFoldedLiteral
import PaperVerifier.ADComplete.PSDFoldedRepresentative
import PaperVerifier.ADComplete.FinalTreeSeparation

/-! The original integer graph inputs satisfy every folded-frame hypothesis. -/
namespace ADComplete.PSDFoldedFrame
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix CircuitAudit.Degrees
open scoped BigOperators Matrix.Norms.Operator NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem probeList_cons_one (N k : ℕ) (hk : 1 ≤ k) :
    probeList N k = .one :: (probeList N k).drop 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k = 0
    · subst k
      simp [probeList, CircuitAudit.Degrees.row, probe, List.ofFn_succ]
    · rw [probeList, ih (by omega)]
      simp

def graphTail (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin ((probeList N N).drop 1).length → V → ℤ :=
  literalTail ((probeList N N).drop 1) (G.adjMatrix ℤ) (G.degMatrix ℤ) (fun _ => 1)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem castVector_one : castVector (fun _ : V => (1 : ℤ)) = (fun _ => 1) := by
  ext i
  change ((1 : ℤ) : ℝ) = 1
  exact Int.cast_one

theorem graph_expr_cast (G : SimpleGraph V) [DecidableRel G.Adj] (p : Expr) :
    castVector (p.eval (G.adjMatrix ℤ) (G.degMatrix ℤ) *ᵥ (fun _ => 1)) =
      p.eval (G.adjMatrix ℝ) (G.degMatrix ℝ) *ᵥ (fun _ => 1) := by
  rw [castVector_mulVec]
  change MatrixSemantics.realMatrix (p.eval (G.adjMatrix ℤ) (G.degMatrix ℤ)) *ᵥ
    castVector (fun _ => 1) = _
  rw [MatrixSemantics.realMatrix_eval, MatrixSemantics.realMatrix_adjacency,
    MatrixSemantics.realMatrix_degree]
  rw [castVector_one]

theorem graph_source_module (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ N) :
    sourceModule (fun _ => (1 : ℤ)) (graphTail N G) =
      Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z (rfl | ⟨a, rfl⟩)
    · change castVector (fun _ : V => (1 : ℤ)) ∈
        Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1)
      rw [castVector_one]
      exact Spanning.seed_mem (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1)
    · change castVector (((((probeList N N).drop 1).get a).eval
        (G.adjMatrix ℤ) (G.degMatrix ℤ)) *ᵥ (fun _ => 1)) ∈ _
      rw [graph_expr_cast]
      have hp := List.mem_of_mem_drop (List.get_mem ((probeList N N).drop 1) a)
      obtain ⟨k, _, j, _, he⟩ := (FrameSemantics.probeList_members N N _).mp hp
      rw [he, FrameSemantics.probe_eval_mulVec]
      exact Spanning.probeVector_mem_jointModule _ _ _ _ k j
  · rw [← FinalTreeSeparation.actual_graph_probe_spanning N hN G hn]
    apply Submodule.span_le.mpr
    rintro z ⟨k, hk, j, hj, rfl⟩
    have hp : probe N k j ∈ probeList N N :=
      (FrameSemantics.probeList_members N N _).mpr ⟨k, hk, j, hj, rfl⟩
    rw [probeList_cons_one N N hN] at hp
    rcases List.mem_cons.mp hp with he | ht
    · rw [← FrameSemantics.probe_eval_mulVec, he]
      rw [Expr.eval, Matrix.one_mulVec]
      change (fun _ : V => (1 : ℝ)) ∈ sourceModule (fun _ : V => (1 : ℤ)) (graphTail N G)
      rw [← castVector_one]
      exact Submodule.subset_span (Set.mem_insert _ _)
    · obtain ⟨a, ha⟩ := List.mem_iff_get.mp ht
      have hmem : castVector (graphTail N G a) ∈ sourceModule
          (fun _ : V => (1 : ℤ)) (graphTail N G) := Submodule.subset_span (Set.mem_insert_of_mem
        (castVector (fun _ : V => (1 : ℤ)))
        (show castVector (graphTail N G a) ∈ Set.range (fun i => castVector (graphTail N G i))
          from ⟨a, rfl⟩))
      change castVector (((((probeList N N).drop 1).get a).eval
        (G.adjMatrix ℤ) (G.degMatrix ℤ)) *ᵥ (fun _ => 1)) ∈ _ at hmem
      rw [graph_expr_cast, ha, FrameSemantics.probe_eval_mulVec] at hmem
      exact hmem

theorem graph_tail_bound (N : ℕ) (hN : 1 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ N)
    (a : Fin ((probeList N N).drop 1).length) (i : V) :
    ‖graphTail N G a i‖ ≤ (IntegerBounds.RNat N : ℝ) := by
  let : Nonempty V := ⟨i⟩
  let p := ((probeList N N).drop 1).get a
  have hp : p ∈ probeList N N :=
    List.mem_of_mem_drop (List.get_mem ((probeList N N).drop 1) a)
  have hb := (IntegerBounds.probe_norm_uniform N hN (G.adjMatrix ℤ) (G.degMatrix ℤ)
    (IntegerBounds.adjacency_norm_bound G N hn) (IntegerBounds.degree_norm_bound G N hn)
    p hp).1
  calc
    ‖graphTail N G a i‖ = ‖∑ j, (p.eval (G.adjMatrix ℤ) (G.degMatrix ℤ)) i j‖ := by
      simp [graphTail, literalTail, p, Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, ‖(p.eval (G.adjMatrix ℤ) (G.degMatrix ℤ)) i j‖ := norm_sum_le _ _
    _ ≤ ‖p.eval (G.adjMatrix ℤ) (G.degMatrix ℤ)‖ := IntegerBounds.row_abs_sum_le_opNorm _ i
    _ ≤ (IntegerBounds.RNat N : ℝ) := hb

theorem graph_tail_length (N : ℕ) :
    ((probeList N N).drop 1).length = N*(N+1)/2-1 := by
  simp [probeList_length]

theorem graph_tail_nonempty (N : ℕ) (hN : 2 ≤ N) :
    1 ≤ ((probeList N N).drop 1).length := by
  rw [List.length_drop]
  have h := probeList_twice_length N N
  have hp : 6 ≤ N*(N+1) := by nlinarith
  omega

theorem RNat_pos (N : ℕ) (hN : 1 ≤ N) : 1 ≤ IntegerBounds.RNat N := by
  unfold IntegerBounds.RNat IntegerBounds.LNat
  have hp : 1 ≤ N^3 := one_le_pow₀ hN
  exact one_le_pow₀ (by omega : 1 ≤ 3*N^3)

def graphFoldedMatrix (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  foldedPrincipalMatrix N ((probeList N N).drop 1).length (IntegerBounds.RNat N)
    (fun _ => 1) (graphTail N G) (Fintype.card V : ℝ)

theorem graph_folded_matrix (N : ℕ) (hN : 2 ≤ N)
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hn : Fintype.card V ≤ N) :
    (graphFoldedMatrix N G).PosSemidef ∧
      LinearMap.range (graphFoldedMatrix N G).mulVecLin =
        Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) ∧
      Submodule.span ℝ (Set.range (fun k : Fin N =>
        ((graphFoldedMatrix N G)^k.val).mulVec (fun _ => 1))) =
        Spanning.jointModule (G.adjMatrix ℝ) (G.degMatrix ℝ) (fun _ => 1) := by
  have hs : castVector (fun _ : V => (1 : ℤ)) ≠ 0 := by
    intro he
    obtain ⟨i⟩ := ‹Nonempty V›
    have h := congrFun he i
    norm_num [castVector] at h
  have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hh := fixed_folded_principal_matrix N ((probeList N N).drop 1).length
    (IntegerBounds.RNat N) (fun _ : V => 1) (graphTail N G) (Fintype.card V : ℝ)
    hN (graph_tail_nonempty N hN) (RNat_pos N (by omega)) hn hs
    (by intro i; norm_num) (graph_tail_bound N (by omega) G hn) hc
  dsimp only at hh
  rw [graph_source_module N (by omega) G hn] at hh
  simpa only [graphFoldedMatrix, castVector_one] using hh

#print axioms graph_source_module
#print axioms graph_tail_bound
#print axioms graph_folded_matrix
end
end ADComplete.PSDFoldedFrame
