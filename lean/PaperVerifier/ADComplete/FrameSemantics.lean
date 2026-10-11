import PaperVerifier.ADComplete.Spanning
import PaperVerifier.PrincipalMomentAudit.GraphSemantics
import PaperVerifier.CircuitAudit.Degrees

/-!
# Literal frame and principal-module semantics

This module identifies the compiler's integer-coefficient probe expressions
with the stated vector recurrence, and transports the literal joint word span
to the Euclidean principal module. It makes no spanning assertion by assumption.
-/

namespace ADComplete.FrameSemantics
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix PrincipalMomentAudit CircuitAudit.Degrees

variable {V : Type*} [Fintype V] [DecidableEq V]

def generators (H K : Matrix V V ℝ) (b : Bool) :
    Module.End ℝ (EuclideanSpace ℝ V) :=
  (if b then K else H).toEuclideanLin

def lift : (V → ℝ) →ₗ[ℝ] EuclideanSpace ℝ V :=
  (WithLp.linearEquiv 2 ℝ (V → ℝ)).symm.toLinearMap

omit [Fintype V] [DecidableEq V] in
@[simp] theorem lift_apply (x : V → ℝ) : lift x = WithLp.toLp 2 x := rfl

theorem wordEval_eq_wordVector (H K : Matrix V V ℝ) (v : V → ℝ) (w : Word) :
    wordEval (generators H K) w (WithLp.toLp 2 v) =
      WithLp.toLp 2 (Spanning.wordVector H K v w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      rw [wordEval_cons, ih]
      cases b <;> rfl

theorem principal_eq_jointModule_map (H K : Matrix V V ℝ) (v : V → ℝ) :
    principal (generators H K) (WithLp.toLp 2 v) =
      (Spanning.jointModule H K v).map lift := by
  rw [principal_eq_span, Spanning.jointModule, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨Spanning.wordVector H K v w, ⟨w, rfl⟩,
      (wordEval_eq_wordVector H K v w).symm⟩
  · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, wordEval_eq_wordVector H K v w⟩

theorem probe_eval_outside {R : Type*} [Ring R] (N : ℕ) (H K : R)
    (k j : ℕ) (hj : k < j) : (probe N k j).eval H K = 0 := by
  induction k generalizing j with
  | zero => simp [probe, Expr.eval, show j ≠ 0 by omega]
  | succ k ih =>
      simp [probe, show ¬ j ≤ k by omega, show 0 < j by omega,
        Expr.eval, ih (j - 1) (by omega)]

theorem probe_eval_mulVec (N k j : ℕ) (H K : Matrix V V ℝ) (v : V → ℝ) :
    (probe N k j).eval H K *ᵥ v = Spanning.probeVector ((N : ℝ)^2) H K v k j := by
  induction k generalizing j with
  | zero => by_cases hj : j = 0 <;> simp [probe, Expr.eval, Spanning.probeVector, hj]
  | succ k ih =>
      have hleft :
          (if j ≤ k then
            (Expr.mul (Expr.add Expr.d
              (Expr.scale ((N : ℤ)^2 * ((j : ℤ) - k)) Expr.one))
              (probe N k j)) else Expr.zero).eval H K *ᵥ v =
          K *ᵥ Spanning.probeVector ((N : ℝ)^2) H K v k j +
            ((N : ℝ)^2 * ((j : ℝ) - k)) •
              Spanning.probeVector ((N : ℝ)^2) H K v k j := by
        by_cases hj : j ≤ k
        · simp only [hj, if_true, Expr.eval, ← Matrix.mulVec_mulVec,
            Matrix.add_mulVec, ← Int.cast_smul_eq_zsmul ℝ,
            Matrix.smul_mulVec, Matrix.one_mulVec, ih]
          push_cast
          rfl
        · have hz := Spanning.probeVector_outside ((N : ℝ)^2) H K v k j (by omega)
          simp [hj, Expr.eval, hz]
      have hright :
          (if 0 < j then
            (Expr.scale ((N : ℤ)^2) (Expr.mul Expr.a (probe N k (j - 1))))
          else Expr.zero).eval H K *ᵥ v =
          (N : ℝ)^2 • H.mulVec
            (if j = 0 then 0 else Spanning.probeVector ((N : ℝ)^2) H K v k (j - 1)) := by
        by_cases hj : j = 0
        · simp [hj, Expr.eval]
        · simp only [show 0 < j by omega, if_true, Expr.eval,
            ← Int.cast_smul_eq_zsmul ℝ, Matrix.smul_mulVec,
            ← Matrix.mulVec_mulVec, ih, hj, if_false]
          push_cast
          rfl
      change ((_ + _) : Matrix V V ℝ) *ᵥ v = _
      rw [Matrix.add_mulVec, hleft, hright]
      rfl

theorem probeList_members (N n : ℕ) (p : Expr) :
    p ∈ probeList N n ↔ ∃ k < n, ∃ j ≤ k, p = probe N k j := by
  induction n with
  | zero => simp [probeList]
  | succ n ih =>
      simp only [probeList, List.mem_append, ih, CircuitAudit.Degrees.row, List.mem_ofFn]
      constructor
      · rintro (⟨k, hk, j, hj, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨k, by omega, j, hj, rfl⟩
        · exact ⟨n, by omega, j, by omega, rfl⟩
      · rintro ⟨k, hk, j, hj, rfl⟩
        by_cases hkn : k < n
        · exact Or.inl ⟨k, hkn, j, hj, rfl⟩
        · have hke : k = n := by omega
          subst k
          exact Or.inr ⟨⟨j, by omega⟩, rfl⟩

def probeMatrices (N : ℕ) (H K : Matrix V V ℝ) :
    Fin (probeList N N).length → Matrix V V ℝ :=
  fun i => ((probeList N N).get i).eval H K

def probeFrame (N : ℕ) (H K : Matrix V V ℝ) (v : V → ℝ) :
    Fin (probeList N N).length → EuclideanSpace ℝ V :=
  fun i => WithLp.toLp 2 (probeMatrices N H K i *ᵥ v)

theorem probeFrame_span (N : ℕ) (H K : Matrix V V ℝ) (v : V → ℝ) :
    Submodule.span ℝ (Set.range (probeFrame N H K v)) =
      (Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
        z = Spanning.probeVector ((N : ℝ)^2) H K v k j}).map lift := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨k, hk, j, hj, heq⟩ := (probeList_members N N _).mp
      (List.get_mem (probeList N N) i)
    refine ⟨Spanning.probeVector ((N : ℝ)^2) H K v k j, ⟨k, hk, j, hj, rfl⟩, ?_⟩
    simp only [probeFrame, probeMatrices, heq, probe_eval_mulVec, lift_apply]
  · rintro ⟨z, ⟨k, hk, j, hj, rfl⟩, rfl⟩
    have hp : probe N k j ∈ probeList N N :=
      (probeList_members N N _).mpr ⟨k, hk, j, hj, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    refine ⟨i, ?_⟩
    simp only [probeFrame, probeMatrices, hi, probe_eval_mulVec, lift_apply]

theorem probeFrame_range_eq_principal (N : ℕ) (H K : Matrix V V ℝ) (v : V → ℝ)
    (hspan : Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k,
        z = Spanning.probeVector ((N : ℝ)^2) H K v k j} = Spanning.jointModule H K v) :
    LinearMap.range (combination (probeFrame N H K v)) =
      principal (generators H K) (WithLp.toLp 2 v) := by
  rw [Finsupp.range_linearCombination, probeFrame_span, hspan,
    principal_eq_jointModule_map]

#print axioms probe_eval_mulVec
#print axioms probeFrame_span
#print axioms probeFrame_range_eq_principal
end
end ADComplete.FrameSemantics
