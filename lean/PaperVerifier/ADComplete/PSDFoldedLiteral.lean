import PaperVerifier.ADComplete.PSDFoldedFixed
import PaperVerifier.ADComplete.PSDFoldCompiler
import PaperVerifier.CircuitAudit.WrittenPolynomialBridge

/-! The literal integer Horner expression evaluates to the prescribed folded vector. -/

namespace ADComplete.PSDFoldedFrame

open Matrix Polynomial CircuitAudit.Degrees
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def literalTail (xs : List Expr) (a d : Matrix ι ι ℤ) (s : ι → ℤ) :
    Fin xs.length → ι → ℤ := fun j => ((xs.get j).eval a d).mulVec s

theorem expr_eval_ringHom {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a d : R) (p : Expr) : f (p.eval a d) = p.eval (f a) (f d) := by
  induction p <;> simp_all [Expr.eval]

omit [DecidableEq ι] in
theorem castVector_mulVec (a : Matrix ι ι ℤ) (s : ι → ℤ) :
    castVector (a.mulVec s) = (a.map (Int.castRingHom ℝ)).mulVec (castVector s) := by
  ext i
  simp [castVector, Matrix.mulVec, dotProduct]

theorem literal_horner_vector (t j : ℕ) (xs : List Expr)
    (a d : Matrix ι ι ℤ) (s : ι → ℤ) :
    castVector ((CircuitAudit.Degrees.horner
      (.scale ((2 : ℤ)^j*(t : ℤ)) .one) xs).eval a d *ᵥ s) =
      foldedVector s (literalTail xs a d s) t (j+1) := by
  classical
  let b : ℤ := (2 : ℤ)^j*(t : ℤ)
  have hb : (Expr.scale b .one).eval a d = (b : Matrix ι ι ℤ) := by
    simp [Expr.eval, zsmul_eq_mul]
  rw [CircuitAudit.WrittenPolynomialBridge.horner_eval_scalar b a d _ hb xs]
  have hlist : xs.map (Expr.eval a d) =
      List.ofFn (fun i : Fin xs.length => (xs.get i).eval a d) := by
    apply List.ext_getElem
    · simp
    · intro n hn hn'
      simp
  rw [hlist, CircuitAudit.HornerBridge.horner_ofFn,
    CircuitAudit.RadixFactorization.weightedSum]
  rw [foldedVector_succ]
  ext i
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
    castVector, Int.cast_sum, Pi.smul_apply, literalTail]
  apply Finset.sum_congr rfl
  intro k _
  change (((b ^ k.val) • (((xs.get k).eval a d) *ᵥ s)) i : ℝ) =
    (((2 ^ j * t : ℕ) : ℝ) ^ k.val) * (((xs.get k).eval a d *ᵥ s) i : ℝ)
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_pow]
  have hb' : (b : ℝ) = ((2^j*t : ℕ) : ℝ) := by simp [b]
  rw [hb']

theorem literal_fold_vector (t : ℕ) (xs : List Expr)
    (a d : Matrix ι ι ℤ) (s : ι → ℤ) (k : ℕ) :
    castVector ((PSDFoldCompiler.foldExpr t xs k).eval a d *ᵥ s) =
      foldedVector s (literalTail xs a d s) t k := by
  cases k with
  | zero => simp [PSDFoldCompiler.foldExpr, Expr.eval, foldedVector_zero]
  | succ j =>
      simpa only [PSDFoldCompiler.foldExpr, Nat.succ_ne_zero, if_false,
        PSDFoldCompiler.scalar, Nat.add_sub_cancel] using literal_horner_vector t j xs a d s

theorem literal_fold_vector_real (t : ℕ) (xs : List Expr)
    (a d : Matrix ι ι ℤ) (s : ι → ℤ) (k : ℕ) :
    (PSDFoldCompiler.foldExpr t xs k).eval
      (a.map (Int.castRingHom ℝ)) (d.map (Int.castRingHom ℝ)) *ᵥ castVector s =
        foldedVector s (literalTail xs a d s) t k := by
  change (PSDFoldCompiler.foldExpr t xs k).eval
    ((Int.castRingHom ℝ).mapMatrix a) ((Int.castRingHom ℝ).mapMatrix d) *ᵥ castVector s = _
  rw [← expr_eval_ringHom ((Int.castRingHom ℝ).mapMatrix) a d]
  change ((PSDFoldCompiler.foldExpr t xs k).eval a d).map (Int.castRingHom ℝ) *ᵥ castVector s = _
  rw [← castVector_mulVec]
  exact literal_fold_vector t xs a d s k

#print axioms literal_fold_vector_real

end
end ADComplete.PSDFoldedFrame
