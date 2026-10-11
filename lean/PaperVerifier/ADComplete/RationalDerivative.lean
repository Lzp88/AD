import Mathlib

/-! The actual real rational-function derivation, constructed by localization. -/
namespace ADComplete.RationalDerivative

open Polynomial
open scoped nonZeroDivisors
noncomputable section

abbrev F := RatFunc ℝ
abbrev Jet := TrivSqZeroExt F F

/-- Polynomial value and first derivative as a square-zero algebra map. -/
def polynomialJet : ℝ[X] →ₐ[ℝ] Jet where
  toFun p := (algebraMap ℝ[X] F p, algebraMap ℝ[X] F p.derivative)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · change algebraMap ℝ[X] F (p+q) = algebraMap ℝ[X] F p + algebraMap ℝ[X] F q
      exact map_add _ p q
    · change algebraMap ℝ[X] F (p+q).derivative =
        algebraMap ℝ[X] F p.derivative + algebraMap ℝ[X] F q.derivative
      simp [Polynomial.derivative_add]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · change algebraMap ℝ[X] F (p*q) = algebraMap ℝ[X] F p * algebraMap ℝ[X] F q
      exact map_mul _ p q
    · change algebraMap ℝ[X] F (p*q).derivative =
        algebraMap ℝ[X] F p * algebraMap ℝ[X] F q.derivative +
        algebraMap ℝ[X] F p.derivative * algebraMap ℝ[X] F q
      simp [Polynomial.derivative_mul, mul_comm, add_comm]
  commutes' r := by
    ext
    · change algebraMap ℝ[X] F (algebraMap ℝ ℝ[X] r) = algebraMap ℝ F r
      exact (IsScalarTower.algebraMap_apply ℝ ℝ[X] F r).symm
    · change algebraMap ℝ[X] F (C r).derivative = 0
      simp

theorem polynomialJet_units (p : ℝ[X]⁰) : IsUnit (polynomialJet p) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  exact RatFunc.algebraMap_ne_zero (nonZeroDivisors.ne_zero p.property)

/-- The polynomial jet extends to the field by the universal localization map. -/
def rationalJet : F →ₐ[ℝ] Jet :=
  IsLocalization.liftAlgHom (M := ℝ[X]⁰) (S := F) polynomialJet_units

theorem rationalJet_polynomial (p : ℝ[X]) :
    rationalJet (algebraMap ℝ[X] F p) = polynomialJet p := by
  exact IsLocalization.lift_eq polynomialJet_units p

theorem rationalJet_fst (x : F) : (rationalJet x).fst = x := by
  let f : F →+* F := (TrivSqZeroExt.fstHom ℝ F F).toRingHom.comp rationalJet.toRingHom
  have hf : f = RingHom.id F := by
    apply IsLocalization.ringHom_ext (R := ℝ[X]) (S := F) (M := ℝ[X]⁰)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change (rationalJet (algebraMap ℝ[X] F p)).fst = algebraMap ℝ[X] F p
    rw [rationalJet_polynomial]
    rfl
  exact DFunLike.congr_fun hf x

/-- The second component of the jet is a genuine real derivation. -/
def derivative : Derivation ℝ F F where
  toLinearMap := (TrivSqZeroExt.sndHom F F).restrictScalars ℝ |>.comp rationalJet.toLinearMap
  map_one_eq_zero' := by change (rationalJet 1).snd = 0; simp
  leibniz' x y := by
    change (rationalJet (x*y)).snd = x • (rationalJet y).snd + y • (rationalJet x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, rationalJet_fst, rationalJet_fst]
    simp [smul_eq_mul, mul_comm]

theorem derivative_polynomial (p : ℝ[X]) :
    derivative (algebraMap ℝ[X] F p) = algebraMap ℝ[X] F p.derivative := by
  change (rationalJet (algebraMap ℝ[X] F p)).snd = _
  rw [rationalJet_polynomial]
  rfl

#print axioms derivative_polynomial

end
end ADComplete.RationalDerivative
