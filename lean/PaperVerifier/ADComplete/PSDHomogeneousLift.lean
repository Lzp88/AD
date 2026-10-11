import Mathlib

/-! Positive homogeneous corner lifting. This is not a unital map: the
matrix unit is never replaced by J. The exponent records auxiliary degree. -/
namespace ADComplete.PSDHomogeneousLift
universe u

def J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

theorem J_mul_J (n : ℕ) : J n * J n = (n : ℝ) • J n := by
  ext i j
  simp [Matrix.mul_apply, J]

theorem scaled_mul (n : ℕ) (f g : ℝ) :
    (f • J n) * (g • J n) = ((n : ℝ)*f*g) • J n := by
  ext i j
  simp [Matrix.mul_apply, J]
  ring

inductive HExpr (ι : Type u) : ℕ → Type u where
  | input (i : ι) : HExpr ι 0
  | zero (q : ℕ) : HExpr ι q
  | scale {q : ℕ} (c : ℤ) (p : HExpr ι q) : HExpr ι q
  | add {q : ℕ} (p r : HExpr ι q) : HExpr ι q
  | mul {p q : ℕ} (f : HExpr ι p) (g : HExpr ι q) : HExpr ι (p+q+1)

def HExpr.scalar {ι : Type*} (g : ι → ℝ) : {q : ℕ} → HExpr ι q → ℝ
  | _, .input i => g i
  | _, .zero _ => 0
  | _, .scale c p => c • p.scalar g
  | _, .add p r => p.scalar g + r.scalar g
  | _, .mul p r => p.scalar g * r.scalar g

def HExpr.matrix {ι : Type*} (n : ℕ) (B : ι → Matrix (Fin n) (Fin n) ℝ) :
    {q : ℕ} → HExpr ι q → Matrix (Fin n) (Fin n) ℝ
  | _, .input i => B i
  | _, .zero _ => 0
  | _, .scale c p => c • p.matrix n B
  | _, .add p r => p.matrix n B + r.matrix n B
  | _, .mul p r => p.matrix n B * r.matrix n B

/-- q indexes degree minus one; the actual scalar degree is q+1. -/
theorem homogeneous_lift {ι : Type*} {q : ℕ} (p : HExpr ι q)
    (n : ℕ) (g : ι → ℝ) :
    p.matrix n (fun i => g i • J n) = ((n : ℝ)^q * p.scalar g) • J n := by
  induction p with
  | input i => simp [HExpr.matrix, HExpr.scalar]
  | zero q => simp [HExpr.matrix, HExpr.scalar]
  | scale c p ih =>
    rw [HExpr.matrix, HExpr.scalar, ih]
    ext i j
    simp [J, zsmul_eq_mul]
    ring
  | add p r ihp ihr =>
    rw [HExpr.matrix, HExpr.scalar, ihp, ihr]
    ext i j
    simp [J]
    ring
  | @mul p q f g ihf ihg =>
    rw [HExpr.matrix, HExpr.scalar, ihf, ihg, scaled_mul]
    congr 1
    rw [pow_add, pow_succ]
    ring

/-- Concrete Gram corner: no entry observation or J/n normalization. -/
theorem gram_corner (n : ℕ) (Zi Zj : Matrix (Fin n) (Fin n) ℝ) :
    J n * Zi.transpose * Zj * J n =
      (dotProduct (fun _ : Fin n => 1)
        (Matrix.mulVec (Zi.transpose * Zj) (fun _ : Fin n => 1))) • J n := by
  rw [Matrix.mul_assoc (J n) Zi.transpose Zj]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, J,
    one_mul, mul_one, Matrix.mulVec, dotProduct]
  exact Finset.sum_comm

#print axioms homogeneous_lift
#print axioms J_mul_J
end ADComplete.PSDHomogeneousLift
