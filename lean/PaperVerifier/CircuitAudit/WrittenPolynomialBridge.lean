import PaperVerifier.CircuitAudit.Degrees
import PaperVerifier.CircuitAudit.HornerBridge

namespace CircuitAudit.WrittenPolynomialBridge

open Degrees RadixFactorization

variable {R : Type*} [Ring R]

theorem horner_eval_scalar (b : ℤ) (a d : R) (base : Expr)
    (hb : base.eval a d = (b : R)) (ps : List Expr) :
    (Degrees.horner base ps).eval a d = HornerBridge.horner b (ps.map (Expr.eval a d)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [Degrees.horner, Expr.eval, hb, ih, List.map_cons, HornerBridge.horner]
    simp only [zsmul_eq_mul]

theorem scalar_powers_eval (b : ℤ) (a d : R) (M : ℕ) :
    (power (power (.scale b .one) M) M).eval a d = ((b ^ (M^2) : ℤ) : R) := by
  simp [power_eval, Expr.eval, zsmul_eq_mul, ← pow_mul, pow_two]

variable [StarRing R]

/-- The exact evaluated factored AST is the literal original radix polynomial.
No graph hypothesis or self-adjointness of J or the probes is used. -/
theorem factored_eq_source (b : ℤ) (a d : R) (ha : star a = a) (hd : star d = d)
    (J : Expr) (ps : List Expr) :
    (factored b J ps).eval a d =
      sourcePolynomial b (J.eval a d) (ps.map (Expr.eval a d)).get (coreSlots a d) := by
  let M := ps.length
  let base : Expr := .scale b .one
  let beta := power base M
  let gamma := power beta M
  let Y := Degrees.horner base ps
  let Z := Degrees.horner beta ps
  let S : Expr := .add (.add .one (.mul gamma .a)) (.mul (.mul gamma gamma) .d)
  let q : Expr := .mul (.mul (.mul J Z.reverse) S) Y
  let xs := ps.map (Expr.eval a d)
  have hb : base.eval a d = (b : R) := by simp [base, Expr.eval, zsmul_eq_mul]
  have hbeta : beta.eval a d = ((b^M : ℤ) : R) := by
    simp [beta, power_eval, hb]
  have hgamma : gamma.eval a d = ((b^(M^2) : ℤ) : R) :=
    scalar_powers_eval b a d M
  have hY : Y.eval a d = weightedSum b (fun i : Fin xs.length => i.val) xs.get := by
    rw [horner_eval_scalar b a d base hb ps, HornerBridge.horner_list]
  have hZ : Z.eval a d = weightedSum b (fun i : Fin xs.length => i.val * xs.length) xs.get := by
    rw [horner_eval_scalar (b^M) a d beta hbeta ps, HornerBridge.horner_list_stride]
    simp only [xs, List.length_map, M]
  have hS : S.eval a d = 1 + b^(xs.length^2) • a + b^(2*xs.length^2) • d := by
    simp only [S, Expr.eval, hgamma]
    simp only [zsmul_eq_mul, Int.cast_pow, xs, List.length_map, ← pow_add,
      ← two_mul, M]
  change (q.eval a d + q.reverse.eval a d) = _
  rw [reverse_eval a d ha hd q]
  simp only [q, Expr.eval, reverse_eval a d ha hd Z, hS, hY, hZ]
  rw [exact_source_factorization b (J.eval a d) xs.get a d ha hd]
  simp only [star_mul, star_add, star_one, star_zsmul, ha, hd, star_star, mul_assoc]

#print axioms factored_eq_source

end CircuitAudit.WrittenPolynomialBridge
