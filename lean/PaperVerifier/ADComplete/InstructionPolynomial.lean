import PaperVerifier.ADComplete.InstructionSharpBits

/-! The public polynomial is the literal forward output of the public
instruction compiler in the integer free algebra. Its N=1 branch is I. -/
namespace ADComplete.InstructionDegrees
open CircuitAudit.CircuitCosts CircuitAudit.Degrees CircuitAudit.RadixFactorization

def polynomial (N : ℕ) (b : ℤ) : IntegerNCPolynomial :=
  ((compiled N b).2.value (compiled N b).1 adjacencyGenerator degreeGenerator).1

def writtenPolynomial (N : ℕ) (b : ℤ) : IntegerNCPolynomial :=
  if N=1 then 1 else
    sourcePolynomial b ((allOnes N).eval adjacencyGenerator degreeGenerator)
      ((probeList N N).map (Expr.eval adjacencyGenerator degreeGenerator)).get
      (coreSlots adjacencyGenerator degreeGenerator)

theorem literal_polynomial_eq_written (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    polynomial N b = writtenPolynomial N b := by
  by_cases he : N=1
  · subst N
    simp only [polynomial, writtenPolynomial, ite_true, compiled_one_value]
  · simp only [polynomial, writtenPolynomial, if_neg he, compiled]
    exact CircuitAudit.FullCompression.full_output_integer_polynomial N hN b

theorem sourcePolynomial_self_adjoint {R : Type*} [Ring R] [StarRing R]
    {M : ℕ} (b : ℤ) (J : R) (U : Fin M → R) (S : Fin 3 → R) :
    star (sourcePolynomial b J U S) = sourcePolynomial b J U S := by
  simp only [sourcePolynomial, star_sum, star_zsmul, star_add, star_mul, star_star, add_comm]

theorem literal_polynomial_self_adjoint (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    star (polynomial N b) = polynomial N b := by
  rw [literal_polynomial_eq_written N hN b]
  unfold writtenPolynomial
  split
  · exact star_one _
  · exact sourcePolynomial_self_adjoint _ _ _ _

theorem polynomial_one (b : ℤ) : polynomial 1 b=1 := by
  simpa only [polynomial] using congrArg Prod.fst (compiled_one_value b adjacencyGenerator degreeGenerator)

theorem expression_eval_hom {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (a d : R) (p : Expr) :
    φ (p.eval a d) = p.eval (φ a) (φ d) := by
  induction p with
  | zero => exact φ.map_zero
  | one => exact φ.map_one
  | a => rfl
  | d => rfl
  | scale k p ih => simp only [Expr.eval, map_zsmul, ih]
  | add p q ihp ihq => simp only [Expr.eval, map_add, ihp, ihq]
  | mul p q ihp ihq => simp only [Expr.eval, map_mul, ihp, ihq]

theorem literal_register_hom {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (a d : R) (c : Circuit) (i : ℕ) :
    φ (c.value a d i) = c.value (φ a) (φ d) i := by
  rw [← expression_register_value a d, ← expression_register_value (φ a) (φ d)]
  exact expression_eval_hom φ a d _

theorem polynomial_evaluation {R : Type*} [Ring R] [Algebra ℤ R] (a d : R)
    (N : ℕ) (b : ℤ) :
    (FreeAlgebra.lift ℤ (fun x : Bool => if x then d else a)) (polynomial N b) =
      ((compiled N b).2.value (compiled N b).1 a d).1 := by
  let φ := FreeAlgebra.lift ℤ (fun x : Bool => if x then d else a)
  have h := literal_register_hom φ.toRingHom adjacencyGenerator degreeGenerator
    (compiled N b).1 (compiled N b).2.forward
  simpa [φ, polynomial, PairRef.value, adjacencyGenerator, degreeGenerator] using h

#print axioms literal_polynomial_self_adjoint
#print axioms polynomial_evaluation
end ADComplete.InstructionDegrees
