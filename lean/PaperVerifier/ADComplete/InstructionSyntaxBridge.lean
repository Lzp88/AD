import PaperVerifier.ADComplete.InstructionCompressionDegrees

/-! Literal instruction-by-instruction syntax, not an equivalent simplified
output expression. Degree and evaluation interpreters bind every register. -/
namespace ADComplete.InstructionDegrees
open CircuitAudit.CircuitCosts CircuitAudit.Degrees

def gateExpression (es : List Expr) : Gate → Expr
  | .zero => .zero
  | .ident => .one
  | .atomA => .a
  | .atomD => .d
  | .add i j => .add (es.getD i .zero) (es.getD j .zero)
  | .mul i j => .mul (es.getD i .zero) (es.getD j .zero)
  | .scale k i => .scale k (es.getD i .zero)

def expressions : Circuit → List Expr
  | .empty => []
  | .snoc c g => expressions c ++ [gateExpression (expressions c) g]

theorem gate_expression_degree (es : List Expr) (g : Gate) :
    (gateExpression es g).degree = gateDegree (es.map Expr.degree) g := by
  have h (i : ℕ) : (es.getD i .zero).degree = (es.map Expr.degree).getD i 0 :=
    (List.getD_map es Expr.zero Expr.degree).symm
  cases g <;> simp only [gateExpression, gateDegree, Expr.degree, h]

theorem expressions_degrees (c : Circuit) :
    (expressions c).map Expr.degree = degrees c := by
  induction c with
  | empty => rfl
  | snoc c g ih => simp only [expressions, List.map_append, List.map_singleton,
      gate_expression_degree, ih, degrees]

theorem expression_register_degree (c : Circuit) (i : ℕ) :
    ((expressions c).getD i .zero).degree = degree c i := by
  rw [degree, ← expressions_degrees]
  exact (List.getD_map (expressions c) Expr.zero Expr.degree).symm

theorem gate_expression_value {R : Type*} [Ring R] (a d : R) (es : List Expr) (g : Gate) :
    (gateExpression es g).eval a d = g.eval a d (es.map (Expr.eval a d)) := by
  have h (i : ℕ) : (es.getD i .zero).eval a d =
      (es.map (Expr.eval a d)).getD i 0 :=
    (List.getD_map es Expr.zero (Expr.eval a d)).symm
  cases g <;> simp only [gateExpression, Gate.eval, Expr.eval, h]

theorem expressions_values {R : Type*} [Ring R] (a d : R) (c : Circuit) :
    (expressions c).map (Expr.eval a d) = c.eval a d := by
  induction c with
  | empty => rfl
  | snoc c g ih => simp only [expressions, List.map_append, List.map_singleton,
      gate_expression_value, ih, Circuit.eval]

theorem expression_register_value {R : Type*} [Ring R]
    (a d : R) (c : Circuit) (i : ℕ) :
    ((expressions c).getD i .zero).eval a d = c.value a d i := by
  rw [Circuit.value, ← expressions_values a d]
  exact (List.getD_map (expressions c) Expr.zero (Expr.eval a d)).symm

theorem compiled_every_register_syntax (N : ℕ) (hN : 1 ≤ N) (b : ℤ)
    (i : ℕ) (hi : i < (compiled N b).1.length) :
    ((expressions (compiled N b).1).getD i .zero).degree ≤ 3*N-2 := by
  rw [expression_register_degree]
  exact compiled_all_degrees N hN b i hi

#print axioms compiled_every_register_syntax
#print axioms expression_register_value
end ADComplete.InstructionDegrees
