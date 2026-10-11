import Mathlib

/-!
Faithful algebraic transport for arXiv:2607.21494v1, Sections 3--5.
This module proves naturality of the *same* finite expressions under an
intertwiner. It does not assume, or assert, that tree coordinate projections
have already been recovered. That combinatorial bridge must be proved separately.
-/

namespace PrincipalMomentAudit.Transport

inductive Expression where
  | scalar (c : ℝ)
  | adjacency
  | degree
  | add (p q : Expression)
  | mul (p q : Expression)

def Expression.eval {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A D : Module.End ℝ E) : Expression → Module.End ℝ E
  | .scalar c => c • 1
  | .adjacency => A
  | .degree => D
  | .add p q => p.eval A D + q.eval A D
  | .mul p q => p.eval A D * q.eval A D

def Intertwines {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F)
    (P : Module.End ℝ E) (Q : Module.End ℝ F) : Prop :=
  ∀ x, L (P x) = Q (L x)

theorem expression_transport {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F)
    (A D : Module.End ℝ E) (A' D' : Module.End ℝ F)
    (hA : Intertwines L A A') (hD : Intertwines L D D')
    (p : Expression) : Intertwines L (p.eval A D) (p.eval A' D') := by
  induction p with
  | scalar c => intro x; simp [Expression.eval]
  | adjacency => exact hA
  | degree => exact hD
  | add p q hp hq =>
      intro x
      simp only [Expression.eval, LinearMap.add_apply, map_add]
      rw [hp x, hq x]
  | mul p q hp hq =>
      intro x
      simp only [Expression.eval, Module.End.mul_apply]
      rw [hp, hq]

def Expression.one : Expression := .scalar 1
def Expression.neg (p : Expression) : Expression := .mul (.scalar (-1)) p
def Expression.sub (p q : Expression) : Expression := .add p q.neg

def Expression.listProduct : List Expression → Expression
  | [] => .one
  | p :: ps => .mul p (Expression.listProduct ps)

/-- Exactly the paper's common level-selector polynomial, applied to an expression.
The index bound N must be shared by both represented pairs. -/
noncomputable def levelSelector (N k : ℕ) (p : Expression) : Expression :=
  Expression.listProduct (((List.range (N + 1)).filter (fun r => r ≠ k)).map
    (fun r => .mul (.scalar (((k : ℝ) - (r : ℝ))⁻¹))
      (p.sub (.scalar (r : ℝ)))))

theorem levelSelector_transport {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (A D : Module.End ℝ E) (A' D' : Module.End ℝ F)
    (hA : Intertwines L A A') (hD : Intertwines L D D')
    (N k : ℕ) (p : Expression) :
    Intertwines L ((levelSelector N k p).eval A D)
      ((levelSelector N k p).eval A' D') :=
  expression_transport L A D A' D' hA hD _

/-- The guarded pruning adjacency update is transported with the same peel selector. -/
theorem pruning_adjacency_transport {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (A D : Module.End ℝ E) (A' D' : Module.End ℝ F)
    (hA : Intertwines L A A') (hD : Intertwines L D D')
    (currentA peel : Expression) :
    Intertwines L
      ((Expression.mul (Expression.mul (Expression.one.sub peel) currentA)
        (Expression.one.sub peel)).eval A D)
      ((Expression.mul (Expression.mul (Expression.one.sub peel) currentA)
        (Expression.one.sub peel)).eval A' D') :=
  expression_transport L A D A' D' hA hD _

/-- Scalar version of exactly the same Lagrange selector in Section 3.2. -/
noncomputable def scalarSelector (N k : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ (Finset.range (N + 1)).erase k, (x - (r : ℝ)) / ((k : ℝ) - (r : ℝ))

theorem scalarSelector_self (N k : ℕ) : scalarSelector N k (k : ℝ) = 1 := by
  unfold scalarSelector
  apply Finset.prod_eq_one
  intro r hr
  have hrk : r ≠ k := (Finset.mem_erase.mp hr).1
  have hcast : (k : ℝ) ≠ (r : ℝ) := by exact_mod_cast Ne.symm hrk
  exact div_self (sub_ne_zero.mpr hcast)

theorem scalarSelector_other (N k j : ℕ) (hj : j ≤ N) (hjk : j ≠ k) :
    scalarSelector N k (j : ℝ) = 0 := by
  unfold scalarSelector
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk, Finset.mem_range.mpr (by omega)⟩)
  simp

theorem scalarSelector_integer (N k j : ℕ) (hj : j ≤ N) :
    scalarSelector N k (j : ℝ) = if j = k then 1 else 0 := by
  by_cases h : j = k
  · subst j
    simp [scalarSelector_self]
  · simp [h, scalarSelector_other N k j hj h]

/-- Seed preservation follows from transport, with no appeal to coordinates. -/
theorem seed_expression_transport {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (A D : Module.End ℝ E) (A' D' : Module.End ℝ F)
    (hA : Intertwines L A A') (hD : Intertwines L D D')
    (e : E) (f : F) (he : L e = f) (p : Expression) :
    L (p.eval A D e) = p.eval A' D' f := by
  rw [expression_transport L A D A' D' hA hD p e, he]

#print axioms expression_transport
#print axioms levelSelector_transport
#print axioms pruning_adjacency_transport
#print axioms scalarSelector_integer
#print axioms seed_expression_transport

end PrincipalMomentAudit.Transport
