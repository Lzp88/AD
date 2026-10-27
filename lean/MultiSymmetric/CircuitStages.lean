import MultiSymmetric.CircuitSynthetic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
set_option autoImplicit false

/-! Literal coefficient-level arithmetic stages. References are free wires;
each other expression constructor is one original-order matrix gate. -/
namespace MultiSymmetric.Circuit
open Polynomial
open scoped BigOperators
noncomputable section

inductive CoeffExpr (ι σ : Type*) where
  | ref : ι → CoeffExpr ι σ
  | constant : ℤ → CoeffExpr ι σ
  | add : CoeffExpr ι σ → CoeffExpr ι σ → CoeffExpr ι σ
  | scale : ℤ → CoeffExpr ι σ → CoeffExpr ι σ
  | leftGenerator : σ → CoeffExpr ι σ → CoeffExpr ι σ

def CoeffExpr.eval {ι σ R : Type*} [Ring R] (input : ι → R) (gen : σ → R) :
    CoeffExpr ι σ → R
  | .ref i => input i
  | .constant c => (c : R)
  | .add a b => a.eval input gen + b.eval input gen
  | .scale c a => (c : R) * a.eval input gen
  | .leftGenerator b a => gen b * a.eval input gen

def CoeffExpr.gates {ι σ : Type*} : CoeffExpr ι σ → ℕ
  | .ref _ => 0
  | .constant _ => 1
  | .add a b => a.gates+b.gates+1
  | .scale _ a => a.gates+1
  | .leftGenerator _ a => a.gates+1

def CoeffExpr.usedScalars {ι σ : Type*} : CoeffExpr ι σ → Finset ℤ
  | .ref _ => ∅
  | .constant c => {c}
  | .add p q => p.usedScalars ∪ q.usedScalars
  | .scale c p => insert c p.usedScalars
  | .leftGenerator _ p => p.usedScalars

def assemble {R : Type*} [Ring R] (L : ℕ) (c : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range L, monomial j (c j)

theorem assemble_coeff {R : Type*} [Ring R] (L : ℕ) (c : ℕ → R) (j : ℕ) :
    (assemble L c).coeff j = if j<L then c j else 0 := by
  classical
  simp [assemble, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, eq_comm]

theorem assemble_eq {R : Type*} [Ring R] (p : R[X]) (L : ℕ)
    (hp : p.natDegree<L) : assemble L p.coeff = p := by
  ext j
  rw [assemble_coeff]
  by_cases hj : j<L
  · simp [hj]
  · simp only [hj, if_false]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_le (Nat.le_of_not_gt hj))).symm

/-- Reading a fixed finite row uses its stored coefficient register, or the
single shared zero register for an index beyond that row. -/
def readStored {R : Type*} [Zero R] (L : ℕ) (v : Fin L → R) (j : ℕ) : R :=
  if h : j<L then v ⟨j,h⟩ else 0

theorem readStored_coeff {R : Type*} [Ring R] (p : R[X]) (L : ℕ)
    (hp : p.natDegree<L) :
    readStored L (fun j => p.coeff j.val) = p.coeff := by
  funext j
  unfold readStored
  split_ifs with hj
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt
      (hp.trans_le (Nat.le_of_not_gt hj))).symm

structure Stage (ι σ : Type*) where
  length : ℕ
  expr : ℕ → CoeffExpr ι σ

def Stage.eval {ι σ R : Type*} [Ring R] (input : ι → R) (gen : σ → R)
    (stage : Stage ι σ) : R[X] :=
  assemble stage.length (fun j => (stage.expr j).eval input gen)

def Stage.gates {ι σ : Type*} (stage : Stage ι σ) : ℕ :=
  ∑ j ∈ Finset.range stage.length, (stage.expr j).gates

def Stage.usedScalars {ι σ : Type*} (stage : Stage ι σ) : Finset ℤ :=
  (Finset.range stage.length).biUnion (fun j => (stage.expr j).usedScalars)

theorem Stage.eval_from_stored {σ R : Type*} [Ring R] (stage : Stage ℕ σ)
    (p : R[X]) (L : ℕ) (hp : p.natDegree<L) (gen : σ → R) :
    stage.eval (readStored L (fun j => p.coeff j.val)) gen =
      stage.eval p.coeff gen := by
  rw [readStored_coeff p L hp]

def factorStage (σ : Type*) (a : ℤ) (b : ℕ) : Stage ℕ σ where
  length := b+2
  expr j := .add (if j=0 then .constant 0 else .ref (j-1)) (.scale (-a) (.ref j))

theorem factorStage_cost (σ : Type*) (a : ℤ) (b : ℕ) :
    (factorStage σ a b).gates ≤ 3*(b+2) := by
  classical
  unfold Stage.gates
  calc
    _ ≤ ∑ _j ∈ Finset.range (b+2), 3 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j=0 <;> simp [factorStage, CoeffExpr.gates, hj]
    _ = _ := by simp [Nat.mul_comm]

theorem factorStage_semantics {σ R : Type*} [Ring R] (gen : σ → R)
    (a : ℤ) (b : ℕ) (p : R[X]) (hp : p.natDegree≤b) :
    (factorStage σ a b).eval p.coeff gen = (X-C (a : R))*p := by
  have hdegree : ((X-C (a : R))*p).natDegree<b+2 := by
    have hm := Polynomial.natDegree_mul_le (p := (X-C (a : R))) (q := p)
    have hx : (X-C (a : R) : R[X]).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_sub_le _ _).trans
        (max_le Polynomial.natDegree_X_le (by simp))
    omega
  have hc (j : ℕ) : ((factorStage σ a b).expr j).eval p.coeff gen =
      ((X-C (a : R))*p).coeff j := by
    cases j with
    | zero => simp [factorStage, CoeffExpr.eval, sub_mul]
    | succ j =>
      simp only [factorStage, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
        CoeffExpr.eval, Int.cast_neg]
      rw [factor_coeff_succ]
      simp [sub_eq_add_neg]
  change assemble (b+2) _ = _
  simp_rw [hc]
  exact assemble_eq _ _ hdegree

def derivativeStage (σ : Type*) (b : ℕ) : Stage ℕ σ where
  length := b+1
  expr j := .scale (j+1 : ℤ) (.ref (j+1))

theorem derivativeStage_cost (σ : Type*) (b : ℕ) :
    (derivativeStage σ b).gates = b+1 := by
  simp [Stage.gates, derivativeStage, CoeffExpr.gates]

theorem derivativeStage_semantics {σ R : Type*} [Ring R] (gen : σ → R)
    (b : ℕ) (p : R[X]) (hp : p.natDegree≤b) :
    (derivativeStage σ b).eval p.coeff gen = p.derivative := by
  have hd : p.derivative.natDegree<b+1 := by
    have hh := Polynomial.natDegree_derivative_le p
    omega
  have hc (j : ℕ) : ((derivativeStage σ b).expr j).eval p.coeff gen =
      p.derivative.coeff j := by
    simp only [derivativeStage, CoeffExpr.eval, Polynomial.coeff_derivative,
      Int.cast_add, Int.cast_natCast, Int.cast_one]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_commute (j+1) (p.coeff (j+1))).eq
  change assemble (b+1) _ = _
  simp_rw [hc]
  exact assemble_eq _ _ hd

def generatorStage (σ : Type*) (g : σ) (b : ℕ) : Stage ℕ σ where
  length := b+1
  expr j := .leftGenerator g (.ref j)

theorem generatorStage_cost (σ : Type*) (g : σ) (b : ℕ) :
    (generatorStage σ g b).gates = b+1 := by
  simp [Stage.gates, generatorStage, CoeffExpr.gates]

theorem generatorStage_semantics {σ R : Type*} [Ring R] (gen : σ → R)
    (g : σ) (b : ℕ) (p : R[X]) (hp : p.natDegree≤b) :
    (generatorStage σ g b).eval p.coeff gen = C (gen g)*p := by
  have hd : (C (gen g)*p).natDegree<b+1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans_lt (by omega)
  have hc (j : ℕ) : ((generatorStage σ g b).expr j).eval p.coeff gen =
      (C (gen g)*p).coeff j := by
    simp [generatorStage, CoeffExpr.eval, Polynomial.coeff_C_mul]
  change assemble (b+1) _ = _
  simp_rw [hc]
  exact assemble_eq _ _ hd

#print axioms factorStage_semantics
#print axioms derivativeStage_semantics
#print axioms generatorStage_semantics
end
end MultiSymmetric.Circuit
