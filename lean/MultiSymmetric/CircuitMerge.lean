import MultiSymmetric.CircuitFactor
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false

namespace MultiSymmetric.Circuit
open Polynomial
open scoped BigOperators
noncomputable section

def sumReferences {ι σ : Type*} : List ι → CoeffExpr ι σ
  | [] => .constant 0
  | i :: rest => .add (.ref i) (sumReferences rest)

theorem sumReferences_cost {ι σ : Type*} (xs : List ι) :
    (sumReferences (σ := σ) xs).gates = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [sumReferences, CoeffExpr.gates, ih]

theorem sumReferences_eval {ι σ R : Type*} [Ring R]
    (input : ι → R) (gen : σ → R) (xs : List ι) :
    (sumReferences xs).eval input gen = (xs.map input).sum := by
  induction xs with
  | nil => simp [sumReferences, CoeffExpr.eval]
  | cons i xs ih => simp [sumReferences, CoeffExpr.eval, ih]

abbrev MergeInput (s : ℕ) := (Fin 3 ⊕ Fin s) × ℕ

def mergeStage (s d k : ℕ) (κ : ℤ) : Stage (MergeInput s) Empty where
  length := d+1
  expr j := .add
    (.add (.scale (κ*(k+1)) (.ref (.inl 0,j)))
      (.scale κ (.ref (.inl 1,j))))
    (.add (sumReferences (List.ofFn (fun i : Fin s => (Sum.inr i,j))))
      (.scale (-((k : ℤ)*κ)) (.ref (.inl 2,j))))

theorem mergeStage_cost (s d k : ℕ) (κ : ℤ) :
    (mergeStage s d k κ).gates = (s+7)*(d+1) := by
  simp [Stage.gates, mergeStage, CoeffExpr.gates, sumReferences_cost,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

def mergeInput {R : Type*} [Ring R] {s : ℕ}
    (p : Fin 3 → R[X]) (q : Fin s → R[X]) : MergeInput s → R
  | (.inl i,j) => (p i).coeff j
  | (.inr i,j) => (q i).coeff j

theorem mergeStage_semantics {R : Type*} [Ring R] (s d k : ℕ) (κ : ℤ)
    (p : Fin 3 → R[X]) (q : Fin s → R[X])
    (hp : ∀ i, (p i).natDegree≤d) (hq : ∀ i, (q i).natDegree≤d) :
    (mergeStage s d k κ).eval (mergeInput p q) Empty.elim =
      C (((κ*(k+1)) : ℤ) : R)*p 0 + C (κ : R)*p 1 +
          ((∑ i, q i) + C ((-((k : ℤ)*κ) : ℤ) : R)*p 2) := by
  let out : R[X] := C ((κ*(k+1) : ℤ) : R)*p 0 + C (κ : R)*p 1 +
    ((∑ i, q i) + C ((-((k : ℤ)*κ) : ℤ) : R)*p 2)
  have hconst (c : R) (i : Fin 3) : (C c*p i).natDegree≤d :=
    (Polynomial.natDegree_C_mul_le _ _).trans (hp i)
  have hs : (∑ i,q i).natDegree≤d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact hq i
  have ho : out.natDegree<d+1 := by
    have h1 := (Polynomial.natDegree_add_le _ _).trans
      (max_le (hconst (((κ*(k+1):ℤ):R)) 0) (hconst (κ:R) 1))
    have h2 := (Polynomial.natDegree_add_le _ _).trans
      (max_le hs (hconst (((-((k:ℤ)*κ)):ℤ):R) 2))
    exact ((Polynomial.natDegree_add_le _ _).trans (max_le h1 h2)).trans_lt (by omega)
  have hc (j : ℕ) : ((mergeStage s d k κ).expr j).eval (mergeInput p q) Empty.elim =
      out.coeff j := by
    simp only [mergeStage, CoeffExpr.eval, mergeInput, sumReferences_eval,
      List.map_ofFn, List.sum_ofFn, out, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.finsetSum_coeff, Function.comp_apply]
  change assemble (d+1) _ = _
  simp_rw [hc]
  rw [assemble_eq out _ ho]

#print axioms mergeStage_semantics
#print axioms mergeStage_cost
end
end MultiSymmetric.Circuit
