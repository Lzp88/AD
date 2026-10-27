import MultiSymmetric.Recurrence
import Mathlib.LinearAlgebra.Span.Basic
/-! Word-degree certificates for the literal integer free-algebra recurrence.
The certificate exhibits a genuine ring expression of the stated degree. -/
namespace MultiSymmetric.Recurrence
open scoped BigOperators
open Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

inductive Expr (s : ℕ) where
  | scalar (c : ℤ)
  | letter (i : Fin (s + 1))
  | add (p q : Expr s)
  | mul (p q : Expr s)

def Expr.eval {s : ℕ} : Expr s → NC s
  | .scalar c => c
  | .letter i => generator s i
  | .add p q => p.eval + q.eval
  | .mul p q => p.eval * q.eval

def Expr.degree {s : ℕ} : Expr s → ℕ
  | .scalar _ => 0
  | .letter _ => 1
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree

def HasWordDegree {s : ℕ} (p : NC s) (d : ℕ) : Prop :=
  ∃ e : Expr s, e.eval = p ∧ e.degree ≤ d

theorem HasWordDegree.mono {s d e : ℕ} {p : NC s}
    (h : HasWordDegree p d) (hde : d ≤ e) : HasWordDegree p e := by
  obtain ⟨f, hf, hd⟩ := h
  exact ⟨f, hf, hd.trans hde⟩

theorem HasWordDegree.scalar (s : ℕ) (c : ℤ) :
    HasWordDegree (c : NC s) 0 := ⟨.scalar c, rfl, le_rfl⟩

theorem HasWordDegree.letter (s : ℕ) (i : Fin (s + 1)) :
    HasWordDegree (generator s i) 1 := ⟨.letter i, rfl, le_rfl⟩

theorem HasWordDegree.add {s d : ℕ} {p q : NC s}
    (hp : HasWordDegree p d) (hq : HasWordDegree q d) :
    HasWordDegree (p + q) d := by
  obtain ⟨ep, hp, hd⟩ := hp
  obtain ⟨eq, hq, he⟩ := hq
  exact ⟨.add ep eq, by simp [Expr.eval, hp, hq], max_le hd he⟩

theorem HasWordDegree.mul {s d e : ℕ} {p q : NC s}
    (hp : HasWordDegree p d) (hq : HasWordDegree q e) :
    HasWordDegree (p * q) (d + e) := by
  obtain ⟨ep, hp, hd⟩ := hp
  obtain ⟨eq, hq, he⟩ := hq
  exact ⟨.mul ep eq, by simp [Expr.eval, hp, hq], Nat.add_le_add hd he⟩

theorem HasWordDegree.neg {s d : ℕ} {p : NC s}
    (hp : HasWordDegree p d) : HasWordDegree (-p) d := by
  simpa using (HasWordDegree.scalar s (-1)).mul hp

theorem HasWordDegree.sub {s d : ℕ} {p q : NC s}
    (hp : HasWordDegree p d) (hq : HasWordDegree q d) :
    HasWordDegree (p - q) d := by
  simpa [sub_eq_add_neg] using hp.add hq.neg

theorem HasWordDegree.sum {s d : ℕ} {α : Type*} (t : Finset α) (f : α → NC s)
    (h : ∀ i ∈ t, HasWordDegree (f i) d) : HasWordDegree (∑ i ∈ t, f i) d := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (HasWordDegree.scalar s 0).mono (Nat.zero_le d)
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

def CoefficientDegree {s : ℕ} (p : (NC s)[X]) (d : ℕ) : Prop :=
  ∀ j, HasWordDegree (p.coeff j) d

theorem CoefficientDegree.mono {s d e : ℕ} {p : (NC s)[X]}
    (h : CoefficientDegree p d) (hde : d ≤ e) : CoefficientDegree p e :=
  fun j => (h j).mono hde

theorem CoefficientDegree.C {s d : ℕ} {p : NC s}
    (h : HasWordDegree p d) : CoefficientDegree (C p) d := by
  intro j
  by_cases hj : j = 0
  · subst j; simpa using h
  · simpa [Polynomial.coeff_C, hj] using
      (HasWordDegree.scalar s 0).mono (Nat.zero_le d)

theorem CoefficientDegree.scalar (s : ℕ) (p : ℤ[X]) :
    CoefficientDegree (scalarPolynomial (R := NC s) p) 0 := by
  intro j
  simpa [scalarPolynomial] using HasWordDegree.scalar s (p.coeff j)

theorem CoefficientDegree.add {s d : ℕ} {p q : (NC s)[X]}
    (hp : CoefficientDegree p d) (hq : CoefficientDegree q d) :
    CoefficientDegree (p + q) d := by
  intro j
  simpa using (hp j).add (hq j)

theorem CoefficientDegree.sub {s d : ℕ} {p q : (NC s)[X]}
    (hp : CoefficientDegree p d) (hq : CoefficientDegree q d) :
    CoefficientDegree (p - q) d := by
  intro j
  simpa using (hp j).sub (hq j)

theorem CoefficientDegree.mul {s d e : ℕ} {p q : (NC s)[X]}
    (hp : CoefficientDegree p d) (hq : CoefficientDegree q e) :
    CoefficientDegree (p * q) (d + e) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact HasWordDegree.sum _ _ (fun ij _ => (hp ij.1).mul (hq ij.2))

theorem CoefficientDegree.derivative {s d : ℕ} {p : (NC s)[X]}
    (hp : CoefficientDegree p d) : CoefficientDegree p.derivative d := by
  intro j
  rw [Polynomial.coeff_derivative]
  simpa using (hp (j+1)).mul (HasWordDegree.scalar s (j+1 : ℕ))

theorem CoefficientDegree.sum {s d : ℕ} {α : Type*} (t : Finset α)
    (f : α → (NC s)[X]) (h : ∀ i ∈ t, CoefficientDegree (f i) d) :
    CoefficientDegree (∑ i ∈ t, f i) d := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact HasWordDegree.sum _ _ (fun i hi => h i hi j)

theorem universalRow_wordDegree (s N k : ℕ) :
    CoefficientDegree (universalRow s N k) k := by
  unfold universalRow
  induction k with
  | zero => simpa [row] using CoefficientDegree.C (HasWordDegree.scalar s 1)
  | succ k ih =>
      rw [row_succ, step]
      have hc (z : ℤ) : CoefficientDegree (C (z : NC s)) 0 :=
        CoefficientDegree.C (HasWordDegree.scalar s z)
      have hd := CoefficientDegree.scalar s (poleProduct s)
      have hq (i : Fin s) := CoefficientDegree.scalar s (poleQuotient s i)
      have hh := CoefficientDegree.C (HasWordDegree.letter s 0)
      have ha (i : Fin s) := CoefficientDegree.C (HasWordDegree.letter s i.succ)
      have hcd := CoefficientDegree.mul (s := s) (d := 0) (e := 0)
        (hc ((s : ℤ) * (N : ℤ)^2)) hd
      have hfirst := CoefficientDegree.mul (s := s) (d := 0 + 0) (e := k)
        hcd (CoefficientDegree.derivative (s := s) ih)
      have hsecond := CoefficientDegree.mul (s := s) (d := 0 + 0 + 1) (e := k)
        (CoefficientDegree.mul (s := s) (d := 0 + 0) (e := 1) hcd hh) ih
      have hthird : CoefficientDegree
          (∑ i : Fin s, scalarPolynomial (poleQuotient s i) *
            C (generator s i.succ) * row s ((s : ℤ) * (N : ℤ)^2)
              (generator s 0) (fun i => generator s i.succ) k) (k+1) := by
        apply CoefficientDegree.sum (s := s)
        intro i hi
        have ht := CoefficientDegree.mul (s := s) (d := 0 + 1) (e := k)
          (CoefficientDegree.mul (s := s) (d := 0) (e := 1) (hq i) (ha i)) ih
        exact CoefficientDegree.mono (s := s) ht (by omega)
      have hlast := CoefficientDegree.mul (s := s) (d := 0 + 0) (e := k)
        (CoefficientDegree.mul (s := s) (d := 0) (e := 0)
          (hc ((k : ℤ) * ((s : ℤ) * (N : ℤ)^2)))
          (CoefficientDegree.derivative (s := s) hd)) ih
      exact CoefficientDegree.sub (s := s)
        (CoefficientDegree.add (s := s)
          (CoefficientDegree.add (s := s)
            (CoefficientDegree.mono (s := s) hfirst (by omega))
            (CoefficientDegree.mono (s := s) hsecond (by omega))) hthird)
        (CoefficientDegree.mono (s := s) hlast (by omega))

theorem probe_wordDegree (s N : ℕ) (i : Index s N) :
    HasWordDegree (probe s N i) (N - 1) :=
  (universalRow_wordDegree s N i.1.val i.2.val).mono (by omega)

/-- The literal integer span of words of length at most d. -/
def wordSpan (s d : ℕ) : Submodule ℤ (NC s) :=
  Submodule.span ℤ {p | ∃ w : List (Fin (s + 1)),
    w.length ≤ d ∧ p = (w.map (generator s)).prod}

theorem word_mem_wordSpan (s : ℕ) (w : List (Fin (s + 1))) (d : ℕ)
    (hw : w.length ≤ d) : (w.map (generator s)).prod ∈ wordSpan s d :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem wordSpan_mono (s : ℕ) {d e : ℕ} (h : d ≤ e) : wordSpan s d ≤ wordSpan s e := by
  apply Submodule.span_mono
  rintro p ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans h, rfl⟩

theorem wordSpan_mul (s d e : ℕ) {p q : NC s}
    (hp : p ∈ wordSpan s d) (hq : q ∈ wordSpan s e) :
    p * q ∈ wordSpan s (d + e) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨w, hw, rfl⟩ := hp
      induction hq using Submodule.span_induction with
      | mem q hq =>
          obtain ⟨z, hz, rfl⟩ := hq
          have hh : (w ++ z).length ≤ d + e := by simp; omega
          simpa [List.map_append, List.prod_append] using word_mem_wordSpan s (w ++ z) (d+e) hh
      | zero => simp
      | add x y hx hy hxp hyp =>
          rw [mul_add]
          exact (wordSpan s (d+e)).add_mem hxp hyp
      | smul c x hx hcx =>
          rw [mul_smul_comm]
          exact (wordSpan s (d+e)).smul_mem c hcx
  | zero => simp
  | add x y hx hy hxp hyp =>
      rw [add_mul]
      exact (wordSpan s (d+e)).add_mem hxp hyp
  | smul c x hx hcx =>
      rw [smul_mul_assoc]
      exact (wordSpan s (d+e)).smul_mem c hcx

theorem Expr.eval_mem_wordSpan {s : ℕ} (e : Expr s) : e.eval ∈ wordSpan s e.degree := by
  induction e with
  | scalar c =>
      have h := (wordSpan s 0).smul_mem c (word_mem_wordSpan s [] 0 (by simp))
      simpa [Expr.eval, Expr.degree, zsmul_eq_mul] using h
  | letter i =>
      simpa [Expr.eval, Expr.degree] using word_mem_wordSpan s [i] 1 (by simp)
  | add p q hp hq =>
      exact (wordSpan s (max p.degree q.degree)).add_mem
        (wordSpan_mono s (le_max_left _ _) hp) (wordSpan_mono s (le_max_right _ _) hq)
  | mul p q hp hq => exact wordSpan_mul s p.degree q.degree hp hq

theorem HasWordDegree.mem_wordSpan {s d : ℕ} {p : NC s}
    (h : HasWordDegree p d) : p ∈ wordSpan s d := by
  obtain ⟨e, rfl, he⟩ := h
  exact wordSpan_mono s he e.eval_mem_wordSpan

theorem universalRow_coeff_wordSpan (s N k j : ℕ) :
    (universalRow s N k).coeff j ∈ wordSpan s k :=
  (universalRow_wordDegree s N k j).mem_wordSpan

theorem probe_mem_wordSpan (s N : ℕ) (i : Index s N) :
    probe s N i ∈ wordSpan s (N - 1) := (probe_wordDegree s N i).mem_wordSpan

#print axioms universalRow_wordDegree
#print axioms probe_wordDegree
#print axioms probe_mem_wordSpan
end
end MultiSymmetric.Recurrence

