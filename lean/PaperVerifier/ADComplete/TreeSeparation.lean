import PaperVerifier.ADComplete.GramTables
import PaperVerifier.ADComplete.Radix
import PaperVerifier.ADComplete.TreeDistance
import PaperVerifier.CircuitAudit.WrittenPolynomialBridge
import PaperVerifier.PrincipalMomentAudit.GraphSemantics

/-!
# The actual single-trace readout

The first bridge identifies the literal matrix trace of the symmetrized
polynomial with twice its signed integer radix code. Integer digit bounds
then recover every entry; the three-table module supplies all moments.
-/

namespace ADComplete.TreeSeparation
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix

variable {V W : Type*} [Fintype V] [Fintype W]

def doubleSum (X : Matrix V V ℤ) : ℤ := ∑ u, ∑ v, X u v

theorem trace_ones_mul (X : Matrix V V ℤ) :
    Matrix.trace (TreeDistance.onesMatrix (V := V) * X) = doubleSum X := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, TreeDistance.onesMatrix, one_mul]
  exact Finset.sum_comm

theorem trace_symmetrized (J X : Matrix V V ℤ) :
    Matrix.trace (J * X + star X * star J) = 2 * Matrix.trace (J * X) := by
  rw [Matrix.trace_add, ← star_mul]
  change Matrix.trace (J * X) + Matrix.trace (J * X)ᴴ = _
  rw [Matrix.trace_conjTranspose]
  simp only [star_trivial]
  ring

def sourceCode {Q : ℕ} (b : ℤ) (J : Matrix V V ℤ)
    (X : Fin Q → Matrix V V ℤ) : Matrix V V ℤ :=
  ∑ i : Fin Q, b ^ (i : ℕ) • (J * X i + star (X i) * star J)

theorem encode_ofFn_eq_sum {Q : ℕ} (b : ℤ) (f : Fin Q → ℤ) :
    Radix.encode b (List.ofFn f) = ∑ i : Fin Q, b ^ (i : ℕ) * f i := by
  induction Q with
  | zero => simp [Radix.encode]
  | succ Q ih =>
      rw [List.ofFn_succ, Radix.encode, ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sourceCode_trace {Q : ℕ} (b : ℤ) (X : Fin Q → Matrix V V ℤ) :
    Matrix.trace (sourceCode b (TreeDistance.onesMatrix (V := V)) X) =
      2 * Radix.encode b (List.ofFn (fun i => doubleSum (X i))) := by
  rw [sourceCode, Matrix.trace_sum, encode_ofFn_eq_sum]
  simp_rw [Matrix.trace_smul, trace_symmetrized, trace_ones_mul]
  simp only [zsmul_eq_mul, Int.cast_id]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Literal final-trace equality recovers all signed digits, across different matrix orders. -/
theorem sourceCode_trace_recovers_digits {Q : ℕ} {H b : ℤ}
    (hH : 0 ≤ H) (hb : 2 * H < b)
    (X : Fin Q → Matrix V V ℤ) (Y : Fin Q → Matrix W W ℤ)
    (hX : ∀ i, |doubleSum (X i)| ≤ H) (hY : ∀ i, |doubleSum (Y i)| ≤ H)
    (htrace : Matrix.trace (sourceCode b (TreeDistance.onesMatrix (V := V)) X) =
      Matrix.trace (sourceCode b (TreeDistance.onesMatrix (V := W)) Y)) :
    ∀ i, doubleSum (X i) = doubleSum (Y i) := by
  rw [sourceCode_trace, sourceCode_trace] at htrace
  have henc : Radix.encode b (List.ofFn (fun i => doubleSum (X i))) =
      Radix.encode b (List.ofFn (fun i => doubleSum (Y i))) := by
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) htrace
  have hXB : Radix.Bounded H (List.ofFn (fun i => doubleSum (X i))) := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hX i
  have hYB : Radix.Bounded H (List.ofFn (fun i => doubleSum (Y i))) := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hY i
  have hlist := Radix.encode_injective_of_bounded hH hb
    (by simp : (List.ofFn (fun i => doubleSum (X i))).length =
      (List.ofFn (fun i => doubleSum (Y i))).length) hXB hYB henc
  exact congrFun (List.ofFn_injective hlist)

def tableIndex (M : ℕ) : ((Fin 3 × Fin M) × Fin M) ≃ Fin (3 * M * M) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin M))).trans finProdFinEquiv

theorem tableIndex_value (M : ℕ) (s : Fin 3) (i j : Fin M) :
    (tableIndex M ((s, i), j)).val = s.val * M ^ 2 + i.val * M + j.val := by
  change j.val + M * (i.val + M * s.val) = _
  ring

def indexedTable {M : ℕ} (U : Fin M → Matrix V V ℤ)
    (S : Fin 3 → Matrix V V ℤ) (q : Fin (3 * M * M)) : Matrix V V ℤ :=
  let t := (tableIndex M).symm q
  (star (U t.1.2) * S t.1.1) * U t.2

theorem indexedTable_index {M : ℕ} (U : Fin M → Matrix V V ℤ)
    (S : Fin 3 → Matrix V V ℤ) (s : Fin 3) (i j : Fin M) :
    indexedTable U S (tableIndex M ((s, i), j)) = (star (U i) * S s) * U j := by
  simp [indexedTable]

/-- The exact s,i,j radix order of the manuscript agrees with the flat code index. -/
theorem sourcePolynomial_eq_sourceCode [DecidableEq V] {M : ℕ} (b : ℤ) (J : Matrix V V ℤ)
    (U : Fin M → Matrix V V ℤ) (S : Fin 3 → Matrix V V ℤ) :
    CircuitAudit.RadixFactorization.sourcePolynomial b J U S =
      sourceCode b J (indexedTable U S) := by
  unfold sourceCode
  have h := (tableIndex M).sum_comp (fun q : Fin (3 * M * M) =>
    b ^ q.val • (J * indexedTable U S q + star (indexedTable U S q) * star J))
  rw [← h]
  simp only [Fintype.sum_prod_type, tableIndex_value, indexedTable_index]
  rfl

/-- The actual source polynomial's trace recovers all three tables. -/
theorem sourcePolynomial_trace_recovers_tables [DecidableEq V] [DecidableEq W]
    {M : ℕ} {H b : ℤ}
    (hH : 0 ≤ H) (hb : 2 * H < b)
    (U : Fin M → Matrix V V ℤ) (T : Fin M → Matrix W W ℤ)
    (S : Fin 3 → Matrix V V ℤ) (R : Fin 3 → Matrix W W ℤ)
    (hU : ∀ s i j, |doubleSum ((star (U i) * S s) * U j)| ≤ H)
    (hT : ∀ s i j, |doubleSum ((star (T i) * R s) * T j)| ≤ H)
    (htrace : Matrix.trace (CircuitAudit.RadixFactorization.sourcePolynomial b
        (TreeDistance.onesMatrix (V := V)) U S) =
      Matrix.trace (CircuitAudit.RadixFactorization.sourcePolynomial b
        (TreeDistance.onesMatrix (V := W)) T R)) :
    ∀ s i j, doubleSum ((star (U i) * S s) * U j) =
      doubleSum ((star (T i) * R s) * T j) := by
  rw [sourcePolynomial_eq_sourceCode, sourcePolynomial_eq_sourceCode] at htrace
  have hUb : ∀ q, |doubleSum (indexedTable U S q)| ≤ H := by
    intro q
    exact hU _ _ _
  have hTb : ∀ q, |doubleSum (indexedTable T R q)| ≤ H := by
    intro q
    exact hT _ _ _
  have h := sourceCode_trace_recovers_digits hH hb (indexedTable U S)
    (indexedTable T R) hUb hTb htrace
  intro s i j
  simpa only [indexedTable_index] using h (tableIndex M ((s, i), j))

#print axioms trace_ones_mul
#print axioms sourceCode_trace_recovers_digits
#print axioms sourcePolynomial_trace_recovers_tables
end
end ADComplete.TreeSeparation
