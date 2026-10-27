import MultiSymmetric.CircuitStages
set_option autoImplicit false

/-! Composition of literal coefficient stages for products and quotients. -/
namespace MultiSymmetric.Circuit
open Polynomial
noncomputable section
variable {R : Type*} [Ring R]

structure PolynomialRun (R : Type*) [Ring R] where
  value : R[X]
  gates : ℕ
  usedScalars : Finset ℤ

def factorPolynomial (a : ℕ → ℤ) : ℕ → ℤ[X]
  | 0 => 1
  | k+1 => (X-C (a k))*factorPolynomial a k

def factorRun (a : ℕ → ℤ) (b : ℕ) (p : R[X]) : ℕ → PolynomialRun R
  | 0 => ⟨p,0,∅⟩
  | k+1 =>
    let previous := factorRun a b p k
    let stage := factorStage Empty (a k) (b+k)
    ⟨stage.eval previous.value.coeff Empty.elim, previous.gates+stage.gates,
      previous.usedScalars ∪ stage.usedScalars⟩

theorem factorRun_degree (a : ℕ → ℤ) (b : ℕ) (p : R[X]) (hp : p.natDegree≤b)
    (k : ℕ) : (factorRun a b p k).value.natDegree≤b+k := by
  induction k with
  | zero => simpa [factorRun] using hp
  | succ k ih =>
      change ((factorStage Empty (a k) (b+k)).eval
        (factorRun a b p k).value.coeff Empty.elim).natDegree ≤ b+(k+1)
      rw [factorStage_semantics Empty.elim (a k) (b+k) _ ih]
      have h := Polynomial.natDegree_mul_le
        (p := (X-C (a k : R))) (q := (factorRun a b p k).value)
      have hc : (X-C (a k : R) : R[X]).natDegree≤1 :=
        (Polynomial.natDegree_sub_le _ _).trans
          (max_le Polynomial.natDegree_X_le (by simp))
      omega

theorem factorRun_semantics (a : ℕ → ℤ) (b : ℕ) (p : R[X]) (hp : p.natDegree≤b)
    (k : ℕ) : (factorRun a b p k).value =
      (factorPolynomial a k).map (Int.castRingHom R) * p := by
  induction k with
  | zero => simp [factorRun, factorPolynomial]
  | succ k ih =>
      change (factorStage Empty (a k) (b+k)).eval
        (factorRun a b p k).value.coeff Empty.elim = _
      rw [factorStage_semantics Empty.elim (a k) (b+k) _
        (factorRun_degree a b p hp k), ih]
      simp [factorPolynomial, mul_assoc]

theorem factorRun_cost (a : ℕ → ℤ) (b : ℕ) (p : R[X]) (k : ℕ) :
    (factorRun a b p k).gates ≤ 3*k*(b+k+1) := by
  induction k with
  | zero => simp [factorRun]
  | succ k ih =>
      have hs := factorStage_cost Empty (a k) (b+k)
      change (factorRun a b p k).gates + (factorStage Empty (a k) (b+k)).gates ≤ _
      nlinarith

structure IntegerScan (R : Type*) where
  run : ScanState R
  usedScalars : Finset ℤ

def integerScanStep (a : ℤ) : CoeffExpr Bool Empty :=
  .add (.ref true) (.scale a (.ref false))

/-- The quotient evaluator executes actual coefficient-expression nodes, and
obtains both costs and scalar inventories from those same nodes. -/
def integerScan (a : ℤ) (g : ℕ → R) (d : ℕ) : ℕ → IntegerScan R
  | 0 => ⟨⟨0,[0],(CoeffExpr.constant (ι := Bool) (σ := Empty) 0).gates⟩,
      (CoeffExpr.constant (ι := Bool) (σ := Empty) 0).usedScalars⟩
  | r+1 =>
      let previous := integerScan a g d r
      let step := integerScanStep a
      let next := step.eval (fun b => if b then g (d-r) else previous.run.current) Empty.elim
      ⟨⟨next,next :: previous.run.history,previous.run.gates+step.gates⟩,
        previous.usedScalars ∪ step.usedScalars⟩

theorem integerScan_bridge (a : ℤ) (g : ℕ → R) (d r : ℕ) :
    (integerScan a g d r).run = syntheticScan (a:R) g d r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [integerScan, integerScanStep, CoeffExpr.eval, CoeffExpr.gates,
        Bool.false_eq_true, ite_false, ite_true]
      rw [ih]
      rfl

theorem integerScan_scalar (a : ℤ) (g : ℕ → R) (d r : ℕ) (c : ℤ)
    (hc : c ∈ (integerScan a g d r).usedScalars) : c=0 ∨ c=a := by
  induction r with
  | zero =>
      have hc' : c=0 := by simpa [integerScan, CoeffExpr.usedScalars] using hc
      exact Or.inl hc'
  | succ r ih =>
      simp only [integerScan, integerScanStep, CoeffExpr.usedScalars,
        Finset.empty_union, Finset.mem_union, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hc
      rcases hc with hp | ha
      · exact ih hp
      · exact Or.inr ha

def quotientRun (a : ℤ) (d : ℕ) (g : R[X]) : PolynomialRun R :=
  let scan := integerScan a g.coeff d d
  ⟨assemble d (fun j => scan.run.history.getD j 0), scan.run.gates, scan.usedScalars⟩

theorem quotientRun_cost (a : ℤ) (d : ℕ) (g : R[X]) :
    (quotientRun a d g).gates = 2*d+1 := by
  change (integerScan a g.coeff d d).run.gates = _
  rw [integerScan_bridge]
  exact syntheticScan_gates (a : R) g.coeff d d

theorem quotientRun_semantics (a : ℤ) (d : ℕ) (q : R[X]) (hq : q.natDegree<d) :
    (quotientRun a d ((X-C (a : R))*q)).value = q := by
  have he (j : ℕ) (hj : j<d) :
      (syntheticScan (a : R) (((X-C (a : R))*q).coeff) d d).history.getD j 0 =
        q.coeff j := by
    rw [syntheticScan_history_getD _ _ _ _ _ (by omega)]
    rw [syntheticScan_correct _ q d hq (d-j) (Nat.sub_le _ _)]
    have hn : d-(d-j)=j := by omega
    rw [hn]
  change assemble d (fun j =>
    (integerScan a (((X-C (a:R))*q).coeff) d d).run.history.getD j 0) = q
  rw [integerScan_bridge]
  ext j
  rw [assemble_coeff]
  by_cases hj : j<d
  · simp only [hj, if_true]; exact he j hj
  · simp only [hj, if_false]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hq.trans_le (by omega))).symm

#print axioms factorRun_semantics
#print axioms factorRun_cost
#print axioms quotientRun_semantics
#print axioms quotientRun_cost
end
end MultiSymmetric.Circuit
