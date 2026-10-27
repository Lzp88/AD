import MultiSymmetric.CircuitMerge
import MultiSymmetric.Recurrence
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace MultiSymmetric.Circuit
open Polynomial
open scoped BigOperators
noncomputable section
variable {R : Type*} [Ring R]

theorem factorPolynomial_eq (s : ℕ) :
    factorPolynomial (fun j => (j : ℤ)) s = Recurrence.poleProduct s := by
  have hf : ∀ k, factorPolynomial (fun j => (j : ℤ)) k =
      ∏ j ∈ Finset.range k, (X-C (j : ℤ)) := by
    intro k
    induction k with
    | zero => simp [factorPolynomial]
    | succ k ih => rw [factorPolynomial, ih, Finset.prod_range_succ, mul_comm]
  rw [hf]
  exact (Fin.prod_univ_eq_prod_range (fun j => (X-C (j : ℤ))) s).symm

theorem scalar_commute_C (p : ℤ[X]) (a : R) :
    C a * Recurrence.scalarPolynomial p = Recurrence.scalarPolynomial p * C a := by
  ext j
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    Recurrence.scalarPolynomial, Polynomial.coeff_map, Int.coe_castRingHom]
  exact (Int.cast_commute (p.coeff j) a).symm.eq

theorem poleQuotient_degree (s : ℕ) (i : Fin s) :
    (Recurrence.poleQuotient s i).natDegree = s-1 := by
  classical
  have h := Polynomial.natDegree_finsetProd_X_sub_C_eq_card
    ((Finset.univ : Finset (Fin s)).erase i) (fun j : Fin s => (j.val : ℤ))
  simpa [Recurrence.poleQuotient, Finset.card_erase_of_mem (Finset.mem_univ i)] using h

def rowRun (s : ℕ) (κ : ℤ) (gen : Fin (s+1) → R) (k : ℕ) (p : R[X]) :
    PolynomialRun R :=
  let b := s*k
  let d := s*(k+1)
  let g := factorRun (fun j => (j : ℤ)) b p s
  let pder := derivativeStage Empty b
  let t := factorRun (fun j => (j : ℤ)) b (pder.eval p.coeff Empty.elim) s
  let gder := derivativeStage Empty d
  let hg := generatorStage (Fin (s+1)) 0 d
  let qi := fun i : Fin s => quotientRun (i.val : ℤ) d g.value
  let ag := fun i : Fin s => generatorStage (Fin (s+1)) i.succ d
  let three : Fin 3 → R[X] := ![t.value, hg.eval g.value.coeff gen,
    gder.eval g.value.coeff Empty.elim]
  let residues := fun i => (ag i).eval (qi i).value.coeff gen
  let merge := mergeStage s d k κ
  ⟨merge.eval (mergeInput three residues) Empty.elim,
    g.gates + pder.gates + t.gates + gder.gates + hg.gates +
      (∑ i, ((qi i).gates + (ag i).gates)) + merge.gates,
    g.usedScalars ∪ pder.usedScalars ∪ t.usedScalars ∪ gder.usedScalars ∪ hg.usedScalars ∪
      ((Finset.univ : Finset (Fin s)).biUnion fun i =>
        (qi i).usedScalars ∪ (ag i).usedScalars) ∪ merge.usedScalars⟩

theorem rowRun_cost (s : ℕ) (κ : ℤ) (gen : Fin (s+1) → R) (k : ℕ) (p : R[X]) :
    (rowRun s κ gen k p).gates ≤ 30*(s+1)^2*(k+1) := by
  have hG := factorRun_cost (fun j => (j : ℤ)) (s*k) p s
  have hT := factorRun_cost (fun j => (j : ℤ)) (s*k)
    ((derivativeStage Empty (s*k)).eval p.coeff Empty.elim) s
  simp only [rowRun, derivativeStage_cost, generatorStage_cost, quotientRun_cost,
    mergeStage_cost, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith [sq_nonneg (s : ℤ), sq_nonneg (k : ℤ)]

theorem rowRun_semantics (s : ℕ) (hs : 0<s) (κ : ℤ) (gen : Fin (s+1) → R)
    (k : ℕ) (p : R[X]) (hp : p.natDegree≤s*k) :
    (rowRun s κ gen k p).value =
      Recurrence.step s κ (gen 0) (fun i => gen i.succ) k p := by
  let D : R[X] := Recurrence.scalarPolynomial (Recurrence.poleProduct s)
  let Q : Fin s → R[X] := fun i => Recurrence.scalarPolynomial (Recurrence.poleQuotient s i)
  let d := s*(k+1)
  have hd : 0<d := Nat.mul_pos hs (Nat.succ_pos _)
  have hD : D.natDegree≤s := by
    exact (Recurrence.scalarPolynomial_natDegree_le _).trans (Recurrence.poleProduct_natDegree s).le
  have hQ (i : Fin s) : (Q i).natDegree≤s-1 :=
    (Recurrence.scalarPolynomial_natDegree_le _).trans (poleQuotient_degree s i).le
  have hdp : (D*p).natDegree≤d := by
    have h := Polynomial.natDegree_mul_le (p := D) (q := p)
    dsimp [d]
    nlinarith
  have hpder : p.derivative.natDegree≤s*k :=
    (Polynomial.natDegree_derivative_le _).trans (by omega)
  have ht : (D*p.derivative).natDegree≤d := by
    have h := Polynomial.natDegree_mul_le (p := D) (q := p.derivative)
    dsimp [d]
    nlinarith
  have hq (i : Fin s) : (Q i*p).natDegree<d := by
    have h := Polynomial.natDegree_mul_le (p := Q i) (q := p)
    have hqi := hQ i
    dsimp [d]
    nlinarith [Nat.sub_add_cancel (by omega : 1≤s)]
  have hfactor (i : Fin s) : (X-C ((i.val : ℤ) : R))*(Q i*p)=D*p := by
    have hf := congrArg (Polynomial.map (Int.castRingHom R)) (Recurrence.pole_factor s i)
    have hf' : (X-C ((i.val : ℤ) : R))*Q i=D := by
      simpa [Q, D, Recurrence.scalarPolynomial] using hf
    rw [← mul_assoc, hf']
  have hG : (factorRun (fun j => (j : ℤ)) (s*k) p s).value=D*p := by
    rw [factorRun_semantics _ _ _ hp, factorPolynomial_eq]
    rfl
  have hT : (factorRun (fun j => (j : ℤ)) (s*k)
      ((derivativeStage Empty (s*k)).eval p.coeff Empty.elim) s).value=D*p.derivative := by
    rw [derivativeStage_semantics Empty.elim _ _ hp]
    rw [factorRun_semantics _ _ _ hpder, factorPolynomial_eq]
    rfl
  have hquot (i : Fin s) : (quotientRun (i.val : ℤ) d (D*p)).value=Q i*p := by
    calc
      _ = (quotientRun (i.val : ℤ) d ((X-C ((i.val : ℤ) : R))*(Q i*p))).value :=
        congrArg (fun f : R[X] => (quotientRun (i.val : ℤ) d f).value) (hfactor i).symm
      _ = _ := quotientRun_semantics (i.val : ℤ) d (Q i*p) (hq i)
  have hleftH : ((generatorStage (Fin (s+1)) 0 d).eval (D*p).coeff gen) =
      C (gen 0)*(D*p) := generatorStage_semantics gen 0 d _ hdp
  have hderG : (derivativeStage Empty d).eval (D*p).coeff Empty.elim =
      (D*p).derivative := derivativeStage_semantics Empty.elim d _ hdp
  have hleftA (i : Fin s) : (generatorStage (Fin (s+1)) i.succ d).eval
      (Q i*p).coeff gen = C (gen i.succ)*(Q i*p) :=
    generatorStage_semantics gen i.succ d _ (Nat.le_of_lt (hq i))
  let three : Fin 3 → R[X] := ![D*p.derivative, C (gen 0)*(D*p), (D*p).derivative]
  let residues : Fin s → R[X] := fun i => C (gen i.succ)*(Q i*p)
  have hthree (i : Fin 3) : (three i).natDegree≤d := by
    fin_cases i
    · exact ht
    · exact (Polynomial.natDegree_C_mul_le _ _).trans hdp
    · exact (Polynomial.natDegree_derivative_le _).trans (by omega)
  have hres (i : Fin s) : (residues i).natDegree≤d :=
    (Polynomial.natDegree_C_mul_le _ _).trans (Nat.le_of_lt (hq i))
  dsimp only [d] at hquot hleftH hderG hleftA
  have hout : (rowRun s κ gen k p).value =
      C (((κ*(k+1)):ℤ):R)*(D*p.derivative) + C (κ:R)*(C (gen 0)*(D*p)) +
        ((∑ i, (C (gen i.succ)*(Q i*p))) + C ((-((k:ℤ)*κ):ℤ):R)*(D*p).derivative) := by
    simp only [rowRun, hG, hT]
    change (mergeStage s d k κ).eval _ Empty.elim = _
    simp only [hquot, hleftH, hderG, hleftA]
    exact mergeStage_semantics s d k κ three residues hthree hres
  rw [hout]
  have hcH : C (gen 0)*(D*p)=D*C (gen 0)*p := by
    rw [← mul_assoc, scalar_commute_C]
  have hcA (i : Fin s) : C (gen i.succ)*(Q i*p)=Q i*C (gen i.succ)*p := by
    rw [← mul_assoc, scalar_commute_C]
  simp only [hcH, hcA, ← mul_assoc]
  simp only [Recurrence.step]
  change _ = C (κ:R)*D*p.derivative + C (κ:R)*D*C (gen 0)*p +
    (∑ i, (Q i*C (gen i.succ)*p)) - C ((((k:ℤ)*κ):ℤ):R)*D.derivative*p
  rw [Polynomial.derivative_mul]
  have hscalar : C (((κ*(k+1)):ℤ):R) = C (κ:R)+C ((((k:ℤ)*κ):ℤ):R) := by
    have hz : κ*((k:ℤ)+1)=κ+(k:ℤ)*κ := by ring
    simpa only [Int.cast_add, map_add] using
      congrArg (fun z : ℤ => (C (z:R) : R[X])) hz
  rw [hscalar]
  simp only [Int.cast_neg, map_neg]
  noncomm_ring

#print axioms rowRun_semantics
#print axioms rowRun_cost
end
end MultiSymmetric.Circuit
