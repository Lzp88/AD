import PaperVerifier.ADComplete.PSDFactoryStar

/-! Literal sum-of-Hermitian-squares output in the integer free algebra,
and positivity on every real symmetric input pair. -/
namespace ADComplete.PSDPairStar
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit ADComplete.PSDBird
open ADComplete.PSDFactory
open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R] {a d : R} {c : Circuit}

theorem square_forward {p : PairRef} (hp : StarPair a d c p) :
    ((square p c).2.value (square p c).1 a d).1 =
      (p.value c a d).1 * star (p.value c a d).1 := by
  rw [square, pairMul_value a d hp.1 (PairRef.swap_valid hp.1), PairRef.swap_value]
  exact congrArg ((p.value c a d).1 * ·) hp.2

theorem chainSquare_forward {N : ℕ} {V : Fin N → PairRef}
    (hV : ∀ i, StarPair a d c (V i)) (r : Fin (N-1)) :
    ((chainSquare V r c).2.value (chainSquare V r c).1 a d).1 =
      (((V (currentIndex r)).value c a d).1 + ((V (nextIndex r)).value c a d).1) *
        star (((V (currentIndex r)).value c a d).1 + ((V (nextIndex r)).value c a d).1) := by
  have h := square_forward (add (hV (currentIndex r)) (hV (nextIndex r)))
  rw [pairAdd_value a d (hV _).1 (hV _).1] at h
  exact h

theorem chainSquareSum_forward {N : ℕ} {V : Fin N → PairRef}
    (hV : ∀ i, StarPair a d c (V i)) (rs : List (Fin (N-1))) :
    ((chainSquareSum V c rs).2.value (chainSquareSum V c rs).1 a d).1 =
      (rs.map (fun r =>
        (((V (currentIndex r)).value c a d).1 + ((V (nextIndex r)).value c a d).1) *
        star (((V (currentIndex r)).value c a d).1 + ((V (nextIndex r)).value c a d).1))).sum := by
  induction rs with
  | nil => simp [chainSquareSum]
  | cons r rs ih =>
      let s := chainSquareSum V c rs
      let w := chainSquare V r s.1
      have es : Extends c s.1 := chainSquareSum_extends V c rs
      have hw := chainSquareSum_star hV rs
      have hv := chainSquare_star (fun i => extend (hV i) es) r
      have hval := chainSquare_forward (fun i => extend (hV i) es) r
      simp only [PairRef.value_extend (hV _).1 es] at hval
      have hew : Extends s.1 w.1 := chainSquare_extends V r s.1
      have hh := congrArg Prod.fst
        (pairAdd_value a d hv.1 (PairRef.valid_extend hw.1 hew))
      rw [PairRef.value_extend hw.1 hew] at hh
      rw [hval, ih] at hh
      exact hh

theorem sos_forward {N : ℕ} (hN : 0<N) {V : Fin N → PairRef}
    (hV : ∀ i, StarPair a d c (V i)) :
    ((sos hN V c).2.value (sos hN V c).1 a d).1 =
      ((V ⟨0,hN⟩).value c a d).1 * star ((V ⟨0,hN⟩).value c a d).1 +
      ∑ r : Fin (N-1),
        (((V (currentIndex r)).value c a d).1 + ((V (nextIndex r)).value c a d).1) *
        star (((V (currentIndex r)).value c a d).1 + ((V (nextIndex r)).value c a d).1) := by
  let s := chainSquareSum V c (List.finRange (N-1))
  have es : Extends c s.1 := chainSquareSum_extends V c _
  have hs := chainSquareSum_star hV (List.finRange (N-1))
  have hv := square_star (extend (hV ⟨0,hN⟩) es)
  have hval := square_forward (extend (hV ⟨0,hN⟩) es)
  simp only [PairRef.value_extend (hV _).1 es] at hval
  have he := square_extends (V ⟨0,hN⟩) s.1
  have hh := congrArg Prod.fst (pairAdd_value a d hv.1 (PairRef.valid_extend hs.1 he))
  rw [PairRef.value_extend hs.1 he, hval, chainSquareSum_forward hV] at hh
  rw [← List.sum_toFinset _ (List.nodup_finRange (N-1)), List.toFinset_finRange] at hh
  exact hh

theorem compiled_sum_of_squares (N : ℕ) (hN : 1≤N) (ha : star a=a) (hd : star d=d) :
    ∃ W : Fin N → R,
      ((PSDFactory.compiled N).2.value (PSDFactory.compiled N).1 a d).1 =
        W ⟨0,by omega⟩ * star (W ⟨0,by omega⟩) +
        ∑ r : Fin (N-1), (W (currentIndex r)+W (nextIndex r)) *
          star (W (currentIndex r)+W (nextIndex r)) := by
  by_cases h1 : N=1
  · subst N
    refine ⟨fun _ => 1, ?_⟩
    simp [PSDFactory.compiled, unitCircuit,unitRef,PairRef.value,Circuit.value,
      Circuit.eval,Gate.eval]
  · have hf := frame_star N hN ha hd
    let f := frame N
    let g := gramStage f.j f.z f.circuit
    let v := residualStage f.j f.z g.2 g.1
    have eg : Extends f.circuit g.1 := gramStage_extends _ _ _
    have hg := gramStage_star hf.1 hf.2
    have hv : ∀ i, StarPair a d v.1 (v.2 i) :=
      residualStage_star (extend hf.1 eg) (fun i => extend (hf.2 i) eg) hg
    refine ⟨fun i => ((v.2 i).value v.1 a d).1, ?_⟩
    have hh := sos_forward (show 0<N by omega) hv
    simpa only [PSDFactory.compiled, show ¬N≤1 by omega, dite_false, f,g,v] using hh

theorem compiled_self_adjoint (N : ℕ) (hN : 1≤N) (ha : star a=a) (hd : star d=d) :
    star ((PSDFactory.compiled N).2.value (PSDFactory.compiled N).1 a d).1 =
      ((PSDFactory.compiled N).2.value (PSDFactory.compiled N).1 a d).1 := by
  obtain ⟨W, hW⟩ := compiled_sum_of_squares N hN ha hd
  rw [hW]
  simp only [star_add,star_sum,star_mul,star_star]

noncomputable def integerPolynomial (N : ℕ) : CircuitAudit.RadixFactorization.IntegerNCPolynomial :=
  ((PSDFactory.compiled N).2.value (PSDFactory.compiled N).1
    CircuitAudit.RadixFactorization.adjacencyGenerator
    CircuitAudit.RadixFactorization.degreeGenerator).1

theorem integerPolynomial_self_adjoint (N : ℕ) (hN : 1≤N) :
    star (integerPolynomial N)=integerPolynomial N :=
  compiled_self_adjoint N hN CircuitAudit.RadixFactorization.adjacencyGenerator_self_adjoint
    CircuitAudit.RadixFactorization.degreeGenerator_self_adjoint

theorem compiled_posSemidef (N n : ℕ) (hN : 1≤N)
    (a d : Matrix (Fin n) (Fin n) ℝ) (ha : a.IsHermitian) (hd : d.IsHermitian) :
    (((PSDFactory.compiled N).2.value (PSDFactory.compiled N).1 a d).1).PosSemidef := by
  obtain ⟨W,hW⟩ := compiled_sum_of_squares N hN ha hd
  rw [hW]
  exact (Matrix.posSemidef_self_mul_conjTranspose (W ⟨0,by omega⟩)).add
    (Matrix.posSemidef_sum Finset.univ (fun r _ =>
      Matrix.posSemidef_self_mul_conjTranspose (W (currentIndex r)+W (nextIndex r))))

theorem integerPolynomial_evaluation {S : Type*} [Ring S] [Algebra ℤ S]
    (a d : S) (N : ℕ) :
    (FreeAlgebra.lift ℤ (fun x : Bool => if x then d else a)) (integerPolynomial N) =
      ((PSDFactory.compiled N).2.value (PSDFactory.compiled N).1 a d).1 := by
  let φ := FreeAlgebra.lift ℤ (fun x : Bool => if x then d else a)
  have h := ADComplete.InstructionDegrees.literal_register_hom φ.toRingHom
    CircuitAudit.RadixFactorization.adjacencyGenerator
    CircuitAudit.RadixFactorization.degreeGenerator (PSDFactory.compiled N).1
    (PSDFactory.compiled N).2.forward
  simpa [φ,integerPolynomial,PairRef.value,
    CircuitAudit.RadixFactorization.adjacencyGenerator,
    CircuitAudit.RadixFactorization.degreeGenerator] using h

#print axioms compiled_sum_of_squares
#print axioms integerPolynomial_self_adjoint
#print axioms compiled_posSemidef
#print axioms integerPolynomial_evaluation

end ADComplete.PSDPairStar
