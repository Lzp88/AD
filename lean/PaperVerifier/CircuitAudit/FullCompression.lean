import PaperVerifier.CircuitAudit.DistanceSemantics
import PaperVerifier.CircuitAudit.WrittenPolynomialBridge

/-! The concrete circuit from the empty prefix through all triangular probes,
the McKay distance sum, and the factored single-trace polynomial. -/
namespace CircuitAudit.FullCompression

open CircuitCosts ProbeCircuit

def full (N : ℕ) (b : ℤ) : Result :=
  let pp := probePrefix N
  let jj := DistanceCircuit.build N pp.circuit
  compress jj.1 oneRef aRef dRef jj.2 b pp.probes.length pp.probes

theorem prefix_ready_empty (N : ℕ) : Ready (probePrefix N).circuit [] := by
  have h := build_ready N (N-1)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by simp⟩

theorem prefix_extends_initial (N : ℕ) : Extends initial (probePrefix N).circuit :=
  build_extends N (N-1)

theorem full_valid (N : ℕ) (b : ℤ) : (full N b).2.valid (full N b).1 :=
  compress_valid _ _ _ _ _ _ _ _

theorem full_safe (N : ℕ) (b : ℤ) : (full N b).1.safe := by
  have hp := prefix_ready_empty N
  have he := DistanceCircuit.build_extends N (probePrefix N).circuit
  have hr := ready_extend hp he
  exact compress_safe b _ (DistanceCircuit.build_safe N (prefix_safe N) hp)
    hr.1 hr.2.1 hr.2.2.1 (DistanceCircuit.build_valid N hp)
    (fun p h => PairRef.valid_extend (build_probes_valid N (N-1) p h) he)

theorem full_extends_initial (N : ℕ) (b : ℤ) : Extends initial (full N b).1 :=
  ((prefix_extends_initial N).trans
    (DistanceCircuit.build_extends N (probePrefix N).circuit)).trans
      (compress_extends _ _ _ _ _ _ _ _)

theorem full_exact_length (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    (full N b).1.length =
      4 + 6*(N-1)*(N+2) + 14 + 10*(N-3) + 12*(N*(N+1)/2) + 21 := by
  have hm := prefix_probe_count N hN
  have hs : N-1+3=N+2 := by omega
  simp only [full, compress_length, DistanceCircuit.build_length, hm]
  change (build N (N-1)).circuit.length + 14 + 10*(N-3) +
    4*(N*(N+1)/2) + 8*(N*(N+1)/2) + 21 = _
  rw [build_exact_length, hs]
  ring

theorem full_gate_bound (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    (full N b).1.length ≤ 61*N^2 := by
  cases N with
  | zero => omega
  | succ n =>
    have hm := build_twice_probe_count (n+1) n
    have hcount := prefix_probe_count (n+1) hN
    simp only [probePrefix, Nat.add_sub_cancel] at hcount
    rw [hcount] at hm
    have hlen := full_exact_length (n+1) hN b
    simp only [Nat.add_sub_cancel] at hlen
    nlinarith [Nat.sub_le (n+1) 3]

def scalarConstants (N : ℕ) (b : ℤ) : Set ℤ :=
  {z | z = b ∨ z = -1 ∨ z ∈ probeConstants N}

theorem full_constants (N : ℕ) (b : ℤ) :
    (full N b).1.constantsAllowed (scalarConstants N b) := by
  apply compress_constants
  · apply DistanceCircuit.build_constants
    · apply prefix_constants_of
      · exact Or.inr (Or.inr (Or.inl rfl))
      · intro k hk j hj
        exact Or.inr (Or.inr (Or.inr ⟨k, j, hk, hj, rfl⟩))
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem scalarConstants_abs_bound (N : ℕ) (hN : 1 ≤ N) (b : ℤ) {z : ℤ}
    (hz : z ∈ scalarConstants N b) : |z| ≤ max |b| ((N : ℤ)^3) := by
  rcases hz with rfl | rfl | hz
  · exact le_max_left _ _
  · have hn : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have hcube : (1 : ℤ) ≤ (N : ℤ)^3 := by nlinarith [sq_nonneg ((N : ℤ)-1)]
    calc
      |(-1 : ℤ)| = 1 := by norm_num
      _ ≤ (N : ℤ)^3 := hcube
      _ ≤ max |b| ((N : ℤ)^3) := le_max_right _ _
  · exact (probeConstants_abs_bound N hN hz).trans (le_max_right _ _)

theorem reverse_involutive (p : Degrees.Expr) : p.reverse.reverse = p := by
  induction p <;> simp_all [Degrees.Expr.reverse]

theorem exprPair_one {R : Type*} [Ring R] (A D : R) :
    exprPair A D .one = (1, 1) := rfl

theorem exprPair_a {R : Type*} [Ring R] (A D : R) :
    exprPair A D .a = (A, A) := rfl

theorem exprPair_d {R : Type*} [Ring R] (A D : R) :
    exprPair A D .d = (D, D) := rfl

theorem exprPair_scale {R : Type*} [Ring R] (A D : R) (k : ℤ) (p : Degrees.Expr) :
    exprPair A D (.scale k p) =
      (k • (exprPair A D p).1, k • (exprPair A D p).2) := rfl

theorem exprPair_add {R : Type*} [Ring R] (A D : R) (p q : Degrees.Expr) :
    exprPair A D (.add p q) = addValue (exprPair A D p) (exprPair A D q) := rfl

theorem exprPair_mul {R : Type*} [Ring R] (A D : R) (p q : Degrees.Expr) :
    exprPair A D (.mul p q) = mulValue (exprPair A D p) (exprPair A D q) := rfl

theorem exprPair_reverse {R : Type*} [Ring R] (A D : R) (p : Degrees.Expr) :
    exprPair A D p.reverse = swapValue (exprPair A D p) := by
  simp only [exprPair, reverse_involutive, swapValue]

theorem power_expr_pair {R : Type*} [Ring R] (A D : R) (base : Degrees.Expr) (n : ℕ) :
    powerValue (exprPair A D base) (1, 1) n = exprPair A D (Degrees.power base n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powerValue, ih]; rfl

theorem horner_expr_pair {R : Type*} [Ring R] (A D : R) (base : Degrees.Expr)
    (ps : List Degrees.Expr) :
    hornerValue (exprPair A D base) (ps.map (exprPair A D)) =
      exprPair A D (Degrees.horner base ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, hornerValue, ih]; rfl

theorem compression_expr_pair {R : Type*} [Ring R] (A D : R) (b : ℤ)
    (J : Degrees.Expr) (ps : List Degrees.Expr) :
    compressionValue (1, 1) (A, A) (D, D) (exprPair A D J) b ps.length
      (ps.map (exprPair A D)) = exprPair A D (Degrees.factored b J ps) := by
  unfold compressionValue
  simp only [Degrees.factored, exprPair_add, exprPair_mul, exprPair_reverse,
    ← power_expr_pair, ← horner_expr_pair, exprPair_scale,
    exprPair_one, exprPair_a, exprPair_d]

set_option maxHeartbeats 500000 in
theorem full_value {R : Type*} [Ring R] (N : ℕ) (hN : 1 ≤ N) (b : ℤ) (A D : R) :
    (full N b).2.value (full N b).1 A D =
      compressionValue (1, 1) (A, A) (D, D)
        (exprPair A D (Degrees.allOnes N)) b (Degrees.probeList N N).length
        ((Degrees.probeList N N).map (exprPair A D)) := by
  have hr := prefix_ready_empty N
  have he := DistanceCircuit.build_extends N (probePrefix N).circuit
  have hf := (prefix_extends_initial N).trans he
  have hv := ready_extend hr he
  have hp : ∀ p ∈ (probePrefix N).probes, p.valid (probePrefix N).circuit :=
    build_probes_valid N (N-1)
  have hval := compress_value A D b (probePrefix N).probes.length hv.1 hv.2.1
    hv.2.2.1 (DistanceCircuit.build_valid N hr)
    (fun p h => PairRef.valid_extend (hp p h) he)
  rw [one_value A D hf, a_value A D hf, d_value A D hf,
    DistanceCircuit.build_value N A D hr (prefix_extends_initial N)] at hval
  rw [map_values_extend A D he hp, prefix_probe_values N hN A D] at hval
  change (full N b).2.value (full N b).1 A D =
    compressionValue (1, 1) (A, A) (D, D)
      (exprPair A D (Degrees.allOnes N)) b (probePrefix N).probes.length
      ((Degrees.probeList N N).map (exprPair A D)) at hval
  calc
    (full N b).2.value (full N b).1 A D =
      compressionValue (1, 1) (A, A) (D, D)
        (exprPair A D (Degrees.allOnes N)) b (probePrefix N).probes.length
        ((Degrees.probeList N N).map (exprPair A D)) := hval
    _ = _ := by rw [prefix_probe_count N hN, Degrees.probeList_length]

theorem full_output_expr {R : Type*} [Ring R] (N : ℕ) (hN : 1 ≤ N) (b : ℤ) (A D : R) :
    (full N b).2.value (full N b).1 A D =
      exprPair A D (Degrees.factored b (Degrees.allOnes N) (Degrees.probeList N N)) := by
  rw [full_value N hN b A D, compression_expr_pair]

theorem full_output_expr_degree {R : Type*} [Ring R]
    (N : ℕ) (hN : 1 ≤ N) (b : ℤ) (A D : R) :
    (full N b).2.value (full N b).1 A D =
      exprPair A D (Degrees.factored b (Degrees.allOnes N) (Degrees.probeList N N)) ∧
    (Degrees.factored b (Degrees.allOnes N) (Degrees.probeList N N)).degree ≤ 3*N-2 :=
  ⟨full_output_expr N hN b A D, Degrees.literal_packed_degree N hN b⟩

theorem full_output_source {R : Type*} [Ring R] [StarRing R]
    (N : ℕ) (hN : 1 ≤ N) (b : ℤ) (A D : R) (ha : star A = A) (hd : star D = D) :
    ((full N b).2.value (full N b).1 A D).1 =
      RadixFactorization.sourcePolynomial b ((Degrees.allOnes N).eval A D)
        ((Degrees.probeList N N).map (Degrees.Expr.eval A D)).get
        (RadixFactorization.coreSlots A D) := by
  calc
    ((full N b).2.value (full N b).1 A D).1 =
      (Degrees.factored b (Degrees.allOnes N) (Degrees.probeList N N)).eval A D :=
        congrArg Prod.fst (full_output_expr N hN b A D)
    _ = _ := WrittenPolynomialBridge.factored_eq_source b A D ha hd _ _

theorem full_output_integer_polynomial (N : ℕ) (hN : 1 ≤ N) (b : ℤ) :
    ((full N b).2.value (full N b).1
      RadixFactorization.adjacencyGenerator RadixFactorization.degreeGenerator).1 =
      RadixFactorization.sourcePolynomial b
        ((Degrees.allOnes N).eval
          RadixFactorization.adjacencyGenerator RadixFactorization.degreeGenerator)
        ((Degrees.probeList N N).map (Degrees.Expr.eval
          RadixFactorization.adjacencyGenerator RadixFactorization.degreeGenerator)).get
        (RadixFactorization.coreSlots
          RadixFactorization.adjacencyGenerator RadixFactorization.degreeGenerator) :=
  full_output_source N hN b _ _
    RadixFactorization.adjacencyGenerator_self_adjoint
    RadixFactorization.degreeGenerator_self_adjoint

#print axioms full_value
#print axioms full_output_expr_degree
#print axioms full_output_source
#print axioms full_output_integer_polynomial
#print axioms full_gate_bound
#print axioms full_safe
#print axioms full_constants

end CircuitAudit.FullCompression
