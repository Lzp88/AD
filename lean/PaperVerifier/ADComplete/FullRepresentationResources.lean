import PaperVerifier.ADComplete.FullRepresentationCompiler
import PaperVerifier.ADComplete.InstructionPolynomial

/-! Literal polynomial, degree and all-register bit bounds for the full
representation compiler. The matrix dimension remains the original order. -/
namespace ADComplete.FullRepresentationCompiler
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit CircuitAudit.Degrees
open CircuitAudit.RadixFactorization ADComplete.IntegerBounds
open scoped Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def polynomial (N : ℕ) (b : ℤ) : IntegerNCPolynomial :=
  ((compiled N b).2.value (compiled N b).1 adjacencyGenerator degreeGenerator).1

theorem polynomial_self_adjoint (N : ℕ) (hN : 1≤N) (b : ℤ) :
    star (polynomial N b)=polynomial N b := by
  have he := congrArg Prod.fst (compiled_value N hN b adjacencyGenerator degreeGenerator)
  change polynomial N b=(expression N b).eval adjacencyGenerator degreeGenerator at he
  rw [he,expression,CircuitAudit.WrittenPolynomialBridge.factored_eq_source b _ _
    adjacencyGenerator_self_adjoint degreeGenerator_self_adjoint]
  exact ADComplete.InstructionDegrees.sourcePolynomial_self_adjoint _ _ _ _

theorem polynomial_evaluation {R : Type*} [Ring R] [Algebra ℤ R] (a d : R) (N : ℕ) (b : ℤ) :
    (FreeAlgebra.lift ℤ (fun x : Bool => if x then d else a)) (polynomial N b)=
      ((compiled N b).2.value (compiled N b).1 a d).1 := by
  let φ := FreeAlgebra.lift ℤ (fun x : Bool => if x then d else a)
  have h := ADComplete.InstructionDegrees.literal_register_hom φ.toRingHom adjacencyGenerator degreeGenerator
    (compiled N b).1 (compiled N b).2.forward
  simpa [φ,polynomial,PairRef.value,adjacencyGenerator,degreeGenerator] using h

theorem expression_degree (N : ℕ) (hN : 1≤N) (b : ℤ) : (expression N b).degree≤2*N^2-1 := by
  have hS : 1≤N^2 := by nlinarith
  let ps := probeList (N^2) (N^2)
  have hp : ∀ p∈ps, p.degree≤N^2-1 := fun p hp => probeList_degree (N^2) (N^2) p hp
  have hbase : (Expr.scale b .one).degree=0 := rfl
  have hbeta := power_degree_zero _ hbase ps.length
  have hgamma := power_degree_zero _ hbeta ps.length
  have hY := horner_degree _ hbase ps (N^2-1) hp
  have hZ := horner_degree _ hbeta ps (N^2-1) hp
  change (factored b .one ps).degree≤2*N^2-1
  simp only [factored,Expr.degree,reverse_degree,hgamma,zero_add,add_zero,
    Nat.max_self,Nat.max_eq_right (by omega : (0 : ℕ)≤1)]
  omega

theorem compiled_all_weights (N : ℕ) (hN : 1≤N) (b : ℤ) :
    ADComplete.InstructionHeights.AllBound (compiled N b).1 (20*N^8) := by
  let S := N^2
  have hS : 1≤S := by dsimp [S]; nlinarith
  let M := (probePrefix S).probes.length
  let T := 2*(3*(S-1))+3*(M*M)+3*M+4
  have gp := ADComplete.InstructionHeights.probe_build_grade S (S-1)
  have hi := ADComplete.InstructionHeights.initial_grade_extend ADComplete.InstructionHeights.initial_grade
    (build_extends S (S-1))
  have hp : ADComplete.InstructionHeights.AllBound (probePrefix S).circuit T :=
    ADComplete.InstructionHeights.all_mono gp.1 (by dsimp [T]; omega)
  have hg := ADComplete.InstructionHeights.compress_grade (J := 0)
    (by simpa only [zero_add,T,M,probePrefix] using hp) hi.1 hi.2.1 hi.2.2.1 hi.1
    (probePrefix S).probes rfl gp.2.2 b
  have hM : M≤S^2 := ADComplete.InstructionHeights.prefix_count_le_square S hS
  have hM2 : M*M≤S^2*S^2 := Nat.mul_le_mul hM hM
  have h14 : S≤S^4 := by simpa using Nat.pow_le_pow_right hS (show 1≤4 by decide)
  have h24 : S^2≤S^4 := Nat.pow_le_pow_right hS (by decide)
  have h04 : 1≤S^4 := Nat.one_le_pow _ _ hS
  have hT : T≤20*S^4 := by dsimp [T]; nlinarith [Nat.sub_le S 1]
  have hh := ADComplete.InstructionHeights.all_mono hg.1
    (show 0+2*(3*(S-1))+3*(M*M)+3*M+4≤20*S^4 by simpa only [zero_add,T] using hT)
  simpa only [compiled,S,probePrefix,zero_add,←pow_mul,show 2*4=8 by decide] using hh

theorem compiled_scalar_constants (N : ℕ) (b : ℤ) :
    (compiled N b).1.constantsAllowed (CircuitAudit.FullCompression.scalarConstants (N^2) b) := by
  apply compress_constants
  · apply ADComplete.InstructionHeights.constants_mono (prefix_constants (N^2))
    intro z hz
    exact Or.inr (Or.inr hz)
  · exact Or.inl rfl

theorem compiled_constants_bound (N : ℕ) (hN : 1≤N) :
    (compiled N (radixNat (N^2))).1.constantsAllowed
      {z | |(z : ℝ)|≤(ADComplete.InstructionHeights.KNat (N^2) : ℝ)} := by
  apply ADComplete.InstructionHeights.constants_mono (compiled_scalar_constants N (radixNat (N^2)))
  intro z hz
  have hS : 1≤N^2 := by nlinarith
  have hh := CircuitAudit.FullCompression.scalarConstants_abs_bound (N^2) hS (radixNat (N^2)) hz
  have hb0 : 0≤(radixNat (N^2) : ℤ) := Nat.cast_nonneg _
  have hb : |z|≤(ADComplete.InstructionHeights.KNat (N^2) : ℤ) := by
    apply hh.trans
    unfold ADComplete.InstructionHeights.KNat
    push_cast
    rw [abs_of_nonneg hb0]
    apply max_le
    · have hn0 : (0 : ℤ)≤(N : ℤ)^2 := sq_nonneg _
      nlinarith [pow_nonneg hn0 3]
    · omega
  change |(z : ℝ)|≤_
  exact_mod_cast hb

theorem compiled_scalar_labels_bits (N : ℕ) (hN : 1≤N) :
    (compiled N (radixNat (N^2))).1.constantsAllowed {z | Nat.size z.natAbs≤16*N^4+1} := by
  apply ADComplete.InstructionHeights.constants_mono (compiled_constants_bound N hN)
  intro z hz
  change |(z : ℝ)|≤(ADComplete.InstructionHeights.KNat (N^2) : ℝ) at hz
  rw [←Int.cast_abs,←Int.natCast_natAbs] at hz
  have hn : z.natAbs≤ADComplete.InstructionHeights.KNat (N^2) := by exact_mod_cast hz
  have hS : 1≤N^2 := by nlinarith
  have hh := ADComplete.InstructionHeights.KNat_binary_bound (N^2) hS
  have he : (N^2)^2=N^4 := by ring
  rw [he] at hh
  change Nat.size z.natAbs≤16*N^4+1
  simpa only [Nat.size_pow] using Nat.size_le_size (hn.trans hh)

theorem actual_register_entry_bits {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) (hN : 1≤N)
    (hn : Fintype.card V≤N) (i : ℕ) (hi : i<(compiled N (radixNat (N^2))).1.length) (u v : V) :
    Nat.size ((compiled N (radixNat (N^2))).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs≤320*N^12+1 := by
  have hS : 1≤N^2 := by nlinarith
  have hnS : Fintype.card V≤N^2 := hn.trans (by nlinarith)
  have hk2 : (2 : ℝ)≤ADComplete.InstructionHeights.KNat (N^2) := by
    exact_mod_cast ADComplete.InstructionHeights.KNat_two_le (N^2)
  have hnk : (N^2 : ℕ)≤ADComplete.InstructionHeights.KNat (N^2) := by
    have h13 : N^2≤(N^2)^3 := by simpa using Nat.pow_le_pow_right hS (show 1≤3 by decide)
    unfold ADComplete.InstructionHeights.KNat
    omega
  have hnkr : ((N^2 : ℕ) : ℝ)≤ADComplete.InstructionHeights.KNat (N^2) := by exact_mod_cast hnk
  have hh := ADComplete.InstructionHeights.every_register_norm_bound _ hk2 (G.adjMatrix ℤ) (G.degMatrix ℤ)
    ((adjacency_norm_bound G (N^2) hnS).trans hnkr) ((degree_norm_bound G (N^2) hnS).trans hnkr)
    (compiled N (radixNat (N^2))).1 (compiled_constants_bound N hN) i
  have hkb : (ADComplete.InstructionHeights.KNat (N^2) : ℝ)≤(2 : ℝ)^(16*N^4) := by
    have hb := ADComplete.InstructionHeights.KNat_binary_bound (N^2) hS
    have he : (N^2)^2=N^4 := by ring
    rw [he] at hb
    exact_mod_cast hb
  have hnrm : ‖(compiled N (radixNat (N^2))).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i‖≤(2 : ℝ)^(320*N^12) := by
    calc
      _ ≤ (ADComplete.InstructionHeights.KNat (N^2) : ℝ)^(ADComplete.InstructionHeights.weight (compiled N (radixNat (N^2))).1 i) := hh
      _ ≤ (ADComplete.InstructionHeights.KNat (N^2) : ℝ)^(20*N^8) :=
        pow_le_pow_right₀ (by linarith) (compiled_all_weights N hN _ i hi)
      _ ≤ ((2 : ℝ)^(16*N^4))^(20*N^8) := pow_le_pow_left₀ (by positivity) hkb _
      _ = _ := by rw [←pow_mul]; congr 1; ring
  have he := (ADComplete.InstructionHeights.entry_norm_le_opNorm _ u v).trans hnrm
  rw [Int.norm_eq_abs,←Int.cast_abs,←Int.natCast_natAbs] at he
  have he' : ((compiled N (radixNat (N^2))).1.value (G.adjMatrix ℤ) (G.degMatrix ℤ) i u v).natAbs≤2^(320*N^12) := by
    exact_mod_cast he
  simpa only [Nat.size_pow] using Nat.size_le_size he'

#print axioms polynomial_self_adjoint
#print axioms polynomial_evaluation
#print axioms expression_degree
#print axioms compiled_scalar_labels_bits
#print axioms actual_register_entry_bits
end
end ADComplete.FullRepresentationCompiler
