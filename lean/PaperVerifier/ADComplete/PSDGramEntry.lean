import PaperVerifier.ADComplete.PSDBirdDeterminant
import PaperVerifier.ADComplete.PSDBirdSafety
import PaperVerifier.ADComplete.PSDBirdDegrees

namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDHomogeneousLift ADComplete.InstructionDegrees

def gramScalar (n : ℕ) (Z W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  dotProduct (Matrix.mulVec Z (fun _ => 1)) (Matrix.mulVec W (fun _ => 1))

theorem gramScalar_symm (n : ℕ) (Z W : Matrix (Fin n) (Fin n) ℝ) :
    gramScalar n Z W = gramScalar n W Z := by
  exact dotProduct_comm _ _

theorem gram_corner_scalar (n : ℕ) (Z W : Matrix (Fin n) (Fin n) ℝ) :
    J n * Z.transpose * W * J n = gramScalar n Z W • J n := by
  rw [gram_corner, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rfl

def AdjointValue (n : ℕ) (a d : Matrix (Fin n) (Fin n) ℝ) (c : Circuit)
    (p : PairRef) (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  p.valid c ∧ p.value c a d = (Z, Z.transpose)

theorem adjoint_extend {n : ℕ} {a d Z : Matrix (Fin n) (Fin n) ℝ}
    {c t : Circuit} {p : PairRef} (h : AdjointValue n a d c p Z) (he : Extends c t) :
    AdjointValue n a d t p Z :=
  ⟨PairRef.valid_extend h.1 he, (PairRef.value_extend h.1 he a d).trans h.2⟩

def gramEntry (j z w : PairRef) (c : Circuit) : Result :=
  let r := pairMul c j z.swap
  let s := pairMul r.1 r.2 w
  pairMul s.1 s.2 j

theorem gramEntry_extends (j z w : PairRef) (c : Circuit) : Extends c (gramEntry j z w c).1 :=
  (pairMul_extends _ _ _).trans ((pairMul_extends _ _ _).trans (pairMul_extends _ _ _))

@[simp] theorem gramEntry_length (j z w : PairRef) (c : Circuit) :
    (gramEntry j z w c).1.length = c.length+6 := by
  simp only [gramEntry, pairMul_length]

theorem gramEntry_valid (j z w : PairRef) (c : Circuit) :
    (gramEntry j z w c).2.valid (gramEntry j z w c).1 := pairMul_valid _ _ _

theorem gramEntry_safe {j z w : PairRef} {c : Circuit}
    (hc : c.safe) (hj : j.valid c) (hz : z.valid c) (hw : w.valid c) :
    (gramEntry j z w c).1.safe := by
  have hr := pairMul_safe hc hj (PairRef.swap_valid hz)
  have er := pairMul_extends c j z.swap
  have hs := pairMul_safe hr (pairMul_valid _ _ _) (PairRef.valid_extend hw er)
  exact pairMul_safe hs (pairMul_valid _ _ _)
    (PairRef.valid_extend hj (er.trans (pairMul_extends _ _ _)))

theorem gramEntry_corner {n : ℕ} {a d Z W : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {j z w : PairRef}
    (hj : Corner n a d c j 1) (hz : AdjointValue n a d c z Z) (hw : AdjointValue n a d c w W) :
    Corner n a d (gramEntry j z w c).1 (gramEntry j z w c).2 (gramScalar n Z W) := by
  let r := pairMul c j z.swap
  let s := pairMul r.1 r.2 w
  have er : Extends c r.1 := pairMul_extends _ _ _
  have es : Extends c s.1 := er.trans (pairMul_extends _ _ _)
  have vr := pairMul_value a d hj.1 (PairRef.swap_valid hz.1)
  rw [hj.2, PairRef.swap_value, hz.2] at vr
  simp only [one_smul] at vr
  have vs := pairMul_value a d (pairMul_valid _ _ _) (PairRef.valid_extend hw.1 er)
  rw [vr, PairRef.value_extend hw.1 er a d, hw.2] at vs
  have vt := pairMul_value a d (pairMul_valid _ _ _) (PairRef.valid_extend hj.1 es)
  rw [vs, PairRef.value_extend hj.1 es a d, hj.2] at vt
  simp only [one_smul, ← Matrix.mul_assoc] at vt
  rw [gram_corner_scalar, gram_corner_scalar, ← gramScalar_symm n Z W] at vt
  exact ⟨gramEntry_valid _ _ _ _, vt⟩

theorem gramEntry_grade {j z w : PairRef} {c : Circuit} {B H : ℕ}
    (hc : AllBound c B) (hj : PairBound c j H) (hz : PairBound c z H) (hw : PairBound c w H)
    (hB : 4*H ≤ B) :
    AllBound (gramEntry j z w c).1 B ∧ PairBound (gramEntry j z w c).1 (gramEntry j z w c).2 (4*H) := by
  have hr := pair_mul hc hj (pair_swap hz) (by omega)
  have er := pairMul_extends c j z.swap
  have hs := pair_mul hr.1 hr.2 (pair_extend hw er) (by omega)
  have ht := pair_mul hs.1 hs.2 (pair_extend hj (er.trans (pairMul_extends _ _ _))) (by omega)
  exact ⟨ht.1, pair_mono ht.2 (by omega)⟩

#print axioms gramEntry_corner
#print axioms gramEntry_grade
end ADComplete.PSDBird
