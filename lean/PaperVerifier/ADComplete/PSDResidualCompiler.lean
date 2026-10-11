import PaperVerifier.ADComplete.PSDGramCompiler

namespace ADComplete.PSDBird
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.InstructionDegrees

theorem adjoint_zero (n : ℕ) (a d : Matrix (Fin n) (Fin n) ℝ) (c : Circuit) :
    AdjointValue n a d (pairZero c).1 (pairZero c).2 0 := by
  exact ⟨pairZero_valid _, by simp⟩

theorem adjoint_add {n : ℕ} {a d Z W : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p q : PairRef} (hp : AdjointValue n a d c p Z) (hq : AdjointValue n a d c q W) :
    AdjointValue n a d (pairAdd c p q).1 (pairAdd c p q).2 (Z+W) := by
  refine ⟨pairAdd_valid _ _ _, ?_⟩
  rw [pairAdd_value a d hp.1 hq.1, hp.2, hq.2]
  simp only [Matrix.transpose_add]

theorem adjoint_scale {n : ℕ} {a d Z : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p : PairRef} (hp : AdjointValue n a d c p Z) (k : ℤ) :
    AdjointValue n a d (pairScale c k p).1 (pairScale c k p).2 (k • Z) := by
  refine ⟨pairScale_valid _ _ _, ?_⟩
  rw [pairScale_value a d hp.1, hp.2]
  simp only [Matrix.transpose_smul]

theorem adjoint_mul {n : ℕ} {a d Z W : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p q : PairRef} (hp : AdjointValue n a d c p Z) (hq : AdjointValue n a d c q W) :
    AdjointValue n a d (pairMul c p q).1 (pairMul c p q).2 (Z*W) := by
  refine ⟨pairMul_valid _ _ _, ?_⟩
  rw [pairMul_value a d hp.1 hq.1, hp.2, hq.2]
  simp only [Matrix.transpose_mul]

theorem adjoint_swap {n : ℕ} {a d Z : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p : PairRef} (hp : AdjointValue n a d c p Z) :
    AdjointValue n a d c p.swap Z.transpose := by
  exact ⟨PairRef.swap_valid hp.1, by rw [PairRef.swap_value, hp.2, Matrix.transpose_transpose]⟩

def productSum {ι : Type*} (Z D : ι → PairRef) (c : Circuit) : List ι → Result
  | [] => pairZero c
  | i::is =>
    let r := productSum Z D c is
    let t := pairMul r.1 (Z i) (D i)
    pairAdd t.1 t.2 r.2

theorem productSum_extends {ι : Type*} (Z D : ι → PairRef) (c : Circuit) (is : List ι) :
    Extends c (productSum Z D c is).1 := by
  induction is with
  | nil => exact pairZero_extends c
  | cons i is ih => exact ih.trans ((pairMul_extends _ _ _).trans (pairAdd_extends _ _ _))

@[simp] theorem productSum_length {ι : Type*} (Z D : ι → PairRef) (c : Circuit) (is : List ι) :
    (productSum Z D c is).1.length=c.length+1+4*is.length := by
  induction is with
  | nil => simp [productSum]
  | cons i is ih => simp only [productSum, pairAdd_length, pairMul_length, ih, List.length_cons]; omega

theorem productSum_valid {ι : Type*} (Z D : ι → PairRef) (c : Circuit) (is : List ι) :
    (productSum Z D c is).2.valid (productSum Z D c is).1 := by
  cases is
  · exact pairZero_valid _
  · exact pairAdd_valid _ _ _

theorem productSum_adjoint {ι : Type*} {n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {Z D : ι → PairRef} {z δ : ι → Matrix (Fin n) (Fin n) ℝ} {c : Circuit}
    (hZ : ∀ i, AdjointValue n a d c (Z i) (z i)) (hD : ∀ i, AdjointValue n a d c (D i) (δ i))
    (is : List ι) :
    AdjointValue n a d (productSum Z D c is).1 (productSum Z D c is).2
      ((is.map (fun i => z i*δ i)).sum) := by
  induction is with
  | nil => simpa only [productSum, List.map_nil, List.sum_nil] using adjoint_zero n a d c
  | cons i is ih =>
    have ex := productSum_extends Z D c is
    have ht := adjoint_mul (adjoint_extend (hZ i) ex) (adjoint_extend (hD i) ex)
    have hs := adjoint_add ht (adjoint_extend ih (pairMul_extends _ _ _))
    simpa only [productSum, List.map_cons, List.sum_cons] using hs

theorem productSum_safe_grade {ι : Type*} {Z D : ι → PairRef} {c : Circuit} {B P Q : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hZ : ∀ i, PairBound c (Z i) P)
    (hD : ∀ i, PairBound c (D i) Q) (hPQ : P+Q ≤ B) (is : List ι) :
    (productSum Z D c is).1.safe ∧ AllBound (productSum Z D c is).1 B ∧
      PairBound (productSum Z D c is).1 (productSum Z D c is).2 (P+Q) := by
  induction is with
  | nil =>
    have hz := pair_zero hb
    exact ⟨pairZero_safe hc,hz.1,pair_mono hz.2 (Nat.zero_le _)⟩
  | cons i is ih =>
    have ex := productSum_extends Z D c is
    have gt := pair_mul ih.2.1 (pair_extend (hZ i) ex) (pair_extend (hD i) ex) hPQ
    have ht := pairMul_safe ih.1 (PairRef.valid_extend (hZ i).1 ex) (PairRef.valid_extend (hD i).1 ex)
    have gs := pair_add gt.1 gt.2 (pair_extend ih.2.2 (pairMul_extends _ _ _))
      (by simpa only [max_self] using hPQ)
    have hs := pairAdd_safe ht gt.2.1 (PairRef.valid_extend ih.2.2.1 (pairMul_extends _ _ _))
    simpa only [productSum, max_self] using And.intro hs gs

def residual {k : ℕ} (z δ : PairRef) (Z D : Fin k → PairRef) (c : Circuit) : Result :=
  let r := productSum Z D c (List.finRange k)
  let neg := pairScale r.1 (-1) r.2
  let t := pairMul neg.1 z δ
  pairAdd t.1 t.2 neg.2

theorem residual_extends {k : ℕ} (z δ : PairRef) (Z D : Fin k → PairRef) (c : Circuit) :
    Extends c (residual z δ Z D c).1 :=
  (productSum_extends _ _ _ _).trans ((pairScale_extends _ _ _).trans
    ((pairMul_extends _ _ _).trans (pairAdd_extends _ _ _)))

theorem residual_length {k : ℕ} (z δ : PairRef) (Z D : Fin k → PairRef) (c : Circuit) :
    (residual z δ Z D c).1.length=c.length+4*k+7 := by
  simp only [residual, pairAdd_length, pairMul_length, pairScale_length, productSum_length, List.length_finRange]
  omega

theorem residual_adjoint {k n : ℕ} {a d zk δk : Matrix (Fin n) (Fin n) ℝ}
    {z δ : PairRef} {Z D : Fin k → PairRef} {zi δi : Fin k → Matrix (Fin n) (Fin n) ℝ} {c : Circuit}
    (hz : AdjointValue n a d c z zk) (hδ : AdjointValue n a d c δ δk)
    (hZ : ∀ i, AdjointValue n a d c (Z i) (zi i)) (hD : ∀ i, AdjointValue n a d c (D i) (δi i)) :
    AdjointValue n a d (residual z δ Z D c).1 (residual z δ Z D c).2
      (zk*δk-∑ i, zi i*δi i) := by
  let r := productSum Z D c (List.finRange k)
  have er : Extends c r.1 := productSum_extends _ _ _ _
  have en := er.trans (pairScale_extends r.1 (-1) r.2)
  have hr := productSum_adjoint hZ hD (List.finRange k)
  have hn := adjoint_scale hr (-1)
  have ht := adjoint_mul (adjoint_extend hz en) (adjoint_extend hδ en)
  have hs := adjoint_add ht (adjoint_extend hn (pairMul_extends _ _ _))
  rw [← List.sum_toFinset (fun i => zi i*δi i) (List.nodup_finRange k), List.toFinset_finRange] at hs
  simpa only [residual, r, neg_one_zsmul, sub_eq_add_neg] using hs

theorem residual_safe_grade {k : ℕ} {z δ : PairRef} {Z D : Fin k → PairRef} {c : Circuit} {B P Q : ℕ}
    (hc : c.safe) (hb : AllBound c B) (hz : PairBound c z P) (hδ : PairBound c δ Q)
    (hZ : ∀ i, PairBound c (Z i) P) (hD : ∀ i, PairBound c (D i) Q) (hPQ : P+Q ≤ B) :
    (residual z δ Z D c).1.safe ∧ AllBound (residual z δ Z D c).1 B ∧
      PairBound (residual z δ Z D c).1 (residual z δ Z D c).2 (P+Q) := by
  have hr := productSum_safe_grade hc hb hZ hD hPQ (List.finRange k)
  have er := productSum_extends Z D c (List.finRange k)
  have hn := pair_scale hr.2.1 hr.2.2 hPQ (-1)
  have hns := pairScale_safe hr.1 hr.2.2.1 (-1)
  have en := er.trans (pairScale_extends (productSum Z D c (List.finRange k)).1 (-1)
    (productSum Z D c (List.finRange k)).2)
  have ht := pair_mul hn.1 (pair_extend hz en) (pair_extend hδ en) hPQ
  have hts := pairMul_safe hns (PairRef.valid_extend hz.1 en) (PairRef.valid_extend hδ.1 en)
  have hs := pair_add ht.1 ht.2 (pair_extend hn.2 (pairMul_extends _ _ _))
    (by simpa only [max_self] using hPQ)
  have hss := pairAdd_safe hts ht.2.1 (PairRef.valid_extend hn.2.1 (pairMul_extends _ _ _))
  simpa only [residual, max_self] using And.intro hss hs

#print axioms residual_adjoint
#print axioms residual_safe_grade
end ADComplete.PSDBird
