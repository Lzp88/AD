import PaperVerifier.ADComplete.PSDBirdHeights
import PaperVerifier.ADComplete.PSDFactoryDegrees

namespace ADComplete.PSDOperationHeight
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDBird ADComplete.PSDFoldCompiler ADComplete.InstructionHeights
open ADComplete.PSDBirdHeight

theorem foldOne_height {τ i : ℕ} {one : PairRef} {ps : List PairRef} {c : Circuit} {B P F : ℕ}
    (hb : AllBound c B) (ho : PairBound c one 0) (hp : ∀ p∈ps, PairBound c p P)
    (hF : P+2*ps.length≤F) (h1 : 1≤B) (hB : F≤B) :
    AllBound (foldOne τ one ps i c).1 B ∧ PairBound (foldOne τ one ps i c).1 (foldOne τ one ps i c).2 F := by
  unfold foldOne
  split
  · exact ⟨hb,pair_mono ho (Nat.zero_le _)⟩
  · have he := scalarBase_extends c one (scalar τ i)
    have hs := scalar_grade hb ho h1 (scalar τ i)
    have hh := horner_grade ps hs.1 hs.2 (fun p h => pair_extend (hp p h) he) (by omega)
    exact ⟨hh.1,pair_mono hh.2 (by omega)⟩

theorem foldScan_height {N τ : ℕ} {one : PairRef} {ps : List PairRef} {c : Circuit}
    {O : Fin N → PairRef} {B P F : ℕ} (hb : AllBound c B) (ho : PairBound c one 0)
    (hp : ∀ p∈ps, PairBound c p P) (hO : ∀ i, PairBound c (O i) F)
    (hF : P+2*ps.length≤F) (h1 : 1≤B) (hB : F≤B) (is : List (Fin N)) :
    AllBound (PSDFoldCompiler.scan τ one ps c O is).1 B ∧
      ∀ i, PairBound (PSDFoldCompiler.scan τ one ps c O is).1 ((PSDFoldCompiler.scan τ one ps c O is).2 i) F := by
  induction is generalizing c O with
  | nil => exact ⟨hb,hO⟩
  | cons i is ih =>
    have he := foldOne_extends τ one ps i c
    have hr := foldOne_height (τ := τ) (i := i) hb ho hp hF h1 hB
    have hw : ∀ j, PairBound (foldOne τ one ps i c).1 (PSDFoldCompiler.write O i (foldOne τ one ps i c).2 j) F := by
      intro j
      unfold PSDFoldCompiler.write
      split
      · exact hr.2
      · exact pair_extend (hO j) he
    exact ih hr.1 (pair_extend ho he) (fun p h => pair_extend (hp p h) he) hw

theorem foldStage_height {N τ : ℕ} {one : PairRef} {ps : List PairRef} {c : Circuit} {B P F : ℕ}
    (hb : AllBound c B) (ho : PairBound c one 0) (hp : ∀ p∈ps, PairBound c p P)
    (hF : P+2*ps.length≤F) (h1 : 1≤B) (hB : F≤B) :
    AllBound (PSDFoldCompiler.stage N τ one ps c).1 B ∧
      ∀ i, PairBound (PSDFoldCompiler.stage N τ one ps c).1 ((PSDFoldCompiler.stage N τ one ps c).2 i) F :=
  foldScan_height hb ho hp (fun _ => pair_mono ho (Nat.zero_le _)) hF h1 hB _

theorem gramEntry_height {j z w : PairRef} {c : Circuit} {B F : ℕ}
    (hb : AllBound c B) (hj : PairBound c j F) (hz : PairBound c z F) (hw : PairBound c w F) (hB : 4*F≤B) :
    AllBound (gramEntry j z w c).1 B ∧ PairBound (gramEntry j z w c).1 (gramEntry j z w c).2 (4*F) := by
  have hr := pair_mul hb hj (pair_swap hz) (by omega)
  have er := pairMul_extends c j z.swap
  have hs := pair_mul hr.1 hr.2 (pair_extend hw er) (by omega)
  have ht := pair_mul hs.1 hs.2 (pair_extend hj (er.trans (pairMul_extends _ _ _))) (by omega)
  exact ⟨ht.1,pair_mono ht.2 (by omega)⟩

theorem gramScan_height {k : ℕ} {j : PairRef} {Z : Fin k → PairRef} {c : Circuit}
    {O : Matrix (Fin k) (Fin k) PairRef} {B F : ℕ}
    (hb : AllBound c B) (hj : PairBound c j F) (hZ : ∀ i, PairBound c (Z i) F)
    (hO : WeightedRefs c O (4*F)) (hB : 4*F≤B) (es : List (Fin k×Fin k)) :
    AllBound (gramScan j Z c O es).1 B ∧ WeightedRefs (gramScan j Z c O es).1 (gramScan j Z c O es).2 (4*F) := by
  induction es generalizing c O with
  | nil => exact ⟨hb,hO⟩
  | cons e es ih =>
    have he := gramEntry_extends j (Z e.1) (Z e.2) c
    have hr := gramEntry_height hb hj (hZ e.1) (hZ e.2) hB
    have hw : WeightedRefs (gramEntry j (Z e.1) (Z e.2) c).1 (PSDBird.write O e (gramEntry j (Z e.1) (Z e.2) c).2) (4*F) := by
      intro i l
      unfold PSDBird.write
      split
      · exact hr.2
      · exact pair_extend (hO i l) he
    exact ih hr.1 (pair_extend hj he) (fun i => pair_extend (hZ i) he) hw

theorem gramStage_height {k : ℕ} {j : PairRef} {Z : Fin k → PairRef} {c : Circuit} {B F : ℕ}
    (hb : AllBound c B) (hj : PairBound c j F) (hZ : ∀ i, PairBound c (Z i) F) (hB : 4*F≤B) :
    AllBound (gramStage j Z c).1 B ∧ WeightedRefs (gramStage j Z c).1 (gramStage j Z c).2 (4*F) := by
  have hz := pair_zero hb
  have he := pairZero_extends c
  exact gramScan_height hz.1 (pair_extend hj he) (fun i => pair_extend (hZ i) he)
    (fun _ _ => pair_mono hz.2 (Nat.zero_le _)) hB _

def detHeight (k D : ℕ) : ℕ := D+k*(D+(k+1)+2)+1

theorem cramerVariants_height {k : ℕ} {c : Circuit}
    {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {b : Fin (k+1) → PairRef} {D : ℕ}
    (hA : WeightedRefs c A D) (hb : ∀ i, PairBound c (b i) D) :
    ∀ r, WeightedRefs c (cramerVariants A b r) D := by
  intro r
  induction r using Fin.cases with
  | zero => exact hA
  | succ r =>
    intro i j
    by_cases hj : j=r
    · subst j; simpa [cramerVariants] using hb i
    · simpa [cramerVariants,Matrix.updateCol_apply,hj] using hA i j

theorem determinantScan_height {k m : ℕ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {c : Circuit} {O : Fin m → PairRef} {B D : ℕ}
    (hb : AllBound c B) (hA : ∀ i, WeightedRefs c (A i) D)
    (hO : ∀ i, PairBound c (O i) (detHeight k D)) (hB : detHeight k D≤B) (is : List (Fin m)) :
    AllBound (determinantScan A c O is).1 B ∧
      ∀ i, PairBound (determinantScan A c O is).1 ((determinantScan A c O is).2 i) (detHeight k D) := by
  induction is generalizing c O with
  | nil => exact ⟨hb,hO⟩
  | cons i is ih =>
    have he := compiler_extends k (A i) c
    have hr := compiler_height k D hb (hA i) hB
    have hw : ∀ j, PairBound (compiler k (A i) c).1 (vectorWrite O i (compiler k (A i) c).2 j) (detHeight k D) := by
      intro j
      unfold vectorWrite
      split
      · exact hr.2
      · exact pair_extend (hO j) he
    exact ih hr.1 (fun i => weighted_extend (hA i) he) hw

theorem determinantBatch_height {k m : ℕ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {c : Circuit} {B D : ℕ}
    (hb : AllBound c B) (hA : ∀ i, WeightedRefs c (A i) D) (hB : detHeight k D≤B) :
    AllBound (determinantBatch A c).1 B ∧
      ∀ i, PairBound (determinantBatch A c).1 ((determinantBatch A c).2 i) (detHeight k D) := by
  have hz := pair_zero hb
  have he := pairZero_extends c
  exact determinantScan_height hz.1 (fun i => weighted_extend (hA i) he)
    (fun _ => pair_mono hz.2 (Nat.zero_le _)) hB _

theorem productSum_height {ι : Type*} {Z D : ι → PairRef} {c : Circuit} {B P Q : ℕ}
    (hb : AllBound c B) (hZ : ∀ i, PairBound c (Z i) P) (hD : ∀ i, PairBound c (D i) Q)
    (is : List ι) (hB : P+Q+is.length≤B) :
    AllBound (productSum Z D c is).1 B ∧ PairBound (productSum Z D c is).1 (productSum Z D c is).2 (P+Q+is.length) := by
  induction is with
  | nil => have hz := pair_zero hb; exact ⟨hz.1,pair_mono hz.2 (by omega)⟩
  | cons i is ih =>
    have hr := ih (by simp only [List.length_cons] at hB; omega)
    have he := productSum_extends Z D c is
    have ht := pair_mul hr.1 (pair_extend (hZ i) he) (pair_extend (hD i) he) (by simp only [List.length_cons] at hB; omega)
    have hs := pair_add ht.1 ht.2 (pair_extend hr.2 (pairMul_extends _ _ _)) (by simp only [List.length_cons] at hB; omega)
    exact ⟨hs.1,pair_mono hs.2 (by simp only [List.length_cons]; omega)⟩

theorem residual_height {k : ℕ} {z δ : PairRef} {Z D : Fin k → PairRef} {c : Circuit} {B P Q : ℕ}
    (hb : AllBound c B) (hz : PairBound c z P) (hδ : PairBound c δ Q)
    (hZ : ∀ i, PairBound c (Z i) P) (hD : ∀ i, PairBound c (D i) Q) (hB : P+Q+k+2≤B) :
    AllBound (residual z δ Z D c).1 B ∧ PairBound (residual z δ Z D c).1 (residual z δ Z D c).2 (P+Q+k+2) := by
  have hr := productSum_height hb hZ hD (List.finRange k) (by simpa only [List.length_finRange] using (show P+Q+k≤B by omega))
  have er := productSum_extends Z D c (List.finRange k)
  have hn := pair_scale hr.1 hr.2 (by simp only [List.length_finRange]; omega) (-1)
  have en := er.trans (pairScale_extends (productSum Z D c (List.finRange k)).1 (-1) (productSum Z D c (List.finRange k)).2)
  have ht := pair_mul hn.1 (pair_extend hz en) (pair_extend hδ en) (by omega)
  have hs := pair_add ht.1 ht.2 (pair_extend hn.2 (pairMul_extends _ _ _)) (by simp only [List.length_finRange]; omega)
  exact ⟨hs.1,pair_mono hs.2 (by simp only [List.length_finRange]; omega)⟩

#print axioms foldStage_height
#print axioms determinantBatch_height
#print axioms residual_height
end ADComplete.PSDOperationHeight
