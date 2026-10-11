import PaperVerifier.ADComplete.PSDFactoryDefinition

/-! Actual reverse-register semantics over every star ring. In particular,
these proofs apply to the integer free algebra and to arbitrary symmetric
real matrix inputs, without the tree-specific Gram-corner identity. -/

namespace ADComplete.PSDPairStar
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit ADComplete.PSDBird

variable {R : Type*} [Ring R] [StarRing R]

def StarPair (a d : R) (c : Circuit) (p : PairRef) : Prop :=
  p.valid c ∧ (p.value c a d).2 = star (p.value c a d).1

variable {a d : R} {c t : Circuit} {p q : PairRef}

theorem extend (hp : StarPair a d c p) (he : Extends c t) : StarPair a d t p := by
  exact ⟨PairRef.valid_extend hp.1 he, by rw [PairRef.value_extend hp.1 he]; exact hp.2⟩

theorem zero (a d : R) (c : Circuit) :
    StarPair a d (pairZero c).1 (pairZero c).2 := by
  exact ⟨pairZero_valid _, by simp⟩

theorem add (hp : StarPair a d c p) (hq : StarPair a d c q) :
    StarPair a d (pairAdd c p q).1 (pairAdd c p q).2 := by
  refine ⟨pairAdd_valid _ _ _, ?_⟩
  rw [pairAdd_value a d hp.1 hq.1]
  simpa only [Prod.fst, Prod.snd, star_add] using congrArg₂ (· + ·) hp.2 hq.2

theorem mul (hp : StarPair a d c p) (hq : StarPair a d c q) :
    StarPair a d (pairMul c p q).1 (pairMul c p q).2 := by
  refine ⟨pairMul_valid _ _ _, ?_⟩
  rw [pairMul_value a d hp.1 hq.1]
  simpa only [Prod.fst, Prod.snd, star_mul] using congrArg₂ (· * ·) hq.2 hp.2

theorem scale (hp : StarPair a d c p) (k : ℤ) :
    StarPair a d (pairScale c k p).1 (pairScale c k p).2 := by
  refine ⟨pairScale_valid _ _ _, ?_⟩
  rw [pairScale_value a d hp.1]
  simpa only [Prod.fst, Prod.snd, star_zsmul] using congrArg (k • ·) hp.2

theorem swap (hp : StarPair a d c p) : StarPair a d c p.swap := by
  refine ⟨PairRef.swap_valid hp.1, ?_⟩
  rw [PairRef.swap_value, hp.2, star_star]

theorem diagSum_star {k : ℕ} {F : Matrix (Fin k) (Fin k) PairRef}
    (hF : ∀ i j, StarPair a d c (F i j)) (ls : List (Fin k)) :
    StarPair a d (diagSum F c ls).1 (diagSum F c ls).2 := by
  induction ls with
  | nil => exact zero a d c
  | cons l ls ih => exact add (extend (hF l l) (diagSum_extends F c ls)) ih

theorem offSum_star {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef}
    (hA : ∀ i j, StarPair a d c (A i j)) (hF : ∀ i j, StarPair a d c (F i j))
    (i j : Fin k) (ls : List (Fin k)) :
    StarPair a d (offSum A F i j c ls).1 (offSum A F i j c ls).2 := by
  induction ls with
  | nil => exact zero a d c
  | cons l ls ih =>
      have ex := offSum_extends A F i j c ls
      have hm := mul (extend (hF i l) ex) (extend (hA l j) ex)
      exact add hm (extend ih (pairMul_extends _ _ _))

theorem entry_star {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef}
    (hA : ∀ i j, StarPair a d c (A i j)) (hF : ∀ i j, StarPair a d c (F i j))
    (i j : Fin k) : StarPair a d (entry A F i j c).1 (entry A F i j c).2 := by
  let ds := diagSum F c (upper k i)
  let neg := pairScale ds.1 (-1) ds.2
  let l := pairMul neg.1 neg.2 (A i j)
  let r := offSum A F i j l.1 (upper k i)
  have eds : Extends c ds.1 := diagSum_extends F c _
  have eneg : Extends c neg.1 := eds.trans (pairScale_extends _ _ _)
  have el : Extends c l.1 := eneg.trans (pairMul_extends _ _ _)
  have er : Extends l.1 r.1 := offSum_extends A F i j _ _
  have hds := diagSum_star hF (upper k i)
  have hneg := scale hds (-1)
  have hl := mul hneg (extend (hA i j) eneg)
  have hr := offSum_star (fun i j => extend (hA i j) el)
    (fun i j => extend (hF i j) el) i j (upper k i)
  exact add (extend hl er) hr

theorem scan_star {k : ℕ} {A F O : Matrix (Fin k) (Fin k) PairRef}
    (hA : ∀ i j, StarPair a d c (A i j)) (hF : ∀ i j, StarPair a d c (F i j))
    (hO : ∀ i j, StarPair a d c (O i j)) (es : List (Fin k × Fin k)) :
    ∀ i j, StarPair a d (scan A F c O es).1 ((scan A F c O es).2 i j) := by
  induction es generalizing c O with
  | nil => exact hO
  | cons e es ih =>
      let r := entry A F e.1 e.2 c
      have he : Extends c r.1 := entry_extends A F e.1 e.2 c
      have hr := entry_star hA hF e.1 e.2
      have hw : ∀ i j, StarPair a d r.1 (write O e r.2 i j) := by
        intro i j
        by_cases hij : (i,j)=e
        · obtain rfl : e=(i,j) := hij.symm
          simpa only [write, ite_true] using hr
        · simpa only [write, hij, ite_false] using extend (hO i j) he
      exact ih (fun i j => extend (hA i j) he) (fun i j => extend (hF i j) he) hw

theorem stage_star {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef}
    (hA : ∀ i j, StarPair a d c (A i j)) (hF : ∀ i j, StarPair a d c (F i j)) :
    ∀ i j, StarPair a d (stage A F c).1 ((stage A F c).2 i j) := by
  have he := pairZero_extends c
  exact scan_star (fun i j => extend (hA i j) he) (fun i j => extend (hF i j) he)
    (fun _ _ => zero a d c) (allPairs k)

theorem iterate_star {k : ℕ} {A F : Matrix (Fin k) (Fin k) PairRef}
    (hA : ∀ i j, StarPair a d c (A i j)) (hF : ∀ i j, StarPair a d c (F i j))
    (t : ℕ) : ∀ i j, StarPair a d (iterate A t c F).1 ((iterate A t c F).2 i j) := by
  induction t generalizing c F with
  | zero => exact hF
  | succ t ih =>
      exact ih (fun i j => extend (hA i j) (stage_extends A F c)) (stage_star hA hF)

theorem compiler_star {k : ℕ} {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    (hA : ∀ i j, StarPair a d c (A i j)) :
    StarPair a d (compiler k A c).1 (compiler k A c).2 :=
  scale (iterate_star hA hA k 0 0) _

theorem gramEntry_star {j z w : PairRef}
    (hj : StarPair a d c j) (hz : StarPair a d c z) (hw : StarPair a d c w) :
    StarPair a d (gramEntry j z w c).1 (gramEntry j z w c).2 := by
  have hr := mul hj (swap hz)
  have er := pairMul_extends c j z.swap
  have hs := mul hr (extend hw er)
  exact mul hs (extend hj (er.trans (pairMul_extends _ _ _)))

theorem gramScan_star {k : ℕ} {j : PairRef} {Z : Fin k → PairRef}
    {O : Matrix (Fin k) (Fin k) PairRef} (hj : StarPair a d c j)
    (hZ : ∀ i, StarPair a d c (Z i)) (hO : ∀ i l, StarPair a d c (O i l))
    (es : List (Fin k × Fin k)) :
    ∀ i l, StarPair a d (gramScan j Z c O es).1 ((gramScan j Z c O es).2 i l) := by
  induction es generalizing c O with
  | nil => exact hO
  | cons e es ih =>
      let r := gramEntry j (Z e.1) (Z e.2) c
      have he : Extends c r.1 := gramEntry_extends _ _ _ _
      have hr := gramEntry_star hj (hZ e.1) (hZ e.2)
      have hw : ∀ i l, StarPair a d r.1 (write O e r.2 i l) := by
        intro i l
        by_cases hil : (i,l)=e
        · obtain rfl : e=(i,l) := hil.symm
          simpa only [write, ite_true] using hr
        · simpa only [write, hil, ite_false] using extend (hO i l) he
      exact ih (extend hj he) (fun i => extend (hZ i) he) hw

theorem gramStage_star {k : ℕ} {j : PairRef} {Z : Fin k → PairRef}
    (hj : StarPair a d c j) (hZ : ∀ i, StarPair a d c (Z i)) :
    ∀ i l, StarPair a d (gramStage j Z c).1 ((gramStage j Z c).2 i l) := by
  have he := pairZero_extends c
  exact gramScan_star (extend hj he) (fun i => extend (hZ i) he)
    (fun _ _ => zero a d c) (allPairs k)

theorem determinantScan_star {k m : ℕ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {O : Fin m → PairRef}
    (hA : ∀ i j l, StarPair a d c (A i j l)) (hO : ∀ i, StarPair a d c (O i))
    (is : List (Fin m)) :
    ∀ i, StarPair a d (determinantScan A c O is).1 ((determinantScan A c O is).2 i) := by
  induction is generalizing c O with
  | nil => exact hO
  | cons i is ih =>
      let r := compiler k (A i) c
      have he : Extends c r.1 := compiler_extends _ _ _
      have hr := compiler_star (hA i)
      have hw : ∀ j, StarPair a d r.1 (vectorWrite O i r.2 j) := by
        intro j
        unfold vectorWrite
        split
        · subst j; exact hr
        · exact extend (hO j) he
      exact ih (fun i j l => extend (hA i j l) he) hw

theorem determinantBatch_star {k m : ℕ}
    {A : Fin m → Matrix (Fin (k+1)) (Fin (k+1)) PairRef}
    (hA : ∀ i j l, StarPair a d c (A i j l)) :
    ∀ i, StarPair a d (determinantBatch A c).1 ((determinantBatch A c).2 i) := by
  have he := pairZero_extends c
  exact determinantScan_star (fun i j l => extend (hA i j l) he)
    (fun _ => zero a d c) (List.finRange m)

theorem cramerVariants_star {k : ℕ}
    {A : Matrix (Fin (k+1)) (Fin (k+1)) PairRef} {b : Fin (k+1) → PairRef}
    (hA : ∀ i j, StarPair a d c (A i j)) (hb : ∀ i, StarPair a d c (b i)) :
    ∀ r i j, StarPair a d c (cramerVariants A b r i j) := by
  intro r
  induction r using Fin.cases with
  | zero => exact hA
  | succ r =>
      intro i j
      by_cases hj : j=r
      · subst j; simpa [cramerVariants] using hb i
      · simpa [cramerVariants,Matrix.updateCol_apply,hj] using hA i j

theorem productSum_star {ι : Type*} {Z D : ι → PairRef}
    (hZ : ∀ i, StarPair a d c (Z i)) (hD : ∀ i, StarPair a d c (D i))
    (is : List ι) : StarPair a d (productSum Z D c is).1 (productSum Z D c is).2 := by
  induction is with
  | nil => exact zero a d c
  | cons i is ih =>
      have ex := productSum_extends Z D c is
      have ht := mul (extend (hZ i) ex) (extend (hD i) ex)
      exact add ht (extend ih (pairMul_extends _ _ _))

theorem residual_star {k : ℕ} {z δ : PairRef} {Z D : Fin k → PairRef}
    (hz : StarPair a d c z) (hδ : StarPair a d c δ)
    (hZ : ∀ i, StarPair a d c (Z i)) (hD : ∀ i, StarPair a d c (D i)) :
    StarPair a d (residual z δ Z D c).1 (residual z δ Z D c).2 := by
  let r := productSum Z D c (List.finRange k)
  have er : Extends c r.1 := productSum_extends _ _ _ _
  have en := er.trans (pairScale_extends r.1 (-1) r.2)
  have hn := scale (productSum_star hZ hD (List.finRange k)) (-1)
  have ht := mul (extend hz en) (extend hδ en)
  exact add ht (extend hn (pairMul_extends _ _ _))

#print axioms compiler_star
#print axioms determinantBatch_star
#print axioms residual_star

end ADComplete.PSDPairStar
