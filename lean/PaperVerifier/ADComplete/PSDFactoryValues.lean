import PaperVerifier.ADComplete.PSDFactoryDegrees

namespace ADComplete.PSDFactory
open CircuitAudit.CircuitCosts CircuitAudit.ProbeCircuit
open ADComplete.PSDBird ADComplete.PSDHomogeneousLift

theorem corner_adjoint {n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {c : Circuit} {p : PairRef} {x : ℝ} (h : Corner n a d c p x) :
    AdjointValue n a d c p (x • J n) := by
  refine ⟨h.1,?_⟩
  rw [h.2]
  simp only [Matrix.transpose_smul]
  rfl

def residualValue {N n : ℕ} (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (g : Matrix (Fin N) (Fin N) ℝ) (r : Fin (N-1)) : Matrix (Fin n) (Fin n) ℝ :=
  let e := prefixIndex r
  let A := g.submatrix e e
  let b := fun i => g (e i) (nextIndex r)
  z (nextIndex r) * (((n : ℝ)^r.val*Matrix.det A) • J n) -
    ∑ i, z (e i) * (((n : ℝ)^r.val*Matrix.det (A.updateCol i b)) • J n)

theorem residualStep_value {N n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {Z : Fin N → PairRef} {G : Matrix (Fin N) (Fin N) PairRef}
    {z : Fin N → Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin N) (Fin N) ℝ} {c : Circuit}
    (hZ : ∀ i, AdjointValue n a d c (Z i) (z i)) (hG : Corners n a d c G g)
    (r : Fin (N-1)) :
    AdjointValue n a d (residualStep Z G r c).1 (residualStep Z G r c).2 (residualValue z g r) := by
  let A := G.submatrix (prefixIndex r) (prefixIndex r)
  let b := fun i => G (prefixIndex r i) (nextIndex r)
  have hA := corners_submatrix hG (prefixIndex r) (prefixIndex r)
  have hc := cramerVariants_corners hA (fun i => hG (prefixIndex r i) (nextIndex r))
  have hd := determinantBatch_corner hc
  have he := determinantBatch_extends (cramerVariants A b) c
  have hv := residual_adjoint (adjoint_extend (hZ (nextIndex r)) he) (corner_adjoint (hd 0))
    (fun i => adjoint_extend (hZ (prefixIndex r i)) he) (fun i => corner_adjoint (hd i.succ))
  simpa only [residualStep,residualValue,cramerVariants,Fin.cases_zero,Fin.cases_succ,A,b] using hv

def residualVectorScan {N n : ℕ} (z : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (g : Matrix (Fin N) (Fin N) ℝ) :
    (Fin N → Matrix (Fin n) (Fin n) ℝ) → List (Fin (N-1)) →
      (Fin N → Matrix (Fin n) (Fin n) ℝ)
  | w,[] => w
  | w,r::rs => residualVectorScan z g (vectorWrite w (nextIndex r) (residualValue z g r)) rs

theorem residualScan_value {N n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {Z : Fin N → PairRef} {G : Matrix (Fin N) (Fin N) PairRef}
    {z : Fin N → Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin N) (Fin N) ℝ}
    {c : Circuit} {V : Fin N → PairRef} {w : Fin N → Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ i, AdjointValue n a d c (Z i) (z i)) (hG : Corners n a d c G g)
    (hV : ∀ i, AdjointValue n a d c (V i) (w i)) (rs : List (Fin (N-1))) :
    ∀ i, AdjointValue n a d (residualScan Z G c V rs).1 ((residualScan Z G c V rs).2 i)
      (residualVectorScan z g w rs i) := by
  induction rs generalizing c V w with
  | nil => exact hV
  | cons r rs ih =>
    have he := residualStep_extends Z G r c
    have hr := residualStep_value hZ hG r
    have hw : ∀ i, AdjointValue n a d (residualStep Z G r c).1
        (vectorWrite V (nextIndex r) (residualStep Z G r c).2 i)
        (vectorWrite w (nextIndex r) (residualValue z g r) i) := by
      intro i
      unfold vectorWrite
      split
      · exact hr
      · exact adjoint_extend (hV i) he
    exact ih (fun i => adjoint_extend (hZ i) he) (fun i j => corner_extend (hG i j) he) hw

theorem square_value {n : ℕ} {a d X : Matrix (Fin n) (Fin n) ℝ}
    {p : PairRef} {c : Circuit} (hp : AdjointValue n a d c p X) :
    AdjointValue n a d (square p c).1 (square p c).2 (X*X.transpose) :=
  adjoint_mul hp (adjoint_swap hp)

theorem chainSquare_value {N n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {V : Fin N → PairRef} {w : Fin N → Matrix (Fin n) (Fin n) ℝ} {c : Circuit}
    (hV : ∀ i, AdjointValue n a d c (V i) (w i)) (r : Fin (N-1)) :
    AdjointValue n a d (chainSquare V r c).1 (chainSquare V r c).2
      ((w (currentIndex r)+w (nextIndex r))*(w (currentIndex r)+w (nextIndex r)).transpose) :=
  square_value (adjoint_add (hV _) (hV _))

theorem chainSquareSum_value {N n : ℕ} {a d : Matrix (Fin n) (Fin n) ℝ}
    {V : Fin N → PairRef} {w : Fin N → Matrix (Fin n) (Fin n) ℝ} {c : Circuit}
    (hV : ∀ i, AdjointValue n a d c (V i) (w i)) (rs : List (Fin (N-1))) :
    AdjointValue n a d (chainSquareSum V c rs).1 (chainSquareSum V c rs).2
      ((rs.map (fun r => (w (currentIndex r)+w (nextIndex r))*
        (w (currentIndex r)+w (nextIndex r)).transpose)).sum) := by
  induction rs with
  | nil => simpa only [chainSquareSum,List.map_nil,List.sum_nil] using adjoint_zero n a d c
  | cons r rs ih =>
    have es := chainSquareSum_extends V c rs
    have hw := chainSquare_value (fun i => adjoint_extend (hV i) es) r
    have hs := adjoint_add hw (adjoint_extend ih (chainSquare_extends _ _ _))
    simpa only [chainSquareSum,List.map_cons,List.sum_cons] using hs

def sosValue {N n : ℕ} (hN : 0<N) (w : Fin N → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  w ⟨0,hN⟩*(w ⟨0,hN⟩).transpose+
    ∑ r : Fin (N-1), (w (currentIndex r)+w (nextIndex r))*(w (currentIndex r)+w (nextIndex r)).transpose

theorem sos_value {N n : ℕ} (hN : 0<N) {a d : Matrix (Fin n) (Fin n) ℝ}
    {V : Fin N → PairRef} {w : Fin N → Matrix (Fin n) (Fin n) ℝ} {c : Circuit}
    (hV : ∀ i, AdjointValue n a d c (V i) (w i)) :
    AdjointValue n a d (sos hN V c).1 (sos hN V c).2 (sosValue hN w) := by
  have hs := chainSquareSum_value hV (List.finRange (N-1))
  have es := chainSquareSum_extends V c (List.finRange (N-1))
  have hv := square_value (adjoint_extend (hV ⟨0,hN⟩) es)
  have hf := adjoint_add hv (adjoint_extend hs (square_extends _ _))
  rw [← List.sum_toFinset _ (List.nodup_finRange (N-1)),List.toFinset_finRange] at hf
  exact hf

#print axioms residualStep_value
#print axioms residualScan_value
#print axioms sos_value
end ADComplete.PSDFactory
