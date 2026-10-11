import Mathlib
import PaperVerifier.PrincipalMomentAudit.Transport

/-!
Algebraic reverse-extraction step of arXiv:2607.21494v1, Lemma 4.3,
lines 781--792 of the locked source main__3_.tex.

The finite selected set may contain children of different parents. Its
parent-fibres have size at most one because the selected vertices represent
one completed lower rooted type. The two zero-entry hypotheses express the
undirected support and unique active parent of a peeled quotient vertex.

These hypotheses are structural obligations, not a formalization of the
theorem that actual automorphism quotients of all trees satisfy them. In
particular, neither diagonality of Z nor existence of a recovered coordinate
projection is assumed.
-/

namespace PrincipalMomentAudit.Quotient

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def selectedDiagonal (S : Finset ι) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => if i ∈ S then 1 else 0)

def coordinate (c : ι) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => if i = c then 1 else 0)

def reverseProduct (B : Matrix ι ι ℝ) (S : Finset ι) (p : ι) : Matrix ι ι ℝ :=
  selectedDiagonal S * B * coordinate p * B * selectedDiagonal S

theorem reverseProduct_apply (B : Matrix ι ι ℝ) (S : Finset ι) (p i j : ι) :
    reverseProduct B S p i j =
      (if i ∈ S then 1 else 0) * B i p * B p j *
        (if j ∈ S then 1 else 0) := by
  simp [reverseProduct, selectedDiagonal, coordinate, Matrix.mul_apply,
    Matrix.diagonal_apply]

/-- A nonzero entry forces both selected vertices to have the specified parent.
No diagonal or support conclusion is included in the assumptions. -/
theorem reverseProduct_support (B : Matrix ι ι ℝ) (S : Finset ι)
    (parent : ι → ι) (p i j : ι)
    (hrow : ∀ a ∈ S, ∀ b, b ≠ parent a → B a b = 0)
    (hcol : ∀ a ∈ S, ∀ b, b ≠ parent a → B b a = 0)
    (h : reverseProduct B S p i j ≠ 0) :
    i ∈ S ∧ j ∈ S ∧ parent i = p ∧ parent j = p := by
  rw [reverseProduct_apply] at h
  have hi : i ∈ S := by
    by_contra hn
    simp [hn] at h
  have hj : j ∈ S := by
    by_contra hn
    simp [hn] at h
  have hip : parent i = p := by
    by_contra hn
    have hz := hrow i hi p (Ne.symm hn)
    simp [hz] at h
  have hjp : parent j = p := by
    by_contra hn
    have hz := hcol j hj p (Ne.symm hn)
    simp [hz] at h
  exact ⟨hi, hj, hip, hjp⟩

/-- Uniqueness of a same-type child under each parent proves diagonality. -/
theorem reverseProduct_offDiagonal (B : Matrix ι ι ℝ) (S : Finset ι)
    (parent : ι → ι) (p i j : ι)
    (hrow : ∀ a ∈ S, ∀ b, b ≠ parent a → B a b = 0)
    (hcol : ∀ a ∈ S, ∀ b, b ≠ parent a → B b a = 0)
    (hunique : ∀ a ∈ S, ∀ b ∈ S, parent a = parent b → a = b)
    (hij : i ≠ j) : reverseProduct B S p i j = 0 := by
  by_contra h
  obtain ⟨hi, hj, hip, hjp⟩ := reverseProduct_support B S parent p i j hrow hcol h
  exact hij (hunique i hi j hj (hip.trans hjp.symm))

/-- Empty specified parent-fibre gives the zero matrix. -/
theorem reverseProduct_empty (B : Matrix ι ι ℝ) (S : Finset ι)
    (parent : ι → ι) (p : ι)
    (hrow : ∀ a ∈ S, ∀ b, b ≠ parent a → B a b = 0)
    (hcol : ∀ a ∈ S, ∀ b, b ≠ parent a → B b a = 0)
    (hempty : ∀ a ∈ S, parent a ≠ p) : reverseProduct B S p = 0 := by
  ext i j
  by_contra h
  have hn : reverseProduct B S p i j ≠ 0 := by simpa using h
  obtain ⟨hi, _, hip, _⟩ := reverseProduct_support B S parent p i j hrow hcol hn
  exact hempty i hi hip

/-- If the parent-fibre contains c, the reverse product is exactly a scalar
multiple of its coordinate projection. It is derived, never assumed. -/
theorem reverseProduct_eq_coordinate (B : Matrix ι ι ℝ) (S : Finset ι)
    (parent : ι → ι) (p c : ι)
    (hrow : ∀ a ∈ S, ∀ b, b ≠ parent a → B a b = 0)
    (hcol : ∀ a ∈ S, ∀ b, b ≠ parent a → B b a = 0)
    (hunique : ∀ a ∈ S, ∀ b ∈ S, parent a = parent b → a = b)
    (hc : c ∈ S) (hcp : parent c = p) :
    reverseProduct B S p = (B c p * B p c) • coordinate c := by
  ext i j
  by_cases hic : i = c
  · subst i
    by_cases hjc : j = c
    · subst j
      simp [reverseProduct_apply, hc, coordinate]
    · have hij : c ≠ j := Ne.symm hjc
      rw [reverseProduct_offDiagonal B S parent p c j hrow hcol hunique hij]
      simp [coordinate, hij]
  · have hz : reverseProduct B S p i j = 0 := by
      by_contra h
      obtain ⟨hi, _, hip, _⟩ := reverseProduct_support B S parent p i j hrow hcol h
      exact hic (hunique i hi c hc (hip.trans hcp.symm))
    rw [hz]
    by_cases hij : i = j
    · subst j
      simp [coordinate, hic]
    · simp [coordinate, hij]

omit [Fintype ι] [DecidableEq ι] in
/-- A real nonnegative adjacency-count quotient has strictly positive weight
at the recovered child whenever both directions of the edge are present. -/
theorem reverseProduct_weight_pos (B : Matrix ι ι ℝ) (p c : ι)
    (hforward : 0 < B c p) (hbackward : 0 < B p c) :
    0 < B c p * B p c := mul_pos hforward hbackward

omit [Fintype ι] [DecidableEq ι] in
/-- The column version of unique-parent support follows from the undirected
support of an actual orbit-count quotient. No Euclidean symmetry is assumed:
the quotient matrix itself is usually nonsymmetric. -/
theorem column_parent_support_of_undirected (B : Matrix ι ι ℝ) (S : Finset ι)
    (parent : ι → ι)
    (hrow : ∀ a ∈ S, ∀ b, b ≠ parent a → B a b = 0)
    (hundirected : ∀ a b, B a b = 0 → B b a = 0) :
    ∀ a ∈ S, ∀ b, b ≠ parent a → B b a = 0 := by
  intro a ha b hb
  exact hundirected a b (hrow a ha b hb)

/-- Literal matrix Lagrange polynomial from the paper. The list product uses
only multiplication, addition, and real scalar constants; it reads no entry.
All factors commute because they are polynomials in the same matrix. -/
noncomputable def matrixSelector (N k : ℕ) (Z : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (((Finset.range (N + 1)).erase k).toList.map (fun (r : ℕ) =>
    (((k : ℝ) - (r : ℝ))⁻¹) • (Z - (r : ℝ) • (1 : Matrix ι ι ℝ)))).prod

private theorem listProd_diagonal (L : List (ι → ℝ)) :
    (L.map Matrix.diagonal).prod = Matrix.diagonal L.prod := by
  exact (map_list_prod (Matrix.diagonalRingHom ι ℝ) L).symm

/-- Evaluation of the literal polynomial on a diagonal matrix. This proves
the coordinate formula from the actual matrix operations; it does not define
the selector by a coordinate operation. -/
theorem matrixSelector_diagonal (N k : ℕ) (z : ι → ℝ) :
    matrixSelector N k (Matrix.diagonal z) =
      Matrix.diagonal (fun i => PrincipalMomentAudit.Transport.scalarSelector N k (z i)) := by
  have hfactor (r : ℕ) :
      (((k : ℝ) - (r : ℝ))⁻¹) •
        (Matrix.diagonal z - (r : ℝ) • (1 : Matrix ι ι ℝ)) =
      Matrix.diagonal (fun i => (z i - (r : ℝ)) / ((k : ℝ) - (r : ℝ))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [div_eq_mul_inv, mul_comm]
    · simp [hij]
  unfold matrixSelector
  let levels := ((Finset.range (N + 1)).erase k).toList
  let f : ℕ → ι → ℝ := fun r i => (z i - (r : ℝ)) / ((k : ℝ) - (r : ℝ))
  have hmap :
      (levels.map (fun (r : ℕ) => (((k : ℝ) - (r : ℝ))⁻¹) •
        (Matrix.diagonal z - (r : ℝ) • (1 : Matrix ι ι ℝ)))) =
      (levels.map f).map Matrix.diagonal := by
    rw [List.map_map]
    exact List.map_congr_left (fun r _ => hfactor r)
  change (levels.map (fun (r : ℕ) => (((k : ℝ) - (r : ℝ))⁻¹) •
    (Matrix.diagonal z - (r : ℝ) • (1 : Matrix ι ι ℝ)))).prod = _
  rw [hmap, listProd_diagonal]
  congr 1
  funext i
  simp [levels, f, Pi.list_prod_apply, List.map_map, PrincipalMomentAudit.Transport.scalarSelector]

/-- The fixed sum of levels 1,...,N; it is exactly the paper's positive
integer spectral support extractor. -/
noncomputable def positiveSelector (N : ℕ) (Z : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑ k ∈ (Finset.range (N + 1)).erase 0, matrixSelector N k Z

theorem positiveSelector_scalar (N j : ℕ) (hj : j ≤ N) :
    (∑ k ∈ (Finset.range (N + 1)).erase 0,
      PrincipalMomentAudit.Transport.scalarSelector N k (j : ℝ)) =
        if j = 0 then 0 else 1 := by
  simp_rw [PrincipalMomentAudit.Transport.scalarSelector_integer N _ j hj]
  simp [Finset.mem_erase, Finset.mem_range, Nat.lt_succ_of_le hj]

/-- A single diagonal integer eigenvalue in 1,...,N is extracted by the
literal fixed polynomial, including all the zero eigenvalues. -/
theorem positiveSelector_coordinate (N j : ℕ) (c : ι)
    (hj : j ≤ N) (hjpos : 0 < j) :
    positiveSelector N ((j : ℝ) • coordinate c) = coordinate c := by
  have hdiag : (j : ℝ) • coordinate c =
      Matrix.diagonal (fun i => if i = c then (j : ℝ) else 0) := by
    ext i l
    by_cases hil : i = l
    · subst l
      simp [coordinate]
    · simp [coordinate, hil]
  rw [hdiag]
  ext i l
  by_cases hil : i = l
  · subst l
    simp only [positiveSelector, Matrix.sum_apply, matrixSelector_diagonal,
      Matrix.diagonal_apply, ite_true]
    by_cases hic : i = c
    · simpa only [hic, ite_true, coordinate, Matrix.diagonal_apply,
        Nat.ne_of_gt hjpos, if_false] using positiveSelector_scalar N j hj
    · simpa only [hic, if_false, coordinate, Matrix.diagonal_apply,
        ite_true, Nat.cast_zero] using positiveSelector_scalar N 0 (Nat.zero_le N)
  · simp [positiveSelector, Matrix.sum_apply, matrixSelector_diagonal,
      coordinate, hil]

/-- The promised end-to-end reverse step. The integer eigenvalue is obtained
from the two actual adjacency counts, never supplied as an assumption about Z.
For tree quotients the child-to-parent count is one, so j is the parent's
integer multiplicity of children of this selected lower type. -/
theorem extract_unique_child (B : Matrix ι ι ℝ) (S : Finset ι)
    (parent : ι → ι) (p c : ι) (N j : ℕ)
    (hrow : ∀ a ∈ S, ∀ b, b ≠ parent a → B a b = 0)
    (hcol : ∀ a ∈ S, ∀ b, b ≠ parent a → B b a = 0)
    (hunique : ∀ a ∈ S, ∀ b ∈ S, parent a = parent b → a = b)
    (hc : c ∈ S) (hcp : parent c = p)
    (hcount : B c p * B p c = (j : ℝ)) (hj : j ≤ N) (hjpos : 0 < j) :
    positiveSelector N (reverseProduct B S p) = coordinate c := by
  rw [reverseProduct_eq_coordinate B S parent p c hrow hcol hunique hc hcp, hcount]
  exact positiveSelector_coordinate N j c hj hjpos

/-- Every literal selector remains in the same real matrix algebra. -/
theorem matrixSelector_mem (Q : Subalgebra ℝ (Matrix ι ι ℝ))
    (N k : ℕ) (Z : Matrix ι ι ℝ) (hZ : Z ∈ Q) : matrixSelector N k Z ∈ Q := by
  unfold matrixSelector
  apply Q.list_prod_mem
  intro M hM
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hM
  exact Q.smul_mem (Q.sub_mem hZ (Q.smul_mem Q.one_mem (r : ℝ))) _

theorem positiveSelector_mem (Q : Subalgebra ℝ (Matrix ι ι ℝ))
    (N : ℕ) (Z : Matrix ι ι ℝ) (hZ : Z ∈ Q) : positiveSelector N Z ∈ Q := by
  unfold positiveSelector
  apply Q.sum_mem
  intro k _
  exact matrixSelector_mem Q N k Z hZ

/-- The recovered coordinate idempotent belongs to Q if the selected leaf
selector, current adjacency, and known parent idempotent already belong to Q.
Thus this is the actual induction step of Lemma 4.3, not merely a computation
performed using additional coordinate operations. -/
theorem extracted_child_mem (Q : Subalgebra ℝ (Matrix ι ι ℝ))
    (B : Matrix ι ι ℝ) (S : Finset ι) (parent : ι → ι) (p c : ι) (N j : ℕ)
    (hB : B ∈ Q) (hX : selectedDiagonal S ∈ Q) (hEp : coordinate p ∈ Q)
    (hrow : ∀ a ∈ S, ∀ b, b ≠ parent a → B a b = 0)
    (hcol : ∀ a ∈ S, ∀ b, b ≠ parent a → B b a = 0)
    (hunique : ∀ a ∈ S, ∀ b ∈ S, parent a = parent b → a = b)
    (hc : c ∈ S) (hcp : parent c = p)
    (hcount : B c p * B p c = (j : ℝ)) (hj : j ≤ N) (hjpos : 0 < j) :
    coordinate c ∈ Q := by
  have hZ : reverseProduct B S p ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.mul_mem hX hB) hEp) hB) hX
  rw [← extract_unique_child B S parent p c N j hrow hcol hunique hc hcp hcount hj hjpos]
  exact positiveSelector_mem Q N _ hZ

/-- A genuine nonnegative-integer row of degree one has exactly one nonzero
entry, and that entry is one. This supplies the child-to-parent count from
the current leaf degree, rather than assuming the reverse product's value. -/
theorem degree_one_parent_count (b : Matrix ι ι ℕ) (c p : ι)
    (hdegree : ∑ q, b c q = 1) (hp : 0 < b c p) :
    b c p = 1 ∧ ∀ q, q ≠ p → b c q = 0 := by
  have hle : b c p ≤ ∑ q, b c q :=
    Finset.single_le_sum (fun q _ => Nat.zero_le (b c q)) (Finset.mem_univ p)
  have hparent : b c p = 1 := by omega
  refine ⟨hparent, ?_⟩
  have hsplit := Finset.sum_erase_add Finset.univ (fun q => b c q) (Finset.mem_univ p)
  have hzero : ∑ q ∈ Finset.univ.erase p, b c q = 0 := by
    rw [hparent, hdegree] at hsplit
    omega
  intro q hq
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => Nat.zero_le (b c q))).mp
    hzero q (by simp [hq])

omit [Fintype ι] [DecidableEq ι] in
/-- Edge balance in a positive orbit-size weighted inner product supplies
undirected zero support. It does not replace the actual count quotient by
a symmetric Euclidean matrix. -/
theorem undirected_support_of_balance (B : Matrix ι ι ℝ) (sizes : ι → ℝ)
    (hsizes : ∀ i, 0 < sizes i)
    (hbalance : ∀ i j, sizes i * B i j = sizes j * B j i) :
    ∀ i j, B i j = 0 → B j i = 0 := by
  intro i j hij
  have h := hbalance i j
  rw [hij, mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt (hsizes j))

/-- The reverse step expressed entirely in actual natural adjacency counts.
Its structural assumptions are a degree-one selected row, a chosen adjacent
parent, edge balance with positive orbit sizes, and uniqueness of a same-type
selected child under a parent. Integer support and both zero-entry conditions
are derived here. The remaining tree obligation is to prove that actual
peeled automorphism orbits satisfy the parent-fibre uniqueness condition. -/
theorem extract_unique_child_of_counts (b : Matrix ι ι ℕ) (S : Finset ι)
    (parent : ι → ι) (sizes : ι → ℝ) (p c : ι) (N : ℕ)
    (hdegree : ∀ a ∈ S, ∑ q, b a q = 1)
    (hparent : ∀ a ∈ S, 0 < b a (parent a))
    (hsizes : ∀ a, 0 < sizes a)
    (hbalance : ∀ a q, sizes a * (b a q : ℝ) = sizes q * (b q a : ℝ))
    (hunique : ∀ a ∈ S, ∀ d ∈ S, parent a = parent d → a = d)
    (hc : c ∈ S) (hcp : parent c = p) (hbound : b p c ≤ N) :
    positiveSelector N (reverseProduct (fun a q => (b a q : ℝ)) S p) = coordinate c := by
  let B : Matrix ι ι ℝ := fun a q => (b a q : ℝ)
  have hrow : ∀ a ∈ S, ∀ q, q ≠ parent a → B a q = 0 := by
    intro a ha q hq
    have hz := (degree_one_parent_count b a (parent a) (hdegree a ha)
      (hparent a ha)).2 q hq
    simp [B, hz]
  have hundirected : ∀ a q, B a q = 0 → B q a = 0 :=
    undirected_support_of_balance B sizes hsizes hbalance
  have hcol := column_parent_support_of_undirected B S parent hrow hundirected
  have hcparent : b c p = 1 := by
    rw [← hcp]
    exact (degree_one_parent_count b c (parent c) (hdegree c hc) (hparent c hc)).1
  have hcpnonzero : B c p ≠ 0 := by simp [B, hcparent]
  have hpcpositive : 0 < b p c := by
    by_contra hn
    have hz : b p c = 0 := by omega
    exact hcpnonzero (hundirected p c (by simp [B, hz]))
  apply extract_unique_child B S parent p c N (b p c) hrow hcol hunique hc hcp
  · simp [B, hcparent]
  · exact hbound
  · exact hpcpositive

#print axioms reverseProduct_apply
#print axioms reverseProduct_support
#print axioms reverseProduct_offDiagonal
#print axioms reverseProduct_empty
#print axioms reverseProduct_eq_coordinate
#print axioms matrixSelector_diagonal
#print axioms positiveSelector_coordinate
#print axioms extract_unique_child
#print axioms extracted_child_mem
#print axioms degree_one_parent_count
#print axioms undirected_support_of_balance
#print axioms extract_unique_child_of_counts

end PrincipalMomentAudit.Quotient
