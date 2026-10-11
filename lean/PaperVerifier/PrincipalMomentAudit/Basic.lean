import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw

/-!
# arXiv:2607.21494v1 audit: adjacency-degree matrices and the leaf diagonal identity

This file formalizes the leaf diagonal lemma in Section 3.1 of
`principal_ad_moments_revised.tex`.  The matrix identity is proved for every
finite simple graph: acyclicity is not needed when the selected vertices have
degree one.  The selector is the ordinary diagonal matrix of a finite-set
indicator; no Hadamard multiplication is used.
-/

namespace PrincipalMomentAudit

open Matrix Finset

section GraphMatrices

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The diagonal selector of a finite set of vertices. -/
def vertexSelector (W : Finset V) : Matrix V V ℝ :=
  Matrix.diagonal (fun v => if v ∈ W then 1 else 0)

/-- Entries of `A X_W A` count selected common neighbors. -/
theorem adjacency_selector_adjacency_apply (W : Finset V) (u v : V) :
    (G.adjMatrix ℝ * vertexSelector W * G.adjMatrix ℝ) u v =
      ∑ w ∈ W, if G.Adj u w ∧ G.Adj w v then (1 : ℝ) else 0 := by
  rw [Matrix.mul_apply]
  simp only [vertexSelector, Matrix.mul_diagonal, SimpleGraph.adjMatrix_apply]
  have hterm (w : V) :
      ((if G.Adj u w then (1 : ℝ) else 0) * (if w ∈ W then 1 else 0)) *
          (if G.Adj w v then 1 else 0) =
        if w ∈ W then (if G.Adj u w ∧ G.Adj w v then (1 : ℝ) else 0) else 0 := by
    split_ifs <;> simp_all
  simp_rw [hterm]
  simp

omit [DecidableEq V] in
/-- Degree-one vertices cannot be common neighbors of distinct vertices. -/
theorem leaf_not_common_neighbor {w u v : V} (hw : G.degree w = 1)
    (huv : u ≠ v) : ¬ (G.Adj u w ∧ G.Adj w v) := by
  rintro ⟨huw, hwv⟩
  obtain ⟨a, ha, hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw
  exact huv ((hunique u huw.symm).trans (hunique v hwv).symm)

/-- Every off-diagonal entry vanishes when all selected vertices are leaves. -/
theorem leaf_selector_offDiagonal (W : Finset V)
    (hW : ∀ w ∈ W, G.degree w = 1) {u v : V} (huv : u ≠ v) :
    (G.adjMatrix ℝ * vertexSelector W * G.adjMatrix ℝ) u v = 0 := by
  rw [adjacency_selector_adjacency_apply]
  apply Finset.sum_eq_zero
  intro w hw
  simp [leaf_not_common_neighbor G (hW w hw) huv]

/-- The diagonal entry equals the number of selected neighbors. -/
theorem selector_diagonal_count (W : Finset V) (v : V) :
    (G.adjMatrix ℝ * vertexSelector W * G.adjMatrix ℝ) v v =
      ((W.filter (G.Adj v)).card : ℝ) := by
  rw [adjacency_selector_adjacency_apply]
  have hterm (w : V) :
      (if G.Adj v w ∧ G.Adj w v then (1 : ℝ) else 0) =
        if G.Adj v w then 1 else 0 := by
    by_cases h : G.Adj v w
    · simp [h, h.symm]
    · simp [h]
  simp_rw [hterm]
  simp

/-- Section 3.1, Leaf diagonal lemma, as an equality of whole matrices. -/
theorem leaf_diagonal_identity (W : Finset V)
    (hW : ∀ w ∈ W, G.degree w = 1) :
    G.adjMatrix ℝ * vertexSelector W * G.adjMatrix ℝ =
      Matrix.diagonal (fun v => ((W.filter (G.Adj v)).card : ℝ)) := by
  ext u v
  by_cases huv : u = v
  · subst v
    simpa using selector_diagonal_count G W u
  · simp [huv, leaf_selector_offDiagonal G W hW huv]

/-- The diagonal of `A²` is the degree vector. -/
theorem adjacency_square_diagonal (v : V) :
    (G.adjMatrix ℝ ^ 2) v v = (G.degree v : ℝ) := by
  rw [pow_two, Matrix.mul_apply, G.degree_eq_sum_if_adj (R := ℝ)]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : G.Adj v w
  · simp [SimpleGraph.adjMatrix_apply, h, h.symm]
  · simp [SimpleGraph.adjMatrix_apply, h]

/-- The unital real adjacency-degree algebra of Section 2. -/
def adjacencyDegreeAlgebra : Subalgebra ℝ (Matrix V V ℝ) :=
  Algebra.adjoin ℝ {G.adjMatrix ℝ, G.degMatrix ℝ}

/-- Both symmetric generators force the generated algebra to be transpose-closed. -/
theorem adjacencyDegreeAlgebra_transpose_mem {X : Matrix V V ℝ}
    (hX : X ∈ adjacencyDegreeAlgebra G) :
    X.transpose ∈ adjacencyDegreeAlgebra G := by
  induction hX using Algebra.adjoin_induction with
  | mem X hX =>
      rcases Set.mem_insert_iff.mp hX with hX | hX
      · subst X
        rw [G.transpose_adjMatrix]
        exact Algebra.subset_adjoin (Set.mem_insert _ _)
      · have hX : X = G.degMatrix ℝ := Set.mem_singleton_iff.mp hX
        subst X
        rw [G.isSymm_degMatrix ℝ]
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_one]
      exact (adjacencyDegreeAlgebra G).smul_mem (adjacencyDegreeAlgebra G).one_mem r
  | add X Y hX hY ihX ihY =>
      simpa using (adjacencyDegreeAlgebra G).add_mem ihX ihY
  | mul X Y hX hY ihX ihY =>
      simpa [Matrix.transpose_mul] using (adjacencyDegreeAlgebra G).mul_mem ihY ihX

end GraphMatrices

namespace MatrixPrincipal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Cyclic module `S c`, defined as an actual submodule, rather than a span
with an unproved representation assumption. -/
def cyclicModule (S : Subalgebra ℝ (Matrix V V ℝ)) (c : V → ℝ) :
    Submodule ℝ (V → ℝ) where
  carrier := {u | ∃ p ∈ S, p *ᵥ c = u}
  zero_mem' := ⟨0, S.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨p + q, S.add_mem hp hq, Matrix.add_mulVec p q c⟩
  smul_mem' := by
    rintro r u ⟨p, hp, rfl⟩
    exact ⟨r • p, S.smul_mem hp r, Matrix.smul_mulVec r p c⟩

@[simp]
theorem mem_cyclicModule (S : Subalgebra ℝ (Matrix V V ℝ)) (c u : V → ℝ) :
    u ∈ cyclicModule S c ↔ ∃ p ∈ S, p *ᵥ c = u := Iff.rfl

/-- The cyclic vector itself belongs to its principal module. -/
theorem cyclicVector_mem (S : Subalgebra ℝ (Matrix V V ℝ)) (c : V → ℝ) :
    c ∈ cyclicModule S c := ⟨1, S.one_mem, by simp⟩

/-- The principal cyclic module is invariant under the algebra. -/
theorem cyclicModule_invariant (S : Subalgebra ℝ (Matrix V V ℝ)) (c : V → ℝ)
    {p : Matrix V V ℝ} (hp : p ∈ S) {u : V → ℝ} (hu : u ∈ cyclicModule S c) :
    p *ᵥ u ∈ cyclicModule S c := by
  rcases hu with ⟨q, hq, rfl⟩
  exact ⟨p * q, S.mul_mem hp hq, (Matrix.mulVec_mulVec c p q).symm⟩

/-- The algebraic two-sided principal ideal, interpreted as its linear span. -/
def principalIdealSpan (S : Subalgebra ℝ (Matrix V V ℝ)) (c : V → ℝ) :
    Submodule ℝ (Matrix V V ℝ) :=
  Submodule.span ℝ {X | ∃ p ∈ S, ∃ q ∈ S, X = p * Matrix.vecMulVec c c * q}

/-- The span of rank-one matrices with both factors in the cyclic module. -/
def cyclicRankOneSpan (S : Subalgebra ℝ (Matrix V V ℝ)) (c : V → ℝ) :
    Submodule ℝ (Matrix V V ℝ) :=
  Submodule.span ℝ {X | ∃ u ∈ cyclicModule S c, ∃ v ∈ cyclicModule S c,
    X = Matrix.vecMulVec u v}

omit [DecidableEq V] in
/-- `p (c cᵀ) q = (p c) (qᵀ c)ᵀ`, the key factorization in Section 2. -/
theorem principal_sandwich_rankOne (p q : Matrix V V ℝ) (c : V → ℝ) :
    p * Matrix.vecMulVec c c * q =
      Matrix.vecMulVec (p *ᵥ c) (q.transpose *ᵥ c) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]

/-- First assertion of the principal rank-one ideal theorem, for any
transpose-closed real matrix algebra and any cyclic vector. -/
theorem principalIdealSpan_eq_cyclicRankOneSpan
    (S : Subalgebra ℝ (Matrix V V ℝ)) (c : V → ℝ)
    (htranspose : ∀ p ∈ S, p.transpose ∈ S) :
    principalIdealSpan S c = cyclicRankOneSpan S c := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ⟨p, hp, q, hq, rfl⟩
    apply Submodule.subset_span
    exact ⟨p *ᵥ c, ⟨p, hp, rfl⟩, q.transpose *ᵥ c,
      ⟨q.transpose, htranspose q hq, rfl⟩, principal_sandwich_rankOne p q c⟩
  · apply Submodule.span_le.mpr
    rintro X ⟨u, hu, v, hv, rfl⟩
    rcases hu with ⟨p, hp, rfl⟩
    rcases hv with ⟨q, hq, rfl⟩
    apply Submodule.subset_span
    refine ⟨p, hp, q.transpose, htranspose q hq, ?_⟩
    simpa using (principal_sandwich_rankOne p q.transpose c).symm

/-- If the seed rank-one matrix belongs to the algebra, the entire principal
ideal is an internal submodule of that algebra. -/
theorem principalIdealSpan_le_algebra (S : Subalgebra ℝ (Matrix V V ℝ))
    (c : V → ℝ) (hJ : Matrix.vecMulVec c c ∈ S) :
    principalIdealSpan S c ≤ S.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro X ⟨p, hp, q, hq, rfl⟩
  exact S.mul_mem (S.mul_mem hp hJ) hq

/-- Every rank-one principal operator annihilates vectors orthogonal to the
principal module (orthogonality is expressed by the ordinary real dot product). -/
theorem principal_rankOne_annihilates_orthogonal
    (S : Subalgebra ℝ (Matrix V V ℝ)) (c u v z : V → ℝ)
    (hv : v ∈ cyclicModule S c)
    (hz : ∀ x ∈ cyclicModule S c, dotProduct x z = 0) :
    Matrix.vecMulVec u v *ᵥ z = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  rw [show (∑ j, u i * v j * z j) = u i * ∑ j, v j * z j by
    simp only [Finset.mul_sum, mul_assoc]]
  change u i * dotProduct v z = 0
  rw [hz v hv, mul_zero]

omit [DecidableEq V] in
/-- Rank-one matrices act by the ordinary dot-product functional. -/
theorem rankOne_mulVec (u v w : V → ℝ) :
    Matrix.vecMulVec u v *ᵥ w = dotProduct v w • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Restricted real dot product, as a map from a subspace to its dual. -/
def submoduleDotDual (M : Submodule ℝ (V → ℝ)) : M →ₗ[ℝ] Module.Dual ℝ M where
  toFun v :=
    { toFun := fun u => dotProduct (v : V → ℝ) (u : V → ℝ)
      map_add' := by intro u w; exact dotProduct_add _ _ _
      map_smul' := by intro r u; exact dotProduct_smul _ _ _ }
  map_add' := by
    intro u v
    ext w
    exact add_dotProduct _ _ _
  map_smul' := by
    intro r v
    ext w
    exact smul_dotProduct _ _ _

omit [DecidableEq V] in
@[simp]
theorem submoduleDotDual_apply (M : Submodule ℝ (V → ℝ)) (v u : M) :
    submoduleDotDual M v u = dotProduct (v : V → ℝ) (u : V → ℝ) := rfl

omit [DecidableEq V] in
/-- Positivity of the real dot product makes its restriction nondegenerate. -/
theorem submoduleDotDual_injective (M : Submodule ℝ (V → ℝ)) :
    Function.Injective (submoduleDotDual M) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hzero : submoduleDotDual M v = 0 := hv
  have hself : dotProduct (v : V → ℝ) (v : V → ℝ) = 0 :=
    congrArg (fun f : Module.Dual ℝ M => f v) hzero
  apply Subtype.ext
  exact dotProduct_self_eq_zero.mp hself

omit [DecidableEq V] in
/-- Every functional on a finite real subspace is represented by a vector
of that same subspace using the dot product. -/
theorem submoduleDotDual_surjective (M : Submodule ℝ (V → ℝ)) :
    Function.Surjective (submoduleDotDual M) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Subspace.dual_finrank_eq])).mp (submoduleDotDual_injective M)

/-- The full-action assertion in Section 2: every endomorphism of the cyclic
module is realized by a matrix in the principal ideal.  This proof constructs
the matrix by expanding in a finite basis and representing each coordinate
functional by the restricted dot product.

The hypothesis that the seed `c cᵀ` is in the algebra is explicit.  For the
graph application with `c = 1`, the connected-Laplacian polynomial argument
that supplies this hypothesis is a separate statement.
-/
theorem principalIdeal_full_action
    (S : Subalgebra ℝ (Matrix V V ℝ)) (c : V → ℝ)
    (htranspose : ∀ p ∈ S, p.transpose ∈ S)
    (hJ : Matrix.vecMulVec c c ∈ S)
    (T : Module.End ℝ (cyclicModule S c)) :
    ∃ X ∈ principalIdealSpan S c, X ∈ S ∧
      ∀ w : cyclicModule S c, X *ᵥ (w : V → ℝ) = (T w : V → ℝ) := by
  classical
  let M := cyclicModule S c
  let b := Module.finBasis ℝ M
  have hsurj := submoduleDotDual_surjective M
  let v := fun i => Classical.choose (hsurj (b.coord i))
  have hv (i) (w : M) : dotProduct (v i : V → ℝ) (w : V → ℝ) = b.repr w i := by
    have hv' := Classical.choose_spec (hsurj (b.coord i))
    have heval := congrArg (fun f : Module.Dual ℝ M => f w) hv'
    simpa [v, submoduleDotDual_apply, Module.Basis.coord_apply] using heval
  let X : Matrix V V ℝ :=
    ∑ i, Matrix.vecMulVec (T (b i) : V → ℝ) (v i : V → ℝ)
  have hXrank : X ∈ cyclicRankOneSpan S c := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.subset_span
    exact ⟨(T (b i) : V → ℝ), (T (b i)).property,
      (v i : V → ℝ), (v i).property, rfl⟩
  have hXideal : X ∈ principalIdealSpan S c := by
    rw [principalIdealSpan_eq_cyclicRankOneSpan S c htranspose]
    exact hXrank
  refine ⟨X, hXideal, principalIdealSpan_le_algebra S c hJ hXideal, ?_⟩
  intro w
  change (∑ i, Matrix.vecMulVec (T (b i) : V → ℝ) (v i : V → ℝ)) *ᵥ
    (w : V → ℝ) = (T w : V → ℝ)
  rw [Matrix.sum_mulVec]
  simp_rw [rankOne_mulVec, hv]
  have hT := congrArg (fun z : M => (T z : V → ℝ)) (b.sum_repr w)
  simpa only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] using hT

/-- The entire principal ideal, including sums of rank-one operators,
annihilates the dot-product orthogonal complement of its cyclic module. -/
theorem principalIdeal_annihilates_orthogonal
    (S : Subalgebra ℝ (Matrix V V ℝ)) (c z : V → ℝ)
    (htranspose : ∀ p ∈ S, p.transpose ∈ S)
    (hz : ∀ x ∈ cyclicModule S c, dotProduct x z = 0)
    {X : Matrix V V ℝ} (hX : X ∈ principalIdealSpan S c) : X *ᵥ z = 0 := by
  rw [principalIdealSpan_eq_cyclicRankOneSpan S c htranspose] at hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
      rcases hX with ⟨u, hu, v, hv, rfl⟩
      exact principal_rankOne_annihilates_orthogonal S c u v z hv hz
  | zero => simp
  | add X Y hX hY ihX ihY => simp [Matrix.add_mulVec, ihX, ihY]
  | smul r X hX ihX => simp [Matrix.smul_mulVec, ihX]

end MatrixPrincipal

section PrincipalAD

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The graph principal module `M_G = A(G) 1` of Section 2. -/
def principalADModule : Submodule ℝ (V → ℝ) :=
  MatrixPrincipal.cyclicModule (adjacencyDegreeAlgebra G) (fun _ => 1)

/-- The graph specialization of the principal rank-one span identity. -/
theorem principalAD_rankOneIdeal_eq :
    MatrixPrincipal.principalIdealSpan (adjacencyDegreeAlgebra G) (fun _ => 1) =
      MatrixPrincipal.cyclicRankOneSpan (adjacencyDegreeAlgebra G) (fun _ => 1) := by
  exact MatrixPrincipal.principalIdealSpan_eq_cyclicRankOneSpan _ _
    (fun _ h => adjacencyDegreeAlgebra_transpose_mem G h)

end PrincipalAD

end PrincipalMomentAudit

-- Kernel dependency audit of the principal mathematical statements.
#print axioms PrincipalMomentAudit.leaf_diagonal_identity
#print axioms PrincipalMomentAudit.adjacencyDegreeAlgebra_transpose_mem
#print axioms PrincipalMomentAudit.MatrixPrincipal.principalIdealSpan_eq_cyclicRankOneSpan
#print axioms PrincipalMomentAudit.MatrixPrincipal.principalIdeal_full_action
#print axioms PrincipalMomentAudit.MatrixPrincipal.principalIdeal_annihilates_orthogonal
