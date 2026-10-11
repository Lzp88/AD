import PaperVerifier.PrincipalMomentAudit.FinalOrbitGeometry
import PaperVerifier.PrincipalMomentAudit.OrbitRepresentation
import PaperVerifier.PrincipalMomentAudit.StageQuotientCounts
import PaperVerifier.PrincipalMomentAudit.PointedTransport

/-!
# Shared literal coordinate idempotents on the actual orbit quotient

This uses the quotient of the original automorphism partition throughout
the pruning stages. Its matrices act on unnormalized orbit coefficients;
symmetry is measured with actual orbit-size weights.
-/

namespace PrincipalMomentAudit.SharedCoordinateFamily

open Matrix Finset PrincipalMomentAudit.Transport PrincipalMomentAudit.SelectorEvaluation
open PrincipalMomentAudit.ForestPruning PrincipalMomentAudit.OrbitQuotient PrincipalMomentAudit.OrbitRepresentation
open PrincipalMomentAudit.IntrinsicRecovery PrincipalMomentAudit.SharedVectorFamily PrincipalMomentAudit.FinalOrbitGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def quotientValue (p : Expression) : Matrix (Orbit G) (Orbit G) ℝ :=
  matrixEval (adjacencyQuotient G) (degreeQuotient G) p

/-- Actual diagonal selectors descend to diagonal selectors on the original
orbit coefficient space, as a consequence of the literal representation. -/
theorem quotient_selector (p : Expression) (W : Finset V)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector W) :
    quotientValue G p = Matrix.diagonal (fun i => if i.out ∈ W then 1 else 0) := by
  unfold quotientValue
  ext i j
  rw [PrincipalMomentAudit.StageQuotientCounts.quotient_eval_entry, hp, PrincipalMomentAudit.vertexSelector,
    Matrix.mulVec_diagonal]
  have hout : classOf G i.out = i := Quotient.out_eq i
  change (if i.out ∈ W then (1 : ℝ) else 0) *
    ((Pi.single j 1 : Orbit G → ℝ) (classOf G i.out)) =
      (if i = j then (if i.out ∈ W then 1 else 0) else 0)
  rw [hout]
  rw [Pi.single_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem quotient_orbit_selector (p : Expression) (i : Orbit G)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector (orbitVertices G i)) :
    quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i := by
  rw [quotient_selector G p _ hp]
  ext j k
  have hout : classOf G j.out = j := Quotient.out_eq j
  change (if j = k then (if j.out ∈ orbitVertices G i then (1 : ℝ) else 0) else 0) =
    (if j = k then (if j = i then 1 else 0) else 0)
  simp [orbitVertices, hout]

theorem quotient_empty_selector (p : Expression)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector ∅) :
    quotientValue G p = 0 := by
  rw [quotient_selector G p _ hp]
  simp

omit [Fintype V] in
theorem vertexIndicator_injective : Function.Injective (vertexIndicator (V := V)) := by
  intro W Z h
  ext v
  have hv := congrArg (fun x : V → ℝ => x v) h
  change (if v ∈ W then (1 : ℝ) else 0) = (if v ∈ Z then 1 else 0) at hv
  by_cases hw : v ∈ W <;> by_cases hz : v ∈ Z <;> simp_all

theorem quotient_selector_of_seed (p : Expression) (W : Finset V) (i : Orbit G)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector W)
    (hseed : seedVector G p = vertexIndicator (orbitVertices G i)) :
    quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i := by
  have hW : W = orbitVertices G i := by
    apply vertexIndicator_injective
    simpa only [seedVector, hp, vertexSelector_mulVec_ones] using hseed
  rw [hW] at hp
  exact quotient_orbit_selector G p i hp

theorem quotient_selector_of_zero_seed (p : Expression) (W : Finset V)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector W)
    (hseed : seedVector G p = 0) : quotientValue G p = 0 := by
  have hW : W = ∅ := by
    apply vertexIndicator_injective
    have he : vertexIndicator W = 0 := by
      simpa only [seedVector, hp, vertexSelector_mulVec_ones] using hseed
    rw [he]
    ext v
    simp [vertexIndicator]
  rw [hW] at hp
  exact quotient_empty_selector G p hp

theorem terminal_seed_selector (p : Expression) (hp : p ∈ terminalSeeds (Fintype.card V)) :
    ∃ W : Finset V, matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector W := by
  simp only [terminalSeeds, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨r, _, rfl⟩ | ⟨⟨r, q⟩, _, rfl⟩
  · exact ⟨_, centerVertexType_matrixEval _ _ _ G _ _ (all_stages_realizes G _) r⟩
  · exact ⟨_, centerEdgeType_matrixEval _ _ _ G _ _ (all_stages_realizes G _) r q⟩

theorem terminal_coordinate_sound (p : Expression) (hp : p ∈ terminalSeeds (Fintype.card V)) :
    quotientValue G p = 0 ∨ ∃ i : Orbit G, i.out ∈ stageActive G (Fintype.card V) ∧
      quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i := by
  obtain ⟨W, hW⟩ := terminal_seed_selector G p hp
  rcases terminal_sound G (actual_orbit_geometry G) p hp with hz | ⟨i, hi, he⟩
  · exact Or.inl (quotient_selector_of_zero_seed G p W hW hz)
  · exact Or.inr ⟨i, hi, quotient_selector_of_seed G p W i hW he⟩

theorem terminal_coordinate_cover (hForest : G.IsAcyclic) (i : Orbit G)
    (hi : i.out ∈ stageActive G (Fintype.card V)) :
    ∃ p ∈ terminalSeeds (Fintype.card V), quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i := by
  obtain ⟨p, hp, he⟩ := terminal_cover G hForest (actual_orbit_geometry G) i hi
  obtain ⟨W, hW⟩ := terminal_seed_selector G p hp
  exact ⟨p, hp, quotient_selector_of_seed G p W i hW he⟩

theorem reverse_product_eval (t : ℕ) (r : StageType (Fintype.card V) t)
    (ep : Expression) (p : Orbit G) (hep : quotientValue G ep = PrincipalMomentAudit.Quotient.coordinate p) :
    quotientValue G ((literalState (Fintype.card V) t).reverseQuotient (Fintype.card V) r ep) =
      PrincipalMomentAudit.Quotient.reverseProduct
        (fun i j => (PrincipalMomentAudit.StageQuotientCounts.currentCounts G t i j : ℝ))
        (PrincipalMomentAudit.StageQuotientCounts.typedOrbits G t r) p := by
  unfold quotientValue at hep ⊢
  simp only [PruningState.reverseQuotient, matrixEval,
    PrincipalMomentAudit.StageQuotientCounts.current_adjacency_matrixEval,
    PrincipalMomentAudit.StageQuotientCounts.typed_selector_matrixEval, hep]
  rfl

theorem actual_reverse_coordinate (t : ℕ) (r : StageType (Fintype.card V) t)
    (c : Orbit G) (hc : c ∈ PrincipalMomentAudit.StageQuotientCounts.typedOrbits G t r)
    (ep : Expression) (p : Orbit G) (hep : quotientValue G ep = PrincipalMomentAudit.Quotient.coordinate p)
    (hpc : PrincipalMomentAudit.StageQuotientCounts.parentOrbit G t c = p) :
    quotientValue G (positiveExpression (Fintype.card V)
      ((literalState (Fintype.card V) t).reverseQuotient (Fintype.card V) r ep)) =
        PrincipalMomentAudit.Quotient.coordinate c := by
  have heval := (reverse_product_eval G t r ep p hep).trans
    (PrincipalMomentAudit.StageQuotientCounts.reverse_product_value G t r p c hc hpc)
  exact positiveExpression_coordinate _ _ _ _ _ c heval
    (PrincipalMomentAudit.StageQuotientCounts.count_bound G t p c)
    (PrincipalMomentAudit.StageQuotientCounts.backward_count_positive G t r c hc p hpc)

theorem actual_reverse_empty (t : ℕ) (r : StageType (Fintype.card V) t)
    (ep : Expression) (p : Orbit G) (hep : quotientValue G ep = PrincipalMomentAudit.Quotient.coordinate p)
    (hempty : ∀ c ∈ PrincipalMomentAudit.StageQuotientCounts.typedOrbits G t r,
      PrincipalMomentAudit.StageQuotientCounts.parentOrbit G t c ≠ p) :
    quotientValue G (positiveExpression (Fintype.card V)
      ((literalState (Fintype.card V) t).reverseQuotient (Fintype.card V) r ep)) = 0 := by
  exact positiveExpression_zero _ _ _ _ ((reverse_product_eval G t r ep p hep).trans
    (PrincipalMomentAudit.StageQuotientCounts.reverse_product_empty G t r p hempty))

theorem actual_reverse_sound (t : ℕ) (r : StageType (Fintype.card V) t)
    (ep : Expression) (p : Orbit G) (hep : quotientValue G ep = PrincipalMomentAudit.Quotient.coordinate p) :
    quotientValue G (positiveExpression (Fintype.card V)
      ((literalState (Fintype.card V) t).reverseQuotient (Fintype.card V) r ep)) = 0 ∨
    ∃ c ∈ PrincipalMomentAudit.StageQuotientCounts.typedOrbits G t r,
      quotientValue G (positiveExpression (Fintype.card V)
        ((literalState (Fintype.card V) t).reverseQuotient (Fintype.card V) r ep)) =
          PrincipalMomentAudit.Quotient.coordinate c := by
  classical
  by_cases hc : ∃ c ∈ PrincipalMomentAudit.StageQuotientCounts.typedOrbits G t r,
      PrincipalMomentAudit.StageQuotientCounts.parentOrbit G t c = p
  · obtain ⟨c, hc, hpc⟩ := hc
    exact Or.inr ⟨c, hc, actual_reverse_coordinate G t r c hc ep p hep hpc⟩
  · exact Or.inl (actual_reverse_empty G t r ep p hep (fun c hcm hpc => hc ⟨c, hcm, hpc⟩))

def CoordinateSoundAt (k : ℕ) : Prop :=
  ∀ p ∈ recoverySteps (Fintype.card V) k, quotientValue G p = 0 ∨
    ∃ i : Orbit G, i.out ∈ stageActive G (Fintype.card V - k) ∧
      quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i

def CoordinateCoverAt (k : ℕ) : Prop :=
  ∀ i : Orbit G, i.out ∈ stageActive G (Fintype.card V - k) →
    ∃ p ∈ recoverySteps (Fintype.card V) k, quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i

theorem coordinate_family_at (hForest : G.IsAcyclic) (k : ℕ) (hk : k ≤ Fintype.card V) :
    CoordinateSoundAt G k ∧ CoordinateCoverAt G k := by
  induction k with
  | zero => exact ⟨terminal_coordinate_sound G, terminal_coordinate_cover G hForest⟩
  | succ k ih =>
      have hk0 : k ≤ Fintype.card V := by omega
      rcases ih hk0 with ⟨hs, hc⟩
      let t := Fintype.card V - (k + 1)
      have hstage : Fintype.card V - k = t + 1 := by dsimp [t]; omega
      constructor
      · intro p hp
        simp only [recoverySteps, List.mem_append] at hp
        rcases hp with hp | hp
        · rcases hs p hp with hz | ⟨i, hi, he⟩
          · exact Or.inl hz
          · rw [hstage] at hi
            exact Or.inr ⟨i, nextActive_subset G (stageActive G t) hi, he⟩
        · simp only [reverseSeeds, List.mem_flatMap, List.mem_map] at hp
          rcases hp with ⟨r, _, q, hq, rfl⟩
          rcases hs q hq with hz | ⟨i, _, he⟩
          · left
            unfold quotientValue at hz ⊢
            apply positiveExpression_zero
            simp [PruningState.reverseQuotient, matrixEval, hz]
          · rcases actual_reverse_sound G t r q i he with hz | ⟨j, hj, hjval⟩
            · exact Or.inl hz
            · exact Or.inr ⟨j, peelable_subset_active G _
                ((mem_typeCell _ _ _ _).mp (Finset.mem_filter.mp hj).2).1, hjval⟩
      · intro i hi
        by_cases hn : i.out ∈ stageActive G (t + 1)
        · have hn' : i.out ∈ stageActive G (Fintype.card V - k) := by rw [hstage]; exact hn
          obtain ⟨p, hp, he⟩ := hc i hn'
          exact ⟨p, List.mem_append.mpr (Or.inl hp), he⟩
        · have hpeel : i.out ∈ peelable (mask G (stageActive G t)) := by
            by_contra hnp
            exact hn (Finset.mem_sdiff.mpr ⟨hi, hnp⟩)
          let r := stageLabel G t i.out
          have hir : i ∈ PrincipalMomentAudit.StageQuotientCounts.typedOrbits G t r :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_typeCell _ _ _ _).mpr ⟨hpeel, rfl⟩⟩
          let j := PrincipalMomentAudit.StageQuotientCounts.parentOrbit G t i
          have hj := PrincipalMomentAudit.StageQuotientCounts.parent_active_next G t r i hir
          have hj' : j.out ∈ stageActive G (Fintype.card V - k) := by rw [hstage]; exact hj
          obtain ⟨p, hp, he⟩ := hc j hj'
          refine ⟨positiveExpression (Fintype.card V)
            ((literalState (Fintype.card V) t).reverseQuotient (Fintype.card V) r p),
            List.mem_append.mpr (Or.inr (reverse_seed_mem _ t _ r p hp)), ?_⟩
          exact actual_reverse_coordinate G t r i hir p j he rfl

/-- Every expression in the one common finite list is exactly zero or a true
coordinate idempotent of the original orbit quotient. -/
theorem coordinate_family_sound (hForest : G.IsAcyclic) (p : Expression)
    (hp : p ∈ recoveryFamily (Fintype.card V)) :
    quotientValue G p = 0 ∨ ∃ i : Orbit G, quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i := by
  rcases (coordinate_family_at G hForest _ (Nat.le_refl _)).1 p hp with hz | ⟨i, _, hi⟩
  · exact Or.inl hz
  · exact Or.inr ⟨i, hi⟩

/-- Every actual coordinate idempotent occurs. This is the full literal
recovery conclusion, with no projection-existence or geometry premise. -/
theorem coordinate_family_covers (hForest : G.IsAcyclic) (i : Orbit G) :
    ∃ p ∈ recoveryFamily (Fintype.card V), quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i := by
  exact (coordinate_family_at G hForest _ (Nat.le_refl _)).2 i (by simp [stageActive])

def coordinateFamily (N : ℕ) : Set Expression := {p | p ∈ recoveryFamily N}

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem coordinate_mulVec_one (i : Orbit G) :
    PrincipalMomentAudit.Quotient.coordinate i *ᵥ (fun _ => 1) = Pi.single i 1 := by
  ext j
  simp [PrincipalMomentAudit.Quotient.coordinate, Matrix.mulVec_diagonal, Pi.single_apply, eq_comm]

theorem seedValue_of_coordinate (p : Expression) (i : Orbit G)
    (hp : quotientValue G p = PrincipalMomentAudit.Quotient.coordinate i) :
    PrincipalMomentAudit.SharedFamilyMomentRigidity.seedValue G p = indicator G i := by
  have h := matrixEval_quotient_compatibility G p (fun _ => 1)
  change quotientLift G (quotientValue G p *ᵥ (fun _ => 1)) = _ at h
  rw [hp, coordinate_mulVec_one, quotientLift_single, quotientLift_one, matrixEval_toEuclideanLin] at h
  exact h.symm

theorem seedValue_of_zero (p : Expression) (hp : quotientValue G p = 0) :
    PrincipalMomentAudit.SharedFamilyMomentRigidity.seedValue G p = 0 := by
  have h := matrixEval_quotient_compatibility G p (fun _ => 1)
  change quotientLift G (quotientValue G p *ᵥ (fun _ => 1)) = _ at h
  rw [hp, Matrix.zero_mulVec, map_zero, quotientLift_one, matrixEval_toEuclideanLin] at h
  exact h.symm

theorem coordinate_family_seed_sound (hForest : G.IsAcyclic) :
    PrincipalMomentAudit.SharedFamilyMomentRigidity.FamilySound G (coordinateFamily (Fintype.card V)) := by
  intro p hp
  rcases coordinate_family_sound G hForest p hp with hz | ⟨i, hi⟩
  · exact Or.inl (seedValue_of_zero G p hz)
  · exact Or.inr ⟨i, seedValue_of_coordinate G p i hi⟩

theorem coordinate_family_seed_covers (hForest : G.IsAcyclic) :
    PrincipalMomentAudit.SharedFamilyMomentRigidity.FamilyCovers G (coordinateFamily (Fintype.card V)) := by
  intro i
  obtain ⟨p, hp, hi⟩ := coordinate_family_covers G hForest i
  exact ⟨p, hp, seedValue_of_coordinate G p i hi⟩

def quotientADAlgebra : Subalgebra ℝ (Matrix (Orbit G) (Orbit G) ℝ) :=
  Algebra.adjoin ℝ {adjacencyQuotient G, degreeQuotient G}

omit [DecidableEq V] in
theorem quotientValue_mem (p : Expression) : quotientValue G p ∈ quotientADAlgebra G := by
  apply matrixEval_mem
  · exact Algebra.subset_adjoin (by simp)
  · exact Algebra.subset_adjoin (by simp)

/-- All actual orbit-coordinate idempotents belong to the represented AD
algebra by the explicit common literal family, rather than a full-action shortcut. -/
theorem coordinate_mem_quotientADAlgebra (hForest : G.IsAcyclic) (i : Orbit G) :
    PrincipalMomentAudit.Quotient.coordinate i ∈ quotientADAlgebra G := by
  obtain ⟨p, _, hp⟩ := coordinate_family_covers G hForest i
  rw [← hp]
  exact quotientValue_mem G p

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The original shared-idempotent proof route recovers the actual orbit
permutation, orbit sizes and adjacency counts. The order is recovered from
the seed moment before choosing the common family. -/
theorem quotient_recovery_from_shared_coordinates (hG : G.IsAcyclic) (hH : H.IsAcyclic)
    (hμ : ∀ word, moment (PrincipalMomentAudit.GraphSemantics.generators G) (PrincipalMomentAudit.GraphSemantics.oneSeed (V := V)) word =
      moment (PrincipalMomentAudit.GraphSemantics.generators H) (PrincipalMomentAudit.GraphSemantics.oneSeed (V := W)) word) :
    ∃ e : Orbit G ≃ Orbit H,
      (∀ i, orbitSize G i = orbitSize H (e i)) ∧
      ∀ i j, quotientEntry G i j = quotientEntry H (e i) (e j) := by
  have hcard := PrincipalMomentAudit.GraphSemantics.equal_moments_same_order G H hμ
  apply PrincipalMomentAudit.SharedFamilyMomentRigidity.common_family_orbit_data G H hμ
    (coordinateFamily (Fintype.card V))
  · exact coordinate_family_seed_sound G hG
  · exact coordinate_family_seed_covers G hG
  · rw [hcard]
    exact coordinate_family_seed_sound H hH
  · rw [hcard]
    exact coordinate_family_seed_covers H hH

theorem pointed_intrinsic_recovery (hG : G.IsTree) (hH : H.IsTree)
    (Φ : principal (PrincipalMomentAudit.GraphSemantics.generators G) (PrincipalMomentAudit.GraphSemantics.oneSeed (V := V)) ≃ₗᵢ[ℝ]
      principal (PrincipalMomentAudit.GraphSemantics.generators H) (PrincipalMomentAudit.GraphSemantics.oneSeed (V := W)))
    (hseed : Φ ⟨PrincipalMomentAudit.GraphSemantics.oneSeed (V := V), seed_mem_principal _ _⟩ =
      ⟨PrincipalMomentAudit.GraphSemantics.oneSeed (V := W), seed_mem_principal _ _⟩)
    (hgen : ∀ b x, Φ (restricted (PrincipalMomentAudit.GraphSemantics.generators G)
      (PrincipalMomentAudit.GraphSemantics.oneSeed (V := V)) b x) =
      restricted (PrincipalMomentAudit.GraphSemantics.generators H) (PrincipalMomentAudit.GraphSemantics.oneSeed (V := W)) b (Φ x)) :
    ∃ e : Orbit G ≃ Orbit H,
      (∀ i, orbitSize G i = orbitSize H (e i)) ∧
      ∀ i j, quotientEntry G i j = quotientEntry H (e i) (e j) := by
  apply quotient_recovery_from_shared_coordinates G H hG.isAcyclic hH.isAcyclic
  exact PrincipalMomentAudit.PointedTransport.pointed_isometry_implies_equal_word_moments _ _ _ _ Φ hseed hgen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem reverse_zero {ρ : Type*} [Fintype ρ] (A D : Matrix ι ι ℝ)
    (s : PruningState ρ) (N : ℕ) (r : ρ) (p : Expression) (hp : matrixEval A D p = 0) :
    matrixEval A D (positiveExpression N (s.reverseQuotient N r p)) = 0 := by
  apply positiveExpression_zero
  simp [PruningState.reverseQuotient, matrixEval, hp]

theorem reverse_coordinate_or_zero {ρ : Type*} [Fintype ρ]
    (A D : Matrix ι ι ℝ) (s : PruningState ρ) (N : ℕ) (r : ρ) (ep : Expression)
    (b : Matrix ι ι ℕ) (S : Finset ι) (parent : ι → ι) (sizes : ι → ℝ) (p : ι)
    (hB : matrixEval A D s.adjacency = fun i j => (b i j : ℝ))
    (hX : matrixEval A D (s.peeledType N r) = PrincipalMomentAudit.Quotient.selectedDiagonal S)
    (hEp : matrixEval A D ep = PrincipalMomentAudit.Quotient.coordinate p)
    (hdegree : ∀ a ∈ S, ∑ q, b a q = 1)
    (hparent : ∀ a ∈ S, 0 < b a (parent a))
    (hsizes : ∀ a, 0 < sizes a)
    (hbalance : ∀ a q, sizes a * (b a q : ℝ) = sizes q * (b q a : ℝ))
    (hunique : ∀ a ∈ S, ∀ d ∈ S, parent a = parent d → a = d)
    (hbound : ∀ c, b p c ≤ N) :
    matrixEval A D (positiveExpression N (s.reverseQuotient N r ep)) = 0 ∨
      ∃ c ∈ S, matrixEval A D (positiveExpression N (s.reverseQuotient N r ep)) =
        PrincipalMomentAudit.Quotient.coordinate c := by
  classical
  by_cases hex : ∃ c ∈ S, parent c = p
  · obtain ⟨c, hc, hcp⟩ := hex
    exact Or.inr ⟨c, hc, reverseExpression_coordinate A D s N r ep b S parent sizes p c
      hB hX hEp hdegree hparent hsizes hbalance hunique hc hcp (hbound c)⟩
  · have hrow : ∀ a ∈ S, ∀ q, q ≠ parent a → (b a q : ℝ) = 0 := by
      intro a ha q hq
      have hz := (PrincipalMomentAudit.Quotient.degree_one_parent_count b a (parent a)
        (hdegree a ha) (hparent a ha)).2 q hq
      simp [hz]
    have hcol := PrincipalMomentAudit.Quotient.column_parent_support_of_undirected
      (fun i j => (b i j : ℝ)) S parent hrow
      (PrincipalMomentAudit.Quotient.undirected_support_of_balance _ sizes hsizes hbalance)
    exact Or.inl (reverseExpression_empty A D s N r ep _ S parent p hB hX hEp hrow hcol
      (fun c hc hcp => hex ⟨c, hc, hcp⟩))

#print axioms quotient_selector
#print axioms terminal_coordinate_sound
#print axioms terminal_coordinate_cover
#print axioms reverse_coordinate_or_zero
#print axioms actual_reverse_coordinate
#print axioms coordinate_family_sound
#print axioms coordinate_family_covers
#print axioms coordinate_mem_quotientADAlgebra
#print axioms quotient_recovery_from_shared_coordinates
#print axioms pointed_intrinsic_recovery

end

end PrincipalMomentAudit.SharedCoordinateFamily
