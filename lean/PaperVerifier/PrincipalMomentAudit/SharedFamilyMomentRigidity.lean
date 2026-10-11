import PaperVerifier.PrincipalMomentAudit.PrincipalExpressions
import PaperVerifier.PrincipalMomentAudit.WeightedQuotientRigidity

/-!
The analytical end of public arXiv:2607.21494v1 §§3.4 and 5.2--5.4.
This module isolates the shared literal orbit-indicator family obligation:
soundness says each seeded expression is zero or an actual orbit indicator;
coverage says every actual orbit indicator occurs. These are explicit inputs
to the lemma here, not assertions that arbitrary trees already satisfy them.
The final public theorem may use this lemma only after both inputs have been
proved for the common fixed-order pruning family, with no extra hypotheses.
-/

namespace PrincipalMomentAudit.SharedFamilyMomentRigidity
noncomputable section
open PrincipalMomentAudit.Transport PrincipalMomentAudit.PrincipalExpressions PrincipalMomentAudit.OrbitQuotient
open scoped InnerProductSpace

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

def seedValue (p : Expression) : EuclideanSpace ℝ V :=
  p.eval (GraphSemantics.generators G false) (GraphSemantics.generators G true)
    (GraphSemantics.oneSeed (V := V))

def FamilySound (family : Set Expression) : Prop :=
  ∀ p ∈ family, seedValue G p = 0 ∨ ∃ i : Orbit G, seedValue G p = indicator G i

def FamilyCovers (family : Set Expression) : Prop :=
  ∀ i : Orbit G, ∃ p ∈ family, seedValue G p = indicator G i

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem indicator_ne_zero (i : Orbit G) : indicator G i ≠ 0 := by
  intro h
  have hnorm := indicator_norm_square G i
  rw [h, inner_zero_left] at hnorm
  have hpos : (0 : ℝ) < (orbitSize G i : ℝ) := by exact_mod_cast orbitSize_pos G i
  linarith

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem indicator_injective : Function.Injective (indicator G) := by
  intro i j hij
  by_contra hne
  have h := congrArg (fun z : EuclideanSpace ℝ V => z i.out) hij
  have hi : classOf G i.out = i := Quotient.out_eq i
  simp [indicator, hi, hne] at h

/-- Equal true graph moments give equal Gram forms for all literal expressions. -/
theorem seeded_expression_gram_equal
    (hμ : ∀ word, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) word =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) word)
    (p q : Expression) :
    ⟪seedValue G p, seedValue G q⟫_ℝ = ⟪seedValue H p, seedValue H q⟫_ℝ := by
  obtain ⟨Φ, hseed, hgen⟩ := GraphSemantics.graph_cyclic_moment_realization G H hμ
  have hp := expressionVector_transport _ _ _ _ Φ hseed hgen p
  have hq := expressionVector_transport _ _ _ _ Φ hseed hgen q
  have h := Φ.inner_map_map
    (expressionVector (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) p)
    (expressionVector (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) q)
  rw [hp, hq] at h
  exact h.symm

theorem seeded_expression_adjacency_gram_equal
    (hμ : ∀ word, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) word =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) word)
    (p q : Expression) :
    ⟪seedValue G p, GraphSemantics.generators G false (seedValue G q)⟫_ℝ =
      ⟪seedValue H p, GraphSemantics.generators H false (seedValue H q)⟫_ℝ := by
  exact seeded_expression_gram_equal G H hμ p (.mul .adjacency q)

theorem seedValue_zero_iff
    (hμ : ∀ word, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) word =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) word)
    (p : Expression) : seedValue G p = 0 ↔ seedValue H p = 0 := by
  have h := seeded_expression_gram_equal G H hμ p p
  constructor
  · intro hp
    rw [hp, inner_zero_left] at h
    exact (inner_self_eq_zero).mp h.symm
  · intro hp
    rw [hp, inner_zero_left] at h
    exact (inner_self_eq_zero).mp h

theorem seedValue_sub (p q : Expression) :
    seedValue G (p.sub q) = seedValue G p - seedValue G q := by
  simp [seedValue, Expression.sub, Expression.neg, Expression.eval, sub_eq_add_neg]

theorem seedValues_eq_iff
    (hμ : ∀ word, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) word =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) word)
    (p q : Expression) : seedValue G p = seedValue G q ↔ seedValue H p = seedValue H q := by
  have h := seedValue_zero_iff G H hμ (p.sub q)
  rw [seedValue_sub, seedValue_sub] at h
  simpa only [sub_eq_zero] using h

theorem common_family_orbit_data
    (hμ : ∀ word, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) word =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) word)
    (family : Set Expression) (hsoundG : FamilySound G family) (hcoverG : FamilyCovers G family)
    (hsoundH : FamilySound H family) (hcoverH : FamilyCovers H family) :
    ∃ e : Orbit G ≃ Orbit H,
      (∀ i, orbitSize G i = orbitSize H (e i)) ∧
      ∀ i j, quotientEntry G i j = quotientEntry H (e i) (e j) := by
  choose p hpFamily hpValue using hcoverG
  have hImage : ∀ i : Orbit G, ∃ j : Orbit H, seedValue H (p i) = indicator H j := by
    intro i
    rcases hsoundH (p i) (hpFamily i) with hzero | hOrbit
    · have hgzero := (seedValue_zero_iff G H hμ (p i)).mpr hzero
      rw [hpValue i] at hgzero
      exact (indicator_ne_zero G i hgzero).elim
    · exact hOrbit
  choose f hf using hImage
  have hfInjective : Function.Injective f := by
    intro i j hij
    have hvaluesH : seedValue H (p i) = seedValue H (p j) := by rw [hf i, hf j, hij]
    have hvaluesG := (seedValues_eq_iff G H hμ (p i) (p j)).mpr hvaluesH
    rw [hpValue i, hpValue j] at hvaluesG
    exact indicator_injective G hvaluesG
  have hfSurjective : Function.Surjective f := by
    intro j
    obtain ⟨q, hqFamily, hqValue⟩ := hcoverH j
    rcases hsoundG q hqFamily with hzero | ⟨i, hi⟩
    · have hhzero := (seedValue_zero_iff G H hμ q).mp hzero
      rw [hqValue] at hhzero
      exact (indicator_ne_zero H j hhzero).elim
    · refine ⟨i, ?_⟩
      have hvaluesG : seedValue G (p i) = seedValue G q := (hpValue i).trans hi.symm
      have hvaluesH := (seedValues_eq_iff G H hμ (p i) q).mp hvaluesG
      rw [hf i, hqValue] at hvaluesH
      exact indicator_injective H hvaluesH
  let e := Equiv.ofBijective f ⟨hfInjective, hfSurjective⟩
  have hs : ∀ i, orbitSize G i = orbitSize H (e i) := by
    intro i
    have h := seeded_expression_gram_equal G H hμ (p i) (p i)
    rw [hpValue i, hf i, indicator_norm_square, indicator_norm_square] at h
    exact Nat.cast_injective (R := ℝ) h
  refine ⟨e, hs, ?_⟩
  intro i j
  have h := seeded_expression_adjacency_gram_equal G H hμ (p i) (p j)
  rw [hpValue i, hpValue j, hf i, hf j, adjacency_gram, adjacency_gram] at h
  have hsReal : (orbitSize G i : ℝ) = orbitSize H (f i) := by exact_mod_cast hs i
  rw [← hsReal] at h
  have hnonzero : (orbitSize G i : ℝ) ≠ 0 := by exact_mod_cast (orbitSize_pos G i).ne'
  exact Nat.cast_injective (R := ℝ) (mul_left_cancel₀ hnonzero h)

/-- This is the final analytical implication conditional only on the explicitly
separate, still-to-be-instantiated shared-family construction. -/
theorem trees_isomorphic_of_equal_moments_and_common_family
    (hG : G.IsTree) (hH : H.IsTree)
    (hμ : ∀ word, moment (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) word =
      moment (GraphSemantics.generators H) (GraphSemantics.oneSeed (V := W)) word)
    (family : Set Expression) (hsoundG : FamilySound G family) (hcoverG : FamilyCovers G family)
    (hsoundH : FamilySound H family) (hcoverH : FamilyCovers H family) : Nonempty (G ≃g H) := by
  obtain ⟨e, hs, hB⟩ := common_family_orbit_data G H hμ family hsoundG hcoverG hsoundH hcoverH
  exact WeightedQuotientRigidity.actual_weighted_orbit_quotient_determines_tree G H hG hH e hs hB

#print axioms seeded_expression_gram_equal
#print axioms common_family_orbit_data
#print axioms trees_isomorphic_of_equal_moments_and_common_family
end
end PrincipalMomentAudit.SharedFamilyMomentRigidity
