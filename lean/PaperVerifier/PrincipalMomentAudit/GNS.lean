import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# arXiv:2607.21494v1 Lemma 5.2: faithful real cyclic-moment realization

Translation baseline: arXiv:2607.21494v1, Lemma 5.2, source
`source/main__3_.tex` in the audited source snapshot,
lines 900--927 (source SHA256 98F9737855B7DD3B50373C6DD38F047D9BB6E2A0C8E53355A1FA5746EEFEEBB6).
The latest local `principal_ad_moments_revised.tex`, lines 836--862,
has the same mathematical statement and real bilinear GNS proof.
Words are lists over two generators, and polynomials are finite real linear
combinations of words. No graph reconstruction assertion is assumed here.
-/

namespace PrincipalMomentAudit

noncomputable section

open scoped InnerProductSpace

abbrev Word := List Bool

section Words

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Noncommutative word evaluation; the head generator acts last on a vector. -/
def wordEval (T : Bool → Module.End ℝ E) : Word → Module.End ℝ E
  | [] => LinearMap.id
  | b :: w => (T b).comp (wordEval T w)

@[simp] theorem wordEval_nil (T : Bool → Module.End ℝ E) (x : E) :
    wordEval T [] x = x := rfl

@[simp] theorem wordEval_cons (T : Bool → Module.End ℝ E) (b : Bool)
    (w : Word) (x : E) : wordEval T (b :: w) x = T b (wordEval T w x) := rfl

theorem wordEval_append (T : Bool → Module.End ℝ E) (v w : Word) (x : E) :
    wordEval T (v ++ w) x = wordEval T v (wordEval T w x) := by
  induction v with
  | nil => rfl
  | cons b v ih => simp only [List.cons_append, wordEval_cons, ih]

/-- Reversal is transpose because each generator is real symmetric. -/
theorem wordEval_inner (T : Bool → Module.End ℝ E)
    (hT : ∀ b, (T b).IsSymmetric) (w : Word) (x y : E) :
    ⟪wordEval T w x, y⟫_ℝ = ⟪x, wordEval T w.reverse y⟫_ℝ := by
  induction w generalizing x y with
  | nil => rfl
  | cons b w ih =>
    rw [wordEval_cons, hT b, ih]
    simp only [List.reverse_cons, wordEval_append, wordEval_cons, wordEval_nil]

def moment (T : Bool → Module.End ℝ E) (seed : E) (w : Word) : ℝ :=
  ⟪seed, wordEval T w seed⟫_ℝ

/-- The paper's real bilinear form `μ(v.rev * w)` is exactly the Gram form. -/
theorem word_gram (T : Bool → Module.End ℝ E)
    (hT : ∀ b, (T b).IsSymmetric) (seed : E) (v w : Word) :
    ⟪wordEval T v seed, wordEval T w seed⟫_ℝ = moment T seed (v.reverse ++ w) := by
  rw [wordEval_inner T hT]
  simp only [moment, wordEval_append]

end Words

section Gram

variable {ι E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Finite linear combinations of an indexed vector family. -/
abbrev combination (v : ι → E) : (ι →₀ ℝ) →ₗ[ℝ] E :=
  Finsupp.linearCombination ℝ v

theorem combination_gram (v : ι → E) (u : ι → F)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ) (c d : ι →₀ ℝ) :
    ⟪combination v c, combination v d⟫_ℝ =
      ⟪combination u c, combination u d⟫_ℝ := by
  simp only [combination, Finsupp.linearCombination_apply, Finsupp.sum_inner,
    Finsupp.inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp_rw [hGram]

/-- The same Gram form has the same null space, without an assumed independence condition. -/
theorem combination_ker_eq (v : ι → E) (u : ι → F)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ) :
    LinearMap.ker (combination v) = LinearMap.ker (combination u) := by
  ext c
  change combination v c = 0 ↔ combination u c = 0
  have h := combination_gram v u hGram c c
  constructor
  · intro hc
    rw [hc, inner_zero_left] at h
    exact (inner_self_eq_zero).mp h.symm
  · intro hc
    rw [hc, inner_zero_left] at h
    exact (inner_self_eq_zero).mp h

/-- The shared Gram-null quotient gives a linear equivalence of the generated spaces. -/
noncomputable def gramRangeEquiv (v : ι → E) (u : ι → F)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ) :
    LinearMap.range (combination v) ≃ₗ[ℝ] LinearMap.range (combination u) :=
  (combination v).quotKerEquivRange.symm |>.trans
    ((LinearMap.ker (combination v)).quotEquivOfEq
      (LinearMap.ker (combination u)) (combination_ker_eq v u hGram)) |>.trans
    (combination u).quotKerEquivRange

theorem gramRangeEquiv_apply_combination (v : ι → E) (u : ι → F)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ) (c : ι →₀ ℝ) :
    (gramRangeEquiv v u hGram ⟨combination v c, ⟨c, rfl⟩⟩ : F) =
      combination u c := by
  change ((combination u).quotKerEquivRange
    (((LinearMap.ker (combination v)).quotEquivOfEq
      (LinearMap.ker (combination u)) (combination_ker_eq v u hGram))
      ((combination v).quotKerEquivRange.symm ⟨combination v c, ⟨c, rfl⟩⟩)) : F) = _
  have hq : (combination v).quotKerEquivRange.symm
      ⟨combination v c, ⟨c, rfl⟩⟩ = Submodule.Quotient.mk c :=
    LinearMap.quotKerEquivRange_symm_apply_image (combination v) c ⟨c, rfl⟩
  erw [hq, Submodule.quotEquivOfEq_mk]
  rfl

/-- The Gram-null quotient equivalence is an actual linear isometric equivalence. -/
noncomputable def gramRangeIsometry (v : ι → E) (u : ι → F)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ) :
    LinearMap.range (combination v) ≃ₗᵢ[ℝ] LinearMap.range (combination u) :=
  { gramRangeEquiv v u hGram with
    norm_map' := by
      rintro ⟨_, c, rfl⟩
      change ‖(gramRangeEquiv v u hGram ⟨combination v c, ⟨c, rfl⟩⟩ : F)‖ =
        ‖combination v c‖
      rw [gramRangeEquiv_apply_combination]
      have h := combination_gram v u hGram c c
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
      nlinarith [norm_nonneg (combination v c), norm_nonneg (combination u c)] }

theorem gramRangeIsometry_apply_combination (v : ι → E) (u : ι → F)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ) (c : ι →₀ ℝ) :
    (gramRangeIsometry v u hGram ⟨combination v c, ⟨c, rfl⟩⟩ : F) =
      combination u c := gramRangeEquiv_apply_combination v u hGram c

end Gram

section Cyclic

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The principal module: evaluations of finite real linear combinations of words. -/
def principal (T : Bool → Module.End ℝ E) (seed : E) : Submodule ℝ E :=
  LinearMap.range (combination (fun w => wordEval T w seed))

/-- The range definition is exactly the word-generated span used in the paper. -/
theorem principal_eq_span (T : Bool → Module.End ℝ E) (seed : E) :
    principal T seed = Submodule.span ℝ (Set.range (fun w => wordEval T w seed)) :=
  Finsupp.range_linearCombination ℝ

theorem word_mem_principal (T : Bool → Module.End ℝ E) (seed : E) (w : Word) :
    wordEval T w seed ∈ principal T seed := by
  exact ⟨Finsupp.single w 1, by simp [combination]⟩

theorem seed_mem_principal (T : Bool → Module.End ℝ E) (seed : E) :
    seed ∈ principal T seed := word_mem_principal T seed []

/-- Generator invariance is proved from the word span, rather than assumed. -/
theorem principal_invariant (T : Bool → Module.End ℝ E) (seed : E)
    (b : Bool) (x : E) (hx : x ∈ principal T seed) : T b x ∈ principal T seed := by
  rw [principal_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨b :: w, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa using Submodule.smul_mem _ r ih

def restricted (T : Bool → Module.End ℝ E) (seed : E) (b : Bool) :
    Module.End ℝ (principal T seed) :=
  (T b).restrict (principal_invariant T seed b)

theorem moments_equal_gram (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F) (hMoment : ∀ w, moment T seed w = moment U target w)
    (v w : Word) :
    ⟪wordEval T v seed, wordEval T w seed⟫_ℝ =
      ⟪wordEval U v target, wordEval U w target⟫_ℝ := by
  rw [word_gram T hT, word_gram U hU]
  exact hMoment _

/-- Canonical isometric realization of equal principal moments (Lemma 5.2). -/
noncomputable def momentIsometry (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F) (hMoment : ∀ w, moment T seed w = moment U target w) :
    principal T seed ≃ₗᵢ[ℝ] principal U target :=
  gramRangeIsometry (fun w => wordEval T w seed) (fun w => wordEval U w target)
    (moments_equal_gram T U hT hU seed target hMoment)

theorem momentIsometry_apply_word (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F) (hMoment : ∀ w, moment T seed w = moment U target w)
    (w : Word) :
    (momentIsometry T U hT hU seed target hMoment
      ⟨wordEval T w seed, word_mem_principal T seed w⟩ : F) = wordEval U w target := by
  have h := gramRangeIsometry_apply_combination
    (fun w => wordEval T w seed) (fun w => wordEval U w target)
    (moments_equal_gram T U hT hU seed target hMoment) (Finsupp.single w 1)
  change (gramRangeIsometry (fun w => wordEval T w seed) (fun w => wordEval U w target)
    (moments_equal_gram T U hT hU seed target hMoment)
      ⟨wordEval T w seed, _⟩ : F) = wordEval U w target
  convert h using 1 <;> simp [combination]

theorem momentIsometry_seed (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F) (hMoment : ∀ w, moment T seed w = moment U target w) :
    momentIsometry T U hT hU seed target hMoment ⟨seed, seed_mem_principal T seed⟩ =
      ⟨target, seed_mem_principal U target⟩ := by
  apply Subtype.ext
  exact momentIsometry_apply_word T U hT hU seed target hMoment []

theorem momentIsometry_apply_combination
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F) (hMoment : ∀ w, moment T seed w = moment U target w)
    (c : Word →₀ ℝ) :
    (momentIsometry T U hT hU seed target hMoment
      ⟨combination (fun w => wordEval T w seed) c, ⟨c, rfl⟩⟩ : F) =
        combination (fun w => wordEval U w target) c := by
  exact gramRangeIsometry_apply_combination
    (fun w => wordEval T w seed) (fun w => wordEval U w target)
    (moments_equal_gram T U hT hU seed target hMoment) c

/-- Left multiplication by a generator on polynomials is the represented generator. -/
theorem combination_prepend (T : Bool → Module.End ℝ E) (seed : E)
    (b : Bool) (c : Word →₀ ℝ) :
    combination (fun w => wordEval T w seed) (c.mapDomain (List.cons b)) =
      T b (combination (fun w => wordEval T w seed) c) := by
  change Finsupp.linearCombination ℝ (fun w => wordEval T w seed)
    (c.mapDomain (List.cons b)) = T b (Finsupp.linearCombination ℝ _ c)
  rw [Finsupp.linearCombination_mapDomain]
  exact (Finsupp.apply_linearCombination ℝ (T b) (fun w => wordEval T w seed) c).symm

/-- The same isometry intertwines both generators on every vector in the principal module. -/
theorem momentIsometry_intertwines
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F) (hMoment : ∀ w, moment T seed w = moment U target w)
    (b : Bool) (x : principal T seed) :
    momentIsometry T U hT hU seed target hMoment (restricted T seed b x) =
      restricted U target b (momentIsometry T U hT hU seed target hMoment x) := by
  rcases x with ⟨_, c, rfl⟩
  have hSource :
      restricted T seed b ⟨combination (fun w => wordEval T w seed) c, ⟨c, rfl⟩⟩ =
        ⟨combination (fun w => wordEval T w seed) (c.mapDomain (List.cons b)),
          ⟨c.mapDomain (List.cons b), rfl⟩⟩ := by
    apply Subtype.ext
    exact (combination_prepend T seed b c).symm
  rw [hSource]
  apply Subtype.ext
  change (momentIsometry T U hT hU seed target hMoment
      ⟨combination (fun w => wordEval T w seed) (c.mapDomain (List.cons b)), _⟩ : F) =
    U b (momentIsometry T U hT hU seed target hMoment
      ⟨combination (fun w => wordEval T w seed) c, _⟩ : F)
  erw [momentIsometry_apply_combination, momentIsometry_apply_combination,
    combination_prepend]

/-- Faithful finite-dimensional statement of public arXiv:2607.21494v1 Lemma 5.2.

The hypotheses are the original real symmetric generators and equality of every
scalar word moment. Invariance, the null-space identification, seed preservation,
surjectivity, and intertwining are conclusions proved above.
-/
theorem cyclic_moment_realization [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F) (hMoment : ∀ w, moment T seed w = moment U target w) :
    ∃ Φ : principal T seed ≃ₗᵢ[ℝ] principal U target,
      Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩ ∧
      ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x) := by
  exact ⟨momentIsometry T U hT hU seed target hMoment,
    momentIsometry_seed T U hT hU seed target hMoment,
    momentIsometry_intertwines T U hT hU seed target hMoment⟩

/-- Noncommutative polynomials are finite real combinations of the word basis. -/
def polynomialMoment (T : Bool → Module.End ℝ E) (seed : E) (c : Word →₀ ℝ) : ℝ :=
  ⟪seed, combination (fun w => wordEval T w seed) c⟫_ℝ

/-- Equality on monomial words is equivalent to the paper's equality on all polynomials. -/
theorem word_moments_iff_polynomial_moments
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F) :
    (∀ w, moment T seed w = moment U target w) ↔
      (∀ c, polynomialMoment T seed c = polynomialMoment U target c) := by
  constructor
  · intro h c
    change ∀ w, ⟪seed, wordEval T w seed⟫_ℝ = ⟪target, wordEval U w target⟫_ℝ at h
    simp only [polynomialMoment, combination, Finsupp.linearCombination_apply,
      Finsupp.inner_sum, real_inner_smul_right]
    simp_rw [h]
  · intro h w
    simpa [polynomialMoment, combination, moment] using h (Finsupp.single w 1)

/-- The public lemma with its literal hypothesis of equality on all noncommutative polynomials. -/
theorem cyclic_polynomial_moment_realization
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (hT : ∀ b, (T b).IsSymmetric) (hU : ∀ b, (U b).IsSymmetric)
    (seed : E) (target : F)
    (hMoment : ∀ c, polynomialMoment T seed c = polynomialMoment U target c) :
    ∃ Φ : principal T seed ≃ₗᵢ[ℝ] principal U target,
      Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩ ∧
      ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x) :=
  cyclic_moment_realization T U hT hU seed target
    ((word_moments_iff_polynomial_moments T U seed target).mpr hMoment)

end Cyclic

end

end PrincipalMomentAudit
