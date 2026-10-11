import PaperVerifier.PrincipalMomentAudit.GNS

/-!
# Overcomplete polynomial frames and three Gram tables

No independence of the indexed frame is assumed. Equality of its Gram
matrix gives the same null space of finite linear combinations. Equality
of the two generator Gram matrices then proves actual intertwining on the
whole generated module and therefore equality of all pointed word moments.
-/

namespace ADComplete.GramTables
noncomputable section
open scoped InnerProductSpace
open PrincipalMomentAudit

variable {ι E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem pointed_isometry_moments
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (seed : E) (target : F)
    (Φ : principal T seed ≃ₗᵢ[ℝ] principal U target)
    (hseed : Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩)
    (hgen : ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x)) :
    ∀ w, moment T seed w = moment U target w := by
  have hword : ∀ w, Φ ⟨wordEval T w seed, word_mem_principal T seed w⟩ =
      ⟨wordEval U w target, word_mem_principal U target w⟩ := by
    intro w
    induction w with
    | nil => exact hseed
    | cons b w ih =>
        change Φ (restricted T seed b ⟨wordEval T w seed, word_mem_principal T seed w⟩) =
          restricted U target b ⟨wordEval U w target, word_mem_principal U target w⟩
        rw [hgen, ih]
  intro w
  have h := Φ.inner_map_map ⟨seed, seed_mem_principal T seed⟩
    ⟨wordEval T w seed, word_mem_principal T seed w⟩
  rw [hseed, hword] at h
  exact h.symm

theorem map_combination (A : Module.End ℝ E) (v : ι → E) (c : ι →₀ ℝ) :
    A (combination v c) = combination (fun i => A (v i)) c :=
  Finsupp.apply_linearCombination ℝ A v c

theorem combination_generator_gram
    (v : ι → E) (u : ι → F) (A : Module.End ℝ E) (B : Module.End ℝ F)
    (h : ∀ i j, ⟪v i, A (v j)⟫_ℝ = ⟪u i, B (u j)⟫_ℝ)
    (c d : ι →₀ ℝ) :
    ⟪combination v c, A (combination v d)⟫_ℝ =
      ⟪combination u c, B (combination u d)⟫_ℝ := by
  rw [map_combination, map_combination]
  simp only [combination, Finsupp.linearCombination_apply, Finsupp.sum_inner,
    Finsupp.inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp_rw [h]

def frameIsometry
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (seed : E) (target : F) (v : ι → E) (u : ι → F)
    (hv : LinearMap.range (combination v) = principal T seed)
    (hu : LinearMap.range (combination u) = principal U target)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ) :
    principal T seed ≃ₗᵢ[ℝ] principal U target :=
  (LinearIsometryEquiv.ofEq _ _ hv.symm).trans
    ((gramRangeIsometry v u hGram).trans (LinearIsometryEquiv.ofEq _ _ hu))

theorem frameIsometry_apply_combination
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (seed : E) (target : F) (v : ι → E) (u : ι → F)
    (hv : LinearMap.range (combination v) = principal T seed)
    (hu : LinearMap.range (combination u) = principal U target)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ)
    (c : ι →₀ ℝ) (hc : combination v c ∈ principal T seed) :
    (frameIsometry T U seed target v u hv hu hGram ⟨combination v c, hc⟩ : F) =
      combination u c := by
  unfold frameIsometry
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_ofEq_apply]
  exact gramRangeIsometry_apply_combination v u hGram c

theorem frameIsometry_intertwines
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (seed : E) (target : F) (v : ι → E) (u : ι → F)
    (hv : LinearMap.range (combination v) = principal T seed)
    (hu : LinearMap.range (combination u) = principal U target)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ)
    (hGen : ∀ b i j, ⟪v i, T b (v j)⟫_ℝ = ⟪u i, U b (u j)⟫_ℝ)
    (b : Bool) (x : principal T seed) :
    frameIsometry T U seed target v u hv hu hGram (restricted T seed b x) =
      restricted U target b (frameIsometry T U seed target v u hv hu hGram x) := by
  let Φ := frameIsometry T U seed target v u hv hu hGram
  change Φ (restricted T seed b x) = restricted U target b (Φ x)
  apply ext_inner_left ℝ
  intro y
  have hxrange : (x : E) ∈ LinearMap.range (combination v) := hv.symm ▸ x.property
  have hyrange : (y : F) ∈ LinearMap.range (combination u) := hu.symm ▸ y.property
  obtain ⟨c, hc⟩ := hxrange
  obtain ⟨d, hd⟩ := hyrange
  have hcprincipal : combination v c ∈ principal T seed := by
    rw [hc]
    exact x.property
  have hdprincipal : combination v d ∈ principal T seed := by
    rw [← hv]
    exact ⟨d, rfl⟩
  let xd : principal T seed := ⟨combination v d, hdprincipal⟩
  have hxd : Φ xd = y := by
    apply Subtype.ext
    change (frameIsometry T U seed target v u hv hu hGram
      ⟨combination v d, hdprincipal⟩ : F) = (y : F)
    rw [frameIsometry_apply_combination]
    exact hd
  have hxc : (Φ x : F) = combination u c := by
    have heqx : x = (⟨combination v c, hcprincipal⟩ : principal T seed) :=
      Subtype.ext hc.symm
    rw [heqx]
    exact frameIsometry_apply_combination T U seed target v u hv hu hGram c hcprincipal
  calc
    ⟪y, Φ (restricted T seed b x)⟫_ℝ = ⟪xd, restricted T seed b x⟫_ℝ := by
      rw [← hxd]
      exact Φ.inner_map_map xd (restricted T seed b x)
    _ = ⟪combination v d, T b (combination v c)⟫_ℝ := by
      change ⟪combination v d, T b (x : E)⟫_ℝ = _
      rw [hc]
    _ = ⟪combination u d, U b (combination u c)⟫_ℝ :=
      combination_generator_gram v u (T b) (U b) (hGen b) d c
    _ = ⟪y, restricted U target b (Φ x)⟫_ℝ := by
      change _ = ⟪(y : F), U b (Φ x : F)⟫_ℝ
      rw [hxc, hd]

theorem frameIsometry_seed
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (seed : E) (target : F) (v : ι → E) (u : ι → F)
    (hv : LinearMap.range (combination v) = principal T seed)
    (hu : LinearMap.range (combination u) = principal U target)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ)
    (i₀ : ι) (hv₀ : v i₀ = seed) (hu₀ : u i₀ = target) :
    frameIsometry T U seed target v u hv hu hGram ⟨seed, seed_mem_principal T seed⟩ =
      ⟨target, seed_mem_principal U target⟩ := by
  apply Subtype.ext
  have hc : combination v (Finsupp.single i₀ 1) ∈ principal T seed := by
    simpa [combination, hv₀] using seed_mem_principal T seed
  have h := frameIsometry_apply_combination T U seed target v u hv hu hGram
    (Finsupp.single i₀ 1) hc
  simpa [combination, hv₀, hu₀] using h

/-- Three finite tables of a spanning frame recover every pointed word moment. -/
theorem frame_three_tables_determine_moments
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F)
    (seed : E) (target : F) (v : ι → E) (u : ι → F)
    (hv : LinearMap.range (combination v) = principal T seed)
    (hu : LinearMap.range (combination u) = principal U target)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪u i, u j⟫_ℝ)
    (hGen : ∀ b i j, ⟪v i, T b (v j)⟫_ℝ = ⟪u i, U b (u j)⟫_ℝ)
    (i₀ : ι) (hv₀ : v i₀ = seed) (hu₀ : u i₀ = target) :
    ∀ w, moment T seed w = moment U target w := by
  apply pointed_isometry_moments
    T U seed target (frameIsometry T U seed target v u hv hu hGram)
  · exact frameIsometry_seed T U seed target v u hv hu hGram i₀ hv₀ hu₀
  · exact frameIsometry_intertwines T U seed target v u hv hu hGram hGen

#print axioms frameIsometry_intertwines
#print axioms frame_three_tables_determine_moments
end
end ADComplete.GramTables
