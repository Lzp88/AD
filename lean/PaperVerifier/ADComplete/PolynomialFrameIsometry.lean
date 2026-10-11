import PaperVerifier.ADComplete.GramTables

/-!
# Three tables are equivalent to pointed isometry for a shared polynomial frame

The coefficients may be arbitrary real numbers. The same prescribed word
coefficients are evaluated on both representations. This shared-polynomial
condition is what makes the reverse direction automatic.
-/
namespace ADComplete.PolynomialFrameIsometry
noncomputable section
open scoped InnerProductSpace
open PrincipalMomentAudit

variable {ι E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def polynomialVector (T : Bool → Module.End ℝ E) (seed : E) (c : Word →₀ ℝ) : E :=
  combination (fun w => wordEval T w seed) c

def principalWord (T : Bool → Module.End ℝ E) (seed : E) (w : Word) : principal T seed :=
  ⟨wordEval T w seed, word_mem_principal T seed w⟩

def principalPolynomial (T : Bool → Module.End ℝ E) (seed : E) (c : Word →₀ ℝ) :
    principal T seed := combination (principalWord T seed) c

@[simp] theorem principalPolynomial_coe (T : Bool → Module.End ℝ E) (seed : E)
    (c : Word →₀ ℝ) : (principalPolynomial T seed c : E) = polynomialVector T seed c := by
  simp [principalPolynomial, polynomialVector, combination, Finsupp.linearCombination_apply,
    Finsupp.sum, principalWord]

theorem pointed_isometry_word_transport
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F)
    (Φ : principal T seed ≃ₗᵢ[ℝ] principal U target)
    (hseed : Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩)
    (hgen : ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x)) (w : Word) :
    Φ (principalWord T seed w) = principalWord U target w := by
  induction w with
  | nil => exact hseed
  | cons b w ih =>
      change Φ (restricted T seed b (principalWord T seed w)) =
        restricted U target b (principalWord U target w)
      rw [hgen, ih]

theorem pointed_isometry_polynomial_transport
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F)
    (Φ : principal T seed ≃ₗᵢ[ℝ] principal U target)
    (hseed : Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩)
    (hgen : ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x)) (c : Word →₀ ℝ) :
    Φ (principalPolynomial T seed c) = principalPolynomial U target c := by
  unfold principalPolynomial combination
  change Φ.toLinearMap ((Finsupp.linearCombination ℝ (principalWord T seed)) c) = _
  rw [Finsupp.apply_linearCombination ℝ Φ.toLinearMap (principalWord T seed) c]
  have hf : (Φ.toLinearMap ∘ principalWord T seed) = principalWord U target := by
    funext w
    exact pointed_isometry_word_transport T U seed target Φ hseed hgen w
  rw [hf]

def polynomialFrame (T : Bool → Module.End ℝ E) (seed : E) (cs : ι → Word →₀ ℝ) : ι → E :=
  fun i => polynomialVector T seed (cs i)

/-- Three tables determine precisely the pointed self-adjoint representation
on the cyclic module, using the same redundant real polynomial frame. -/
theorem three_tables_iff_pointed_isometry
    (T : Bool → Module.End ℝ E) (U : Bool → Module.End ℝ F) (seed : E) (target : F)
    (cs : ι → Word →₀ ℝ)
    (hT : LinearMap.range (combination (polynomialFrame T seed cs)) = principal T seed)
    (hU : LinearMap.range (combination (polynomialFrame U target cs)) = principal U target)
    (i₀ : ι) (hc₀ : cs i₀ = Finsupp.single [] 1) :
    ((∀ i j, ⟪polynomialFrame T seed cs i, polynomialFrame T seed cs j⟫_ℝ =
        ⟪polynomialFrame U target cs i, polynomialFrame U target cs j⟫_ℝ) ∧
      (∀ b i j, ⟪polynomialFrame T seed cs i, T b (polynomialFrame T seed cs j)⟫_ℝ =
        ⟪polynomialFrame U target cs i, U b (polynomialFrame U target cs j)⟫_ℝ)) ↔
    ∃ Φ : principal T seed ≃ₗᵢ[ℝ] principal U target,
      Φ ⟨seed, seed_mem_principal T seed⟩ = ⟨target, seed_mem_principal U target⟩ ∧
        ∀ b x, Φ (restricted T seed b x) = restricted U target b (Φ x) := by
  constructor
  · rintro ⟨hGram, hGen⟩
    have hv₀ : polynomialFrame T seed cs i₀ = seed := by
      simp [polynomialFrame, polynomialVector, hc₀, combination]
    have hu₀ : polynomialFrame U target cs i₀ = target := by
      simp [polynomialFrame, polynomialVector, hc₀, combination]
    refine ⟨GramTables.frameIsometry T U seed target _ _ hT hU hGram, ?_, ?_⟩
    · exact GramTables.frameIsometry_seed T U seed target _ _ hT hU hGram i₀ hv₀ hu₀
    · exact GramTables.frameIsometry_intertwines T U seed target _ _ hT hU hGram hGen
  · rintro ⟨Φ, hseed, hgen⟩
    have hc (i : ι) := pointed_isometry_polynomial_transport T U seed target Φ hseed hgen (cs i)
    constructor
    · intro i j
      have h := Φ.inner_map_map (principalPolynomial T seed (cs i))
        (principalPolynomial T seed (cs j))
      rw [hc i, hc j] at h
      simpa only [Submodule.coe_inner, principalPolynomial_coe, polynomialFrame] using h.symm
    · intro b i j
      have h := Φ.inner_map_map (principalPolynomial T seed (cs i))
        (restricted T seed b (principalPolynomial T seed (cs j)))
      rw [hc i, hgen, hc j] at h
      simpa only [Submodule.coe_inner, restricted, LinearMap.restrict_apply,
        principalPolynomial_coe, polynomialFrame] using h.symm

#print axioms pointed_isometry_polynomial_transport
#print axioms three_tables_iff_pointed_isometry
end
end ADComplete.PolynomialFrameIsometry
