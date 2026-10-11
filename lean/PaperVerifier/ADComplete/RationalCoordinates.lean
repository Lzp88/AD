import PaperVerifier.ADComplete.PolynomialPrimitivity

/-! Common denominator clearing and primitive representatives of rational lines. -/
namespace ADComplete.RationalCoordinates

open Polynomial
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem clear_denominators (v : ι → RatFunc ℝ) :
    ∃ d : ℝ[X], d ≠ 0 ∧ ∃ p : ι → ℝ[X],
      ∀ i, algebraMap ℝ[X] (RatFunc ℝ) (p i) =
        algebraMap ℝ[X] (RatFunc ℝ) d * v i := by
  classical
  let d : ℝ[X] := ∏ i, (v i).denom
  let p : ι → ℝ[X] := fun i => (v i).num *
    ∏ j ∈ Finset.univ.erase i, (v j).denom
  have hd : d ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact RatFunc.denom_ne_zero (v i)
  refine ⟨d, hd, p, ?_⟩
  intro i
  have hprod : d = (v i).denom * ∏ j ∈ Finset.univ.erase i, (v j).denom := by
    exact (Finset.mul_prod_erase Finset.univ (fun j => (v j).denom)
      (Finset.mem_univ i)).symm
  have hcancel : algebraMap ℝ[X] (RatFunc ℝ) (v i).denom * v i =
      algebraMap ℝ[X] (RatFunc ℝ) (v i).num := by
    calc
      _ = algebraMap ℝ[X] (RatFunc ℝ) (v i).denom *
          (algebraMap ℝ[X] (RatFunc ℝ) (v i).num /
            algebraMap ℝ[X] (RatFunc ℝ) (v i).denom) := by
              rw [RatFunc.num_div_denom]
      _ = _ := by
        field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (v i))]
  simp only [p, map_mul]
  rw [hprod, map_mul]
  calc
    _ = algebraMap ℝ[X] (RatFunc ℝ) (∏ j ∈ Finset.univ.erase i, (v j).denom) *
          algebraMap ℝ[X] (RatFunc ℝ) (v i).num := by ring
    _ = _ := by rw [← hcancel]; ring

theorem primitive_representative (v : ι → RatFunc ℝ) (hv : v ≠ 0) :
    ∃ c : RatFunc ℝ, c ≠ 0 ∧ ∃ w : ι → ℝ[X],
      PolynomialPrimitivity.Primitive w ∧
      ∀ i, v i = c * algebraMap ℝ[X] (RatFunc ℝ) (w i) := by
  classical
  obtain ⟨d, hd, p, hp⟩ := clear_denominators v
  have hd' : algebraMap ℝ[X] (RatFunc ℝ) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hpn : ∃ i, p i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    refine ⟨i, ?_⟩
    intro hz
    have hh := hp i
    rw [hz, map_zero] at hh
    exact (mul_ne_zero hd' hi) hh.symm
  obtain ⟨g, hg, w, hw, hgw⟩ := PolynomialPrimitivity.extract_primitive p hpn
  refine ⟨algebraMap ℝ[X] (RatFunc ℝ) g / algebraMap ℝ[X] (RatFunc ℝ) d,
    div_ne_zero (RatFunc.algebraMap_ne_zero hg) hd', w, hw, ?_⟩
  intro i
  have hh := hp i
  rw [hgw i, map_mul] at hh
  apply (mul_left_cancel₀ hd')
  calc
    _ = algebraMap ℝ[X] (RatFunc ℝ) g *
        algebraMap ℝ[X] (RatFunc ℝ) (w i) := hh.symm
    _ = _ := by field_simp

#print axioms clear_denominators
#print axioms primitive_representative

end
end ADComplete.RationalCoordinates
