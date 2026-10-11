import PaperVerifier.ADComplete.PSDFoldedFrame

/-! The prescribed specialization bound on the actual original integer coordinates.
The constant seed column contributes length one, so the determinant bound uses
H0^(r-1), rather than a bound in an arbitrary real quotient basis. -/

namespace ADComplete.PSDFoldedFrame

open Matrix Polynomial
open scoped BigOperators
noncomputable section

variable {ι : Type*}

theorem folded_minor_length_le (N m R : ℕ) (s : ι → ℤ)
    (u : Fin m → ι → ℤ) {r : ℕ} (rows : Fin r → ι)
    (hr0 : 0 < r) (hr : r ≤ N) (hN : 2 ≤ N)
    (hm : 1 ≤ m) (hR : 1 ≤ R)
    (hs : ∀ i, ‖s i‖ ≤ (1 : ℝ))
    (hu : ∀ a i, ‖u a i‖ ≤ (R : ℝ)) :
    PSDSpecialization.length (foldedMinor s u rows).det ≤ (H1 N m R : ℝ) := by
  classical
  have hb : 1 ≤ H0 N m R := by
    unfold H0
    have ht : 0 < 2 ^ ((N-2)*(m-1)) := by positivity
    have : 0 < m * R * 2 ^ ((N-2)*(m-1)) := by positivity
    omega
  have hbR : (1 : ℝ) ≤ (H0 N m R : ℝ) := by exact_mod_cast hb
  let bounds : Fin r → ℝ := fun j => if j.val = 0 then 1 else H0 N m R
  have hcol (i j : Fin r) :
      PSDSpecialization.length (foldedMinor s u rows i j) ≤ bounds j := by
    by_cases hj : j.val = 0
    · change PSDSpecialization.length (foldedPolynomial s u j.val (rows i)) ≤ _
      rw [hj]
      change PSDSpecialization.length (C (s (rows i))) ≤ bounds j
      rw [PSDSpecialization.length_C]
      simpa [bounds, hj] using hs (rows i)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have hkN : k ≤ N - 2 := by omega
      have hlen := PSDSpecialization.foldedEntry_length m k (N-2) hkN
        (fun a => u a (rows i)) R (fun a => hu a (rows i))
      simpa [foldedMinor, foldedPolynomial, hk, bounds, hj, H0] using hlen
  have hprod : (∏ j : Fin r, bounds j) = (H0 N m R : ℝ) ^ (r-1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr0)
    simp [bounds, Fin.prod_univ_succ]
  have hlen := PSDSpecialization.length_det_le (foldedMinor s u rows) bounds
    (fun j => by dsimp [bounds]; split_ifs <;> positivity) hcol
  rw [Fintype.card_fin, hprod] at hlen
  have hf : (r.factorial : ℝ) ≤ (N.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hr
  have he : (H0 N m R : ℝ) ^ (r-1) ≤ (H0 N m R : ℝ) ^ (N-1) :=
    pow_le_pow_right₀ hbR (by omega)
  apply hlen.trans
  change (r.factorial : ℝ) * (H0 N m R : ℝ) ^ (r-1) ≤ _
  calc
    (r.factorial : ℝ) * (H0 N m R : ℝ) ^ (r-1)
        ≤ (N.factorial : ℝ) * (H0 N m R : ℝ) ^ (N-1) := by gcongr
    _ = (H1 N m R : ℝ) := by simp [H1]

theorem folded_minor_tau_ne_zero (N m R : ℕ) (s : ι → ℤ)
    (u : Fin m → ι → ℤ) {r : ℕ} (rows : Fin r → ι)
    (hr0 : 0 < r) (hr : r ≤ N) (hN : 2 ≤ N)
    (hm : 1 ≤ m) (hR : 1 ≤ R)
    (hs : ∀ i, ‖s i‖ ≤ (1 : ℝ))
    (hu : ∀ a i, ‖u a i‖ ≤ (R : ℝ))
    (hp : (foldedMinor s u rows).det ≠ 0) :
    (foldedMinor s u rows).det.eval (tau N m R : ℤ) ≠ 0 := by
  have hh := folded_minor_length_le N m R s u rows hr0 hr hN hm hR hs hu
  simpa [tau] using PSDSpecialization.eval_length_plus_two_ne_zero
    (foldedMinor s u rows).det hp (H1 N m R) hh

#print axioms folded_minor_length_le
#print axioms folded_minor_tau_ne_zero

end
end ADComplete.PSDFoldedFrame
