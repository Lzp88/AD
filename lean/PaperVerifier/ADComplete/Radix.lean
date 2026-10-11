import Mathlib

/-!
# Signed radix injectivity

The digits are integers, including negative digits. The base exceeds the
largest possible absolute difference of two allowed digits. The result is
for equal-length finite sequences, so trailing zero digits cause no ambiguity.
-/

namespace ADComplete.Radix

def encode (b : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: xs => a + b * encode b xs

def Bounded (H : ℤ) (xs : List ℤ) : Prop :=
  ∀ a ∈ xs, |a| ≤ H

theorem bounded_tail {H a : ℤ} {xs : List ℤ} (h : Bounded H (a :: xs)) :
    Bounded H xs := by
  intro x hx
  exact h x (List.mem_cons_of_mem a hx)

theorem head_equal {H b a c : ℤ} {xs ys : List ℤ}
    (hH : 0 ≤ H) (hb : 2 * H < b) (ha : |a| ≤ H) (hc : |c| ≤ H)
    (heq : encode b (a :: xs) = encode b (c :: ys)) : a = c := by
  have hbpos : 0 < b := by omega
  have hdvd : b ∣ a - c := by
    refine ⟨encode b ys - encode b xs, ?_⟩
    simp only [encode] at heq
    nlinarith [heq]
  have hsmall : |a - c| < b := by
    calc
      |a - c| ≤ |a| + |c| := abs_sub a c
      _ ≤ 2 * H := by omega
      _ < b := hb
  have hsmallabs : |a - c| < |b| := by
    simpa [abs_of_pos hbpos] using hsmall
  have hnat : (a - c).natAbs < b.natAbs := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hsmallabs
    exact_mod_cast hsmallabs
  exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hnat)

theorem encode_injective_of_bounded {H b : ℤ} (hH : 0 ≤ H) (hb : 2 * H < b)
    {xs ys : List ℤ} (hlen : xs.length = ys.length)
    (hxs : Bounded H xs) (hys : Bounded H ys)
    (heq : encode b xs = encode b ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons c ys => simp at hlen
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons c ys =>
          have ha : |a| ≤ H := hxs a (by simp)
          have hc : |c| ≤ H := hys c (by simp)
          have hac := head_equal hH hb ha hc heq
          have htail : encode b xs = encode b ys := by
            have hbpos : 0 < b := by omega
            simp only [encode] at heq
            rw [hac] at heq
            exact mul_left_cancel₀ (ne_of_gt hbpos) (add_left_cancel heq)
          have hlentail : xs.length = ys.length := by simpa using hlen
          rw [hac, ih hlentail (bounded_tail hxs) (bounded_tail hys) htail]

theorem encode_eq_iff {H b : ℤ} (hH : 0 ≤ H) (hb : 2 * H < b)
    {xs ys : List ℤ} (hlen : xs.length = ys.length)
    (hxs : Bounded H xs) (hys : Bounded H ys) :
    encode b xs = encode b ys ↔ xs = ys :=
  ⟨encode_injective_of_bounded hH hb hlen hxs hys, congrArg (encode b)⟩

theorem balanced_base_injective {H : ℤ} (hH : 0 ≤ H)
    {xs ys : List ℤ} (hlen : xs.length = ys.length)
    (hxs : Bounded H xs) (hys : Bounded H ys)
    (heq : encode (2 * H + 1) xs = encode (2 * H + 1) ys) : xs = ys := by
  exact encode_injective_of_bounded hH (by omega) hlen hxs hys heq

theorem encode_eq_sum (b : ℤ) (xs : List ℤ) :
    encode b xs = ∑ i : Fin xs.length, b ^ (i : ℕ) * xs[i] := by
  induction xs with
  | nil => simp [encode]
  | cons a xs ih =>
      rw [encode, ih]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [Fin.getElem_fin, Fin.val_zero, pow_zero, List.getElem_cons_zero, one_mul,
        Fin.val_succ, List.getElem_cons_succ, pow_succ]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

#print axioms encode_injective_of_bounded
#print axioms balanced_base_injective
#print axioms encode_eq_sum

end ADComplete.Radix
