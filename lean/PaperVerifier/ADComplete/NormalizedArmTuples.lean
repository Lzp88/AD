import PaperVerifier.ADComplete.SpiderArmChains

/-! A faithful finite-coordinate normalization, including every allowed translation. -/
namespace ADComplete.SpiderGraph
noncomputable section
open scoped BigOperators

def NormalizedTuple (m n : ℕ) :=
  {f : Fin (n + 1) → Fin m // ∃ i, (f i).val = 0}

instance (m n : ℕ) : Fintype (NormalizedTuple m n) := by
  classical
  unfold NormalizedTuple
  infer_instance

def tupleWidth {m n : ℕ} (f : NormalizedTuple m n) : ℕ :=
  Finset.univ.sup (fun i => (f.val i).val)

theorem value_le_tupleWidth {m n : ℕ} (f : NormalizedTuple m n) (i : Fin (n + 1)) :
    (f.val i).val ≤ tupleWidth f :=
  Finset.le_sup (f := fun i => (f.val i).val) (Finset.mem_univ i)

theorem tupleWidth_lt {m n : ℕ} (hm : 0 < m) (f : NormalizedTuple m n) :
    tupleWidth f < m := by
  exact (Finset.sup_lt_iff hm).mpr (fun i _ => (f.val i).isLt)

theorem tupleWidth_attained {m n : ℕ} (f : NormalizedTuple m n) :
    ∃ i, tupleWidth f = (f.val i).val := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
    (fun i => (f.val i).val)
  exact ⟨i, hi⟩

def BoundedArmTuple (L : Fin 3 → ℕ) (m n : ℕ) :=
  (a : Fin 3) × {q : Fin (n + 1) → Fin (L a) //
    ∀ i j, (q i).val - (q j).val < m}

instance (L : Fin 3 → ℕ) (m n : ℕ) : Fintype (BoundedArmTuple L m n) := by
  classical
  unfold BoundedArmTuple
  infer_instance

def ShiftedArmTuple (L : Fin 3 → ℕ) (m n : ℕ) :=
  (f : NormalizedTuple m n) × (a : Fin 3) × Fin (L a - tupleWidth f)

instance (L : Fin 3 → ℕ) (m n : ℕ) : Fintype (ShiftedArmTuple L m n) := by
  classical
  unfold ShiftedArmTuple
  infer_instance

def shiftedTupleMap (L : Fin 3 → ℕ) (m n : ℕ) (hm : 0 < m) :
    ShiftedArmTuple L m n → BoundedArmTuple L m n := fun p =>
  ⟨p.2.1, ⟨fun i => ⟨p.2.2.val + (p.1.val i).val, by
    have ht := p.2.2.isLt
    have hi := value_le_tupleWidth p.1 i
    omega⟩, by
      intro i j
      have hi := value_le_tupleWidth p.1 i
      have hw := tupleWidth_lt hm p.1
      change (p.2.2.val + (p.1.val i).val) - (p.2.2.val + (p.1.val j).val) < m
      omega⟩⟩

def tupleMin {n l : ℕ} (q : Fin (n + 1) → Fin l) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => (q i).val)

theorem tupleMin_le {n l : ℕ} (q : Fin (n + 1) → Fin l) (i : Fin (n + 1)) :
    tupleMin q ≤ (q i).val := Finset.inf'_le (fun i => (q i).val) (Finset.mem_univ i)

theorem tupleMin_attained {n l : ℕ} (q : Fin (n + 1) → Fin l) :
    ∃ i, tupleMin q = (q i).val := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i => (q i).val)
  exact ⟨i, hi⟩

theorem shiftedTupleMap_bijective (L : Fin 3 → ℕ) (m n : ℕ) (hm : 0 < m) :
    Function.Bijective (shiftedTupleMap L m n hm) := by
  constructor
  · intro p q hpq
    rcases p with ⟨f, a, t⟩
    rcases q with ⟨g, b, s⟩
    have hab : a = b := congrArg Sigma.fst hpq
    subst b
    have hh (i : Fin (n + 1)) : t.val + (f.val i).val = s.val + (g.val i).val :=
      congrArg (fun p => (p.2.val i).val) hpq
    obtain ⟨i, hi⟩ := f.property
    obtain ⟨j, hj⟩ := g.property
    have ht : t.val = s.val := by have := hh i; have := hh j; omega
    have hfg : f = g := by
      apply Subtype.ext
      funext k
      apply Fin.ext
      have := hh k
      omega
    subst g
    have hts : t = s := Fin.ext ht
    subst s
    rfl
  · rintro ⟨a, q, hq⟩
    obtain ⟨i₀, hi₀⟩ := tupleMin_attained q
    let f : NormalizedTuple m n := ⟨fun i => ⟨(q i).val - tupleMin q, by
      have h := hq i i₀
      rw [← hi₀] at h
      exact h⟩, i₀, by simp only [hi₀, Nat.sub_self]⟩
    have hf (i : Fin (n + 1)) : tupleMin q + (f.val i).val = (q i).val :=
      Nat.add_sub_of_le (tupleMin_le q i)
    obtain ⟨j, hj⟩ := tupleWidth_attained f
    have ht : tupleMin q < L a - tupleWidth f := by
      have hqj := (q j).isLt
      have hh := hf j
      omega
    refine ⟨⟨f, a, ⟨tupleMin q, ht⟩⟩, ?_⟩
    dsimp only [shiftedTupleMap]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      funext i
      exact Fin.ext (hf i)

def shiftedTupleEquiv (L : Fin 3 → ℕ) (m n : ℕ) (hm : 0 < m) :
    ShiftedArmTuple L m n ≃ BoundedArmTuple L m n :=
  Equiv.ofBijective _ (shiftedTupleMap_bijective L m n hm)

#print axioms shiftedTupleMap_bijective
end
end ADComplete.SpiderGraph
