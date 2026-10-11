import PaperVerifier.ADComplete.ClosedChainEquiv

/-! Flat coordinates for literal A/D chains, with an arbitrary degree weight. -/
namespace ADComplete.ADClosedWalks
noncomputable section
open scoped BigOperators

def finish {V : Type*} : (w : List Bool) → (Fin (w.length + 1) → V) → V
  | [], y => y 0
  | _ :: w, y => finish w (Fin.tail y)

def lineValid {V : Type*} (R : V → V → Prop) :
    (w : List Bool) → (Fin (w.length + 1) → V) → Prop
  | [], _ => True
  | false :: w, y => R (y 0) (y 1) ∧ lineValid R w (Fin.tail y)
  | true :: w, y => y 0 = y 1 ∧ lineValid R w (Fin.tail y)

def lineWeight {V : Type*} (d : V → ℤ) :
    (w : List Bool) → (Fin (w.length + 1) → V) → ℤ
  | [], _ => 1
  | false :: w, y => lineWeight d w (Fin.tail y)
  | true :: w, y => d (y 0) * lineWeight d w (Fin.tail y)

def FlatClosed {V : Type*} (R : V → V → Prop) (w : List Bool) :=
  {y : Fin (w.length + 1) → V // lineValid R w y ∧ finish w y = y 0}

instance {V : Type*} [Fintype V] (R : V → V → Prop) (w : List Bool) :
    Fintype (FlatClosed R w) := by
  classical
  unfold FlatClosed
  infer_instance

theorem finish_map {V W : Type*} (f : V → W) (w : List Bool)
    (y : Fin (w.length + 1) → V) : finish w (f ∘ y) = f (finish w y) := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih (Fin.tail y)

theorem valid_flat {V : Type*} (G : SimpleGraph V) (w : List Bool) (u v : V)
    (x : Fin w.length → V) : valid G w u v x ↔
    lineValid G.Adj w (Fin.cons u x) ∧ finish w (Fin.cons u x) = v := by
  induction w generalizing u v with
  | nil => simp [valid, lineValid, finish]
  | cons b w ih =>
      cases b
      · simp only [valid, lineValid, finish, Fin.cons_zero,
          Fin.tail_cons, ih, Fin.cons_self_tail]
        tauto
      · simp only [valid, lineValid, finish, Fin.cons_zero,
          Fin.tail_cons, ih, Fin.cons_self_tail]
        tauto

theorem degreeWeight_flat {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : List Bool) (u : V) (x : Fin w.length → V) :
    degreeWeight G w u x = lineWeight (fun v => G.degree v) w (Fin.cons u x) := by
  induction w generalizing u with
  | nil => rfl
  | cons b w ih =>
      cases b
      · simpa only [degreeWeight, lineWeight, Fin.tail_cons, Fin.cons_self_tail] using
          ih (x 0) (Fin.tail x)
      · change (G.degree u : ℤ) * degreeWeight G w (x 0) (Fin.tail x) =
          (G.degree u : ℤ) * lineWeight (fun v => G.degree v) w x
        rw [ih, Fin.cons_self_tail]

def closedChainFlatEquiv {V : Type*} (G : SimpleGraph V) (w : List Bool) :
    ClosedChain G w ≃ FlatClosed G.Adj w :=
  { toFun := fun p => ⟨Fin.cons p.val.1 p.val.2,
      (valid_flat G w p.val.1 p.val.1 p.val.2).mp p.property⟩
    invFun := fun y => ⟨(y.val 0, Fin.tail y.val), by
      apply (valid_flat G w (y.val 0) (y.val 0) (Fin.tail y.val)).mpr
      simpa only [Fin.cons_self_tail] using y.property⟩
    left_inv := by intro p; apply Subtype.ext; simp
    right_inv := by intro y; apply Subtype.ext; exact Fin.cons_self_tail y.val }

theorem trace_word_flat_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : List Bool) :
    Matrix.trace (wordMatrix G w) =
    ∑ y : FlatClosed G.Adj w, lineWeight (fun v => G.degree v) w y.val := by
  rw [trace_word_closedChain_sum]
  apply Fintype.sum_equiv (closedChainFlatEquiv G w)
  intro p
  exact degreeWeight_flat G w p.val.1 p.val.2

theorem lineValid_transport {V W : Type*} (R : V → V → Prop) (S : W → W → Prop)
    (f : V → W) (hR : ∀ u v, R u v → S (f u) (f v)) (w : List Bool)
    (y : Fin (w.length + 1) → V) (hy : lineValid R w y) :
    lineValid S w (f ∘ y) := by
  induction w with
  | nil => trivial
  | cons b w ih =>
      cases b
      · exact ⟨hR _ _ hy.1, ih (Fin.tail y) hy.2⟩
      · exact ⟨congrArg f hy.1, ih (Fin.tail y) hy.2⟩

theorem lineWeight_transport {V W : Type*} (d : V → ℤ) (e : W → ℤ)
    (f : V → W) (hd : ∀ v, e (f v) = d v) (w : List Bool)
    (y : Fin (w.length + 1) → V) : lineWeight e w (f ∘ y) = lineWeight d w y := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b
      · exact ih (Fin.tail y)
      · simp only [lineWeight, Function.comp_apply, hd]
        rw [show Fin.tail (f ∘ y) = f ∘ Fin.tail y from rfl, ih]

theorem lineValid_embedding_iff {V W : Type*} (R : V → V → Prop) (S : W → W → Prop)
    (f : V → W) (hf : Function.Injective f)
    (hR : ∀ u v, S (f u) (f v) ↔ R u v) (w : List Bool)
    (y : Fin (w.length + 1) → V) : lineValid S w (f ∘ y) ↔ lineValid R w y := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b
      · change S (f (y 0)) (f (y 1)) ∧ lineValid S w (f ∘ Fin.tail y) ↔ _
        rw [hR, ih]
        rfl
      · change f (y 0) = f (y 1) ∧ lineValid S w (f ∘ Fin.tail y) ↔ _
        rw [hf.eq_iff, ih]
        rfl

theorem flatClosed_embedding_iff {V W : Type*} (R : V → V → Prop) (S : W → W → Prop)
    (f : V → W) (hf : Function.Injective f)
    (hR : ∀ u v, S (f u) (f v) ↔ R u v) (w : List Bool)
    (y : Fin (w.length + 1) → V) :
    (lineValid S w (f ∘ y) ∧ finish w (f ∘ y) = (f ∘ y) 0) ↔
      (lineValid R w y ∧ finish w y = y 0) := by
  rw [lineValid_embedding_iff R S f hf hR, finish_map]
  exact and_congr_right (fun _ => hf.eq_iff)

#print axioms trace_word_flat_sum
end
end ADComplete.ADClosedWalks
