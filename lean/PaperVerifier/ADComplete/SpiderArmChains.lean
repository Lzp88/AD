import PaperVerifier.ADComplete.SpiderArmWalks
import PaperVerifier.ADComplete.FlatWordPaths

/-! Actual center-free spider chains are closed coordinate chains in one arm. -/
namespace ADComplete.SpiderGraph
noncomputable section
open ADClosedWalks

def coordAdj {n : ℕ} (i j : Fin n) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

def armEmbed (L : Fin 3 → ℕ) (a : Fin 3) (i : Fin (L a)) : Vertex L := some ⟨a, i⟩

theorem armEmbed_injective (L : Fin 3 → ℕ) (a : Fin 3) :
    Function.Injective (armEmbed L a) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg height h
  simpa only [armEmbed, height, Nat.add_right_cancel_iff] using hh

theorem armEmbed_adj (L : Fin 3 → ℕ) (a : Fin 3) (i j : Fin (L a)) :
    (graph L).Adj (armEmbed L a i) (armEmbed L a j) ↔ coordAdj i j := by
  simp only [armEmbed, some_adj_some, true_and, coordAdj]

def armDecode (L : Fin 3 → ℕ) (a : Fin 3) (x : Vertex L) (hx : arm x = some a) : Fin (L a) := by
  cases x with
  | none => simp [arm] at hx
  | some y =>
      rcases y with ⟨b, i⟩
      have hb : b = a := Option.some_injective _ hx
      subst b
      exact i

theorem armEmbed_decode (L : Fin 3 → ℕ) (a : Fin 3) (x : Vertex L)
    (hx : arm x = some a) : armEmbed L a (armDecode L a x hx) = x := by
  cases x with
  | none => simp [arm] at hx
  | some y =>
      rcases y with ⟨b, i⟩
      have hb : b = a := Option.some_injective _ hx
      subst b
      rfl

theorem line_arm_constant (L : Fin 3 → ℕ) (w : List Bool)
    (y : Fin (w.length + 1) → Vertex L) (hy : lineValid (graph L).Adj w y)
    (hn : ∀ i, y i ≠ none) : ∀ i, arm (y i) = arm (y 0) := by
  induction w with
  | nil => intro i; fin_cases i; rfl
  | cons b w ih =>
      have hv : lineValid (graph L).Adj w (Fin.tail y) := by cases b <;> exact hy.2
      have ht := ih (Fin.tail y) hv (fun i => hn i.succ)
      have hh : arm (y 1) = arm (y 0) := by
        cases b
        · exact (adjacent_arm_eq L hy.1 (hn 0) (hn 1)).symm
        · exact congrArg arm hy.1.symm
      intro i
      refine Fin.cases rfl (fun j => ?_) i
      exact (ht j).trans hh

def NonCenterChain (L : Fin 3 → ℕ) (w : List Bool) :=
  {p : FlatClosed (graph L).Adj w // ¬ ∃ i, p.val i = none}

instance (L : Fin 3 → ℕ) (w : List Bool) : Fintype (NonCenterChain L w) := by
  classical
  unfold NonCenterChain
  infer_instance

def ArmChain (L : Fin 3 → ℕ) (w : List Bool) :=
  (a : Fin 3) × FlatClosed (@coordAdj (L a)) w

instance (L : Fin 3 → ℕ) (w : List Bool) : Fintype (ArmChain L w) := by
  classical
  unfold ArmChain
  infer_instance

def armChainMap (L : Fin 3 → ℕ) (w : List Bool) : ArmChain L w → NonCenterChain L w := fun p =>
  ⟨⟨armEmbed L p.1 ∘ p.2.val,
    (flatClosed_embedding_iff _ _ _ (armEmbed_injective L p.1)
      (armEmbed_adj L p.1) w p.2.val).mpr p.2.property⟩,
    by rintro ⟨i, hi⟩; exact Option.some_ne_none _ hi⟩

theorem armChainMap_bijective (L : Fin 3 → ℕ) (w : List Bool) :
    Function.Bijective (armChainMap L w) := by
  constructor
  · intro p q hpq
    have ha : p.1 = q.1 := by
      have hh := congrArg (fun z => arm (z.val.val 0)) hpq
      exact Option.some_injective _ hh
    rcases p with ⟨a, p⟩
    rcases q with ⟨b, q⟩
    change a = b at ha
    subst b
    congr 1
    apply Subtype.ext
    funext i
    exact armEmbed_injective L a (congrArg (fun z => z.val.val i) hpq)
  · intro p
    have hn (i : Fin (w.length + 1)) : p.val.val i ≠ none :=
      fun hi => p.property ⟨i, hi⟩
    have hc := line_arm_constant L w p.val.val p.val.property.1 hn
    cases h₀ : p.val.val 0 with
    | none => exact (hn 0 h₀).elim
    | some q =>
        rcases q with ⟨a, k⟩
        have har (i : Fin (w.length + 1)) : arm (p.val.val i) = some a := by
          rw [hc i, h₀]
          rfl
        let y : Fin (w.length + 1) → Fin (L a) := fun i => armDecode L a _ (har i)
        have hy : armEmbed L a ∘ y = p.val.val := by
          funext i
          exact armEmbed_decode L a _ _
        have hv : lineValid (@coordAdj (L a)) w y ∧ finish w y = y 0 :=
          (flatClosed_embedding_iff _ _ _ (armEmbed_injective L a)
            (armEmbed_adj L a) w y).mp (by rw [hy]; exact p.val.property)
        refine ⟨⟨a, ⟨y, hv⟩⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hy

def armChainEquiv (L : Fin 3 → ℕ) (w : List Bool) : ArmChain L w ≃ NonCenterChain L w :=
  Equiv.ofBijective _ (armChainMap_bijective L w)

#print axioms armChainMap_bijective
end
end ADComplete.SpiderGraph
