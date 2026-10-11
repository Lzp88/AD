import PaperVerifier.ADComplete.SpiderArmWalks
import PaperVerifier.ADComplete.FlatWordPaths

/-! An actual weighted bijection for all short closed words visiting the center. -/
namespace ADComplete.SpiderGraph
noncomputable section
open ADClosedWalks
open scoped BigOperators

def CenterChain (L : Fin 3 → ℕ) (w : List Bool) :=
  {p : FlatClosed (graph L).Adj w // ∃ i, p.val i = none}

instance (L : Fin 3 → ℕ) (w : List Bool) : Fintype (CenterChain L w) := by
  classical
  unfold CenterChain
  infer_instance

def centerEmbed (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a) :
    Vertex (fun _ : Fin 3 => m - 1) → Vertex L
  | none => none
  | some ⟨a, i⟩ => some ⟨a, ⟨i.val, by
      have := hL a
      have hi : i.val < m - 1 := i.isLt
      omega⟩⟩

def centerDecode (L : Fin 3 → ℕ) (m : ℕ) (x : Vertex L) (hx : height x < m) :
    Vertex (fun _ : Fin 3 => m - 1) := by
  cases x with
  | none => exact none
  | some y =>
      rcases y with ⟨a, i⟩
      exact some ⟨a, ⟨i.val, by change i.val < m - 1; change i.val + 1 < m at hx; omega⟩⟩

theorem centerEmbed_decode (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a)
    (x : Vertex L) (hx : height x < m) :
    centerEmbed L m hL (centerDecode L m x hx) = x := by
  cases x with
  | none => rfl
  | some y => rcases y with ⟨a, i⟩; rfl

@[simp] theorem centerEmbed_height (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a)
    (x : Vertex (fun _ : Fin 3 => m - 1)) : height (centerEmbed L m hL x) = height x := by
  cases x <;> rfl

@[simp] theorem centerEmbed_arm (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a)
    (x : Vertex (fun _ : Fin 3 => m - 1)) : arm (centerEmbed L m hL x) = arm x := by
  cases x <;> rfl

theorem centerEmbed_injective (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a) :
    Function.Injective (centerEmbed L m hL) := by
  intro x z h
  apply vertex_eq_of_arm_height
  · simpa only [centerEmbed_arm] using congrArg arm h
  · simpa only [centerEmbed_height] using congrArg height h

theorem centerEmbed_adj (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a)
    (x z : Vertex (fun _ : Fin 3 => m - 1)) :
    (graph L).Adj (centerEmbed L m hL x) (centerEmbed L m hL z) ↔
      (graph (fun _ : Fin 3 => m - 1)).Adj x z := by
  cases x with
  | none =>
      cases z with
      | none => simp [centerEmbed]
      | some y => simp only [centerEmbed, root_adj_some]
  | some y =>
      cases z with
      | none =>
          rw [(graph L).adj_comm, (graph (fun _ : Fin 3 => m - 1)).adj_comm]
          simp only [centerEmbed, root_adj_some]
      | some q =>
          rcases y with ⟨a, i⟩
          rcases q with ⟨b, j⟩
          simp only [centerEmbed, some_adj_some]

def centerWeight {m : ℕ} : Vertex (fun _ : Fin 3 => m - 1) → ℤ
  | none => 3
  | some _ => 2

theorem centerEmbed_degree (L : Fin 3 → ℕ) (m : ℕ) (hm : 2 ≤ m)
    (hL : ∀ a, m ≤ L a) (x : Vertex (fun _ : Fin 3 => m - 1)) :
    ((graph L).degree (centerEmbed L m hL x) : ℤ) = centerWeight x := by
  cases x with
  | none =>
      rw [centerEmbed, root_degree L (by intro a; have := hL a; omega)]
      rfl
  | some y =>
      rcases y with ⟨a, i⟩
      rw [centerEmbed, arm_degree]
      have hi : i.val + 1 ≠ L a := by
        have hi : i.val < m - 1 := i.isLt
        have := hL a
        omega
      simp [hi, centerWeight]

theorem center_chain_height (L : Fin 3 → ℕ) (m : ℕ) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) (p : CenterChain L w) (i : Fin (w.length + 1)) :
    height (p.val.val i) < m := by
  have hv : valid (graph L) w (p.val.val 0) (p.val.val 0) (Fin.tail p.val.val) :=
    (valid_flat _ _ _ _ _).mpr (by simpa only [Fin.cons_self_tail] using p.val.property)
  let q := toWalk (graph L) w (p.val.val 0) (p.val.val 0) (Fin.tail p.val.val) hv
  have hq : q.length < 2 * m := by simpa only [q, toWalk_length] using hw
  obtain ⟨j, hj⟩ := p.property
  have hc : none ∈ q.support := by
    have h := positions_mem_support (graph L) w (p.val.val 0) (p.val.val 0)
      (Fin.tail p.val.val) hv j
    simpa only [Fin.cons_self_tail, hj] using h
  have hi : p.val.val i ∈ q.support := by
    simpa only [Fin.cons_self_tail] using positions_mem_support (graph L) w
      (p.val.val 0) (p.val.val 0) (Fin.tail p.val.val) hv i
  exact short_center_walk_height L m q hq hc _ hi

def centerChainMap (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a) (w : List Bool) :
    CenterChain (fun _ : Fin 3 => m - 1) w → CenterChain L w := fun p =>
  ⟨⟨centerEmbed L m hL ∘ p.val.val,
    (flatClosed_embedding_iff _ _ _ (centerEmbed_injective L m hL)
      (centerEmbed_adj L m hL) w p.val.val).mpr p.val.property⟩,
    by obtain ⟨i, hi⟩ := p.property; exact ⟨i, congrArg (centerEmbed L m hL) hi⟩⟩

theorem centerChainMap_bijective (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a)
    (w : List Bool) (hw : adjacencyCount w < 2 * m) :
    Function.Bijective (centerChainMap L m hL w) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact centerEmbed_injective L m hL
      (congrArg (fun p => p.val.val i) hpq)
  · intro p
    let y : Fin (w.length + 1) → Vertex (fun _ : Fin 3 => m - 1) := fun i =>
      centerDecode L m (p.val.val i) (center_chain_height L m w hw p i)
    have hy : centerEmbed L m hL ∘ y = p.val.val := by
      funext i
      exact centerEmbed_decode L m hL _ _
    have hv : lineValid (graph (fun _ : Fin 3 => m - 1)).Adj w y ∧ finish w y = y 0 :=
      (flatClosed_embedding_iff _ _ _ (centerEmbed_injective L m hL)
        (centerEmbed_adj L m hL) w y).mp (by rw [hy]; exact p.val.property)
    have hc : ∃ i, y i = none := by
      obtain ⟨i, hi⟩ := p.property
      refine ⟨i, centerEmbed_injective L m hL ?_⟩
      have h := congrFun hy i
      change centerEmbed L m hL (y i) = none
      exact h.trans hi
    refine ⟨⟨⟨y, hv⟩, hc⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hy

def centerChainEquiv (L : Fin 3 → ℕ) (m : ℕ) (hL : ∀ a, m ≤ L a)
    (w : List Bool) (hw : adjacencyCount w < 2 * m) :
    CenterChain (fun _ : Fin 3 => m - 1) w ≃ CenterChain L w :=
  Equiv.ofBijective _ (centerChainMap_bijective L m hL w hw)

theorem center_chain_sum (L : Fin 3 → ℕ) (m : ℕ) (hm : 2 ≤ m)
    (hL : ∀ a, m ≤ L a) (w : List Bool) (hw : adjacencyCount w < 2 * m) :
    (∑ p : CenterChain L w, lineWeight (fun v => (graph L).degree v) w p.val.val) =
      ∑ p : CenterChain (fun _ : Fin 3 => m - 1) w, lineWeight centerWeight w p.val.val := by
  symm
  apply Fintype.sum_equiv (centerChainEquiv L m hL w hw)
  intro p
  exact (lineWeight_transport centerWeight (fun v => (graph L).degree v)
    (centerEmbed L m hL) (centerEmbed_degree L m hm hL) w p.val.val).symm

#print axioms centerChainMap_bijective
#print axioms center_chain_sum
end
end ADComplete.SpiderGraph
