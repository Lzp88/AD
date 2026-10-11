import PaperVerifier.ADComplete.ADClosedWalks

/-! Exact trace transport through weighted bijections of actual closed chains. -/
namespace ADComplete.ADClosedWalks
noncomputable section
open scoped BigOperators

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def ClosedChain (G : SimpleGraph V) (w : List Bool) :=
  {p : V × (Fin w.length → V) // valid G w p.1 p.1 p.2}

instance (G : SimpleGraph V) (w : List Bool) : Fintype (ClosedChain G w) := by
  classical
  unfold ClosedChain
  infer_instance

theorem trace_word_closedChain_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : List Bool) : Matrix.trace (wordMatrix G w) =
    ∑ p : ClosedChain G w, degreeWeight G w p.val.1 p.val.2 := by
  classical
  unfold ClosedChain
  rw [trace_word_as_weighted_closed_walks]
  trans ∑ p : V × (Fin w.length → V),
    if valid G w p.1 p.1 p.2 then degreeWeight G w p.1 p.2 else 0
  · simp only [Fintype.sum_prod_type]
  · rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _

theorem trace_eq_of_closedChainEquiv (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (w : List Bool)
    (e : ClosedChain G w ≃ ClosedChain H w)
    (he : ∀ p, degreeWeight G w p.val.1 p.val.2 =
      degreeWeight H w (e p).val.1 (e p).val.2) :
    Matrix.trace (wordMatrix G w) = Matrix.trace (wordMatrix H w) := by
  rw [trace_word_closedChain_sum, trace_word_closedChain_sum]
  exact Fintype.sum_equiv e _ _ he

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem valid_transport (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (ha : ∀ u v, G.Adj u v → H.Adj (f u) (f v))
    (w : List Bool) (u v : V) (x : Fin w.length → V)
    (hx : valid G w u v x) : valid H w (f u) (f v) (f ∘ x) := by
  induction w generalizing u v with
  | nil => exact congrArg f hx
  | cons b w ih =>
      cases b
      · exact ⟨ha _ _ hx.1, ih _ _ (Fin.tail x) hx.2⟩
      · exact ⟨congrArg f hx.1, ih _ _ (Fin.tail x) hx.2⟩

omit [DecidableEq V] [DecidableEq W] in
theorem degreeWeight_transport (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : V → W)
    (hd : ∀ u, H.degree (f u) = G.degree u) (w : List Bool) (u : V)
    (x : Fin w.length → V) : degreeWeight H w (f u) (f ∘ x) = degreeWeight G w u x := by
  induction w generalizing u with
  | nil => rfl
  | cons b w ih =>
      cases b
      · exact ih _ (Fin.tail x)
      · simp only [degreeWeight, hd, Function.comp_apply]
        rw [show Fin.tail (f ∘ x) = f ∘ Fin.tail x from rfl, ih]

#print axioms trace_eq_of_closedChainEquiv
#print axioms valid_transport
end
end ADComplete.ADClosedWalks
