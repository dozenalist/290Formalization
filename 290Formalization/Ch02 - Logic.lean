import Mathlib.Tactic





theorem contrapose_mp (p q : Prop) : (p → q) → (¬ q → ¬ p) :=
  fun h hnq hp => hnq (h hp)


-- Axiom 5.6
theorem not_forall {α} (P : α → Prop) : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) := by
  constructor <;> intro h
  { contrapose h
    intro x
    contrapose h
    exact ⟨x, h⟩ }
  { intro h'
    let ⟨x,hx⟩ := h
    exact hx (h' x) }
