
-- import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

set_option linter.style.emptyLine false


-- The contrapositive equivalence.


open Classical in
theorem imp_iff_contrapositive (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  constructor -- splits a biconditional goal into two implications
  · sorry -- this direction is constructive; fill in the details!
  · intro h p -- this part of the proof requires the law of excluded middle
    have hq : Q ∨ ¬Q := Classical.em Q
    cases hq with
    | inl hq => exact hq
    | inr hnq =>
      exfalso -- `exfalso` is a tactic that changes the goal to `False`
      apply h hnq p

/-
Tactic : `contrapose` and `contrapose!`
`contrapose` transforms the main goal into its contrapositive.
If the goal has the form `⊢ P → Q`, then `contrapose` turns it into `⊢ ¬ Q → ¬ P`.
If the goal has the form `⊢ P ↔ Q`, then `contrapose` turns it into `⊢ ¬ P ↔ ¬ Q`.

If you have a hypothesis `h : P` and your goal is `⊢ Q`, then `contrapose h` will
turn `h` into `h : ¬ Q` and the goal into `⊢ ¬ P`.

`contrapose!` will push the negation deeper into the goal after contraposing, using
e.g. DeMorgan's laws.
-/

open Int

-- The following theorems from Mathlib will be helpful
#check not_odd_iff_even
#check not_even_iff_odd

example {x : ℤ} (h : Even (3 * x - 7)) : Odd x := by
  contrapose h
  rw [Int.not_odd_iff_even] at h -- `at h` performs the rewrite at the hypothesis `h`
  rw [Int.not_even_iff_odd]
  obtain ⟨k, rfl⟩ := h
  use (3*k - 4)
  ring

example {x : ℤ} (h : Odd (x ^ 2 - 6 * x + 7)) : Even x := by
  contrapose h
  rw [not_even_iff_odd] at h
  rw [not_odd_iff_even]
  obtain ⟨k, rfl⟩ := h
  use (2*k^2 - 4 * k + 1)
  ring

example {a b : Int} (h : a ∣ b) : a ∣ 2 * b := by
  obtain ⟨k, rfl⟩ := h
  use (2 * k)
  ring

theorem dvd_transitive {a b c : Int}
  (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k, rfl⟩ := hab
  obtain ⟨j, rfl⟩ := hbc
  use (j * k)
  ring

theorem dvd_of_dvd_mul_add {a b c x y : Int}
  (hab : a ∣ b) (hac : a ∣ c) : a ∣ (b * x + c * y) := by
  obtain ⟨k, rfl⟩ := hab
  obtain ⟨j, rfl⟩ := hac
  use (k * x + j * y)
  ring

example {x : ℤ} (h : ¬ (2 ∣ x)) : Odd x := by
  contrapose! h
  rw [not_odd_iff_even] at h
  obtain ⟨k, rfl⟩ := h
  use k
  ring

/-- Biconditional: `n^2` is odd iff `n` is odd. One direction is direct,
		the other is contrapositive. -/
theorem sq_odd_iff_odd (n : ℤ) : Odd (n ^ 2) ↔ Odd n := by
  constructor
  · intro h
    contrapose! h
    rw [not_odd_iff_even] at *
    obtain ⟨k, rfl⟩ := h
    use 2*k^2
    ring
  · intro h
    obtain ⟨k, rfl⟩ := h
    use 2 * k^2 + 2 * k
    ring

/- Exercises -/

-- Exercise 7.1 If a^2 + 3 is odd then a is even
example {a : ℤ} (h : Odd (a ^ 2 + 3)) : Even a := by
  sorry

-- Exercise 7.2 If xy + y^2 is even then x is odd or y is even
example {x y : ℤ} (h : Even (x * y + y ^ 2)) : Odd x ∨ Even y := by
  sorry


-- Exercise 7.3 s is odd iff s^3 is odd
example (s : ℤ) : Odd s ↔ Odd (s ^ 3) := by
  sorry

-- Exercise 7.5 If a | c and b | d then ab | cd
example {a b c d : Int} (hac : a ∣ c) (hbd : b ∣ d) :
  (a * b) ∣ (c * d) := by
  sorry

-- Exercise 7.7 If 4 does not divide a^2 then a is odd
example {a : ℤ} (h : ¬ (4 ∣ a ^ 2)) : ∃ k, a = 2 * k + 1 := by
  sorry

-- Exercise 7.8a If 5x-1 is even then x is odd (direct proof)
example {x : ℤ} (h : Even (5 * x - 1)) : Odd x := by
  sorry

-- Exercise 7.8b If 5x-1 is even then x is odd (contrapositive proof)
example {x : ℤ} (h : Even (5 * x - 1)) : Odd x := by
  sorry
