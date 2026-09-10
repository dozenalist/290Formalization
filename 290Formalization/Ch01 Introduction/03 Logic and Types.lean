import Mathlib.Tactic

/-
# Logic in Lean
-/

namespace LeMa

/-
### Conjunction

A proof of `P ∧ Q` consists of a proof of `P` and a proof of `Q`.

Tactic : `constructor`
If `And` is in a goal, `constructor` produces two subgoals.
If you have multiple goals, use the center dot · to focus on one
goal at a time.

If `And` is in a hypothesis `h : P ∧ Q`, use `h.left` and `h.right`
to get `P` and `Q` on their own.
-/

variable {P Q R : Prop}

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

theorem and_left (h : P ∧ Q) : P := by
  exact h.left

theorem and_right (h : P ∧ Q) : Q := by
  exact h.right

theorem and_comm : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.right
  · exact h.left

/-!
### Disjunction

Tactic : `left` and `right`
To prove `P ∨ Q`, it suffices to prove one side. The tactics `left` and
`right` indicate which side we are proving.

To use a hypothesis `h : P ∨ Q`, the tactic `cases h` splits the argument into
the two possible cases. This is followed by some pattern matching depending on
whether the left or right side is true.
-/

example (p : P) : P ∨ Q := by
  left
  exact p

example (q : Q) : P ∨ Q := by
  right
  exact q

example : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl p =>
      right
      exact p
  | inr q =>
      left
      exact q

/-
Tactic : `rcases`
An alternative to `cases` is the powerful tactic `rcases` which can
do some recursive pattern matching on complicated logical expressions.

In type theory, And is encoded using the Cartesian product, which
is written in Lean using angle brackets `⟨⟩` (hover over a symbol in
VSCode to learn how you can type it).
-/

example : (P ∨ Q) ∧ R → R ∧ (Q ∨ P) := by
  intro h
  rcases h with ⟨p | q, r⟩ -- p | q is the pattern for p ∨ q, and ⟨x, r⟩ is the pattern for x ∧ r
  constructor
  · exact r
  · right
    exact p
  constructor
  · exact r
  · left
    exact q


/-!
### Biconditional

`P ↔ Q` is just a pair of implications. To prove it, use `constructor`.
If you have `↔` in a hypothesis, use `mp` and `mpr` to get the individual directions:

`h.mp : P → Q` mp stands for modus ponens
`h.mpr : Q → P` mpr stands for modus ponens reverse
-/

example (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · exact h1
  · exact h2

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  constructor
  · exact h.mpr
  · exact h.mp

/-
Tactic : `rw`
One of the most commonly-used tactics is the rewrite tactic `rw`.
Anytime you have a statement of the form `A = B` (or `P ↔ Q`), the
rewrite tactic will replace the leftmost instance of `A` with `B`.
-/

example (h : P ↔ Q) (q : Q) : P := by
  rw [h]
  exact q


/-!
## Classical reasoning: LEM, DNE, and `open Classical`

Lean is constructive by default. This means that, in general, you cannot use:

* the law of excluded middle `P ∨ ¬ P`;
* double-negation elimination `¬¬ P → P`;
* proof by contradiction in the classical sense.

If you want those principles, a common local choice is to write
`open Classical in` before a theorem, or `open Classical` for a larger block.
Then Lean can use classical decidability for propositions.

You'll need to open classical whenever you use contrapositive or contradiction,
and sometimes when you're doing a proof by cases.
The following examples illustrate this. Don't pay too much attention to the
tactics used here; we'll cover them in more detail later.
-/

variable {P Q : Prop}

open Classical in
example : P ∨ ¬ P := by
  exact Classical.em P

open Classical in
example : ¬¬ P → P := by
  intro hNNP
  by_contra hNP
  exact hNNP hNP

open Classical in
example (hP : P → Q) (hNotP : ¬ P → Q) : Q := by
  by_cases hp : P
  · exact hP hp
  · exact hNotP hp

open Classical in
example (h : ¬¬ P) : P := by
  by_contra hNP
  exact h hNP


/-!
## Exercises
-/

variable {P Q R : Prop}

example : (P ∧ Q ∧ R) ↔ ((P ∧ Q) ∧ R) := by
  sorry

example : (P ∨ Q ∨ R) ↔ ((P ∨ Q) ∨ R) := by
  sorry

open Classical in
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  sorry
