import Mathlib.Data.Int.Basic
import Mathlib.Tactic



namespace LeMa

/-!
### Relations

A relation from `A` to `B` is a function `R : A → B → Prop`
Given `a : A` and `b : B`, we say that `a` is related to `b` if `R a b`
In other words, if `R a b` is inhabited and we can find some `h : R a b`.
-/

/- Some Examples -/

def Nat.le : ℕ → ℕ → Prop :=
  fun a b => a ≤ b

def Nat.lt : ℕ → ℕ → Prop :=
  fun a b => a < b

def Nat.dvd : ℕ → ℕ → Prop :=
  fun a b => ∃ k : ℕ, b = k * a

/-
We could alternatively define a relation from `A` to `B` as a set
`R : Set (A × B)` as we typically do in math.
This implementation is equivalent, but is not as nice to work with.
-/


variable {α : Type*}


abbrev Reflexive (R : α → α → Prop) :=
  ∀ x : α, R x x

abbrev Symmetric (R : α → α → Prop) :=
  ∀ x y : α, R x y → R y x

abbrev Transitive (R : α → α → Prop) :=
  ∀ x y z : α, R x y → R y z → R x z

abbrev AntiSymmetric (R : α → α → Prop) :=
  ∀ x y : α, R x y → R y x → x = y


/-
Tactic: `rfl`, `symm`, `trans`
Proving that a relation is Reflexive, Symmetric, Transitive
gives access to the tactics `rfl`, `symm`, `trans`.
`rfl` proves goals of the form `R x x` (along with equalities that follow by definition)
`symm` changes goals of the form `R x y` to `R y x`
`trans y` changes goals of the form `R x z` into two subgoals `R x y` and `R y z`
-/

variable (R : ℕ → ℕ → Prop)

@[refl]
theorem R_is_refl : Reflexive R := sorry

example : R 2 2 := by
  rfl


@[symm]
theorem R_is_symm : Symmetric R := sorry

example (h : R 2 3) : R 3 2 := by
  symm
  exact h


@[trans]
theorem R_is_trans : Transitive R := sorry

example (h23 : R 2 3) (h34 : R 3 4) : R 2 4 := by
  trans 3
  · exact h23
  · exact h34


/- We often use infix notation to represent a relation -/
local infixl:30 " ~ " => R
#check 2 ~ 3

/- We can use dot-notation to concisely define a relation.
The following is short for fun a b => a < b -/
#check (· < ·)




-- Exercise 20.3
theorem not_refl_mul_lt_zero : ¬ Reflexive (· * · < (0 : ℝ)) := by
  sorry

theorem symm_mul_lt_zero : Symmetric (· * · < (0 : ℝ)) := by
  sorry

theorem not_trans_mul_lt_zero : ¬ Transitive (· * · < (0 : ℝ)) := by
  sorry

theorem antisymm_mul_lt_zero : AntiSymmetric (· * · < (0 : ℝ)) := by
  sorry


-- Exercise 20.4
theorem refl_sub_mem_intCast : Reflexive (· - · ∈ Set.range ((↑) : ℤ → ℝ)) := by
  sorry

theorem symm_sub_mem_intCast : Symmetric (· - · ∈ Set.range ((↑) : ℤ → ℝ)) := by
  sorry

theorem trans_sub_mem_intCast : Transitive (· - · ∈ Set.range ((↑) : ℤ → ℝ)) := by
  sorry

theorem not_anitsymm_sub_mem_intCast : ¬ AntiSymmetric (· - · ∈ Set.range ((↑) : ℤ → ℝ)) := by
  sorry


--Exercise 20.5
theorem refl_even_sub : Reflexive (fun x y : ℤ => Even (x - y)) := by
  sorry

theorem symm_even_sub : Symmetric (fun x y : ℤ => Even (x - y)) := by
  sorry

theorem trans_even_sub : Transitive (fun x y : ℤ => Even (x - y)) := by
  sorry

theorem not_antisymm_even_sub : ¬ AntiSymmetric (fun x y : ℤ => Even (x - y)) := by
  sorry

theorem even_one_sub_iff_odd (n : ℤ) : Odd n ↔ (fun x y : ℤ => Even (x - y)) 1 n := by
  sorry


end LeMa
