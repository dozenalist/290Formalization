import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option autoImplicit false

open Set

universe u v

namespace Section20

/-- The textbook defines a relation from `A` to `B` as a set of ordered pairs in `A × B`. -/
abbrev PairRelation (A : Type u) (B : Type v) := Set (A × B)

/-- In Lean, it is usually more convenient to represent the same data as a predicate
in two variables. -/
abbrev RelationFrom (A : Type u) (B : Type v) := A → B → Prop

/-- A relation on a set `A` is just a relation from `A` to itself. -/
abbrev RelationOn (A : Type u) := RelationFrom A A

variable {A : Type u} {B : Type v}

def Relates (R : PairRelation A B) (a : A) (b : B) : Prop := (a, b) ∈ R

def asPairSet (R : RelationFrom A B) : PairRelation A B := {p | R p.1 p.2}

theorem relates_asPairSet_iff (R : RelationFrom A B) (a : A) (b : B) :
    Relates (asPairSet R) a b ↔ R a b := Iff.rfl

/- The phrase “define `a R b` if ...” is Lean’s natural style: it directly defines
the relation as a predicate. -/

def shiftByTwo : RelationFrom ℕ ℕ := fun a b => a - b = 2

example : shiftByTwo 3 1 := by
  norm_num [shiftByTwo]

example : ¬ shiftByTwo 1 3 := by
  norm_num [shiftByTwo]

def sameLength : RelationOn String := fun s t => s.length = t.length

example : sameLength "tree" "yaks" := by
  unfold sameLength
  native_decide

example : ¬ sameLength "awesome" "gum" := by
  unfold sameLength
  native_decide

def membershipRelation : RelationFrom ℕ (Set ℕ) := fun a X => a ∈ X

example : membershipRelation 2 ({1, 2, 3} : Set ℕ) := by
  simp [membershipRelation]

example : ¬ membershipRelation 2 ({1, 4, 5} : Set ℕ) := by
  simp [membershipRelation]

/-- Example 20.6: two elements are related when they lie in a common set from a
chosen family of subsets. -/
def samePiece (S : Set (Set A)) : RelationOn A :=
  fun a b => ∃ X ∈ S, a ∈ X ∧ b ∈ X

def family20_6 : Set (Set ℕ) :=
  {X | X = ({1, 2} : Set ℕ) ∨ X = ({3, 4} : Set ℕ) ∨ X = ({5} : Set ℕ)}

def relation20_6 : RelationOn ℕ := samePiece family20_6

example : relation20_6 1 2 := by
  refine ⟨({1, 2} : Set ℕ), by simp [family20_6], by simp, by simp⟩

example : ¬ relation20_6 1 4 := by
  intro h
  rcases h with ⟨X, hX, h1, h4⟩
  simp [family20_6] at hX
  rcases hX with rfl | rfl | rfl <;> simp at h1 h4

/- Relations on `ℝ` can also be viewed as subsets of `ℝ × ℝ`, which is how the
book pictures them graphically. -/

def lessThanGraph : PairRelation ℝ ℝ := asPairSet ((· < ·) : ℝ → ℝ → Prop)

example : Relates lessThanGraph 2 5 := by
  change ((2 : ℝ), 5) ∈ ({p : ℝ × ℝ | p.1 < p.2} : Set (ℝ × ℝ))
  simp
  norm_num

example : ¬ Relates lessThanGraph 5 2 := by
  change ¬ (((5 : ℝ), 2) ∈ ({p : ℝ × ℝ | p.1 < p.2} : Set (ℝ × ℝ)))
  simp
  norm_num

/-- The four main properties of a relation on a set. -/
abbrev Reflexive (R : RelationOn A) : Prop := ∀ a : A, R a a
abbrev Symmetric (R : RelationOn A) : Prop := ∀ ⦃a b : A⦄, R a b → R b a
abbrev Transitive (R : RelationOn A) : Prop := ∀ ⦃a b c : A⦄, R a b → R b c → R a c
abbrev Antisymmetric (R : RelationOn A) : Prop := ∀ ⦃a b : A⦄, R a b → R b a → a = b

open Classical in
theorem not_reflexive_iff (R : RelationOn A) :
    ¬ Reflexive R ↔ ∃ a : A, ¬ R a a := by
  simp [Reflexive]

open Classical in
theorem not_symmetric_iff (R : RelationOn A) :
    ¬ Symmetric R ↔ ∃ a b : A, R a b ∧ ¬ R b a := by
  simp [Symmetric]

open Classical in
theorem not_transitive_iff (R : RelationOn A) :
    ¬ Transitive R ↔ ∃ a b c : A, R a b ∧ R b c ∧ ¬ R a c := by
  simp [Transitive]

open Classical in
theorem not_antisymmetric_iff (R : RelationOn A) :
    ¬ Antisymmetric R ↔ ∃ a b : A, R a b ∧ R b a ∧ a ≠ b := by
  simp [Antisymmetric]

/- Worked examples for the properties. -/

theorem eq_reflexive (A : Type u) : Reflexive (@Eq A) := by
  intro a
  rfl

theorem eq_symmetric (A : Type u) : Symmetric (@Eq A) := by
  intro a b hab
  exact hab.symm

theorem eq_transitive (A : Type u) : Transitive (@Eq A) := by
  intro a b c hab hbc
  exact hab.trans hbc

theorem eq_antisymmetric (A : Type u) : Antisymmetric (@Eq A) := by
  intro a b hab hba
  exact hab

theorem lt_not_reflexive : ¬ Reflexive ((· < ·) : ℝ → ℝ → Prop) := by
  intro h
  exact lt_irrefl 0 (h 0)

theorem lt_not_symmetric : ¬ Symmetric ((· < ·) : ℝ → ℝ → Prop) := by
  intro h
  have h01 : (0 : ℝ) < 1 := by norm_num
  have h10 : (1 : ℝ) < 0 := h h01
  linarith

theorem lt_transitive : Transitive ((· < ·) : ℝ → ℝ → Prop) := by
  intro a b c hab hbc
  exact lt_trans hab hbc

theorem lt_antisymmetric : Antisymmetric ((· < ·) : ℝ → ℝ → Prop) := by
  intro a b hab hba
  exact False.elim (not_lt_of_gt hab hba)

theorem dvd_reflexive : Reflexive ((· ∣ ·) : ℕ → ℕ → Prop) := by
  intro a
  exact dvd_rfl

theorem dvd_not_symmetric : ¬ Symmetric ((· ∣ ·) : ℕ → ℕ → Prop) := by
  intro h
  have h12 : 1 ∣ 2 := by norm_num
  have h21 : 2 ∣ 1 := h h12
  norm_num at h21

theorem dvd_transitive : Transitive ((· ∣ ·) : ℕ → ℕ → Prop) := by
  intro a b c hab hbc
  exact dvd_trans hab hbc

theorem dvd_antisymmetric : Antisymmetric ((· ∣ ·) : ℕ → ℕ → Prop) := by
  intro a b hab hba
  exact Nat.dvd_antisymm hab hba

theorem subset_reflexive (A : Type u) : Reflexive ((· ⊆ ·) : Set A → Set A → Prop) := by
  intro X x hx
  exact hx

theorem subset_not_symmetric : ¬ Symmetric ((· ⊆ ·) : Set ℕ → Set ℕ → Prop) := by
  intro h
  let X : Set ℕ := {n | n = 1}
  let Y : Set ℕ := {n | n = 1 ∨ n = 2}
  have hXY : X ⊆ Y := by
    intro n hn
    simp [X, Y] at hn ⊢
    tauto
  have hYX : Y ⊆ X := h hXY
  have h2Y : 2 ∈ Y := by
    simp [Y]
  have h2X : 2 ∈ X := hYX h2Y
  simp [X] at h2X

theorem subset_transitive (A : Type u) : Transitive ((· ⊆ ·) : Set A → Set A → Prop) := by
  intro X Y Z hXY hYZ x hx
  exact hYZ (hXY hx)

theorem subset_antisymmetric (A : Type u) :
    Antisymmetric ((· ⊆ ·) : Set A → Set A → Prop) := by
  intro X Y hXY hYX
  exact Set.Subset.antisymm hXY hYX

def emptyRelation : RelationOn A := fun _ _ => False
def universalRelation : RelationOn A := fun _ _ => True

theorem empty_not_reflexive [Nonempty A] : ¬ Reflexive (emptyRelation (A := A)) := by
  intro h
  rcases ‹Nonempty A› with ⟨a⟩
  exact h a

theorem empty_symmetric : Symmetric (emptyRelation (A := A)) := by
  intro a b hab
  exact False.elim hab

theorem empty_transitive : Transitive (emptyRelation (A := A)) := by
  intro a b c hab hbc
  exact False.elim hab

theorem empty_antisymmetric : Antisymmetric (emptyRelation (A := A)) := by
  intro a b hab hba
  exact False.elim hab

theorem universal_reflexive : Reflexive (universalRelation (A := A)) := by
  intro a
  trivial

theorem universal_symmetric : Symmetric (universalRelation (A := A)) := by
  intro a b hab
  trivial

theorem universal_transitive : Transitive (universalRelation (A := A)) := by
  intro a b c hab hbc
  trivial

theorem universal_antisymmetric_iff_subsingleton (A : Type u) :
    Antisymmetric (universalRelation (A := A)) ↔ Subsingleton A := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro a b
    exact h trivial trivial
  · intro h
    intro a b hab hba
    exact Subsingleton.elim a b

/- Exercises 20.1 and 20.2 are mostly about listing sets and graphing relations as
subsets of `A × A`, so we record only the proof-oriented exercises below. -/

def oppositeSigns : RelationOn ℝ := fun x y => x * y < 0

-- Exercise 20.3
example : ¬ Reflexive oppositeSigns := by
  sorry

-- Exercise 20.3
example : Symmetric oppositeSigns := by
  sorry

-- Exercise 20.3
example : ¬ Transitive oppositeSigns := by
  sorry

-- Exercise 20.3
example : ¬ Antisymmetric oppositeSigns := by
  sorry

def differsByInteger : RelationOn ℝ := fun x y => ∃ n : ℤ, x - y = n

-- Exercise 20.4
example : Reflexive differsByInteger := by
  sorry

-- Exercise 20.4
example : Symmetric differsByInteger := by
  sorry

-- Exercise 20.4
example : Transitive differsByInteger := by
  sorry

-- Exercise 20.4
example : ¬ Antisymmetric differsByInteger := by
  sorry

def evenDifference : RelationOn ℤ := fun a b => Even (a - b)

-- Exercise 20.5
example : Reflexive evenDifference := by
  sorry

-- Exercise 20.5
example : Symmetric evenDifference := by
  sorry

-- Exercise 20.5
example : Transitive evenDifference := by
  sorry

-- Exercise 20.5
example : ¬ Antisymmetric evenDifference := by
  sorry

-- Exercise 20.5
example (b : ℤ) : evenDifference 1 b ↔ Odd b := by
  sorry

/- Exercise 20.6 asks for students to invent relations with various combinations of
properties, so we leave it as an open-ended paper exercise rather than forcing one
particular answer into Lean. -/

def family20_7 : Set (Set ℕ) :=
  {X | X = ({1, 2, 3} : Set ℕ) ∨ X = ({3, 4} : Set ℕ) ∨ X = ({5} : Set ℕ)}

def relation20_7 : RelationOn ℕ := samePiece family20_7

-- Exercise 20.7
example : Symmetric relation20_7 := by
  sorry

-- Exercise 20.7
example : ¬ Transitive relation20_7 := by
  sorry

def family20_8 : Set (Set ℕ) :=
  {X | X = ({1, 2} : Set ℕ) ∨ X = ({4, 5} : Set ℕ)}

def relation20_8 : RelationOn ℕ := samePiece family20_8

-- Exercise 20.8
example : ¬ Reflexive relation20_8 := by
  sorry

-- Exercise 20.8
example : Symmetric relation20_8 := by
  sorry

-- Exercise 20.8
example : Transitive relation20_8 := by
  sorry

end Section20
