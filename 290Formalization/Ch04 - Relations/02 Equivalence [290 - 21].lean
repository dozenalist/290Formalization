import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
### Equivalence Relations

In lean, we typically state that a relation `R` is an equivalence relation
by proving `Equivalence R` which requires us to
prove that `R` is reflexive, symmetric, and transitive.
-/

def addSq : (ℝ × ℝ) → (ℝ × ℝ) → Prop
  | (a, b), (c, d) => a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2


theorem addSq_equiv : Equivalence addSq where
  refl := by
    intro x
    rfl
  symm := by
    simp only [addSq]
    intro x y h
    exact h.symm
  trans := by
    simp only [addSq]
    intro x y z h1 h2
    exact h1.trans h2


/-!
### Equivalence Classes and Quotients

Given an equivalence relation `R` on a type `X`, we can form the
quotient of `X` by `R`, the type of equivalence classes of elements of `R`
We have that equivalence classes `⟦a⟧ ⟦b⟧ : Quotient R` are equal
if and only if `a` and `b` are related by `R`.
We form the quotient by first declaring that our type `R` is a `Setoid`,
equipped with a relation and a proof that that relation is an equivalence.
This gives access to the notation `a ≈ b` for `R a b`.
-/


instance addSq_setoid : Setoid (ℝ × ℝ) where
  r := addSq
  iseqv := addSq_equiv


variable (a b : ℝ × ℝ)

#check a ≈ b

def Quot_addSq : Type :=
  Quotient addSq_setoid

#check (⟦a⟧ : Quot_addSq)


theorem Quot_addSq.eq_iff : (⟦a⟧ : Quot_addSq) = ⟦b⟧ ↔ a ≈ b := by
  exact Quotient.eq


/- The following are theorems and definitions
that are important to know when working with Quotients -/

/- `Quotient.eq` : `⟦a⟧ = ⟦b⟧ ↔ a ≈ b` -/
#check Quotient.eq

/- `Quotient.inductionOn` : If a proposition holds for all equivalence classes
`⟦a⟧ : Quotient s` then it holds for all elements `b : Quotient s` -/
#check Quotient.inductionOn

/- `Quotient.exists_rep` : For every `b : Quotient s`,
`b = ⟦a⟧` for some equivalence class `⟦a⟧`. -/
#check Quotient.exists_rep

/- `Quotient.lift` : Lift a function `f : α → β` to a function on the Quotient type
given a proof that if `a ≈ b` then `f a = f b`. -/
#check Quotient.lift
/- Note that we cannot do something like the following:

def f (s : Quotient s) : ℝ :=
  match s with
  | ⟦(a,b)⟧ => a + b
-/


-- Exercise 21.5
def Real.mul_pos (a b : ℝˣ) : Prop := a * b > (0 : ℝ)

theorem mul_pos_equiv : Equivalence Real.mul_pos where
  refl := sorry
  symm := sorry
  trans := sorry


instance mul_pos_setoid : Setoid ℝˣ where
  r := Real.mul_pos
  iseqv := mul_pos_equiv


def SignClass : Type := Quotient mul_pos_setoid

theorem SignClass.eq_one_or_neg_one (a : SignClass) : a = ⟦1⟧ ∨ a = ⟦-1⟧ := by
  sorry

theorem SignClass.one_ne_neg_one : (⟦1⟧ : SignClass) ≠ ⟦-1⟧ := by
  sorry



-- Exercise 21.6
def String.head_eq (s t : String) : Prop := s.head = t.head

theorem head_eq_equiv : Equivalence String.head_eq where
  refl := sorry
  symm := sorry
  trans := sorry

instance head_eq_setoid : Setoid String where
  r := String.head_eq
  iseqv := head_eq_equiv


-- Exercise 21.7
-- Hint: use `funext` and `propext`
#check funext
#check propext

theorem isEq_of_refl_symm_antisymm {α} (R : α → α → Prop)
  (hrefl : Reflexive R) (hsymm : Symmetric R) (hasymm : AntiSymmetric R) :
    R = Eq := by
  sorry
