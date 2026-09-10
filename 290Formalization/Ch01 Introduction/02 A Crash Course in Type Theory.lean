import Mathlib.Tactic

/-!
# A crash course in type theory for mathematicians

In type theory, there are terms and types. For now, the following
mental model will work for you (even though it's not quite right):
* `Type` = `Set`
* `Term` = `Element`
* `x : X` means that `x` is a term of type `X`. This acts like `x ∈ X`.

Lean is essentially just a fancy type checker. If you write
`thing : type`, Lean can check that `thing` is a term of type `type`.
If it isn't, you'll get an error.
-/

variable {X Y Z : Type}

/-
The next example does the following: Given a function f : X → Y,
and a term x of type X, construct a term of type Y.

Of course the solution is that f(x) has type Y, so that's what we write.
Function application is written `f x` instead of `f(x)`

Tactic : `exact`
If you can exactly construct the term it's looking for, use the tactic `exact`.
-/

example (f : X → Y) (x : X) : Y := by
  exact f x


/-
In type theory, propositions are also types. If `P : Prop` then `P` is
a proposition. It can be helpful to think of `P` as a set whose elements
are its proofs. If `P` is the empty set, it's `False`. If `P` is nonempty
(in type theory we say it's "inhabited") then it's `True`.
So `h : P` means `h` is a proof of `P`.

Implication `P implies Q` is denoted `P → Q`. This looks a lot like a function.
That's because it is! In type theory, implication is just a function that
sends proofs of `P` to proofs of `Q`.
-/

variable {P Q R : Prop}

/-
The next example proves the theorem: If we know `P` implies `Q` and we have a
proof of `P`, then `Q` is true.

Observe that the statement and proof are identical to the previous example!
-/

example (h : P → Q) (p : P) : Q := by
  exact h p


/-
Functions are primitive in type theory. Thus, much of what we do in Lean
involves functions.

Tactic : `intro`
When defining a function `f : X → Y`, we might start by saying "given an
element `x` of `X`, ...". The tactic `intro` introduces an element of `X`.
Similarly, when proving an implication `P → Q` we might start by saying
"suppose `P` is true, ...". The tactic `intro` introduces a proof of `P`.

Tactic : `apply`
This very common tactic "works backwards" from the goal. If we want to
prove `Q` and we have `h : P → Q`, we might say "by `h`, it suffices to
supply a proof of `P`". The `apply` tactic pulls back along the arrow
to change the goal from `Q` to `P`.

Put your cursor on each line of the following definition and proof, and
see how the tactic state in the sidebar changes as we use each tactic.
-/

def compose (g : Y → Z) (f : X → Y) : X → Z := by
  intro x -- "given an element x of X"
  apply g -- "to create an element of Z, by g it suffices to supply an element of Y"
  apply f -- "to create an element of Y, by f it suffices to supply an element of X"
  exact x -- "here's an element of X"

example (h1 : Q → R) (h2 : P → Q) : P → R := by
  intro p -- "assume P"
  apply h1 -- "by h2, it suffices to prove Q"
  apply h2 -- "by h1, it suffices to prove P"
  exact p -- "here's a proof of P"

/-
We can shorten the proof above by using actual function composition.
-/

example (h1 : Q → R) (h2 : P → Q) : P → R := by
  intro p
  exact h1 (h2 p)

/-
In Lean, it's common to use "currying" instead of Cartesian products
or logical And (which are the same thing under the hood).
Instead of writing `f : X × Y → Z` we would write
`f : X → Y → Z`. By default, arrows associate to the right, so this
is the same as `f : X → (Y → Z)`. So `f` takes in an element of `X`
and returns a function `Y → Z`, i.e. `f x y : Z` if `x : X` and `y : Y`.

This works in logic too. Instead of writing `h : P ∧ Q → R` we
would write `h : P → Q → R`. The next example shows that we can
swap `Q` and `R`, as we would expect from the commutativity of And.
-/

example (h : P → Q → R) : Q → P → R := by
  intro q p
  exact h p q

/-
This next example shows that implication is transitive.
-/

theorem imp_trans : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR p
  apply hQR
  apply hPQ
  exact p

/-
Wait, that proof is nearly identical to a previous one!
That's because everything to the left of the colon acts
like a hypothesis, so
`(h1 : Q → R) (h2 : P → Q) : P → R`
is equivalent to
`(Q → R) → (P → Q) → P → R`
-/


/-!
Negation is also a function type: `¬ P` is notation for `P → False`.

So proving `¬ P` means giving a function that turns any hypothetical proof of
`P` into a contradiction.
-/

theorem doubleNeg : P → ¬¬ P := by
  intro p np
  exact np p

theorem contrapositive (h : P → Q) : ¬ Q → ¬ P := by
  intro nq p
  apply nq
  apply h
  exact p

/-
The expression `∀ x : X, P x` acts like a function, too.
If we have `h : ∀ x : X, P x` and some `x : X` then `h x`
outputs `P x`. The tactic `intro` also peels off `∀ x : X`
in a goal.
-/

variable {P Q : X → Prop}

theorem pointwise_implication (h1 : ∀ x : X, P x → Q x) :
    (∀ x : X, P x) → ∀ x : X, Q x := by
  intro h2 x
  apply h1 x
  exact h2 x


/-
Exercises
-/

namespace LeMa

variable {P Q R : Prop} {X : Type}

example (h : P → Q → R) : P → (P → Q) → R := by
  sorry

example : ((((P → Q) → P) → P) → Q) → Q := by
  sorry

-- For the next two exercises, give two different answers.
def projFirst : X → X → X := by
  sorry

def projSecond : X → X → X := by
  sorry

-- Prove that P ∧ ¬P implies False
example : P → ¬ P → False := by
  sorry

-- Try to prove the following and see what breaks.
-- Then modify the statement slightly and prove the result.
example (h : P → Q) (np : ¬ P) : ¬ Q → False := by
  sorry


end LeMa
