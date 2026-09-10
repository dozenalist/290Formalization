import Mathlib.Data.Nat.Basic

namespace LeMa

/-!
# "The person who's going to have the best ideas is the person who is knee-deep in execution."
# - Brennan Lee Mulligan
-/

section Intro

/-!
# 1. Intro to Programming in Lean
-/

/-!
# Lean as a Programming Language

Lean has a become a somewhat infamous tool in the mathematics community in recent history. As
such, there are many ideas of what Lean is that float around in conversation, most of which
capturing only part of what Lean is and what Lean can do. So, what exactly is Lean?

Lean is a dependently typed, functional programming language. This means that the fundamental
structure of Lean is functions, exactly in the same way that sets are the fundamental structure
of set theory.

Dependent typing is a very strict condition for type systems in the context of programming
languages. Essentially, it means that every datum must be an instance of a type (static typing)
and an instance cannot be cast to an instance of a different type (strong typing). In contrast,
Python is weakly typed and dynamically typed, which is largely why it is quick to write Python
code and slow to run Python code. It should be noted that, while type casting is disallowed,
type coercion is allowed; this is one of the reasons why dependent typing is more than just
static typing and strong typing together.
-/

/-!
# Constructing the Naturals

Since every datum, which we call a term, must be an instance of a type, we ought to start by
defining a type. A type in Lean is defined as the aggregate of its constructors. To see this in
action, let's consider how should define the natural numbers (beginning with zero) as a type in
Lean.
-/

inductive CopyNat : Type
| zero : CopyNat
| succ : CopyNat → CopyNat

/-!
This code introduces a new type called `CopyNat`, which is defined by two constructors.
First, the number called `zero` is an instance of `CopyNat`. Second, any "successor"
(denoted by the function `succ`) of a `CopyNat` is a `CopyNat`. These constructors are
representative of the following two axioms defining the naturals.

* Zero exists and is a natural number.
* If you have a natural number then the successor produces a new natural number.

Here we defined our natural numbers using `CopyNat` instead of `Nat` as `Nat` is already
defined in MathLib. Further, we have defined our model of the natural numbers in the same way
as MathLib. We have purposefully done this such that this text will have access to the many
tools and structures available in it. For example, MathLib provides `ℕ` as an alias for `Nat`
for ease of use. Additionally, it provides the standard decimal numerals as aliases for
instances of `ℕ`. For example, we can write `4` instead of `succ (succ (succ (succ zero)))`.
For this benefit, we will continue to build from MathLib for the remainder of the text.

A more detailed explanation of these modeling decisions for `ℕ` is presented in the next
section.
-/

-- Put your cursor at the end of this line to "run" the `#eval` command. The output is in the
-- sidebar on the right.
#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

/-!
# Defining the Fibonacci Function

Now, let's consider how we might define a simple function: the Fibonacci sequence function. We
aim to create a function that takes as input `(n : ℕ)` and returns the nth output of the
Fibonacci sequence.

First, let's recall how we do this informally, using the name `fib`. Given a term of type
`ℕ`, we do the following:

* If our term matches the form `zero` (or `0`), we produce `0`.
* Otherwise, if our term matches the form `succ zero` (or `1`) then we produce `1`.
* Otherwise, if our term matches the form `succ (succ n)` (or `n + 2`) for some `n : ℕ` then we
  produce `fib (succ n) + fib n` (or `fib (n + 1) + fib n`).
-/

def fib : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

-- Again, put your cursor at the end of each line to see the output.
#eval fib 0

#eval fib 1

#eval fib 3

#eval fib 6

#eval fib 25

/-!
# Defining Addition on ℕ

Notice that we used `+` in our definition of `fib`. We can do this because it is already
defined in MathLib. In this text, we will sometimes leave this kind of explanation here
instead of rebuilding everything from scratch. In this instance, we will leave the full
explanation to the next section.

Briefly, `add` is a recursively defined function from `ℕ × ℕ` to `ℕ`. So why do we write
`ℕ → ℕ → ℕ`? This is called "currying" (more on that in a later section). We think of `add`
as a function that takes in a natural number `n` and outputs a function `addₙ : ℕ → ℕ`,
the "add n" function.
-/

def add : ℕ → ℕ → ℕ
| n, 0 => n
| n, m + 1 => add (n + 1) m

#eval add 7 1

#eval add 4 0

#eval add 3 3

/-!
Notice that, in both pattern matching cases, `n` fits the same pattern of an arbitrary
instance of `ℕ`, not associated with a specific constructor. As such, we can also define
addition on `ℕ` with the following alternative.
-/

def add' (n : ℕ) : ℕ → ℕ
| 0 => n
| m + 1 => add' (n + 1) m

#eval add' 7 1

#eval add' 4 0

#eval add' 3 3

/-!
# Defining Multiplication on ℕ (Exercise)
-/
-- The `sorry` term is a temporary placeholder for a missing proof or value.
-- When you're ready to work on this exercise, delete `:= sorry` and
-- write your code on the next line, following the patterns above.
def mul : ℕ → ℕ → ℕ := sorry

-- Uncomment the following lines to check your definition
--#eval mul 3 4

--#eval mul 2 8

--#eval mul 0 7

/-!
# Constructing Lists of Naturals

Now, let's build a type for lists of naturals using `ℕ`.
-/

inductive NatList : Type
| nil : NatList
| cons : ℕ → NatList → NatList

/-!
Just like our definition of `ℕ`, this registers the name `NatList` as an instance of `Type`
produced by the listed constructors. The first constructor is registered with the binder `nil`
as an instance of `NatList` and the second constructor is registered with the binder `cons` as
an instance of `ℕ → NatList → NatList`. These constructors are representative of the following
two axioms defining the list structure (on natural numbers).

* The empty list exists and is a list.
* If you have a natural number `a` and a list of natural numbers `L` then you can produce a new
list by prepending `a` to the front of `L`, often written `[a] ++ L`.
-/

open NatList

/-!
# Defining the Sum Function
-/

-- Given a list of natural numbers, output the sum of the elements of the list.
def sum : NatList → ℕ
| nil => 0
| cons n ns => n + sum ns

/-!
# Defining the Append Function
-/

-- Given two NatLists `L` and `M`, output `L ++ M`
def append : NatList → NatList → NatList
| nil, bs => bs
| cons a as, bs => cons a (append as bs)

/-!
# Defining the Count Function
-/

-- Given a natural number `n` and a list `L`, count how many times `n` appears in `L`
def count : ℕ → NatList → ℕ
| _, nil => 0
| a, cons b bs => (if a = b then 1 else 0) + (count a bs)

/-!
# Defining the Product Function (Exercise)
-/

-- Return the product of the natural numbers in a list
def NatList.prod : NatList → ℕ := sorry

/-!
# Defining the Length Function (Exercise)
-/

-- Return the length of a list
def NatList.length : NatList → ℕ := sorry

/-!
# Defining the Reverse Function (Exercise)
-/

-- Reverse the order of a list
def NatList.rev : NatList → NatList := sorry

end Intro

end LeMa
