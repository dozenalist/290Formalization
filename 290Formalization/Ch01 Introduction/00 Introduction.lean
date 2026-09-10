/-

The theme of this project is "Anyone can cook", the title of Chef Gusteau's
book from the Pixar film Ratatouille, and its purpose is similar.
It is meant to be a gentle introduction to Lean for curious mathematicians,
without focusing on the details of type theory or the Lean language.

This book is intended to be a companion to the BYU Math 290 textbook
"A Transition to Advanced Mathematics" by Doud and Nielsen
(hereafter referred to as [290]).
We will follow that textbook very closely and assume that the reader
is already familiar with the material in it.

We have made some design decisions that necessitate a few departures
from [290], namely:
* We have skipped the first five sections of [290], which give a brief
introduction to logic and set theory. The main purpose of this book is to
teach readers how to write proofs in Lean. That means that we will
provide a very brief crash course in type theory (the foundation of Lean)
and assume that the reader is already familiar with logic.
* We have moved Sections 10 and 12 of [290] (on proofs in set theory)
to later in the project; working with sets in type theory can sometimes
be frustrating.
* We have ignored examples and exercises that require geometric intuition,
e.g. the problem in Section 15 about cutting a square into smaller squares.

-/
