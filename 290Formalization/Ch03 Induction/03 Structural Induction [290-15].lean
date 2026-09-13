import Mathlib.Tactic
import Mathlib.Data.List.Basic

/-
This section introduces structural induction, which is a generalization
of induction to arbitrary inductive types. We give two examples of this
here (natural numbers and lists) but it can be used quite generally.

The main takeaway is that a proof using structural induction usually
ends up looking almost indistinguishable from a recursively defined function.
Use `match` to pattern match on the constructors of the inductive type
(for natural numbers, these are `zero` and `succ`, but you can more generally
pattern match on more cases if that's convenient.)
-/

/-
The Chicken Nugget Problem
The classic chicken nugget problem asks how many chicken nuggets one can
buy if nuggets come in 6-piece, 9-piece, and 20-piece. Here we do the
easier problem with 5 and 7, and the 6, 9, 20 case is an exercise.
-/

theorem nugget_5_7_exists (n : ℕ) (h : n ≥ 24) : ∃ x y : ℕ, n = 5*x + 7*y := by
  match n with
  | 24 => use 2, 2
  | 25 => use 5, 0
  | 26 => use 1, 3
  | 27 => use 4, 1
  | 28 => use 0, 4
  | n + 29 =>
    obtain ⟨x, y, hxy⟩ := nugget_5_7_exists (n + 24) (by linarith) -- IH looks like a recursive call
    use (x+1), y
    grind

/-
The following function returns an ordered pair (x,y) such that 5x+7y = n.
Observe how closely the function definition resembles the proof of the
theorem above.
-/

def nugget_5_7_construct : ℕ → ℕ × ℕ
  | 24 => ⟨2, 2⟩
  | 25 => ⟨5, 0⟩
  | 26 => ⟨1, 3⟩
  | 27 => ⟨4, 1⟩
  | 28 => ⟨0, 4⟩
  | n + 29 => by
    obtain ⟨x, y⟩ := nugget_5_7_construct (n + 24)
    exact ⟨x+1, y⟩
  | _ => ⟨0, 0⟩

#eval nugget_5_7_construct 34

/-
Prove that the output of `nugget_5_7_construct` is a valid solution
to the 5,7 chicken nugget problem.
-/

theorem nugget_5_7_construct_valid (n : ℕ) (h : n ≥ 24) :
  n = 5*(nugget_5_7_construct n).1 + 7*(nugget_5_7_construct n).2 := by
  match n with
  | 24 => simp only [nugget_5_7_construct, Nat.reduceMul, Nat.reduceAdd]
  | 25 => simp only [nugget_5_7_construct, Nat.reduceMul, Nat.reduceAdd]
  | 26 => simp only [nugget_5_7_construct, Nat.reduceMul, Nat.reduceAdd]
  | 27 => simp only [nugget_5_7_construct, Nat.reduceMul, Nat.reduceAdd]
  | 28 => simp only [nugget_5_7_construct, Nat.reduceMul, Nat.reduceAdd]
  | n + 29 =>
    obtain ih := nugget_5_7_construct_valid (n + 24) (by simp)
    simp only [nugget_5_7_construct]
    linarith

/-
System of One-Way Roads
From [290] Section 15:
Let S be a finite set of cities. We will call a collection of one-way roads,
with a single road connecting each pair of distinct cities in S, a system of
one-way roads for S. If there is some path through the cities that follows
the system of one-way roads and visits each city exactly once, we will call
it a valid path through the cities.

The following structure defines a system of one-way roads. The example
below it matches the 5-city example in [290].
-/


structure Roads (cities : Type) where
  R : cities → cities → ℤ
  conn : ∀ x y, x = y ↔ R x y = 0
  one_way : ∀ x y, R x y = - R y x

inductive FiveCities
| A | B | C | D | E
deriving DecidableEq, Fintype, Repr

open FiveCities

def FiveCitiesRoads : Roads FiveCities where
  R := fun m n =>
  if m = n then 0 else
  match m, n with
    | A, C => 1
    | B, A => 1
    | B, D => 1
    | B, E => 1
    | C, B => 1
    | C, E => 1
    | D, A => 1
    | D, C => 1
    | E, A => 1
    | E, D => 1
    | _, _ => -1
  conn := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp
  one_way := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp

open List

/-
The following structure encodes the definition of a valid path.
Given a list of cities L, a valid path is a permutation of L
such that the i-th element of L is connected to the (i+1)-th
element of L for each i.
-/

structure ValidPath {cities : Type} (S : Roads cities)
  (L : List cities) (hL : Nodup L) (path : List cities) :
  Prop where
  cover : L ~ path -- this means L is a permuatation of path
  valid : path.IsChain (fun x y => S.R x y > 0)

-- Verify that the path [B, A, C, E, D] is valid
def FiveCitiesPath : ValidPath FiveCitiesRoads [A, B, C, D, E]
  (by decide) [B, A, C, E, D] where
  cover := by decide
  valid := by decide

-- Prove that there always exists a valid path
theorem ExistsValidPath {cities : Type} (S : Roads cities)
  (L : List cities) (hL : Nodup L) :
  ∃ path : List cities, ValidPath S L hL path := by
    match L with
    | [] =>
      use []
      exact ⟨ Perm.refl [], by simp only [gt_iff_lt, IsChain.nil] ⟩
    | X :: other =>
      set p := other.partition (fun Y => S.R Y X > 0) with hp
      have p_nodup : (p.1).Nodup ∧ (p.2).Nodup := by
        rw [hp, partition_eq_filter_filter]
        constructor <;> apply Nodup.filter <;> exact hL.tail
      obtain ⟨p1, p1_valid⟩ := ExistsValidPath S p.1 p_nodup.1
      obtain ⟨p2, p2_valid⟩ := ExistsValidPath S p.2 p_nodup.2
      have other_p1_p2 : other ~ p1 ++ p2 := by
        calc
          other ~ p.1 ++ p.2 := by
              rw [hp]
              rw [partition_eq_filter_filter]
              exact (filter_append_perm _ other).symm
            _ ~ p.1 ++ p2 := by rw [perm_append_left_iff]; exact p2_valid.1
            _ ~ p1 ++ p2 := by rw [perm_append_right_iff]; exact p1_valid.1
      use p1 ++ X :: p2
      exact ⟨
        by calc
        X :: other ~ X :: (p1 ++ p2) := by rw [perm_cons]; exact other_p1_p2
          _ ~ p1 ++ X :: p2 := perm_middle.symm
        ,
        by
        apply IsChain.append
        · exact p1_valid.2
        · apply IsChain.cons
          · exact p2_valid.2
          · by_cases h : p2 = []
            · simp only [h, head?_nil, Option.mem_def, reduceCtorEq, gt_iff_lt, IsEmpty.forall_iff,
              implies_true]
            · intro y yin
              apply mem_of_mem_head? at yin
              rw [← (p2_valid.1).mem_iff, hp] at yin
              simp only [gt_iff_lt, partition_eq_filter_filter, mem_filter, Function.comp_apply,
                Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt] at yin
              simp only [gt_iff_lt, lt_iff_le_and_ne, ne_eq]
              constructor
              · rw [S.one_way]
                simp only [Int.neg_nonneg, yin.2]
              · intro eq
                symm at eq
                rw [← S.conn] at eq
                apply (nodup_cons.mp hL).1
                rw [eq]
                exact yin.1
        · by_cases h : p1 = []
          · simp only [h, getLast?_nil, Option.mem_def, reduceCtorEq, head?_cons,
              Option.some.injEq, gt_iff_lt, forall_eq', IsEmpty.forall_iff, implies_true]
          · intro x xin
            simp only [head?_cons, Option.mem_def, Option.some.injEq, gt_iff_lt, forall_eq']
            apply mem_of_mem_getLast? at xin
            rw [← (p1_valid.1).mem_iff, hp] at xin
            simp only [gt_iff_lt, partition_eq_filter_filter, mem_filter, decide_eq_true_eq] at xin
            exact xin.2
      ⟩
termination_by L.length
decreasing_by
  all_goals simp_wf; simp [List.length_filter_le]

-- Construct the valid path
def CityPath {cities : Type} (S : Roads cities) : List cities → List cities
  | [] => []
  | X :: other =>
    CityPath S (other.partition (fun Y => S.R Y X > 0)).1 -- Y -> X cities
    ++ X ::
    CityPath S (other.partition (fun Y => S.R Y X > 0)).2 -- X -> Y cities
termination_by xs => xs.length
decreasing_by
  all_goals simp_wf; simp only [List.length_filter_le]

#eval CityPath FiveCitiesRoads [A, B, C, D, E] -- B -> E -> D -> A -> C

-- BONUS : Prove that CityPath outputs a valid path. (This is hard.)

theorem CityPath_valid {cities : Type}
  (S : Roads cities) (L : List cities) (hL : L.Nodup) :
  ValidPath S L hL (CityPath S L) where
    cover := sorry
    valid := sorry





--Exercise 15.3
theorem nugget_3_8_exists (n : ℕ) (hn : n ≥ 14) : ∃ x y : ℤ, n = 3 * x + 8 * y := sorry

--Exercise 15.4
theorem exists_pow_two_mul_odd (n : ℕ) : ∃ e m : ℕ, Odd m ∧ n = 2 ^ e * m := sorry

-- Exercise 15.5
theorem nugget_6_9_20_exists (n : ℕ) (hn : n ≥ 14) :
    ∃ x y z : ℤ, n = 6 * x + 9 * y + 20 * z := sorry

-- Exercise 15.7
theorem exists_sum_fib (n : ℕ) : ∃ s : Finset ℕ, n = ∑ i ∈ s, Nat.fib i := sorry

#check Quotient
