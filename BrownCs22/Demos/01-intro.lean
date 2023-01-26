import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Aesop
import Mathlib.Data.Set.Basic

/-

Lean is a language that we will be using in CS22 this year.

If you're in this class, you've most likely used a programming language before.
Lean is a programming language too. But we'll be using it for a different reason:
Lean lets us state *propositions*, write *proofs* of these propositions, and *check*
automatically that these proofs are correct.

Some basic Lean syntax:

* Block comments, like this one, are written as /- ... -/.
* Line comments begin with -- 
* If a file imports other files, this appears at the very top of the file.
  You shouldn't change these imports!

**Definition**. A *proposition* is a statement with a truth value.
That is, it is a statement that could be either true or false.

"Lean is a language" is a proposition. "Lean is not a language" is a proposition.
"1 + 1 = 2" is a proposition, as is "1 + 1 = 3".
But "Lean" is not a proposition, nor is "1 + 1", nor is "is Lean a language?".

-/

#check Prop 
#check ℤ

/-

Lean uses the shorthand `Prop` for proposition.
The `#check` command asks Lean to tell us "what kind of thing" something is.
(This will be very useful for us!)
Lean tells us that `Prop` is a Type, that is, a "kind of thing" -- not very enlightening!

But what if we try some of our examples from above?

-/

#check 1 + 1 = 2
#check 1 + 1 = 3

#check True 
#check False 


/-

In normal math, it's common for us to write things like 
"let p, q, and r be propositions" or "let x and y be integers".

In Lean, we write:

-/

variable (p q r : Prop)

#check p 
#check p ∧ q 
#check p ∧ q → r 
#check p ∨ q ∨ p ∧ r ∧ ¬ (p ∧ q ∧ r) 

/-

A few things to note here.

* In the third `#check` above, if you hover over the output in the infoview,
  you can see how this formula is parenthesized!
* Those unicode symbols are input using \ . To write the third line I typed
  `p \and q \to r`. But there are lots of variants. 
  They usually match the LaTeX command.

  * `∧`: and, wedge
  * `∨`: or, vee 
  * `¬`: not, neg
  * `→`: to, imp, rightarrow 
  * `↔`: iff
  * `ℕ`: N, nat 
  * `ℤ`: Z, int
  * `∀`: all, forall
  * `∃`: ex, exist
  * `∣` (divides): | (note, you need to type `\|`, this isn't the normal pipe character)


You may have guessed from the list, Lean lets us write first-order propositions
(i.e. with quantifiers). The syntax here looks like:

-/

#check ∀ x : ℕ, ∃ y : ℕ, x < y ∧ 1 = 1
#check ∀ x : ℕ, ∃ y : ℕ, Prime x ∧ x ∣ y


/-

Try it out yourself: write some propositions.
If you want to use things like `Prime`, you can try to guess with
auto-complete: write `#check Pr` and hit ctrl-space.

-/

#check Prime

def f (x : ℕ) : ℕ := x + 2


/-

The real magic of Lean is that we can *prove* these propositions.
For today we'll stick mostly to basic logic.

There is an array of *tactics* which represent individual proof steps.
To write a proof, we state a theorem, and then write a sequence of tactics.
The tactics manipulate the *proof state* by changing our *hypotheses* and *goals*.

-/

theorem my_first_theorem : p ∧ q → q ∧ p := by 
  intro hpq               -- Assume we know `p ∧ q`.
  cases' hpq with hp hq   -- This means that we know `p` and we know `q`.
  apply And.intro         -- In order to prove `q ∧ p`, we must prove `q` and then prove `p`.
  . exact hq              -- We can prove `q`, since we know `q`!
  . exact hp              -- And we can prove `p`, since we know `p`.

theorem false_context : 1 = 2 → 1 = 2 := by
  intro h12 
  exact h12

/-
Some notes here:

* `intro`, `cases'`, `apply`, `exact` are *tactics*.
* At each line in the proof we have 1 or more *goals*.
* In each goal, there are 0 or more *hypotheses*.
* The distinction here: hypotheses are what we know, 
  and the goal is what we are trying to show.
* Some tactics take arguments. These can be fresh names (`intro hpq`),
  or names of hypotheses (`exact hq`), or names of rules (`apply And.intro`).
* When we applied a tactic that left us with multiple goals,
  I tried to solve each one individually, indenting with `.` 

Here are some useful tactics:

* `intro`: when our goal is of the form `_ → _`,
  `intro h` will move the left hand side into a hypothesis,
  like saying "Assume _".
  When our goal is `∀ _, _`, `intro x` will create a new variable named `x`.

* `cases'`: note the '. If `h` is a hypothesis proving an `and`,
  `cases' h` will split it into its components.
  If `h` is a hypothesis proving an `or`, `cases' h` will set up a
  proof by cases with two goals.
  If `h` is a hypothesis proving an `exists`, `cases' h` will find a witness.
  Use the syntax `with` to name the new hypotheses. 
  In general, `cases'` is something we do to *hypotheses* only,
  to "extract" information from them.

* `apply`: uses a rule from the library, or from your context.
  If a rule `r` says "to prove `b`, it suffices to prove `a`"
  and your goal is to prove `b`, then
  `apply r` will change your goal to proving `a`.

* `exact`: when a hypothesis `h` matches the goal exactly, 
  `exact h` finishes that part of the proof.

* `use`: when the goal is `∃ x, P(x)`,
  `use z` will change the goal to `P(z)`. 
  Essentially, this is providing a *witness* to prove the existential.

* `contradiction`: if we have hypotheses `p` and `¬ p`, we can prove anything!

* `linarith`: does "easy" arithmetic to prove inequalities and equalities.

Try out a few examples. Some useful rules from the library:

-/

#check Or.inl -- to prove `a ∨ b`, it suffices to prove `a`.
#check Or.inr -- to prove `a ∨ b`, it suffices to prove `b`.

theorem flip_ors : p ∨ q → q ∨ p := by
  sorry

theorem from_above : ∀ x : ℕ, ∃ y : ℕ, x < y := by 
  sorry

theorem other_order : ∃ x : ℕ, ∀ y : ℕ, x ≤ y := by 
  sorry

theorem two_imp 
  (h1 : p → q) (h2 : q → ¬ r) : r → ¬ p := by
  sorry
  

/- together: -/

theorem quantifier_switch (P : ℕ → Prop) : 
  (¬ ∃ x, P x) → (∀ x, ¬ P x) := by
  sorry


/- Some other cool things we can do: induction!

Note: `n ∣ m` is defined to be `∃ k, n * k = m`. -/



lemma div_by_5 : ∀ n : ℕ, 5 ∣ 11^n - 6 := by
  intro n 
  induction' n with k ih 
  . simp 
  . cases' ih with w hw
    have : 11 ^ k = 5*w + 6 
    . sorry
    simp [Nat.pow_succ, this, add_mul]
    use w*11
    ring


section 
variable (P : ℕ → Prop)

example : ∀ n : ℕ, P n := by 
  intro n 
  induction' n with k ih

example : ∀ n : ℕ, P n := by 
  intro n 
  induction' n using Nat.strong_induction_on with k ih 

example : ∀ n : ℕ, P n := by 
  intro n 
  induction' n using Nat.two_step_induction with k ih1 ih2 
  


end 

/- sets! -/

theorem sets_eq (s t u : Set ℕ) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := by 
  ext x
  constructor

#check ℕ 