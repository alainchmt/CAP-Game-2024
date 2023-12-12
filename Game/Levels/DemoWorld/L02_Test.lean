import Game.Metadata

World "DemoWorld"
Level 2

Title "Introduction"

namespace boop
lemma add_comm : ∀ (x : ℕ) (y : ℕ), x + y = y + x := Nat.add_comm


Introduction "
Let's now discuss the language Lean uses to represent statements.

## The language

A lemma in Lean is written using a specific syntax, that is designed to look similar to written
mathematics, but is more restricted in how statements can be constructed.
Here is an example of a lemma statement in Lean:

``` lemma add_comm : ∀ (x : ℕ) (y : ℕ), x + y = y + x ```

This lemma states that for all natural numbers `x` and `y` that addition of `x` and `y` commutes,
hopefully you agree that this is a straightforward, but very useful fact!
Note the first word `lemma` is a keyword (highlighted in blue) and means we are stating a new
lemma.
The second word is simply a name we give to the lemma so we can refer to it later, naming lemmas
works much better than numbering lemmas when you need to refer back to many things.
This is especially helpful if you give the lemmas sensible names, so that you can remember them
later, and so that when you use them you can tell what the lemma does from its name.
In this case `add_comm` says that addition is commutative, so it seems like a pretty good choice.

The symbol `:` is used to say that `x` and `y` are natural numbers, this is similar to how we
normally write `x ∈ ℕ`, and you should think of `:` as meaning `∈`.
The symbol `:` is also used after the name of the lemma, and it has the same meaning!
Here within the lemma `x : ℕ` gives a name to a natural number and
`add_comm : ∀ x y, x + y = y + x` gives a name to the statement that addition is commutative.

The lemma `add_comm` is a 'for all' statement, so in order to get the statement that addition
commutes for a _specific_ pair of natural numbers rather than variables `x` and `y`,
we place the naturals we want to refer to after the name,
for instance `add_comm 2 3` means `2 + 3 = 3 + 2`.
Here we used 2 and 3, but we could apply this lemma with variables too by using their names
instead of 2 and 3.
 "
/- Hint (hidden := true) " Delete `sorry` and type `rewrite add_comm x y,` (don't forget the comma!).
  That is the first step of the proof, after typing the comma you should see the goal (on the right)
  change so the sides of the equation look closer to each other.
  The next two steps of the proof go on the next lines, and are similar to the first, can you work
  them out?" -/

Statement (x y z w : ℕ) : x + y + (z + w) = (w + z) + (y + x) := by
  rw [add_comm]
  rw [add_comm z w]
  rw [add_comm x y]

Conclusion "This last message appears if the level is solved."
