import Game.Metadata

World "Intro"
Level 3

Title ""


Introduction "
So far we've worked with numbers in Lean and seen how we can substitute equalities
of natural numbers using `rewrite`.
In Lean we don't just work with objects like numbers, but we can also manipulate and prove things
that are far more abstract, and deal with propositions themselves as objects we want to prove things about.

In Lean these are called *propositions* and denoted `P : Prop`, exactly the same as how we had `n : ℕ`
before.
A proposition itself is a statement we might be trying to prove or disprove, but we can use the
same tool we used so far, rewriting, to manipulate them.
When dealing with concrete objects like numbers, we substitute equal numbers when proving.
For propositions we can subsitute equivalent propositions, where propositions are equivalent
if they are related by an 'if and only if'. For instance one simple fact is that

``` lemma or_comm : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P ```

So if we wanted to show `⊢ x = 2 ∨ y = 1` we could `rewrite [or_comm]` to change the goal to
`⊢ y = 1 ∨ x = 2`, which might then match one of our hypotheses better.

Check out the right sidebar for some new lemmas that you can use to prove the statement below.
One subtlety, note the curly (instead of round) brackets used in `{P : Prop}` in the `not_not` lemma statement.
This signals that `P` is a so-called implicit argument to `not_not`, meaning that syntax like `rewrite [not_not P]` is not correct,
and instead `rewrite [not_not]` should be used (where the argument `P` is then infered automatically).

"

Statement (P Q R : Prop) (hPQ : P ↔ Q) (hQR : Q ↔ ¬R) :
  (¬P ↔ (Q ↔ P)) ↔ R := by
  rw [hPQ]
  rw [iff_self]
  rw [iff_true]
  rw [hQR]
  rw [not_not]

LemmaDoc iff_self as "iff_self" in "Logic"
  "Says that `(P ↔ P) ↔ True`. Here the symbol `=`
  means the same as `↔`. "
LemmaDoc iff_true as "iff_true" in "Logic"
  "Says that `(P ↔ True) ↔ P`. Here the symbol `=`
  means the same as `↔`. "
LemmaDoc Classical.not_not as "not_not" in "Logic"
  "The Double Negation Theorem."

NewLemma iff_self iff_true Classical.not_not
