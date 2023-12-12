import Game.Metadata

World "DemoWorld"
Level 1

Title "Hello World HOlA"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides. Hola"

Statement (x y z w : ℕ) : x + y + (z + w) = (w + z) + (y + x) := by
  rw [Nat.add_comm]
  rw [Nat.add_comm z w]
  rw [Nat.add_comm x y]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
