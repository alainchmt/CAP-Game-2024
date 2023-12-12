import Game.Metadata
import Game.Levels.Intermediate.L04_Four


World "Intermediate"
Level 5

Statement {G : Type*} [Group G] {x y z : G} :
 [[x ; y⁻¹]; z] ^ y * [[y; z⁻¹]; x] ^ z * [[z; x⁻¹]; y] ^ x = 1 := by
  simp only [commutator_def, inv_inv, mul_assoc, mul_inv_rev, conjugate_def, inv_mul_cancel_left,
    mul_inv_cancel_left, mul_left_inv]

LemmaDoc mul_assoc as "mul_assoc" in "Group Theory"
  "The group operation is associative."

NewLemma mul_assoc
