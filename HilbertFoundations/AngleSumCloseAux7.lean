import HilbertFoundations.AngleSumCloseAux6

/-!
# Helper module for the angle-sum theorem: comparison in a quadrilateral with two right angles

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

In a quadrilateral `ABDC` with right angles at `A` and `B` (`BiRight`), the summit angle on the
side of the shorter perpendicular is the greater one: if `AC < BD` then `∠BDC < ∠ACD`, and
symmetrically. The proof cuts off a Saccheri quadrilateral and uses the exterior angle theorem.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}
include hC hl

/-- D6(a): in a quadrilateral with two right angles at `A`, `B`, if `AC < BD` then the summit
angle at `D` is less than the summit angle at `C`. -/
theorem biRight_lt (h : BiRight L A B C D) (hlt : SLt A C B D) :
    AngLt (L := L) B D C A C D := by
  sorry

/-- D6(b): in a quadrilateral with two right angles at `A`, `B`, if `BD < AC` then the summit
angle at `C` is less than the summit angle at `D`. -/
theorem biRight_gt (h : BiRight L A B C D) (hlt : SLt B D A C) :
    AngLt (L := L) A C D B D C := by
  sorry

end

end AngSum

end HilbertFoundations
