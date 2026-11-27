import HilbertFoundations.AngleSumCloseAux3

/-!
# Helper module for the angle-sum theorem: invariance of the type of an angle

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

The type of an angle (acute, right, obtuse: `LtSupp`, `EqSupp`, `GtSupp`) is invariant under
congruence, under moving the points along the arms and under exchanging the arms. A smaller angle
than an acute one is acute, a larger one than an obtuse one is obtuse. Finally the type of `∠AOB`
is read off from the position of a copy `∠XOB` of it laid off on the other side of `OB`, relative
to the extension `OC` of the first arm.
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

/-- B4: congruent angles have the same type. -/
theorem sameType_of_angCong (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') (hc : AngCong A O B A' O' B') :
    SameType L A O B A' O' B' := by
  sorry

/-- The type of an angle does not depend on the points chosen on its arms. -/
theorem sameType_rays (h : ¬Collinear (Line := L) A O B) (hX : X ∈ ray O A)
    (hY : Y ∈ ray O B) : SameType L A O B X O Y := by
  sorry

/-- B5: exchanging the arms does not change the type of an angle. -/
theorem sameType_swap (h : ¬Collinear (Line := L) A O B) : SameType L A O B B O A := by
  sorry

/-- B6: an angle less than an acute angle is acute. -/
theorem ltSupp_of_angLt (h : AngLt (L := L) A O B A' O' B') (h' : LtSupp L A' O' B') :
    LtSupp L A O B := by
  sorry

/-- An angle greater than an obtuse angle is obtuse. -/
theorem gtSupp_of_angLt (h : AngLt (L := L) A' O' B' A O B) (h' : GtSupp L A' O' B') :
    GtSupp L A O B := by
  sorry

/-- B8 (a): if a copy `∠XOB` of `∠AOB` lies inside the supplement `∠COB`, the angle is acute. -/
theorem ltSupp_of_copy (h : ¬Collinear (Line := L) A O B) (hC : Between A O C)
    (hc : AngCong A O B X O B) (hX : X ∈ Interior (Line := L) C O B) : LtSupp L A O B := by
  sorry

/-- B8 (b): if a copy `∠XOB` of `∠AOB` has its arm on the half-ray `OC`, the angle is right. -/
theorem eqSupp_of_copy (h : ¬Collinear (Line := L) A O B) (hC : Between A O C)
    (hc : AngCong A O B X O B) (hX : X ∈ ray O C) : EqSupp L A O B := by
  sorry

/-- B8 (c): if the extension `OC` lies inside a copy `∠XOB` of `∠AOB`, the angle is obtuse. -/
theorem gtSupp_of_copy (h : ¬Collinear (Line := L) A O B) (hC : Between A O C)
    (hc : AngCong A O B X O B) (hX' : ¬Collinear (Line := L) X O B)
    (hX : C ∈ Interior (Line := L) X O B) : GtSupp L A O B := by
  sorry

end

end AngSum

end HilbertFoundations
