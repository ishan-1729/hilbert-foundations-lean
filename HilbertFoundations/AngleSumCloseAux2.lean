import HilbertFoundations.AngleSumCloseAux1

/-!
# Helper module for the angle-sum theorem: the order of angles

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

The relation `AngLt` of `Congruence.lean` ("`∠AOB` is congruent to a part of `∠A'O'B'` adjacent
to the first arm") is shown to be a strict order on angles up to congruence: it is compatible with
congruence and with the choice of points on the arms, irreflexive, transitive, asymmetric, and any
two angles are comparable (trichotomy). Passing to supplements reverses it.
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

/-- A1: an angle congruent to `∠A'O'X`, with `X` inside `∠A'O'B'`, is less than `∠A'O'B'`. -/
theorem angLt_of_interior (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') (hX : X ∈ Interior (Line := L) A' O' B')
    (hc : AngCong A O B A' O' X) : AngLt (L := L) A O B A' O' B' := by
  sorry

/-- A2: if `∠AOB < ∠A'O'B'`, a copy of `∠AOB` on the arm `O'A'` lies inside `∠A'O'B'`. -/
theorem angLt_interior (h : AngLt (L := L) A O B A' O' B') :
    ∃ X, X ∈ Interior (Line := L) A' O' B' ∧ AngCong A O B A' O' X := by
  sorry

/-- A3: `AngLt` is compatible with congruence of the smaller angle. -/
theorem angLt_congr_left (h : AngLt (L := L) A O B A' O' B')
    (h₁ : ¬Collinear (Line := L) A₁ O₁ B₁) (hc : AngCong A O B A₁ O₁ B₁) :
    AngLt (L := L) A₁ O₁ B₁ A' O' B' := by
  sorry

/-- A4: `AngLt` is compatible with congruence of the larger angle. -/
theorem angLt_congr_right (h : AngLt (L := L) A O B A' O' B')
    (h₁ : ¬Collinear (Line := L) A₁ O₁ B₁) (hc : AngCong A' O' B' A₁ O₁ B₁) :
    AngLt (L := L) A O B A₁ O₁ B₁ := by
  sorry

/-- The arms of the smaller angle can be exchanged. -/
theorem angLt_swap_left (h : AngLt (L := L) A O B A' O' B') : AngLt (L := L) B O A A' O' B' := by
  sorry

/-- The arms of the larger angle can be exchanged. -/
theorem angLt_swap_right (h : AngLt (L := L) A O B A' O' B') :
    AngLt (L := L) A O B B' O' A' := by
  sorry

/-- The points on the arms of the smaller angle can be moved along their half-rays. -/
theorem angLt_rays_left (h : AngLt (L := L) A O B A' O' B') (hX : X ∈ ray O A)
    (hY : Y ∈ ray O B) : AngLt (L := L) X O Y A' O' B' := by
  sorry

/-- The points on the arms of the larger angle can be moved along their half-rays. -/
theorem angLt_rays_right (h : AngLt (L := L) A O B A' O' B') (hX : X ∈ ray O' A')
    (hY : Y ∈ ray O' B') : AngLt (L := L) A O B X O' Y := by
  sorry

/-- A5: no angle is less than itself. -/
theorem angLt_irrefl : ¬AngLt (L := L) A O B A O B := by
  sorry

/-- A6: `AngLt` is transitive. -/
theorem angLt_trans {A₂ O₂ B₂ : P} (h1 : AngLt (L := L) A O B A' O' B')
    (h2 : AngLt (L := L) A' O' B' A₂ O₂ B₂) : AngLt (L := L) A O B A₂ O₂ B₂ := by
  sorry

/-- A7: `AngLt` is asymmetric. -/
theorem angLt_asymm (h1 : AngLt (L := L) A O B A' O' B')
    (h2 : AngLt (L := L) A' O' B' A O B) : False := by
  sorry

/-- An angle less than another is not congruent to it. -/
theorem angLt_not_angCong (h1 : AngLt (L := L) A O B A' O' B')
    (h2 : AngCong A O B A' O' B') : False := by
  sorry

/-- A8: trichotomy: of two angles, one is less than the other or they are congruent. -/
theorem angLt_trichotomy (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') :
    AngLt (L := L) A O B A' O' B' ∨ AngCong A O B A' O' B' ∨ AngLt (L := L) A' O' B' A O B := by
  sorry

/-- A9: passing to the supplements (extending the first arms) reverses `AngLt`. -/
theorem angLt_supp (h : AngLt (L := L) A O B A' O' B') (hC : Between A O C)
    (hC' : Between A' O' C') : AngLt (L := L) C' O' B' C O B := by
  sorry

end

end AngSum

end HilbertFoundations
