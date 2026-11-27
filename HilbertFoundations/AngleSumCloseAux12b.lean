import HilbertFoundations.AngleSumCloseAux12

/-!
# Helper module for the angle-sum theorem: the configuration at `C`, part 2

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

The remaining items of Lemma G3: the half-turns carry the summit angles `∠FAB`, `∠GBA` of the
Saccheri quadrilateral `F G A B` to `∠HCB₁`, `∠HCA₁`, which are therefore congruent; `A₁` and `Y`
lie on the same side of the line `CH`, and `H`, `B` on the same side of the line `CY`. Assembled
with the items of part 1, every triangle carries a configuration `TriConf` (`exists_triConf`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L} {e : L}
include hC hl

/-- G3.6: the half-turns carry `∠FAB` to `∠HCB₁` and `∠GBA` to `∠HCA₁`; both image angles are
genuine. -/
theorem tri_angS (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) :
    AngCong F A B H C B₁ ∧ ¬Collinear (Line := L) B₁ C H ∧
      AngCong G B A H C A₁ ∧ ¬Collinear (Line := L) A₁ C H := by
  sorry

/-- G3.7: the angles `∠B₁CH` and `∠A₁CH` are congruent. -/
theorem tri_angH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) :
    AngCong B₁ C H A₁ C H := by
  sorry

/-- G3.8: `A₁` and `Y` are on the same side of the line `CH`. -/
theorem tri_sideH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y := by
  sorry

/-- G3.9: `H` and `B` are on the same side of the line `CY`. -/
theorem tri_sideYH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B := by
  sorry

/-- G3: every triangle `ABC` carries a configuration `TriConf` at its vertex `C`. -/
theorem exists_triConf (h : ¬Collinear (Line := L) A B C) :
    ∃ F G H X Y A₁ B₁ : P, TriConf L A B C F G H X Y A₁ B₁ := by
  sorry

end

end AngSum

end HilbertFoundations
