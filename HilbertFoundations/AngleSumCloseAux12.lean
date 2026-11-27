import HilbertFoundations.AngleSumCloseAux11

/-!
# Helper module for the angle-sum theorem: the configuration at `C`, part 1

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

For a triangle `ABC` with midline configuration `MidConf L A B C D E F G H e`, put
`B₁ := ρ B`, `A₁ := ρ' A` (half-turns about `D`, `E`), choose `X` beyond `C` on `AC` and `Y`
beyond `C` on `B₁C`. The structure `TriConf` collects the properties of this configuration
(Lemma G3); this module proves its first five items: `∠CAB ≡ ∠XCY`, the position of `Y` with
respect to the lines `AC` and `CB`, `∠CBA ≡ ∠BCA₁`, and the position of `A₁` with respect to `CB`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
/-- The configuration of Lemma G3 attached to a triangle `ABC`: the angle `∠A` laid off at `C`
as `∠XCY`, the angle `∠B` laid off at `C` as `∠BCA₁`, and the Saccheri quadrilateral `F G A B`
whose summit angle reappears at `C` as `∠HCB₁ ≡ ∠HCA₁`. -/
structure TriConf (A B C F G H X Y A₁ B₁ : P) : Prop where
  nc : ¬Collinear (Line := L) A B C
  sac : Saccheri L F G A B
  hX : Between A C X
  hY : Between B₁ C Y
  angA : AngCong C A B X C Y
  sideY : ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B
  intY : Y ∈ Interior (Line := L) X C B
  angB : AngCong C B A B C A₁
  ncA : ¬Collinear (Line := L) A₁ C B
  sideA : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y
  angS : AngCong F A B H C B₁
  ncH : ¬Collinear (Line := L) B₁ C H
  ncH' : ¬Collinear (Line := L) A₁ C H
  angH : AngCong B₁ C H A₁ C H
  sideH : ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y
  sideYH : ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B

end

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L} {e : L}
include hC hl

/-- G3, setup: the image `B₁` of `B` under the half-turn about `D` differs from `C`, lies beyond
`D` on `BD`, and lies off the midline `e`. -/
theorem tri_B₁_ne (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) : B₁ ≠ C ∧ Between B D B₁ ∧ B₁ ∉ e := by
  sorry

/-- G3.1: the angle `∠CAB` is congruent to `∠XCY`. -/
theorem tri_angA (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X) (hY : Between B₁ C Y) :
    AngCong C A B X C Y := by
  sorry

/-- G3.2: `Y` and `B` are on the same side of the line `AC`. -/
theorem tri_sideY (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B := by
  sorry

/-- G3.3: `Y` is interior to the exterior angle `∠XCB`. -/
theorem tri_intY (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X) (hY : Between B₁ C Y) :
    Y ∈ Interior (Line := L) X C B := by
  sorry

/-- G3.4: the angle `∠CBA` is congruent to `∠BCA₁`, and `A₁, C, B` are not collinear. -/
theorem tri_angB (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) :
    AngCong C B A B C A₁ ∧ ¬Collinear (Line := L) A₁ C B := by
  sorry

/-- G3.5: `A₁` and `Y` are on the same side of the line `CB`. -/
theorem tri_sideA (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X)
    (hY : Between B₁ C Y) : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y := by
  sorry

end

end AngSum

end HilbertFoundations
