import HilbertFoundations.AngleSumCloseAux10

/-!
# Helper module for the angle-sum theorem: the midline of a triangle

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

For a triangle `ABC` let `D`, `E` be the midpoints of `CA`, `CB` and `e` the line `DE`. The points
`A`, `B`, `C` lie off `e`, with `A`, `B` on the same side (`tri_midline_side`). The feet `F`, `G`,
`H` of `A`, `B`, `C` on `e` satisfy `ρ F = H`, `ρ' G = H` for the half-turns `ρ`, `ρ'` about `D`,
`E`, and `F G A B` is a Saccheri quadrilateral. The data are packaged as `MidConf`
(`tri_midline`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [PlaneCongruence P L]

variable (L) in
/-- The data of Lemmas G1, G2 for the triangle `ABC`: `D`, `E` the midpoints of `CA`, `CB`, `e` the
line `DE`, `F`, `G`, `H` the feet of `A`, `B`, `C` on `e`. -/
structure MidConf (A B C D E F G H : P) (e : L) : Prop where
  htA : Pas.ht (L := L) D A = C
  htB : Pas.ht (L := L) E B = C
  bD : Between A D C
  bE : Between B E C
  hD : D ∈ e
  hE : E ∈ e
  hA : A ∉ e
  hB : B ∉ e
  hC : C ∉ e
  sideAB : SameSide e A B
  fA : Foot e A F
  fB : Foot e B G
  fC : Foot e C H
  htF : Pas.ht (L := L) D F = H
  htG : Pas.ht (L := L) E G = H
  sac : Saccheri L F G A B

end

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}
include hC hl

/-- G1: if `D`, `E` lie strictly inside the sides `AC`, `BC` of a triangle and on a line `e`, then
`D ≠ E`, the vertices lie off `e`, and `A`, `B` are on the same side of `e`. -/
theorem tri_midline_side (h : ¬Collinear (Line := L) A B C) {e : L} (bD : Between A D C)
    (bE : Between B E C) (hD : D ∈ e) (hE : E ∈ e) :
    D ≠ E ∧ A ∉ e ∧ B ∉ e ∧ C ∉ e ∧ SameSide e A B := by
  sorry

/-- G2(a): the half-turn about a point `D` of a line `e` maps the foot of `A` on `e` to the foot
of `ρ A` on `e`. -/
theorem tri_midline_foot {e : L} (hD : D ∈ e) (fA : Foot e A F) (fC : Foot e C H)
    (htA : Pas.ht (L := L) D A = C) : Pas.ht (L := L) D F = H := by
  sorry

/-- G1 + G2: every triangle `ABC` carries a midline configuration `MidConf`. -/
theorem tri_midline (h : ¬Collinear (Line := L) A B C) :
    ∃ (D E F G H : P) (e : L), MidConf L A B C D E F G H e := by
  sorry

end

end AngSum

end HilbertFoundations
