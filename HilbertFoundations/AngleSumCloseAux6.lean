import HilbertFoundations.AngleSumCloseAux5

/-!
# Helper module for the angle-sum theorem: exterior angle and Saccheri quadrilaterals

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

* **Exterior angle theorem** (`ext_angle`): an exterior angle of a triangle is greater than each
  of the two opposite interior angles.
* **Quadrilaterals with two right angles** (`BiRight`), **Saccheri quadrilaterals** (`Saccheri`)
  and **Lambert quadrilaterals** (`Lambert`): basic incidence facts; the reflection in the common
  perpendicular of base and summit exchanges the two sides of a Saccheri quadrilateral, so its
  summit angles are congruent, its base and summit lines do not meet, and it splits into two
  Lambert quadrilaterals.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
/-- A quadrilateral `ABDC` with right angles at `A`, `B`; `C`, `D` on the same side of `AB`. -/
def BiRight (A B C D : P) : Prop :=
  A ≠ B ∧ RightAng (L := L) B A C ∧ RightAng (L := L) A B D ∧
    ∀ l : L, A ∈ l → B ∈ l → SameSide l C D

variable (L) in
/-- A Saccheri quadrilateral with base `AB`, sides `AC ≡ BD`, summit `CD`. -/
def Saccheri (A B C D : P) : Prop := BiRight L A B C D ∧ SegCong A C B D

variable (L) in
/-- A Lambert quadrilateral: right angles at `M`, `B`, `N`; fourth angle `∠BDN`. -/
def Lambert (M B D N : P) : Prop :=
  RightAng (L := L) B M N ∧ RightAng (L := L) M B D ∧ RightAng (L := L) M N D

end

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}
include hC hl

/-- D1 (exterior angle theorem): if `Between B C D`, the exterior angle `∠ACD` of the triangle
`ABC` is greater than both interior angles `∠BAC` and `∠ABC`. -/
theorem ext_angle (h : ¬Collinear (Line := L) A B C) (hD : Between B C D) :
    AngLt (L := L) B A C A C D ∧ AngLt (L := L) A B C A C D := by
  sorry

/-- Building `BiRight A B C D` from one line `l` through `A`, `B` with `C`, `D` on the same side
of it. -/
theorem biRight_mk (hAB : A ≠ B) (hA : A ∈ l) (hB : B ∈ l) (h1 : RightAng (L := L) B A C)
    (h2 : RightAng (L := L) A B D) (hs : SameSide l C D) : BiRight L A B C D := by
  sorry

/-- D2(a): a quadrilateral with two right angles read from the other end of its base. -/
theorem biRight_symm (h : BiRight L A B C D) : BiRight L B A D C := by
  sorry

/-- D2(b): the two sides `AC`, `BD` of a quadrilateral with two right angles lie on lines without
common point. -/
theorem biRight_not_meets (h : BiRight L A B C D) {a b : L} (hA : A ∈ a) (hC : C ∈ a)
    (hB : B ∈ b) (hD : D ∈ b) : ¬Meets (Point := P) a b := by
  sorry

/-- D2(b): the summit angles of a quadrilateral with two right angles are genuine and its summit
points are distinct. -/
theorem biRight_nc (h : BiRight L A B C D) :
    ¬Collinear (Line := L) A C D ∧ ¬Collinear (Line := L) B D C ∧ C ≠ D := by
  sorry

/-- Helper for D3: a reflection exchanging two points `A`, `B` of `l` maps `l` onto itself. -/
theorem refl_mem_line_iff (hA : A ∈ l) (hB : B ∈ l) (hAB : A ≠ B) (e : Pas.refl m A = B) :
    ∀ Z : P, Z ∈ l ↔ Pas.refl m Z ∈ l := by
  sorry

/-- D3: a Saccheri quadrilateral is symmetric in a line `m` meeting base and summit in `M`, `N`;
`M B D N` is then a Lambert quadrilateral. -/
theorem saccheri_refl (h : Saccheri L A B C D) :
    ∃ (m : L) (M N : P), Pas.refl m A = B ∧ Pas.refl m C = D ∧ M ∈ m ∧ N ∈ m ∧
      Between A M B ∧ Between C N D ∧ Lambert L M B D N := by
  sorry

/-- D4: the two summit angles of a Saccheri quadrilateral are congruent. -/
theorem saccheri_summit (h : Saccheri L A B C D) : AngCong A C D B D C := by
  sorry

/-- D5: the line of the base and the line of the summit of a Saccheri quadrilateral do not
meet. -/
theorem saccheri_not_meets (h : Saccheri L A B C D) {l s : L} (hA : A ∈ l) (hB : B ∈ l)
    (hC : C ∈ s) (hD : D ∈ s) : ¬Meets (Point := P) l s := by
  sorry

/-- A Saccheri quadrilateral `A B C D` contains a Lambert quadrilateral `M B D N` with `M` on the
base and `N` on the summit. -/
theorem saccheri_lambert (h : Saccheri L A B C D) :
    ∃ M N : P, Between A M B ∧ Between C N D ∧ Lambert L M B D N := by
  obtain ⟨_, M, N, _, _, _, _, h1, h2, h3⟩ := saccheri_refl hl h
  exact ⟨M, N, h1, h2, h3⟩

end

end AngSum

end HilbertFoundations
