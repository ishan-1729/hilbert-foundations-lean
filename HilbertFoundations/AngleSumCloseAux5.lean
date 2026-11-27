import HilbertFoundations.AngleSumCloseAux4

/-!
# Helper module for the angle-sum theorem: comparison of segments and perpendiculars

This module contains no unit of Hilbert's text. Plane geometry with groups I, II, IV.

* **Comparison of segments** (`SLt`): `AB < CD` when `AB` is congruent to a part of `CD` starting
  at `C`; trichotomy and compatibility with congruence, without any use of parallels.
* **Perpendiculars**: the reflection in a line maps a point to the other end of its perpendicular
  through the line; two perpendiculars to a line do not meet; every point off a line has a unique
  foot (`Foot`) on it, and isometries mapping the line into itself map feet to feet; every point
  of a line carries a perpendicular.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

/-- `AB < CD`: the segment `AB` is congruent to a part `CX` of `CD`. -/
def SLt (A B C D : P) : Prop := ∃ X, Between C X D ∧ SegCong A B C X

/-- `F` is the foot of the perpendicular from `X` to `l`. -/
def Foot (l : L) (X F : P) : Prop :=
  F ∈ l ∧ X ∉ l ∧ ∀ G : P, G ∈ l → G ≠ F → RightAng (L := L) G F X

end

section

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}
include hC hl

/-- C1: trichotomy for segments: `AB < CD`, `AB ≡ CD` or `CD < AB`. -/
theorem sLt_trichotomy (hAB : A ≠ B) (hCD : C ≠ D) :
    SLt A B C D ∨ SegCong A B C D ∨ SLt C D A B := by
  sorry

/-- C2: `SLt` is compatible with congruence of the smaller segment. -/
theorem sLt_congr_left (h : SLt A B C D) (hAB : A ≠ B) (hA'B' : A' ≠ B')
    (hc : SegCong A B A' B') : SLt A' B' C D := by
  sorry

/-- `SLt` is compatible with congruence of the larger segment. -/
theorem sLt_congr_right (h : SLt A B C D) (hAB : A ≠ B) (hC'D' : C' ≠ D')
    (hc : SegCong C D C' D') : SLt A B C' D' := by
  sorry

/-- C3: if `AB < CD`, the segment `CD` can be laid off on the line `AB` beyond `B`. -/
theorem sLt_exists_beyond (h : SLt A B C D) (hAB : A ≠ B) :
    ∃ E, Between A B E ∧ SegCong C D A E := by
  sorry

/-- C4: if `∠GFX` is right with `G, F` on `l`, the reflection of `X` in `l` lies on the line `XF`
beyond `F`. -/
theorem between_refl_of_rightAng (hG : G ∈ l) (hF : F ∈ l) (h : RightAng (L := L) G F X) :
    Between X F (Pas.refl l X) := by
  sorry

/-- C5: a triangle `F F' X` cannot have right angles at both `F` and `F'`. -/
theorem no_two_right {F' : P} (h1 : RightAng (L := L) F' F X)
    (h2 : RightAng (L := L) F F' X) : False := by
  sorry

/-- C6: every point off a line has a foot of the perpendicular on it. -/
theorem exists_foot (hX : X ∉ l) : ∃ F, Foot l X F := by
  sorry

/-- A right angle `∠GFX` with `G, F` on `l` makes `F` the foot of `X` on `l`. -/
theorem foot_of_rightAng (hG : G ∈ l) (hF : F ∈ l) (h : RightAng (L := L) G F X) :
    Foot l X F := by
  sorry

/-- The foot of the perpendicular from a point to a line is unique. -/
theorem foot_unique {F' : P} (h : Foot l X F) (h' : Foot l X F') : F = F' := by
  sorry

/-- An isometry mapping the line `l` into itself maps the foot of `X` to the foot of the image of
`X`. -/
theorem foot_map {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (hmap : ∀ Z : P, Z ∈ l → f Z ∈ l) (h : Foot l X F) : Foot l (f X) (f F) := by
  sorry

/-- C7: two right angles `∠GFX`, `∠GFY` on the same arm `FG` have their other arms on one
line. -/
theorem rightAng_collinear (h1 : RightAng (L := L) G F X) (h2 : RightAng (L := L) G F Y) :
    Collinear (Line := L) F X Y := by
  sorry

/-- C8: two perpendiculars `FX`, `F'Y` to the line `FF'` do not meet. -/
theorem perp_not_meets {a b : L} {F' : P} (hF : F ∈ a) (hX : X ∈ a) (hF' : F' ∈ b)
    (hY : Y ∈ b) (h1 : RightAng (L := L) F' F X) (h2 : RightAng (L := L) F F' Y) :
    ¬Meets (Point := P) a b := by
  sorry

/-- C9: if `FX` and `F'W` are perpendicular to `FF'`, then `W` and `F'` lie on the same side of
the line `a = FX`. -/
theorem sameSide_perp {a : L} {F' W : P} (hF : F ∈ a) (hX : X ∈ a)
    (h1 : RightAng (L := L) F' F X) (h2 : RightAng (L := L) F F' W) : SameSide a W F' := by
  sorry

/-- C10: through every point `F` of `l` there is a line `m` perpendicular to `l`. -/
theorem exists_perp_at (hF : F ∈ l) :
    ∃ m : L, F ∈ m ∧
      ∀ Z : P, Z ∈ m → Z ≠ F → ∀ G : P, G ∈ l → G ≠ F → RightAng (L := L) G F Z := by
  sorry

end

end AngSum

end HilbertFoundations
