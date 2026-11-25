import HilbertFoundations.ProportionAux1

/-!
# Helper module for `Proportion.lean`: Theorems 22 and 23, equations of lines (§§ 16–17)

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV and axes
`ax`; lengths `len` in the ordered field `G ax` of segments.

* `thales`: parallels cut proportional segments from the sides of an angle (Theorem 23), and the
  converse `thales_converse`.
* `similar_prop`: similar triangles have proportional sides (Theorem 22), from Theorem 23 by laying
  off the second triangle in the first and the converse of Theorem 19.
* `mem_line_eq`, `exists_line_eq`, `line_of_eq`: the lines are the solution sets of linear
  equations in the co-ordinates.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section Thales

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- The cross product of two points of half-rays from `V₀`, in terms of the lengths. -/
theorem cross_rays {V0 X1 Y1 : P} (hX : X1 ≠ V0) (hY : Y1 ≠ V0) :
    ∃ c1 s1 c2 s2 : G ax, (∀ Z, Z ∈ ray V0 X1 → xc ax (toV ax.O Z - toV ax.O V0) = len ax V0 Z * c1 ∧
        yc ax (toV ax.O Z - toV ax.O V0) = len ax V0 Z * s1) ∧
      (∀ Z, Z ∈ ray V0 Y1 → xc ax (toV ax.O Z - toV ax.O V0) = len ax V0 Z * c2 ∧
        yc ax (toV ax.O Z - toV ax.O V0) = len ax V0 Z * s2) := by
  obtain ⟨c1, s1, h1⟩ := ray_coords ax hX
  obtain ⟨c2, s2, h2⟩ := ray_coords ax hY
  exact ⟨c1, s1, c2, s2, h1, h2⟩

/-- The direction of a segment joining points of two half-rays. -/
theorem sub_coords {V0 Y X : P} (cX sX cY sY : G ax) (lX lY : G ax)
    (hX : xc ax (toV ax.O X - toV ax.O V0) = lX * cX ∧ yc ax (toV ax.O X - toV ax.O V0) = lX * sX)
    (hY : xc ax (toV ax.O Y - toV ax.O V0) = lY * cY ∧ yc ax (toV ax.O Y - toV ax.O V0) = lY * sY) :
    xc ax (toV ax.O Y - toV ax.O X) = lY * cY - lX * cX ∧
      yc ax (toV ax.O Y - toV ax.O X) = lY * sY - lX * sX := by
  have e : toV ax.O Y - toV ax.O X = (toV ax.O Y - toV ax.O V0) - (toV ax.O X - toV ax.O V0) := by
    abel
  rw [e, xc_sub, yc_sub, hX.1, hX.2, hY.1, hY.2]
  exact ⟨rfl, rfl⟩

/-- **Theorem 23**: parallels cut proportional segments from the sides of an angle. Two lines
`X₁Y₁`, `X₂Y₂` parallel or equal, with `X₁, X₂` on one side and `Y₁, Y₂` on the other side of the
angle `∠X₁V₀Y₁`: `V₀X₁ · V₀Y₂ = V₀Y₁ · V₀X₂`. -/
theorem thales {V0 X1 X2 Y1 Y2 : P} (hn : ¬Collinear (Line := L) X1 V0 Y1)
    (hX2 : X2 ∈ ray V0 X1) (hY2 : Y2 ∈ ray V0 Y1) {l m : L} (hX1l : X1 ∈ l) (hY1l : Y1 ∈ l)
    (hX2m : X2 ∈ m) (hY2m : Y2 ∈ m) (hpar : l = m ∨ ¬Meets (Point := P) l m) :
    len ax V0 X1 * len ax V0 Y2 = len ax V0 Y1 * len ax V0 X2 := by
  obtain ⟨hX1V, hY1V, hXY⟩ := nc_ne ax hn
  have hXY2 : X2 ≠ Y2 := by
    intro e
    rw [e] at hX2
    exact not_collinear_of_mem_rays (L := L) hn hX2 hY2
      (collinear_of_ne (Line := L) (ne_of_mem_ray hY2))
  obtain ⟨c1, s1, c2, s2, h1, h2⟩ := cross_rays ax hX1V hY1V
  have pX1 := h1 X1 (mem_ray_self' (L := L) hX1V)
  have pX2 := h1 X2 hX2
  have pY1 := h2 Y1 (mem_ray_self' (L := L) hY1V)
  have pY2 := h2 Y2 hY2
  have hc := (parEq_iff_cross ax hXY hXY2 hX1l hY1l hX2m hY2m).1 hpar
  rw [cross] at hc
  rw [(sub_coords ax c1 s1 c2 s2 _ _ pX1 pY1).1, (sub_coords ax c1 s1 c2 s2 _ _ pX1 pY1).2,
    (sub_coords ax c1 s1 c2 s2 _ _ pX2 pY2).1, (sub_coords ax c1 s1 c2 s2 _ _ pX2 pY2).2] at hc
  -- the directions are independent
  have hD : cr c1 s1 c2 s2 ≠ 0 := by
    intro e
    apply hn
    have hm := (mem_line_iff_cross ax (Ne.symm hX1V) (mem_line_left (Line := L) (Ne.symm hX1V))
      (mem_line_right _) Y1).2 (by
        rw [cross, pX1.1, pX1.2, pY1.1, pY1.2]
        unfold cr at e ⊢
        linear_combination (len ax V0 X1 * len ax V0 Y1) * e)
    exact (collinear_of_mem (mem_line_right _) (mem_line_left _) hm)
  unfold cr at hc hD
  have : (len ax V0 X1 * len ax V0 Y2 - len ax V0 Y1 * len ax V0 X2) * (c1 * s2 - s1 * c2) = 0 := by
    linear_combination (-1 : G ax) * hc
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)

/-- **Converse of Theorem 23.** -/
theorem thales_converse {V0 X1 X2 Y1 Y2 : P} (hn : ¬Collinear (Line := L) X1 V0 Y1)
    (hX2 : X2 ∈ ray V0 X1) (hY2 : Y2 ∈ ray V0 Y1) {l m : L} (hX1l : X1 ∈ l) (hY1l : Y1 ∈ l)
    (hX2m : X2 ∈ m) (hY2m : Y2 ∈ m)
    (h : len ax V0 X1 * len ax V0 Y2 = len ax V0 Y1 * len ax V0 X2) :
    l = m ∨ ¬Meets (Point := P) l m := by
  obtain ⟨hX1V, hY1V, hXY⟩ := nc_ne ax hn
  have hXY2 : X2 ≠ Y2 := by
    intro e
    rw [e] at hX2
    exact not_collinear_of_mem_rays (L := L) hn hX2 hY2
      (collinear_of_ne (Line := L) (ne_of_mem_ray hY2))
  obtain ⟨c1, s1, c2, s2, h1, h2⟩ := cross_rays ax hX1V hY1V
  have pX1 := h1 X1 (mem_ray_self' (L := L) hX1V)
  have pX2 := h1 X2 hX2
  have pY1 := h2 Y1 (mem_ray_self' (L := L) hY1V)
  have pY2 := h2 Y2 hY2
  refine (parEq_iff_cross ax hXY hXY2 hX1l hY1l hX2m hY2m).2 ?_
  rw [cross, (sub_coords ax c1 s1 c2 s2 _ _ pX1 pY1).1, (sub_coords ax c1 s1 c2 s2 _ _ pX1 pY1).2,
    (sub_coords ax c1 s1 c2 s2 _ _ pX2 pY2).1, (sub_coords ax c1 s1 c2 s2 _ _ pX2 pY2).2]
  unfold cr
  linear_combination (s1 * c2 - c1 * s2) * h

end Thales

section Similar

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- **Theorem 22** at the vertex `A`: if `∠A ≡ ∠A'` and `∠B ≡ ∠B'`, then
`AB · A'C' = AC · A'B'`. -/
theorem similar_prop {A B C A' B' C' : P} (h : ¬Collinear (Line := L) A B C)
    (h' : ¬Collinear (Line := L) A' B' C') (hA : AngCong B A C B' A' C')
    (hB : AngCong A B C A' B' C') :
    len ax A B * len ax A' C' = len ax A C * len ax A' B' := by
  let F := pf (L := L) ax.hOE
  obtain ⟨hAB, hCB, hAC⟩ := nc_ne ax h
  obtain ⟨hAB', hCB', hAC'⟩ := nc_ne ax h'
  obtain ⟨B'', hB''r, sB''⟩ := segCong_layoff (L := L) hAB' hAB
  obtain ⟨C'', hC''r, sC''⟩ := segCong_layoff (L := L) hAC' hAC
  have hBAC : ¬Collinear (Line := L) B A C := fun hh => h hh.swap12
  have hB'A'C' : ¬Collinear (Line := L) B' A' C' := fun hh => h' hh.swap12
  have n2 : ¬Collinear (Line := L) B'' A C'' := not_collinear_of_mem_rays (L := L) hBAC hB''r hC''r
  have n2' : ¬Collinear (Line := L) A B'' C'' := fun hh => n2 hh.swap12
  have a1 : AngCong B' A' C' B'' A C'' :=
    angCong_rays hB'A'C' hBAC (angCong_symm hBAC hB'A'C' hA) (mem_ray_self' (L := L) (Ne.symm hAB'))
      (mem_ray_self' (L := L) (Ne.symm hAC')) hB''r hC''r
  obtain ⟨-, a2, -⟩ := F.sas h' n2' sB'' sC'' a1
  have a3 : AngCong A B C A B'' C'' := angCong_trans h h' n2' hB a2
  have hB''A : B'' ≠ A := ne_of_mem_ray hB''r
  have hC''A : C'' ≠ A := ne_of_mem_ray hC''r
  have eB : len ax A B'' = len ax A' B' :=
    (len_eq_iff ax (Ne.symm hB''A) hAB').2 (segCong_symm (L := L) hAB' (Ne.symm hB''A) sB'')
  have eC : len ax A C'' = len ax A' C' :=
    (len_eq_iff ax (Ne.symm hC''A) hAC').2 (segCong_symm (L := L) hAC' (Ne.symm hC''A) sC'')
  rw [← eB, ← eC]
  -- the lines `BC` and `B''C''` are parallel or equal
  set lAB := line (Line := L) A B hAB
  have hAl : A ∈ lAB := mem_line_left _
  have hBl : B ∈ lAB := mem_line_right _
  have hCl : C ∉ lAB := fun hh => h (collinear_of_mem hAl hBl hh)
  have hB''l : B'' ∈ lAB := mem_of_collinear (collinear_of_mem_ray hB''r) hAB hAl hBl
  have sCC : SameSide lAB C C'' := sameSide_of_ray hAl hCl hC''r
  have hBC := Ne.symm hCB
  have hBC'' : B'' ≠ C'' := fun e => sCC.2.1 (e ▸ hB''l)
  have tl := fun {X2 Y2 : P} {m : L} (hX2 : X2 ∈ ray A B) (hY2 : Y2 ∈ ray A C) (hX2m : X2 ∈ m)
      (hY2m : Y2 ∈ m) (hpar : line (Line := L) B C hBC = m ∨
        ¬Meets (Point := P) (line (Line := L) B C hBC) m) =>
    thales ax (L := L) hBAC hX2 hY2 (mem_line_left _) (mem_line_right _) hX2m hY2m hpar
  rcases mem_ray_cases (L := L) (mem_ray_self' (L := L) (Ne.symm hAB)) hB''r with e | hb | hb
  · -- `B'' = B`, then `C'' = C`
    subst e
    have r := F.layoff_unique Set.univ rfl A B C lAB B A C C'' h (lineIn_univ _) hBl hAl hAB
      trivial trivial sCC (angCong_refl (Line := L) h) a3
    have hC''r' : C'' ∈ ray B C := by rw [r]; exact mem_ray_self' (L := L) hBC''.symm
    have e2 : C'' = C := eq_of_collinear_collinear (L := L) h (collinear_of_mem_ray hC''r)
      (collinear_of_mem_ray hC''r')
    subst e2
    exact tl hB''r hC''r (mem_line_left _) (mem_line_right _) (Or.inl rfl)
  · -- `B` between `A` and `B''`
    obtain ⟨R, hR⟩ := exists_beyond (Line := L) (ne23_of_between (Line := L) hb)
    have hAR := (OrderLin.trans₁ hb hR).2
    have hc := F.supp h n2' a3 hb hAR
    have ss : SameSide (line (Line := L) B B'' (ne23_of_between (Line := L) hb)) C C'' := by
      rw [← eq_line (ne23_of_between (Line := L) hb) hBl hB''l]; exact sCC
    have hpar := theorem19_converse_corresponding (L := L) (a := line B C hBC)
      (b := line B'' C'' hBC'') (mem_line_left _) (mem_line_left _) (ne23_of_between (Line := L) hb)
      (mem_line_right _) (mem_line_right _) ss hR hc
    exact tl hB''r hC''r (mem_line_left _) (mem_line_right _) (Or.inr hpar)
  · -- `B''` between `A` and `B`
    obtain ⟨R, hR⟩ := exists_beyond (Line := L) (ne23_of_between (Line := L) hb)
    have hAR := (OrderLin.trans₁ hb hR).2
    have hc := F.supp n2' h (angCong_symm h n2' a3) hb hAR
    have ss : SameSide (line (Line := L) B'' B (ne23_of_between (Line := L) hb)) C'' C := by
      rw [← eq_line (ne23_of_between (Line := L) hb) hB''l hBl]; exact OrderCore.sameSide_symm sCC
    have hpar := theorem19_converse_corresponding (L := L) (a := line B'' C'' hBC'')
      (b := line B C hBC) (mem_line_left _) (mem_line_left _) (ne23_of_between (Line := L) hb)
      (mem_line_right _) (mem_line_right _) ss hR hc
    exact tl hB''r hC''r (mem_line_left _) (mem_line_right _)
      (Or.inr fun ⟨W, h1, h2⟩ => hpar ⟨W, h2, h1⟩)

end Similar

section Equations

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- The first co-ordinate of a point. -/
noncomputable def px (Z : P) : G ax := xc ax (toV ax.O Z)

/-- The second co-ordinate of a point. -/
noncomputable def py (Z : P) : G ax := yc ax (toV ax.O Z)

/-- The point with co-ordinates `(x, y)`. -/
noncomputable def mkPt (x y : G ax) : P := ofV ((x : V ax) + jE ax (y : V ax))

theorem mkPt_coords (x y : G ax) : px ax (mkPt ax x y) = x ∧ py ax (mkPt ax x y) = y :=
  coords_of ax x y rfl

/-- **Every point is uniquely determined by its co-ordinates.** -/
theorem coords_bijective : Function.Bijective (fun Z : P => (px ax Z, py ax Z)) := by
  refine ⟨fun Z W h => ?_, fun ⟨x, y⟩ => ⟨mkPt ax x y, by
    simp only [Prod.mk.injEq]; exact mkPt_coords ax x y⟩⟩
  simp only [Prod.mk.injEq] at h
  exact ofV_injective (O := ax.O) (vec_ext ax h.1 h.2)

theorem px_sub (Y X : P) : xc ax (toV ax.O Y - toV ax.O X) = px ax Y - px ax X := xc_sub ax _ _

theorem py_sub (Y X : P) : yc ax (toV ax.O Y - toV ax.O X) = py ax Y - py ax X := yc_sub ax _ _

/-- The line through two points in co-ordinates. -/
theorem mem_line_coords {X Y : P} (hXY : X ≠ Y) {l : L} (hX : X ∈ l) (hY : Y ∈ l) (Z : P) :
    Z ∈ l ↔ (px ax Y - px ax X) * (py ax Z - py ax X) - (py ax Y - py ax X) * (px ax Z - px ax X)
      = 0 := by
  rw [mem_line_iff_cross ax hXY hX hY Z, cross, px_sub, py_sub, px_sub, py_sub]
  rfl

/-- **Every line has a linear equation.** -/
theorem exists_line_eq (l : L) : ∃ a b c : G ax, (a ≠ 0 ∨ b ≠ 0) ∧
    ∀ Z : P, Z ∈ l ↔ a * px ax Z + b * py ax Z + c = 0 := by
  obtain ⟨X, Y, hXY, hX, hY⟩ := exists_two_points (Point := P) l
  refine ⟨-(py ax Y - py ax X), px ax Y - px ax X,
    (py ax Y - py ax X) * px ax X - (px ax Y - px ax X) * py ax X, ?_, fun Z => ?_⟩
  · by_contra hh
    push Not at hh
    apply hXY
    apply (coords_bijective ax).1
    simp only [Prod.mk.injEq]
    exact ⟨(sub_eq_zero.1 hh.2).symm, (sub_eq_zero.1 (neg_eq_zero.1 hh.1)).symm⟩
  · rw [mem_line_coords ax hXY hX hY Z]
    constructor <;> intro h <;> linear_combination h

/-- **Every linear equation represents a line.** -/
theorem exists_line_of_eq {a b : G ax} (hab : a ≠ 0 ∨ b ≠ 0) (c : G ax) :
    ∃ l : L, ∀ Z : P, Z ∈ l ↔ a * px ax Z + b * py ax Z + c = 0 := by
  obtain ⟨x0, y0, h0⟩ : ∃ x0 y0 : G ax, a * x0 + b * y0 + c = 0 := by
    by_cases ha : a = 0
    · have hb := hab.resolve_left (not_not.2 ha)
      exact ⟨0, -c / b, by rw [ha]; field_simp; ring⟩
    · exact ⟨-c / a, 0, by field_simp; ring⟩
  set X := mkPt ax x0 y0
  set Y := mkPt ax (x0 + b) (y0 - a)
  obtain ⟨hXx, hXy⟩ := mkPt_coords ax x0 y0
  obtain ⟨hYx, hYy⟩ := mkPt_coords ax (x0 + b) (y0 - a)
  have hXY : X ≠ Y := by
    intro e
    have e1 := congrArg (px ax) e
    have e2 := congrArg (py ax) e
    rw [hXx, hYx] at e1; rw [hXy, hYy] at e2
    rcases hab with ha | hb
    · exact ha (by linear_combination e2)
    · exact hb (by linear_combination -e1)
  refine ⟨line X Y hXY, fun Z => ?_⟩
  rw [mem_line_coords ax hXY (mem_line_left _) (mem_line_right _) Z, hXx, hXy, hYx, hYy]
  constructor
  · intro h; linear_combination h + h0
  · intro h; linear_combination h - h0

/-- **The line through the origin and the point `(a, b)`**: `b x - a y = 0`. -/
theorem line_origin_eq {C : P} (hC : C ≠ ax.O) {l : L} (hO : ax.O ∈ l) (hCl : C ∈ l) (Z : P) :
    Z ∈ l ↔ py ax C * px ax Z - px ax C * py ax Z = 0 := by
  have hpO : px ax ax.O = 0 ∧ py ax ax.O = 0 := by
    unfold px py; rw [toV_O ax]; exact ⟨xc_zero ax, yc_zero ax⟩
  rw [mem_line_coords ax (Ne.symm hC) hO hCl Z, hpO.1, hpO.2]
  constructor <;> intro h <;> linear_combination -h

/-- **The parallel to the line `OC` cutting off `c` on the `x`-axis**: `b x - a y - b c = 0`. -/
theorem parallel_line_eq {C : P} (hC : C ≠ ax.O) {l l' : L} (hO : ax.O ∈ l) (hCl : C ∈ l)
    (c : G ax) (hc : mkPt ax c 0 ∈ l') (hpar : l = l' ∨ ¬Meets (Point := P) l l') (Z : P) :
    Z ∈ l' ↔ py ax C * px ax Z - px ax C * py ax Z - py ax C * c = 0 := by
  have hd : toV ax.O C ∈ lineSub (L := L) l hO := hCl
  have hd0 : toV ax.O C ≠ 0 := fun e => hC (by
    have := congrArg ofV e; rwa [ofV_zero (L := L)] at this)
  rw [mem_line_iff_sub hO (parEq_symm hpar) hc Z, mem_lineSub_iff_cross ax hO hd hd0, cross,
    xc_sub, yc_sub]
  obtain ⟨h1, h2⟩ := mkPt_coords ax c 0
  have e1 : xc ax (toV ax.O (mkPt ax c 0)) = c := h1
  have e2 : yc ax (toV ax.O (mkPt ax c 0)) = 0 := h2
  rw [e1, e2]
  unfold cr px py
  constructor <;> intro h <;> linear_combination -h

/-- **The perpendicular to the `x`-axis at the point `x`** consists of the points with first
co-ordinate `x` (Hilbert's construction of the co-ordinates). -/
theorem perp_iff_px {x : G ax} (hx : x ≠ 0) {Z : P} (hZ : Z ∉ ax.x) :
    IsRightAngle (L := L) ax.O (ofV (x : V ax)) Z ↔ px ax Z = x := by
  have hx0 : ofV (x : V ax) ≠ ax.O := ofV_ne_O ax (fun h => hx (Subtype.ext h))
  rw [rightAngle_iff ax x.2 hx0 hZ, mem_Ys_iff, xc_sub]
  have : xc ax (toV ax.O (ofV (x : V ax))) = x := (coords_x ax x).1
  rw [this, sub_eq_zero]
  rfl

end Equations

end Pas

end HilbertFoundations
