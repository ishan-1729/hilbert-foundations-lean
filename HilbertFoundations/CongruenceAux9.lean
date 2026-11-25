import HilbertFoundations.CongruenceAux8

/-!
# Helper module for `Congruence.lean`: points with prescribed distances from a plane triangle

This module contains no unit of Hilbert's text. In a plane frame with groups I, II, IV:

* `Frame.memS_of_equidistant`: a point having the same distances from three non-collinear points
  of a plane `S` as a point of `S` lies in `S` (so, by `Frame.eq_of_equidistant`, it is that
  point). This is the solid-geometry fact behind the preservation of coplanarity by congruent
  figures (`congruentFigures_coplanar_space`) and the uniqueness part of Theorem 18 for a new point
  in the plane of three points of the figure. The proof is plane geometry only: every point of a
  side line of the triangle is equidistant from the two points (`Frame.equidistant_of_mem`, the
  triangles being taken in their own planes); a line of `S` through the given point meets two side
  lines (Pasch), and three collinear points with the same mutual distances as the new point and two
  of them force the new point onto that line (`Frame.collinear_of_segCong'`).
* `injective_fin3`: a list of three distinct points is injective.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

/-- Three distinct points, listed, form an injective family. -/
theorem injective_fin3 {P : Type u} {a b c : P} (h01 : a ≠ b) (h02 : a ≠ c) (h12 : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hT : TriangleCongruence P L] (F : Frame P L) {S : Set P}
  {G₁ G₂ G₃ X Y : P}
include hT F

/-- **A point with the distances of a point of a plane from three non-collinear points of the
plane lies in the plane.** -/
theorem memS_of_equidistant (hS : F.IsPl S) (h1 : G₁ ∈ S) (h2 : G₂ ∈ S) (h3 : G₃ ∈ S)
    (hY : Y ∈ S) (hn : ¬Collinear (Line := L) G₁ G₂ G₃) (hY1 : Y ≠ G₁) (hY2 : Y ≠ G₂)
    (hY3 : Y ≠ G₃) (hX1 : X ≠ G₁) (hX2 : X ≠ G₂) (hX3 : X ≠ G₃) (s1 : SegCong G₁ Y G₁ X)
    (s2 : SegCong G₂ Y G₂ X) (s3 : SegCong G₃ Y G₃ X) : X ∈ S := by
  obtain ⟨h12, h32, h13⟩ := F.ne hn
  have h23 : G₂ ≠ G₃ := h32.symm
  by_contra hXS
  -- `Y` on a side line: then so is `X`
  have side : ∀ {A B : P}, A ∈ S → B ∈ S → A ≠ B → Y ≠ A → Y ≠ B → X ≠ A → X ≠ B →
      SegCong A Y A X → SegCong B Y B X → Collinear (Line := L) A B Y → False := by
    intro A B hA hB hAB hYA hYB hXA hXB sA sB hc
    have c := F.collinear_of_segCong' hc hAB (Ne.symm hYB) (Ne.symm hYA) hAB (Ne.symm hXB)
      (Ne.symm hXA) (segCong_refl (Line := L) hAB) sB sA
    exact hXS (F.memS_of_collinear hS hA hB hAB c)
  have offY : ∀ {A B : P} (hAB : A ≠ B), A ∈ S → B ∈ S → Y ≠ A → Y ≠ B → X ≠ A → X ≠ B →
      SegCong A Y A X → SegCong B Y B X → Y ∉ line (Line := L) A B hAB :=
    fun hAB hA hB hYA hYB hXA hXB sA sB hYl => side hA hB hAB hYA hYB hXA hXB sA sB
      (collinear_of_mem (mem_line_left _) (mem_line_right _) hYl)
  have offX : ∀ {A B : P} (hAB : A ≠ B), A ∈ S → B ∈ S → X ∉ line (Line := L) A B hAB :=
    fun hAB hA hB hXl => hXS (F.lineIn hS hA hB hAB X hXl)
  -- the side line `G₂G₃` and a point `Z₁` within the segment `G₂G₃`
  have hY23 := offY h23 h2 h3 hY2 hY3 hX2 hX3 s2 s3
  obtain ⟨Z₁, hZ₁⟩ := exists_between (Line := L) h23
  have hZ₁l : Z₁ ∈ line (Line := L) G₂ G₃ h23 :=
    mem_mid_of_between hZ₁ (mem_line_left _) (mem_line_right _)
  have hZ₁S : Z₁ ∈ S := F.memS_of_between hS h2 h3 hZ₁
  have hYZ₁ : Y ≠ Z₁ := fun e => hY23 (e ▸ hZ₁l)
  have hXZ₁ : X ≠ Z₁ := fun e => hXS (e ▸ hZ₁S)
  have sZ₁ : SegCong Z₁ Y Z₁ X :=
    F.equidistant_of_mem h23 hY23 (offX h23 h2 h3) s2 s3 hZ₁l
  -- the line `m = YZ₁` of `S`
  set m := line (Line := L) Y Z₁ hYZ₁
  have hYm : Y ∈ m := mem_line_left _
  have hZ₁m : Z₁ ∈ m := mem_line_right _
  have hmS : LineIn m S := F.lineIn hS hY hZ₁S hYZ₁
  have finish : ∀ W, W ∈ m → W ≠ Z₁ → W ≠ Y → SegCong W Y W X → False := by
    intro W hWm hWZ hWY sW
    have hWS := hmS W hWm
    have c := F.collinear_of_segCong' (collinear_of_mem hZ₁m hWm hYm) hWZ.symm hWY
      (Ne.symm hYZ₁) hWZ.symm (fun e : W = X => hXS (by rw [← e]; exact hWS)) (Ne.symm hXZ₁)
      (segCong_refl (Line := L) hWZ.symm) sW sZ₁
    exact hXS (F.memS_of_collinear hS hZ₁S hWS hWZ.symm c)
  have hG₁23 : G₁ ∉ line (Line := L) G₂ G₃ h23 := fun hh =>
    hn (collinear_of_mem hh (mem_line_left _) (mem_line_right _))
  by_cases hG₁m : G₁ ∈ m
  · exact finish G₁ hG₁m (fun e => hG₁23 (e ▸ hZ₁l)) (Ne.symm hY1) s1
  have hG₂m : G₂ ∉ m := by
    intro hh
    have e := line_unique (ne12_of_between hZ₁) hh hZ₁m (mem_line_left (Line := L) h23) hZ₁l
    exact hY23 (e ▸ hYm)
  have hG₃m : G₃ ∉ m := by
    intro hh
    have e := line_unique (ne23_of_between hZ₁) hZ₁m hh hZ₁l (mem_line_right (Line := L) h23)
    exact hY23 (e ▸ hYm)
  have nc : ¬Collinear (Line := L) G₂ G₃ G₁ := fun hh => hn hh.perm312
  rcases F.pasch S hS G₂ G₃ G₁ Z₁ m hmS h2 h3 h1 nc hG₂m hG₃m hG₁m hZ₁m hZ₁ with
    ⟨W, hWm, hW⟩ | ⟨W, hWm, hW⟩
  · -- `W` within `G₃G₁`
    have h31 : G₃ ≠ G₁ := h13.symm
    have hWl : W ∈ line (Line := L) G₃ G₁ h31 :=
      mem_mid_of_between hW (mem_line_left _) (mem_line_right _)
    have hY31 := offY h31 h3 h1 hY3 hY1 hX3 hX1 s3 s1
    have hWZ : W ≠ Z₁ := by
      intro e
      have hne : line (Line := L) G₂ G₃ h23 ≠ line (Line := L) G₃ G₁ h31 := fun ee =>
        hG₁23 (ee ▸ mem_line_right _)
      exact ne23_of_between hZ₁ (eq_of_mem_of_mem hne hZ₁l (e ▸ hWl) (mem_line_right _)
        (mem_line_left _))
    exact finish W hWm hWZ (fun e => hY31 (e ▸ hWl))
      (F.equidistant_of_mem h31 hY31 (offX h31 h3 h1) s3 s1 hWl)
  · -- `W` within `G₂G₁`
    have h21 : G₂ ≠ G₁ := h12.symm
    have hWl : W ∈ line (Line := L) G₂ G₁ h21 :=
      mem_mid_of_between hW (mem_line_left _) (mem_line_right _)
    have hY21 := offY h21 h2 h1 hY2 hY1 hX2 hX1 s2 s1
    have hWZ : W ≠ Z₁ := by
      intro e
      have hne : line (Line := L) G₂ G₃ h23 ≠ line (Line := L) G₂ G₁ h21 := fun ee =>
        hG₁23 (ee ▸ mem_line_right _)
      exact ne12_of_between hZ₁ (eq_of_mem_of_mem hne (mem_line_left _) (mem_line_left _)
        hZ₁l (e ▸ hWl))
    exact finish W hWm hWZ (fun e => hY21 (e ▸ hWl))
      (F.equidistant_of_mem h21 hY21 (offX h21 h2 h1) s2 s1 hWl)

end Frame

end HilbertFoundations
