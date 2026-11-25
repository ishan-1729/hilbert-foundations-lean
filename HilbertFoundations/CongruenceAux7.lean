import HilbertFoundations.CongruenceAux6

/-!
# Helper module for `Congruence.lean`: congruent figures (Theorem 17)

This module contains no unit of Hilbert's text. In a plane frame, with groups I, II, IV, points of
two planes `S`, `S'` are compared through a base `A, B` (in `S`) and `A', B'` (in `S'`): a point `Z`
corresponds to `Z'` when `AZ ≡ A'Z'` and `Z` has the same position with respect to the base (on the
line `AB`: on the same half-ray from `A`; off it: `∠BAZ ≡ ∠B'A'Z'`), and pairs of points off the base
line correspond when they lie on the same side or on different sides of it in both planes. Then
corresponding pairs have congruent distances (`Frame.seg_line_line`, `Frame.seg_line_off`,
`Frame.seg_off_off`), from which:

* `Frame.sameSide_of_segCong`: the arrangement of points with respect to lines is the same in
  figures with congruent segments (property of congruent figures, § 7);
* `Frame.theorem17_exists`: the point `P'` of Theorem 17.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

section Line

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] {A Z W A' Z' W' : P}
include hS

/-- Two points of a line through `A` at given distances from `A`, on the same or on different
half-rays from `A`: their distance is determined (IV 1–3). -/
theorem seg_on_line (hAZ : SegCong A Z A' Z') (hAW : SegCong A W A' W') (hZA : Z ≠ A)
    (hWA : W ≠ A) (hZ'A' : Z' ≠ A') (hW'A' : W' ≠ A') (hc : Collinear A W Z)
    (hc' : Collinear A' W' Z') (hZW : Z ≠ W) (hpos : Z ∈ ray A W ↔ Z' ∈ ray A' W') :
    SegCong Z W Z' W' := by
  by_cases hr : Z ∈ ray A W
  · have hr' := hpos.1 hr
    rcases mem_ray_cases (L := L) hr (mem_ray_self' (L := L) hWA) with e | hb | hb
    · exact absurd e hZW
    · have hb' := between_of_segCong_ray hb hr' hAZ hAW
      exact segCong_sub hb hb' hAZ hAW
    · have hb' := between_of_segCong_ray hb (mem_ray_comm hr') hAW hAZ
      exact segCong_swap (segCong_sub hb hb' hAW hAZ)
  · have hr' : Z' ∉ ray A' W' := fun h => hr (hpos.2 h)
    have hb : Between W A Z := (mem_ray_or_between (L := L) hc hWA hZA).resolve_left hr
    have hb' : Between W' A' Z' := (mem_ray_or_between (L := L) hc' hW'A' hZ'A').resolve_left hr'
    exact segCong_add (between_symm hb) (between_symm hb') (segCong_swap_left (Line := L)
      (segCong_swap_right (Line := L) hAZ)) hAW

end Line

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hT : TriangleCongruence P L] (F : Frame P L) {S S' : Set P}
  {A B Z W A' B' Z' W' X Y X' Y' : P}
include hT F

/-- A point `Z` of the line `AB` and a point `W` off it, with corresponding positions: `ZW ≡ Z'W'`. -/
theorem seg_line_off (hAB : A ≠ B) (hA'B' : A' ≠ B') (hZ : Collinear A B Z) (hZA : Z ≠ A)
    (hZ' : Collinear A' B' Z') (hZ'A' : Z' ≠ A') (hpos : Z ∈ ray A B ↔ Z' ∈ ray A' B')
    (hW : ¬Collinear B A W) (hW' : ¬Collinear B' A' W') (hang : AngCong B A W B' A' W')
    (hAZ : SegCong A Z A' Z') (hAW : SegCong A W A' W') : SegCong Z W Z' W' := by
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hZl : Z ∈ line (Line := L) A B hAB := mem_of_collinear hZ hAB hAl hBl
  have hWl : W ∉ line (Line := L) A B hAB := fun hh => hW (collinear_of_mem hBl hAl hh)
  have hA'l : A' ∈ line (Line := L) A' B' hA'B' := mem_line_left _
  have hB'l : B' ∈ line (Line := L) A' B' hA'B' := mem_line_right _
  have hZ'l : Z' ∈ line (Line := L) A' B' hA'B' := mem_of_collinear hZ' hA'B' hA'l hB'l
  have hW'l : W' ∉ line (Line := L) A' B' hA'B' := fun hh => hW' (collinear_of_mem hB'l hA'l hh)
  have nZ := nc_of hAl hZl hZA.symm hWl
  have nZ' := nc_of hA'l hZ'l hZ'A'.symm hW'l
  have hWA : W ≠ A := ne_of_mem_not_mem hAl hWl
  have hW'A' : W' ≠ A' := ne_of_mem_not_mem hA'l hW'l
  have a : AngCong Z A W Z' A' W' := by
    by_cases hr : Z ∈ ray A B
    · exact angCong_rays hW hW' hang hr (mem_ray_self' (L := L) hWA) (hpos.1 hr)
        (mem_ray_self' (L := L) hW'A')
    · have hr' : Z' ∉ ray A' B' := fun h => hr (hpos.2 h)
      have hb := (mem_ray_or_between (L := L) hZ hAB.symm hZA).resolve_left hr
      have hb' := (mem_ray_or_between (L := L) hZ' hA'B'.symm hZ'A').resolve_left hr'
      have s := F.supp hW hW' hang hb hb'
      exact angCong_swap_right nZ.2.2.2.1 nZ'.2.2.1 (angCong_swap_left nZ.2.2.1 nZ'.2.2.1 s)
  exact (F.sas (A := A) (B := Z) (C := W) (A' := A') (B' := Z') (C' := W') nZ.1 nZ'.1 hAZ hAW a).1

/-- Collinearity of `Z`, `A`, `W` (two points off the line `AB`) is carried to `Z'`, `A'`, `W'` by
corresponding angles and sides. -/
theorem col_of_col (hS' : F.IsPl S') (hA'S : A' ∈ S') (hB'S : B' ∈ S') (hZ'S : Z' ∈ S')
    (hW'S : W' ∈ S') (hAB : A ≠ B) (hA'B' : A' ≠ B')
    (hZ : ¬Collinear B A Z) (hW : ¬Collinear B A W) (hZ' : ¬Collinear B' A' Z')
    (hW' : ¬Collinear B' A' W') (aZ : AngCong B A Z B' A' Z') (aW : AngCong B A W B' A' W')
    (hside : SameSide (line (Line := L) A B hAB) Z W ↔ SameSide (line (Line := L) A' B' hA'B') Z' W')
    (hc : Collinear Z A W) : Collinear Z' A' W' := by
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hA'l : A' ∈ line (Line := L) A' B' hA'B' := mem_line_left _
  have hB'l : B' ∈ line (Line := L) A' B' hA'B' := mem_line_right _
  have hZl : Z ∉ line (Line := L) A B hAB := fun hh => hZ (collinear_of_mem hBl hAl hh)
  have hWl : W ∉ line (Line := L) A B hAB := fun hh => hW (collinear_of_mem hBl hAl hh)
  have hZ'l : Z' ∉ line (Line := L) A' B' hA'B' := fun hh => hZ' (collinear_of_mem hB'l hA'l hh)
  have hW'l : W' ∉ line (Line := L) A' B' hA'B' := fun hh => hW' (collinear_of_mem hB'l hA'l hh)
  have hZA := ne_of_mem_not_mem hAl hZl
  have hWA := ne_of_mem_not_mem hAl hWl
  have hZ'A' := ne_of_mem_not_mem hA'l hZ'l
  have hW'A' := ne_of_mem_not_mem hA'l hW'l
  have hl'S := F.lineIn hS' hA'S hB'S hA'B'
  rcases mem_ray_or_between (L := L) (show Collinear A W Z from hc.perm231) hWA hZA with
    hr | hb
  · have hs : SameSide (line (Line := L) A B hAB) Z W :=
      sameSide_symm' (sameSide_of_ray hAl hWl hr)
    have hs' := hside.1 hs
    have e1 : AngCong B A Z B A W := angCong_rays hW hW (angCong_refl hW)
      (mem_ray_self' (L := L) hAB.symm) hr (mem_ray_self' (L := L) hAB.symm)
      (mem_ray_self' (L := L) hWA)
    have e2 : AngCong B' A' Z' B' A' W' := angCong_trans hZ' hZ hW'
      (angCong_symm hZ hZ' aZ) (angCong_trans hZ hW hW' e1 aW)
    have e := F.layoff_unique S' hS' B' A' Z' _ A' B' Z' W' hZ' hl'S hA'l hB'l hA'B'.symm hZ'S
      hW'S hs' (angCong_refl hZ') e2
    have hW'r : W' ∈ ray A' Z' := by rw [e]; exact mem_ray_self' (L := L) hW'A'
    obtain ⟨g, h1, h2, h3⟩ := collinear_of_mem_ray hW'r
    exact ⟨g, h2, h1, h3⟩
  · have hns : ¬SameSide (line (Line := L) A B hAB) Z W := fun hs =>
      not_sameSide_of_opp' (opp_of_between_mem hAl hZl (between_symm hb)) hs
    have ho' : OppositeSides (line (Line := L) A' B' hA'B') Z' W' :=
      (sameSide_or_opp' hZ'l hW'l).resolve_left (fun h => hns (hside.2 h))
    obtain ⟨Ws, hWs⟩ := exists_beyond (Line := L) hZ'A'
    have hWsS := F.memS_of_between' hS' hZ'S hA'S hWs
    have nZ : ¬Collinear Z A B := fun hh => hZ hh.swap13
    have nZ' : ¬Collinear Z' A' B' := fun hh => hZ' hh.swap13
    have aZ' : AngCong Z A B Z' A' B' := angCong_swap_right nZ (not_collinear_swap nZ')
      (angCong_swap_left hZ hZ' aZ)
    have s : AngCong B A W B' A' Ws := F.supp nZ nZ' aZ' (between_symm hb) hWs
    have nWs : ¬Collinear B' A' Ws := not_collinear_swap (not_collinear_of_between nZ' hWs)
    have e2 : AngCong B' A' W' B' A' Ws := angCong_trans hW' hW nWs (angCong_symm hW hW' aW) s
    have oWs : OppositeSides (line (Line := L) A' B' hA'B') Z' Ws :=
      opp_of_between_mem hA'l hZ'l hWs
    have hss : SameSide (line (Line := L) A' B' hA'B') W' Ws :=
      F.ss_of_opp_opp hS' hl'S hW'S hZ'S hWsS (opp_symm' ho') oWs
    have e := F.layoff_unique S' hS' B' A' W' _ A' B' W' Ws hW' hl'S hA'l hB'l hA'B'.symm hW'S
      hWsS hss (angCong_refl hW') e2
    have hWsA' : Ws ≠ A' := ne_of_mem_not_mem hA'l oWs.2.1
    have hWsr : Ws ∈ ray A' W' := by rw [e]; exact mem_ray_self' (L := L) hWsA'
    obtain ⟨g, h1, h2, h3⟩ := collinear_of_mem_ray hWsr
    have hZ'g : Z' ∈ g := mem_left_of_between hWs h1 h3
    exact ⟨g, hZ'g, h1, h2⟩

/-- For a point `A` of `l` and `Z`, `W` off `l` on a line through `A`: `Z` is on the half-ray `AW`
iff `Z`, `W` lie on the same side of `l`. -/
theorem ray_iff_sameSide {l : L} (hA : A ∈ l) (hZ : Z ∉ l) (hW : W ∉ l)
    (hc : Collinear A W Z) : Z ∈ ray A W ↔ SameSide l Z W := by
  have hZA := ne_of_mem_not_mem hA hZ
  have hWA := ne_of_mem_not_mem hA hW
  constructor
  · intro hr; exact sameSide_symm' (sameSide_of_ray hA hW hr)
  · intro hs; exact mem_ray_of_sameSide hA hc hZA (sameSide_symm' hs)

/-- Two points `Z`, `W` off the line `AB`, with corresponding distances from `A`, corresponding
angles with `AB` and corresponding sides: `ZW ≡ Z'W'` (Theorems 14 and 10). -/
theorem seg_off_off (hS : F.IsPl S) (hS' : F.IsPl S') (hAS : A ∈ S) (hBS : B ∈ S) (hZS : Z ∈ S)
    (hWS : W ∈ S) (hA'S : A' ∈ S') (hB'S : B' ∈ S') (hZ'S : Z' ∈ S') (hW'S : W' ∈ S')
    (hAB : A ≠ B) (hA'B' : A' ≠ B') (hZ : ¬Collinear B A Z) (hW : ¬Collinear B A W)
    (hZ' : ¬Collinear B' A' Z') (hW' : ¬Collinear B' A' W') (hZW : Z ≠ W)
    (hAZ : SegCong A Z A' Z') (hAW : SegCong A W A' W') (aZ : AngCong B A Z B' A' Z')
    (aW : AngCong B A W B' A' W')
    (hside : SameSide (line (Line := L) A B hAB) Z W ↔
      SameSide (line (Line := L) A' B' hA'B') Z' W') : SegCong Z W Z' W' := by
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hA'l : A' ∈ line (Line := L) A' B' hA'B' := mem_line_left _
  have hB'l : B' ∈ line (Line := L) A' B' hA'B' := mem_line_right _
  have hZl : Z ∉ line (Line := L) A B hAB := fun hh => hZ (collinear_of_mem hBl hAl hh)
  have hWl : W ∉ line (Line := L) A B hAB := fun hh => hW (collinear_of_mem hBl hAl hh)
  have hZ'l : Z' ∉ line (Line := L) A' B' hA'B' := fun hh => hZ' (collinear_of_mem hB'l hA'l hh)
  have hW'l : W' ∉ line (Line := L) A' B' hA'B' := fun hh => hW' (collinear_of_mem hB'l hA'l hh)
  have hZA := ne_of_mem_not_mem hAl hZl
  have hWA := ne_of_mem_not_mem hAl hWl
  have hZ'A' := ne_of_mem_not_mem hA'l hZ'l
  have hW'A' := ne_of_mem_not_mem hA'l hW'l
  by_cases hc : Collinear Z A W
  · have hc' := F.col_of_col hS' hA'S hB'S hZ'S hW'S hAB hA'B' hZ hW hZ' hW' aZ aW hside hc
    have p1 := F.ray_iff_sameSide hAl hZl hWl hc.perm231
    have p2 := F.ray_iff_sameSide hA'l hZ'l hW'l hc'.perm231
    exact seg_on_line hAZ hAW hZA hWA hZ'A' hW'A' hc.perm231 hc'.perm231 hZW
      (p1.trans (hside.trans p2.symm))
  · have hc' : ¬Collinear Z' A' W' := fun hc' =>
      hc (F.col_of_col hS hAS hBS hZS hWS hA'B' hAB hZ' hW' hZ hW (angCong_symm hZ hZ' aZ)
        (angCong_symm hW hW' aW) hside.symm hc')
    have nZ : ¬Collinear Z A B := fun hh => hZ hh.swap13
    have nW : ¬Collinear W A B := fun hh => hW hh.swap13
    have nZ' : ¬Collinear Z' A' B' := fun hh => hZ' hh.swap13
    have nW' : ¬Collinear W' A' B' := fun hh => hW' hh.swap13
    have h1 : AngCong Z A B Z' A' B' :=
      angCong_swap_right nZ hZ' (angCong_swap_left hZ hZ' aZ)
    have h2 : AngCong W A B W' A' B' :=
      angCong_swap_right nW hW' (angCong_swap_left hW hW' aW)
    have hsd : (SameSide (line (Line := L) A B hAB) Z W ∧
          SameSide (line (Line := L) A' B' hA'B') Z' W') ∨
        (OppositeSides (line (Line := L) A B hAB) Z W ∧
          OppositeSides (line (Line := L) A' B' hA'B') Z' W') := by
      rcases sameSide_or_opp' hZl hWl with hs | ho
      · exact Or.inl ⟨hs, hside.1 hs⟩
      · exact Or.inr ⟨ho, (sameSide_or_opp' hZ'l hW'l).resolve_left
          (fun h => not_sameSide_of_opp' ho (hside.2 h))⟩
    have a := F.angle_addition (O := A) (H := Z) (K := W) (M := B) (O' := A') (H' := Z')
      (K' := W') (M' := B') hS hS' hAS hZS hWS hBS hA'S hZ'S hW'S hB'S nZ nW hc nZ' nW' hc'
      h1 h2 hAB.symm hA'B'.symm hsd
    have nAZW : ¬Collinear A Z W := fun hh => hc hh.swap12
    have nAZW' : ¬Collinear A' Z' W' := fun hh => hc' hh.swap12
    exact (F.sas (A := A) (B := Z) (C := W) (A' := A') (B' := Z') (C' := W') nAZW nAZW' hAZ hAW
      a).1

/-- **The arrangement of points with respect to a line is carried by congruence** (property of
congruent figures, § 7): if the six segments of `A, B, X, Y` (in a plane `S`) and of `A', B', X', Y'`
(in a plane `S'`) are congruent and `X`, `Y` lie on the same side of `AB`, then `X'`, `Y'` lie on
the same side of `A'B'`. -/
theorem sameSide_of_segCong (hS : F.IsPl S) (hS' : F.IsPl S') (hAS : A ∈ S) (hBS : B ∈ S)
    (hXS : X ∈ S) (hYS : Y ∈ S) (hA'S : A' ∈ S') (hB'S : B' ∈ S') (hX'S : X' ∈ S')
    (hY'S : Y' ∈ S') (hAB : A ≠ B) (hA'B' : A' ≠ B') (hX : ¬Collinear A B X)
    (hY : ¬Collinear A B Y) (hX' : ¬Collinear A' B' X') (hY' : ¬Collinear A' B' Y')
    (hXY : X ≠ Y) (hX'Y' : X' ≠ Y') (sAB : SegCong A B A' B') (sAX : SegCong A X A' X')
    (sAY : SegCong A Y A' Y') (sBX : SegCong B X B' X') (sBY : SegCong B Y B' Y')
    (sXY : SegCong X Y X' Y') (hs : SameSide (line (Line := L) A B hAB) X Y) :
    SameSide (line (Line := L) A' B' hA'B') X' Y' := by
  by_contra hn
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hA'l : A' ∈ line (Line := L) A' B' hA'B' := mem_line_left _
  have hB'l : B' ∈ line (Line := L) A' B' hA'B' := mem_line_right _
  have hX'l : X' ∉ line (Line := L) A' B' hA'B' := fun hh => hX' (collinear_of_mem hA'l hB'l hh)
  have hY'l : Y' ∉ line (Line := L) A' B' hA'B' := fun hh => hY' (collinear_of_mem hA'l hB'l hh)
  have ho' := (sameSide_or_opp' hX'l hY'l).resolve_left hn
  have nBAX : ¬Collinear B A X := fun hh => hX hh.swap12
  have nBAY : ¬Collinear B A Y := fun hh => hY hh.swap12
  have nBAX' : ¬Collinear B' A' X' := fun hh => hX' hh.swap12
  have nBAY' : ¬Collinear B' A' Y' := fun hh => hY' hh.swap12
  have aX := (F.sss hX hX' sAB sAX sBX).1
  have aY := (F.sss hY hY' sAB sAY sBY).1
  have hlS' := F.lineIn hS' hA'S hB'S hA'B'
  obtain ⟨Y0, hY0S, hY0s, hY0c⟩ := F.layoff S' hS' B' A' Y' _ A' B' X' nBAY' hlS' hA'l hB'l
    hA'B'.symm hX'S hX'l
  have hY0A : Y0 ≠ A' := ne_of_mem_not_mem hA'l hY0s.1
  have hAY : A ≠ Y := (F.ne nBAY).2.1.symm
  obtain ⟨Ys, hYsr, hYsc⟩ := segCong_layoff (L := L) hAY hY0A.symm
  have hYsS := F.memS_of_ray hS' hA'S hY0S hYsr
  have nY0 : ¬Collinear B' A' Y0 := fun hh => hY0s.1 (by
    obtain ⟨g, h1, h2, h3⟩ := hh
    rw [line_unique hA'B' hA'l hB'l h2 h1]; exact h3)
  have nYs : ¬Collinear B' A' Ys := not_collinear_of_mem_rays nY0
    (mem_ray_self' (L := L) hA'B'.symm) hYsr
  have r1 : AngCong B' A' Y' B' A' Ys := angCong_rays nBAY' nY0 hY0c
    (mem_ray_self' (L := L) hA'B'.symm) (mem_ray_self' (L := L) (F.ne nBAY').2.1)
    (mem_ray_self' (L := L) hA'B'.symm) hYsr
  have aYs : AngCong B A Y B' A' Ys := angCong_trans nBAY nBAY' nYs aY r1
  have sXYs : SameSide (line (Line := L) A' B' hA'B') X' Ys :=
    F.ss_trans hS' hlS' hX'S hY0S hYsS (sameSide_symm' hY0s) (sameSide_of_ray hA'l hY0s.1 hYsr)
  have hYsl : Ys ∉ line (Line := L) A' B' hA'B' := sXYs.2.1
  have hX'A' : X' ≠ A' := ne_of_mem_not_mem hA'l hX'l
  have hAX : A ≠ X := (F.ne nBAX).2.1.symm
  have hX'Ys : X' ≠ Ys := by
    intro e
    rw [← e] at aYs hYsc
    have hl := F.lineIn hS hAS hBS hAB
    have e1 : AngCong B A X B A Y := angCong_trans nBAX nBAX' nBAY aX
      (angCong_symm nBAY nBAX' aYs)
    have er := F.layoff_unique S hS B A X _ A B X Y nBAX hl hAl hBl hAB.symm hXS hYS hs
      (angCong_refl nBAX) e1
    have s1 : SegCong A X A Y := segCong_trans (L := L) hAX hX'A'.symm hAY sAX
      (segCong_symm (L := L) hAY hX'A'.symm hYsc)
    exact hXY (eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hAX.symm)
      (by rw [er]; exact mem_ray_self' (L := L) hAY.symm) s1)
  have hYsA : Ys ≠ A' := ne_of_mem_ray hYsr
  have hY'A' : Y' ≠ A' := ne_of_mem_not_mem hA'l hY'l
  have sXY' := F.seg_off_off hS hS' hAS hBS hXS hYS hA'S hB'S hX'S hYsS hAB hA'B' nBAX nBAY
    nBAX' nYs hXY sAX hYsc aX aYs ⟨fun _ => sXYs, fun _ => hs⟩
  have sAYs : SegCong A' Ys A' Y' := segCong_trans (L := L) hYsA.symm hAY hY'A'.symm
    (segCong_symm (L := L) hAY hYsA.symm hYsc) sAY
  have nYs' : ¬Collinear A' B' Ys := fun hh => nYs hh.swap12
  have sBYs := (F.sas (A := A') (B := B') (C := Ys) (A' := A') (B' := B') (C' := Y') nYs' hY'
    (segCong_refl (Line := L) hA'B') sAYs (angCong_symm nBAY' nYs r1)).1
  have cXYs : SegCong X' Ys X' Y' := segCong_trans (L := L) hX'Ys hXY hX'Y' (segCong_symm (L := L)
    hXY hX'Ys sXY') sXY
  have e := F.eq_of_equidistant hS' hA'S hB'S hX'S hYsS hY'S hX' hYsA
    (ne_of_mem_not_mem hB'l hYsl) hX'Ys.symm hY'A' (ne_of_mem_not_mem hB'l hY'l) hX'Y'.symm
    sAYs sBYs cXYs
  rw [e] at sXYs
  exact hn sXYs
/-- Points of a line through `A` and `B`: `X` lies on the half-ray `AQ` iff `X` and `Q` lie both on
the half-ray `AB` or both off it. -/
theorem ray_iff_of_rays {a : L} {Q : P} (hA : A ∈ a) (hB : B ∈ a) (hX : X ∈ a) (hQ : Q ∈ a)
    (hBA : B ≠ A) (hXA : X ≠ A) (hQA : Q ≠ A) :
    X ∈ ray A Q ↔ (X ∈ ray A B ↔ Q ∈ ray A B) := by
  have s := fun Y Z (hY : Y ∈ a) (hZ : Z ∈ a) (hYA : Y ≠ A) (hZA : Z ≠ A) =>
    sameSidePt_iff_sgn (L := L) hA hB hBA.symm hY hZ hYA hZA
  simp only [mem_ray]
  rw [s Q X hQ hX hQA hXA, s B X hB hX hBA hXA, s B Q hB hQ hBA hQA]
  have hBB : OrderLin.sgn A B B = 1 := by
    rcases OrderLin.sgn_of_ne (U := B) hBA with h | h
    · exact absurd h.2 (not_between_self (Line := L))
    · exact h.1
  rw [hBB]
  rcases OrderLin.sgn_of_ne (U := B) hXA with h1 | h1 <;>
    rcases OrderLin.sgn_of_ne (U := B) hQA with h2 | h2 <;> rw [h1.1, h2.1] <;> decide

/-- Three points `X`, `Q`, `C` off a line `l` of a plane: `X`, `Q` are on the same side iff their
positions with respect to `C` agree. -/
theorem ss_iff3 (hS : F.IsPl S) {l : L} {Q C : P} (hl : LineIn l S) (hXS : X ∈ S) (hQS : Q ∈ S)
    (hCS : C ∈ S) (hX : X ∉ l) (hQ : Q ∉ l) (hC : C ∉ l) :
    SameSide l X Q ↔ (SameSide l X C ↔ SameSide l Q C) := by
  constructor
  · intro h
    exact ⟨fun h1 => F.ss_trans hS hl hQS hXS hCS (sameSide_symm' h) h1,
      fun h2 => F.ss_trans hS hl hXS hQS hCS h h2⟩
  · intro h
    rcases sameSide_or_opp' hX hC with h1 | h1
    · exact F.ss_trans hS hl hXS hCS hQS h1 (sameSide_symm' (h.1 h1))
    · have h2 : ¬SameSide l Q C := fun h2 => not_sameSide_of_opp' h1 (h.2 h2)
      have h2' := (sameSide_or_opp' hQ hC).resolve_left h2
      exact F.ss_of_opp_opp hS hl hXS hCS hQS h1 (opp_symm' h2')

/-- **Theorem 17, existence** (a figure with at least two points `f a0 ≠ f b0`): for congruent
figures `f` (in the plane `S`) and `g` (in `S'`) and a new point `Q` of `S` there is a new point
`Q'` of `S'` with `f i Q ≡ g i Q'` for all `i`. -/
theorem theorem17_two (hS : F.IsPl S) (hS' : F.IsPl S') {n : ℕ} {f g : Fin n → P}
    (hfS : ∀ i, f i ∈ S) (hgS : ∀ i, g i ∈ S') (hfi : Function.Injective f)
    (hgi : Function.Injective g) (hseg : ∀ i j, i ≠ j → SegCong (f i) (f j) (g i) (g j))
    {a0 b0 : Fin n} (hab : a0 ≠ b0) {Q : P} (hQS : Q ∈ S) (hQf : ∀ i, Q ≠ f i) :
    ∃ Q', Q' ∈ S' ∧ (∀ i, Q' ≠ g i) ∧ ∀ i, SegCong (f i) Q (g i) Q' := by
  classical
  have hAB : f a0 ≠ f b0 := hfi.ne hab
  have hA'B' : g a0 ≠ g b0 := hgi.ne hab
  set l := line (Line := L) (f a0) (f b0) hAB with hl
  set l' := line (Line := L) (g a0) (g b0) hA'B' with hl'
  have hAl : f a0 ∈ l := mem_line_left _
  have hBl : f b0 ∈ l := mem_line_right _
  have hA'l : g a0 ∈ l' := mem_line_left _
  have hB'l : g b0 ∈ l' := mem_line_right _
  have hlS : LineIn l S := F.lineIn hS (hfS a0) (hfS b0) hAB
  have hl'S : LineIn l' S' := F.lineIn hS' (hgS a0) (hgS b0) hA'B'
  have sym : ∀ i j, i ≠ j → SegCong (g i) (g j) (f i) (f j) := fun i j h =>
    segCong_symm (L := L) (hfi.ne h) (hgi.ne h) (hseg i j h)
  have offA : ∀ k, f k ∉ l → k ≠ a0 := fun k hk e => hk (by rw [e]; exact hAl)
  have offB : ∀ k, f k ∉ l → k ≠ b0 := fun k hk e => hk (by rw [e]; exact hBl)
  -- collinearity with the base line is preserved
  have col : ∀ k, (f k ∈ l ↔ g k ∈ l') := by
    intro k
    by_cases hka : k = a0
    · subst hka; exact ⟨fun _ => hA'l, fun _ => hAl⟩
    by_cases hkb : k = b0
    · subst hkb; exact ⟨fun _ => hB'l, fun _ => hBl⟩
    constructor
    · intro hk
      exact mem_of_collinear (F.collinear_of_segCong' (collinear_of_mem hAl hBl hk) hAB
        (hfi.ne (Ne.symm hkb)) (hfi.ne (Ne.symm hka)) hA'B' (hgi.ne (Ne.symm hkb))
        (hgi.ne (Ne.symm hka)) (hseg a0 b0 hab) (hseg b0 k (Ne.symm hkb))
        (hseg a0 k (Ne.symm hka))) hA'B' hA'l hB'l
    · intro hk
      exact mem_of_collinear (F.collinear_of_segCong' (collinear_of_mem hA'l hB'l hk) hA'B'
        (hgi.ne (Ne.symm hkb)) (hgi.ne (Ne.symm hka)) hAB (hfi.ne (Ne.symm hkb))
        (hfi.ne (Ne.symm hka)) (sym a0 b0 hab) (sym b0 k (Ne.symm hkb))
        (sym a0 k (Ne.symm hka))) hAB hAl hBl
  have ncf : ∀ k, f k ∉ l → ¬Collinear (f b0) (f a0) (f k) := fun k hk hc =>
    hk (mem_of_collinear hc.swap12 hAB hAl hBl)
  have ncg : ∀ k, f k ∉ l → ¬Collinear (g b0) (g a0) (g k) := fun k hk hc =>
    hk ((col k).2 (mem_of_collinear hc.swap12 hA'B' hA'l hB'l))
  -- the half-ray from `A` is preserved for points of the base line
  have rayc : ∀ k, k ≠ a0 → f k ∈ l → (f k ∈ ray (f a0) (f b0) ↔ g k ∈ ray (g a0) (g b0)) := by
    intro k hka hk
    by_cases hkb : k = b0
    · subst hkb
      exact ⟨fun _ => mem_ray_self' (L := L) hA'B'.symm, fun _ => mem_ray_self' (L := L) hAB.symm⟩
    have hk' := (col k).1 hk
    have iff1 : ∀ {O A X : P} {m : L}, O ∈ m → A ∈ m → X ∈ m → A ≠ O → X ≠ O →
        (X ∈ ray O A ↔ ¬Between A O X) := fun hO hA hX hAO hXO =>
      ⟨fun h => h.2.2.2, fun h => (mem_ray_or_between (L := L) (collinear_of_mem hO hA hX) hAO
        hXO).resolve_right h⟩
    rw [iff1 hAl hBl hk hAB.symm (hfi.ne hka), iff1 hA'l hB'l hk' hA'B'.symm (hgi.ne hka)]
    constructor
    · intro h h'
      exact h (between_of_segCong h' (collinear_of_mem hBl hAl hk) hAB.symm (hfi.ne (Ne.symm hka))
        (hfi.ne (Ne.symm hkb)) (sym b0 a0 (Ne.symm hab)) (sym a0 k (Ne.symm hka))
        (sym b0 k (Ne.symm hkb)))
    · intro h h'
      exact h (between_of_segCong h' (collinear_of_mem hB'l hA'l hk') hA'B'.symm
        (hgi.ne (Ne.symm hka)) (hgi.ne (Ne.symm hkb)) (hseg b0 a0 (Ne.symm hab))
        (hseg a0 k (Ne.symm hka)) (hseg b0 k (Ne.symm hkb)))
  -- the angle with the base is preserved for points off the base line
  have angc : ∀ k, (hk : f k ∉ l) → AngCong (f b0) (f a0) (f k) (g b0) (g a0) (g k) := by
    intro k hk
    have hka := offA k hk
    have hkb := offB k hk
    exact (F.sss (fun hc => ncf k hk hc.swap12) (fun hc => ncg k hk hc.swap12) (hseg a0 b0 hab)
      (hseg a0 k (Ne.symm hka)) (hseg b0 k (Ne.symm hkb))).1
  -- the sides of the base line are preserved
  have sidec : ∀ k m, f k ∉ l → f m ∉ l →
      (SameSide l (f k) (f m) ↔ SameSide l' (g k) (g m)) := by
    intro k m hk hm
    have hk' : g k ∉ l' := fun h => hk ((col k).2 h)
    have hm' : g m ∉ l' := fun h => hm ((col m).2 h)
    by_cases hkm : k = m
    · subst hkm; exact ⟨fun _ => sameSide_refl' hk', fun _ => sameSide_refl' hk⟩
    have hka := offA k hk
    have hkb := offB k hk
    have hma := offA m hm
    have hmb := offB m hm
    constructor
    · exact F.sameSide_of_segCong hS hS' (hfS a0) (hfS b0) (hfS k) (hfS m) (hgS a0) (hgS b0)
        (hgS k) (hgS m) hAB hA'B' (fun hc => ncf k hk hc.swap12) (fun hc => ncf m hm hc.swap12)
        (fun hc => ncg k hk hc.swap12) (fun hc => ncg m hm hc.swap12) (hfi.ne hkm) (hgi.ne hkm)
        (hseg a0 b0 hab) (hseg a0 k (Ne.symm hka)) (hseg a0 m (Ne.symm hma))
        (hseg b0 k (Ne.symm hkb)) (hseg b0 m (Ne.symm hmb)) (hseg k m hkm)
    · exact F.sameSide_of_segCong hS' hS (hgS a0) (hgS b0) (hgS k) (hgS m) (hfS a0) (hfS b0)
        (hfS k) (hfS m) hA'B' hAB (fun hc => ncg k hk hc.swap12) (fun hc => ncg m hm hc.swap12)
        (fun hc => ncf k hk hc.swap12) (fun hc => ncf m hm hc.swap12) (hgi.ne hkm) (hfi.ne hkm)
        (sym a0 b0 hab) (sym a0 k (Ne.symm hka)) (sym a0 m (Ne.symm hma))
        (sym b0 k (Ne.symm hkb)) (sym b0 m (Ne.symm hmb)) (sym k m hkm)
  have hQA : Q ≠ f a0 := hQf a0
  by_cases hQl : Q ∈ l
  · -- `Q` on the base line: lay off `AQ` on the corresponding half-ray of `A'B'`
    obtain ⟨Q', hQ'l, hQ'A, hQ'c, hQ'r⟩ : ∃ Q', Q' ∈ l' ∧ Q' ≠ g a0 ∧
        SegCong (f a0) Q (g a0) Q' ∧ (Q ∈ ray (f a0) (f b0) ↔ Q' ∈ ray (g a0) (g b0)) := by
      by_cases hr : Q ∈ ray (f a0) (f b0)
      · obtain ⟨Q', h1, h2⟩ := segCong_layoff (L := L) hQA.symm hA'B'
        exact ⟨Q', mem_of_collinear (collinear_of_mem_ray h1) hA'B' hA'l hB'l, ne_of_mem_ray h1,
          h2, ⟨fun _ => h1, fun _ => hr⟩⟩
      · obtain ⟨Bs, hBs⟩ := exists_beyond (Line := L) hA'B'.symm
        obtain ⟨Q', h1, h2⟩ := segCong_layoff (L := L) hQA.symm (ne23_of_between hBs)
        have hBsl : Bs ∈ l' := mem_right_of_between hBs hB'l hA'l
        have hnr : Q' ∉ ray (g a0) (g b0) := not_mem_ray_of_between
          (between_of_mem_rays hBs (mem_ray_self' (L := L) hA'B'.symm) h1)
        exact ⟨Q', mem_of_collinear (collinear_of_mem_ray h1) (ne23_of_between hBs) hA'l hBsl,
          ne_of_mem_ray h1, h2, ⟨fun h => absurd h hr, fun h => absurd h hnr⟩⟩
    have hQ'S := hl'S Q' hQ'l
    have posc : ∀ i, i ≠ a0 → f i ∈ l →
        (f i ∈ ray (f a0) Q ↔ g i ∈ ray (g a0) Q') := by
      intro i hia hfl
      have p1 := F.ray_iff_of_rays hAl hBl hfl hQl hAB.symm (hfi.ne hia) hQA
      have p2 := F.ray_iff_of_rays hA'l hB'l ((col i).1 hfl) hQ'l hA'B'.symm (hgi.ne hia) hQ'A
      exact p1.trans ((iff_congr (rayc i hia hfl) hQ'r).trans p2.symm)
    refine ⟨Q', hQ'S, ?_, ?_⟩
    · intro i e
      by_cases hia : i = a0
      · subst hia; exact hQ'A e
      by_cases hfl : f i ∈ l
      · have hfr : f i ∈ ray (f a0) Q := (posc i hia hfl).2 (by
          rw [← e]; exact mem_ray_self' (L := L) hQ'A)
        have hc := hQ'c
        rw [e] at hc
        have ee := eq_of_segCong_ray (L := L) (hgi.ne (Ne.symm hia)) hfr
          (mem_ray_self' (L := L) hQA) (sym a0 i (Ne.symm hia))
          (segCong_symm (L := L) hQA.symm (hgi.ne (Ne.symm hia)) hc)
        exact hQf i ee.symm
      · exact hfl ((col i).2 (by rw [← e]; exact hQ'l))
    · intro i
      by_cases hia : i = a0
      · subst hia; exact hQ'c
      by_cases hfl : f i ∈ l
      · exact seg_on_line (hseg a0 i (Ne.symm hia)) hQ'c (hfi.ne hia) hQA (hgi.ne hia) hQ'A
          (collinear_of_mem hAl hQl hfl) (collinear_of_mem hA'l hQ'l ((col i).1 hfl))
          (hQf i).symm (posc i hia hfl)
      · exact segCong_swap (F.seg_line_off hAB hA'B' (collinear_of_mem hAl hBl hQl) hQA
          (collinear_of_mem hA'l hB'l hQ'l) hQ'A hQ'r (ncf i hfl) (ncg i hfl) (angc i hfl) hQ'c
          (hseg a0 i (Ne.symm hia)))
  · -- `Q` off the base line: lay off `∠BAQ` on the side given by the figure
    have nQ : ¬Collinear (f b0) (f a0) Q := fun hc =>
      hQl (mem_of_collinear hc.swap12 hAB hAl hBl)
    obtain ⟨D', hD'S, hD'l, hD'side⟩ : ∃ D', D' ∈ S' ∧ D' ∉ l' ∧
        ∀ c, f c ∉ l → (SameSide l Q (f c) ↔ SameSide l' D' (g c)) := by
      by_cases hC : ∃ c, f c ∉ l
      · obtain ⟨c, hc⟩ := hC
        have hc' : g c ∉ l' := fun h => hc ((col c).2 h)
        have side_c : ∀ D', D' ∈ S' → D' ∉ l' → (SameSide l Q (f c) ↔ SameSide l' D' (g c)) →
            ∀ c2, f c2 ∉ l → (SameSide l Q (f c2) ↔ SameSide l' D' (g c2)) := by
          intro D' hD'S hD'l hD c2 hc2
          have hc2' : g c2 ∉ l' := fun h => hc2 ((col c2).2 h)
          rw [F.ss_iff3 hS hlS hQS (hfS c2) (hfS c) hQl hc2 hc,
            F.ss_iff3 hS' hl'S hD'S (hgS c2) (hgS c) hD'l hc2' hc', sidec c2 c hc2 hc, hD]
        by_cases hQC : SameSide l Q (f c)
        · exact ⟨g c, hgS c, hc', side_c (g c) (hgS c) hc'
            ⟨fun _ => sameSide_refl' hc', fun _ => hQC⟩⟩
        · obtain ⟨D', hD'⟩ := exists_beyond (Line := L) (hgi.ne (offA c hc))
          have hD'S := F.memS_of_between' hS' (hgS c) (hgS a0) hD'
          have ho : OppositeSides l' (g c) D' := opp_of_between_mem hA'l hc' hD'
          exact ⟨D', hD'S, ho.2.1, side_c D' hD'S ho.2.1 ⟨fun h => absurd h hQC,
            fun h => absurd (sameSide_symm' h) (not_sameSide_of_opp' ho)⟩⟩
      · push Not at hC
        obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := F.pl_three S' hS'
        have : ∃ D', D' ∈ S' ∧ D' ∉ l' := by
          by_cases hXl : X ∈ l'
          · by_cases hYl : Y ∈ l'
            · exact ⟨Z, hZ, fun hZl => hn (collinear_of_mem hXl hYl hZl)⟩
            · exact ⟨Y, hY, hYl⟩
          · exact ⟨X, hX, hXl⟩
        obtain ⟨D', h1, h2⟩ := this
        exact ⟨D', h1, h2, fun c hc => absurd (hC c) hc⟩
    obtain ⟨Y0, hY0S, hY0s, hY0c⟩ := F.layoff S' hS' (f b0) (f a0) Q l' (g a0) (g b0) D' nQ hl'S
      hA'l hB'l hA'B'.symm hD'S hD'l
    have hY0A : Y0 ≠ g a0 := ne_of_mem_not_mem hA'l hY0s.1
    obtain ⟨Q', hQ'r, hQ'c⟩ := segCong_layoff (L := L) hQA.symm hY0A.symm
    have hQ'S := F.memS_of_ray hS' (hgS a0) hY0S hQ'r
    have sQ' : SameSide l' Y0 Q' := sameSide_of_ray hA'l hY0s.1 hQ'r
    have hQ'l : Q' ∉ l' := sQ'.2.1
    have hQ'A : Q' ≠ g a0 := ne_of_mem_ray hQ'r
    have nY0 : ¬Collinear (g b0) (g a0) Y0 := fun hc =>
      hY0s.1 (mem_of_collinear hc.swap12 hA'B' hA'l hB'l)
    have nQ' : ¬Collinear (g b0) (g a0) Q' := fun hc =>
      hQ'l (mem_of_collinear hc.swap12 hA'B' hA'l hB'l)
    have aQ : AngCong (f b0) (f a0) Q (g b0) (g a0) Q' := angCong_rays nQ nY0 hY0c
      (mem_ray_self' (L := L) hAB.symm) (mem_ray_self' (L := L) hQA)
      (mem_ray_self' (L := L) hA'B'.symm) hQ'r
    have sDQ : SameSide l' D' Q' := F.ss_trans hS' hl'S hD'S hY0S hQ'S (sameSide_symm' hY0s) sQ'
    have sideQ : ∀ i, f i ∉ l → (SameSide l (f i) Q ↔ SameSide l' (g i) Q') := by
      intro i hi
      have h1 := hD'side i hi
      have h2 : SameSide l' Q' (g i) ↔ SameSide l' D' (g i) :=
        ⟨fun h => F.ss_trans hS' hl'S hD'S hQ'S (hgS i) sDQ h,
          fun h => F.ss_trans hS' hl'S hQ'S hD'S (hgS i) (sameSide_symm' sDQ) h⟩
      exact ⟨fun h => sameSide_symm' (h2.2 (h1.1 (sameSide_symm' h))),
        fun h => sameSide_symm' (h1.2 (h2.1 (sameSide_symm' h)))⟩
    refine ⟨Q', hQ'S, ?_, ?_⟩
    · intro i e
      by_cases hia : i = a0
      · subst hia; exact hQ'A e
      by_cases hfl : f i ∈ l
      · exact hQ'l (by rw [e]; exact (col i).1 hfl)
      · have aQ' := aQ
        rw [e] at aQ'
        have a1 : AngCong (f b0) (f a0) (f i) (f b0) (f a0) Q := angCong_trans (ncf i hfl)
          (ncg i hfl) nQ (angc i hfl) (angCong_symm nQ (ncg i hfl) aQ')
        have hss : SameSide l (f i) Q := (sideQ i hfl).2 (by
          rw [← e]; exact sameSide_refl' hQ'l)
        have er := F.layoff_unique S hS (f b0) (f a0) (f i) l (f a0) (f b0) (f i) Q (ncf i hfl)
          hlS hAl hBl hAB.symm (hfS i) hQS hss (angCong_refl (ncf i hfl)) a1
        have hc := hQ'c
        rw [e] at hc
        have ee := eq_of_segCong_ray (L := L) (hgi.ne (Ne.symm hia))
          (mem_ray_self' (L := L) (hfi.ne hia)) (by rw [er]; exact mem_ray_self' (L := L) hQA)
          (sym a0 i (Ne.symm hia)) (segCong_symm (L := L) hQA.symm (hgi.ne (Ne.symm hia)) hc)
        exact hQf i ee.symm
    · intro i
      by_cases hia : i = a0
      · subst hia; exact hQ'c
      by_cases hfl : f i ∈ l
      · exact F.seg_line_off hAB hA'B' (collinear_of_mem hAl hBl hfl) (hfi.ne hia)
          (collinear_of_mem hA'l hB'l ((col i).1 hfl)) (hgi.ne hia) (rayc i hia hfl) nQ nQ' aQ
          (hseg a0 i (Ne.symm hia)) hQ'c
      · exact F.seg_off_off hS hS' (hfS a0) (hfS b0) (hfS i) hQS (hgS a0) (hgS b0) (hgS i) hQ'S
          hAB hA'B' (ncf i hfl) nQ (ncg i hfl) nQ' (hQf i).symm (hseg a0 i (Ne.symm hia)) hQ'c
          (angc i hfl) aQ (sideQ i hfl)

/-- **Theorem 17, existence**, for any figure (also with fewer than two points). -/
theorem theorem17_exists (hS : F.IsPl S) (hS' : F.IsPl S') {n : ℕ} {f g : Fin n → P}
    (hfS : ∀ i, f i ∈ S) (hgS : ∀ i, g i ∈ S') (hfi : Function.Injective f)
    (hgi : Function.Injective g) (hseg : ∀ i j, i ≠ j → SegCong (f i) (f j) (g i) (g j))
    {Q : P} (hQS : Q ∈ S) (hQf : ∀ i, Q ≠ f i) :
    ∃ Q', Q' ∈ S' ∧ (∀ i, Q' ≠ g i) ∧ ∀ i, SegCong (f i) Q (g i) Q' := by
  by_cases h2 : ∃ a b : Fin n, a ≠ b
  · obtain ⟨a, b, hab⟩ := h2
    exact F.theorem17_two hS hS' hfS hgS hfi hgi hseg hab hQS hQf
  push Not at h2
  obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := F.pl_three S' hS'
  obtain ⟨hXY, -, -⟩ := F.ne hn
  by_cases h1 : Nonempty (Fin n)
  · obtain ⟨a⟩ := h1
    have hD : ∃ D, D ∈ S' ∧ D ≠ g a := by
      by_cases hXa : X = g a
      · exact ⟨Y, hY, fun e => hXY (hXa.trans e.symm)⟩
      · exact ⟨X, hX, hXa⟩
    obtain ⟨D, hDS, hDa⟩ := hD
    obtain ⟨Q', hQ'r, hQ'c⟩ := segCong_layoff (L := L) (hQf a).symm hDa.symm
    refine ⟨Q', F.memS_of_ray hS' (hgS a) hDS hQ'r, fun i => ?_, fun i => ?_⟩
    · rw [h2 i a]; exact ne_of_mem_ray hQ'r
    · rw [h2 i a]; exact hQ'c
  · have he : IsEmpty (Fin n) := not_nonempty_iff.1 h1
    exact ⟨X, hX, fun i => he.elim i, fun i => he.elim i⟩

/-- Congruent segments give congruent angles (Theorem 16): in figures whose corresponding segments
are congruent, the corresponding angles are congruent. -/
theorem angles_of_segs {n : ℕ} {f g : Fin n → P} (hseg : ∀ i j, i ≠ j → SegCong (f i) (f j) (g i) (g j))
    {i j k : Fin n} (h : ¬Collinear (f i) (f j) (f k)) (h' : ¬Collinear (g i) (g j) (g k)) :
    AngCong (f i) (f j) (f k) (g i) (g j) (g k) := by
  obtain ⟨hij, hkj, hik⟩ := F.ne h
  have nij : i ≠ j := fun e => hij (by rw [e])
  have nkj : k ≠ j := fun e => hkj (by rw [e])
  have nik : i ≠ k := fun e => hik (by rw [e])
  exact (F.sss h h' (hseg i j nij) (hseg i k nik) (hseg j k (Ne.symm nkj))).2.1

end Frame

end HilbertFoundations
