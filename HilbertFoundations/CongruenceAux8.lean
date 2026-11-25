import HilbertFoundations.CongruenceAux7

/-!
# Helper module for `Congruence.lean`: perpendicular bisectors and the circle through three points

This module contains no unit of Hilbert's text. In a plane frame with groups I, II, IV:

* `RightAng A O B`: `∠AOB` is congruent to its supplementary angle along the side `OB`; it is
  invariant under the change of points on the sides, under exchange of the sides, and under
  congruence (`rt_side`, `rt_arm`, `rt_symm`, `rt_congr`), and all such angles are congruent
  (Theorem 15, `rt_cong`);
* `Frame.iso_converse`: equal base angles give equal sides;
* `Frame.apex`, `Frame.bisector`: points equidistant from `A` and `B` on both sides of `AB`;
* `Frame.equidistant_of_mem`: the points of the line through two such points are equidistant;

and with the uniqueness of parallels, `Frame.circumcenter`: three non-collinear points of a plane are
equidistant from some point (the possibility of a circle through three points, § 7).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

/-- `∠AOB` is a right angle, congruent to its supplementary angle along the side `OB`. -/
def RightAng {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P] (A O B : P) :
    Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between B O C ∧ AngCong A O B A O C

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hT : TriangleCongruence P L] (F : Frame P L) {S : Set P}
  {A B C D O Q R X Y A' B' O' : P}
include hT F

/-- A right angle stays right when the point on the side `OB` moves along its line. -/
theorem rt_side (h : RightAng (L := L) A O B) (hB2 : B' ≠ O) (hc : Collinear (Line := L) O B B') :
    RightAng (L := L) A O B' := by
  obtain ⟨hn, C, hC, hc'⟩ := h
  obtain ⟨hAO, hBO, -⟩ := F.ne hn
  have hCO : C ≠ O := (ne23_of_between hC).symm
  have nC : ¬Collinear (Line := L) A O C := not_collinear_swap (not_collinear_of_between
    (not_collinear_swap hn) hC)
  obtain ⟨g, hOg, hBg, hB'g⟩ := hc
  have hCg : C ∈ g := mem_right_of_between hC hBg hOg
  have nB' : ¬Collinear (Line := L) A O B' := fun hh =>
    hn (by
      obtain ⟨g', h1, h2, h3⟩ := hh
      have e : g' = g := line_unique hB2.symm h2 h3 hOg hB'g
      rw [e] at h1
      exact ⟨g, h1, hOg, hBg⟩)
  rcases mem_ray_or_between (L := L) (collinear_of_mem hOg hBg hB'g) hBO hB2 with hr | hb
  · refine ⟨nB', C, between_of_mem_rays hC hr (mem_ray_self' (L := L) hCO), ?_⟩
    exact angCong_rays hn nC hc' (mem_ray_self' (L := L) hAO) hr (mem_ray_self' (L := L) hAO)
      (mem_ray_self' (L := L) hCO)
  · have hr : B' ∈ ray O C := by
      have := (F.ray_iff_of_rays hOg hBg hB'g hCg hBO hB2 hCO).2
      exact this ⟨fun h => absurd h (not_mem_ray_of_between hb),
        fun h => absurd h (not_mem_ray_of_between hC)⟩
    refine ⟨nB', B, between_symm hb, ?_⟩
    exact angCong_symm hn nB' (angCong_rays hn nC hc' (mem_ray_self' (L := L) hAO)
      (mem_ray_self' (L := L) hBO) (mem_ray_self' (L := L) hAO) hr)

/-- A right angle stays right under exchange of its sides. -/
theorem rt_symm (h : RightAng (L := L) A O B) : RightAng (L := L) B O A := by
  obtain ⟨hn, C, hC, hc⟩ := h
  obtain ⟨hAO, -, -⟩ := F.ne hn
  obtain ⟨D, hD⟩ := exists_beyond (Line := L) hAO
  have nAOC : ¬Collinear (Line := L) A O C := not_collinear_swap (not_collinear_of_between
    (not_collinear_swap hn) hC)
  have nCOA : ¬Collinear (Line := L) C O A := not_collinear_swap nAOC
  have nBOD : ¬Collinear (Line := L) B O D := not_collinear_swap (not_collinear_of_between hn hD)
  have v : AngCong B O D C O A := F.vertical nBOD hC (between_symm hD)
  refine ⟨not_collinear_swap hn, D, hD, ?_⟩
  have t : AngCong B O A C O A := angCong_swap_left hn nCOA
    (angCong_swap_right hn nAOC hc)
  exact angCong_trans (not_collinear_swap hn) nCOA nBOD t (angCong_symm nBOD nCOA v)

/-- A right angle stays right when the point on the side `OA` moves along its line. -/
theorem rt_arm (h : RightAng (L := L) A O B) (hA2 : A' ≠ O) (hc : Collinear (Line := L) O A A') :
    RightAng (L := L) A' O B :=
  F.rt_symm (F.rt_side (F.rt_symm h) hA2 hc)

/-- An angle congruent to a right angle is a right angle (Theorem 12). -/
theorem rt_congr (h : RightAng (L := L) A O B) (h' : ¬Collinear (Line := L) A' O' B')
    (hc : AngCong A O B A' O' B') : RightAng (L := L) A' O' B' := by
  obtain ⟨hn, C, hC, hc0⟩ := h
  obtain ⟨-, hB'O, -⟩ := F.ne h'
  obtain ⟨C', hC'⟩ := exists_beyond (Line := L) hB'O
  have nAOC : ¬Collinear (Line := L) A O C := not_collinear_swap (not_collinear_of_between
    (not_collinear_swap hn) hC)
  have nAOC' : ¬Collinear (Line := L) A' O' C' := not_collinear_swap (not_collinear_of_between
    (not_collinear_swap h') hC')
  have s : AngCong A O C A' O' C' := F.supp (not_collinear_swap hn) (not_collinear_swap h')
    (angCong_swap_left hn (not_collinear_swap h') (angCong_swap_right hn h' hc)) hC hC'
  refine ⟨h', C', hC', ?_⟩
  exact angCong_trans h' hn nAOC' (angCong_symm hn h' hc) (angCong_trans hn nAOC nAOC' hc0 s)

/-- **All right angles are congruent** (Theorem 15). -/
theorem rt_cong (h : RightAng (L := L) A O B) (h' : RightAng (L := L) A' O' B') : AngCong A O B A' O' B' := by
  have h1 := F.rt_symm h
  have h2 := F.rt_symm h'
  obtain ⟨hn, C, hC, hc⟩ := h1
  obtain ⟨hn', C', hC', hc'⟩ := h2
  have nC : ¬Collinear (Line := L) C O B := not_collinear_of_between (not_collinear_swap hn) hC
  have nC' : ¬Collinear (Line := L) C' O' B' := not_collinear_of_between (not_collinear_swap hn')
    hC'
  have r := F.right_angles (B := A) (A := O) (C := C) (D := B) (B' := A') (A' := O') (C' := C')
    (D' := B') hC (not_collinear_swap hn)
    (angCong_swap_right (not_collinear_swap hn) (not_collinear_swap nC)
      (angCong_swap_left hn (not_collinear_swap nC) hc))
    hC' (not_collinear_swap hn')
    (angCong_swap_right (not_collinear_swap hn') (not_collinear_swap nC')
      (angCong_swap_left hn' (not_collinear_swap nC') hc'))
  exact r

/-- **Equal base angles give equal sides** (Theorem 11). -/
theorem iso_converse (h : ¬Collinear (Line := L) Q A B) (hc : AngCong Q A B Q B A) :
    SegCong Q A Q B := by
  have n1 : ¬Collinear (Line := L) A B Q := fun hh => h hh.perm312
  have n2 : ¬Collinear (Line := L) B A Q := fun hh => h hh.swap13
  have n3 : ¬Collinear (Line := L) Q B A := fun hh => h hh.swap23
  have hA : AngCong B A Q A B Q := angCong_swap_right n2 n3 (angCong_swap_left h n3 hc)
  have hB : AngCong A B Q B A Q := angCong_symm n2 n1 hA
  have hAB : A ≠ B := (F.ne n1).1
  exact segCong_swap (L := L) (F.asa (A := A) (B := B) (C := Q) (A' := B) (B' := A) (C' := Q) n1
    n2 (segCong_swap_right (Line := L) (segCong_refl (Line := L) hAB)) hA hB).1

/-- **An isosceles apex on a given side**: for `A ≠ B` and `D` off `AB` (in a plane `S`) there is a
point `Q` of `S` on the side of `D` with `QA ≡ QB`. -/
theorem apex (hS : F.IsPl S) (hAS : A ∈ S) (hBS : B ∈ S) (hDS : D ∈ S) (hAB : A ≠ B)
    (hD : D ∉ line (Line := L) A B hAB) :
    ∃ Q, Q ∈ S ∧ SameSide (line (Line := L) A B hAB) Q D ∧ SegCong Q A Q B := by
  set l := line (Line := L) A B hAB
  have hAl : A ∈ l := mem_line_left _
  have hBl : B ∈ l := mem_line_right _
  have hlS := F.lineIn hS hAS hBS hAB
  have nD := nc_of hAl hBl hAB hD
  -- `nD.2.2.2.1 : ¬Col B A D`, `nD.1 : ¬Col A B D`
  obtain ⟨Y, hYS, hYs, hYc⟩ := F.layoff S hS B A D l B A D nD.2.2.2.1 hlS hBl hAl hAB hDS hD
  -- `hYc : ∠BAD ≡ ∠ABY`
  have nY := nc_of hAl hBl hAB hYs.1
  have hDA : D ≠ A := ne_of_mem_not_mem hAl hD
  have hDB : D ≠ B := ne_of_mem_not_mem hBl hD
  have hYB : Y ≠ B := ne_of_mem_not_mem hBl hYs.1
  have el : line (Line := L) B A hAB.symm = l := line_comm hAB
  by_cases hcol : Collinear (Line := L) Y B D
  · -- the half-ray `BY` is `BD`: `D` itself is the apex
    have hr : Y ∈ ray B D := mem_ray_of_sameSide hBl (by
      obtain ⟨g, h1, h2, h3⟩ := hcol; exact ⟨g, h2, h3, h1⟩) hYB (sameSide_symm' hYs)
    have a : AngCong B A D A B D := angCong_rays nD.2.2.2.1 nY.1 hYc
      (mem_ray_self' (L := L) hAB.symm) (mem_ray_self' (L := L) hDA) (mem_ray_self' (L := L) hAB)
      (mem_ray_comm hr)
    have a' : AngCong D A B D B A := angCong_swap_right nD.2.2.1 nD.1
      (angCong_swap_left nD.2.2.2.1 nD.1 a)
    exact ⟨D, hDS, sameSide_refl' hD, F.iso_converse nD.2.2.1 a'⟩
  · have hs' : SameSide (line (Line := L) B A hAB.symm) Y D := by rw [el]; exact hYs
    rcases F.interior_or_interior hS hBS hYS hDS hAS nY.2.2.2.2.2 hAB hs' hcol with hi | hi
    · -- `D` within `∠YBA`: transfer `∠ABD` to `A`
      have hi' : D ∈ Interior (Line := L) A B Y := by rw [interior_swap]; exact hi
      have hc : AngCong A B Y B A D := angCong_symm nD.2.2.2.1 nY.1 hYc
      obtain ⟨X', hX'S, hX'i, a1, -⟩ := F.interior_transfer hS hBS hAS hYS hDS nY.1
        nD.2.2.2.1 hc hi'
      have hX'S' := hX'S S hS hAS hBS hDS
      obtain ⟨Qp, hQp, hQpr⟩ := F.crossbar hS hAS hBS hDS hX'S' nD.2.2.2.1 hX'i
      have hQpl : Qp ∉ l := (sameSide_of_between_mem' hBl hD hQp).1
      have nQ := nc_of hAl hBl hAB hQpl
      have a2 : AngCong A B Qp B A Qp := angCong_rays nD.1 (nc_of_interior (L := L) hAB.symm
        hDA hX'i).1 a1 (mem_ray_self' (L := L) hAB) (mem_ray_of_between hQp) (mem_ray_self' (L := L) hAB.symm)
        hQpr
      have a3 : AngCong Qp A B Qp B A := angCong_swap_right nQ.2.2.1 nQ.1
        (angCong_swap_left nQ.2.2.2.1 nQ.1 (angCong_symm nQ.1 nQ.2.2.2.1 a2))
      exact ⟨Qp, F.memS_of_between hS hBS hDS hQp, sameSide_of_between_mem' hBl hD hQp,
        F.iso_converse nQ.2.2.1 a3⟩
    · -- `Y` within `∠DBA`: the half-ray `BY` meets `AD`
      have hi' : Y ∈ Interior (Line := L) A B D := by rw [interior_swap]; exact hi
      obtain ⟨Qp, hQp, hQpr⟩ := F.crossbar hS hBS hAS hDS hYS nD.1 hi'
      have hQpl : Qp ∉ l := (sameSide_of_between_mem' hAl hD hQp).1
      have nQ := nc_of hAl hBl hAB hQpl
      have a2 : AngCong B A Qp A B Qp := angCong_rays nD.2.2.2.1 nY.1 hYc
        (mem_ray_self' (L := L) hAB.symm) (mem_ray_of_between hQp) (mem_ray_self' (L := L) hAB)
        hQpr
      have a3 : AngCong Qp A B Qp B A := angCong_swap_right nQ.2.2.1 nQ.1
        (angCong_swap_left nQ.2.2.2.1 nQ.1 a2)
      exact ⟨Qp, F.memS_of_between hS hAS hDS hQp, sameSide_of_between_mem' hAl hD hQp,
        F.iso_converse nQ.2.2.1 a3⟩

/-- **Two apexes on opposite sides**: for `A ≠ B` in a plane `S` there are points `Q`, `R` of `S`
on different sides of `AB` with `QA ≡ QB` and `RA ≡ RB`. -/
theorem bisector (hS : F.IsPl S) (hAS : A ∈ S) (hBS : B ∈ S) (hAB : A ≠ B) :
    ∃ Q R, Q ∈ S ∧ R ∈ S ∧ OppositeSides (line (Line := L) A B hAB) Q R ∧ SegCong Q A Q B ∧
      SegCong R A R B := by
  set l := line (Line := L) A B hAB
  have hAl : A ∈ l := mem_line_left _
  have hBl : B ∈ l := mem_line_right _
  have hlS := F.lineIn hS hAS hBS hAB
  obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := F.pl_three S hS
  have hD : ∃ D, D ∈ S ∧ D ∉ l := by
    by_cases hXl : X ∈ l
    · by_cases hYl : Y ∈ l
      · exact ⟨Z, hZ, fun hZl => hn (collinear_of_mem hXl hYl hZl)⟩
      · exact ⟨Y, hY, hYl⟩
    · exact ⟨X, hX, hXl⟩
  obtain ⟨D, hDS, hDl⟩ := hD
  obtain ⟨Ds, hDs⟩ := exists_beyond (Line := L) (ne_of_mem_not_mem hAl hDl)
  have hDsS := F.memS_of_between' hS hDS hAS hDs
  have oD : OppositeSides l D Ds := opp_of_between_mem hAl hDl hDs
  obtain ⟨Q, hQS, hQs, hQc⟩ := F.apex hS hAS hBS hDS hAB hDl
  obtain ⟨R, hRS, hRs, hRc⟩ := F.apex hS hAS hBS hDsS hAB oD.2.1
  refine ⟨Q, R, hQS, hRS, ?_, hQc, hRc⟩
  exact F.opp_of_ss_opp hS hlS hQS hDS hRS hQs
    (opp_symm' (F.opp_of_ss_opp hS hlS hRS hDsS hDS hRs (opp_symm' oD)))

/-- `A` and `B` do not lie on the line through two points `Q`, `R` (on different sides of `AB`)
equidistant from them. -/
theorem not_mem_bisector (hAB : A ≠ B)
    (ho : OppositeSides (line (Line := L) A B hAB) Q R) (hQ : SegCong Q A Q B)
    (hR : SegCong R A R B) (hQR : Q ≠ R) :
    A ∉ line (Line := L) Q R hQR ∧ B ∉ line (Line := L) Q R hQR := by
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hQA := ne_of_mem_not_mem hAl ho.1
  have hQB := ne_of_mem_not_mem hBl ho.1
  have hRA := ne_of_mem_not_mem hAl ho.2.1
  have hRB := ne_of_mem_not_mem hBl ho.2.1
  have hQl : Q ∈ line (Line := L) Q R hQR := mem_line_left _
  have hRl : R ∈ line (Line := L) Q R hQR := mem_line_right _
  have key : A ∈ line (Line := L) Q R hQR → B ∈ line (Line := L) Q R hQR → False := fun hA hB =>
    ho.1 (by rw [line_unique hAB hA hB hAl hBl] at hQl; exact hQl)
  constructor
  · intro hA
    apply key hA
    have c := F.collinear_of_segCong' (collinear_of_mem hQl hRl hA) hQR hRA hQA hQR
      hRB hQB (segCong_refl (Line := L) hQR) hR hQ
    exact mem_of_collinear c hQR hQl hRl
  · intro hB
    apply key _ hB
    have hR' := segCong_symm (L := L) hRA hRB hR
    have hQ' := segCong_symm (L := L) hQA hQB hQ
    have c := F.collinear_of_segCong' (collinear_of_mem hQl hRl hB) hQR hRB hQB hQR
      hRA hQA (segCong_refl (Line := L) hQR) hR' hQ'
    exact mem_of_collinear c hQR hQl hRl

/-- **The points of the perpendicular bisector are equidistant**: every point of the line through
two points `Q ≠ R` equidistant from `A` and `B` (both off that line) is equidistant from them. -/
theorem equidistant_of_mem (hQR : Q ≠ R) (hA : A ∉ line (Line := L) Q R hQR)
    (hB : B ∉ line (Line := L) Q R hQR) (hQ : SegCong Q A Q B) (hR : SegCong R A R B)
    (hX : X ∈ line (Line := L) Q R hQR) : SegCong X A X B := by
  have hQl : Q ∈ line (Line := L) Q R hQR := mem_line_left _
  have hRl : R ∈ line (Line := L) Q R hQR := mem_line_right _
  have nA := nc_of hQl hRl hQR hA
  have nB := nc_of hQl hRl hQR hB
  obtain ⟨a, -, -⟩ := F.sss nA.1 nB.1 (segCong_refl (Line := L) hQR) hQ hR
  -- `a : ∠RQA ≡ ∠RQB`
  by_cases hXQ : X = Q
  · rw [hXQ]; exact hQ
  have nXA := nc_of hQl hX (Ne.symm hXQ) hA
  have nXB := nc_of hQl hX (Ne.symm hXQ) hB
  have hAQ := ne_of_mem_not_mem hQl hA
  have hBQ := ne_of_mem_not_mem hQl hB
  have aX : AngCong X Q A X Q B := by
    rcases mem_ray_or_between (L := L) (collinear_of_mem hQl hRl hX) hQR.symm hXQ with hr | hb
    · exact angCong_rays nA.2.2.2.1 nB.2.2.2.1 a hr (mem_ray_self' (L := L) hAQ) hr
        (mem_ray_self' (L := L) hBQ)
    · have s := F.supp nA.2.2.2.1 nB.2.2.2.1 a hb hb
      exact angCong_swap_right nXA.2.2.2.1 nXB.2.2.1 (angCong_swap_left nXA.2.2.1 nXB.2.2.1 s)
  exact (F.sas (A := Q) (B := X) (C := A) (A' := Q) (B' := X) (C' := B) nXA.1 nXB.1
    (segCong_refl (Line := L) (Ne.symm hXQ)) hQ aX).1

/-- The midpoint `M` of `AB` on the line through the apexes, with the right angle `∠QMA`. -/
theorem midpoint_rt (hS : F.IsPl S) (hQS : Q ∈ S) (hRS : R ∈ S) (hAS : A ∈ S) (hBS : B ∈ S)
    (hAB : A ≠ B) (ho : OppositeSides (line (Line := L) A B hAB) Q R) (hQ : SegCong Q A Q B)
    (hR : SegCong R A R B) (hQR : Q ≠ R) :
    ∃ M, M ∈ line (Line := L) Q R hQR ∧ Between A M B ∧ RightAng (L := L) Q M A := by
  obtain ⟨hAm, hBm⟩ := F.not_mem_bisector hAB ho hQ hR hQR
  obtain ⟨M, hMm, hM, sM⟩ := F.midpoint_of_equidistant hS hQS hRS hAS hBS hQR hAB hAm hBm hQ hR
  have hMt : M ∈ line (Line := L) A B hAB := mem_mid_of_between hM (mem_line_left _)
    (mem_line_right _)
  have hQM : Q ≠ M := ne_of_mem_not_mem hMt ho.1
  have hQl : Q ∈ line (Line := L) Q R hQR := mem_line_left _
  have nA := nc_of hMm hQl hQM.symm hAm
  have nB := nc_of hMm hQl hQM.symm hBm
  obtain ⟨a, -, -⟩ := F.sss nA.1 nB.1 (segCong_refl (Line := L) hQM.symm) sM hQ
  exact ⟨M, hMm, hM, nA.2.2.2.1, B, hM, a⟩

/-- **The circle through three points** (§ 7): three non-collinear points of a plane are equidistant
from some point of the plane (groups I–IV of the plane, the uniqueness of parallels being used). -/
theorem circumcenter (hS : F.IsPl S) (hpar : F.ParUnique) (hAS : A ∈ S) (hBS : B ∈ S)
    (hCS : C ∈ S) (h : ¬Collinear (Line := L) A B C) :
    ∃ O, O ∈ S ∧ O ≠ A ∧ O ≠ B ∧ O ≠ C ∧ SegCong O A O B ∧ SegCong O A O C := by
  obtain ⟨hAB, hCB, hAC⟩ := F.ne h
  have hBC : B ≠ C := hCB.symm
  obtain ⟨Q1, R1, hQ1S, hR1S, ho1, hQ1, hR1⟩ := F.bisector hS hAS hBS hAB
  obtain ⟨Q2, R2, hQ2S, hR2S, ho2, hQ2, hR2⟩ := F.bisector hS hBS hCS hBC
  have hQR1 : Q1 ≠ R1 := by obtain ⟨-, -, Z, -, hZ⟩ := ho1; exact ne13_of_between hZ
  have hQR2 : Q2 ≠ R2 := by obtain ⟨-, -, Z, -, hZ⟩ := ho2; exact ne13_of_between hZ
  set m1 := line (Line := L) Q1 R1 hQR1
  set m2 := line (Line := L) Q2 R2 hQR2
  obtain ⟨hAm1, hBm1⟩ := F.not_mem_bisector hAB ho1 hQ1 hR1 hQR1
  obtain ⟨hBm2, hCm2⟩ := F.not_mem_bisector hBC ho2 hQ2 hR2 hQR2
  have hm1S : LineIn m1 S := F.lineIn hS hQ1S hR1S hQR1
  have hm2S : LineIn m2 S := F.lineIn hS hQ2S hR2S hQR2
  by_cases hm : Meets (Point := P) m1 m2
  · obtain ⟨O, hO1, hO2⟩ := hm
    have e1 := F.equidistant_of_mem hQR1 hAm1 hBm1 hQ1 hR1 hO1
    have e2 := F.equidistant_of_mem hQR2 hBm2 hCm2 hQ2 hR2 hO2
    have hOA : O ≠ A := (ne_of_mem_not_mem hO1 hAm1).symm
    have hOB : O ≠ B := (ne_of_mem_not_mem hO1 hBm1).symm
    have hOC : O ≠ C := (ne_of_mem_not_mem hO2 hCm2).symm
    exact ⟨O, hm1S O hO1, hOA, hOB, hOC, e1, segCong_trans (L := L) hOA hOB hOC e1 e2⟩
  · exfalso
    set t := line (Line := L) A B hAB
    set u := line (Line := L) B C hBC
    have hAt : A ∈ t := mem_line_left _
    have hBt : B ∈ t := mem_line_right _
    have hBu : B ∈ u := mem_line_left _
    have hCu : C ∈ u := mem_line_right _
    have htS : LineIn t S := F.lineIn hS hAS hBS hAB
    have huS : LineIn u S := F.lineIn hS hBS hCS hBC
    have hCt : C ∉ t := fun hh => h (collinear_of_mem hAt hBt hh)
    obtain ⟨M1, hM1m, hM1, rA⟩ := F.midpoint_rt hS hQ1S hR1S hAS hBS hAB ho1 hQ1 hR1 hQR1
    obtain ⟨M2, hM2m, hM2, rB⟩ := F.midpoint_rt hS hQ2S hR2S hBS hCS hBC ho2 hQ2 hR2 hQR2
    have hM1t : M1 ∈ t := mem_mid_of_between hM1 hAt hBt
    have hM2u : M2 ∈ u := mem_mid_of_between hM2 hBu hCu
    have hM1m2 : M1 ∉ m2 := fun hh => hm ⟨M1, hM1m, hh⟩
    -- the line `AB` meets `m2` (uniqueness of parallels)
    obtain ⟨X, hXt, hXm2⟩ : Meets (Point := P) t m2 := by
      by_contra hno
      have e := hpar S hS m2 m1 t M1 hm2S hm1S htS hM1m2 hM1m hM1t hm hno
      exact ho1.1 (by rw [← e]; exact mem_line_left _)
    have hM1X : M1 ≠ X := fun e => hM1m2 (by rw [e]; exact hXm2)
    have et : line (Line := L) M1 X hM1X = t := (eq_line hM1X hM1t hXt).symm
    -- a point of `m2` on the other side of `AB` than `Q1`
    obtain ⟨Qb, hQbm, hQbo⟩ : ∃ Qb, Qb ∈ m2 ∧ OppositeSides t Q1 Qb := by
      have hY : ∃ Y, Y ∈ m2 ∧ Y ≠ X := by
        by_cases hq : Q2 = X
        · exact ⟨R2, mem_line_right _, fun e => hQR2 (hq.trans e.symm)⟩
        · exact ⟨Q2, mem_line_left _, hq⟩
      obtain ⟨Y, hYm, hYX⟩ := hY
      have hYt : Y ∉ t := fun hh => hM1m2 (by
        rw [line_unique hYX hYm hXm2 hh hXt]; exact hM1t)
      rcases sameSide_or_opp' ho1.1 hYt with hs | ho
      · obtain ⟨Ys, hYs⟩ := exists_beyond (Line := L) hYX
        have hYsm : Ys ∈ m2 := mem_right_of_between hYs hYm hXm2
        exact ⟨Ys, hYsm, F.opp_of_ss_opp hS htS hQ1S (hm2S Y hYm) (hm2S Ys hYsm) hs
          (opp_of_between_mem hXt hYt hYs)⟩
      · exact ⟨Y, hYm, ho⟩
    have alt := F.alternate_of_parallel hS hpar hm1S hm2S hm hM1m hXm2 hM1X (mem_line_left _)
      hQbm (by rw [et]; exact hQbo)
    have r1 : RightAng (L := L) Q1 M1 X := F.rt_side rA hM1X.symm (collinear_of_mem hM1t hAt hXt)
    have nQb := nc_of hXt hM1t hM1X.symm hQbo.2.1
    have r2 : RightAng (L := L) Qb X M1 := F.rt_congr r1 nQb.2.2.1 alt
    by_cases hXM2 : X = M2
    · have hM2B : M2 ≠ B := (ne12_of_between hM2).symm
      have hM2t : M2 ∈ t := by rw [← hXM2]; exact hXt
      have e := line_unique hM2B hM2t hBt hM2u hBu
      exact hCt (by rw [e]; exact hCu)
    · have oBC : OppositeSides m2 B C := opp_of_between_mem hM2m hBm2 hM2
      obtain ⟨Qc, hQcu, hQco⟩ : ∃ Qc, Qc ∈ u ∧ OppositeSides m2 M1 Qc := by
        rcases sameSide_or_opp' hM1m2 hBm2 with hs | ho
        · exact ⟨C, hCu, F.opp_of_ss_opp hS hm2S (htS M1 hM1t) hBS hCS hs oBC⟩
        · exact ⟨B, hBu, ho⟩
      have hQcM2 : Qc ≠ M2 := ne_of_mem_not_mem hM2m hQco.2.1
      have rM1 : RightAng (L := L) M1 X M2 := F.rt_side (F.rt_symm r2) (Ne.symm hXM2)
        (collinear_of_mem hXm2 hQbm hM2m)
      have rQ : RightAng (L := L) Qc M2 X := F.rt_side (F.rt_arm (F.rt_symm rB) hQcM2
        (collinear_of_mem hM2u hBu hQcu)) hXM2 (collinear_of_mem hM2m (mem_line_left _) hXm2)
      have c := F.rt_cong rM1 rQ
      have em : line (Line := L) X M2 hXM2 = m2 := (eq_line hXM2 hXm2 hM2m).symm
      have hpar' := F.parallel_of_alternate hS htS huS hXt hM2u hXM2 hM1t hQcu
        (by rw [em]; exact hQco) c
      exact hpar' ⟨B, hBt, hBu⟩

end Frame

end HilbertFoundations
