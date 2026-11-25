import HilbertFoundations.CongruenceAux3

/-!
# Helper module for `Congruence.lean`: points equidistant from given points

This module contains no unit of Hilbert's text. In a plane frame, with groups I, II, IV:

* `Frame.collinear_of_segCong`: three points whose mutual segments are congruent to those of three
  collinear points are collinear (used for the properties of congruent figures);
* `midpoint_unique`: a segment has at most one point between its extremities equidistant from
  them (IV 1–3);
* `Frame.eq_of_equidistant`: two points of a plane equidistant from three non-collinear points of
  that plane coincide (the uniqueness in Theorem 17);
* `Frame.theorem14_counterexample`: Theorem 14 as printed fails in every plane of the frame.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

section Midpoint

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] {M N X Y : P}
include hS

theorem midpoint_unique_aux (h1 : Between X M Y) (h2 : Between X N Y) (hM : SegCong M X M Y)
    (hN : SegCong N X N Y) (h : Between X M N) : False := by
  have hMN := ne23_of_between h
  have hMX := (ne12_of_between h1).symm
  have hMY := ne23_of_between h1
  have hNX := (ne12_of_between h2).symm
  have hNY := ne23_of_between h2
  have hMNY : Between M N Y := (OrderLin.trans₂ h h2).2
  obtain ⟨N', hN'r, hN'c⟩ := segCong_layoff (L := L) hMN hMX
  have hb : Between M N' X := between_of_segCong_ray hMNY hN'r hN'c
    (segCong_symm (L := L) hMX hMY hM)
  have hN'M : N' ≠ M := ne_of_mem_ray hN'r
  have s : SegCong N' X N Y := segCong_sub hb hMNY (segCong_symm (L := L) hMN hN'M.symm hN'c) hM
  have s2 : SegCong N' X N X := segCong_trans (L := L) (ne23_of_between hb) hNY hNX s
    (segCong_symm (L := L) hNX hNY hN)
  have hXN'N : Between X N' N := (OrderLin.trans₂ (between_symm hb) h).1
  have e := eq_of_segCong_ray' (L := L) (mem_ray_of_between hXN'N)
    (mem_ray_self' (L := L) hNX) (segCong_swap s2)
  exact ne23_of_between hXN'N e

/-- **A segment has only one midpoint** (IV 1–3). -/
theorem midpoint_unique (h1 : Between X M Y) (h2 : Between X N Y) (hM : SegCong M X M Y)
    (hN : SegCong N X N Y) : M = N := by
  have hM' : M ∈ ray X Y := mem_ray_of_between h1
  have hN' : N ∈ ray X Y := mem_ray_of_between h2
  rcases mem_ray_cases (L := L) hM' hN' with e | h | h
  · exact e
  · exact (midpoint_unique_aux h1 h2 hM hN h).elim
  · exact (midpoint_unique_aux h2 h1 hN hM h).elim

end Midpoint

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hT : TriangleCongruence P L] (F : Frame P L) {S : Set P}
  {A B C D O A' B' C' D' O' X Y : P}
include hT F

/-- **Collinearity is carried by the congruence of segments**: if `B` lies between `A` and `C`
and the segments of `A'`, `B'`, `C'` are congruent to those of `A`, `B`, `C`, then `A'`, `B'`,
`C'` are collinear. -/
theorem collinear_of_segCong (hb : Between A B C) (hA'B' : A' ≠ B') (hB'C' : B' ≠ C')
    (hA'C' : A' ≠ C') (h1 : SegCong A B A' B') (h2 : SegCong B C B' C')
    (h3 : SegCong A C A' C') : Collinear A' B' C' := by
  by_contra hn
  obtain ⟨S, hS, hA'S, hB'S, hC'S⟩ := F.exists_pl A' B' C' hn
  obtain ⟨E, hE⟩ := exists_beyond (Line := L) hA'B'
  obtain ⟨R, hRr, hRc⟩ := segCong_layoff (L := L) (ne23_of_between hb) (ne23_of_between hE)
  have hbR : Between A' B' R := between_of_mem_rays hE (mem_ray_self' (L := L) hA'B') hRr
  have h3' : SegCong A C A' R := segCong_add hb hbR h1 hRc
  have hRS := F.memS_of_between' hS hA'S hB'S hbR
  have hA'l : A' ∈ line (Line := L) A' B' hA'B' := mem_line_left _
  have hB'l : B' ∈ line (Line := L) A' B' hA'B' := mem_line_right _
  have hRl : R ∈ line (Line := L) A' B' hA'B' := mem_right_of_between hbR hA'l hB'l
  have hC'l : C' ∉ line (Line := L) A' B' hA'B' := fun hh => hn (collinear_of_mem hA'l hB'l hh)
  have hRC' : R ≠ C' := ne_of_mem_not_mem hRl hC'l |>.symm
  have hA'R : A' ≠ R := ne13_of_between hbR
  have hB'R : B' ≠ R := ne23_of_between hbR
  have nA := nc_of hA'l hRl hA'R hC'l
  have nB := nc_of hB'l hRl hB'R hC'l
  have hAC := ne13_of_between hb
  have hBC := ne23_of_between hb
  have sA : SegCong A' C' A' R := segCong_trans (L := L) hA'C' hAC hA'R
    (segCong_symm (L := L) hAC hA'C' h3) h3'
  have sB : SegCong B' C' B' R := segCong_trans (L := L) hB'C' hBC hB'R
    (segCong_symm (L := L) hBC hB'C' h2) hRc
  -- the isosceles triangles `A'C'R`, `B'C'R`
  have iA := base_angles (L := L) nA.2.1 hA'C' hA'R sA
  have iB := base_angles (L := L) nB.2.1 hB'C' hB'R sB
  -- `∠A'RC' = ∠B'RC'`
  have hB'r : B' ∈ ray R A' := mem_ray_of_between (between_symm hbR)
  have eR : AngCong A' R C' B' R C' := angCong_rays nA.1 nA.1
    (angCong_refl nA.1) (mem_ray_self' (L := L) hA'R) (mem_ray_self' (L := L) hRC'.symm)
    hB'r (mem_ray_self' (L := L) hRC'.symm)
  have t : AngCong A' C' R B' C' R := angCong_trans nA.2.1 nB.1 nB.2.1
    (angCong_trans nA.2.1 nA.1 nB.1 iA eR) (angCong_symm nB.2.1 nB.1 iB)
  have t' : AngCong R C' A' R C' B' := angCong_swap_right nA.2.2.2.2.1 nB.2.1
    (angCong_swap_left nA.2.1 nB.2.1 t)
  have hlS := F.lineIn hS hC'S hRS hRC'.symm
  have hA'm : A' ∉ line (Line := L) C' R hRC'.symm := fun hh =>
    nA.2.1 (collinear_of_mem hh (mem_line_left _) (mem_line_right _))
  have hss : SameSide (line (Line := L) C' R hRC'.symm) A' B' :=
    sameSide_of_ray (mem_line_right _) hA'm hB'r
  have e := F.layoff_unique S hS R C' A' _ C' R A' B' nA.2.2.2.2.1 hlS (mem_line_left _)
    (mem_line_right _) hRC' hA'S hB'S hss (angCong_refl nA.2.2.2.2.1) t'
  have hB'r2 : B' ∈ ray C' A' := by rw [e]; exact mem_ray_self' (L := L) hB'C'
  exact hn (collinear_of_mem_ray hB'r2).perm231

/-- Three distinct collinear points and three points with congruent mutual segments: the latter
are collinear (any order of the first three). -/
theorem collinear_of_segCong' (hc : Collinear A B C) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hA'B' : A' ≠ B') (hB'C' : B' ≠ C') (hA'C' : A' ≠ C') (h1 : SegCong A B A' B')
    (h2 : SegCong B C B' C') (h3 : SegCong A C A' C') : Collinear A' B' C' := by
  rcases between_trichotomy (Line := L) hc hAB hAC hBC with hb | hb | hb
  · -- `A` between `B` and `C`
    have := F.collinear_of_segCong hb hA'B'.symm hA'C' hB'C' (segCong_swap h1) h3 h2
    obtain ⟨g, h1g, h2g, h3g⟩ := this
    exact ⟨g, h2g, h1g, h3g⟩
  · exact F.collinear_of_segCong hb hA'B' hB'C' hA'C' h1 h2 h3
  · have := F.collinear_of_segCong hb hA'C' hB'C'.symm hA'B' h3 (segCong_swap h2) h1
    obtain ⟨g, h1g, h2g, h3g⟩ := this
    exact ⟨g, h1g, h3g, h2g⟩

/-- Two points of the line `PQ` equidistant from `P` and from `Q` coincide. -/
theorem eq_of_equidistant_line {Q R : P} (hPQ : Q ≠ R) (hc : Collinear Q R X) (hXQ : X ≠ Q)
    (hXR : X ≠ R) (hYQ : Y ≠ Q) (hYR : Y ≠ R) (hQ : SegCong Q X Q Y) (hR : SegCong R X R Y) :
    X = Y := by
  have hcY : Collinear Q R Y := F.collinear_of_segCong' hc hPQ hXR.symm hXQ.symm hPQ hYR.symm
    hYQ.symm (segCong_refl (Line := L) hPQ) hR hQ
  by_contra hXY
  obtain ⟨g, hQg, hRg, hXg⟩ := hc
  have hYg : Y ∈ g := mem_of_collinear hcY hPQ hQg hRg
  have bQ : Between X Q Y := by
    rcases mem_ray_or_between (L := L) (collinear_of_mem hQg hXg hYg) hXQ hYQ with h | h
    · exact absurd (eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hXQ) h hQ) hXY
    · exact h
  have bR : Between X R Y := by
    rcases mem_ray_or_between (L := L) (collinear_of_mem hRg hXg hYg) hXR hYR with h | h
    · exact absurd (eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hXR) h hR) hXY
    · exact h
  exact hPQ (midpoint_unique bQ bR hQ hR)

/-- Two points `X ≠ Y` of a plane, off the line `QR` of that plane and equidistant from `Q` and
from `R`, lie on opposite sides of `QR`, and the line `QR` passes through the midpoint of `XY`. -/
theorem midpoint_of_equidistant (hS : F.IsPl S) {Q R : P} (hQS : Q ∈ S) (hRS : R ∈ S)
    (hXS : X ∈ S) (hYS : Y ∈ S) (hQR : Q ≠ R) (hXY : X ≠ Y)
    (hX : X ∉ line (Line := L) Q R hQR) (hY : Y ∉ line (Line := L) Q R hQR)
    (hQ : SegCong Q X Q Y) (hR : SegCong R X R Y) :
    ∃ M, M ∈ line (Line := L) Q R hQR ∧ Between X M Y ∧ SegCong M X M Y := by
  have hQl : Q ∈ line (Line := L) Q R hQR := mem_line_left _
  have hRl : R ∈ line (Line := L) Q R hQR := mem_line_right _
  have nX := nc_of hQl hRl hQR hX
  have nY := nc_of hQl hRl hQR hY
  obtain ⟨a, -, -⟩ := F.sss nX.1 nY.1 (segCong_refl (Line := L) hQR) hQ hR
  -- `a : ∠RQX ≡ ∠RQY`
  have hXQ : X ≠ Q := (F.ne nX.2.2.1).1
  have hYQ : Y ≠ Q := (F.ne nY.2.2.1).1
  rcases sameSide_or_opp' hX hY with hs | ho
  · exfalso
    have e := F.layoff_unique S hS R Q X _ Q R X Y nX.2.2.2.1 (F.lineIn hS hQS hRS hQR) hQl hRl
      hQR.symm hXS hYS hs (angCong_refl nX.2.2.2.1) a
    exact hXY (eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hXQ)
      (by rw [e]; exact mem_ray_self' (L := L) hYQ) hQ)
  · obtain ⟨-, -, M, hMl, hM⟩ := ho
    refine ⟨M, hMl, hM, ?_⟩
    by_cases hMQ : M = Q
    · rw [hMQ]; exact hQ
    have nMX := nc_of hQl hMl (Ne.symm hMQ) hX
    have nMY := nc_of hQl hMl (Ne.symm hMQ) hY
    have aM : AngCong M Q X M Q Y := by
      rcases mem_ray_or_between (L := L) (collinear_of_mem hQl hRl hMl) hQR.symm hMQ with hr | hb
      · exact angCong_rays nX.2.2.2.1 nY.2.2.2.1 a hr (mem_ray_self' (L := L) hXQ) hr
          (mem_ray_self' (L := L) hYQ)
      · have s := F.supp nX.2.2.2.1 nY.2.2.2.1 a hb hb
        exact angCong_swap_right nMX.2.2.2.1 nMY.2.2.1 (angCong_swap_left nMX.2.2.1 nMY.2.2.1 s)
    obtain ⟨s, -, -⟩ := F.sas (A := Q) (B := M) (C := X) (A' := Q) (B' := M) (C' := Y) nMX.1 nMY.1
      (segCong_refl (Line := L) (Ne.symm hMQ)) hQ aM
    exact s

/-- **Two points of a plane equidistant from three non-collinear points of that plane coincide**
(groups I, II, IV). The points `X`, `Y` must differ from `A`, `B`, `C` (segments have distinct
extremities). -/
theorem eq_of_equidistant (hS : F.IsPl S) (hAS : A ∈ S) (hBS : B ∈ S) (hCS : C ∈ S)
    (hXS : X ∈ S) (hYS : Y ∈ S) (hn : ¬Collinear A B C) (hXA : X ≠ A) (hXB : X ≠ B)
    (hXC : X ≠ C) (hYA : Y ≠ A) (hYB : Y ≠ B) (hYC : Y ≠ C) (hA : SegCong A X A Y)
    (hB : SegCong B X B Y) (hC : SegCong C X C Y) : X = Y := by
  obtain ⟨hAB, hCB, hAC⟩ := F.ne (A := A) (O := B) (B := C) hn
  -- `X` or `Y` on a side line
  have online : ∀ {Q R : P}, Q ≠ R → (Collinear Q R X ∨ Collinear Q R Y) → X ≠ Q → X ≠ R →
      Y ≠ Q → Y ≠ R → SegCong Q X Q Y → SegCong R X R Y → X = Y := by
    intro Q R hQR hc h1 h2 h3 h4 sQ sR
    rcases hc with hc | hc
    · exact F.eq_of_equidistant_line hQR hc h1 h2 h3 h4 sQ sR
    · have hQ' := segCong_symm (L := L) h1.symm h3.symm sQ
      have hR' := segCong_symm (L := L) h2.symm h4.symm sR
      exact (F.eq_of_equidistant_line hQR hc h3 h4 h1 h2 hQ' hR').symm
  by_cases cAB : Collinear A B X ∨ Collinear A B Y
  · exact online hAB cAB hXA hXB hYA hYB hA hB
  by_cases cAC : Collinear A C X ∨ Collinear A C Y
  · exact online hAC cAC hXA hXC hYA hYC hA hC
  by_cases cBC : Collinear B C X ∨ Collinear B C Y
  · exact online hCB.symm cBC hXB hXC hYB hYC hB hC
  push Not at cAB cAC cBC
  by_contra hXY
  have nl : ∀ {Q R Z : P} (h : Q ≠ R), ¬Collinear Q R Z → Z ∉ line (Line := L) Q R h :=
    fun h hc hZ => hc (collinear_of_mem (mem_line_left h) (mem_line_right h) hZ)
  obtain ⟨M1, hM1l, hM1, sM1⟩ := F.midpoint_of_equidistant hS hAS hBS hXS hYS hAB hXY
    (nl hAB cAB.1) (nl hAB cAB.2) hA hB
  obtain ⟨M2, hM2l, hM2, sM2⟩ := F.midpoint_of_equidistant hS hAS hCS hXS hYS hAC hXY
    (nl hAC cAC.1) (nl hAC cAC.2) hA hC
  obtain ⟨M3, hM3l, hM3, sM3⟩ := F.midpoint_of_equidistant hS hBS hCS hXS hYS hCB.symm hXY
    (nl hCB.symm cBC.1) (nl hCB.symm cBC.2) hB hC
  have e12 := midpoint_unique hM1 hM2 sM1 sM2
  have e13 := midpoint_unique hM1 hM3 sM1 sM3
  subst e12 e13
  have hlAB : line (Line := L) A B hAB ≠ line A C hAC := fun e =>
    hn (collinear_of_mem (mem_line_left (Line := L) hAB) (mem_line_right hAB)
      (e ▸ mem_line_right (Line := L) hAC))
  have hlAB' : line (Line := L) A B hAB ≠ line B C hCB.symm := fun e =>
    hn (collinear_of_mem (mem_line_left (Line := L) hAB) (mem_line_right hAB)
      (e ▸ mem_line_right (Line := L) hCB.symm))
  have eA := eq_of_mem_of_mem hlAB hM1l hM2l (mem_line_left _) (mem_line_left _)
  have eB := eq_of_mem_of_mem hlAB' hM1l hM3l (mem_line_right _) (mem_line_left _)
  exact hAB (eA.symm.trans eB)

/-- The reflection of `B` in the line `OK`, `K` between `A` and `B`: a point `B'` of the plane on
the side of `A` with `OB ≡ OB'`, `∠KOB ≡ ∠KOB'` and `KB ≡ KB'`. -/
theorem reflect_point (hS : F.IsPl S) (hAS : A ∈ S) (hOS : O ∈ S) (hBS : B ∈ S)
    (h : ¬Collinear A O B) {K : P} (hK : Between A K B) (hKO : K ≠ O) :
    ∃ B', B' ∈ S ∧ SameSide (line (Line := L) O K hKO.symm) B' A ∧ SegCong O B O B' ∧
      AngCong K O B K O B' ∧ SegCong K B K B' := by
  obtain ⟨hAO, hBO, -⟩ := F.ne h
  have hKS := F.memS_of_between hS hAS hBS hK
  have hKi := mem_interior_of_between (L := L) h hK
  have nK := nc_of_interior (L := L) hAO hBO hKi
  have hOl : O ∈ line (Line := L) O K hKO.symm := mem_line_left _
  have hKl : K ∈ line (Line := L) O K hKO.symm := mem_line_right _
  have hAl : A ∉ line (Line := L) O K hKO.symm := fun hh =>
    nK.1 (collinear_of_mem hh hOl hKl)
  have hBl : B ∉ line (Line := L) O K hKO.symm := fun hh =>
    nK.2 (collinear_of_mem hh hOl hKl)
  have nKOB := nc_of hOl hKl hKO.symm hBl
  have hlS := F.lineIn hS hOS hKS hKO.symm
  obtain ⟨X, hXS, hXs, hXc⟩ := F.layoff S hS K O B _ O K A nKOB.2.2.2.1 hlS hOl hKl hKO hAS hAl
  have hXO : X ≠ O := ne_of_mem_not_mem hOl hXs.1
  obtain ⟨B', hB'r, hB'c⟩ := segCong_layoff (L := L) hBO.symm hXO.symm
  have hB'S := F.memS_of_ray hS hOS hXS hB'r
  have s1 : SameSide (line (Line := L) O K hKO.symm) X B' := sameSide_of_ray hOl hXs.1 hB'r
  have hss : SameSide (line (Line := L) O K hKO.symm) B' A :=
    F.ss_trans hS hlS hB'S hXS hAS (sameSide_symm' s1) hXs
  have nX := nc_of hOl hKl hKO.symm hXs.1
  have nB' := nc_of hOl hKl hKO.symm hss.1
  have a : AngCong K O B K O B' := angCong_rays nKOB.2.2.2.1 nX.2.2.2.1 hXc
    (mem_ray_self' (L := L) hKO) (mem_ray_self' (L := L) hBO) (mem_ray_self' (L := L) hKO) hB'r
  obtain ⟨s, -, -⟩ := F.sas (A := O) (B := K) (C := B) (A' := O) (B' := K) (C' := B') nKOB.1
    nB'.1 (segCong_refl (Line := L) hKO.symm) hB'c a
  exact ⟨B', hB'S, hss, hB'c, a, s⟩

/-- The configuration refuting Theorem 14 as printed, once the reflected point is off `OA`. -/
theorem theorem14_counter_aux (hS : F.IsPl S) (hAS : A ∈ S) (hOS : O ∈ S) (hBS : B ∈ S)
    (h : ¬Collinear A O B) {K B' : P} (hK : Between A K B) (hKO : K ≠ O) (hB'S : B' ∈ S)
    (hss : SameSide (line (Line := L) O K hKO.symm) B' A) (hOB : SegCong O B O B')
    (hKOB : AngCong K O B K O B') (hKB : SegCong K B K B') (hn : ¬Collinear A O B') :
    ¬AngCong A O B A O B' := by
  intro c
  obtain ⟨hAO, hBO, hAB⟩ := F.ne h
  have hKS := F.memS_of_between hS hAS hBS hK
  have hKi := mem_interior_of_between (L := L) h hK
  have nK := nc_of_interior (L := L) hAO hBO hKi
  have hOl : O ∈ line (Line := L) O K hKO.symm := mem_line_left _
  have hKl : K ∈ line (Line := L) O K hKO.symm := mem_line_right _
  have hAl : A ∉ line (Line := L) O K hKO.symm := fun hh =>
    nK.1 (collinear_of_mem hh hOl hKl)
  have hBl : B ∉ line (Line := L) O K hKO.symm := fun hh =>
    nK.2 (collinear_of_mem hh hOl hKl)
  have hopp : OppositeSides (line (Line := L) O K hKO.symm) A B :=
    opp_of_between_mem hKl hAl hK
  obtain ⟨-, hB'O, hAB'⟩ := F.ne hn
  obtain ⟨s, -, -⟩ := F.sas (A := O) (B := A) (C := B) (A' := O) (B' := A) (C' := B')
    (fun hh => h hh.swap12) (fun hh => hn hh.swap12) (segCong_refl (Line := L) hAO.symm) hOB c
  have hnOAK : ¬Collinear O A K := fun hh => nK.1 hh.swap12
  have e := F.eq_of_equidistant hS hOS hAS hKS hBS hB'S hnOAK hBO hAB.symm
    (ne_of_mem_not_mem hKl hBl) hB'O hAB'.symm (ne_of_mem_not_mem hKl hss.1) hOB s hKB
  subst e
  exact not_sameSide_of_opp' hopp (sameSide_symm' hss)

/-- **Theorem 14 as printed fails**: in every plane of the frame there are two configurations of
three half-rays from a point `O` with `∠(h, l) ≡ ∠(h', l')` and `∠(k, l) ≡ ∠(k', l')`, all angles
genuine, but `∠(h, k)` not congruent to `∠(h', k')`. Here `h = h' = OA`, `k = OB`, `l = l' = OK`
with `K` between `A` and `B`, and `k' = OB'` is the reflection of `OB` in `OK`. -/
theorem theorem14_counterexample (hS : F.IsPl S) (hAS : A ∈ S) (hOS : O ∈ S) (hBS : B ∈ S)
    (h : ¬Collinear A O B) :
    ∃ K B' : P, K ∈ S ∧ B' ∈ S ∧ ¬Collinear A O K ∧ ¬Collinear B O K ∧ ¬Collinear B' O K ∧
      ¬Collinear A O B' ∧ AngCong A O K A O K ∧ AngCong B O K B' O K ∧
      ¬AngCong A O B A O B' := by
  obtain ⟨hAO, hBO, hAB⟩ := F.ne h
  -- the data of a configuration from a point `K` of the segment `AB`
  have conf : ∀ K : P, Between A K B → ∀ B' : P, (hKO : K ≠ O) → B' ∈ S →
      SameSide (line (Line := L) O K hKO.symm) B' A → SegCong O B O B' →
      AngCong K O B K O B' → SegCong K B K B' → ¬Collinear A O B' →
      ∃ K B' : P, K ∈ S ∧ B' ∈ S ∧ ¬Collinear A O K ∧ ¬Collinear B O K ∧ ¬Collinear B' O K ∧
        ¬Collinear A O B' ∧ AngCong A O K A O K ∧ AngCong B O K B' O K ∧
        ¬AngCong A O B A O B' := by
    intro K hK B' hKO hB'S hss hOB hKOB hKB hn
    have hKi := mem_interior_of_between (L := L) h hK
    have nK := nc_of_interior (L := L) hAO hBO hKi
    have hOl : O ∈ line (Line := L) O K hKO.symm := mem_line_left _
    have hKl : K ∈ line (Line := L) O K hKO.symm := mem_line_right _
    have nB' := nc_of hOl hKl hKO.symm hss.1
    have nKOB : ¬Collinear K O B := fun hh => nK.2 hh.swap13
    refine ⟨K, B', F.memS_of_between hS hAS hBS hK, hB'S, nK.1, nK.2, nB'.2.2.1, hn,
      angCong_refl nK.1, ?_,
      F.theorem14_counter_aux hS hAS hOS hBS h hK hKO hB'S hss hOB hKOB hKB hn⟩
    exact angCong_swap_right nK.2 nB'.2.2.2.1 (angCong_swap_left nKOB nB'.2.2.2.1 hKOB)
  have hKO : ∀ {K : P}, Between A K B → K ≠ O := fun hK e =>
    h (e ▸ collinear_of_between hK)
  obtain ⟨K1, hK1⟩ := exists_between (Line := L) hAB
  obtain ⟨B1, hB1S, hss1, hOB1, hKOB1, hKB1⟩ := F.reflect_point hS hAS hOS hBS h hK1 (hKO hK1)
  by_cases hn1 : Collinear A O B1
  · obtain ⟨K2, hK2⟩ := exists_between (Line := L) (ne23_of_between hK1)
    have hAK2B : Between A K2 B :=
      between_symm (OrderLin.trans₂ (between_symm hK2) (between_symm hK1)).1
    obtain ⟨B2, hB2S, hss2, hOB2, hKOB2, hKB2⟩ := F.reflect_point hS hAS hOS hBS h hAK2B
      (hKO hAK2B)
    by_cases hn2 : Collinear A O B2
    · exfalso
      have hB1O : B1 ≠ O := ne_of_mem_not_mem (mem_line_left _) hss1.1
      have hB2O : B2 ≠ O := ne_of_mem_not_mem (mem_line_left _) hss2.1
      have r1 : B1 ∈ ray O A := mem_ray_of_sameSide (mem_line_left _) hn1.swap12 hB1O
        (sameSide_symm' hss1)
      have r2 : B2 ∈ ray O A := mem_ray_of_sameSide (mem_line_left _) hn2.swap12 hB2O
        (sameSide_symm' hss2)
      have e12 := eq_of_segCong_ray (L := L) hBO.symm r1 r2 hOB1 hOB2
      subst e12
      have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
      have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
      have hK1l := mem_mid_of_between hK1 hAl hBl
      have hK2l := mem_mid_of_between hAK2B hAl hBl
      have hOl : O ∉ line (Line := L) A B hAB := fun hh => h (collinear_of_mem hAl hh hBl)
      have nOK := nc_of hK1l hK2l (ne12_of_between hK2) hOl
      have hK1S := F.memS_of_between hS hAS hBS hK1
      have hK2S := F.memS_of_between hS hAS hBS hAK2B
      have e := F.eq_of_equidistant hS hOS hK1S hK2S hBS hB1S nOK.2.2.1 hBO
        (ne23_of_between hK1).symm (ne23_of_between hAK2B).symm hB1O
        (ne_of_mem_not_mem (mem_line_right _) hss1.1) (ne_of_mem_not_mem (mem_line_right _) hss2.1)
        hOB1 hKB1 hKB2
      subst e
      exact h hn1
    · exact conf K2 hAK2B B2 (hKO hAK2B) hB2S hss2 hOB2 hKOB2 hKB2 hn2
  · exact conf K1 hK1 B1 (hKO hK1) hB1S hss1 hOB1 hKOB1 hKB1 hn1

end Frame

end HilbertFoundations
