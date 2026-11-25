import HilbertFoundations.CongruenceAux4

/-!
# Helper module for `Congruence.lean`: parallels (Theorems 19, 20) and comparison of angles

This module contains no unit of Hilbert's text. In a plane frame:

* `Frame.ParUnique`: the uniqueness half of the axiom of parallels inside the planes of the frame
  (from `PlaneParallels`, `SpaceParallels`: `parUnique_plane`, `parUnique_space`);
* `Frame.parallel_of_alternate`, `Frame.parallel_of_corresponding` (converse of Theorem 19, without
  the axiom of parallels), `Frame.alternate_of_parallel`, `Frame.corresponding_of_parallel`
  (Theorem 19), `Frame.angle_sum` (Theorem 20);
* `Frame.angLt_congr`: "less than" between angles is compatible with congruence.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P]

/-- The uniqueness of the parallel (Axiom III, second assertion) inside each plane of the frame. -/
def ParUnique (F : Frame P L) : Prop :=
  ∀ S, F.IsPl S → ∀ (l m n : L) (X : P), LineIn l S → LineIn m S → LineIn n S → X ∉ l → X ∈ m →
    X ∈ n → ¬Meets (Point := P) m l → ¬Meets (Point := P) n l → m = n

end Frame

theorem parUnique_plane {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P]
    [PlaneAngleCongruence P L] [PlaneParallels P L] (hl : ∀ X : P, ∃ l : L, X ∈ l) :
    (planeFrame hl).ParUnique := by
  intro S _ l m n X _ _ _ hX hm hn hml hnl
  exact (exists_unique_parallel hX).unique ⟨hm, hml⟩ ⟨hn, hnl⟩

theorem parUnique_space {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [HasAngCong P] [SpaceAngleCongruence P L Pl] [SpaceParallels P L Pl] :
    (spaceFrame (P := P) (L := L) (Pl := Pl)).ParUnique := by
  intro S hS l m n X hl hm' hn' hX hm hn hml hnl
  obtain ⟨α, rfl⟩ := hS
  have hXα : X ∈ α := hm' X hm
  exact (SpaceParallels.ax_III (Line := L) α l X hl hXα hX).unique ⟨hm', hm, hml⟩ ⟨hn', hn, hnl⟩

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hT : TriangleCongruence P L] (F : Frame P L) {S : Set P}
  {A B C D O A' B' C' D' O' X Y Z W Q R : P}
include hT F

/-- The case of the converse of Theorem 19 in which the common point lies on the side of `Pa`. -/
theorem no_meet_aux (hS : F.IsPl S) {a b : L} (ha : LineIn a S) (hb : LineIn b S) {Pa Qb : P}
    (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb) (hc : AngCong Pa A B Qb B A)
    (hXa : X ∈ a) (hXb : X ∈ b) (hXs : SameSide (line (Line := L) A B hAB) X Pa) : False := by
  set c := line (Line := L) A B hAB
  have hAc : A ∈ c := mem_line_left _
  have hBc : B ∈ c := mem_line_right _
  have hAS := ha A hA
  have hBS := hb B hB
  have hPS := ha Pa hPa
  have hQS := hb Qb hQb
  have hXS := ha X hXa
  have hcS : LineIn c S := F.lineIn hS hAS hBS hAB
  have hPA : Pa ≠ A := ne_of_mem_not_mem hAc hopp.1
  have hQB : Qb ≠ B := ne_of_mem_not_mem hBc hopp.2.1
  have hXA : X ≠ A := ne_of_mem_not_mem hAc hXs.1
  have hXB : X ≠ B := ne_of_mem_not_mem hBc hXs.1
  have hXr : X ∈ ray A Pa := mem_ray_of_sameSide hAc (collinear_of_mem hA hPa hXa) hXA
    (sameSide_symm' hXs)
  have hXQ : OppositeSides c X Qb := F.opp_of_ss_opp hS hcS hXS hPS hQS hXs hopp
  have hbQX : Between Qb B X := by
    rcases mem_ray_or_between (L := L) (collinear_of_mem hB hQb hXb) hQB hXB with h | h
    · exact absurd (sameSide_of_ray hBc hopp.2.1 h) (fun hs =>
        not_sameSide_of_opp' hXQ (sameSide_symm' hs))
    · exact h
  obtain ⟨Y, hYr, hYc⟩ := segCong_layoff (L := L) hXA.symm hQB.symm
  have hYS : Y ∈ S := F.memS_of_ray hS hBS hQS hYr
  have hYs : SameSide c Qb Y := sameSide_of_ray hBc hopp.2.1 hYr
  have nP := nc_of hAc hBc hAB hopp.1
  have nQ := nc_of hAc hBc hAB hopp.2.1
  have nX := nc_of hAc hBc hAB hXs.1
  have nY := nc_of hAc hBc hAB hYs.2.1
  have hc2 : AngCong X A B Y B A := angCong_rays nP.2.2.1 nQ.2.2.2.2.2 hc hXr
    (mem_ray_self' (L := L) hAB.symm) hYr (mem_ray_self' (L := L) hAB)
  have hc3 : AngCong B A X A B Y := angCong_swap_right nX.2.2.2.1 nY.2.2.2.2.2
    (angCong_swap_left nX.2.2.1 nY.2.2.2.2.2 hc2)
  obtain ⟨-, s2, -⟩ := F.sas (A := A) (B := B) (C := X) (A' := B) (B' := A) (C' := Y) nX.1
    nY.2.2.2.1 (segCong_swap_right (Line := L) (segCong_refl (Line := L) hAB)) hYc hc3
  -- `s2 : ∠ABX ≡ ∠BAY`
  obtain ⟨Ps, hPs⟩ := exists_beyond (Line := L) hPA
  have hPsa : Ps ∈ a := mem_right_of_between hPs hPa hA
  have hPsS := ha Ps hPsa
  have hsupp : AngCong B A Ps A B X := F.supp nP.2.2.1 nQ.2.2.2.2.2 hc hPs hbQX
  have hPsQ : SameSide c Ps Qb := F.ss_of_opp_opp hS hcS hPsS hPS hQS
    (opp_symm' (opp_of_between_mem hAc hopp.1 hPs)) hopp
  have nPs := nc_of hAc hBc hAB hPsQ.1
  have t : AngCong B A Ps B A Y := angCong_trans nPs.2.2.2.1 nX.1 nY.2.2.2.1 hsupp s2
  have e := F.layoff_unique S hS B A Ps c A B Ps Y nPs.2.2.2.1 hcS hAc hBc hAB.symm hPsS hYS
    (F.ss_trans hS hcS hPsS hQS hYS hPsQ hYs) (angCong_refl nPs.2.2.2.1) t
  have hYA : Y ≠ A := ne_of_mem_not_mem hAc hYs.2.1
  have hYr2 : Y ∈ ray A Ps := by rw [e]; exact mem_ray_self' (L := L) hYA
  have hYa : Y ∈ a := mem_of_collinear (collinear_of_mem_ray hYr2)
    (ne_of_mem_ray' hYr2).symm hA hPsa
  have hYb : Y ∈ b := mem_of_collinear (collinear_of_mem_ray hYr) hQB.symm hB hQb
  have hXY : X ≠ Y := fun e => not_sameSide_of_opp' hXQ (e ▸ sameSide_symm' hYs)
  have hab : a = b := line_unique hXY hXa hYa hXb hYb
  subst hab
  exact hopp.1 (by rw [line_unique hAB hA hB hAc hBc] at hPa; exact hPa)

/-- **Converse of Theorem 19** (alternate angles): if the alternate angles `∠(Pa, A, B)` and
`∠(Qb, B, A)` made by the transversal `AB` with the lines `a ∋ A, Pa` and `b ∋ B, Qb` are congruent,
`a` and `b` have no common point. No axiom of parallels is used. -/
theorem parallel_of_alternate (hS : F.IsPl S) {a b : L} (ha : LineIn a S) (hb : LineIn b S)
    {Pa Qb : P} (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb) (hc : AngCong Pa A B Qb B A) :
    ¬Meets (Point := P) a b := by
  rintro ⟨X, hXa, hXb⟩
  set c := line (Line := L) A B hAB
  have hAc : A ∈ c := mem_line_left _
  have hBc : B ∈ c := mem_line_right _
  have hcS : LineIn c S := F.lineIn hS (ha A hA) (hb B hB) hAB
  have hXc : X ∉ c := by
    intro hX
    have hac : a ≠ c := fun e => hopp.1 (e ▸ hPa)
    have hbc : b ≠ c := fun e => hopp.2.1 (e ▸ hQb)
    exact hAB ((eq_of_mem_of_mem hac hXa hX hA hAc).symm.trans
      (eq_of_mem_of_mem hbc hXb hX hB hBc))
  rcases sameSide_or_opp' hXc hopp.1 with h | h
  · exact F.no_meet_aux hS ha hb hA hB hAB hPa hQb hopp hc hXa hXb h
  · have hXQ : SameSide c X Qb := F.ss_of_opp_opp hS hcS (ha X hXa) (ha Pa hPa) (hb Qb hQb) h hopp
    have ec : line (Line := L) B A hAB.symm = c := line_comm hAB
    have nP := nc_of hAc hBc hAB hopp.1
    have nQ := nc_of hAc hBc hAB hopp.2.1
    have hc' : AngCong Qb B A Pa A B := angCong_symm nP.2.2.1 nQ.2.2.2.2.2 hc
    exact F.no_meet_aux hS hb ha hB hA hAB.symm hQb hPa (by rw [ec]; exact opp_symm' hopp) hc'
      hXb hXa (by rw [ec]; exact hXQ)

/-- **Converse of Theorem 19** (exterior-interior angles): if `Pa`, `Qb` lie on the same side of the
transversal `AB`, `B` lies between `A` and `R`, and `∠(Pa, A, B) ≡ ∠(Qb, B, R)`, then `a` and `b`
have no common point. -/
theorem parallel_of_corresponding (hS : F.IsPl S) {a b : L} (ha : LineIn a S) (hb : LineIn b S)
    {Pa Qb : P} (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hs : SameSide (line (Line := L) A B hAB) Pa Qb) (hR : Between A B R)
    (hc : AngCong Pa A B Qb B R) : ¬Meets (Point := P) a b := by
  have hAc : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBc : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hQB : Qb ≠ B := ne_of_mem_not_mem hBc hs.2.1
  obtain ⟨Qs, hQs⟩ := exists_beyond (Line := L) hQB
  have hQsb : Qs ∈ b := mem_right_of_between hQs hQb hB
  have nP := nc_of hAc hBc hAB hs.1
  have nQ := nc_of hAc hBc hAB hs.2.1
  have hopp : OppositeSides (line (Line := L) A B hAB) Pa Qs :=
    F.opp_of_ss_opp hS (F.lineIn hS (ha A hA) (hb B hB) hAB) (ha Pa hPa) (hb Qb hQb)
      (hb Qs hQsb) hs (opp_of_between_mem hBc hs.2.1 hQs)
  have nQs := nc_of hAc hBc hAB hopp.2.1
  have nQR : ¬Collinear Qb B R := fun hh =>
    nQ.2.2.2.2.2 (by
      obtain ⟨g, h1, h2, h3⟩ := hh
      exact ⟨g, h1, h2, mem_left_of_between hR h2 h3⟩)
  have v : AngCong Qb B R Qs B A := F.vertical nQR hQs (between_symm hR)
  exact F.parallel_of_alternate hS ha hb hA hB hAB hPa hQsb hopp
    (angCong_trans nP.2.2.1 nQR nQs.2.2.2.2.2 hc v)

/-- **Theorem 19** (alternate angles), with the uniqueness of parallels in the plane. -/
theorem alternate_of_parallel (hS : F.IsPl S) (hpar : F.ParUnique) {a b : L} (ha : LineIn a S)
    (hb : LineIn b S) (hab : ¬Meets (Point := P) a b) {Pa Qb : P} (hA : A ∈ a) (hB : B ∈ b)
    (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb) : AngCong Pa A B Qb B A := by
  set c := line (Line := L) A B hAB
  have hAc : A ∈ c := mem_line_left _
  have hBc : B ∈ c := mem_line_right _
  have hAS := ha A hA
  have hBS := hb B hB
  have hPS := ha Pa hPa
  have hQS := hb Qb hQb
  have hcS : LineIn c S := F.lineIn hS hAS hBS hAB
  have nQ := nc_of hAc hBc hAB hopp.2.1
  obtain ⟨X, hXS, hXs, hXc⟩ := F.layoff S hS Qb B A c A B Pa nQ.2.2.2.2.2 hcS hAc hBc hAB.symm
    hPS hopp.1
  -- `hXc : ∠QbBA ≡ ∠BAX`
  have hXA : X ≠ A := ne_of_mem_not_mem hAc hXs.1
  have nX := nc_of hAc hBc hAB hXs.1
  have hXc' : AngCong X A B Qb B A := angCong_symm nQ.2.2.2.2.2 nX.2.2.1
    (angCong_swap_right nQ.2.2.2.2.2 nX.2.2.2.1 hXc)
  have hopp' : OppositeSides c X Qb := F.opp_of_ss_opp hS hcS hXS hPS hQS hXs hopp
  have ha'S := F.lineIn hS hAS hXS hXA.symm
  have hAa' : A ∈ line (Line := L) A X hXA.symm := mem_line_left _
  have hXa' : X ∈ line (Line := L) A X hXA.symm := mem_line_right _
  have hpar' := F.parallel_of_alternate hS ha'S hb hAa' hB hAB hXa' hQb hopp' hXc'
  have hAb : A ∉ b := fun hA' => hopp.2.1 (by
    rw [line_unique hAB hA' hB hAc hBc] at hQb; exact hQb)
  have e := hpar S hS b a _ A hb ha ha'S hAb hA hAa' hab hpar'
  have hPa' : Pa ∈ line (Line := L) A X hXA.symm := e ▸ hPa
  have hPr : Pa ∈ ray A X := mem_ray_of_sameSide hAc (collinear_of_mem hAa' hXa' hPa')
    (ne_of_mem_not_mem hAc hopp.1) hXs
  exact angCong_rays nX.2.2.1 nQ.2.2.2.2.2 hXc' hPr (mem_ray_self' (L := L) hAB.symm)
    (mem_ray_self' (L := L) (ne_of_mem_not_mem hBc hopp.2.1)) (mem_ray_self' (L := L) hAB)

/-- **Theorem 19** (exterior-interior angles), with the uniqueness of parallels in the plane. -/
theorem corresponding_of_parallel (hS : F.IsPl S) (hpar : F.ParUnique) {a b : L}
    (ha : LineIn a S) (hb : LineIn b S) (hab : ¬Meets (Point := P) a b) {Pa Qb : P} (hA : A ∈ a)
    (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hs : SameSide (line (Line := L) A B hAB) Pa Qb) (hR : Between A B R) :
    AngCong Pa A B Qb B R := by
  have hAc : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBc : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hQB : Qb ≠ B := ne_of_mem_not_mem hBc hs.2.1
  obtain ⟨Qs, hQs⟩ := exists_beyond (Line := L) hQB
  have hQsb : Qs ∈ b := mem_right_of_between hQs hQb hB
  have nP := nc_of hAc hBc hAB hs.1
  have nQ := nc_of hAc hBc hAB hs.2.1
  have hopp : OppositeSides (line (Line := L) A B hAB) Pa Qs :=
    F.opp_of_ss_opp hS (F.lineIn hS (ha A hA) (hb B hB) hAB) (ha Pa hPa) (hb Qb hQb)
      (hb Qs hQsb) hs (opp_of_between_mem hBc hs.2.1 hQs)
  have nQs := nc_of hAc hBc hAB hopp.2.1
  have alt := F.alternate_of_parallel hS hpar ha hb hab hA hB hAB hPa hQsb hopp
  have v : AngCong Qs B A Qb B R := F.vertical nQs.2.2.2.2.2 (between_symm hQs) hR
  have nQR : ¬Collinear Qb B R := fun hh =>
    nQ.2.2.2.2.2 (by
      obtain ⟨g, h1, h2, h3⟩ := hh
      exact ⟨g, h1, h2, mem_left_of_between hR h2 h3⟩)
  exact angCong_trans nP.2.2.1 nQs.2.2.2.2.2 nQR alt v

/-- **Theorem 20** in a plane frame with the uniqueness of parallels: the three angles of the
triangle `ABC` laid off side by side at `C` fill a straight angle: `∠XCA ≡ ∠A`, `∠ACB = ∠C`,
`∠BCW ≡ ∠B` with `C` between `X` and `W`, `A` within `∠XCB` and `B` within `∠ACW`. -/
theorem angle_sum (hS : F.IsPl S) (hpar : F.ParUnique) (hAS : A ∈ S) (hBS : B ∈ S)
    (hCS : C ∈ S) (h : ¬Collinear A B C) :
    ∃ X W : P, X ∈ S ∧ W ∈ S ∧ Between X C W ∧ A ∈ Interior X C B ∧ B ∈ Interior A C W ∧
      AngCong C A B X C A ∧ AngCong C B A B C W := by
  obtain ⟨hAB, hCB, hAC⟩ := F.ne h
  have hmS := F.lineIn hS hCS hAS hAC.symm
  have hCm : C ∈ line (Line := L) C A hAC.symm := mem_line_left _
  have hAm : A ∈ line (Line := L) C A hAC.symm := mem_line_right _
  have hBm : B ∉ line (Line := L) C A hAC.symm := fun hh => h (collinear_of_mem hAm hh hCm)
  obtain ⟨Bs, hBs⟩ := exists_beyond (Line := L) hCB.symm
  have hBsS := F.memS_of_between' hS hBS hCS hBs
  have oB : OppositeSides (line (Line := L) C A hAC.symm) B Bs := opp_of_between_mem hCm hBm hBs
  have nBAC : ¬Collinear B A C := fun hh => h hh.swap12
  obtain ⟨X, hXS, hXs, hXc⟩ := F.layoff S hS B A C _ C A Bs nBAC hmS hCm hAm hAC hBsS oB.2.1
  have hXm : X ∉ line (Line := L) C A hAC.symm := hXs.1
  have oXB : OppositeSides (line (Line := L) C A hAC.symm) X B :=
    F.opp_of_ss_opp hS hmS hXS hBsS hBS hXs (opp_symm' oB)
  have hXC : X ≠ C := ne_of_mem_not_mem hCm hXm
  have nXm := nc_of hCm hAm hAC.symm hXm
  have hXc' : AngCong X C A B A C := angCong_swap_left nXm.2.2.2.1 nBAC
    (angCong_symm nBAC nXm.2.2.2.1 hXc)
  have haS := F.lineIn hS hCS hXS hXC.symm
  have hbS := F.lineIn hS hAS hBS hAB
  have hCa : C ∈ line (Line := L) C X hXC.symm := mem_line_left _
  have hXa : X ∈ line (Line := L) C X hXC.symm := mem_line_right _
  have hAb : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBb : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hab := F.parallel_of_alternate hS haS hbS hCa hAb hAC.symm hXa hBb oXB hXc'
  obtain ⟨W, hW⟩ := exists_beyond (Line := L) hXC
  have hWa : W ∈ line (Line := L) C X hXC.symm := mem_right_of_between hW hXa hCa
  have hWS := haS W hWa
  have hWC : W ≠ C := (ne23_of_between hW).symm
  have hAa : A ∉ line (Line := L) C X hXC.symm := fun hh => hab ⟨A, hh, hAb⟩
  have hBa : B ∉ line (Line := L) C X hXC.symm := fun hh => hab ⟨B, hh, hBb⟩
  have sAB : SameSide (line (Line := L) C X hXC.symm) A B :=
    ⟨hAa, hBa, fun ⟨Z, hZa, hZ⟩ => hab ⟨Z, hZa, mem_mid_of_between hZ hAb hBb⟩⟩
  have hnS := F.lineIn hS hCS hBS hCB
  have hCn : C ∈ line (Line := L) C B hCB := mem_line_left _
  have hBn : B ∈ line (Line := L) C B hCB := mem_line_right _
  have hAn : A ∉ line (Line := L) C B hCB := fun hh => h (collinear_of_mem hh hBn hCn)
  have hXn : X ∉ line (Line := L) C B hCB := fun hh => hBa (by
    rw [line_unique hXC.symm hCa hXa hCn hh]; exact hBn)
  have hWn : W ∉ line (Line := L) C B hCB := fun hh => hBa (by
    rw [line_unique hWC.symm hCa hWa hCn hh]; exact hBn)
  have sAX : SameSide (line (Line := L) C B hCB) A X := by
    rcases sameSide_or_opp' hAn hXn with hs | ho
    · exact hs
    · exfalso
      obtain ⟨-, -, Y, hYn, hY⟩ := ho
      have hYS := F.memS_of_between hS hAS hXS hY
      have hYC : Y ≠ C := fun e => hXm (by
        rw [e] at hY
        exact mem_right_of_between hY hAm hCm)
      rcases mem_ray_or_between (L := L) (collinear_of_mem hCn hBn hYn) hCB.symm hYC with hr | hb
      · have s1 : SameSide (line (Line := L) C A hAC.symm) B Y := sameSide_of_ray hCm hBm hr
        have s2 : SameSide (line (Line := L) C A hAC.symm) Y X :=
          sameSide_of_between_mem' hAm hXm hY
        exact not_sameSide_of_opp' oXB
          (sameSide_symm' (F.ss_trans hS hmS hBS hYS hXS s1 s2))
      · have s1 : SameSide (line (Line := L) C X hXC.symm) Y A :=
          sameSide_of_between_mem' hXa hAa (between_symm hY)
        have s2 := F.ss_trans hS haS hYS hAS hBS s1 sAB
        exact not_sameSide_of_opp' (opp_of_between_mem hCa hBa hb) (sameSide_symm' s2)
  have oAW : OppositeSides (line (Line := L) C B hCB) A W :=
    F.opp_of_ss_opp hS hnS hAS hXS hWS sAX (opp_of_between_mem hCn hXn hW)
  have alt := F.alternate_of_parallel hS hpar haS hbS hab hCa hBb hCB hWa hAb
    (opp_symm' oAW)
  -- `alt : ∠WCB ≡ ∠ABC`
  have ea : line (Line := L) C W hWC.symm = line C X hXC.symm :=
    (eq_line hWC.symm hCa hWa).symm
  refine ⟨X, W, hXS, hWS, hW, ?_, ?_, ?_, ?_⟩
  · exact (interior_iff (L := L) hXC hCB.symm).2 ⟨sAB, sAX⟩
  · refine (interior_iff (L := L) hAC hWC).2 ⟨?_, ?_⟩
    · exact F.ss_of_opp_opp hS hmS hBS hXS hWS (opp_symm' oXB) (opp_of_between_mem hCm hXm hW)
    · rw [ea]; exact sameSide_symm' sAB
  · have nCAB : ¬Collinear C A B := fun hh => h hh.perm231
    exact angCong_swap_right nCAB nXm.2.2.2.1 (angCong_swap_left nBAC nXm.2.2.2.1 hXc)
  · have nWn := nc_of hCn hBn hCB hWn
    have nCBA : ¬Collinear C B A := fun hh => h hh.swap13
    exact angCong_swap_right nCBA nWn.2.2.1
      (angCong_swap_left h nWn.2.2.1 (angCong_symm nWn.2.2.1 h alt))

/-- "Less than" between angles is compatible with the congruence of the larger angle: if `∠AOB` is
congruent to `∠A₁O₁X` with `X` within the segment `A₁B₁`, and `∠A₁O₁B₁ ≡ ∠A₂O₂B₂`, then `∠AOB` is
congruent to `∠A₂O₂Y` for a point `Y` within the segment `A₂B₂` (Theorem 13 and the crossbar
theorem). -/
theorem angLt_congr {A₁ O₁ B₁ A₂ O₂ B₂ : P} (h1 : ¬Collinear A₁ O₁ B₁)
    (h2 : ¬Collinear A₂ O₂ B₂) (hX : Between A₁ X B₁) (hc : AngCong A O B A₁ O₁ X)
    (h : ¬Collinear A O B) (hc12 : AngCong A₁ O₁ B₁ A₂ O₂ B₂) :
    ∃ Y, Between A₂ Y B₂ ∧ AngCong A O B A₂ O₂ Y := by
  obtain ⟨S1, hS1, hA1, hO1, hB1⟩ := F.exists_pl A₁ O₁ B₁ h1
  have hXS := F.memS_of_between hS1 hA1 hB1 hX
  have hXi := mem_interior_of_between (L := L) h1 hX
  obtain ⟨Y0, hY0S, hY0i, a1, -⟩ := F.interior_transfer hS1 hO1 hA1 hB1 hXS h1 h2 hc12 hXi
  obtain ⟨S2, hS2, hA2, hO2, hB2⟩ := F.exists_pl A₂ O₂ B₂ h2
  have hY0S2 := hY0S S2 hS2 hO2 hA2 hB2
  obtain ⟨Y, hY, hYr⟩ := F.crossbar hS2 hO2 hA2 hB2 hY0S2 h2 hY0i
  obtain ⟨hA1O, hB1O, -⟩ := F.ne h1
  obtain ⟨hA2O, hB2O, -⟩ := F.ne h2
  have nX := (nc_of_interior (L := L) hA1O hB1O hXi).1
  have nY0 := (nc_of_interior (L := L) hA2O hB2O hY0i).1
  have nY := (nc_of_interior (L := L) hA2O hB2O (mem_interior_of_between (L := L) h2 hY)).1
  refine ⟨Y, hY, angCong_trans h nX nY hc ?_⟩
  exact angCong_rays nX nY0 a1 (mem_ray_self' (L := L) hA1O)
    (mem_ray_self' (L := L) (F.ne nX).2.1) (mem_ray_self' (L := L) hA2O) hYr

end Frame

end HilbertFoundations
