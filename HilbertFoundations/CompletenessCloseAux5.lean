import HilbertFoundations.CompletenessCloseAux4

/-!
# Helper module for `CompletenessClose.lean` (5): every geometry of space with I–V embeds into `ℝ³`

This module contains no unit of Hilbert's text.

* `CC.emb_plane`: under an isometric map into `Coord ℝ 3` carrying four points to the standard
  frame, every plane goes into a unique plane.
* `CC.exists_preEmb_of_metric`: an isometric, betweenness-preserving map into `Coord ℝ 3` that
  carries planes into planes extends to an embedding `CC.PreEmb` (lines by `CC.emb_line`, angles by
  `CC.ang_char` on both sides).
* `CC.exists_preEmb`: a geometry of space with I–V having a plane has an embedding into
  `Coord ℝ 3` (rectangular co-ordinates, `CompletenessCloseAux2.lean`).
* `CC.exists_preEmb_line`: a geometry of space with I–V *without planes* (all its points lie on one
  line, by I 3) has an embedding into the first axis of `Coord ℝ 3` (the co-ordinate of the line,
  `CompletenessCloseAux4.lean`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace CC

universe u v w

section Space

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hG : SpaceGeometry P L Pl] {ℓ : P → P → ℝ} {ι : P → Coord ℝ 3}

include hG

/-- **Every plane goes into a unique plane of the co-ordinate space.** -/
theorem emb_plane (hℓ : IsLen ℓ) (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X))
    (hbtw : ∀ A B C, Between A B C → Between (ι A) (ι B) (ι C))
    (hfr : ∃ O E1 E2 E3 : P, ι O = AffPt.ofV ![0, 0, 0] ∧ ι E1 = AffPt.ofV ![1, 0, 0] ∧
      ι E2 = AffPt.ofV ![0, 1, 0] ∧ ι E3 = AffPt.ofV ![0, 0, 1]) (α : Pl) :
    ∃ α' : CoordPlane ℝ 3, ∀ X : P, ι X ∈ α' ↔ X ∈ α := by
  obtain ⟨A, B, C, hA, hB, hC, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  obtain ⟨hAB, hCB, hAC⟩ := ne_of_not_collinear (L := L) hn (line_through_space (Pl := Pl) B)
  have hn' : ¬Collinear (Line := CoordLine ℝ 3) (ι A) (ι B) (ι C) := fun hc =>
    hn (emb_collinear_rev (L := L) hℓ hiso hbtw hc hAB hAC hCB.symm)
  obtain ⟨α', hA', hB', hC'⟩ := exists_plane (Plane := CoordPlane ℝ 3) hn'
  have hS : LineClosed (L := L) {X : P | ι X ∈ α'} := by
    intro U V X hUV hU hV hc
    have hc' := emb_collinear (L := L) hℓ hiso hbtw hc
    have hUV' : ι U ≠ ι V := (emb_injective hℓ hiso).ne hUV
    obtain ⟨l, hUl, hVl⟩ := exists_line (Line := CoordLine ℝ 3) hUV'
    exact liesInPlane_of_mem hUV' hUl hVl hU hV (ι X) (mem_of_collinear hc' hUV' hUl hVl)
  have hα : ∀ X, X ∈ α → ι X ∈ α' := plane_closure (L := L) hS α hA hB hC hn hA' hB' hC'
  refine ⟨α', fun X => ⟨fun hX => ?_, hα X⟩⟩
  by_contra hXα
  have hall : ∀ Y : P, ι Y ∈ α' := space_closure (L := L) hS α hα hX hXα
  obtain ⟨O, E1, E2, E3, e0, e1, e2, e3⟩ := hfr
  have h0 := hall O
  have h1 := hall E1
  have h2 := hall E2
  have h3 := hall E3
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  exact not_coplanar_std α' h0 h1 h2 h3

/-- **From an isometric map to an embedding.** -/
theorem exists_preEmb_of_metric (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X))
    (hbtw : ∀ A B C, Between A B C → Between (ι A) (ι B) (ι C))
    (hpl : ∀ α : Pl, ∃ α' : CoordPlane ℝ 3, ∀ X : P, ι X ∈ α' ↔ X ∈ α) :
    ∃ e : PreEmb P L Pl, e.pt = ι := by
  classical
  have hinj := emb_injective hℓ hiso
  have hln := fun a : L => emb_line (L := L) hℓ hiso hbtw a
  have hlinj : Function.Injective (fun a : L => Classical.choose (hln a)) := by
    intro a b e
    have e' : Classical.choose (hln a) = Classical.choose (hln b) := e
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) a
    have h1 := Classical.choose_spec (hln a)
    have h2 := Classical.choose_spec (hln b)
    have hA' : ι A ∈ Classical.choose (hln b) := by rw [← e']; exact (h1 A).2 hA
    have hB' : ι B ∈ Classical.choose (hln b) := by rw [← e']; exact (h1 B).2 hB
    exact line_unique hAB hA hB ((h2 A).1 hA') ((h2 B).1 hB')
  have hpinj : Function.Injective (fun α : Pl => Classical.choose (hpl α)) := by
    intro α β e
    have e' : Classical.choose (hpl α) = Classical.choose (hpl β) := e
    obtain ⟨A, B, C, hA, hB, hC, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
    have h1 := Classical.choose_spec (hpl α)
    have h2 := Classical.choose_spec (hpl β)
    have hA' : ι A ∈ Classical.choose (hpl β) := by rw [← e']; exact (h1 A).2 hA
    have hB' : ι B ∈ Classical.choose (hpl β) := by rw [← e']; exact (h1 B).2 hB
    have hC' : ι C ∈ Classical.choose (hpl β) := by rw [← e']; exact (h1 C).2 hC
    exact plane_unique hn hA hB hC ((h2 A).1 hA') ((h2 B).1 hB') ((h2 C).1 hC')
  refine ⟨{
    pt := ι
    line := fun a => Classical.choose (hln a)
    plane := fun α => Classical.choose (hpl α)
    pt_injective := hinj
    line_injective := hlinj
    plane_injective := hpinj
    mem_iff := fun A a => Classical.choose_spec (hln a) A
    memPlane_iff := fun A α => Classical.choose_spec (hpl α) A
    between_iff := fun A B C => ⟨emb_between_rev (L := L) hℓ hiso hbtw, hbtw A B C⟩
    segCong_iff := fun A B C D hAB hCD => emb_segCong hℓ hiso hAB hCD
    angCong_iff := ?_ }, rfl⟩
  intro A O B A' O' B' h h'
  obtain ⟨hAO, hBO, hAB⟩ := ne_of_not_collinear (L := L) h (line_through_space (Pl := Pl) O)
  obtain ⟨hAO', hBO', hAB'⟩ := ne_of_not_collinear (L := L) h' (line_through_space (Pl := Pl) O')
  obtain ⟨A1, hA1, sA⟩ := segCong_layoff (L := L) hAO.symm hAO'.symm
  obtain ⟨B1, hB1, sB⟩ := segCong_layoff (L := L) hBO.symm hBO'.symm
  have n1 : ¬Collinear (Line := L) A1 O' B1 := not_collinear_of_mem_rays h' hA1 hB1
  obtain ⟨hA1O, hB1O, hA1B1⟩ :=
    ne_of_not_collinear (L := L) n1 (line_through_space (Pl := Pl) O')
  have c := ang_char (L := L) (Pl := Pl) h h' (mem_ray_self' (L := L) hAO)
    (mem_ray_self' (L := L) hBO) hA1 hB1 sA sB
  have g : ¬Collinear (Line := CoordLine ℝ 3) (ι A) (ι O) (ι B) := fun hc =>
    h (emb_collinear_rev (L := L) hℓ hiso hbtw hc hAO hAB hBO.symm)
  have g' : ¬Collinear (Line := CoordLine ℝ 3) (ι A') (ι O') (ι B') := fun hc =>
    h' (emb_collinear_rev (L := L) hℓ hiso hbtw hc hAO' hAB' hBO'.symm)
  have c' := ang_char (L := CoordLine ℝ 3) (Pl := CoordPlane ℝ 3) g g'
    (mem_ray_self' (L := CoordLine ℝ 3) (hinj.ne hAO))
    (mem_ray_self' (L := CoordLine ℝ 3) (hinj.ne hBO))
    (emb_ray (L := L) hℓ hiso hbtw hA1) (emb_ray (L := L) hℓ hiso hbtw hB1)
    ((emb_segCong hℓ hiso hAO.symm hA1O.symm).2 sA)
    ((emb_segCong hℓ hiso hBO.symm hB1O.symm).2 sB)
  rw [c, c']
  exact emb_segCong hℓ hiso hAB hA1B1

/-- **A geometry of space with I–V having a plane has an embedding into `Coord ℝ 3`.** -/
theorem exists_preEmb (α₀ : Pl) : Nonempty (PreEmb P L Pl) := by
  obtain ⟨ℓ, ι, hℓ, hiso, hbtw, O, E1, E2, E3, e0, e1, e2, e3⟩ :=
    exists_metric_emb (P := P) (L := L) α₀
  obtain ⟨e, -⟩ := exists_preEmb_of_metric (L := L) (Pl := Pl) hℓ hiso hbtw
    (emb_plane (L := L) hℓ hiso hbtw ⟨O, E1, E2, E3, e0, e1, e2, e3⟩)
  exact ⟨e⟩

/-- **A geometry of space with I–V without planes has an embedding into the first axis of
`Coord ℝ 3`.** -/
theorem exists_preEmb_line [IsEmpty Pl] {O E : P} (hOE : O ≠ E) :
    ∃ e : PreEmb P L Pl, ∀ X : P, AffPt.toV (e.pt X) 1 = 0 := by
  have hcol : ∀ X Y Z : P, Collinear (Line := L) X Y Z := by
    intro X Y Z
    by_contra h
    obtain ⟨α, -⟩ := exists_plane (Plane := Pl) h
    exact isEmptyElim α
  obtain ⟨a, hO, hE⟩ := exists_line (Line := L) hOE
  have hall : ∀ X : P, X ∈ a := fun X => mem_of_collinear (hcol O E X) hOE hO hE
  obtain ⟨f, hinj, hb, hc⟩ := exists_line_coord (L := L) a hall hOE
  have hℓ : IsLen (fun X Y : P => |f Y - f X|) := by
    refine ⟨fun A => by simp, fun A B h => abs_pos.2 (sub_ne_zero.2 (hinj.ne h.symm)),
      fun A B C D hAB hCD => hc A B C D hAB hCD, ?_⟩
    intro A B C h
    rcases hb A B C h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · show |f B - f A| + |f C - f B| = |f C - f A|
      rw [abs_of_pos (sub_pos.2 h1), abs_of_pos (sub_pos.2 h2),
        abs_of_pos (sub_pos.2 (h1.trans h2))]
      ring
    · show |f B - f A| + |f C - f B| = |f C - f A|
      rw [abs_of_neg (sub_neg.2 h2), abs_of_neg (sub_neg.2 h1),
        abs_of_neg (sub_neg.2 (h1.trans h2))]
      ring
  have hiso : ∀ X Y : P, (fun X Y : P => |f Y - f X|) X Y ^ 2 =
      Coord.ip ((AffPt.ofV ![f Y, 0, 0] : Coord ℝ 3) - AffPt.ofV ![f X, 0, 0])
        (AffPt.ofV ![f Y, 0, 0] - AffPt.ofV ![f X, 0, 0]) := by
    intro X Y
    show |f Y - f X| ^ 2 = _
    rw [sq_abs, Coord.ip_def, Fin.sum_univ_three]
    simp <;> ring
  have hbtw : ∀ A B C : P, Between A B C →
      Between (AffPt.ofV ![f A, 0, 0] : Coord ℝ 3) (AffPt.ofV ![f B, 0, 0])
        (AffPt.ofV ![f C, 0, 0]) := by
    intro A B C h
    have hAC : f A ≠ f C := hinj.ne (ne13_of_between (Line := L) h)
    have hd : f C - f A ≠ 0 := sub_ne_zero.2 hAC.symm
    have ht : 0 < (f B - f A) / (f C - f A) ∧ (f B - f A) / (f C - f A) < 1 := by
      rcases hb A B C h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h3 : 0 < f C - f A := by linarith
        exact ⟨div_pos (by linarith) h3, (div_lt_one h3).2 (by linarith)⟩
      · have h3 : f C - f A < 0 := by linarith
        exact ⟨div_pos_of_neg_of_neg (by linarith) h3, (div_lt_one_of_neg h3).2 (by linarith)⟩
    have key0 : f B = (f B - f A) / (f C - f A) * (f C - f A) + f A := by
      rw [div_mul_cancel₀ _ hd]; ring
    obtain ⟨t, t0, t1, key⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ f B = t * (f C - f A) + f A :=
      ⟨_, ht.1, ht.2, key0⟩
    refine AffPt.between_iff.2 (AffPt.sbtw_iff_param.2 ⟨fun e => hAC ?_, t, t0, t1, ?_⟩)
    · have e0 := congrFun (congrArg AffPt.toV e) 0
      simpa using e0
    · apply AffPt.toV_injective
      funext i
      fin_cases i
      · simpa using key
      · simp
      · simp
  obtain ⟨e, he⟩ := exists_preEmb_of_metric (L := L) (Pl := Pl)
    (ℓ := fun X Y : P => |f Y - f X|) (ι := fun X : P => (AffPt.ofV ![f X, 0, 0] : Coord ℝ 3))
    hℓ hiso hbtw (fun α => isEmptyElim α)
  refine ⟨e, fun X => ?_⟩
  rw [he]
  simp

end Space

end CC

end HilbertFoundations
