import HilbertFoundations.CompletenessCloseAux6

/-!
# Helper module for `CompletenessClose.lean` (7): the real co-ordinate space is complete

This module contains no unit of Hilbert's text. It shows that the hypotheses of the units
`s8.bolzano` and `s8.real_numbers` (groups I–V and the Axiom of Completeness) are satisfiable, so
that the two theorems of `CompletenessClose.lean` are not vacuous:

* `CC.coord_len_sq`: every length of segments of `Coord ℝ 3` (`CC.IsLen`) is a constant multiple of
  the euclidean length.
* `CC.ext_pt_surjective`: an extension (`SpaceEmbedding`) of `Coord ℝ 3` to a geometry of space with
  I–V adds no point. The extension is mapped isometrically into `Coord ℝ 3` (`CC.exists_metric_emb`);
  the composite map of `Coord ℝ 3` into itself multiplies the distances by a constant and preserves
  collinearity, so it is affine along every line. Hence the set of the old points contains, with two
  points, every point of the extension on their line; since it contains four points not in a plane,
  it contains every point (`CC.plane_closure`, `CC.space_closure`).
* `CC.spaceComplete_coord_real : SpaceComplete (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3)`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace CC

universe u v w

/-- **A length of `Coord ℝ 3` is a constant multiple of the euclidean length.** -/
theorem coord_len_sq {ℓ : Coord ℝ 3 → Coord ℝ 3 → ℝ} (hℓ : IsLen ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∀ X Y : Coord ℝ 3, ℓ X Y ^ 2 = c ^ 2 * Coord.ip (Y - X) (Y - X) := by
  obtain ⟨pt, hpt⟩ : ∃ pt : ℝ → Coord ℝ 3, ∀ t, pt t = AffPt.ofV ![t, 0, 0] := ⟨_, fun _ => rfl⟩
  have hpt_sub : ∀ s t : ℝ, Coord.ip (pt t - pt s) (pt t - pt s) = (t - s) ^ 2 := by
    intro s t
    rw [Coord.ip_def, Fin.sum_univ_three, hpt, hpt]
    simp
    ring
  have hpt_inj : ∀ s t : ℝ, pt s = pt t → s = t := by
    intro s t h
    have h0 := congrFun (congrArg AffPt.toV h) 0
    rw [hpt, hpt] at h0
    simpa using h0
  have hadd : ∀ s ∈ (⊤ : Subfield ℝ), ∀ t ∈ (⊤ : Subfield ℝ), 0 < s → 0 < t →
      ℓ (pt 0) (pt (s + t)) = ℓ (pt 0) (pt s) + ℓ (pt 0) (pt t) := by
    intro s _ t _ hs ht
    have hst : s + t ≠ 0 := by positivity
    have hb : Between (pt 0) (pt s) (pt (s + t)) := by
      refine AffPt.between_iff.2 (AffPt.sbtw_iff_param.2
        ⟨fun h => ?_, s / (s + t), by positivity, ?_, ?_⟩)
      · have := hpt_inj _ _ h
        linarith
      · rw [div_lt_one (by positivity)]
        linarith
      · have e : s = s / (s + t) * (s + t - 0) + 0 := by
          rw [sub_zero, add_zero, div_mul_cancel₀ _ hst]
        rw [hpt, hpt, hpt]
        apply AffPt.toV_injective
        funext i
        fin_cases i
        · simpa using e
        · simp
        · simp
    have hc : SegCong (pt s) (pt (s + t)) (pt 0) (pt t) := by
      rw [Coord.segCong_iff, hpt_sub, hpt_sub]
      ring
    have hne1 : pt s ≠ pt (s + t) := fun h => by
      have := hpt_inj _ _ h
      linarith
    have hne2 : pt 0 ≠ pt t := fun h => by
      have := hpt_inj _ _ h
      linarith
    rw [← hℓ.add _ _ _ hb, (hℓ.cong _ _ _ _ hne1 hne2).1 hc]
  have hpos : ∀ t ∈ (⊤ : Subfield ℝ), 0 < t → 0 < ℓ (pt 0) (pt t) := by
    intro t _ ht
    refine hℓ.pos _ _ (fun h => ?_)
    have := hpt_inj _ _ h
    linarith
  have lin := mu_linear ⊤ (fun t => ℓ (pt 0) (pt t)) hadd hpos
  refine ⟨ℓ (pt 0) (pt 1), hpos 1 (Subfield.mem_top _) one_pos, fun X Y => ?_⟩
  by_cases hXY : X = Y
  · subst hXY
    rw [hℓ.self, sub_self, Coord.ip_zero_left]
    ring
  · have hp : 0 < Coord.ip (Y - X) (Y - X) := Coord.ip_self_pos (sub_ne_zero.2 (Ne.symm hXY))
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (Coord.ip (Y - X) (Y - X)) := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr]
      exact Real.sqrt_pos.2 hp
    have hr2 : r ^ 2 = Coord.ip (Y - X) (Y - X) := by
      rw [hr]
      exact Real.sq_sqrt hp.le
    have hne : pt 0 ≠ pt r := fun h => by
      have := hpt_inj _ _ h
      linarith
    have hc : SegCong X Y (pt 0) (pt r) := by
      rw [Coord.segCong_iff, hpt_sub, sub_zero, hr2]
    have e := lin r (Subfield.mem_top _) hr0
    have e' : ℓ (pt 0) (pt r) = ℓ (pt 0) (pt 1) * r := e
    rw [(hℓ.cong _ _ _ _ hXY hne).1 hc, e', mul_pow, hr2]

/-- The points `(0, 0, 0)`, `(1, 0, 0)`, `(0, 1, 0)` of `Coord ℝ 3` are not collinear. -/
theorem not_collinear_std :
    ¬Collinear (Line := CoordLine ℝ 3) (AffPt.ofV ![0, 0, 0] : Coord ℝ 3) (AffPt.ofV ![1, 0, 0])
      (AffPt.ofV ![0, 1, 0]) := by
  rintro ⟨l, h0, h1, h2⟩
  have h01 : (AffPt.ofV ![0, 0, 0] : Coord ℝ 3) ≠ AffPt.ofV ![1, 0, 0] := by
    intro h
    have h' := congrFun (congrArg AffPt.toV h) 0
    simp at h'
  have hl : l = AffLine.through _ _ h01 :=
    line_unique h01 h0 h1 (AffLine.left_mem_through h01) (AffLine.right_mem_through h01)
  rw [hl] at h2
  obtain ⟨r, hr⟩ := (AffLine.mem_through_iff h01).1 h2
  have h' := congrFun (congrArg AffPt.toV hr) 1
  simp at h'

section Model

variable {P' : Type u} {L' : Type v} {Pl' : Type w} [HasLines P' L'] [HasPlanes P' Pl']
  [HasBetween P'] [HasSegCong P'] [HasAngCong P'] [hG : SpaceGeometry P' L' Pl']

include hG

/-- Collinearity is reflected by an extension of `Coord ℝ 3`. -/
theorem ext_collinear_rev
    (e : SpaceEmbedding (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) P' L' Pl') {A B C : Coord ℝ 3}
    (hc : Collinear (Line := L') (e.pt A) (e.pt B) (e.pt C)) :
    Collinear (Line := CoordLine ℝ 3) A B C := by
  have two : ∀ X Y : Coord ℝ 3, ∃ l : CoordLine ℝ 3, X ∈ l ∧ Y ∈ l := by
    intro X Y
    by_cases h : X = Y
    · subst h
      obtain ⟨l, hl⟩ := line_through_space (L := CoordLine ℝ 3) (Pl := CoordPlane ℝ 3) X
      exact ⟨l, hl, hl⟩
    · exact exists_line (Line := CoordLine ℝ 3) h
  by_cases hAB : A = B
  · subst hAB
    obtain ⟨l, h1, h2⟩ := two A C
    exact ⟨l, h1, h1, h2⟩
  by_cases hAC : A = C
  · subst hAC
    obtain ⟨l, h1, h2⟩ := two A B
    exact ⟨l, h1, h2, h1⟩
  by_cases hBC : B = C
  · subst hBC
    obtain ⟨l, h1, h2⟩ := two A B
    exact ⟨l, h1, h2, h2⟩
  rcases between_trichotomy (Line := L') hc (e.pt_injective.ne hAB) (e.pt_injective.ne hAC)
    (e.pt_injective.ne hBC) with h | h | h
  · exact (collinear_of_between (Line := CoordLine ℝ 3) ((e.between_iff _ _ _).1 h)).swap12
  · exact collinear_of_between (Line := CoordLine ℝ 3) ((e.between_iff _ _ _).1 h)
  · exact (collinear_of_between (Line := CoordLine ℝ 3) ((e.between_iff _ _ _).1 h)).swap23

/-- **An extension of `Coord ℝ 3` to a geometry of space with I–V adds no point.** -/
theorem ext_pt_surjective
    (e : SpaceEmbedding (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) P' L' Pl') :
    Function.Surjective e.pt := by
  obtain ⟨α, hOα, hE1α, hE2α⟩ := exists_plane (Plane := CoordPlane ℝ 3) not_collinear_std
  have hE3 : (AffPt.ofV ![0, 0, 1] : Coord ℝ 3) ∉ α := fun h =>
    not_coplanar_std α hOα hE1α hE2α h
  obtain ⟨ℓ, ι, hℓ, hiso, hbtw, -⟩ := exists_metric_emb (P := P') (L := L') (e.plane α)
  have hinj : Function.Injective ι := emb_injective hℓ hiso
  have hℓ₁ : IsLen (fun X Y : Coord ℝ 3 => ℓ (e.pt X) (e.pt Y)) :=
    ⟨fun A => hℓ.self _, fun A B h => hℓ.pos _ _ (e.pt_injective.ne h),
      fun A B C D hAB hCD => (e.segCong_iff A B C D).symm.trans
        (hℓ.cong _ _ _ _ (e.pt_injective.ne hAB) (e.pt_injective.ne hCD)),
      fun A B C h => hℓ.add _ _ _ ((e.between_iff A B C).2 h)⟩
  obtain ⟨c, hc, hsq⟩ := coord_len_sq hℓ₁
  have hf : ∀ X Y : Coord ℝ 3, Coord.ip (ι (e.pt Y) - ι (e.pt X)) (ι (e.pt Y) - ι (e.pt X)) =
      c ^ 2 * Coord.ip (Y - X) (Y - X) := fun X Y => by
    rw [← hiso]
    exact hsq X Y
  -- the composite map is affine along every line
  have key : ∀ (U V : Coord ℝ 3) (t : ℝ), U ≠ V →
      ι (e.pt (t • (V - U) + U)) = t • (ι (e.pt V) - ι (e.pt U)) + ι (e.pt U) := by
    intro U V t hUV
    have hfUV : ι (e.pt U) ≠ ι (e.pt V) := hinj.ne (e.pt_injective.ne hUV)
    have hcol : Collinear (Line := L') (e.pt U) (e.pt V) (e.pt (t • (V - U) + U)) :=
      ⟨e.line (AffLine.through U V hUV), (e.mem_iff _ _).2 (AffLine.left_mem_through hUV),
        (e.mem_iff _ _).2 (AffLine.right_mem_through hUV),
        (e.mem_iff _ _).2 ((AffLine.mem_through_iff hUV).2 ⟨t, rfl⟩)⟩
    have hc' := emb_collinear (L := L') hℓ hiso hbtw hcol
    obtain ⟨s, hs⟩ := (AffLine.mem_through_iff hfUV).1 (mem_of_collinear hc' hfUV
      (AffLine.left_mem_through hfUV) (AffLine.right_mem_through hfUV))
    have hD : 0 < Coord.ip (V - U) (V - U) := Coord.ip_self_pos (sub_ne_zero.2 hUV.symm)
    have hcD : 0 < c ^ 2 * Coord.ip (V - U) (V - U) := by positivity
    have e0 := hf U V
    have e1 := hf U (t • (V - U) + U)
    have e2 := hf V (t • (V - U) + U)
    have v1 : t • (V - U) + U - U = t • (V - U) := add_sub_cancel_right _ _
    have v2 : t • (V - U) + U - V = (t - 1) • (V - U) := by
      rw [sub_smul, one_smul]
      abel
    have w1 : s • (ι (e.pt V) - ι (e.pt U)) + ι (e.pt U) - ι (e.pt U) =
        s • (ι (e.pt V) - ι (e.pt U)) := add_sub_cancel_right _ _
    have w2 : s • (ι (e.pt V) - ι (e.pt U)) + ι (e.pt U) - ι (e.pt V) =
        (s - 1) • (ι (e.pt V) - ι (e.pt U)) := by
      rw [sub_smul, one_smul]
      abel
    rw [hs, w1, Coord.ip_smul_left, Coord.ip_smul_right, e0, v1, Coord.ip_smul_left,
      Coord.ip_smul_right] at e1
    rw [hs, w2, Coord.ip_smul_left, Coord.ip_smul_right, e0, v2, Coord.ip_smul_left,
      Coord.ip_smul_right] at e2
    have h1 : s ^ 2 = t ^ 2 := by
      have h : (s ^ 2 - t ^ 2) * (c ^ 2 * Coord.ip (V - U) (V - U)) = 0 := by
        linear_combination e1
      rcases mul_eq_zero.1 h with h | h
      · linarith
      · exact absurd h hcD.ne'
    have h2 : (s - 1) ^ 2 = (t - 1) ^ 2 := by
      have h : ((s - 1) ^ 2 - (t - 1) ^ 2) * (c ^ 2 * Coord.ip (V - U) (V - U)) = 0 := by
        linear_combination e2
      rcases mul_eq_zero.1 h with h | h
      · linarith
      · exact absurd h hcD.ne'
    have hst : s = t := by linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h2
    rw [hs, hst]
  -- the old points contain, with two points, every point of their line
  have hS : LineClosed (L := L') (Set.range e.pt) := by
    rintro _ _ X' hUV ⟨U, rfl⟩ ⟨V, rfl⟩ hcol
    have hUV0 : U ≠ V := fun h => hUV (by rw [h])
    have hfUV : ι (e.pt U) ≠ ι (e.pt V) := hinj.ne hUV
    have hc' := emb_collinear (L := L') hℓ hiso hbtw hcol
    obtain ⟨t, ht⟩ := (AffLine.mem_through_iff hfUV).1 (mem_of_collinear hc' hfUV
      (AffLine.left_mem_through hfUV) (AffLine.right_mem_through hfUV))
    refine ⟨t • (V - U) + U, hinj ?_⟩
    rw [ht]
    exact key U V t hUV0
  have hplane : ∀ X' : P', X' ∈ e.plane α → X' ∈ Set.range e.pt :=
    plane_closure (L := L') hS (e.plane α) ((e.memPlane_iff _ _).2 hOα)
      ((e.memPlane_iff _ _).2 hE1α) ((e.memPlane_iff _ _).2 hE2α)
      (fun h => not_collinear_std (ext_collinear_rev e h)) ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩
  have hall : ∀ X' : P', X' ∈ Set.range e.pt :=
    space_closure (L := L') hS (e.plane α) hplane ⟨AffPt.ofV ![0, 0, 1], rfl⟩
      (fun h => hE3 ((e.memPlane_iff _ _).1 h))
  intro Q
  obtain ⟨X, hX⟩ := hall Q
  exact ⟨X, hX⟩

end Model

/-- **The real co-ordinate space satisfies the Axiom of Completeness**: the hypotheses of the units
`s8.bolzano` and `s8.real_numbers` are satisfied by `Coord ℝ 3`. -/
theorem spaceComplete_coord_real :
    SpaceComplete (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) := by
  intro P' L' Pl' _ _ _ _ _ hG e
  have hpt := ext_pt_surjective (hG := hG) e
  refine ⟨hpt, ?_, ?_⟩
  · intro l'
    obtain ⟨A', B', hAB, hA, hB⟩ := exists_two_points (Point := P') l'
    obtain ⟨A, rfl⟩ := hpt A'
    obtain ⟨B, rfl⟩ := hpt B'
    have hAB0 : A ≠ B := fun h => hAB (by rw [h])
    obtain ⟨l, h1, h2⟩ := exists_line (Line := CoordLine ℝ 3) hAB0
    exact ⟨l, line_unique hAB ((e.mem_iff _ _).2 h1) ((e.mem_iff _ _).2 h2) hA hB⟩
  · intro α'
    obtain ⟨A', B', C', hA, hB, hC, hn⟩ :=
      SpaceConnection.ax_I7_plane (Point := P') (Line := L') α'
    obtain ⟨A, rfl⟩ := hpt A'
    obtain ⟨B, rfl⟩ := hpt B'
    obtain ⟨C, rfl⟩ := hpt C'
    have hn0 : ¬Collinear (Line := CoordLine ℝ 3) A B C := by
      rintro ⟨l, h1, h2, h3⟩
      exact hn ⟨e.line l, (e.mem_iff _ _).2 h1, (e.mem_iff _ _).2 h2, (e.mem_iff _ _).2 h3⟩
    obtain ⟨α, h1, h2, h3⟩ := exists_plane (Plane := CoordPlane ℝ 3) hn0
    exact ⟨α, plane_unique hn ((e.memPlane_iff _ _).2 h1) ((e.memPlane_iff _ _).2 h2)
      ((e.memPlane_iff _ _).2 h3) hA hB hC⟩

end CC

end HilbertFoundations
