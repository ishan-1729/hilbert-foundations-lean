import HilbertFoundations.CompletenessCloseAux7

/-!
# The consequences of the Axiom of Completeness (§ 8): the units `s8.bolzano`, `s8.real_numbers`

This file proves the two units of `Basic.lean` that are only stated there:

* `s8.bolzano` — `completenessGivesBolzano : CompletenessGivesBolzano`: in a geometry of space with
  groups I–V and the Axiom of Completeness (`SpaceComplete`), every infinite set of points between
  two points of a line has a point of condensation;
* `s8.real_numbers` — `completenessGivesReals : CompletenessGivesReals`: in such a geometry the
  points of every segment correspond one-to-one and in order to the real numbers.

**Proof.** Every geometry of space with I–V is embedded into the analytic geometry `Coord ℝ 3` of
Analytic.lean (`CC.PreEmb`):

* if it has a plane, by rectangular co-ordinates: the field of segments of a plane (Pascal.lean) is
  archimedean, hence a subfield of `ℝ`, which gives real charts of the planes and a length of
  segments (`CompletenessCloseAux.lean`); Stewart's relation makes the functions `QX² - OX²` affine
  along every line, which gives three rectangular co-ordinates in which the length is euclidean
  (`CompletenessCloseAux2.lean`), and the resulting isometric map carries lines to lines, planes to
  planes and congruent angles to congruent angles (`CompletenessCloseAux3.lean`,
  `CompletenessCloseAux5.lean`);
* if it has no plane (this is not excluded by I–V: then, by I 3, all points lie on one line), by
  the real co-ordinate of the line given by Hölder's theorem, from the linear axioms alone
  (`CompletenessCloseAux4.lean`); the image is then contained in the first axis.

The image of the embedding is a system inside the geometry `Coord ℝ 3`, which satisfies I–V; after
transport to the universes of the given system and adjustment of the congruences on the degenerate
tuples, which the axioms do not constrain (`CompletenessCloseAux6.lean`), the Axiom of Completeness
applies and shows that the embedding is onto. So the geometry has a plane and is carried bijectively
onto `Coord ℝ 3`, betweenness corresponding to betweenness (`CC.exists_bijective_emb`). A line is
then parametrised by `ℝ` (`CC.line_param`), and the two claims are the theorem of
Bolzano–Weierstrass on `[0, 1]` and the order isomorphism of `(0, 1)` with `ℝ`.

**The hypotheses are satisfiable.** The two theorems are not vacuous: the analytic geometry
`Coord ℝ 3` satisfies I–V (`real_spaceGeometry`, Analytic.lean) and the Axiom of Completeness as
formulated in Basic.lean (`CC.spaceComplete_coord_real`, `CompletenessCloseAux7.lean`: an extension
of `Coord ℝ 3` satisfying I–V is mapped isometrically into `Coord ℝ 3`, and the composite map of
`Coord ℝ 3` into itself, a similarity, is affine along every line, so that the old points are all
the points). The instances `bolzano_coord_real` and `segmentRealCorrespondence_coord_real` of the
two units are stated at the end of the file.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

namespace CC

section Final

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hG : SpaceGeometry P L Pl]

include hG

/-- **A complete geometry of space with two distinct points is carried bijectively onto
`Coord ℝ 3`.** -/
theorem exists_bijective_emb (hc : SpaceComplete P L Pl) {A B : P} (hAB : A ≠ B) :
    ∃ e : PreEmb P L Pl, Function.Surjective e.pt := by
  by_cases hPl : Nonempty Pl
  · obtain ⟨α₀⟩ := hPl
    obtain ⟨e⟩ := exists_preEmb (P := P) (L := L) α₀
    exact ⟨e, e.surjective_of_complete hc⟩
  · have : IsEmpty Pl := not_nonempty_iff.1 hPl
    obtain ⟨e, he⟩ := exists_preEmb_line (L := L) (Pl := Pl) hAB
    exfalso
    obtain ⟨X, hX⟩ := e.surjective_of_complete hc (AffPt.ofV ![0, 1, 0])
    have h1 := he X
    rw [hX] at h1
    simp at h1

/-- **The real parameter of a line** in a geometry carried bijectively onto `Coord ℝ 3`. -/
theorem line_param (e : PreEmb P L Pl) (hs : Function.Surjective e.pt) {A B : P} (hAB : A ≠ B) :
    ∃ g : ℝ → P, g 0 = A ∧ g 1 = B ∧ Function.Injective g ∧
      (∀ X : P, Collinear (Line := L) A B X ↔ ∃ s : ℝ, X = g s) ∧
      ∀ r s t : ℝ, Between (g r) (g s) (g t) ↔ (r < s ∧ s < t) ∨ (t < s ∧ s < r) := by
  have hab : e.pt A ≠ e.pt B := e.pt_injective.ne hAB
  have hd : e.pt B - e.pt A ≠ 0 := sub_ne_zero.2 hab.symm
  choose g hg using fun s : ℝ => hs (s • (e.pt B - e.pt A) + e.pt A)
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · apply e.pt_injective
    rw [hg, zero_smul, zero_add]
  · apply e.pt_injective
    rw [hg, one_smul, sub_add_cancel]
  · intro s t h
    have h1 := congrArg e.pt h
    rw [hg, hg] at h1
    exact (smul_add_inj hd).1 h1
  · intro X
    constructor
    · intro hc
      have hc' := (e.collinear_iff A B X).2 hc
      have hX : e.pt X ∈ AffLine.through (e.pt A) (e.pt B) hab :=
        mem_of_collinear hc' hab (AffLine.left_mem_through hab) (AffLine.right_mem_through hab)
      obtain ⟨r, hr⟩ := (AffLine.mem_through_iff hab).1 hX
      exact ⟨r, e.pt_injective (by rw [hr, hg])⟩
    · rintro ⟨s, rfl⟩
      rw [← e.collinear_iff]
      exact ⟨AffLine.through (e.pt A) (e.pt B) hab, AffLine.left_mem_through hab,
        AffLine.right_mem_through hab, (AffLine.mem_through_iff hab).2 ⟨s, hg s⟩⟩
  · intro r s t
    rw [← e.between_iff, hg, hg, hg, AffPt.between_iff]
    exact sbtw_param_iff hd r s t

/-- **Bolzano's theorem** in a geometry carried bijectively onto `Coord ℝ 3`. -/
theorem bolzano_of_bijective (e : PreEmb P L Pl) (hs : Function.Surjective e.pt) :
    BolzanoProperty P := by
  intro A B S hAB hS hinf
  obtain ⟨g, g0, g1, ginj, gcol, gbtw⟩ := line_param e hs hAB
  have hpar : ∀ s : ℝ, g s ∈ S → 0 < s ∧ s < 1 := by
    intro s hs'
    have hb : Between (g 0) (g s) (g 1) := by rw [g0, g1]; exact hS hs'
    rcases (gbtw 0 s 1).1 hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exfalso; linarith
  have hTsub : g ⁻¹' S ⊆ Set.Icc (0 : ℝ) 1 := fun s hs' =>
    ⟨(hpar s hs').1.le, (hpar s hs').2.le⟩
  have hSimg : S = g '' (g ⁻¹' S) := by
    ext X
    constructor
    · intro hX
      obtain ⟨s, rfl⟩ := (gcol X).1 (collinear_of_between (Line := L) (hS hX)).swap23
      exact ⟨s, hX, rfl⟩
    · rintro ⟨s, hs', rfl⟩
      exact hs'
  have hTinf : (g ⁻¹' S).Infinite := by
    intro hfin
    apply hinf
    rw [hSimg]
    exact hfin.image g
  obtain ⟨x, -, hx⟩ := hTinf.exists_accPt_of_subset_isCompact isCompact_Icc hTsub
  rw [accPt_iff_nhds] at hx
  refine ⟨g x, (gcol _).2 ⟨x, rfl⟩, ?_⟩
  intro U V hU hV hUV
  obtain ⟨u, rfl⟩ := (gcol U).1 hU
  obtain ⟨v, rfl⟩ := (gcol V).1 hV
  rw [gbtw] at hUV
  have hnb : Set.Ioo (min u v) (max u v) ∈ nhds x := by
    apply Ioo_mem_nhds
    · rcases hUV with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact lt_of_le_of_lt (min_le_left _ _) h1
      · exact lt_of_le_of_lt (min_le_right _ _) h1
    · rcases hUV with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact lt_of_lt_of_le h2 (le_max_right _ _)
      · exact lt_of_lt_of_le h2 (le_max_left _ _)
  obtain ⟨y, ⟨⟨hy1, hy2⟩, hyT⟩, hyx⟩ := hx _ hnb
  refine ⟨g y, hyT, fun h => hyx (ginj h), ?_⟩
  rw [gbtw]
  rcases le_total u v with huv | huv
  · rw [min_eq_left huv] at hy1
    rw [max_eq_right huv] at hy2
    exact Or.inl ⟨hy1, hy2⟩
  · rw [min_eq_right huv] at hy1
    rw [max_eq_left huv] at hy2
    exact Or.inr ⟨hy1, hy2⟩

/-- **The points of a segment correspond in order to the real numbers**, in a geometry carried
bijectively onto `Coord ℝ 3`. -/
theorem reals_of_bijective (e : PreEmb P L Pl) (hs : Function.Surjective e.pt) :
    SegmentRealCorrespondence P := by
  intro A B hAB
  obtain ⟨g, g0, g1, ginj, gcol, gbtw⟩ := line_param e hs hAB
  have hpar : ∀ X : Seg A B, ∃ s : ℝ, (X : P) = g s ∧ 0 < s ∧ s < 1 := by
    intro X
    have hb : Between A (X : P) B := X.2
    obtain ⟨s, hs'⟩ := (gcol X).1 (collinear_of_between (Line := L) hb).swap23
    refine ⟨s, hs', ?_⟩
    have hb' : Between (g 0) (g s) (g 1) := by rw [g0, g1, ← hs']; exact hb
    rcases (gbtw 0 s 1).1 hb' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exfalso; linarith
  choose tp htp using hpar
  have hmem : ∀ X : Seg A B, 2 * tp X - 1 ∈ Set.Ioo (-1 : ℝ) 1 := fun X =>
    ⟨by linarith [(htp X).2.1], by linarith [(htp X).2.2]⟩
  have hlt : ∀ X Y : Seg A B,
      (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp X - 1, hmem X⟩ <
        (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp Y - 1, hmem Y⟩ ↔ tp X < tp Y := by
    intro X Y
    rw [OrderIso.lt_iff_lt, Subtype.mk_lt_mk]
    constructor <;> intro h <;> linarith
  have hinj : Function.Injective
      (fun X : Seg A B => (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp X - 1, hmem X⟩) := by
    intro X Y h
    have h' : (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp X - 1, hmem X⟩ =
        (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp Y - 1, hmem Y⟩ := h
    have h1 : ¬tp X < tp Y := fun k => ((hlt X Y).2 k).ne h'
    have h2 : ¬tp Y < tp X := fun k => ((hlt Y X).2 k).ne h'.symm
    have h3 : tp X = tp Y := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    apply Subtype.ext
    rw [(htp X).1, (htp Y).1, h3]
  have hsurj : Function.Surjective
      (fun X : Seg A B => (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp X - 1, hmem X⟩) := by
    intro r
    have hq := (orderIsoIooNegOneOne ℝ r).2
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = ((orderIsoIooNegOneOne ℝ r : ℝ) + 1) / 2 := ⟨_, rfl⟩
    have hs0 : 0 < s := by have := hq.1; rw [hs_def]; linarith
    have hs1 : s < 1 := by have := hq.2; rw [hs_def]; linarith
    have hb : Between A (g s) B := by
      have h := (gbtw 0 s 1).2 (Or.inl ⟨hs0, hs1⟩)
      rwa [g0, g1] at h
    have ht : tp ⟨g s, hb⟩ = s := ginj ((htp ⟨g s, hb⟩).1).symm
    refine ⟨⟨g s, hb⟩, ?_⟩
    show (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp ⟨g s, hb⟩ - 1, hmem ⟨g s, hb⟩⟩ = r
    rw [OrderIso.symm_apply_eq]
    apply Subtype.ext
    show 2 * tp ⟨g s, hb⟩ - 1 = (orderIsoIooNegOneOne ℝ r : ℝ)
    rw [ht, hs_def]
    ring
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun X Y => ?_⟩
  show Between A (X : P) (Y : P) ↔
    (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp X - 1, hmem X⟩ <
      (orderIsoIooNegOneOne ℝ).symm ⟨2 * tp Y - 1, hmem Y⟩
  rw [hlt]
  have h := gbtw 0 (tp X) (tp Y)
  rw [g0, ← (htp X).1, ← (htp Y).1] at h
  rw [h]
  constructor
  · rintro (⟨-, h2⟩ | ⟨-, h2⟩)
    · exact h2
    · exact absurd h2 (not_lt.2 (htp X).2.1.le)
  · intro h2
    exact Or.inl ⟨(htp X).2.1, h2⟩

end Final

end CC

/-- **[s8.bolzano] The Axiom of Completeness gives Bolzano's theorem** (with groups I–V). -/
theorem completenessGivesBolzano : CompletenessGivesBolzano.{u, v, w} := by
  intro P L Pl _ _ _ _ _ hG hc A B S hAB hS hinf
  obtain ⟨e, he⟩ := CC.exists_bijective_emb (hG := hG) hc hAB
  exact CC.bolzano_of_bijective (hG := hG) e he A B S hAB hS hinf

/-- **[s8.real_numbers] The Axiom of Completeness gives the correspondence between the points of a
segment and the real numbers** (with groups I–V). -/
theorem completenessGivesReals : CompletenessGivesReals.{u, v, w} := by
  intro P L Pl _ _ _ _ _ hG hc A B hAB
  obtain ⟨e, he⟩ := CC.exists_bijective_emb (hG := hG) hc hAB
  exact CC.reals_of_bijective (hG := hG) e he A B hAB

/-! ### The hypotheses are satisfied by the real co-ordinate space -/

/-- Bolzano's theorem in `Coord ℝ 3`, as an instance of `completenessGivesBolzano`: the hypotheses
of the unit `s8.bolzano` hold in the real co-ordinate space (`CC.spaceComplete_coord_real`). -/
theorem bolzano_coord_real : BolzanoProperty (Line := CoordLine ℝ 3) (Coord ℝ 3) :=
  completenessGivesBolzano (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) real_spaceGeometry
    CC.spaceComplete_coord_real

/-- The correspondence of the points of a segment of `Coord ℝ 3` with the real numbers, as an
instance of `completenessGivesReals`. -/
theorem segmentRealCorrespondence_coord_real : SegmentRealCorrespondence (Coord ℝ 3) :=
  completenessGivesReals (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) real_spaceGeometry
    CC.spaceComplete_coord_real

end HilbertFoundations
