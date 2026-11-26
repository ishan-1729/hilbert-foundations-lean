import HilbertFoundations.CongruenceCloseAux2

/-!
# Helper module for `CongruenceClose.lean`: Theorem 18 for figures

This module contains no unit of Hilbert's text. Space geometry with groups I, II, IV in which a
plane exists. For congruent figures `f`, `g` and a new point `Q`:

* `theorem18_exists`: a point `Q'` with `(f, Q)` congruent to `(g, Q')`. If the figure is contained
  in a line, Theorem 17 in suitable planes; otherwise three non-collinear points of `f` span a
  plane `α` with a distance-preserving map `φ` onto the plane of the corresponding points
  (`Frame.plane_iso`), and `Q'` is `φ Q` (if `Q ∈ α`), or the image of `Q` in a tetrahedral frame:
  the frame of a fourth point of `f` off `α` (`Tet.extend`, `Tet.rigid`), or, if `f` lies in `α`,
  any frame of `φ` (`exists_tet`);
* `theorem18_unique`: if `f` has four points not in a plane, `Q'` is unique (`Tet.unique`, and
  `theorem18_unique_of_coplanar` for `Q ∈ α`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

section Figures

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hSC : SpaceCongruence P L Pl]
include hSC

local notation "𝔽" => (spaceFrame (P := P) (L := L) (Pl := Pl))

/-- A point repeated and another point are collinear (space geometry). -/
theorem collinear_self_left (X Y : P) : Collinear (Line := L) X X Y := by
  by_cases h : X = Y
  · obtain ⟨l, hl⟩ := line_through_space (L := L) (Pl := Pl) X
    exact ⟨l, hl, hl, h ▸ hl⟩
  · obtain ⟨l, h1, h2⟩ := exists_line (Line := L) h
    exact ⟨l, h1, h1, h2⟩

/-- A figure all of whose triples are collinear lies on a line. -/
theorem line_of_collinear {n : ℕ} (f : Fin n → P)
    (h : ∀ a b c, Collinear (Line := L) (f a) (f b) (f c)) : ∃ l : L, ∀ i, f i ∈ l := by
  by_cases hd : ∃ i j, f i ≠ f j
  · obtain ⟨i, j, hij⟩ := hd
    exact ⟨line (Line := L) (f i) (f j) hij, fun k =>
      mem_of_collinear (h i j k) hij (mem_line_left _) (mem_line_right _)⟩
  · push Not at hd
    rcases isEmpty_or_nonempty (Fin n) with he | ⟨⟨i₀⟩⟩
    · obtain ⟨A, -, -, -, -⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L)
        (Plane := Pl)
      obtain ⟨l, -⟩ := line_through_space (L := L) (Pl := Pl) A
      exact ⟨l, fun i => he.elim i⟩
    · obtain ⟨l, hl⟩ := line_through_space (L := L) (Pl := Pl) (f i₀)
      exact ⟨l, fun i => hd i i₀ ▸ hl⟩

/-- In a space geometry having a plane, a line and a point lie in a plane. -/
theorem plane_through_line_point [Nonempty Pl] (l : L) (Q : P) :
    ∃ α : Pl, (∀ Z : P, Z ∈ l → Z ∈ α) ∧ Q ∈ α := by
  obtain ⟨U, V, hUV, hU, hV⟩ := exists_two_points (Point := P) l
  have key : ∀ W : P, W ∉ l → ∃ α : Pl, (∀ Z : P, Z ∈ l → Z ∈ α) ∧ W ∈ α := fun W hW => by
    obtain ⟨α, h1, h2, h3⟩ := exists_plane (Plane := Pl) (nc_of hU hV hUV hW).1
    exact ⟨α, liesInPlane_of_mem hUV hU hV h1 h2, h3⟩
  by_cases hQ : Q ∈ l
  · obtain β : Pl := Classical.arbitrary Pl
    obtain ⟨A, B, C, -, -, -, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) β
    have hW : ∃ W : P, W ∉ l := by
      by_contra h
      push Not at h
      exact hn ⟨l, h A, h B, h C⟩
    obtain ⟨W, hW⟩ := hW
    obtain ⟨α, h1, -⟩ := key W hW
    exact ⟨α, h1, h1 Q hQ⟩
  · exact key Q hQ

variable {n : ℕ} {f g : Fin n → P}

/-- Three non-collinear points of a figure and the corresponding points of a congruent figure: the
distance-preserving map of their planes. -/
theorem figure_plane_iso (hc : CongruentFigures (L := L) f g) {a b c : Fin n}
    (hn : ¬Collinear (Line := L) (f a) (f b) (f c)) :
    ∃ (α α' : Pl) (φ : P → P), f a ∈ α ∧ f b ∈ α ∧ f c ∈ α ∧ IsoOn {Z : P | Z ∈ α} φ ∧
      (∀ Z : P, Z ∈ α → φ Z ∈ α') ∧ φ (f a) = g a ∧ φ (f b) = g b ∧ φ (f c) = g c := by
  obtain ⟨hab', hcb', hac'⟩ := (𝔽).ne hn
  have hab : a ≠ b := fun e => hab' (by rw [e])
  have hbc : b ≠ c := fun e => hcb' (by rw [e])
  have hac : a ≠ c := fun e => hac' (by rw [e])
  have hn' : ¬Collinear (Line := L) (g a) (g b) (g c) := fun hg =>
    hn (congruentFigures_collinear_gen 𝔽 (congruentFigures_symm hc) hab hbc hac hg)
  obtain ⟨α, ha, hb, hc'⟩ := exists_plane (Plane := Pl) hn
  obtain ⟨α', ha', hb', hc''⟩ := exists_plane (Plane := Pl) hn'
  obtain ⟨φ, e1, e2, e3, hmap, hiso⟩ := (𝔽).plane_iso (isPl_plane α) (isPl_plane α') ha hb hc'
    hn ha' hb' hc'' (hc.2.1.ne hab) (hc.2.1.ne hac) (hc.2.1.ne hbc) (hc.2.2.1 a b hab)
    (hc.2.2.1 a c hac) (hc.2.2.1 b c hbc)
  exact ⟨α, α', φ, ha, hb, hc', hiso, hmap, e1, e2, e3⟩

/-- A point off the plane of three points of the figure with the distances of `X'` from the
corresponding points: `X'` has its distances from the images of all points of the plane. -/
theorem fig_good {α : Pl} {φ : P → P} {a b c : Fin n} (hiso : IsoOn {Z : P | Z ∈ α} φ)
    (ha : f a ∈ α) (hb : f b ∈ α) (hc' : f c ∈ α)
    (hn : ¬Collinear (Line := L) (f a) (f b) (f c)) (ea : φ (f a) = g a) (eb : φ (f b) = g b)
    (ec : φ (f c) = g c) {X X' : P} (hX : X ∉ α) (da : X' ≠ g a ∧ SegCong X (f a) X' (g a))
    (db : X' ≠ g b ∧ SegCong X (f b) X' (g b)) (dc : X' ≠ g c ∧ SegCong X (f c) X' (g c)) :
    GoodAt α φ X X' := by
  rw [← ea] at da
  rw [← eb] at db
  rw [← ec] at dc
  exact fun Z hZ => (𝔽).iso_outside (isPl_plane α) hiso ha hb hc' hn hX da db dc hZ

/-- The points of the figure in the plane of three of its points correspond under the map of the
plane. -/
theorem fig_in (hc : CongruentFigures (L := L) f g) {α α' : Pl} {φ : P → P} {a b c : Fin n}
    (hiso : IsoOn {Z : P | Z ∈ α} φ) (hmap : ∀ Z : P, Z ∈ α → φ Z ∈ α') (ha : f a ∈ α)
    (hb : f b ∈ α) (hc' : f c ∈ α) (hn : ¬Collinear (Line := L) (f a) (f b) (f c))
    (ea : φ (f a) = g a) (eb : φ (f b) = g b) (ec : φ (f c) = g c) {i : Fin n} (hi : f i ∈ α) :
    φ (f i) = g i := by
  by_cases hia : i = a
  · rw [hia]; exact ea
  by_cases hib : i = b
  · rw [hib]; exact eb
  by_cases hic : i = c
  · rw [hic]; exact ec
  have hn' := (𝔽).iso_not_collinear hiso ha hb hc' hn
  have m1 := hmap _ ha
  have m2 := hmap _ hb
  have m3 := hmap _ hc'
  have i1 := hiso (f a) ha (f i) hi (hc.1.ne (Ne.symm hia))
  have i2 := hiso (f b) hb (f i) hi (hc.1.ne (Ne.symm hib))
  have i3 := hiso (f c) hc' (f i) hi (hc.1.ne (Ne.symm hic))
  rw [ea] at i1 m1
  rw [eb] at i2 m2
  rw [ec] at i3 m3
  rw [ea, eb, ec] at hn'
  exact ((𝔽).eq_of_equidistant_space (isPl_plane α') m1 m2 m3 (hmap _ hi) hn' i1.1.symm
    i2.1.symm i3.1.symm (hc.2.1.ne hia) (hc.2.1.ne hib) (hc.2.1.ne hic)
    (SegmentCongruence.ax_IV2 (Line := L) (f a) (f i) (g a) (φ (f i)) (g a) (g i)
      (hc.1.ne (Ne.symm hia)) i1.1 (hc.2.1.ne (Ne.symm hia)) i1.2 (hc.2.2.1 a i (Ne.symm hia)))
    (SegmentCongruence.ax_IV2 (Line := L) (f b) (f i) (g b) (φ (f i)) (g b) (g i)
      (hc.1.ne (Ne.symm hib)) i2.1 (hc.2.1.ne (Ne.symm hib)) i2.2 (hc.2.2.1 b i (Ne.symm hib)))
    (SegmentCongruence.ax_IV2 (Line := L) (f c) (f i) (g c) (φ (f i)) (g c) (g i)
      (hc.1.ne (Ne.symm hic)) i3.1 (hc.2.1.ne (Ne.symm hic)) i3.2
      (hc.2.2.1 c i (Ne.symm hic)))).symm

/-- **Theorem 18, existence, for a figure with three non-collinear points**: the distances. -/
theorem theorem18_exists_of_triangle (hc : CongruentFigures (L := L) f g) {a b c : Fin n}
    (hn : ¬Collinear (Line := L) (f a) (f b) (f c)) {Q : P} (hQ : Q ∉ Set.range f) :
    ∃ Q', ∀ i, Q' ≠ g i ∧ SegCong (f i) Q (g i) Q' := by
  obtain ⟨α, α', φ, ha, hb, hc', hiso, hmap, ea, eb, ec⟩ := figure_plane_iso hc hn
  have hQf : ∀ i, Q ≠ f i := fun i e => hQ ⟨i, e.symm⟩
  have fin : ∀ i, f i ∈ α → φ (f i) = g i := fun i hi =>
    fig_in hc hiso hmap ha hb hc' hn ea eb ec hi
  have fout : ∀ i, f i ∉ α → GoodAt α φ (f i) (g i) := fun i hi => by
    have hia : i ≠ a := fun e => hi (e ▸ ha)
    have hib : i ≠ b := fun e => hi (e ▸ hb)
    have hic : i ≠ c := fun e => hi (e ▸ hc')
    exact fig_good hiso ha hb hc' hn ea eb ec hi ⟨hc.2.1.ne hia, hc.2.2.1 i a hia⟩
      ⟨hc.2.1.ne hib, hc.2.2.1 i b hib⟩ ⟨hc.2.1.ne hic, hc.2.2.1 i c hic⟩
  by_cases hQα : Q ∈ α
  · refine ⟨φ Q, fun i => ?_⟩
    by_cases hi : f i ∈ α
    · have := hiso (f i) hi Q hQα (hQf i).symm
      rw [fin i hi] at this
      exact ⟨this.1.symm, this.2⟩
    · have := fout i hi Q hQα
      exact ⟨this.1.symm, this.2⟩
  by_cases hall : ∀ i, f i ∈ α
  · obtain ⟨D, D', T⟩ := exists_tet hiso hmap
    have hQ' : ∃ Q', GoodAt α φ Q Q' := by
      by_cases e : Q = D
      · exact ⟨D', e ▸ T.good⟩
      · obtain ⟨Q', h, -, -⟩ := T.extend hQα e
        exact ⟨Q', h⟩
    obtain ⟨Q', gQ⟩ := hQ'
    refine ⟨Q', fun i => ?_⟩
    have := gQ (f i) (hall i)
    rw [fin i (hall i)] at this
    exact ⟨this.1, segCong_swap (L := L) this.2⟩
  · push Not at hall
    obtain ⟨d, hd⟩ := hall
    have T : Tet α φ (f d) (g d) := ⟨hiso, hd, fout d hd⟩
    obtain ⟨Q', gQ, hQ'D, sQ⟩ := T.extend hQα (hQf d)
    refine ⟨Q', fun i => ?_⟩
    by_cases hi : f i ∈ α
    · have := gQ (f i) hi
      rw [fin i hi] at this
      exact ⟨this.1, segCong_swap (L := L) this.2⟩
    by_cases hid : i = d
    · rw [hid]; exact ⟨hQ'D, segCong_swap (L := L) sQ⟩
    · have := T.rigid hQα (hQf d) hi (hc.1.ne hid) (hQf i) gQ hQ'D sQ (fout i hi)
        (hc.2.1.ne hid) (hc.2.2.1 i d hid)
      exact ⟨this.1, segCong_swap (L := L) this.2⟩

/-- **Theorem 18, existence** (space geometry with groups I, II, IV having a plane). -/
theorem theorem18_exists [Nonempty Pl] (hc : CongruentFigures (L := L) f g) {Q : P}
    (hQ : Q ∉ Set.range f) :
    ∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') := by
  by_cases h3 : ∃ a b c, ¬Collinear (Line := L) (f a) (f b) (f c)
  · obtain ⟨a, b, c, hn⟩ := h3
    obtain ⟨Q', h⟩ := theorem18_exists_of_triangle hc hn hQ
    exact ⟨Q', congruentFigures_snoc 𝔽 hc hQ (fun ⟨i, hi⟩ => (h i).1 hi.symm) (fun i => (h i).2)⟩
  · push Not at h3
    have h3' : ∀ a b c, Collinear (Line := L) (g a) (g b) (g c) := by
      intro a b c
      by_cases hab : a = b
      · rw [hab]; exact collinear_self_left (Pl := Pl) _ _
      by_cases hbc : b = c
      · rw [hbc]; exact (collinear_self_left (Pl := Pl) _ _).swap13
      by_cases hac : a = c
      · rw [hac]; exact (collinear_self_left (Pl := Pl) _ _).swap23
      exact congruentFigures_collinear_gen 𝔽 hc hab hbc hac (h3 a b c)
    obtain ⟨l, hl⟩ := line_of_collinear (Pl := Pl) f h3
    obtain ⟨l', hl'⟩ := line_of_collinear (Pl := Pl) g h3'
    obtain ⟨α, hlα, hQα⟩ := plane_through_line_point (Pl := Pl) l Q
    obtain ⟨α', hlα', -⟩ := plane_through_line_point (Pl := Pl) l' Q
    obtain ⟨Q', -, h⟩ := theorem17_space (fun i => hlα _ (hl i)) (fun i => hlα' _ (hl' i)) hc
      hQα hQ
    exact ⟨Q', h⟩

/-- **Theorem 18, uniqueness** (space geometry with groups I, II, IV having a plane): if the
figure has four points not in a plane. -/
theorem theorem18_unique [Nonempty Pl] (hc : CongruentFigures (L := L) f g) {Q : P}
    (h4 : ∃ i j k m : Fin n, ¬Coplanar (Plane := Pl) (f i) (f j) (f k) (f m)) {Q' Q'' : P}
    (h1 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'))
    (h2 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'')) :
    Q' = Q'' := by
  obtain ⟨a, b, c, d, h4⟩ := h4
  have hn : ¬Collinear (Line := L) (f a) (f b) (f c) := by
    rintro ⟨l, l1, l2, l3⟩
    obtain ⟨α, hl, hd⟩ := plane_through_line_point (Pl := Pl) l (f d)
    exact h4 ⟨α, hl _ l1, hl _ l2, hl _ l3, hd⟩
  obtain ⟨α, α', φ, ha, hb, hc', hiso, hmap, ea, eb, ec⟩ := figure_plane_iso hc hn
  have hd : f d ∉ α := fun h => h4 ⟨α, ha, hb, hc', h⟩
  have ext : ∀ {R : P}, CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P)
      (Fin.snoc g R) → (∀ m, SegCong (f m) Q (g m) R) ∧ (∀ m, f m ≠ Q) ∧ (∀ m, g m ≠ R) := by
    intro R h
    refine ⟨fun m => ?_, fun m e => ?_, fun m e => ?_⟩
    · have := h.2.2.1 (Fin.castSucc m) (Fin.last n) (Fin.castSucc_lt_last m).ne
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using this
    · exact (Fin.castSucc_lt_last m).ne (h.1 (by
        simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact e))
    · exact (Fin.castSucc_lt_last m).ne (h.2.1 (by
        simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact e))
  obtain ⟨s1, nf, n1⟩ := ext h1
  obtain ⟨s2, -, n2⟩ := ext h2
  by_cases hQα : Q ∈ α
  · exact theorem18_unique_of_coplanar (Pl := Pl) hc hn ⟨ha, hb, hc'⟩ hQα h1 h2
  · have hia : d ≠ a := fun e => hd (e ▸ ha)
    have hib : d ≠ b := fun e => hd (e ▸ hb)
    have hic : d ≠ c := fun e => hd (e ▸ hc')
    have T : Tet α φ (f d) (g d) := ⟨hiso, hd, fig_good hiso ha hb hc' hn ea eb ec hd
      ⟨hc.2.1.ne hia, hc.2.2.1 d a hia⟩ ⟨hc.2.1.ne hib, hc.2.2.1 d b hib⟩
      ⟨hc.2.1.ne hic, hc.2.2.1 d c hic⟩⟩
    have good : ∀ {R : P}, (∀ m, SegCong (f m) Q (g m) R) → (∀ m, g m ≠ R) → GoodAt α φ Q R :=
      fun s nR => fig_good hiso ha hb hc' hn ea eb ec hQα
        ⟨(nR a).symm, segCong_swap (L := L) (s a)⟩ ⟨(nR b).symm, segCong_swap (L := L) (s b)⟩
        ⟨(nR c).symm, segCong_swap (L := L) (s c)⟩
    exact T.unique hQα (nf d).symm (good s1 n1) (n1 d).symm (segCong_swap (L := L) (s1 d))
      (good s2 n2) (n2 d).symm (segCong_swap (L := L) (s2 d))

end Figures

end HilbertFoundations
