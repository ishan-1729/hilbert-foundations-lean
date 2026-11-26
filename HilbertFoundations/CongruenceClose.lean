import HilbertFoundations.Congruence
import HilbertFoundations.CongruenceCloseAux5
import HilbertFoundations.CongruenceCloseAux6

/-!
# Closing the open units of `Congruence.lean`

This module closes the two units of `Congruence.lean` that were stated there without proof.

* **[th.18] Theorem 18** (congruent figures in space). The statement recorded in `Congruence.lean`
  (`SpaceCongruenceGivesTheorem18`: every space geometry with groups I, II, IV satisfies
  `Theorem18Statement`) is **false as stated** (`spaceCongruenceGivesTheorem18_false`): with the
  literal reading of Axiom I 7, a single line without planes is a space geometry, four of its points
  are vacuously "not in a plane", and a point has two images. It is **proved in corrected form**:
  * `theorem18`: `Theorem18Statement` holds in every space geometry (I, II, IV) that has a plane;
  * `theorem18_corrected` (`Theorem18Corrected`), with no extra hypothesis on the geometry:
    existence always holds, and uniqueness holds when the figure contains three points not in a
    straight line and a fourth point not in a plane with them;
  * `spaceCongruenceGivesTheorem18Corrected`: the corrected claim for every space geometry;
  * `theorem18_distinct` (`Theorem18Distinct`, the sharp form), with no extra hypothesis on the
    geometry: uniqueness holds when the figure contains four *distinct* points not in a plane.
    This is `Theorem18Statement` with the four points required to be distinct (which is what
    "four points" means, and is automatic where a plane exists: `theorem18Statement_iff_distinct`);
    it implies `Theorem18Corrected` (`theorem18Corrected_of_distinct`), and
    `spaceCongruenceGivesTheorem18Distinct` is the claim for every space geometry.

  The proof (helper modules `CongruenceCloseAux`–`CongruenceCloseAux4`, `CongruenceCloseAux6`) uses
  no perpendiculars to planes: three non-collinear points of the figure and the corresponding points
  determine a distance-preserving map of their planes (Theorem 17); a point off the plane with its
  image forms a "tetrahedral frame", in which every further point has exactly one image, found in a
  plane through the apex by Theorem 17 again; and sets of points with prescribed distances are
  closed under joining lines (the congruence theorems).

* **[s7.circle_properties] The known properties of the circle**: `circlePropertiesClaim` proves
  `CirclePropertiesClaim` as stated: the circle through three points (already in `Congruence.lean`),
  the congruence of the angles inscribed in the same segment (`inscribedAnglesCongruent`) and the
  theorem on the angles of an inscribed quadrilateral (`inscribedQuadrilateral`). The proof is
  analytic (helper module `CongruenceCloseAux5`): in the co-ordinates over the field of segments
  built for Pascal's theorem (helper modules of `Pascal.lean`, which use no property of circles),
  the cosine of `∠ACB` is the scalar product of `A - C`, `B - C` divided by the lengths, the side
  of the line `AB` on which `C` lies is the sign of a determinant, and for four points of a circle
  the scalar products and determinants at `C` and `D` are proportional.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

/-!
## Unit `th.18`: Theorem 18 (closed)

**Status.** proved (corrected): `theorem18` (every space geometry with groups I, II, IV having a
plane satisfies `Theorem18Statement`), `theorem18_distinct` (every space geometry with groups I, II,
IV satisfies `Theorem18Distinct`: uniqueness for four distinct points not in a plane),
`theorem18_corrected`, and the refutation `spaceCongruenceGivesTheorem18_false` of the claim
`SpaceCongruenceGivesTheorem18` as stated.
-/

section Theorem18

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P]

/-- **Theorem 18** (corrected as in `Theorem18Statement`) holds in every space geometry with groups
I, II, IV in which a plane exists. -/
theorem theorem18 [SpaceCongruence P L Pl] [Nonempty Pl] :
    Theorem18Statement (L := L) (Pl := Pl) P :=
  fun _ _ _ hc _ hQ => ⟨theorem18_exists hc hQ, fun h4 _ _ h1 h2 => theorem18_unique hc h4 h1 h2⟩

/-- **The claim `SpaceCongruenceGivesTheorem18` is false as stated**: the rational line without
planes is a space geometry with groups I, II, IV (literal reading of I 7) in which the uniqueness
clause of `Theorem18Statement` fails. -/
theorem spaceCongruenceGivesTheorem18_false : ¬SpaceCongruenceGivesTheorem18.{u, v, w} :=
  fun h => linePt_not_theorem18.{u, v, w}
    (h LinePt.{u} PUnit.{v + 1} PEmpty.{w + 1} LinePt.instSpaceCongruence)

/-- **Theorem 18, final corrected statement**: for congruent figures `(A, B, C, …)`,
`(A', B', C', …)` and a point `P` there is a point `P'` such that `(A, B, C, …, P)` and
`(A', B', C', …, P')` are congruent; if the figure `(A, B, C, …)` contains three points not in a
straight line and a fourth point not in a plane with them, `P'` is unique. -/
def Theorem18Corrected (P : Type u) {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ (n : ℕ) (f g : Fin n → P), CongruentFigures (L := L) f g → ∀ Q : P, Q ∉ Set.range f →
    (∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q')) ∧
    ((∃ i j k m : Fin n, ¬Collinear (Line := L) (f i) (f j) (f k) ∧
        ¬Coplanar (Plane := Pl) (f i) (f j) (f k) (f m)) →
      ∀ Q' Q'' : P, CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') →
        CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'') → Q' = Q'')

/-- **Theorem 18** in every space geometry with groups I, II, IV (no further hypothesis). -/
theorem theorem18_corrected [SpaceCongruence P L Pl] :
    Theorem18Corrected (L := L) (Pl := Pl) P := by
  intro n f g hc Q hQ
  refine ⟨theorem18_exists_all hc hQ, ?_⟩
  rintro ⟨i, j, k, m, hn, h4⟩ Q' Q'' h1 h2
  obtain ⟨α, -⟩ := exists_plane (Plane := Pl) hn
  have : Nonempty Pl := ⟨α⟩
  exact theorem18_unique hc ⟨i, j, k, m, h4⟩ h1 h2

/-- In a space geometry having a plane, four points not in a plane contain three points not in a
straight line: there the hypotheses of `Theorem18Statement` and `Theorem18Corrected` agree. -/
theorem not_collinear_of_not_coplanar [SpaceCongruence P L Pl] [Nonempty Pl] {A B C D : P}
    (h : ¬Coplanar (Plane := Pl) A B C D) : ¬Collinear (Line := L) A B C := by
  rintro ⟨l, l1, l2, l3⟩
  obtain ⟨α, hl, hd⟩ := plane_through_line_point (Pl := Pl) l D
  exact h ⟨α, hl _ l1, hl _ l2, hl _ l3, hd⟩

/-- **Hilbert's claim** (Theorem 18), corrected: every space geometry with groups I, II, IV
satisfies `Theorem18Corrected`. -/
def SpaceCongruenceGivesTheorem18Corrected : Prop :=
  ∀ (P : Type u) (L : Type v) (Pl : Type w) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceCongruence P L Pl →
      Theorem18Corrected (L := L) (Pl := Pl) P

theorem spaceCongruenceGivesTheorem18Corrected :
    SpaceCongruenceGivesTheorem18Corrected.{u, v, w} := by
  intro P L Pl _ _ _ _ _ hS
  have := hS
  exact theorem18_corrected

/-!
### The sharp form: four *distinct* points not in a plane

The only defect of `Theorem18Statement` is that its four points `f i`, `f j`, `f k`, `f m` need not
be distinct: where a plane exists, four points not in a plane are distinct anyway
(`ne_of_not_coplanar`), but in the geometry without planes the single point `f 0` counts as "four
points not in a plane". Reading Hilbert's "at least four points not lying in the same plane" as
four distinct points gives `Theorem18Distinct`, which holds in **every** space geometry with groups
I, II, IV (`theorem18_distinct`): without planes all points lie on one line, and a point of a line
is determined by its distances from two distinct points of it (`theorem18_unique_noPlane`). It
implies `Theorem18Corrected` (`theorem18Corrected_of_distinct`) and, where a plane exists, is
equivalent to `Theorem18Statement` (`theorem18Statement_iff_distinct`).
-/

/-- In a space geometry having a plane, any three points lie in a plane. -/
theorem exists_plane_three_pts [SpaceCongruence P L Pl] [Nonempty Pl] (A B C : P) :
    ∃ α : Pl, A ∈ α ∧ B ∈ α ∧ C ∈ α := by
  by_cases h : Collinear (Line := L) A B C
  · obtain ⟨l, l1, l2, l3⟩ := h
    obtain ⟨α, hl, -⟩ := plane_through_line_point (Pl := Pl) l A
    exact ⟨α, hl _ l1, hl _ l2, hl _ l3⟩
  · exact exists_plane (Plane := Pl) h

/-- In a space geometry having a plane, four points not in a plane are distinct. -/
theorem ne_of_not_coplanar [SpaceCongruence P L Pl] [Nonempty Pl] {A B C D : P}
    (h : ¬Coplanar (Plane := Pl) A B C D) :
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨α, h1, h2, h3⟩ := exists_plane_three_pts (L := L) (Pl := Pl) A C D
    exact h ⟨α, h1, e ▸ h1, h2, h3⟩
  · obtain ⟨α, h1, h2, h3⟩ := exists_plane_three_pts (L := L) (Pl := Pl) A B D
    exact h ⟨α, h1, h2, e ▸ h1, h3⟩
  · obtain ⟨α, h1, h2, h3⟩ := exists_plane_three_pts (L := L) (Pl := Pl) A B C
    exact h ⟨α, h1, h2, h3, e ▸ h1⟩
  · obtain ⟨α, h1, h2, h3⟩ := exists_plane_three_pts (L := L) (Pl := Pl) A B D
    exact h ⟨α, h1, h2, e ▸ h2, h3⟩
  · obtain ⟨α, h1, h2, h3⟩ := exists_plane_three_pts (L := L) (Pl := Pl) A B C
    exact h ⟨α, h1, h2, h3, e ▸ h2⟩
  · obtain ⟨α, h1, h2, h3⟩ := exists_plane_three_pts (L := L) (Pl := Pl) A B C
    exact h ⟨α, h1, h2, h3, e ▸ h3⟩

/-- **Theorem 18, uniqueness, in a space geometry without planes**: if the figure has two distinct
points, `P'` is unique (all points lie on one line). -/
theorem theorem18_unique_noPlane [SpaceCongruence P L Pl] [IsEmpty Pl] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {i j : Fin n} (hij : i ≠ j) {Q Q' Q'' : P}
    (h1 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'))
    (h2 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'')) :
    Q' = Q'' := by
  have col : ∀ A B C : P, Collinear (Line := L) A B C := by
    intro A B C
    by_contra h
    obtain ⟨α, -⟩ := exists_plane (Plane := Pl) h
    exact isEmptyElim α
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
  have t : ∀ m, SegCong (g m) Q' (g m) Q'' := fun m =>
    SegmentCongruence.ax_IV2 (Line := L) (f m) Q (g m) Q' (g m) Q'' (nf m) (n1 m) (n2 m) (s1 m)
      (s2 m)
  exact (spaceFrame (P := P) (L := L) (Pl := Pl)).eq_of_equidistant_line (hc.2.1.ne hij)
    (col _ _ _) (n1 i).symm (n1 j).symm (n2 i).symm (n2 j).symm (t i) (t j)

/-- **Theorem 18, sharp corrected statement**: existence as printed, and uniqueness when the given
figure `(A, B, C, …)` contains four *distinct* points not in a plane. -/
def Theorem18Distinct (P : Type u) {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ (n : ℕ) (f g : Fin n → P), CongruentFigures (L := L) f g → ∀ Q : P, Q ∉ Set.range f →
    (∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q')) ∧
    ((∃ i j k m : Fin n, i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m ∧
        ¬Coplanar (Plane := Pl) (f i) (f j) (f k) (f m)) →
      ∀ Q' Q'' : P, CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') →
        CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'') → Q' = Q'')

/-- **Theorem 18** (four distinct points not in a plane) in every space geometry with groups I, II,
IV, with or without planes. -/
theorem theorem18_distinct [SpaceCongruence P L Pl] :
    Theorem18Distinct (L := L) (Pl := Pl) P := by
  intro n f g hc Q hQ
  refine ⟨theorem18_exists_all hc hQ, ?_⟩
  rintro ⟨i, j, k, m, hij, -, -, -, -, -, h4⟩ Q' Q'' h1 h2
  rcases isEmpty_or_nonempty Pl with h | h
  · exact theorem18_unique_noPlane hc hij h1 h2
  · exact theorem18_unique hc ⟨i, j, k, m, h4⟩ h1 h2

/-- `Theorem18Statement` (four points, possibly repeated) implies `Theorem18Distinct`, in any
system of points, lines and planes. -/
theorem Theorem18Statement.distinct (h : Theorem18Statement (L := L) (Pl := Pl) P) :
    Theorem18Distinct (L := L) (Pl := Pl) P := fun n f g hc Q hQ =>
  ⟨(h n f g hc Q hQ).1, fun ⟨i, j, k, m, _, _, _, _, _, _, h4⟩ =>
    (h n f g hc Q hQ).2 ⟨i, j, k, m, h4⟩⟩

/-- Where a plane exists, `Theorem18Statement` and `Theorem18Distinct` are the same statement. -/
theorem theorem18Statement_iff_distinct [SpaceCongruence P L Pl] [Nonempty Pl] :
    Theorem18Statement (L := L) (Pl := Pl) P ↔ Theorem18Distinct (L := L) (Pl := Pl) P := by
  refine ⟨Theorem18Statement.distinct, fun h n f g hc Q hQ => ⟨(h n f g hc Q hQ).1, ?_⟩⟩
  rintro ⟨i, j, k, m, h4⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := ne_of_not_coplanar (L := L) h4
  exact (h n f g hc Q hQ).2 ⟨i, j, k, m, fun e => e1 (congrArg f e), fun e => e2 (congrArg f e),
    fun e => e3 (congrArg f e), fun e => e4 (congrArg f e), fun e => e5 (congrArg f e), fun e => e6 (congrArg f e), h4⟩

/-- `Theorem18Distinct` implies `Theorem18Corrected` in every space geometry with groups I, II, IV:
the hypothesis of the latter (three non-collinear points and a fourth off their plane) provides a
plane, hence four distinct points not in a plane. -/
theorem theorem18Corrected_of_distinct [SpaceCongruence P L Pl]
    (h : Theorem18Distinct (L := L) (Pl := Pl) P) : Theorem18Corrected (L := L) (Pl := Pl) P := by
  intro n f g hc Q hQ
  refine ⟨(h n f g hc Q hQ).1, ?_⟩
  rintro ⟨i, j, k, m, hn, h4⟩
  obtain ⟨α, -⟩ := exists_plane (Plane := Pl) hn
  have : Nonempty Pl := ⟨α⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := ne_of_not_coplanar (L := L) h4
  exact (h n f g hc Q hQ).2 ⟨i, j, k, m, fun e => e1 (congrArg f e), fun e => e2 (congrArg f e),
    fun e => e3 (congrArg f e), fun e => e4 (congrArg f e), fun e => e5 (congrArg f e), fun e => e6 (congrArg f e), h4⟩

/-- **Hilbert's claim** (Theorem 18), in its sharp corrected form: every space geometry with groups
I, II, IV satisfies `Theorem18Distinct`. -/
def SpaceCongruenceGivesTheorem18Distinct : Prop :=
  ∀ (P : Type u) (L : Type v) (Pl : Type w) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceCongruence P L Pl →
      Theorem18Distinct (L := L) (Pl := Pl) P

theorem spaceCongruenceGivesTheorem18Distinct :
    SpaceCongruenceGivesTheorem18Distinct.{u, v, w} := by
  intro P L Pl _ _ _ _ _ hS
  have := hS
  exact theorem18_distinct

end Theorem18

/-!
## Unit `s7.circle_properties`: The known properties of the circle (closed)

**Status.** proved (`circlePropertiesClaim`).
-/

section Circle

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-- For points `A`, `B`, `C`, `D` of a circle with centre `M`: the cosines of the inscribed angles
`∠ACB`, `∠ADB` are equal if the determinants of `C`, `D` with respect to `AB` have the same sign,
and opposite if they have different signs. -/
theorem Pas.inscribed_cos (ax : Pas.Axes P L) {M A B C D : P} (hAM : A ≠ M) (hBM : B ≠ M)
    (hCM : C ≠ M) (hDM : D ≠ M) (sB : SegCong M A M B) (sC : SegCong M A M C)
    (sD : SegCong M A M D) (hC' : ¬Collinear (Line := L) A C B)
    (hD' : ¬Collinear (Line := L) A D B) :
    (0 < Pas.crs ax A B C * Pas.crs ax A B D → Pas.cosA ax A C B = Pas.cosA ax A D B) ∧
      (Pas.crs ax A B C * Pas.crs ax A B D < 0 → Pas.cosA ax A C B = -Pas.cosA ax A D B) := by
  have eB : (Pas.xco ax A - Pas.xco ax M) ^ 2 + (Pas.yco ax A - Pas.yco ax M) ^ 2 =
      (Pas.xco ax B - Pas.xco ax M) ^ 2 + (Pas.yco ax B - Pas.yco ax M) ^ 2 := by
    rw [← Pas.len_sq_coord, ← Pas.len_sq_coord, (Pas.len_eq_iff ax hAM.symm hBM.symm).2 sB]
  have eC : (Pas.xco ax A - Pas.xco ax M) ^ 2 + (Pas.yco ax A - Pas.yco ax M) ^ 2 =
      (Pas.xco ax C - Pas.xco ax M) ^ 2 + (Pas.yco ax C - Pas.yco ax M) ^ 2 := by
    rw [← Pas.len_sq_coord, ← Pas.len_sq_coord, (Pas.len_eq_iff ax hAM.symm hCM.symm).2 sC]
  have eD : (Pas.xco ax A - Pas.xco ax M) ^ 2 + (Pas.yco ax A - Pas.yco ax M) ^ 2 =
      (Pas.xco ax D - Pas.xco ax M) ^ 2 + (Pas.yco ax D - Pas.yco ax M) ^ 2 := by
    rw [← Pas.len_sq_coord, ← Pas.len_sq_coord, (Pas.len_eq_iff ax hAM.symm hDM.symm).2 sD]
  obtain ⟨hAC, hBC, -⟩ := Pas.nc_ne ax hC'
  obtain ⟨hAD, hBD, -⟩ := Pas.nc_ne ax hD'
  have fC := Pas.cos_formula ax hC'
  have fD := Pas.cos_formula ax hD'
  have hn : 0 < Pas.len ax C A * Pas.len ax C B :=
    mul_pos (Pas.len_pos ax hAC.symm) (Pas.len_pos ax hBC.symm)
  have hn' : 0 < Pas.len ax D A * Pas.len ax D B :=
    mul_pos (Pas.len_pos ax hAD.symm) (Pas.len_pos ax hBD.symm)
  have e : (Pas.len ax C A * Pas.len ax C B) ^ 2 =
      ((Pas.xco ax A - Pas.xco ax C) * (Pas.xco ax B - Pas.xco ax C) +
        (Pas.yco ax A - Pas.yco ax C) * (Pas.yco ax B - Pas.yco ax C)) ^ 2 +
      Pas.crs ax A B C ^ 2 := by
    rw [mul_pow, Pas.len_sq_coord, Pas.len_sq_coord]; unfold Pas.crs; ring
  have e' : (Pas.len ax D A * Pas.len ax D B) ^ 2 =
      ((Pas.xco ax A - Pas.xco ax D) * (Pas.xco ax B - Pas.xco ax D) +
        (Pas.yco ax A - Pas.yco ax D) * (Pas.yco ax B - Pas.yco ax D)) ^ 2 +
      Pas.crs ax A B D ^ 2 := by
    rw [mul_pow, Pas.len_sq_coord, Pas.len_sq_coord]; unfold Pas.crs; ring
  have hc : ((Pas.xco ax A - Pas.xco ax C) * (Pas.xco ax B - Pas.xco ax C) +
        (Pas.yco ax A - Pas.yco ax C) * (Pas.yco ax B - Pas.yco ax C)) * Pas.crs ax A B D =
      ((Pas.xco ax A - Pas.xco ax D) * (Pas.xco ax B - Pas.xco ax D) +
        (Pas.yco ax A - Pas.yco ax D) * (Pas.yco ax B - Pas.yco ax D)) * Pas.crs ax A B C := by
    unfold Pas.crs
    linear_combination
      (Pas.xco ax A * Pas.yco ax C - Pas.xco ax A * Pas.yco ax D - Pas.yco ax A * Pas.xco ax C +
        Pas.yco ax A * Pas.xco ax D + Pas.xco ax C * Pas.yco ax D - Pas.yco ax C * Pas.xco ax D) * eB +
      (-(Pas.xco ax A * Pas.yco ax B) + Pas.xco ax A * Pas.yco ax D + Pas.yco ax A * Pas.xco ax B -
        Pas.yco ax A * Pas.xco ax D - Pas.xco ax B * Pas.yco ax D + Pas.yco ax B * Pas.xco ax D) * eC +
      (Pas.xco ax A * Pas.yco ax B - Pas.xco ax A * Pas.yco ax C - Pas.yco ax A * Pas.xco ax B +
        Pas.yco ax A * Pas.xco ax C + Pas.xco ax B * Pas.yco ax C - Pas.yco ax B * Pas.xco ax C) * eD
  exact ⟨Pas.cos_alg_pos hn hn' e e' hc fC fD, Pas.cos_alg_neg hn hn' e e' hc fC fD⟩

/-- **Angles inscribed in the same segment of a circle are congruent** (plane geometry, groups
I–IV). -/
theorem inscribedAnglesCongruent : InscribedAnglesCongruent (L := L) P := by
  intro M A B C D hAB hAM hBM hCM hDM sB sC sD hC' hD' hside
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hAB
  have hs := hside (line (Line := L) A B hAB) (mem_line_left _) (mem_line_right _)
  have hpos := Pas.crs_same ax hAB (mem_line_left _) (mem_line_right _) hs
  exact Pas.angCong_of_cosA ax hC' hD'
    ((Pas.inscribed_cos ax hAM hBM hCM hDM sB sC sD hC' hD').1 hpos)

/-- **The opposite angles of a quadrilateral inscribed in a circle sum to two right angles** (plane
geometry, groups I–IV): `∠ADB` is congruent to the supplement `∠BCW` of `∠ACB`. -/
theorem inscribedQuadrilateral : InscribedQuadrilateral (L := L) P := by
  intro M A B C D hAB hAM hBM hCM hDM sB sC sD hside
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hAB
  have ho := hside (line (Line := L) A B hAB) (mem_line_left _) (mem_line_right _)
  have hC' : ¬Collinear (Line := L) A C B := fun h =>
    ho.1 (mem_of_collinear h.swap23 hAB (mem_line_left _) (mem_line_right _))
  have hD' : ¬Collinear (Line := L) A D B := fun h =>
    ho.2.1 (mem_of_collinear h.swap23 hAB (mem_line_left _) (mem_line_right _))
  have hneg := Pas.crs_opp ax hAB (mem_line_left _) (mem_line_right _) ho
  have hcos := (Pas.inscribed_cos ax hAM hBM hCM hDM sB sC sD hC' hD').2 hneg
  obtain ⟨hAC, hBC, -⟩ := Pas.nc_ne ax hC'
  obtain ⟨hb, sW⟩ := (Pas.ht_eq_iff (L := L) hAC).1 rfl
  have hBCW : ¬Collinear (Line := L) B C (Pas.ht (L := L) C A) :=
    not_collinear_swap (not_collinear_of_between hC' hb)
  have f1 := Pas.cos_formula ax hC'
  have f2 := Pas.cos_formula ax hBCW
  have hW1 : Pas.xco ax (Pas.ht (L := L) C A) = Pas.xco ax C + Pas.xco ax C - Pas.xco ax A := by
    unfold Pas.xco; rw [Pas.ht_vec, Pas.xc_sub, Pas.xc_add]
  have hW2 : Pas.yco ax (Pas.ht (L := L) C A) = Pas.yco ax C + Pas.yco ax C - Pas.yco ax A := by
    unfold Pas.yco; rw [Pas.ht_vec, Pas.yc_sub, Pas.yc_add]
  have hlW : Pas.len ax C (Pas.ht (L := L) C A) = Pas.len ax C A :=
    (Pas.len_eq_iff ax (Pas.htp_ne hAC).symm hAC.symm).2
      (segCong_symm (L := L) hAC.symm (Pas.htp_ne hAC).symm sW)
  rw [hW1, hW2, hlW] at f2
  have hpos : 0 < Pas.len ax C A * Pas.len ax C B :=
    mul_pos (Pas.len_pos ax hAC.symm) (Pas.len_pos ax hBC.symm)
  have hsup : Pas.cosA ax B C (Pas.ht (L := L) C A) = -Pas.cosA ax A C B := by
    apply mul_right_cancel₀ hpos.ne'
    linear_combination f2 + f1
  refine ⟨C, A, B, Pas.ht (L := L) C A, hb, hBC, hC', angCong_refl (Line := L) hC',
    Pas.angCong_of_cosA ax hD' hBCW ?_⟩
  rw [hsup, hcos, neg_neg]

end Circle

/-- **The known properties of the circle** (§ 7): the claim `CirclePropertiesClaim`. -/
theorem circlePropertiesClaim : CirclePropertiesClaim.{u, v} := by
  intro P L _ _ _ _ hC hP
  have := hC
  have := hP
  exact ⟨circleThroughThree, inscribedAnglesCongruent, inscribedQuadrilateral⟩

end HilbertFoundations
