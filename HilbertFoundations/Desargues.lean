import HilbertFoundations.Proportion
import HilbertFoundations.DesarguesAux2

/-!
# Desargues's theorem from the axioms of congruence (§ 22, Theorem 32)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 22. Desargues's theorem and its demonstration for plane geometry by aid of the axioms of congruence

## Organisation

Desargues's theorem as a proposition about a plane geometry (`DesAlg.DesarguesI`, the first part,
Theorem 32 proper; `DesAlg.DesarguesII`, the converse; `DesAlg.DesarguesTheorem`, both) and the
notion "a plane geometry regarded as a part of a geometry of space" (`DesAlg.PlaneInSpace`) are
those of DesarguesAlgebra.lean (§§ 24–30), which is imported, so that Theorem 32 proved here is
literally the hypothesis used there. The space proof of Desargues's theorem (`DesAlg.space_desargues`)
and the plane restriction of a space geometry (`DesAlg.restrictPlaneInSpace`) also come from there.

Helper modules of this file:

* `DesarguesAux.lean`: the planes of `K³` are the solution sets of the linear equations
  `u x + v y + w z + r = 0` (both directions), lines are the intersections of two planes, and the
  embedding of a plane geometry with I 1–2, II, III, IV as the plane `z = 0` of the space of
  triples of its segments (`Des.planeInSpace ax`).
* `DesarguesAux2.lean`: the general theorem of Desargues (points of intersection, centre a point or
  at infinity), in coordinates over any skew field, and in every plane of a space geometry with
  I, II, III; the plane axioms I, III of a plane geometry which is a part of a space; sides of a
  plane and of a line in `K³` by the sign of `u x + v y + w z + r`.

## API for other files

`PartOfSpace`, `GeneralDesargues` (`Des.GeneralDesargues`), `space_generalDesargues`,
`theorem32`, `theorem32_converse`, `theorem32_both`, `theorem32_converse_literal_false`,
`theorem32_of_space`, `necessary_condition`, `segment_coordinates`, `segment_space`,
`segment_space_planes`, `segment_space_lines`, `segment_space_between`,
`segment_space_sides_plane`, `segment_space_sides_line`, `plane_is_part`,
`partOfSpace_of_congruence`, `desargues_from_space`, `generalDesargues_of_congruence`,
`desargues_via_theorem23`, `Des.planeInSpace`, `Des.plane_of_equation`, `Des.equation_of_plane`,
`Des.planeParallels_of_planeInSpace`.
-/

namespace HilbertFoundations

universe u v

open DesAlg

/-!
## [s22.space_axioms] The space axioms

*(§ 22)*

> Of the axioms given in \S§ 1–8, pp. \pageref{folio1}–\pageref{folio26}, those of groups II–V are in part linear and in part plane axioms. Axioms 3–7 of group I are the only space axioms.

**Lean reading.** A classification of the axioms, reflected in the class hierarchy of Basic.lean:
groups II–V are stated with points and lines only (`LineOrder`, `PlaneOrder`, `PlaneParallels`,
`PlaneCongruence`, `Archimedes`), and planes (`HasPlanes`) enter only through `SpaceConnection`
(I 3–7; I 7 has a line clause, kept in `Connection`, and plane and space clauses). In the space
versions (`SpaceOrder`, `SpaceParallels`, `SpaceAngleCongruence`) II 5, III and IV 4 are required in
each plane, i.e. they remain plane axioms. Nothing to prove.

**Status.** remark
-/

/-!
## [s22.part_of_space] A plane geometry regarded as a part of a geometry of space

*(§ 22)*

> In order to show clearly the significance of these axioms of space, let us assume a plane geometry and investigate, in general, the conditions for which this plane geometry may be regarded as a part of a geometry of space in which at least the axioms of groups I–III are all fulfilled.

**Lean reading.** `PartOfSpace P L`: there are a space geometry `(P', L', Pl')` (in the universe of
`P`) satisfying groups I, II, III (`SpaceOrder`, `SpaceParallels`) and a
`DesAlg.PlaneInSpace P L P' L' Pl'`: a plane `α` of the space, a bijection of the points of the plane
geometry with the points of `α` and a bijection of its lines with the lines lying in `α`, preserving
and reflecting incidence and betweenness. This is the notion of Theorem 35 (§ 30), where Hilbert
answers the question raised here (DesarguesAlgebra.lean, `theorem35`).

**Status.** definition
-/

/-- **The plane geometry `(P, L)` can be regarded as a part of a geometry of space with I, II,
III.** -/
def PartOfSpace (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] : Prop :=
  ∃ (P' L' Pl' : Type u) (_ : HasLines P' L') (_ : HasPlanes P' Pl') (_ : HasBetween P'),
    SpaceOrder P' L' Pl' ∧ SpaceParallels P' L' Pl' ∧ Nonempty (PlaneInSpace P L P' L' Pl')

/-!
## [s22.desargues_general] The theorem of Desargues relating to points of intersection

*(§ 22)*

> Upon the basis of the axioms of groups I–III, it is well known that the so-called theorem of Desargues may be easily demonstrated. This theorem relates to points of intersection in a plane.

**Lean reading.** Hilbert does not state the general theorem; it is the classical one (Fig. 37
shows only the special case): if the lines joining the homologous vertices of two triangles `ABC`,
`A'B'C'` in a plane pass through one point `O`, the points of intersection `R`, `S`, `T` of the
homologous sides `AB, A'B'`, `BC, B'C'`, `CA, C'A'` lie on one straight line. Since Hilbert's
special case below allows the joins to be parallel ("the centre at infinity"), so does the reading
`Des.GeneralDesargues`: lines `a ∋ A, A'`, `b ∋ B, B'`, `c ∋ C, C'` which pass through one point or
are pairwise parallel (`DesAlg.ConcurrentOrParallel`), triangles (non-collinear vertices), and
homologous sides that are distinct lines meeting in `R`, `S`, `T` (the only hypotheses needed for
"the points of intersection" to exist; the cases with some of `R`, `S`, `T` at infinity are not
"points of intersection in a plane"). No further non-degeneracy is assumed: the centre may be a
vertex and homologous vertices may coincide (these cases are settled by I 1–2 alone,
`Des.collinear_of_center_vertex`). `space_generalDesargues`: in a space geometry with I, II, III
every plane `α` (with its points and the lines lying in it) satisfies it. Hilbert's "easily
demonstrated" refers to the classical spatial argument; the proof here goes another way: the
special case (Theorem 32's converse in space, `DesAlg.space_desargues`, a spatial argument) makes
`α` desarguesian, hence (§§ 24–30, DesarguesAlgebra.lean) a plane of a coordinate space over a skew
field, where the general theorem is a computation in "homogeneous co-ordinates"
(`Des.desargues_model`, `Des.desargues_model_par`: `α A + α' A' = β B + β' B' = γ C + γ' C'` with
`α + α' = β + β' = γ + γ' = 1` for a centre `O`, `= 0` for parallel joins, and
`(α-β)R + (β-γ)S + (γ-α)T = 0`), valid without commutativity. The order axioms II enter only
through the co-ordinatization of DesarguesAlgebra.lean (which uses the order of the segments), so
the hypotheses stay within Hilbert's I–III.

**Status.** proved
-/

/-- **The general theorem of Desargues** (points of intersection in a plane). -/
abbrev GeneralDesargues (P : Type u) {L : Type v} [HasLines P L] : Prop := Des.GeneralDesargues P

/-- **The theorem of Desargues holds in every plane of a space geometry with I, II, III.** -/
theorem space_generalDesargues {P : Type u} {L : Type v} {Pl : Type*} [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [SpaceOrder P L Pl] [SpaceParallels P L Pl] (α : Pl) :
    GeneralDesargues {A : P // A ∈ α} :=
  Des.space_generalDesargues α

/-!
## [s22.special_case] The theorem of Desargues: the line of intersections at infinity

*(§ 22)*

> Let us assume in particular that the straight line, upon which are situated the points of intersection of the homologous sides of the two triangles, is the straight line which we call the straight line at infinity. We will designate the theorem which arises in this case, together with its converse, as the theorem of Desargues.

**Lean reading.** "Points of intersection on the line at infinity" = homologous sides parallel
(lines without a common point). The definitions are those of DesarguesAlgebra.lean (unit
`s24.desargues`): `DesarguesI P` (Theorem 32: homologous sides of two triangles parallel ⇒ the joins
`AA'`, `BB'`, `CC'` pass through one point or are pairwise parallel), `DesarguesII P` (the converse,
with the correction explained in unit `s22.converse`), `DesarguesTheorem P` (both): "the theorem of
Desargues" of Chapter V.

**Status.** definition
-/

theorem desarguesTheorem_iff {P : Type u} {L : Type v} [HasLines P L] :
    DesarguesTheorem P ↔ DesarguesI P ∧ DesarguesII P := Iff.rfl

/-!
## [th.32] Theorem 32

*(§ 22)*

> (Desargues's theorem.) When two triangles are so situated in a plane that their homologous sides are respectively parallel, then the lines joining the homologous vertices pass through one and the same point, or are parallel to one another.

**Lean reading.** `theorem32`: in a plane geometry with I 1–2, II, III, IV (`PlaneCongruence`,
`PlaneParallels`; Hilbert's hypotheses in § 22: "the axioms I, 1–2 and II–IV all hold"; no
Archimedes), `DesarguesI P`: for triangles `ABC`, `A'B'C'` (non-collinear) with `AB ∥ A'B'`,
`AC ∥ A'C'`, `BC ∥ B'C'` (some lines through the pairs without a common point), either there is a
point `O` with `A, A', O`, `B, B', O`, `C, C', O` collinear, or the lines `AA'`, `BB'`, `CC'` are
pairwise parallel. Proof: Hilbert's own (units `s22.coordinates` – `s22.conclusion`): the plane is
the plane `z = 0` of the space of triples of its segments (`Des.planeInSpace`), a space geometry with
I, II, III, and a plane of such a space satisfies Desargues's theorem
(`DesAlg.desarguesTheorem_of_planeInSpace`, the spatial argument). The degenerate plane without
lines satisfies the statement vacuously. Group IV enters only through the algebra of segments
(§§ 15–17); its necessity is Theorem 33 (§ 23).

**Status.** proved
-/

section Plane

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [PlaneCongruence P L] [PlaneParallels P L]

/-- Desargues's theorem (both parts) in a plane geometry with I 1–2, II, III, IV: Hilbert's proof
through the space of triples of segments. -/
theorem theorem32_both : DesarguesTheorem P := by
  rcases isEmpty_or_nonempty L with hL | hL
  · constructor
    · rintro _ _ _ _ _ _ _ _ ⟨l, -⟩
      exact (hL.false l).elim
    · intro _ _ _ _ _ _ a
      exact (hL.false a).elim
  · obtain ⟨l⟩ := id hL
    obtain ⟨O, E, hOE, -, -⟩ := exists_two_points (Point := P) l
    obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hOE
    exact desarguesTheorem_of_planeInSpace (Des.planeInSpace ax)

/-- **Theorem 32** (Desargues's theorem). -/
theorem theorem32 : DesarguesI P := theorem32_both.1

/-!
## [s22.converse] The converse of Theorem 32

*(§ 22)*

> Conversely, if two triangles are so situated in a plane that the straight lines joining the homologous vertices intersect in a common point, or are parallel to one another, and, furthermore, if two pairs of homologous sides are parallel to each other, then the third sides of the two triangles are also parallel to each other.

**Lean reading.** `theorem32_converse`: `DesarguesII P` in a plane geometry with I 1–2, II, III, IV:
for triangles `ABC`, `A'B'C'` and lines `a ∋ A, A'`, `b ∋ B, B'`, `c ∋ C, C'` which are pairwise
distinct and pass through one point or are pairwise parallel, `AB ∥ A'B'` and `AC ∥ A'C'` imply
`BC ∥ B'C'`. The distinctness of the three joining lines is a correction: as printed the converse is
false, already in the ordinary plane (`Coord ℝ 2`, a model of all the plane axioms I–V,
`real_planeGeometry`): `O = (0,0)`, `A = (0,1)`, `A' = (0,2)`, `B = (1,0)`, `B' = (2,0)`,
`C = (-1,0)`, `C' = (-2,0)`; the joins pass through `O`, `AB ∥ A'B'`, `AC ∥ A'C'`, but `BC = B'C'`
(`theorem32_converse_literal_false`, from DesarguesAlgebra.lean). With distinct joins the third
sides are parallel (and not merely parallel or equal). Proof as for Theorem 32.

**Status.** proved (corrected)
-/

/-- **The converse of Theorem 32** (with distinct joining lines). -/
theorem theorem32_converse : DesarguesII P := theorem32_both.2

end Plane

/-- The literal converse fails in the ordinary plane, a model of all the plane axioms. -/
theorem theorem32_converse_literal_false :
    PlaneGeometry (Coord ℝ 2) (CoordLine ℝ 2) ∧ ¬DesarguesIILiteral (Coord ℝ 2) :=
  ⟨real_planeGeometry, desargues_literal_false⟩

/-!
## [s22.necessary] Desargues's theorem is necessary for a plane to be part of a space

*(§ 22)*

> As we have already mentioned, theorem 32 is a consequence of the axioms I–III. Because of this fact, the validity of Desargues's theorem in the plane is, in any case, a necessary condition that the geometry of this plane may be regarded as a part of a geometry of space in which the axioms of groups I–III are all fulfilled.

**Lean reading.** Two statements. `theorem32_of_space`: in a space geometry satisfying I and III
(`SpaceParallels`; group II is not needed), every plane `α`, with its points and the lines lying in
it, satisfies Desargues's theorem, both parts (`planes_of_space_desarguesian` of DesarguesAlgebra.lean,
by the spatial argument `DesAlg.space_desargues`: the figure is lifted out of `α` through a point
`S ∉ α`, which exists by I 7, and two triangles in distinct planes with two pairs of parallel sides
lie in planes without common point). `necessary_condition`: a plane geometry which is a part of a
space geometry with I–III (`PartOfSpace`) satisfies Desargues's theorem; no axiom is assumed of the
plane geometry itself, since the plane axioms I 1–2 and III are inherited from the space
(`Des.planeParallels_of_planeInSpace`).

**Status.** proved
-/

/-- **Theorem 32 is a consequence of the axioms I, III of space.** -/
theorem theorem32_of_space {P : Type u} {L : Type v} {Pl : Type*} [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [SpaceParallels P L Pl] (α : Pl) :
    DesarguesTheorem {A : P // A ∈ α} :=
  planes_of_space_desarguesian (L := L) α

/-- **The validity of Desargues's theorem is a necessary condition.** -/
theorem necessary_condition {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    (h : PartOfSpace P L) : DesarguesTheorem P := by
  obtain ⟨P', L', Pl', _, _, _, -, hPar, ⟨e⟩⟩ := h
  have := Des.planeParallels_of_planeInSpace e
  rcases isEmpty_or_nonempty L with hL | hL
  · constructor
    · rintro _ _ _ _ _ _ _ _ ⟨l, -⟩
      exact (hL.false l).elim
    · intro _ _ _ _ _ _ a
      exact (hL.false a).elim
  · exact desarguesTheorem_of_planeInSpace e

/-!
## [s22.setting] The setting: a plane geometry with I 1–2, II–IV and the algebra of segments

*(§ 22)*

> Let us assume, as in \S§ 13–21, pp. \pageref{folio37}–\pageref{folio70}, that we have a plane geometry in which the axioms I, 1–2 and II–IV all hold and, also, that we have introduced in this geometry an algebra of segments conforming to § 15.

**Lean reading.** The setting of the rest of § 22: `[PlaneCongruence P L] [PlaneParallels P L]`
(I 1–2, II, III, IV; no Archimedes) with rectangular axes `ax : Pas.Axes P L`, whose signed segments
form the ordered field `Pas.G ax` of Proportion.lean (§§ 15, 17: `segment_algebra`,
`signed_segments_laws`). Nothing to prove here.

**Status.** remark
-/

/-!
## [s22.coordinates] Co-ordinates of points and equations of lines

*(§ 22)*

> Now, as has already been established in § 17, there may be made to correspond to each point in the plane a pair of segments $(x, y)$ and to each straight line a ratio of three segments $(u:v:w)$, so that the linear equation \[ ux+vy+w=0 \] expresses the condition that the point is situated upon the straight line. The system composed of all the segments in our geometry forms, according to § 17, a domain of numbers for which the properties (1–16), enumerated in § 13, are valid.

**Lean reading.** `segment_coordinates`: in a plane geometry with I 1–2, II, III, IV, for axes `ax`,
the map `Z ↦ (x, y)` to the signed segments is a bijection; every line is the solution set of an
equation `u x + v y + w = 0` with `(u, v) ≠ 0` and every such equation represents a line; and the
signed segments satisfy the laws 1–16 of § 13 (an ordered field). All from Proportion.lean
(`coordinates_bijective`, `lines_are_linear`, `linear_eqs_are_lines`, `signed_segments_laws`). The
"ratio" `(u : v : w)` is represented by any of its triples (proportional triples give the same
equation).

**Status.** proved
-/

theorem segment_coordinates {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) :
    Function.Bijective (fun Z : P => (Pas.px ax Z, Pas.py ax Z)) ∧
      (∀ l : L, ∃ u v w : Pas.G ax, (u ≠ 0 ∨ v ≠ 0) ∧
        ∀ Z : P, Z ∈ l ↔ u * Pas.px ax Z + v * Pas.py ax Z + w = 0) ∧
      (∀ u v w : Pas.G ax, (u ≠ 0 ∨ v ≠ 0) → ∃ l : L,
        ∀ Z : P, Z ∈ l ↔ u * Pas.px ax Z + v * Pas.py ax Z + w = 0) ∧
      (Laws1to16 (Pas.G ax) ∧ Law13Asymm (Pas.G ax)) :=
  ⟨coordinates_bijective ax, lines_are_linear ax, fun _ _ w h => linear_eqs_are_lines ax h w,
    signed_segments_laws ax⟩

/-!
## [s22.space_model] The geometry of space over the segments

*(§ 22)*

> We can, therefore, by means of this domain of numbers, construct a geometry of space in a manner similar to that already employed in § 9 or in § 12, where we made use of the systems of numbers $\Omega$ and $\Omega(t)$, respectively. For this purpose, we assume that a system of three segments $(x, y, z)$ shall represent a point, and that the ratio of four segments $(u:v:w:r)$ shall represent a plane, while a straight line is defined as the intersection of two planes. Hence, the linear equation \[ ux+vy+wz+r = 0 \] expresses the fact that the point $(x, y, z)$ lies in the plane $(u: v: w: r)$. Finally, we determine the arrangement of the points upon a straight line, or the points of a plane with respect to a straight line situated in this plane, or the arrangement of the points in space with respect to a plane, by means of inequalities in a manner similar to the method employed for the plane in § 9.

**Lean reading.** The space is the coordinate space `Coord K 3` of Analytic.lean over the field
`K = Pas.G ax` of segments: points are the triples, planes and lines the affine subspaces of
dimension 2 and 1, betweenness `B = A + t (C - A)` with `0 < t < 1`. `segment_space`: it satisfies
groups I, II, III (`SpaceOrder`, `SpaceParallels`; Analytic.lean, for every ordered field). The
identification with Hilbert's description is proved: `segment_space_planes` — the planes are exactly
the solution sets of the equations `u x + v y + w z + r = 0`, `(u, v, w) ≠ 0` (`Des.plane_of_equation`,
`Des.equation_of_plane`; "the ratio" because proportional quadruples have the same solutions);
`segment_space_lines` — every line is the set of common points of two distinct planes, and the
common points of two distinct planes with a common point form a line (`Des.line_eq_inter`,
`Des.inter_eq_line`, from the axioms I); `segment_space_between` — betweenness is Hilbert's
"inequalities": for `B` on the line `AC`, `B` lies between `A` and `C` iff some co-ordinate satisfies
`A_i < B_i < C_i` or `A_i > B_i > C_i` (`between_iff_double_inequality` of DesarguesAlgebra.lean,
§ 29); `segment_space_sides_plane` — the arrangement of the points of space with respect to a plane
by inequalities: every plane has an equation `f = u x + v y + w z + r = 0`, and two points off the
plane are separated by it (the segment joining them meets the plane) iff `f` takes values of
opposite signs at them; `segment_space_sides_line` — likewise for the points of a plane `π` with
respect to a line `ℓ` of `π`: `ℓ` is the intersection of `π` with a plane `f = 0`
(`Des.exists_cutting_plane`), and two points of `π` off `ℓ` are separated by `ℓ` iff `f` has
opposite signs at them.

**Status.** proved
-/

section SegmentSpace

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L)

/-- **The space of triples of segments satisfies the axioms I, II, III.** -/
theorem segment_space :
    SpaceOrder (Coord (Pas.G ax) 3) (CoordLine (Pas.G ax) 3) (CoordPlane (Pas.G ax) 3) ∧
      SpaceParallels (Coord (Pas.G ax) 3) (CoordLine (Pas.G ax) 3) (CoordPlane (Pas.G ax) 3) :=
  ⟨inferInstance, inferInstance⟩

/-- **The planes are the linear equations `u x + v y + w z + r = 0`.** -/
theorem segment_space_planes :
    (∀ u v w r : Pas.G ax, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) → ∃ π : CoordPlane (Pas.G ax) 3,
      ∀ X : Coord (Pas.G ax) 3, X ∈ π ↔
        u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2 + r = 0) ∧
    (∀ π : CoordPlane (Pas.G ax) 3, ∃ u v w r : Pas.G ax, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      ∀ X : Coord (Pas.G ax) 3, X ∈ π ↔
        u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2 + r = 0) :=
  ⟨Des.plane_of_equation, Des.equation_of_plane⟩

/-- **A straight line is the intersection of two planes.** -/
theorem segment_space_lines :
    (∀ ℓ : CoordLine (Pas.G ax) 3, ∃ π₁ π₂ : CoordPlane (Pas.G ax) 3, π₁ ≠ π₂ ∧
      ∀ X : Coord (Pas.G ax) 3, X ∈ ℓ ↔ X ∈ π₁ ∧ X ∈ π₂) ∧
    (∀ π₁ π₂ : CoordPlane (Pas.G ax) 3, π₁ ≠ π₂ → (∃ A : Coord (Pas.G ax) 3, A ∈ π₁ ∧ A ∈ π₂) →
      ∃ ℓ : CoordLine (Pas.G ax) 3, ∀ X : Coord (Pas.G ax) 3, X ∈ ℓ ↔ X ∈ π₁ ∧ X ∈ π₂) := by
  have : Nonempty (CoordPlane (Pas.G ax) 3) :=
    ⟨(Des.plane_of_equation (1 : Pas.G ax) 0 0 0 (Or.inl one_ne_zero)).choose⟩
  exact ⟨fun ℓ => Des.line_eq_inter (Pl := CoordPlane (Pas.G ax) 3) ℓ,
    fun _ _ hne ⟨_, h1, h2⟩ => Des.inter_eq_line (L := CoordLine (Pas.G ax) 3) hne h1 h2⟩

/-- **The arrangement of the points of a line by inequalities.** -/
theorem segment_space_between {A C : Coord (Pas.G ax) 3} (hAC : A ≠ C) (t : Pas.G ax) :
    Between A (t • (C - A) + A) C ↔ ∃ i : Fin 3,
      (AffPt.toV A i < AffPt.toV (t • (C - A) + A) i ∧
          AffPt.toV (t • (C - A) + A) i < AffPt.toV C i) ∨
        (AffPt.toV C i < AffPt.toV (t • (C - A) + A) i ∧
          AffPt.toV (t • (C - A) + A) i < AffPt.toV A i) :=
  between_iff_double_inequality hAC t

/-- **The arrangement of the points of space with respect to a plane by inequalities.** -/
theorem segment_space_sides_plane (π : CoordPlane (Pas.G ax) 3) :
    ∃ u v w r : Pas.G ax, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      (∀ X : Coord (Pas.G ax) 3, X ∈ π ↔ Des.eqVal u v w r X = 0) ∧
      ∀ X Y : Coord (Pas.G ax) 3, X ∉ π → Y ∉ π →
        ((∃ Z, Z ∈ π ∧ Between X Z Y) ↔ Des.eqVal u v w r X * Des.eqVal u v w r Y < 0) := by
  obtain ⟨u, v, w, r, h0, hπ⟩ := Des.equation_of_plane π
  have hmem : ∀ X : Coord (Pas.G ax) 3, X ∈ π ↔ Des.eqVal u v w r X = 0 := hπ
  refine ⟨u, v, w, r, h0, hmem, fun X Y hX hY => ?_⟩
  rw [← Des.segment_meets_iff u v w r (fun h => hX ((hmem X).2 h)) (fun h => hY ((hmem Y).2 h))]
  exact ⟨fun ⟨Z, hZ, hb⟩ => ⟨Z, hb, (hmem Z).1 hZ⟩, fun ⟨Z, hb, hZ⟩ => ⟨Z, (hmem Z).2 hZ, hb⟩⟩

/-- **The arrangement of the points of a plane with respect to a line of the plane by
inequalities.** -/
theorem segment_space_sides_line {ℓ : CoordLine (Pas.G ax) 3} {π : CoordPlane (Pas.G ax) 3}
    (hℓ : LiesInPlane (Point := Coord (Pas.G ax) 3) ℓ π) :
    ∃ u v w r : Pas.G ax, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧
      (∀ X : Coord (Pas.G ax) 3, X ∈ ℓ ↔ X ∈ π ∧ Des.eqVal u v w r X = 0) ∧
      ∀ X Y : Coord (Pas.G ax) 3, X ∈ π → Y ∈ π → X ∉ ℓ → Y ∉ ℓ →
        ((∃ Z, Z ∈ ℓ ∧ Between X Z Y) ↔ Des.eqVal u v w r X * Des.eqVal u v w r Y < 0) := by
  obtain ⟨π', hπ'⟩ := Des.exists_cutting_plane (L := CoordLine (Pas.G ax) 3) hℓ
  obtain ⟨u, v, w, r, h0, he⟩ := Des.equation_of_plane π'
  have he' : ∀ X : Coord (Pas.G ax) 3, X ∈ π' ↔ Des.eqVal u v w r X = 0 := he
  have hmem : ∀ X : Coord (Pas.G ax) 3, X ∈ ℓ ↔ X ∈ π ∧ Des.eqVal u v w r X = 0 :=
    fun X => (hπ' X).trans (and_congr_right' (he' X))
  refine ⟨u, v, w, r, h0, hmem, fun X Y hXπ hYπ hX hY => ?_⟩
  have nz : ∀ {Z : Coord (Pas.G ax) 3}, Z ∈ π → Z ∉ ℓ → Des.eqVal u v w r Z ≠ 0 :=
    fun hZ hZl h => hZl ((hmem _).2 ⟨hZ, h⟩)
  rw [← Des.segment_meets_iff u v w r (nz hXπ hX) (nz hYπ hY)]
  constructor
  · rintro ⟨Z, hZ, hb⟩
    exact ⟨Z, hb, ((hmem Z).1 hZ).2⟩
  · rintro ⟨Z, hb, hZ⟩
    refine ⟨Z, (hmem Z).2 ⟨?_, hZ⟩, hb⟩
    obtain ⟨t, -, -, rfl⟩ := Des.between_param hb
    exact AffPt.add_mem_of_mem_direction
      (Submodule.smul_mem _ t (AffPt.sub_mem_direction (S := π.carrier) hXπ hYπ)) hXπ

end SegmentSpace

/-!
## [s22.plane_part] The plane `z = 0` is the given plane geometry

*(§ 22)*

> Since we obtain again the original plane geometry by putting $z=0$, we know that our plane geometry can be regarded as a part of geometry of space.

**Lean reading.** `plane_is_part`: for axes `ax` of a plane geometry with I 1–2, II, III, IV, the map
`Z ↦ (x, y, 0)` and the map sending a line to the line of the space through the images of two of its
points form a `PlaneInSpace` (`Des.planeInSpace ax`): bijective onto the plane `z = 0` and onto the
lines lying in it, with incidence (§ 17's equations, `Pas.mem_line_coords`) and betweenness
(`Pas.between_coords`, `Pas.between_of_coords`) preserved and reflected. `partOfSpace_of_congruence`:
hence (if there is a line, i.e. two distinct points to set up the axes) the plane geometry is a
`PartOfSpace`.

**Status.** proved
-/

section PlanePart

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [PlaneCongruence P L] [PlaneParallels P L]

theorem plane_is_part (ax : Pas.Axes P L) :
    Nonempty (PlaneInSpace P L (Coord (Pas.G ax) 3) (CoordLine (Pas.G ax) 3)
      (CoordPlane (Pas.G ax) 3)) :=
  ⟨Des.planeInSpace ax⟩

theorem partOfSpace_of_congruence [Nonempty L] : PartOfSpace P L := by
  obtain ⟨l⟩ := ‹Nonempty L›
  obtain ⟨O, E, hOE, -, -⟩ := exists_two_points (Point := P) l
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hOE
  exact ⟨Coord (Pas.G ax) 3, CoordLine (Pas.G ax) 3, CoordPlane (Pas.G ax) 3, inferInstance,
    inferInstance, inferInstance, (segment_space ax).1, (segment_space ax).2, plane_is_part ax⟩

/-!
## [s22.conclusion] Hence Desargues's theorem holds in the plane

*(§ 22)*

> Now, the validity of Desargues's theorem is, according to the above considerations, a necessary condition for this result. Hence, in the assumed plane geometry, it follows that Desargues's theorem must also hold.

**Lean reading.** `desargues_from_space`: the chain of § 22 exactly as Hilbert gives it, in a plane
geometry with I 1–2, II, III, IV: the plane is a part of a space with I–III
(`partOfSpace_of_congruence`), and Desargues's theorem (both parts) is necessary for this
(`necessary_condition`). This is the proof of `theorem32_both`. The same embedding also gives the
general theorem of Desargues (unit `s22.desargues_general`) in the assumed plane geometry
(`generalDesargues_of_congruence`, through the co-ordinate computation `Des.desargues_model` in the
space of triples of segments).

**Status.** proved
-/

theorem desargues_from_space : DesarguesTheorem P := by
  rcases isEmpty_or_nonempty L with hL | hL
  · constructor
    · rintro _ _ _ _ _ _ _ _ ⟨l, -⟩
      exact (hL.false l).elim
    · intro _ _ _ _ _ _ a
      exact (hL.false a).elim
  · exact necessary_condition partOfSpace_of_congruence

/-- The general theorem of Desargues in a plane geometry with I 1–2, II, III, IV. -/
theorem generalDesargues_of_congruence : GeneralDesargues P := by
  rcases isEmpty_or_nonempty L with hL | hL
  · intro _ _ _ _ _ _ _ _ _ a
    exact (hL.false a).elim
  · obtain ⟨l⟩ := id hL
    obtain ⟨O, E, hOE, -, -⟩ := exists_two_points (Point := P) l
    obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hOE
    exact Des.generalDesargues_of_planeInSpace (Des.planeInSpace ax)

end PlanePart

/-!
## [s22.via_theorem23] The proof by Theorem 23

*(§ 22)*

> It will be seen that the result just stated may also be deduced without difficulty from theorem 23 in the theory of proportion.

**Lean reading.** `desargues_via_theorem23` carries this out for the configuration to which
Theorem 23 applies as stated (segments, not signed segments): the converse of Theorem 32 when the
joining lines meet in `O` and `A'`, `B'`, `C'` lie on the half-rays `OA`, `OB`, `OC` (the triangles
`AOB`, `AOC`, `BOC` non-degenerate). With `a = OA`, `a' = OA'` etc., Theorem 23 gives
`a : b = a' : b'` from `AB ∥ A'B'` and `a : c = a' : c'` from `AC ∥ A'C'`; hence `b : c = b' : c'`
in the algebra of segments, and the corrected converse of Theorem 23 (`theorem23_converse`) gives
`BC ∥ B'C'` (the alternative `BC = B'C'` would force `B = B'`, so that `AB` and `A'B'` would meet).
The other configurations (points on opposite half-rays, parallel joins) need signed segments, i.e.
the proportions in the form of § 17; they are covered by `theorem32_converse`, and the first part of
Theorem 32 follows from the second (`DesAlg.desarguesI_of_II`). Plane geometry with I 1–2, II, III,
IV.

**Status.** proved (reading)
-/

/-- **The converse of Theorem 32 from Theorem 23**, for perspective triangles with `A'`, `B'`, `C'`
on the half-rays `OA`, `OB`, `OC`. -/
theorem desargues_via_theorem23 {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [PlaneCongruence P L] [PlaneParallels P L]
    {O A B C A' B' C' : P} (hAB : ¬Collinear (Line := L) A O B) (hAC : ¬Collinear (Line := L) A O C)
    (hBC : ¬Collinear (Line := L) B O C) (hA' : A' ∈ ray O A) (hB' : B' ∈ ray O B)
    (hC' : C' ∈ ray O C) (h1 : ParPts (L := L) A B A' B') (h2 : ParPts (L := L) A C A' C') :
    ParPts (L := L) B C B' C' := by
  obtain ⟨lO, hOl, -, -⟩ := collinear_of_mem_ray hA'
  obtain ⟨hAO, hBO, -⟩ := ne_of_not_collinear (L := L) hAB ⟨lO, hOl⟩
  obtain ⟨-, hCO, -⟩ := ne_of_not_collinear (L := L) hAC ⟨lO, hOl⟩
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) (Ne.symm hAO)
  have hA'O := ne_of_mem_ray hA'
  have hB'O := ne_of_mem_ray hB'
  have hC'O := ne_of_mem_ray hC'
  obtain ⟨l1, m1, k1, k2, k3, k4, p1⟩ := h1
  obtain ⟨l2, m2, n1, n2, n3, n4, p2⟩ := h2
  have e1 := theorem23 ax.hOE hAB hA' hB' k1 k2 k3 k4 p1
  have e2 := theorem23 ax.hOE hAC hA' hC' n1 n2 n3 n4 p2
  rw [segProportion_iff ax (Ne.symm hAO) (Ne.symm hBO) (Ne.symm hA'O) (Ne.symm hB'O)] at e1
  rw [segProportion_iff ax (Ne.symm hAO) (Ne.symm hCO) (Ne.symm hA'O) (Ne.symm hC'O)] at e2
  have ha := Pas.len_pos ax (Ne.symm hAO)
  have e3 : Pas.len ax O B * Pas.len ax O C' = Pas.len ax O C * Pas.len ax O B' := by
    apply mul_left_cancel₀ (ne_of_gt ha)
    linear_combination Pas.len ax O B * e2 - Pas.len ax O C * e1
  have hp : SegProportion (L := L) ax.O ax.E O B O C O B' O C' :=
    (segProportion_iff ax (Ne.symm hBO) (Ne.symm hCO) (Ne.symm hB'O) (Ne.symm hC'O)).2 e3
  obtain ⟨bc, hB1, hC1⟩ := exists_line (Line := L) (ne_of_not_collinear (L := L) hBC ⟨lO, hOl⟩).2.2
  have hB'C' : B' ≠ C' := by
    rintro rfl
    obtain ⟨l1, o1, b1, b1'⟩ := collinear_of_mem_ray hB'
    obtain ⟨l2, o2, c2, c2'⟩ := collinear_of_mem_ray hC'
    have e : l1 = l2 := line_unique (Ne.symm hB'O) o1 b1' o2 c2'
    subst e
    exact hBC ⟨l1, b1, o1, c2⟩
  obtain ⟨b'c', hB2, hC2⟩ := exists_line (Line := L) hB'C'
  rcases theorem23_converse ax.hOE hBC hB' hC' hB1 hC1 hB2 hC2 hp with
    ⟨hpar, -⟩ | ⟨-, hs, -⟩
  · exact ⟨bc, b'c', hB1, hC1, hB2, hC2, hpar⟩
  · exfalso
    have hBB : B = B' := eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hBO) hB' hs
    exact p1 ⟨B, k2, hBB ▸ k4⟩

end HilbertFoundations
