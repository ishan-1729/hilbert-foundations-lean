import HilbertFoundations.Analytic
import HilbertFoundations.Order
import HilbertFoundations.Congruence

/-!
# The introduction, the conclusion and the appendix

Covers `introduction`, `conclusion` and `appendix` of `data/foundations.json`.

* **Introduction** (namespace `HilbertFoundations.Intro`). Hilbert's claim of "a simple and complete
  set of independent axioms": the axioms of this edition are *not* independent (II 4 follows from the
  other axioms of groups I and II, Order.lean; the second conclusion of IV 6 follows from the first),
  while the groups III, IV, V are independent of the others (§§ 10–12; the case of V is re-checked
  here over `Ω(t)`); groups I–V do not determine the geometry up to isomorphism (the models over `Ω`
  and over `ℝ`); and, read literally, the space axioms I–V are satisfied by the real line with no
  plane at all (`Intro.coord_one_spaceGeometry`).
* **Conclusion** (namespace `HilbertFoundations.Conclusion`). Dehn's axioms of order (separation of pairs
  of points), derived from Hilbert's II 1–4 on every line, with a counterexample to the printed
  "consequently"; the comparison of the angle sum of a triangle with two right angles, defined from
  the primitive notions, which agree with Theorem 20 in euclidean planes; Dehn's theorems (the angle
  sum theorem, the non-legendrian and the semi-euclidean geometry, the pseudo-geometry) stated as
  `Prop`s, with their stated consequences proved (the two geometries are constructed, and their
  existence proved, in `CommentaryClose.lean`; the angle sum theorem and the pseudo-geometry are
  open here); the case without parallels, which with Hilbert's axioms of order is vacuous (Euclid
  I 27 gives parallels), proved in corrected form; the misprinted table.
* **Appendix** (namespace `HilbertFoundations.Appendix`). Hilbert's foundation of plane geometry on a
  group of displacements: the number plane `ℂ`, Jordan curves and regions, Jordan's theorem (stated
  here; proved in `JordanCurveClose.lean` from the library `JordanPick`, a copy of files of another
  project), the plane, displacements (the sense of traversal through winding numbers), axioms
  I–III, the three particular cases of axiom III (proved from it), the euclidean plane with its
  proper motions as a model of axioms I–III (so that they are compatible), and the main theorem
  and the steps of its proof as `Prop`s (open here), each of them verified in the euclidean plane;
  the steps that follow from the axioms directly (closedness of the true circles, transitivity of
  the rotations on them) are proved.
  As stated, the main theorem fails for the empty plane; the statement for a plane with a point is
  open, and four steps of its proof are shown to follow from it (`CommentaryCloseAux7.lean`,
  `CommentaryClose.lean`).
-/

namespace HilbertFoundations

open Module

namespace Intro

/-!
## [intro.axioms] Geometry rests on a small number of axioms

*(Introduction)*

> Geometry, like arithmetic, requires for its logical development only a small number of simple, fundamental principles. These fundamental principles are called the axioms of geometry. The choice of the axioms and the investigation of their relations to one another is a problem which, since the time of Euclid, has been discussed in numerous excellent memoirs to be found in the mathematical literature. … This problem is tantamount to the logical analysis of our intuition of space.

**Lean reading.** The axioms of geometry are the five groups of Basic.lean (`s1.groups`): one `Prop`
per axiom (`AxiomI1`, …, `AxiomV`) and one class per group or subgroup. "The investigation of their
relations to one another" is carried out in the project by derivations from exactly the classes
Hilbert names and by models in which a single axiom fails; the results bearing on the Introduction's
claims are the next three units. The sentence itself asserts nothing that can be proved.

**Status.** remark
-/

/-!
## [intro.complete] "Complete": groups I–V do not determine the geometry

*(Introduction)*

> The following investigation is a new attempt to choose for geometry a *simple* and *complete* set of *independent* axioms …

**Lean reading.** "Simple" is a judgement. "Complete" means, in the programme of the book, that the
axioms suffice for the deduction of the theorems of euclidean geometry; that has no formal
counterpart. The precise modern sense of completeness (categoricity: the axioms determine the
geometry up to isomorphism) does *not* hold for groups I–V of this book, and this is why the French
edition adds the Axiom of Completeness (Basic.lean, `ax.completeness`). `SpaceIsomorphic` is an
extension in the sense of `SpaceEmbedding` (injective maps on points, lines and planes preserving and
reflecting all relations) whose three maps are bijective. `axioms_not_categorical`: the coordinate
space over Hilbert's countable field `Ω` (§ 9) and the coordinate space over `ℝ` both satisfy all
the axioms I–V of space geometry (`omega_spaceGeometry`, `real_spaceGeometry`, Analytic.lean), and
they are not isomorphic, since the points of `Ω³` are countable (`countable_omega_points`) and those
of `ℝ³` are not (`not_countable_coord_real`). The degenerate model of the next unit is a further,
sharper failure of completeness of the axioms as worded.

**Status.** proved (reading)
-/

/-- Two systems of points, lines and planes are **isomorphic**: there is an extension of the first
into the second (`SpaceEmbedding`) that is bijective on points, lines and planes. -/
def SpaceIsomorphic (P L Pl P' L' Pl' : Type*) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P']
    [HasSegCong P'] [HasAngCong P'] : Prop :=
  ∃ e : SpaceEmbedding P L Pl P' L' Pl',
    Function.Surjective e.pt ∧ Function.Surjective e.line ∧ Function.Surjective e.plane

/-- The points of the real coordinate space are not countable. -/
theorem not_countable_coord_real : ¬Countable (Coord ℝ 3) := by
  intro h
  have hinj : Function.Injective (fun x : ℝ => (AffPt.ofV (fun _ : Fin 3 => x) : Coord ℝ 3)) := by
    intro x y hxy
    have := congrFun (congrArg AffPt.toV hxy) 0
    simpa using this
  have : Countable ℝ := hinj.countable
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr this)

/-- The geometries over `Ω` and over `ℝ` are not isomorphic. -/
theorem omega_real_not_isomorphic :
    ¬SpaceIsomorphic (Coord OmegaField 3) (CoordLine OmegaField 3) (CoordPlane OmegaField 3)
      (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) := by
  rintro ⟨e, he, -, -⟩
  have := countable_omega_points
  exact not_countable_coord_real he.countable

/-- **Groups I–V are not categorical**: two non-isomorphic geometries satisfy all of them. -/
theorem axioms_not_categorical :
    SpaceGeometry (Coord OmegaField 3) (CoordLine OmegaField 3) (CoordPlane OmegaField 3) ∧
      SpaceGeometry (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) ∧
      ¬SpaceIsomorphic (Coord OmegaField 3) (CoordLine OmegaField 3) (CoordPlane OmegaField 3)
        (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) :=
  ⟨omega_spaceGeometry, real_spaceGeometry, omega_real_not_isomorphic⟩

/-!
## [intro.literal_I7] As worded, the space axioms admit a geometry consisting of one line

*(Introduction)*

> The following investigation is a new attempt to choose for geometry a *simple* and *complete* set of *independent* axioms …

**Lean reading.** Basic.lean (`ax.I7`) reads the space clause of I 7 literally: "in space there
exist at least four points not lying in a plane" is true when there is no plane at all. With this
wording the axioms of space geometry admit a degenerate geometry. The real line `Coord ℝ 1`, with its
lines `CoordLine ℝ 1` (the affine subspaces of dimension 1, i.e. the whole line, `lineTop`) and planes
`CoordPlane ℝ 1` (the affine subspaces of dimension 2: there are none, `coordPlane_one_isEmpty`),
the usual betweenness and the metric congruences of § 9 (Analytic.lean), satisfies all the space
axioms I–V: `coord_one_spaceGeometry : SpaceGeometry (Coord ℝ 1) (CoordLine ℝ 1) (CoordPlane ℝ 1)`.
I 3, I 4 and IV 6 hold vacuously because all points are collinear (`coord_one_collinear`); I 5,
I 6, the plane clause of I 7, II 5, III and the laying off of angles hold vacuously because there
is no plane; the space clause of I 7 holds with any four points; the linear axioms (I 1–2, II 1–4,
IV 1–3, the plane-free parts of IV 4–5, V) are those of the coordinate geometry of § 9 in dimension
one. There are not even three non-collinear points (`not_existsNoncollinear_coord_one`), so this
"geometry of space" is not a plane geometry. Hilbert evidently means that some plane exists (with
I 3, I 7 this gives four points in general position); results of the project that need a plane
assume one. Order.lean uses the same reading to show that the literal space axioms of groups I, II
do not imply II 4 (`axiomII4_not_of_others_without_planes`).

**Status.** proved
-/

/-- The real line has no plane. -/
theorem coordPlane_one_isEmpty : IsEmpty (CoordPlane ℝ 1) := by
  refine ⟨fun α => ?_⟩
  have h1 := α.finrank_direction
  have : FiniteDimensional ℝ (AffPt ℝ (Fin 1 → ℝ)) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin 1 → ℝ))
  have h2 := Submodule.finrank_le α.carrier.direction
  have : finrank ℝ (AffPt ℝ (Fin 1 → ℝ)) = 1 := Module.finrank_fin_fun ℝ
  omega

/-- The real line as a line of the coordinate geometry. -/
noncomputable def lineTop : CoordLine ℝ 1 :=
  ⟨⊤, by rw [AffineSubspace.direction_top, finrank_top]; exact Module.finrank_fin_fun ℝ⟩

/-- All points of the real line are collinear. -/
theorem coord_one_collinear (A B C : Coord ℝ 1) : Collinear A B C :=
  ⟨lineTop, AffineSubspace.mem_top _ _ _, AffineSubspace.mem_top _ _ _,
    AffineSubspace.mem_top _ _ _⟩

/-- The real line has no three non-collinear points. -/
theorem not_existsNoncollinear_coord_one : ¬ExistsNoncollinear (Coord ℝ 1) := by
  rintro ⟨A, B, C, h⟩; exact h (coord_one_collinear A B C)

/-- The real line satisfies I 1–7, read literally. -/
theorem coord_one_spaceConnection :
    SpaceConnection (Coord ℝ 1) (CoordLine ℝ 1) (CoordPlane ℝ 1) :=
  { (inferInstance : Connection (Coord ℝ 1) (CoordLine ℝ 1)) with
    ax_I3 := fun A B C h => absurd (coord_one_collinear A B C) h
    ax_I4 := fun A B C _ _ h => absurd (coord_one_collinear A B C) h
    ax_I5 := fun _ _ _ α => (coordPlane_one_isEmpty.false α).elim
    ax_I6 := fun α => (coordPlane_one_isEmpty.false α).elim
    ax_I7_plane := fun α => (coordPlane_one_isEmpty.false α).elim
    ax_I7_space := ⟨0, 0, 0, 0, fun ⟨α, _⟩ => coordPlane_one_isEmpty.false α⟩ }

/-- **The real line, without planes, satisfies all the axioms I–V of space geometry** as worded. -/
theorem coord_one_spaceGeometry :
    SpaceGeometry (Coord ℝ 1) (CoordLine ℝ 1) (CoordPlane ℝ 1) :=
  { coord_one_spaceConnection, (inferInstance : TriangleCongruence (Coord ℝ 1) (CoordLine ℝ 1)),
    (inferInstance : Archimedes (Coord ℝ 1) (CoordLine ℝ 1)) with
    ax_II5 := fun _ _ _ α => (coordPlane_one_isEmpty.false α).elim
    ax_III := fun α => (coordPlane_one_isEmpty.false α).elim
    ax_IV4 := fun _ _ _ α => (coordPlane_one_isEmpty.false α).elim }

/-- The degenerate geometry: all axioms I–V of space, no plane, no three non-collinear points. -/
theorem degenerate_space_geometry :
    SpaceGeometry (Coord ℝ 1) (CoordLine ℝ 1) (CoordPlane ℝ 1) ∧ IsEmpty (CoordPlane ℝ 1) ∧
      ¬ExistsNoncollinear (Coord ℝ 1) :=
  ⟨coord_one_spaceGeometry, coordPlane_one_isEmpty, not_existsNoncollinear_coord_one⟩

/-!
## [intro.independent] The axioms of this edition are not independent

*(Introduction)*

> The following investigation is a new attempt to choose for geometry a *simple* and *complete* set of *independent* axioms …

**Lean reading.** An axiom is independent of the others if some system satisfies all the others and
not it. As printed, the claim is false for the axioms of this edition, in two places.

1. *II 4 follows from the other axioms of groups I and II* in plane geometry (E. H. Moore, 1902):
   `axiomII4_of_others` (Order.lean, unit `s3.II4_dependent`). `not_axiomII4Independent`: there is
   no system satisfying group I of plane geometry, `BetweenOnLine`, II 1–3 and II 5 in which II 4
   fails, so a fortiori none satisfying all the other axioms I–V. In space the same holds as soon as
   a plane exists (`axiomII4_of_others_space`); under the literal reading of I 7 (unit
   `intro.literal_I7`) it does not (`axiomII4_not_of_others_without_planes`).
2. *The second conclusion of IV 6 is redundant*: `∠ACB ≡ ∠A'C'B'` is the first conclusion applied
   to the triangles `ACB`, `A'C'B'` (with the plane-free axioms of angle congruence, for `angCong_wd`):
   `axiomIV6_of_first`. Later editions state only the first.

Corrected claim, proved here: the individual axioms of this edition are *not* independent (items 1
and 2). What Chapter II establishes instead is the independence of the *groups* III, IV, V from the
remaining ones: the axiom of parallels (§ 10), the axioms of congruence (IV 6, § 11) and
Archimedes's axiom (§ 12), together with the compatibility of all five groups (§ 9,
`axiomsConsistent`). Those are units of Independence.lean and Analytic.lean; this file neither
imports nor relies on the independence models of §§ 10–11. The case of group V is re-proved here:
`omegaT_independence_V`, the coordinate plane over Hilbert's non-archimedean field `Ω(t)`
(AnalyticAux3.lean) satisfies groups I–IV of plane geometry and not Archimedes's axiom
(`not_axiomV_of_infinite`: over an ordered field with an element `T` exceeding every natural number,
the points `n e` laid off from `0` with the unit `e` never pass `T e`).

**Status.** proved (corrected)
-/

/-- **II 4 would be independent** (in plane geometry) if some system satisfied group I, the
presupposition `BetweenOnLine` and II 1–3, II 5, but not II 4. -/
def AxiomII4Independent.{u, v} : Prop :=
  ∃ (P : Type u) (L : Type v) (_ : HasLines P L) (_ : HasBetween P), PlaneConnection P L ∧ BetweenOnLine P ∧
    AxiomII1 P ∧ AxiomII2 P ∧ AxiomII3 P ∧ AxiomII5 P ∧ ¬AxiomII4 P

/-- **II 4 is not independent** (E. H. Moore): it follows from the other axioms of groups I, II. -/
theorem not_axiomII4Independent : ¬AxiomII4Independent := by
  rintro ⟨P, L, _, _, hc, hB, h1, h2, h3, h5, h4⟩
  exact h4 (axiomII4_of_others (L := L) hB h1 h2 h3 h5)

/-- The first half of IV 6: `∠ABC ≡ ∠A'B'C'` only. -/
def AxiomIV6First (P : Type*) {L : Type*} [HasLines P L] [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ A B C A' B' C' : P, IsTriangle A B C → IsTriangle A' B' C' →
    SegCong A B A' B' → SegCong A C A' C' → AngCong B A C B' A' C' → AngCong A B C A' B' C'

/-- **The second conclusion of IV 6 is redundant**: the first half of IV 6 gives all of it. -/
theorem axiomIV6_of_first {P L : Type*} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [AngleCongruence P L] (h : AxiomIV6First P) : AxiomIV6 P := by
  intro A B C A' B' C' hT hT' hAB hAC hA
  refine ⟨h A B C A' B' C' hT hT' hAB hAC hA, ?_⟩
  have hT2 : IsTriangle A C B := fun hc => hT hc.swap23
  have hT2' : IsTriangle A' C' B' := fun hc => hT' hc.swap23
  have hBAC : ¬Collinear B A C := fun hc => hT hc.swap12
  have hBAC' : ¬Collinear B' A' C' := fun hc => hT' hc.swap12
  exact h A C B A' C' B' hT2 hT2' hAC hAB
    (angCong_swap_right (Line := L) (fun hc => hBAC hc.swap13) hBAC'
      (angCong_swap_left (Line := L) hBAC hBAC' hA))

/-- Over an ordered field with an infinitely large element, Archimedes's axiom fails in the
coordinate geometry of any positive dimension. -/
theorem not_axiomV_of_infinite {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (T : K) (hT : ∀ m : ℕ, (m : K) < T) : ¬AxiomV (Coord K (n + 1)) := by
  intro hV
  let e : Coord K (n + 1) := AffPt.ofV (fun _ => (1 : K))
  have hT1 : (1 : K) < T := by exact_mod_cast hT 1
  have hT0 : (0 : K) < T := zero_lt_one.trans hT1
  have hne : ∀ a b : K, a ≠ b → a • e ≠ b • e := by
    intro a b hab h
    apply hab
    have := congrFun (congrArg AffPt.toV h) 0
    simpa [e] using this
  have h01 : Between ((0 : ℕ) • e) ((1 : ℕ) • e) (T • e) := by
    refine AffPt.sbtw_iff_param.2 ⟨?_, T⁻¹, inv_pos.2 hT0, inv_lt_one_of_one_lt₀ hT1, ?_⟩
    · simpa using hne 0 T hT0.ne
    · simp [smul_smul, inv_mul_cancel₀ hT0.ne']
  have hstep : ∀ k : ℕ,
      Between ((k : K) • e) (((k + 1 : ℕ) : K) • e) (((k + 2 : ℕ) : K) • e) := by
    intro k
    refine AffPt.sbtw_iff_param.2 ⟨hne _ _ (by push_cast; linarith), 1 / 2, by norm_num,
      by norm_num, ?_⟩
    rw [← sub_smul, smul_smul, ← add_smul]
    congr 1; push_cast; ring
  have hcong : ∀ a b : ℕ, SegCong ((a : K) • e) (((a + 1 : ℕ) : K) • e) ((b : K) • e)
      (((b + 1 : ℕ) : K) • e) := by
    intro a b
    rw [Coord.segCong_iff, ← sub_smul, ← sub_smul]
    push_cast; ring_nf
  obtain ⟨N, hN⟩ := hV (fun k => (k : K) • e) (T • e) (by simpa using h01) hstep hcong
  obtain ⟨-, s, hs0, hs1, hs⟩ := AffPt.sbtw_iff_param.1 hN
  have := congrFun (congrArg AffPt.toV hs) 0
  simp [e] at this
  have hNT := hT N
  nlinarith

/-- Archimedes's axiom fails in the coordinate plane over `Ω(t)`. -/
theorem omegaT_not_axiomV : ¬AxiomV (Coord OmegaT 2) :=
  not_axiomV_of_infinite OmegaT.t OmegaT.natCast_lt_t

/-- **Independence of group V** (§ 12): the plane over `Ω(t)` satisfies groups I–IV, not V. -/
theorem omegaT_independence_V :
    PlaneParallels (Coord OmegaT 2) (CoordLine OmegaT 2) ∧
      PlaneCongruence (Coord OmegaT 2) (CoordLine OmegaT 2) ∧ ¬AxiomV (Coord OmegaT 2) :=
  ⟨inferInstance, inferInstance, omegaT_not_axiomV⟩

/-!
## [intro.groups] The significance of the different groups of axioms

*(Introduction)*

> … and to deduce from these the most important geometrical theorems in such a manner as to bring out as clearly as possible the significance of the different groups of axioms and the scope of the conclusions to be derived from the individual axioms.

**Lean reading.** A programme, not a claim. In the project it is carried out by the house rule of
Basic.lean: every theorem assumes exactly the axiom classes Hilbert uses for it, so the scope of each
group can be read off the hypotheses.

**Status.** remark
-/

end Intro

namespace Conclusion

/-!
## [concl.euclidean_only] The book treats euclidean geometry

*(Conclusion)*

> The preceding work treats essentially of the problems of the euclidean geometry only; that is to say, it is a discussion of the questions which present themselves when we admit the validity of the axiom of parallels. It is none the less important to discuss the principles and the fundamental theorems when we disregard the axiom of parallels.

**Lean reading.** A description of the book and a programme. In the project every result that does
not use the axiom of parallels says so by not assuming `PlaneParallels` / `SpaceParallels`.

**Status.** remark
-/

/-!
## [concl.lie] Geometry from points and groups of transformations; Lie's differentiability

*(Conclusion)*

> We have thus excluded from our study the important question as to whether it is possible to construct a geometry in a logical manner, without introducing the notion of the plane and the straight line, by means of only points as elements, making use of the idea of groups of transformations, or employing the idea of distance. … First of all, it would seem to me desirable to discuss thoroughly the hypothesis of Lie, that functions which produce transformations are not only continuous, but may also be differentiated. As to myself, it does not seem to me probable that the geometrical axioms included in the condition for the possibility of differentiation are all necessary.

**Lean reading.** A question and a conjecture, neither precise enough to be stated. Hilbert's own
answer for the plane is the Appendix: its axioms I–III (namespace `HilbertFoundations.Appendix`)
speak of points and a group of continuous displacements only, with no lines, no planes and no
differentiability; the euclidean plane is a model of them (`app.main_theorem`), and the theorem that
they characterize the euclidean and the Bolyai–Lobachevskian plane is stated there (open here).

**Status.** remark
-/

/-!
## [concl.dehn] Dehn's investigation rests on groups I, II, IV

*(Conclusion)*

> In the treatment of all questions of this character, I believe the methods and the principles employed in the preceding work will be of value. As an example, let me call attention to an investigation undertaken at my suggestion by Mr. Dehn, and which has already appeared. … In this article, he has discussed the known theorems of Legendre concerning the sum of the angles of a triangle, in the demonstration of which that geometer made use of the idea of continuity.
>
> The investigation of Mr. Dehn rests upon the axioms of connection, of order, and of congruence; that is to say, upon the axioms of groups I, II, IV. However, the axiom of parallels and the axiom of Archimedes are excluded.

**Lean reading.** In the classes of Basic.lean, Dehn's axiom system is `PlaneCongruence P L` (groups
I, II, IV of plane geometry) without `PlaneParallels` and `Archimedes`; the statements of Dehn's
theorems below (`AngleSumTheorem`, `NonLegendrianGeometryExists`, `SemiEuclideanGeometryExists`,
`NoParallelsTheorem`, `PseudoGeometryTheorem`) assume exactly this. Dehn's own axioms of order are
more general (next unit); the statements use Hilbert's group II, a special case.

**Status.** remark
-/

/-!
## [concl.dehn_order] Dehn's axioms of order: separation of pairs of points

*(Conclusion)*

> Moreover, the axioms of order are stated in a more general manner than in the present work, and in substance as follows: Among four points $A, B, C, D$ of a straight line, there are always two, for example $A, C$, which are separated from the other two and conversely. Five points $A, B, C, D, E$ upon a straight line may always be so arranged that $A, C$ shall be separated from $B, E$ and from $B, D$. Consequently, $A, D$ are always separated from $B, E$ and from $C, E$, etc. The (elliptic) geometry of Riemann, which we have not considered in the present work, is in this way not necessarily excluded.

**Lean reading.** Dehn's primitive notion is a relation `Sep A C B D` ("`A, C` are separated from
`B, D`") among four points of a line. The two clauses are `Prop`s about a relation `Sep` on a set
`S` of points (the points of a line): `FourPoint` (four distinct points can be named `A, B, C, D`
so that `A, C` are separated from `B, D` and, conversely, `B, D` from `A, C`; "for example" is read
like "can be so arranged" in II 4, by a permutation) and `FivePoint` (five distinct points can be
arranged so that `A, C` are separated from `B, E` and from `B, D`). That they are "more general"
than Hilbert's axioms of order: betweenness gives a separation relation, `SepOf Between` (exactly
one of `B`, `D` lies between `A` and `C`), and II 1–4 give Dehn's clauses on every line:
`fourPoint_line`, `fivePointCorrected_line` (through the order of sequence of the points of a line,
Order.lean `OrderLin.lineOrder`, `OrderLin.between_iff_lineLt`, and the case of an abstract linear
order, `fourPoint_lin`, `fivePointCorrected_lin`). The sentence "Consequently, `A, D` are always
separated from `B, E` and from `C, E`" is a non sequitur as printed: the two separations named in the
five-point clause do not force the other two. `not_fivePointConsequenceLiteral`: on the rational
line the points `A, B, C, D, E = 0, 1, 2, 4, 3` have `A, C` separated from `B, E` and from `B, D`,
but `A, D` are not separated from `B, E` (both `1` and `3` lie between `0` and `4`). The intended
statement is that five points of a line can be arranged in their cyclic order, and then all four
separations hold: `FivePointCorrected`, which implies `FivePoint` (`fivePoint_of_corrected`) and
holds on every line of a geometry satisfying II 1–4 (`fivePointCorrected_line`). The last sentence
is a remark: separation of pairs, unlike betweenness, makes sense on the closed lines of elliptic
geometry; the elliptic plane is not constructed here.

**Status.** proved (corrected)
-/

/-- `A, C` **are separated from** `B, D` with respect to a betweenness relation: exactly one of
`B`, `D` lies between `A` and `C`. -/
def SepOf {α : Type*} (Btw : α → α → α → Prop) (A C B D : α) : Prop :=
  Xor (Btw A B C) (Btw A D C)

/-- Dehn's four-point clause. -/
def FourPoint {α : Type*} (Sep : α → α → α → α → Prop) (S : Set α) : Prop :=
  ∀ P : Fin 4 → α, Function.Injective P → (∀ i, P i ∈ S) → ∃ σ : Equiv.Perm (Fin 4),
    Sep (P (σ 0)) (P (σ 2)) (P (σ 1)) (P (σ 3)) ∧ Sep (P (σ 1)) (P (σ 3)) (P (σ 0)) (P (σ 2))

/-- Dehn's five-point clause. -/
def FivePoint {α : Type*} (Sep : α → α → α → α → Prop) (S : Set α) : Prop :=
  ∀ P : Fin 5 → α, Function.Injective P → (∀ i, P i ∈ S) → ∃ σ : Equiv.Perm (Fin 5),
    Sep (P (σ 0)) (P (σ 2)) (P (σ 1)) (P (σ 4)) ∧ Sep (P (σ 0)) (P (σ 2)) (P (σ 1)) (P (σ 3))

/-- The consequence Hilbert draws, read literally: every arrangement as in the five-point clause
also has `A, D` separated from `B, E` and from `C, E`. -/
def FivePointConsequenceLiteral {α : Type*} (Sep : α → α → α → α → Prop) (S : Set α) : Prop :=
  ∀ Q : Fin 5 → α, Function.Injective Q → (∀ i, Q i ∈ S) →
    Sep (Q 0) (Q 2) (Q 1) (Q 4) → Sep (Q 0) (Q 2) (Q 1) (Q 3) →
      Sep (Q 0) (Q 3) (Q 1) (Q 4) ∧ Sep (Q 0) (Q 3) (Q 2) (Q 4)

/-- The corrected five-point clause: five points can be arranged so that all four separations hold. -/
def FivePointCorrected {α : Type*} (Sep : α → α → α → α → Prop) (S : Set α) : Prop :=
  ∀ P : Fin 5 → α, Function.Injective P → (∀ i, P i ∈ S) → ∃ σ : Equiv.Perm (Fin 5),
    Sep (P (σ 0)) (P (σ 2)) (P (σ 1)) (P (σ 4)) ∧ Sep (P (σ 0)) (P (σ 2)) (P (σ 1)) (P (σ 3)) ∧
    Sep (P (σ 0)) (P (σ 3)) (P (σ 1)) (P (σ 4)) ∧ Sep (P (σ 0)) (P (σ 3)) (P (σ 2)) (P (σ 4))

/-- Betweenness of a linear order. -/
def LinBtw {α : Type*} [LinearOrder α] (x y z : α) : Prop := (x < y ∧ y < z) ∨ (z < y ∧ y < x)

theorem strictMono_sort {α : Type*} [LinearOrder α] {n : ℕ} (P : Fin n → α)
    (hP : Function.Injective P) : StrictMono (P ∘ Tuple.sort P) :=
  (Tuple.monotone_sort P).strictMono_of_injective (hP.comp (Tuple.sort P).injective)

theorem fourPoint_lin {α : Type*} [LinearOrder α] : FourPoint (SepOf (LinBtw (α := α))) Set.univ := by
  intro P hP _
  have hm := strictMono_sort P hP
  refine ⟨Tuple.sort P, ?_, ?_⟩ <;>
  · have h01 := hm (show (0 : Fin 4) < 1 by decide)
    have h12 := hm (show (1 : Fin 4) < 2 by decide)
    have h23 := hm (show (2 : Fin 4) < 3 by decide)
    simp only [Function.comp] at h01 h12 h23
    simp only [SepOf, LinBtw, Xor]
    first
      | exact Or.inl ⟨Or.inl ⟨h01, h12⟩, fun h => by
          rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> order⟩
      | exact Or.inr ⟨Or.inl ⟨h12, h23⟩, fun h => by
          rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> order⟩

theorem fivePointCorrected_lin {α : Type*} [LinearOrder α] :
    FivePointCorrected (SepOf (LinBtw (α := α))) Set.univ := by
  intro P hP _
  have hm := strictMono_sort P hP
  have h01 := hm (show (0 : Fin 5) < 1 by decide)
  have h12 := hm (show (1 : Fin 5) < 2 by decide)
  have h23 := hm (show (2 : Fin 5) < 3 by decide)
  have h34 := hm (show (3 : Fin 5) < 4 by decide)
  simp only [Function.comp] at h01 h12 h23 h34
  refine ⟨Tuple.sort P, ?_, ?_, ?_, ?_⟩ <;> simp only [SepOf, LinBtw, Xor]
  · exact Or.inl ⟨Or.inl ⟨h01, h12⟩, fun h => by rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> order⟩
  · exact Or.inl ⟨Or.inl ⟨h01, h12⟩, fun h => by rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> order⟩
  · exact Or.inl ⟨Or.inl ⟨h01, h12.trans h23⟩, fun h => by rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> order⟩
  · exact Or.inl ⟨Or.inl ⟨h01.trans h12, h23⟩, fun h => by rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> order⟩

theorem fivePoint_of_corrected {α : Type*} {Sep : α → α → α → α → Prop} {S : Set α}
    (h : FivePointCorrected Sep S) : FivePoint Sep S := by
  intro P hP hS
  obtain ⟨σ, h1, h2, -, -⟩ := h P hP hS
  exact ⟨σ, h1, h2⟩

/-- Hilbert's "consequently" is a non sequitur: on the rational line, the points `0, 1, 2, 4, 3`
satisfy the two separations of the five-point clause but not the third. -/
theorem not_fivePointConsequenceLiteral :
    ¬FivePointConsequenceLiteral (SepOf (LinBtw (α := ℚ))) Set.univ := by
  intro h
  have hinj : Function.Injective (![0, 1, 2, 4, 3] : Fin 5 → ℚ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have := (h ![0, 1, 2, 4, 3] hinj (fun _ => trivial) (by norm_num [SepOf, LinBtw, Xor])
    (by norm_num [SepOf, LinBtw, Xor])).1
  norm_num [SepOf, LinBtw, Xor] at this

section Line

variable {P L : Type*} [HasLines P L] [HasBetween P] [LineOrder P L]

/-- Betweenness on a line is the betweenness of its order of sequence. -/
theorem linBtw_iff_between {a : L} {O U : P} (hO : O ∈ a) (hU : U ∈ a) (hOU : O ≠ U)
    (x y z : {X : P // X ∈ a}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    @LinBtw _ (OrderLin.lineOrder hO hU hOU) x y z ↔ Between (x : P) y z := by
  rw [OrderLin.between_iff_lineLt hO hU hOU x.2 y.2 z.2 (fun e => hxy (Subtype.ext e))
    (fun e => hxz (Subtype.ext e)) (fun e => hyz (Subtype.ext e))]
  rfl

theorem sepOf_iff {a : L} {O U : P} (hO : O ∈ a) (hU : U ∈ a) (hOU : O ≠ U)
    (x z y w : {X : P // X ∈ a}) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hxw : x ≠ w)
    (hwz : w ≠ z) :
    @SepOf _ (@LinBtw _ (OrderLin.lineOrder hO hU hOU)) x z y w ↔ SepOf Between (x : P) z y w := by
  unfold SepOf
  rw [linBtw_iff_between hO hU hOU x y z hxy hxz hyz, linBtw_iff_between hO hU hOU x w z hxw hxz hwz]

/-- **Hilbert's axioms of order give Dehn's four-point clause** on every line. -/
theorem fourPoint_line (a : L) : FourPoint (SepOf (Between (Point := P))) {X | X ∈ a} := by
  intro Q hQ ha
  have h01 : Q 0 ≠ Q 1 := fun e => absurd (hQ e) (by decide)
  let _ : LinearOrder {X : P // X ∈ a} := OrderLin.lineOrder (ha 0) (ha 1) h01
  let R : Fin 4 → {X : P // X ∈ a} := fun i => ⟨Q i, ha i⟩
  have hR : Function.Injective R := fun i j e => hQ (congrArg Subtype.val e)
  obtain ⟨σ, h1, h2⟩ := fourPoint_lin R hR (fun _ => trivial)
  have hne : ∀ i j : Fin 4, i ≠ j → R (σ i) ≠ R (σ j) := fun i j h e => h (σ.injective (hR e))
  refine ⟨σ, (sepOf_iff (ha 0) (ha 1) h01 _ _ _ _ ?_ ?_ ?_ ?_ ?_).1 h1,
    (sepOf_iff (ha 0) (ha 1) h01 _ _ _ _ ?_ ?_ ?_ ?_ ?_).1 h2⟩ <;> exact hne _ _ (by decide)

/-- **Hilbert's axioms of order give the corrected five-point clause** on every line. -/
theorem fivePointCorrected_line (a : L) :
    FivePointCorrected (SepOf (Between (Point := P))) {X | X ∈ a} := by
  intro Q hQ ha
  have h01 : Q 0 ≠ Q 1 := fun e => absurd (hQ e) (by decide)
  let _ : LinearOrder {X : P // X ∈ a} := OrderLin.lineOrder (ha 0) (ha 1) h01
  let R : Fin 5 → {X : P // X ∈ a} := fun i => ⟨Q i, ha i⟩
  have hR : Function.Injective R := fun i j e => hQ (congrArg Subtype.val e)
  obtain ⟨σ, h1, h2, h3, h4⟩ := fivePointCorrected_lin R hR (fun _ => trivial)
  have hne : ∀ i j : Fin 5, i ≠ j → R (σ i) ≠ R (σ j) := fun i j h e => h (σ.injective (hR e))
  refine ⟨σ, (sepOf_iff (ha 0) (ha 1) h01 _ _ _ _ ?_ ?_ ?_ ?_ ?_).1 h1,
    (sepOf_iff (ha 0) (ha 1) h01 _ _ _ _ ?_ ?_ ?_ ?_ ?_).1 h2,
    (sepOf_iff (ha 0) (ha 1) h01 _ _ _ _ ?_ ?_ ?_ ?_ ?_).1 h3,
    (sepOf_iff (ha 0) (ha 1) h01 _ _ _ _ ?_ ?_ ?_ ?_ ?_).1 h4⟩ <;> exact hne _ _ (by decide)

end Line

/-!
## [concl.pseudo_geometry] Dehn's pseudo-geometry

*(Conclusion)*

> Upon the basis of the axioms of connection, order, and congruence, that is to say, the axioms I, II, IV, we may introduce, in the well known manner, the elements called ideal,–ideal points, ideal straight lines, and ideal planes. Having done this, Mr. Dehn demonstrates the following theorem.
>
> If, with the exception of the straight line $t$ and the points lying upon it, we regard all of the straight lines and all of the points (ideal or real) of a plane as the elements of a new geometry, we may then define a new kind of congruence so that all of the axioms of connection, order, and congruence, as well as the axiom of Euclid, shall be fulfilled. In this new geometry, the straight line $t$ takes the place of the straight line at infinity.
>
> This euclidean geometry, superimposed upon the non-euclidean plane, may be called a *pseudo-geometry* and the new kind of congruence a *pseudo-congruence.*

**Lean reading.** The ideal elements (the projective completion of a plane satisfying I, II, IV by
pencils of lines) are not defined in the book ("in the well known manner") and are not constructed
here, so Dehn's theorem cannot be stated in full. `PseudoGeometryTheorem` records its consequences
for the real points: for every plane satisfying groups I, II, IV (`PlaneCongruence`) and every line
`t`, there are a plane satisfying groups I–IV (`PlaneParallels` and `PlaneCongruence`: the new
geometry, with Euclid's axiom) and an injective map `φ` of the points off `t` into it that (1)
preserves and reflects collinearity (the real points off `t` are points of the pseudo-geometry, and
its lines through two of them are the old lines), and (2) makes `t` "the straight line at infinity":
two distinct old lines `AB`, `CD` (`A, B, C, D` off `t`) meeting in a point `T` of `t` become
parallel, i.e. no point of the new geometry is collinear both with `φ A, φ B` and with `φ C, φ D`.
Betweenness is deliberately not required to be preserved (the new order is the order of the
projective plane cut along `t`), nor is the behaviour of the ideal points stated. This is a deep
theorem of Dehn (*Math. Ann.* 53) and is not proved here.

**Status.** stated (open here)
-/

/-- **Dehn's pseudo-geometry** (incidence part): the points off a line `t` of a plane satisfying
groups I, II, IV are, with their collinearity, points of a plane satisfying groups I–IV, in which
`t` plays the part of the line at infinity. -/
def PseudoGeometryTheorem : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → ∀ t : L,
      ∃ (P' L' : Type) (_ : HasLines P' L') (_ : HasBetween P') (_ : HasSegCong P')
        (_ : HasAngCong P'), PlaneParallels P' L' ∧ PlaneCongruence P' L' ∧
        ∃ φ : {A : P // A ∉ t} → P', Function.Injective φ ∧
          (∀ A B C : {A : P // A ∉ t},
            (Collinear (Line := L) (A : P) B C ↔ Collinear (Line := L') (φ A) (φ B) (φ C))) ∧
          ∀ (A B C D : {A : P // A ∉ t}) (T : P), T ∈ t → (A : P) ≠ B → (C : P) ≠ D →
            ¬Collinear (Line := L) (A : P) B C → Collinear (Line := L) (A : P) B T →
            Collinear (Line := L) (C : P) D T →
              ∀ X : P', ¬(Collinear (Line := L') (φ A) (φ B) X ∧ Collinear (Line := L') (φ C) (φ D) X)

/-!
## [concl.angle_sum] The angle sum of one triangle decides that of all triangles

*(Conclusion)*

> By aid of the preceding theorem, we may now introduce an algebra of segments relating to the plane and depending upon the developments made in § 15, … This algebra of segments permits the demonstration of the following important theorem:
>
> If, in any triangle whatever, the sum of the angles is greater than, equal to, or less than, two right angles, then the same is true for all triangles.

**Lean reading.** Angles are not added in this edition, so the three comparisons are defined from
the primitive notions, through the exterior angle at `C` (the sum of the angles of `ABC` is two right
angles iff `∠A + ∠B` equals the exterior angle `∠XCB`, `X` on `AC` beyond `C`).
`ExteriorConfig L A B C X Y` lays `∠CAB` off at `C`: `C` lies between `A` and `X`, `∠XCY ≡ ∠CAB`,
and `Y` lies on the side of the line `AC` where `B` lies (corresponding angles). Then
`AngleSumEqTwoRight` says that `Y` is interior to `∠XCB` and `∠YCB ≡ ∠CBA`; `AngleSumLtTwoRight`
that `Y` is interior to `∠XCB` and the angle `∠CBA`, laid off at `C` from `CB`, falls inside `∠YCB`;
`AngleSumGtTwoRight` that `Y` is not interior to `∠XCB` (then `∠A` alone reaches the exterior
angle), or that `∠YCB` is congruent to an angle `∠ZBC` with `Z` interior to `∠CBA` (then `∠YCB < ∠B`).
That the three cases are exclusive and exhaustive in a plane satisfying I, II, IV is part of the
theory the statement needs and is not proved here. The definitions are not vacuous and agree with
Theorem 20: in a plane satisfying groups I–IV every triangle `ABC` (with `A ≠ B`, which only excludes
the degenerate geometry of a single point) has angle sum two right angles in this sense
(`angleSumEqTwoRight_of_parallels`: `∠A` laid off at `C` gives a parallel to `AB` by the converse of
Theorem 19, and Theorem 19 gives `∠YCB ≡ ∠CBA`). `AngleSumTheorem`: in every plane satisfying
groups I, II, IV (`PlaneCongruence`), if one triangle has angle sum greater than / equal to / less
than two right angles, so has every triangle. Not proved here: Dehn's proof goes through the
pseudo-geometry (`concl.pseudo_geometry`) and the segment calculus of § 15, and any proof (also the
classical one of Legendre and Saccheri) needs a large part of neutral geometry (addition of angles,
the exterior angle theorem, Saccheri quadrilaterals) that the project does not develop.

**Status.** stated (open here)
-/

section AngleSum

variable {P L : Type*} [HasLines P L] [HasBetween P] [HasAngCong P]

variable (L) in
/-- The exterior angle at `C` of the triangle `ABC` with the angle `∠A` laid off at it: `X` lies on
`AC` beyond `C`, and `∠XCY ≡ ∠CAB` with `Y` on the side of the line `AC` where `B` lies. -/
def ExteriorConfig (A B C X Y : P) : Prop :=
  Between A C X ∧ AngCong C A B X C Y ∧ ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B

variable (L) in
/-- **The sum of the angles of `ABC` is two right angles**: `∠A + ∠B` is the exterior angle at `C`. -/
def AngleSumEqTwoRight (A B C : P) : Prop :=
  IsTriangle (Line := L) A B C ∧ ∃ X Y : P, ExteriorConfig L A B C X Y ∧
    Y ∈ Interior (Line := L) X C B ∧ AngCong Y C B C B A

variable (L) in
/-- **The sum of the angles of `ABC` is less than two right angles**: `∠A + ∠B` is smaller than the
exterior angle at `C`. -/
def AngleSumLtTwoRight (A B C : P) : Prop :=
  IsTriangle (Line := L) A B C ∧ ∃ X Y : P, ExteriorConfig L A B C X Y ∧
    Y ∈ Interior (Line := L) X C B ∧ ∃ Z ∈ Interior (Line := L) Y C B, AngCong Z C B C B A

variable (L) in
/-- **The sum of the angles of `ABC` is greater than two right angles**: `∠A + ∠B` exceeds the
exterior angle at `C`. -/
def AngleSumGtTwoRight (A B C : P) : Prop :=
  IsTriangle (Line := L) A B C ∧ ∃ X Y : P, ExteriorConfig L A B C X Y ∧
    (Y ∉ Interior (Line := L) X C B ∨ ∃ Z ∈ Interior (Line := L) C B A, AngCong Y C B Z B C)

end AngleSum

/-- Two lines meet symmetrically. -/
theorem meets_comm {P L : Type*} [HasLines P L] {a b : L} (h : Meets (Point := P) a b) :
    Meets (Point := P) b a := by
  obtain ⟨X, ha, hb⟩ := h; exact ⟨X, hb, ha⟩

section Euclid

variable {P L : Type*} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [PlaneCongruence P L]

/-- In a plane satisfying groups I–IV the sum of the angles of every triangle is two right angles in
the sense of `AngleSumEqTwoRight`. -/
theorem angleSumEqTwoRight_of_parallels [PlaneParallels P L] {A B C : P}
    (h : IsTriangle (Line := L) A B C) (hAB : A ≠ B) : AngleSumEqTwoRight L A B C := by
  have hl := line_through_of_ne (L := L) hAB
  set F := planeFrame (P := P) (L := L) hl
  obtain ⟨-, hCB, hAC⟩ := ne_of_not_collinear (L := L) h (hl B)
  obtain ⟨X, hX⟩ := exists_beyond (Line := L) hAC
  set lAC := line (Line := L) A C hAC
  have hAl : A ∈ lAC := mem_line_left hAC
  have hCl : C ∈ lAC := mem_line_right hAC
  have hXl : X ∈ lAC := mem_right_of_between hX hAl hCl
  have hBl : B ∉ lAC := fun hB => h ⟨lAC, hAl, hB, hCl⟩
  have hXC : X ≠ C := (ne23_of_between hX).symm
  have hCAB : ¬Collinear C A B := fun hc => h hc.swap12.swap23
  obtain ⟨Y, -, hYB, hY⟩ := F.layoff Set.univ rfl C A B lAC C X B hCAB (fun _ _ => trivial) hCl
    hXl hXC trivial hBl
  have hYl : Y ∉ lAC := hYB.1
  have hXCY : ¬Collinear X C Y := fun hc => hYl (mem_of_collinear hc hXC hXl hCl)
  have hCY : C ≠ Y := fun e => hYl (e ▸ hCl)
  set lCY := line (Line := L) C Y hCY
  set lAB := line (Line := L) A B hAB
  -- the line `CY` is parallel to `AB` (corresponding angles)
  have hBAC : ¬Collinear B A C := fun hc => h hc.swap12
  have hYCX : ¬Collinear Y C X := fun hc => hXCY hc.swap13
  have hc1 : AngCong B A C Y C X :=
    angCong_swap_right (Line := L) hBAC hXCY (angCong_swap_left (Line := L) hCAB hXCY hY)
  have hpar : ¬Meets (Point := P) lAB lCY :=
    theorem19_converse_corresponding (a := lAB) (b := lCY) (mem_line_left hAB) (mem_line_left hCY)
      hAC (mem_line_right hAB) (mem_line_right hCY) (sameSide_symm' hYB) hX hc1
  set lCB := line (Line := L) C B hCB
  have hCl' : C ∈ lCB := mem_line_left _
  have hBl' : B ∈ lCB := mem_line_right _
  have hAl' : A ∉ lCB := fun hA => h ⟨lCB, hA, hBl', hCl'⟩
  have hXl' : X ∉ lCB := fun hX' => hAl' (mem_left_of_between hX hCl' hX')
  have hYl' : Y ∉ lCB := by
    intro hY'
    have : lCY = lCB := (eq_line hCY hCl' hY').symm
    exact hpar ⟨B, mem_line_right hAB, this ▸ hBl'⟩
  have hAX : OppositeSides lCB A X := ⟨hAl', hXl', C, hCl', hX⟩
  have hYA : OppositeSides lCB Y A := by
    rcases sameSide_or_opp' hYl' hAl' with hs | ho
    · exfalso
      have hACB : ¬Collinear A C B := fun hc => h hc.swap23
      have hint : Y ∈ Interior (Line := L) A C B := by
        refine (interior_iff (L := L) hAC hCB.symm).2 ⟨?_, hs⟩
        rw [line_comm hAC]
        exact hYB
      obtain ⟨Z, hZ, hZr⟩ := F.crossbar rfl trivial trivial trivial trivial hACB hint
      exact hpar ⟨Z, mem_mid_of_between hZ (mem_line_left hAB) (mem_line_right hAB),
        mem_of_collinear (collinear_of_mem_ray hZr) hCY (mem_line_left hCY) (mem_line_right hCY)⟩
    · exact ho
  have hYCB : ¬Collinear Y C B := fun hc => hYl' (mem_of_collinear hc.swap12.swap23 hCB hCl' hBl')
  have halt : AngCong Y C B A B C :=
    theorem19_alternate (a := lCY) (b := lAB) (meets_comm.mt hpar) (mem_line_left hCY)
      (mem_line_right hAB) hCB (mem_line_right hCY) (mem_line_left hAB) hYA
  have hABC' : ¬Collinear A B C := h
  refine ⟨h, X, Y, ⟨hX, hY, fun a hAa hCa => by rw [eq_line hAC hAa hCa]; exact hYB⟩, ?_,
    angCong_swap_right (Line := L) hYCB hABC' halt⟩
  refine (interior_iff (L := L) hXC hCB.symm).2 ⟨?_, ?_⟩
  · rw [← eq_line hXC.symm hCl hXl]; exact hYB
  · exact F.ss_of_opp_opp rfl (fun _ _ => trivial) trivial trivial trivial hYA hAX

end Euclid

/-- **Dehn's theorem on the angle sum** (the generalization of Legendre's theorem). -/
def AngleSumTheorem : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → ∀ A B C A' B' C' : P, IsTriangle (Line := L) A' B' C' →
      (AngleSumGtTwoRight L A B C → AngleSumGtTwoRight L A' B' C') ∧
      (AngleSumEqTwoRight L A B C → AngleSumEqTwoRight L A' B' C') ∧
      (AngleSumLtTwoRight L A B C → AngleSumLtTwoRight L A' B' C')

/-!
## [concl.legendre] Legendre's theorem

*(Conclusion)*

> The case where the sum of the angles is equal to two right angles gives the well known theorem of Legendre. However, in his demonstration, Legendre makes use of continuity.

**Lean reading.** The case "equal" of `AngleSumTheorem` (unit `concl.angle_sum`); Dehn's proof
avoids Archimedes's axiom, Legendre's uses it. Nothing beyond that unit to state.

**Status.** remark
-/

/-!
## [concl.non_legendrian] The non-legendrian geometry

*(Conclusion)*

> Upon the hypothesis that through a given point we may draw an infinity of lines parallel to a given straight line, it does not follow, when we exclude the axiom of Archimedes, that the sum of the angles of a triangle is less than two right angles, but on the contrary, this sum may be
>
> (*a*) greater than two right angles, or
>
> (*b*) equal to two right angles.
>
> In order to demonstrate part (*a*) of this theorem, Mr. Dehn constructs a geometry where we may draw through a point an infinity of lines parallel to a given straight line and where, moreover, all of the theorems of Riemann's (elliptic) geometry are valid. This geometry may be called non-legendrian, for it is in contradiction with that theorem of Legendre by virtue of which the sum of the angles a triangle is never greater than two right angles.

**Lean reading.** `InfinitelyManyParallels P L`: through every point outside a line pass infinitely
many lines not meeting it. Part (a) is `NonLegendrianGeometryExists`: some plane satisfying groups
I, II, IV (`PlaneCongruence`) has infinitely many parallels and every triangle of it has angle sum
greater than two right angles. "All the theorems of Riemann's geometry are valid" is not formalized
beyond the angle sum. Part (b) is `SemiEuclideanGeometryExists` (unit `concl.semi_euclidean`).

Part (a) is proved: `nonLegendrianGeometryExists` in `CommentaryClose.lean`, with Dehn's model, the
part of an elliptic plane infinitely near to a point, over a non-archimedean ordered field in which
the non-negative elements have square roots (the hyperreal numbers). In the gnomonic chart its
points are the pairs of infinitesimal numbers and its lines the straight lines of the coordinate
plane that meet this part, with the incidence and the order of that plane (`Elliptic.EPt`,
`Elliptic.ELn`, a `ConvexPart` of the plane; `CommentaryCloseAux.lean`, `CommentaryCloseAux4.lean`).
Segments are congruent when the cosines `Elliptic.cs` of their elliptic lengths agree, angles when
the cosines `Elliptic.kc` of their elliptic measures agree (`CommentaryCloseAux3.lean`). Groups I,
II, IV are `Elliptic.planeCongruence`, and the infinitely many parallels
`Elliptic.infinitelyManyParallels`: the lines in question meet the given line outside the
infinitesimal part (`CommentaryCloseAux5.lean`). The angle sum is `Elliptic.angleSumGt`
(`CommentaryCloseAux6.lean`): `∠A` is laid off at `C` on the prolongation of `AC`, which gives `Y`;
if `Y` is not interior to the exterior angle `∠XCB` the first alternative of `AngleSumGtTwoRight`
holds, and otherwise `∠YCB`, laid off at `B` on `BC`, falls inside `∠CBA`, by an identity whose
right side, the spherical excess, is positive (`Elliptic.excess_pos`).

**Status.** proved
-/

/-- Through every point outside a line pass infinitely many lines not meeting it. -/
def InfinitelyManyParallels (P L : Type*) [HasLines P L] : Prop :=
  ∀ (a : L) (A : P), A ∉ a → {b : L | A ∈ b ∧ ¬Meets b a}.Infinite

/-- **The non-legendrian geometry exists.** -/
def NonLegendrianGeometryExists : Prop :=
  ∃ (P L : Type) (_ : HasLines P L) (_ : HasBetween P) (_ : HasSegCong P) (_ : HasAngCong P),
    PlaneCongruence P L ∧ InfinitelyManyParallels P L ∧
      ∀ A B C : P, IsTriangle (Line := L) A B C → AngleSumGtTwoRight L A B C

/-!
## [concl.legendre_archimedes] Legendre's theorem needs the axiom of Archimedes

*(Conclusion)*

> From the existence of this non-legendrian geometry, it follows at once that it is impossible to demonstrate the theorem of Legendre just mentioned without employing the axiom of Archimedes, and in fact, Legendre made use of continuity in his demonstration of this theorem.

**Lean reading.** `LegendreNeedsArchimedes`: it is not true that in every plane satisfying groups I,
II, IV no triangle has angle sum greater than two right angles. "It follows at once" is proved:
`legendreNeedsArchimedes_of_nonLegendrian` (a non-legendrian geometry has a triangle, by I 7, and its
angle sum exceeds two right angles). The non-legendrian geometry exists
(`nonLegendrianGeometryExists` in `CommentaryClose.lean`, unit `concl.non_legendrian`: the part of
an elliptic plane over the hyperreal numbers infinitely near to a point), so the conclusion is
proved: `legendreNeedsArchimedes` in `CommentaryClose.lean`. The last clause ("Legendre made use of
continuity in his demonstration") presupposes that Legendre's theorem does hold once Archimedes's
axiom is added (the Saccheri–Legendre theorem): `LegendreTheorem`, in every plane satisfying groups
I, II, IV and V no triangle has angle sum greater than two right angles. It is a classical theorem
whose proof (doubling of angles, Archimedes's axiom for angles) needs the addition of angles that
the project does not develop; it is stated only, and `legendreNeedsArchimedes` does not use it. Its
consequence, used in the next unit ("as in the case of the non-legendrian geometry, it is clear
that … is a non-archimedean geometry"), is proved from it: `nonLegendrian_not_axiomV`, given
`LegendreTheorem`, a plane satisfying I, II, IV in which every triangle has angle sum greater than
two right angles does not satisfy Archimedes's axiom.

**Status.** proved
-/

/-- **Legendre's theorem cannot be proved without the axiom of Archimedes**: groups I, II, IV do not
imply that no triangle has an angle sum greater than two right angles. -/
def LegendreNeedsArchimedes : Prop :=
  ¬∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → ∀ A B C : P, ¬AngleSumGtTwoRight L A B C

theorem legendreNeedsArchimedes_of_nonLegendrian (h : NonLegendrianGeometryExists) :
    LegendreNeedsArchimedes := by
  obtain ⟨P, L, _, _, _, _, hc, -, hgt⟩ := h
  intro hall
  obtain ⟨A, B, C, hABC⟩ := exists_noncollinear (Point := P) (Line := L)
  exact hall P L hc A B C (hgt A B C hABC)

/-- **Legendre's theorem** (Saccheri–Legendre): with Archimedes's axiom, no triangle has an angle sum
greater than two right angles. A classical theorem, not proved here. -/
def LegendreTheorem : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → AxiomV P → ∀ A B C : P, ¬AngleSumGtTwoRight L A B C

/-- Given Legendre's theorem, the non-legendrian geometry is non-archimedean. -/
theorem nonLegendrian_not_axiomV (hL : LegendreTheorem) {P L : Type} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [hc : PlaneCongruence P L]
    (hgt : ∀ A B C : P, IsTriangle (Line := L) A B C → AngleSumGtTwoRight L A B C) :
    ¬AxiomV P := by
  intro hV
  obtain ⟨A, B, C, hABC⟩ := exists_noncollinear (Point := P) (Line := L)
  exact hL P L hc hV A B C (hgt A B C hABC)

/-!
## [concl.semi_euclidean] The semi-euclidean geometry

*(Conclusion)*

> For the demonstration of case (*b*), Mr. Dehn constructs a geometry where the axiom of parallels does not hold, but where, nevertheless, all of the theorems of the euclidean geometry are valid. Then, we have the sum of the angles of a triangle equal to two right angles. There exist also similar triangles, and the extremities of the perpendiculars having the same length and their bases upon a straight line all lie upon the same straight line, etc. The existence of this geometry shows that, if we disregard the axiom of Archimedes, the axiom of parallels cannot be replaced by any of the propositions which we usually regard as equivalent to it.
>
> This new geometry may be called a *semi-euclidean* *geometry.* As in the case of the non-legendrian geometry, it is clear that the semi-euclidean geometry is at the same time a non-archimedean geometry.

**Lean reading.** `SemiEuclideanGeometryExists`: some plane satisfying groups I, II, IV has
infinitely many parallels through every point outside a line (`InfinitelyManyParallels`), every
triangle of it has angle sum two right angles, it has similar triangles (`ExistSimilarTriangles`: two
triangles with their three angles congruent and not congruent) and the ends of equal perpendiculars
erected on the same side of a line are collinear (`EqualPerpendicularsCollinear`; a perpendicular
`FE` on `a` is a right angle `∠EFG` with `F`, `G` on `a`). "All of the theorems of the euclidean
geometry are valid" overstates as printed (Euclid's axiom itself fails, and with it every theorem
equivalent to it in the presence of Archimedes's axiom); it is read as the theorems Hilbert lists
("etc." is not formalized).

"The existence of this geometry shows that … the axiom of parallels cannot be replaced by any of the
propositions which we usually regard as equivalent to it" is `ParallelsNotReplaceable`: for each of
the three listed propositions, groups I, II, IV and that proposition do not imply Euclid's axiom
(`AxiomIII`). It follows from the existence of the geometry: `parallelsNotReplaceable_of_semiEuclidean`
(infinitely many parallels contradict the uniqueness in Euclid's axiom,
`not_axiomIII_of_infinitelyManyParallels`). "It is clear that the semi-euclidean geometry is a
non-archimedean geometry" would follow, for every such geometry, from the classical theorem that
with Archimedes's axiom an angle sum of two right angles in every triangle gives Euclid's axiom
(`ArchimedesAngleSumGivesParallels`, stated only, like `LegendreTheorem` in the previous unit; the
implication is `semiEuclidean_not_axiomV`). That theorem is not needed: the clause is proved
directly for the geometry constructed (`semiEuclidean_not_archimedean`, next paragraph).

The existence is proved in `CommentaryClose.lean`: `semiEuclideanGeometryExists`, and with it
`parallelsNotReplaceable`. The geometry is Dehn's model, the finite part of the euclidean plane over
the non-archimedean Pythagorean field `Ω(t)`: the points whose coordinates are bounded by natural
numbers, with the lines meeting that region (`FinitePart.finPart`, `CommentaryCloseAux2.lean`). It
is a case of the restriction of a plane to a convex part (`ConvexPart`, `CommentaryCloseAux.lean`),
in which groups I, II, IV hold when they hold in the plane and segments laid off from points of the
part stay in it (`ConvexPart.planeCongruence`, `FinitePart.finPart_layOffClosed`). Infinitely many
parallels (`FinitePart.finPart_infinitelyManyParallels`): the lines through a finite point whose
slopes differ infinitesimally (relative to its distance) from that of a given line meet it only at
infinite distance. The angle sum transfers from the plane, where it is
`angleSumEqTwoRight_of_parallels` (`FinitePart.finPart_angleSum`); the similar triangles are those
with vertices `(0,0), (1,0), (0,1)` and `(0,0), (2,0), (0,2)` (`FinitePart.finPart_similar`); the
perpendiculars are computed in coordinates (`FinitePart.finPart_equalPerp`). The geometry is
non-archimedean: `semiEuclidean_not_archimedean`, from `FinitePart.finPart_not_axiomV` (the
multiples of the segment from `(0,0)` to `(1/t,0)` never reach `(1,0)`); all the properties
together are `semiEuclideanGeometryExists_nonArchimedean`.

**Status.** proved
-/

section SemiEuclidean

variable (P L : Type*) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

/-- There are **similar triangles**: two triangles with congruent angles that are not congruent. -/
def ExistSimilarTriangles : Prop :=
  ∃ A B C A' B' C' : P, IsTriangle (Line := L) A B C ∧ IsTriangle (Line := L) A' B' C' ∧
    AngCong B A C B' A' C' ∧ AngCong A B C A' B' C' ∧ AngCong A C B A' C' B' ∧ ¬SegCong A B A' B'

/-- **The ends of equal perpendiculars** erected on the same side of a line `a` (at `F₁`, `F₂`,
`F₃`) lie on one straight line. -/
def EqualPerpendicularsCollinear : Prop :=
  ∀ (a : L) (F₁ F₂ F₃ G₁ G₂ G₃ E₁ E₂ E₃ : P), F₁ ∈ a → F₂ ∈ a → F₃ ∈ a → G₁ ∈ a → G₂ ∈ a →
    G₃ ∈ a → IsRightAngle (L := L) E₁ F₁ G₁ → IsRightAngle (L := L) E₂ F₂ G₂ →
    IsRightAngle (L := L) E₃ F₃ G₃ → SameSide a E₁ E₂ → SameSide a E₁ E₃ →
    SegCong F₁ E₁ F₂ E₂ → SegCong F₁ E₁ F₃ E₃ → Collinear (Line := L) E₁ E₂ E₃

end SemiEuclidean

/-- **The semi-euclidean geometry exists.** -/
def SemiEuclideanGeometryExists : Prop :=
  ∃ (P L : Type) (_ : HasLines P L) (_ : HasBetween P) (_ : HasSegCong P) (_ : HasAngCong P),
    PlaneCongruence P L ∧ InfinitelyManyParallels P L ∧
      (∀ A B C : P, IsTriangle (Line := L) A B C → AngleSumEqTwoRight L A B C) ∧
      ExistSimilarTriangles P L ∧ EqualPerpendicularsCollinear P L

/-- **Without Archimedes's axiom, Euclid's axiom cannot be replaced** by the theorem on the angle
sum, by the existence of similar triangles, or by the collinearity of the ends of equal
perpendiculars: none of them, with groups I, II, IV, implies Euclid's axiom. -/
def ParallelsNotReplaceable : Prop :=
  (¬∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
      PlaneCongruence P L → (∀ A B C : P, IsTriangle (Line := L) A B C → AngleSumEqTwoRight L A B C) →
        AxiomIII P) ∧
  (¬∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
      PlaneCongruence P L → ExistSimilarTriangles P L → AxiomIII P) ∧
  (¬∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
      PlaneCongruence P L → EqualPerpendicularsCollinear P L → AxiomIII P)

/-- Infinitely many parallels contradict Euclid's axiom (in a plane with two distinct points). -/
theorem not_axiomIII_of_infinitelyManyParallels {P L : Type*} [HasLines P L] [PlaneConnection P L]
    {X Y : P} (hXY : X ≠ Y) (h : InfinitelyManyParallels P L) : ¬AxiomIII P := by
  intro h3
  obtain ⟨A, B, C, hABC⟩ := exists_noncollinear (Point := P) (Line := L)
  have hl := line_through_of_ne (L := L) hXY
  have hCB : C ≠ B := by
    rintro rfl
    obtain ⟨l, hCl⟩ := hl C
    by_cases hAC : A = C
    · subst hAC; exact hABC ⟨l, hCl, hCl, hCl⟩
    · exact hABC ⟨line (Line := L) A C hAC, mem_line_left _, mem_line_right _, mem_line_right _⟩
  have hA : A ∉ line (Line := L) B C hCB.symm := fun hA =>
    hABC ⟨_, hA, mem_line_left hCB.symm, mem_line_right hCB.symm⟩
  have hsub : {b : L | A ∈ b ∧ ¬Meets (Point := P) b (line (Line := L) B C hCB.symm)}.Subsingleton :=
    fun b hb c hc => (h3 _ A hA).unique hb hc
  exact h _ A hA hsub.finite

/-- The existence of the semi-euclidean geometry shows that Euclid's axiom cannot be replaced. -/
theorem parallelsNotReplaceable_of_semiEuclidean (h : SemiEuclideanGeometryExists) :
    ParallelsNotReplaceable := by
  obtain ⟨P, L, _, _, _, _, hc, hinf, hsum, hsim, hperp⟩ := h
  have hIII : ¬AxiomIII P := by
    obtain ⟨A, B, C, hABC⟩ := exists_noncollinear (Point := P) (Line := L)
    obtain ⟨-, X, Y, ⟨hX, -⟩, -⟩ := hsum A B C hABC
    exact not_axiomIII_of_infinitelyManyParallels (L := L) (ne12_of_between (Line := L) hX) hinf
  exact ⟨fun hall => hIII (hall P L hc hsum), fun hall => hIII (hall P L hc hsim),
    fun hall => hIII (hall P L hc hperp)⟩

/-- **With Archimedes's axiom, an angle sum of two right angles gives Euclid's axiom** (Legendre).
A classical theorem, not proved here. -/
def ArchimedesAngleSumGivesParallels : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → AxiomV P →
      (∀ A B C : P, IsTriangle (Line := L) A B C → A ≠ B → AngleSumEqTwoRight L A B C) → AxiomIII P

/-- Given that classical theorem, a semi-euclidean geometry is non-archimedean. -/
theorem semiEuclidean_not_axiomV (hA : ArchimedesAngleSumGivesParallels) {P L : Type}
    [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P] [hc : PlaneCongruence P L]
    (hinf : InfinitelyManyParallels P L)
    (hsum : ∀ A B C : P, IsTriangle (Line := L) A B C → AngleSumEqTwoRight L A B C) :
    ¬AxiomV P := by
  intro hV
  obtain ⟨A, B, C, hABC⟩ := exists_noncollinear (Point := P) (Line := L)
  obtain ⟨-, X, Y, ⟨hX, -⟩, -⟩ := hsum A B C hABC
  exact not_axiomIII_of_infinitelyManyParallels (L := L) (ne12_of_between (Line := L) hX) hinf
    (hA P L hc hV (fun A B C h _ => hsum A B C h))

/-!
## [concl.no_parallels] Without parallels the angle sum exceeds two right angles

*(Conclusion)*

> Upon the hypothesis that there exists no parallel, it follows that the sum of the angles of a triangle is greater than two right angles.
>
> This theorem shows that, with respect to the axiom of Archimedes, the two non-euclidean hypotheses concerning parallels act very differently.

**Lean reading.** `NoParallels P L`: every line through a point outside a line meets it.
`NoParallelsTheorem` is the claim read literally: in a plane satisfying groups I, II, IV
(`PlaneCongruence`) without parallels, every triangle has angle sum greater than two right angles.
With Hilbert's axioms the hypothesis is contradictory: in a plane satisfying I, II, IV two lines
making congruent alternate angles with a transversal do not meet (Euclid I 27, the converse of
Theorem 19, proved in Congruence.lean without III and V), so through every point outside a line
there is a parallel (`exists_parallel`) and `NoParallels` fails in every such plane with two distinct
points (`not_noParallels`). As formalized the literal statement is nevertheless false, for a
degenerate reason: the plane consisting of a single point and no line (`OnePt`, `NoLine`) satisfies
groups I, II, IV of Basic.lean (`onePt_planeCongruence`; the plane clause of I 7 asks only for three
non-collinear points, and with no line the point is "non-collinear" with itself), has no parallels
vacuously, and its "triangle" `A A A` has no exterior angle (`not_noParallelsTheorem`). The corrected
statement asks for a triangle with distinct vertices (`A ≠ B`, as in Theorem 20), and then holds,
vacuously: `noParallelsTheoremCorrected`. Dehn's theorem has real content only for his more general
axioms of order (`concl.dehn_order`), which admit the closed lines of elliptic geometry; Dehn's
version, with his axioms of order and congruence, is not formalized here.

**Status.** proved (corrected)
-/

/-- Every line through a point outside a line meets it (there are no parallels). -/
def NoParallels (P L : Type*) [HasLines P L] : Prop :=
  ∀ (a : L) (A : P), A ∉ a → ∀ b : L, A ∈ b → Meets b a

/-- **Dehn's theorem** as printed: without parallels, the angle sum exceeds two right angles. -/
def NoParallelsTheorem : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → NoParallels P L →
      ∀ A B C : P, IsTriangle (Line := L) A B C → AngleSumGtTwoRight L A B C

/-- **Dehn's theorem**, for triangles with distinct vertices. -/
def NoParallelsTheoremCorrected : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → NoParallels P L →
      ∀ A B C : P, IsTriangle (Line := L) A B C → A ≠ B → AngleSumGtTwoRight L A B C

section Neutral

variable {P L : Type*} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [PlaneCongruence P L]

/-- **Euclid I 27** in Hilbert's groups I, II, IV: through a point outside a line there is a line
not meeting it. -/
theorem exists_parallel (a : L) (A : P) (hA : A ∉ a) :
    ∃ b : L, A ∈ b ∧ ¬Meets (Point := P) b a := by
  obtain ⟨B, C, hBC, hB, hC⟩ := exists_two_points (Point := P) a
  have hAB : A ≠ B := fun e => hA (e ▸ hB)
  have hl := line_through_of_ne (L := L) hAB
  set F := planeFrame (P := P) (L := L) hl
  set l := line (Line := L) A B hAB
  have hAl : A ∈ l := mem_line_left hAB
  have hBl : B ∈ l := mem_line_right hAB
  have hCl : C ∉ l := fun hCl => hA (by
    have : l = a := line_unique hBC hBl hCl hB hC
    exact this ▸ hAl)
  obtain ⟨D, hD⟩ := exists_beyond (Line := L) hBC.symm
  have hDl : D ∉ l := fun hDl => hCl (mem_left_of_between hD hBl hDl)
  have hopp : OppositeSides l C D := ⟨hCl, hDl, B, hBl, hD⟩
  have hCBA : ¬Collinear C B A := fun hc => hCl (mem_of_collinear hc.swap13 hAB hAl hBl)
  obtain ⟨Q, -, hQD, hQ⟩ := F.layoff Set.univ rfl C B A l A B D hCBA (fun _ _ => trivial) hAl hBl
    hAB.symm trivial hDl
  have hQC : OppositeSides l Q C :=
    F.opp_of_ss_opp rfl (fun _ _ => trivial) trivial trivial trivial hQD (opp_symm' hopp)
  have hAQ : A ≠ Q := fun e => hQC.1 (e ▸ hAl)
  have hBAQ : ¬Collinear B A Q := fun hc => hQC.1 (mem_of_collinear hc.swap12 hAB hAl hBl)
  have h1 : AngCong B A Q C B A := angCong_symmetric (L := L) hCBA hBAQ hQ
  have h2 : AngCong Q A B C B A := angCong_swap_left (Line := L) hBAQ hCBA h1
  refine ⟨line (Line := L) A Q hAQ, mem_line_left hAQ, ?_⟩
  exact theorem19_converse_alternate (a := line (Line := L) A Q hAQ) (b := a) (mem_line_left hAQ)
    hB hAB (mem_line_right hAQ) hC hQC h2

/-- Under Hilbert's groups I, II, IV, in a plane with two distinct points, the hypothesis "there
exists no parallel" never holds. -/
theorem not_noParallels {X Y : P} (hXY : X ≠ Y) : ¬NoParallels P L := by
  intro h
  obtain ⟨A, B, C, hABC⟩ := exists_noncollinear (Point := P) (Line := L)
  have hl := line_through_of_ne (L := L) hXY
  obtain ⟨-, hCB, -⟩ := ne_of_not_collinear (L := L) hABC (hl B)
  have hA : A ∉ line (Line := L) B C hCB.symm := fun hA =>
    hABC ⟨_, hA, mem_line_left hCB.symm, mem_line_right hCB.symm⟩
  obtain ⟨b, hb, hba⟩ := exists_parallel (line (Line := L) B C hCB.symm) A hA
  exact hba (h _ A hA b hb)

end Neutral

/-- The degenerate plane: a single point. -/
inductive OnePt | pt

/-- The degenerate plane has no line. -/
inductive NoLine

instance : HasLines OnePt NoLine := ⟨fun _ l => nomatch l⟩
instance : HasBetween OnePt := ⟨fun _ _ _ => False⟩
instance : HasSegCong OnePt := ⟨fun _ _ _ _ => True⟩
instance : HasAngCong OnePt := ⟨fun _ _ _ _ _ _ => True⟩

theorem onePt_eq (A B : OnePt) : A = B := by cases A; cases B; rfl

theorem onePt_not_collinear (A B C : OnePt) : ¬Collinear A B C := fun ⟨l, _⟩ => nomatch l

/-- The single point satisfies groups I, II, IV of plane geometry as worded in Basic.lean. -/
theorem onePt_planeCongruence : PlaneCongruence OnePt NoLine where
  ax_I1 A B h := absurd (onePt_eq A B) h
  ax_I2 _ _ a := nomatch a
  ax_I7_line a := nomatch a
  ax_I7_noncollinear := ⟨.pt, .pt, .pt, onePt_not_collinear _ _ _⟩
  between_onLine _ _ _ h := h.elim
  ax_II1 _ _ _ _ h := h.elim
  ax_II2 _ _ a := nomatch a
  ax_II3 _ _ _ h := absurd h (onePt_not_collinear _ _ _)
  ax_II4 _ _ _ _ a := nomatch a
  ax_II5 _ _ _ a := nomatch a
  angCong_wd := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  ax_IV4_refl _ _ _ _ := trivial
  ax_IV5 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  ax_IV4 _ _ _ a := nomatch a
  segCong_swap _ _ _ _ _ := ⟨trivial, trivial⟩
  ax_IV1 A B _ _ h := absurd (onePt_eq A B) h
  ax_IV1_refl _ _ _ := trivial
  ax_IV2 := fun _ _ _ _ _ _ _ _ _ _ _ => trivial
  ax_IV3 := fun _ _ _ _ _ _ _ _ _ _ => trivial
  ax_IV6 := fun _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩

/-- **The literal statement fails** in the one-point plane. -/
theorem not_noParallelsTheorem : ¬NoParallelsTheorem := by
  intro h
  obtain ⟨-, X, Y, ⟨hb, -⟩, -⟩ :=
    h OnePt NoLine onePt_planeCongruence (fun a => nomatch a) .pt .pt .pt (onePt_not_collinear _ _ _)
  exact hb

/-- **The corrected statement holds** (vacuously: with Hilbert's axioms of order there are always
parallels). -/
theorem noParallelsTheoremCorrected : NoParallelsTheoremCorrected := by
  intro P L _ _ _ _ _ hno A B C _ hAB
  exact absurd hno (not_noParallels (L := L) hAB)

/-!
## [concl.table] Dehn's table

*(Conclusion)*

> We may combine the preceding results in the following table. … {\tiny $<2$ right}&{\tiny This case is}&{\tiny Euclidean}&{\tiny Semi-euclidean geometry}\\[-1ex] {\tiny angles}&{\tiny impossible}&{\tiny (parabolic) geometry} & \\ \hline {\tiny $= 2$ right}&{\tiny This case is}&{\tiny This case is}&{\tiny Geometry of Lobatschewski}\\[-1ex] …

**Lean reading.** A summary of `concl.non_legendrian`, `concl.semi_euclidean`, `concl.no_parallels`
and the classical geometries. As printed (translation and LaTeX source) the labels of the second and
third rows are interchanged: euclidean and semi-euclidean geometry have angle sum *equal* to two right
angles (`concl.semi_euclidean`), the geometry of Lobachevsky *less* than two right angles. The correct
table reads: "`> 2` right angles": Riemann's (elliptic) geometry | impossible | non-legendrian
geometry; "`= 2` right angles": impossible | euclidean geometry | semi-euclidean geometry; "`< 2` right
angles": impossible | impossible | geometry of Lobachevsky. What is proved here: with Hilbert's
axioms of order the whole first column is impossible, Riemann's geometry included (`not_noParallels`:
groups I, II, IV always give parallels; Riemann's geometry needs Dehn's axioms of order, unit
`concl.no_parallels`); in the middle column, every triangle of a plane satisfying groups I–IV has angle
sum two right angles (`angleSumEqTwoRight_of_parallels`, unit `concl.angle_sum`). The two
"impossible" entries of the middle column also need the exclusiveness of the three cases, which is
not proved here; in the third column the non-legendrian and the semi-euclidean geometry exist
(`nonLegendrianGeometryExists`, `semiEuclideanGeometryExists` in `CommentaryClose.lean`, units
`concl.non_legendrian`, `concl.semi_euclidean`), and the geometry of Lobachevsky is not constructed
in this file.

**Status.** remark
-/

/-!
## [concl.principle] Questions answered by limited means, or shown unanswerable

*(Conclusion)*

> However, as I have already remarked, the present work is rather a critical investigation of the principles of the euclidean geometry. In this investigation, we have taken as a guide the following fundamental principle; viz., to make the discussion of each question of such a character as to examine at the same time whether or not it is possible to answer this question by following out a previously determined method and by employing certain limited means. … our reason is satisfied only when we possess a complete solution of the problem or a rigorous demonstration of the theorem, or, indeed, when we see clearly the reason of the impossibility of the success and, consequently, the necessity of failure.

**Lean reading.** A methodological principle. In the project "answering a question by limited means"
is a derivation from a named set of axiom classes, and "the impossibility of success" a model of
those classes in which the statement fails; both occur, e.g. `axiomII4_of_others` and
`axiomII4_not_of_others_without_planes` (Order.lean), `omegaT_independence_V` (unit
`intro.independent`). No claim to prove.

**Status.** remark
-/

/-!
## [concl.impossibility] Impossibility proofs

*(Conclusion)*

> Thus, in the modern mathematics, the question of the impossibility of solution of certain problems plays an important role, and the attempts made to answer such questions have often been the occasion of discovering new and fruitful fields for research. We recall in this connection the demonstration by Abel of the impossibility of solving an equation of the fifth degree by means of radicals, as also the discovery of the impossibility of demonstrating the axiom of parallels, and, finally, the theorems of Hermite and Lindeman concerning the impossibility of constructing by algebraic means the numbers $e$ and $\pi$.

**Lean reading.** Historical examples, not claims of the book. The impossibility of demonstrating
the axiom of parallels from the other axioms is Hilbert's § 10 (Independence.lean). The theorems of
Abel and of Hermite and Lindemann are outside the subject of the book and are not formalized here
(Mathlib, at the version used, has the irrationality of `π`, `irrational_pi`, but not the
transcendence of `e` and `π`).

**Status.** remark
-/

/-!
## [concl.purity] Purity of method

*(Conclusion)*

> This fundamental principle, which we ought to bear in mind when we come to discuss the principles underlying the impossibility of demonstrations, is intimately connected with the condition for the “purity” of methods in demonstration, which in recent times has been considered of the highest importance by many mathematicians. … In fact, the preceding geometrical study attempts, in general, to explain what are the axioms, hypotheses, or means, necessary to the demonstration of a truth of elementary geometry, and it only remains now for us to judge from the point of view in which we place ourselves as to what are the methods of demonstration which we should prefer.

**Lean reading.** A methodological remark. Purity of method is reflected in the house rule that every
theorem assumes exactly the axiom classes Hilbert uses (or fewer, when the proof needs fewer).

**Status.** remark
-/

end Conclusion

namespace Appendix

open Complex Set

/-!
## [app.lie] Lie's axioms and the aim of the appendix

*(Appendix)*

> The investigations by Riemann and Helmholtz of the foundations of geometry led Lie to take up the problem of the *axiomatic* treatment of geometry as introductory to the study of groups. … In what follows, I have therefore attempted to set up for plane geometry a system of axioms, depending likewise upon the conception of a group, … which contains only those requirements which are simple and easily seen geometrically. In particular they do not require the differentiability of the functions defining displacement. The axioms of the system which I set up are a special division of Lie's, or, as I believe, are at once deducible from his.

**Lean reading.** Historical background and the aim of the appendix. Lie's axioms are not formalized,
so the last claim (Hilbert's axioms follow from Lie's) is not stated. That axioms I–III do not
require differentiability is visible in their formalization below: displacements are only required
to be continuous bijections preserving the sense of traversal (`IsDisplacement`).

**Status.** remark
-/

/-!
## [app.jordan_theorem] Jordan's curve theorem

*(Appendix)*

> My method of proof is entirely different from Lie's method. I make use particularly of Cantor's theory of assemblages of points and of the theorem of C. Jordan, according to which every closed continuous plane curve free from double points divides the plane into an inner and an outer region.

**Lean reading.** The number plane is `ℂ` (unit `app.jordan_curve`). A closed continuous curve free
from double points is `IsClosedJordanCurve γ`: `γ : ℝ → ℂ` continuous, of period `1`, and injective
on `[0, 1)` (a continuous injective image of a circle; the curve is `range γ`, compact by
`IsClosedJordanCurve.isCompact_range`). `JordanCurveTheorem`: the complement of the curve is the
union of a bounded and an unbounded connected component (the inner and the outer region), each
having the curve as its frontier. This is the Jordan curve theorem. It is proved in
`JordanCurveClose.lean`: `jordanCurveTheorem : JordanCurveTheorem`.

The proof of the Jordan curve theorem is not a proof of this project. It is that of the library
`JordanPick` (directory `JordanPick/`): four files of the repository
<https://github.com/rkirov/jordan_pick> by Rado Kirov, under the Apache License 2.0, copied without
change (see `JordanPick/README.md`). They prove the theorem by Maehara's method, from the Brouwer
fixed point theorem, for a continuous injective map of the unit circle of
`EuclideanSpace ℝ (Fin 2)`. What `JordanCurveClose.lean` contributes is the transport to the
statement of this unit. A curve of period `1` is a continuous injective map of that circle, through
the additive circle `AddCircle 1` (`IsClosedJordanCurve.exists_sphere_map`). The components of the
complement, their boundedness and their frontiers are carried along a linear isometry of `ℂ` onto
`EuclideanSpace ℝ (Fin 2)` (`jordanCurveTheorem_of_isometry`).

The rest of the appendix does not depend on the theorem: Jordan regions are defined as bounded
components (`IsJordanRegion`), and the only curves used are round circles, whose inner region is
computed directly (`connectedComponentIn_sphere_compl`).

**Status.** proved
-/

/-- A **closed Jordan curve**: `γ` continuous, of period `1`, injective on `[0, 1)`. -/
def IsClosedJordanCurve (γ : ℝ → ℂ) : Prop :=
  Continuous γ ∧ Function.Periodic γ 1 ∧ InjOn γ (Ico 0 1)

theorem IsClosedJordanCurve.isCompact_range {γ : ℝ → ℂ} (h : IsClosedJordanCurve γ) :
    IsCompact (range γ) :=
  h.2.1.compact_of_continuous one_ne_zero h.1

/-- **Jordan's theorem**: a closed Jordan curve divides the number plane into an inner (bounded) and
an outer (unbounded) region, each bounded by the curve. -/
def JordanCurveTheorem : Prop :=
  ∀ γ : ℝ → ℂ, IsClosedJordanCurve γ → ∃ z w : ℂ, z ∉ range γ ∧ w ∉ range γ ∧
    Bornology.IsBounded (connectedComponentIn (range γ)ᶜ z) ∧
    ¬Bornology.IsBounded (connectedComponentIn (range γ)ᶜ w) ∧
    (range γ)ᶜ = connectedComponentIn (range γ)ᶜ z ∪ connectedComponentIn (range γ)ᶜ w ∧
    frontier (connectedComponentIn (range γ)ᶜ z) = range γ ∧
    frontier (connectedComponentIn (range γ)ᶜ w) = range γ

/-!
## [app.unnecessary_parts] Parts of the system are unnecessary

*(Appendix)*

> To be sure, in the system set up by me, particular parts are unnecessary. However, I have turned aside from the further investigation of these conditions to the simple statement of the axioms, and above all because I wish to avoid a comparatively too complicated proof, and one which is not at once geometrically evident.

**Lean reading.** Hilbert does not say which parts are unnecessary, so there is nothing precise to
state. (One instance is the footnote to axiom III: the axiom for sufficiently small domains
suffices.)

**Status.** remark
-/

/-!
## [app.space] An analogous system for space

*(Appendix)*

> In what follows I shall consider only the axioms relating to the plane, although I suppose that an analogous system of axioms for space can be set up which will make possible the construction of the geometry of space in a similar manner.

**Lean reading.** A conjecture without a precise statement ("an analogous system"); not formalized.

**Status.** remark
-/

/-!
## [app.jordan_curve] The number plane, Jordan curves and Jordan regions

*(Appendix)*

> We establish the following convention, namely: We will understand by *number-plane* the ordinary plane having a rectangular system of co-ordinates $x, y$.
>
> A continuous curve lying in this number-plane and being free from double points and including its end points is called a *Jordan curve*. If the Jordan curve is closed, the interior of the region of the number-plane bounded by it is called a *Jordan region*.

**Lean reading.** The number plane is `ℂ`, the point with co-ordinates `x, y` being `x + y i` (the
complex structure is only a convenience for writing rotations). A Jordan curve is `IsJordanArc γ`:
`γ : ℝ → ℂ` continuous and injective on `[0, 1]` (the curve is `γ '' [0, 1]`, end points included).
A closed one is `IsClosedJordanCurve` (unit `app.jordan_theorem`). "The interior of the region
bounded by it" is `IsJordanRegion U`: `U` is a bounded connected component of the complement of a
closed Jordan curve (by Jordan's theorem there is exactly one; the definition does not depend on the
theorem). Jordan regions are open (`IsJordanRegion.isOpen`), and every open disc is one
(`isJordanRegion_ball`: the circle `circleCurve c r` is a closed Jordan curve with range the sphere,
and the open disc is the component of the centre in its complement).

**Status.** definition
-/

/-- A **Jordan curve**: `γ` continuous and injective on `[0, 1]`; the curve is `γ '' [0, 1]`. -/
def IsJordanArc (γ : ℝ → ℂ) : Prop := ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1)

/-- A **Jordan region**: a bounded connected component of the complement of a closed Jordan curve. -/
def IsJordanRegion (U : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, IsClosedJordanCurve γ ∧ ∃ z : ℂ, z ∉ range γ ∧
    U = connectedComponentIn (range γ)ᶜ z ∧ Bornology.IsBounded U

theorem IsJordanRegion.isOpen {U : Set ℂ} (h : IsJordanRegion U) : IsOpen U := by
  obtain ⟨γ, hγ, z, -, rfl, -⟩ := h
  exact hγ.isCompact_range.isClosed.isOpen_compl.connectedComponentIn

/-- The circle of centre `c` and radius `r`, traversed once in the positive sense. -/
noncomputable def circleCurve (c : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  c + r * exp (((2 * Real.pi * t : ℝ) : ℂ) * I)

theorem circleCurve_isClosedJordanCurve (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsClosedJordanCurve (circleCurve c r) := by
  refine ⟨by unfold circleCurve; fun_prop, ?_, ?_⟩
  · intro t
    unfold circleCurve
    congr 2
    rw [show (((2 * Real.pi * (t + 1) : ℝ) : ℂ) * I) =
      (((2 * Real.pi * t : ℝ) : ℂ) * I) + 2 * Real.pi * I by push_cast; ring, exp_add,
      exp_two_pi_mul_I, mul_one]
  · intro s hs t ht hst
    unfold circleCurve at hst
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have he := mul_left_cancel₀ hr' (add_left_cancel hst)
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 he
    have h2 : ((s : ℂ) - t - n) * (2 * Real.pi * I) = 0 := by push_cast at hn; linear_combination hn
    have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    have h3 : ((s - t - n : ℝ) : ℂ) = 0 := by push_cast; exact (mul_eq_zero.1 h2).resolve_right hpi
    have h4 : s - t = n := by have := ofReal_eq_zero.1 h3; linarith
    have h5 : (n : ℝ) < 1 := by rw [← h4]; linarith [hs.2, ht.1]
    have h6 : (-1 : ℝ) < n := by rw [← h4]; linarith [hs.1, ht.2]
    have : n = 0 := by
      have a : n < 1 := by exact_mod_cast h5
      have b : -1 < n := by exact_mod_cast h6
      omega
    subst this
    simp at h4; linarith

theorem range_circleCurve (c : ℂ) {r : ℝ} (hr : 0 < r) :
    range (circleCurve c r) = Metric.sphere c r := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simp only [circleCurve, mem_sphere_iff_norm, add_sub_cancel_left, norm_mul,
      norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  · intro hz
    rw [mem_sphere_iff_norm] at hz
    refine ⟨arg (z - c) / (2 * Real.pi), ?_⟩
    unfold circleCurve
    have : (2 * Real.pi * (arg (z - c) / (2 * Real.pi)) : ℝ) = arg (z - c) := by
      field_simp
    rw [this, ← hz, norm_mul_exp_arg_mul_I]
    ring

theorem connectedComponentIn_sphere_compl (c : ℂ) {r : ℝ} (hr : 0 < r) :
    connectedComponentIn (Metric.sphere c r)ᶜ c = Metric.ball c r := by
  have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  apply Subset.antisymm
  · have hsub : connectedComponentIn (Metric.sphere c r)ᶜ c ⊆
        Metric.ball c r ∪ (Metric.closedBall c r)ᶜ := by
      intro x hx
      have := connectedComponentIn_subset _ _ hx
      simp only [mem_compl_iff, Metric.mem_sphere, Metric.mem_ball, Metric.mem_closedBall,
        not_le, mem_union] at this ⊢
      exact lt_or_gt_of_ne this
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union Metric.isOpen_ball
      Metric.isClosed_closedBall.isOpen_compl ?_ hsub
      ⟨c, mem_connectedComponentIn (by simp [hr.ne]), hc⟩
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx' (Metric.ball_subset_closedBall hx)
  · refine (convex_ball c r).isPreconnected.subset_connectedComponentIn hc ?_
    intro x hx hx'
    rw [Metric.mem_ball] at hx; rw [Metric.mem_sphere] at hx'; linarith

/-- An open disc is a Jordan region. -/
theorem isJordanRegion_ball (c : ℂ) {r : ℝ} (hr : 0 < r) : IsJordanRegion (Metric.ball c r) :=
  ⟨circleCurve c r, circleCurve_isClosedJordanCurve c hr, c, by
    rw [range_circleCurve c hr]; simp [hr.ne], by
    rw [range_circleCurve c hr, connectedComponentIn_sphere_compl c hr], Metric.isBounded_ball⟩

/-!
## [app.plane] Definition of the plane

*(Appendix)*

> For the sake of easier representation and comprehension, I shall in the following investigation formulate the definition of the plane in a more restricted sense than my method of proof requires, … Definitions of the Plane. The plane is a system of points which can be mapped in a reversible, single-valued manner upon the points lying in the finite region of the number-plane, or upon a certain partial system of the same. To each point $A$ of our geometry, there exists a Jordan curve in whose interior the map of $A$ lies and all of whose points likewise represent points of our geometry. This Jordan region is called the domain of the point $A$. Each Jordan region contained in a Jordan region which includes the point $A$ is likewise called a domain of $A$. If $B$ is any point in a domain of $A$, then this domain is at the same time called also a domain of $B$.
>
> If $A$ and $B$ are any two points of our geometry, then there always exists a domain which contains at the same time both of the points $A$ and $B$.

**Lean reading.** The points of the plane are identified with their maps (the map is reversible),
so a plane is a set `S` of points of the number plane `ℂ` ("the finite region of the number-plane" is
`ℂ` itself, as opposed to points at infinity; "a partial system" is a subset). `IsDomainOf S U z`: `U`
is a Jordan region containing `z`, all of whose points belong to `S` ("all of whose points" read as
the points of the region). Hilbert's two naming conventions would let a "domain of `A`" fail to
contain `A` (a Jordan region inside a domain of `A`); since domains serve as neighbourhoods ("an
arbitrarily small domain about the point `A`", axiom III), a domain of a point is required to contain
it. `IsPlane S`: every point of `S` has a domain, and for any two points of `S` some domain of the
first contains the second. `exists_domain_subset_inter`: two domains of a point contain a third one
(a small disc), used for the particular cases of axiom III.

**Status.** definition
-/

/-- `U` is a **domain of the point** (with map) `z` in the plane `S`. -/
def IsDomainOf (S : Set ℂ) (U : Set ℂ) (z : ℂ) : Prop := IsJordanRegion U ∧ z ∈ U ∧ U ⊆ S

/-- **Definition of the plane.** -/
def IsPlane (S : Set ℂ) : Prop :=
  (∀ z ∈ S, ∃ U, IsDomainOf S U z) ∧ ∀ z ∈ S, ∀ w ∈ S, ∃ U, IsDomainOf S U z ∧ w ∈ U

theorem exists_domain_subset_inter {S U V : Set ℂ} {z : ℂ} (hU : IsDomainOf S U z)
    (hV : IsDomainOf S V z) : ∃ W, IsDomainOf S W z ∧ W ⊆ U ∩ V := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 (hU.1.isOpen.inter hV.1.isOpen) z ⟨hU.2.1, hV.2.1⟩
  exact ⟨Metric.ball z r, ⟨isJordanRegion_ball z hr, Metric.mem_ball_self hr,
    hsub.trans (inter_subset_left.trans hU.2.2)⟩, hsub⟩

/-!
## [app.displacement] Definition of displacement and of rotation

*(Appendix)*

> We will define a *displacement* as a reversible, single-valued transformation of a plane into itself. Evidently we may distinguish two kinds of reversible, single-valued, continuous transformations of the number-plane into itself. … We shall assume in the present investigation that it is traversed in the same sense as the original Jordan curve, when we apply a transformation of the number-plane into itself, which defines a displacement. …
>
> Definition of Displacement. A displacement is a reversible, single-valued, continuous transformation of the maps of the given points upon the number-plane into themselves in such a manner that a closed Jordan curve is traversed in the same sense after the transformation as before. A displacement by which the point $M$ remains unchanged is called a *rotation* … about the point $M$.

**Lean reading.** The sense in which a closed curve is traversed is measured by winding numbers:
`WindsAround δ n` (for `δ t = γ t - p`, the curve seen from a point `p` off it) says that a continuous
determination `θ` of the argument (`δ t = |δ t| e^{iθ(t)}`) increases by `2πn` over one period.
`SensePreserving S f`: for every closed Jordan curve in `S`, every point `p ∈ S` off it and every `n`,
the curve winds `n` times about `p` iff its image winds `n` times about `f p` (about the points of its
inner region a closed Jordan curve winds `±1` times, the sign being the sense of traversal, and `0`
times about the points of its outer region, so this is "traversed in the same sense"; the definition
does not presuppose the Jordan theorem). `IsDisplacement S f`: `f` is a bijection of `S`
(`Equiv.Perm S`: "reversible, single-valued"), continuous for the topology of the number plane, and
sense-preserving. Read literally, the first sentence would make every such map a displacement; but
the axioms speak of a given system of displacements (the motions of the geometry), so a geometry
`Geometry` consists of a plane `S`, a set `D` of permutations of `S` (its displacements) and the
requirement that each of them is a displacement in the above sense. `IsRotationAbout G f M`: `f ∈ D`
and `f M = M`. The footnote about reversals (*Umklappung*) concerns an alternative Hilbert does not
take.

**Status.** definition
-/

/-- `δ` (a curve seen from a point off it) **winds `n` times** around `0`. -/
def WindsAround (δ : ℝ → ℂ) (n : ℤ) : Prop :=
  ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, δ t = (‖δ t‖ : ℂ) * exp ((θ t : ℂ) * I)) ∧
    θ 1 - θ 0 = 2 * Real.pi * n

/-- `f` **preserves the sense** of traversal of closed Jordan curves of the plane `S`. -/
def SensePreserving (S : Set ℂ) (f : S → S) : Prop :=
  ∀ γ : ℝ → S, IsClosedJordanCurve (fun t => (γ t : ℂ)) → ∀ p : S, p ∉ range γ → ∀ n : ℤ,
    (WindsAround (fun t => (γ t : ℂ) - p) n ↔ WindsAround (fun t => (f (γ t) : ℂ) - f p) n)

/-- **Definition of displacement.** -/
def IsDisplacement (S : Set ℂ) (f : Equiv.Perm S) : Prop := Continuous f ∧ SensePreserving S f

/-- A plane with a system of displacements. -/
structure Geometry where
  /-- The maps of the points on the number plane. -/
  S : Set ℂ
  isPlane : IsPlane S
  /-- The displacements. -/
  D : Set (Equiv.Perm S)
  isDisplacement : ∀ f ∈ D, IsDisplacement S f

/-- A **rotation about `M`**: a displacement leaving `M` unchanged. -/
def IsRotationAbout (G : Geometry) (f : Equiv.Perm G.S) (M : G.S) : Prop := f ∈ G.D ∧ f M = M

/-!
## [app.axiom1] Appendix, Axiom I

*(Appendix)*

> *If two displacements are followed out one after the other, then the resulting map of the plane upon itself is again a displacement.*

**Lean reading.** `AxiomI G`: if `f` and `g` are displacements of `G`, so is the composite `f.trans g`
(first `f`, then `g`). Literally this is only closure under composition. Hilbert's short form,
"Axiom I. The Displacements Form a Group", adds that the identity and the inverse of a displacement
are displacements: `AxiomIGroup G`. The main theorem is stated with the group reading (a set of
bijections closed under composition alone need not be a group). Both forms hold in the euclidean
plane (`euclideanPlane_axiomIGroup`, unit `app.main_theorem`).

**Status.** definition
-/

/-- **Axiom I** (literal). -/
def AxiomI (G : Geometry) : Prop := ∀ f ∈ G.D, ∀ g ∈ G.D, f.trans g ∈ G.D

/-- **Axiom I** (group reading). -/
def AxiomIGroup (G : Geometry) : Prop :=
  AxiomI G ∧ Equiv.refl G.S ∈ G.D ∧ ∀ f ∈ G.D, f.symm ∈ G.D

/-!
## [app.axiom2] Appendix, Axiom II

*(Appendix)*

> *If $A$ and $M$ are two arbitrary points distinct from each other, then by a rotation about $M$ we can always bring $A$ into an infinite number of different positions.*

**Lean reading.** `AxiomII G`: for `A ≠ M`, the set of the images of `A` under the rotations about
`M` (`IsRotationAbout`) is infinite. Hilbert's restatement in the next paragraph: the true circle
about `M` through `A` is `TrueCircle G M A`, the totality of the points arising from `A` by rotations
about `M`, and `axiomII_iff_trueCircle` is "Axiom II. Every true circle consists of an infinite
number of points."

**Status.** definition
-/

/-- **Axiom II.** -/
def AxiomII (G : Geometry) : Prop :=
  ∀ A M : G.S, A ≠ M → {X : G.S | ∃ f, IsRotationAbout G f M ∧ f A = X}.Infinite

/-- The **true circle** about `M` through `A`. -/
def TrueCircle (G : Geometry) (M A : G.S) : Set G.S := {X | ∃ f, IsRotationAbout G f M ∧ f A = X}

theorem axiomII_iff_trueCircle (G : Geometry) :
    AxiomII G ↔ ∀ A M : G.S, A ≠ M → (TrueCircle G M A).Infinite := Iff.rfl

/-!
## [app.near] Points, segments and triangles arbitrarily near

*(Appendix)*

> As preliminary to axiom III, we make the following explanations:
>
> Let $A$ be a definite point in our geometry and $A_1$, $A_2$, $A_3$, \ldots any infinite system of points. … If then there are triads of points $A_iB_iC_i$ such that $A_i$ falls in the domain $\alpha$, and likewise $B_i$ in the domain $\beta$ and $C_i$ in the domain $\gamma$, then we say that there are triangles $A_iB_iC_i$ lying arbitrarily near to the triangle $ABC$.

**Lean reading.** Nearness is only used in axiom III and its particular cases, in the phrase "there
are displacements such that triangles arbitrarily near `ABC` can be brought arbitrarily near
`A'B'C'`": `NearlyBrought G A B C A' B' C'` says that for all domains `α, β, γ` of `A, B, C` and
`α', β', γ'` of `A', B', C'` there are a triad `A₁, B₁, C₁` with `A₁ ∈ α`, `B₁ ∈ β`, `C₁ ∈ γ` and a
displacement `f ∈ D` with `f A₁ ∈ α'`, `f B₁ ∈ β'`, `f C₁ ∈ γ'`. Hilbert's "infinite system of
triads" is the family of these triads, indexed by the choices of domains; the triads are arbitrary
(a "triangle" here is any triad of points). Points and segments arbitrarily near are the analogous
notions for one and two points, written out in the particular cases of III (`app.special_cases`).

**Status.** definition
-/

/-- **Triangles arbitrarily near `ABC` can be brought arbitrarily near `A'B'C'`.** -/
def NearlyBrought (G : Geometry) (A B C A' B' C' : G.S) : Prop :=
  ∀ α β γ α' β' γ' : Set ℂ, IsDomainOf G.S α A → IsDomainOf G.S β B → IsDomainOf G.S γ C →
    IsDomainOf G.S α' A' → IsDomainOf G.S β' B' → IsDomainOf G.S γ' C' →
    ∃ A₁ B₁ C₁ : G.S, ∃ f ∈ G.D, (A₁ : ℂ) ∈ α ∧ (B₁ : ℂ) ∈ β ∧ (C₁ : ℂ) ∈ γ ∧
      (f A₁ : ℂ) ∈ α' ∧ (f B₁ : ℂ) ∈ β' ∧ (f C₁ : ℂ) ∈ γ'

/-!
## [app.axiom3] Appendix, Axiom III

*(Appendix)*

> *If there are displacements of such a kind that triangles arbitrarily near the triangle $ABC$ can be brought arbitrarily near to the triangle $A'B'C'$, then there always exists a displacement by which the triangle $ABC$ goes over exactly into the triangle $A'B'C'$.* [Note: It is sufficient to assume that axiom III holds for sufficiently small domains as Lie has done. My method of proof may be so changed as to make use of only this narrower assumption.]

**Lean reading.** `AxiomIII G`: if `NearlyBrought G A B C A' B' C'` (unit `app.near`), then some
displacement `f ∈ D` has `f A = A'`, `f B = B'`, `f C = C'`. Hilbert's short form: "The displacements
form a closed system." The footnote concerns a weakening used in Hilbert's proof and is not
formalized.

**Status.** definition
-/

/-- **Axiom III.** -/
def AxiomIII (G : Geometry) : Prop :=
  ∀ A B C A' B' C' : G.S, NearlyBrought G A B C A' B' C' →
    ∃ f ∈ G.D, f A = A' ∧ f B = B' ∧ f C = C'

/-!
## [app.special_cases] Particular cases of axiom III

*(Appendix)*

> We call special attention to the following particular cases of axiom III.
>
> If there are rotations about a point $M$ of the kind that segments lying arbitrarily near the segment $AB$ can be brought arbitrarily near the segment $A'B'$, then there is always such a rotation about $M$ possible by which the segment $AB$ goes over exactly into the segment $A'B'$.
>
> If there are displacements of the kind that segments arbitrarily near the segment $AB$ can be brought arbitrarily near to the segment $A'B'$, then there is always a displacement possible by which the segment $AB$ goes over exactly into the segment $A'B'$.
>
> If there are rotations about the point $M$ of the kind that points arbitrarily near the point A can be brought arbitrarily near the point $A'$, then there is always such a rotation about $M$ possible by which $A$ goes over exactly into the point $A'$.

**Lean reading.** `SpecialCaseRotSeg`, `SpecialCaseSeg`, `SpecialCaseRotPt` are the three statements,
with nearness for segments and points defined as in `NearlyBrought` (domains of the end points). They
follow from axiom III: the first by applying III to the triads `M, A, B` and `M, A', B'` (the triads
`M, A₁, B₁` are near `M, A, B`, and a rotation about `M` keeps `M` in every domain of `M`), the third
by applying it to `M, A, M` and `M, A', M`, the second by applying it to `A, B, B` and `A', B', B'`,
choosing for the repeated point a domain inside the two given ones (`exists_domain_subset_inter`).

**Status.** proved
-/

/-- First special case of III: rotations about `M` and segments. -/
def SpecialCaseRotSeg (G : Geometry) : Prop :=
  ∀ M A B A' B' : G.S, (∀ α β α' β' : Set ℂ, IsDomainOf G.S α A → IsDomainOf G.S β B →
      IsDomainOf G.S α' A' → IsDomainOf G.S β' B' →
      ∃ A₁ B₁ : G.S, ∃ f, IsRotationAbout G f M ∧ (A₁ : ℂ) ∈ α ∧ (B₁ : ℂ) ∈ β ∧
        (f A₁ : ℂ) ∈ α' ∧ (f B₁ : ℂ) ∈ β') →
    ∃ f, IsRotationAbout G f M ∧ f A = A' ∧ f B = B'

/-- Second special case of III: displacements and segments. -/
def SpecialCaseSeg (G : Geometry) : Prop :=
  ∀ A B A' B' : G.S, (∀ α β α' β' : Set ℂ, IsDomainOf G.S α A → IsDomainOf G.S β B →
      IsDomainOf G.S α' A' → IsDomainOf G.S β' B' →
      ∃ A₁ B₁ : G.S, ∃ f ∈ G.D, (A₁ : ℂ) ∈ α ∧ (B₁ : ℂ) ∈ β ∧
        (f A₁ : ℂ) ∈ α' ∧ (f B₁ : ℂ) ∈ β') →
    ∃ f ∈ G.D, f A = A' ∧ f B = B'

/-- Third special case of III: rotations about `M` and points. -/
def SpecialCaseRotPt (G : Geometry) : Prop :=
  ∀ M A A' : G.S, (∀ α α' : Set ℂ, IsDomainOf G.S α A → IsDomainOf G.S α' A' →
      ∃ A₁ : G.S, ∃ f, IsRotationAbout G f M ∧ (A₁ : ℂ) ∈ α ∧ (f A₁ : ℂ) ∈ α') →
    ∃ f, IsRotationAbout G f M ∧ f A = A'

theorem specialCaseRotSeg_of_axiomIII {G : Geometry} (h : AxiomIII G) : SpecialCaseRotSeg G := by
  intro M A B A' B' hn
  obtain ⟨f, hf, h1, h2, h3⟩ := h M A B M A' B' (by
    intro μ α β μ' α' β' hμ hα hβ hμ' hα' hβ'
    obtain ⟨A₁, B₁, f, ⟨hfD, hfM⟩, h1, h2, h3, h4⟩ := hn α β α' β' hα hβ hα' hβ'
    exact ⟨M, A₁, B₁, f, hfD, hμ.2.1, h1, h2, by rw [hfM]; exact hμ'.2.1, h3, h4⟩)
  exact ⟨f, ⟨hf, h1⟩, h2, h3⟩

theorem specialCaseRotPt_of_axiomIII {G : Geometry} (h : AxiomIII G) : SpecialCaseRotPt G := by
  intro M A A' hn
  obtain ⟨f, hf, h1, h2, -⟩ := h M A M M A' M (by
    intro μ α ν μ' α' ν' hμ hα hν hμ' hα' hν'
    obtain ⟨A₁, f, ⟨hfD, hfM⟩, h1, h2⟩ := hn α α' hα hα'
    exact ⟨M, A₁, M, f, hfD, hμ.2.1, h1, hν.2.1, by rw [hfM]; exact hμ'.2.1, h2,
      by rw [hfM]; exact hν'.2.1⟩)
  exact ⟨f, ⟨hf, h1⟩, h2⟩

theorem specialCaseSeg_of_axiomIII {G : Geometry} (h : AxiomIII G) : SpecialCaseSeg G := by
  intro A B A' B' hn
  obtain ⟨f, hf, h1, h2, -⟩ := h A B B A' B' B' (by
    intro α β γ α' β' γ' hα hβ hγ hα' hβ' hγ'
    obtain ⟨δ, hδ, hδs⟩ := exists_domain_subset_inter hβ hγ
    obtain ⟨δ', hδ', hδs'⟩ := exists_domain_subset_inter hβ' hγ'
    obtain ⟨A₁, B₁, f, hfD, h1, h2, h3, h4⟩ := hn α δ α' δ' hα hδ hα' hδ'
    exact ⟨A₁, B₁, B₁, f, hfD, h1, (hδs h2).1, (hδs h2).2, h3, (hδs' h4).1, (hδs' h4).2⟩)
  exact ⟨f, hf, h1, h2⟩

/-!
## [app.main_theorem] Axioms I–III give the euclidean or the Bolyai–Lobachevskian plane

*(Appendix)*

> I now prove the following proposition:
>
> A geometry in which axioms I–III are fulfilled is either the euclidean or the bolyai-lobatchefskian geometry.

**Lean reading.** `IsEuclideanGeometry G`: a bijection `φ` of the points of `G` onto the number plane
carries the displacements of `G` exactly onto the proper motions `z ↦ a z + b`, `|a| = 1`.
`IsHyperbolicGeometry G`: a bijection onto the open unit disc carries them exactly onto the maps
`z ↦ c (z - a) / (1 - conj(a) z)`, `|c| = 1`, `|a| < 1` (the proper motions of Poincaré's model of
the Bolyai–Lobachevskian plane). "Is the geometry" is read as an isomorphism of the structures
(points and displacements); the continuity of `φ`, which Hilbert's proof also yields, is not required.
`AppendixMainTheorem`: every `Geometry` satisfying axiom I (in the group reading, `AxiomIGroup`), II
and III is euclidean or hyperbolic. Not proved here: Hilbert's proof (*Math. Ann.* 56, 1902) is a
long paper using the point-set topology of the plane, the Jordan curve theorem and the construction
of the true straight lines outlined in the following units; this is far beyond the present
development. The formal statement, which depends on the formalization of "sense of traversal" and
"domain", is false as it stands, for the empty plane, and has to be read for a plane with a point
(last paragraph). Partial results proved:

* the theorem is not vacuous, and axioms I–III are compatible: the euclidean plane is a geometry of
  this kind (`appendix_axioms_consistent`). `euclideanPlane`: `S = ℂ` (`isPlane_univ`), `D` the proper
  motions (`eucD`, constructed by `motion`); these are continuous and preserve winding numbers
  (`windsAround_mul_iff`), so they are displacements. Axiom I, also in the group reading
  (`euclideanPlane_axiomIGroup`); axiom II (`euclideanPlane_axiomII`: the rotations about `M` move `A`
  to the points `M + u_n (A - M)`, `u_n = (1 + n i)/(1 - n i)`, which are pairwise distinct);
  axiom III (`euclideanPlane_axiomIII`: the quantities `conj(B - A)(B - A)`, `conj(C - A)(C - A)`,
  `conj(B - A)(C - A)` are continuous and invariant under the motions, so, taking small discs as
  domains, they agree for `ABC` and `A'B'C'` (`invariant_eq_of_nearlyBrought`), and two triads with
  equal invariants differ by a proper motion (`exists_rot`));
* the euclidean plane is euclidean in the sense of the theorem (`euclideanPlane_isEuclidean`).

That Poincaré's disc with its proper motions satisfies axioms I–III is not proved here (the sense
preservation of these maps needs the homotopy invariance of winding numbers).

Partial results (`CommentaryCloseAux7.lean`): as stated, `AppendixMainTheorem` is false, for a
degenerate reason (`not_appendixMainTheorem`). The empty set of points is a plane in the sense of
`IsPlane` (`isPlane_empty`), and with the identity as only displacement (`emptyGeometry`) it
satisfies axioms I–III vacuously (`emptyGeometry_axioms`); it is neither euclidean nor hyperbolic,
there being no bijection of the empty set onto the number plane or onto the disc. The statement
Hilbert means adds that the plane has a point: `AppendixMainTheoremNonempty` (hypothesis
`G.S.Nonempty`). Four steps of its proof (units `app.two_fixed_points`, `app.transitive`,
`app.middle`, `app.rotation_group`) are shown to follow from it (`steps_of_main` in
`CommentaryClose.lean`). Still missing: `AppendixMainTheoremNonempty` itself, that is, the argument
of Hilbert's memoir. The Jordan curve theorem, which the memoir uses, is available
(`jordanCurveTheorem` in `JordanCurveClose.lean`, unit `app.jordan_theorem`). The argument of the
memoir itself, on the point sets of the plane formed by the true circles and the true straight
lines (outlined in the following units), is not formalized.

**Status.** stated (open here)
-/

/-- Winding is unchanged by a rotation of the number plane. -/
theorem windsAround_mul {δ : ℝ → ℂ} {n : ℤ} {a : ℂ} (ha : ‖a‖ = 1) (h : WindsAround δ n) :
    WindsAround (fun t => a * δ t) n := by
  obtain ⟨θ, hθ, hδ, hn⟩ := h
  refine ⟨fun t => θ t + arg a, hθ.add continuous_const, fun t => ?_, by simp only; linarith⟩
  have ha' : a = exp ((arg a : ℂ) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I a]
    rw [ha]; simp
  simp only [norm_mul, ha, one_mul]
  conv_lhs => rw [hδ t, ha']
  push_cast
  rw [add_mul, exp_add]; ring

theorem windsAround_mul_iff {δ : ℝ → ℂ} {n : ℤ} {a : ℂ} (ha : ‖a‖ = 1) :
    WindsAround (fun t => a * δ t) n ↔ WindsAround δ n := by
  refine ⟨fun h => ?_, windsAround_mul ha⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have := windsAround_mul (a := a⁻¹) (by rw [norm_inv, ha, inv_one]) h
  simpa [← mul_assoc, inv_mul_cancel₀ ha0] using this

/-- The proper motion `z ↦ a z + b` of the number plane (`a ≠ 0`). -/
noncomputable def motion (a b : ℂ) (ha : a ≠ 0) : Equiv.Perm (univ : Set ℂ) where
  toFun z := ⟨a * z + b, trivial⟩
  invFun z := ⟨a⁻¹ * (z - b), trivial⟩
  left_inv z := Subtype.ext (by simp only; field_simp; ring)
  right_inv z := Subtype.ext (by simp only; field_simp; ring)

@[simp] theorem motion_apply (a b : ℂ) (ha : a ≠ 0) (z : (univ : Set ℂ)) :
    (motion a b ha z : ℂ) = a * z + b := rfl

theorem ne_zero_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) : a ≠ 0 := by rintro rfl; simp at ha

theorem isPlane_univ : IsPlane (univ : Set ℂ) := by
  refine ⟨fun z _ => ⟨Metric.ball z 1, isJordanRegion_ball z one_pos, Metric.mem_ball_self one_pos,
    subset_univ _⟩, fun z _ w _ => ⟨Metric.ball z (dist w z + 1), ⟨isJordanRegion_ball z
      (by positivity), Metric.mem_ball_self (by positivity), subset_univ _⟩, ?_⟩⟩
  rw [Metric.mem_ball]; linarith

/-- The displacements of the euclidean plane. -/
def eucD : Set (Equiv.Perm (univ : Set ℂ)) :=
  {f | ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z, (f z : ℂ) = a * z + b}

theorem isDisplacement_of_mem_eucD {f : Equiv.Perm (univ : Set ℂ)} (hf : f ∈ eucD) :
    IsDisplacement univ f := by
  obtain ⟨a, b, ha, hf⟩ := hf
  refine ⟨continuous_induced_rng.2 ?_, ?_⟩
  · have : ((↑) ∘ f : ↥(univ : Set ℂ) → ℂ) = fun z : ↥(univ : Set ℂ) => a * (z : ℂ) + b := funext hf
    rw [this]; fun_prop
  · intro γ _ p _ n
    have : (fun t => (f (γ t) : ℂ) - f p) = fun t => a * ((γ t : ℂ) - p) := by
      funext t; rw [hf, hf]; ring
    rw [this, windsAround_mul_iff ha]

/-- **The euclidean plane**: the number plane with its proper motions. -/
noncomputable def euclideanPlane : Geometry where
  S := univ
  isPlane := isPlane_univ
  D := eucD
  isDisplacement _ hf := isDisplacement_of_mem_eucD hf

theorem euclideanPlane_axiomIGroup : AxiomIGroup euclideanPlane := by
  refine ⟨?_, ?_, ?_⟩
  · change ∀ f ∈ eucD, ∀ g ∈ eucD, f.trans g ∈ eucD
    rintro f ⟨a, b, ha, hf⟩ g ⟨c, d, hc, hg⟩
    exact ⟨c * a, c * b + d, by rw [norm_mul, ha, hc, one_mul], fun z => by
      simp only [Equiv.trans_apply]; rw [hg, hf]; ring⟩
  · change Equiv.refl _ ∈ eucD
    exact ⟨1, 0, by simp, fun z => by simp⟩
  · change ∀ f ∈ eucD, f.symm ∈ eucD
    rintro f ⟨a, b, ha, hf⟩
    have ha0 := ne_zero_of_norm_eq_one ha
    refine ⟨a⁻¹, -(a⁻¹ * b), by rw [norm_inv, ha, inv_one], fun z => ?_⟩
    have := hf (f.symm z)
    rw [Equiv.apply_symm_apply] at this
    rw [this]; field_simp; ring

theorem euclideanPlane_axiomI : AxiomI euclideanPlane := euclideanPlane_axiomIGroup.1

/-- The points `(1 + n i) / (1 - n i)` of the unit circle, pairwise distinct. -/
noncomputable def unitPt (n : ℕ) : ℂ := (1 + n * I) / (1 - n * I)

theorem one_sub_mul_I_ne_zero (n : ℕ) : (1 : ℂ) - n * I ≠ 0 := by
  intro h
  have := congrArg re h
  simp at this

theorem norm_unitPt (n : ℕ) : ‖unitPt n‖ = 1 := by
  unfold unitPt
  rw [norm_div, div_eq_one_iff_eq (by simpa using one_sub_mul_I_ne_zero n)]
  have : (1 : ℂ) - n * I = (starRingEnd ℂ) (1 + n * I) := by simp [sub_eq_add_neg]
  rw [this, Complex.norm_conj]

theorem unitPt_injective : Function.Injective unitPt := by
  intro m n h
  unfold unitPt at h
  rw [div_eq_div_iff (one_sub_mul_I_ne_zero m) (one_sub_mul_I_ne_zero n)] at h
  have := congrArg im h
  simp at this
  exact_mod_cast (by linarith : (m : ℝ) = n)

theorem euclideanPlane_axiomII : AxiomII euclideanPlane := by
  intro A M hAM
  change Set.Infinite {X : ↥(univ : Set ℂ) | ∃ f : Equiv.Perm ↥(univ : Set ℂ),
    (f ∈ eucD ∧ f M = M) ∧ f A = X}
  have hAM' : (A : ℂ) - M ≠ 0 := sub_ne_zero.2 (fun e => hAM (Subtype.ext e))
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (⟨M + unitPt n * (A - M), trivial⟩ : (univ : Set ℂ))) ?_ ?_
  · intro m n h
    have := congrArg Subtype.val h
    simp only [add_right_inj] at this
    exact unitPt_injective (mul_right_cancel₀ hAM' this)
  · intro n
    have h1 := norm_unitPt n
    refine ⟨motion (unitPt n) (M - unitPt n * M) (ne_zero_of_norm_eq_one h1),
      ⟨⟨unitPt n, M - unitPt n * M, h1, fun z => rfl⟩, Subtype.ext ?_⟩, Subtype.ext ?_⟩
    · show unitPt n * (M : ℂ) + (M - unitPt n * M) = M; ring
    · show unitPt n * (A : ℂ) + (M - unitPt n * M) = M + unitPt n * (A - M); ring

/-- The invariant `conj u * v` of a pair of vectors under the rotations. -/
theorem conj_mul_motion {a : ℂ} (ha : ‖a‖ = 1) (u v : ℂ) :
    starRingEnd ℂ (a * u) * (a * v) = starRingEnd ℂ u * v := by
  have : starRingEnd ℂ a * a = 1 := by rw [Complex.conj_mul', ha]; simp
  rw [map_mul]; linear_combination (starRingEnd ℂ u * v) * this

/-- A continuous invariant of triads takes the same value on `ABC` and `A'B'C'` when triangles near
`ABC` can be brought near `A'B'C'`. -/
theorem invariant_eq_of_nearlyBrought (g : ℂ × ℂ × ℂ → ℂ) (hg : Continuous g)
    (hinv : ∀ f ∈ euclideanPlane.D, ∀ x y z : euclideanPlane.S,
      g ((f x : ℂ), (f y : ℂ), (f z : ℂ)) = g ((x : ℂ), (y : ℂ), (z : ℂ)))
    {A B C A' B' C' : euclideanPlane.S} (h : NearlyBrought euclideanPlane A B C A' B' C') :
    g ((A : ℂ), (B : ℂ), (C : ℂ)) = g ((A' : ℂ), (B' : ℂ), (C' : ℂ)) := by
  by_contra hne
  set p : ℂ × ℂ × ℂ := ((A : ℂ), (B : ℂ), (C : ℂ))
  set p' : ℂ × ℂ × ℂ := ((A' : ℂ), (B' : ℂ), (C' : ℂ))
  have hε : 0 < dist (g p) (g p') / 2 := by have := dist_pos.2 hne; linarith
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuous_iff.1 hg p _ hε
  obtain ⟨δ', hδ', hδg'⟩ := Metric.continuous_iff.1 hg p' _ hε
  set r := min δ δ'
  have hr : 0 < r := lt_min hδ hδ'
  have dom : ∀ z : euclideanPlane.S, IsDomainOf euclideanPlane.S (Metric.ball (z : ℂ) r) z :=
    fun z => ⟨isJordanRegion_ball _ hr, Metric.mem_ball_self hr, fun _ _ => Set.mem_univ _⟩
  obtain ⟨A₁, B₁, C₁, f, hf, h1, h2, h3, h4, h5, h6⟩ :=
    h _ _ _ _ _ _ (dom A) (dom B) (dom C) (dom A') (dom B') (dom C')
  have hq : dist ((A₁ : ℂ), (B₁ : ℂ), (C₁ : ℂ)) p < δ := by
    simp only [Prod.dist_eq, p, max_lt_iff]
    rw [Metric.mem_ball] at h1 h2 h3
    exact ⟨h1.trans_le (min_le_left _ _), h2.trans_le (min_le_left _ _),
      h3.trans_le (min_le_left _ _)⟩
  have hq' : dist ((f A₁ : ℂ), (f B₁ : ℂ), (f C₁ : ℂ)) p' < δ' := by
    simp only [Prod.dist_eq, p', max_lt_iff]
    rw [Metric.mem_ball] at h4 h5 h6
    exact ⟨h4.trans_le (min_le_right _ _), h5.trans_le (min_le_right _ _),
      h6.trans_le (min_le_right _ _)⟩
  have e1 := hδg _ hq
  have e2 := hδg' _ hq'
  rw [hinv f hf] at e2
  have := dist_triangle_left (g p) (g p') (g ((A₁ : ℂ), (B₁ : ℂ), (C₁ : ℂ)))
  linarith

/-- Two pairs of vectors with the same invariants are related by a rotation. -/
theorem exists_rot {u v u' v' : ℂ} (h1 : starRingEnd ℂ u * u = starRingEnd ℂ u' * u')
    (h2 : starRingEnd ℂ v * v = starRingEnd ℂ v' * v')
    (h3 : starRingEnd ℂ u * v = starRingEnd ℂ u' * v') :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a * u = u' ∧ a * v = v' := by
  have hn : ∀ w w' : ℂ, starRingEnd ℂ w * w = starRingEnd ℂ w' * w' → ‖w‖ = ‖w'‖ := by
    intro w w' h
    rw [Complex.conj_mul', Complex.conj_mul'] at h
    have : ‖w‖ ^ 2 = ‖w'‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have nu := hn u u' h1
  have nv := hn v v' h2
  by_cases hu : u = 0
  · have hu' : u' = 0 := by rw [hu, norm_zero] at nu; exact norm_eq_zero.1 nu.symm
    by_cases hv : v = 0
    · have hv' : v' = 0 := by rw [hv, norm_zero] at nv; exact norm_eq_zero.1 nv.symm
      exact ⟨1, by simp, by simp [hu, hu'], by simp [hv, hv']⟩
    · refine ⟨v' / v, ?_, by simp [hu, hu'], div_mul_cancel₀ _ hv⟩
      rw [norm_div, ← nv, div_self (norm_ne_zero_iff.2 hv)]
  · refine ⟨u' / u, ?_, div_mul_cancel₀ _ hu, ?_⟩
    · rw [norm_div, ← nu, div_self (norm_ne_zero_iff.2 hu)]
    · have hcu : starRingEnd ℂ u ≠ 0 := by simpa using hu
      have key : starRingEnd ℂ u * (u' * v - u * v') = 0 := by
        linear_combination u' * h3 - v' * h1
      have := (mul_eq_zero.1 key).resolve_left hcu
      field_simp
      linear_combination this

theorem euclideanPlane_axiomIII : AxiomIII euclideanPlane := by
  intro A B C A' B' C' h
  have key : ∀ (i j : ℂ × ℂ × ℂ → ℂ), Continuous i → Continuous j →
      (∀ x : ℂ × ℂ × ℂ, ∀ a b : ℂ, i (a * x.1 + b, a * x.2.1 + b, a * x.2.2 + b) = a * i x ∧
        j (a * x.1 + b, a * x.2.1 + b, a * x.2.2 + b) = a * j x) →
      starRingEnd ℂ (i ((A : ℂ), (B : ℂ), (C : ℂ))) * j ((A : ℂ), (B : ℂ), (C : ℂ)) =
        starRingEnd ℂ (i ((A' : ℂ), (B' : ℂ), (C' : ℂ))) * j ((A' : ℂ), (B' : ℂ), (C' : ℂ)) := by
    intro i j hi hj hij
    refine invariant_eq_of_nearlyBrought (fun x => starRingEnd ℂ (i x) * j x)
      ((Complex.continuous_conj.comp hi).mul hj) ?_ h
    intro f hf x y z
    obtain ⟨a, b, ha, hf⟩ := hf
    rw [show (f x : ℂ) = a * x + b from hf x, show (f y : ℂ) = a * y + b from hf y,
      show (f z : ℂ) = a * z + b from hf z]
    rw [(hij ((x : ℂ), (y : ℂ), (z : ℂ)) a b).1, (hij ((x : ℂ), (y : ℂ), (z : ℂ)) a b).2,
      conj_mul_motion ha]
  have e1 := key (fun x => x.2.1 - x.1) (fun x => x.2.1 - x.1) (by fun_prop) (by fun_prop)
    (fun x a b => ⟨by ring, by ring⟩)
  have e2 := key (fun x => x.2.2 - x.1) (fun x => x.2.2 - x.1) (by fun_prop) (by fun_prop)
    (fun x a b => ⟨by ring, by ring⟩)
  have e3 := key (fun x => x.2.1 - x.1) (fun x => x.2.2 - x.1) (by fun_prop) (by fun_prop)
    (fun x a b => ⟨by ring, by ring⟩)
  obtain ⟨a, ha, hu, hv⟩ := exists_rot e1 e2 e3
  refine ⟨motion a (A' - a * A) (ne_zero_of_norm_eq_one ha),
    ⟨a, A' - a * A, ha, fun z => rfl⟩, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · show a * (A : ℂ) + (A' - a * A) = A'; ring
  · show a * (B : ℂ) + (A' - a * A) = B'; linear_combination hu
  · show a * (C : ℂ) + (A' - a * A) = C'; linear_combination hv

/-- **The axioms I–III of the appendix are compatible.** -/
theorem appendix_axioms_consistent : ∃ G : Geometry, AxiomIGroup G ∧ AxiomII G ∧ AxiomIII G :=
  ⟨euclideanPlane, euclideanPlane_axiomIGroup, euclideanPlane_axiomII, euclideanPlane_axiomIII⟩

/-- The geometry `G` **is the euclidean geometry**: some bijection of its points onto the number
plane carries its displacements exactly onto the proper motions `z ↦ a z + b`, `|a| = 1`. -/
def IsEuclideanGeometry (G : Geometry) : Prop :=
  ∃ φ : G.S ≃ ℂ, ∀ f : Equiv.Perm G.S,
    f ∈ G.D ↔ ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ X, φ (f X) = a * φ X + b

/-- The geometry `G` **is the Bolyai–Lobachevskian geometry**: some bijection of its points onto
the unit disc carries its displacements exactly onto the conformal automorphisms
`z ↦ c (z - a) / (1 - conj a z)`, `|c| = 1`, `|a| < 1` (Poincaré's model). -/
def IsHyperbolicGeometry (G : Geometry) : Prop :=
  ∃ φ : G.S ≃ Metric.ball (0 : ℂ) 1, ∀ f : Equiv.Perm G.S,
    f ∈ G.D ↔ ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧
      ∀ X, (φ (f X) : ℂ) = c * ((φ X : ℂ) - a) / (1 - starRingEnd ℂ a * φ X)

/-- **Hilbert's theorem** (appendix): a geometry satisfying axioms I–III is the euclidean or the
Bolyai–Lobachevskian geometry. Not proved here; as stated it fails for the empty plane
(`not_appendixMainTheorem` in `CommentaryCloseAux7.lean`), and the statement for a plane with a
point is `AppendixMainTheoremNonempty` there. -/
def AppendixMainTheorem : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G →
    IsEuclideanGeometry G ∨ IsHyperbolicGeometry G

theorem euclideanPlane_isEuclidean : IsEuclideanGeometry euclideanPlane :=
  ⟨Equiv.Set.univ ℂ, fun _ => Iff.rfl⟩

/-!
## [app.invariant_subgroup] An invariant sub-group gives the euclidean plane

*(Appendix)*

> If we wish to obtain only the euclidean geometry, it is necessary merely to make in connection with axiom I the additional statement that the groups of displacements shall possess an invariant sub-group. This additional statement takes the place of the axioms of parallels.

**Lean reading.** `HasInvariantSubgroup G`: the displacements contain a normal subgroup other than the
trivial one and the whole group ("invariant sub-group" in the sense of the time: a proper non-trivial
normal subgroup). `AppendixEuclideanTheorem`: a geometry satisfying axioms I–III whose displacements
have an invariant sub-group is euclidean. Not proved here (it rests on the main theorem and on the
simplicity of the group of proper hyperbolic motions). Partial result: the addition is compatible
with axioms I–III, since the euclidean plane satisfies it (the translations,
`euclideanPlane_hasInvariantSubgroup`).

**Status.** stated (open here)
-/

/-- The group of displacements **possesses an invariant sub-group**: a normal subgroup other than
the trivial one and the whole group. -/
def HasInvariantSubgroup (G : Geometry) : Prop :=
  ∃ N : Set (Equiv.Perm G.S), N ⊆ G.D ∧ Equiv.refl G.S ∈ N ∧
    (∀ f ∈ N, ∀ g ∈ N, f.trans g ∈ N) ∧ (∀ f ∈ N, f.symm ∈ N) ∧
    (∃ f ∈ N, f ≠ Equiv.refl G.S) ∧ (∃ g ∈ G.D, g ∉ N) ∧
    ∀ g ∈ G.D, ∀ f ∈ N, (g.symm.trans f).trans g ∈ N

/-- **Hilbert's claim**: with an invariant sub-group, axioms I–III give the euclidean geometry. -/
def AppendixEuclideanTheorem : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → HasInvariantSubgroup G →
    IsEuclideanGeometry G

/-- The translations form an invariant sub-group of the euclidean displacements. -/
theorem euclideanPlane_hasInvariantSubgroup : HasInvariantSubgroup euclideanPlane := by
  unfold HasInvariantSubgroup
  dsimp only [euclideanPlane]
  refine ⟨{f | ∃ b : ℂ, ∀ z, (f z : ℂ) = z + b}, ?_, ⟨0, fun z => by simp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro f ⟨b, hf⟩
    exact ⟨1, b, by simp, fun z => by rw [hf, one_mul]⟩
  · rintro f ⟨b, hf⟩ g ⟨c, hg⟩
    exact ⟨b + c, fun z => by simp only [Equiv.trans_apply]; rw [hg, hf]; ring⟩
  · rintro f ⟨b, hf⟩
    refine ⟨-b, fun z => ?_⟩
    have := hf (f.symm z)
    rw [Equiv.apply_symm_apply] at this
    rw [this]; ring
  · refine ⟨motion 1 1 one_ne_zero, ⟨1, fun z => by simp [motion_apply]⟩, fun h => ?_⟩
    have := congrArg (fun f : Equiv.Perm ↥(univ : Set ℂ) => (f ⟨0, trivial⟩ : ℂ)) h
    simp at this
  · refine ⟨motion (-1) 0 (by norm_num), ⟨-1, 0, by simp, fun z => rfl⟩, ?_⟩
    rintro ⟨b, hb⟩
    have h0 := hb ⟨0, trivial⟩
    have h1 := hb ⟨1, trivial⟩
    simp at h0 h1
    rw [← h0] at h1
    norm_num at h1
  · intro g hg f hf
    obtain ⟨a, b, ha, hg⟩ := hg
    obtain ⟨c, hf⟩ := hf
    refine ⟨a * c, fun z => ?_⟩
    simp only [Equiv.trans_apply]
    rw [hg, hf]
    have := hg (g.symm z)
    rw [Equiv.apply_symm_apply] at this
    rw [this]; ring

/-!
## [app.true_circle_jordan] The true circles are closed Jordan curves

*(Appendix)*

> In what follows, I will briefly outline the general idea of my method of proof. … It may be easily shown that the true circle $k$ is an assemblage of points which is closed and in itself dense. It constitutes, therefore, a perfect assemblage of points.
>
> The next objective point in our demonstration is to show that the true circle $k$ is a closed Jordan curve. … Moreover, the law holds that each true circle inside of $k$ is likewise a closed Jordan curve.

**Lean reading.** The configuration `kk` and the point `K` are not specified, so the intermediate
claims about `k` cannot be stated; the conclusion Hilbert reaches ("We now see that every true circle
is a Jordan curve", two paragraphs later) is `TrueCirclesAreJordan`: in a geometry satisfying axioms
I–III, every true circle is the range of a closed Jordan curve (which makes it compact and perfect).
Not proved here. Partial results: the first property Hilbert names, closedness, holds for every true
circle and follows from axiom III alone (`trueCircle_closed`: a point of the plane in the closure of a
true circle lies on it, by the third particular case of axiom III; closed is meant within the plane,
since points outside it are not points of the geometry); "in itself dense" is not proved. In the
euclidean plane the true circle about `M` through `A` is the round circle of radius `|A - M|`
(`euclideanPlane_trueCircle`).

**Status.** stated (open here)
-/

/-- **The true circles are closed Jordan curves** (a step of Hilbert's proof). -/
def TrueCirclesAreJordan : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → ∀ M A : G.S, A ≠ M →
    ∃ γ : ℝ → ℂ, IsClosedJordanCurve γ ∧ range γ = Subtype.val '' TrueCircle G M A

/-- **The true circle is closed** (in the plane): a point of the plane that is a limit of points of
the true circle lies on it (axiom III, through its third particular case). -/
theorem trueCircle_closed {G : Geometry} (h3 : AxiomIII G) {M A X : G.S}
    (hX : (X : ℂ) ∈ closure (Subtype.val '' TrueCircle G M A)) : X ∈ TrueCircle G M A := by
  obtain ⟨f, hf, hfA⟩ := specialCaseRotPt_of_axiomIII h3 M A X (by
    intro α α' hα hα'
    obtain ⟨_, hzo, Y, ⟨f, hf, rfl⟩, rfl⟩ := mem_closure_iff.1 hX α' hα'.1.isOpen hα'.2.1
    exact ⟨A, f, hf, hα.2.1, hzo⟩)
  exact ⟨f, hf, hfA⟩

theorem euclideanPlane_trueCircle (M A : euclideanPlane.S) (hAM : A ≠ M) :
    ∃ γ : ℝ → ℂ, IsClosedJordanCurve γ ∧ range γ = Subtype.val '' TrueCircle euclideanPlane M A := by
  have hr : 0 < dist (A : ℂ) M := dist_pos.2 (fun e => hAM (Subtype.ext e))
  refine ⟨circleCurve M (dist (A : ℂ) M), circleCurve_isClosedJordanCurve _ hr, ?_⟩
  rw [range_circleCurve _ hr]
  ext z
  constructor
  · intro hz
    rw [mem_sphere_iff_norm] at hz
    have hd : (A : ℂ) - M ≠ 0 := sub_ne_zero.2 (fun e => hAM (Subtype.ext e))
    set a := (z - M) / ((A : ℂ) - M)
    have ha : ‖a‖ = 1 := by
      rw [norm_div, hz, ← dist_eq_norm, div_self hr.ne']
    refine ⟨⟨z, trivial⟩, ⟨motion a (M - a * M) (ne_zero_of_norm_eq_one ha),
      ⟨⟨a, M - a * M, ha, fun _ => rfl⟩, Subtype.ext ?_⟩, Subtype.ext ?_⟩, rfl⟩
    · show a * (M : ℂ) + (M - a * M) = M; ring
    · show a * (A : ℂ) + (M - a * M) = z
      simp only [a]; field_simp; ring
  · rintro ⟨X, ⟨f, ⟨hfD, hfM⟩, rfl⟩, rfl⟩
    obtain ⟨a, b, ha, hf⟩ := hfD
    have hM : (M : ℂ) = a * M + b := (congrArg Subtype.val hfM).symm.trans (hf M)
    have hA : ((f A : euclideanPlane.S) : ℂ) = a * A + b := hf A
    rw [mem_sphere_iff_norm, hA, dist_eq_norm,
      show a * (A : ℂ) + b - M = a * ((A : ℂ) - M) by linear_combination -hM, norm_mul, ha, one_mul]

/-!
## [app.rotation_group] The rotations of a true circle form the group of the circle

*(Appendix)*

> We turn now to the investigation of the group of all the displacements which by the rotation of the plane about $M$ transforms a definite true circle $k$ into itself. This group possesses the following properties: (1) Every displacement which leaves one point of $k$ undisturbed, leaves all points of $k$ undisturbed. (2) There always exists a displacement which changes any given point of $k$ into any other given point of $k$. (3) The group of displacements is a continuous one. … We set up the following proposition: The group of all the displacements of the true circle into itself, which are rotations about M, is holoedric, isomorphic with the group of ordinary rotations of the ordinary circle into itself.

**Lean reading.** "Holoedric isomorphic" is "isomorphic" (as opposed to "merohedric", homomorphic).
`RotationsOfTrueCircle`: for a true circle `k` about `M`, some bijection `φ` of `k` onto the unit
circle conjugates the action of the rotations about `M` on `k` exactly onto the ordinary rotations
`w ↦ c w`, `|c| = 1`, of the unit circle: every rotation about `M` acts on `k` as some `c`, and every
`c` is so obtained. Since the ordinary rotations act faithfully, the group of the restrictions to `k`
is then isomorphic to the circle group. Not proved here. Partial results: every rotation about `M`
maps the true circle `k` into itself (`trueCircle_mapsTo`, axiom I), so the group of the quotation is
that of all rotations about `M`; property (2) holds in every geometry satisfying axiom I in the group
reading (`trueCircle_transitive`); property (1) follows from the proposition
(`fixes_trueCircle_of_rotationsOfTrueCircle`: the factor `c` of a rotation fixing a point of `k` is
`1`). Property (3), continuity of the group, is not formalized. In the euclidean plane the
proposition holds with `φ X = (X - M)/(A - M)` (`euclideanPlane_rotationsOfTrueCircle`).

Partial results (`CommentaryCloseAux7.lean`): the proposition holds in every geometry that is
euclidean in the sense of `IsEuclideanGeometry` (`rotationsOfTrueCircle_of_isEuclidean`) and in
every geometry that is hyperbolic in the sense of `IsHyperbolicGeometry` and whose displacements
form a group (`rotationsOfTrueCircle_of_isHyperbolic`: after the displacement carrying `M` into the
centre of the disc, the rotations about `M` are the maps `z ↦ c z`, `|c| = 1`). Hence
`RotationsOfTrueCircle` follows from the main theorem for a plane with a point
(`rotationsOfTrueCircle_of_main`, from `AppendixMainTheoremNonempty`, unit `app.main_theorem`).
Still missing: a proof from axioms I–III themselves, that is, that the true circle is a closed
Jordan curve (unit `app.true_circle_jordan`) and the determination of the continuous groups acting
transitively on it in which only the identity has a fixed point; `AppendixMainTheoremNonempty` is
open.

**Status.** stated (open here)
-/

/-- **The rotations about `M` act on a true circle as the ordinary rotations act on the ordinary
circle** (a step of Hilbert's proof). -/
def RotationsOfTrueCircle : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → ∀ M A : G.S, A ≠ M →
    ∃ φ : G.S → ℂ, BijOn φ (TrueCircle G M A) (Metric.sphere 0 1) ∧
      (∀ f, IsRotationAbout G f M → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ X ∈ TrueCircle G M A, φ (f X) = c * φ X) ∧
      ∀ c : ℂ, ‖c‖ = 1 → ∃ f, IsRotationAbout G f M ∧ ∀ X ∈ TrueCircle G M A, φ (f X) = c * φ X

/-- Every rotation about `M` maps the true circle about `M` through `A` into itself (axiom I). -/
theorem trueCircle_mapsTo {G : Geometry} (h1 : AxiomI G) {M A X : G.S} {f : Equiv.Perm G.S}
    (hf : IsRotationAbout G f M) (hX : X ∈ TrueCircle G M A) : f X ∈ TrueCircle G M A := by
  obtain ⟨g, ⟨hgD, hgM⟩, rfl⟩ := hX
  exact ⟨g.trans f, ⟨h1 g hgD f hf.1, by simp [Equiv.trans_apply, hgM, hf.2]⟩, rfl⟩

/-- Property (2): the rotations about `M` carry any point of a true circle about `M` into any other
(axiom I, group reading). -/
theorem trueCircle_transitive {G : Geometry} (h1 : AxiomIGroup G) {M A X Y : G.S}
    (hX : X ∈ TrueCircle G M A) (hY : Y ∈ TrueCircle G M A) :
    ∃ f, IsRotationAbout G f M ∧ f X = Y := by
  obtain ⟨f, ⟨hfD, hfM⟩, rfl⟩ := hX
  obtain ⟨g, ⟨hgD, hgM⟩, rfl⟩ := hY
  have hfM' : f.symm M = M := by rw [Equiv.symm_apply_eq]; exact hfM.symm
  exact ⟨f.symm.trans g, ⟨h1.1 _ (h1.2.2 f hfD) g hgD, by simp [hfM', hgM]⟩, by simp⟩

/-- Property (1) follows from the proposition on the group of a true circle: a rotation about `M`
fixing one point of the true circle fixes all of them. -/
theorem fixes_trueCircle_of_rotationsOfTrueCircle (h : RotationsOfTrueCircle) {G : Geometry}
    (h1 : AxiomIGroup G) (h2 : AxiomII G) (h3 : AxiomIII G) {M A : G.S} (hAM : A ≠ M)
    {f : Equiv.Perm G.S} (hf : IsRotationAbout G f M) {X : G.S} (hX : X ∈ TrueCircle G M A)
    (hfX : f X = X) : ∀ Y ∈ TrueCircle G M A, f Y = Y := by
  obtain ⟨φ, hφ, hrot, -⟩ := h G h1 h2 h3 M A hAM
  obtain ⟨c, -, hc⟩ := hrot f hf
  have hX1 : φ X ≠ 0 := by
    have := hφ.1 hX
    intro h0
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  have hc1 : c = 1 := by
    have e := hc X hX
    rw [hfX] at e
    have : (c - 1) * φ X = 0 := by linear_combination -e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hX1)
  intro Y hY
  apply hφ.2.1 (trueCircle_mapsTo h1.1 hf hY) hY
  rw [hc Y hY, hc1, one_mul]

theorem euclideanPlane_rotationsOfTrueCircle (M A : euclideanPlane.S) (hAM : A ≠ M) :
    ∃ φ : euclideanPlane.S → ℂ, BijOn φ (TrueCircle euclideanPlane M A) (Metric.sphere 0 1) ∧
      (∀ f, IsRotationAbout euclideanPlane f M →
        ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ X ∈ TrueCircle euclideanPlane M A, φ (f X) = c * φ X) ∧
      ∀ c : ℂ, ‖c‖ = 1 → ∃ f, IsRotationAbout euclideanPlane f M ∧
        ∀ X ∈ TrueCircle euclideanPlane M A, φ (f X) = c * φ X := by
  have hd : (A : ℂ) - M ≠ 0 := sub_ne_zero.2 (fun e => hAM (Subtype.ext e))
  -- the values of a rotation about `M`
  have hrot : ∀ f, IsRotationAbout euclideanPlane f M →
      ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ X : euclideanPlane.S, (f X : ℂ) - M = a * ((X : ℂ) - M) := by
    rintro f ⟨⟨a, b, ha, hf⟩, hfM⟩
    have hM : (M : ℂ) = a * M + b := (congrArg Subtype.val hfM).symm.trans (hf M)
    refine ⟨a, ha, fun X => ?_⟩
    have hX : ((f X : euclideanPlane.S) : ℂ) = a * X + b := hf X
    rw [hX]; linear_combination -hM
  have hrotc : ∀ c : ℂ, ‖c‖ = 1 → ∃ f, IsRotationAbout euclideanPlane f M ∧
      ∀ X : euclideanPlane.S, (f X : ℂ) = M + c * ((X : ℂ) - M) := by
    intro c hc
    refine ⟨motion c (M - c * M) (ne_zero_of_norm_eq_one hc),
      ⟨⟨c, M - c * M, hc, fun _ => rfl⟩, Subtype.ext ?_⟩, fun X => ?_⟩
    · show c * (M : ℂ) + (M - c * M) = M; ring
    · show c * (X : ℂ) + (M - c * M) = M + c * (X - M); ring
  refine ⟨fun X => ((X : ℂ) - M) / ((A : ℂ) - M), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro X ⟨f, hf, rfl⟩
    obtain ⟨a, ha, hfa⟩ := hrot f hf
    show (((f A : euclideanPlane.S) : ℂ) - M) / ((A : ℂ) - M) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, hfa, mul_div_assoc, div_self hd, mul_one, ha]
  · intro X _ Y _ h
    exact Subtype.ext (sub_left_injective ((div_left_inj₀ hd).1 h))
  · intro c hc
    rw [mem_sphere_zero_iff_norm] at hc
    obtain ⟨f, hf, hfv⟩ := hrotc c hc
    refine ⟨f A, ⟨f, hf, rfl⟩, ?_⟩
    simp only
    rw [hfv, add_sub_cancel_left, mul_div_assoc, div_self hd, mul_one]
  · intro f hf
    obtain ⟨a, ha, hfa⟩ := hrot f hf
    exact ⟨a, ha, fun X _ => by simp only; rw [hfa, mul_div_assoc]⟩
  · intro c hc
    obtain ⟨f, hf, hfv⟩ := hrotc c hc
    exact ⟨f, hf, fun X _ => by simp only; rw [hfv, add_sub_cancel_left, mul_div_assoc]⟩

/-!
## [app.two_fixed_points] A displacement with two fixed points is the identity

*(Appendix)*

> Moreover, we investigate the group of displacements of all the points of our plane by a rotation about $M$. The law holds that, aside from the identity, there is no rotation of the plane about $M$ which leaves every point of the true circle undisturbed. … Finally, the proposition easily follows that: If any two points remain fixed by a displacement of the plane, then all points remain fixed; that is to say, the displacement is the identity.

**Lean reading.** `TwoFixedPointsIdentity`: in a geometry satisfying axioms I–III, a displacement
fixing two distinct points is the identity. Not proved here. The first law of the quotation (aside
from the identity no rotation about `M` fixes every point of a true circle about `M`) follows from it:
`rotation_fixing_trueCircle_eq_refl` (such a rotation fixes `M` and the point `A` of the circle).
Partial result: the theorem is true in the euclidean plane (`euclideanPlane_twoFixedPoints`:
`a A + b = A`, `a B + b = B` force `a = 1`, `b = 0`).

Partial results (`CommentaryCloseAux7.lean`): the theorem holds in every geometry that is euclidean
or hyperbolic in the sense of `IsEuclideanGeometry`, `IsHyperbolicGeometry`
(`twoFixedPoints_of_isEuclidean`, `twoFixedPoints_of_isHyperbolic`: a motion `z ↦ a z + b`, or a
conformal automorphism `z ↦ c (z - a) / (1 - conj(a) z)` of the disc, with two fixed points is the
identity). Hence `TwoFixedPointsIdentity` follows from the main theorem for a plane with a point
(`twoFixedPointsIdentity_of_main`, from `AppendixMainTheoremNonempty`, unit `app.main_theorem`).
Still missing: a proof from axioms I–III themselves. The statement quantifies over every geometry
satisfying I–III, so the computations in the two models do not prove it, and
`AppendixMainTheoremNonempty` is open; in Hilbert's memoir it is a step of the proof, resting on the
true circles being closed Jordan curves (unit `app.true_circle_jordan`) and on the Jordan curve
theorem. The Jordan curve theorem is available (`jordanCurveTheorem` in `JordanCurveClose.lean`,
unit `app.jordan_theorem`). That the true circles are closed Jordan curves is not proved, and
Hilbert's derivation of this step from the two is not formalized.

**Status.** stated (open here)
-/

/-- **A displacement with two fixed points is the identity** (a step of Hilbert's proof). -/
def TwoFixedPointsIdentity : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → ∀ f ∈ G.D, ∀ A B : G.S, A ≠ B →
    f A = A → f B = B → f = Equiv.refl G.S

/-- The law "aside from the identity, no rotation about `M` leaves every point of a true circle
undisturbed" follows from the two-fixed-points theorem. -/
theorem rotation_fixing_trueCircle_eq_refl (h : TwoFixedPointsIdentity) {G : Geometry}
    (h1 : AxiomIGroup G) (h2 : AxiomII G) (h3 : AxiomIII G) {M A : G.S} (hAM : A ≠ M)
    {f : Equiv.Perm G.S} (hf : IsRotationAbout G f M) (hfix : ∀ X ∈ TrueCircle G M A, f X = X) :
    f = Equiv.refl G.S :=
  h G h1 h2 h3 f hf.1 A M hAM (hfix A ⟨Equiv.refl _, ⟨h1.2.1, rfl⟩, rfl⟩) hf.2

theorem euclideanPlane_twoFixedPoints (f : Equiv.Perm euclideanPlane.S) (hf : f ∈ euclideanPlane.D)
    (A B : euclideanPlane.S) (hAB : A ≠ B) (hA : f A = A) (hB : f B = B) :
    f = Equiv.refl _ := by
  obtain ⟨a, b, -, hf⟩ := hf
  have h1 : (A : ℂ) = a * A + b := (congrArg Subtype.val hA).symm.trans (hf A)
  have h2 : (B : ℂ) = a * B + b := (congrArg Subtype.val hB).symm.trans (hf B)
  have hd : (A : ℂ) - B ≠ 0 := sub_ne_zero.2 (fun e => hAB (Subtype.ext e))
  have ha : a = 1 := by
    have : (a - 1) * ((A : ℂ) - B) = 0 := by linear_combination h2 - h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)
  have hb : b = 0 := by rw [ha] at h1; linear_combination -h1
  ext z
  have h := hf z
  rw [ha, hb, one_mul, add_zero] at h
  exact h

/-!
## [app.transitive] The displacements are transitive

*(Appendix)*

> Each point of the plane may be indeed made to go over into any other point of the plane by means of a displacement.

**Lean reading.** `DisplacementsTransitive`: in a geometry satisfying axioms I–III, for any two
points some displacement carries the first into the second. Not proved here. Partial result: true in
the euclidean plane, by a translation (`euclideanPlane_transitive`).

Partial results (`CommentaryCloseAux7.lean`): the displacements are transitive in every geometry
that is euclidean in the sense of `IsEuclideanGeometry` (`transitive_of_isEuclidean`, by a
translation) and in every geometry that is hyperbolic in the sense of `IsHyperbolicGeometry` and
whose displacements form a group (`transitive_of_isHyperbolic`, by the maps
`z ↦ (z - a) / (1 - conj(a) z)`, `mobPerm`, which carry `a` into the centre of the disc). Hence
`DisplacementsTransitive` follows from the main theorem for a plane with a point
(`displacementsTransitive_of_main`, from `AppendixMainTheoremNonempty`, unit `app.main_theorem`).
Still missing: a proof from axioms I–III themselves; `AppendixMainTheoremNonempty` is open, and in
Hilbert's memoir the transitivity comes after the true circles are shown to be closed Jordan curves
(unit `app.true_circle_jordan`, open). That step uses the Jordan curve theorem, which is available
(`jordanCurveTheorem` in `JordanCurveClose.lean`, unit `app.jordan_theorem`), and an argument on
the point sets of the plane that is not formalized.

**Status.** stated (open here)
-/

/-- **Every point can be brought into every other point by a displacement.** -/
def DisplacementsTransitive : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → ∀ A B : G.S, ∃ f ∈ G.D, f A = B

theorem euclideanPlane_transitive (A B : euclideanPlane.S) : ∃ f ∈ euclideanPlane.D, f A = B :=
  ⟨motion 1 ((B : ℂ) - A) one_ne_zero, ⟨1, (B : ℂ) - A, by simp, fun _ => rfl⟩,
    Subtype.ext (by show 1 * (A : ℂ) + (B - A) = B; ring)⟩

/-!
## [app.middle] Semi-rotations and the middle of a segment

*(Appendix)*

> Our further important objective point is to define the idea of the true straight line in our geometry and deduce those properties of it which are necessary in the further development of geometry. First of all, the notions “semi-rotation” and “middle of a segment” are defined. A segment has at most one middle, and, when we know the middle of one segment, then every smaller segment possesses a middle.

**Lean reading.** The definitions are not given in the summary; read: a semi-rotation about `M` is a
rotation about `M` of order two (a half-turn), `IsSemiRotation`, and `M` is a middle of `AB` if a
semi-rotation about `M` carries `A` into `B`, `IsMiddle`. `AtMostOneMiddle`: in a geometry satisfying
axioms I–III a segment `AB` (`A ≠ B`) has at most one middle. The second claim needs a comparison of
segments ("smaller") that the summary does not define, and is not stated. Not proved here. Partial
result: in the euclidean plane the semi-rotations are the half-turns `z ↦ 2M - z`
(`euclideanPlane_semiRotation`), so the middle of `AB` is `(A + B)/2` (`euclideanPlane_middle`,
`euclideanPlane_atMostOneMiddle`).

Partial results (`CommentaryCloseAux7.lean`): `AtMostOneMiddle` follows from
`TwoFixedPointsIdentity` (`atMostOneMiddle_of_twoFixedPoints`: the composite of two semi-rotations
carrying `A` into `B` fixes `A` and `B`, so the two coincide, and a semi-rotation, not being the
identity, fixes only its centre), and hence from the main theorem for a plane with a point
(`atMostOneMiddle_of_main`, from `AppendixMainTheoremNonempty`, unit `app.main_theorem`). Still
missing: `TwoFixedPointsIdentity` (unit `app.two_fixed_points`), which is open.

**Status.** stated (open here)
-/

/-- A **semi-rotation about `M`**: a rotation about `M` of order two. -/
def IsSemiRotation (G : Geometry) (σ : Equiv.Perm G.S) (M : G.S) : Prop :=
  IsRotationAbout G σ M ∧ σ.trans σ = Equiv.refl G.S ∧ σ ≠ Equiv.refl G.S

/-- `M` is a **middle of the segment `AB`**: a semi-rotation about `M` carries `A` into `B`. -/
def IsMiddle (G : Geometry) (M A B : G.S) : Prop := ∃ σ, IsSemiRotation G σ M ∧ σ A = B

/-- **A segment has at most one middle** (a step of Hilbert's proof). -/
def AtMostOneMiddle : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → ∀ M M' A B : G.S, A ≠ B →
    IsMiddle G M A B → IsMiddle G M' A B → M = M'

/-- The semi-rotations of the euclidean plane are the half-turns `z ↦ 2M - z`. -/
theorem euclideanPlane_semiRotation {σ : Equiv.Perm euclideanPlane.S} {M : euclideanPlane.S}
    (h : IsSemiRotation euclideanPlane σ M) (z : euclideanPlane.S) :
    (σ z : ℂ) = 2 * (M : ℂ) - z := by
  obtain ⟨⟨⟨a, b, ha, hσ⟩, hσM⟩, hσσ, hne⟩ := h
  have hM : (M : ℂ) = a * M + b := (congrArg Subtype.val hσM).symm.trans (hσ M)
  have hsq : ∀ z : euclideanPlane.S, (z : ℂ) = a * (a * z + b) + b := by
    intro z
    have h1 := congrArg (fun f : Equiv.Perm euclideanPlane.S => ((f z : euclideanPlane.S) : ℂ)) hσσ
    simp only [Equiv.trans_apply, Equiv.refl_apply] at h1
    have e1 : ((σ (σ z) : euclideanPlane.S) : ℂ) = a * (σ z : ℂ) + b := hσ (σ z)
    have e2 : ((σ z : euclideanPlane.S) : ℂ) = a * z + b := hσ z
    linear_combination -h1 + e1 + a * e2
  have h0 := hsq ⟨0, trivial⟩
  have h1 := hsq ⟨1, trivial⟩
  simp only at h0 h1
  have ha2 : a * a = 1 := by linear_combination -h1 + h0
  have ha1 : a ≠ 1 := by
    rintro rfl
    have hb : b = 0 := by linear_combination -h0 / 2
    apply hne
    ext z
    have := hσ z
    rw [hb, one_mul, add_zero] at this
    exact this
  have ham : a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by linear_combination ha2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) ha1
    · linear_combination h
  have e : ((σ z : euclideanPlane.S) : ℂ) = a * z + b := hσ z
  rw [e, ham]
  rw [ham] at hM
  linear_combination -hM

theorem euclideanPlane_middle {M A B : euclideanPlane.S} (h : IsMiddle euclideanPlane M A B) :
    (M : ℂ) = ((A : ℂ) + B) / 2 := by
  obtain ⟨σ, hσ, hσA⟩ := h
  have e := euclideanPlane_semiRotation hσ A
  rw [hσA] at e
  linear_combination (-1 / 2 : ℂ) * e

theorem euclideanPlane_atMostOneMiddle {M M' A B : euclideanPlane.S}
    (h : IsMiddle euclideanPlane M A B) (h' : IsMiddle euclideanPlane M' A B) : M = M' :=
  Subtype.ext ((euclideanPlane_middle h).trans (euclideanPlane_middle h').symm)

/-!
## [app.true_line] The true straight line

*(Appendix)*

> In order to pass judgment as to the position of the middle of a segment, we need particular propositions concerning true circles which are mutually tangent, … From what has been said, the definition of the true straight line follows as a system of points which arise from two fundamental points, if we apply repeatedly a semi-rotation, take the middle point, and add to the assemblage the points of condensation of the system of points which arises. We can then prove that the true straight line is a continuous curve, possessing no double points and having with any other true straight line at most one point in common. … We see also that in our geometry the laws of congruence hold, by which however two triangles are proven to be congruent if they are traversed in the same sense.

**Lean reading.** The definition of the true straight line is given: `TrueLineGen G A B` holds for
the points generated from the two fundamental points `A`, `B` by semi-rotations about generated
points (applied to generated points) and by middles of pairs of generated points (`IsSemiRotation`,
`IsMiddle`, unit `app.middle`); `TrueLine G A B` adds their points of condensation (the points of the
plane in the closure, in the number plane, of the generated points). Hilbert's claims about it, for a
geometry satisfying axioms I–III: the true straight line is a continuous curve without double points
(`TrueLineIsCurve`: the range of a continuous injective map of `ℝ`), and two true straight lines
have at most one point in common (`TrueLinesMeetAtMostOnce`). Not proved here. The other steps of
the paragraph (mutually tangent true circles; the numbering of the generated points by dyadic
numbers and the convergence of the points numbered `1/2, 1/4, 1/8, …`; the true line cuts every
circle about one of its points; any two points can be joined by a true line, which with this
definition is only significant when the fundamental points form the small unit segment; the
congruence theorems for triangles traversed in the same sense) are sketched without statements
precise enough to be formalized separately (the "law concerning this correspondence" is not given);
their content is part of `AppendixMainTheorem`. Partial result: in the euclidean plane the true
straight line with fundamental points `A`, `B` lies on the ordinary straight line `AB`
(`euclideanPlane_trueLine_subset`, by induction over the generation and closedness of the line);
that it is the whole line (density of the dyadic numbers) is not proved here.

**Status.** stated (open here)
-/

/-- The points generated from two fundamental points `A`, `B` by semi-rotations (about generated
points) and middles (of generated points). -/
inductive TrueLineGen (G : Geometry) (A B : G.S) : G.S → Prop
  | left : TrueLineGen G A B A
  | right : TrueLineGen G A B B
  | semi {X Y : G.S} {σ : Equiv.Perm G.S} : TrueLineGen G A B X → TrueLineGen G A B Y →
      IsSemiRotation G σ X → TrueLineGen G A B (σ Y)
  | middle {X Y M : G.S} : TrueLineGen G A B X → TrueLineGen G A B Y → IsMiddle G M X Y →
      TrueLineGen G A B M

/-- The **true straight line** with the fundamental points `A`, `B`: the generated points and
their points of condensation in the plane. -/
def TrueLine (G : Geometry) (A B : G.S) : Set G.S :=
  {X | (X : ℂ) ∈ closure (Subtype.val '' {Y | TrueLineGen G A B Y})}

/-- **A true straight line is a continuous curve without double points.** -/
def TrueLineIsCurve : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → ∀ A B : G.S, A ≠ B →
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Injective γ ∧ range γ = Subtype.val '' TrueLine G A B

/-- **Two true straight lines have at most one point in common.** -/
def TrueLinesMeetAtMostOnce : Prop :=
  ∀ G : Geometry, AxiomIGroup G → AxiomII G → AxiomIII G → ∀ A B C D : G.S, A ≠ B → C ≠ D →
    TrueLine G A B ≠ TrueLine G C D → (TrueLine G A B ∩ TrueLine G C D).Subsingleton

/-- In the euclidean plane the true straight line with fundamental points `A`, `B` lies on the
ordinary straight line `AB`. -/
theorem euclideanPlane_trueLine_subset (A B : euclideanPlane.S) :
    Subtype.val '' TrueLine euclideanPlane A B ⊆
      {z : ℂ | ∃ r : ℝ, z = (A : ℂ) + r * ((B : ℂ) - A)} := by
  set S := {z : ℂ | ∃ r : ℝ, z = (A : ℂ) + r * ((B : ℂ) - A)}
  have hgen : ∀ X, TrueLineGen euclideanPlane A B X → (X : ℂ) ∈ S := by
    intro X hX
    induction hX with
    | left => exact ⟨0, by simp⟩
    | right => exact ⟨1, by simp⟩
    | @semi X Y σ _ _ hσ ihX ihY =>
      obtain ⟨r, hr⟩ := ihX
      obtain ⟨s, hs⟩ := ihY
      refine ⟨2 * r - s, ?_⟩
      rw [euclideanPlane_semiRotation hσ, hr, hs]; push_cast; ring
    | @middle X Y M _ _ hM ihX ihY =>
      obtain ⟨r, hr⟩ := ihX
      obtain ⟨s, hs⟩ := ihY
      refine ⟨(r + s) / 2, ?_⟩
      rw [euclideanPlane_middle hM, hr, hs]; push_cast; ring
  have hS : IsClosed S := by
    by_cases hAB : (B : ℂ) - A = 0
    · have : S = {(A : ℂ)} := by ext z; simp [S, hAB]
      rw [this]; exact isClosed_singleton
    · have : S = (fun z : ℂ => ((z - A) / ((B : ℂ) - A)).im) ⁻¹' {0} := by
        ext z
        simp only [S, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨r, rfl⟩
          rw [add_sub_cancel_left, mul_div_assoc, div_self hAB, mul_one, ofReal_im]
        · intro h
          refine ⟨((z - A) / ((B : ℂ) - A)).re, ?_⟩
          have hq : (((z - A) / ((B : ℂ) - A)).re : ℂ) = (z - A) / ((B : ℂ) - A) := by
            apply Complex.ext <;> simp [h]
          rw [hq]; field_simp; ring
      rw [this]
      exact isClosed_singleton.preimage (by fun_prop)
  rintro _ ⟨X, hX, rfl⟩
  exact closure_minimal (by rintro _ ⟨Y, hY, rfl⟩; exact hgen Y hY) hS hX

/-!
## [app.parallels_cases] The two cases: euclidean and Bolyai–Lobachevskian

*(Appendix)*

> With regard to the position of the systems of all the true straight lines with respect to one another, there are two cases to distinguish, according as the axiom of parallels holds, or through each point there exists two straight lines which separate the straight lines which cut the given straight line from those which do not cut it. In the first case we have the euclidean and in the second the bolyai-lobatschefskian geometry.

**Lean reading.** The last step of the proof; its conclusion is the dichotomy of
`AppendixMainTheorem` (unit `app.main_theorem`). Nothing further to state.

**Status.** remark
-/

end Appendix

end HilbertFoundations
