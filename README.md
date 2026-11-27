# Hilbert, *The Foundations of Geometry*, in Lean 4

David Hilbert's *The Foundations of Geometry*, in E. J. Townsend's authorized English translation (Open Court, Chicago, 1902; [Project Gutenberg #17384](https://www.gutenberg.org/ebooks/17384), public domain in the USA), formalized in Lean 4 and mathlib.

Townsend translated the first German edition (*Grundlagen der Geometrie*, 1899) together with the additions Hilbert made for the French edition. The axiom system formalized here is the one of this edition, which is not that of the later ones: II 4 is the four-point axiom, IV 6 concludes the congruence of both remaining angles, and the Axiom of Completeness is a remark of § 8, added for the French edition.

Every axiom, definition, theorem and claim of the book is a *unit*: the Introduction, the seven chapters (§§ 1–39), the Conclusion and the Appendix give 430 units. Each unit quotes the text, says how it is read in Lean, and is followed by the declarations that state and prove it. Where the text is false or imprecise as printed, the unit says what is wrong and the corrected statement is proved. Ten units are stated as `Prop`s and not proved; they are listed [below](#what-is-not-proved) with what is missing.

## Highlights

- **The axioms** ([`Basic.lean`](HilbertFoundations/Basic.lean)). Points, lines and planes are three types; lines and planes are primitive objects, not sets of points. Each axiom is a `Prop`-valued definition (`AxiomI1`, …, `AxiomIV6`, `AxiomV`, `PlaneComplete`, `SpaceComplete`), and the groups are classes (`PlaneOrder`, `PlaneParallels`, `PlaneCongruence`, `Archimedes`, …, `PlaneGeometry`, `SpaceGeometry`), so that a theorem assumes exactly the axioms Hilbert names for it.
- **Compatibility and independence (Chapter II).** The coordinate space over Hilbert's field `Ω` satisfies all five groups (`omega_spaceGeometry`, hence `axiomsConsistent`, in [`Analytic.lean`](HilbertFoundations/Analytic.lean)). In [`Independence.lean`](HilbertFoundations/Independence.lean): the geometry inside a sphere satisfies groups I, II, IV, V and not the second assertion of the axiom of parallels (`nonEuclidean_model`; it is built over `ℝ`, not over `Ω`, and the unit says why); the geometry of § 11 satisfies everything except IV 6 (`axiomIV6_independent`); the coordinate space over the non-archimedean field `Ω(t)` satisfies groups I–IV and not V (`omegaT_model`, `axiomV_independent`).
- **Axiom II 4 is redundant.** `axiomII4_of_others` in [`Order.lean`](HilbertFoundations/Order.lean) derives the four-point axiom from the other axioms of groups I and II of plane geometry (E. H. Moore, 1902).
- **Theorem 6**, the Jordan curve theorem for polygons: every simple polygon divides the plane into an interior and an exterior. Hilbert gives no proof. `polygonTheorem` in [`OrderPolygon.lean`](HilbertFoundations/OrderPolygon.lean) proves it from groups I and II alone (`PlaneOrder`), by counting crossings modulo 2; `theorem6_space` is the form for a plane of space.
- **Pascal's theorem and the algebra of segments (Chapter III).** `theorem21` in [`Pascal.lean`](HilbertFoundations/Pascal.lean) proves Pascal's theorem from I 1–2, II, III, IV, without Archimedes's axiom. [`Proportion.lean`](HilbertFoundations/Proportion.lean) has the calculus of segments, Theorems 22 and 23 and the equations of lines; co-ordinates of space are `spaceCoordinatesClaim` in [`CoordinatesClose.lean`](HilbertFoundations/CoordinatesClose.lean).
- **Plane areas (Chapter IV).** Theorems 24–31 in [`Areas.lean`](HilbertFoundations/Areas.lean), among them `theorem30` (two polygons are of equal content if and only if they have equal measures of area). `nonarch_triangles` gives, over a non-archimedean field of segments, two triangles of equal content that are not of equal area.
- **Desargues's theorem (Chapter V).** `theorem32` ([`Desargues.lean`](HilbertFoundations/Desargues.lean)) proves it in a plane geometry with I 1–2, II, III, IV, without Archimedes's axiom. `theorem33` and `theorem33_exists` ([`NonDesargues.lean`](HilbertFoundations/NonDesargues.lean)) give a plane satisfying I 1–2, II–III, IV 1–5, V in which it fails; the model is the Moulton plane of the translator's note, and the computations of Hilbert's own ellipse construction are verified separately. [`DesarguesAlgebra.lean`](HilbertFoundations/DesarguesAlgebra.lean) builds the algebra of segments from Desargues's theorem without congruence and proves `theorem35`: a plane geometry with I 1–2, II, III that has a line satisfies Desargues's theorem if and only if it is part of a geometry of space with I, II, III.
- **Non-pascalian geometry (Chapter VI),** in [`NonPascal.lean`](HilbertFoundations/NonPascal.lean). `theorem38`: an archimedean number system is commutative, by Hilbert's argument. `theorem39`: Hilbert's `Ω(s, t)` is `OmegaST`, a division ring of skew Laurent series with `t s = 2 s t`, ordered, non-archimedean and not commutative (`OmegaST.t_mul_s_ne`). The coordinate space over it, with the numbers acting on the right (`Coord OmegaSTᵐᵒᵖ 3`), satisfies I, II, III and has a plane in which Pascal's theorem fails (`theorem37`, `nonpascal_geometry`); `theorem36` is the positive statement with Archimedes's axiom.
- **Constructions (Chapter VII).** In [`Constructions.lean`](HilbertFoundations/Constructions.lean), `theorem40` shows, in the coordinate plane over an ordered Pythagorean field, that the constructions by the axioms can be carried out by straight-edge and transferer of segments, and `theorem41` that, when the frame `(0,0)`, `(1,0)`, `(0,1)` is among the given points, a point is so constructible if and only if its co-ordinates lie in the domain `Ω(R)`; `compass_not_rt` gives a compass construction that is not of this kind. Theorem 43 is `theorem43` in [`ConstructionsClose.lean`](HilbertFoundations/ConstructionsClose.lean), proved in the stronger form `theorem43_polynomial` (the denominator is `1`) and without Theorem 42; Hilbert's own derivation from Theorem 42 is formalized as the implication `theorem42_imp_theorem43`. The same file proves that the regular polygons constructible with the compass and the circles of Malfatti are constructible by straight-edge and transferer (`regularPolygonsClaim`, `malfattiClaim`).
- **Theorem 42 (Chapter VII):** every totally positive number of a number field is a sum of four squares of numbers of the field. `theorem42` in [`Theorem42Close.lean`](HilbertFoundations/Theorem42Close.lean) proves it from the Hasse–Minkowski theorem for quadratic forms over number fields. That theorem is not proved in this project: it is taken from the library [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (The Tau Ceti contributors, Apache License 2.0), which is a dependency of the package; none of its code is copied. This project contributes the application: the form `x₁² + x₂² + x₃² + x₄² − α x₅²`, its isotropy at the finite places (rank five) and at the real places (from total positivity), and the passage from a zero of the form to four squares (`four_squares_of_isotropic`).
- **Definite functions of two variables (§ 38):** a polynomial in two variables with real coefficients that takes no negative value is a quotient of two sums of squares of polynomials (Hilbert, 1893). `twoVariableClaim` in [`TwoVariablesClose.lean`](HilbertFoundations/TwoVariablesClose.lean) derives it from Artin's theorem of 1927, the solution of Hilbert's seventeenth problem. That theorem is not proved in this project: the proof is that of the repository <https://github.com/pd4st8hb95-hub/hilbert17-lean>, 18 files of which are in [`Hilbert17/`](Hilbert17/README.md), copied with the changes that the toolchain of this repository requires; they are not under the licence of this repository (see [License](#license)). This project contributes the passage from Artin's theorem for two variables to Hilbert's statement, and, without the copied files, the case of degree two in one of the variables (`twoVariableClaim_quadratic`).
- **Theorem 44 (§ 39):** a construction whose co-ordinates are computed by square roots can be carried out by straight-edge and transferer of segments if and only if all its radicands are nonnegative for every real value of the parameters and either sign of the square roots. Hilbert proves it for one parameter and leaves the general case open, as depending on the generalization of Theorem 43 to several variables. `theorem44` in [`Theorem44Close.lean`](HilbertFoundations/Theorem44Close.lean) proves it for any number of parameters, from Hilbert's reduction (`theorem44_of_theorem43For`) and Artin's theorem of 1927 for the subfields of `ℝ` generated by finitely many numbers (`theorem43For_closure`). Two steps of Artin's proof are not proved in this project: the separation of the non-sums of squares by orderings and the transfer of sign conditions between real closed fields are taken from the copied library [`Hilbert17/`](Hilbert17/README.md), and the real closure of an ordered field from the dependency Tau Ceti. This project contributes the passage from an ordering of a finitely generated field to an embedding into `ℝ` (the Artin–Lang step: a transcendence basis and a primitive element, a simple real zero of a polynomial obtained by the transfer, and its persistence at a point with algebraically independent co-ordinates), and, without these libraries, the case of one parameter and the case of algebraic co-ordinates (`theorem44_one_parameter`, `theorem44_algebraic`, in `ConstructionsClose.lean`).
- **The Axiom of Completeness.** `completenessGivesBolzano` and `completenessGivesReals` in [`CompletenessClose.lean`](HilbertFoundations/CompletenessClose.lean): a geometry of space with groups I–V and `SpaceComplete` has Bolzano's property, and the points of a segment correspond in order to the real numbers.
- **Dehn's geometries (Conclusion).** [`CommentaryClose.lean`](HilbertFoundations/CommentaryClose.lean) constructs the semi-euclidean geometry (the finite part of the plane over `Ω(t)`, `semiEuclideanGeometryExists`) and the non-legendrian geometry (the part of an elliptic plane over the hyperreal numbers infinitely near to a point, `nonLegendrianGeometryExists`), and deduces `legendreNeedsArchimedes`.
- **Jordan's curve theorem (Appendix).** Hilbert quotes "the theorem of C. Jordan" without proof; the unit `app.jordan_theorem` states it for the closed curves `γ : ℝ → ℂ` of period 1 without double points (`JordanCurveTheorem`). The proof of the Jordan curve theorem is not a proof of this project: it is the formalization of Maehara's proof, from the Brouwer fixed point theorem, in the repository [rkirov/jordan_pick](https://github.com/rkirov/jordan_pick) by Rado Kirov (Apache License 2.0), four files of which are copied without change into [`JordanPick/`](JordanPick/README.md). This project contributes the transport to the statement of the unit, `jordanCurveTheorem` in [`JordanCurveClose.lean`](HilbertFoundations/JordanCurveClose.lean).

## Status

Every unit is a block `## [id] Title` in one of the fourteen chapter files, with Hilbert's words, a **Lean reading** and a **Status**. The statuses are defined in [`Basic.lean`](HilbertFoundations/Basic.lean) ("Status vocabulary").

| Status | Units |
|---|---|
| proved: the statement, read as in the Lean reading, is formalized at full strength and proved | 191 |
| proved (reading): Hilbert's words admit more than one precise reading; the Lean reading says which one is formalized and why | 41 |
| proved (corrected): false or imprecise as printed; the corrected statement is proved, and the Lean reading says what is wrong | 22 |
| definition: a definition or an axiom | 106 |
| remark: prose without mathematical content to prove | 60 |
| stated (open here): formalized as a `Prop`; only the partial results named in the Lean reading are proved | 10 |
| **total** | **430** |

- No declaration uses `sorry`: an open unit is a definition of a `Prop`, never a theorem with an incomplete proof. `scripts/AxiomsAudit.lean` checks that every declaration of the namespace `HilbertFoundations` depends only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- The 430 units are the 68 statements that the text labels (the 21 axioms of groups I–V, counting the Axiom of Completeness, the 3 axioms of the Appendix and Theorems 1–44) and 362 unlabelled definitions, claims and remarks of the running text.
- Of Theorems 1–44, 32 are `proved`, 6 are `proved (reading)` (33, 35, 36, 38, 39, 40) and 6 are `proved (corrected)` (4, 14, 18, 21, 23, 41); none is open. Theorems 42 and 44 are among the 32. The proof of Theorem 42 rests on the Hasse–Minkowski theorem, which is not proved in this project but taken from the dependency Tau Ceti; that of Theorem 44 rests on the separation by orderings and the transfer of sign conditions of the copied library `Hilbert17` and on the real closure of Tau Ceti.
- The unit-by-unit map, with each unit's section, opening words, status and Lean declarations, is [docs/UNITS.md](docs/UNITS.md). It is generated by `scripts/unit_table.py`.
- The conventions, the readings and the corrections are discussed in [docs/FAITHFULNESS.md](docs/FAITHFULNESS.md); the edition and its copyright status are in [docs/SOURCES.md](docs/SOURCES.md).

**Some of the corrections** (each is a `proved (corrected)` unit):
- **Theorem 14** is false as printed: nothing relates the position of `h`, `k` with respect to `l` to that of `h'`, `k'` with respect to `l'` (`theorem14_as_printed_false`). `theorem14` adds the hypothesis of the later editions: `h`, `k` lie on the same side of `l` exactly when `h'`, `k'` lie on the same side of `l'`.
- **Theorem 18.** The uniqueness clause asks for four points not in a plane in the *extended* figure; a triangle and a point off its plane give two images (`theorem18_as_printed_false`). `theorem18` in `CongruenceClose.lean` proves the theorem with the condition on the *given* figure, in every geometry of space with groups I, II, IV that has a plane.
- **Theorem 21 (Pascal).** Read literally, without `A ≠ B`, the theorem is false in the real plane (`pascal_literal_false`); `theorem21` has the hypothesis `A ≠ B`.
- **The converse of Theorem 32** (§ 22) fails when two of the joining lines coincide (`theorem32_converse_literal_false`); `theorem32_converse` assumes them distinct. Likewise the converse half of **Theorem 23** concludes "parallel or equal" (`theorem23_converse`).
- **Theorem 41.** Without the unit of length among the given points the "if" half is false (`theorem41_needs_frame`); `theorem41` assumes the frame `(0,0)`, `(1,0)`, `(0,1)` given.
- **§ 21.** The triangle with base `g` and altitude `1` has the measure `g/2`, not `g` (`polygon_triangle_as_printed_false`); `polygon_triangle` takes the altitude `2`.
- **§ 12.** A function of `Ω(t)` can vanish at infinitely many values of `t` (`OmegaT.exists_isGen_infinite_zeros`); the conclusion Hilbert needs is `OmegaT.sign_eventually`.
- **§ 33.** `Ω(s, t)` as defined is not enumerable (`omegaST_not_countable`); the sub-system generated by `s` and `t` is (`omegaST₀_countable`).
- **§ 27.** "The commutative law … of multiplication" should be the associative law, as in the German text (`seg_laws_25_26`); not every linear equation can be brought into the form `ex + ny + nec = 0` (`normal_form_counterexample`).
- **Introduction and § 10.** The axioms of this edition are not independent: II 4 follows from the others (`not_axiomII4Independent`), and so does the second conclusion of IV 6 (`axiomIV6_of_first`). What Chapter II proves is the independence of the second assertion of III, of IV 6 and of V.

The other units with this status are `th.4`, `s9.sqrt`, `s23.conventions_valid`, `s23.fig40_hilbert`, `s27.origin_line`, `s36.fig52`, `s37.domain`, `concl.dehn_order` and `concl.no_parallels`.

**Readings.** A `proved (reading)` unit names the choice it makes. Examples: the non-euclidean geometry of § 10 is built over `ℝ`; the model of Theorem 33 is the Moulton plane; Theorem 40 is proved for the coordinate planes over ordered Pythagorean fields, not for an abstract plane satisfying I–V; Theorem 38 needs the asymmetry of the order that law 13 leaves tacit (`quatTotal_laws` shows it cannot be dropped); in Theorem 36, "equal" segments in Archimedes's axiom are translates of each other, as in § 24; the claim of § 35 is proved in its semantic form (`identity_for_segments`), not as a statement about proofs.

## What is not proved

Ten units have the status `stated (open here)`: two in the Conclusion and eight in the Appendix. Each is a `Prop` with its partial results proved; the unit block says precisely what is missing.

**Dehn's theorems in the Conclusion** (two units in [`Commentary.lean`](HilbertFoundations/Commentary.lean)):
- `concl.pseudo_geometry` (`PseudoGeometryTheorem`): on a plane satisfying I, II, IV, the points off a line `t` carry a euclidean pseudo-geometry in which `t` is the line at infinity. The ideal elements are not constructed, so only the consequences for the real points are stated. Not proved.
- `concl.angle_sum` (`AngleSumTheorem`): if one triangle has angle sum greater than, equal to, or less than two right angles, so has every triangle. The three comparisons are defined from the primitive notions and agree with Theorem 20 in planes satisfying I–IV (`angleSumEqTwoRight_of_parallels`). Missing: the theorem itself, which needs a part of neutral geometry (addition of angles, the exterior angle theorem, Saccheri quadrilaterals) that is not developed here.

**The Appendix** (eight units in [`Commentary.lean`](HilbertFoundations/Commentary.lean)). The Appendix is a summary of Hilbert's memoir on the foundation of plane geometry on a group of displacements (*Math. Ann.* 56, 1902); it outlines the proof without carrying it out. Its definitions and its axioms I–III are formalized, and the euclidean plane with its proper motions is proved to satisfy them (`appendix_axioms_consistent`). The Jordan curve theorem, which the memoir uses, is proved (unit `app.jordan_theorem`, `jordanCurveTheorem`, with the copied library [`JordanPick/`](JordanPick/README.md)); the definitions of the Appendix do not depend on it. What is open is the main theorem, the steps of Hilbert's argument and the theorem on the invariant sub-group:
- `app.main_theorem` (`AppendixMainTheorem`): a geometry satisfying axioms I–III is the euclidean or the Bolyai–Lobachevskian plane. As formalized the statement is false for the empty plane (`not_appendixMainTheorem`); the statement for a plane with a point, `AppendixMainTheoremNonempty`, is open. It is the content of the memoir. Proved: the euclidean plane is euclidean in the sense of the theorem (`euclideanPlane_isEuclidean`).
- `app.true_circle_jordan` (`TrueCirclesAreJordan`): every true circle is a closed Jordan curve. Proved: a true circle is closed in the plane (`trueCircle_closed`).
- `app.rotation_group` (`RotationsOfTrueCircle`): the rotations about `M` act on a true circle about `M` as the rotations of the ordinary circle. Proved: these rotations are transitive on the circle (`trueCircle_transitive`, from axiom I in its group reading).
- `app.two_fixed_points` (`TwoFixedPointsIdentity`), `app.transitive` (`DisplacementsTransitive`), `app.middle` (`AtMostOneMiddle`): a displacement with two fixed points is the identity; the displacements are transitive; a segment has at most one middle. These three and `RotationsOfTrueCircle` are shown to follow from `AppendixMainTheoremNonempty` (`steps_of_main` in [`CommentaryClose.lean`](HilbertFoundations/CommentaryClose.lean)), and `AtMostOneMiddle` from `TwoFixedPointsIdentity` (`atMostOneMiddle_of_twoFixedPoints`). A proof from axioms I–III is missing.
- `app.true_line` (`TrueLineIsCurve`, `TrueLinesMeetAtMostOnce`): the true straight line is a continuous curve without double points, and two true straight lines have at most one point in common. The definition is formalized. Proved: in the euclidean plane the true straight line through `A`, `B` lies on the ordinary line `AB` (`euclideanPlane_trueLine_subset`).
- `app.invariant_subgroup` (`AppendixEuclideanTheorem`): if the displacements have an invariant sub-group, the geometry is euclidean. It rests on the main theorem. Proved: the euclidean plane satisfies the added condition (`euclideanPlane_hasInvariantSubgroup`).

Two classical theorems occur only as hypotheses inside units whose own claim is proved: `LegendreTheorem` and `ArchimedesAngleSumGivesParallels` in `Commentary.lean` are stated and not proved. What a unit with another status leaves unformalized (for instance Hilbert's ellipse geometry of § 23 as a model, or Dehn's form of the theorem on the case without parallels) is said in its Lean reading; see also [docs/FAITHFULNESS.md](docs/FAITHFULNESS.md).

Four units are proved with a theorem whose proof is not this project's: `app.jordan_theorem` with the Jordan curve theorem of the copied library `JordanPick`, `th.42` with the Hasse–Minkowski theorem of the dependency Tau Ceti, `s38.two_variables` with Artin's theorem of the copied library `Hilbert17`, and `th.44` with the separation by orderings and the transfer of sign conditions of `Hilbert17` and the real closure of Tau Ceti. In each case this repository proves the passage from those theorems to the statement of the unit; for `th.42` this includes the verification of the hypotheses of the Hasse–Minkowski theorem at the places of the field, and for `th.44` the passage from an ordering of a finitely generated field to an embedding into `ℝ`.

## Reading a unit

```lean
/-!
## [th.37] Theorem 37

*(§ 31)*

> Pascal's theorem (theorem 21) cannot be demonstrated by means of the axioms I, II, III alone; that is to say, by exclusion of the axioms of congruence and also the axiom of Archimedes.

**Lean reading.** `theorem37`: there is a space geometry (in `Type`) satisfying I, II, III
(`SpaceOrder`, `SpaceParallels`) with a plane `α` in which Pascal's theorem fails. The model is
Hilbert's (§ 34): the space of § 29 over the desarguesian number system `Ω(s, t)` of § 33, …

**Status.** proved
-/

theorem theorem37 : ∃ (P L Pl : Type) (_ : HasLines P L) (_ : HasPlanes P Pl) (_ : HasBetween P),
    SpaceOrder P L Pl ∧ SpaceParallels P L Pl ∧
      ∃ α : Pl, ¬PascalTheorem {A : P // A ∈ α} (L := {a : L // LiesInPlane (Point := P) a α}) :=
```

The unit ids are `ax.I1`, …, `ax.V`, `ax.completeness` for the axioms, `th.1`, …, `th.44` for the theorems, `sN.<slug>` for the other statements of § N, and `intro.<slug>`, `concl.<slug>`, `app.<slug>` for the Introduction, the Conclusion and the Appendix. The conventions are fixed in [`HilbertFoundations/Basic.lean`](HilbertFoundations/Basic.lean), in its header and in the unit blocks of the axioms:
- "lies on" and "lies in" are relations between a point and a line or a plane, written `A ∈ a` and `A ∈ α`; `Between A B C` says that `B` lies between `A` and `C`;
- congruence is `SegCong A B A' B'` and `AngCong A O B A' O' B'`, relations on tuples of points; the axioms speak only of genuine segments and angles, so the values on degenerate tuples are unconstrained;
- a plane geometry is a pair `(Point, Line)` and a geometry of space a triple `(Point, Line, Plane)`; the plane axioms have a plane form and a space form, and every plane of a geometry of space is a plane geometry;
- "parallel" is Hilbert's notion: in a plane, two lines without a common point;
- axiom I 7 is read literally, so its clauses about planes hold vacuously when there is no plane, and a single line satisfies the space axioms (`coord_one_spaceGeometry`); a result that needs a plane assumes one;
- a result assumes the axiom classes that Hilbert names for it, or fewer.

## The book and the Lean files

| Book | Lean files | Units |
|---|---|---|
| Introduction | [`Commentary.lean`](HilbertFoundations/Commentary.lean) | 5 |
| Chapter I, *The five groups of axioms*, §§ 1–8 | [`Basic.lean`](HilbertFoundations/Basic.lean) (the axioms and the definitions of §§ 1–6 and 8), [`Order.lean`](HilbertFoundations/Order.lean) (§§ 2–5, Theorems 1–8), [`Congruence.lean`](HilbertFoundations/Congruence.lean) (§§ 6–7, Theorems 9–20) | 99 |
| Chapter II, *The compatibility and mutual independence of the axioms*, §§ 9–12 | [`Analytic.lean`](HilbertFoundations/Analytic.lean) (§ 9), [`Independence.lean`](HilbertFoundations/Independence.lean) (§§ 10–12) | 36 |
| Chapter III, *The theory of proportion*, §§ 13–17 | [`Analytic.lean`](HilbertFoundations/Analytic.lean) (§ 13), [`Pascal.lean`](HilbertFoundations/Pascal.lean) (§ 14, Theorem 21), [`Proportion.lean`](HilbertFoundations/Proportion.lean) (§§ 15–17, Theorems 22–23) | 61 |
| Chapter IV, *The theory of plane areas*, §§ 18–21 | [`Areas.lean`](HilbertFoundations/Areas.lean) (Theorems 24–31) | 43 |
| Chapter V, *Desargues's theorem*, §§ 22–30 | [`Desargues.lean`](HilbertFoundations/Desargues.lean) (§ 22, Theorem 32), [`NonDesargues.lean`](HilbertFoundations/NonDesargues.lean) (§ 23, Theorem 33), [`DesarguesAlgebra.lean`](HilbertFoundations/DesarguesAlgebra.lean) (§§ 24–30, Theorems 34–35) | 67 |
| Chapter VI, *Pascal's theorem*, §§ 31–35 | [`NonPascal.lean`](HilbertFoundations/NonPascal.lean) (Theorems 36–39) | 41 |
| Chapter VII, *Geometrical constructions based upon the axioms I–V*, §§ 36–39 | [`Constructions.lean`](HilbertFoundations/Constructions.lean) (Theorems 40–44) | 42 |
| Conclusion | [`Commentary.lean`](HilbertFoundations/Commentary.lean) | 15 |
| Appendix | [`Commentary.lean`](HilbertFoundations/Commentary.lean) | 21 |

Ten further files contain no unit blocks. They prove statements that a chapter file states as a `Prop`, because the proof uses later chapters, is long, or uses code that is not this project's: the copied library `JordanPick` (for `JordanCurveClose.lean`), the dependency Tau Ceti (for `Theorem42Close.lean`), the copied library `Hilbert17` (for `TwoVariablesClose.lean`) or both of the latter (for `Theorem44Close.lean`):

| File | Units it proves | Main declarations |
|---|---|---|
| [`OrderPolygon.lean`](HilbertFoundations/OrderPolygon.lean) | `th.6` | `polygonTheorem`, `theorem6_space` |
| [`CongruenceClose.lean`](HilbertFoundations/CongruenceClose.lean) | `th.18`, `s7.circle_properties` | `theorem18`, `theorem18_distinct`, `circlePropertiesClaim` |
| [`CompletenessClose.lean`](HilbertFoundations/CompletenessClose.lean) | `s8.bolzano`, `s8.real_numbers` | `completenessGivesBolzano`, `completenessGivesReals` |
| [`CoordinatesClose.lean`](HilbertFoundations/CoordinatesClose.lean) | `s17.space`, `s17.ideal`, `s30.any_dimension` | `spaceCoordinatesClaim`, `idealElementsClaim`, `anyDimensionClaim` |
| [`ConstructionsClose.lean`](HilbertFoundations/ConstructionsClose.lean) | `th.43`, `s39.regular_polygons`, `s39.malfatti`; partial results for `th.44`; the case of degree two of `s38.two_variables`; the results on `th.42` that do not need the Hasse–Minkowski theorem | `theorem43`, `regularPolygonsClaim`, `malfattiClaim`, `theorem44_one_parameter`, `four_squares_of_isotropic` |
| [`CommentaryClose.lean`](HilbertFoundations/CommentaryClose.lean) | `concl.semi_euclidean`, `concl.non_legendrian`, `concl.legendre_archimedes`; partial results for the Appendix | `semiEuclideanGeometryExists`, `nonLegendrianGeometryExists`, `legendreNeedsArchimedes`, `steps_of_main` |
| [`JordanCurveClose.lean`](HilbertFoundations/JordanCurveClose.lean) | `app.jordan_theorem`, from the Jordan curve theorem of the copied library `JordanPick` | `jordanCurveTheorem`, `IsClosedJordanCurve.exists_sphere_map`, `jordanCurveTheorem_of_isometry` |
| [`Theorem42Close.lean`](HilbertFoundations/Theorem42Close.lean) | `th.42`, from the Hasse–Minkowski theorem of the dependency Tau Ceti | `theorem42`, `exists_isotropic_of_totallyPositive`, `not_anisotropic_diagonalForm5` |
| [`TwoVariablesClose.lean`](HilbertFoundations/TwoVariablesClose.lean) | `s38.two_variables`, from Artin's theorem of the copied library `Hilbert17` | `twoVariableClaim` |
| [`Theorem44Close.lean`](HilbertFoundations/Theorem44Close.lean) | `th.44`, from the separation by orderings and the transfer of sign conditions of the copied library `Hilbert17` and the real closure of the dependency Tau Ceti | `theorem44`, `theorem43For_closure`, `exists_ringHom_real_neg`, `nonempty_ringHom_real` |

The directory [`JordanPick/`](JordanPick/) is not part of the formalization of the book and was not written for this repository. It holds four Lean files copied without change from <https://github.com/rkirov/jordan_pick> (Rado Kirov, Apache License 2.0, commit `7905cd4`): a proof of the Jordan curve theorem by Maehara's method, with the Brouwer fixed point theorem for the plane. The files are built as a second library of the package, `JordanPick`, and are used only by `JordanCurveClose.lean`. [`JordanPick/README.md`](JordanPick/README.md) gives the source, the commit, the checksums of the files and what differs from the upstream repository; see also [docs/SOURCES.md](docs/SOURCES.md).

The library [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (The Tau Ceti contributors, Apache License 2.0) is used in a different way: it is a dependency of the package, fetched by Lake, and none of its code is copied into this repository. `lakefile.toml` and `lake-manifest.json` pin it to the commit `aa3cfad1274c06cff25f2b58848498b3c3f68d0f`, its last commit on Lean v4.36.0, which uses the same mathlib commit as this repository. Of the files of `HilbertFoundations/` two import it: `Theorem42Close.lean`, which takes from it the Hasse–Minkowski theorem for quadratic forms over number fields, with the definitions the theorem is stated in, and `Theorem44Close.lean`, which takes from it the real closure of an ordered field; the headers of these files list the declarations used. For `Theorem42Close.lean` Lake builds the Tau Ceti modules that it imports, directly or through other modules: 1,044 modules, about 255,000 lines; the files of the copied library `Hilbert17` (next paragraph) import Tau Ceti as well and need 78 more, and `Theorem44Close.lean` needs none beyond these. Tau Ceti is not part of the formalization of the book, and neither the Hasse–Minkowski theorem nor the real closure is a result of this project; see [docs/SOURCES.md](docs/SOURCES.md) and [docs/FAITHFULNESS.md](docs/FAITHFULNESS.md), "Third-party code".

The directory [`Hilbert17/`](Hilbert17/) is, like `JordanPick/`, not part of the formalization of the book and was not written for this repository. It holds 18 Lean files from <https://github.com/pd4st8hb95-hub/hilbert17-lean> (commit `19cd90e`), a proof of Artin's theorem on definite polynomials with real coefficients (the solution of Hilbert's seventeenth problem). The proof is the work of the author of that repository. Unlike the files of `JordanPick/`, these are not copied without change: the upstream repository is built with Lean v4.32.1 and with its own copies of mathlib and of Tau Ceti files, and here the files are built with Lean v4.36.0, mathlib v4.36.0 and Tau Ceti as a dependency. Three files are identical to the upstream files; fourteen differ from them in import lines and in five further lines; and one, `OrderingSeparation.lean`, is rewritten, so that the one statement of it that the other files use is proved from Tau Ceti. No statement that is kept has changed. The files are built as a third library of the package, `Hilbert17`, and are used only by `TwoVariablesClose.lean`, which takes from them Artin's theorem for polynomials with real coefficients, and by `Theorem44Close.lean` and its helper module `Theorem44CloseAux1.lean`, which take from them the separation by orderings (`Hilbert17.RingPreordering.isSumSq_iff_nonneg_all_orders`) and the transfer of sign conditions between real closed fields (`Hilbert17Transfer.exists_matching_signs_eval₂`, with `Hilbert17Transfer.eval₂_finSuccEquiv`). Lake builds the 18 modules and the 83 modules of Tau Ceti that they import, 78 of which `Theorem42Close.lean` does not need. The files are not under the licence of this repository: the upstream repository keeps the Apache License 2.0 for the third-party material it attributes and states that it assigns no project-wide licence to its own contributions, and the Lean files copied here carry no licence header. They are reproduced with attribution so that the formalization builds, and no licence is granted for them here. [`Hilbert17/README.md`](Hilbert17/README.md) gives the source, the commit, every change and the checksums of the files; see also [License](#license) and [docs/SOURCES.md](docs/SOURCES.md).

## Layout

```
lakefile.toml, lake-manifest.json        the package and its two direct dependencies, mathlib v4.36.0 and Tau Ceti, each pinned to a commit
HilbertFoundations.lean                  root: imports the fourteen chapter files and the ten closing files
HilbertFoundations/Basic.lean            primitive notions, the axioms as Props and classes, conventions, status vocabulary
HilbertFoundations/Order.lean            §§ 2–5: connection, order, parallels
HilbertFoundations/Congruence.lean       §§ 6–7: congruence
HilbertFoundations/Analytic.lean         § 9: the field Ω and the coordinate models; § 13: number systems
HilbertFoundations/Independence.lean     §§ 10–12: the independence models
HilbertFoundations/Pascal.lean           § 14: Pascal's theorem
HilbertFoundations/Proportion.lean       §§ 15–17: algebra of segments, proportion, equations of lines and planes
HilbertFoundations/Areas.lean            §§ 18–21: plane areas
HilbertFoundations/Desargues.lean        § 22: Desargues's theorem
HilbertFoundations/NonDesargues.lean     § 23: a non-desarguesian plane geometry
HilbertFoundations/DesarguesAlgebra.lean §§ 24–30: the algebra of segments from Desargues's theorem
HilbertFoundations/NonPascal.lean        §§ 31–35: Pascal's theorem and commutativity
HilbertFoundations/Constructions.lean    §§ 36–39: constructions by straight-edge and transferer
HilbertFoundations/Commentary.lean       Introduction, Conclusion, Appendix
HilbertFoundations/OrderPolygon.lean, CongruenceClose.lean, CompletenessClose.lean,
  CoordinatesClose.lean, ConstructionsClose.lean, CommentaryClose.lean, JordanCurveClose.lean,
  Theorem42Close.lean, TwoVariablesClose.lean, Theorem44Close.lean
                                         proofs of statements that the chapter files state (table above);
                                         only Theorem42Close.lean and Theorem44Close.lean import the dependency Tau Ceti, and only
                                         TwoVariablesClose.lean, Theorem44Close.lean and Theorem44CloseAux1.lean the copied library Hilbert17
HilbertFoundations/<Name>Aux*.lean       107 helper modules of the files above
JordanPick/JordanCurve.lean, JordanPick/JordanCurve/{Arcs,Brouwer,Counting}.lean
                                         third-party code, copied without change from rkirov/jordan_pick (Rado Kirov,
                                         Apache License 2.0): the Jordan curve theorem, used by JordanCurveClose.lean
JordanPick/README.md                     source, commit, licence and checksums of the copied files
Hilbert17/*.lean                         third-party code, 18 files from pd4st8hb95-hub/hilbert17-lean, changed for the toolchain of
                                         this repository and not under its licence: Artin's theorem, used by TwoVariablesClose.lean
                                         and Theorem44Close.lean
Hilbert17/README.md                      source, commit, licence situation, changes and checksums of these files
data/foundations.json                    the text, extracted from the Gutenberg LaTeX source
docs/UNITS.md                            generated unit map
docs/FAITHFULNESS.md                     how the text is read: conventions, readings, corrections, what is not formalized
docs/SOURCES.md                          the edition, bibliography and copyright
scripts/extract_source.py                Gutenberg LaTeX (17384-t.tex) → data/foundations.json
scripts/make_skeletons.py                data/foundations.json → the chapter files with the unit blocks of the labelled statements
scripts/unit_table.py                    unit map and status check
scripts/check.py                         checks single files, a bounded number at a time
scripts/AxiomsAudit.lean                 axiom audit
scripts/ClosingProofs.lean               checks that the closing files prove the units as stated
.github/workflows/ci.yml                 build, axiom audit, closing-proof check and unit map check on every push and pull request
```

`data/foundations.json` holds the translator's preface, the Introduction, the 7 chapters with their 39 sections, the Conclusion, the Appendix, and the 68 labelled statements (24 axioms and 44 theorems).

## Building and checking

Lean v4.36.0 and mathlib v4.36.0 are pinned in `lean-toolchain` and `lakefile.toml`. The dependency Tau Ceti is pinned to a commit in `lakefile.toml`, and `lake-manifest.json` records the commit of every dependency.

```sh
lake exe cache get                       # download prebuilt mathlib (mathlib only)
lake build                               # every file, with the copied libraries and the modules of Tau Ceti that the closing files import
lake env lean scripts/AxiomsAudit.lean   # axiom audit
lake env lean scripts/ClosingProofs.lean # the closing files prove the units as stated
python3 scripts/unit_table.py --check    # regenerate docs/UNITS.md and check statuses
```

- `lake exe cache get` covers mathlib only. `lake build` therefore also compiles, from source, the modules of the dependency Tau Ceti that `Theorem42Close.lean`, `Theorem44Close.lean` and the copied library `Hilbert17` import, directly or through other modules, 1,122 modules (1,044 for `Theorem42Close.lean`), and the 18 modules of `Hilbert17`, which take about half an hour the first time; later builds reuse them. The other modules of Tau Ceti are not built. A target that does not depend on `Theorem42Close.lean`, `TwoVariablesClose.lean` or `Theorem44Close.lean`, such as `lake build HilbertFoundations.Constructions`, does not build any of them.
- `scripts/AxiomsAudit.lean` imports the root module and reports an error for every declaration of the namespace `HilbertFoundations` that depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`; a `sorry` would appear as `sorryAx`. The axioms are collected through everything a declaration depends on, so the declarations of the copied library `JordanPick` (namespace `JordanCurve`) that `jordanCurveTheorem` uses are covered through it; the audit does not examine the other declarations of that library. In the same way the declarations of Tau Ceti that the proof of `theorem42` uses are covered through `theorem42`, with everything they depend on; the declarations of Tau Ceti are not examined one by one, and those that `theorem42` does not use are outside the audit. The same holds for the copied library `Hilbert17` (namespaces `Hilbert17`, `Hilbert17Target`, `Hilbert17Transfer`): the audits of `twoVariableClaim` and of `theorem44` cover the parts of it, and of Tau Ceti, that the proofs use.
- `scripts/ClosingProofs.lean` checks, for every unit whose statement is a `Prop` of a chapter file proved in one of the ten closing files, that the closing theorem has exactly that `Prop` as its type (for `th.42`, that `theorem42` has the type `Theorem42`); for `th.18` and `app.main_theorem` it checks the refutations of the statements as printed.
- `scripts/unit_table.py` rewrites `docs/UNITS.md` from the unit blocks. With `--check` it fails if a unit has no status or a placeholder status, if a labelled axiom or theorem of `data/foundations.json` has no unit, if a unit id occurs twice, or if a unit whose status begins with `proved` is followed by a declaration containing `sorry`.
- The CI workflow runs `lake build` (which includes the copied libraries and the modules of Tau Ceti), the audit, `scripts/ClosingProofs.lean` and the unit map check, and fails if `docs/UNITS.md` differs from the generated file.
- `python3 scripts/check.py HilbertFoundations/Order.lean` checks one file: it builds the project modules the file imports and then runs `lake env lean` on it. `--slots N` (default 3) bounds the number of Lean processes when several checks run at once, and `--no-deps` skips the build of the imports.

`lake build` builds several files in parallel. If memory is short, build a few modules at a time, for instance `lake build HilbertFoundations.Order`, then `lake build HilbertFoundations.Congruence HilbertFoundations.Analytic`.

## Contributing

Lean checks that a statement is proved, not that it is the statement Hilbert made. Reports of a misreading, or of a unit that should have another status, are welcome as issues.

## License

- Lean code and documentation: [Apache License 2.0](LICENSE), except the Lean files in `Hilbert17/`, which are not under this licence (see below).
- The four Lean files in `JordanPick/` are copied, without change, from <https://github.com/rkirov/jordan_pick>, which is under the Apache License 2.0, the licence of this repository. Their copyright belongs to their author, Rado Kirov, not to this project; see [`JordanPick/README.md`](JordanPick/README.md).
- The library Tau Ceti (<https://github.com/TauCetiProject/TauCeti>), which `HilbertFoundations/Theorem42Close.lean`, `HilbertFoundations/Theorem44Close.lean` and the files of `Hilbert17/` import, is under the Apache License 2.0. Its copyright belongs to its contributors, not to this project: the headers of its files name "The Tau Ceti contributors", and some of them other holders (see [docs/SOURCES.md](docs/SOURCES.md)). It is a dependency that Lake fetches from its own repository: none of its files is in this repository, and it is not redistributed here.
- The 18 Lean files in `Hilbert17/`, which `HilbertFoundations/TwoVariablesClose.lean`, `HilbertFoundations/Theorem44Close.lean` and `HilbertFoundations/Theorem44CloseAux1.lean` import, are not covered by the licence of this repository. They come from <https://github.com/pd4st8hb95-hub/hilbert17-lean>, and the copyright of the proof belongs to the author of that repository, not to this project. That repository contains the text of the Apache License 2.0 and states, in its files `THIRD_PARTY.md` and `PROVENANCE.json`, that the licence is kept for the third-party material it attributes and that no project-wide licence is assigned to its own contributions; its Lean files carry no licence header. The files are reproduced here with attribution, so that the formalization builds, and this repository grants no licence for them. One of them, `OrderingSeparation.lean`, is rewritten, and lines of fourteen others are changed; that file and the changed lines are this project's. See [`Hilbert17/README.md`](Hilbert17/README.md) and [docs/SOURCES.md](docs/SOURCES.md).
- Quotations from Townsend's translation in the Lean files and in `data/` are from the 1902 translation (in the Project Gutenberg transcription), which is in the public domain in the USA; see [docs/SOURCES.md](docs/SOURCES.md).
