import HilbertFoundations.Congruence
import HilbertFoundations.Analytic
import HilbertFoundations.ConstructionsAux10

/-!
# Constructions with straight-edge and transferer of segments (§§ 36–39, Theorems 40–44)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 36. Geometrical constructions by means of a straight-edge and a transferer of segments
* § 37. Analytical representation of the co-ordinates of points which can be so constructed
* § 38. The representation of algebraic numbers and of integral rational functions as sums of squares
* § 39. Criterion for the possibility of a geometrical construction by means of a straight-edge and a transferer of segments

## Helper modules

* `ConstructionsAux.lean`: the generic notions (`Perp`, `Constr` — constructions by problems 1–5,
  `RulerTransferer` — constructions by straight-edge and transferer) and the algebra of the
  coordinate plane `Coord K 2` (cross product, lines, right angles);
* `ConstructionsAux2.lean`: Hilbert's constructions of the parallel (Fig. 50) and of a
  perpendicular (Fig. 51) by straight-edge and transferer;
* `ConstructionsAux3.lean`: Theorem 40 in the coordinate plane over an ordered Pythagorean field;
* `ConstructionsAux4.lean`: Hilbert's domain `Ω(R)` (`PythClosure`) and Theorem 41;
* `ConstructionsAux5.lean`: quadratic extensions of subfields of `ℝ` and the extension of their
  embeddings into `ℂ`; every embedding maps the numbers of `Ω` into `Ω`;
* `ConstructionsAux6.lean`: conjugates of the numbers of `Ω`, towers of square roots and Theorem 44
  without parameters, regular polygons;
* `ConstructionsAux7.lean`: Theorems 42 and 43 (definitions, partial results, Hilbert's proof of
  Theorem 43 from Theorem 42);
* `ConstructionsAux8.lean`: Fig. 52, the right triangle of § 37, a contact problem of Apollonius;
* `ConstructionsAux9.lean`: towers of square roots over a domain `R` with parameters, the statement
  of Theorem 44, and the necessity of its condition;
* `ConstructionsAux10.lean`: Hilbert's reduction of Theorem 44 to the generalization of
  Theorem 43 (`Theorem43For R`), for any number of parameters.

## The setting

Hilbert's constructions take place in a plane satisfying the axioms I–V. The constructions are
defined here for any system of points and lines (`Constr`, `RulerTransferer`); the existence of
the elementary constructions (problems 1–5) is proved from the axioms (units `s36.problem1` …
`s36.problem5`). The comparison of the two kinds of construction (Theorems 40, 41, 44) is carried
out, as Hilbert does in § 37, in the coordinate plane `Coord K 2` over an ordered field `K`
(Pythagorean where laying off segments requires it): this is the model of § 9 (with `K = Ω` or
`ℝ`), and by Hilbert's Chapters III and V every plane satisfying I–V is such a coordinate plane;
that coordinatization is not formalized in this project, so the analytic theorems are statements
about the coordinate planes.
-/

namespace HilbertFoundations

open Coord Polynomial
open scoped Real

universe u v

/-!
## [s36.plane] Constructions in a plane

*(§ 36)*

> Suppose we have given a geometry of space, in which all of the axioms I–V are valid. For the sake of simplicity, we shall consider in this chapter a a plane geometry which is contained in this geometry of space and shall investigate the question as to what elementary geometrical constructions may be carried out in such a geometry.

**Lean reading.** The chapter is formalized in plane geometry: the notions of construction are
defined for an arbitrary system of points and lines `(P, L)` with betweenness and congruence, and
the problems are solved from the plane classes of `Basic.lean`; the analytic comparisons are made
in the coordinate plane `Coord K 2` (see the module header). The passage from a geometry of space to
one of its planes is the restriction to a plane built in `Order.lean` and is not repeated here.

**Status.** remark
-/

/-!
## [s36.problem1] Problem 1: joining two points, intersecting two lines

*(§ 36)*

> Upon the basis of the axioms of group I, the following constructions are always possible. Problem 1. To join two points with a straight line and to find the intersection of two straight lines, the lines not being parallel.

**Lean reading.** From I 1–2 alone (`Connection`): two distinct points lie on one and only one line
(`problem1_join`), and two distinct lines that are not parallel (`¬Parallel`, i.e. they meet, § 5)
have one and only one common point (`problem1_meet`). "Not parallel" includes "distinct": two equal
lines are not parallel in Hilbert's sense but have no single intersection.

**Status.** proved
-/

section Problems

variable {P : Type u} {L : Type v} [HasLines P L]

theorem problem1_join [Connection P L] {A B : P} (h : A ≠ B) : ∃! a : L, A ∈ a ∧ B ∈ a := by
  obtain ⟨a, ha, hb⟩ := exists_line (Line := L) h
  exact ⟨a, ⟨ha, hb⟩, fun b ⟨ha', hb'⟩ => line_unique h ha' hb' ha hb⟩

theorem problem1_meet [Connection P L] {a b : L} (hab : a ≠ b)
    (h : ¬Parallel (Point := P) a b) : ∃! X : P, X ∈ a ∧ X ∈ b := by
  obtain ⟨X, hXa, hXb⟩ := not_not.1 h
  refine ⟨X, ⟨hXa, hXb⟩, fun Y ⟨hYa, hYb⟩ => ?_⟩
  by_contra hYX
  exact hab (line_unique hYX hYa hXa hYb hXb)

/-!
## [s36.problem2] Problem 2: the parallel through a point

*(§ 36)*

> Axiom III renders possible the following construction: Problem 2. Through a given point to draw a parallel to a given straight line.

**Lean reading.** With I and III in the plane (`PlaneParallels`): through a point `A` outside a
line `a` there is one and only one line parallel to `a` (`problem2`). For a point on `a` there is
no parallel in Hilbert's sense (parallel lines have no common point), so the problem is posed for
a point outside the line.

**Status.** proved
-/

theorem problem2 [PlaneParallels P L] {A : P} {a : L} (h : A ∉ a) :
    ∃! b : L, A ∈ b ∧ Parallel (Point := P) a b := by
  obtain ⟨b, ⟨hAb, hb⟩, hu⟩ := exists_unique_parallel (Point := P) (Line := L) h
  refine ⟨b, ⟨hAb, fun ⟨X, h1, h2⟩ => hb ⟨X, h2, h1⟩⟩, fun c ⟨hAc, hc⟩ => hu c ⟨hAc, ?_⟩⟩
  exact fun ⟨X, h1, h2⟩ => hc ⟨X, h2, h1⟩

/-!
## [s36.problem3] Problem 3: laying off a segment

*(§ 36)*

> By the assistance of the axioms (IV) of congruence, it is possible to lay off segments and angles; that is to say, in the given geometry we may solve the following problems: Problem 3. To lay off from a given point upon a given straight line a given segment.

**Lean reading.** With IV 1 (`SegmentCongruence`): a segment `AB` can be laid off from a point `O`
of a line on the side of a point `Q ≠ O` of the line in one and only one way (`problem3`); the
point lies on the line (`problem3_mem`). On a line through `O` there are two sides, hence two
solutions.

**Status.** proved
-/

theorem problem3 [HasBetween P] [HasSegCong P] [SegmentCongruence P L] {A B O Q : P}
    (hAB : A ≠ B) (hOQ : O ≠ Q) : ∃! X : P, SameSidePt (Line := L) O Q X ∧ SegCong A B O X :=
  exists_unique_segCong hAB hOQ

theorem problem3_mem [HasBetween P] [LineOrder P L] {O Q X : P} {a : L} (hO : O ∈ a)
    (hQ : Q ∈ a) (hOQ : O ≠ Q) (hX : SameSidePt (Line := L) O Q X) : X ∈ a :=
  mem_of_collinear hX.2.2.1 hOQ.symm hQ hO

/-!
## [s36.problem4] Problem 4: laying off an angle

*(§ 36)*

> Problem 4. To lay off on a given straight line a given angle; or what is the same thing, to construct a straight line which shall cut a given straight line at a given angle.

**Lean reading.** With IV 4 of plane geometry (`PlaneAngleCongruence`): for an angle `∠AOB`, a line
`a'` with points `O' ≠ A'` and a point `D'` outside `a'`, there is a point `B'` on the side of `D'`
with `∠AOB ≡ ∠A'O'B'`; the line `O'B'` then cuts `a'` at the given angle (`problem4`). On the given
side of `a'` the half-ray `O'B'` is unique (the last clause of `problem4`, second half of IV 4).

**Status.** proved
-/

theorem problem4 [HasBetween P] [HasAngCong P] [PlaneAngleCongruence P L] {A O B O' A' D' : P}
    {a' : L} (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ a') (hA' : A' ∈ a') (hA'O' : A' ≠ O')
    (hD' : D' ∉ a') :
    ∃ B' : P, B' ∉ a' ∧ AngCong A O B A' O' B' ∧
      (∀ X : P, X ∈ Interior (Line := L) A' O' B' → SameSide a' X D') ∧
      ∀ B'' : P, B'' ∉ a' → AngCong A O B A' O' B'' →
        (∀ X : P, X ∈ Interior (Line := L) A' O' B'' → SameSide a' X D') →
          ray (Line := L) O' B'' = ray (Line := L) O' B' :=
  PlaneAngleCongruence.axiomIV4.1 A O B a' O' A' D' h hO' hA' hA'O' hD'

end Problems

/-!
## [s36.constructions] The constructions possible by the axioms I–V

*(§ 36)*

> It is impossible to make any new constructions by the addition of the axioms of groups II and V. Consequently, when we take into consideration merely the axioms of groups I–V, all of those constructions and only those are possible, which may be reduced to the problems 1–4 given above.

**Lean reading.** Hilbert does not define "construction"; the second sentence is taken as the
definition. `Constr p5 S` is the set of points and lines obtained from a set `S` of given points by
finitely many applications of problems 1–4 (and of problem 5 when `p5` holds); its constructors
`join`, `meet`, `parallel`, `layOff`, `angle`, `perp` are the problems, each applied to elements
already constructed. The first sentence is a heuristic remark, not a theorem: the axioms of
groups II and V assert the existence of points (II 2, the point of V) without determining them, so
they provide no construction step.

**Status.** definition
-/

/-- The elements constructible by problems 1–4 from the given points `S`. -/
abbrev ElemConstr {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] (S : Set P) : P ⊕ L → Prop :=
  Constr False S

/-!
## [s36.problem5] Problem 5: a perpendicular

*(§ 36)*

> We will add to the fundamental problems 1–4 also the following: Problem 5. To draw a perpendicular to a given straight line. We see at once that this construction can be made in different ways by means of the problems 1–4.

**Lean reading.** `Perp P a b`: `b` meets `a` in a point `O` and forms a right angle with it there.
(1) *Existence* (`problem5`): in a plane with I, II, IV (`PlaneCongruence`) every line has a
perpendicular, the line through two points equidistant from two points of it (Congruence.lean,
`Frame.bisector`, `Frame.midpoint_rt`). (2) *Reduction to problems 1–4*: as a construction
problem, the perpendicular has to be drawn through a constructed point (constructor `Constr.perp`);
this is checked in the coordinate plane over an ordered Pythagorean field. Hilbert's reductions
(Fig. 50, Fig. 51) make free choices ("any point", "any two straight lines passing through the
point `A`"), i.e. they may use an auxiliary point that is not determined by the data. With such a
point the claim holds for any data: if the given points contain two distinct points `A`, `B`, every
element constructible with problem 5 is constructible by problems 1–4 once an arbitrary point `P`
outside `AB` is added (`problem5_with_auxiliary_point`); without auxiliary points it holds when the
given points are not all on one line (`problem5_reducible`). The free choice cannot be dropped:
from the two given points `(0, 0)`, `(1, 0)` alone, problem 5 constructs the axis `x = 0`, while
problems 1–4 construct only elements of the axis `y = 0` (`problem5_not_reducible`: there is no
angle to lay off and no point outside the line).

**Status.** proved (reading)
-/

/-- Constructions are monotone in the given points. -/
theorem Constr.mono {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] {p5 : Prop} {S T : Set P} (hST : S ⊆ T) {e : P ⊕ L} (h : Constr p5 S e) :
    Constr p5 T e := by
  induction h with
  | given hA => exact .given (hST hA)
  | join _ _ hAB hAa hBa iA iB => exact .join iA iB hAB hAa hBa
  | meet _ _ hab hXa hXb ia ib => exact .meet ia ib hab hXa hXb
  | parallel _ _ hAa hAb hpar iA ia => exact .parallel iA ia hAa hAb hpar
  | layOff _ _ _ _ hAB hOa hXa hXO hseg iA iB iO ia => exact .layOff iA iB iO ia hAB hOa hXa hXO hseg
  | angle _ _ _ _ _ hn hn' hang hO'b hB'b iA iO iB iA' iO' =>
    exact .angle iA iO iB iA' iO' hn hn' hang hO'b hB'b
  | perp hp _ _ hAb hperp iA ia => exact .perp hp iA ia hAb hperp

section Problem5

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

theorem problem5 [PlaneCongruence P L] (a : L) : ∃ b : L, Perp P a b := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) a
  have hl : ∀ X : P, ∃ l : L, X ∈ l := by
    intro X
    by_cases hXA : X = A
    · subst hXA
      obtain ⟨l, h1, -⟩ := exists_line (Line := L) hAB
      exact ⟨l, h1⟩
    · obtain ⟨l, h1, -⟩ := exists_line (Line := L) hXA
      exact ⟨l, h1⟩
  let F := planeFrame (P := P) (L := L) hl
  have hS : F.IsPl Set.univ := rfl
  obtain ⟨Q, R, -, -, hopp, hQ, hR⟩ := F.bisector hS trivial trivial hAB
  have hQR : Q ≠ R := by
    rintro rfl
    obtain ⟨-, -, X, -, hX⟩ := hopp
    exact not_between_self (Line := L) hX
  obtain ⟨M, hMm, hM, hrt⟩ := F.midpoint_rt hS trivial trivial trivial trivial hAB hopp hQ hR hQR
  have hMa : M ∈ a := mem_of_collinear (collinear_of_between (Line := L) hM).swap23 hAB hA hB
  refine ⟨line (Line := L) Q R hQR, M, A, Q, hMa, hA, hMm, mem_line_left hQR, ?_⟩
  obtain ⟨hn, C, hC, hc⟩ := hrt
  have hn' : ¬Collinear (Line := L) A M Q := fun h => hn h.swap13
  have hnC : ¬Collinear (Line := L) Q M C := fun h =>
    not_collinear_of_between (L := L) hn' hC h.swap13
  exact ⟨hn', C, hC, angCong_swap_left hn hnC hc⟩

end Problem5

theorem problem5_reducible {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [IsPythagorean K] (S : Set (Coord K 2))
    (hS : ∃ A O B : Coord K 2, A ∈ S ∧ O ∈ S ∧ B ∈ S ∧ ¬Collinear A O B)
    (e : Coord K 2 ⊕ CoordLine K 2) : Constr True S e ↔ Constr False S e := by
  obtain ⟨h1, h2⟩ := theorem40_coord (K := K) (p5 := True) S (fun _ => hS)
  obtain ⟨h3, h4⟩ := theorem40_coord (K := K) (p5 := False) S (fun h => h.elim)
  rcases e with X | a
  · rw [h1, h3]
  · rw [h2, h4]

/-- **Problem 5 by problems 1–4 with an auxiliary point** (Hilbert's free choice in Fig. 51): if
`A ≠ B` are given and `P` is any point outside `AB`, everything constructible from the given points
with problem 5 is constructible by problems 1–4 from the given points and `P`. -/
theorem problem5_with_auxiliary_point {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [IsPythagorean K] (S : Set (Coord K 2)) {A B P : Coord K 2}
    (hA : A ∈ S) (hB : B ∈ S) (hP : ¬Collinear A B P) (e : Coord K 2 ⊕ CoordLine K 2)
    (h : Constr True S e) : Constr False (insert P S) e :=
  (problem5_reducible (insert P S) ⟨A, B, P, Set.mem_insert_of_mem _ hA,
    Set.mem_insert_of_mem _ hB, Set.mem_insert _ _, hP⟩ e).1
    (Constr.mono (Set.subset_insert _ _) h)

theorem problem5_not_reducible {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [IsPythagorean K] :
    Constr True ({pt2 0 0, pt2 1 0} : Set (Coord K 2)) (.inr yAxis) ∧
      ¬Constr False ({pt2 0 0, pt2 1 0} : Set (Coord K 2)) (.inr yAxis) := by
  refine ⟨constr_perp_yAxis, fun h => not_rtLine_yAxis (K := K) ?_⟩
  exact ((theorem40_coord (K := K) (p5 := False) _ (fun h => h.elim)).2 _).1 h

/-!
## [s36.instruments] The straight-edge and the transferer of segments

*(§ 36)*

> In order to carry out the construction in problem 1, we need to make use of only a *straight edge*. An instrument which enables us to make the construction in problem 3, we will call a *transferer of segments*.

**Lean reading.** `RulerTransferer S` is the set of points constructible from `S` with these two
instruments: the common point of two distinct lines each drawn through two constructed points
(`meet`), and the points of a line drawn through two constructed points at the distance of a
constructed segment from a constructed point of it, on either side (`layOff`).
`RulerTransfererLine S a`: `a` can be drawn, i.e. passes through two constructed points. Every
such construction is one by problems 1 and 3 (`rt_imp_constr`).

**Status.** definition
-/

theorem rulerTransferer_constr {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] {p5 : Prop} {S : Set P} :
    (∀ {X : P}, RulerTransferer (L := L) S X → Constr (L := L) p5 S (.inl X)) ∧
      ∀ {a : L}, RulerTransfererLine S a → Constr p5 S (.inr a) := by
  have h : ∀ {X : P}, RulerTransferer (L := L) S X → Constr (L := L) p5 S (.inl X) := by
    intro X hX
    induction hX with
    | given hA => exact Constr.given hA
    | @meet A B C D X a b _ _ _ _ hAB hCD hAa hBa hCb hDb hab hXa hXb iA iB iC iD =>
      exact Constr.meet (Constr.join iA iB hAB hAa hBa) (Constr.join iC iD hCD hCb hDb) hab
        hXa hXb
    | @layOff A B O Q X a _ _ _ _ hAB hOQ hOa hQa hXa hXO hseg iA iB iO iQ =>
      exact Constr.layOff iA iB iO (Constr.join iO iQ hOQ hOa hQa) hAB hOa hXa hXO hseg
  exact ⟨h, fun ⟨A, B, hA, hB, hAB, hAa, hBa⟩ => Constr.join (h hA) (h hB) hAB hAa hBa⟩

/-!
## [s36.reduction] Problems 2, 4, 5 by straight-edge and transferer

*(§ 36)*

> We shall now show that problems 2, 4, and 5 can be reduced to the constructions in problems 1 and 3 and, consequently, all of the problems 1–5 can be completely constructed by means of a straight-edge and a transferer of segments.

**Lean reading.** In the coordinate plane over an ordered Pythagorean field: problems 2 and 4 are
always reducible to problems 1 and 3, i.e. to straight-edge and transferer (Theorem 40); problem 5
is reducible when the given points are not all on one line (`reduction_problems_1_5`), which can
always be arranged by Hilbert's free choice of an auxiliary point (unit `s36.problem5`). Without
such a choice the claim fails for collinear data: with the given points `(0, 0)`, `(1, 0)` the
perpendicular `x = 0` is constructible by problem 5 but cannot be drawn with straight-edge and
transferer (`reduction_problem5_fails`).

**Status.** proved (reading)
-/

theorem reduction_problems_1_5 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [IsPythagorean K] (S : Set (Coord K 2))
    (hS : ∃ A O B : Coord K 2, A ∈ S ∧ O ∈ S ∧ B ∈ S ∧ ¬Collinear A O B) :
    (∀ X : Coord K 2, Constr (L := CoordLine K 2) True S (.inl X) ↔ RulerTransferer S X) ∧
      ∀ a : CoordLine K 2, Constr True S (.inr a) ↔ RulerTransfererLine S a :=
  theorem40_coord S (fun _ => hS)

theorem reduction_problem5_fails {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Constr (L := CoordLine K 2) True ({pt2 0 0, pt2 1 0} : Set (Coord K 2)) (.inr yAxis) ∧
      ¬RulerTransfererLine ({pt2 0 0, pt2 1 0} : Set (Coord K 2)) (yAxis : CoordLine K 2) :=
  ⟨constr_perp_yAxis, not_rtLine_yAxis⟩

/-!
## [th.40] Theorem 40

*(§ 36)*

> Those problems in geometrical construction, which may be solved by the assistance of only the axioms I–V, can always be carried out by the use of the straight-edge and the transferer of segments.

**Lean reading.** The problems solvable by the axioms I–V are those reducible to problems 1–4
(unit `s36.constructions`). `theorem40`: in the coordinate plane `Coord K 2` over any ordered
Pythagorean field `K`, for every set `S` of given points, the points and lines constructible by
problems 1–4 are exactly those constructible by straight-edge and transferer. The axioms used are
I, II, III (in the parallel step) and IV (laying off segments needs `K` Pythagorean, which is
equivalent to IV 1 in a coordinate plane, `isPythagorean_of_axiomIV1`); Archimedes's axiom V is
not needed. The proof follows Hilbert for problem 2 (Fig. 50, `rt_parallelPt`) and for the
perpendiculars (Fig. 51, `rt_perp_exists`); for problem 4 it lays off the two legs of a right
triangle (`rt_angle_line`) instead of Hilbert's Fig. 52, which is verified separately and works
only for acute angles (unit `s36.fig52`). Hilbert's free choices ("any point", "any two straight
lines") are replaced by constructed points: problems 2 and 4 come with a point outside a line (the
given point of problem 2, one of the three non-collinear points of the angle of problem 4), and
that is all the construction needs. The
theorem is proved for the coordinate planes, not for an abstract plane satisfying I–V; the
transfer would need the coordinatization of Chapters III and V, not formalized in this project.

**Status.** proved (reading)
-/

theorem theorem40 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [IsPythagorean K] (S : Set (Coord K 2)) :
    (∀ X : Coord K 2, ElemConstr (L := CoordLine K 2) S (.inl X) ↔ RulerTransferer S X) ∧
      ∀ a : CoordLine K 2, ElemConstr S (.inr a) ↔ RulerTransfererLine S a :=
  theorem40_coord S (fun h => h.elim)

/-!
## [s36.fig50] The parallel by straight-edge and transferer (Fig. 50)

*(§ 36)*

> Proof. In order to reduce problem 2 to the solution of problems 1 and 3, we join the given point $P$ with any point $A$ of the given straight line and produce $PA$ to $C$, making $AC=PA$. Then, join $C$ with any other point $B$ of the given straight line and produce $CB$ to $Q$, making, $BQ=CB$. The straight line $PQ$ is the desired parallel.

**Lean reading.** In the coordinate plane over an ordered field (`fig50`): for `P` outside the line
`AB`, the conditions `A` between `P` and `C`, `AC ≡ PA`, `B` between `C` and `Q`, `BQ ≡ CB` force
`C = 2A - P`, `Q = P + 2(B - A)`, and every line through `P` and `Q` is parallel to every line
through `A` and `B` (`P ≠ Q`). By straight-edge and transferer, `Q` is constructible from `P`, `A`,
`B` (`rt_parallelPt`). The proof is analytic (`PQ` has the direction `2(B - A)`), not Hilbert's
synthetic one (the midline of the triangle `PCQ`), which he leaves to the reader.

**Status.** proved (reading)
-/

section Fig50

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- If `A` lies between `P` and `C` and `AC ≡ PA`, then `A` is the midpoint: `C = 2A - P`. -/
theorem eq_of_between_segCong {P A C : Coord K 2} (hb : Between P A C) (hs : SegCong A C P A) :
    C = (2 : K) • A - P := by
  rw [AffPt.between_iff, AffPt.sbtw_iff_param] at hb
  obtain ⟨hPC, t, ht0, ht1, rfl⟩ := hb
  rw [segCong_iff] at hs
  have hv : C - P ≠ 0 := sub_ne_zero.2 (Ne.symm hPC)
  have hN := ip_self_pos hv
  have e1 : C - (t • (C - P) + P) = (1 - t) • (C - P) := by
    apply ext2 <;> simp <;> ring
  have e2 : t • (C - P) + P - P = t • (C - P) := by abel
  rw [e1, e2] at hs
  simp only [ip_smul_left, ip_smul_right] at hs
  have ht : t = 1 / 2 := by
    have : (1 - 2 * t) * ip (C - P) (C - P) = 0 := by linear_combination hs
    have := (mul_eq_zero.1 this).resolve_right hN.ne'
    linarith
  subst ht
  apply ext2 <;> simp <;> ring

theorem fig50 {P A B C Q : Coord K 2} (hP : crossProd2 (B - A) (P - A) ≠ 0)
    (hC : Between P A C) (hAC : SegCong A C P A) (hQ : Between C B Q) (hBQ : SegCong B Q C B) :
    Q = P + (2 : K) • (B - A) ∧ P ≠ Q ∧
      ∀ a b : CoordLine K 2, P ∈ a → Q ∈ a → A ∈ b → B ∈ b → Parallel (Point := Coord K 2) a b := by
  have hC' := eq_of_between_segCong hC hAC
  have hQ' := eq_of_between_segCong hQ hBQ
  have hQe : Q = P + (2 : K) • (B - A) := by
    rw [hQ', hC']; apply ext2 <;> simp <;> ring
  have hAB : A ≠ B := by rintro rfl; simp at hP
  have hu := ne_zero_of_ne hAB
  have hPQ : P ≠ Q := by
    intro e
    have : (2 : K) • (B - A) = 0 := by
      rw [show (2 : K) • (B - A) = (P + (2 : K) • (B - A)) - P by abel, ← hQe, ← e, sub_self]
    exact hu ((smul_eq_zero.1 this).resolve_left two_ne_zero)
  refine ⟨hQe, hPQ, fun a b hPa hQa hAb hBb => ?_⟩
  rintro ⟨X, hXa, hXb⟩
  rw [mem_line_iff_cross hPQ hPa hQa, hQe, add_sub_cancel_left] at hXa
  rw [mem_line_iff_cross hAB hAb hBb] at hXb
  obtain ⟨r, hr⟩ := (cross_eq_zero_iff (smul_ne_zero two_ne_zero hu)).1 hXa
  apply hP
  rw [show X - A = (X - P) + (P - A) by abel, cross_add_right, hr, cross_smul_right,
    cross_smul_right, Coord.cross_self, mul_zero, mul_zero, zero_add] at hXb
  exact hXb

end Fig50

/-!
## [s36.fig51] A perpendicular by straight-edge and transferer (Fig. 51)

*(§ 36)*

> We can solve problem 5 in the following manner. Let $A$ be an arbitrary point of the given straight line. Then upon this straight line, lay off in both directions from $A$ the two equal segments $AB$ and $AC$. … Suppose the straight lines $BD$ and $CE$ intersect in $F$ and the straight lines $BE$ and $CD$ intersect in $H$. $FH$ is then the desired perpendicular. In fact, the angles $BDC$ and $BEC$, being inscribed in a semicircle having the diameter $BC$, are both right angles, and, hence, according to the theorem relating to the point of intersection of the altitudes of a triangle, the straight lines $FH$ and $BC$ are perpendicular to each other.

**Lean reading.** In the coordinate plane over an ordered field, with `C = 2A - B` and
`AD ≡ AE ≡ AB`: the angles `BDC`, `BEC` are right (`thales`, inscribed in the semicircle); the
altitudes of a triangle meet in a point (`altitudes`); hence `FH ⊥ BC` (`fig51`). Over a
Pythagorean field, the construction can be carried out with straight-edge and transferer from a
point `P` outside the line (`rt_perp_exists`): `D` on `AP`, `E` on the line through `A` and
`P + 2(B - A)`; the proof shows that the lines `BD`, `CE` and `BE`, `CD` do meet (they are parallel
only if `E` is the reflection of `D` in `A`) and that `F ≠ H` (three distinct points of a circle
are not collinear). Hilbert's "any two straight lines passing through the point `A`" must be two
distinct lines different from `BC`.

**Status.** proved (reading)
-/

section Fig51

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The angle inscribed in a semicircle is right** (Thales): if `A` is the midpoint of `BC` and
`AD ≡ AB`, then `DB ⊥ DC`. -/
theorem thales {A B C D : Coord K 2} (hC : C - A = -(B - A))
    (hD : ip (D - A) (D - A) = ip (B - A) (B - A)) : ip (B - D) (C - D) = 0 := by
  have hc1 : xc C = 2 * xc A - xc B := by have := congrArg xc hC; simp at this; linarith
  have hc2 : yc C = 2 * yc A - yc B := by have := congrArg yc hC; simp at this; linarith
  simp only [ip_two, xc_sub, yc_sub] at hD ⊢
  rw [hc1, hc2]
  linear_combination hD

/-- **The altitudes of a triangle meet in a point**: if `H` lies on the altitudes from `B` and
from `C` of the triangle `BCF`, it lies on the altitude from `F`. -/
theorem altitudes {B C F H : Coord K 2} (hB : ip (H - B) (F - C) = 0)
    (hC : ip (H - C) (F - B) = 0) : ip (F - H) (B - C) = 0 := by
  rw [altitude_identity, hB, hC, sub_zero]

/-- **Fig. 51**: `FH ⊥ BC`. -/
theorem fig51 {A B C D E F H : Coord K 2} (hC : C - A = -(B - A))
    (hD : ip (D - A) (D - A) = ip (B - A) (B - A)) (hE : ip (E - A) (E - A) = ip (B - A) (B - A))
    (hF1 : crossProd2 (D - B) (F - B) = 0) (hF2 : crossProd2 (E - C) (F - C) = 0)
    (hH1 : crossProd2 (E - B) (H - B) = 0) (hH2 : crossProd2 (D - C) (H - C) = 0)
    (hBD : B ≠ D) (hCE : C ≠ E) (hBE : B ≠ E) (hCD : C ≠ D) :
    ip (F - H) (B - C) = 0 := by
  obtain ⟨s, hs⟩ := (cross_eq_zero_iff (ne_zero_of_ne hBD)).1 hF1
  obtain ⟨t, ht⟩ := (cross_eq_zero_iff (ne_zero_of_ne hCE)).1 hF2
  obtain ⟨s', hs'⟩ := (cross_eq_zero_iff (ne_zero_of_ne hBE)).1 hH1
  obtain ⟨t', ht'⟩ := (cross_eq_zero_iff (ne_zero_of_ne hCD)).1 hH2
  have hD' := thales hC hD
  have hE' := thales hC hE
  apply altitudes
  · rw [hs', ht, ip_smul_left, ip_smul_right,
      show ip (E - B) (E - C) = ip (B - E) (C - E) by
        rw [show E - B = -(B - E) by abel, show E - C = -(C - E) by abel, ip_neg_left,
          ip_neg_right, neg_neg], hE', mul_zero, mul_zero]
  · rw [ht', hs, ip_smul_left, ip_smul_right,
      show ip (D - C) (D - B) = ip (B - D) (C - D) by
        rw [show D - C = -(C - D) by abel, show D - B = -(B - D) by abel, ip_neg_left,
          ip_neg_right, neg_neg, ip_comm], hD', mul_zero, mul_zero]

end Fig51

/-!
## [s36.fig52] Problem 4 by parallels and perpendiculars (Fig. 52)

*(§ 36)*

> Moreover, we can easily solve problem 4 simply by the drawing of straight lines and the laying off of segments. … From an arbitrary point $B$ of one side of the angle $\beta$, let fall a perpendicular upon the other side of this angle and also one upon $l$. Denote the feet of these perpendiculars by $D$ and $C$ respectively. … Then, let fall from $A$ a perpendicular upon $CD$, and let its foot be denoted by $E$. According to the demonstration given in Section § 14, the angle $CAE$ equals $\beta$. Consequently, the construction in 4 is made to depend upon that of 1 and 3 and with this our proposition is demonstrated.

**Lean reading.** `fig52`, in the coordinate plane over an ordered field: `β = ∠BAX`, `l = AY`,
`D`, `C`, `E` the feet as described. If `β` is not right, `AB` is not perpendicular to `l` and
`l ≠ AX`, then `C ≠ D`, `E ≠ A`, and `∠CAE ≡ β` **if and only if `β` is acute**. Hilbert's claim
is false for an obtuse `β`: `∠CAE` is then the supplementary angle (`ip (C - A) (E - A) = |AE|² > 0`
always, so `∠CAE` is acute); for a right `β` the construction degenerates (`D = A`, `E = A`), as it
does when `AB ⊥ l` (`C = A`). The correct construction lays off the supplement of an obtuse angle
(or uses `rt_angle_line`). The parallel `l` to the given line plays no role in the angle claim.

**Status.** proved (corrected)
-/

theorem fig52_construction {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A B X Y C D E : Coord K 2} (hβ : ip (B - A) (X - A) ≠ 0)
    (hC0 : ip (B - A) (Y - A) ≠ 0) (hXY : crossProd2 (X - A) (Y - A) ≠ 0)
    (hD : D = (ip (B - A) (X - A) / ip (X - A) (X - A)) • (X - A) + A)
    (hC : C = (ip (B - A) (Y - A) / ip (Y - A) (Y - A)) • (Y - A) + A)
    (hE : E = (ip (A - C) (D - C) / ip (D - C) (D - C)) • (D - C) + C) :
    C ≠ D ∧ E ≠ A ∧ (AngCong C A E B A X ↔ 0 < ip (B - A) (X - A)) :=
  fig52 hβ hC0 hXY hD hC hE

/-- For an obtuse angle `β` (e.g. `∠BAX` with `B = (1,0)`, `X = (-1,1)`) Hilbert's construction
does not give `β`. -/
theorem fig52_obtuse_counterexample :
    let A : Coord ℚ 2 := pt2 0 0
    let B : Coord ℚ 2 := pt2 1 0
    let X : Coord ℚ 2 := pt2 (-1) 1
    let Y : Coord ℚ 2 := pt2 1 2
    let D := (ip (B - A) (X - A) / ip (X - A) (X - A)) • (X - A) + A
    let C := (ip (B - A) (Y - A) / ip (Y - A) (Y - A)) • (Y - A) + A
    let E := (ip (A - C) (D - C) / ip (D - C) (D - C)) • (D - C) + C
    ¬AngCong C A E B A X := by
  intro A B X Y D C E h
  have := (fig52 (A := A) (B := B) (X := X) (Y := Y) (C := C) (D := D) (E := E)
    (by simp [A, B, X, ip_two]) (by simp [A, B, Y, ip_two])
    (by simp [A, X, Y, crossProd2_def]; norm_num) rfl rfl rfl).2.2.1 h
  norm_num [A, B, X, ip_two] at this

/-!
## [s37.frame] Coordinates and the domains `R` and `Ω(R)`

*(§ 37)*

> In order to get a general survey of the scope of the problems which may be solved in this manner, let us take as the basis of our consideration a system of axes in rectangular co-ordinates and suppose that the co-ordinates of the points are, as usual, represented by real numbers or by functions of certain arbitrary parameters. … Let a system of definite points be given. Combine the co-ordinates of these points into a domain $R$. … Consider, now, the totality of points capable of construction by the drawing of straight lines and the laying off of definite segments, making use of the system of points in question. We will call the domain formed from the co-ordinates of these points $\Omega(R)$, which will then contain real numbers and functions of the arbitrary parameters $p$.

**Lean reading.** The plane is `Coord K 2` over an ordered field `K`: `K = ℝ`, or a field of
functions of parameters (only the field operations and the order are used). The system of axes is
given by the frame `(0,0)`, `(1,0)`, `(0,1)` (`frameSet K`): an origin, the unit and the two axes.
`coordSet S` is the set of coordinates of the given points (Hilbert's `R` is the field they
generate). Hilbert defines `Ω(R)` as the set of coordinates of the constructible points and then
shows that it is the closure of `R` under the five operations; here `PythClosure (coordSet S)` is
that closure, and Theorem 41 proves the identity (with the frame among the given points).

**Status.** definition
-/

theorem frameSet_mem {K : Type*} [Field K] :
    (pt2 0 0 : Coord K 2) ∈ frameSet K ∧ (pt2 1 0 : Coord K 2) ∈ frameSet K ∧
      (pt2 0 1 : Coord K 2) ∈ frameSet K := by
  simp [frameSet]

/-!
## [s37.rational_operations] Straight lines and laying off segments analytically

*(§ 37)*

> The discussion in § 17 shows that the drawing of straight lines and of parallels amounts, analytically, to the addition, subtraction, multiplication, and division of segments. Furthermore, the well known formula given in § 9 for a rotation shows that the laying off of segments upon a straight line does not necessitate any other analytical operation than the extraction of the square root of the sum of the squares of two segments whose bases have been previously constructed.

**Lean reading.** The common point of two lines through given points has coordinates obtained by
the four operations (`meet_param`: `X = A + r (B - A)` with `r` a quotient of cross products); a
point laid off from `O` on `OQ` at the distance `|AB|` is `O + t (Q - O)` with
`|t| |Q - O|² = √(⟪Q - O, B - A⟫² + ((Q - O) × (B - A))²)` (the square root of a sum of two
squares). Together (`rt_coords_mem`): the coordinates of every point constructible by
straight-edge and transferer lie in `Ω(R)`. No frame and no square roots in `K` are needed.

**Status.** proved
-/

theorem rational_operations {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set (Coord K 2)} {X : Coord K 2} (h : RulerTransferer S X) :
    PythClosure (coordSet S) (xc X) ∧ PythClosure (coordSet S) (yc X) :=
  rt_coords_mem h

/-!
## [s37.pythagoras] The square root of a sum of two squares by laying off

*(§ 37)*

> Conversely, in consequence of the pythagorean theorem, we can always construct, by the aid of a right triangle, the square root of the sum of the squares of two segments by the mere laying off of segments.

**Lean reading.** With the frame among the given points: if `(x, 0)` and `(y, 0)` are constructible,
so is `(√(x² + y²), 0)`: construct `(x, y)` with two parallels to the axes and lay off the
hypotenuse `O(x, y)` on the axis (`pythagoras_construction`, from `rt_axis_sqrt`).

**Status.** proved
-/

theorem pythagoras_construction {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set (Coord K 2)} (hF : frameSet K ⊆ S) {x y z : K}
    (hx : RulerTransferer S (pt2 x 0)) (hy : RulerTransferer S (pt2 y 0)) (hz : 0 ≤ z)
    (hzz : z ^ 2 = x ^ 2 + y ^ 2) : RulerTransferer S (pt2 z 0) :=
  rt_axis_sqrt (hF frameSet_mem.1) (hF frameSet_mem.2.1) (hF frameSet_mem.2.2) hx hy hz hzz

/-!
## [s37.domain] The domain `Ω(R)`

*(§ 37)*

> From these considerations, it follows that the domain $\Omega(R)$ contains all of those and only those real numbers and functions of the parameters $p$, which arise from the numbers and parameters in $R$ by means of a finite number of applications of the five operations; viz., the four elementary operations of arithmetic and, in addition, the fifth operation of extracting the square root of the sum of two squares.

**Lean reading.** Hilbert's `Ω(R)` is the domain of the coordinates of the constructible points.
`domain_coords`: when the frame is among the given points, a number is a coordinate of a point
constructible by straight-edge and transferer iff it lies in the closure `PythClosure (coordSet S)`
of the coordinates of the given points under the five operations; `domain_eq`: iff `(x, 0)` is
constructible. The "only those" half holds for any given points (`rational_operations`); the "all
of those" half needs the unit of length among the data (unit `th.41`: from `(0,0)`, `(c,0)`,
`(0,c)` the number `1 = c/c` is obtained by the five operations but is not a coordinate of a
constructible point when `1/c ∉ Ω`).

**Status.** proved (corrected)
-/

theorem domain_eq {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set (Coord K 2)} (hF : frameSet K ⊆ S) (x : K) :
    RulerTransferer S (pt2 x 0) ↔ PythClosure (coordSet S) x := by
  rw [theorem41_coord (hF frameSet_mem.1) (hF frameSet_mem.2.1) (hF frameSet_mem.2.2)]
  simp only [xc_pt2, yc_pt2]
  exact ⟨fun h => h.1, fun h => ⟨h, .base ⟨pt2 0 0, hF frameSet_mem.1, Or.inl (by simp)⟩⟩⟩

theorem domain_coords {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set (Coord K 2)} (hF : frameSet K ⊆ S) (x : K) :
    (∃ X : Coord K 2, RulerTransferer S X ∧ (x = xc X ∨ x = yc X)) ↔
      PythClosure (coordSet S) x := by
  constructor
  · rintro ⟨X, hX, rfl | rfl⟩
    · exact (rational_operations hX).1
    · exact (rational_operations hX).2
  · intro h
    exact ⟨pt2 x 0, (domain_eq hF x).2 h, Or.inl (by simp)⟩

/-!
## [th.41] Theorem 41

*(§ 37)*

> A problem in geometrical construction is, then, possible of solution by the drawing of straight lines and the laying off of segments, that is to say, by the use of the straight-edge and a transferer of segments, when and only when, by the analytical solution of the problem, the co-ordinates of the desired points are such functions of the co-ordinates of the given points as may be determined by the rational operations and, in addition, the extraction of the square root of the sum of two squares.

**Lean reading.** `theorem41`: in the coordinate plane over any ordered field, if the frame
`(0,0)`, `(1,0)`, `(0,1)` (Hilbert's "system of axes", with its unit segment) is among the given
points, a point is constructible by straight-edge and transferer iff its coordinates lie in
`Ω(R) = PythClosure (coordSet S)`. The "only if" half holds for any given points. **As printed,
without the frame, the "if" half is false** (`theorem41_needs_frame`): from the given points
`(0,0)`, `(c,0)`, `(0,c)` with `1/c ∉ Ω` (such `c` exist since `Ω` is countable), the point
`(1, 0)` has coordinates `1 = c/c` and `0` in `Ω(R)` but is not constructible, since every
construction commutes with the similarity `X ↦ X/c` (`rt_closed`). The unit of length must be
among the data.

**Status.** proved (corrected)
-/

theorem theorem41 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {S : Set (Coord K 2)} (hF : frameSet K ⊆ S) (X : Coord K 2) :
    RulerTransferer S X ↔
      PythClosure (coordSet S) (xc X) ∧ PythClosure (coordSet S) (yc X) :=
  theorem41_coord (hF frameSet_mem.1) (hF frameSet_mem.2.1) (hF frameSet_mem.2.2)

theorem theorem41_as_printed_false :
    ∃ c : ℝ, c ≠ 0 ∧ PythClosure (coordSet ({pt2 0 0, pt2 c 0, pt2 0 c} : Set (Coord ℝ 2))) 1 ∧
      PythClosure (coordSet ({pt2 0 0, pt2 c 0, pt2 0 c} : Set (Coord ℝ 2))) 0 ∧
      ¬RulerTransferer ({pt2 0 0, pt2 c 0, pt2 0 c} : Set (Coord ℝ 2)) (pt2 1 0) :=
  theorem41_needs_frame

/-!
## [s37.compass] Not every compass construction is a straight-edge and transferer construction

*(§ 37)*

> From this proposition, we can at once show that not every problem which can be solved by the use of a compass can also be solved by the aid of a transferer of segments and a straight-edge.

**Lean reading.** `compass_not_rt`: in the real plane, there is a point `C` (the vertex of the
right triangle of unit `s37.right_triangle`) that is not constructible by straight-edge and
transferer from the frame, although it is an intersection of two circles whose data are so
constructible: the circle on the diameter from `(0,0)` to `(1,0)` and the circle about `(0,0)`
through the constructible point `(√2 - 1, 0)`. The compass itself is not formalized as an
instrument; one intersection of two circles with constructible data is what it adds.

**Status.** proved
-/

theorem compass_not_rt : RulerTransferer (frameSet ℝ) (pt2 (Real.sqrt 2 - 1) 0) ∧
    ∃ C : Coord ℝ 2, ip (pt2 0 0 - C) (pt2 1 0 - C) = 0 ∧
      ip (C - pt2 0 0) (C - pt2 0 0) = ip (pt2 (Real.sqrt 2 - 1) 0 - pt2 0 0)
        (pt2 (Real.sqrt 2 - 1) 0 - pt2 0 0) ∧ ¬RulerTransferer (frameSet ℝ) C := by
  obtain ⟨⟨C, h1, h2⟩, h3⟩ := right_triangle_example
  refine ⟨rt_frame_iff_omega.2 ?_, C, h1, ?_, h3 C h1 h2⟩
  · simp only [xc_pt2, yc_pt2]
    exact ⟨Omega.sub_mem sqrt_two_mem Omega.one_mem, Omega.zero_mem⟩
  · rw [h2]; simp [ip_two]; ring

/-!
## [s37.omega_geometry] The geometry over `Ω`

*(§ 37)*

> For the purpose of showing this, let us consider again that geometry which was constructed in § 9 by the help of the domain $\Omega$ of algebraic numbers. In this geometry, there exist only such segments as can be constructed by means of a straight-edge and a transferer of segments, namely, the segments determined by the numbers of the domain $\Omega$.

**Lean reading.** `Ω(ℚ) = Ω`: the closure of the coordinates `0, 1` of the frame under the five
operations is Hilbert's field `Ω` (`pythClosure_frame_iff`), so the points of the real plane
constructible from the frame are exactly the points of the geometry over `Ω`
(`omega_geometry`).

**Status.** proved
-/

theorem omega_geometry (X : Coord ℝ 2) :
    RulerTransferer (frameSet ℝ) X ↔ xc X ∈ Omega ∧ yc X ∈ Omega :=
  rt_frame_iff_omega

/-!
## [s37.conjugates] The conjugates of the numbers of `Ω`

*(§ 37)*

> Now, if $\omega$ is a number of the domain $\Omega$, we easily see from the definition of $\Omega$ that every algebraic number conjugate to $\omega$ must also lie in $\Omega$. Since the numbers of the domain $\Omega$ are evidently all real, it follows that it can contain only such real algebraic numbers as have their conjugates also real.

**Lean reading.** `conjugates_mem_omega`: for `ω ∈ Ω`, every complex root of the minimal
polynomial of `ω` over `ℚ` is a real number of `Ω`. Hilbert's "easily see" is an induction on the
construction of `ω`: every embedding of a subfield of `ℝ` into `ℂ` extends along the construction
of `ω` (adjoining `√(1 + w²)` step by step, `exists_ext`) and maps `ω` to `±`-variants of its
construction, which are again real numbers of `Ω` (`omega_ext`); a conjugate of `ω` is the image of
`ω` under an embedding of `ℚ(ω)`.

**Status.** proved
-/

theorem conjugates_mem_omega {ω : ℝ} (hω : ω ∈ Omega) {z : ℂ}
    (hz : aeval z (minpoly ℚ ω) = 0) : ∃ r ∈ Omega, z = (r : ℂ) :=
  omega_conj hω hz

/-!
## [s37.right_triangle] A right triangle not constructible by straight-edge and transferer

*(§ 37)*

> Let us now consider the following problem; viz., to construct a right triangle having the hypotenuse 1 and one side $|\sqrt{2}| - 1$. The algebraic number $\sqrt{2|\sqrt{2}| - 2}$, which expresses the numerical value of the other side, does not occur in the domain $\Omega$, since the conjugate number $\sqrt{-2|\sqrt{2}| - 2}$ is imaginary. This problem is, therefore, not capable of solution in the geometry in question and, hence, cannot be constructed by means of a straight-edge and a transferer of segments, although the solution by means of a compass is possible.

**Lean reading.** `sqrt_two_sqrt_two_sub_two_not_mem`: `√(2√2 - 2) ∉ Ω` — an embedding of `ℚ(√2)`
sending `√2` to `-√2` would send it to a square root of `-2√2 - 2 < 0`. `right_triangle`: with
`A = (0,0)`, `B = (1,0)`, there is a point `C` of the real plane with a right angle at `C` and
`AC = √2 - 1` (the intersection of the circle on the diameter `AB` with the circle about `A`), but
no such point is constructible by straight-edge and transferer from the frame (then
`BC = √(2√2 - 2)` would lie in `Ω`). `right_triangle_not_in_omega_plane`: the problem has no
solution in the plane over `Ω` itself.

**Status.** proved
-/

theorem right_triangle :
    (∃ C : Coord ℝ 2, ip (pt2 0 0 - C) (pt2 1 0 - C) = 0 ∧
        ip (C - pt2 0 0) (C - pt2 0 0) = (Real.sqrt 2 - 1) ^ 2) ∧
      ∀ C : Coord ℝ 2, ip (pt2 0 0 - C) (pt2 1 0 - C) = 0 →
        ip (C - pt2 0 0) (C - pt2 0 0) = (Real.sqrt 2 - 1) ^ 2 →
        ¬RulerTransferer (frameSet ℝ) C :=
  right_triangle_example

theorem right_triangle_not_in_omega_plane :
    ¬∃ C : Coord OmegaField 2, ip (pt2 0 0 - C) (pt2 1 0 - C) = 0 ∧
      ip (C - pt2 0 0) (C - pt2 0 0) = ((⟨Real.sqrt 2, sqrt_two_mem⟩ : OmegaField) - 1) ^ 2 := by
  rintro ⟨C, h1, h2⟩
  simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2] at h1 h2
  have h1' := congrArg Subtype.val h1
  have h2' := congrArg Subtype.val h2
  push_cast at h1' h2'
  set x : ℝ := ((xc C : OmegaField) : ℝ)
  set y : ℝ := ((yc C : OmegaField) : ℝ)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hBC : (1 - x) ^ 2 + (0 - y) ^ 2 = 2 * Real.sqrt 2 - 2 := by nlinarith
  have hm := Omega.sqrt_sq_add_sq_mem (Omega.sub_mem Omega.one_mem (xc C).2)
    (Omega.sub_mem Omega.zero_mem (yc C).2)
  rw [hBC] at hm
  exact sqrt_two_sqrt_two_sub_two_not_mem hm

/-!
## [s38.fermat] Every positive integer is a sum of four squares

*(§ 38)*

> Since the time of Fermat, it has been known that every positive integral rational number can be represented as the sum of four squares.

**Lean reading.** Lagrange's four-square theorem (stated by Fermat, proved by Lagrange in 1770),
from mathlib (`fermat_four_squares`), and its consequence for nonnegative rational numbers
(`rat_sum_four_sq`).

**Status.** proved
-/

theorem fermat_four_squares (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

theorem rat_four_squares {q : ℚ} (hq : 0 ≤ q) :
    ∃ a b c d : ℚ, q = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 :=
  rat_sum_four_sq hq

/-!
## [s38.totally_positive] Totally positive numbers

*(§ 38)*

> Definition. Let $k$ be an arbitrary number field and let $m$ be its degree. We will denote by $k^{\prime}$, $k^{\prime\prime}$, \ldots, $k^{(m-1)}$ the $m-1$ number fields conjugate to $k$. If, among the $m$ fields $k$, $k^{\prime}, k^{\prime\prime}, \ldots, k^{(m-1)}$ there is one or more formed entirely of real numbers, then we call these fields real. … A number $\alpha$ of the field $k$ is called in this case totally positive in $k$, whenever the $s$ numbers conjugate to $\alpha$, contained respectively in $k$, $k^\prime$, $k^{\prime\prime}$, \ldots, $k^{(s-1)}$ are all positive. However, if in each of the $m$ fields $k$, $k^\prime$, $k^{\prime\prime}$, \ldots, $k^{(m-1)}$ there are also imaginary numbers present, we call every number $\alpha$ in $k$ totally positive.

**Lean reading.** `k` is a number field (`[NumberField k]`); the conjugate fields are the images
of the embeddings `σ : k →+* ℂ`, real when `σ` takes only real values. `TotallyPositive α`: `σ α` is
a positive real number for every real embedding `σ`. When there is no real embedding the condition
is vacuous, which is exactly Hilbert's second clause (`totallyPositive_of_no_real`).

**Status.** definition
-/

theorem totallyPositive_of_no_real {k : Type*} [Field k]
    (h : ∀ σ : k →+* ℂ, ∃ x : k, (σ x).im ≠ 0) (α : k) : TotallyPositive α :=
  fun σ hσ => absurd (hσ (h σ).choose) (h σ).choose_spec

/-!
## [th.42] Theorem 42

*(§ 38)*

> Every totally positive number in $k$ may be represented as the sum of four squares, whose bases are integral or fractional numbers of the field $k$.

**Lean reading.** `Theorem42`: for every number field `k` and every totally positive `α ∈ k`, there
are `a, b, c, d ∈ k` with `α = a² + b² + c² + d²`. Hilbert's proof rests on his theory of relatively
quadratic fields (the solvability of `αξ² + βη² + γζ² = 0`, i.e. the Hasse principle for ternary
forms) and is only sketched; the theorem was proved by Siegel (1921). That is far beyond this
project. Proved here: the case `k = ℚ` (`theorem42_rat`, from Lagrange's theorem), every field
containing `√-1` (`theorem42_of_sq_eq_neg_one`: `α = ((α+1)/2)² + (i(α-1)/2)²`), and the converse
(a nonzero sum of four squares is totally positive, `totallyPositive_of_sum_sq`). The use Hilbert
makes of it in Theorem 43 is formalized as `negOneSumSq_of_theorem42`.

**Status.** stated (open here)
-/

theorem theorem42_for_rat (α : ℚ) (h : TotallyPositive α) :
    ∃ a b c d : ℚ, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 :=
  theorem42_rat α h

/-!
## [s38.ternary] The ternary diophantine equation

*(§ 38)*

> The demonstration of this theorem presents serious difficulty. It depends essentially upon the theory of relatively quadratic number fields, which I have recently developed in several papers. … We will here call attention only to that proposition in this theory which gives the condition that a ternary diophantine equation of the form \[ \alpha\xi^2 + \beta\eta^2 + \gamma\zeta^2 = 0 \] can be solved when the coefficients $\alpha$, $\beta$, $\gamma$ are given numbers in $k$ and $\xi$, $\eta$, $\zeta$ are the required numbers in $k$. The demonstration of theorem 42 is accomplished by the repeated application of the proposition just mentioned.

**Lean reading.** Hilbert names the proposition (the norm-residue criterion for the solvability
of a ternary quadratic equation, i.e. the Hasse principle) without stating it; there is no
statement to formalize. It is not used elsewhere here.

**Status.** remark
-/

/-!
## [th.43] Theorem 43

*(§ 38)*

> Let, $f(x)$ be an integral rational function of $x$ whose coefficients are rational numbers and which never becomes negative for any real value of $x$. Then $f(x)$ can always be represented as the quotient of two sums of squares of which the bases are all integral rational functions of $x$ with rational coefficients.

**Lean reading.** `Theorem43`: for every `f ∈ ℚ[x]` with `f(x) ≥ 0` for all real `x` (`PSD f`),
there are sums of squares `N`, `D ≠ 0` in `ℚ[x]` with `f · D = N` (`RepQSOS f`). **Hilbert's proof
is formalized in full** (`theorem42_imp_theorem43`): by induction on the degree, with the
reducible case (an irreducible factor with a real root divides `f` twice, units
`s38.factor_cases`) and the irreducible case (`-1` is a sum of four squares in `ℚ(θ)` by
Theorem 42, unit `s38.reduction`). Theorem 43 itself is true (Landau 1906: a definite polynomial
over `ℚ` is even a sum of eight squares; Pourchet: five), but both proofs need arithmetic beyond
this project, and Theorem 42 is open here; so Theorem 43 is proved only conditionally, and
unconditionally for degree `≤ 2` (`theorem43_natDegree_le_two`: `4a f = (2ax + b)² + (4ac - b²)`).

**Status.** stated (open here)
-/

theorem theorem43_from_theorem42 (h42 : Theorem42) : Theorem43 :=
  theorem42_imp_theorem43 h42

theorem theorem43_degree_le_two {f : ℚ[X]} (hf : PSD f) (hd : f.natDegree ≤ 2) : RepQSOS f :=
  theorem43_natDegree_le_two hf hd

/-!
## [s38.even_degree] A definite polynomial has even degree

*(§ 38)*

> Proof. We will denote the degree of the function $f(x)$ by $m$, which, in any case, must evidently be even.

**Lean reading.** `psd_even_degree`: a nonzero polynomial with rational coefficients that is
nonnegative on `ℝ` has even degree (an odd degree polynomial tends to `-∞` on one side). The
zero polynomial is excluded (Hilbert tacitly assumes `f ≠ 0`).

**Status.** proved
-/

theorem psd_even_degree {f : ℚ[X]} (hf : PSD f) (hf0 : f ≠ 0) : Even f.natDegree :=
  psd_even_natDegree hf hf0

/-!
## [s38.constant_case] Theorem 43 for constants

*(§ 38)*

> When $m = 0$, that is to say, when $f(x)$ is a rational number, the validity of theorem 43 follows immediately from Fermat's theorem concerning the representation of a positive number as the sum of four squares.

**Lean reading.** `theorem43_constant`: a nonnegative rational constant is a sum of four squares of
rational constants (from Lagrange's theorem for `num · den`), hence `RepQSOS` with denominator `1`.

**Status.** proved
-/

theorem theorem43_constant {q : ℚ} (hq : 0 ≤ q) : RepQSOS (C q) :=
  ⟨C q, 1, isSumSq_C hq, by simp, one_ne_zero, mul_one _⟩

/-!
## [s38.factor_cases] The irreducible factors of a definite polynomial

*(§ 38)*

> Suppose $p(x)$ to be one of those functions contained in $f(x)$, which itself cannot be further decomposed into a product of integral functions having rational coefficients. It then follows at once from the “definite” character which we have given to the function $f(x)$, that the factor $p(x)$ must either appear in $f(x)$ to an even degree or $p(x)$ must be itself “definite”; that is to say, must be a function which never has negative values for any real values of $x$. In the first case, the quotient $\frac{f(x)}{\{p(x)\}^2}$ and, in the second case, both $p(x)$ and $\frac{f(x)}{p(x)}$, are “definite,” …

**Lean reading.** For `p` irreducible dividing a definite `f`: if `p` has a real root, it appears
in `f` to an even power — `p^(2k+1) ∣ f` implies `p^(2k+2) ∣ f` (`factor_even_power`; the root is a
minimum of `f`, so `f'` vanishes there while `p'` does not, `p` being separable) — and `f/p²` is
definite (`psd_of_sq_mul`, by continuity off the finitely many roots); otherwise `p` or `-p` is
positive on `ℝ` (`definite_sign`, intermediate value theorem) and then `f/p` is definite. "Even
degree" is read as "even multiplicity"; "`p` definite" is up to the sign of `p`, which Hilbert leaves
tacit.

**Status.** proved
-/

theorem factor_even_power {f p : ℚ[X]} (hf : PSD f) (hp : Irreducible p) {r : ℝ}
    (hr : aeval r p = 0) : ∀ k : ℕ, p ^ (2 * k + 1) ∣ f → p ^ (2 * k + 2) ∣ f := by
  intro k ⟨g, hg⟩
  have hp0 := hp.ne_zero
  have hpg : PSD (p * g) := by
    have e : f = (p ^ k) ^ 2 * (p * g) := by rw [hg]; ring
    exact psd_of_sq_mul (pow_ne_zero k hp0) (e ▸ hf)
  obtain ⟨g', hg'⟩ := sq_dvd_of_real_root hpg hp (dvd_mul_right p g) hr
  have hgg : g = p * g' := by
    have : p * g = p * (p * g') := by rw [hg']; ring
    exact mul_left_cancel₀ hp0 this
  exact ⟨g', by rw [hg, hgg]; ring⟩

theorem factor_definite {p : ℚ[X]} (h : ∀ x : ℝ, aeval x p ≠ 0) :
    (∀ x : ℝ, 0 < aeval x p) ∨ ∀ x : ℝ, aeval x p < 0 :=
  definite_sign h

theorem factor_quotient_sq {p g : ℚ[X]} (hp : p ≠ 0) (hf : PSD (p ^ 2 * g)) : PSD g :=
  psd_of_sq_mul hp hf

/-!
## [s38.reduction] The irreducible case: reduction of the degree

*(§ 38)*

> Let us now consider the case where $f(x)$ cannot be broken up into the product of two integral functions having rational coefficients. The equation $f(\theta)=0$ defines, then, a field of algebraic numbers $k(\theta)$ of the $m^\text{th}$ degree, which, together with all their conjugate fields, are imaginary. Since, according to the definition given just before the statement of theorem 42, each number given in $k(\theta)$, and hence also $-1$ is totally positive in $k(\theta)$, it follows from theorem 42 that the number $-1$ can be represented as a sum of the squares of four definite numbers in $k(\theta)$. … $F(x)$ is, then, a “definite” function of the degree $(2m-2)$ or lower. Hence, the quotient $\frac{F(x)}{f(x)}$ is a “definite” function of the degree $(m-2)$ or lower in $x$, having rational coefficients. Consequently, by the hypothesis we have made, $\frac{F(x)}{f(x)}$ can be represented as the quotient of two sums of squares of the kind mentioned in theorem 43 and, since $F(x)$ is itself such a sum of squares, it follows that, $f(x)$ must also be a quotient of two sums of squares of the required kind. The validity of theorem 43 is accordingly established.

**Lean reading.** `imaginary_field`: for `f` irreducible without real roots, `ℚ[x]/(f)` is a number
field none of whose embeddings into `ℂ` is real, so `-1` is totally positive in it;
`negOneSumSq_of_theorem42`: Theorem 42 then gives `-1 = α² + β² + γ² + δ²`. `irreducible_step`
(Hilbert's argument): with `φ, ψ, χ, ρ` the representatives of degree `< m`,
`F = 1 + φ² + ψ² + χ² + ρ²` is divisible by `f`, `F/f` is definite of degree `≤ m - 2`, and
`f = F / (F/f)`. Two misprints in the text: the fourth line of the display reads `θ = d₁θ^{m-1} + …`
for `δ = …`, and `F(x)` is written with `φ(θ)`, … for `φ(x)`, …. An irreducible definite `f` has no
real root (a real root would be a double root, `factor_even_power`).

**Status.** proved
-/

theorem imaginary_field {p : ℚ[X]} (hroot : ∀ x : ℝ, aeval x p ≠ 0) (σ : AdjoinRoot p →+* ℂ) :
    ∃ x : AdjoinRoot p, (σ x).im ≠ 0 := by
  by_contra hc
  push Not at hc
  set z := σ (AdjoinRoot.root p)
  have hz : aeval z p = 0 := by
    have h1 : σ (eval₂ (AdjoinRoot.of p) (AdjoinRoot.root p) p) = 0 := by
      rw [AdjoinRoot.eval₂_root, map_zero]
    rw [hom_eval₂] at h1
    have h2 : σ.comp (AdjoinRoot.of p) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
    rw [h2] at h1
    rw [aeval_def]; exact h1
  have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [z, hc])
  apply hroot z.re
  have : aeval ((z.re : ℝ) : ℂ) p = 0 := by rw [← hzr]; exact hz
  rw [show ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re from rfl, aeval_algebraMap_apply] at this
  exact (map_eq_zero _).1 this

theorem irreducible_definite_no_root {p : ℚ[X]} (hp : Irreducible p) (hf : PSD p) :
    ∀ x : ℝ, aeval x p ≠ 0 := by
  intro r hr
  obtain ⟨g, hg⟩ := factor_even_power hf hp hr 0 (by simp)
  have hp0 := hp.ne_zero
  have : p * 1 = p * (p * g) := by rw [mul_one]; nth_rewrite 1 [hg]; ring
  have h1 := mul_left_cancel₀ hp0 this
  exact hp.not_isUnit (IsUnit.of_mul_eq_one g h1.symm)

theorem irreducible_step (hyp : NegOneSumSq) {p : ℚ[X]} (hp : Irreducible p)
    (hpos : ∀ x : ℝ, 0 < aeval x p)
    (ih : ∀ g : ℚ[X], g.natDegree < p.natDegree → PSD g → RepQSOS g) : RepQSOS p :=
  rep_irreducible_pos hyp hp hpos ih

theorem negOneSumSq_from_theorem42 (h42 : Theorem42) : NegOneSumSq :=
  negOneSumSq_of_theorem42 h42

/-!
## [s38.two_variables] Definite functions of two variables

*(§ 38)*

> It would be perhaps difficult to formulate and to demonstrate the corresponding proposition for integral functions of two or more variables. However, I will here merely remark that I have demonstrated in an entirely different manner the possibility of representing any “definite” integral rational function of two variables as the quotient of sums of squares of integral functions, upon the hypothesis that the functions represented may have as coefficients not only rational but *any* real numbers.

**Lean reading.** `TwoVariableClaim`: every polynomial `f ∈ ℝ[x, y]` with `f ≥ 0` on `ℝ²` is a
quotient `N / D` of sums of squares in `ℝ[x, y]` (`f · D = N`, `D ≠ 0`). This is Hilbert's theorem of
1893 (Acta Math. 17); its proof (via ternary quartic forms) is far beyond this project. Only the
trivial converse is proved: such a quotient is nonnegative wherever `D` does not vanish
(`TwoVariableClaim_converse`).

**Status.** stated (open here)
-/

/-- Hilbert's theorem on definite polynomials in two variables (1893). -/
def TwoVariableClaim : Prop :=
  ∀ f : MvPolynomial (Fin 2) ℝ, (∀ x : Fin 2 → ℝ, 0 ≤ MvPolynomial.eval x f) →
    ∃ N D : MvPolynomial (Fin 2) ℝ, IsSumSq N ∧ IsSumSq D ∧ D ≠ 0 ∧ f * D = N

theorem isSumSq_eval_nonneg {s : MvPolynomial (Fin 2) ℝ} (hs : IsSumSq s) (x : Fin 2 → ℝ) :
    0 ≤ MvPolynomial.eval x s := by
  induction hs with
  | zero => simp
  | sq_add a _ ih => rw [map_add, map_mul]; nlinarith [mul_self_nonneg (MvPolynomial.eval x a)]

theorem TwoVariableClaim_converse {f N D : MvPolynomial (Fin 2) ℝ} (hN : IsSumSq N)
    (hD : IsSumSq D) (h : f * D = N) (x : Fin 2 → ℝ) (hx : MvPolynomial.eval x D ≠ 0) :
    0 ≤ MvPolynomial.eval x f := by
  have hN' := isSumSq_eval_nonneg hN x
  have hD' := isSumSq_eval_nonneg hD x
  have hDpos : 0 < MvPolynomial.eval x D := lt_of_le_of_ne hD' (Ne.symm hx)
  have := congrArg (MvPolynomial.eval x) h
  rw [map_mul] at this
  by_contra hneg; push Not at hneg
  nlinarith

/-!
## [th.44] Theorem 44

*(§ 39)*

> Suppose we have given a problem in geometrical construction, which is of such a character that the analytical treatment of it enables us to determine uniquely the co-ordinates of the desired points from the co-ordinates of the given points by means of the rational operations and the extraction of the square root. Let $n$ be the smallest number of square roots which suffice to calculate the co-ordinates of the points. Then, in order that the required construction shall be possible by the drawing of straight lines and the laying off of segments, it is necessary and sufficient that the given geometrical problem shall have exactly $2^n$ real solutions for every position of the given points; that is to say, for all values of the arbitrary parameter expressed in terms of the co-ordinates of the given points.

**Lean reading.** The computation is a tower of square roots over the domain `R` generated by the
coordinates of the given points: radicands `a₁ ∈ R`, `a₂ ∈ R(√a₁)`, … (`towerFieldOver R`,
`ValidTowerOver R`). "Exactly `2^n` real solutions for every position of the given points" is
read as: for every embedding of the tower field into `ℂ` that is real on `R` — i.e. for all real
values of the parameters (the transcendental generators of `R`) and either sign of each square
root — every radicand is a nonnegative real number (`RealTowerOver R`). The construction is
possible iff all numbers of the tower lie in `Ω(R)` (Theorem 41). `Theorem44`: for every `R`
generated by finitely many real numbers, the two conditions are equivalent. Proved here: the
necessity for every `R`, any number of parameters (`condition_necessary`, unit `s39.necessary`),
and the case **without parameters**, `R = ℚ`, in both directions
(`theorem44_without_parameters`): sufficiency by Hilbert's argument (with the trace and norm of a
totally nonnegative number, units `s39.quadratic`, `s39.remark`), where for `R = ℚ` Lagrange's
theorem replaces Theorem 43. Hilbert's sufficiency argument is formalized for **every** domain `R`
as a reduction (`theorem44For_of_theorem43For`, `theorem44_from_theorem43For`): Theorem 44 for `R`
follows from `Theorem43For R` — every number of `R` that is nonnegative for all real values of the
parameters is a quotient of two sums of squares in `R` — which for `R = ℚ` is Lagrange's theorem
(`theorem43For_rat`). For one parameter, `Theorem43For ℚ(p)` is Theorem 43 for rational functions
(open here, unit `th.43`); for several parameters it is Hilbert's seventeenth problem (Artin 1927),
which Hilbert himself leaves open (unit `s39.general_case`). So the sufficiency with parameters
remains open here. The minimality of `n` is not needed in the statement: for a minimal `n` the
tower field is the field generated over `R` by the coordinates of the desired points (degree
`2^n`), so "all numbers of the tower lie in `Ω(R)`" is "the desired points are constructible".

**Status.** stated (open here)
-/

theorem theorem44_def : Theorem44 = ∀ S : Finset ℝ, Theorem44For (Subfield.closure (S : Set ℝ)) :=
  rfl

theorem ratField_eq_closure_empty : ratField = Subfield.closure (∅ : Set ℝ) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨q, rfl⟩ := mem_ratField.1 hx
    exact SubfieldClass.ratCast_mem _ q
  · rw [Subfield.closure_le]; exact Set.empty_subset _

theorem towerFieldOver_rat (l : List ℝ) : towerFieldOver ratField l = towerField l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [towerFieldOver, towerField, ih]

theorem validTowerOver_rat (l : List ℝ) : ValidTowerOver ratField l ↔ ValidTower l := by
  induction l with
  | nil => exact Iff.rfl
  | cons a l ih => simp only [ValidTowerOver, ValidTower, ih, towerFieldOver_rat]

theorem realTowerOver_rat (l : List ℝ) : RealTowerOver ratField l ↔ RealTower l := by
  induction l with
  | nil => exact Iff.rfl
  | cons a l ih =>
    simp only [RealTowerOver, RealTower, ih]
    rw [towerFieldOver_rat]
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun σ => h σ fun y hy => ?_⟩
      obtain ⟨q, hq⟩ := mem_ratField.1 hy
      have : y = (q : towerField l) := Subtype.ext (by rw [← hq]; simp)
      exact ⟨q, by rw [this, map_ratCast]; simp⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, fun σ _ => h σ⟩

theorem pythClosure_rat_iff {x : ℝ} : PythClosure (ratField : Set ℝ) x ↔ x ∈ Omega := by
  constructor
  · intro h
    refine PythClosure.le_of_closed omega_closed ?_ h
    intro y hy
    obtain ⟨q, rfl⟩ := mem_ratField.1 hy
    exact SubfieldClass.ratCast_mem Omega q
  · intro h
    have h1 : PythClosure (ratField : Set ℝ) 1 := .base ratField.one_mem
    induction h with
    | one => exact h1
    | add _ _ ha hb => exact .add ha hb
    | sub _ _ ha hb => exact .sub ha hb
    | mul _ _ ha hb => exact .mul ha hb
    | div _ _ hb0 ha hb => exact .div ha hb hb0
    | @sqrt w _ hw =>
      exact .sqrt h1 hw (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt (by positivity)]; ring)

/-- Hilbert's reduction: Theorem 44 follows from the generalization of Theorem 43 to every
domain. -/
theorem theorem44_from_theorem43For
    (h : ∀ S : Finset ℝ, Theorem43For (Subfield.closure (S : Set ℝ))) : Theorem44 :=
  theorem44_of_theorem43For h

/-- **Theorem 44 without parameters** (`R = ℚ`). -/
theorem theorem44_without_parameters : Theorem44For (Subfield.closure (∅ : Set ℝ)) := by
  rw [← ratField_eq_closure_empty]
  intro l hl
  rw [validTowerOver_rat] at hl
  rw [realTowerOver_rat, towerFieldOver_rat, theorem44_noParam l hl]
  exact ⟨fun h x hx => pythClosure_rat_iff.2 (h hx), fun h x hx => pythClosure_rat_iff.1 (h x hx)⟩

/-!
## [s39.necessary] The condition is necessary

*(§ 39)*

> Proof. We shall demonstrate this proposition merely for the case where the co-ordinates of the given points are rational functions, having rational coefficients, of a single parameter $p$. It is at once evident that the proposition gives a necessary condition.

**Lean reading.** `condition_necessary`, for every domain `R` (any number of parameters): if the
numbers of a tower of square roots over `R` lie in `Ω(R)`, every radicand is a nonnegative real
number under every embedding into `ℂ` that is real on `R` (for all real values of the parameters
and either sign of the square roots). Hilbert's "at once evident" is an induction on the
construction of each number of `Ω(R)`: an embedding real on `R` extends along the construction
with real values (`pyth_ext`), and a radicand is the square of a real value. In particular, without
parameters (`condition_necessary_rat`): an embedding extends to the numbers of `Ω` with values in
`Ω` (`omega_ext`).

**Status.** proved
-/

theorem condition_necessary (R : Subfield ℝ) (l : List ℝ) (hv : ValidTowerOver R l)
    (h : ∀ x ∈ towerFieldOver R l, PythClosure (R : Set ℝ) x) : RealTowerOver R l :=
  theorem44_necessary R l hv h

theorem condition_necessary_rat (l : List ℝ) (hv : ValidTower l) (h : towerField l ≤ Omega) :
    RealTower l :=
  realTower_of_le_omega l hv h

/-!
## [s39.sum_of_squares] Square roots of sums of several squares

*(§ 39)*

> Moreover, the formul{\ae} \begin{eqnarray*} \sqrt{a^2 + b^2 + c^2} & = & \sqrt{(\sqrt{a^2 + b^2})^2 + c^2}\\ \sqrt{a^2 + b^2 + c^2 + d^2} & = & \sqrt{(\sqrt{a^2 + b^2 + c^2})^2 + d^2} \end{eqnarray*} … show that, in general, the extraction of the square root of a sum of any number of squares may always be reduced to the repeated extraction of the square root of the sum of two squares.

**Lean reading.** `sqrt_sum_three_sq` is the first formula; `sqrt_sum_sq_mem`: the square root of a
sum of squares of numbers of a subfield `F ⊆ Ω` lies in `Ω` (`SOSIn.sqrt_mem_omega`, by repeated
square roots of sums of two squares).

**Status.** proved
-/

theorem sqrt_sum_three_sq (a b c : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) = Real.sqrt (Real.sqrt (a ^ 2 + b ^ 2) ^ 2 + c ^ 2) := by
  rw [Real.sq_sqrt (by positivity)]

theorem sqrt_sum_sq_mem {F : Subfield ℝ} (hF : F ≤ Omega) {u : ℝ} (h : SOSIn F u) :
    Real.sqrt u ∈ Omega :=
  SOSIn.sqrt_mem_omega hF h

/-!
## [s39.first_radicand] The first square root is constructible

*(§ 39)*

> In order to show that it is also sufficient, let us assume that it is fulfilled and then, among the $n$ square roots, consider that one which, in the calculation of the co-ordinates of the desired points, is first to be extracted. The expression under this radical is a rational function $f_1(p)$, having rational coefficients, of the parameter $p$. … Hence, from theorem 43, we conclude that $f_1(p)$ can be represented as a quotient of the sums of squares of integral rational functions. … If now we combine this conclusion with the preceding results, it follows that the expression $\sqrt{f_1(p)}$ can certainly be constructed by means of a straight-edge and a transferer of segments.

**Lean reading.** `first_radicand`: for any domain `R`, if a radicand `f₁ ∈ R` is a quotient of
two sums of squares of numbers of `R` (what Theorem 43 gives for `R = ℚ(p)`), then `√f₁ ∈ Ω(R)`:
`√(u/v) = √(u v)/v` and `√(u v)` is obtained by repeated square roots of sums of two squares
(`sqrt_qsos_mem`). That `f₁` is such a quotient is `Theorem43For R` applied to a radicand which
is nonnegative for all real parameter values (Hilbert's "cannot have a negative value"), part of
the reduction in unit `th.44`.

**Status.** proved
-/

theorem first_radicand (R : Subfield ℝ) {f₁ : ℝ} (h : QSOS R f₁) :
    PythClosure (R : Set ℝ) (Real.sqrt f₁) :=
  sqrt_qsos_mem (fun _ hx => PythClosure.base hx) h

/-!
## [s39.quadratic] The quadratic equation for a radicand

*(§ 39)*

> This function $f_2$ can never be negative for any real arbitrary value of the parameter $p$ and for either sign of $\sqrt{f_1}$; for, otherwise among the $2^n$ solutions of our problem, there would exist for certain values of $p$ also imaginary solutions, which is contrary to our hypothesis. It follows, therefore, that $f_2$ must satisfy a quadratic equation of the form \[ f_2^2 - \phi_2(p)f_2 + \psi_1(p) = 0, \] where $\phi_1(p)$ and $\psi_1(p)$ are, necessarily, such rational functions of $p$ as have rational coefficients and for real values of $p$ never become negative. From this equation, we have \[ f_2 = \frac{f_2^2 + \psi_1(p)}{\phi_1(p)}. \]

**Lean reading.** For `g = r + s√a` (`r, s, a` in the field below), `φ = 2r` (trace) and
`ψ = r² - s²a` (norm) are totally nonnegative when `g` is, `g² - φ g + ψ = 0`, and
`g = (g² + ψ)/φ` when `φ ≠ 0` (`quadratic_relation`; the total nonnegativity is part of
`tower_qsos`). Misprints: the equation has `φ₂` for `φ₁`; in the next step of the text the
equation for `f₃` is printed `f₃² - φ₂ f₃ - ψ₂ = 0`, which is inconsistent with the formula
`f₃ = (f₃² + ψ₂)/φ₂` drawn from it; the correct equation is `f₃² - φ₂ f₃ + ψ₂ = 0`. If `φ = 0`
then `g = 0`.

**Status.** proved
-/

theorem quadratic_relation (r s a b : ℝ) (hb : b ^ 2 = a) :
    (r + s * b) ^ 2 - (2 * r) * (r + s * b) + (r ^ 2 - s ^ 2 * a) = 0 ∧
      (2 * r ≠ 0 → r + s * b = ((r + s * b) ^ 2 + (r ^ 2 - s ^ 2 * a)) / (2 * r)) := by
  refine ⟨by rw [← hb]; ring, fun h => ?_⟩
  rw [eq_div_iff h, ← hb]; ring

/-!
## [s39.remark] Totally nonnegative numbers of the tower

*(§ 39)*

> Just as with the expression $f_2$, any other rational function $\phi_2(p, \sqrt{f_1})$ of $p$ and $\sqrt{f_1}$ may be shown to be the quotient of two sums of squares of functions which may be constructed, provided this rational function $\phi_2$ possesses the property that for real values of the parameter $p$ and for either sign of $\sqrt{f_1}$, it never becomes negative. This remark permits us to extend the above method of reasoning in the following manner. … The continuation of this method of reasoning leads to the demonstration of theorem 44 for the case of a single parameter $p$.

**Lean reading.** `tower_remark_over`, for every domain `R` (any number of parameters): if
`Theorem43For R` holds (Theorem 43 is used by Hilbert exactly in this role, for the functions of
`p` alone), then in a tower of square roots over `R` every number that is nonnegative for all real
values of the parameters and either sign of every square root is a quotient of two sums of squares
of numbers of the tower; the induction is Hilbert's (trace and norm, unit `s39.quadratic`). With the
tower inside `Ω(R)`, the square root of such a number lies in `Ω(R)` (unit `s39.sum_of_squares`),
which gives the sufficiency in Theorem 44 from `Theorem43For R` (`tower_sufficient_over`).
Unconditionally without parameters (`tower_remark`, `R = ℚ`, Lagrange's theorem in place of
Theorem 43; `tower_sufficient`: the tower lies in `Ω`). For one parameter `Theorem43For ℚ(p)` is
open here (unit `th.43`), so there the remark is proved only relative to it.

**Status.** proved (reading)
-/

theorem tower_remark (l : List ℝ) (hv : ValidTower l) (g : ℝ) (hg : TotNonneg (towerField l) g) :
    QSOS (towerField l) g :=
  tower_qsos l hv g hg

theorem tower_remark_over (R : Subfield ℝ) (hR : Theorem43For R) (l : List ℝ)
    (hv : ValidTowerOver R l) (g : ℝ) (hg : TotNonnegOver R (towerFieldOver R l) g) :
    QSOS (towerFieldOver R l) g :=
  tower_qsos_over R hR l hv g hg

theorem tower_sufficient_over (R : Subfield ℝ) (hR : Theorem43For R) (l : List ℝ)
    (hv : ValidTowerOver R l) (h : RealTowerOver R l) (x : ℝ) (hx : x ∈ towerFieldOver R l) :
    PythClosure (R : Set ℝ) x :=
  tower_le_pythClosure R hR l hv h hx

theorem tower_sufficient (l : List ℝ) (hv : ValidTower l) (h : RealTower l) :
    towerField l ≤ Omega :=
  tower_le_omega l hv h

/-!
## [s39.general_case] The general case

*(§ 39)*

> The truth of theorem 44 for the general case depends upon whether or not theorem 43 can be generalized in a similar manner to cover the case of two or more variables.

**Lean reading.** The dependence is proved (`general_case`): Theorem 44 for every domain `R`
generated by finitely many real numbers (any number of parameters) follows from `Theorem43For R`
for every such `R`, the generalization of Theorem 43 to functions of several parameters (and to
algebraic coefficients). That generalization is Hilbert's seventeenth problem (every definite
rational function of several variables is a sum of squares of rational functions), solved by
Artin in 1927 — not formalized here, so `Theorem44` stays open.

**Status.** proved (reading)
-/

theorem general_case (h : ∀ S : Finset ℝ, Theorem43For (Subfield.closure (S : Set ℝ))) :
    Theorem44 :=
  theorem44_of_theorem43For h

/-!
## [s39.regular_polygons] Regular polygons

*(§ 39)*

> As an example of the application of theorem 44, we may consider the regular polygons which may be constructed by means of a compass. In this case, the arbitrary parameter, $p$ does not occur, and the expressions to be constructed all represent algebraic numbers. We easily see that the criterion of theorem 44 is fulfilled, and, consequently, it follows that the above-mentioned regular polygons can be constructed by the drawing of straight lines and the laying off of segments. We might deduce this result also directly from the theory of the division of the circle (*Kreisteilung*).

**Lean reading.** `RegularPolygonsClaim`: if the regular `n`-gon is constructible with the compass
(`cos (2π/n)` lies in the closure `EuclidClosure` of `ℚ` under the field operations and square
roots of nonnegative numbers), then its vertices `(cos 2πk/n, sin 2πk/n)` have coordinates in `Ω`,
i.e. are constructible from the frame by straight-edge and transferer (unit `s37.omega_geometry`).
The general proof needs the Galois theory of the cyclotomic fields (the real subfield of `ℚ(ζₙ)` is
totally real with a `2`-group as Galois group, so it is a tower to which Theorem 44 applies), which is
beyond this project. Proved: the cases `n = 3, 4, 5, 6, 8, 10` (`regular_polygons_small`; for the
pentagon `sin(π/5) = √(((√5 - 1)/4)² + (1/2)²)`).

**Status.** stated (open here)
-/

/-- The numbers constructible with the compass (and straight-edge): closure of `ℚ` under the
field operations and the square roots of nonnegative numbers. -/
inductive EuclidClosure : ℝ → Prop
  | one : EuclidClosure 1
  | add {a b : ℝ} : EuclidClosure a → EuclidClosure b → EuclidClosure (a + b)
  | sub {a b : ℝ} : EuclidClosure a → EuclidClosure b → EuclidClosure (a - b)
  | mul {a b : ℝ} : EuclidClosure a → EuclidClosure b → EuclidClosure (a * b)
  | div {a b : ℝ} : EuclidClosure a → EuclidClosure b → b ≠ 0 → EuclidClosure (a / b)
  | sqrt {a : ℝ} : EuclidClosure a → 0 ≤ a → EuclidClosure (Real.sqrt a)

/-- Hilbert's claim on the regular polygons constructible with the compass. -/
def RegularPolygonsClaim : Prop :=
  ∀ n : ℕ, 3 ≤ n → EuclidClosure (Real.cos (2 * π / n)) →
    ∀ k : ℕ, Real.cos (2 * π * k / n) ∈ Omega ∧ Real.sin (2 * π * k / n) ∈ Omega

theorem regular_polygons_small (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 10)
    (k : ℕ) :
    RulerTransferer (frameSet ℝ) (pt2 (Real.cos (2 * π * k / n)) (Real.sin (2 * π * k / n))) := by
  rw [omega_geometry]; simpa using regular_polygon_mem n hn k

/-!
## [s39.malfatti] The problem of Malfatti

*(§ 39)*

> Concerning the other known problems of construction in the elementary geometry, we will here only mention that the problem of Malfatti may be constructed by means of a straight-edge and a transferer of segments.

**Lean reading.** The problem of Malfatti: to inscribe in a triangle three circles, each tangent
to the two sides through one vertex and to the other two circles. `MalfattiClaim`: for every
triangle `ABC` of the real plane there are such circles (centers inside the triangle, tangency to
a side as distance to its line, `((Q - P) × (O - P))² = r²|PQ|²`, external tangency of two circles
as `|OᵢOⱼ| = rᵢ + rⱼ`) whose centers are constructible by straight-edge and transferer from the
frame and the vertices. Hilbert gives no proof. A proof would verify the classical closed form of
the Malfatti radii (in terms of the inradius, the semiperimeter and the distances from the
incenter to the vertices, all in `Ω(R)`) against these conditions; that algebra is not done here.
Proved: the claim for the equilateral triangle `(0,0)`, `(1,0)`, `(1/2, √3/2)` (`malfatti_equilateral`:
radii `(√3 - 1)/4`, centers `((3 - √3)/4, (√3 - 1)/4)`, `((1 + √3)/4, (√3 - 1)/4)`, `(1/2, 1/2)`,
all with coordinates in `Ω`).

**Status.** stated (open here)
-/

/-- `O` lies strictly inside the triangle `ABC`. -/
def InTriangle (O A B C : Coord ℝ 2) : Prop :=
  ∃ l m n : ℝ, 0 < l ∧ 0 < m ∧ 0 < n ∧ l + m + n = 1 ∧ O = l • A + m • B + n • C

/-- The circle about `O` with radius `r` is tangent to the line `PQ`. -/
def TangentToLine (O P Q : Coord ℝ 2) (r : ℝ) : Prop :=
  crossProd2 (Q - P) (O - P) ^ 2 = r ^ 2 * ip (Q - P) (Q - P)

/-- The circles of Malfatti of the triangle `ABC`, with centers constructible by straight-edge and
transferer from the frame and the vertices. -/
def MalfattiFor (A B C : Coord ℝ 2) : Prop :=
  ∃ (O₁ O₂ O₃ : Coord ℝ 2) (r₁ r₂ r₃ : ℝ), 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
    InTriangle O₁ A B C ∧ InTriangle O₂ A B C ∧ InTriangle O₃ A B C ∧
    TangentToLine O₁ A B r₁ ∧ TangentToLine O₁ A C r₁ ∧
    TangentToLine O₂ B A r₂ ∧ TangentToLine O₂ B C r₂ ∧
    TangentToLine O₃ C A r₃ ∧ TangentToLine O₃ C B r₃ ∧
    ip (O₁ - O₂) (O₁ - O₂) = (r₁ + r₂) ^ 2 ∧ ip (O₂ - O₃) (O₂ - O₃) = (r₂ + r₃) ^ 2 ∧
    ip (O₃ - O₁) (O₃ - O₁) = (r₃ + r₁) ^ 2 ∧
    RulerTransferer (frameSet ℝ ∪ {A, B, C}) O₁ ∧ RulerTransferer (frameSet ℝ ∪ {A, B, C}) O₂ ∧
    RulerTransferer (frameSet ℝ ∪ {A, B, C}) O₃

/-- Hilbert's claim on the problem of Malfatti: the circles of Malfatti can be constructed by
straight-edge and transferer. -/
def MalfattiClaim : Prop :=
  ∀ A B C : Coord ℝ 2, ¬Collinear A B C → MalfattiFor A B C

/-- Constructions by straight-edge and transferer are monotone in the given points. -/
theorem RulerTransferer.mono {P : Type*} {L : Type*} [HasLines P L] [HasBetween P]
    [HasSegCong P] {S T : Set P} (hST : S ⊆ T) {X : P} (h : RulerTransferer (L := L) S X) :
    RulerTransferer (L := L) T X := by
  induction h with
  | given hA => exact .given (hST hA)
  | meet _ _ _ _ hAB hCD hAa hBa hCb hDb hab hXa hXb iA iB iC iD =>
    exact .meet iA iB iC iD hAB hCD hAa hBa hCb hDb hab hXa hXb
  | layOff _ _ _ _ hAB hOQ hOa hQa hXa hXO hseg iA iB iO iQ =>
    exact .layOff iA iB iO iQ hAB hOQ hOa hQa hXa hXO hseg

theorem malfatti_equilateral :
    MalfattiFor (pt2 0 0) (pt2 1 0) (pt2 (1 / 2) (Real.sqrt 3 / 2)) := by
  set s := Real.sqrt 3 with hsdef
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < s := by rw [hsdef, Real.lt_sqrt (by norm_num)]; norm_num
  have hs3 : s < 3 := by nlinarith
  have hsO : s ∈ Omega := sqrt_three_mem
  have rt : ∀ x y : ℝ, x ∈ Omega → y ∈ Omega →
      RulerTransferer (frameSet ℝ ∪ {pt2 0 0, pt2 1 0, pt2 (1 / 2) (s / 2)}) (pt2 x y) := by
    intro x y hx hy
    exact RulerTransferer.mono Set.subset_union_left (rt_frame_iff_omega.2 (by simpa using ⟨hx, hy⟩))
  have h4 : (4 : ℝ) ∈ Omega := by norm_num
  have h2 : (2 : ℝ) ∈ Omega := two_mem_subfield _
  set r := (s - 1) / 4 with hr
  refine ⟨pt2 ((3 - s) / 4) ((s - 1) / 4), pt2 ((1 + s) / 4) ((s - 1) / 4), pt2 (1 / 2) (1 / 2),
    r, r, r, by rw [hr]; linarith, by rw [hr]; linarith, by rw [hr]; linarith,
    ⟨s / 3, (3 - s) / 6, (3 - s) / 6, by positivity, by linarith, by linarith, by ring, ?_⟩,
    ⟨(3 - s) / 6, s / 3, (3 - s) / 6, by linarith, by positivity, by linarith, by ring, ?_⟩,
    ⟨(3 - s) / 6, (3 - s) / 6, s / 3, by linarith, by linarith, by positivity, by ring, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext2 <;> simp <;> field_simp <;> nlinarith
  · apply ext2 <;> simp <;> field_simp <;> nlinarith
  · apply ext2 <;> simp <;> field_simp <;> nlinarith
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (0) * hs
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (-s / 32) * hs
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (0) * hs
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (-s / 32) * hs
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (-(s - 1) ^ 2 / 64) * hs
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (-(s - 1) ^ 2 / 64) * hs
  · simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (0 : ℝ) * hs
  · simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (-1 / 8 : ℝ) * hs
  · simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hr]
    linear_combination (-1 / 8 : ℝ) * hs
  · exact rt _ _ (Omega.div_mem (Omega.sub_mem (show (3 : ℝ) ∈ Omega by norm_num) hsO) h4)
      (Omega.div_mem (Omega.sub_mem hsO Omega.one_mem) h4)
  · exact rt _ _ (Omega.div_mem (Omega.add_mem Omega.one_mem hsO) h4)
      (Omega.div_mem (Omega.sub_mem hsO Omega.one_mem) h4)
  · exact rt _ _ (Omega.div_mem Omega.one_mem h2) (Omega.div_mem Omega.one_mem h2)

/-!
## [s39.apollonius] The contact problems of Apollonius

*(§ 39)*

> This is, however, not the case with the contact problems of Appolonius.

**Lean reading.** The contact problems of Apollonius (circles tangent to three given circles,
points or lines) are not all solvable by straight-edge and transferer. `apollonius_case`: the case
"two points and a line" with the points `(0, 1)`, `(0, 2√2 - 2)` and the axis `y = 0` — all
constructible from the frame. The circles through the two points tangent to the axis exist in the
real plane (they are constructible with the compass), but neither their points of contact
`(±√(2√2 - 2), 0)` nor their centers are constructible by straight-edge and transferer
(`TangentCircle` expresses tangency by `T` on the axis, `MT ⊥` axis, `MT = MP = MQ`). Read as "not
every contact problem of Apollonius can be solved".

**Status.** proved (reading)
-/

theorem apollonius_case :
    RulerTransferer (frameSet ℝ) (pt2 0 1) ∧
      RulerTransferer (frameSet ℝ) (pt2 0 (2 * Real.sqrt 2 - 2)) ∧
      (∃ T M, TangentCircle (pt2 0 1) (pt2 0 (2 * Real.sqrt 2 - 2)) T M) ∧
      ∀ T M, TangentCircle (pt2 0 1) (pt2 0 (2 * Real.sqrt 2 - 2)) T M →
        ¬RulerTransferer (frameSet ℝ) T ∧ ¬RulerTransferer (frameSet ℝ) M :=
  apollonius_example

end HilbertFoundations
