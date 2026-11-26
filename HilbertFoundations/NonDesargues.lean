import HilbertFoundations.Analytic
import HilbertFoundations.NonDesarguesAux4
import HilbertFoundations.NonDesarguesAux5
import HilbertFoundations.NonDesarguesAux6
import HilbertFoundations.NonDesarguesAux7

/-!
# A plane geometry in which Desargues's theorem fails (§ 23, Theorem 33)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 23. The impossibility of demonstrating Desargues's theorem for the plane without the help of the axioms of congruence

The model is built in the helper modules:

* `NonDesarguesAux`: the Moulton plane (points `Moulton.Pt`, lines `Moulton.Ln`), groups I, II, III;
* `NonDesarguesAux2`: congruence of segments by the length of broken lines, IV 1–3, V;
* `NonDesarguesAux3`: congruence of angles, IV 4–5;
* `NonDesarguesAux4`: the counterexamples to Desargues's theorem and to IV 6;
* `NonDesarguesAux5`: Hilbert's ellipse and the circles through `F` (the facts his own
  construction rests on);
* `NonDesarguesAux6`: the direct part of Desargues's theorem in a plane of space, proved from the
  axioms I and III (so that the Moulton plane is not part of a space geometry);
* `NonDesarguesAux7`: Hilbert's own geometry: exterior doubly tangent circles, the lines through
  `F`, and the configuration of Fig. 40.
-/

namespace HilbertFoundations

universe u v

/-!
## [th.33] Theorem 33

*(§ 23)*

> A plane geometry exists in which the axioms I 1–2, II–III, IV 1–5, V, that is to say, all linear and all plane axioms with the exception of axiom IV, 6 of congruence, are fulfilled, but in which the theorem of Desargues (theorem 32) is not valid. Desargues's theorem is not, therefore, a consequence solely of the axioms mentioned; for, its demonstration necessitates either the space axioms or all of the axioms of congruence.

**Lean reading.** Theorem 32 is stated here for plane geometries (self-contained, independent of
Desargues.lean): `DesarguesParallel` (two triangles whose homologous sides lie on lines without
common point have their three joining lines concurrent or pairwise without common point) and its
converse `DesarguesConverse` (§ 22 counts both as "the theorem of Desargues"; in the converse a
"parallel" third side may coincide), `DesarguesTheorem` being the conjunction. "I 1–2, II–III,
IV 1–5, V" is `PlaneOrder`, `PlaneParallels`, `SegmentCongruence`, `PlaneAngleCongruence`,
`Archimedes` (no `TriangleCongruence`). The model is not Hilbert's ellipse geometry but its simplest
faithful variant, the Moulton plane cited in the translator's note: the ellipse is replaced by the
half-plane `x > 0`, the lines meeting it by broken lines (refracted on the `y`-axis), segments are
compared by the ordinary length of broken lines, angles by the ordinary angle off the `y`-axis and
by a normalized angle on it (see `s23.angle_congruence`); everything Hilbert's own construction
needs about the ellipse is proved separately (`s23.tangent_circle` – `s23.circle_PQF`). The
existence statement is `theorem33_exists` (a model of these axioms in which the direct part of
Theorem 32 fails and, necessarily, IV 6 fails too); the "therefore" sentence is `theorem33`:
`DesarguesFromTh33Axioms` (Desargues's theorem in every model of these axioms) is false. The last
clause ("its demonstration necessitates either the space axioms or all of the axioms of
congruence") is a reference to § 22: the proof of Desargues's theorem from all plane axioms of
congruence is Theorem 32 (Desargues.lean), not repeated here; from the space axioms, the direct
part is proved in every plane of a space satisfying I and III (`spaceDesargues_holds`, see
`s23.not_part_of_space`). This also checks the formulation of `DesarguesParallel`: the same
statement, read in a plane of space, is a theorem of I and III, so it holds in the Euclidean plane.

**Status.** proved (reading)
-/

section DesarguesStatement

variable (P : Type u) {L : Type v} [HasLines P L]

/-- **Desargues's theorem** (Theorem 32, direct part), plane geometry: if the triangles `ABC`,
`A'B'C'` have their homologous sides on lines `a ∥ a'`, `b ∥ b'`, `c ∥ c'` (no common point), then
the lines `p = AA'`, `q = BB'`, `r = CC'` pass through one point or are pairwise parallel. -/
def DesarguesParallel : Prop :=
  ∀ (A B C A' B' C' : P) (a b c a' b' c' p q r : L),
    ¬Collinear A B C → ¬Collinear A' B' C' →
    B ∈ a → C ∈ a → C ∈ b → A ∈ b → A ∈ c → B ∈ c →
    B' ∈ a' → C' ∈ a' → C' ∈ b' → A' ∈ b' → A' ∈ c' → B' ∈ c' →
    ¬Meets (Point := P) a a' → ¬Meets (Point := P) b b' → ¬Meets (Point := P) c c' →
    A ∈ p → A' ∈ p → B ∈ q → B' ∈ q → C ∈ r → C' ∈ r →
    (∃ O : P, O ∈ p ∧ O ∈ q ∧ O ∈ r) ∨
      (¬Meets (Point := P) p q ∧ ¬Meets (Point := P) q r ∧ ¬Meets (Point := P) p r)

/-- **The converse of Desargues's theorem** (§ 22): if the joining lines pass through one point or
are pairwise parallel and two pairs of homologous sides are parallel, the third sides are parallel
(or coincide). -/
def DesarguesConverse : Prop :=
  ∀ (A B C A' B' C' : P) (a b c a' b' c' p q r : L),
    ¬Collinear A B C → ¬Collinear A' B' C' →
    B ∈ a → C ∈ a → C ∈ b → A ∈ b → A ∈ c → B ∈ c →
    B' ∈ a' → C' ∈ a' → C' ∈ b' → A' ∈ b' → A' ∈ c' → B' ∈ c' →
    A ∈ p → A' ∈ p → B ∈ q → B' ∈ q → C ∈ r → C' ∈ r →
    ((∃ O : P, O ∈ p ∧ O ∈ q ∧ O ∈ r) ∨
      (¬Meets (Point := P) p q ∧ ¬Meets (Point := P) q r ∧ ¬Meets (Point := P) p r)) →
    ¬Meets (Point := P) b b' → ¬Meets (Point := P) c c' → a = a' ∨ ¬Meets (Point := P) a a'

/-- **The theorem of Desargues** (Theorem 32 with its converse), plane geometry. -/
def DesarguesTheorem : Prop := DesarguesParallel P ∧ DesarguesConverse P

end DesarguesStatement

/-- "Desargues's theorem is a consequence of the axioms I 1–2, II–III, IV 1–5, V": it holds in
every plane geometry satisfying them. -/
def DesarguesFromTh33Axioms : Prop :=
  ∀ (P : Type) (L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneOrder P L → PlaneParallels P L → SegmentCongruence P L → PlaneAngleCongruence P L →
    Archimedes P L → DesarguesTheorem P

open Moulton in
/-- The Moulton plane satisfies I 1–2, II–III, IV 1–5, V. -/
theorem moulton_axioms :
    PlaneOrder Pt Ln ∧ PlaneParallels Pt Ln ∧ SegmentCongruence Pt Ln ∧
      PlaneAngleCongruence Pt Ln ∧ Archimedes Pt Ln :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

open Moulton in
/-- Desargues's theorem fails in the Moulton plane. -/
theorem moulton_not_desarguesParallel : ¬DesarguesParallel Pt := by
  intro h
  obtain ⟨n1, n2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pa, pb, pc, p1, p2, q1, q2,
    r1, r2, hno, hqr⟩ := desargues_config
  rcases h dA dB dC dA' dB' dC' la lb lc la' lb' lc' lp lq lr n1 n2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 pa pb pc p1 p2 q1 q2 r1 r2 with h | h
  · exact hno h
  · exact h.2.1 hqr

theorem moulton_not_desargues : ¬DesarguesTheorem Moulton.Pt :=
  fun h => moulton_not_desarguesParallel h.1

/-- **Theorem 33.** Desargues's theorem is not a consequence of I 1–2, II–III, IV 1–5, V. -/
theorem theorem33 : ¬DesarguesFromTh33Axioms := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := moulton_axioms
  exact moulton_not_desargues (h Moulton.Pt Moulton.Ln h1 h2 h3 h4 h5)

/-- In the Moulton plane axiom IV 6 fails (as it must, Desargues's theorem being a consequence of
all the plane axioms of congruence). -/
theorem moulton_not_axiomIV6 : ¬AxiomIV6 Moulton.Pt := by
  intro h
  obtain ⟨t1, t2, s1, s2, a1, a2⟩ := Moulton.not_axiomIV6_config
  exact a2 (h _ _ _ _ _ _ t1 t2 s1 s2 a1).1

/-- **Theorem 33**, existence form: a plane geometry satisfying I 1–2, II–III, IV 1–5, V in which
Desargues's theorem (direct part of Theorem 32) is not valid (and IV 6 fails). -/
theorem theorem33_exists :
    ∃ (P L : Type) (_ : HasLines P L) (_ : HasBetween P) (_ : HasSegCong P) (_ : HasAngCong P),
      PlaneOrder P L ∧ PlaneParallels P L ∧ SegmentCongruence P L ∧ PlaneAngleCongruence P L ∧
        Archimedes P L ∧ ¬DesarguesParallel P ∧ ¬AxiomIV6 P :=
  ⟨Moulton.Pt, Moulton.Ln, inferInstance, inferInstance, inferInstance, inferInstance,
    moulton_axioms.1, moulton_axioms.2.1, moulton_axioms.2.2.1, moulton_axioms.2.2.2.1,
    moulton_axioms.2.2.2.2, moulton_not_desarguesParallel, moulton_not_axiomIV6⟩

/-!
## [s23.symmetric_tangent] Exterior doubly tangent circles are symmetric to the `y`-axis

*(§ 23)*

> The desired farthest point will accordingly be found among those points of intersection of the positive $x$-axis by circles lying exterior to the ellipse and being doubly tangent to it. All such circles must lie, as we can easily see, symmetrically with respect to the $y$-axis.

**Lean reading.** The first sentence is the conclusion of Hilbert's variational argument (turning
and enlarging circles), which is not formalized; its purpose, that no circle meeting the ellipse
four times passes through `F`, is proved algebraically in `s23.no_four_point_circle`. The second
sentence is proved: a circle "lying exterior to the ellipse" (the ellipse `x² + 4y² = 1` lies in
its closed disc) and "doubly tangent to it" (it has two distinct points in common with the ellipse,
where it is then necessarily tangent) has its centre on the `y`-axis, and the two points of contact
are symmetric with respect to the `y`-axis (`HilbertEllipse.exterior_bitangent_symmetric`). The
proof compares the two points of contact with the point of the ellipse of mean ordinate (strict
concavity). Exteriority is needed: the circles of centre `(3c/4, 0)` touching the ellipse from
inside at `(c, ±√(1-c²)/2)` are doubly tangent and symmetric to the `x`-axis instead.

**Status.** proved
-/

theorem s23_symmetric_tangent {h k ρ x1 y1 x2 y2 : ℝ}
    (hin : ∀ x y : ℝ, HilbertEllipse.OnEllipse x y → (x - h) ^ 2 + (y - k) ^ 2 ≤ ρ)
    (e1 : HilbertEllipse.OnEllipse x1 y1) (e2 : HilbertEllipse.OnEllipse x2 y2)
    (c1 : (x1 - h) ^ 2 + (y1 - k) ^ 2 = ρ) (c2 : (x2 - h) ^ 2 + (y2 - k) ^ 2 = ρ)
    (hne : x1 ≠ x2 ∨ y1 ≠ y2) : h = 0 ∧ y2 = y1 ∧ x2 = -x1 :=
  HilbertEllipse.exterior_bitangent_symmetric hin e1 e2 c1 c2 hne

/-!
## [s23.tangent_circle] The doubly tangent circle symmetric to the `y`-axis

*(§ 23)*

> Select in the ordinary plane geometry … any two straight lines perpendicular to each other as the axes of $x$ and $y$. Construct about the origin $O$ of this system of co-ordinates an ellipse having the major and minor axes equal to 1 and $\frac{1}{2}$, respectively. … Let $a$, $b$ be the co-ordinates of any point on the ellipse. Then an easy calculation shows that the circle, which is symmetrical with respect to $y$-axis and tangent to the ellipse at this point, cuts off from the positive $x$-axis the segment \[ x = \mid \sqrt{1 + 3b^2} \mid. \]

**Lean reading.** "Major and minor axes equal to 1 and 1/2" are the semi-axes (the point
`(3/5, 2/5)` used later lies on it): the ellipse is `x² + 4y² = 1` (`HilbertEllipse.OnEllipse`). A
circle symmetric to the `y`-axis has centre `(0, k)`; it is tangent to the ellipse at `(a, b)`
(`a ≠ 0`) iff the centre lies on the normal `(a, 4b)` of the ellipse there, i.e. `k = -3b`; its
point `(x, 0)` with `x > 0` then satisfies `x = √(1 + 3b²)`. For `a = 0` (`b = ±1/2`) every centre
on the `y`-axis gives a tangent circle, and Hilbert's formula is the one of the osculating circle
(the limit case). The analytic argument before this sentence (turning and enlarging circles until
they are doubly tangent) is heuristic; it is replaced by the algebraic proof of
`s23.no_four_point_circle`; the symmetry of the exterior doubly tangent circles is
`s23.symmetric_tangent`.

**Status.** proved
-/

theorem s23_tangent_circle {a b : ℝ} (hE : HilbertEllipse.OnEllipse a b) (ha : a ≠ 0) :
    (∀ k : ℝ, a * (4 * b) - (b - k) * a = 0 ↔ k = -3 * b) ∧
    ∀ x : ℝ, 0 < x →
      (x ^ 2 + (0 - -3 * b) ^ 2 = a ^ 2 + (b - -3 * b) ^ 2 ↔ x = √(1 + 3 * b ^ 2)) :=
  HilbertEllipse.tangent_circle hE ha

/-!
## [s23.max_intercept] The greatest intercept is $\frac12\sqrt7 < \frac32$

*(§ 23)*

> The greatest possible value of this expression occurs for $b = \frac{1}{2}$ and, hence, is equal to $\frac{1}{2}\mid\sqrt{7}\mid$. Since the point on the $x$-axis which we have denoted by $F$ has for its abscissa the value $\frac{3}{2} > \frac{1}{2} \mid\sqrt{7}\mid$, …

**Lean reading.** For every point `(a, b)` of the ellipse `√(1 + 3b²) ≤ √7/2`, with equality at the
point `(0, 1/2)`, and `√7/2 < 3/2` (the abscissa of `F`).

**Status.** proved
-/

theorem s23_max_intercept :
    (∀ a b : ℝ, HilbertEllipse.OnEllipse a b → √(1 + 3 * b ^ 2) ≤ √7 / 2) ∧
    HilbertEllipse.OnEllipse 0 (1 / 2) ∧ √(1 + 3 * (1 / 2) ^ 2) = √7 / 2 ∧ √7 / 2 < 3 / 2 :=
  HilbertEllipse.max_intercept

/-!
## [s23.no_four_point_circle] No circle cutting the ellipse four times passes through $F$

*(§ 23)*

> Consider all of the circles which cut the ellipse in four real points. These points may be either distinct or in any way coincident. … it follows that *among the circles cutting the ellipse four times there is certainly none which passes through the point $F$.*

**Lean reading.** Points of the ellipse are `(cos θ, sin θ / 2)` (`ellipse_param`). For eccentric
angles `θ₁, θ₂, θ₃` and `θ₄ = -(θ₁+θ₂+θ₃)` the circle with coefficients `cD`, `cE`, `cG` meets the
ellipse exactly in these four points counted with multiplicity: its power at the point of angle `θ`
is `3 ∏ sin ((θ - θₖ)/2)` (`circleStar_factor`); by `circle_eq_circleStar` every circle with three
distinct common points with the ellipse is one of them. "The circles cutting the ellipse in four
real points" are read as this family; the identification of an arbitrary circle with four real
intersections of which at most two are distinct (e.g. a doubly tangent one) with a member of the
family (Joachimsthal's condition with multiplicities) is not formalized. The claim is then that the
power of `F = (3/2, 0)` never vanishes; it is proved by an algebraic identity (the power is
`(3/4) g + 1/2`, `g ≥ 0`, see `HilbertEllipse.power_F_pos`) instead of Hilbert's variational
argument, whose maximum `√7/2` is the symmetric case of this bound.

**Status.** proved (reading)
-/

theorem s23_no_four_point_circle (t1 t2 t3 : ℝ) :
    ¬HilbertEllipse.OnCircle (HilbertEllipse.cD t1 t2 t3) (HilbertEllipse.cE t1 t2 t3)
      (HilbertEllipse.cG t1 t2 t3) (3 / 2) 0 :=
  HilbertEllipse.no_four_point_circle_through_F t1 t2 t3

theorem s23_circleStar_factor (t1 t2 t3 t : ℝ) :
    Real.cos t ^ 2 + (Real.sin t / 2) ^ 2 + HilbertEllipse.cD t1 t2 t3 * Real.cos t +
        HilbertEllipse.cE t1 t2 t3 * (Real.sin t / 2) + HilbertEllipse.cG t1 t2 t3 =
      3 * (Real.sin ((t - t1) / 2) * Real.sin ((t - t2) / 2) * Real.sin ((t - t3) / 2) *
        Real.sin ((t - -(t1 + t2 + t3)) / 2)) :=
  HilbertEllipse.circleStar_factor t1 t2 t3 t

/-!
## [s23.circle_PQF] The circle through $P$, $Q$, $F$ meets the ellipse only in $P$, $Q$

*(§ 23)*

> However, when any straight line $g$ of the $(xy)$-plane cuts the ellipse, say in the points $P$ and $Q$, we will then define the corresponding … straight line of the new geometry as follows. Construct a circle passing through the points $P$ and $Q$ and the fixed point $F$. From what has just been said, this circle will have no other point in common with the ellipse.

**Lean reading.** `circle_through_F`: a circle `x² + y² + Dx + Ey + G = 0` through `F` has no
three distinct points in common with the ellipse (of any three common points two coincide). This is
proved directly (a circle with three distinct common points is a `circleStar`, whose power at `F` is
positive), so it does not depend on the reading of the previous unit. Hilbert's rule tacitly
excludes the lines `g` through `F`: then `P`, `Q`, `F` are collinear and there is no circle through
them (for the `x`-axis, used in Fig. 40: `HilbertEllipse.xaxis_no_circle`); such a line must be kept
straight (the circles through `F` degenerate into it), see `s23.fig40_hilbert`.

**Status.** proved
-/

theorem s23_circle_PQF {D E G : ℝ} (hF : HilbertEllipse.OnCircle D E G (3 / 2) 0)
    {x1 y1 x2 y2 x3 y3 : ℝ} (e1 : HilbertEllipse.OnEllipse x1 y1)
    (e2 : HilbertEllipse.OnEllipse x2 y2) (e3 : HilbertEllipse.OnEllipse x3 y3)
    (c1 : HilbertEllipse.OnCircle D E G x1 y1) (c2 : HilbertEllipse.OnCircle D E G x2 y2)
    (c3 : HilbertEllipse.OnCircle D E G x3 y3) :
    (x1 = x2 ∧ y1 = y2) ∨ (x1 = x3 ∧ y1 = y3) ∨ (x2 = x3 ∧ y2 = y3) :=
  HilbertEllipse.circle_through_F hF e1 e2 e3 c1 c2 c3

/-!
## [s23.broken_lines] The broken lines satisfy I 1–2, II, III

*(§ 23)*

> We will now construct a new plane geometry in the following manner. As points in this new geometry, let us take the points of the $(xy)$-plane. … Every straight line of the $(xy)$-plane which is either tangent to the fixed ellipse, or does not cut it at all, is taken unchanged as a straight line of the new geometry. … We will now take the broken line, consisting of the arc $PQ$ just mentioned and the two parts of the straight line $g$ extending outward indefinitely from the points $P$ and $Q$, as the required straight line in our new geometry. Let us suppose all of the broken lines constructed which correspond to straight lines of the $(xy)$-plane. We have then a system of broken lines which, considered as straight lines of our new geometry, evidently satisfy the axioms I, 1–2 and III. By a convention as to the actual arrangement of the points and the straight lines in our new geometry, we have also the axioms II fulfilled.

**Lean reading.** Proved for the Moulton variant: points are the points of the plane
(`Moulton.Pt`); the ordinary lines of slope `≥ 0` and the vertical lines are kept, a line of slope
`m < 0` becomes the broken line of slope `m` for `x ≤ 0` and `2m` for `x ≥ 0` (`Moulton.Ln`,
`Moulton.ht`). "The convention as to the arrangement" is betweenness of the arc-length parameter of
the broken line (`Moulton.Btw`). That these satisfy I 1–2 (and the plane clauses of I 7), II 1–5 and
III is `moulton_planeOrder_parallels`; "evidently" hides the facts that two lines meet at most once
and that a line separates the plane (Pasch), proved through the side function `Moulton.sd`. For
Hilbert's own circle-arc lines, I 1 needs that through two points inside the ellipse passes exactly
one circle through `F` meeting the ellipse twice, which is not formalized.

**Status.** proved (reading)
-/

theorem moulton_planeOrder_parallels : PlaneOrder Moulton.Pt Moulton.Ln ∧
    PlaneParallels Moulton.Pt Moulton.Ln :=
  ⟨inferInstance, inferInstance⟩

/-!
## [s23.segment_congruence] Congruence of segments by the length of broken lines

*(§ 23)*

> Moreover, we will call two segments $AB$ and $A'B'$ congruent in this new geometry, if the broken line extending between $A$ and $B$ has equal length, in the ordinary sense of the word, with the broken line extending from $A'$ to $B'$.

**Lean reading.** `Moulton.segLen A B` is the length of the broken line from `A` to `B`: the
ordinary distance when both lie on the same straight part (`segLen_eq_edist_left`,
`segLen_eq_edist_right`, `segLen_eq_edist_vert`) and the sum of the parts across the corner
(`segLen_add`). `SegCong A B A' B'` is `segLen A B = segLen A' B'`.

**Status.** definition
-/

theorem s23_segCong_iff {A B A' B' : Moulton.Pt} :
    SegCong A B A' B' ↔ Moulton.segLen A B = Moulton.segLen A' B' := Iff.rfl

theorem s23_segLen_ordinary {m b : ℝ} {P Q : Moulton.Pt} (hP : P ∈ Moulton.Ln.graph m b)
    (hQ : Q ∈ Moulton.Ln.graph m b) (h : (P.x ≤ 0 ∧ Q.x ≤ 0) ∨ (0 ≤ P.x ∧ 0 ≤ Q.x)) :
    Moulton.segLen P Q = Moulton.edist P Q := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Moulton.segLen_eq_edist_left hP hQ h1 h2
  · exact Moulton.segLen_eq_edist_right hP hQ h1 h2

/-!
## [s23.angle_congruence] Congruence of angles

*(§ 23)*

> Finally, we need a convention concerning the congruence of angles. So long as neither of the vertices of the angles to be compared lies upon the ellipse, we call the two angles congruent to each other, if they are equal in the ordinary sense. In all other cases we make the following convention. Let $A, B, C$ be points which follow one another in this order upon a straight line of our new geometry, … We will now say that, in our new geometry, the angles between these straight lines fulfill the congruences \[ \angle ABD \equiv \angle A'B'D' and \angle CBD \equiv \angle C'B'D' \] whenever the natural angles between the corresponding broken lines of the ordinary geometry fulfill the proportion \[ \angle ABD: \angle CBD = \angle A'B'D' : \angle C'B'D'. \]

**Lean reading.** Off the curve where the lines break (the `y`-axis here, the ellipse for Hilbert)
two angles are congruent iff their ordinary angles (between the tangents of the broken lines at the
vertex) are equal: `Moulton.angM_eq_ordinary`. At a vertex on the curve the two half-rays of a
broken line are not opposite, and Hilbert rescales the angles on either side of a line in
proportion. As printed the convention is imprecise: it only compares pairs of adjacent angles, an
angle `(h, k)` at a corner adjoins two lines (those of `h` and of `k`), and the text does not say
which of the two proportions decides, nor how angles at a corner compare with angles elsewhere.
Corrected convention: at a vertex `O`
on the `y`-axis each half-ray is given the direction of the right part of its line, taken with the
sign of the ray (`Moulton.dirL`, `Moulton.rdir`), so that the two half-rays of every line are
opposite, and angles are measured by the ordinary angle between these directions
(`Moulton.angM`); this is a well-defined measure on angles, which is what Hilbert's proportions aim
at.

**Status.** definition
-/

theorem s23_angCong_iff {A O B A' O' B' : Moulton.Pt} :
    AngCong A O B A' O' B' ↔ Moulton.angM A O B = Moulton.angM A' O' B' := Iff.rfl

theorem s23_angM_ordinary {A O B : Moulton.Pt} (hA : O ≠ A) (hB : O ≠ B)
    (hpA : (O.x < 0 ∧ A.x ≤ 0) ∨ (0 ≤ O.x ∧ 0 ≤ A.x))
    (hpB : (O.x < 0 ∧ B.x ≤ 0) ∨ (0 ≤ O.x ∧ 0 ≤ B.x)) :
    Moulton.angM A O B = Moulton.angV (Moulton.vec O A) (Moulton.vec O B) :=
  Moulton.angM_eq_ordinary hA hB hpA hpB

/-!
## [s23.conventions_valid] These conventions render IV 1–5 and V valid

*(§ 23)*

> These conventions render the axioms IV, 1–5 and V valid.

**Lean reading.** For the Moulton variant with the corrected angle convention:
`SegmentCongruence` (IV 1–3), `PlaneAngleCongruence` (IV 4–5, including laying off angles on a
given side, with interior points on that side) and `Archimedes` (V). Laying off at a vertex on the
`y`-axis is exactly where Hilbert's proportional convention is needed and where the correction
matters: the directions of the half-rays on one side of a line through the vertex fill an open
half-turn (`Moulton.side_sign`, `Moulton.sameSide_iff_cross`).

**Status.** proved (corrected)
-/

theorem s23_conventions_valid : SegmentCongruence Moulton.Pt Moulton.Ln ∧
    PlaneAngleCongruence Moulton.Pt Moulton.Ln ∧ Archimedes Moulton.Pt Moulton.Ln :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-!
## [s23.desargues_fails] Two triangles violating Desargues's theorem

*(§ 23)*

> In order to see that Desargues's theorem does not hold for our new geometry, let us consider the following three ordinary straight lines of the $(xy)$-plane; viz., the axis of $x$, the axis of $y$, and the straight line joining the two points of the ellipse $(\frac{3}{5},\frac{2}{5})$ and $(-\frac{3}{5},-\frac{2}{5})$. … the broken lines arising from the three straight lines in question do not intersect in a common point. Hence, it follows that Desargues's theorem certainly does not hold for this particular plane geometry in which we have constructed the two triangles just considered. [Fig. 40]

**Lean reading.** The analogous configuration in the Moulton plane: the ordinary lines through
`(1, 0)` of slopes `-1/2`, `∞`, `2` carry the vertices of `A = (-1, 1)`, `B = (1, 1)`,
`C = (2, 2)` and of their image `A' = (-3, 2)`, `B' = (1, 2)`, `C' = (3, 4)` under the homothety of
ratio `2`; the sides (slopes `0`, `1/3`, `1`) are unbroken and pairwise parallel, the line `BB'`
(vertical) and `CC'` (slope `2`) are unbroken and meet at `(1, 0)`, while `AA'` (slope `-1/2`) is
broken at the `y`-axis and misses `(1, 0)`. So the joining lines are neither concurrent nor
parallel (`moulton_not_desarguesParallel`).

**Status.** proved (reading)
-/

theorem s23_desargues_fails :
    ¬Collinear Moulton.dA Moulton.dB Moulton.dC ∧ ¬Collinear Moulton.dA' Moulton.dB' Moulton.dC' ∧
    ¬Meets (Point := Moulton.Pt) Moulton.la Moulton.la' ∧
    ¬Meets (Point := Moulton.Pt) Moulton.lb Moulton.lb' ∧
    ¬Meets (Point := Moulton.Pt) Moulton.lc Moulton.lc' ∧
    ¬(∃ O : Moulton.Pt, O ∈ Moulton.lp ∧ O ∈ Moulton.lq ∧ O ∈ Moulton.lr) ∧
    Meets (Point := Moulton.Pt) Moulton.lq Moulton.lr := by
  obtain ⟨n1, n2, -, -, -, -, -, -, -, -, -, -, -, -, pa, pb, pc, -, -, -, -, -, -, hno, hqr⟩ :=
    Moulton.desargues_config
  exact ⟨n1, n2, pa, pb, pc, hno, hqr⟩

/-!
## [s23.fig40_hilbert] The configuration of Fig. 40 in Hilbert's own geometry

*(§ 23)*

> In order to see that Desargues's theorem does not hold for our new geometry, let us consider the following three ordinary straight lines of the $(xy)$-plane; viz., the axis of $x$, the axis of $y$, and the straight line joining the two points of the ellipse $(\frac{3}{5},\frac{2}{5})$ and $(-\frac{3}{5},-\frac{2}{5})$. Since these three ordinary straight lines pass through the origin, we can easily construct two triangles so that their vertices shall lie respectively upon these three straight lines and their homologous sides shall be parallel and all three sides shall lie exterior to the ellipse. As we may see from figure 40, or show … by an easy calculation, the broken lines arising from the three straight lines in question do not intersect in a common point.

**Lean reading.** Hilbert's own computation, in the coordinates of § 23 (not in the Moulton
variant). The `x`-axis passes through `F`, so Hilbert's rule gives no broken line for it: there is
no circle through `(-1, 0)`, `(1, 0)`, `F` (`HilbertEllipse.xaxis_no_circle`). Corrected reading:
a line through `F` stays straight (the circle through `P`, `Q`, `F` degenerates into it). The
broken line from the `y`-axis is `lineY` (the two outer parts of the axis and the arc inside the
ellipse of the circle through `(0, ±1/2)` and `F`, which is `x² + y² - 4x/3 - 1/4 = 0` and is
unique: `circleY_spec`); that from the line `y = 2x/3` is `lineT` (circle
`x² + y² - 173x/150 + 173y/100 - 13/25 = 0`, `circleT_spec`). The triangles `(3,0)`, `(0,3)`,
`(3,2)` and `(6,0)`, `(0,6)`, `(6,4)` have their vertices on the three lines, and their sides lie
on ordinary lines which miss the ellipse, homologous sides being parallel (`fig40_triangles`).
The three lines have no common point, while the `x`-axis meets `lineY` (only) in `(-1/6, 0)` and
`lineT` in `(-26/75, 0)`, so the lines joining homologous vertices are neither concurrent nor
parallel (`fig40_joining_lines`). That these sets are the lines of the new geometry through the
vertices (I 2 for Hilbert's geometry) is not proved, Hilbert's geometry not being formalized as a
model; for the model, see `s23.desargues_fails`.

**Status.** proved (corrected)
-/

theorem s23_fig40_xaxis :
    HilbertEllipse.OnEllipse (-1) 0 ∧ HilbertEllipse.OnEllipse 1 0 ∧
    ¬∃ D E G : ℝ, HilbertEllipse.OnCircle D E G (-1) 0 ∧ HilbertEllipse.OnCircle D E G 1 0 ∧
      HilbertEllipse.OnCircle D E G (3 / 2) 0 :=
  ⟨HilbertEllipse.xaxis_cuts.1, HilbertEllipse.xaxis_cuts.2, HilbertEllipse.xaxis_no_circle⟩

theorem s23_fig40_hilbert :
    ¬(∃ x y : ℝ, y = 0 ∧ HilbertEllipse.lineY x y ∧ HilbertEllipse.lineT x y) ∧
    (HilbertEllipse.lineY (-1 / 6) 0 ∧ ∀ x : ℝ, HilbertEllipse.lineY x 0 → x = -1 / 6) ∧
    HilbertEllipse.lineT (-26 / 75) 0 :=
  HilbertEllipse.fig40_joining_lines

/-!
## [s23.not_part_of_space] The new geometry is not part of a geometry of space

*(§ 23)*

> This new geometry serves at the same time as an example of a plane geometry in which the axioms I, 1–2, II–III, IV, 1–5, V all hold, but which cannot be considered as a part of a geometry of space.

**Lean reading.** `IsPartOfSpace P L`: there is a space geometry satisfying I, II, III
(`SpaceOrder`, `SpaceParallels`, as in § 22) with a plane `α` and bijections of the points and the
lines of the given plane geometry onto the points and the lines of `α` preserving and reflecting
incidence and betweenness. Hilbert's reason is § 22: Desargues's theorem holds in every plane of a
space satisfying I–III (`SpaceDesargues`). This premise is proved here, from I and III only
(`spaceDesargues_holds`, by `SpaceDesargues.direct` in `NonDesarguesAux6`: the classical proof
leaving the plane through a point `S ∉ α`, with parallel planes). Hence every plane geometry which is
part of such a space satisfies the direct part of Theorem 32 (`desarguesParallel_of_partOfSpace`),
and the Moulton plane is not (`moulton_not_partOfSpace`); `moulton_not_partOfSpace_of` is the
earlier conditional form.

**Status.** proved
-/

/-- The plane geometry `(P, L)` is part of a geometry of space satisfying I, II, III. This is the
notion `PartOfSpace` of § 22 (`Desargues.lean`), written out for types in `Type`; this file does not
import that one. -/
def IsPartOfSpace (P : Type) (L : Type) [HasLines P L] [HasBetween P] : Prop :=
  ∃ (P' : Type) (L' : Type) (Pl' : Type) (_ : HasLines P' L') (_ : HasPlanes P' Pl')
    (_ : HasBetween P'), SpaceOrder P' L' Pl' ∧ SpaceParallels P' L' Pl' ∧
    ∃ (α : Pl') (f : P → P') (g : L → L'), Function.Injective f ∧ Function.Injective g ∧
      (∀ A, f A ∈ α) ∧ (∀ a, LiesInPlane (Point := P') (g a) α) ∧
      (∀ A', A' ∈ α → ∃ A, f A = A') ∧ (∀ a', LiesInPlane (Point := P') a' α → ∃ a, g a = a') ∧
      (∀ A a, f A ∈ g a ↔ A ∈ a) ∧ (∀ A B C, Between (f A) (f B) (f C) ↔ Between A B C)

/-- Desargues's theorem (direct part) in every plane of every space geometry satisfying I–III
(the claim of § 22 that Theorem 32 is a consequence of I–III). -/
def SpaceDesargues : Prop :=
  ∀ (P' : Type) (L' : Type) (Pl' : Type) [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P'],
    SpaceOrder P' L' Pl' → SpaceParallels P' L' Pl' → ∀ α : Pl',
    ∀ (A B C A' B' C' : P') (a b c a' b' c' p q r : L'),
      A ∈ α → B ∈ α → C ∈ α → A' ∈ α → B' ∈ α → C' ∈ α →
      LiesInPlane (Point := P') a α → LiesInPlane (Point := P') b α →
      LiesInPlane (Point := P') c α → LiesInPlane (Point := P') a' α →
      LiesInPlane (Point := P') b' α → LiesInPlane (Point := P') c' α →
      LiesInPlane (Point := P') p α → LiesInPlane (Point := P') q α →
      LiesInPlane (Point := P') r α →
      ¬Collinear A B C → ¬Collinear A' B' C' →
      B ∈ a → C ∈ a → C ∈ b → A ∈ b → A ∈ c → B ∈ c →
      B' ∈ a' → C' ∈ a' → C' ∈ b' → A' ∈ b' → A' ∈ c' → B' ∈ c' →
      ¬Meets (Point := P') a a' → ¬Meets (Point := P') b b' → ¬Meets (Point := P') c c' →
      A ∈ p → A' ∈ p → B ∈ q → B' ∈ q → C ∈ r → C' ∈ r →
      (∃ O : P', O ∈ p ∧ O ∈ q ∧ O ∈ r) ∨
        (¬Meets (Point := P') p q ∧ ¬Meets (Point := P') q r ∧ ¬Meets (Point := P') p r)

open Moulton in
/-- **The Moulton plane is not part of a space geometry satisfying I–III**, granted that Desargues's
theorem holds in the planes of such a space (§ 22). -/
theorem moulton_not_partOfSpace_of (hD : SpaceDesargues) : ¬IsPartOfSpace Pt Ln := by
  rintro ⟨P', L', Pl', iL, iP, iB, hO, hPar, α, f, g, hf, -, hfα, hgα, hfs, hgs, hinc, -⟩
  obtain ⟨n1, n2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pa, pb, pc, p1, p2, q1, q2,
    r1, r2, hno, hqr⟩ := desargues_config
  have : SpaceConnection P' L' Pl' := hO.toSpaceConnection
  -- transport of non-collinearity and of parallelism
  have hcol : ∀ X Y Z : Pt, X ≠ Y → ¬Collinear X Y Z → ¬Collinear (f X) (f Y) (f Z) := by
    rintro X Y Z hXY hn ⟨l', hX, hY, hZ⟩
    have hl : LiesInPlane (Point := P') l' α :=
      liesInPlane_of_mem (fun e => hXY (hf e)) hX hY (hfα X) (hfα Y)
    obtain ⟨l, rfl⟩ := hgs l' hl
    exact hn ⟨l, (hinc X l).1 hX, (hinc Y l).1 hY, (hinc Z l).1 hZ⟩
  have hpar : ∀ l m : Ln, ¬Meets (Point := Pt) l m → ¬Meets (Point := P') (g l) (g m) := by
    rintro l m hn ⟨X', hl, hm⟩
    obtain ⟨X, rfl⟩ := hfs X' (hgα l X' hl)
    exact hn ⟨X, (hinc X l).1 hl, (hinc X m).1 hm⟩
  have hAB : dA ≠ dB := by norm_num [dA, dB, Pt.ext_iff]
  have hAB' : dA' ≠ dB' := by norm_num [dA', dB', Pt.ext_iff]
  have hi : ∀ (X : Pt) (l : Ln), X ∈ l → f X ∈ g l := fun X l h => (hinc X l).2 h
  rcases hD P' L' Pl' hO hPar α (f dA) (f dB) (f dC) (f dA') (f dB') (f dC') (g la) (g lb) (g lc)
    (g la') (g lb') (g lc') (g lp) (g lq) (g lr) (hfα _) (hfα _) (hfα _) (hfα _) (hfα _) (hfα _)
    (hgα _) (hgα _) (hgα _) (hgα _) (hgα _) (hgα _) (hgα _) (hgα _) (hgα _)
    (hcol _ _ _ hAB n1) (hcol _ _ _ hAB' n2) (hi _ _ h1) (hi _ _ h2) (hi _ _ h3) (hi _ _ h4)
    (hi _ _ h5) (hi _ _ h6) (hi _ _ h7) (hi _ _ h8) (hi _ _ h9) (hi _ _ h10) (hi _ _ h11)
    (hi _ _ h12) (hpar _ _ pa) (hpar _ _ pb) (hpar _ _ pc) (hi _ _ p1) (hi _ _ p2) (hi _ _ q1)
    (hi _ _ q2) (hi _ _ r1) (hi _ _ r2) with h | h
  · obtain ⟨O', hp, hq, hr⟩ := h
    obtain ⟨O, rfl⟩ := hfs O' (hgα _ O' hp)
    exact hno ⟨O, (hinc O _).1 hp, (hinc O _).1 hq, (hinc O _).1 hr⟩
  · obtain ⟨Z, hq, hr⟩ := hqr
    exact h.2.1 ⟨f Z, hi _ _ hq, hi _ _ hr⟩

/-- **§ 22's premise, proved**: the direct part of Desargues's theorem holds in every plane of every
space geometry satisfying I and III (`SpaceDesargues.direct`; order is not used). -/
theorem spaceDesargues_holds : SpaceDesargues :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hA' hB' hC' _ _ _ _ _ _ _ _ _
    nABC nABC' hBa hCa hCb hAb hAc hBc hBa' hCa' hCb' hAb' hAc' hBc' pa pb pc hAp hA'p hBq hB'q
    hCr hC'r =>
  SpaceDesargues.direct hA hB hC hA' hB' hC' nABC nABC' hBa hCa hCb hAb hAc hBc hBa' hCa' hCb' hAb'
    hAc' hBc' pa pb pc hAp hA'p hBq hB'q hCr hC'r

/-- **Desargues's theorem is a necessary condition** for a plane geometry to be part of a space
geometry satisfying I–III (§ 22, used in § 23). -/
theorem desarguesParallel_of_partOfSpace {P : Type} {L : Type} [HasLines P L] [HasBetween P]
    (h : IsPartOfSpace P L) : DesarguesParallel P := by
  obtain ⟨P', L', Pl', iL, iP, iB, -, hPar, α, f, g, hf, -, hfα, hgα, hfs, hgs, hinc, -⟩ := h
  have : SpaceConnection P' L' Pl' := hPar.toSpaceConnection
  intro A B C A' B' C' a b c a' b' c' p q r nABC nABC' hBa hCa hCb hAb hAc hBc hBa' hCa' hCb' hAb'
    hAc' hBc' pa pb pc hAp hA'p hBq hB'q hCr hC'r
  have hcol : ∀ X Y Z : P, X ≠ Y → ¬Collinear X Y Z → ¬Collinear (f X) (f Y) (f Z) := by
    rintro X Y Z hXY hn ⟨l', hX, hY, hZ⟩
    have hl : LiesInPlane (Point := P') l' α :=
      liesInPlane_of_mem (fun e => hXY (hf e)) hX hY (hfα X) (hfα Y)
    obtain ⟨l, rfl⟩ := hgs l' hl
    exact hn ⟨l, (hinc X l).1 hX, (hinc Y l).1 hY, (hinc Z l).1 hZ⟩
  have hpar : ∀ l m : L, ¬Meets (Point := P) l m → ¬Meets (Point := P') (g l) (g m) := by
    rintro l m hn ⟨X', hl, hm⟩
    obtain ⟨X, rfl⟩ := hfs X' (hgα l X' hl)
    exact hn ⟨X, (hinc X l).1 hl, (hinc X m).1 hm⟩
  have hback : ∀ l m : L, ¬Meets (Point := P') (g l) (g m) → ¬Meets (Point := P) l m :=
    fun l m hn ⟨X, hl, hm⟩ => hn ⟨f X, (hinc X l).2 hl, (hinc X m).2 hm⟩
  have hAB : A ≠ B := fun e => nABC ⟨a, e ▸ hBa, hBa, hCa⟩
  have hAB' : A' ≠ B' := fun e => nABC' ⟨a', e ▸ hBa', hBa', hCa'⟩
  have hi : ∀ (X : P) (l : L), X ∈ l → f X ∈ g l := fun X l h => (hinc X l).2 h
  rcases SpaceDesargues.direct (hfα A) (hfα B) (hfα C) (hfα A') (hfα B') (hfα C')
    (hcol _ _ _ hAB nABC) (hcol _ _ _ hAB' nABC') (hi _ _ hBa) (hi _ _ hCa) (hi _ _ hCb)
    (hi _ _ hAb) (hi _ _ hAc) (hi _ _ hBc) (hi _ _ hBa') (hi _ _ hCa') (hi _ _ hCb') (hi _ _ hAb')
    (hi _ _ hAc') (hi _ _ hBc') (hpar _ _ pa) (hpar _ _ pb) (hpar _ _ pc) (hi _ _ hAp)
    (hi _ _ hA'p) (hi _ _ hBq) (hi _ _ hB'q) (hi _ _ hCr) (hi _ _ hC'r) with h | h
  · obtain ⟨O', hp, hq, hr⟩ := h
    obtain ⟨O, rfl⟩ := hfs O' (hgα _ O' hp)
    exact Or.inl ⟨O, (hinc O _).1 hp, (hinc O _).1 hq, (hinc O _).1 hr⟩
  · exact Or.inr ⟨hback _ _ h.1, hback _ _ h.2.1, hback _ _ h.2.2⟩

/-- **The Moulton plane is not part of a space geometry satisfying I–III.** -/
theorem moulton_not_partOfSpace : ¬IsPartOfSpace Moulton.Pt Moulton.Ln :=
  fun h => moulton_not_desarguesParallel (desarguesParallel_of_partOfSpace h)

end HilbertFoundations
