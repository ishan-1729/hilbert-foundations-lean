import Mathlib

/-!
# The elements of geometry and the five groups of axioms (§§ 1–3, 5, 6, 8)

(with the notions of § 4 that the axioms of congruence need: sides of a point, half-rays, sides of
a line; units `s4.side_of_point`, `s4.half_ray`, `s4.side_of_line` live here, not in Order.lean.)

David Hilbert, *The Foundations of Geometry*, authorized translation by E. J. Townsend (Open Court,
Chicago, 1902) of the first German edition (*Grundlagen der Geometrie*, 1899), with the additions
Hilbert made for the French edition (Project Gutenberg #17384). The full text is in
`data/foundations.json`.

This file fixes the axiom system of the book. Every other file of the project imports it, proves
Hilbert's theorems from these axioms, or builds models of them. The axioms are those of *this*
edition, which differ from the later editions: II, 1 carries no distinctness clause, II, 4 is the
four-point axiom (later shown redundant by E. H. Moore), IV, 1 and IV, 4 contain "every segment
(angle) is congruent to itself", IV, 6 concludes the congruence of *both* remaining angles, V is
Archimedes's axiom stated with "equal" segments, and the Axiom of Completeness is a remark added
for the French edition.

Each statement Hilbert makes is a *unit*, a block

    ## [id] Title
    *(§ N)*
    > Hilbert's words (verbatim, cut with … when long)
    **Lean reading.** how it is formalized
    **Status.** what is proved

followed by its Lean declarations.

## The primitive notions

* **Points, straight lines, planes** are three types `Point`, `Line`, `Plane`. Lines and planes are
  primitive objects, *not* sets of points.
* **"Lies on"** is a relation `HasLines.LiesOn : Point → Line → Prop`, written `A ∈ a`, and
  **"lies in"** is `HasPlanes.LiesIn : Point → Plane → Prop`, written `A ∈ α`. In `HasLines Point
  Line` and `HasPlanes Point Plane` the line and plane types are `outParam`s, so that `Collinear A B
  C` or `Coplanar A B C D` find them from the point type. A model must use different types for its
  lines and its planes (otherwise the two `Membership` instances clash).
* **"Between"** is a ternary relation `Between A B C` ("`B` lies between `A` and `C`").
* **"Congruent"** is `SegCong A B A' B'` (the segment `AB` is congruent to `A'B'`) and `AngCong A O B
  A' O' B'` (`∠AOB ≡ ∠A'O'B'`, the angle with vertex `O` and sides the half-rays `OA`, `OB`). These
  are relations on tuples of points; that they are relations on *segments* (unordered pairs) and on
  *angles* (unordered pairs of half-rays) is expressed by the fields `segCong_swap` and
  `angCong_wd` (units `s6.segment_congruence`, `s6.angle`).
* The signature classes `HasLines`, `HasPlanes`, `HasBetween`, `HasSegCong`, `HasAngCong` carry the
  data; the axiom classes below are `Prop`-valued mixins over them.

**Degenerate tuples are junk.** Hilbert's relations are only meaningful on genuine objects: a segment
has two distinct extremities, an angle has non-collinear `A, O, B`. Every axiom is quantified only
over genuine objects (with the distinctness / non-collinearity hypotheses Hilbert leaves tacit), so
the values of `SegCong`, `AngCong` on degenerate tuples are unconstrained; the only exception is
`segCong_swap`, which holds for all tuples. Betweenness, in contrast, is not junk-tolerant:
`between_onLine` says that `Between A B C` only holds for three distinct points of a line (unit
`s3.between`).

## The axioms and the class hierarchy

Every axiom is a standalone `Prop`-valued definition (`AxiomI1`, …, `AxiomV`, `PlaneComplete`,
`SpaceComplete`), so that models can be checked against single axioms and independence statements
("IV 6 fails", "II 4 follows from the others") can be formulated. The classes have one field per
axiom, whose type is that definition (fields `ax_I1`, …, `ax_V`); only I 7, IV 1 and IV 4 have their
clauses as separate fields, and the linear presuppositions `between_onLine`, `segCong_swap`,
`angCong_wd` are fields of the first class that uses the relation.

| class | extends | own fields | Hilbert |
|---|---|---|---|
| `Connection P L` | – | `ax_I1`, `ax_I2`, `ax_I7_line` | I 1–2, I 7 (lines) |
| `PlaneConnection P L` | `Connection` | `ax_I7_noncollinear` | group I of plane geometry |
| `SpaceConnection P L Pl` | `Connection` | `ax_I3`–`ax_I6`, `ax_I7_plane`, `ax_I7_space` | I 1–7 |
| `LineOrder P L` | `Connection` | `between_onLine`, `ax_II1`–`ax_II4` | linear axioms II 1–4 |
| `PlaneOrder P L` | `PlaneConnection`, `LineOrder` | `ax_II5` | I, II in the plane |
| `SpaceOrder P L Pl` | `SpaceConnection`, `LineOrder` | `ax_II5` | I, II in space |
| `PlaneParallels P L` | `PlaneConnection` | `ax_III` | III in the plane |
| `SpaceParallels P L Pl` | `SpaceConnection` | `ax_III` | III in each plane |
| `SegmentCongruence P L` | `LineOrder` | `segCong_swap`, `ax_IV1`, `ax_IV1_refl`, `ax_IV2`, `ax_IV3` | linear axioms IV 1–3 |
| `AngleCongruence P L` | `LineOrder` | `angCong_wd`, `ax_IV4_refl`, `ax_IV5` | the parts of IV 4–5 not involving planes |
| `PlaneAngleCongruence P L` | `PlaneOrder`, `AngleCongruence` | `ax_IV4` | IV 4–5 in the plane |
| `SpaceAngleCongruence P L Pl` | `SpaceOrder`, `AngleCongruence` | `ax_IV4` | IV 4–5 in space |
| `TriangleCongruence P L` | `SegmentCongruence`, `AngleCongruence` | `ax_IV6` | IV 6 |
| `PlaneCongruence P L` | `PlaneAngleCongruence`, `TriangleCongruence` | – | I, II, IV in the plane |
| `SpaceCongruence P L Pl` | `SpaceAngleCongruence`, `TriangleCongruence` | – | I, II, IV in space |
| `Archimedes P L` | `LineOrder` | `ax_V` | V (with congruence as equality) |
| `PlaneGeometry P L` | `PlaneParallels`, `PlaneCongruence`, `Archimedes` | – | groups I–V, plane |
| `SpaceGeometry P L Pl` | `SpaceParallels`, `SpaceCongruence`, `Archimedes` | – | groups I–V, space |

Hilbert's subsets are combinations of these mixins, e.g. Theorem 33's "axioms I 1–2, II–III,
IV 1–5, V" (a plane geometry) is `[PlaneOrder P L] [PlaneParallels P L] [SegmentCongruence P L]
[PlaneAngleCongruence P L] [Archimedes P L]`, and the geometry of § 11, in which IV 6 fails, is an
instance of everything except `TriangleCongruence`. Archimedes's axiom with another notion of
"equal" segments (Chapter V, § 24) is `ArchimedesWith Point Equal`.

## Plane geometry and space geometry

Hilbert proves most of his theorems for a plane `α` inside space, and the geometries of Chapters
III–VI are plane geometries. Both are modelled:

* *Linear* axioms (I 1–2 and the line clause of I 7, II 1–4, IV 1–3, V) do not mention planes, and
  their classes (`Connection`, `LineOrder`, `SegmentCongruence`, `Archimedes`, and the plane-free
  parts of IV 4–6 in `AngleCongruence`, `TriangleCongruence`) are shared by both.
* *Plane* axioms (II 5, III, the laying-off clause of IV 4) have a plane version over `(Point, Line)`,
  where the plane is the whole set of points, and a space version over `(Point, Line, Plane)`, where
  the axiom is stated inside an arbitrary plane `α` ("lying in the plane `ABC`", "in a plane `α`",
  "in the plane `α'`"). Group I of plane geometry is I 1–2 together with the two clauses of I 7 that
  make sense in a plane (every line has two points; there are three non-collinear points).
* A space geometry is *not* a plane geometry, but each of its planes is: the points and lines of a
  plane `α` (the subtypes `{A // A ∈ α}` and `{a // LiesInPlane a α}`) satisfy the plane classes.
  This restriction is constructed in later files where it is needed (for example
  `DesAlg.restrictPlaneInSpace`), which then transfer plane theorems to the planes of space.

## Status vocabulary

* `proved`: the statement, read as in the Lean reading, is formalized at full strength and proved.
* `proved (reading)`: Hilbert's words admit more than one precise reading; the Lean reading says
  which one is formalized and why.
* `proved (corrected)`: as printed, the claim is false or imprecise; the corrected statement is
  proved, and the Lean reading says exactly what is wrong.
* `definition`: a definition or an axiom (axioms are definitions of `Prop`s and class fields).
* `remark`: prose without mathematical content to prove.
* `stated (open here)`: the claim is formalized as a `Prop` and only the partial results named in
  the Lean reading are proved. It is never stated with `sorry`.

## House rules for later files

* A result assumes exactly the axiom classes Hilbert uses for it (or fewer), never more.
* No axiom is ever strengthened: the classes below are the axiom system, and a later file that needs
  a stronger form must derive it.
* Complete proofs only: no `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `unsafe`.
* The Lean declarations of a unit follow its block; the quote is verbatim from
  `data/foundations.json`.

## Practical notes

* The class projections (`LineOrder.ax_II3`, `AngleCongruence.angCong_wd`, …) take the line (and
  plane) type as an implicit argument that is only determined by unification, so when the expected
  type does not mention it write `LineOrder.ax_II3 (Line := Line) A B C …`, or use the API lemmas
  (`between_symm`, `exists_line`, `segCong_refl`, `angCong_swap_left`, …), whose instance arguments
  are found from the point type.
* In a `section` with `variable [hO : LineOrder Point Line]`, a theorem whose statement only
  mentions points needs `include hO` (otherwise the instance is not available in the proof).
* A projection whose type mentions neither the point nor the line type (for instance
  `SpaceConnection.ax_I7_plane α`, whose type `AxiomI7Plane Point` is applied to a plane) also
  needs `(Point := P)`.
* Line and plane types of a model must not already carry a `Membership Point _` instance of their
  own: do not take `Set Point`, `Finset Point`, `AffineSubspace …` or any `SetLike` type directly as
  the type of lines, but a structure or a subtype of it (`{s : Set P // …}`), whose membership then
  comes only from `HasLines` / `HasPlanes`. Otherwise `A ∈ a` has two competing instances.
* The restriction of a space geometry to a plane `α` is the instance
  `HasLines {A : P // A ∈ α} {a : L // LiesInPlane a α}` (with `A ∈ a` meaning `(A : P) ∈ (a : L)`);
  that it is a `PlaneConnection` follows from I 1, I 2, I 5 and the line and plane clauses of I 7.
  The higher classes transfer in the same way, using the space versions of II 5, III and IV 4.
-/

namespace HilbertFoundations

universe u v w

/-!
## [s1.elements] Points, straight lines and planes

*(§ 1)*

> Let us consider three distinct systems of things. The things composing the first system, we will call *points* and designate them by the letters $A$, $B$, $C$,\ldots; those of the second, we will call *straight lines* … and those of the third system, we will call *planes* … The points are called the *elements of linear geometry*; the points and straight lines, the *elements of plane geometry*; and the points, lines, and planes, the *elements of the geometry of space* or the *elements of space*.

**Lean reading.** The three systems are three types `Point`, `Line`, `Plane`; lines and planes are
primitive, not sets of points. The elements of plane geometry are the pair `(Point, Line)` with
`HasLines Point Line`, the elements of space the triple `(Point, Line, Plane)` with in addition
`HasPlanes Point Plane`. The relation "`A` lies upon `a`" (`HasLines.LiesOn`) and "`A` lies in `α`"
(`HasPlanes.LiesIn`) are written `A ∈ a`, `A ∈ α` through `Membership` instances. Line and plane
types are `outParam`s, so a point type has one system of lines and planes (a model reusing a point
type with other lines uses a type synonym).

**Status.** definition
-/

/-- **Points and straight lines** (§ 1). `HasLines Point Line` provides the relation "the point `A`
lies upon the straight line `a`" (§ 2), written `A ∈ a`. -/
class HasLines (Point : Type u) (Line : outParam (Type v)) where
  /-- `LiesOn A a`: the point `A` lies upon the straight line `a`; written `A ∈ a`. -/
  LiesOn : Point → Line → Prop

/-- **Points and planes** (§ 1). `HasPlanes Point Plane` provides the relation "the point `A` lies
in the plane `α`" (§ 2), written `A ∈ α`. -/
class HasPlanes (Point : Type u) (Plane : outParam (Type w)) where
  /-- `LiesIn A α`: the point `A` lies in the plane `α`; written `A ∈ α`. -/
  LiesIn : Point → Plane → Prop

set_option synthInstance.checkSynthOrder false in
instance instMembershipLine {Point : Type u} {Line : Type v} [HasLines Point Line] :
    Membership Point Line :=
  ⟨fun a A => HasLines.LiesOn A a⟩

set_option synthInstance.checkSynthOrder false in
instance instMembershipPlane {Point : Type u} {Plane : Type w} [HasPlanes Point Plane] :
    Membership Point Plane :=
  ⟨fun α A => HasPlanes.LiesIn A α⟩

theorem liesOn_iff_mem {Point : Type u} {Line : Type v} [HasLines Point Line] {A : Point}
    {a : Line} : HasLines.LiesOn A a ↔ A ∈ a := Iff.rfl

theorem liesIn_iff_mem {Point : Type u} {Plane : Type w} [HasPlanes Point Plane] {A : Point}
    {α : Plane} : HasPlanes.LiesIn A α ↔ A ∈ α := Iff.rfl

/-!
## [s1.relations] The relations between the elements

*(§ 1)*

> We think of these points, straight lines, and planes as having certain mutual relations, which we indicate by means of such words as “are situated,” “between,” “parallel,” “congruent,” “continuous,” etc. The complete and exact description of these relations follows as a consequence of the *axioms of geometry*.

**Lean reading.** "Are situated" is the incidence of `s1.elements`. "Between" is a ternary relation
on points (`HasBetween`), "congruent" a relation on segments (`HasSegCong`, on four points) and on
angles (`HasAngCong`, on six points: `AngCong A O B A' O' B'` is `∠AOB ≡ ∠A'O'B'`). "Parallel" is
defined from incidence (`Parallel`, `ParallelIn`, after unit `ax.III`), and "continuous" has no relation of its own:
it is expressed by axiom V and the Axiom of Completeness. No property of these relations is assumed
here; everything is in the axioms.

**Status.** definition
-/

/-- **Between** (§ 3). `Between A B C`: the point `B` lies between `A` and `C`. -/
class HasBetween (Point : Type u) where
  /-- `Between A B C`: the point `B` lies between the points `A` and `C`. -/
  Between : Point → Point → Point → Prop

/-- **Congruence of segments** (§ 6). `SegCong A B A' B'`: the segment `AB` is congruent to the
segment `A'B'`, `AB ≡ A'B'`. -/
class HasSegCong (Point : Type u) where
  /-- `SegCong A B A' B'`: `AB ≡ A'B'`. -/
  SegCong : Point → Point → Point → Point → Prop

/-- **Congruence of angles** (§ 6). `AngCong A O B A' O' B'`: the angle `∠AOB` (vertex `O`, sides the
half-rays from `O` through `A` and through `B`) is congruent to `∠A'O'B'`. -/
class HasAngCong (Point : Type u) where
  /-- `AngCong A O B A' O' B'`: `∠AOB ≡ ∠A'O'B'`. -/
  AngCong : Point → Point → Point → Point → Point → Point → Prop

export HasBetween (Between)
export HasSegCong (SegCong)
export HasAngCong (AngCong)

/-!
## [s1.groups] The five groups of axioms

*(§ 1)*

> These axioms may be arranged in five groups. Each of these groups expresses, by itself, certain related fundamental facts of our intuition. We will name these groups as follows: … I,&1–7.&Axioms of *connection*.\\ II,&1–5.&Axioms of *order*.\\ III.&&Axiom of *parallels* (Euclid's axiom).\\ IV,&1–6.&Axioms of *congruence*.\\ V.&&Axiom of *continuity* (Archimedes's axiom).

**Lean reading.** The groups are the classes of this file (see the table in the module docstring):
group I is `Connection` / `PlaneConnection` / `SpaceConnection`, group II `LineOrder` (II 1–4) and
`PlaneOrder` / `SpaceOrder` (II 5), group III `PlaneParallels` / `SpaceParallels`, group IV
`SegmentCongruence` (IV 1–3), `AngleCongruence`, `PlaneAngleCongruence` / `SpaceAngleCongruence`
(IV 4–5), `TriangleCongruence` (IV 6), group V `Archimedes`.

**Status.** remark
-/

/-! ### Basic notions of incidence -/

section IncidenceDefs

variable {Point : Type u} {Line : Type v} {Plane : Type w}

/-- Three points are **collinear** ("lie in the same straight line") if some line contains all
three. -/
def Collinear [HasLines Point Line] (A B C : Point) : Prop :=
  ∃ a : Line, A ∈ a ∧ B ∈ a ∧ C ∈ a

/-- Four points are **coplanar** if some plane contains all four. -/
def Coplanar [HasPlanes Point Plane] (A B C D : Point) : Prop :=
  ∃ α : Plane, A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ D ∈ α

/-- Two lines **meet** ("intersect", "have a point in common") if some point lies on both. -/
def Meets [Membership Point Line] (a b : Line) : Prop :=
  ∃ P : Point, P ∈ a ∧ P ∈ b

theorem Collinear.swap12 [HasLines Point Line] {A B C : Point} (h : Collinear A B C) :
    Collinear B A C := by
  obtain ⟨a, hA, hB, hC⟩ := h; exact ⟨a, hB, hA, hC⟩

theorem Collinear.swap23 [HasLines Point Line] {A B C : Point} (h : Collinear A B C) :
    Collinear A C B := by
  obtain ⟨a, hA, hB, hC⟩ := h; exact ⟨a, hA, hC, hB⟩

theorem Collinear.swap13 [HasLines Point Line] {A B C : Point} (h : Collinear A B C) :
    Collinear C B A := by
  obtain ⟨a, hA, hB, hC⟩ := h; exact ⟨a, hC, hB, hA⟩

end IncidenceDefs

/-! ## Group I: Axioms of connection (§ 2) -/

section GroupI

variable (Point : Type u) {Line : Type v} {Plane : Type w}

/-!
## [ax.I1] Axiom I, 1

*(§ 2)*

> *Two distinct points $A$ and $B$ always completely determine a straight line $a$. We write $AB = a$ or $BA = a$*.

**Lean reading.** `AxiomI1`: for all points `A ≠ B` there is a line `a` with `A ∈ a` and `B ∈ a`.
"Completely determine" already suggests uniqueness, but the uniqueness of the line is what I 2
asserts (its "that is" clause only makes sense if `AB = a` means "`A`, `B` lie on `a`"), so, as in
all later editions, I 1 is read as the existence and I 2 as the uniqueness of the line. The notation
`AB` for the line is `line A B h` (`h : A ≠ B`), defined by choice from I 1 and characterised by I 2.

**Status.** definition
-/

/-- **Axiom I, 1.** Two distinct points lie on a common line. -/
def AxiomI1 [HasLines Point Line] : Prop :=
  ∀ A B : Point, A ≠ B → ∃ a : Line, A ∈ a ∧ B ∈ a

/-!
## [s2.lies_upon] "Lies upon", "goes through"

*(§ 2)*

> Instead of “determine,” we may also employ other forms of expression; for example, we may say $A$ “lies upon” $a$, $A$ “is a point of” $a$, $a$ “goes through” $A$ “and through” $B$, $a$ “joins” $A$ “and” or “with” $B$, etc. If $A$ lies upon $a$ and at the same time upon another straight line $b$, we make use also of the expression: “The straight lines” $a$ “and” $b$ “have the point $A$ in common,” etc.

**Lean reading.** All these expressions are `A ∈ a` (`HasLines.LiesOn A a`). "`a` and `b` have a
point in common" is `Meets a b`.

**Status.** definition
-/

/-!
## [ax.I2] Axiom I, 2

*(§ 2)*

> *Any two distinct points of a straight line completely determine that line; that is, if $AB = a$ and $AC=a$, where $B \neq C$, then is also $BC=a$*.

**Lean reading.** `AxiomI2`: if two distinct points `A ≠ B` lie on the lines `a` and `b`, then
`a = b`. This is the first sentence ("any two distinct points of a straight line completely
determine that line"). The "that is" clause, read literally with `AB = a` meaning "`A` and `B` lie on
`a`", is a tautology (`B`, `C` lie on `a` by hypothesis); read with `AB = a` meaning "`a` is *the*
line determined by `A` and `B`", it says that the line determined by two of its points does not
depend on the two points, i.e. uniqueness again. The uniqueness reading is the one of all later
editions ("there exists no more than one line containing `A` and `B`").

**Status.** definition
-/

/-- **Axiom I, 2.** Two distinct points lie on at most one line. -/
def AxiomI2 [HasLines Point Line] : Prop :=
  ∀ (A B : Point) (a b : Line), A ≠ B → A ∈ a → B ∈ a → A ∈ b → B ∈ b → a = b

/-!
## [ax.I3] Axiom I, 3

*(§ 2)*

> *Three points $A$, $B$, $C$ not situated in the same straight line always completely determine a plane $\alpha$. We write $ABC=\alpha$*.

**Lean reading.** `AxiomI3`: for non-collinear `A`, `B`, `C` there is a plane containing all three.
As for I 1 / I 2, existence is assigned to I 3 and uniqueness to I 4. "Not situated in the same
straight line" is `¬Collinear A B C` (in particular `A`, `B`, `C` are then distinct, given I 1).

**Status.** definition
-/

/-- **Axiom I, 3.** Three non-collinear points lie in a common plane. -/
def AxiomI3 [HasLines Point Line] [HasPlanes Point Plane] : Prop :=
  ∀ A B C : Point, ¬Collinear A B C → ∃ α : Plane, A ∈ α ∧ B ∈ α ∧ C ∈ α

/-!
## [s2.lie_in] "Lie in", "are points of" a plane

*(§ 2)*

> We employ also the expressions: $A$, $B$, $C$, “lie in” $\alpha$; $A$, $B$, $C$ “are points of” $\alpha$, etc.

**Lean reading.** Both expressions are `A ∈ α` (`HasPlanes.LiesIn A α`), as "lies upon" is `A ∈ a`
for lines (`s2.lies_upon`). Four points lying in one plane are `Coplanar A B C D`.

**Status.** definition
-/

/-!
## [ax.I4] Axiom I, 4

*(§ 2)*

> *Any three points $A$, $B$, $C$ of a plane $\alpha$, which do not lie in the same straight line, completely determine that plane*.

**Lean reading.** `AxiomI4`: if non-collinear `A`, `B`, `C` lie in the planes `α` and `β`, then
`α = β`.

**Status.** definition
-/

/-- **Axiom I, 4.** Three non-collinear points lie in at most one plane. -/
def AxiomI4 [HasLines Point Line] [HasPlanes Point Plane] : Prop :=
  ∀ (A B C : Point) (α β : Plane), ¬Collinear A B C →
    A ∈ α → B ∈ α → C ∈ α → A ∈ β → B ∈ β → C ∈ β → α = β

/-!
## [ax.I5] Axiom I, 5

*(§ 2)*

> *If two points $A$, $B$ of a straight line $a$ lie in a plane $\alpha$, then every point of $a$ lies in $a$*.

**Lean reading.** The last words are a misprint of the transcription: "every point of `a` lies in
`α`" (German: "so liegt jeder Punkt von `a` in `α`"; the LaTeX source has `$a$` for `$\alpha$`).
`AxiomI5`: if two *distinct* points `A ≠ B` of `a` lie in `α`, then every point of `a` lies in `α`.
Distinctness is tacit ("two points") and necessary: with `A = B` the statement would put every line
through a point of `α` into `α`.

**Status.** definition
-/

/-- **Axiom I, 5.** If two distinct points of a line lie in a plane, every point of the line does. -/
def AxiomI5 [HasLines Point Line] [HasPlanes Point Plane] : Prop :=
  ∀ (A B : Point) (a : Line) (α : Plane), A ≠ B → A ∈ a → B ∈ a → A ∈ α → B ∈ α →
    ∀ P : Point, P ∈ a → P ∈ α

/-!
## [s2.line_in_plane] A straight line lies in a plane

*(§ 2)*

> In this case we say: “The straight line a lies in the plane $\alpha$,” etc.

**Lean reading.** `LiesInPlane a α`: every point of `a` lies in `α`. Hilbert's phrase refers to the
situation of I 5 (two distinct points of `a` lie in `α`), which by I 5 is the same thing whenever `a`
has two points (I 7); `liesInPlane_of_mem` is this direction of the equivalence.

**Status.** definition
-/

/-- The straight line `a` **lies in** the plane `α`: every point of `a` lies in `α`. -/
def LiesInPlane {Point : Type u} [Membership Point Line] [Membership Point Plane]
    (a : Line) (α : Plane) : Prop :=
  ∀ P : Point, P ∈ a → P ∈ α

/-!
## [ax.I6] Axiom I, 6

*(§ 2)*

> *If two planes $\alpha$, $\beta$ have a point $A$ in common, then they have at least a second point $B$ in common.*

**Lean reading.** `AxiomI6`: if `α ≠ β` have the point `A` in common, they have a point `B ≠ A` in
common. "Two planes" is read as two *distinct* planes (the weaker reading; for `α = β` the statement
follows from the plane clause of I 7 anyway).

**Status.** definition
-/

/-- **Axiom I, 6.** Two distinct planes with a common point have a second common point. -/
def AxiomI6 [HasPlanes Point Plane] : Prop :=
  ∀ (α β : Plane) (A : Point), α ≠ β → A ∈ α → A ∈ β → ∃ B : Point, B ≠ A ∧ B ∈ α ∧ B ∈ β

/-!
## [ax.I7] Axiom I, 7

*(§ 2)*

> *Upon every straight line there exist at least two points, in every plane at least three points not lying in the same straight line, and in space there exist at least four points not lying in a plane.*

**Lean reading.** Three clauses, three definitions: `AxiomI7Line` (every line contains two distinct
points), `AxiomI7Plane` (every plane contains three non-collinear points), `AxiomI7Space` (there are
four points not all in one plane: `¬Coplanar A B C D`); `AxiomI7` is their conjunction. In plane
geometry the only plane is the set of all points, and the plane clause becomes
`ExistsNoncollinear` (there are three non-collinear points). Read literally, as here, the space
clause does not imply that a plane exists: a single line with at least four points and no planes at
all satisfies I 1–7 (I 3–6 and the plane clause of I 7 hold vacuously, and four points are "not in a
plane" because there is none). Hilbert evidently means four points in general position; the literal
reading is kept (no axiom is strengthened), and results that need a plane must assume one.

**Status.** definition
-/

/-- **Axiom I, 7, first clause.** Every line contains at least two (distinct) points. -/
def AxiomI7Line [HasLines Point Line] : Prop :=
  ∀ a : Line, ∃ A B : Point, A ≠ B ∧ A ∈ a ∧ B ∈ a

/-- **Axiom I, 7, second clause.** Every plane contains three non-collinear points. -/
def AxiomI7Plane [HasLines Point Line] [HasPlanes Point Plane] : Prop :=
  ∀ α : Plane, ∃ A B C : Point, A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ ¬Collinear A B C

/-- **Axiom I, 7, third clause.** There are four points not lying in a (common) plane. -/
def AxiomI7Space [HasPlanes Point Plane] : Prop :=
  ∃ A B C D : Point, ¬Coplanar A B C D

/-- **Axiom I, 7** (space geometry). -/
def AxiomI7 [HasLines Point Line] [HasPlanes Point Plane] : Prop :=
  AxiomI7Line Point ∧ AxiomI7Plane Point ∧ AxiomI7Space Point

/-- **Axiom I, 7 in plane geometry**, plane clause: there are three points not on a line. -/
def ExistsNoncollinear [HasLines Point Line] : Prop :=
  ∃ A B C : Point, ¬Collinear A B C

/-!
## [s2.plane_space_axioms] Plane and space axioms of group I

*(§ 2)*

> Axioms I, 1–2 contain statements concerning points and straight lines only; that is, concerning the elements of plane geometry. We will call them, therefore, the *plane axioms of group I*, in order to distinguish them from the axioms I, 3–7, which we will designate briefly as the *space axioms* of this group.

**Lean reading.** I 1–2 are the fields `ax_I1`, `ax_I2` of `Connection`, which mentions no plane.
Hilbert's division is not quite exact: plane geometry also needs the first clause of I 7 (every line
has two points), which mentions no plane either, and the existence of three non-collinear points.
So `Connection` (shared by plane and space geometry) is I 1–2 with the line clause of I 7,
`PlaneConnection` adds `ExistsNoncollinear`, and `SpaceConnection` adds I 3–6 and the other two
clauses of I 7.

**Status.** remark
-/

end GroupI

/-! ### Group I as classes -/

/-- **Group I, linear part**: axioms I 1, I 2 and the first clause of I 7 (every line has two
points). Shared by plane and space geometry. -/
class Connection (Point : Type u) (Line : Type v) [HasLines Point Line] : Prop where
  ax_I1 : AxiomI1 Point
  ax_I2 : AxiomI2 Point
  ax_I7_line : AxiomI7Line Point

/-- **Group I of plane geometry**: `Connection` and the existence of three non-collinear points
(the plane clause of I 7 for the one plane). -/
class PlaneConnection (Point : Type u) (Line : Type v) [HasLines Point Line] : Prop
    extends Connection Point Line where
  ax_I7_noncollinear : ExistsNoncollinear Point

/-- **Group I of space geometry**: axioms I 1–7. -/
class SpaceConnection (Point : Type u) (Line : Type v) (Plane : Type w) [HasLines Point Line]
    [HasPlanes Point Plane] : Prop extends Connection Point Line where
  ax_I3 : AxiomI3 Point
  ax_I4 : AxiomI4 Point
  ax_I5 : AxiomI5 Point
  ax_I6 : AxiomI6 Point
  ax_I7_plane : AxiomI7Plane Point
  ax_I7_space : AxiomI7Space Point

section GroupIAPI

variable {Point : Type u} {Line : Type v} {Plane : Type w}

section
variable [HasLines Point Line] [Connection Point Line]

/-- I 1: two distinct points lie on a line. -/
theorem exists_line {A B : Point} (h : A ≠ B) : ∃ a : Line, A ∈ a ∧ B ∈ a :=
  Connection.ax_I1 A B h

/-- I 2: two distinct points lie on at most one line. -/
theorem line_unique {A B : Point} {a b : Line} (h : A ≠ B) (ha : A ∈ a) (hb : B ∈ a)
    (ha' : A ∈ b) (hb' : B ∈ b) : a = b :=
  Connection.ax_I2 A B a b h ha hb ha' hb'

/-- I 7: every line has two distinct points. -/
theorem exists_two_points (a : Line) : ∃ A B : Point, A ≠ B ∧ A ∈ a ∧ B ∈ a :=
  Connection.ax_I7_line a

/-- **The line `AB`** determined by two distinct points (I 1, I 2). -/
noncomputable def line (A B : Point) (h : A ≠ B) : Line :=
  Classical.choose (exists_line (Line := Line) h)

theorem mem_line_left {A B : Point} (h : A ≠ B) : A ∈ line A B h :=
  (Classical.choose_spec (exists_line (Line := Line) h)).1

theorem mem_line_right {A B : Point} (h : A ≠ B) : B ∈ line A B h :=
  (Classical.choose_spec (exists_line (Line := Line) h)).2

/-- Every line through `A ≠ B` is the line `AB`. -/
theorem eq_line {A B : Point} (h : A ≠ B) {a : Line} (ha : A ∈ a) (hb : B ∈ a) :
    a = line A B h :=
  line_unique h ha hb (mem_line_left h) (mem_line_right h)

theorem line_comm {A B : Point} (h : A ≠ B) : line B A h.symm = line A B h :=
  eq_line h (mem_line_right h.symm) (mem_line_left h.symm)

/-- Two distinct points `A`, `B` and `A` again are collinear (I 1). -/
theorem collinear_of_ne {A B : Point} (h : A ≠ B) : Collinear A B A := by
  obtain ⟨a, ha, hb⟩ := exists_line (Line := Line) h
  exact ⟨a, ha, hb, ha⟩

end

end GroupIAPI


section SpaceIAPI

variable {Point : Type u} {Line : Type v} {Plane : Type w}

theorem exists_noncollinear [HasLines Point Line] [PlaneConnection Point Line] :
    ∃ A B C : Point, ¬Collinear A B C :=
  PlaneConnection.ax_I7_noncollinear

variable [HasLines Point Line] [HasPlanes Point Plane] [SpaceConnection Point Line Plane]

/-- I 3: three non-collinear points lie in a plane. -/
theorem exists_plane {A B C : Point} (h : ¬Collinear A B C) :
    ∃ α : Plane, A ∈ α ∧ B ∈ α ∧ C ∈ α :=
  SpaceConnection.ax_I3 A B C h

/-- I 4: three non-collinear points lie in at most one plane. -/
theorem plane_unique {A B C : Point} {α β : Plane} (h : ¬Collinear A B C) (hA : A ∈ α)
    (hB : B ∈ α) (hC : C ∈ α) (hA' : A ∈ β) (hB' : B ∈ β) (hC' : C ∈ β) : α = β :=
  SpaceConnection.ax_I4 A B C α β h hA hB hC hA' hB' hC'

/-- I 5: a line two of whose distinct points lie in a plane lies in that plane. -/
theorem liesInPlane_of_mem {A B : Point} {a : Line} {α : Plane} (h : A ≠ B) (hA : A ∈ a)
    (hB : B ∈ a) (hA' : A ∈ α) (hB' : B ∈ α) : LiesInPlane a α :=
  SpaceConnection.ax_I5 A B a α h hA hB hA' hB'

end SpaceIAPI

/-! ## Group II: Axioms of order (§ 3) -/

section GroupII

variable (Point : Type u) {Line : Type v} {Plane : Type w}

/-!
## [s3.between] "Between" is a relation among the points of a line

*(§ 3)*

> The axioms of this group define the idea expressed by the word “between,” and make possible, upon the basis of this idea, an *order of sequence* of the points upon a straight line, in a plane, and in space. The points of a straight line have a certain relation to one another which the word “between” serves to describe.

**Lean reading.** `BetweenOnLine`: if `B` lies between `A` and `C`, then `A`, `B`, `C` are three
distinct points of one line. This is not one of Hilbert's numbered axioms but the presupposition of
all of them: "between" is a relation among the points of a straight line, and the axioms of this
edition (II 1 "if `A`, `B`, `C` are points of a straight line and `B` lies between `A` and `C`",
II 3 "of any three points") only speak about such points; Hilbert's segment `AB` is a "system of two
points" with "the points lying between `A` and `B`". Without it nothing excludes `Between A B A`
or a point "between" two others off their line, and even `Between A B C → A ≠ C` is unprovable from
II 1–5. Later editions moved exactly this into II 1 ("If a point `B` lies between `A` and `C`, then
`A`, `B`, `C` are three distinct points of a line, and …"); here it is the separate field
`between_onLine` of `LineOrder`, so that II 1 keeps the form of this edition.

**Status.** definition
-/

/-- **"Between" is a relation among three distinct points of a line** (§ 3, tacit). -/
def BetweenOnLine [HasLines Point Line] [HasBetween Point] : Prop :=
  ∀ A B C : Point, Between A B C → A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ Collinear A B C

/-!
## [ax.II1] Axiom II, 1

*(§ 3)*

> *If $A$, $B$, $C$ are points of a straight line and $B$ lies between $A$ and $C$, then $B$ lies also between $C$ and $A$.* [Fig. 1]

**Lean reading.** `AxiomII1`: `Collinear A B C → Between A B C → Between C B A`, literally, with no
distinctness clause (in this edition distinctness is not part of II 1; see `s3.between`).
`between_symm` is the usable form.

**Status.** definition
-/

/-- **Axiom II, 1.** If `B` lies between `A` and `C` (points of a line), it lies between `C`
and `A`. -/
def AxiomII1 [HasLines Point Line] [HasBetween Point] : Prop :=
  ∀ A B C : Point, Collinear A B C → Between A B C → Between C B A

/-!
## [ax.II2] Axiom II, 2

*(§ 3)*

> *If $A$ and $C$ are two points of a straight line, then there exists at least one point $B$ lying between $A$ and $C$ and at least one point $D$ so situated that $C$ lies between $A$ and $D$.* [Fig. 2]

**Lean reading.** `AxiomII2`: for every line `a` and points `A ≠ C` on `a` there are `B` with
`Between A B C` and `D` with `Between A C D`. "Two points" are distinct (for `A = C` the axiom
would contradict `BetweenOnLine`). That `B` and `D` lie on `a` is not stated by Hilbert; it follows
from `BetweenOnLine` and I 2. `exists_between`, `exists_beyond` are the usable forms.

**Status.** definition
-/

/-- **Axiom II, 2.** Between two distinct points of a line there is a point, and beyond `C` (seen
from `A`) there is a point. -/
def AxiomII2 [HasLines Point Line] [HasBetween Point] : Prop :=
  ∀ (A C : Point) (a : Line), A ∈ a → C ∈ a → A ≠ C →
    (∃ B : Point, Between A B C) ∧ ∃ D : Point, Between A C D

/-!
## [ax.II3] Axiom II, 3

*(§ 3)*

> *Of any three points situated on a straight line, there is always one and only one which lies between the other two.*

**Lean reading.** `AxiomII3`: for three *distinct* collinear points `A`, `B`, `C`, exactly one of
`Between B A C` (`A` lies between the other two), `Between A B C`, `Between A C B` holds, stated as
"at least one" and "no two". Distinctness is tacit ("three points"); without it the axiom is
contradictory (for `A = B = C` the three statements coincide). "Between the other two" is taken in
the order in which the other two are named; by II 1 the order does not matter. The halves are
separately usable: `between_trichotomy` (existence), `not_between_swap12`, `not_between_swap23`
(uniqueness). Later editions keep only the uniqueness half.

**Status.** definition
-/

/-- **Axiom II, 3.** Of three distinct points of a line, exactly one lies between the other two. -/
def AxiomII3 [HasLines Point Line] [HasBetween Point] : Prop :=
  ∀ A B C : Point, Collinear A B C → A ≠ B → A ≠ C → B ≠ C →
    (Between B A C ∨ Between A B C ∨ Between A C B) ∧
      ¬(Between B A C ∧ Between A B C) ∧ ¬(Between B A C ∧ Between A C B) ∧
      ¬(Between A B C ∧ Between A C B)

/-!
## [ax.II4] Axiom II, 4

*(§ 3)*

> *Any four points $A$, $B$, $C$, $D$ of a straight line can always be so arranged that $B$ shall lie between $A$ and $C$ and also between $A$ and $D$, and, furthermore, that $C$ shall lie between $A$ and $D$ and also between $B$ and $D$*.

**Lean reading.** `AxiomII4`: for four pairwise distinct points `A`, `B`, `C`, `D` of a line `a`
there is a permutation `σ` of `Fin 4` such that, writing `P i = ![A, B, C, D] (σ i)`, `P 1` lies
between `P 0` and `P 2` and between `P 0` and `P 3`, and `P 2` lies between `P 0` and `P 3` and
between `P 1` and `P 3`. "Can be so arranged" is the permutation; the letters of the conclusion name
the rearranged points. Distinctness is tacit and necessary (with `A = B` no arrangement is compatible
with `BetweenOnLine`). This is the four-point axiom of the first edition, shown to follow from the
other axioms of groups I and II by E. H. Moore (1902); later editions drop it.

**Status.** definition
-/

/-- **Axiom II, 4.** Four distinct points of a line can be arranged in a linear order. -/
def AxiomII4 [HasLines Point Line] [HasBetween Point] : Prop :=
  ∀ (A B C D : Point) (a : Line), A ∈ a → B ∈ a → C ∈ a → D ∈ a →
    A ≠ B → A ≠ C → A ≠ D → B ≠ C → B ≠ D → C ≠ D →
    ∃ σ : Equiv.Perm (Fin 4),
      Between (![A, B, C, D] (σ 0)) (![A, B, C, D] (σ 1)) (![A, B, C, D] (σ 2)) ∧
      Between (![A, B, C, D] (σ 0)) (![A, B, C, D] (σ 1)) (![A, B, C, D] (σ 3)) ∧
      Between (![A, B, C, D] (σ 0)) (![A, B, C, D] (σ 2)) (![A, B, C, D] (σ 3)) ∧
      Between (![A, B, C, D] (σ 1)) (![A, B, C, D] (σ 2)) (![A, B, C, D] (σ 3))

end GroupII

/-!
## [s3.segment] Segments

*(§ 3)*

> Definition. We will call the system of two points $A$ and $B$, lying upon a straight line, a *segment* and denote it by $AB$ or $BA$. The points lying between $A$ and $B$ are called the *points of the segment $AB$* or the *points lying within the segment $AB$*. All other points of the straight line are referred to as the *points lying* *outside the segment $AB$*. The points $A$ and $B$ are called the *extremities* of the segment $AB$.

**Lean reading.** A segment is represented by its two extremities, a pair of *distinct* points
(every axiom about segments carries the hypothesis `A ≠ B`); "`AB` or `BA`" means that every notion
about segments is symmetric in the extremities: for congruence this is `segCong_swap`
(`s6.segment_congruence`), for the points of a segment it is `seg_comm` (from II 1). `Seg A B` is
the set of points of the segment (the points between `A` and `B`; by `BetweenOnLine` they lie on the
line `AB`), and `SegWithEnds A B` adds the extremities. The points outside the segment are the
points of the line `AB` not in `SegWithEnds A B` (no separate definition is needed).

**Status.** definition
-/

section OrderDefs

variable {Point : Type u}

/-- The **points of the segment `AB`**: the points lying between `A` and `B`. -/
def Seg [HasBetween Point] (A B : Point) : Set Point := {X | Between A X B}

/-- The segment `AB` together with its **extremities** `A`, `B`. -/
def SegWithEnds [HasBetween Point] (A B : Point) : Set Point :=
  {X | X = A ∨ X = B ∨ Between A X B}

theorem mem_seg [HasBetween Point] {A B X : Point} : X ∈ Seg A B ↔ Between A X B := Iff.rfl

end OrderDefs

section GroupII5

variable (Point : Type u) {Line : Type v} {Plane : Type w}

/-!
## [ax.II5] Axiom II, 5

*(§ 3)*

> *Let $A$, $B$, $C$ be three points not lying in the same straight line and let $a$ be a straight line lying in the plane $ABC$ and not passing through any of the points $A$, $B$, $C$. Then, if the straight line $a$ passes through a point of the segment $AB$, it will also pass through either a point of the segment $BC$ or a point of the segment $AC$.* Axioms II, 1–4 contain statements concerning the points of a straight line only, and, hence, we will call them the *linear axioms of group II*. Axiom II, 5 relates to the elements of plane geometry and, consequently, shall be called the *plane axiom of group II*.

**Lean reading.** Pasch's axiom. Space version `AxiomII5Space`: for non-collinear `A`, `B`, `C`, a
plane `α` containing them ("the plane `ABC`", unique by I 4) and a line `a` with `LiesInPlane a α`
and `A, B, C ∉ a`: if some point of `a` lies between `A` and `B`, then some point of `a` lies between
`B` and `C` or some point of `a` lies between `A` and `C`. Plane version `AxiomII5`: the same, the
plane being the set of all points (no condition on `a`). "Either … or" is an inclusive `∨` (that it
is exclusive is a theorem). As Hilbert says, II 1–4 are linear (class `LineOrder`, shared by plane
and space geometry) and II 5 is a plane axiom (classes `PlaneOrder`, `SpaceOrder`).

**Status.** definition
-/

/-- **Axiom II, 5** (Pasch), plane geometry. -/
def AxiomII5 [HasLines Point Line] [HasBetween Point] : Prop :=
  ∀ (A B C : Point) (a : Line), ¬Collinear A B C → A ∉ a → B ∉ a → C ∉ a →
    (∃ X : Point, X ∈ a ∧ Between A X B) →
      (∃ Y : Point, Y ∈ a ∧ Between B Y C) ∨ ∃ Y : Point, Y ∈ a ∧ Between A Y C

/-- **Axiom II, 5** (Pasch), space geometry: the line `a` lies in the plane `ABC`. -/
def AxiomII5Space [HasLines Point Line] [HasPlanes Point Plane] [HasBetween Point] : Prop :=
  ∀ (A B C : Point) (α : Plane) (a : Line), ¬Collinear A B C → A ∈ α → B ∈ α → C ∈ α →
    LiesInPlane a α → A ∉ a → B ∉ a → C ∉ a →
    (∃ X : Point, X ∈ a ∧ Between A X B) →
      (∃ Y : Point, Y ∈ a ∧ Between B Y C) ∨ ∃ Y : Point, Y ∈ a ∧ Between A Y C

end GroupII5

/-! ### Group II as classes -/

/-- **The linear axioms of order** II 1–4 (with `Connection`) and the presupposition
`between_onLine` (unit `s3.between`). Shared by plane and space geometry. -/
class LineOrder (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point] : Prop
    extends Connection Point Line where
  between_onLine : BetweenOnLine Point
  ax_II1 : AxiomII1 Point
  ax_II2 : AxiomII2 Point
  ax_II3 : AxiomII3 Point
  ax_II4 : AxiomII4 Point

/-- **Groups I and II of plane geometry.** -/
class PlaneOrder (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point] : Prop
    extends PlaneConnection Point Line, LineOrder Point Line where
  ax_II5 : AxiomII5 Point

/-- **Groups I and II of space geometry.** -/
class SpaceOrder (Point : Type u) (Line : Type v) (Plane : Type w) [HasLines Point Line]
    [HasPlanes Point Plane] [HasBetween Point] : Prop
    extends SpaceConnection Point Line Plane, LineOrder Point Line where
  ax_II5 : AxiomII5Space Point

section OrderAPI

variable {Point : Type u} {Line : Type v} [HasLines Point Line] [HasBetween Point]
  [hO : LineOrder Point Line] {A B C : Point}
include hO

theorem ne12_of_between (h : Between A B C) : A ≠ B := (LineOrder.between_onLine (Line := Line) A B C h).1

theorem ne13_of_between (h : Between A B C) : A ≠ C := (LineOrder.between_onLine (Line := Line) A B C h).2.1

theorem ne23_of_between (h : Between A B C) : B ≠ C := (LineOrder.between_onLine (Line := Line) A B C h).2.2.1

theorem collinear_of_between (h : Between A B C) : Collinear A B C :=
  (LineOrder.between_onLine (Line := Line) A B C h).2.2.2

theorem not_between_self : ¬Between A B A := fun h => ne13_of_between h rfl

/-- II 1. -/
theorem between_symm (h : Between A B C) : Between C B A :=
  LineOrder.ax_II1 (Line := Line) A B C (collinear_of_between h) h

theorem between_comm : Between A B C ↔ Between C B A := ⟨between_symm, between_symm⟩

/-- II 3 (uniqueness): if `B` is between `A` and `C`, then `A` is not between `B` and `C`. -/
theorem not_between_swap12 (h : Between A B C) : ¬Between B A C := fun h' =>
  (LineOrder.ax_II3 (Line := Line) A B C (collinear_of_between h) (ne12_of_between h) (ne13_of_between h)
    (ne23_of_between h)).2.1 ⟨h', h⟩

/-- II 3 (uniqueness): if `B` is between `A` and `C`, then `C` is not between `A` and `B`. -/
theorem not_between_swap23 (h : Between A B C) : ¬Between A C B := fun h' =>
  (LineOrder.ax_II3 (Line := Line) A B C (collinear_of_between h) (ne12_of_between h) (ne13_of_between h)
    (ne23_of_between h)).2.2.2 ⟨h, h'⟩

/-- II 3 (existence): of three distinct collinear points one lies between the other two. -/
theorem between_trichotomy (h : Collinear A B C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    Between B A C ∨ Between A B C ∨ Between A C B :=
  (LineOrder.ax_II3 (Line := Line) A B C h hAB hAC hBC).1

/-- II 2: there is a point between two distinct points. -/
theorem exists_between (h : A ≠ C) : ∃ B, Between A B C := by
  obtain ⟨a, hA, hC⟩ := exists_line (Line := Line) h
  exact (LineOrder.ax_II2 A C a hA hC h).1

/-- II 2: the segment `AC` can be extended beyond `C`. -/
theorem exists_beyond (h : A ≠ C) : ∃ D, Between A C D := by
  obtain ⟨a, hA, hC⟩ := exists_line (Line := Line) h
  exact (LineOrder.ax_II2 A C a hA hC h).2

/-- The segment `AB` is the segment `BA` (II 1). -/
theorem seg_comm : Seg A B = Seg B A := Set.ext fun _ => between_comm (Line := Line)

end OrderAPI

/-- II 5 (Pasch) in plane geometry. -/
theorem pasch {Point : Type u} {Line : Type v} [HasLines Point Line] [HasBetween Point]
    [PlaneOrder Point Line] {A B C X : Point} {a : Line} (h : ¬Collinear A B C) (hA : A ∉ a)
    (hB : B ∉ a) (hC : C ∉ a) (hX : X ∈ a) (hAXB : Between A X B) :
    (∃ Y, Y ∈ a ∧ Between B Y C) ∨ ∃ Y, Y ∈ a ∧ Between A Y C :=
  PlaneOrder.ax_II5 A B C a h hA hB hC ⟨X, hX, hAXB⟩

/-! ## Notions of § 4 needed to state the axioms of congruence -/

/-!
## [s4.side_of_point] Sides of a point on a line

*(§ 4)*

> If $A$, $A'$, $O$, $B$ are four points of a straight line $a$, where $O$ lies between $A$ and $B$ but not between $A$ and $A'$, then we may say: The points $A$, $A'$ are situated *on the line a upon one and the same side of the point $O$,* and the points $A$, $B$ are situated *on the straight line $a$ upon different sides of the point $O$*.

**Lean reading.** Needed ("a given side of `A'` on the straight line `a'`") to state IV 1, so
defined here, directly from betweenness. `SameSidePt O A A'`: `A ≠ O`, `A' ≠ O`, `A`, `O`, `A'`
collinear, and `O` not between `A` and `A'`. Two departures from the letter: Hilbert's definition also
posits a point `B` with `O` between `A` and `B` (such a point exists by II 2 as soon as `A ≠ O`), and
it speaks of four points, while `A' = A` is allowed here (so that `A` lies on its own side and on its
own half-ray). "Different sides of `O`" is `Between A O B`. That "same side" is an equivalence
relation with two classes on the points `≠ O` of the line is a consequence of II 1–4 (Order.lean).

**Status.** definition
-/

/-!
## [s4.half_ray] Half-rays

*(§ 4)*

> All of the points of $a$ which lie upon the same side of $O$, when taken together, are called the *half-ray* emanating from $O$. Hence, each point of a straight line divides it into two half-rays.

**Lean reading.** `ray O A`: the set of points on the same side of `O` as `A` (for `A ≠ O` it
contains `A`, `mem_ray_self`); a half-ray emanating from `O` is a set of this form (`IsHalfRay`).
A half-ray is a set of points, not a primitive object. The last sentence ("hence, each point …
divides it into two half-rays") is a claim, to be proved with the other consequences of II 1–4 in
Order.lean.

**Status.** definition
-/

/-!
## [s4.side_of_line] Sides of a line in a plane

*(§ 4)*

> Making use of the notation of theorem $5$, we say: The points $A$, $A'$ lie *in the plane $\alpha$ upon one and the same side of the straight line $a$*, and the points $A$, $B$ lie *in the plane $\alpha$ upon different sides of the straight line $a$*.

**Lean reading.** Hilbert defines the sides of a line by the two regions of Theorem 5, which is
proved later but needed to state IV 4. So the sides are defined directly by the property Theorem 5
attributes to the regions: `SameSide a A A'` means `A, A' ∉ a` and no point of `a` lies between `A`
and `A'` (so `SameSide a A A` for `A ∉ a`); `OppositeSides a A B` means `A, B ∉ a` and some point of
`a` lies between `A` and `B`. In plane geometry these are Hilbert's notions. In space they are only
meaningful for points of a plane `α` containing `a`, and the axioms that use them say so (`X ∈ α`).
That these relations divide the points of the plane off `a` into exactly two classes is Theorem 5
(Order.lean).

**Status.** definition
-/

section RayDefs

variable {Point : Type u} {Line : Type v}

/-- **`A` and `A'` lie on the same side of `O`** (on the line through them). -/
def SameSidePt [HasLines Point Line] [HasBetween Point] (O A A' : Point) : Prop :=
  A ≠ O ∧ A' ≠ O ∧ Collinear A O A' ∧ ¬Between A O A'

/-- The **half-ray** emanating from `O` through `A`: the points on the same side of `O` as `A`. -/
def ray [HasLines Point Line] [HasBetween Point] (O A : Point) : Set Point :=
  {X | SameSidePt O A X}

/-- `h` is a **half-ray emanating from `O`**. -/
def IsHalfRay [HasLines Point Line] [HasBetween Point] (O : Point) (h : Set Point) : Prop :=
  ∃ A : Point, A ≠ O ∧ h = ray O A

/-- **`A` and `B` lie on the same side of the line `a`**: neither lies on `a`, and no point of `a`
lies between them. -/
def SameSide [Membership Point Line] [HasBetween Point] (a : Line) (A B : Point) : Prop :=
  A ∉ a ∧ B ∉ a ∧ ¬∃ X : Point, X ∈ a ∧ Between A X B

/-- **`A` and `B` lie on different sides of the line `a`**: neither lies on `a`, and some point of
`a` lies between them. -/
def OppositeSides [Membership Point Line] [HasBetween Point] (a : Line) (A B : Point) : Prop :=
  A ∉ a ∧ B ∉ a ∧ ∃ X : Point, X ∈ a ∧ Between A X B

theorem mem_ray [HasLines Point Line] [HasBetween Point] {O A X : Point} :
    X ∈ ray O A ↔ SameSidePt O A X := Iff.rfl

variable [HasLines Point Line] [HasBetween Point] [hO : LineOrder Point Line]
include hO

/-- A half-ray contains the point through which it is drawn. -/
theorem mem_ray_self {O A : Point} (h : A ≠ O) : A ∈ ray O A :=
  ⟨h, h, collinear_of_ne (Line := Line) h, not_between_self (Line := Line)⟩

/-- Two points spanning the same half-ray from `O` lie on the same side of `O`. -/
theorem sameSidePt_of_ray_eq {O A B : Point} (hB : B ≠ O) (h : ray O A = ray O B) :
    SameSidePt O A B := by
  have := mem_ray_self (Line := Line) hB
  rw [← h] at this
  exact this

end RayDefs

/-! ## Group III: Axiom of parallels (§ 5) -/

section GroupIII

variable (Point : Type u) {Line : Type v} {Plane : Type w}

/-!
## [ax.III] Axiom III

*(§ 5)*

> *In a plane $\alpha$ there can be drawn through any point $A$, lying outside of a straight line $a$, one and only one straight line which does not intersect the line $a$. This straight line is called the parallel to $a$ through the given point $A$.*

**Lean reading.** Space version `AxiomIIISpace`: for a plane `α`, a line `a` with `LiesInPlane a α`
and a point `A ∈ α`, `A ∉ a`, there is exactly one line `b` with `LiesInPlane b α`, `A ∈ b` and
`¬Meets b a` ("does not intersect": no common point). Plane version `AxiomIII`: the same without
`α`. No order or congruence is involved: group III presupposes only group I. "The parallel" gives
`Parallel` (plane: lines without a common point) and `ParallelIn α` (space: lines of `α` without a
common point).

**Status.** definition
-/

/-- **Axiom III** (Euclid's axiom), plane geometry. -/
def AxiomIII [HasLines Point Line] : Prop :=
  ∀ (a : Line) (A : Point), A ∉ a → ∃! b : Line, A ∈ b ∧ ¬Meets b a

/-- **Axiom III** (Euclid's axiom), space geometry: in each plane. -/
def AxiomIIISpace [HasLines Point Line] [HasPlanes Point Plane] : Prop :=
  ∀ (α : Plane) (a : Line) (A : Point), LiesInPlane a α → A ∈ α → A ∉ a →
    ∃! b : Line, LiesInPlane b α ∧ A ∈ b ∧ ¬Meets b a

/-!
## [s5.two_assertions] The two assertions of the axiom of parallels

*(§ 5)*

> This statement of the axiom of parallels contains two assertions. The first of these is that, in the plane $\alpha$, there is always a straight line passing through $A$ which does not intersect the given line $a$. The second states that only one such line is possible.

**Lean reading.** `AxiomIIIExists` and `AxiomIIIUnique` (plane geometry) are the two assertions,
and `axiomIII_iff` proves that III is their conjunction. The next claim ("the latter … is the
essential one, and it may also be expressed as follows", i.e. its equivalence with Theorem 8) is
unit `th.8` in Order.lean.

**Status.** proved
-/

/-- The first assertion of III: through `A ∉ a` there is a line not meeting `a`. -/
def AxiomIIIExists [HasLines Point Line] : Prop :=
  ∀ (a : Line) (A : Point), A ∉ a → ∃ b : Line, A ∈ b ∧ ¬Meets b a

/-- The second assertion of III: through `A ∉ a` there is at most one line not meeting `a`. -/
def AxiomIIIUnique [HasLines Point Line] : Prop :=
  ∀ (a : Line) (A : Point), A ∉ a → ∀ b c : Line, A ∈ b → ¬Meets b a → A ∈ c → ¬Meets c a → b = c

theorem axiomIII_iff [HasLines Point Line] :
    AxiomIII Point ↔ AxiomIIIExists Point ∧ AxiomIIIUnique Point := by
  constructor
  · intro h
    exact ⟨fun a A hA => (h a A hA).exists,
      fun a A hA b c hb hb' hc hc' => (h a A hA).unique ⟨hb, hb'⟩ ⟨hc, hc'⟩⟩
  · rintro ⟨h1, h2⟩ a A hA
    obtain ⟨b, hb, hb'⟩ := h1 a A hA
    exact ⟨b, ⟨hb, hb'⟩, fun c hc => h2 a A hA c b hc.1 hc.2 hb hb'⟩

/-!
## [s5.plane_axiom] The axiom of parallels is a plane axiom

*(§ 5)*

> The axiom of parallels is a *plane axiom*.

**Lean reading.** Reflected in the hierarchy: III has a plane version (`PlaneParallels`) and a space
version stated inside each plane (`SpaceParallels`).

**Status.** remark
-/

end GroupIII

section ParallelDefs

variable {Point : Type u} {Line : Type v} {Plane : Type w}

/-- **Parallel lines** in plane geometry: lines without a common point (§ 5). -/
def Parallel [Membership Point Line] (a b : Line) : Prop := ¬Meets (Point := Point) a b

/-- **Parallel lines in the plane `α`** (space geometry): lines of `α` without a common point. -/
def ParallelIn [Membership Point Line] [Membership Point Plane] (α : Plane) (a b : Line) : Prop :=
  LiesInPlane (Point := Point) a α ∧ LiesInPlane (Point := Point) b α ∧ ¬Meets (Point := Point) a b

end ParallelDefs

/-- **Group III of plane geometry** (with group I). -/
class PlaneParallels (Point : Type u) (Line : Type v) [HasLines Point Line] : Prop
    extends PlaneConnection Point Line where
  ax_III : AxiomIII Point

/-- **Group III of space geometry** (with group I): Euclid's axiom in every plane. -/
class SpaceParallels (Point : Type u) (Line : Type v) (Plane : Type w) [HasLines Point Line]
    [HasPlanes Point Plane] : Prop extends SpaceConnection Point Line Plane where
  ax_III : AxiomIIISpace Point

/-- III, plane geometry: the parallel through a point outside a line exists and is unique. -/
theorem exists_unique_parallel {Point : Type u} {Line : Type v} [HasLines Point Line]
    [PlaneParallels Point Line] {A : Point} {a : Line} (h : A ∉ a) :
    ∃! b : Line, A ∈ b ∧ ¬Meets b a :=
  PlaneParallels.ax_III a A h


/-! ## Group IV: Axioms of congruence (§ 6) -/

section GroupIVSeg

variable (Point : Type u) {Line : Type v} {Plane : Type w}

/-!
## [s6.segment_congruence] Congruence of segments

*(§ 6)*

> The axioms of this group define the idea of congruence or displacement. … Segments stand in a certain relation to one another which is described by the word “*congruent*.”

**Lean reading.** The relation is `SegCong A B A' B'` ("`AB ≡ A'B'`") on four points. Since a
segment is the unordered pair of its extremities ("`AB` or `BA`", `s3.segment`), the relation must
not depend on the order in which the extremities are named: `SegCongSwap` says that
`AB ≡ A'B'` implies `BA ≡ A'B'` and `AB ≡ B'A'`. It is part of the encoding (field `segCong_swap` of
`SegmentCongruence`), not one of Hilbert's axioms. It is required for all tuples, degenerate ones
included, which costs a model nothing (symmetrise the relation). Otherwise the values of `SegCong` on
degenerate segments (`A = B`) are junk: every axiom quantifies over genuine segments only.

**Status.** definition
-/

/-- **Congruence is a relation between segments** (unordered pairs): `AB ≡ A'B'` implies
`BA ≡ A'B'` and `AB ≡ B'A'`. -/
def SegCongSwap [HasSegCong Point] : Prop :=
  ∀ A B A' B' : Point, SegCong A B A' B' → SegCong B A A' B' ∧ SegCong A B B' A'

/-!
## [ax.IV1] Axiom IV, 1

*(§ 6)*

> *If $A$, $B$ are two points on a straight line $a$, and if $A'$ is a point upon the same or another straight line $a'$, then, upon a given side of $A'$ on the straight line $a'$, we can always find one and only one point $B'$ so that the segment $AB$ (or $BA$) is congruent to the segment $A'B'$. We indicate this relation by writing * \[ AB\equiv A'B'. \] *Every segment is congruent to itself; that is, we always have* \[ AB\equiv AB. \]

**Lean reading.** Two clauses. `AxiomIV1LayOff`: for `A ≠ B` ("two points", tacit distinctness)
and `A' ≠ C'`, there is exactly one `B'` with `SameSidePt A' C' B'` (`B'` lies on the side of `A'`
given by `C'`, on the line `a' = A'C'`) and `SegCong A B A' B'`. "The given side of `A'` on `a'`" is
specified by a point `C'` of `a'` other than `A'`; the line `a` of `A`, `B` plays no role (it is
determined by I 1, I 2), nor does the line `a'` beyond containing `A'` and `C'`. "`AB` (or `BA`)" is
taken care of by `segCong_swap`. `AxiomIV1Refl`: `SegCong A B A B` for `A ≠ B`. `AxiomIV1` is the
conjunction; the class `SegmentCongruence` has the two clauses as fields `ax_IV1` and `ax_IV1_refl`.
Usable forms: `exists_unique_segCong`, `segCong_refl`.

**Status.** definition
-/

/-- **Axiom IV, 1** (laying off segments): a segment can be laid off on a given side of a given
point of a given line in one and only one way. -/
def AxiomIV1LayOff [HasLines Point Line] [HasBetween Point] [HasSegCong Point] : Prop :=
  ∀ A B A' C' : Point, A ≠ B → A' ≠ C' → ∃! B' : Point, SameSidePt A' C' B' ∧ SegCong A B A' B'

/-- **Axiom IV, 1** (reflexivity): every segment is congruent to itself. -/
def AxiomIV1Refl [HasSegCong Point] : Prop :=
  ∀ A B : Point, A ≠ B → SegCong A B A B

/-- **Axiom IV, 1.** -/
def AxiomIV1 [HasLines Point Line] [HasBetween Point] [HasSegCong Point] : Prop :=
  AxiomIV1LayOff Point ∧ AxiomIV1Refl Point

/-!
## [s6.laying_off_segments] Laying off segments

*(§ 6)*

> We can state the above axiom briefly by saying that every segment can be *laid off* upon a given side of a given point of a given straight line in one and and only one way.

**Lean reading.** A paraphrase of the first clause of IV 1 (`AxiomIV1LayOff`). "In one and and only
one way" is a misprint of the translation (a line break in the LaTeX source repeats "and").

**Status.** remark
-/

/-!
## [ax.IV2] Axiom IV, 2

*(§ 6)*

> *If a segment $AB$ is congruent to the segment $A'B'$ and also to the segment $A''B''$, then the segment $A'B'$ is congruent to the segment $A''B''$; that is, if $AB \equiv A'B$ and $AB \equiv A''B''$, then $A'B' \equiv A''B''$.*

**Lean reading.** "`AB ≡ A'B`" in the "that is" clause is a misprint (of the translation and the
LaTeX source) for `AB ≡ A'B'`. `AxiomIV2`: for genuine segments (`A ≠ B`, `A' ≠ B'`, `A'' ≠ B''`),
`SegCong A B A' B' → SegCong A B A'' B'' → SegCong A' B' A'' B''`.

**Status.** definition
-/

/-- **Axiom IV, 2.** Two segments congruent to a third are congruent to each other. -/
def AxiomIV2 [HasSegCong Point] : Prop :=
  ∀ A B A' B' A'' B'' : Point, A ≠ B → A' ≠ B' → A'' ≠ B'' →
    SegCong A B A' B' → SegCong A B A'' B'' → SegCong A' B' A'' B''

/-!
## [ax.IV3] Axiom IV, 3

*(§ 6)*

> *Let $AB$ and $BC$ be two segments of a straight line $a$ which have no points in common aside from the point $B$, and, furthermore, let $A'B'$ and $B'C'$ be two segments of the same or of another straight line $a'$ having, likewise, no point other than $B'$ in common. Then, if $AB \equiv A'B'$ and $BC \equiv B'C'$, we have $AC \equiv A'C'$.* [Fig. 8]

**Lean reading.** `SegmentsMeetOnlyAt A B C`: `A`, `B`, `C` are collinear, `A ≠ B`, `B ≠ C`, and
every point common to the segments `AB` and `BC`, *extremities included* (`SegWithEnds`), is `B`.
The extremities must be included: Hilbert's "points of a segment" are the points between the
extremities, which never include `B`, so "aside from the point `B`" only makes sense for the closed
segments. (Both readings are equivalent under II 1–4, and both are equivalent to `Between A B C`;
this is proved in Congruence.lean, not assumed here.) `AxiomIV3`: if `SegmentsMeetOnlyAt A B C`,
`SegmentsMeetOnlyAt A' B' C'`, `AB ≡ A'B'` and `BC ≡ B'C'`, then `AC ≡ A'C'`.

**Status.** definition
-/

/-- `AB` and `BC` are segments of a line having no point in common but `B` (extremities
included). -/
def SegmentsMeetOnlyAt {Point : Type u} [HasLines Point Line] [HasBetween Point] (A B C : Point) :
    Prop :=
  Collinear A B C ∧ A ≠ B ∧ B ≠ C ∧ ∀ X : Point, X ∈ SegWithEnds A B → X ∈ SegWithEnds B C → X = B

/-- **Axiom IV, 3.** Sums of congruent segments are congruent. -/
def AxiomIV3 [HasLines Point Line] [HasBetween Point] [HasSegCong Point] : Prop :=
  ∀ A B C A' B' C' : Point, SegmentsMeetOnlyAt A B C → SegmentsMeetOnlyAt A' B' C' →
    SegCong A B A' B' → SegCong B C B' C' → SegCong A C A' C'

end GroupIVSeg

/-- **The linear axioms of congruence** IV 1–3 (with groups I, II 1–4), and `segCong_swap`
(unit `s6.segment_congruence`). Shared by plane and space geometry. -/
class SegmentCongruence (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point]
    [HasSegCong Point] : Prop extends LineOrder Point Line where
  segCong_swap : SegCongSwap Point
  ax_IV1 : AxiomIV1LayOff Point
  ax_IV1_refl : AxiomIV1Refl Point
  ax_IV2 : AxiomIV2 Point
  ax_IV3 : AxiomIV3 Point

section SegCongAPI

variable {Point : Type u} {Line : Type v} [HasLines Point Line] [HasBetween Point]
  [HasSegCong Point] [hS : SegmentCongruence Point Line] {A B A' B' : Point}
include hS

theorem SegmentCongruence.axiomIV1 : AxiomIV1 Point :=
  ⟨SegmentCongruence.ax_IV1 (Line := Line), SegmentCongruence.ax_IV1_refl (Line := Line)⟩

/-- IV 1: every segment is congruent to itself. -/
theorem segCong_refl (h : A ≠ B) : SegCong A B A B :=
  SegmentCongruence.ax_IV1_refl (Line := Line) A B h

theorem segCong_swap_left (h : SegCong A B A' B') : SegCong B A A' B' :=
  (SegmentCongruence.segCong_swap (Line := Line) A B A' B' h).1

theorem segCong_swap_right (h : SegCong A B A' B') : SegCong A B B' A' :=
  (SegmentCongruence.segCong_swap (Line := Line) A B A' B' h).2

/-- IV 1: the segment `AB` can be laid off from `A'` on the side of `C'` in exactly one way. -/
theorem exists_unique_segCong {C' : Point} (hAB : A ≠ B) (hC' : A' ≠ C') :
    ∃! B' : Point, SameSidePt A' C' B' ∧ SegCong A B A' B' :=
  SegmentCongruence.ax_IV1 A B A' C' hAB hC'

end SegCongAPI

section GroupIVAng

variable (Point : Type u) {Line : Type v} {Plane : Type w}

/-!
## [s6.angle] Angles

*(§ 6)*

> Definitions. Let $\alpha$ be any arbitrary plane and $h$, $k$ any two distinct half-rays lying in $\alpha$ and emanating from the point $O$ so as to form a part of two different straight lines. We call the system formed by these two half-rays $h$, $k$ an *angle* and represent it by the symbol $\angle(h, k)$ or $\angle(k, h)$. … The half rays $h$ and $k$ are called the *sides of the angle*, and the point $O$ is called the *vertex of the angle*.

**Lean reading.** An angle `∠(h, k)` is represented by a triple `A, O, B` of non-collinear points:
`O` is the vertex and `h = ray O A`, `k = ray O B` are the sides ("two different straight lines" is
`¬Collinear A O B`; the plane `α` is the plane `AOB`). The triple is not unique: `SameAngle A O B
C D` says that `∠AOB` and `∠COD` are the same angle, i.e. the same unordered pair of half-rays
(`{ray O A, ray O B} = {ray O C, ray O D}` as sets of sets of points), which also expresses
"`∠(h, k)` or `∠(k, h)`". Hilbert's angle congruence is a relation between angles; it is encoded as
the relation `AngCong A O B A' O' B'` on triples together with `AngCongWellDefined`: for genuine
angles, `AngCong` only depends on the angles (`SameAngle`) on either side. This is the meaning of
"angle", not an axiom (field `angCong_wd` of `AngleCongruence`). On degenerate triples `AngCong` is
junk. In the elided part, "the remaining points of the plane a" is a misprint (also in the LaTeX
source) for "of the plane `α`". The claim made in the elided part of the quote, that the sides and the vertex divide the other
points of the plane into two regions, is not proved here; it is a consequence of II 1–5 belonging to
Congruence.lean (unit `s6.angle_regions` there).

**Status.** definition
-/

/-- **`∠AOB` and `∠COD` are the same angle**: the same (unordered) pair of half-rays from `O`. -/
def SameAngle {Point : Type u} [HasLines Point Line] [HasBetween Point] (A O B C D : Point) : Prop :=
  ({ray O A, ray O B} : Set (Set Point)) = {ray O C, ray O D}

/-- **Congruence is a relation between angles**: for genuine angles, `∠AOB ≡ ∠A'O'B'` only depends
on the angles `∠AOB`, `∠A'O'B'` (pairs of half-rays), not on the points chosen on their sides or on
the order of the sides. -/
def AngCongWellDefined [HasLines Point Line] [HasBetween Point] [HasAngCong Point] : Prop :=
  ∀ A O B C D A' O' B' C' D' : Point, ¬Collinear A O B → ¬Collinear A' O' B' →
    SameAngle A O B C D → SameAngle A' O' B' C' D' →
    AngCong A O B A' O' B' → AngCong C O D C' O' D'

/-!
## [s6.interior] Interior and exterior of an angle

*(§ 6)*

> One of these two regions is distinguished from the other in that the segment joining any two points of this region lies entirely within the region. The region so characterised is called the *interior of the angle $(h,k)$*. To distinguish the other region from this, we call it the *exterior of the angle $(h,k)$*.

**Lean reading.** Hilbert defines the interior as one of the two regions whose existence he asserts
(see `s6.angle`); since IV 4 needs the interior before anything is proved, it is defined directly,
as in later editions: `X ∈ Interior A O B` iff `X` lies on the same side of the line `OA` as `B`
and on the same side of the line `OB` as `A` (`SameSide`; "the line `OA`" is any line through `O`
and `A`, unique by I 2). `Exterior A O B` is the set of points other than `O`, not on the sides and
not in the interior. In plane geometry these are subsets of the plane; in space they are only
meaningful inside the plane `AOB`, and the space version of IV 4 restricts to points of that plane.
That `Interior A O B` is the convex region of Hilbert's description, and that both are well defined
on angles (depend only on the half-rays), are consequences of II 1–5 for Congruence.lean.

**Status.** definition
-/

/-- The **interior** of `∠AOB`: the points on the same side of `OA` as `B` and on the same side of
`OB` as `A`. -/
def Interior {Point : Type u} [HasLines Point Line] [HasBetween Point] (A O B : Point) :
    Set Point :=
  {X | ∀ a b : Line, O ∈ a → A ∈ a → O ∈ b → B ∈ b → SameSide a X B ∧ SameSide b X A}

/-- The **exterior** of `∠AOB` (plane geometry): the points not on the angle and not interior. -/
def Exterior {Point : Type u} [HasLines Point Line] [HasBetween Point] (A O B : Point) :
    Set Point :=
  {X | X ≠ O ∧ X ∉ ray O A ∧ X ∉ ray O B ∧ X ∉ Interior A O B}

/-!
## [ax.IV4] Axiom IV, 4

*(§ 6)*

> *Let an angle $(h,k)$ be given in the plane $\alpha$ and let a straight line $a'$ be given in a plane $\alpha'$. Suppose also that, in the plane $\alpha'$, a definite side of the straight line $a'$ be assigned. Denote by $h'$ a half-ray of the straight line $a'$ emanating from a point $O'$ of this line. Then in the plane $\alpha'$ there is one and only one half-ray $k'$ such that the angle $(h,k)$, or $(k,h)$, is congruent to the angle $(h',k')$ and at the same time all interior points of the angle $(h',k')$ lie upon the given side of $a'$. We express this relation by means of the notation \[ \angle (h,k) \equiv \angle (h',k') \] Every angle is congruent to itself; that is, \[ \angle (h,k) \equiv \angle (h,k) \] or \[ \angle (h,k) \equiv \angle (k,h) \] *

**Lean reading.** Two clauses. Laying off, space version `AxiomIV4LayOffSpace`: given an angle
`∠AOB` (`¬Collinear A O B`; its plane `α` plays no role), a plane `α'`, a line `a'` in `α'`, points
`O' ≠ A'` of `a'` (`h' = ray O' A'`) and a point `D' ∈ α'` off `a'` (the assigned side of `a'` in `α'`
is the side of `D'`), there is a point `B' ∈ α'` off `a'` (so `k' = ray O' B'` is a half-ray of `α'`
and `(h', k')` is an angle) with `∠AOB ≡ ∠A'O'B'` and every interior point `X ∈ α'` of `∠A'O'B'` on
the side of `D'`; and for every other such `B''` (same conditions) the half-ray is the same:
`ray O' B'' = ray O' B'` ("one and only one half-ray", as sets). Plane version `AxiomIV4LayOff`:
the same without `α`, `α'`. "`(h, k)`, or `(k, h)`" is taken care of by `angCong_wd`. Reflexivity
`AxiomIV4Refl`: `∠AOB ≡ ∠AOB` for `¬Collinear A O B`; the alternative "`∠(h, k) ≡ ∠(k, h)`" is
the same statement since `∠(h, k)` and `∠(k, h)` are the same angle (`angCong_swap_right`).
`AxiomIV4`, `AxiomIV4Space` are the conjunctions. Fields: `ax_IV4_refl` in the shared class
`AngleCongruence`, `ax_IV4` (laying off) in `PlaneAngleCongruence` / `SpaceAngleCongruence`.

**Status.** definition
-/

/-- **Axiom IV, 4** (laying off angles), plane geometry. -/
def AxiomIV4LayOff [HasLines Point Line] [HasBetween Point] [HasAngCong Point] : Prop :=
  ∀ (A O B : Point) (a' : Line) (O' A' D' : Point), ¬Collinear A O B →
    O' ∈ a' → A' ∈ a' → A' ≠ O' → D' ∉ a' →
    ∃ B' : Point, B' ∉ a' ∧ AngCong A O B A' O' B' ∧
      (∀ X : Point, X ∈ Interior A' O' B' → SameSide a' X D') ∧
      ∀ B'' : Point, B'' ∉ a' → AngCong A O B A' O' B'' →
        (∀ X : Point, X ∈ Interior A' O' B'' → SameSide a' X D') → ray O' B'' = ray O' B'

/-- **Axiom IV, 4** (laying off angles), space geometry: inside the plane `α'`. -/
def AxiomIV4LayOffSpace [HasLines Point Line] [HasPlanes Point Plane] [HasBetween Point]
    [HasAngCong Point] : Prop :=
  ∀ (A O B : Point) (α' : Plane) (a' : Line) (O' A' D' : Point), ¬Collinear A O B →
    LiesInPlane a' α' → O' ∈ a' → A' ∈ a' → A' ≠ O' → D' ∈ α' → D' ∉ a' →
    ∃ B' : Point, B' ∈ α' ∧ B' ∉ a' ∧ AngCong A O B A' O' B' ∧
      (∀ X : Point, X ∈ α' → X ∈ Interior A' O' B' → SameSide a' X D') ∧
      ∀ B'' : Point, B'' ∈ α' → B'' ∉ a' → AngCong A O B A' O' B'' →
        (∀ X : Point, X ∈ α' → X ∈ Interior A' O' B'' → SameSide a' X D') →
          ray O' B'' = ray O' B'

/-- **Axiom IV, 4** (reflexivity): every angle is congruent to itself. -/
def AxiomIV4Refl [HasLines Point Line] [HasAngCong Point] : Prop :=
  ∀ A O B : Point, ¬Collinear A O B → AngCong A O B A O B

/-- **Axiom IV, 4**, plane geometry. -/
def AxiomIV4 [HasLines Point Line] [HasBetween Point] [HasAngCong Point] : Prop :=
  AxiomIV4LayOff Point ∧ AxiomIV4Refl Point

/-- **Axiom IV, 4**, space geometry. -/
def AxiomIV4Space [HasLines Point Line] [HasPlanes Point Plane] [HasBetween Point]
    [HasAngCong Point] : Prop :=
  AxiomIV4LayOffSpace Point ∧ AxiomIV4Refl Point

/-!
## [s6.laying_off_angles] Laying off angles

*(§ 6)*

> We say, briefly, that every angle in a given plane can be *laid off* upon a given side of a given half-ray in one and only one way.

**Lean reading.** A paraphrase of the first clause of IV 4 (`AxiomIV4LayOff`,
`AxiomIV4LayOffSpace`). "In a given plane" refers to the plane `α'` of the laying off.

**Status.** remark
-/

/-!
## [ax.IV5] Axiom IV, 5

*(§ 6)*

> *If the angle $(h,k)$ is congruent to the angle $(h',k')$ and to the angle $(h'',k'')$, then the angle $(h',k')$ is congruent to the angle $(h'',k'')$; that is to say, if $\angle (h, k) \equiv \angle (h', k')$ and $\angle (h, k) \equiv \angle (h'',k'')$, then $\angle (h',k') \equiv \angle (h'',k'')$.*

**Lean reading.** `AxiomIV5`: for genuine angles `∠AOB`, `∠A'O'B'`, `∠A''O''B''` (non-collinear
triples), `∠AOB ≡ ∠A'O'B'` and `∠AOB ≡ ∠A''O''B''` imply `∠A'O'B' ≡ ∠A''O''B''`. No plane is
involved, so the axiom is shared by plane and space geometry (class `AngleCongruence`), although
Hilbert counts IV 4–6 among the plane axioms.

**Status.** definition
-/

/-- **Axiom IV, 5.** Two angles congruent to a third are congruent to each other. -/
def AxiomIV5 [HasLines Point Line] [HasAngCong Point] : Prop :=
  ∀ A O B A' O' B' A'' O'' B'' : Point, ¬Collinear A O B → ¬Collinear A' O' B' →
    ¬Collinear A'' O'' B'' →
    AngCong A O B A' O' B' → AngCong A O B A'' O'' B'' → AngCong A' O' B' A'' O'' B''

/-!
## [s6.angle_of_triangle] The angles of a triangle

*(§ 6)*

> Suppose we have given a triangle $ABC$. Denote by $h$, $k$ the two half-rays emanating from $A$ and passing respectively through $B$ and $C$. The angle $(h,k)$ is then said to be the angle included by the sides $AB$ and $AC$, or the one opposite to the side $BC$ in the triangle $ABC$. It contains all of the interior points of the triangle $ABC$ and is represented by the symbol $\angle BAC$, or by $\angle A$.

**Lean reading.** A triangle `ABC` (a polygon with three vertices, § 4) is used here with its
angles, so its vertices are not collinear: `IsTriangle A B C := ¬Collinear A B C`. The angle
`∠BAC` = `∠(ray A B, ray A C)` is the triple `B, A, C` in the encoding of `s6.angle`. The claim
"it contains all of the interior points of the triangle" depends on the interior of a polygon
(Theorem 6) and belongs to Congruence.lean; it is not proved here.

**Status.** definition
-/

/-- `ABC` is a **triangle** (three non-collinear vertices). -/
def IsTriangle {Point : Type u} [HasLines Point Line] (A B C : Point) : Prop :=
  ¬Collinear A B C

/-!
## [ax.IV6] Axiom IV, 6

*(§ 6)*

> *If, in the two triangles $ABC$ and $A'B'C'$ the congruences \[ AB \equiv A'B', \: AC \equiv A'C', \: \angle BAC \equiv \angle B'A'C' \] hold, then the congruences \[ \angle ABC \equiv \angle A'B'C' \:and\; \angle ACB \equiv \angle A'C'B' \] also hold.*

**Lean reading.** `AxiomIV6`: for triangles `ABC`, `A'B'C'` (non-collinear), if `AB ≡ A'B'`,
`AC ≡ A'C'` and `∠BAC ≡ ∠B'A'C'`, then `∠ABC ≡ ∠A'B'C'` and `∠ACB ≡ ∠A'C'B'`. This edition
concludes both base angles; later editions state only the first (the second follows by renaming).
No plane is involved; the axiom is the only field of the class `TriangleCongruence`, shared by plane
and space geometry, so that the geometry of § 11 (IV 6 false, all other axioms true) can be
formulated.

**Status.** definition
-/

/-- **Axiom IV, 6.** -/
def AxiomIV6 [HasLines Point Line] [HasSegCong Point] [HasAngCong Point] : Prop :=
  ∀ A B C A' B' C' : Point, IsTriangle A B C → IsTriangle A' B' C' →
    SegCong A B A' B' → SegCong A C A' C' → AngCong B A C B' A' C' →
    AngCong A B C A' B' C' ∧ AngCong A C B A' C' B'

/-!
## [s6.linear_plane] Linear and plane axioms of group IV

*(§ 6)*

> Axioms IV, 1–3 contain statements concerning the congruence of segments of a straight line only. They may, therefore, be called the *linear* axioms of group IV. Axioms IV, 4, 5 contain statements relating to the congruence of angles. Axiom IV, 6 gives the connection between the congruence of segments and the congruence of angles. Axioms IV, 4–6 contain statements regarding the elements of plane geometry and may be called the *plane* axioms of group IV.

**Lean reading.** The classes follow this division: `SegmentCongruence` (IV 1–3, linear),
`AngleCongruence` with `PlaneAngleCongruence` / `SpaceAngleCongruence` (IV 4–5), and
`TriangleCongruence` (IV 6). Of the plane axioms only the laying-off clause of IV 4 refers to a
plane; reflexivity in IV 4, IV 5 and IV 6 do not, and are shared by plane and space geometry.

**Status.** remark
-/

end GroupIVAng

/-- **The plane-free part of the axioms of congruence of angles**: `angCong_wd` (unit `s6.angle`),
the reflexivity clause of IV 4 and IV 5 (with groups I, II 1–4). Shared by plane and space
geometry; the laying-off clause of IV 4 is in `PlaneAngleCongruence` / `SpaceAngleCongruence`. -/
class AngleCongruence (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point]
    [HasAngCong Point] : Prop extends LineOrder Point Line where
  angCong_wd : AngCongWellDefined Point
  ax_IV4_refl : AxiomIV4Refl Point
  ax_IV5 : AxiomIV5 Point

/-- **Axioms IV 4–5 of plane geometry** (with groups I, II). -/
class PlaneAngleCongruence (Point : Type u) (Line : Type v) [HasLines Point Line]
    [HasBetween Point] [HasAngCong Point] : Prop
    extends PlaneOrder Point Line, AngleCongruence Point Line where
  ax_IV4 : AxiomIV4LayOff Point

/-- **Axioms IV 4–5 of space geometry** (with groups I, II). -/
class SpaceAngleCongruence (Point : Type u) (Line : Type v) (Plane : Type w) [HasLines Point Line]
    [HasPlanes Point Plane] [HasBetween Point] [HasAngCong Point] : Prop
    extends SpaceOrder Point Line Plane, AngleCongruence Point Line where
  ax_IV4 : AxiomIV4LayOffSpace Point

/-- **Axiom IV 6** (with IV 1–3, the plane-free part of IV 4–5, groups I, II 1–4). -/
class TriangleCongruence (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point]
    [HasSegCong Point] [HasAngCong Point] : Prop
    extends SegmentCongruence Point Line, AngleCongruence Point Line where
  ax_IV6 : AxiomIV6 Point

/-- **Groups I, II, IV of plane geometry.** -/
class PlaneCongruence (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point]
    [HasSegCong Point] [HasAngCong Point] : Prop
    extends PlaneAngleCongruence Point Line, TriangleCongruence Point Line

/-- **Groups I, II, IV of space geometry.** -/
class SpaceCongruence (Point : Type u) (Line : Type v) (Plane : Type w) [HasLines Point Line]
    [HasPlanes Point Plane] [HasBetween Point] [HasSegCong Point] [HasAngCong Point] : Prop
    extends SpaceAngleCongruence Point Line Plane, TriangleCongruence Point Line

section SameAngleAPI

variable {Point : Type u} {Line : Type v} [HasLines Point Line] [HasBetween Point]

/-- `∠AOB` and `∠BOA` are the same angle. -/
theorem sameAngle_swap (A O B : Point) : SameAngle A O B B A :=
  Set.pair_comm _ _

theorem sameAngle_refl (A O B : Point) : SameAngle A O B A B := rfl

end SameAngleAPI

section AngCongAPI

variable {Point : Type u} {Line : Type v} {Plane : Type w} [HasLines Point Line] [HasBetween Point]
  [HasAngCong Point]

theorem PlaneAngleCongruence.axiomIV4 [PlaneAngleCongruence Point Line] : AxiomIV4 Point :=
  ⟨PlaneAngleCongruence.ax_IV4 (Line := Line), AngleCongruence.ax_IV4_refl (Line := Line)⟩

theorem SpaceAngleCongruence.axiomIV4 [HasPlanes Point Plane]
    [SpaceAngleCongruence Point Line Plane] : AxiomIV4Space Point :=
  ⟨SpaceAngleCongruence.ax_IV4 (Line := Line) (Plane := Plane),
    AngleCongruence.ax_IV4_refl (Line := Line)⟩

variable [hA : AngleCongruence Point Line] {A O B A' O' B' C D C' D' : Point}
include hA

/-- IV 4: every angle is congruent to itself. -/
theorem angCong_refl (h : ¬Collinear A O B) : AngCong A O B A O B :=
  AngleCongruence.ax_IV4_refl (Line := Line) A O B h

/-- Congruence of angles only depends on the angles (`angCong_wd`). -/
theorem angCong_of_sameAngle (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hs : SameAngle A O B C D) (hs' : SameAngle A' O' B' C' D') (hc : AngCong A O B A' O' B') :
    AngCong C O D C' O' D' :=
  AngleCongruence.angCong_wd (Line := Line) A O B C D A' O' B' C' D' h h' hs hs' hc

theorem angCong_swap_left (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong B O A A' O' B' :=
  angCong_of_sameAngle h h' (sameAngle_swap A O B) (sameAngle_refl A' O' B') hc

theorem angCong_swap_right (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong A O B B' O' A' :=
  angCong_of_sameAngle h h' (sameAngle_refl A O B) (sameAngle_swap A' O' B') hc

/-- IV 5. -/
theorem angCong_trans_left {A'' O'' B'' : Point} (h : ¬Collinear A O B)
    (h' : ¬Collinear A' O' B') (h'' : ¬Collinear A'' O'' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A O B A'' O'' B'') : AngCong A' O' B' A'' O'' B'' :=
  AngleCongruence.ax_IV5 (Line := Line) A O B A' O' B' A'' O'' B'' h h' h'' h1 h2

end AngCongAPI

/-- IV 6. -/
theorem angCong_of_sas {Point : Type u} {Line : Type v} [HasLines Point Line] [HasBetween Point]
    [HasSegCong Point] [HasAngCong Point] [TriangleCongruence Point Line] {A B C A' B' C' : Point}
    (h : IsTriangle A B C) (h' : IsTriangle A' B' C') (hAB : SegCong A B A' B')
    (hAC : SegCong A C A' C') (hA : AngCong B A C B' A' C') :
    AngCong A B C A' B' C' ∧ AngCong A C B A' C' B' :=
  TriangleCongruence.ax_IV6 (Line := Line) A B C A' B' C' h h' hAB hAC hA


/-! ## Group V: Axiom of continuity (§ 8) -/

section GroupV

variable (Point : Type u) {Line : Type v} {Plane : Type w}

/-!
## [s8.equality] The convention on "equal" segments

*(§ 8)*

> This axiom makes possible the introduction into geometry of the idea of continuity. In order to state this axiom, we must first establish a convention concerning the equality of two segments. For this purpose, we can either base our idea of equality upon the axioms relating to the congruence of segments and define as “*equal*” the correspondingly congruent segments, or upon the basis of groups I and II, we may determine how, by suitable constructions (see Chap. V, § 24), a segment is to be laid off from a point of a given straight line so that a new, definite segment is obtained “*equal*” to it.

**Lean reading.** Axiom V is stated for an arbitrary relation `Equal : Point → Point → Point →
Point → Prop` ("the segment `AB` is equal to `A'B'`"): `ArchimedesWith Point Equal`. The first
convention is `Equal = SegCong` (`AxiomV`, class `Archimedes`). The second is the equality of
segments defined by the constructions of § 24, to be supplied in Chapter V; there the construction
uses parallels, so it rests on the plane axioms I 1–2, II, III (§ 24 says "I 1–2, II–III"), not on
groups I and II alone as § 8 says. Nothing about `Equal` is assumed.

**Status.** definition
-/

/-- **Archimedes's axiom with respect to a notion `Equal` of equal segments.** If `A 1` lies between
`A 0` and `B`, each `A (n + 1)` lies between `A n` and `A (n + 2)`, and the segments
`A n A (n + 1)` are all equal to one another, then `B` lies between `A 0` and some `A n`. -/
def ArchimedesWith [HasBetween Point] (Equal : Point → Point → Point → Point → Prop) : Prop :=
  ∀ (A : ℕ → Point) (B : Point), Between (A 0) (A 1) B →
    (∀ n : ℕ, Between (A n) (A (n + 1)) (A (n + 2))) →
    (∀ m n : ℕ, Equal (A m) (A (m + 1)) (A n) (A (n + 1))) →
    ∃ n : ℕ, Between (A 0) B (A n)

/-!
## [ax.V] Axiom V

*(§ 8)*

> *Let $A_1$ be any point upon a straight line between the arbitrarily chosen points $A$ and $B$. Take the points $A_2$, $A_3$, $A_4,\ldots$ so that $A_1$ lies between $A$ and $A_2$, $A_2$ between $A_1$ and $A_3$, $A_3$ between $A_2$ and $A_4$ etc. Moreover, let the segments \[ A A_1, \; A_1 A_2, \; A_2 A_3, \; A_3 A_4, \;\ldots \] be equal to one another. Then, among this series of points, there always exists a certain point $A_n$ such that $B$ lies between $A$ and $A_n$.*

**Lean reading.** `ArchimedesWith Point Equal`: the points are a sequence `A : ℕ → Point` with
`A 0` Hilbert's `A` and `A n` his `A_n`; the hypotheses are `Between (A 0) (A 1) B`,
`Between (A n) (A (n+1)) (A (n+2))` for all `n` ("`A_1` between `A` and `A_2`, `A_2` between `A_1`
and `A_3`, …") and `Equal (A m) (A (m+1)) (A n) (A (n+1))` for all `m`, `n` ("equal to one another",
pairwise: the weakest reading; for an equivalence relation it is the same as "all equal to `AA_1`").
The conclusion is `∃ n, Between (A 0) B (A n)`. That the points lie on one line ("upon a straight
line") follows from `BetweenOnLine` and I 2. `AxiomV` takes congruence as equality.

**Status.** definition
-/

/-- **Axiom V** (Archimedes), with congruent segments as equal segments. -/
def AxiomV [HasBetween Point] [HasSegCong Point] : Prop :=
  ArchimedesWith Point SegCong

/-!
## [s8.linear] Archimedes's axiom is linear

*(§ 8)*

> The axiom of Archimedes is a *linear* axiom.

**Lean reading.** Reflected in the hierarchy: `Archimedes` extends only `LineOrder` and is shared by
plane and space geometry.

**Status.** remark
-/

end GroupV

/-- **Axiom V** (with groups I, II 1–4), congruent segments counting as equal. Shared by plane and
space geometry. Results that use it also assume `SegmentCongruence`. -/
class Archimedes (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point]
    [HasSegCong Point] : Prop extends LineOrder Point Line where
  ax_V : AxiomV Point

/-- **Plane geometry**: the plane axioms of all five groups I–V. -/
class PlaneGeometry (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point]
    [HasSegCong Point] [HasAngCong Point] : Prop
    extends PlaneParallels Point Line, PlaneCongruence Point Line, Archimedes Point Line

/-- **Space geometry**: all five groups of axioms I–V. -/
class SpaceGeometry (Point : Type u) (Line : Type v) (Plane : Type w) [HasLines Point Line]
    [HasPlanes Point Plane] [HasBetween Point] [HasSegCong Point] [HasAngCong Point] : Prop
    extends SpaceParallels Point Line Plane, SpaceCongruence Point Line Plane, Archimedes Point Line

/-!
## [ax.completeness] Axiom of Completeness

*(§ 8)*

> [Note: See Hilbert, “Ueber den Zahlenbegriff,” *Berichte der deutschen Mathematiker-Vereinigung*, 1900.] *(Vollständigkeit): To a system of points, straight lines, and planes, it is impossible to add other elements in such a manner that the system thus generalized shall form a new geometry obeying all of the five groups of axioms. In other words, the elements of geometry form a system which is not susceptible of extension, if we regard the five groups of axioms as valid.*

**Lean reading.** "Adding elements" so that the result is a "generalized system" is an *extension*:
a `SpaceEmbedding` of `(Point, Line, Plane)` into another structure `(Point', Line', Plane')`
consists of injective maps on points, lines and planes that preserve *and reflect* incidence
(`A ∈ a`, `A ∈ α`), betweenness and both congruences, i.e. the relations of the old system are the
ones induced by the new system. `SpaceComplete Point Line Plane`: for every structure
`(Point', Line', Plane')` (in the same universes) satisfying all five groups (`SpaceGeometry`,
"a new geometry obeying all of the five groups") and every embedding into it, the three maps are
surjective (nothing was added). `PlaneComplete` is the same for plane geometry (`PlaneGeometry`,
`PlaneEmbedding`). Choices: (1) the old system is not assumed to satisfy the axioms in the
definition (the axiom is used together with `SpaceGeometry`); (2) the new geometry must satisfy the
same groups as the old, in the version (plane or space) at hand; (3) preservation is required on all
tuples, degenerate (junk) ones included: since the axioms do not constrain the congruences on
degenerate tuples beyond `segCong_swap`, any extension can be modified there to agree with the old
system, so this is no restriction; (4) surjectivity is required on every sort, literally "no other
elements" (it would follow from surjectivity on points by I 2, I 4, I 7). Hilbert's remark that the
axiom is not used in the sequel is respected: nothing in the project assumes it unless a unit says
so.

**Status.** definition
-/

/-- An **extension** of a system of points and lines `(P, L)` to `(P', L')`: injective maps
preserving and reflecting incidence, betweenness and the congruences. -/
structure PlaneEmbedding (P L P' L' : Type*) [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [HasLines P' L'] [HasBetween P'] [HasSegCong P'] [HasAngCong P'] where
  /-- The map on points. -/
  pt : P → P'
  /-- The map on lines. -/
  line : L → L'
  pt_injective : Function.Injective pt
  line_injective : Function.Injective line
  mem_iff : ∀ (A : P) (a : L), pt A ∈ line a ↔ A ∈ a
  between_iff : ∀ A B C : P, Between (pt A) (pt B) (pt C) ↔ Between A B C
  segCong_iff : ∀ A B C D : P, SegCong (pt A) (pt B) (pt C) (pt D) ↔ SegCong A B C D
  angCong_iff : ∀ A B C D E F : P,
    AngCong (pt A) (pt B) (pt C) (pt D) (pt E) (pt F) ↔ AngCong A B C D E F

/-- An **extension** of a system of points, lines and planes. -/
structure SpaceEmbedding (P L Pl P' L' Pl' : Type*) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P']
    [HasSegCong P'] [HasAngCong P'] extends PlaneEmbedding P L P' L' where
  /-- The map on planes. -/
  plane : Pl → Pl'
  plane_injective : Function.Injective plane
  memPlane_iff : ∀ (A : P) (α : Pl), pt A ∈ plane α ↔ A ∈ α

/-- **Axiom of Completeness**, plane geometry: every extension to a plane geometry is trivial. -/
def PlaneComplete (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] : Prop :=
  ∀ (P' : Type u) (L' : Type v) [HasLines P' L'] [HasBetween P'] [HasSegCong P'] [HasAngCong P'],
    PlaneGeometry P' L' → ∀ e : PlaneEmbedding P L P' L',
      Function.Surjective e.pt ∧ Function.Surjective e.line

/-- **Axiom of Completeness**, space geometry: every extension to a space geometry is trivial. -/
def SpaceComplete (P : Type u) (L : Type v) (Pl : Type w) [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ (P' : Type u) (L' : Type v) (Pl' : Type w) [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P']
    [HasSegCong P'] [HasAngCong P'],
    SpaceGeometry P' L' Pl' → ∀ e : SpaceEmbedding P L Pl P' L' Pl',
      Function.Surjective e.pt ∧ Function.Surjective e.line ∧ Function.Surjective e.plane

/-- The identity is an extension (so completeness is about *proper* extensions). -/
def PlaneEmbedding.id (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] : PlaneEmbedding P L P L where
  pt := _root_.id
  line := _root_.id
  pt_injective := Function.injective_id
  line_injective := Function.injective_id
  mem_iff _ _ := Iff.rfl
  between_iff _ _ _ := Iff.rfl
  segCong_iff _ _ _ _ := Iff.rfl
  angCong_iff _ _ _ _ _ _ := Iff.rfl

/-!
## [s8.completeness_remark] The Axiom of Completeness is not purely geometrical

*(§ 8)*

> Remark. [Note: Added by Professor Hilbert in the French translation.—*Tr.*] To the preceeding five groups of axioms, we may add the following one, which, although not of a purely geometrical nature, merits particular attention from a theoretical point of view.

**Lean reading.** The Axiom of Completeness (`ax.completeness`) is not a sixth group: it is not a
field of any class, and `PlaneComplete` / `SpaceComplete` are hypotheses that a result must name.
"Not of a purely geometrical nature": it quantifies over all other systems (`P'`, `L'`, `Pl'`) and
all embeddings into them, not over the points, lines and planes of the system itself.

**Status.** remark
-/

/-!
## [s8.bolzano] Completeness gives Bolzano's theorem

*(§ 8)*

> This axiom gives us nothing directly concerning the existence of limiting points, or of the idea of convergence. Nevertheless, it enables us to demonstrate Bolzano's theorem by virtue of which, for all sets of points situated upon a straight line between two definite points of the same line, there exists necessarily a point of condensation, that is to say, a limiting point.

**Lean reading.** A point of condensation of a set `S` of points between `A ≠ B` is a point `P` of
the line `AB` such that every segment `UV` of that line with `P` between `U` and `V` contains a point
of `S` other than `P` (`IsCondensationPointOn A B S P`; neighbourhoods are taken along the line,
not in the plane). "For all sets" must be "for all *infinite* sets" (a finite set has no point of
condensation), so `BolzanoProperty` asks it for infinite `S ⊆ Seg A B`. The claim is
`CompletenessGivesBolzano`: every space geometry satisfying `SpaceComplete` has `BolzanoProperty`.
The proof needs the coordinatization of Chapters III and V, so it is not in this file: the claim is
proved as `completenessGivesBolzano` in `CompletenessClose.lean`. A space geometry with I–V is
embedded into the analytic geometry `Coord ℝ 3` (`CC.PreEmb`, the congruences being compared on
genuine segments and angles only): by rectangular co-ordinates taken from the archimedean field of
segments of a plane if the system has a plane (`CC.exists_preEmb`), and by Hölder's real
co-ordinate of the line if it has no plane but two distinct points (`CC.exists_preEmb_line`; I–V
do not exclude this case, in which all points lie on one line). The copy of `Coord ℝ 3` in the
universes of the system, with its congruences changed on the degenerate tuples so as to agree with
those of the system, is an extension satisfying I–V, so `SpaceComplete` makes the embedding onto
(`CC.PreEmb.surjective_of_complete`); a system with two distinct points, as `A ≠ B` in the claim,
is thus carried bijectively onto `Coord ℝ 3`, betweenness corresponding to betweenness
(`CC.exists_bijective_emb`). A line is then parametrised by `ℝ` (`CC.line_param`), and the claim is
the theorem of Bolzano–Weierstrass on `[0, 1]` (`CC.bolzano_of_bijective`). The hypotheses are
satisfiable: `Coord ℝ 3` satisfies I–V (`real_spaceGeometry`, Analytic.lean) and `SpaceComplete`
(`CC.spaceComplete_coord_real`), which gives the instance `bolzano_coord_real`.

**Status.** proved
-/

section GroupVConsequences

/-- `P` is a **point of condensation** of the set `S` of points of the line through `A ≠ B`: `P`
lies on that line, and every segment `UV` of the line having `P` between its extremities contains a
point of `S` other than `P`. -/
def IsCondensationPointOn {Point : Type u} {Line : Type v} [HasLines Point Line] [HasBetween Point]
    (A B : Point) (S : Set Point) (P : Point) : Prop :=
  Collinear A B P ∧ ∀ U V : Point, Collinear A B U → Collinear A B V → Between U P V →
    ∃ X ∈ S, X ≠ P ∧ Between U X V

/-- **Bolzano's theorem** on a line: every infinite set of points lying between two distinct
points `A`, `B` has a point of condensation. -/
def BolzanoProperty (Point : Type u) {Line : Type v} [HasLines Point Line] [HasBetween Point] :
    Prop :=
  ∀ (A B : Point) (S : Set Point), A ≠ B → S ⊆ Seg A B → S.Infinite →
    ∃ P : Point, IsCondensationPointOn A B S P

/-- **Hilbert's claim** (§ 8): the Axiom of Completeness, with groups I–V, gives Bolzano's
theorem. Proved as `completenessGivesBolzano` in `CompletenessClose.lean`. -/
def CompletenessGivesBolzano : Prop :=
  ∀ (P : Type u) (L : Type v) (Pl : Type w) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceGeometry P L Pl → SpaceComplete P L Pl → BolzanoProperty P

/-!
## [s8.real_numbers] Completeness gives the correspondence with the real numbers

*(§ 8)*

> From a theoretical point of view, the value of this axiom is that it leads indirectly to the introduction of limiting points, and, hence, renders it possible to establish a one-to-one correspondence between the points of a segment and the system of real numbers. However, in what is to follow, no use will be made of the “axiom of completeness.”

**Lean reading.** The correspondence is read as order-preserving (otherwise it would be a mere
statement about cardinalities, which is not what Hilbert means): `SegmentRealCorrespondence` asks,
for `A ≠ B`, for a bijection `f` from the points of the segment `AB` onto `ℝ` with `Between A X Y ↔
f X < f Y` (the order of the segment seen from `A`). The claim is `CompletenessGivesReals`; like
`s8.bolzano` it needs the coordinatization of Chapters III and V, and it is proved as
`completenessGivesReals` in `CompletenessClose.lean`. By the Axiom of Completeness the geometry is
carried bijectively onto the analytic geometry `Coord ℝ 3`, betweenness corresponding to
betweenness (`CC.exists_bijective_emb`, by the embedding described in `s8.bolzano`), so the line
`AB` has a real parameter `g` with `g 0 = A`, `g 1 = B`, in which betweenness is the order of `ℝ`
(`CC.line_param`). The segment `AB` then corresponds to the interval `(0, 1)`, which is
order-isomorphic to `ℝ` (`CC.reals_of_bijective`). The statement is not vacuous: `Coord ℝ 3`
satisfies I–V (`real_spaceGeometry`, Analytic.lean) and `SpaceComplete`
(`CC.spaceComplete_coord_real`), which gives the instance `segmentRealCorrespondence_coord_real`.
The last sentence is respected: no other file assumes `PlaneComplete` or `SpaceComplete` unless its
unit says so.

**Status.** proved
-/

/-- The points of every segment `AB` correspond one-to-one and in order to the real numbers. -/
def SegmentRealCorrespondence (Point : Type u) [HasBetween Point] : Prop :=
  ∀ A B : Point, A ≠ B →
    ∃ f : Seg A B ≃ ℝ, ∀ X Y : Seg A B, Between A (X : Point) Y ↔ f X < f Y

/-- **Hilbert's claim** (§ 8): the Axiom of Completeness, with groups I–V, gives the
correspondence between the points of a segment and the real numbers. Proved as
`completenessGivesReals` in `CompletenessClose.lean`. -/
def CompletenessGivesReals : Prop :=
  ∀ (P : Type u) (L : Type v) (Pl : Type w) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceGeometry P L Pl → SpaceComplete P L Pl →
      SegmentRealCorrespondence P

end GroupVConsequences

end HilbertFoundations
