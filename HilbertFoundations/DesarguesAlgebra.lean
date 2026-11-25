import HilbertFoundations.Order
import HilbertFoundations.Analytic
import HilbertFoundations.DesarguesAlgebraAux7

/-!
# The algebra of segments based on Desargues's theorem (§§ 24–30, Theorems 34–35)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 24. Introduction of an algebra of segments based upon Desargues's theorem and independent of the axioms of congruence
* § 25. The commutative and the associative law of addition for our new algebra of segments
* § 26. The associative law of multiplication and the two distributive laws for the new algebra of segments
* § 27. Equation of the straight line, based upon the new algebra of segments
* § 28. The totality of segments, regarded as a complex number system
* § 29. Construction of a geometry of space by aid of a desarguesian number system
* § 30. Significance of Desargues's theorem

## The development (helper modules)

The proofs are in seven helper modules; this file states Hilbert's claims and derives them.

* `DesarguesAlgebraAux.lean` — affine incidence in a plane geometry with I 1–2, III (`LPar`,
  `pline`, `ln`, `meet`); **Desargues's theorem** as a proposition (`DesarguesI`, `DesarguesII`,
  `DesarguesTheorem`); dilatations and translations (E. Artin, *Geometric Algebra*, ch. II); the
  *pencil construction*: from the second part of Desargues's theorem, translations `A ↦ B`
  (`exists_tr`) and dilatations with a given centre (`exists_cdil`) exist; the translations form a
  commutative group.
* `DesarguesAlgebraAux2.lean` — the frame (`Frame`), Hilbert's segments (`Seg`) with his sum and
  product **defined by his constructions** (`Frame.hsumPt`, `Frame.hmulPt`); these constructions are
  a translation and a dilatation (`hsumPt_eq`, `hmulPt_eq`); `DesAlg.Seg F` is a division ring
  (`Seg.instDivisionRing`); the plane is a 2-dimensional vector space over the segments acting on
  the right (`Vec F`, a module over `(DesAlg.Seg F)ᵐᵒᵖ`, basis `E, E'`), and its lines are the affine lines
  (`mem_ln_iff_smul`).
* `DesarguesAlgebraAux3.lean` — parallel projections preserve betweenness (`proj_between`, from
  Pasch); Hilbert's order of the segments; the segments form an ordered division ring; betweenness
  is `Y = t (Z - X) + X` with `0 < t < 1` (`between_iff_param`).
* `DesarguesAlgebraAux4.lean` — Desargues's theorem in a plane of a space geometry with I, III
  (`space_desargues`); the first part of Desargues's theorem from the second (`desarguesI_of_II`).
* `DesarguesAlgebraAux5.lean` — co-ordinates and Theorem 34; `PlaneInSpace`; the desarguesian
  plane as the plane `z = 0` of the coordinate space over its segments (`planeInSpace`); necessity
  (`desarguesTheorem_of_planeInSpace`).
* `DesarguesAlgebraAux6.lean` — the laws 1–16 in ordered division rings, Hilbert's order by
  sequences, `x' = x + c`, desarguesian number systems, betweenness by co-ordinates in § 29, the
  degenerate plane geometry without lines, the planes of space.
* `DesarguesAlgebraAux7.lean` — the laws 1–6 without Desargues's theorem (inverting Hilbert's
  constructions), laws 13–14 from the order axioms, the degenerate cases of the order convention of
  § 28, Hilbert's segment `e` of a line through the origin, the literal second part of Desargues's
  theorem refuted in the real plane, and the planes and lines of the space of § 29 described by
  Hilbert's equations (both directions).

Hilbert's proofs in §§ 25–26 are figure arguments (Figs. 43–47) that apply Desargues's theorem to
particular configurations; they tacitly assume the figures to be in general position (no two of the
constructed points or lines coincide, the triangles are genuine), so they do not cover all cases.
The proofs here follow Artin's method instead: the second part of Desargues's theorem gives the
translations and the dilatations, Hilbert's constructions are identified with these maps, and the
laws become the composition laws of the maps; every case is covered.
-/

namespace HilbertFoundations

open DesAlg

universe u v

/-!
## [s24.setting] The setting: plane geometry with I 1–2, II, III, without congruence

*(§ 24)*

> In order to see fully the significance of Desargues's theorem (theorem 32), let us take as the basis of our consideration a plane geometry where all of the axioms I 1–2, II–III are valid, that is to say, where all of the plane axioms of the first three groups hold, and then introduce into this geometry, in the following manner, a new algebra of segments independent of the axioms of congruence.

**Lean reading.** The plane geometry is a type of points `P` and lines `L` with `[PlaneOrder P L]`
(I 1–2 with the plane clauses of I 7, II 1–5) and `[PlaneParallels P L]` (III); no congruence is
used anywhere in this file. Desargues's theorem is a hypothesis, the proposition `DesarguesTheorem P`
of `DesarguesAlgebraAux.lean` (unit `s24.desargues`). Of the order axioms the algebraic part
(§§ 24–27) only uses that every line has a third point (II 2); the order of § 28 uses all of II.
Hilbert's Theorem 32 itself (Desargues's theorem from the axioms of congruence) belongs to
Desargues.lean; here it is a hypothesis.

**Status.** remark
-/

/-!
## [s24.desargues] Desargues's theorem as a hypothesis

*(§ 24)*

> In order to see fully the significance of Desargues's theorem (theorem 32), let us take as the basis of our consideration a plane geometry where all of the axioms I 1–2, II–III are valid, …

**Lean reading.** Theorem 32 (§ 22) has two parts, both formalized as propositions about a plane
geometry. `ParPts A B C D`: some line through `A, B` and some line through `C, D` have no common
point (Hilbert's "parallel"). `DesarguesI P` (first part): for triangles `ABC`, `A'B'C'` (non-collinear)
with `AB ∥ A'B'`, `AC ∥ A'C'`, `BC ∥ B'C'`, the lines `AA'`, `BB'`, `CC'` pass through one point
(`Collinear A A' O` etc.) or are pairwise parallel. `DesarguesII P` (second part, "the converse"):
for triangles `ABC`, `A'B'C'`, three lines `a ∋ A, A'`, `b ∋ B, B'`, `c ∋ C, C'` that are pairwise
distinct and pass through one point or are pairwise parallel, `AB ∥ A'B'` and `AC ∥ A'C'` imply
`BC ∥ B'C'`. The distinctness of the three joining lines is a correction: read literally, with
"parallel" meaning "without common point", the second part is false when two joining lines coincide
(in the ordinary plane: `O = (0,0)`, `A = (0,1)`, `A' = (0,2)`, `B = (1,0)`, `B' = (2,0)`,
`C = (-1,0)`, `C' = (-2,0)`: the joins pass through `O`, `AB ∥ A'B'`, `AC ∥ A'C'`, but `BC = B'C'`).
This counterexample is checked in Lean: `DesarguesIILiteral` is the literal second part (no
distinctness), `not_desarguesIILiteral_real` proves that it fails in the real plane `Coord ℝ 2`
(a model of I 1–2, II, III, `real_planeGeometry`), and `desarguesII_of_literal` that it implies the
corrected `DesarguesII`, so the correction only weakens the hypothesis.
With distinct joins the conclusion `BC ∥ B'C'` (and not merely "parallel or equal") holds.
`DesarguesTheorem P` is the conjunction. The algebra of §§ 24–28 needs only the second part, and
the first follows from it (`desarguesI_of_II`, proved below for unit `s30.first_part`).

**Status.** definition
-/

theorem desarguesTheorem_def {P : Type u} {L : Type v} [HasLines P L] :
    DesarguesTheorem P ↔ DesarguesI P ∧ DesarguesII P := Iff.rfl

theorem desarguesII_def {P : Type u} {L : Type v} [HasLines P L] :
    DesarguesII P ↔ ∀ (A B C A' B' C' : P) (a b c : L), ¬Collinear A B C → ¬Collinear A' B' C' →
      A ∈ a → A' ∈ a → B ∈ b → B' ∈ b → C ∈ c → C' ∈ c → a ≠ b → a ≠ c → b ≠ c →
      ((∃ O : P, O ∈ a ∧ O ∈ b ∧ O ∈ c) ∨
        (¬Meets (Point := P) a b ∧ ¬Meets (Point := P) a c ∧ ¬Meets (Point := P) b c)) →
      ParPts A B A' B' → ParPts A C A' C' → ParPts B C B' C' := Iff.rfl

theorem desarguesI_def {P : Type u} {L : Type v} [HasLines P L] :
    DesarguesI P ↔ ∀ A B C A' B' C' : P, ¬Collinear A B C → ¬Collinear A' B' C' →
      ParPts A B A' B' → ParPts A C A' C' → ParPts B C B' C' →
      (∃ O : P, Collinear A A' O ∧ Collinear B B' O ∧ Collinear C C' O) ∨
        (ParPts A A' B B' ∧ ParPts A A' C C' ∧ ParPts B B' C C') := Iff.rfl

theorem parPts_def {P : Type u} {L : Type v} [HasLines P L] (A B C D : P) :
    ParPts A B C D ↔ ∃ a b : L, A ∈ a ∧ B ∈ a ∧ C ∈ b ∧ D ∈ b ∧ ¬Meets (Point := P) a b :=
  Iff.rfl

/-- The literal second part of Theorem 32 fails in the real plane (two joins coinciding). -/
theorem desargues_literal_false : ¬DesarguesIILiteral (Coord ℝ 2) :=
  not_desarguesIILiteral_real

theorem desarguesII_of_desarguesIILiteral {P : Type u} {L : Type v} [HasLines P L]
    (h : DesarguesIILiteral P) : DesarguesII P :=
  desarguesII_of_literal h

section Plane

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L]

/-!
## [s24.frame] The two fixed lines, the segment 0 and the segment 1

*(§ 24)*

> Take in the plane two fixed straight lines intersecting in $O$, and consider only such segments as have $O$ for their origin and their other extremity in one of the fixed lines. We will regard the point $O$ itself as a segment and call it the segment $O$. We will indicate this fact by writing \[ OO = 0, or 0 = OO. \] Let $E$ and $E'$ be two definite points situated respectively upon the two fixed straight lines through $O$. Then, define the two segments $OE$ and $OE'$ as the segment 1 and write accordingly \begin{equation} OE = OE' = 1 or 1 = OE = OE'. \end{equation} We will call the straight line $EE'$, for brevity, the unit-line.

**Lean reading.** A `Frame P` consists of points `O`, `E`, `E'` with `O ≠ E` and `O, E, E'`
non-collinear: the fixed lines are `F.xl = OE` and `F.yl = OE'` (distinct, through `O`), the unit
line is `F.ul = EE'` (Hilbert tacitly takes `E, E' ≠ O`). A segment `OA` with `A` on `OE` is an
element of `DesAlg.Seg F` (its extremity `A`, with `A ∈ OE`); segments on `OE'` are identified with these
through the "equality" of unit `s24.equal`. The segment `0` is `O` and the segment `1` is `E` (and
`OE' = OE = 1`: `F.toY_E`). The existence of a frame is equivalent to the existence of a line
(`exists_frame`, `frame_nonempty_lines`); the hypothesis `[Nonempty L]` that the files carry is thus
implied by the frame.

**Status.** definition
-/

omit [HasBetween P] [PlaneOrder P L] in
theorem seg_zero_pt (F : Frame P) : (0 : DesAlg.Seg F).pt = F.O := rfl

omit [HasBetween P] [PlaneOrder P L] in
theorem seg_one_pt (F : Frame P) : (1 : DesAlg.Seg F).pt = F.E := rfl

omit [HasBetween P] [PlaneOrder P L] in
theorem frame_toY_E (F : Frame P) : F.toY F.E = F.E' := F.toY_E

theorem frame_nonempty_lines {P : Type u} {L : Type v} [HasLines P L] [Connection P L]
    (F : Frame P) : Nonempty L :=
  ⟨line F.O F.E F.hOE⟩

theorem frame_exists {P : Type u} {L : Type v} [HasLines P L] [PlaneConnection P L]
    [Nonempty L] : Nonempty (Frame P) :=
  exists_frame

/-!
## [s24.equal] Equal segments on the two fixed lines

*(§ 24)*

> If, furthermore, $A$ and $A'$ are points upon … the straight lines $OE$ and $OE'$, respectively, and, if the straight line $AA'$ joining them is parallel to $EE'$, then we will say that the segments OA and OA' are equal to one another, and write \[ OA=OA' or OA'=OA. \]

**Lean reading.** `F.toY A` is the point `A'` of `OE'` with `AA' ∥ EE'` (`A' ∈ pline EE' A`, which
includes `A = A' = O`), `F.toX` the inverse correspondence. `equal_segments`: for every `A` of `OE`
there is exactly one such `A'` on `OE'` (and conversely, `equal_segments'`), so "equal" is a
bijection between the segments on the two lines and `DesAlg.Seg F` represents all of them. Only axioms I and
III are used.

**Status.** definition
-/

omit [HasBetween P] [PlaneOrder P L] in
theorem equal_segments (F : Frame P) {A : P} (_hA : A ∈ (F.xl : L)) :
    ∃! A' : P, A' ∈ (F.yl : L) ∧ A' ∈ pline (F.ul : L) A :=
  ⟨F.toY A, ⟨F.toY_mem A, F.toY_par A⟩, fun _ ⟨h1, h2⟩ => F.toY_eq h1 h2⟩

omit [HasBetween P] [PlaneOrder P L] in
theorem equal_segments' (F : Frame P) {A' : P} (_hA' : A' ∈ (F.yl : L)) :
    ∃! A : P, A ∈ (F.xl : L) ∧ A ∈ pline (F.ul : L) A' :=
  ⟨F.toX A', ⟨F.toX_mem A', F.toX_par A'⟩, fun _ ⟨h1, h2⟩ => F.toX_eq h1 h2⟩

/-!
## [s24.sum] The sum of two segments

*(§ 24)*

> In order now to define the sum of the segments $a=OA$ and $b= OB$, we construct $AA'$ parallel to the unit-line $EE'$ and draw through $A'$ a parallel to $OE$ and through $B$ a parallel to $OE'$. Let these two parallels intersect in $A''$. Finally, draw through $A''$ a straight line parallel to the unit-line $EE'$. Let this parallel cut the two fixed lines $OE$ and $OE'$ in $C$ and $C'$ respectively. Then $c=OC= OC'$ is called the *sum* of the segments $a=OA$ and $b=OB$. We indicate this by writing \[ c=a+b, or a+b=c. \]

**Lean reading.** The addition of `DesAlg.Seg F` is this construction, literally (`seg_add_def`):
`A' = F.toY A`, `A'' = meet (parallel to OE through A') (parallel to OE' through B)`, `C =
F.toX A''` (the point of `OE` with `A''C ∥ EE'`; the point `C'` of `OE'` is `F.toY C`). The two
parallels through `A'` and `B` meet because `OE` and `OE'` do (`sum_construction_meets`), and the
parallel through `A''` meets `OE` because `EE'` does. No hypothesis beyond I and III is needed to
make the definition.

**Status.** definition
-/

omit [HasBetween P] [PlaneOrder P L] in
theorem seg_add_def (F : Frame P) (a b : DesAlg.Seg F) :
    (a + b).pt = F.toX (meet (pline (F.xl : L) (F.toY a.pt)) (pline (F.yl : L) b.pt)) := rfl

omit [HasBetween P] [PlaneOrder P L] in
theorem sum_construction_meets (F : Frame P) (A' B : P) :
    ∃! A'' : P, A'' ∈ pline (F.xl : L) A' ∧ A'' ∈ pline (F.yl : L) B :=
  ⟨_, meet_mem (not_lpar_pline F.nl_xy A' B),
    fun _ ⟨h1, h2⟩ => eq_meet (not_lpar_pline F.nl_xy A' B) h1 h2⟩

/-!
## [s24.product] The product of two segments

*(§ 24)*

> In order to define the product of a segment $a=OA$ by a segment $b=OB$, we make use of exactly the same construction as employed in § 15, except that, in place of the sides of a right angle, we make use here of the straight lines $OE$ and $OE'$. … Determine upon $OE'$ a point $A'$ so that $AA'$ is parallel to the unit-line $EE'$, and join $E$ with $A'$. Then draw through $B$ a straight line parallel to $EA'$. This parallel will intersect the fixed straight line $OE'$ in the point $C'$, and we call $c=OC'$ the product of the segment $a = OA$ by the segment $b = OB$. We indicate this relation by writing \[ c = ab, or ab = c. \]

**Lean reading.** The multiplication of `DesAlg.Seg F` is this construction (`seg_mul_def`): `A' =
F.toY A`, `C' = meet OE' (parallel to EA' through B)`, and the product is the segment `OC'`,
represented on `OE` by `F.toX C'`. The parallel to `EA'` through `B` meets `OE'` because `EA'` does
(at `A'`, with `E ∉ OE'`: `product_construction_meets`), including the case `A = O` (then `EA' = OE`
and `C' = O`). The comparison with § 15 is a remark.

**Status.** definition
-/

omit [HasBetween P] [PlaneOrder P L] in
theorem seg_mul_def (F : Frame P) (a b : DesAlg.Seg F) :
    (a * b).pt = F.toX (meet (F.yl : L) (pline (ln F.E (F.toY a.pt) : L) b.pt)) := rfl

omit [HasBetween P] [PlaneOrder P L] in
theorem product_construction_meets (F : Frame P) (A B : P) :
    ∃! C' : P, C' ∈ (F.yl : L) ∧ C' ∈ pline (ln F.E (F.toY A) : L) B :=
  ⟨_, meet_mem (not_lpar_pline_right (F.nl_EA' A) B),
    fun _ ⟨h1, h2⟩ => eq_meet (not_lpar_pline_right (F.nl_EA' A) B) h1 h2⟩

/-!
## [s25.setting] The laws of § 13 for the new algebra

*(§ 25)*

> In this section, we shall investigate the laws of operation, as enumerated in § 13, in order to see which of these hold for our new algebra of segments, when we base our considerations upon a plane geometry in which axioms I 1–2, II–III are all fulfilled, and, moreover, in which Desargues's theorem also holds.

**Lean reading.** From here on the theorems assume, besides `[PlaneOrder P L] [PlaneParallels P L]`,
the hypothesis `hD : DesarguesII P` (the second part of Desargues's theorem), which is weaker than
Hilbert's `DesarguesTheorem P` (it is all that the proofs need; the first part follows from it,
unit `s30.first_part`). The laws themselves are the units below.

**Status.** remark
-/

/-!
## [s25.commutative] The commutative law of addition

*(§ 25)*

> First of all, we shall show that, for the addition of segments as defined in § 24, the commutative law \[ a+ b = b+a \] holds.

**Lean reading.** `seg_add_comm`: for all segments `a`, `b` (Hilbert's construction `+`),
`a + b = b + a`, from the second part of Desargues's theorem. Proof: Hilbert's sum `a + b` is the image
of `A` under the translation `O ↦ B` (`hsumPt_eq`); translations exist (the parallel case of the
second part of Desargues's theorem, through the pencil construction) and commute. Hilbert's figure
proof (Fig. 43) applies both parts of Desargues's theorem to triangles of the figure, assuming them
non-degenerate (e.g. `a ≠ b`, `A, B ≠ O`); the proof here covers all cases.

**Status.** proved
-/

theorem seg_add_comm (hD : DesarguesII P) {F : Frame P} (a b : DesAlg.Seg F) : a + b = b + a :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  add_comm a b

/-!
## [s25.associative] The associative law of addition

*(§ 25)*

> To prove the associative law of addition \[ a+(b+c)=(a+b)+c, \] we shall make use of figure 44. In consequence of the commutative law of addition just demonstrated, the above formula states that the straight line $A''B''$ must be parallel to the unit-line. [Fig. 44] The validity of this statement is evident, since the shaded part of figure 44 corresponds exactly with figure 43.

**Lean reading.** `seg_add_assoc`: `a + (b + c) = (a + b) + c`, from the second part of Desargues's
theorem: the composite of the translations `O ↦ B` and `O ↦ C` is the translation `O ↦ B + C`
(translations are determined by one image). Hilbert's proof refers to a figure (Fig. 44, to be
reconstructed: the figure of the commutative law applied to the points of `a + b` and `c`).

**Status.** proved
-/

theorem seg_add_assoc (hD : DesarguesII P) {F : Frame P} (a b c : DesAlg.Seg F) :
    a + (b + c) = (a + b) + c :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  (add_assoc a b c).symm

/-!
## [s26.associative_mul] The associative law of multiplication

*(§ 26)*

> The associative law of multiplication \[ a(bc)=(ab)c \] has also a place in our new algebra of segments.

**Lean reading.** `seg_mul_assoc`: `a (b c) = (a b) c` for Hilbert's product, from the second part of
Desargues's theorem. Proof: Hilbert's product `a b` is the image of `A` under the dilatation with
centre `O` mapping `E` to `B` (`hmulPt_eq`); these dilatations exist (the concurrent case of the
second part of Desargues's theorem), are determined by the image of one point, and the composite of
the dilatations `E ↦ B`, `E ↦ C` is the dilatation `E ↦ B C`. Hilbert's proof (Fig. 45) uses
Desargues's theorem twice on generic triangles.

**Status.** proved
-/

theorem seg_mul_assoc (hD : DesarguesII P) {F : Frame P} (a b c : DesAlg.Seg F) :
    a * (b * c) = (a * b) * c :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  (mul_assoc a b c).symm

/-!
## [s26.distributive_left] The first distributive law

*(§ 26)*

> Finally, upon the basis of Desargues's theorem, we shall show that the two distributive laws \[ a (b+c) = ab+ac \] and \[ (a+b)c = ac+bc \] hold for our algebra of segments. In the proof of the first one of these laws, we shall make use of figure 46. … Our proposition amounts to asserting that we must necessarily have also $F'F''$ parallel to $A'A''$ and to $C'C''$.

**Lean reading.** `seg_mul_add`: `a (b + c) = a b + a c`. In terms of maps, `x (b + c)` is the
dilatation `E ↦ B + C` applied to `X`, and the claim is that the pointwise sum of the dilatations
`E ↦ B` and `E ↦ C` is again a dilatation (it maps lines into parallel lines because sums of vectors
parallel to a line are parallel to it, `trf_par`), hence the dilatation `E ↦ B + C` (`dl_sum`). Only
the second part of Desargues's theorem is used. Hilbert's figure proof (Fig. 46, auxiliary points
`F', F'', G, H₁, H₂, J, P`) applies Desargues's theorem six times to generic triangles.

**Status.** proved
-/

theorem seg_mul_add (hD : DesarguesII P) {F : Frame P} (a b c : DesAlg.Seg F) :
    a * (b + c) = a * b + a * c :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  mul_add a b c

/-!
## [s26.distributive_right] The second distributive law

*(§ 26)*

> To prove the second formula of the distributive law, we make use of an entirely different figure,–figure 47. … That which we are to prove amounts, then, to demonstrating that \[ DJ must be parallel to D'J'. \]

**Lean reading.** `seg_add_mul`: `(a + b) c = a c + b c`: a dilatation with centre `O` is additive
(`dl_add`): the conjugate of a translation by a dilatation is a translation. Only the second part of
Desargues's theorem is used. Hilbert's figure proof (Fig. 47) again assumes general position.

**Status.** proved
-/

theorem seg_add_mul (hD : DesarguesII P) {F : Frame P} (a b c : DesAlg.Seg F) :
    (a + b) * c = a * c + b * c :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  add_mul a b c

/-!
## [s27.recap] The laws established in §§ 25–26

*(§ 27)*

> In \S§ 24–26, we have introduced into the plane geometry an algebra of segments in which the commutative law of addition and that of multiplication, as well as the two distributive laws, hold. This was done upon the assumption that the axioms cited in § 24, as also the theorem of Desargues, were valid.

**Lean reading.** As printed, "the commutative law … of multiplication" is wrong: §§ 25–26 prove
the commutative and the associative laws of addition, the *associative* law of multiplication and
the two distributive laws (the German has "das assoziative Gesetz der Multiplikation"); the
commutative law of multiplication is not proved and does not hold in every desarguesian plane (it is
equivalent to Pascal's theorem, Chapter VI; § 28 states it as the single exception, and
`th34_right` shows that it fails exactly when some right-sided equation `x a + y b + c = 0` is not
a line). `seg_laws_25_26` is the corrected statement: the five laws hold, from the second part of
Desargues's theorem.

**Status.** proved (corrected)
-/

theorem seg_laws_25_26 (hD : DesarguesII P) (F : Frame P) :
    (∀ a b : DesAlg.Seg F, a + b = b + a) ∧ (∀ a b c : DesAlg.Seg F, a + (b + c) = (a + b) + c) ∧
      (∀ a b c : DesAlg.Seg F, a * (b * c) = (a * b) * c) ∧
      (∀ a b c : DesAlg.Seg F, a * (b + c) = a * b + a * c) ∧
      (∀ a b c : DesAlg.Seg F, (a + b) * c = a * c + b * c) :=
  ⟨seg_add_comm hD, seg_add_assoc hD, seg_mul_assoc hD, seg_mul_add hD, seg_add_mul hD⟩

/-!
## [s27.coordinates] Co-ordinates

*(§ 27)*

> Definition. Take the two given fixed straight lines lying in the plane and intersecting in $O$ as the axis of $x$ and of $y$, respectively. Let us suppose any point $P$ of the plane determined by the two segments $x$, $y$ which we obtain upon the $x$-axis and $y$-axis, respectively, by drawing through $P$ parallels to these axes. These segments are called the *co-ordinates* of the point $P$.

**Lean reading.** `F.xc X` is the segment `OX₁` cut off on the `x`-axis `OE` by the parallel to the
`y`-axis through `X`; `F.yc X` is the segment `OX₂` cut off on the `y`-axis by the parallel to the
`x`-axis, represented (as a segment of `DesAlg.Seg F`) by the "equal" segment on `OE`. "Determined by the two
segments" is proved: the co-ordinates determine the point, and every pair of segments is the pair of
co-ordinates of a point (`coords_bijective`). Like the definition itself this needs only I 1–2 and
III, not Desargues's theorem: the point with co-ordinates `x`, `y` is the common point of the
parallel to the `y`-axis through `x` and the parallel to the `x`-axis through the point of the
`y`-axis "equal" to `y`.

**Status.** definition
-/

omit [HasBetween P] [PlaneOrder P L] in
theorem coords_bijective (F : Frame P) :
    Function.Bijective (fun X : P => (F.xc X, F.yc X)) :=
  coords_bijective_nd F

/-!
## [th.34] Theorem 34

*(§ 27)*

> The co-ordinates $x$, $y$ of a point on an arbitrary straight line always satisfy an equation in these segments of the form \[ ax+by+c = 0. \] In this equation, the segments $a$ and $b$ stand necessarily to the left of the co-ordinates $x$ and $y$. The segments $a$ and $b$ are never both zero and $c$ is an arbitrary segment.

**Lean reading.** `theorem34`: for every line `l` there are segments `a`, `b`, `c` with `a`, `b` not
both zero such that a point lies on `l` iff `a x + b y + c = 0` for its co-ordinates (Hilbert's
product, the coefficients on the left). This is stronger than "the co-ordinates of a point on `l`
satisfy the equation": the points of `l` are exactly the solutions. "The segments `a`, `b` stand
necessarily to the left" is the content of `th34_right` (unit `s27.right_coefficients`): with the
coefficients on the right the statement fails as soon as the multiplication is not commutative.
Assumptions: I 1–2, II, III and the second part of Desargues's theorem. Proof: the points of the line
`AB` are `x = (x_B - x_A) t + x_A`, `y = (y_B - y_A) t + y_A` (the vector structure,
`mem_ln_iff_coord`), and a parametrized line is the solution set of a left-sided equation
(`line_eq_alg`). Hilbert's own proof (Figs. 48, 49) goes through the special lines through `O` and
the translation `x' = x + c` (units `s27.origin_line`, `s27.translate`, `s27.equation_steps`); it
does not treat the lines parallel to the `x`-axis (see `s27.normal_form`).

**Status.** proved
-/

theorem theorem34 (hD : DesarguesII P) (F : Frame P) (l : L) :
    ∃ a b c : DesAlg.Seg F, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ X : P, X ∈ l ↔ a * F.xc X + b * F.yc X + c = 0 :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  th34_line l

/-!
## [s27.converse] Every linear equation represents a line

*(§ 27)*

> Conversely, every equation in these segments and of this form represents always a straight line in the plane geometry under consideration.

**Lean reading.** `theorem34_converse`: for segments `a`, `b`, `c` with `a`, `b` not both zero there
is a line `l` whose points are exactly the solutions of `a x + b y + c = 0`.

**Status.** proved
-/

theorem theorem34_converse (hD : DesarguesII P) (F : Frame P) (a b c : DesAlg.Seg F)
    (h : a ≠ 0 ∨ b ≠ 0) : ∃ l : L, ∀ X : P, X ∈ l ↔ a * F.xc X + b * F.yc X + c = 0 :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  th34_converse a b c h

/-!
## [s27.origin_line] A line through the origin: `ex = y`

*(§ 27)*

> Proof. Suppose that the straight line $l$ passes through the origin $O$. … Finally, through the extremity of the segment $1$, laid off on the $x$-axis, draw a straight line $h$ parallel to $AB$. This parallel cuts off upon the $y$-axis the segment $e$. … Since $g$ is always parallel to $h$, it follows that the co-ordinates $x$, $y$ of the point $P$ must satisfy the equation $$ ex=g. $$

**Lean reading.** "`ex = g`" is a misprint for `ex = y` (as the later formula "`ex = y` and
`x' = x + c`" shows). `origin_line_eq`: for a line `l` through `O` other than the `y`-axis there is a
segment `e` with `X ∈ l ↔ y = e x`. `origin_line_hilbert` proves Hilbert's argument as stated: for a
point `C ≠ O` of `l` with feet `A` (on the `x`-axis, `F.xc C`) and `B` (on the `y`-axis,
`F.yfoot C`), (1) for every point `X ≠ O` of `l` the line `g` joining the feet of `X` is parallel
to `AB` (the step "from the second part of Desargues's theorem, `g` is always parallel to `AB`"),
and (2) with `e` the segment cut off on the `y`-axis by the parallel `h` to `AB` through `E`, the
points of `l` are exactly the solutions of `e x = y`. The `y`-axis itself (`x = 0`) is not of this
form; Hilbert's figure tacitly excludes it (hypothesis `l ≠ F.yl`).

**Status.** proved (corrected)
-/

theorem origin_line_eq (hD : DesarguesII P) (F : Frame P) {l : L} (hO : F.O ∈ l)
    (hl : l ≠ F.yl) : ∃ e : DesAlg.Seg F, ∀ X : P, X ∈ l ↔ F.yc X = e * F.xc X :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  origin_line hO hl

theorem origin_line_hilbert_construction (hD : DesarguesII P) (F : Frame P) {l : L}
    (hO : F.O ∈ l) (hl : l ≠ F.yl) {C : P} (hC : C ∈ l) (hCO : C ≠ F.O) :
    (∀ X : P, X ∈ l → X ≠ F.O →
      LPar P (ln (F.xc X).pt (F.yfoot X) : L) (ln (F.xc C).pt (F.yfoot C))) ∧
    ∀ X : P, X ∈ l ↔ F.yc X =
      ⟨F.toX (meet (F.yl : L) (pline (ln (F.xc C).pt (F.yfoot C) : L) F.E)), F.toX_mem _⟩ *
        F.xc X :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  origin_line_hilbert hO hl hC hCO

/-!
## [s27.translate] The step `x' = x + c`

*(§ 27)*

> Moreover, in figure 49 let $l'$ be any arbitrary straight line in our plane. This straight line will cut off on the $x$-axis the segment $c=OO'$. … We shall now undertake to show that the equation \[ x'=x+c \] is fulfilled by the segments in question.

**Lean reading.** `translate_step`: let `l'` meet the `x`-axis in `O'` (`c = OO'`), let `P'` lie on
`l'`, and let `P` be the point of the parallel to `l'` through `O` on the parallel to the `x`-axis
through `P'`; then `x(P') = x(P) + c`, and `P`, `P'` have the same second co-ordinate `y` (both
cut off `y = OB` on the `y`-axis, as Hilbert says). The tacit assumption that `l'` cuts the `x`-axis
in one point (`l'` not parallel to it) is made explicit. Proof: the translation `O ↦ O'` maps `P` to
`P'` and adds `c` to the first co-ordinate (Hilbert's figure argument applies Desargues's theorem
four times).

**Status.** proved
-/

theorem translate_step (hD : DesarguesII P) (F : Frame P) {l' : L} {O' P' Q : P}
    (hO' : O' ∈ (F.xl : L)) (hO'l : O' ∈ l') (hl : ¬LPar P l' F.xl) (hP' : P' ∈ l')
    (hQ : Q ∈ pline l' F.O) (hQP : Q ∈ pline (F.xl : L) P') :
    F.xc P' = F.xc Q + ⟨O', hO'⟩ ∧ F.yc Q = F.yc P' :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  ⟨translate_coord hO' hO'l hl hP' hQ hQP, yc_eq_of_pline hQP⟩

/-!
## [s27.n] The segment `n`

*(§ 27)*

> If we denote, finally, by $n$ the segment which added to the segment 1 gives the segment 0, then, from this last equation, we may easily deduce the following

**Lean reading.** `segment_n`: there is exactly one segment `n` with `1 + n = 0` (law 3); it is `-1`.

**Status.** proved
-/

theorem segment_n (hD : DesarguesII P) (F : Frame P) : ∃! n : DesAlg.Seg F, 1 + n = 0 := by
  have : Fact (DesarguesII P) := ⟨hD⟩
  exact ⟨-1, add_neg_cancel 1, fun n hn => eq_neg_of_add_eq_zero_right hn⟩

/-!
## [s27.equation_steps] From `ex = y` and `x' = x + c` to `ex' + ny + nec = 0`

*(§ 27)*

> From the two equations already obtained, viz.: \begin{equation} ex = y and x' = x + c, \end{equation} follows at once the equation \begin{equation} ex' = y + ec. \end{equation} … \begin{equation} ex' + ny + nec = 0, \end{equation} and this equation is of the form required by theorem 34.

**Lean reading.** `equation_steps`: in the segments (any ring), `e x = y` and `x' = x + c` give
`e x' = y + e c` (first distributive law) and `e x' + n y + n e c = 0` for `1 + n = 0`. That the
result is of the form of Theorem 34 needs `e`, `n` not both zero, true as `n ≠ 0`.

**Status.** proved
-/

theorem equation_steps {D : Type*} [Ring D] {e x y x' c n : D} (h1 : e * x = y) (h2 : x' = x + c)
    (hn : 1 + n = 0) : e * x' = y + e * c ∧ e * x' + n * y + n * e * c = 0 := by
  have hn' : n = -1 := eq_neg_of_add_eq_zero_right hn
  refine ⟨by rw [h2, mul_add, h1], ?_⟩
  rw [hn', h2, ← h1]; noncomm_ring

/-!
## [s27.normal_form] Bringing an equation into the form `ex + ny + nec = 0`

*(§ 27)*

> We can now show that the second part of the theorem is equally true; for, every linear equation \begin{equation} ax + by + c = 0 \end{equation} may evidently be brought into the required form \begin{equation} ex + ny + nec = 0 \end{equation} by a left-sided multiplication by a properly chosen segment.

**Lean reading.** As printed this is false: a left-sided multiplication by `d ≠ 0` brings
`a x + b y + c = 0` into the form `e x + n y + n e c' = 0` (`n = -1`) iff `b ≠ 0` and (`a ≠ 0` or
`c = 0`) (`normal_form_iff`, in any division ring): the lines parallel to the `y`-axis (`b = 0`) and
the lines parallel to the `x`-axis not through `O` (`a = 0`, `c ≠ 0`) are not of this form, e.g.
`y + 1 = 0` (`normal_form_counterexample`). Hilbert's proof of the first part also covered only the
lines meeting the `x`-axis in one point. The converse of Theorem 34 is nevertheless true
(`theorem34_converse`).

**Status.** proved (corrected)
-/

theorem normal_form_iff {D : Type*} [DivisionRing D] (a b c : D) :
    (∃ d e c' : D, d ≠ 0 ∧ d * a = e ∧ d * b = -1 ∧ d * c = -1 * e * c') ↔
      b ≠ 0 ∧ (a ≠ 0 ∨ c = 0) := by
  constructor
  · rintro ⟨d, e, c', hd, ha, hb, hc⟩
    refine ⟨fun h => by rw [h, mul_zero] at hb; exact zero_ne_one (neg_eq_zero.1 hb.symm).symm, ?_⟩
    by_cases ha0 : a = 0
    · right
      rw [ha0, mul_zero] at ha
      rw [← ha, mul_zero, zero_mul] at hc
      exact (mul_eq_zero.1 hc).resolve_left hd
    · exact Or.inl ha0
  · rintro ⟨hb, ha | hc⟩
    · refine ⟨-b⁻¹, -b⁻¹ * a, (-1 * (-b⁻¹ * a))⁻¹ * (-b⁻¹ * c), neg_ne_zero.2 (inv_ne_zero hb),
        rfl, by rw [neg_mul, inv_mul_cancel₀ hb], ?_⟩
      have hne : -1 * (-b⁻¹ * a) ≠ 0 := by
        rw [neg_one_mul, neg_mul, neg_neg]; exact mul_ne_zero (inv_ne_zero hb) ha
      rw [← mul_assoc (-1 * (-b⁻¹ * a)), mul_inv_cancel₀ hne, one_mul]
    · refine ⟨-b⁻¹, -b⁻¹ * a, 0, neg_ne_zero.2 (inv_ne_zero hb), rfl,
        by rw [neg_mul, inv_mul_cancel₀ hb], by rw [hc, mul_zero, mul_zero]⟩

theorem normal_form_counterexample {D : Type*} [DivisionRing D] :
    ¬∃ d e c' : D, d ≠ 0 ∧ d * 0 = e ∧ d * 1 = -1 ∧ d * 1 = -1 * e * c' := by
  rw [normal_form_iff]
  rintro ⟨-, h | h⟩
  · exact h rfl
  · exact one_ne_zero h

/-!
## [s27.right_coefficients] Equations with the coefficients on the right

*(§ 27)*

> It must be expressly stated, however, that, by our hypothesis, an equation of segments of the form \begin{equation} xa + yb + c = 0, \end{equation} where the segments $a$, $b$ stand to the right of the co-ordinates $x$, $y$ does not, in general, represent a straight line.

**Lean reading.** "Does not, in general" is made precise by `right_coefficients_iff`: every equation
`x a + y b + c = 0` (`a`, `b` not both zero) represents a line iff the multiplication of the segments
is commutative. (One way: if `y = x s` is a line, it is the line through `(0,0)` and `(1,s)`, whose
points are `(t, s t)`, so `t s = s t`.) That non-commutative desarguesian planes exist (so that the
right-sided equations really fail to be lines) is Hilbert's § 33, not part of this unit.

**Status.** proved (reading)
-/

theorem right_coefficients_iff (hD : DesarguesII P) (F : Frame P) :
    (∀ a b c : DesAlg.Seg F, (a ≠ 0 ∨ b ≠ 0) →
      ∃ l : L, ∀ X : P, X ∈ l ↔ F.xc X * a + F.yc X * b + c = 0) ↔
    ∀ s t : DesAlg.Seg F, s * t = t * s :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  th34_right

/-!
## [s27.application] Theorem 34 is applied in § 30

*(§ 27)*

> In Section 30, we shall make an important application of theorem 34.

**Lean reading.** Theorem 34 (through `mem_ln_iff_smul`, of which it is the co-ordinate form) is what
identifies the lines of the plane with the lines `z = 0` of the space in Theorem 35.

**Status.** remark
-/

/-!
## [s28.laws_connection] Laws 1–11 hold for the segments

*(§ 28)*

> We see immediately that, for the new algebra of segments established in Section 24, theorems 1–6 of Section 13 are fulfilled. Moreover, by aid of Desargues's theorem, we have already shown in Sections 25 and 26 that the laws 7–11 of operation, as given in Section 13, are all valid in this algebra of segments. With the single exception of the commutative law of multiplication, therefore, all of the theorems of connection hold.

**Lean reading.** With Hilbert's operations on `DesAlg.Seg F` (`seg_add_def`, `seg_mul_def`),
`0 = O`, `1 = E`: `seg_laws_1_6` — the laws `Law1`–`Law6` of § 13 (Analytic.lean) hold from I 1–2
and III alone, without Desargues's theorem and without the order axioms, as Hilbert says ("we see
immediately"): sums and products exist and are unique by construction, `O` and `E` are neutral, and
the equations `a + x = b`, `y + a = b`, `a x = b`, `y a = b` (`a ≠ 0`) are solved by running
Hilbert's constructions backwards with parallels (`Seg.add_left_unique_nd`, …,
`Seg.mul_right_unique_nd`). `seg_laws_7_11` — the laws 7–11 from the second part of Desargues's
theorem (§§ 25–26). `seg_laws_1_11` combines them. The commutative law 12 is not claimed (see
`s27.recap`).

**Status.** proved
-/

omit [HasBetween P] [PlaneOrder P L] in
theorem seg_laws_1_6 (F : Frame P) :
    Law1 (DesAlg.Seg F) ∧ Law2 (DesAlg.Seg F) ∧ Law3 (DesAlg.Seg F) ∧ Law4 (DesAlg.Seg F) ∧
      Law5 (DesAlg.Seg F) ∧ Law6 (DesAlg.Seg F) :=
  seg_laws_1_6_nd F

theorem seg_laws_7_11 (hD : DesarguesII P) (F : Frame P) :
    Law7 (DesAlg.Seg F) ∧ Law8 (DesAlg.Seg F) ∧ Law9 (DesAlg.Seg F) ∧ Law10 (DesAlg.Seg F) ∧
      Law11 (DesAlg.Seg F) :=
  ⟨seg_add_assoc hD, seg_add_comm hD, seg_mul_assoc hD, seg_mul_add hD, seg_add_mul hD⟩

theorem seg_laws_1_11 (hD : DesarguesII P) (F : Frame P) :
    Law1 (DesAlg.Seg F) ∧ Law2 (DesAlg.Seg F) ∧ Law3 (DesAlg.Seg F) ∧ Law4 (DesAlg.Seg F) ∧ Law5 (DesAlg.Seg F) ∧ Law6 (DesAlg.Seg F) ∧
      Law7 (DesAlg.Seg F) ∧ Law8 (DesAlg.Seg F) ∧ Law9 (DesAlg.Seg F) ∧ Law10 (DesAlg.Seg F) ∧ Law11 (DesAlg.Seg F) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := seg_laws_1_6 F
  obtain ⟨h7, h8, h9, h10, h11⟩ := seg_laws_7_11 hD F
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-!
## [s28.order] The order of the segments

*(§ 28)*

> Finally, in order to make possible an order of magnitude of these segments, we make the following convention. Let $A$ and $B$ be any two distinct points of the straight line $OE$. Suppose then that the four points $O$, $E$, $A$, $B$ stand, in conformity with axiom II, 4, in a certain sequence. If this sequence is one of the following six possible ones, viz.: \[ ABOE, AOBE, AOEB, OABE, OAEB, OEAB, \] then we will call the segment $a = OA$ {\itshape smaller} than the segment $b = OB$ and indicate the same by writing \[ a < b. \] On the other hand, if the sequence is one of the six following ones, viz.: \[ BAOE, BOAE, BOEA, OBAE, OBEA, OEBA, \] then we will call the segment $a = OA$ greater than the segment $b = OB$, and we write accordingly \[ a > b. \] This convention remains in force whenever $A$ or $B$ coincides with $O$ or $E$, only then the coinciding points are to be regarded as a single point, and, consequently, we have only to consider the order of three points.

**Lean reading.** The order of `DesAlg.Seg F` is the order of sequence of the line `OE` in which `O`
precedes `E` (`OrderLin.lineLt O E` of Order.lean, built from II 1–4), uniformly for all `A`, `B`,
including the coincidences with `O`, `E`. `lt_iff_six_sequences` proves that for `A`, `B`, `O`, `E`
pairwise distinct `a < b` holds iff the four points stand in one of Hilbert's first six sequences
(a sequence `WXYZ` is `II4Arrangement W X Y Z`: each point between its neighbours, as in II 4; a
sequence and its reverse are the same), and `gt_iff_six_sequences` that `a > b` iff they stand in
one of the other six. The degenerate convention ("the coinciding points are to be regarded as a
single point, and … we have only to consider the order of three points") is read as: in each of the
twelve sequences in which the two coinciding points are adjacent, merge them into one point (a
sequence in which they are not adjacent cannot occur). For `A = O` this gives `0 < b` iff `OBE` or
`OEB`, and `0 > b` iff `BOE`; for `A = E`: `1 < b` iff `OEB`, `1 > b` iff `BOE` or `OBE`; the cases
`B = O`, `B = E` are the same with `A`, `B` exchanged; for `A = O`, `B = E` both points merge and
`0 < 1`. These are proved for the order of `DesAlg.Seg F`: `zero_lt_iff_three`, `lt_zero_iff_three`,
`one_lt_iff_three`, `lt_one_iff_three` (with `b ≠ 0, 1`) and `zero_lt_one_seg`. The reading of the
merging rule is ours.

**Status.** proved (reading)
-/

theorem lt_iff_six_sequences (F : Frame P) {a b : DesAlg.Seg F} (hab : a ≠ b) (ha0 : a ≠ 0)
    (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    a < b ↔ II4Arrangement a.pt b.pt F.O F.E ∨ II4Arrangement a.pt F.O b.pt F.E ∨
      II4Arrangement a.pt F.O F.E b.pt ∨ II4Arrangement F.O a.pt b.pt F.E ∨
      II4Arrangement F.O a.pt F.E b.pt ∨ II4Arrangement F.O F.E a.pt b.pt :=
  lt_iff_sequences hab ha0 ha1 hb0 hb1

theorem gt_iff_six_sequences (F : Frame P) {a b : DesAlg.Seg F} (hab : a ≠ b) (ha0 : a ≠ 0)
    (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    a > b ↔ II4Arrangement b.pt a.pt F.O F.E ∨ II4Arrangement b.pt F.O a.pt F.E ∨
      II4Arrangement b.pt F.O F.E a.pt ∨ II4Arrangement F.O b.pt a.pt F.E ∨
      II4Arrangement F.O b.pt F.E a.pt ∨ II4Arrangement F.O F.E b.pt a.pt :=
  lt_iff_sequences (Ne.symm hab) hb0 hb1 ha0 ha1

theorem seg_lt_iff (F : Frame P) (a b : DesAlg.Seg F) : a < b ↔ OrderLin.lineLt F.O F.E a.pt b.pt :=
  Iff.rfl

theorem zero_lt_iff_three (F : Frame P) {b : DesAlg.Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    0 < b ↔ Between F.O b.pt F.E ∨ Between F.O F.E b.pt :=
  zero_lt_iff_seq hb0 hb1

theorem lt_zero_iff_three (F : Frame P) {b : DesAlg.Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    b < 0 ↔ Between b.pt F.O F.E :=
  lt_zero_iff_seq hb0 hb1

theorem one_lt_iff_three (F : Frame P) {b : DesAlg.Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    1 < b ↔ Between F.O F.E b.pt :=
  one_lt_iff_seq hb0 hb1

theorem lt_one_iff_three (F : Frame P) {b : DesAlg.Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    b < 1 ↔ Between b.pt F.O F.E ∨ Between F.O b.pt F.E :=
  lt_one_iff_seq hb0 hb1

theorem zero_lt_one_seg (F : Frame P) : (0 : DesAlg.Seg F) < 1 :=
  Seg.zero_lt_one'

/-!
## [s28.order_laws] Laws 13–16 hold for the segments

*(§ 28)*

> Upon the basis of the axioms of group II, we can easily show also that, in our algebra of segments, the laws 13–16 of operation given in Section 13 are fulfilled.

**Lean reading.** `seg_laws_13_14`: laws 13, 14 and the (tacit) asymmetry of law 13 hold for
Hilbert's order from the axioms of order alone (it is the order of sequence of the line `OE`,
II 1–4), without Desargues's theorem. `seg_laws_13_16` adds laws 15 and 16, proved in the setting
of § 28, i.e. with the second part of Desargues's theorem (a standing hypothesis since § 25):
Hilbert's maps `x ↦ x + c` and `x ↦ a x` are composed of parallel projections, which preserve
betweenness (Pasch, II 5), hence are monotone or antitone; `x ↦ a x` is monotone for `a > 0`, and
the translations are monotone by an argument with the conjugates `a (a⁻¹ x + c) = x + a c`
(`Seg.add_strictMono`), which uses the field laws. Hilbert's "upon the basis of the axioms of group
II" suggests that laws 15–16 need no Desargues; a Desargues-free proof (by orientation arguments for
the parallel projections) is not given here, and whether laws 15–16 hold for Hilbert's operations in
every plane with I 1–2, II, III is left undecided.

**Status.** proved
-/

theorem seg_laws_13_14 (F : Frame P) :
    Law13 (DesAlg.Seg F) ∧ Law13Asymm (DesAlg.Seg F) ∧ Law14 (DesAlg.Seg F) :=
  seg_laws_13_14_nd F

theorem seg_laws_13_16 (hD : DesarguesII P) (F : Frame P) :
    Law13 (DesAlg.Seg F) ∧ Law13Asymm (DesAlg.Seg F) ∧ Law14 (DesAlg.Seg F) ∧ Law15 (DesAlg.Seg F) ∧ Law16 (DesAlg.Seg F) := by
  have : Fact (DesarguesII P) := ⟨hD⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, h16⟩ :=
    laws_of_divisionRing (D := DesAlg.Seg F)
  obtain ⟨h13, h13a, h14⟩ := seg_laws_13_14 F
  exact ⟨h13, h13a, h14, h15, h16⟩

/-!
## [s28.dns] Desarguesian number systems

*(§ 28)*

> Consequently, the totality of all the different segments forms a complex number system for which the laws 1–11, 13–16 of Section 13 hold; that is to say, all of the usual laws of operation except the commutative law of multiplication and the theorem of Archimedes. We will call such a system, briefly, a *desarguesian number system.*

**Lean reading.** `DesarguesianNumberSystem α` (defined in `DesarguesAlgebraAux6.lean`): a type with
`+`, `·`, `0`, `1`, `<` satisfying `Law1`–`Law11` and `Law13`–`Law16`. `seg_dns`: the segments of a
plane geometry with I 1–2, II, III and the second part of Desargues's theorem form one (and satisfy
the tacit asymmetry of law 13). Conversely, such a system with the asymmetry of law 13 and `0 ≠ 1` is
a linearly ordered division ring (`DesarguesianNumberSystem.toDivisionRing`, `toLinearOrder`,
`isStrictOrderedRing`), which is the form used in § 29.

**Status.** definition
-/

theorem desarguesianNumberSystem_def {α : Type*} [Add α] [Mul α] [Zero α] [One α] [LT α] :
    DesarguesianNumberSystem α ↔ Law1 α ∧ Law2 α ∧ Law3 α ∧ Law4 α ∧ Law5 α ∧ Law6 α ∧ Law7 α ∧
      Law8 α ∧ Law9 α ∧ Law10 α ∧ Law11 α ∧ Law13 α ∧ Law14 α ∧ Law15 α ∧ Law16 α :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩

theorem seg_dns (hD : DesarguesII P) (F : Frame P) :
    DesarguesianNumberSystem (DesAlg.Seg F) ∧ Law13Asymm (DesAlg.Seg F) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := seg_laws_1_11 hD F
  obtain ⟨h13, h13a, h14, h15, h16⟩ := seg_laws_13_16 hD F
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, h15, h16⟩, h13a⟩

end Plane

/-!
## [s29.space] A desarguesian number system gives a space geometry with I, II, III

*(§ 29)*

> Suppose we have given a desarguesian number system $D$. Such a system makes possible the construction of a geometry of space in which axioms I, II, III are all fulfilled.

**Lean reading.** `dns_space`: for a desarguesian number system `D` with the tacit asymmetry of law 13
and `0 ≠ 1`, made into a linearly ordered division ring with its own operations, the coordinate space
`Coord Dᵐᵒᵖ 3` (points: triples of elements of `D`; lines and planes: affine subspaces of dimensions
1 and 2; betweenness: `B = A + t (C - A)`, `0 < t < 1`) satisfies `SpaceOrder` and `SpaceParallels`
(groups I, II, III; Analytic.lean). The scalars are `Dᵐᵒᵖ`, i.e. `D` acting on the right, so that the
planes are the equations `u x + v y + w z + r = 0` with the coefficients on the *left*, as in
Hilbert's convention (unit `s29.model`). The two tacit hypotheses are not consequences of the laws
as formalized: with `0 = 1` every number is `0` (`dns_trivial_of_zero_eq_one`; the one-element
system satisfies all the laws, `punit_laws`), so the "space" would have a single point and could
not satisfy I 7; and the relation `<` true for all pairs satisfies the laws 13–17 but not the
asymmetry (`totalLT_laws`), and then Hilbert's "betweenness by double inequalities" would make each
of three distinct collinear points lie between the other two, against II 3. Hilbert's law 13 ("one
of them is greater, the other smaller") is read as including the asymmetry.

**Status.** proved
-/

theorem dns_trivial_of_zero_eq_one {D : Type*} [Add D] [Mul D] [Zero D] [One D] [LT D]
    (h : DesarguesianNumberSystem D) (h01 : (0 : D) = 1) (a : D) : a = 0 := by
  rw [← (h.law5 a).1, ← h01]
  exact DesarguesianNumberSystem.mul_zero' h.law3 h.law2 h.law10 a

theorem dns_space {D : Type u} [Add D] [Mul D] [Zero D] [One D] [LT D]
    (h : DesarguesianNumberSystem D) (ha : Law13Asymm D) (h01 : (0 : D) ≠ 1) :
    letI := h.toDivisionRing h01
    letI := h.toLinearOrder ha
    letI : LinearOrder Dᵐᵒᵖ := opLinearOrder D
    haveI := h.isStrictOrderedRing ha h01
    haveI := opIsStrictOrderedRing D
    SpaceOrder (Coord Dᵐᵒᵖ 3) (CoordLine Dᵐᵒᵖ 3) (CoordPlane Dᵐᵒᵖ 3) ∧
      SpaceParallels (Coord Dᵐᵒᵖ 3) (CoordLine Dᵐᵒᵖ 3) (CoordPlane Dᵐᵒᵖ 3) := by
  let := h.toDivisionRing h01
  let := h.toLinearOrder ha
  let : LinearOrder Dᵐᵒᵖ := opLinearOrder D
  have := h.isStrictOrderedRing ha h01
  have := opIsStrictOrderedRing D
  exact ⟨inferInstance, inferInstance⟩

/-!
## [s29.model] Points, planes and lines of the space of § 29

*(§ 29)*

> In order to show this, let us consider any system of three numbers $(x, y, z)$ of the desarguesian number system $D$ as a point, and the ratio of four such numbers $(u:v:w:r)$, of which the first three are not 0, as a plane. … The existence of the equation \[ ux + vy + wz + r = 0 \] expresses the condition that the point $(x, y, z)$ shall lie in the plane $(u:v:w:r)$. Finally, we define a straight line by the aid of a system of two planes … A point $(x, y, z)$ is said to be situated upon this straight line $[(u':v':w':r'), (u'':v'':w'':r'')]$, if it is common to the two planes $(u':v':w':r')$ and $(u'':v'':w'':r'')$. Two straight lines which contain the same points are not regarded as being distinct.

**Lean reading.** The model of `dns_space` takes its points as Hilbert does (`Coord Dᵐᵒᵖ 3`, triples)
and its planes and lines as affine subspaces of dimension 2 and 1 of the right `D`-module `D³`
(Analytic.lean), not as classes of equations. "Of which the first three are not 0" is read as "not
all three 0". The identification with Hilbert's description is proved in both directions, so the
model of `dns_space` *is* Hilbert's geometry: `hilbert_plane_equation` shows that the solution set
of `u x + v y + w z + r = 0` (left coefficients, `(u, v, w) ≠ 0`) is a plane of the model, and
`plane_is_equation` that every plane of the model is such a solution set; `equation_proportional`
that the proportional systems `(a u : a v : a w : a r)` (`a ≠ 0`) have the same solutions. For the
lines, `HilbertIndep u' v' w' u'' v'' w''` is Hilbert's condition ("impossible to find in `D` two
numbers `a'`, `a''` different from zero" with `a'u' = a''u''`, `a'v' = a''v''`, `a'w' = a''w''`);
`hilbert_line` shows that the common points of two such planes form a line of the model, and
`line_is_hilbert_line` that every line of the model is the set of common points of two planes
satisfying Hilbert's condition. "Two straight lines which contain the same points are not regarded
as being distinct" is built in: a line of the model is its set of points.

**Status.** definition
-/

theorem equation_proportional {D : Type*} [DivisionRing D] (u v w r a x y z : D) (ha : a ≠ 0) :
    a * u * x + a * v * y + a * w * z + a * r = 0 ↔ u * x + v * y + w * z + r = 0 := by
  constructor
  · intro h
    have : a * (u * x + v * y + w * z + r) = 0 := by
      rw [← h]; simp only [mul_add, mul_assoc]
    exact (mul_eq_zero.1 this).resolve_left ha
  · intro h
    rw [show a * u * x + a * v * y + a * w * z + a * r = a * (u * x + v * y + w * z + r) by
      simp only [mul_add, mul_assoc], h, mul_zero]

theorem hilbert_plane_equation {D : Type*} [DivisionRing D] (u v w r : D)
    (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    ∃ π : CoordPlane Dᵐᵒᵖ 3, ∀ X : Coord Dᵐᵒᵖ 3, X ∈ π ↔
      u * MulOpposite.unop (AffPt.toV X 0) + v * MulOpposite.unop (AffPt.toV X 1) +
        w * MulOpposite.unop (AffPt.toV X 2) + r = 0 :=
  equation_plane u v w r h

theorem plane_is_equation {D : Type*} [DivisionRing D] (π : CoordPlane Dᵐᵒᵖ 3) :
    ∃ u v w r : D, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧ ∀ X : Coord Dᵐᵒᵖ 3, X ∈ π ↔
      u * MulOpposite.unop (AffPt.toV X 0) + v * MulOpposite.unop (AffPt.toV X 1) +
        w * MulOpposite.unop (AffPt.toV X 2) + r = 0 :=
  plane_eq_equation π

theorem hilbert_line {D : Type*} [DivisionRing D] {u' v' w' r' u'' v'' w'' r'' : D}
    (h1 : u' ≠ 0 ∨ v' ≠ 0 ∨ w' ≠ 0) (h2 : u'' ≠ 0 ∨ v'' ≠ 0 ∨ w'' ≠ 0)
    (hind : HilbertIndep u' v' w' u'' v'' w'') :
    ∃ ℓ : CoordLine Dᵐᵒᵖ 3, ∀ X : Coord Dᵐᵒᵖ 3,
      X ∈ ℓ ↔ lin3 u' v' w' X + r' = 0 ∧ lin3 u'' v'' w'' X + r'' = 0 :=
  hilbert_line_of_planes h1 h2 hind

theorem line_is_hilbert_line {D : Type*} [DivisionRing D] (ℓ : CoordLine Dᵐᵒᵖ 3) :
    ∃ u' v' w' r' u'' v'' w'' r'' : D, (u' ≠ 0 ∨ v' ≠ 0 ∨ w' ≠ 0) ∧
      (u'' ≠ 0 ∨ v'' ≠ 0 ∨ w'' ≠ 0) ∧ HilbertIndep u' v' w' u'' v'' w'' ∧
      ∀ X : Coord Dᵐᵒᵖ 3, X ∈ ℓ ↔ lin3 u' v' w' X + r' = 0 ∧ lin3 u'' v'' w'' X + r'' = 0 :=
  line_eq_hilbert_line ℓ

/-!
## [s29.axioms_I_III] Groups I and III in the space of § 29

*(§ 29)*

> By application of the laws 1–11 of § 13, which by hypothesis hold for the numbers of $D$, we obtain without difficulty the result that the geometry of space which we have just constructed satisfies all of the axioms of groups I and III.

**Lean reading.** `dns_space_I_III`: the model satisfies `SpaceConnection` and `SpaceParallels`
(groups I, III). Laws 1–11 make `D` a division ring (`toDivisionRing`, with `0 ≠ 1`), and linear algebra
over a division ring (dimensions of affine subspaces) gives the axioms; no order is used.

**Status.** proved
-/

theorem dns_space_I_III {D : Type u} [Add D] [Mul D] [Zero D] [One D] [LT D]
    (h : DesarguesianNumberSystem D) (h01 : (0 : D) ≠ 1) :
    letI := h.toDivisionRing h01
    SpaceConnection (Coord Dᵐᵒᵖ 3) (CoordLine Dᵐᵒᵖ 3) (CoordPlane Dᵐᵒᵖ 3) ∧
      SpaceParallels (Coord Dᵐᵒᵖ 3) (CoordLine Dᵐᵒᵖ 3) (CoordPlane Dᵐᵒᵖ 3) := by
  let := h.toDivisionRing h01
  exact ⟨inferInstance, inferInstance⟩

/-!
## [s29.between] Betweenness by co-ordinates

*(§ 29)*

> In order that the axioms (II) of order may also be valid, we adopt the following conventions. Let \[ (x_1, y_1, z_1), (x_2, y_2, z_2), (x_3, y_3, z_3) \] be any three points of a straight line \[ [(u':v':w':r'), (u'':v'':w'':r'')]. \] Then, the point $(x_2, y_2, z_2)$ is said to lie between the other two, if we have fulfilled at least one of the six following double inequalities: …

**Lean reading.** The model's betweenness is `Sbtw`: `B = t (C - A) + A` with `0 < t < 1`.
`between_iff_double_inequality` proves it is Hilbert's convention: for `A ≠ C` and a point `B` of the
line `AC`, `B` lies between `A` and `C` iff some co-ordinate satisfies `A_i < B_i < C_i` or
`A_i > B_i > C_i`, in any linearly ordered division ring (applied to `Dᵐᵒᵖ`, whose order is that of `D`).

**Status.** proved
-/

theorem between_iff_double_inequality {K : Type*} [DivisionRing K] [LinearOrder K]
    [IsStrictOrderedRing K] {A C : Coord K 3} (hAC : A ≠ C) (t : K) :
    Between A (t • (C - A) + A) C ↔ ∃ i : Fin 3,
      (AffPt.toV A i < AffPt.toV (t • (C - A) + A) i ∧
          AffPt.toV (t • (C - A) + A) i < AffPt.toV C i) ∨
        (AffPt.toV C i < AffPt.toV (t • (C - A) + A) i ∧
          AffPt.toV (t • (C - A) + A) i < AffPt.toV A i) :=
  sbtw_iff_coord hAC t

/-!
## [s29.coordinate_order] The co-ordinates along a line

*(§ 29)*

> If one of the two double inequalities (1) exists, then we can easily conclude that either $y_1 = y_2 = y_3$ or one of the two double inequalities (2) exists, and, consequently, either $z_1 = z_2 = z_3$ or one of the double inequalities (3) must exist. … In each of these double inequalities, we must take either the upper sign throughout, or the middle sign throughout, or the lower sign throughout.

**Lean reading.** `coordinates_along_line`: if `B` lies between `A` and `C` on a line (in particular if
one double inequality holds), every co-ordinate `j` satisfies `A_j < B_j < C_j`, `A_j = B_j = C_j` or
`A_j > B_j > C_j` (each double inequality homogeneous). Hilbert's argument eliminates one co-ordinate
by a left-sided combination of the two plane equations; here `B_j - A_j = t (C_j - A_j)` with
`0 < t < 1`. (The printed "`u'''x_1 ⋚ x'''u_2 ⋚ x'''u_3`" is a misprint for
`u'''x_1 ⋚ u'''x_2 ⋚ u'''x_3`.)

**Status.** proved
-/

theorem coordinates_along_line {K : Type*} [DivisionRing K] [LinearOrder K]
    [IsStrictOrderedRing K] {A C : Coord K 3} (hAC : A ≠ C) {t : K}
    (h : Between A (t • (C - A) + A) C) (j : Fin 3) :
    (AffPt.toV A j < AffPt.toV (t • (C - A) + A) j ∧
        AffPt.toV (t • (C - A) + A) j < AffPt.toV C j) ∨
      (AffPt.toV A j = AffPt.toV (t • (C - A) + A) j ∧
        AffPt.toV (t • (C - A) + A) j = AffPt.toV C j) ∨
      (AffPt.toV C j < AffPt.toV (t • (C - A) + A) j ∧
        AffPt.toV (t • (C - A) + A) j < AffPt.toV A j) :=
  coord_monotone hAC h j

/-- Hilbert's form: three points of a line with `x₁ < x₂ < x₃` (or `>`) have, in every
co-ordinate, all equal values or a double inequality with one sign throughout. -/
theorem coordinates_along_line_of_ineq {K : Type*} [DivisionRing K] [LinearOrder K]
    [IsStrictOrderedRing K] {A C : Coord K 3} (hAC : A ≠ C) {t : K} (i : Fin 3)
    (h : (AffPt.toV A i < AffPt.toV (t • (C - A) + A) i ∧
          AffPt.toV (t • (C - A) + A) i < AffPt.toV C i) ∨
        (AffPt.toV C i < AffPt.toV (t • (C - A) + A) i ∧
          AffPt.toV (t • (C - A) + A) i < AffPt.toV A i)) (j : Fin 3) :
    (AffPt.toV A j < AffPt.toV (t • (C - A) + A) j ∧
        AffPt.toV (t • (C - A) + A) j < AffPt.toV C j) ∨
      (AffPt.toV A j = AffPt.toV (t • (C - A) + A) j ∧
        AffPt.toV (t • (C - A) + A) j = AffPt.toV C j) ∨
      (AffPt.toV C j < AffPt.toV (t • (C - A) + A) j ∧
        AffPt.toV (t • (C - A) + A) j < AffPt.toV A j) :=
  coordinates_along_line hAC ((between_iff_double_inequality hAC t).2 ⟨i, h⟩) j

/-!
## [s29.axioms_II] Group II in the space of § 29

*(§ 29)*

> The preceding considerations show, that, in our geometry, the linear axioms II, 1–4 of order are all valid. However, it remains yet to show that, in this geometry, the plane axiom II, 5 is also valid. For this purpose let a plane $(u:v:w:r)$ and a straight line $[(u:v:w:r), (u':v':w':r')]$ in this plane be given. Let us assume that all the points $(x, y, z)$ of the plane $(u:v:w:r)$, for which we have the expression $u'x + v'y + w'z + r'$ greater than or less than zero, lie respectively upon the one side or upon the other side of the given straight line. We have then only to show that this convention is in accordance with the preceding statements. This, however, is easily done.

**Lean reading.** `dns_space_II`: the model satisfies `SpaceOrder` (II 1–4 on lines, II 5 in every
plane), from `dns_space`. In Analytic.lean II 5 is proved exactly by Hilbert's convention: the two
sides of a line in a plane are the signs of a linear form vanishing on the line (`exists_side_functional`,
`sameSide_iff_mul_pos`).

**Status.** proved
-/

theorem dns_space_II {D : Type u} [Add D] [Mul D] [Zero D] [One D] [LT D]
    (h : DesarguesianNumberSystem D) (ha : Law13Asymm D) (h01 : (0 : D) ≠ 1) :
    letI := h.toDivisionRing h01
    letI := h.toLinearOrder ha
    letI : LinearOrder Dᵐᵒᵖ := opLinearOrder D
    haveI := h.isStrictOrderedRing ha h01
    haveI := opIsStrictOrderedRing D
    SpaceOrder (Coord Dᵐᵒᵖ 3) (CoordLine Dᵐᵒᵖ 3) (CoordPlane Dᵐᵒᵖ 3) :=
  (dns_space h ha h01).1

/-!
## [s29.converse] § 29 is the converse of § 28

*(§ 29)*

> We have thus shown that all of the axioms of groups I, II, III are fulfilled in the geometry of space which we have obtained in the above indicated manner from the desarguesian number system *D*. Remembering now that the theorem of Desargues is a consequence of the axioms I, II, III, we see that the proposition just stated is exactly the converse of the result reached in Section 28.

**Lean reading.** The result of § 28 is `seg_dns` (desarguesian plane ⇒ desarguesian number system),
that of § 29 `dns_space` (desarguesian number system ⇒ space geometry with I, II, III), and "the
theorem of Desargues is a consequence of the axioms I, II, III" is `planes_of_space_desarguesian`
(unit `s30.any_dimension`), proved here from I and III. The two directions are combined in
Theorem 35.

**Status.** remark
-/

/-!
## [s30.algebra] The algebra of segments of a desarguesian plane

*(§ 30)*

> If, in a plane geometry, axioms I, 1–2, II, III are all fulfilled and, moreover, if the theorem of Desargues holds, then, according to \S§ 24–28, it is always possible to introduce into this geometry an algebra of segments to which the laws 1–11, 13–16 of § 13 are applicable. We will now consider the totality of these segments as a complex number system and construct, upon the basis of this system, a geometry of space, in accordance with § 29, in which all of the axioms I, II, III hold.

**Lean reading.** `algebra_of_desarguesian`: a plane geometry with I 1–2, II, III, a line, and the
second part of Desargues's theorem has a frame `F`, and `DesAlg.Seg F` is a desarguesian number system
(`seg_dns`); the space of § 29 over it is the space of Theorem 35 (`planeInSpace`, `space_instances`).

**Status.** proved
-/

theorem algebra_of_desarguesian {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P) :
    ∃ F : Frame P, DesarguesianNumberSystem (DesAlg.Seg F) ∧ Law13Asymm (DesAlg.Seg F) := by
  obtain ⟨F⟩ := exists_frame (P := P) (L := L)
  exact ⟨F, seg_dns hD F⟩

/-!
## [s30.plane_coincides] The plane `z = 0` is the given plane geometry

*(§ 30)*

> In this geometry of space, we shall consider only the points $(x, y, 0)$ and those straight lines upon which only such points lie. We have then a plane geometry which must, if we take into account the proposition established in § 27, coincide exactly with the plane geometry proposed at the beginning.

**Lean reading.** `plane_coincides`: for a frame `F` of a plane geometry with I 1–2, II, III and the
second part of Desargues's theorem, `planeInSpace F : PlaneInSpace P L S SL SPl` identifies the given
plane geometry with the plane `z = 0` of the coordinate space `S = AffPt K (Vec F × K)` over
`K = (DesAlg.Seg F)ᵐᵒᵖ` (the vectors of the plane with origin `O` and a third co-ordinate): points
correspond one-to-one to the points `(x, y, 0)`, lines to the lines lying in that plane, and
incidence and betweenness correspond ("coincide exactly"). Incidence is § 27 (lines are the affine
lines); betweenness is `between_iff_param` (§ 28's order). `PlaneInSpace` (Aux5) bundles the two
bijections and the four properties.

**Status.** proved
-/

theorem plane_coincides {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P) (F : Frame P) :
    haveI : Fact (DesarguesII P) := ⟨hD⟩
    Nonempty (PlaneInSpace P L (AffPt (DesAlg.Seg F)ᵐᵒᵖ (Vec F × (DesAlg.Seg F)ᵐᵒᵖ))
      (AffLine (DesAlg.Seg F)ᵐᵒᵖ (Vec F × (DesAlg.Seg F)ᵐᵒᵖ)) (AffPlane (DesAlg.Seg F)ᵐᵒᵖ (Vec F × (DesAlg.Seg F)ᵐᵒᵖ))) :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  ⟨planeInSpace F⟩

/-!
## [s30.first_part] The first part of Desargues's theorem follows from the second

*(§ 30)*

> If, in a plane geometry, axioms I, 1–2, II, III are all fulfilled and, moreover, if the theorem of Desargues holds, then, according to \S§ 24–28, it is always possible to introduce into this geometry an algebra of segments …

**Lean reading.** Not a claim of Hilbert's but needed to state the results with the weakest
hypothesis: `first_part_of_second` — in a plane geometry with I 1–2, III, the second part of
Desargues's theorem implies the first (`desarguesI_of_II`: if `AA'`, `BB'` meet in `O`, the point
`C''` of `A'C'` on `OC` satisfies `BC ∥ B'C''` by the second part, hence `C'' = C'`; similarly with
parallel joins). So `DesarguesTheorem P ↔ DesarguesII P`.

**Status.** proved
-/

theorem first_part_of_second {P : Type u} {L : Type v} [HasLines P L] [PlaneParallels P L]
    [Nonempty L] : DesarguesTheorem P ↔ DesarguesII P :=
  ⟨fun h => h.2, fun h => ⟨desarguesI_of_II h, h⟩⟩

/-!
## [th.35] Theorem 35

*(§ 30)*

> If, in a plane geometry, axioms I, 1–2, II, III are all fulfilled, then the existence of Desargues's theorem is the necessary and sufficient condition that this plane geometry may be regarded as a part of a geometry of space in which all of the axioms I, II, III are fulfilled.

**Lean reading.** `theorem35`: for a plane geometry `(P, L)` with `[PlaneOrder P L]`,
`[PlaneParallels P L]` (I 1–2, II, III) and at least one line, `DesarguesTheorem P` holds iff there
are a space geometry `(P', L', Pl')` (in the universe of `P`) satisfying `SpaceOrder` and
`SpaceParallels` (I, II, III) and a `PlaneInSpace P L P' L' Pl'`: bijections of the points with the
points of a plane `α` and of the lines with the lines lying in `α`, preserving and reflecting
incidence and betweenness ("regarded as a part of"). Sufficiency (Desargues ⇒ part of a space) is
the chain of §§ 24–30 (`plane_coincides`); necessity uses the spatial proof of Desargues's theorem
(`space_desargues`; Hilbert only says "it is well known that … may be easily demonstrated"), and only
I and III of the space. The hypothesis `[Nonempty L]` (a line exists) is not a correction of
Hilbert but of the encoding: Hilbert's I 7 gives three distinct points not on one line, hence (I 1)
a line, while `ExistsNoncollinear` of Basic.lean is satisfied vacuously by one point and no line;
that structure satisfies the plane classes and Desargues's theorem but is part of no space geometry
(`s30.degenerate`), so without `[Nonempty L]` the Lean statement would be false. In addition the
second part of Desargues's theorem alone is equivalent (`theorem35_second_part`).

**Status.** proved (reading)
-/

theorem theorem35 {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
    [PlaneParallels P L] [Nonempty L] :
    DesarguesTheorem P ↔ ∃ (P' L' Pl' : Type u) (_ : HasLines P' L') (_ : HasPlanes P' Pl')
      (_ : HasBetween P'), SpaceOrder P' L' Pl' ∧ SpaceParallels P' L' Pl' ∧
        Nonempty (PlaneInSpace P L P' L' Pl') := by
  constructor
  · intro hD
    obtain ⟨F⟩ := exists_frame (P := P) (L := L)
    have : Fact (DesarguesII P) := ⟨hD.2⟩
    exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, (space_instances F).1,
      (space_instances F).2, ⟨planeInSpace F⟩⟩
  · rintro ⟨P', L', Pl', _, _, _, -, hPar, ⟨e⟩⟩
    exact desarguesTheorem_of_planeInSpace e

theorem theorem35_second_part {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] :
    DesarguesII P ↔ ∃ (P' L' Pl' : Type u) (_ : HasLines P' L') (_ : HasPlanes P' Pl')
      (_ : HasBetween P'), SpaceOrder P' L' Pl' ∧ SpaceParallels P' L' Pl' ∧
        Nonempty (PlaneInSpace P L P' L' Pl') :=
  first_part_of_second.symm.trans theorem35

/-!
## [s30.degenerate] Theorem 35 needs a line

*(§ 30)*

> If, in a plane geometry, axioms I, 1–2, II, III are all fulfilled, then the existence of Desargues's theorem is the necessary and sufficient condition …

**Lean reading.** A finding about the encoding of plane geometry (Basic.lean), not an error of
Hilbert's (his three points "not lying in the same straight line" are distinct, which excludes this
structure): the structure with one
point and no line (`DegPt`, `DegLn`) satisfies `PlaneOrder` and `PlaneParallels` (I 1–2 and the plane
clauses of I 7 hold vacuously: three "non-collinear" points exist because there is no line at all),
and Desargues's theorem vacuously; but it is part of no space geometry satisfying I: the plane `α`
would contain only one point, the plane clause of I 7 would forbid a line through it, so I 1 would
leave no other point, and the four points of the space clause would lie in `α`
(`degenerate_counterexample`). Hence the hypothesis `[Nonempty L]` of `theorem35`.

**Status.** proved
-/

theorem degenerate_counterexample :
    PlaneOrder DegPt DegLn ∧ PlaneParallels DegPt DegLn ∧ DesarguesTheorem DegPt ∧
      ∀ (P' L' Pl' : Type) [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P'],
        SpaceConnection P' L' Pl' → IsEmpty (PlaneInSpace DegPt DegLn P' L' Pl') :=
  ⟨deg_planeOrder, deg_planeParallels, deg_desargues,
    fun _ _ _ _ _ _ _ => ⟨fun e => deg_not_planeInSpace e⟩⟩

/-!
## [s30.elimination] Desargues's theorem as the elimination of the space axioms

*(§ 30)*

> The theorem of Desargues may be characterized for plane geometry as being, so to speak, the result of the elimination of the space axioms.

**Lean reading.** A comment on Theorem 35: among plane geometries with I 1–2, II, III, those that
are planes of a space geometry with I, II, III are exactly those satisfying Desargues's theorem.

**Status.** remark
-/

/-!
## [s30.any_dimension] Every space geometry is part of a geometry of any number of dimensions

*(§ 30)*

> The results obtained so far put us now in the position to show that every geometry of space in which axioms I, II, III are all fulfilled may be always regarded as a part of a “geometry of any number of dimensions whatever.” By a geometry of an arbitrary number of dimensions is to be understood the totality of all points, straight lines, planes, and other linear elements, for which the corresponding axioms of connection and of order, as well as the axiom of parallels, are all valid.

**Lean reading.** "A geometry of any number of dimensions" is not axiomatized in the book; it is
read as the coordinate geometry `AffPt K (Fin n → K)` over a linearly ordered division ring `K`
(`n ≥ 3`). `AnyDimensionClaim` states: every space geometry with I, II, III and at least one plane
embeds, for every `n ≥ 3`, into such a geometry, injectively on points, with betweenness preserved
and reflected and every line and plane mapped onto the points of an affine subspace of dimension 1,
resp. 2, that it meets. The proof would coordinatize the space (each plane is desarguesian; the
segments of one plane coordinatize the whole space through a point off the plane), which is not done
here. Proved partial results: (1) the first step and the claim "the theorem of Desargues is a
consequence of the axioms I, II, III" of § 29: `planes_of_space_desarguesian` — every plane of a
space geometry satisfying I and III, with its points and its lines, satisfies Desargues's theorem;
(2) the last step: `coordinate_space_any_dimension` — the coordinate space `K³` over any ordered skew
field (in particular the space of § 29 over a desarguesian number system) is a part of `Kⁿ` for every
`n ≥ 3` in the sense of `AnyDimensionClaim`. The missing middle step is the coordinatization of an
arbitrary space geometry with I, II, III by the segments of one of its planes.

**Status.** stated (open here)
-/

/-- **Hilbert's claim** (§ 30): every space geometry with I, II, III is part of a coordinate
geometry of any dimension `n ≥ 3` over an ordered skew field. Not proved here. -/
def AnyDimensionClaim : Prop :=
  ∀ (P L Pl : Type) [HasLines P L] [HasPlanes P Pl] [HasBetween P],
    SpaceOrder P L Pl → SpaceParallels P L Pl → Nonempty Pl →
    ∀ n : ℕ, 3 ≤ n → ∃ (K : Type) (_ : DivisionRing K) (_ : LinearOrder K)
      (_ : IsStrictOrderedRing K) (f : P → AffPt K (Fin n → K)), Function.Injective f ∧
      (∀ A B C : P, Between A B C ↔ Sbtw K (f A) (f B) (f C)) ∧
      (∀ l : L, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        Module.finrank K S.direction = 1 ∧ ∀ X : P, X ∈ l ↔ f X ∈ S) ∧
      (∀ π : Pl, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        Module.finrank K S.direction = 2 ∧ ∀ X : P, X ∈ π ↔ f X ∈ S)

/-- **Every plane of a space geometry with I, III is desarguesian** (with its points and the lines
lying in it). -/
theorem planes_of_space_desarguesian {P : Type u} {L : Type v} {Pl : Type*} [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [SpaceParallels P L Pl] (α : Pl) :
    DesarguesTheorem {A : P // A ∈ α} := by
  have := nonempty_lines_of_plane (P := P) (L := L) α
  exact desarguesTheorem_of_planeInSpace (restrictPlaneInSpace α)

/-- **Coordinate spaces are parts of coordinate geometries of any dimension `n ≥ 3`.** -/
theorem coordinate_space_any_dimension {K : Type*} [DivisionRing K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (hn : 3 ≤ n) :
    ∃ f : Coord K 3 → AffPt K (Fin n → K), Function.Injective f ∧
      (∀ A B C : Coord K 3, Between A B C ↔ Sbtw K (f A) (f B) (f C)) ∧
      (∀ l : CoordLine K 3, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        Module.finrank K S.direction = 1 ∧ ∀ X : Coord K 3, X ∈ l ↔ f X ∈ S) ∧
      (∀ π : CoordPlane K 3, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        Module.finrank K S.direction = 2 ∧ ∀ X : Coord K 3, X ∈ π ↔ f X ∈ S) :=
  coord3_any_dimension hn

end HilbertFoundations
