import HilbertFoundations.Order
import HilbertFoundations.CongruenceAux9

/-!
# Consequences of the axioms of congruence (Theorems 9–20)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 6. Group IV: Axioms of congruence
* § 7. Consequences of the axioms of congruence

## Organisation

The proofs are in the helper modules (which contain no units):

* `CongruenceAux.lean`: half-rays, sides and interiors from the linear axioms, and **plane frames**
  (`Frame P L`): a family of "planes" with the facts used inside one plane (Pasch, transitivity of
  "same side", the laying off of angles IV 4). Hilbert's theorems of § 7 compare figures lying in
  two (possibly different) planes `α`, `α'`; every proof works inside these planes, so each theorem
  is proved once for an arbitrary frame and specialised to plane geometry (`planeFrame`: the only
  plane is the set of all points; groups I, II, IV of plane geometry) and to space geometry
  (`spaceFrame`: the planes of space; groups I, II, IV of space geometry).
* `CongruenceAux2.lean`: segments (IV 1–3) and the plane-free axioms of angles.
* `CongruenceAux3.lean`: Theorems 10–16 in a frame.
* `CongruenceAux4.lean`: points equidistant from given points; the counterexample to Theorem 14 as
  printed.
* `CongruenceAux5.lean`: Theorems 19–20 and the comparison of angles.
* `CongruenceAux6.lean`: the two regions of an angle (§ 6) and the reading of Axiom IV 3.
* `CongruenceAux7.lean`: congruent figures: preservation of sides, and the construction of
  Theorem 17.
* `CongruenceAux8.lean`: right angles, isosceles apexes, perpendicular bisectors and the circle
  through three points.
* `CongruenceAux9.lean`: a point with the distances of a point of a plane from three
  non-collinear points of the plane lies in the plane (used for coplanarity and Theorem 18).

**Degenerate plane geometry.** Group I of plane geometry is satisfied by a single point without any
line; there `¬Collinear A A A` holds and every congruence statement about that point is junk. The
plane statements below handle this case separately (`plane_cases`); it is the only reason for the
case distinctions in their proofs.

## API for other files

* definitions: `CongruentSeries`, `AreSupplementary`, `AreVertical`, `IsRightAngle`, `TriCong`,
  `AngLt`, `IsAcute`, `IsObtuse`, `AnglesSumTwoRight`, `Theorem14AsPrinted`,
  `Theorem14AsPrintedSpace`, `IsFigure`, `IsPlaneFigure`, `CongruentFigures`,
  `Theorem18AsPrinted` (false), `Theorem18Statement`, `SpaceCongruenceGivesTheorem18` (open),
  `Circle`, `CircleIn`,
  `CircleThroughThree`, `InscribedAnglesCongruent`, `InscribedQuadrilateral`,
  `CirclePropertiesClaim` (open);
* § 6: `IV3_reading`, `IV3_reading_open`, `angle_regions`, `angle_regions_space`,
  `interior_wellDefined`, `interior_wellDefined_space`, `exterior_wellDefined`,
  `triangle_angle_contains_interior`, `triangle_angle_contains_interior_space`;
* § 7: `segCong_symmetric`, `theorem9`, `angCong_symmetric`, `areSupplementary_of_between`,
  `areVertical_of_between`, `theorem10`, `theorem10_space`, `theorem11`, `theorem11_space`,
  `theorem12`, `theorem12_space`, `vertical_angles`, `vertical_angles_space`, `theorem13`,
  `theorem13_space`, `theorem14`, `theorem14_space`, `theorem14_as_printed_false`,
  `theorem14_as_printed_false_space`, `theorem15`, `theorem15_space`, `isAcute_wellDefined`,
  `isObtuse_wellDefined` (and `_space`), `isosceles_base_angles`, `theorem16`, `theorem16_space`,
  `theorem19_alternate`, `theorem19_corresponding` (and `_space`), `theorem19_converse_alternate`,
  `theorem19_converse_corresponding` (and `_space`), `theorem20`, `theorem20_space`,
  `Frame.isRightAngle_other`, `congruentFigures_symm`, `congruentFigures_collinear`,
  `congruentFigures_between`, `congruentFigures_sameSide` (and `_gen`, `_space`),
  `congruentFigures_oppositeSides` (and `_space`), `congruentFigures_coplanar_space`,
  `congruentFigures_snoc`, `theorem17`, `theorem17_unique`, `theorem17_space`,
  `theorem17_unique_space`, `theorem18_as_printed_false`, `theorem18_planar`,
  `theorem18_unique_of_coplanar`, `circle_segCong`, `mem_circle_of_segCong`,
  `circleThroughThree`, `circleThroughThree_space`;
* from the helper modules, usable in any frame: `Frame.sas`, `Frame.asa`, `Frame.supp`,
  `Frame.vertical`, `Frame.interior_transfer`, `Frame.angle_addition`, `Frame.right_angles`,
  `Frame.sss`, `Frame.crossbar`, `Frame.eq_of_equidistant`, `Frame.collinear_of_segCong`,
  `midpoint_unique`, `segCong_symm`, `segCong_trans`, `segCong_add`, `segCong_sub`,
  `segCong_layoff`, `eq_of_segCong_ray`, `between_of_segCong`, `angCong_symm`, `angCong_trans`,
  `angCong_rays`, `base_angles`, `Frame.theorem17_exists`, `Frame.sameSide_of_segCong`,
  `Frame.circumcenter`, `Frame.apex`, `Frame.equidistant_of_mem`, `RightAng`, `Frame.rt_cong`,
  `Frame.memS_of_equidistant`, `injective_fin3`.
-/

namespace HilbertFoundations

universe u v w

variable {P : Type u} {L : Type v} {Pl : Type w}

/-!
## [s6.IV3_reading] Segments with no common point but `B`

*(§ 6)*

> Let $AB$ and $BC$ be two segments of a straight line $a$ which have no points in common aside from the point $B$

**Lean reading.** Basic.lean formalizes the hypothesis of Axiom IV 3 as `SegmentsMeetOnlyAt A B C`
(collinear, `A ≠ B`, `B ≠ C`, and the closed segments `AB`, `BC` have only `B` in common) and states
that this reading is equivalent to `Between A B C` and to the reading with the points *within* the
segments. Both equivalences are proved here from the linear axioms II 1–4 (`LineOrder`):
`IV3_reading` (closed segments) and `IV3_reading_open` (Hilbert's "points of a segment", those
between the extremities). So IV 3 says: if `B` lies between `A` and `C` and `B'` between `A'` and
`C'`, then `AB ≡ A'B'` and `BC ≡ B'C'` give `AC ≡ A'C'` (`segCong_add`).

**Status.** proved
-/

theorem IV3_reading [HasLines P L] [HasBetween P] [LineOrder P L] {A B C : P} :
    SegmentsMeetOnlyAt (Line := L) A B C ↔ Between A B C :=
  segmentsMeetOnlyAt_iff_between

theorem IV3_reading_open [HasLines P L] [HasBetween P] [LineOrder P L] {A B C : P} :
    (Collinear (Line := L) A B C ∧ A ≠ B ∧ B ≠ C ∧ ∀ X, X ∈ Seg A B → X ∉ Seg B C) ↔
      Between A B C :=
  segments_disjoint_iff_between

/-!
## [s6.angle_regions] The two regions of an angle

*(§ 6)*

> From axioms II, 1–5, it follows readily that the half-rays $h$ and $k$, taken together with the point $O$, divide the remaining points of the plane a into two regions having the following property: If $A$ is a point of one region and $B$ a point of the other, then every broken line joining $A$ and $B$ either passes through $O$ or has a point in common with one of the half-rays $h$, $k$. If, however, $A$, $A'$ both lie within the same region, then it is always possible to join these two points by a broken line which neither passes through $O$ nor has a point in common with either of the half-rays $h$, $k$. One of these two regions is distinguished from the other in that the segment joining any two points of this region lies entirely within the region.

**Lean reading.** Plane geometry with groups I and II only (`PlaneOrder`), as Hilbert says. The angle
is `∠AOB` with `h = ray O A`, `k = ray O B` (`A ≠ O`, `B ≠ O`: half-rays, and `¬Collinear A O B`:
"two different straight lines"). `AngleBoundary A O B` is `{O} ∪ h ∪ k`; the two regions are the
interior `Interior A O B` and the exterior `Exterior A O B` of Basic.lean. `angle_regions` proves:
both are non-empty, disjoint, and together they are the remaining points (`Tᶜ`); every broken line
from a point of one region to a point of the other (either order) has a point in common with
`{O} ∪ h ∪ k`; any two points of the same region are joined by a broken line (`IsBrokenLine`)
without such a point; the interior is convex and the exterior is not (so the interior is "the
region so characterised"). The proof: an exit lemma (`angle_exit`: the segment from an interior to
a non-interior point meets `{O} ∪ h ∪ k`), the interior is convex, and the exterior is the union of
two convex open half-planes with a common point (`exterior_eq`). "The plane a" is a misprint for
"the plane `α`". Space version (`angle_regions_space`): the same statement in the plane geometry of
any plane `α` of space (the restriction of Order.lean). Hilbert's "two regions" are named here;
that no other pair of regions has these properties is not claimed by Hilbert and not proved.

**Status.** proved
-/

/-- **§ 6: the two regions of an angle** (plane geometry, groups I, II). -/
theorem angle_regions [HasLines P L] [HasBetween P] [PlaneOrder P L] {A O B : P} (hAO : A ≠ O)
    (hBO : B ≠ O) (h : ¬Collinear A O B) :
    let I := Interior (Line := L) A O B
    let E := Exterior (Line := L) A O B
    let T := AngleBoundary A O B
    I.Nonempty ∧ E.Nonempty ∧ Disjoint I E ∧ I ∪ E = Tᶜ ∧
    (∀ X ∈ I, ∀ Y ∈ E, ∀ (n : ℕ) (w : Fin (n + 1) → P), w 0 = X → w (Fin.last n) = Y →
      (BrokenLinePoints w ∩ T).Nonempty) ∧
    (∀ X ∈ E, ∀ Y ∈ I, ∀ (n : ℕ) (w : Fin (n + 1) → P), w 0 = X → w (Fin.last n) = Y →
      (BrokenLinePoints w ∩ T).Nonempty) ∧
    (∀ X ∈ I, ∀ X' ∈ I, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = X ∧
      w (Fin.last n) = X' ∧ Disjoint (BrokenLinePoints w) T) ∧
    (∀ X ∈ E, ∀ X' ∈ E, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = X ∧
      w (Fin.last n) = X' ∧ Disjoint (BrokenLinePoints w) T) ∧
    (∀ X Y Z, X ∈ I → Y ∈ I → Between X Z Y → Z ∈ I) ∧
    ¬(∀ X Y Z, X ∈ E → Y ∈ E → Between X Z Y → Z ∈ E) :=
  angle_regions_aux hAO hBO h

/-- **§ 6: the two regions of an angle** in a plane `α` of space (groups I, II of space), in the
plane geometry of `α`. -/
theorem angle_regions_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [SpaceOrder P L Pl]
    (α : Pl) {A O B : {X : P // X ∈ α}} (hAO : A ≠ O) (hBO : B ≠ O) (h : ¬Collinear A O B) :
    let I := Interior (Line := {a : L // LiesInPlane (Point := P) a α}) A O B
    let E := Exterior (Line := {a : L // LiesInPlane (Point := P) a α}) A O B
    let T := AngleBoundary A O B
    I.Nonempty ∧ E.Nonempty ∧ Disjoint I E ∧ I ∪ E = Tᶜ ∧
    (∀ X ∈ I, ∀ Y ∈ E, ∀ (n : ℕ) (w : Fin (n + 1) → {X : P // X ∈ α}), w 0 = X →
      w (Fin.last n) = Y → (BrokenLinePoints w ∩ T).Nonempty) ∧
    (∀ X ∈ E, ∀ Y ∈ I, ∀ (n : ℕ) (w : Fin (n + 1) → {X : P // X ∈ α}), w 0 = X →
      w (Fin.last n) = Y → (BrokenLinePoints w ∩ T).Nonempty) ∧
    (∀ X ∈ I, ∀ X' ∈ I, ∃ (n : ℕ) (w : Fin (n + 1) → {X : P // X ∈ α}), IsBrokenLine w ∧
      w 0 = X ∧ w (Fin.last n) = X' ∧ Disjoint (BrokenLinePoints w) T) ∧
    (∀ X ∈ E, ∀ X' ∈ E, ∃ (n : ℕ) (w : Fin (n + 1) → {X : P // X ∈ α}), IsBrokenLine w ∧
      w 0 = X ∧ w (Fin.last n) = X' ∧ Disjoint (BrokenLinePoints w) T) ∧
    (∀ X Y Z, X ∈ I → Y ∈ I → Between X Z Y → Z ∈ I) ∧
    ¬(∀ X Y Z, X ∈ E → Y ∈ E → Between X Z Y → Z ∈ E) :=
  angle_regions_aux hAO hBO h

/-!
## [s6.interior_well_defined] The interior of the angle `(h, k)`

*(§ 6)*

> The region so characterised is called the *interior of the angle $(h,k)$*.

**Lean reading.** Basic.lean defines `Interior A O B` from the points `A`, `B` chosen on the sides;
for "the interior of the angle `(h, k)`" to make sense it must only depend on the angle, i.e. on
the unordered pair of half-rays (`SameAngle`). `interior_wellDefined` (plane geometry, groups I, II):
if `∠AOB` and `∠COD` are the same angle (`A ≠ O`, `B ≠ O`), then `Interior A O B = Interior C O D`.
`interior_wellDefined_space`: in space, for the points of a plane `α` containing `O`, `A`, `B`
(Basic.lean: in space the interior is only meaningful inside the plane of the angle).
`exterior_wellDefined`: the same for the exterior (plane geometry). That the interior is the convex
one of the two regions is part of `s6.angle_regions`.

**Status.** proved
-/

theorem interior_wellDefined [HasLines P L] [HasBetween P] [PlaneOrder P L] {A O B C D : P}
    (hAO : A ≠ O) (hBO : B ≠ O) (hs : SameAngle (Line := L) A O B C D) :
    Interior (Line := L) A O B = Interior (Line := L) C O D :=
  interior_eq_of_sameAngle hAO hBO hs

theorem interior_wellDefined_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [SpaceOrder P L Pl] {α : Pl} {A O B C D : P} (hO : O ∈ α) (hA : A ∈ α) (hB : B ∈ α)
    (hAO : A ≠ O) (hBO : B ≠ O) (hs : SameAngle (Line := L) A O B C D) :
    {X | X ∈ α ∧ X ∈ Interior (Line := L) A O B} = {X | X ∈ α ∧ X ∈ Interior (Line := L) C O D} :=
  interior_eq_of_sameAngle_space hO hA hB hAO hBO hs

/-- The exterior is well defined on angles as well (plane geometry). -/
theorem exterior_wellDefined [HasLines P L] [HasBetween P] [PlaneOrder P L] {A O B C D : P}
    (hAO : A ≠ O) (hBO : B ≠ O) (hs : SameAngle (Line := L) A O B C D) :
    Exterior (Line := L) A O B = Exterior (Line := L) C O D := by
  have hI := interior_eq_of_sameAngle hAO hBO hs
  ext X
  simp only [Exterior, Set.mem_ofPred_eq]
  rw [hI]
  have hr : (X ∈ ray O A ∨ X ∈ ray O B) ↔ (X ∈ ray O C ∨ X ∈ ray O D) := by
    have h1 : X ∈ ({ray O A, ray O B} : Set (Set P)).sUnion ↔
        X ∈ ({ray O C, ray O D} : Set (Set P)).sUnion := by
      unfold SameAngle at hs; rw [hs]
    simpa using h1
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun h => ?_, fun h => ?_, h4⟩
    · rcases hr.2 (Or.inl h) with h' | h'
      · exact h2 h'
      · exact h3 h'
    · rcases hr.2 (Or.inr h) with h' | h'
      · exact h2 h'
      · exact h3 h'
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun h => ?_, fun h => ?_, h4⟩
    · rcases hr.1 (Or.inl h) with h' | h'
      · exact h2 h'
      · exact h3 h'
    · rcases hr.1 (Or.inr h) with h' | h'
      · exact h2 h'
      · exact h3 h'

/-!
## [s6.triangle_angle_interior] The angle of a triangle contains its interior

*(§ 6)*

> It contains all of the interior points of the triangle $ABC$

**Lean reading.** The interior points of a triangle are those of Theorem 6 for triangles
(Order.lean): for side lines `ℓ` of the triangle `V 0 V 1 V 2` (`TriangleLines V ℓ`), `TriInside V ℓ`
is the set of points on the side of each side line containing the opposite vertex.
`triangle_angle_contains_interior`: `TriInside V ℓ ⊆ Interior (V (i+1)) (V i) (V (i+2))` for each
vertex `i`, i.e. the angle `∠A` (`∠BAC` for `A = V 0`) contains all interior points of the
triangle. It only uses I 2 (each side line is the line through two vertices); stated for plane
geometry (`PlaneOrder`, where the interior of a triangle is Hilbert's region of Theorem 6) and in
the plane geometry of a plane `α` of space.

**Status.** proved
-/

theorem triangle_angle_contains_interior [HasLines P L] [HasBetween P] [PlaneOrder P L]
    {V : Fin 3 → P} {ℓ : Fin 3 → L} (hT : TriangleLines V ℓ) (i : Fin 3) :
    TriInside V ℓ ⊆ Interior (Line := L) (V (i + 1)) (V i) (V (i + 2)) :=
  triInside_subset_interior hT i

theorem triangle_angle_contains_interior_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [SpaceOrder P L Pl] (α : Pl) {V : Fin 3 → {X : P // X ∈ α}}
    {ℓ : Fin 3 → {a : L // LiesInPlane (Point := P) a α}} (hT : TriangleLines V ℓ) (i : Fin 3) :
    TriInside V ℓ ⊆ Interior (Line := {a : L // LiesInPlane (Point := P) a α})
      (V (i + 1)) (V i) (V (i + 2)) :=
  triInside_subset_interior hT i

/-!
## [s7.segcong_symm] Congruence of segments is symmetric

*(§ 7)*

> Suppose the segment $AB$ is congruent to the segment $A'B'$. Since, according to axiom IV, 1, the segment $AB$ is congruent to itself, it follows from axiom IV, 2 that $A'B'$ is congruent to $AB$; that is to say, if $AB \equiv A'B'$, then $A'B' \equiv AB$. We say, then, that the two segments are congruent to one another.

**Lean reading.** `segCong_symmetric`: for genuine segments (`A ≠ B`, `A' ≠ B'`; IV 2 only speaks of
genuine segments), `AB ≡ A'B'` implies `A'B' ≡ AB`, by Hilbert's argument (IV 1 reflexivity and
IV 2). Also `segCong_transitive`, which follows in the same way and is used throughout.

**Status.** proved
-/

theorem segCong_symmetric [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {A B A' B' : P} (hAB : A ≠ B) (hA'B' : A' ≠ B') (h : SegCong A B A' B') : SegCong A' B' A B :=
  segCong_symm (L := L) hAB hA'B' h

theorem segCong_transitive [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {A B C D E F : P} (hAB : A ≠ B) (hCD : C ≠ D) (hEF : E ≠ F) (h1 : SegCong A B C D)
    (h2 : SegCong C D E F) : SegCong A B E F :=
  segCong_trans (L := L) hAB hCD hEF h1 h2

/-!
## [s7.congruent_series] Congruent series of points

*(§ 7)*

> Let $A$, $B$, $C$, $D,\ldots,$ $K$, $L$ and $A'$, $B'$, $C'$, $D',\ldots,$ $K'$, $L'$ be two series of points on the straight lines $a$ and $a'$, respectively, so that all the corresponding segments $AB$ and $A'B'$, $AC$ and $A'C'$, $BC$ and $B'C',\ldots,$ $KL$ and $K'L'$ are respectively congruent, then *the two series of points are said to be congruent to one another*. $A$ and $A'$, $B$ and $B',\ldots,$ $L$ and $L'$ are called *corresponding points* of the two congruent series of points.

**Lean reading.** A series of `n` points is `f : Fin n → P`, its points distinct (`Injective`) and on
one line; `CongruentSeries f g`: both are series and `f i f j ≡ g i g j` for all `i ≠ j`. The
corresponding points are `f i` and `g i`.

**Status.** definition
-/

/-- Two **congruent series of points** (§ 7). -/
def CongruentSeries [HasLines P L] [HasSegCong P] {n : ℕ} (f g : Fin n → P) : Prop :=
  (∃ a : L, ∀ i, f i ∈ a) ∧ (∃ a' : L, ∀ i, g i ∈ a') ∧ Function.Injective f ∧
    Function.Injective g ∧ ∀ i j, i ≠ j → SegCong (f i) (f j) (g i) (g j)

/-!
## [th.9] Theorem 9

*(§ 7)*

> If the first of two congruent series of points $A$, $B$, $C$, $D,\ldots,$ $K$, $L$ and $A'$, $B'$, $C'$, $D',\ldots,$ $K'$, $L'$ is so arranged that $B$ lies between $A$ and $C$, $D,\ldots,$ $K$, $L$, and $C$ between $A$, $B$ and $D,\ldots,$ $K$, $L$, etc., then the points $A'$, $B'$, $C'$, $D',\ldots,$ $K'$, $L'$ of the second series are arranged in a similar way; that is to say, $B'$ lies between $A'$ and $C'$, $D',\ldots,$ $K'$, $L'$, and $C'$ lies between $A'$, $B'$ and $D',\ldots,$ $K'$, $L'$, etc.

**Lean reading.** "So arranged" is Order.lean's `IsArrangement f` (each point lies between any
earlier and any later one, Theorem 4). `theorem9`: if `CongruentSeries f g` and `IsArrangement f`,
then `IsArrangement g`. From the linear axioms I 1–2, II 1–4, IV 1–3 (`SegmentCongruence`), as
Hilbert says. The core is the case of three points (`between_of_segCong`): if `B` lies between `A`
and `C`, `A'B'C'` are distinct collinear points and the three segments are congruent, then `B'` lies
between `A'` and `C'`. Proof: lay off `BC` beyond `B'` to `C*`; by IV 3 `A'C* ≡ AC ≡ A'C'`; if `C'`
is on the half-ray `A'C*`, then `C' = C*` (IV 1); otherwise `A'` lies between `C'` and `B'`, and the
symmetric construction from `C'` gives `A' = A*` with `B'` between `C'` and `A'`, contradicting
II 3.

**Status.** proved
-/

/-- **Theorem 9.** -/
theorem theorem9 [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L] {n : ℕ}
    {f g : Fin n → P} (hc : CongruentSeries (L := L) f g) (hf : IsArrangement f) :
    IsArrangement g := by
  obtain ⟨-, ⟨a', ha'⟩, hfi, hgi, hs⟩ := hc
  intro i j k hij hjk
  have hik : i ≠ k := (hij.trans hjk).ne
  exact between_of_segCong (hf i j k hij hjk) (collinear_of_mem (ha' i) (ha' j) (ha' k))
    (hgi.ne hij.ne) (hgi.ne hjk.ne) (hgi.ne hik) (hs i j hij.ne) (hs j k hjk.ne) (hs i k hik)

/-!
## [s7.angcong_symm] Congruence of angles is symmetric

*(§ 7)*

> Let the angle $(h,k)$ be congruent to the angle $(h',k')$. Since, according to axiom IV, 4, the angle $(h,k)$ is congruent to itself, it follows from axiom IV, 5 that the angle $(h',k')$ is congruent to the angle $(h,k)$. We say, then, that the angles $(h,k)$ and $(h',k')$ are *congruent to one another*.

**Lean reading.** `angCong_symmetric`: for genuine angles, `∠AOB ≡ ∠A'O'B'` implies
`∠A'O'B' ≡ ∠AOB`, by Hilbert's argument (reflexivity in IV 4, and IV 5); with
`angCong_transitive`. Only the plane-free part of IV 4–5 is used (`AngleCongruence`).

**Status.** proved
-/

theorem angCong_symmetric [HasLines P L] [HasBetween P] [HasAngCong P] [AngleCongruence P L]
    {A O B A' O' B' : P} (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong A' O' B' A O B :=
  angCong_symm (L := L) h h' hc

theorem angCong_transitive [HasLines P L] [HasBetween P] [HasAngCong P] [AngleCongruence P L]
    {A O B A' O' B' A'' O'' B'' : P} (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (h'' : ¬Collinear A'' O'' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A' O' B' A'' O'' B'') : AngCong A O B A'' O'' B'' :=
  angCong_trans (L := L) h h' h'' h1 h2

/-!
## [s7.supplementary] Supplementary angles

*(§ 7)*

> Two angles having the same vertex and one side in common, while the sides not common form a straight line, are called *supplementary angles*.

**Lean reading.** `AreSupplementary A O B C O' D`: the angles `∠AOB` and `∠COD` (genuine) have the
same vertex (`O' = O`) and can be written `∠XOY`, `∠YOZ` (`SameAngle`) with the common side `OY`
and `O` between `X` and `Z` (the sides not common form a straight line). The normal form used in
Theorem 12 is `areSupplementary_of_between`: `∠AOB` and `∠BOC` are supplementary when `O` lies
between `A` and `C`.

**Status.** definition
-/

/-- `∠AOB` and `∠COD` are **supplementary angles**. -/
def AreSupplementary [HasLines P L] [HasBetween P] (A O B C O' D : P) : Prop :=
  O' = O ∧ ¬Collinear A O B ∧ ¬Collinear C O D ∧
    ∃ X Y Z : P, SameAngle (Line := L) A O B X Y ∧ SameAngle (Line := L) C O D Y Z ∧ Between X O Z

theorem areSupplementary_of_between [HasLines P L] [HasBetween P] [LineOrder P L] {A O B C : P}
    (h : ¬Collinear A O B) (hb : Between A O C) : AreSupplementary (L := L) A O B B O C :=
  ⟨rfl, h, not_collinear_swap (not_collinear_of_between h hb), A, B, C, sameAngle_refl _ _ _,
    sameAngle_refl _ _ _, hb⟩

/-!
## [s7.vertical] Vertical angles

*(§ 7)*

> Two angles having a common vertex and whose sides form straight lines are called *vertical angles*.

**Lean reading.** `AreVertical A O B C O' D`: the genuine angles `∠AOB`, `∠COD` have the same vertex
and can be written `∠XOY`, `∠X'OY'` with `O` between `X` and `X'` and between `Y` and `Y'` (each
side of one angle forms a straight line with a side of the other). Normal form:
`areVertical_of_between`.

**Status.** definition
-/

/-- `∠AOB` and `∠COD` are **vertical angles**. -/
def AreVertical [HasLines P L] [HasBetween P] (A O B C O' D : P) : Prop :=
  O' = O ∧ ¬Collinear A O B ∧ ∃ X Y X' Y' : P, SameAngle (Line := L) A O B X Y ∧
    SameAngle (Line := L) C O D X' Y' ∧ Between X O X' ∧ Between Y O Y'

theorem areVertical_of_between [HasLines P L] [HasBetween P] {A O B C D : P}
    (h : ¬Collinear A O B) (h1 : Between A O C) (h2 : Between B O D) :
    AreVertical (L := L) A O B C O D :=
  ⟨rfl, h, A, B, C, D, sameAngle_refl _ _ _, sameAngle_refl _ _ _, h1, h2⟩

/-!
## [s7.right_angle] Right angles

*(§ 7)*

> An angle which is congruent to its supplementary angle is called a *right angle*.

**Lean reading.** `IsRightAngle A O B`: `∠AOB` is a genuine angle congruent to its supplementary
angle `∠BOC`, `C` a point with `O` between `A` and `C`. An angle has two supplementary angles (along
either side), which are vertical angles and so congruent; the choice in the definition does not
matter (`Frame.isRightAngle_other`: a right angle is congruent to its other supplementary angle,
and `∠BOA` is right when `∠AOB` is; for plane geometry use `planeFrame`, for space `spaceFrame`).

**Status.** definition
-/

/-- `∠AOB` is a **right angle**. -/
def IsRightAngle [HasLines P L] [HasBetween P] [HasAngCong P] (A O B : P) : Prop :=
  ¬Collinear A O B ∧ ∃ C : P, Between A O C ∧ AngCong A O B B O C

/-- A right angle is also congruent to its other supplementary angle (along the side `OB`), and so
`∠BOA` is a right angle as well: the choice of the supplementary angle in the definition does not
matter (vertical angles, in a plane frame). -/
theorem Frame.isRightAngle_other [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [TriangleCongruence P L] (F : Frame P L) {A O B D : P} (h : IsRightAngle (L := L) A O B)
    (hD : Between B O D) : AngCong A O B A O D ∧ IsRightAngle (L := L) B O A := by
  obtain ⟨hn, C, hC, hc⟩ := h
  have nBOC : ¬Collinear (Line := L) B O C := not_collinear_swap (not_collinear_of_between hn hC)
  have nDOA : ¬Collinear (Line := L) D O A := not_collinear_of_between (not_collinear_swap hn) hD
  have v : AngCong B O C D O A := F.vertical nBOC hD (between_symm hC)
  have t : AngCong A O B D O A := angCong_trans hn nBOC nDOA hc v
  have t' : AngCong A O B A O D := angCong_swap_right hn nDOA t
  refine ⟨t', not_collinear_swap hn, D, hD, ?_⟩
  exact angCong_swap_left hn (not_collinear_swap nDOA) t'

/-!
## [s7.congruent_triangles] Congruent triangles

*(§ 7)*

> Two triangles $ABC$ and $A'B'C'$ are said to be *congruent* to one another when all of the following congruences are fulfilled: \[ \begin{array}{ccc} AB \equiv A'B', & AC \equiv A'C', & BC \equiv B'C', \\ \angle A \equiv \angle A', & \angle B \equiv \angle B', & \angle C \equiv \angle C'. \end{array} \]

**Lean reading.** `TriCong A B C A' B' C'`: the six congruences, with `∠A = ∠BAC`, `∠B = ∠ABC`,
`∠C = ∠ACB` (Basic.lean's notation, unit `s6.angle_of_triangle`).

**Status.** definition
-/

/-- The triangles `ABC` and `A'B'C'` are **congruent**. -/
def TriCong [HasSegCong P] [HasAngCong P] (A B C A' B' C' : P) : Prop :=
  SegCong A B A' B' ∧ SegCong A C A' C' ∧ SegCong B C B' C' ∧
    AngCong B A C B' A' C' ∧ AngCong A B C A' B' C' ∧ AngCong A C B A' C' B'

/-!
## [th.10] Theorem 10

*(§ 7)*

> (First theorem of congruence for triangles). If, for the two triangles $ABC$ and $A'B'C'$, the congruences \[ AB \equiv A'B', \: AC \equiv A'C', \: \angle A \equiv \angle A' \] hold, then the two triangles are congruent to each other.

**Lean reading.** `theorem10` (plane geometry, groups I, II, IV: `PlaneCongruence`) and
`theorem10_space` (space geometry, `SpaceCongruence`; the two triangles may lie in different
planes): for triangles `ABC`, `A'B'C'` (`IsTriangle`), `AB ≡ A'B'`, `AC ≡ A'C'` and `∠A ≡ ∠A'` give
`TriCong A B C A' B' C'`. Hilbert's proof, formalized in `Frame.sas`: IV 6 gives `∠B`, `∠C`; lay off
`BC` from `B'` on the half-ray `B'C'` to `D'` (IV 1); IV 6 in `ABC`, `A'B'D'` gives
`∠BAC ≡ ∠B'A'D'`, so by IV 5 `∠B'A'C' ≡ ∠B'A'D'` with `C'`, `D'` on the same side of `A'B'` in the
plane of `A'B'C'`, and the uniqueness in IV 4 gives `D' = C'`. Axioms used: IV 1, 2 (laying off,
symmetry), IV 4 (uniqueness), IV 5, IV 6, with groups I, II (the side of `D'`, and the transitivity
of "same side" that converts IV 4's condition on interior points); IV 3 is not used, although it is
part of the class `SegmentCongruence`.

**Status.** proved
-/

/-- **Theorem 10** (plane geometry). -/
theorem theorem10 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A B C A' B' C' : P} (h : IsTriangle (Line := L) A B C)
    (h' : IsTriangle (Line := L) A' B' C') (hAB : SegCong A B A' B') (hAC : SegCong A C A' C')
    (hA : AngCong B A C B' A' C') : TriCong A B C A' B' C' := by
  rcases plane_cases (P := P) (L := L) with hl | e
  · obtain ⟨x, y, z⟩ := (planeFrame hl).sas h h' hAB hAC hA
    exact ⟨hAB, hAC, x, hA, y, z⟩
  · obtain rfl := e A B; obtain rfl := e A C; obtain rfl := e A A'; obtain rfl := e A B'
    obtain rfl := e A C'
    exact ⟨hAB, hAC, hAB, hA, hA, hA⟩

/-- **Theorem 10** (space geometry). -/
theorem theorem10_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A B C A' B' C' : P}
    (h : IsTriangle (Line := L) A B C) (h' : IsTriangle (Line := L) A' B' C')
    (hAB : SegCong A B A' B') (hAC : SegCong A C A' C') (hA : AngCong B A C B' A' C') :
    TriCong A B C A' B' C' := by
  obtain ⟨x, y, z⟩ := (spaceFrame (Pl := Pl)).sas h h' hAB hAC hA
  exact ⟨hAB, hAC, x, hA, y, z⟩

/-!
## [th.11] Theorem 11

*(§ 7)*

> (Second theorem of congruence for triangles). If in any two triangles one side and the two adjacent angles are respectively congruent, the triangles are congruent.

**Lean reading.** `theorem11` (plane, `PlaneCongruence`), `theorem11_space` (space,
`SpaceCongruence`): `AB ≡ A'B'`, `∠A ≡ ∠A'`, `∠B ≡ ∠B'` give `TriCong A B C A' B' C'`. Hilbert gives no
proof ("we can also easily demonstrate"); the proof (`Frame.asa`): lay off `AC` on the half-ray
`A'C'` to `C''`; Theorem 10 gives `∠ABC ≡ ∠A'B'C''`; the uniqueness in IV 4 gives the half-ray
`B'C'' = B'C'`, so `C''` is the common point `C'` of the lines `A'C'` and `B'C'`.

**Status.** proved
-/

/-- **Theorem 11** (plane geometry). -/
theorem theorem11 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A B C A' B' C' : P} (h : IsTriangle (Line := L) A B C)
    (h' : IsTriangle (Line := L) A' B' C') (hAB : SegCong A B A' B') (hA : AngCong B A C B' A' C')
    (hB : AngCong A B C A' B' C') : TriCong A B C A' B' C' := by
  rcases plane_cases (P := P) (L := L) with hl | e
  · obtain ⟨x, y, z⟩ := (planeFrame hl).asa h h' hAB hA hB
    exact ⟨hAB, x, y, hA, hB, z⟩
  · obtain rfl := e A B; obtain rfl := e A C; obtain rfl := e A A'; obtain rfl := e A B'
    obtain rfl := e A C'
    exact ⟨hAB, hAB, hAB, hA, hA, hA⟩

/-- **Theorem 11** (space geometry). -/
theorem theorem11_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A B C A' B' C' : P}
    (h : IsTriangle (Line := L) A B C) (h' : IsTriangle (Line := L) A' B' C')
    (hAB : SegCong A B A' B') (hA : AngCong B A C B' A' C') (hB : AngCong A B C A' B' C') :
    TriCong A B C A' B' C' := by
  obtain ⟨x, y, z⟩ := (spaceFrame (Pl := Pl)).asa h h' hAB hA hB
  exact ⟨hAB, x, y, hA, hB, z⟩

/-!
## [th.12] Theorem 12

*(§ 7)*

> If two angles $ABC$ and $A'B'C'$ are congruent to each other, their supplementary angles $CBD$ and $C'B'D'$ are also congruent.

**Lean reading.** `theorem12` (plane), `theorem12_space` (space): `∠ABC ≡ ∠A'B'C'`, `B` between `A`
and `D`, `B'` between `A'` and `D'` give `∠CBD ≡ ∠C'B'D'` (the supplementary angles along the sides
`BA`, `B'A'`, as in Hilbert's notation and Fig. 10). Hilbert's proof (`Frame.supp`): lay off
`A'B' ≡ AB`, `C'B' ≡ CB`, `D'B' ≡ DB` on the sides; Theorem 10 in `ABC`, `A'B'C'`; IV 3 for
`AD ≡ A'D'`; Theorem 10 in `CAD`, `C'A'D'`; IV 6 in `BCD`, `B'C'D'`. In the second display of the
proof, "`AC ≡ A'C`" is a misprint for `AC ≡ A'C'`.

**Status.** proved
-/

/-- **Theorem 12** (plane geometry). -/
theorem theorem12 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A B C D A' B' C' D' : P} (h : ¬Collinear (Line := L) A B C)
    (h' : ¬Collinear (Line := L) A' B' C') (hc : AngCong A B C A' B' C') (hD : Between A B D)
    (hD' : Between A' B' D') : AngCong C B D C' B' D' :=
  (planeFrame (line_through_of_ne (L := L) (ne12_of_between (Line := L) hD))).supp h h' hc hD hD'

/-- **Theorem 12** (space geometry). -/
theorem theorem12_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A B C D A' B' C' D' : P}
    (h : ¬Collinear (Line := L) A B C) (h' : ¬Collinear (Line := L) A' B' C')
    (hc : AngCong A B C A' B' C') (hD : Between A B D) (hD' : Between A' B' D') :
    AngCong C B D C' B' D' :=
  (spaceFrame (Pl := Pl)).supp h h' hc hD hD'

/-!
## [s7.vertical_angles] Vertical angles are congruent

*(§ 7)*

> As an immediate consequence of theorem 12, we have a similar theorem concerning the congruence of vertical angles.

**Lean reading.** Two statements. `vertical_angles`: vertical angles are congruent (`O` between `A`
and `C` and between `B` and `D` give `∠AOB ≡ ∠COD`); proof by Theorem 12 applied to `∠COB ≡ ∠BOC`.
`vertical_angles_of_congr`, the analogue of Theorem 12: if `∠AOB ≡ ∠A'O'B'`, their vertical angles
`∠COD`, `∠C'O'D'` are congruent. Plane (`PlaneCongruence`) and space (`_space`) versions.

**Status.** proved
-/

theorem vertical_angles [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A O B C D : P} (h : ¬Collinear (Line := L) A O B)
    (h1 : Between A O C) (h2 : Between B O D) : AngCong A O B C O D :=
  (planeFrame (line_through_of_ne (L := L) (ne12_of_between (Line := L) h1))).vertical h h1 h2

theorem vertical_angles_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A O B C D : P} (h : ¬Collinear (Line := L) A O B)
    (h1 : Between A O C) (h2 : Between B O D) : AngCong A O B C O D :=
  (spaceFrame (Pl := Pl)).vertical h h1 h2

theorem vertical_angles_of_congr [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A O B C D A' O' B' C' D' : P} (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') (hc : AngCong A O B A' O' B') (h1 : Between A O C)
    (h2 : Between B O D) (h1' : Between A' O' C') (h2' : Between B' O' D') :
    AngCong C O D C' O' D' := by
  have nC : ¬Collinear (Line := L) C O D :=
    not_collinear_swap (not_collinear_of_between (not_collinear_swap
      (not_collinear_of_between h h1)) h2)
  have nC' : ¬Collinear (Line := L) C' O' D' :=
    not_collinear_swap (not_collinear_of_between (not_collinear_swap
      (not_collinear_of_between h' h1')) h2')
  exact angCong_trans (L := L) nC h nC' (angCong_symm (L := L) h nC (vertical_angles h h1 h2))
    (angCong_trans (L := L) h h' nC' hc (vertical_angles h' h1' h2'))

theorem vertical_angles_of_congr_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {A O B C D A' O' B' C' D' : P}
    (h : ¬Collinear (Line := L) A O B) (h' : ¬Collinear (Line := L) A' O' B')
    (hc : AngCong A O B A' O' B') (h1 : Between A O C) (h2 : Between B O D)
    (h1' : Between A' O' C') (h2' : Between B' O' D') : AngCong C O D C' O' D' := by
  have nC : ¬Collinear (Line := L) C O D :=
    not_collinear_swap (not_collinear_of_between (not_collinear_swap
      (not_collinear_of_between h h1)) h2)
  have nC' : ¬Collinear (Line := L) C' O' D' :=
    not_collinear_swap (not_collinear_of_between (not_collinear_swap
      (not_collinear_of_between h' h1')) h2')
  exact angCong_trans (L := L) nC h nC'
    (angCong_symm (L := L) h nC (vertical_angles_space (Pl := Pl) h h1 h2))
    (angCong_trans (L := L) h h' nC' hc (vertical_angles_space (Pl := Pl) h' h1' h2'))

/-!
## [th.13] Theorem 13

*(§ 7)*

> Let the angle ($h$, $k$) of the plane $\alpha$ be congruent to the angle ($h'$, $k'$) of the plane $\alpha'$, and, furthermore, let $l$ be a half-ray in the plane $\alpha$ emanating from the vertex of the angle ($h$, $k$) and lying within this angle. Then, there always exists in the plane $\alpha'$ a half-ray $l'$ emanating from the vertex of the angle ($h'$, $k'$) and lying within this angle so that we have \[ \angle (h, l) \equiv \angle (h', l'), \angle (k, l) \equiv \angle (k', l'). \]

**Lean reading.** The angles are `∠AOB` (in `α`) and `∠A'O'B'` (in `α'`); the half-ray `l` within
`∠AOB` is `ray O X` for an interior point `X` (all of whose points are then interior,
`Frame.mem_interior_of_ray`), and likewise `l' = ray O' Y`. `theorem13_space` (space,
`SpaceCongruence`): for `O, A, B, X ∈ α` and `O', A', B' ∈ α'` there is `Y ∈ α'` interior to
`∠A'O'B'` with `∠AOX ≡ ∠A'O'Y` and `∠BOX ≡ ∠B'O'Y`. `theorem13`: plane geometry. Hilbert's proof
(`Frame.interior_transfer`): equal segments `OA ≡ O'A'`, `OB ≡ O'B'`; Theorem 10; the line `AB` meets
`l` in `C` — this is the crossbar theorem, which Hilbert uses without proof; it is proved here from
Pasch's axiom (`Frame.crossbar`); `C'` on `A'B'` with `A'C' ≡ AC` lies between `A'` and `B'`, and
"`BC ≡ B'C'` by IV 3" is really the subtraction of segments (IV 1 and IV 3, `segCong_sub`); then
Theorem 10 twice.

**Status.** proved
-/

/-- **Theorem 13** (plane geometry). -/
theorem theorem13 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A O B A' O' B' X : P} (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') (hc : AngCong A O B A' O' B')
    (hX : X ∈ Interior (Line := L) A O B) :
    ∃ Y, Y ∈ Interior (Line := L) A' O' B' ∧ AngCong A O X A' O' Y ∧ AngCong B O X B' O' Y := by
  rcases plane_cases (P := P) (L := L) with hl | e
  · obtain ⟨Y, -, hY, h1, h2⟩ := (planeFrame hl).interior_transfer (S := Set.univ) rfl trivial
      trivial trivial trivial h h' hc hX
    exact ⟨Y, hY, h1, h2⟩
  · obtain rfl := e A O; obtain rfl := e A B; obtain rfl := e A A'; obtain rfl := e A O'
    obtain rfl := e A B'; obtain rfl := e A X
    exact ⟨A, hX, hc, hc⟩

/-- **Theorem 13** (space geometry): the angles lie in planes `α`, `α'`. -/
theorem theorem13_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {α α' : Pl} {A O B A' O' B' X : P} (hO : O ∈ α)
    (hA : A ∈ α) (hB : B ∈ α) (hXα : X ∈ α) (hO' : O' ∈ α') (hA' : A' ∈ α') (hB' : B' ∈ α')
    (h : ¬Collinear (Line := L) A O B) (h' : ¬Collinear (Line := L) A' O' B')
    (hc : AngCong A O B A' O' B') (hX : X ∈ Interior (Line := L) A O B) :
    ∃ Y, Y ∈ α' ∧ Y ∈ Interior (Line := L) A' O' B' ∧ AngCong A O X A' O' Y ∧
      AngCong B O X B' O' Y := by
  obtain ⟨Y, hYS, hY, h1, h2⟩ := (spaceFrame (Pl := Pl)).interior_transfer (S := {Z | Z ∈ α})
    ⟨α, rfl⟩ hO hA hB hXα h h' hc hX
  exact ⟨Y, hYS {Z | Z ∈ α'} ⟨α', rfl⟩ hO' hA' hB', hY, h1, h2⟩

/-!
## [th.14] Theorem 14

*(§ 7)*

> Let $h$, $k$, $l$ and $h'$, $k'$, $l'$ be two sets of three half-rays, where those of each set emanate from the same point and lie in the same plane. Then, if the congruences \[ \angle (h, l) \equiv \angle (h', l'), \angle (k, l) \equiv \angle (k', l') \] are fulfilled, the following congruence is also valid; viz.: \[ \angle (h,k) \equiv \angle (h', k'). \]

**Lean reading.** The half-rays are `h = OH`, `k = OK`, `l = OM` and `h' = O'H'`, `k' = O'K'`,
`l' = O'M'`, the six angles genuine (`¬Collinear`). **As printed the theorem is false**: nothing
relates the position of `h`, `k` with respect to `l` to that of `h'`, `k'` with respect to `l'`, and
if `h`, `k` lie on the same side of `l` while `h'`, `k'` lie on different sides of `l'`, then
`∠(h, k)` is the "difference" and `∠(h', k')` the "sum" of the two angles. `Theorem14AsPrinted` is
the statement as printed and `theorem14_as_printed_false` refutes it in every plane geometry with
groups I, II, IV having two distinct points (and `theorem14_as_printed_false_space` in every space
geometry with a plane): with `K` between `A` and `B`, `h = h' = OA`, `k = OB`, `l = l' = OK`, and
`k' = OB'` the reflection of `OB` in `OK`, `∠(h, k) ≡ ∠(h', k')` would make `O`, `A`, `K` equidistant
from `B` and `B'` (`Frame.theorem14_counterexample`, by Theorem 10 and the uniqueness of a point
equidistant from three non-collinear points, `Frame.eq_of_equidistant`). The **corrected** theorem
(the form of later editions) adds: `h`, `k` lie on the same side of the line of `l` exactly when
`h'`, `k'` lie on the same side of the line of `l'`. `theorem14` (plane, `PlaneCongruence`) and
`theorem14_space` (space, each set of half-rays in its plane): with this hypothesis
`∠(h, k) ≡ ∠(h', k')`. Proof (`Frame.angle_addition`, "in a similar manner" to Theorem 13): on the
same side, one of `k`, `h` lies within the angle of the other with `l` (`Frame.interior_or_interior`)
and Theorem 13 with the uniqueness in IV 4 gives the claim; on different sides, replace `h`, `h'` by
their opposite half-rays (Theorem 12) and use the first case and Theorem 12 again.

**Status.** proved (corrected)
-/

/-- **Theorem 14 as printed** (plane geometry): two sets of three half-rays from a point with
`∠(h, l) ≡ ∠(h', l')` and `∠(k, l) ≡ ∠(k', l')` have `∠(h, k) ≡ ∠(h', k')`. False. -/
def Theorem14AsPrinted (P : Type u) {L : Type v} [HasLines P L] [HasAngCong P] : Prop :=
  ∀ O H K M O' H' K' M' : P, ¬Collinear (Line := L) H O M → ¬Collinear (Line := L) K O M →
    ¬Collinear (Line := L) H O K → ¬Collinear (Line := L) H' O' M' →
    ¬Collinear (Line := L) K' O' M' → ¬Collinear (Line := L) H' O' K' →
    AngCong H O M H' O' M' → AngCong K O M K' O' M' → AngCong H O K H' O' K'

/-- **Theorem 14 as printed** (space geometry): each set of half-rays lies in a plane. False. -/
def Theorem14AsPrintedSpace (P : Type u) {L : Type v} {Pl : Type w} [HasLines P L]
    [HasPlanes P Pl] [HasAngCong P] : Prop :=
  ∀ O H K M O' H' K' M' : P, (∃ α : Pl, O ∈ α ∧ H ∈ α ∧ K ∈ α ∧ M ∈ α) →
    (∃ α' : Pl, O' ∈ α' ∧ H' ∈ α' ∧ K' ∈ α' ∧ M' ∈ α') →
    ¬Collinear (Line := L) H O M → ¬Collinear (Line := L) K O M →
    ¬Collinear (Line := L) H O K → ¬Collinear (Line := L) H' O' M' →
    ¬Collinear (Line := L) K' O' M' → ¬Collinear (Line := L) H' O' K' →
    AngCong H O M H' O' M' → AngCong K O M K' O' M' → AngCong H O K H' O' K'

/-- **Theorem 14 as printed is false** in every plane geometry (I, II, IV) with two points. -/
theorem theorem14_as_printed_false [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] (h2 : ∃ X Y : P, X ≠ Y) : ¬Theorem14AsPrinted (L := L) P := by
  intro hT
  obtain ⟨X, Y, hXY⟩ := h2
  obtain ⟨A, O, B, h⟩ := exists_noncollinear (Point := P) (Line := L)
  obtain ⟨K, B', -, -, n1, n2, n3, n4, a1, a2, hn⟩ :=
    (planeFrame (line_through_of_ne (L := L) hXY)).theorem14_counterexample (S := Set.univ) rfl
      trivial trivial trivial h
  exact hn (hT O A B K O A B' K n1 n2 h n1 n3 n4 a1 a2)

/-- **Theorem 14 as printed is false** in every space geometry (I, II, IV) having a plane. -/
theorem theorem14_as_printed_false_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] [Nonempty Pl] :
    ¬Theorem14AsPrintedSpace (L := L) (Pl := Pl) P := by
  intro hT
  obtain α : Pl := Classical.arbitrary Pl
  obtain ⟨A, O, B, hA, hO, hB, h⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  obtain ⟨K, B', hK, hB', n1, n2, n3, n4, a1, a2, hn⟩ :=
    (spaceFrame (Pl := Pl)).theorem14_counterexample (S := {Z | Z ∈ α}) ⟨α, rfl⟩ hA hO hB h
  exact hn (hT O A B K O A B' K ⟨α, hO, hA, hB, hK⟩ ⟨α, hO, hA, hB', hK⟩ n1 n2 h n1 n3 n4 a1 a2)

/-- **Theorem 14** (corrected; plane geometry). -/
theorem theorem14 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {O H K M O' H' K' M' : P} (hMO : M ≠ O) (hMO' : M' ≠ O')
    (hHM : ¬Collinear (Line := L) H O M) (hKM : ¬Collinear (Line := L) K O M)
    (hHK : ¬Collinear (Line := L) H O K) (hH'M' : ¬Collinear (Line := L) H' O' M')
    (hK'M' : ¬Collinear (Line := L) K' O' M') (hH'K' : ¬Collinear (Line := L) H' O' K')
    (h1 : AngCong H O M H' O' M') (h2 : AngCong K O M K' O' M')
    (hside : (SameSide (line (Line := L) O M hMO.symm) H K ∧
        SameSide (line (Line := L) O' M' hMO'.symm) H' K') ∨
      (OppositeSides (line (Line := L) O M hMO.symm) H K ∧
        OppositeSides (line (Line := L) O' M' hMO'.symm) H' K')) :
    AngCong H O K H' O' K' :=
  (planeFrame (line_through_of_ne (L := L) hMO)).angle_addition (S := Set.univ) (S' := Set.univ)
    rfl rfl trivial trivial trivial trivial trivial trivial trivial trivial hHM hKM hHK hH'M'
    hK'M' hH'K' h1 h2 hMO hMO' hside

/-- **Theorem 14** (corrected; space geometry): each set of half-rays lies in a plane. -/
theorem theorem14_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {α α' : Pl} {O H K M O' H' K' M' : P} (hO : O ∈ α)
    (hH : H ∈ α) (hK : K ∈ α) (hM : M ∈ α) (hO' : O' ∈ α') (hH' : H' ∈ α') (hK' : K' ∈ α')
    (hM' : M' ∈ α') (hMO : M ≠ O) (hMO' : M' ≠ O')
    (hHM : ¬Collinear (Line := L) H O M) (hKM : ¬Collinear (Line := L) K O M)
    (hHK : ¬Collinear (Line := L) H O K) (hH'M' : ¬Collinear (Line := L) H' O' M')
    (hK'M' : ¬Collinear (Line := L) K' O' M') (hH'K' : ¬Collinear (Line := L) H' O' K')
    (h1 : AngCong H O M H' O' M') (h2 : AngCong K O M K' O' M')
    (hside : (SameSide (line (Line := L) O M hMO.symm) H K ∧
        SameSide (line (Line := L) O' M' hMO'.symm) H' K') ∨
      (OppositeSides (line (Line := L) O M hMO.symm) H K ∧
        OppositeSides (line (Line := L) O' M' hMO'.symm) H' K')) :
    AngCong H O K H' O' K' :=
  (spaceFrame (Pl := Pl)).angle_addition (S := {Z | Z ∈ α}) (S' := {Z | Z ∈ α'}) ⟨α, rfl⟩
    ⟨α', rfl⟩ hO hH hK hM hO' hH' hK' hM' hHM hKM hHK hH'M' hK'M' hH'K' h1 h2 hMO hMO' hside

/-!
## [th.15] Theorem 15

*(§ 7)*

> All right angles are congruent to one another.

**Lean reading.** `theorem15` (plane, `PlaneCongruence`), `theorem15_space` (space): if `∠AOB` and
`∠A'O'B'` are right angles (`IsRightAngle`), then `∠AOB ≡ ∠A'O'B'`. Hilbert's proof
(`Frame.right_angles`): lay off `∠B'A'D'` on the half-ray `AB` on the side of `D`; the new side
`AD''` falls within `∠BAD` or within `∠CAD` (`Frame.interior_or_interior` and the two sides of `AD`;
if it is `AD` itself the angles are congruent); in the first case Theorem 12, IV 5 and Theorem 13
give a half-ray `AD'''` within `∠CAD` with `∠CAD'' ≡ ∠CAD'''`, so by the uniqueness in IV 4 the
half-rays `AD''`, `AD'''` coincide, contradicting the disjointness of the interiors of `∠BAD` and
`∠CAD`; the second case is symmetric (Hilbert: "suppose, for example"). Euclid's postulate thus is
a theorem from groups I, II, IV.

**Status.** proved
-/

/-- **Theorem 15** (plane geometry). -/
theorem theorem15 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A O B A' O' B' : P} (h1 : IsRightAngle (L := L) A O B)
    (h2 : IsRightAngle (L := L) A' O' B') : AngCong A O B A' O' B' := by
  obtain ⟨hn, C, hb, hc⟩ := h1
  obtain ⟨hn', C', hb', hc'⟩ := h2
  have hr := angCong_swap_right hn (not_collinear_swap (not_collinear_of_between hn hb)) hc
  have hr' := angCong_swap_right hn' (not_collinear_swap (not_collinear_of_between hn' hb')) hc'
  exact (planeFrame (line_through_of_ne (L := L) (ne12_of_between (Line := L) hb))).right_angles
    hb hn hr hb' hn' hr'

/-- **Theorem 15** (space geometry). -/
theorem theorem15_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A O B A' O' B' : P}
    (h1 : IsRightAngle (L := L) A O B) (h2 : IsRightAngle (L := L) A' O' B') :
    AngCong A O B A' O' B' := by
  obtain ⟨hn, C, hb, hc⟩ := h1
  obtain ⟨hn', C', hb', hc'⟩ := h2
  have hr := angCong_swap_right hn (not_collinear_swap (not_collinear_of_between hn hb)) hc
  have hr' := angCong_swap_right hn' (not_collinear_swap (not_collinear_of_between hn' hb')) hc'
  exact (spaceFrame (Pl := Pl)).right_angles hb hn hr hb' hn' hr'

/-!
## [s7.acute_obtuse] Acute and obtuse angles

*(§ 7)*

> We can now introduce, in accordance with common usage, the terms “*acute angle*” and “*obtuse angle*.”

**Lean reading.** Common usage needs "less than": `AngLt A O B A' O' B'` (`∠AOB < ∠A'O'B'`) means
that `∠AOB` is congruent to `∠A'O'X` for a point `X` within the segment `A'B'` (a half-ray within
`∠A'O'B'`, by the crossbar theorem; this form needs no plane, so it serves in space as well).
`IsAcute A O B`: `∠AOB` is less than some right angle; `IsObtuse A O B`: some right angle is less
than `∠AOB`. The point of "we can now" is that by Theorem 15 these notions do not depend on the right
angle chosen: `isAcute_wellDefined`, `isObtuse_wellDefined` (plane and space): an acute angle is
less than *every* right angle and an obtuse angle greater than every right angle (with
`Frame.angLt_congr`, from Theorem 13 and the crossbar theorem). Whether right angles exist is not
discussed by Hilbert here and is not needed.

**Status.** definition
-/

/-- `∠AOB` is **less than** `∠A'O'B'`. -/
def AngLt [HasLines P L] [HasBetween P] [HasAngCong P] (A O B A' O' B' : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ¬Collinear (Line := L) A' O' B' ∧
    ∃ X, Between A' X B' ∧ AngCong A O B A' O' X

/-- `∠AOB` is an **acute angle**: less than a right angle. -/
def IsAcute [HasLines P L] [HasBetween P] [HasAngCong P] (A O B : P) : Prop :=
  ∃ A' O' B' : P, IsRightAngle (L := L) A' O' B' ∧ AngLt (L := L) A O B A' O' B'

/-- `∠AOB` is an **obtuse angle**: greater than a right angle. -/
def IsObtuse [HasLines P L] [HasBetween P] [HasAngCong P] (A O B : P) : Prop :=
  ∃ A' O' B' : P, IsRightAngle (L := L) A' O' B' ∧ AngLt (L := L) A' O' B' A O B

theorem isAcute_wellDefined [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A O B A' O' B' : P} (h : IsAcute (L := L) A O B)
    (hr : IsRightAngle (L := L) A' O' B') : AngLt (L := L) A O B A' O' B' := by
  obtain ⟨A1, O1, B1, hr1, hn, hn1, X, hX, hc⟩ := h
  have e := theorem15 hr1 hr
  obtain ⟨Y, hY, hY'⟩ := (planeFrame (line_through_of_ne (L := L) (ne12_of_between (Line := L)
    hX))).angLt_congr hn1 hr.1 hX hc hn e
  exact ⟨hn, hr.1, Y, hY, hY'⟩

theorem isAcute_wellDefined_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A O B A' O' B' : P} (h : IsAcute (L := L) A O B)
    (hr : IsRightAngle (L := L) A' O' B') : AngLt (L := L) A O B A' O' B' := by
  obtain ⟨A1, O1, B1, hr1, hn, hn1, X, hX, hc⟩ := h
  have e := theorem15_space (Pl := Pl) hr1 hr
  obtain ⟨Y, hY, hY'⟩ := (spaceFrame (Pl := Pl)).angLt_congr hn1 hr.1 hX hc hn e
  exact ⟨hn, hr.1, Y, hY, hY'⟩

theorem isObtuse_wellDefined [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A O B A' O' B' : P} (h : IsObtuse (L := L) A O B)
    (hr : IsRightAngle (L := L) A' O' B') : AngLt (L := L) A' O' B' A O B := by
  obtain ⟨A1, O1, B1, hr1, hn1, hn, X, hX, hc⟩ := h
  have e := theorem15 hr hr1
  have F := planeFrame (line_through_of_ne (L := L) (ne12_of_between (Line := L) hX))
  obtain ⟨hAO, hBO, -⟩ := F.ne hn
  have nX := (nc_of_interior (L := L) hAO hBO (mem_interior_of_between (L := L) hn hX)).1
  exact ⟨hr.1, hn, X, hX, angCong_trans hr.1 hn1 nX e hc⟩

theorem isObtuse_wellDefined_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A O B A' O' B' : P} (h : IsObtuse (L := L) A O B)
    (hr : IsRightAngle (L := L) A' O' B') : AngLt (L := L) A' O' B' A O B := by
  obtain ⟨A1, O1, B1, hr1, hn1, hn, X, hX, hc⟩ := h
  have e := theorem15_space (Pl := Pl) hr hr1
  obtain ⟨hAO, hBO, -⟩ := (spaceFrame (Pl := Pl)).ne hn
  have nX := (nc_of_interior (L := L) hAO hBO (mem_interior_of_between (L := L) hn hX)).1
  exact ⟨hr.1, hn, X, hX, angCong_trans hr.1 hn1 nX e hc⟩

/-!
## [s7.isosceles] The base angles of an isosceles triangle

*(§ 7)*

> The theorem relating to the congruence of the base angles $A$ and $B$ of an equilateral triangle $ABC$ follows immediately by the application of axiom IV, 6 to the triangles $ABC$ and $BAC$.

**Lean reading.** "Equilateral" translates *gleichschenklig*, i.e. isosceles: the two sides `CA`,
`CB` are congruent (the claim holds a fortiori for equilateral triangles). `isosceles_base_angles`:
for a triangle with `CA ≡ CB`, `∠CAB ≡ ∠CBA` (no further hypothesis: the distinctness of the
vertices follows from `IsTriangle`, except in a geometry where a point lies on no line, where the
claim is the reflexivity of IV 4). As Hilbert says, it is IV 6 applied to the triangle
and to itself with the vertices `A`, `B` interchanged (formally the triangles `CAB` and `CBA`, the
congruent sides issuing from the first vertex as in IV 6), with `CB ≡ CA` by IV 1–2 and
`∠ACB ≡ ∠BCA` by IV 4. No plane axiom is used (`TriangleCongruence`, shared by plane and space).

**Status.** proved
-/

theorem isosceles_base_angles [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [TriangleCongruence P L] {A B C : P} (h : IsTriangle (Line := L) A B C)
    (hc : SegCong C A C B) : AngCong C A B C B A := by
  by_cases hCA : C = A
  · subst hCA
    by_cases hCB : C = B
    · subst hCB
      exact angCong_refl (Line := L) h
    · exact absurd (collinear_of_ne (Line := L) hCB) h
  · by_cases hCB : C = B
    · subst hCB
      exact absurd (collinear_of_ne (Line := L) hCA).swap12 h
    · exact base_angles (L := L) (fun hh => h hh.perm231) hCA hCB hc

/-!
## [th.16] Theorem 16

*(§ 7)*

> (Third theorem of congruence for triangles.) If two triangles have the three sides of one congruent respectively to the corresponding three sides of the other, the triangles are congruent.

**Lean reading.** `theorem16` (plane, `PlaneCongruence`), `theorem16_space` (space): `AB ≡ A'B'`,
`AC ≡ A'C'`, `BC ≡ B'C'` give `TriCong A B C A' B' C'`. Hilbert only indicates the proof (isosceles
triangles and Theorem 14). The proof (`Frame.sss`): lay off `∠BAC` on `A'B'` on the side opposite
to `C'` and `AC` on its side, giving `C''` with `A'B'C'' ≡ ABC` (Theorem 10); the segment `C'C''`
meets the line `A'B'`; the triangles `A'C'C''` and `B'C'C''` are isosceles, and the base angles add
up (Theorem 14 in its corrected form, both pairs of half-rays lying on the same or on different
sides of the common line `C'C''`) or coincide (when `A'` or `B'` lies on `C'C''`) to
`∠A'C'B' ≡ ∠A'C''B'`; then Theorem 10 twice.

**Status.** proved
-/

/-- **Theorem 16** (plane geometry). -/
theorem theorem16 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {A B C A' B' C' : P} (h : IsTriangle (Line := L) A B C)
    (h' : IsTriangle (Line := L) A' B' C') (hAB : SegCong A B A' B') (hAC : SegCong A C A' C')
    (hBC : SegCong B C B' C') : TriCong A B C A' B' C' := by
  rcases plane_cases (P := P) (L := L) with hl | e
  · obtain ⟨x, y, z⟩ := (planeFrame hl).sss h h' hAB hAC hBC
    exact ⟨hAB, hAC, hBC, x, y, z⟩
  · obtain rfl := e A B; obtain rfl := e A C; obtain rfl := e A A'; obtain rfl := e A B'
    obtain rfl := e A C'
    have r := angCong_refl (Line := L) h
    exact ⟨hAB, hAC, hBC, r, r, r⟩

/-- **Theorem 16** (space geometry). -/
theorem theorem16_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {A B C A' B' C' : P}
    (h : IsTriangle (Line := L) A B C) (h' : IsTriangle (Line := L) A' B' C')
    (hAB : SegCong A B A' B') (hAC : SegCong A C A' C') (hBC : SegCong B C B' C') :
    TriCong A B C A' B' C' := by
  obtain ⟨x, y, z⟩ := (spaceFrame (Pl := Pl)).sss h h' hAB hAC hBC
  exact ⟨hAB, hAC, hBC, x, y, z⟩

/-!
## [s7.figure] Figures and plane figures

*(§ 7)*

> Any finite number of points is called a *figure*. If all of the points lie in a plane, the figure is called a *plane figure*.

**Lean reading.** A figure with `n` points is `f : Fin n → P` with distinct points
(`IsFigure f`: `f` injective; "any finite number of points" is a finite set, listed). A plane
figure (space geometry) has all its points in one plane (`IsPlaneFigure`); in plane geometry every
figure is a plane figure.

**Status.** definition
-/

/-- A **figure**: finitely many (distinct) points. -/
def IsFigure {n : ℕ} (f : Fin n → P) : Prop := Function.Injective f

/-- A **plane figure** (space geometry): a figure all of whose points lie in one plane. -/
def IsPlaneFigure [HasPlanes P Pl] {n : ℕ} (f : Fin n → P) : Prop :=
  IsFigure f ∧ ∃ α : Pl, ∀ i, f i ∈ α

/-!
## [s7.congruent_figures] Congruent figures

*(§ 7)*

> Two figures are said to be *congruent* if their points can be arranged in a one-to-one correspondence so that the corresponding segments and the corresponding angles of the two figures are in every case congruent to each other.

**Lean reading.** The one-to-one correspondence is the indexing: `CongruentFigures f g` for figures
`f`, `g : Fin n → P` (the points `f i` and `g i` correspond) means: both are figures, corresponding
segments are congruent (`f i f j ≡ g i g j` for `i ≠ j`), and corresponding angles are congruent
(`∠(f i)(f j)(f k) ≡ ∠(g i)(g j)(g k)` whenever both are genuine angles). Two figures given as sets
are congruent when some arrangement (indexing) makes them so. The definition does not require
collinear triples to correspond to collinear triples: that is the first property below, a theorem.

**Status.** definition
-/

/-- The figures `f` and `g` are **congruent**, `f i` corresponding to `g i`. -/
def CongruentFigures [HasLines P L] [HasSegCong P] [HasAngCong P] {n : ℕ} (f g : Fin n → P) :
    Prop :=
  Function.Injective f ∧ Function.Injective g ∧
    (∀ i j, i ≠ j → SegCong (f i) (f j) (g i) (g j)) ∧
    ∀ i j k, ¬Collinear (Line := L) (f i) (f j) (f k) → ¬Collinear (Line := L) (g i) (g j) (g k) →
      AngCong (f i) (f j) (f k) (g i) (g j) (g k)

theorem congruentFigures_symm [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [TriangleCongruence P L] {n : ℕ} {f g : Fin n → P} (hc : CongruentFigures (L := L) f g) :
    CongruentFigures (L := L) g f :=
  ⟨hc.2.1, hc.1, fun i j h => segCong_symm (L := L) (hc.1.ne h) (hc.2.1.ne h) (hc.2.2.1 i j h),
    fun i j k h h' => angCong_symm h' h (hc.2.2.2 i j k h' h)⟩

/-!
## [s7.figure_properties] Properties of congruent figures

*(§ 7)*

> Congruent figures have, as may be seen from theorems 9 and 12, the following properties: Three points of a figure lying in a straight line are likewise in a straight line in every figure congruent to it. In congruent figures, the arrangement of the points in corresponding planes with respect to corresponding lines is always the same. The same is true of the sequence of corresponding points situated on corresponding lines.

**Lean reading.** For congruent figures `f`, `g` and distinct indices: `congruentFigures_collinear`
(three points in a straight line correspond to three points in a straight line);
`congruentFigures_sameSide` and `congruentFigures_oppositeSides` (two points `f k`, `f m` on the
same side, resp. on different sides, of the line `f i f j` correspond to points on the same side,
resp. on different sides, of `g i g j`: the arrangement with respect to corresponding lines);
`congruentFigures_between` (betweenness, i.e. the sequence of points on a line, is preserved).
Plane geometry with groups I, II, IV (`PlaneCongruence`) and space geometry (`_space`). In space,
"corresponding planes" is itself a claim: `congruentFigures_coplanar_space` proves that four points
of a figure lying in a plane `α` (three of them not collinear) correspond to four points lying in a
plane `α'`; the side statements in space then only assume that the four points of the first
figure lie in a plane. The proofs use only the congruence of the segments: collinearity by the
isosceles triangles and the uniqueness in IV 4 (`Frame.collinear_of_segCong'`), betweenness by the
core of Theorem 9 (`between_of_segCong`), sides by reflecting a point in the line and the
uniqueness of a point equidistant from three non-collinear points (`Frame.sameSide_of_segCong`),
coplanarity by Theorem 17 in the plane of three corresponding points and the fact that a point with
the distances of a point of a plane from three non-collinear points of that plane lies in the plane
(`Frame.memS_of_equidistant`). Hilbert's "as may be seen from theorems 9 and 12" undersells the
work: the collinearity of the corresponding points needs more than Theorems 9 and 12.

**Status.** proved
-/

theorem congruentFigures_collinear_gen [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [TriangleCongruence P L] (F : Frame P L) {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (h : Collinear (Line := L) (f i) (f j) (f k)) :
    Collinear (Line := L) (g i) (g j) (g k) :=
  F.collinear_of_segCong' h (hc.1.ne hij) (hc.1.ne hjk) (hc.1.ne hik) (hc.2.1.ne hij)
    (hc.2.1.ne hjk) (hc.2.1.ne hik) (hc.2.2.1 i j hij) (hc.2.2.1 j k hjk) (hc.2.2.1 i k hik)

theorem congruentFigures_collinear [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {n : ℕ} {f g : Fin n → P} (hc : CongruentFigures (L := L) f g)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h : Collinear (Line := L) (f i) (f j) (f k)) : Collinear (Line := L) (g i) (g j) (g k) :=
  congruentFigures_collinear_gen (planeFrame (line_through_of_ne (L := L) (hc.2.1.ne hij))) hc hij
    hjk hik h

theorem congruentFigures_collinear_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h : Collinear (Line := L) (f i) (f j) (f k)) : Collinear (Line := L) (g i) (g j) (g k) :=
  congruentFigures_collinear_gen (spaceFrame (Pl := Pl)) hc hij hjk hik h

theorem congruentFigures_between_gen [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [TriangleCongruence P L] (F : Frame P L) {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {i j k : Fin n} (h : Between (f i) (f j) (f k)) :
    Between (g i) (g j) (g k) := by
  have hij : i ≠ j := fun e => ne12_of_between (Line := L) h (by rw [e])
  have hjk : j ≠ k := fun e => ne23_of_between (Line := L) h (by rw [e])
  have hik : i ≠ k := fun e => ne13_of_between (Line := L) h (by rw [e])
  exact between_of_segCong h (congruentFigures_collinear_gen F hc hij hjk hik
    (collinear_of_between h)) (hc.2.1.ne hij) (hc.2.1.ne hjk) (hc.2.1.ne hik) (hc.2.2.1 i j hij)
    (hc.2.2.1 j k hjk) (hc.2.2.1 i k hik)

theorem congruentFigures_between [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {n : ℕ} {f g : Fin n → P} (hc : CongruentFigures (L := L) f g)
    {i j k : Fin n} (h : Between (f i) (f j) (f k)) : Between (g i) (g j) (g k) :=
  congruentFigures_between_gen (planeFrame (line_through_of_ne (L := L)
    (hc.2.1.ne (fun e : i = j => ne12_of_between (Line := L) h (by rw [e]))))) hc h

theorem congruentFigures_between_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {i j k : Fin n} (h : Between (f i) (f j) (f k)) :
    Between (g i) (g j) (g k) :=
  congruentFigures_between_gen (spaceFrame (Pl := Pl)) hc h

theorem congruentFigures_sameSide_gen [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [TriangleCongruence P L] (F : Frame P L) {S S' : Set P} (hS : F.IsPl S)
    (hS' : F.IsPl S') {n : ℕ} {f g : Fin n → P} (hc : CongruentFigures (L := L) f g)
    {i j k m : Fin n} (hfS : f i ∈ S ∧ f j ∈ S ∧ f k ∈ S ∧ f m ∈ S)
    (hgS : g i ∈ S' ∧ g j ∈ S' ∧ g k ∈ S' ∧ g m ∈ S') (hij : i ≠ j) (hkm : k ≠ m)
    (hk : ¬Collinear (Line := L) (f i) (f j) (f k)) (hm : ¬Collinear (Line := L) (f i) (f j) (f m))
    (hs : SameSide (line (Line := L) (f i) (f j) (hc.1.ne hij)) (f k) (f m)) :
    SameSide (line (Line := L) (g i) (g j) (hc.2.1.ne hij)) (g k) (g m) := by
  have ne3 : ∀ {a b c : Fin n}, ¬Collinear (Line := L) (f a) (f b) (f c) → a ≠ c ∧ b ≠ c := by
    intro a b c h
    obtain ⟨h1, h2, h3⟩ := F.ne h
    exact ⟨fun e => h3 (by rw [e]), fun e => h2 (by rw [e])⟩
  obtain ⟨hik, hjk⟩ := ne3 hk
  obtain ⟨him, hjm⟩ := ne3 hm
  have nc : ∀ {c : Fin n}, i ≠ c → j ≠ c → ¬Collinear (Line := L) (f i) (f j) (f c) →
      ¬Collinear (Line := L) (g i) (g j) (g c) := fun h1 h2 h hg =>
    h (congruentFigures_collinear_gen F (congruentFigures_symm hc) hij h2 h1 hg)
  exact F.sameSide_of_segCong hS hS' hfS.1 hfS.2.1 hfS.2.2.1 hfS.2.2.2 hgS.1 hgS.2.1 hgS.2.2.1
    hgS.2.2.2 (hc.1.ne hij) (hc.2.1.ne hij) hk hm (nc hik hjk hk) (nc him hjm hm) (hc.1.ne hkm)
    (hc.2.1.ne hkm) (hc.2.2.1 i j hij) (hc.2.2.1 i k hik) (hc.2.2.1 i m him) (hc.2.2.1 j k hjk)
    (hc.2.2.1 j m hjm) (hc.2.2.1 k m hkm) hs

theorem congruentFigures_sameSide [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {n : ℕ} {f g : Fin n → P} (hc : CongruentFigures (L := L) f g)
    {i j k m : Fin n} (hij : i ≠ j) (hkm : k ≠ m) (hk : ¬Collinear (Line := L) (f i) (f j) (f k))
    (hm : ¬Collinear (Line := L) (f i) (f j) (f m))
    (hs : SameSide (line (Line := L) (f i) (f j) (hc.1.ne hij)) (f k) (f m)) :
    SameSide (line (Line := L) (g i) (g j) (hc.2.1.ne hij)) (g k) (g m) :=
  congruentFigures_sameSide_gen (planeFrame (line_through_of_ne (L := L) (hc.2.1.ne hij)))
    (S := Set.univ) (S' := Set.univ) rfl rfl hc ⟨trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial⟩ hij hkm hk hm hs

/-- **Corresponding planes** (space geometry): four points of a figure in a plane, three of them not
collinear, correspond to four points in a plane. -/
theorem congruentFigures_coplanar_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {α : Pl} {i j k m : Fin n}
    (hn : ¬Collinear (Line := L) (f i) (f j) (f k))
    (hf : f i ∈ α ∧ f j ∈ α ∧ f k ∈ α ∧ f m ∈ α) :
    ∃ α' : Pl, g i ∈ α' ∧ g j ∈ α' ∧ g k ∈ α' ∧ g m ∈ α' := by
  let F : Frame P L := spaceFrame (Pl := Pl)
  obtain ⟨hij', hkj', hik'⟩ := F.ne hn
  have hij : i ≠ j := fun e => hij' (by rw [e])
  have hjk : j ≠ k := fun e => hkj' (by rw [e])
  have hik : i ≠ k := fun e => hik' (by rw [e])
  have hn' : ¬Collinear (Line := L) (g i) (g j) (g k) := fun hg =>
    hn (congruentFigures_collinear_gen F (congruentFigures_symm hc) hij hjk hik hg)
  obtain ⟨α', hi, hj, hk⟩ := exists_plane (Plane := Pl) hn'
  refine ⟨α', hi, hj, hk, ?_⟩
  by_cases hmi : m = i
  · rw [hmi]; exact hi
  by_cases hmj : m = j
  · rw [hmj]; exact hj
  by_cases hmk : m = k
  · rw [hmk]; exact hk
  -- Theorem 17 for the triangle `f i f j f k` in `α`, `g i g j g k` in `α'`, and the point `f m`
  set e : Fin 3 → Fin n := ![i, j, k]
  have he : Function.Injective e := injective_fin3 hij hik hjk
  have hfS : ∀ a, (f ∘ e) a ∈ {Z | Z ∈ α} := by
    intro a; fin_cases a
    exacts [hf.1, hf.2.1, hf.2.2.1]
  have hgS : ∀ a, (g ∘ e) a ∈ {Z | Z ∈ α'} := by
    intro a; fin_cases a
    exacts [hi, hj, hk]
  have hme : ∀ a, m ≠ e a := by
    intro a; fin_cases a
    exacts [hmi, hmj, hmk]
  obtain ⟨Q', hQ'S, hQ'g, hs⟩ := F.theorem17_exists (S := {Z | Z ∈ α}) (S' := {Z | Z ∈ α'})
    ⟨α, rfl⟩ ⟨α', rfl⟩ hfS hgS (hc.1.comp he) (hc.2.1.comp he)
    (fun a b hab => hc.2.2.1 (e a) (e b) (he.ne hab)) (Q := f m) hf.2.2.2
    (fun a => hc.1.ne (hme a))
  have t : ∀ a, SegCong (g (e a)) Q' (g (e a)) (g m) := fun a =>
    SegmentCongruence.ax_IV2 (Line := L) (f (e a)) (f m) (g (e a)) Q' (g (e a)) (g m)
      (hc.1.ne (hme a).symm) (hQ'g a).symm (hc.2.1.ne (hme a).symm) (hs a)
      (hc.2.2.1 (e a) m (hme a).symm)
  exact F.memS_of_equidistant (S := {Z | Z ∈ α'}) ⟨α', rfl⟩ hi hj hk hQ'S hn' (hQ'g 0) (hQ'g 1)
    (hQ'g 2) (hc.2.1.ne hmi) (hc.2.1.ne hmj) (hc.2.1.ne hmk) (t 0) (t 1) (t 2)

/-- Sides are preserved (space geometry): the four points of the first figure lie in a plane `α`
(the corresponding points then lie in a plane, `congruentFigures_coplanar_space`). -/
theorem congruentFigures_sameSide_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {α : Pl} {i j k m : Fin n}
    (hf : f i ∈ α ∧ f j ∈ α ∧ f k ∈ α ∧ f m ∈ α)
    (hij : i ≠ j) (hkm : k ≠ m) (hk : ¬Collinear (Line := L) (f i) (f j) (f k))
    (hm : ¬Collinear (Line := L) (f i) (f j) (f m))
    (hs : SameSide (line (Line := L) (f i) (f j) (hc.1.ne hij)) (f k) (f m)) :
    SameSide (line (Line := L) (g i) (g j) (hc.2.1.ne hij)) (g k) (g m) := by
  obtain ⟨α', hg⟩ := congruentFigures_coplanar_space (Pl := Pl) hc hk hf
  exact congruentFigures_sameSide_gen (spaceFrame (Pl := Pl)) (S := {Z | Z ∈ α})
    (S' := {Z | Z ∈ α'}) ⟨α, rfl⟩ ⟨α', rfl⟩ hc hf hg hij hkm hk hm hs

/-- Different sides are preserved (plane geometry). -/
theorem congruentFigures_oppositeSides [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [PlaneCongruence P L] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {i j k m : Fin n} (hij : i ≠ j) (hkm : k ≠ m)
    (hk : ¬Collinear (Line := L) (f i) (f j) (f k)) (hm : ¬Collinear (Line := L) (f i) (f j) (f m))
    (ho : OppositeSides (line (Line := L) (f i) (f j) (hc.1.ne hij)) (f k) (f m)) :
    OppositeSides (line (Line := L) (g i) (g j) (hc.2.1.ne hij)) (g k) (g m) := by
  have hc' := congruentFigures_symm hc
  have nc : ∀ {c : Fin n}, ¬Collinear (Line := L) (f i) (f j) (f c) →
      ¬Collinear (Line := L) (g i) (g j) (g c) := by
    intro c h hg
    have hic : i ≠ c := by
      rintro rfl; exact h (collinear_of_ne (Line := L) (hc.1.ne hij))
    have hjc : j ≠ c := by
      rintro rfl; exact h (collinear_of_ne (Line := L) (hc.1.ne hij).symm).swap12
    exact h (congruentFigures_collinear hc' hij hjc hic hg)
  have hgk := nc hk
  have hgm := nc hm
  have offl : ∀ {c : Fin n}, ¬Collinear (Line := L) (g i) (g j) (g c) →
      g c ∉ line (Line := L) (g i) (g j) (hc.2.1.ne hij) := fun h hh =>
    h (collinear_of_mem (mem_line_left _) (mem_line_right _) hh)
  rcases sameSide_or_opp' (offl hgk) (offl hgm) with hs | ho'
  · exact absurd (congruentFigures_sameSide hc' hij hkm hgk hgm hs) (not_sameSide_of_opp' ho)
  · exact ho'

/-- Different sides are preserved (space geometry; the four points of the first figure in a
plane). -/
theorem congruentFigures_oppositeSides_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {α : Pl} {i j k m : Fin n}
    (hf : f i ∈ α ∧ f j ∈ α ∧ f k ∈ α ∧ f m ∈ α)
    (hij : i ≠ j) (hkm : k ≠ m) (hk : ¬Collinear (Line := L) (f i) (f j) (f k))
    (hm : ¬Collinear (Line := L) (f i) (f j) (f m))
    (ho : OppositeSides (line (Line := L) (f i) (f j) (hc.1.ne hij)) (f k) (f m)) :
    OppositeSides (line (Line := L) (g i) (g j) (hc.2.1.ne hij)) (g k) (g m) := by
  have hc' := congruentFigures_symm hc
  have nc : ∀ {c : Fin n}, ¬Collinear (Line := L) (f i) (f j) (f c) →
      ¬Collinear (Line := L) (g i) (g j) (g c) := by
    intro c h hg
    have hic : i ≠ c := by
      rintro rfl; exact h (collinear_of_ne (Line := L) (hc.1.ne hij))
    have hjc : j ≠ c := by
      rintro rfl; exact h (collinear_of_ne (Line := L) (hc.1.ne hij).symm).swap12
    exact h (congruentFigures_collinear_space (Pl := Pl) hc' hij hjc hic hg)
  have hgk := nc hk
  have hgm := nc hm
  obtain ⟨α', hg⟩ := congruentFigures_coplanar_space (Pl := Pl) hc hk hf
  have offl : ∀ {c : Fin n}, ¬Collinear (Line := L) (g i) (g j) (g c) →
      g c ∉ line (Line := L) (g i) (g j) (hc.2.1.ne hij) := fun h hh =>
    h (collinear_of_mem (mem_line_left _) (mem_line_right _) hh)
  rcases sameSide_or_opp' (offl hgk) (offl hgm) with hs | ho'
  · exact absurd (congruentFigures_sameSide_space (Pl := Pl) hc' hg hij hkm hgk hgm hs)
      (not_sameSide_of_opp' ho)
  · exact ho'

/-!
## [th.17] Theorem 17

*(§ 7)*

> If $(A, B, C,\ldots)$ and $(A', B', C',\ldots)$ are congruent plane figures and P is a point in the plane of the first, then it is always possible to find a point $P$ in the plane of the second figure so that $(A, B, C,\ldots , P)$ and $(A', B', C', \ldots , P')$ shall likewise be congruent figures. If the two figures have at least three points not lying in a straight line, then the selection of $P'$ can be made in only one way.

**Lean reading.** "Find a point `P`" is a misprint for `P'`. The figures are `f`, `g : Fin n → P`
with `CongruentFigures f g`; the extended figures are `Fin.snoc f Q`, `Fin.snoc g Q'` (the new point
`Q` = Hilbert's `P` is not a point of the figure, so that the extended figure is again a figure; for
a point of the figure the corresponding point is the answer). Plane geometry (`theorem17`,
`theorem17_unique`; groups I, II, IV) and space geometry (`theorem17_space`,
`theorem17_unique_space`: the figures lie in planes `α`, `α'`, `Q ∈ α`, and `Q'` is sought in
`α'`). Existence for any figure; uniqueness when the first figure has three non-collinear points
(then so has the second). Hilbert gives no proof. The proof (`Frame.theorem17_two`): with two points
`A`, `B` of the figure as base, `Q'` is laid off from `A'` at the distance `AQ`, on the line `A'B'`
on the corresponding half-ray if `Q` lies on `AB`, otherwise at the angle `∠BAQ` on the side of
`A'B'` corresponding (through a figure point `C` off `AB`, if any) to the side of `Q`; then every
`f i Q ≡ g i Q'` (Theorems 9, 10, 12, 14 corrected, and the preservation of collinearity, order and
sides), and the angles follow from the segments by Theorem 16 (`Frame.angles_of_segs`). Uniqueness:
`Q'`, `Q''` would be equidistant from three non-collinear points of the plane
(`Frame.eq_of_equidistant`).

**Status.** proved
-/

/-- Extending congruent figures by points at congruent distances gives congruent figures (the
angles by Theorem 16). -/
theorem congruentFigures_snoc [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [TriangleCongruence P L] (F : Frame P L) {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {Q Q' : P} (hQ : Q ∉ Set.range f)
    (hQ' : Q' ∉ Set.range g) (hs : ∀ i, SegCong (f i) Q (g i) Q') :
    CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') := by
  have segs : ∀ i j : Fin (n + 1), i ≠ j → SegCong ((Fin.snoc f Q : Fin (n + 1) → P) i)
      ((Fin.snoc f Q : Fin (n + 1) → P) j) ((Fin.snoc g Q' : Fin (n + 1) → P) i)
      ((Fin.snoc g Q' : Fin (n + 1) → P) j) := by
    intro i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact segCong_swap (L := L) (hs j)
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hs i
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact hc.2.2.1 i j (fun e => hij (by rw [e]))
  exact ⟨Fin.snoc_injective_of_injective hc.1 hQ, Fin.snoc_injective_of_injective hc.2.1 hQ',
    segs, fun i j k h h' => F.angles_of_segs segs h h'⟩

/-- **Theorem 17**, existence (plane geometry). -/
theorem theorem17 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {n : ℕ} {f g : Fin n → P} (hc : CongruentFigures (L := L) f g) {Q : P}
    (hQ : Q ∉ Set.range f) :
    ∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') := by
  rcases plane_cases (P := P) (L := L) with hl | e
  · obtain ⟨Q', -, hQ'g, hs⟩ := (planeFrame hl).theorem17_exists (S := Set.univ)
      (S' := Set.univ) rfl rfl (fun _ => trivial) (fun _ => trivial) hc.1 hc.2.1 hc.2.2.1 trivial
      (fun i e => hQ ⟨i, e.symm⟩)
    exact ⟨Q', congruentFigures_snoc (planeFrame hl) hc hQ (fun ⟨i, hi⟩ => hQ'g i hi.symm) hs⟩
  · -- a single point: `f` has no point at all
    have he : IsEmpty (Fin n) := ⟨fun i => hQ ⟨i, e (f i) Q⟩⟩
    have ei : ∀ x : Fin (n + 1), x = Fin.last n := fun x => by
      cases x using Fin.lastCases with
      | last => rfl
      | cast x => exact he.elim x
    refine ⟨Q, Fin.snoc_injective_of_injective hc.1 hQ,
      Fin.snoc_injective_of_injective hc.2.1 (fun ⟨i, _⟩ => he.elim i),
      fun i j hij => absurd ((ei i).trans (ei j).symm) hij, fun i j k h _ => ?_⟩
    rw [ei i, ei j, ei k] at h ⊢
    simp only [Fin.snoc_last] at h ⊢
    exact angCong_refl h

/-- Uniqueness in Theorem 17, in a plane frame. -/
theorem theorem17_unique_gen [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [TriangleCongruence P L] (F : Frame P L) {S' : Set P} (hS' : F.IsPl S') {n : ℕ}
    {f g : Fin n → P} (hc : CongruentFigures (L := L) f g)
    (h3 : ∃ i j k, ¬Collinear (Line := L) (f i) (f j) (f k)) {Q Q' Q'' : P} (hQ' : Q' ∈ S')
    (hQ'' : Q'' ∈ S') (hgS : ∀ i, g i ∈ S')
    (h1 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'))
    (h2 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'')) :
    Q' = Q'' := by
  obtain ⟨i, j, k, hn⟩ := h3
  obtain ⟨hij', hkj', hik'⟩ := F.ne hn
  have hij : i ≠ j := fun e => hij' (by rw [e])
  have hjk : j ≠ k := fun e => hkj' (by rw [e])
  have hik : i ≠ k := fun e => hik' (by rw [e])
  have hn' : ¬Collinear (Line := L) (g i) (g j) (g k) := fun hg =>
    hn (congruentFigures_collinear_gen F (congruentFigures_symm hc) hij hjk hik hg)
  have ext : ∀ {R : P}, CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P)
      (Fin.snoc g R) → (∀ m, SegCong (f m) Q (g m) R) ∧ (∀ m, f m ≠ Q) ∧ (∀ m, g m ≠ R) := by
    intro R h
    refine ⟨fun m => ?_, fun m e => ?_, fun m e => ?_⟩
    · have := h.2.2.1 (Fin.castSucc m) (Fin.last n) (Fin.castSucc_lt_last m).ne
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using this
    · exact (Fin.castSucc_lt_last m).ne (h.1 (by simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact e))
    · exact (Fin.castSucc_lt_last m).ne (h.2.1 (by
        simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact e))
  obtain ⟨s1, nf, n1⟩ := ext h1
  obtain ⟨s2, -, n2⟩ := ext h2
  have t : ∀ m, SegCong (g m) Q' (g m) Q'' := fun m =>
    SegmentCongruence.ax_IV2 (Line := L) (f m) Q (g m) Q' (g m) Q'' (nf m) (n1 m) (n2 m) (s1 m) (s2 m)
  exact F.eq_of_equidistant hS' (hgS i) (hgS j) (hgS k) hQ' hQ'' hn' (n1 i).symm (n1 j).symm
    (n1 k).symm (n2 i).symm (n2 j).symm (n2 k).symm (t i) (t j) (t k)

/-- **Theorem 17**, uniqueness (plane geometry). -/
theorem theorem17_unique [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {n : ℕ} {f g : Fin n → P} (hc : CongruentFigures (L := L) f g)
    (h3 : ∃ i j k, ¬Collinear (Line := L) (f i) (f j) (f k)) {Q Q' Q'' : P}
    (h1 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'))
    (h2 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'')) :
    Q' = Q'' := by
  rcases plane_cases (P := P) (L := L) with hl | e
  · exact theorem17_unique_gen (planeFrame hl) (S' := Set.univ) rfl hc h3 trivial trivial
      (fun _ => trivial) h1 h2
  · exact e Q' Q''

/-- **Theorem 17**, existence (space geometry: plane figures in the planes `α`, `α'`). -/
theorem theorem17_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {α α' : Pl} {n : ℕ} {f g : Fin n → P}
    (hf : ∀ i, f i ∈ α) (hg : ∀ i, g i ∈ α') (hc : CongruentFigures (L := L) f g) {Q : P}
    (hQα : Q ∈ α) (hQ : Q ∉ Set.range f) :
    ∃ Q', Q' ∈ α' ∧ CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') := by
  obtain ⟨Q', hQ'S, hQ'g, hs⟩ := (spaceFrame (Pl := Pl)).theorem17_exists (S := {Z | Z ∈ α})
    (S' := {Z | Z ∈ α'}) ⟨α, rfl⟩ ⟨α', rfl⟩ hf hg hc.1 hc.2.1 hc.2.2.1 hQα
    (fun i e => hQ ⟨i, e.symm⟩)
  exact ⟨Q', hQ'S, congruentFigures_snoc (spaceFrame (Pl := Pl)) hc hQ
    (fun ⟨i, hi⟩ => hQ'g i hi.symm) hs⟩

/-- **Theorem 17**, uniqueness (space geometry): the point `P'` is unique in the plane `α'`. -/
theorem theorem17_unique_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {α' : Pl} {n : ℕ} {f g : Fin n → P}
    (hg : ∀ i, g i ∈ α') (hc : CongruentFigures (L := L) f g)
    (h3 : ∃ i j k, ¬Collinear (Line := L) (f i) (f j) (f k)) {Q Q' Q'' : P} (hQ' : Q' ∈ α')
    (hQ'' : Q'' ∈ α')
    (h1 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'))
    (h2 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'')) :
    Q' = Q'' :=
  theorem17_unique_gen (spaceFrame (Pl := Pl)) (S' := {Z | Z ∈ α'}) ⟨α', rfl⟩ hc h3 hQ' hQ'' hg
    h1 h2




/-!
## [th.18] Theorem 18

*(§ 7)*

> If $(A, B, C, \ldots)$ and $(A', B', C',\ldots=$ are congruent figures and $P$ represents any arbitrary point, then there can always be found a point $P'$ so that the two figures $(A, B, C, \ldots, P)$ and $(A', B', C', \ldots, P')$ shall likewise be congruent. If the figure $(A, B, C, \ldots , P)$ contains at least four points not lying in the same plane, then the determination of $P'$ can be made in but one way.

**Lean reading.** "`C',…=`" is a misprint for "`C',…)`". Space geometry with groups I, II, IV
(`SpaceCongruence`). The figures are `f`, `g : Fin n → P` with `CongruentFigures f g`, the new
point `Q` (Hilbert's `P`) is not a point of the first figure, and the extended figures are
`Fin.snoc f Q`, `Fin.snoc g Q'`.

**As printed the uniqueness clause is false.** It asks for four non-coplanar points in the
*extended* figure `(A, B, C, …, P)`; but if `(A, B, C, …)` is a triangle and `P` a point off its
plane, then `P'` and its mirror image in the plane of `A'B'C'` both work (in Theorem 17 the
corresponding condition is, correctly, on the given figures). `Theorem18AsPrinted` is the statement as printed, and
`theorem18_as_printed_false` refutes it in every space geometry with groups I, II, IV having a
plane: for two points `Q ≠ R` of a plane `β`, a point `Q₁` of `β` and two points `Q₂`, `R₂` of
another plane through `QR`, on different sides of `QR`, all equidistant from `Q` and `R`
(`Frame.bisector`), the figure `(Q₁, Q₂, R₂)` (congruent to itself) extends by `Q` and also by `R`
(`congruentFigures_snoc`), and `Q₁, Q₂, R₂, Q` are not in one plane.

**Corrected statement** (`Theorem18Statement`): existence as printed, and uniqueness when the
given figure `(A, B, C, …)` contains four points not in a plane; `SpaceCongruenceGivesTheorem18`
is the claim for every space geometry with groups I, II, IV. **The corrected theorem is not proved
here** (Hilbert gives no proof). Proved partial results: (1) the planar case,
`theorem18_planar` (existence for a plane figure and `P` in its plane, `P'` in the plane of the
second figure: Theorem 17 in space) and `theorem18_unique_of_coplanar` (for any figure, if `P` lies
in a plane with three non-collinear points of the first figure, `P'` is unique in all of space;
by `congruentFigures_coplanar_space` and `Frame.eq_of_equidistant`); (2) the refutation above. The general existence needs the elements of solid geometry from groups I, II,
IV: the perpendicular to a plane through a point, Euclid's XI 4 (a line perpendicular to two lines
of a plane through its foot is perpendicular to every line of the plane through it), the plane of
the points equidistant from two points (for the uniqueness), and a case analysis on the position
of `P` and of the figure points with respect to the plane of three non-collinear points of the
figure. This development (comparable in length to all of Theorems 10–17) is not formalized; the
statement is recorded as a `Prop`. A subtlety of this edition: with the literal reading of I 7
(Basic.lean), a single line with no planes is a space geometry, in which four points are "not in a
common plane" vacuously; there all points are collinear and the claim reduces to the linear case.

**Status.** stated (open here)
-/

/-- **Theorem 18 as printed**: uniqueness when the *extended* figure has four points not in a
plane. False (`theorem18_as_printed_false`). -/
def Theorem18AsPrinted (P : Type u) {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ (n : ℕ) (f g : Fin n → P), CongruentFigures (L := L) f g → ∀ Q : P, Q ∉ Set.range f →
    (∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q')) ∧
    ((∃ i j k m : Fin (n + 1), ¬Coplanar (Plane := Pl) ((Fin.snoc f Q : Fin (n + 1) → P) i)
        ((Fin.snoc f Q : Fin (n + 1) → P) j) ((Fin.snoc f Q : Fin (n + 1) → P) k)
        ((Fin.snoc f Q : Fin (n + 1) → P) m)) →
      ∀ Q' Q'' : P, CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') →
        CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'') → Q' = Q'')

/-- **Theorem 18 as printed is false** in every space geometry (I, II, IV) having a plane. -/
theorem theorem18_as_printed_false [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] [Nonempty Pl] :
    ¬Theorem18AsPrinted (L := L) (Pl := Pl) P := by
  intro hT
  let F : Frame P L := spaceFrame (Pl := Pl)
  obtain β : Pl := Classical.arbitrary Pl
  obtain ⟨A, B, C, hA, hB, hC, h⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) β
  have hAB : A ≠ B := (F.ne h).1
  obtain ⟨W, hW⟩ : ∃ W : P, W ∉ β := by
    obtain ⟨A₁, B₁, C₁, D₁, hn⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L)
      (Plane := Pl)
    by_contra hno
    push Not at hno
    exact hn ⟨β, hno A₁, hno B₁, hno C₁, hno D₁⟩
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hWl : W ∉ line (Line := L) A B hAB := fun hh =>
    hW (liesInPlane_of_mem hAB hAl hBl hA hB W hh)
  obtain ⟨γ, hAγ, hBγ, hWγ⟩ := exists_plane (Plane := Pl) (nc_of hAl hBl hAB hWl).1
  obtain ⟨Q₁, R₁, hQ₁β, -, ho₁, hQ₁, -⟩ := F.bisector (S := {Z | Z ∈ β}) ⟨β, rfl⟩ hA hB hAB
  obtain ⟨Q₂, R₂, hQ₂γ, hR₂γ, ho₂, hQ₂, hR₂⟩ :=
    F.bisector (S := {Z | Z ∈ γ}) ⟨γ, rfl⟩ hAγ hBγ hAB
  have hQ₁γ : Q₁ ∉ γ := fun hh => hW (by
    rw [plane_unique (nc_of hAl hBl hAB ho₁.1).1 hA hB hQ₁β hAγ hBγ hh]; exact hWγ)
  have hQR₂ : Q₂ ≠ R₂ := by obtain ⟨-, -, Z, -, hZ⟩ := ho₂; exact ne13_of_between hZ
  obtain ⟨hAm, -⟩ := F.not_mem_bisector hAB ho₂ hQ₂ hR₂ hQR₂
  have hQ₁Q₂ : Q₁ ≠ Q₂ := fun e => hQ₁γ (by rw [e]; exact hQ₂γ)
  have hQ₁R₂ : Q₁ ≠ R₂ := fun e => hQ₁γ (by rw [e]; exact hR₂γ)
  set f : Fin 3 → P := ![Q₁, Q₂, R₂]
  have hfi : Function.Injective f := injective_fin3 hQ₁Q₂ hQ₁R₂ hQR₂
  have hc : CongruentFigures (L := L) f f :=
    ⟨hfi, hfi, fun i j hij => segCong_refl (Line := L) (hfi.ne hij),
      fun i j k hn _ => angCong_refl (Line := L) hn⟩
  have hfl : ∀ i, f i ∉ line (Line := L) A B hAB := by
    intro i; fin_cases i
    exacts [ho₁.1, ho₂.1, ho₂.2.1]
  have hAr : A ∉ Set.range f := fun ⟨i, hi⟩ => hfl i (by rw [hi]; exact hAl)
  have hBr : B ∉ Set.range f := fun ⟨i, hi⟩ => hfl i (by rw [hi]; exact hBl)
  have hsA : ∀ i, SegCong (f i) A (f i) A := fun i =>
    segCong_refl (Line := L) (fun e => hfl i (by rw [e]; exact hAl))
  have hsB : ∀ i, SegCong (f i) A (f i) B := by
    intro i; fin_cases i
    exacts [hQ₁, hQ₂, hR₂]
  have c1 := congruentFigures_snoc F hc hAr hAr hsA
  have c2 := congruentFigures_snoc F hc hAr hBr hsB
  have hnc : ¬Coplanar (Plane := Pl) Q₁ Q₂ R₂ A := by
    rintro ⟨δ, h1, h2, h3, h4⟩
    have e := plane_unique (nc_of (mem_line_left (Line := L) hQR₂) (mem_line_right hQR₂) hQR₂
      hAm).1 h2 h3 h4 hQ₂γ hR₂γ hAγ
    exact hQ₁γ (e ▸ h1)
  refine hAB ((hT 3 f f hc A hAr).2 ⟨Fin.castSucc 0, Fin.castSucc 1, Fin.castSucc 2, Fin.last 3,
    ?_⟩ A B c1 c2)
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  exact hnc

/-- **Theorem 18** (corrected) as a statement about a system of points, lines and planes: existence,
and uniqueness when the given figure `(A, B, C, …)` has four points not in a plane. -/
def Theorem18Statement (P : Type u) {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ (n : ℕ) (f g : Fin n → P), CongruentFigures (L := L) f g → ∀ Q : P, Q ∉ Set.range f →
    (∃ Q', CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q')) ∧
    ((∃ i j k m : Fin n, ¬Coplanar (Plane := Pl) (f i) (f j) (f k) (f m)) →
      ∀ Q' Q'' : P, CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') →
        CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'') → Q' = Q'')

/-- **Hilbert's claim** (Theorem 18, corrected): every space geometry with groups I, II, IV
satisfies it. Not proved here. -/
def SpaceCongruenceGivesTheorem18 : Prop :=
  ∀ (P : Type u) (L : Type v) (Pl : Type w) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceCongruence P L Pl → Theorem18Statement (L := L) (Pl := Pl) P

/-- **Theorem 18, the planar case** (proved): plane figures, the new point in the plane of the
first figure. -/
theorem theorem18_planar [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] {α α' : Pl} {n : ℕ} {f g : Fin n → P}
    (hf : ∀ i, f i ∈ α) (hg : ∀ i, g i ∈ α') (hc : CongruentFigures (L := L) f g) {Q : P}
    (hQα : Q ∈ α) (hQ : Q ∉ Set.range f) :
    ∃ Q', Q' ∈ α' ∧ CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q') :=
  theorem17_space (Pl := Pl) hf hg hc hQα hQ

/-- **Theorem 18, uniqueness for a point coplanar with three points of the figure** (proved): if
the new point lies in a plane with three non-collinear points of the first figure, the point `P'`
is unique in space. -/
theorem theorem18_unique_of_coplanar [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {n : ℕ} {f g : Fin n → P}
    (hc : CongruentFigures (L := L) f g) {α : Pl} {i j k : Fin n}
    (hn : ¬Collinear (Line := L) (f i) (f j) (f k)) (hf : f i ∈ α ∧ f j ∈ α ∧ f k ∈ α) {Q Q' Q'' : P}
    (hQ : Q ∈ α)
    (h1 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'))
    (h2 : CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P) (Fin.snoc g Q'')) :
    Q' = Q'' := by
  let F : Frame P L := spaceFrame (Pl := Pl)
  obtain ⟨hij', hkj', hik'⟩ := F.ne hn
  have hij : i ≠ j := fun e => hij' (by rw [e])
  have hjk : j ≠ k := fun e => hkj' (by rw [e])
  have hik : i ≠ k := fun e => hik' (by rw [e])
  have hn' : ¬Collinear (Line := L) (g i) (g j) (g k) := fun hg =>
    hn (congruentFigures_collinear_gen F (congruentFigures_symm hc) hij hjk hik hg)
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
  -- the corresponding points lie in one plane `α'` with `Q'`, and in one with `Q''`
  have pl : ∀ {R : P}, CongruentFigures (L := L) (Fin.snoc f Q : Fin (n + 1) → P)
      (Fin.snoc g R) → ∃ α' : Pl, g i ∈ α' ∧ g j ∈ α' ∧ g k ∈ α' ∧ R ∈ α' := by
    intro R h
    have := congruentFigures_coplanar_space (Pl := Pl) h (i := Fin.castSucc i)
      (j := Fin.castSucc j) (k := Fin.castSucc k) (m := Fin.last n) (α := α)
      (by simpa only [Fin.snoc_castSucc] using hn)
      (by simpa only [Fin.snoc_castSucc, Fin.snoc_last] using ⟨hf.1, hf.2.1, hf.2.2, hQ⟩)
    simpa only [Fin.snoc_castSucc, Fin.snoc_last] using this
  obtain ⟨α₁, hi₁, hj₁, hk₁, hQ'₁⟩ := pl h1
  obtain ⟨α₂, hi₂, hj₂, hk₂, hQ''₂⟩ := pl h2
  have e : α₂ = α₁ := plane_unique hn' hi₂ hj₂ hk₂ hi₁ hj₁ hk₁
  rw [e] at hQ''₂
  have t : ∀ m, SegCong (g m) Q' (g m) Q'' := fun m =>
    SegmentCongruence.ax_IV2 (Line := L) (f m) Q (g m) Q' (g m) Q'' (nf m) (n1 m) (n2 m) (s1 m)
      (s2 m)
  exact F.eq_of_equidistant (S := {Z | Z ∈ α₁}) ⟨α₁, rfl⟩ hi₁ hj₁ hk₁ hQ'₁ hQ''₂ hn' (n1 i).symm
    (n1 j).symm (n1 k).symm (n2 i).symm (n2 j).symm (n2 k).symm (t i) (t j) (t k)

/-!
## [s7.space_congruence_remark] Congruence in space rests on the linear and plane axioms

*(§ 7)*

> This theorem contains an important result; namely, that all the facts concerning space which have reference to congruence, that is to say, to displacements in space, are (by the addition of the axioms of groups I and II) exclusively the consequences of the six linear and plane axioms mentioned above. Hence, it is not necessary to assume the axiom of parallels in order to establish these facts.

**Lean reading.** A remark on Theorem 18 (stated, not proved here). What is checked in this file:
none of the results of §§ 6–7 up to Theorem 18 assumes the axiom of parallels (the classes used are
`SpaceCongruence` / `PlaneCongruence`, without `SpaceParallels` / `PlaneParallels`); group III enters
only in Theorems 19, 20. "Displacements" (motions) are not defined in this edition; the remark is
read as a comment, not as a theorem about motions.

**Status.** remark
-/

/-!
## [th.19] Theorem 19

*(§ 7)*

> If two parallel lines are cut by a third straight line, the alternate-interior angles and also the exterior-interior angles are congruent.

**Lean reading.** Plane geometry with groups I–IV (`PlaneCongruence`, `PlaneParallels`), and in
space for two parallel lines of a plane `α` (`ParallelIn`; `SpaceCongruence`, `SpaceParallels`).
The parallels are `a`, `b` without a common point, the transversal is the line `AB` (`A ∈ a`,
`B ∈ b`, `A ≠ B`), `Pa ∈ a`, `Qb ∈ b`. Alternate-interior angles (`theorem19_alternate`): `Pa`, `Qb`
on different sides of `AB` give `∠(Pa, A, B) ≡ ∠(Qb, B, A)`. Exterior-interior angles (corresponding
angles, `theorem19_corresponding`): `Pa`, `Qb` on the same side of `AB` and `R` beyond `B` (`B`
between `A` and `R`) give `∠(Pa, A, B) ≡ ∠(Qb, B, R)`. Proof (`Frame.alternate_of_parallel`): lay
off the angle `∠(Qb, B, A)` at `A`; the new line does not meet `b` by the converse
(`s7.parallel_criterion`, without III), so it is `a` by the uniqueness of parallels (III); the
exterior-interior case follows with vertical angles. Hilbert omits the proofs ("we can then easily
establish").

**Status.** proved
-/

/-- **Theorem 19**, alternate-interior angles (plane geometry). -/
theorem theorem19_alternate [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {a b : L} (hab : ¬Meets (Point := P) a b)
    {A B Pa Qb : P} (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb) : AngCong Pa A B Qb B A :=
  (planeFrame (line_through_of_ne (L := L) hAB)).alternate_of_parallel (S := Set.univ) rfl
    (parUnique_plane _) (fun _ _ => trivial) (fun _ _ => trivial) hab hA hB hAB hPa hQb hopp

/-- **Theorem 19**, exterior-interior angles (plane geometry). -/
theorem theorem19_corresponding [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {a b : L} (hab : ¬Meets (Point := P) a b)
    {A B Pa Qb R : P} (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hs : SameSide (line (Line := L) A B hAB) Pa Qb) (hR : Between A B R) :
    AngCong Pa A B Qb B R :=
  (planeFrame (line_through_of_ne (L := L) hAB)).corresponding_of_parallel (S := Set.univ) rfl
    (parUnique_plane _) (fun _ _ => trivial) (fun _ _ => trivial) hab hA hB hAB hPa hQb hs hR

/-- **Theorem 19**, alternate-interior angles (space geometry, parallels in a plane `α`). -/
theorem theorem19_alternate_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] [SpaceParallels P L Pl] {α : Pl} {a b : L}
    (hab : ParallelIn (Point := P) α a b) {A B Pa Qb : P} (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B)
    (hPa : Pa ∈ a) (hQb : Qb ∈ b) (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb) :
    AngCong Pa A B Qb B A :=
  (spaceFrame (Pl := Pl)).alternate_of_parallel (S := {Z | Z ∈ α}) ⟨α, rfl⟩ parUnique_space
    hab.1 hab.2.1 hab.2.2 hA hB hAB hPa hQb hopp

/-- **Theorem 19**, exterior-interior angles (space geometry, parallels in a plane `α`). -/
theorem theorem19_corresponding_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] [SpaceParallels P L Pl] {α : Pl}
    {a b : L} (hab : ParallelIn (Point := P) α a b) {A B Pa Qb R : P} (hA : A ∈ a) (hB : B ∈ b)
    (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hs : SameSide (line (Line := L) A B hAB) Pa Qb) (hR : Between A B R) :
    AngCong Pa A B Qb B R :=
  (spaceFrame (Pl := Pl)).corresponding_of_parallel (S := {Z | Z ∈ α}) ⟨α, rfl⟩ parUnique_space
    hab.1 hab.2.1 hab.2.2 hA hB hAB hPa hQb hs hR

/-!
## [s7.parallel_criterion] The converse of Theorem 19

*(§ 7)*

> Conversely, if the alternate-interior or the exterior-interior angles are congruent, the given lines are parallel.

**Lean reading.** `theorem19_converse_alternate`, `theorem19_converse_corresponding` (plane, groups I,
II, IV only: no axiom of parallels is needed), and the space versions for two lines of a plane `α`:
with the notation of Theorem 19, congruent alternate-interior angles, or congruent exterior-interior
angles, imply that `a` and `b` have no common point. Proof (`Frame.parallel_of_alternate`): if they
met in `X`, say on the side of `Pa`, lay off `AX` from `B` on the half-ray `BQb` to `Y`; Theorem 10
gives `∠ABX ≡ ∠BAY`, Theorem 12 and IV 4 put `Y` on `a`, and the two lines would have the two common
points `X`, `Y`. (Hilbert's "parallel" means: lying in one plane without a common point; both lines
lie in `α` by hypothesis.)

**Status.** proved
-/

theorem theorem19_converse_alternate [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] {a b : L} {A B Pa Qb : P} (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B)
    (hPa : Pa ∈ a) (hQb : Qb ∈ b) (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb)
    (hc : AngCong Pa A B Qb B A) : ¬Meets (Point := P) a b :=
  (planeFrame (line_through_of_ne (L := L) hAB)).parallel_of_alternate (S := Set.univ) rfl
    (fun _ _ => trivial) (fun _ _ => trivial) hA hB hAB hPa hQb hopp hc

theorem theorem19_converse_corresponding [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [PlaneCongruence P L] {a b : L} {A B Pa Qb R : P} (hA : A ∈ a) (hB : B ∈ b)
    (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hs : SameSide (line (Line := L) A B hAB) Pa Qb) (hR : Between A B R)
    (hc : AngCong Pa A B Qb B R) : ¬Meets (Point := P) a b :=
  (planeFrame (line_through_of_ne (L := L) hAB)).parallel_of_corresponding (S := Set.univ) rfl
    (fun _ _ => trivial) (fun _ _ => trivial) hA hB hAB hPa hQb hs hR hc

theorem theorem19_converse_alternate_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {α : Pl} {a b : L}
    (ha : LiesInPlane (Point := P) a α) (hb : LiesInPlane (Point := P) b α) {A B Pa Qb : P}
    (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb) (hc : AngCong Pa A B Qb B A) :
    ParallelIn (Point := P) α a b :=
  ⟨ha, hb, (spaceFrame (Pl := Pl)).parallel_of_alternate (S := {Z | Z ∈ α}) ⟨α, rfl⟩ ha hb hA hB
    hAB hPa hQb hopp hc⟩

theorem theorem19_converse_corresponding_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl] {α : Pl} {a b : L}
    (ha : LiesInPlane (Point := P) a α) (hb : LiesInPlane (Point := P) b α) {A B Pa Qb R : P}
    (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hs : SameSide (line (Line := L) A B hAB) Pa Qb) (hR : Between A B R)
    (hc : AngCong Pa A B Qb B R) : ParallelIn (Point := P) α a b :=
  ⟨ha, hb, (spaceFrame (Pl := Pl)).parallel_of_corresponding (S := {Z | Z ∈ α}) ⟨α, rfl⟩ ha hb hA
    hB hAB hPa hQb hs hR hc⟩

/-!
## [th.20] Theorem 20

*(§ 7)*

> The sum of the angles of a triangle is two right angles.

**Lean reading.** No addition of angles is defined in this edition; "the sum of the angles `α`,
`β`, `γ` is two right angles" is read as: the three angles can be laid off side by side at a point
`O` so as to fill a straight angle, `AnglesSumTwoRight`: there are `X`, `Y`, `Z`, `W` with `O` between
`X` and `W`, `Y` within `∠XOZ`, `Z` within `∠YOW`, and `∠XOY ≡ α`, `∠YOZ ≡ β`, `∠ZOW ≡ γ`. A straight
angle is two right angles: a right angle `∠XOY` and its supplementary angle `∠YOW` (congruent to it)
fill it (`straight_angle_two_right`). `theorem20` (plane, groups I–IV) and `theorem20_space` (a
triangle of space, groups I–IV of space): for a triangle `ABC`, `AnglesSumTwoRight C A B A C B C B A`
(the angles `∠A`, `∠C`, `∠B`). The plane version assumes `A ≠ B` (the vertices of a triangle are
distinct); without it the statement fails in the geometry consisting of a single point, where
`¬Collinear A A A` holds and nothing lies between two points. Proof (`Frame.angle_sum`): lay off `∠A` at `C` on `CA`, opposite to
`B`; the new line `CX` is parallel to `AB` (converse of Theorem 19); with `W` beyond `C`, Theorem 19
gives `∠BCW ≡ ∠B`; the parallel puts `A` within `∠XCB` and `B` within `∠ACW`.

**Status.** proved
-/

/-- The angles `∠A₁O₁B₁`, `∠A₂O₂B₂`, `∠A₃O₃B₃` **sum to two right angles**: laid off side by side
they fill a straight angle. -/
def AnglesSumTwoRight [HasLines P L] [HasBetween P] [HasAngCong P]
    (A₁ O₁ B₁ A₂ O₂ B₂ A₃ O₃ B₃ : P) : Prop :=
  ∃ O X Y Z W : P, Between X O W ∧ Y ∈ Interior (Line := L) X O Z ∧
    Z ∈ Interior (Line := L) Y O W ∧ AngCong A₁ O₁ B₁ X O Y ∧ AngCong A₂ O₂ B₂ Y O Z ∧
    AngCong A₃ O₃ B₃ Z O W

/-- A straight angle consists of two right angles: a right angle `∠XOY` and its supplementary
angle, which is congruent to it. -/
theorem straight_angle_two_right [HasLines P L] [HasBetween P] [HasAngCong P] {X O Y : P}
    (h : IsRightAngle (L := L) X O Y) : ∃ W, Between X O W ∧ AngCong X O Y Y O W :=
  h.2

/-- **Theorem 20** (plane geometry). The vertices of a triangle are distinct (`A ≠ B`; this only
excludes the geometry with a single point, where there is no betweenness at all). -/
theorem theorem20 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {A B C : P} (h : IsTriangle (Line := L) A B C)
    (hAB : A ≠ B) : AnglesSumTwoRight (L := L) C A B A C B C B A := by
  obtain ⟨X, W, -, -, hW, hA, hB, h1, h2⟩ := (planeFrame (line_through_of_ne (L := L) hAB)).angle_sum
    (S := Set.univ) rfl (parUnique_plane _) trivial trivial trivial h
  exact ⟨C, X, A, B, W, hW, hA, hB, h1, angCong_refl (fun hh => h hh.swap23), h2⟩

/-- **Theorem 20** (space geometry). -/
theorem theorem20_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] [SpaceParallels P L Pl] {A B C : P}
    (h : IsTriangle (Line := L) A B C) : AnglesSumTwoRight (L := L) C A B A C B C B A := by
  obtain ⟨α, hA, hB, hC⟩ := exists_plane (Plane := Pl) h
  obtain ⟨X, W, -, -, hW, hA', hB', h1, h2⟩ := (spaceFrame (Pl := Pl)).angle_sum
    (S := {Z | Z ∈ α}) ⟨α, rfl⟩ parUnique_space hA hB hC h
  exact ⟨C, X, A, B, W, hW, hA', hB', h1, angCong_refl (fun hh => h hh.swap23), h2⟩

/-!
## [s7.circle] Circles

*(§ 7)*

> Definitions. If $M$ is an arbitrary point in the plane $a$, the totality of all points $A$, for which the segments $MA$ are congruent to one another, is called *a circle*. $M$ is called the *centre of the circle*.

**Lean reading.** "The plane `a`" is a misprint for "the plane `α`". A circle with centre `M` is
the set of the points `A ≠ M` whose segments `MA` are congruent to a given segment `MR`
(`Circle M R`, plane geometry; `CircleIn α M R`, the points of a plane `α` of space). Any two of its
segments `MA`, `MB` are congruent to one another (`circle_segCong`, IV 1–2), and the circle is the
whole class: a point `A ≠ M` with `MA` congruent to some `MB` of the circle belongs to it
(`mem_circle_of_segCong`), so that "the totality of all points for which the segments `MA` are
congruent to one another" is a set of this form.

**Status.** definition
-/

/-- The **circle** with centre `M` through `R` (plane geometry). -/
def Circle [HasSegCong P] (M R : P) : Set P := {A | A ≠ M ∧ SegCong M R M A}

/-- The **circle** with centre `M` through `R` in the plane `α` of space. -/
def CircleIn [HasPlanes P Pl] [HasSegCong P] (α : Pl) (M R : P) : Set P :=
  {A | A ∈ α ∧ A ≠ M ∧ SegCong M R M A}

theorem circle_segCong [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {M R A B : P} (hR : R ≠ M) (hA : A ∈ Circle M R) (hB : B ∈ Circle M R) :
    SegCong M A M B :=
  SegmentCongruence.ax_IV2 (Line := L) M R M A M B hR.symm hA.1.symm hB.1.symm hA.2 hB.2

theorem mem_circle_of_segCong [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {M R A B : P} (hR : R ≠ M) (hB : B ∈ Circle M R) (hA : A ≠ M) (h : SegCong M A M B) :
    A ∈ Circle M R :=
  ⟨hA, segCong_trans (L := L) hR.symm hB.1.symm hA.symm hB.2
    (segCong_symm (L := L) hA.symm hB.1.symm h)⟩

/-!
## [s7.circle_properties] The known properties of the circle

*(§ 7)*

> From this definition can be easily deduced, with the help of the axioms of groups III and IV, the known properties of the circle; in particular, the possibility of constructing a circle through any three points not lying in a straight line, as also the congruence of all angles inscribed in the same segment of a circle, and the theorem relating to the angles of an inscribed quadrilateral.

**Lean reading.** Plane geometry with groups I–IV (`PlaneCongruence`, `PlaneParallels`; "with the
help of III and IV", groups I and II being presupposed). The three named properties are formalized
as statements about a plane geometry: `CircleThroughThree` (for non-collinear `A`, `B`, `C` there is
a centre `M`, distinct from the three points, with `MA ≡ MB ≡ MC`), `InscribedAnglesCongruent` (if
`A`, `B`, `C`, `D` lie on a circle with centre `M`, none of them being `M`, and `C`, `D` lie on the
same side of `AB`, i.e. in the same segment of the circle, then `∠ACB ≡ ∠ADB`; the points must
differ from `M` since congruences of degenerate segments `MM` are junk), `InscribedQuadrilateral` (if `C`, `D` lie on different sides of `AB`, the opposite
angles `∠ACB`, `∠ADB` of the inscribed quadrilateral `ACBD` sum to two right angles: laid side by
side they fill a straight angle), and `CirclePropertiesClaim` is Hilbert's claim for every plane
geometry with groups I–IV. Hilbert gives no proof ("can be easily deduced"). **Proved here: the
circle through three points**, `circleThroughThree` (plane) and `circleThroughThree_space` (the centre
in the plane of the three points), by `Frame.circumcenter`: on each side of `AB` an isosceles apex
(`Frame.apex`, by laying off the base angle and the crossbar theorem); the line of two apexes passes
through the midpoint of `AB` at a right angle and all its points are equidistant from `A`, `B`
(`Frame.equidistant_of_mem`); the perpendicular bisectors of `AB` and `BC` meet, for otherwise the
line `AB` would meet the second one (uniqueness of parallels) at a right angle (Theorem 19), and `AB`,
`BC`, both perpendicular to it, would be parallel (Theorems 15 and 19, converse) although they meet
in `B`. **Not proved here**: the inscribed angles and the inscribed quadrilateral, which need the
angle sums of triangles (Theorem 20) combined with isosceles triangles in each configuration of the
centre with respect to the inscribed angle, a development not undertaken here; and "the known
properties of the circle" in general are not formalized.

**Status.** stated (open here)
-/

/-- Through three non-collinear points passes a circle. -/
def CircleThroughThree (P : Type u) {L : Type v} [HasLines P L] [HasSegCong P] : Prop :=
  ∀ A B C : P, A ≠ B → ¬Collinear (Line := L) A B C →
    ∃ M : P, M ≠ A ∧ M ≠ B ∧ M ≠ C ∧ SegCong M A M B ∧ SegCong M A M C

/-- Angles inscribed in the same segment of a circle are congruent. -/
def InscribedAnglesCongruent (P : Type u) {L : Type v} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ M A B C D : P, A ≠ B → A ≠ M → B ≠ M → C ≠ M → D ≠ M → SegCong M A M B → SegCong M A M C →
    SegCong M A M D → ¬Collinear (Line := L) A C B → ¬Collinear (Line := L) A D B →
    (∀ m : L, A ∈ m → B ∈ m → SameSide m C D) → AngCong A C B A D B

/-- The opposite angles of a quadrilateral inscribed in a circle sum to two right angles. -/
def InscribedQuadrilateral (P : Type u) {L : Type v} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] : Prop :=
  ∀ M A B C D : P, A ≠ B → A ≠ M → B ≠ M → C ≠ M → D ≠ M → SegCong M A M B → SegCong M A M C →
    SegCong M A M D → (∀ m : L, A ∈ m → B ∈ m → OppositeSides m C D) →
    ∃ O X Y W : P, Between X O W ∧ Y ≠ O ∧ ¬Collinear (Line := L) X O Y ∧
      AngCong A C B X O Y ∧ AngCong A D B Y O W

/-- **Hilbert's claim** (§ 7): with groups I–IV of plane geometry, the circle has these properties.
Not proved here. -/
def CirclePropertiesClaim : Prop :=
  ∀ (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → PlaneParallels P L →
      CircleThroughThree (L := L) P ∧ InscribedAnglesCongruent (L := L) P ∧
        InscribedQuadrilateral (L := L) P

/-- **Proved part: a circle through any three non-collinear points** (plane geometry, groups I–IV). -/
theorem circleThroughThree [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] : CircleThroughThree (L := L) P := by
  intro A B C hAB h
  have hl := line_through_of_ne (L := L) hAB
  obtain ⟨M, -, hMA, hMB, hMC, h1, h2⟩ := (planeFrame hl).circumcenter (S := Set.univ) rfl
    (parUnique_plane hl) trivial trivial trivial h
  exact ⟨M, hMA, hMB, hMC, h1, h2⟩

/-- **Proved part: a circle through any three non-collinear points** (space geometry, groups I–IV):
its centre lies in the plane of the three points. -/
theorem circleThroughThree_space [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [SpaceCongruence P L Pl] [SpaceParallels P L Pl] {A B C : P}
    (h : ¬Collinear (Line := L) A B C) :
    ∃ α : Pl, A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ ∃ M, M ∈ α ∧ M ≠ A ∧ M ≠ B ∧ M ≠ C ∧ SegCong M A M B ∧
      SegCong M A M C := by
  obtain ⟨α, hA, hB, hC⟩ := exists_plane (Plane := Pl) h
  obtain ⟨M, hM, hMA, hMB, hMC, h1, h2⟩ := (spaceFrame (Pl := Pl)).circumcenter
    (S := {Z | Z ∈ α}) ⟨α, rfl⟩ parUnique_space hA hB hC h
  exact ⟨α, hA, hB, hC, M, hM, hMA, hMB, hMC, h1, h2⟩

end HilbertFoundations
