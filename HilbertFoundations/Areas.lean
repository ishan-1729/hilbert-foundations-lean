import HilbertFoundations.Proportion
import HilbertFoundations.AreasAux3
import HilbertFoundations.AreasAux7
import HilbertFoundations.AreasAux8
import HilbertFoundations.AreasAux9

/-!
# The theory of plane areas (§§ 18–21, Theorems 24–31)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 18. Equal area and equal content of polygons
* § 19. Parallelograms and triangles having equal bases and equal altitudes
* § 20. The measure of area of triangles and polygons
* § 21. Equality of content and the measure of area

## Setting and encoding

The setting is a plane geometry with the axioms I 1–2, II, III, IV (`PlaneCongruence`,
`PlaneParallels`), without Archimedes's axiom, as Hilbert says (unit `s18.basis`); Archimedes's
axiom is assumed only in the unit that says it needs it.

* **Polygons** are *polygonal regions*: a set `S` of points is a polygon if it has a
  **decomposition** `IsDecomposition S l` into finitely many genuine triangles (`Tri`, with
  non-collinear vertices, `Tri.Nd`) with pairwise disjoint interiors whose closed regions
  (`TriRegion`: the points of the triangle and of its interior) cover `S` exactly. A polygon
  `U` is **composed of** `S₁` and `S₂` (`Composed U S₁ S₂`) if decompositions of `S₁` and `S₂`
  together form a decomposition of `U`.
* **Equal area** (`EqualArea`) and **equal content** (`EqualContent`) are Hilbert's definitions
  for these notions; congruence of triangles is Hilbert's `TriCong` (§ 7).
* The **measure of area** `triMeasure ax t` is half the product of a side and the corresponding
  altitude, computed in the field of segments `Pas.G ax` of Chapter III (whose multiplication is
  Hilbert's product of segments, `hilbertProd_iff'`); `polyMeasure ax S` is the sum over a
  decomposition.

## Organisation

The proofs go through co-ordinates (`Areas.co ax`, Chapter III), where everything is algebra over
an ordered field; the helper modules contain no unit:

* `AreasAux1.lean`: triangles over an ordered field, decompositions (`DecS`), the transversal
  decomposition, cuts of triangles by lines, the closure lemma, the common refinement of a
  triangle by the side lines of a decomposition;
* `AreasAux2.lean`: the additivity of the measure (vertical sections, midpoint sums), the
  common refinement of two decompositions, independence of the decomposition;
* `AreasAux4.lean`: isometries of the co-ordinate plane, equal area and equal content in
  co-ordinates (`KEqArea`, `KEqContent`), the transitivity of both (Theorem 24), copies far away,
  the measure `kmeasure`;
* `AreasAux5.lean`: explicit decompositions (Theorem 26, Euclid's parallelograms, shears);
* `AreasAux6.lean`: adding polygons of equal content, right triangles of equal measure
  (Hilbert's argument of § 21), every polygon is of equal content with a standard triangle,
  polygons of equal measure are of equal content;
* `AreasAux3.lean`: the transfer to the plane geometry (triangles, betweenness, collinearity,
  congruence of triangles, right angles and feet of perpendiculars in co-ordinates);
* `AreasAux7.lean`: a proper part has smaller measure, and the bound on lengths in a triangle of
  equal area with a bounded triangle (used for the non-archimedean example of § 19);
* `AreasAux8.lean`: Euclid's parallelograms with overlapping tops are of equal area, shears keep
  the area over an archimedean field (with Archimedes's axiom equal bases and altitudes give
  equal area), and Euclid's reasoning for Theorem 25 (a motion and `euclid_K`);
* `AreasAux9.lean`: Hilbert's lemma of § 20 (a decomposition of a triangle without points of
  division inside it or within one side is a series of transversal decompositions).

## API for other files

`IsDecomposition`, `IsPolyRegion`, `Composed`, `EqualArea`, `EqualContent`, `IsFoot`,
`IsParallelogram`, `ParRegion`, `IsRectangle`, `triMeasure`, `polyMeasure`, `TransDecomp`,
`SmallerContent`, `theorem24_area`, `theorem24_content`, `theorem25`, `theorem26`,
`theorem27`, `theorem28`, `theorem29`, `theorem30`, `theorem31`, `equalArea_combine`,
`equalContent_of_subtract`, `base_altitude_product`, `transversal_decomposition`,
`transversal_measure`, `transDecomp_measure`, `polyMeasure_eq`, `equalArea_measure`,
`equalContent_measure`, `equalContent_of_measure`, `rectangles_equal_content`, `IsSquare`,
`pythagoras_content`, `nonarch_triangles`, `nonarchimedean_example`, `polygon_triangle`,
`smaller_content_of_subset`, `not_all_equal_content`, `converse_pascal`,
`equalContent_of_equalArea`, `archimedes_equal_area`, `ArchimedesEqualAreaClaim`,
`archimedesEqualAreaClaim`, `TransversalSeriesClaim`, `transversalSeriesClaim`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Areas

universe u v

/-!
## [s18.gerard] Gérard, Schur and Stolz on the theory of areas

*(§ 18)*

> [Note: In connection with the theory of areas, we desire to call attention to the following works of M. Gérard: … M. Gérard has developed a theory concerning the measurement of polygons analogous to that presented in § 20 of the present work. The difference is that M. Gérard makes use of parallel transversals, while I use transversals emanating from the vertex. …]

**Lean reading.** A bibliographical note. Its mathematical content, the measure of polygons of
§ 20 computed with transversals, is formalized in units `s20.transversal`, `th.29`; the works of
Gérard, Schur and Stolz are not checked.

**Status.** remark
-/

/-!
## [s18.basis] The axioms of Chapter IV

*(§ 18)*

> We shall base the investigations of the present chapter upon the same axioms as were made use of in the last chapter, \S§ 13–17, namely, upon the plane axioms of all the groups, with the single exception of the axiom of Archimedes. This involves then the axioms I, 1–2 and II–IV.

**Lean reading.** Every theorem of this file assumes the plane classes `PlaneCongruence P L`
(I 1–2, II, IV) and `PlaneParallels P L` (III), and no `Archimedes` instance. The only unit
that needs Archimedes's axiom, `s19.archimedes_equal_area`, assumes all plane axioms
(`PlaneGeometry`); the non-archimedean example of `s19.usual_demonstration` is an instance of
the plane classes I–IV.

**Status.** remark
-/

/-!
## [s18.euclid] Euclid's theory of areas without Archimedes's axiom

*(§ 18)*

> The theory of proportion as developed in \S§ 13–17 together with the algebra of segments introduced in the same chapter, puts us now in a position to establish Euclid's theory of areas by means of the axioms already mentioned; that is to say, *for the plane geometry, and that independently of the axiom of Archimedes.*

**Lean reading.** A programme, carried out by the theorems of this file, all proved from the
plane axioms I 1–2, II–IV without Archimedes's axiom.

**Status.** remark
-/

/-!
## [s18.pascal] Pascal's theorem and the theory of areas

*(§ 18)*

> Since, by the development given in the last chapter, pp. \pageref{folio37}–\pageref{folio56}, the theory of proportion was made to depend essentially upon Pascal's theorem (theorem 21), the same may then be said here of the theory of areas. This manner of establishing the theory of areas seems to me a very remarkable application of Pascal's theorem to elementary geometry.

**Lean reading.** The measure of area is computed in the field of segments `Pas.G ax` of
Chapter III, whose commutativity is Pascal's theorem (Pascal.lean); the commutativity of the
product is used throughout (for instance in `base_altitude_product`).

**Status.** remark
-/

section Defs

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]

/-!
## [s18.decomposition] Decomposition and composition of polygons

*(§ 18)*

> If we join two points of a polygon $P$ by any arbitrary broken line lying entirely within the polygon, we shall obtain two new polygons $P_1$ and $P_2$ whose interior points all lie within $P$. We say that $P$ is *decomposed into* $P_1$ and $P_2$, or that the polygon $P$ is *composed of* $P_1$ and $P_2$.

**Lean reading.** Hilbert's polygons are the simple polygons of § 4, whose interior is given by
Theorem 6, open in general (Order.lean); a broken line inside a polygon cuts it into two polygons.
Here polygons are encoded as **polygonal regions**, the encoding standard for the theory of
content: a triangle `t : Tri P` with non-collinear vertices (`Tri.Nd`) has the region
`TriRegion t` (the points of the segments joining the vertex `a` to the points of the side `bc`:
the points of the triangle and of its interior) and the interior `TriInterior t`;
`IsDecomposition S l` says that the genuine triangles of the list `l` have pairwise disjoint
interiors and that their regions cover the set `S` exactly; `IsPolyRegion S`: `S` has a non-empty
decomposition. `Composed U S₁ S₂` ("`U` is composed of `S₁` and `S₂`"): there are non-empty
decompositions of `S₁` and `S₂` which together decompose `U`; so the interior points of `S₁`,
`S₂` lie in `U` and the two parts do not overlap, which is what Hilbert's broken line achieves.
Departures: polygonal regions need not be simple polygons (they may be disconnected), which
makes "composed of" more general than a cut by one broken line; Hilbert's definitions of equal
area and content are taken over verbatim for these regions. All statements below are about
polygonal regions; every simple polygon decomposable into triangles is one.

**Status.** definition
-/

/-- `l` is a **decomposition of `S` into triangles**: genuine triangles with pairwise disjoint
interiors whose regions cover `S`. -/
def IsDecomposition (S : Set P) (l : List (Tri P)) : Prop :=
  (∀ t ∈ l, t.Nd (L := L)) ∧ l.Pairwise (fun t t' => Disjoint (TriInterior t) (TriInterior t')) ∧
    ∀ X, X ∈ S ↔ ∃ t ∈ l, X ∈ TriRegion t

/-- `S` is a **polygon** (a polygonal region): it has a non-empty decomposition into triangles. -/
def IsPolyRegion (S : Set P) : Prop := ∃ l : List (Tri P), l ≠ [] ∧ IsDecomposition (L := L) S l

/-- The polygon `U` is **composed of** the polygons `S₁` and `S₂`. -/
def Composed (U S₁ S₂ : Set P) : Prop :=
  ∃ l₁ l₂ : List (Tri P), l₁ ≠ [] ∧ l₂ ≠ [] ∧ IsDecomposition (L := L) S₁ l₁ ∧
    IsDecomposition (L := L) S₂ l₂ ∧ IsDecomposition (L := L) U (l₁ ++ l₂)

variable [HasSegCong P] [HasAngCong P]

/-!
## [s18.equal_area] Equal area

*(§ 18)*

> Definition. Two polygons are said to be of *equal area* when they can be decomposed into a finite number of triangles which are respectively congruent to one another in pairs.

**Lean reading.** `EqualArea S T`: there are decompositions `l` of `S` and `m` of `T` of the same
length whose triangles are congruent in pairs, `List.Forall₂ Tri.Cong l m`, where `Tri.Cong` is
Hilbert's congruence of triangles `TriCong` of § 7 (three sides and three angles). "Respectively
congruent in pairs" is read as a bijection between the two systems of triangles; listing them
in corresponding order costs nothing. (German: *zerlegungsgleich*.)

**Status.** definition
-/

/-- `S` and `T` are of **equal area**. -/
def EqualArea (S T : Set P) : Prop :=
  ∃ l m : List (Tri P), IsDecomposition (L := L) S l ∧ IsDecomposition (L := L) T m ∧
    List.Forall₂ Tri.Cong l m

/-!
## [s18.equal_content] Equal content

*(§ 18)*

> Definition. Two polygons are said to be of *equal content* when it is possible, by the addition of other polygons having equal area, to obtain two resulting polygons having equal area.

**Lean reading.** `EqualContent S T`: there are polygons `S'`, `T'` of equal area such that the
polygon `U` composed of `S` and `S'` and the polygon `V` composed of `T` and `T'` are of equal
area. (German: *ergänzungsgleich*.)

**Status.** definition
-/

/-- `S` and `T` are of **equal content**. -/
def EqualContent (S T : Set P) : Prop :=
  ∃ S' T' U V : Set P, IsPolyRegion (L := L) S' ∧ IsPolyRegion (L := L) T' ∧
    EqualArea (L := L) S' T' ∧ Composed (L := L) U S S' ∧ Composed (L := L) V T T' ∧
    EqualArea (L := L) U V

end Defs

/-! ### Proof infrastructure: the transfer to co-ordinates -/

section Transfer

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-- The co-ordinates of the points of `S`. -/
def Areas.img (ax : Pas.Axes P L) (S : Set P) : Pas.G ax × Pas.G ax → Prop :=
  fun p => ∃ X ∈ S, Areas.co ax X = p

/-- The points with co-ordinates in a region. -/
def Areas.preimg (ax : Pas.Axes P L) (S : Pas.G ax × Pas.G ax → Prop) : Set P :=
  {X | S (Areas.co ax X)}

variable (ax : Pas.Axes P L)

theorem Areas.img_iff {S : Set P} (X : P) : Areas.img ax S (Areas.co ax X) ↔ X ∈ S :=
  ⟨fun ⟨_, hY, e⟩ => (Areas.co_inj ax e) ▸ hY, fun h => ⟨X, h, rfl⟩⟩

theorem Areas.img_preimg (S : Pas.G ax × Pas.G ax → Prop) (p : Pas.G ax × Pas.G ax) :
    Areas.img ax (Areas.preimg ax S) p ↔ S p := by
  obtain ⟨X, rfl⟩ := Areas.co_surj ax p
  rw [Areas.img_iff]; rfl

theorem Areas.img_triRegion {t : Tri P} (ht : t.Nd (L := L)) (p : Pas.G ax × Pas.G ax) :
    Areas.img ax (TriRegion t) p ↔ (Areas.Tri.co ax t).mem p := by
  obtain ⟨X, rfl⟩ := Areas.co_surj ax p
  rw [Areas.img_iff, Areas.mem_triRegion_iff ax ht]

theorem disjoint_triInterior_iff {t t' : Tri P} (ht : t.Nd (L := L)) (ht' : t'.Nd (L := L)) :
    Disjoint (TriInterior t) (TriInterior t') ↔
      ∀ p, ¬((Areas.Tri.co ax t).int p ∧ (Areas.Tri.co ax t').int p) := by
  rw [Set.disjoint_left]
  constructor
  · intro h p ⟨h1, h2⟩
    obtain ⟨X, rfl⟩ := Areas.co_surj ax p
    exact h ((Areas.mem_triInterior_iff ax ht X).2 h1) ((Areas.mem_triInterior_iff ax ht' X).2 h2)
  · intro h X h1 h2
    exact h _ ⟨(Areas.mem_triInterior_iff ax ht X).1 h1, (Areas.mem_triInterior_iff ax ht' X).1 h2⟩

/-- **Decompositions in co-ordinates.** -/
theorem isDecomposition_iff {S : Set P} {l : List (Tri P)} :
    IsDecomposition (L := L) S l ↔ DecS (Areas.img ax S) (l.map (Areas.Tri.co ax)) := by
  constructor
  · rintro ⟨hnd, hpw, hun⟩
    refine ⟨?_, ?_, fun p => ?_⟩
    · simp only [List.mem_map]
      rintro r ⟨t, ht, rfl⟩
      exact (Areas.nd_iff ax).1 (hnd t ht)
    · rw [List.pairwise_map]
      exact hpw.imp_of_mem fun {t t'} h1 h2 h =>
        (disjoint_triInterior_iff ax (hnd t h1) (hnd t' h2)).1 h
    · obtain ⟨X, rfl⟩ := Areas.co_surj ax p
      rw [Areas.img_iff, hun X]
      simp only [List.mem_map, exists_exists_and_eq_and]
      exact exists_congr fun t => and_congr_right fun ht =>
        Areas.mem_triRegion_iff ax (hnd t ht) X
  · rintro ⟨hnd, hpw, hun⟩
    have hnd' : ∀ t ∈ l, t.Nd (L := L) := fun t ht =>
      (Areas.nd_iff ax).2 (hnd _ (List.mem_map_of_mem ht))
    refine ⟨hnd', ?_, fun X => ?_⟩
    · rw [List.pairwise_map] at hpw
      exact hpw.imp_of_mem fun {t t'} h1 h2 h =>
        (disjoint_triInterior_iff ax (hnd' t h1) (hnd' t' h2)).2 h
    · rw [← Areas.img_iff ax X, hun]
      simp only [List.mem_map, exists_exists_and_eq_and]
      exact exists_congr fun t => and_congr_right fun ht =>
        (Areas.mem_triRegion_iff ax (hnd' t ht) X).symm

theorem map_co_unco (l : List (Areas.Tr (Pas.G ax))) :
    (l.map (Areas.unco (L := L) ax)).map (Areas.Tri.co ax) = l := by
  rw [List.map_map]
  have : (Areas.Tri.co ax ∘ Areas.unco (L := L) ax) = id := funext (Areas.co_unco ax)
  rw [this, List.map_id]

theorem isDecomposition_of_decS {S : Set P} {l : List (Areas.Tr (Pas.G ax))}
    (h : DecS (Areas.img ax S) l) : IsDecomposition (L := L) S (l.map (Areas.unco ax)) := by
  rw [isDecomposition_iff ax, map_co_unco]; exact h

theorem isPolygon_iff {S : Set P} : IsPolyRegion (L := L) S ↔ KPoly (Areas.img ax S) := by
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨_, by simpa using hl, (isDecomposition_iff ax).1 h⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨_, by simpa using hl, isDecomposition_of_decS ax h⟩

theorem composed_iff {U S₁ S₂ : Set P} :
    Composed (L := L) U S₁ S₂ ↔
      KComposed (Areas.img ax U) (Areas.img ax S₁) (Areas.img ax S₂) := by
  constructor
  · rintro ⟨l₁, l₂, n₁, n₂, h₁, h₂, hU⟩
    refine ⟨_, _, by simpa using n₁, by simpa using n₂, (isDecomposition_iff ax).1 h₁,
      (isDecomposition_iff ax).1 h₂, ?_⟩
    rw [← List.map_append]; exact (isDecomposition_iff ax).1 hU
  · rintro ⟨l₁, l₂, n₁, n₂, h₁, h₂, hU⟩
    refine ⟨_, _, by simpa using n₁, by simpa using n₂, isDecomposition_of_decS ax h₁,
      isDecomposition_of_decS ax h₂, ?_⟩
    rw [← List.map_append]; exact isDecomposition_of_decS ax hU

omit hC hP in
theorem forall₂_imp_mem {α β : Type*} {R R' : α → β → Prop} {p : α → Prop} {q : β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → (∀ a ∈ l, p a) → (∀ b ∈ m, q b) →
      (∀ a b, p a → q b → R a b → R' a b) → List.Forall₂ R' l m
  | _, _, .nil, _, _, _ => List.Forall₂.nil
  | _, _, .cons h rest, hp, hq, hR =>
    List.Forall₂.cons (hR _ _ (hp _ List.mem_cons_self) (hq _ List.mem_cons_self) h)
      (forall₂_imp_mem rest (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun b hb => hq b (List.mem_cons_of_mem _ hb)) hR)

theorem equalArea_iff {S T : Set P} :
    EqualArea (L := L) S T ↔ KEqArea (Areas.img ax S) (Areas.img ax T) := by
  constructor
  · rintro ⟨l, m, hl, hm, hc⟩
    refine ⟨_, _, (isDecomposition_iff ax).1 hl, (isDecomposition_iff ax).1 hm, ?_⟩
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine forall₂_imp_mem hc hl.1 hm.1 ?_
    intro a b ha hb h
    exact (Areas.cong_iff ax ha hb).1 h
  · rintro ⟨l, m, hl, hm, hc⟩
    refine ⟨_, _, isDecomposition_of_decS ax hl, isDecomposition_of_decS ax hm, ?_⟩
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine forall₂_imp_mem hc hl.1 hm.1 fun a b ha hb h => ?_
    have ha' : (Areas.unco (L := L) ax a).Nd (L := L) := by
      rw [Areas.nd_iff ax, Areas.co_unco]; exact ha
    have hb' : (Areas.unco (L := L) ax b).Nd (L := L) := by
      rw [Areas.nd_iff ax, Areas.co_unco]; exact hb
    rw [Areas.cong_iff ax ha' hb', Areas.co_unco, Areas.co_unco]
    exact h

theorem KEqArea.congr {S S' T T' : Pas.G ax × Pas.G ax → Prop} (h : KEqArea S T)
    (hS : ∀ p, S p ↔ S' p) (hT : ∀ p, T p ↔ T' p) : KEqArea S' T' := by
  obtain ⟨l, m, hl, hm, hc⟩ := h
  exact ⟨l, m, hl.congr hS, hm.congr hT, hc⟩

theorem KComposed.congr3 {U U' S S' T T' : Pas.G ax × Pas.G ax → Prop} (h : KComposed U S T)
    (hU : ∀ p, U p ↔ U' p) (hS : ∀ p, S p ↔ S' p) (hT : ∀ p, T p ↔ T' p) :
    KComposed U' S' T' := by
  obtain ⟨l1, l2, n1, n2, h1, h2, h3⟩ := h
  exact ⟨l1, l2, n1, n2, h1.congr hS, h2.congr hT, h3.congr hU⟩

theorem equalContent_iff {S T : Set P} :
    EqualContent (L := L) S T ↔ KEqContent (Areas.img ax S) (Areas.img ax T) := by
  constructor
  · rintro ⟨S', T', U, V, p1, p2, e, c1, c2, e'⟩
    exact ⟨_, _, _, _, (isPolygon_iff ax).1 p1, (isPolygon_iff ax).1 p2, (equalArea_iff ax).1 e,
      (composed_iff ax).1 c1, (composed_iff ax).1 c2, (equalArea_iff ax).1 e'⟩
  · rintro ⟨S', T', U, V, p1, p2, e, c1, c2, e'⟩
    have hpre := Areas.img_preimg ax
    refine ⟨Areas.preimg ax S', Areas.preimg ax T', Areas.preimg ax U, Areas.preimg ax V,
      (isPolygon_iff ax).2 ?_, (isPolygon_iff ax).2 ?_, (equalArea_iff ax).2 ?_,
      (composed_iff ax).2 ?_, (composed_iff ax).2 ?_, (equalArea_iff ax).2 ?_⟩
    · obtain ⟨l, hl, d⟩ := p1; exact ⟨l, hl, d.congr fun p => (hpre S' p).symm⟩
    · obtain ⟨l, hl, d⟩ := p2; exact ⟨l, hl, d.congr fun p => (hpre T' p).symm⟩
    · exact KEqArea.congr ax e (fun p => (hpre S' p).symm) (fun p => (hpre T' p).symm)
    · exact KComposed.congr3 ax c1 (fun p => (hpre U p).symm) (fun _ => Iff.rfl)
        (fun p => (hpre S' p).symm)
    · exact KComposed.congr3 ax c2 (fun p => (hpre V p).symm) (fun _ => Iff.rfl)
        (fun p => (hpre T' p).symm)
    · exact KEqArea.congr ax e' (fun p => (hpre U p).symm) (fun p => (hpre V p).symm)

omit hC hP in
theorem isDecomposition_single' {t : Tri P} (ht : t.Nd (L := L)) :
    IsDecomposition (L := L) (TriRegion t) [t] :=
  ⟨by simpa using ht, List.pairwise_singleton _ _, fun X => by simp⟩

theorem nil_of_no_axes (h : ¬Nonempty (Pas.Axes P L)) {S : Set P} {l : List (Tri P)}
    (hd : IsDecomposition (L := L) S l) : l = [] := by
  rcases l with _ | ⟨t, l⟩
  · rfl
  · exact absurd (Areas.ax_of_ne (hd.1 t List.mem_cons_self).2) h

end Transfer


section Section18

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-!
## [s18.combine] Combining polygons of equal area

*(§ 18)*

> From these definitions, it follows at once that by combining polygons having equal area, we obtain as a result polygons having equal area.

**Lean reading.** `equalArea_combine`: if `U` is composed of `S₁`, `S₂` and `V` of `T₁`, `T₂`, and
`S₁`, `T₁` and `S₂`, `T₂` are of equal area, then `U`, `V` are of equal area. It does not quite
"follow at once": the decompositions witnessing the equal areas need not be those composing `U`
and `V`, and one has to show that they still fit together (their interiors do not overlap:
`DecS.append_of`, an interior point of one part meeting a triangle of the other would give
overlapping interiors in the original decomposition).

**Status.** proved
-/

theorem equalArea_combine {U V S₁ S₂ T₁ T₂ : Set P} (hU : Composed (L := L) U S₁ S₂)
    (hV : Composed (L := L) V T₁ T₂) (h₁ : EqualArea (L := L) S₁ T₁)
    (h₂ : EqualArea (L := L) S₂ T₂) : EqualArea (L := L) U V := by
  obtain ⟨l₁, -, n₁, -, d₁, -, -⟩ := id hU
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil l₁ n₁
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) (d₁.1 t ht).2
  rw [equalArea_iff ax] at h₁ h₂ ⊢
  rw [composed_iff ax] at hU hV
  exact KEqArea.combine hU hV h₁ h₂

/-!
## [s18.subtract] Taking away polygons of equal area

*(§ 18)*

> However, if from polygons having equal area we take polygons having equal area, we obtain polygons which are of equal content.

**Lean reading.** `equalContent_of_subtract`: if `U` (composed of `S₁`, `S₂`) and `V` (composed
of `T₁`, `T₂`) are of equal area and so are `S₂`, `T₂`, then `S₁`, `T₁` are of equal content.
This is the definition of equal content read backwards.

**Status.** proved
-/

theorem equalContent_of_subtract {U V S₁ S₂ T₁ T₂ : Set P} (hU : Composed (L := L) U S₁ S₂)
    (hV : Composed (L := L) V T₁ T₂) (h : EqualArea (L := L) U V)
    (h₂ : EqualArea (L := L) S₂ T₂) : EqualContent (L := L) S₁ T₁ := by
  obtain ⟨-, l₂, -, n₂, -, d₂, -⟩ := id hU
  obtain ⟨-, m₂, -, k₂, -, f₂, -⟩ := id hV
  exact ⟨S₂, T₂, U, V, ⟨l₂, n₂, d₂⟩, ⟨m₂, k₂, f₂⟩, h₂, hU, hV, h⟩

/-!
## [th.24] Theorem 24

*(§ 18)*

> If each of two polygons $P_1$ and $P_2$ is of equal area to a third polygon $P_3$ then $P_1$ and $P_2$ are themselves of equal area. If each of two polygons is of equal content to a third, then they are themselves of equal content.

**Lean reading.** `theorem24_area`, `theorem24_content`, for arbitrary sets (polygons in the
hypotheses). Hilbert's proof of the first part is formalized: the two decompositions of `P₃` are
refined by cutting each triangle of one by the side lines of the other (`Areas.cutAll`) into
triangles each lying in a triangle of the second (`Areas.common_refinement`); the pieces are
carried to `P₁` and `P₂` by the isometries that map the triangles of `P₃` to their congruent
partners (`Areas.pullback`; congruent triangles are related by an isometry, `Areas.exists_iso`).
That the pieces lying in a triangle of the second decomposition cover it needs a closure argument
(`Areas.Tr.mem_cover_of_int_cover`) which Hilbert's "evidently" passes over. The second part
"follows without difficulty" only after a further idea: the polygons added to `P₃` in the two
hypotheses may overlap; one replaces them by congruent copies placed far away (translations,
`Areas.far_obst`), which requires the first part, and combines (`Areas.KEqContent.trans`).

**Status.** proved
-/

/-- **Theorem 24**, first part. -/
theorem theorem24_area {S₁ S₂ S₃ : Set P} (h₁ : EqualArea (L := L) S₁ S₃)
    (h₂ : EqualArea (L := L) S₂ S₃) : EqualArea (L := L) S₁ S₂ := by
  by_cases hax : Nonempty (Pas.Axes P L)
  · obtain ⟨ax⟩ := hax
    rw [equalArea_iff ax] at h₁ h₂ ⊢
    exact KEqArea.trans h₁ h₂
  · obtain ⟨l₁, -, d₁, -, -⟩ := h₁
    obtain ⟨l₂, -, d₂, -, -⟩ := h₂
    have e₁ := nil_of_no_axes hax d₁
    have e₂ := nil_of_no_axes hax d₂
    subst e₁ e₂
    exact ⟨[], [], d₁, d₂, List.Forall₂.nil⟩

/-- **Theorem 24**, second part. -/
theorem theorem24_content {S₁ S₂ S₃ : Set P} (h₁ : EqualContent (L := L) S₁ S₃)
    (h₂ : EqualContent (L := L) S₂ S₃) : EqualContent (L := L) S₁ S₂ := by
  obtain ⟨_, _, _, _, ⟨l, hl, d⟩, _⟩ := id h₁
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil l hl
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) (d.1 t ht).2
  rw [equalContent_iff ax] at h₁ h₂ ⊢
  exact KEqContent.trans h₁ h₂

end Section18

section Terms

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P]

/-!
## [s18.terms] Rectangle, base and height

*(§ 18)*

> We define, in the usual manner, the terms: *rectangle*, *base* and *height of a parallelogram*, *base* and *height of a triangle*.

**Lean reading.** `IsParallelogram A B C D`: `A`, `B`, `C` are not collinear and the lines `AB`,
`DC` and the lines `AD`, `BC` have no common point (the opposite sides lie on parallel lines);
`ParRegion A B C D`: its region, the triangles `ABC` and `ACD` (the diagonal `AC`).
`IsRectangle A B C D`: a parallelogram with a right angle at `B`. `IsFoot A B C F`: `F` is the
**foot of the perpendicular** from `A` to the line `BC`: `F` lies on `BC` and makes a right angle
`∠AFX` with some other point `X` of `BC`. The **base** of the triangle `ABC` is a side, say `BC`,
its **height** (altitude) the segment `AF` with `IsFoot A B C F`; the base of the parallelogram
`ABCD` is `AB`, its height `DF` with `IsFoot D A B F`. "Equal bases and equal heights" are
congruent segments. The feet exist (`exists_foot`) and all feet give congruent heights
(`len_mul_foot` determines their lengths).

**Status.** definition
-/

/-- `F` is the **foot of the perpendicular** from `A` to the line `BC`. -/
def IsFoot (A B C F : P) : Prop :=
  Collinear (Line := L) B C F ∧ ∃ X : P, Collinear (Line := L) B C X ∧ X ≠ F ∧
    IsRightAngle (L := L) A F X

/-- `ABCD` is a **parallelogram**. -/
def IsParallelogram (A B C D : P) : Prop :=
  ¬Collinear (Line := L) A B C ∧ (¬∃ X : P, Collinear (Line := L) A B X ∧ Collinear (Line := L) D C X) ∧
    ¬∃ X : P, Collinear (Line := L) A D X ∧ Collinear (Line := L) B C X

/-- The region of the parallelogram `ABCD`. -/
def ParRegion (A B C D : P) : Set P := TriRegion ⟨A, B, C⟩ ∪ TriRegion ⟨A, C, D⟩

/-- `ABCD` is a **rectangle**. -/
def IsRectangle (A B C D : P) : Prop :=
  IsParallelogram (L := L) A B C D ∧ IsRightAngle (L := L) A B C

end Terms

/-! ### Proof infrastructure: measures, parallelograms and feet in co-ordinates -/

section MeasureDefs

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]

open Classical in
/-- The chosen foot of the perpendicular from `A` to `BC` (`A` if there is none). -/
noncomputable def foot (A B C : P) : P :=
  if h : ∃ F, IsFoot (L := L) A B C F then h.choose else A

end MeasureDefs


section Infra19

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Pas.Axes P L)

theorem Areas.img_union (S T : Set P) (p : Pas.G ax × Pas.G ax) :
    Areas.img ax (S ∪ T) p ↔ Areas.img ax S p ∨ Areas.img ax T p := by
  obtain ⟨X, rfl⟩ := Areas.co_surj ax p
  rw [Areas.img_iff, Areas.img_iff, Areas.img_iff]; rfl

/-- The measure of a triangle in co-ordinates. -/
theorem kmeasure_tri {t : Tri P} (ht : t.Nd (L := L)) :
    kmeasure (Areas.img ax (TriRegion t)) = |(Areas.Tri.co ax t).D| / 2 := by
  have h := (isDecomposition_iff ax).1 (isDecomposition_single' ht)
  rw [kmeasure_of_decS h]
  simp

/-- The foot of a perpendicular exists. -/
theorem exists_foot (ax : Pas.Axes P L) {A B C : P} (h : Tri.Nd (L := L) ⟨A, B, C⟩) :
    ∃ F, IsFoot (L := L) A B C F := by
  obtain ⟨hab, hcb, hac⟩ := Pas.nc_ne ax h.1
  obtain ⟨F, X, h1, h2, h3, h4⟩ := Areas.foot_exists (L := L) (Ne.symm hcb)
    (fun hc => h.1 (by obtain ⟨l, h1, h2, h3⟩ := hc; exact ⟨l, h3, h1, h2⟩))
  exact ⟨F, h1, X, h2, h3, h4⟩

/-- Base times height in co-ordinates. -/
theorem len_mul_foot {A B C F : P} (h : IsFoot (L := L) A B C F) :
    Pas.len ax B C * Pas.len ax A F = |det3 (Areas.co ax B) (Areas.co ax C) (Areas.co ax A)| := by
  obtain ⟨h1, X, h2, h3, h4⟩ := h
  exact Areas.len_mul_len_foot ax h1 h2 h3 h4

/-- **Parallelograms in co-ordinates**: `ABCD` is a parallelogram iff `ABC` is a triangle and
`C = D + (B - A)`. -/
theorem parallelogram_iff {A B C D : P} :
    IsParallelogram (L := L) A B C D ↔ ¬Collinear (Line := L) A B C ∧
      Areas.co ax C = par4 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D) := by
  set a := Areas.co ax A
  set b := Areas.co ax B
  set c := Areas.co ax C
  set d := Areas.co ax D
  have col := fun X Y Z : P => Areas.collinear_iff_det3 (L := L) ax (X := X) (Y := Y) (Z := Z)
  constructor
  · rintro ⟨hn, h1, h2⟩
    refine ⟨hn, ?_⟩
    have hd : det3 a b d ≠ 0 := by
      intro e
      exact h1 ⟨D, (col A B D).2 e, (col D C D).2 (by unfold det3; ring)⟩
    have hcr1 : (b.1 - a.1) * (c.2 - d.2) - (b.2 - a.2) * (c.1 - d.1) = 0 := by
      by_contra hne
      have hden : det3 d c a - det3 d c b ≠ 0 := by
        intro e; apply hne; unfold det3 at e; linear_combination e
      obtain ⟨X, hX⟩ := Areas.co_surj ax (lerp (det3 d c a / (det3 d c a - det3 d c b)) a b)
      apply h1
      refine ⟨X, (col A B X).2 ?_, (col D C X).2 ?_⟩
      · show det3 a b (Areas.co ax X) = 0
        rw [hX]; unfold det3 lerp; ring
      · show det3 d c (Areas.co ax X) = 0
        rw [hX]; exact det3_cross d c a b hden
    have hcr2 : (d.1 - a.1) * (c.2 - b.2) - (d.2 - a.2) * (c.1 - b.1) = 0 := by
      by_contra hne
      have hden : det3 b c a - det3 b c d ≠ 0 := by
        intro e; apply hne; unfold det3 at e; linear_combination e
      obtain ⟨X, hX⟩ := Areas.co_surj ax (lerp (det3 b c a / (det3 b c a - det3 b c d)) a d)
      apply h2
      refine ⟨X, (col A D X).2 ?_, (col B C X).2 ?_⟩
      · show det3 a d (Areas.co ax X) = 0
        rw [hX]; unfold det3 lerp; ring
      · show det3 b c (Areas.co ax X) = 0
        rw [hX]; exact det3_cross b c a d hden
    have e1 : (c.1 - b.1 - d.1 + a.1) * det3 a b d = 0 := by
      unfold det3; linear_combination (d.1 - a.1) * hcr1 - (b.1 - a.1) * hcr2
    have e2 : (c.2 - b.2 - d.2 + a.2) * det3 a b d = 0 := by
      unfold det3; linear_combination (d.2 - a.2) * hcr1 - (b.2 - a.2) * hcr2
    have f1 := (mul_eq_zero.1 e1).resolve_right hd
    have f2 := (mul_eq_zero.1 e2).resolve_right hd
    simp only [par4]
    exact Prod.ext (by simp only; linarith) (by simp only; linarith)
  · rintro ⟨hn, hc⟩
    have hd : det3 a b d ≠ 0 := by
      intro e; apply hn; rw [col A B C]
      show det3 a b c = 0
      rw [hc]; simp only [par4]; unfold det3 at e ⊢; linear_combination e
    refine ⟨hn, ?_, ?_⟩
    · rintro ⟨X, hX1, hX2⟩
      rw [col] at hX1 hX2
      apply hd
      change det3 d c (Areas.co ax X) = 0 at hX2
      change det3 a b (Areas.co ax X) = 0 at hX1
      rw [hc] at hX2
      simp only [par4] at hX2
      unfold det3 at hX1 hX2 ⊢
      linear_combination hX1 - hX2
    · rintro ⟨X, hX1, hX2⟩
      rw [col] at hX1 hX2
      apply hd
      change det3 a d (Areas.co ax X) = 0 at hX1
      change det3 b c (Areas.co ax X) = 0 at hX2
      rw [hc] at hX2
      simp only [par4] at hX2
      unfold det3 at hX1 hX2 ⊢
      linear_combination hX2 - hX1

/-- The two triangles of a parallelogram, in co-ordinates. -/
theorem parallelogram_decomposition {A B C D : P} (h : IsParallelogram (L := L) A B C D) :
    IsDecomposition (L := L) (ParRegion A B C D) [⟨A, B, C⟩, ⟨A, C, D⟩] ∧
      kmeasure (Areas.img ax (ParRegion A B C D)) =
        |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D)| := by
  obtain ⟨hn, hc⟩ := (parallelogram_iff ax).1 h
  have hd : det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D) ≠ 0 := by
    intro e; apply hn; rw [Areas.collinear_iff_det3 ax, hc]
    simp only [par4]; unfold det3 at e ⊢; linear_combination e
  have dK := decS_parReg hd
  rw [← hc] at dK
  have dP : DecS (Areas.img ax (ParRegion A B C D))
      ([(⟨A, B, C⟩ : Tri P), ⟨A, C, D⟩].map (Areas.Tri.co ax)) := by
    refine dK.congr (fun p => ?_)
    have n1 : (Tri.mk A B C).Nd (L := L) := (Areas.nd_iff ax).2 (dK.1 _ List.mem_cons_self)
    have n2 : (Tri.mk A C D).Nd (L := L) :=
      (Areas.nd_iff ax).2 (dK.1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [ParRegion, Areas.img_union, Areas.img_triRegion ax n1, Areas.img_triRegion ax n2]
    rfl
  refine ⟨(isDecomposition_iff ax).2 dP, ?_⟩
  rw [kmeasure_of_decS dP]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  show (|det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C)| +
    |det3 (Areas.co ax A) (Areas.co ax C) (Areas.co ax D)|) / 2 = _
  rw [hc]
  have e1 : det3 (Areas.co ax A) (Areas.co ax B)
      (par4 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D)) =
      det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D) := by
    simp only [par4, det3]; ring
  have e2 : det3 (Areas.co ax A) (par4 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D))
      (Areas.co ax D) = det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D) := by
    simp only [par4, det3]; ring
  rw [e1, e2]; ring

/-- A point with the co-ordinates of the midpoint of `XY` is the midpoint. -/
theorem midpoint_of_co {X Y M : P} (hXY : X ≠ Y)
    (h : Areas.co ax M = lerp (1 / 2) (Areas.co ax X) (Areas.co ax Y)) :
    Between X M Y ∧ SegCong X M M Y := by
  have hb : Between X M Y :=
    (Areas.between_iff_co ax).2 ⟨hXY, 1 / 2, by norm_num, by norm_num, h⟩
  refine ⟨hb, (Pas.len_eq_iff ax (ne12_of_between (Line := L) hb)
    (ne23_of_between (Line := L) hb)).1 (Areas.len_eq_of_sq ax ?_)⟩
  rw [Areas.len_sq_co, Areas.len_sq_co, h]
  simp only [lerp]; ring

/-- For a right angle at `O`, `|(A - O) × (B - O)| = OA · OB`. -/
theorem abs_det_of_right {A O B : P} (h : IsRightAngle (L := L) A O B) :
    |det3 (Areas.co ax O) (Areas.co ax A) (Areas.co ax B)| = Pas.len ax O A * Pas.len ax O B := by
  obtain ⟨-, -, hd⟩ := (Areas.isRightAngle_iff_dot ax).1 h
  simp only [Areas.dotc] at hd
  have key : (Pas.len ax O A * Pas.len ax O B) * (Pas.len ax O A * Pas.len ax O B) =
      |det3 (Areas.co ax O) (Areas.co ax A) (Areas.co ax B)| *
        |det3 (Areas.co ax O) (Areas.co ax A) (Areas.co ax B)| := by
    rw [abs_mul_abs_self]
    have : (Pas.len ax O A * Pas.len ax O B) * (Pas.len ax O A * Pas.len ax O B) =
        (Pas.len ax O A * Pas.len ax O A) * (Pas.len ax O B * Pas.len ax O B) := by ring
    rw [this, Areas.len_sq_co, Areas.len_sq_co]
    unfold det3
    linear_combination (((Areas.co ax A).1 - (Areas.co ax O).1) * ((Areas.co ax B).1 -
      (Areas.co ax O).1) + ((Areas.co ax A).2 - (Areas.co ax O).2) * ((Areas.co ax B).2 -
      (Areas.co ax O).2)) * hd
  exact ((mul_self_inj (mul_nonneg (Pas.len_nonneg ax O A) (Pas.len_nonneg ax O B))
    (abs_nonneg _)).1 key).symm

/-- The region of a parallelogram in co-ordinates. -/
theorem img_parRegion {A B C D : P} (h : IsParallelogram (L := L) A B C D)
    (p : Pas.G ax × Pas.G ax) :
    Areas.img ax (ParRegion A B C D) p ↔ parReg (Areas.co ax A) (Areas.co ax B)
      (par4 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D)) (Areas.co ax D) p := by
  obtain ⟨d, -⟩ := parallelogram_decomposition ax h
  have n1 : (Tri.mk A B C).Nd (L := L) := d.1 _ (by simp)
  have n2 : (Tri.mk A C D).Nd (L := L) := d.1 _ (by simp)
  obtain ⟨-, hc⟩ := (parallelogram_iff ax).1 h
  rw [ParRegion, Areas.img_union, Areas.img_triRegion ax n1, Areas.img_triRegion ax n2]
  simp only [Areas.Tri.co, hc]
  exact Iff.rfl

/-- Congruent segments have equal squared distances in co-ordinates. -/
theorem sqd_eq_of_segCong {X Y X' Y' : P} (hXY : X ≠ Y) (hXY' : X' ≠ Y')
    (h : SegCong X Y X' Y') :
    sqd (Areas.co ax X) (Areas.co ax Y) = sqd (Areas.co ax X') (Areas.co ax Y') := by
  have hl := (Pas.len_eq_iff ax hXY hXY').2 h
  unfold sqd; rw [← Areas.len_sq_co, ← Areas.len_sq_co, hl]

end Infra19


section Section19

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

theorem ne_of_isFoot {A B C F : P} (h : IsFoot (L := L) A B C F) (ax : Pas.Axes P L) :
    A ≠ F := by
  obtain ⟨-, X, -, -, hr⟩ := h
  exact (Pas.nc_ne ax hr.1).1

theorem axes_of_isFoot {A B C F : P} (h : IsFoot (L := L) A B C F) : Nonempty (Pas.Axes P L) := by
  obtain ⟨-, X, -, hXF, -⟩ := h
  exact Areas.ax_of_ne hXF

/-!
## [th.25] Theorem 25

*(§ 19)*

> Two parallelograms having equal bases and equal altitudes are also of equal content.

**Lean reading.** `theorem25`: for parallelograms `ABCD`, `A'B'C'D'` (`IsParallelogram`) with
bases `AB ≡ A'B'` and heights `DF ≡ D'F'` (`IsFoot D A B F`, `IsFoot D' A' B' F'`), the regions
`ParRegion A B C D` and `ParRegion A' B' C' D'` are of equal content. "The well known reasoning
of Euclid" (I 35, Fig. 30) treats parallelograms on the *same* base between the same parallels:
adding to `ABCD` and to `ABC'D'` two congruent triangles gives one quadrilateral
(`Areas.euclid_K`). For two arbitrary parallelograms, which Hilbert's statement covers, Euclid's
argument needs a motion first, which Hilbert passes over: the proof
(`Areas.parallelograms_eqContent`) carries `A'B'C'D'` by an isometry of the co-ordinate plane (a
motion: congruent triangles go to congruent triangles) onto a parallelogram `ABC''X` on the base
`AB` and on the side of `D`, which is of equal area with `A'B'C'D'`; equal heights put `X` on the
parallel `DC`, Euclid's argument makes `ABCD` and `ABC''X` of equal content, and Theorem 24
combines. No measure of area is used.

**Status.** proved
-/

/-- **Theorem 25.** -/
theorem theorem25 {A B C D A' B' C' D' F F' : P} (h : IsParallelogram (L := L) A B C D)
    (h' : IsParallelogram (L := L) A' B' C' D') (hb : SegCong A B A' B')
    (hF : IsFoot (L := L) D A B F) (hF' : IsFoot (L := L) D' A' B' F') (hh : SegCong D F D' F') :
    EqualContent (L := L) (ParRegion A B C D) (ParRegion A' B' C' D') := by
  obtain ⟨ax⟩ := axes_of_isFoot hF
  obtain ⟨hn, hc⟩ := (parallelogram_iff ax).1 h
  have hD : det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D) ≠ 0 := by
    intro e; apply hn; rw [Areas.collinear_iff_det3 ax, hc]
    simp only [par4]; unfold det3 at e ⊢; linear_combination e
  obtain ⟨hab, -, -⟩ := Pas.nc_ne ax h.1
  obtain ⟨hab', -, -⟩ := Pas.nc_ne ax h'.1
  rw [equalContent_iff ax]
  refine (parallelograms_eqContent hD (sqd_eq_of_segCong ax hab hab' hb) ?_).congr
    (fun p => (img_parRegion ax h p).symm) (fun p => (img_parRegion ax h' p).symm)
  rw [← len_mul_foot ax hF, ← len_mul_foot ax hF', (Pas.len_eq_iff ax hab hab').2 hb,
    (Pas.len_eq_iff ax (ne_of_isFoot hF ax) (ne_of_isFoot hF' ax)).2 hh]

/-!
## [th.26] Theorem 26

*(§ 19)*

> Any triangle $ABC$ is always of equal area to a certain parallelogram having an equal base and an altitude half as great as that of the triangle. … Proof. Bisect $AC$ in $D$ and $BC$ in $E$, and extend the line $DE$ to $F$, making $EF$ equal to $DE$. Then, the triangles $DEC$ and $FBE$ are congruent to each other, and, consequently, the triangle $ABC$ and the parallelogram $ABFD$ are of equal area.

**Lean reading.** `theorem26`: for a triangle `ABC` there are `D`, `E`, `F` as in the proof (`D`
the midpoint of `AC`, `E` of `BC`, `E` the midpoint of `DF`) such that `ABFD` is a parallelogram
with the base `AB` of the triangle, `TriRegion ABC` and `ParRegion A B F D` are of equal area,
and the height of the parallelogram is half that of the triangle: for the feet `F₁` of `D` and
`F₂` of `C` on `AB`, `CF₂` is the sum (`Pas.SegSum`, § 15) of `DF₁` and `DF₁`. The proof is
Hilbert's (`Areas.th26_K`): the triangle is decomposed into `ABE`, `ECD`, `EDA`, the
parallelogram into `ABE`, `EBF`, `EDA`, and `ECD ≡ EBF`. Hilbert's "`DEC` and `FBE` are
congruent" holds with the correspondence `D ↦ F`, `E ↦ E`, `C ↦ B` (the half-turn about `E`);
read with the vertices in the order printed (`D ↦ F`, `E ↦ B`, `C ↦ E`) it would be false
(`DE ≡ FB` fails in general). That the triangle `ABC` is
"composed" of the quadrilateral `ABED` and `DEC`, and the parallelogram of `ABED` and `FBE`,
needs the two diagonals of the quadrilateral `ABFE` (`Areas.diag_swap`).

**Status.** proved
-/

/-- **Theorem 26.** -/
theorem theorem26 {A B C : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩) :
    ∃ D E F : P, (Between A D C ∧ SegCong A D D C) ∧ (Between B E C ∧ SegCong B E E C) ∧
      (Between D E F ∧ SegCong D E E F) ∧ IsParallelogram (L := L) A B F D ∧
      EqualArea (L := L) (TriRegion ⟨A, B, C⟩) (ParRegion A B F D) ∧
      ∀ F₁ F₂ : P, IsFoot (L := L) D A B F₁ → IsFoot (L := L) C A B F₂ →
        Pas.SegSum D F₁ D F₁ C F₂ := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  have hD : det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C) ≠ 0 := by
    have h := (Areas.nd_iff ax).1 ht
    exact h
  set a := Areas.co ax A
  set b := Areas.co ax B
  set c := Areas.co ax C
  obtain ⟨hab, hcb, hac⟩ := Pas.nc_ne ax ht.1
  obtain ⟨D, hDd⟩ := Areas.co_surj ax (lerp (1 / 2) c a)
  obtain ⟨E, hEe⟩ := Areas.co_surj ax (lerp (1 / 2) b c)
  obtain ⟨F, hFf⟩ := Areas.co_surj ax (refl2 (lerp (1 / 2) b c) (lerp (1 / 2) c a))
  obtain ⟨d1, d2, d3⟩ := th26_K hD
  have hdet_d : det3 a b (Areas.co ax D) = det3 a b c / 2 := by
    rw [hDd]; simp only [lerp, det3]; ring
  have hfpar : Areas.co ax F = par4 a b (Areas.co ax D) := by
    rw [hFf, hDd]; simp only [refl2, par4, lerp]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring
  have nABF : ¬Collinear (Line := L) A B F := by
    rw [Areas.collinear_iff_det3 ax, hfpar]
    intro e
    apply hD
    have : det3 a b (par4 a b (Areas.co ax D)) = det3 a b (Areas.co ax D) := by
      simp only [par4, det3]; ring
    rw [this, hdet_d] at e
    linarith [e]
  have hpar : IsParallelogram (L := L) A B F D := (parallelogram_iff ax).2 ⟨nABF, hfpar⟩
  have mD : Areas.co ax D = lerp (1 / 2) (Areas.co ax A) (Areas.co ax C) := by
    rw [hDd]; simp only [lerp]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring
  refine ⟨D, E, F, midpoint_of_co ax hac mD,
    midpoint_of_co ax (Ne.symm hcb) hEe, midpoint_of_co ax ?_ ?_, hpar, ?_, ?_⟩
  · intro e
    apply hab
    apply Areas.co_inj ax
    have h' : Areas.co ax D = Areas.co ax F := by rw [e]
    rw [hDd, hFf] at h'
    simp only [refl2, lerp] at h'
    have h1 := congrArg Prod.fst h'
    have h2 := congrArg Prod.snd h'
    simp only at h1 h2
    exact Prod.ext (by linarith) (by linarith)
  · rw [hEe, hDd, hFf]; simp only [refl2, lerp]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring
  · rw [equalArea_iff ax]
    obtain ⟨nABFt, -⟩ := (parallelogram_decomposition ax hpar).1
    have n1 : (Tri.mk A B F).Nd (L := L) := nABFt _ (by simp)
    have n2 : (Tri.mk A F D).Nd (L := L) := nABFt _ (by simp)
    refine ⟨_, _, d1.congr (fun p => ?_), d2.congr (fun p => ?_), d3⟩
    · rw [Areas.img_triRegion ax ht]
      exact Iff.rfl
    · rw [ParRegion, Areas.img_union, Areas.img_triRegion ax n1, Areas.img_triRegion ax n2]
      simp only [Areas.Tri.co, hDd, hFf]
      exact Iff.rfl
  · intro F₁ F₂ h1 h2
    have e1 := len_mul_foot ax h1
    have e2 := len_mul_foot ax h2
    have hDF := ne_of_isFoot h1 ax
    have hCF := ne_of_isFoot h2 ax
    rw [segSum_iff_len ax hDF hDF hCF]
    have hpos := Pas.len_pos ax hab
    apply mul_left_cancel₀ hpos.ne'
    rw [mul_add, e1, e2]
    change |det3 a b c| = |det3 a b (Areas.co ax D)| + |det3 a b (Areas.co ax D)|
    rw [hdet_d, abs_div, abs_two]; ring

/-!
## [th.27] Theorem 27

*(§ 19)*

> From theorems 25 and 26, we have at once, by aid of theorem 24, the following proposition. Theorem 27. Two triangles having equal bases and equal altitudes have also equal content.

**Lean reading.** `theorem27`: for triangles `ABC`, `A'B'C'` with bases `BC ≡ B'C'` and heights
`AF ≡ A'F'` (`IsFoot`), `TriRegion ABC` and `TriRegion A'B'C'` are of equal content. The proof is
Hilbert's: by Theorem 26 (`theorem26` for the triangles `BCA`, `B'C'A'`, `th26_base`) each
triangle is of equal area with a parallelogram on its base whose height `DF₁` is half the height
`AF`; halves of congruent segments are congruent (lengths in the field of segments), so Theorem 25
makes the two parallelograms of equal content, and Theorem 24 (`theorem24_content`) combines. One
tacit step: polygons of equal area are of equal content (`equalContent_of_equalArea`; Hilbert's
definition of equal content requires *adding* polygons, and one adds a congruent copy placed far
away).

**Status.** proved
-/

/-- **Polygons of equal area are of equal content.** -/
theorem equalContent_of_equalArea {S T : Set P} (hS : IsPolyRegion (L := L) S)
    (h : EqualArea (L := L) S T) : EqualContent (L := L) S T := by
  obtain ⟨l, hl, d⟩ := id hS
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil l hl
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) (d.1 t ht).2
  rw [equalContent_iff ax]
  exact ((equalArea_iff ax).1 h).toContent ((isPolygon_iff ax).1 hS)

theorem equalContent_symm {S T : Set P} (h : EqualContent (L := L) S T) :
    EqualContent (L := L) T S := by
  obtain ⟨_, _, _, _, ⟨l, hl, d⟩, _⟩ := id h
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil l hl
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) (d.1 t ht).2
  rw [equalContent_iff ax] at h ⊢
  exact h.symm

theorem triRegion_rot_eq {A B C : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩) :
    TriRegion (⟨B, C, A⟩ : Tri P) = TriRegion ⟨A, B, C⟩ := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  have ht' : Tri.Nd (L := L) ⟨B, C, A⟩ := by
    rw [Areas.nd_iff ax] at ht ⊢; exact (Tr.nd_rot (t := Areas.Tri.co ax ⟨A, B, C⟩)).2 ht
  ext X
  rw [← Areas.img_iff ax X, ← Areas.img_iff ax X, Areas.img_triRegion ax ht',
    Areas.img_triRegion ax ht]
  exact Tr.mem_rot (t := Areas.Tri.co ax ⟨A, B, C⟩)

/-- Theorem 26 for the base `BC`: the parallelogram, half the height, and the equal content. -/
theorem th26_base {A B C F : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩) (hF : IsFoot (L := L) A B C F)
    (ax : Pas.Axes P L) :
    ∃ D G F₁ : P, IsParallelogram (L := L) B C G D ∧ IsFoot (L := L) D B C F₁ ∧
      Pas.len ax A F = Pas.len ax D F₁ + Pas.len ax D F₁ ∧
      EqualContent (L := L) (TriRegion ⟨A, B, C⟩) (ParRegion B C G D) := by
  have ht' : Tri.Nd (L := L) ⟨B, C, A⟩ := by
    rw [Areas.nd_iff ax] at ht ⊢; exact (Tr.nd_rot (t := Areas.Tri.co ax ⟨A, B, C⟩)).2 ht
  obtain ⟨D, -, G, -, -, -, hpar, harea, hheight⟩ := theorem26 ht'
  obtain ⟨hn, hc⟩ := (parallelogram_iff ax).1 hpar
  have hnD : ¬Collinear (Line := L) D B C := by
    intro e; apply hn
    rw [Areas.collinear_iff_det3 ax] at e ⊢
    rw [hc]; simp only [par4]; unfold det3 at e ⊢; linear_combination e
  have hDB : D ≠ B := (Pas.nc_ne ax hnD).1
  obtain ⟨F₁, hF₁⟩ := exists_foot ax (A := D) (B := B) (C := C) ⟨hnD, hDB⟩
  have hs := hheight F₁ F hF₁ hF
  rw [segSum_iff_len ax (ne_of_isFoot hF₁ ax) (ne_of_isFoot hF₁ ax) (ne_of_isFoot hF ax)] at hs
  refine ⟨D, G, F₁, hpar, hF₁, hs, ?_⟩
  rw [← triRegion_rot_eq ht]
  exact equalContent_of_equalArea ⟨_, by simp, isDecomposition_single' ht'⟩ harea

/-- **Theorem 27.** -/
theorem theorem27 {A B C A' B' C' F F' : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩)
    (ht' : Tri.Nd (L := L) ⟨A', B', C'⟩) (hb : SegCong B C B' C') (hF : IsFoot (L := L) A B C F)
    (hF' : IsFoot (L := L) A' B' C' F') (hh : SegCong A F A' F') :
    EqualContent (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A', B', C'⟩) := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  obtain ⟨D, G, F₁, hpar, hF₁, hl, h1⟩ := th26_base ht hF ax
  obtain ⟨D', G', F₁', hpar', hF₁', hl', h3⟩ := th26_base ht' hF' ax
  have hAF : Pas.len ax A F = Pas.len ax A' F' :=
    (Pas.len_eq_iff ax (ne_of_isFoot hF ax) (ne_of_isFoot hF' ax)).2 hh
  have hDF : SegCong D F₁ D' F₁' := by
    refine (Pas.len_eq_iff ax (ne_of_isFoot hF₁ ax) (ne_of_isFoot hF₁' ax)).1 ?_
    linarith
  have h2 := theorem25 hpar hpar' hb hF₁ hF₁' hDF
  exact theorem24_content (theorem24_content h1 (equalContent_symm h2)) h3

/-!
## [s19.usual_demonstration] Equal bases and altitudes need not give equal area

*(§ 19)*

> It is usual to show that two triangles having equal bases and equal altitudes are always of equal area. It is to be remarked, however, that *this demonstration cannot be made without the aid of the axiom of Archimedes.* In fact, we may easily construct in our non-archimedean geometry … two triangles so that they shall have equal bases and equal altitudes and, consequently, by theorem 27, must be of equal content, but which are not, however, of equal area. As such an example, we may take the two triangles $ABC$ and $ABD$ having each the base $AB=1$ and the altitude $1$, where the vertex of the first triangle is situated perpendicularly above $A$, and in the second triangle the foot $F$ of the perpendicular let fall from the vertex $D$ upon the base is so situated that $AF=t$.

**Lean reading.** `nonarch_triangles`: in any plane geometry (I 1–2, II–IV) whose field of
segments `Pas.G ax` contains an element `T` larger than every natural number, the triangles `ABC`,
`ABD` with the co-ordinates `A = (0, 0)`, `B = (1, 0)`, `C = (0, 1)`, `D = (T, 1)` have the
common base `AB`, the heights `AC ≡ FD` (`A` is the foot of `C`, `F = (T, 0)` the foot of `D`,
`AF = T`), are of equal content (Theorem 27) and are **not** of equal area. Proof
(`Areas.sqd_le_of_kEqArea`): every triangle of a decomposition of `ABC` has all squared
distances `≤ 2`, congruent triangles too, so `n` of them cannot cover the segment `AD`, whose
squared length `T² + 1` exceeds `2n²` (pigeonhole on `n + 1` equally spaced points of `AD`).
`nonarchimedean_example`: Hilbert's example in the non-archimedean geometry `Coord OmegaT 2` of
§ 12 (an instance of I 1–2, II–IV in which Archimedes's axiom fails, `omegaT_plane_model` in
Independence.lean): `AB`, `AC`, `FD` congruent to the unit segment `0e`, `AF` congruent to the
segment `0(te)`, equal content, not equal area. The positive half ("it is usual to show"), that
*with* Archimedes's axiom triangles with equal bases and altitudes are of equal area, is unit
`s19.archimedes_equal_area`.

**Status.** proved
-/

theorem len_eq_of_sqd (ax : Pas.Axes P L) {X Y : P} {g : Pas.G ax} (hg : 0 ≤ g)
    (h : sqd (Areas.co ax X) (Areas.co ax Y) = g * g) : Pas.len ax X Y = g :=
  (mul_self_inj (Pas.len_nonneg ax X Y) hg).1 (by rw [Areas.len_sq_co]; exact h)

/-- **Equal bases and altitudes without equal area** (in a geometry whose field of segments has
an element `T` larger than every natural number): the triangles with the co-ordinates
`(0, 0), (1, 0), (0, 1)` and `(0, 0), (1, 0), (T, 1)`. -/
theorem nonarch_triangles (ax : Pas.Axes P L) {T : Pas.G ax} (hT : ∀ n : ℕ, (n : Pas.G ax) < T) :
    ∃ A B C D F : P, IsFoot (L := L) C A B A ∧ IsFoot (L := L) D A B F ∧
      Pas.len ax A B = 1 ∧ Pas.len ax A C = 1 ∧ Pas.len ax F D = 1 ∧ Pas.len ax A F = T ∧
      EqualContent (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A, B, D⟩) ∧
      ¬EqualArea (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A, B, D⟩) := by
  have hT0 : 0 < T := by have := hT 0; simpa using this
  obtain ⟨A, hA⟩ := Areas.co_surj ax (0, 0)
  obtain ⟨B, hB⟩ := Areas.co_surj ax (1, 0)
  obtain ⟨C, hC'⟩ := Areas.co_surj ax (0, 1)
  obtain ⟨D, hD⟩ := Areas.co_surj ax (T, 1)
  obtain ⟨F, hF⟩ := Areas.co_surj ax (T, 0)
  have col : ∀ X Y Z : P, det3 (Areas.co ax X) (Areas.co ax Y) (Areas.co ax Z) = 0 →
      Collinear (Line := L) X Y Z := fun X Y Z h => (Areas.collinear_iff_det3 ax).2 h
  have ne : ∀ X Y : P, Areas.co ax X ≠ Areas.co ax Y → X ≠ Y := fun X Y h e => h (by rw [e])
  have hBA : B ≠ A := ne B A (by rw [hB, hA]; simp)
  have hCA : C ≠ A := ne C A (by rw [hC', hA]; simp)
  have hDF : D ≠ F := ne D F (by rw [hD, hF]; simp)
  have hAF : A ≠ F := ne A F (by rw [hA, hF]; simp [hT0.ne])
  have f1 : IsFoot (L := L) C A B A := by
    refine ⟨col A B A (by unfold det3; ring), B, col A B B (by unfold det3; ring), hBA, ?_⟩
    rw [Areas.isRightAngle_iff_dot ax]
    refine ⟨hCA, hBA, ?_⟩
    simp only [Areas.dotc, hA, hB, hC']; ring
  have f2 : IsFoot (L := L) D A B F := by
    refine ⟨col A B F (by rw [hA, hB, hF]; unfold det3; ring), A,
      col A B A (by unfold det3; ring), hAF, ?_⟩
    rw [Areas.isRightAngle_iff_dot ax]
    refine ⟨hDF, hAF, ?_⟩
    simp only [Areas.dotc, hA, hD, hF]; ring
  have nd1 : Tri.Nd (L := L) ⟨A, B, C⟩ :=
    ⟨fun h => by
      rw [Areas.collinear_iff_det3 ax, hA, hB, hC'] at h; unfold det3 at h; norm_num at h,
     Ne.symm hBA⟩
  have nd2 : Tri.Nd (L := L) ⟨A, B, D⟩ :=
    ⟨fun h => by
      rw [Areas.collinear_iff_det3 ax, hA, hB, hD] at h; unfold det3 at h; norm_num at h,
     Ne.symm hBA⟩
  refine ⟨A, B, C, D, F, f1, f2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact len_eq_of_sqd ax zero_le_one (by rw [hA, hB]; simp only [sqd]; ring)
  · exact len_eq_of_sqd ax zero_le_one (by rw [hA, hC']; simp only [sqd]; ring)
  · exact len_eq_of_sqd ax zero_le_one (by rw [hF, hD]; simp only [sqd]; ring)
  · exact len_eq_of_sqd ax hT0.le (by rw [hA, hF]; simp only [sqd]; ring)
  · rw [equalContent_iff ax]
    refine KEqContent.of_kmeasure
      ((isPolygon_iff ax).1 ⟨_, by simp, isDecomposition_single' nd1⟩)
      ((isPolygon_iff ax).1 ⟨_, by simp, isDecomposition_single' nd2⟩) ?_
    rw [kmeasure_tri ax nd1, kmeasure_tri ax nd2]
    change |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C)| / 2 =
      |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D)| / 2
    rw [hA, hB, hC', hD]; unfold det3; norm_num
  · rw [equalArea_iff ax]
    rintro ⟨l, m, hl, hm, hc⟩
    have hl' := hl.congr (fun p => Areas.img_triRegion ax nd1 p)
    have hseg : ∀ s : Pas.G ax, 0 ≤ s → s ≤ 1 →
        Areas.img ax (TriRegion ⟨A, B, D⟩) (lerp s (Areas.co ax A) (Areas.co ax D)) := by
      intro s h0 h1
      rw [Areas.img_triRegion ax nd2, Tr.mem_iff_bary ((Areas.nd_iff ax).1 nd2)]
      refine ⟨1 - s, 0, s, by linarith, le_rfl, h0, by ring, ?_⟩
      simp only [comb, lerp, Areas.Tri.co]
      refine Prod.ext ?_ ?_ <;> simp only <;> ring
    have hnd := (Areas.nd_iff ax).1 nd1
    have key := sqd_le_of_kEqArea hnd (R := 2)
      (by show sqd (Areas.co ax A) (Areas.co ax B) ≤ 2
          rw [hA, hB]; simp only [sqd]; norm_num)
      (by show sqd (Areas.co ax A) (Areas.co ax C) ≤ 2
          rw [hA, hC']; simp only [sqd]; norm_num)
      (by show sqd (Areas.co ax B) (Areas.co ax C) ≤ 2
          rw [hB, hC']; simp only [sqd]; norm_num)
      hl' hm hc hseg
    rw [hA, hD] at key
    simp only [sqd] at key
    have h2n := hT (2 * m.length)
    push_cast at h2n
    have hpos : (0 : Pas.G ax) ≤ 2 * m.length := by positivity
    have := mul_lt_mul'' h2n h2n hpos hpos
    nlinarith


end Section19

section NonArchModel

theorem len_self' {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) (X : P) :
    Pas.len ax X X = 0 := by
  simp [Pas.len]

/-- **Hilbert's example in the non-archimedean geometry** `Ω(t)²` of § 12 (`Coord OmegaT 2`, an
instance of I 1–2, II–IV in which V fails): triangles `ABC`, `ABD` with `AB ≡ AC ≡ FD ≡` the
unit segment `0e`, `AF ≡` the segment `0(te)`, `A` the foot of `C` and `F` the foot of `D` on
`AB`, of equal content and not of equal area. -/
theorem nonarchimedean_example :
    ∃ A B C D F : Coord OmegaT 2,
      SegCong A B (0 : Coord OmegaT 2) (Coord.pt2 1 0) ∧
      SegCong A C (0 : Coord OmegaT 2) (Coord.pt2 1 0) ∧
      SegCong F D (0 : Coord OmegaT 2) (Coord.pt2 1 0) ∧
      SegCong A F (0 : Coord OmegaT 2) (OmegaT.t • Coord.pt2 1 0) ∧
      IsFoot (L := CoordLine OmegaT 2) C A B A ∧ IsFoot (L := CoordLine OmegaT 2) D A B F ∧
      EqualContent (L := CoordLine OmegaT 2) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A, B, D⟩) ∧
      ¬EqualArea (L := CoordLine OmegaT 2) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A, B, D⟩) := by
  set e : Coord OmegaT 2 := Coord.pt2 1 0 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun (congrArg AffPt.toV h) 0
    simp [he, Coord.pt2] at this
  have key : ∀ x y z : OmegaT, Between (x • e) (y • e) (z • e) ↔
      (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
    intro x y z
    have := sbtw_param_iff he0 x y z (O := 0)
    simp only [add_zero] at this
    exact this
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := CoordLine OmegaT 2) (Ne.symm he0)
  have h1 : Pas.len ax 0 e = 1 := by rw [← hO, ← hE]; exact Pas.len_E ax
  have unit : ∀ k : ℕ, SegCong ((k : OmegaT) • e) (((k + 1 : ℕ) : OmegaT) • e) 0 e := by
    intro k
    rw [Coord.segCong_iff, ← sub_smul, sub_zero]
    push_cast
    rw [add_sub_cancel_left, one_smul]
  have hlen : ∀ k : ℕ, Pas.len ax 0 ((k : OmegaT) • e) = k := by
    intro k
    induction k with
    | zero => simp [len_self']
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [h1]
      · have hb : Between ((0 : OmegaT) • e) ((k : OmegaT) • e) (((k + 1 : ℕ) : OmegaT) • e) :=
          (key _ _ _).2 (Or.inl ⟨by exact_mod_cast hk, by push_cast; linarith⟩)
        rw [zero_smul] at hb
        have hne : (k : OmegaT) • e ≠ ((k + 1 : ℕ) : OmegaT) • e := ne23_of_between hb
        rw [Pas.len_add ax hb, ih,
          (Pas.len_eq_iff ax hne (Ne.symm he0)).2 (unit k), h1]
        push_cast; ring
  set T := Pas.len ax 0 (OmegaT.t • e) with hTdef
  have ht0 : (0 : Coord OmegaT 2) ≠ OmegaT.t • e := by
    intro h
    have hb := (key 0 1 OmegaT.t).2 (Or.inl ⟨one_pos, by
      simpa using OmegaT.natCast_lt_t 1⟩)
    rw [zero_smul, ← h] at hb
    exact not_between_self (Line := CoordLine OmegaT 2) hb
  have hT : ∀ n : ℕ, (n : Pas.G ax) < T := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using Pas.len_pos ax ht0
    · have hb : Between ((0 : OmegaT) • e) ((n : OmegaT) • e) (OmegaT.t • e) :=
        (key _ _ _).2 (Or.inl ⟨by exact_mod_cast hn, OmegaT.natCast_lt_t n⟩)
      rw [zero_smul] at hb
      rw [hTdef, Pas.len_add ax hb, hlen]
      have := Pas.len_pos ax (ne23_of_between (Line := CoordLine OmegaT 2) hb)
      linarith
  obtain ⟨A, B, C, D, F, f1, f2, l1, l2, l3, l4, hc, ha⟩ := nonarch_triangles ax hT
  have ne_of_len : ∀ X Y : Coord OmegaT 2, Pas.len ax X Y ≠ 0 → X ≠ Y := by
    intro X Y h e'; subst e'; exact h (len_self' ax X)
  refine ⟨A, B, C, D, F, ?_, ?_, ?_, ?_, f1, f2, hc, ha⟩
  · exact (Pas.len_eq_iff ax (ne_of_len A B (by rw [l1]; exact one_ne_zero)) (Ne.symm he0)).1
      (by rw [l1, h1])
  · exact (Pas.len_eq_iff ax (ne_of_len A C (by rw [l2]; exact one_ne_zero)) (Ne.symm he0)).1
      (by rw [l2, h1])
  · exact (Pas.len_eq_iff ax (ne_of_len F D (by rw [l3]; exact one_ne_zero)) (Ne.symm he0)).1
      (by rw [l3, h1])
  · have hTpos : 0 < T := by simpa using hT 0
    exact (Pas.len_eq_iff ax (ne_of_len A F (by rw [l4]; exact hTpos.ne')) ht0).1 (by rw [l4])

end NonArchModel

/-!
## [s19.archimedes_equal_area] With Archimedes's axiom, equal bases and altitudes give equal area

*(§ 19)*

> It is usual to show that two triangles having equal bases and equal altitudes are always of equal area. It is to be remarked, however, that *this demonstration cannot be made without the aid of the axiom of Archimedes.*

**Lean reading.** The positive half of the remark: in a plane geometry with all the axioms I–V
(`PlaneGeometry`), two triangles with congruent bases and congruent heights are of equal area
(`archimedes_equal_area`; `archimedesEqualAreaClaim` proves the statement
`ArchimedesEqualAreaClaim`). The usual demonstration is formalized
(`Areas.eqArea_of_base_height`): a congruent copy of the second triangle is placed on the base of
the first, on the side of its vertex (the copy is of equal area, by definition); equal heights put
its vertex on the parallel to the base through the vertex of the first; the vertex is then moved
along this parallel in finitely many steps, each shorter than twice the base, and each step keeps
the area (Theorem 26 twice and Euclid's parallelograms with overlapping tops, decomposed into
three triangles each: `Areas.euclid_area_small`, `Areas.shear_area_small`); Archimedes's axiom,
through the archimedean field of segments (`Pas.archimedean_G`), bounds the number of steps
(`Areas.shear_area`), and Theorem 24 chains them. The negative half (without Archimedes's axiom
the statement fails) is unit `s19.usual_demonstration`.

**Status.** proved
-/

/-- **Claim** (§ 19): with Archimedes's axiom, triangles with equal bases and equal altitudes are of
equal area (proved: `archimedesEqualAreaClaim`). -/
def ArchimedesEqualAreaClaim : Prop :=
  ∀ (P : Type) (L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneGeometry P L → ∀ A B C A' B' C' F F' : P, Tri.Nd (L := L) ⟨A, B, C⟩ →
      Tri.Nd (L := L) ⟨A', B', C'⟩ → SegCong B C B' C' → IsFoot (L := L) A B C F →
      IsFoot (L := L) A' B' C' F' → SegCong A F A' F' →
      EqualArea (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A', B', C'⟩)

/-- **With Archimedes's axiom, triangles with equal bases and equal altitudes are of equal
area.** -/
theorem archimedes_equal_area {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [PlaneGeometry P L] {A B C A' B' C' F F' : P}
    (ht : Tri.Nd (L := L) ⟨A, B, C⟩) (ht' : Tri.Nd (L := L) ⟨A', B', C'⟩)
    (hb : SegCong B C B' C') (hF : IsFoot (L := L) A B C F) (hF' : IsFoot (L := L) A' B' C' F')
    (hh : SegCong A F A' F') :
    EqualArea (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A', B', C'⟩) := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  have : Archimedean (Pas.G ax) := Pas.archimedean_G ax
  obtain ⟨-, hcb, -⟩ := Pas.nc_ne ax ht.1
  obtain ⟨-, hcb', -⟩ := Pas.nc_ne ax ht'.1
  have hl : Pas.len ax B C = Pas.len ax B' C' :=
    (Pas.len_eq_iff ax (Ne.symm hcb) (Ne.symm hcb')).2 hb
  have hh' : |det3 (Areas.co ax B) (Areas.co ax C) (Areas.co ax A)| =
      |det3 (Areas.co ax B') (Areas.co ax C') (Areas.co ax A')| := by
    rw [← len_mul_foot ax hF, ← len_mul_foot ax hF', hl,
      (Pas.len_eq_iff ax (ne_of_isFoot hF ax) (ne_of_isFoot hF' ax)).2 hh]
  have hD : det3 (Areas.co ax B) (Areas.co ax C) (Areas.co ax A) ≠ 0 := by
    have h := (Areas.nd_iff ax).1 ht
    rw [det3_cyc]; exact h
  rw [equalArea_iff ax]
  refine KEqArea.congr ax (eqArea_of_base_height hD
    (sqd_eq_of_segCong ax (Ne.symm hcb) (Ne.symm hcb') hb) hh') (fun p => ?_) (fun p => ?_)
  · rw [Areas.img_triRegion ax ht]; exact Tr.mem_rot (t := Areas.Tri.co ax ⟨A, B, C⟩)
  · rw [Areas.img_triRegion ax ht']; exact Tr.mem_rot (t := Areas.Tri.co ax ⟨A', B', C'⟩)

theorem archimedesEqualAreaClaim : ArchimedesEqualAreaClaim := by
  intro P L _ _ _ _ hG A B C A' B' C' F F' ht ht' hb hF hF' hh
  exact archimedes_equal_area ht ht' hb hF hF' hh

section Section19b

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-!
## [s19.pythagoras] The remaining propositions and the theorem of Pythagoras

*(§ 19)*

> The remaining propositions of elementary geometry concerning the equal content of polygons, and in particular the pythagorean theorem, are all simple consequences of the theorems which we have already given.

**Lean reading.** "The remaining propositions" are not enumerated; the theorem of Pythagoras is
formalized: `pythagoras_content`: if `∠ACB` is a right angle, `Q` is a square (`IsSquare`) with
the side `AB`, `Q₁`, `Q₂` squares with the sides `BC`, `AC` (anywhere in the plane), and `U` is
composed of `Q₁` and `Q₂`, then `Q` and `U` are of equal content. The proof uses the measure and
Theorem 30 (proved below), which are not "the theorems which we have already given" at this
point of the text; the derivation from Theorems 24–27 alone (Euclid I 47) is not formalized.

**Status.** proved
-/

/-- `ABCD` is a **square**. -/
def IsSquare (A B C D : P) : Prop := IsRectangle (L := L) A B C D ∧ SegCong A B B C

/-- The measure of a square, in co-ordinates. -/
theorem square_kmeasure (ax : Pas.Axes P L) {A B C D : P} (h : IsSquare (L := L) A B C D) :
    IsPolyRegion (L := L) (ParRegion A B C D) ∧
      kmeasure (Areas.img ax (ParRegion A B C D)) = Pas.len ax A B * Pas.len ax A B := by
  obtain ⟨⟨hpar, hr⟩, hs⟩ := h
  obtain ⟨d, m⟩ := parallelogram_decomposition ax hpar
  refine ⟨⟨_, by simp, d⟩, ?_⟩
  rw [m]
  obtain ⟨-, hc⟩ := (parallelogram_iff ax).1 hpar
  have e1 : det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D) =
      -det3 (Areas.co ax B) (Areas.co ax A) (Areas.co ax C) := by
    rw [hc]; simp only [par4, det3]; ring
  rw [e1, abs_neg, abs_det_of_right ax hr]
  obtain ⟨hAB, hCB, -⟩ := Pas.nc_ne ax hr.1
  rw [Pas.len_comm ax B A, ((Pas.len_eq_iff ax hAB (Ne.symm hCB)).2 hs).symm]

/-- **The theorem of Pythagoras** for content. -/
theorem pythagoras_content {A B C Q₁ Q₂ Q₃ Q₄ R₁ R₂ R₃ R₄ S₁ S₂ S₃ S₄ : P} {U : Set P}
    (hr : IsRightAngle (L := L) A C B) (hQ : IsSquare (L := L) Q₁ Q₂ Q₃ Q₄)
    (hQs : SegCong Q₁ Q₂ A B) (hR : IsSquare (L := L) R₁ R₂ R₃ R₄) (hRs : SegCong R₁ R₂ B C)
    (hS : IsSquare (L := L) S₁ S₂ S₃ S₄) (hSs : SegCong S₁ S₂ A C)
    (hU : Composed (L := L) U (ParRegion R₁ R₂ R₃ R₄) (ParRegion S₁ S₂ S₃ S₄)) :
    EqualContent (L := L) (ParRegion Q₁ Q₂ Q₃ Q₄) U := by
  obtain ⟨-, D, hD, -⟩ := id hr
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) (ne12_of_between (Line := L) hD)
  obtain ⟨hAC, hBC, hAB⟩ := Pas.nc_ne ax hr.1
  obtain ⟨pQ, mQ⟩ := square_kmeasure ax hQ
  obtain ⟨-, mR⟩ := square_kmeasure ax hR
  obtain ⟨-, mS⟩ := square_kmeasure ax hS
  have cU := (composed_iff ax).1 hU
  rw [equalContent_iff ax]
  refine KEqContent.of_kmeasure ((isPolygon_iff ax).1 pQ)
    (by obtain ⟨l1, l2, n1, -, -, -, hU'⟩ := cU; exact ⟨_, by simp [n1], hU'⟩) ?_
  rw [cU.kmeasure_eq, mQ, mR, mS]
  have hQ12 : Q₁ ≠ Q₂ := (Pas.nc_ne ax hQ.1.1.1).1
  have hR12 : R₁ ≠ R₂ := (Pas.nc_ne ax hR.1.1.1).1
  have hS12 : S₁ ≠ S₂ := (Pas.nc_ne ax hS.1.1.1).1
  rw [(Pas.len_eq_iff ax hQ12 hAB).2 hQs, (Pas.len_eq_iff ax hR12 hBC).2 hRs,
    (Pas.len_eq_iff ax hS12 hAC).2 hSs]
  -- Pythagoras in co-ordinates
  obtain ⟨-, -, hd⟩ := (Areas.isRightAngle_iff_dot ax).1 hr
  simp only [Areas.dotc] at hd
  rw [Areas.len_sq_co, Areas.len_sq_co, Areas.len_sq_co]
  linear_combination (-2 : Pas.G ax) * hd

/-!
## [s19.all_equal] Are all polygons of equal content?

*(§ 19)*

> In the further development of the theory of area, we meet, however, with an essential difficulty. In fact, the discussion so far leaves it still in doubt whether all polygons are not, perhaps, of equal content. In this case, all of the propositions which we have given would be devoid of meaning and hence of no value.

**Lean reading.** The question is answered by Theorem 30: `not_all_equal_content` (unit
`s21.comparison`) shows that a triangle and a triangle strictly inside it are not of equal
content.

**Status.** remark
-/

/-!
## [s19.rectangle_question] Is a rectangle determined by a side and its content?

*(§ 19)*

> Furthermore, the more general question also arises as to whether two rectangles of equal content and having one side in common, do not also have their other sides congruent; that is to say, whether a rectangle is not definitely determined by means of a side and its area. As a closer investigation shows, in order to answer this question, we need to make use of the converse of theorem 27. This may be stated as follows:

**Lean reading.** The question is answered in unit `s21.rectangles` (`rectangles_equal_content`).
The methodological claim "we need to make use of the converse of Theorem 27" is not a
mathematical statement; the proof given there uses the measure, as does Hilbert's.

**Status.** remark
-/

/-!
## [th.28] Theorem 28

*(§ 19)*

> If two triangles have equal content and equal bases, they have also equal altitudes.

**Lean reading.** `theorem28`: for triangles `ABC`, `A'B'C'` with `TriRegion ABC`,
`TriRegion A'B'C'` of equal content and bases `BC ≡ B'C'`, the heights are congruent:
`AF ≡ A'F'` for the feet `F`, `F'` of the perpendiculars from `A`, `A'`. Hilbert's proof (end of
§ 20) is followed: equal content gives equal measures (Theorem 30, first half), so
`BC · AF = B'C' · A'F'` in the field of segments, and `AF ≡ A'F'` after cancelling `BC ≡ B'C'`.

**Status.** proved
-/

/-- **Theorem 28.** -/
theorem theorem28 {A B C A' B' C' F F' : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩)
    (ht' : Tri.Nd (L := L) ⟨A', B', C'⟩)
    (h : EqualContent (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A', B', C'⟩))
    (hb : SegCong B C B' C') (hF : IsFoot (L := L) A B C F) (hF' : IsFoot (L := L) A' B' C' F') :
    SegCong A F A' F' := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  rw [equalContent_iff ax] at h
  have hm := h.kmeasure_eq
  rw [kmeasure_tri ax ht, kmeasure_tri ax ht'] at hm
  have e1 := len_mul_foot ax hF
  have e2 := len_mul_foot ax hF'
  rw [det3_cyc] at e1 e2
  change |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C)| / 2 =
    |det3 (Areas.co ax A') (Areas.co ax B') (Areas.co ax C')| / 2 at hm
  rw [← e1, ← e2] at hm
  obtain ⟨-, hcb, -⟩ := Pas.nc_ne ax ht.1
  obtain ⟨-, hcb', -⟩ := Pas.nc_ne ax ht'.1
  rw [(Pas.len_eq_iff ax (Ne.symm hcb) (Ne.symm hcb')).2 hb] at hm
  have hpos := Pas.len_pos ax (Ne.symm hcb')
  have : Pas.len ax A F = Pas.len ax A' F' := by
    apply mul_left_cancel₀ hpos.ne'; linarith
  exact (Pas.len_eq_iff ax (ne_of_isFoot hF ax) (ne_of_isFoot hF' ax)).1 this

/-!
## [s19.euclid_axiom] Euclid's proof of I 39 uses an axiom on magnitudes

*(§ 19)*

> This fundamental theorem is to be found in the first book of Euclid's Elements as proposition 39. In the demonstration of this theorem, however, Euclid appeals to the general proposition relating to magnitudes: “$K \alpha \grave{\iota} \tau \grave{o} \check{o} \lambda o \upsilon \tau o \hat{\nu} \mu \acute{\epsilon} \rho o \upsilon \varsigma \mu \epsilon \hat{\iota} \zeta \acute{o} \nu \grave{\epsilon} \sigma \tau \iota \nu$”—a method of procedure which amounts to the same thing as introducing a new geometrical axiom concerning areas.

**Lean reading.** A historical remark; the common notion "the whole is greater than the part"
corresponds, for content, to unit `s21.comparison` (`smaller_content_of_subset`), which is
proved here, not assumed.

**Status.** remark
-/

/-!
## [s19.without_archimedes] Theorem 28 without Archimedes's axiom

*(§ 19)*

> It is now possible to establish the above theorem and hence the theory of areas in the manner we have proposed, that is to say, with the help of the plane axioms and without making use of the axiom of Archimedes. In order to show this, it is necessary to introduce the idea of the measure of area.

**Lean reading.** `theorem28` assumes only `PlaneCongruence` and `PlaneParallels`; its proof uses
the measure of area of § 20, as announced.

**Status.** remark
-/

end Section19b

section Section20

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-!
## [s20.base_altitude] The product of a side and its altitude

*(§ 20)*

> Definition. If in a triangle $ABC$, having the sides $a$, $b$, $c$, we construct the two altitudes $h_a = AD$, $h_b = BE$, then, according to theorem 22, it follows from the similarity of the triangles $BCE$ and $ACD$, that we have the proportion \[ a: h_b = b: ha; \] that is, we have \[ a \cdot h_a = b \cdot h_b. \] … This shows that the product of the base and the corresponding altitude of a triangle is the same whichever side is selected as the base.

**Lean reading.** `base_altitude_product`: for a triangle `ABC` and the feet `D` of the
perpendicular from `A` to `BC` and `E` from `B` to `CA`, `BC · AD = CA · BE` in the field of
segments `Pas.G ax` (for any axes `ax`; products of lengths are Hilbert's products of segments,
`hilbertProd_iff'`). Both products equal `|(C - B) × (A - B)|` (`len_mul_foot`), which replaces
the similarity of `BCE` and `ACD` (Theorem 22); `ha` in the printed proportion is a misprint for
`h_a`.

**Status.** proved
-/

/-- `a · h_a = b · h_b`. -/
theorem base_altitude_product (ax : Pas.Axes P L) {A B C D E : P}
    (hD : IsFoot (L := L) A B C D) (hE : IsFoot (L := L) B C A E) :
    Pas.len ax B C * Pas.len ax A D = Pas.len ax C A * Pas.len ax B E := by
  rw [len_mul_foot ax hD, len_mul_foot ax hE, ← det3_cyc]

/-!
## [s20.measure] The measure of area of a triangle

*(§ 20)*

> The half of this product of the base and the altitude of a triangle $\Delta$ is called the *measure of area of the triangle $\Delta$* and we denote it by $F(\Delta)$.

**Lean reading.** `triMeasure ax t`: half the product of the side `bc` and the altitude from `a`
(the chosen foot `foot`), an element of the field of segments `Pas.G ax`; it depends on the axes
`ax` (on the unit segment of the algebra of segments), as Hilbert's segment algebra does.
`triMeasure_eq_of_foot`: any foot gives the same value; `triMeasure_eq`: in co-ordinates it is
`|D| / 2`, `D` the cross product of two sides; by `base_altitude_product` it does not depend on
the side chosen (`triMeasure_rot`).

**Status.** definition
-/

/-- The **measure of area** `F(Δ)` of a triangle. -/
noncomputable def triMeasure (ax : Pas.Axes P L) (t : Tri P) : Pas.G ax :=
  Pas.len ax t.b t.c * Pas.len ax t.a (foot (L := L) t.a t.b t.c) / 2

variable (ax : Pas.Axes P L)

theorem triMeasure_eq_of_foot {A B C F : P} (hF : IsFoot (L := L) A B C F) :
    triMeasure ax ⟨A, B, C⟩ = Pas.len ax B C * Pas.len ax A F / 2 := by
  have hex : ∃ F, IsFoot (L := L) A B C F := ⟨F, hF⟩
  have h := hex.choose_spec
  unfold triMeasure foot
  rw [dite_eq_left_of_eq_true (eq_true hex), len_mul_foot ax h, len_mul_foot ax hF]

theorem triMeasure_eq {t : Tri P} (ht : t.Nd (L := L)) :
    triMeasure ax t = |(Areas.Tri.co ax t).D| / 2 := by
  obtain ⟨F, hF⟩ := exists_foot ax ht
  have := triMeasure_eq_of_foot ax hF
  rw [len_mul_foot ax hF, det3_cyc] at this
  exact this

theorem triMeasure_rot {t : Tri P} (ht : t.Nd (L := L)) (ht' : (Tri.mk t.b t.c t.a).Nd (L := L)) :
    triMeasure ax ⟨t.b, t.c, t.a⟩ = triMeasure ax t := by
  rw [triMeasure_eq ax ht, triMeasure_eq ax ht']
  show |det3 (Areas.co ax t.b) (Areas.co ax t.c) (Areas.co ax t.a)| / 2 =
    |det3 (Areas.co ax t.a) (Areas.co ax t.b) (Areas.co ax t.c)| / 2
  rw [det3_cyc]

theorem triMeasure_pos {t : Tri P} (ht : t.Nd (L := L)) : 0 < triMeasure ax t := by
  rw [triMeasure_eq ax ht]
  exact div_pos (abs_pos.2 ((Areas.nd_iff ax).1 ht)) two_pos

/-!
## [s20.transversal] Transversals and transversal decompositions

*(§ 20)*

> A segment joining a vertex of a triangle with a point of the opposite side is called *a transversal.* A transversal divides the given triangle into two others having the same altitude and having bases which lie in the same straight line. Such a decomposition is called a *transversal decomposition of the triangle.*

**Lean reading.** `transversal_decomposition`: for `X` between `B` and `C` (the transversal `AX`),
`TriRegion ABC` is decomposed into `TriRegion ABX` and `TriRegion AXC` (`Areas.split`); their
bases `BX`, `XC` lie on the line `BC` and every foot of the perpendicular from `A` to `BC` is
the foot for both (same altitude). The inductive predicate `TransDecomp t l` ("`l` arises from
`t` by a series of transversal decompositions"): `[t]`; splitting a triangle by a transversal
and decomposing both parts; and relabelling the vertices cyclically (so that transversals from
every vertex are allowed).

**Status.** proved
-/

theorem img_triRegion_rot {t : Tri P} (ht : t.Nd (L := L)) (p : Pas.G ax × Pas.G ax) :
    Areas.img ax (TriRegion (Tri.mk t.b t.c t.a)) p ↔ Areas.img ax (TriRegion t) p := by
  have ht' : (Tri.mk t.b t.c t.a).Nd (L := L) := by
    rw [Areas.nd_iff ax] at ht ⊢; exact (Tr.nd_rot (t := Areas.Tri.co ax t)).2 ht
  rw [Areas.img_triRegion ax ht', Areas.img_triRegion ax ht]
  exact Tr.mem_rot (t := Areas.Tri.co ax t)

theorem transversal_decomposition {A B C X : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩)
    (hX : Between B X C) :
    IsDecomposition (L := L) (TriRegion ⟨A, B, C⟩) [⟨A, B, X⟩, ⟨A, X, C⟩] ∧
      Collinear (Line := L) B C X ∧
      ∀ F, IsFoot (L := L) A B C F → IsFoot (L := L) A B X F ∧ IsFoot (L := L) A X C F := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  obtain ⟨hBC, s, s0, s1, hs⟩ := (Areas.between_iff_co ax).1 hX
  have sp := split ((Areas.nd_iff ax).1 ht) s0 s1
  have hcol := collinear_of_between (Line := L) hX
  refine ⟨(isDecomposition_iff ax).2 ?_, hcol.swap23, fun F hF => ?_⟩
  · refine (sp.congr (fun p => (Areas.img_triRegion ax ht p).symm)).replace ?_
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil) <;>
      exact TrEquiv.of_eq (by simp only [Areas.Tri.co, hs])
  · -- the line `BX` (and `XC`) is the line `BC`
    have key : ∀ Y : P, Collinear (Line := L) B C Y →
        Collinear (Line := L) B X Y ∧ Collinear (Line := L) X C Y := by
      intro Y hY
      rw [Areas.collinear_iff_det3 ax] at hY
      rw [Areas.collinear_iff_det3 ax, Areas.collinear_iff_det3 ax, hs]
      constructor
      · rw [show det3 (Areas.co ax B) (lerp s (Areas.co ax B) (Areas.co ax C)) (Areas.co ax Y) =
          s * det3 (Areas.co ax B) (Areas.co ax C) (Areas.co ax Y) by unfold det3 lerp; ring, hY,
          mul_zero]
      · rw [show det3 (lerp s (Areas.co ax B) (Areas.co ax C)) (Areas.co ax C) (Areas.co ax Y) =
          (1 - s) * det3 (Areas.co ax B) (Areas.co ax C) (Areas.co ax Y) by unfold det3 lerp; ring,
          hY, mul_zero]
    obtain ⟨hF1, Y, hY1, hYF, hr⟩ := hF
    exact ⟨⟨(key F hF1).1, Y, (key Y hY1).1, hYF, hr⟩, ⟨(key F hF1).2, Y, (key Y hY1).2, hYF, hr⟩⟩

/-- `l` arises from `t` by a **series of transversal decompositions**. -/
inductive TransDecomp : Tri P → List (Tri P) → Prop
  | single (t : Tri P) : TransDecomp t [t]
  | split {A B C X : P} {l₁ l₂ : List (Tri P)} : Between B X C → TransDecomp ⟨A, B, X⟩ l₁ →
      TransDecomp ⟨A, X, C⟩ l₂ → TransDecomp ⟨A, B, C⟩ (l₁ ++ l₂)
  | rot {t : Tri P} {l : List (Tri P)} : TransDecomp t l → TransDecomp ⟨t.b, t.c, t.a⟩ l

/-!
## [s20.transversal_additive] The measure is additive for transversal decompositions

*(§ 20)*

> Proof. From the distributive law of our algebra of segments, it follows immediately that the measure of area of an arbitrary triangle is equal to the sum of the measures of area of two such triangles as arise from any transversal decomposition of the given triangle. The repeated application of this proposition shows that the measure of area of any triangle is equal to the sum of the measures of area of all the triangles arising by applying the transversal decomposition an arbitrary number of times in succession.

**Lean reading.** `transversal_measure`: `F(ABC) = F(ABX) + F(AXC)` for `X` between `B` and `C`
(the common altitude times `BX + XC = BC`, by `Pas.len_add`, and distributivity);
`transDecomp_measure`: for `TransDecomp t l`, `l` is a decomposition of `t` and `F(t)` is the sum
of the `F` of its triangles (induction).

**Status.** proved
-/

theorem transversal_measure {A B C X : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩) (hX : Between B X C) :
    triMeasure ax ⟨A, B, C⟩ = triMeasure ax ⟨A, B, X⟩ + triMeasure ax ⟨A, X, C⟩ := by
  obtain ⟨d, -, hF⟩ := transversal_decomposition ht hX
  obtain ⟨F, hF0⟩ := exists_foot ax ht
  obtain ⟨h1, h2⟩ := hF F hF0
  rw [triMeasure_eq_of_foot ax hF0, triMeasure_eq_of_foot ax h1, triMeasure_eq_of_foot ax h2,
    Pas.len_add ax hX]
  ring

theorem transDecomp_measure {t : Tri P} {l : List (Tri P)} (h : TransDecomp t l)
    (ht : t.Nd (L := L)) :
    IsDecomposition (L := L) (TriRegion t) l ∧ triMeasure ax t = (l.map (triMeasure ax)).sum := by
  induction h with
  | single t => exact ⟨isDecomposition_single' ht, by simp⟩
  | @split A B C X l₁ l₂ hX h₁ h₂ ih₁ ih₂ =>
    obtain ⟨d, -, -⟩ := transversal_decomposition ht hX
    have n₁ : (Tri.mk A B X).Nd (L := L) := d.1 _ (by simp)
    have n₂ : (Tri.mk A X C).Nd (L := L) := d.1 _ (by simp)
    obtain ⟨d₁, m₁⟩ := ih₁ n₁
    obtain ⟨d₂, m₂⟩ := ih₂ n₂
    refine ⟨(isDecomposition_iff ax).2 ?_, ?_⟩
    · rw [List.map_append]
      exact ((isDecomposition_iff ax).1 d).append_of
        ((isDecomposition_iff ax).1 (isDecomposition_single' n₁))
        ((isDecomposition_iff ax).1 (isDecomposition_single' n₂))
        ((isDecomposition_iff ax).1 d₁) ((isDecomposition_iff ax).1 d₂)
    · rw [transversal_measure ax ht hX, m₁, m₂, List.map_append, List.sum_append]
  | @rot t l h ih =>
    have ht' : t.Nd (L := L) := by
      rw [Areas.nd_iff ax] at ht ⊢; exact (Tr.nd_rot (t := Areas.Tri.co ax t)).1 ht
    obtain ⟨d, m⟩ := ih ht'
    refine ⟨(isDecomposition_iff ax).2 (((isDecomposition_iff ax).1 d).congr
      (fun p => (img_triRegion_rot ax ht' p).symm)), ?_⟩
    rw [triMeasure_rot ax ht' ht, m]

/-!
## [th.29] Theorem 29

*(§ 20)*

> If a triangle $\Delta$ is decomposed by means of arbitrary straight lines into a finite number of triangles $\Delta_k$, then the measure of area of $\Delta$ is equal to the sum of the measures of area of the separate triangles $\Delta_k$.

**Lean reading.** `theorem29`: for a decomposition `l` of `TriRegion Δ` (any decomposition into
triangles with disjoint interiors; "by means of arbitrary straight lines" adds nothing, the sides
of the triangles being segments), `F(Δ) = Σ F(Δ_k)`. The proof is not Hilbert's: in co-ordinates
(`Areas.area_additive`) the lengths of the vertical sections of the triangles add up at every
abscissa which is not that of a vertex (a one-dimensional lemma on intervals), these lengths are
affine between consecutive such abscissae, and the midpoint sums over the sorted abscissae of all
vertices integrate them exactly to `|D| / 2`; all of this holds in any ordered field, without
Archimedes's axiom. Hilbert's proof refines the decomposition by the transversals from a vertex
through all points of division and asserts that the pieces arise from both `Δ` and the `Δ_k` by
series of transversal decompositions; its first step is unit `s20.transversal_additive`, its key
lemma unit `s20.transversal_series` (proved there). The remaining steps of Hilbert's proof (the
triangles `Δ_t` and, after drawing the diagonals, the `Δ_k` satisfy the hypotheses of that lemma)
are not formalized, since the theorem is proved by the other method.

**Status.** proved
-/

/-- **Theorem 29.** -/
theorem theorem29 {T : Tri P} (hT : T.Nd (L := L)) {l : List (Tri P)}
    (h : IsDecomposition (L := L) (TriRegion T) l) :
    triMeasure ax T = (l.map (triMeasure ax)).sum := by
  have hd := ((isDecomposition_iff ax).1 h).congr (fun p => Areas.img_triRegion ax hT p)
  have := area_additive ((Areas.nd_iff ax).1 hT) hd
  have e : ∀ r ∈ l, triMeasure ax r = |(Areas.Tri.co ax r).D| / 2 := fun r hr =>
    triMeasure_eq ax (h.1 r hr)
  have hsum : ∀ l' : List (Tri P), (l'.map (fun r => |(Areas.Tri.co ax r).D| / 2)).sum =
      (l'.map (fun r => |(Areas.Tri.co ax r).D|)).sum / 2 := by
    intro l'
    induction l' with
    | nil => simp
    | cons x l' ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [triMeasure_eq ax hT, this, List.map_map, List.map_congr_left e, hsum]
  rfl

end Section20


section Section20b

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-!
## [s20.polygon_measure] The measure of area of a polygon

*(§ 20)*

> Definition. If we define the measure of area $F(P)$ of a polygon as the sum of the measures of area of all the triangles into which the polygon is, by a definite decomposition, divided, then upon the basis of theorem 29 and by a process of reasoning similar to that which we have employed in … to prove theorem 24, we know that the measure of area of a polygon is independent of the manner of decomposition into triangles and, consequently, is definitely determined by the polygon itself.

**Lean reading.** `polyMeasure ax S`: the sum of `triMeasure ax` over a chosen decomposition of
`S` (`0` if there is none). `polyMeasure_eq`: for every decomposition `l` of `S`,
`polyMeasure ax S = Σ_{t ∈ l} F(t)` — the independence of the decomposition, proved as Hilbert
says: the common refinement of the two decompositions (as in Theorem 24, `Areas.common_refinement`)
and Theorem 29 applied to each triangle of both (`Areas.decS_sum_eq`).

**Status.** proved
-/

open Classical in
/-- The **measure of area** `F(P)` of a polygon. -/
noncomputable def polyMeasure (ax : Pas.Axes P L) (S : Set P) : Pas.G ax :=
  if h : ∃ l, IsDecomposition (L := L) S l then (h.choose.map (triMeasure ax)).sum else 0

variable (ax : Pas.Axes P L)

theorem sum_triMeasure {S : Set P} {l : List (Tri P)} (h : IsDecomposition (L := L) S l) :
    (l.map (triMeasure ax)).sum = kmeasure (Areas.img ax S) := by
  rw [kmeasure_of_decS ((isDecomposition_iff ax).1 h), List.map_map]
  have e : ∀ r ∈ l, triMeasure ax r = |(Areas.Tri.co ax r).D| / 2 := fun r hr =>
    triMeasure_eq ax (h.1 r hr)
  have hsum : ∀ l' : List (Tri P), (l'.map (fun r => |(Areas.Tri.co ax r).D| / 2)).sum =
      (l'.map (fun r => |(Areas.Tri.co ax r).D|)).sum / 2 := by
    intro l'
    induction l' with
    | nil => simp
    | cons x l' ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [List.map_congr_left e, hsum]
  rfl

theorem polyMeasure_eq {S : Set P} {l : List (Tri P)} (h : IsDecomposition (L := L) S l) :
    polyMeasure ax S = (l.map (triMeasure ax)).sum := by
  have hex : ∃ l, IsDecomposition (L := L) S l := ⟨l, h⟩
  unfold polyMeasure
  rw [dite_eq_left_of_eq_true (eq_true hex), sum_triMeasure ax hex.choose_spec, sum_triMeasure ax h]

theorem polyMeasure_eq_kmeasure (S : Set P) : polyMeasure ax S = kmeasure (Areas.img ax S) := by
  by_cases hex : ∃ l, IsDecomposition (L := L) S l
  · obtain ⟨l, h⟩ := hex
    rw [polyMeasure_eq ax h, sum_triMeasure ax h]
  · unfold polyMeasure kmeasure
    rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false
      (fun ⟨_, h⟩ => hex ⟨_, isDecomposition_of_decS ax h⟩))]

/-!
## [s20.equal_area_measure] Polygons of equal area have equal measures

*(§ 20)*

> From this we obtain, by aid of theorem 29, the result that *polygons of equal area have also equal measures of area*.

**Lean reading.** `equalArea_measure`: congruent triangles have equal measures (their squared
sides are equal, and `D²` is a polynomial in them, `Areas.D_sq`), so the sums over corresponding
decompositions agree.

**Status.** proved
-/

theorem equalArea_measure {S T : Set P} (h : EqualArea (L := L) S T) :
    polyMeasure ax S = polyMeasure ax T := by
  rw [polyMeasure_eq_kmeasure, polyMeasure_eq_kmeasure]
  exact ((equalArea_iff ax).1 h).kmeasure_eq

/-!
## [s20.equal_content_measure] Polygons of equal content have equal measures

*(§ 20)*

> Furthermore, if $P$ and $Q$ are two polygons of equal content, then there must exist, according to the above definition, two other polygons $P'$ and $Q'$ of equal area, such that the polygon composed of $P$ and $P'$ shall be of equal area with the polygon formed by combining the polygons $Q$ and $Q'$. From the two equations \begin{eqnarray*} F(P+P') & = & F(Q + Q') \\ F(P') & = & F(Q'), \end{eqnarray*} we easily deduce the equation \[ F(P) = F(Q); \] that is to say, *polygons of equal content have also equal measure of area*.

**Lean reading.** `equalContent_measure`, with Hilbert's proof: `F` is additive for composed
polygons (`F(P + P') = F(P) + F(P')`, sum over the joined decompositions) and the equations give
`F(P) = F(Q)`.

**Status.** proved
-/

theorem equalContent_measure {S T : Set P} (h : EqualContent (L := L) S T) :
    polyMeasure ax S = polyMeasure ax T := by
  rw [polyMeasure_eq_kmeasure, polyMeasure_eq_kmeasure]
  exact ((equalContent_iff ax).1 h).kmeasure_eq

/-!
## [s20.theorem28_proof] Hilbert's proof of Theorem 28

*(§ 20)*

> From this last statement, we obtain immediately the proof of theorem 28. If we denote the equal bases of the two triangles by $g$ and the corresponding altitudes by $h$ and $h'$, respectively, then we may conclude from the assumed equality of content of the two triangles that they must also have equal measures of area; that is to say, it follows that \[ \frac{1}{2}gh = \frac{1}{2}gh' \] and, consequently, dividing by $\frac{1}{2}g$, we get \[ h = h', \] which is the statement made in theorem 28.

**Lean reading.** This is the proof of `theorem28` (unit `th.28`): `g h = g h'` in the field of
segments, and the cancellation of `g ≠ 0`.

**Status.** remark
-/

/-!
## [s20.transversal_series] Decompositions without interior points of division

*(§ 20)*

> In fact, it is at once evident that any decomposition of a triangle into partial triangles may always be affected by a series of transversal decompositions, providing, in this decomposition, points of division do not exist within the triangle, and further, that at least one side of the triangle remains free from points of division.

**Lean reading.** `TransversalSeriesClaim P`: for a triangle `ABC` and a decomposition `l` of it
none of whose vertices ("points of division") lies in the interior of `ABC` or within the side
`BC` (the free side), there is a series of transversal decompositions (`TransDecomp`) of `ABC`
whose triangles are those of `l` (same regions, as many). `transversalSeriesClaim` proves it in
every plane with the axioms I 1–2, II–IV, by the induction Hilbert's "at once evident" passes
over (`Areas.trans_series_K`): the triangle of `l` containing the midpoint of `BC` has the
vertices `B`, `C` and a third vertex `W` (`Areas.piece_at_mid`: no vertex lies within `BC`); `W`
is not inside `ABC`, so `W = A` (then `l` has one triangle) or `W` lies within `CA` or `AB`; the
transversal `BW` (resp. `CW`) cuts off this triangle, the other triangles decompose the remaining
triangle (`Areas.decS_erase`), in which the new side `BW` (resp. `WC`) is free of points of
division (its points are inside `ABC`), and the induction on the number of triangles applies.
The converse, that a series of transversal decompositions is a decomposition with additive
measure, is `transDecomp_measure`. (Theorem 29 itself is proved by another method, unit `th.29`.)

**Status.** proved
-/

/-- **Hilbert's claim** (§ 20): a decomposition of a triangle without points of division in its
interior and with a side free of points of division is a series of transversal
decompositions (proved: `transversalSeriesClaim`). -/
def TransversalSeriesClaim (P : Type u) {L : Type v} [HasLines P L] [HasBetween P] : Prop :=
  ∀ (A B C : P) (l : List (Tri P)), Tri.Nd (L := L) ⟨A, B, C⟩ →
    IsDecomposition (L := L) (TriRegion ⟨A, B, C⟩) l →
    (∀ t ∈ l, ∀ V ∈ [t.a, t.b, t.c], V ∉ TriInterior (Tri.mk A B C) ∧ ¬Between B V C) →
    ∃ l' : List (Tri P), TransDecomp ⟨A, B, C⟩ l' ∧ l'.length = l.length ∧
      ∀ t' ∈ l', ∃ t ∈ l, TriRegion t' = TriRegion t

/-- A series of transversal decompositions in co-ordinates gives one in the plane. -/
theorem transDecomp_of_KTD {r : Areas.Tr (Pas.G ax)} {l : List (Areas.Tr (Pas.G ax))}
    (h : KTD r l) : TransDecomp (Areas.unco (L := L) ax r) (l.map (Areas.unco (L := L) ax)) := by
  induction h with
  | single t => exact TransDecomp.single _
  | @split a b c s l₁ l₂ hbc hs0 hs1 h₁ h₂ ih₁ ih₂ =>
    rw [List.map_append]
    have e : ∀ v, Areas.co ax (Areas.co_surj (L := L) ax v).choose = v :=
      fun v => (Areas.co_surj (L := L) ax v).choose_spec
    have hB : Between (Areas.co_surj (L := L) ax b).choose
        (Areas.co_surj (L := L) ax (lerp s b c)).choose (Areas.co_surj (L := L) ax c).choose := by
      rw [Areas.between_iff_co ax]
      refine ⟨fun h => hbc ?_, s, hs0, hs1, by rw [e, e, e]⟩
      rw [← e b, ← e c, h]
    exact TransDecomp.split hB ih₁ ih₂
  | @rot t l h ih => exact TransDecomp.rot ih

/-- **Hilbert's lemma of § 20**: a decomposition of a triangle without points of division in its
interior or within one side is a series of transversal decompositions. -/
theorem transversalSeriesClaim : TransversalSeriesClaim (L := L) P := by
  intro A B C l ht hl hv
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  have htK : (Areas.Tri.co ax ⟨A, B, C⟩).nd := (Areas.nd_iff ax).1 ht
  have hlK : DecS (Areas.Tri.co ax ⟨A, B, C⟩).mem (l.map (Areas.Tri.co ax)) :=
    ((isDecomposition_iff ax).1 hl).congr (fun p => Areas.img_triRegion ax ht p)
  have hvK : ∀ r ∈ l.map (Areas.Tri.co ax), ∀ v ∈ [r.a, r.b, r.c],
      ¬(Areas.Tri.co ax ⟨A, B, C⟩).int v ∧
        ∀ s : Pas.G ax, 0 < s → s < 1 → v ≠ lerp s (Areas.co ax B) (Areas.co ax C) := by
    intro r hr v hv'
    obtain ⟨t, ht', rfl⟩ := List.mem_map.1 hr
    have hV : ∃ V ∈ [t.a, t.b, t.c], v = Areas.co ax V := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
      rcases hv' with rfl | rfl | rfl
      · exact ⟨t.a, by simp, rfl⟩
      · exact ⟨t.b, by simp, rfl⟩
      · exact ⟨t.c, by simp, rfl⟩
    obtain ⟨V, hVm, rfl⟩ := hV
    obtain ⟨h1, h2⟩ := hv t ht' V hVm
    refine ⟨fun hi => h1 ((Areas.mem_triInterior_iff ax ht V).2 hi), fun s hs0 hs1 he => h2 ?_⟩
    obtain ⟨-, hcb, -⟩ := Pas.nc_ne ax ht.1
    exact (Areas.between_iff_co ax).2 ⟨Ne.symm hcb, s, hs0, hs1, he⟩
  obtain ⟨l'K, hK, hlen, hreg⟩ := trans_series_K _ _ _ _ _ rfl htK hlK hvK
  refine ⟨l'K.map (Areas.unco (L := L) ax), ?_, by simp [hlen], ?_⟩
  · have := transDecomp_of_KTD ax (r := Areas.Tri.co ax ⟨A, B, C⟩) hK
    rwa [Areas.unco_co] at this
  · intro t' ht'
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 ht'
    obtain ⟨r, hr, e⟩ := hreg r' hr'
    obtain ⟨t, htl, rfl⟩ := List.mem_map.1 hr
    refine ⟨t, htl, ?_⟩
    have htnd := hl.1 t htl
    have hr'nd : (Areas.unco (L := L) ax r').Nd (L := L) := by
      rw [Areas.nd_iff ax, Areas.co_unco]; exact e.1.2 ((Areas.nd_iff ax).1 htnd)
    ext X
    rw [Areas.mem_triRegion_iff ax hr'nd, Areas.mem_triRegion_iff ax htnd, Areas.co_unco]
    exact e.2.1 _

end Section20b

section Section21

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Pas.Axes P L)

theorem isPolygon_tri {t : Tri P} (ht : t.Nd (L := L)) : IsPolyRegion (L := L) (TriRegion t) :=
  ⟨[t], by simp, isDecomposition_single' ht⟩

/-- **Polygons of equal measure are of equal content** (the converse half of Theorem 30). -/
theorem equalContent_of_measure {S T : Set P} (hS : IsPolyRegion (L := L) S)
    (hT : IsPolyRegion (L := L) T) (h : polyMeasure ax S = polyMeasure ax T) :
    EqualContent (L := L) S T := by
  rw [equalContent_iff ax]
  rw [polyMeasure_eq_kmeasure, polyMeasure_eq_kmeasure] at h
  exact KEqContent.of_kmeasure ((isPolygon_iff ax).1 hS) ((isPolygon_iff ax).1 hT) h

theorem polyMeasure_tri {t : Tri P} (ht : t.Nd (L := L)) :
    polyMeasure ax (TriRegion t) = triMeasure ax t := by
  rw [polyMeasure_eq ax (isDecomposition_single' ht)]; simp

/-- The measure of a right triangle is half the product of its legs. -/
theorem triMeasure_right {A B C : P} (h : IsRightAngle (L := L) B A C) :
    triMeasure ax ⟨A, B, C⟩ = Pas.len ax A B * Pas.len ax A C / 2 := by
  obtain ⟨hn, -⟩ := id h
  obtain ⟨hBA, hCA, -⟩ := Pas.nc_ne ax hn
  have ht : Tri.Nd (L := L) ⟨A, B, C⟩ :=
    ⟨fun hc => hn hc.swap12, Ne.symm hBA⟩
  obtain ⟨-, -, hd⟩ := (Areas.isRightAngle_iff_dot ax).1 h
  rw [triMeasure_eq ax ht]
  -- `|AB × AC| = AB · AC` for a right angle at `A`
  have key : (Pas.len ax A B * Pas.len ax A C) * (Pas.len ax A B * Pas.len ax A C) =
      |(Areas.Tri.co ax ⟨A, B, C⟩).D| * |(Areas.Tri.co ax ⟨A, B, C⟩).D| := by
    rw [abs_mul_abs_self]
    have h1 := Areas.len_sq_co ax A B
    have h2 := Areas.len_sq_co ax A C
    have : (Pas.len ax A B * Pas.len ax A C) * (Pas.len ax A B * Pas.len ax A C) =
        (Pas.len ax A B * Pas.len ax A B) * (Pas.len ax A C * Pas.len ax A C) := by ring
    rw [this, h1, h2]
    simp only [Areas.dotc] at hd
    show _ = det3 _ _ _ * det3 _ _ _
    unfold det3
    simp only [Areas.Tri.co]
    linear_combination (((Areas.co ax B).1 - (Areas.co ax A).1) * ((Areas.co ax C).1 -
      (Areas.co ax A).1) + ((Areas.co ax B).2 - (Areas.co ax A).2) * ((Areas.co ax C).2 -
      (Areas.co ax A).2)) * hd
  have := (mul_self_inj (mul_nonneg (Pas.len_nonneg ax A B) (Pas.len_nonneg ax A C))
    (abs_nonneg _)).1 key
  rw [this]

/-!
## [s21.right_triangles] Right triangles of equal measure are of equal content

*(§ 21)*

> In order to prove the converse, let us consider two triangles $ABC$ and $AB'C'$ having a common right angle at $A$. The measures of area of these two triangles are expressed by the formul{\ae} … We now assume that these measures of area are equal to each other, and consequently we have \[ AB \cdot AC = AB' \cdot AC', \] or \[ AB:AB' = AC':AC. \] … From this proposition, it follows, according to theorem 23, that the two straight lines $BC'$ and $B'C$ are parallel, and hence, by theorem 27, the two triangles $BC'B'$ and $BC'C$ are of equal content. By the addition of the triangle $ABC'$, it follows that the two triangles $ABC$ and $AB'C'$ are of equal content. We have then shown that two right triangles having the same measure of area are always of equal content.

**Lean reading.** `triMeasure_right`: `F(ABC) = AB · AC / 2` for a right angle at `A`.
`right_triangles_equal_content`: two triangles `ABC`, `AB'C'` with the right angle `∠BAC`,
`B'` on the half-ray `AB` and `C'` on `AC`, and `AB · AC = AB' · AC'`, are of equal content.
Hilbert's argument is formalized in co-ordinates (`Areas.rescale`): the triangle with the longer
leg is cut by the transversal from `B` (resp. `C'`) into the common triangle `ABC'` and a second
triangle; the second triangles `BC'C` and `BC'B'` have the base `BC'` and their vertices on a
parallel to it (the proportion, i.e. Theorem 23), so a shear (Theorems 25–26) gives their equal
content, and the common triangle is added (`Areas.KEqContent.add`, which needs copies placed far
away). The statement is derived here from the general `triangles_equal_content`.

**Status.** proved
-/

/-!
## [s21.triangles] Triangles of equal measure are of equal content

*(§ 21)*

> Take now any arbitrary triangle having the base $g$ and the altitude $h$. Then, according to theorem 27, it has equal content with a right triangle having the two sides $g$ and $h$. Since the original triangle had evidently the same measure of area as the right triangle, it follows that, in the above consideration, the restriction to right triangles was not necessary. Hence, two *arbitrary triangles with equal measures of area are also of equal content*.

**Lean reading.** `triangles_equal_content`: two triangles of equal measure are of equal content
(proof: `Areas.tri_to_rt` moves every triangle by an isometry and shears to a right triangle with
the legs on the axes, then `Areas.rescale`). `right_triangle_of_triangle`: a triangle with base
`BC` and height `AF` and a right triangle `A'B'C'` (right angle at `A'`) with `A'B' ≡ BC`,
`A'C' ≡ AF` are of equal content.

**Status.** proved
-/

theorem triangles_equal_content {t t' : Tri P} (ht : t.Nd (L := L)) (ht' : t'.Nd (L := L))
    (h : triMeasure ax t = triMeasure ax t') :
    EqualContent (L := L) (TriRegion t) (TriRegion t') :=
  equalContent_of_measure ax (isPolygon_tri ht) (isPolygon_tri ht')
    (by rw [polyMeasure_tri ax ht, polyMeasure_tri ax ht', h])

/-- A right angle stays right when its sides are replaced by points of the same half-rays. -/
theorem isRightAngle_of_rays {A B C B' C' : P}
    (h : IsRightAngle (L := L) B A C) (hB' : B' ∈ ray A B) (hC' : C' ∈ ray A C) :
    IsRightAngle (L := L) B' A C' := by
  obtain ⟨hn, D, hD, hc⟩ := h
  have hn' : ¬Collinear (Line := L) B' A C' := not_collinear_of_mem_rays hn hB' hC'
  have hD' : Between B' A D := between_of_between_mem_ray hD (mem_ray_comm hB')
  have nCAD : ¬Collinear (Line := L) C A D := fun hc' =>
    (not_collinear_of_between hn hD) hc'.swap13
  have nC'AD : ¬Collinear (Line := L) C' A D := fun hc' =>
    (not_collinear_of_between hn' hD') hc'.swap13
  refine ⟨hn', D, hD', ?_⟩
  exact angCong_of_sameAngle hn nCAD
    (sameAngle_of_ray_eq (ray_eq_of_mem hB').symm (ray_eq_of_mem hC').symm)
    (sameAngle_of_ray_eq (ray_eq_of_mem hC').symm rfl) hc

theorem right_triangles_equal_content {A B C B' C' : P} (h : IsRightAngle (L := L) B A C)
    (hB' : B' ∈ ray A B) (hC' : C' ∈ ray A C)
    (hm : Pas.len ax A B * Pas.len ax A C = Pas.len ax A B' * Pas.len ax A C') :
    EqualContent (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A, B', C'⟩) := by
  have h' := isRightAngle_of_rays h hB' hC'
  have nd : ∀ {X Y : P}, IsRightAngle (L := L) X A Y → Tri.Nd (L := L) ⟨A, X, Y⟩ := by
    intro X Y hr
    exact ⟨fun hc => hr.1 hc.swap12, Ne.symm (Pas.nc_ne ax hr.1).1⟩
  refine triangles_equal_content ax (nd h) (nd h') ?_
  rw [triMeasure_right ax h, triMeasure_right ax h', hm]

theorem right_triangle_of_triangle {A B C F A' B' C' : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩)
    (hF : IsFoot (L := L) A B C F) (hr : IsRightAngle (L := L) B' A' C')
    (h1 : SegCong A' B' B C) (h2 : SegCong A' C' A F) :
    EqualContent (L := L) (TriRegion ⟨A, B, C⟩) (TriRegion ⟨A', B', C'⟩) := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  obtain ⟨hBA, hCA, -⟩ := Pas.nc_ne ax hr.1
  have ht' : Tri.Nd (L := L) ⟨A', B', C'⟩ := ⟨fun hc => hr.1 hc.swap12, Ne.symm hBA⟩
  refine triangles_equal_content ax ht ht' ?_
  rw [triMeasure_eq_of_foot ax hF, triMeasure_right ax hr]
  obtain ⟨-, hcb, -⟩ := Pas.nc_ne ax ht.1
  rw [(Pas.len_eq_iff ax (Ne.symm hBA) (Ne.symm hcb)).2 h1,
    (Pas.len_eq_iff ax (Ne.symm hCA) (ne_of_isFoot hF ax)).2 h2]

end Section21


section Section21b

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Pas.Axes P L)

theorem polyMeasure_pos {S : Set P} (hS : IsPolyRegion (L := L) S) : 0 < polyMeasure ax S := by
  obtain ⟨l, hl, d⟩ := hS
  rw [polyMeasure_eq_kmeasure]
  exact kmeasure_pos ((isDecomposition_iff ax).1 d) (by simpa using hl)

theorem len_of_co {X Y : P} {g : Pas.G ax} (hg : 0 ≤ g)
    (h : (Areas.co ax X).1 - (Areas.co ax Y).1 = g ∨ (Areas.co ax Y).1 - (Areas.co ax X).1 = g)
    (h2 : (Areas.co ax X).2 = (Areas.co ax Y).2) : Pas.len ax X Y = g := by
  have e := Areas.len_sq_co ax X Y
  rw [h2, sub_self, mul_zero, add_zero] at e
  have : Pas.len ax X Y * Pas.len ax X Y = g * g := by
    rw [e]; rcases h with h | h
    · rw [h]
    · rw [← h]; ring
  exact (mul_self_inj (Pas.len_nonneg ax X Y) hg).1 this

/-!
## [s21.polygon_triangle] A polygon is of equal content with a triangle

*(§ 21)*

> Moreover, let us suppose $P$ to be any polygon having the measure of area $g$ and let $P$ be decomposed into $n$ triangles having respectively the measures of area $g_1$, $g_2$, $g_3$, $\ldots$, $g_n$. Then, we have \[ g = g_1 + g_2 + g_3 + \cdots + g_n. \] Construct now a triangle $ABC$ having the base $AB=g$ and the altitude $h = 1$. Take, upon the base of this triangle, the points $A_1$, $A_2$, $\ldots$, $A_{n-1}$ so that $g_1=AA_1$, $g_1=A_1A_2$, $\ldots$, $g_{n-1}=A_{n-2}A_{n-1}$, $g_n=A_{n-1}B$. … Consequently, the polygon $P$ and a triangle, having the base $g$ and the altitude $h = 1$ are of equal content. From this, it follows, by the application of theorem 24, that two polygons having equal measures of area are always of equal content.

**Lean reading.** As printed the claim is false: the triangle with base `g` and altitude `1` has
the measure `g / 2`, not `g` (and the triangles `A_{k-1}A_kC` have the measures `g_k / 2`), so by
Theorem 30 it is not of equal content with `P` (`polygon_triangle_as_printed_false`). The
corrected statement takes the altitude `2` (or the base `2g`): `polygon_triangle`: every polygon
`S` is of equal content with a triangle `ABC` whose base `AB` has the length `F(S)` and whose
height `CF` has the length `2`. (The second "`g_1 = A_1A_2`" is a misprint for `g_2`.) The proof
follows Hilbert's (`Areas.poly_to_Tstd`): each triangle of a decomposition is of equal content
with the triangle on its piece `[x_{k-1}, x_k]` of the base (apex `(0, 2)`), these pieces form a
fan decomposition of the big triangle, and the parts are added (`Areas.KEqContent.add`).

**Status.** proved (corrected)
-/

theorem polygon_triangle {S : Set P} (hS : IsPolyRegion (L := L) S) :
    ∃ A B C F : P, Tri.Nd (L := L) ⟨A, B, C⟩ ∧ IsFoot (L := L) C A B F ∧
      Pas.len ax A B = polyMeasure ax S ∧ Pas.len ax C F = 2 ∧
      EqualContent (L := L) S (TriRegion ⟨A, B, C⟩) := by
  set g := polyMeasure ax S
  have hg : 0 < g := polyMeasure_pos ax hS
  obtain ⟨A, hA⟩ := Areas.co_surj ax (0, 0)
  obtain ⟨B, hB⟩ := Areas.co_surj ax (g, 0)
  obtain ⟨C, hC'⟩ := Areas.co_surj ax (0, 2)
  have hD : det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C) = 2 * g := by
    rw [hA, hB, hC']; simp only [det3]; ring
  have hAB : A ≠ B := fun e => by
    have := congrArg (fun X => (Areas.co ax X).1) e
    simp only [hA, hB] at this
    linarith
  have ht : Tri.Nd (L := L) ⟨A, B, C⟩ :=
    ⟨by rw [Areas.collinear_iff_det3 ax, hD]; exact mul_ne_zero two_ne_zero hg.ne', hAB⟩
  have htC : Tri.Nd (L := L) ⟨C, A, B⟩ := by
    refine ⟨fun hc => ht.1 (by obtain ⟨l, h1, h2, h3⟩ := hc; exact ⟨l, h2, h3, h1⟩), ?_⟩
    intro e
    have := congrArg (fun X => (Areas.co ax X).2) e
    norm_num [hA, hC'] at this
  obtain ⟨F, hF⟩ := exists_foot ax htC
  have hlen : Pas.len ax A B = g := len_of_co ax hg.le (Or.inr (by rw [hA, hB]; simp))
    (by rw [hA, hB])
  have e := len_mul_foot ax hF
  rw [hD, hlen, abs_of_pos (mul_pos two_pos hg)] at e
  have hCF : Pas.len ax C F = 2 := by
    apply mul_left_cancel₀ hg.ne'; rw [e]; ring
  refine ⟨A, B, C, F, ht, hF, hlen, hCF, equalContent_of_measure ax hS (isPolygon_tri ht) ?_⟩
  rw [polyMeasure_tri ax ht, triMeasure_eq ax ht]
  change g = |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C)| / 2
  rw [hD, abs_of_pos (mul_pos two_pos hg)]; ring

theorem polygon_triangle_as_printed_false {S : Set P} (hS : IsPolyRegion (L := L) S) {A B C F : P}
    (ht : Tri.Nd (L := L) ⟨A, B, C⟩) (hF : IsFoot (L := L) C A B F)
    (hb : Pas.len ax A B = polyMeasure ax S) (hh : Pas.len ax C F = 1) :
    ¬EqualContent (L := L) S (TriRegion ⟨A, B, C⟩) := by
  intro h
  have hm := equalContent_measure ax h
  rw [polyMeasure_tri ax ht, triMeasure_eq ax ht] at hm
  have e := len_mul_foot ax hF
  rw [hb, hh, mul_one] at e
  change polyMeasure ax S = |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C)| / 2 at hm
  rw [← e] at hm
  have := polyMeasure_pos ax hS
  linarith

/-!
## [th.30] Theorem 30

*(§ 21)*

> Two polygons of equal content have always equal measures of area. Conversely, two polygons having equal measures of area are always of equal content.

**Lean reading.** `theorem30`: for polygons `S`, `T` and any axes `ax`, `S` and `T` are of equal
content iff `polyMeasure ax S = polyMeasure ax T`. The first half is unit
`s20.equal_content_measure`; the converse is Hilbert's argument (units `s21.triangles`,
`s21.polygon_triangle` corrected, and Theorem 24), `Areas.KEqContent.of_kmeasure`.

**Status.** proved
-/

/-- **Theorem 30.** -/
theorem theorem30 {S T : Set P} (hS : IsPolyRegion (L := L) S) (hT : IsPolyRegion (L := L) T) :
    EqualContent (L := L) S T ↔ polyMeasure ax S = polyMeasure ax T :=
  ⟨equalContent_measure ax, equalContent_of_measure ax hS hT⟩

theorem triMeasure_of_cong {t t' : Tri P} (ht : t.Nd (L := L)) (ht' : t'.Nd (L := L))
    (h : t.Cong t') : triMeasure ax t = triMeasure ax t' := by
  rw [triMeasure_eq ax ht, triMeasure_eq ax ht', ((Areas.cong_iff ax ht ht').1 h).abs_D]

/-- The measure of a rectangle is the product of two adjacent sides. -/
theorem rectangle_measure {A B C D : P} (h : IsRectangle (L := L) A B C D) :
    IsPolyRegion (L := L) (ParRegion A B C D) ∧
      polyMeasure ax (ParRegion A B C D) = Pas.len ax B A * Pas.len ax B C := by
  obtain ⟨hpar, hr⟩ := h
  obtain ⟨d, m⟩ := parallelogram_decomposition ax hpar
  refine ⟨⟨_, by simp, d⟩, ?_⟩
  rw [polyMeasure_eq_kmeasure, m]
  obtain ⟨-, hc⟩ := (parallelogram_iff ax).1 hpar
  have e1 : det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax D) =
      det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C) := by
    rw [hc]; simp only [par4, det3]; ring
  have hm := triMeasure_right ax hr
  obtain ⟨hAB, -, -⟩ := Pas.nc_ne ax hr.1
  have ht : Tri.Nd (L := L) ⟨B, A, C⟩ := ⟨fun hc => hr.1 hc.swap12, Ne.symm hAB⟩
  rw [triMeasure_eq ax ht] at hm
  change |det3 (Areas.co ax B) (Areas.co ax A) (Areas.co ax C)| / 2 = _ at hm
  rw [det3_swap, abs_neg] at hm
  rw [e1]
  linarith

/-!
## [s21.rectangles] A rectangle is determined by a side and its content

*(§ 21)*

> In particular, if two rectangles are of equal content and have one side in common, then their remaining sides are respectively congruent.

**Lean reading.** `rectangles_equal_content`: for rectangles `ABCD`, `A'B'C'D'` (right angles at
`B`, `B'`) with `AB ≡ A'B'` ("a side in common" read as congruent sides) and of equal content,
all the remaining sides are respectively congruent: `BC ≡ B'C'`, `CD ≡ C'D'`, `DA ≡ D'A'`.
Proof: the measures are `AB · BC` and `A'B' · B'C'` (`rectangle_measure`), equal by Theorem 30,
`AB ≡ A'B'` cancels, and opposite sides of a parallelogram are congruent
(`parallelogram_sides`).

**Status.** proved
-/

/-- Opposite sides of a parallelogram have equal lengths. -/
theorem parallelogram_sides {A B C D : P} (h : IsParallelogram (L := L) A B C D) :
    Pas.len ax C D = Pas.len ax A B ∧ Pas.len ax D A = Pas.len ax B C := by
  obtain ⟨-, hc⟩ := (parallelogram_iff ax).1 h
  constructor <;> apply Areas.len_eq_of_sq ax <;> rw [Areas.len_sq_co, Areas.len_sq_co, hc] <;>
    simp only [par4] <;> ring

theorem rectangles_equal_content {A B C D A' B' C' D' : P} (h : IsRectangle (L := L) A B C D)
    (h' : IsRectangle (L := L) A' B' C' D') (hs : SegCong A B A' B')
    (hc : EqualContent (L := L) (ParRegion A B C D) (ParRegion A' B' C' D')) :
    SegCong B C B' C' ∧ SegCong C D C' D' ∧ SegCong D A D' A' := by
  obtain ⟨-, D₀, hD₀, -⟩ := h.2
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) (ne12_of_between (Line := L) hD₀)
  obtain ⟨-, m⟩ := rectangle_measure ax h
  obtain ⟨-, m'⟩ := rectangle_measure ax h'
  have hm := equalContent_measure ax hc
  rw [m, m'] at hm
  obtain ⟨hAB, hCB, -⟩ := Pas.nc_ne ax h.1.1
  obtain ⟨hAB', hCB', -⟩ := Pas.nc_ne ax h'.1.1
  have hl : Pas.len ax B A = Pas.len ax B' A' :=
    (Pas.len_eq_iff ax (Ne.symm hAB) (Ne.symm hAB')).2
      (segCong_swap_left (Line := L) (segCong_swap_right (Line := L) hs))
  rw [hl] at hm
  have hBC := mul_left_cancel₀ (Pas.len_pos ax (Ne.symm hAB')).ne' hm
  have hlAB : Pas.len ax A B = Pas.len ax A' B' := (Pas.len_eq_iff ax hAB hAB').2 hs
  obtain ⟨s1, s2⟩ := parallelogram_sides ax h.1
  obtain ⟨s1', s2'⟩ := parallelogram_sides ax h'.1
  have ne_of : ∀ {X Y U V : P}, U ≠ V → Pas.len ax X Y = Pas.len ax U V → X ≠ Y := by
    intro X Y U V hUV e hXY
    rw [hXY, len_self'] at e
    exact (Pas.len_pos ax hUV).ne' e.symm
  refine ⟨(Pas.len_eq_iff ax (Ne.symm hCB) (Ne.symm hCB')).1 hBC,
    (Pas.len_eq_iff ax (ne_of hAB s1) (ne_of hAB' s1')).1 (by rw [s1, s1', hlAB]),
    (Pas.len_eq_iff ax (ne_of (Ne.symm hCB) s2) (ne_of (Ne.symm hCB') s2')).1
      (by rw [s2, s2', hBC])⟩

/-!
## [th.31] Theorem 31

*(§ 21)*

> If we decompose a rectangle into several triangles by means of straight lines and then omit one of these triangles, we can no longer make up completely the rectangle from the triangles which remain.

**Lean reading.** `theorem31`: if `l₁ ++ t :: l₂` is a decomposition of the rectangle
`ParRegion A B C D` (`IsRectangle`), there is no decomposition `m` of the rectangle whose
triangles are congruent, in order, to those of `l₁ ++ l₂` ("make up the rectangle from the
triangles which remain": congruent copies of them, without overlapping, covering it). The proof
works for every polygon (`theorem31_polygon`): the measure of the rectangle would be the sum of
the measures of the remaining triangles and also that sum plus `F(t) > 0`. The rectangle
hypothesis is not used.

**Status.** proved
-/

omit hC hP in
theorem sum_eq_of_forall₂ {α β M : Type*} [AddCommMonoid M] {f : α → M} {g : β → M} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => f a = g b) l m →
      (l.map f).sum = (m.map g).sum
  | _, _, .nil => rfl
  | _, _, .cons h rest => by
    simp only [List.map_cons, List.sum_cons, h, sum_eq_of_forall₂ rest]

theorem theorem31_polygon {S : Set P} {l₁ l₂ : List (Tri P)} {t : Tri P}
    (hd : IsDecomposition (L := L) S (l₁ ++ t :: l₂)) :
    ¬∃ m : List (Tri P), IsDecomposition (L := L) S m ∧ List.Forall₂ Tri.Cong (l₁ ++ l₂) m := by
  rintro ⟨m, hm, hc⟩
  have htnd : t.Nd (L := L) := hd.1 t (by simp)
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) htnd.2
  have e1 := polyMeasure_eq ax hd
  have e2 := polyMeasure_eq ax hm
  have hnd1 : ∀ r ∈ l₁ ++ l₂, r.Nd (L := L) := fun r hr => hd.1 r (by
    rcases List.mem_append.1 hr with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hcm : List.Forall₂ (fun a b => triMeasure ax a = triMeasure ax b) (l₁ ++ l₂) m := by
    refine forall₂_imp_mem hc hnd1 hm.1 ?_
    intro a b ha hb h
    exact triMeasure_of_cong ax ha hb h
  have hsum := sum_eq_of_forall₂ hcm
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at e1 hsum
  have := triMeasure_pos ax htnd
  linarith

/-- **Theorem 31.** -/
theorem theorem31 {A B C D : P} (_hR : IsRectangle (L := L) A B C D) {l₁ l₂ : List (Tri P)}
    {t : Tri P} (hd : IsDecomposition (L := L) (ParRegion A B C D) (l₁ ++ t :: l₂)) :
    ¬∃ m : List (Tri P), IsDecomposition (L := L) (ParRegion A B C D) m ∧
      List.Forall₂ Tri.Cong (l₁ ++ l₂) m :=
  theorem31_polygon hd

end Section21b


/-!
## [s21.schur_killing_stolz] Theorem 31 is independent of Archimedes's axiom

*(§ 21)*

> This theorem has been demonstrated by F. Schur [Note: *Sitzungsberichte der Dorpater Naturf. Ges.* 1892.] and by W. Killing, [Note: *Grundlagen der Geometrie*, Vol. 2, Chapter 5, § 5, 1898.] but by making use of the axiom of Archimedes. By O. Stolz, [Note: *Monatshefte für Math, und Phys.* 1894.] it has been regarded as an axiom. In the foregoing discussion, it has been shown that it is completely independent of the axiom of Archimedes.

**Lean reading.** "Independent of the axiom of Archimedes" means "provable without it":
`theorem31` assumes only `PlaneCongruence` and `PlaneParallels`. The historical claims about
Schur, Killing and Stolz are not checked.

**Status.** remark
-/

/-!
## [s21.not_sufficient] Theorem 31 alone does not give Theorem 28

*(§ 21)*

> However, when we disregard the axiom of Archimedes, this theorem (31) is not sufficient of itself to enable us to demonstrate Euclid's theorem concerning the equality of altitudes of triangles having equal content and equal bases. (Theorem 28.)

**Lean reading.** A methodological claim without a precise formal content: Theorem 28 *is*
provable from I 1–2, II–IV (`theorem28`), so "not sufficient of itself" refers to a proof using
only Theorem 31 and the elementary properties of content, which Hilbert does not delimit. What
can be stated precisely is the reason: Theorem 31 is a statement about decompositions (equal
area), Theorem 28 about equal content, and without Archimedes's axiom the two notions differ
(unit `s19.usual_demonstration`: two triangles of equal content that are not of equal area, in
the non-archimedean geometry, where Theorem 31 nevertheless holds).

**Status.** remark
-/

/-!
## [s21.cornerstone] Pascal's theorem is the corner-stone of the theory of areas

*(§ 21)*

> In the demonstration of theorems 28, 29, and 30, we have employed essentially the algebra of segments introduced in § 15, p. \pageref{folio46}, and as this depends substantially upon Pascal's theorem (theorem 21), we see that this theorem is really the corner-stone in the theory of areas.

**Lean reading.** The measures of area live in the field of segments `Pas.G ax` built in
Chapters III (Pascal.lean, Proportion.lean), whose commutativity is Pascal's theorem.

**Status.** remark
-/

/-!
## [s21.converse_pascal] Pascal's theorem from Theorems 27 and 28

*(§ 21)*

> We may, by the aid of theorems 27 and 28, easily establish the converse of Pascal's theorem.

**Lean reading.** The German original ("Umgekehrt läßt sich mit Hilfe der Sätze 27 und 28 der
Pascalsche Satz leicht beweisen") says that, *conversely*, Pascal's theorem itself follows from
Theorems 27 and 28; "the converse of Pascal's theorem" is a mistranslation. Read as a statement
of plane geometry, the claim is that Pascal's theorem holds in every plane satisfying the axioms
under which Theorems 27 and 28 were proved (I 1–2, II–IV): `converse_pascal` states Pascal's
theorem (Theorem 21: `CB' ∥ BC'` and `CA' ∥ AC'` give `BA' ∥ AB'`) under exactly the classes
`PlaneCongruence` and `PlaneParallels`. The area-theoretic derivation (by Theorem 27 the
triangles `OBB'`, `OCC'`, `OAA'` are of equal content, so the triangles `AB'B` and `AB'A'` on
the base `AB'` are of equal content, and Theorem 28 gives `BA' ∥ AB'`) is not formalized: in this
development the theory of areas is itself built on the field of segments, i.e. on Pascal's
theorem, so that route would be circular here; the proof cites `theorem21`.

**Status.** proved (reading)
-/

/-- **Pascal's theorem** (Theorem 21) in the setting of the theory of areas. -/
theorem converse_pascal {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [PlaneCongruence P L] [PlaneParallels P L] {g h : L}
    {O A B C A' B' C' : P} (hgh : g ≠ h) (hOg : O ∈ g) (hOh : O ∈ h) (hA : A ∈ g) (hB : B ∈ g)
    (hC : C ∈ g) (hA' : A' ∈ h) (hB' : B' ∈ h) (hC' : C' ∈ h) (hAO : A ≠ O) (hBO : B ≠ O)
    (hCO : C ≠ O) (hA'O : A' ≠ O) (hB'O : B' ≠ O) (hC'O : C' ≠ O) (hAB : A ≠ B)
    {l l' m m' n n' : L} (hl : C ∈ l ∧ B' ∈ l) (hl' : B ∈ l' ∧ C' ∈ l') (hm : C ∈ m ∧ A' ∈ m)
    (hm' : A ∈ m' ∧ C' ∈ m') (hn : B ∈ n ∧ A' ∈ n) (hn' : A ∈ n' ∧ B' ∈ n')
    (h1 : Parallel (Point := P) l l') (h2 : Parallel (Point := P) m m') :
    Parallel (Point := P) n n' :=
  theorem21 hgh hOg hOh hA hB hC hA' hB' hC' hAO hBO hCO hA'O hB'O hC'O hAB hl hl' hm hm' hn hn'
    h1 h2

section Comparison

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Pas.Axes P L)

/-!
## [s21.comparison] Smaller and larger content

*(§ 21)*

> Of two polygons $P$ and $Q$, we call $P$ the smaller or larger in content according as the measure of area $F(P)$ is less or greater than the measure of area $F(Q)$. From what has already been said, it is clear that the notions, equal content, smaller content, larger content, are mutually exclusive. Moreover, we easily see that a polygon, which lies wholly within another polygon, must always be of smaller content than the exterior one.

**Lean reading.** `SmallerContent ax S T`: `F(S) < F(T)` (for the measure with respect to the
axes `ax`; "larger" is `SmallerContent ax T S`). `content_exclusive`: for polygons, equal content
excludes smaller and larger content, and smaller excludes larger (Theorem 30); `content_trichotomy`
adds that one of the three holds. `smaller_content_of_subset`: a polygon `S ⊆ T`, `S ≠ T`, has
smaller content than `T` ("lies wholly within" read as a proper part): cutting the triangles of a
decomposition of `T` by the side lines of one of `S`, the pieces whose centroid lies in `S`
decompose `S` (closure lemma) and the others have positive measure (`Areas.kmeasure_lt_of_sub`).
`not_all_equal_content` answers the doubt of unit `s19.all_equal`: a triangle is not of equal
content with the half cut off by a median.

**Status.** proved
-/

/-- `S` is of **smaller content** than `T`. -/
def SmallerContent (S T : Set P) : Prop := polyMeasure ax S < polyMeasure ax T

theorem content_exclusive {S T : Set P} :
    (EqualContent (L := L) S T → ¬SmallerContent ax S T ∧ ¬SmallerContent ax T S) ∧
      (SmallerContent ax S T → ¬SmallerContent ax T S) := by
  refine ⟨fun h => ?_, fun h h' => lt_asymm h h'⟩
  have := equalContent_measure ax h
  unfold SmallerContent
  rw [this]
  exact ⟨lt_irrefl _, lt_irrefl _⟩

theorem content_trichotomy {S T : Set P} (hS : IsPolyRegion (L := L) S) (hT : IsPolyRegion (L := L) T) :
    EqualContent (L := L) S T ∨ SmallerContent ax S T ∨ SmallerContent ax T S := by
  rcases lt_trichotomy (polyMeasure ax S) (polyMeasure ax T) with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl (equalContent_of_measure ax hS hT h)
  · exact Or.inr (Or.inr h)

theorem smaller_content_of_subset {S T : Set P} (hS : IsPolyRegion (L := L) S)
    (hT : IsPolyRegion (L := L) T) (hsub : S ⊆ T) (hne : S ≠ T) : SmallerContent ax S T := by
  obtain ⟨lS, -, dS⟩ := hS
  obtain ⟨lT, -, dT⟩ := hT
  unfold SmallerContent
  rw [polyMeasure_eq_kmeasure, polyMeasure_eq_kmeasure]
  refine kmeasure_lt_of_sub ((isDecomposition_iff ax).1 dS) ((isDecomposition_iff ax).1 dT)
    (fun p hp => ?_) ?_
  · obtain ⟨X, hX, rfl⟩ := hp
    exact ⟨X, hsub hX, rfl⟩
  · obtain ⟨X, hXT, hXS⟩ : ∃ X, X ∈ T ∧ X ∉ S := by
      by_contra h
      push Not at h
      exact hne (Set.Subset.antisymm hsub h)
    exact ⟨Areas.co ax X, ⟨X, hXT, rfl⟩, fun h => hXS ((Areas.img_iff ax X).1 h)⟩

theorem not_all_equal_content {A B C : P} (ht : Tri.Nd (L := L) ⟨A, B, C⟩) :
    ∃ X : P, Between B X C ∧ ¬EqualContent (L := L) (TriRegion ⟨A, B, X⟩) (TriRegion ⟨A, B, C⟩) := by
  obtain ⟨ax⟩ := Areas.ax_of_ne (L := L) ht.2
  obtain ⟨-, hcb, -⟩ := Pas.nc_ne ax ht.1
  obtain ⟨X, hX⟩ := Areas.co_surj ax (lerp (1 / 2) (Areas.co ax B) (Areas.co ax C))
  have hb : Between B X C := (Areas.between_iff_co ax).2 ⟨Ne.symm hcb, 1 / 2, by norm_num,
    by norm_num, hX⟩
  refine ⟨X, hb, fun h => ?_⟩
  obtain ⟨d, -, -⟩ := transversal_decomposition ht hb
  have n1 : (Tri.mk A B X).Nd (L := L) := d.1 _ (by simp)
  have hm := equalContent_measure ax h
  rw [polyMeasure_tri ax n1, polyMeasure_tri ax ht, triMeasure_eq ax n1, triMeasure_eq ax ht] at hm
  change |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax X)| / 2 =
    |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C)| / 2 at hm
  rw [hX, show det3 (Areas.co ax A) (Areas.co ax B) (lerp (1 / 2) (Areas.co ax B) (Areas.co ax C)) =
    det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C) / 2 by unfold det3 lerp; ring,
    abs_div, abs_two] at hm
  have := abs_pos.2 ((Areas.nd_iff ax).1 ht)
  change 0 < |det3 (Areas.co ax A) (Areas.co ax B) (Areas.co ax C)| at this
  linarith

end Comparison


end HilbertFoundations
