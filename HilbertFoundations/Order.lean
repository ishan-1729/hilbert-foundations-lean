import HilbertFoundations.OrderAux

/-!
# Consequences of the axioms of connection and order (Theorems 1–8)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 2. Group I: Axioms of connection
* § 3. Group II: Axioms of Order
* § 4. Consequences of the axioms of connection and order
* § 5. Group III: Axiom of Parallels (Euclid's axiom)

The helper module `OrderAux.lean` (no units) contains the infrastructure:

* the plane theory of order **without II 4** (class `PlaneOrderCore`, namespace `OrderCore`):
  Pasch's axiom, a line does not meet the three sides of a triangle, the transitivity properties of
  `SameSide` / `OppositeSides`, Moore's four-point lemmas and the derivation of II 4;
* the linear theory of II 1–4 (namespace `OrderLin`): integer positions of three and four points
  (`three_points`, `four_points`), the transitivity lemmas `trans₁`, `trans₂`, the order of
  sequence `lineLt` of the points of a line with respect to two reference points and its
  description of betweenness (`between_iff_lineLt`), the linear order `lineOrder`;
* the **restriction of a space geometry to a plane** `α`: the instances
  `planeHasLines α : HasLines {A // A ∈ α} {a // LiesInPlane a α}`, `planeHasBetween α`,
  `planeConnection α`, `planeOrder α`, `planeParallels α`, the transfer lemmas
  `restrict_mem_iff`, `restrict_between_iff`, `restrict_collinear_iff`, `restrict_sameSide_iff`,
  `restrict_opp_iff`, and `restrict_planeOrderCore` (without II 4);
* incidence in space (`exists_plane_line_point`, `exists_mem_plane_not_mem`,
  `exists_plane_of_line`, `planes_meet_in_line`, `exists_plane_three`) and the sides of a line in a
  plane of space (namespace `OrderSpace`).

## API for other files

* `theorem1_lines`, `theorem1_planes`, `theorem1_line_plane`, `theorem2_line_point`,
  `theorem2_two_lines`;
* `axiomII4_of_others` (plane), `axiomII4_of_others_space` (space), `planeOrder_iff_core`,
  and the planeless counter-model `PlanelessPt`, `axiomII4_not_of_others_without_planes`;
* the plane restriction instances (above) and `planeConnection_of_space`, `planeOrder_of_space`,
  `planeParallels_of_space`;
* `theorem3`, `IsArrangement`, `theorem4`, `theorem4_degenerate`;
* `sameSidePt_iff_hilbert`, `sameSidePt_iff_sgn`, `sameSidePt_refl`, `sameSidePt_symm`,
  `sameSidePt_trans`, `sameSidePt_or_between`, `two_half_rays`;
* `SeparatesInto`, `SeparatesInto.unique`, `theorem5`, `theorem5_sides`, `sides_of_line_iff`,
  `theorem5_space`, `theorem5_space_sides`; for computations with sides use `OrderCore.sameSide_trans`,
  `OrderCore.opp_of_sameSide_opp`, `OrderCore.sameSide_of_opp_opp` (plane) and the `OrderSpace`
  versions (a plane of space);
* `BrokenLinePoints`, `IsBrokenLine`, `IsPolygon`, `PolygonPoints`, `IsSimplePolygon`,
  `DividesLikePolygon`, `PolygonTheorem` (the statement; proved as `polygonTheorem` in
  `OrderPolygon.lean`), `theorem6_triangle`, `theorem6_triangle_space`,
  and for triangles `TriangleLines`, `TriPts`, `TriInside`, `TriBeyond` with the lemmas
  `TriangleLines.exit`, `TriangleLines.crossbar`, `TriangleLines.divides`; the side lemmas
  `sameSide_of_between_mem`, `sameSide_of_between`;
* `SameSidePlane`, `OppositeSidesPlane`, `mem_plane_of_between`, `section_line`,
  `sameSidePlane_trans`, `oppPlane_of_sameSidePlane_opp`, `sameSidePlane_of_opp_opp`, `theorem7`,
  `theorem7_sides`, `sides_of_plane_iff`;
* `Theorem8Statement`, `theorem8`, `axiomIIIUnique_of_theorem8`, `axiomIIIUnique_iff_theorem8`,
  `theorem8_of_parallels` and the space versions `AxiomIIIUniqueSpace`, `Theorem8Space`,
  `theorem8_space`, `axiomIIIUniqueSpace_iff_theorem8Space`.
-/

namespace HilbertFoundations

universe u v w

variable {P : Type u} {L : Type v} {Pl : Type w}

/-!
## [th.1] Theorem 1

*(§ 2)*

> Two straight lines of a plane have either one point or no point in common; two planes have no point in common or a straight line in common; a plane and a straight line not lying in it have no point or one point in common.

**Lean reading.** Three statements. `theorem1_lines`: two *distinct* lines have at most one common
point ("either one point or no point"); this only uses I 2, and "of a plane" plays no role.
`theorem1_planes`: two distinct planes either have no common point, or there is a line `m` whose
points are *exactly* the common points of the two planes (I 1, I 2, I 4, I 5, I 6: the second
common point of I 6 spans a line lying in both planes by I 5, and a common point off that line
would make the planes equal by I 4). `theorem1_line_plane`: a line not lying in a plane has at most
one point in common with it (I 5). "Two lines", "two planes" are read as distinct ones (two equal
planes have a plane in common). Hilbert says the theorems follow from I 3–7; they use I 1–2 as
well, and the first statement only I 2.

**Status.** proved
-/

/-- **Theorem 1** (lines): two distinct lines have at most one common point. -/
theorem theorem1_lines [HasLines P L] [Connection P L] {a b : L} (hab : a ≠ b) {X Y : P}
    (hXa : X ∈ a) (hXb : X ∈ b) (hYa : Y ∈ a) (hYb : Y ∈ b) : X = Y :=
  eq_of_mem_of_mem hab hXa hXb hYa hYb

/-- **Theorem 1** (planes): two distinct planes have no common point, or their common points are
exactly the points of a line. -/
theorem theorem1_planes [HasLines P L] [HasPlanes P Pl] [SpaceConnection P L Pl] {α β : Pl}
    (hαβ : α ≠ β) :
    (¬∃ X : P, X ∈ α ∧ X ∈ β) ∨ ∃ m : L, ∀ X : P, X ∈ m ↔ X ∈ α ∧ X ∈ β := by
  by_cases h : ∃ X : P, X ∈ α ∧ X ∈ β
  · obtain ⟨X, hXα, hXβ⟩ := h
    exact Or.inr (planes_meet_in_line hαβ hXα hXβ)
  · exact Or.inl h

/-- **Theorem 1** (a line and a plane): a line not lying in a plane has at most one point in common
with it. -/
theorem theorem1_line_plane [HasLines P L] [HasPlanes P Pl] [SpaceConnection P L Pl] {a : L}
    {α : Pl} (h : ¬LiesInPlane (Point := P) a α) {X Y : P} (hXa : X ∈ a) (hXα : X ∈ α)
    (hYa : Y ∈ a) (hYα : Y ∈ α) : X = Y := by
  by_contra hXY
  exact h (liesInPlane_of_mem hXY hXa hYa hXα hYα)

/-!
## [th.2] Theorem 2

*(§ 2)*

> Through a straight line and a point not lying in it, or through two distinct straight lines having a common point, one and only one plane may be made to pass.

**Lean reading.** "One and only one" is existence and uniqueness (`∃!`). `theorem2_line_point`: for
`A ∉ a` there is exactly one plane `α` with `LiesInPlane a α` and `A ∈ α`. `theorem2_two_lines`:
for distinct lines `a`, `b` with a common point there is exactly one plane containing both. Proofs
from I 1–5 and I 7: two points of `a` (I 7) and `A` are non-collinear and span a plane (I 3), which
contains `a` by I 5 and is unique by I 4; for two lines, a point of each other than the common
point.

**Status.** proved
-/

/-- **Theorem 2** (a line and a point): exactly one plane passes through a line and a point off
it. -/
theorem theorem2_line_point [HasLines P L] [HasPlanes P Pl] [SpaceConnection P L Pl] {a : L}
    {A : P} (hA : A ∉ a) : ∃! α : Pl, LiesInPlane (Point := P) a α ∧ A ∈ α := by
  obtain ⟨α, ha, hAα⟩ := exists_plane_line_point (Pl := Pl) hA
  refine ⟨α, ⟨ha, hAα⟩, fun β ⟨hb, hAβ⟩ => ?_⟩
  obtain ⟨B, C, hBC, hB, hC⟩ := exists_two_points (Point := P) a
  have hn : ¬Collinear A B C := fun h => hA (mem_of_collinear h.perm231 hBC hB hC)
  exact plane_unique hn hAβ (hb B hB) (hb C hC) hAα (ha B hB) (ha C hC)

/-- **Theorem 2** (two lines): exactly one plane passes through two distinct lines with a common
point. -/
theorem theorem2_two_lines [HasLines P L] [HasPlanes P Pl] [SpaceConnection P L Pl] {a b : L}
    (hab : a ≠ b) {A : P} (hAa : A ∈ a) (hAb : A ∈ b) :
    ∃! α : Pl, LiesInPlane (Point := P) a α ∧ LiesInPlane (Point := P) b α := by
  have other : ∀ c : L, ∃ B : P, B ∈ c ∧ B ≠ A := fun c => by
    obtain ⟨X, Y, hXY, hX, hY⟩ := exists_two_points (Point := P) c
    by_cases h : X = A
    · exact ⟨Y, hY, fun e => hXY (h.trans e.symm)⟩
    · exact ⟨X, hX, h⟩
  obtain ⟨B, hBa, hBA⟩ := other a
  obtain ⟨C, hCb, hCA⟩ := other b
  have hn : ¬Collinear A B C := by
    intro h
    have hCa : C ∈ a := mem_of_collinear h hBA.symm hAa hBa
    exact hab (line_unique hCA.symm hAa hCa hAb hCb)
  obtain ⟨α, hAα, hBα, hCα⟩ := exists_plane (Plane := Pl) hn
  refine ⟨α, ⟨liesInPlane_of_mem hBA.symm hAa hBa hAα hBα,
    liesInPlane_of_mem hCA.symm hAb hCb hAα hCα⟩, fun β ⟨ha, hb⟩ => ?_⟩
  exact plane_unique hn (ha A hAa) (ha B hBa) (hb C hCb) hAα hBα hCα

/-!
## [s2.plane_restriction] The points and lines of a plane form a plane geometry (group I)

*(§ 2)*

> Axioms I, 1–2 contain statements concerning points and straight lines only; that is, concerning the elements of plane geometry.

**Lean reading.** Not a claim of Hilbert's but the construction that lets plane theorems be used in
every plane of space (required by Basic.lean). For a plane `α` of a space geometry, the points of
`α` and the lines lying in `α` are the subtypes `{A : P // A ∈ α}` and
`{a : L // LiesInPlane a α}`, with incidence and betweenness of space (instances `planeHasLines`,
`planeHasBetween` in OrderAux.lean). `planeConnection_of_space`: they satisfy group I of plane
geometry (I 1 and I 2 by I 1, I 2 and I 5; the line clause of I 7; three non-collinear points by the
plane clause of I 7). `restrict_collinear_iff` (collinearity in `α` is collinearity in space) uses
I 5 and the plane clause of I 7.

**Status.** proved
-/

/-- The points and lines of a plane of a space geometry satisfy group I of plane geometry. -/
theorem planeConnection_of_space [HasLines P L] [HasPlanes P Pl] [SpaceConnection P L Pl]
    (α : Pl) : PlaneConnection {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} :=
  inferInstance

/-!
## [s3.II4_dependent] Axiom II, 4 is a consequence of the other axioms of groups I and II

*(§ 3)*

> II, 4. *Any four points $A$, $B$, $C$, $D$ of a straight line can always be so arranged that $B$ shall lie between $A$ and $C$ and also between $A$ and $D$, and, furthermore, that $C$ shall lie between $A$ and $D$ and also between $B$ and $D$*.

**Lean reading.** `axiomII4_of_others`: in plane geometry, `AxiomII4` follows from group I of
plane geometry (`PlaneConnection`: I 1, I 2, two points on each line, three non-collinear points),
the presupposition `BetweenOnLine`, and II 1, II 2, II 3, II 5. This is E. H. Moore's theorem
(*Trans. AMS* 3, 1902; also R. L. Moore): the four-point axiom of this edition is redundant, so the
axioms of the book are **not independent**, against the claim of the Introduction ("a simple and
complete set of independent axioms"); later editions drop II 4. The proof (OrderAux.lean): Pasch's
axiom gives that a line cannot meet all three sides of a triangle (`OrderCore.pasch_excl`) and the
transitivity properties of the sides of a line, first for non-collinear points and then, with an
auxiliary point off their line, for collinear ones; with a line through `C` and a point off the
line `AC`, these give Moore's lemmas `between_of_between_between₁` (`B` between `A`, `C` and `C`
between `B`, `D` give `C` between `A`, `D`) and `between_of_between_between₂` (`B` between `A`, `C`
and `C` between `A`, `D` give `C` between `B`, `D`), and II 3 with these lemmas arranges any four
points. `planeOrder_iff_core`: hence `PlaneOrder P L` is equivalent to the bundle without II 4.
`axiomII4_of_others_space`: the same in space (from `SpaceConnection`, `BetweenOnLine`, II 1–3 and
the space form of II 5), under the extra hypothesis that some plane exists (`Nonempty Pl`): the
line is put in a plane and the plane theorem is applied to the restriction. This hypothesis cannot
be dropped under the literal reading of I 7 (Basic.lean, `ax.I7`): `axiomII4_not_of_others_without_planes`
exhibits a model with a single line (the rational numbers) and no plane, satisfying I 1–7,
`BetweenOnLine`, II 1–3 and (vacuously) II 5, with the usual betweenness changed on the three
points `0, 1, 2` only (`0` becomes the middle one); there II 4 fails, since `0` is between `1`,
`2` and `2` between `1`, `3`, but `0` is not between `1` and `3`. So in this edition the
dependence of II 4 rests on the existence of a plane, which Hilbert's I 7 is meant to provide.

**Status.** proved
-/

/-- **Axiom II 4 is a consequence of I 1–2, I 7 (plane), II 1–3 and II 5** (E. H. Moore). -/
theorem axiomII4_of_others [HasLines P L] [HasBetween P] [PlaneConnection P L]
    (hB : BetweenOnLine P) (h1 : AxiomII1 P) (h2 : AxiomII2 P) (h3 : AxiomII3 P)
    (h5 : AxiomII5 P) : AxiomII4 P :=
  @OrderCore.axiomII4 P L _ _
    { between_onLine := hB, ax_II1 := h1, ax_II2 := h2, ax_II3 := h3, ax_II5 := h5 }

/-- A plane geometry satisfies groups I and II iff it satisfies them without II 4. -/
theorem planeOrder_iff_core [HasLines P L] [HasBetween P] :
    PlaneOrder P L ↔ PlaneOrderCore P L :=
  ⟨fun h => @PlaneOrder.toPlaneOrderCore _ _ _ _ h, fun h =>
    { toPlaneConnection := h.toPlaneConnection
      between_onLine := h.between_onLine
      ax_II1 := h.ax_II1
      ax_II2 := h.ax_II2
      ax_II3 := h.ax_II3
      ax_II4 := @OrderCore.axiomII4 P L _ _ h
      ax_II5 := h.ax_II5 }⟩

/-- **II 4 follows from the other axioms of groups I and II in space**, if some plane exists. -/
theorem axiomII4_of_others_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [SpaceConnection P L Pl] [Nonempty Pl] (hB : BetweenOnLine P) (h1 : AxiomII1 P)
    (h2 : AxiomII2 P) (h3 : AxiomII3 P) (h5 : AxiomII5Space P) : AxiomII4 P := by
  intro A B C D a hA hB' hC hD hAB hAC hAD hBC hBD hCD
  obtain ⟨α, ha⟩ := exists_plane_of_line (P := P) (Pl := Pl) a
  have := restrict_planeOrderCore (α := α) hB h1 h2 h3 h5
  obtain ⟨σ, hσ⟩ := OrderCore.axiomII4 (P := {A : P // A ∈ α})
    (L := {a : L // LiesInPlane (Point := P) a α}) ⟨A, ha A hA⟩ ⟨B, ha B hB'⟩ ⟨C, ha C hC⟩
    ⟨D, ha D hD⟩ ⟨a, ha⟩ hA hB' hC hD (fun e => hAB (congrArg Subtype.val e))
    (fun e => hAC (congrArg Subtype.val e)) (fun e => hAD (congrArg Subtype.val e))
    (fun e => hBC (congrArg Subtype.val e)) (fun e => hBD (congrArg Subtype.val e))
    (fun e => hCD (congrArg Subtype.val e))
  refine ⟨σ, ?_⟩
  simpa only [restrict_between_iff, restrict_vec_apply] using hσ

/-- The points of the **planeless model**: the rational numbers (wrapped). -/
structure PlanelessPt where
  /-- The rational number of the point. -/
  val : ℚ

/-- The usual strict betweenness of rational numbers. -/
def ratBetween (x y z : ℚ) : Prop := (x < y ∧ y < z) ∨ (z < y ∧ y < x)

/-- The **twisted betweenness** on `ℚ`: the usual one, except that of the three points `0, 1, 2`
the point `0` (and not `1`) is the one lying between the other two. -/
def twistedBetween (x y z : ℚ) : Prop :=
  (({x, y, z} : Finset ℚ) = {0, 1, 2} ∧ y = 0) ∨
    (({x, y, z} : Finset ℚ) ≠ {0, 1, 2} ∧ ratBetween x y z)

/-- The planeless model has a single line (the unit type) on which every point lies. -/
instance : HasLines PlanelessPt Unit := ⟨fun _ _ => True⟩

/-- The planeless model has no plane. -/
instance : HasPlanes PlanelessPt Empty := ⟨fun _ e => e.elim⟩

instance : HasBetween PlanelessPt := ⟨fun x y z => twistedBetween x.val y.val z.val⟩

theorem planeless_between_iff {x y z : PlanelessPt} :
    Between x y z ↔ twistedBetween x.val y.val z.val := Iff.rfl

theorem planeless_ne_iff {x y : PlanelessPt} : x ≠ y ↔ x.val ≠ y.val :=
  ⟨fun h e => h (by cases x; cases y; simp_all), fun h e => h (e ▸ rfl)⟩

theorem planeless_collinear (A B C : PlanelessPt) : Collinear A B C :=
  ⟨(), trivial, trivial, trivial⟩

/-- The planeless model satisfies I 1–7, read literally. -/
theorem planeless_spaceConnection : SpaceConnection PlanelessPt Unit Empty where
  ax_I1 _ _ _ := ⟨(), trivial, trivial⟩
  ax_I2 _ _ _ _ _ _ _ _ _ := rfl
  ax_I7_line _ := ⟨⟨0⟩, ⟨1⟩, by simp, trivial, trivial⟩
  ax_I3 A B C h := absurd (planeless_collinear A B C) h
  ax_I4 A B C _ _ h := absurd (planeless_collinear A B C) h
  ax_I5 _ _ _ α := α.elim
  ax_I6 α := α.elim
  ax_I7_plane α := α.elim
  ax_I7_space := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, fun ⟨α, _⟩ => α.elim⟩

theorem finset3_perm12 (x y z : ℚ) : ({y, x, z} : Finset ℚ) = {x, y, z} :=
  Finset.insert_comm _ _ _

theorem finset3_perm23 (x y z : ℚ) : ({x, z, y} : Finset ℚ) = {x, y, z} := by
  rw [Finset.pair_comm]

theorem finset3_perm13 (x y z : ℚ) : ({z, y, x} : Finset ℚ) = {x, y, z} := by
  ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem twisted_mem {x y z : ℚ} (h : ({x, y, z} : Finset ℚ) = {0, 1, 2}) :
    x ∈ ({0, 1, 2} : Finset ℚ) ∧ y ∈ ({0, 1, 2} : Finset ℚ) ∧ z ∈ ({0, 1, 2} : Finset ℚ) := by
  rw [← h]; simp

theorem twisted_zero {x y z : ℚ} (h : ({x, y, z} : Finset ℚ) = {0, 1, 2}) :
    x = 0 ∨ y = 0 ∨ z = 0 := by
  have : (0 : ℚ) ∈ ({x, y, z} : Finset ℚ) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

theorem twisted_distinct {x y z : ℚ} (h : ({x, y, z} : Finset ℚ) = {0, 1, 2}) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have h3 : ({x, y, z} : Finset ℚ).card = 3 := by rw [h]; simp
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · subst e
    have : ({x, x, z} : Finset ℚ) = {x, z} := by simp
    rw [this] at h3
    exact absurd h3 (by have := Finset.card_le_two (a := x) (b := z); omega)
  · subst e
    have : ({x, y, x} : Finset ℚ) = {x, y} := by
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [this] at h3
    exact absurd h3 (by have := Finset.card_le_two (a := x) (b := y); omega)
  · subst e
    have : ({x, y, y} : Finset ℚ) = {x, y} := by simp
    rw [this] at h3
    exact absurd h3 (by have := Finset.card_le_two (a := x) (b := y); omega)

theorem not_twisted_of_not_mem₂ {x y z : ℚ} (hy : y ∉ ({0, 1, 2} : Finset ℚ)) :
    ({x, y, z} : Finset ℚ) ≠ {0, 1, 2} := fun h => hy (twisted_mem h).2.1

theorem not_twisted_of_not_mem₃ {x y z : ℚ} (hz : z ∉ ({0, 1, 2} : Finset ℚ)) :
    ({x, y, z} : Finset ℚ) ≠ {0, 1, 2} := fun h => hz (twisted_mem h).2.2

theorem planeless_betweenOnLine : BetweenOnLine PlanelessPt := by
  intro A B C h
  rw [planeless_between_iff] at h
  simp only [planeless_ne_iff]
  refine ⟨?_, ?_, ?_, planeless_collinear A B C⟩ <;>
  · rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · have := twisted_distinct h1
      first | exact this.1 | exact this.2.1 | exact this.2.2
    · intro e
      unfold ratBetween at h2
      rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith

theorem planeless_axiomII1 : AxiomII1 PlanelessPt := by
  intro A B C _ h
  rw [planeless_between_iff] at h ⊢
  unfold twistedBetween ratBetween at *
  rw [finset3_perm13 A.val B.val C.val]
  tauto

theorem planeless_axiomII2 : AxiomII2 PlanelessPt := by
  intro A C _ _ _ hAC
  rw [planeless_ne_iff] at hAC
  simp only [planeless_between_iff]
  rcases lt_or_gt_of_ne hAC with h | h
  · obtain ⟨B, hB, hB'⟩ := (Set.Ioo_infinite h).exists_notMem_finset ({0, 1, 2} : Finset ℚ)
    obtain ⟨D, hD, hD'⟩ :=
      (Set.Ioi_infinite C.val).exists_notMem_finset ({0, 1, 2} : Finset ℚ)
    exact ⟨⟨⟨B⟩, Or.inr ⟨not_twisted_of_not_mem₂ hB', Or.inl hB⟩⟩,
      ⟨⟨D⟩, Or.inr ⟨not_twisted_of_not_mem₃ hD', Or.inl ⟨h, hD⟩⟩⟩⟩
  · obtain ⟨B, hB, hB'⟩ := (Set.Ioo_infinite h).exists_notMem_finset ({0, 1, 2} : Finset ℚ)
    obtain ⟨D, hD, hD'⟩ :=
      (Set.Iio_infinite C.val).exists_notMem_finset ({0, 1, 2} : Finset ℚ)
    exact ⟨⟨⟨B⟩, Or.inr ⟨not_twisted_of_not_mem₂ hB', Or.inr ⟨hB.1, hB.2⟩⟩⟩,
      ⟨⟨D⟩, Or.inr ⟨not_twisted_of_not_mem₃ hD', Or.inr ⟨hD, h⟩⟩⟩⟩

theorem ratBetween_axiomII3 {x y z : ℚ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (ratBetween y x z ∨ ratBetween x y z ∨ ratBetween x z y) ∧
      ¬(ratBetween y x z ∧ ratBetween x y z) ∧ ¬(ratBetween y x z ∧ ratBetween x z y) ∧
      ¬(ratBetween x y z ∧ ratBetween x z y) := by
  unfold ratBetween
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3 <;>
    first
    | (exfalso; linarith)
    | (have := lt_asymm h1; have := lt_asymm h2; have := lt_asymm h3; simp_all)

theorem planeless_axiomII3 : AxiomII3 PlanelessPt := by
  intro A B C _ hAB hAC hBC
  simp only [planeless_ne_iff] at hAB hAC hBC
  simp only [planeless_between_iff]
  unfold twistedBetween
  rw [finset3_perm12 A.val B.val C.val, finset3_perm23 A.val B.val C.val]
  by_cases ht : ({A.val, B.val, C.val} : Finset ℚ) = {0, 1, 2}
  · have hz := twisted_zero ht
    simp only [ht, ne_eq, not_true_eq_false, false_and, or_false, true_and]
    refine ⟨hz, ?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩
    · exact hAB (h1.trans h2.symm)
    · exact hAC (h1.trans h2.symm)
    · exact hBC (h1.trans h2.symm)
  · simp only [ht, false_and, false_or, ne_eq, not_false_eq_true, true_and]
    exact ratBetween_axiomII3 hAB hAC hBC

/-- II 4 fails in the planeless model: `0` lies between `1` and `2` (the twist) and `2` between `1`
and `3`, which with II 4 would put `0` between `1` and `3`. -/
theorem planeless_not_axiomII4 : ¬AxiomII4 PlanelessPt := by
  intro h4
  let _ : LineOrder PlanelessPt Unit :=
    { toConnection := planeless_spaceConnection.toConnection
      between_onLine := planeless_betweenOnLine
      ax_II1 := planeless_axiomII1
      ax_II2 := planeless_axiomII2
      ax_II3 := planeless_axiomII3
      ax_II4 := h4 }
  have h3 : (3 : ℚ) ∉ ({0, 1, 2} : Finset ℚ) := by norm_num
  have h1 : Between (⟨1⟩ : PlanelessPt) ⟨0⟩ ⟨2⟩ :=
    Or.inl ⟨finset3_perm12 0 1 2, rfl⟩
  have h2 : Between (⟨1⟩ : PlanelessPt) ⟨2⟩ ⟨3⟩ :=
    Or.inr ⟨not_twisted_of_not_mem₃ h3, Or.inl ⟨by norm_num, by norm_num⟩⟩
  have h := (OrderLin.trans₂ (L := Unit) h1 h2).1
  rw [planeless_between_iff] at h
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  · exact h3 (by rw [← h]; simp)
  · unfold ratBetween at h
    norm_num at h

/-- **Without a plane, II 4 is independent of the other axioms of groups I and II**: the planeless
model satisfies I 1–7 (literal reading), `BetweenOnLine`, II 1, II 2, II 3 and II 5 (in its space
form, vacuously), but not II 4. -/
theorem axiomII4_not_of_others_without_planes :
    SpaceConnection PlanelessPt Unit Empty ∧ BetweenOnLine PlanelessPt ∧
      AxiomII1 PlanelessPt ∧ AxiomII2 PlanelessPt ∧ AxiomII3 PlanelessPt ∧
      AxiomII5Space PlanelessPt ∧ ¬AxiomII4 PlanelessPt :=
  ⟨planeless_spaceConnection, planeless_betweenOnLine, planeless_axiomII1, planeless_axiomII2,
    planeless_axiomII3, fun _ _ _ α => α.elim, planeless_not_axiomII4⟩

/-!
## [s3.plane_restriction] The points and lines of a plane form a plane geometry (group II)

*(§ 3)*

> Axiom II, 5 relates to the elements of plane geometry and, consequently, shall be called the *plane axiom of group II*.

**Lean reading.** Not a claim of Hilbert's but the construction used to transfer plane theorems to
the planes of space. For a plane `α` of a geometry satisfying `SpaceOrder` (I 1–7, II 1–5 in
space), the restriction `{A // A ∈ α}`, `{a // LiesInPlane a α}` satisfies `PlaneOrder`
(`planeOrder_of_space`, the instance `planeOrder` of OrderAux.lean): II 1, II 3, II 4 restrict
directly, II 2 because the points it provides lie on the given line (`BetweenOnLine`, I 2) and
hence in `α` (I 5), and II 5 is the space form of II 5 for the plane `α`. In the same way III in
space gives III in each plane (`planeParallels_of_space`). The transfer lemmas
`restrict_sameSide_iff`, `restrict_opp_iff` identify the sides of a line in the restricted geometry
with the sides in space.

**Status.** proved
-/

/-- The points and lines of a plane of a space geometry satisfy groups I and II of plane
geometry. -/
theorem planeOrder_of_space [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [SpaceOrder P L Pl] (α : Pl) :
    PlaneOrder {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} :=
  inferInstance

/-- The points and lines of a plane of a space geometry satisfy groups I and III of plane
geometry. -/
theorem planeParallels_of_space [HasLines P L] [HasPlanes P Pl] [SpaceParallels P L Pl]
    (α : Pl) : PlaneParallels {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} :=
  inferInstance

/-!
## [th.3] Theorem 3

*(§ 4)*

> Between any two points of a straight line, there always exists an unlimited number of points.

**Lean reading.** Hilbert derives Theorems 3 and 4 "by the aid of the four linear axioms II, 1–4",
so only `LineOrder` (I 1–2, two points on a line, `BetweenOnLine`, II 1–4) is assumed.
"An unlimited number" is read as infinitely many: `theorem3` says that for `A ≠ C` the set
`Seg A C` of points between `A` and `C` is infinite. Proof: a sequence `B₀, B₁, …` with `B₀`
between `A` and `C` and `Bₙ₊₁` between `A` and `Bₙ` (II 2); by `OrderLin.trans₂` (from II 4) every
`Bₙ` is between `A` and `C` and `Bₙ` is between `A` and `Bₘ` for `m < n`, so the `Bₙ` are distinct.

**Status.** proved
-/

/-- **Theorem 3.** Between two distinct points there are infinitely many points. -/
theorem theorem3 [HasLines P L] [HasBetween P] [LineOrder P L] {A C : P} (h : A ≠ C) :
    (Seg A C).Infinite := by
  obtain ⟨B₀, hB₀⟩ := exists_between (Line := L) h
  have hn : ∀ X : P, ∃ Y : P, A ≠ X → Between A Y X := fun X => by
    by_cases hX : A = X
    · exact ⟨A, fun h' => absurd hX h'⟩
    · obtain ⟨Y, hY⟩ := exists_between (Line := L) hX
      exact ⟨Y, fun _ => hY⟩
  choose nxt hnxt using hn
  let f : ℕ → P := fun n => Nat.rec (motive := fun _ => P) B₀ (fun _ X => nxt X) n
  have hfs : ∀ n, f (n + 1) = nxt (f n) := fun _ => rfl
  have key : ∀ n, Between A (f n) C ∧ ∀ m, m < n → Between A (f n) (f m) := by
    intro n
    induction n with
    | zero => exact ⟨hB₀, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
    | succ n ih =>
      have h1 : Between A (f (n + 1)) (f n) := by
        rw [hfs]; exact hnxt _ (ne12_of_between ih.1)
      refine ⟨(OrderLin.trans₂ h1 ih.1).1, fun m hm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
      · exact (OrderLin.trans₂ h1 (ih.2 m hm)).1
      · exact h1
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ (fun n => (key n).1)
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact ne23_of_between ((key n).2 m h') hmn.symm
  · exact ne23_of_between ((key m).2 n h') hmn

/-!
## [th.4] Theorem 4

*(§ 4)*

> If we have given any finite number of points situated upon a straight line, we can always arrange them in a sequence $A$, $B$, $C$, $D$, $E$,$\ldots$, $K$ so that $B$ shall lie between $A$ and $C$, $D$, $E$,$\ldots$, $K$; $C$ between $A$, $B$ and $D$, $E$,\ldots, $K$; $D$ between $A$, $B$, $C$ and $E$,\ldots$K$, etc. Aside from this order of sequence, there exists but one other possessing this property namely, the reverse order $K$,\ldots, $E$, $D$, $C$, $B$, $A$.

**Lean reading.** From the linear axioms only (`LineOrder`). A finite set `S` of points of a line
`a` with `n` elements; an *arrangement* of `S` is a bijection `f : Fin n → S` (injective with range
`S`) such that `f j` lies between `f i` and `f k` whenever `i < j < k` (`IsArrangement`), which is
Hilbert's condition ("`B` between `A` and `C, D, …`; `C` between `A, B` and `D, …`"). `theorem4`:
an arrangement `f` exists; its reverse `f ∘ Fin.rev` is an arrangement; every arrangement is `f` or
its reverse; and the reverse differs from `f` as soon as `n ≥ 2`. So for `n ≥ 2` there are exactly
two arrangements, as Hilbert says. As printed the second sentence is false for `n ≤ 1` (a single
point, or none): then the reverse order *is* the given order (`theorem4_degenerate`: every
`f : Fin n → P` with `n ≤ 1` equals `f ∘ Fin.rev`), so there is no "other" order of sequence at
all; the corrected statement is the one proved, "exactly two orders when `n ≥ 2`, exactly one when
`n ≤ 1`" (uniqueness up to reversal holds for every `n`). Proof: two points
`O ≠ U` of `a` (I 7) define the order of sequence `OrderLin.lineLt O U` of the points of `a` (a sign
with respect to `O`, then betweenness with `O`); it is a strict total order describing betweenness
(`OrderLin.between_iff_lineLt`, from integer positions of four points given by II 4); `S` sorted in
this order is an arrangement, and an arrangement is strictly monotone or antitone for it.

**Status.** proved (corrected)
-/

/-- `f 0, f 1, …` are **arranged in a sequence**: each lies between any earlier and any later
one. -/
def IsArrangement [HasBetween P] {n : ℕ} (f : Fin n → P) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → Between (f i) (f j) (f k)

/-- **Theorem 4.** A finite set of points of a line can be arranged in a sequence, and in exactly
one other way, the reverse sequence (when it has at least two points). -/
theorem theorem4 [HasLines P L] [HasBetween P] [LineOrder P L] (a : L) (S : Finset P)
    (hS : ∀ X ∈ S, X ∈ a) :
    ∃ f : Fin S.card → P, Function.Injective f ∧ Set.range f = ↑S ∧ IsArrangement f ∧
      IsArrangement (f ∘ Fin.rev) ∧ (2 ≤ S.card → f ∘ Fin.rev ≠ f) ∧
      ∀ g : Fin S.card → P, Function.Injective g → Set.range g = ↑S → IsArrangement g →
        g = f ∨ g = f ∘ Fin.rev := by
  classical
  obtain ⟨O, U, hOU, hO, hU⟩ := exists_two_points (Point := P) a
  let _ : LinearOrder {X : P // X ∈ a} := OrderLin.lineOrder hO hU hOU
  have hlt : ∀ X Y : {X : P // X ∈ a}, X < Y ↔ OrderLin.lineLt O U (X : P) Y :=
    fun _ _ => Iff.rfl
  have hval : ∀ X Y : {X : P // X ∈ a}, X ≠ Y → (X : P) ≠ Y :=
    fun X Y h e => h (Subtype.ext e)
  have btw_iff : ∀ X Y Z : {X : P // X ∈ a}, X ≠ Y → X ≠ Z → Y ≠ Z →
      (Between (X : P) Y Z ↔ (X < Y ∧ Y < Z) ∨ (Z < Y ∧ Y < X)) := by
    intro X Y Z h1 h2 h3
    rw [hlt, hlt, hlt, hlt]
    exact OrderLin.between_iff_lineLt hO hU hOU X.2 Y.2 Z.2 (hval _ _ h1) (hval _ _ h2)
      (hval _ _ h3)
  set S' : Finset {X : P // X ∈ a} := S.subtype (· ∈ a) with hS'
  have hcard : S'.card = S.card := by
    rw [hS', Finset.card_subtype, Finset.filter_true_of_mem hS]
  set e := S'.orderEmbOfFin hcard
  have hmemS' : ∀ X : {X : P // X ∈ a}, X ∈ S' ↔ (X : P) ∈ S := fun X => Finset.mem_subtype
  refine ⟨fun i => (e i : P), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    exact e.injective (Subtype.ext h)
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (hmemS' _).1 (Finset.orderEmbOfFin_mem S' hcard i)
    · intro hx
      have : (⟨x, hS x hx⟩ : {X : P // X ∈ a}) ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]; exact (hmemS' _).2 hx
      obtain ⟨i, hi⟩ := this
      exact ⟨i, by simp [hi]⟩
  · intro i j k hij hjk
    exact (btw_iff _ _ _ (e.strictMono hij).ne (e.strictMono (hij.trans hjk)).ne
      (e.strictMono hjk).ne).2 (Or.inl ⟨e.strictMono hij, e.strictMono hjk⟩)
  · intro i j k hij hjk
    have h1 : k.rev < j.rev := Fin.rev_lt_rev.2 hjk
    have h2 : j.rev < i.rev := Fin.rev_lt_rev.2 hij
    exact (btw_iff _ _ _ (e.strictMono h2).ne' (e.strictMono (h1.trans h2)).ne'
      (e.strictMono h1).ne').2 (Or.inr ⟨e.strictMono h1, e.strictMono h2⟩)
  · intro hn heq
    have h0 := congrFun heq ⟨0, by omega⟩
    have := Fin.ext_iff.1 (e.injective (Subtype.ext h0))
    simp only [Fin.val_rev] at this
    omega
  · intro g hg hgr harr
    have hgS : ∀ i, g i ∈ S := fun i => by
      have : g i ∈ Set.range g := ⟨i, rfl⟩
      rw [hgr] at this; exact this
    let g' : Fin S.card → {X : P // X ∈ a} := fun i => ⟨g i, hS _ (hgS i)⟩
    have hg' : Function.Injective g' := fun i j h => hg (congrArg Subtype.val h)
    have hg'S : ∀ i, g' i ∈ S' := fun i => (hmemS' _).2 (hgS i)
    have hbtw : ∀ i j k : Fin S.card, i < j → j < k →
        (g' i < g' j ∧ g' j < g' k) ∨ (g' k < g' j ∧ g' j < g' i) := by
      intro i j k hij hjk
      exact (btw_iff _ _ _ (hg'.ne hij.ne) (hg'.ne (hij.trans hjk).ne) (hg'.ne hjk.ne)).1
        (harr i j k hij hjk)
    rcases OrderLin.strictMono_or_strictAnti_of_btw g' hg' hbtw with hm | hm
    · left
      have := Finset.orderEmbOfFin_unique hcard hg'S hm
      funext i
      exact congrArg Subtype.val (congrFun this i)
    · right
      have hm' : StrictMono (g' ∘ Fin.rev) := fun i j hij => hm (Fin.rev_lt_rev.2 hij)
      have := Finset.orderEmbOfFin_unique hcard (fun i => hg'S _) hm'
      funext i
      have := congrArg Subtype.val (congrFun this i.rev)
      simpa [g'] using this

/-- **Theorem 4, the degenerate case** (where Hilbert's "one other" order fails): for at most one
point the reverse of an arrangement is the arrangement itself, so there is no other order. -/
theorem theorem4_degenerate {n : ℕ} (hn : n ≤ 1) (f : Fin n → P) : f ∘ Fin.rev = f := by
  funext i
  simp only [Function.comp_apply]
  congr 1
  ext
  simp only [Fin.val_rev]
  have := i.2
  omega

/-!
## [s4.same_side_of_point] Points on the same side of a point

*(§ 4)*

> If $A$, $A'$, $O$, $B$ are four points of a straight line $a$, where $O$ lies between $A$ and $B$ but not between $A$ and $A'$, then we may say: The points $A$, $A'$ are situated *on the line a upon one and the same side of the point $O$,* and the points $A$, $B$ are situated *on the straight line $a$ upon different sides of the point $O$*.

**Lean reading.** The definition is `SameSidePt` of Basic.lean (unit `s4.side_of_point`), which
drops the auxiliary point `B`. `sameSidePt_iff_hilbert`: for points `A`, `A' ≠ O` of a line through
`O`, `SameSidePt O A A'` holds iff, as Hilbert says, there is a point `B` of the line with `O`
between `A` and `B` but not between `A` and `A'` (such a `B` exists by II 2). "Different sides" is
`Between A O B`, and `sameSidePt_or_between`: two points `≠ O` of the line are on the same side or
on different sides, not both. Hilbert uses tacitly that "the same side" is an equivalence relation
on the points `≠ O` of the line (otherwise the half-ray of the next unit is not well defined):
`sameSidePt_refl`, `sameSidePt_symm`, `sameSidePt_trans`, from II 1–4 (`LineOrder`). The key is
`sameSidePt_iff_sgn`: two points are on the same side of `O` iff they have the same sign
`OrderLin.sgn O U` for any reference point `U ≠ O` of the line (the sign rule, from the positions of
four points).

**Status.** proved
-/

section SideOfPoint

variable [HasLines P L] [HasBetween P] [hO : LineOrder P L] {a : L} {O A A' B U X Y Z : P}
include hO

/-- Hilbert's definition of "the same side of `O`", with the auxiliary point `B`. -/
theorem sameSidePt_iff_hilbert (hOa : O ∈ a) (hA : A ∈ a) (hA' : A' ∈ a) (hAO : A ≠ O)
    (hA'O : A' ≠ O) :
    SameSidePt O A A' ↔ ∃ B : P, B ∈ a ∧ Between A O B ∧ ¬Between A O A' := by
  constructor
  · rintro ⟨-, -, -, h⟩
    obtain ⟨B, hB⟩ := exists_beyond (Line := L) hAO
    exact ⟨B, mem_of_collinear (collinear_of_between hB) hAO hA hOa, hB, h⟩
  · rintro ⟨B, -, -, h⟩
    exact ⟨hAO, hA'O, collinear_of_mem hA hOa hA', h⟩

omit hO in
/-- Two points `≠ O` of a line through `O` are on the same side of `O` or on different sides, and
not both. -/
theorem sameSidePt_or_between (hOa : O ∈ a) (hA : A ∈ a) (hB : B ∈ a) (hAO : A ≠ O)
    (hBO : B ≠ O) : (SameSidePt O A B ∨ Between A O B) ∧ ¬(SameSidePt O A B ∧ Between A O B) := by
  refine ⟨?_, fun ⟨h1, h2⟩ => h1.2.2.2 h2⟩
  by_cases h : Between A O B
  · exact Or.inr h
  · exact Or.inl ⟨hAO, hBO, collinear_of_mem hA hOa hB, h⟩

/-- Same side of `O` means same sign with respect to `O` and any reference point `U ≠ O`. -/
theorem sameSidePt_iff_sgn (hOa : O ∈ a) (hU : U ∈ a) (hOU : O ≠ U) (hX : X ∈ a) (hY : Y ∈ a)
    (hXO : X ≠ O) (hYO : Y ≠ O) :
    SameSidePt O X Y ↔ OrderLin.sgn O U X = OrderLin.sgn O U Y := by
  by_cases hXY : X = Y
  · subst hXY
    exact ⟨fun _ => rfl, fun _ =>
      ⟨hXO, hXO, collinear_of_mem hX hOa hX, not_between_self (Line := L)⟩⟩
  · unfold SameSidePt
    rw [OrderLin.sign_rule hOa hU hOU hX hY hXO hYO hXY]
    constructor
    · rintro ⟨-, -, -, h⟩
      by_contra h'
      exact h h'
    · intro h
      exact ⟨hXO, hYO, collinear_of_mem hX hOa hY, fun h' => h' h⟩

theorem sameSidePt_refl (hOa : O ∈ a) (hX : X ∈ a) (hXO : X ≠ O) : SameSidePt O X X :=
  ⟨hXO, hXO, collinear_of_mem hX hOa hX, not_between_self (Line := L)⟩

theorem sameSidePt_symm (h : SameSidePt O X Y) : SameSidePt O Y X :=
  ⟨h.2.1, h.1, h.2.2.1.swap13, fun h' => h.2.2.2 (between_symm h')⟩

theorem sameSidePt_trans (h1 : SameSidePt O X Y) (h2 : SameSidePt O Y Z) : SameSidePt O X Z := by
  have hXO := h1.1
  have hYO := h1.2.1
  have hZO := h2.2.1
  obtain ⟨g, hXg, hOg, hYg⟩ := h1.2.2.1
  have hZg : Z ∈ g := mem_of_collinear h2.2.2.1 hYO hYg hOg
  have e1 := (sameSidePt_iff_sgn hOg hXg hXO.symm hXg hYg hXO hYO).1 h1
  have e2 := (sameSidePt_iff_sgn hOg hXg hXO.symm hYg hZg hYO hZO).1 h2
  exact (sameSidePt_iff_sgn hOg hXg hXO.symm hXg hZg hXO hZO).2 (e1.trans e2)

end SideOfPoint

/-!
## [s4.two_half_rays] Each point divides a line into two half-rays

*(§ 4)*

> All of the points of $a$ which lie upon the same side of $O$, when taken together, are called the *half-ray* emanating from $O$. Hence, each point of a straight line divides it into two half-rays.

**Lean reading.** The definition is `ray O A` of Basic.lean (unit `s4.half_ray`). The claim
("hence …") is `two_half_rays`: for a point `O` of a line `a` there are points `A`, `B` of `a` with
`O` between them such that the half-rays `ray O A` and `ray O B` are disjoint, together consist of
all the points of `a` other than `O`, and every half-ray `ray O X` drawn from `O` through a point
`X ≠ O` of `a` is one of the two. (They are distinct, being disjoint and containing `A`, `B`.) From
II 1–4 and I 7 (`LineOrder`); the proof describes the half-rays by the sign `OrderLin.sgn O A`.

**Status.** proved
-/

/-- **Each point of a line divides it into two half-rays.** -/
theorem two_half_rays [HasLines P L] [HasBetween P] [LineOrder P L] {a : L} {O : P}
    (hO : O ∈ a) :
    ∃ A B : P, A ∈ a ∧ B ∈ a ∧ Between A O B ∧ Disjoint (ray O A) (ray O B) ∧
      ray O A ∪ ray O B = {X | X ∈ a ∧ X ≠ O} ∧
      ∀ X, X ∈ a → X ≠ O → ray O X = ray O A ∨ ray O X = ray O B := by
  obtain ⟨A, hA, hAO⟩ : ∃ A : P, A ∈ a ∧ A ≠ O := by
    obtain ⟨X, Y, hXY, hX, hY⟩ := exists_two_points (Point := P) a
    by_cases h : X = O
    · exact ⟨Y, hY, fun e => hXY (h.trans e.symm)⟩
    · exact ⟨X, hX, h⟩
  obtain ⟨B, hAOB⟩ := exists_beyond (Line := L) hAO
  have hB : B ∈ a := mem_of_collinear (collinear_of_between hAOB) hAO hA hO
  have hBO : B ≠ O := (ne23_of_between hAOB).symm
  have mem : ∀ Y X : P, X ∈ a → X ≠ O →
      (Y ∈ ray O X ↔ Y ∈ a ∧ Y ≠ O ∧ OrderLin.sgn O A Y = OrderLin.sgn O A X) := by
    intro Y X hX hXO
    rw [mem_ray]
    constructor
    · intro h
      have hY : Y ∈ a := mem_of_collinear h.2.2.1 hXO hX hO
      exact ⟨hY, h.2.1, ((sameSidePt_iff_sgn hO hA hAO.symm hX hY hXO h.2.1).1 h).symm⟩
    · rintro ⟨hY, hYO, hs⟩
      exact (sameSidePt_iff_sgn hO hA hAO.symm hX hY hXO hYO).2 hs.symm
  have sA : OrderLin.sgn O A A = 1 := by
    rcases OrderLin.sgn_of_ne (U := A) hAO with h | h
    · exact absurd h.2 (not_between_self (Line := L))
    · exact h.1
  have sB : OrderLin.sgn O A B = -1 := by
    rcases OrderLin.sgn_of_ne (U := A) hBO with h | h
    · exact h.1
    · exact absurd hAOB h.2
  refine ⟨A, B, hA, hB, hAOB, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.2 fun Y h1 h2 => ?_
    rw [mem Y A hA hAO] at h1
    rw [mem Y B hB hBO] at h2
    omega
  · ext Y
    simp only [Set.mem_union, Set.mem_ofPred_eq, mem Y A hA hAO, mem Y B hB hBO, sA, sB]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases OrderLin.sgn_of_ne (U := A) h2 with h | h
      · exact Or.inr ⟨h1, h2, h.1⟩
      · exact Or.inl ⟨h1, h2, h.1⟩
  · intro X hX hXO
    rcases OrderLin.sgn_of_ne (U := A) hXO with h | h
    · right
      ext Y
      rw [mem Y X hX hXO, mem Y B hB hBO, h.1, sB]
    · left
      ext Y
      rw [mem Y X hX hXO, mem Y A hA hAO, h.1, sA]

/-!
## [th.5] Theorem 5

*(§ 4)*

> Every straight line $a$, which lies in a plane $\alpha$, divides the remaining points of this plane into two regions having the following properties: Every point $A$ of the one region determines with each point $B$ of the other region a segment $AB$ containing a point of the straight line $a$. On the other hand, any two points $A$, $A'$ of the same region determine a segment $AA'$ containing no point of $a$.

**Lean reading.** `SeparatesInto S cross R₁ R₂`: the regions `R₁`, `R₂` are non-empty ("two
regions"), disjoint, cover `S` ("divides the remaining points"), `cross A B` holds for `A ∈ R₁`,
`B ∈ R₂`, and fails for two points of the same region; here `cross A B` is "the segment `AB`
contains a point of `a`" (`∃ X ∈ a, Between A X B`). `SeparatesInto.unique`: the two regions are
determined by these properties up to their order. Plane geometry (`PlaneOrder`, I and II):
`theorem5` (existence) and `theorem5_sides`: for any `A ∉ a` the regions are the points on the same
side of `a` as `A` and the points on the other side (`SameSide`, `OppositeSides` of Basic.lean, unit
`s4.side_of_line`: so the sides of a line defined there are Hilbert's regions; `sides_of_line_iff`:
for *any* two regions with the properties of Theorem 5, "same side" means "same region" and
"different sides" means "different regions"). Space geometry
(`SpaceOrder`): `theorem5_space`, `theorem5_space_sides` for a line `a` lying in a plane `α`, the
remaining points of `α` being divided. The proofs use only II 1–3 and II 5 besides group I
(`OrderCore`): the region properties are the transitivity properties of the sides of a line, proved
with Pasch's axiom, and in space they are transferred from the plane restriction.

**Status.** proved
-/

/-- The regions `R₁`, `R₂` **divide** the set `S` with respect to the relation `cross` (Theorems 5
and 7): both are non-empty, they partition `S`, `cross` holds between the regions and fails within
each region. -/
def SeparatesInto (S : Set P) (cross : P → P → Prop) (R₁ R₂ : Set P) : Prop :=
  R₁.Nonempty ∧ R₂.Nonempty ∧ Disjoint R₁ R₂ ∧ R₁ ∪ R₂ = S ∧
    (∀ A ∈ R₁, ∀ B ∈ R₂, cross A B) ∧ (∀ A ∈ R₁, ∀ A' ∈ R₁, ¬cross A A') ∧
    ∀ B ∈ R₂, ∀ B' ∈ R₂, ¬cross B B'

/-- The two regions of a division are unique up to their order. -/
theorem SeparatesInto.unique {S : Set P} {cross : P → P → Prop} {R₁ R₂ S₁ S₂ : Set P}
    (h : SeparatesInto S cross R₁ R₂) (h' : SeparatesInto S cross S₁ S₂) :
    (S₁ = R₁ ∧ S₂ = R₂) ∨ (S₁ = R₂ ∧ S₂ = R₁) := by
  obtain ⟨-, -, hd, hu, h12, h11, h22⟩ := h
  obtain ⟨⟨A, hA⟩, -, hd', hu', h12', h11', h22'⟩ := h'
  have memS : ∀ X, X ∈ S ↔ X ∈ R₁ ∨ X ∈ R₂ := fun X => by rw [← hu]; rfl
  have memS' : ∀ X, X ∈ S ↔ X ∈ S₁ ∨ X ∈ S₂ := fun X => by rw [← hu']; rfl
  have hAS : A ∈ S := (memS' A).2 (Or.inl hA)
  have rest : S₁ = R₁ → S₂ = R₂ := fun e => by
    ext X
    constructor
    · intro hX
      rcases (memS X).1 ((memS' X).2 (Or.inr hX)) with h1 | h1
      · rw [← e] at h1; exact absurd hX (Set.disjoint_left.1 hd' h1)
      · exact h1
    · intro hX
      rcases (memS' X).1 ((memS X).2 (Or.inr hX)) with h1 | h1
      · rw [e] at h1; exact absurd hX (Set.disjoint_left.1 hd h1)
      · exact h1
  have rest' : S₁ = R₂ → S₂ = R₁ := fun e => by
    ext X
    constructor
    · intro hX
      rcases (memS X).1 ((memS' X).2 (Or.inr hX)) with h1 | h1
      · exact h1
      · rw [← e] at h1; exact absurd hX (Set.disjoint_left.1 hd' h1)
    · intro hX
      rcases (memS' X).1 ((memS X).2 (Or.inl hX)) with h1 | h1
      · rw [e] at h1; exact absurd hX (Set.disjoint_right.1 hd h1)
      · exact h1
  rcases (memS A).1 hAS with hA1 | hA2
  · have e : S₁ = R₁ := by
      ext X
      constructor
      · intro hX
        rcases (memS X).1 ((memS' X).2 (Or.inl hX)) with h1 | h1
        · exact h1
        · exact absurd (h12 A hA1 X h1) (h11' A hA X hX)
      · intro hX
        rcases (memS' X).1 ((memS X).2 (Or.inl hX)) with h1 | h1
        · exact h1
        · exact absurd (h12' A hA X h1) (h11 A hA1 X hX)
    exact Or.inl ⟨e, rest e⟩
  · have e : S₁ = R₂ := by
      ext X
      constructor
      · intro hX
        rcases (memS X).1 ((memS' X).2 (Or.inl hX)) with h1 | h1
        · exact absurd (h12 X h1 A hA2) (h11' X hX A hA)
        · exact h1
      · intro hX
        rcases (memS' X).1 ((memS X).2 (Or.inr hX)) with h1 | h1
        · exact h1
        · exact absurd (h12' A hA X h1) (h22 A hA2 X hX)
    exact Or.inr ⟨e, rest' e⟩

section Theorem5Plane

variable [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
include hO

/-- **Theorem 5** (plane geometry), with the regions named: the sides of `a`. -/
theorem theorem5_sides (a : L) {A : P} (hA : A ∉ a) :
    SeparatesInto {X | X ∉ a} (fun X Y => ∃ Z, Z ∈ a ∧ Between X Z Y)
      {X | SameSide a A X} {X | OppositeSides a A X} := by
  refine ⟨⟨A, OrderCore.sameSide_refl hA⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Q, R, hQR, hQ, -⟩ := exists_two_points (Point := P) a
    have hAQ : A ≠ Q := fun e => hA (e ▸ hQ)
    obtain ⟨D, hAQD⟩ := exists_beyond (Line := L) hAQ
    refine ⟨D, hA, fun hD => hA ?_, Q, hQ, hAQD⟩
    exact mem_of_collinear (collinear_of_between hAQD).perm231 (ne23_of_between hAQD) hQ hD
  · exact Set.disjoint_left.2 fun X h1 h2 => OrderCore.not_sameSide_of_opp h2 h1
  · ext X
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h)
      · exact h.2.1
      · exact h.2.1
    · intro hX
      exact OrderCore.sameSide_or_opp hA hX
  · intro X hX Y hY
    exact (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hX) hY).2.2
  · intro X hX Y hY
    exact (OrderCore.sameSide_trans (OrderCore.sameSide_symm hX) hY).2.2
  · intro X hX Y hY
    exact (OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm hX) hY).2.2

/-- **Theorem 5** (plane geometry). Every line divides the remaining points into two regions. -/
theorem theorem5 (a : L) :
    ∃ R₁ R₂ : Set P, SeparatesInto {X | X ∉ a} (fun X Y => ∃ Z, Z ∈ a ∧ Between X Z Y) R₁ R₂ := by
  obtain ⟨A, hA⟩ := exists_not_mem (P := P) a
  exact ⟨_, _, theorem5_sides a hA⟩

/-- For any two regions `R₁`, `R₂` dividing the points off `a` as in Theorem 5, two points lie on the
same side of `a` (Basic.lean's `SameSide`, unit `s4.side_of_line`) iff they lie in the same region,
and on different sides iff in different regions: the sides of a line are Hilbert's notions, defined
"making use of the notation of theorem 5". -/
theorem sides_of_line_iff {a : L} {R₁ R₂ : Set P}
    (h : SeparatesInto {X | X ∉ a} (fun X Y => ∃ Z, Z ∈ a ∧ Between X Z Y) R₁ R₂) (A B : P) :
    (SameSide a A B ↔ (A ∈ R₁ ∧ B ∈ R₁) ∨ (A ∈ R₂ ∧ B ∈ R₂)) ∧
      (OppositeSides a A B ↔ (A ∈ R₁ ∧ B ∈ R₂) ∨ (A ∈ R₂ ∧ B ∈ R₁)) := by
  obtain ⟨-, -, hd, hu, h12, h11, h22⟩ := h
  have memS : ∀ X, X ∉ a ↔ X ∈ R₁ ∨ X ∈ R₂ := fun X => by
    rw [← Set.mem_union, hu]; rfl
  have cross_symm : ∀ X Y : P, (∃ Z, Z ∈ a ∧ Between X Z Y) → ∃ Z, Z ∈ a ∧ Between Y Z X :=
    fun X Y ⟨Z, hZ, hb⟩ => ⟨Z, hZ, between_symm (Line := L) hb⟩
  constructor
  · constructor
    · rintro ⟨hA, hB, hc⟩
      rcases (memS A).1 hA with hA1 | hA2 <;> rcases (memS B).1 hB with hB1 | hB2
      · exact Or.inl ⟨hA1, hB1⟩
      · exact absurd (h12 A hA1 B hB2) hc
      · exact absurd (cross_symm _ _ (h12 B hB1 A hA2)) hc
      · exact Or.inr ⟨hA2, hB2⟩
    · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
      · exact ⟨(memS A).2 (Or.inl hA), (memS B).2 (Or.inl hB), h11 A hA B hB⟩
      · exact ⟨(memS A).2 (Or.inr hA), (memS B).2 (Or.inr hB), h22 A hA B hB⟩
  · constructor
    · rintro ⟨hA, hB, hc⟩
      rcases (memS A).1 hA with hA1 | hA2 <;> rcases (memS B).1 hB with hB1 | hB2
      · exact absurd hc (h11 A hA1 B hB1)
      · exact Or.inl ⟨hA1, hB2⟩
      · exact Or.inr ⟨hA2, hB1⟩
      · exact absurd hc (h22 A hA2 B hB2)
    · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
      · exact ⟨(memS A).2 (Or.inl hA), (memS B).2 (Or.inr hB), h12 A hA B hB⟩
      · exact ⟨(memS A).2 (Or.inr hA), (memS B).2 (Or.inl hB), cross_symm _ _ (h12 B hB A hA)⟩

end Theorem5Plane

section Theorem5Space

variable [HasLines P L] [HasPlanes P Pl] [HasBetween P] [hO : SpaceOrder P L Pl]
include hO

/-- **Theorem 5** (space geometry), with the regions named: a line `a` of a plane `α` divides the
remaining points of `α` into its two sides. -/
theorem theorem5_space_sides {α : Pl} {a : L} (ha : LiesInPlane (Point := P) a α) {A : P}
    (hAα : A ∈ α) (hA : A ∉ a) :
    SeparatesInto {X | X ∈ α ∧ X ∉ a} (fun X Y => ∃ Z, Z ∈ a ∧ Between X Z Y)
      {X | X ∈ α ∧ SameSide a A X} {X | X ∈ α ∧ OppositeSides a A X} := by
  refine ⟨⟨A, hAα, hA, hA, fun ⟨_, _, h⟩ => ne13_of_between h rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Q, R, hQR, hQ, -⟩ := exists_two_points (Point := P) a
    have hAQ : A ≠ Q := fun e => hA (e ▸ hQ)
    obtain ⟨D, hAQD⟩ := exists_beyond (Line := L) hAQ
    obtain ⟨g, hAg, hQg, hDg⟩ := collinear_of_between hAQD
    have hDα : D ∈ α := liesInPlane_of_mem hAQ hAg hQg hAα (ha Q hQ) D hDg
    refine ⟨D, hDα, hA, fun hD => hA ?_, Q, hQ, hAQD⟩
    exact mem_of_collinear (collinear_of_between hAQD).perm231 (ne23_of_between hAQD) hQ hD
  · exact Set.disjoint_left.2 fun X h1 h2 => h1.2.2.2 h2.2.2.2
  · ext X
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.2.1⟩
      · exact ⟨h.1, h.2.2.1⟩
    · rintro ⟨hXα, hX⟩
      by_cases h : ∃ Z, Z ∈ a ∧ Between A Z X
      · exact Or.inr ⟨hXα, hA, hX, h⟩
      · exact Or.inl ⟨hXα, hA, hX, h⟩
  · intro X hX Y hY
    have hXA : SameSide a X A := ⟨hX.2.2.1, hX.2.1, fun ⟨Z, hZ, h⟩ => hX.2.2.2 ⟨Z, hZ,
      between_symm h⟩⟩
    exact (OrderSpace.opp_of_sameSide_opp ha hX.1 hAα hY.1 hXA hY.2).2.2
  · intro X hX Y hY
    have hXA : SameSide a X A := ⟨hX.2.2.1, hX.2.1, fun ⟨Z, hZ, h⟩ => hX.2.2.2 ⟨Z, hZ,
      between_symm h⟩⟩
    exact (OrderSpace.sameSide_trans ha hX.1 hAα hY.1 hXA hY.2).2.2
  · intro X hX Y hY
    obtain ⟨Z, hZ, hAZX⟩ := hX.2.2.2
    have hXA : OppositeSides a X A := ⟨hX.2.2.1, hX.2.1, Z, hZ, between_symm hAZX⟩
    exact (OrderSpace.sameSide_of_opp_opp ha hX.1 hAα hY.1 hXA hY.2).2.2

/-- **Theorem 5** (space geometry). Every line lying in a plane divides the remaining points of the
plane into two regions. -/
theorem theorem5_space {α : Pl} {a : L} (ha : LiesInPlane (Point := P) a α) :
    ∃ R₁ R₂ : Set P, SeparatesInto {X | X ∈ α ∧ X ∉ a}
      (fun X Y => ∃ Z, Z ∈ a ∧ Between X Z Y) R₁ R₂ := by
  obtain ⟨A, hAα, hA⟩ := exists_mem_plane_not_mem (P := P) (L := L) α a
  exact ⟨_, _, theorem5_space_sides ha hAα hA⟩

end Theorem5Space

/-!
## [s4.broken_line] Broken lines

*(§ 4)*

> Definitions. A system of segments $AB$, $BC$, $CD$, \ldots, $KL$ is called a *broken line* joining $A$ with $L$ and is designated, briefly, as the broken line $ABCDE$ \ldots $KL$. The points lying within the segments $AB$, $BC$, $CD$, \ldots, $KL$, as also the points $A$, $B$, $C$, $D$, \ldots, $K$, $L$, are called *the points of the broken line*.

**Lean reading.** A broken line is given by its sequence of vertices `w : Fin (n + 1) → P`
(`w 0 = A`, …, `w n = L`); its segments are `w i w (i+1)`, so consecutive vertices are distinct
(`IsBrokenLine`: a segment has two distinct extremities). It joins `w 0` with `w (Fin.last n)`.
`BrokenLinePoints w`: the vertices and the points within the segments. For `n = 0` the "broken
line" is a single point (no segment); it is allowed, to join a point with itself.

**Status.** definition
-/

/-- `w 0, …, w n` are the vertices of a **broken line**: consecutive vertices are distinct. -/
def IsBrokenLine {n : ℕ} (w : Fin (n + 1) → P) : Prop :=
  ∀ i : Fin n, w i.castSucc ≠ w i.succ

/-- The **points of the broken line** `w 0 … w n`: its vertices and the points within its
segments. -/
def BrokenLinePoints [HasBetween P] {n : ℕ} (w : Fin (n + 1) → P) : Set P :=
  {X | (∃ i, X = w i) ∨ ∃ i : Fin n, Between (w i.castSucc) X (w i.succ)}

/-!
## [s4.polygon] Polygons

*(§ 4)*

> In particular, if the point $A$ coincides with $L$, the broken line is called a *polygon* and is designated as the polygon $ABCD \ldots K$. The segments $AB$, $BC$, $CD$, \ldots, $KA$ are called the *sides of the polygon* and the points $A$, $B$, $C$, $D$, \ldots, $K$ the *vertices*. Polygons having $3$, $4$, $5$, \ldots, $n$ vertices are called, respectively, *triangles*, *quadrangles*, *pentagons*, \ldots, *n-gons*.

**Lean reading.** A polygon with `k` vertices is given by `v : Fin k → P`, its sides being
`v i v (i+1)` with indices mod `k` (`finRotate k i` is `i + 1 mod k`); it is the closed broken line
`v 0 … v (k-1) v 0`. `IsPolygon v`: consecutive vertices are distinct (each side is a segment).
`PolygonPoints v`: the vertices and the points within the sides. The names "triangle", … are the
cases `k = 3, 4, …`.

**Status.** definition
-/

/-- `v 0, …, v (k-1)` are the vertices of a **polygon**: consecutive vertices (mod `k`) are
distinct. -/
def IsPolygon {k : ℕ} (v : Fin k → P) : Prop :=
  ∀ i : Fin k, v i ≠ v (finRotate k i)

/-- The **points of the polygon** with vertices `v`: the vertices and the points within the
sides. -/
def PolygonPoints [HasBetween P] {k : ℕ} (v : Fin k → P) : Set P :=
  {X | (∃ i, X = v i) ∨ ∃ i, Between (v i) X (v (finRotate k i))}

/-!
## [s4.simple_polygon] Simple polygons

*(§ 4)*

> If the vertices of a polygon are all distinct and none of them lie within the segments composing the sides of the polygon, and, furthermore, if no two sides have a point in common, then the polygon is called a *simple polygon*.

**Lean reading.** `IsSimplePolygon v`: at least three vertices (a polygon in Hilbert's list starts
with triangles), the vertices are distinct (`Function.Injective v`), no vertex lies within a side,
and no point lies within two different sides. "No two sides have a point in common" must refer to
the points *within* the sides (Hilbert's "points of a segment"), since consecutive sides always
share a vertex.

**Status.** definition
-/

/-- A **simple polygon**: at least three distinct vertices, no vertex within a side, no point
within two sides. -/
def IsSimplePolygon [HasBetween P] {k : ℕ} (v : Fin k → P) : Prop :=
  3 ≤ k ∧ Function.Injective v ∧ (∀ i j : Fin k, ¬Between (v j) (v i) (v (finRotate k j))) ∧
    ∀ i j : Fin k, i ≠ j → ∀ X : P, Between (v i) X (v (finRotate k i)) →
      ¬Between (v j) X (v (finRotate k j))

/-!
## [th.6] Theorem 6

*(§ 4)*

> Every simple polygon, whose vertices all lie in a plane $\alpha$, divides the points of this plane, not belonging to the broken line constituting the sides of the polygon, into two regions, an interior and an exterior, having the following properties: If $A$ is a point of the interior region (interior point) and $B$ a point of the exterior region (exterior point), then any broken line joining $A$ and $B$ must have at least one point in common with the polygon. If, on the other hand, $A$, $A'$ are two points of the interior and $B$, $B'$ two points of the exterior region, then there are always broken lines to be found joining $A$ with $A'$ and $B$ with $B'$ without having a point in common with the polygon. There exist straight lines in the plane $\alpha$ which lie entirely outside of the given polygon, but there are none which lie entirely within it.

**Lean reading.** `DividesLikePolygon S` is the conclusion for the set `S` of the points of a
polygon, in a plane geometry: there are regions `I` (interior) and `E` (exterior), both non-empty,
partitioning the points not on the polygon, such that every broken line joining a point of `I`
with a point of `E` has a point in common with `S`; any two points of `I`, and any two points of
`E`, are joined by a broken line (`IsBrokenLine`) without a point in common with `S`; some line has
all its points in `E` ("lies entirely outside", read strongly), and no line has all its points in
`I`. `PolygonTheorem P`: every simple polygon (`IsSimplePolygon`) of the plane geometry `P`
satisfies it. Hilbert's "vertices all lie in a plane `α`" is the plane geometry of `α` (the plane
restriction): the broken lines are those of the plane. The assumptions are groups I and II
(`PlaneOrder`), as Hilbert says ("with the aid of theorem 5").

The general statement is the Jordan curve theorem for polygons in ordered geometry. Hilbert gives
no proof ("without serious difficulty"); a proof was given by O. Veblen (*Trans. AMS* 5, 1904).
The theorem is proved in `OrderPolygon.lean` from groups I and II only:
`polygonTheorem : PolygonTheorem P` in every plane geometry `PlaneOrder P L`, and
`theorem6_space` for the simple polygons whose vertices lie in a plane `α` of a space geometry
(in the plane geometry of `α`). The proof (helper modules `OrderPolygonAux.lean` …
`OrderPolygonAux4.lean`, namespace `PolyJordan`) is a parity count of the crossings of the sides
with segments, together with the construction of broken lines running alongside the polygon. All
vertices lie on one side of some line `ℓ0` (`exists_line_sameSide`). The parity `par v ℓ0 X` of a
point `X` off the polygon is the number, mod 2, of sides crossed by a segment from `X` to a point
of `ℓ0` in general position; it does not depend on that point (`cr_indep`, by counting the
crossings of the polygon with a triangle, `tri_parity`). The parity is constant along every
segment that does not meet the polygon (`par_eq_of_step`), it takes both values (`exists_jump`),
and it is `0` on every line that does not meet the polygon (`par_zero_of_line`). The interior is
the set of the points off the polygon of parity `1`, the exterior the set of those of parity `0`
(`PolyJordan.Simple.divides`): a broken line joining an interior and an exterior point meets the
polygon, `ℓ0` lies in the exterior, and no line lies in the interior. Two points off the polygon
of the same parity are joined by a broken line that does not meet the polygon (`two_classes`,
`Conn.exists_brokenLine`): every point off the polygon sees a point of the polygon (`first_hit`),
and walking round the polygon (`good_side`, `vertex_good`, with the sweep lemma `sweep`) joins it
to one of two fixed points `N₁`, `N₂` on either side of the side `v n v 0`.

**The case of triangles** is proved in this file by a direct argument, `theorem6_triangle` (in any
plane of space: `theorem6_triangle_space`); it is a special case, now subsumed by
`polygonTheorem`. For a triangle the interior is the intersection of the sides of the three side
lines that contain the opposite vertices (`TriInside`; it is convex, so two interior points are
joined by a segment); every point that is neither interior nor on the triangle lies beyond a side
line (`TriBeyond`), these three half-planes are convex and meet pairwise, so two exterior points
are joined by at most two segments; a broken line from an interior to an exterior point meets the
triangle by the exit lemma `TriangleLines.exit` (the segment from an interior point to a
non-interior point contains a point of the triangle, by induction on the number of side lines
separating the two points); the line through the points beyond a vertex on the two adjacent side
lines lies outside (`TriangleLines.exists_line_outside`), and no line lies inside
(`TriangleLines.no_line_inside`, by the crossbar theorem and Pasch's axiom).

**Status.** proved
-/

/-- **The conclusion of Theorem 6** for the set `S` of the points of a polygon (plane geometry). -/
def DividesLikePolygon [HasLines P L] [HasBetween P] (S : Set P) : Prop :=
  ∃ I E : Set P, I.Nonempty ∧ E.Nonempty ∧ Disjoint I E ∧ I ∪ E = Sᶜ ∧
    (∀ A ∈ I, ∀ B ∈ E, ∀ (n : ℕ) (w : Fin (n + 1) → P), w 0 = A → w (Fin.last n) = B →
      (BrokenLinePoints w ∩ S).Nonempty) ∧
    (∀ A ∈ I, ∀ A' ∈ I, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = A ∧
      w (Fin.last n) = A' ∧ Disjoint (BrokenLinePoints w) S) ∧
    (∀ B ∈ E, ∀ B' ∈ E, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = B ∧
      w (Fin.last n) = B' ∧ Disjoint (BrokenLinePoints w) S) ∧
    (∃ l : L, ∀ X : P, X ∈ l → X ∈ E) ∧ ¬∃ l : L, ∀ X : P, X ∈ l → X ∈ I

/-- **Theorem 6** as a statement (proved as `polygonTheorem` in `OrderPolygon.lean`): every
simple polygon divides the plane into an interior and an exterior. -/
def PolygonTheorem (P : Type u) {L : Type v} [HasLines P L] [HasBetween P] : Prop :=
  ∀ (k : ℕ) (v : Fin k → P), IsSimplePolygon v → DividesLikePolygon (L := L) (PolygonPoints v)

/-- Side lines of a triangle with vertices `V 0, V 1, V 2`: `ℓ i` passes through the two vertices
other than `V i`, and not through `V i`. -/
structure TriangleLines [HasLines P L] (V : Fin 3 → P) (ℓ : Fin 3 → L) : Prop where
  mem₁ : ∀ i, V (i + 1) ∈ ℓ i
  mem₂ : ∀ i, V (i + 2) ∈ ℓ i
  not_mem : ∀ i, V i ∉ ℓ i

/-- The points of the triangle `V 0 V 1 V 2` (vertices and points within the sides). -/
def TriPts [HasBetween P] (V : Fin 3 → P) : Set P :=
  {X | (∃ i, X = V i) ∨ ∃ i, Between (V (i + 1)) X (V (i + 2))}

/-- The interior of the triangle: the points on the same side of each side line as the opposite
vertex. -/
def TriInside [HasLines P L] [HasBetween P] (V : Fin 3 → P) (ℓ : Fin 3 → L) : Set P :=
  {X | ∀ i, SameSide (ℓ i) X (V i)}

/-- The open half-plane beyond the side line `ℓ i` (opposite to `V i`). -/
def TriBeyond [HasLines P L] [HasBetween P] (V : Fin 3 → P) (ℓ : Fin 3 → L) (i : Fin 3) :
    Set P :=
  {X | OppositeSides (ℓ i) (V i) X}

theorem fin3_cases (i j : Fin 3) : j = i ∨ j = i + 1 ∨ j = i + 2 := by
  fin_cases i <;> fin_cases j <;> decide

theorem fin3_add11 (i : Fin 3) : i + 1 + 1 = i + 2 := by fin_cases i <;> decide
theorem fin3_add12 (i : Fin 3) : i + 1 + 2 = i := by fin_cases i <;> decide
theorem fin3_add21 (i : Fin 3) : i + 2 + 1 = i := by fin_cases i <;> decide
theorem fin3_add22 (i : Fin 3) : i + 2 + 2 = i + 1 := by fin_cases i <;> decide
theorem fin3_ne1 (i : Fin 3) : i + 1 ≠ i := by fin_cases i <;> decide
theorem fin3_ne2 (i : Fin 3) : i + 2 ≠ i := by fin_cases i <;> decide
theorem fin3_ne12 (i : Fin 3) : i + 1 ≠ i + 2 := by fin_cases i <;> decide

section Triangle

variable [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
include hO

/-- The points between a point of a line and a point off it are on the side of the latter. -/
theorem sameSide_of_between_mem {l : L} {X Y Z : P} (hX : X ∈ l) (hY : Y ∉ l)
    (h : Between X Z Y) : SameSide l Z Y := by
  have hXY : X ≠ Y := ne13_of_between h
  obtain ⟨g, hXg, hYg⟩ := exists_line (Line := L) hXY
  have hZg : Z ∈ g := OrderCore.mem_of_between h hXg hYg
  have hgl : g ≠ l := fun e => hY (e ▸ hYg)
  have key : ∀ W, W ∈ g → W ∈ l → W = X := fun W hWg hWl =>
    eq_of_mem_of_mem hgl hWg hWl hXg hX
  refine ⟨fun hZ => ne12_of_between h (key Z hZg hZ).symm, hY, ?_⟩
  rintro ⟨W, hWl, hZWY⟩
  have hWg : W ∈ g := OrderCore.mem_of_between hZWY hZg hYg
  rw [key W hWg hWl] at hZWY
  exact not_between_swap12 h hZWY

/-- The sides of a line are convex. -/
theorem sameSide_of_between {l : L} {X Y Z : P} (hs : SameSide l X Y) (h : Between X Z Y) :
    SameSide l X Z := by
  have hZ : Z ∉ l := fun hZ => hs.2.2 ⟨Z, hZ, h⟩
  refine ⟨hs.1, hZ, ?_⟩
  rintro ⟨W, hWl, hXWZ⟩
  exact hs.2.2 ⟨W, hWl, (OrderLin.trans₂ hXWZ h).1⟩

variable {V : Fin 3 → P} {ℓ : Fin 3 → L}

omit [HasBetween P] hO in
/-- A vertex lies on the side lines other than its own. -/
theorem TriangleLines.mem_of_ne (hT : TriangleLines V ℓ) {i j : Fin 3} (h : i ≠ j) :
    V i ∈ ℓ j := by
  rcases fin3_cases j i with e | e | e
  · exact absurd e h
  · have := hT.mem₁ j; rwa [← e] at this
  · have := hT.mem₂ j; rwa [← e] at this

omit [HasBetween P] hO in
theorem TriangleLines.lines_ne (hT : TriangleLines V ℓ) {i j : Fin 3} (h : i ≠ j) :
    ℓ i ≠ ℓ j := fun e => hT.not_mem i (e ▸ hT.mem_of_ne h)

omit [HasBetween P] hO in
theorem TriangleLines.vertex_ne (hT : TriangleLines V ℓ) {i j : Fin 3} (h : i ≠ j) :
    V i ≠ V j := fun e => hT.not_mem i (e ▸ hT.mem_of_ne h.symm)

/-- Two side lines meet only in their common vertex. -/
theorem TriangleLines.eq_vertex (hT : TriangleLines V ℓ) {i j : Fin 3} (h : i ≠ j) {X : P}
    (hi : X ∈ ℓ i) (hj : X ∈ ℓ j) : ∃ k, X = V k := by
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp_all <;> decide
  exact ⟨k, eq_of_mem_of_mem (hT.lines_ne h) hi hj (hT.mem_of_ne hki) (hT.mem_of_ne hkj)⟩

/-- A point of the side line `ℓ i` on the inner side of the two other side lines lies within the
side `V (i+1) V (i+2)`. -/
theorem TriangleLines.between_of_mem (hT : TriangleLines V ℓ) {i : Fin 3} {X : P} (hX : X ∈ ℓ i)
    (h1 : SameSide (ℓ (i + 1)) X (V (i + 1))) (h2 : SameSide (ℓ (i + 2)) X (V (i + 2))) :
    Between (V (i + 1)) X (V (i + 2)) := by
  have hB2 : V (i + 1) ∈ ℓ (i + 2) := hT.mem_of_ne (fin3_ne12 i)
  have hC1 : V (i + 2) ∈ ℓ (i + 1) := hT.mem_of_ne (fin3_ne12 i).symm
  have hXB : X ≠ V (i + 1) := fun e => h2.1 (e ▸ hB2)
  have hXC : X ≠ V (i + 2) := fun e => h1.1 (e ▸ hC1)
  have hBC : V (i + 1) ≠ V (i + 2) := hT.vertex_ne (fin3_ne12 i)
  rcases between_trichotomy (collinear_of_mem (hT.mem₁ i) hX (hT.mem₂ i)) hXB.symm hBC hXC with
    h | h | h
  · exact absurd h2 (OrderCore.not_sameSide_of_opp ⟨h2.1, h2.2.1, V (i + 1), hB2, h⟩)
  · exact h
  · exact absurd (OrderCore.sameSide_symm h1)
      (OrderCore.not_sameSide_of_opp ⟨h1.2.1, h1.1, V (i + 2), hC1, h⟩)

theorem TriangleLines.mem_line_of_side (hT : TriangleLines V ℓ) {i : Fin 3} {X : P}
    (h : Between (V (i + 1)) X (V (i + 2))) : X ∈ ℓ i :=
  OrderCore.mem_of_between h (hT.mem₁ i) (hT.mem₂ i)

/-- The interior points are not points of the triangle. -/
theorem TriangleLines.not_mem_inside (hT : TriangleLines V ℓ) {X : P} (hX : X ∈ TriPts V) :
    X ∉ TriInside V ℓ := by
  intro hI
  rcases hX with ⟨j, rfl⟩ | ⟨i, h⟩
  · exact (hI (j + 1)).1 (hT.mem_of_ne (fin3_ne1 j).symm)
  · exact (hI i).1 (hT.mem_line_of_side h)

/-- The half-plane beyond a side line contains no point of the triangle. -/
theorem TriangleLines.not_mem_beyond (hT : TriangleLines V ℓ) {X : P} (hX : X ∈ TriPts V)
    (i : Fin 3) : X ∉ TriBeyond V ℓ i := by
  intro hB
  rcases hX with ⟨j, rfl⟩ | ⟨k, h⟩
  · by_cases hji : j = i
    · subst hji; exact OrderCore.ne_of_opp hB rfl
    · exact hB.2.1 (hT.mem_of_ne hji)
  · rcases fin3_cases i k with e | e | e
    · subst e; exact hB.2.1 (hT.mem_line_of_side h)
    · -- k = i + 1: the side is `V (i+2) V i`
      subst e
      rw [fin3_add11, fin3_add12] at h
      have := sameSide_of_between_mem (hT.mem₂ i) (hT.not_mem i) h
      exact OrderCore.not_sameSide_of_opp hB (OrderCore.sameSide_symm this)
    · -- k = i + 2: the side is `V i V (i+1)`
      subst e
      rw [fin3_add21, fin3_add22] at h
      have := sameSide_of_between_mem (hT.mem₁ i) (hT.not_mem i) (between_symm h)
      exact OrderCore.not_sameSide_of_opp hB (OrderCore.sameSide_symm this)

/-- Every point that is neither a point of the triangle nor interior lies beyond some side
line. -/
theorem TriangleLines.mem_beyond (hT : TriangleLines V ℓ) {X : P} (hX : X ∉ TriPts V)
    (hI : X ∉ TriInside V ℓ) : ∃ i, X ∈ TriBeyond V ℓ i := by
  simp only [TriInside, Set.mem_ofPred_eq, not_forall] at hI
  obtain ⟨i, hi⟩ := hI
  by_cases hXi : X ∈ ℓ i
  · have : ¬(SameSide (ℓ (i + 1)) X (V (i + 1)) ∧ SameSide (ℓ (i + 2)) X (V (i + 2))) :=
      fun ⟨h1, h2⟩ => hX (Or.inr ⟨i, hT.between_of_mem hXi h1 h2⟩)
    have hnot : ∀ j, j ≠ i → X ∉ ℓ j := fun j hj hXj => by
      obtain ⟨k, rfl⟩ := hT.eq_vertex (Ne.symm hj) hXi hXj
      exact hX (Or.inl ⟨k, rfl⟩)
    by_cases h1 : SameSide (ℓ (i + 1)) X (V (i + 1))
    · have h2 : ¬SameSide (ℓ (i + 2)) X (V (i + 2)) := fun h2 => this ⟨h1, h2⟩
      refine ⟨i + 2, ?_⟩
      rcases OrderCore.sameSide_or_opp (hT.not_mem (i + 2)) (hnot _ (fin3_ne2 i)) with h | h
      · exact absurd (OrderCore.sameSide_symm h) h2
      · exact h
    · refine ⟨i + 1, ?_⟩
      rcases OrderCore.sameSide_or_opp (hT.not_mem (i + 1)) (hnot _ (fin3_ne1 i)) with h | h
      · exact absurd (OrderCore.sameSide_symm h) h1
      · exact h
  · refine ⟨i, ?_⟩
    rcases OrderCore.sameSide_or_opp (hT.not_mem i) hXi with h | h
    · exact absurd (OrderCore.sameSide_symm h) hi
    · exact h

/-- The half-plane beyond a side line is convex. -/
theorem TriangleLines.beyond_convex {i : Fin 3} {X Y Z : P} (hX : X ∈ TriBeyond V ℓ i)
    (hY : Y ∈ TriBeyond V ℓ i) (h : Between X Z Y) : Z ∈ TriBeyond V ℓ i := by
  have hXY := OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm hX) hY
  have hXZ := sameSide_of_between hXY h
  exact OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hXZ)
    (OrderCore.opp_symm hX))

/-- The interior is convex. -/
theorem TriangleLines.inside_convex {X Y Z : P} (hX : X ∈ TriInside V ℓ)
    (hY : Y ∈ TriInside V ℓ) (h : Between X Z Y) : Z ∈ TriInside V ℓ := by
  intro i
  have hXY := OrderCore.sameSide_trans (hX i) (OrderCore.sameSide_symm (hY i))
  have hXZ := sameSide_of_between hXY h
  exact OrderCore.sameSide_trans (OrderCore.sameSide_symm hXZ) (hX i)

/-- Two half-planes beyond side lines have a common point. -/
theorem TriangleLines.beyond_inter (hT : TriangleLines V ℓ) {i j : Fin 3} (hij : i ≠ j) :
    ∃ Q, Q ∈ TriBeyond V ℓ i ∧ Q ∈ TriBeyond V ℓ j := by
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp_all <;> decide
  have hVij : V i ≠ V j := hT.vertex_ne hij
  obtain ⟨M, hM⟩ := exists_between (Line := L) hVij
  have hMk : M ≠ V k := by
    intro e
    have hMlk : M ∈ ℓ k := OrderCore.mem_of_between hM (hT.mem_of_ne hki.symm)
      (hT.mem_of_ne hkj.symm)
    exact hT.not_mem k (e ▸ hMlk)
  obtain ⟨Q, hMQ⟩ := exists_beyond (Line := L) hMk
  have side : ∀ {a b : Fin 3}, a ≠ b → k ≠ a → k ≠ b → Between (V a) M (V b) →
      Q ∈ TriBeyond V ℓ a := by
    intro a b hab hka hkb hM'
    have hMa : SameSide (ℓ a) M (V a) :=
      sameSide_of_between_mem (hT.mem_of_ne hab.symm) (hT.not_mem a) (between_symm hM')
    have hQa : Q ∉ ℓ a := by
      intro hQ
      have hka' : V k ∈ ℓ a := hT.mem_of_ne hka
      exact hMa.1 (OrderCore.mem_of_between'' hMQ hka' hQ)
    exact OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hMa)
      ⟨hMa.1, hQa, V k, hT.mem_of_ne hka, hMQ⟩
  exact ⟨Q, side hij hki hkj hM, side hij.symm hkj hki (between_symm hM)⟩

/-- **Exit lemma**: a segment from an interior point `X` to a point `Y` that is not interior
contains a point of the triangle (`Y` itself or a point between `X` and `Y`). -/
theorem TriangleLines.exit (hT : TriangleLines V ℓ) {X : P} (hX : X ∈ TriInside V ℓ) (Y : P)
    (hY : Y ∉ TriInside V ℓ) : ∃ Z ∈ TriPts V, Z = Y ∨ Between X Z Y := by
  classical
  let bad : P → Finset (Fin 3) := fun Y =>
    Finset.univ.filter (fun i => ¬SameSide (ℓ i) X Y)
  have mem_bad : ∀ {k : Fin 3} {Y : P}, k ∈ bad Y ↔ ¬SameSide (ℓ k) X Y := by
    intro k Y; simp [bad]
  have key : ∀ n : ℕ, ∀ Y : P, (bad Y).card ≤ n → (bad Y).Nonempty →
      ∃ Z ∈ TriPts V, Z = Y ∨ Between X Z Y := by
    intro n
    induction n with
    | zero =>
      intro Y h hne
      have := Finset.card_pos.2 hne
      omega
    | succ n ih =>
      intro Y hcard ⟨i, hi⟩
      by_cases hYT : Y ∈ TriPts V
      · exact ⟨Y, hYT, Or.inl rfl⟩
      have hi' : ¬SameSide (ℓ i) X Y := mem_bad.1 hi
      obtain ⟨Z₁, hZ₁l, hZ₁s, hZ₁bad⟩ : ∃ Z₁, Z₁ ∈ ℓ i ∧ (Z₁ = Y ∨ Between X Z₁ Y) ∧
          ∀ k, ¬SameSide (ℓ k) X Z₁ → ¬SameSide (ℓ k) X Y := by
        by_cases hYl : Y ∈ ℓ i
        · exact ⟨Y, hYl, Or.inl rfl, fun _ h => h⟩
        · obtain ⟨-, -, Z₁, hZ₁, hb⟩ :=
            (OrderCore.sameSide_or_opp (hX i).1 hYl).resolve_left hi'
          exact ⟨Z₁, hZ₁, Or.inr hb, fun k hk hkY => hk (sameSide_of_between hkY hb)⟩
      by_cases hZT : Z₁ ∈ TriPts V
      · exact ⟨Z₁, hZT, hZ₁s⟩
      obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ ¬SameSide (ℓ j) X Z₁ := by
        by_contra hall
        simp only [not_exists, not_and, not_not] at hall
        have h1 : SameSide (ℓ (i + 1)) Z₁ (V (i + 1)) :=
          OrderCore.sameSide_trans (OrderCore.sameSide_symm (hall _ (fin3_ne1 i))) (hX (i + 1))
        have h2 : SameSide (ℓ (i + 2)) Z₁ (V (i + 2)) :=
          OrderCore.sameSide_trans (OrderCore.sameSide_symm (hall _ (fin3_ne2 i))) (hX (i + 2))
        exact hZT (Or.inr ⟨i, hT.between_of_mem hZ₁l h1 h2⟩)
      have hZ₁j : Z₁ ∉ ℓ j := fun h => by
        obtain ⟨k, rfl⟩ := hT.eq_vertex (Ne.symm hji) hZ₁l h
        exact hZT (Or.inl ⟨k, rfl⟩)
      obtain ⟨-, -, Z₂, hZ₂, hXZ₂Z₁⟩ :=
        (OrderCore.sameSide_or_opp (hX j).1 hZ₁j).resolve_left hj
      have hsub : bad Z₂ ⊆ (bad Y).erase i := by
        intro k hk
        rw [mem_bad] at hk
        rw [Finset.mem_erase, mem_bad]
        refine ⟨?_, fun hkY => ?_⟩
        · rintro rfl
          exact hk (OrderCore.sameSide_symm
            (sameSide_of_between_mem hZ₁l (hX k).1 (between_symm hXZ₂Z₁)))
        · have hkZ₁ : SameSide (ℓ k) X Z₁ := by
            by_contra hn
            exact hZ₁bad k hn hkY
          exact hk (sameSide_of_between hkZ₁ hXZ₂Z₁)
      have hcard2 : (bad Z₂).card ≤ n := by
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hi] at this
        omega
      obtain ⟨Z, hZT', hZs⟩ := ih Z₂ hcard2 ⟨j, mem_bad.2 fun h => h.2.1 hZ₂⟩
      have hXZ₂Y : Between X Z₂ Y := by
        rcases hZ₁s with rfl | hb
        · exact hXZ₂Z₁
        · exact (OrderLin.trans₂ hXZ₂Z₁ hb).1
      refine ⟨Z, hZT', Or.inr ?_⟩
      rcases hZs with rfl | hb
      · exact hXZ₂Y
      · exact (OrderLin.trans₂ hb hXZ₂Y).1
  have hne : (bad Y).Nonempty := by
    simp only [TriInside, Set.mem_ofPred_eq, not_forall] at hY
    obtain ⟨i, hi⟩ := hY
    exact ⟨i, mem_bad.2 fun h => hi (OrderCore.sameSide_trans (OrderCore.sameSide_symm h)
      (hX i))⟩
  exact key _ Y le_rfl hne

/-- The interior of a triangle is not empty. -/
theorem TriangleLines.inside_nonempty (hT : TriangleLines V ℓ) : (TriInside V ℓ).Nonempty := by
  have h1 : V 1 ∈ ℓ 0 := hT.mem₁ 0
  have h2 : V 2 ∈ ℓ 0 := hT.mem₂ 0
  have h21 : V 2 ∈ ℓ 1 := hT.mem₁ 1
  have h01 : V 0 ∈ ℓ 1 := hT.mem₂ 1
  have h02 : V 0 ∈ ℓ 2 := hT.mem₁ 2
  have h12 : V 1 ∈ ℓ 2 := hT.mem₂ 2
  obtain ⟨D, hD⟩ := exists_between (Line := L) (hT.vertex_ne (by decide : (1 : Fin 3) ≠ 2))
  have hD0 : D ∈ ℓ 0 := OrderCore.mem_of_between hD h1 h2
  have hD0' : V 0 ≠ D := fun e => hT.not_mem 0 (e ▸ hD0)
  obtain ⟨X, hX⟩ := exists_between (Line := L) hD0'
  refine ⟨X, fun i => ?_⟩
  fin_cases i
  · exact sameSide_of_between_mem hD0 (hT.not_mem 0) (between_symm hX)
  · have hDV : SameSide (ℓ 1) D (V 1) :=
      sameSide_of_between_mem h21 (hT.not_mem 1) (between_symm hD)
    exact OrderCore.sameSide_trans (sameSide_of_between_mem h01 hDV.1 hX) hDV
  · have hDV : SameSide (ℓ 2) D (V 2) := sameSide_of_between_mem h12 (hT.not_mem 2) hD
    exact OrderCore.sameSide_trans (sameSide_of_between_mem h02 hDV.1 hX) hDV

/-- **Crossbar**: the half-ray from `V 0` through an interior point meets the opposite side. -/
theorem TriangleLines.crossbar (hT : TriangleLines V ℓ) {Z : P} (hZ : Z ∈ TriInside V ℓ) :
    ∃ W, Between (V 1) W (V 2) ∧ Between (V 0) Z W := by
  have h1 : V 1 ∈ ℓ 0 := hT.mem₁ 0
  have h2 : V 2 ∈ ℓ 0 := hT.mem₂ 0
  have h21 : V 2 ∈ ℓ 1 := hT.mem₁ 1
  have h01 : V 0 ∈ ℓ 1 := hT.mem₂ 1
  have h02 : V 0 ∈ ℓ 2 := hT.mem₁ 2
  have h12 : V 1 ∈ ℓ 2 := hT.mem₂ 2
  have hl12 : ℓ 1 ≠ ℓ 2 := hT.lines_ne (by decide)
  have hZ0 : Z ≠ V 0 := fun e => (hZ 1).1 (e ▸ h01)
  obtain ⟨E, hE⟩ := exists_beyond (Line := L) (hT.vertex_ne (by decide : (2 : Fin 3) ≠ 0))
  have hE1 : E ∈ ℓ 1 := OrderCore.mem_of_between' hE h21 h01
  have hE2 : E ∉ ℓ 2 := fun h => ne23_of_between hE (eq_of_mem_of_mem hl12 h01 h02 hE1 h)
  have hV0m : V 0 ∈ line (Line := L) (V 0) Z hZ0.symm := mem_line_left hZ0.symm
  have hZm : Z ∈ line (Line := L) (V 0) Z hZ0.symm := mem_line_right hZ0.symm
  have hm1 : line (Line := L) (V 0) Z hZ0.symm ≠ ℓ 1 := fun e => (hZ 1).1 (e ▸ hZm)
  have hm2 : line (Line := L) (V 0) Z hZ0.symm ≠ ℓ 2 := fun e => (hZ 2).1 (e ▸ hZm)
  have hEm : E ∉ line (Line := L) (V 0) Z hZ0.symm := fun h =>
    ne23_of_between hE (eq_of_mem_of_mem hm1 hV0m h01 h hE1)
  have hV2m : V 2 ∉ line (Line := L) (V 0) Z hZ0.symm := fun h =>
    hT.vertex_ne (by decide : (2 : Fin 3) ≠ 0) (eq_of_mem_of_mem hm1 h h21 hV0m h01)
  have hV1m : V 1 ∉ line (Line := L) (V 0) Z hZ0.symm := fun h =>
    hT.vertex_ne (by decide : (1 : Fin 3) ≠ 0) (eq_of_mem_of_mem hm2 h h12 hV0m h02)
  have hnc : ¬Collinear E (V 2) (V 1) :=
    not_collinear_of_not_mem hE1 h21 (ne13_of_between hE).symm (hT.not_mem 1)
  rcases OrderCore.pasch hnc hEm hV2m hV1m hV0m (between_symm hE) with
    ⟨W, hWm, hW⟩ | ⟨Y, hYm, hY⟩
  · have hW0 : W ∈ ℓ 0 := OrderCore.mem_of_between hW h2 h1
    have hWV0 : V 0 ≠ W := fun e => hT.not_mem 0 (e ▸ hW0)
    have hZW : Z ≠ W := fun e => (hZ 0).1 (e ▸ hW0)
    rcases between_trichotomy (collinear_of_mem hV0m hZm hWm) hZ0.symm hWV0 hZW with h | h | h
    · have hWV2 : SameSide (ℓ 2) W (V 2) :=
        sameSide_of_between_mem h12 (hT.not_mem 2) (between_symm hW)
      exact absurd ⟨V 0, h02, h⟩
        (OrderCore.sameSide_trans (hZ 2) (OrderCore.sameSide_symm hWV2)).2.2
    · exact ⟨W, between_symm hW, h⟩
    · exact absurd ⟨W, hW0, between_symm h⟩ (hZ 0).2.2
  · exfalso
    have hYE : SameSide (ℓ 2) Y E := sameSide_of_between_mem h12 hE2 (between_symm hY)
    have o : OppositeSides (ℓ 2) (V 2) E := ⟨hT.not_mem 2, hE2, V 0, h02, hE⟩
    have o' := OrderCore.opp_of_sameSide_opp hYE
      (OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp (hZ 2) o))
    obtain ⟨-, -, W, hW2, hYWZ⟩ := o'
    have hWm := OrderCore.mem_of_between hYWZ hYm hZm
    rw [eq_of_mem_of_mem hm2 hWm hW2 hV0m h02] at hYWZ
    have hY1 : SameSide (ℓ 1) Y (V 1) := sameSide_of_between_mem hE1 (hT.not_mem 1) hY
    exact (OrderCore.sameSide_trans hY1 (OrderCore.sameSide_symm (hZ 1))).2.2 ⟨V 0, h01, hYWZ⟩

/-- **No line lies entirely within the triangle.** -/
theorem TriangleLines.no_line_inside (hT : TriangleLines V ℓ) :
    ¬∃ l : L, ∀ Z : P, Z ∈ l → Z ∈ TriInside V ℓ := by
  rintro ⟨l, hl⟩
  obtain ⟨Z, -, -, hZ, -⟩ := exists_two_points (Point := P) l
  obtain ⟨W, hW, hV0ZW⟩ := hT.crossbar (hl Z hZ)
  have hWT : W ∈ TriPts V := Or.inr ⟨0, hW⟩
  have notl : ∀ X, X ∈ TriPts V → X ∉ l := fun X hX hXl => hT.not_mem_inside hX (hl X hXl)
  have hW0 : W ∈ ℓ 0 := hT.mem_line_of_side hW
  have hnc : ¬Collinear (V 0) W (V 1) :=
    OrderCore.not_collinear_left hW0 (hT.mem₁ 0) (ne12_of_between hW).symm (hT.not_mem 0)
  rcases OrderCore.pasch hnc (notl _ (Or.inl ⟨0, rfl⟩)) (notl _ hWT) (notl _ (Or.inl ⟨1, rfl⟩))
      hZ hV0ZW with ⟨Y, hYl, hY⟩ | ⟨Y, hYl, hY⟩
  · exact notl Y (Or.inr ⟨0, (OrderLin.trans₂ (between_symm hY) hW).1⟩) hYl
  · exact notl Y (Or.inr ⟨2, hY⟩) hYl

/-- **A line lying entirely outside the triangle**: all its points are neither points of the
triangle nor interior. -/
theorem TriangleLines.exists_line_outside (hT : TriangleLines V ℓ) :
    ∃ m : L, ∀ Z : P, Z ∈ m → Z ∉ TriPts V ∧ Z ∉ TriInside V ℓ := by
  have h21 : V 2 ∈ ℓ 1 := hT.mem₁ 1
  have h01 : V 0 ∈ ℓ 1 := hT.mem₂ 1
  have h02 : V 0 ∈ ℓ 2 := hT.mem₁ 2
  have h12 : V 1 ∈ ℓ 2 := hT.mem₂ 2
  have hl12 : ℓ 1 ≠ ℓ 2 := hT.lines_ne (by decide)
  obtain ⟨E, hE⟩ := exists_beyond (Line := L) (hT.vertex_ne (by decide : (1 : Fin 3) ≠ 0))
  obtain ⟨F, hF⟩ := exists_beyond (Line := L) (hT.vertex_ne (by decide : (2 : Fin 3) ≠ 0))
  have hE2 : E ∈ ℓ 2 := OrderCore.mem_of_between' hE h12 h02
  have hF1 : F ∈ ℓ 1 := OrderCore.mem_of_between' hF h21 h01
  have hE1 : E ∉ ℓ 1 := fun h => ne23_of_between hE (eq_of_mem_of_mem hl12 h01 h02 h hE2)
  have hF2 : F ∉ ℓ 2 := fun h => ne23_of_between hF (eq_of_mem_of_mem hl12 h01 h02 hF1 h)
  have hEF : E ≠ F := fun e => hF2 (e ▸ hE2)
  have hEm : E ∈ line (Line := L) E F hEF := mem_line_left hEF
  have hFm : F ∈ line (Line := L) E F hEF := mem_line_right hEF
  have hm2 : line (Line := L) E F hEF ≠ ℓ 2 := fun e => hF2 (e ▸ hFm)
  have hm1 : line (Line := L) E F hEF ≠ ℓ 1 := fun e => hE1 (e ▸ hEm)
  have k2 : ∀ W, W ∈ line (Line := L) E F hEF → W ∈ ℓ 2 → W = E := fun W h h' =>
    eq_of_mem_of_mem hm2 h h' hEm hE2
  have k1 : ∀ W, W ∈ line (Line := L) E F hEF → W ∈ ℓ 1 → W = F := fun W h h' =>
    eq_of_mem_of_mem hm1 h h' hFm hF1
  have hV0m : V 0 ∉ line (Line := L) E F hEF := fun h => ne23_of_between hE (k2 _ h h02)
  have hV1m : V 1 ∉ line (Line := L) E F hEF := fun h => ne13_of_between hE (k2 _ h h12)
  have hV2m : V 2 ∉ line (Line := L) E F hEF := fun h => ne13_of_between hF (k1 _ h h21)
  have s01 : SameSide (line (Line := L) E F hEF) (V 0) (V 1) := ⟨hV0m, hV1m, fun ⟨W, hWm, hb⟩ => by
    rw [k2 W hWm (OrderCore.mem_of_between hb h02 h12)] at hb
    exact not_between_swap23 hE (between_symm hb)⟩
  have s02 : SameSide (line (Line := L) E F hEF) (V 0) (V 2) := ⟨hV0m, hV2m, fun ⟨W, hWm, hb⟩ => by
    rw [k1 W hWm (OrderCore.mem_of_between hb h01 h21)] at hb
    exact not_between_swap23 hF (between_symm hb)⟩
  have s12 := OrderCore.sameSide_trans (OrderCore.sameSide_symm s01) s02
  refine ⟨line E F hEF, fun Z hZ => ⟨?_, ?_⟩⟩
  · rintro (⟨j, rfl⟩ | ⟨i, h⟩)
    · fin_cases j
      · exact hV0m hZ
      · exact hV1m hZ
      · exact hV2m hZ
    · fin_cases i
      · exact s12.2.2 ⟨Z, hZ, h⟩
      · exact s02.2.2 ⟨Z, hZ, between_symm h⟩
      · exact s01.2.2 ⟨Z, hZ, h⟩
  · intro hI
    have oF : OppositeSides (ℓ 2) Z F :=
      OrderCore.opp_of_sameSide_opp (hI 2) ⟨hT.not_mem 2, hF2, V 0, h02, hF⟩
    obtain ⟨-, -, W, hW2, hZWF⟩ := oF
    rw [k2 W (OrderCore.mem_of_between hZWF hZ hFm) hW2] at hZWF
    have oE : OppositeSides (ℓ 1) Z E :=
      OrderCore.opp_of_sameSide_opp (hI 1) ⟨hT.not_mem 1, hE1, V 0, h01, hE⟩
    obtain ⟨-, -, W', hW1, hZWE⟩ := oE
    rw [k1 W' (OrderCore.mem_of_between hZWE hZ hEm) hW1] at hZWE
    exact not_between_swap23 hZWF hZWE

end Triangle

/-- Joining two points of a convex set `S` disjoint from `T` by a broken line avoiding `T`. -/
theorem join_of_convex [HasBetween P] {S T : Set P}
    (hconv : ∀ X Y Z, X ∈ S → Y ∈ S → Between X Z Y → Z ∈ S) (hST : Disjoint S T) {A B : P}
    (hA : A ∈ S) (hB : B ∈ S) :
    ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = A ∧ w (Fin.last n) = B ∧
      Disjoint (BrokenLinePoints w) T := by
  by_cases hAB : A = B
  · subst hAB
    refine ⟨0, fun _ => A, fun i => i.elim0, rfl, rfl, Set.disjoint_left.2 ?_⟩
    rintro X (⟨i, rfl⟩ | ⟨i, -⟩)
    · exact Set.disjoint_left.1 hST hA
    · exact i.elim0
  · refine ⟨1, ![A, B], fun i => ?_, rfl, rfl, Set.disjoint_left.2 ?_⟩
    · fin_cases i; exact hAB
    · rintro X (⟨i, rfl⟩ | ⟨i, h⟩)
      · fin_cases i
        · exact Set.disjoint_left.1 hST hA
        · exact Set.disjoint_left.1 hST hB
      · fin_cases i
        exact Set.disjoint_left.1 hST (hconv A B X hA hB h)

/-- Joining a point of a convex set `S` with a point of a convex set `S'` through a common point
`Q`, avoiding `T`. -/
theorem join_of_convex₂ [HasBetween P] {S S' T : Set P}
    (hconv : ∀ X Y Z, X ∈ S → Y ∈ S → Between X Z Y → Z ∈ S)
    (hconv' : ∀ X Y Z, X ∈ S' → Y ∈ S' → Between X Z Y → Z ∈ S') (hST : Disjoint S T)
    (hS'T : Disjoint S' T) {A Q B : P} (hA : A ∈ S) (hQ : Q ∈ S) (hQ' : Q ∈ S') (hB : B ∈ S')
    (hAQ : A ≠ Q) (hQB : Q ≠ B) :
    ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = A ∧ w (Fin.last n) = B ∧
      Disjoint (BrokenLinePoints w) T := by
  refine ⟨2, ![A, Q, B], fun i => ?_, rfl, rfl, Set.disjoint_left.2 ?_⟩
  · fin_cases i
    · exact hAQ
    · exact hQB
  · rintro X (⟨i, rfl⟩ | ⟨i, h⟩)
    · fin_cases i
      · exact Set.disjoint_left.1 hST hA
      · exact Set.disjoint_left.1 hST hQ
      · exact Set.disjoint_left.1 hS'T hB
    · fin_cases i
      · exact Set.disjoint_left.1 hST (hconv A Q X hA hQ h)
      · exact Set.disjoint_left.1 hS'T (hconv' Q B X hQ' hB h)

section Triangle2

variable [HasLines P L] [HasBetween P] [hO : PlaneOrder P L] {V : Fin 3 → P} {ℓ : Fin 3 → L}
include hO

/-- Any broken line from an interior point to a point that is not interior meets the triangle. -/
theorem TriangleLines.brokenLine_meets (hT : TriangleLines V ℓ) {n : ℕ} (w : Fin (n + 1) → P)
    (h0 : w 0 ∈ TriInside V ℓ) (hn : w (Fin.last n) ∉ TriInside V ℓ) :
    (BrokenLinePoints w ∩ TriPts V).Nonempty := by
  classical
  have hex : ∃ m : ℕ, ∃ h : m < n + 1, w ⟨m, h⟩ ∉ TriInside V ℓ := ⟨n, by omega, hn⟩
  obtain ⟨hm, hwm⟩ := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro e
    have : (⟨Nat.find hex, hm⟩ : Fin (n + 1)) = 0 := Fin.ext e
    rw [this] at hwm
    exact hwm h0
  have hprev : w ⟨Nat.find hex - 1, by omega⟩ ∈ TriInside V ℓ := by
    by_contra h
    exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨by omega, h⟩
  obtain ⟨Z, hZ, hZs⟩ := hT.exit hprev _ hwm
  refine ⟨Z, ?_, hZ⟩
  rcases hZs with rfl | hb
  · exact Or.inl ⟨_, rfl⟩
  · refine Or.inr ⟨⟨Nat.find hex - 1, by omega⟩, ?_⟩
    have e2 : (⟨Nat.find hex - 1, by omega⟩ : Fin n).succ = ⟨Nat.find hex, hm⟩ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [e2]
    exact hb

/-- **Theorem 6 for a triangle given by its side lines.** -/
theorem TriangleLines.divides (hT : TriangleLines V ℓ) :
    ∃ I E : Set P, I.Nonempty ∧ E.Nonempty ∧ Disjoint I E ∧ I ∪ E = (TriPts V)ᶜ ∧
      (∀ A ∈ I, ∀ B ∈ E, ∀ (n : ℕ) (w : Fin (n + 1) → P), w 0 = A → w (Fin.last n) = B →
        (BrokenLinePoints w ∩ TriPts V).Nonempty) ∧
      (∀ A ∈ I, ∀ A' ∈ I, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = A ∧
        w (Fin.last n) = A' ∧ Disjoint (BrokenLinePoints w) (TriPts V)) ∧
      (∀ B ∈ E, ∀ B' ∈ E, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = B ∧
        w (Fin.last n) = B' ∧ Disjoint (BrokenLinePoints w) (TriPts V)) ∧
      (∃ l : L, ∀ X : P, X ∈ l → X ∈ E) ∧ ¬∃ l : L, ∀ X : P, X ∈ l → X ∈ I := by
  have hIT : Disjoint (TriInside V ℓ) (TriPts V) :=
    Set.disjoint_right.2 fun X hX => hT.not_mem_inside hX
  have hBT : ∀ i, Disjoint (TriBeyond V ℓ i) (TriPts V) := fun i =>
    Set.disjoint_right.2 fun X hX => hT.not_mem_beyond hX i
  have hBI : ∀ i X, X ∈ TriBeyond V ℓ i → X ∉ TriInside V ℓ := fun i X hX hI =>
    OrderCore.not_sameSide_of_opp (OrderCore.opp_symm hX) (hI i)
  have hBE : ∀ i X, X ∈ TriBeyond V ℓ i → X ∈ (TriPts V ∪ TriInside V ℓ)ᶜ := fun i X hX => by
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨fun h => hT.not_mem_beyond h i hX, hBI i X hX⟩
  have hconvB : ∀ i X Y Z, X ∈ TriBeyond V ℓ i → Y ∈ TriBeyond V ℓ i → Between X Z Y →
      Z ∈ TriBeyond V ℓ i := fun _ _ _ _ hX hY h => TriangleLines.beyond_convex hX hY h
  refine ⟨TriInside V ℓ, (TriPts V ∪ TriInside V ℓ)ᶜ, hT.inside_nonempty, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · obtain ⟨Q, hQ, -⟩ := hT.beyond_inter (by decide : (0 : Fin 3) ≠ 1)
    exact ⟨Q, hBE 0 Q hQ⟩
  · exact Set.disjoint_left.2 fun X hX hE => hE (Or.inr hX)
  · ext X
    simp only [Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro (h | h)
      · exact fun h' => hT.not_mem_inside h' h
      · exact fun h' => h (Or.inl h')
    · intro hX
      by_cases hI : X ∈ TriInside V ℓ
      · exact Or.inl hI
      · exact Or.inr fun h => h.elim hX hI
  · intro A hA B hB n w hw0 hwn
    refine hT.brokenLine_meets w (hw0 ▸ hA) ?_
    rw [hwn]
    exact fun h => hB (Or.inr h)
  · intro A hA A' hA'
    exact join_of_convex (fun X Y Z hX hY h => TriangleLines.inside_convex hX hY h) hIT hA hA'
  · intro B hB B' hB'
    simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hB hB'
    obtain ⟨i, hi⟩ := hT.mem_beyond hB.1 hB.2
    obtain ⟨j, hj⟩ := hT.mem_beyond hB'.1 hB'.2
    by_cases hB'i : B' ∈ TriBeyond V ℓ i
    · exact join_of_convex (hconvB i) (hBT i) hi hB'i
    by_cases hBj : B ∈ TriBeyond V ℓ j
    · exact join_of_convex (hconvB j) (hBT j) hBj hj
    have hij : i ≠ j := fun e => hB'i (e ▸ hj)
    obtain ⟨Q, hQi, hQj⟩ := hT.beyond_inter hij
    exact join_of_convex₂ (hconvB i) (hconvB j) (hBT i) (hBT j) hi hQi hQj hj
      (fun e => hBj (e ▸ hQj)) (fun e => hB'i (e ▸ hQi))
  · obtain ⟨m, hm⟩ := hT.exists_line_outside
    exact ⟨m, fun X hX => fun h => h.elim (hm X hX).1 (hm X hX).2⟩
  · exact hT.no_line_inside

end Triangle2


theorem finRotate_three (j : Fin 3) : finRotate 3 j = j + 1 := by fin_cases j <;> decide

/-- The points of a polygon with three vertices are the points of the triangle. -/
theorem polygonPoints_three [HasBetween P] (v : Fin 3 → P) : PolygonPoints v = TriPts v := by
  ext X
  constructor
  · rintro (h | ⟨j, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨j + 2, ?_⟩
      rw [fin3_add21, fin3_add22]
      rwa [finRotate_three] at h
  · rintro (h | ⟨i, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨i + 1, ?_⟩
      rwa [finRotate_three, fin3_add11]

/-- A simple polygon with three vertices has non-collinear vertices and side lines. -/
theorem IsSimplePolygon.exists_triangleLines [HasLines P L] [HasBetween P] [LineOrder P L]
    {v : Fin 3 → P} (hv : IsSimplePolygon v) : ∃ ℓ : Fin 3 → L, TriangleLines v ℓ := by
  have hinj := hv.2.1
  have hside := hv.2.2.1
  have hne : ∀ i : Fin 3, v (i + 1) ≠ v (i + 2) := fun i => hinj.ne (fin3_ne12 i)
  have hnc : ¬Collinear (v 0) (v 1) (v 2) := by
    intro hc
    rcases between_trichotomy (Line := L) hc (hinj.ne (by decide)) (hinj.ne (by decide))
      (hinj.ne (by decide)) with h | h | h
    · exact hside 0 1 (by rw [finRotate_three]; exact h)
    · exact hside 1 2 (by rw [finRotate_three]; exact between_symm h)
    · exact hside 2 0 (by rw [finRotate_three]; exact h)
  refine ⟨fun i => line (v (i + 1)) (v (i + 2)) (hne i), fun i => mem_line_left (hne i),
    fun i => mem_line_right (hne i), fun i h => ?_⟩
  have hc : Collinear (v (i + 1)) (v (i + 2)) (v i) :=
    ⟨_, mem_line_left (hne i), mem_line_right (hne i), h⟩
  fin_cases i
  · exact hnc hc.perm312
  · exact hnc hc.perm231
  · exact hnc hc

/-- **Theorem 6 for triangles** (plane geometry, groups I and II). -/
theorem theorem6_triangle [HasLines P L] [HasBetween P] [PlaneOrder P L] (v : Fin 3 → P)
    (hv : IsSimplePolygon v) : DividesLikePolygon (L := L) (PolygonPoints v) := by
  obtain ⟨ℓ, hT⟩ := hv.exists_triangleLines (L := L)
  rw [polygonPoints_three]
  exact hT.divides

/-- **Theorem 6 for triangles** whose vertices lie in a plane `α` of space: in the plane geometry
of `α`. -/
theorem theorem6_triangle_space {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [SpaceOrder P L Pl] (α : Pl) (v : Fin 3 → {A : P // A ∈ α}) (hv : IsSimplePolygon v) :
    DividesLikePolygon (L := {a : L // LiesInPlane (Point := P) a α}) (PolygonPoints v) :=
  theorem6_triangle v hv

/-!
## [th.7] Theorem 7

*(§ 4)*

> Every plane $\alpha$ divides the remaining points of space into two regions having the following properties: Every point $A$ of the one region determines with each point $B$ of the other region a segment $AB$, within which lies a point of $\alpha$. On the other hand, any two points $A$, $A'$ lying within the same region determine a segment $AA'$ containing no point of $\alpha$.

**Lean reading.** As Theorem 5, with `SeparatesInto`: `theorem7`: the points not in `α` are divided
into two regions, `cross A B` being "some point of `α` lies between `A` and `B`"; the regions are
unique up to order (`SeparatesInto.unique`). `theorem7_sides`: for any `A ∉ α` the regions are the
points on the same side of `α` as `A` and on the other side (`SameSidePlane`,
`OppositeSidesPlane`, introduced here and named by Hilbert in the next unit). From groups I and II
of space (`SpaceOrder`) only. Proof, "with the aid of theorem 5": for three points off `α`, a plane
`β` through them (I 3, or I 7 and Theorem 2 when they are collinear) meets `α`, as soon as a segment
between two of them contains a point of `α`, in a line `m` (Theorem 1); for points of `β`, a point
of `α` between two of them lies in `β` (I 5) and hence on `m`, so the transitivity properties of
the sides of `m` in `β` (Theorem 5 in the plane `β`, via the plane restriction) give those of the
sides of `α`. A point off `α` exists by the space clause of I 7, and a point beyond `α` by II 2.

**Status.** proved
-/

/-- `A` and `B` lie **on the same side of the plane `α`**: neither lies in `α`, and no point of `α`
lies between them. -/
def SameSidePlane [HasPlanes P Pl] [HasBetween P] (α : Pl) (A B : P) : Prop :=
  A ∉ α ∧ B ∉ α ∧ ¬∃ X : P, X ∈ α ∧ Between A X B

/-- `A` and `B` lie **on different sides of the plane `α`**: neither lies in `α`, and some point of
`α` lies between them. -/
def OppositeSidesPlane [HasPlanes P Pl] [HasBetween P] (α : Pl) (A B : P) : Prop :=
  A ∉ α ∧ B ∉ α ∧ ∃ X : P, X ∈ α ∧ Between A X B

section Theorem7

variable [HasLines P L] [HasPlanes P Pl] [HasBetween P] [hO : SpaceOrder P L Pl]
include hO

/-- A point between two points of a plane lies in the plane (I 5). -/
theorem mem_plane_of_between {β : Pl} {U X V : P} (h : Between U X V) (hU : U ∈ β)
    (hV : V ∈ β) : X ∈ β := by
  obtain ⟨g, hUg, hXg, hVg⟩ := collinear_of_between h
  exact liesInPlane_of_mem (ne13_of_between h) hUg hVg hU hV X hXg

/-- The section of `α` by a plane `β` through a point `A ∉ α` and a point `X ∈ α`: a line `m` of
`β`, such that for points of `β` the sides of `α` are the sides of `m`. -/
theorem section_line {α β : Pl} {A X : P} (hAβ : A ∈ β) (hAα : A ∉ α) (hXα : X ∈ α)
    (hXβ : X ∈ β) :
    ∃ m : L, LiesInPlane (Point := P) m β ∧
      ∀ U V : P, U ∈ β → V ∈ β → (SameSidePlane α U V ↔ SameSide m U V) ∧
        (OppositeSidesPlane α U V ↔ OppositeSides m U V) := by
  have hαβ : α ≠ β := fun e => hAα (e ▸ hAβ)
  obtain ⟨m, hm⟩ := planes_meet_in_line hαβ hXα hXβ
  refine ⟨m, fun Y hY => ((hm Y).1 hY).2, fun U V hU hV => ?_⟩
  have hnot : ∀ Y : P, Y ∈ β → (Y ∉ α ↔ Y ∉ m) := fun Y hY =>
    ⟨fun h h' => h ((hm Y).1 h').1, fun h h' => h ((hm Y).2 ⟨h', hY⟩)⟩
  have hcross : (∃ Y : P, Y ∈ α ∧ Between U Y V) ↔ ∃ Y : P, Y ∈ m ∧ Between U Y V :=
    ⟨fun ⟨Y, hYα, hb⟩ => ⟨Y, (hm Y).2 ⟨hYα, mem_plane_of_between hb hU hV⟩, hb⟩,
      fun ⟨Y, hYm, hb⟩ => ⟨Y, ((hm Y).1 hYm).1, hb⟩⟩
  unfold SameSidePlane OppositeSidesPlane SameSide OppositeSides
  rw [hnot U hU, hnot V hV, hcross]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem sameSidePlane_trans {α : Pl} {A B C : P} (h1 : SameSidePlane α A B)
    (h2 : SameSidePlane α B C) : SameSidePlane α A C := by
  refine ⟨h1.1, h2.2.1, ?_⟩
  rintro ⟨X, hXα, hAXC⟩
  obtain ⟨β, hAβ, hBβ, hCβ⟩ := exists_plane_three (L := L) α (B := B) (ne13_of_between hAXC)
  obtain ⟨m, hmβ, hs⟩ := section_line hAβ h1.1 hXα (mem_plane_of_between hAXC hAβ hCβ)
  have := OrderSpace.sameSide_trans hmβ hAβ hBβ hCβ ((hs A B hAβ hBβ).1.1 h1)
    ((hs B C hBβ hCβ).1.1 h2)
  exact ((hs A C hAβ hCβ).1.2 this).2.2 ⟨X, hXα, hAXC⟩

theorem oppPlane_of_sameSidePlane_opp {α : Pl} {A B C : P} (h1 : SameSidePlane α A B)
    (h2 : OppositeSidesPlane α B C) : OppositeSidesPlane α A C := by
  obtain ⟨-, -, Y, hYα, hBYC⟩ := id h2
  obtain ⟨β, hBβ, hAβ, hCβ⟩ := exists_plane_three (L := L) α (B := A) (ne13_of_between hBYC)
  obtain ⟨m, hmβ, hs⟩ := section_line hBβ h1.2.1 hYα (mem_plane_of_between hBYC hBβ hCβ)
  have := OrderSpace.opp_of_sameSide_opp hmβ hAβ hBβ hCβ ((hs A B hAβ hBβ).1.1 h1)
    ((hs B C hBβ hCβ).2.1 h2)
  exact (hs A C hAβ hCβ).2.2 this

theorem sameSidePlane_of_opp_opp {α : Pl} {A B C : P} (h1 : OppositeSidesPlane α A B)
    (h2 : OppositeSidesPlane α B C) : SameSidePlane α A C := by
  obtain ⟨hA, -, X, hXα, hAXB⟩ := id h1
  obtain ⟨β, hAβ, hCβ, hBβ⟩ := exists_plane_three (L := L) α (B := C) (ne13_of_between hAXB)
  obtain ⟨m, hmβ, hs⟩ := section_line hAβ hA hXα (mem_plane_of_between hAXB hAβ hBβ)
  have := OrderSpace.sameSide_of_opp_opp hmβ hAβ hBβ hCβ ((hs A B hAβ hBβ).2.1 h1)
    ((hs B C hBβ hCβ).2.1 h2)
  exact (hs A C hAβ hCβ).1.2 this

/-- **Theorem 7**, with the regions named: the two sides of the plane `α`. -/
theorem theorem7_sides (α : Pl) {A : P} (hA : A ∉ α) :
    SeparatesInto {X | X ∉ α} (fun X Y => ∃ Z, Z ∈ α ∧ Between X Z Y)
      {X | SameSidePlane α A X} {X | OppositeSidesPlane α A X} := by
  have symm1 : ∀ {X Y : P}, SameSidePlane α X Y → SameSidePlane α Y X := fun h =>
    ⟨h.2.1, h.1, fun ⟨Z, hZ, hb⟩ => h.2.2 ⟨Z, hZ, between_symm hb⟩⟩
  have symm2 : ∀ {X Y : P}, OppositeSidesPlane α X Y → OppositeSidesPlane α Y X := fun h =>
    ⟨h.2.1, h.1, let ⟨Z, hZ, hb⟩ := h.2.2; ⟨Z, hZ, between_symm hb⟩⟩
  refine ⟨⟨A, hA, hA, fun ⟨_, _, h⟩ => ne13_of_between h rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Q, -, -, hQ, -⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
    have hAQ : A ≠ Q := fun e => hA (e ▸ hQ)
    obtain ⟨D, hAQD⟩ := exists_beyond (Line := L) hAQ
    refine ⟨D, hA, fun hD => hA ?_, Q, hQ, hAQD⟩
    obtain ⟨g, hAg, hQg, hDg⟩ := collinear_of_between hAQD
    exact liesInPlane_of_mem (ne23_of_between hAQD) hQg hDg hQ hD A hAg
  · exact Set.disjoint_left.2 fun X h1 h2 => h1.2.2 h2.2.2
  · ext X
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h)
      · exact h.2.1
      · exact h.2.1
    · intro hX
      by_cases h : ∃ Z, Z ∈ α ∧ Between A Z X
      · exact Or.inr ⟨hA, hX, h⟩
      · exact Or.inl ⟨hA, hX, h⟩
  · intro X hX Y hY
    exact (oppPlane_of_sameSidePlane_opp (symm1 hX) hY).2.2
  · intro X hX Y hY
    exact (sameSidePlane_trans (symm1 hX) hY).2.2
  · intro X hX Y hY
    exact (sameSidePlane_of_opp_opp (symm2 hX) hY).2.2

/-- **Theorem 7.** Every plane divides the remaining points of space into two regions. -/
theorem theorem7 (α : Pl) :
    ∃ R₁ R₂ : Set P, SeparatesInto {X | X ∉ α} (fun X Y => ∃ Z, Z ∈ α ∧ Between X Z Y) R₁ R₂ := by
  obtain ⟨A, B, C, D, h⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
  have : ∃ X : P, X ∉ α := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact h ⟨α, hall A, hall B, hall C, hall D⟩
  obtain ⟨X, hX⟩ := this
  exact ⟨_, _, theorem7_sides α hX⟩

end Theorem7

/-!
## [s4.side_of_plane] Sides of a plane

*(§ 4)*

> Making use of the notation of theorem 7, we may now say: The points $A$, $A'$ are situated in space *upon one and the same side of the plane $\alpha$*, and the points $A$, $B$ are situated in space *upon different sides of the plane $\alpha$*.

**Lean reading.** The relations `SameSidePlane α` and `OppositeSidesPlane α` (defined with
Theorem 7) are Hilbert's: by `theorem7_sides` and `SeparatesInto.unique`, two points off `α` lie on
the same side iff they belong to one region of Theorem 7, and on different sides iff they belong to
different regions (`sides_of_plane_iff`, for any division of the points off `α` with the properties
of Theorem 7).

**Status.** proved
-/

/-- For any two regions `R₁`, `R₂` dividing the points off `α` as in Theorem 7, two points lie on the
same side of `α` iff they lie in the same region, and on different sides iff in different
regions. -/
theorem sides_of_plane_iff [HasLines P L] [HasPlanes P Pl] [HasBetween P] [SpaceOrder P L Pl]
    {α : Pl} {R₁ R₂ : Set P}
    (h : SeparatesInto {X | X ∉ α} (fun X Y => ∃ Z, Z ∈ α ∧ Between X Z Y) R₁ R₂) (A B : P) :
    (SameSidePlane α A B ↔ (A ∈ R₁ ∧ B ∈ R₁) ∨ (A ∈ R₂ ∧ B ∈ R₂)) ∧
      (OppositeSidesPlane α A B ↔ (A ∈ R₁ ∧ B ∈ R₂) ∨ (A ∈ R₂ ∧ B ∈ R₁)) := by
  obtain ⟨-, -, hd, hu, h12, h11, h22⟩ := h
  have memS : ∀ X, X ∉ α ↔ X ∈ R₁ ∨ X ∈ R₂ := fun X => by
    rw [← Set.mem_union, hu]; rfl
  have cross_symm : ∀ X Y : P, (∃ Z, Z ∈ α ∧ Between X Z Y) → ∃ Z, Z ∈ α ∧ Between Y Z X :=
    fun X Y ⟨Z, hZ, hb⟩ => ⟨Z, hZ, between_symm (Line := L) hb⟩
  constructor
  · constructor
    · rintro ⟨hA, hB, hc⟩
      rcases (memS A).1 hA with hA1 | hA2 <;> rcases (memS B).1 hB with hB1 | hB2
      · exact Or.inl ⟨hA1, hB1⟩
      · exact absurd (h12 A hA1 B hB2) hc
      · exact absurd (cross_symm _ _ (h12 B hB1 A hA2)) hc
      · exact Or.inr ⟨hA2, hB2⟩
    · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
      · exact ⟨(memS A).2 (Or.inl hA), (memS B).2 (Or.inl hB), h11 A hA B hB⟩
      · exact ⟨(memS A).2 (Or.inr hA), (memS B).2 (Or.inr hB), h22 A hA B hB⟩
  · constructor
    · rintro ⟨hA, hB, hc⟩
      rcases (memS A).1 hA with hA1 | hA2 <;> rcases (memS B).1 hB with hB1 | hB2
      · exact absurd hc (h11 A hA1 B hB1)
      · exact Or.inl ⟨hA1, hB2⟩
      · exact Or.inr ⟨hA2, hB1⟩
      · exact absurd hc (h22 A hA2 B hB2)
    · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
      · exact ⟨(memS A).2 (Or.inl hA), (memS B).2 (Or.inr hB), h12 A hA B hB⟩
      · exact ⟨(memS A).2 (Or.inr hA), (memS B).2 (Or.inl hB), cross_symm _ _ (h12 B hB A hA)⟩

/-!
## [s4.no_new_space_axioms] No new space axioms of order are needed

*(§ 4)*

> Theorem 7 gives us the most important facts relating to the order of sequence of the elements of space. These facts are the results, exclusively, of the axioms already considered, and, hence, no new space axioms are required in group II.

**Lean reading.** A remark on the proof of Theorem 7: `theorem7` assumes only `SpaceOrder`, i.e.
groups I and II with II 5 stated in each plane; no axiom of order about space beyond the plane
axiom II 5 is used.

**Status.** remark
-/

/-!
## [s5.essential_assertion] The second assertion of the axiom of parallels is the essential one

*(§ 5)*

> The latter of these statements is the essential one, and it may also be expressed as follows:

**Lean reading.** "May also be expressed as follows" announces the equivalence of the second
assertion (`AxiomIIIUnique`) with Theorem 8, proved in the next unit. "The essential one" is a
judgment: the first assertion (existence of a non-intersecting line) is the part that can be
obtained from the other groups of axioms (with congruence, in later chapters); Hilbert does not
state or prove that here, and it is not formalized in this file.

**Status.** remark
-/

/-!
## [th.8] Theorem 8

*(§ 5)*

> If two straight lines $a$, $b$ of a plane do not meet a third straight line $c$ of the same plane, then they do not meet each other.

**Lean reading.** Hilbert states Theorem 8 as an equivalent form of the second assertion of the
axiom of parallels (`AxiomIIIUnique` of Basic.lean, unit `s5.two_assertions`: "The latter of these
statements is the essential one, and it may also be expressed as follows"), and proves both
directions ("For, if `a`, `b` had a point `A` in common … Conversely, the second part of the axiom
of parallels … follows as a consequence of theorem 8"). `Theorem8Statement`: for *distinct* lines
`a`, `b` ("two straight lines"; equal lines meet as soon as they have a point) not meeting `c`,
`a` and `b` do not meet. `theorem8`: it follows from `AxiomIIIUnique`;
`axiomIIIUnique_of_theorem8`: the converse; `axiomIIIUnique_iff_theorem8`: the equivalence, and
`theorem8_of_parallels` for a plane geometry with group III. Nothing but the relation "lies on" is
used: not even group I is needed. In space (`Theorem8Space`, `AxiomIIIUniqueSpace`) the lines are
lines of a plane `α`, and the equivalence `axiomIIIUniqueSpace_iff_theorem8Space` holds in the same
way; `theorem8_space` derives Theorem 8 from axiom III in space.

**Status.** proved
-/

/-- **Theorem 8** as a statement (plane geometry): two distinct lines not meeting a third line do
not meet each other. -/
def Theorem8Statement (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  ∀ a b c : L, a ≠ b → ¬Meets (Point := P) a c → ¬Meets (Point := P) b c → ¬Meets (Point := P) a b

/-- **Theorem 8** follows from the second assertion of the axiom of parallels. -/
theorem theorem8 [HasLines P L] (h : AxiomIIIUnique P) : Theorem8Statement P := by
  rintro a b c hab hac hbc ⟨A, hAa, hAb⟩
  have hAc : A ∉ c := fun hAc => hac ⟨A, hAa, hAc⟩
  exact hab (h c A hAc a b hAa hac hAb hbc)

/-- Conversely, the second assertion of the axiom of parallels follows from Theorem 8. -/
theorem axiomIIIUnique_of_theorem8 [HasLines P L] (h : Theorem8Statement P) :
    AxiomIIIUnique P := by
  intro a A _ b c hAb hb hAc hc
  by_contra hbc
  exact h b c a hbc hb hc ⟨A, hAb, hAc⟩

/-- **Theorem 8 is equivalent to the second assertion of the axiom of parallels.** -/
theorem axiomIIIUnique_iff_theorem8 [HasLines P L] : AxiomIIIUnique P ↔ Theorem8Statement P :=
  ⟨theorem8, axiomIIIUnique_of_theorem8⟩

/-- **Theorem 8** in a plane geometry with the axiom of parallels. -/
theorem theorem8_of_parallels [HasLines P L] [PlaneParallels P L] : Theorem8Statement P :=
  theorem8 ((axiomIII_iff P).1 PlaneParallels.ax_III).2

/-- The second assertion of the axiom of parallels in space: in each plane. -/
def AxiomIIIUniqueSpace (P : Type u) {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] :
    Prop :=
  ∀ (α : Pl) (a : L) (A : P), LiesInPlane a α → A ∈ α → A ∉ a → ∀ b c : L,
    LiesInPlane b α → A ∈ b → ¬Meets b a → LiesInPlane c α → A ∈ c → ¬Meets c a → b = c

/-- **Theorem 8** in space: for lines of a plane. -/
def Theorem8Space (P : Type u) {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] :
    Prop :=
  ∀ (α : Pl) (a b c : L), LiesInPlane (Point := P) a α → LiesInPlane (Point := P) b α →
    LiesInPlane (Point := P) c α → a ≠ b → ¬Meets (Point := P) a c → ¬Meets (Point := P) b c →
      ¬Meets (Point := P) a b

theorem axiomIIIUniqueSpace_iff_theorem8Space [HasLines P L] [HasPlanes P Pl] :
    AxiomIIIUniqueSpace (L := L) (Pl := Pl) P ↔ Theorem8Space (L := L) (Pl := Pl) P := by
  constructor
  · rintro h α a b c ha hb hc hab hac hbc ⟨A, hAa, hAb⟩
    have hAc : A ∉ c := fun hAc => hac ⟨A, hAa, hAc⟩
    exact hab (h α c A hc (ha A hAa) hAc a b ha hAa hac hb hAb hbc)
  · intro h α a A _ _ _ b c hb hAb hba hc hAc hca
    by_contra hbc
    exact h α b c a hb hc ‹LiesInPlane a α› hbc hba hca ⟨A, hAb, hAc⟩

/-- **Theorem 8** in space, from the axiom of parallels. -/
theorem theorem8_space [HasLines P L] [HasPlanes P Pl] [SpaceParallels P L Pl] :
    Theorem8Space (L := L) (Pl := Pl) P := by
  refine axiomIIIUniqueSpace_iff_theorem8Space.1 ?_
  intro α a A ha hA hAa b c hb hAb hba hc hAc hca
  exact (SpaceParallels.ax_III α a A ha hA hAa).unique ⟨hb, hAb, hba⟩ ⟨hc, hAc, hca⟩

end HilbertFoundations
