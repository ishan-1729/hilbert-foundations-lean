import HilbertFoundations.IndependenceAux2

/-!
# The first assertion of the axiom of parallels in space (helper of `Independence.lean`)

Hilbert states the first assertion of the axiom of parallels (§ 10) for a plane `α` of a geometry of
space: "in the plane `α`, there is always a straight line passing through `A` which does not
intersect the given line `a`". `IndependenceAux2.lean` proves it for plane geometry
(`ParallelExists.axiomIIIExists`). Here the space version is derived from it:

* the restriction of the congruences of space to a plane `α` (the points `{A // A ∈ α}`, the lines
  `{a // LiesInPlane a α}` of `Order.lean`, with the congruences of space): `planeHasSegCong`,
  `planeHasAngCong`, and `planeCongruence`: groups I, II, IV of space give groups I, II, IV of plane
  geometry in every plane (laying off of angles is the space IV 4 in the plane `α`);
* `ParallelExists.axiomIIIExistsSpace`: in every geometry of space satisfying groups I, II, IV,
  through a point `A` of a plane `α` off a line `a` of `α` there is a line of `α` not meeting `a`.
-/

namespace HilbertFoundations

section PlaneRestrictionCong

variable {P : Type*} {L : Type*} {Pl : Type*} [HasLines P L] [HasPlanes P Pl]

/-- Congruence of segments of the plane `α`: congruence in space. -/
instance planeHasSegCong [HasSegCong P] (α : Pl) : HasSegCong {A : P // A ∈ α} :=
  ⟨fun A B A' B' => SegCong (A : P) B A' B'⟩

/-- Congruence of angles of the plane `α`: congruence in space. -/
instance planeHasAngCong [HasAngCong P] (α : Pl) : HasAngCong {A : P // A ∈ α} :=
  ⟨fun A O B A' O' B' => AngCong (A : P) O B A' O' B'⟩

theorem restrict_segCong_iff [HasSegCong P] {α : Pl} {A B A' B' : {A : P // A ∈ α}} :
    SegCong A B A' B' ↔ SegCong (A : P) B A' B' := Iff.rfl

theorem restrict_angCong_iff [HasAngCong P] {α : Pl} {A O B A' O' B' : {A : P // A ∈ α}} :
    AngCong A O B A' O' B' ↔ AngCong (A : P) O B A' O' B' := Iff.rfl

theorem restrict_ne_iff {α : Pl} {A B : {A : P // A ∈ α}} : A ≠ B ↔ (A : P) ≠ B :=
  Subtype.ext_iff.not

variable [HasBetween P] [hS : SpaceOrder P L Pl] {α : Pl}
include hS

theorem restrict_not_collinear_iff {A B C : {A : P // A ∈ α}} :
    ¬Collinear A B C ↔ ¬Collinear (A : P) B C :=
  (restrict_collinear_iff (L := L)).not

theorem restrict_sameSidePt_iff {O A X : {A : P // A ∈ α}} :
    SameSidePt O A X ↔ SameSidePt (O : P) A X := by
  unfold SameSidePt
  rw [restrict_ne_iff, restrict_ne_iff, restrict_collinear_iff (L := L), restrict_between_iff]

theorem restrict_mem_ray_iff {O A X : {A : P // A ∈ α}} :
    X ∈ ray O A ↔ (X : P) ∈ ray (O : P) A :=
  restrict_sameSidePt_iff

/-- The points of a half-ray of the plane `α` lie in `α`. -/
theorem mem_plane_of_mem_ray {O A : {A : P // A ∈ α}} {X : P} (h : X ∈ ray (O : P) A) : X ∈ α := by
  obtain ⟨hAO, -, ⟨g, hAg, hOg, hXg⟩, -⟩ := h
  exact liesInPlane_of_mem hAO hAg hOg A.2 O.2 X hXg

theorem restrict_ray_eq_iff {O A C : {A : P // A ∈ α}} :
    ray O A = ray O C ↔ ray (O : P) A = ray (O : P) C := by
  constructor
  · intro h
    ext X
    constructor
    · intro hX
      have := (restrict_mem_ray_iff (L := L) (X := ⟨X, mem_plane_of_mem_ray (L := L) hX⟩)).2 hX
      rw [h] at this
      exact (restrict_mem_ray_iff (L := L)).1 this
    · intro hX
      have := (restrict_mem_ray_iff (L := L) (X := ⟨X, mem_plane_of_mem_ray (L := L) hX⟩)).2 hX
      rw [← h] at this
      exact (restrict_mem_ray_iff (L := L)).1 this
  · intro h
    ext X
    rw [restrict_mem_ray_iff (L := L), restrict_mem_ray_iff (L := L), h]

theorem restrict_sameAngle_iff {A O B C D : {A : P // A ∈ α}} :
    SameAngle A O B C D ↔ SameAngle (A : P) O B C D := by
  unfold SameAngle
  rw [Set.pair_eq_pair_iff, Set.pair_eq_pair_iff, restrict_ray_eq_iff (L := L),
    restrict_ray_eq_iff (L := L), restrict_ray_eq_iff (L := L), restrict_ray_eq_iff (L := L)]

/-- The interior of an angle of the plane `α`, read in the plane or in space. -/
theorem restrict_mem_interior_iff {A O B X : {A : P // A ∈ α}} (hOA : (O : P) ≠ A)
    (hOB : (O : P) ≠ B) : X ∈ Interior A O B ↔ (X : P) ∈ Interior (A : P) O B := by
  constructor
  · intro hX a b hOa hAa hOb hBb
    have h := hX ⟨a, liesInPlane_of_mem hOA hOa hAa O.2 A.2⟩
      ⟨b, liesInPlane_of_mem hOB hOb hBb O.2 B.2⟩ hOa hAa hOb hBb
    exact ⟨restrict_sameSide_iff.1 h.1, restrict_sameSide_iff.1 h.2⟩
  · intro hX a b hOa hAa hOb hBb
    have h := hX (a : L) (b : L) hOa hAa hOb hBb
    exact ⟨restrict_sameSide_iff.2 h.1, restrict_sameSide_iff.2 h.2⟩

theorem mem_plane_of_mem_segWithEnds {A B : {A : P // A ∈ α}} {X : P}
    (h : X ∈ SegWithEnds (A : P) B) : X ∈ α := by
  rcases h with rfl | rfl | h
  · exact A.2
  · exact B.2
  · obtain ⟨g, hAg, hXg, hBg⟩ := collinear_of_between (Line := L) h
    exact liesInPlane_of_mem (ne13_of_between (Line := L) h) hAg hBg A.2 B.2 X hXg

theorem restrict_segmentsMeetOnlyAt {A B C : {A : P // A ∈ α}} (h : SegmentsMeetOnlyAt A B C) :
    SegmentsMeetOnlyAt (A : P) B C := by
  obtain ⟨hc, hAB, hBC, hX⟩ := h
  refine ⟨(restrict_collinear_iff (L := L)).1 hc, restrict_ne_iff.1 hAB, restrict_ne_iff.1 hBC,
    fun X h1 h2 => ?_⟩
  have hXα := mem_plane_of_mem_segWithEnds (L := L) h1
  have e := hX ⟨X, hXα⟩ (by
    rcases h1 with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)) (by
    rcases h2 with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h))
  exact congrArg Subtype.val e

omit hS in
/-- **The points and lines of a plane of space satisfy groups I, II, IV of plane geometry**, with
the congruences of space. -/
theorem planeCongruence [HasSegCong P] [HasAngCong P] [h : SpaceCongruence P L Pl] (α : Pl) :
    PlaneCongruence {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} := by
  have hPO := planeOrder (L := L) (h := h.toSpaceOrder) α
  have hSO := h.toSpaceOrder
  -- IV 1: the point laid off in space lies on the half-ray, hence in `α`
  have hIV1 : AxiomIV1LayOff {A : P // A ∈ α} := by
    intro A B A' C' hAB hA'C'
    obtain ⟨B', ⟨hr, hc⟩, hu⟩ :=
      h.ax_IV1 A B A' C' (restrict_ne_iff.1 hAB) (restrict_ne_iff.1 hA'C')
    have hB'α : B' ∈ α := mem_plane_of_mem_ray (L := L) (O := A') (A := C') hr
    refine ⟨⟨B', hB'α⟩, ⟨(restrict_sameSidePt_iff (L := L)).2 hr, hc⟩, fun Y ⟨hY, hYc⟩ => ?_⟩
    exact Subtype.ext (hu Y ⟨(restrict_sameSidePt_iff (L := L)).1 hY, hYc⟩)
  -- IV 4: laying off in the plane `α`
  have hIV4 : AxiomIV4LayOff {A : P // A ∈ α} := by
    intro A O B a' O' A' D' h1 hO' hA' hA'O' hD'
    have hO'A' : (O' : P) ≠ A' := fun e => hA'O' (Subtype.ext e.symm)
    obtain ⟨B', hB'α, hB'a, hc, hint, hu⟩ :=
      h.ax_IV4 A O B α (a' : L) O' A' D' ((restrict_not_collinear_iff (L := L)).1 h1) a'.2 hO' hA'
        (restrict_ne_iff.1 hA'O') D'.2 hD'
    have hO'B' : (O' : P) ≠ B' := fun e => hB'a (e ▸ hO')
    refine ⟨⟨B', hB'α⟩, hB'a, hc, fun X hX => ?_, fun B'' hB''a hc'' hint'' => ?_⟩
    · exact restrict_sameSide_iff.2
        (hint X X.2 ((restrict_mem_interior_iff (L := L) (O := O') (A := A') (B := ⟨B', hB'α⟩)
          hO'A' hO'B').1 hX))
    · have hO'B'' : (O' : P) ≠ B'' := fun e => hB''a (by rw [restrict_mem_iff, ← e]; exact hO')
      have e := hu B'' B''.2 hB''a hc'' (fun X hXα hX => restrict_sameSide_iff.1
        (hint'' ⟨X, hXα⟩ ((restrict_mem_interior_iff (L := L) (X := ⟨X, hXα⟩) hO'A' hO'B'').2 hX)))
      exact (restrict_ray_eq_iff (L := L) (O := O') (A := B'') (C := ⟨B', hB'α⟩)).2 e
  exact
    { hPO with
      segCong_swap := fun A B A' B' hc => h.segCong_swap A B A' B' hc
      ax_IV1 := hIV1
      ax_IV1_refl := fun A B hAB => h.ax_IV1_refl A B (restrict_ne_iff.1 hAB)
      ax_IV2 := fun A B A' B' A'' B'' h1 h2 h3 h4 h5 =>
        h.ax_IV2 A B A' B' A'' B'' (restrict_ne_iff.1 h1) (restrict_ne_iff.1 h2)
          (restrict_ne_iff.1 h3) h4 h5
      ax_IV3 := fun A B C A' B' C' h1 h2 h3 h4 =>
        h.ax_IV3 A B C A' B' C' (restrict_segmentsMeetOnlyAt (L := L) h1)
          (restrict_segmentsMeetOnlyAt (L := L) h2) h3 h4
      angCong_wd := fun A O B C D A' O' B' C' D' h1 h2 h3 h4 h5 =>
        h.angCong_wd A O B C D A' O' B' C' D' ((restrict_not_collinear_iff (L := L)).1 h1)
          ((restrict_not_collinear_iff (L := L)).1 h2) ((restrict_sameAngle_iff (L := L)).1 h3)
          ((restrict_sameAngle_iff (L := L)).1 h4) h5
      ax_IV4_refl := fun A O B h1 => h.ax_IV4_refl A O B ((restrict_not_collinear_iff (L := L)).1 h1)
      ax_IV5 := fun A O B A' O' B' A'' O'' B'' h1 h2 h3 h4 h5 =>
        h.ax_IV5 A O B A' O' B' A'' O'' B'' ((restrict_not_collinear_iff (L := L)).1 h1)
          ((restrict_not_collinear_iff (L := L)).1 h2) ((restrict_not_collinear_iff (L := L)).1 h3)
          h4 h5
      ax_IV4 := hIV4
      ax_IV6 := fun A B C A' B' C' h1 h2 h3 h4 h5 =>
        h.ax_IV6 A B C A' B' C' ((restrict_not_collinear_iff (L := L)).1 h1)
          ((restrict_not_collinear_iff (L := L)).1 h2) h3 h4 h5 }

end PlaneRestrictionCong

namespace ParallelExists

/-- **The first assertion of the axiom of parallels in space**: in a geometry of space satisfying
groups I, II, IV, through a point `A` of a plane `α` off a line `a` of `α` there is a line of `α`
not meeting `a`. -/
theorem axiomIIIExistsSpace {P : Type*} {L : Type*} {Pl : Type*} [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [HasSegCong P] [HasAngCong P] [h : SpaceCongruence P L Pl] (α : Pl) (a : L)
    (A : P) (ha : LiesInPlane (Point := P) a α) (hAα : A ∈ α) (hAa : A ∉ a) :
    ∃ b : L, LiesInPlane (Point := P) b α ∧ A ∈ b ∧ ¬Meets (Point := P) b a := by
  have hG := planeCongruence (P := P) (L := L) α
  obtain ⟨b, hAb, hb⟩ := axiomIIIExists (P := {A : P // A ∈ α})
    (L := {a : L // LiesInPlane (Point := P) a α}) ⟨a, ha⟩ ⟨A, hAα⟩ hAa
  refine ⟨b, b.2, hAb, fun ⟨X, hXb, hXa⟩ => hb ⟨⟨X, ha X hXa⟩, hXb, hXa⟩⟩

end ParallelExists

end HilbertFoundations
