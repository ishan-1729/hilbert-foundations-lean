import HilbertFoundations.Commentary

/-!
# Convex parts of a plane (helper for `CommentaryClose.lean`)

Dehn's geometries of the Conclusion (units `concl.semi_euclidean`, `concl.non_legendrian`) are
*parts* of a plane: the points at finite distance of the plane over a non-archimedean field, with
the lines that meet that part. This file constructs such a restriction once and for all.

`ConvexPart P L`: a set `S` of points of a plane that is convex (with two points it contains the
points between them), meets every half-ray emanating from one of its points, and contains three
non-collinear points. Its points `σ.Pt` (a subtype) and the lines meeting it `σ.Ln`, with the
betweenness and the congruences of the plane, form a geometry:

* `ConvexPart.instPlaneOrder`: groups I and II hold in the part when they hold in the plane;
* `ConvexPart.planeCongruence`: groups I, II, IV hold in the part when they hold in the plane and
  segments laid off from points of the part stay in the part (`LayOffClosed`).

The notions of the part agree with those of the plane (`collinear_iff`, `sameSide_iff`,
`sameSidePt_iff`, `mem_ray_iff`, `mem_interior_iff`), and the statements about the sum of the angles
of a triangle transfer (`angleSumEqTwoRight_of_plane`).
-/

namespace HilbertFoundations

universe u v

/-- A **convex part** of a plane: a convex set of points meeting every half-ray that emanates from
one of its points and containing three non-collinear points. -/
structure ConvexPart (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] where
  /-- The points of the part. -/
  S : Set P
  convex : ∀ A B X : P, A ∈ S → B ∈ S → Between A X B → X ∈ S
  ray_meets : ∀ O X : P, O ∈ S → X ≠ O → ∃ Y : P, Y ∈ S ∧ Y ∈ ray (Line := L) O X
  noncollinear : ∃ A B C : P, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ ¬Collinear (Line := L) A B C

namespace ConvexPart

open Conclusion

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]

/-- The points of a convex part. -/
def Pt (σ : ConvexPart P L) : Type u := {A : P // A ∈ σ.S}

/-- The lines of a convex part: the lines of the plane that meet it. -/
def Ln (σ : ConvexPart P L) : Type v := {a : L // ∃ A : P, A ∈ σ.S ∧ A ∈ a}

variable (σ : ConvexPart P L)

instance instHasLines : HasLines σ.Pt σ.Ln := ⟨fun A a => A.1 ∈ a.1⟩

instance instHasBetween : HasBetween σ.Pt := ⟨fun A B C => Between A.1 B.1 C.1⟩

instance instHasSegCong [HasSegCong P] : HasSegCong σ.Pt :=
  ⟨fun A B C D => SegCong A.1 B.1 C.1 D.1⟩

instance instHasAngCong [HasAngCong P] : HasAngCong σ.Pt :=
  ⟨fun A O B A' O' B' => AngCong A.1 O.1 B.1 A'.1 O'.1 B'.1⟩

variable {σ}

theorem mem_iff {A : σ.Pt} {a : σ.Ln} : A ∈ a ↔ A.1 ∈ a.1 := Iff.rfl

theorem between_iff {A B C : σ.Pt} : Between A B C ↔ Between A.1 B.1 C.1 := Iff.rfl

theorem segCong_iff [HasSegCong P] {A B C D : σ.Pt} :
    SegCong A B C D ↔ SegCong A.1 B.1 C.1 D.1 := Iff.rfl

theorem angCong_iff [HasAngCong P] {A O B A' O' B' : σ.Pt} :
    AngCong A O B A' O' B' ↔ AngCong A.1 O.1 B.1 A'.1 O'.1 B'.1 := Iff.rfl

theorem ne_iff {A B : σ.Pt} : A ≠ B ↔ A.1 ≠ B.1 := not_congr Subtype.ext_iff

/-- Collinearity in the part is collinearity in the plane. -/
theorem collinear_iff {A B C : σ.Pt} :
    Collinear (Line := σ.Ln) A B C ↔ Collinear (Line := L) A.1 B.1 C.1 :=
  ⟨fun ⟨a, hA, hB, hC⟩ => ⟨a.1, hA, hB, hC⟩,
    fun ⟨a, hA, hB, hC⟩ => ⟨⟨a, A.1, A.2, hA⟩, hA, hB, hC⟩⟩

/-- The sides of a line of the part are those of the plane (convexity). -/
theorem sameSide_iff {a : σ.Ln} {A B : σ.Pt} : SameSide a A B ↔ SameSide a.1 A.1 B.1 := by
  constructor
  · rintro ⟨hA, hB, h⟩
    exact ⟨hA, hB, fun ⟨X, hX, hb⟩ => h ⟨⟨X, σ.convex _ _ _ A.2 B.2 hb⟩, hX, hb⟩⟩
  · rintro ⟨hA, hB, h⟩
    exact ⟨hA, hB, fun ⟨X, hX, hb⟩ => h ⟨X.1, hX, hb⟩⟩

theorem sameSidePt_iff {O A B : σ.Pt} :
    SameSidePt (Line := σ.Ln) O A B ↔ SameSidePt (Line := L) O.1 A.1 B.1 := by
  unfold SameSidePt
  rw [ne_iff, ne_iff, collinear_iff, between_iff]

theorem mem_ray_iff {O A X : σ.Pt} :
    X ∈ ray (Line := σ.Ln) O A ↔ X.1 ∈ ray (Line := L) O.1 A.1 := sameSidePt_iff

/-- The interior of an angle of the part is that of the plane. -/
theorem mem_interior_iff {A O B X : σ.Pt} :
    X ∈ Interior (Line := σ.Ln) A O B ↔ X.1 ∈ Interior (Line := L) A.1 O.1 B.1 := by
  constructor
  · intro h a b hOa hAa hOb hBb
    have := h ⟨a, O.1, O.2, hOa⟩ ⟨b, O.1, O.2, hOb⟩ hOa hAa hOb hBb
    exact ⟨sameSide_iff.1 this.1, sameSide_iff.1 this.2⟩
  · intro h a b hOa hAa hOb hBb
    have := h a.1 b.1 hOa hAa hOb hBb
    exact ⟨sameSide_iff.2 this.1, sameSide_iff.2 this.2⟩

section Order

variable [hO : PlaneOrder P L]
include hO

/-- **Groups I and II hold in a convex part of a plane.** -/
instance instPlaneOrder : PlaneOrder σ.Pt σ.Ln :=
  planeOrder_iff_core.2
    { ax_I1 := fun A B h => by
        obtain ⟨a, hA, hB⟩ := exists_line (Line := L) (ne_iff.1 h)
        exact ⟨⟨a, A.1, A.2, hA⟩, hA, hB⟩
      ax_I2 := fun A B a b h hAa hBa hAb hBb =>
        Subtype.ext (line_unique (ne_iff.1 h) hAa hBa hAb hBb)
      ax_I7_line := fun a => by
        obtain ⟨A, hAS, hAa⟩ := a.2
        obtain ⟨X, Y, hXY, hX, hY⟩ := exists_two_points (Point := P) a.1
        obtain ⟨Z, hZA, hZ⟩ : ∃ Z : P, Z ≠ A ∧ Z ∈ a.1 := by
          by_cases hXA : X = A
          · exact ⟨Y, fun e => hXY (hXA.trans e.symm), hY⟩
          · exact ⟨X, hXA, hX⟩
        obtain ⟨W, hWS, hW⟩ := σ.ray_meets A Z hAS hZA
        exact ⟨⟨A, hAS⟩, ⟨W, hWS⟩, fun e => ne_of_mem_ray (L := L) hW (congrArg Subtype.val e).symm, hAa,
          mem_of_collinear (L := L) (collinear_of_mem_ray (L := L) hW) hZA.symm hAa hZ⟩
      ax_I7_noncollinear := by
        obtain ⟨A, B, C, hA, hB, hC, h⟩ := σ.noncollinear
        exact ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, fun hc => h (collinear_iff.1 hc)⟩
      between_onLine := fun A B C h =>
        ⟨ne_iff.2 (ne12_of_between (Line := L) h), ne_iff.2 (ne13_of_between (Line := L) h),
          ne_iff.2 (ne23_of_between (Line := L) h),
          collinear_iff.2 (collinear_of_between (Line := L) h)⟩
      ax_II1 := fun A B C _ h => between_symm (Point := P) (Line := L) h
      ax_II2 := fun A C a _ _ h => by
        have hAC := ne_iff.1 h
        obtain ⟨B, hB⟩ := exists_between (Line := L) hAC
        obtain ⟨D, hD⟩ := exists_beyond (Line := L) hAC
        obtain ⟨E, hES, hE⟩ := σ.ray_meets C.1 D C.2 (ne23_of_between (Line := L) hD).symm
        exact ⟨⟨⟨B, σ.convex _ _ _ A.2 C.2 hB⟩, hB⟩, ⟨E, hES⟩,
          between_of_mem_rays (P := P) (L := L) hD (mem_ray_self' (P := P) (L := L) hAC) hE⟩
      ax_II3 := fun A B C hc hAB hAC hBC =>
        LineOrder.ax_II3 (Point := P) (Line := L) A.1 B.1 C.1 (collinear_iff.1 hc) (ne_iff.1 hAB)
          (ne_iff.1 hAC) (ne_iff.1 hBC)
      ax_II5 := fun A B C a h hA hB hC ⟨X, hX, hb⟩ => by
        rcases pasch (Point := P) (Line := L) (fun hc => h (collinear_iff.2 hc)) hA hB hC hX hb with ⟨Y, hY, hb'⟩ | ⟨Y, hY, hb'⟩
        · exact Or.inl ⟨⟨Y, σ.convex _ _ _ B.2 C.2 hb'⟩, hY, hb'⟩
        · exact Or.inr ⟨⟨Y, σ.convex _ _ _ A.2 C.2 hb'⟩, hY, hb'⟩ }


/-- Equality of half-rays of the part gives equality of the half-rays of the plane. -/
theorem ray_eq_of_ray_eq {O A C : σ.Pt}
    (h : ray (Line := σ.Ln) O A = ray (Line := σ.Ln) O C) :
    ray (Line := L) O.1 A.1 = ray (Line := L) O.1 C.1 := by
  by_cases hA : A = O
  · by_cases hC : C = O
    · rw [hA, hC]
    · exfalso
      have hm : C ∈ ray (Line := σ.Ln) O A := h ▸ mem_ray_self (Line := σ.Ln) hC
      exact hm.1 hA
  · have hm : A ∈ ray (Line := σ.Ln) O C := h ▸ mem_ray_self (Line := σ.Ln) hA
    exact ray_eq_of_mem (mem_ray_iff.1 hm)

omit hO in
theorem ray_eq_of_plane {O A C : σ.Pt}
    (h : ray (Line := L) O.1 A.1 = ray (Line := L) O.1 C.1) :
    ray (Line := σ.Ln) O A = ray (Line := σ.Ln) O C := by
  ext X
  rw [mem_ray_iff, mem_ray_iff, h]

/-- The same angle in the part is the same angle in the plane. -/
theorem sameAngle_of_sameAngle {A O B C D : σ.Pt}
    (h : SameAngle (Line := σ.Ln) A O B C D) : SameAngle (Line := L) A.1 O.1 B.1 C.1 D.1 := by
  unfold SameAngle at h ⊢
  rcases Set.pair_eq_pair_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ray_eq_of_ray_eq h1, ray_eq_of_ray_eq h2]
  · rw [ray_eq_of_ray_eq h1, ray_eq_of_ray_eq h2]
    exact Set.pair_comm _ _

end Order

/-- Segments laid off from points of the part, with segments of the part, stay in the part. -/
def LayOffClosed [HasSegCong P] (σ : ConvexPart P L) : Prop :=
  ∀ A B A' C' B' : P, A ∈ σ.S → B ∈ σ.S → A' ∈ σ.S → C' ∈ σ.S → A ≠ B → A' ≠ C' →
    SameSidePt (Line := L) A' C' B' → SegCong A B A' B' → B' ∈ σ.S

section Congruence

variable [HasSegCong P] [HasAngCong P] [hC : PlaneCongruence P L]
include hC

/-- **Groups I, II, IV hold in a convex part of a plane** in which segments can be laid off. -/
theorem planeCongruence (hσ : σ.LayOffClosed) : PlaneCongruence σ.Pt σ.Ln :=
  { (inferInstance : PlaneOrder σ.Pt σ.Ln) with
    angCong_wd := fun A O B C D A' O' B' C' D' h h' hs hs' hc =>
      AngleCongruence.angCong_wd (Point := P) (Line := L) A.1 O.1 B.1 C.1 D.1 A'.1 O'.1 B'.1 C'.1 D'.1
        (fun hc => h (collinear_iff.2 hc)) (fun hc => h' (collinear_iff.2 hc))
        (sameAngle_of_sameAngle hs) (sameAngle_of_sameAngle hs') hc
    ax_IV4_refl := fun A O B h =>
      AngleCongruence.ax_IV4_refl (Point := P) (Line := L) A.1 O.1 B.1 (fun hc => h (collinear_iff.2 hc))
    ax_IV5 := fun A O B A' O' B' A'' O'' B'' h h' h'' h1 h2 =>
      AngleCongruence.ax_IV5 (Point := P) (Line := L) A.1 O.1 B.1 A'.1 O'.1 B'.1 A''.1 O''.1 B''.1
        (fun hc => h (collinear_iff.2 hc)) (fun hc => h' (collinear_iff.2 hc))
        (fun hc => h'' (collinear_iff.2 hc)) h1 h2
    ax_IV4 := fun A O B a' O' A' D' h hO' hA' hA'O' hD' => by
      have hn : ¬Collinear (Line := L) A.1 O.1 B.1 := fun hc => h (collinear_iff.2 hc)
      have hl := line_through_of_ne (L := L) (ne_iff.1 hA'O')
      set F := planeFrame (P := P) (L := L) hl
      obtain ⟨B₀, -, hB₀D, hB₀⟩ := F.layoff Set.univ rfl A.1 O.1 B.1 a'.1 O'.1 A'.1 D'.1 hn
        (fun _ _ => trivial) hO' hA' (ne_iff.1 hA'O') trivial hD'
      have hB₀O : B₀ ≠ O'.1 := fun e => hB₀D.1 (e ▸ hO')
      obtain ⟨B₁, hB₁S, hB₁⟩ := σ.ray_meets O'.1 B₀ O'.2 hB₀O
      have hss : SameSide a'.1 B₀ B₁ := sameSide_of_ray hO' hB₀D.1 hB₁
      have hB₁D : SameSide a'.1 B₁ D'.1 := OrderCore.sameSide_trans (sameSide_symm' hss) hB₀D
      have hn₀ : ¬Collinear (Line := L) A'.1 O'.1 B₀ := fun hc =>
        hB₀D.1 (mem_of_collinear hc (ne_iff.1 hA'O') hA' hO')
      have hAng : AngCong A.1 O.1 B.1 A'.1 O'.1 B₁ :=
        angCong_of_sameAngle (Line := L) hn hn₀ (sameAngle_refl _ _ _)
          (sameAngle_of_ray_eq rfl (ray_eq_of_mem hB₁).symm) hB₀
      have key : ∀ Q : σ.Pt, Q ∉ a' →
          ((∀ X : σ.Pt, X ∈ Interior (Line := σ.Ln) A' O' Q → SameSide a' X D') ↔
            SameSide a' Q D') := fun Q hQ => by
        have := interior_cond_iff (L := σ.Ln) (S := Set.univ) (l := a') (O' := O') (A' := A')
          (B' := Q) (D' := D') (fun _ _ _ _ _ _ h1 h2 => OrderCore.sameSide_trans h1 h2)
          (fun _ _ => trivial) hO' hA' hA'O' hQ trivial trivial
        exact ⟨fun h => this.1 (fun X _ hX => h X hX), fun h X hX => this.2 h X trivial hX⟩
      refine ⟨⟨B₁, hB₁S⟩, hB₁D.1, hAng, (key _ hB₁D.1).2 (sameSide_iff.2 hB₁D), ?_⟩
      intro B'' hB'' hc'' hint
      have h1 : SameSide a'.1 B''.1 D'.1 := sameSide_iff.1 ((key _ hB'').1 hint)
      have h2 : SameSide a'.1 B''.1 B₁ := OrderCore.sameSide_trans h1 (sameSide_symm' hB₁D)
      exact ray_eq_of_plane (F.layoff_unique Set.univ rfl A.1 O.1 B.1 a'.1 O'.1 A'.1 B''.1 B₁ hn
        (fun _ _ => trivial) hO' hA' (ne_iff.1 hA'O') trivial trivial h2 hc'' hAng)
    segCong_swap := fun A B A' B' h =>
      SegmentCongruence.segCong_swap (Point := P) (Line := L) A.1 B.1 A'.1 B'.1 h
    ax_IV1 := fun A B A' C' hAB hA'C' => by
      obtain ⟨B', ⟨hs, hc⟩, huniq⟩ :=
        exists_unique_segCong (Point := P) (Line := L) (ne_iff.1 hAB) (ne_iff.1 hA'C')
      refine ⟨⟨B', hσ A.1 B.1 A'.1 C'.1 B' A.2 B.2 A'.2 C'.2 (ne_iff.1 hAB) (ne_iff.1 hA'C') hs hc⟩,
        ⟨sameSidePt_iff.2 hs, hc⟩, ?_⟩
      rintro Y ⟨hs', hc'⟩
      exact Subtype.ext (huniq Y.1 ⟨sameSidePt_iff.1 hs', hc'⟩)
    ax_IV1_refl := fun A B h => segCong_refl (Point := P) (Line := L) (ne_iff.1 h)
    ax_IV2 := fun A B A' B' A'' B'' h h' h'' h1 h2 =>
      SegmentCongruence.ax_IV2 (Point := P) (Line := L) A.1 B.1 A'.1 B'.1 A''.1 B''.1 (ne_iff.1 h) (ne_iff.1 h')
        (ne_iff.1 h'') h1 h2
    ax_IV3 := fun A B C A' B' C' h h' h1 h2 =>
      SegmentCongruence.ax_IV3 (Point := P) (Line := L) A.1 B.1 C.1 A'.1 B'.1 C'.1
        ((IV3_reading (P := P) (L := L)).2 ((IV3_reading (P := σ.Pt) (L := σ.Ln)).1 h))
        ((IV3_reading (P := P) (L := L)).2 ((IV3_reading (P := σ.Pt) (L := σ.Ln)).1 h')) h1 h2
    ax_IV6 := fun A B C A' B' C' h h' h1 h2 h3 =>
      TriangleCongruence.ax_IV6 (Point := P) (Line := L) A.1 B.1 C.1 A'.1 B'.1 C'.1
        (fun hc => h (collinear_iff.2 hc)) (fun hc => h' (collinear_iff.2 hc)) h1 h2 h3 }

/-- A triangle of the part whose angle sum is two right angles in the plane has angle sum two
right angles in the part (the auxiliary points are moved into the part along their half-rays). -/
theorem angleSumEqTwoRight_of_plane {A B C : σ.Pt} (h : AngleSumEqTwoRight L A.1 B.1 C.1) :
    AngleSumEqTwoRight σ.Ln A B C := by
  obtain ⟨hT, X, Y, ⟨hX, hXY, hYB⟩, hYi, hYc⟩ := h
  have hAC : A.1 ≠ C.1 := ne12_of_between (Line := L) hX
  have hl := line_through_of_ne (L := L) hAC
  set F := planeFrame (P := P) (L := L) hl
  set a := line (Line := L) A.1 C.1 hAC
  have hAa : A.1 ∈ a := mem_line_left hAC
  have hCa : C.1 ∈ a := mem_line_right hAC
  have hXa : X ∈ a := mem_right_of_between hX hAa hCa
  have hYa := hYB a hAa hCa
  have hXC : X ≠ C.1 := (ne23_of_between (Line := L) hX).symm
  have hYC : Y ≠ C.1 := fun e => hYa.1 (e ▸ hCa)
  obtain ⟨X', hX'S, hX'⟩ := σ.ray_meets C.1 X C.2 hXC
  obtain ⟨Y', hY'S, hY'⟩ := σ.ray_meets C.1 Y C.2 hYC
  have hCAB : ¬Collinear (Line := L) C.1 A.1 B.1 := fun hc => hT hc.swap12.swap23
  have hXCY : ¬Collinear (Line := L) X C.1 Y := fun hc =>
    hYa.1 (mem_of_collinear hc hXC hXa hCa)
  have hbX' : Between A.1 C.1 X' := between_of_mem_rays hX (mem_ray_self' hAC) hX'
  have hang1 : AngCong C.1 A.1 B.1 X' C.1 Y' :=
    angCong_of_sameAngle (Line := L) hCAB hXCY (sameAngle_refl _ _ _)
      (sameAngle_of_ray_eq (ray_eq_of_mem hX').symm (ray_eq_of_mem hY').symm) hXY
  have hside : ∀ l : L, A.1 ∈ l → C.1 ∈ l → SameSide l Y' B.1 := fun l hAl hCl =>
    OrderCore.sameSide_trans (sameSide_symm' (sameSide_of_ray hCl (hYB l hAl hCl).1 hY'))
      (hYB l hAl hCl)
  have hXCB : ¬Collinear (Line := L) X C.1 B.1 := fun hc =>
    hYa.2.1 (mem_of_collinear hc hXC hXa hCa)
  have hBC : B.1 ≠ C.1 := (ne_of_not_collinear hXCB (hl _)).2.1
  have hYi' : Y' ∈ Interior (Line := L) X' C.1 B.1 := by
    have h1 := F.mem_interior_of_ray rfl trivial trivial trivial trivial hXCB hYi hY'
    exact F.mem_interior_of_rays rfl trivial trivial trivial trivial hXCB h1 hX'
      (mem_ray_self' hBC)
  have hYCB : ¬Collinear (Line := L) Y C.1 B.1 := by
    intro hc
    have := ((interior_iff (L := L) hXC hBC).1 hYi).2
    exact this.1 (mem_of_collinear hc.swap13 hBC (mem_line_right _) (mem_line_left _))
  have hang2 : AngCong Y' C.1 B.1 C.1 B.1 A.1 :=
    angCong_of_sameAngle (Line := L) hYCB (fun hc => hT hc.swap13)
      (sameAngle_of_ray_eq (ray_eq_of_mem hY').symm rfl) (sameAngle_refl _ _ _) hYc
  exact ⟨fun hc => hT (collinear_iff.1 hc), ⟨X', hX'S⟩, ⟨Y', hY'S⟩,
    ⟨hbX', hang1, fun l hAl hCl => sameSide_iff.2 (hside l.1 hAl hCl)⟩,
    mem_interior_iff.2 hYi', hang2⟩

omit hC [HasSegCong P] in
/-- A right angle of the part is a right angle of the plane. -/
theorem isRightAngle_plane {A O B : σ.Pt} (h : IsRightAngle (L := σ.Ln) A O B) :
    IsRightAngle (L := L) A.1 O.1 B.1 := by
  obtain ⟨hn, C, hC, hc⟩ := h
  exact ⟨fun hcol => hn (collinear_iff.2 hcol), C.1, hC, hc⟩

end Congruence

end ConvexPart

end HilbertFoundations
