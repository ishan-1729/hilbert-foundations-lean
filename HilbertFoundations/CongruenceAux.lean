import HilbertFoundations.Order

/-!
# Helper module for `Congruence.lean`: rays, sides, interiors, and plane frames

This module contains no unit of Hilbert's text; its results are used by the units of
`Congruence.lean`.

* Elementary lemmas on lines, half-rays and angles from the linear axioms (`LineOrder`).
* Sides of a line computed by the linear axioms only (`sameSide_of_between_mem'`,
  `sameSide_of_ray`, `opp_of_between_mem`) and the points of a segment as interior points of an
  angle (`mem_interior_of_between`).
* **Plane frames.** Hilbert's theorems of § 7 speak of figures lying in planes (two triangles, two
  angles, … each in its own plane). To prove them once for plane geometry and for space geometry, a
  `Frame P L` records a family of "planes" (sets of points) together with the plane facts that the
  proofs use *inside one plane*: a plane through three non-collinear points, lines through two
  points of a plane lie in it, Pasch's axiom, the transitivity of "same side", and the laying off
  of angles (IV 4) in the form "on the side of a given point". These are not new axioms: `planeFrame`
  derives them from `PlaneAngleCongruence` (the plane being the set of all points) and `spaceFrame`
  from `SpaceAngleCongruence` (the planes of space).
* Consequences inside a plane of a frame: the crossbar theorem, the position of a ray with respect
  to an angle, the invariance of the interior.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

section Linear

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L]
  {A B C D O X Y Z A' B' : P}
include hO

theorem mem_mid_of_between {a : L} (h : Between A B C) (hA : A ∈ a) (hC : C ∈ a) : B ∈ a :=
  mem_of_collinear (collinear_of_between h).swap23 (ne13_of_between h) hA hC

theorem mem_right_of_between {a : L} (h : Between A B C) (hA : A ∈ a) (hB : B ∈ a) : C ∈ a :=
  mem_of_collinear (collinear_of_between h) (ne12_of_between h) hA hB

theorem mem_left_of_between {a : L} (h : Between A B C) (hB : B ∈ a) (hC : C ∈ a) : A ∈ a :=
  mem_of_collinear (collinear_of_between h).perm231 (ne23_of_between h) hB hC

omit hO in
/-- A point off a line differs from every point of the line. -/
theorem ne_of_mem_not_mem {l : L} (hX : X ∈ l) (hY : Y ∉ l) : Y ≠ X := fun e => hY (e ▸ hX)

omit hO in
theorem collinear_iff_mem_line [Connection P L] {A B X : P} (h : A ≠ B) :
    Collinear A B X ↔ X ∈ line (Line := L) A B h :=
  ⟨fun hc => mem_of_collinear hc h (mem_line_left h) (mem_line_right h),
    fun hX => ⟨_, mem_line_left h, mem_line_right h, hX⟩⟩

/-- A point on the half-ray `OA` spans the same half-ray. -/
theorem ray_eq_of_mem (hX : X ∈ ray O A) : ray O X = ray O A := by
  ext Y
  simp only [mem_ray]
  exact ⟨fun h => sameSidePt_trans hX h, fun h => sameSidePt_trans (sameSidePt_symm hX) h⟩

theorem mem_ray_comm (hX : X ∈ ray O A) : A ∈ ray O X := sameSidePt_symm hX

theorem ne_of_mem_ray (hX : X ∈ ray O A) : X ≠ O := hX.2.1

theorem ne_of_mem_ray' (hX : X ∈ ray O A) : A ≠ O := hX.1

theorem collinear_of_mem_ray (hX : X ∈ ray O A) : Collinear O A X :=
  hX.2.2.1.swap12

/-- Points of the segment `OA` lie on the half-ray `OA`. -/
theorem mem_ray_of_between (h : Between O X A) : X ∈ ray O A :=
  ⟨(ne13_of_between h).symm, (ne12_of_between h).symm, (collinear_of_between h).perm312,
    fun h' => not_between_swap12 h (between_symm h')⟩

/-- Points beyond `A` lie on the half-ray `OA`. -/
theorem mem_ray_of_between' (h : Between O A X) : X ∈ ray O A :=
  sameSidePt_symm (mem_ray_of_between h)

theorem mem_ray_self' (h : A ≠ O) : A ∈ ray O A := mem_ray_self (Line := L) h

/-- A point of the line `OA` other than `O` lies on the half-ray `OA` or on the opposite half-ray. -/
theorem mem_ray_or_between (h : Collinear O A X) (hA : A ≠ O) (hX : X ≠ O) :
    X ∈ ray O A ∨ Between A O X := by
  by_cases hb : Between A O X
  · exact Or.inr hb
  · exact Or.inl ⟨hA, hX, h.swap12, hb⟩

theorem not_mem_ray_of_between (h : Between A O X) : X ∉ ray O A := fun h' => h'.2.2.2 h

/-- The two points of a half-ray: one lies between the vertex and the other. -/
theorem mem_ray_cases (hX : X ∈ ray O A) (hY : Y ∈ ray O A) :
    X = Y ∨ Between O X Y ∨ Between O Y X := by
  have hXY : SameSidePt O X Y := sameSidePt_trans (sameSidePt_symm hX) hY
  by_cases e : X = Y
  · exact Or.inl e
  obtain ⟨hXO, hYO, hc, hn⟩ := hXY
  rcases between_trichotomy (Line := L) hc.swap12 hXO.symm hYO.symm e with h | h | h
  · exact absurd (between_symm h) (fun h' => hn (between_symm (between_symm h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Opposite half-rays: if `O` lies between `A` and `B`, points of the half-ray `OA` and of the
half-ray `OB` are separated by `O`. -/
theorem between_of_mem_rays (h : Between A O B) (hX : X ∈ ray O A) (hY : Y ∈ ray O B) :
    Between X O Y := by
  obtain ⟨g, hAg, hOg, hBg⟩ := collinear_of_between h
  have hAO := ne12_of_between h
  have hBO := (ne23_of_between h).symm
  have hXg : X ∈ g := mem_of_collinear (collinear_of_mem_ray hX) hAO.symm hOg hAg
  have hYg : Y ∈ g := mem_of_collinear (collinear_of_mem_ray hY) hBO.symm hOg hBg
  have hXO := ne_of_mem_ray hX
  have hYO := ne_of_mem_ray hY
  rcases (sameSidePt_or_between hOg hXg hYg hXO hYO).1 with h1 | h1
  · exfalso
    have h2 : SameSidePt O A B := sameSidePt_trans hX (sameSidePt_trans h1 (sameSidePt_symm hY))
    exact h2.2.2.2 h
  · exact h1

/-- A point opposite to a point of the half-ray `OA` is opposite to `A`. -/
theorem between_of_between_mem_ray (h : Between X O Y) (hX : X ∈ ray O A) : Between A O Y := by
  have hY : Y ∈ ray O Y := mem_ray_self' (ne23_of_between h).symm
  exact between_of_mem_rays h (mem_ray_comm hX) hY

/-! ### Angles and their representatives -/

theorem sameAngle_of_ray_eq {C D : P} (h1 : ray O A = ray O C) (h2 : ray O B = ray O D) :
    SameAngle A O B C D := by
  unfold SameAngle; rw [h1, h2]

/-- Replacing the points on the sides of an angle by other points of the same half-rays keeps the
angle non-degenerate. -/
theorem not_collinear_of_mem_rays (h : ¬Collinear A O B) (hX : X ∈ ray O A) (hY : Y ∈ ray O B) :
    ¬Collinear X O Y := by
  intro hc
  have hAO := ne_of_mem_ray' hX
  have hBO := ne_of_mem_ray' hY
  have hXO := ne_of_mem_ray hX
  have hYO := ne_of_mem_ray hY
  obtain ⟨g, hXg, hOg, hYg⟩ := hc
  have hAg : A ∈ g := mem_of_collinear (collinear_of_mem_ray (mem_ray_comm hX)) hXO.symm hOg hXg
  have hBg : B ∈ g := mem_of_collinear (collinear_of_mem_ray (mem_ray_comm hY)) hYO.symm hOg hYg
  exact h ⟨g, hAg, hOg, hBg⟩

/-- A point opposite to a side keeps the angle non-degenerate. -/
theorem not_collinear_of_between (h : ¬Collinear A O B) (hb : Between A O C) :
    ¬Collinear C O B := by
  rintro ⟨g, hCg, hOg, hBg⟩
  exact h ⟨g, mem_left_of_between hb hOg hCg, hOg, hBg⟩

omit hO in
theorem not_collinear_swap {A O B : P} (h : ¬Collinear A O B) : ¬Collinear B O A :=
  fun hc => h hc.swap13

/-- The three points of a genuine angle are distinct, provided some line passes through the
vertex (true in plane and in space geometry). -/
theorem ne_of_not_collinear (h : ¬Collinear A O B) (hl : ∃ l : L, O ∈ l) :
    A ≠ O ∧ B ≠ O ∧ A ≠ B := by
  have hBO : B ≠ O := by
    rintro rfl
    by_cases hAB : A = B
    · subst hAB; obtain ⟨l, hl⟩ := hl; exact h ⟨l, hl, hl, hl⟩
    · exact h (collinear_of_ne (Line := L) (Ne.symm hAB)).swap12
  refine ⟨?_, hBO, ?_⟩
  · rintro rfl; exact h (collinear_of_ne (Line := L) hBO.symm).swap23
  · rintro rfl; exact h (collinear_of_ne (Line := L) hBO)

end Linear

/-! ### Sides of a line computed with the linear axioms -/

section Sides

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L]
  {A B C D O X Y Z A' B' : P} {l : L}
include hO

theorem sameSide_symm' (h : SameSide l A B) : SameSide l B A :=
  ⟨h.2.1, h.1, fun ⟨X, hX, hB⟩ => h.2.2 ⟨X, hX, between_symm hB⟩⟩

theorem opp_symm' (h : OppositeSides l A B) : OppositeSides l B A := by
  obtain ⟨hA, hB, X, hX, hAXB⟩ := h
  exact ⟨hB, hA, X, hX, between_symm hAXB⟩

theorem sameSide_refl' (h : A ∉ l) : SameSide l A A :=
  ⟨h, h, fun ⟨_, _, hX⟩ => ne13_of_between hX rfl⟩

omit hO in
theorem sameSide_or_opp' (hA : A ∉ l) (hB : B ∉ l) : SameSide l A B ∨ OppositeSides l A B := by
  by_cases h : ∃ X, X ∈ l ∧ Between A X B
  · exact Or.inr ⟨hA, hB, h⟩
  · exact Or.inl ⟨hA, hB, h⟩

omit hO in
theorem not_sameSide_of_opp' (h : OppositeSides l A B) : ¬SameSide l A B :=
  fun h' => h'.2.2 h.2.2

/-- The points between a point of a line and a point off it are on the side of the latter (linear
axioms only). -/
theorem sameSide_of_between_mem' (hX : X ∈ l) (hY : Y ∉ l) (h : Between X Z Y) :
    SameSide l Z Y := by
  have hXY : X ≠ Y := ne13_of_between h
  obtain ⟨g, hXg, hYg⟩ := exists_line (Line := L) hXY
  have hZg : Z ∈ g := mem_mid_of_between h hXg hYg
  have hgl : g ≠ l := fun e => hY (e ▸ hYg)
  have key : ∀ W, W ∈ g → W ∈ l → W = X := fun W hWg hWl =>
    eq_of_mem_of_mem hgl hWg hWl hXg hX
  refine ⟨fun hZ => ne12_of_between h (key Z hZg hZ).symm, hY, ?_⟩
  rintro ⟨W, hWl, hZWY⟩
  have hWg : W ∈ g := mem_mid_of_between hZWY hZg hYg
  rw [key W hWg hWl] at hZWY
  exact not_between_swap12 h hZWY

/-- A point of the line between two points puts them on opposite sides. -/
theorem opp_of_between_mem (hZ : Z ∈ l) (hX : X ∉ l) (h : Between X Z Y) :
    OppositeSides l X Y :=
  ⟨hX, fun hY => hX (mem_left_of_between h hZ hY), Z, hZ, h⟩

/-- The points of a half-ray from a point of `l` lie on the side of `l` of the half-ray. -/
theorem sameSide_of_ray (hOl : O ∈ l) (hA : A ∉ l) (hX : X ∈ ray O A) : SameSide l A X := by
  have hAO := ne_of_mem_ray' hX
  have hXO := ne_of_mem_ray hX
  obtain ⟨g, hOg, hAg⟩ := exists_line (Line := L) hAO.symm
  have hXg : X ∈ g := mem_of_collinear (collinear_of_mem_ray hX) hAO.symm hOg hAg
  have hgl : g ≠ l := fun e => hA (e ▸ hAg)
  have key : ∀ W, W ∈ g → W ∈ l → W = O := fun W hWg hWl =>
    eq_of_mem_of_mem hgl hWg hWl hOg hOl
  refine ⟨hA, fun hXl => hXO (key X hXg hXl), ?_⟩
  rintro ⟨W, hWl, hAWX⟩
  have hWg : W ∈ g := mem_mid_of_between hAWX hAg hXg
  rw [key W hWg hWl] at hAWX
  exact hX.2.2.2 hAWX

/-- A point of the line `OA` (`O ∈ l`, `A ∉ l`) on the side of `A` lies on the half-ray `OA`. -/
theorem mem_ray_of_sameSide (hOl : O ∈ l) (hc : Collinear O A X) (hXO : X ≠ O)
    (h : SameSide l A X) : X ∈ ray O A := by
  have hAO : A ≠ O := fun e => h.1 (e ▸ hOl)
  rcases mem_ray_or_between (L := L) hc hAO hXO with h1 | h1
  · exact h1
  · exact absurd h (not_sameSide_of_opp' (opp_of_between_mem hOl h.1 h1))

/-! ### The interior of an angle -/

theorem interior_iff (hA : A ≠ O) (hB : B ≠ O) :
    X ∈ Interior A O B ↔ SameSide (line (Line := L) O A hA.symm) X B ∧
      SameSide (line (Line := L) O B hB.symm) X A := by
  constructor
  · intro h
    exact h _ _ (mem_line_left _) (mem_line_right _) (mem_line_left _) (mem_line_right _)
  · rintro ⟨h1, h2⟩ a b hOa hAa hOb hBb
    rw [eq_line hA.symm hOa hAa, eq_line hB.symm hOb hBb]
    exact ⟨h1, h2⟩

omit hO in
theorem interior_swap : Interior A O B = Interior (Line := L) B O A := by
  ext X
  simp only [Interior, Set.mem_ofPred_eq]
  exact ⟨fun h a b ha hA hb hB => (h b a hb hB ha hA).symm,
    fun h a b ha hA hb hB => (h b a hb hB ha hA).symm⟩

/-- The points within the segment `AB` are interior points of the angle `AOB`. -/
theorem mem_interior_of_between (h : ¬Collinear A O B) (hb : Between A X B) :
    X ∈ Interior (Line := L) A O B := by
  intro a b hOa hAa hOb hBb
  exact ⟨sameSide_of_between_mem' hAa (fun hB => h ⟨a, hAa, hOa, hB⟩) hb,
    sameSide_of_between_mem' hBb (fun hA => h ⟨b, hA, hOb, hBb⟩) (between_symm hb)⟩

end Sides

/-! ## Plane frames -/

/-- The line `l` lies in the set of points `S`. -/
def LineIn {P : Type u} {L : Type v} [HasLines P L] (l : L) (S : Set P) : Prop :=
  ∀ X : P, X ∈ l → X ∈ S

/-- A **plane frame**: a family of "planes" (sets of points, `IsPl`) with the facts of plane
geometry used inside one plane in § 7. Instances: `planeFrame` (plane geometry, the only plane
being the set of all points) and `spaceFrame` (the planes of space). -/
structure Frame (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] [HasAngCong P] where
  /-- The sets of points that are planes. -/
  IsPl : Set P → Prop
  line_through : ∀ X : P, ∃ l : L, X ∈ l
  pl_three : ∀ S, IsPl S → ∃ A B C : P, A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ ¬Collinear A B C
  exists_pl : ∀ A B C : P, ¬Collinear A B C → ∃ S, IsPl S ∧ A ∈ S ∧ B ∈ S ∧ C ∈ S
  line_sub : ∀ S, IsPl S → ∀ (A B : P) (l : L), A ≠ B → A ∈ S → B ∈ S → A ∈ l → B ∈ l →
    LineIn l S
  sameSide_trans : ∀ S, IsPl S → ∀ (l : L) (A B C : P), LineIn l S → A ∈ S → B ∈ S → C ∈ S →
    SameSide l A B → SameSide l B C → SameSide l A C
  sameSide_of_opp_opp : ∀ S, IsPl S → ∀ (l : L) (A B C : P), LineIn l S → A ∈ S → B ∈ S →
    C ∈ S → OppositeSides l A B → OppositeSides l B C → SameSide l A C
  pasch : ∀ S, IsPl S → ∀ (A B C X : P) (l : L), LineIn l S → A ∈ S → B ∈ S → C ∈ S →
    ¬Collinear A B C → A ∉ l → B ∉ l → C ∉ l → X ∈ l → Between A X B →
      (∃ Y, Y ∈ l ∧ Between B Y C) ∨ ∃ Y, Y ∈ l ∧ Between A Y C
  layoff : ∀ S, IsPl S → ∀ (A O B : P) (l : L) (O' A' D' : P), ¬Collinear A O B → LineIn l S →
    O' ∈ l → A' ∈ l → A' ≠ O' → D' ∈ S → D' ∉ l →
      ∃ B', B' ∈ S ∧ SameSide l B' D' ∧ AngCong A O B A' O' B'
  layoff_unique : ∀ S, IsPl S → ∀ (A O B : P) (l : L) (O' A' B' B'' : P), ¬Collinear A O B →
    LineIn l S → O' ∈ l → A' ∈ l → A' ≠ O' → B' ∈ S → B'' ∈ S → SameSide l B' B'' →
      AngCong A O B A' O' B' → AngCong A O B A' O' B'' → ray O' B' = ray O' B''

section FrameInstances

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P]

/-- The condition of IV 4 ("all interior points of the angle `(h', k')` lie upon the given side")
in terms of the side of the point `B'`, given the transitivity of "same side" in the plane `S`. -/
theorem interior_cond_iff [hO : LineOrder P L] {S : Set P} {l : L} {O' A' B' D' : P}
    (htr : ∀ X Y Z : P, X ∈ S → Y ∈ S → Z ∈ S → SameSide l X Y → SameSide l Y Z →
      SameSide l X Z)
    (hseg : ∀ X : P, Between A' X B' → X ∈ S)
    (hO' : O' ∈ l) (hA' : A' ∈ l) (hA'O' : A' ≠ O') (hB' : B' ∉ l) (hB'S : B' ∈ S)
    (hD'S : D' ∈ S) :
    (∀ X : P, X ∈ S → X ∈ Interior A' O' B' → SameSide l X D') ↔ SameSide l B' D' := by
  have hn : ¬Collinear A' O' B' := fun hc =>
    hB' (mem_of_collinear hc.swap12 hA'O'.symm hO' hA')
  constructor
  · intro h
    have hA'B' : A' ≠ B' := fun e => hB' (e ▸ hA')
    obtain ⟨X, hX⟩ := exists_between (Line := L) hA'B'
    have h1 := h X (hseg X hX) (mem_interior_of_between hn hX)
    have h2 := sameSide_of_between_mem' hA' hB' hX
    exact htr _ _ _ hB'S (hseg X hX) hD'S (sameSide_symm' h2) h1
  · intro h X hXS hX
    have hB'O' : B' ≠ O' := fun e => hB' (e ▸ hO')
    obtain ⟨b, hOb, hBb⟩ := exists_line (Line := L) hB'O'.symm
    have h1 := (hX l b hO' hA' hOb hBb).1
    exact htr _ _ _ hXS hB'S hD'S h1 h

/-- In plane geometry (group I) every point lies on a line, unless there is only one point. -/
theorem line_through_or_subsingleton [PlaneConnection P L] :
    (∀ X : P, ∃ l : L, X ∈ l) ∨ Subsingleton P := by
  by_cases h : ∃ X Y : P, X ≠ Y
  · left
    obtain ⟨X, Y, hXY⟩ := h
    intro Z
    by_cases hZX : Z = X
    · subst hZX
      obtain ⟨l, hl, -⟩ := exists_line (Line := L) hXY
      exact ⟨l, hl⟩
    · obtain ⟨l, hl, -⟩ := exists_line (Line := L) hZX
      exact ⟨l, hl⟩
  · right
    push Not at h
    exact ⟨h⟩

/-- **The plane frame of a plane geometry** (groups I, II and IV 4–5 of plane geometry): one plane,
the set of all points. It needs a line through every point, which fails only in the geometry with a
single point (`line_through_or_subsingleton`). -/
def planeFrame [PlaneAngleCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l) : Frame P L where
  IsPl S := S = Set.univ
  line_through := hl
  pl_three S hS := by
    subst hS
    obtain ⟨A, B, C, h⟩ := exists_noncollinear (Point := P) (Line := L)
    exact ⟨A, B, C, trivial, trivial, trivial, h⟩
  exists_pl _ _ _ _ := ⟨Set.univ, rfl, trivial, trivial, trivial⟩
  line_sub S hS _ _ _ _ _ _ _ _ := by subst hS; exact fun _ _ => trivial
  sameSide_trans _ _ _ _ _ _ _ _ _ _ h1 h2 := OrderCore.sameSide_trans h1 h2
  sameSide_of_opp_opp _ _ _ _ _ _ _ _ _ _ h1 h2 := OrderCore.sameSide_of_opp_opp h1 h2
  pasch _ _ A B C X l _ _ _ _ h hA hB hC hX hb := pasch h hA hB hC hX hb
  layoff S hS A O B l O' A' D' h _ hO' hA' hA'O' _ hD' := by
    subst hS
    obtain ⟨B', hB', hc, hint, -⟩ := PlaneAngleCongruence.ax_IV4 A O B l O' A' D' h hO' hA'
      hA'O' hD'
    refine ⟨B', trivial, ?_, hc⟩
    exact (interior_cond_iff (S := Set.univ)
      (fun _ _ _ _ _ _ h1 h2 => OrderCore.sameSide_trans h1 h2) (fun _ _ => trivial) hO' hA'
      hA'O' hB' trivial trivial).1 (fun X _ hX => hint X hX)
  layoff_unique S hS A O B l O' A' B' B'' h _ hO' hA' hA'O' _ _ hs h1 h2 := by
    subst hS
    obtain ⟨E, -, -, -, huniq⟩ := PlaneAngleCongruence.ax_IV4 A O B l O' A' B' h hO' hA'
      hA'O' hs.1
    have cond : ∀ Q : P, SameSide l Q B' → ∀ X : P, X ∈ Interior A' O' Q → SameSide l X B' :=
      fun Q hQ X hX => (interior_cond_iff (S := Set.univ)
        (fun _ _ _ _ _ _ h1 h2 => OrderCore.sameSide_trans h1 h2) (fun _ _ => trivial) hO' hA'
        hA'O' hQ.1 trivial trivial).2 hQ X trivial hX
    have e1 := huniq B' hs.1 h1 (cond B' (sameSide_refl' hs.1))
    have e2 := huniq B'' hs.2.1 h2 (cond B'' (sameSide_symm' hs))
    rw [e1, e2]

/-- In space geometry (group I) every point lies on a line. -/
theorem line_through_space {Pl : Type w} [HasPlanes P Pl] [SpaceConnection P L Pl] (X : P) :
    ∃ l : L, X ∈ l := by
  obtain ⟨A, B, C, D, hn⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
  have key : ∀ Y : P, Y ≠ X → ∃ l : L, X ∈ l := fun Y hY => by
    obtain ⟨l, hl, -⟩ := exists_line (Line := L) hY.symm
    exact ⟨l, hl⟩
  by_cases hA : A = X
  · by_cases hB : B = X
    · by_cases hC : C = X
      · by_cases hD : D = X
        · rw [hA, hB, hC, hD] at hn
          by_contra hno
          push Not at hno
          obtain ⟨α, hα, -, -⟩ := exists_plane (Plane := Pl) (A := X) (B := X) (C := X)
            (fun ⟨l, hl, _, _⟩ => hno l hl)
          exact hn ⟨α, hα, hα, hα, hα⟩
        · exact key D hD
      · exact key C hC
    · exact key B hB
  · exact key A hA

/-- **The plane frame of a space geometry** (groups I, II and IV 4–5 of space geometry): the planes
of space. -/
def spaceFrame {Pl : Type w} [HasPlanes P Pl] [SpaceAngleCongruence P L Pl] : Frame P L where
  IsPl S := ∃ α : Pl, S = {X | X ∈ α}
  line_through := line_through_space (Pl := Pl)
  pl_three S hS := by
    obtain ⟨α, rfl⟩ := hS
    exact SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  exists_pl A B C h := by
    obtain ⟨α, hA, hB, hC⟩ := exists_plane (Plane := Pl) h
    exact ⟨{X | X ∈ α}, ⟨α, rfl⟩, hA, hB, hC⟩
  line_sub S hS A B l hAB hA hB hAl hBl := by
    obtain ⟨α, rfl⟩ := hS
    exact liesInPlane_of_mem hAB hAl hBl hA hB
  sameSide_trans S hS l A B C hl hA hB hC h1 h2 := by
    obtain ⟨α, rfl⟩ := hS
    exact OrderSpace.sameSide_trans (Pl := Pl) (β := α) hl hA hB hC h1 h2
  sameSide_of_opp_opp S hS l A B C hl hA hB hC h1 h2 := by
    obtain ⟨α, rfl⟩ := hS
    exact OrderSpace.sameSide_of_opp_opp (Pl := Pl) (β := α) hl hA hB hC h1 h2
  pasch S hS A B C X l hl hA hB hC h hAl hBl hCl hX hb := by
    obtain ⟨α, rfl⟩ := hS
    exact SpaceOrder.ax_II5 (Line := L) A B C α l h hA hB hC hl hAl hBl hCl ⟨X, hX, hb⟩
  layoff S hS A O B l O' A' D' h hl hO' hA' hA'O' hD'S hD' := by
    obtain ⟨α, rfl⟩ := hS
    obtain ⟨B', hB'α, hB', hc, hint, -⟩ := SpaceAngleCongruence.ax_IV4 (Line := L) A O B α l O' A'
      D' h hl hO' hA' hA'O' hD'S hD'
    refine ⟨B', hB'α, ?_, hc⟩
    have hA'B' : A' ≠ B' := fun e => hB' (e ▸ hA')
    have hm := liesInPlane_of_mem hA'B' (mem_line_left (Line := L) hA'B') (mem_line_right hA'B')
      (hl A' hA') hB'α
    exact (interior_cond_iff (S := {X | X ∈ α})
      (fun _ _ _ h1 h2 h3 s1 s2 => OrderSpace.sameSide_trans (Pl := Pl) (β := α) hl h1 h2 h3 s1 s2)
      (fun X hX => hm X (mem_mid_of_between hX (mem_line_left hA'B') (mem_line_right hA'B')))
      hO' hA' hA'O' hB' hB'α hD'S).1 (fun X hXα hX => hint X hXα hX)
  layoff_unique S hS A O B l O' A' B' B'' h hl hO' hA' hA'O' hB'S hB''S hs h1 h2 := by
    obtain ⟨α, rfl⟩ := hS
    obtain ⟨E, -, -, -, -, huniq⟩ := SpaceAngleCongruence.ax_IV4 (Line := L) A O B α l O' A' B' h
      hl hO' hA' hA'O' hB'S hs.1
    have cond : ∀ Q : P, Q ∈ α → SameSide l Q B' → ∀ X : P, X ∈ α → X ∈ Interior A' O' Q →
        SameSide l X B' := by
      intro Q hQα hQ X hXα hX
      have hA'Q : A' ≠ Q := fun e => hQ.1 (e ▸ hA')
      have hm := liesInPlane_of_mem hA'Q (mem_line_left (Line := L) hA'Q) (mem_line_right hA'Q)
        (hl A' hA') hQα
      exact (interior_cond_iff (S := {X | X ∈ α})
        (fun _ _ _ h1 h2 h3 s1 s2 =>
          OrderSpace.sameSide_trans (Pl := Pl) (β := α) hl h1 h2 h3 s1 s2)
        (fun Y hY => hm Y (mem_mid_of_between hY (mem_line_left hA'Q) (mem_line_right hA'Q)))
        hO' hA' hA'O' hQ.1 hQα hB'S).2 hQ X hXα hX
    have e1 := huniq B' hB'S hs.1 h1 (cond B' hB'S (sameSide_refl' hs.1))
    have e2 := huniq B'' hB''S hs.2.1 h2 (cond B'' hB''S (sameSide_symm' hs))
    rw [e1, e2]

end FrameInstances

/-! ## Plane facts inside a plane of a frame -/

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P]
  [hO : LineOrder P L] (F : Frame P L) {S : Set P} {A B C D E O X Y Z A' B' H K L' : P} {l : L}
include hO F

/-- The three points of a genuine angle are distinct. -/
theorem ne (h : ¬Collinear A O B) : A ≠ O ∧ B ≠ O ∧ A ≠ B :=
  ne_of_not_collinear h (F.line_through O)

theorem memS_of_collinear (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B)
    (h : Collinear A B X) : X ∈ S :=
  F.line_sub S hS A B _ hAB hA hB (mem_line_left (Line := L) hAB) (mem_line_right hAB) X
    (mem_of_collinear h hAB (mem_line_left hAB) (mem_line_right hAB))

theorem memS_of_between (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (h : Between A X B) :
    X ∈ S :=
  F.memS_of_collinear hS hA hB (ne13_of_between h) (collinear_of_between h).swap23

theorem memS_of_between' (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (h : Between A B X) :
    X ∈ S :=
  F.memS_of_collinear hS hA hB (ne12_of_between h) (collinear_of_between h)

theorem memS_of_ray (hS : F.IsPl S) (hO : O ∈ S) (hA : A ∈ S) (h : X ∈ ray O A) : X ∈ S :=
  F.memS_of_collinear hS hO hA (ne_of_mem_ray' h).symm (collinear_of_mem_ray h)

theorem lineIn (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    LineIn (line (Line := L) A B hAB) S :=
  F.line_sub S hS A B _ hAB hA hB (mem_line_left hAB) (mem_line_right hAB)

theorem ss_trans (hS : F.IsPl S) (hl : LineIn l S) (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (h1 : SameSide l A B) (h2 : SameSide l B C) : SameSide l A C :=
  F.sameSide_trans S hS l A B C hl hA hB hC h1 h2

theorem opp_of_ss_opp (hS : F.IsPl S) (hl : LineIn l S) (hA : A ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) (h1 : SameSide l A B) (h2 : OppositeSides l B C) : OppositeSides l A C := by
  rcases sameSide_or_opp' h1.1 h2.2.1 with h | h
  · exact absurd (F.ss_trans hS hl hB hA hC (sameSide_symm' h1) h) (not_sameSide_of_opp' h2)
  · exact h

theorem ss_of_opp_opp (hS : F.IsPl S) (hl : LineIn l S) (hA : A ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) (h1 : OppositeSides l A B) (h2 : OppositeSides l B C) : SameSide l A C :=
  F.sameSide_of_opp_opp S hS l A B C hl hA hB hC h1 h2

/-- **Crossbar theorem**: a half-ray from the vertex through an interior point of the angle `BAC`
meets the segment `BC`. -/
theorem crossbar (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hD : D ∈ S)
    (h : ¬Collinear B A C) (hDi : D ∈ Interior B A C) : ∃ Y, Between B Y C ∧ Y ∈ ray A D := by
  obtain ⟨hBA, hCA, hBC⟩ := F.ne h
  have hint := (interior_iff (L := L) hBA hCA).1 hDi
  set lAB := line (Line := L) A B hBA.symm
  set lAC := line (Line := L) A C hCA.symm
  have hAAB : A ∈ lAB := mem_line_left _
  have hBAB : B ∈ lAB := mem_line_right _
  have hAAC : A ∈ lAC := mem_line_left _
  have hCAC : C ∈ lAC := mem_line_right _
  have hDAB : D ∉ lAB := hint.1.1
  have hCAB : C ∉ lAB := hint.1.2.1
  have hDAC : D ∉ lAC := hint.2.1
  have hBAC : B ∉ lAC := hint.2.2.1
  have hDA : D ≠ A := fun e => hDAB (e ▸ hAAB)
  set lAD := line (Line := L) A D hDA.symm
  have hAAD : A ∈ lAD := mem_line_left _
  have hDAD : D ∈ lAD := mem_line_right _
  obtain ⟨E, hE⟩ := exists_beyond (Line := L) hCA
  have hEAC : E ∈ lAC := mem_right_of_between hE hCAC hAAC
  have hEA : E ≠ A := (ne23_of_between hE).symm
  have hES : E ∈ S := F.memS_of_between' hS hC hA hE
  have hlS : LineIn lAD S := F.lineIn hS hA hD hDA.symm
  have hlACS : LineIn lAC S := F.lineIn hS hA hC hCA.symm
  have hlABS : LineIn lAB S := F.lineIn hS hA hB hBA.symm
  have notAD : ∀ Q, Q ∈ lAC → Q ≠ A → Q ∉ lAD := fun Q hQ hQA hQD =>
    hDAC (by rw [line_unique hQA.symm hAAC hQ hAAD hQD]; exact hDAD)
  have hBAD : B ∉ lAD := fun hB' =>
    hDAB (by rw [line_unique hBA.symm hAAB hBAB hAAD hB']; exact hDAD)
  have hEAB : E ∉ lAB := fun hE' =>
    hCAB ((line_unique hEA.symm hAAC hEAC hAAB hE' : lAC = lAB) ▸ hCAC)
  have hnc : ¬Collinear E C B :=
    not_collinear_of_not_mem hEAC hCAC (ne13_of_between hE).symm hBAC
  have toRay : ∀ Y, Y ∈ lAD → Y ∈ S → SameSide lAC Y B → Y ∈ ray A D := fun Y hY hYS hYB =>
    mem_ray_of_sameSide hAAC (collinear_of_mem hAAD hDAD hY) (fun e => hYB.1 (e ▸ hAAC))
      (F.ss_trans hS hlACS hD hB hYS hint.2 (sameSide_symm' hYB))
  rcases F.pasch S hS E C B A lAD hlS hES hC hB hnc (notAD E hEAC hEA)
      (notAD C hCAC hCA) hBAD hAAD (between_symm hE) with ⟨Y, hY, hCYB⟩ | ⟨Y, hY, hEYB⟩
  · have hYS : Y ∈ S := F.memS_of_between hS hC hB hCYB
    exact ⟨Y, between_symm hCYB, toRay Y hY hYS (sameSide_of_between_mem' hCAC hBAC hCYB)⟩
  · exfalso
    have hYS : Y ∈ S := F.memS_of_between hS hES hB hEYB
    have hYr := toRay Y hY hYS (sameSide_of_between_mem' hEAC hBAC hEYB)
    have h1 : SameSide lAB D Y := sameSide_of_ray hAAB hDAB hYr
    have h2 : SameSide lAB Y C := F.ss_trans hS hlABS hYS hD hC (sameSide_symm' h1) hint.1
    have h3 : SameSide lAB Y E := sameSide_of_between_mem' hBAB hEAB (between_symm hEYB)
    have h4 : SameSide lAB C E := F.ss_trans hS hlABS hC hYS hES (sameSide_symm' h2) h3
    exact not_sameSide_of_opp' (opp_of_between_mem hAAB hCAB hE) h4

/-- A point of the half-ray `OX` from the vertex through an interior point is interior. -/
theorem mem_interior_of_ray (hS : F.IsPl S) (hO : O ∈ S) (hA : A ∈ S) (hB : B ∈ S)
    (hX : X ∈ S) (h : ¬Collinear A O B) (hXi : X ∈ Interior A O B) (hY : Y ∈ ray O X) :
    Y ∈ Interior A O B := by
  obtain ⟨hAO, hBO, -⟩ := F.ne h
  have hYS : Y ∈ S := F.memS_of_ray hS hO hX hY
  have hi := (interior_iff (L := L) hAO hBO).1 hXi
  refine (interior_iff (L := L) hAO hBO).2 ⟨?_, ?_⟩
  · exact F.ss_trans hS (F.lineIn hS hO hA hAO.symm) hYS hX hB
      (sameSide_symm' (sameSide_of_ray (mem_line_left _) hi.1.1 hY)) hi.1
  · exact F.ss_trans hS (F.lineIn hS hO hB hBO.symm) hYS hX hA
      (sameSide_symm' (sameSide_of_ray (mem_line_left _) hi.2.1 hY)) hi.2

/-- The interior only depends on the half-rays. -/
theorem mem_interior_of_rays (hS : F.IsPl S) (hO : O ∈ S) (hA : A ∈ S) (hB : B ∈ S)
    (hX : X ∈ S) (h : ¬Collinear A O B) (hXi : X ∈ Interior A O B) (hA' : A' ∈ ray O A)
    (hB' : B' ∈ ray O B) : X ∈ Interior A' O B' := by
  obtain ⟨hAO, hBO, -⟩ := F.ne h
  have hA'O := ne_of_mem_ray hA'
  have hB'O := ne_of_mem_ray hB'
  have hA'S : A' ∈ S := F.memS_of_ray hS hO hA hA'
  have hB'S : B' ∈ S := F.memS_of_ray hS hO hB hB'
  have hi := (interior_iff (L := L) hAO hBO).1 hXi
  have e1 : line (Line := L) O A' hA'O.symm = line O A hAO.symm :=
    (eq_line hA'O.symm (mem_line_left (Line := L) hAO.symm)
      (mem_of_collinear (collinear_of_mem_ray hA') hAO.symm (mem_line_left _)
        (mem_line_right _))).symm
  have e2 : line (Line := L) O B' hB'O.symm = line O B hBO.symm :=
    (eq_line hB'O.symm (mem_line_left (Line := L) hBO.symm)
      (mem_of_collinear (collinear_of_mem_ray hB') hBO.symm (mem_line_left _)
        (mem_line_right _))).symm
  refine (interior_iff (L := L) hA'O hB'O).2 ⟨?_, ?_⟩
  · rw [e1]
    exact F.ss_trans hS (F.lineIn hS hO hA hAO.symm) hX hB hB'S hi.1
      (sameSide_of_ray (mem_line_left _) hi.1.2.1 hB')
  · rw [e2]
    exact F.ss_trans hS (F.lineIn hS hO hB hBO.symm) hX hA hA'S hi.2
      (sameSide_of_ray (mem_line_left _) hi.2.2.1 hA')

/-- The interiors of the two adjacent angles `BAD`, `CAD` (with `A` between `B` and `C`) are
disjoint. -/
theorem interior_disjoint (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (hD : D ∈ S) (hX : X ∈ S)
    (h : ¬Collinear B A D) (hb : Between B A C) (h1 : X ∈ Interior B A D)
    (h2 : X ∈ Interior C A D) : False := by
  obtain ⟨hBA, hDA, -⟩ := F.ne h
  have hCA : C ≠ A := (ne23_of_between hb).symm
  have hCS : C ∈ S := F.memS_of_between' hS hB hA hb
  have i1 := (interior_iff (L := L) hBA hDA).1 h1
  have i2 := (interior_iff (L := L) hCA hDA).1 h2
  have hm : LineIn (line (Line := L) A D hDA.symm) S := F.lineIn hS hA hD hDA.symm
  have s := F.ss_trans hS hm hB hX hCS (sameSide_symm' i1.2) i2.2
  exact not_sameSide_of_opp' (opp_of_between_mem (mem_line_left _) s.1 hb) s

/-- **Position of a half-ray**: if `H`, `K` lie on the same side of the line `OL` and on different
half-rays, then `K` is interior to the angle `HOL` or `H` interior to the angle `KOL`. -/
theorem interior_or_interior (hS : F.IsPl S) (hO : O ∈ S) (hH : H ∈ S) (hK : K ∈ S)
    (hL : L' ∈ S) (hHL : ¬Collinear H O L') (hLO : L' ≠ O)
    (hs : SameSide (line (Line := L) O L' hLO.symm) H K) (hHK : ¬Collinear H O K) :
    K ∈ Interior H O L' ∨ H ∈ Interior K O L' := by
  obtain ⟨hHO, -, -⟩ := F.ne hHL
  obtain ⟨-, hKO, -⟩ := F.ne hHK
  set m := line (Line := L) O H hHO.symm
  set n := line (Line := L) O L' hLO.symm
  have hmS := F.lineIn hS hO hH hHO.symm
  have hnS : LineIn n S := F.lineIn hS hO hL hLO.symm
  have hKm : K ∉ m := fun hK' => hHK (collinear_of_mem (mem_line_right _) (mem_line_left _) hK')
  have hLm : L' ∉ m := fun hL' => hHL (collinear_of_mem (mem_line_right _) (mem_line_left _) hL')
  rcases sameSide_or_opp' hKm hLm with h1 | h1
  · left
    exact (interior_iff (L := L) hHO hLO).2 ⟨h1, sameSide_symm' hs⟩
  · right
    set k := line (Line := L) O K hKO.symm
    have hkS := F.lineIn hS hO hK hKO.symm
    have hHk : H ∉ k := fun hH' => hHK (collinear_of_mem hH' (mem_line_left _) (mem_line_right _))
    have hLk : L' ∉ k := fun hL' => hs.2.1
      ((line_unique hLO.symm (mem_line_left _) (mem_line_right _) (mem_line_left _) hL' :
        n = k) ▸ mem_line_right _)
    refine (interior_iff (L := L) hKO hLO).2 ⟨?_, hs⟩
    rcases sameSide_or_opp' hHk hLk with h2 | h2
    · exact h2
    · exfalso
      obtain ⟨-, -, X, hXk, hHXL⟩ := h2
      have hXS : X ∈ S := F.memS_of_between hS hH hL hHXL
      have hXi : X ∈ Interior H O L' := mem_interior_of_between hHL hHXL
      have hXO : X ≠ O := fun e => hHL (e ▸ collinear_of_between hHXL)
      have hi := (interior_iff (L := L) hHO hLO).1 hXi
      have hXK : SameSide n X K := F.ss_trans hS hnS hXS hH hK hi.2 hs
      have hXr : X ∈ ray O K := mem_ray_of_sameSide (mem_line_left _)
        (collinear_of_mem (mem_line_left _) (mem_line_right _) hXk) hXO (sameSide_symm' hXK)
      have hKX : SameSide m K X := sameSide_of_ray (mem_line_left _) hKm hXr
      exact not_sameSide_of_opp' h1 (F.ss_trans hS hmS hK hXS hL hKX hi.1)

end Frame

end HilbertFoundations
