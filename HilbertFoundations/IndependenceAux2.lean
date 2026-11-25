import HilbertFoundations.Order

/-!
# The first assertion of the axiom of parallels from groups I, II, IV (helper of `Independence.lean`)

Unit `s10.first_assertion` of `Independence.lean`: in a plane geometry satisfying groups I, II and
IV, through a point `A` off a line `a` there is a line not meeting `a` (the first assertion of the
parallel axiom III). Hilbert's proof uses the first congruence theorem for triangles (Theorem 10)
and the
theorem on supplementary angles (Theorem 12); since `Congruence.lean` (where these are units
`th.10`, `th.12`) is not imported here, the two theorems are proved again below, from IV 1–6 and
the plane separation properties of `Order.lean` / `OrderAux.lean`:

* `ParallelExists.segCong_of_sas` (third side in Theorem 10), `ParallelExists.supplement`
  (Theorem 12);
* `ParallelExists.no_meet_core`: the core of Hilbert's argument;
* `ParallelExists.axiomIIIExists`: the theorem.
-/

namespace HilbertFoundations

namespace ParallelExists

variable {P : Type*} {L : Type*} [HasLines P L] [HasBetween P]

/-! ### Rays -/

section Lin

variable [hO : LineOrder P L]
include hO

theorem mem_ray_of_between {A B D : P} (h : Between A B D) : D ∈ ray A B :=
  ⟨(ne12_of_between (Line := L) h).symm, (ne13_of_between (Line := L) h).symm,
    (collinear_of_between (Line := L) h).swap12, not_between_swap12 (Line := L) h⟩

theorem mem_ray_of_between' {A B D : P} (h : Between A D B) : D ∈ ray A B :=
  ⟨(ne13_of_between (Line := L) h).symm, (ne12_of_between (Line := L) h).symm,
    (collinear_of_between (Line := L) h).swap23.swap12,
    fun h' => not_between_swap12 (Line := L) h (between_symm (Line := L) h')⟩

theorem ray_eq_of_mem {O A X : P} (h : X ∈ ray O A) : ray O X = ray O A := by
  ext Z
  constructor
  · intro hZ; exact sameSidePt_trans h hZ
  · intro hZ; exact sameSidePt_trans (sameSidePt_symm h) hZ

omit hO in
theorem ne_of_mem_ray {O A X : P} (h : X ∈ ray O A) : X ≠ O := h.2.1

/-- Points on the two half-rays of `O` determined by `X` and `Y`, with `O` between `X` and `Y`, have
`O` between them. -/
theorem between_of_rays {X O Y X' Y' : P} (h : Between X O Y) (hX : X' ∈ ray O X)
    (hY : Y' ∈ ray O Y) : Between X' O Y' := by
  obtain ⟨a, hXa, hOa, hYa⟩ := collinear_of_between (Line := L) h
  have hX'a : X' ∈ a := mem_of_collinear (P := P) hX.2.2.1.swap12 hX.1.symm hOa hXa
  have hY'a : Y' ∈ a := mem_of_collinear (P := P) hY.2.2.1.swap12 hY.1.symm hOa hYa
  rcases (sameSidePt_or_between hOa hX'a hY'a hX.2.1 hY.2.1).1 with h1 | h1
  · exfalso
    have := sameSidePt_trans (sameSidePt_trans hX h1) (sameSidePt_symm hY)
    exact this.2.2.2 h
  · exact h1

end Lin

/-! ### Sides of a line -/

section Plane

variable [hO : PlaneOrder P L]
include hO

theorem sameSide_of_mem_ray {l : L} {O A X : P} (hO : O ∈ l) (hA : A ∉ l) (hX : X ∈ ray O A) :
    SameSide l A X := by
  obtain ⟨hAO, hXO, ⟨m, hAm, hOm, hXm⟩, hnb⟩ := hX
  have hml : m ≠ l := fun e => hA (e ▸ hAm)
  refine ⟨hA, fun hXl => hXO (eq_of_mem_of_mem hml hXm hXl hOm hO), ?_⟩
  rintro ⟨Z, hZl, hAZX⟩
  have hZm : Z ∈ m := OrderCore.mem_of_between (P := P) hAZX hAm hXm
  have hZO := eq_of_mem_of_mem hml hZm hZl hOm hO
  rw [hZO] at hAZX
  exact hnb hAZX

theorem opp_of_between {l : L} {O A X : P} (hO : O ∈ l) (hA : A ∉ l) (h : Between A O X) :
    OppositeSides l A X :=
  ⟨hA, fun hX => hA (OrderCore.mem_of_between'' (P := P) h hO hX), O, hO, h⟩

/-- Two points of a line `a` on opposite sides of a line `l` meeting `a` in `B` have `B` between
them. -/
theorem between_of_opp {l a : L} {B C D : P} (hla : l ≠ a) (hBl : B ∈ l) (hBa : B ∈ a)
    (hCa : C ∈ a) (hDa : D ∈ a) (h : OppositeSides l C D) : Between C B D := by
  obtain ⟨-, -, Z, hZl, hZ⟩ := h
  have hZa : Z ∈ a := OrderCore.mem_of_between (P := P) hZ hCa hDa
  rw [eq_of_mem_of_mem hla hZl hZa hBl hBa] at hZ
  exact hZ

/-- A point of a half-ray `OA` lies on the line through `O` and `A`. -/
theorem mem_of_mem_ray {a : L} {O A X : P} (hO : O ∈ a) (hA : A ∈ a) (hX : X ∈ ray O A) : X ∈ a :=
  mem_of_collinear (P := P) hX.2.2.1.swap12 hX.1.symm hO hA

end Plane

/-! ### Congruence of angles -/

section Ang

variable [HasAngCong P] [hA : AngleCongruence P L]
include hA

theorem angCong_symm {A O B A' O' B' : P} (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong A' O' B' A O B :=
  angCong_trans_left h h' h hc (angCong_refl h)

theorem angCong_trans {A O B A' O' B' A'' O'' B'' : P} (h : ¬Collinear A O B)
    (h' : ¬Collinear A' O' B') (h'' : ¬Collinear A'' O'' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A' O' B' A'' O'' B'') : AngCong A O B A'' O'' B'' :=
  angCong_trans_left h' h h'' (angCong_symm h h' h1) h2

/-- Congruence of angles only depends on the half-rays: points of the sides may be replaced by
other points of the same sides. -/
theorem angCong_of_rays {A O B C D A' O' B' C' D' : P} (h : ¬Collinear A O B)
    (h' : ¬Collinear A' O' B') (hC : C ∈ ray O A) (hD : D ∈ ray O B) (hC' : C' ∈ ray O' A')
    (hD' : D' ∈ ray O' B') (hc : AngCong A O B A' O' B') : AngCong C O D C' O' D' := by
  refine angCong_of_sameAngle h h' ?_ ?_ hc
  · unfold SameAngle; rw [ray_eq_of_mem (L := L) hC, ray_eq_of_mem (L := L) hD]
  · unfold SameAngle; rw [ray_eq_of_mem (L := L) hC', ray_eq_of_mem (L := L) hD']

end Ang

/-! ### Theorems 10 and 12 -/

section Cong

variable [HasSegCong P] [HasAngCong P] [hG : PlaneCongruence P L]
include hG

/-- Adjacent segments `AB`, `BD` with `B` between `A` and `D` meet only in `B`. -/
theorem segmentsMeetOnlyAt_of_between {A B D : P} (h : Between A B D) :
    SegmentsMeetOnlyAt (Line := L) A B D := by
  refine ⟨collinear_of_between (Line := L) h, ne12_of_between (Line := L) h,
    ne23_of_between (Line := L) h, ?_⟩
  intro X hX1 hX2
  rcases hX1 with rfl | rfl | h1 <;> rcases hX2 with e | e | h2
  · exact e
  · exact absurd e (ne13_of_between (Line := L) h)
  · exact absurd h2 (not_between_swap12 (Line := L) h)
  · rfl
  · rfl
  · rfl
  · exact e
  · rw [e] at h1; exact absurd h1 (not_between_swap23 (Line := L) h)
  · exact absurd h2 (not_between_swap12 (Line := L)
      (OrderCore.between_of_between_between₂ (L := L) h1 h))

/-- Points of two half-rays from `B` along non-collinear `A`, `B`, `C` are not collinear with
`B`. -/
theorem not_collinear_of_rays {A B C X Y : P} (h : ¬Collinear A B C) (hX : X ∈ ray B A)
    (hY : Y ∈ ray B C) : ¬Collinear X B Y := by
  rintro ⟨m, hXm, hBm, hYm⟩
  apply h
  refine ⟨m, ?_, hBm, ?_⟩
  · exact mem_of_collinear (P := P) hX.2.2.1.swap13 (ne_of_mem_ray hX) hXm hBm
  · exact mem_of_collinear (P := P) hY.2.2.1.swap13 (ne_of_mem_ray hY) hYm hBm


/-- **IV 4, uniqueness**: two half-rays from `O'` on the same side of `l` making angles with the
half-ray `O'A'` of `l` congruent to the same angle coincide. -/
theorem ray_eq_of_angCong {A O B O' A' X Y : P} {l : L} (hAOB : ¬Collinear A O B) (hO' : O' ∈ l)
    (hA' : A' ∈ l) (hA'O' : A' ≠ O') (hX : X ∉ l) (hXY : SameSide l X Y)
    (h1 : AngCong A O B A' O' X) (h2 : AngCong A O B A' O' Y) : ray O' X = ray O' Y := by
  obtain ⟨B', -, -, -, huniq⟩ :=
    PlaneAngleCongruence.ax_IV4 (Line := L) A O B l O' A' X hAOB hO' hA' hA'O' hX
  have hcond : ∀ Z : P, Z ∉ l → SameSide l Z X → ∀ W : P, W ∈ Interior A' O' Z →
      SameSide l W X := by
    intro Z hZ hZX W hW
    have hZO' : Z ≠ O' := fun e => hZ (e ▸ hO')
    obtain ⟨b, hO'b, hZb⟩ := exists_line (Line := L) hZO'.symm
    exact OrderCore.sameSide_trans (hW l b hO' hA' hO'b hZb).1 hZX
  have eX := huniq X hX h1 (hcond X hX (OrderCore.sameSide_refl hX))
  have eY := huniq Y hXY.2.1 h2 (hcond Y hXY.2.1 (OrderCore.sameSide_symm hXY))
  rw [eX, eY]

/-- **Theorem 10, third side**: two sides and the included angle determine the third side. -/
theorem segCong_of_sas {A B C A' B' C' : P} (hT : ¬Collinear A B C) (hT' : ¬Collinear A' B' C')
    (hBC : B ≠ C) (hA'B' : A' ≠ B') (hB'C' : B' ≠ C') (hAB : SegCong A B A' B')
    (hAC : SegCong A C A' C') (hA : AngCong B A C B' A' C') : SegCong B C B' C' := by
  obtain ⟨C'', ⟨hC''r, hC''c⟩, -⟩ := exists_unique_segCong (Line := L) hBC hB'C'
  set l := line A' B' hA'B'
  have hA'l : A' ∈ l := mem_line_left hA'B'
  have hB'l : B' ∈ l := mem_line_right hA'B'
  have hC'l : C' ∉ l := fun h => hT' ⟨l, hA'l, hB'l, h⟩
  have hsame : SameSide l C' C'' := sameSide_of_mem_ray hB'l hC'l hC''r
  have hC''l : C'' ∉ l := hsame.2.1
  have hT'' : ¬Collinear B' A' C'' := not_collinear_of_not_mem hB'l hA'l hA'B'.symm hC''l
  have hBA'C : ¬Collinear B A C := fun h => hT h.swap12
  have hB'A'C' : ¬Collinear B' A' C' := fun h => hT' h.swap12
  have hAB0 : A ≠ B := fun e => hT (by subst e; exact (collinear_of_ne (Line := L) hBC).swap23)
  have hBang := (angCong_of_sas hT hT' hAB hAC hA).1
  have hBang' : AngCong A B C A' B' C'' :=
    angCong_of_rays hT hT' (mem_ray_self (Line := L) hAB0) (mem_ray_self (Line := L) hBC.symm)
      (mem_ray_self (Line := L) hA'B') hC''r hBang
  have hA1 := (angCong_of_sas hBA'C hT'' (segCong_swap_left (segCong_swap_right hAB)) hC''c
    hBang').1
  have hray := ray_eq_of_angCong hBA'C hA'l hB'l hA'B'.symm hC'l hsame hA hA1
  have hC''A' : C'' ≠ A' := fun e => hC''l (e ▸ hA'l)
  have hC''r' : C'' ∈ ray A' C' := by rw [hray]; exact mem_ray_self (Line := L) hC''A'
  have hA'C' : A' ≠ C' := fun e => hC'l (e ▸ hA'l)
  have h1 : C'' ∈ line A' C' hA'C' :=
    mem_of_mem_ray (mem_line_left hA'C') (mem_line_right hA'C') hC''r'
  have h2 : C'' ∈ line B' C' hB'C' :=
    mem_of_mem_ray (mem_line_left hB'C') (mem_line_right hB'C') hC''r
  have hne : line A' C' hA'C' ≠ line B' C' hB'C' := fun e =>
    hT' ⟨line B' C' hB'C', e ▸ mem_line_left hA'C', mem_line_left hB'C', mem_line_right hB'C'⟩
  have : C'' = C' := eq_of_mem_of_mem hne h1 h2 (mem_line_right hA'C') (mem_line_right hB'C')
  rw [← this]; exact hC''c

theorem not_collinear_of_line {l : L} {X Y Z : P} (hX : X ∈ l) (hY : Y ∈ l) (hXY : X ≠ Y)
    (hZ : Z ∉ l) : ¬Collinear X Z Y := fun h =>
  not_collinear_of_not_mem hX hY hXY hZ h.swap23

/-- **Theorem 12**: supplements of congruent angles are congruent. -/
theorem supplement {A B C D A' B' C' D' : P} (hT : ¬Collinear A B C) (hT' : ¬Collinear A' B' C')
    (hAB : A ≠ B) (hBC : B ≠ C) (hA'B' : A' ≠ B') (hB'C' : B' ≠ C')
    (hD : Between A B D) (hD' : Between A' B' D') (h : AngCong A B C A' B' C') :
    AngCong C B D C' B' D' := by
  have hBD : B ≠ D := ne23_of_between (Line := L) hD
  have hB'D' : B' ≠ D' := ne23_of_between (Line := L) hD'
  obtain ⟨A₁, ⟨hA₁r, hA₁c⟩, -⟩ := exists_unique_segCong (Line := L) hAB.symm hA'B'.symm
  obtain ⟨C₁, ⟨hC₁r, hC₁c⟩, -⟩ := exists_unique_segCong (Line := L) hBC hB'C'
  obtain ⟨D₁, ⟨hD₁r, hD₁c⟩, -⟩ := exists_unique_segCong (Line := L) hBD hB'D'
  have hB₁ : Between A₁ B' D₁ := between_of_rays hD' hA₁r hD₁r
  -- the line `AB` and the line `A₁B'`
  set l := line A B hAB
  have hAl : A ∈ l := mem_line_left hAB
  have hBl : B ∈ l := mem_line_right hAB
  have hDl : D ∈ l := OrderCore.mem_of_between' (P := P) hD hAl hBl
  have hCl : C ∉ l := fun h => hT ⟨l, hAl, hBl, h⟩
  have hA₁B' : A₁ ≠ B' := ne_of_mem_ray hA₁r
  set l₁ := line A₁ B' hA₁B'
  have hA₁l : A₁ ∈ l₁ := mem_line_left hA₁B'
  have hB'l : B' ∈ l₁ := mem_line_right hA₁B'
  have hD₁l : D₁ ∈ l₁ := OrderCore.mem_of_between' (P := P) hB₁ hA₁l hB'l
  have hT₁' : ¬Collinear A₁ B' C₁ := not_collinear_of_rays hT' hA₁r hC₁r
  have hC₁l : C₁ ∉ l₁ := fun h => hT₁' ⟨l₁, hA₁l, hB'l, h⟩
  have hAD : A ≠ D := ne13_of_between (Line := L) hD
  have hA₁D₁ : A₁ ≠ D₁ := ne13_of_between (Line := L) hB₁
  have hC₁B' : C₁ ≠ B' := ne_of_mem_ray hC₁r
  have hD₁B' : D₁ ≠ B' := ne_of_mem_ray hD₁r
  -- at the vertex `B`
  have hangB : AngCong A B C A₁ B' C₁ :=
    angCong_of_rays hT hT' (mem_ray_self (Line := L) hAB) (mem_ray_self (Line := L) hBC.symm)
      hA₁r hC₁r h
  have hBAC : ¬Collinear B A C := fun h => hT h.swap12
  have hB'A₁C₁ : ¬Collinear B' A₁ C₁ := fun h => hT₁' h.swap12
  have hBA : SegCong B A B' A₁ := hA₁c
  have hAC₁ : SegCong A C A₁ C₁ :=
    segCong_of_sas hBAC hB'A₁C₁ (fun e => hCl (e ▸ hAl)) hA₁B'.symm
      (fun e => hC₁l (e ▸ hA₁l)) hBA hC₁c hangB
  have hangA := (angCong_of_sas hBAC hB'A₁C₁ hBA hC₁c hangB).1
  -- `AD ≡ A₁D₁` (IV 3)
  have hAD₁ : SegCong A D A₁ D₁ :=
    SegmentCongruence.ax_IV3 (Line := L) A B D A₁ B' D₁ (segmentsMeetOnlyAt_of_between hD)
      (segmentsMeetOnlyAt_of_between hB₁) (segCong_swap_left (segCong_swap_right hBA)) hD₁c
  -- at the vertex `A`
  have hACD : ¬Collinear A C D := not_collinear_of_line hAl hDl hAD hCl
  have hA₁C₁D₁ : ¬Collinear A₁ C₁ D₁ := not_collinear_of_line hA₁l hD₁l hA₁D₁ hC₁l
  have hDAC : ¬Collinear D A C := fun h => hACD (h.swap12.swap23)
  have hD₁A₁C₁ : ¬Collinear D₁ A₁ C₁ := fun h => hA₁C₁D₁ (h.swap12.swap23)
  have hangA' : AngCong D A C D₁ A₁ C₁ :=
    angCong_of_rays hBAC hB'A₁C₁ (mem_ray_of_between hD)
      (mem_ray_self (Line := L) (fun e => hCl (e ▸ hAl))) (mem_ray_of_between hB₁)
      (mem_ray_self (Line := L) (fun e => hC₁l (e ▸ hA₁l))) hangA
  have hangA'' : AngCong C A D C₁ A₁ D₁ :=
    angCong_swap_right (fun h => hACD h.swap12) hD₁A₁C₁ (angCong_swap_left hDAC hD₁A₁C₁ hangA')
  have hCD₁ : SegCong C D C₁ D₁ :=
    segCong_of_sas hACD hA₁C₁D₁ (fun e => hCl (e ▸ hDl)) (fun e => hC₁l (e ▸ hA₁l))
      (fun e => hC₁l (e ▸ hD₁l)) hAC₁ hAD₁ hangA''
  have hangD := (angCong_of_sas hACD hA₁C₁D₁ hAC₁ hAD₁ hangA'').2
  -- at the vertex `D`
  have hADC : ¬Collinear A D C := fun h => hACD h.swap23
  have hA₁D₁C₁ : ¬Collinear A₁ D₁ C₁ := fun h => hA₁C₁D₁ h.swap23
  have hDl' : C ≠ D := fun e => hCl (e ▸ hDl)
  have hangD' : AngCong B D C B' D₁ C₁ :=
    angCong_of_rays hADC hA₁D₁C₁ (mem_ray_of_between' (between_symm (Line := L) hD))
      (mem_ray_self (Line := L) hDl') (mem_ray_of_between' (between_symm (Line := L) hB₁))
      (mem_ray_self (Line := L) (fun e => hC₁l (e ▸ hD₁l))) hangD
  have hD₁B'C₁ : ¬Collinear D₁ B' C₁ := fun h =>
    not_collinear_of_not_mem hD₁l hB'l hD₁B' hC₁l h
  have hDBC' : ¬Collinear D B C := fun h => not_collinear_of_not_mem hDl hBl hBD.symm hCl h
  have hangDB := (angCong_of_sas hDBC' hD₁B'C₁ (segCong_swap_left (segCong_swap_right hD₁c))
    (segCong_swap_left (segCong_swap_right hCD₁)) hangD').1
  -- back to the original half-rays
  have hD'r : D' ∈ ray B' D₁ := by
    rw [ray_eq_of_mem (L := L) hD₁r]; exact mem_ray_self (Line := L) hB'D'.symm
  have hC'r : C' ∈ ray B' C₁ := by
    rw [ray_eq_of_mem (L := L) hC₁r]; exact mem_ray_self (Line := L) hB'C'.symm
  have hfin : AngCong D B C D' B' C' :=
    angCong_of_rays hDBC' hD₁B'C₁ (mem_ray_self (Line := L) hBD.symm)
      (mem_ray_self (Line := L) hBC.symm) hD'r hC'r hangDB
  have hl' : D' ∈ line A' B' hA'B' :=
    OrderCore.mem_of_between' (P := P) hD' (mem_line_left hA'B') (mem_line_right hA'B')
  have hC'l' : C' ∉ line A' B' hA'B' := fun h => hT' ⟨_, mem_line_left hA'B', mem_line_right hA'B', h⟩
  have hD'B'C' : ¬Collinear D' B' C' := fun h =>
    not_collinear_of_not_mem hl' (mem_line_right hA'B') hB'D'.symm hC'l' h
  exact angCong_swap_right (fun h => hDBC' (h.swap13)) hD'B'C'
    (angCong_swap_left hDBC' hD'B'C' hfin)

/-- **The core of Hilbert's argument**: if `B`, `C`, `D` lie on `a`, `A` off `a`, `C` and `D` on
different sides of the line `l = AB`, then `∠BAD` is not congruent to `∠ABC`. -/
theorem no_meet_core {a l : L} {A B C D : P} (hAa : A ∉ a) (hAl : A ∈ l) (hBl : B ∈ l)
    (hBa : B ∈ a) (hCa : C ∈ a) (hDa : D ∈ a) (hopp : OppositeSides l C D)
    (hang : AngCong B A D A B C) : False := by
  have hAB : A ≠ B := fun e => hAa (e ▸ hBa)
  have hla : l ≠ a := fun e => hAa (e ▸ hAl)
  have hCl : C ∉ l := hopp.1
  have hDl : D ∉ l := hopp.2.1
  have hCB : C ≠ B := fun e => hCl (e ▸ hBl)
  have hDB : D ≠ B := fun e => hDl (e ▸ hBl)
  have hAD : A ≠ D := fun e => hAa (e ▸ hDa)
  have hCBD : Between C B D := between_of_opp hla hBl hBa hCa hDa hopp
  obtain ⟨D', ⟨hD'r, hD'c⟩, -⟩ := exists_unique_segCong (Line := L) hAD hCB.symm
  have hD'a : D' ∈ a := mem_of_mem_ray hBa hCa hD'r
  have hsCD' : SameSide l C D' := sameSide_of_mem_ray hBl hCl hD'r
  have hD'l : D' ∉ l := hsCD'.2.1
  have hDBD' : Between D B D' :=
    between_of_rays (between_symm (Line := L) hCBD) (mem_ray_self (Line := L) hDB) hD'r
  have hABD : ¬Collinear A B D := not_collinear_of_not_mem hAl hBl hAB hDl
  have hBAD' : ¬Collinear B A D' := not_collinear_of_not_mem hBl hAl hAB.symm hD'l
  have hBAD : ¬Collinear B A D := fun h => hABD h.swap12
  have hABC : ¬Collinear A B C := not_collinear_of_not_mem hAl hBl hAB hCl
  have hang' : AngCong B A D A B D' :=
    angCong_of_rays hBAD hABC (mem_ray_self (Line := L) hAB.symm)
      (mem_ray_self (Line := L) hAD.symm) (mem_ray_self (Line := L) hAB) hD'r hang
  have h6 := (angCong_of_sas hABD hBAD' (segCong_swap_right (segCong_refl hAB)) hD'c hang').1
  -- the supplement of `∠DAB`
  obtain ⟨G, hDAG⟩ := exists_beyond (Line := L) hAD.symm
  have hDAB : ¬Collinear D A B := fun h => hABD h.swap13.swap12
  have hD'BA : ¬Collinear D' B A := fun h => hBAD' h.swap13.swap12
  have hABD' : ¬Collinear A B D' := fun h => hBAD' h.swap12
  have hsup : AngCong B A G A B D :=
    supplement hDAB hD'BA hAD.symm hAB (fun e => hD'l (e ▸ hBl)) hAB.symm hDAG
      (between_symm (Line := L) hDBD')
      (angCong_swap_right hDAB hABD' (angCong_swap_left hBAD hABD' hang'))
  have hGl : G ∉ l := fun h => hDl (OrderCore.mem_of_between'' (P := P) hDAG hAl h)
  have hBAG : ¬Collinear B A G := not_collinear_of_not_mem hBl hAl hAB.symm hGl
  have hcong : AngCong B A G B A D' := angCong_trans hBAG hABD hBAD' hsup h6
  have hsCG : SameSide l C G := OrderCore.sameSide_of_opp_opp hopp (opp_of_between hAl hDl hDAG)
  have hsGD' : SameSide l G D' := OrderCore.sameSide_trans (OrderCore.sameSide_symm hsCG) hsCD'
  have hray := ray_eq_of_angCong hBAG hAl hBl hAB.symm hGl hsGD' (angCong_refl hBAG) hcong
  have hD'A : D' ≠ A := fun e => hD'l (e ▸ hAl)
  have hD'rG : D' ∈ ray A G := by rw [hray]; exact mem_ray_self (Line := L) hD'A
  set m := line A D hAD
  have hAm : A ∈ m := mem_line_left hAD
  have hDm : D ∈ m := mem_line_right hAD
  have hGm : G ∈ m := OrderCore.mem_of_between' (P := P) hDAG hDm hAm
  have hD'm : D' ∈ m := mem_of_mem_ray hAm hGm hD'rG
  have hma : m = a := line_unique (ne13_of_between (Line := L) hDBD') hDm hD'm hDa hD'a
  exact hAa (hma ▸ hAm)

/-- **The first assertion of the axiom of parallels** follows from groups I, II, IV (plane
geometry): through a point `A` off a line `a` there is a line not meeting `a`. -/
theorem axiomIIIExists : AxiomIIIExists P := by
  intro a A hAa
  obtain ⟨B, C, hBC, hBa, hCa⟩ := exists_two_points (Point := P) a
  have hAB : A ≠ B := fun e => hAa (e ▸ hBa)
  set l := line A B hAB
  have hAl : A ∈ l := mem_line_left hAB
  have hBl : B ∈ l := mem_line_right hAB
  have hla : l ≠ a := fun e => hAa (e ▸ hAl)
  have hCl : C ∉ l := fun h => hBC (eq_of_mem_of_mem hla hBl hBa h hCa)
  have hCA : C ≠ A := fun e => hCl (e ▸ hAl)
  obtain ⟨F, hCAF⟩ := exists_beyond (Line := L) hCA
  have hoppCF : OppositeSides l C F := opp_of_between hAl hCl hCAF
  have hFl : F ∉ l := hoppCF.2.1
  have hABC : ¬Collinear A B C := not_collinear_of_not_mem hAl hBl hAB hCl
  obtain ⟨E, hEl, hEang, hEint, -⟩ :=
    PlaneAngleCongruence.ax_IV4 (Line := L) A B C l A B F hABC hAl hBl hAB.symm hFl
  have hBE : B ≠ E := fun e => hEl (e ▸ hBl)
  have hAE : A ≠ E := fun e => hEl (e ▸ hAl)
  -- `E` lies on the side of `F`
  obtain ⟨X, hBXE⟩ := exists_between (Line := L) hBE
  have hXint : X ∈ Interior B A E := by
    intro a₁ b₁ hAa₁ hBa₁ hAb₁ hEb₁
    have ha₁ : a₁ = l := line_unique hAB hAa₁ hBa₁ hAl hBl
    subst ha₁
    have hBb₁ : B ∉ b₁ := fun h => hEl (by
      rw [line_unique hAB hAl hBl hAb₁ h]; exact hEb₁)
    exact ⟨OrderCore.sameSide_symm (sameSide_of_mem_ray hBl hEl (mem_ray_of_between' hBXE)),
      OrderCore.sameSide_symm (sameSide_of_mem_ray hEb₁ hBb₁
        (mem_ray_of_between' (between_symm (Line := L) hBXE)))⟩
  have hsXF := hEint X hXint
  have hsXE : SameSide l X E :=
    OrderCore.sameSide_symm (sameSide_of_mem_ray hBl hEl (mem_ray_of_between' hBXE))
  have hsEF : SameSide l E F := OrderCore.sameSide_trans (OrderCore.sameSide_symm hsXE) hsXF
  have hoppCE : OppositeSides l C E :=
    OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp hsEF (OrderCore.opp_symm hoppCF))
  -- the line `AE` does not meet `a`
  refine ⟨line A E hAE, mem_line_left hAE, ?_⟩
  rintro ⟨D, hDm, hDa⟩
  have hDA : D ≠ A := fun e => hAa (e ▸ hDa)
  have hDl : D ∉ l := by
    intro hDl
    have hDB : D = B := eq_of_mem_of_mem hla hDl hDa hBl hBa
    subst hDB
    exact hEl (by rw [line_unique hAB hAl hBl (mem_line_left hAE) hDm]; exact mem_line_right hAE)
  have hBAE : ¬Collinear B A E := not_collinear_of_not_mem hBl hAl hAB.symm hEl
  have hang0 : AngCong B A E A B C := angCong_symm hABC hBAE hEang
  rcases (sameSidePt_or_between (mem_line_left hAE) (mem_line_right hAE) hDm hAE.symm hDA).1 with
    hray | hEAD
  · -- `D` on the half-ray `AE`
    have hang : AngCong B A D A B C :=
      angCong_of_rays hBAE hABC (mem_ray_self (Line := L) hAB.symm) hray
        (mem_ray_self (Line := L) hAB) (mem_ray_self (Line := L) (fun e => hCl (e ▸ hBl))) hang0
    have hsED : SameSide l E D := sameSide_of_mem_ray hAl hEl hray
    exact no_meet_core hAa hAl hBl hBa hCa hDa
      (OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hsED)
        (OrderCore.opp_symm hoppCE))) hang
  · -- `A` between `E` and `D`: pass to the supplementary angles
    have hCB : C ≠ B := fun e => hCl (e ▸ hBl)
    obtain ⟨C₂, hCBC₂⟩ := exists_beyond (Line := L) hCB
    have hC₂a : C₂ ∈ a := OrderCore.mem_of_between' (P := P) hCBC₂ hCa hBa
    have hEAB : ¬Collinear E A B := fun h => hBAE h.swap13
    have hCBA : ¬Collinear C B A := fun h => hABC h.swap13
    have hsup : AngCong B A D A B C₂ :=
      supplement hEAB hCBA hAE.symm hAB hCB hAB.symm hEAD hCBC₂
        (angCong_swap_right hEAB hABC (angCong_swap_left hBAE hABC hang0))
    have hoppCC₂ : OppositeSides l C C₂ := opp_of_between hBl hCl hCBC₂
    have hoppED : OppositeSides l E D := opp_of_between hAl hEl hEAD
    have hsCD : SameSide l C D := OrderCore.sameSide_of_opp_opp hoppCE hoppED
    exact no_meet_core hAa hAl hBl hBa hC₂a hDa
      (OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hsCD) hoppCC₂))
      hsup

end Cong

end ParallelExists

end HilbertFoundations
