import HilbertFoundations.CongruenceCloseAux

/-!
# Helper module for `CongruenceClose.lean`: distance-preserving maps of space

This module contains no unit of Hilbert's text. Space geometry with groups I, II, IV
(`SpaceCongruence`). A *tetrahedral frame* `Tet α φ D D'` is a distance-preserving map `φ` of a
plane `α` together with a point `D` off `α` and a point `D'` having the distances of `D` from the
images of all points of `α` (`GoodAt α φ D D'`). For such a frame:

* `Tet.slab`: every point `X` off `α`, other than `D`, lies in a plane `β` through `D` that meets
  `α` in a line, and `β` carries a distance-preserving map `ψ` that agrees with `φ` on that line
  and sends `D` to `D'` (`Slab`);
* `Tet.extend`: every point `X` off `α` has an image `X'` with the distances of `X` from the
  images of all points of `α` and from `D'` (the image `ψ X`);
* `Tet.rigid`: two such points have images at a congruent distance;
* `Tet.unique`: the image is unique;
* `exists_tet`: every distance-preserving map of a plane into a plane belongs to a tetrahedral
  frame (the apex of an isosceles triangle off the plane, carried over through the plane of the
  points equidistant from two points, and the congruence of right angles).

These are the facts of solid geometry behind Theorem 18; they are obtained from the plane theorems
without perpendiculars to planes: the only tool is that a set of points equidistant from two
points, or having prescribed distances, is closed under joining lines.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

/-- Two distinct points, listed, form an injective family. -/
theorem injective_fin2 {P : Type u} {a b : P} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

section Space

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P]

/-- `X'` has the distances of `X` from the images under `φ` of all points of the plane `α`. -/
def GoodAt (α : Pl) (φ : P → P) (X X' : P) : Prop :=
  ∀ Z : P, Z ∈ α → X' ≠ φ Z ∧ SegCong X Z X' (φ Z)

/-- A **tetrahedral frame**: a distance-preserving map `φ` of the plane `α`, a point `D` off `α` and
a point `D'` with the distances of `D` from the images of the points of `α`. -/
structure Tet (α : Pl) (φ : P → P) (D D' : P) : Prop where
  iso : IsoOn {Z : P | Z ∈ α} φ
  hD : D ∉ α
  good : GoodAt α φ D D'

/-- A plane `β` through `D` meeting `α` in the line `A₀E`, with a distance-preserving map `ψ`
agreeing with `φ` at `A₀`, `E` and sending `D` to `D'`. -/
structure Slab (α : Pl) (φ : P → P) (D D' : P) (β : Pl) (ψ : P → P) (A₀ E : P) : Prop where
  hDβ : D ∈ β
  hA₀α : A₀ ∈ α
  hEα : E ∈ α
  hA₀β : A₀ ∈ β
  hEβ : E ∈ β
  hne : A₀ ≠ E
  iso : IsoOn {Z : P | Z ∈ β} ψ
  eA : ψ A₀ = φ A₀
  eE : ψ E = φ E
  eD : ψ D = D'
  maps : ∃ β' : Pl, ∀ Z : P, Z ∈ β → ψ Z ∈ β'

variable [hSC : SpaceCongruence P L Pl]

local notation "𝔽" => (spaceFrame (P := P) (L := L) (Pl := Pl))

omit [HasSegCong P] hSC in
theorem isPl_plane [SpaceAngleCongruence P L Pl] (α : Pl) :
    (spaceFrame (P := P) (L := L) (Pl := Pl)).IsPl {Z : P | Z ∈ α} := ⟨α, rfl⟩

include hSC

theorem exists_not_mem_plane (α : Pl) : ∃ W : P, W ∉ α := by
  obtain ⟨A₁, B₁, C₁, D₁, hn⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L)
    (Plane := Pl)
  by_contra hno
  push Not at hno
  exact hn ⟨α, hno A₁, hno B₁, hno C₁, hno D₁⟩

/-- The common points of two distinct planes are collinear. -/
theorem collinear_of_two_planes {α β : Pl} (hαβ : α ≠ β) {A E Z : P} (hA : A ∈ α) (hE : E ∈ α)
    (hZ : Z ∈ α) (hA' : A ∈ β) (hE' : E ∈ β) (hZ' : Z ∈ β) : Collinear (Line := L) A E Z := by
  by_contra h
  exact hαβ (plane_unique h hA hE hZ hA' hE' hZ')

variable {α β : Pl} {φ ψ : P → P} {D D' A₀ E X Y Z W X' Y' W' X'' : P}

/-- Through `D` and another point `X` there is a slab. -/
theorem Tet.slab (T : Tet α φ D D') (hXD : X ≠ D) :
    ∃ (β : Pl) (ψ : P → P) (A₀ E : P), X ∈ β ∧ Slab α φ D D' β ψ A₀ E := by
  obtain ⟨A, B, C, hA, hB, hC, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  obtain ⟨hAB, -, -⟩ := (𝔽).ne hn
  have h0 : ∃ A₀ : P, A₀ ∈ α ∧ ¬Collinear (Line := L) A₀ D X := by
    by_cases h : Collinear (Line := L) A D X
    · refine ⟨B, hB, fun h' => ?_⟩
      have hA' : A ∈ line (Line := L) D X hXD.symm :=
        mem_of_collinear h.perm231 hXD.symm (mem_line_left _) (mem_line_right _)
      have hB' : B ∈ line (Line := L) D X hXD.symm :=
        mem_of_collinear h'.perm231 hXD.symm (mem_line_left _) (mem_line_right _)
      exact T.hD (liesInPlane_of_mem hAB hA' hB' hA hB D (mem_line_left _))
    · exact ⟨A, hA, h⟩
  obtain ⟨A₀, hA₀, hnc⟩ := h0
  obtain ⟨β, hA₀β, hDβ, hXβ⟩ := exists_plane (Plane := Pl) hnc
  have hne : β ≠ α := fun e => T.hD (e ▸ hDβ)
  obtain ⟨E, hEA, hEβ, hEα⟩ := SpaceConnection.ax_I6 (Line := L) β α A₀ hne hA₀β hA₀
  have nAED : ¬Collinear (Line := L) A₀ E D := fun h =>
    T.hD ((𝔽).memS_of_collinear (isPl_plane α) hA₀ hEα hEA.symm h)
  have hED : E ≠ D := fun e => T.hD (e ▸ hEα)
  have hAD : A₀ ≠ D := fun e => T.hD (e ▸ hA₀)
  obtain ⟨h1, s1⟩ := T.iso A₀ hA₀ E hEα hEA.symm
  obtain ⟨h2, s2⟩ := T.good A₀ hA₀
  obtain ⟨h3, s3⟩ := T.good E hEα
  have s2' : SegCong A₀ D (φ A₀) D' := segCong_swap (L := L) s2
  have s3' : SegCong E D (φ E) D' := segCong_swap (L := L) s3
  have n' : ¬Collinear (Line := L) (φ A₀) (φ E) D' := fun h =>
    nAED ((𝔽).col_rev hEA.symm hED hAD h1 h3.symm h2.symm s1 s3' s2' h)
  obtain ⟨β', hb1, hb2, hb3⟩ := exists_plane (Plane := Pl) n'
  obtain ⟨ψ, e1, e2, e3, hmap, hiso⟩ := (𝔽).plane_iso (isPl_plane β) (isPl_plane β') hA₀β hEβ
    hDβ nAED hb1 hb2 hb3 h1 h2.symm h3.symm s1 s2' s3'
  exact ⟨β, ψ, A₀, E, hXβ, ⟨hDβ, hA₀, hEα, hA₀β, hEβ, hEA.symm, hiso, e1, e2, e3, ⟨β', hmap⟩⟩⟩

theorem Slab.nc (Sl : Slab α φ D D' β ψ A₀ E) (T : Tet α φ D D') :
    ¬Collinear (Line := L) A₀ E D := fun h =>
  T.hD ((𝔽).memS_of_collinear (isPl_plane α) Sl.hA₀α Sl.hEα Sl.hne h)

theorem Slab.ne_plane (Sl : Slab α φ D D' β ψ A₀ E) (T : Tet α φ D D') : α ≠ β :=
  fun e => T.hD (e ▸ Sl.hDβ)

/-- On the common line, the map of the slab agrees with the map of the plane. -/
theorem Slab.agree (Sl : Slab α φ D D' β ψ A₀ E) (T : Tet α φ D D') (hZα : Z ∈ α)
    (hZβ : Z ∈ β) : ψ Z = φ Z := by
  by_cases h1 : Z = A₀
  · rw [h1]; exact Sl.eA
  by_cases h2 : Z = E
  · rw [h2]; exact Sl.eE
  have hc : Collinear (Line := L) A₀ E Z :=
    collinear_of_two_planes (Sl.ne_plane T) Sl.hA₀α Sl.hEα hZα Sl.hA₀β Sl.hEβ hZβ
  obtain ⟨n1, s1⟩ := T.iso A₀ Sl.hA₀α Z hZα (Ne.symm h1)
  obtain ⟨n2, s2⟩ := T.iso E Sl.hEα Z hZα (Ne.symm h2)
  have i1 := Sl.iso A₀ Sl.hA₀β Z hZβ (Ne.symm h1)
  have i2 := Sl.iso E Sl.hEβ Z hZβ (Ne.symm h2)
  rw [Sl.eA] at i1
  rw [Sl.eE] at i2
  have hc' := (𝔽).iso_collinear T.iso Sl.hA₀α Sl.hEα hZα Sl.hne (Ne.symm h2) (Ne.symm h1) hc
  exact ((𝔽).eq_of_equidistant_line (T.iso A₀ Sl.hA₀α E Sl.hEα Sl.hne).1 hc' n1.symm n2.symm
    i1.1.symm i2.1.symm
    (SegmentCongruence.ax_IV2 (Line := L) A₀ Z (φ A₀) (φ Z) (φ A₀) (ψ Z) (Ne.symm h1) n1 i1.1 s1
      i1.2)
    (SegmentCongruence.ax_IV2 (Line := L) E Z (φ E) (φ Z) (φ E) (ψ Z) (Ne.symm h2) n2 i2.1 s2
      i2.2)).symm

/-- The image under the map of the slab of a point off `α` has the distances of that point from
the images of the points of `α`. -/
theorem Slab.good (Sl : Slab α φ D D' β ψ A₀ E) (T : Tet α φ D D') (hWβ : W ∈ β)
    (hWα : W ∉ α) : GoodAt α φ W (ψ W) := by
  intro Z hZ
  have hWZ : W ≠ Z := fun e => hWα (e ▸ hZ)
  by_cases hZβ : Z ∈ β
  · rw [← Sl.agree T hZ hZβ]; exact Sl.iso W hWβ Z hZβ hWZ
  · have d1 : φ Z ≠ ψ A₀ ∧ SegCong Z A₀ (φ Z) (ψ A₀) := by
      rw [Sl.eA]; exact T.iso Z hZ A₀ Sl.hA₀α (fun e => hZβ (e ▸ Sl.hA₀β))
    have d2 : φ Z ≠ ψ E ∧ SegCong Z E (φ Z) (ψ E) := by
      rw [Sl.eE]; exact T.iso Z hZ E Sl.hEα (fun e => hZβ (e ▸ Sl.hEβ))
    have d3 : φ Z ≠ ψ D ∧ SegCong Z D (φ Z) (ψ D) := by
      rw [Sl.eD]; exact ⟨(T.good Z hZ).1.symm, segCong_swap (L := L) (T.good Z hZ).2⟩
    have r := (𝔽).iso_outside (isPl_plane β) Sl.iso Sl.hA₀β Sl.hEβ Sl.hDβ (Sl.nc T) hZβ d1 d2
      d3 hWβ
    exact ⟨r.1.symm, segCong_swap (L := L) r.2⟩

/-- A point with the prescribed distances is the image under the map of the slab. -/
theorem Slab.eq (Sl : Slab α φ D D' β ψ A₀ E) (T : Tet α φ D D') (hWβ : W ∈ β) (hWα : W ∉ α)
    (hWD : W ≠ D) (g : GoodAt α φ W W') (hW'D : W' ≠ D') (s : SegCong W D W' D') :
    W' = ψ W := by
  obtain ⟨β', hmap⟩ := Sl.maps
  have hWA : W ≠ A₀ := fun e => hWα (e ▸ Sl.hA₀α)
  have hWE : W ≠ E := fun e => hWα (e ▸ Sl.hEα)
  have i1 := Sl.iso A₀ Sl.hA₀β W hWβ hWA.symm
  have i2 := Sl.iso E Sl.hEβ W hWβ hWE.symm
  have i3 := Sl.iso D Sl.hDβ W hWβ hWD.symm
  have g1 := g A₀ Sl.hA₀α
  have g2 := g E Sl.hEα
  rw [← Sl.eA] at g1
  rw [← Sl.eE] at g2
  have hW'D2 : W' ≠ ψ D := by rw [Sl.eD]; exact hW'D
  have s3 : SegCong W D W' (ψ D) := by rw [Sl.eD]; exact s
  exact (𝔽).eq_of_equidistant_space (isPl_plane β') (hmap A₀ Sl.hA₀β) (hmap E Sl.hEβ)
    (hmap D Sl.hDβ) (hmap W hWβ)
    ((𝔽).iso_not_collinear Sl.iso Sl.hA₀β Sl.hEβ Sl.hDβ (Sl.nc T)) i1.1.symm i2.1.symm
    i3.1.symm g1.1 g2.1 hW'D2
    (SegmentCongruence.ax_IV2 (Line := L) A₀ W (ψ A₀) (ψ W) (ψ A₀) W' hWA.symm i1.1 g1.1.symm
      i1.2 (segCong_swap (L := L) g1.2))
    (SegmentCongruence.ax_IV2 (Line := L) E W (ψ E) (ψ W) (ψ E) W' hWE.symm i2.1 g2.1.symm
      i2.2 (segCong_swap (L := L) g2.2))
    (SegmentCongruence.ax_IV2 (Line := L) D W (ψ D) (ψ W) (ψ D) W' hWD.symm i3.1 hW'D2.symm
      i3.2 (segCong_swap (L := L) s3))

theorem Slab.rigid (Sl : Slab α φ D D' β ψ A₀ E) (T : Tet α φ D D') (hXβ : X ∈ β)
    (hXα : X ∉ α) (hXD : X ≠ D) (hYα : Y ∉ α) (hYD : Y ≠ D) (hXY : X ≠ Y)
    (gX : GoodAt α φ X X') (hX'D : X' ≠ D') (sX : SegCong X D X' D') (gY : GoodAt α φ Y Y')
    (hY'D : Y' ≠ D') (sY : SegCong Y D Y' D') : X' ≠ Y' ∧ SegCong X Y X' Y' := by
  rw [Sl.eq T hXβ hXα hXD gX hX'D sX]
  by_cases hYβ : Y ∈ β
  · rw [Sl.eq T hYβ hYα hYD gY hY'D sY]; exact Sl.iso X hXβ Y hYβ hXY
  · have d1 : Y' ≠ ψ A₀ ∧ SegCong Y A₀ Y' (ψ A₀) := by rw [Sl.eA]; exact gY A₀ Sl.hA₀α
    have d2 : Y' ≠ ψ E ∧ SegCong Y E Y' (ψ E) := by rw [Sl.eE]; exact gY E Sl.hEα
    have d3 : Y' ≠ ψ D ∧ SegCong Y D Y' (ψ D) := by rw [Sl.eD]; exact ⟨hY'D, sY⟩
    have r := (𝔽).iso_outside (isPl_plane β) Sl.iso Sl.hA₀β Sl.hEβ Sl.hDβ (Sl.nc T) hYβ d1 d2
      d3 hXβ
    exact ⟨r.1.symm, segCong_swap (L := L) r.2⟩

/-- **Existence of the image** of a point off the plane of a tetrahedral frame. -/
theorem Tet.extend (T : Tet α φ D D') (hX : X ∉ α) (hXD : X ≠ D) :
    ∃ X', GoodAt α φ X X' ∧ X' ≠ D' ∧ SegCong X D X' D' := by
  obtain ⟨β, ψ, A₀, E, hXβ, Sl⟩ := T.slab hXD
  have i := Sl.iso X hXβ D Sl.hDβ hXD
  rw [Sl.eD] at i
  exact ⟨ψ X, Sl.good T hXβ hX, i.1, i.2⟩

/-- **Rigidity**: the images of two points off the plane of a tetrahedral frame are at a congruent
distance. -/
theorem Tet.rigid (T : Tet α φ D D') (hXα : X ∉ α) (hXD : X ≠ D) (hYα : Y ∉ α) (hYD : Y ≠ D)
    (hXY : X ≠ Y) (gX : GoodAt α φ X X') (hX'D : X' ≠ D') (sX : SegCong X D X' D')
    (gY : GoodAt α φ Y Y') (hY'D : Y' ≠ D') (sY : SegCong Y D Y' D') :
    X' ≠ Y' ∧ SegCong X Y X' Y' := by
  obtain ⟨β, ψ, A₀, E, hXβ, Sl⟩ := T.slab hXD
  exact Sl.rigid T hXβ hXα hXD hYα hYD hXY gX hX'D sX gY hY'D sY

/-- **Uniqueness of the image** of a point off the plane of a tetrahedral frame. -/
theorem Tet.unique (T : Tet α φ D D') (hXα : X ∉ α) (hXD : X ≠ D) (gX : GoodAt α φ X X')
    (hX'D : X' ≠ D') (sX : SegCong X D X' D') (gX2 : GoodAt α φ X X'') (hX''D : X'' ≠ D')
    (sX2 : SegCong X D X'' D') : X' = X'' := by
  obtain ⟨β, ψ, A₀, E, hXβ, Sl⟩ := T.slab hXD
  rw [Sl.eq T hXβ hXα hXD gX hX'D sX, Sl.eq T hXβ hXα hXD gX2 hX''D sX2]

/-- **Every distance-preserving map of a plane into a plane belongs to a tetrahedral frame.** -/
theorem exists_tet {α α' : Pl} {φ : P → P} (hφ : IsoOn {Z : P | Z ∈ α} φ)
    (hmap : ∀ Z : P, Z ∈ α → φ Z ∈ α') : ∃ D D' : P, Tet α φ D D' := by
  obtain ⟨A₁, A₂, C₀, h1, h2, -, hn0⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  obtain ⟨hA, -, -⟩ := (𝔽).ne hn0
  -- the perpendicular bisector of `A₁A₂` in `α`: two points `H`, `R` and the midpoint `M`
  obtain ⟨H, R, hH, hR, ho, sH, sR⟩ := (𝔽).bisector (isPl_plane α) h1 h2 hA
  have hHR : H ≠ R := by obtain ⟨-, -, Z, -, hZ⟩ := ho; exact ne13_of_between hZ
  obtain ⟨hA₁l, hA₂l⟩ := (𝔽).not_mem_bisector hA ho sH sR hHR
  obtain ⟨M, hMl, hM, -⟩ := (𝔽).midpoint_rt (isPl_plane α) hH hR h1 h2 hA ho sH sR hHR
  have sM : SegCong M A₁ M A₂ := (𝔽).equidistant_of_mem hHR hA₁l hA₂l sH sR hMl
  have hMα : M ∈ α := (𝔽).memS_of_between (isPl_plane α) h1 h2 hM
  have hMA : M ∈ line (Line := L) A₁ A₂ hA :=
    mem_mid_of_between hM (mem_line_left _) (mem_line_right _)
  have hMH : M ≠ H := fun e => ho.1 (e ▸ hMA)
  have hMR : M ≠ R := fun e => ho.2.1 (e ▸ hMA)
  have hMA₁ : M ≠ A₁ := (ne12_of_between hM).symm
  have hMA₂ : M ≠ A₂ := ne23_of_between hM
  have hHA₁ : H ≠ A₁ := fun e => ho.1 (e ▸ mem_line_left _)
  have hHA₂ : H ≠ A₂ := fun e => ho.1 (e ▸ mem_line_right _)
  have hRA₁ : R ≠ A₁ := fun e => ho.2.1 (e ▸ mem_line_left _)
  have hRA₂ : R ≠ A₂ := fun e => ho.2.1 (e ▸ mem_line_right _)
  -- a point `K` off `α` equidistant from `A₁`, `A₂`
  have offPlane : ∀ {γ : Pl} {U V : P} (hUV : U ≠ V), U ∈ γ → V ∈ γ →
      ∃ K : P, K ∉ γ ∧ SegCong K U K V := by
    intro γ U V hUV hU hV
    obtain ⟨W, hW⟩ := exists_not_mem_plane (P := P) (L := L) γ
    have nW : ¬Collinear (Line := L) U V W := fun h =>
      hW ((𝔽).memS_of_collinear (isPl_plane γ) hU hV hUV h)
    obtain ⟨δ, d1, d2, dW⟩ := exists_plane (Plane := Pl) nW
    obtain ⟨K, R₀, hKδ, -, hoK, sK, -⟩ := (𝔽).bisector (isPl_plane δ) d1 d2 hUV
    refine ⟨K, fun h => hW ?_, sK⟩
    rw [plane_unique (nc_of (mem_line_left hUV) (mem_line_right hUV) hUV hoK.1).1 hU hV h d1 d2
      hKδ]
    exact dW
  obtain ⟨K, hKα, sK⟩ := offPlane hA h1 h2
  have hKA₁ : K ≠ A₁ := fun e => hKα (e ▸ h1)
  have hKA₂ : K ≠ A₂ := fun e => hKα (e ▸ h2)
  have hKM : K ≠ M := fun e => hKα (e ▸ hMα)
  -- the images
  have tr : ∀ {X : P}, X ∈ α → X ≠ A₁ → X ≠ A₂ → SegCong X A₁ X A₂ →
      SegCong (φ X) (φ A₁) (φ X) (φ A₂) := by
    intro X hX hX1 hX2 s
    obtain ⟨n1, s1⟩ := hφ X hX A₁ h1 hX1
    obtain ⟨n2, s2⟩ := hφ X hX A₂ h2 hX2
    exact SegmentCongruence.ax_IV2 (Line := L) X A₁ (φ X) (φ A₁) (φ X) (φ A₂) hX1 n1 n2 s1
      (segCong_trans (L := L) hX1 hX2 n2 s s2)
  obtain ⟨hA', sA'⟩ := hφ A₁ h1 A₂ h2 hA
  obtain ⟨hHR', sHR'⟩ := hφ H hH R hR hHR
  obtain ⟨K', hK'α, sK'⟩ := offPlane hA' (hmap A₁ h1) (hmap A₂ h2)
  have nγ : ¬Collinear (Line := L) (φ H) (φ R) K' := fun h =>
    hK'α ((𝔽).memS_of_collinear (isPl_plane α') (hmap H hH) (hmap R hR) hHR' h)
  obtain ⟨γ', g1, g2, g3⟩ := exists_plane (Plane := Pl) nγ
  have hγα : α' ≠ γ' := fun e => hK'α (e ▸ g3)
  have nHRA₁ : ¬Collinear (Line := L) H R A₁ := fun h =>
    hA₁l (mem_of_collinear h hHR (mem_line_left _) (mem_line_right _))
  have nHRA₂ : ¬Collinear (Line := L) H R A₂ := fun h =>
    hA₂l (mem_of_collinear h hHR (mem_line_left _) (mem_line_right _))
  have nA₁' : φ A₁ ∉ γ' := fun h => (𝔽).iso_not_collinear hφ hH hR h1 nHRA₁
    (collinear_of_two_planes hγα (hmap H hH) (hmap R hR) (hmap A₁ h1) g1 g2 h)
  have nA₂' : φ A₂ ∉ γ' := fun h => (𝔽).iso_not_collinear hφ hH hR h2 nHRA₂
    (collinear_of_two_planes hγα (hmap H hH) (hmap R hR) (hmap A₂ h2) g1 g2 h)
  -- every point of `γ'` is equidistant from the images of `A₁`, `A₂`
  have eqγ : ∀ Z : P, Z ∈ γ' → SegCong Z (φ A₁) Z (φ A₂) := fun Z hZ =>
    (𝔽).gen_plane (isPl_plane γ') g1 g2 g3 nγ (G := fun Z => SegCong Z (φ A₁) Z (φ A₂))
      (tr hH hHA₁ hHA₂ sH) (tr hR hRA₁ hRA₂ sR) sK'
      (fun X Y Z hX hY gX gY hXY hc => (𝔽).equidistant_of_mem hXY
        (fun h => nA₁' ((𝔽).lineIn (isPl_plane γ') hX hY hXY _ h))
        (fun h => nA₂' ((𝔽).lineIn (isPl_plane γ') hX hY hXY _ h)) gX gY
        (mem_of_collinear hc hXY (mem_line_left _) (mem_line_right _))) hZ
  -- the triangle `H R K` copied into `γ'`
  have nHRK : ¬Collinear (Line := L) H R K := fun h =>
    hKα ((𝔽).memS_of_collinear (isPl_plane α) hH hR hHR h)
  obtain ⟨ε, e1, e2, e3⟩ := exists_plane (Plane := Pl) nHRK
  have hKH : K ≠ H := fun e => hKα (e ▸ hH)
  have hKR : K ≠ R := fun e => hKα (e ▸ hR)
  obtain ⟨D', hD'γ, hD'g, hD's⟩ := (𝔽).theorem17_exists (isPl_plane ε) (isPl_plane γ')
    (f := ![H, R]) (g := ![φ H, φ R])
    (by intro i; fin_cases i; exacts [e1, e2]) (by intro i; fin_cases i; exacts [g1, g2])
    (injective_fin2 hHR) (injective_fin2 hHR')
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact sHR'
      · exact segCong_swap (L := L) sHR'
      · exact absurd rfl hij)
    (Q := K) e3 (by intro i; fin_cases i; exacts [hKH, hKR])
  have gH : D' ≠ φ H ∧ SegCong K H D' (φ H) := ⟨hD'g 0, segCong_swap (L := L) (hD's 0)⟩
  have gR : D' ≠ φ R ∧ SegCong K R D' (φ R) := ⟨hD'g 1, segCong_swap (L := L) (hD's 1)⟩
  have hcM : Collinear (Line := L) H R M := collinear_of_mem (mem_line_left _) (mem_line_right _) hMl
  have gM := (𝔽).iso_outside_line (isPl_plane α) hφ hH hR hHR hKα gH gR hcM
  -- `D'` is off `α'`
  have nHRD' : ¬Collinear (Line := L) (φ H) (φ R) D' := fun h =>
    nHRK ((𝔽).col_rev hHR hKR.symm hKH.symm hHR' gR.1.symm gH.1.symm sHR'
      (segCong_swap (L := L) gR.2) (segCong_swap (L := L) gH.2) h)
  have hD'α : D' ∉ α' := fun h =>
    nHRD' (collinear_of_two_planes hγα (hmap H hH) (hmap R hR) h g1 g2 hD'γ)
  -- the right angles at `M` and at its image
  have nMKA₁ : ¬Collinear (Line := L) M K A₁ := fun h =>
    hKα ((𝔽).memS_of_collinear (isPl_plane α) hMα h1 hMA₁ h.swap23)
  have nMKA₂ : ¬Collinear (Line := L) M K A₂ := fun h =>
    hKα ((𝔽).memS_of_collinear (isPl_plane α) hMα h2 hMA₂ h.swap23)
  have ang1 := ((𝔽).sss nMKA₁ nMKA₂ (segCong_refl (Line := L) hKM.symm) sM sK).1
  have rt : RightAng (L := L) K M A₁ := ⟨fun h => nMKA₁ h.swap12, A₂, hM, ang1⟩
  obtain ⟨hMA₁', sMA₁'⟩ := hφ M hMα A₁ h1 hMA₁
  obtain ⟨hMA₂', sMA₂'⟩ := hφ M hMα A₂ h2 hMA₂
  have hM' : Between (φ A₁) (φ M) (φ A₂) := (𝔽).iso_between hφ h1 hMα h2 hM
  have sM' : SegCong (φ M) (φ A₁) (φ M) (φ A₂) := tr hMα hMA₁ hMA₂ sM
  have sD' : SegCong D' (φ A₁) D' (φ A₂) := eqγ D' hD'γ
  have nMD'A₁ : ¬Collinear (Line := L) (φ M) D' (φ A₁) := fun h =>
    hD'α ((𝔽).memS_of_collinear (isPl_plane α') (hmap M hMα) (hmap A₁ h1) hMA₁' h.swap23)
  have nMD'A₂ : ¬Collinear (Line := L) (φ M) D' (φ A₂) := fun h =>
    hD'α ((𝔽).memS_of_collinear (isPl_plane α') (hmap M hMα) (hmap A₂ h2) hMA₂' h.swap23)
  have ang1' := ((𝔽).sss nMD'A₁ nMD'A₂ (segCong_refl (Line := L) gM.1.symm) sM' sD').1
  have rt' : RightAng (L := L) D' (φ M) (φ A₁) := ⟨fun h => nMD'A₁ h.swap12, φ A₂, hM', ang1'⟩
  have angc := (𝔽).rt_cong rt rt'
  have sKA₁ := ((𝔽).sas nMKA₁ nMD'A₁ (segCong_swap (L := L) gM.2) sMA₁' angc).1
  have gA₁ : D' ≠ φ A₁ ∧ SegCong K A₁ D' (φ A₁) := ⟨fun e => hD'α (e ▸ hmap A₁ h1), sKA₁⟩
  exact ⟨K, D', hφ, hKα, fun Z hZ =>
    (𝔽).iso_outside (isPl_plane α) hφ hH hR h1 nHRA₁ hKα gH gR gA₁ hZ⟩

end Space

end HilbertFoundations
