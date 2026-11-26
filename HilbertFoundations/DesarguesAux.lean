import HilbertFoundations.Proportion
import HilbertFoundations.DesarguesAlgebra

/-!
# Helper for `Desargues.lean` (§ 22): the plane as the plane `z = 0` of a space over the segments

This module contains no unit of Hilbert's text. Setting: a plane geometry with I 1–2, II, III, IV
(`PlaneCongruence`, `PlaneParallels`) with rectangular axes `ax` (`Pas.Axes`), whose signed segments
form the ordered field `Pas.G ax` (§§ 15–17, Proportion.lean).

* **Planes of `K³` are linear equations** (`plane_of_equation`, `equation_of_plane`), for any field
  `K`: the solution set of `u x + v y + w z + r = 0`, `(u, v, w) ≠ 0`, is a plane of the
  coordinate space `Coord K 3` (Analytic.lean), and every plane is such a solution set.
* **Lines as intersections of planes** (`line_eq_inter`, `inter_eq_line`), in any space geometry
  with I having a plane: every line is the set of common points of two distinct planes, and two
  distinct planes with a common point meet in a line.
* **The plane as `z = 0`** (`planeInSpace ax`): the point with co-ordinates `(x, y)` goes to the
  point `(x, y, 0)` of `Coord (G ax) 3`, a line to the line of the space through the images of two
  of its points; this is a `DesAlg.PlaneInSpace` (incidence and betweenness preserved and
  reflected, bijective onto the plane `z = 0` and onto the lines lying in it). Incidence is § 17
  (`Pas.mem_line_coords`), betweenness is `Pas.between_coords`, `Pas.between_of_coords`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Des

universe u v

open Pas

/-! ## Algebra -/

/-- A vector `e` is a multiple of `d ≠ 0` iff their cross product vanishes. -/
theorem cross_zero_iff {K : Type*} [Field K] {d1 d2 e1 e2 : K} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    d1 * e2 - d2 * e1 = 0 ↔ ∃ r : K, e1 = r * d1 ∧ e2 = r * d2 := by
  constructor
  · intro h
    rcases hd with hd | hd
    · refine ⟨e1 / d1, by rw [div_mul_cancel₀ _ hd], ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff hd]
      linear_combination h
    · refine ⟨e2 / d2, ?_, by rw [div_mul_cancel₀ _ hd]⟩
      rw [div_mul_eq_mul_div, eq_div_iff hd]
      linear_combination -h
  · rintro ⟨r, rfl, rfl⟩
    ring

/-! ## Planes of `K³` and linear equations -/

section Equations

variable {K : Type*} [Field K]

/-- The linear form `u x + v y + w z`. -/
def eqForm (u v w : K) : Coord K 3 →ₗ[K] K where
  toFun X := u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2
  map_add' X Y := by
    simp only [AffPt.toV_add, Pi.add_apply]
    ring
  map_smul' c X := by
    simp only [AffPt.toV_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem eqForm_apply (u v w : K) (X : Coord K 3) :
    eqForm u v w X = u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2 := rfl

instance : Module.Finite K (Coord K 3) := inferInstanceAs (Module.Finite K (Fin 3 → K))

theorem finrank_coord3 : Module.finrank K (Coord K 3) = 3 := Module.finrank_fin_fun K

/-- The kernel of a nonzero linear form on `K³` has dimension `2`. -/
theorem finrank_ker {f : Coord K 3 →ₗ[K] K} (hf : Function.Surjective f) :
    Module.finrank K (LinearMap.ker f) = 2 := by
  have h1 : Module.finrank K (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.2 hf, finrank_top, Module.finrank_self]
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [finrank_coord3] at this
  omega

theorem eqForm_surjective {u v w : K} (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    Function.Surjective (eqForm u v w) := by
  intro k
  rcases h with h | h | h
  · refine ⟨AffPt.ofV ![k / u, 0, 0], ?_⟩
    rw [eqForm_apply]
    simp only [AffPt.toV_ofV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  · refine ⟨AffPt.ofV ![0, k / v, 0], ?_⟩
    rw [eqForm_apply]
    simp only [AffPt.toV_ofV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  · refine ⟨AffPt.ofV ![0, 0, k / w], ?_⟩
    rw [eqForm_apply]
    simp only [AffPt.toV_ofV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring

/-- **Every linear equation with `(u, v, w) ≠ 0` represents a plane.** -/
theorem plane_of_equation (u v w r : K) (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    ∃ π : CoordPlane K 3, ∀ X : Coord K 3, X ∈ π ↔
      u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2 + r = 0 := by
  have hs := eqForm_surjective h
  obtain ⟨X0, hX0⟩ := hs (-r)
  refine ⟨⟨AffineSubspace.mk' X0 (LinearMap.ker (eqForm u v w)),
    by rw [AffineSubspace.direction_mk']; exact finrank_ker hs⟩, fun X => ?_⟩
  show X ∈ AffineSubspace.mk' X0 _ ↔ _
  rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hX0, ← eqForm_apply,
    sub_neg_eq_add]

/-- **Every plane is represented by a linear equation.** -/
theorem equation_of_plane (π : CoordPlane K 3) :
    ∃ u v w r : K, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧ ∀ X : Coord K 3, X ∈ π ↔
      u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2 + r = 0 := by
  set D := π.carrier.direction
  have hD : Module.finrank K D = 2 := π.finrank_direction
  have hlt : D < ⊤ := by
    refine lt_of_le_of_ne le_top fun e => ?_
    have := finrank_top K (Coord K 3)
    rw [← e, hD, finrank_coord3] at this
    exact absurd this (by norm_num)
  obtain ⟨f, hf0, hfD⟩ := Submodule.exists_le_ker_of_lt_top D hlt
  have hfs : Function.Surjective f := by
    intro k
    obtain ⟨X, hX⟩ : ∃ X, f X ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hf0 (LinearMap.ext hc)
    exact ⟨(k / f X) • X, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hX]⟩
  have hker : D = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hfD (by rw [hD, finrank_ker hfs])
  set u := f (AffPt.ofV ![1, 0, 0])
  set v := f (AffPt.ofV ![0, 1, 0])
  set w := f (AffPt.ofV ![0, 0, 1])
  have hfX : ∀ X : Coord K 3, f X = u * AffPt.toV X 0 + v * AffPt.toV X 1 + w * AffPt.toV X 2 := by
    intro X
    have e : X = AffPt.toV X 0 • AffPt.ofV ![1, 0, 0] + AffPt.toV X 1 • AffPt.ofV ![0, 1, 0] +
        AffPt.toV X 2 • AffPt.ofV ![0, 0, 1] := by
      apply AffPt.toV_injective
      funext i
      fin_cases i <;> simp
    conv_lhs => rw [e]
    simp only [map_add, map_smul, smul_eq_mul, u, v, w]
    ring
  obtain ⟨O, hO⟩ := (AffineSubspace.nonempty_iff_ne_bot π.carrier).2 (by
    intro h
    have := π.finrank_direction
    rw [h, AffineSubspace.direction_bot, finrank_bot] at this
    exact absurd this (by norm_num))
  refine ⟨u, v, w, -f O, ?_, fun X => ?_⟩
  · by_contra hc
    push Not at hc
    apply hf0
    apply LinearMap.ext
    intro X
    rw [hfX, hc.1, hc.2.1, hc.2.2]
    simp
  · rw [AffPt.mem_plane_iff, AffPt.mem_iff_sub_mem_direction hO, ← hfX, ← sub_eq_add_neg,
      ← map_sub]
    show X - O ∈ D ↔ _
    rw [hker, LinearMap.mem_ker]

end Equations

/-! ## Lines as intersections of two planes (space geometry with I) -/

section Incidence

variable {P : Type u} {L : Type v} {Pl : Type*} [HasLines P L] [HasPlanes P Pl]
  [SpaceConnection P L Pl]

/-- If a space has a plane, every line is the set of common points of two distinct planes. -/
theorem line_eq_inter [Nonempty Pl] (ℓ : L) :
    ∃ π₁ π₂ : Pl, π₁ ≠ π₂ ∧ ∀ X : P, X ∈ ℓ ↔ X ∈ π₁ ∧ X ∈ π₂ := by
  obtain ⟨α⟩ := ‹Nonempty Pl›
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) ℓ
  -- a point off `ℓ`
  obtain ⟨X0, hX0⟩ : ∃ X0 : P, X0 ∉ ℓ := by
    obtain ⟨X, Y, Z, -, -, -, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
    by_contra hc
    push Not at hc
    exact hn ⟨ℓ, hc X, hc Y, hc Z⟩
  have hn1 : ¬Collinear (Line := L) A B X0 := fun ⟨m, h1, h2, h3⟩ =>
    hX0 ((line_unique hAB hA hB h1 h2) ▸ h3)
  obtain ⟨π₁, h1A, h1B, -⟩ := exists_plane (Line := L) (Plane := Pl) hn1
  obtain ⟨S, hS⟩ : ∃ S : P, S ∉ π₁ := by
    obtain ⟨A1, B1, C1, D1, h⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
    by_contra hall
    push Not at hall
    exact h ⟨π₁, hall A1, hall B1, hall C1, hall D1⟩
  have hSℓ : S ∉ ℓ := fun h => hS (liesInPlane_of_mem hAB hA hB h1A h1B S h)
  have hn2 : ¬Collinear (Line := L) A B S := fun ⟨m, h1, h2, h3⟩ =>
    hSℓ ((line_unique hAB hA hB h1 h2) ▸ h3)
  obtain ⟨π₂, h2A, h2B, h2S⟩ := exists_plane (Line := L) (Plane := Pl) hn2
  refine ⟨π₁, π₂, fun e => hS (e ▸ h2S), fun X => ⟨fun hX =>
    ⟨liesInPlane_of_mem hAB hA hB h1A h1B X hX, liesInPlane_of_mem hAB hA hB h2A h2B X hX⟩,
    fun ⟨h1, h2⟩ => ?_⟩⟩
  by_contra hX
  have hn : ¬Collinear (Line := L) A B X := fun ⟨m, k1, k2, k3⟩ =>
    hX ((line_unique hAB hA hB k1 k2) ▸ k3)
  exact hS ((plane_unique (Line := L) hn h1A h1B h1 h2A h2B h2) ▸ h2S)

/-- The common points of two distinct planes with a common point form a line. -/
theorem inter_eq_line {π₁ π₂ : Pl} (hne : π₁ ≠ π₂) {A : P} (h1 : A ∈ π₁) (h2 : A ∈ π₂) :
    ∃ ℓ : L, ∀ X : P, X ∈ ℓ ↔ X ∈ π₁ ∧ X ∈ π₂ := by
  obtain ⟨B, hBA, hB1, hB2⟩ := SpaceConnection.ax_I6 (Point := P) (Line := L) π₁ π₂ A hne h1 h2
  have hAB : A ≠ B := Ne.symm hBA
  obtain ⟨ℓ, hA, hB⟩ := exists_line (Line := L) hAB
  refine ⟨ℓ, fun X => ⟨fun hX =>
    ⟨liesInPlane_of_mem hAB hA hB h1 hB1 X hX, liesInPlane_of_mem hAB hA hB h2 hB2 X hX⟩,
    fun ⟨k1, k2⟩ => ?_⟩⟩
  by_contra hX
  have hn : ¬Collinear (Line := L) A B X := fun ⟨m, m1, m2, m3⟩ =>
    hX ((line_unique hAB hA hB m1 m2) ▸ m3)
  exact hne (plane_unique (Line := L) hn h1 hB1 k1 h2 hB2 k2)

end Incidence

/-! ## The plane geometry as the plane `z = 0` of the space over its segments -/

section Space

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

/-- The point `(x, y, 0)` of the space of § 22 corresponding to the point with co-ordinates
`(x, y)`. -/
noncomputable def spt (Z : P) : Coord (G ax) 3 := AffPt.ofV ![px ax Z, py ax Z, 0]

theorem spt_0 (Z : P) : AffPt.toV (spt ax Z) 0 = px ax Z := rfl

theorem spt_1 (Z : P) : AffPt.toV (spt ax Z) 1 = py ax Z := rfl

theorem spt_2 (Z : P) : AffPt.toV (spt ax Z) 2 = 0 := rfl

theorem spt_injective : Function.Injective (spt ax) := by
  intro X Y h
  apply (Pas.coords_bijective ax).1
  have h0 := congrArg (fun Z : Coord (G ax) 3 => AffPt.toV Z 0) h
  have h1 := congrArg (fun Z : Coord (G ax) 3 => AffPt.toV Z 1) h
  simp only [spt_0, spt_1] at h0 h1
  simp only [h0, h1]

theorem spt_comb (Z A B : P) (r : G ax) :
    spt ax Z = r • (spt ax B - spt ax A) + spt ax A ↔
      px ax Z - px ax A = r * (px ax B - px ax A) ∧ py ax Z - py ax A = r * (py ax B - py ax A) := by
  constructor
  · intro h
    have h0 := congrArg (fun X : Coord (G ax) 3 => AffPt.toV X 0) h
    have h1 := congrArg (fun X : Coord (G ax) 3 => AffPt.toV X 1) h
    simp only [AffPt.toV_add, AffPt.toV_smul, AffPt.toV_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul, spt_0, spt_1] at h0 h1
    exact ⟨by rw [h0]; ring, by rw [h1]; ring⟩
  · rintro ⟨h0, h1⟩
    apply AffPt.toV_injective
    funext i
    simp only [AffPt.toV_add, AffPt.toV_smul, AffPt.toV_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    fin_cases i
    · show px ax Z = r * (px ax B - px ax A) + px ax A
      linear_combination h0
    · show py ax Z = r * (py ax B - py ax A) + py ax A
      linear_combination h1
    · show (0 : G ax) = r * (0 - 0) + 0
      ring

/-- The plane `z = 0`. -/
noncomputable def zPlane : CoordPlane (G ax) 3 :=
  (plane_of_equation (0 : G ax) 0 1 0 (Or.inr (Or.inr one_ne_zero))).choose

theorem mem_zPlane (Y : Coord (G ax) 3) : Y ∈ zPlane ax ↔ AffPt.toV Y 2 = 0 := by
  rw [zPlane, (plane_of_equation (0 : G ax) 0 1 0 (Or.inr (Or.inr one_ne_zero))).choose_spec Y]
  simp

theorem spt_mem (Z : P) : spt ax Z ∈ zPlane ax := (mem_zPlane ax _).2 rfl

theorem spt_surj (Y : Coord (G ax) 3) (hY : Y ∈ zPlane ax) : ∃ Z : P, spt ax Z = Y := by
  refine ⟨Pas.mkPt ax (AffPt.toV Y 0) (AffPt.toV Y 1), ?_⟩
  obtain ⟨e0, e1⟩ := Pas.mkPt_coords ax (AffPt.toV Y 0) (AffPt.toV Y 1)
  apply AffPt.toV_injective
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact ((mem_zPlane ax Y).1 hY).symm

/-- The line of the space through the images of two distinct points. -/
noncomputable def slnOf {A B : P} (h : A ≠ B) : CoordLine (G ax) 3 :=
  AffLine.through (spt ax A) (spt ax B) ((spt_injective ax).ne h)

theorem mem_slnOf {A B : P} (h : A ≠ B) {l : L} (hA : A ∈ l) (hB : B ∈ l) (X : P) :
    spt ax X ∈ slnOf ax h ↔ X ∈ l := by
  unfold slnOf
  rw [AffLine.mem_through_iff, Pas.mem_line_coords ax h hA hB X, cross_zero_iff (Pas.coords_ne ax h)]
  exact exists_congr fun r => spt_comb ax X A B r

theorem slnOf_in {A B : P} (h : A ≠ B) :
    LiesInPlane (Point := Coord (G ax) 3) (slnOf ax h) (zPlane ax) := by
  intro Y hY
  unfold slnOf at hY
  rw [AffLine.mem_through_iff] at hY
  obtain ⟨r, rfl⟩ := hY
  rw [mem_zPlane]
  simp only [AffPt.toV_add, AffPt.toV_smul, AffPt.toV_sub, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, spt_2, sub_self, mul_zero, add_zero]

theorem two_pts (l : L) : ∃ AB : P × P, AB.1 ≠ AB.2 ∧ AB.1 ∈ l ∧ AB.2 ∈ l := by
  obtain ⟨A, B, h, hA, hB⟩ := exists_two_points (Point := P) l
  exact ⟨(A, B), h, hA, hB⟩

/-- The line of the space corresponding to a line of the plane. -/
noncomputable def sln (l : L) : CoordLine (G ax) 3 :=
  slnOf ax (two_pts (P := P) l).choose_spec.1

theorem mem_sln (X : P) (l : L) : spt ax X ∈ sln ax l ↔ X ∈ l := by
  obtain ⟨hAB, hA, hB⟩ := (two_pts (P := P) l).choose_spec
  exact mem_slnOf ax hAB hA hB X

theorem sln_in (l : L) : LiesInPlane (Point := Coord (G ax) 3) (sln ax l) (zPlane ax) :=
  slnOf_in ax _

theorem sln_injective : Function.Injective (sln ax) := by
  intro l l' h
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  have hA' : A ∈ l' := (mem_sln ax A l').1 (h ▸ (mem_sln ax A l).2 hA)
  have hB' : B ∈ l' := (mem_sln ax B l').1 (h ▸ (mem_sln ax B l).2 hB)
  exact line_unique hAB hA hB hA' hB'

theorem sln_surj (m : CoordLine (G ax) 3)
    (hm : LiesInPlane (Point := Coord (G ax) 3) m (zPlane ax)) : ∃ l, sln ax l = m := by
  obtain ⟨Y1, Y2, hY, h1, h2⟩ := exists_two_points (Point := Coord (G ax) 3) m
  obtain ⟨X1, rfl⟩ := spt_surj ax _ (hm _ h1)
  obtain ⟨X2, rfl⟩ := spt_surj ax _ (hm _ h2)
  have hX : X1 ≠ X2 := fun e => hY (e ▸ rfl)
  refine ⟨line X1 X2 hX, line_unique hY ((mem_sln ax _ _).2 (mem_line_left hX))
    ((mem_sln ax _ _).2 (mem_line_right hX)) h1 h2⟩

theorem spt_between (X Y Z : P) :
    Between (spt ax X) (spt ax Y) (spt ax Z) ↔ Between X Y Z := by
  rw [AffPt.between_iff]
  by_cases hXZ : X = Z
  · subst hXZ
    exact ⟨fun h => absurd rfl h.left_ne_right, fun h => absurd rfl (ne13_of_between (Line := L) h)⟩
  have hd : spt ax Z - spt ax X ≠ 0 := sub_ne_zero.2 ((spt_injective ax).ne (Ne.symm hXZ))
  have key : ∀ r : G ax, Sbtw (G ax) (spt ax X) (r • (spt ax Z - spt ax X) + spt ax X)
      (spt ax Z) ↔ (0 < r ∧ r < 1) ∨ (1 < r ∧ r < 0) := by
    intro r
    have k := sbtw_param_iff (O := spt ax X) hd (0 : G ax) r 1
    rwa [zero_smul, zero_add, one_smul, sub_add_cancel] at k
  constructor
  · intro h
    have hs := h
    obtain ⟨⟨r, -, hr⟩, -, -⟩ := h
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hr
    rw [← hr, key] at hs
    rcases hs with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · obtain ⟨e0, e1⟩ := (spt_comb ax Y X Z r).1 hr.symm
      exact Pas.between_of_coords ax hXZ k1 k2 e0 e1
    · exact absurd (k1.trans k2) (not_lt.2 zero_le_one)
  · intro h
    obtain ⟨t, ht0, ht1, e0, e1⟩ := Pas.between_coords ax h
    rw [(spt_comb ax Y X Z t).2 ⟨e0, e1⟩, key]
    exact Or.inl ⟨ht0, ht1⟩

/-- **The plane geometry as the plane `z = 0` of the space over its segments.** -/
noncomputable def planeInSpace :
    DesAlg.PlaneInSpace P L (Coord (G ax) 3) (CoordLine (G ax) 3) (CoordPlane (G ax) 3) where
  plane := zPlane ax
  pt := spt ax
  ln := sln ax
  pt_injective := spt_injective ax
  pt_mem := spt_mem ax
  pt_surj := spt_surj ax
  ln_injective := sln_injective ax
  ln_in := sln_in ax
  ln_surj := sln_surj ax
  mem_iff := mem_sln ax
  between_iff := spt_between ax

end Space

end Des

end HilbertFoundations
