import HilbertFoundations.CompletenessCloseAux

/-!
# Helper module for `CompletenessClose.lean` (2): rectangular co-ordinates of space

This module contains no unit of Hilbert's text. In a geometry of space with groups I–V having a
plane, with a length `ℓ` of segments (`CC.IsLen`, `CompletenessCloseAux.lean`):

* `CC.IsAff`: the functions that are **affine along every line** (`g B · AC = g A · BC + g C · AB`
  for `B` between `A` and `C`). By Stewart's relation, `X ↦ QX² - OX²` is affine for all `Q`, `O`
  (`CC.isAff_sqdiff`).
* The zero set of an affine function is closed under joining lines (`CC.LineClosed`); such a set
  containing three non-collinear points of a plane contains the plane (`CC.plane_closure`, II 2
  and III), and one containing a plane and a point outside it is the whole space
  (`CC.space_closure`, I 6).
* `CC.exists_frame`: three mutually perpendicular unit segments `OE₁`, `OE₂`, `OE₃` (in the metric
  form `EᵢEⱼ² = 2`), `E₃` outside the plane `OE₁E₂`.
* `CC.exists_isometry`: the co-ordinates `xᵢ(X) = (OX² + 1 - EᵢX²)/2` are affine and
  `XY² = Σ (xᵢ(X) - xᵢ(Y))²`: the space is isometric to a subset of the euclidean `ℝ³`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace CC

universe u v w

/-- `g` is **affine along every line** (with respect to the length `ℓ`). -/
def IsAff {P : Type u} [HasBetween P] (ℓ : P → P → ℝ) (g : P → ℝ) : Prop :=
  ∀ A B C, Between A B C → g B * ℓ A C = g A * ℓ B C + g C * ℓ A B

section AffBasic

variable {P : Type u} [HasBetween P] [HasSegCong P] {ℓ : P → P → ℝ}

theorem isAff_const (hℓ : IsLen ℓ) (k : ℝ) : IsAff ℓ (fun _ => k) := by
  intro A B C h
  have := hℓ.add A B C h
  show k * ℓ A C = k * ℓ B C + k * ℓ A B
  linear_combination (-k) * this

theorem IsAff.add {g1 g2 : P → ℝ} (h1 : IsAff ℓ g1) (h2 : IsAff ℓ g2) :
    IsAff ℓ (fun X => g1 X + g2 X) := by
  intro A B C h
  have a := h1 A B C h
  have b := h2 A B C h
  show (g1 B + g2 B) * ℓ A C = (g1 A + g2 A) * ℓ B C + (g1 C + g2 C) * ℓ A B
  linear_combination a + b

theorem IsAff.smul {g : P → ℝ} (h1 : IsAff ℓ g) (k : ℝ) : IsAff ℓ (fun X => k * g X) := by
  intro A B C h
  have a := h1 A B C h
  show k * g B * ℓ A C = k * g A * ℓ B C + k * g C * ℓ A B
  linear_combination k * a

end AffBasic

/-- The co-ordinate of `X` along `OE`: `(OX² + 1 - EX²) / 2`. -/
noncomputable def coordFn {P : Type u} (ℓ : P → P → ℝ) (O E : P) : P → ℝ :=
  fun X => -1 / 2 * (ℓ E X ^ 2 - ℓ O X ^ 2) + 1 / 2

theorem coordFn_apply {P : Type u} (ℓ : P → P → ℝ) (O E X : P) :
    coordFn ℓ O E X = -1 / 2 * (ℓ E X ^ 2 - ℓ O X ^ 2) + 1 / 2 := rfl

section Space

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hG : SpaceGeometry P L Pl] {ℓ : P → P → ℝ}

include hG

theorem isAff_sqdiff (γ : Pl) (hℓ : IsLen ℓ) (Q O : P) :
    IsAff ℓ (fun X => ℓ Q X ^ 2 - ℓ O X ^ 2) := by
  intro A B C h
  have s1 := stewart (L := L) γ hℓ Q h
  have s2 := stewart (L := L) γ hℓ O h
  show (ℓ Q B ^ 2 - ℓ O B ^ 2) * ℓ A C =
    (ℓ Q A ^ 2 - ℓ O A ^ 2) * ℓ B C + (ℓ Q C ^ 2 - ℓ O C ^ 2) * ℓ A B
  linear_combination s1 - s2

theorem isAff_coordFn (γ : Pl) (hℓ : IsLen ℓ) (O E : P) : IsAff ℓ (coordFn ℓ O E) :=
  ((isAff_sqdiff (L := L) γ hℓ E O).smul (-1 / 2)).add (isAff_const hℓ (1 / 2))

theorem IsAff.zero_of_collinear (hℓ : IsLen ℓ) {g : P → ℝ} (hg : IsAff ℓ g) {A B X : P}
    (hAB : A ≠ B) (hA : g A = 0) (hB : g B = 0) (hc : Collinear A B X) : g X = 0 := by
  by_cases hXA : X = A
  · rw [hXA]; exact hA
  by_cases hXB : X = B
  · rw [hXB]; exact hB
  rcases between_trichotomy (Line := L) hc hAB (Ne.symm hXA) (Ne.symm hXB) with h | h | h
  · have e := hg B A X h
    rw [hA, hB] at e
    have hp := hℓ.pos B A (Ne.symm hAB)
    have e' : g X * ℓ B A = 0 := by linarith
    rcases mul_eq_zero.1 e' with h0 | h0
    · exact h0
    · exact absurd h0 hp.ne'
  · have e := hg A B X h
    rw [hA, hB] at e
    have hp := hℓ.pos A B hAB
    have e' : g X * ℓ A B = 0 := by linarith
    rcases mul_eq_zero.1 e' with h0 | h0
    · exact h0
    · exact absurd h0 hp.ne'
  · have e := hg A X B h
    rw [hA, hB] at e
    have hp := hℓ.pos A B hAB
    have e' : g X * ℓ A B = 0 := by linarith
    rcases mul_eq_zero.1 e' with h0 | h0
    · exact h0
    · exact absurd h0 hp.ne'

/-- A set of points containing, with two distinct points, every point of their line. -/
def LineClosed (S : Set P) : Prop :=
  ∀ A B X : P, A ≠ B → A ∈ S → B ∈ S → Collinear (Line := L) A B X → X ∈ S

omit hG in
theorem lineClosed_def (S : Set P) : LineClosed (L := L) S ↔
    ∀ A B X : P, A ≠ B → A ∈ S → B ∈ S → Collinear (Line := L) A B X → X ∈ S := Iff.rfl

theorem IsAff.lineClosed (hℓ : IsLen ℓ) {g : P → ℝ} (hg : IsAff ℓ g) :
    LineClosed (L := L) {X | g X = 0} :=
  fun _ _ _ hAB hA hB hc => hg.zero_of_collinear (L := L) hℓ hAB hA hB hc

/-- A line-closed set containing three non-collinear points of a plane contains the plane. -/
theorem plane_closure {S : Set P} (hS : LineClosed (L := L) S) (β : Pl) {A B C : P} (hA : A ∈ β)
    (hB : B ∈ β) (hC : C ∈ β) (hn : ¬Collinear A B C) (sA : A ∈ S) (sB : B ∈ S) (sC : C ∈ S) :
    ∀ X, X ∈ β → X ∈ S := by
  intro X hX
  obtain ⟨hAB, hCB, hAC⟩ := ne_of_not_collinear (L := L) hn (line_through_space (Pl := Pl) B)
  have hBC : B ≠ C := hCB.symm
  obtain ⟨ab, hAab, hBab⟩ := exists_line (Line := L) hAB
  obtain ⟨bc, hBbc, hCbc⟩ := exists_line (Line := L) hBC
  have hCab : C ∉ ab := fun h => hn ⟨ab, hAab, hBab, h⟩
  by_cases hXab : X ∈ ab
  · exact hS A B X hAB sA sB ⟨ab, hAab, hBab, hXab⟩
  by_cases hXbc : X ∈ bc
  · exact hS B C X hBC sB sC ⟨bc, hBbc, hCbc, hXbc⟩
  obtain ⟨D, hD⟩ := exists_between (Line := L) hBC
  have hDbc : D ∈ bc := mem_mid_of_between hD hBbc hCbc
  have hBD : B ≠ D := ne12_of_between (Line := L) hD
  have hDC : D ≠ C := ne23_of_between (Line := L) hD
  have hDβ : D ∈ β := mem_plane_of_between (L := L) hD hB hC
  have sD : D ∈ S := hS B C D hBC sB sC ⟨bc, hBbc, hCbc, hDbc⟩
  have hXC : X ≠ C := fun e => hXbc (by rw [e]; exact hCbc)
  have hXD : X ≠ D := fun e => hXbc (by rw [e]; exact hDbc)
  obtain ⟨xc, hXxc, hCxc⟩ := exists_line (Line := L) hXC
  obtain ⟨xd, hXxd, hDxd⟩ := exists_line (Line := L) hXD
  have hne : xc ≠ xd := by
    intro e
    have hDxc : D ∈ xc := by rw [e]; exact hDxd
    have e2 : xc = bc := line_unique hDC hDxc hCxc hDbc hCbc
    exact hXbc (by rw [← e2]; exact hXxc)
  have habβ : LiesInPlane (Point := P) ab β := liesInPlane_of_mem hAB hAab hBab hA hB
  have hxcβ : LiesInPlane (Point := P) xc β := liesInPlane_of_mem hXC hXxc hCxc hX hC
  have hxdβ : LiesInPlane (Point := P) xd β := liesInPlane_of_mem hXD hXxd hDxd hX hDβ
  have hmeet : Meets (Point := P) xc ab ∨ Meets (Point := P) xd ab := by
    by_contra hno
    obtain ⟨h1, h2⟩ := not_or.1 hno
    obtain ⟨b, -, hu⟩ := hG.toSpaceParallels.ax_III β ab X habβ hX hXab
    exact hne ((hu xc ⟨hxcβ, hXxc, h1⟩).trans (hu xd ⟨hxdβ, hXxd, h2⟩).symm)
  rcases hmeet with ⟨N, hNxc, hNab⟩ | ⟨N, hNxd, hNab⟩
  · have sN : N ∈ S := hS A B N hAB sA sB ⟨ab, hAab, hBab, hNab⟩
    have hNC : N ≠ C := fun e => hCab (by rw [← e]; exact hNab)
    exact hS N C X hNC sN sC ⟨xc, hNxc, hCxc, hXxc⟩
  · have sN : N ∈ S := hS A B N hAB sA sB ⟨ab, hAab, hBab, hNab⟩
    have hDab : D ∉ ab := by
      intro h
      have e2 : ab = bc := line_unique hBD hBab h hBbc hDbc
      exact hCab (by rw [e2]; exact hCbc)
    have hND : N ≠ D := fun e => hDab (by rw [← e]; exact hNab)
    exact hS N D X hND sN sD ⟨xd, hNxd, hDxd, hXxd⟩

/-- A line-closed set containing a plane and a point outside it is the whole space. -/
theorem space_closure {S : Set P} (hS : LineClosed (L := L) S) (α : Pl)
    (hα : ∀ X, X ∈ α → X ∈ S) {D : P} (hD : D ∈ S) (hDα : D ∉ α) : ∀ X, X ∈ S := by
  intro X
  obtain ⟨O, -, -, hO, -, -, -⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  have hOD : O ≠ D := fun e => hDα (by rw [← e]; exact hO)
  by_cases hc : Collinear O D X
  · exact hS O D X hOD (hα O hO) hD hc
  obtain ⟨β, hOβ, hDβ, hXβ⟩ := exists_plane (Plane := Pl) hc
  have hαβ : α ≠ β := fun e => hDα (by rw [e]; exact hDβ)
  obtain ⟨m, hm⟩ := planes_meet_in_line (L := L) hαβ hO hOβ
  obtain ⟨M1, M2, hM, h1, h2⟩ := exists_two_points (Point := P) m
  have hDm : D ∉ m := fun h => hDα ((hm D).1 h).1
  have hn : ¬Collinear M1 M2 D := not_collinear_of_not_mem h1 h2 hM hDm
  exact plane_closure (L := L) hS β ((hm M1).1 h1).2 ((hm M2).1 h2).2 hDβ hn
    (hα _ ((hm M1).1 h1).1) (hα _ ((hm M2).1 h2).1) hD X hXβ

/-- Two unit segments from `O` whose extremities are at distance `√2` are not collinear. -/
theorem nc_of_right (hℓ : IsLen ℓ) {O A B : P} (h1 : ℓ O A = 1) (h2 : ℓ O B = 1)
    (h3 : ℓ A B ^ 2 = 2) : ¬Collinear O A B := by
  intro hc
  have hOA : O ≠ A := by intro e; rw [e, hℓ.self] at h1; norm_num at h1
  have hOB : O ≠ B := by intro e; rw [e, hℓ.self] at h2; norm_num at h2
  have hAB : A ≠ B := by intro e; rw [e, hℓ.self] at h3; norm_num at h3
  rcases between_trichotomy (Line := L) hc hOA hOB hAB with h | h | h
  · have e := hℓ.add A O B h
    rw [hℓ.symm (L := L) A O, h1, h2] at e
    rw [← e] at h3; norm_num at h3
  · have e := hℓ.add O A B h
    rw [h1, h2] at e
    have e' : ℓ A B = 0 := by linarith
    rw [e'] at h3; norm_num at h3
  · have e := hℓ.add O B A h
    rw [h1, h2, hℓ.symm (L := L) B A] at e
    have e' : ℓ A B = 0 := by linarith
    rw [e'] at h3; norm_num at h3

/-- **A rectangular frame**: three mutually perpendicular unit segments from a point of a plane,
two of them in the plane and the third one ending outside it. -/
theorem exists_frame (α₀ : Pl) :
    ∃ (ℓ : P → P → ℝ) (O E1 E2 E3 : P), IsLen ℓ ∧ O ∈ α₀ ∧ E1 ∈ α₀ ∧ E2 ∈ α₀ ∧ E3 ∉ α₀ ∧
      ¬Collinear O E1 E2 ∧ ℓ O E1 = 1 ∧ ℓ O E2 = 1 ∧ ℓ O E3 = 1 ∧
      ℓ E1 E2 ^ 2 = 2 ∧ ℓ E1 E3 ^ 2 = 2 ∧ ℓ E2 E3 ^ 2 = 2 := by
  obtain ⟨O, E1, Z0, hO, hE1, -, hn0⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α₀
  have hOE1 : O ≠ E1 :=
    (ne_of_not_collinear (L := L) hn0 (line_through_space (Pl := Pl) E1)).1
  obtain ⟨ℓ, hℓ, h1⟩ := exists_len (L := L) α₀ hO hE1 hOE1
  obtain ⟨E2, hE2, h2, h12, hrig⟩ := exists_perp (L := L) hℓ α₀ hO hE1 hOE1
  have h2' : ℓ O E2 = 1 := h2.trans h1
  have h12' : ℓ E1 E2 ^ 2 = 2 := by rw [h12, h1]; norm_num
  have hnc12 : ¬Collinear O E1 E2 := nc_of_right (L := L) hℓ h1 h2' h12'
  obtain ⟨A, B, C, D', hncop⟩ :=
    SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
  have hD : ∃ D : P, D ∉ α₀ := by
    by_contra hno
    have hall : ∀ D : P, D ∈ α₀ := fun D => by
      by_contra hD; exact hno ⟨D, hD⟩
    exact hncop ⟨α₀, hall A, hall B, hall C, hall D'⟩
  obtain ⟨D, hD⟩ := hD
  have hncD : ¬Collinear O E1 D := by
    rintro ⟨g, hOg, hE1g, hDg⟩
    exact hD (liesInPlane_of_mem hOE1 hOg hE1g hO hE1 D hDg)
  obtain ⟨β, hOβ, hE1β, hDβ⟩ := exists_plane (Plane := Pl) hncD
  obtain ⟨F1, hF1β, f1, f2, -⟩ := exists_perp (L := L) hℓ β hOβ hE1β hOE1
  have f1' : ℓ O F1 = 1 := f1.trans h1
  have f2' : ℓ E1 F1 ^ 2 = 2 := by rw [f2, h1]; norm_num
  have hncF : ¬Collinear O E1 F1 := nc_of_right (L := L) hℓ h1 f1' f2'
  have hF1α : F1 ∉ α₀ := by
    intro h
    have e : α₀ = β := plane_unique hncF hO hE1 h hOβ hE1β hF1β
    exact hD (by rw [e]; exact hDβ)
  have hOE2 : O ≠ E2 := by intro e; rw [← e, hℓ.self] at h2'; norm_num at h2'
  have hnc2F : ¬Collinear O E2 F1 := by
    rintro ⟨g, hOg, hE2g, hFg⟩
    exact hF1α (liesInPlane_of_mem hOE2 hOg hE2g hO hE2 F1 hFg)
  obtain ⟨γ, hOγ, hE2γ, hF1γ⟩ := exists_plane (Plane := Pl) hnc2F
  obtain ⟨E3, hE3γ, g1, g2, -⟩ := exists_perp (L := L) hℓ γ hOγ hE2γ hOE2
  have h3 : ℓ O E3 = 1 := g1.trans h2'
  have h23 : ℓ E2 E3 ^ 2 = 2 := by rw [g2, h2']; norm_num
  have haff : IsAff ℓ (fun X => (ℓ E1 X ^ 2 - ℓ O X ^ 2) + (-1)) :=
    (isAff_sqdiff (L := L) α₀ hℓ E1 O).add (isAff_const hℓ (-1))
  have hcl := haff.lineClosed (L := L) hℓ
  have z : (ℓ E1 E3 ^ 2 - ℓ O E3 ^ 2) + (-1) = 0 := by
    refine plane_closure (L := L) hcl γ hOγ hE2γ hF1γ hnc2F ?_ ?_ ?_ E3 hE3γ
    · show (ℓ E1 O ^ 2 - ℓ O O ^ 2) + (-1) = 0
      rw [hℓ.symm (L := L) E1 O, h1, hℓ.self]; norm_num
    · show (ℓ E1 E2 ^ 2 - ℓ O E2 ^ 2) + (-1) = 0
      rw [h12', h2']; norm_num
    · show (ℓ E1 F1 ^ 2 - ℓ O F1 ^ 2) + (-1) = 0
      rw [f2', f1']; norm_num
  have h13 : ℓ E1 E3 ^ 2 = 2 := by rw [h3] at z; linarith
  refine ⟨ℓ, O, E1, E2, E3, hℓ, hO, hE1, hE2, ?_, hnc12, h1, h2', h3, h12', h13, h23⟩
  intro hE3α
  refine hrig E3 hE3α ⟨by rw [h3, h1], by rw [h13, h1]; norm_num, by rw [h23, h1]; norm_num⟩

/-- **Rectangular co-ordinates of space**: three affine functions `x₁, x₂, x₃` with
`XY² = Σ (xᵢ(X) - xᵢ(Y))²`, and four points with the co-ordinates of the origin and of the three
unit points. -/
theorem exists_isometry (α₀ : Pl) :
    ∃ (ℓ : P → P → ℝ) (x1 x2 x3 : P → ℝ), IsLen ℓ ∧ IsAff ℓ x1 ∧ IsAff ℓ x2 ∧ IsAff ℓ x3 ∧
      (∀ X Y, ℓ X Y ^ 2 = (x1 X - x1 Y) ^ 2 + (x2 X - x2 Y) ^ 2 + (x3 X - x3 Y) ^ 2) ∧
      ∃ O E1 E2 E3 : P, (x1 O = 0 ∧ x2 O = 0 ∧ x3 O = 0) ∧ (x1 E1 = 1 ∧ x2 E1 = 0 ∧ x3 E1 = 0) ∧
        (x1 E2 = 0 ∧ x2 E2 = 1 ∧ x3 E2 = 0) ∧ (x1 E3 = 0 ∧ x2 E3 = 0 ∧ x3 E3 = 1) := by
  obtain ⟨ℓ, O, E1, E2, E3, hℓ, hO, hE1, hE2, hE3, hnc, h1, h2, h3, h12, h13, h23⟩ :=
    exists_frame (P := P) (L := L) α₀
  have a1 := isAff_coordFn (L := L) α₀ hℓ O E1
  have a2 := isAff_coordFn (L := L) α₀ hℓ O E2
  have a3 := isAff_coordFn (L := L) α₀ hℓ O E3
  have s1 : ℓ E1 O = 1 := (hℓ.symm (L := L) E1 O).trans h1
  have s2 : ℓ E2 O = 1 := (hℓ.symm (L := L) E2 O).trans h2
  have s3 : ℓ E3 O = 1 := (hℓ.symm (L := L) E3 O).trans h3
  have h21 : ℓ E2 E1 ^ 2 = 2 := by rw [hℓ.symm (L := L) E2 E1]; exact h12
  have h31 : ℓ E3 E1 ^ 2 = 2 := by rw [hℓ.symm (L := L) E3 E1]; exact h13
  have h32 : ℓ E3 E2 ^ 2 = 2 := by rw [hℓ.symm (L := L) E3 E2]; exact h23
  have o1 : coordFn ℓ O E1 O = 0 := by rw [coordFn_apply, s1, hℓ.self]; norm_num
  have o2 : coordFn ℓ O E2 O = 0 := by rw [coordFn_apply, s2, hℓ.self]; norm_num
  have o3 : coordFn ℓ O E3 O = 0 := by rw [coordFn_apply, s3, hℓ.self]; norm_num
  have e11 : coordFn ℓ O E1 E1 = 1 := by rw [coordFn_apply, hℓ.self, h1]; norm_num
  have e21 : coordFn ℓ O E2 E1 = 0 := by rw [coordFn_apply, h21, h1]; norm_num
  have e31 : coordFn ℓ O E3 E1 = 0 := by rw [coordFn_apply, h31, h1]; norm_num
  have e12 : coordFn ℓ O E1 E2 = 0 := by rw [coordFn_apply, h12, h2]; norm_num
  have e22 : coordFn ℓ O E2 E2 = 1 := by rw [coordFn_apply, hℓ.self, h2]; norm_num
  have e32 : coordFn ℓ O E3 E2 = 0 := by rw [coordFn_apply, h32, h2]; norm_num
  have e13 : coordFn ℓ O E1 E3 = 0 := by rw [coordFn_apply, h13, h3]; norm_num
  have e23 : coordFn ℓ O E2 E3 = 0 := by rw [coordFn_apply, h23, h3]; norm_num
  have e33 : coordFn ℓ O E3 E3 = 1 := by rw [coordFn_apply, hℓ.self, h3]; norm_num
  -- the polarisation identity, from the closure lemmas
  have key : ∀ Q X : P, (ℓ Q X ^ 2 - ℓ O X ^ 2) + (-(ℓ O Q ^ 2)) +
      ((2 * coordFn ℓ O E1 Q) * coordFn ℓ O E1 X + (2 * coordFn ℓ O E2 Q) * coordFn ℓ O E2 X +
        (2 * coordFn ℓ O E3 Q) * coordFn ℓ O E3 X) = 0 := by
    intro Q
    have haff : IsAff ℓ (fun X => (ℓ Q X ^ 2 - ℓ O X ^ 2) + (-(ℓ O Q ^ 2)) +
        ((2 * coordFn ℓ O E1 Q) * coordFn ℓ O E1 X + (2 * coordFn ℓ O E2 Q) * coordFn ℓ O E2 X +
          (2 * coordFn ℓ O E3 Q) * coordFn ℓ O E3 X)) :=
      ((isAff_sqdiff (L := L) α₀ hℓ Q O).add (isAff_const hℓ (-(ℓ O Q ^ 2)))).add
        (((a1.smul (2 * coordFn ℓ O E1 Q)).add (a2.smul (2 * coordFn ℓ O E2 Q))).add
          (a3.smul (2 * coordFn ℓ O E3 Q)))
    have hcl := haff.lineClosed (L := L) hℓ
    have q1 := coordFn_apply ℓ O E1 Q
    have q2 := coordFn_apply ℓ O E2 Q
    have q3 := coordFn_apply ℓ O E3 Q
    have hpl := plane_closure (L := L) hcl α₀ hO hE1 hE2 hnc
      (by
        show (ℓ Q O ^ 2 - ℓ O O ^ 2) + (-(ℓ O Q ^ 2)) +
          ((2 * coordFn ℓ O E1 Q) * coordFn ℓ O E1 O + (2 * coordFn ℓ O E2 Q) * coordFn ℓ O E2 O +
            (2 * coordFn ℓ O E3 Q) * coordFn ℓ O E3 O) = 0
        rw [o1, o2, o3, hℓ.self, hℓ.symm (L := L) Q O]; ring)
      (by
        show (ℓ Q E1 ^ 2 - ℓ O E1 ^ 2) + (-(ℓ O Q ^ 2)) +
          ((2 * coordFn ℓ O E1 Q) * coordFn ℓ O E1 E1 + (2 * coordFn ℓ O E2 Q) * coordFn ℓ O E2 E1 +
            (2 * coordFn ℓ O E3 Q) * coordFn ℓ O E3 E1) = 0
        rw [e11, e21, e31, h1, q1, hℓ.symm (L := L) Q E1]; ring)
      (by
        show (ℓ Q E2 ^ 2 - ℓ O E2 ^ 2) + (-(ℓ O Q ^ 2)) +
          ((2 * coordFn ℓ O E1 Q) * coordFn ℓ O E1 E2 + (2 * coordFn ℓ O E2 Q) * coordFn ℓ O E2 E2 +
            (2 * coordFn ℓ O E3 Q) * coordFn ℓ O E3 E2) = 0
        rw [e12, e22, e32, h2, q2, hℓ.symm (L := L) Q E2]; ring)
    have hE3S : (ℓ Q E3 ^ 2 - ℓ O E3 ^ 2) + (-(ℓ O Q ^ 2)) +
        ((2 * coordFn ℓ O E1 Q) * coordFn ℓ O E1 E3 + (2 * coordFn ℓ O E2 Q) * coordFn ℓ O E2 E3 +
          (2 * coordFn ℓ O E3 Q) * coordFn ℓ O E3 E3) = 0 := by
      rw [e13, e23, e33, h3, q3, hℓ.symm (L := L) Q E3]; ring
    intro X
    exact space_closure (L := L) hcl α₀ hpl hE3S hE3 X
  have norm : ∀ X : P, ℓ O X ^ 2 =
      coordFn ℓ O E1 X ^ 2 + coordFn ℓ O E2 X ^ 2 + coordFn ℓ O E3 X ^ 2 := by
    intro X
    have k := key X X
    rw [hℓ.self] at k
    linarith
  refine ⟨ℓ, coordFn ℓ O E1, coordFn ℓ O E2, coordFn ℓ O E3, hℓ, a1, a2, a3, ?_,
    O, E1, E2, E3, ⟨o1, o2, o3⟩, ⟨e11, e21, e31⟩, ⟨e12, e22, e32⟩, ⟨e13, e23, e33⟩⟩
  intro X Y
  have k := key X Y
  have nX := norm X
  have nY := norm Y
  linear_combination k + nX + nY

end Space

end CC

end HilbertFoundations
