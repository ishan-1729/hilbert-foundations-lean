import HilbertFoundations.CompletenessCloseAux2

/-!
# Helper module for `CompletenessClose.lean` (3): the embedding into the real co-ordinate space

This module contains no unit of Hilbert's text.

* `CC.PreEmb P L Pl`: an embedding of a system of points, lines and planes into the analytic geometry
  `Coord ℝ 3` (Analytic.lean): injective maps preserving and reflecting incidence and betweenness,
  the congruence of *genuine* segments and the congruence of *genuine* angles.
* Linear part (`SegmentCongruence` only): a map `ι` into `Coord ℝ 3` that is isometric for a length
  `ℓ` (`CC.IsLen`) and carries points lying between to points lying between is injective, reflects
  betweenness (`CC.emb_between_rev`), preserves and reflects collinearity and the congruence of
  genuine segments, and carries every line into a unique line (`CC.emb_line`).
* Space: the co-ordinates of `CompletenessCloseAux2.lean` give such a map (`CC.exists_metric_emb`),
  and the congruence of genuine angles is determined by the congruence of segments in any geometry
  of space (`CC.ang_char`: Theorems 10 and 16), hence preserved and reflected. That planes go to
  planes (`CC.emb_plane`) and that every geometry of space with I–V having a plane has an embedding
  into `Coord ℝ 3` (`CC.exists_preEmb`) is proved in `CompletenessCloseAux5.lean`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace CC

universe u v w

/-- An **embedding into the real co-ordinate space**, the congruences being compared on genuine
segments and genuine angles only. -/
structure PreEmb (P : Type u) (L : Type v) (Pl : Type w) [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [HasSegCong P] [HasAngCong P] where
  pt : P → Coord ℝ 3
  line : L → CoordLine ℝ 3
  plane : Pl → CoordPlane ℝ 3
  pt_injective : Function.Injective pt
  line_injective : Function.Injective line
  plane_injective : Function.Injective plane
  mem_iff : ∀ (A : P) (a : L), pt A ∈ line a ↔ A ∈ a
  memPlane_iff : ∀ (A : P) (α : Pl), pt A ∈ plane α ↔ A ∈ α
  between_iff : ∀ A B C : P, Between (pt A) (pt B) (pt C) ↔ Between A B C
  segCong_iff : ∀ A B C D : P, A ≠ B → C ≠ D →
    (SegCong (pt A) (pt B) (pt C) (pt D) ↔ SegCong A B C D)
  angCong_iff : ∀ A O B A' O' B' : P, ¬Collinear (Line := L) A O B →
    ¬Collinear (Line := L) A' O' B' →
    (AngCong (pt A) (pt O) (pt B) (pt A') (pt O') (pt B') ↔ AngCong A O B A' O' B')

theorem eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, h]

/-! ### Isometric maps into `Coord ℝ 3` (linear axioms) -/

section Linear

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] {ℓ : P → P → ℝ} {ι : P → Coord ℝ 3}

omit [HasLines P L] hS in
theorem IsLen.nonneg (hℓ : IsLen ℓ) (A B : P) : 0 ≤ ℓ A B := by
  by_cases h : A = B
  · rw [h, hℓ.self]
  · exact (hℓ.pos A B h).le

omit [HasLines P L] hS in
theorem emb_injective (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X)) : Function.Injective ι := by
  intro X Y h
  by_contra hne
  have hp := hℓ.pos X Y hne
  have e := hiso X Y
  rw [h, sub_self, Coord.ip_zero_left] at e
  have h2 := mul_pos hp hp
  nlinarith

omit [HasLines P L] hS in
theorem emb_segCong (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X)) {A B C D : P} (hAB : A ≠ B)
    (hCD : C ≠ D) : SegCong (ι A) (ι B) (ι C) (ι D) ↔ SegCong A B C D := by
  rw [Coord.segCong_iff, ← hiso A B, ← hiso C D, hℓ.cong A B C D hAB hCD]
  exact ⟨fun h => eq_of_sq_eq (hℓ.nonneg A B) (hℓ.nonneg C D) h, fun h => by rw [h]⟩

omit [HasLines P L] hS in
theorem emb_len_param (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X)) {A B C : P} {t : ℝ} (t0 : 0 < t)
    (h : ι B = t • (ι C - ι A) + ι A) : ℓ A B = t * ℓ A C := by
  have e := hiso A B
  have e2 : t • (ι C - ι A) + ι A - ι A = t • (ι C - ι A) := add_sub_cancel_right _ _
  rw [h, e2, Coord.ip_smul_left, Coord.ip_smul_right, ← hiso A C] at e
  refine eq_of_sq_eq (hℓ.nonneg A B) (mul_nonneg t0.le (hℓ.nonneg A C)) ?_
  rw [e]; ring

include hS in
/-- **Betweenness is reflected.** -/
theorem emb_between_rev (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X))
    (hbtw : ∀ A B C, Between A B C → Between (ι A) (ι B) (ι C)) {A B C : P}
    (h : Between (ι A) (ι B) (ι C)) : Between A B C := by
  obtain ⟨hAC', t, t0, t1, hB⟩ := AffPt.sbtw_iff_param.1 (AffPt.between_iff.1 h)
  have hAC : A ≠ C := fun e => hAC' (by rw [e])
  have lB := emb_len_param hℓ hiso t0 hB
  have pAC := hℓ.pos A C hAC
  have hAB : A ≠ B := by
    intro e
    rw [← e, hℓ.self] at lB
    have := mul_pos t0 pAC
    linarith
  obtain ⟨B', hB', sB'⟩ := segCong_layoff (L := L) hAB hAC
  have hAB' : A ≠ B' := (ne_of_mem_ray (L := L) hB').symm
  have lB' : ℓ A B' = ℓ A B := ((hℓ.cong A B A B' hAB hAB').1 sB').symm
  have hpos := mul_pos (sub_pos.2 t1) pAC
  rcases mem_ray_cases (L := L) hB' (mem_ray_self' (L := L) hAC.symm) with e | hb | hb
  · rw [e] at lB'
    nlinarith
  · have h2 := hbtw A B' C hb
    obtain ⟨-, t', t0', t1', hB''⟩ := AffPt.sbtw_iff_param.1 (AffPt.between_iff.1 h2)
    have lB'' := emb_len_param hℓ hiso t0' hB''
    have ett : t' = t := by
      have e3 : t' * ℓ A C = t * ℓ A C := by rw [← lB'', lB', lB]
      exact mul_right_cancel₀ pAC.ne' e3
    have e4 : ι B' = ι B := by rw [hB'', hB, ett]
    have e5 := emb_injective hℓ hiso e4
    rw [← e5]; exact hb
  · have e := hℓ.add A C B' hb
    have p := hℓ.pos C B' (ne23_of_between (Line := L) hb)
    nlinarith

include hS in
/-- Collinearity is preserved. -/
theorem emb_collinear (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X))
    (hbtw : ∀ A B C, Between A B C → Between (ι A) (ι B) (ι C)) {A B C : P}
    (hc : Collinear (Line := L) A B C) :
    Collinear (Line := CoordLine ℝ 3) (ι A) (ι B) (ι C) := by
  have hinj := emb_injective hℓ hiso
  by_cases hAB : A = B
  · subst hAB
    by_cases hAC : A = C
    · subst hAC
      obtain ⟨l, hl⟩ := line_through_space (Pl := CoordPlane ℝ 3) (ι A)
      exact ⟨l, hl, hl, hl⟩
    · obtain ⟨l, h1, h2⟩ := exists_line (Line := CoordLine ℝ 3) (hinj.ne hAC)
      exact ⟨l, h1, h1, h2⟩
  by_cases hAC : A = C
  · subst hAC
    obtain ⟨l, h1, h2⟩ := exists_line (Line := CoordLine ℝ 3) (hinj.ne hAB)
    exact ⟨l, h1, h2, h1⟩
  by_cases hBC : B = C
  · subst hBC
    obtain ⟨l, h1, h2⟩ := exists_line (Line := CoordLine ℝ 3) (hinj.ne hAB)
    exact ⟨l, h1, h2, h2⟩
  rcases between_trichotomy (Line := L) hc hAB hAC hBC with h | h | h
  · exact (collinear_of_between (Line := CoordLine ℝ 3) (hbtw _ _ _ h)).swap12
  · exact collinear_of_between (Line := CoordLine ℝ 3) (hbtw _ _ _ h)
  · exact (collinear_of_between (Line := CoordLine ℝ 3) (hbtw _ _ _ h)).swap23

include hS in
/-- Collinearity of three distinct points is reflected. -/
theorem emb_collinear_rev (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X))
    (hbtw : ∀ A B C, Between A B C → Between (ι A) (ι B) (ι C)) {A B C : P}
    (hc : Collinear (Line := CoordLine ℝ 3) (ι A) (ι B) (ι C)) (hAB : A ≠ B) (hAC : A ≠ C)
    (hBC : B ≠ C) : Collinear (Line := L) A B C := by
  have hinj := emb_injective hℓ hiso
  rcases between_trichotomy (Line := CoordLine ℝ 3) hc (hinj.ne hAB) (hinj.ne hAC) (hinj.ne hBC)
    with h | h | h
  · exact (collinear_of_between (Line := L) (emb_between_rev hℓ hiso hbtw h)).swap12
  · exact collinear_of_between (Line := L) (emb_between_rev hℓ hiso hbtw h)
  · exact (collinear_of_between (Line := L) (emb_between_rev hℓ hiso hbtw h)).swap23

include hS in
/-- Half-rays go into half-rays. -/
theorem emb_ray (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X))
    (hbtw : ∀ A B C, Between A B C → Between (ι A) (ι B) (ι C)) {O A X : P}
    (h : X ∈ ray (Line := L) O A) : ι X ∈ ray (Line := CoordLine ℝ 3) (ι O) (ι A) := by
  have hinj := emb_injective hℓ hiso
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨hinj.ne h1, hinj.ne h2, emb_collinear hℓ hiso hbtw h3,
    fun hb => h4 (emb_between_rev hℓ hiso hbtw hb)⟩

include hS in
/-- **Every line goes into a unique line of the co-ordinate space.** -/
theorem emb_line (hℓ : IsLen ℓ)
    (hiso : ∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X))
    (hbtw : ∀ A B C, Between A B C → Between (ι A) (ι B) (ι C)) (a : L) :
    ∃ a' : CoordLine ℝ 3, ∀ X : P, ι X ∈ a' ↔ X ∈ a := by
  have hinj := emb_injective hℓ hiso
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) a
  have hAB' : ι A ≠ ι B := hinj.ne hAB
  refine ⟨AffLine.through (ι A) (ι B) hAB', fun X => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_cases hXA : X = A
    · rw [hXA]; exact hA
    by_cases hXB : X = B
    · rw [hXB]; exact hB
    have hc' : Collinear (Line := CoordLine ℝ 3) (ι A) (ι B) (ι X) :=
      ⟨_, AffLine.left_mem_through hAB', AffLine.right_mem_through hAB', h⟩
    have hc := emb_collinear_rev hℓ hiso hbtw hc' hAB (Ne.symm hXA) (Ne.symm hXB)
    exact mem_of_collinear hc hAB hA hB
  · have hc := emb_collinear hℓ hiso hbtw (collinear_of_mem hA hB h)
    exact mem_of_collinear hc hAB' (AffLine.left_mem_through hAB') (AffLine.right_mem_through hAB')

end Linear

/-! ### The congruence of angles is determined by the congruence of segments -/

/-- In a geometry of space (I, II, IV): two genuine angles are congruent iff the triangles cut off
on their sides by congruent segments have congruent third sides (Theorems 10 and 16). -/
theorem ang_char {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl]
    {A O B A' O' B' A1 B1 A1' B1' : P} (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') (hA1 : A1 ∈ ray (Line := L) O A)
    (hB1 : B1 ∈ ray (Line := L) O B) (hA1' : A1' ∈ ray (Line := L) O' A')
    (hB1' : B1' ∈ ray (Line := L) O' B') (sA : SegCong O A1 O' A1') (sB : SegCong O B1 O' B1') :
    AngCong A O B A' O' B' ↔ SegCong A1 B1 A1' B1' := by
  have n1 : ¬Collinear (Line := L) A1 O B1 := not_collinear_of_mem_rays h hA1 hB1
  have n1' : ¬Collinear (Line := L) A1' O' B1' := not_collinear_of_mem_rays h' hA1' hB1'
  have t1 : IsTriangle (Line := L) O A1 B1 := fun hc => n1 hc.swap12
  have t1' : IsTriangle (Line := L) O' A1' B1' := fun hc => n1' hc.swap12
  constructor
  · intro hc
    have hc1 : AngCong A1 O B1 A1' O' B1' := angCong_rays (L := L) h h' hc hA1 hB1 hA1' hB1'
    exact (theorem10_space (L := L) (Pl := Pl) t1 t1' sA sB hc1).2.2.1
  · intro hs
    have hc1 : AngCong A1 O B1 A1' O' B1' :=
      (theorem16_space (L := L) (Pl := Pl) t1 t1' sA sB hs).2.2.2.1
    exact angCong_rays (L := L) n1 n1' hc1 (mem_ray_comm hA1) (mem_ray_comm hB1)
      (mem_ray_comm hA1') (mem_ray_comm hB1')

/-! ### The standard frame of `Coord ℝ 3` is not coplanar -/

theorem not_coplanar_std (α : CoordPlane ℝ 3)
    (h0 : (AffPt.ofV ![0, 0, 0] : Coord ℝ 3) ∈ α) (h1 : (AffPt.ofV ![1, 0, 0] : Coord ℝ 3) ∈ α)
    (h2 : (AffPt.ofV ![0, 1, 0] : Coord ℝ 3) ∈ α) (h3 : (AffPt.ofV ![0, 0, 1] : Coord ℝ 3) ∈ α) :
    False := by
  have d1 := AffPt.sub_mem_direction (AffPt.mem_plane_iff.1 h0) (AffPt.mem_plane_iff.1 h1)
  have d2 := AffPt.sub_mem_direction (AffPt.mem_plane_iff.1 h0) (AffPt.mem_plane_iff.1 h2)
  have d3 := AffPt.sub_mem_direction (AffPt.mem_plane_iff.1 h0) (AffPt.mem_plane_iff.1 h3)
  have hW : α.carrier.direction = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have e : v = AffPt.toV v 0 • ((AffPt.ofV ![1, 0, 0] : Coord ℝ 3) - AffPt.ofV ![0, 0, 0]) +
        AffPt.toV v 1 • ((AffPt.ofV ![0, 1, 0] : Coord ℝ 3) - AffPt.ofV ![0, 0, 0]) +
        AffPt.toV v 2 • ((AffPt.ofV ![0, 0, 1] : Coord ℝ 3) - AffPt.ofV ![0, 0, 0]) := by
      apply AffPt.toV_injective
      funext i
      fin_cases i <;> simp
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ d1)
      (Submodule.smul_mem _ _ d2)) (Submodule.smul_mem _ _ d3)
  have hf := α.finrank_direction
  rw [hW, finrank_top] at hf
  have h3' : Module.finrank ℝ (AffPt ℝ (Fin 3 → ℝ)) = 3 := Module.finrank_fin_fun ℝ
  rw [h3'] at hf
  norm_num at hf

/-! ### The embedding of a geometry of space with I–V -/

section Space

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hG : SpaceGeometry P L Pl]

include hG

/-- **The isometric map into `Coord ℝ 3`** given by rectangular co-ordinates. -/
theorem exists_metric_emb (α₀ : Pl) :
    ∃ (ℓ : P → P → ℝ) (ι : P → Coord ℝ 3), IsLen ℓ ∧
      (∀ X Y, ℓ X Y ^ 2 = Coord.ip (ι Y - ι X) (ι Y - ι X)) ∧
      (∀ A B C, Between A B C → Between (ι A) (ι B) (ι C)) ∧
      ∃ O E1 E2 E3 : P, ι O = AffPt.ofV ![0, 0, 0] ∧
        ι E1 = AffPt.ofV ![1, 0, 0] ∧ ι E2 = AffPt.ofV ![0, 1, 0] ∧ ι E3 = AffPt.ofV ![0, 0, 1] := by
  obtain ⟨ℓ, x1, x2, x3, hℓ, a1, a2, a3, hsq, O, E1, E2, E3, ⟨o1, o2, o3⟩,
    ⟨e11, e21, e31⟩, ⟨e12, e22, e32⟩, ⟨e13, e23, e33⟩⟩ := exists_isometry (P := P) (L := L) α₀
  have hiso : ∀ X Y, ℓ X Y ^ 2 =
      Coord.ip ((AffPt.ofV ![x1 Y, x2 Y, x3 Y] : Coord ℝ 3) - AffPt.ofV ![x1 X, x2 X, x3 X])
        (AffPt.ofV ![x1 Y, x2 Y, x3 Y] - AffPt.ofV ![x1 X, x2 X, x3 X]) := by
    intro X Y
    rw [hsq X Y, Coord.ip_def, Fin.sum_univ_three]
    simp
    ring
  have hinj := emb_injective (ι := fun X => (AffPt.ofV ![x1 X, x2 X, x3 X] : Coord ℝ 3)) hℓ hiso
  refine ⟨ℓ, fun X => AffPt.ofV ![x1 X, x2 X, x3 X], hℓ, hiso, ?_, O, E1, E2, E3,
    by simp only [o1, o2, o3], by simp only [e11, e21, e31], by simp only [e12, e22, e32],
    by simp only [e13, e23, e33]⟩
  intro A B C h
  have hAC := ne13_of_between (Line := L) h
  have pAC := hℓ.pos A C hAC
  have pAB := hℓ.pos A B (ne12_of_between (Line := L) h)
  have pBC := hℓ.pos B C (ne23_of_between (Line := L) h)
  have ad := hℓ.add A B C h
  have key : ∀ g : P → ℝ, IsAff ℓ g → g B = ℓ A B / ℓ A C * (g C - g A) + g A := by
    intro g hg
    have e := hg A B C h
    field_simp
    linear_combination e + g A * ad
  refine AffPt.between_iff.2 (AffPt.sbtw_iff_param.2 ⟨hinj.ne hAC, ℓ A B / ℓ A C, div_pos pAB pAC,
    (div_lt_one pAC).2 (by linarith), ?_⟩)
  apply AffPt.toV_injective
  funext i
  fin_cases i
  · simpa using key x1 a1
  · simpa using key x2 a2
  · simpa using key x3 a3

end Space

end CC

end HilbertFoundations
