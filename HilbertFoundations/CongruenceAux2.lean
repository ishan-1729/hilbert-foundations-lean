import HilbertFoundations.CongruenceAux

/-!
# Helper module for `Congruence.lean`: congruence of segments (IV 1–3) and of angles (IV 4–5)

This module contains no unit of Hilbert's text; its results are used by the units of
`Congruence.lean`.

* The linear axioms IV 1–3: symmetry and transitivity of the congruence of segments (§ 7), laying
  off on a half-ray and its uniqueness, Axiom IV 3 read with betweenness (`segCong_add`), the
  subtraction of segments (`segCong_sub`), the order of three points carried by congruence (the
  core of Theorem 9, `between_of_segCong`).
* The plane-free axioms of angles: symmetry and transitivity of the congruence of angles (§ 7) and
  the change of the points chosen on the sides (`angCong_rays`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

section Segments

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] {A B C D E F A' B' C' D' X Y : P}
include hS

/-- § 7: congruence of segments is symmetric (IV 1, IV 2). -/
theorem segCong_symm (hAB : A ≠ B) (hA'B' : A' ≠ B') (h : SegCong A B A' B') :
    SegCong A' B' A B :=
  SegmentCongruence.ax_IV2 (Line := L) A B A' B' A B hAB hA'B' hAB h (segCong_refl (Line := L) hAB)

/-- Congruence of segments is transitive (IV 1, IV 2). -/
theorem segCong_trans (hAB : A ≠ B) (hCD : C ≠ D) (hEF : E ≠ F) (h1 : SegCong A B C D)
    (h2 : SegCong C D E F) : SegCong A B E F :=
  SegmentCongruence.ax_IV2 (Line := L) C D A B E F hCD hAB hEF (segCong_symm hAB hCD h1) h2

theorem segCong_swap (h : SegCong A B A' B') : SegCong B A B' A' :=
  segCong_swap_right (Line := L) (segCong_swap_left (Line := L) h)

/-- IV 1 (existence): a segment can be laid off on a half-ray. -/
theorem segCong_layoff (hAB : A ≠ B) (hA'C' : A' ≠ C') :
    ∃ B', B' ∈ ray A' C' ∧ SegCong A B A' B' :=
  (exists_unique_segCong (Line := L) hAB hA'C').exists

/-- IV 1 (uniqueness): on a half-ray there is only one point at a given distance. -/
theorem eq_of_segCong_ray (hAB : A ≠ B) (hX : X ∈ ray A' C') (hY : Y ∈ ray A' C')
    (h1 : SegCong A B A' X) (h2 : SegCong A B A' Y) : X = Y :=
  (exists_unique_segCong (Line := L) hAB (ne_of_mem_ray' hX).symm).unique ⟨hX, h1⟩ ⟨hY, h2⟩

/-- Two points of a half-ray from `A'` at congruent distances from `A'` coincide. -/
theorem eq_of_segCong_ray' (hX : X ∈ ray A' C') (hY : Y ∈ ray A' C')
    (h : SegCong A' X A' Y) : X = Y := by
  have hXA' := ne_of_mem_ray hX
  have hY' : Y ∈ ray A' X := by rw [ray_eq_of_mem hX]; exact hY
  exact eq_of_segCong_ray hXA'.symm (mem_ray_self' (L := L) hXA') hY'
    (segCong_refl (Line := L) hXA'.symm) h

/-- Axiom IV 3 for segments `AB`, `BC` with `B` between `A` and `C`. -/
theorem segCong_add (h : Between A B C) (h' : Between A' B' C') (h1 : SegCong A B A' B')
    (h2 : SegCong B C B' C') : SegCong A C A' C' := by
  have meet : ∀ {X Y Z : P}, Between X Y Z → SegmentsMeetOnlyAt (Line := L) X Y Z := by
    intro X Y Z hb
    refine ⟨collinear_of_between hb, ne12_of_between hb, ne23_of_between hb, ?_⟩
    intro W hW1 hW2
    rcases hW1 with e | e | hW
    · rcases hW2 with e2 | e2 | h3
      · exact absurd (e.symm.trans e2) (ne12_of_between hb)
      · exact absurd (e.symm.trans e2) (ne13_of_between hb)
      · subst e; exact absurd h3 (not_between_swap12 hb)
    · exact e
    · rcases hW2 with e2 | e2 | h3
      · exact e2
      · subst e2; exact absurd hW (not_between_swap23 hb)
      · exact absurd h3 (not_between_swap12 (OrderLin.trans₂ hW hb).2)
  exact SegmentCongruence.ax_IV3 (Line := L) A B C A' B' C' (meet h) (meet h') h1 h2

/-- Subtraction of segments: if `B` lies between `A` and `C`, `B'` between `A'` and `C'`,
`AB ≡ A'B'` and `AC ≡ A'C'`, then `BC ≡ B'C'` (IV 1, IV 3). -/
theorem segCong_sub (h : Between A B C) (h' : Between A' B' C') (h1 : SegCong A B A' B')
    (h2 : SegCong A C A' C') : SegCong B C B' C' := by
  obtain ⟨E, hE, hcE⟩ := segCong_layoff (L := L) (ne23_of_between h) (ne23_of_between h')
  have hb : Between A' B' E := between_of_mem_rays h' (mem_ray_self' (L := L)
    (ne12_of_between h')) hE
  have h3 := segCong_add h hb h1 hcE
  have hC'r : C' ∈ ray A' B' := mem_ray_of_between' h'
  have hEr : E ∈ ray A' B' := mem_ray_of_between' hb
  rwa [eq_of_segCong_ray (L := L) (ne13_of_between h) hC'r hEr h2 h3]

/-- **The order of three points is carried by congruence** (the core of Theorem 9; IV 1–3): if `B`
lies between `A` and `C`, `A'`, `B'`, `C'` are distinct collinear points and the three segments
are congruent, then `B'` lies between `A'` and `C'`. -/
theorem between_of_segCong (h : Between A B C) (hc : Collinear A' B' C') (hA'B' : A' ≠ B')
    (hB'C' : B' ≠ C') (hA'C' : A' ≠ C') (h1 : SegCong A B A' B') (h2 : SegCong B C B' C')
    (h3 : SegCong A C A' C') : Between A' B' C' := by
  obtain ⟨g, hA'g, hB'g, hC'g⟩ := hc
  obtain ⟨E, hE⟩ := exists_beyond (Line := L) hA'B'
  obtain ⟨Cs, hCs, hcCs⟩ := segCong_layoff (L := L) (ne23_of_between h) (ne23_of_between hE)
  have hb : Between A' B' Cs := between_of_mem_rays hE (mem_ray_self' (L := L) hA'B') hCs
  have h4 := segCong_add h hb h1 hcCs
  have hCsg : Cs ∈ g := mem_right_of_between hb hA'g hB'g
  rcases mem_ray_or_between (L := L) (collinear_of_mem hA'g hCsg hC'g)
      (ne13_of_between hb).symm hA'C'.symm with hr | hr
  · rw [eq_of_segCong_ray (L := L) (ne13_of_between h) hr
      (mem_ray_self' (L := L) (ne13_of_between hb).symm) h3 h4]
    exact hb
  · exfalso
    -- `A'` lies between `C'` and `Cs`, hence between `C'` and `B'`
    have hB'r : B' ∈ ray A' Cs := mem_ray_of_between hb
    have hC'A'B' : Between C' A' B' :=
      between_of_mem_rays (between_symm hr) (mem_ray_self' (L := L) hA'C'.symm) hB'r
    obtain ⟨E', hE'⟩ := exists_beyond (Line := L) hB'C'.symm
    obtain ⟨As, hAs, hcAs⟩ := segCong_layoff (L := L) (ne12_of_between h).symm
      (ne23_of_between hE')
    have hb' : Between C' B' As := between_of_mem_rays hE' (mem_ray_self' (L := L)
      hB'C'.symm) hAs
    have h5 := segCong_add (between_symm h) hb' (segCong_swap h2) hcAs
    have h3' : SegCong C A C' A' := segCong_swap h3
    have hA'r : A' ∈ ray C' B' := mem_ray_of_between hC'A'B'
    have hAsr : As ∈ ray C' B' := mem_ray_of_between' hb'
    have e := eq_of_segCong_ray (L := L) (ne13_of_between h).symm hA'r hAsr h3' h5
    subst e
    exact not_between_swap23 hC'A'B' hb'

/-- If `C` lies between `A` and `B`, `AC ≡ A'C'` with `C'` on the half-ray `A'B'`, and `AB ≡ A'B'`,
then `C'` lies between `A'` and `B'` (IV 1, IV 3). -/
theorem between_of_segCong_ray (h : Between A C B) (hC' : C' ∈ ray A' B')
    (h1 : SegCong A C A' C') (h2 : SegCong A B A' B') : Between A' C' B' := by
  have hC'A' := ne_of_mem_ray hC'
  obtain ⟨E, hE⟩ := exists_beyond (Line := L) hC'A'.symm
  obtain ⟨Y, hY, hcY⟩ := segCong_layoff (L := L) (ne23_of_between h) (ne23_of_between hE)
  have hb : Between A' C' Y := between_of_mem_rays hE (mem_ray_self' (L := L) hC'A'.symm) hY
  have h3 := segCong_add h hb h1 hcY
  have hYr : Y ∈ ray A' B' := by
    rw [← ray_eq_of_mem hC']; exact mem_ray_of_between' hb
  have e := eq_of_segCong_ray (L := L) (ne13_of_between h) hYr
    (mem_ray_self' (L := L) (ne_of_mem_ray' hC')) h3 h2
  rw [← e]; exact hb

end Segments

section Incidence

variable {P : Type u} {L : Type v} [HasLines P L] [hI : Connection P L] {A B C X Y Z : P} {a : L}
include hI

/-- A point off a line through two distinct points is not collinear with them, in any order. -/
theorem nc_of (hX : X ∈ a) (hY : Y ∈ a) (hXY : X ≠ Y) (hZ : Z ∉ a) :
    ¬Collinear X Y Z ∧ ¬Collinear X Z Y ∧ ¬Collinear Z X Y ∧ ¬Collinear Y X Z ∧
      ¬Collinear Y Z X ∧ ¬Collinear Z Y X := by
  have h : ¬Collinear X Y Z := fun hc => hZ (mem_of_collinear hc hXY hX hY)
  exact ⟨h, fun hc => h hc.swap23, fun hc => h hc.perm231, fun hc => h hc.swap12,
    fun hc => h hc.perm312, fun hc => h hc.swap13⟩

/-- Two lines through `C` (one through `A`, one through `B`, `A`, `B`, `C` not collinear) meet only
in `C`. -/
theorem eq_of_collinear_collinear (hn : ¬Collinear A B C) (h1 : Collinear A C X)
    (h2 : Collinear B C X) : X = C := by
  by_contra hXC
  have hCX : C ≠ X := Ne.symm hXC
  obtain ⟨g, hCg, hXg⟩ := exists_line (Line := L) hCX
  have hA : A ∈ g := mem_of_collinear h1.perm231 hCX hCg hXg
  have hB : B ∈ g := mem_of_collinear h2.perm231 hCX hCg hXg
  exact hn ⟨g, hA, hB, hCg⟩

end Incidence

section Segments2

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] {A B C D E F A' B' C' D' X Y : P}
include hS

end Segments2

section Angles

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P]
  [hA : AngleCongruence P L] {A B C O A' B' O' A'' B'' O'' X Y X' Y' : P}
include hA

/-- § 7: congruence of angles is symmetric (IV 4, IV 5). -/
theorem angCong_symm (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong A' O' B' A O B :=
  angCong_trans_left h h' h hc (angCong_refl (Line := L) h)

/-- Congruence of angles is transitive (IV 4, IV 5). -/
theorem angCong_trans (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (h'' : ¬Collinear A'' O'' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A' O' B' A'' O'' B'') : AngCong A O B A'' O'' B'' :=
  angCong_trans_left h' h h'' (angCong_symm h h' h1) h2

/-- Congruence of angles does not depend on the points chosen on the sides. -/
theorem angCong_rays (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') (hX : X ∈ ray O A) (hY : Y ∈ ray O B) (hX' : X' ∈ ray O' A')
    (hY' : Y' ∈ ray O' B') : AngCong X O Y X' O' Y' :=
  angCong_of_sameAngle h h' (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem hX).symm
    (ray_eq_of_mem hY).symm) (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem hX').symm
    (ray_eq_of_mem hY').symm) hc

end Angles

end HilbertFoundations
