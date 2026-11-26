import HilbertFoundations.ProportionAux5

/-!
# Helper module for `Proportion.lean`: Hilbert's product construction works in every right angle

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV and axes
`ax`. `prod_construction`: in *every* right angle `∠P₁O'P₂`, with `1 = O'E₁` and `b = O'B'` laid off
on the side `O'P₁` and `a = O'A'` on the side `O'P₂`, the line through `B'` parallel to `E₁A'` (or
equal to it) meets the half-ray `O'P₂` in a point `C'`, and `O'C'` has the length `ab`. The proof
maps the right angle onto the standard right angle `EOF` of the axes by an isometry (Theorem 15 and
the isometry of congruent triangles), as in `hilbertProd_iff`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

namespace Pas

section ProdConstruction

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- **Hilbert's product construction succeeds in every right angle.** -/
theorem prod_construction {O' P1 P2 E1 A' B' : P} (hr : IsRightAngle (L := L) P1 O' P2)
    (hE1 : E1 ∈ ray O' P1) (sE1 : SegCong O' E1 ax.O ax.E) (hB' : B' ∈ ray O' P1)
    (hA' : A' ∈ ray O' P2) {l m : L} (hl1 : E1 ∈ l) (hl2 : A' ∈ l) (hm : B' ∈ m)
    (hpar : l = m ∨ ¬Meets (Point := P) l m) :
    ∃ C' : P, C' ∈ ray O' P2 ∧ C' ∈ m ∧ len ax O' C' = len ax O' A' * len ax O' B' := by
  have hO'P2 : O' ≠ P2 := Ne.symm (ne_of_mem_ray' hA')
  obtain ⟨P2', hP2'r, sP2'⟩ := segCong_layoff (L := L) ax.hOE hO'P2
  have hr' : IsRightAngle (L := L) E1 O' P2' :=
    rightAngle_ray_right ax (rightAngle_ray_left ax hr hE1) hP2'r
  have r0 := axes_right ax
  have a1 := theorem15 hr' r0
  have hn := hr'.1
  have hn0 := r0.1
  obtain ⟨hE1O, hP2'O, -⟩ := nc_ne ax hn
  have sOF : SegCong O' P2' ax.O ax.F :=
    segCong_trans (L := L) (Ne.symm hP2'O) ax.hOE ax.hOF
      (segCong_symm (L := L) ax.hOE (Ne.symm hP2'O) sP2') ax.sOF
  have hn' : ¬Collinear (Line := L) O' E1 P2' := fun h => hn h.swap12
  have hn0' : ¬Collinear (Line := L) ax.O ax.E ax.F := fun h => hn0 h.swap12
  obtain ⟨sEF, -, -⟩ := (pf (L := L) ax.hOE).sas hn' hn0' sE1 sOF a1
  obtain ⟨ψ, hψ, ψO, ψE, ψF⟩ := exists_isom_of_tri hn' hn0' (Ne.symm hE1O) sE1 sOF sEF
  have hψi : ψ⁻¹ ∈ isom (L := L) := (isom (L := L)).inv_mem hψ
  have iO : ψ⁻¹ ax.O = O' := Equiv.Perm.inv_eq_iff_eq.2 ψO.symm
  have iE : ψ⁻¹ ax.E = E1 := Equiv.Perm.inv_eq_iff_eq.2 ψE.symm
  have iF : ψ⁻¹ ax.F = P2' := Equiv.Perm.inv_eq_iff_eq.2 ψF.symm
  have hA'O := ne_of_mem_ray hA'
  have hB'O := ne_of_mem_ray hB'
  have ha := len_pos ax (Ne.symm hA'O)
  have hb := len_pos ax (Ne.symm hB'O)
  -- the images of `A'`, `B'` on the standard half-rays
  have eA : ψ A' = ofV (jE ax (len ax O' A' : V ax)) := by
    have hX : ψ A' ∈ ray ax.O ax.F := by
      have := isom_ray hψ (sameSidePt_trans (sameSidePt_symm hP2'r) hA')
      rwa [ψO, ψF] at this
    obtain ⟨hJr, hJl⟩ := jE_pos ax ha
    have s1 : SegCong O' A' ax.O (ψ A') := by
      have := hψ O' A' (Ne.symm hA'O); rwa [ψO] at this
    have s2 : SegCong O' A' ax.O (ofV (jE ax (len ax O' A' : V ax))) :=
      (len_eq_iff ax (Ne.symm hA'O) (Ne.symm (ne_of_mem_ray hJr))).1 hJl.symm
    exact eq_of_segCong_ray (L := L) (Ne.symm hA'O) hX hJr s1 s2
  have eB : ψ B' = ofV (len ax O' B' : V ax) := by
    have hX : ψ B' ∈ ray ax.O ax.E := by
      have := isom_ray hψ (sameSidePt_trans (sameSidePt_symm hE1) hB')
      rwa [ψO, ψE] at this
    have hJr := ofV_pos ax hb
    have hJl := len_of_pos ax ((pos_iff_posG ax).1 hb)
    have s1 : SegCong O' B' ax.O (ψ B') := by
      have := hψ O' B' (Ne.symm hB'O); rwa [ψO] at this
    have s2 : SegCong O' B' ax.O (ofV (len ax O' B' : V ax)) :=
      (len_eq_iff ax (Ne.symm hB'O) (Ne.symm (ne_of_mem_ray hJr))).1 hJl.symm
    exact eq_of_segCong_ray (L := L) (Ne.symm hB'O) hX hJr s1 s2
  -- the point `C'`
  obtain ⟨hC''r, hC''l⟩ := jE_pos ax (mul_pos ha hb)
  set C'' := ofV (jE ax ((len ax O' A' * len ax O' B' : G ax) : V ax))
  have hψC : ψ (ψ⁻¹ C'') = C'' := perm_apply_inv ψ C''
  refine ⟨ψ⁻¹ C'', ?_, ?_, ?_⟩
  · have := isom_ray hψi hC''r
    rw [iO, iF, ray_eq_of_mem (L := L) hP2'r] at this
    exact this
  · have hEA := E_ne_J ax (len ax O' A')
    have hBC := x_ne_J ax hb (c := len ax O' A' * len ax O' B')
    have hB'C : B' ≠ ψ⁻¹ C'' := fun e => hBC (by
      have h := congrArg ψ e; rw [hψC, eB] at h; exact h)
    have iA : ψ⁻¹ (ofV (jE ax (len ax O' A' : V ax))) = A' := Equiv.Perm.inv_eq_iff_eq.2 eA.symm
    have iB : ψ⁻¹ (ofV (len ax O' B' : V ax)) = B' := Equiv.Perm.inv_eq_iff_eq.2 eB.symm
    have hp := isom_parEq ax hψi hEA hBC (l := line ax.E (ofV (jE ax (len ax O' A' : V ax))) hEA)
      (m := line (ofV (len ax O' B' : V ax)) C'' hBC) (l2 := l) (m2 := line B' (ψ⁻¹ C'') hB'C)
      (mem_line_left _) (mem_line_right _) (mem_line_left _) (mem_line_right _)
      (by rw [iE]; exact hl1) (by rw [iA]; exact hl2) (by rw [iB]; exact mem_line_left _)
      (mem_line_right _)
      ((std_parallel_iff ax hb (mem_line_left _) (mem_line_right _) (mem_line_left _)
        (mem_line_right _)).2 rfl)
    have hmk : m = line B' (ψ⁻¹ C'') hB'C :=
      eq_of_parEq (parEq_trans (parEq_symm (hpar : ParEq (P := P) l m)) hp) hm (mem_line_left _)
    rw [hmk]; exact mem_line_right _
  · have := len_isom ax hψ O' (ψ⁻¹ C'')
    rw [ψO, hψC, hC''l] at this
    exact this.symm

end ProdConstruction

end Pas

end HilbertFoundations
