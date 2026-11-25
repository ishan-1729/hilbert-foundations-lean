import HilbertFoundations.PascalAux6

/-!
# Helper module for `Pascal.lean`: lengths, half-rays in co-ordinates, right triangles

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV, with
rectangular axes `ax`.

* Isometries preserve the congruence of angles; the axes form a right angle (`axes_right`).
* **Lengths** (`len`): a segment `P₁P₂` is congruent to exactly one positive segment `OX` of the
  axis; `len P₁ P₂ ∈ G ax` is that `X`. Congruence of segments is equality of lengths.
* **Rotations are linear over the field** (`rot_xc`, `rot_yc`): the co-ordinates of `ρ t` are `t`
  times those of `ρ E`.
* **Half-rays in co-ordinates** (`ray_coords`): the points `Z` of a half-ray from `V₀` are
  `V₀ + len V₀ Z · (c, s)` for a fixed direction `(c, s)`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section Metric

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

theorem nc_ne {A O B : P} (h : ¬Collinear (Line := L) A O B) : A ≠ O ∧ B ≠ O ∧ A ≠ B :=
  (pf (L := L) ax.hOE).ne h

/-- Isometries preserve the congruence of angles. -/
theorem isom_angCong {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) {A O B : P}
    (h : ¬Collinear (Line := L) A O B) : AngCong A O B (f A) (f O) (f B) := by
  have hn' : ¬Collinear (Line := L) (f A) (f O) (f B) := fun hc => h ((isom_collinear_iff hf).1 hc)
  obtain ⟨hAO, hBO, hAB⟩ := nc_ne ax h
  exact ((pf (L := L) ax.hOE).sss h hn' (hf A O hAO) (hf A B hAB) (hf O B (Ne.symm hBO))).2.1

/-- Isometries preserve right angles. -/
theorem isom_rightAngle {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) {A O B : P}
    (h : IsRightAngle (L := L) A O B) : IsRightAngle (L := L) (f A) (f O) (f B) := by
  obtain ⟨hn, C, hb, hc⟩ := h
  have hn' : ¬Collinear (Line := L) (f A) (f O) (f B) := fun hh => hn ((isom_collinear_iff hf).1 hh)
  have hBOC : ¬Collinear (Line := L) B O C := not_collinear_swap (not_collinear_of_between hn hb)
  have hBOC' : ¬Collinear (Line := L) (f B) (f O) (f C) :=
    fun hh => hBOC ((isom_collinear_iff hf).1 hh)
  refine ⟨hn', f C, isom_between hf hb, ?_⟩
  have a1 := isom_angCong ax hf hn
  have a2 := isom_angCong ax hf hBOC
  exact angCong_trans hn' hn hBOC' (angCong_symm hn hn' a1) (angCong_trans hn hBOC hBOC' hc a2)

theorem ofV_jE_E : ofV (jE ax (eV ax)) = ax.F := ax.JE

theorem jE_F : ax.J ax.F = ht (L := L) ax.O ax.E := by
  rw [← ax.JE, ← Equiv.Perm.mul_apply, ax.JJ]

/-- **The axes form a right angle.** -/
theorem axes_right : IsRightAngle (L := L) ax.E ax.O ax.F := by
  have hEO : ax.E ≠ ax.O := Ne.symm ax.hOE
  have hn : ¬Collinear (Line := L) ax.E ax.O ax.F := by
    rintro ⟨l, hE, hO, hF⟩
    have : l = ax.x := line_unique ax.hOE hO hE ax.hOx ax.hEx
    rw [this] at hF
    exact ax.hOF (ax.hxy _ hF ax.hFy).symm
  refine ⟨hn, ht (L := L) ax.O ax.E, ((ht_eq_iff (L := L) hEO).1 rfl).1, ?_⟩
  have := isom_angCong ax (rot_isom ax.hJ) hn
  rwa [ax.JE, rot_fix ax.hJ, jE_F] at this

/-! ### Lengths -/

theorem exists_len {P1 P2 : P} (h : P1 ≠ P2) :
    ∃ g : G ax, PosG ax g ∧ SegCong P1 P2 ax.O (ofV (g : V ax)) := by
  obtain ⟨X, hXr, hX⟩ := segCong_layoff (L := L) h ax.hOE
  have hXx : X ∈ ax.x := mem_of_collinear (collinear_of_mem_ray hXr) ax.hOE ax.hOx ax.hEx
  exact ⟨⟨toV ax.O X, hXx⟩, hXr, hX⟩

/-- The **length** of the segment `P₁P₂`: the positive segment of the axis congruent to it. -/
noncomputable def len (P1 P2 : P) : G ax := by
  classical
  exact if h : P1 = P2 then 0 else Classical.choose (exists_len ax h)

theorem len_spec {P1 P2 : P} (h : P1 ≠ P2) :
    PosG ax (len ax P1 P2) ∧ SegCong P1 P2 ax.O (ofV (len ax P1 P2 : V ax)) := by
  simp only [len, h, ↓reduceDIte]
  exact Classical.choose_spec (exists_len ax h)

theorem len_pos {P1 P2 : P} (h : P1 ≠ P2) : 0 < len ax P1 P2 :=
  (pos_iff_posG ax).2 (len_spec ax h).1

theorem len_unique {P1 P2 : P} (h : P1 ≠ P2) {g : G ax} (hg : PosG ax g)
    (hs : SegCong P1 P2 ax.O (ofV (g : V ax))) : len ax P1 P2 = g := by
  obtain ⟨h1, h2⟩ := len_spec ax h
  exact Subtype.ext (ofV_injective (eq_of_segCong_ray (L := L) h h1 hg h2 hs))

/-- **Congruent segments are the segments of equal length.** -/
theorem len_eq_iff {P1 P2 Q1 Q2 : P} (h : P1 ≠ P2) (h' : Q1 ≠ Q2) :
    len ax P1 P2 = len ax Q1 Q2 ↔ SegCong P1 P2 Q1 Q2 := by
  obtain ⟨p1, s1⟩ := len_spec ax h
  obtain ⟨p2, s2⟩ := len_spec ax h'
  have hne : ofV (len ax Q1 Q2 : V ax) ≠ ax.O := ne_of_mem_ray p2
  constructor
  · intro e
    rw [← e] at s2
    exact segCong_trans (L := L) h (Ne.symm (ne_of_mem_ray p1)) h' s1
      (segCong_symm (L := L) h' (Ne.symm (ne_of_mem_ray p1)) s2)
  · intro hs
    exact len_unique ax h p2 (segCong_trans (L := L) h h' (Ne.symm hne) hs s2)

theorem len_comm (P1 P2 : P) : len ax P1 P2 = len ax P2 P1 := by
  by_cases h : P1 = P2
  · subst h; rfl
  · exact (len_eq_iff ax h (Ne.symm h)).2 (segCong_swap_right (Line := L)
      (segCong_refl (Line := L) h))

theorem len_of_pos {g : G ax} (hg : PosG ax g) : len ax ax.O (ofV (g : V ax)) = g :=
  len_unique ax (Ne.symm (ne_of_mem_ray hg)) hg (segCong_refl (Line := L) (Ne.symm (ne_of_mem_ray hg)))

theorem len_isom {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (P1 P2 : P) :
    len ax (f P1) (f P2) = len ax P1 P2 := by
  by_cases h : P1 = P2
  · subst h; simp [len]
  · exact (len_eq_iff ax (f.injective.ne h) h).2
      (segCong_symm (L := L) h (f.injective.ne h) (hf P1 P2 h))

/-! ### Rotations are linear over the field -/

theorem AE_mulV {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) {t g : V ax} (ht : t ∈ Xs ax)
    (hg : g ∈ Xs ax) : AE ax hρ (mulV ax t g) = mulV ax t (AE ax hρ g) ∧
      BE ax hρ (mulV ax t g) = mulV ax t (BE ax hρ g) := by
  obtain ⟨β, hβ, hβℓ, hβℓ'⟩ := exists_rot_line ax (O_mem_lA ax ht)
  obtain ⟨k, hk, rfl⟩ := AE_surj ax (O_mem_lA ax ht) (lA_ne_y ax ht) hβ hβℓ hβℓ' hg
  have hAk := (AE_X ax hρ hk).1
  have hBk := (BE_X ax hρ hk).1
  have sl : ∀ h : V ax, h ∈ Xs ax → mulV ax t (AE ax hβ h) = BE ax hβ h := by
    intro h hh; rw [mulV_def ax ht]; exact slope_AE ax _ _ hβ hβℓ hh
  have c1 : AE ax hρ (AE ax hβ k) = AE ax hβ (AE ax hρ k) :=
    congrArg (fun T : AddMonoid.End (V ax) => T k) (AE_comm_AE ax hρ hβ)
  have c2 : BE ax hρ (AE ax hβ k) = AE ax hβ (BE ax hρ k) :=
    congrArg (fun T : AddMonoid.End (V ax) => T k) (AE_comm_BE ax hβ hρ).symm
  have c3 : AE ax hρ (BE ax hβ k) = BE ax hβ (AE ax hρ k) :=
    congrArg (fun T : AddMonoid.End (V ax) => T k) (AE_comm_BE ax hρ hβ)
  have c4 : BE ax hρ (BE ax hβ k) = BE ax hβ (BE ax hρ k) :=
    congrArg (fun T : AddMonoid.End (V ax) => T k) (BE_comm_BE ax hρ hβ)
  refine ⟨?_, ?_⟩
  · rw [sl k hk, c1, sl _ hAk, c3]
  · rw [sl k hk, c2, sl _ hBk, c4]

theorem AE_coords {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) {g : V ax} (hg : g ∈ Xs ax) :
    AE ax hρ g = (xc ax (rE ax hρ g) : V ax) + (xc ax (rE ax hρ g) : V ax) ∧
      BE ax hρ g = (yc ax (rE ax hρ g) : V ax) + (yc ax (rE ax hρ g) : V ax) := by
  obtain ⟨hA, hD, hsum⟩ := AE_X ax hρ hg
  obtain ⟨hB, hJB⟩ := BE_X ax hρ hg
  have e := coords_eq ax (rE ax hρ g)
  have h2 : rE ax hρ g + rE ax hρ g = ((xc ax (rE ax hρ g) : V ax) + xc ax (rE ax hρ g)) +
      jE ax ((yc ax (rE ax hρ g) : V ax) + yc ax (rE ax hρ g)) := by
    rw [map_add]; conv_lhs => rw [e]
    abel
  rw [← hsum, ← hJB] at h2
  have hx := (xc ax (rE ax hρ g)).2
  have hy := (yc ax (rE ax hρ g)).2
  obtain ⟨e1, e2⟩ := coords_unique ax hA hB ((Xs ax).add_mem hx hx) ((Xs ax).add_mem hy hy) h2
  exact ⟨e1, e2⟩

/-- The co-ordinates of `ρ t` are `t` times those of `ρ E`. -/
theorem rot_coords {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) (t : G ax) :
    xc ax (rE ax hρ t) = t * xc ax (rE ax hρ (eV ax)) ∧
      yc ax (rE ax hρ t) = t * yc ax (rE ax hρ (eV ax)) := by
  have hE := eV_mem ax
  obtain ⟨a1, b1⟩ := AE_mulV ax hρ t.2 hE
  rw [mulV_one ax t.2] at a1 b1
  obtain ⟨cx, cy⟩ := AE_coords ax hρ t.2
  obtain ⟨dx, dy⟩ := AE_coords ax hρ hE
  constructor
  · apply Subtype.ext
    rw [← sub_eq_zero]
    apply two_ne_zero_vec' ax
    rw [cx] at a1
    rw [dx, mulV_add ax t.2 (xc ax _).2 (xc ax _).2] at a1
    show (xc ax (rE ax hρ t) : V ax) - mulV ax t (xc ax _) +
      ((xc ax (rE ax hρ t) : V ax) - mulV ax t (xc ax _)) = 0
    rw [show ∀ p q : V ax, p - q + (p - q) = (p + p) - (q + q) by intro p q; abel, a1, sub_self]
  · apply Subtype.ext
    rw [← sub_eq_zero]
    apply two_ne_zero_vec' ax
    rw [cy] at b1
    rw [dy, mulV_add ax t.2 (yc ax _).2 (yc ax _).2] at b1
    show (yc ax (rE ax hρ t) : V ax) - mulV ax t (yc ax _) +
      ((yc ax (rE ax hρ t) : V ax) - mulV ax t (yc ax _)) = 0
    rw [show ∀ p q : V ax, p - q + (p - q) = (p + p) - (q + q) by intro p q; abel, b1, sub_self]

/-! ### Half-rays in co-ordinates -/

/-- The translation taking `V₀` to `O`. -/
noncomputable def trTo (V0 : P) : Equiv.Perm P := tr (L := L) ax.O (ofV (-toV ax.O V0))

theorem trTo_isom (V0 : P) : trTo ax V0 ∈ isom (L := L) := transl_isom (tr_mem _ _)

theorem trTo_apply (V0 Z : P) : toV ax.O (trTo ax V0 Z) = toV ax.O Z - toV ax.O V0 := by
  rw [sub_eq_neg_add]
  have := ofV_add (L := L) (-toV ax.O V0) (toV ax.O Z)
  exact (congrArg (toV ax.O) this).symm

theorem trTo_self (V0 : P) : trTo ax V0 V0 = ax.O := by
  have := congrArg ofV (trTo_apply ax V0 V0)
  rwa [sub_self, ofV_zero (L := L)] at this

/-- **A half-ray in co-ordinates**: there is a direction `(c, s)` such that every point `Z` of the
half-ray `V₀X` is `V₀ + len V₀ Z · (c, s)`. -/
theorem ray_coords {V0 X : P} (h : X ≠ V0) : ∃ c s : G ax, ∀ Z : P, Z ∈ ray V0 X →
    xc ax (toV ax.O Z - toV ax.O V0) = len ax V0 Z * c ∧
      yc ax (toV ax.O Z - toV ax.O V0) = len ax V0 Z * s := by
  set T := trTo ax V0
  have hT := trTo_isom ax V0
  have hTV := trTo_self ax V0
  set W := T X
  have hWO : W ≠ ax.O := by
    intro e; rw [← hTV] at e; exact h (T.injective e)
  obtain ⟨U, hUr, sU⟩ := segCong_layoff (L := L) ax.hOE (Ne.symm hWO)
  have hUO : U ≠ ax.O := ne_of_mem_ray hUr
  obtain ⟨ρ, hρ, hρE⟩ := exists_rot (L := L) ax.hOx ax.hEx (Ne.symm ax.hOE) hUO sU
  refine ⟨xc ax (rE ax hρ (eV ax)), yc ax (rE ax hρ (eV ax)), fun Z hZ => ?_⟩
  have hZV : Z ≠ V0 := ne_of_mem_ray hZ
  set ℓ := len ax V0 Z
  obtain ⟨hℓ, sℓ⟩ := len_spec ax (Ne.symm hZV)
  -- `T Z` is the point `ρ ℓ`
  have hTZ : T Z ∈ ray ax.O U := by
    have := isom_ray hT hZ
    rw [hTV] at this
    exact sameSidePt_trans (sameSidePt_symm hUr) this
  have hρℓ : ρ (ofV (ℓ : V ax)) ∈ ray ax.O U := by
    have := isom_ray (rot_isom hρ) hℓ
    rwa [rot_fix hρ, hρE] at this
  have s1 : SegCong ax.O (ofV (ℓ : V ax)) ax.O (ρ (ofV (ℓ : V ax))) := by
    have := rot_isom hρ ax.O (ofV (ℓ : V ax)) (Ne.symm (ne_of_mem_ray hℓ))
    rwa [rot_fix hρ] at this
  have s2 : SegCong V0 Z ax.O (T Z) := by
    have := hT V0 Z (Ne.symm hZV); rwa [hTV] at this
  have hOℓ : ax.O ≠ ofV (ℓ : V ax) := Ne.symm (ne_of_mem_ray hℓ)
  have e : T Z = ρ (ofV (ℓ : V ax)) := eq_of_segCong_ray (L := L) hOℓ hTZ hρℓ
    (segCong_trans (L := L) hOℓ (Ne.symm hZV) (Ne.symm (ne_of_mem_ray hTZ))
      (segCong_symm (L := L) (Ne.symm hZV) hOℓ sℓ) s2) s1
  have e2 : toV ax.O Z - toV ax.O V0 = rE ax hρ ℓ := by
    rw [← trTo_apply ax V0 Z]; exact congrArg (toV ax.O) e
  rw [e2]
  exact rot_coords ax hρ ℓ

end Metric

end Pas

end HilbertFoundations
