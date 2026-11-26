import HilbertFoundations.Congruence
import HilbertFoundations.PascalAux8

/-!
# Helper module for `CongruenceClose.lean`: lengths, cosines and sides in co-ordinates

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV, with
rectangular axes `ax` (`Pas.Axes`, from the helper modules of `Pascal.lean`: the field `G ax` of the
segments of the axis `x`, the co-ordinates `xc`, `yc` of the vectors, the lengths `len`, the cosine
`cosA` of an angle). It prepares the properties of the circle (unit `s7.circle_properties`):

* `rot_vec`, `rot_sq`: a rotation about `O` is `(x, y) ↦ (xc - ys, xs + yc)` with `c² + s² = 1`;
* `len_sq_coord`: **the theorem of Pythagoras in co-ordinates**, `len X Y ^ 2 = Δx ^ 2 + Δy ^ 2`;
* `cos_formula`: `cos ∠AOB · |OA| · |OB|` is the scalar product of `A - O` and `B - O`;
* `angCong_of_cosA`: angles with the same cosine are congruent;
* `crs_same`, `crs_opp`: two points lie on the same side (on different sides) of the line `AB` iff
  the determinants `crs A B ·` have the same sign (different signs).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section Coords

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

/-- The first co-ordinate of a point. -/
noncomputable def xco (X : P) : G ax := xc ax (toV ax.O X)

/-- The second co-ordinate of a point. -/
noncomputable def yco (X : P) : G ax := yc ax (toV ax.O X)

theorem coords_mk (p q : G ax) :
    xc ax ((p : V ax) + jE ax (q : V ax)) = p ∧ yc ax ((p : V ax) + jE ax (q : V ax)) = q :=
  coords_of ax p q rfl

theorem coords_E : xco ax ax.E = 1 ∧ yco ax ax.E = 0 := by
  refine coords_of ax 1 0 ?_
  show eV ax = eV ax + jE ax ((0 : G ax) : V ax)
  rw [ZeroMemClass.coe_zero, map_zero, add_zero]

theorem coords_O : xco ax ax.O = 0 ∧ yco ax ax.O = 0 := by
  unfold xco yco
  rw [toV_O]
  exact ⟨xc_zero ax, yc_zero ax⟩

theorem point_ext {X Y : P} (h1 : xco ax X = xco ax Y) (h2 : yco ax X = yco ax Y) : X = Y :=
  vec_ext ax (v := toV ax.O X) (w := toV ax.O Y) h1 h2

/-- The co-ordinates of `J v`. -/
theorem xc_jE (v : V ax) : xc ax (jE ax v) = -yc ax v ∧ yc ax (jE ax v) = xc ax v := by
  refine coords_of ax (-yc ax v) (xc ax v) ?_
  conv_lhs => rw [coords_eq ax v]
  rw [map_add, jE_jE_apply, NegMemClass.coe_neg, add_comm]

/-- The co-ordinates of the reflection in the axis `x`. -/
theorem xc_sE (v : V ax) : xc ax (sE ax v) = xc ax v ∧ yc ax (sE ax v) = -yc ax v := by
  refine coords_of ax (xc ax v) (-yc ax v) ?_
  conv_lhs => rw [coords_eq ax v]
  rw [map_add, sE_X ax (xc ax v).2, sE_Y ax (jE_X ax (yc ax v).2), NegMemClass.coe_neg, map_neg]

/-- **A rotation in co-ordinates.** -/
theorem rot_vec {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) (v : V ax) :
    xc ax (rE ax hρ v) =
        xc ax v * xc ax (rE ax hρ (eV ax)) - yc ax v * yc ax (rE ax hρ (eV ax)) ∧
      yc ax (rE ax hρ v) =
        xc ax v * yc ax (rE ax hρ (eV ax)) + yc ax v * xc ax (rE ax hρ (eV ax)) := by
  have hj : rE ax hρ (jE ax (yc ax v : V ax)) = jE ax (rE ax hρ (yc ax v : V ax)) :=
    (congrArg (fun T : AddMonoid.End (V ax) => T (yc ax v : V ax)) (jE_comm ax hρ).eq).symm
  have e : rE ax hρ v = rE ax hρ (xc ax v : V ax) + jE ax (rE ax hρ (yc ax v : V ax)) := by
    conv_lhs => rw [coords_eq ax v]
    rw [map_add, hj]
  obtain ⟨x1, x2⟩ := rot_coords ax hρ (xc ax v)
  obtain ⟨y1, y2⟩ := rot_coords ax hρ (yc ax v)
  obtain ⟨j1, j2⟩ := xc_jE ax (rE ax hρ (yc ax v : V ax))
  rw [e, xc_add, yc_add, j1, j2, x1, x2, y1, y2]
  exact ⟨by ring, rfl⟩

/-- The inverse rotation has the direction `(c, -s)`. -/
theorem rot_inv_E {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) :
    xc ax (rE ax ((rot (L := L) ax.O).inv_mem hρ) (eV ax)) = xc ax (rE ax hρ (eV ax)) ∧
      yc ax (rE ax ((rot (L := L) ax.O).inv_mem hρ) (eV ax)) = -yc ax (rE ax hρ (eV ax)) := by
  have h : sE ax (rE ax hρ (sE ax (eV ax))) = rE ax ((rot (L := L) ax.O).inv_mem hρ) (eV ax) :=
    congrArg (fun T : AddMonoid.End (V ax) => T (eV ax)) (sE_conj ax hρ)
  rw [sE_X ax (eV_mem ax)] at h
  rw [← h]
  exact xc_sE ax _

/-- **The direction of a rotation is a unit vector.** -/
theorem rot_sq {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) :
    xc ax (rE ax hρ (eV ax)) ^ 2 + yc ax (rE ax hρ (eV ax)) ^ 2 = 1 := by
  have hinv := (rot (L := L) ax.O).inv_mem hρ
  have h1 : rE ax hinv (rE ax hρ (eV ax)) = eV ax :=
    congrArg (toV ax.O) (perm_inv_apply ρ (ofV (eV ax)))
  obtain ⟨r1, -⟩ := rot_vec ax hinv (rE ax hρ (eV ax))
  obtain ⟨i1, i2⟩ := rot_inv_E ax hρ
  have hE : xc ax (eV ax) = 1 := (coords_E ax).1
  rw [h1, i1, i2, hE] at r1
  linear_combination (-1 : G ax) * r1

/-- Pythagoras for a segment from the origin. -/
theorem len_sq_origin {W : P} (hW : W ≠ ax.O) :
    len ax ax.O W ^ 2 = xco ax W ^ 2 + yco ax W ^ 2 := by
  obtain ⟨hℓ, sℓ⟩ := len_spec ax (Ne.symm hW)
  have hℓO : ofV (len ax ax.O W : V ax) ≠ ax.O := ne_of_mem_ray hℓ
  obtain ⟨ρ, hρ, hρW⟩ := exists_rot (L := L) ax.hOx (X := ofV (len ax ax.O W : V ax))
    (len ax ax.O W).2 hℓO hW
    (segCong_symm (L := L) (Ne.symm hW) (Ne.symm hℓO) sℓ)
  have e : toV ax.O W = rE ax hρ (len ax ax.O W : V ax) := congrArg (toV ax.O) hρW.symm
  obtain ⟨r1, r2⟩ := rot_coords ax hρ (len ax ax.O W)
  have hs := rot_sq ax hρ
  unfold xco yco
  rw [e, r1, r2]
  linear_combination (-(len ax ax.O W ^ 2)) * hs

theorem px_trTo (X Z : P) : xco ax (trTo ax X Z) = xco ax Z - xco ax X := by
  unfold xco; rw [trTo_apply, xc_sub]

theorem py_trTo (X Z : P) : yco ax (trTo ax X Z) = yco ax Z - yco ax X := by
  unfold yco; rw [trTo_apply, yc_sub]

theorem len_trTo (X Y : P) : len ax ax.O (trTo ax X Y) = len ax X Y := by
  have := len_isom ax (trTo_isom ax X) X Y
  rwa [trTo_self] at this

/-- **The theorem of Pythagoras in co-ordinates.** -/
theorem len_sq_coord (X Y : P) :
    len ax X Y ^ 2 = (xco ax Y - xco ax X) ^ 2 + (yco ax Y - yco ax X) ^ 2 := by
  by_cases h : X = Y
  · subst h; simp [len]
  · have hW : trTo ax X Y ≠ ax.O := fun e =>
      h ((trTo ax X).injective ((trTo_self ax X).trans e.symm))
    rw [← len_trTo ax X Y, len_sq_origin ax hW, px_trTo, py_trTo]

theorem F_not_mem_x : ax.F ∉ ax.x := fun h => ax.hOF (ax.hxy _ h ax.hFy).symm

/-- The first co-ordinate of a point on the side of `F`, by the cosine of its angle with the
positive half-axis. -/
theorem cos_x_same {A B : P} (hA : A ∈ ray ax.O ax.E) (hB : SameSide ax.x B ax.F) :
    xco ax B = len ax ax.O B * cosA ax A ax.O B := by
  have hAO : A ≠ ax.O := ne_of_mem_ray hA
  have hAx : A ∈ ax.x := mem_of_collinear (collinear_of_mem_ray hA) ax.hOE ax.hOx ax.hEx
  have hn : ¬Collinear (Line := L) A ax.O B := fun hc =>
    hB.1 (mem_of_collinear hc hAO hAx ax.hOx)
  obtain ⟨hU, sU, aU⟩ := stdPt_spec ax hn
  have hBO : B ≠ ax.O := fun e => hB.1 (e ▸ ax.hOx)
  have a2 : AngCong A ax.O B ax.E ax.O B := angCong_rays hn hn (angCong_refl (Line := L) hn)
    (mem_ray_self' (L := L) hAO) (mem_ray_self' (L := L) hBO) (mem_ray_comm hA)
    (mem_ray_self' (L := L) hBO)
  have r := (pf (L := L) ax.hOE).layoff_unique Set.univ rfl A ax.O B ax.x ax.O ax.E B
    (stdPt ax A ax.O B) hn (lineIn_univ _) ax.hOx ax.hEx (Ne.symm ax.hOE) trivial trivial
    (OrderCore.sameSide_trans hB (OrderCore.sameSide_symm hU)) a2 aU
  have hBr : B ∈ ray ax.O (stdPt ax A ax.O B) := by
    rw [← r]; exact mem_ray_self' (L := L) hBO
  exact std_ray_coords ax hn hBr

/-- The same for a point on either side of the axis. -/
theorem cos_x {A B : P} (hA : A ∈ ray ax.O ax.E) (hB : B ∉ ax.x) :
    xco ax B = len ax ax.O B * cosA ax A ax.O B := by
  rcases OrderCore.sameSide_or_opp hB (F_not_mem_x ax) with hs | ho
  · exact cos_x_same ax hA hs
  · have hσ := refl_isom (P := P) ax.x
    have hAO : A ≠ ax.O := ne_of_mem_ray hA
    have hAx : A ∈ ax.x := mem_of_collinear (collinear_of_mem_ray hA) ax.hOE ax.hOx ax.hEx
    have hn : ¬Collinear (Line := L) A ax.O B := fun hc =>
      hB (mem_of_collinear hc hAO hAx ax.hOx)
    have hB' : SameSide ax.x (refl ax.x B) ax.F :=
      OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm (refl_opp hB)) ho
    have hn' : ¬Collinear (Line := L) A ax.O (refl ax.x B) := fun hc =>
      hB'.1 (mem_of_collinear hc hAO hAx ax.hOx)
    have h1 := cos_x_same ax hA hB'
    have e1 : xco ax (refl ax.x B) = xco ax B := (xc_sE ax (toV ax.O B)).1
    have e2 : len ax ax.O (refl ax.x B) = len ax ax.O B := by
      have := len_isom ax hσ ax.O B; rwa [refl_fix ax.hOx] at this
    have e3 : cosA ax A ax.O B = cosA ax A ax.O (refl ax.x B) := by
      have := isom_angCong ax hσ hn
      rw [refl_fix hAx, refl_fix ax.hOx] at this
      exact cosA_congr ax hn hn' this
    rw [← e1, h1, e2, e3]

/-- The scalar product formula at the origin. -/
theorem cos_O {A B : P} (hn : ¬Collinear (Line := L) A ax.O B) :
    cosA ax A ax.O B * (len ax ax.O A * len ax ax.O B) =
      xco ax A * xco ax B + yco ax A * yco ax B := by
  obtain ⟨hAO, hBO, -⟩ := nc_ne ax hn
  obtain ⟨hℓ, sℓ⟩ := len_spec ax (Ne.symm hAO)
  have hℓO : ofV (len ax ax.O A : V ax) ≠ ax.O := ne_of_mem_ray hℓ
  obtain ⟨ρ, hρ, hρA⟩ := exists_rot (L := L) ax.hOx (X := ofV (len ax ax.O A : V ax))
    (len ax ax.O A).2 hℓO hAO
    (segCong_symm (L := L) (Ne.symm hAO) (Ne.symm hℓO) sℓ)
  have hinv := (rot (L := L) ax.O).inv_mem hρ
  have hi := rot_isom hinv
  have eA : ρ⁻¹ A = ofV (len ax ax.O A : V ax) := by
    have h := perm_inv_apply ρ (ofV (len ax ax.O A : V ax))
    rwa [hρA] at h
  have ang := isom_angCong ax hi hn
  rw [eA, rot_fix hinv] at ang
  have hn2 : ¬Collinear (Line := L) (ofV (len ax ax.O A : V ax)) ax.O (ρ⁻¹ B) := by
    intro hc
    apply hn
    refine (isom_collinear_iff hi).1 ?_
    rw [eA, rot_fix hinv]; exact hc
  have ec := cosA_congr ax hn hn2 ang
  have hB₂x : ρ⁻¹ B ∉ ax.x := fun h => hn2 ⟨ax.x, (len ax ax.O A).2, ax.hOx, h⟩
  have h1 := cos_x ax (A := ofV (len ax ax.O A : V ax)) hℓ hB₂x
  have e2 : len ax ax.O (ρ⁻¹ B) = len ax ax.O B := by
    have := len_isom ax hi ax.O B; rwa [rot_fix hinv] at this
  obtain ⟨c1, c2⟩ := rot_coords ax hρ (len ax ax.O A)
  have eAv : toV ax.O A = rE ax hρ (len ax ax.O A : V ax) := congrArg (toV ax.O) hρA.symm
  obtain ⟨v1, -⟩ := rot_vec ax hinv (toV ax.O B)
  obtain ⟨i1, i2⟩ := rot_inv_E ax hρ
  rw [i1, i2] at v1
  have pB₂ : xco ax (ρ⁻¹ B) = xco ax B * xc ax (rE ax hρ (eV ax)) -
      yco ax B * -yc ax (rE ax hρ (eV ax)) := v1
  have pA1 : xco ax A = len ax ax.O A * xc ax (rE ax hρ (eV ax)) := by
    unfold xco; rw [eAv]; exact c1
  have pA2 : yco ax A = len ax ax.O A * yc ax (rE ax hρ (eV ax)) := by
    unfold yco; rw [eAv]; exact c2
  rw [pB₂, e2] at h1
  rw [ec, pA1, pA2]
  linear_combination (-(len ax ax.O A)) * h1

/-- **The scalar product formula**: `cos ∠AOB · |OA| · |OB| = (A - O) · (B - O)`. -/
theorem cos_formula {A O' B : P} (hn : ¬Collinear (Line := L) A O' B) :
    cosA ax A O' B * (len ax O' A * len ax O' B) =
      (xco ax A - xco ax O') * (xco ax B - xco ax O') +
        (yco ax A - yco ax O') * (yco ax B - yco ax O') := by
  have hT := trTo_isom ax O'
  have hn' : ¬Collinear (Line := L) (trTo ax O' A) ax.O (trTo ax O' B) := by
    intro hc
    apply hn
    refine (isom_collinear_iff hT).1 ?_
    rw [trTo_self]; exact hc
  have ang := isom_angCong ax hT hn
  rw [trTo_self] at ang
  have h := cos_O ax hn'
  rw [← cosA_congr ax hn hn' ang, len_trTo, len_trTo, px_trTo, px_trTo, py_trTo, py_trTo] at h
  exact h

/-- **Angles with the same cosine are congruent.** -/
theorem angCong_of_cosA {A O₁ B A' O₂ B' : P} (h : ¬Collinear (Line := L) A O₁ B)
    (h' : ¬Collinear (Line := L) A' O₂ B') (hc : cosA ax A O₁ B = cosA ax A' O₂ B') :
    AngCong A O₁ B A' O₂ B' := by
  obtain ⟨hU, sU, aU⟩ := stdPt_spec ax h
  obtain ⟨hU', sU', aU'⟩ := stdPt_spec ax h'
  have hUO : stdPt ax A O₁ B ≠ ax.O := fun e => hU.1 (e ▸ ax.hOx)
  have hU'O : stdPt ax A' O₂ B' ≠ ax.O := fun e => hU'.1 (e ▸ ax.hOx)
  have hUE : ax.E ≠ stdPt ax A O₁ B := fun e => hU.1 (e ▸ ax.hEx)
  have hU'E : ax.E ≠ stdPt ax A' O₂ B' := fun e => hU'.1 (e ▸ ax.hEx)
  have lU : len ax ax.O (stdPt ax A O₁ B) = 1 := by
    rw [← len_E ax]
    exact (len_eq_iff ax (Ne.symm hUO) ax.hOE).2 (segCong_symm (L := L) ax.hOE (Ne.symm hUO) sU)
  have lU' : len ax ax.O (stdPt ax A' O₂ B') = 1 := by
    rw [← len_E ax]
    exact (len_eq_iff ax (Ne.symm hU'O) ax.hOE).2
      (segCong_symm (L := L) ax.hOE (Ne.symm hU'O) sU')
  have q := len_sq_origin ax hUO
  have q' := len_sq_origin ax hU'O
  rw [lU] at q
  rw [lU'] at q'
  have hx : xco ax (stdPt ax A O₁ B) = xco ax (stdPt ax A' O₂ B') := hc
  obtain ⟨hE1, hE2⟩ := coords_E ax
  have dd : len ax ax.E (stdPt ax A O₁ B) ^ 2 = len ax ax.E (stdPt ax A' O₂ B') ^ 2 := by
    rw [len_sq_coord, len_sq_coord, hE1, hE2]
    linear_combination -q + q' - 2 * hx
  have dl : len ax ax.E (stdPt ax A O₁ B) = len ax ax.E (stdPt ax A' O₂ B') :=
    (pow_left_inj₀ (len_pos ax hUE).le (len_pos ax hU'E).le two_ne_zero).1 dd
  have sE' : SegCong ax.E (stdPt ax A O₁ B) ax.E (stdPt ax A' O₂ B') :=
    (len_eq_iff ax hUE hU'E).1 dl
  have sO' : SegCong ax.O (stdPt ax A O₁ B) ax.O (stdPt ax A' O₂ B') :=
    segCong_trans (L := L) (Ne.symm hUO) ax.hOE (Ne.symm hU'O)
      (segCong_symm (L := L) ax.hOE (Ne.symm hUO) sU) sU'
  have hss : SameSide (line (Line := L) ax.O ax.E ax.hOE) (stdPt ax A O₁ B)
      (stdPt ax A' O₂ B') := by
    rw [← eq_line ax.hOE ax.hOx ax.hEx]
    exact OrderCore.sameSide_trans hU (OrderCore.sameSide_symm hU')
  have e : stdPt ax A O₁ B = stdPt ax A' O₂ B' :=
    eq_of_sameSide_equidistant (L := L) ax.hOE hss sO' sE'
  have nEU : ¬Collinear (Line := L) ax.E ax.O (stdPt ax A O₁ B) := fun hc' => hU.1
    (mem_of_collinear hc' (Ne.symm ax.hOE) ax.hEx ax.hOx)
  rw [← e] at aU'
  exact angCong_trans h nEU h' aU (angCong_symm h' nEU aU')

/-! ### The sides of a line -/

/-- The determinant of `B - A` and `Z - A`. -/
noncomputable def crs (A B Z : P) : G ax :=
  (xco ax B - xco ax A) * (yco ax Z - yco ax A) - (yco ax B - yco ax A) * (xco ax Z - xco ax A)

theorem mem_line_iff_crs {A B : P} (hAB : A ≠ B) {l : L} (hA : A ∈ l) (hB : B ∈ l) (Z : P) :
    Z ∈ l ↔ crs ax A B Z = 0 := by
  rw [mem_line_iff_cross ax hAB hA hB Z]
  unfold crs cross cr xco yco
  rw [xc_sub, yc_sub, xc_sub, yc_sub]

/-- **Betweenness in co-ordinates**: if `C` lies between `X` and `D`, then `D - C` is a positive
multiple of `C - X`. -/
theorem between_coord {X C D : P} (h : Between X C D) :
    ∃ t : G ax, 0 < t ∧ xco ax D - xco ax C = t * (xco ax C - xco ax X) ∧
      yco ax D - yco ax C = t * (yco ax C - yco ax X) := by
  have hXC : X ≠ C := ne12_of_between (Line := L) h
  have hDC : D ≠ C := (ne23_of_between (Line := L) h).symm
  obtain ⟨hb, -⟩ := (ht_eq_iff (L := L) hXC).1 rfl
  have hX'r : ht (L := L) C X ∈ ray C D := mem_ray_of_between_between h hb
  obtain ⟨c, s, hcs⟩ := ray_coords ax hDC
  obtain ⟨d1, d2⟩ := hcs D (mem_ray_self' (L := L) hDC)
  obtain ⟨x1, x2⟩ := hcs _ hX'r
  rw [ht_vec ax C X, xc_sub, xc_sub, xc_add] at x1
  rw [ht_vec ax C X, yc_sub, yc_sub, yc_add] at x2
  rw [xc_sub] at d1
  rw [yc_sub] at d2
  have l1 := len_pos ax (ne_of_mem_ray hX'r).symm
  have l2 := len_pos ax hDC.symm
  have hdiv : len ax C D / len ax C (ht (L := L) C X) * len ax C (ht (L := L) C X) =
      len ax C D := div_mul_cancel₀ _ l1.ne'
  refine ⟨len ax C D / len ax C (ht (L := L) C X), div_pos l2 l1, ?_, ?_⟩
  · have e1 : xco ax C - xco ax X = len ax C (ht (L := L) C X) * c := by
      unfold xco; linear_combination x1
    show xc ax (toV ax.O D) - xc ax (toV ax.O C) = _
    rw [d1, e1, ← mul_assoc, hdiv]
  · have e2 : yco ax C - yco ax X = len ax C (ht (L := L) C X) * s := by
      unfold yco; linear_combination x2
    show yc ax (toV ax.O D) - yc ax (toV ax.O C) = _
    rw [d2, e2, ← mul_assoc, hdiv]

theorem crs_between (A B : P) {C X D : P} (h : Between C X D) :
    ∃ t : G ax, 0 < t ∧ crs ax A B D - crs ax A B X = t * (crs ax A B X - crs ax A B C) := by
  obtain ⟨t, ht, e1, e2⟩ := between_coord ax h
  refine ⟨t, ht, ?_⟩
  unfold crs
  linear_combination (xco ax B - xco ax A) * e2 - (yco ax B - yco ax A) * e1

/-- Points on different sides of the line `AB` have determinants of different signs. -/
theorem crs_opp {A B C D : P} (hAB : A ≠ B) {l : L} (hA : A ∈ l) (hB : B ∈ l)
    (ho : OppositeSides l C D) : crs ax A B C * crs ax A B D < 0 := by
  obtain ⟨hC', -, X, hX, hb⟩ := ho
  obtain ⟨t, ht, e⟩ := crs_between ax A B hb
  rw [(mem_line_iff_crs ax hAB hA hB X).1 hX] at e
  have hC0 : crs ax A B C ≠ 0 := fun e0 => hC' ((mem_line_iff_crs ax hAB hA hB C).2 e0)
  have hD : crs ax A B D = -(t * crs ax A B C) := by linear_combination e
  rw [hD]
  have := mul_pos ht (mul_self_pos.2 hC0)
  linarith

/-- Points on the same side of the line `AB` have determinants of the same sign. -/
theorem crs_same {A B C D : P} (hAB : A ≠ B) {l : L} (hA : A ∈ l) (hB : B ∈ l)
    (hs : SameSide l C D) : 0 < crs ax A B C * crs ax A B D := by
  have hCA : C ≠ A := fun e => hs.1 (e ▸ hA)
  obtain ⟨C', hC'⟩ := exists_beyond (Line := L) hCA
  have o1 : OppositeSides l C C' := opp_of_between_mem hA hs.1 hC'
  have o2 : OppositeSides l D C' := OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hs) o1
  have p1 := crs_opp ax hAB hA hB o1
  have p2 := crs_opp ax hAB hA hB o2
  have h := mul_pos_of_neg_of_neg p1 p2
  by_contra hle
  have := mul_nonneg (neg_nonneg.2 (not_lt.1 hle)) (mul_self_nonneg (crs ax A B C'))
  linarith

end Coords

/-! ### The algebra of the inscribed angles -/

section Algebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Two angles with cosines `k = u/n`, `k' = u'/n'` (`n² = u² + s²`, `n'² = u'² + s'²`), with
`u s' = u' s` and sines `s`, `s'` of the same sign, have the same cosine. -/
theorem cos_alg_pos {u s n u' s' n' k k' : K} (hn : 0 < n) (hn' : 0 < n')
    (e : n ^ 2 = u ^ 2 + s ^ 2) (e' : n' ^ 2 = u' ^ 2 + s' ^ 2) (hc : u * s' = u' * s)
    (hk : k * n = u) (hk' : k' * n' = u') (hss : 0 < s * s') : k = k' := by
  have key : (u * n') ^ 2 = (u' * n) ^ 2 := by
    linear_combination u ^ 2 * e' - u' ^ 2 * e + (u * s' + u' * s) * hc
  have huu : 0 ≤ u * u' := by
    have h1 : 0 ≤ (u * u') * (s * s') := by
      have : (u * u') * (s * s') = (u' * s) ^ 2 := by linear_combination (u' * s) * hc
      rw [this]; positivity
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) hss
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 key with h | h
  · have : k * (n * n') = k' * (n * n') := by linear_combination n' * hk - n * hk' + h
    exact mul_right_cancel₀ (ne_of_gt (mul_pos hn hn')) this
  · have h4 : u * u' * n' = -(u' * u' * n) := by linear_combination u' * h
    have h5 := mul_nonneg huu hn'.le
    have hu'0 : u' = 0 := by
      by_contra hne
      have := mul_pos (mul_self_pos.2 hne) hn
      linarith
    have hu0 : u = 0 := by
      have : u * n' = 0 := by rw [h, hu'0]; ring
      exact (mul_eq_zero.1 this).resolve_right hn'.ne'
    have hk0 : k = 0 := (mul_eq_zero.1 (hk.trans hu0)).resolve_right hn.ne'
    have hk'0 : k' = 0 := (mul_eq_zero.1 (hk'.trans hu'0)).resolve_right hn'.ne'
    rw [hk0, hk'0]

/-- The same with sines of different signs: the cosines are opposite. -/
theorem cos_alg_neg {u s n u' s' n' k k' : K} (hn : 0 < n) (hn' : 0 < n')
    (e : n ^ 2 = u ^ 2 + s ^ 2) (e' : n' ^ 2 = u' ^ 2 + s' ^ 2) (hc : u * s' = u' * s)
    (hk : k * n = u) (hk' : k' * n' = u') (hss : s * s' < 0) : k = -k' :=
  cos_alg_pos (u' := -u') (s' := -s') hn hn' e (by rw [e']; ring) (by linear_combination -hc) hk
    (by rw [← hk']; ring) (by linarith)

end Algebra

end Pas

end HilbertFoundations
