import HilbertFoundations.PascalAux7

/-!
# Helper module for `Pascal.lean`: right triangles and Hilbert's symbol `αc`

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV, with
rectangular axes `ax`.

* **Perpendiculars to the axis** (`rightAngle_iff`): for `p ≠ O` on `x` and `Z` off `x`, the angle
  `∠OpZ` is right iff `Z - p` lies on `y`.
* **The standard half-ray of an angle** (`stdPt`): the angle `α` laid off at `O` on the half-ray
  `OE` towards `F`, with the point `U_α` at the unit distance; its first co-ordinate is the "cosine"
  `cosA α`. Congruent angles have the same standard point.
* **Right triangles** (`base_eq`): if `∠XYZ` is right, then `XY = XZ · cosA ∠YXZ` (lengths in the
  field of segments). For an acute angle `cosA α > 0` (`cosA_pos`), and for every length `c` there is
  a right triangle with hypotenuse `c` and base angle `α` (`exists_right_triangle`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section RightTriangles

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- A right angle stays right when a point of a side moves on its half-ray. -/
theorem rightAngle_ray_left {A O B A' : P} (h : IsRightAngle (L := L) A O B) (hA : A' ∈ ray O A) :
    IsRightAngle (L := L) A' O B := by
  obtain ⟨hn, C, hb, hc⟩ := h
  obtain ⟨-, hBO, -⟩ := nc_ne ax hn
  have hn' : ¬Collinear (Line := L) A' O B :=
    not_collinear_of_mem_rays (L := L) hn hA (mem_ray_self' (L := L) hBO)
  have hBOC : ¬Collinear (Line := L) B O C := not_collinear_swap (not_collinear_of_between hn hb)
  obtain ⟨-, hCO, -⟩ := nc_ne ax (not_collinear_swap hBOC)
  refine ⟨hn', C, between_of_between_mem_ray hb (mem_ray_comm hA), ?_⟩
  exact angCong_rays hn hBOC hc hA (mem_ray_self' (L := L) hBO) (mem_ray_self' (L := L) hBO)
    (mem_ray_self' (L := L) (nc_ne ax hBOC).2.1)

theorem rightAngle_ray_right {A O B B' : P} (h : IsRightAngle (L := L) A O B) (hB : B' ∈ ray O B) :
    IsRightAngle (L := L) A O B' := by
  obtain ⟨hn, C, hb, hc⟩ := h
  obtain ⟨hAO, hBO, -⟩ := nc_ne ax hn
  have hn' : ¬Collinear (Line := L) A O B' :=
    not_collinear_of_mem_rays (L := L) hn (mem_ray_self' (L := L) hAO) hB
  have hBOC : ¬Collinear (Line := L) B O C := not_collinear_swap (not_collinear_of_between hn hb)
  refine ⟨hn', C, hb, ?_⟩
  exact angCong_rays hn hBOC hc (mem_ray_self' (L := L) hAO) hB hB
    (mem_ray_self' (L := L) (nc_ne ax hBOC).2.1)

theorem ht_E_mem : ht (L := L) ax.O ax.E ∈ ax.x :=
  mem_right_of_between ((ht_eq_iff (L := L) (Ne.symm ax.hOE)).1 rfl).1 ax.hEx ax.hOx

theorem ht_F_mem : ht (L := L) ax.O ax.F ∈ ax.y :=
  mem_right_of_between ((ht_eq_iff (L := L) (Ne.symm ax.hOF)).1 rfl).1 ax.hFy ax.hOy

/-- A point of a line through `O` other than `O` lies on the half-ray of `X` or of its symmetric. -/
theorem ray_or_ray {l : L} (hO : ax.O ∈ l) {X Z : P} (hX : X ∈ l) (hXO : X ≠ ax.O) (hZ : Z ∈ l)
    (hZO : Z ≠ ax.O) : Z ∈ ray ax.O X ∨ Z ∈ ray ax.O (ht (L := L) ax.O X) := by
  rcases mem_ray_or_between (L := L) (collinear_of_mem hO hX hZ) hXO hZO with h | h
  · exact Or.inl h
  · exact Or.inr (mem_ray_of_between_between ((ht_eq_iff (L := L) hXO).1 rfl).1 h)

/-- **The axes are perpendicular**: any points `p`, `q` of `x`, `y` other than `O` form a right
angle at `O`. -/
theorem axes_right' {p q : P} (hp : p ∈ ax.x) (hpO : p ≠ ax.O) (hq : q ∈ ax.y) (hqO : q ≠ ax.O) :
    IsRightAngle (L := L) p ax.O q := by
  have r0 := axes_right ax
  have hσy := refl_isom (P := P) ax.y
  have hσx := refl_isom (P := P) ax.x
  have r1 : IsRightAngle (L := L) (ht (L := L) ax.O ax.E) ax.O ax.F := by
    have := isom_rightAngle ax hσy r0
    rwa [ax.refly_x _ ax.hEx, refl_fix ax.hOy, refl_fix ax.hFy] at this
  have rq : ∀ {e : P}, e ∈ ax.x → IsRightAngle (L := L) e ax.O ax.F →
      IsRightAngle (L := L) e ax.O q := by
    intro e hex he
    have he' : IsRightAngle (L := L) e ax.O (ht (L := L) ax.O ax.F) := by
      have := isom_rightAngle ax hσx he
      rwa [refl_fix hex, refl_fix ax.hOx, ax.reflx_y _ ax.hFy] at this
    rcases ray_or_ray ax ax.hOy ax.hFy (Ne.symm ax.hOF) hq hqO with h | h
    · exact rightAngle_ray_right ax he h
    · exact rightAngle_ray_right ax he' h
  rcases ray_or_ray ax ax.hOx ax.hEx (Ne.symm ax.hOE) hp hpO with h | h
  · exact rq hp (rightAngle_ray_left ax r0 h)
  · exact rq hp (rightAngle_ray_left ax r1 h)

theorem tr_vec (p X : P) : toV ax.O (tr (L := L) ax.O p X) = toV ax.O p + toV ax.O X :=
  (vadd_def (L := L) (toV ax.O p) (toV ax.O X)).symm

theorem toV_O : toV ax.O ax.O = (0 : V ax) := (vzero_def (L := L) ax.O).symm

theorem len_E : len ax ax.O ax.E = 1 := len_of_pos ax (posG_one ax)

/-- **Perpendiculars to the axis `x`**: for `p ≠ O` on `x` and `Z` off `x`, `∠OpZ` is a right angle
iff `Z - p` lies on `y`. -/
theorem rightAngle_iff {p Z : P} (hp : p ∈ ax.x) (hpO : p ≠ ax.O) (hZ : Z ∉ ax.x) :
    IsRightAngle (L := L) ax.O p Z ↔ toV ax.O Z - toV ax.O p ∈ Ys ax := by
  set T := tr (L := L) ax.O p
  have hT : T ∈ isom (L := L) := transl_isom (tr_mem _ _)
  have hp' : toV ax.O p ∈ Xs ax := hp
  have hnp : -toV ax.O p ∈ Xs ax := (Xs ax).neg_mem hp'
  have hnp0 : -toV ax.O p ≠ 0 := fun h => hpO (by
    have := congrArg ofV (neg_eq_zero.1 h); rwa [ofV_zero (L := L)] at this)
  have T1 : T (ofV (-toV ax.O p)) = ax.O := by
    apply ofV_injective (O := ax.O)
    show toV ax.O (T (ofV (-toV ax.O p))) = toV ax.O ax.O
    rw [tr_vec, toV_ofV, add_neg_cancel, toV_O]
  have T2 : T ax.O = p := tr_apply_O ax.O p
  have back : ∀ q : V ax, q ∈ Ys ax → q ≠ 0 → IsRightAngle (L := L) ax.O p (T (ofV q)) := by
    intro q hq hq0
    have r := axes_right' ax hnp (ofV_ne_O ax hnp0) hq (ofV_ne_O ax hq0)
    have := isom_rightAngle ax hT r
    rwa [T1, T2] at this
  constructor
  · intro h
    -- choose `q₁ = ±F` on the side of `Z`
    obtain ⟨q1, hq1y, hq10, hside⟩ : ∃ q1 : V ax, q1 ∈ Ys ax ∧ q1 ≠ 0 ∧
        SameSide ax.x (ofV q1) Z := by
      have hFx : ax.F ∉ ax.x := fun h => ax.hOF (ax.hxy _ h ax.hFy).symm
      rcases OrderCore.sameSide_or_opp hFx hZ with hs | ho
      · exact ⟨toV ax.O ax.F, ax.hFy, fun e => ax.hOF (by
          have := congrArg ofV e; rw [ofV_zero (L := L)] at this; exact this.symm), hs⟩
      · refine ⟨toV ax.O (ht (L := L) ax.O ax.F), ht_F_mem ax, fun e => ?_, ?_⟩
        · have := congrArg ofV e; rw [ofV_zero (L := L)] at this
          exact htp_ne (Ne.symm ax.hOF) this
        · have hb := ((ht_eq_iff (L := L) (Ne.symm ax.hOF)).1 rfl).1
          have o := opp_of_between_mem ax.hOx hFx hb
          exact OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm o) ho
    set W1 := T (ofV q1)
    have hW1 : toV ax.O W1 - toV ax.O p = q1 := by
      show toV ax.O (T (ofV q1)) - toV ax.O p = q1
      rw [tr_vec]; abel
    have rW := back q1 hq1y hq10
    have hq1x : ofV q1 ∉ ax.x := fun h => hq10 (X_inf_Y ax h hq1y)
    have sW : SameSide ax.x W1 Z := by
      have : SameSide ax.x W1 (ofV q1) := sameSide_of_sub_mem ax ax.hOx hq1x (by
        show toV ax.O (T (ofV q1)) - q1 ∈ Xs ax
        rw [tr_vec]; simp only [toV_ofV, add_sub_cancel_right]; exact hp')
      exact OrderCore.sameSide_trans this hside
    have nW : ¬Collinear (Line := L) ax.O p W1 := rW.1
    have a := theorem15 rW h
    have r := (pf (L := L) ax.hOE).layoff_unique Set.univ rfl ax.O p W1 ax.x p ax.O W1 Z nW
      (lineIn_univ _) hp ax.hOx (Ne.symm hpO) trivial trivial sW (angCong_refl (Line := L) nW) a
    have hZr : Z ∈ ray p W1 := by rw [r]; exact mem_ray_self' (L := L) (fun e => hZ (e ▸ hp))
    obtain ⟨k, hpk, hk⟩ := exists_parEq (P := P) ax.y p
    have hW1k : W1 ∈ k := (mem_line_iff_sub ax.hOy (parEq_symm hk) hpk W1).2 (by rw [hW1]; exact hq1y)
    have hpW1 : p ≠ W1 := fun e =>
      hq10 (hW1.symm.trans (sub_eq_zero.2 (congrArg (toV ax.O) e.symm)))
    have hZk : Z ∈ k := mem_of_collinear (collinear_of_mem_ray hZr) hpW1 hpk hW1k
    exact (mem_line_iff_sub ax.hOy (parEq_symm hk) hpk Z).1 hZk
  · intro h
    have hq0 : toV ax.O Z - toV ax.O p ≠ 0 := fun e => hZ (by
      have h5 : toV ax.O Z = toV ax.O p := sub_eq_zero.1 e
      have : Z = p := h5
      rw [this]; exact hp)
    have := back _ h hq0
    have e : T (ofV (toV ax.O Z - toV ax.O p)) = Z := by
      apply ofV_injective (O := ax.O)
      show toV ax.O (T (ofV (toV ax.O Z - toV ax.O p))) = toV ax.O Z
      rw [tr_vec]; simp only [toV_ofV]; abel
    rwa [e] at this

/-- The standard point of an angle: laid off at `O` from the half-ray `OE` towards `F`, at the unit
distance. -/
theorem exists_stdPt {A O' B : P} (h : ¬Collinear (Line := L) A O' B) :
    ∃! U : P, SameSide ax.x U ax.F ∧ SegCong ax.O ax.E ax.O U ∧ AngCong A O' B ax.E ax.O U := by
  have hFx : ax.F ∉ ax.x := fun h => ax.hOF (ax.hxy _ h ax.hFy).symm
  let F' := pf (L := L) ax.hOE
  obtain ⟨Z1, -, hZ1, a1⟩ := F'.layoff Set.univ rfl A O' B ax.x ax.O ax.E ax.F h (lineIn_univ _)
    ax.hOx ax.hEx (Ne.symm ax.hOE) trivial hFx
  have hZ1O : Z1 ≠ ax.O := fun e => hZ1.1 (e ▸ ax.hOx)
  obtain ⟨U, hUr, sU⟩ := segCong_layoff (L := L) ax.hOE (Ne.symm hZ1O)
  have nEZ1 : ¬Collinear (Line := L) ax.E ax.O Z1 := fun hc => hZ1.1
    (mem_of_collinear hc (Ne.symm ax.hOE) ax.hEx ax.hOx)
  have nEU : ¬Collinear (Line := L) ax.E ax.O U := not_collinear_of_mem_rays (L := L) nEZ1
    (mem_ray_self' (L := L) (Ne.symm ax.hOE)) hUr
  have hU : SameSide ax.x U ax.F := OrderCore.sameSide_trans
    (OrderCore.sameSide_symm (sameSide_of_ray ax.hOx hZ1.1 hUr)) hZ1
  obtain ⟨hAO, hBO, -⟩ := nc_ne ax h
  refine ⟨U, ⟨hU, sU, angCong_rays h nEZ1 a1 (mem_ray_self' (L := L) hAO)
    (mem_ray_self' (L := L) hBO) (mem_ray_self' (L := L) (Ne.symm ax.hOE)) hUr⟩, ?_⟩
  rintro U' ⟨hU', sU', aU'⟩
  have nEU' : ¬Collinear (Line := L) ax.E ax.O U' := fun hc => hU'.1
    (mem_of_collinear hc (Ne.symm ax.hOE) ax.hEx ax.hOx)
  have aU := angCong_rays h nEZ1 a1 (mem_ray_self' (L := L) hAO) (mem_ray_self' (L := L) hBO)
    (mem_ray_self' (L := L) (Ne.symm ax.hOE)) hUr
  have r := F'.layoff_unique Set.univ rfl A O' B ax.x ax.O ax.E U' U h (lineIn_univ _) ax.hOx
    ax.hEx (Ne.symm ax.hOE) trivial trivial (OrderCore.sameSide_trans hU' (OrderCore.sameSide_symm hU))
    aU' aU
  have hU'r : U' ∈ ray ax.O U := by rw [← r]; exact mem_ray_self' (L := L) (nc_ne ax nEU').2.1
  exact eq_of_segCong_ray (L := L) ax.hOE hU'r (mem_ray_self' (L := L) (nc_ne ax nEU).2.1) sU' sU

/-- The **standard point** `U_α` of the angle `α = ∠AO'B` (the identity of `O` for degenerate
triples). -/
noncomputable def stdPt (A O' B : P) : P := by
  classical
  exact if h : ¬Collinear (Line := L) A O' B then Classical.choose (exists_stdPt ax h) else ax.O

theorem stdPt_spec {A O' B : P} (h : ¬Collinear (Line := L) A O' B) :
    SameSide ax.x (stdPt ax A O' B) ax.F ∧ SegCong ax.O ax.E ax.O (stdPt ax A O' B) ∧
      AngCong A O' B ax.E ax.O (stdPt ax A O' B) := by
  simp only [stdPt, h, not_false_eq_true, ↓reduceDIte]
  exact (Classical.choose_spec (exists_stdPt ax h)).1

theorem stdPt_eq {A O' B U : P} (h : ¬Collinear (Line := L) A O' B) (hU : SameSide ax.x U ax.F)
    (sU : SegCong ax.O ax.E ax.O U) (aU : AngCong A O' B ax.E ax.O U) : stdPt ax A O' B = U :=
  ((exists_stdPt ax h).unique (stdPt_spec ax h) ⟨hU, sU, aU⟩)

/-- Congruent angles have the same standard point. -/
theorem stdPt_congr {A O' B A' O'' B' : P} (h : ¬Collinear (Line := L) A O' B)
    (h' : ¬Collinear (Line := L) A' O'' B') (hc : AngCong A O' B A' O'' B') :
    stdPt ax A O' B = stdPt ax A' O'' B' := by
  obtain ⟨hU, sU, aU⟩ := stdPt_spec ax h'
  have nU : ¬Collinear (Line := L) ax.E ax.O (stdPt ax A' O'' B') := fun hc => hU.1
    (mem_of_collinear hc (Ne.symm ax.hOE) ax.hEx ax.hOx)
  exact stdPt_eq ax h hU sU (angCong_trans h h' nU hc aU)

/-- The **cosine** of an angle: the first co-ordinate of its standard point. -/
noncomputable def cosA (A O' B : P) : G ax := xc ax (toV ax.O (stdPt ax A O' B))

theorem cosA_congr {A O' B A' O'' B' : P} (h : ¬Collinear (Line := L) A O' B)
    (h' : ¬Collinear (Line := L) A' O'' B') (hc : AngCong A O' B A' O'' B') :
    cosA ax A O' B = cosA ax A' O'' B' := by
  unfold cosA; rw [stdPt_congr ax h h' hc]

/-- The co-ordinates of the points of the standard half-ray. -/
theorem std_ray_coords {A O' B : P} (h : ¬Collinear (Line := L) A O' B) {Z : P}
    (hZ : Z ∈ ray ax.O (stdPt ax A O' B)) :
    xc ax (toV ax.O Z) = len ax ax.O Z * cosA ax A O' B := by
  obtain ⟨hU, sU, -⟩ := stdPt_spec ax h
  have hUO : stdPt ax A O' B ≠ ax.O := fun e => hU.1 (e ▸ ax.hOx)
  obtain ⟨c, s, hcs⟩ := ray_coords ax hUO
  have e1 := (hcs _ (mem_ray_self' (L := L) hUO)).1
  have hlen : len ax ax.O (stdPt ax A O' B) = 1 := by
    rw [← len_E ax]; exact (len_eq_iff ax (Ne.symm hUO) ax.hOE).2
      (segCong_symm (L := L) ax.hOE (Ne.symm hUO) sU)
  rw [toV_O, sub_zero, hlen, one_mul] at e1
  have e2 := (hcs Z hZ).1
  rw [toV_O, sub_zero] at e2
  rw [e2, cosA, e1]

/-- **The base of a right triangle**: if `∠XYZ` is a right angle, `XY = XZ · cos ∠YXZ`. -/
theorem base_eq {X Y Z : P} (h : IsRightAngle (L := L) X Y Z) :
    len ax X Y = len ax X Z * cosA ax Y X Z := by
  have hn : ¬Collinear (Line := L) X Y Z := h.1
  have nc : ¬Collinear (Line := L) Y X Z := fun hc => hn hc.swap12
  obtain ⟨hXY, hZY, hXZ⟩ := nc_ne ax hn
  obtain ⟨hU, sU, aU⟩ := stdPt_spec ax nc
  set U := stdPt ax Y X Z
  have hUO : U ≠ ax.O := fun e => hU.1 (e ▸ ax.hOx)
  obtain ⟨hpos, sY⟩ := len_spec ax hXY
  set Y' := ofV (len ax X Y : V ax)
  have hY'O : Y' ≠ ax.O := ne_of_mem_ray hpos
  obtain ⟨Z', hZ'r, sZ'⟩ := segCong_layoff (L := L) hXZ (Ne.symm hUO)
  have nEU : ¬Collinear (Line := L) ax.E ax.O U := fun hc => hU.1
    (mem_of_collinear hc (Ne.symm ax.hOE) ax.hEx ax.hOx)
  have a2 : AngCong Y X Z Y' ax.O Z' := angCong_rays nc nEU aU (mem_ray_self' (L := L) (Ne.symm hXY))
    (mem_ray_self' (L := L) (Ne.symm hXZ)) hpos hZ'r
  have hZ'x : Z' ∉ ax.x := fun hh => (sameSide_of_ray ax.hOx hU.1 hZ'r).2.1 hh
  have nc' : ¬Collinear (Line := L) ax.O Y' Z' := fun hc => hZ'x
    (mem_of_collinear hc (Ne.symm hY'O) ax.hOx (len ax X Y).2)
  obtain ⟨sYZ, -, -⟩ := (pf (L := L) ax.hOE).sas hn nc' sY sZ' a2
  obtain ⟨φ, hφ, φX, φY, φZ⟩ := exists_isom_of_tri hn nc' hXY sY sZ' sYZ
  have r := isom_rightAngle ax hφ h
  rw [φX, φY, φZ] at r
  have hq := (rightAngle_iff ax (len ax X Y).2 hY'O hZ'x).1 r
  -- the first co-ordinate of `Z'` is `Y'`
  have e1 : xc ax (toV ax.O Z') = len ax X Y := by
    refine (coords_of ax (len ax X Y) ⟨-jE ax (toV ax.O Z' - toV ax.O Y'), (Xs ax).neg_mem
      (jE_Y ax hq)⟩ ?_).1
    show toV ax.O Z' = toV ax.O Y' + jE ax (-jE ax (toV ax.O Z' - toV ax.O Y'))
    rw [map_neg, jE_jE_apply, neg_neg]; abel
  have e2 := std_ray_coords ax nc hZ'r
  have e3 : len ax ax.O Z' = len ax X Z :=
    (len_eq_iff ax (Ne.symm (ne_of_mem_ray hZ'r)) hXZ).2
      (segCong_symm (L := L) hXZ (Ne.symm (ne_of_mem_ray hZ'r)) sZ')
  rw [← e1, e2, e3]

/-- The cosine of an **acute** angle is positive. -/
theorem cosA_pos {A O' B : P} (h : IsAcute (L := L) A O' B) : 0 < cosA ax A O' B := by
  have r0 := axes_right ax
  obtain ⟨nc, -, W, hW, aW⟩ := isAcute_wellDefined h r0
  have hFx : ax.F ∉ ax.x := fun h => ax.hOF (ax.hxy _ h ax.hFy).symm
  have hEy : ax.E ∉ ax.y := E_not_mem_y ax
  obtain ⟨hU, sU, aU⟩ := stdPt_spec ax nc
  set U := stdPt ax A O' B
  have sWx : SameSide ax.x W ax.F := sameSide_of_between_mem' ax.hEx hFx hW
  have sWy : SameSide ax.y W ax.E := sameSide_of_between_mem' ax.hFy hEy (between_symm hW)
  have r := (pf (L := L) ax.hOE).layoff_unique Set.univ rfl A O' B ax.x ax.O ax.E W U nc
    (lineIn_univ _) ax.hOx ax.hEx (Ne.symm ax.hOE) trivial trivial
    (OrderCore.sameSide_trans sWx (OrderCore.sameSide_symm hU)) aW aU
  have hUO : U ≠ ax.O := fun e => hU.1 (e ▸ ax.hOx)
  have hUr : U ∈ ray ax.O W := by rw [r]; exact mem_ray_self' (L := L) hUO
  have sUy : SameSide ax.y U ax.E := OrderCore.sameSide_trans
    (OrderCore.sameSide_symm (sameSide_of_ray ax.hOy sWy.1 hUr)) sWy
  rw [pos_iff_posG]
  set p := xc ax (toV ax.O U)
  have hU' := coords_eq ax (toV ax.O U)
  have hp0 : (p : V ax) ≠ 0 := by
    intro e
    apply sUy.1
    have h2 : toV ax.O U = jE ax (yc ax (toV ax.O U)) := by
      conv_lhs => rw [hU']
      rw [show (xc ax (toV ax.O U) : V ax) = 0 from e, zero_add]
    have h1 : toV ax.O U ∈ Ys ax := by rw [h2]; exact jE_X ax (yc ax _).2
    exact h1
  have hpy : ofV (p : V ax) ∉ ax.y := not_mem_y_of ax p.2 hp0
  have h3 : toV ax.O U - (p : V ax) = jE ax (yc ax (toV ax.O U)) := by
    conv_lhs => rw [hU']
    rw [add_sub_cancel_left]
  have s1 : SameSide ax.y U (ofV (p : V ax)) := sameSide_of_sub_mem ax ax.hOy hpy (by
    show toV ax.O U - (p : V ax) ∈ Ys ax
    rw [h3]; exact jE_X ax (yc ax _).2)
  exact (posV_iff ax p.2).2 ⟨hp0, OrderCore.sameSide_trans (OrderCore.sameSide_symm s1) sUy⟩

/-- **For an acute angle `α` and every length `c` there is a right triangle with hypotenuse `c` and
base angle `α`.** -/
theorem exists_right_triangle {A O' B : P} (h : IsAcute (L := L) A O' B) {c : G ax} (hc : 0 < c) :
    ∃ X Y Z : P, IsRightAngle (L := L) X Y Z ∧ AngCong A O' B Y X Z ∧ len ax X Z = c := by
  have nc : ¬Collinear (Line := L) A O' B := h.choose_spec.choose_spec.choose_spec.2.1
  have hcos := cosA_pos ax h
  obtain ⟨hU, sU, aU⟩ := stdPt_spec ax nc
  set U := stdPt ax A O' B
  have hUO : U ≠ ax.O := fun e => hU.1 (e ▸ ax.hOx)
  have hcp : PosG ax c := (pos_iff_posG ax).1 hc
  have hcO : ofV (c : V ax) ≠ ax.O := ne_of_mem_ray hcp
  obtain ⟨Z', hZ'r, sZ'⟩ := segCong_layoff (L := L) (Ne.symm hcO) (Ne.symm hUO)
  have hlen : len ax ax.O Z' = c := by
    rw [← len_of_pos ax hcp]
    exact (len_eq_iff ax (Ne.symm (ne_of_mem_ray hZ'r)) (Ne.symm hcO)).2
      (segCong_symm (L := L) (Ne.symm hcO) (Ne.symm (ne_of_mem_ray hZ'r)) sZ')
  set y := c * cosA ax A O' B
  have hy : PosG ax y := (pos_iff_posG ax).1 (mul_pos hc hcos)
  set Y' := ofV (y : V ax)
  have hY'O : Y' ≠ ax.O := ne_of_mem_ray hy
  have hZ'x : Z' ∉ ax.x := fun hh => (sameSide_of_ray ax.hOx hU.1 hZ'r).2.1 hh
  have e1 := std_ray_coords ax nc hZ'r
  rw [hlen] at e1
  have hq : toV ax.O Z' - toV ax.O Y' ∈ Ys ax := by
    have h0 := coords_eq ax (toV ax.O Z')
    rw [e1] at h0
    have h4 : toV ax.O Z' - (y : V ax) = jE ax (yc ax (toV ax.O Z')) := by
      conv_lhs => rw [h0]
      rw [add_sub_cancel_left]
    show toV ax.O Z' - (y : V ax) ∈ Ys ax
    rw [h4]; exact jE_X ax (yc ax _).2
  have r := (rightAngle_iff ax y.2 hY'O hZ'x).2 hq
  refine ⟨ax.O, Y', Z', r, ?_, hlen⟩
  have nEU : ¬Collinear (Line := L) ax.E ax.O U := fun hc => hU.1
    (mem_of_collinear hc (Ne.symm ax.hOE) ax.hEx ax.hOx)
  obtain ⟨hAO, hBO, -⟩ := nc_ne ax nc
  exact angCong_rays nc nEU aU (mem_ray_self' (L := L) hAO) (mem_ray_self' (L := L) hBO) hy hZ'r

end RightTriangles

section AngleLine

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-- **A line through a given point cutting a given line at a given angle** (§ 14): lay off the angle
at a point of the line and draw the parallel (III) through the given point. -/
theorem exists_line_at_angle {a : L} {U O V Pt : P} (hn : ¬Collinear (Line := L) U O V)
    (hP : Pt ∉ a) : ∃ X Y : P, X ∈ a ∧ Y ∈ a ∧ X ≠ Y ∧ AngCong U O V Y X Pt := by
  obtain ⟨X0, Y0, hXY0, hX0, hY0⟩ := exists_two_points (Point := P) a
  have ea := eq_line hXY0 hX0 hY0
  let F := pf (L := L) hXY0
  obtain ⟨Z, -, hZ, aZ⟩ := F.layoff Set.univ rfl U O V a X0 Y0 Pt hn (lineIn_univ _) hX0 hY0
    (Ne.symm hXY0) trivial hP
  have hZa : Z ∉ a := hZ.1
  have hZX0 : Z ≠ X0 := fun e => hZa (e ▸ hX0)
  obtain ⟨hUO, hVO, -⟩ := F.ne hn
  have nY0Z : ¬Collinear (Line := L) Y0 X0 Z := fun hc =>
    hZa (mem_of_collinear hc (Ne.symm hXY0) hY0 hX0)
  set k := line (Line := L) X0 Z (Ne.symm hZX0)
  have hX0k : X0 ∈ k := mem_line_left _
  have hZk : Z ∈ k := mem_line_right _
  by_cases hPk : Pt ∈ k
  · -- the point lies on the laid-off half-ray
    have hPr : Pt ∈ ray X0 Z := mem_ray_of_sameSide hX0 (collinear_of_mem hX0k hZk hPk)
      (fun e => hP (e ▸ hX0)) hZ
    exact ⟨X0, Y0, hX0, hY0, hXY0, angCong_rays hn nY0Z aZ (mem_ray_self' (L := L) hUO)
      (mem_ray_self' (L := L) hVO) (mem_ray_self' (L := L) (Ne.symm hXY0)) hPr⟩
  obtain ⟨k', ⟨hPk', hk'⟩, -⟩ := exists_unique_parallel (Point := P) hPk
  have hk'k : ¬Meets (Point := P) k' k := hk'
  -- the parallel meets `a`
  obtain ⟨X, hXk', hXa⟩ : Meets (Point := P) k' a := by
    by_contra hn'
    have hX0k' : X0 ∉ k' := fun h => hn' ⟨X0, h, hX0⟩
    obtain ⟨b, -, hb⟩ := exists_unique_parallel (Point := P) hX0k'
    have e1 := hb a ⟨hX0, fun ⟨W, h1, h2⟩ => hn' ⟨W, h2, h1⟩⟩
    have e2 := hb k ⟨hX0k, fun ⟨W, h1, h2⟩ => hk'k ⟨W, h2, h1⟩⟩
    exact hZa (by rw [e1.trans e2.symm]; exact hZk)
  have hXX0 : X ≠ X0 := fun e => hk'k ⟨X, hXk', e ▸ hX0k⟩
  have sPZ : SameSide (line (Line := L) X0 X (Ne.symm hXX0)) Z Pt := by
    rw [← eq_line (Ne.symm hXX0) hX0 hXa]; exact hZ
  rcases mem_ray_or_between (L := L) (collinear_of_mem hX0 hY0 hXa) (Ne.symm hXY0) hXX0 with hr | hb
  · -- `X` on the half-ray `X₀Y₀`
    obtain ⟨R, hR⟩ := exists_beyond (Line := L) (Ne.symm hXX0)
    have c := theorem19_corresponding (L := L) (fun ⟨W, h1, h2⟩ => hk'k ⟨W, h2, h1⟩) hX0k hXk'
      (Ne.symm hXX0) hZk hPk' sPZ hR
    have hRa : R ∈ a := mem_right_of_between hR hX0 hXa
    have nXZ : ¬Collinear (Line := L) X X0 Z := fun hc =>
      hZa (mem_of_collinear hc hXX0 hXa hX0)
    have a1 : AngCong U O V X X0 Z := angCong_rays hn nY0Z aZ (mem_ray_self' (L := L) hUO)
      (mem_ray_self' (L := L) hVO) hr (mem_ray_self' (L := L) hZX0)
    have nZX0X : ¬Collinear (Line := L) Z X0 X := fun hc => nXZ hc.swap13
    have nPXR : ¬Collinear (Line := L) Pt X R := fun hc =>
      hP (mem_of_collinear hc.swap13 (ne23_of_between (Line := L) hR).symm hRa hXa)
    refine ⟨X, R, hXa, hRa, ne23_of_between (Line := L) hR, ?_⟩
    have a2 : AngCong X X0 Z R X Pt := angCong_swap_left nZX0X (not_collinear_swap nPXR)
      (angCong_swap_right nZX0X nPXR c)
    exact angCong_trans hn nXZ (fun hc => nPXR hc.swap13) a1 a2
  · -- `X` on the opposite half-ray
    have hR : Between X X0 Y0 := between_symm hb
    have sPZ' : SameSide (line (Line := L) X X0 hXX0) Pt Z := by
      rw [← eq_line hXX0 hXa hX0]; exact OrderCore.sameSide_symm hZ
    have c := theorem19_corresponding (L := L) hk'k hXk' hX0k hXX0 hPk' hZk sPZ' hR
    have nPXX0 : ¬Collinear (Line := L) Pt X X0 := fun hc =>
      hP (mem_of_collinear hc.swap13 hXX0.symm hX0 hXa)
    refine ⟨X, X0, hXa, hX0, hXX0, ?_⟩
    have a1 : AngCong U O V Z X0 Y0 := angCong_swap_right hn nY0Z aZ
    have c' : AngCong Z X0 Y0 Pt X X0 := angCong_symm nPXX0 (not_collinear_swap nY0Z) c
    exact angCong_swap_right hn nPXX0 (angCong_trans hn (not_collinear_swap nY0Z) nPXX0 a1 c')

end AngleLine

end Pas

end HilbertFoundations
