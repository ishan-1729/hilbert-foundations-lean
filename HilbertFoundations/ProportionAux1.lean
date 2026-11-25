import HilbertFoundations.Pascal

/-!
# Helper module for `Proportion.lean`: sums and products of segments (§ 15)

This module contains no unit of Hilbert's text.

* **Sums of segments** (`SegSum`), from the linear axioms only (`SegmentCongruence`): existence,
  uniqueness up to congruence, commutativity and associativity.
* In a plane geometry with I 1–2, II, III, IV and axes `ax` (with `OE` the unit segment):
  **lengths add** (`len_add`: if `B` lies between `A` and `C`, then `AC = AB + BC` in the field of
  segments), and **Hilbert's product construction** (`HilbertProd`, on an arbitrary right angle)
  gives the product of the lengths in this field (`hilbertProd_iff`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section SegSumSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L]
include hS

/-- The segment `C₁C₂` is the **sum** of `A₁A₂` and `B₁B₂` (§ 15): there are points `X`, `Y`, `Z`
of a line with `Y` between `X` and `Z`, `XY ≡ A₁A₂`, `YZ ≡ B₁B₂` and `XZ ≡ C₁C₂`. -/
def SegSum (A1 A2 B1 B2 C1 C2 : P) : Prop :=
  ∃ X Y Z : P, Between X Y Z ∧ SegCong X Y A1 A2 ∧ SegCong Y Z B1 B2 ∧ SegCong X Z C1 C2

/-- A segment can be extended beyond an extremity by a given segment. -/
theorem exists_extend {A1 A2 B1 B2 : P} (hA : A1 ≠ A2) (hB : B1 ≠ B2) :
    ∃ Z : P, Between A1 A2 Z ∧ SegCong A2 Z B1 B2 := by
  obtain ⟨D, hD⟩ := exists_beyond (Line := L) hA
  obtain ⟨Z, hZr, hZ⟩ := segCong_layoff (L := L) hB (ne23_of_between (Line := L) hD)
  refine ⟨Z, between_of_mem_rays hD (mem_ray_self' (L := L) hA) hZr, ?_⟩
  exact segCong_symm (L := L) hB (Ne.symm (ne_of_mem_ray hZr)) hZ

/-- **Existence of the sum.** -/
theorem segSum_exists {A1 A2 B1 B2 : P} (hA : A1 ≠ A2) (hB : B1 ≠ B2) :
    ∃ C1 C2 : P, C1 ≠ C2 ∧ SegSum A1 A2 B1 B2 C1 C2 := by
  obtain ⟨Z, hZ, sZ⟩ := exists_extend (L := L) hA hB
  exact ⟨A1, Z, ne13_of_between (Line := L) hZ, A1, A2, Z, hZ, segCong_refl (Line := L) hA, sZ,
    segCong_refl (Line := L) (ne13_of_between (Line := L) hZ)⟩

/-- **Uniqueness of the sum** up to congruence (IV 3). -/
theorem segSum_unique {A1 A2 B1 B2 C1 C2 C1' C2' : P} (hA : A1 ≠ A2) (hB : B1 ≠ B2)
    (hC : C1 ≠ C2) (hC' : C1' ≠ C2') (h : SegSum A1 A2 B1 B2 C1 C2)
    (h' : SegSum A1 A2 B1 B2 C1' C2') : SegCong C1 C2 C1' C2' := by
  obtain ⟨X, Y, Z, hb, s1, s2, s3⟩ := h
  obtain ⟨X', Y', Z', hb', s1', s2', s3'⟩ := h'
  have hXY := ne12_of_between (Line := L) hb
  have hYZ := ne23_of_between (Line := L) hb
  have hXZ := ne13_of_between (Line := L) hb
  have hXY' := ne12_of_between (Line := L) hb'
  have hYZ' := ne23_of_between (Line := L) hb'
  have hXZ' := ne13_of_between (Line := L) hb'
  have e1 : SegCong X Y X' Y' := segCong_trans (L := L) hXY hA hXY' s1
    (segCong_symm (L := L) hXY' hA s1')
  have e2 : SegCong Y Z Y' Z' := segCong_trans (L := L) hYZ hB hYZ' s2
    (segCong_symm (L := L) hYZ' hB s2')
  have e3 := segCong_add hb hb' e1 e2
  exact segCong_trans (L := L) hC hXZ hC' (segCong_symm (L := L) hXZ hC s3)
    (segCong_trans (L := L) hXZ hXZ' hC' e3 s3')

/-- **Commutative law of addition.** -/
theorem segSum_comm {A1 A2 B1 B2 C1 C2 : P} (h : SegSum A1 A2 B1 B2 C1 C2) :
    SegSum B1 B2 A1 A2 C1 C2 := by
  obtain ⟨X, Y, Z, hb, s1, s2, s3⟩ := h
  exact ⟨Z, Y, X, between_symm hb, segCong_swap_left (Line := L) s2,
    segCong_swap_left (Line := L) s1, segCong_swap_left (Line := L) s3⟩

/-- **Associative law of addition**: if `d = a + b`, `e = d + c` and `f = b + c`, then
`e = a + f`. -/
theorem segSum_assoc {A1 A2 B1 B2 C1 C2 D1 D2 E1 E2 F1 F2 : P} (hA : A1 ≠ A2) (hB : B1 ≠ B2)
    (hC : C1 ≠ C2) (hD : D1 ≠ D2) (hE : E1 ≠ E2) (hF : F1 ≠ F2)
    (h1 : SegSum A1 A2 B1 B2 D1 D2) (h2 : SegSum D1 D2 C1 C2 E1 E2)
    (h3 : SegSum B1 B2 C1 C2 F1 F2) : SegSum A1 A2 F1 F2 E1 E2 := by
  obtain ⟨Y, hY, sY⟩ := exists_extend (L := L) hA hB
  obtain ⟨Z, hZ, sZ⟩ := exists_extend (L := L) (ne23_of_between (Line := L) hY) hC
  obtain ⟨hAZ, hA1Z⟩ := OrderLin.trans₁ hY hZ
  -- `A₁Y` is `d`, `A₁Z` is `e`, `A₂Z` is `f`
  have hd : SegSum A1 A2 B1 B2 A1 Y :=
    ⟨A1, A2, Y, hY, segCong_refl (Line := L) hA, sY,
      segCong_refl (Line := L) (ne13_of_between (Line := L) hY)⟩
  have sd := segSum_unique (L := L) hA hB (ne13_of_between (Line := L) hY) hD hd h1
  have he : SegSum D1 D2 C1 C2 A1 Z :=
    ⟨A1, Y, Z, hA1Z, sd, sZ, segCong_refl (Line := L) (ne13_of_between (Line := L) hA1Z)⟩
  have se := segSum_unique (L := L) hD hC (ne13_of_between (Line := L) hA1Z) hE he h2
  have hf : SegSum B1 B2 C1 C2 A2 Z :=
    ⟨A2, Y, Z, hZ, sY, sZ, segCong_refl (Line := L) (ne13_of_between (Line := L) hZ)⟩
  have sf := segSum_unique (L := L) hB hC (ne13_of_between (Line := L) hZ) hF hf h3
  exact ⟨A1, A2, Z, hAZ, segCong_refl (Line := L) hA, sf, se⟩

end SegSumSec

section PlaneSeg

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

theorem ofV_pos {t : G ax} (ht : 0 < t) : ofV (t : V ax) ∈ ray ax.O ax.E :=
  (pos_iff_posG ax).1 ht

theorem ofV_ne_O' {t : G ax} (ht : 0 < t) : ofV (t : V ax) ≠ ax.O := ne_of_mem_ray (ofV_pos ax ht)

/-- `O`, `y`, `y + w` follow each other for positive `y`, `w`. -/
theorem between_pos {y w : G ax} (hy : 0 < y) (hw : 0 < w) :
    Between ax.O (ofV (y : V ax)) (ofV ((y + w : G ax) : V ax)) := by
  have hyp := (pos_iff_posG ax).1 hy
  have hwp := (pos_iff_posG ax).1 hw
  have hny : ¬PosG ax (-y) := fun h => posG_not_both ax y hyp h
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hny0 : ((-y : G ax) : V ax) ≠ 0 := fun h => hy0 (by
    have : (-y : G ax) = 0 := Subtype.ext h
    exact neg_eq_zero.1 this)
  have hnyy := not_mem_y_of ax (-y).2 hny0
  have o1 : OppositeSides ax.y (ofV ((-y : G ax) : V ax)) ax.E := by
    rcases OrderCore.sameSide_or_opp hnyy (E_not_mem_y ax) with hs | ho
    · exact absurd ((posV_iff ax (-y).2).2 ⟨hny0, hs⟩) hny
    · exact ho
  have sw := ((posV_iff ax w.2).1 hwp).2
  obtain ⟨-, -, Q, hQy, hb⟩ : OppositeSides ax.y (ofV ((-y : G ax) : V ax)) (ofV (w : V ax)) :=
    OrderCore.opp_of_sameSide_opp sw (OrderCore.opp_symm o1) |>
      OrderCore.opp_symm
  have hQx : Q ∈ ax.x := mem_mid_of_between hb (-y).2 w.2
  have hQO : Q = ax.O := ax.hxy Q hQx hQy
  rw [hQO] at hb
  set T := tr (L := L) ax.O (ofV (y : V ax))
  have hT : T ∈ isom (L := L) := transl_isom (tr_mem _ _)
  have hb' := isom_between hT hb
  have e1 : T (ofV ((-y : G ax) : V ax)) = ax.O := by
    apply ofV_injective (O := ax.O)
    show toV ax.O (T _) = toV ax.O ax.O
    rw [tr_vec, toV_ofV, toV_ofV, toV_O]
    show (y : V ax) + -(y : V ax) = 0
    exact add_neg_cancel _
  have e2 : T ax.O = ofV (y : V ax) := tr_apply_O _ _
  have e3 : T (ofV (w : V ax)) = ofV ((y + w : G ax) : V ax) := by
    apply ofV_injective (O := ax.O)
    show toV ax.O (T _) = _
    rw [tr_vec]; rfl
  rwa [e1, e2, e3] at hb'

/-- **Lengths add**: if `Y` lies between `X` and `Z`, then `XZ = XY + YZ`. -/
theorem len_add {X Y Z : P} (h : Between X Y Z) : len ax X Z = len ax X Y + len ax Y Z := by
  have hXY := ne12_of_between (Line := L) h
  have hYZ := ne23_of_between (Line := L) h
  have hXZ := ne13_of_between (Line := L) h
  have hy := len_pos ax hXY
  have hw := len_pos ax hYZ
  have hb := between_pos ax hy hw
  set T := tr (L := L) ax.O (ofV (len ax X Y : V ax))
  have hT : T ∈ isom (L := L) := transl_isom (tr_mem _ _)
  have sT := hT ax.O (ofV (len ax Y Z : V ax)) (Ne.symm (ofV_ne_O' ax hw))
  have e2 : T ax.O = ofV (len ax X Y : V ax) := tr_apply_O _ _
  have e3 : T (ofV (len ax Y Z : V ax)) = ofV ((len ax X Y + len ax Y Z : G ax) : V ax) := by
    apply ofV_injective (O := ax.O)
    show toV ax.O (T _) = _
    rw [tr_vec]; rfl
  rw [e2, e3] at sT
  obtain ⟨-, s1⟩ := len_spec ax hXY
  obtain ⟨-, s2⟩ := len_spec ax hYZ
  have hyO := ofV_ne_O' ax hy
  have hsO := ofV_ne_O' ax (add_pos hy hw)
  have s2' : SegCong Y Z (ofV (len ax X Y : V ax)) (ofV ((len ax X Y + len ax Y Z : G ax) : V ax)) :=
    segCong_trans (L := L) hYZ (Ne.symm (ofV_ne_O' ax hw)) (ne23_of_between (Line := L) hb) s2 sT
  have s3 := segCong_add h hb s1 s2'
  rw [← len_of_pos ax ((pos_iff_posG ax).1 (add_pos hy hw))]
  exact (len_eq_iff ax hXZ (Ne.symm hsO)).2 s3

/-- The points `J t` of the axis `y` for `t > 0`: on the half-ray `OF`, at distance `t`. -/
theorem jE_pos {t : G ax} (ht : 0 < t) :
    ofV (jE ax (t : V ax)) ∈ ray ax.O ax.F ∧ len ax ax.O (ofV (jE ax (t : V ax))) = t := by
  have hJ := rot_isom ax.hJ
  have h1 := isom_ray hJ (ofV_pos ax ht)
  rw [rot_fix ax.hJ, ax.JE] at h1
  refine ⟨h1, ?_⟩
  have := len_isom ax hJ ax.O (ofV (t : V ax))
  rw [rot_fix ax.hJ, len_of_pos ax ((pos_iff_posG ax).1 ht)] at this
  exact this

theorem coords_x (t : G ax) : xc ax (t : V ax) = t ∧ yc ax (t : V ax) = 0 :=
  coords_of ax t 0 (by simp)

theorem coords_J (t : G ax) : xc ax (jE ax (t : V ax)) = 0 ∧ yc ax (jE ax (t : V ax)) = t :=
  coords_of ax 0 t (by simp)

/-- Isometries preserve "parallel or equal" for lines given by two points each. -/
theorem isom_parEq {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) {X Y Z W : P} (hXY : X ≠ Y)
    (hZW : Z ≠ W) {l m l2 m2 : L} (hX : X ∈ l) (hY : Y ∈ l) (hZ : Z ∈ m) (hW : W ∈ m)
    (hX2 : f X ∈ l2) (hY2 : f Y ∈ l2) (hZ2 : f Z ∈ m2) (hW2 : f W ∈ m2)
    (h : l = m ∨ ¬Meets (Point := P) l m) : l2 = m2 ∨ ¬Meets (Point := P) l2 m2 := by
  have e1 : l2 = imLine f hf l := line_unique (f.injective.ne hXY) hX2 hY2
    ((mem_imLine hf l X).2 hX) ((mem_imLine hf l Y).2 hY)
  have e2 : m2 = imLine f hf m := line_unique (f.injective.ne hZW) hZ2 hW2
    ((mem_imLine hf m Z).2 hZ) ((mem_imLine hf m W).2 hW)
  subst e1 e2
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr fun hh => h ((isom_meets_iff hf).1 hh)

end PlaneSeg

/-- **Hilbert's construction of the product** `c = ab` (§ 15) with the unit segment `U₁U₂`: on the
side `OP₁` of a right angle lay off `1 = OE₁` and `b = OB'`, on the side `OP₂` lay off `a = OA'`;
the line `E₁A'` and the line through `B'` parallel to it (or equal to it) cut off `c = OC'` on `OP₂`. -/
def HilbertProd {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] (U1 U2 A1 A2 B1 B2 C1 C2 : P) : Prop :=
  ∃ O P1 P2 E1 A' B' C' : P, IsRightAngle (L := L) P1 O P2 ∧ E1 ∈ ray O P1 ∧
    SegCong O E1 U1 U2 ∧ B' ∈ ray O P1 ∧ SegCong O B' B1 B2 ∧ A' ∈ ray O P2 ∧
    SegCong O A' A1 A2 ∧ C' ∈ ray O P2 ∧ SegCong O C' C1 C2 ∧
    ∃ l m : L, E1 ∈ l ∧ A' ∈ l ∧ B' ∈ m ∧ C' ∈ m ∧ (l = m ∨ ¬Meets (Point := P) l m)

section ProdSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

theorem E_ne_J (a : G ax) : ax.E ≠ ofV (jE ax (a : V ax)) := fun e =>
  E_not_mem_y ax (by rw [e]; exact jE_X ax a.2)

theorem x_ne_J {b c : G ax} (hb : 0 < b) : ofV (b : V ax) ≠ ofV (jE ax (c : V ax)) := fun e =>
  ofV_ne_O' ax hb (ax.hxy _ b.2 (by rw [e]; exact jE_X ax c.2))

/-- Hilbert's product construction in the standard right angle `EOF`. -/
theorem std_parallel_iff {a b c : G ax} (hb : 0 < b) {l m : L} (hl1 : ax.E ∈ l)
    (hl2 : ofV (jE ax (a : V ax)) ∈ l) (hm1 : ofV (b : V ax) ∈ m)
    (hm2 : ofV (jE ax (c : V ax)) ∈ m) :
    (l = m ∨ ¬Meets (Point := P) l m) ↔ c = a * b := by
  have h := parEq_iff_cross ax (E_ne_J ax a) (x_ne_J ax hb) hl1 hl2 hm1 hm2
  have e : (l = m ∨ ¬Meets (Point := P) l m) ↔ ParEq (P := P) l m := Iff.rfl
  rw [e, h, cross]
  simp only [toV_ofV]
  rw [xc_sub, yc_sub, xc_sub, yc_sub]
  have hE : toV ax.O ax.E = ((1 : G ax) : V ax) := rfl
  rw [hE, (coords_x ax 1).1, (coords_x ax 1).2, (coords_J ax a).1, (coords_J ax a).2,
    (coords_J ax c).1, (coords_J ax c).2, (coords_x ax b).1, (coords_x ax b).2]
  unfold cr
  constructor
  · intro h0; linear_combination -h0
  · intro h0; rw [h0]; ring

/-- **Hilbert's product construction gives the product of the lengths** (axes with the unit segment
`OE`). -/
theorem hilbertProd_iff {A1 A2 B1 B2 C1 C2 : P} (ha : A1 ≠ A2) (hb : B1 ≠ B2) (hc : C1 ≠ C2) :
    HilbertProd (L := L) ax.O ax.E A1 A2 B1 B2 C1 C2 ↔
      len ax C1 C2 = len ax A1 A2 * len ax B1 B2 := by
  have hla := len_pos ax ha
  have hlb := len_pos ax hb
  have hlc := len_pos ax hc
  -- the points at given distances on the standard half-rays
  have onE : ∀ {X : P} {D1 D2 : P}, D1 ≠ D2 → X ∈ ray ax.O ax.E → SegCong ax.O X D1 D2 →
      X = ofV (len ax D1 D2 : V ax) := by
    intro X D1 D2 hD hX sX
    obtain ⟨hp, sp⟩ := len_spec ax hD
    exact eq_of_segCong_ray (L := L) hD hX hp (segCong_symm (L := L) (Ne.symm (ne_of_mem_ray hX))
      hD sX) sp
  have onF : ∀ {X : P} {D1 D2 : P}, D1 ≠ D2 → X ∈ ray ax.O ax.F → SegCong ax.O X D1 D2 →
      X = ofV (jE ax (len ax D1 D2 : V ax)) := by
    intro X D1 D2 hD hX sX
    obtain ⟨hJr, hJl⟩ := jE_pos ax (len_pos ax hD)
    have hJO := Ne.symm (ne_of_mem_ray hJr)
    have s2 : SegCong D1 D2 ax.O (ofV (jE ax (len ax D1 D2 : V ax))) := by
      rw [← len_eq_iff ax hD (hJO)]; exact hJl.symm
    exact eq_of_segCong_ray (L := L) hD hX hJr (segCong_symm (L := L) (Ne.symm (ne_of_mem_ray hX))
      hD sX) s2
  constructor
  · rintro ⟨O', P1, P2, E1, A', B', C', hr, hE1, sE1, hB', sB', hA', sA', hC', sC', l, m, h1, h2,
      h3, h4, hpar⟩
    have hO'P2 : O' ≠ P2 := Ne.symm (ne_of_mem_ray' hA')
    obtain ⟨P2', hP2'r, sP2'⟩ := segCong_layoff (L := L) ax.hOE hO'P2
    have hr' : IsRightAngle (L := L) E1 O' P2' :=
      rightAngle_ray_right ax (rightAngle_ray_left ax hr hE1) hP2'r
    have r0 := axes_right ax
    have a1 := theorem15 hr' r0
    have hn := hr'.1
    have hn0 := r0.1
    obtain ⟨hE1O, hP2'O, -⟩ := nc_ne ax hn
    have sOE : SegCong O' E1 ax.O ax.E := sE1
    have sOF : SegCong O' P2' ax.O ax.F :=
      segCong_trans (L := L) (Ne.symm hP2'O) ax.hOE ax.hOF
        (segCong_symm (L := L) ax.hOE (Ne.symm hP2'O) sP2') ax.sOF
    have hn' : ¬Collinear (Line := L) O' E1 P2' := fun h => hn h.swap12
    have hn0' : ¬Collinear (Line := L) ax.O ax.E ax.F := fun h => hn0 h.swap12
    obtain ⟨sEF, -, -⟩ := (pf (L := L) ax.hOE).sas hn' hn0' sOE sOF a1
    obtain ⟨ψ, hψ, ψO, ψE, ψF⟩ := exists_isom_of_tri hn' hn0' (Ne.symm hE1O) sOE sOF sEF
    have rayE : ∀ {X : P}, X ∈ ray O' P1 → ψ X ∈ ray ax.O ax.E := by
      intro X hX
      have := isom_ray hψ (sameSidePt_trans (sameSidePt_symm hE1) hX)
      rwa [ψO, ψE] at this
    have rayF : ∀ {X : P}, X ∈ ray O' P2 → ψ X ∈ ray ax.O ax.F := by
      intro X hX
      have := isom_ray hψ (sameSidePt_trans (sameSidePt_symm hP2'r) hX)
      rwa [ψO, ψF] at this
    have dist : ∀ {X D1 D2 : P}, X ≠ O' → D1 ≠ D2 → SegCong O' X D1 D2 →
        SegCong ax.O (ψ X) D1 D2 := by
      intro X D1 D2 hX hD sX
      have h1 := hψ O' X (Ne.symm hX)
      rw [ψO] at h1
      have hψX : ax.O ≠ ψ X := fun e => hX (ψ.injective (by rw [ψO]; exact e.symm))
      exact SegmentCongruence.ax_IV2 (Line := L) O' X ax.O (ψ X) D1 D2 (Ne.symm hX) hψX hD h1 sX
    have eB := onE hb (rayE hB') (dist (ne_of_mem_ray hB') hb sB')
    have eA := onF ha (rayF hA') (dist (ne_of_mem_ray hA') ha sA')
    have eC := onF hc (rayF hC') (dist (ne_of_mem_ray hC') hc sC')
    have hEA : E1 ≠ A' := fun e => by
      have := congrArg ψ e; rw [ψE, eA] at this; exact E_ne_J ax _ this
    have hBC : B' ≠ C' := fun e => by
      have := congrArg ψ e; rw [eB, eC] at this; exact x_ne_J ax hlb this
    have hp := isom_parEq ax hψ hEA hBC h1 h2 h3 h4
      (l2 := line ax.E (ofV (jE ax (len ax A1 A2 : V ax))) (E_ne_J ax _))
      (m2 := line (ofV (len ax B1 B2 : V ax)) (ofV (jE ax (len ax C1 C2 : V ax))) (x_ne_J ax hlb))
      (by rw [ψE]; exact mem_line_left _) (by rw [eA]; exact mem_line_right _)
      (by rw [eB]; exact mem_line_left _) (by rw [eC]; exact mem_line_right _) hpar
    exact (std_parallel_iff ax hlb (mem_line_left _) (mem_line_right _) (mem_line_left _)
      (mem_line_right _)).1 hp
  · intro h
    set A' := ofV (jE ax (len ax A1 A2 : V ax))
    set B' := ofV (len ax B1 B2 : V ax)
    set C' := ofV (jE ax ((len ax A1 A2 * len ax B1 B2 : G ax) : V ax))
    have hA'r := jE_pos ax hla
    have hC'r := jE_pos ax (mul_pos hla hlb)
    have hEA := E_ne_J ax (len ax A1 A2)
    have hBC := x_ne_J ax hlb (c := len ax A1 A2 * len ax B1 B2)
    have sOf : ∀ {X D1 D2 : P}, X ≠ ax.O → D1 ≠ D2 → len ax ax.O X = len ax D1 D2 →
        SegCong ax.O X D1 D2 := fun hX hD e => (len_eq_iff ax (Ne.symm hX) hD).1 e
    refine ⟨ax.O, ax.E, ax.F, ax.E, A', B', C', axes_right ax,
      mem_ray_self' (L := L) (Ne.symm ax.hOE), segCong_refl (Line := L) ax.hOE,
      ofV_pos ax hlb, sOf (ofV_ne_O' ax hlb) hb (len_of_pos ax ((pos_iff_posG ax).1 hlb)),
      hA'r.1, sOf (ne_of_mem_ray hA'r.1) ha hA'r.2, hC'r.1,
      sOf (ne_of_mem_ray hC'r.1) hc (by rw [hC'r.2, h]),
      line ax.E A' hEA, line B' C' hBC, mem_line_left _, mem_line_right _, mem_line_left _,
      mem_line_right _, ?_⟩
    exact (std_parallel_iff ax hlb (mem_line_left _) (mem_line_right _) (mem_line_left _)
      (mem_line_right _)).2 rfl

end ProdSec

end Pas

end HilbertFoundations
