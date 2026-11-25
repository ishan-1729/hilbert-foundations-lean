import HilbertFoundations.PascalAux4

/-!
# Helper module for `Pascal.lean`: the ordered field of the segments of an axis

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV, with
rectangular axes `ax`.

The points of the axis `x` (vectors of the subgroup `Xs ax`) form a commutative group `G ax`. Its
**multiplication** is Hilbert's construction of § 15: `a * b` is the slope map of the line through
`O` and `E + J a` applied to `b`, i.e. the point `c` with `b + J c` on that line (equivalently:
the parallel through `b` to the line joining `E` with the point `J a` of `y` cuts `y` in `J c`).
Since all slope maps commute (`slope_comm`), this multiplication is commutative and associative,
and `G ax` is a **field** (`fieldG`); with the order of the half-ray `OE` it is an **ordered field**.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section FieldSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

/-- The unit vector `E`. -/
def eV : V ax := toV ax.O ax.E

theorem eV_mem : eV ax ∈ Xs ax := ax.hEx

theorem eV_ne : eV ax ≠ 0 := fun h => by
  have : ofV (eV ax) = ofV (0 : V ax) := congrArg ofV h
  rw [ofV_zero (L := L)] at this
  exact ax.hOE this.symm

theorem eV_not_mem_Ys : eV ax ∉ Ys ax := fun h => eV_ne ax (X_inf_Y ax (eV_mem ax) h)

theorem eJ_ne {a : V ax} (ha : a ∈ Xs ax) : eV ax + jE ax a ≠ 0 := fun h =>
  eV_not_mem_Ys ax (by
    have : eV ax = -jE ax a := eq_neg_of_add_eq_zero_left h
    rw [this]; exact (Ys ax).neg_mem (jE_X ax ha))

theorem ofV_ne_O {v : V ax} (h : v ≠ 0) : ofV v ≠ ax.O := fun e =>
  h (ofV_injective (e.trans (ofV_zero (L := L)).symm))

/-- The line through `O` and `E + J a`. -/
noncomputable def lA {a : V ax} (ha : a ∈ Xs ax) : L :=
  line ax.O (ofV (eV ax + jE ax a)) (Ne.symm (ofV_ne_O ax (eJ_ne ax ha)))

theorem O_mem_lA {a : V ax} (ha : a ∈ Xs ax) : ax.O ∈ lA ax ha := mem_line_left _

theorem eJ_mem_lA {a : V ax} (ha : a ∈ Xs ax) :
    eV ax + jE ax a ∈ lineSub (L := L) (lA ax ha) (O_mem_lA ax ha) := mem_line_right _

theorem lA_ne_y {a : V ax} (ha : a ∈ Xs ax) : lA ax ha ≠ ax.y := by
  intro e
  have h1 : eV ax + jE ax a ∈ Ys ax := by
    have := eJ_mem_lA ax ha
    show ofV (eV ax + jE ax a) ∈ ax.y
    rw [← e]; exact this
  have h2 : eV ax ∈ Ys ax := by
    have := (Ys ax).sub_mem h1 (jE_X ax ha)
    rwa [add_sub_cancel_right] at this
  exact eV_not_mem_Ys ax h2

theorem lA_ne_x {a : V ax} (ha : a ∈ Xs ax) (ha0 : a ≠ 0) : lA ax ha ≠ ax.x := by
  intro e
  have h1 : eV ax + jE ax a ∈ Xs ax := by
    have := eJ_mem_lA ax ha
    show ofV (eV ax + jE ax a) ∈ ax.x
    rw [← e]; exact this
  have h2 : jE ax a ∈ Xs ax := by
    have := (Xs ax).sub_mem h1 (eV_mem ax)
    rwa [add_sub_cancel_left] at this
  exact ha0 (jE_injective ax (X_inf_Y ax h2 (jE_X ax ha)))

/-- **Hilbert's product** (on vectors of `x`). -/
noncomputable def mulV (a b : V ax) : V ax := by
  classical
  exact if ha : a ∈ Xs ax then slope ax (O_mem_lA ax ha) (lA_ne_y ax ha) b else 0

theorem mulV_def {a : V ax} (ha : a ∈ Xs ax) (b : V ax) :
    mulV ax a b = slope ax (O_mem_lA ax ha) (lA_ne_y ax ha) b := by
  simp only [mulV, ha, ↓reduceDIte]

theorem mulV_mem {a b : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) : mulV ax a b ∈ Xs ax := by
  rw [mulV_def ax ha]; exact slope_mem ax _ _ hb

theorem mulV_spec {a b : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) :
    b + jE ax (mulV ax a b) ∈ lineSub (L := L) (lA ax ha) (O_mem_lA ax ha) := by
  rw [mulV_def ax ha]; exact (slope_spec ax _ _ hb).2

theorem mulV_eq {a b c : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) (hc : c ∈ Xs ax)
    (h : b + jE ax c ∈ lineSub (L := L) (lA ax ha) (O_mem_lA ax ha)) : mulV ax a b = c := by
  rw [mulV_def ax ha]; exact slope_eq ax _ _ hb hc h

theorem mulV_one {a : V ax} (ha : a ∈ Xs ax) : mulV ax a (eV ax) = a :=
  mulV_eq ax ha (eV_mem ax) ha (eJ_mem_lA ax ha)

theorem mulV_add {a b c : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) (hc : c ∈ Xs ax) :
    mulV ax a (b + c) = mulV ax a b + mulV ax a c := by
  rw [mulV_def ax ha, mulV_def ax ha, mulV_def ax ha]; exact slope_add ax _ _ hb hc

theorem mulV_zero {a : V ax} (ha : a ∈ Xs ax) : mulV ax a 0 = 0 := by
  have h := mulV_add ax ha (Xs ax).zero_mem (Xs ax).zero_mem
  rw [add_zero] at h
  have h2 : mulV ax a 0 + 0 = mulV ax a 0 + mulV ax a 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem mulV_comm_ops {a b c : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) (hc : c ∈ Xs ax) :
    mulV ax a (mulV ax b c) = mulV ax b (mulV ax a c) := by
  rw [mulV_def ax ha, mulV_def ax hb, mulV_def ax ha, mulV_def ax hb]
  exact slope_comm ax _ _ _ _ hc

theorem mulV_comm {a b : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) : mulV ax a b = mulV ax b a := by
  conv_lhs => rw [← mulV_one ax hb]
  rw [mulV_comm_ops ax ha hb (eV_mem ax), mulV_one ax ha]

theorem mulV_assoc {a b c : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) (hc : c ∈ Xs ax) :
    mulV ax (mulV ax a b) c = mulV ax a (mulV ax b c) := by
  rw [mulV_comm ax (mulV_mem ax ha hb) hc]
  conv_lhs => rw [← mulV_one ax hb]
  rw [mulV_comm_ops ax hc ha (mulV_mem ax hb (eV_mem ax)), mulV_comm_ops ax hc hb (eV_mem ax),
    mulV_one ax hc]

/-- The slope map of a line other than `x` and `y` is surjective. -/
theorem slope_surj {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) (hℓx : ℓ ≠ ax.x) {w : V ax}
    (hw : w ∈ Xs ax) : ∃ u : V ax, u ∈ Xs ax ∧ slope ax hO hℓ u = w := by
  obtain ⟨m, hJm, hm⟩ := exists_parEq (P := P) ax.x (ofV (jE ax w))
  have hmℓ : Meets (Point := P) m ℓ := by
    by_contra hn
    exact hℓx (eq_of_parEq (parEq_trans hm (Or.inr hn : ParEq (P := P) m ℓ)) ax.hOx hO).symm
  obtain ⟨Z, hZm, hZℓ⟩ := hmℓ
  have hu : toV ax.O Z - jE ax w ∈ Xs ax :=
    (mem_line_iff_sub ax.hOx (parEq_symm hm) hJm Z).1 hZm
  refine ⟨toV ax.O Z - jE ax w, hu, slope_eq ax hO hℓ hu hw ?_⟩
  rw [sub_add_cancel]; exact hZℓ

/-- The **segments of the axis** `x`: the points of `x` as vectors. -/
abbrev G (ax : Axes P L) := ↥(Xs ax)

noncomputable instance instMulG : Mul (G ax) := ⟨fun a b => ⟨mulV ax a b, mulV_mem ax a.2 b.2⟩⟩

noncomputable instance instOneG : One (G ax) := ⟨⟨eV ax, eV_mem ax⟩⟩

theorem coe_mulG (a b : G ax) : ((a * b : G ax) : V ax) = mulV ax a b := rfl

theorem coe_oneG : ((1 : G ax) : V ax) = eV ax := rfl

noncomputable instance commRingG : CommRing (G ax) :=
  { (inferInstance : AddCommGroup (G ax)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun a b c => Subtype.ext (mulV_assoc ax a.2 b.2 c.2)
    one_mul := fun a => Subtype.ext (by
      show mulV ax (eV ax) a = a
      rw [mulV_comm ax (eV_mem ax) a.2, mulV_one ax a.2])
    mul_one := fun a => Subtype.ext (mulV_one ax a.2)
    zero_mul := fun a => Subtype.ext (by
      show mulV ax 0 a = 0
      rw [mulV_comm ax (Xs ax).zero_mem a.2, mulV_zero ax a.2])
    mul_zero := fun a => Subtype.ext (mulV_zero ax a.2)
    left_distrib := fun a b c => Subtype.ext (mulV_add ax a.2 b.2 c.2)
    right_distrib := fun a b c => Subtype.ext (by
      show mulV ax (a + b : V ax) c = mulV ax a c + mulV ax b c
      rw [mulV_comm ax ((Xs ax).add_mem a.2 b.2) c.2, mulV_add ax c.2 a.2 b.2,
        mulV_comm ax c.2 a.2, mulV_comm ax c.2 b.2])
    mul_comm := fun a b => Subtype.ext (mulV_comm ax a.2 b.2) }

theorem isFieldG : IsField (G ax) where
  exists_pair_ne := ⟨0, 1, fun h => eV_ne ax (congrArg Subtype.val h).symm⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro a ha
    have ha0 : (a : V ax) ≠ 0 := fun h => ha (Subtype.ext h)
    obtain ⟨u, hu, e⟩ := slope_surj ax (O_mem_lA ax a.2) (lA_ne_y ax a.2) (lA_ne_x ax a.2 ha0)
      (eV_mem ax)
    exact ⟨⟨u, hu⟩, Subtype.ext (by
      show mulV ax a u = eV ax
      rw [mulV_def ax a.2]; exact e)⟩

/-- The **field of the segments** of the axis `x`. -/
noncomputable instance fieldG : Field (G ax) := (isFieldG ax).toField

end FieldSec

section OrderSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

theorem E_not_mem_y : ax.E ∉ ax.y := fun h => ax.hOE (ax.hxy _ ax.hEx h).symm

/-- A point `Z` with `Z - W` on a line `k` through `O`, `W` off `k`: `Z`, `W` lie on the same side
of `k`. -/
theorem sameSide_of_sub_mem {k : L} (hOk : ax.O ∈ k) {Z W : P} (hW : W ∉ k)
    (h : toV ax.O Z - toV ax.O W ∈ lineSub (L := L) k hOk) : SameSide k Z W := by
  obtain ⟨m, hWm, hm⟩ := exists_parEq (P := P) k W
  have hZm : Z ∈ m := (mem_line_iff_sub hOk (parEq_symm hm) hWm Z).2 h
  have hmk : ¬Meets (Point := P) k m := by
    rcases hm with e | e
    · exact absurd (e ▸ hWm) hW
    · exact e
  refine ⟨fun hZ => hmk ⟨Z, hZ, hZm⟩, hW, ?_⟩
  rintro ⟨X, hXk, hb⟩
  have hZW : Z ≠ W := ne13_of_between (Line := L) hb
  have hXm : X ∈ m := mem_mid_of_between hb hZm hWm
  exact hmk ⟨X, hXk, hXm⟩

/-- The **positive** vectors: the points of the half-ray `OE`. -/
def PosV (v : V ax) : Prop := ofV v ∈ ray ax.O ax.E

theorem posV_iff {v : V ax} (hv : v ∈ Xs ax) :
    PosV ax v ↔ v ≠ 0 ∧ SameSide ax.y (ofV v) ax.E := by
  constructor
  · intro h
    refine ⟨fun e => ne_of_mem_ray h (by rw [e, ofV_zero (L := L)]), ?_⟩
    exact OrderCore.sameSide_symm (sameSide_of_ray ax.hOy (E_not_mem_y ax) h)
  · rintro ⟨h0, hs⟩
    exact mem_ray_of_sameSide ax.hOy (collinear_of_mem ax.hOx ax.hEx hv) (ofV_ne_O ax h0)
      (OrderCore.sameSide_symm hs)

theorem not_mem_y_of {v : V ax} (hv : v ∈ Xs ax) (h0 : v ≠ 0) : ofV v ∉ ax.y := fun h =>
  ofV_ne_O ax h0 (ax.hxy _ hv h)

theorem pos_trich {v : V ax} (hv : v ∈ Xs ax) : v = 0 ∨ PosV ax v ∨ PosV ax (-v) := by
  by_cases h0 : v = 0
  · exact Or.inl h0
  right
  have hvy := not_mem_y_of ax hv h0
  rcases OrderCore.sameSide_or_opp hvy (E_not_mem_y ax) with hs | ho
  · exact Or.inl ((posV_iff ax hv).2 ⟨h0, hs⟩)
  · right
    have hn : -v ∈ Xs ax := (Xs ax).neg_mem hv
    have hn0 : -v ≠ 0 := neg_ne_zero.2 h0
    refine (posV_iff ax hn).2 ⟨hn0, ?_⟩
    have hb : Between (ofV v) ax.O (ofV (-v)) := by
      rw [ofV_neg (L := L)]
      exact ((ht_eq_iff (L := L) (ofV_ne_O ax h0)).1 rfl).1
    have o2 : OppositeSides ax.y (ofV v) (ofV (-v)) :=
      opp_of_between_mem ax.hOy hvy hb
    exact OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm o2) ho

theorem pos_not_both {v : V ax} (hv : v ∈ Xs ax) (h1 : PosV ax v) (h2 : PosV ax (-v)) : False := by
  have h0 : v ≠ 0 := ((posV_iff ax hv).1 h1).1
  have hvy := not_mem_y_of ax hv h0
  have hb : Between (ofV v) ax.O (ofV (-v)) := by
    rw [ofV_neg (L := L)]
    exact ((ht_eq_iff (L := L) (ofV_ne_O ax h0)).1 rfl).1
  have o2 : OppositeSides ax.y (ofV v) (ofV (-v)) := opp_of_between_mem ax.hOy hvy hb
  have s := OrderCore.sameSide_trans ((posV_iff ax hv).1 h1).2
    (OrderCore.sameSide_symm ((posV_iff ax ((Xs ax).neg_mem hv)).1 h2).2)
  exact OrderCore.not_sameSide_of_opp o2 s

theorem pos_E : PosV ax (eV ax) := mem_ray_self' (L := L) (Ne.symm ax.hOE)

theorem pos_add {v w : V ax} (hv : v ∈ Xs ax) (hw : w ∈ Xs ax) (h1 : PosV ax v)
    (h2 : PosV ax w) : PosV ax (v + w) := by
  obtain ⟨hv0, sv⟩ := (posV_iff ax hv).1 h1
  obtain ⟨hw0, sw⟩ := (posV_iff ax hw).1 h2
  set M := midp (L := L) (ofV v) (ofV w)
  have hM : ht (L := L) M (ofV v) = ofV w := ht_midp _ _
  -- `M` lies on `x`, on the side of `E`
  have hMx : M ∈ ax.x ∧ SameSide ax.y M ax.E := by
    by_cases e : ofV v = ofV w
    · have : M = ofV v := by
        have := hM; rw [e] at this; exact (ht_fix_iff.1 this).symm.trans e.symm
      rw [this]; exact ⟨hv, sv⟩
    · have hvM : ofV v ≠ M := by
        intro h; rw [← h, ht_self] at hM; exact e hM
      have hb := ((ht_eq_iff (L := L) hvM).1 hM).1
      refine ⟨mem_mid_of_between hb hv hw, ?_⟩
      have s1 : SameSide ax.y (ofV v) (ofV w) := OrderCore.sameSide_trans sv
        (OrderCore.sameSide_symm sw)
      exact OrderCore.sameSide_trans (OrderCore.sameSide_symm (sameSide_of_between s1 hb)) sv
  have hMO : M ≠ ax.O := fun e => hMx.2.1 (e ▸ ax.hOy)
  have hsum : v + w = toV ax.O (ht (L := L) M ax.O) := by
    have := ht_vec ax M (ofV v)
    rw [hM] at this
    have h0 := ht_vec ax M ax.O
    rw [show toV ax.O ax.O = (0 : V ax) from (vzero_def (L := L) ax.O).symm, sub_zero] at h0
    rw [h0]
    have : (w : V ax) = toV ax.O M + toV ax.O M - v := this
    rw [this]; abel
  have hbO := ((ht_eq_iff (L := L) (Ne.symm hMO)).1 rfl).1
  have hx : ht (L := L) M ax.O ∈ ax.x := mem_right_of_between hbO ax.hOx hMx.1
  have hy : ht (L := L) M ax.O ∉ ax.y := fun h =>
    ne13_of_between (Line := L) hbO (ax.hxy _ hx h).symm
  rw [hsum]
  refine (posV_iff ax hx).2 ⟨fun e => ?_, ?_⟩
  · have : ht (L := L) M ax.O = ax.O := by
      have := congrArg ofV e; rwa [ofV_zero (L := L)] at this
    exact ne13_of_between (Line := L) hbO this.symm
  · exact OrderCore.sameSide_trans (OrderCore.sameSide_symm
      (sameSide_of_between_mem' ax.hOy hy hbO)) hMx.2

/-- **The product of positive segments is positive.** -/
theorem pos_mul {a b : V ax} (ha : a ∈ Xs ax) (hb : b ∈ Xs ax) (h1 : PosV ax a)
    (h2 : PosV ax b) : PosV ax (mulV ax a b) := by
  obtain ⟨ha0, sa⟩ := (posV_iff ax ha).1 h1
  obtain ⟨hb0, sb⟩ := (posV_iff ax hb).1 h2
  have hab := mulV_mem ax ha hb
  set c := mulV ax a b
  have hℓ := lA_ne_x ax ha ha0
  set ℓ := lA ax ha
  have hOℓ := O_mem_lA ax ha
  set Z := b + jE ax c
  set Z' := eV ax + jE ax a
  have hZ : ofV Z ∈ ℓ := mulV_spec ax ha hb
  have hZ' : ofV Z' ∈ ℓ := eJ_mem_lA ax ha
  have hZ0 : ofV Z ≠ ax.O := by
    intro e
    have hZx : Z ∈ Ys ax := by
      show ofV Z ∈ ax.y; rw [e]; exact ax.hOy
    have : b ∈ Ys ax := by
      have := (Ys ax).sub_mem hZx (jE_X ax hab)
      rwa [add_sub_cancel_right] at this
    exact hb0 (X_inf_Y ax hb this)
  have hZ'0 : ofV Z' ≠ ax.O := ofV_ne_O ax (eJ_ne ax ha)
  -- Step A: `Z`, `Z'` lie on the side of `E` with respect to `y`
  have sZ : SameSide ax.y (ofV Z) ax.E := by
    have : SameSide ax.y (ofV Z) (ofV b) := sameSide_of_sub_mem ax ax.hOy
      (not_mem_y_of ax hb hb0) (by
        show Z - b ∈ Ys ax
        rw [add_sub_cancel_left]; exact jE_X ax hab)
    exact OrderCore.sameSide_trans this sb
  have sZ' : SameSide ax.y (ofV Z') ax.E := by
    have : SameSide ax.y (ofV Z') ax.E := sameSide_of_sub_mem ax ax.hOy (E_not_mem_y ax) (by
        show Z' - eV ax ∈ Ys ax
        rw [add_sub_cancel_left]; exact jE_X ax ha)
    exact this
  -- Step B: `Z`, `Z'` on the same half-ray of `ℓ`, hence on the same side of `x`
  have hr : ofV Z' ∈ ray ax.O (ofV Z) :=
    mem_ray_of_sameSide ax.hOy (collinear_of_mem hOℓ hZ hZ') hZ'0
      (OrderCore.sameSide_trans sZ (OrderCore.sameSide_symm sZ'))
  have hZx : ofV Z ∉ ax.x := fun h => hZ0 (by
    by_contra hne
    exact hℓ (line_unique (Ne.symm hne) hOℓ hZ ax.hOx h))
  have sx : SameSide ax.x (ofV Z) (ofV Z') := sameSide_of_ray ax.hOx hZx hr
  -- Step C: `J c` and `J a` on the same side of `x`
  have hJc0 : c ≠ 0 := by
    intro e
    apply hZx
    show Z ∈ Xs ax
    simp only [Z, e, map_zero, add_zero]; exact hb
  have hJcx : ofV (jE ax c) ∉ ax.x := fun h => hJc0 (jE_injective ax (X_inf_Y ax h (jE_X ax hab)))
  have hJax : ofV (jE ax a) ∉ ax.x := fun h => ha0 (jE_injective ax (X_inf_Y ax h (jE_X ax ha)))
  have s1 : SameSide ax.x (ofV Z) (ofV (jE ax c)) := sameSide_of_sub_mem ax ax.hOx hJcx (by
    show Z - jE ax c ∈ Xs ax
    rw [add_sub_cancel_right]; exact hb)
  have s2 : SameSide ax.x (ofV Z') (ofV (jE ax a)) := sameSide_of_sub_mem ax ax.hOx hJax (by
    show Z' - jE ax a ∈ Xs ax
    rw [add_sub_cancel_right]; exact eV_mem ax)
  have s3 : SameSide ax.x (ofV (jE ax a)) (ofV (jE ax c)) :=
    OrderCore.sameSide_trans (OrderCore.sameSide_symm s2)
      (OrderCore.sameSide_trans (OrderCore.sameSide_symm sx) s1)
  -- Step D: back to `x` by `J⁻¹`
  have hr2 : ofV (jE ax c) ∈ ray ax.O (ofV (jE ax a)) :=
    mem_ray_of_sameSide ax.hOx (collinear_of_mem ax.hOy (jE_X ax ha) (jE_X ax hab))
      (fun e => hJcx (by rw [e]; exact ax.hOx)) s3
  have hJi := isom_inv (rot_isom ax.hJ)
  have hr3 := isom_ray hJi hr2
  have e1 : ∀ v : V ax, ax.J⁻¹ (ofV (jE ax v)) = ofV v := fun v => perm_inv_apply ax.J (ofV v)
  rw [e1, e1, show ax.J⁻¹ ax.O = ax.O by
    rw [Equiv.Perm.inv_eq_iff_eq, rot_fix ax.hJ]] at hr3
  exact sameSidePt_trans h1 (sameSidePt_trans (sameSidePt_symm (mem_ray_self' (L := L)
    (ofV_ne_O ax ha0))) hr3)

end OrderSec

section OrderInst

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

/-- Positive elements of `G ax`. -/
def PosG (a : G ax) : Prop := PosV ax (a : V ax)

theorem not_posG_zero : ¬PosG ax 0 := fun h => ne_of_mem_ray h (ofV_zero (L := L))

theorem posG_trich (a : G ax) : a = 0 ∨ PosG ax a ∨ PosG ax (-a) := by
  rcases pos_trich ax a.2 with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem posG_not_both (a : G ax) (h1 : PosG ax a) (h2 : PosG ax (-a)) : False :=
  pos_not_both ax a.2 h1 h2

theorem posG_add {a b : G ax} (h1 : PosG ax a) (h2 : PosG ax b) : PosG ax (a + b) :=
  pos_add ax a.2 b.2 h1 h2

theorem posG_mul {a b : G ax} (h1 : PosG ax a) (h2 : PosG ax b) : PosG ax (a * b) :=
  pos_mul ax a.2 b.2 h1 h2

theorem posG_one : PosG ax 1 := pos_E ax

/-- The **order of the segments**: `a < b` when `b - a` is positive. -/
noncomputable instance linOrdG : LinearOrder (G ax) where
  le a b := a = b ∨ PosG ax (b - a)
  lt a b := PosG ax (b - a)
  le_refl a := Or.inl rfl
  le_trans a b c := by
    rintro (rfl | h1) (rfl | h2)
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h1
    · right
      have := posG_add ax h1 h2
      rwa [show b - a + (c - b) = c - a by abel] at this
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (e | h')
      · rw [e, sub_self] at h; exact not_posG_zero ax h
      · exact posG_not_both ax _ h (by rwa [neg_sub])
    · rintro ⟨(e | h), h'⟩
      · exact absurd (Or.inl e.symm) h'
      · exact h
  le_antisymm a b := by
    rintro (e | h1) (e' | h2)
    · exact e
    · exact e
    · exact e'.symm
    · exact absurd h2 (fun h2 => posG_not_both ax _ h1 (by rwa [neg_sub]))
  le_total a b := by
    rcases posG_trich ax (b - a) with h | h | h
    · exact Or.inl (Or.inl (sub_eq_zero.1 h).symm)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr (by rwa [neg_sub] at h))
  toDecidableLE := Classical.decRel _

theorem lt_iff_posG {a b : G ax} : a < b ↔ PosG ax (b - a) := Iff.rfl

theorem pos_iff_posG {a : G ax} : 0 < a ↔ PosG ax a := by
  rw [lt_iff_posG, sub_zero]

instance isOrderedAddMonoidG : IsOrderedAddMonoid (G ax) where
  add_le_add_left a b h c := by
    rcases h with rfl | h
    · exact le_refl _
    · right
      rwa [show b + c - (a + c) = b - a by abel]

instance zeroLEOneG : ZeroLEOneClass (G ax) where
  zero_le_one := Or.inr (by rw [sub_zero]; exact posG_one ax)

/-- **The segments of the axis form an ordered field.** -/
instance isStrictOrderedRingG : IsStrictOrderedRing (G ax) :=
  IsStrictOrderedRing.of_mul_pos fun a b ha hb => by
    rw [pos_iff_posG] at ha hb ⊢
    exact posG_mul ax ha hb

end OrderInst

end Pas

end HilbertFoundations
