import HilbertFoundations.DesarguesAlgebraAux6

/-!
# Helper for §§ 24–30 (review additions)

Helper module of `DesarguesAlgebra.lean` (the units are stated there). Contents:

* **Laws 1–6 without Desargues's theorem** (§ 28: "we see immediately that … theorems 1–6 of
  Section 13 are fulfilled"): Hilbert's sum and product are defined in any plane with I 1–2 and III,
  and the laws 1–6 (existence and uniqueness of sums, products, differences and quotients, the
  neutral elements `0`, `1`) hold there; the proofs invert Hilbert's constructions by parallels.
* **Laws 13, 14** (and the asymmetry of 13) for Hilbert's order, from the axioms of order alone.
* **The degenerate cases of Hilbert's order convention** (§ 28): `A` or `B` coinciding with `O` or
  `E`.
* **The line through the origin** (§ 27): Hilbert's segment `e` (cut off on the `y`-axis by the
  parallel through `E` to `AB`) and the parallelism `g ∥ AB`.
* **The literal second part of Desargues's theorem fails in the real plane** when two joining lines
  coincide.
* **The planes and lines of the space of § 29 are Hilbert's**: every plane is given by an equation
  with left coefficients (`plane_eq_equation`); two planes satisfying Hilbert's condition meet in a
  line (`hilbert_line_of_planes`), and every line arises so (`line_eq_hilbert_line`).
* **`K³` is a part of `Kⁿ`** (`coord3_any_dimension`), a partial result for the last claim of § 30.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

namespace DesAlg

/-! ## Laws 1–6 from I 1–2 and III alone -/

section Laws16

variable {P : Type u} {L : Type v} [HasLines P L] [PlaneParallels P L] [Nonempty L] {F : Frame P}

namespace Frame

variable (F)

theorem toX_of_mem {A : P} (hA : A ∈ (F.xl : L)) : F.toX A = A :=
  (F.toX_eq hA (mem_pline _ _)).symm

theorem toY_injOn {A B : P} (hA : A ∈ (F.xl : L)) (hB : B ∈ (F.xl : L)) (h : F.toY A = F.toY B) :
    A = B := by
  rw [← F.toX_toY A hA, ← F.toX_toY B hB, h]

theorem toX_injOn {A B : P} (hA : A ∈ (F.yl : L)) (hB : B ∈ (F.yl : L)) (h : F.toX A = F.toX B) :
    A = B := by
  rw [← F.toY_toX A hA, ← F.toY_toX B hB, h]

/-- A point of the first axis lying on the second one is `O`. -/
theorem eq_O_of_mem {A : P} (hx : A ∈ (F.xl : L)) (hy : A ∈ (F.yl : L)) : A = F.O :=
  eq_of_mem_not_lpar F.nl_xy hx hy F.O_xl F.O_yl

theorem not_lpar_xl_pline_ul (X : P) : ¬LPar P (F.xl : L) (pline (F.ul : L) X) :=
  not_lpar_pline_right (fun h => F.nl_ux h.symm) X

theorem not_lpar_yl_pline_ul (X : P) : ¬LPar P (F.yl : L) (pline (F.ul : L) X) :=
  not_lpar_pline_right (fun h => F.nl_uy h.symm) X

end Frame

namespace Seg

theorem ne_zero_iff_pt {a : Seg F} : a ≠ 0 ↔ a.pt ≠ F.O :=
  ⟨fun h e => h (Seg.ext e), fun h e => h (congrArg Seg.pt e)⟩

theorem pt_not_yl {a : Seg F} (ha : a ≠ 0) : a.pt ∉ (F.yl : L) := fun h =>
  ne_zero_iff_pt.1 ha (F.eq_O_of_mem a.mem h)

/-- **Law 2 without Desargues**: `a + 0 = a` and `0 + a = a`. -/
theorem add_zero_nd (a : Seg F) : a + 0 = a := by
  apply Seg.ext
  show F.toX (meet (pline (F.xl : L) (F.toY a.pt)) (pline (F.yl : L) F.O)) = a.pt
  rw [pline_of_mem F.O_yl, ← eq_meet (not_lpar_pline_left F.nl_xy _) (mem_pline _ _)
    (F.toY_mem _), F.toX_toY _ a.mem]

theorem zero_add_nd (a : Seg F) : 0 + a = a := by
  apply Seg.ext
  show F.toX (meet (pline (F.xl : L) (F.toY F.O)) (pline (F.yl : L) a.pt)) = a.pt
  rw [F.toY_O, pline_of_mem F.O_xl, ← eq_meet (not_lpar_pline_right F.nl_xy _) a.mem
    (mem_pline _ _), F.toX_of_mem a.mem]

/-- **Law 5 without Desargues**: `a · 1 = a` and `1 · a = a`. -/
theorem mul_one_nd (a : Seg F) : a * 1 = a := by
  apply Seg.ext
  show F.toX (meet (F.yl : L) (pline (ln F.E (F.toY a.pt) : L) F.E)) = a.pt
  rw [pline_of_mem (mem_ln_left _ _), ← eq_meet (F.nl_EA' a.pt) (F.toY_mem _)
    (mem_ln_right _ _), F.toX_toY _ a.mem]

theorem one_mul_nd (a : Seg F) : 1 * a = a := by
  apply Seg.ext
  show F.toX (meet (F.yl : L) (pline (ln F.E (F.toY F.E) : L) a.pt)) = a.pt
  rw [F.toY_E]
  exact F.toX_toY _ a.mem

/-- The solutions of `a + x = b`: the only candidate is the point of `OE` on the parallel to `OE'`
through the point `A''` of the parallel to `OE` through `A'` on the parallel to `EE'` through `B`. -/
theorem add_left_unique_nd (a b : Seg F) :
    ∃! x : Seg F, a + x = b := by
  set A' := F.toY a.pt
  have h1 : ¬LPar P (pline (F.xl : L) A') (pline (F.ul : L) b.pt) :=
    not_lpar_pline (fun h => F.nl_ux h.symm) _ _
  set A'' := meet (P := P) (pline (F.xl : L) A') (pline (F.ul : L) b.pt)
  have h2 : ¬LPar P (F.xl : L) (pline (F.yl : L) A'') := not_lpar_pline_right F.nl_xy _
  set X := meet (P := P) (F.xl : L) (pline (F.yl : L) A'')
  have hX : X ∈ (F.xl : L) := meet_mem_left h2
  have h3 : ¬LPar P (pline (F.xl : L) A') (pline (F.yl : L) X) := not_lpar_pline F.nl_xy _ _
  -- every `x` with `a + x = b` has `M x = A''`
  have key : ∀ x : Seg F, a + x = b ↔ x.pt = X := by
    intro x
    have hx3 : ¬LPar P (pline (F.xl : L) A') (pline (F.yl : L) x.pt) :=
      not_lpar_pline F.nl_xy _ _
    constructor
    · intro h
      have hb : F.toX (meet (pline (F.xl : L) A') (pline (F.yl : L) x.pt)) = b.pt :=
        congrArg Seg.pt h
      have hM : meet (pline (F.xl : L) A') (pline (F.yl : L) x.pt) = A'' := by
        refine eq_meet h1 (meet_mem_left hx3) ?_
        rw [← hb]; exact pline_symm (F.toX_par _)
      have : x.pt ∈ pline (F.yl : L) A'' := by
        rw [← hM]; exact pline_symm (meet_mem_right hx3)
      exact eq_meet h2 x.mem this
    · intro h
      apply Seg.ext
      show F.toX (meet (pline (F.xl : L) A') (pline (F.yl : L) x.pt)) = b.pt
      rw [h, pline_eq_of_mem (meet_mem_right h2),
        ← eq_meet (not_lpar_pline F.nl_xy _ _) (meet_mem_left h1) (mem_pline _ _)]
      exact (F.toX_eq b.mem (pline_symm (meet_mem_right h1))).symm
  exact ⟨⟨X, hX⟩, (key _).2 rfl, fun x hx => Seg.ext ((key x).1 hx)⟩

theorem add_right_unique_nd (a b : Seg F) :
    ∃! y : Seg F, y + a = b := by
  have h1 : ¬LPar P (pline (F.yl : L) a.pt) (pline (F.ul : L) b.pt) :=
    not_lpar_pline (fun h => F.nl_uy h.symm) _ _
  set A'' := meet (P := P) (pline (F.yl : L) a.pt) (pline (F.ul : L) b.pt)
  have h2 : ¬LPar P (F.yl : L) (pline (F.xl : L) A'') :=
    not_lpar_pline_right (fun h => F.nl_xy h.symm) _
  set Y' := meet (P := P) (F.yl : L) (pline (F.xl : L) A'')
  have hY' : Y' ∈ (F.yl : L) := meet_mem_left h2
  have key : ∀ y : Seg F, y + a = b ↔ y.pt = F.toX Y' := by
    intro y
    have hy3 : ¬LPar P (pline (F.xl : L) (F.toY y.pt)) (pline (F.yl : L) a.pt) :=
      not_lpar_pline F.nl_xy _ _
    constructor
    · intro h
      have hb : F.toX (meet (pline (F.xl : L) (F.toY y.pt)) (pline (F.yl : L) a.pt)) = b.pt :=
        congrArg Seg.pt h
      have hM : meet (pline (F.xl : L) (F.toY y.pt)) (pline (F.yl : L) a.pt) = A'' := by
        refine eq_meet h1 (meet_mem_right hy3) ?_
        rw [← hb]; exact pline_symm (F.toX_par _)
      have : F.toY y.pt ∈ pline (F.xl : L) A'' := by
        rw [← hM]; exact pline_symm (meet_mem_left hy3)
      have e : F.toY y.pt = Y' := eq_meet h2 (F.toY_mem _) this
      rw [← e, F.toX_toY _ y.mem]
    · intro h
      apply Seg.ext
      show F.toX (meet (pline (F.xl : L) (F.toY y.pt)) (pline (F.yl : L) a.pt)) = b.pt
      rw [h, F.toY_toX _ hY', pline_eq_of_mem (meet_mem_right h2),
        ← eq_meet (not_lpar_pline F.nl_xy _ _) (mem_pline _ _) (meet_mem_left h1)]
      exact (F.toX_eq b.mem (pline_symm (meet_mem_right h1))).symm
  exact ⟨⟨F.toX Y', F.toX_mem _⟩, (key _).2 rfl, fun y hy => Seg.ext ((key y).1 hy)⟩

/-- `a · x = b` (`a ≠ 0`): the only candidate is the point of `OE` on the parallel to `EA'` through
the point `C'` of `OE'` "equal" to `b`. -/
theorem mul_left_unique_nd {a : Seg F} (ha : a ≠ 0) (b : Seg F) :
    ∃! x : Seg F, a * x = b := by
  set A' := F.toY a.pt
  set m : L := ln F.E A'
  have hA'O : A' ≠ F.O := fun h => ne_zero_iff_pt.1 ha (by
    rw [← F.toX_toY _ a.mem]; show F.toX A' = F.O; rw [h, F.toX_O])
  have hm : ¬LPar P (F.xl : L) m := by
    refine not_lpar_of F.E_xl (mem_ln_left _ _) fun e => hA'O ?_
    exact F.eq_O_of_mem (by rw [e]; exact mem_ln_right _ _) (F.toY_mem _)
  have hmy : ¬LPar P (F.yl : L) m := F.nl_EA' a.pt
  set C' := F.toY b.pt
  have h2 : ¬LPar P (F.xl : L) (pline m C') := not_lpar_pline_right hm _
  set X := meet (P := P) (F.xl : L) (pline m C')
  have key : ∀ x : Seg F, a * x = b ↔ x.pt = X := by
    intro x
    have hx : ¬LPar P (F.yl : L) (pline m x.pt) := not_lpar_pline_right hmy _
    constructor
    · intro h
      have hb : F.toX (meet (F.yl : L) (pline m x.pt)) = b.pt := congrArg Seg.pt h
      have hM : meet (F.yl : L) (pline m x.pt) = C' :=
        (F.toY_toX _ (meet_mem_left hx)).symm.trans (congrArg F.toY hb)
      have : x.pt ∈ pline m C' := by rw [← hM]; exact pline_symm (meet_mem_right hx)
      exact eq_meet h2 x.mem this
    · intro h
      apply Seg.ext
      show F.toX (meet (F.yl : L) (pline m x.pt)) = b.pt
      rw [h, pline_eq_of_mem (meet_mem_right h2),
        ← eq_meet (not_lpar_pline_right hmy _) (F.toY_mem _) (mem_pline _ _)]
      exact F.toX_toY _ b.mem
  exact ⟨⟨X, meet_mem_left h2⟩, (key _).2 rfl, fun x hx => Seg.ext ((key x).1 hx)⟩

theorem mul_right_unique_nd {a : Seg F} (ha : a ≠ 0) (b : Seg F) :
    ∃! y : Seg F, y * a = b := by
  set C' := F.toY b.pt
  have hAC : a.pt ≠ C' := fun e => pt_not_yl ha (by rw [e]; exact F.toY_mem _)
  set n : L := ln a.pt C'
  have hny : ¬LPar P (F.yl : L) n := by
    refine not_lpar_of (F.toY_mem _) (mem_ln_right _ _) fun e => pt_not_yl ha ?_
    rw [e]; exact mem_ln_left _ _
  have h2 : ¬LPar P (F.yl : L) (pline n F.E) := not_lpar_pline_right hny _
  set Y' := meet (P := P) (F.yl : L) (pline n F.E)
  have hY' : Y' ∈ (F.yl : L) := meet_mem_left h2
  have hEY' : F.E ≠ Y' := fun e => F.E_not_yl (e ▸ hY')
  have key : ∀ y : Seg F, y * a = b ↔ y.pt = F.toX Y' := by
    intro y
    have hy : ¬LPar P (F.yl : L) (pline (ln F.E (F.toY y.pt) : L) a.pt) :=
      not_lpar_pline_right (F.nl_EA' y.pt) _
    have hEy : F.E ≠ F.toY y.pt := fun e => F.E_not_yl (e ▸ F.toY_mem _)
    constructor
    · intro h
      have hb : F.toX (meet (F.yl : L) (pline (ln F.E (F.toY y.pt) : L) a.pt)) = b.pt :=
        congrArg Seg.pt h
      have hM : meet (F.yl : L) (pline (ln F.E (F.toY y.pt) : L) a.pt) = C' :=
        (F.toY_toX _ (meet_mem_left hy)).symm.trans (congrArg F.toY hb)
      have hC : C' ∈ pline (ln F.E (F.toY y.pt) : L) a.pt := hM ▸ meet_mem_right hy
      have e1 : n = pline (ln F.E (F.toY y.pt) : L) a.pt := ln_eq_pline hAC hC
      have e2 : (ln F.E (F.toY y.pt) : L) = pline n F.E := by
        refine eq_pline (mem_ln_left _ _) ?_
        rw [e1]; exact (pline_lpar _ _).symm
      have e3 : F.toY y.pt = Y' := eq_meet h2 (F.toY_mem _) (e2 ▸ mem_ln_right _ _)
      rw [← e3, F.toX_toY _ y.mem]
    · intro h
      apply Seg.ext
      show F.toX (meet (F.yl : L) (pline (ln F.E (F.toY y.pt) : L) a.pt)) = b.pt
      rw [h, F.toY_toX _ hY', ln_eq_pline hEY' (meet_mem_right h2), pline_pline,
        pline_of_mem (mem_ln_left _ _),
        ← eq_meet hny (F.toY_mem _) (mem_ln_right _ _)]
      exact F.toX_toY _ b.mem
  exact ⟨⟨F.toX Y', F.toX_mem _⟩, (key _).2 rfl, fun y hy => Seg.ext ((key y).1 hy)⟩

end Seg

/-- **Laws 1–6 of § 13 for Hilbert's segments, without Desargues's theorem** (only I 1–2, III). -/
theorem seg_laws_1_6_nd (F : Frame P) :
    Law1 (Seg F) ∧ Law2 (Seg F) ∧ Law3 (Seg F) ∧ Law4 (Seg F) ∧ Law5 (Seg F) ∧ Law6 (Seg F) :=
  ⟨law1_holds _, fun a => ⟨Seg.add_zero_nd a, Seg.zero_add_nd a⟩,
    fun a b => ⟨Seg.add_left_unique_nd a b, Seg.add_right_unique_nd a b⟩, law4_holds _,
    fun a => ⟨Seg.mul_one_nd a, Seg.one_mul_nd a⟩,
    fun _ b ha => ⟨Seg.mul_left_unique_nd ha b, Seg.mul_right_unique_nd ha b⟩⟩

/-- **Co-ordinates without Desargues** (§ 27): the co-ordinates determine the point and every pair
of segments is the pair of co-ordinates of a point (I 1–2, III only). -/
theorem coords_bijective_nd (F : Frame P) :
    Function.Bijective (fun X : P => (F.xc X, F.yc X)) := by
  have hyx : ∀ X Y : P, ¬LPar P (pline (F.yl : L) X) (pline (F.xl : L) Y) :=
    not_lpar_pline (fun h => F.nl_xy h.symm)
  constructor
  · intro X Y h
    have hx : meet (F.xl : L) (pline (F.yl : L) X) = meet (P := P) (F.xl : L) (pline (F.yl : L) Y) :=
      congrArg Seg.pt (Prod.ext_iff.1 h).1
    have hy : meet (F.yl : L) (pline (F.xl : L) X) = meet (P := P) (F.yl : L) (pline (F.xl : L) Y) :=
      F.toX_injOn (F.yproj_mem X) (F.yproj_mem Y) (congrArg Seg.pt (Prod.ext_iff.1 h).2)
    have e1 : pline (F.yl : L) X = pline (F.yl : L) Y := by
      rw [← pline_eq_of_mem (F.xc_par X), ← pline_eq_of_mem (F.xc_par Y)]
      exact congrArg (pline (F.yl : L)) hx
    have e2 : pline (F.xl : L) X = pline (F.xl : L) Y := by
      rw [← pline_eq_of_mem (F.yproj_par X), ← pline_eq_of_mem (F.yproj_par Y)]
      exact congrArg (pline (F.xl : L)) hy
    refine eq_of_mem_not_lpar (hyx Y Y) ?_ ?_ (mem_pline _ _) (mem_pline _ _)
    · rw [← e1]; exact mem_pline _ _
    · rw [← e2]; exact mem_pline _ _
  · rintro ⟨x, y⟩
    set X := meet (P := P) (pline (F.yl : L) x.pt) (pline (F.xl : L) (F.toY y.pt))
    have hX1 : X ∈ pline (F.yl : L) x.pt := meet_mem_left (hyx _ _)
    have hX2 : X ∈ pline (F.xl : L) (F.toY y.pt) := meet_mem_right (hyx _ _)
    refine ⟨X, Prod.ext (Seg.ext ?_) (Seg.ext ?_)⟩
    · show meet (F.xl : L) (pline (F.yl : L) X) = x.pt
      rw [pline_eq_of_mem hX1]
      exact (eq_meet (not_lpar_pline_right F.nl_xy _) x.mem (mem_pline _ _)).symm
    · show F.toX (meet (F.yl : L) (pline (F.xl : L) X)) = y.pt
      rw [pline_eq_of_mem hX2, ← eq_meet (not_lpar_pline_right (fun h => F.nl_xy h.symm) _)
        (F.toY_mem _) (mem_pline _ _)]
      exact F.toX_toY _ y.mem

end Laws16

/-! ## Laws 13, 14 and Hilbert's degenerate order convention, from the axioms of order -/

section OrderLaws

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L] {F : Frame P}

/-- **Laws 13, 14 and the asymmetry of 13** for Hilbert's order (II 1–4 on the line `OE`; no
Desargues). -/
theorem seg_laws_13_14_nd (F : Frame P) :
    Law13 (Seg F) ∧ Law13Asymm (Seg F) ∧ Law14 (Seg F) :=
  ⟨fun _ _ h => (lt_or_gt_of_ne h).symm, fun _ _ h h' => lt_asymm h h',
    fun _ _ _ h1 h2 => h2.trans h1⟩

theorem zero_lt_iff_seq {b : Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    0 < b ↔ Between F.O b.pt F.E ∨ Between F.O F.E b.pt := by
  have h01 : (0 : Seg F) ≠ 1 := fun h => F.hOE (congrArg Seg.pt h)
  have hoe : (0 : Seg F) < 1 := Seg.zero_lt_one'
  rw [show F.O = (0 : Seg F).pt from rfl, show F.E = (1 : Seg F).pt from rfl,
    Seg.between_iff hb0.symm h01 hb1, Seg.between_iff h01 hb0.symm hb1.symm]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hb1 with h1 | h1
    · exact Or.inl (Or.inl ⟨h, h1⟩)
    · exact Or.inr (Or.inl ⟨hoe, h1⟩)
  · rintro ((⟨h, -⟩ | ⟨h1, h2⟩) | (⟨-, h⟩ | ⟨-, h⟩))
    · exact h
    · exact absurd (hoe.trans (h1.trans h2)) (lt_irrefl _)
    · exact hoe.trans h
    · exact absurd (hoe.trans h) (lt_irrefl _)

theorem lt_zero_iff_seq {b : Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    b < 0 ↔ Between b.pt F.O F.E := by
  have h01 : (0 : Seg F) ≠ 1 := fun h => F.hOE (congrArg Seg.pt h)
  have hoe : (0 : Seg F) < 1 := Seg.zero_lt_one'
  rw [show F.O = (0 : Seg F).pt from rfl, show F.E = (1 : Seg F).pt from rfl,
    Seg.between_iff hb0 hb1 h01]
  constructor
  · intro h; exact Or.inl ⟨h, hoe⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd (hoe.trans h) (lt_irrefl _)

theorem one_lt_iff_seq {b : Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    1 < b ↔ Between F.O F.E b.pt := by
  have h01 : (0 : Seg F) ≠ 1 := fun h => F.hOE (congrArg Seg.pt h)
  have hoe : (0 : Seg F) < 1 := Seg.zero_lt_one'
  rw [show F.O = (0 : Seg F).pt from rfl, show F.E = (1 : Seg F).pt from rfl,
    Seg.between_iff h01 hb0.symm hb1.symm]
  constructor
  · intro h; exact Or.inl ⟨hoe, h⟩
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact h
    · exact absurd (hoe.trans h) (lt_irrefl _)

theorem lt_one_iff_seq {b : Seg F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    b < 1 ↔ Between b.pt F.O F.E ∨ Between F.O b.pt F.E := by
  have h01 : (0 : Seg F) ≠ 1 := fun h => F.hOE (congrArg Seg.pt h)
  have hoe : (0 : Seg F) < 1 := Seg.zero_lt_one'
  rw [show F.O = (0 : Seg F).pt from rfl, show F.E = (1 : Seg F).pt from rfl,
    Seg.between_iff hb0 hb1 h01, Seg.between_iff hb0.symm h01 hb1]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hb0 with h0 | h0
    · exact Or.inl (Or.inl ⟨h0, hoe⟩)
    · exact Or.inr (Or.inl ⟨h0, h⟩)
  · rintro ((⟨h1, h2⟩ | ⟨h, -⟩) | (⟨-, h⟩ | ⟨h1, h2⟩))
    · exact h1.trans h2
    · exact absurd (hoe.trans h) (lt_irrefl _)
    · exact h
    · exact absurd ((hoe.trans h1).trans h2) (lt_irrefl _)

end OrderLaws

/-! ## The line through the origin (§ 27) -/

section OriginLine

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L] [hDF : Fact (DesarguesII P)] {F : Frame P}

/-- The foot on the second axis of the parallel to the first axis through `X`. -/
noncomputable def Frame.yfoot (F : Frame P) (X : P) : P := meet (F.yl : L) (pline (F.xl : L) X)

theorem yfoot_mem (X : P) : F.yfoot X ∈ (F.yl : L) := F.yproj_mem X

/-- If `y = e x` with `x ≠ 0`, the line `g` joining the feet of `X` on the two axes is the parallel
through the foot on the first axis to the line `h = EE₁`, `E₁` the point of the second axis equal to
`e`. -/
theorem g_eq_pline {X : P} {e : Seg F} (hX : F.yc X = e * F.xc X) (hx : F.xc X ≠ 0) :
    (ln (F.xc X).pt (F.yfoot X) : L) = pline (ln F.E (F.toY e.pt) : L) (F.xc X).pt := by
  have hy : (F.yc X).pt = (e * F.xc X).pt := congrArg Seg.pt hX
  have h1 : F.yfoot X = meet (F.yl : L) (pline (ln F.E (F.toY e.pt) : L) (F.xc X).pt) :=
    F.toX_injOn (yfoot_mem X) (meet_mem_left (not_lpar_pline_right (F.nl_EA' e.pt) _)) hy
  have hne : (F.xc X).pt ≠ F.yfoot X := fun h =>
    Seg.pt_not_yl hx (by rw [h]; exact yfoot_mem X)
  refine ln_eq_pline hne ?_
  rw [h1]; exact meet_mem_right (not_lpar_pline_right (F.nl_EA' e.pt) _)

/-- **Hilbert's construction of `e`** (§ 27, Fig. 48): for a line `l` through `O` other than the
second axis and a point `C ≠ O` of `l` with feet `A` (on the first axis) and `B` (on the second),
the parallel `h` to `AB` through `E` cuts off on the second axis the segment `e`, the line `g`
joining the feet of any point `X ≠ O` of `l` is parallel to `AB`, and the points of `l` are exactly
the solutions of `e x = y`. -/
theorem origin_line_hilbert {l : L} (hO : F.O ∈ l) (hl : l ≠ F.yl) {C : P} (hC : C ∈ l)
    (hCO : C ≠ F.O) :
    (∀ X : P, X ∈ l → X ≠ F.O →
      LPar P (ln (F.xc X).pt (F.yfoot X) : L) (ln (F.xc C).pt (F.yfoot C))) ∧
    ∀ X : P, X ∈ l ↔ F.yc X =
      ⟨F.toX (meet (F.yl : L) (pline (ln (F.xc C).pt (F.yfoot C) : L) F.E)), F.toX_mem _⟩ *
        F.xc X := by
  obtain ⟨e, he⟩ := origin_line (F := F) hO hl
  have hx : ∀ X : P, X ∈ l → X ≠ F.O → F.xc X ≠ 0 := by
    intro X hX hXO h0
    have hy : F.yc X = 0 := by rw [(he X).1 hX, h0, mul_zero]
    exact hXO (eq_of_coords (F := F) (by rw [h0, xc_O]) (by rw [hy, yc_O]))
  have hg : ∀ X : P, X ∈ l → X ≠ F.O →
      (ln (F.xc X).pt (F.yfoot X) : L) = pline (ln F.E (F.toY e.pt) : L) (F.xc X).pt :=
    fun X hX hXO => g_eq_pline ((he X).1 hX) (hx X hX hXO)
  have hh : pline (ln (F.xc C).pt (F.yfoot C) : L) F.E = ln F.E (F.toY e.pt) := by
    rw [hg C hC hCO, pline_pline, pline_of_mem (mem_ln_left _ _)]
  have hee : (⟨F.toX (meet (F.yl : L) (pline (ln (F.xc C).pt (F.yfoot C) : L) F.E)),
      F.toX_mem _⟩ : Seg F) = e := by
    apply Seg.ext
    show F.toX (meet (F.yl : L) (pline (ln (F.xc C).pt (F.yfoot C) : L) F.E)) = e.pt
    rw [hh, ← eq_meet (F.nl_EA' e.pt) (F.toY_mem _) (mem_ln_right _ _), F.toX_toY _ e.mem]
  refine ⟨fun X hX hXO => ?_, fun X => by rw [hee]; exact he X⟩
  rw [hg X hX hXO, hg C hC hCO]
  exact (pline_lpar _ _).trans (pline_lpar _ _).symm

/-- In the step `x' = x + c` of § 27 the points `P'` and `P` have the same second co-ordinate
(they lie on one parallel to the first axis). -/
theorem yc_eq_of_pline {P' Q : P} (hQP : Q ∈ pline (F.xl : L) P') : F.yc Q = F.yc P' :=
  Seg.ext (by show F.toX _ = F.toX _; rw [pline_eq_of_mem hQP])

end OriginLine

/-! ## The literal second part of Desargues's theorem -/

section Literal

/-- **The second part of Desargues's theorem read literally** (Theorem 32: "if the straight lines
joining the corresponding vertices meet in a point or are parallel, and two pairs of corresponding
sides are parallel, then the third sides are parallel"), with "parallel" meaning "without common
point" and without requiring the three joining lines to be distinct. -/
def DesarguesIILiteral (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  ∀ (A B C A' B' C' : P) (a b c : L), ¬Collinear A B C → ¬Collinear A' B' C' →
    A ∈ a → A' ∈ a → B ∈ b → B' ∈ b → C ∈ c → C' ∈ c →
    ConcurrentOrParallel P a b c → ParPts A B A' B' → ParPts A C A' C' → ParPts B C B' C'

theorem desarguesII_of_literal {P : Type u} {L : Type v} [HasLines P L]
    (h : DesarguesIILiteral P) : DesarguesII P :=
  fun A B C A' B' C' a b c h1 h2 hA hA' hB hB' hC hC' _ _ _ hcp hp1 hp2 =>
    h A B C A' B' C' a b c h1 h2 hA hA' hB hB' hC hC' hcp hp1 hp2

/-- The point `(x, y)` of the real plane. -/
noncomputable abbrev rpt (x y : ℝ) : Coord ℝ 2 := Coord.pt2 x y

theorem coords_of_mem_through {A B X : Coord ℝ 2} (h : A ≠ B) (hX : X ∈ AffLine.through A B h) :
    ∃ r : ℝ, Coord.xc X = r * (Coord.xc B - Coord.xc A) + Coord.xc A ∧
      Coord.yc X = r * (Coord.yc B - Coord.yc A) + Coord.yc A := by
  obtain ⟨r, hr⟩ := (AffLine.mem_through_iff h).1 hX
  exact ⟨r, by rw [hr]; simp, by rw [hr]; simp⟩

theorem mem_through_of_coords {A B X : Coord ℝ 2} (h : A ≠ B) (r : ℝ)
    (hx : Coord.xc X = r * (Coord.xc B - Coord.xc A) + Coord.xc A)
    (hy : Coord.yc X = r * (Coord.yc B - Coord.yc A) + Coord.yc A) :
    X ∈ AffLine.through A B h :=
  (AffLine.mem_through_iff h).2 ⟨r, Coord.ext2 (by simp [hx]) (by simp [hy])⟩

theorem rpt_ne {x y x' y' : ℝ} (h : x ≠ x' ∨ y ≠ y') : rpt x y ≠ rpt x' y' := fun e => by
  rcases h with h | h
  · exact h (by simpa using congrArg Coord.xc e)
  · exact h (by simpa using congrArg Coord.yc e)

theorem not_collinear_of_not_mem {A B C : Coord ℝ 2} (h : A ≠ B)
    (hC : C ∉ AffLine.through A B h) : ¬Collinear A B C := by
  rintro ⟨m, hA, hB, hC'⟩
  rw [AffLine.eq_through m h hA hB] at hC'
  exact hC hC'

/-- **The literal second part of Desargues's theorem is false in the real plane**: `O = (0,0)`,
`A = (0,1)`, `A' = (0,2)`, `B = (1,0)`, `B' = (2,0)`, `C = (-1,0)`, `C' = (-2,0)`; the joining lines
`AA'` (the `y`-axis) and `BB' = CC'` (the `x`-axis) pass through `O`, `AB ∥ A'B'`, `AC ∥ A'C'`, but
`BC` and `B'C'` are the same line. -/
theorem not_desarguesIILiteral_real : ¬DesarguesIILiteral (Coord ℝ 2) := by
  intro hD
  have hOA : rpt 0 0 ≠ rpt 0 1 := rpt_ne (Or.inr (by norm_num))
  have hAB : rpt 0 1 ≠ rpt 1 0 := rpt_ne (Or.inl (by norm_num))
  have hAC : rpt 0 1 ≠ rpt (-1) 0 := rpt_ne (Or.inl (by norm_num))
  have hBC : rpt 1 0 ≠ rpt (-1) 0 := rpt_ne (Or.inl (by norm_num))
  have hA'B' : rpt 0 2 ≠ rpt 2 0 := rpt_ne (Or.inl (by norm_num))
  have hA'C' : rpt 0 2 ≠ rpt (-2) 0 := rpt_ne (Or.inl (by norm_num))
  have n1 : ¬Collinear (rpt 0 1) (rpt 1 0) (rpt (-1) 0) := by
    refine not_collinear_of_not_mem hAB fun h => ?_
    obtain ⟨r, hx, hy⟩ := coords_of_mem_through hAB h
    simp at hx hy; linarith
  have n2 : ¬Collinear (rpt 0 2) (rpt 2 0) (rpt (-2) 0) := by
    refine not_collinear_of_not_mem hA'B' fun h => ?_
    obtain ⟨r, hx, hy⟩ := coords_of_mem_through hA'B' h
    simp at hx hy; linarith
  have hA'a : rpt 0 2 ∈ AffLine.through (rpt 0 0) (rpt 0 1) hOA :=
    mem_through_of_coords hOA 2 (by simp) (by simp)
  have hB'b : rpt 2 0 ∈ AffLine.through (rpt 1 0) (rpt (-1) 0) hBC :=
    mem_through_of_coords hBC (-1 / 2) (by simp; norm_num) (by simp)
  have hC'b : rpt (-2) 0 ∈ AffLine.through (rpt 1 0) (rpt (-1) 0) hBC :=
    mem_through_of_coords hBC (3 / 2) (by simp; norm_num) (by simp)
  have hOb : rpt 0 0 ∈ AffLine.through (rpt 1 0) (rpt (-1) 0) hBC :=
    mem_through_of_coords hBC (1 / 2) (by simp; norm_num) (by simp)
  have p1 : ParPts (rpt 0 1) (rpt 1 0) (rpt 0 2) (rpt 2 0) := by
    refine ⟨AffLine.through _ _ hAB, AffLine.through _ _ hA'B', AffLine.left_mem_through hAB,
      AffLine.right_mem_through hAB, AffLine.left_mem_through hA'B',
      AffLine.right_mem_through hA'B', ?_⟩
    rintro ⟨X, h1, h2⟩
    obtain ⟨r, hx, hy⟩ := coords_of_mem_through hAB h1
    obtain ⟨s, hx', hy'⟩ := coords_of_mem_through hA'B' h2
    simp at hx hy hx' hy'; linarith
  have p2 : ParPts (rpt 0 1) (rpt (-1) 0) (rpt 0 2) (rpt (-2) 0) := by
    refine ⟨AffLine.through _ _ hAC, AffLine.through _ _ hA'C', AffLine.left_mem_through hAC,
      AffLine.right_mem_through hAC, AffLine.left_mem_through hA'C',
      AffLine.right_mem_through hA'C', ?_⟩
    rintro ⟨X, h1, h2⟩
    obtain ⟨r, hx, hy⟩ := coords_of_mem_through hAC h1
    obtain ⟨s, hx', hy'⟩ := coords_of_mem_through hA'C' h2
    simp at hx hy hx' hy'; linarith
  obtain ⟨l1, l2, k1, k2, k3, -, hn⟩ := hD (rpt 0 1) (rpt 1 0) (rpt (-1) 0) (rpt 0 2) (rpt 2 0)
    (rpt (-2) 0) (AffLine.through _ _ hOA) (AffLine.through _ _ hBC) (AffLine.through _ _ hBC)
    n1 n2 (AffLine.right_mem_through hOA) hA'a (AffLine.left_mem_through hBC) hB'b
    (AffLine.right_mem_through hBC) hC'b
    (Or.inl ⟨rpt 0 0, AffLine.left_mem_through hOA, hOb, hOb⟩) p1 p2
  rw [AffLine.eq_through l1 hBC k1 k2] at hn
  exact hn ⟨rpt 2 0, hB'b, k3⟩

end Literal

/-! ## Every plane of the space of § 29 is given by an equation -/

section PlaneConverse

variable {D : Type*} [DivisionRing D]

open MulOpposite

/-- **Every plane of `Coord Dᵐᵒᵖ 3` is the solution set of an equation `u x + v y + w z + r = 0`**
with left coefficients and `(u, v, w) ≠ 0` (the converse of `equation_plane`). -/
theorem plane_eq_equation (π : CoordPlane Dᵐᵒᵖ 3) :
    ∃ u v w r : D, (u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) ∧ ∀ X : Coord Dᵐᵒᵖ 3, X ∈ π ↔
      u * unop (AffPt.toV X 0) + v * unop (AffPt.toV X 1) + w * unop (AffPt.toV X 2) + r = 0 := by
  have : Module.Finite Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) :=
    inferInstanceAs (Module.Finite Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ))
  have hdim : Module.finrank Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) = 3 :=
    Module.finrank_fin_fun Dᵐᵒᵖ
  have hW : Module.finrank Dᵐᵒᵖ π.carrier.direction = 2 := π.finrank_direction
  have hlt : π.carrier.direction < ⊤ := lt_top_iff_ne_top.2 fun h => by
    rw [h, finrank_top, hdim] at hW; omega
  obtain ⟨f, hf0, hWf⟩ := π.carrier.direction.exists_le_ker_of_lt_top hlt
  have hk : Module.finrank Dᵐᵒᵖ (LinearMap.ker f) < 3 := by
    have := Submodule.finrank_lt (s := LinearMap.ker f) fun h => hf0 (LinearMap.ker_eq_top.1 h)
    rwa [hdim] at this
  have hWeq : π.carrier.direction = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_le hWf (by omega)
  set c : Fin 3 → Dᵐᵒᵖ := fun i => f (AffPt.ofV (fun j => if i = j then 1 else 0))
  have hfX : ∀ X : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ), f X = ∑ i, AffPt.toV X i * c i := fun X =>
    LinearMap.pi_apply_eq_sum_univ (f : (Fin 3 → Dᵐᵒᵖ) →ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ) X
  have hunop : ∀ X : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ), unop (f X) =
      unop (c 0) * unop (AffPt.toV X 0) + unop (c 1) * unop (AffPt.toV X 1) +
        unop (c 2) * unop (AffPt.toV X 2) := fun X => by
    rw [hfX, Fin.sum_univ_three, unop_add, unop_add, unop_mul, unop_mul, unop_mul]
  obtain ⟨X0, hX0⟩ := AffPt.nonempty_plane π
  refine ⟨unop (c 0), unop (c 1), unop (c 2), unop (-f X0), ?_, fun X => ?_⟩
  · by_contra hall
    simp only [not_or, not_not, unop_eq_zero_iff] at hall
    apply hf0
    apply LinearMap.ext
    intro X
    rw [hfX, Fin.sum_univ_three, hall.1, hall.2.1, hall.2.2]
    simp
  · show X ∈ π.carrier ↔ _
    rw [AffPt.mem_iff_sub_mem_direction hX0, hWeq, LinearMap.mem_ker, map_sub, ← hunop,
      ← unop_add, ← sub_eq_add_neg, unop_eq_zero_iff]

end PlaneConverse

/-! ## Hilbert's lines in the space of § 29: two planes -/

section LineConverse

variable {D : Type*} [DivisionRing D]

open MulOpposite

/-- Hilbert's linear expression `u x + v y + w z` (coefficients on the left) at a point of
`Coord Dᵐᵒᵖ 3`. -/
def lin3 (u v w : D) (X : Coord Dᵐᵒᵖ 3) : D :=
  u * unop (AffPt.toV X 0) + v * unop (AffPt.toV X 1) + w * unop (AffPt.toV X 2)

/-- **Hilbert's condition on the two planes of a line** (§ 29): it is impossible to find two numbers
`a', a''` different from zero with `a'u' = a''u''`, `a'v' = a''v''`, `a'w' = a''w''`. -/
def HilbertIndep (u' v' w' u'' v'' w'' : D) : Prop :=
  ¬∃ a' a'' : D, a' ≠ 0 ∧ a'' ≠ 0 ∧ a' * u' = a'' * u'' ∧ a' * v' = a'' * v'' ∧ a' * w' = a'' * w''

/-- The basis vector `eᵢ` of `Coord Dᵐᵒᵖ 3`. -/
def ebas (i : Fin 3) : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ) := AffPt.ofV (fun j => if i = j then 1 else 0)

theorem functional_lin3 (f : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ) →ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ)
    (X : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) :
    unop (f X) = lin3 (unop (f (ebas 0))) (unop (f (ebas 1))) (unop (f (ebas 2))) X := by
  have h : f X = ∑ i, AffPt.toV X i * f (ebas i) :=
    LinearMap.pi_apply_eq_sum_univ (f : (Fin 3 → Dᵐᵒᵖ) →ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ) X
  rw [h, Fin.sum_univ_three, unop_add, unop_add, unop_mul, unop_mul, unop_mul]; rfl

theorem functional_coeff_ne_zero {f : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ) →ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ} (hf : f ≠ 0) :
    unop (f (ebas 0)) ≠ 0 ∨ unop (f (ebas 1)) ≠ 0 ∨ unop (f (ebas 2)) ≠ 0 := by
  by_contra hall
  simp only [not_or, not_not] at hall
  apply hf
  apply LinearMap.ext
  intro X
  apply unop_injective
  rw [functional_lin3, lin3, hall.1, hall.2.1, hall.2.2]
  simp

theorem unop_eqForm' (u v w : D) (X : Coord Dᵐᵒᵖ 3) :
    unop (eqForm ![op u, op v, op w] X) = lin3 u v w X := unop_eqForm u v w X

/-- **Hilbert's line** (§ 29): for two planes `(u':v':w':r')`, `(u'':v'':w'':r'')` satisfying his
condition, the common points form a line of the space `Coord Dᵐᵒᵖ 3`. -/
theorem hilbert_line_of_planes {u' v' w' r' u'' v'' w'' r'' : D} (h1 : u' ≠ 0 ∨ v' ≠ 0 ∨ w' ≠ 0)
    (h2 : u'' ≠ 0 ∨ v'' ≠ 0 ∨ w'' ≠ 0) (hind : HilbertIndep u' v' w' u'' v'' w'') :
    ∃ ℓ : CoordLine Dᵐᵒᵖ 3, ∀ X : Coord Dᵐᵒᵖ 3,
      X ∈ ℓ ↔ lin3 u' v' w' X + r' = 0 ∧ lin3 u'' v'' w'' X + r'' = 0 := by
  set f1 := eqForm (![op u', op v', op w'] : Fin 3 → Dᵐᵒᵖ)
  set f2 := eqForm (![op u'', op v'', op w''] : Fin 3 → Dᵐᵒᵖ)
  set g := f1.prod f2
  have : Module.Finite Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) :=
    inferInstanceAs (Module.Finite Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ))
  have hdim : Module.finrank Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) = 3 :=
    Module.finrank_fin_fun Dᵐᵒᵖ
  have hsurj : LinearMap.range g = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := (LinearMap.range g).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    have hφab : ∀ a b : Dᵐᵒᵖ, φ (a, b) = a * φ (1, 0) + b * φ (0, 1) := by
      intro a b
      have e : ((a, b) : Dᵐᵒᵖ × Dᵐᵒᵖ) = a • ((1 : Dᵐᵒᵖ), (0 : Dᵐᵒᵖ)) + b • ((0 : Dᵐᵒᵖ), (1 : Dᵐᵒᵖ)) := by
        ext <;> simp
      rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hzero : ∀ X, f1 X * φ (1, 0) + f2 X * φ (0, 1) = 0 := fun X => by
      rw [← hφab]; exact hφ ⟨X, rfl⟩
    -- at the basis vectors
    have hc : ∀ i : Fin 3, unop (φ (1, 0)) * unop (f1 (ebas i)) =
        -unop (φ (0, 1)) * unop (f2 (ebas i)) := by
      intro i
      have := congrArg unop (hzero (ebas i))
      rw [unop_add, unop_mul, unop_mul, unop_zero] at this
      rw [neg_mul, eq_neg_iff_add_eq_zero, this]
    have hf1 : ∀ i, unop (f1 (ebas i)) = (![u', v', w'] : Fin 3 → D) i := by
      intro i; fin_cases i <;> simp [f1, ebas, eqForm_apply]
    have hf2 : ∀ i, unop (f2 (ebas i)) = (![u'', v'', w''] : Fin 3 → D) i := by
      intro i; fin_cases i <;> simp [f2, ebas, eqForm_apply]
    have hφ' : φ (1, 0) ≠ 0 ∨ φ (0, 1) ≠ 0 := by
      by_contra hall
      simp only [not_or, not_not] at hall
      apply hφ0
      apply LinearMap.ext
      rintro ⟨a, b⟩
      rw [hφab, hall.1, hall.2]; simp
    by_cases hα : φ (1, 0) = 0
    · have hβ : unop (φ (0, 1)) ≠ 0 := by
        rw [Ne, unop_eq_zero_iff]; exact hφ'.resolve_left (not_not.2 hα)
      have : ∀ i, (![u'', v'', w''] : Fin 3 → D) i = 0 := by
        intro i
        have := hc i
        rw [hα, unop_zero, zero_mul, neg_mul, zero_eq_neg, hf2] at this
        exact (mul_eq_zero.1 this).resolve_left hβ
      rcases h2 with h | h | h
      · exact h (this 0)
      · exact h (this 1)
      · exact h (this 2)
    · by_cases hβ : φ (0, 1) = 0
      · have hα' : unop (φ (1, 0)) ≠ 0 := by rw [Ne, unop_eq_zero_iff]; exact hα
        have : ∀ i, (![u', v', w'] : Fin 3 → D) i = 0 := by
          intro i
          have := hc i
          rw [hβ, unop_zero, neg_zero, zero_mul, hf1] at this
          exact (mul_eq_zero.1 this).resolve_left hα'
        rcases h1 with h | h | h
        · exact h (this 0)
        · exact h (this 1)
        · exact h (this 2)
      · refine hind ⟨unop (φ (1, 0)), -unop (φ (0, 1)), by rw [Ne, unop_eq_zero_iff]; exact hα,
          by rw [Ne, neg_eq_zero, unop_eq_zero_iff]; exact hβ, ?_, ?_, ?_⟩
        · have := hc 0; rw [hf1, hf2] at this; simpa using this
        · have := hc 1; rw [hf1, hf2] at this; simpa using this
        · have := hc 2; rw [hf1, hf2] at this; simpa using this
  have hker : Module.finrank Dᵐᵒᵖ (LinearMap.ker g) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker g
    rw [hsurj, finrank_top, Module.finrank_prod, Module.finrank_self, hdim] at this
    omega
  obtain ⟨X0, hX0⟩ : ∃ X0, g X0 = (op (-r'), op (-r'')) :=
    LinearMap.range_eq_top.1 hsurj _
  refine ⟨⟨AffineSubspace.mk' X0 (LinearMap.ker g), by rw [AffineSubspace.direction_mk']; exact hker⟩,
    fun X => ?_⟩
  show X ∈ AffineSubspace.mk' X0 _ ↔ _
  rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hX0, sub_eq_zero]
  show (f1 X, f2 X) = (op (-r'), op (-r'')) ↔ _
  rw [Prod.mk.injEq, ← unop_inj, ← unop_inj (x := f2 X), unop_op, unop_op, unop_eqForm',
    unop_eqForm', eq_neg_iff_add_eq_zero, eq_neg_iff_add_eq_zero]

/-- **Every line of the space of § 29 is a line of Hilbert's**: it is the set of common points of
two planes `(u':v':w':r')`, `(u'':v'':w'':r'')` satisfying Hilbert's condition. -/
theorem line_eq_hilbert_line (ℓ : CoordLine Dᵐᵒᵖ 3) :
    ∃ u' v' w' r' u'' v'' w'' r'' : D, (u' ≠ 0 ∨ v' ≠ 0 ∨ w' ≠ 0) ∧
      (u'' ≠ 0 ∨ v'' ≠ 0 ∨ w'' ≠ 0) ∧ HilbertIndep u' v' w' u'' v'' w'' ∧
      ∀ X : Coord Dᵐᵒᵖ 3, X ∈ ℓ ↔ lin3 u' v' w' X + r' = 0 ∧ lin3 u'' v'' w'' X + r'' = 0 := by
  have : Module.Finite Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) :=
    inferInstanceAs (Module.Finite Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ))
  have hdim : Module.finrank Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) = 3 :=
    Module.finrank_fin_fun Dᵐᵒᵖ
  set U := ℓ.carrier.direction
  have hU : Module.finrank Dᵐᵒᵖ U = 1 := ℓ.finrank_direction
  have hlt : U < ⊤ := lt_top_iff_ne_top.2 fun h => by
    rw [h, finrank_top, hdim] at hU; omega
  obtain ⟨f1, hf10, hUf1⟩ := U.exists_le_ker_of_lt_top hlt
  have hk1 : Module.finrank Dᵐᵒᵖ (LinearMap.ker f1) = 2 := by
    have h3 := Submodule.finrank_lt (s := LinearMap.ker f1) fun h => hf10 (LinearMap.ker_eq_top.1 h)
    have hrk := LinearMap.finrank_range_add_finrank_ker f1
    have hr := Submodule.finrank_le (LinearMap.range f1)
    rw [Module.finrank_self] at hr
    rw [hdim] at h3 hrk
    omega
  have hUne : U ≠ LinearMap.ker f1 := fun h => by rw [h, hk1] at hU; omega
  obtain ⟨v, hv1, hvU⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hUf1 hUne)
  obtain ⟨f2, hf2v, hUf2⟩ := U.exists_le_ker_of_notMem hvU
  have hf20 : f2 ≠ 0 := fun h => hf2v (by rw [h]; rfl)
  have hinf : U = LinearMap.ker f1 ⊓ LinearMap.ker f2 := by
    refine Submodule.eq_of_le_of_finrank_le (le_inf hUf1 hUf2) ?_
    have hlt2 : LinearMap.ker f1 ⊓ LinearMap.ker f2 < LinearMap.ker f1 :=
      lt_of_le_of_ne inf_le_left fun h => hf2v (by
        have : v ∈ LinearMap.ker f1 ⊓ LinearMap.ker f2 := by rw [h]; exact hv1
        exact (Submodule.mem_inf.1 this).2)
    have := Submodule.finrank_lt_finrank_of_lt hlt2
    omega
  obtain ⟨X0, hX0⟩ := AffLine.nonempty ℓ
  refine ⟨unop (f1 (ebas 0)), unop (f1 (ebas 1)), unop (f1 (ebas 2)), unop (-f1 X0),
    unop (f2 (ebas 0)), unop (f2 (ebas 1)), unop (f2 (ebas 2)), unop (-f2 X0),
    functional_coeff_ne_zero hf10, functional_coeff_ne_zero hf20, ?_, fun X => ?_⟩
  · rintro ⟨a', a'', ha', ha'', e0, e1, e2⟩
    have key : ∀ X, a' * unop (f1 X) = a'' * unop (f2 X) := fun X => by
      rw [functional_lin3 f1, functional_lin3 f2, lin3, lin3, mul_add, mul_add, mul_add, mul_add,
        ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, e0, e1, e2]
    have := key v
    rw [LinearMap.mem_ker.1 hv1, unop_zero, mul_zero] at this
    exact hf2v (unop_injective ((mul_eq_zero.1 this.symm).resolve_left ha''))
  · show X ∈ ℓ.carrier ↔ _
    rw [AffPt.mem_iff_sub_mem_direction hX0, show ℓ.carrier.direction = _ from hinf, Submodule.mem_inf, LinearMap.mem_ker,
      LinearMap.mem_ker, map_sub, map_sub, ← functional_lin3, ← functional_lin3, ← unop_add,
      ← unop_add, ← sub_eq_add_neg, ← sub_eq_add_neg, unop_eq_zero_iff, unop_eq_zero_iff]

end LineConverse

/-! ## Coordinate spaces in any number of dimensions (§ 30) -/

section AnyDim

variable {K : Type*} [DivisionRing K]

/-- The embedding of `K³` into `Kⁿ` (`n ≥ 3`): `(x, y, z) ↦ (x, y, z, 0, …, 0)`. -/
def ext3 (n : ℕ) : AffPt K (Fin 3 → K) →ₗ[K] AffPt K (Fin n → K) where
  toFun X := AffPt.ofV (fun i => if hi : i.val < 3 then AffPt.toV X ⟨i.val, hi⟩ else 0)
  map_add' X Y := by
    apply AffPt.toV_injective; funext i
    simp only [AffPt.toV_ofV, AffPt.toV_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c X := by
    apply AffPt.toV_injective; funext i
    simp only [AffPt.toV_ofV, AffPt.toV_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem ext3_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (ext3 (K := K) n) := by
  intro X Y h
  apply AffPt.toV_injective; funext j
  have := congrFun (congrArg AffPt.toV h) ⟨j.val, by omega⟩
  simpa [ext3, j.isLt] using this

/-- **The coordinate space `K³` is a part of the coordinate geometry `Kⁿ` for every `n ≥ 3`**:
`ext3` is injective, preserves and reflects betweenness, and maps every line and every plane onto
the points of an affine subspace of dimension 1, resp. 2, of `Kⁿ`. -/
theorem coord3_any_dimension [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ} (hn : 3 ≤ n) :
    ∃ f : Coord K 3 → AffPt K (Fin n → K), Function.Injective f ∧
      (∀ A B C : Coord K 3, Between A B C ↔ Sbtw K (f A) (f B) (f C)) ∧
      (∀ l : CoordLine K 3, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        Module.finrank K S.direction = 1 ∧ ∀ X : Coord K 3, X ∈ l ↔ f X ∈ S) ∧
      (∀ π : CoordPlane K 3, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        Module.finrank K S.direction = 2 ∧ ∀ X : Coord K 3, X ∈ π ↔ f X ∈ S) := by
  have hinj := ext3_injective (K := K) hn
  have hinj' : Function.Injective (ext3 (K := K) n).toAffineMap := hinj
  have hfr : ∀ S : AffineSubspace K (AffPt K (Fin 3 → K)),
      Module.finrank K (S.map (ext3 (K := K) n).toAffineMap).direction =
        Module.finrank K S.direction := fun S => by
    rw [AffineSubspace.map_direction, LinearMap.toAffineMap_linear]
    exact (Submodule.equivMapOfInjective _ hinj S.direction).finrank_eq.symm
  have hmem : ∀ (S : AffineSubspace K (AffPt K (Fin 3 → K))) (X : AffPt K (Fin 3 → K)),
      X ∈ S ↔ ext3 (K := K) n X ∈ S.map (ext3 (K := K) n).toAffineMap := fun S X => by
    rw [AffineSubspace.mem_map]
    constructor
    · intro h; exact ⟨X, h, rfl⟩
    · rintro ⟨Y, hY, e⟩; rw [← hinj e]; exact hY
  refine ⟨ext3 n, hinj, fun A B C => (hinj'.sbtw_map_iff).symm, fun l => ?_, fun π => ?_⟩
  · exact ⟨l.carrier.map (ext3 (K := K) n).toAffineMap, by rw [hfr]; exact l.finrank_direction,
      fun X => hmem l.carrier X⟩
  · exact ⟨π.carrier.map (ext3 (K := K) n).toAffineMap, by rw [hfr]; exact π.finrank_direction,
      fun X => hmem π.carrier X⟩

end AnyDim

end DesAlg

end HilbertFoundations
