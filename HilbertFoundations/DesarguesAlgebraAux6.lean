import HilbertFoundations.DesarguesAlgebraAux5

/-!
# Helper for §§ 27–30: laws, Hilbert's order by sequences, number systems, the space of § 29

Helper module of `DesarguesAlgebra.lean`.

* `laws_of_divisionRing`: an ordered division ring satisfies the laws 1–11, 13–16 of § 13 (and the
  asymmetry of 13).
* `lt_iff_sequences`: Hilbert's definition of the order of the segments by the six sequences of
  `O, E, A, B` (§ 28) agrees with the order of sequence of the line `OE`.
* `xc_add`, `translate_coord`: the step `x' = x + c` of § 27.
* `DesarguesianNumberSystem`: the laws 1–11, 13–16; such a system (with the asymmetry of law 13 and
  `0 ≠ 1`) is a linearly ordered division ring (`DesarguesianNumberSystem.toDivisionRing`, …).
* The space of § 29: `Coord Dᵐᵒᵖ 3`; Hilbert's betweenness by coordinates (`sbtw_iff_coord`).
* The degenerate plane geometry without lines (`DegPt`, `DegLn`).
* The planes of a space geometry as plane geometries embedded in it (`restrictPlaneInSpace`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

namespace DesAlg

/-! ## Laws 1–16 in an ordered division ring -/

section LawsDR

variable {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D]

theorem laws_of_divisionRing :
    Law1 D ∧ Law2 D ∧ Law3 D ∧ Law4 D ∧ Law5 D ∧ Law6 D ∧ Law7 D ∧ Law8 D ∧ Law9 D ∧ Law10 D ∧
      Law11 D ∧ Law13 D ∧ Law13Asymm D ∧ Law14 D ∧ Law15 D ∧ Law16 D := by
  refine ⟨law1_holds D, fun a => ⟨add_zero a, zero_add a⟩, fun a b => ⟨⟨-a + b, by abel,
    fun x hx => by rw [← hx]; abel⟩, ⟨b + -a, by abel, fun y hy => by rw [← hy]; abel⟩⟩,
    law4_holds D, fun a => ⟨mul_one a, one_mul a⟩, fun a b ha => ⟨⟨a⁻¹ * b, by
      show a * (a⁻¹ * b) = b
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul], fun x hx => by
      rw [← hx, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]⟩, ⟨b * a⁻¹, by
      show b * a⁻¹ * a = b
      rw [mul_assoc, inv_mul_cancel₀ ha, mul_one], fun y hy => by
      rw [← hy, mul_assoc, mul_inv_cancel₀ ha, mul_one]⟩⟩,
    fun a b c => (add_assoc a b c).symm, add_comm, fun a b c => (mul_assoc a b c).symm,
    mul_add, add_mul, fun a b h => (lt_or_gt_of_ne h).symm, fun a b h h' => lt_asymm h h',
    fun a b c h1 h2 => h2.trans h1, fun a b c h => ⟨add_lt_add_left h c, add_lt_add_right h c⟩,
    fun a b c h hc => ⟨mul_lt_mul_of_pos_right h hc, mul_lt_mul_of_pos_left h hc⟩⟩

end LawsDR

/-! ## Hilbert's order of the segments by sequences -/

section Sequences

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L] {F : Frame P}

/-- Four distinct points of the line `OE` stand in the sequence `W X Y Z` iff their segments are
increasing or decreasing. -/
theorem arr_iff {w x y z : Seg F} (h1 : w ≠ x) (h2 : w ≠ y) (h3 : w ≠ z) (h4 : x ≠ y)
    (h5 : x ≠ z) (h6 : y ≠ z) :
    II4Arrangement w.pt x.pt y.pt z.pt ↔
      (w < x ∧ x < y ∧ y < z) ∨ (z < y ∧ y < x ∧ x < w) := by
  unfold II4Arrangement
  rw [Seg.between_iff h1 h2 h4, Seg.between_iff h1 h3 h5, Seg.between_iff h2 h3 h6,
    Seg.between_iff h4 h5 h6]
  constructor
  · rintro ⟨a1 | a1, -, -, a4 | a4⟩
    · exact Or.inl ⟨a1.1, a1.2, a4.2⟩
    · exact absurd a1.2 (lt_asymm a4.2)
    · exact absurd a4.1 (lt_asymm a1.1)
    · exact Or.inr ⟨a4.1, a4.2, a1.2⟩
  · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
    · exact ⟨Or.inl ⟨a, b⟩, Or.inl ⟨a, b.trans c⟩, Or.inl ⟨a.trans b, c⟩, Or.inl ⟨b, c⟩⟩
    · exact ⟨Or.inr ⟨b, c⟩, Or.inr ⟨a.trans b, c⟩, Or.inr ⟨a, b.trans c⟩, Or.inr ⟨a, b⟩⟩

/-- **Hilbert's definition of `a < b`** (§ 28): for `A`, `B`, `O`, `E` pairwise distinct, `a < b` iff
the four points stand in one of the sequences `ABOE, AOBE, AOEB, OABE, OAEB, OEAB`. -/
theorem lt_iff_sequences {a b : Seg F} (hab : a ≠ b) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0)
    (hb1 : b ≠ 1) :
    a < b ↔ II4Arrangement a.pt b.pt F.O F.E ∨ II4Arrangement a.pt F.O b.pt F.E ∨
      II4Arrangement a.pt F.O F.E b.pt ∨ II4Arrangement F.O a.pt b.pt F.E ∨
      II4Arrangement F.O a.pt F.E b.pt ∨ II4Arrangement F.O F.E a.pt b.pt := by
  have h01 : (0 : Seg F) ≠ 1 := fun h => F.hOE (congrArg Seg.pt h)
  have hoe : (0 : Seg F) < 1 := Seg.zero_lt_one'
  rw [show F.O = (0 : Seg F).pt from rfl, show F.E = (1 : Seg F).pt from rfl,
    arr_iff hab ha0 ha1 hb0 hb1 h01, arr_iff ha0 hab ha1 hb0.symm h01 hb1,
    arr_iff ha0 ha1 hab h01 hb0.symm hb1.symm, arr_iff ha0.symm hb0.symm h01 hab ha1 hb1,
    arr_iff ha0.symm h01 hb0.symm ha1 hab hb1.symm,
    arr_iff h01 ha0.symm hb0.symm ha1.symm hb1.symm hab]
  constructor
  · intro h
    rcases lt_or_gt_of_ne ha0 with ho | ho
    · rcases lt_or_gt_of_ne hb0 with ho' | ho'
      · exact Or.inl (Or.inl ⟨h, ho', hoe⟩)
      · rcases lt_or_gt_of_ne hb1 with he | he
        · exact Or.inr (Or.inl (Or.inl ⟨ho, ho', he⟩))
        · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨ho, hoe, he⟩)))
    · rcases lt_or_gt_of_ne ha1 with he | he
      · rcases lt_or_gt_of_ne hb1 with he' | he'
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨ho, h, he'⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨ho, he, he'⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hoe, he, h⟩)))))
  · have no10 : ¬(1 : Seg F) < 0 := lt_asymm hoe
    rintro ((⟨h, -, -⟩ | ⟨h, -, -⟩) | (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) | (⟨h1, h2, h3⟩ | ⟨-, h2, -⟩) |
        (⟨-, h, -⟩ | ⟨h1, h2, h3⟩) | (⟨-, h1, h2⟩ | ⟨-, h2, h3⟩) | (⟨-, -, h⟩ | ⟨-, -, h⟩))
    · exact h
    · exact absurd h no10
    · exact h1.trans h2
    · exact absurd (h1.trans h2) no10
    · exact h1.trans (h2.trans h3)
    · exact absurd h2 no10
    · exact h
    · exact absurd ((h1.trans h2).trans h3) no10
    · exact h1.trans h2
    · exact absurd (h2.trans h3) no10
    · exact h
    · exact absurd h no10

end Sequences


/-! ## The step `x' = x + c` of § 27 -/

section Translate

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [LineOrder P L]
  [PlaneParallels P L] [Nonempty L] [hDF : Fact (DesarguesII P)] {F : Frame P}

open Vec MulOpposite

/-- The co-ordinates of a sum of vectors are the sums of the co-ordinates. -/
theorem xc_add (X Y : P) :
    F.xc (toP (ofP X + ofP Y : Vec F)) = F.xc X + F.xc Y ∧
      F.yc (toP (ofP X + ofP Y : Vec F)) = F.yc X + F.yc Y := by
  have h : (ofP (toP (ofP X + ofP Y : Vec F)) : Vec F) =
      op (F.xc X + F.xc Y) • ofP F.E + op (F.yc X + F.yc Y) • ofP F.E' := by
    rw [ofP_toP, decomp X, decomp Y, op_add, op_add, add_smul, add_smul]; abel
  exact coord_unique ((decomp _).symm.trans h)

theorem xc_of_mem {O' : P} (h : O' ∈ (F.xl : L)) : F.xc O' = ⟨O', h⟩ :=
  Seg.ext (eq_meet (not_lpar_pline_right F.nl_xy O') h (mem_pline _ _)).symm

/-- **`x' = x + c`** (§ 27): if `l'` cuts the first axis in `O'` (`c = OO'`), `P'` lies on `l'`, and
`Q` is the point of the parallel to `l'` through `O` on the parallel to the first axis through `P'`,
then `x(P') = x(Q) + c`. (Hilbert assumes tacitly that `l'` is not parallel to the first axis.) -/
theorem translate_coord {l' : L} {O' P' Q : P} (hO' : O' ∈ (F.xl : L)) (hO'l : O' ∈ l')
    (hl : ¬LPar P l' F.xl) (hP' : P' ∈ l') (hQ : Q ∈ pline l' F.O)
    (hQP : Q ∈ pline (F.xl : L) P') : F.xc P' = F.xc Q + ⟨O', hO'⟩ := by
  have hD := hDF.out
  have k1 : trf F.O O' Q ∈ l' := by
    have := (trf_isTr hD F.O O').1.map_line (mem_pline l' F.O) hQ
    rwa [trf_O hD, pline_pline, pline_of_mem hO'l] at this
  have k2 : trf F.O O' Q ∈ pline (F.xl : L) P' := by
    have := trf_trace hD F.O_xl hO' Q
    rwa [pline_eq_of_mem hQP] at this
  have hn : ¬LPar P l' (pline (F.xl : L) P') := not_lpar_pline_right hl P'
  have e : trf F.O O' Q = P' := eq_of_mem_not_lpar hn k1 k2 hP' (mem_pline _ P')
  have e2 : trf F.O O' Q = toP (ofP O' + ofP Q : Vec F) := rfl
  rw [← e, e2, (xc_add O' Q).1, add_comm, xc_of_mem hO']

end Translate

/-! ## Desarguesian number systems -/

section NumberSystem

variable {α : Type*} [Add α] [Mul α] [Zero α] [One α] [LT α]

/-- **A desarguesian number system** (§ 28): a number system satisfying the laws 1–11 and 13–16 of
§ 13 (all the laws but the commutative law of multiplication and the law of Archimedes). -/
structure DesarguesianNumberSystem (α : Type*) [Add α] [Mul α] [Zero α] [One α] [LT α] : Prop where
  law1 : Law1 α
  law2 : Law2 α
  law3 : Law3 α
  law4 : Law4 α
  law5 : Law5 α
  law6 : Law6 α
  law7 : Law7 α
  law8 : Law8 α
  law9 : Law9 α
  law10 : Law10 α
  law11 : Law11 α
  law13 : Law13 α
  law14 : Law14 α
  law15 : Law15 α
  law16 : Law16 α

namespace DesarguesianNumberSystem

omit [LT α] in
theorem zero_mul' (h3 : Law3 α) (h2 : Law2 α) (h11 : Law11 α) (a : α) : 0 * a = 0 := by
  have e : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← h11, (h2 0).1, (h2 _).1]
  exact (h3 (0 * a) (0 * a + 0)).1.unique e rfl

omit [LT α] in
theorem mul_zero' (h3 : Law3 α) (h2 : Law2 α) (h10 : Law10 α) (a : α) : a * 0 = 0 := by
  have e : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← h10, (h2 0).1, (h2 _).1]
  exact (h3 (a * 0) (a * 0 + 0)).1.unique e rfl

open Classical in
/-- **A desarguesian number system is a division ring** (with the given operations), provided
`0 ≠ 1`. -/
@[instance_reducible] noncomputable def toDivisionRing (h : DesarguesianNumberSystem α)
    (h01 : (0 : α) ≠ 1) : DivisionRing α :=
  let neg : α → α := fun a => Classical.choose (h.law3 a 0).1.exists
  let inv : α → α := fun a => if ha : a = 0 then 0 else Classical.choose (h.law6 a 1 ha).1.exists
  { add := (· + ·)
    add_assoc := fun a b c => (h.law7 a b c).symm
    zero := 0
    zero_add := fun a => (h.law2 a).2
    add_zero := fun a => (h.law2 a).1
    nsmul := nsmulRec
    neg := neg
    neg_add_cancel := fun a => by
      show neg a + a = 0
      rw [h.law8]; exact Classical.choose_spec (h.law3 a 0).1.exists
    add_comm := h.law8
    mul := (· * ·)
    left_distrib := h.law10
    right_distrib := h.law11
    zero_mul := zero_mul' h.law3 h.law2 h.law11
    mul_zero := mul_zero' h.law3 h.law2 h.law10
    mul_assoc := fun a b c => (h.law9 a b c).symm
    one := 1
    one_mul := fun a => (h.law5 a).2
    mul_one := fun a => (h.law5 a).1
    inv := inv
    exists_pair_ne := ⟨0, 1, h01⟩
    mul_inv_cancel := fun a ha => by
      show a * inv a = 1
      have e : inv a = Classical.choose (h.law6 a 1 ha).1.exists := by simp [inv, ha]
      rw [e]; exact Classical.choose_spec (h.law6 a 1 ha).1.exists
    inv_zero := by simp [inv]
    zsmul := @zsmulRec α _ _ ⟨neg⟩ nsmulRec
    nnqsmul := _
    qsmul := _ }

/-- **The order of a desarguesian number system** (laws 13–16 with the asymmetry of law 13). -/
@[instance_reducible] noncomputable def toLinearOrder (h : DesarguesianNumberSystem α)
    (ha : Law13Asymm α) : LinearOrder α :=
  OrderLaws.toLinearOrder ⟨h.law13, h.law14, h.law15, h.law16⟩ ha

/-- **A desarguesian number system is an ordered division ring.** -/
theorem isStrictOrderedRing (h : DesarguesianNumberSystem α) (ha : Law13Asymm α)
    (h01 : (0 : α) ≠ 1) :
    letI := h.toDivisionRing h01
    letI := h.toLinearOrder ha
    IsStrictOrderedRing α := by
  let := h.toDivisionRing h01
  let := h.toLinearOrder ha
  obtain ⟨n, hn, -⟩ := (h.law3 1 0).1
  have h01' : (0 : α) < 1 := by
    rcases h.law13 0 1 h01 with h1 | h1
    · exfalso
      have k1 : (0 : α) < n := by
        have := (h.law15 0 1 n h1).1
        rw [(h.law2 n).2, hn] at this; exact this
      have k2 := (h.law16 0 1 n h1 k1).1
      rw [zero_mul' h.law3 h.law2 h.law11, (h.law5 n).2] at k2
      exact ha _ _ k1 k2
    · exact h1
  have hadd : ∀ a b c : α, a ≤ b → a + c ≤ b + c := fun a b c hab => by
    rcases hab with hab | rfl
    · exact Or.inl (h.law15 b a c hab).1
    · exact Or.inr rfl
  have : IsOrderedAddMonoid α :=
    { add_le_add_left := fun a b hab c => hadd a b c hab
      add_le_add_right := fun a b hab c => by
        rw [h.law8 c a, h.law8 c b]; exact hadd a b c hab }
  have : ZeroLEOneClass α := ⟨Or.inl h01'⟩
  exact IsStrictOrderedRing.of_mul_pos fun a b ha' hb => by
    have := (h.law16 a 0 b ha' hb).1
    rwa [zero_mul' h.law3 h.law2 h.law11] at this

end DesarguesianNumberSystem

end NumberSystem

/-! ## The opposite of an ordered division ring -/

/-- The order of `αᵐᵒᵖ` (that of `α`). -/
@[instance_reducible] def opLinearOrder (α : Type*) [LinearOrder α] : LinearOrder αᵐᵒᵖ :=
  LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective

theorem opIsStrictOrderedRing (α : Type*) [DivisionRing α] [LinearOrder α]
    [IsStrictOrderedRing α] :
    @IsStrictOrderedRing αᵐᵒᵖ _ (@LinearOrder.toPartialOrder _ (opLinearOrder α)) := by
  let _ : PartialOrder αᵐᵒᵖ := @LinearOrder.toPartialOrder _ (opLinearOrder α)
  have h1 : IsOrderedAddMonoid αᵐᵒᵖ :=
    { add_le_add_left := fun a b h c => by
        show MulOpposite.unop a + MulOpposite.unop c ≤ MulOpposite.unop b + MulOpposite.unop c
        exact add_le_add_left (show MulOpposite.unop a ≤ MulOpposite.unop b from h) _
      add_le_add_right := fun a b h c => by
        show MulOpposite.unop c + MulOpposite.unop a ≤ MulOpposite.unop c + MulOpposite.unop b
        exact add_le_add_right (show MulOpposite.unop a ≤ MulOpposite.unop b from h) _ }
  have h2 : ZeroLEOneClass αᵐᵒᵖ := ⟨show (0 : α) ≤ 1 from zero_le_one⟩
  exact IsStrictOrderedRing.of_mul_pos fun a b ha hb => by
    show 0 < MulOpposite.unop (a * b)
    rw [MulOpposite.unop_mul]
    exact mul_pos (show 0 < MulOpposite.unop b from hb) (show 0 < MulOpposite.unop a from ha)

/-! ## Hilbert's betweenness by co-ordinates (§ 29) -/

section CoordBetween

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem sbtw_iff_param {A C : Coord K 3} (hAC : A ≠ C) (t : K) :
    Sbtw K A (t • (C - A) + A) C ↔ 0 < t ∧ t < 1 := by
  have hd : C - A ≠ 0 := sub_ne_zero.2 (Ne.symm hAC)
  have k := sbtw_param_iff (O := A) hd 0 t 1
  rw [zero_smul, zero_add, one_smul, sub_add_cancel] at k
  rw [k]
  exact ⟨fun h => h.resolve_right fun ⟨h1, h2⟩ => absurd (h1.trans h2) (lt_asymm zero_lt_one),
    Or.inl⟩

theorem coord_sub (t : K) (A C : Coord K 3) (i : Fin 3) :
    AffPt.toV (t • (C - A) + A) i - AffPt.toV A i = t * (AffPt.toV C i - AffPt.toV A i) := by
  simp [AffPt.toV_add, AffPt.toV_smul, AffPt.toV_sub]

theorem coord_sub' (t : K) (A C : Coord K 3) (i : Fin 3) :
    AffPt.toV C i - AffPt.toV (t • (C - A) + A) i = (1 - t) * (AffPt.toV C i - AffPt.toV A i) := by
  simp only [AffPt.toV_add, AffPt.toV_smul, AffPt.toV_sub, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, sub_mul, one_mul]
  abel

/-- **Hilbert's betweenness in co-ordinates** (§ 29): a point `B` of the line `AC` lies between `A`
and `C` iff for some co-ordinate `A_i < B_i < C_i` or `A_i > B_i > C_i`. -/
theorem sbtw_iff_coord {A C : Coord K 3} (hAC : A ≠ C) (t : K) :
    Sbtw K A (t • (C - A) + A) C ↔ ∃ i : Fin 3,
      (AffPt.toV A i < AffPt.toV (t • (C - A) + A) i ∧ AffPt.toV (t • (C - A) + A) i < AffPt.toV C i) ∨
      (AffPt.toV C i < AffPt.toV (t • (C - A) + A) i ∧ AffPt.toV (t • (C - A) + A) i < AffPt.toV A i) := by
  rw [sbtw_iff_param hAC]
  constructor
  · rintro ⟨ht0, ht1⟩
    have : ∃ i, AffPt.toV A i ≠ AffPt.toV C i := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hAC (AffPt.toV_injective (funext hc))
    obtain ⟨i, hi⟩ := this
    have e1 := coord_sub t A C i
    have e2 := coord_sub' t A C i
    have ht1' : 0 < 1 - t := sub_pos.2 ht1
    refine ⟨i, ?_⟩
    rcases lt_or_gt_of_ne hi with h | h
    · left
      have hd : 0 < AffPt.toV C i - AffPt.toV A i := sub_pos.2 h
      exact ⟨sub_pos.1 (e1 ▸ mul_pos ht0 hd), sub_pos.1 (e2 ▸ mul_pos ht1' hd)⟩
    · right
      have hd : AffPt.toV C i - AffPt.toV A i < 0 := sub_neg.2 h
      exact ⟨sub_neg.1 (e2 ▸ mul_neg_of_pos_of_neg ht1' hd),
        sub_neg.1 (e1 ▸ mul_neg_of_pos_of_neg ht0 hd)⟩
  · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · have hd : 0 < AffPt.toV C i - AffPt.toV A i := sub_pos.2 (h1.trans h2)
      have e1 := coord_sub t A C i
      have e2 := coord_sub' t A C i
      exact ⟨(mul_pos_iff_of_pos_right hd).1 (e1 ▸ sub_pos.2 h1),
        sub_pos.1 ((mul_pos_iff_of_pos_right hd).1 (e2 ▸ sub_pos.2 h2))⟩
    · have hd : 0 < -(AffPt.toV C i - AffPt.toV A i) := neg_pos.2 (sub_neg.2 (h1.trans h2))
      have e1 := coord_sub t A C i
      have e2 := coord_sub' t A C i
      refine ⟨(mul_pos_iff_of_pos_right hd).1 ?_, sub_pos.1 ((mul_pos_iff_of_pos_right hd).1 ?_)⟩
      · rw [mul_neg, ← e1, neg_sub]; exact sub_pos.2 h2
      · rw [mul_neg, ← e2, neg_sub]; exact sub_pos.2 h1

/-- **The order of the co-ordinates along a line** (§ 29): if `B` lies between `A` and `C`, every
co-ordinate is either constant or strictly monotone along `A, B, C`. -/
theorem coord_monotone {A C : Coord K 3} (hAC : A ≠ C) {t : K}
    (h : Sbtw K A (t • (C - A) + A) C) (j : Fin 3) :
    (AffPt.toV A j < AffPt.toV (t • (C - A) + A) j ∧ AffPt.toV (t • (C - A) + A) j < AffPt.toV C j) ∨
    (AffPt.toV A j = AffPt.toV (t • (C - A) + A) j ∧ AffPt.toV (t • (C - A) + A) j = AffPt.toV C j) ∨
    (AffPt.toV C j < AffPt.toV (t • (C - A) + A) j ∧ AffPt.toV (t • (C - A) + A) j < AffPt.toV A j) := by
  obtain ⟨ht0, ht1⟩ := (sbtw_iff_param hAC t).1 h
  have e1 := coord_sub t A C j
  have e2 := coord_sub' t A C j
  have ht1' : 0 < 1 - t := sub_pos.2 ht1
  rcases lt_trichotomy (AffPt.toV A j) (AffPt.toV C j) with hj | hj | hj
  · have hd : 0 < AffPt.toV C j - AffPt.toV A j := sub_pos.2 hj
    exact Or.inl ⟨sub_pos.1 (e1 ▸ mul_pos ht0 hd), sub_pos.1 (e2 ▸ mul_pos ht1' hd)⟩
  · rw [hj, sub_self, mul_zero, sub_eq_zero] at e1 e2
    exact Or.inr (Or.inl ⟨hj.trans e2, e2.symm⟩)
  · have hd : AffPt.toV C j - AffPt.toV A j < 0 := sub_neg.2 hj
    exact Or.inr (Or.inr ⟨sub_neg.1 (e2 ▸ mul_neg_of_pos_of_neg ht1' hd),
      sub_neg.1 (e1 ▸ mul_neg_of_pos_of_neg ht0 hd)⟩)

end CoordBetween

/-! ## The degenerate plane geometry without lines -/

/-- One point. -/
def DegPt : Type := Unit

/-- No line. -/
def DegLn : Type := Empty

instance : HasLines DegPt DegLn := ⟨fun _ e => Empty.elim e⟩
instance : HasBetween DegPt := ⟨fun _ _ _ => False⟩

theorem degPt_eq (X Y : DegPt) : X = Y := Subsingleton.elim (α := Unit) X Y

theorem deg_not_collinear (X Y Z : DegPt) : ¬Collinear X Y Z := fun ⟨a, _⟩ => Empty.elim a

theorem deg_planeOrder : PlaneOrder DegPt DegLn where
  ax_I1 A B h := absurd (degPt_eq A B) h
  ax_I2 A B _ _ h := absurd (degPt_eq A B) h
  ax_I7_line a := Empty.elim a
  ax_I7_noncollinear := ⟨(), (), (), deg_not_collinear _ _ _⟩
  between_onLine _ _ _ h := h.elim
  ax_II1 _ _ _ _ h := h.elim
  ax_II2 _ _ a := Empty.elim a
  ax_II3 _ _ _ h := absurd h (deg_not_collinear _ _ _)
  ax_II4 _ _ _ _ a := Empty.elim a
  ax_II5 _ _ _ a := Empty.elim a

theorem deg_planeParallels : PlaneParallels DegPt DegLn where
  ax_I1 A B h := absurd (degPt_eq A B) h
  ax_I2 A B _ _ h := absurd (degPt_eq A B) h
  ax_I7_line a := Empty.elim a
  ax_I7_noncollinear := ⟨(), (), (), deg_not_collinear _ _ _⟩
  ax_III a := Empty.elim a

theorem deg_desargues : DesarguesTheorem DegPt :=
  ⟨fun _ _ _ _ _ _ _ _ ⟨a, _⟩ => Empty.elim a, fun _ _ _ _ _ _ a => Empty.elim a⟩

/-- **The degenerate plane geometry is not a part of any space geometry** satisfying I. -/
theorem deg_not_planeInSpace {P' : Type u} {L' : Type v} {Pl' : Type w} [HasLines P' L']
    [HasPlanes P' Pl'] [HasBetween P'] [SpaceConnection P' L' Pl']
    (e : PlaneInSpace DegPt DegLn P' L' Pl') : False := by
  have hα : ∀ W : P', W ∈ e.plane → W = e.pt () := fun W hW => by
    obtain ⟨X, rfl⟩ := e.pt_surj W hW
    rw [degPt_eq X ()]
  obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := SpaceConnection.ax_I7_plane (Point := P') (Line := L') e.plane
  rw [hα X hX, hα Y hY, hα Z hZ] at hn
  have all : ∀ W : P', W = e.pt () := fun W => by
    by_contra hW
    obtain ⟨m, h1, -⟩ := exists_line (Line := L') (Ne.symm hW)
    exact hn ⟨m, h1, h1, h1⟩
  obtain ⟨A, B, C, D, h⟩ := SpaceConnection.ax_I7_space (Point := P') (Line := L') (Plane := Pl')
  have hQ : e.pt () ∈ e.plane := e.pt_mem ()
  exact h ⟨e.plane, by rw [all A]; exact hQ, by rw [all B]; exact hQ, by rw [all C]; exact hQ,
    by rw [all D]; exact hQ⟩

/-! ## The planes of a space geometry -/

section Restrict

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]

/-- **A plane of space, as a plane geometry, is a part of the space** (with the identity maps). -/
def restrictPlaneInSpace (α : Pl) :
    PlaneInSpace {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} P L Pl where
  plane := α
  pt := Subtype.val
  ln := Subtype.val
  pt_injective := Subtype.val_injective
  pt_mem X := X.2
  pt_surj Y hY := ⟨⟨Y, hY⟩, rfl⟩
  ln_injective := Subtype.val_injective
  ln_in l := l.2
  ln_surj m hm := ⟨⟨m, hm⟩, rfl⟩
  mem_iff _ _ := Iff.rfl
  between_iff _ _ _ := Iff.rfl

theorem nonempty_lines_of_plane [SpaceConnection P L Pl] (α : Pl) :
    Nonempty {a : L // LiesInPlane (Point := P) a α} := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  have key : ∀ U V : P, U ∈ α → V ∈ α → U ≠ V →
      Nonempty {a : L // LiesInPlane (Point := P) a α} := fun U V hU hV h => by
    obtain ⟨m, h1, h2⟩ := exists_line (Line := L) h
    exact ⟨⟨m, liesInPlane_of_mem h h1 h2 hU hV⟩⟩
  by_cases hXY : X = Y
  · by_cases hXZ : X = Z
    · exfalso
      have : ∃ R : P, R ∉ α := by
        obtain ⟨A, B, C, D, h⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
        by_contra hall
        simp only [not_exists, not_not] at hall
        exact h ⟨α, hall A, hall B, hall C, hall D⟩
      obtain ⟨R, hR⟩ := this
      have hXR : X ≠ R := fun e => hR (e ▸ hX)
      obtain ⟨m, h1, -⟩ := exists_line (Line := L) hXR
      exact hn ⟨m, h1, hXY ▸ h1, hXZ ▸ h1⟩
    · exact key X Z hX hZ hXZ
  · exact key X Y hX hY hXY

end Restrict


/-! ## Hilbert's plane equations (§ 29) -/

section PlaneEquation

variable {D : Type*} [DivisionRing D]

open MulOpposite

/-- The linear form `X ↦ Σ Xᵢ cᵢ` on `Coord Dᵐᵒᵖ 3` (scalars `Dᵐᵒᵖ` acting on the left, i.e. `D`
acting on the right). -/
def eqForm (c : Fin 3 → Dᵐᵒᵖ) : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ) →ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ where
  toFun X := ∑ i, AffPt.toV X i * c i
  map_add' X Y := by
    simp only [AffPt.toV_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' k X := by
    simp only [AffPt.toV_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply,
      Finset.mul_sum]

theorem eqForm_apply (c : Fin 3 → Dᵐᵒᵖ) (X : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) :
    eqForm c X = ∑ i, AffPt.toV X i * c i := rfl

theorem unop_eqForm (u v w : D) (X : AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) :
    unop (eqForm ![op u, op v, op w] X) =
      u * unop (AffPt.toV X 0) + v * unop (AffPt.toV X 1) + w * unop (AffPt.toV X 2) := by
  simp [eqForm_apply, Fin.sum_univ_three, unop_add, unop_mul]

theorem eqForm_single (c : Fin 3 → Dᵐᵒᵖ) (i : Fin 3) (k : Dᵐᵒᵖ) :
    eqForm c (AffPt.ofV (Pi.single i k)) = k * c i := by
  rw [eqForm_apply]
  simp only [AffPt.toV_ofV]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Hilbert's plane equations** (§ 29): for `(u, v, w) ≠ 0` the points `(x, y, z)` of `D³` with
`u x + v y + w z + r = 0` (coefficients on the left) are exactly the points of a plane of the
coordinate space `Coord Dᵐᵒᵖ 3`. -/
theorem equation_plane (u v w r : D) (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    ∃ π : CoordPlane Dᵐᵒᵖ 3, ∀ X : Coord Dᵐᵒᵖ 3, X ∈ π ↔
      u * unop (AffPt.toV X 0) + v * unop (AffPt.toV X 1) + w * unop (AffPt.toV X 2) + r = 0 := by
  have hc : ∃ i, (![op u, op v, op w] : Fin 3 → Dᵐᵒᵖ) i ≠ 0 := by
    rcases h with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  obtain ⟨i, hi⟩ := hc
  have hsurj : Function.Surjective (eqForm (![op u, op v, op w] : Fin 3 → Dᵐᵒᵖ)) := fun k =>
    ⟨AffPt.ofV (Pi.single i (k * ((![op u, op v, op w] : Fin 3 → Dᵐᵒᵖ) i)⁻¹)), by
      rw [eqForm_single, mul_assoc, inv_mul_cancel₀ hi, mul_one]⟩
  have hrange : Module.finrank Dᵐᵒᵖ
      (LinearMap.range (eqForm (![op u, op v, op w] : Fin 3 → Dᵐᵒᵖ))) = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self]
  have : Module.Finite Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) :=
    inferInstanceAs (Module.Finite Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ))
  have hdim : Module.finrank Dᵐᵒᵖ (AffPt Dᵐᵒᵖ (Fin 3 → Dᵐᵒᵖ)) = 3 :=
    Module.finrank_fin_fun Dᵐᵒᵖ
  have hker : Module.finrank Dᵐᵒᵖ
      (LinearMap.ker (eqForm (![op u, op v, op w] : Fin 3 → Dᵐᵒᵖ))) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker
      (eqForm (![op u, op v, op w] : Fin 3 → Dᵐᵒᵖ))
    omega
  obtain ⟨X0, hX0⟩ := hsurj (-op r)
  refine ⟨⟨AffineSubspace.mk' X0 (LinearMap.ker (eqForm (![op u, op v, op w] : Fin 3 → Dᵐᵒᵖ))),
    by rw [AffineSubspace.direction_mk']; exact hker⟩, fun X => ?_⟩
  show X ∈ AffineSubspace.mk' X0 _ ↔ _
  rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hX0, sub_neg_eq_add,
    ← unop_inj, unop_add, unop_op, unop_zero, unop_eqForm]

end PlaneEquation

end DesAlg

end HilbertFoundations
