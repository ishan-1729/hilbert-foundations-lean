import HilbertFoundations.DesarguesAlgebraAux2

/-!
# Helper for § 28: the order of the segments

Helper module of `DesarguesAlgebra.lean`. In a plane geometry satisfying I 1–2, II, III and the
second part of Desargues's theorem:

* `proj_between`: a parallel projection of one line onto another preserves betweenness (from
  Pasch's axiom II 5, through the sides of a line).
* `Seg.instLinearOrder`: Hilbert's order of the segments (§ 28), the order of sequence of the points
  of the line `OE` in which `O` precedes `E` (`OrderLin.lineLt O E` of Order.lean).
* Translations preserve betweenness (`trf_between`); so do Hilbert's maps `x ↦ x + c` and
  `x ↦ a x` (`a ≠ 0`), which are therefore strictly monotone or strictly antitone; the translations
  are monotone (`add_strictMono`), and the segments form an ordered division ring
  (`Seg.instIsStrictOrderedRing`): laws 13–16.
* `between_iff_param`: `Y` lies between `X` and `Z` iff `Y = t (Z - X) + X` with `0 < t < 1`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

namespace DesAlg

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]

/-! ## Parallel projection preserves betweenness -/

section Proj

variable [PlaneOrder P L] [PlaneParallels P L] [Nonempty L]

/-- Two points of a line lie on the same side of a different parallel line. -/
theorem sameSide_of_lpar {a b : L} (h : LPar P a b) (hab : a ≠ b) {A A' : P} (hA : A ∈ a)
    (hA' : A' ∈ a) : SameSide b A A' := by
  have hAb : A ∉ b := fun h' => hab (h A hA h')
  have hA'b : A' ∉ b := fun h' => hab (h A' hA' h')
  refine ⟨hAb, hA'b, ?_⟩
  rintro ⟨W, hW, hb⟩
  have hWa : W ∈ a := OrderCore.mem_of_between hb hA hA'
  exact hab (h W hWa hW)

/-- **A parallel projection preserves betweenness**: if `X'`, `Y'`, `Z'` on `l'` lie on the
parallels to `d` through the points `X`, `Y`, `Z` of `l`, and `Y` lies between `X` and `Z`, then
`Y'` lies between `X'` and `Z'`. -/
theorem proj_between {l l' d : L} (hl : ¬LPar P d l) (hl' : ¬LPar P d l') {X Y Z X' Y' Z' : P}
    (hX : X ∈ l) (hY : Y ∈ l) (hZ : Z ∈ l) (hX' : X' ∈ l') (hY' : Y' ∈ l') (hZ' : Z' ∈ l')
    (pX : X' ∈ pline d X) (pY : Y' ∈ pline d Y) (pZ : Z' ∈ pline d Z) (h : Between X Y Z) :
    Between X' Y' Z' := by
  have hXY := ne12_of_between h
  have hYZ := ne23_of_between h
  have nl : ∀ U, ¬LPar P (pline d U) l := fun U => not_lpar_pline_left hl U
  have nl' : ∀ U, ¬LPar P (pline d U) l' := fun U => not_lpar_pline_left hl' U
  have gXY : pline d X ≠ pline d Y := fun e =>
    hXY (eq_of_mem_not_lpar (nl X) (mem_pline d X) hX (by rw [e]; exact mem_pline d Y) hY)
  have gZY : pline d Z ≠ pline d Y := fun e =>
    hYZ (eq_of_mem_not_lpar (nl Z) (mem_pline d Z) hZ (by rw [e]; exact mem_pline d Y) hY).symm
  have pXY : LPar P (pline d X) (pline d Y) := (pline_lpar d X).trans (pline_lpar d Y).symm
  have pZY : LPar P (pline d Z) (pline d Y) := (pline_lpar d Z).trans (pline_lpar d Y).symm
  have hXg : X ∉ pline d Y := fun h' => gXY (pline_eq_of_mem h')
  have hZg : Z ∉ pline d Y := fun h' => gZY (pline_eq_of_mem h')
  have o1 : OppositeSides (pline d Y) X Z := ⟨hXg, hZg, Y, mem_pline d Y, h⟩
  have s1 : SameSide (pline d Y) X' X := sameSide_of_lpar pXY gXY pX (mem_pline d X)
  have o2 : OppositeSides (pline d Y) X' Z := OrderCore.opp_of_sameSide_opp s1 o1
  have s2 : SameSide (pline d Y) Z' Z := sameSide_of_lpar pZY gZY pZ (mem_pline d Z)
  have o3 : OppositeSides (pline d Y) Z' X' :=
    OrderCore.opp_of_sameSide_opp s2 (OrderCore.opp_symm o2)
  obtain ⟨-, -, W, hW, hb⟩ := o3
  have hWl : W ∈ l' := OrderCore.mem_of_between hb hZ' hX'
  have hWY : W = Y' := eq_of_mem_not_lpar (nl' Y) hW hWl pY hY'
  rw [hWY] at hb
  exact between_symm hb

end Proj

/-! ## Betweenness-preserving maps of linear orders -/

/-- An injective map of linear orders preserving "betweenness" is strictly monotone or strictly
antitone. -/
theorem strictMono_or_strictAnti {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β)
    (hinj : Function.Injective f)
    (hb : ∀ x y z, x < y → y < z → (f x < f y ∧ f y < f z) ∨ (f z < f y ∧ f y < f x)) :
    StrictMono f ∨ StrictAnti f := by
  have t3 : ∀ x y z, x < y → y < z →
      ((f x < f y ↔ f y < f z) ∧ (f x < f y ↔ f x < f z)) := by
    intro x y z h1 h2
    rcases hb x y z h1 h2 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact ⟨iff_of_true a1 a2, iff_of_true a1 (a1.trans a2)⟩
    · exact ⟨iff_of_false (not_lt.2 a2.le) (not_lt.2 a1.le),
        iff_of_false (not_lt.2 a2.le) (not_lt.2 (a1.trans a2).le)⟩
  have toMax : ∀ x y M, x < y → y ≤ M → (f x < f y ↔ f x < f M) := by
    intro x y M h1 h2
    rcases eq_or_lt_of_le h2 with e | h2
    · rw [e]
    · exact (t3 x y M h1 h2).2
  have key : ∀ x y x' y', x < y → x' < y' → (f x < f y ↔ f x' < f y') := by
    intro x y x' y' h h'
    set M := max y y'
    have e1 := toMax x y M h (le_max_left y y')
    have e2 := toMax x' y' M h' (le_max_right y y')
    have hxM : x < M := lt_of_lt_of_le h (le_max_left y y')
    have hx'M : x' < M := lt_of_lt_of_le h' (le_max_right y y')
    rw [e1, e2]
    rcases lt_trichotomy x x' with hx | hx | hx
    · have := t3 x x' M hx hx'M
      exact this.2.symm.trans this.1
    · rw [hx]
    · have := t3 x' x M hx hxM
      exact (this.2.symm.trans this.1).symm
  by_cases hm : StrictMono f
  · exact Or.inl hm
  · right
    simp only [StrictMono, not_forall] at hm
    obtain ⟨a, b, hab, hn⟩ := hm
    intro c d hcd
    have h1 : ¬f c < f d := fun h => hn ((key c d a b hcd hab).1 h)
    exact lt_of_le_of_ne (not_lt.1 h1) fun e => hcd.ne (hinj e).symm

theorem not_strictMono_and_strictAnti {α β : Type*} [Preorder α] [Preorder β] {f : α → β} {a b : α}
    (hab : a < b) (h1 : StrictMono f) (h2 : StrictAnti f) : False :=
  lt_asymm (h1 hab) (h2 hab)

/-! ## Hilbert's order of the segments -/

section SegOrder

variable [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] {F : Frame P}

namespace Seg

/-- The extremity of a segment as a point of the line `OE`. -/
def toSub (a : Seg F) : {X : P // X ∈ (F.xl : L)} := ⟨a.pt, a.mem⟩

theorem toSub_injective : Function.Injective (toSub (F := F)) := fun _ _ h =>
  Seg.ext (congrArg Subtype.val h)

/-- **Hilbert's order of the segments** (§ 28): `a < b` iff `A` precedes `B` in the order of
sequence of the line `OE` in which `O` precedes `E`. -/
noncomputable instance instLinearOrder : LinearOrder (Seg F) :=
  @LinearOrder.lift' _ _ (OrderLin.lineOrder F.O_xl F.E_xl F.hOE) toSub toSub_injective

theorem lt_iff (a b : Seg F) : a < b ↔ OrderLin.lineLt F.O F.E a.pt b.pt := Iff.rfl

theorem pt_ne {a b : Seg F} (h : a ≠ b) : a.pt ≠ b.pt := fun e => h (Seg.ext e)

/-- Betweenness of three distinct points of `OE` in terms of Hilbert's order. -/
theorem between_iff {a b c : Seg F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Between a.pt b.pt c.pt ↔ (a < b ∧ b < c) ∨ (c < b ∧ b < a) := by
  simp only [lt_iff]
  exact OrderLin.between_iff_lineLt F.O_xl F.E_xl F.hOE a.mem b.mem c.mem (pt_ne hab)
    (pt_ne hac) (pt_ne hbc)

theorem zero_lt_one' : (0 : Seg F) < 1 := by
  rw [lt_iff]
  left
  simp only [zero_pt, one_pt, OrderLin.sgn_self]
  rcases OrderLin.sgn_of_ne (U := F.E) F.hOE.symm with ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd h not_between_self
  · rw [h]; norm_num

/-- A map of segments preserving betweenness of the points is strictly monotone or antitone. -/
theorem mono_or_anti {f : Seg F → Seg F} (hinj : Function.Injective f)
    (hf : ∀ a b c : Seg F, Between a.pt b.pt c.pt → Between (f a).pt (f b).pt (f c).pt) :
    StrictMono f ∨ StrictAnti f := by
  refine strictMono_or_strictAnti f hinj fun x y z h1 h2 => ?_
  have hxy := h1.ne; have hyz := h2.ne; have hxz := (h1.trans h2).ne
  have hb := (between_iff hxy hxz hyz).2 (Or.inl ⟨h1, h2⟩)
  exact (between_iff (hinj.ne hxy) (hinj.ne hxz) (hinj.ne hyz)).1 (hf x y z hb)

end Seg

end SegOrder

/-! ## Translations and Hilbert's maps preserve betweenness -/

section Translations

variable [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] [hDF : Fact (DesarguesII P)]
  {F : Frame P}

open Vec

/-- A line through `O` contains the differences of its points. -/
theorem vsub_mem {Y Z : P} {g : L} (hO : F.O ∈ g) (hY : Y ∈ g) (hZ : Z ∈ g) :
    toP (ofP Y - ofP Z : Vec F) ∈ g := by
  have hD := hDF.out
  have hnZ : toP (-(ofP Z : Vec F)) ∈ g := by
    have e : (-(ofP Z : Vec F)) = (-1 : (Seg F)ᵐᵒᵖ) • ofP Z := (neg_one_smul _ _).symm
    rw [e, smul_def]
    exact dl_mem hD F (MulOpposite.unop (-1 : (Seg F)ᵐᵒᵖ)).mem hO hZ
  rw [sub_eq_add_neg]
  exact trf_mem_of hD hO hY hnZ

theorem trf_between_nl {X A B C : P} {l : L} (hl : ¬LPar P (ln F.O X : L) l) (hA : A ∈ l)
    (hB : B ∈ l) (hC : C ∈ l) (h : Between A B C) :
    Between (trf F.O X A) (trf F.O X B) (trf F.O X C) := by
  have hD := hDF.out
  have hτ := (trf_isTr hD F.O X).1
  exact proj_between hl (not_lpar_pline_right hl _) hA hB hC (mem_pline l _)
    (hτ.map_line hA hB) (hτ.map_line hA hC) (trf_trace hD (mem_ln_left F.O X) (mem_ln_right F.O X) A)
    (trf_trace hD (mem_ln_left F.O X) (mem_ln_right F.O X) B)
    (trf_trace hD (mem_ln_left F.O X) (mem_ln_right F.O X) C) h

/-- **Translations preserve betweenness.** -/
theorem trf_between (X : P) {A B C : P} (h : Between A B C) :
    Between (trf F.O X A) (trf F.O X B) (trf F.O X C) := by
  have hD := hDF.out
  have hAC := ne13_of_between h
  have hB : B ∈ (ln A C : L) := (collinear_iff_mem_ln hAC).1 (collinear_of_between h).swap23
  by_cases hl : LPar P (ln F.O X : L) (ln A C)
  · obtain ⟨X1, hX1⟩ := exists_not_mem' (P := P) (ln F.O X : L)
    set X2 : P := toP (ofP X - ofP X1 : Vec F)
    have hX : trf F.O X1 X2 = X := by
      show toP (ofP X1 + (ofP X - ofP X1) : Vec F) = X
      rw [add_sub_cancel]; rfl
    have hO1 : X1 ≠ F.O := fun e => hX1 (e ▸ mem_ln_left F.O X)
    have n1 : ¬LPar P (ln F.O X1 : L) (ln F.O X) :=
      not_lpar_of (mem_ln_left F.O X1) (mem_ln_left F.O X) fun e => hX1 (e ▸ mem_ln_right F.O X1)
    have n2 : ¬LPar P (ln F.O X2 : L) (ln A C) := by
      intro h2
      have e : (ln F.O X2 : L) = ln F.O X :=
        (h2.trans hl.symm) F.O (mem_ln_left F.O X2) (mem_ln_left F.O X)
      have hX2 : X2 ∈ (ln F.O X : L) := e ▸ mem_ln_right F.O X2
      have := vsub_mem (F := F) (mem_ln_left F.O X) (mem_ln_right F.O X) hX2
      apply hX1
      have e2 : toP (ofP X - ofP X2 : Vec F) = X1 := by
        show toP (ofP X - (ofP X - ofP X1) : Vec F) = X1
        rw [sub_sub_cancel]; rfl
      rw [← e2]; exact this
    have b1 := trf_between_nl (F := F) n2 (mem_ln_left A C) hB (mem_ln_right A C) h
    have hτ := (trf_isTr hD F.O X2).1
    have n3 : ¬LPar P (ln F.O X1 : L) (pline (ln A C : L) (trf F.O X2 A)) := fun h3 =>
      n1 (h3.trans ((pline_lpar _ _).trans hl.symm))
    have b2 := trf_between_nl (F := F) n3 (mem_pline _ _) (hτ.map_line (mem_ln_left A C) hB)
      (hτ.map_line (mem_ln_left A C) (mem_ln_right A C)) b1
    rw [← hX, ← trf_comp hD]
    exact b2
  · exact trf_between_nl hl (mem_ln_left A C) hB (mem_ln_right A C) h

/-- Translations reflect betweenness. -/
theorem trf_between_iff (X : P) {A B C : P} :
    Between (trf F.O X A) (trf F.O X B) (trf F.O X C) ↔ Between A B C := by
  have hD := hDF.out
  refine ⟨fun h => ?_, trf_between X⟩
  have := trf_between (F := F) (toP (-(ofP X : Vec F))) h
  have e : ∀ Y : P, trf F.O (toP (-(ofP X : Vec F))) (trf F.O X Y) = Y := fun Y => by
    show toP (-(ofP X : Vec F) + (ofP X + ofP Y)) = Y
    rw [neg_add_cancel_left]; rfl
  rwa [e, e, e] at this

namespace Seg

theorem add_between (c : Seg F) {a b d : Seg F} (h : Between a.pt b.pt d.pt) :
    Between (a + c).pt (b + c).pt (d + c).pt := by
  simp only [add_pt']
  exact trf_between c.pt h

/-- Hilbert's map `x ↦ a x` (a parallel projection of `OE` onto `OE'` followed by one back) preserves
betweenness. -/
theorem mul_between {a : Seg F} (ha : a ≠ 0) {x y z : Seg F} (h : Between x.pt y.pt z.pt) :
    Between (a * x).pt (a * y).pt (a * z).pt := by
  simp only [mul_pt, Frame.hmulPt]
  set d : L := ln F.E (F.toY a.pt)
  have hYa : F.toY a.pt ≠ F.O := fun e => ha (Seg.ext (by
    rw [← F.toX_toY a.pt a.mem, e, F.toX_O]; rfl))
  have hdx : ¬LPar P d (F.xl : L) := not_lpar_of (mem_ln_left _ _) F.E_xl fun e => hYa
    (eq_of_mem_not_lpar F.nl_xy (e ▸ mem_ln_right F.E (F.toY a.pt)) (F.toY_mem a.pt) F.O_xl F.O_yl)
  have hdy : ¬LPar P d (F.yl : L) := fun e => F.nl_EA' a.pt e.symm
  have n1 : ∀ X, ¬LPar P (F.yl : L) (pline d X) := fun X => not_lpar_pline_right
    (fun e => hdy e.symm) X
  have b1 := proj_between hdx hdy x.mem y.mem z.mem (meet_mem_left (n1 x.pt))
    (meet_mem_left (n1 y.pt)) (meet_mem_left (n1 z.pt)) (meet_mem_right (n1 x.pt))
    (meet_mem_right (n1 y.pt)) (meet_mem_right (n1 z.pt)) h
  exact proj_between F.nl_uy F.nl_ux (meet_mem_left (n1 x.pt)) (meet_mem_left (n1 y.pt))
    (meet_mem_left (n1 z.pt)) (F.toX_mem _) (F.toX_mem _) (F.toX_mem _) (F.toX_par _)
    (F.toX_par _) (F.toX_par _) b1

theorem add_mono_or_anti (c : Seg F) : StrictMono (· + c) ∨ StrictAnti (· + c) :=
  mono_or_anti (add_left_injective c) fun _ _ _ h => add_between c h

theorem mul_mono_or_anti {a : Seg F} (ha : a ≠ 0) : StrictMono (a * ·) ∨ StrictAnti (a * ·) :=
  mono_or_anti (mul_right_injective₀ ha) fun _ _ _ h => mul_between ha h

theorem exists_third : ∃ m : Seg F, m ≠ 0 ∧ m ≠ 1 := by
  obtain ⟨M, hM⟩ := exists_between (Line := L) F.hOE
  have hMl : M ∈ (F.xl : L) := OrderCore.mem_of_between hM F.O_xl F.E_xl
  exact ⟨⟨M, hMl⟩, fun e => ne12_of_between hM (congrArg Seg.pt e).symm,
    fun e => ne23_of_between hM (congrArg Seg.pt e)⟩

/-- **The translations of the segments are increasing** (Law 15). -/
theorem add_strictMono (c : Seg F) : StrictMono (· + c) := by
  by_contra hc
  have hanti : StrictAnti (· + c) := (add_mono_or_anti c).resolve_left hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc fun a b h => by simpa using h
  -- every translation by a non-zero segment is antitone
  have all : ∀ d : Seg F, d ≠ 0 → StrictAnti (· + d) := by
    intro d hd
    set e := d * c⁻¹
    have he : e ≠ 0 := mul_ne_zero hd (inv_ne_zero hc0)
    have hec : e * c = d := by simp only [e, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    have heq : (· + d) = (e * ·) ∘ (· + c) ∘ (e⁻¹ * ·) := by
      funext x
      simp only [Function.comp]
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ he, one_mul, hec]
    rw [heq]
    rcases mul_mono_or_anti he with h1 | h1 <;>
      rcases mul_mono_or_anti (inv_ne_zero he) with h2 | h2
    · exact h1.comp_strictAnti (hanti.comp_strictMono h2)
    · exfalso
      have k := h1.comp_strictAnti h2
      have : (fun x => e * (e⁻¹ * x)) = id := by funext x; simp [← mul_assoc, mul_inv_cancel₀ he]
      exact not_strictMono_and_strictAnti zero_lt_one' strictMono_id (by
        rw [← this]; exact k)
    · exfalso
      have k := h1.comp_strictMono h2
      have : (fun x => e * (e⁻¹ * x)) = id := by funext x; simp [← mul_assoc, mul_inv_cancel₀ he]
      exact not_strictMono_and_strictAnti zero_lt_one' strictMono_id (by
        rw [← this]; exact k)
    · exact h1.comp_strictMono (hanti.comp h2)
  -- two antitone translations compose to a monotone one
  have two : ∃ d : Seg F, d ≠ 0 ∧ 1 + d ≠ 0 := by
    by_cases h2 : (1 : Seg F) + 1 = 0
    · obtain ⟨m, hm0, hm1⟩ := exists_third (F := F)
      refine ⟨m, hm0, fun e => hm1 ?_⟩
      have k1 : m = -1 := eq_neg_of_add_eq_zero_right e
      have k2 : (1 : Seg F) = -1 := eq_neg_of_add_eq_zero_right h2
      rw [k1, ← k2]
    · exact ⟨1, one_ne_zero, h2⟩
  obtain ⟨d, hd, hd1⟩ := two
  have k := (all 1 one_ne_zero).comp (all d hd)
  have e : ((· + (1 : Seg F)) ∘ (· + d)) = (· + (1 + d)) := by
    funext x; simp [add_assoc, add_comm 1 d]
  rw [e] at k
  exact not_strictMono_and_strictAnti zero_lt_one' k (all (1 + d) hd1)

theorem mul_strictMono {a : Seg F} (ha : 0 < a) : StrictMono (a * ·) := by
  rcases mul_mono_or_anti ha.ne' with h | h
  · exact h
  · exfalso
    have := h zero_lt_one'
    simp only [mul_zero, mul_one] at this
    exact lt_asymm ha this

theorem add_le_add_right' {a b : Seg F} (h : a ≤ b) (c : Seg F) : a + c ≤ b + c :=
  (add_strictMono c).monotone h

instance instIsOrderedAddMonoid : IsOrderedAddMonoid (Seg F) where
  add_le_add_left _ _ h c := add_le_add_right' h c
  add_le_add_right a b h c := by
    rw [add_comm c a, add_comm c b]; exact add_le_add_right' h c

instance instZeroLEOneClass : ZeroLEOneClass (Seg F) := ⟨zero_lt_one'.le⟩

/-- **The segments form an ordered division ring** (laws 13–16). -/
instance instIsStrictOrderedRing : IsStrictOrderedRing (Seg F) :=
  IsStrictOrderedRing.of_mul_pos fun a b ha hb => by
    have := mul_strictMono ha hb
    simpa using this

end Seg

/-! ### The opposite ring -/

noncomputable instance Seg.instLinearOrderOp : LinearOrder (Seg F)ᵐᵒᵖ :=
  LinearOrder.lift' MulOpposite.unop MulOpposite.unop_injective

/-- The opposite ring of the segments is an ordered division ring, for the order `instLinearOrderOp`
(stated with this order explicitly, so that it is the one found by instance search). -/
instance Seg.instIsStrictOrderedRingOp :
    @IsStrictOrderedRing (Seg F)ᵐᵒᵖ _ (@LinearOrder.toPartialOrder _ Seg.instLinearOrderOp) := by
  let _ : PartialOrder (Seg F)ᵐᵒᵖ := @LinearOrder.toPartialOrder _ Seg.instLinearOrderOp
  have h1 : IsOrderedAddMonoid (Seg F)ᵐᵒᵖ :=
    { add_le_add_left := fun a b h c => by
        show MulOpposite.unop a + MulOpposite.unop c ≤ MulOpposite.unop b + MulOpposite.unop c
        exact Seg.add_le_add_right' h _
      add_le_add_right := fun a b h c => by
        show MulOpposite.unop c + MulOpposite.unop a ≤ MulOpposite.unop c + MulOpposite.unop b
        rw [add_comm (MulOpposite.unop c), add_comm (MulOpposite.unop c)]
        exact Seg.add_le_add_right' h _ }
  have h2 : ZeroLEOneClass (Seg F)ᵐᵒᵖ := ⟨Seg.zero_lt_one'.le⟩
  exact IsStrictOrderedRing.of_mul_pos fun a b ha hb => by
    show 0 < MulOpposite.unop (a * b)
    rw [MulOpposite.unop_mul]
    exact mul_pos (show 0 < MulOpposite.unop b from hb) (show 0 < MulOpposite.unop a from ha)

/-! ## Betweenness in co-ordinates -/

theorem between_seg_iff (t : Seg F) : Between F.O t.pt F.E ↔ 0 < t ∧ t < 1 := by
  by_cases h0 : t = 0
  · subst h0
    simp only [Seg.zero_pt, lt_irrefl, false_and, iff_false]
    exact fun h => ne12_of_between h rfl
  by_cases h1 : t = 1
  · subst h1
    simp only [Seg.one_pt, lt_irrefl, and_false, iff_false]
    exact fun h => ne23_of_between h rfl
  have := Seg.between_iff (a := 0) (b := t) (c := 1) (Ne.symm h0) zero_ne_one (h1)
  simp only [Seg.zero_pt, Seg.one_pt] at this
  rw [this]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact h
    · exact absurd (h.trans h') (lt_asymm Seg.zero_lt_one')
  · exact Or.inl

theorem between_dl_transfer {W W' : P} (hW : W ≠ F.O) (hW' : W' ∉ (ln F.O W : L)) (t : Seg F) :
    Between F.O (dl F.O F.E t.pt W) W ↔ Between F.O (dl F.O F.E t.pt W') W' := by
  have hD := hDF.out
  have hO' : W' ≠ F.O := fun e => hW' (e ▸ mem_ln_left F.O W)
  set d : L := ln W W'
  have hWW' : W ≠ W' := fun e => hW' (e ▸ mem_ln_right F.O W)
  have n1 : ¬LPar P d (ln F.O W : L) :=
    not_lpar_of (mem_ln_left W W') (mem_ln_right F.O W) fun e => hW' (e ▸ mem_ln_right W W')
  have hWn : W ∉ (ln F.O W' : L) := fun h => hW' (by
    rw [ln_eq (Ne.symm hW) (mem_ln_left F.O W') h]; exact mem_ln_right F.O W')
  have n2 : ¬LPar P d (ln F.O W' : L) :=
    not_lpar_of (mem_ln_right W W') (mem_ln_right F.O W') fun e => hWn (e ▸ mem_ln_left W W')
  have hdl := dl_isDil hD F t.mem
  have m1 : dl F.O F.E t.pt W ∈ (ln F.O W : L) := dl_mem hD F t.mem (mem_ln_left _ _) (mem_ln_right _ _)
  have m2 : dl F.O F.E t.pt W' ∈ (ln F.O W' : L) :=
    dl_mem hD F t.mem (mem_ln_left _ _) (mem_ln_right _ _)
  have pO : F.O ∈ pline d F.O := mem_pline d F.O
  have pW : W' ∈ pline d W := by rw [pline_of_mem (mem_ln_left W W')]; exact mem_ln_right W W'
  have pt : dl F.O F.E t.pt W' ∈ pline d (dl F.O F.E t.pt W) := hdl W W' hWW'
  constructor
  · exact proj_between n1 n2 (mem_ln_left _ _) m1 (mem_ln_right _ _) (mem_ln_left _ _) m2
      (mem_ln_right _ _) pO pt pW
  · exact proj_between n2 n1 (mem_ln_left _ _) m2 (mem_ln_right _ _) (mem_ln_left _ _) m1
      (mem_ln_right _ _) pO (pline_symm pt) (pline_symm pW)

/-- `t W` lies between `O` and `W` iff `0 < t < 1`. -/
theorem between_dl_iff {W : P} (hW : W ≠ F.O) (t : Seg F) :
    Between F.O (dl F.O F.E t.pt W) W ↔ 0 < t ∧ t < 1 := by
  have hD := hDF.out
  have key : Between F.O (dl F.O F.E t.pt W) W ↔ Between F.O (dl F.O F.E t.pt F.E) F.E := by
    by_cases hWx : W ∈ (F.xl : L)
    · have e : (ln F.O W : L) = F.xl := ln_eq (Ne.symm hW) F.O_xl hWx
      rw [between_dl_transfer hW (W' := F.E') (by rw [e]; exact F.E'_not_xl),
        between_dl_transfer (Ne.symm F.hOE') (W' := F.E) F.E_not_yl]
    · have hE : F.E ∉ (ln F.O W : L) := fun h => hWx (by
        have e : (F.xl : L) = ln F.O W := ln_eq F.hOE (mem_ln_left F.O W) h
        rw [e]; exact mem_ln_right F.O W)
      exact between_dl_transfer hW hE t
  rw [key, dl_at_E hD F t.mem, between_seg_iff]

/-- **Betweenness in terms of the vector structure**: `Y` lies between `X ≠ Z` iff
`Y = t (Z - X) + X` with `0 < t < 1`. -/
theorem between_iff_param {X Y Z : P} (hXZ : X ≠ Z) :
    Between X Y Z ↔ ∃ t : Seg F, 0 < t ∧ t < 1 ∧
      (ofP Y : Vec F) = MulOpposite.op t • (ofP Z - ofP X) + ofP X := by
  have hD := hDF.out
  have tr : ∀ A : P, trf F.O (toP (-(ofP X : Vec F))) A = toP (ofP A - ofP X : Vec F) := fun A => by
    show toP (-(ofP X : Vec F) + ofP A) = toP (ofP A - ofP X : Vec F)
    rw [neg_add_eq_sub]
  have hW : toP (ofP Z - ofP X : Vec F) ≠ F.O := by
    intro h
    have : (ofP Z - ofP X : Vec F) = 0 := h
    exact hXZ (sub_eq_zero.1 this).symm
  rw [← trf_between_iff (F := F) (toP (-(ofP X : Vec F))), tr, tr, tr, sub_self]
  constructor
  · intro h
    have hYl : toP (ofP Y - ofP X : Vec F) ∈ (ln F.O (toP (ofP Z - ofP X : Vec F)) : L) :=
      (collinear_iff_mem_ln (ne13_of_between h)).1 (collinear_of_between h).swap23
    obtain ⟨r, hr⟩ := (mem_ln_O_iff (F := F) hW).1 hYl
    refine ⟨MulOpposite.unop r, ?_⟩
    have e : dl F.O F.E (MulOpposite.unop r).pt (toP (ofP Z - ofP X : Vec F)) =
        toP (ofP Y - ofP X : Vec F) := by
      exact (congrArg toP hr).symm
    have hb := (between_dl_iff hW (MulOpposite.unop r)).1 (by rw [e]; exact h)
    refine ⟨hb.1, hb.2, ?_⟩
    rw [MulOpposite.op_unop, ← sub_eq_iff_eq_add]
    exact hr
  · rintro ⟨t, ht0, ht1, hY⟩
    have e : toP (ofP Y - ofP X : Vec F) = dl F.O F.E t.pt (toP (ofP Z - ofP X : Vec F)) := by
      rw [hY, add_sub_cancel_right]; rfl
    rw [e]
    exact (between_dl_iff hW t).2 ⟨ht0, ht1⟩

end Translations

end DesAlg

end HilbertFoundations
