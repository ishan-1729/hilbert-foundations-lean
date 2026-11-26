import HilbertFoundations.CoordinatesCloseAux3

/-!
# Helper for § 17 (ideal elements): the length of the segments of space

Helper module of `CoordinatesClose.lean` (unit `s17.ideal`). In a geometry of space with I–IV, III
and a plane `α` with rectangular axes `ax`:

* `slen α ax X Y`: the length of the segment `XY` of space, an element of the field of segments
  `Pas.G ax` of the plane `α` (the segment is laid off in `α` from the origin of the axes). Two
  segments are congruent iff their lengths are equal (`slen_eq_iff`), and lengths add
  (`slen_add`).
* With Archimedes's axiom: in every plane `π` with axes `bx`, the length of space is proportional to
  the length `Pas.len bx` of the plane (`slen_plane`: after embedding both fields of segments into
  `ℝ`); the proof uses no solid geometry, only that an additive positive map between archimedean
  ordered fields is linear (`additive_pos_eq_mul`). Hence the theorem of Pythagoras holds for `slen`
  on the axes of every plane (`slen_pyth`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace SpaceCoord

open Module

universe u v w

/-! ## Additive maps of archimedean ordered fields -/

theorem exists_nat_div_btwn {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x < (a : ℝ) / b ∧ (a : ℝ) / b < y := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn hxy
  have hq : (0 : ℝ) < q := lt_of_le_of_lt hx h1
  have hq' : 0 < q := by exact_mod_cast hq
  have hnum : 0 < q.num := Rat.num_pos.2 hq'
  have e : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    rw [Rat.cast_def, ← Int.cast_natCast (q.num.toNat), Int.toNat_of_nonneg hnum.le]
  exact ⟨q.num.toNat, q.den, by omega, q.den_pos, by rw [e]; exact h1, by rw [e]; exact h2⟩

section Squeeze

variable {G : Type*} [Field G] [LinearOrder G] [IsStrictOrderedRing G]

theorem orderRingHom_strictMono (ι : G →+*o ℝ) : StrictMono ι :=
  (OrderHomClass.mono ι).strictMono_of_injective ι.toRingHom.injective

theorem orderRingHom_pos (ι : G →+*o ℝ) {g : G} (hg : 0 < g) : 0 < ι g := by
  have := orderRingHom_strictMono ι hg
  rwa [map_zero] at this

theorem orderRingHom_abs (ι : G →+*o ℝ) (t : G) : ι |t| = |ι t| := by
  rcases le_total 0 t with h | h
  · have h' : 0 ≤ ι t := by simpa using OrderHomClass.mono ι h
    rw [abs_of_nonneg h, abs_of_nonneg h']
  · have h' : ι t ≤ 0 := by simpa using OrderHomClass.mono ι h
    rw [abs_of_nonpos h, abs_of_nonpos h', map_neg]

/-- **An additive positive map of an ordered field into `ℝ` is linear**: if `T (g + h) = T g + T h`
and `T g > 0` for positive `g`, `h`, then `T g = ι g · T 1` for the embedding `ι` of the field into
`ℝ` (which exists iff the field is archimedean). -/
theorem additive_pos_eq_mul (ι : G →+*o ℝ) (T : G → ℝ)
    (hadd : ∀ g h : G, 0 < g → 0 < h → T (g + h) = T g + T h)
    (hpos : ∀ g : G, 0 < g → 0 < T g) {g : G} (hg : 0 < g) : T g = ι g * T 1 := by
  have hι : StrictMono ι := orderRingHom_strictMono ι
  have hnat : ∀ (n : ℕ) (x : G), 0 < x →
      T (((n + 1 : ℕ) : G) * x) = ((n + 1 : ℕ) : ℝ) * T x := by
    intro n x hx
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos' : 0 < ((n + 1 : ℕ) : G) * x := mul_pos (by exact_mod_cast Nat.succ_pos n) hx
      have e : ((n + 1 + 1 : ℕ) : G) * x = ((n + 1 : ℕ) : G) * x + x := by push_cast; ring
      rw [e, hadd _ _ hpos' hx, ih]; push_cast; ring
  have hmono : ∀ x y : G, 0 < x → x < y → T x < T y := by
    intro x y hx hxy
    have h := hadd x (y - x) hx (sub_pos.2 hxy)
    rw [add_sub_cancel] at h
    rw [h]; linarith [hpos (y - x) (sub_pos.2 hxy)]
  have hfrac : ∀ a b : ℕ, 0 < a → 0 < b →
      T ((a : G) / (b : G)) = (a : ℝ) / (b : ℝ) * T 1 := by
    intro a b ha hb
    obtain ⟨a', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha.ne'
    obtain ⟨b', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hb.ne'
    have hbG : ((b' + 1 : ℕ) : G) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b'
    have hbR : ((b' + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b'
    have hx : 0 < ((a' + 1 : ℕ) : G) / ((b' + 1 : ℕ) : G) :=
      div_pos (by exact_mod_cast Nat.succ_pos a') (by exact_mod_cast Nat.succ_pos b')
    have h1 := hnat b' _ hx
    have h2 := hnat a' (1 : G) one_pos
    have e : ((b' + 1 : ℕ) : G) * (((a' + 1 : ℕ) : G) / ((b' + 1 : ℕ) : G)) =
        ((a' + 1 : ℕ) : G) * 1 := by
      field_simp
    rw [e, h2] at h1
    rw [div_mul_eq_mul_div, eq_div_iff hbR]
    linear_combination (-1 : ℝ) * h1
  have hT1 : 0 < T 1 := hpos 1 one_pos
  have hιg : 0 < ι g := orderRingHom_pos ι hg
  have hcast : ∀ a b : ℕ, ι ((a : G) / (b : G)) = (a : ℝ) / (b : ℝ) := fun a b => by
    rw [map_div₀, map_natCast, map_natCast]
  rcases lt_trichotomy (T g) (ι g * T 1) with h | h | h
  · exfalso
    have h' : T g / T 1 < ι g := (div_lt_iff₀ hT1).2 h
    obtain ⟨a, b, ha, hb, h1, h2⟩ :=
      exists_nat_div_btwn (div_nonneg (hpos g hg).le hT1.le) h'
    have hlt : (a : G) / (b : G) < g := hι.lt_iff_lt.1 (by rw [hcast]; exact h2)
    have hx : 0 < (a : G) / (b : G) := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
    have h3 := hmono _ _ hx hlt
    rw [hfrac a b ha hb] at h3
    have h4 := (div_lt_iff₀ hT1).1 h1
    linarith
  · exact h
  · exfalso
    have h' : ι g < T g / T 1 := (lt_div_iff₀ hT1).2 h
    obtain ⟨a, b, ha, hb, h1, h2⟩ := exists_nat_div_btwn hιg.le h'
    have hlt : g < (a : G) / (b : G) := hι.lt_iff_lt.1 (by rw [hcast]; exact h1)
    have h3 := hmono _ _ hg hlt
    rw [hfrac a b ha hb] at h3
    have h4 := (lt_div_iff₀ hT1).1 h2
    linarith

end Squeeze

/-! ## The length of a segment of space -/

section Length

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hC : SpaceCongruence P L Pl] [hS : SpaceParallels P L Pl]

local notation "𝒫[" π "]" => {A : P // A ∈ π}
local notation "ℒ[" π "]" => {a : L // LiesInPlane (Point := P) a π}

include hC hS

/-- A point collinear with two distinct points of a plane lies in the plane. -/
theorem mem_plane_of_collinear (α : Pl) {A B X : P} (hA : A ∈ α)
    (hB : B ∈ α) (hAB : A ≠ B) (h : Collinear (Line := L) A B X) : X ∈ α := by
  obtain ⟨a, h1, h2, h3⟩ := h
  exact liesInPlane_of_mem hAB h1 h2 hA hB X h3

-- (no local notation in `variable` binders: it makes the variable inaccessible)
variable (α : Pl) (ax : Pas.Axes {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α})

/-- Every segment of space can be laid off in `α` from the origin of the axes. -/
theorem exists_layoff {X Y : P} (h : X ≠ Y) :
    ∃ B : 𝒫[α], B ≠ ax.O ∧ SegCong X Y (ax.O : P) (B : P) := by
  have hOE : (ax.O : P) ≠ ax.E := fun e => ax.hOE (Subtype.ext e)
  obtain ⟨B, hB, s⟩ := segCong_layoff (L := L) h hOE
  have hBα : B ∈ α := mem_plane_of_collinear (L := L) α ax.E.2 ax.O.2 hOE.symm hB.2.2.1
  exact ⟨⟨B, hBα⟩, fun e => hB.2.1 (congrArg Subtype.val e), s⟩

open Classical in
/-- **The length of a segment of space**, in the field of segments of the plane `α`. -/
noncomputable def slen (X Y : P) : Pas.G ax :=
  if h : X = Y then 0 else Pas.len ax ax.O (exists_layoff α ax h).choose

theorem slen_self (X : P) : slen α ax X X = 0 := by simp [slen]

theorem slen_spec {X Y : P} (h : X ≠ Y) {B : 𝒫[α]} (hB : B ≠ ax.O)
    (s : SegCong X Y (ax.O : P) (B : P)) : slen α ax X Y = Pas.len ax ax.O B := by
  have hc := (exists_layoff α ax h).choose_spec
  have e0 : slen α ax X Y = Pas.len ax ax.O (exists_layoff α ax h).choose := by
    rw [slen]; simp only [h, ↓reduceDIte]
  rw [e0]
  refine (Pas.len_eq_iff ax (Ne.symm hc.1) (Ne.symm hB)).2 ?_
  have hc1 : (ax.O : P) ≠ ((exists_layoff α ax h).choose : P) := fun e =>
    hc.1 (Subtype.ext e).symm
  have hB1 : (ax.O : P) ≠ (B : P) := fun e => hB (Subtype.ext e).symm
  show SegCong (ax.O : P) ((exists_layoff α ax h).choose : P) (ax.O : P) (B : P)
  exact segCong_trans (L := L) hc1 h hB1 (segCong_symm (L := L) h hc1 hc.2) s

theorem slen_pos {X Y : P} (h : X ≠ Y) : 0 < slen α ax X Y := by
  obtain ⟨B, hB, s⟩ := exists_layoff α ax h
  rw [slen_spec α ax h hB s]
  exact Pas.len_pos ax (Ne.symm hB)

theorem slen_nonneg (X Y : P) : 0 ≤ slen α ax X Y := by
  by_cases h : X = Y
  · subst h; rw [slen_self]
  · exact (slen_pos α ax h).le

/-- **Two segments of space are congruent iff their lengths are equal.** -/
theorem slen_eq_iff {X Y Z W : P} (h : X ≠ Y) (h' : Z ≠ W) :
    slen α ax X Y = slen α ax Z W ↔ SegCong X Y Z W := by
  obtain ⟨B, hB, s⟩ := exists_layoff α ax h
  obtain ⟨C, hC', s'⟩ := exists_layoff α ax h'
  have hB1 : (ax.O : P) ≠ (B : P) := fun e => hB (Subtype.ext e).symm
  have hC1 : (ax.O : P) ≠ (C : P) := fun e => hC' (Subtype.ext e).symm
  rw [slen_spec α ax h hB s, slen_spec α ax h' hC' s',
    Pas.len_eq_iff ax (Ne.symm hB) (Ne.symm hC')]
  constructor
  · intro e
    have e' : SegCong (ax.O : P) (B : P) (ax.O : P) (C : P) := e
    exact segCong_trans (L := L) h hC1 h' (segCong_trans (L := L) h hB1 hC1 s e')
      (segCong_symm (L := L) h' hC1 s')
  · intro e
    show SegCong (ax.O : P) (B : P) (ax.O : P) (C : P)
    exact segCong_trans (L := L) hB1 h hC1 (segCong_symm (L := L) h hB1 s)
      (segCong_trans (L := L) h h' hC1 e s')

theorem slen_comm (X Y : P) : slen α ax X Y = slen α ax Y X := by
  by_cases h : X = Y
  · subst h; rfl
  · exact (slen_eq_iff α ax h (Ne.symm h)).2
      (segCong_swap_right (Line := L) (segCong_refl (Line := L) h))

/-- On the plane `α` the length of space is the length of the plane. -/
theorem slen_of_mem (X Y : 𝒫[α]) : slen α ax (X : P) (Y : P) = Pas.len ax X Y := by
  by_cases h : X = Y
  · subst h; rw [slen_self]; simp [Pas.len]
  · have h' : (X : P) ≠ (Y : P) := fun e => h (Subtype.ext e)
    obtain ⟨B, hB, s⟩ := exists_layoff α ax h'
    rw [slen_spec α ax h' hB s]
    exact ((Pas.len_eq_iff ax h (Ne.symm hB)).2 s).symm

/-- **Lengths add** along a line of space. -/
theorem slen_add {X Y Z : P} (h : Between X Y Z) :
    slen α ax X Z = slen α ax X Y + slen α ax Y Z := by
  have hXY := ne12_of_between (Line := L) h
  have hYZ := ne23_of_between (Line := L) h
  have hXZ := ne13_of_between (Line := L) h
  obtain ⟨B, hB, s1⟩ := exists_layoff α ax hXY
  have hOB : (ax.O : P) ≠ (B : P) := fun e => hB (Subtype.ext e).symm
  obtain ⟨C, hbC, sC⟩ := Pas.exists_extend (L := L) hOB hYZ
  have hCα : C ∈ α :=
    mem_plane_of_collinear (L := L) α ax.O.2 B.2 hOB (collinear_of_between hbC)
  have hOC := ne13_of_between (Line := L) hbC
  have hBC := ne23_of_between (Line := L) hbC
  have s2 : SegCong Y Z (B : P) C := segCong_symm (L := L) hBC hYZ sC
  have s3 : SegCong X Z (ax.O : P) C := segCong_add h hbC s1 s2
  have e1 : slen α ax X Z = Pas.len ax ax.O ⟨C, hCα⟩ :=
    slen_spec α ax hXZ (B := ⟨C, hCα⟩) (fun e => hOC (congrArg Subtype.val e).symm) s3
  have e2 : slen α ax Y Z = Pas.len ax B ⟨C, hCα⟩ := by
    rw [← slen_of_mem α ax B ⟨C, hCα⟩]
    exact (slen_eq_iff α ax hYZ hBC).2 s2
  rw [e1, slen_spec α ax hXY hB s1, e2]
  exact Pas.len_add ax (X := ax.O) (Y := B) (Z := ⟨C, hCα⟩) hbC

/-! ## The length of space in a plane (with Archimedes's axiom) -/

section Archi

variable [hA : Archimedes P L]

include hA

/-- **In every plane, the length of space is proportional to the length of the plane** (the two
fields of segments being embedded into `ℝ`). -/
theorem slen_plane (π : Pl) (bx : Pas.Axes 𝒫[π] ℒ[π]) (ιK : Pas.G ax →+*o ℝ)
    (ιπ : Pas.G bx →+*o ℝ) (X Y : 𝒫[π]) :
    ιK (slen α ax (X : P) (Y : P)) =
      ιπ (Pas.len bx X Y) * ιK (slen α ax (bx.O : P) (bx.E : P)) := by
  let pt : Pas.G bx → 𝒫[π] := fun g => Pas.ofV (g : Pas.V bx)
  let T : Pas.G bx → ℝ := fun g => ιK (slen α ax (bx.O : P) (pt g : P))
  have hadd : ∀ g h : Pas.G bx, 0 < g → 0 < h → T (g + h) = T g + T h := by
    intro g h hg hh
    have hb : Between bx.O (pt g) (pt (g + h)) := Pas.between_pos bx hg hh
    have hb' : Between (bx.O : P) (pt g : P) (pt (g + h) : P) := hb
    have e1 := slen_add α ax hb'
    have e2 := Pas.len_add bx hb
    have l1 : Pas.len bx bx.O (pt (g + h)) = g + h :=
      Pas.len_of_pos bx ((Pas.pos_iff_posG bx).1 (add_pos hg hh))
    have l2 : Pas.len bx bx.O (pt g) = g := Pas.len_of_pos bx ((Pas.pos_iff_posG bx).1 hg)
    have l3 : Pas.len bx bx.O (pt h) = h := Pas.len_of_pos bx ((Pas.pos_iff_posG bx).1 hh)
    rw [l1, l2] at e2
    have e3 : Pas.len bx (pt g) (pt (g + h)) = Pas.len bx bx.O (pt h) := by
      rw [l3]; exact (add_left_cancel e2).symm
    have hne1 : pt g ≠ pt (g + h) := ne23_of_between (Line := ℒ[π]) hb
    have hne2 : bx.O ≠ pt h := Ne.symm (Pas.ofV_ne_O' bx hh)
    have s : SegCong (pt g : P) (pt (g + h) : P) (bx.O : P) (pt h : P) :=
      (Pas.len_eq_iff bx hne1 hne2).1 e3
    have e4 := (slen_eq_iff α ax (fun e => hne1 (Subtype.ext e))
      (fun e => hne2 (Subtype.ext e))).2 s
    show ιK (slen α ax (bx.O : P) (pt (g + h) : P)) =
      ιK (slen α ax (bx.O : P) (pt g : P)) + ιK (slen α ax (bx.O : P) (pt h : P))
    rw [e1, e4, map_add]
  have hpos : ∀ g : Pas.G bx, 0 < g → 0 < T g := by
    intro g hg
    have hne : (bx.O : P) ≠ (pt g : P) := fun e =>
      Pas.ofV_ne_O' bx hg (Subtype.ext e).symm
    exact orderRingHom_pos ιK (slen_pos α ax hne)
  have hT1 : T 1 = ιK (slen α ax (bx.O : P) (bx.E : P)) := rfl
  by_cases hXY : X = Y
  · subst hXY
    have : Pas.len bx X X = 0 := by simp [Pas.len]
    rw [slen_self, this, map_zero, map_zero, zero_mul]
  · have hg := Pas.len_pos bx hXY
    have s : SegCong (X : P) (Y : P) (bx.O : P) (pt (Pas.len bx X Y) : P) :=
      (Pas.len_spec bx hXY).2
    have hne : (bx.O : P) ≠ (pt (Pas.len bx X Y) : P) := fun e =>
      Pas.ofV_ne_O' bx hg (Subtype.ext e).symm
    have e := (slen_eq_iff α ax (fun e => hXY (Subtype.ext e)) hne).2 s
    rw [e, ← hT1]
    exact additive_pos_eq_mul ιπ T hadd hpos hg

/-- **The theorem of Pythagoras for the length of space**, on the axes of any plane: for a point
`p` of the axis `x` and a point `q` of the axis `y`, `pq² = Op² + Oq²`. -/
theorem slen_pyth (π : Pl) (bx : Pas.Axes 𝒫[π] ℒ[π]) {p q : 𝒫[π]} (hp : p ∈ bx.x)
    (hq : q ∈ bx.y) :
    slen α ax (p : P) (q : P) * slen α ax (p : P) (q : P) =
      slen α ax (bx.O : P) (p : P) * slen α ax (bx.O : P) (p : P) +
        slen α ax (bx.O : P) (q : P) * slen α ax (bx.O : P) (q : P) := by
  have := Pas.archimedean_G ax
  have := Pas.archimedean_G bx
  obtain ⟨ιK⟩ := Real.nonemptyOrderRingHom (Pas.G ax)
  obtain ⟨ιπ⟩ := Real.nonemptyOrderRingHom (Pas.G bx)
  apply ιK.toRingHom.injective
  show ιK _ = ιK _
  rw [map_add, map_mul, map_mul, map_mul, slen_plane α ax π bx ιK ιπ p q,
    slen_plane α ax π bx ιK ιπ bx.O p, slen_plane α ax π bx ιK ιπ bx.O q]
  have hpy : Pas.py bx p = 0 := (Pas.mem_x_iff bx p).1 hp
  have hqx : Pas.px bx q = 0 := (Pas.mem_y_iff bx q).1 hq
  have hOx : Pas.py bx bx.O = 0 := (Pas.mem_x_iff bx bx.O).1 bx.hOx
  have hOy : Pas.px bx bx.O = 0 := (Pas.mem_y_iff bx bx.O).1 bx.hOy
  have k1 := Pas.len_sq bx p q
  have k2 := Pas.len_sq bx bx.O p
  have k3 := Pas.len_sq bx bx.O q
  rw [hpy, hqx] at k1
  rw [hpy, hOx, hOy] at k2
  rw [hqx, hOx, hOy] at k3
  have key : Pas.len bx p q * Pas.len bx p q =
      Pas.len bx bx.O p * Pas.len bx bx.O p + Pas.len bx bx.O q * Pas.len bx bx.O q := by
    rw [k1, k2, k3]; ring
  have key' := congrArg ιπ key
  rw [map_add, map_mul, map_mul, map_mul] at key'
  linear_combination (ιK (slen α ax (bx.O : P) (bx.E : P)) *
    ιK (slen α ax (bx.O : P) (bx.E : P))) * key'

end Archi

end Length

end SpaceCoord

end HilbertFoundations
