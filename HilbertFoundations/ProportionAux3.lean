import HilbertFoundations.ProportionAux2
import HilbertFoundations.Analytic

/-!
# Helper module for `Proportion.lean`: order on a line and Archimedes's axiom (§ 17)

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV and axes
`ax`.

* On the axis `x`, betweenness is the order of the field of segments (`between_iff_lt`).
* With Archimedes's axiom V the field of segments is archimedean (`archimedean_G`), hence it embeds
  into `ℝ` as an ordered field (mathlib's `Real.nonemptyOrderRingHom`); the points of every line then
  correspond to real numbers, betweenness going over into the order (`exists_real_coord`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section LineOrderSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- Points of the axis in increasing order follow each other. -/
theorem between_of_lt {a b c : G ax} (hab : a < b) (hbc : b < c) :
    Between (ofV (a : V ax)) (ofV (b : V ax)) (ofV (c : V ax)) := by
  have h1 := between_pos ax (sub_pos.2 hab) (sub_pos.2 hbc)
  set T := tr (L := L) ax.O (ofV (a : V ax))
  have hT : T ∈ isom (L := L) := transl_isom (tr_mem _ _)
  have h2 := isom_between hT h1
  have e0 : T ax.O = ofV (a : V ax) := tr_apply_O _ _
  have e1 : ∀ t : G ax, T (ofV (t : V ax)) = ofV ((a + t : G ax) : V ax) := by
    intro t
    apply ofV_injective (O := ax.O)
    show toV ax.O (T _) = _
    rw [tr_vec]; rfl
  rw [e0, e1, e1, show a + (b - a) = b by ring, show a + (b - a + (c - b)) = c by ring] at h2
  exact h2

/-- **On the axis, betweenness is the order of the field of segments.** -/
theorem between_iff_lt (a b c : G ax) :
    Between (ofV (a : V ax)) (ofV (b : V ax)) (ofV (c : V ax)) ↔
      (a < b ∧ b < c) ∨ (c < b ∧ b < a) := by
  constructor
  · intro h
    have hab : a ≠ b := fun e => ne12_of_between (Line := L) h (by rw [e])
    have hbc : b ≠ c := fun e => ne23_of_between (Line := L) h (by rw [e])
    have hac : a ≠ c := fun e => ne13_of_between (Line := L) h (by rw [e])
    rcases lt_or_gt_of_ne hab with h1 | h1
    · rcases lt_or_gt_of_ne hbc with h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · exfalso
        rcases lt_or_gt_of_ne hac with h3 | h3
        · exact not_between_swap23 (Line := L) h (between_of_lt ax h3 h2)
        · exact not_between_swap12 (Line := L) h (between_symm (between_of_lt ax h3 h1))
    · rcases lt_or_gt_of_ne hbc with h2 | h2
      · exfalso
        rcases lt_or_gt_of_ne hac with h3 | h3
        · exact not_between_swap12 (Line := L) h (between_of_lt ax h1 h3)
        · exact not_between_swap23 (Line := L) h (between_symm (between_of_lt ax h2 h3))
      · exact Or.inr ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact between_of_lt ax h1 h2
    · exact between_symm (between_of_lt ax h1 h2)

/-- A point of the axis `x` is its own first co-ordinate. -/
theorem eq_of_mem_x {Z : P} (hZ : Z ∈ ax.x) : Z = ofV ((px ax Z : G ax) : V ax) := by
  have h := (coords_x ax ⟨toV ax.O Z, hZ⟩).1
  have : px ax Z = ⟨toV ax.O Z, hZ⟩ := h
  rw [this]; rfl

/-- `n • y` for the points of the axis. -/
theorem len_step {y : G ax} (hy : 0 < y) (m : ℕ) :
    len ax (ofV (((m : ℕ) • y : G ax) : V ax)) (ofV ((((m + 1 : ℕ)) • y : G ax) : V ax)) = y := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_smul, zero_add, one_smul]
    have : ofV ((0 : G ax) : V ax) = ax.O := ofV_zero (L := L)
    rw [this]; exact len_of_pos ax ((pos_iff_posG ax).1 hy)
  · have hmy : 0 < (m • y : G ax) := nsmul_pos hy (Nat.pos_iff_ne_zero.1 hm)
    have hb := between_pos ax hmy hy
    have e : (m • y + y : G ax) = (m + 1 : ℕ) • y := by rw [succ_nsmul]
    rw [e] at hb
    have := len_add ax hb
    have h0 : ofV ((0 : G ax) : V ax) = ax.O := ofV_zero (L := L)
    rw [len_of_pos ax ((pos_iff_posG ax).1 hmy),
      len_of_pos ax ((pos_iff_posG ax).1 (nsmul_pos hy (Nat.succ_ne_zero m)))] at this
    simp only [Nat.succ_eq_add_one] at this
    linear_combination -this - e

end LineOrderSec

section ArchimedesSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L] [hV : Archimedes P L]
include hC hP hV

variable (ax : Axes P L)
include ax

/-- **With Archimedes's axiom the field of segments is archimedean.** -/
theorem archimedean_G : Archimedean (G ax) := by
  refine ⟨fun x y hy => ?_⟩
  by_cases hxy : x ≤ y
  · exact ⟨1, by rw [one_nsmul]; exact hxy⟩
  push Not at hxy
  have hx : 0 < x := hy.trans hxy
  set A : ℕ → P := fun n => ofV (((n : ℕ) • y : G ax) : V ax)
  have h0 : A 0 = ax.O := by simp only [A, zero_smul]; exact ofV_zero (L := L)
  have hB : Between (A 0) (A 1) (ofV (x : V ax)) := by
    rw [h0]
    have := between_pos ax hy (sub_pos.2 hxy)
    simp only [A, one_smul]
    rwa [show y + (x - y) = x by ring] at this
  have hseq : ∀ n : ℕ, Between (A n) (A (n + 1)) (A (n + 2)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h0]
      have := between_pos ax hy hy
      simp only [A, zero_add, one_smul]
      rwa [show y + y = 2 • y by rw [two_nsmul]] at this
    · exact between_of_lt ax (by
        show (n • y : G ax) < (n + 1 : ℕ) • y
        rw [succ_nsmul]; exact lt_add_of_pos_right _ hy) (by
        show ((n + 1 : ℕ) • y : G ax) < (n + 2 : ℕ) • y
        rw [show n + 2 = (n + 1) + 1 by ring, succ_nsmul (n := n + 1)]
        exact lt_add_of_pos_right _ hy)
  have hcong : ∀ m n : ℕ, SegCong (A m) (A (m + 1)) (A n) (A (n + 1)) := by
    intro m n
    have hm := ne12_of_between (Line := L) (hseq m)
    have hn := ne12_of_between (Line := L) (hseq n)
    rw [← len_eq_iff ax hm hn]
    exact (len_step ax hy m).trans (len_step ax hy n).symm
  obtain ⟨n, hn⟩ := Archimedes.ax_V (Line := L) A (ofV (x : V ax)) hB hseq hcong
  rw [h0] at hn
  refine ⟨n, ?_⟩
  -- `x` lies between `O` and `n y`
  have hr : A n ∈ ray ax.O (ofV (x : V ax)) := mem_ray_of_between' hn
  have hpos : PosG ax (n • y) := sameSidePt_trans (ofV_pos ax hx) hr
  have := len_add ax hn
  rw [len_of_pos ax ((pos_iff_posG ax).1 hx), len_of_pos ax hpos] at this
  rw [this]
  exact le_of_lt (lt_add_of_pos_right _ (len_pos ax (ne23_of_between (Line := L) hn)))

end ArchimedesSec

section Pythagoras

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

theorem coe_negG (q : G ax) : ((-q : G ax) : V ax) = -(q : V ax) := rfl

/-- The co-ordinates of `J v`: `(-y, x)`. -/
theorem coords_jE (v : V ax) : xc ax (jE ax v) = -yc ax v ∧ yc ax (jE ax v) = xc ax v := by
  refine coords_of ax (-yc ax v) (xc ax v) ?_
  conv_lhs => rw [coords_eq ax v]
  rw [map_add, jE_jE_apply, coe_negG]
  abel

/-- The co-ordinates of `σ v` (reflection in `x`): `(x, -y)`. -/
theorem coords_sE (v : V ax) : xc ax (sE ax v) = xc ax v ∧ yc ax (sE ax v) = -yc ax v := by
  refine coords_of ax (xc ax v) (-yc ax v) ?_
  conv_lhs => rw [coords_eq ax v]
  rw [map_add, sE_X ax (xc ax v).2, sE_Y ax (jE_X ax (yc ax v).2), coe_negG, map_neg]

/-- **The Pythagorean identity**: the co-ordinates `(c, s)` of the image of `E` under a rotation
satisfy `c² + s² = 1`. -/
theorem pyth_rot {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) :
    xc ax (rE ax hρ (eV ax)) * xc ax (rE ax hρ (eV ax)) +
      yc ax (rE ax hρ (eV ax)) * yc ax (rE ax hρ (eV ax)) = 1 := by
  set c := xc ax (rE ax hρ (eV ax))
  set s := yc ax (rE ax hρ (eV ax))
  have hinv := (rot (L := L) ax.O).inv_mem hρ
  -- `ρ⁻¹ E = c + J (-s)`
  have h1 : rE ax hinv (eV ax) = (c : V ax) + jE ax ((-s : G ax) : V ax) := by
    rw [← sE_conj ax hρ]
    show sE ax (rE ax hρ (sE ax (eV ax))) = _
    rw [sE_X ax (eV_mem ax)]
    obtain ⟨e1, e2⟩ := coords_sE ax (rE ax hρ (eV ax))
    rw [coords_eq ax (sE ax (rE ax hρ (eV ax))), e1, e2]
  -- `ρ (ρ⁻¹ E) = E`
  have h2 : rE ax hρ (rE ax hinv (eV ax)) = eV ax := by
    show toV ax.O (ρ (ofV (toV ax.O (ρ⁻¹ (ofV (eV ax)))))) = eV ax
    simp only [ofV_toV, perm_apply_inv]; rfl
  rw [h1, map_add] at h2
  have hJ : rE ax hρ (jE ax ((-s : G ax) : V ax)) = jE ax (rE ax hρ ((-s : G ax) : V ax)) :=
    congrArg (fun T : AddMonoid.End (V ax) => T _) (jE_comm ax hρ).symm
  rw [hJ] at h2
  have hx := congrArg (xc ax) h2
  rw [xc_add, (coords_jE ax _).1, (rot_coords ax hρ c).1, (rot_coords ax hρ (-s)).2] at hx
  have h1x : xc ax (eV ax) = 1 := (coords_x ax 1).1
  rw [h1x] at hx
  linear_combination hx

/-- Every vector `v ≠ 0` is `ρ (len O v)` for a rotation `ρ`. -/
theorem exists_rot_of_vec {Z : P} (hZ : Z ≠ ax.O) :
    ∃ ρ : Equiv.Perm P, ∃ hρ : ρ ∈ rot (L := L) ax.O,
      toV ax.O Z = rE ax hρ ((len ax ax.O Z : G ax) : V ax) := by
  obtain ⟨U, hUr, sU⟩ := segCong_layoff (L := L) ax.hOE (Ne.symm hZ)
  have hUO : U ≠ ax.O := ne_of_mem_ray hUr
  obtain ⟨ρ, hρ, hρE⟩ := exists_rot (L := L) ax.hOx ax.hEx (Ne.symm ax.hOE) hUO sU
  refine ⟨ρ, hρ, ?_⟩
  obtain ⟨hℓ, sℓ⟩ := len_spec ax (Ne.symm hZ)
  have hρℓ : ρ (ofV (len ax ax.O Z : V ax)) ∈ ray ax.O U := by
    have := isom_ray (rot_isom hρ) hℓ
    rwa [rot_fix hρ, hρE] at this
  have s1 : SegCong ax.O (ofV (len ax ax.O Z : V ax)) ax.O (ρ (ofV (len ax ax.O Z : V ax))) := by
    have := rot_isom hρ ax.O (ofV (len ax ax.O Z : V ax)) (Ne.symm (ne_of_mem_ray hℓ))
    rwa [rot_fix hρ] at this
  have hOℓ : ax.O ≠ ofV (len ax ax.O Z : V ax) := Ne.symm (ne_of_mem_ray hℓ)
  have hZr : Z ∈ ray ax.O U := mem_ray_comm hUr
  have e : Z = ρ (ofV (len ax ax.O Z : V ax)) :=
    eq_of_segCong_ray (L := L) hOℓ hZr hρℓ (segCong_symm (L := L) (Ne.symm hZ) hOℓ sℓ) s1
  exact congrArg (toV ax.O) e

/-- **The field of segments is Pythagorean**: `1 + t²` is a square (the theorem of Pythagoras for
the right triangle with legs `1` and `t`). -/
theorem pythagorean (t : G ax) : ∃ h : G ax, 0 < h ∧ h * h = 1 + t * t := by
  set Z := mkPt ax 1 t
  obtain ⟨hZx, hZy⟩ := mkPt_coords ax 1 t
  have hZ : Z ≠ ax.O := by
    intro e
    have : px ax Z = 0 := by rw [e]; unfold px; rw [toV_O ax]; exact xc_zero ax
    rw [hZx] at this; exact one_ne_zero this
  obtain ⟨ρ, hρ, e⟩ := exists_rot_of_vec ax hZ
  refine ⟨len ax ax.O Z, len_pos ax (Ne.symm hZ), ?_⟩
  have h1 : px ax Z = len ax ax.O Z * xc ax (rE ax hρ (eV ax)) := by
    unfold px; rw [e]; exact (rot_coords ax hρ _).1
  have h2 : py ax Z = len ax ax.O Z * yc ax (rE ax hρ (eV ax)) := by
    unfold py; rw [e]; exact (rot_coords ax hρ _).2
  rw [hZx] at h1; rw [hZy] at h2
  have hp := pyth_rot ax hρ
  linear_combination (-(len ax ax.O Z * len ax ax.O Z)) * hp
    + (-(len ax ax.O Z * xc ax (rE ax hρ (eV ax)) + 1)) * h1
    + (-(len ax ax.O Z * yc ax (rE ax hρ (eV ax)) + t)) * h2

end Pythagoras

section RealCoord

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L] [hV : Archimedes P L]
include hC hP hV

/-- **The points of a line correspond to real numbers** (with Archimedes's axiom): there is a map
`f` of the points to `ℝ`, injective on the line `ℓ`, such that betweenness on `ℓ` goes over into
the order of `ℝ`, and every number of Hilbert's field `Ω` is the image of a point of `ℓ`. -/
theorem exists_real_coord (ℓ : L) :
    ∃ f : P → ℝ, (∀ Z W : P, Z ∈ ℓ → W ∈ ℓ → f Z = f W → Z = W) ∧
      (∀ A B C : P, A ∈ ℓ → B ∈ ℓ → C ∈ ℓ → Between A B C →
        (f A < f B ∧ f B < f C) ∨ (f C < f B ∧ f B < f A)) ∧
      ∀ ω : ℝ, ω ∈ Omega → ∃ Z : P, Z ∈ ℓ ∧ f Z = ω := by
  obtain ⟨O, E, hOE, hO, hE⟩ := exists_two_points (Point := P) ℓ
  obtain ⟨ax, hO', hE'⟩ := exists_axes (L := L) hOE
  have hℓ : ℓ = ax.x := by
    subst hO' hE'
    exact line_unique ax.hOE hO hE ax.hOx ax.hEx
  subst hℓ
  have := archimedean_G ax
  obtain ⟨ι⟩ := Real.nonemptyOrderRingHom (G ax)
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hmono : StrictMono ι := (OrderHomClass.mono ι).strictMono_of_injective hinj
  refine ⟨fun Z => ι (px ax Z), fun Z W hZ hW h => ?_, fun A B C hA hB hC hb => ?_, ?_⟩
  · rw [eq_of_mem_x ax hZ, eq_of_mem_x ax hW, hinj h]
  · rw [eq_of_mem_x ax hA, eq_of_mem_x ax hB, eq_of_mem_x ax hC, between_iff_lt] at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hmono h1, hmono h2⟩
    · exact Or.inr ⟨hmono h1, hmono h2⟩
  · -- the image of `ι` is a subfield closed under `√(1 + w²)`
    have hS : ∀ w ∈ (ι : G ax →+* ℝ).fieldRange, Real.sqrt (1 + w ^ 2) ∈
        (ι : G ax →+* ℝ).fieldRange := by
      intro w hw
      obtain ⟨t, rfl⟩ := RingHom.mem_fieldRange.1 hw
      obtain ⟨h, hh, e⟩ := pythagorean ax t
      refine RingHom.mem_fieldRange.2 ⟨h, ?_⟩
      have h0 : 0 ≤ ι h := by
        have := OrderHomClass.mono ι (le_of_lt hh); rwa [map_zero] at this
      have e2 : ι h * ι h = 1 + (ι t) ^ 2 := by
        rw [← map_mul, e, map_add, map_one, map_mul, sq]
      show ι h = _
      conv_lhs => rw [← Real.sqrt_mul_self h0]
      rw [e2]
      rfl
    intro ω hω
    obtain ⟨g, rfl⟩ := RingHom.mem_fieldRange.1 (Omega_le_of_closed _ hS hω)
    refine ⟨ofV (g : V ax), g.2, ?_⟩
    show ι (xc ax (toV ax.O (ofV (g : V ax)))) = ι g
    rw [toV_ofV, (coords_x ax g).1]

end RealCoord

end Pas

end HilbertFoundations
