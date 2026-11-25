import HilbertFoundations.PascalAux3

/-!
# Helper module for `Pascal.lean`: the commuting operators of the rotations

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV, with
rectangular axes `ax : Axes P L` (origin `O`, unit point `E`, axes `x = OE` and `y ⟂ x`, the
rotation `J` taking `x` to `y`).

The vectors with origin `O` form a commutative group `V = Vec O`; isometries fixing `O` act on it
as additive maps, i.e. as elements of the ring `End V`. In this ring:

* all rotations about `O` commute (`PascalAux3.rot_comm`), `J * J = -1`, and the reflection `σ` in
  `x` conjugates a rotation into its inverse;
* consequently, for a rotation `ρ`, the operators `A ρ = ρ + ρ⁻¹` and `B ρ = J ρ⁻¹ - J ρ` all commute
  with each other and map the axis `x` into itself (`A ρ` is twice the "cosine", `B ρ` twice the
  "sine" of the angle of `ρ`).

For a line `ℓ` through `O` other than `y`, the **slope map** `slope ℓ : x → x` is defined by
`u + J (slope ℓ u) ∈ ℓ`; for `ℓ = ρ x` it satisfies `slope ℓ (A ρ g) = B ρ g`. Therefore **all
slope maps commute** (`slope_comm`): this is the core of Pascal's theorem and of the commutativity
of Hilbert's multiplication of segments; it plays the role of Hilbert's lemma `αβc = βαc`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section Operators

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

/-- The vectors of the axes. -/
abbrev V (ax : Axes P L) := Vec ax.O

/-- The subgroup of the axis `x`. -/
def Xs (ax : Axes P L) : AddSubgroup (V ax) := lineSub (L := L) ax.x ax.hOx

/-- The subgroup of the axis `y`. -/
def Ys (ax : Axes P L) : AddSubgroup (V ax) := lineSub (L := L) ax.y ax.hOy

/-- The additive map of an isometry fixing `O`. -/
noncomputable def endo {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (hfO : f ax.O = ax.O) :
    AddMonoid.End (V ax) := isomHom hf hfO

theorem endo_apply {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (hfO : f ax.O = ax.O) (v : V ax) :
    endo ax hf hfO v = toV ax.O (f (ofV v)) := rfl

/-- The additive map of a rotation about `O`. -/
noncomputable def rE {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) : AddMonoid.End (V ax) :=
  endo ax (rot_isom hρ) (rot_fix hρ)

theorem rE_apply {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) (v : V ax) :
    rE ax hρ v = toV ax.O (ρ (ofV v)) := rfl

theorem rE_mul {ρ ρ' : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) (hρ' : ρ' ∈ rot (L := L) ax.O) :
    rE ax ((rot (L := L) ax.O).mul_mem hρ hρ') = rE ax hρ * rE ax hρ' := by
  ext v; rfl

theorem rE_comm {ρ ρ' : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O)
    (hρ' : ρ' ∈ rot (L := L) ax.O) : Commute (rE ax hρ) (rE ax hρ') := by
  show rE ax hρ * rE ax hρ' = rE ax hρ' * rE ax hρ
  ext v
  show toV ax.O ((ρ * ρ') (ofV v)) = toV ax.O ((ρ' * ρ) (ofV v))
  rw [rot_comm hρ hρ']

/-- The reflection `σ` in the axis `x`. -/
noncomputable def sE : AddMonoid.End (V ax) :=
  endo ax (refl_isom (P := P) ax.x) (refl_fix ax.hOx)

/-- `J` as an operator. -/
noncomputable def jE : AddMonoid.End (V ax) := rE ax ax.hJ

theorem mem_Xs {v : V ax} : v ∈ Xs ax ↔ ofV v ∈ ax.x := Iff.rfl

theorem mem_Ys {v : V ax} : v ∈ Ys ax ↔ ofV v ∈ ax.y := Iff.rfl

theorem neg_eq_ht (v : V ax) : -v = toV ax.O (ht (L := L) ax.O (ofV v)) := vneg_def (L := L) v

theorem jE_jE : jE ax * jE ax = -1 := by
  ext v
  show toV ax.O (ax.J (ax.J (ofV v))) = -v
  rw [neg_eq_ht, ← Equiv.Perm.mul_apply, ax.JJ]

theorem jE_jE_apply (v : V ax) : jE ax (jE ax v) = -v := by
  have := congrArg (fun T : AddMonoid.End (V ax) => T v) (jE_jE ax)
  exact this

theorem sE_X {v : V ax} (hv : v ∈ Xs ax) : sE ax v = v := by
  show toV ax.O (refl ax.x (ofV v)) = v
  rw [refl_fix hv]; rfl

theorem sE_Y {v : V ax} (hv : v ∈ Ys ax) : sE ax v = -v := by
  show toV ax.O (refl ax.x (ofV v)) = -v
  rw [ax.reflx_y _ hv, neg_eq_ht]

theorem jE_X {v : V ax} (hv : v ∈ Xs ax) : jE ax v ∈ Ys ax := ax.Jx _ hv

theorem jE_Y {v : V ax} (hv : v ∈ Ys ax) : jE ax v ∈ Xs ax := by
  show ax.J (ofV v) ∈ ax.x
  have hJi := rot_isom ax.hJ
  have hJF : ax.J ax.F = ht (L := L) ax.O ax.E := by
    rw [← ax.JE, ← Equiv.Perm.mul_apply, ax.JJ]
  have hE' : ht (L := L) ax.O ax.E ∈ ax.x := by
    have := ((ht_eq_iff (L := L) (Ne.symm ax.hOE)).1 rfl).1
    exact mem_right_of_between this ax.hEx ax.hOx
  exact isom_mem_line hJi ax.hOF ax.hOy ax.hFy hv (by rw [rot_fix ax.hJ]; exact ax.hOx)
    (by rw [hJF]; exact hE')

theorem X_inf_Y {v : V ax} (h1 : v ∈ Xs ax) (h2 : v ∈ Ys ax) : v = 0 := by
  have := ax.hxy _ h1 h2
  exact ofV_injective (this.trans (ofV_zero (L := L)).symm)

theorem x_ne_y : ax.x ≠ ax.y := fun e => ax.hOE (ax.hxy _ ax.hEx (e ▸ ax.hEx)).symm

theorem exists_XY (v : V ax) : ∃ p q : V ax, p ∈ Xs ax ∧ q ∈ Ys ax ∧ v = p + q :=
  exists_decomp (L := L) ax.hOx ax.hOy (x_ne_y ax) v

theorem XY_unique {p q p' q' : V ax} (hp : p ∈ Xs ax) (hq : q ∈ Ys ax) (hp' : p' ∈ Xs ax)
    (hq' : q' ∈ Ys ax) (h : p + q = p' + q') : p = p' ∧ q = q' := by
  have h1 : p - p' = q' - q := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have hX : p - p' ∈ Xs ax := (Xs ax).sub_mem hp hp'
  have hY : p - p' ∈ Ys ax := h1 ▸ (Ys ax).sub_mem hq' hq
  have e := X_inf_Y ax hX hY
  refine ⟨sub_eq_zero.1 e, ?_⟩
  rw [e] at h1
  exact (sub_eq_zero.1 h1.symm).symm

/-- Conjugation by `σ` inverts the rotations. -/
theorem sE_conj {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) :
    sE ax * rE ax hρ * sE ax = rE ax ((rot (L := L) ax.O).inv_mem hρ) := by
  ext v
  show toV ax.O ((refl (P := P) ax.x * ρ * refl (P := P) ax.x : Equiv.Perm P) (ofV v)) =
    toV ax.O (ρ⁻¹ (ofV v))
  rw [refl_conj_rot hρ ax.hOx]

theorem jE_comm {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) : Commute (jE ax) (rE ax hρ) :=
  rE_comm ax ax.hJ hρ

/-- The "doubled cosine" `A ρ = ρ + ρ⁻¹`. -/
noncomputable def AE {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) : AddMonoid.End (V ax) :=
  rE ax hρ + rE ax ((rot (L := L) ax.O).inv_mem hρ)

/-- The "doubled sine" `B ρ = J ρ⁻¹ - J ρ`. -/
noncomputable def BE {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) : AddMonoid.End (V ax) :=
  jE ax * rE ax ((rot (L := L) ax.O).inv_mem hρ) - jE ax * rE ax hρ

theorem AE_comm_AE {α β : Equiv.Perm P} (hα : α ∈ rot (L := L) ax.O)
    (hβ : β ∈ rot (L := L) ax.O) : Commute (AE ax hα) (AE ax hβ) := by
  unfold AE
  refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_) <;>
    exact rE_comm ax _ _

theorem BE_comm_BE {α β : Equiv.Perm P} (hα : α ∈ rot (L := L) ax.O)
    (hβ : β ∈ rot (L := L) ax.O) : Commute (BE ax hα) (BE ax hβ) := by
  unfold BE
  have hJ := ax.hJ
  refine Commute.sub_left (Commute.sub_right ?_ ?_) (Commute.sub_right ?_ ?_) <;>
    exact Commute.mul_left (Commute.mul_right (Commute.refl _) (jE_comm ax _))
      (Commute.mul_right (jE_comm ax _).symm (rE_comm ax _ _))

theorem AE_comm_BE {α β : Equiv.Perm P} (hα : α ∈ rot (L := L) ax.O)
    (hβ : β ∈ rot (L := L) ax.O) : Commute (AE ax hα) (BE ax hβ) := by
  unfold AE BE
  refine Commute.add_left (Commute.sub_right ?_ ?_) (Commute.sub_right ?_ ?_) <;>
    exact Commute.mul_right (jE_comm ax _).symm (rE_comm ax _ _)

/-- On the axis `x`: `ρ g + ρ⁻¹ g` lies on `x` and `ρ g - ρ⁻¹ g` on `y`. -/
theorem AE_X {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) {g : V ax} (hg : g ∈ Xs ax) :
    AE ax hρ g ∈ Xs ax ∧ rE ax hρ g - rE ax ((rot (L := L) ax.O).inv_mem hρ) g ∈ Ys ax ∧
      AE ax hρ g + (rE ax hρ g - rE ax ((rot (L := L) ax.O).inv_mem hρ) g) =
        rE ax hρ g + rE ax hρ g := by
  obtain ⟨p, q, hp, hq, e⟩ := exists_XY ax (rE ax hρ g)
  have hinv : rE ax ((rot (L := L) ax.O).inv_mem hρ) g = p - q := by
    rw [← sE_conj ax hρ]
    show sE ax (rE ax hρ (sE ax g)) = p - q
    rw [sE_X ax hg, e, map_add, sE_X ax hp, sE_Y ax hq, sub_eq_add_neg]
  have hA : AE ax hρ g = p + p := by
    show rE ax hρ g + rE ax ((rot (L := L) ax.O).inv_mem hρ) g = p + p
    rw [hinv, e]; abel
  refine ⟨hA ▸ (Xs ax).add_mem hp hp, ?_, ?_⟩
  · rw [hinv, e]
    have : p + q - (p - q) = q + q := by abel
    rw [this]; exact (Ys ax).add_mem hq hq
  · show rE ax hρ g + rE ax ((rot (L := L) ax.O).inv_mem hρ) g + (rE ax hρ g -
      rE ax ((rot (L := L) ax.O).inv_mem hρ) g) = rE ax hρ g + rE ax hρ g
    abel

theorem BE_X {ρ : Equiv.Perm P} (hρ : ρ ∈ rot (L := L) ax.O) {g : V ax} (hg : g ∈ Xs ax) :
    BE ax hρ g ∈ Xs ax ∧ jE ax (BE ax hρ g) =
      rE ax hρ g - rE ax ((rot (L := L) ax.O).inv_mem hρ) g := by
  obtain ⟨-, hD, -⟩ := AE_X ax hρ hg
  have hB : BE ax hρ g = -jE ax (rE ax hρ g - rE ax ((rot (L := L) ax.O).inv_mem hρ) g) := by
    show jE ax (rE ax ((rot (L := L) ax.O).inv_mem hρ) g) - jE ax (rE ax hρ g) = _
    rw [map_sub, neg_sub]
  refine ⟨?_, ?_⟩
  · rw [hB]; exact (Xs ax).neg_mem (jE_Y ax hD)
  · rw [hB, map_neg, jE_jE_apply, neg_neg]

end Operators

section Slopes

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

/-- The half-turn about `M` in vector form: `X ↦ 2M - X`. -/
theorem ht_vec (M X : P) :
    toV ax.O (ht (L := L) M X) = toV ax.O M + toV ax.O M - toV ax.O X := by
  set m := midp (L := L) ax.O M
  have hm : ht (L := L) m ax.O = M := ht_midp ax.O M
  have hmM : ht (L := L) m M = ax.O := by rw [← hm, ht_ht]
  -- `ht M * ht m` is the translation taking `O` to `M`
  have h1 : ht (L := L) M * ht (L := L) m ∈ transl (L := L) ax.O := by
    obtain ⟨Z, hZ⟩ := ht_three (L := L) ax.O m M
    exact ⟨Z, by rw [← hZ, mul_assoc, ht_mul_self, mul_one]⟩
  have h2 : ht (L := L) M * ht (L := L) m = tr (L := L) ax.O M := by
    refine transl_ext h1 (tr_mem ax.O M) ?_
    rw [tr_apply_O, Equiv.Perm.mul_apply, hm, ht_self]
  have hMO : toV ax.O (ht (L := L) M ax.O) = toV ax.O M + toV ax.O M := by
    rw [vadd_def (L := L)]
    show ht (L := L) M ax.O = tr (L := L) ax.O M M
    rw [← h2, Equiv.Perm.mul_apply, hmM]
  have h3 : ht (L := L) M * ht (L := L) ax.O ∈ transl (L := L) ax.O := ⟨M, rfl⟩
  have h4 : ht (L := L) M * ht (L := L) ax.O = tr (L := L) ax.O (ht (L := L) M ax.O) := by
    have := eq_tr h3
    rw [Equiv.Perm.mul_apply, ht_self] at this
    exact this
  have : ht (L := L) M X = ht (L := L) M (ht (L := L) ax.O (ht (L := L) ax.O X)) := by rw [ht_ht]
  rw [this, ← Equiv.Perm.mul_apply, h4, sub_eq_add_neg, neg_eq_ht ax, ← hMO,
    vadd_def (L := L) (toV ax.O (ht (L := L) M ax.O))]
  rfl

/-- **Halving**: every vector of a line through `O` is twice a vector of that line. -/
theorem exists_half {l : L} (hO : ax.O ∈ l) {v : V ax} (hv : v ∈ lineSub (L := L) l hO) :
    ∃ h : V ax, h ∈ lineSub (L := L) l hO ∧ h + h = v := by
  set M := midp (L := L) ax.O (ofV v)
  have hM : ht (L := L) M ax.O = ofV v := ht_midp ax.O (ofV v)
  refine ⟨toV ax.O M, ?_, ?_⟩
  · show M ∈ l
    by_cases e : ofV v = ax.O
    · have : M = ax.O := by
        have := hM; rw [e] at this; exact (ht_fix_iff.1 this).symm
      rw [this]; exact hO
    · have hMO : ax.O ≠ M := by
        intro h; rw [← h, ht_self] at hM; exact e hM.symm
      have hb := ((ht_eq_iff (L := L) hMO).1 hM).1
      exact mem_mid_of_between hb hO hv
  · have := ht_vec ax M ax.O
    rw [hM, show toV ax.O ax.O = (0 : V ax) from (vzero_def (L := L) ax.O).symm, sub_zero] at this
    exact this.symm

theorem two_ne_zero_vec' {v : V ax} (h : v + v = 0) : v = 0 := by
  have h1 : v = -v := eq_neg_of_add_eq_zero_left h
  rw [neg_eq_ht ax] at h1
  have h2 : ht (L := L) ax.O (ofV v) = ofV v := h1.symm
  rw [ht_fix_iff] at h2
  exact ofV_injective (h2.trans (ofV_zero (L := L)).symm)

theorem jE_injective {v : V ax} (h : jE ax v = 0) : v = 0 := by
  have := jE_jE_apply ax v
  rw [h, map_zero] at this
  exact neg_eq_zero.1 this.symm

/-- The slope of a line `ℓ` through `O` other than `y`: for `u` on `x`, the `w` on `x` with
`u + J w ∈ ℓ` exists and is unique. -/
theorem slope_exists {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) {u : V ax} (_hu : u ∈ Xs ax) :
    ∃! w : V ax, w ∈ Xs ax ∧ u + jE ax w ∈ lineSub (L := L) ℓ hO := by
  obtain ⟨m, hum, hm⟩ := exists_parEq (P := P) ax.y (ofV u)
  have hmℓ : Meets (Point := P) m ℓ := by
    by_contra hn
    exact hℓ (eq_of_parEq (parEq_trans hm (Or.inr hn : ParEq (P := P) m ℓ)) ax.hOy hO).symm
  obtain ⟨Z, hZm, hZℓ⟩ := hmℓ
  have hq : toV ax.O Z - u ∈ Ys ax := (mem_line_iff_sub ax.hOy (parEq_symm hm) hum Z).1 hZm
  refine ⟨-jE ax (toV ax.O Z - u), ⟨(Xs ax).neg_mem (jE_Y ax hq), ?_⟩, ?_⟩
  · rw [map_neg, jE_jE_apply, neg_neg, add_sub_cancel]; exact hZℓ
  · rintro w ⟨hw, hwℓ⟩
    have h1 : u + jE ax (-jE ax (toV ax.O Z - u)) ∈ lineSub (L := L) ℓ hO := by
      rw [map_neg, jE_jE_apply, neg_neg, add_sub_cancel]; exact hZℓ
    have h2 : jE ax (w - -jE ax (toV ax.O Z - u)) ∈ lineSub (L := L) ℓ hO := by
      have := (lineSub (L := L) ℓ hO).sub_mem hwℓ h1
      rwa [add_sub_add_left_eq_sub, ← map_sub] at this
    have h3 : jE ax (w - -jE ax (toV ax.O Z - u)) ∈ Ys ax :=
      jE_X ax ((Xs ax).sub_mem hw ((Xs ax).neg_mem (jE_Y ax hq)))
    have h4 := decomp_unique (L := L) hO ax.hOy hℓ h2 h3
    exact sub_eq_zero.1 (jE_injective ax h4)

/-- The **slope map** of a line through `O` other than `y`. -/
noncomputable def slope {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) (u : V ax) : V ax := by
  classical
  exact if hu : u ∈ Xs ax then Classical.choose (slope_exists ax hO hℓ hu) else 0

theorem slope_spec {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) {u : V ax} (hu : u ∈ Xs ax) :
    slope ax hO hℓ u ∈ Xs ax ∧ u + jE ax (slope ax hO hℓ u) ∈ lineSub (L := L) ℓ hO := by
  simp only [slope, hu, ↓reduceDIte]
  exact (Classical.choose_spec (slope_exists ax hO hℓ hu)).1

theorem slope_eq {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) {u w : V ax} (hu : u ∈ Xs ax)
    (hw : w ∈ Xs ax) (h : u + jE ax w ∈ lineSub (L := L) ℓ hO) : slope ax hO hℓ u = w :=
  (slope_exists ax hO hℓ hu).unique (slope_spec ax hO hℓ hu) ⟨hw, h⟩

theorem slope_mem {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) {u : V ax} (hu : u ∈ Xs ax) :
    slope ax hO hℓ u ∈ Xs ax := (slope_spec ax hO hℓ hu).1

theorem slope_add {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) {u u' : V ax} (hu : u ∈ Xs ax)
    (hu' : u' ∈ Xs ax) : slope ax hO hℓ (u + u') = slope ax hO hℓ u + slope ax hO hℓ u' := by
  refine slope_eq ax hO hℓ ((Xs ax).add_mem hu hu')
    ((Xs ax).add_mem (slope_mem ax hO hℓ hu) (slope_mem ax hO hℓ hu')) ?_
  have := (lineSub (L := L) ℓ hO).add_mem (slope_spec ax hO hℓ hu).2 (slope_spec ax hO hℓ hu').2
  rw [map_add]
  convert this using 1
  abel

/-- A rotation carrying `x` into `ℓ`: the slope map of `ℓ` takes `A ρ g` to `B ρ g`. -/
theorem slope_AE {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) {ρ : Equiv.Perm P}
    (hρ : ρ ∈ rot (L := L) ax.O) (hρℓ : ∀ g : V ax, g ∈ Xs ax → rE ax hρ g ∈ lineSub (L := L) ℓ hO)
    {g : V ax} (hg : g ∈ Xs ax) : slope ax hO hℓ (AE ax hρ g) = BE ax hρ g := by
  obtain ⟨hA, -, hsum⟩ := AE_X ax hρ hg
  obtain ⟨hB, hJB⟩ := BE_X ax hρ hg
  refine slope_eq ax hO hℓ hA hB ?_
  rw [hJB, hsum]
  exact (lineSub (L := L) ℓ hO).add_mem (hρℓ g hg) (hρℓ g hg)

/-- `A ρ` maps `x` onto `x` when `ρ` carries `x` onto a line other than `y`. -/
theorem AE_surj {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) {ρ : Equiv.Perm P}
    (hρ : ρ ∈ rot (L := L) ax.O) (_hρℓ : ∀ g : V ax, g ∈ Xs ax → rE ax hρ g ∈ lineSub (L := L) ℓ hO)
    (hρℓ' : ∀ v : V ax, v ∈ lineSub (L := L) ℓ hO →
      rE ax ((rot (L := L) ax.O).inv_mem hρ) v ∈ Xs ax)
    {u : V ax} (hu : u ∈ Xs ax) : ∃ g : V ax, g ∈ Xs ax ∧ AE ax hρ g = u := by
  obtain ⟨h, hh, rfl⟩ := exists_half ax ax.hOx hu
  set Z := h + jE ax (slope ax hO hℓ h)
  have hZ : Z ∈ lineSub (L := L) ℓ hO := (slope_spec ax hO hℓ hh).2
  set g := rE ax ((rot (L := L) ax.O).inv_mem hρ) Z
  have hg : g ∈ Xs ax := hρℓ' Z hZ
  have hρg : rE ax hρ g = Z := by
    show toV ax.O (ρ (ρ⁻¹ (ofV Z))) = Z
    rw [perm_apply_inv]; rfl
  refine ⟨g, hg, ?_⟩
  obtain ⟨hA, hD, hsum⟩ := AE_X ax hρ hg
  have hsum' : AE ax hρ g + (rE ax hρ g - rE ax ((rot (L := L) ax.O).inv_mem hρ) g) =
      (h + h) + (jE ax (slope ax hO hℓ h) + jE ax (slope ax hO hℓ h)) := by
    rw [hsum, hρg]; simp only [Z]; abel
  have hY : jE ax (slope ax hO hℓ h) + jE ax (slope ax hO hℓ h) ∈ Ys ax :=
    (Ys ax).add_mem (jE_X ax (slope_mem ax hO hℓ hh)) (jE_X ax (slope_mem ax hO hℓ hh))
  exact (XY_unique ax hA hD ((Xs ax).add_mem hh hh) hY hsum').1

/-- Every line through `O` is the image of `x` under a rotation. -/
theorem exists_rot_line {ℓ : L} (hO : ax.O ∈ ℓ) :
    ∃ ρ : Equiv.Perm P, ∃ hρ : ρ ∈ rot (L := L) ax.O,
      (∀ g : V ax, g ∈ Xs ax → rE ax hρ g ∈ lineSub (L := L) ℓ hO) ∧
      (∀ v : V ax, v ∈ lineSub (L := L) ℓ hO →
        rE ax ((rot (L := L) ax.O).inv_mem hρ) v ∈ Xs ax) := by
  obtain ⟨Z0, Z1, hZ01, hZ0, hZ1⟩ := exists_two_points (Point := P) ℓ
  obtain ⟨Z, hZℓ, hZO⟩ : ∃ Z, Z ∈ ℓ ∧ Z ≠ ax.O := by
    by_cases e : Z0 = ax.O
    · exact ⟨Z1, hZ1, fun e' => hZ01 (e.trans e'.symm)⟩
    · exact ⟨Z0, hZ0, e⟩
  obtain ⟨Q, hQr, sQ⟩ := segCong_layoff (L := L) ax.hOE (Ne.symm hZO)
  have hQO : Q ≠ ax.O := ne_of_mem_ray hQr
  have hQℓ : Q ∈ ℓ := mem_of_collinear (collinear_of_mem_ray hQr) (Ne.symm hZO) hO hZℓ
  obtain ⟨ρ, hρ, hρE⟩ := exists_rot (L := L) ax.hOx ax.hEx (Ne.symm ax.hOE) hQO sQ
  have hρi := rot_isom hρ
  refine ⟨ρ, hρ, fun g hg => ?_, fun v hv => ?_⟩
  · exact isom_mem_line hρi ax.hOE ax.hOx ax.hEx hg (by rw [rot_fix hρ]; exact hO)
      (by rw [hρE]; exact hQℓ)
  · have hρi' := rot_isom ((rot (L := L) ax.O).inv_mem hρ)
    have hQE : ρ⁻¹ Q = ax.E := by rw [Equiv.Perm.inv_eq_iff_eq, hρE]
    exact isom_mem_line hρi' (Ne.symm hQO) hO hQℓ hv
      (by rw [rot_fix ((rot (L := L) ax.O).inv_mem hρ)]; exact ax.hOx)
      (by rw [hQE]; exact ax.hEx)

/-- **All slope maps commute.** -/
theorem slope_comm {ℓ ℓ' : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) (hO' : ax.O ∈ ℓ')
    (hℓ' : ℓ' ≠ ax.y) {u : V ax} (hu : u ∈ Xs ax) :
    slope ax hO hℓ (slope ax hO' hℓ' u) = slope ax hO' hℓ' (slope ax hO hℓ u) := by
  obtain ⟨α, hα, hαℓ, hαℓ'⟩ := exists_rot_line ax hO
  obtain ⟨β, hβ, hβℓ, hβℓ'⟩ := exists_rot_line ax hO'
  obtain ⟨g1, hg1, rfl⟩ := AE_surj ax hO hℓ hα hαℓ hαℓ' hu
  obtain ⟨g, hg, rfl⟩ := AE_surj ax hO' hℓ' hβ hβℓ hβℓ' hg1
  have hAg := (AE_X ax hα hg).1
  have hBg := (BE_X ax hβ hg).1
  have hBg' := (BE_X ax hα hg).1
  have hAg' := (AE_X ax hβ hg).1
  have e1 : slope ax hO' hℓ' (AE ax hα (AE ax hβ g)) = AE ax hα (BE ax hβ g) := by
    rw [show AE ax hα (AE ax hβ g) = AE ax hβ (AE ax hα g) from
      congrArg (fun T : AddMonoid.End (V ax) => T g) (AE_comm_AE ax hα hβ),
      slope_AE ax hO' hℓ' hβ hβℓ hAg]
    exact congrArg (fun T : AddMonoid.End (V ax) => T g) (AE_comm_BE ax hα hβ).symm
  have e2 : slope ax hO hℓ (AE ax hα (AE ax hβ g)) = AE ax hβ (BE ax hα g) := by
    rw [slope_AE ax hO hℓ hα hαℓ hAg']
    exact congrArg (fun T : AddMonoid.End (V ax) => T g) (AE_comm_BE ax hβ hα).symm
  rw [e1, e2, slope_AE ax hO hℓ hα hαℓ hBg, slope_AE ax hO' hℓ' hβ hβℓ hBg']
  exact congrArg (fun T : AddMonoid.End (V ax) => T g) (BE_comm_BE ax hα hβ)

end Slopes

end Pas

end HilbertFoundations
