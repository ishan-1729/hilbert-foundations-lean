import HilbertFoundations.CoordinatesCloseAux

/-!
# Helper for the co-ordinates of space (§ 17, § 30): from the co-ordinates of a plane to space

Helper module of `CoordinatesClose.lean` (units `s17.space`, `s30.any_dimension`).

Let `α` be a plane of a geometry of space with I–III, co-ordinatized by a two-dimensional vector
space `V` over a skew field `K`: a bijection `e` of the points of `α` with `V` under which the lines
of `α` are the lines `{r d + O}` of `V` (`LineHyp`). With two parallel projections `p₁`, `p₂` of
space onto `α` (along lines `d₁`, `d₂` through a point of `α`) a point `X` gets the co-ordinates
`(q₁ X, h X) ∈ V × K`, where `q₁ X = e (p₁ X)` and `e (p₂ X) = q₁ X + h X • u` (`u` the direction
of the trace of the plane `d₁d₂`). Every line of space is mapped onto a line of `V × K`
(`isImg_main`): for a line not in a plane parallel to `d₁d₂` because the parallel projection in `α`
between two lines is affine (`height_affine`), and for the remaining lines through a third
projection `p₃` and the homothety of the triangles `p₁X p₂X p₃X`.
-/

namespace HilbertFoundations

namespace SpaceCoord

open Module SpaceDesargues

universe u v w

/-! ## Lines of a vector space of dimension 2 -/

section Lin

variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]

/-- In a space of dimension 2, a vector `u ≠ 0` and a vector `w` not a multiple of `u` span. -/
theorem exists_comb (hV : finrank K V = 2) {u w : V} (hu : u ≠ 0) (hw : ∀ c : K, w ≠ c • u)
    (x : V) : ∃ a b : K, x = a • u + b • w := by
  have hli : LinearIndependent K ![u, w] :=
    (LinearIndependent.pair_iff' hu).2 fun a h => hw a h.symm
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hV])
  have hx : x ∈ Submodule.span K (Set.range ![u, w]) := hspan ▸ Submodule.mem_top
  have hr : Set.range ![u, w] = {u, w} := by
    ext y; simp [eq_comm, or_comm]
  rw [hr] at hx
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.1 hx
  exact ⟨a, b, h.symm⟩

theorem indep_zero {u w : V} (hu : u ≠ 0) (hw : ∀ c : K, w ≠ c • u) {a b : K}
    (h : a • u + b • w = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.1 h).resolve_right hu, rfl⟩
  · exfalso
    apply hw (-(b⁻¹ * a))
    have h1 : b • w = -(a • u) := eq_neg_of_add_eq_zero_right h
    calc w = b⁻¹ • b • w := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = -(b⁻¹ * a) • u := by rw [h1, smul_neg, smul_smul, neg_smul]

variable (K) in
/-- The line `{r d + O}` of a vector space. -/
def PLine (O d : V) : Set V := {x | ∃ r : K, x = r • d + O}

theorem pline_base (O d : V) : O ∈ PLine K O d := ⟨0, by rw [zero_smul, zero_add]⟩

theorem pline_add {O d x : V} (hx : x ∈ PLine K O d) (s : K) : s • d + x ∈ PLine K O d := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨s + r, by rw [add_smul, add_assoc]⟩

theorem pline_sub {O d x y : V} (hx : x ∈ PLine K O d) (hy : y ∈ PLine K O d) :
    ∃ c : K, y - x = c • d := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  exact ⟨s - r, by rw [sub_smul]; abel⟩

theorem pline_dir_of_subset {O d O' d' : V} (h : PLine K O' d' ⊆ PLine K O d) :
    ∃ c : K, d' = c • d := by
  obtain ⟨c, hc⟩ := pline_sub (h (pline_base O' d')) (h (pline_add (pline_base O' d') 1))
  exact ⟨c, by rw [← hc, one_smul, add_sub_cancel_right]⟩

theorem pline_dir_of_disjoint (hV : finrank K V = 2) {O d O' d' : V} (hd : d ≠ 0)
    (h : ∀ x, x ∈ PLine K O d → x ∉ PLine K O' d') : ∃ c : K, d' = c • d := by
  by_contra hc
  rw [not_exists] at hc
  obtain ⟨a, b, hab⟩ := exists_comb hV hd hc (O' - O)
  refine h (a • d + O) ⟨a, rfl⟩ ⟨-b, ?_⟩
  have : O' = a • d + b • d' + O := by rw [← hab, sub_add_cancel]
  rw [this, neg_smul]
  abel

theorem pline_rebase {O d x₀ : V} (hx : x₀ ∈ PLine K O d) : PLine K x₀ d = PLine K O d := by
  obtain ⟨r₀, rfl⟩ := hx
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r + r₀, by rw [add_smul, add_assoc]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r - r₀, by rw [sub_smul]; abel⟩

end Lin

/-! ## The co-ordinates of the projections -/

section Geo

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
  [hS : SpaceParallels P L Pl]
variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {α : Pl} (e : {A : P // A ∈ α} ≃ V)

variable (K) in
/-- The lines of the plane `α` are the lines of `V`. -/
def LineHyp (e : {A : P // A ∈ α} ≃ V) : Prop :=
  ∀ a : L, LiesInPlane (Point := P) a α → ∃ O d : V, d ≠ 0 ∧
    ∀ Z : {A : P // A ∈ α}, (Z : P) ∈ a ↔ e Z ∈ PLine K O d

variable (K) in
/-- The map `q` sends the line `ℓ` one-to-one onto a line of `V`. -/
def QInj (q : P → V) (ℓ : L) : Prop :=
  ∃ O v : V, v ≠ 0 ∧ (∀ X : P, X ∈ ℓ → q X ∈ PLine K O v) ∧
    (∀ x, x ∈ PLine K O v → ∃ X : P, X ∈ ℓ ∧ q X = x) ∧
    ∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → q X = q X' → X = X'

include hS

/-- The co-ordinates in `α` of the projection of a point. -/
noncomputable def qmap {d : L} (hd : Cuts (P := P) d α) (X : P) : V :=
  e ⟨proj hd X, proj_mem hd X⟩

theorem qmap_line (he : LineHyp K e) {d : L} (hd : Cuts (P := P) d α) {ℓ : L}
    (hℓ : ¬Par (P := P) (Pl := Pl) d ℓ) : QInj K (qmap e hd) ℓ := by
  obtain ⟨m, hmα, h1, h2, h3⟩ := proj_line hd hℓ
  obtain ⟨O, v, hv, hm⟩ := he m hmα
  refine ⟨O, v, hv, fun X hX => (hm ⟨_, proj_mem hd X⟩).1 (h1 X hX), fun x hx => ?_,
    fun X X' hX hX' hq => h3 X X' hX hX' (congrArg Subtype.val (e.injective hq))⟩
  have hx' : ((e.symm x : {A : P // A ∈ α}) : P) ∈ m :=
    (hm (e.symm x)).2 (by rwa [e.apply_symm_apply])
  obtain ⟨X, hX, hpX⟩ := h2 _ hx'
  refine ⟨X, hX, ?_⟩
  have : (⟨proj hd X, proj_mem hd X⟩ : {A : P // A ∈ α}) = e.symm x := Subtype.ext hpX
  unfold qmap
  rw [this, e.apply_symm_apply]

omit [AddCommGroup V] [Module K V] in
theorem qmap_const {d : L} (hd : Cuts (P := P) d α) {ℓ : L}
    (hℓ : Par (P := P) (Pl := Pl) d ℓ) {X X' : P} (hX : X ∈ ℓ) (hX' : X' ∈ ℓ) :
    qmap e hd X = qmap e hd X' := by
  unfold qmap
  exact congrArg e (Subtype.ext (proj_const hd hℓ hX hX'))

omit [AddCommGroup V] [Module K V] in
theorem qmap_of_mem {d : L} (hd : Cuts (P := P) d α) {X : P} (hX : X ∈ α) :
    qmap e hd X = e ⟨X, hX⟩ := by
  unfold qmap
  exact congrArg e (Subtype.ext (proj_of_mem hd hX))

omit [AddCommGroup V] [Module K V] in
theorem qmap_inj_pair {d₁ d₂ : L} (hd₁ : Cuts (P := P) d₁ α) (hd₂ : Cuts (P := P) d₂ α)
    {O : P} (hO₁ : O ∈ d₁) (hO₂ : O ∈ d₂) (h12 : d₁ ≠ d₂) {X Y : P}
    (h1 : qmap e hd₁ X = qmap e hd₁ Y) (h2 : qmap e hd₂ X = qmap e hd₂ Y) : X = Y :=
  proj_inj_pair hd₁ hd₂ hO₁ hO₂ h12 (congrArg Subtype.val (e.injective h1))
    (congrArg Subtype.val (e.injective h2))

/-- **The trace of the plane of two directions.** For two distinct lines `d₁`, `d₂` through a
point `O` of `α` that cut `α`, there is a vector `u ≠ 0` such that the co-ordinates of the two
projections of every point differ by a multiple of `u`; the points of `α` in the plane `d₁d₂` are
those of the line `{r u + e O}`. -/
theorem exists_trace (hV : finrank K V = 2) (he : LineHyp K e) {d₁ d₂ : L}
    (hd₁ : Cuts (P := P) d₁ α) (hd₂ : Cuts (P := P) d₂ α) {O : P} (hOα : O ∈ α) (hO₁ : O ∈ d₁)
    (hO₂ : O ∈ d₂) (h12 : d₁ ≠ d₂) :
    ∃ u : V, u ≠ 0 ∧ (∀ X : P, ∃ h : K, qmap e hd₂ X = qmap e hd₁ X + h • u) ∧
      ∀ (Z : {A : P // A ∈ α}) (γ : Pl), LiesInPlane (Point := P) d₁ γ →
        LiesInPlane (Point := P) d₂ γ → ((Z : P) ∈ γ ↔ e Z ∈ PLine K (e ⟨O, hOα⟩) u) := by
  obtain ⟨γ₀, ⟨h1γ, h2γ⟩, huniq⟩ := theorem2_two_lines (Pl := Pl) h12 hO₁ hO₂
  have hγα : γ₀ ≠ α := by rintro rfl; exact hd₁.1 h1γ
  obtain ⟨m₀, hm₀⟩ := planes_meet_in_line (L := L) hγα (h1γ O hO₁) hOα
  have hm₀α : LiesInPlane (Point := P) m₀ α := fun X hX => ((hm₀ X).1 hX).2
  obtain ⟨O', u, hu, hmu⟩ := he m₀ hm₀α
  have hOm : e ⟨O, hOα⟩ ∈ PLine K O' u := (hmu ⟨O, hOα⟩).1 ((hm₀ O).2 ⟨h1γ O hO₁, hOα⟩)
  refine ⟨u, hu, fun X => ?_, fun Z γ hγ1 hγ2 => ?_⟩
  · rcases proj_pair hd₁ hd₂ hO₁ hO₂ h12 h1γ h2γ hm₀ X with heq | ⟨m, hmα, hp1, hp2, hmm⟩
    · refine ⟨0, ?_⟩
      rw [zero_smul, add_zero]
      unfold qmap
      exact congrArg e (Subtype.ext heq.symm)
    · obtain ⟨O'', v, hv, hmv⟩ := he m hmα
      obtain ⟨c, hc⟩ := pline_sub ((hmv ⟨_, proj_mem hd₁ X⟩).1 hp1)
        ((hmv ⟨_, proj_mem hd₂ X⟩).1 hp2)
      have hc' : qmap e hd₂ X - qmap e hd₁ X = c • v := hc
      have hvu : ∃ c' : K, v = c' • u := by
        rcases hmm with hmm | hmm
        · subst hmm
          refine pline_dir_of_subset (O := O') (O' := O'') fun x hx => ?_
          have := (hmu (e.symm x)).1 ((hmv (e.symm x)).2 (by rwa [e.apply_symm_apply]))
          rwa [e.apply_symm_apply] at this
        · refine pline_dir_of_disjoint (O := O') (O' := O'') hV hu fun x hx hx' =>
            hmm ⟨((e.symm x : {A : P // A ∈ α}) : P), ?_, ?_⟩
          · exact (hmv (e.symm x)).2 (by rwa [e.apply_symm_apply])
          · exact (hmu (e.symm x)).2 (by rwa [e.apply_symm_apply])
      obtain ⟨c', rfl⟩ := hvu
      exact ⟨c * c', by rw [mul_smul]; exact eq_add_of_sub_eq' hc'⟩
  · have : γ = γ₀ := huniq γ ⟨hγ1, hγ2⟩
    subst this
    rw [pline_rebase hOm, ← hmu Z, hm₀]
    exact ⟨fun h => ⟨h, Z.2⟩, fun h => h.1⟩

/-- The traces of the planes `d_c d_a` and `d_c d_b` of three lines through `O` that are not in
one plane have independent directions. -/
theorem trace_indep {dc da db : L} (hdc : Cuts (P := P) dc α) {O : P} (hOα : O ∈ α)
    (hOc : O ∈ dc) (hOa : O ∈ da) (hOb : O ∈ db) (hca : dc ≠ da) (hcb : dc ≠ db) {ua ub : V}
    (hub : ub ≠ 0)
    (hta : ∀ (Z : {A : P // A ∈ α}) (γ : Pl), LiesInPlane (Point := P) dc γ →
      LiesInPlane (Point := P) da γ → ((Z : P) ∈ γ ↔ e Z ∈ PLine K (e ⟨O, hOα⟩) ua))
    (htb : ∀ (Z : {A : P // A ∈ α}) (γ : Pl), LiesInPlane (Point := P) dc γ →
      LiesInPlane (Point := P) db γ → ((Z : P) ∈ γ ↔ e Z ∈ PLine K (e ⟨O, hOα⟩) ub))
    (hnc : ¬∃ γ : Pl, LiesInPlane (Point := P) dc γ ∧ LiesInPlane (Point := P) da γ ∧
      LiesInPlane (Point := P) db γ) : ∀ c : K, ub ≠ c • ua := by
  intro c hc
  obtain ⟨γa, ⟨hca1, hca2⟩, -⟩ := theorem2_two_lines (Pl := Pl) hca hOc hOa
  obtain ⟨γb, ⟨hcb1, hcb2⟩, -⟩ := theorem2_two_lines (Pl := Pl) hcb hOc hOb
  set Z : {A : P // A ∈ α} := e.symm (ub + e ⟨O, hOα⟩) with hZ
  have heZ : e Z = ub + e ⟨O, hOα⟩ := e.apply_symm_apply _
  have hZb : (Z : P) ∈ γb := (htb Z γb hcb1 hcb2).2 ⟨1, by rw [heZ, one_smul]⟩
  have hZa : (Z : P) ∈ γa := (hta Z γa hca1 hca2).2 ⟨c, by rw [heZ, hc]⟩
  have hZdc : (Z : P) ∉ dc := by
    intro h
    have : (Z : P) = O := theorem1_line_plane hdc.1 h Z.2 hOc hOα
    have hZO : Z = ⟨O, hOα⟩ := Subtype.ext this
    rw [hZO] at heZ
    exact hub (by simpa using heZ.symm)
  have : γa = γb := plane_eq_of_line_point hZdc hca1 hZa hcb1 hZb
  subst this
  exact hnc ⟨γa, hca1, hca2, hcb2⟩

end Geo

/-! ## The image of a line -/

section Img

variable {P : Type u} {L : Type v} [HasLines P L] [hC : Connection P L]
variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]

variable (K) in
/-- The map `F` sends the line `ℓ` onto a line `{r D + T₀}` of `V × K`. -/
def IsImg (ℓ : L) (F : P → V × K) : Prop :=
  ∃ T₀ D : V × K, D ≠ 0 ∧ (∀ X : P, X ∈ ℓ → ∃ r : K, F X = r • D + T₀) ∧
    ∀ r : K, ∃ X : P, X ∈ ℓ ∧ F X = r • D + T₀

include hC

/-- If `q` is constant on `ℓ` and `q' = q + h u` is one-to-one onto a line, the height `h` takes
every value on `ℓ`. -/
theorem height_surj_of_const {q q' : P → V} {h : P → K} {u : V} (hu : u ≠ 0)
    (hh : ∀ X, q' X = q X + h X • u) {ℓ : L}
    (hc : ∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → q X = q X') (hq' : QInj K q' ℓ) (r : K) :
    ∃ X : P, X ∈ ℓ ∧ h X = r := by
  obtain ⟨O', v, hv, hin, hsurj, hinj⟩ := hq'
  obtain ⟨X₁, X₂, h12, hX₁, hX₂⟩ := exists_two_points (Point := P) ℓ
  have hne : h X₁ ≠ h X₂ := fun e =>
    h12 (hinj X₁ X₂ hX₁ hX₂ (by rw [hh, hh, e, hc X₁ X₂ hX₁ hX₂]))
  obtain ⟨c, hc'⟩ := pline_sub (hin X₁ hX₁) (hin X₂ hX₂)
  have hu' : u = ((h X₂ - h X₁)⁻¹ * c) • v := by
    have : (h X₂ - h X₁) • u = c • v := by
      rw [← hc', hh X₂, hh X₁, hc X₂ X₁ hX₂ hX₁, sub_smul]; abel
    rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne.symm), one_smul]
  have hmem : (r - h X₁) • u + q' X₁ ∈ PLine K O' v := by
    rw [hu', smul_smul]
    exact pline_add (hin X₁ hX₁) _
  obtain ⟨X, hX, hqX⟩ := hsurj _ hmem
  refine ⟨X, hX, ?_⟩
  have e1 := hh X
  rw [hqX, hh X₁, hc X X₁ hX hX₁] at e1
  have e2 : r • u = h X • u := by
    have : r • u + q X₁ = h X • u + q X₁ := by
      rw [add_comm (h X • u), ← e1, sub_smul]; abel
    exact add_right_cancel this
  have e3 : (h X - r) • u = 0 := by rw [sub_smul, e2, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 e3).resolve_right hu)

omit hC in
/-- **The parallel projection between two lines of a plane is affine**: if `q` runs on the line
`{r v₁ + O₁}`, `q' = q + h u` runs on a line `{s v₂ + O₂}` whose direction is independent of `u`,
then the height `h` is an affine function of the parameter `r`. -/
theorem height_affine (hV : finrank K V = 2) {q q' : P → V} {h : P → K} {u : V} (hu : u ≠ 0)
    (hh : ∀ X, q' X = q X + h X • u) {ℓ : L} {O₁ v₁ O₂ v₂ : V}
    (hin₂ : ∀ X : P, X ∈ ℓ → q' X ∈ PLine K O₂ v₂) (hv₂ : ∀ c : K, v₂ ≠ c • u) :
    ∃ c₀ c₁ : K, ∀ X : P, X ∈ ℓ → ∀ r : K, q X = r • v₁ + O₁ → h X = c₀ + r * c₁ := by
  obtain ⟨a', a, ha⟩ := exists_comb hV hu hv₂ v₁
  obtain ⟨b', b, hb⟩ := exists_comb hV hu hv₂ (O₁ - O₂)
  refine ⟨-b', -a', fun X hX r hr => ?_⟩
  obtain ⟨s, hs⟩ := hin₂ X hX
  have key : (r * a' + b' + h X) • u + (r * a + b - s) • v₂ = 0 := by
    have e1 := hh X
    have hO : O₁ = b' • u + b • v₂ + O₂ := by rw [← hb, sub_add_cancel]
    rw [hs, hr, hO, ha] at e1
    simp only [add_smul, sub_smul, mul_smul, smul_add] at e1 ⊢
    rw [← sub_eq_zero] at e1
    refine neg_eq_zero.1 (Eq.trans ?_ e1)
    abel
  obtain ⟨h0, -⟩ := indep_zero hu hv₂ key
  rw [mul_neg, ← neg_add, add_comm]
  exact eq_neg_of_add_eq_zero_right h0

theorem isImg_of_const {q q' : P → V} {h : P → K} {u : V} (hu : u ≠ 0)
    (hh : ∀ X, q' X = q X + h X • u) {ℓ : L}
    (hc : ∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → q X = q X') (hq' : QInj K q' ℓ) :
    IsImg K ℓ (fun X => (q X, h X)) := by
  obtain ⟨X₀, -, -, hX₀, -⟩ := exists_two_points (Point := P) ℓ
  refine ⟨(q X₀, 0), (0, 1), by simp, fun X hX => ⟨h X, ?_⟩, fun r => ?_⟩
  · simp [hc X X₀ hX hX₀]
  · obtain ⟨X, hX, hr⟩ := height_surj_of_const hu hh hc hq' r
    exact ⟨X, hX, by simp [hc X X₀ hX hX₀, hr]⟩

theorem isImg_of_const' {q q' : P → V} {h : P → K} {u : V} (hu : u ≠ 0)
    (hh : ∀ X, q' X = q X + h X • u) {ℓ : L}
    (hc' : ∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → q' X = q' X') (hq : QInj K q ℓ) :
    IsImg K ℓ (fun X => (q X, h X)) := by
  have hh' : ∀ X, q X = q' X + h X • (-u) := fun X => by rw [hh X, smul_neg]; abel
  obtain ⟨X₀, -, -, hX₀, -⟩ := exists_two_points (Point := P) ℓ
  refine ⟨(q' X₀, 0), (-u, 1), by simp, fun X hX => ⟨h X, ?_⟩, fun r => ?_⟩
  · simp [hh' X, hc' X X₀ hX hX₀, add_comm]
  · obtain ⟨X, hX, hr⟩ := height_surj_of_const (neg_ne_zero.2 hu) hh' hc' hq r
    exact ⟨X, hX, by simp [hh' X, hc' X X₀ hX hX₀, hr, add_comm]⟩

omit hC in
theorem isImg_of_indep (hV : finrank K V = 2) {q q' : P → V} {h : P → K} {u : V} (hu : u ≠ 0)
    (hh : ∀ X, q' X = q X + h X • u) {ℓ : L} (hq : QInj K q ℓ) {O₂ v₂ : V}
    (hin₂ : ∀ X : P, X ∈ ℓ → q' X ∈ PLine K O₂ v₂) (hv₂ : ∀ c : K, v₂ ≠ c • u) :
    IsImg K ℓ (fun X => (q X, h X)) := by
  obtain ⟨O₁, v₁, hv₁, hin, hsurj, -⟩ := hq
  obtain ⟨c₀, c₁, hc⟩ := height_affine hV hu hh hin₂ hv₂ (O₁ := O₁) (v₁ := v₁)
  refine ⟨(O₁, c₀), (v₁, c₁), fun h0 => hv₁ (congrArg Prod.fst h0), fun X hX => ?_, fun r => ?_⟩
  · obtain ⟨r, hr⟩ := hin X hX
    exact ⟨r, Prod.ext (by simpa using hr) (by simp [hc X hX r hr, add_comm])⟩
  · obtain ⟨X, hX, hqX⟩ := hsurj _ ⟨r, rfl⟩
    exact ⟨X, hX, Prod.ext (by simpa using hqX) (by simp [hc X hX r hqX, add_comm])⟩

omit hC in
theorem isImg_mul {q : P → V} {ha hb : P → K} {c : K} (hc : c ≠ 0)
    (h' : ∀ X, hb X = ha X * c) {ℓ : L} (h : IsImg K ℓ (fun X => (q X, ha X))) :
    IsImg K ℓ (fun X => (q X, hb X)) := by
  obtain ⟨T₀, D, hD, h1, h2⟩ := h
  refine ⟨(T₀.1, T₀.2 * c), (D.1, D.2 * c), fun h0 => hD (Prod.ext
    (show D.1 = 0 from congrArg Prod.fst h0)
    (show D.2 = 0 from (mul_eq_zero.1 (congrArg Prod.snd h0)).resolve_right hc)),
    fun X hX => ?_, fun r => ?_⟩
  · obtain ⟨r, hr⟩ := h1 X hX
    refine ⟨r, Prod.ext ?_ ?_⟩
    · simpa using congrArg Prod.fst hr
    · have := congrArg Prod.snd hr
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this ⊢
      rw [h', this, add_mul, mul_assoc]
  · obtain ⟨X, hX, hr⟩ := h2 r
    refine ⟨X, hX, Prod.ext ?_ ?_⟩
    · simpa using congrArg Prod.fst hr
    · have := congrArg Prod.snd hr
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this ⊢
      rw [h', this, add_mul, mul_assoc]

/-- **Every line of space is mapped onto a line of `V × K`** by `X ↦ (q₁ X, h₁₂ X)`. -/
theorem isImg_main (hV : finrank K V = 2) {q₁ q₂ q₃ : P → V} {h₁₂ h₁₃ h₂₃ : P → K}
    {u₁₂ u₁₃ u₂₃ : V} (hu₁₂ : u₁₂ ≠ 0) (hu₁₃ : u₁₃ ≠ 0)
    (hh₁₂ : ∀ X, q₂ X = q₁ X + h₁₂ X • u₁₂) (hh₁₃ : ∀ X, q₃ X = q₁ X + h₁₃ X • u₁₃)
    (hh₂₃ : ∀ X, q₃ X = q₂ X + h₂₃ X • u₂₃)
    (i1 : ∀ c : K, u₁₃ ≠ c • u₁₂) (i2 : ∀ c : K, u₂₃ ≠ c • u₁₃) (i3 : ∀ c : K, u₂₃ ≠ c • u₁₂)
    (hq₁ : ∀ ℓ : L, (∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → q₁ X = q₁ X') ∨ QInj K q₁ ℓ)
    (hq₂ : ∀ ℓ : L, (∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → q₂ X = q₂ X') ∨ QInj K q₂ ℓ)
    (hq₃ : ∀ ℓ : L, (∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → q₃ X = q₃ X') ∨ QInj K q₃ ℓ)
    (hinj : ∀ X Y : P, q₁ X = q₁ Y → q₂ X = q₂ Y → X = Y) (ℓ : L) :
    IsImg K ℓ (fun X => (q₁ X, h₁₂ X)) := by
  obtain ⟨a, b, hab⟩ := exists_comb hV hu₁₂ i1 u₂₃
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hab
    exact i2 b hab
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hab
    exact i3 a hab
  have hcne : -(a⁻¹ * b) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (inv_ne_zero ha) hb)
  have htr : ∀ X, h₁₃ X = h₁₂ X * (-(a⁻¹ * b)) := by
    intro X
    have key : (h₁₂ X + h₂₃ X * a) • u₁₂ + (h₂₃ X * b - h₁₃ X) • u₁₃ = 0 := by
      have e1 := hh₂₃ X
      rw [hh₁₃ X, hh₁₂ X, hab] at e1
      simp only [add_smul, sub_smul, mul_smul, smul_add] at e1 ⊢
      rw [← sub_eq_zero] at e1
      refine neg_eq_zero.1 (Eq.trans ?_ e1)
      abel
    obtain ⟨k1, k2⟩ := indep_zero hu₁₂ i1 key
    have e23 : h₂₃ X = -(h₁₂ X * a⁻¹) := by
      have : h₂₃ X * a = -h₁₂ X := eq_neg_of_add_eq_zero_right k1
      rw [← mul_inv_cancel_right₀ ha (h₂₃ X), this, neg_mul]
    rw [← sub_eq_zero.1 k2, e23, neg_mul, mul_neg, mul_assoc]
  obtain ⟨Y₁, Y₂, hY, hY₁, hY₂⟩ := exists_two_points (Point := P) ℓ
  rcases hq₁ ℓ with c1 | j1
  · rcases hq₂ ℓ with c2 | j2
    · exact absurd (hinj Y₁ Y₂ (c1 _ _ hY₁ hY₂) (c2 _ _ hY₁ hY₂)) hY
    · exact isImg_of_const hu₁₂ hh₁₂ c1 j2
  · rcases hq₂ ℓ with c2 | j2
    · exact isImg_of_const' hu₁₂ hh₁₂ c2 j1
    · obtain ⟨O₂, v₂, hv₂, hin₂, -, -⟩ := j2
      by_cases hv : ∃ c : K, v₂ = c • u₁₂
      · have h13 : IsImg K ℓ (fun X => (q₁ X, h₁₃ X)) := by
          rcases hq₃ ℓ with c3 | j3
          · exact isImg_of_const' hu₁₃ hh₁₃ c3 j1
          · obtain ⟨O₃, v₃, hv₃, hin₃, -, -⟩ := j3
            refine isImg_of_indep hV hu₁₃ hh₁₃ j1 hin₃ fun c₃ hc₃ => ?_
            obtain ⟨c₂, hc₂⟩ := hv
            obtain ⟨s₂, hs₂⟩ := pline_sub (hin₂ Y₁ hY₁) (hin₂ Y₂ hY₂)
            obtain ⟨s₃, hs₃⟩ := pline_sub (hin₃ Y₁ hY₁) (hin₃ Y₂ hY₂)
            have e2 : q₁ Y₂ - q₁ Y₁ = (s₂ * c₂ - h₁₂ Y₂ + h₁₂ Y₁) • u₁₂ := by
              rw [hh₁₂ Y₂, hh₁₂ Y₁, hc₂] at hs₂
              simp only [add_smul, sub_smul, mul_smul]
              rw [← hs₂]
              abel
            have e3 : q₁ Y₂ - q₁ Y₁ = (s₃ * c₃ - h₁₃ Y₂ + h₁₃ Y₁) • u₁₃ := by
              rw [hh₁₃ Y₂, hh₁₃ Y₁, hc₃] at hs₃
              simp only [add_smul, sub_smul, mul_smul]
              rw [← hs₃]
              abel
            obtain ⟨-, -, -, -, -, inj1⟩ := j1
            have hne : q₁ Y₂ - q₁ Y₁ ≠ 0 :=
              sub_ne_zero.2 fun e => hY (inj1 Y₂ Y₁ hY₂ hY₁ e).symm
            have ht : s₃ * c₃ - h₁₃ Y₂ + h₁₃ Y₁ ≠ 0 := by
              intro h0
              rw [h0, zero_smul] at e3
              exact hne e3
            refine i1 ((s₃ * c₃ - h₁₃ Y₂ + h₁₃ Y₁)⁻¹ * (s₂ * c₂ - h₁₂ Y₂ + h₁₂ Y₁)) ?_
            rw [mul_smul, ← e2, e3, smul_smul, inv_mul_cancel₀ ht, one_smul]
        refine isImg_mul (c := (-(a⁻¹ * b))⁻¹) (inv_ne_zero hcne) (fun X => ?_) h13
        rw [htr X, mul_inv_cancel_right₀ hcne]
      · rw [not_exists] at hv
        exact isImg_of_indep hV hu₁₂ hh₁₂ j1 hin₂ hv

end Img

/-! ## The co-ordinates of space -/

section Main

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [hO : SpaceOrder P L Pl] [hS : SpaceParallels P L Pl]
variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsStrictOrderedRing K] {V : Type*}
  [AddCommGroup V] [Module K V]

include hO hS

/-- **First step**: a bijection of space with `V × K` extending the co-ordinates of `α`, mapping
every line onto a line, and compatible with betweenness on every line if the co-ordinates of `α`
are. -/
theorem exists_coords_lines (hV : finrank K V = 2) (α : Pl) (e : {A : P // A ∈ α} ≃ V)
    (he : LineHyp K e) :
    ∃ f₀ : P → V × K, Function.Bijective f₀ ∧
      (∀ Z : {A : P // A ∈ α}, f₀ Z = (e Z, 0)) ∧ (∀ ℓ : L, IsImg K ℓ f₀) ∧
      ((∀ X Y Z : {A : P // A ∈ α}, Sbtw K (e X) (e Y) (e Z) ↔ Between (X : P) Y Z) →
        ∀ (ℓ : L) (X Y Z : P), X ∈ ℓ → Y ∈ ℓ → Z ∈ ℓ →
          (Sbtw K (f₀ X) (f₀ Y) (f₀ Z) ↔ Between X Y Z)) := by
  obtain ⟨O, d₁, d₂, d₃, hOα, hO₁, hO₂, hO₃, hn₁, hn₂, hn₃, hnc⟩ :=
    exists_three_directions (P := P) (L := L) α
  have hd₁ : Cuts (P := P) d₁ α := ⟨hn₁, O, hO₁, hOα⟩
  have hd₂ : Cuts (P := P) d₂ α := ⟨hn₂, O, hO₂, hOα⟩
  have hd₃ : Cuts (P := P) d₃ α := ⟨hn₃, O, hO₃, hOα⟩
  have hpl : ∀ a b : L, O ∈ a → O ∈ b →
      ∃ γ : Pl, LiesInPlane (Point := P) a γ ∧ LiesInPlane (Point := P) b γ := by
    intro a b ha hb
    by_cases hab : a = b
    · subst hab
      obtain ⟨Q, -, hQ⟩ := exists_mem_plane_not_mem (P := P) α a
      obtain ⟨γ, hγ, -⟩ := exists_plane_line_point (Pl := Pl) hQ
      exact ⟨γ, hγ, hγ⟩
    · obtain ⟨γ, hγ, -⟩ := theorem2_two_lines (Pl := Pl) hab ha hb
      exact ⟨γ, hγ⟩
  have h12 : d₁ ≠ d₂ := by
    rintro rfl
    obtain ⟨γ, h1, h3⟩ := hpl d₁ d₃ hO₁ hO₃
    exact hnc ⟨γ, h1, h1, h3⟩
  have h13 : d₁ ≠ d₃ := by
    rintro rfl
    obtain ⟨γ, h1, h2⟩ := hpl d₁ d₂ hO₁ hO₂
    exact hnc ⟨γ, h1, h2, h1⟩
  have h23 : d₂ ≠ d₃ := by
    rintro rfl
    obtain ⟨γ, h1, h2⟩ := hpl d₁ d₂ hO₁ hO₂
    exact hnc ⟨γ, h1, h2, h2⟩
  obtain ⟨u₁₂, hu₁₂, hr₁₂, ht₁₂⟩ := exists_trace e hV he hd₁ hd₂ hOα hO₁ hO₂ h12
  obtain ⟨u₁₃, hu₁₃, hr₁₃, ht₁₃⟩ := exists_trace e hV he hd₁ hd₃ hOα hO₁ hO₃ h13
  obtain ⟨u₂₃, hu₂₃, hr₂₃, ht₂₃⟩ := exists_trace e hV he hd₂ hd₃ hOα hO₂ hO₃ h23
  choose h₁₂ hh₁₂ using hr₁₂
  choose h₁₃ hh₁₃ using hr₁₃
  choose h₂₃ hh₂₃ using hr₂₃
  have i1 : ∀ c : K, u₁₃ ≠ c • u₁₂ :=
    trace_indep e hd₁ hOα hO₁ hO₂ hO₃ h12 h13 hu₁₃ ht₁₂ ht₁₃ hnc
  have i2 : ∀ c : K, u₂₃ ≠ c • u₁₃ :=
    trace_indep e hd₃ hOα hO₃ hO₁ hO₂ h13.symm h23.symm hu₂₃ (fun Z γ hc ha => ht₁₃ Z γ ha hc)
      (fun Z γ hc hb => ht₂₃ Z γ hb hc) (fun ⟨γ, h3, h1, h2⟩ => hnc ⟨γ, h1, h2, h3⟩)
  have i3 : ∀ c : K, u₂₃ ≠ c • u₁₂ :=
    trace_indep e hd₂ hOα hO₂ hO₁ hO₃ h12.symm h23 hu₂₃ (fun Z γ hc ha => ht₁₂ Z γ ha hc)
      ht₂₃ (fun ⟨γ, h2, h1, h3⟩ => hnc ⟨γ, h1, h2, h3⟩)
  have hq : ∀ {d : L} (hd : Cuts (P := P) d α) (ℓ : L),
      (∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → qmap e hd X = qmap e hd X') ∨ QInj K (qmap e hd) ℓ := by
    intro d hd ℓ
    by_cases hp : Par (P := P) (Pl := Pl) d ℓ
    · exact Or.inl fun X X' hX hX' => qmap_const e hd hp hX hX'
    · exact Or.inr (qmap_line e he hd hp)
  have hinj12 : ∀ X Y : P, qmap e hd₁ X = qmap e hd₁ Y → qmap e hd₂ X = qmap e hd₂ Y → X = Y :=
    fun X Y h1 h2 => qmap_inj_pair e hd₁ hd₂ hO₁ hO₂ h12 h1 h2
  have himg := isImg_main hV hu₁₂ hu₁₃ hh₁₂ hh₁₃ hh₂₃ i1 i2 i3 (hq hd₁) (hq hd₂) (hq hd₃) hinj12
  have hnp : ¬Par (P := P) (Pl := Pl) d₁ d₂ := fun h => h12 (par_eq_of_meets h hO₁ hO₂)
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : P → V × K, ∀ X, f₀ X = (qmap e hd₁ X, h₁₂ X) := ⟨_, fun _ => rfl⟩
  have himg' : ∀ ℓ : L, IsImg K ℓ f₀ := by
    have : f₀ = fun X => (qmap e hd₁ X, h₁₂ X) := funext hf₀
    rw [this]
    exact himg
  refine ⟨f₀, ⟨?_, ?_⟩, ?_, himg', ?_⟩
  · intro X Y hXY
    rw [hf₀, hf₀] at hXY
    have e1 : qmap e hd₁ X = qmap e hd₁ Y := congrArg Prod.fst hXY
    have e2 : h₁₂ X = h₁₂ Y := congrArg Prod.snd hXY
    exact hinj12 X Y e1 (by rw [hh₁₂, hh₁₂, e1, e2])
  · rintro ⟨v, t⟩
    obtain ⟨b, hb, hZb⟩ := exists_par (Pl := Pl) d₁ ((e.symm v : {A : P // A ∈ α}) : P)
    have hb2 : ¬Par (P := P) (Pl := Pl) d₂ b := fun h => hnp (par_trans hb (par_symm h))
    obtain ⟨X, hX, hr⟩ := height_surj_of_const hu₁₂ hh₁₂
      (fun X X' hX hX' => qmap_const e hd₁ hb hX hX') (qmap_line e he hd₂ hb2) t
    refine ⟨X, ?_⟩
    rw [hf₀]
    refine Prod.ext ?_ hr
    show qmap e hd₁ X = v
    rw [qmap_const e hd₁ hb hX hZb, qmap_of_mem e hd₁ (e.symm v).2]
    exact e.apply_symm_apply v
  · intro Z
    have h1 : qmap e hd₁ Z = e Z := qmap_of_mem e hd₁ Z.2
    have h2 : qmap e hd₂ Z = e Z := qmap_of_mem e hd₂ Z.2
    have h0 : h₁₂ Z = 0 := by
      have h3 := hh₁₂ Z
      rw [h1, h2] at h3
      have h4 : h₁₂ (Z : P) • u₁₂ = 0 := by simpa using h3.symm
      exact (smul_eq_zero.1 h4).resolve_right hu₁₂
    rw [hf₀]
    exact Prod.ext h1 h0
  · intro hbt ℓ X Y Z hX hY hZ
    obtain ⟨T₀, D, hD, hin, -⟩ := himg' ℓ
    obtain ⟨x, hx⟩ := hin X hX
    obtain ⟨y, hy⟩ := hin Y hY
    obtain ⟨z, hz⟩ := hin Z hZ
    have hord : Sbtw K (f₀ X) (f₀ Y) (f₀ Z) ↔ (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
      rw [hx, hy, hz]
      exact sbtw_param_iff (V := V × K) (O := T₀) (d := D) hD x y z
    have chain : ∀ {d : L} (hd : Cuts (P := P) d α), ¬Par (P := P) (Pl := Pl) d ℓ →
        ∀ D' T' : V, (∀ W : P, W ∈ ℓ → ∀ r : K, f₀ W = r • D + T₀ → qmap e hd W = r • D' + T') →
        (((x < y ∧ y < z) ∨ (z < y ∧ y < x)) ↔ Between X Y Z) := by
      intro d hd hp D' T' hpar
      have hD' : D' ≠ 0 := by
        rintro rfl
        obtain ⟨Y₁, Y₂, hY12, hY₁, hY₂⟩ := exists_two_points (Point := P) ℓ
        obtain ⟨r₁, hr₁⟩ := hin Y₁ hY₁
        obtain ⟨r₂, hr₂⟩ := hin Y₂ hY₂
        obtain ⟨-, -, -, -, -, inj⟩ := qmap_line e he hd hp
        exact hY12 (inj Y₁ Y₂ hY₁ hY₂
          (by rw [hpar Y₁ hY₁ r₁ hr₁, hpar Y₂ hY₂ r₂ hr₂, smul_zero, smul_zero]))
      have hs : Sbtw K (qmap e hd X) (qmap e hd Y) (qmap e hd Z) ↔
          (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
        rw [hpar X hX x hx, hpar Y hY y hy, hpar Z hZ z hz]
        exact sbtw_param_iff (V := V) (O := T') (d := D') hD' x y z
      exact hs.symm.trans ((hbt ⟨_, proj_mem hd X⟩ ⟨_, proj_mem hd Y⟩ ⟨_, proj_mem hd Z⟩).trans
        (proj_between hd hp hX hY hZ))
    rw [hord]
    by_cases hp1 : Par (P := P) (Pl := Pl) d₁ ℓ
    · have hp2 : ¬Par (P := P) (Pl := Pl) d₂ ℓ := fun h => hnp (par_trans hp1 (par_symm h))
      refine chain hd₂ hp2 (D.1 + D.2 • u₁₂) (T₀.1 + T₀.2 • u₁₂) fun W hW r hr => ?_
      rw [hf₀] at hr
      have e1 : qmap e hd₁ W = r • D.1 + T₀.1 := congrArg Prod.fst hr
      have e2 : h₁₂ W = r * D.2 + T₀.2 := congrArg Prod.snd hr
      rw [hh₁₂ W, e1, e2, smul_add, add_smul, mul_smul]
      abel
    · refine chain hd₁ hp1 D.1 T₀.1 fun W hW r hr => ?_
      rw [hf₀] at hr
      exact congrArg Prod.fst hr

/-- **Second step**: a bijection of space with `V × K` (`V` of dimension 2) that maps every line
onto a line identifies the lines and the planes of space with the lines and planes of the
coordinate space `AffPt K (V × K)`. -/
theorem coords_of_lines (hV : finrank K V = 2) (f₀ : P → V × K) (hbij : Function.Bijective f₀)
    (himg : ∀ ℓ : L, IsImg K ℓ f₀) :
    (∀ ℓ : L, ∃ m : AffLine K (V × K), ∀ X : P, X ∈ ℓ ↔ (f₀ X : AffPt K (V × K)) ∈ m) ∧
    (∀ m : AffLine K (V × K), ∃ ℓ : L, ∀ X : P, X ∈ ℓ ↔ (f₀ X : AffPt K (V × K)) ∈ m) ∧
    (∀ π : Pl, ∃ S : AffPlane K (V × K), ∀ X : P, X ∈ π ↔ (f₀ X : AffPt K (V × K)) ∈ S) ∧
    (∀ S : AffPlane K (V × K), ∃ π : Pl, ∀ X : P, X ∈ π ↔ (f₀ X : AffPt K (V × K)) ∈ S) := by
  have hfin : Module.Finite K V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
  have : Fact (finrank K (V × K) = 3) :=
    ⟨by rw [Module.finrank_prod, hV, Module.finrank_self]⟩
  have hl1 : ∀ ℓ : L, ∃ m : AffLine K (V × K), ∀ X : P,
      X ∈ ℓ ↔ (f₀ X : AffPt K (V × K)) ∈ m := by
    intro ℓ
    obtain ⟨T₀, D, hD, h1, h2⟩ := himg ℓ
    have hne : (T₀ : AffPt K (V × K)) ≠ (D + T₀ : V × K) := fun h =>
      hD (by simpa using h.symm)
    have key : ∀ r : K, r • ((D + T₀) - T₀) + T₀ = r • D + T₀ := fun r => by
      rw [add_sub_cancel_right]
    refine ⟨AffLine.through _ _ hne, fun X => ⟨fun hX => ?_, fun hX => ?_⟩⟩
    · obtain ⟨r, hr⟩ := h1 X hX
      exact (AffLine.mem_through_iff hne).2 ⟨r, hr.trans (key r).symm⟩
    · obtain ⟨r, hr⟩ := (AffLine.mem_through_iff hne).1 hX
      obtain ⟨X', hX', hr'⟩ := h2 r
      have : X = X' := hbij.1 ((hr.trans (key r)).trans hr'.symm)
      subst this
      exact hX'
  have hl2 : ∀ m : AffLine K (V × K), ∃ ℓ : L, ∀ X : P,
      X ∈ ℓ ↔ (f₀ X : AffPt K (V × K)) ∈ m := by
    intro m
    obtain ⟨Y₁, Y₂, hY, h1, h2⟩ := exists_two_points (Point := AffPt K (V × K)) m
    obtain ⟨X₁, rfl⟩ := hbij.2 Y₁
    obtain ⟨X₂, rfl⟩ := hbij.2 Y₂
    have hX : X₁ ≠ X₂ := fun h => hY (by rw [h])
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_line (Line := L) hX
    obtain ⟨m', hm'⟩ := hl1 ℓ
    have : m' = m := line_unique hY ((hm' X₁).1 hℓ1) ((hm' X₂).1 hℓ2) h1 h2
    exact ⟨ℓ, fun X => by rw [← this]; exact hm' X⟩
  have hp1 : ∀ π : Pl, ∃ S : AffPlane K (V × K), ∀ X : P,
      X ∈ π ↔ (f₀ X : AffPt K (V × K)) ∈ S := by
    intro π
    obtain ⟨A, B, C, a, hA, hB, hC, hAB, hAa, hBa, hCa⟩ :=
      exists_triangle_in_plane (P := P) (L := L) π
    obtain ⟨a', ha'⟩ := hl1 a
    have hn : ¬Collinear (Point := AffPt K (V × K)) (f₀ A) (f₀ B) (f₀ C) :=
      not_collinear_of_not_mem ((ha' A).1 hAa) ((ha' B).1 hBa) (hbij.1.ne hAB)
        (fun h => hCa ((ha' C).2 h))
    obtain ⟨S, hSA, hSB, hSC⟩ := exists_plane (Plane := AffPlane K (V × K)) hn
    refine ⟨S, fun X => ⟨fun hX => ?_, fun hX => ?_⟩⟩
    · exact plane_transfer (P' := AffPt K (V × K)) f₀ hbij.1
        (fun ℓ => by obtain ⟨m, hm⟩ := hl1 ℓ; exact ⟨m, fun X hX => (hm X).1 hX⟩)
        hA hB hC hAB hAa hBa hCa hSA hSB hSC X hX
    · let g : AffPt K (V × K) → P := (Equiv.ofBijective f₀ hbij).symm
      have hgf : ∀ X, g (f₀ X) = X := (Equiv.ofBijective f₀ hbij).symm_apply_apply
      have hfg : ∀ Y, f₀ (g Y) = Y := (Equiv.ofBijective f₀ hbij).apply_symm_apply
      have hgi : Function.Injective g := (Equiv.ofBijective f₀ hbij).symm.injective
      have := plane_transfer (P := AffPt K (V × K)) (P' := P) g hgi
        (fun m => by
          obtain ⟨ℓ, hℓ⟩ := hl2 m
          exact ⟨ℓ, fun Y hY => (hℓ (g Y)).2 (by rw [hfg]; exact hY)⟩)
        (π := S) (S := π) (A := f₀ A) (B := f₀ B) (C := f₀ C) (a := a') hSA hSB hSC
        (hbij.1.ne hAB) ((ha' A).1 hAa) ((ha' B).1 hBa) (fun h => hCa ((ha' C).2 h))
        (by rw [hgf]; exact hA) (by rw [hgf]; exact hB) (by rw [hgf]; exact hC) (f₀ X) hX
      rwa [hgf] at this
  refine ⟨hl1, hl2, hp1, fun S => ?_⟩
  obtain ⟨A', B', C', a', hA, hB, hC, hAB, hAa, hBa, hCa⟩ :=
    exists_triangle_in_plane (P := AffPt K (V × K)) (L := AffLine K (V × K)) S
  obtain ⟨A, rfl⟩ := hbij.2 A'
  obtain ⟨B, rfl⟩ := hbij.2 B'
  obtain ⟨C, rfl⟩ := hbij.2 C'
  obtain ⟨a, ha⟩ := hl2 a'
  have hAB' : A ≠ B := fun h => hAB (by rw [h])
  have hn : ¬Collinear A B C :=
    not_collinear_of_not_mem ((ha A).2 hAa) ((ha B).2 hBa) hAB' (fun h => hCa ((ha C).1 h))
  obtain ⟨π, hπA, hπB, hπC⟩ := exists_plane (Plane := Pl) hn
  obtain ⟨S', hS'⟩ := hp1 π
  have hn' : ¬Collinear (Point := AffPt K (V × K)) (f₀ A) (f₀ B) (f₀ C) :=
    not_collinear_of_not_mem hAa hBa hAB hCa
  have : S' = S := plane_unique hn' ((hS' A).1 hπA) ((hS' B).1 hπB) ((hS' C).1 hπC) hA hB hC
  exact ⟨π, fun X => by rw [← this]; exact hS' X⟩

/-- **The co-ordinates of space from the co-ordinates of a plane.** Let `α` be a plane of a
geometry of space with I, II, III, and `e` a bijection of its points with a vector space `V` of
dimension 2 over an ordered skew field `K` under which the lines of `α` are the lines of `V`. Then
`e` extends to a bijection `f` of space with `V × K` under which the lines and the planes of space
are exactly the lines and planes of the coordinate space `AffPt K (V × K)`; if `e` is compatible
with betweenness, so is `f`. -/
theorem exists_space_coords (hV : finrank K V = 2) (α : Pl) (e : {A : P // A ∈ α} ≃ V)
    (he : LineHyp K e) :
    ∃ f : P ≃ AffPt K (V × K),
      (∀ Z : {A : P // A ∈ α}, f Z = ((e Z, (0 : K)) : V × K)) ∧
      (∀ ℓ : L, ∃ m : AffLine K (V × K), ∀ X : P, X ∈ ℓ ↔ f X ∈ m) ∧
      (∀ m : AffLine K (V × K), ∃ ℓ : L, ∀ X : P, X ∈ ℓ ↔ f X ∈ m) ∧
      (∀ π : Pl, ∃ S : AffPlane K (V × K), ∀ X : P, X ∈ π ↔ f X ∈ S) ∧
      (∀ S : AffPlane K (V × K), ∃ π : Pl, ∀ X : P, X ∈ π ↔ f X ∈ S) ∧
      ((∀ X Y Z : {A : P // A ∈ α}, Sbtw K (e X) (e Y) (e Z) ↔ Between (X : P) Y Z) →
        ∀ X Y Z : P, Between (f X) (f Y) (f Z) ↔ Between X Y Z) := by
  obtain ⟨f₀, hbij, hα, himg, hbt⟩ := exists_coords_lines hV α e he
  obtain ⟨hl1, hl2, hp1, hp2⟩ := coords_of_lines hV f₀ hbij himg
  refine ⟨(Equiv.ofBijective f₀ hbij : P ≃ V × K), hα, hl1, hl2, hp1, hp2, fun h X Y Z => ?_⟩
  have hline := hbt h
  constructor
  · intro hb
    have hb' : Sbtw K (f₀ X) (f₀ Y) (f₀ Z) := hb
    have hXZ : X ≠ Z := fun e => hb'.left_ne_right (by rw [e])
    obtain ⟨ℓ, hXℓ, hZℓ⟩ := exists_line (Line := L) hXZ
    obtain ⟨m, hm⟩ := hl1 ℓ
    have hY : Y ∈ ℓ := (hm Y).2
      (affineSpan_pair_le_of_mem_of_mem ((hm X).1 hXℓ) ((hm Z).1 hZℓ) hb.wbtw.mem_affineSpan)
    exact (hline ℓ X Y Z hXℓ hY hZℓ).1 hb'
  · intro hb
    obtain ⟨ℓ, hXℓ, hYℓ, hZℓ⟩ := collinear_of_between hb
    exact (hline ℓ X Y Z hXℓ hYℓ hZℓ).2 hb

end Main

end SpaceCoord

end HilbertFoundations
