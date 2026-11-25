import HilbertFoundations.Analytic

/-!
# The non-euclidean geometry of § 10 (helper module of `Independence.lean`)

Hilbert's model (§ 10): "the points, straight lines, and planes of the ordinary geometry …
restricted in extent to the interior of a fixed sphere", the congruences being defined "by aid of
such linear transformations of the ordinary geometry as transform the fixed sphere into itself"
(the projective model of Beltrami, Cayley and Klein).

Here, over `ℝ`:

* points `KPt n`: the points `p` of `ℝⁿ` with `|p|² < 1`; lines `KLine n`, planes `KPlane n`: the
  lines and planes of `ℝⁿ` (`CoordLine ℝ n`, `CoordPlane ℝ n`) having a point inside the ball;
  incidence and betweenness are those of `ℝⁿ`;
* congruence of segments: equality of the projective invariant
  `ch p q = (1 - ⟪p, q⟫) / (√(1 - |p|²) √(1 - |q|²))` (the hyperbolic cosine of the Cayley–Klein
  distance, a function of the cross-ratio of `p`, `q` and the two ends of the chord);
* congruence of angles: equality of `kcos A O B`, the cosine of the angle `∠AOB` for the
  Cayley–Klein metric at `O` (the quadratic form `G_O u v = (1 - |O|²) ⟪u, v⟫ + ⟪O, u⟫ ⟪O, v⟫`).

Both invariants are preserved by the projective transformations that map the sphere onto itself
(proved for the transformations of `Independence.lean`, unit `s10.non_euclidean`).

Results (for `n = 3`, Hilbert's geometry of space): groups I and II (`instSpaceConnection`,
`instSpaceOrder`), group IV (`instSpaceCongruence`), axiom V (`instArchimedes`), and the failure
of the axiom of parallels III (`not_axiomIIISpace`, `exists_two_parallels`). The motions (`IsMotion`:
composites of boosts and reflections) preserve both congruences, and congruence is congruence by
motions (`segCong_iff_motion`, `angCong_iff_motion`).
-/

namespace HilbertFoundations

open Module Coord AffPt

/-! ### Points `(x, y, z)` of `K³` -/

/-- The point `(x, y, z)` of `K³`. -/
def pt3 {K : Type*} (x y z : K) : Coord K 3 := AffPt.ofV ![x, y, z]

section Pt3

variable {K : Type*}

@[simp] theorem toV_pt3_0 (x y z : K) : AffPt.toV (pt3 x y z) 0 = x := rfl
@[simp] theorem toV_pt3_1 (x y z : K) : AffPt.toV (pt3 x y z) 1 = y := rfl
@[simp] theorem toV_pt3_2 (x y z : K) : AffPt.toV (pt3 x y z) 2 = z := rfl

theorem pt3_ext {X Y : Coord K 3} (h0 : AffPt.toV X 0 = AffPt.toV Y 0)
    (h1 : AffPt.toV X 1 = AffPt.toV Y 1) (h2 : AffPt.toV X 2 = AffPt.toV Y 2) : X = Y := by
  apply AffPt.toV_injective
  funext i; fin_cases i <;> assumption

theorem eq_pt3 (X : Coord K 3) : X = pt3 (AffPt.toV X 0) (AffPt.toV X 1) (AffPt.toV X 2) :=
  pt3_ext rfl rfl rfl

variable [Field K]

theorem pt3_sub (x y z x' y' z' : K) : pt3 x y z - pt3 x' y' z' = pt3 (x - x') (y - y') (z - z') :=
  pt3_ext (by simp) (by simp) (by simp)

theorem pt3_add (x y z x' y' z' : K) : pt3 x y z + pt3 x' y' z' = pt3 (x + x') (y + y') (z + z') :=
  pt3_ext (by simp) (by simp) (by simp)

theorem smul_pt3 (c x y z : K) : c • pt3 x y z = pt3 (c * x) (c * y) (c * z) :=
  pt3_ext (by simp) (by simp) (by simp)

theorem pt3_zero : (0 : Coord K 3) = pt3 0 0 0 := pt3_ext (by simp) (by simp) (by simp)

theorem ip_pt3 (x y z x' y' z' : K) : ip (pt3 x y z) (pt3 x' y' z') = x * x' + y * y' + z * z' := by
  rw [ip_def, Fin.sum_univ_three]; rfl

theorem ip_eq_coords (X Y : Coord K 3) : ip X Y = AffPt.toV X 0 * AffPt.toV Y 0 +
    AffPt.toV X 1 * AffPt.toV Y 1 + AffPt.toV X 2 * AffPt.toV Y 2 := by
  rw [ip_def, Fin.sum_univ_three]

/-- Linear independence of two vectors of `K³` in the plane `z = 0`. -/
theorem li_pt3 {a b c d : K} (h : a * d - b * c ≠ 0) :
    LinearIndependent K ![pt3 a b 0, pt3 c d 0] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun (congrArg AffPt.toV hst) 0
  have h1 := congrFun (congrArg AffPt.toV hst) 1
  simp only [AffPt.toV_add, AffPt.toV_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    AffPt.toV_zero, Pi.zero_apply, toV_pt3_0, toV_pt3_1] at h0 h1
  constructor
  · have : s * (a * d - b * c) = 0 := by linear_combination d * h0 - c * h1
    exact (mul_eq_zero.1 this).resolve_right h
  · have : t * (a * d - b * c) = 0 := by linear_combination a * h1 - b * h0
    exact (mul_eq_zero.1 this).resolve_right h

end Pt3

/-- Three points are not collinear if the two difference vectors are linearly independent. -/
theorem not_collinear_of_li {K : Type*} [DivisionRing K] {n : ℕ} {A B C : Coord K n}
    (h : LinearIndependent K ![B - A, C - A]) : ¬Collinear A B C := by
  have := AffPt.not_collinear_of_linearIndependent (O := A) h
  simpa only [sub_add_cancel] using this

/-- Conversely, the difference vectors of three non-collinear points are linearly independent. -/
theorem li_of_not_collinear {K : Type*} [Field K] {n : ℕ} [NeZero n] {A B C : Coord K n}
    (h : ¬Collinear A B C) : LinearIndependent K ![B - A, C - A] := by
  obtain ⟨hAB, -, -⟩ := AffPt.not_collinear_of_eq h
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    rcases smul_eq_zero.1 hst with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.1 h1).symm hAB
  · exfalso
    apply h
    have : C - A = (-s / t) • (B - A) := by
      have e : t • (C - A) = (-s) • (B - A) := by
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hst
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← e, smul_smul, inv_mul_cancel₀ ht, one_smul]
    exact (AffPt.collinear_of_smul (Ne.symm hAB) _ this).swap12

namespace Klein

/-! ### The ball -/

variable {n : ℕ}

/-- `p` lies inside the unit sphere. -/
def InBall (p : Coord ℝ n) : Prop := ip p p < 1

/-- The points of the non-euclidean geometry: the points inside the fixed sphere. -/
@[ext]
structure KPt (n : ℕ) where
  /-- The point of ordinary space. -/
  pt : Coord ℝ n
  inBall : InBall pt

/-- The straight lines: the lines of ordinary space having a point inside the sphere. -/
@[ext]
structure KLine (n : ℕ) where
  /-- The line of ordinary space. -/
  line : CoordLine ℝ n
  meets : ∃ p : Coord ℝ n, InBall p ∧ p ∈ line

/-- The planes: the planes of ordinary space having a point inside the sphere. -/
@[ext]
structure KPlane (n : ℕ) where
  /-- The plane of ordinary space. -/
  plane : CoordPlane ℝ n
  meets : ∃ p : Coord ℝ n, InBall p ∧ p ∈ plane

instance instHasLines : HasLines (KPt n) (KLine n) := ⟨fun A a => A.pt ∈ a.line⟩
instance instHasPlanes : HasPlanes (KPt n) (KPlane n) := ⟨fun A α => A.pt ∈ α.plane⟩
instance instHasBetween : HasBetween (KPt n) := ⟨fun A B C => Between A.pt B.pt C.pt⟩

theorem mem_line {A : KPt n} {a : KLine n} : A ∈ a ↔ A.pt ∈ a.line := Iff.rfl
theorem mem_plane {A : KPt n} {α : KPlane n} : A ∈ α ↔ A.pt ∈ α.plane := Iff.rfl
theorem between_iff {A B C : KPt n} : Between A B C ↔ Between A.pt B.pt C.pt := Iff.rfl

theorem pt_ne {A B : KPt n} (h : A ≠ B) : A.pt ≠ B.pt := fun e => h (KPt.ext e)

theorem ne_of_pt_ne {A B : KPt n} (h : A.pt ≠ B.pt) : A ≠ B := fun e => h (e ▸ rfl)

/-- The ball is convex. -/
theorem inBall_comb {a c : Coord ℝ n} (ha : InBall a) (hc : InBall c) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : InBall (t • (c - a) + a) := by
  unfold InBall at *
  have e : ip (t • (c - a) + a) (t • (c - a) + a) =
      (1 - t) * ip a a + t * ip c c - t * (1 - t) * ip (c - a) (c - a) := by
    simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, ip_sub_left, ip_sub_right]
    rw [ip_comm c a]; ring
  rw [e]
  have h3 := ip_self_nonneg (c - a)
  have h4 : 0 ≤ t * (1 - t) * ip (c - a) (c - a) :=
    mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) h3
  have h5 : (1 - t) * ip a a + t * ip c c < 1 := by
    rcases h0.eq_or_lt with ht | ht
    · subst ht; simpa using ha
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha.le), mul_pos ht (sub_pos.2 hc)]
  linarith

theorem inBall_between {a b c : Coord ℝ n} (ha : InBall a) (hc : InBall c) (h : Between a b c) :
    InBall b := by
  obtain ⟨-, t, h0, h1, rfl⟩ := sbtw_iff_param.1 h
  exact inBall_comb ha hc h0.le h1.le

/-- The ball is open (along every line). -/
theorem exists_inBall_add {p : Coord ℝ n} (hp : InBall p) (v : Coord ℝ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| ≤ ε → InBall (s • v + p) := by
  unfold InBall at *
  set δ := 1 - ip p p with hδ
  have hδ0 : 0 < δ := by linarith
  set M := 2 * |ip p v| + ip v v + 1 with hM
  have hv := ip_self_nonneg v
  have hM1 : 1 ≤ M := by have := abs_nonneg (ip p v); linarith
  refine ⟨δ / (2 * M), div_pos hδ0 (by linarith), fun s hs => ?_⟩
  have hδ1 : δ ≤ 1 := by have := ip_self_nonneg p; linarith
  have hε1 : δ / (2 * M) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hs1 : |s| ≤ 1 := hs.trans hε1
  have e : ip (s • v + p) (s • v + p) = s ^ 2 * ip v v + 2 * s * ip p v + ip p p := by
    simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right]; rw [ip_comm v p]; ring
  rw [e]
  have h2 : s ^ 2 ≤ |s| := by
    rw [← sq_abs]; nlinarith [abs_nonneg s]
  have h2' : s ^ 2 * ip v v ≤ |s| * ip v v := mul_le_mul_of_nonneg_right h2 hv
  have h3 : 2 * s * ip p v ≤ 2 * (|s| * |ip p v|) := by
    have h4 := le_abs_self (s * ip p v)
    rw [abs_mul] at h4; linarith
  have h5 : |s| * (2 * M) ≤ δ := by
    rw [le_div_iff₀ (by linarith)] at hs; linarith
  have h6 : |s| * ip v v + 2 * (|s| * |ip p v|) ≤ |s| * M := by
    rw [hM]; nlinarith [abs_nonneg s]
  have h7 : |s| * M ≤ δ / 2 := by linarith
  linarith

theorem exists_inBall_pos {p : Coord ℝ n} (hp : InBall p) (v : Coord ℝ n) :
    ∃ ε : ℝ, 0 < ε ∧ InBall (ε • v + p) := by
  obtain ⟨ε, hε, h⟩ := exists_inBall_add hp v
  exact ⟨ε, hε, h ε (by rw [abs_of_pos hε])⟩

/-! ### Incidence in the ball and in ordinary space -/

theorem collinear_iff {A B C : KPt n} : Collinear A B C ↔ Collinear A.pt B.pt C.pt := by
  constructor
  · rintro ⟨a, hA, hB, hC⟩; exact ⟨a.line, hA, hB, hC⟩
  · rintro ⟨l, hA, hB, hC⟩; exact ⟨⟨l, A.pt, A.inBall, hA⟩, hA, hB, hC⟩

theorem coplanar_iff {A B C D : KPt n} : Coplanar A B C D ↔ Coplanar A.pt B.pt C.pt D.pt := by
  constructor
  · rintro ⟨α, hA, hB, hC, hD⟩; exact ⟨α.plane, hA, hB, hC, hD⟩
  · rintro ⟨l, hA, hB, hC, hD⟩; exact ⟨⟨l, A.pt, A.inBall, hA⟩, hA, hB, hC, hD⟩

/-- **Group I, linear part**, in the ball. -/
instance instConnection : Connection (KPt n) (KLine n) where
  ax_I1 A B h := by
    have h' := pt_ne h
    exact ⟨⟨AffLine.through A.pt B.pt h', A.pt, A.inBall, AffLine.left_mem_through h'⟩,
      AffLine.left_mem_through h', AffLine.right_mem_through h'⟩
  ax_I2 A B a b h hA hB hA' hB' :=
    KLine.ext (line_unique (pt_ne h) hA hB hA' hB')
  ax_I7_line a := by
    obtain ⟨p, hp, hpa⟩ := a.meets
    obtain ⟨O, d, hd, hmem⟩ := a.line.exists_param
    obtain ⟨r, hr⟩ := (hmem p).1 hpa
    obtain ⟨ε, hε, hq⟩ := exists_inBall_pos hp d
    refine ⟨⟨p, hp⟩, ⟨ε • d + p, hq⟩, ?_, hpa, ?_⟩
    · intro h
      have : (0 : Coord ℝ n) = ε • d := by
        have := congrArg KPt.pt h
        simpa using congrArg (· - p) this
      rcases smul_eq_zero.1 this.symm with h1 | h1
      · exact hε.ne' h1
      · exact hd h1
    · show ε • d + p ∈ a.line
      rw [hmem]; exact ⟨ε + r, by rw [hr, add_smul]; abel⟩

/-- **The linear axioms of order**, in the ball. -/
instance instLineOrder : LineOrder (KPt n) (KLine n) :=
  { instConnection with
    between_onLine := fun A B C h => by
      have := LineOrder.between_onLine (Line := CoordLine ℝ n) A.pt B.pt C.pt h
      exact ⟨ne_of_pt_ne this.1, ne_of_pt_ne this.2.1, ne_of_pt_ne this.2.2.1,
        collinear_iff.2 this.2.2.2⟩
    ax_II1 := fun A B C _ h => by
      show Between C.pt B.pt A.pt
      exact between_symm (Line := CoordLine ℝ n) (between_iff.1 h)
    ax_II2 := fun A C a _ _ hAC => by
      have h' := pt_ne hAC
      have hd : C.pt - A.pt ≠ 0 := sub_ne_zero.2 h'.symm
      refine ⟨⟨⟨(2 : ℝ)⁻¹ • (C.pt - A.pt) + A.pt,
          inBall_comb A.inBall C.inBall (by norm_num) (by norm_num)⟩, ?_⟩, ?_⟩
      · show Between A.pt _ C.pt
        exact sbtw_iff_param.2 ⟨h', 2⁻¹, by norm_num, by norm_num, rfl⟩
      · obtain ⟨ε, hε, hD⟩ := exists_inBall_pos C.inBall (C.pt - A.pt)
        refine ⟨⟨ε • (C.pt - A.pt) + C.pt, hD⟩, ?_⟩
        show Between A.pt C.pt (ε • (C.pt - A.pt) + C.pt)
        have key := (sbtw_param_iff hd (0 : ℝ) 1 (1 + ε) (O := A.pt)).2
          (Or.inl ⟨one_pos, by linarith⟩)
        rw [zero_smul, zero_add, one_smul, sub_add_cancel] at key
        have e : ε • (C.pt - A.pt) + C.pt = (1 + ε) • (C.pt - A.pt) + A.pt := by
          rw [add_smul, one_smul]; abel
        rw [e]; exact key
    ax_II3 := fun A B C h hAB hAC hBC =>
      LineOrder.ax_II3 (Line := CoordLine ℝ n) A.pt B.pt C.pt (collinear_iff.1 h) (pt_ne hAB)
        (pt_ne hAC) (pt_ne hBC)
    ax_II4 := fun A B C D a hA hB hC hD hAB hAC hAD hBC hBD hCD => by
      obtain ⟨σ, h1, h2, h3, h4⟩ := LineOrder.ax_II4 (Line := CoordLine ℝ n) A.pt B.pt C.pt D.pt
        a.line hA hB hC hD (pt_ne hAB) (pt_ne hAC) (pt_ne hAD) (pt_ne hBC) (pt_ne hBD) (pt_ne hCD)
      have e : ∀ i, (![A, B, C, D] i).pt = ![A.pt, B.pt, C.pt, D.pt] i := by
        intro i; fin_cases i <;> rfl
      refine ⟨σ, ?_, ?_, ?_, ?_⟩ <;> simp only [between_iff, e] <;> assumption }

/-! ### Group I in space -/

/-- In ordinary space, the points `0`, `(½, 0, 0)`, `(0, ½, 0)`, `(0, 0, ½)` do not lie in a plane. -/
theorem not_coplanar_pt3 :
    ¬Coplanar (pt3 (0 : ℝ) 0 0) (pt3 (1/2) 0 0) (pt3 0 (1/2) 0) (pt3 0 0 (1/2)) := by
  rintro ⟨α, h0, h1, h2, h3⟩
  set W := α.carrier.direction
  have hv : ∀ X : Coord ℝ 3, X ∈ α.carrier → X - pt3 0 0 0 ∈ W := fun X hX => sub_mem_direction h0 hX
  let f : Fin 3 → W := ![⟨_, hv _ h1⟩, ⟨_, hv _ h2⟩, ⟨_, hv _ h3⟩]
  have hli : LinearIndependent ℝ f := by
    apply LinearIndependent.of_comp W.subtype
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have e := fun j => congrFun (congrArg AffPt.toV hg) j
    simp only [Fin.sum_univ_three, Function.comp_apply, Submodule.subtype_apply, f,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, ← pt3_zero] at e
    have e0 := e 0; have e1 := e 1; have e2 := e 2
    simp at e0 e1 e2
    fin_cases i <;> simp <;> linarith
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, α.finrank_direction] at this
  omega

theorem inBall_pt3 {x y z : ℝ} (h : x * x + y * y + z * z < 1) : InBall (pt3 x y z) := by
  unfold InBall; rw [ip_pt3]; exact h

/-- **Group I** (I 1–7) in the ball of space. -/
instance instSpaceConnection : SpaceConnection (KPt 3) (KLine 3) (KPlane 3) :=
  { instConnection with
    ax_I3 := fun A B C h => by
      obtain ⟨α, hA, hB, hC⟩ :=
        exists_plane (Plane := CoordPlane ℝ 3) (mt collinear_iff.2 h)
      exact ⟨⟨α, A.pt, A.inBall, hA⟩, hA, hB, hC⟩
    ax_I4 := fun A B C α β h hA hB hC hA' hB' hC' =>
      KPlane.ext (plane_unique (mt collinear_iff.2 h) hA hB hC hA' hB' hC')
    ax_I5 := fun A B a α h hA hB hA' hB' P hP =>
      liesInPlane_of_mem (pt_ne h) hA hB hA' hB' P.pt hP
    ax_I6 := fun α β A hne hA hB => by
      obtain ⟨B, hBA, hBα, hBβ⟩ := SpaceConnection.ax_I6 (Point := Coord ℝ 3)
        (Line := CoordLine ℝ 3) α.plane β.plane A.pt (fun e => hne (KPlane.ext e)) hA hB
      obtain ⟨ε, hε, hq⟩ := exists_inBall_pos A.inBall (B - A.pt)
      have hmem : ∀ γ : CoordPlane ℝ 3, A.pt ∈ γ.carrier → B ∈ γ.carrier →
          ε • (B - A.pt) + A.pt ∈ γ.carrier := fun γ h1 h2 =>
        add_mem_of_mem_direction (Submodule.smul_mem _ ε (sub_mem_direction h1 h2)) h1
      refine ⟨⟨ε • (B - A.pt) + A.pt, hq⟩, ?_, hmem α.plane hA hBα, hmem β.plane hB hBβ⟩
      intro e
      have : ε • (B - A.pt) = 0 := by
        have := congrArg KPt.pt e
        simpa using congrArg (· - A.pt) this
      rcases smul_eq_zero.1 this with h1 | h1
      · exact hε.ne' h1
      · exact hBA (sub_eq_zero.1 h1)
    ax_I7_plane := fun α => by
      obtain ⟨p, hp, hpα⟩ := α.meets
      let b := Module.finBasisOfFinrankEq ℝ α.plane.carrier.direction α.plane.finrank_direction
      have hli := AffPt.linearIndependent_coe_basis b
      set u : Coord ℝ 3 := (b 0).1
      set w : Coord ℝ 3 := (b 1).1
      obtain ⟨ε₁, hε₁, h₁⟩ := exists_inBall_add hp u
      obtain ⟨ε₂, hε₂, h₂⟩ := exists_inBall_add hp w
      set ε := min ε₁ ε₂
      have hε : 0 < ε := lt_min hε₁ hε₂
      have hu : InBall (ε • u + p) := h₁ ε (by rw [abs_of_pos hε]; exact min_le_left _ _)
      have hw : InBall (ε • w + p) := h₂ ε (by rw [abs_of_pos hε]; exact min_le_right _ _)
      have hli' : LinearIndependent ℝ ![ε • u, ε • w] := by
        rw [LinearIndependent.pair_iff] at hli ⊢
        intro s t hst
        have := hli (s * ε) (t * ε) (by rw [mul_smul, mul_smul]; exact hst)
        exact ⟨(mul_eq_zero.1 this.1).resolve_right hε.ne',
          (mul_eq_zero.1 this.2).resolve_right hε.ne'⟩
      refine ⟨⟨p, hp⟩, ⟨_, hu⟩, ⟨_, hw⟩, hpα,
        add_mem_of_mem_direction (Submodule.smul_mem _ ε (b 0).2) hpα,
        add_mem_of_mem_direction (Submodule.smul_mem _ ε (b 1).2) hpα, ?_⟩
      rw [collinear_iff]
      exact AffPt.not_collinear_of_linearIndependent hli'
    ax_I7_space := ⟨⟨_, inBall_pt3 (by norm_num : (0:ℝ) * 0 + 0 * 0 + 0 * 0 < 1)⟩,
      ⟨_, inBall_pt3 (by norm_num : (1/2:ℝ) * (1/2) + 0 * 0 + 0 * 0 < 1)⟩,
      ⟨_, inBall_pt3 (by norm_num : (0:ℝ) * 0 + (1/2) * (1/2) + 0 * 0 < 1)⟩,
      ⟨_, inBall_pt3 (by norm_num : (0:ℝ) * 0 + 0 * 0 + (1/2) * (1/2) < 1)⟩,
      fun h => not_coplanar_pt3 (coplanar_iff.1 h)⟩ }

/-- A line of the ball lies (in ordinary space) in a plane of the ball if all its points inside
the ball do. -/
theorem liesInPlane_line {a : KLine 3} {α : KPlane 3} (h : LiesInPlane (Point := KPt 3) a α) :
    LiesInPlane (Point := Coord ℝ 3) a.line α.plane := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := exists_two_points (Point := KPt 3) a
  exact liesInPlane_of_mem (pt_ne hPQ) hP hQ (h P hP) (h Q hQ)

/-- **Groups I and II** in the ball of space. -/
instance instSpaceOrder : SpaceOrder (KPt 3) (KLine 3) (KPlane 3) :=
  { instSpaceConnection, instLineOrder with
    ax_II5 := fun A B C α a hnc hA hB hC hai hAa hBa hCa hX => by
      obtain ⟨X, hXa, hX⟩ := hX
      have key := SpaceOrder.ax_II5 (Point := Coord ℝ 3) (Line := CoordLine ℝ 3)
        A.pt B.pt C.pt α.plane a.line (mt collinear_iff.2 hnc) hA hB hC (liesInPlane_line hai)
        hAa hBa hCa ⟨X.pt, hXa, hX⟩
      rcases key with ⟨Y, hYa, hY⟩ | ⟨Y, hYa, hY⟩
      · exact Or.inl ⟨⟨Y, inBall_between B.inBall C.inBall hY⟩, hYa, hY⟩
      · exact Or.inr ⟨⟨Y, inBall_between A.inBall C.inBall hY⟩, hYa, hY⟩ }

/-! ### Axiom III fails -/

/-- A point of `K³` written in the plane `z = 0` spanned by `O`, `P`, `Q`. -/
theorem mem_plane_z0 {S : AffineSubspace ℝ (Coord ℝ 3)} (hO : pt3 (0:ℝ) 0 0 ∈ S)
    (hP : pt3 (1/2 : ℝ) 0 0 ∈ S) (hQ : pt3 (0 : ℝ) (1/2) 0 ∈ S) {X : Coord ℝ 3}
    (hX : AffPt.toV X 2 = 0) : X ∈ S := by
  have e : X = (2 * AffPt.toV X 0) • (pt3 (1/2) 0 0 - pt3 0 0 0) +
      (2 * AffPt.toV X 1) • (pt3 0 (1/2) 0 - pt3 0 0 0) + pt3 0 0 0 := by
    rw [pt3_sub, pt3_sub, smul_pt3, smul_pt3, pt3_add, pt3_add]
    exact pt3_ext (by simp; ring) (by simp; ring) (by simp [hX])
  rw [e]
  exact add_mem_of_mem_direction (Submodule.add_mem _
    (Submodule.smul_mem _ _ (sub_mem_direction hO hP))
    (Submodule.smul_mem _ _ (sub_mem_direction hO hQ))) hO

theorem toV2_of_mem_through {X P Q : Coord ℝ 3} (hPQ : P ≠ Q) (hP : AffPt.toV P 2 = 0)
    (hQ : AffPt.toV Q 2 = 0) (hX : X ∈ AffLine.through P Q hPQ) : AffPt.toV X 2 = 0 := by
  obtain ⟨r, rfl⟩ := (AffLine.mem_through_iff hPQ).1 hX
  simp [hP, hQ]

/-- **Two parallels**: in the plane `z = 0` of the non-euclidean geometry, through the point
`A = (0, ½, 0)` off the line `a` (`y = z = 0`) pass two different lines not meeting `a`: the line
`y = ½` and the line through `(½, ¼, 0)`, which meets `y = z = 0` (in ordinary space) only in the
point `(1, 0, 0)` of the sphere. -/
theorem exists_two_parallels :
    ∃ (α : KPlane 3) (a : KLine 3) (A : KPt 3) (b₁ b₂ : KLine 3),
      LiesInPlane (Point := KPt 3) a α ∧ A ∈ α ∧ A ∉ a ∧ b₁ ≠ b₂ ∧
      (LiesInPlane (Point := KPt 3) b₁ α ∧ A ∈ b₁ ∧ ¬Meets (Point := KPt 3) b₁ a) ∧
      (LiesInPlane (Point := KPt 3) b₂ α ∧ A ∈ b₂ ∧ ¬Meets (Point := KPt 3) b₂ a) := by
  have hO : InBall (pt3 (0:ℝ) 0 0) := inBall_pt3 (by norm_num)
  have hQ : InBall (pt3 (0:ℝ) (1/2) 0) := inBall_pt3 (by norm_num)
  have hOPQ : ¬Collinear (pt3 (0:ℝ) 0 0) (pt3 (1/2) 0 0) (pt3 0 (1/2) 0) := by
    apply not_collinear_of_li; rw [pt3_sub, pt3_sub]; simp only [sub_zero]
    exact li_pt3 (by norm_num)
  obtain ⟨α₀, h0, h1, h2⟩ := exists_plane (Plane := CoordPlane ℝ 3) hOPQ
  let α : KPlane 3 := ⟨α₀, _, hO, h0⟩
  have hα : ∀ X : KPt 3, AffPt.toV X.pt 2 = 0 → X ∈ α := fun X hX => mem_plane_z0 h0 h1 h2 hX
  have hOP : pt3 (0:ℝ) 0 0 ≠ pt3 (1/2) 0 0 := fun e => by
    have := congrFun (congrArg AffPt.toV e) 0; norm_num at this
  have hQR₁ : pt3 (0:ℝ) (1/2) 0 ≠ pt3 (1/2) (1/2) 0 := fun e => by
    have := congrFun (congrArg AffPt.toV e) 0; norm_num at this
  have hQR₂ : pt3 (0:ℝ) (1/2) 0 ≠ pt3 (1/2) (1/4) 0 := fun e => by
    have := congrFun (congrArg AffPt.toV e) 0; norm_num at this
  let a : KLine 3 := ⟨AffLine.through _ _ hOP, _, hO, AffLine.left_mem_through hOP⟩
  let b₁ : KLine 3 := ⟨AffLine.through _ _ hQR₁, _, hQ, AffLine.left_mem_through hQR₁⟩
  let b₂ : KLine 3 := ⟨AffLine.through _ _ hQR₂, _, hQ, AffLine.left_mem_through hQR₂⟩
  let A : KPt 3 := ⟨_, hQ⟩
  have hai : LiesInPlane (Point := KPt 3) a α := fun X hX =>
    hα X (toV2_of_mem_through hOP rfl rfl hX)
  have hmem_a : ∀ X : KPt 3, X ∈ a → AffPt.toV X.pt 1 = 0 := by
    intro X hX
    obtain ⟨r, hr⟩ := (AffLine.mem_through_iff hOP).1 hX
    rw [hr]; simp
  have hAa : A ∉ a := fun h => by have := hmem_a A h; norm_num [A] at this
  have hb₁ : LiesInPlane (Point := KPt 3) b₁ α ∧ A ∈ b₁ ∧ ¬Meets (Point := KPt 3) b₁ a := by
    refine ⟨fun X hX => hα X (toV2_of_mem_through hQR₁ rfl rfl hX),
      AffLine.left_mem_through hQR₁, ?_⟩
    rintro ⟨X, hX1, hX2⟩
    have h1 := hmem_a X hX2
    obtain ⟨r, hr⟩ := (AffLine.mem_through_iff hQR₁).1 hX1
    rw [hr] at h1; simp at h1
  have hb₂ : LiesInPlane (Point := KPt 3) b₂ α ∧ A ∈ b₂ ∧ ¬Meets (Point := KPt 3) b₂ a := by
    refine ⟨fun X hX => hα X (toV2_of_mem_through hQR₂ rfl rfl hX),
      AffLine.left_mem_through hQR₂, ?_⟩
    rintro ⟨X, hX1, hX2⟩
    have h1 := hmem_a X hX2
    have hXa : AffPt.toV X.pt 2 = 0 := toV2_of_mem_through hOP rfl rfl hX2
    obtain ⟨r, hr⟩ := (AffLine.mem_through_iff hQR₂).1 hX1
    have hX0 : AffPt.toV X.pt 0 = r * (1/2) := by rw [hr]; simp
    rw [hr] at h1; simp at h1
    have hr2 : r = 2 := by linarith
    have hb := X.inBall
    unfold InBall at hb
    rw [ip_eq_coords, hX0, hXa, hr2] at hb
    nlinarith [sq_nonneg (AffPt.toV X.pt 1)]
  have hne : b₁ ≠ b₂ := by
    intro e
    have hR₂b₁ : pt3 (1/2 : ℝ) (1/4) 0 ∈ b₁.line := by
      rw [e]; exact AffLine.right_mem_through hQR₂
    obtain ⟨r, hr⟩ := (AffLine.mem_through_iff hQR₁).1 hR₂b₁
    have := congrFun (congrArg AffPt.toV hr) 1
    simp at this
  exact ⟨α, a, A, b₁, b₂, hai, hα A rfl, hAa, hne, hb₁, hb₂⟩

/-- **Axiom III fails** in the non-euclidean geometry of space. -/
theorem not_axiomIIISpace : ¬AxiomIIISpace (KPt 3) := by
  intro hIII
  obtain ⟨α, a, A, b₁, b₂, hai, hAα, hAa, hne, hb₁, hb₂⟩ := exists_two_parallels
  obtain ⟨b, -, huniq⟩ := hIII α a A hai hAα hAa
  exact hne ((huniq b₁ hb₁).trans (huniq b₂ hb₂).symm)

/-! ### The projective invariant of two points -/

/-- `√(1 - |p|²)`. -/
noncomputable def wt (p : Coord ℝ n) : ℝ := Real.sqrt (1 - ip p p)

/-- **The invariant of two points** `ch p q = (1 - ⟪p, q⟫) / (√(1 - |p|²) √(1 - |q|²))`: the
hyperbolic cosine of the Cayley–Klein distance of `p` and `q`. -/
noncomputable def ch (p q : Coord ℝ n) : ℝ := (1 - ip p q) / (wt p * wt q)

theorem wt_pos {p : Coord ℝ n} (hp : InBall p) : 0 < wt p :=
  Real.sqrt_pos.2 (by unfold InBall at hp; linarith)

theorem wt_sq {p : Coord ℝ n} (hp : InBall p) : wt p ^ 2 = 1 - ip p p :=
  Real.sq_sqrt (by unfold InBall at hp; linarith)

theorem one_sub_ip_pos {p q : Coord ℝ n} (hp : InBall p) (hq : InBall q) : 0 < 1 - ip p q := by
  unfold InBall at hp hq
  have h := ip_self_nonneg (p - q)
  simp only [ip_sub_left, ip_sub_right] at h
  rw [ip_comm q p] at h
  linarith

theorem ch_comm (p q : Coord ℝ n) : ch p q = ch q p := by
  rw [ch, ch, ip_comm, mul_comm]

theorem ch_pos {p q : Coord ℝ n} (hp : InBall p) (hq : InBall q) : 0 < ch p q :=
  div_pos (one_sub_ip_pos hp hq) (mul_pos (wt_pos hp) (wt_pos hq))

/-- The identity behind `ch p q > 1`. -/
theorem gram_identity (p q : Coord ℝ n) :
    (1 - ip p q) ^ 2 - (1 - ip p p) * (1 - ip q q) =
      ip (p - q) (p - q) * (1 - ip q q) + ip (p - q) q ^ 2 := by
  simp only [ip_sub_left, ip_sub_right]
  rw [ip_comm q p]; ring

/-- `ch p q > 1` for distinct points `p ≠ q`. -/
theorem one_lt_ch {p q : Coord ℝ n} (hp : InBall p) (hq : InBall q) (hpq : p ≠ q) :
    1 < ch p q := by
  have hw := mul_pos (wt_pos hp) (wt_pos hq)
  rw [ch, one_lt_div hw]
  have h1 : 0 < ip (p - q) (p - q) := ip_self_pos (sub_ne_zero.2 hpq)
  have h2 : 0 < 1 - ip q q := by unfold InBall at hq; linarith
  have key : (wt p * wt q) ^ 2 < (1 - ip p q) ^ 2 := by
    rw [mul_pow, wt_sq hp, wt_sq hq]
    have := gram_identity p q
    nlinarith [sq_nonneg (ip (p - q) q), mul_pos h1 h2]
  exact lt_of_pow_lt_pow_left₀ 2 (one_sub_ip_pos hp hq).le key

theorem ch_self {p : Coord ℝ n} (hp : InBall p) : ch p p = 1 := by
  rw [ch, ← sq, wt_sq hp, div_self (by unfold InBall at hp; linarith)]

/-! ### The invariant along a segment -/

/-- The relations between the invariants of three points `a`, `b`, `c` with `b` between `a` and
`c` (`b = (1 - t) a + t c`). -/
theorem ch_between_rel {a c : Coord ℝ n} (ha : InBall a) (hc : InBall c) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hb : InBall (t • (c - a) + a)) :
    ∃ l m : ℝ, 0 < l ∧ 0 < m ∧ ch a (t • (c - a) + a) = l + m * ch a c ∧
      ch (t • (c - a) + a) c = l * ch a c + m ∧ l ^ 2 + m ^ 2 + 2 * l * m * ch a c = 1 := by
  set b := t • (c - a) + a with hbdef
  have hwa := wt_pos ha; have hwb := wt_pos hb; have hwc := wt_pos hc
  have ea := wt_sq ha; have eb := wt_sq hb; have ec := wt_sq hc
  have i1 : 1 - ip a b = (1 - t) * wt a ^ 2 + t * (1 - ip a c) := by
    rw [ea, hbdef]; simp only [ip_add_right, ip_smul_right, ip_sub_right]; ring
  have i2 : 1 - ip b c = (1 - t) * (1 - ip a c) + t * wt c ^ 2 := by
    rw [ec, hbdef]; simp only [ip_add_left, ip_smul_left, ip_sub_left]; ring
  have i3 : wt b ^ 2 = (1 - t) ^ 2 * wt a ^ 2 + t ^ 2 * wt c ^ 2 + 2 * t * (1 - t) * (1 - ip a c) := by
    rw [ea, eb, ec, hbdef]
    simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, ip_sub_left, ip_sub_right]
    rw [ip_comm c a]; ring
  refine ⟨(1 - t) * wt a / wt b, t * wt c / wt b, by have := sub_pos.2 ht1; positivity,
    by positivity, ?_, ?_, ?_⟩
  · rw [ch, ch, i1]; field_simp
  · rw [ch, ch, i2]; field_simp
  · rw [ch]; field_simp; rw [i3]; ring

/-- **Addition of distances**: for `b` between `a` and `c`,
`ch a c = ch a b · ch b c + √((ch a b² - 1)(ch b c² - 1))`. -/
theorem ch_add {a b c : Coord ℝ n} (ha : InBall a) (hb : InBall b) (hc : InBall c)
    (h : Between a b c) :
    ch a c = ch a b * ch b c + Real.sqrt ((ch a b ^ 2 - 1) * (ch b c ^ 2 - 1)) := by
  obtain ⟨hac, t, ht0, ht1, rfl⟩ := sbtw_iff_param.1 h
  obtain ⟨l, m, hl, hm, e1, e2, e3⟩ := ch_between_rel ha hc ht0 ht1 hb
  have hg := one_lt_ch ha hc hac
  set α := ch a (t • (c - a) + a)
  set β := ch (t • (c - a) + a) c
  set γ := ch a c
  have hF : (γ - α * β) ^ 2 = (α ^ 2 - 1) * (β ^ 2 - 1) := by
    rw [e1, e2]; linear_combination (-(γ ^ 2 - 1)) * e3
  have hs1 : α < β * γ := by
    have : β * γ - α = l * (γ ^ 2 - 1) := by rw [e1, e2]; ring
    have : 0 < l * (γ ^ 2 - 1) := mul_pos hl (by nlinarith)
    linarith
  have hs2 : β < α * γ := by
    have : α * γ - β = m * (γ ^ 2 - 1) := by rw [e1, e2]; ring
    have : 0 < m * (γ ^ 2 - 1) := mul_pos hm (by nlinarith)
    linarith
  have hα : 0 < α := by rw [e1]; positivity
  have hβ : 0 < β := by rw [e2]; positivity
  have hge : α * β ≤ γ := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    set x := α * β - γ
    have hx : 0 < x := sub_pos.2 hlt
    have hx2 : x ^ 2 = (α ^ 2 - 1) * (β ^ 2 - 1) := by rw [← hF]; ring
    have k1 : β * x < α * (β ^ 2 - 1) := by
      have : β * γ = α * β ^ 2 - β * x := by simp only [x]; ring
      nlinarith
    have k2 : α * x < β * (α ^ 2 - 1) := by
      have : α * γ = α ^ 2 * β - α * x := by simp only [x]; ring
      nlinarith
    have k3 : 0 ≤ β * x := by positivity
    have k4 : 0 ≤ α * x := by positivity
    have := mul_lt_mul'' k1 k2 k3 k4
    nlinarith
  have : γ - α * β = Real.sqrt ((α ^ 2 - 1) * (β ^ 2 - 1)) := by
    rw [← hF, Real.sqrt_sq (sub_nonneg.2 hge)]
  linarith

theorem mul_ch_le_of_between {a b c : Coord ℝ n} (ha : InBall a) (hb : InBall b) (hc : InBall c)
    (h : Between a b c) : ch a b * ch b c ≤ ch a c := by
  rw [ch_add ha hb hc h]
  linarith [Real.sqrt_nonneg ((ch a b ^ 2 - 1) * (ch b c ^ 2 - 1))]

/-- **The invariant increases along a segment.** -/
theorem ch_lt_of_between {a b c : Coord ℝ n} (ha : InBall a) (hb : InBall b) (hc : InBall c)
    (h : Between a b c) : ch a b < ch a c := by
  have h1 := mul_ch_le_of_between ha hb hc h
  have h2 := one_lt_ch hb hc (ne23_of_between (Line := CoordLine ℝ n) h)
  have h3 := ch_pos ha hb
  nlinarith

/-- **Laying off a given distance** from `a` in the direction `u`. -/
theorem exists_ch_eq {a u : Coord ℝ n} (ha : InBall a) (hu : u ≠ 0) {κ : ℝ} (hκ : 1 < κ) :
    ∃ s : ℝ, 0 < s ∧ InBall (s • u + a) ∧ ch a (s • u + a) = κ := by
  set w := wt a with hwdef
  have hw : 0 < w := wt_pos ha
  have ew : w ^ 2 = 1 - ip a a := wt_sq ha
  set m := ip a u
  set q := ip u u
  have hq : 0 < q := ip_self_pos hu
  set g := w ^ 2 * q + m ^ 2
  have hg : m ^ 2 < g := by
    have : 0 < w ^ 2 * q := by positivity
    linarith
  set r := Real.sqrt g
  have hr2 : r ^ 2 = g := Real.sq_sqrt (by positivity)
  have hr : |m| < r := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) hg
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg m) hr
  set k := Real.sqrt (κ ^ 2 - 1)
  have hk2 : k ^ 2 = κ ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hk0 : 0 < k := Real.sqrt_pos.2 (by nlinarith)
  have hkκ : k < κ := by nlinarith
  set D := κ * r + k * m with hDdef
  have hD : 0 < D := by
    have h1 : k * |m| ≤ k * r := mul_le_mul_of_nonneg_left hr.le hk0.le
    have h2 : k * r < κ * r := mul_lt_mul_of_pos_right hkκ hr0
    have h3 : -(k * |m|) ≤ k * m := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le m) hk0.le
    linarith
  set s := k * w ^ 2 / D with hsdef
  have hs : 0 < s := by positivity
  have hsD : s * D = k * w ^ 2 := by rw [hsdef]; field_simp
  clear_value s D
  have hb1 : 1 - ip (s • u + a) (s • u + a) = (w * r / D) ^ 2 := by
    have e : ip (s • u + a) (s • u + a) = s ^ 2 * q + 2 * s * m + ip a a := by
      simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right]
      rw [ip_comm u a]; ring
    rw [e, div_pow, eq_div_iff (by positivity)]
    have key : w ^ 2 * D ^ 2 - 2 * (k * w ^ 2) * m * D - (k * w ^ 2) ^ 2 * q = w ^ 2 * r ^ 2 := by
      rw [hDdef]
      linear_combination (-(w ^ 2 * r ^ 2)) * hk2 + (w ^ 2 * k ^ 2) * hr2
    have e2 : (1 - (s ^ 2 * q + 2 * s * m + ip a a)) * D ^ 2 =
        w ^ 2 * D ^ 2 - 2 * (s * D) * m * D - (s * D) ^ 2 * q := by
      linear_combination (-(D ^ 2)) * ew
    rw [e2, hsD, key]; ring
  have hbin : InBall (s • u + a) := by
    unfold InBall
    have : 0 < (w * r / D) ^ 2 := by positivity
    linarith
  refine ⟨s, hs, hbin, ?_⟩
  have hwb : wt (s • u + a) = w * r / D := by
    rw [wt, hb1, Real.sqrt_sq (by positivity)]
  have h1 : 1 - ip a (s • u + a) = w ^ 2 * κ * r / D := by
    simp only [ip_add_right, ip_smul_right]
    rw [eq_div_iff hD.ne']
    have : 1 - (s * m + ip a a) = w ^ 2 - s * m := by rw [ew]; ring
    rw [this]
    linear_combination (-m) * hsD + w ^ 2 * hDdef
  rw [ch, hwb, h1, ← hwdef]
  field_simp

/-! ### Points of the ball on lines and rays -/

theorem sameSidePt_iff {O A X : KPt n} : SameSidePt O A X ↔ SameSidePt O.pt A.pt X.pt := by
  unfold SameSidePt
  rw [collinear_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨pt_ne h1, pt_ne h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨ne_of_pt_ne h1, ne_of_pt_ne h2, h3, h4⟩

theorem mem_ray_iff' {O A X : KPt n} : X ∈ ray O A ↔ X.pt ∈ ray O.pt A.pt := sameSidePt_iff

/-- Two points of a ray of the ball given by positive multiples of the same vector. -/
theorem ray_eq_of_pos_smul' {O A B : KPt n} (hA : A ≠ O) {c : ℝ} (hc : 0 < c)
    (hB : B.pt - O.pt = c • (A.pt - O.pt)) : ray O B = ray O A := by
  ext X
  rw [mem_ray_iff', mem_ray_iff', AffPt.ray_eq_of_pos_smul (pt_ne hA) hc hB]

/-- In ordinary space, `b` between `a` and `c` and `c` between `b` and `d` give `c` between `a`
and `d`. -/
theorem between_trans_coord {a b c d : Coord ℝ n} (h1 : Between a b c) (h2 : Between b c d) :
    Between a c d := by
  obtain ⟨l, ha, hb, hc⟩ := collinear_of_between (Line := CoordLine ℝ n) h1
  obtain ⟨l', hb', hc', hd⟩ := collinear_of_between (Line := CoordLine ℝ n) h2
  have e : l' = l := line_unique (ne23_of_between (Line := CoordLine ℝ n) h1) hb' hc' hb hc
  rw [e] at hd
  obtain ⟨O, v, hv, hmem⟩ := l.exists_param
  obtain ⟨x, rfl⟩ := (hmem _).1 ha
  obtain ⟨y, rfl⟩ := (hmem _).1 hb
  obtain ⟨z, rfl⟩ := (hmem _).1 hc
  obtain ⟨w, rfl⟩ := (hmem _).1 hd
  rw [AffPt.between_iff, sbtw_param_iff hv] at h1 h2 ⊢
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · exact Or.inl ⟨by linarith, h2'⟩
  · exfalso; linarith
  · exfalso; linarith
  · exact Or.inr ⟨h2, by linarith⟩

/-! ### Congruence of segments (IV 1–3) and Archimedes's axiom (V) -/

/-- **Congruence of segments** in the non-euclidean geometry: equal invariants `ch`. -/
noncomputable instance instHasSegCong : HasSegCong (KPt n) :=
  ⟨fun A B A' B' => ch A.pt B.pt = ch A'.pt B'.pt⟩

theorem segCong_iff {A B A' B' : KPt n} : SegCong A B A' B' ↔ ch A.pt B.pt = ch A'.pt B'.pt :=
  Iff.rfl

theorem ch_lt_on_ray {a u : Coord ℝ n} (ha : InBall a) (hu : u ≠ 0) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) (h1 : InBall (s • u + a)) (h2 : InBall (t • u + a)) :
    ch a (s • u + a) < ch a (t • u + a) := by
  refine ch_lt_of_between ha h1 h2 ?_
  have := (sbtw_param_iff hu 0 s t (O := a)).2 (Or.inl ⟨hs, hst⟩)
  rwa [zero_smul, zero_add] at this

/-- **Laying off segments** (IV 1) in the non-euclidean geometry. -/
theorem axiomIV1LayOff : AxiomIV1LayOff (KPt n) := by
  intro A B A' C' hAB hC'
  have hκ := one_lt_ch A.inBall B.inBall (pt_ne hAB)
  have hC'A' : C'.pt ≠ A'.pt := (pt_ne hC').symm
  have hu : C'.pt - A'.pt ≠ 0 := sub_ne_zero.2 hC'A'
  obtain ⟨s, hs, hb, hch⟩ := exists_ch_eq A'.inBall hu hκ
  refine ⟨⟨s • (C'.pt - A'.pt) + A'.pt, hb⟩, ⟨?_, hch.symm⟩, ?_⟩
  · rw [sameSidePt_iff]; exact (AffPt.mem_ray_iff hC'A').2 ⟨s, hs, rfl⟩
  · rintro Y ⟨hY, hYc⟩
    rw [sameSidePt_iff] at hY
    obtain ⟨c, hc, hYe⟩ := (AffPt.mem_ray_iff hC'A').1 hY
    rw [segCong_iff] at hYc
    have hYb : InBall (c • (C'.pt - A'.pt) + A'.pt) := hYe ▸ Y.inBall
    have heq : ch A'.pt (c • (C'.pt - A'.pt) + A'.pt) = ch A'.pt (s • (C'.pt - A'.pt) + A'.pt) := by
      rw [← hYe, ← hYc, hch]
    apply KPt.ext
    show Y.pt = s • (C'.pt - A'.pt) + A'.pt
    rw [hYe]
    rcases lt_trichotomy c s with h | h | h
    · exact absurd heq (ch_lt_on_ray A'.inBall hu hc h hYb hb).ne
    · rw [h]
    · exact absurd heq (ch_lt_on_ray A'.inBall hu hs h hb hYb).ne'

/-- **The linear axioms of congruence** IV 1–3 in the non-euclidean geometry. -/
instance instSegmentCongruence : SegmentCongruence (KPt n) (KLine n) :=
  { instLineOrder with
    segCong_swap := fun A B A' B' h =>
      ⟨by rw [segCong_iff, ch_comm]; exact h, by rw [segCong_iff, ch_comm B'.pt]; exact h⟩
    ax_IV1 := axiomIV1LayOff
    ax_IV1_refl := fun _ _ _ => rfl
    ax_IV2 := fun _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
    ax_IV3 := fun A B C A' B' C' h h' h1 h2 => by
      have hb := between_of_segmentsMeetOnlyAt (L := KLine n) h
      have hb' := between_of_segmentsMeetOnlyAt (L := KLine n) h'
      rw [segCong_iff] at h1 h2 ⊢
      rw [ch_add A.inBall B.inBall C.inBall hb, ch_add A'.inBall B'.inBall C'.inBall hb', h1, h2] }

/-- **Archimedes's axiom** (V) in the non-euclidean geometry. -/
theorem axiomV : AxiomV (KPt n) := by
  intro P B h01 hstep hcong
  set κ := ch (P 0).pt (P 1).pt with hκdef
  have hP01 : (P 0).pt ≠ (P 1).pt := pt_ne (ne12_of_between (Line := KLine n) h01)
  have hκ : 1 < κ := one_lt_ch (P 0).inBall (P 1).inBall hP01
  have hstep' : ∀ k, ch (P k).pt (P (k + 1)).pt = κ := fun k => hcong k 0
  have hchain : ∀ k, 1 ≤ k → Between (P 0).pt (P k).pt (P (k + 1)).pt := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk'
      · exact hstep 0
      · exact between_trans_coord (ih hk') (hstep k)
  have hpow : ∀ k, 1 ≤ k → κ ^ k ≤ ch (P 0).pt (P k).pt := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk'
      · simp [κ]
      · have h1 := mul_ch_le_of_between (P 0).inBall (P k).inBall (P (k + 1)).inBall (hchain k hk')
        rw [hstep' k] at h1
        rw [pow_succ]
        nlinarith [ih hk']
  set d := (P 1).pt - (P 0).pt with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hP01.symm
  have hpos : ∀ k, 1 ≤ k → ∃ x : ℝ, 1 ≤ x ∧ (P k).pt = x • d + (P 0).pt := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk'
      · exact ⟨1, le_rfl, by rw [one_smul, hd, sub_add_cancel]⟩
      · obtain ⟨x, hx, hxe⟩ := ih hk'
        obtain ⟨-, t, ht0, ht1, hte⟩ := sbtw_iff_param.1 (hchain k hk')
        refine ⟨x / t, ?_, ?_⟩
        · rw [le_div_iff₀ ht0]; nlinarith
        · have e : (P (k + 1)).pt - (P 0).pt = t⁻¹ • ((P k).pt - (P 0).pt) := by
            rw [hte, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
          rw [hxe, add_sub_cancel_right, smul_smul] at e
          rw [← sub_add_cancel (P (k + 1)).pt (P 0).pt, e, div_eq_inv_mul]
  obtain ⟨-, t, ht0, ht1, hB1⟩ := sbtw_iff_param.1 h01
  have hBpos : B.pt = t⁻¹ • d + (P 0).pt := by
    have : d = t • (B.pt - (P 0).pt) := by rw [hd, hB1, add_sub_cancel_right]
    rw [this, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, sub_add_cancel]
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (ch (P 0).pt B.pt) hκ
  obtain ⟨x, hx1, hxe⟩ := hpos (N + 1) (by omega)
  have hchM : ch (P 0).pt B.pt < ch (P 0).pt (P (N + 1)).pt :=
    lt_of_lt_of_le hN (le_trans (pow_le_pow_right₀ hκ.le (by omega)) (hpow (N + 1) (by omega)))
  refine ⟨N + 1, ?_⟩
  show Between (P 0).pt B.pt (P (N + 1)).pt
  have ht1' : 1 < t⁻¹ := one_lt_inv₀ ht0 |>.2 ht1
  rcases lt_trichotomy t⁻¹ x with h | h | h
  · rw [hBpos, hxe]
    have := (sbtw_param_iff hd0 0 t⁻¹ x (O := (P 0).pt)).2 (Or.inl ⟨by linarith, h⟩)
    rwa [zero_smul, zero_add] at this
  · exfalso
    rw [hBpos, h, ← hxe] at hchM
    exact lt_irrefl _ hchM
  · exfalso
    have hb : Between (P 0).pt (P (N + 1)).pt B.pt := by
      rw [hBpos, hxe]
      have := (sbtw_param_iff hd0 0 x t⁻¹ (O := (P 0).pt)).2 (Or.inl ⟨by linarith, h⟩)
      rwa [zero_smul, zero_add] at this
    exact absurd hchM (not_lt.2 (ch_lt_of_between (P 0).inBall (P (N + 1)).inBall B.inBall hb).le)

/-- **Archimedes's axiom** in the non-euclidean geometry. -/
instance instArchimedes : Archimedes (KPt n) (KLine n) :=
  { instLineOrder with ax_V := axiomV }

/-! ### The Cayley–Klein angle -/

/-- **The quadratic form of the Cayley–Klein metric at `o`**:
`G_o(u, v) = (1 - |o|²) ⟪u, v⟫ + ⟪o, u⟫ ⟪o, v⟫`. -/
noncomputable def G (o u v : Coord ℝ n) : ℝ := (1 - ip o o) * ip u v + ip o u * ip o v

theorem G_comm (o u v : Coord ℝ n) : G o u v = G o v u := by
  unfold G; rw [ip_comm u v]; ring

theorem G_smul_left (o : Coord ℝ n) (c : ℝ) (u v : Coord ℝ n) : G o (c • u) v = c * G o u v := by
  unfold G; simp only [ip_smul_left, ip_smul_right]; ring

theorem G_smul_right (o : Coord ℝ n) (c : ℝ) (u v : Coord ℝ n) : G o u (c • v) = c * G o u v := by
  rw [G_comm, G_smul_left, G_comm]

theorem G_add_left (o u u' v : Coord ℝ n) : G o (u + u') v = G o u v + G o u' v := by
  unfold G; simp only [ip_add_left, ip_add_right]; ring

theorem G_add_right (o u v v' : Coord ℝ n) : G o u (v + v') = G o u v + G o u v' := by
  rw [G_comm, G_add_left, G_comm, G_comm o v' u]

theorem G_sub_left (o u u' v : Coord ℝ n) : G o (u - u') v = G o u v - G o u' v := by
  unfold G; simp only [ip_sub_left, ip_sub_right]; ring

theorem G_sub_right (o u v v' : Coord ℝ n) : G o u (v - v') = G o u v - G o u v' := by
  rw [G_comm, G_sub_left, G_comm, G_comm o v' u]

theorem G_self_pos {o u : Coord ℝ n} (ho : InBall o) (hu : u ≠ 0) : 0 < G o u u := by
  unfold G
  have h1 : 0 < 1 - ip o o := by unfold InBall at ho; linarith
  have h2 := ip_self_pos hu
  nlinarith [mul_self_nonneg (ip o u)]

/-- The cosine of the Cayley–Klein angle between the directions `u`, `v` at `o`. -/
noncomputable def kcosV (o u v : Coord ℝ n) : ℝ := G o u v / Real.sqrt (G o u u * G o v v)

/-- **The cosine of the angle `∠AOB`** in the non-euclidean geometry. -/
noncomputable def kcos (A O B : Coord ℝ n) : ℝ := kcosV O (A - O) (B - O)

theorem kcosV_comm (o u v : Coord ℝ n) : kcosV o u v = kcosV o v u := by
  unfold kcosV; rw [G_comm, mul_comm]

theorem kcosV_smul (o u v : Coord ℝ n) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    kcosV o (c • u) (d • v) = kcosV o u v := by
  unfold kcosV
  simp only [G_smul_left, G_smul_right]
  have e : c * (c * G o u u) * (d * (d * G o v v)) = (c * d) ^ 2 * (G o u u * G o v v) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
    show d * (c * G o u v) = (c * d) * G o u v by ring,
    mul_div_mul_left _ _ (by positivity : c * d ≠ 0)]

/-- `G` in terms of the invariants `ch`. -/
theorem G_eq_ch {o a b : Coord ℝ n} (ho : InBall o) (ha : InBall a) (hb : InBall b) :
    G o (a - o) (b - o) = wt o ^ 2 * wt a * wt b * (ch o a * ch o b - ch a b) := by
  have h1 : wt o ^ 2 * wt a * wt b * (ch o a * ch o b - ch a b) =
      (1 - ip o a) * (1 - ip o b) - wt o ^ 2 * (1 - ip a b) := by
    have := wt_pos ho; have := wt_pos ha; have := wt_pos hb
    unfold ch; field_simp
  rw [h1, wt_sq ho]
  unfold G
  simp only [ip_sub_left, ip_sub_right]
  rw [ip_comm a o]
  ring

/-- **The cosine of an angle in terms of the invariants of its vertex and two points of its
sides** (the law of cosines of the non-euclidean geometry). -/
theorem kcos_eq_ch {o a b : Coord ℝ n} (ho : InBall o) (ha : InBall a) (hb : InBall b) :
    kcos a o b = (ch o a * ch o b - ch a b) / Real.sqrt ((ch o a ^ 2 - 1) * (ch o b ^ 2 - 1)) := by
  unfold kcos kcosV
  rw [G_eq_ch ho ha hb, G_eq_ch ho ha ha, G_eq_ch ho hb hb, ch_self ha, ch_self hb]
  have hW : 0 < wt o ^ 2 * wt a * wt b := by
    have := wt_pos ho; have := wt_pos ha; have := wt_pos hb; positivity
  have e : wt o ^ 2 * wt a * wt a * (ch o a * ch o a - 1) * (wt o ^ 2 * wt b * wt b *
      (ch o b * ch o b - 1)) = (wt o ^ 2 * wt a * wt b) ^ 2 * ((ch o a ^ 2 - 1) * (ch o b ^ 2 - 1)) := by
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW.le, mul_div_mul_left _ _ hW.ne']

theorem sqrt_ch_pos {o a b : Coord ℝ n} (ho : InBall o) (ha : InBall a) (hb : InBall b)
    (hao : a ≠ o) (hbo : b ≠ o) : 0 < Real.sqrt ((ch o a ^ 2 - 1) * (ch o b ^ 2 - 1)) := by
  have h1 := one_lt_ch ho ha hao.symm
  have h2 := one_lt_ch ho hb hbo.symm
  exact Real.sqrt_pos.2 (mul_pos (by nlinarith) (by nlinarith))

/-! ### Congruence of angles (IV 4–6) -/

/-- **Congruence of angles** in the non-euclidean geometry: equal cosines `kcos`. -/
noncomputable instance instHasAngCong : HasAngCong (KPt n) :=
  ⟨fun A O B A' O' B' => kcos A.pt O.pt B.pt = kcos A'.pt O'.pt B'.pt⟩

theorem angCong_iff {A O B A' O' B' : KPt n} :
    AngCong A O B A' O' B' ↔ kcos A.pt O.pt B.pt = kcos A'.pt O'.pt B'.pt := Iff.rfl

theorem exists_pos_of_ray_eq' {O A C : KPt n} (hA : A ≠ O) (h : ray O C = ray O A) :
    ∃ c : ℝ, 0 < c ∧ C.pt - O.pt = c • (A.pt - O.pt) := by
  have hC : C ≠ O := by
    intro hCO
    rw [hCO] at h
    have : A ∈ ray O O := h ▸ mem_ray_self (Line := KLine n) hA
    exact this.1 rfl
  have : C ∈ ray O A := h ▸ mem_ray_self (Line := KLine n) hC
  rw [mem_ray_iff'] at this
  obtain ⟨c, hc, e⟩ := (AffPt.mem_ray_iff (pt_ne hA)).1 this
  exact ⟨c, hc, by rw [e, add_sub_cancel_right]⟩

variable [NeZero n]

theorem ne_of_not_collinear {A B C : KPt n} (h : ¬Collinear A B C) : A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  obtain ⟨h1, h2, h3⟩ := AffPt.not_collinear_of_eq (mt collinear_iff.2 h)
  exact ⟨ne_of_pt_ne h1, ne_of_pt_ne h2, ne_of_pt_ne h3⟩

theorem ray_ne_ray' {A O B : KPt n} (h : ¬Collinear A O B) : ray O A ≠ ray O B := by
  obtain ⟨hAO, -, hOB⟩ := ne_of_not_collinear h
  intro e
  obtain ⟨c, -, hc⟩ := exists_pos_of_ray_eq' hAO e.symm
  exact h (collinear_iff.2 (AffPt.collinear_of_smul (pt_ne hAO) c hc))

theorem sameAngle_cases' {A O B C D : KPt n} (h : ¬Collinear A O B) (hs : SameAngle A O B C D) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ((C.pt - O.pt = c • (A.pt - O.pt) ∧ D.pt - O.pt = d • (B.pt - O.pt)) ∨
      (C.pt - O.pt = c • (B.pt - O.pt) ∧ D.pt - O.pt = d • (A.pt - O.pt))) := by
  obtain ⟨hAO, -, hOB⟩ := ne_of_not_collinear h
  have hrAB := ray_ne_ray' h
  have hC : ray O C ∈ ({ray O A, ray O B} : Set (Set (KPt n))) := hs ▸ Set.mem_insert _ _
  have hD : ray O D ∈ ({ray O A, ray O B} : Set (Set (KPt n))) :=
    hs ▸ Set.mem_insert_of_mem _ rfl
  have hA' : ray O A ∈ ({ray O C, ray O D} : Set (Set (KPt n))) := hs ▸ Set.mem_insert _ _
  have hB' : ray O B ∈ ({ray O C, ray O D} : Set (Set (KPt n))) :=
    hs ▸ Set.mem_insert_of_mem _ rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC hD hA' hB'
  rcases hC with hC | hC <;> rcases hD with hD | hD
  · exfalso; rcases hB' with e | e <;> exact hrAB (by first | rw [e, hC] | rw [e, hD])
  · obtain ⟨c, hc, ec⟩ := exists_pos_of_ray_eq' hAO hC
    obtain ⟨d, hd, ed⟩ := exists_pos_of_ray_eq' hOB.symm hD
    exact ⟨c, d, hc, hd, Or.inl ⟨ec, ed⟩⟩
  · obtain ⟨c, hc, ec⟩ := exists_pos_of_ray_eq' hOB.symm hC
    obtain ⟨d, hd, ed⟩ := exists_pos_of_ray_eq' hAO hD
    exact ⟨c, d, hc, hd, Or.inr ⟨ec, ed⟩⟩
  · exfalso; rcases hA' with e | e <;> exact hrAB (by first | rw [e, hC] | rw [e, hD])

theorem kcos_of_sameAngle {A O B C D : KPt n} (h : ¬Collinear A O B) (hs : SameAngle A O B C D) :
    kcos C.pt O.pt D.pt = kcos A.pt O.pt B.pt := by
  obtain ⟨c, d, hc, hd, hcd⟩ := sameAngle_cases' h hs
  unfold kcos
  rcases hcd with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2, kcosV_smul _ _ _ hc hd]
  · rw [e1, e2, kcosV_smul _ _ _ hc hd, kcosV_comm]

/-- **The plane-free axioms of congruence of angles** (IV 4 reflexivity, IV 5) in the
non-euclidean geometry. -/
instance instAngleCongruence : AngleCongruence (KPt n) (KLine n) :=
  { instLineOrder with
    angCong_wd := fun A O B C D A' O' B' C' D' h h' hs hs' hc => by
      rw [angCong_iff, kcos_of_sameAngle h hs, kcos_of_sameAngle h' hs']; exact hc
    ax_IV4_refl := fun _ _ _ _ => rfl
    ax_IV5 := fun _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2 }

/-- **Axiom IV 6** in the non-euclidean geometry. -/
theorem axiomIV6 : AxiomIV6 (KPt n) := by
  intro A B C A' B' C' h h' hAB hAC hA
  obtain ⟨hab, hac, hbc⟩ := ne_of_not_collinear h
  obtain ⟨hab', hac', hbc'⟩ := ne_of_not_collinear h'
  rw [segCong_iff] at hAB hAC
  rw [angCong_iff, kcos_eq_ch A.inBall B.inBall C.inBall,
    kcos_eq_ch A'.inBall B'.inBall C'.inBall, hAB, hAC] at hA
  have hS := sqrt_ch_pos A'.inBall B'.inBall C'.inBall (pt_ne hab').symm (pt_ne hac').symm
  have hBC : ch B.pt C.pt = ch B'.pt C'.pt := by
    have := (div_left_inj₀ hS.ne').1 hA
    linarith
  rw [angCong_iff, angCong_iff, kcos_eq_ch B.inBall A.inBall C.inBall,
    kcos_eq_ch B'.inBall A'.inBall C'.inBall, kcos_eq_ch C.inBall A.inBall B.inBall,
    kcos_eq_ch C'.inBall A'.inBall B'.inBall]
  rw [ch_comm B.pt A.pt, ch_comm B'.pt A'.pt, ch_comm C.pt A.pt, ch_comm C'.pt A'.pt,
    ch_comm C.pt B.pt, ch_comm C'.pt B'.pt, hAB, hAC, hBC]
  exact ⟨rfl, rfl⟩

/-- **Axiom IV 6 (with IV 1–5 of the line)** in the non-euclidean geometry. -/
instance instTriangleCongruence : TriangleCongruence (KPt n) (KLine n) :=
  { instSegmentCongruence, instAngleCongruence with ax_IV6 := axiomIV6 }

/-! ### Laying off angles (IV 4) -/

omit [NeZero n] in
/-- Sides of a line of the ball are the sides of the line of ordinary space. -/
theorem sameSide_iff' {a : KLine n} {X Y : KPt n} : SameSide a X Y ↔ SameSide a.line X.pt Y.pt := by
  unfold SameSide
  constructor
  · rintro ⟨hX, hY, hno⟩
    exact ⟨hX, hY, fun ⟨Z, hZa, hZ⟩ => hno ⟨⟨Z, inBall_between X.inBall Y.inBall hZ⟩, hZa, hZ⟩⟩
  · rintro ⟨hX, hY, hno⟩
    exact ⟨hX, hY, fun ⟨Z, hZa, hZ⟩ => hno ⟨Z.pt, hZa, hZ⟩⟩

omit [NeZero n] in
/-- The midpoint of `R ∈ l` and `Q ∉ l` lies on the same side of `l` as `Q`. -/
theorem sameSide_mid {l : CoordLine ℝ n} {R Q : Coord ℝ n} (hR : R ∈ l) (hQ : Q ∉ l) :
    SameSide l ((1 / 2 : ℝ) • (Q - R) + R) Q := by
  have hRQ : Q - R ≠ 0 := sub_ne_zero.2 (fun e => hQ (e ▸ hR))
  have key : ∀ s : ℝ, s ≠ 0 → s • (Q - R) + R ∈ l → False := by
    intro s hs hm
    have hne : R ≠ s • (Q - R) + R := by
      intro e
      have : s • (Q - R) = 0 := by simpa using (congrArg (· - R) e).symm
      rcases smul_eq_zero.1 this with h | h
      · exact hs h
      · exact hRQ h
    apply hQ
    rw [l.eq_through hne hR hm, AffLine.mem_through_iff]
    exact ⟨s⁻¹, by rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hs, one_smul, sub_add_cancel]⟩
  refine ⟨fun h => key (1 / 2) (by norm_num) h, hQ, ?_⟩
  rintro ⟨Z, hZl, hZ⟩
  obtain ⟨-, t, ht0, -, hZe⟩ := sbtw_iff_param.1 hZ
  apply key (1 / 2 + t / 2) (by linarith)
  have : Z = (1 / 2 + t / 2) • (Q - R) + R := by rw [hZe]; module
  rw [← this]; exact hZl

omit [NeZero n] in
/-- The side functional of a line `l` in a plane `S`, centred at a point `O'` of `l`. -/
theorem exists_side_functional' {S : AffineSubspace ℝ (Coord ℝ n)} [FiniteDimensional ℝ S.direction]
    (hS : finrank ℝ S.direction = 2) (l : CoordLine ℝ n) (hl : l.carrier ≤ S) {O' : Coord ℝ n}
    (hO' : O' ∈ l.carrier) :
    ∃ f : Coord ℝ n →ₗ[ℝ] ℝ, ∀ X ∈ S, (X ∈ l.carrier ↔ f (X - O') = 0) := by
  obtain ⟨O0, f, -, hf⟩ := AffPt.exists_side_functional hS l hl
  have h0 : f (O' - O0) = 0 := (hf O' (hl hO')).1 hO'
  refine ⟨f, fun X hX => ?_⟩
  rw [hf X hX, show X - O0 = (X - O') + (O' - O0) by abel, map_add, h0, add_zero]

omit [NeZero n] in
/-- **Strict Cauchy–Schwarz inequality** for the form `G_o`. -/
theorem G_cs_strict {o u v : Coord ℝ n} (ho : InBall o) (hv : v ≠ 0) (huv : ∀ t : ℝ, u ≠ t • v) :
    G o u v ^ 2 < G o u u * G o v v := by
  have hGv := G_self_pos ho hv
  set t := G o u v / G o v v
  have hx : u - t • v ≠ 0 := fun h => huv t (sub_eq_zero.1 h)
  have h := G_self_pos ho hx
  simp only [G_sub_left, G_sub_right, G_smul_left, G_smul_right] at h
  rw [G_comm o v u] at h
  have e : t * G o v v = G o u v := by simp only [t]; field_simp
  rw [e, sub_self, mul_zero, sub_zero] at h
  have e2 : G o u v ^ 2 = t * G o u v * G o v v := by rw [mul_assoc, mul_comm (G o u v), ← mul_assoc, e]; ring
  nlinarith [mul_pos h hGv]

theorem kcos_sq_lt_one {A O B : Coord ℝ n} (hO : InBall O) (h : ¬Collinear A O B) :
    kcos A O B ^ 2 < 1 := by
  obtain ⟨hAO, -, hOB⟩ := AffPt.not_collinear_of_eq h
  have hv : B - O ≠ 0 := sub_ne_zero.2 hOB.symm
  have hu : A - O ≠ 0 := sub_ne_zero.2 hAO
  have huv : ∀ t : ℝ, A - O ≠ t • (B - O) := fun t e =>
    h (AffPt.collinear_of_smul hOB.symm t e).swap13
  have hcs := G_cs_strict hO hv huv
  have hP : 0 < G O (A - O) (A - O) * G O (B - O) (B - O) :=
    mul_pos (G_self_pos hO hu) (G_self_pos hO hv)
  unfold kcos kcosV
  rw [div_pow, Real.sq_sqrt hP.le, div_lt_one hP]
  exact hcs

/-- `p² = q²` and `p q ≥ 0` give `p = q`. -/
theorem eq_of_sq_eq_of_mul_nonneg {p q : ℝ} (h : p ^ 2 = q ^ 2) (hpq : 0 ≤ p * q) : p = q := by
  have : (p - q) * (p + q) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · have hq : q = -p := by linarith
    rw [hq] at hpq
    have : p = 0 := by nlinarith [sq_nonneg p]
    rw [hq, this, neg_zero]

theorem pos_mul_trans {x y z : ℝ} (h1 : 0 < x * y) (h2 : 0 < y * z) : 0 < x * z := by
  have h3 := mul_pos h1 h2
  have hy : y ≠ 0 := fun h => by rw [h, mul_zero] at h1; exact lt_irrefl _ h1
  have hy2 : 0 < y ^ 2 := by positivity
  have e : x * y * (y * z) = (x * z) * y ^ 2 := by ring
  rw [e] at h3
  exact pos_of_mul_pos_left h3 hy2.le

/-- **Laying off angles** (IV 4) in the planes of the non-euclidean geometry of space. -/
theorem axiomIV4LayOffSpace : AxiomIV4LayOffSpace (KPt 3) := by
  intro A O B α' a' O' A' D' hAOB hai hO'a hA'a hA'O' hD'α hD'a
  set S := α'.plane.carrier
  have hS : finrank ℝ S.direction = 2 := α'.plane.finrank_direction
  have hle : a'.line.carrier ≤ S := (AffPt.liesInPlane_iff).1 (liesInPlane_line hai)
  obtain ⟨f, hf⟩ := exists_side_functional' hS a'.line hle hO'a
  have hO'S : O'.pt ∈ S := hle hO'a
  have hA'S : A'.pt ∈ S := hle hA'a
  have hD'S : D'.pt ∈ S := hD'α
  have side : ∀ X Y : KPt 3, X.pt ∈ S → Y.pt ∈ S →
      (SameSide a' X Y ↔ 0 < f (X.pt - O'.pt) * f (Y.pt - O'.pt)) := fun X Y hX hY => by
    rw [sameSide_iff']; exact AffPt.sameSide_iff_mul_pos hle hf hX hY
  set o := O'.pt with hodef
  have ho : InBall o := O'.inBall
  set u := A'.pt - o with hudef
  set w := D'.pt - o with hwdef
  have hfu : f u = 0 := (hf _ hA'S).1 hA'a
  have hfw : f w ≠ 0 := fun h => hD'a ((hf _ hD'S).2 h)
  have huS : u ∈ S.direction := sub_mem_direction hO'S hA'S
  have hwS : w ∈ S.direction := sub_mem_direction hO'S hD'S
  have hu0 : u ≠ 0 := sub_ne_zero.2 (pt_ne hA'O')
  set Guu := G o u u with hGuudef
  have hGuu : 0 < Guu := G_self_pos ho hu0
  set wp := w - (G o w u / Guu) • u with hwpdef
  have hfwp : f wp = f w := by rw [hwpdef, map_sub, map_smul, hfu, smul_zero, sub_zero]
  have hwp0 : wp ≠ 0 := fun h => hfw (by rw [← hfwp, h, map_zero])
  have hwpS : wp ∈ S.direction := Submodule.sub_mem _ hwS (Submodule.smul_mem _ _ huS)
  have hGuwp : G o u wp = 0 := by
    rw [hwpdef, G_sub_right, G_smul_right, G_comm o u w, ← hGuudef]; field_simp; ring
  set Gpp := G o wp wp with hGppdef
  have hGpp : 0 < Gpp := G_self_pos ho hwp0
  set κ := kcos A.pt O.pt B.pt with hκdef
  have hκ : κ ^ 2 < 1 := kcos_sq_lt_one O.inBall (mt collinear_iff.2 hAOB)
  set nu := Real.sqrt Guu with hnudef
  set np := Real.sqrt Gpp with hnpdef
  set sk := Real.sqrt (1 - κ ^ 2) with hskdef
  have hnu : 0 < nu := Real.sqrt_pos.2 hGuu
  have hnp : 0 < np := Real.sqrt_pos.2 hGpp
  have hsk : 0 < sk := Real.sqrt_pos.2 (by linarith)
  have hnu2 : nu ^ 2 = Guu := Real.sq_sqrt hGuu.le
  have hnp2 : np ^ 2 = Gpp := Real.sq_sqrt hGpp.le
  have hsk2 : sk ^ 2 = 1 - κ ^ 2 := Real.sq_sqrt (by linarith)
  set v := (κ / nu) • u + (sk / np) • wp with hvdef
  have hvS : v ∈ S.direction :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ huS) (Submodule.smul_mem _ _ hwpS)
  have hGuv : G o u v = κ * nu := by
    rw [hvdef, G_add_right, G_smul_right, G_smul_right, hGuwp, ← hGuudef, ← hnu2]
    field_simp; ring
  have hGvv : G o v v = 1 := by
    rw [hvdef]
    simp only [G_add_left, G_add_right, G_smul_left, G_smul_right]
    rw [G_comm o wp u, hGuwp, ← hGuudef, ← hGppdef, ← hnu2, ← hnp2]
    field_simp
    linear_combination (nu * np) * hsk2
  have hfv : f v = sk / np * f w := by
    rw [hvdef, map_add, map_smul, map_smul, hfu, hfwp, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
  obtain ⟨ε, hε, hεb⟩ := exists_inBall_pos ho v
  let B' : KPt 3 := ⟨ε • v + o, hεb⟩
  have hB'v : B'.pt - o = ε • v := add_sub_cancel_right _ _
  have hB'S : B'.pt ∈ S := add_mem_of_mem_direction (Submodule.smul_mem _ ε hvS) hO'S
  have hfB' : f (B'.pt - o) = ε * (sk / np) * f w := by
    rw [hB'v, map_smul, hfv, smul_eq_mul]; ring
  have hB'a : B' ∉ a' := fun h => by
    have := (hf _ hB'S).1 h
    rw [hfB'] at this
    exact hfw ((mul_eq_zero.1 this).resolve_left (by positivity))
  have hB'O' : B' ≠ O' := fun e => hB'a (e ▸ hO'a)
  have hB'D' : 0 < f (B'.pt - o) * f (D'.pt - o) := by
    rw [hfB', ← hwdef]
    have : 0 < f w ^ 2 := by positivity
    have e : ε * (sk / np) * f w * f w = ε * (sk / np) * f w ^ 2 := by ring
    rw [e]; positivity
  have hang : kcos A'.pt O'.pt B'.pt = κ := by
    show kcosV o u (B'.pt - o) = κ
    rw [hB'v, ← one_smul ℝ u, kcosV_smul _ _ _ one_pos hε]
    unfold kcosV
    rw [hGuv, hGvv, mul_one, ← hGuudef, ← hnudef]
    field_simp
  refine ⟨B', hB'S, hB'a, hang.symm, ?_, ?_⟩
  · -- the interior of the angle lies on the side of `D'`
    intro X hXS hX
    obtain ⟨b, hO'b, hB'b⟩ := exists_line (Line := KLine 3) hB'O'.symm
    have h1 := (hX a' b hO'a hA'a hO'b hB'b).1
    rw [side X B' hXS hB'S] at h1
    rw [side X D' hXS hD'S]
    exact pos_mul_trans h1 hB'D'
  · -- uniqueness
    intro B'' hB''S hB''a hang'' hint''
    have hang2 : kcosV o u (B''.pt - o) = κ := hang''.symm
    let X : KPt 3 := ⟨(1 / 2 : ℝ) • (B''.pt - A'.pt) + A'.pt,
      inBall_comb A'.inBall B''.inBall (by norm_num) (by norm_num)⟩
    have hXS : X.pt ∈ S :=
      add_mem_of_mem_direction (Submodule.smul_mem _ _ (sub_mem_direction hA'S hB''S)) hA'S
    have hXint : X ∈ Interior A' O' B'' := by
      intro a b hO'a2 hA'a2 hO'b hB''b
      have ha2 : a = a' := line_unique hA'O'.symm hO'a2 hA'a2 hO'a hA'a
      subst ha2
      constructor
      · rw [sameSide_iff']; exact sameSide_mid hA'a hB''a
      · rw [sameSide_iff']
        have hA'b : A' ∉ b := fun h => hB''a (by
          have := line_unique hA'O'.symm hO'b h hO'a hA'a
          rw [← this]; exact hB''b)
        have e : X.pt = (1 / 2 : ℝ) • (A'.pt - B''.pt) + B''.pt := by
          show (1 / 2 : ℝ) • (B''.pt - A'.pt) + A'.pt = _; module
        show SameSide b.line X.pt A'.pt
        rw [e]; exact sameSide_mid hB''b hA'b
    have hXD := hint'' X hXS hXint
    rw [side X D' hXS hD'S] at hXD
    set v'' := B''.pt - o with hv''def
    have hfX : f (X.pt - o) = (1 / 2) * f v'' := by
      have : X.pt - o = (1 / 2 : ℝ) • v'' + (1 / 2 : ℝ) • u := by
        show (1 / 2 : ℝ) • (B''.pt - A'.pt) + A'.pt - o = _; rw [hv''def, hudef]; module
      rw [this, map_add, map_smul, map_smul, hfu, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
    rw [hfX, ← hwdef] at hXD
    have hv''S : v'' ∈ S.direction := sub_mem_direction hO'S hB''S
    set y := f v'' / f w with hydef
    have hy : 0 < y := by
      have h1 : 0 < f v'' * f w := by nlinarith
      have : y = f v'' * f w / f w ^ 2 := by rw [hydef]; field_simp
      rw [this]; positivity
    have hZS : (v'' - y • wp) + o ∈ S :=
      add_mem_of_mem_direction (Submodule.sub_mem _ hv''S (Submodule.smul_mem _ _ hwpS)) hO'S
    have hZa : (v'' - y • wp) + o ∈ a'.line.carrier := by
      refine (hf _ hZS).2 ?_
      rw [add_sub_cancel_right, map_sub, map_smul, hfwp, smul_eq_mul, hydef]
      field_simp; ring
    have hline := a'.line.eq_through (pt_ne hA'O').symm hO'a hA'a
    rw [← AffPt.mem_line_iff, hline, AffLine.mem_through_iff] at hZa
    obtain ⟨x, hx⟩ := hZa
    have hdec : v'' = x • u + y • wp := by
      have := add_right_cancel hx
      rw [← hudef] at this
      rw [← this]; abel
    have hGuv'' : G o u v'' = x * Guu := by
      rw [hdec, G_add_right, G_smul_right, G_smul_right, hGuwp, ← hGuudef]; ring
    have hGv''v'' : G o v'' v'' = x ^ 2 * Guu + y ^ 2 * Gpp := by
      rw [hdec]
      simp only [G_add_left, G_add_right, G_smul_left, G_smul_right]
      rw [G_comm o wp u, hGuwp, ← hGuudef, ← hGppdef]; ring
    have hR : 0 < Guu * G o v'' v'' := by
      rw [hGv''v'']; have : 0 < y ^ 2 * Gpp := by positivity
      have : 0 ≤ x ^ 2 * Guu := by positivity
      exact mul_pos hGuu (by linarith)
    set R := Real.sqrt (Guu * G o v'' v'') with hRdef
    have hR0 : 0 < R := Real.sqrt_pos.2 hR
    have hR2 : R ^ 2 = Guu * G o v'' v'' := Real.sq_sqrt hR.le
    have hk : κ * R = x * Guu := by
      unfold kcosV at hang2
      rw [hGuv'', ← hRdef] at hang2
      rw [← hang2]; field_simp
    have hxκ : 0 ≤ x * κ := by
      have : x * κ * Guu = κ ^ 2 * R := by
        calc x * κ * Guu = κ * (x * Guu) := by ring
          _ = κ * (κ * R) := by rw [hk]
          _ = κ ^ 2 * R := by ring
      have h2 : 0 ≤ κ ^ 2 * R := by positivity
      exact nonneg_of_mul_nonneg_left (by linarith) hGuu
    have hsq : (x * nu * sk) ^ 2 = (y * np * κ) ^ 2 := by
      have h1 : κ ^ 2 * R ^ 2 = x ^ 2 * Guu ^ 2 := by rw [← mul_pow, hk]; ring
      rw [hR2, hGv''v''] at h1
      have h2 : κ ^ 2 * (x ^ 2 * Guu + y ^ 2 * Gpp) = x ^ 2 * Guu := by
        apply mul_left_cancel₀ hGuu.ne'; linear_combination h1
      rw [mul_pow, mul_pow, mul_pow, mul_pow, hnu2, hnp2, hsk2]
      linear_combination -h2
    have hpq : x * nu * sk = y * np * κ := by
      apply eq_of_sq_eq_of_mul_nonneg hsq
      have : x * nu * sk * (y * np * κ) = (x * κ) * (y * nu * np * sk) := by ring
      rw [this]; positivity
    have hx' : x = y * np / sk * (κ / nu) := by
      field_simp; linarith
    have hc : v'' = (y * np / sk) • v := by
      rw [hdec, hvdef, hx', smul_add, smul_smul, smul_smul]
      congr 2
      field_simp
    apply ray_eq_of_pos_smul' hB'O' (c := y * np / sk / ε) (by positivity)
    show B''.pt - o = _ • (B'.pt - o)
    rw [hB'v, smul_smul, div_mul_cancel₀ _ hε.ne', ← hc]

/-- **Axioms IV 4–5** in the non-euclidean geometry of space. -/
instance instSpaceAngleCongruence : SpaceAngleCongruence (KPt 3) (KLine 3) (KPlane 3) :=
  { instSpaceOrder, instAngleCongruence with ax_IV4 := axiomIV4LayOffSpace }

/-- **Groups I, II, IV** in the non-euclidean geometry of space. -/
instance instSpaceCongruence : SpaceCongruence (KPt 3) (KLine 3) (KPlane 3) :=
  { instSpaceAngleCongruence, instTriangleCongruence with }

/-! ### The projective transformations of the sphere into itself -/

/-- `√(1 + s²)`. -/
noncomputable def bc (s : ℝ) : ℝ := Real.sqrt (1 + s ^ 2)

theorem bc_sq (s : ℝ) : bc s ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)

theorem bc_pos (s : ℝ) : 0 < bc s := Real.sqrt_pos.2 (by positivity)

theorem bc_neg (s : ℝ) : bc (-s) = bc s := by rw [bc, bc, neg_sq]

theorem abs_lt_bc (s : ℝ) : |s| < bc s := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

/-- The denominator `s x + c` of the boost. -/
noncomputable def bden (s : ℝ) (p : Coord ℝ 3) : ℝ := s * AffPt.toV p 0 + bc s

/-- **The boost** of parameter `s` along the `x`-axis: the projective transformation
`(x : y : z : w) ↦ (c x + s w : y : z : s x + c w)` (`c = √(1 + s²)`), a linear transformation of
homogeneous coordinates preserving `x² + y² + z² - w²`, hence mapping the sphere onto itself. -/
noncomputable def boost (s : ℝ) (p : Coord ℝ 3) : Coord ℝ 3 :=
  (bden s p)⁻¹ • pt3 (bc s * AffPt.toV p 0 + s) (AffPt.toV p 1) (AffPt.toV p 2)

theorem bden_pos (s : ℝ) {p : Coord ℝ 3} (hp : InBall p) : 0 < bden s p := by
  unfold bden
  have h0 : AffPt.toV p 0 ^ 2 < 1 := by
    unfold InBall at hp; rw [ip_eq_coords] at hp
    nlinarith [sq_nonneg (AffPt.toV p 1), sq_nonneg (AffPt.toV p 2)]
  have h1 : |AffPt.toV p 0| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]; exact h0
  have h2 : |s * AffPt.toV p 0| ≤ |s| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg s) h1.le
  have := neg_abs_le (s * AffPt.toV p 0)
  have := abs_lt_bc s
  linarith

theorem boost_eq (s : ℝ) (p : Coord ℝ 3) :
    boost s p = pt3 ((bc s * AffPt.toV p 0 + s) / bden s p) (AffPt.toV p 1 / bden s p)
      (AffPt.toV p 2 / bden s p) := by
  rw [boost, smul_pt3]; congr 1 <;> ring

/-- The key identity: `1 - ⟪B p, B q⟫ = (1 - ⟪p, q⟫) / (D p · D q)`. -/
theorem one_sub_ip_boost (s : ℝ) {p q : Coord ℝ 3} (hp : InBall p) (hq : InBall q) :
    1 - ip (boost s p) (boost s q) = (1 - ip p q) / (bden s p * bden s q) := by
  have hDp := (bden_pos s hp).ne'
  have hDq := (bden_pos s hq).ne'
  have hc := bc_sq s
  have key : bden s p * bden s q - ((bc s * AffPt.toV p 0 + s) * (bc s * AffPt.toV q 0 + s) +
      AffPt.toV p 1 * AffPt.toV q 1 + AffPt.toV p 2 * AffPt.toV q 2) =
      1 - (AffPt.toV p 0 * AffPt.toV q 0 + AffPt.toV p 1 * AffPt.toV q 1 +
        AffPt.toV p 2 * AffPt.toV q 2) := by
    unfold bden; linear_combination (1 - AffPt.toV p 0 * AffPt.toV q 0) * hc
  rw [boost, boost, ip_smul_left, ip_smul_right, ip_pt3, ip_eq_coords p q, ← key]
  field_simp

theorem inBall_boost (s : ℝ) {p : Coord ℝ 3} (hp : InBall p) : InBall (boost s p) := by
  have h := one_sub_ip_boost s hp hp
  have hD := bden_pos s hp
  have h1 : 0 < 1 - ip p p := by unfold InBall at hp; linarith
  unfold InBall
  have : 0 < (1 - ip p p) / (bden s p * bden s p) := by positivity
  linarith

theorem wt_boost (s : ℝ) {p : Coord ℝ 3} (hp : InBall p) : wt (boost s p) = wt p / bden s p := by
  have hD := bden_pos s hp
  rw [wt, one_sub_ip_boost s hp hp, ← sq, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hD.le]
  rfl

/-- **Boosts preserve the invariant `ch`.** -/
theorem ch_boost (s : ℝ) {p q : Coord ℝ 3} (hp : InBall p) (hq : InBall q) :
    ch (boost s p) (boost s q) = ch p q := by
  have hDp := bden_pos s hp
  have hDq := bden_pos s hq
  have := wt_pos hp; have := wt_pos hq
  rw [ch, ch, one_sub_ip_boost s hp hq, wt_boost s hp, wt_boost s hq]
  field_simp

/-- The boost of parameter `-s` undoes the boost of parameter `s`. -/
theorem boost_neg_boost (s : ℝ) {p : Coord ℝ 3} (hp : InBall p) : boost (-s) (boost s p) = p := by
  have hD := bden_pos s hp
  have hc := bc_sq s
  have hc0 := bc_pos s
  have hD' : bden (-s) (boost s p) = (bden s p)⁻¹ := by
    rw [bden, bc_neg, boost_eq, toV_pt3_0]
    unfold bden at *
    field_simp
    linear_combination hc
  have hD0 := hD.ne'
  rw [boost, hD', inv_inv, boost_eq, smul_pt3, bc_neg]
  apply pt3_ext <;> simp only [toV_pt3_0, toV_pt3_1, toV_pt3_2]
  · field_simp; unfold bden; linear_combination (AffPt.toV p 0) * hc
  · field_simp
  · field_simp

/-- The boost moving the point `(r, 0, 0)` (`|r| < 1`) to the centre. -/
theorem boost_to_centre {r : ℝ} (hr : r ^ 2 < 1) :
    boost (-r / Real.sqrt (1 - r ^ 2)) (pt3 r 0 0) = 0 := by
  have hw : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hw2 : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
  have hbc : bc (-r / Real.sqrt (1 - r ^ 2)) = 1 / Real.sqrt (1 - r ^ 2) := by
    rw [bc, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    linear_combination hw2
  rw [boost, toV_pt3_0, toV_pt3_1, toV_pt3_2, hbc, pt3_zero]
  rw [show 1 / Real.sqrt (1 - r ^ 2) * r + -r / Real.sqrt (1 - r ^ 2) = 0 by ring, smul_pt3]
  simp

/-- **The reflection** in the plane through the centre orthogonal to `m` (the identity for
`m = 0`): an orthogonal linear map, hence a projective transformation fixing the sphere. -/
noncomputable def refl (m v : Coord ℝ 3) : Coord ℝ 3 := v - (2 * ip v m / ip m m) • m

theorem ip_refl (m u v : Coord ℝ 3) : ip (refl m u) (refl m v) = ip u v := by
  by_cases hm : m = 0
  · simp [refl, hm]
  · have hmm := ip_self_pos hm
    simp only [refl, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right]
    rw [ip_comm m v]
    field_simp
    ring

theorem refl_zero (m : Coord ℝ 3) : refl m 0 = 0 := by simp [refl]

theorem refl_refl (m v : Coord ℝ 3) : refl m (refl m v) = v := by
  by_cases hm : m = 0
  · simp [refl, hm]
  · have hmm := ip_self_pos hm
    simp only [refl, ip_sub_left, ip_smul_left]
    rw [sub_sub, ← add_smul]
    have : 2 * ip v m / ip m m + 2 * (ip v m - 2 * ip v m / ip m m * ip m m) / ip m m = 0 := by
      field_simp; ring
    rw [this, zero_smul, sub_zero]

/-- The reflection in the plane bisecting `x` and `y` maps `x` to `y` when `|x| = |y|`. -/
theorem refl_map {x y : Coord ℝ 3} (h : ip x x = ip y y) : refl (x - y) x = y := by
  by_cases hm : x - y = 0
  · rw [sub_eq_zero.1 hm, sub_self]; simp [refl]
  · have hmm := ip_self_pos hm
    have e : ip (x - y) (x - y) = 2 * ip x (x - y) := by
      simp only [ip_sub_left, ip_sub_right]; rw [ip_comm y x, ← h]; ring
    have ha : ip x (x - y) ≠ 0 := by intro h0; rw [h0, mul_zero] at e; exact hmm.ne' e
    simp only [refl]
    rw [show 2 * ip x (x - y) / ip (x - y) (x - y) = 1 by
      rw [e, div_self (mul_ne_zero two_ne_zero ha)], one_smul]
    abel

theorem inBall_refl (m : Coord ℝ 3) {p : Coord ℝ 3} (hp : InBall p) : InBall (refl m p) := by
  unfold InBall; rw [ip_refl]; exact hp

theorem ch_refl (m : Coord ℝ 3) (p q : Coord ℝ 3) : ch (refl m p) (refl m q) = ch p q := by
  rw [ch, ch, wt, wt, wt, wt, ip_refl, ip_refl, ip_refl]

/-- **The motions** of the non-euclidean geometry: the composites of boosts and reflections (all
projective transformations of ordinary space mapping the sphere onto itself). -/
inductive IsMotion : (Coord ℝ 3 → Coord ℝ 3) → Prop
  | id : IsMotion id
  | boost (s : ℝ) {f : Coord ℝ 3 → Coord ℝ 3} : IsMotion f → IsMotion (boost s ∘ f)
  | refl (m : Coord ℝ 3) {f : Coord ℝ 3 → Coord ℝ 3} : IsMotion f → IsMotion (refl m ∘ f)

namespace IsMotion

theorem inBall {f : Coord ℝ 3 → Coord ℝ 3} (hf : IsMotion f) {p : Coord ℝ 3} (hp : InBall p) :
    InBall (f p) := by
  induction hf with
  | id => exact hp
  | boost s _ ih => exact inBall_boost s ih
  | refl m _ ih => exact inBall_refl m ih

/-- **Motions preserve the invariant `ch`**, hence the congruence of segments. -/
theorem ch_eq {f : Coord ℝ 3 → Coord ℝ 3} (hf : IsMotion f) {p q : Coord ℝ 3} (hp : InBall p)
    (hq : InBall q) : ch (f p) (f q) = ch p q := by
  induction hf with
  | id => rfl
  | boost s hg ih =>
    simp only [Function.comp]; rw [ch_boost s (hg.inBall hp) (hg.inBall hq), ih]
  | refl m _ ih => simp only [Function.comp]; rw [ch_refl, ih]

/-- **Motions preserve the cosine of angles**, hence the congruence of angles. -/
theorem kcos_eq {f : Coord ℝ 3 → Coord ℝ 3} (hf : IsMotion f) {a o b : Coord ℝ 3} (ha : InBall a)
    (ho : InBall o) (hb : InBall b) : kcos (f a) (f o) (f b) = kcos a o b := by
  rw [kcos_eq_ch (hf.inBall ho) (hf.inBall ha) (hf.inBall hb), kcos_eq_ch ho ha hb,
    hf.ch_eq ho ha, hf.ch_eq ho hb, hf.ch_eq ha hb]

theorem comp {f g : Coord ℝ 3 → Coord ℝ 3} (hf : IsMotion f) (hg : IsMotion g) :
    IsMotion (g ∘ f) := by
  induction hg with
  | id => exact hf
  | boost s _ ih => exact IsMotion.boost s ih
  | refl m _ ih => exact IsMotion.refl m ih

/-- Every motion has an inverse motion (on the ball). -/
theorem exists_inv {f : Coord ℝ 3 → Coord ℝ 3} (hf : IsMotion f) :
    ∃ g, IsMotion g ∧ ∀ p, InBall p → g (f p) = p := by
  induction hf with
  | id => exact ⟨_root_.id, IsMotion.id, fun _ _ => rfl⟩
  | boost s hf' ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    refine ⟨g ∘ Klein.boost (-s), (IsMotion.boost (-s) IsMotion.id).comp hg, fun p hp => ?_⟩
    simp only [Function.comp]
    rw [boost_neg_boost s (hf'.inBall hp), hgf p hp]
  | refl m _ ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    refine ⟨g ∘ Klein.refl m, (IsMotion.refl m IsMotion.id).comp hg, fun p hp => ?_⟩
    simp only [Function.comp]
    rw [refl_refl, hgf p hp]

end IsMotion

/-- **Every point can be moved to the centre** by a motion. -/
theorem exists_motion_to_centre {p : Coord ℝ 3} (hp : InBall p) :
    ∃ f, IsMotion f ∧ f p = 0 := by
  set r := Real.sqrt (ip p p)
  have hr2 : r ^ 2 = ip p p := Real.sq_sqrt (ip_self_nonneg p)
  have hrr : r ^ 2 < 1 := by rw [hr2]; exact hp
  have hpy : ip p p = ip (pt3 r 0 0) (pt3 r 0 0) := by rw [ip_pt3, ← hr2]; ring
  refine ⟨Klein.boost (-r / Real.sqrt (1 - r ^ 2)) ∘ Klein.refl (p - pt3 r 0 0),
    IsMotion.boost _ (IsMotion.refl _ IsMotion.id), ?_⟩
  simp only [Function.comp]
  rw [refl_map hpy, boost_to_centre hrr]

/-- `ch 0 x` determines `|x|`. -/
theorem ip_eq_of_ch_zero {x y : Coord ℝ 3} (hx : InBall x) (hy : InBall y)
    (h : ch 0 x = ch 0 y) : ip x x = ip y y := by
  have hw0 : wt (0 : Coord ℝ 3) = 1 := by simp [wt]
  have e : ∀ z : Coord ℝ 3, ch 0 z = 1 / wt z := by
    intro z; rw [ch, ip_zero_left, sub_zero, hw0, one_mul]
  rw [e, e] at h
  have hwx := wt_pos hx; have hwy := wt_pos hy
  have h' : wt x = wt y := by
    have := congrArg (·⁻¹) h; simpa using this
  have := congrArg (· ^ 2) h'
  simp only [wt_sq hx, wt_sq hy] at this
  linarith

/-- **Congruent segments are carried onto each other by a motion**: if `ch A B = ch A' B'`, a
composite of boosts and reflections maps `A` to `A'` and `B` to `B'`. -/
theorem exists_motion_of_segCong {A B A' B' : Coord ℝ 3} (hA : InBall A) (hB : InBall B)
    (hA' : InBall A') (hB' : InBall B') (h : ch A B = ch A' B') :
    ∃ f, IsMotion f ∧ f A = A' ∧ f B = B' := by
  obtain ⟨m, hm, hmA⟩ := exists_motion_to_centre hA
  obtain ⟨m', hm', hmA'⟩ := exists_motion_to_centre hA'
  obtain ⟨g, hg, hgm⟩ := hm'.exists_inv
  have h1 : ch 0 (m B) = ch A B := by rw [← hmA, hm.ch_eq hA hB]
  have h2 : ch 0 (m' B') = ch A' B' := by rw [← hmA', hm'.ch_eq hA' hB']
  have hx : ch 0 (m B) = ch 0 (m' B') := h1.trans (h.trans h2.symm)
  have hxy := ip_eq_of_ch_zero (hm.inBall hB) (hm'.inBall hB') hx
  refine ⟨g ∘ Klein.refl (m B - m' B') ∘ m, (hm.comp (IsMotion.refl _ IsMotion.id)).comp hg, ?_, ?_⟩
  · simp only [Function.comp]
    rw [hmA, refl_zero, ← hmA', hgm A' hA']
  · simp only [Function.comp]
    rw [refl_map hxy, hgm B' hB']

/-- **Congruence of segments in the non-euclidean geometry is congruence by motions**: `AB ≡ A'B'`
iff a motion maps `A`, `B` to `A'`, `B'`. -/
theorem segCong_iff_motion {A B A' B' : KPt 3} :
    SegCong A B A' B' ↔ ∃ f, IsMotion f ∧ f A.pt = A'.pt ∧ f B.pt = B'.pt := by
  rw [segCong_iff]
  constructor
  · exact exists_motion_of_segCong A.inBall B.inBall A'.inBall B'.inBall
  · rintro ⟨f, hf, h1, h2⟩
    rw [← h1, ← h2, hf.ch_eq A.inBall B.inBall]

/-- **Motions preserve the congruence of angles.** -/
theorem angCong_of_motion {A O B : KPt 3} {f : Coord ℝ 3 → Coord ℝ 3} (hf : IsMotion f)
    {A' O' B' : KPt 3} (hA : f A.pt = A'.pt) (hO : f O.pt = O'.pt) (hB : f B.pt = B'.pt) :
    AngCong A O B A' O' B' := by
  rw [angCong_iff, ← hA, ← hO, ← hB, hf.kcos_eq A.inBall O.inBall B.inBall]

/-- A point of a half-ray spans the same half-ray. -/
theorem ray_eq_of_mem_ray {O A X : KPt 3} (hA : A ≠ O) (hX : X ∈ ray O A) : ray O X = ray O A := by
  rw [mem_ray_iff'] at hX
  obtain ⟨c, hc, e⟩ := (AffPt.mem_ray_iff (pt_ne hA)).1 hX
  exact ray_eq_of_pos_smul' hA hc (by rw [e, add_sub_cancel_right])

/-- **Congruent angles are carried onto each other by a motion**: if `∠AOB ≡ ∠A'O'B'`, a motion
maps `O` to `O'`, `A` to a point of the side `O'A'` and `B` to a point of the side `O'B'`. -/
theorem exists_motion_of_angCong {A O B A' O' B' : KPt 3} (h : ¬Collinear A O B)
    (h' : ¬Collinear A' O' B') (hc : AngCong A O B A' O' B') :
    ∃ f, IsMotion f ∧ f O.pt = O'.pt ∧ (∃ A₁ : KPt 3, A₁ ∈ ray O' A' ∧ f A.pt = A₁.pt) ∧
      ∃ B₁ : KPt 3, B₁ ∈ ray O' B' ∧ f B.pt = B₁.pt := by
  obtain ⟨hAO, hAB, hOB⟩ := ne_of_not_collinear h
  obtain ⟨hAO', -, hOB'⟩ := ne_of_not_collinear h'
  obtain ⟨A₁, ⟨hA₁r, hA₁c⟩, -⟩ := axiomIV1LayOff O A O' A' hAO.symm hAO'.symm
  obtain ⟨B₁, ⟨hB₁r, hB₁c⟩, -⟩ := axiomIV1LayOff O B O' B' hOB hOB'
  rw [segCong_iff] at hA₁c hB₁c
  have hsa : SameAngle A' O' B' A₁ B₁ := by
    unfold SameAngle
    rw [ray_eq_of_mem_ray hAO' hA₁r, ray_eq_of_mem_ray hOB'.symm hB₁r]
  have hk : kcos A₁.pt O'.pt B₁.pt = kcos A.pt O.pt B.pt := by
    rw [kcos_of_sameAngle h' hsa]; exact hc.symm
  rw [kcos_eq_ch O'.inBall A₁.inBall B₁.inBall, kcos_eq_ch O.inBall A.inBall B.inBall, ← hA₁c,
    ← hB₁c] at hk
  have hS := sqrt_ch_pos O.inBall A.inBall B.inBall (pt_ne hAO) (pt_ne hOB).symm
  have hAB₁ : ch A₁.pt B₁.pt = ch A.pt B.pt := by
    have := (div_left_inj₀ hS.ne').1 hk; linarith
  obtain ⟨f₁, hf₁, hf₁O, hf₁A⟩ :=
    exists_motion_of_segCong O.inBall A.inBall O'.inBall A₁.inBall hA₁c
  obtain ⟨m, hm, hmO⟩ := exists_motion_to_centre O'.inBall
  obtain ⟨g, hg, hgm⟩ := hm.exists_inv
  set b := f₁ B.pt
  have hb : InBall b := hf₁.inBall B.inBall
  have hOb : ch O'.pt b = ch O'.pt B₁.pt := by
    rw [show ch O'.pt b = ch (f₁ O.pt) (f₁ B.pt) by rw [hf₁O], hf₁.ch_eq O.inBall B.inBall]
    exact hB₁c
  have hAb : ch A₁.pt b = ch A₁.pt B₁.pt := by
    rw [show ch A₁.pt b = ch (f₁ A.pt) (f₁ B.pt) by rw [hf₁A], hf₁.ch_eq A.inBall B.inBall, hAB₁]
  set a := m A₁.pt
  set x := m b
  set y := m B₁.pt
  have ha : InBall a := hm.inBall A₁.inBall
  have hx : InBall x := hm.inBall hb
  have hy : InBall y := hm.inBall B₁.inBall
  have hxy : ip x x = ip y y := by
    apply ip_eq_of_ch_zero hx hy
    rw [← hmO, hm.ch_eq O'.inBall hb, hm.ch_eq O'.inBall B₁.inBall, hOb]
  have hwxy : wt x = wt y := by rw [wt, wt, hxy]
  have haxy : ip a x = ip a y := by
    have e : ch a x = ch a y := by
      rw [hm.ch_eq A₁.inBall hb, hm.ch_eq A₁.inBall B₁.inBall, hAb]
    rw [ch, ch, hwxy] at e
    have := wt_pos ha; have := wt_pos hy
    have := (div_left_inj₀ (by positivity)).1 e
    linarith
  have hRa : refl (x - y) a = a := by
    have : ip a (x - y) = 0 := by rw [ip_sub_right, haxy, sub_self]
    simp [refl, this]
  refine ⟨g ∘ refl (x - y) ∘ m ∘ f₁,
    ((hf₁.comp hm).comp (IsMotion.refl _ IsMotion.id)).comp hg, ?_, ⟨A₁, hA₁r, ?_⟩, ⟨B₁, hB₁r, ?_⟩⟩
  · simp only [Function.comp]
    rw [hf₁O, hmO, refl_zero, ← hmO, hgm _ O'.inBall]
  · simp only [Function.comp]
    rw [hf₁A, show m A₁.pt = a from rfl, hRa, hgm _ A₁.inBall]
  · simp only [Function.comp]
    rw [show m (f₁ B.pt) = x from rfl, refl_map hxy, hgm _ B₁.inBall]

/-- **Congruence of angles in the non-euclidean geometry is congruence by motions.** -/
theorem angCong_iff_motion {A O B A' O' B' : KPt 3} (h : ¬Collinear A O B)
    (h' : ¬Collinear A' O' B') :
    AngCong A O B A' O' B' ↔ ∃ f, IsMotion f ∧ f O.pt = O'.pt ∧
      (∃ A₁ : KPt 3, A₁ ∈ ray O' A' ∧ f A.pt = A₁.pt) ∧
      ∃ B₁ : KPt 3, B₁ ∈ ray O' B' ∧ f B.pt = B₁.pt := by
  refine ⟨exists_motion_of_angCong h h', ?_⟩
  rintro ⟨f, hf, hO, ⟨A₁, hA₁r, hA₁⟩, ⟨B₁, hB₁r, hB₁⟩⟩
  obtain ⟨-, -, hOB'⟩ := ne_of_not_collinear h'
  obtain ⟨hAO', -, -⟩ := ne_of_not_collinear h'
  have hsa : SameAngle A' O' B' A₁ B₁ := by
    unfold SameAngle
    rw [ray_eq_of_mem_ray hAO' hA₁r, ray_eq_of_mem_ray hOB'.symm hB₁r]
  rw [angCong_iff, ← kcos_of_sameAngle h' hsa, ← hA₁, ← hO, ← hB₁,
    hf.kcos_eq A.inBall O.inBall B.inBall]

end Klein

end HilbertFoundations
