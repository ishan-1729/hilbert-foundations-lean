import HilbertFoundations.NonDesarguesAux2

/-!
# The Moulton plane: congruence of angles (helper for `NonDesargues.lean`)

The angle between two half-rays from `O` is measured by the ordinary angle between their
*directions at `O`*. A ray from `O` along a line `ℓ` has direction `± dirL ℓ O`, where
`dirL (vert c) O = (0, 1)` and `dirL (graph m b) O = (1, slopeAt m O.x)`: the slope of the part of
the broken line on which `O` lies, except that at a point `O` of the `y`-axis (the "corner" of the
broken lines) the slope of the right part `tr m` is used for *both* rays of the line. Off the
`y`-axis this is the ordinary angle of the broken lines at the vertex (`angM_eq_ordinary`); on the
`y`-axis it is the normalization that makes the two rays of every line opposite (the role of
Hilbert's proportional convention, see the Lean reading of `th.33` in `NonDesargues.lean`).

We prove `angCong_wd`, the reflexivity in IV 4, IV 5 and the laying-off clause of IV 4.
-/

namespace HilbertFoundations

namespace Moulton

/-! ### Plane vectors -/

/-- Cross product (determinant) of two plane vectors. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Dot product of two plane vectors. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Euclidean norm of a plane vector. -/
noncomputable def nrm (u : ℝ × ℝ) : ℝ := √(u.1 ^ 2 + u.2 ^ 2)

/-- Cosine of the angle between two plane vectors. -/
noncomputable def cosV (u v : ℝ × ℝ) : ℝ := dot u v / (nrm u * nrm v)

/-- **The ordinary (unsigned) angle** between two nonzero plane vectors, in `[0, π]`. -/
noncomputable def angV (u v : ℝ × ℝ) : ℝ := Real.arccos (cosV u v)

theorem nrm_sq (u : ℝ × ℝ) : nrm u ^ 2 = u.1 ^ 2 + u.2 ^ 2 := Real.sq_sqrt (by positivity)

theorem nrm_pos {u : ℝ × ℝ} (h : u ≠ 0) : 0 < nrm u := by
  apply Real.sqrt_pos.2
  by_cases h1 : u.1 = 0
  · have h2 : u.2 ≠ 0 := fun h2 => h (Prod.ext h1 h2)
    have := mul_self_pos.2 h2; nlinarith [sq_nonneg u.1]
  · have := mul_self_pos.2 h1; nlinarith [sq_nonneg u.2]

theorem lagrange (u v : ℝ × ℝ) :
    dot u v ^ 2 + cross u v ^ 2 = (u.1 ^ 2 + u.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2) := by
  simp only [dot, cross]; ring

theorem cosV_comm (u v : ℝ × ℝ) : cosV u v = cosV v u := by
  simp only [cosV, dot, mul_comm]

theorem cosV_smul_right (u v : ℝ × ℝ) {c : ℝ} (hc : 0 < c) : cosV u (c • v) = cosV u v := by
  simp only [cosV, dot, nrm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : (c * v.1) ^ 2 + (c * v.2) ^ 2 = c ^ 2 * (v.1 ^ 2 + v.2 ^ 2) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  rcases eq_or_ne (√(u.1 ^ 2 + u.2 ^ 2) * √(v.1 ^ 2 + v.2 ^ 2)) 0 with h | h
  · rw [show √(u.1 ^ 2 + u.2 ^ 2) * (c * √(v.1 ^ 2 + v.2 ^ 2))
        = c * (√(u.1 ^ 2 + u.2 ^ 2) * √(v.1 ^ 2 + v.2 ^ 2)) by ring, h]; simp
  · field_simp

theorem cosV_mem {u v : ℝ × ℝ} (hu : u ≠ 0) (hv : v ≠ 0) : -1 ≤ cosV u v ∧ cosV u v ≤ 1 := by
  have h1 := nrm_pos hu
  have h2 := nrm_pos hv
  have hl := lagrange u v
  rw [← nrm_sq, ← nrm_sq] at hl
  have hd : dot u v ^ 2 ≤ (nrm u * nrm v) ^ 2 := by nlinarith [sq_nonneg (cross u v)]
  have hN : 0 < nrm u * nrm v := by positivity
  unfold cosV
  constructor
  · rw [le_div_iff₀ hN]; nlinarith
  · rw [div_le_iff₀ hN]; nlinarith

/-- If `cross u v ≠ 0`, the cosine is strictly between `-1` and `1`. -/
theorem cosV_sq_lt {u v : ℝ × ℝ} (h : cross u v ≠ 0) : cosV u v ^ 2 < 1 := by
  have hu : u ≠ 0 := by rintro rfl; exact h (by simp [cross])
  have hv : v ≠ 0 := by rintro rfl; exact h (by simp [cross])
  have h1 := nrm_pos hu
  have h2 := nrm_pos hv
  have hl := lagrange u v
  rw [← nrm_sq, ← nrm_sq] at hl
  unfold cosV
  rw [div_pow, div_lt_one (by positivity)]
  have : 0 < cross u v ^ 2 := by positivity
  nlinarith

/-- Two vectors making the same angle with `v`, on the same side of `v`, have the same direction
(their cross product vanishes and their dot product is positive). -/
theorem same_dir_of_cosV {v u u' : ℝ × ℝ} (hv : v ≠ 0) (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hc : cosV v u = cosV v u') (hs : 0 < cross v u * cross v u') :
    cross u u' = 0 ∧ 0 < dot u u' := by
  have n0 := nrm_pos hv
  have n1 := nrm_pos hu
  have n2 := nrm_pos hu'
  have hl1 := lagrange v u
  have hl2 := lagrange v u'
  rw [← nrm_sq, ← nrm_sq] at hl1 hl2
  unfold cosV at hc
  rw [div_eq_div_iff (by positivity) (by positivity)] at hc
  -- `α * |u'| = α' * |u|`
  set α := dot v u
  set β := cross v u
  set α' := dot v u'
  set β' := cross v u'
  have hc' : α * nrm u' = α' * nrm u := by
    have : nrm v * (α * nrm u' - α' * nrm u) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hsign : 0 ≤ α * α' := by
    have : α * α' * (nrm u * nrm u') = (α * nrm u') * (α' * nrm u) - 0 := by ring
    have h3 : 0 ≤ (α * nrm u') * (α' * nrm u) := by rw [hc']; exact mul_self_nonneg _
    by_contra hneg; push Not at hneg
    have : α * α' * (nrm u * nrm u') < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  have hsq : α ^ 2 * β' ^ 2 = α' ^ 2 * β ^ 2 := by
    have e1 : α ^ 2 * nrm u' ^ 2 = α' ^ 2 * nrm u ^ 2 := by
      calc α ^ 2 * nrm u' ^ 2 = (α * nrm u') ^ 2 := by ring
        _ = (α' * nrm u) ^ 2 := by rw [hc']
        _ = α' ^ 2 * nrm u ^ 2 := by ring
    have e2 : α ^ 2 * (nrm v ^ 2 * nrm u' ^ 2) = α' ^ 2 * (nrm v ^ 2 * nrm u ^ 2) := by
      rw [show α ^ 2 * (nrm v ^ 2 * nrm u' ^ 2) = nrm v ^ 2 * (α ^ 2 * nrm u' ^ 2) by ring, e1]
      ring
    rw [← hl1, ← hl2] at e2
    linarith
  have hkey : α * β' = α' * β := by
    have hfac : (α * β' - α' * β) * (α * β' + α' * β) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 hfac with h | h
    · linarith
    · -- `α β' = - α' β` with `α α' ≥ 0` and `β β' > 0` forces `α = α' = 0`
      have h4 : α * α' * (β * β') = -(α' * β) ^ 2 := by
        have : α * β' = -(α' * β) := by linarith
        calc α * α' * (β * β') = (α * β') * (α' * β) := by ring
          _ = -(α' * β) * (α' * β) := by rw [this]
          _ = -(α' * β) ^ 2 := by ring
      have h5 : 0 ≤ α * α' * (β * β') := mul_nonneg hsign hs.le
      have h6 : (α' * β) ^ 2 = 0 := by nlinarith [sq_nonneg (α' * β)]
      have h7 : α' * β = 0 := by simpa using h6
      linarith
  -- now express `u`, `u'` in the frame of `v`
  have hN : 0 < v.1 ^ 2 + v.2 ^ 2 := by rw [← nrm_sq]; positivity
  have id1 : (v.1 ^ 2 + v.2 ^ 2) * cross u u' = α * β' - β * α' := by
    simp only [α, β, α', β', dot, cross]; ring
  have id2 : (v.1 ^ 2 + v.2 ^ 2) * dot u u' = α * α' + β * β' := by
    simp only [α, β, α', β', dot, cross]; ring
  constructor
  · have : (v.1 ^ 2 + v.2 ^ 2) * cross u u' = 0 := by rw [id1]; linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  · have : 0 < (v.1 ^ 2 + v.2 ^ 2) * dot u u' := by rw [id2]; nlinarith
    exact pos_of_mul_pos_right this hN.le

/-! ### Directions of rays -/

/-- The slope used for the direction of the broken line `graph m _` at a point of abscissa `x`:
the slope of the left part for `x < 0`, of the right part for `x ≥ 0`. -/
noncomputable def slopeAt (m x : ℝ) : ℝ := if x < 0 then m else tr m

theorem slopeAt_strictMono (x : ℝ) : StrictMono fun m => slopeAt m x := by
  intro a b h; simp only [slopeAt]; split_ifs
  · exact h
  · exact tr_strictMono h

/-- **Direction of a line at a point** (the positive direction, that of increasing parameter). -/
noncomputable def dirL : Ln → Pt → ℝ × ℝ
  | .vert _, _ => (0, 1)
  | .graph m _, O => (1, slopeAt m O.x)

/-- **Direction at `O` of the ray `OA`** along the line `ℓ`. -/
noncomputable def rdirL (ℓ : Ln) (O A : Pt) : ℝ × ℝ :=
  if lam ℓ O < lam ℓ A then dirL ℓ O else -dirL ℓ O

/-- **Direction at `O` of the half-ray `OA`.** -/
noncomputable def rdir (O A : Pt) : ℝ × ℝ := rdirL (through O A) O A

theorem rdir_eq {ℓ : Ln} {O A : Pt} (hO : O ∈ ℓ) (hA : A ∈ ℓ) (h : O ≠ A) :
    rdir O A = rdirL ℓ O A := by
  rw [rdir, eq_through h hO hA]

theorem rdirL_cases (ℓ : Ln) (O A : Pt) : rdirL ℓ O A = dirL ℓ O ∨ rdirL ℓ O A = -dirL ℓ O := by
  unfold rdirL; split_ifs <;> simp

theorem dirL_ne_zero (ℓ : Ln) (O : Pt) : dirL ℓ O ≠ 0 := by
  cases ℓ <;> simp [dirL, Prod.ext_iff]

theorem rdirL_ne_zero (ℓ : Ln) (O A : Pt) : rdirL ℓ O A ≠ 0 := by
  rcases rdirL_cases ℓ O A with h | h <;> rw [h]
  · exact dirL_ne_zero ℓ O
  · exact neg_ne_zero.2 (dirL_ne_zero ℓ O)

theorem rdir_ne_zero (O A : Pt) : rdir O A ≠ 0 := rdirL_ne_zero _ _ _

theorem cross_neg_left (u v : ℝ × ℝ) : cross (-u) v = -cross u v := by
  simp [cross]; ring

theorem cross_neg_right (u v : ℝ × ℝ) : cross u (-v) = -cross u v := by
  simp [cross]; ring

theorem cross_self (u : ℝ × ℝ) : cross u u = 0 := by simp [cross]; ring

theorem cross_smul_right (u v : ℝ × ℝ) (c : ℝ) : cross u (c • v) = c * cross u v := by
  simp [cross]; ring

/-- Two lines through `O` with parallel directions at `O` coincide. -/
theorem eq_of_cross_dirL {ℓ ℓ' : Ln} {O : Pt} (h : O ∈ ℓ) (h' : O ∈ ℓ')
    (hc : cross (dirL ℓ O) (dirL ℓ' O) = 0) : ℓ = ℓ' := by
  cases ℓ with
  | vert c =>
    cases ℓ' with
    | vert c' => simp at h h'; rw [← h, ← h']
    | graph m' b' => simp [dirL, cross] at hc
  | graph m b =>
    cases ℓ' with
    | vert c' => simp [dirL, cross] at hc
    | graph m' b' =>
      simp only [dirL, cross] at hc
      have hs : slopeAt m O.x = slopeAt m' O.x := by linarith
      have hm : m = m' := (slopeAt_strictMono O.x).injective hs
      subst hm
      simp at h h'
      have : b = b' := by linarith
      rw [this]

/-- If the rays `OA`, `OB` have parallel directions, `A`, `O`, `B` are collinear. -/
theorem collinear_of_cross_rdir {A O B : Pt} (h : cross (rdir O A) (rdir O B) = 0) :
    Collinear A O B := by
  by_cases hA : A = O
  · subst hA; exact ⟨through A B, left_mem_through A B, left_mem_through A B,
      right_mem_through A B⟩
  by_cases hB : B = O
  · subst hB; exact ⟨through A B, left_mem_through A B, right_mem_through A B,
      right_mem_through A B⟩
  have hc : cross (dirL (through O A) O) (dirL (through O B) O) = 0 := by
    unfold rdir at h
    rcases rdirL_cases (through O A) O A with h1 | h1 <;>
      rcases rdirL_cases (through O B) O B with h2 | h2 <;>
      rw [h1, h2] at h <;>
      (try simp only [cross_neg_left, cross_neg_right, neg_neg, neg_eq_zero] at h) <;>
      exact h
  have := eq_of_cross_dirL (left_mem_through O A) (left_mem_through O B) hc
  refine ⟨through O A, right_mem_through O A, left_mem_through O A, ?_⟩
  rw [this]; exact right_mem_through O B

theorem cross_rdir_ne_zero {A O B : Pt} (h : ¬Collinear A O B) : cross (rdir O A) (rdir O B) ≠ 0 :=
  fun hc => h (collinear_of_cross_rdir hc)

/-- **Half-rays and directions**: `Z` lies on the half-ray `OX` iff `Z ≠ O` and the ray `OZ` has
the direction of `OX`. -/
theorem sameSidePt_iff_rdir {O X Z : Pt} (hOX : O ≠ X) :
    SameSidePt O X Z ↔ Z ≠ O ∧ rdir O Z = rdir O X := by
  have hO := left_mem_through O X
  have hX := right_mem_through O X
  set ℓ := through O X
  rw [sameSidePt_iff hO hX hOX]
  constructor
  · rintro ⟨hZ, hZO, hpos⟩
    refine ⟨hZO, ?_⟩
    rw [rdir_eq hO hZ (Ne.symm hZO), rdir_eq hO hX hOX]
    unfold rdirL
    split_ifs with h1 h2 h2
    · rfl
    · push Not at h2; have := lam_ne hX hO (Ne.symm hOX)
      have h2' : lam ℓ X < lam ℓ O := lt_of_le_of_ne h2 this
      nlinarith
    · push Not at h1; have := lam_ne hZ hO hZO
      have h1' : lam ℓ Z < lam ℓ O := lt_of_le_of_ne h1 this
      nlinarith
    · rfl
  · rintro ⟨hZO, he⟩
    have hZ' := right_mem_through O Z
    have hO' := left_mem_through O Z
    have hc : cross (dirL ℓ O) (dirL (through O Z) O) = 0 := by
      have he' := he
      rw [rdir_eq hO' hZ' (Ne.symm hZO), rdir_eq hO hX hOX] at he'
      rcases rdirL_cases ℓ O X with h1 | h1 <;>
        rcases rdirL_cases (through O Z) O Z with h2 | h2 <;> rw [h1, h2] at he'
      · rw [he', cross_self]
      · rw [← neg_neg (dirL (through O Z) O), he', cross_neg_right, cross_self, neg_zero]
      · rw [he', cross_neg_right, cross_self, neg_zero]
      · rw [neg_inj.1 he', cross_self]
    have hl := eq_of_cross_dirL hO hO' hc
    have hZ : Z ∈ ℓ := by rw [hl]; exact hZ'
    refine ⟨hZ, hZO, ?_⟩
    rw [rdir_eq hO hZ (Ne.symm hZO), rdir_eq hO hX hOX] at he
    have hd := dirL_ne_zero ℓ O
    have hZl := lam_ne hZ hO hZO
    have hXl := lam_ne hX hO (Ne.symm hOX)
    unfold rdirL at he
    split_ifs at he with h1 h2 h2
    · nlinarith
    · exact absurd (by
        have : (2 : ℝ) • dirL ℓ O = 0 := by rw [two_smul]; nth_rewrite 1 [he]; simp
        simpa using this) hd
    · exact absurd (by
        have : (2 : ℝ) • dirL ℓ O = 0 := by rw [two_smul]; nth_rewrite 2 [← he]; simp
        simpa using this) hd
    · push Not at h1 h2
      have h1' := lt_of_le_of_ne h1 hZl
      have h2' := lt_of_le_of_ne h2 hXl
      nlinarith

/-- A ray determines its direction. -/
theorem rdir_eq_of_ray_eq {O A C : Pt} (hA : A ≠ O) (h : ray O A = ray O C) :
    C ≠ O ∧ rdir O A = rdir O C := by
  have hmem : A ∈ ray O A := (sameSidePt_iff_rdir (Ne.symm hA)).2 ⟨hA, rfl⟩
  rw [h] at hmem
  have hC : C ≠ O := hmem.1
  exact ⟨hC, ((sameSidePt_iff_rdir (Ne.symm hC)).1 hmem).2⟩

/-- Directions of rays are normalized: `(0, ±1)` or `±(1, k)`. -/
def NF (v : ℝ × ℝ) : Prop := (v.1 = 0 ∧ (v.2 = 1 ∨ v.2 = -1)) ∨ v.1 = 1 ∨ v.1 = -1

theorem nf_rdir (O A : Pt) : NF (rdir O A) := by
  unfold rdir
  rcases rdirL_cases (through O A) O A with h | h <;> rw [h] <;>
    cases through O A <;> simp [NF, dirL]

theorem eq_of_nf {u v : ℝ × ℝ} (hu : NF u) (hv : NF v) (hc : cross u v = 0) (hd : 0 < dot u v) :
    u = v := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  simp only [NF, cross, dot] at *
  rcases hu with ⟨rfl, rfl | rfl⟩ | rfl | rfl <;> rcases hv with ⟨rfl, rfl | rfl⟩ | rfl | rfl <;>
    simp only [Prod.mk.injEq, true_and] <;>
    first
    | linarith
    | (exfalso
       have e : v2 = -u2 := by linarith
       rw [e] at hd; nlinarith [sq_nonneg u2])

/-! ### Sides of a line through the vertex -/

/-- **The side of a line and the direction of a ray** (the key lemma): if `O` lies on `a` and
`X` does not, then `X` lies on the side of `a` given by the sign of the cross product of the
direction of `a` at `O` with the direction of the ray `OX`. -/
theorem side_sign {a : Ln} {O X : Pt} (hO : O ∈ a) (hX : X ∉ a) :
    0 < sd a X * cross (dirL a O) (rdir O X) := by
  have hOX : O ≠ X := fun e => hX (e ▸ hO)
  have hOn := left_mem_through O X
  have hXn := right_mem_through O X
  rw [rdir]
  generalize through O X = n at hOn hXn
  cases a with
  | vert c =>
    simp only [mem_vert] at hO hX
    cases n with
    | vert c' => simp at hOn hXn; exact (hX (by rw [hXn, ← hOn, hO])).elim
    | graph m b =>
      have hx : O.x ≠ X.x := by rw [hO]; exact Ne.symm hX
      simp only [rdirL, sd, dirL]
      split_ifs with h
      · rw [lam_graph_lt] at h; simp [cross]; linarith
      · rw [lam_graph_lt] at h; push Not at h
        have := lt_of_le_of_ne h (Ne.symm hx); simp [cross]; linarith
  | graph m b =>
    simp only [mem_graph] at hO hX
    cases n with
    | vert c' =>
      simp only [mem_vert] at hOn hXn
      have hx : X.x = O.x := by rw [hOn, hXn]
      have hy : X.y ≠ O.y := fun e => hOX (Pt.ext hx.symm e.symm)
      simp only [rdirL, sd, dirL]
      rw [hx]
      split_ifs with h
      · change O.y < X.y at h; simp [cross]; linarith
      · change ¬O.y < X.y at h; push Not at h
        have := lt_of_le_of_ne h hy; simp [cross]; linarith
    | graph m' b' =>
      simp only [mem_graph] at hOn hXn
      have hx : O.x ≠ X.x := fun e => hOX (Pt.ext e (by rw [hOn, hXn, e]))
      have hm : m ≠ m' := by
        rintro rfl
        have : b = b' := by linarith
        exact hX (by rw [hXn, this])
      have hsd : sd (.graph m b) X = (ht m' X.x - ht m X.x) - (ht m' O.x - ht m O.x) := by
        simp only [sd]; linarith
      simp only [rdirL, lam_graph_lt, dirL]
      rw [hsd]
      rcases lt_or_gt_of_ne hm with hmm | hmm
      · have hk := slopeAt_strictMono O.x hmm
        have hg := ht_sub_strictMono hmm
        simp only at hk
        split_ifs with h
        · have := hg h; simp only at this; simp [cross]; nlinarith
        · push Not at h
          have := hg (lt_of_le_of_ne h (Ne.symm hx)); simp only at this; simp [cross]; nlinarith
      · have hk := slopeAt_strictMono O.x hmm
        have hg := ht_sub_strictMono hmm
        simp only at hk
        split_ifs with h
        · have := hg h; simp only at this; simp [cross]; nlinarith
        · push Not at h
          have := hg (lt_of_le_of_ne h (Ne.symm hx)); simp only at this; simp [cross]; nlinarith

theorem sameSide_trans {ℓ : Ln} {X Y Z : Pt} (h1 : SameSide ℓ X Y) (h2 : SameSide ℓ Y Z) :
    SameSide ℓ X Z := by
  rw [sameSide_iff] at *
  have hY : sd ℓ Y ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have : 0 < sd ℓ X * sd ℓ Z * (sd ℓ Y * sd ℓ Y) := by nlinarith
  have hY2 : 0 < sd ℓ Y * sd ℓ Y := mul_self_pos.2 hY
  exact pos_of_mul_pos_left this hY2.le

/-- Sides of a line through `O`, read off the directions at `O`. -/
theorem sameSide_iff_cross {a : Ln} {O X Y : Pt} (hO : O ∈ a) (hX : X ∉ a) (hY : Y ∉ a) :
    SameSide a X Y ↔ 0 < cross (dirL a O) (rdir O X) * cross (dirL a O) (rdir O Y) := by
  rw [sameSide_iff]
  have h1 := side_sign hO hX
  have h2 := side_sign hO hY
  constructor
  · intro h
    have : 0 < sd a X * sd a Y * (cross (dirL a O) (rdir O X) * cross (dirL a O) (rdir O Y)) := by
      nlinarith
    exact pos_of_mul_pos_right this h.le
  · intro h
    have : 0 < sd a X * sd a Y * (cross (dirL a O) (rdir O X) * cross (dirL a O) (rdir O Y)) := by
      nlinarith
    exact pos_of_mul_pos_left this h.le

/-- If `P` lies on `ℓ` and `Q` does not, every point between them is on the side of `Q`. -/
theorem sameSide_of_btw {ℓ : Ln} {P Q M : Pt} (hP : P ∈ ℓ) (hQ : Q ∉ ℓ) (h : Btw P M Q) :
    SameSide ℓ M Q := by
  obtain ⟨n, hPn, hMn, hQn, hs⟩ := h
  have hPM : P ≠ M := (show Btw P M Q from ⟨n, hPn, hMn, hQn, hs⟩).ne12
  have hM : M ∉ ℓ := by
    intro hM
    have := eq_of_mem hPM hP hM hPn hMn
    exact hQ (this ▸ hQn)
  rw [sameSide_iff]
  have eP : sd ℓ (gam n (lam n P)) = 0 := by rw [sd_gam_lam hPn]; exact sd_eq_zero_iff.2 hP
  have eQ : sd ℓ (gam n (lam n Q)) = sd ℓ Q := sd_gam_lam hQn
  have eM : sd ℓ (gam n (lam n M)) = sd ℓ M := sd_gam_lam hMn
  have hQ0 := sd_ne_zero hQ
  have hM0 := sd_ne_zero hM
  rcases sd_gam_mono ℓ n with hm | hm <;> rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 : sd ℓ (gam n (lam n P)) ≤ sd ℓ (gam n (lam n M)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n M)) ≤ sd ℓ (gam n (lam n Q)) := hm h2.le
    rw [eP, eM] at a1; rw [eM, eQ] at a2
    have := lt_of_le_of_ne a1 (Ne.symm hM0); nlinarith
  · have a1 : sd ℓ (gam n (lam n Q)) ≤ sd ℓ (gam n (lam n M)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n M)) ≤ sd ℓ (gam n (lam n P)) := hm h2.le
    rw [eQ, eM] at a1; rw [eM, eP] at a2
    have := lt_of_le_of_ne a2 hM0; nlinarith
  · have a1 : sd ℓ (gam n (lam n M)) ≤ sd ℓ (gam n (lam n P)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n Q)) ≤ sd ℓ (gam n (lam n M)) := hm h2.le
    rw [eP, eM] at a1; rw [eM, eQ] at a2
    have := lt_of_le_of_ne a1 hM0; nlinarith
  · have a1 : sd ℓ (gam n (lam n M)) ≤ sd ℓ (gam n (lam n Q)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n P)) ≤ sd ℓ (gam n (lam n M)) := hm h2.le
    rw [eM, eQ] at a1; rw [eP, eM] at a2
    have := lt_of_le_of_ne a2 (Ne.symm hM0); nlinarith

/-! ### Every direction is the direction of a ray -/

theorem exists_rdir (O : Pt) {w : ℝ × ℝ} (hw : w ≠ 0) :
    ∃ X, X ≠ O ∧ ∃ c : ℝ, 0 < c ∧ rdir O X = c • w := by
  by_cases h1 : w.1 = 0
  · have h2 : w.2 ≠ 0 := fun h2 => hw (Prod.ext h1 h2)
    set X : Pt := ⟨O.x, O.y + w.2⟩
    have hX : X ≠ O := fun e => h2 (by have := congrArg Pt.y e; simp [X] at this; exact this)
    refine ⟨X, hX, 1 / |w.2|, by positivity, ?_⟩
    have hO : O ∈ Ln.vert O.x := rfl
    have hXm : X ∈ Ln.vert O.x := rfl
    rw [rdir_eq hO hXm (Ne.symm hX)]
    simp only [rdirL, dirL]
    split_ifs with h
    · change O.y < O.y + w.2 at h
      rw [abs_of_pos (by linarith)]
      ext <;> simp [h1]; field_simp
    · change ¬O.y < O.y + w.2 at h
      rw [abs_of_neg (lt_of_le_of_ne (by linarith) h2)]
      ext <;> simp [h1]; field_simp
  · set k := w.2 / w.1
    set m := if O.x < 0 then k else trInv k
    have hk : slopeAt m O.x = k := by
      simp only [slopeAt, m]; split_ifs with h
      · rfl
      · exact tr_trInv k
    set ℓ : Ln := .graph m (O.y - ht m O.x)
    set X : Pt := ⟨O.x + w.1, O.y - ht m O.x + ht m (O.x + w.1)⟩
    have hO : O ∈ ℓ := by simp [ℓ]
    have hXm : X ∈ ℓ := by simp [ℓ, X]
    have hX : X ≠ O := fun e => h1 (by have := congrArg Pt.x e; simp [X] at this; exact this)
    refine ⟨X, hX, 1 / |w.1|, by positivity, ?_⟩
    rw [rdir_eq hO hXm (Ne.symm hX)]
    simp only [rdirL, ℓ, dirL, hk]
    split_ifs with h
    · rw [lam_graph_lt] at h; simp only [X] at h
      rw [abs_of_pos (by linarith)]
      ext <;> simp [k] <;> field_simp
    · rw [lam_graph_lt] at h; simp only [X] at h
      rw [abs_of_neg (lt_of_le_of_ne (by linarith) h1)]
      ext <;> simp [k] <;> field_simp

/-! ### Congruence of angles: IV 4–5 -/

/-- **The measure of the angle `∠AOB`**: the ordinary angle between the directions at `O` of the
half-rays `OA`, `OB`. -/
noncomputable def angM (A O B : Pt) : ℝ := angV (rdir O A) (rdir O B)

/-- **Congruence of angles**: equal measure. -/
noncomputable instance instHasAngCong : HasAngCong Pt :=
  ⟨fun A O B A' O' B' => angM A O B = angM A' O' B'⟩

theorem angCong_iff {A O B A' O' B' : Pt} : AngCong A O B A' O' B' ↔ angM A O B = angM A' O' B' :=
  Iff.rfl

theorem angM_comm (A O B : Pt) : angM A O B = angM B O A := by
  simp only [angM, angV, cosV_comm]

theorem angM_eq_iff {A O B A' O' B' : Pt} :
    angM A O B = angM A' O' B' ↔ cosV (rdir O A) (rdir O B) = cosV (rdir O' A') (rdir O' B') := by
  have h1 := cosV_mem (rdir_ne_zero O A) (rdir_ne_zero O B)
  have h2 := cosV_mem (rdir_ne_zero O' A') (rdir_ne_zero O' B')
  exact Real.arccos_inj h1.1 h1.2 h2.1 h2.2

theorem angM_of_sameAngle {A O B C D : Pt} (hAO : A ≠ O) (hBO : B ≠ O)
    (h : SameAngle A O B C D) : angM A O B = angM C O D := by
  unfold SameAngle at h
  rcases Set.pair_eq_pair_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [angM, (rdir_eq_of_ray_eq hAO h1).2, (rdir_eq_of_ray_eq hBO h2).2]
  · rw [angM_comm C O D]
    simp only [angM, (rdir_eq_of_ray_eq hAO h1).2, (rdir_eq_of_ray_eq hBO h2).2]

theorem ne_of_not_collinear {A O B : Pt} (h : ¬Collinear A O B) : A ≠ O ∧ B ≠ O := by
  constructor
  · rintro rfl; exact h ⟨through A B, left_mem_through A B, left_mem_through A B,
      right_mem_through A B⟩
  · rintro rfl; exact h ⟨through A B, left_mem_through A B, right_mem_through A B,
      right_mem_through A B⟩

/-- The plane-free part of IV 4–5 holds in the Moulton plane. -/
instance instAngleCongruence : AngleCongruence Pt Ln where
  angCong_wd A O B C D A' O' B' C' D' h h' hs hs' hc := by
    rw [angCong_iff] at *
    have e1 := angM_of_sameAngle (ne_of_not_collinear h).1 (ne_of_not_collinear h).2 hs
    have e2 := angM_of_sameAngle (ne_of_not_collinear h').1 (ne_of_not_collinear h').2 hs'
    rw [← e1, ← e2, hc]
  ax_IV4_refl _ _ _ _ := rfl
  ax_IV5 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 := by
    rw [angCong_iff] at *; rw [← h1, ← h2]

/-- An interior point of an angle `∠A'O'B''` with `A'` on `a'`: a point between `A'` and `B''`. -/
theorem exists_interior {a' : Ln} {O' A' B'' : Pt} (hO' : O' ∈ a') (hA' : A' ∈ a') (hAO : A' ≠ O')
    (hB'' : B'' ∉ a') : ∃ M, M ∈ Interior A' O' B'' ∧ SameSide a' M B'' := by
  have hAB : A' ≠ B'' := fun e => hB'' (e ▸ hA')
  obtain ⟨M, hM⟩ := exists_between (Line := Ln) hAB
  have hM' : Btw A' M B'' := hM
  refine ⟨M, ?_, sameSide_of_btw hA' hB'' hM'⟩
  intro a b ha1 ha2 hb1 hb2
  have ha : a = a' := eq_of_mem (Ne.symm hAO) ha1 ha2 hO' hA'
  subst ha
  refine ⟨sameSide_of_btw ha2 hB'' hM', ?_⟩
  have hAb : A' ∉ b := by
    intro hAb
    have := eq_of_mem (Ne.symm hAO) hb1 hAb hO' hA'
    exact hB'' (this ▸ hb2)
  exact sameSide_of_btw hb2 hAb hM'.symm

/-- **Axioms IV 4–5 of plane geometry** hold in the Moulton plane. -/
instance instPlaneAngleCongruence : PlaneAngleCongruence Pt Ln where
  ax_IV4 A O B a' O' A' D' hcol hO' hA' hAO hD' := by
    set v := rdir O' A'
    set d0 := dirL a' O'
    have hv : v = d0 ∨ v = -d0 := by
      rw [show v = rdirL a' O' A' from rdir_eq hO' hA' (Ne.symm hAO)]; exact rdirL_cases _ _ _
    have hv0 : v ≠ 0 := rdir_ne_zero _ _
    set κ := cosV (rdir O A) (rdir O B)
    have hκ : κ ^ 2 < 1 := cosV_sq_lt (cross_rdir_ne_zero hcol)
    set Jv : ℝ × ℝ := (-v.2, v.1)
    have hN : 0 < v.1 ^ 2 + v.2 ^ 2 := by rw [← nrm_sq]; have := nrm_pos hv0; positivity
    have hcJ : cross d0 Jv ≠ 0 := by
      rcases hv with h | h
      · rw [← h]; simp only [cross, Jv]; nlinarith
      · rw [show d0 = -v by rw [h, neg_neg], cross_neg_left]; simp only [cross, Jv]; nlinarith
    have hcv : cross d0 v = 0 := by
      rcases hv with h | h <;> rw [h]
      · exact cross_self _
      · rw [cross_neg_right, cross_self, neg_zero]
    set ρ := cross d0 (rdir O' D')
    set s := √(1 - κ ^ 2)
    have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hs2 : s ^ 2 = 1 - κ ^ 2 := Real.sq_sqrt (by linarith)
    set μ := if 0 < ρ * cross d0 Jv then s else -s
    have hμ2 : μ ^ 2 = 1 - κ ^ 2 := by simp only [μ]; split_ifs <;> simp [hs2]
    set w : ℝ × ℝ := κ • v + μ • Jv
    have hcw : cross d0 w = μ * cross d0 Jv := by
      have : cross d0 w = κ * cross d0 v + μ * cross d0 Jv := by
        simp only [w, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]; ring
      rw [this, hcv]; ring
    have hρ : ρ ≠ 0 := by
      have := side_sign hO' hD'; intro h
      have h' : cross (dirL a' O') (rdir O' D') = 0 := h
      rw [h'] at this; simp at this
    have hside : 0 < cross d0 w * ρ := by
      rw [hcw]; simp only [μ]; split_ifs with h
      · nlinarith
      · push Not at h
        have : ρ * cross d0 Jv ≠ 0 := mul_ne_zero hρ hcJ
        have h' := lt_of_le_of_ne h this
        nlinarith
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hside; simp [cross] at hside
    have hcosw : cosV v w = κ := by
      have hnw : nrm w = nrm v := by
        simp only [nrm, w, Jv, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
        congr 1
        have : (κ * v.1 + μ * -v.2) ^ 2 + (κ * v.2 + μ * v.1) ^ 2
            = (κ ^ 2 + μ ^ 2) * (v.1 ^ 2 + v.2 ^ 2) := by ring
        rw [this, hμ2]; ring
      unfold cosV
      rw [hnw, ← sq, nrm_sq]
      simp only [dot, w, Jv, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      field_simp; ring
    obtain ⟨B', hBO, c, hc, hBw⟩ := exists_rdir O' hw0
    have hB'side : 0 < cross d0 (rdir O' B') * ρ := by
      rw [hBw, cross_smul_right]; nlinarith
    have hB' : B' ∉ a' := by
      intro hB
      have : cross d0 (rdir O' B') = 0 := by
        rw [rdir_eq hO' hB (Ne.symm hBO)]
        rcases rdirL_cases a' O' B' with h | h <;> rw [h]
        · exact cross_self _
        · rw [cross_neg_right, cross_self, neg_zero]
      rw [this] at hB'side; simp at hB'side
    have hBD : SameSide a' B' D' := (sameSide_iff_cross hO' hB' hD').2 hB'side
    have hcosB : cosV v (rdir O' B') = κ := by rw [hBw, cosV_smul_right _ _ hc, hcosw]
    refine ⟨B', hB', ?_, ?_, ?_⟩
    · rw [angCong_iff, angM_eq_iff]; exact hcosB.symm
    · intro X hX
      have := (hX a' (through O' B') hO' hA' (left_mem_through _ _) (right_mem_through _ _)).1
      exact sameSide_trans this hBD
    · intro B'' hB'' hcong hint
      have hBO'' : B'' ≠ O' := fun e => hB'' (e ▸ hO')
      rw [angCong_iff, angM_eq_iff] at hcong
      obtain ⟨M, hMint, hMB⟩ := exists_interior hO' hA' hAO hB''
      have hB''D : SameSide a' B'' D' := by
        have h1 := hint M hMint
        rw [sameSide_iff] at h1 hMB ⊢
        have hM0 : sd a' M ≠ 0 := fun e => by rw [e] at h1; simp at h1
        have : 0 < sd a' B'' * sd a' D' * (sd a' M * sd a' M) := by nlinarith
        exact pos_of_mul_pos_left this (mul_self_nonneg _)
      have hc'' := (sameSide_iff_cross hO' hB'' hD').1 hB''D
      -- both `B'` and `B''` lie on the side of `D'`, with the same angle to `v`
      have hboth : 0 < cross v (rdir O' B') * cross v (rdir O' B'') := by
        have : 0 < cross d0 (rdir O' B') * cross d0 (rdir O' B'') := by
          have := mul_pos hB'side hc''
          have hρ2 : 0 < ρ * ρ := mul_self_pos.2 hρ
          have : 0 < cross d0 (rdir O' B') * cross d0 (rdir O' B'') * (ρ * ρ) := by nlinarith
          exact pos_of_mul_pos_left this hρ2.le
        rcases hv with h | h <;> rw [h]
        · exact this
        · rw [cross_neg_left, cross_neg_left]; linarith
      have hcos'' : cosV v (rdir O' B') = cosV v (rdir O' B'') := by rw [hcosB, ← hcong]
      obtain ⟨hcr, hdt⟩ := same_dir_of_cosV hv0 (rdir_ne_zero _ _) (rdir_ne_zero _ _) hcos'' hboth
      have heq := eq_of_nf (nf_rdir O' B') (nf_rdir O' B'') hcr hdt
      ext Z
      change SameSidePt O' B'' Z ↔ SameSidePt O' B' Z
      rw [sameSidePt_iff_rdir (Ne.symm hBO''), sameSidePt_iff_rdir (Ne.symm hBO), heq]

/-! ### The angle measure is the ordinary angle off the `y`-axis -/

/-- The vector from `O` to `A`. -/
def vec (O A : Pt) : ℝ × ℝ := (A.x - O.x, A.y - O.y)

/-- On the part of the line through `O` on which `O` lies (and in the direction away from the
corner when `O` is on the `y`-axis), the direction of the ray `OA` is that of the ordinary
segment `OA`. -/
theorem rdir_ordinary {O A : Pt} (hOA : O ≠ A)
    (hpiece : (O.x < 0 ∧ A.x ≤ 0) ∨ (0 ≤ O.x ∧ 0 ≤ A.x)) :
    ∃ c : ℝ, 0 < c ∧ vec O A = c • rdir O A := by
  have hO := left_mem_through O A
  have hA := right_mem_through O A
  rw [rdir]
  generalize through O A = n at hO hA
  cases n with
  | vert c' =>
    simp only [mem_vert] at hO hA
    have hy : O.y ≠ A.y := fun e => hOA (Pt.ext (by rw [hO, hA]) e)
    simp only [rdirL, dirL]
    split_ifs with h
    · change O.y < A.y at h; refine ⟨A.y - O.y, by linarith, ?_⟩
      ext <;> simp [vec, hO, hA]
    · change ¬O.y < A.y at h; push Not at h
      refine ⟨O.y - A.y, by have := lt_of_le_of_ne h (Ne.symm hy); linarith, ?_⟩
      ext <;> simp [vec, hO, hA]
  | graph m b =>
    simp only [mem_graph] at hO hA
    have hx : O.x ≠ A.x := fun e => hOA (Pt.ext e (by rw [hO, hA, e]))
    have hdy : A.y - O.y = slopeAt m O.x * (A.x - O.x) := by
      rw [hA, hO]
      rcases hpiece with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [ht_of_nonpos h2, ht_of_nonpos h1.le]; simp [slopeAt, h1]; ring
      · rw [ht_of_nonneg h2, ht_of_nonneg h1]; simp [slopeAt, not_lt.2 h1]; ring
    simp only [rdirL, dirL]
    split_ifs with h
    · rw [lam_graph_lt] at h; refine ⟨A.x - O.x, by linarith, ?_⟩
      ext <;> simp [vec, hdy]; ring
    · rw [lam_graph_lt] at h; push Not at h
      refine ⟨O.x - A.x, by have := lt_of_le_of_ne h (Ne.symm hx); linarith, ?_⟩
      ext <;> simp [vec, hdy]; ring

theorem cosV_smul_left (u v : ℝ × ℝ) {c : ℝ} (hc : 0 < c) : cosV (c • u) v = cosV u v := by
  rw [cosV_comm, cosV_smul_right _ _ hc, cosV_comm]

/-- **Off the corner, angles are ordinary angles**: if `A` and `B` lie on the same part of their
lines through `O` as `O` (in particular, for `O` off the `y`-axis, near `O`), the measure of
`∠AOB` is the ordinary angle `∠AOB` of the plane. -/
theorem angM_eq_ordinary {A O B : Pt} (hA : O ≠ A) (hB : O ≠ B)
    (hpA : (O.x < 0 ∧ A.x ≤ 0) ∨ (0 ≤ O.x ∧ 0 ≤ A.x))
    (hpB : (O.x < 0 ∧ B.x ≤ 0) ∨ (0 ≤ O.x ∧ 0 ≤ B.x)) :
    angM A O B = angV (vec O A) (vec O B) := by
  obtain ⟨c, hc, ec⟩ := rdir_ordinary hA hpA
  obtain ⟨d, hd, ed⟩ := rdir_ordinary hB hpB
  simp only [angM, angV, ec, ed, cosV_smul_left _ _ hc, cosV_smul_right _ _ hd]

end Moulton

end HilbertFoundations
