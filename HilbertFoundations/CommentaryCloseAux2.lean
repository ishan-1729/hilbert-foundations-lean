import HilbertFoundations.CommentaryCloseAux

/-!
# The finite part of a coordinate plane (helper for `CommentaryClose.lean`)

Dehn's semi-euclidean geometry (unit `concl.semi_euclidean`): over an ordered field `K` the points
of the plane `K²` whose co-ordinates are bounded by natural numbers (`FinPt`) form a convex part
`finPart K` of the plane (`ConvexPart`, CommentaryCloseAux.lean). Proved here, for a Pythagorean
field `K`:

* `finPart_layOffClosed`: segments laid off in the finite part stay in it, so the finite part
  satisfies groups I, II, IV;
* `finPart_infinitelyManyParallels`: if `K` contains an element `T` greater than every natural
  number, then through a point outside a line pass infinitely many lines that do not meet it inside
  the finite part (the lines `μ (u x + v y) + (u y - v x) = const` with `μ = T (k + 1) (1 + N) / c`
  meet the line `u x + v y + w = 0` at a distance `≥ T` from the point);
* `finPart_angleSum`: every triangle has angle sum two right angles;
* `finPart_similar`: there are similar triangles that are not congruent;
* `finPart_equalPerp`: the ends of equal perpendiculars erected on one side of a line are collinear.
-/

namespace HilbertFoundations

namespace FinitePart

open Coord Conclusion

universe u

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A **finite** element of an ordered field: bounded by a natural number. -/
def IsFin (x : K) : Prop := ∃ n : ℕ, |x| ≤ n

theorem isFin_zero : IsFin (0 : K) := ⟨0, by simp⟩

theorem isFin_natCast (m : ℕ) : IsFin (m : K) := ⟨m, by simp⟩

theorem IsFin.add {x y : K} (hx : IsFin x) (hy : IsFin y) : IsFin (x + y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, by push_cast; exact (abs_add_le x y).trans (add_le_add hm hn)⟩

omit [IsStrictOrderedRing K] in
theorem IsFin.neg {x : K} (hx : IsFin x) : IsFin (-x) := by
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, by rwa [abs_neg]⟩

theorem IsFin.sub {x y : K} (hx : IsFin x) (hy : IsFin y) : IsFin (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IsFin.mul {x y : K} (hx : IsFin x) (hy : IsFin y) : IsFin (x * y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m * n, by
    push_cast; rw [abs_mul]; exact mul_le_mul hm hn (abs_nonneg _) (Nat.cast_nonneg _)⟩

omit [IsStrictOrderedRing K] in
theorem isFin_of_abs_le_one {x : K} (h : |x| ≤ 1) : IsFin x := ⟨1, by simpa using h⟩

theorem isFin_of_sq_add_sq {x y : K} (h : IsFin (x ^ 2 + y ^ 2)) : IsFin x := by
  obtain ⟨n, hn⟩ := h
  have h2 : (0 : K) ≤ n := Nat.cast_nonneg n
  have h1 : x ^ 2 ≤ n := by
    have := le_abs_self (x ^ 2 + y ^ 2)
    nlinarith [sq_nonneg y]
  refine ⟨n + 1, abs_le_of_sq_le_sq ?_ (by positivity)⟩
  push_cast
  nlinarith

/-- A **finite point** of the plane `K²`: both co-ordinates are finite. -/
def FinPt (X : Coord K 2) : Prop := IsFin (xc X) ∧ IsFin (yc X)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Three points with non-zero determinant are not collinear. -/
theorem not_collinear_of_det {A B C : Coord K 2}
    (h : (xc B - xc A) * (yc C - yc A) - (yc B - yc A) * (xc C - xc A) ≠ 0) :
    ¬Collinear (Line := CoordLine K 2) A B C := by
  rintro ⟨a, hA, hB, hC⟩
  obtain ⟨u, v, w, huv, rfl⟩ := exists_eq_of_line a
  rw [mem_lineOfEq] at hA hB hC
  simp only [lin] at hA hB hC
  have hu : u * ((xc B - xc A) * (yc C - yc A) - (yc B - yc A) * (xc C - xc A)) = 0 := by
    linear_combination (yc C - yc A) * (hB - hA) - (yc B - yc A) * (hC - hA)
  have hv : v * ((xc B - xc A) * (yc C - yc A) - (yc B - yc A) * (xc C - xc A)) = 0 := by
    linear_combination (xc B - xc A) * (hC - hA) - (xc C - xc A) * (hB - hA)
  rcases huv with h' | h'
  · exact h' ((mul_eq_zero.1 hu).resolve_right h)
  · exact h' ((mul_eq_zero.1 hv).resolve_right h)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem lin_sub_lin (u v w : K) (X A : Coord K 2) :
    lin u v w X - lin u v w A = (xc X - xc A) * u + (yc X - yc A) * v := by
  simp only [lin]; ring

variable (K) in
/-- **The finite part** of the plane `K²`. -/
def finPart : ConvexPart (Coord K 2) (CoordLine K 2) where
  S := {X | FinPt X}
  convex := by
    rintro A B X ⟨hA1, hA2⟩ ⟨hB1, hB2⟩ hb
    obtain ⟨-, t, ht0, ht1, rfl⟩ := AffPt.sbtw_iff_param.1 (AffPt.between_iff.1 hb)
    have ht : IsFin t := isFin_of_abs_le_one (by rw [abs_of_pos ht0]; exact ht1.le)
    constructor
    · simp only [xc_add, xc_smul, xc_sub]; exact (ht.mul (hB1.sub hA1)).add hA1
    · simp only [yc_add, yc_smul, yc_sub]; exact (ht.mul (hB2.sub hA2)).add hA2
  ray_meets := by
    rintro O X ⟨hO1, hO2⟩ hXO
    have hpos : 0 < 1 + |xc X - xc O| + |yc X - yc O| := by positivity
    have hc0 : 0 < (1 + |xc X - xc O| + |yc X - yc O|)⁻¹ := inv_pos.2 hpos
    refine ⟨(1 + |xc X - xc O| + |yc X - yc O|)⁻¹ • (X - O) + O, ⟨?_, ?_⟩,
      (AffPt.mem_ray_iff hXO).2 ⟨_, hc0, rfl⟩⟩
    · simp only [xc_add, xc_smul, xc_sub]
      refine (isFin_of_abs_le_one ?_).add hO1
      rw [abs_mul, abs_of_pos hc0]
      calc (1 + |xc X - xc O| + |yc X - yc O|)⁻¹ * |xc X - xc O|
          ≤ (1 + |xc X - xc O| + |yc X - yc O|)⁻¹ * (1 + |xc X - xc O| + |yc X - yc O|) :=
            mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (yc X - yc O)]) hc0.le
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    · simp only [yc_add, yc_smul, yc_sub]
      refine (isFin_of_abs_le_one ?_).add hO2
      rw [abs_mul, abs_of_pos hc0]
      calc (1 + |xc X - xc O| + |yc X - yc O|)⁻¹ * |yc X - yc O|
          ≤ (1 + |xc X - xc O| + |yc X - yc O|)⁻¹ * (1 + |xc X - xc O| + |yc X - yc O|) :=
            mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (xc X - xc O)]) hc0.le
        _ = 1 := inv_mul_cancel₀ hpos.ne'
  noncollinear :=
    ⟨pt2 0 0, pt2 1 0, pt2 0 1, ⟨isFin_zero, isFin_zero⟩, ⟨by
      simpa using isFin_natCast (K := K) 1, isFin_zero⟩, ⟨isFin_zero, by simpa using isFin_natCast (K := K) 1⟩,
      not_collinear_of_det (by simp)⟩

theorem mem_finPart {X : Coord K 2} : X ∈ (finPart K).S ↔ FinPt X := Iff.rfl

/-- Segments laid off in the finite part stay in the finite part. -/
theorem finPart_layOffClosed : (finPart K).LayOffClosed := by
  rintro A B A' C' B' ⟨hA1, hA2⟩ ⟨hB1, hB2⟩ ⟨hA'1, hA'2⟩ - - - - hc
  rw [Coord.segCong_iff, ip_two, ip_two] at hc
  simp only [xc_sub, yc_sub] at hc
  have hfin : IsFin ((xc B' - xc A') ^ 2 + (yc B' - yc A') ^ 2) := by
    have : (xc B' - xc A') ^ 2 + (yc B' - yc A') ^ 2 =
        (xc B - xc A) * (xc B - xc A) + (yc B - yc A) * (yc B - yc A) := by
      linear_combination -hc
    rw [this]
    exact ((hB1.sub hA1).mul (hB1.sub hA1)).add ((hB2.sub hA2).mul (hB2.sub hA2))
  constructor
  · have := (isFin_of_sq_add_sq hfin).add hA'1
    simpa using this
  · have hfin' : IsFin ((yc B' - yc A') ^ 2 + (xc B' - xc A') ^ 2) := by rwa [add_comm]
    have := (isFin_of_sq_add_sq hfin').add hA'2
    simpa using this

/-! ### Infinitely many parallels -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem tilted_ne [LinearOrder K] [IsStrictOrderedRing K] {u v : K} (huv : u ≠ 0 ∨ v ≠ 0) (μ : K) :
    μ * u - v ≠ 0 ∨ μ * v + u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : (μ * u - v) ^ 2 + (μ * v + u) ^ 2 = (μ ^ 2 + 1) * (u ^ 2 + v ^ 2) := by ring
  rw [hcon.1, hcon.2] at h1
  have h2 : (μ ^ 2 + 1) * (u ^ 2 + v ^ 2) = 0 := by rw [← h1]; ring
  have h3 : u ^ 2 + v ^ 2 = 0 :=
    (mul_eq_zero.1 h2).resolve_left (by positivity)
  rcases huv with h | h
  · exact h (pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg u, sq_nonneg v]))
  · exact h (pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg u, sq_nonneg v]))

/-- The line through `A` with the equation `μ (u x + v y) + (u y - v x) = const`: the line through
`A` making with the lines `u x + v y = const` an angle of tangent `1 / μ`. -/
noncomputable def tilted (u v : K) (huv : u ≠ 0 ∨ v ≠ 0) (A : Coord K 2) (μ : K) :
    CoordLine K 2 :=
  lineOfEq (μ * u - v) (μ * v + u) (-(xc A * (μ * u - v) + yc A * (μ * v + u))) (tilted_ne huv μ)

theorem mem_tilted {u v : K} (huv : u ≠ 0 ∨ v ≠ 0) (A X : Coord K 2) (μ : K) :
    X ∈ tilted u v huv A μ ↔
      (xc X - xc A) * (μ * u - v) + (yc X - yc A) * (μ * v + u) = 0 := by
  rw [tilted, mem_lineOfEq]
  simp only [lin]
  constructor <;> intro h' <;> linear_combination h'

/-- **Infinitely many parallels in the finite part** of the plane over a non-archimedean field. -/
theorem finPart_infinitelyManyParallels (T : K) (hT : ∀ m : ℕ, (m : K) < T) :
    InfinitelyManyParallels (finPart K).Pt (finPart K).Ln := by
  intro a A hA
  obtain ⟨u, v, w, huv, ha⟩ := exists_eq_of_line a.1
  have hc0 : lin u v w A.1 ≠ 0 := fun h0 => hA (by
    show A.1 ∈ a.1
    rw [ha, mem_lineOfEq]; exact h0)
  have hT0 : (0 : K) < T := by simpa using hT 0
  have hN : 0 < u ^ 2 + v ^ 2 := by
    rcases huv with h | h
    · have := lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg v]
    · have := lt_of_le_of_ne (sq_nonneg v) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg u]
  have h1N : (1 : K) + (u ^ 2 + v ^ 2) ≠ 0 := by positivity
  -- the family of lines
  let μ : ℕ → K := fun k => T * ((k : K) + 1) * (1 + (u ^ 2 + v ^ 2)) / lin u v w A.1
  have hμ : ∀ k, μ k * lin u v w A.1 = T * ((k : K) + 1) * (1 + (u ^ 2 + v ^ 2)) := fun k =>
    div_mul_cancel₀ _ hc0
  let f : ℕ → (finPart K).Ln := fun k =>
    ⟨tilted u v huv A.1 (μ k), A.1, A.2, (mem_tilted huv A.1 A.1 (μ k)).2 (by ring)⟩
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ ?_
  · intro j k hjk
    have hl : tilted u v huv A.1 (μ j) = tilted u v huv A.1 (μ k) := congrArg Subtype.val hjk
    have hZ : pt2 (xc A.1 + (μ k * v + u)) (yc A.1 - (μ k * u - v)) ∈ tilted u v huv A.1 (μ k) := by
      rw [mem_tilted]; simp only [xc_pt2, yc_pt2]; ring
    rw [← hl, mem_tilted] at hZ
    simp only [xc_pt2, yc_pt2] at hZ
    have h2 : (μ j - μ k) * (u ^ 2 + v ^ 2) = 0 := by linear_combination hZ
    have h3 : μ j = μ k := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hN.ne')
    have h4 := (div_left_inj₀ hc0).1 h3
    have h5 := mul_left_cancel₀ hT0.ne' (by
      have := mul_right_cancel₀ h1N h4
      exact this)
    exact Nat.cast_injective (add_right_cancel h5)
  · intro k
    refine ⟨(mem_tilted huv A.1 A.1 (μ k)).2 (by ring), ?_⟩
    rintro ⟨X, hXb, hXa⟩
    have hXb' := (mem_tilted huv A.1 X.1 (μ k)).1 hXb
    have hXa' : lin u v w X.1 = 0 := by
      have : X.1 ∈ a.1 := hXa
      rwa [ha, mem_lineOfEq] at this
    have hd := lin_sub_lin u v w X.1 A.1
    rw [hXa', zero_sub] at hd
    obtain ⟨n₁, h₁⟩ : IsFin (xc X.1 - xc A.1) := X.2.1.sub A.2.1
    obtain ⟨n₂, h₂⟩ : IsFin (yc X.1 - yc A.1) := X.2.2.sub A.2.2
    set p := xc X.1 - xc A.1
    set q := yc X.1 - yc A.1
    set c := lin u v w A.1
    have hcross : q * u - p * v = μ k * c := by linear_combination hXb' + μ k * hd
    have e1 : (u ^ 2 + v ^ 2) * (p ^ 2 + q ^ 2) =
        c ^ 2 + (T * ((k : K) + 1) * (1 + (u ^ 2 + v ^ 2))) ^ 2 := by
      rw [← hμ k]
      linear_combination (-(p * u + q * v) + c) * hd + (q * u - p * v + μ k * c) * hcross
    have hk1 : (1 : K) ≤ ((k : K) + 1) ^ 2 := by
      have := Nat.cast_nonneg (α := K) k
      nlinarith
    have h2 : u ^ 2 + v ^ 2 ≤ (1 + (u ^ 2 + v ^ 2)) ^ 2 := by nlinarith
    have e2 : T ^ 2 * (u ^ 2 + v ^ 2) ≤ (T * ((k : K) + 1) * (1 + (u ^ 2 + v ^ 2))) ^ 2 := by
      have : T ^ 2 * (u ^ 2 + v ^ 2) ≤
          T ^ 2 * (((k : K) + 1) ^ 2 * (1 + (u ^ 2 + v ^ 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_mul_of_one_le_left (sq_nonneg _) hk1))
          (sq_nonneg T)
      calc T ^ 2 * (u ^ 2 + v ^ 2) ≤ T ^ 2 * (((k : K) + 1) ^ 2 * (1 + (u ^ 2 + v ^ 2)) ^ 2) := this
        _ = (T * ((k : K) + 1) * (1 + (u ^ 2 + v ^ 2))) ^ 2 := by ring
    have hp : p ^ 2 ≤ (n₁ : K) ^ 2 := sq_le_sq' (abs_le.1 h₁).1 (abs_le.1 h₁).2
    have hq : q ^ 2 ≤ (n₂ : K) ^ 2 := sq_le_sq' (abs_le.1 h₂).1 (abs_le.1 h₂).2
    have hn : ((n₁ + n₂ : ℕ) : K) < T := hT (n₁ + n₂)
    push_cast at hn
    have hn1 : (0 : K) ≤ n₁ := Nat.cast_nonneg n₁
    have hn2 : (0 : K) ≤ n₂ := Nat.cast_nonneg n₂
    have h3 : (n₁ : K) ^ 2 + (n₂ : K) ^ 2 ≤ ((n₁ : K) + n₂) ^ 2 := by
      have h30 := mul_nonneg hn1 hn2
      have e : ((n₁ : K) + n₂) ^ 2 = (n₁ : K) ^ 2 + (n₂ : K) ^ 2 + 2 * ((n₁ : K) * n₂) := by ring
      rw [e]; linarith
    have h4 : ((n₁ : K) + n₂) ^ 2 < T ^ 2 := by
      have h40 := mul_pos (sub_pos.2 hn) (by linarith : (0 : K) < T + ((n₁ : K) + n₂))
      have e : (T - ((n₁ : K) + n₂)) * (T + ((n₁ : K) + n₂)) = T ^ 2 - ((n₁ : K) + n₂) ^ 2 := by
        ring
      rw [e] at h40; linarith
    have hlt : p ^ 2 + q ^ 2 < T ^ 2 := by linarith
    have hge : T ^ 2 * (u ^ 2 + v ^ 2) ≤ (u ^ 2 + v ^ 2) * (p ^ 2 + q ^ 2) := by
      rw [e1]; linarith [sq_nonneg c]
    linarith [mul_lt_mul_of_pos_left hlt hN]

/-! ### The angle sum -/

/-- **Every triangle of the finite part has angle sum two right angles.** -/
theorem finPart_angleSum [IsPythagorean K] (A B C : (finPart K).Pt)
    (h : IsTriangle (Line := (finPart K).Ln) A B C) :
    AngleSumEqTwoRight (finPart K).Ln A B C := by
  have hT : IsTriangle (Line := CoordLine K 2) A.1 B.1 C.1 := fun hc =>
    h (ConvexPart.collinear_iff.2 hc)
  exact ConvexPart.angleSumEqTwoRight_of_plane
    (angleSumEqTwoRight_of_parallels hT (AffPt.not_collinear_of_eq hT).1)

/-! ### Similar triangles -/

/-- The point with natural co-ordinates `(m, n)`, a finite point. -/
def fp (m n : ℕ) : (finPart K).Pt := ⟨pt2 (m : K) (n : K), isFin_natCast m, isFin_natCast n⟩

theorem fp_val (m n : ℕ) : (fp (K := K) m n).1 = pt2 (m : K) (n : K) := rfl

/-- **There are similar triangles that are not congruent** in the finite part: the triangles with
vertices `(0,0), (1,0), (0,1)` and `(0,0), (2,0), (0,2)`. -/
theorem finPart_similar : ExistSimilarTriangles (finPart K).Pt (finPart K).Ln := by
  refine ⟨fp 0 0, fp 1 0, fp 0 1, fp 0 0, fp 2 0, fp 0 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hc => not_collinear_of_det (by simp [fp_val]) (ConvexPart.collinear_iff.1 hc)
  · exact fun hc => not_collinear_of_det (by simp [fp_val]) (ConvexPart.collinear_iff.1 hc)
  · show AngCong (fp (K := K) 1 0).1 (fp 0 0).1 (fp 0 1).1 (fp 2 0).1 (fp 0 0).1 (fp 0 2).1
    rw [Coord.angCong_iff]
    constructor <;> simp [fp_val, ip_two]
  · show AngCong (fp (K := K) 0 0).1 (fp 1 0).1 (fp 0 1).1 (fp 0 0).1 (fp 2 0).1 (fp 0 2).1
    rw [Coord.angCong_iff]
    have e1 : ip ((fp (K := K) 0 0).1 - (fp 1 0).1) ((fp 0 1).1 - (fp 1 0).1) = 1 := by
      simp [fp_val, ip_two]
    have e2 : ip ((fp (K := K) 0 0).1 - (fp 2 0).1) ((fp 0 2).1 - (fp 2 0).1) = 4 := by
      simp [fp_val, ip_two]; norm_num
    refine ⟨?_, ?_⟩
    · rw [e1, e2, sign_pos one_pos, sign_pos (by norm_num)]
    · rw [e1, e2]; simp [fp_val, ip_two]; norm_num
  · show AngCong (fp (K := K) 0 0).1 (fp 0 1).1 (fp 1 0).1 (fp 0 0).1 (fp 0 2).1 (fp 2 0).1
    rw [Coord.angCong_iff]
    have e1 : ip ((fp (K := K) 0 0).1 - (fp 0 1).1) ((fp 1 0).1 - (fp 0 1).1) = 1 := by
      simp [fp_val, ip_two]
    have e2 : ip ((fp (K := K) 0 0).1 - (fp 0 2).1) ((fp 2 0).1 - (fp 0 2).1) = 4 := by
      simp [fp_val, ip_two]; norm_num
    refine ⟨?_, ?_⟩
    · rw [e1, e2, sign_pos one_pos, sign_pos (by norm_num)]
    · rw [e1, e2]; simp [fp_val, ip_two]; norm_num
  · show ¬SegCong (fp (K := K) 0 0).1 (fp 1 0).1 (fp 0 0).1 (fp 2 0).1
    rw [Coord.segCong_iff]
    simp [fp_val, ip_two]
    norm_num

/-! ### Equal perpendiculars -/

/-- The sides of a right angle of the coordinate plane are orthogonal. -/
theorem ip_eq_zero_of_isRightAngle {E F G : Coord K 2}
    (h : IsRightAngle (L := CoordLine K 2) E F G) : ip (E - F) (G - F) = 0 := by
  obtain ⟨-, C, hC, hc⟩ := h
  obtain ⟨-, t, ht0, ht1, hF⟩ := AffPt.sbtw_iff_param.1 (AffPt.between_iff.1 hC)
  have h1 := (Coord.angCong_iff.1 hc).1
  have hx : xc F = t * (xc C - xc E) + xc E := by rw [hF]; simp
  have hy : yc F = t * (yc C - yc E) + yc E := by rw [hF]; simp
  have key : t * ip (G - F) (C - F) = -(1 - t) * ip (E - F) (G - F) := by
    simp only [ip_two, xc_sub, yc_sub]
    have a1 : t * (xc C - xc F) = -(1 - t) * (xc E - xc F) := by rw [hx]; ring
    have a2 : t * (yc C - yc F) = -(1 - t) * (yc E - yc F) := by rw [hy]; ring
    linear_combination (xc G - xc F) * a1 + (yc G - yc F) * a2
  by_contra hx0
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hy' : 0 < ip (G - F) (C - F) := by
      by_contra hy'
      push Not at hy'
      have := mul_nonpos_of_nonneg_of_nonpos ht0.le hy'
      have := mul_neg_of_pos_of_neg (sub_pos.2 ht1) hneg
      linarith
    rw [sign_neg hneg, sign_pos hy'] at h1
    exact absurd h1 (by decide)
  · have hy' : ip (G - F) (C - F) < 0 := by
      by_contra hy'
      push Not at hy'
      have := mul_nonneg ht0.le hy'
      have := mul_pos (sub_pos.2 ht1) hpos
      linarith
    rw [sign_pos hpos, sign_neg hy'] at h1
    exact absurd h1 (by decide)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The square of the distance of `E` from the line `u x + v y + w = 0`, measured along a
perpendicular with foot `F`. -/
theorem perp_foot {u v w : K} {E F G : Coord K 2} (hF : lin u v w F = 0) (hG : lin u v w G = 0)
    (hGF : G ≠ F) (hperp : ip (E - F) (G - F) = 0) :
    (u ^ 2 + v ^ 2) * ip (E - F) (E - F) = lin u v w E ^ 2 := by
  have hg : (xc G - xc F) * u + (yc G - yc F) * v = 0 := by
    rw [← lin_sub_lin u v w G F, hG, hF, sub_zero]
  have hl : lin u v w E = (xc E - xc F) * u + (yc E - yc F) * v := by
    rw [← lin_sub_lin u v w E F, hF, sub_zero]
  rw [ip_two] at hperp
  simp only [xc_sub, yc_sub] at hperp
  have hdet : u * (yc E - yc F) - v * (xc E - xc F) = 0 := by
    have h1 : (xc G - xc F) * (u * (yc E - yc F) - v * (xc E - xc F)) = 0 := by
      linear_combination (yc E - yc F) * hg - v * hperp
    have h2 : (yc G - yc F) * (u * (yc E - yc F) - v * (xc E - xc F)) = 0 := by
      linear_combination u * hperp - (xc E - xc F) * hg
    by_contra hne
    have hx := (mul_eq_zero.1 h1).resolve_right hne
    have hy := (mul_eq_zero.1 h2).resolve_right hne
    exact hGF (ext2 (sub_eq_zero.1 hx) (sub_eq_zero.1 hy))
  rw [hl, ip_two]
  simp only [xc_sub, yc_sub]
  linear_combination (u * (yc E - yc F) - v * (xc E - xc F)) * hdet

/-- **In the coordinate plane the ends of equal perpendiculars erected on one side of a line are
collinear.** -/
theorem equalPerp_coord (a : CoordLine K 2) (F₁ F₂ F₃ G₁ G₂ G₃ E₁ E₂ E₃ : Coord K 2)
    (hF₁ : F₁ ∈ a) (hF₂ : F₂ ∈ a) (hF₃ : F₃ ∈ a) (hG₁ : G₁ ∈ a) (hG₂ : G₂ ∈ a) (hG₃ : G₃ ∈ a)
    (h₁ : IsRightAngle (L := CoordLine K 2) E₁ F₁ G₁)
    (h₂ : IsRightAngle (L := CoordLine K 2) E₂ F₂ G₂)
    (h₃ : IsRightAngle (L := CoordLine K 2) E₃ F₃ G₃)
    (s₂ : SameSide a E₁ E₂) (s₃ : SameSide a E₁ E₃) (c₂ : SegCong F₁ E₁ F₂ E₂)
    (c₃ : SegCong F₁ E₁ F₃ E₃) : Collinear (Line := CoordLine K 2) E₁ E₂ E₃ := by
  obtain ⟨u, v, w, huv, rfl⟩ := exists_eq_of_line a
  rw [mem_lineOfEq] at hF₁ hF₂ hF₃ hG₁ hG₂ hG₃
  rw [sameSide_lineOfEq_iff] at s₂ s₃
  have key : ∀ E F G : Coord K 2, lin u v w F = 0 → lin u v w G = 0 →
      IsRightAngle (L := CoordLine K 2) E F G →
      (u ^ 2 + v ^ 2) * ip (E - F) (E - F) = lin u v w E ^ 2 := fun E F G hF hG h =>
    perp_foot hF hG (AffPt.not_collinear_of_eq h.1).2.2.symm (ip_eq_zero_of_isRightAngle h)
  have k₁ := key E₁ F₁ G₁ hF₁ hG₁ h₁
  have k₂ := key E₂ F₂ G₂ hF₂ hG₂ h₂
  have k₃ := key E₃ F₃ G₃ hF₃ hG₃ h₃
  rw [Coord.segCong_iff] at c₂ c₃
  have e₂ : lin u v w E₁ ^ 2 = lin u v w E₂ ^ 2 := by rw [← k₁, ← k₂, c₂]
  have e₃ : lin u v w E₁ ^ 2 = lin u v w E₃ ^ 2 := by rw [← k₁, ← k₃, c₃]
  have eq_of : ∀ x y : K, 0 < x * y → x ^ 2 = y ^ 2 → x = y := by
    intro x y hxy h
    have h' : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact sub_eq_zero.1 h0
    · exfalso
      have hx : x = -y := by linear_combination h0
      rw [hx] at hxy
      nlinarith [sq_nonneg y]
  have l₂ := eq_of _ _ s₂ e₂
  have l₃ := eq_of _ _ s₃ e₃
  refine ⟨lineOfEq u v (w - lin u v w E₁) huv, ?_, ?_, ?_⟩
  · rw [mem_lineOfEq]; simp only [lin]; ring
  · rw [mem_lineOfEq, l₂]; simp only [lin]; ring
  · rw [mem_lineOfEq, l₃]; simp only [lin]; ring

/-- **The ends of equal perpendiculars are collinear** in the finite part. -/
theorem finPart_equalPerp : EqualPerpendicularsCollinear (finPart K).Pt (finPart K).Ln := by
  intro a F₁ F₂ F₃ G₁ G₂ G₃ E₁ E₂ E₃ hF₁ hF₂ hF₃ hG₁ hG₂ hG₃ h₁ h₂ h₃ s₂ s₃ c₂ c₃
  exact ConvexPart.collinear_iff.2 (equalPerp_coord a.1 F₁.1 F₂.1 F₃.1 G₁.1 G₂.1 G₃.1 E₁.1 E₂.1
    E₃.1 hF₁ hF₂ hF₃ hG₁ hG₂ hG₃ (ConvexPart.isRightAngle_plane h₁)
    (ConvexPart.isRightAngle_plane h₂) (ConvexPart.isRightAngle_plane h₃)
    (ConvexPart.sameSide_iff.1 s₂) (ConvexPart.sameSide_iff.1 s₃) c₂ c₃)

end FinitePart

end HilbertFoundations
