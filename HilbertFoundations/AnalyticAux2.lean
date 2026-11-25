import HilbertFoundations.AnalyticAux

/-!
# Coordinate geometry over an ordered field: congruence (group IV) and Archimedes (group V)

Helper module of `Analytic.lean` (units `s9.*` are stated there). Over a linearly ordered field `K`
the coordinate space `Coord K n = K^n` receives Hilbert's congruences of § 9:

* `SegCong A B A' B'`: the squared euclidean lengths agree, `|B - A|² = |B' - A'|²`;
* `AngCong A O B A' O' B'`: the cosines agree, `cos ∠AOB = cos ∠A'O'B'`, written without square
  roots (`AngleEq`): `⟪a, b⟫` and `⟪a', b'⟫` have the same sign and
  `⟪a, b⟫² |a'|² |b'|² = ⟪a', b'⟫² |a|² |b|²`, where `a = A - O`, `b = B - O`, ….

The axioms that do not lay anything off (`segCong_swap`, IV 1 reflexivity, IV 2, IV 3, `angCong_wd`,
IV 4 reflexivity, IV 5, IV 6) hold over every ordered field; laying off segments and angles (IV 1,
IV 4) needs square roots of sums of squares, i.e. a **Pythagorean** field (`IsPythagorean K`:
closed under Hilbert's operation `ω ↦ √(1 + ω²)`); Archimedes's axiom holds over every archimedean
ordered field.
-/

namespace HilbertFoundations

open Module

universe u v

/-! ### Half-rays and segments in the coordinate geometry (ordered division rings) -/

namespace AffPt

section Rays

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  [LinearOrder K] [IsStrictOrderedRing K]

/-- **Half-rays** in the coordinate geometry: the half-ray from `O` through `A` consists of the
points `c (A - O) + O` with `c > 0`. -/
theorem mem_ray_iff {O A X : AffPt K V} (hA : A ≠ O) :
    X ∈ ray O A ↔ ∃ c : K, 0 < c ∧ X = c • (A - O) + O := by
  have hd : A - O ≠ 0 := sub_ne_zero.2 hA
  have hbet : ∀ c : K, Between A O (c • (A - O) + O) ↔ c < 0 := by
    intro c
    have key := sbtw_param_iff hd (1 : K) 0 c (O := O)
    simp only [one_smul, zero_smul, zero_add, sub_add_cancel] at key
    rw [between_iff, key]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h1 (not_lt.2 zero_le_one)
      · exact h1
    · intro h; exact Or.inr ⟨h, zero_lt_one⟩
  constructor
  · rintro ⟨-, hXO, hcol, hnb⟩
    obtain ⟨a, hA', hO', hX'⟩ := hcol
    have ha := a.eq_through hA.symm hO' hA'
    rw [ha, AffLine.mem_through_iff] at hX'
    obtain ⟨c, rfl⟩ := hX'
    refine ⟨c, ?_, rfl⟩
    rcases lt_trichotomy c 0 with h | h | h
    · exact absurd ((hbet c).2 h) hnb
    · subst h; simp at hXO
    · exact h
  · rintro ⟨c, hc, rfl⟩
    refine ⟨hA, ?_, ⟨AffLine.through O A hA.symm, AffLine.right_mem_through _,
      AffLine.left_mem_through _, (AffLine.mem_through_iff _).2 ⟨c, rfl⟩⟩, ?_⟩
    · intro h
      have : c • (A - O) = 0 := by
        have := congrArg (· - O) h; simpa using this
      rcases smul_eq_zero.1 this with h1 | h1
      · exact hc.ne' h1
      · exact hd h1
    · rw [hbet]; exact not_lt.2 hc.le

theorem mem_ray_self' {O A : AffPt K V} (hA : A ≠ O) : A ∈ ray O A :=
  (mem_ray_iff hA).2 ⟨1, one_pos, by simp⟩

/-- A half-ray is determined by any of its points: if `B - O = c (A - O)` with `c > 0`, the
half-rays `OB` and `OA` coincide. -/
theorem ray_eq_of_pos_smul {O A B : AffPt K V} (hA : A ≠ O) {c : K} (hc : 0 < c)
    (hB : B - O = c • (A - O)) : ray O B = ray O A := by
  have hBO : B ≠ O := by
    intro h; rw [h, sub_self] at hB
    rcases smul_eq_zero.1 hB.symm with h1 | h1
    · exact hc.ne' h1
    · exact hA (sub_eq_zero.1 h1)
  ext X
  rw [mem_ray_iff hA, mem_ray_iff hBO, hB]
  constructor
  · rintro ⟨d, hd, rfl⟩; exact ⟨d * c, mul_pos hd hc, by rw [smul_smul]⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d * c⁻¹, mul_pos hd (inv_pos.2 hc), ?_⟩
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

end Rays

end AffPt

/-- In any system satisfying the linear axioms II 1–4: if the segments `AB` and `BC` of a line
have no point but `B` in common (the hypothesis of IV 3), then `B` lies between `A` and `C`. -/
theorem between_of_segmentsMeetOnlyAt {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [LineOrder P L] {A B C : P} (h : SegmentsMeetOnlyAt (Line := L) A B C) : Between A B C := by
  obtain ⟨hcol, hAB, hBC, hmeet⟩ := h
  have hAC : A ≠ C := by
    intro hAC; subst hAC
    exact hAB (hmeet A (Or.inl rfl) (Or.inr (Or.inl rfl)))
  rcases between_trichotomy (Line := L) hcol hAB hAC hBC with h | h | h
  · exact absurd (hmeet A (Or.inl rfl) (Or.inr (Or.inr h))) hAB
  · exact h
  · exact absurd (hmeet C (Or.inr (Or.inr h)) (Or.inr (Or.inl rfl))) hBC.symm

/-! ### Pythagorean fields -/

/-- A **Pythagorean** ordered field: closed under Hilbert's fifth operation `ω ↦ √(1 + ω²)`
(§ 9). -/
class IsPythagorean (K : Type u) [Field K] [LinearOrder K] : Prop where
  sqrt_one_add_sq : ∀ x : K, ∃ y : K, 0 ≤ y ∧ y ^ 2 = 1 + x ^ 2

section Pythagorean

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In a Pythagorean field the sum of two squares has a square root:
`√(a² + b²) = |a| √(1 + (b/a)²)` (Hilbert's identity of § 9, with `|a|` for `a`). -/
theorem IsPythagorean.exists_sqrt_sq_add_sq [IsPythagorean K] (a b : K) :
    ∃ c : K, 0 ≤ c ∧ c ^ 2 = a ^ 2 + b ^ 2 := by
  by_cases ha : a = 0
  · exact ⟨|b|, abs_nonneg b, by rw [ha, sq_abs]; ring⟩
  · obtain ⟨y, hy0, hy⟩ := IsPythagorean.sqrt_one_add_sq (b / a)
    refine ⟨|a| * y, mul_nonneg (abs_nonneg a) hy0, ?_⟩
    rw [mul_pow, sq_abs, hy]; field_simp

/-- In a Pythagorean field every sum of squares has a (nonnegative) square root. -/
theorem IsPythagorean.exists_sqrt_of_isSumSq [IsPythagorean K] {s : K} (hs : IsSumSq s) :
    ∃ r : K, 0 ≤ r ∧ r ^ 2 = s := by
  induction hs with
  | zero => exact ⟨0, le_rfl, by ring⟩
  | sq_add a hs ih =>
    obtain ⟨r, -, hr⟩ := ih
    obtain ⟨c, hc, hc2⟩ := IsPythagorean.exists_sqrt_sq_add_sq a r
    exact ⟨c, hc, by rw [hc2, ← hr]; ring⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem isSumSq_div {s t : K} (hs : IsSumSq s) (ht : IsSumSq t) : IsSumSq (s / t) := by
  rw [div_eq_mul_inv, show s * t⁻¹ = (s * t) * (t⁻¹ * t⁻¹) by
    rcases eq_or_ne t 0 with h | h
    · simp [h]
    · field_simp]
  exact (hs.mul ht).mul (IsSumSq.mul_self _)

theorem isSumSq_nonneg {s : K} (hs : IsSumSq s) : 0 ≤ s := by
  induction hs with
  | zero => exact le_rfl
  | sq_add a _ ih => exact add_nonneg (mul_self_nonneg a) ih

omit [IsStrictOrderedRing K] in
/-- Conversely, a field in which every sum of two squares has a square root is Pythagorean. -/
theorem IsPythagorean.of_sq_add_sq (h : ∀ a b : K, ∃ c : K, 0 ≤ c ∧ c ^ 2 = a ^ 2 + b ^ 2) :
    IsPythagorean K :=
  ⟨fun x => by obtain ⟨c, hc, h2⟩ := h 1 x; exact ⟨c, hc, by rw [h2]; ring⟩⟩

instance : IsPythagorean ℝ :=
  ⟨fun x => ⟨Real.sqrt (1 + x ^ 2), Real.sqrt_nonneg _, Real.sq_sqrt (by positivity)⟩⟩

end Pythagorean

/-! ### The euclidean inner product of `K^n` -/

namespace Coord

variable {K : Type u} [Field K] {n : ℕ}

/-- The **inner product** `⟪u, v⟫ = Σ uᵢ vᵢ` of `K^n`. -/
def ip (u v : Coord K n) : K := dotProduct (AffPt.toV u) (AffPt.toV v)

theorem ip_def (u v : Coord K n) : ip u v = ∑ i, AffPt.toV u i * AffPt.toV v i := rfl

theorem ip_comm (u v : Coord K n) : ip u v = ip v u := dotProduct_comm _ _

@[simp] theorem ip_add_left (u v w : Coord K n) : ip (u + v) w = ip u w + ip v w :=
  add_dotProduct _ _ _

@[simp] theorem ip_add_right (u v w : Coord K n) : ip u (v + w) = ip u v + ip u w :=
  dotProduct_add _ _ _

@[simp] theorem ip_sub_left (u v w : Coord K n) : ip (u - v) w = ip u w - ip v w :=
  sub_dotProduct _ _ _

@[simp] theorem ip_sub_right (u v w : Coord K n) : ip u (v - w) = ip u v - ip u w :=
  dotProduct_sub _ _ _

@[simp] theorem ip_neg_left (u v : Coord K n) : ip (-u) v = -ip u v := neg_dotProduct _ _

@[simp] theorem ip_neg_right (u v : Coord K n) : ip u (-v) = -ip u v := dotProduct_neg _ _

@[simp] theorem ip_smul_left (c : K) (u v : Coord K n) : ip (c • u) v = c * ip u v := by
  rw [ip, AffPt.toV_smul, smul_dotProduct, smul_eq_mul]; rfl

@[simp] theorem ip_smul_right (c : K) (u v : Coord K n) : ip u (c • v) = c * ip u v := by
  rw [ip_comm, ip_smul_left, ip_comm]

@[simp] theorem ip_zero_left (v : Coord K n) : ip 0 v = 0 := zero_dotProduct _

@[simp] theorem ip_zero_right (v : Coord K n) : ip v 0 = 0 := dotProduct_zero _

theorem isSumSq_ip_self (v : Coord K n) : IsSumSq (ip v v) :=
  IsSumSq.sum_mul_self Finset.univ (AffPt.toV v)

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem ip_self_nonneg (v : Coord K n) : 0 ≤ ip v v := isSumSq_nonneg (isSumSq_ip_self v)

theorem ip_self_eq_zero {v : Coord K n} : ip v v = 0 ↔ v = 0 := dotProduct_self_eq_zero

theorem ip_self_pos {v : Coord K n} (h : v ≠ 0) : 0 < ip v v :=
  lt_of_le_of_ne (ip_self_nonneg v) (fun h' => h (ip_self_eq_zero.1 h'.symm))

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem lagrange_vec (x y : Fin n → K) :
    2 * ((∑ i, x i * x i) * (∑ i, y i * y i) - (∑ i, x i * y i) ^ 2) =
      ∑ i, ∑ j, (x i * y j - x j * y i) ^ 2 := by
  have e : ∀ i j, (x i * y j - x j * y i) ^ 2 =
      (x i * x i) * (y j * y j) + (x j * x j) * (y i * y i) - 2 * ((x i * y i) * (x j * y j)) := by
    intro i j; ring
  have h1 : ∑ i, ∑ j, (x i * x i) * (y j * y j) = (∑ i, x i * x i) * (∑ i, y i * y i) := by
    rw [Finset.sum_mul_sum]
  have h2 : ∑ i, ∑ j, (x j * x j) * (y i * y i) = (∑ i, x i * x i) * (∑ i, y i * y i) := by
    rw [Finset.sum_comm]; exact h1
  have h3 : ∑ i, ∑ j, (x i * y i) * (x j * y j) = (∑ i, x i * y i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have h4 : ∑ i, ∑ j, ((x i * x i) * (y j * y j) + (x j * x j) * (y i * y i) -
      2 * ((x i * y i) * (x j * y j))) = ∑ i, ∑ j, (x i * x i) * (y j * y j) +
      ∑ i, ∑ j, (x j * x j) * (y i * y i) - 2 * ∑ i, ∑ j, (x i * y i) * (x j * y j) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [e]
  rw [h4, h1, h2, h3]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **Lagrange's identity**: `2 (|a|² |b|² - ⟪a, b⟫²) = Σᵢ Σⱼ (aᵢ bⱼ - aⱼ bᵢ)²`. -/
theorem lagrange (a b : Coord K n) :
    2 * (ip a a * ip b b - ip a b ^ 2) =
      ∑ i, ∑ j, (AffPt.toV a i * AffPt.toV b j - AffPt.toV a j * AffPt.toV b i) ^ 2 :=
  lagrange_vec _ _

end Coord

namespace AffPt

section Sbtw

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  [LinearOrder K] [IsStrictOrderedRing K]

/-- Betweenness in the coordinate geometry: `B = A + t (C - A)` with `0 < t < 1`. -/
theorem sbtw_iff_param {A B C : AffPt K V} :
    Sbtw K A B C ↔ A ≠ C ∧ ∃ t : K, 0 < t ∧ t < 1 ∧ B = t • (C - A) + A := by
  constructor
  · intro h
    have hAC := Sbtw.left_ne_right h
    have hd : C - A ≠ 0 := sub_ne_zero.2 hAC.symm
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff.1 (Wbtw.mem_affineSpan h.wbtw)
    have key := sbtw_param_iff hd (0 : K) t 1 (O := A)
    simp only [one_smul, zero_smul, zero_add, sub_add_cancel] at key
    rcases key.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hAC, t, h1, h2, rfl⟩
    · exact absurd (h1.trans h2) (not_lt.2 zero_le_one)
  · rintro ⟨hAC, t, h1, h2, rfl⟩
    have hd : C - A ≠ 0 := sub_ne_zero.2 hAC.symm
    have key := sbtw_param_iff hd (0 : K) t 1 (O := A)
    simp only [one_smul, zero_smul, zero_add, sub_add_cancel] at key
    exact key.2 (Or.inl ⟨h1, h2⟩)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem not_collinear_of_eq [Nontrivial V] {A B C : AffPt K V} (h : ¬Collinear A B C) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  refine ⟨fun e => h (collinear_of_mathlib ?_), fun e => h (collinear_of_mathlib ?_),
    fun e => h (collinear_of_mathlib ?_)⟩
  · subst e; exact (collinear_pair K A C).subset (by intro x hx; simp at hx ⊢; tauto)
  · subst e; exact (collinear_pair K A B).subset (by intro x hx; simp at hx ⊢; tauto)
  · subst e; exact (collinear_pair K A B).subset (by intro x hx; simp at hx ⊢; tauto)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem collinear_of_smul {A O B : AffPt K V} (hA : A ≠ O) (c : K) (h : B - O = c • (A - O)) :
    Collinear A O B :=
  ⟨AffLine.through O A hA.symm, AffLine.right_mem_through _, AffLine.left_mem_through _,
    (AffLine.mem_through_iff _).2 ⟨c, by rw [← h, sub_add_cancel]⟩⟩

/-- The two half-rays of a (genuine) angle are distinct. -/
theorem ray_ne_ray {A O B : AffPt K V} (h : ¬Collinear A O B) (hA : A ≠ O) (hB : B ≠ O) :
    ray O A ≠ ray O B := by
  intro e
  have : B ∈ ray O A := e ▸ mem_ray_self' hB
  obtain ⟨c, -, hc⟩ := (mem_ray_iff hA).1 this
  exact h (collinear_of_smul hA c (by rw [hc, add_sub_cancel_right]))

theorem exists_pos_of_ray_eq {O A C : AffPt K V} (hA : A ≠ O) (h : ray O C = ray O A) :
    ∃ c : K, 0 < c ∧ C - O = c • (A - O) := by
  have hC : C ≠ O := by
    intro hCO
    rw [hCO] at h
    have : A ∈ ray O O := h ▸ mem_ray_self' hA
    exact this.1 rfl
  have : C ∈ ray O A := h ▸ mem_ray_self' hC
  obtain ⟨c, hc, e⟩ := (mem_ray_iff hA).1 this
  exact ⟨c, hc, by rw [e, add_sub_cancel_right]⟩

/-- Two triples describing the same (genuine) angle: the sides agree up to positive factors, in the
same or in the opposite order. -/
theorem sameAngle_cases [Nontrivial V] {A O B C D : AffPt K V} (h : ¬Collinear A O B)
    (hs : SameAngle A O B C D) :
    ∃ c d : K, 0 < c ∧ 0 < d ∧ ((C - O = c • (A - O) ∧ D - O = d • (B - O)) ∨
      (C - O = c • (B - O) ∧ D - O = d • (A - O))) := by
  obtain ⟨hAO, -, hOB⟩ := not_collinear_of_eq h
  have hrAB := ray_ne_ray h hAO hOB.symm
  have hC : ray O C ∈ ({ray O A, ray O B} : Set (Set (AffPt K V))) := hs ▸ Set.mem_insert _ _
  have hD : ray O D ∈ ({ray O A, ray O B} : Set (Set (AffPt K V))) :=
    hs ▸ Set.mem_insert_of_mem _ rfl
  have hA' : ray O A ∈ ({ray O C, ray O D} : Set (Set (AffPt K V))) := hs ▸ Set.mem_insert _ _
  have hB' : ray O B ∈ ({ray O C, ray O D} : Set (Set (AffPt K V))) :=
    hs ▸ Set.mem_insert_of_mem _ rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC hD hA' hB'
  rcases hC with hC | hC <;> rcases hD with hD | hD
  · exfalso; rcases hB' with e | e <;> exact hrAB (by first | rw [e, hC] | rw [e, hD])
  · obtain ⟨c, hc, ec⟩ := exists_pos_of_ray_eq hAO hC
    obtain ⟨d, hd, ed⟩ := exists_pos_of_ray_eq hOB.symm hD
    exact ⟨c, d, hc, hd, Or.inl ⟨ec, ed⟩⟩
  · obtain ⟨c, hc, ec⟩ := exists_pos_of_ray_eq hOB.symm hC
    obtain ⟨d, hd, ed⟩ := exists_pos_of_ray_eq hAO hD
    exact ⟨c, d, hc, hd, Or.inr ⟨ec, ed⟩⟩
  · exfalso; rcases hA' with e | e <;> exact hrAB (by first | rw [e, hC] | rw [e, hD])

end Sbtw

end AffPt

namespace Coord

open AffPt

variable {K : Type u} [Field K] [LinearOrder K] {n : ℕ}

/-- **Equality of angles** (equality of cosines, without square roots): the angle between `a`, `b`
equals the angle between `a'`, `b'`. -/
def AngleEq (a b a' b' : Coord K n) : Prop :=
  SignType.sign (ip a b) = SignType.sign (ip a' b') ∧
    ip a b ^ 2 * (ip a' a' * ip b' b') = ip a' b' ^ 2 * (ip a a * ip b b)

/-- **Congruence of segments** in the coordinate geometry (§ 9): equal euclidean lengths. -/
instance instHasSegCong : HasSegCong (Coord K n) :=
  ⟨fun A B A' B' => ip (B - A) (B - A) = ip (B' - A') (B' - A')⟩

/-- **Congruence of angles** in the coordinate geometry (§ 9): equal cosines. -/
instance instHasAngCong : HasAngCong (Coord K n) :=
  ⟨fun A O B A' O' B' => AngleEq (A - O) (B - O) (A' - O') (B' - O')⟩

omit [LinearOrder K] in
theorem segCong_iff {A B A' B' : Coord K n} :
    SegCong A B A' B' ↔ ip (B - A) (B - A) = ip (B' - A') (B' - A') := Iff.rfl

theorem angCong_iff {A O B A' O' B' : Coord K n} :
    AngCong A O B A' O' B' ↔ AngleEq (A - O) (B - O) (A' - O') (B' - O') := Iff.rfl

theorem angleEq_refl (a b : Coord K n) : AngleEq a b a b := ⟨rfl, rfl⟩

theorem AngleEq.symm {a b a' b' : Coord K n} (h : AngleEq a b a' b') : AngleEq a' b' a b :=
  ⟨h.1.symm, h.2.symm⟩

theorem angleEq_comm_left {a b a' b' : Coord K n} : AngleEq a b a' b' ↔ AngleEq b a a' b' := by
  unfold AngleEq; rw [ip_comm a b, mul_comm (ip a a)]

variable [IsStrictOrderedRing K]

theorem angleEq_smul_left {a b a' b' : Coord K n} {c d : K} (hc : 0 < c) (hd : 0 < d) :
    AngleEq (c • a) (d • b) a' b' ↔ AngleEq a b a' b' := by
  have hcd : 0 < c * d := mul_pos hc hd
  have e1 : ip (c • a) (d • b) = (c * d) * ip a b := by
    simp only [ip_smul_left, ip_smul_right]; ring
  have e2 : ip (c • a) (c • a) = c ^ 2 * ip a a := by simp only [ip_smul_left, ip_smul_right]; ring
  have e3 : ip (d • b) (d • b) = d ^ 2 * ip b b := by simp only [ip_smul_left, ip_smul_right]; ring
  unfold AngleEq
  rw [e1, e2, e3, sign_mul, sign_pos hcd, one_mul]
  apply and_congr Iff.rfl
  have hne : (c * d) ^ 2 ≠ 0 := pow_ne_zero 2 hcd.ne'
  constructor
  · intro h
    apply mul_left_cancel₀ hne
    linear_combination h
  · intro h
    linear_combination (c * d) ^ 2 * h

theorem eq_of_sq_eq_of_sign_eq {x y : K} (h2 : x ^ 2 = y ^ 2)
    (hs : SignType.sign x = SignType.sign y) : x = y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact h
  · rw [h, Left.sign_neg] at hs
    have : SignType.sign y = 0 := by
      rcases (SignType.sign y).trichotomy with h' | h' | h' <;> rw [h'] at hs ⊢
      · exact absurd hs (by decide)
      · exact absurd hs (by decide)
    rw [sign_eq_zero_iff] at this
    rw [h, this, neg_zero]

theorem AngleEq.trans {a b a' b' a'' b'' : Coord K n} (h1 : AngleEq a b a' b')
    (h2 : AngleEq a b a'' b'') (hN : ip a a * ip b b ≠ 0) : AngleEq a' b' a'' b'' := by
  refine ⟨h1.1.symm.trans h2.1, ?_⟩
  apply mul_left_cancel₀ hN
  linear_combination (ip a' a' * ip b' b') * h2.2 - (ip a'' a'' * ip b'' b'') * h1.2

/-- Two angles with equal sides (`|b| = |b'|`, `|c| = |c'|`) and equal cosines have equal inner
products. -/
theorem ip_eq_of_angleEq {b c b' c' : Coord K n} (h : AngleEq b c b' c') (hb : ip b b = ip b' b')
    (hc : ip c c = ip c' c') (hN : ip b b * ip c c ≠ 0) : ip b c = ip b' c' := by
  apply eq_of_sq_eq_of_sign_eq _ h.1
  have := h.2
  rw [← hb, ← hc] at this
  exact mul_right_cancel₀ hN this

omit [IsStrictOrderedRing K] in
theorem angleEq_of_ip_eq {a b a' b' : Coord K n} (h : ip a b = ip a' b') (ha : ip a a = ip a' a')
    (hb : ip b b = ip b' b') : AngleEq a b a' b' :=
  ⟨by rw [h], by rw [h, ha, hb]⟩

variable [NeZero n]

instance : Nontrivial (Fin n → K) := Function.nontrivial

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem sub_ne_zero_of_not_collinear {A O B : Coord K n} (h : ¬Collinear A O B) :
    A - O ≠ 0 ∧ B - O ≠ 0 := by
  obtain ⟨h1, -, h3⟩ := not_collinear_of_eq h
  exact ⟨sub_ne_zero.2 h1, sub_ne_zero.2 h3.symm⟩

theorem ipN_pos {A O B : Coord K n} (h : ¬Collinear A O B) :
    0 < ip (A - O) (A - O) * ip (B - O) (B - O) := by
  obtain ⟨h1, h2⟩ := sub_ne_zero_of_not_collinear h
  exact mul_pos (ip_self_pos h1) (ip_self_pos h2)

/-- **Strict Cauchy–Schwarz inequality** for a genuine angle. -/
theorem cauchySchwarz_pos {A O B : Coord K n} (h : ¬Collinear A O B) :
    0 < ip (A - O) (A - O) * ip (B - O) (B - O) - ip (A - O) (B - O) ^ 2 := by
  set a := A - O
  set b := B - O
  have hL := lagrange a b
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, (AffPt.toV a i * AffPt.toV b j -
      AffPt.toV a j * AffPt.toV b i) ^ 2 :=
    fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hge : 0 ≤ ip a a * ip b b - ip a b ^ 2 := by
    have : 0 ≤ 2 * (ip a a * ip b b - ip a b ^ 2) := hL ▸ Finset.sum_nonneg hnn
    linarith
  refine lt_of_le_of_ne hge (fun h0 => h ?_)
  rw [← h0, mul_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg hnn] at hL
  have hij : ∀ i j, AffPt.toV a i * AffPt.toV b j = AffPt.toV a j * AffPt.toV b i := by
    intro i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1
      (hL i (Finset.mem_univ _)) j (Finset.mem_univ _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  have ha0 : AffPt.toV a ≠ 0 := (sub_ne_zero_of_not_collinear h).1
  obtain ⟨k, hk⟩ := Function.ne_iff.1 ha0
  simp only [Pi.zero_apply] at hk
  have hAO : A ≠ O := not_collinear_of_eq h |>.1
  refine collinear_of_smul hAO (AffPt.toV b k / AffPt.toV a k) ?_
  apply AffPt.toV_injective
  funext j
  simp only [AffPt.toV_smul, Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff hk]
  linear_combination hij k j

omit [NeZero n] [LinearOrder K] [IsStrictOrderedRing K] in
theorem isSumSq_finset_sum {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IsSumSq (f i)) :
    IsSumSq (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsSumSq (fun _ _ => IsSumSq.add) IsSumSq.zero h

omit [NeZero n] in
theorem isSumSq_cs (a b : Coord K n) : IsSumSq (ip a a * ip b b - ip a b ^ 2) := by
  have h2 : (ip a a * ip b b - ip a b ^ 2) = (2 * (ip a a * ip b b - ip a b ^ 2)) / (1 * 1 + 1 * 1) := by
    field_simp; ring
  rw [h2, lagrange]
  apply isSumSq_div
  · exact isSumSq_finset_sum _ _ (fun i _ => isSumSq_finset_sum _ _ (fun j _ => by
      rw [sq]; exact IsSumSq.mul_self _))
  · exact (IsSumSq.mul_self 1).add (IsSumSq.mul_self 1)

end Coord

namespace AffPt

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The side functional of a line `a` of a plane `S`, based at any point `O'` of `a`. -/
theorem side_functional_at {S : AffineSubspace K (AffPt K V)} [FiniteDimensional K S.direction]
    (hS : finrank K S.direction = 2) (a : AffLine K V) (ha : a.carrier ≤ S) {O' : AffPt K V}
    (hO' : O' ∈ a) : ∃ f : AffPt K V →ₗ[K] K, ∀ X ∈ S, (X ∈ a.carrier ↔ f (X - O') = 0) := by
  obtain ⟨O, f, hO, hf⟩ := exists_side_functional hS a ha
  have h0 : f (O' - O) = 0 := (hf O' (ha hO')).1 hO'
  refine ⟨f, fun X hX => ?_⟩
  rw [hf X hX, show X - O = (X - O') + (O' - O) by abel, map_add, h0, add_zero]

end AffPt

namespace Coord

open AffPt

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-! ### The axioms of congruence of segments (IV 1–3) -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem ip_sub_swap (X Y : Coord K n) : ip (X - Y) (X - Y) = ip (Y - X) (Y - X) := by
  rw [← neg_sub Y X, ip_neg_left, ip_neg_right, neg_neg]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem segCongSwap : SegCongSwap (Coord K n) := by
  intro A B A' B' h
  refine ⟨?_, ?_⟩
  · show ip (A - B) (A - B) = _; rw [ip_sub_swap]; exact h
  · show _ = ip (A' - B') (A' - B'); rw [ip_sub_swap A' B']; exact h

/-- The algebra behind IV 3: if `t² s = t'² s'` and `(1 - t)² s = (1 - t')² s'` with
`0 < t, t' < 1` and `s, s' > 0`, then `s = s'`. -/
theorem iv3_algebra {t t' s s' : K} (ht0 : 0 < t) (ht1 : t < 1) (ht0' : 0 < t') (ht1' : t' < 1)
    (hs' : 0 < s') (h1 : t ^ 2 * s = t' ^ 2 * s') (h2 : (1 - t) ^ 2 * s = (1 - t') ^ 2 * s') :
    s = s' := by
  have k : (t * (1 - t')) ^ 2 = (t' * (1 - t)) ^ 2 := by
    apply mul_right_cancel₀ hs'.ne'
    linear_combination (-t ^ 2) * h2 + (1 - t) ^ 2 * h1
  have k2 : t * (1 - t') = t' * (1 - t) :=
    (pow_left_inj₀ (mul_pos ht0 (sub_pos.2 ht1')).le (mul_pos ht0' (sub_pos.2 ht1)).le
      two_ne_zero).1 k
  have htt : t = t' := by linear_combination k2
  subst htt
  exact mul_left_cancel₀ (pow_ne_zero 2 ht0.ne') h1

theorem axiomIV3 : AxiomIV3 (Coord K n) := by
  intro A B C A' B' C' h h' hAB hBC
  have hb := between_of_segmentsMeetOnlyAt (L := CoordLine K n) h
  have hb' := between_of_segmentsMeetOnlyAt (L := CoordLine K n) h'
  obtain ⟨hAC, t, ht0, ht1, hB⟩ := sbtw_iff_param.1 hb
  obtain ⟨hAC', t', ht0', ht1', hB'⟩ := sbtw_iff_param.1 hb'
  rw [segCong_iff] at hAB hBC ⊢
  have e1 : B - A = t • (C - A) := by rw [hB, add_sub_cancel_right]
  have e2 : C - B = (1 - t) • (C - A) := by rw [hB, sub_smul, one_smul]; abel
  have e1' : B' - A' = t' • (C' - A') := by rw [hB', add_sub_cancel_right]
  have e2' : C' - B' = (1 - t') • (C' - A') := by rw [hB', sub_smul, one_smul]; abel
  rw [e1, e1'] at hAB
  rw [e2, e2'] at hBC
  simp only [ip_smul_left, ip_smul_right] at hAB hBC
  have hs' : 0 < ip (C' - A') (C' - A') := ip_self_pos (sub_ne_zero.2 hAC'.symm)
  exact iv3_algebra ht0 ht1 ht0' ht1' hs' (by linear_combination hAB) (by linear_combination hBC)

/-- **Laying off segments** (IV 1) in the coordinate geometry over a Pythagorean field. -/
theorem axiomIV1LayOff [IsPythagorean K] : AxiomIV1LayOff (Coord K n) := by
  intro A B A' C' hAB hC'
  have hd : C' - A' ≠ 0 := sub_ne_zero.2 hC'.symm
  set d := C' - A'
  set s := ip (B - A) (B - A)
  set E := ip d d
  have hs : 0 < s := ip_self_pos (sub_ne_zero.2 hAB.symm)
  have hE : 0 < E := ip_self_pos hd
  obtain ⟨r, hr0, hr⟩ :=
    IsPythagorean.exists_sqrt_of_isSumSq ((isSumSq_ip_self (B - A)).mul (isSumSq_ip_self d))
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hr; exfalso
      have : 0 < s * E := mul_pos hs hE
      rw [← hr] at this; simp at this
    · exact h
  set l := r / E
  have hl : 0 < l := div_pos hrpos hE
  have hl2 : l * (l * E) = s := by
    simp only [l]; field_simp; rw [hr]; exact mul_comm _ _
  refine ⟨l • d + A', ⟨(mem_ray_iff hC'.symm).2 ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
  · show s = ip (l • d + A' - A') (l • d + A' - A')
    rw [add_sub_cancel_right, ip_smul_left, ip_smul_right, hl2]
  · rintro y ⟨hy, hys⟩
    obtain ⟨m, hm, rfl⟩ := (mem_ray_iff hC'.symm).1 hy
    have h2 : m * (m * E) = s := by
      have := hys.symm
      show _ = s
      rw [segCong_iff, add_sub_cancel_right, ip_smul_left, ip_smul_right] at hys
      exact hys.symm
    have : m = l := by
      have hsq : m ^ 2 = l ^ 2 := by
        apply mul_right_cancel₀ hE.ne'
        linear_combination h2 - hl2
      exact (pow_left_inj₀ hm.le hl.le two_ne_zero).1 hsq
    rw [this]

/-- **The linear axioms of congruence** IV 1–3 in the coordinate geometry over a Pythagorean
ordered field. -/
instance instSegmentCongruence [IsPythagorean K] : SegmentCongruence (Coord K n) (CoordLine K n) :=
  { AffPt.instLineOrder with
    segCong_swap := segCongSwap
    ax_IV1 := axiomIV1LayOff
    ax_IV1_refl := fun _ _ _ => rfl
    ax_IV2 := fun _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
    ax_IV3 := axiomIV3 }

/-! ### The axioms of congruence of angles and of triangles -/

variable [NeZero n]

theorem angCongWellDefined : AngCongWellDefined (Coord K n) := by
  intro A O B C D A' O' B' C' D' h h' hs hs' hc
  rw [angCong_iff] at hc ⊢
  obtain ⟨c, d, hc0, hd0, hcd⟩ := sameAngle_cases h hs
  obtain ⟨c', d', hc0', hd0', hcd'⟩ := sameAngle_cases h' hs'
  have step1 : AngleEq (C - O) (D - O) (A' - O') (B' - O') := by
    rcases hcd with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2, angleEq_smul_left hc0 hd0]; exact hc
    · rw [e1, e2, angleEq_smul_left hc0 hd0, angleEq_comm_left]; exact hc
  apply AngleEq.symm
  rcases hcd' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2, angleEq_smul_left hc0' hd0']; exact step1.symm
  · rw [e1, e2, angleEq_smul_left hc0' hd0', angleEq_comm_left]; exact step1.symm

theorem axiomIV5 : AxiomIV5 (Coord K n) := by
  intro A O B A' O' B' A'' O'' B'' h _ _ h1 h2
  exact AngleEq.trans h1 h2 (ipN_pos h).ne'

/-- **The plane-free axioms of congruence of angles** in the coordinate geometry (any ordered
field). -/
instance instAngleCongruence : AngleCongruence (Coord K n) (CoordLine K n) :=
  { AffPt.instLineOrder with
    angCong_wd := angCongWellDefined
    ax_IV4_refl := fun _ _ _ _ => angleEq_refl _ _
    ax_IV5 := axiomIV5 }

/-- **Axiom IV 6** in the coordinate geometry (any ordered field). -/
theorem axiomIV6 : AxiomIV6 (Coord K n) := by
  intro A B C A' B' C' h h' hAB hAC hA
  rw [segCong_iff] at hAB hAC
  rw [angCong_iff] at hA ⊢
  rw [angCong_iff]
  have hN : ip (B - A) (B - A) * ip (C - A) (C - A) ≠ 0 := by
    have : ¬Collinear B A C := fun hc => h (by
      obtain ⟨l, h1, h2, h3⟩ := hc; exact ⟨l, h2, h1, h3⟩)
    exact (ipN_pos this).ne'
  have hbc := ip_eq_of_angleEq hA hAB hAC hN
  set b := B - A
  set c := C - A
  set b' := B' - A'
  set c' := C' - A'
  have eAB : A - B = -b := (neg_sub B A).symm
  have eCB : C - B = c - b := (sub_sub_sub_cancel_right C B A).symm
  have eAC : A - C = -c := (neg_sub C A).symm
  have eBC : B - C = b - c := (sub_sub_sub_cancel_right B C A).symm
  have eAB' : A' - B' = -b' := (neg_sub B' A').symm
  have eCB' : C' - B' = c' - b' := (sub_sub_sub_cancel_right C' B' A').symm
  have eAC' : A' - C' = -c' := (neg_sub C' A').symm
  have eBC' : B' - C' = b' - c' := (sub_sub_sub_cancel_right B' C' A').symm
  rw [eAB, eCB, eAB', eCB', eAC, eBC, eAC', eBC']
  have hcb : ip c b = ip c' b' := by rw [ip_comm, hbc, ip_comm]
  constructor <;> apply angleEq_of_ip_eq <;>
    simp only [ip_neg_left, ip_neg_right, ip_sub_left, ip_sub_right, neg_neg] <;>
    simp only [hAB, hAC, hbc, hcb]

/-- **Axioms IV of congruence without laying off of angles** (IV 1–3, IV 4 reflexivity, IV 5,
IV 6) in the coordinate geometry over a Pythagorean ordered field. -/
instance instTriangleCongruence [IsPythagorean K] :
    TriangleCongruence (Coord K n) (CoordLine K n) :=
  { instSegmentCongruence, instAngleCongruence with ax_IV6 := axiomIV6 }

end Coord

namespace Coord

open AffPt

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-! ### Laying off angles (IV 4) -/

/-- **Orthogonal decomposition** in a plane: if `e₁ ⊥ e₂` are nonzero vectors of the
two-dimensional direction of `S`, every vector `u` of that direction is
`(⟪u, e₁⟫/|e₁|²) e₁ + (⟪u, e₂⟫/|e₂|²) e₂`. -/
theorem orth_decomp {S : AffineSubspace K (Coord K n)} [FiniteDimensional K S.direction]
    (hS : finrank K S.direction = 2) {e1 e2 : Coord K n} (h1 : e1 ∈ S.direction)
    (h2 : e2 ∈ S.direction) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) (horth : ip e2 e1 = 0) {u : Coord K n}
    (hu : u ∈ S.direction) :
    u = (ip u e1 / ip e1 e1) • e1 + (ip u e2 / ip e2 e2) • e2 := by
  have hE1 := ip_self_pos he1
  have hE2 := ip_self_pos he2
  have horth' : ip e1 e2 = 0 := by rw [ip_comm]; exact horth
  have hli : LinearIndependent K ![e1, e2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have k1 := congrArg (fun v => ip v e1) hst
    have k2 := congrArg (fun v => ip v e2) hst
    simp only [ip_add_left, ip_smul_left, horth, horth', ip_zero_left, mul_zero, add_zero,
      zero_add] at k1 k2
    exact ⟨(mul_eq_zero.1 k1).resolve_right hE1.ne', (mul_eq_zero.1 k2).resolve_right hE2.ne'⟩
  have hspan : Submodule.span K (Set.range ![e1, e2]) = S.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; fin_cases i
      · exact h1
      · exact h2
    · rw [finrank_span_eq_card hli, hS]; simp
  rw [← hspan] at hu
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hu
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  subst hc
  simp only [ip_add_left, ip_smul_left, horth, horth', mul_zero, add_zero, zero_add]
  rw [mul_div_cancel_right₀ _ hE1.ne', mul_div_cancel_right₀ _ hE2.ne']

variable [NeZero n]

/-- **Laying off angles** (IV 4) inside a plane `S` of the coordinate geometry over a Pythagorean
ordered field: given a genuine angle `∠AOB`, a line `a'` of `S`, points `O' ≠ A'` of `a'` and a point
`D'` of `S` off `a'`, there is a point `B'` of `S` off `a'` with `∠AOB ≡ ∠A'O'B'` whose interior
(in `S`) lies on the side of `D'`, and the half-ray `O'B'` is unique. -/
theorem layOff_angle_in [IsPythagorean K] {S : AffineSubspace K (Coord K n)}
    [FiniteDimensional K S.direction] (hS : finrank K S.direction = 2) {A O B : Coord K n}
    (hAOB : ¬Collinear A O B) {a' : CoordLine K n} (ha' : a'.carrier ≤ S) {O' A' D' : Coord K n}
    (hO' : O' ∈ a') (hA' : A' ∈ a') (hA'O' : A' ≠ O') (hD'S : D' ∈ S) (hD' : D' ∉ a') :
    ∃ B' : Coord K n, B' ∈ S ∧ B' ∉ a' ∧ AngCong A O B A' O' B' ∧
      (∀ X, X ∈ S → X ∈ Interior A' O' B' → SameSide a' X D') ∧
      ∀ B'', B'' ∈ S → B'' ∉ a' → AngCong A O B A' O' B'' →
        (∀ X, X ∈ S → X ∈ Interior A' O' B'' → SameSide a' X D') → ray O' B'' = ray O' B' := by
  obtain ⟨f, hf⟩ := side_functional_at hS a' ha' hO'
  have hO'S : O' ∈ S := ha' hO'
  have hA'S : A' ∈ S := ha' hA'
  have he1S : A' - O' ∈ S.direction := sub_mem_direction hO'S hA'S
  have hwS : D' - O' ∈ S.direction := sub_mem_direction hO'S hD'S
  have he10 : A' - O' ≠ 0 := sub_ne_zero.2 hA'O'
  have hfe1 : f (A' - O') = 0 := (hf A' hA'S).1 hA'
  have hfw : f (D' - O') ≠ 0 := fun h => hD' ((hf D' hD'S).2 h)
  set e1 := A' - O' with he1
  set w := D' - O' with hw
  set E1 := ip e1 e1 with hE1def
  have hE1 : 0 < E1 := ip_self_pos he10
  set e2 := w - (ip w e1 / E1) • e1 with he2
  have he2S : e2 ∈ S.direction := Submodule.sub_mem _ hwS (Submodule.smul_mem _ _ he1S)
  have hfe2 : f e2 = f w := by rw [he2, map_sub, map_smul, hfe1, smul_zero, sub_zero]
  have he20 : e2 ≠ 0 := fun h => hfw (by rw [← hfe2, h, map_zero])
  have horth : ip e2 e1 = 0 := by
    rw [he2, ip_sub_left, ip_smul_left]; field_simp; ring
  have horth' : ip e1 e2 = 0 := by rw [ip_comm]; exact horth
  set E2 := ip e2 e2 with hE2def
  have hE2 : 0 < E2 := ip_self_pos he20
  set a := A - O with ha
  set b := B - O with hb
  set c := ip a b with hc
  set N := ip a a * ip b b with hN
  have hS0 : 0 < N - c ^ 2 := cauchySchwarz_pos hAOB
  have hNpos : 0 < N := ipN_pos hAOB
  obtain ⟨r, hr0, hr⟩ := IsPythagorean.exists_sqrt_of_isSumSq
    ((isSumSq_cs a b).mul ((isSumSq_ip_self e1).mul (isSumSq_ip_self e2)))
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · exfalso
      have : 0 < (N - c ^ 2) * (E1 * E2) := mul_pos hS0 (mul_pos hE1 hE2)
      rw [← h] at hr
      have h' : (ip a a * ip b b - ip a b ^ 2) * (ip e1 e1 * ip e2 e2) = 0 := by rw [← hr]; ring
      exact this.ne' h'
    · exact h
  set x := c / E1 with hx
  set y := r / (E1 * E2) with hy
  have hypos : 0 < y := div_pos hrpos (mul_pos hE1 hE2)
  have hy2 : y ^ 2 * (E1 * E2) = N - c ^ 2 := by
    rw [hy, div_pow]; field_simp; rw [hr, hN, hc, hE1def, hE2def]; ring
  set v := x • e1 + y • e2 with hv
  have hvS : v ∈ S.direction :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ he1S) (Submodule.smul_mem _ _ he2S)
  have hfv : f v = y * f w := by
    rw [hv, map_add, map_smul, map_smul, hfe1, hfe2, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
  have hv0 : v ≠ 0 := fun h => by
    have : f v = 0 := by rw [h, map_zero]
    rw [hfv] at this
    exact (mul_ne_zero hypos.ne' hfw) this
  have hBS : v + O' ∈ S := add_mem_of_mem_direction hvS hO'S
  have hBsub : v + O' - O' = v := add_sub_cancel_right v O'
  have hBa : v + O' ∉ a' := fun h => by
    have := (hf _ hBS).1 h
    rw [hBsub, hfv] at this
    exact (mul_ne_zero hypos.ne' hfw) this
  have hBO : v + O' ≠ O' := fun h => hv0 (by rw [← hBsub, h, sub_self])
  -- the angle `∠A'O'B'` in terms of `x`, `y`
  have hip1 : ip e1 v = c := by
    rw [hv, ip_add_right, ip_smul_right, ip_smul_right, horth', mul_zero, add_zero, hx]
    exact div_mul_cancel₀ c hE1.ne'
  have hipv : ip v v = N / E1 := by
    rw [hv]
    simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, horth, horth']
    rw [hx]
    field_simp
    linear_combination E1 * hy2
  refine ⟨v + O', hBS, hBa, ?_, ?_, ?_⟩
  · -- the congruence
    rw [angCong_iff, hBsub, ← ha, ← hb, ← he1]
    refine ⟨by rw [hip1], ?_⟩
    rw [hip1, hipv, ← hc, ← hN, ← hE1def]
    field_simp
  · -- the interior lies on the side of `D'`
    intro X hXS hX
    have hl := (hX a' (AffLine.through O' (v + O') hBO.symm) hO' hA'
      (AffLine.left_mem_through _) (AffLine.right_mem_through _)).1
    rw [sameSide_iff_mul_pos ha' hf hXS hBS, hBsub, hfv] at hl
    rw [sameSide_iff_mul_pos ha' hf hXS hD'S]
    have : 0 < y * (f (X - O') * f w) := by linear_combination hl
    exact pos_of_mul_pos_right this hypos.le
  · -- uniqueness of the half-ray
    intro B'' hB''S hB''a hcong hint
    set u := B'' - O' with hu
    have huS : u ∈ S.direction := sub_mem_direction hO'S hB''S
    have hfu : f u ≠ 0 := fun h => hB''a ((hf B'' hB''S).2 h)
    have hB''O : B'' ≠ O' := fun h => hB''a (h ▸ hO')
    -- an interior point of `∠A'O'B''`
    have hX0S : e1 + u + O' ∈ S :=
      add_mem_of_mem_direction (Submodule.add_mem _ he1S huS) hO'S
    have hX0sub : e1 + u + O' - O' = e1 + u := add_sub_cancel_right _ O'
    have hX0 : e1 + u + O' ∈ Interior A' O' B'' := by
      intro l m hO'l hA'l hO'm hB''m
      have hla : l = a' := line_unique hA'O'.symm hO'l hA'l hO' hA'
      subst hla
      have hm : m = AffLine.through O' B'' hB''O.symm := m.eq_through hB''O.symm hO'm hB''m
      have hmS : m.carrier ≤ S := by
        rw [hm]; show affineSpan K _ ≤ S
        rw [affineSpan_le]; intro z hz
        rcases hz with rfl | hz
        · exact hO'S
        · rw [Set.mem_singleton_iff] at hz; subst hz; exact hB''S
      obtain ⟨g, hg⟩ := side_functional_at hS m hmS hO'm
      have hgu : g u = 0 := (hg B'' hB''S).1 hB''m
      have hge1 : g e1 ≠ 0 := fun h => by
        have hA'm : A' ∈ m := (hg A' hA'S).2 h
        have : m = l := line_unique hA'O'.symm hO'm hA'm hO' hA'
        exact hB''a (this ▸ hB''m)
      refine ⟨?_, ?_⟩
      · rw [sameSide_iff_mul_pos ha' hf hX0S hB''S, hX0sub, map_add, hfe1, zero_add]
        exact mul_self_pos.2 hfu
      · rw [sameSide_iff_mul_pos hmS hg hX0S hA'S, hX0sub, map_add, hgu, add_zero]
        exact mul_self_pos.2 hge1
    have hside := hint _ hX0S hX0
    rw [sameSide_iff_mul_pos ha' hf hX0S hD'S, hX0sub, map_add, hfe1, zero_add] at hside
    -- coordinates of `u`
    have hdec := orth_decomp hS he1S he2S he10 he20 horth huS
    set x'' := ip u e1 / E1 with hx''
    set y'' := ip u e2 / E2 with hy''
    have hfu' : f u = y'' * f w := by
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, hfe1, hfe2, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
    have hy''pos : 0 < y'' := by
      rw [hfu'] at hside
      have : 0 < y'' * (f w * f w) := by linear_combination hside
      exact pos_of_mul_pos_left this (mul_self_nonneg _)
    have hip1u : ip e1 u = x'' * E1 := by
      conv_lhs => rw [hdec]
      rw [ip_add_right, ip_smul_right, ip_smul_right, horth', mul_zero, add_zero]
    have hipu : ip u u = x'' ^ 2 * E1 + y'' ^ 2 * E2 := by
      conv_lhs => rw [hdec]
      simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, horth, horth']
      ring
    rw [angCong_iff, ← hu, ← ha, ← hb, ← he1] at hcong
    obtain ⟨hsg, heq⟩ := hcong
    rw [hip1u, hipu, ← hc, ← hN, ← hE1def] at heq
    rw [hip1u, ← hc] at hsg
    -- `x'' y E1 = y'' c`
    have hkey : x'' * y * E1 = y'' * c := by
      apply eq_of_sq_eq_of_sign_eq
      · apply mul_left_cancel₀ (mul_pos hE1 hE2).ne'
        linear_combination (x'' ^ 2 * E1 ^ 2) * hy2 - heq
      · rw [sign_mul, sign_mul, sign_mul, sign_pos hypos, sign_pos hE1, sign_pos hy''pos,
          mul_one, mul_one, one_mul, hsg, sign_mul, sign_pos hE1, mul_one]
    have huv : u = (y'' / y) • v := by
      rw [hdec, hv, smul_add, smul_smul, smul_smul]
      congr 2
      · rw [hx]; field_simp; linear_combination hkey
      · field_simp
    exact ray_eq_of_pos_smul hBO (div_pos hy''pos hypos) (by rw [hBsub]; exact huv)

end Coord

namespace Coord

open AffPt

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Axioms IV 4–5 of plane geometry** in the coordinate plane `K²` over a Pythagorean ordered
field. -/
instance instPlaneAngleCongruence [IsPythagorean K] :
    PlaneAngleCongruence (Coord K 2) (CoordLine K 2) :=
  { AffPt.instPlaneOrder, instAngleCongruence with
    ax_IV4 := fun A O B a' O' A' D' h hO' hA' hA'O' hD' => by
      have := finiteDimensional_of_fact (K := K) (V := Fin 2 → K) (n := 1)
      obtain ⟨B', -, hB'a, hc, hint, huniq⟩ := layOff_angle_in (S := ⊤) finrank_top_direction h
        le_top hO' hA' hA'O' (AffineSubspace.mem_top K _ D') hD'
      exact ⟨B', hB'a, hc, fun X hX => hint X (AffineSubspace.mem_top K _ X) hX,
        fun B'' h1 h2 h3 => huniq B'' (AffineSubspace.mem_top K _ B'') h1 h2
          (fun X _ hX => h3 X hX)⟩ }

/-- **Axioms IV 4–5 of space geometry** in the coordinate space `K³` over a Pythagorean ordered
field. -/
instance instSpaceAngleCongruence [IsPythagorean K] :
    SpaceAngleCongruence (Coord K 3) (CoordLine K 3) (CoordPlane K 3) :=
  { AffPt.instSpaceOrder, instAngleCongruence with
    ax_IV4 := fun _ _ _ α' _ _ _ _ h ha' hO' hA' hA'O' hD'α hD' =>
      layOff_angle_in α'.finrank_direction h (liesInPlane_iff.1 ha') hO' hA' hA'O' hD'α hD' }

/-- **Groups I, II, IV of plane geometry** in `K²`, `K` Pythagorean. -/
instance instPlaneCongruence [IsPythagorean K] : PlaneCongruence (Coord K 2) (CoordLine K 2) :=
  { instPlaneAngleCongruence, instTriangleCongruence with }

/-- **Groups I, II, IV of space geometry** in `K³`, `K` Pythagorean. -/
instance instSpaceCongruence [IsPythagorean K] :
    SpaceCongruence (Coord K 3) (CoordLine K 3) (CoordPlane K 3) :=
  { instSpaceAngleCongruence, instTriangleCongruence with }

/-! ### Archimedes's axiom (V) -/

variable {n : ℕ}

/-- **Archimedes's axiom** (V) in the coordinate geometry over an archimedean ordered field. -/
theorem axiomV [Archimedean K] : AxiomV (Coord K n) := by
  intro P B h01 hstep hcong
  have hP01 : P 0 ≠ P 1 := ne12_of_between (Line := CoordLine K n) h01
  set d := P 1 - P 0 with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hP01.symm
  have hdiff : ∀ k : ℕ, P (k + 1) - P k = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show P (k + 2) - P (k + 1) = d
      obtain ⟨hne, t, ht0, ht1, ht⟩ := sbtw_iff_param.1 (hstep k)
      have hc : ip (P (k + 2) - P (k + 1)) (P (k + 2) - P (k + 1)) =
          ip (P (k + 1) - P k) (P (k + 1) - P k) := hcong (k + 1) k
      have hu0 : P (k + 1) - P k ≠ 0 := by rw [ih]; exact hd0
      -- `u = t (u + w)`
      have hu : P (k + 1) - P k = t • ((P (k + 2) - P (k + 1)) + (P (k + 1) - P k)) := by
        rw [sub_add_sub_cancel]; rw [ht]; abel
      have hw : P (k + 2) - P (k + 1) = ((1 - t) / t) • (P (k + 1) - P k) := by
        have e : t • (P (k + 2) - P (k + 1)) = (1 - t) • (P (k + 1) - P k) := by
          calc t • (P (k + 2) - P (k + 1))
              = t • ((P (k + 2) - P (k + 1)) + (P (k + 1) - P k)) - t • (P (k + 1) - P k) := by
                rw [smul_add]; abel
            _ = (P (k + 1) - P k) - t • (P (k + 1) - P k) := by rw [← hu]
            _ = (1 - t) • (P (k + 1) - P k) := by rw [sub_smul, one_smul]
        rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← e, smul_smul, inv_mul_cancel₀ ht0.ne',
          one_smul]
      rw [hw, ip_smul_left, ip_smul_right] at hc
      have hq : ((1 - t) / t) ^ 2 = 1 := by
        apply mul_right_cancel₀ (ip_self_pos hu0).ne'
        linear_combination hc
      have hq1 : (1 - t) / t = 1 :=
        (pow_left_inj₀ (div_pos (sub_pos.2 ht1) ht0).le zero_le_one two_ne_zero).1
          (by rw [hq, one_pow])
      rw [hw, hq1, one_smul, ih]
  have hpos : ∀ k : ℕ, P k = (k : K) • d + P 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show P (k + 1) = (P (k + 1) - P k) + P k by abel, hdiff k, ih, Nat.cast_succ, add_smul,
        one_smul]; abel
  obtain ⟨-, t, ht0, ht1, ht⟩ := sbtw_iff_param.1 h01
  have hB : B = t⁻¹ • d + P 0 := by
    have : d = t • (B - P 0) := by rw [hd, ht, add_sub_cancel_right]
    rw [this, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, sub_add_cancel]
  obtain ⟨N, hN⟩ := exists_nat_gt t⁻¹
  refine ⟨N, ?_⟩
  have key := (sbtw_param_iff hd0 (0 : K) t⁻¹ N (O := P 0)).2 (Or.inl ⟨inv_pos.2 ht0, hN⟩)
  rw [zero_smul, zero_add] at key
  rw [between_iff, hB, hpos N]
  exact key

/-- **Archimedes's axiom** in the coordinate geometry over an archimedean ordered field. -/
instance instArchimedes [Archimedean K] : Archimedes (Coord K n) (CoordLine K n) :=
  { AffPt.instLineOrder with ax_V := axiomV }

/-- **All axioms I–V of plane geometry** hold in `K²` for a Pythagorean archimedean ordered
field `K`. -/
instance instPlaneGeometry [IsPythagorean K] [Archimedean K] :
    PlaneGeometry (Coord K 2) (CoordLine K 2) :=
  { AffPt.instPlaneParallels, instPlaneCongruence, instArchimedes with }

/-- **All axioms I–V of space geometry** hold in `K³` for a Pythagorean archimedean ordered
field `K`. -/
instance instSpaceGeometry [IsPythagorean K] [Archimedean K] :
    SpaceGeometry (Coord K 3) (CoordLine K 3) (CoordPlane K 3) :=
  { AffPt.instSpaceParallels, instSpaceCongruence, instArchimedes with }

example : SpaceGeometry (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) := inferInstance
example : PlaneGeometry (Coord ℝ 2) (CoordLine ℝ 2) := inferInstance

end Coord

end HilbertFoundations
