import HilbertFoundations.AreasAux5

/-!
# Helper module for `Areas.lean`: equal area with Archimedes's axiom, Euclid's parallelograms

This module contains no unit of Hilbert's text. Over a linearly ordered field `K`:

* **Euclid's parallelograms with overlapping tops** (`euclid_area_small`): two parallelograms
  `abcd`, `abc'd'` on the same base and between the same parallels, with `d' = d + μ (b - a)`,
  `0 < μ < 1`, are of equal **area** (both are the trapezoid `abcd'` plus one of the congruent
  triangles `ad'd`, `bc'c`);
* the **small shear** (`shear_area_small`): moving the vertex `c` of a triangle parallel to `ab`
  by less than twice `ab` gives a triangle of equal area (Theorem 26 twice and
  `euclid_area_small`);
* the **shear** over an archimedean field (`shear_area`): finitely many small shears;
* a triangle congruent to a given one on a given base with a prescribed signed area
  (`exists_congr_apex`, rational in the co-ordinates: no square roots are needed), and the apex
  of a triangle with the same base and the same signed area is a shear of the apex
  (`eq_shift_of_det3`);
* **equal bases and altitudes give equal area over an archimedean field**
  (`eqArea_of_base_height`), the positive half of Hilbert's remark in § 19;
* **two parallelograms with equal bases and altitudes are of equal content** by Euclid's
  reasoning (`parallelograms_eqContent`): a motion carries one onto the base of the other, and
  `euclid_K` (Fig. 30) applies.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem shift_shift (c a b : K × K) (x y : K) :
    shift (shift c a b x) a b y = shift c a b (x + y) := by
  simp only [shift]; refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem shift_zero (c a b : K × K) : shift c a b 0 = c := by
  simp only [shift]; refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem det3_shift (a b c : K × K) (μ : K) : det3 a b (shift c a b μ) = det3 a b c := by
  simp only [shift, det3]; ring

/-- **Euclid's parallelograms with overlapping tops are of equal area**: `abcd` and `abc'd'`
(`d' = d + μ (b - a)`, `0 < μ < 1`) are decomposed into `abc, acd', ad'd` and `abc, acd', bc'c`,
and `ad'd ≡ bc'c`. -/
theorem euclid_area_small {a b d : K × K} (hD : det3 a b d ≠ 0) {μ : K} (hμ : 0 < μ)
    (hμ1 : μ < 1) :
    KEqArea (parReg a b (par4 a b d) d)
      (parReg a b (par4 a b (shift d a b μ)) (shift d a b μ)) := by
  set c := par4 a b d with hc
  set d' := shift d a b μ with hd'
  set c' := par4 a b d' with hc'
  set D := det3 a b d with hDd
  have hμ1p : 0 < μ + 1 := by linarith
  have hμne : μ ≠ 0 := hμ.ne'
  have hD' : det3 a b d' ≠ 0 := by rw [hd', det3_shift]; exact hD
  -- non-degeneracy
  have nabc : (Tr.mk a b c).nd := ne_of_eq (k := 1)
    (by simp only [hc, hDd, par4, Tr.D, det3]; ring) one_ne_zero hD
  have nacd : (Tr.mk a c d).nd := ne_of_eq (k := 1)
    (by simp only [hc, hDd, par4, Tr.D, det3]; ring) one_ne_zero hD
  have nabc' : (Tr.mk a b c').nd := ne_of_eq (k := 1)
    (by simp only [hc', hd', hDd, par4, shift, Tr.D, det3]; ring) one_ne_zero hD
  have nac'd' : (Tr.mk a c' d').nd := ne_of_eq (k := 1)
    (by simp only [hc', hd', hDd, par4, shift, Tr.D, det3]; ring) one_ne_zero hD
  have nac'c : (Tr.mk a c' c).nd := ne_of_eq (k := μ)
    (by simp only [hc, hc', hd', hDd, par4, shift, Tr.D, det3]; ring) hμne hD
  have nbc'c : (Tr.mk b c' c).nd := ne_of_eq (k := μ)
    (by simp only [hc, hc', hd', hDd, par4, shift, Tr.D, det3]; ring) hμne hD
  have hbc : b ≠ c := Tr.nd_ne_bc nabc
  have hac' : a ≠ c' := fun h => Tr.nd_ne_ca nabc' h.symm
  -- the first parallelogram: `abc`, `acd'`, `ad'd`
  have dP1 : DecS (parReg a b c d) ([Tr.mk a b c] ++ [Tr.mk a c d]) := decS_parReg hD
  have sp1 : DecS (Tr.mk a c d).mem [Tr.mk a c d', Tr.mk a d' d] := by
    have h := split nacd (s := 1 - μ) (by linarith) (by linarith)
    have e : lerp (1 - μ) (Tr.mk a c d).b (Tr.mk a c d).c = d' := by
      simp only [hc, hd', par4, shift, lerp]
      refine Prod.ext ?_ ?_ <;> simp only <;> ring
    rw [e] at h
    exact h
  have dP1' : DecS (parReg a b c d) ([Tr.mk a b c] ++ [Tr.mk a c d', Tr.mk a d' d]) :=
    dP1.append_of (DecS.single nabc) (DecS.single nacd) (DecS.single nabc) sp1
  -- the second parallelogram: `abc'`, `ac'c`, `acd'`, then `abc`, `bc'c`, `acd'`
  have dP2 : DecS (parReg a b c' d') ([Tr.mk a b c'] ++ [Tr.mk a c' d']) := decS_parReg hD'
  have sp2 : DecS (Tr.mk a c' d').mem [Tr.mk a c' c, Tr.mk a c d'] := by
    have h := split nac'd' (s := μ) hμ hμ1
    have e : lerp μ (Tr.mk a c' d').b (Tr.mk a c' d').c = c := by
      simp only [hc, hc', hd', par4, shift, lerp]
      refine Prod.ext ?_ ?_ <;> simp only <;> ring
    rw [e] at h
    exact h
  have dP2a : DecS (parReg a b c' d') ([Tr.mk a b c'] ++ [Tr.mk a c' c, Tr.mk a c d']) :=
    dP2.append_of (DecS.single nabc') (DecS.single nac'd') (DecS.single nabc') sp2
  have dP2' : DecS (parReg a b c' d') ([Tr.mk a b c', Tr.mk a c' c] ++ [Tr.mk a c d']) := dP2a
  set Q : K × K → Prop := fun p => (Tr.mk a b c').mem p ∨ (Tr.mk a c' c).mem p with hQ
  have dQ1 : DecS Q [Tr.mk a b c', Tr.mk a c' c] := by
    refine ⟨fun r hr => ?_, ?_, fun p => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact nabc'
      · exact nac'c
    · rw [List.pairwise_pair]
      exact sep' nabc' nac'c hac' (κ := D) hD
        (nonpos_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
        (nonpos_of_eq (k := -1) (by simp only [hc', hd', hDd, par4, shift, det3]; ring)
          (by norm_num))
        (nonpos_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
        (nonneg_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
        (nonneg_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
        (nonneg_of_eq (k := μ) (by simp only [hc, hc', hd', hDd, par4, shift, det3]; ring)
          hμ.le)
    · simp [hQ]
  have ds : ∀ p, ((Tr.mk a b c').mem p ∨ (Tr.mk a c' c).mem p) ↔
      ((Tr.mk a b c).mem p ∨ (Tr.mk b c' c).mem p) := by
    intro p
    refine diag_swap (s := 1 / (μ + 1)) (r := 1 / (μ + 1)) (div_pos one_pos hμ1p)
      ((div_lt_one hμ1p).2 (by linarith)) (div_pos one_pos hμ1p)
      ((div_lt_one hμ1p).2 (by linarith)) ?_ ?_ ?_ ?_ ?_ p
    · simp only [hc, hc', hd', par4, shift, lerp]
      refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
    · exact ne_of_eq (k := -1) (by simp only [hc', hd', hDd, par4, shift, Tr.D, det3]; ring)
        (by norm_num) hD
    · exact ne_of_eq (k := μ) (by simp only [hc, hc', hd', hDd, par4, shift, Tr.D, det3]; ring)
        hμne hD
    · exact nabc
    · exact ne_of_eq (k := -μ) (by simp only [hc, hc', hd', hDd, par4, shift, Tr.D, det3]; ring)
        (neg_ne_zero.2 hμne) hD
  have dQ2 : DecS Q [Tr.mk a b c, Tr.mk b c' c] := by
    refine ⟨fun r hr => ?_, ?_, fun p => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact nabc
      · exact nbc'c
    · rw [List.pairwise_pair]
      exact sep nabc nbc'c hbc (κ := D) hD
        (nonneg_of_eq (k := 1) (by simp only [hc, hDd, par4, det3]; ring) zero_le_one)
        (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
        (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
        (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
        (nonpos_of_eq (k := -μ) (by simp only [hc, hc', hd', hDd, par4, shift, det3]; ring)
          (by linarith))
        (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
    · simp only [hQ, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left]
      exact ds p
  have dP2'' : DecS (parReg a b c' d') ([Tr.mk a b c, Tr.mk b c' c] ++ [Tr.mk a c d']) :=
    dP2'.append_of dQ1 (DecS.single (by
      exact ne_of_eq (k := 1 - μ) (by simp only [hc, hd', hDd, par4, shift, Tr.D, det3]; ring)
        (by linarith) hD)) dQ2 (DecS.single (by
      exact ne_of_eq (k := 1 - μ) (by simp only [hc, hd', hDd, par4, shift, Tr.D, det3]; ring)
        (by linarith) hD))
  have dP2''' : DecS (parReg a b c' d') [Tr.mk a b c, Tr.mk a c d', Tr.mk b c' c] :=
    dP2''.perm (show List.Perm ([Tr.mk a b c, Tr.mk b c' c] ++ [Tr.mk a c d'])
      [Tr.mk a b c, Tr.mk a c d', Tr.mk b c' c] from (List.Perm.swap _ _ _).cons _)
  have cg : KCong (Tr.mk a d' d) (Tr.mk b c' c) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [sqd, hc, hc', hd', par4, shift] <;> ring
  exact ⟨_, _, dP1', dP2''', List.Forall₂.cons (KCong.refl _)
    (List.Forall₂.cons (KCong.refl _) (List.Forall₂.cons cg List.Forall₂.nil))⟩

/-- **The small shear keeps the area**: for `0 < μ < 2`, the triangles `abc` and `abc₂`,
`c₂ = c + μ (b - a)`, are of equal area (Theorem 26 twice and Euclid's parallelograms with
overlapping tops). -/
theorem shear_area_small {a b c : K × K} (hD : det3 a b c ≠ 0) {μ : K} (hμ : 0 < μ)
    (hμ2 : μ < 2) :
    KEqArea (Tr.mk a b c).mem (Tr.mk a b (shift c a b μ)).mem := by
  set c₂ := shift c a b μ with hc₂
  have hD₂ : det3 a b c₂ ≠ 0 := by rw [hc₂, det3_shift]; exact hD
  obtain ⟨d1, d2, d3⟩ := th26_K hD
  obtain ⟨e1, e2, e3⟩ := th26_K hD₂
  set dd := lerp (1 / 2) c a with hdd
  have hf1 : refl2 (lerp (1 / 2) b c) dd = par4 a b dd := by
    simp only [hdd, refl2, par4, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
  have hd2 : lerp (1 / 2) c₂ a = shift dd a b (μ / 2) := by
    simp only [hdd, hc₂, shift, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
  have hf2 : refl2 (lerp (1 / 2) b c₂) (lerp (1 / 2) c₂ a) =
      par4 a b (shift dd a b (μ / 2)) := by
    simp only [hdd, hc₂, refl2, par4, shift, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
  rw [hf1] at d2 d3
  rw [hd2] at e1
  rw [hf2, hd2] at e2 e3
  have a1 : KEqArea (Tr.mk a b c).mem (parReg a b (par4 a b dd) dd) := ⟨_, _, d1, d2, d3⟩
  have a2 : KEqArea (Tr.mk a b c₂).mem
      (parReg a b (par4 a b (shift dd a b (μ / 2))) (shift dd a b (μ / 2))) :=
    ⟨_, _, e1, e2, e3⟩
  have hDd : det3 a b dd ≠ 0 := ne_of_eq (k := 1 / 2) (by simp only [hdd, lerp, det3]; ring)
    (by norm_num) hD
  have a3 := euclid_area_small hDd (μ := μ / 2) (by linarith) (by linarith)
  exact KEqArea.trans (KEqArea.trans a1 a3.symm) a2

/-- A shear by less than twice the base, in either direction. -/
theorem shear_area_step {a b c : K × K} (hD : det3 a b c ≠ 0) {ν : K} (hν : |ν| < 2) :
    KEqArea (Tr.mk a b c).mem (Tr.mk a b (shift c a b ν)).mem := by
  rcases lt_trichotomy ν 0 with h | rfl | h
  · have hD' : det3 a b (shift c a b ν) ≠ 0 := by rw [det3_shift]; exact hD
    have := shear_area_small hD' (μ := -ν) (by linarith)
      (by rw [abs_of_neg h] at hν; exact hν)
    rw [shift_shift, add_neg_cancel, shift_zero] at this
    exact this.symm
  · rw [shift_zero]; exact KEqArea.refl (DecS.single (t := Tr.mk a b c) hD)
  · exact shear_area_small hD h (by rw [abs_of_pos h] at hν; exact hν)

/-- **The shear keeps the area over an archimedean field**: finitely many small shears. -/
theorem shear_area [Archimedean K] {a b c : K × K} (hD : det3 a b c ≠ 0) (μ : K) :
    KEqArea (Tr.mk a b c).mem (Tr.mk a b (shift c a b μ)).mem := by
  obtain ⟨n, hn⟩ := exists_nat_gt |μ|
  have hn0 : (0 : K) < n := lt_of_le_of_lt (abs_nonneg μ) hn
  set ν := μ / n with hν
  have hνlt : |ν| < 2 := by
    rw [hν, abs_div, Nat.abs_cast, div_lt_iff₀ hn0]; linarith
  have key : ∀ k : ℕ, KEqArea (Tr.mk a b c).mem (Tr.mk a b (shift c a b (k * ν))).mem := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul, shift_zero]
      exact KEqArea.refl (DecS.single (t := Tr.mk a b c) hD)
    | succ k ih =>
      have hDk : det3 a b (shift c a b (k * ν)) ≠ 0 := by rw [det3_shift]; exact hD
      have step := shear_area_step hDk hνlt
      rw [shift_shift, show (k : K) * ν + ν = ((k + 1 : ℕ) : K) * ν by push_cast; ring] at step
      exact KEqArea.trans ih step.symm
  have := key n
  rwa [hν, mul_div_cancel₀ _ hn0.ne'] at this

theorem sq_ne_zero_of_ne {b c : K × K} (hbc : b ≠ c) :
    (c.1 - b.1) * (c.1 - b.1) + (c.2 - b.2) * (c.2 - b.2) ≠ 0 := by
  intro h0
  apply hbc
  have h1 : c.1 - b.1 = 0 := by
    nlinarith [mul_self_nonneg (c.1 - b.1), mul_self_nonneg (c.2 - b.2)]
  have h2 : c.2 - b.2 = 0 := by
    nlinarith [mul_self_nonneg (c.1 - b.1), mul_self_nonneg (c.2 - b.2)]
  exact Prod.ext (by linarith) (by linarith)

/-- **A congruent copy on a given base with a prescribed signed area**: if `bc ≡ b'c'` and
`Y² = (det3 b' c' a')²`, there is `a''` with `bca'' ≡ b'c'a'` and `det3 b c a'' = Y`. (The
apex is `b + (X (c - b) + Y (c - b)^⊥) / |c - b|²`, `X = (a' - b') · (c' - b')`: no square root
is needed.) -/
theorem exists_congr_apex {b c b' c' a' : K × K} (hbc : b ≠ c) (hs : sqd b c = sqd b' c')
    {Y : K} (hY : Y * Y = det3 b' c' a' * det3 b' c' a') :
    ∃ a'' : K × K, KCong (Tr.mk b c a'') (Tr.mk b' c' a') ∧ det3 b c a'' = Y := by
  obtain ⟨S, hSdef⟩ : ∃ S : K, S = (c.1 - b.1) * (c.1 - b.1) + (c.2 - b.2) * (c.2 - b.2) :=
    ⟨_, rfl⟩
  have hS : S ≠ 0 := by rw [hSdef]; exact sq_ne_zero_of_ne hbc
  obtain ⟨X, hXdef⟩ : ∃ X : K, X = (a'.1 - b'.1) * (c'.1 - b'.1) + (a'.2 - b'.2) * (c'.2 - b'.2) :=
    ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : K, x * S = X * (c.1 - b.1) - Y * (c.2 - b.2) :=
    ⟨(X * (c.1 - b.1) - Y * (c.2 - b.2)) / S, div_mul_cancel₀ _ hS⟩
  obtain ⟨y, hy⟩ : ∃ y : K, y * S = X * (c.2 - b.2) + Y * (c.1 - b.1) :=
    ⟨(X * (c.2 - b.2) + Y * (c.1 - b.1)) / S, div_mul_cancel₀ _ hS⟩
  have hs' : S = (c'.1 - b'.1) * (c'.1 - b'.1) + (c'.2 - b'.2) * (c'.2 - b'.2) := by
    rw [hSdef]; unfold sqd at hs; linear_combination hs
  unfold det3 at hY
  -- `x² + y² = |a' - b'|²`
  have h1 : x * x + y * y = (b'.1 - a'.1) * (b'.1 - a'.1) + (b'.2 - a'.2) * (b'.2 - a'.2) := by
    apply mul_right_cancel₀ (mul_ne_zero hS hS)
    linear_combination (x * S + X * (c.1 - b.1) - Y * (c.2 - b.2)) * hx +
      (y * S + X * (c.2 - b.2) + Y * (c.1 - b.1)) * hy - (X * X + Y * Y) * hSdef + S * hY +
      S * (X + ((a'.1 - b'.1) * (c'.1 - b'.1) + (a'.2 - b'.2) * (c'.2 - b'.2))) * hXdef -
      ((b'.1 - a'.1) * (b'.1 - a'.1) + (b'.2 - a'.2) * (b'.2 - a'.2)) * S * hs'
  -- `(c - b) · (a'' - b) = X`
  have h2 : (c.1 - b.1) * x + (c.2 - b.2) * y = X := by
    apply mul_right_cancel₀ hS
    linear_combination (c.1 - b.1) * hx + (c.2 - b.2) * hy - X * hSdef
  -- `(c - b) × (a'' - b) = Y`
  have h3 : (c.1 - b.1) * y - (c.2 - b.2) * x = Y := by
    apply mul_right_cancel₀ hS
    linear_combination (c.1 - b.1) * hy - (c.2 - b.2) * hx - Y * hSdef
  refine ⟨(b.1 + x, b.2 + y), ⟨hs, ?_, ?_⟩, ?_⟩
  · simp only [sqd]; linear_combination h1
  · simp only [sqd]
    linear_combination h1 - 2 * h2 - 2 * hXdef - hSdef + hs'
  · simp only [det3]; linear_combination h3

/-- **Same base, same signed area: the apex is sheared** parallel to the base. -/
theorem eq_shift_of_det3 {b c a a'' : K × K} (hbc : b ≠ c) (h : det3 b c a'' = det3 b c a) :
    ∃ μ : K, a'' = shift a b c μ := by
  have hS := sq_ne_zero_of_ne hbc
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ * ((c.1 - b.1) * (c.1 - b.1) + (c.2 - b.2) * (c.2 - b.2)) =
      (c.1 - b.1) * (a''.1 - a.1) + (c.2 - b.2) * (a''.2 - a.2) :=
    ⟨_, div_mul_cancel₀ _ hS⟩
  unfold det3 at h
  refine ⟨μ, Prod.ext ?_ ?_⟩ <;> simp only [shift] <;> apply mul_right_cancel₀ hS
  · linear_combination (-(c.2 - b.2)) * h - (c.1 - b.1) * hμ
  · linear_combination (c.1 - b.1) * h - (c.2 - b.2) * hμ

/-- **Equal bases and equal altitudes give equal area over an archimedean field**: if
`bc ≡ b'c'` and `|det3 b c a| = |det3 b' c' a'|` (equal products of base and altitude), the
triangles `bca` and `b'c'a'` are of equal area: a congruent copy of `b'c'a'` on the base `bc`
on the side of `a`, then a shear. -/
theorem eqArea_of_base_height [Archimedean K] {a b c a' b' c' : K × K} (hD : det3 b c a ≠ 0)
    (hs : sqd b c = sqd b' c') (hh : |det3 b c a| = |det3 b' c' a'|) :
    KEqArea (Tr.mk b c a).mem (Tr.mk b' c' a').mem := by
  have hbc : b ≠ c := Tr.nd_ne_ab (t := Tr.mk b c a) hD
  have hY : det3 b c a * det3 b c a = det3 b' c' a' * det3 b' c' a' := by
    rw [← abs_mul_abs_self, hh, abs_mul_abs_self]
  obtain ⟨a'', hc, hd⟩ := exists_congr_apex hbc hs hY
  obtain ⟨μ, hμ⟩ := eq_shift_of_det3 hbc hd
  have h1 : KEqArea (Tr.mk b c a).mem (Tr.mk b c a'').mem := by
    rw [hμ]; exact shear_area hD μ
  have nd'' : (Tr.mk b c a'').nd := by show det3 b c a'' ≠ 0; rw [hd]; exact hD
  have h2 : KEqArea (Tr.mk b c a'').mem (Tr.mk b' c' a').mem :=
    ⟨_, _, DecS.single nd'', DecS.single (hc.nd nd''), List.Forall₂.cons hc List.Forall₂.nil⟩
  exact KEqArea.trans h1 h2.symm

theorem KIso.app_par4 (φ : KIso K) (a b d : K × K) :
    φ.app (par4 a b d) = par4 (φ.app a) (φ.app b) (φ.app d) := by
  unfold KIso.app par4; ext <;> simp only <;> ring

/-- **Euclid's reasoning for Theorem 25**: two parallelograms `abcd`, `a'b'c'd'` with `ab ≡ a'b'`
and `|det3 a b d| = |det3 a' b' d'|` (equal products of base and altitude) are of equal content.
A motion carries `a'b'c'd'` to a parallelogram `abc''x` on the base `ab`, on the side of `d`
(equal area); `x` lies on the parallel `dc` (equal signed area), and Euclid's parallelograms on
the same base and between the same parallels are of equal content (`euclid_K`, Fig. 30). -/
theorem parallelograms_eqContent {a b d a' b' d' : K × K} (hD : det3 a b d ≠ 0)
    (hs : sqd a b = sqd a' b') (hh : |det3 a b d| = |det3 a' b' d'|) :
    KEqContent (parReg a b (par4 a b d) d) (parReg a' b' (par4 a' b' d') d') := by
  have hab : a ≠ b := Tr.nd_ne_ab (t := Tr.mk a b d) hD
  have hY : det3 a b d * det3 a b d = det3 a' b' d' * det3 a' b' d' := by
    rw [← abs_mul_abs_self, hh, abs_mul_abs_self]
  obtain ⟨x, hc, hx⟩ := exists_congr_apex hab hs hY
  obtain ⟨μ, hμ⟩ := eq_shift_of_det3 hab hx
  have hDx : det3 a b x ≠ 0 := by rw [hx]; exact hD
  have hD' : det3 a' b' d' ≠ 0 := hc.nd (r := Tr.mk a b x) hDx
  obtain ⟨φ, hφ⟩ := exists_iso (r := Tr.mk a' b' d') hD' hc.symm
  have ha : φ.app a' = a := congrArg Tr.a hφ
  have hb : φ.app b' = b := congrArg Tr.b hφ
  have hd : φ.app d' = x := congrArg Tr.c hφ
  have dP' := decS_parReg hD'
  have dI := dP'.mapI φ
  simp only [List.map_cons, List.map_nil, Tr.mapI, KIso.app_par4, ha, hb, hd] at dI
  have dX := decS_parReg hDx
  have e1 : KEqArea (parReg a' b' (par4 a' b' d') d') (parReg a b (par4 a b x) x) := by
    obtain ⟨l, m, hl, hm, hcg⟩ := KEqArea.mapI dP' φ
    exact ⟨l, m, hl, hm.congr (fun p => (dI.2.2 p).trans (dX.2.2 p).symm), hcg⟩
  have e2 : KEqContent (parReg a b (par4 a b d) d) (parReg a b (par4 a b x) x) := by
    rw [hμ]; exact euclid_K hD μ
  have e3 := e1.symm.toContent ⟨_, by simp, dX⟩
  exact KEqContent.trans e2 e3.symm

end Areas

end HilbertFoundations
