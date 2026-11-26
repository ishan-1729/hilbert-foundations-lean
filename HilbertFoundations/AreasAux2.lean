import HilbertFoundations.AreasAux1

/-!
# Helper module for `Areas.lean`: additivity of the measure of area

This module contains no unit of Hilbert's text. Over a linearly ordered field `K`:

* the **one-dimensional lemma** (`sum_len_cover`): if a closed interval is covered by finitely
  many closed intervals with pairwise disjoint interiors, lying in it, the lengths add up;
* the **vertical sections** of a triangle (`secLo`, `secHi`, `secLen`): at an abscissa which is not
  the abscissa of a vertex, the section of a non-degenerate triangle is empty or a non-degenerate
  closed interval whose interior points are interior points of the triangle (`section_interval`);
* the **midpoint sums** `msum f s = Σ (b - a) f ((a + b) / 2)` over consecutive points of a sorted
  list, which integrate the section lengths exactly (`msum_secLen`: `|D| / 2`);
* **additivity** (`area_additive`): if a non-degenerate triangle is decomposed into triangles
  (`DecS`), `|D|` is the sum of the `|D|` of the pieces; and the **common refinement** of two
  decompositions of one region (`common_refinement`), whence the sum of the `|D|` over a
  decomposition only depends on the region (`decS_sum_eq`).

The proof of additivity is not Hilbert's (§ 20, by transversals from a vertex); it integrates the
lengths of the vertical sections, which is possible in any ordered field because these lengths
are affine between consecutive abscissae of vertices.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### The one-dimensional lemma -/

theorem sum_len_cover_aux (n : ℕ) : ∀ (l : List (K × K)), l.length = n → ∀ lo hi : K, lo < hi →
    (∀ q ∈ l, lo ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ hi) →
    l.Pairwise (fun p q => q.2 ≤ p.1 ∨ p.2 ≤ q.1) →
    (∀ y, lo < y → y < hi → ∃ q ∈ l, q.1 ≤ y ∧ y ≤ q.2) →
    (l.map (fun q => q.2 - q.1)).sum = hi - lo := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn lo hi hlt hsub hdisj hcov
  have hne : l.toFinset.Nonempty := by
    obtain ⟨q, hq, -⟩ := hcov ((lo + hi) / 2) (by linarith) (by linarith)
    exact ⟨q, List.mem_toFinset.2 hq⟩
  obtain ⟨k, hk, hmin⟩ := l.toFinset.exists_min_image (fun q => q.1) hne
  rw [List.mem_toFinset] at hk
  have hk1 : k.1 = lo := by
    by_contra hc
    have hlt' : lo < k.1 := lt_of_le_of_ne (hsub k hk).1 (Ne.symm hc)
    set y := (lo + min k.1 hi) / 2
    have hm : lo < min k.1 hi := lt_min hlt' hlt
    obtain ⟨q, hq, hq1, -⟩ := hcov y (by simp only [y]; linarith)
      (by simp only [y]; linarith [min_le_right k.1 hi])
    have := hmin q (List.mem_toFinset.2 hq)
    have : y < k.1 := by simp only [y]; linarith [min_le_left k.1 hi]
    linarith
  have hperm := List.perm_cons_erase hk
  set rest := l.erase k
  have hsum : (l.map (fun q => q.2 - q.1)).sum = (k.2 - k.1) + (rest.map (fun q => q.2 - q.1)).sum := by
    rw [(hperm.map _).sum_eq]; simp
  have hdisj' : (k :: rest).Pairwise (fun p q => q.2 ≤ p.1 ∨ p.2 ≤ q.1) :=
    hdisj.perm hperm (fun h => h.symm)
  rw [List.pairwise_cons] at hdisj'
  have hrest : ∀ q ∈ rest, k.2 ≤ q.1 := by
    intro q hq
    have hql : q ∈ l := List.mem_of_mem_erase hq
    rcases hdisj'.1 q hq with h | h
    · have := hsub q hql; linarith
    · exact h
  have hk2 := (hsub k hk).2.2
  rcases hk2.lt_or_eq with hk2 | hk2
  · have hlen : rest.length < n := by
      rw [← hn, List.length_erase_of_mem hk]
      exact Nat.sub_lt (List.length_pos_of_mem hk) one_pos
    have hk12 := (hsub k hk).2.1
    have := ih rest.length hlen rest rfl k.2 hi hk2
      (fun q hq => ⟨hrest q hq, (hsub q (List.mem_of_mem_erase hq)).2.1,
        (hsub q (List.mem_of_mem_erase hq)).2.2⟩) hdisj'.2
      (fun y h1 h2 => by
        obtain ⟨q, hq, hq1, hq2⟩ := hcov y (by linarith) h2
        rcases List.mem_cons.1 (hperm.subset hq) with rfl | hq'
        · linarith
        · exact ⟨q, hq', hq1, hq2⟩)
    rw [hsum, this, hk1]; ring
  · have : rest = [] := by
      by_contra h
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil rest h
      have := hrest q hq
      have := hsub q (List.mem_of_mem_erase hq)
      linarith
    rw [hsum, this, hk1, hk2]; simp

/-- **One-dimensional lemma**: a closed interval `[lo, hi]` covered by finitely many closed
intervals lying in it, with pairwise disjoint interiors, is the sum of their lengths. -/
theorem sum_len_cover (l : List (K × K)) {lo hi : K} (hlt : lo < hi)
    (hsub : ∀ q ∈ l, lo ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ hi)
    (hdisj : l.Pairwise (fun p q => q.2 ≤ p.1 ∨ p.2 ≤ q.1))
    (hcov : ∀ y, lo < y → y < hi → ∃ q ∈ l, q.1 ≤ y ∧ y ≤ q.2) :
    (l.map (fun q => q.2 - q.1)).sum = hi - lo :=
  sum_len_cover_aux _ l rfl lo hi hlt hsub hdisj hcov

/-! ### Vertical sections -/

/-- The section of the region `S` at the abscissa `x0` is the closed interval `[lo, hi]`,
`lo < hi`. -/
def IsSec (S : K × K → Prop) (x0 lo hi : K) : Prop :=
  lo < hi ∧ ∀ y, S (x0, y) ↔ lo ≤ y ∧ y ≤ hi

theorem IsSec.unique {S : K × K → Prop} {x0 lo hi lo' hi' : K} (h : IsSec S x0 lo hi)
    (h' : IsSec S x0 lo' hi') : lo = lo' ∧ hi = hi' := by
  have a1 := (h'.2 lo).1 ((h.2 lo).2 ⟨le_rfl, h.1.le⟩)
  have a2 := (h.2 lo').1 ((h'.2 lo').2 ⟨le_rfl, h'.1.le⟩)
  have a3 := (h'.2 hi).1 ((h.2 hi).2 ⟨h.1.le, le_rfl⟩)
  have a4 := (h.2 hi').1 ((h'.2 hi').2 ⟨h'.1.le, le_rfl⟩)
  exact ⟨le_antisymm a2.1 a1.1, le_antisymm a3.2 a4.2⟩

open Classical in
/-- The lower end of the section (`0` if the section is not a non-degenerate interval). -/
noncomputable def secLo (S : K × K → Prop) (x0 : K) : K :=
  if h : ∃ lo hi, IsSec S x0 lo hi then h.choose else 0

open Classical in
/-- The upper end of the section (`0` if the section is not a non-degenerate interval). -/
noncomputable def secHi (S : K × K → Prop) (x0 : K) : K :=
  if h : ∃ lo hi, IsSec S x0 lo hi then h.choose_spec.choose else 0

/-- The length of the section. -/
noncomputable def secLen (S : K × K → Prop) (x0 : K) : K := secHi S x0 - secLo S x0

theorem sec_eq {S : K × K → Prop} {x0 lo hi : K} (h : IsSec S x0 lo hi) :
    secLo S x0 = lo ∧ secHi S x0 = hi := by
  have hex : ∃ lo hi, IsSec S x0 lo hi := ⟨lo, hi, h⟩
  have := hex.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := this.unique h
  unfold secLo secHi
  rw [dif_pos hex, dif_pos hex]
  exact ⟨e1, e2⟩

theorem secLen_eq {S : K × K → Prop} {x0 lo hi : K} (h : IsSec S x0 lo hi) :
    secLen S x0 = hi - lo := by
  unfold secLen; rw [(sec_eq h).1, (sec_eq h).2]

theorem secLen_empty {S : K × K → Prop} {x0 : K} (h : ∀ y, ¬S (x0, y)) : secLen S x0 = 0 := by
  have hn : ¬∃ lo hi, IsSec S x0 lo hi := by
    rintro ⟨lo, hi, h1, h2⟩
    exact h lo ((h2 lo).2 ⟨le_rfl, h1.le⟩)
  unfold secLen secLo secHi
  rw [dif_neg hn, dif_neg hn, sub_zero]

/-- Three affine constraints `α k y + β k ≥ 0`, some with positive and some with negative slope,
cut out a closed interval bounded by the zeros of two of them. -/
theorem interval_of_constraints (α β : Fin 3 → K) (hpos : ∃ i, 0 < α i) (hneg : ∃ j, α j < 0)
    (hne : ∃ y, ∀ k, 0 ≤ α k * y + β k) :
    ∃ i j, 0 < α i ∧ α j < 0 ∧
      ∀ y, (∀ k, 0 ≤ α k * y + β k) ↔ (-β i / α i ≤ y ∧ y ≤ -β j / α j) := by
  classical
  obtain ⟨i, hi, himax⟩ := (Finset.univ.filter (fun k => 0 < α k)).exists_max_image
    (fun k => -β k / α k) (by obtain ⟨i, h⟩ := hpos; exact ⟨i, by simp [h]⟩)
  obtain ⟨j, hj, hjmin⟩ := (Finset.univ.filter (fun k => α k < 0)).exists_min_image
    (fun k => -β k / α k) (by obtain ⟨j, h⟩ := hneg; exact ⟨j, by simp [h]⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj himax hjmin
  obtain ⟨y0, hy0⟩ := hne
  refine ⟨i, j, hi, hj, fun y => ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ k => ?_⟩⟩
  · rw [div_le_iff₀ hi]; linarith [h i]
  · rw [le_div_iff_of_neg hj]; linarith [h j]
  · rcases lt_trichotomy (α k) 0 with hk | hk | hk
    · have := le_trans h2 (hjmin k hk)
      rw [le_div_iff_of_neg hk] at this; linarith
    · have := hy0 k; rw [hk] at this ⊢; linarith
    · have := le_trans (himax k hk) h1
      rw [div_le_iff₀ hk] at this; linarith

/-- The three constraints defining a triangle, on the vertical line `x = x0`. -/
def secA (t : Tr K) : Fin 3 → K :=
  ![t.D * (t.c.1 - t.b.1), t.D * (t.a.1 - t.c.1), t.D * (t.b.1 - t.a.1)]

def secB (t : Tr K) (x0 : K) : Fin 3 → K :=
  ![t.D * (-(t.c.1 - t.b.1) * t.b.2 - (t.c.2 - t.b.2) * (x0 - t.b.1)),
    t.D * (-(t.a.1 - t.c.1) * t.c.2 - (t.a.2 - t.c.2) * (x0 - t.c.1)),
    t.D * (-(t.b.1 - t.a.1) * t.a.2 - (t.b.2 - t.a.2) * (x0 - t.a.1))]

theorem forall_fin3 {p : Fin 3 → Prop} : (∀ k, p k) ↔ p 0 ∧ p 1 ∧ p 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ k => by fin_cases k <;> assumption⟩

theorem sec_eqs (t : Tr K) (x0 y : K) :
    t.D * det3 t.b t.c (x0, y) = secA t 0 * y + secB t x0 0 ∧
      t.D * det3 t.c t.a (x0, y) = secA t 1 * y + secB t x0 1 ∧
      t.D * det3 t.a t.b (x0, y) = secA t 2 * y + secB t x0 2 := by
  refine ⟨?_, ?_, ?_⟩
  · change _ = t.D * (t.c.1 - t.b.1) * y +
      t.D * (-(t.c.1 - t.b.1) * t.b.2 - (t.c.2 - t.b.2) * (x0 - t.b.1))
    unfold det3; ring
  · change _ = t.D * (t.a.1 - t.c.1) * y +
      t.D * (-(t.a.1 - t.c.1) * t.c.2 - (t.a.2 - t.c.2) * (x0 - t.c.1))
    unfold det3; ring
  · change _ = t.D * (t.b.1 - t.a.1) * y +
      t.D * (-(t.b.1 - t.a.1) * t.a.2 - (t.b.2 - t.a.2) * (x0 - t.a.1))
    unfold det3; ring

theorem sec_mem_iff (t : Tr K) (x0 y : K) :
    t.mem (x0, y) ↔ ∀ k, 0 ≤ secA t k * y + secB t x0 k := by
  obtain ⟨e0, e1, e2⟩ := sec_eqs t x0 y
  rw [forall_fin3, ← e0, ← e1, ← e2]
  rfl

theorem sec_int_iff (t : Tr K) (x0 y : K) :
    t.int (x0, y) ↔ ∀ k, 0 < secA t k * y + secB t x0 k := by
  obtain ⟨e0, e1, e2⟩ := sec_eqs t x0 y
  rw [forall_fin3, ← e0, ← e1, ← e2]
  rfl

/-- **Sections of a triangle.** At an abscissa which is not that of a vertex, the section of a
non-degenerate triangle, if not empty, is a non-degenerate closed interval whose interior points
are interior points of the triangle. -/
theorem section_interval {t : Tr K} (ht : t.nd) {x0 : K} (ha : x0 ≠ t.a.1) (hb : x0 ≠ t.b.1)
    (hc : x0 ≠ t.c.1) (hne : ∃ y, t.mem (x0, y)) :
    ∃ lo hi, IsSec t.mem x0 lo hi ∧ ∀ y, lo < y → y < hi → t.int (x0, y) := by
  have hD : t.D ≠ 0 := ht
  have hsum : secA t 0 + secA t 1 + secA t 2 = 0 := by
    simp only [secA, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]; ring
  have hnz : ¬(secA t 0 = 0 ∧ secA t 1 = 0 ∧ secA t 2 = 0) := by
    rintro ⟨h0, h1, -⟩
    simp only [secA, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h0 h1
    have e0 := (mul_eq_zero.1 h0).resolve_left hD
    have e1 := (mul_eq_zero.1 h1).resolve_left hD
    apply hD; unfold Tr.D det3
    have : t.b.1 - t.a.1 = 0 := by linarith
    have : t.c.1 - t.a.1 = 0 := by linarith
    simp [*]
  have hpos : ∃ i, 0 < secA t i := by
    by_contra h; push Not at h
    apply hnz
    have := h 0; have := h 1; have := h 2
    exact ⟨by linarith, by linarith, by linarith⟩
  have hneg : ∃ j, secA t j < 0 := by
    by_contra h; push Not at h
    apply hnz
    have := h 0; have := h 1; have := h 2
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨y0, hy0⟩ := hne
  have hne' : ∃ y, ∀ k, 0 ≤ secA t k * y + secB t x0 k := ⟨y0, (sec_mem_iff t x0 y0).1 hy0⟩
  obtain ⟨i, j, hi, hj, hiff⟩ := interval_of_constraints (secA t) (secB t x0) hpos hneg hne'
  set lo := -secB t x0 i / secA t i
  set hi' := -secB t x0 j / secA t j
  have hle : lo ≤ hi' := by
    have := (hiff y0).1 ((sec_mem_iff t x0 y0).1 hy0); linarith [this.1, this.2]
  -- the constraints are the scaled cross products of the three sides
  have hd0 : ∀ y, t.D * det3 t.b t.c (x0, y) = secA t 0 * y + secB t x0 0 :=
    fun y => (sec_eqs t x0 y).1
  have hd1 : ∀ y, t.D * det3 t.c t.a (x0, y) = secA t 1 * y + secB t x0 1 :=
    fun y => (sec_eqs t x0 y).2.1
  have hd2 : ∀ y, t.D * det3 t.a t.b (x0, y) = secA t 2 * y + secB t x0 2 :=
    fun y => (sec_eqs t x0 y).2.2
  have f0 : ∀ y, secA t 0 * y + secB t x0 0 = 0 → det3 t.b t.c (x0, y) = 0 :=
    fun y h => (mul_eq_zero.1 ((hd0 y).trans h)).resolve_left hD
  have f1 : ∀ y, secA t 1 * y + secB t x0 1 = 0 → det3 t.c t.a (x0, y) = 0 :=
    fun y h => (mul_eq_zero.1 ((hd1 y).trans h)).resolve_left hD
  have f2 : ∀ y, secA t 2 * y + secB t x0 2 = 0 → det3 t.a t.b (x0, y) = 0 :=
    fun y h => (mul_eq_zero.1 ((hd2 y).trans h)).resolve_left hD
  -- two vanishing cross products give a vertex
  have hrec := fun y : K => det3_recon t.a t.b t.c (x0, y)
  have hs := fun y : K => det3_sum t.a t.b t.c (x0, y)
  have c01 : ∀ y, det3 t.b t.c (x0, y) = 0 → det3 t.c t.a (x0, y) = 0 → False := by
    intro y h1 h2
    obtain ⟨r1, -⟩ := hrec y
    have := hs y
    rw [h1, h2] at r1 this
    apply hc; apply mul_left_cancel₀ hD
    change t.D * x0 = _ at r1
    change _ = t.D at this
    rw [r1, ← this]; ring
  have c02 : ∀ y, det3 t.b t.c (x0, y) = 0 → det3 t.a t.b (x0, y) = 0 → False := by
    intro y h1 h2
    obtain ⟨r1, -⟩ := hrec y
    have := hs y
    rw [h1, h2] at r1 this
    apply hb; apply mul_left_cancel₀ hD
    change t.D * x0 = _ at r1
    change _ = t.D at this
    rw [r1, ← this]; ring
  have c12 : ∀ y, det3 t.c t.a (x0, y) = 0 → det3 t.a t.b (x0, y) = 0 → False := by
    intro y h1 h2
    obtain ⟨r1, -⟩ := hrec y
    have := hs y
    rw [h1, h2] at r1 this
    apply ha; apply mul_left_cancel₀ hD
    change t.D * x0 = _ at r1
    change _ = t.D at this
    rw [r1, ← this]; ring
  have hij : i ≠ j := by rintro rfl; linarith
  have hlt : lo < hi' := by
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hine := hi.ne'
      have hjne := hj.ne
      have z1 : secA t i * lo + secB t x0 i = 0 := by
        simp only [lo]; field_simp; ring
      have z2 : secA t j * lo + secB t x0 j = 0 := by
        rw [h]; simp only [hi']; field_simp; ring
      clear_value lo hi'
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact c01 lo (f0 lo z1) (f1 lo z2)
        | exact c01 lo (f0 lo z2) (f1 lo z1)
        | exact c02 lo (f0 lo z1) (f2 lo z2)
        | exact c02 lo (f0 lo z2) (f2 lo z1)
        | exact c12 lo (f1 lo z1) (f2 lo z2)
        | exact c12 lo (f1 lo z2) (f2 lo z1)
  -- a constraint with zero slope is strictly positive
  have hB : ∀ k, secA t k = 0 → secB t x0 k ≠ 0 := by
    intro k hk hk'
    fin_cases k
    · change t.D * (t.c.1 - t.b.1) = 0 at hk
      change t.D * (-(t.c.1 - t.b.1) * t.b.2 - (t.c.2 - t.b.2) * (x0 - t.b.1)) = 0 at hk'
      have e1 : t.c.1 = t.b.1 := by have := (mul_eq_zero.1 hk).resolve_left hD; linarith
      have : t.D * ((t.c.2 - t.b.2) * (x0 - t.b.1)) = 0 := by
        linear_combination -hk' - t.D * t.b.2 * e1
      rcases mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hD) with h | h
      · exact Tr.nd_ne_bc ht (Prod.ext e1.symm (by linarith))
      · exact hb (by linarith)
    · change t.D * (t.a.1 - t.c.1) = 0 at hk
      change t.D * (-(t.a.1 - t.c.1) * t.c.2 - (t.a.2 - t.c.2) * (x0 - t.c.1)) = 0 at hk'
      have e1 : t.a.1 = t.c.1 := by have := (mul_eq_zero.1 hk).resolve_left hD; linarith
      have : t.D * ((t.a.2 - t.c.2) * (x0 - t.c.1)) = 0 := by
        linear_combination -hk' - t.D * t.c.2 * e1
      rcases mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hD) with h | h
      · exact Tr.nd_ne_ca ht (Prod.ext e1.symm (by linarith))
      · exact hc (by linarith)
    · change t.D * (t.b.1 - t.a.1) = 0 at hk
      change t.D * (-(t.b.1 - t.a.1) * t.a.2 - (t.b.2 - t.a.2) * (x0 - t.a.1)) = 0 at hk'
      have e1 : t.b.1 = t.a.1 := by have := (mul_eq_zero.1 hk).resolve_left hD; linarith
      have : t.D * ((t.b.2 - t.a.2) * (x0 - t.a.1)) = 0 := by
        linear_combination -hk' - t.D * t.a.2 * e1
      rcases mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hD) with h | h
      · exact Tr.nd_ne_ab ht (Prod.ext e1.symm (by linarith))
      · exact ha (by linarith)
  refine ⟨lo, hi', ⟨hlt, fun y => (sec_mem_iff t x0 y).trans (hiff y)⟩, fun y h1 h2 => ?_⟩
  rw [sec_int_iff]
  intro k
  rcases lt_trichotomy (secA t k) 0 with hk | hk | hk
  · have hmem := (hiff hi').2 ⟨hlt.le, le_rfl⟩ k
    nlinarith
  · have hmem := (hiff lo).2 ⟨le_rfl, hlt.le⟩ k
    rw [hk, zero_mul, zero_add] at hmem ⊢
    exact lt_of_le_of_ne hmem (Ne.symm (hB k hk))
  · have hmem := (hiff lo).2 ⟨le_rfl, hlt.le⟩ k
    nlinarith

/-! ### Sections of a triangle with a vertical side -/

theorem secLen_congr {S S' : K × K → Prop} (h : ∀ p, S p ↔ S' p) : secLen S = secLen S' := by
  have : S = S' := funext fun p => propext (h p)
  rw [this]

theorem vert_sec_pos {a1 a2 b2 c1 c2 : K} (hδ : 0 < b2 - a2) (huv : c1 ≠ a1) {x0 : K}
    (hxa : x0 ≠ a1) (hxc : x0 ≠ c1) :
    secLen (Tr.mk (a1, a2) (a1, b2) (c1, c2)).mem x0 =
      if 0 < (x0 - a1) / (c1 - a1) ∧ (x0 - a1) / (c1 - a1) < 1 then
        |b2 - a2| * (1 - (x0 - a1) / (c1 - a1)) else 0 := by
  have hvu : c1 - a1 ≠ 0 := sub_ne_zero.2 huv
  obtain ⟨ρ, hρ⟩ : ∃ ρ : K, ρ = (x0 - a1) / (c1 - a1) := ⟨_, rfl⟩
  obtain ⟨ya, hya⟩ : ∃ ya : K, ya = a2 + ρ * (c2 - a2) := ⟨_, rfl⟩
  obtain ⟨yb, hyb⟩ : ∃ yb : K, yb = b2 + ρ * (c2 - b2) := ⟨_, rfl⟩
  rw [← hρ]
  set t : Tr K := Tr.mk (a1, a2) (a1, b2) (c1, c2) with htdef
  have hD : t.D = -(b2 - a2) * (c1 - a1) := by simp only [htdef, Tr.D, det3]; ring
  have e3 : ∀ y, t.D * det3 t.a t.b (x0, y) = (b2 - a2) * (b2 - a2) * ((c1 - a1) * (x0 - a1)) := by
    intro y; rw [hD]; simp only [htdef, det3]; ring
  have e1 : ∀ y, t.D * det3 t.b t.c (x0, y) =
      (b2 - a2) * ((c1 - a1) * (c1 - a1)) * (yb - y) := by
    intro y; rw [hD, hyb, hρ]; simp only [htdef, det3]; field_simp; ring
  have e2 : ∀ y, t.D * det3 t.c t.a (x0, y) =
      (b2 - a2) * ((c1 - a1) * (c1 - a1)) * (y - ya) := by
    intro y; rw [hD, hya, hρ]; simp only [htdef, det3]; field_simp; ring
  have hw : 0 < (b2 - a2) * ((c1 - a1) * (c1 - a1)) := mul_pos hδ (mul_self_pos.2 hvu)
  have hρiff : 0 ≤ (c1 - a1) * (x0 - a1) ↔ 0 ≤ ρ := by
    rw [hρ, show (x0 - a1) / (c1 - a1) = ((c1 - a1) * (x0 - a1)) / ((c1 - a1) * (c1 - a1)) by
      field_simp]
    constructor
    · intro h; exact div_nonneg h (mul_self_nonneg _)
    · intro h
      have := mul_nonneg h (mul_self_nonneg (c1 - a1))
      rwa [div_mul_cancel₀ _ (mul_self_pos.2 hvu).ne'] at this
  have hmem : ∀ y, t.mem (x0, y) ↔ 0 ≤ ρ ∧ ya ≤ y ∧ y ≤ yb := by
    intro y
    unfold Tr.mem
    rw [e1, e2, e3, mul_nonneg_iff_of_pos_left hw, mul_nonneg_iff_of_pos_left hw,
      mul_nonneg_iff_of_pos_left (mul_pos hδ hδ), hρiff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h3, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, h1⟩
  have hdiff : yb - ya = (b2 - a2) * (1 - ρ) := by rw [hya, hyb]; ring
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact div_ne_zero (sub_ne_zero.2 hxa) hvu
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [hρ, div_eq_one_iff_eq hvu] at h; exact hxc (by linarith)
  split_ifs with hin
  · have hlt : ya < yb := by
      have := mul_pos hδ (sub_pos.2 hin.2); linarith
    have hsec : IsSec t.mem x0 ya yb :=
      ⟨hlt, fun y => by rw [hmem]; exact ⟨fun h => h.2, fun h => ⟨hin.1.le, h⟩⟩⟩
    rw [secLen_eq hsec, hdiff, abs_of_pos hδ]
  · apply secLen_empty
    intro y hy
    rw [hmem] at hy
    apply hin
    refine ⟨lt_of_le_of_ne hy.1 (Ne.symm hρ0), lt_of_le_of_ne ?_ hρ1⟩
    by_contra h
    push Not at h
    have : (b2 - a2) * (1 - ρ) < 0 := mul_neg_of_pos_of_neg hδ (by linarith)
    linarith [hy.2.1, hy.2.2]

theorem vert_sec {t : Tr K} (ht : t.nd) (hab : t.a.1 = t.b.1) {x0 : K} (hxa : x0 ≠ t.a.1)
    (hxc : x0 ≠ t.c.1) :
    secLen t.mem x0 =
      if 0 < (x0 - t.a.1) / (t.c.1 - t.a.1) ∧ (x0 - t.a.1) / (t.c.1 - t.a.1) < 1 then
        |t.b.2 - t.a.2| * (1 - (x0 - t.a.1) / (t.c.1 - t.a.1)) else 0 := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := t
  simp only at hab hxa hxc ⊢
  cases hab
  have hD : det3 (a1, a2) (a1, b2) (c1, c2) ≠ 0 := ht
  have huv : c1 ≠ a1 := by
    intro e; apply hD; unfold det3; rw [e]; ring
  have hδ : b2 - a2 ≠ 0 := by
    intro e; apply hD; unfold det3; rw [show b2 = a2 by linarith]; ring
  rcases lt_or_gt_of_ne hδ with h | h
  · have hs := vert_sec_pos (a1 := a1) (a2 := b2) (b2 := a2) (c1 := c1) (c2 := c2)
      (by linarith) huv hxa hxc
    rw [abs_sub_comm] at hs
    rw [← hs]
    exact congrFun (secLen_congr (S := (Tr.mk (a1, a2) (a1, b2) (c1, c2)).mem)
      (S' := (Tr.mk (a1, b2) (a1, a2) (c1, c2)).mem)
      (fun p => Tr.mem_swap (t := Tr.mk (a1, b2) (a1, a2) (c1, c2)))) x0
  · exact vert_sec_pos h huv hxa hxc

/-! ### Midpoint sums -/

/-- Consecutive elements of a list satisfy `R`. -/
def Consec (R : K → K → Prop) : List K → Prop
  | a :: b :: t => R a b ∧ Consec R (b :: t)
  | _ => True

theorem Consec.mono {R R' : K → K → Prop} (h : ∀ a b, R a b → R' a b) :
    ∀ {s : List K}, Consec R s → Consec R' s
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, ⟨h1, h2⟩ => ⟨h _ _ h1, Consec.mono h h2⟩

/-- In a strictly increasing list, no point of `W` lies strictly between consecutive elements,
if every point of `W` is an element of the list or below all of them. -/
theorem consec_sorted (W : K → Prop) :
    ∀ (s : List K), s.Pairwise (· < ·) → (∀ w, W w → w ∈ s ∨ ∀ x ∈ s, w < x) →
      Consec (fun a b => a < b ∧ ∀ w, W w → ¬(a < w ∧ w < b)) s
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: t, hs, hW => by
    have hab : a < b := List.rel_of_pairwise_cons hs List.mem_cons_self
    have hs' := hs.of_cons
    refine ⟨⟨hab, fun w hw ⟨h1, h2⟩ => ?_⟩, consec_sorted W (b :: t) hs' (fun w hw => ?_)⟩
    · rcases hW w hw with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact lt_irrefl _ h1
        · rcases List.mem_cons.1 h with rfl | h
          · exact lt_irrefl _ h2
          · have := List.rel_of_pairwise_cons hs' h; linarith
      · have := h a List.mem_cons_self; linarith
    · rcases hW w hw with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · right; intro x hx; exact List.rel_of_pairwise_cons hs hx
        · exact Or.inl h
      · exact Or.inr fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- The midpoint sum `Σ (b - a) f ((a + b) / 2)` over consecutive elements. -/
def msum (f : K → K) : List K → K
  | a :: b :: t => (b - a) * f ((a + b) / 2) + msum f (b :: t)
  | _ => 0

theorem msum_congr {f g : K → K} :
    ∀ {s : List K}, Consec (fun a b => f ((a + b) / 2) = g ((a + b) / 2)) s → msum f s = msum g s
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, ⟨h1, h2⟩ => by simp only [msum]; rw [h1, msum_congr h2]

theorem msum_add (f g : K → K) :
    ∀ s : List K, msum (fun x => f x + g x) s = msum f s + msum g s
  | [] => by simp [msum]
  | [_] => by simp [msum]
  | a :: b :: t => by simp only [msum]; rw [msum_add f g (b :: t)]; ring

theorem msum_listSum {α : Type*} (G : α → K → K) (l : List α) :
    ∀ s : List K, msum (fun x => (l.map (fun r => G r x)).sum) s =
      (l.map (fun r => msum (G r) s)).sum
  | [] => by simp [msum]
  | [_] => by simp [msum]
  | a :: b :: t => by
    simp only [msum]
    rw [msum_listSum G l (b :: t), ← List.sum_map_mul_left, ← List.sum_map_add]

/-- The last element of `a :: t`, written `lastD t a`. -/
def lastD : List K → K → K
  | [], d => d
  | a :: t, _ => lastD t a

theorem msum_tele (f F : K → K) (R : K → K → Prop)
    (hstep : ∀ a b, R a b → (b - a) * f ((a + b) / 2) = F b - F a) :
    ∀ (a : K) (t : List K), Consec R (a :: t) → msum f (a :: t) = F (lastD t a) - F a
  | a, [], _ => by simp [msum, lastD]
  | a, b :: t, ⟨h1, h2⟩ => by
    have ih := msum_tele f F R hstep b t h2
    have e : msum f (a :: b :: t) = (b - a) * f ((a + b) / 2) + msum f (b :: t) := rfl
    rw [e, ih, hstep a b h1]
    simp only [lastD]
    ring

theorem le_lastD : ∀ (a : K) (t : List K), (a :: t).Pairwise (· < ·) → ∀ w ∈ a :: t,
    w ≤ lastD t a
  | a, [], _, w, hw => by
    rw [List.mem_singleton.1 hw]; exact le_refl _
  | a, b :: t, hs, w, hw => by
    have ih := le_lastD b t hs.of_cons
    have e : lastD (b :: t) a = lastD t b := rfl
    rw [e]
    rcases List.mem_cons.1 hw with rfl | hw
    · exact le_trans (List.rel_of_pairwise_cons hs List.mem_cons_self).le (ih b List.mem_cons_self)
    · exact ih w hw

/-- Midpoint sums integrate a function which is affine on `(lo, hi)` and vanishes outside. -/
theorem msum_affine {lo hi A B : K} (hlh : lo < hi) (f : K → K)
    (hin : ∀ m, lo < m → m < hi → f m = A * m + B) (hout : ∀ m, m < lo ∨ hi < m → f m = 0)
    (s : List K) (hs : s.Pairwise (· < ·)) (hlo : lo ∈ s) (hhi : hi ∈ s) :
    msum f s = (A * hi ^ 2 / 2 + B * hi) - (A * lo ^ 2 / 2 + B * lo) := by
  set F : K → K := fun x => A * (max lo (min x hi)) ^ 2 / 2 + B * max lo (min x hi) with hF
  have hstep : ∀ a b : K, (a < b ∧ ∀ w, (w = lo ∨ w = hi) → ¬(a < w ∧ w < b)) →
      (b - a) * f ((a + b) / 2) = F b - F a := by
    rintro a b ⟨hab, hw⟩
    have nlo := hw lo (Or.inl rfl)
    have nhi := hw hi (Or.inr rfl)
    simp only [hF]
    by_cases hb : b ≤ lo
    · rw [hout _ (Or.inl (by linarith)), min_eq_left (hb.trans hlh.le),
        min_eq_left ((hab.le.trans hb).trans hlh.le), max_eq_left hb,
        max_eq_left (hab.le.trans hb)]
      ring
    by_cases ha : hi ≤ a
    · rw [hout _ (Or.inr (by linarith)), min_eq_right ha, min_eq_right (ha.trans hab.le),
        max_eq_right hlh.le]
      ring
    push Not at hb ha
    have ha' : lo ≤ a := by by_contra h; push Not at h; exact nlo ⟨h, hb⟩
    have hb' : b ≤ hi := by by_contra h; push Not at h; exact nhi ⟨ha, h⟩
    rw [hin _ (by linarith) (by linarith), min_eq_left hb', min_eq_left (hab.le.trans hb'),
      max_eq_right (ha'.trans hab.le), max_eq_right ha']
    ring
  have hc := consec_sorted (fun w => w = lo ∨ w = hi) s hs (fun w hw => by
    rcases hw with rfl | rfl
    · exact Or.inl hlo
    · exact Or.inl hhi)
  cases s with
  | nil => exact absurd hlo List.not_mem_nil
  | cons a t =>
    rw [msum_tele f F _ hstep a t hc]
    have h1 : a ≤ lo := by
      rcases List.mem_cons.1 hlo with h | h
      · exact h.symm.le
      · exact (List.rel_of_pairwise_cons hs h).le
    have h2 : hi ≤ lastD t a := le_lastD a t hs hi hhi
    simp only [hF]
    rw [min_eq_right h2, max_eq_right hlh.le, min_eq_left (h1.trans hlh.le), max_eq_left h1]

/-- **The midpoint sum of the section lengths of a triangle with a vertical side** is `|D| / 2`. -/
theorem msum_secLen_vert {t : Tr K} (ht : t.nd) (hab : t.a.1 = t.b.1) (s : List K)
    (hs : s.Pairwise (· < ·)) (ha : t.a.1 ∈ s) (hc : t.c.1 ∈ s) :
    msum (secLen t.mem) s = |t.D| / 2 := by
  have hD : t.D ≠ 0 := ht
  obtain ⟨u, hu⟩ : ∃ u, u = t.a.1 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = t.c.1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = |t.b.2 - t.a.2| := ⟨_, rfl⟩
  have huv : v ≠ u := by
    intro e; apply hD; unfold Tr.D det3; rw [← hab, ← hu, ← hv, e]; ring
  have hvu : v - u ≠ 0 := sub_ne_zero.2 huv
  have hDe : t.D = -(t.b.2 - t.a.2) * (v - u) := by
    unfold Tr.D det3; rw [← hab, hu, hv]; ring
  set f : K → K := fun m => if 0 < (m - u) / (v - u) ∧ (m - u) / (v - u) < 1 then
    δ * (1 - (m - u) / (v - u)) else 0 with hfdef
  have hc' := consec_sorted (fun w => w = u ∨ w = v) s hs (fun w hw => by
    rcases hw with rfl | rfl
    · rw [hu]; exact Or.inl ha
    · rw [hv]; exact Or.inl hc)
  rw [msum_congr (g := f) (hc'.mono fun a b ⟨_, hw⟩ => by
    have h1 : (a + b) / 2 ≠ t.a.1 := by
      intro e; exact hw u (Or.inl rfl) ⟨by rw [hu]; linarith, by rw [hu]; linarith⟩
    have h2 : (a + b) / 2 ≠ t.c.1 := by
      intro e; exact hw v (Or.inr rfl) ⟨by rw [hv]; linarith, by rw [hv]; linarith⟩
    rw [vert_sec ht hab h1 h2, hfdef]
    simp only [← hu, ← hv, ← hδ])]
  -- `f` is affine between `u` and `v`
  have key : ∀ lo hi : K, lo < hi → (lo = u ∧ hi = v ∨ lo = v ∧ hi = u) →
      msum f s = (-δ / (v - u) * hi ^ 2 / 2 + δ * v / (v - u) * hi) -
        (-δ / (v - u) * lo ^ 2 / 2 + δ * v / (v - u) * lo) := by
    intro lo hi hlh hcase
    have hρ : ∀ m, (0 < (m - u) / (v - u) ∧ (m - u) / (v - u) < 1) ↔ lo < m ∧ m < hi := by
      intro m
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hp : 0 < hi - lo := by linarith
        rw [div_pos_iff_of_pos_right hp, div_lt_one hp]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      · have hp : lo - hi < 0 := by linarith
        rw [div_lt_one_of_neg hp]
        constructor
        · rintro ⟨h1, h2⟩
          rcases div_pos_iff.1 h1 with h | h
          · exact absurd h.2 (not_lt.2 hp.le)
          · constructor <;> linarith [h.1]
        · rintro ⟨h1, h2⟩
          exact ⟨div_pos_of_neg_of_neg (by linarith) hp, by linarith⟩
    refine msum_affine hlh f (fun m h1 h2 => ?_) (fun m hm => ?_) s hs ?_ ?_
    · simp only [hfdef]; rw [if_pos ((hρ m).2 ⟨h1, h2⟩)]; field_simp; ring
    · simp only [hfdef]; rw [if_neg (fun h => by
        have := (hρ m).1 h; rcases hm with hm | hm <;> linarith)]
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hu]; exact ha
      · rw [hv]; exact hc
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hv]; exact hc
      · rw [hu]; exact ha
  rw [hDe, abs_mul, abs_neg, ← hδ]
  rcases lt_or_gt_of_ne huv with h | h
  · rw [key v u h (Or.inr ⟨rfl, rfl⟩), abs_of_neg (sub_neg.2 h)]
    field_simp; ring
  · rw [key u v h (Or.inl ⟨rfl, rfl⟩), abs_of_pos (sub_pos.2 h)]
    field_simp; ring

/-! ### Additivity -/

/-- **Additivity of section lengths**: at an abscissa which is not that of a vertex, the section
length of a triangle is the sum of the section lengths of the triangles of a decomposition. -/
theorem secLen_additive {T : Tr K} (hT : T.nd) {l : List (Tr K)} (hl : DecS T.mem l) {x0 : K}
    (hx : ∀ r ∈ T :: l, x0 ≠ r.a.1 ∧ x0 ≠ r.b.1 ∧ x0 ≠ r.c.1) :
    secLen T.mem x0 = (l.map (fun r => secLen r.mem x0)).sum := by
  classical
  obtain ⟨hnd, hpw, hun⟩ := hl
  have hsub : ∀ r ∈ l, ∀ p, r.mem p → T.mem p := fun r hr p hp => (hun p).2 ⟨r, hr, hp⟩
  by_cases hne : ∃ y, T.mem (x0, y)
  · obtain ⟨hTa, hTb, hTc⟩ := hx T List.mem_cons_self
    obtain ⟨lo, hi, hsec, -⟩ := section_interval hT hTa hTb hTc hne
    -- the triangles meeting the vertical line
    set l' := l.filter (fun r => ∃ y, r.mem (x0, y))
    have hdata : ∀ r ∈ l', IsSec r.mem x0 (secLo r.mem x0) (secHi r.mem x0) ∧
        ∀ y, secLo r.mem x0 < y → y < secHi r.mem x0 → r.int (x0, y) := by
      intro r hr
      have hr' := List.mem_filter.1 hr
      obtain ⟨hra, hrb, hrc⟩ := hx r (List.mem_cons_of_mem _ hr'.1)
      obtain ⟨lo', hi', hs', hint⟩ := section_interval (hnd r hr'.1) hra hrb hrc
        (by simpa using hr'.2)
      rw [(sec_eq hs').1, (sec_eq hs').2]
      exact ⟨hs', hint⟩
    have hsum : (l.map (fun r => secLen r.mem x0)).sum =
        (l'.map (fun r => secLen r.mem x0)).sum := by
      rw [← List.sum_map_filter_add_sum_map_filter_not (fun r => ∃ y, r.mem (x0, y))
        (fun r => secLen r.mem x0) l]
      have : ((l.filter (fun r => ¬∃ y, r.mem (x0, y))).map (fun r => secLen r.mem x0)).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
        have := (List.mem_filter.1 hr).2
        simp only [decide_eq_true_eq, not_exists] at this
        exact secLen_empty this
      rw [this, add_zero]
    rw [secLen_eq hsec, hsum]
    have := sum_len_cover (l'.map (fun r => (secLo r.mem x0, secHi r.mem x0))) hsec.1
      (fun q hq => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
        obtain ⟨⟨hlt, hiff⟩, -⟩ := hdata r hr
        have h1 := hsub r (List.mem_filter.1 hr).1 _ ((hiff _).2 ⟨le_rfl, hlt.le⟩)
        have h2 := hsub r (List.mem_filter.1 hr).1 _ ((hiff _).2 ⟨hlt.le, le_rfl⟩)
        rw [hsec.2] at h1 h2
        exact ⟨h1.1, hlt, h2.2⟩)
      (by
        rw [List.pairwise_map]
        refine (hpw.sublist List.filter_sublist).imp_of_mem (fun {r s} hr hs hrs => ?_)
        obtain ⟨⟨hlt, -⟩, hir⟩ := hdata r hr
        obtain ⟨⟨hlt', -⟩, his⟩ := hdata s hs
        by_contra hc
        push Not at hc
        simp only at hc
        set y := (max (secLo r.mem x0) (secLo s.mem x0) + min (secHi r.mem x0) (secHi s.mem x0)) / 2
        have hm : max (secLo r.mem x0) (secLo s.mem x0) < min (secHi r.mem x0) (secHi s.mem x0) := by
          rw [max_lt_iff, lt_min_iff, lt_min_iff]
          exact ⟨⟨hlt, hc.1⟩, hc.2, hlt'⟩
        exact hrs (x0, y) ⟨hir y (by simp only [y]; linarith [le_max_left (secLo r.mem x0) (secLo s.mem x0)])
          (by simp only [y]; linarith [min_le_left (secHi r.mem x0) (secHi s.mem x0)]),
          his y (by simp only [y]; linarith [le_max_right (secLo r.mem x0) (secLo s.mem x0)])
          (by simp only [y]; linarith [min_le_right (secHi r.mem x0) (secHi s.mem x0)])⟩)
      (fun y h1 h2 => by
        obtain ⟨r, hr, hry⟩ := (hun (x0, y)).1 ((hsec.2 y).2 ⟨h1.le, h2.le⟩)
        have hr' : r ∈ l' := List.mem_filter.2 ⟨hr, by simpa using ⟨y, hry⟩⟩
        obtain ⟨⟨-, hiff⟩, -⟩ := hdata r hr'
        exact ⟨_, List.mem_map.2 ⟨r, hr', rfl⟩, (hiff y).1 hry⟩)
    rw [List.map_map] at this
    rw [← this]
    rfl
  · push Not at hne
    rw [secLen_empty hne]
    symm
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
    exact secLen_empty fun y hy => hne y (hsub r hr _ hy)

theorem D_split (t : Tr K) (s : K) :
    det3 t.a t.b (lerp s t.b t.c) = s * t.D ∧ det3 t.a (lerp s t.b t.c) t.c = (1 - s) * t.D := by
  unfold Tr.D det3 lerp; constructor <;> ring

/-- **The midpoint sum of the section lengths of a triangle** is `|D| / 2`, for every strictly
increasing list containing the abscissae of the vertices. -/
theorem msum_secLen {t : Tr K} (ht : t.nd) (s : List K) (hs : s.Pairwise (· < ·))
    (ha : t.a.1 ∈ s) (hb : t.b.1 ∈ s) (hc : t.c.1 ∈ s) :
    msum (secLen t.mem) s = |t.D| / 2 := by
  -- the case where `a` lies strictly between `b` and `c` (in abscissa)
  have mid : ∀ t : Tr K, t.nd → t.a.1 ∈ s → t.b.1 ∈ s → t.c.1 ∈ s →
      (t.b.1 < t.a.1 ∧ t.a.1 < t.c.1 ∨ t.c.1 < t.a.1 ∧ t.a.1 < t.b.1) →
      msum (secLen t.mem) s = |t.D| / 2 := by
    intro t ht ha hb hc hord
    have hbc : t.c.1 - t.b.1 ≠ 0 := by
      rcases hord with h | h <;> intro e <;> linarith [h.1, h.2]
    obtain ⟨σ, hσ⟩ : ∃ σ : K, σ = (t.a.1 - t.b.1) / (t.c.1 - t.b.1) := ⟨_, rfl⟩
    have hσ0 : 0 < σ := by
      rw [hσ]
      rcases hord with h | h
      · exact div_pos (by linarith) (by linarith)
      · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hσ1 : σ < 1 := by
      rw [hσ]
      rcases hord with h | h
      · rw [div_lt_one (by linarith)]; linarith
      · rw [div_lt_one_of_neg (by linarith)]; linarith
    obtain ⟨x, hx⟩ : ∃ x : K × K, x = lerp σ t.b t.c := ⟨_, rfl⟩
    have hx1 : x.1 = t.a.1 := by rw [hx, hσ]; simp only [lerp]; field_simp; ring
    have sp := split ht hσ0 hσ1
    rw [← hx] at sp
    have n1 : (⟨t.a, t.b, x⟩ : Tr K).nd := sp.1 _ (by simp)
    have n2 : (⟨t.a, x, t.c⟩ : Tr K).nd := sp.1 _ (by simp)
    have hcons := consec_sorted (fun w => w = t.a.1 ∨ w = t.b.1 ∨ w = t.c.1) s hs (fun w hw => by
      rcases hw with rfl | rfl | rfl
      · exact Or.inl ha
      · exact Or.inl hb
      · exact Or.inl hc)
    rw [msum_congr (g := fun m => secLen (⟨t.a, t.b, x⟩ : Tr K).mem m +
        secLen (⟨t.a, x, t.c⟩ : Tr K).mem m) (hcons.mono fun a b ⟨_, hw⟩ => by
      have h1 : (a + b) / 2 ≠ t.a.1 := fun e => hw _ (Or.inl rfl) ⟨by linarith, by linarith⟩
      have h2 : (a + b) / 2 ≠ t.b.1 :=
        fun e => hw _ (Or.inr (Or.inl rfl)) ⟨by linarith, by linarith⟩
      have h3 : (a + b) / 2 ≠ t.c.1 :=
        fun e => hw _ (Or.inr (Or.inr rfl)) ⟨by linarith, by linarith⟩
      have hnx : (a + b) / 2 ≠ x.1 := by rw [hx1]; exact h1
      rw [secLen_additive ht sp (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨h1, h2, h3⟩
        · exact ⟨h1, h2, hnx⟩
        · exact ⟨h1, hnx, h3⟩)]
      simp), msum_add]
    have e1 : msum (secLen (⟨t.a, t.b, x⟩ : Tr K).mem) s = |det3 t.a t.b x| / 2 := by
      have n1' : (⟨x, t.a, t.b⟩ : Tr K).nd := by
        show det3 x t.a t.b ≠ 0; rw [← det3_cyc x t.a t.b]; exact n1
      rw [secLen_congr (S := (⟨t.a, t.b, x⟩ : Tr K).mem) (S' := (⟨x, t.a, t.b⟩ : Tr K).mem)
        (fun p => by
          show _ ↔ (Tr.rot (Tr.rot ⟨t.a, t.b, x⟩)).mem p
          rw [Tr.mem_rot, Tr.mem_rot])]
      rw [msum_secLen_vert n1' hx1 s hs (by show x.1 ∈ s; rw [hx1]; exact ha) hb]
      show |det3 x t.a t.b| / 2 = _
      rw [← det3_cyc x t.a t.b]
    have e2 : msum (secLen (⟨t.a, x, t.c⟩ : Tr K).mem) s = |det3 t.a x t.c| / 2 :=
      msum_secLen_vert n2 hx1.symm s hs ha hc
    rw [e1, e2, hx, (D_split t σ).1, (D_split t σ).2, abs_mul, abs_mul, abs_of_pos hσ0,
      abs_of_pos (sub_pos.2 hσ1)]
    ring
  have hrot : msum (secLen t.rot.mem) s = msum (secLen t.mem) s := by
    rw [secLen_congr (S := t.rot.mem) (S' := t.mem) (fun p => Tr.mem_rot)]
  have hrot2 : msum (secLen t.rot.rot.mem) s = msum (secLen t.mem) s := by
    rw [secLen_congr (S := t.rot.rot.mem) (S' := t.mem) (fun p => by rw [Tr.mem_rot, Tr.mem_rot])]
  have n1 : t.rot.nd := Tr.nd_rot.2 ht
  have n2 : t.rot.rot.nd := Tr.nd_rot.2 n1
  -- vertical sides
  by_cases e1 : t.a.1 = t.b.1
  · exact msum_secLen_vert ht e1 s hs ha hc
  by_cases e2 : t.b.1 = t.c.1
  · have := msum_secLen_vert n1 e2 s hs hb ha
    rwa [hrot, Tr.D_rot] at this
  by_cases e3 : t.c.1 = t.a.1
  · have := msum_secLen_vert n2 e3 s hs hc hb
    rwa [hrot2, Tr.D_rot, Tr.D_rot] at this
  -- the middle vertex
  have viaRot : (t.c.1 < t.b.1 ∧ t.b.1 < t.a.1 ∨ t.a.1 < t.b.1 ∧ t.b.1 < t.c.1) →
      msum (secLen t.mem) s = |t.D| / 2 := by
    intro h
    have := mid t.rot n1 hb hc ha h
    rwa [hrot, Tr.D_rot] at this
  have viaRot2 : (t.a.1 < t.c.1 ∧ t.c.1 < t.b.1 ∨ t.b.1 < t.c.1 ∧ t.c.1 < t.a.1) →
      msum (secLen t.mem) s = |t.D| / 2 := by
    intro h
    have := mid t.rot.rot n2 hc ha hb h
    rwa [hrot2, Tr.D_rot, Tr.D_rot] at this
  rcases lt_or_gt_of_ne e1 with h1 | h1 <;> rcases lt_or_gt_of_ne e2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne e3 with h3 | h3
  · exact absurd (h1.trans (h2.trans h3)) (lt_irrefl _)
  · exact viaRot (Or.inr ⟨h1, h2⟩)
  · exact mid t ht ha hb hc (Or.inr ⟨h3, h1⟩)
  · exact viaRot2 (Or.inl ⟨h3, h2⟩)
  · exact viaRot2 (Or.inr ⟨h2, h3⟩)
  · exact mid t ht ha hb hc (Or.inl ⟨h1, h3⟩)
  · exact viaRot (Or.inl ⟨h2, h1⟩)
  · exact absurd (h3.trans (h2.trans h1)) (lt_irrefl _)

/-- **Additivity of the measure of area** (the analytic core of Theorem 29): if a non-degenerate
triangle is decomposed into triangles, `|D|` is the sum of the `|D|` of the pieces. -/
theorem area_additive {T : Tr K} (hT : T.nd) {l : List (Tr K)} (hl : DecS T.mem l) :
    |T.D| = (l.map (fun r => |r.D|)).sum := by
  classical
  set xs : List K := (T :: l).flatMap (fun r => [r.a.1, r.b.1, r.c.1])
  set s := xs.toFinset.sort
  have hs : s.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have hmem : ∀ r ∈ T :: l, r.a.1 ∈ s ∧ r.b.1 ∈ s ∧ r.c.1 ∈ s := by
    intro r hr
    simp only [s, Finset.mem_sort, List.mem_toFinset, xs, List.mem_flatMap]
    exact ⟨⟨r, hr, by simp⟩, ⟨r, hr, by simp⟩, ⟨r, hr, by simp⟩⟩
  have hcons := consec_sorted (fun w => w ∈ s) s hs (fun w hw => Or.inl hw)
  have h1 := msum_secLen hT s hs (hmem T List.mem_cons_self).1 (hmem T List.mem_cons_self).2.1
    (hmem T List.mem_cons_self).2.2
  rw [msum_congr (g := fun x => (l.map (fun r => secLen r.mem x)).sum) (hcons.mono
    fun a b ⟨_, hw⟩ => secLen_additive hT hl (fun r hr => by
      obtain ⟨m1, m2, m3⟩ := hmem r hr
      exact ⟨fun e => hw _ m1 ⟨by linarith, by linarith⟩, fun e => hw _ m2 ⟨by linarith, by linarith⟩,
        fun e => hw _ m3 ⟨by linarith, by linarith⟩⟩)), msum_listSum] at h1
  have h2 : ∀ r ∈ l, msum (secLen r.mem) s = |r.D| / 2 := fun r hr => by
    obtain ⟨m1, m2, m3⟩ := hmem r (List.mem_cons_of_mem _ hr)
    exact msum_secLen (hl.1 r hr) s hs m1 m2 m3
  have e : (l.map (fun r => |r.D| / 2)).sum = (l.map (fun r => |r.D|)).sum / 2 := by
    simp only [div_eq_mul_inv]; rw [List.sum_map_mul_right]
  rw [List.map_congr_left h2, e] at h1
  linarith

/-! ### Common refinement of two decompositions -/

theorem DecS.nodup {S : K × K → Prop} {l : List (Tr K)} (hl : DecS S l) : l.Nodup := by
  refine hl.2.1.imp_of_mem (fun {r s} hr _ h e => ?_)
  subst e
  exact h r.cen ⟨Tr.int_cen (hl.1 r hr), Tr.int_cen (hl.1 r hr)⟩

theorem DecS.eq_of_meet {S : K × K → Prop} {l : List (Tr K)} (hl : DecS S l) {r r' : Tr K}
    (hr : r ∈ l) (hr' : r' ∈ l) {p : K × K} (hp : r.int p) (hp' : r'.mem p) : r = r' := by
  obtain ⟨q, h1, h2⟩ := Tr.int_meet (hl.1 r hr) (hl.1 r' hr') hp hp'
  by_contra hne
  have : Std.Symm (fun r s : Tr K => ∀ p, ¬(r.int p ∧ s.int p)) :=
    ⟨fun a b h p hp => h p ⟨hp.2, hp.1⟩⟩
  exact hl.2.1.forall hr hr' hne q ⟨h1, h2⟩

open Classical in
/-- **Common refinement** of two decompositions of a region: a decomposition `Q` and maps `j₁`,
`j₂` assigning to each piece a triangle of each decomposition containing it, such that the pieces
assigned to a triangle decompose it. -/
theorem common_refinement {S : K × K → Prop} {l1 l2 : List (Tr K)} (h1 : DecS S l1)
    (h2 : DecS S l2) :
    ∃ (Q : List (Tr K)) (j1 j2 : Tr K → Tr K), DecS S Q ∧
      (∀ q ∈ Q, j1 q ∈ l1 ∧ j2 q ∈ l2 ∧ (∀ p, q.mem p → (j1 q).mem p) ∧
        (∀ p, q.mem p → (j2 q).mem p)) ∧
      (∀ r ∈ l1, DecS r.mem (Q.filter (fun q => j1 q = r))) ∧
      (∀ r ∈ l2, DecS r.mem (Q.filter (fun q => j2 q = r))) := by
  set R : Tr K → List (Tr K) := fun r => cutAll (edges l2) r
  set Q := l1.flatMap R
  have hQ : DecS S Q := h1.flatMap R (fun r hr => (cutAll_spec _ (h1.1 r hr)).1)
  have ex1 : ∀ q ∈ Q, ∃ r ∈ l1, q ∈ R r := fun q hq => List.mem_flatMap.1 hq
  have ex2 : ∀ q ∈ Q, ∃ r ∈ l2, ∀ p, q.mem p → r.mem p := by
    intro q hq
    obtain ⟨r, hr, hqr⟩ := ex1 q hq
    exact refine_sub (h1.1 r hr) h2.1 (fun p hp => (h2.2.2 p).1 (h1.sub hr hp)) q hqr
  let j1 : Tr K → Tr K := fun q => if h : ∃ r ∈ l1, q ∈ R r then h.choose else q
  let j2 : Tr K → Tr K := fun q => if h : ∃ r ∈ l2, ∀ p, q.mem p → r.mem p then h.choose else q
  have hj1 : ∀ q ∈ Q, j1 q ∈ l1 ∧ ∀ p, q.mem p → (j1 q).mem p := by
    intro q hq
    have h := ex1 q hq
    simp only [j1, dif_pos h]
    obtain ⟨hr, hqr⟩ := h.choose_spec
    exact ⟨hr, fun p hp => ((cutAll_spec _ (h1.1 _ hr)).1.2.2 p).2 ⟨q, hqr, hp⟩⟩
  have hj2 : ∀ q ∈ Q, j2 q ∈ l2 ∧ ∀ p, q.mem p → (j2 q).mem p := by
    intro q hq
    have h := ex2 q hq
    simp only [j2, dif_pos h]
    exact h.choose_spec
  -- the pieces assigned to a triangle decompose it
  have fib : ∀ (l : List (Tr K)) (j : Tr K → Tr K), DecS S l →
      (∀ q ∈ Q, j q ∈ l ∧ ∀ p, q.mem p → (j q).mem p) →
      ∀ r ∈ l, DecS r.mem (Q.filter (fun q => j q = r)) := by
    intro l j hl hj r hr
    refine ⟨fun q hq => hQ.1 q (List.mem_filter.1 hq).1,
      hQ.2.1.sublist List.filter_sublist, fun p => ⟨fun hp => ?_, fun ⟨q, hq, hqp⟩ => ?_⟩⟩
    · refine Tr.mem_cover_of_int_cover (hl.1 r hr) _ (fun x hx => ?_) hp
      obtain ⟨q, hq, hqx⟩ := (hQ.2.2 x).1 (hl.sub hr (Tr.mem_of_int hx))
      obtain ⟨hjq, hsub⟩ := hj q hq
      have := hl.eq_of_meet hr hjq hx (hsub x hqx)
      exact ⟨q, List.mem_filter.2 ⟨hq, by simp [this]⟩, hqx⟩
    · obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
      simp only [decide_eq_true_eq] at hq2
      rw [← hq2]
      exact (hj q hq1).2 p hqp
  exact ⟨Q, j1, j2, hQ, fun q hq => ⟨(hj1 q hq).1, (hj2 q hq).1, (hj1 q hq).2, (hj2 q hq).2⟩,
    fib l1 j1 h1 hj1, fib l2 j2 h2 hj2⟩

theorem sum_fiber {α β : Type*} [DecidableEq β] (Q : List α) (l : List β) (j : α → β)
    (hl : l.Nodup) (hj : ∀ q ∈ Q, j q ∈ l) (f : α → K) :
    (l.map (fun r => ((Q.filter (fun q => j q = r)).map f).sum)).sum = (Q.map f).sum := by
  induction Q with
  | nil => simp
  | cons q Q ih =>
    have hq := hj q List.mem_cons_self
    have ih' := ih (fun q' hq' => hj q' (List.mem_cons_of_mem _ hq'))
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    have : ∀ r, ((if decide (j q = r) = true then q :: Q.filter (fun q => j q = r)
        else Q.filter (fun q => j q = r)).map f).sum =
        (if j q = r then f q else 0) + ((Q.filter (fun q => j q = r)).map f).sum := by
      intro r; by_cases h : j q = r <;> simp [h]
    simp only [this, List.sum_map_add, ih']
    congr 1
    rw [← List.sum_toFinset _ hl, Finset.sum_ite_eq]
    simp [List.mem_toFinset.2 hq]

/-- **The sum of the measures over a decomposition only depends on the region.** -/
theorem decS_sum_eq {S : K × K → Prop} {l1 l2 : List (Tr K)} (h1 : DecS S l1) (h2 : DecS S l2) :
    (l1.map (fun r => |r.D|)).sum = (l2.map (fun r => |r.D|)).sum := by
  classical
  obtain ⟨Q, j1, j2, -, hj, f1, f2⟩ := common_refinement h1 h2
  have e1 : (l1.map (fun r => |r.D|)).sum = (Q.map (fun r => |r.D|)).sum := by
    rw [← sum_fiber Q l1 j1 h1.nodup (fun q hq => (hj q hq).1)]
    congr 1
    exact List.map_congr_left (fun r hr => area_additive (h1.1 r hr) (f1 r hr))
  have e2 : (l2.map (fun r => |r.D|)).sum = (Q.map (fun r => |r.D|)).sum := by
    rw [← sum_fiber Q l2 j2 h2.nodup (fun q hq => (hj q hq).2.1)]
    congr 1
    exact List.map_congr_left (fun r hr => area_additive (h2.1 r hr) (f2 r hr))
  rw [e1, e2]

end Areas

end HilbertFoundations
