import HilbertFoundations.AreasAux6

/-!
# Helper module for `Areas.lean`: proper parts, and bounded decompositions

This module contains no unit of Hilbert's text. Over a linearly ordered field `K`:

* **a proper part has smaller measure** (`kmeasure_lt_of_sub`): cutting a decomposition of `T`
  by the side lines of one of `S ⊆ T`, the pieces with centroid in `S` decompose `S`, the others
  have positive measure;
* **diameters**: the squared distance of two points of a triangle is at most the largest squared
  side (`sqd_le_of_mem`);
* **equal area with a bounded triangle bounds lengths** (`sqd_le_of_kEqArea`): if a triangle
  `abc`, all of whose squared sides are `≤ R`, is of equal area with a triangle `abd` by a
  decomposition into `n` triangles, then `sqd a d ≤ n² R` (pigeonhole on `n + 1` points of the
  segment `ad`). In a non-archimedean field this excludes equal area for `d` far away.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Proper parts -/

theorem side_of_int {u v : K × K} {q : Tr K} (hq : q.nd) (hs : OnSide u v q) {y : K × K}
    (hy : q.int y) {κ : K} (hκ : 0 < κ * det3 u v y) : ∀ p, q.mem p → 0 ≤ κ * det3 u v p := by
  rcases hs with h | h
  · have hy0 := h y (Tr.mem_of_int hy)
    have hfy : 0 < det3 u v y := by
      refine lt_of_le_of_ne hy0 (fun e => ?_)
      rw [← e, mul_zero] at hκ
      exact lt_irrefl _ hκ
    have hk : 0 < κ := by
      by_contra hc; push Not at hc; nlinarith
    exact fun p hp => mul_nonneg hk.le (h p hp)
  · have hy0 := h y (Tr.mem_of_int hy)
    have hfy : det3 u v y < 0 := by
      refine lt_of_le_of_ne hy0 (fun e => ?_)
      rw [e, mul_zero] at hκ
      exact lt_irrefl _ hκ
    have hk : κ < 0 := by
      by_contra hc; push Not at hc; nlinarith
    exact fun p hp => mul_nonneg_of_nonpos_of_nonpos hk.le (h p hp)

/-- A piece lying on one side of each side line of `s` and meeting the interior of `s` lies
in `s`. -/
theorem sub_of_int_meet {q s : Tr K} (hq : q.nd) (hs : s.nd)
    (hside : ∀ uv ∈ edges [s], OnSide uv.1 uv.2 q) {y : K × K} (hyq : q.int y) (hys : s.int y) :
    ∀ p, q.mem p → s.mem p := by
  intro p hp
  have e1 : ((s.b, s.c) : (K × K) × (K × K)) ∈ edges [s] := by simp [edges]
  have e2 : ((s.c, s.a) : (K × K) × (K × K)) ∈ edges [s] := by simp [edges]
  have e3 : ((s.a, s.b) : (K × K) × (K × K)) ∈ edges [s] := by simp [edges]
  exact ⟨side_of_int hq (hside _ e1) hyq hys.1 p hp, side_of_int hq (hside _ e2) hyq hys.2.1 p hp,
    side_of_int hq (hside _ e3) hyq hys.2.2 p hp⟩

open Classical in
/-- **A proper part has smaller measure.** -/
theorem kmeasure_lt_of_sub {S T : K × K → Prop} {lS lT : List (Tr K)} (hS : DecS S lS)
    (hT : DecS T lT) (hsub : ∀ p, S p → T p) (hne : ∃ p, T p ∧ ¬S p) :
    kmeasure S < kmeasure T := by
  set Q := lT.flatMap (cutAll (edges lS))
  have hQ : DecS T Q := hT.flatMap _ (fun r hr => (cutAll_spec _ (hT.1 r hr)).1)
  have hQside : ∀ q ∈ Q, ∀ uv ∈ edges lS, OnSide uv.1 uv.2 q := by
    intro q hq uv huv
    obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.1 hq
    exact (cutAll_spec _ (hT.1 r hr)).2 q hqr uv huv
  have hedges : ∀ s ∈ lS, ∀ uv ∈ edges [s], uv ∈ edges lS := by
    intro s hs uv huv
    simp only [edges, List.flatMap_cons, List.flatMap_nil, List.append_nil] at huv
    exact List.mem_flatMap.2 ⟨s, hs, huv⟩
  set Qin := Q.filter (fun q => S q.cen)
  set Qout := Q.filter (fun q => ¬S q.cen)
  -- the pieces with centroid in `S` lie in `S`
  have hin : ∀ q ∈ Q, S q.cen → ∃ s ∈ lS, ∀ p, q.mem p → s.mem p := by
    intro q hq hc
    obtain ⟨s, hs, hsc⟩ := (hS.2.2 q.cen).1 hc
    obtain ⟨y, hy1, hy2⟩ := Tr.int_meet (hQ.1 q hq) (hS.1 s hs) (Tr.int_cen (hQ.1 q hq)) hsc
    exact ⟨s, hs, sub_of_int_meet (hQ.1 q hq) (hS.1 s hs)
      (fun uv huv => hQside q hq uv (hedges s hs uv huv)) hy1 hy2⟩
  have dIn : DecS S Qin := by
    refine ⟨fun q hq => hQ.1 q (List.mem_filter.1 hq).1, hQ.2.1.sublist List.filter_sublist,
      fun p => ⟨fun hp => ?_, fun ⟨q, hq, hqp⟩ => ?_⟩⟩
    · obtain ⟨s, hs, hsp⟩ := (hS.2.2 p).1 hp
      refine Tr.mem_cover_of_int_cover (hS.1 s hs) Qin (fun x hx => ?_) hsp
      obtain ⟨q, hq, hqx⟩ := (hQ.2.2 x).1 (hsub x (hS.sub hs (Tr.mem_of_int hx)))
      obtain ⟨y, hy1, hy2⟩ := Tr.int_meet (hS.1 s hs) (hQ.1 q hq) hx hqx
      have hqs := sub_of_int_meet (hQ.1 q hq) (hS.1 s hs)
        (fun uv huv => hQside q hq uv (hedges s hs uv huv)) hy2 hy1
      exact ⟨q, List.mem_filter.2 ⟨hq, by
        simpa using hS.sub hs (hqs _ (Tr.mem_of_int (Tr.int_cen (hQ.1 q hq))))⟩, hqx⟩
    · obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
      simp only [decide_eq_true_eq] at hq2
      obtain ⟨s, hs, hqs⟩ := hin q hq1 hq2
      exact hS.sub hs (hqs p hqp)
  -- some piece has its centroid outside `S`
  have hout : Qout ≠ [] := by
    intro hnil
    obtain ⟨p, hpT, hpS⟩ := hne
    obtain ⟨q, hq, hqp⟩ := (hQ.2.2 p).1 hpT
    by_cases hc : S q.cen
    · obtain ⟨s, hs, hqs⟩ := hin q hq hc
      exact hpS (hS.sub hs (hqs p hqp))
    · have : q ∈ Qout := List.mem_filter.2 ⟨hq, by simpa using hc⟩
      rw [hnil] at this
      exact absurd this List.not_mem_nil
  have dOut : DecS (fun p => ∃ q ∈ Qout, q.mem p) Qout :=
    ⟨fun q hq => hQ.1 q (List.mem_filter.1 hq).1, hQ.2.1.sublist List.filter_sublist,
      fun _ => Iff.rfl⟩
  have hpos := kmeasure_pos dOut hout
  rw [kmeasure_of_decS dOut] at hpos
  rw [kmeasure_of_decS dIn, kmeasure_of_decS hQ]
  have e' : ∀ L : List (Tr K), ((L.filter (fun q => S q.cen)).map (fun r => |r.D|)).sum +
      ((L.filter (fun q => ¬S q.cen)).map (fun r => |r.D|)).sum = (L.map (fun r => |r.D|)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      by_cases hx : S x.cen
      · rw [List.filter_cons_of_pos (by simpa using hx),
          List.filter_cons_of_neg (by simpa using hx)]
        simp only [List.map_cons, List.sum_cons]
        linarith
      · rw [List.filter_cons_of_neg (by simpa using hx),
          List.filter_cons_of_pos (by simpa using hx)]
        simp only [List.map_cons, List.sum_cons]
        linarith
  have e : (Qin.map (fun r => |r.D|)).sum + (Qout.map (fun r => |r.D|)).sum =
      (Q.map (fun r => |r.D|)).sum := e' Q
  rw [← e]
  linarith

/-! ### Diameters of triangles -/

theorem sqd_comb (a b c q : K × K) {α β γ : K} (h : α + β + γ = 1) :
    sqd (comb α β γ a b c) q = α * sqd a q + β * sqd b q + γ * sqd c q -
      (α * β * sqd a b + α * γ * sqd a c + β * γ * sqd b c) := by
  have hγ : γ = 1 - α - β := by linear_combination h
  subst hγ
  unfold sqd comb; ring

theorem sqd_nonneg (p q : K × K) : 0 ≤ sqd p q := by
  unfold sqd; nlinarith [mul_self_nonneg (p.1 - q.1), mul_self_nonneg (p.2 - q.2)]

theorem sqd_self (p : K × K) : sqd p p = 0 := by unfold sqd; ring

/-- A point of a triangle is within the largest squared side of a vertex... and of any point. -/
theorem sqd_le_of_mem {t : Tr K} (ht : t.nd) {R : K} (hab : sqd t.a t.b ≤ R)
    (hac : sqd t.a t.c ≤ R) (hbc : sqd t.b t.c ≤ R) {p q : K × K} (hp : t.mem p)
    (hq : t.mem q) : sqd p q ≤ R := by
  have hR : 0 ≤ R := le_trans (sqd_nonneg _ _) hab
  -- first, every vertex is within `R` of `q`
  have vert : ∀ v : K × K, (v = t.a ∨ v = t.b ∨ v = t.c) → sqd v q ≤ R := by
    intro v hv
    obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.mem_iff_bary ht).1 hq
    rw [sqd_comm, sqd_comb _ _ _ _ hs]
    have k1 : sqd t.a v ≤ R := by
      rcases hv with rfl | rfl | rfl
      · rw [sqd_self]; exact hR
      · exact hab
      · exact hac
    have k2 : sqd t.b v ≤ R := by
      rcases hv with rfl | rfl | rfl
      · rw [sqd_comm]; exact hab
      · rw [sqd_self]; exact hR
      · exact hbc
    have k3 : sqd t.c v ≤ R := by
      rcases hv with rfl | rfl | rfl
      · rw [sqd_comm]; exact hac
      · rw [sqd_comm]; exact hbc
      · rw [sqd_self]; exact hR
    have := mul_le_mul_of_nonneg_left k1 h1
    have := mul_le_mul_of_nonneg_left k2 h2
    have := mul_le_mul_of_nonneg_left k3 h3
    have := mul_nonneg (mul_nonneg h1 h2) (sqd_nonneg t.a t.b)
    have := mul_nonneg (mul_nonneg h1 h3) (sqd_nonneg t.a t.c)
    have := mul_nonneg (mul_nonneg h2 h3) (sqd_nonneg t.b t.c)
    have e : α * R + β * R + γ * R = R := by rw [← add_mul, ← add_mul, hs, one_mul]
    linarith
  obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.mem_iff_bary ht).1 hp
  rw [sqd_comb _ _ _ _ hs]
  have k1 := vert t.a (Or.inl rfl)
  have k2 := vert t.b (Or.inr (Or.inl rfl))
  have k3 := vert t.c (Or.inr (Or.inr rfl))
  have := mul_le_mul_of_nonneg_left k1 h1
  have := mul_le_mul_of_nonneg_left k2 h2
  have := mul_le_mul_of_nonneg_left k3 h3
  have := mul_nonneg (mul_nonneg h1 h2) (sqd_nonneg t.a t.b)
  have := mul_nonneg (mul_nonneg h1 h3) (sqd_nonneg t.a t.c)
  have := mul_nonneg (mul_nonneg h2 h3) (sqd_nonneg t.b t.c)
  have e : α * R + β * R + γ * R = R := by rw [← add_mul, ← add_mul, hs, one_mul]
  linarith

/-- **Equal area with a bounded triangle bounds the lengths**: if the triangle `t₀` (all squared
sides `≤ R`) is of equal area with a region containing the segment `pq`, by decompositions into
`n` triangles, then `sqd p q ≤ n² R`. -/
theorem sqd_le_of_kEqArea {t₀ : Tr K} (ht₀ : t₀.nd) {R : K} (hab : sqd t₀.a t₀.b ≤ R)
    (hac : sqd t₀.a t₀.c ≤ R) (hbc : sqd t₀.b t₀.c ≤ R) {T : K × K → Prop} {l m : List (Tr K)}
    (hl : DecS t₀.mem l) (hm : DecS T m) (hc : List.Forall₂ KCong l m) {p q : K × K}
    (hseg : ∀ s : K, 0 ≤ s → s ≤ 1 → T (lerp s p q)) :
    sqd p q ≤ (m.length : K) * (m.length : K) * R := by
  -- every triangle of `m` has diameter `≤ R`
  have hdiam : ∀ r ∈ m, ∀ x y, r.mem x → r.mem y → sqd x y ≤ R := by
    intro r hr x y hx hy
    obtain ⟨r0, hr0, hcg⟩ := forall₂_mem_right hc hr
    have hr0nd := hl.1 r0 hr0
    have hsub : ∀ z, r0.mem z → t₀.mem z := fun z hz => hl.sub hr0 hz
    have b1 := sqd_le_of_mem ht₀ hab hac hbc (hsub _ (Tr.mem_a hr0nd)) (hsub _ (Tr.mem_b hr0nd))
    have b2 := sqd_le_of_mem ht₀ hab hac hbc (hsub _ (Tr.mem_a hr0nd)) (hsub _ (Tr.mem_c hr0nd))
    have b3 := sqd_le_of_mem ht₀ hab hac hbc (hsub _ (Tr.mem_b hr0nd)) (hsub _ (Tr.mem_c hr0nd))
    rw [hcg.1] at b1; rw [hcg.2.1] at b2; rw [hcg.2.2] at b3
    exact sqd_le_of_mem (hm.1 r hr) b1 b2 b3 hx hy
  have hR : 0 ≤ R := le_trans (sqd_nonneg _ _) hab
  by_cases hn : m.length = 0
  · -- no triangle: the region is empty, contradicting the segment
    exfalso
    have := hseg 0 le_rfl zero_le_one
    obtain ⟨r, hr, -⟩ := (hm.2.2 _).1 this
    have : m = [] := List.length_eq_zero_iff.1 hn
    rw [this] at hr
    exact absurd hr List.not_mem_nil
  have hnpos : (0 : K) < m.length := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn0 : (m.length : K) ≠ 0 := hnpos.ne'
  -- the points `p + (i / n) (q - p)`, `i = 0, …, n`, and a triangle containing each
  have hcov : ∀ i : Fin (m.length + 1), ∃ j : Fin m.length,
      m[j].mem (lerp (((i : ℕ) : K) / m.length) p q) := by
    intro i
    have hi : ((i : ℕ) : K) / m.length ≤ 1 := by
      rw [div_le_one hnpos]; exact_mod_cast Nat.lt_succ_iff.1 i.2
    obtain ⟨r, hr, hrx⟩ := (hm.2.2 _).1 (hseg _ (by positivity) hi)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    exact ⟨⟨j, hj⟩, hrx⟩
  choose f hf using hcov
  obtain ⟨i, i', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have h1 := hf i
  have h2 := hf i'
  rw [heq] at h1
  have hd := hdiam _ (List.getElem_mem _) _ _ h1 h2
  -- the squared distance of the two points
  have e : sqd (lerp (((i : ℕ) : K) / m.length) p q) (lerp (((i' : ℕ) : K) / m.length) p q) =
      ((((i : ℕ) : K) - ((i' : ℕ) : K)) / m.length) *
        ((((i : ℕ) : K) - ((i' : ℕ) : K)) / m.length) * sqd p q := by
    unfold sqd lerp; field_simp; ring
  rw [e] at hd
  have hii : (1 : K) ≤ (((i : ℕ) : K) - ((i' : ℕ) : K)) * (((i : ℕ) : K) - ((i' : ℕ) : K)) := by
    have : (i : ℕ) ≠ i' := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne this with h | h
    · have : ((i : ℕ) : K) + 1 ≤ i' := by exact_mod_cast h
      nlinarith
    · have : ((i' : ℕ) : K) + 1 ≤ i := by exact_mod_cast h
      nlinarith
  have hsq := sqd_nonneg p q
  have key : sqd p q ≤
      (((i : ℕ) : K) - ((i' : ℕ) : K)) * (((i : ℕ) : K) - ((i' : ℕ) : K)) * sqd p q := by
    nlinarith
  have e2 : ((((i : ℕ) : K) - ((i' : ℕ) : K)) / m.length) *
      ((((i : ℕ) : K) - ((i' : ℕ) : K)) / m.length) * sqd p q * (m.length * m.length) =
      (((i : ℕ) : K) - ((i' : ℕ) : K)) * (((i : ℕ) : K) - ((i' : ℕ) : K)) * sqd p q := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_right hd (mul_self_nonneg (m.length : K))
  rw [e2] at h3
  linarith

end Areas

end HilbertFoundations
