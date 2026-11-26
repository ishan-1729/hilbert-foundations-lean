import HilbertFoundations.AreasAux5

/-!
# Helper module for `Areas.lean`: decompositions without interior points of division

This module contains no unit of Hilbert's text. Over a linearly ordered field `K` it proves
Hilbert's lemma of § 20 (unit `s20.transversal_series`): a decomposition of a triangle `abc`
none of whose vertices lies in the interior of `abc` or within the side `bc` is a series of
transversal decompositions.

* `KTD t l`: `l` arises from `t` by a series of transversal decompositions (co-ordinates);
* `decS_erase`: removing from a decomposition of `T = r ∪ q` (`r`, `q` on the two sides of a line)
  the triangle `r` leaves a decomposition of `q`;
* `piece_at_mid`: the triangle of the decomposition containing the midpoint of `bc` has the
  vertices `b`, `c` and a third vertex `w`;
* `trans_series_K`: the lemma, by induction on the number of triangles: `w` is `a` (one triangle),
  or lies within `ca` (the transversal `bw` cuts off `bcw`) or within `ab` (the transversal `cw`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

open Classical

/-- `l` arises from `t` by a **series of transversal decompositions** (in co-ordinates). -/
inductive KTD : Tr K → List (Tr K) → Prop
  | single (t : Tr K) : KTD t [t]
  | split {a b c : K × K} {s : K} {l₁ l₂ : List (Tr K)} : b ≠ c → 0 < s → s < 1 →
      KTD ⟨a, b, lerp s b c⟩ l₁ → KTD ⟨a, lerp s b c, c⟩ l₂ → KTD ⟨a, b, c⟩ (l₁ ++ l₂)
  | rot {t : Tr K} {l : List (Tr K)} : KTD t l → KTD t.rot l

theorem pw_disj_of_ne {l : List (Tr K)} (h : l.Pairwise (fun r s => ∀ p, ¬(r.int p ∧ s.int p)))
    {r s : Tr K} (hr : r ∈ l) (hs : s ∈ l) (hne : r ≠ s) : ∀ p, ¬(r.int p ∧ s.int p) := by
  induction l with
  | nil => simp at hr
  | cons x l ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hr with rfl | hr' <;> rcases List.mem_cons.1 hs with rfl | hs'
    · exact absurd rfl hne
    · exact h.1 s hs'
    · intro p hp; exact h.1 r hr' p ⟨hp.2, hp.1⟩
    · exact ih h.2 hr' hs'

theorem lerp_int_of_mem {r : Tr K} (hr : r.nd) {p : K × K} (hp : r.mem p) {s : K} (hs0 : 0 < s)
    (hs1 : s ≤ 1) : r.int (lerp s p r.cen) := by
  rw [Tr.mem_iff_l hr] at hp
  rw [Tr.int_iff_l hr, Tr.la_lerp, Tr.lb_lerp, Tr.lc_lerp, Tr.la_cen hr, Tr.lb_cen hr,
    Tr.lc_cen hr]
  have h1 : 0 ≤ 1 - s := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := mul_nonneg h1 hp.1; linarith
  · have := mul_nonneg h1 hp.2.1; linarith
  · have := mul_nonneg h1 hp.2.2; linarith

theorem pos_of_eq {D x k : K} (h : x = k * D) (hk : 0 < k) (hD : D ≠ 0) : 0 < D * x := by
  rw [h, show D * (k * D) = k * (D * D) by ring]; exact mul_pos hk (mul_self_pos.2 hD)

theorem neg_of_eq {D x k : K} (h : x = k * D) (hk : k < 0) (hD : D ≠ 0) : D * x < 0 := by
  rw [h, show D * (k * D) = k * (D * D) by ring]; exact mul_neg_of_neg_of_pos hk (mul_self_pos.2 hD)

theorem side_nonneg {r : Tr K} (hr : r.nd) {κ : K} {u v : K × K} (ha : 0 ≤ κ * det3 u v r.a)
    (hb : 0 ≤ κ * det3 u v r.b) (hc : 0 ≤ κ * det3 u v r.c) {p : K × K} (hp : r.mem p) :
    0 ≤ κ * det3 u v p := by
  obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.mem_iff_bary hr).1 hp
  rw [det3_comb _ _ hs]
  have e : κ * (α * det3 u v r.a + β * det3 u v r.b + γ * det3 u v r.c) =
      α * (κ * det3 u v r.a) + β * (κ * det3 u v r.b) + γ * (κ * det3 u v r.c) := by ring
  rw [e]
  have := mul_nonneg h1 ha; have := mul_nonneg h2 hb; have := mul_nonneg h3 hc; linarith

theorem side_nonpos {r : Tr K} (hr : r.nd) {κ : K} {u v : K × K} (ha : κ * det3 u v r.a ≤ 0)
    (hb : κ * det3 u v r.b ≤ 0) (hc : κ * det3 u v r.c ≤ 0) {p : K × K} (hp : r.mem p) :
    κ * det3 u v p ≤ 0 := by
  have := side_nonneg hr (κ := -κ) (u := u) (v := v) (by linarith) (by linarith) (by linarith) hp
  linarith

theorem side_neg_int {r : Tr K} (hr : r.nd) {κ : K} {u v : K × K} (ha : κ * det3 u v r.a < 0)
    (hb : κ * det3 u v r.b ≤ 0) (hc : κ * det3 u v r.c ≤ 0) {p : K × K} (hp : r.int p) :
    κ * det3 u v p < 0 := by
  obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.int_iff_bary hr).1 hp
  rw [det3_comb _ _ hs]
  have e : κ * (α * det3 u v r.a + β * det3 u v r.b + γ * det3 u v r.c) =
      α * (κ * det3 u v r.a) + β * (κ * det3 u v r.b) + γ * (κ * det3 u v r.c) := by ring
  rw [e]
  have := mul_neg_of_pos_of_neg h1 ha
  have := mul_nonpos_iff.2 (Or.inl ⟨h2.le, hb⟩)
  have := mul_nonpos_iff.2 (Or.inl ⟨h3.le, hc⟩)
  linarith

/-- **Removing a triangle cut off by a line**: if `T` is the union of `r` and `q`, which lie on the
two sides of a line, and `l` decomposes `T` with `r ∈ l`, then `l` without `r` decomposes `q`. -/
theorem decS_erase {T : K × K → Prop} {l : List (Tr K)} (hl : DecS T l) {r q : Tr K} (hr : r ∈ l)
    (hq : q.nd) {κ : K} {u v : K × K}
    (hT : ∀ p, T p → r.mem p ∨ q.mem p) (hTq : ∀ p, q.mem p → T p)
    (hrs : ∀ p, r.mem p → 0 ≤ κ * det3 u v p) (hqs : ∀ p, q.mem p → κ * det3 u v p ≤ 0)
    (hqint : ∀ p, q.int p → κ * det3 u v p < 0)
    (hstrict : ∀ p, T p → ¬q.mem p → 0 < κ * det3 u v p) :
    DecS q.mem (l.erase r) := by
  have hsub : (l.erase r).Sublist l := List.erase_sublist
  have hnd := hl.nodup
  refine ⟨fun r' h => hl.1 r' (hsub.subset h), hl.2.1.sublist hsub, fun p => ?_⟩
  constructor
  · intro hp
    refine Tr.mem_cover_of_int_cover hq (l.erase r) (fun p' hp' => ?_) hp
    obtain ⟨r', hr', hm⟩ := (hl.2.2 p').1 (hTq p' (Tr.mem_of_int hp'))
    have hne : r' ≠ r := by
      rintro rfl; have := hrs p' hm; have := hqint p' hp'; linarith
    exact ⟨r', (List.mem_erase_of_ne hne).2 hr', hm⟩
  · rintro ⟨r', hr', hm⟩
    obtain ⟨hne, hr'l⟩ := (List.Nodup.mem_erase_iff hnd).1 hr'
    by_contra hnq
    have hTp : T p := (hl.2.2 p).2 ⟨r', hr'l, hm⟩
    have hgp := hstrict p hTp hnq
    have hnd' := hl.1 r' hr'l
    obtain ⟨ε, hε, hsm⟩ := small_pos (κ * det3 u v r'.cen) hgp
    set s0 := min (ε / 2) (1 / 2) with hs0
    have hs0p : 0 < s0 := lt_min (half_pos hε) (by norm_num)
    have hs0ε : s0 < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have hs01 : s0 ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
    have hint : r'.int (lerp s0 p r'.cen) := lerp_int_of_mem hnd' hm hs0p hs01
    have hgq : 0 < κ * det3 u v (lerp s0 p r'.cen) := by
      rw [det3_lerp]
      have := hsm s0 hs0p hs0ε
      linarith [show κ * ((1 - s0) * det3 u v p + s0 * det3 u v r'.cen) =
        (1 - s0) * (κ * det3 u v p) + s0 * (κ * det3 u v r'.cen) by ring]
    have hTq0 : T (lerp s0 p r'.cen) := (hl.2.2 _).2 ⟨r', hr'l, Tr.mem_of_int hint⟩
    rcases hT _ hTq0 with h | h
    · obtain ⟨q', h1, h2⟩ := Tr.int_meet hnd' (hl.1 r hr) hint h
      exact pw_disj_of_ne hl.2.1 hr'l hr hne q' ⟨h1, h2⟩
    · have := hqs _ h; linarith

/-- A point of the closed triangle `abc` on the line `bc` and not within `bc` is `b` or `c`. -/
theorem on_bc {a b c v : K × K} (ht : (Tr.mk a b c).nd) (hv : (Tr.mk a b c).mem v)
    (h0 : (Tr.mk a b c).la v = 0) (hfree : ∀ s : K, 0 < s → s < 1 → v ≠ lerp s b c) :
    v = b ∨ v = c := by
  have hm := (Tr.mem_iff_l ht).1 hv
  have hsum := Tr.l_sum ht v
  have hrec := Tr.l_recon ht v
  obtain ⟨x, hx⟩ : ∃ x, x = (Tr.mk a b c).la v := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = (Tr.mk a b c).lb v := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = (Tr.mk a b c).lc v := ⟨_, rfl⟩
  rw [← hx, ← hy, ← hz] at hrec hsum
  rw [← hx] at h0
  rw [← hx, ← hy, ← hz] at hm
  simp only at hrec
  by_cases hz0 : z = 0
  · left
    have hy1 : y = 1 := by linarith
    rw [hrec, h0, hy1, hz0]; simp [comb]
  by_cases hz1 : z = 1
  · right
    have hy0 : y = 0 := by linarith
    rw [hrec, h0, hy0, hz1]; simp [comb]
  exfalso
  have hzp : 0 < z := lt_of_le_of_ne hm.2.2 (Ne.symm hz0)
  have hzl : z < 1 := lt_of_le_of_ne (by linarith) hz1
  apply hfree z hzp hzl
  rw [hrec, h0, show y = 1 - z by linarith]
  simp only [comb, lerp]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-- **The triangle at the midpoint of the free side** has the vertices `b`, `c` and a third
vertex `w`. -/
theorem piece_at_mid {a b c : K × K} (ht : (Tr.mk a b c).nd) {r : Tr K} (hr : r.nd)
    (hsub : ∀ p, r.mem p → (Tr.mk a b c).mem p)
    (hfree : ∀ v ∈ [r.a, r.b, r.c], ∀ s : K, 0 < s → s < 1 → v ≠ lerp s b c)
    (hm : r.mem (lerp (1 / 2) b c)) :
    ∃ w ∈ [r.a, r.b, r.c], TrEquiv r (Tr.mk w b c) := by
  have hbc : b ≠ c := Tr.nd_ne_bc ht
  obtain ⟨α, β, γ, h1, h2, h3, hs, hmid⟩ := (Tr.mem_iff_bary hr).1 hm
  have hva := hsub _ (Tr.mem_a hr)
  have hvb := hsub _ (Tr.mem_b hr)
  have hvc := hsub _ (Tr.mem_c hr)
  have la0 : (Tr.mk a b c).la (lerp (1 / 2) b c) = 0 := by
    rw [Tr.la_lerp]
    have e1 : (Tr.mk a b c).la b = 0 := Tr.la_b _
    have e2 : (Tr.mk a b c).la c = 0 := Tr.la_c _
    rw [e1, e2]; ring
  have e := la0
  rw [hmid, Tr.la_comb _ hs] at e
  have na := ((Tr.mem_iff_l ht).1 hva).1
  have nb := ((Tr.mem_iff_l ht).1 hvb).1
  have nc := ((Tr.mem_iff_l ht).1 hvc).1
  have ma := mul_nonneg h1 na
  have mb := mul_nonneg h2 nb
  have mc := mul_nonneg h3 nc
  have za : α * (Tr.mk a b c).la r.a = 0 := by linarith
  have zb : β * (Tr.mk a b c).la r.b = 0 := by linarith
  have zc : γ * (Tr.mk a b c).la r.c = 0 := by linarith
  have ka : α = 0 ∨ r.a = b ∨ r.a = c := by
    rcases eq_or_ne α 0 with h | h
    · exact Or.inl h
    · exact Or.inr (on_bc ht hva ((mul_eq_zero.1 za).resolve_left h) (hfree _ (by simp)))
  have kb : β = 0 ∨ r.b = b ∨ r.b = c := by
    rcases eq_or_ne β 0 with h | h
    · exact Or.inl h
    · exact Or.inr (on_bc ht hvb ((mul_eq_zero.1 zb).resolve_left h) (hfree _ (by simp)))
  have kc : γ = 0 ∨ r.c = b ∨ r.c = c := by
    rcases eq_or_ne γ 0 with h | h
    · exact Or.inl h
    · exact Or.inr (on_bc ht hvc ((mul_eq_zero.1 zc).resolve_left h) (hfree _ (by simp)))
  have comb_const : ∀ q : K × K, (α = 0 ∨ r.a = q) → (β = 0 ∨ r.b = q) → (γ = 0 ∨ r.c = q) →
      comb α β γ r.a r.b r.c = q := by
    intro q qa qb qc
    have e1 : α * r.a.1 = α * q.1 ∧ α * r.a.2 = α * q.2 := by
      rcases qa with h | h <;> simp [h]
    have e2 : β * r.b.1 = β * q.1 ∧ β * r.b.2 = β * q.2 := by
      rcases qb with h | h <;> simp [h]
    have e3 : γ * r.c.1 = γ * q.1 ∧ γ * r.c.2 = γ * q.2 := by
      rcases qc with h | h <;> simp [h]
    refine Prod.ext ?_ ?_
    · show α * r.a.1 + β * r.b.1 + γ * r.c.1 = q.1
      rw [e1.1, e2.1, e3.1]; linear_combination q.1 * hs
    · show α * r.a.2 + β * r.b.2 + γ * r.c.2 = q.2
      rw [e1.2, e2.2, e3.2]; linear_combination q.2 * hs
  have hmc : lerp (1 / 2) b c ≠ c := by
    intro h; apply hbc
    have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only [lerp] at h1 h2
    exact Prod.ext (by linarith) (by linarith)
  have hmb : lerp (1 / 2) b c ≠ b := by
    intro h; apply hbc
    have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only [lerp] at h1 h2
    exact Prod.ext (by linarith) (by linarith)
  have hbV : r.a = b ∨ r.b = b ∨ r.c = b := by
    by_contra hno
    push Not at hno
    apply hmc; rw [hmid]
    apply comb_const
    · rcases ka with h | h | h
      exacts [Or.inl h, absurd h hno.1, Or.inr h]
    · rcases kb with h | h | h
      exacts [Or.inl h, absurd h hno.2.1, Or.inr h]
    · rcases kc with h | h | h
      exacts [Or.inl h, absurd h hno.2.2, Or.inr h]
  have hcV : r.a = c ∨ r.b = c ∨ r.c = c := by
    by_contra hno
    push Not at hno
    apply hmb; rw [hmid]
    apply comb_const
    · rcases ka with h | h | h
      exacts [Or.inl h, Or.inr h, absurd h hno.1]
    · rcases kb with h | h | h
      exacts [Or.inl h, Or.inr h, absurd h hno.2.1]
    · rcases kc with h | h | h
      exacts [Or.inl h, Or.inr h, absurd h hno.2.2]
  obtain ⟨ra, rb, rc⟩ := r
  simp only at hbV hcV ⊢
  rcases hbV with h1 | h1 | h1 <;> rcases hcV with h2 | h2 | h2
  · exact absurd (h1.symm.trans h2) hbc
  · rw [← h1, ← h2]; exact ⟨rc, by simp, TrEquiv.rot (Tr.mk rc ra rb)⟩
  · rw [← h1, ← h2]; exact ⟨rb, by simp, TrEquiv.swap (Tr.mk rb ra rc)⟩
  · rw [← h1, ← h2]
    exact ⟨rc, by simp, (TrEquiv.rot2 ra rb rc).symm.trans (TrEquiv.swap23 rc rb ra)⟩
  · exact absurd (h1.symm.trans h2) hbc
  · rw [← h1, ← h2]; exact ⟨ra, by simp, TrEquiv.refl _⟩
  · rw [← h1, ← h2]; exact ⟨rb, by simp, TrEquiv.rot2 rb rc ra⟩
  · rw [← h1, ← h2]; exact ⟨ra, by simp, TrEquiv.swap23 ra rc rb⟩
  · exact absurd (h1.symm.trans h2) hbc

theorem vert_mem {r : Tr K} (hr : r.nd) {v : K × K} (hv : v ∈ [r.a, r.b, r.c]) : r.mem v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  exacts [Tr.mem_a hr, Tr.mem_b hr, Tr.mem_c hr]

/-- **Hilbert's lemma of § 20 in co-ordinates**: a decomposition of the triangle `abc` without
vertices in its interior or within the side `bc` is a series of transversal decompositions (with
the same triangles, up to the order of their vertices). -/
theorem trans_series_K : ∀ (n : ℕ) (a b c : K × K) (l : List (Tr K)), l.length = n →
    (Tr.mk a b c).nd → DecS (Tr.mk a b c).mem l →
    (∀ r ∈ l, ∀ v ∈ [r.a, r.b, r.c],
      ¬(Tr.mk a b c).int v ∧ ∀ s : K, 0 < s → s < 1 → v ≠ lerp s b c) →
    ∃ l' : List (Tr K), KTD (Tr.mk a b c) l' ∧ l'.length = l.length ∧
      ∀ r' ∈ l', ∃ r ∈ l, TrEquiv r' r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c l hlen ht hl hv
  have hD : det3 a b c ≠ 0 := ht
  have hbc : b ≠ c := Tr.nd_ne_bc ht
  have hmid : (Tr.mk a b c).mem (lerp (1 / 2) b c) := by
    rw [Tr.mem_iff_bary ht]
    refine ⟨0, 1 / 2, 1 / 2, le_rfl, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [comb, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
  obtain ⟨r, hr, hrm⟩ := (hl.2.2 _).1 hmid
  have hrnd := hl.1 r hr
  have hrsub : ∀ p, r.mem p → (Tr.mk a b c).mem p := fun p hp => (hl.2.2 p).2 ⟨r, hr, hp⟩
  obtain ⟨w, hwV, hE⟩ := piece_at_mid ht hrnd hrsub (fun v hv' => (hv r hr v hv').2) hrm
  have hwmem := hrsub w (vert_mem hrnd hwV)
  have hwint := (hv r hr w hwV).1
  have hwnd : (Tr.mk w b c).nd := hE.1.1 hrnd
  have hE' : ∀ p, r.mem p ↔ (Tr.mk w b c).mem p := hE.2.1
  have hnodup := hl.nodup
  have hlpos : 0 < l.length := List.length_pos_of_mem hr
  have hlerase : (l.erase r).length = l.length - 1 := List.length_erase_of_mem hr
  -- the barycentric co-ordinates of `w`
  have hwl := (Tr.mem_iff_l ht).1 hwmem
  have hwsum := Tr.l_sum ht w
  have hwrec := Tr.l_recon ht w
  have hla : 0 < (Tr.mk a b c).la w := by
    refine lt_of_le_of_ne hwl.1 (fun h0 => hwnd ?_)
    have : det3 b c w = 0 := by
      have h0' : det3 b c w / det3 a b c = 0 := h0.symm
      rcases div_eq_zero_iff.1 h0' with h | h
      · exact h
      · exact absurd h hD
    show det3 w b c = 0
    rw [← det3_cyc]; exact this
  have hnot : (Tr.mk a b c).lb w = 0 ∨ (Tr.mk a b c).lc w = 0 := by
    by_contra hno
    push Not at hno
    exact hwint ((Tr.int_iff_l ht).2 ⟨hla, lt_of_le_of_ne hwl.2.1 (Ne.symm hno.1),
      lt_of_le_of_ne hwl.2.2 (Ne.symm hno.2)⟩)
  obtain ⟨x, hx⟩ : ∃ x, x = (Tr.mk a b c).la w := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = (Tr.mk a b c).lb w := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = (Tr.mk a b c).lc w := ⟨_, rfl⟩
  rw [← hx, ← hy, ← hz] at hwrec hwsum
  rw [← hx] at hla
  rw [← hy, ← hz] at hnot
  rw [← hx, ← hy, ← hz] at hwl
  simp only at hwrec
  by_cases hy0 : y = 0 <;> by_cases hz0 : z = 0
  · ------------------------------------------------------------------ `w = a`: one triangle
    have hwa : w = a := by
      rw [hwrec, hy0, hz0, show x = 1 by linarith]; simp [comb]
    rw [hwa] at hE hE'
    have hall : ∀ r' ∈ l, r' = r := by
      intro r' hr'
      by_contra hne
      have hnd' := hl.1 r' hr'
      have hc := Tr.int_cen hnd'
      have hcm : r.mem r'.cen := (hE' _).2 ((hl.2.2 _).2 ⟨r', hr', Tr.mem_of_int hc⟩)
      obtain ⟨q, h1, h2⟩ := Tr.int_meet hnd' hrnd hc hcm
      exact pw_disj_of_ne hl.2.1 hr' hr hne q ⟨h1, h2⟩
    have hsub1 : l ⊆ [r] := fun r' hr' => by rw [hall r' hr']; exact List.mem_singleton_self _
    have hle := (List.Nodup.subperm hnodup hsub1).length_le
    simp only [List.length_singleton] at hle
    refine ⟨[Tr.mk a b c], KTD.single _, by simp only [List.length_singleton]; omega, ?_⟩
    intro r' hr'
    rw [List.mem_singleton] at hr'
    subst hr'
    exact ⟨r, hr, hE.symm⟩
  · ------------------------------------------------------------------ `w` within `ca`
    have hzp : 0 < z := lt_of_le_of_ne hwl.2.2 (Ne.symm hz0)
    have hx1 : x < 1 := by linarith
    have hw : w = lerp x c a := by
      rw [hwrec, hy0, show z = 1 - x by linarith]
      simp only [comb, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
    rw [hw] at hE hE' hwnd
    clear hwrec hwsum hx hy hz hnot hwl hwV hwmem hwint hw
    clear w
    set w := lerp x c a with hwdef
    have nq : (Tr.mk a b w).nd := ne_of_eq (k := 1 - x)
      (by simp only [hwdef, Tr.D, det3, lerp]; ring) (by linarith) hD
    -- the transversal `bw`
    have sp := split (t := Tr.mk b c a) ((Tr.nd_rot (t := Tr.mk a b c)).2 ht) hla hx1
    have hsplit : ∀ p, (Tr.mk a b c).mem p ↔ (Tr.mk w b c).mem p ∨ (Tr.mk a b w).mem p := by
      intro p
      have := sp.2.2 p
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left] at this
      rw [show (Tr.mk a b c).mem p ↔ (Tr.mk b c a).mem p from (Tr.mem_rot (t := Tr.mk a b c)).symm,
        this]
      exact or_congr ((TrEquiv.rot (Tr.mk w b c)).2.1 p) ((TrEquiv.rot (Tr.mk a b w)).2.1 p)
    have hdec : DecS (Tr.mk a b w).mem (l.erase r) := by
      refine decS_erase hl hr nq (κ := det3 a b c) (u := w) (v := b)
        (fun p hp => ?_) (fun p hp => (hsplit p).2 (Or.inr hp)) (fun p hp => ?_)
        (fun p hp => ?_) (fun p hp => ?_) (fun p hp hnq => ?_)
      · rcases (hsplit p).1 hp with h | h
        · exact Or.inl ((hE' p).2 h)
        · exact Or.inr h
      · exact side_nonneg hwnd
          (nonneg_of_eq (k := 0) (by simp only [det3]; ring) le_rfl)
          (nonneg_of_eq (k := 0) (by simp only [det3]; ring) le_rfl)
          (nonneg_of_eq (k := x) (by simp only [hwdef, det3, lerp]; ring) hla.le) ((hE' p).1 hp)
      · exact side_nonpos nq
          (nonpos_of_eq (k := x - 1) (by simp only [hwdef, det3, lerp]; ring) (by linarith))
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl)
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl) hp
      · exact side_neg_int nq
          (neg_of_eq (k := x - 1) (by simp only [hwdef, det3, lerp]; ring) (by linarith) hD)
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl)
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl) hp
      · rcases (hsplit p).1 hp with h | h
        · obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.mem_iff_bary hwnd).1 h
          have hγ : 0 < γ := by
            refine lt_of_le_of_ne h3 (fun hγ0 => hnq ?_)
            rw [Tr.mem_iff_bary nq]
            refine ⟨0, β, α, le_rfl, h2, h1, by rw [← hγ0] at hs; linarith, ?_⟩
            rw [← hγ0]
            simp only [comb]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
          rw [det3_comb _ _ hs]
          have e1 : det3 w b w = 0 := by simp only [det3]; ring
          have e2 : det3 w b b = 0 := by simp only [det3]; ring
          have e3 : det3 w b c = x * det3 a b c := by simp only [hwdef, det3, lerp]; ring
          rw [e1, e2, e3]
          have := pos_of_eq (D := det3 a b c) (x := γ * (x * det3 a b c)) (k := γ * x)
            (by ring) (mul_pos hγ hla) hD
          linarith [show det3 a b c * (α * 0 + β * 0 + γ * (x * det3 a b c)) =
            det3 a b c * (γ * (x * det3 a b c)) by ring]
        · exact absurd h hnq
    have hv' : ∀ r' ∈ l.erase r, ∀ v ∈ [r'.a, r'.b, r'.c],
        ¬(Tr.mk a b w).int v ∧ ∀ s : K, 0 < s → s < 1 → v ≠ lerp s b w := by
      intro r' hr' v hvv
      have hr'l := (List.erase_sublist).subset hr'
      refine ⟨fun hi => (hv r' hr'l v hvv).1
        (Tr.int_of_sub nq ht (fun p hp => (hsplit p).2 (Or.inr hp)) hi), fun s hs0 hs1 he => ?_⟩
      apply (hv r' hr'l v hvv).1
      rw [he]
      refine ⟨pos_of_eq (k := s * x) (by simp only [hwdef, Tr.D, det3, lerp]; ring)
          (mul_pos hs0 hla) hD,
        pos_of_eq (k := 1 - s) (by simp only [hwdef, Tr.D, det3, lerp]; ring) (by linarith) hD,
        pos_of_eq (k := s * (1 - x)) (by simp only [hwdef, Tr.D, det3, lerp]; ring)
          (mul_pos hs0 (by linarith)) hD⟩
    obtain ⟨l'', k1, k2, k3⟩ := ih (l.erase r).length (by omega) a b w (l.erase r) rfl nq hdec hv'
    refine ⟨[Tr.mk b c w] ++ l'', ?_, ?_, ?_⟩
    · have := KTD.split (a := b) (b := c) (c := a) (s := x) (Tr.nd_ne_ca ht) hla hx1
        (KTD.single (Tr.mk b c w)) (KTD.rot k1)
      exact KTD.rot (KTD.rot this)
    · simp only [List.length_append, List.length_singleton]; omega
    · intro r' hr'
      rcases List.mem_append.1 hr' with h | h
      · rw [List.mem_singleton] at h; subst h
        exact ⟨r, hr, (TrEquiv.rot (Tr.mk w b c)).trans hE.symm⟩
      · obtain ⟨r0, hr0, e⟩ := k3 r' h
        exact ⟨r0, (List.erase_sublist).subset hr0, e⟩
  · ------------------------------------------------------------------ `w` within `ab`
    have hyp : 0 < y := lt_of_le_of_ne hwl.2.1 (Ne.symm hy0)
    have hy1 : y < 1 := by linarith
    have hw : w = lerp y a b := by
      rw [hwrec, hz0, show x = 1 - y by linarith]
      simp only [comb, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
    rw [hw] at hE hE' hwnd
    clear hwrec hwsum hx hy hz hnot hwl hwV hwmem hwint hw
    clear w
    set w := lerp y a b with hwdef
    have nq : (Tr.mk a w c).nd := ne_of_eq (k := y)
      (by simp only [hwdef, Tr.D, det3, lerp]; ring) hyp.ne' hD
    -- the transversal `cw`
    have ht2 : (Tr.mk c a b).nd := (Tr.nd_rot (t := Tr.mk b c a)).2 ((Tr.nd_rot (t := Tr.mk a b c)).2 ht)
    have sp := split (t := Tr.mk c a b) ht2 hyp hy1
    have hsplit : ∀ p, (Tr.mk a b c).mem p ↔ (Tr.mk w b c).mem p ∨ (Tr.mk a w c).mem p := by
      intro p
      rw [← (TrEquiv.rot2 a b c).2.1 p]
      have := sp.2.2 p
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left] at this
      rw [this]
      exact or_comm.trans (or_congr ((TrEquiv.rot2 w b c).2.1 p) ((TrEquiv.rot2 a w c).2.1 p))
    have hdec : DecS (Tr.mk a w c).mem (l.erase r) := by
      refine decS_erase hl hr nq (κ := det3 a b c) (u := c) (v := w)
        (fun p hp => ?_) (fun p hp => (hsplit p).2 (Or.inr hp)) (fun p hp => ?_)
        (fun p hp => ?_) (fun p hp => ?_) (fun p hp hnq => ?_)
      · rcases (hsplit p).1 hp with h | h
        · exact Or.inl ((hE' p).2 h)
        · exact Or.inr h
      · exact side_nonneg hwnd
          (nonneg_of_eq (k := 0) (by simp only [det3]; ring) le_rfl)
          (nonneg_of_eq (k := 1 - y) (by simp only [hwdef, det3, lerp]; ring) (by linarith))
          (nonneg_of_eq (k := 0) (by simp only [det3]; ring) le_rfl) ((hE' p).1 hp)
      · exact side_nonpos nq
          (nonpos_of_eq (k := -y) (by simp only [hwdef, det3, lerp]; ring) (by linarith))
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl)
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl) hp
      · exact side_neg_int nq
          (neg_of_eq (k := -y) (by simp only [hwdef, det3, lerp]; ring) (by linarith) hD)
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl)
          (nonpos_of_eq (k := 0) (by simp only [det3]; ring) le_rfl) hp
      · rcases (hsplit p).1 hp with h | h
        · obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.mem_iff_bary hwnd).1 h
          have hβ : 0 < β := by
            refine lt_of_le_of_ne h2 (fun hβ0 => hnq ?_)
            rw [Tr.mem_iff_bary nq]
            refine ⟨0, α, γ, le_rfl, h1, h3, by rw [← hβ0] at hs; linarith, ?_⟩
            rw [← hβ0]
            simp only [comb]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
          rw [det3_comb _ _ hs]
          have e1 : det3 c w w = 0 := by simp only [det3]; ring
          have e2 : det3 c w b = (1 - y) * det3 a b c := by simp only [hwdef, det3, lerp]; ring
          have e3 : det3 c w c = 0 := by simp only [det3]; ring
          rw [e1, e2, e3]
          have := pos_of_eq (D := det3 a b c) (x := β * ((1 - y) * det3 a b c)) (k := β * (1 - y))
            (by ring) (mul_pos hβ (by linarith)) hD
          linarith [show det3 a b c * (α * 0 + β * ((1 - y) * det3 a b c) + γ * 0) =
            det3 a b c * (β * ((1 - y) * det3 a b c)) by ring]
        · exact absurd h hnq
    have hv' : ∀ r' ∈ l.erase r, ∀ v ∈ [r'.a, r'.b, r'.c],
        ¬(Tr.mk a w c).int v ∧ ∀ s : K, 0 < s → s < 1 → v ≠ lerp s w c := by
      intro r' hr' v hvv
      have hr'l := (List.erase_sublist).subset hr'
      refine ⟨fun hi => (hv r' hr'l v hvv).1
        (Tr.int_of_sub nq ht (fun p hp => (hsplit p).2 (Or.inr hp)) hi), fun s hs0 hs1 he => ?_⟩
      apply (hv r' hr'l v hvv).1
      rw [he]
      refine ⟨pos_of_eq (k := (1 - s) * (1 - y)) (by simp only [hwdef, Tr.D, det3, lerp]; ring)
          (mul_pos (by linarith) (by linarith)) hD,
        pos_of_eq (k := (1 - s) * y) (by simp only [hwdef, Tr.D, det3, lerp]; ring)
          (mul_pos (by linarith) hyp) hD,
        pos_of_eq (k := s) (by simp only [hwdef, Tr.D, det3, lerp]; ring) hs0 hD⟩
    obtain ⟨l'', k1, k2, k3⟩ := ih (l.erase r).length (by omega) a w c (l.erase r) rfl nq hdec hv'
    refine ⟨l'' ++ [Tr.mk c w b], ?_, ?_, ?_⟩
    · have := KTD.split (a := c) (b := a) (c := b) (s := y) (Tr.nd_ne_ab ht) hyp hy1
        (KTD.rot (KTD.rot k1)) (KTD.single (Tr.mk c w b))
      exact KTD.rot this
    · simp only [List.length_append, List.length_singleton]; omega
    · intro r' hr'
      rcases List.mem_append.1 hr' with h | h
      · obtain ⟨r0, hr0, e⟩ := k3 r' h
        exact ⟨r0, (List.erase_sublist).subset hr0, e⟩
      · rw [List.mem_singleton] at h; subst h
        exact ⟨r, hr, (TrEquiv.rot2 w b c).trans hE.symm⟩
  · ------------------------------------------------------------------ impossible
    rcases hnot with h | h
    · exact absurd h hy0
    · exact absurd h hz0

end Areas

end HilbertFoundations
