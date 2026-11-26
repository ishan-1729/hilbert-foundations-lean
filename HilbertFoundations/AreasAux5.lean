import HilbertFoundations.AreasAux4

/-!
# Helper module for `Areas.lean`: explicit decompositions in the co-ordinate plane

This module contains no unit of Hilbert's text. Over a linearly ordered field `K`:

* separation of triangles by a line (`sep`), equivalent triangles (`TrEquiv`: the same points,
  interior points and non-degeneracy; permutations of the vertices), `DecS.replace`;
* the two diagonals of a convex quadrilateral (`diag_swap`);
* **Theorem 26** in co-ordinates (`th26_K`): the triangle `abc` and the parallelogram `abfd`
  (`d`, `e` the midpoints of `ca`, `bc`, `f = 2e - d`) are of equal area;
* **Euclid's parallelograms on the same base and between the same parallels** (`euclid_K`): they
  are of equal content (Fig. 30);
* the **shear** of a triangle (`shear_K`): moving the vertex `c` parallel to the side `ab` keeps
  the content.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Separation and equivalent triangles -/

/-- Triangles on different sides of a line have disjoint interiors. -/
theorem sep {t t' : Tr K} (ht : t.nd) (ht' : t'.nd) {u v : K × K} (huv : u ≠ v) {κ : K}
    (hκ : κ ≠ 0) (h1 : 0 ≤ κ * det3 u v t.a) (h2 : 0 ≤ κ * det3 u v t.b)
    (h3 : 0 ≤ κ * det3 u v t.c) (h1' : κ * det3 u v t'.a ≤ 0) (h2' : κ * det3 u v t'.b ≤ 0)
    (h3' : κ * det3 u v t'.c ≤ 0) : ∀ p, ¬(t.int p ∧ t'.int p) := by
  -- the value at an interior point has the sign of the values at the vertices, strictly
  have key : ∀ r : Tr K, r.nd → ∀ σ : K, σ ≠ 0 → 0 ≤ σ * det3 u v r.a → 0 ≤ σ * det3 u v r.b →
      0 ≤ σ * det3 u v r.c → ∀ p, r.int p → 0 < σ * det3 u v p := by
    intro r hr σ hσ a1 a2 a3 p hp
    obtain ⟨α, β, γ, b1, b2, b3, hs, rfl⟩ := (Tr.int_iff_bary hr).1 hp
    rw [det3_comb _ _ hs]
    by_contra hc
    push Not at hc
    have m1 := mul_nonneg b1.le a1
    have m2 := mul_nonneg b2.le a2
    have m3 := mul_nonneg b3.le a3
    have hsum : α * (σ * det3 u v r.a) + β * (σ * det3 u v r.b) + γ * (σ * det3 u v r.c) ≤ 0 := by
      linarith [show σ * (α * det3 u v r.a + β * det3 u v r.b + γ * det3 u v r.c) =
        α * (σ * det3 u v r.a) + β * (σ * det3 u v r.b) + γ * (σ * det3 u v r.c) by ring]
    have z1 : α * (σ * det3 u v r.a) = 0 := by linarith
    have z2 : β * (σ * det3 u v r.b) = 0 := by linarith
    have z3 : γ * (σ * det3 u v r.c) = 0 := by linarith
    have e1 : σ * det3 u v r.a = 0 := (mul_eq_zero.1 z1).resolve_left b1.ne'
    have e2 : σ * det3 u v r.b = 0 := (mul_eq_zero.1 z2).resolve_left b2.ne'
    have e3 : σ * det3 u v r.c = 0 := (mul_eq_zero.1 z3).resolve_left b3.ne'
    exact hr (det3_eq_zero_of_line huv ((mul_eq_zero.1 e1).resolve_left hσ)
      ((mul_eq_zero.1 e2).resolve_left hσ) ((mul_eq_zero.1 e3).resolve_left hσ))
  intro p ⟨hp, hp'⟩
  have a := key t ht κ hκ h1 h2 h3 p hp
  have b := key t' ht' (-κ) (neg_ne_zero.2 hκ) (by linarith) (by linarith) (by linarith) p hp'
  linarith

/-- Two triangles with the same points, interior points and non-degeneracy. -/
def TrEquiv (r r' : Tr K) : Prop :=
  (r.nd ↔ r'.nd) ∧ (∀ p, r.mem p ↔ r'.mem p) ∧ (∀ p, r.int p ↔ r'.int p)

theorem TrEquiv.rot (r : Tr K) : TrEquiv r.rot r :=
  ⟨Tr.nd_rot, fun _ => Tr.mem_rot, fun _ => Tr.int_rot⟩

theorem TrEquiv.swap (r : Tr K) : TrEquiv r.swap r :=
  ⟨Tr.nd_swap, fun _ => Tr.mem_swap, fun _ => Tr.int_swap⟩

theorem TrEquiv.refl (r : Tr K) : TrEquiv r r := ⟨Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem TrEquiv.symm {r r' : Tr K} (h : TrEquiv r r') : TrEquiv r' r :=
  ⟨h.1.symm, fun p => (h.2.1 p).symm, fun p => (h.2.2 p).symm⟩

theorem TrEquiv.trans {r r' r'' : Tr K} (h : TrEquiv r r') (h' : TrEquiv r' r'') :
    TrEquiv r r'' :=
  ⟨h.1.trans h'.1, fun p => (h.2.1 p).trans (h'.2.1 p), fun p => (h.2.2 p).trans (h'.2.2 p)⟩

theorem TrEquiv.of_eq {r r' : Tr K} (h : r = r') : TrEquiv r r' := h ▸ TrEquiv.refl r

/-- `⟨c, a, b⟩` is `⟨a, b, c⟩`. -/
theorem TrEquiv.rot2 (a b c : K × K) : TrEquiv (Tr.mk c a b) (Tr.mk a b c) :=
  (TrEquiv.rot (Tr.mk b c a)).trans (TrEquiv.rot (Tr.mk a b c))

/-- `⟨a, c, b⟩` is `⟨a, b, c⟩`. -/
theorem TrEquiv.swap23 (a b c : K × K) : TrEquiv (Tr.mk a c b) (Tr.mk a b c) :=
  (TrEquiv.swap (Tr.mk c a b)).trans (TrEquiv.rot2 a b c)

theorem forall₂_mem_right {α β : Type*} {E : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ E l l' → ∀ {s' : β}, s' ∈ l' → ∃ s ∈ l, E s s'
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hab hrest, s', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨s, hs, e⟩ := forall₂_mem_right hrest h
      exact ⟨s, List.mem_cons_of_mem _ hs, e⟩

theorem forall₂_mem_left {α β : Type*} {E : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ E l l' → ∀ {s : α}, s ∈ l → ∃ s' ∈ l', E s s'
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hab hrest, s, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨s', hs, e⟩ := forall₂_mem_left hrest h
      exact ⟨s', List.mem_cons_of_mem _ hs, e⟩

/-- Replacing the triangles of a decomposition by equivalent triangles. -/
theorem DecS.replace {S : K × K → Prop} {l l' : List (Tr K)} (h : DecS S l)
    (hr : List.Forall₂ TrEquiv l l') : DecS S l' := by
  refine ⟨fun r' hr' => ?_, ?_, fun p => ?_⟩
  · obtain ⟨r, hr, e⟩ := forall₂_mem_right hr hr'
    exact e.1.1 (h.1 r hr)
  · have key : ∀ {l l' : List (Tr K)}, List.Forall₂ TrEquiv l l' →
        l.Pairwise (fun r s => ∀ p, ¬(r.int p ∧ s.int p)) →
        l'.Pairwise (fun r s => ∀ p, ¬(r.int p ∧ s.int p)) := by
      intro l l' hr
      induction hr with
      | nil => intro _; exact List.Pairwise.nil
      | @cons r r' l l' hab hrest ih =>
        intro hp
        rw [List.pairwise_cons] at hp ⊢
        refine ⟨fun s' hs' q hq => ?_, ih hp.2⟩
        obtain ⟨s, hs, e⟩ := forall₂_mem_right hrest hs'
        exact hp.1 s hs q ⟨(hab.2.2 q).2 hq.1, (e.2.2 q).2 hq.2⟩
    exact key hr h.2.1
  · rw [h.2.2 p]
    constructor
    · rintro ⟨r, hr', hp⟩
      obtain ⟨r', hr'', e⟩ := forall₂_mem_left hr hr'
      exact ⟨r', hr'', (e.2.1 p).1 hp⟩
    · rintro ⟨r', hr', hp⟩
      obtain ⟨r, hr'', e⟩ := forall₂_mem_right hr hr'
      exact ⟨r, hr'', (e.2.1 p).2 hp⟩

/-! ### Small algebraic helpers -/

theorem nonneg_of_eq {D x k : K} (h : x = k * D) (hk : 0 ≤ k) : 0 ≤ D * x := by
  rw [h]; nlinarith [mul_self_nonneg D]

theorem nonpos_of_eq {D x k : K} (h : x = k * D) (hk : k ≤ 0) : D * x ≤ 0 := by
  rw [h]; nlinarith [mul_self_nonneg D]

theorem ne_of_eq {D x k : K} (h : x = k * D) (hk : k ≠ 0) (hD : D ≠ 0) : x ≠ 0 := by
  rw [h]; exact mul_ne_zero hk hD

theorem split_mem {t : Tr K} (ht : t.nd) {s : K} (hs0 : 0 < s) (hs1 : s < 1) (p : K × K) :
    t.mem p ↔ (Tr.mk t.a t.b (lerp s t.b t.c)).mem p ∨ (Tr.mk t.a (lerp s t.b t.c) t.c).mem p := by
  rw [(split ht hs0 hs1).2.2 p]
  simp

/-- **The two diagonals of a convex quadrilateral** `abcd` (the diagonals `ac` and `bd` crossing at
a point within both) give the same region. -/
theorem diag_swap {a b c d : K × K} {s r : K} (hs0 : 0 < s) (hs1 : s < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (ho : lerp s a c = lerp r b d) (h1 : (Tr.mk b a c).nd) (h2 : (Tr.mk d a c).nd)
    (h3 : (Tr.mk a b d).nd) (h4 : (Tr.mk c b d).nd) (p : K × K) :
    ((Tr.mk a b c).mem p ∨ (Tr.mk a c d).mem p) ↔ ((Tr.mk a b d).mem p ∨ (Tr.mk b c d).mem p) := by
  have e1 : (Tr.mk a b c).mem p ↔
      (Tr.mk b a (lerp s a c)).mem p ∨ (Tr.mk b (lerp s a c) c).mem p :=
    (Tr.mem_swap (t := Tr.mk a b c)).symm.trans (split_mem h1 hs0 hs1 p)
  have e2 : (Tr.mk a c d).mem p ↔
      (Tr.mk d a (lerp s a c)).mem p ∨ (Tr.mk d (lerp s a c) c).mem p :=
    ((TrEquiv.rot2 a c d).2.1 p).symm.trans (split_mem h2 hs0 hs1 p)
  have e3 : (Tr.mk a b d).mem p ↔
      (Tr.mk a b (lerp s a c)).mem p ∨ (Tr.mk a (lerp s a c) d).mem p := by
    rw [ho]; exact split_mem h3 hr0 hr1 p
  have e4 : (Tr.mk b c d).mem p ↔
      (Tr.mk c b (lerp s a c)).mem p ∨ (Tr.mk c (lerp s a c) d).mem p := by
    rw [ho]; exact (Tr.mem_swap (t := Tr.mk b c d)).symm.trans (split_mem h4 hr0 hr1 p)
  set o := lerp s a c
  have f1 : (Tr.mk b a o).mem p ↔ (Tr.mk a b o).mem p := (TrEquiv.swap (Tr.mk a b o)).2.1 p
  have f2 : (Tr.mk b o c).mem p ↔ (Tr.mk c b o).mem p := (TrEquiv.rot (Tr.mk c b o)).2.1 p
  have f3 : (Tr.mk d a o).mem p ↔ (Tr.mk a o d).mem p := (TrEquiv.rot2 a o d).2.1 p
  have f4 : (Tr.mk d o c).mem p ↔ (Tr.mk c o d).mem p :=
    ((TrEquiv.swap (Tr.mk o d c)).trans (TrEquiv.rot (Tr.mk c o d))).2.1 p
  rw [e1, e2, e3, e4, f1, f2, f3, f4]
  exact or_or_or_comm

/-! ### Theorem 26 in co-ordinates -/

/-- The point `2e - d`. -/
def refl2 (e d : K × K) : K × K := (2 * e.1 - d.1, 2 * e.2 - d.2)

/-- **Theorem 26 in co-ordinates**: with `d`, `e` the midpoints of `ca`, `bc` and `f = 2e - d`,
the triangle `abc` is decomposed into `abe`, `ecd`, `eda` and the parallelogram `abfd` (the
triangles `abf` and `afd`) into `abe`, `ebf`, `eda`, and `ecd ≡ ebf`. -/
theorem th26_K {a b c : K × K} (hD : det3 a b c ≠ 0) :
    DecS (Tr.mk a b c).mem [Tr.mk a b (lerp (1 / 2) b c),
        Tr.mk (lerp (1 / 2) b c) c (lerp (1 / 2) c a),
        Tr.mk (lerp (1 / 2) b c) (lerp (1 / 2) c a) a] ∧
      DecS (fun p => (Tr.mk a b (refl2 (lerp (1 / 2) b c) (lerp (1 / 2) c a))).mem p ∨
        (Tr.mk a (refl2 (lerp (1 / 2) b c) (lerp (1 / 2) c a)) (lerp (1 / 2) c a)).mem p)
        [Tr.mk a b (lerp (1 / 2) b c),
          Tr.mk (lerp (1 / 2) b c) b (refl2 (lerp (1 / 2) b c) (lerp (1 / 2) c a)),
          Tr.mk (lerp (1 / 2) b c) (lerp (1 / 2) c a) a] ∧
      List.Forall₂ KCong
        [Tr.mk a b (lerp (1 / 2) b c),
          Tr.mk (lerp (1 / 2) b c) c (lerp (1 / 2) c a),
          Tr.mk (lerp (1 / 2) b c) (lerp (1 / 2) c a) a]
        [Tr.mk a b (lerp (1 / 2) b c),
          Tr.mk (lerp (1 / 2) b c) b (refl2 (lerp (1 / 2) b c) (lerp (1 / 2) c a)),
          Tr.mk (lerp (1 / 2) b c) (lerp (1 / 2) c a) a] := by
  set e := lerp (1 / 2) b c with he
  set d := lerp (1 / 2) c a with hd
  set f := refl2 e d with hf
  set D := det3 a b c with hDdef
  have ht : (Tr.mk a b c).nd := hD
  -- the triangle
  have sp1 := split ht (s := 1 / 2) (by norm_num) (by norm_num)
  have n2 : (Tr.mk a e c).nd := sp1.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have sp2 := split (t := Tr.mk e c a) (Tr.nd_rot.2 n2) (s := 1 / 2) (by norm_num) (by norm_num)
  have sp2' : DecS (Tr.mk a e c).mem [Tr.mk e c d, Tr.mk e d a] :=
    sp2.congr (fun p => Tr.mem_rot (t := Tr.mk a e c))
  have dT : DecS (Tr.mk a b c).mem [Tr.mk a b e, Tr.mk e c d, Tr.mk e d a] := sp1.cons_refine sp2'
  -- congruence of `ecd` and `ebf` (the half-turn about `e`)
  have cg : KCong (Tr.mk e c d) (Tr.mk e b f) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [sqd, he, hd, hf, refl2, lerp] <;> ring
  have nd1 : (Tr.mk a b e).nd := dT.1 _ (by simp)
  have nd2 : (Tr.mk e b f).nd := cg.nd (dT.1 _ (by simp))
  have nd3 : (Tr.mk e d a).nd := dT.1 _ (by simp)
  -- the parallelogram
  have hfe : lerp (1 / 2) f d = e := by
    simp only [hf, he, hd, refl2, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
  have nAFD : (Tr.mk a f d).nd := by
    show det3 a f d ≠ 0
    exact ne_of_eq (k := 1 / 2) (by simp only [hf, he, hd, hDdef, refl2, lerp, det3]; ring)
      (by norm_num) hD
  have spP : ∀ p, (Tr.mk a f d).mem p ↔ (Tr.mk a f e).mem p ∨ (Tr.mk a e d).mem p := by
    intro p
    have := split_mem nAFD (s := 1 / 2) (by norm_num) (by norm_num) p
    simp only at this
    rw [hfe] at this
    exact this
  have ds : ∀ p, ((Tr.mk a b f).mem p ∨ (Tr.mk a f e).mem p) ↔
      ((Tr.mk a b e).mem p ∨ (Tr.mk b f e).mem p) := by
    intro p
    refine diag_swap (s := 2 / 3) (r := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ?_ ?_ ?_ ?_ ?_ p
    · simp only [hf, he, hd, refl2, lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
    · show det3 b a f ≠ 0
      exact ne_of_eq (k := -1 / 2) (by simp only [hf, he, hd, hDdef, refl2, lerp, det3]; ring)
        (by norm_num) hD
    · show det3 e a f ≠ 0
      exact ne_of_eq (k := 1 / 4) (by simp only [hf, he, hd, hDdef, refl2, lerp, det3]; ring)
        (by norm_num) hD
    · exact nd1
    · show det3 f b e ≠ 0
      exact ne_of_eq (k := -1 / 4) (by simp only [hf, he, hd, hDdef, refl2, lerp, det3]; ring)
        (by norm_num) hD
  have hm : (lerp (1 / 2) a b : K × K) ≠ e := by
    intro h
    apply hD
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [he, lerp] at h1 h2
    rw [hDdef]; unfold det3
    have e1 : c.1 = a.1 := by linarith
    have e2 : c.2 = a.2 := by linarith
    rw [e1, e2]; ring
  have hbe : b ≠ e := Tr.nd_ne_bc nd1
  have hae : a ≠ e := fun h => Tr.nd_ne_ca nd1 h.symm
  refine ⟨dT, ⟨?_, ?_, fun p => ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact nd1
    · exact nd2
    · exact nd3
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sep nd1 nd2 hbe (κ := D) hD
          (nonneg_of_eq (k := 1 / 2) (by simp only [he, hDdef, lerp, det3]; ring) (by norm_num))
          (nonneg_of_eq (k := 0) (by simp only [he, hDdef, lerp, det3]; ring) le_rfl)
          (nonneg_of_eq (k := 0) (by simp only [he, hDdef, lerp, det3]; ring) le_rfl)
          (nonpos_of_eq (k := 0) (by simp only [he, hDdef, lerp, det3]; ring) le_rfl)
          (nonpos_of_eq (k := 0) (by simp only [he, hDdef, lerp, det3]; ring) le_rfl)
          (nonpos_of_eq (k := -1 / 4) (by simp only [hf, he, hd, hDdef, refl2, lerp, det3]; ring)
            (by norm_num))
      · exact sep nd1 nd3 hae (κ := -D) (neg_ne_zero.2 hD)
          (by have := nonpos_of_eq (D := D) (x := det3 a e a) (k := 0)
                (by simp only [he, hDdef, lerp, det3]; ring) le_rfl; linarith)
          (by have := nonpos_of_eq (D := D) (x := det3 a e b) (k := -1 / 2)
                (by simp only [he, hDdef, lerp, det3]; ring) (by norm_num); linarith)
          (by have := nonpos_of_eq (D := D) (x := det3 a e e) (k := 0)
                (by simp only [he, hDdef, lerp, det3]; ring) le_rfl; linarith)
          (by have := nonneg_of_eq (D := D) (x := det3 a e e) (k := 0)
                (by simp only [he, hDdef, lerp, det3]; ring) le_rfl; linarith)
          (by have := nonneg_of_eq (D := D) (x := det3 a e d) (k := 1 / 4)
                (by simp only [he, hd, hDdef, lerp, det3]; ring) (by norm_num); linarith)
          (by have := nonneg_of_eq (D := D) (x := det3 a e a) (k := 0)
                (by simp only [he, hDdef, lerp, det3]; ring) le_rfl; linarith)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact sep nd2 nd3 (Ne.symm hm) (κ := D) hD
        (nonneg_of_eq (k := 0) (by simp only [he, hDdef, lerp, det3]; ring) le_rfl)
        (nonneg_of_eq (k := 1 / 4) (by simp only [he, hDdef, lerp, det3]; ring) (by norm_num))
        (nonneg_of_eq (k := 1 / 4) (by simp only [hf, he, hd, hDdef, refl2, lerp, det3]; ring)
          (by norm_num))
        (nonpos_of_eq (k := 0) (by simp only [he, hDdef, lerp, det3]; ring) le_rfl)
        (nonpos_of_eq (k := -1 / 4) (by simp only [he, hd, hDdef, lerp, det3]; ring)
          (by norm_num))
        (nonpos_of_eq (k := -1 / 4) (by simp only [he, hDdef, lerp, det3]; ring) (by norm_num))
    · intro r hr; exact absurd hr List.not_mem_nil
  · simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [spP p]
    have r1 : (Tr.mk b f e).mem p ↔ (Tr.mk e b f).mem p := (TrEquiv.rot (Tr.mk e b f)).2.1 p
    have r2 : (Tr.mk e d a).mem p ↔ (Tr.mk a e d).mem p := (TrEquiv.rot (Tr.mk a e d)).2.1 p
    have := ds p
    rw [r1] at this
    rw [r2]
    exact or_assoc.symm.trans ((or_congr_left this).trans or_assoc)
  · exact List.Forall₂.cons (KCong.refl _) (List.Forall₂.cons cg
      (List.Forall₂.cons (KCong.refl _) List.Forall₂.nil))

/-! ### Equal content: elementary properties -/

theorem KEqContent.symm {S T : K × K → Prop} (h : KEqContent S T) : KEqContent T S := by
  obtain ⟨S', T', U, V, p1, p2, e, c1, c2, e'⟩ := h
  exact ⟨T', S', V, U, p2, p1, e.symm, c2, c1, e'.symm⟩

theorem KPoly.ne_nil {S : K × K → Prop} (h : KPoly S) {l : List (Tr K)} (hl : DecS S l) :
    l ≠ [] := by
  rintro rfl
  obtain ⟨m, hm, dm⟩ := h
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil m hm
  have := (hl.2.2 r.a).1 (dm.sub hr (Tr.mem_a (dm.1 r hr)))
  simp at this

/-- **Polygons of equal area are of equal content.** -/
theorem KEqArea.toContent {S T : K × K → Prop} (h : KEqArea S T) (hS : KPoly S) :
    KEqContent S T := by
  obtain ⟨l, m, hl, hm, hc⟩ := h
  have hne := hS.ne_nil hl
  obtain ⟨φ, hφ⟩ := far_obst hl (l ++ m) (fun r hr => by
    rcases List.mem_append.1 hr with h | h
    · exact hl.1 r h
    · exact hm.1 r h)
  have dA := hl.mapI φ
  have nA : l.map (fun r => r.mapI φ) ≠ [] := by simp [hne]
  have hSA := disj_of_obst hl (fun r hr => List.mem_append_left _ hr) hφ
  have hTA := disj_of_obst hm (fun r hr => List.mem_append_right _ hr) hφ
  have hmne : m ≠ [] := by
    intro e; subst e; cases hc; exact hne rfl
  have cU : KComposed (fun p => S p ∨ imgI φ S p) S (imgI φ S) :=
    ⟨l, _, hne, nA, hl, dA, hl.append_disjoint dA hSA⟩
  have cV : KComposed (fun p => T p ∨ imgI φ S p) T (imgI φ S) :=
    ⟨m, _, hmne, nA, hm, dA, hm.append_disjoint dA hTA⟩
  exact ⟨_, _, _, _, ⟨_, nA, dA⟩, ⟨_, nA, dA⟩, KEqArea.refl dA, cU, cV,
    KEqArea.combine cU cV ⟨l, m, hl, hm, hc⟩ (KEqArea.refl dA)⟩

theorem KEqContent.refl {S : K × K → Prop} (hS : KPoly S) : KEqContent S S := by
  have h := hS
  obtain ⟨l, -, hl⟩ := h
  exact (KEqArea.refl hl).toContent hS

theorem KEqContent.congr {S S' T T' : K × K → Prop} (h : KEqContent S T) (hS : ∀ p, S p ↔ S' p)
    (hT : ∀ p, T p ↔ T' p) : KEqContent S' T' := by
  obtain ⟨A, B, U, V, p1, p2, e, c1, c2, e'⟩ := h
  refine ⟨A, B, U, V, p1, p2, e, ?_, ?_, e'⟩
  · obtain ⟨l1, l2, n1, n2, h1, h2, hU⟩ := c1
    exact ⟨l1, l2, n1, n2, h1.congr hS, h2, hU⟩
  · obtain ⟨l1, l2, n1, n2, h1, h2, hU⟩ := c2
    exact ⟨l1, l2, n1, n2, h1.congr hT, h2, hU⟩

/-- A triangle is a polygon. -/
theorem KPoly.tri {t : Tr K} (ht : t.nd) : KPoly t.mem := ⟨[t], by simp, DecS.single ht⟩

/-! ### Euclid's parallelograms on the same base and between the same parallels -/

/-- The fourth vertex `d + (b - a)` of the parallelogram with the side `ab` and the vertex `d`. -/
def par4 (a b d : K × K) : K × K := (d.1 + b.1 - a.1, d.2 + b.2 - a.2)

/-- The region of the parallelogram `abcd` (the triangles `abc`, `acd`). -/
def parReg (a b c d : K × K) : K × K → Prop := fun p => (Tr.mk a b c).mem p ∨ (Tr.mk a c d).mem p

/-- The point `d + μ (b - a)`. -/
def shift (d a b : K × K) (μ : K) : K × K := (d.1 + μ * (b.1 - a.1), d.2 + μ * (b.2 - a.2))

theorem sep' {t t' : Tr K} (ht : t.nd) (ht' : t'.nd) {u v : K × K} (huv : u ≠ v) {κ : K}
    (hκ : κ ≠ 0) (h1 : κ * det3 u v t.a ≤ 0) (h2 : κ * det3 u v t.b ≤ 0)
    (h3 : κ * det3 u v t.c ≤ 0) (h1' : 0 ≤ κ * det3 u v t'.a) (h2' : 0 ≤ κ * det3 u v t'.b)
    (h3' : 0 ≤ κ * det3 u v t'.c) : ∀ p, ¬(t.int p ∧ t'.int p) := fun p hp =>
  sep ht' ht huv hκ h1' h2' h3' h1 h2 h3 p ⟨hp.2, hp.1⟩

theorem decS_parReg {a b d : K × K} (hD : det3 a b d ≠ 0) :
    DecS (parReg a b (par4 a b d) d) [Tr.mk a b (par4 a b d), Tr.mk a (par4 a b d) d] := by
  set c := par4 a b d with hc
  set D := det3 a b d with hDd
  have n1 : (Tr.mk a b c).nd := ne_of_eq (k := 1) (by simp only [hc, hDd, par4, Tr.D, det3]; ring)
    one_ne_zero hD
  have n2 : (Tr.mk a c d).nd := ne_of_eq (k := 1) (by simp only [hc, hDd, par4, Tr.D, det3]; ring)
    one_ne_zero hD
  have hac : a ≠ c := fun h => Tr.nd_ne_ca n1 h.symm
  refine ⟨fun r hr => ?_, ?_, fun p => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact n1
    · exact n2
  · rw [List.pairwise_pair]
    exact sep' n1 n2 hac (κ := D) hD
      (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
      (nonpos_of_eq (k := -1) (by simp only [hc, hDd, par4, det3]; ring) (by norm_num))
      (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
      (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
      (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
      (nonneg_of_eq (k := 1) (by simp only [hc, hDd, par4, det3]; ring) zero_le_one)
  · simp [parReg]

/-- **Euclid's parallelograms** (Fig. 30): the parallelograms `abcd` and `abc'd'` on the same base,
with `d' = d + μ (b - a)`, `μ > 0`, are of equal content: adding the triangles `bc'c` and `ad'd`
(congruent by a translation) gives the same quadrilateral `abc'd`. -/
theorem euclid_pos {a b d : K × K} (hD : det3 a b d ≠ 0) {μ : K} (hμ : 0 < μ) :
    KEqContent (parReg a b (par4 a b d) d)
      (parReg a b (par4 a b (shift d a b μ)) (shift d a b μ)) := by
  set c := par4 a b d with hc
  set d' := shift d a b μ with hd'
  set c' := par4 a b d' with hc'
  set D := det3 a b d with hDd
  have hμ1 : 0 < μ + 1 := by linarith
  have hμne : μ ≠ 0 := hμ.ne'
  have hμ1ne : μ + 1 ≠ 0 := hμ1.ne'
  -- non-degeneracy
  have nabc : (Tr.mk a b c).nd := ne_of_eq (k := 1)
    (by simp only [hc, hDd, par4, Tr.D, det3]; ring) one_ne_zero hD
  have nacd : (Tr.mk a c d).nd := ne_of_eq (k := 1)
    (by simp only [hc, hDd, par4, Tr.D, det3]; ring) one_ne_zero hD
  have nbc'c : (Tr.mk b c' c).nd := ne_of_eq (k := μ)
    (by simp only [hc, hc', hd', hDd, par4, shift, Tr.D, det3]; ring) hμne hD
  have nabc' : (Tr.mk a b c').nd := ne_of_eq (k := 1)
    (by simp only [hc', hd', hDd, par4, shift, Tr.D, det3]; ring) one_ne_zero hD
  have nac'd' : (Tr.mk a c' d').nd := ne_of_eq (k := 1)
    (by simp only [hc', hd', hDd, par4, shift, Tr.D, det3]; ring) one_ne_zero hD
  have nad'd : (Tr.mk a d' d).nd := ne_of_eq (k := μ)
    (by simp only [hd', hDd, shift, Tr.D, det3]; ring) hμne hD
  have nac'd : (Tr.mk a c' d).nd := ne_of_eq (k := μ + 1)
    (by simp only [hc', hd', hDd, par4, shift, Tr.D, det3]; ring) hμ1ne hD
  have hac : a ≠ c := fun h => Tr.nd_ne_ca nabc h.symm
  have hbc : b ≠ c := Tr.nd_ne_bc nabc
  have hac' : a ≠ c' := fun h => Tr.nd_ne_ca nabc' h.symm
  have had' : a ≠ d' := Tr.nd_ne_ab nad'd
  -- the quadrilateral `abc'd`
  set U : K × K → Prop := fun p => (Tr.mk a b c').mem p ∨ (Tr.mk a c' d).mem p with hU
  have sp1 : ∀ p, (Tr.mk a c' d).mem p ↔ (Tr.mk a c' c).mem p ∨ (Tr.mk a c d).mem p := by
    intro p
    have h := split_mem nac'd (s := μ / (μ + 1)) (div_pos hμ hμ1)
      ((div_lt_one hμ1).2 (by linarith)) p
    have e : lerp (μ / (μ + 1)) c' d = c := by
      simp only [hc, hc', hd', par4, shift, lerp]
      refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
    simp only at h
    rw [e] at h
    exact h
  have ds : ∀ p, ((Tr.mk a b c').mem p ∨ (Tr.mk a c' c).mem p) ↔
      ((Tr.mk a b c).mem p ∨ (Tr.mk b c' c).mem p) := by
    intro p
    refine diag_swap (s := 1 / (μ + 1)) (r := 1 / (μ + 1)) (div_pos one_pos hμ1)
      ((div_lt_one hμ1).2 (by linarith)) (div_pos one_pos hμ1)
      ((div_lt_one hμ1).2 (by linarith)) ?_ ?_ ?_ ?_ ?_ p
    · simp only [hc, hc', hd', par4, shift, lerp]
      refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
    · exact ne_of_eq (k := -1) (by simp only [hc', hd', hDd, par4, shift, Tr.D, det3]; ring)
        (by norm_num) hD
    · exact ne_of_eq (k := μ) (by simp only [hc, hc', hd', hDd, par4, shift, Tr.D, det3]; ring)
        hμne hD
    · exact nabc
    · exact ne_of_eq (k := -μ) (by simp only [hc, hc', hd', hDd, par4, shift, Tr.D, det3]; ring)
        (neg_ne_zero.2 hμne) hD
  have sp2 : ∀ p, (Tr.mk a c' d).mem p ↔ (Tr.mk a c' d').mem p ∨ (Tr.mk a d' d).mem p := by
    intro p
    have h := split_mem nac'd (s := 1 / (μ + 1)) (div_pos one_pos hμ1)
      ((div_lt_one hμ1).2 (by linarith)) p
    have e : lerp (1 / (μ + 1)) c' d = d' := by
      simp only [hc', hd', par4, shift, lerp]
      refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
    simp only at h
    rw [e] at h
    exact h
  -- the two decompositions of the quadrilateral
  have dU1 : DecS U ([Tr.mk a b c, Tr.mk a c d] ++ [Tr.mk b c' c]) := by
    refine ⟨fun r hr => ?_, ?_, fun p => ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact nabc
      · exact nacd
      · exact nbc'c
    · simp only [List.cons_append, List.nil_append]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sep' nabc nacd hac (κ := D) hD
            (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
            (nonpos_of_eq (k := -1) (by simp only [hc, hDd, par4, det3]; ring) (by norm_num))
            (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 1) (by simp only [hc, hDd, par4, det3]; ring) zero_le_one)
        · exact sep nabc nbc'c hbc (κ := D) hD
            (nonneg_of_eq (k := 1) (by simp only [hc, hDd, par4, det3]; ring) zero_le_one)
            (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
            (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
            (nonpos_of_eq (k := -μ) (by simp only [hc, hc', hd', hDd, par4, shift, det3]; ring)
              (by linarith))
            (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact sep nacd nbc'c hbc (κ := D) hD
          (nonneg_of_eq (k := 1) (by simp only [hc, hDd, par4, det3]; ring) zero_le_one)
          (nonneg_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
          (nonneg_of_eq (k := 1) (by simp only [hc, hDd, par4, det3]; ring) zero_le_one)
          (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
          (nonpos_of_eq (k := -μ) (by simp only [hc, hc', hd', hDd, par4, shift, det3]; ring)
            (by linarith))
          (nonpos_of_eq (k := 0) (by simp only [hc, hDd, par4, det3]; ring) le_rfl)
      · intro r hr; exact absurd hr List.not_mem_nil
    · simp only [hU, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left]
      rw [sp1 p]
      have := ds p
      exact or_assoc.symm.trans ((or_congr_left this).trans (or_right_comm.trans or_assoc))
  have dU2 : DecS U ([Tr.mk a b c', Tr.mk a c' d'] ++ [Tr.mk a d' d]) := by
    refine ⟨fun r hr => ?_, ?_, fun p => ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact nabc'
      · exact nac'd'
      · exact nad'd
    · simp only [List.cons_append, List.nil_append]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sep' nabc' nac'd' hac' (κ := D) hD
            (nonpos_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
            (nonpos_of_eq (k := -1) (by simp only [hc', hd', hDd, par4, shift, det3]; ring)
              (by norm_num))
            (nonpos_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 1) (by simp only [hc', hd', hDd, par4, shift, det3]; ring)
              zero_le_one)
        · exact sep' nabc' nad'd hac' (κ := D) hD
            (nonpos_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
            (nonpos_of_eq (k := -1) (by simp only [hc', hd', hDd, par4, shift, det3]; ring)
              (by norm_num))
            (nonpos_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 0) (by simp only [hc', hd', hDd, par4, shift, det3]; ring) le_rfl)
            (nonneg_of_eq (k := 1) (by simp only [hc', hd', hDd, par4, shift, det3]; ring)
              zero_le_one)
            (nonneg_of_eq (k := μ + 1) (by simp only [hc', hd', hDd, par4, shift, det3]; ring)
              hμ1.le)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact sep' nac'd' nad'd had' (κ := D) hD
          (nonpos_of_eq (k := 0) (by simp only [hd', hDd, shift, det3]; ring) le_rfl)
          (nonpos_of_eq (k := -1) (by simp only [hc', hd', hDd, par4, shift, det3]; ring)
            (by norm_num))
          (nonpos_of_eq (k := 0) (by simp only [hd', hDd, shift, det3]; ring) le_rfl)
          (nonneg_of_eq (k := 0) (by simp only [hd', hDd, shift, det3]; ring) le_rfl)
          (nonneg_of_eq (k := 0) (by simp only [hd', hDd, shift, det3]; ring) le_rfl)
          (nonneg_of_eq (k := μ) (by simp only [hd', hDd, shift, det3]; ring) hμ.le)
      · intro r hr; exact absurd hr List.not_mem_nil
    · simp only [hU, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left]
      rw [sp2 p]
  have cg : KCong (Tr.mk b c' c) (Tr.mk a d' d) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [sqd, hc, hc', hd', par4, shift] <;> ring
  have dP1 := decS_parReg hD
  have hD' : det3 a b d' ≠ 0 := ne_of_eq (k := 1)
    (by simp only [hd', hDd, shift, det3]; ring) one_ne_zero hD
  have dP2 := decS_parReg hD'
  refine ⟨(Tr.mk b c' c).mem, (Tr.mk a d' d).mem, U, U, KPoly.tri nbc'c, KPoly.tri nad'd,
    ⟨[Tr.mk b c' c], [Tr.mk a d' d], DecS.single nbc'c, DecS.single nad'd,
      List.Forall₂.cons cg List.Forall₂.nil⟩,
    ⟨_, _, by simp, by simp, dP1, DecS.single nbc'c, dU1⟩,
    ⟨_, _, by simp, by simp, dP2, DecS.single nad'd, dU2⟩, KEqArea.refl dU1⟩

/-- **Parallelograms on the same base and between the same parallels have equal content**
(Euclid, I 35). -/
theorem euclid_K {a b d : K × K} (hD : det3 a b d ≠ 0) (μ : K) :
    KEqContent (parReg a b (par4 a b d) d)
      (parReg a b (par4 a b (shift d a b μ)) (shift d a b μ)) := by
  rcases lt_trichotomy μ 0 with h | rfl | h
  · have hD' : det3 a b (shift d a b μ) ≠ 0 := ne_of_eq (k := 1)
      (by simp only [shift, det3]; ring) one_ne_zero hD
    have := euclid_pos hD' (μ := -μ) (by linarith)
    have e : shift (shift d a b μ) a b (-μ) = d := by
      simp only [shift]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
    rw [e] at this
    exact this.symm
  · have e : shift d a b 0 = d := by
      simp only [shift]; refine Prod.ext ?_ ?_ <;> simp only <;> ring
    rw [e]
    exact KEqContent.refl ⟨_, by simp, decS_parReg hD⟩
  · exact euclid_pos hD h

/-! ### Shears -/

/-- **The shear**: moving the vertex `c` of a triangle parallel to the side `ab` keeps its content
(Theorem 26 twice and Euclid's parallelograms). -/
theorem shear_K {a b c : K × K} (hD : det3 a b c ≠ 0) (μ : K) :
    KEqContent (Tr.mk a b c).mem (Tr.mk a b (shift c a b μ)).mem := by
  set c₂ := shift c a b μ with hc₂
  have hD₂ : det3 a b c₂ ≠ 0 := ne_of_eq (k := 1) (by simp only [hc₂, shift, det3]; ring)
    one_ne_zero hD
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
  have c1 := a1.toContent (KPoly.tri hD)
  have c2 := a2.toContent (KPoly.tri hD₂)
  have c3 := euclid_K hDd (μ / 2)
  exact KEqContent.trans (KEqContent.trans c1 c3.symm) c2

end Areas

end HilbertFoundations
