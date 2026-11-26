import HilbertFoundations.AreasAux2

/-!
# Helper module for `Areas.lean`: equal area and equal content in the co-ordinate plane

This module contains no unit of Hilbert's text. Over a linearly ordered field `K` (in Areas.lean
the field of segments of the plane geometry, via co-ordinates):

* `sqd`: squared distances; `KCong`: triangles with equal squared sides (the co-ordinate form of
  Hilbert's congruence of triangles, by Theorem 16);
* `KIso`: the isometries `p ↦ o + R (diag (1, ε) (p - q))` of the co-ordinate plane (`R` a rotation
  matrix, `ε = ±1`), which preserve triangles, interiors and squared distances; congruent
  triangles are related by an isometry (`exists_iso`, no square roots needed); translations;
* `KEqArea`, `KComposed`, `KPoly`, `KEqContent`: the co-ordinate forms of Hilbert's definitions
  of § 18; the transitivity of equal area (`KEqArea.trans`, through the common refinement of
  `AreasAux2.lean` and the isometries: Theorem 24), the combination of equal-area polygons
  (`KEqArea.combine`), and the transitivity of equal content (`KEqContent.trans`), using
  translated copies placed far away (`far_iso`);
* the measure `kmeasure S` (half the sum of `|D|` over a decomposition): it is additive for
  composed polygons, invariant under equal area and equal content.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Squared distances and congruent triangles -/

/-- The squared distance. -/
def sqd (p q : K × K) : K := (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)

theorem sqd_comm (p q : K × K) : sqd p q = sqd q p := by unfold sqd; ring

/-- Congruent triangles in co-ordinates: equal squared sides. -/
def KCong (r r' : Tr K) : Prop :=
  sqd r.a r.b = sqd r'.a r'.b ∧ sqd r.a r.c = sqd r'.a r'.c ∧ sqd r.b r.c = sqd r'.b r'.c

theorem KCong.refl (r : Tr K) : KCong r r := ⟨rfl, rfl, rfl⟩

theorem KCong.symm {r r' : Tr K} (h : KCong r r') : KCong r' r := ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem KCong.trans {r r' r'' : Tr K} (h : KCong r r') (h' : KCong r' r'') : KCong r r'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-- `D²` in terms of the squared sides. -/
theorem D_sq (r : Tr K) : 4 * (r.D * r.D) = 4 * sqd r.a r.b * sqd r.a r.c -
    (sqd r.a r.b + sqd r.a r.c - sqd r.b r.c) * (sqd r.a r.b + sqd r.a r.c - sqd r.b r.c) := by
  unfold Tr.D det3 sqd; ring

theorem KCong.abs_D {r r' : Tr K} (h : KCong r r') : |r.D| = |r'.D| := by
  have e := D_sq r
  rw [h.1, h.2.1, h.2.2, ← D_sq r'] at e
  have : r.D * r.D = r'.D * r'.D := by linarith
  rw [← abs_mul_abs_self r.D, ← abs_mul_abs_self r'.D] at this
  exact (mul_self_inj (abs_nonneg _) (abs_nonneg _)).1 this

theorem KCong.nd {r r' : Tr K} (h : KCong r r') (hr : r.nd) : r'.nd := by
  intro e
  have := h.abs_D
  rw [e, abs_zero] at this
  exact hr (abs_eq_zero.1 this)

/-! ### Isometries of the co-ordinate plane -/

/-- An isometry `p ↦ o + R (diag (1, ε) (p - q))`, `R` the rotation matrix of `(c, s)`. -/
structure KIso (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  q : K × K
  o : K × K
  c : K
  s : K
  ε : K
  hcs : c * c + s * s = 1
  hε : ε * ε = 1

namespace KIso

/-- The image of a point. -/
def app (φ : KIso K) (p : K × K) : K × K :=
  (φ.o.1 + φ.c * (p.1 - φ.q.1) - φ.s * (φ.ε * (p.2 - φ.q.2)),
    φ.o.2 + φ.s * (p.1 - φ.q.1) + φ.c * (φ.ε * (p.2 - φ.q.2)))

/-- The inverse map. -/
def inv (φ : KIso K) (p : K × K) : K × K :=
  (φ.q.1 + (φ.c * (p.1 - φ.o.1) + φ.s * (p.2 - φ.o.2)),
    φ.q.2 + φ.ε * (-φ.s * (p.1 - φ.o.1) + φ.c * (p.2 - φ.o.2)))

theorem app_inv (φ : KIso K) (p : K × K) : φ.app (φ.inv p) = p := by
  have h1 := φ.hcs; have h2 := φ.hε
  unfold app inv
  ext
  · simp only
    linear_combination (p.1 - φ.o.1) * h1 + (φ.s * φ.s * (p.1 - φ.o.1) -
      φ.s * φ.c * (p.2 - φ.o.2)) * h2
  · simp only
    linear_combination (p.2 - φ.o.2) * h1 + (φ.c * φ.c * (p.2 - φ.o.2) -
      φ.c * φ.s * (p.1 - φ.o.1)) * h2

theorem inv_app (φ : KIso K) (p : K × K) : φ.inv (φ.app p) = p := by
  have h1 := φ.hcs; have h2 := φ.hε
  unfold app inv
  ext
  · simp only
    linear_combination (p.1 - φ.q.1) * h1
  · simp only
    linear_combination (p.2 - φ.q.2) * (φ.c * φ.c + φ.s * φ.s) * h2 + (p.2 - φ.q.2) * h1

theorem app_injective (φ : KIso K) {p p' : K × K} (h : φ.app p = φ.app p') : p = p' := by
  rw [← φ.inv_app p, h, φ.inv_app]

theorem sqd_app (φ : KIso K) (p p' : K × K) : sqd (φ.app p) (φ.app p') = sqd p p' := by
  have h1 := φ.hcs; have h2 := φ.hε
  unfold sqd app; simp only
  linear_combination ((p.1 - p'.1) * (p.1 - p'.1) + φ.ε * φ.ε * (p.2 - p'.2) * (p.2 - p'.2)) * h1 +
    (p.2 - p'.2) * (p.2 - p'.2) * h2

theorem det3_app (φ : KIso K) (a b p : K × K) :
    det3 (φ.app a) (φ.app b) (φ.app p) = φ.ε * det3 a b p := by
  have h1 := φ.hcs
  unfold det3 app; simp only
  linear_combination φ.ε * ((b.1 - a.1) * (p.2 - a.2) - (b.2 - a.2) * (p.1 - a.1)) * h1

theorem app_lerp (φ : KIso K) (s : K) (p p' : K × K) :
    φ.app (lerp s p p') = lerp s (φ.app p) (φ.app p') := by
  unfold app lerp; ext <;> simp only <;> ring

/-- The translation by `(M, 0)`. -/
def transl (M : K) : KIso K where
  q := (0, 0)
  o := (M, 0)
  c := 1
  s := 0
  ε := 1
  hcs := by ring
  hε := by ring

theorem transl_app (M : K) (p : K × K) : (transl M).app p = (p.1 + M, p.2) := by
  unfold transl app; ext <;> simp <;> ring

end KIso

/-- The image of a triangle. -/
def Tr.mapI (t : Tr K) (φ : KIso K) : Tr K := ⟨φ.app t.a, φ.app t.b, φ.app t.c⟩

theorem Tr.D_mapI (t : Tr K) (φ : KIso K) : (t.mapI φ).D = φ.ε * t.D := φ.det3_app _ _ _

theorem Tr.nd_mapI {t : Tr K} (φ : KIso K) : (t.mapI φ).nd ↔ t.nd := by
  unfold Tr.nd; rw [Tr.D_mapI]
  have hε : φ.ε ≠ 0 := fun e => by have := φ.hε; rw [e] at this; simp at this
  exact ⟨fun h e => h (by rw [e, mul_zero]), fun h => mul_ne_zero hε h⟩

theorem Tr.mem_mapI (t : Tr K) (φ : KIso K) (p : K × K) :
    (t.mapI φ).mem (φ.app p) ↔ t.mem p := by
  have h2 := φ.hε
  unfold Tr.mem
  rw [Tr.D_mapI]
  simp only [Tr.mapI, φ.det3_app]
  have e : ∀ x y : K, φ.ε * x * (φ.ε * y) = x * y := by
    intro x y; linear_combination x * y * h2
  rw [e, e, e]

theorem Tr.int_mapI (t : Tr K) (φ : KIso K) (p : K × K) :
    (t.mapI φ).int (φ.app p) ↔ t.int p := by
  have h2 := φ.hε
  unfold Tr.int
  rw [Tr.D_mapI]
  simp only [Tr.mapI, φ.det3_app]
  have e : ∀ x y : K, φ.ε * x * (φ.ε * y) = x * y := by
    intro x y; linear_combination x * y * h2
  rw [e, e, e]

theorem Tr.mem_mapI' (t : Tr K) (φ : KIso K) (p : K × K) :
    (t.mapI φ).mem p ↔ t.mem (φ.inv p) := by
  rw [← Tr.mem_mapI t φ, φ.app_inv]

theorem Tr.int_mapI' (t : Tr K) (φ : KIso K) (p : K × K) :
    (t.mapI φ).int p ↔ t.int (φ.inv p) := by
  rw [← Tr.int_mapI t φ, φ.app_inv]

theorem KCong.mapI (t : Tr K) (φ : KIso K) : KCong t (t.mapI φ) :=
  ⟨(φ.sqd_app _ _).symm, (φ.sqd_app _ _).symm, (φ.sqd_app _ _).symm⟩

/-- The image of a region. -/
def imgI (φ : KIso K) (S : K × K → Prop) : K × K → Prop := fun p => S (φ.inv p)

theorem DecS.mapI {S : K × K → Prop} {l : List (Tr K)} (h : DecS S l) (φ : KIso K) :
    DecS (imgI φ S) (l.map (fun r => r.mapI φ)) := by
  obtain ⟨hnd, hpw, hun⟩ := h
  refine ⟨?_, ?_, fun p => ?_⟩
  · simp only [List.mem_map]
    rintro r ⟨t, ht, rfl⟩
    exact (Tr.nd_mapI φ).2 (hnd t ht)
  · rw [List.pairwise_map]
    refine hpw.imp fun {r s} h p hp => h (φ.inv p) ?_
    rw [← Tr.int_mapI' r φ, ← Tr.int_mapI' s φ]; exact hp
  · simp only [imgI, List.mem_map, exists_exists_and_eq_and]
    rw [hun]
    simp only [Tr.mem_mapI']

theorem iso_core (p1 p2 r1 r2 P1 P2 R1 R2 : K) (hD : p1 * r2 - p2 * r1 ≠ 0)
    (hn : p1 * p1 + p2 * p2 = P1 * P1 + P2 * P2) (hw : r1 * r1 + r2 * r2 = R1 * R1 + R2 * R2)
    (hdot : p1 * r1 + p2 * r2 = P1 * R1 + P2 * R2) :
    ∃ ε c s : K, ε * ε = 1 ∧ c * c + s * s = 1 ∧ c * p1 - s * (ε * p2) = P1 ∧
      s * p1 + c * (ε * p2) = P2 ∧ c * r1 - s * (ε * r2) = R1 ∧ s * r1 + c * (ε * r2) = R2 := by
  have hcr2 : (p1 * r2 - p2 * r1) * (p1 * r2 - p2 * r1) =
      (P1 * R2 - P2 * R1) * (P1 * R2 - P2 * R1) := by
    have e1 : (p1 * r2 - p2 * r1) * (p1 * r2 - p2 * r1) =
        (p1 * p1 + p2 * p2) * (r1 * r1 + r2 * r2) - (p1 * r1 + p2 * r2) * (p1 * r1 + p2 * r2) := by
      ring
    have e2 : (P1 * R2 - P2 * R1) * (P1 * R2 - P2 * R1) =
        (P1 * P1 + P2 * P2) * (R1 * R1 + R2 * R2) - (P1 * R1 + P2 * R2) * (P1 * R1 + P2 * R2) := by
      ring
    rw [e1, e2, hn, hw, hdot]
  -- the sign `ε`
  obtain ⟨ε, hε, hεc⟩ : ∃ ε : K, ε * ε = 1 ∧ ε * (p1 * r2 - p2 * r1) = P1 * R2 - P2 * R1 := by
    by_cases he : p1 * r2 - p2 * r1 = P1 * R2 - P2 * R1
    · exact ⟨1, by ring, by rw [he]; ring⟩
    · refine ⟨-1, by ring, ?_⟩
      have : (p1 * r2 - p2 * r1 - (P1 * R2 - P2 * R1)) *
          (p1 * r2 - p2 * r1 + (P1 * R2 - P2 * R1)) = 0 := by
        linear_combination hcr2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) he
      · linear_combination -h
  have hn0 : p1 * p1 + p2 * p2 ≠ 0 := by
    intro e
    have e1 : p1 = 0 := by nlinarith [mul_self_nonneg p1, mul_self_nonneg p2]
    have e2 : p2 = 0 := by nlinarith [mul_self_nonneg p1, mul_self_nonneg p2]
    apply hD; rw [e1, e2]; ring
  obtain ⟨c, hcn⟩ : ∃ c : K, c * (p1 * p1 + p2 * p2) = p1 * P1 + ε * p2 * P2 :=
    ⟨_, div_mul_cancel₀ _ hn0⟩
  obtain ⟨s, hsn⟩ : ∃ s : K, s * (p1 * p1 + p2 * p2) = p1 * P2 - ε * p2 * P1 :=
    ⟨_, div_mul_cancel₀ _ hn0⟩
  refine ⟨ε, c, s, hε, ?_, ?_, ?_, ?_, ?_⟩
  · have key : (c * c + s * s) * ((p1 * p1 + p2 * p2) * (p1 * p1 + p2 * p2)) =
        1 * ((p1 * p1 + p2 * p2) * (p1 * p1 + p2 * p2)) := by
      linear_combination (c * (p1 * p1 + p2 * p2) + (p1 * P1 + ε * p2 * P2)) * hcn +
        (s * (p1 * p1 + p2 * p2) + (p1 * P2 - ε * p2 * P1)) * hsn -
        (p1 * p1 + ε * ε * p2 * p2) * hn + ((p1 * p1 + p2 * p2) * p2 * p2) * hε
    exact mul_right_cancel₀ (mul_ne_zero hn0 hn0) key
  · have key : (c * p1 - s * (ε * p2)) * (p1 * p1 + p2 * p2) = P1 * (p1 * p1 + p2 * p2) := by
      linear_combination p1 * hcn - ε * p2 * hsn + P1 * p2 * p2 * hε
    exact mul_right_cancel₀ hn0 key
  · have key : (s * p1 + c * (ε * p2)) * (p1 * p1 + p2 * p2) = P2 * (p1 * p1 + p2 * p2) := by
      linear_combination p1 * hsn + ε * p2 * hcn + P2 * p2 * p2 * hε
    exact mul_right_cancel₀ hn0 key
  · have key : (c * r1 - s * (ε * r2)) * (p1 * p1 + p2 * p2) = R1 * (p1 * p1 + p2 * p2) := by
      linear_combination r1 * hcn - ε * r2 * hsn + P1 * hdot - P2 * hεc +
        P1 * p2 * r2 * hε - R1 * hn
    exact mul_right_cancel₀ hn0 key
  · have key : (s * r1 + c * (ε * r2)) * (p1 * p1 + p2 * p2) = R2 * (p1 * p1 + p2 * p2) := by
      linear_combination r1 * hsn + ε * r2 * hcn + P2 * hdot + P1 * hεc +
        P2 * p2 * r2 * hε - R2 * hn
    exact mul_right_cancel₀ hn0 key

/-- **Congruent triangles are related by an isometry.** -/
theorem exists_iso {r r' : Tr K} (hr : r.nd) (h : KCong r r') : ∃ φ : KIso K, r.mapI φ = r' := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := r
  obtain ⟨⟨a1', a2'⟩, ⟨b1', b2'⟩, ⟨c1', c2'⟩⟩ := r'
  unfold KCong sqd at h
  simp only at h
  obtain ⟨hab, hac, hbc⟩ := h
  have hD : (b1 - a1) * (c2 - a2) - (b2 - a2) * (c1 - a1) ≠ 0 := hr
  obtain ⟨ε, c, s, hε, hcs, e1, e2, e3, e4⟩ := iso_core (b1 - a1) (b2 - a2) (c1 - a1) (c2 - a2)
    (b1' - a1') (b2' - a2') (c1' - a1') (c2' - a2') hD (by linear_combination hab)
    (by linear_combination hac) (by linear_combination (hab + hac - hbc) / 2)
  refine ⟨⟨(a1, a2), (a1', a2'), c, s, ε, hcs, hε⟩, ?_⟩
  simp only [Tr.mapI, KIso.app]
  refine Tr.ext ?_ ?_ ?_ <;> refine Prod.ext ?_ ?_ <;> simp only <;> linarith

/-! ### Decompositions: appending, permuting, disjoint unions -/

theorem DecS.perm {S : K × K → Prop} {l l' : List (Tr K)} (h : DecS S l) (hp : l.Perm l') :
    DecS S l' := by
  refine ⟨fun r hr => h.1 r (hp.symm.subset hr),
    h.2.1.perm hp (fun h p hp => h p ⟨hp.2, hp.1⟩), fun p => ?_⟩
  rw [h.2.2 p]
  exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hp.subset hr, h⟩, fun ⟨r, hr, h⟩ => ⟨r, hp.symm.subset hr, h⟩⟩

/-- In a decomposition `a₁ ++ a₂` of `U` (with `aᵢ` decomposing `Sᵢ`), the decompositions of the
two parts can be replaced by any other decompositions. -/
theorem DecS.append_of {U S1 S2 : K × K → Prop} {a1 a2 l1 l2 : List (Tr K)} (hU : DecS U (a1 ++ a2))
    (ha1 : DecS S1 a1) (ha2 : DecS S2 a2) (hl1 : DecS S1 l1) (hl2 : DecS S2 l2) :
    DecS U (l1 ++ l2) := by
  have hcross := (List.pairwise_append.1 hU.2.1).2.2
  refine ⟨fun r hr => ?_, List.pairwise_append.2 ⟨hl1.2.1, hl2.2.1, ?_⟩, fun p => ?_⟩
  · rcases List.mem_append.1 hr with h | h
    · exact hl1.1 r h
    · exact hl2.1 r h
  · intro t ht t' ht' p ⟨h1, h2⟩
    obtain ⟨s1, hs1, hp1⟩ := (ha1.2.2 p).1 (hl1.sub ht (Tr.mem_of_int h1))
    obtain ⟨q, hq1, hq2⟩ := Tr.int_meet (hl2.1 t' ht') (ha1.1 s1 hs1) h2 hp1
    obtain ⟨s2, hs2, hp2⟩ := (ha2.2.2 q).1 (hl2.sub ht' (Tr.mem_of_int hq1))
    obtain ⟨q', h3, h4⟩ := Tr.int_meet (ha1.1 s1 hs1) (ha2.1 s2 hs2) hq2 hp2
    exact hcross s1 hs1 s2 hs2 q' ⟨h3, h4⟩
  · rw [hU.2.2 p]
    simp only [List.mem_append]
    constructor
    · rintro ⟨r, hr | hr, h⟩
      · obtain ⟨r', hr', h'⟩ := (hl1.2.2 p).1 ((ha1.2.2 p).2 ⟨r, hr, h⟩)
        exact ⟨r', Or.inl hr', h'⟩
      · obtain ⟨r', hr', h'⟩ := (hl2.2.2 p).1 ((ha2.2.2 p).2 ⟨r, hr, h⟩)
        exact ⟨r', Or.inr hr', h'⟩
    · rintro ⟨r, hr | hr, h⟩
      · obtain ⟨r', hr', h'⟩ := (ha1.2.2 p).1 ((hl1.2.2 p).2 ⟨r, hr, h⟩)
        exact ⟨r', Or.inl hr', h'⟩
      · obtain ⟨r', hr', h'⟩ := (ha2.2.2 p).1 ((hl2.2.2 p).2 ⟨r, hr, h⟩)
        exact ⟨r', Or.inr hr', h'⟩

/-- Two decomposed regions without common point form a decomposition of their union. -/
theorem DecS.append_disjoint {S1 S2 : K × K → Prop} {l1 l2 : List (Tr K)} (h1 : DecS S1 l1)
    (h2 : DecS S2 l2) (hd : ∀ p, S1 p → ¬S2 p) :
    DecS (fun p => S1 p ∨ S2 p) (l1 ++ l2) := by
  refine ⟨fun r hr => ?_, List.pairwise_append.2 ⟨h1.2.1, h2.2.1, ?_⟩, fun p => ?_⟩
  · rcases List.mem_append.1 hr with h | h
    · exact h1.1 r h
    · exact h2.1 r h
  · intro t ht t' ht' p ⟨a, b⟩
    exact hd p (h1.sub ht (Tr.mem_of_int a)) (h2.sub ht' (Tr.mem_of_int b))
  · show S1 p ∨ S2 p ↔ _
    rw [h1.2.2 p, h2.2.2 p]
    simp only [List.mem_append]
    constructor
    · rintro (⟨r, hr, h⟩ | ⟨r, hr, h⟩)
      · exact ⟨r, Or.inl hr, h⟩
      · exact ⟨r, Or.inr hr, h⟩
    · rintro ⟨r, hr | hr, h⟩
      · exact Or.inl ⟨r, hr, h⟩
      · exact Or.inr ⟨r, hr, h⟩

/-! ### Equal area and equal content in co-ordinates -/

/-- A polygon (polygonal region) in co-ordinates. -/
def KPoly (S : K × K → Prop) : Prop := ∃ l : List (Tr K), l ≠ [] ∧ DecS S l

/-- `U` is composed of the polygons `S₁` and `S₂`. -/
def KComposed (U S1 S2 : K × K → Prop) : Prop :=
  ∃ l1 l2 : List (Tr K), l1 ≠ [] ∧ l2 ≠ [] ∧ DecS S1 l1 ∧ DecS S2 l2 ∧ DecS U (l1 ++ l2)

/-- Equal area in co-ordinates. -/
def KEqArea (S T : K × K → Prop) : Prop :=
  ∃ l m : List (Tr K), DecS S l ∧ DecS T m ∧ List.Forall₂ KCong l m

/-- Equal content in co-ordinates. -/
def KEqContent (S T : K × K → Prop) : Prop :=
  ∃ S' T' U V : K × K → Prop, KPoly S' ∧ KPoly T' ∧ KEqArea S' T' ∧ KComposed U S S' ∧
    KComposed V T T' ∧ KEqArea U V

theorem KEqArea.refl {S : K × K → Prop} {l : List (Tr K)} (h : DecS S l) : KEqArea S S :=
  ⟨l, l, h, h, List.forall₂_same.2 fun r _ => KCong.refl r⟩

theorem forall₂_kcong_symm {l m : List (Tr K)} (h : List.Forall₂ KCong l m) :
    List.Forall₂ KCong m l := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons h.symm ih

theorem KEqArea.symm {S T : K × K → Prop} (h : KEqArea S T) : KEqArea T S := by
  obtain ⟨l, m, hl, hm, hc⟩ := h
  exact ⟨m, l, hm, hl, forall₂_kcong_symm hc⟩

theorem KComposed.comm {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) : KComposed U S2 S1 := by
  obtain ⟨l1, l2, n1, n2, h1, h2, hU⟩ := h
  exact ⟨l2, l1, n2, n1, h2, h1, hU.perm List.perm_append_comm⟩

theorem KComposed.poly_left {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) : KPoly S1 := by
  obtain ⟨l1, l2, n1, n2, h1, h2, hU⟩ := h
  exact ⟨l1, n1, h1⟩

theorem KComposed.poly_right {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) : KPoly S2 := by
  obtain ⟨l1, l2, n1, n2, h1, h2, hU⟩ := h
  exact ⟨l2, n2, h2⟩

theorem KComposed.decS {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) {l1 l2 : List (Tr K)}
    (h1 : DecS S1 l1) (h2 : DecS S2 l2) : DecS U (l1 ++ l2) := by
  obtain ⟨a1, a2, -, -, ha1, ha2, hU⟩ := h
  exact hU.append_of ha1 ha2 h1 h2

theorem KComposed.congr {U U' S1 S2 : K × K → Prop} (h : KComposed U S1 S2)
    (e : ∀ p, U p ↔ U' p) : KComposed U' S1 S2 := by
  obtain ⟨l1, l2, n1, n2, h1, h2, hU⟩ := h
  exact ⟨l1, l2, n1, n2, h1, h2, hU.congr e⟩

/-- **Combining polygons of equal area gives polygons of equal area.** -/
theorem KEqArea.combine {U V S1 S2 T1 T2 : K × K → Prop} (hU : KComposed U S1 S2)
    (hV : KComposed V T1 T2) (h1 : KEqArea S1 T1) (h2 : KEqArea S2 T2) : KEqArea U V := by
  obtain ⟨l1, m1, hl1, hm1, c1⟩ := h1
  obtain ⟨l2, m2, hl2, hm2, c2⟩ := h2
  exact ⟨l1 ++ l2, m1 ++ m2, hU.decS hl1 hl2, hV.decS hm1 hm2, List.rel_append c1 c2⟩

/-- An isometric copy has equal area. -/
theorem KEqArea.mapI {S : K × K → Prop} {l : List (Tr K)} (h : DecS S l) (φ : KIso K) :
    KEqArea S (imgI φ S) :=
  ⟨l, l.map (fun r => r.mapI φ), h, h.mapI φ,
    List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun r _ => KCong.mapI r φ)⟩

/-! ### The pull-back of a refinement along an equal-area correspondence -/

open Classical in
theorem pullback {S S1 : K × K → Prop} {m l Q : List (Tr K)} (hm : DecS S m) (hl : DecS S1 l)
    (hc : List.Forall₂ KCong l m) (hQ : DecS S Q) {j : Tr K → Tr K} (hj : ∀ q ∈ Q, j q ∈ m)
    (hf : ∀ r ∈ m, DecS r.mem (Q.filter (fun q => j q = r))) :
    ∃ g : Tr K → KIso K, DecS S1 (Q.map (fun q => q.mapI (g (j q)))) := by
  have hlen := hc.length_eq
  have hcong : ∀ i (h1 : i < l.length) (h2 : i < m.length), KCong l[i] m[i] := by
    intro i h1 h2
    exact (List.forall₂_iff_get.1 hc).2 i h1 h2
  have hnodup := hm.nodup
  have hidxlt : ∀ r ∈ m, m.idxOf r < l.length := fun r hr => by
    rw [hlen]; exact List.idxOf_lt_length_of_mem hr
  -- the isometry carrying `m[i]` to `l[i]`
  have hex : ∀ r (hr : r ∈ m), ∃ φ : KIso K, r.mapI φ = l[m.idxOf r]'(hidxlt r hr) := by
    intro r hr
    have hi := List.idxOf_lt_length_of_mem hr
    have e := List.getElem_idxOf hi
    have := hcong (m.idxOf r) (by rw [hlen]; exact hi) hi
    rw [e] at this
    exact exists_iso (hm.1 r hr) this.symm
  let g : Tr K → KIso K := fun r => if h : r ∈ m then (hex r h).choose else KIso.transl 0
  have hg : ∀ r (hr : r ∈ m), r.mapI (g r) = l[m.idxOf r]'(hidxlt r hr) := by
    intro r hr
    simp only [g, dif_pos hr]
    exact (hex r hr).choose_spec
  have hsub : ∀ q ∈ Q, ∀ p, q.mem p → (j q).mem p := by
    intro q hq p hp
    exact ((hf (j q) (hj q hq)).2.2 p).2 ⟨q, List.mem_filter.2 ⟨hq, by simp⟩, hp⟩
  have hidx : ∀ r ∈ m, ∀ r' ∈ m, m.idxOf r = m.idxOf r' → r = r' := by
    intro r hr r' hr' e
    have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hr)
    have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hr')
    simp only [e] at h1
    rw [← h1, h2]
  have hldisj : ∀ i i' (hi : i < l.length) (hi' : i' < l.length), i ≠ i' →
      ∀ p, ¬(l[i].int p ∧ l[i'].int p) := by
    intro i i' hi hi' hne p hp
    rcases lt_or_gt_of_ne hne with h | h
    · exact List.pairwise_iff_getElem.1 hl.2.1 i i' hi hi' h p hp
    · exact List.pairwise_iff_getElem.1 hl.2.1 i' i hi' hi h p ⟨hp.2, hp.1⟩
  refine ⟨g, ?_, ?_, fun p => ?_⟩
  · simp only [List.mem_map]
    rintro r ⟨q, hq, rfl⟩
    exact (Tr.nd_mapI _).2 (hQ.1 q hq)
  · rw [List.pairwise_map]
    refine hQ.2.1.imp_of_mem fun {q q'} hq hq' h p hp => ?_
    rw [Tr.int_mapI', Tr.int_mapI'] at hp
    by_cases e : j q = j q'
    · rw [e] at hp
      exact h _ hp
    · -- the images lie in different triangles of `l`
      rw [← Tr.int_mapI', ← Tr.int_mapI'] at hp
      have i1 : (l[m.idxOf (j q)]'(hidxlt _ (hj q hq))).int p := by
        rw [← hg (j q) (hj q hq)]
        refine Tr.int_of_sub ((Tr.nd_mapI _).2 (hQ.1 q hq)) ((Tr.nd_mapI _).2 (hm.1 _ (hj q hq)))
          (fun x hx => ?_) hp.1
        rw [Tr.mem_mapI'] at hx ⊢
        exact hsub q hq _ hx
      have i2 : (l[m.idxOf (j q')]'(hidxlt _ (hj q' hq'))).int p := by
        rw [← hg (j q') (hj q' hq')]
        refine Tr.int_of_sub ((Tr.nd_mapI _).2 (hQ.1 q' hq')) ((Tr.nd_mapI _).2 (hm.1 _ (hj q' hq')))
          (fun x hx => ?_) hp.2
        rw [Tr.mem_mapI'] at hx ⊢
        exact hsub q' hq' _ hx
      exact hldisj _ _ _ _ (fun e' => e (hidx _ (hj q hq) _ (hj q' hq') e')) p ⟨i1, i2⟩
  · constructor
    · intro hp
      obtain ⟨pp, hpp, hmem⟩ := (hl.2.2 p).1 hp
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpp
      have him : i < m.length := by rw [← hlen]; exact hi
      set r := m[i]
      have hr : r ∈ m := List.getElem_mem him
      have hri : m.idxOf r = i := List.Nodup.idxOf_getElem hnodup i him
      have e := hg r hr
      simp only [hri] at e
      rw [← e, Tr.mem_mapI'] at hmem
      obtain ⟨q, hq, hqm⟩ := ((hf r hr).2.2 _).1 hmem
      obtain ⟨hqQ, hqj⟩ := List.mem_filter.1 hq
      simp only [decide_eq_true_eq] at hqj
      refine ⟨_, List.mem_map.2 ⟨q, hqQ, rfl⟩, ?_⟩
      rw [Tr.mem_mapI', hqj]
      exact hqm
    · rintro ⟨_, hr, hmem⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      rw [Tr.mem_mapI'] at hmem
      have hrm := hj q hq
      have := hsub q hq _ hmem
      rw [← Tr.mem_mapI', hg _ hrm] at this
      exact (hl.2.2 p).2 ⟨_, List.getElem_mem _, this⟩

/-- **Theorem 24 (first part), in co-ordinates**: two polygons of equal area to a third are of
equal area. -/
theorem KEqArea.trans {S1 S2 S3 : K × K → Prop} (h1 : KEqArea S1 S3) (h2 : KEqArea S2 S3) :
    KEqArea S1 S2 := by
  classical
  obtain ⟨l1, m1, hl1, hm1, c1⟩ := h1
  obtain ⟨l2, m2, hl2, hm2, c2⟩ := h2
  obtain ⟨Q, j1, j2, hQ, hj, f1, f2⟩ := common_refinement hm1 hm2
  obtain ⟨g1, d1⟩ := pullback hm1 hl1 c1 hQ (fun q hq => (hj q hq).1) f1
  obtain ⟨g2, d2⟩ := pullback hm2 hl2 c2 hQ (fun q hq => (hj q hq).2.1) f2
  refine ⟨_, _, d1, d2, ?_⟩
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun q _ => (KCong.mapI q _).symm.trans (KCong.mapI q _)

/-! ### Copies far away -/

theorem Tr.fst_le {t : Tr K} (ht : t.nd) {p : K × K} (hp : t.mem p) {B : K} (ha : t.a.1 ≤ B)
    (hb : t.b.1 ≤ B) (hc : t.c.1 ≤ B) : p.1 ≤ B := by
  obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.mem_iff_bary ht).1 hp
  simp only [comb]
  have e : α * B + β * B + γ * B = B := by rw [← add_mul, ← add_mul, hs, one_mul]
  have := mul_le_mul_of_nonneg_left ha h1
  have := mul_le_mul_of_nonneg_left hb h2
  have := mul_le_mul_of_nonneg_left hc h3
  linarith

theorem Tr.le_fst {t : Tr K} (ht : t.nd) {p : K × K} (hp : t.mem p) {B : K} (ha : B ≤ t.a.1)
    (hb : B ≤ t.b.1) (hc : B ≤ t.c.1) : B ≤ p.1 := by
  obtain ⟨α, β, γ, h1, h2, h3, hs, rfl⟩ := (Tr.mem_iff_bary ht).1 hp
  simp only [comb]
  have e : α * B + β * B + γ * B = B := by rw [← add_mul, ← add_mul, hs, one_mul]
  have := mul_le_mul_of_nonneg_left ha h1
  have := mul_le_mul_of_nonneg_left hb h2
  have := mul_le_mul_of_nonneg_left hc h3
  linarith

theorem list_bounds (l : List (Tr K)) : ∃ B1 B2 : K, ∀ r ∈ l,
    (r.a.1 ≤ B1 ∧ r.b.1 ≤ B1 ∧ r.c.1 ≤ B1) ∧ (B2 ≤ r.a.1 ∧ B2 ≤ r.b.1 ∧ B2 ≤ r.c.1) := by
  induction l with
  | nil => exact ⟨0, 0, fun r hr => absurd hr List.not_mem_nil⟩
  | cons r l ih =>
    obtain ⟨B1, B2, h⟩ := ih
    refine ⟨max B1 (max r.a.1 (max r.b.1 r.c.1)), min B2 (min r.a.1 (min r.b.1 r.c.1)),
      fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> simp
    · obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := h r' hr'
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      · exact le_trans a1 (le_max_left _ _)
      · exact le_trans a2 (le_max_left _ _)
      · exact le_trans a3 (le_max_left _ _)
      · exact le_trans (min_le_left _ _) b1
      · exact le_trans (min_le_left _ _) b2
      · exact le_trans (min_le_left _ _) b3

/-- **A translated copy can be placed away from finitely many triangles.** -/
theorem far_iso (l1 l2 : List (Tr K)) (h1 : ∀ r ∈ l1, r.nd) (h2 : ∀ r ∈ l2, r.nd) :
    ∃ φ : KIso K, ∀ r ∈ l1, ∀ r' ∈ l2, ∀ p, r.mem p → ¬(r'.mapI φ).mem p := by
  obtain ⟨B1, B1', hB1⟩ := list_bounds l1
  obtain ⟨B2', B2, hB2⟩ := list_bounds l2
  refine ⟨KIso.transl (B1 - B2 + 1), fun r hr r' hr' p hp hp' => ?_⟩
  have a := (hB1 r hr).1
  have b := (hB2 r' hr').2
  have x1 := Tr.fst_le (h1 r hr) hp a.1 a.2.1 a.2.2
  rw [Tr.mem_mapI'] at hp'
  have x2 := Tr.le_fst (h2 r' hr') hp' b.1 b.2.1 b.2.2
  simp only [KIso.inv, KIso.transl] at x2
  linarith

/-- A polygon has an isometric copy away from given triangles. -/
theorem far_obst {T : K × K → Prop} {lT : List (Tr K)} (hT : DecS T lT) (obst : List (Tr K))
    (hob : ∀ r ∈ obst, r.nd) : ∃ φ : KIso K, ∀ r ∈ obst, ∀ p, r.mem p → ¬imgI φ T p := by
  obtain ⟨φ, hφ⟩ := far_iso obst lT hob hT.1
  refine ⟨φ, fun r hr p hp hp' => ?_⟩
  obtain ⟨r', hr', hr'p⟩ := ((hT.mapI φ).2.2 p).1 hp'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr'
  exact hφ r hr t ht p hp hr'p

theorem disj_of_obst {S A : K × K → Prop} {lS obst : List (Tr K)} (hS : DecS S lS)
    (hsub : ∀ r ∈ lS, r ∈ obst) (h : ∀ r ∈ obst, ∀ p, r.mem p → ¬A p) : ∀ p, S p → ¬A p := by
  intro p hp
  obtain ⟨r, hr, hrp⟩ := (hS.2.2 p).1 hp
  exact h r (hsub r hr) p hrp

/-- Adding a polygon `A` without common point to a composed polygon. -/
theorem KComposed.add_disjoint {U S1 S2 A : K × K → Prop} (h : KComposed U S1 S2)
    {lA : List (Tr K)} (hA : DecS A lA) (hne : lA ≠ []) (hd : ∀ p, U p → ¬A p) :
    KComposed (fun p => U p ∨ A p) S1 (fun p => S2 p ∨ A p) ∧
      KComposed (fun p => U p ∨ A p) U A ∧ KComposed (fun p => S2 p ∨ A p) S2 A := by
  obtain ⟨l1, l2, n1, n2, h1, h2, hU⟩ := h
  have hd2 : ∀ p, S2 p → ¬A p := fun p hp => hd p ((hU.2.2 p).2 (by
    obtain ⟨r, hr, h⟩ := (h2.2.2 p).1 hp
    exact ⟨r, List.mem_append_right _ hr, h⟩))
  have dUA := hU.append_disjoint hA hd
  have dSA := h2.append_disjoint hA hd2
  refine ⟨⟨l1, l2 ++ lA, n1, by simp [n2], h1, dSA, by rw [← List.append_assoc]; exact dUA⟩,
    ⟨l1 ++ l2, lA, by simp [n1], hne, hU, hA, dUA⟩, ⟨l2, lA, n2, hne, h2, hA, dSA⟩⟩

theorem KComposed.decS_left {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) :
    ∃ l, l ≠ [] ∧ DecS S1 l := h.poly_left

/-- **Theorem 24 (second part), in co-ordinates**: two polygons of equal content to a third are
of equal content. -/
theorem KEqContent.trans {S T W : K × K → Prop} (h1 : KEqContent S T) (h2 : KEqContent W T) :
    KEqContent S W := by
  obtain ⟨S', T', U, V, -, pT', eST, cU, cV, eUV⟩ := h1
  obtain ⟨W'', T'', U2, V2, -, pT'', eWT, cU2, cV2, eUV2⟩ := h2
  obtain ⟨lU, lV, dU, dV, -⟩ := id eUV
  obtain ⟨lU2, lV2, dU2, dV2, -⟩ := id eUV2
  obtain ⟨lT', nT', dT'⟩ := pT'
  obtain ⟨lT'', nT'', dT''⟩ := pT''
  obtain ⟨lT, nT, dT⟩ := cV.poly_left
  -- `A`: a copy of `T''` away from `U` and `V`; `B`: a copy of `T'` away from `U₂` and `V₂`
  obtain ⟨φ, hφ⟩ := far_obst dT'' (lU ++ lV) (fun r hr => by
    rcases List.mem_append.1 hr with h | h
    · exact dU.1 r h
    · exact dV.1 r h)
  obtain ⟨ψ, hψ⟩ := far_obst dT' (lU2 ++ lV2) (fun r hr => by
    rcases List.mem_append.1 hr with h | h
    · exact dU2.1 r h
    · exact dV2.1 r h)
  set A := imgI φ T''
  set B := imgI ψ T'
  have dA := dT''.mapI φ
  have dB := dT'.mapI ψ
  have nA : lT''.map (fun r => r.mapI φ) ≠ [] := by simp [nT'']
  have nB : lT'.map (fun r => r.mapI ψ) ≠ [] := by simp [nT']
  have UA := disj_of_obst dU (fun r hr => List.mem_append_left _ hr) hφ
  have VA := disj_of_obst dV (fun r hr => List.mem_append_right _ hr) hφ
  have U2B := disj_of_obst dU2 (fun r hr => List.mem_append_left _ hr) hψ
  have V2B := disj_of_obst dV2 (fun r hr => List.mem_append_right _ hr) hψ
  obtain ⟨cX, cXUA, cS'A⟩ := cU.add_disjoint dA nA UA
  obtain ⟨cY, cYU2B, cW''B⟩ := cU2.add_disjoint dB nB U2B
  obtain ⟨cVA, cVA', cT'A⟩ := cV.add_disjoint dA nA VA
  obtain ⟨cV2B, cV2B', cT''B⟩ := cV2.add_disjoint dB nB V2B
  have eAA : KEqArea A A := KEqArea.refl dA
  have eBB : KEqArea B B := KEqArea.refl dB
  have eT'B : KEqArea T' B := KEqArea.mapI dT' ψ
  have eT''A : KEqArea T'' A := KEqArea.mapI dT'' φ
  -- the chain `U + A ~ V + A ~ V₂ + B ~ U₂ + B`
  have e1 : KEqArea (fun p => U p ∨ A p) (fun p => V p ∨ A p) :=
    KEqArea.combine cXUA cVA' eUV eAA
  have e12 : KEqArea (fun p => T' p ∨ A p) (fun p => T'' p ∨ B p) :=
    KEqArea.combine cT'A cT''B.comm eT'B eT''A.symm
  have e2 : KEqArea (fun p => V p ∨ A p) (fun p => V2 p ∨ B p) :=
    KEqArea.combine cVA cV2B (KEqArea.refl dT) e12
  have e3 : KEqArea (fun p => V2 p ∨ B p) (fun p => U2 p ∨ B p) :=
    KEqArea.combine cV2B' cYU2B eUV2.symm eBB
  have eXY : KEqArea (fun p => U p ∨ A p) (fun p => U2 p ∨ B p) :=
    KEqArea.trans (KEqArea.trans e1 e2.symm) e3.symm
  have eS'B : KEqArea S' B := KEqArea.trans eST eT'B.symm
  have eAW : KEqArea A W'' := KEqArea.trans eT''A.symm eWT
  exact ⟨_, _, _, _, cX.poly_right, cY.poly_right, KEqArea.combine cS'A cW''B.comm eS'B eAW,
    cX, cY, eXY⟩

/-! ### The measure of area -/

open Classical in
/-- Half the sum of `|D|` over a decomposition (`0` if there is none). -/
noncomputable def kmeasure (S : K × K → Prop) : K :=
  if h : ∃ l : List (Tr K), DecS S l then (h.choose.map (fun r => |r.D|)).sum / 2 else 0

theorem kmeasure_of_decS {S : K × K → Prop} {l : List (Tr K)} (h : DecS S l) :
    kmeasure S = (l.map (fun r => |r.D|)).sum / 2 := by
  have hex : ∃ l : List (Tr K), DecS S l := ⟨l, h⟩
  unfold kmeasure
  rw [dif_pos hex, decS_sum_eq hex.choose_spec h]

theorem sum_forall₂ {l m : List (Tr K)} (h : List.Forall₂ KCong l m) :
    (l.map (fun r => |r.D|)).sum = (m.map (fun r => |r.D|)).sum := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, List.sum_cons, hab.abs_D, ih]

theorem KEqArea.kmeasure_eq {S T : K × K → Prop} (h : KEqArea S T) :
    kmeasure S = kmeasure T := by
  obtain ⟨l, m, hl, hm, hc⟩ := h
  rw [kmeasure_of_decS hl, kmeasure_of_decS hm, sum_forall₂ hc]

theorem KComposed.kmeasure_eq {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) :
    kmeasure U = kmeasure S1 + kmeasure S2 := by
  obtain ⟨l1, l2, -, -, h1, h2, hU⟩ := h
  rw [kmeasure_of_decS hU, kmeasure_of_decS h1, kmeasure_of_decS h2, List.map_append,
    List.sum_append]
  ring

theorem KEqContent.kmeasure_eq {S T : K × K → Prop} (h : KEqContent S T) :
    kmeasure S = kmeasure T := by
  obtain ⟨S', T', U, V, -, -, e, cU, cV, eUV⟩ := h
  have := eUV.kmeasure_eq
  rw [cU.kmeasure_eq, cV.kmeasure_eq, e.kmeasure_eq] at this
  linarith

theorem kmeasure_pos {S : K × K → Prop} {l : List (Tr K)} (h : DecS S l) (hne : l ≠ []) :
    0 < kmeasure S := by
  rw [kmeasure_of_decS h]
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil l hne
  have hpos : 0 < |r.D| := abs_pos.2 (h.1 r hr)
  have : |r.D| ≤ (l.map (fun r => |r.D|)).sum :=
    List.single_le_sum (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _) _ (List.mem_map_of_mem hr)
  linarith

end Areas

end HilbertFoundations
