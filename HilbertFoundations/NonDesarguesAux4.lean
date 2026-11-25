import HilbertFoundations.NonDesarguesAux3

/-!
# The Moulton plane: the counterexamples (helper for `NonDesargues.lean`)

* A configuration of two triangles with respectively parallel sides whose joining lines are
  neither concurrent nor parallel (Desargues's theorem fails; § 23, Fig. 40).
* Two triangles satisfying the hypotheses of IV 6 but not its conclusion (IV 6 fails, as it must,
  since Desargues's theorem follows from the plane axioms I–IV).
-/

namespace HilbertFoundations

namespace Moulton

/-! ### Computing directions of rays -/

theorem rdir_graph_pos {m b : ℝ} {O A : Pt} (hO : O ∈ Ln.graph m b) (hA : A ∈ Ln.graph m b)
    (h : O.x < A.x) : rdir O A = (1, slopeAt m O.x) := by
  have hOA : O ≠ A := fun e => by rw [e] at h; exact lt_irrefl _ h
  have hl : lam (Ln.graph m b) O < lam (Ln.graph m b) A := lam_graph_lt.2 h
  rw [rdir_eq hO hA hOA]; simp only [rdirL, hl, ↓reduceIte]; rfl

theorem rdir_graph_neg {m b : ℝ} {O A : Pt} (hO : O ∈ Ln.graph m b) (hA : A ∈ Ln.graph m b)
    (h : A.x < O.x) : rdir O A = -(1, slopeAt m O.x) := by
  have hOA : O ≠ A := fun e => by rw [e] at h; exact lt_irrefl _ h
  have hl : ¬lam (Ln.graph m b) O < lam (Ln.graph m b) A := not_lt.2 (lam_graph_lt.2 h).le
  rw [rdir_eq hO hA hOA]; simp only [rdirL, hl, ↓reduceIte]; rfl

theorem rdir_vert_pos {c : ℝ} {O A : Pt} (hO : O.x = c) (hA : A.x = c) (h : O.y < A.y) :
    rdir O A = (0, 1) := by
  have hOA : O ≠ A := fun e => by rw [e] at h; exact lt_irrefl _ h
  have hl : lam (Ln.vert c) O < lam (Ln.vert c) A := h
  rw [rdir_eq (ℓ := Ln.vert c) hO hA hOA]; simp only [rdirL, hl, ↓reduceIte]; rfl

theorem collinear_mem {A B C : Pt} {ℓ : Ln} (hAB : A ≠ B) (hA : A ∈ ℓ) (hB : B ∈ ℓ)
    (h : Collinear A B C) : C ∈ ℓ := by
  obtain ⟨ℓ', h1, h2, h3⟩ := h
  rw [eq_of_mem hAB h1 h2 hA hB] at h3; exact h3

theorem not_meets_graph {m b b' : ℝ} (h : b ≠ b') :
    ¬Meets (Point := Pt) (Ln.graph m b) (Ln.graph m b') := by
  rintro ⟨P, h1, h2⟩; simp at h1 h2; exact h (by linarith)

/-! ### The Desargues configuration -/

/-- The vertices of the first triangle. -/
noncomputable def dA : Pt := ⟨-1, 1⟩
/-- Vertex `B = (1, 1)`. -/
noncomputable def dB : Pt := ⟨1, 1⟩
/-- Vertex `C = (2, 2)`. -/
noncomputable def dC : Pt := ⟨2, 2⟩
/-- The vertices of the second triangle (the image of the first under the ordinary homothety of
centre `(1, 0)` and ratio `2`). -/
noncomputable def dA' : Pt := ⟨-3, 2⟩
/-- Vertex `B' = (1, 2)`. -/
noncomputable def dB' : Pt := ⟨1, 2⟩
/-- Vertex `C' = (3, 4)`. -/
noncomputable def dC' : Pt := ⟨3, 4⟩

/-- The sides `BC`, `CA`, `AB` and `B'C'`, `C'A'`, `A'B'` (ordinary lines of slopes `1`, `1/3`, `0`). -/
noncomputable def la : Ln := .graph 1 0
/-- The side `CA`. -/
noncomputable def lb : Ln := .graph (1 / 3) (4 / 3)
/-- The side `AB`. -/
noncomputable def lc : Ln := .graph 0 1
/-- The side `B'C'`. -/
noncomputable def la' : Ln := .graph 1 1
/-- The side `C'A'`. -/
noncomputable def lb' : Ln := .graph (1 / 3) 3
/-- The side `A'B'`. -/
noncomputable def lc' : Ln := .graph 0 2
/-- The joining lines `AA'` (a refracted line of slope parameter `-1/2`), `BB'` (vertical),
`CC'` (an ordinary line of slope `2`). -/
noncomputable def lp : Ln := .graph (-1 / 2) (1 / 2)
/-- The joining line `BB'`. -/
noncomputable def lq : Ln := .vert 1
/-- The joining line `CC'`. -/
noncomputable def lr : Ln := .graph 2 (-2)

theorem ht_num_nonneg {m x : ℝ} (hm : 0 ≤ m) : ht m x = m * x := by
  rcases le_total x 0 with h | h
  · exact ht_of_nonpos h
  · rw [ht_of_nonneg h, tr_of_nonneg hm]

theorem ht_mhalf_neg1 : ht (-1 / 2) (-1) = 1 / 2 := by rw [ht_of_nonpos (by norm_num)]; norm_num

theorem ht_mhalf_neg3 : ht (-1 / 2) (-3) = 3 / 2 := by rw [ht_of_nonpos (by norm_num)]; norm_num

theorem ht_mhalf_one : ht (-1 / 2) 1 = -1 := by
  rw [ht_of_nonneg (by norm_num), tr_of_neg (by norm_num)]; norm_num

/-- A membership check for the configuration. -/
macro "memtac" : tactic => `(tactic| first
  | (simp only [mem_graph, dA, dB, dC, dA', dB', dC', la, lb, lc, la', lb', lc', lr]
     rw [ht_num_nonneg (by norm_num)]; norm_num)
  | (simp only [mem_graph, dA, dA', lp, ht_mhalf_neg1, ht_mhalf_neg3]; norm_num)
  | (simp only [mem_vert, dB, dB', lq]))

theorem desargues_config :
    ¬Collinear dA dB dC ∧ ¬Collinear dA' dB' dC' ∧
    dB ∈ la ∧ dC ∈ la ∧ dC ∈ lb ∧ dA ∈ lb ∧ dA ∈ lc ∧ dB ∈ lc ∧
    dB' ∈ la' ∧ dC' ∈ la' ∧ dC' ∈ lb' ∧ dA' ∈ lb' ∧ dA' ∈ lc' ∧ dB' ∈ lc' ∧
    ¬Meets (Point := Pt) la la' ∧ ¬Meets (Point := Pt) lb lb' ∧ ¬Meets (Point := Pt) lc lc' ∧
    dA ∈ lp ∧ dA' ∈ lp ∧ dB ∈ lq ∧ dB' ∈ lq ∧ dC ∈ lr ∧ dC' ∈ lr ∧
    ¬(∃ O : Pt, O ∈ lp ∧ O ∈ lq ∧ O ∈ lr) ∧ Meets (Point := Pt) lq lr := by
  refine ⟨?_, ?_, by memtac, by memtac, by memtac, by memtac, by memtac, by memtac, by memtac,
    by memtac, by memtac, by memtac, by memtac, by memtac, not_meets_graph (by norm_num),
    not_meets_graph (by norm_num), not_meets_graph (by norm_num), by memtac, by memtac, by memtac,
    by memtac, by memtac, by memtac, ?_, ?_⟩
  · intro h
    have := collinear_mem (ℓ := lc) (by norm_num [dA, dB, Pt.ext_iff]) (by memtac) (by memtac) h
    simp only [mem_graph, dC, lc] at this; rw [ht_num_nonneg (by norm_num)] at this; norm_num at this
  · intro h
    have := collinear_mem (ℓ := lc') (by norm_num [dA', dB', Pt.ext_iff]) (by memtac) (by memtac) h
    simp only [mem_graph, dC', lc'] at this; rw [ht_num_nonneg (by norm_num)] at this
    norm_num at this
  · rintro ⟨O, hp, hq, hr⟩
    simp only [lp, lq, lr, mem_graph, mem_vert] at hp hq hr
    rw [hq, ht_mhalf_one] at hp
    rw [hq, ht_num_nonneg (by norm_num)] at hr
    linarith
  · refine ⟨⟨1, 0⟩, by simp [lq], ?_⟩
    simp only [lr, mem_graph]; rw [ht_num_nonneg (by norm_num)]; norm_num

/-! ### Axiom IV 6 fails -/

/-- The first triangle, in the half-plane `x < 0` (where the geometry is ordinary). -/
noncomputable def tA : Pt := ⟨-3, 0⟩
/-- Vertex `B = (-2, 0)`. -/
noncomputable def tB : Pt := ⟨-2, 0⟩
/-- Vertex `C = (-3, 1)`. -/
noncomputable def tC : Pt := ⟨-3, 1⟩
/-- The second triangle, the ordinary translate of the first by `(5/2, 0)`: its side `B'C'` is
refracted at the `y`-axis. -/
noncomputable def tA' : Pt := ⟨-1 / 2, 0⟩
/-- Vertex `B' = (1/2, 0)`. -/
noncomputable def tB' : Pt := ⟨1 / 2, 0⟩
/-- Vertex `C' = (-1/2, 1)`. -/
noncomputable def tC' : Pt := ⟨-1 / 2, 1⟩

theorem cosV_sq (u v : ℝ × ℝ) :
    cosV u v ^ 2 = dot u v ^ 2 / ((u.1 ^ 2 + u.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2)) := by
  rw [cosV, div_pow, mul_pow, nrm_sq, nrm_sq]

theorem sL_zero : sL 0 = 1 := by simp [sL]

theorem sR_zero : sR 0 = 1 := by simp [sR, tr]

theorem lam_graph_zero (b : ℝ) (P : Pt) : lam (Ln.graph 0 b) P = P.x := by
  simp only [lam, ulen, sL_zero, sR_zero, one_mul]
  have := min_add_max P.x 0; linarith

theorem not_axiomIV6_config :
    IsTriangle tA tB tC ∧ IsTriangle tA' tB' tC' ∧ SegCong tA tB tA' tB' ∧
    SegCong tA tC tA' tC' ∧ AngCong tB tA tC tB' tA' tC' ∧ ¬AngCong tA tB tC tA' tB' tC' := by
  have hAB : tA ∈ Ln.graph 0 0 := by simp [tA, ht]
  have hBB : tB ∈ Ln.graph 0 0 := by simp [tB, ht]
  have hAB' : tA' ∈ Ln.graph 0 0 := by simp [tA', ht]
  have hBB' : tB' ∈ Ln.graph 0 0 := by simp [tB', ht]
  have hAC : tA ∈ Ln.vert (-3) := by simp [tA]
  have hCC : tC ∈ Ln.vert (-3) := by simp [tC]
  have hAC' : tA' ∈ Ln.vert (-1 / 2) := by simp [tA']
  have hCC' : tC' ∈ Ln.vert (-1 / 2) := by simp [tC']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := collinear_mem (by norm_num [tA, tC, Pt.ext_iff]) hAC hCC h.swap23
    norm_num [tB] at this
  · intro h
    have := collinear_mem (by norm_num [tA', tC', Pt.ext_iff]) hAC' hCC' h.swap23
    norm_num [tB'] at this
  · rw [segCong_iff, segLen_eq hAB hBB, segLen_eq hAB' hBB', lam_graph_zero, lam_graph_zero,
      lam_graph_zero, lam_graph_zero]
    simp [tA, tB, tA', tB']; norm_num
  · rw [segCong_iff, segLen_eq hAC hCC, segLen_eq hAC' hCC']
    simp [lam, tA, tC, tA', tC']
  · rw [angCong_iff, angM, angM, rdir_graph_pos hAB hBB (by simp [tA, tB]; norm_num),
      rdir_vert_pos hAC hCC (by simp [tA, tC]),
      rdir_graph_pos hAB' hBB' (by simp [tA', tB']; norm_num),
      rdir_vert_pos hAC' hCC' (by simp [tA', tC'])]
    norm_num [slopeAt, tA, tA']
  · rw [angCong_iff, angM_eq_iff]
    have hBC : tB ∈ Ln.graph (-1) (-2) := by
      simp [tB]; rw [ht_of_nonpos (by norm_num)]; norm_num
    have hCC2 : tC ∈ Ln.graph (-1) (-2) := by
      simp [tC]; rw [ht_of_nonpos (by norm_num)]; norm_num
    have hBC' : tB' ∈ Ln.graph (-2 / 3) (2 / 3) := by
      simp [tB']; rw [ht_of_nonneg (by norm_num), tr_of_neg (by norm_num)]; norm_num
    have hCC2' : tC' ∈ Ln.graph (-2 / 3) (2 / 3) := by
      simp [tC']; rw [ht_of_nonpos (by norm_num)]; norm_num
    rw [rdir_graph_neg hBB hAB (by simp [tA, tB]; norm_num),
      rdir_graph_neg hBC hCC2 (by simp [tB, tC]; norm_num),
      rdir_graph_neg hBB' hAB' (by simp [tA', tB']; norm_num),
      rdir_graph_neg hBC' hCC2' (by simp [tB', tC']; norm_num)]
    have s1 : slopeAt 0 tB.x = 0 := by simp [slopeAt, tB]
    have s2 : slopeAt (-1) tB.x = -1 := by simp [slopeAt, tB]
    have s3 : slopeAt 0 tB'.x = 0 := by simp [slopeAt, tB', tr]
    have s4 : slopeAt (-2 / 3) tB'.x = -4 / 3 := by
      have : ¬tB'.x < 0 := by norm_num [tB']
      simp only [slopeAt, this, ↓reduceIte]; rw [tr_of_neg (by norm_num)]; norm_num
    rw [s1, s2, s3, s4]
    intro h
    have := congrArg (· ^ 2) h
    simp only [cosV_sq, dot] at this
    norm_num at this

end Moulton

end HilbertFoundations
