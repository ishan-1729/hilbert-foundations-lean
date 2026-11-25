import HilbertFoundations.NonPascalAux

/-!
# Helper for §§ 31–35: Pascal's theorem and the commutative law; Theorems 36 and 37

Helper module of `NonPascal.lean` (the units are stated there). Contents:

* `PascalTheorem P`: Pascal's theorem (Theorem 21 of § 14) as a proposition about a plane
  geometry, stated with Hilbert's (strict) parallels `ParPts` of `DesarguesAlgebra.lean`.
* `CentreComm P`: any two dilatations with the same centre commute.
* `pascal_of_centreComm`, `centreComm_of_pascal`: in a plane with I 1–2, II 1–4, III and the second
  part of Desargues's theorem, Pascal's theorem holds iff dilatations with a common centre commute
  (the configuration of Pascal's theorem is the composition of two such dilatations).
* `pascal_iff_law12`: hence Pascal's theorem holds iff the multiplication of Hilbert's segments
  (§ 24) is commutative for every frame (§ 34: "the commutative law of multiplication is here
  nothing else than Pascal's theorem").
* `TrEqual`: segments "equal" by a translation (the constructions of § 24, from I and III);
  `law17_seg`: Archimedes's axiom with this equality gives law 17 for the segments;
  `theorem36_plane`, `theorem36_space`: Theorem 36.
* The coordinate space over a non-commutative ordered division ring: `not_pascal_of_noncomm`
  (Pascal's theorem fails in a plane); with `Ω(s, t)`, Theorem 37.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations
namespace NonPascal

open DesAlg

universe u v w

/-! ## Pascal's theorem as a proposition -/

/-- **Pascal's theorem** (Theorem 21, § 14): for points `A, B, C` (pairwise distinct) on a line `g`
and `A', B', C'` on a line `h ≠ g`, none of them at the intersection `O` of `g` and `h`: if `CB'` is
parallel to `BC'` and `CA'` to `AC'`, then `BA'` is parallel to `AB'` (parallel: lines without
common point, `ParPts`). -/
def PascalTheorem (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  ∀ (g h : L) (O A B C A' B' C' : P), g ≠ h → O ∈ g → O ∈ h →
    A ∈ g → B ∈ g → C ∈ g → A' ∈ h → B' ∈ h → C' ∈ h →
    A ≠ O → B ≠ O → C ≠ O → A' ≠ O → B' ≠ O → C' ≠ O → A ≠ B → B ≠ C → A ≠ C →
    ParPts (L := L) C B' B C' → ParPts (L := L) C A' A C' → ParPts (L := L) B A' A B'

section Affine

variable {P : Type u} {L : Type v} [HasLines P L]

/-- **Any two dilatations with the same centre `O` commute.** -/
def CentreComm (P : Type u) {L : Type v} [HasLines P L] [PlaneParallels P L] [Nonempty L] :
    Prop :=
  ∀ (O : P) (f g : P → P), IsDil (L := L) f → IsDil (L := L) g → f O = O → g O = O →
    f ∘ g = g ∘ f

/-- **Segments equal in the sense of § 24**: a translation (built from parallels alone, groups I
and III) carries `A` to `A'` and `B` to `B'`. -/
def TrEqual (L : Type v) [HasLines P L] [PlaneParallels P L] [Nonempty L] (A B A' B' : P) :
    Prop :=
  ∃ τ : P → P, IsTr (L := L) τ ∧ τ A = A' ∧ τ B = B'

variable [PlaneParallels P L] [Nonempty L]

/-- A point of `g` other than the common point `O` of two lines `g ≠ h` is not on `h`. -/
theorem not_mem_of_ne {g h : L} {O X : P} (hgh : g ≠ h) (hOg : O ∈ g) (hOh : O ∈ h)
    (hXg : X ∈ g) (hXO : X ≠ O) : X ∉ h := fun hXh =>
  hgh (line_unique hXO hXg hOg hXh hOh)

/-- The point of `h` on a parallel `pline l X` (when `l` meets `h` and is not `h`). -/
theorem eq_on_pline {l h : L} {X Y Z W : P} (hYl : Y ∈ l) (hYh : Y ∈ h) (hlh : l ≠ h)
    (hZ : Z ∈ pline l X) (hZh : Z ∈ h) (hW : W ∈ pline l X) (hWh : W ∈ h) : Z = W :=
  eq_of_mem_not_lpar (not_lpar_pline_left (not_lpar_of hYl hYh hlh) X) hZ hZh hW hWh

variable [HasBetween P] [LineOrder P L]

/-- **Commuting dilatations give Pascal's theorem.** For `δ : C ↦ B` and `ε : C ↦ A` with centre
`O`, the hypotheses say `δ B' = C'` and `ε A' = C'`; then `ε δ⁻¹` maps `B ↦ A` and `A' ↦ B'`. -/
theorem pascal_of_centreComm (hD : DesarguesII P) (hc : CentreComm P (L := L)) :
    PascalTheorem P (L := L) := by
  intro g h O A B C A' B' C' hgh hOg hOh hAg hBg hCg hA'h hB'h hC'h hAO hBO hCO hA'O hB'O hC'O
    hAB hBC hAC h1 h2
  have hCh := not_mem_of_ne hgh hOg hOh hCg hCO
  have hBh := not_mem_of_ne hgh hOg hOh hBg hBO
  have hA'g := not_mem_of_ne hgh.symm hOh hOg hA'h hA'O
  have hlnOC : (ln O C : L) = g := ln_eq hCO.symm hOg hCg
  obtain ⟨δ, hδ, hδO, hδC⟩ := exists_cdil hD hCO hBO (by rw [hlnOC]; exact hBg)
  obtain ⟨ε, hε, hεO, hεC⟩ := exists_cdil hD hCO hAO (by rw [hlnOC]; exact hAg)
  have hCB' : C ≠ B' := fun e => hCh (e ▸ hB'h)
  have hCA' : C ≠ A' := fun e => hCh (e ▸ hA'h)
  have hBA' : B ≠ A' := fun e => hBh (e ▸ hA'h)
  -- `δ B' = C'`
  have hδB' : δ B' = C' := by
    have m := hδ C B' hCB'
    rw [hδC] at m
    exact eq_on_pline (mem_ln_right C B') hB'h (fun e => hCh (e ▸ mem_ln_left C B')) m
      (hδ.mem_of_fix hδO hOh hB'h) (mem_pline_of_parPts h1 hCB') hC'h
  -- `ε A' = C'`
  have hεA' : ε A' = C' := by
    have m := hε C A' hCA'
    rw [hεC] at m
    exact eq_on_pline (mem_ln_right C A') hA'h (fun e => hCh (e ▸ mem_ln_left C A')) m
      (hε.mem_of_fix hεO hOh hA'h) (mem_pline_of_parPts h2 hCA') hC'h
  obtain ⟨δ', hδ', hδ'O, hδ'δ, hδδ'⟩ := cdil_inv hD hδ hδO hCO (by rw [hδC]; exact hBO)
  have k1 := congrFun hδ'δ
  have k2 := congrFun hδδ'
  simp only [Function.comp, id] at k1 k2
  have hcomm := congrFun (hc O ε δ hε hδ hεO hδO)
  simp only [Function.comp] at hcomm
  -- `δ'` and `ε` commute
  have hcomm' : ∀ Z, ε (δ' Z) = δ' (ε Z) := fun Z => by
    have := hcomm (δ' Z)
    rw [k2] at this
    rw [← k1 (ε (δ' Z)), ← this]
  have hφB : ε (δ' B) = A := by rw [← hδC, k1, hεC]
  have hφA' : ε (δ' A') = B' := by rw [hcomm', hεA', ← hδB', k1]
  have hmem : B' ∈ pline (ln B A' : L) A := by
    have := (hε.comp hδ') B A' hBA'
    simp only [Function.comp] at this
    rwa [hφB, hφA'] at this
  refine parPts_of hBA' (fun hA => hA'g ?_) hmem
  have e : (ln B A' : L) = g := line_unique hAB.symm (mem_ln_left B A') hA hBg hAg
  rw [← e]; exact mem_ln_right B A'

/-- **Pascal's theorem gives commuting dilatations.** -/
theorem centreComm_of_pascal (hD : DesarguesII P) (hP : PascalTheorem P (L := L)) :
    CentreComm P (L := L) := by
  intro O f g hf hg hfO hgO
  -- constant dilatations
  by_cases hfc : ∃ X, X ≠ O ∧ f X = O
  · obtain ⟨X, hXO, hfX⟩ := hfc
    have e := hf.eq_const (Ne.symm hXO) (hfO.trans hfX.symm)
    have e' : ∀ Z, f Z = O := fun Z => (congrFun e Z).trans hfO
    funext Z
    simp only [Function.comp, e', hgO]
  by_cases hgc : ∃ X, X ≠ O ∧ g X = O
  · obtain ⟨X, hXO, hgX⟩ := hgc
    have e := hg.eq_const (Ne.symm hXO) (hgO.trans hgX.symm)
    have e' : ∀ Z, g Z = O := fun Z => (congrFun e Z).trans hgO
    funext Z
    simp only [Function.comp, e', hfO]
  push Not at hfc hgc
  obtain ⟨C, hCO⟩ := exists_other (L := L) O
  obtain ⟨A', hA'⟩ := exists_not_mem' (P := P) (ln O C : L)
  have hA'O : A' ≠ O := fun e => hA' (e ▸ mem_ln_left O C)
  set g0 : L := ln O C with hg0
  set h0 : L := ln O A' with hh0
  have hOg : O ∈ g0 := mem_ln_left O C
  have hCg : C ∈ g0 := mem_ln_right O C
  have hOh : O ∈ h0 := mem_ln_left O A'
  have hA'h : A' ∈ h0 := mem_ln_right O A'
  have hgh : g0 ≠ h0 := fun e => hA' (e ▸ hA'h)
  have hBg : f C ∈ g0 := hf.mem_of_fix hfO hOg hCg
  have hAg : g C ∈ g0 := hg.mem_of_fix hgO hOg hCg
  -- trivial cases
  by_cases hAB : g C = f C
  · rw [dil_eq_of_two hf hg hCO.symm (hfO.trans hgO.symm) hAB.symm]
  by_cases hBC : f C = C
  · rw [hf.eq_id hCO.symm hfO hBC]; rfl
  by_cases hAC : g C = C
  · rw [hg.eq_id hCO.symm hgO hAC]; rfl
  have hBO := hfc C hCO
  have hAO := hgc C hCO
  obtain ⟨δ', hδ', hδ'O, hδ'δ, hδδ'⟩ := cdil_inv hD hf hfO hCO hBO
  have k1 := congrFun hδ'δ
  have k2 := congrFun hδδ'
  simp only [Function.comp, id] at k1 k2
  set C' := g A' with hC'
  set B' := δ' C' with hB'
  have hC'h : C' ∈ h0 := hg.mem_of_fix hgO hOh hA'h
  have hB'h : B' ∈ h0 := hδ'.mem_of_fix hδ'O hOh hC'h
  have hC'O : C' ≠ O := hgc A' hA'O
  have hB'O : B' ≠ O := fun e => hC'O (by rw [← k2 C', ← hB', e, hfO])
  have hCh := not_mem_of_ne hgh hOg hOh hCg hCO
  have hBh := not_mem_of_ne hgh hOg hOh hBg hBO
  have hAh := not_mem_of_ne hgh hOg hOh hAg hAO
  have hCB' : C ≠ B' := fun e => hCh (e ▸ hB'h)
  have hCA' : C ≠ A' := fun e => hCh (e ▸ hA'h)
  have hBA' : f C ≠ A' := fun e => hBh (e ▸ hA'h)
  have hB'g := not_mem_of_ne hgh.symm hOh hOg hB'h hB'O
  have hA'g := not_mem_of_ne hgh.symm hOh hOg hA'h hA'O
  -- the two hypotheses of Pascal's theorem
  have hp1 : ParPts (L := L) C B' (f C) C' := by
    refine parPts_of hCB' (fun hm => hB'g ?_) ?_
    · have e : (ln C B' : L) = g0 := line_unique hBC hm (mem_ln_left C B') hBg hCg
      rw [← e]; exact mem_ln_right C B'
    · have := hf C B' hCB'
      rwa [hB', k2] at this
  have hp2 : ParPts (L := L) C A' (g C) C' := by
    refine parPts_of hCA' (fun hm => hA'g ?_) (hg C A' hCA')
    have e : (ln C A' : L) = g0 := line_unique hAC hm (mem_ln_left C A') hAg hCg
    rw [← e]; exact mem_ln_right C A'
  have hp := hP g0 h0 O (g C) (f C) C A' B' C' hgh hOg hOh hAg hBg hCg hA'h hB'h hC'h hAO hBO
    hCO hA'O hB'O hC'O hAB (Ne.symm hBC |>.symm) hAC hp1 hp2
  have hmem : B' ∈ pline (ln (f C) A' : L) (g C) := mem_pline_of_parPts hp hBA'
  -- `g δ'` and `δ' g` agree on `O` and `A'`
  have hφ : g (δ' A') = δ' (g A') := by
    have m := (hg.comp hδ') (f C) A' hBA'
    simp only [Function.comp] at m
    rw [k1] at m
    exact eq_on_pline (mem_ln_right (f C) A') hA'h
      (fun e => hBh (e ▸ mem_ln_left (f C) A')) m
      ((hg.comp hδ').mem_of_fix (by simp [hδ'O, hgO]) hOh hA'h) hmem hB'h
  have heq : g ∘ δ' = δ' ∘ g := dil_eq_of_two (hg.comp hδ') (hδ'.comp hg) hA'O.symm
    (by simp [hδ'O, hgO]) (by simpa using hφ)
  funext Z
  have := congrFun heq (f Z)
  simp only [Function.comp, k1] at this ⊢
  rw [this, k2]

/-- A frame with a given origin. -/
theorem exists_frame_at (O : P) : ∃ F : Frame P, F.O = O := by
  obtain ⟨E, hE⟩ := exists_other (L := L) O
  obtain ⟨E', hE'⟩ := exists_not_mem' (P := P) (ln O E : L)
  exact ⟨⟨O, E, E', Ne.symm hE, fun h => hE' ((collinear_iff_mem_ln (Ne.symm hE)).1 h)⟩, rfl⟩

/-- A dilatation with centre `O` (of a frame) is `dl O E t` with `t` its image of `E`. -/
theorem eq_dl (hD : DesarguesII P) (F : Frame P) {f : P → P} (hf : IsDil (L := L) f)
    (hO : f F.O = F.O) : f = dl (L := L) F.O F.E (f F.E) :=
  dl_eq_of hD F.hOE (hf.mem_of_fix hO (mem_ln_left F.O F.E) (mem_ln_right F.O F.E)) hf hO rfl

/-- **The commutative law for the segments of a frame is the commutativity of the dilatations
with centre `O`.** -/
theorem law12_iff (hD : DesarguesII P) (F : Frame P) :
    Law12 (DesAlg.Seg F) ↔ ∀ f g : P → P, IsDil (L := L) f → IsDil (L := L) g → f F.O = F.O →
      g F.O = F.O → f ∘ g = g ∘ f := by
  constructor
  · intro h f g hf hg hfO hgO
    have hs : f F.E ∈ (F.xl : L) := hf.mem_of_fix hfO F.O_xl F.E_xl
    have ht : g F.E ∈ (F.xl : L) := hg.mem_of_fix hgO F.O_xl F.E_xl
    have e := congrArg Seg.pt (h ⟨g F.E, ht⟩ ⟨f F.E, hs⟩)
    rw [Seg.mul_pt, Seg.mul_pt, hmulPt_eq hD F ht hs, hmulPt_eq hD F hs ht] at e
    rw [eq_dl hD F hf hfO, eq_dl hD F hg hgO, dl_comp hD F ht hs, dl_comp hD F hs ht, e]
  · intro h a b
    apply Seg.ext
    rw [Seg.mul_pt, Seg.mul_pt, hmulPt_eq hD F a.mem b.mem, hmulPt_eq hD F b.mem a.mem]
    have := congrFun (h _ _ (dl_isDil hD F b.mem) (dl_isDil hD F a.mem) (dl_O hD F b.mem)
      (dl_O hD F a.mem)) F.E
    simp only [Function.comp, dl_at_E hD F a.mem, dl_at_E hD F b.mem] at this
    exact this

/-- **Pascal's theorem holds iff the multiplication of the segments is commutative** (for every
frame; § 34). -/
theorem pascal_iff_law12 (hD : DesarguesII P) :
    PascalTheorem P (L := L) ↔ ∀ F : Frame P, Law12 (DesAlg.Seg F) := by
  constructor
  · intro hP F
    exact (law12_iff hD F).2 fun f g hf hg hfO hgO => centreComm_of_pascal hD hP F.O f g hf hg hfO hgO
  · intro h
    refine pascal_of_centreComm hD fun O f g hf hg hfO hgO => ?_
    obtain ⟨F, rfl⟩ := exists_frame_at (L := L) O
    exact (law12_iff hD F).1 (h F) f g hf hg hfO hgO

end Affine

/-! ## Theorem 36 -/

section Theorem36

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L]

/-- **Archimedes's axiom with the equality of § 24 gives law 17 for the segments** (§ 34:
"evidently Archimedes's theorem … also holds for our algebra of segments"). -/
theorem law17_seg [hDF : Fact (DesarguesII P)] (F : Frame P)
    (hV : ArchimedesWith P (TrEqual (P := P) L)) : Law17 (DesAlg.Seg F) := by
  intro y x hy hx
  rw [gt_iff_lt] at hy hx
  simp only [gt_iff_lt]
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact ⟨0, by rw [repeatAdd_eq_nsmul]; simpa using hxy⟩
  · refine ⟨1, ?_⟩
    rw [repeatAdd_eq_nsmul, show (1 + 1 : ℕ) = 2 from rfl, two_nsmul]
    exact lt_add_of_pos_right _ hy
  set A : ℕ → P := fun k => (k • y).pt with hAdef
  have hlt : ∀ k : ℕ, k • y < (k + 1) • y := fun k => by
    rw [succ_nsmul]; exact lt_add_of_pos_right _ hy
  have hne : ∀ {a b : DesAlg.Seg F}, a < b → a ≠ b := fun h => ne_of_lt h
  have hbet1 : Between (A 0) (A 1) x.pt := by
    have h01 : (0 • y : DesAlg.Seg F) < 1 • y := hlt 0
    have h1x : (1 • y : DesAlg.Seg F) < x := by rwa [one_nsmul]
    exact (Seg.between_iff (hne h01) (hne (h01.trans h1x)) (hne h1x)).2 (Or.inl ⟨h01, h1x⟩)
  have hbet2 : ∀ k : ℕ, Between (A k) (A (k + 1)) (A (k + 2)) := fun k => by
    have a1 := hlt k
    have a2 := hlt (k + 1)
    exact (Seg.between_iff (hne a1) (hne (a1.trans a2)) (hne a2)).2 (Or.inl ⟨a1, a2⟩)
  have heq : ∀ m n : ℕ, TrEqual (P := P) L (A m) (A (m + 1)) (A n) (A (n + 1)) := fun m n => by
    refine ⟨trf (L := L) F.O (n • y - m • y).pt, trf_isTr hDF.out F.O _, ?_, ?_⟩
    · show trf F.O (n • y - m • y).pt (m • y).pt = (n • y).pt
      rw [← Seg.add_pt']; congr 1; abel
    · show trf F.O (n • y - m • y).pt ((m + 1) • y).pt = ((n + 1) • y).pt
      rw [← Seg.add_pt']; congr 1; rw [succ_nsmul, succ_nsmul]; abel
  obtain ⟨k, hk⟩ := hV A x.pt hbet1 hbet2 heq
  have hk0 : A 0 = (0 : DesAlg.Seg F).pt := by simp [hAdef]
  have hxA0 : (0 : DesAlg.Seg F) ≠ x := (hne hx)
  have hd1 : (0 • y : DesAlg.Seg F) ≠ x := by rw [zero_smul]; exact hxA0
  have hd2 : (0 • y : DesAlg.Seg F) ≠ k • y := fun e => ne13_of_between hk (by rw [hAdef]; simp only; rw [e])
  have hd3 : x ≠ k • y := fun e => ne23_of_between hk (by rw [hAdef]; simp only; rw [e])
  rcases (Seg.between_iff hd1 hd2 hd3).1 hk with ⟨-, h2⟩ | ⟨-, h2⟩
  · cases k with
    | zero => exact absurd rfl hd2
    | succ j => exact ⟨j, by rw [repeatAdd_eq_nsmul]; exact h2⟩
  · rw [zero_smul] at h2; exact absurd (h2.trans hx) (lt_irrefl _)

/-- **Theorem 36** (plane form): in a plane geometry with I 1–2, II, III, in which the second part
of Desargues's theorem holds and Archimedes's axiom holds for the equality of segments of § 24,
Pascal's theorem holds. -/
theorem theorem36_plane (hD : DesarguesII P) (hV : ArchimedesWith P (TrEqual (P := P) L)) :
    PascalTheorem P (L := L) := by
  refine (pascal_iff_law12 hD).2 fun F => ?_
  have : Fact (DesarguesII P) := ⟨hD⟩
  obtain ⟨hdns, hasymm⟩ := seg_dns hD F
  exact theorem38_laws hdns hasymm (law17_seg F hV)

end Theorem36

/-- **Theorem 36** (space form): in a space geometry with I, II, III, Pascal's theorem holds in
every plane in which Archimedes's axiom holds (for the equality of segments of § 24 in that
plane). -/
theorem theorem36_space {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [SpaceOrder P L Pl] [SpaceParallels P L Pl] (α : Pl) :
    haveI := nonempty_lines_of_plane (P := P) (L := L) α
    ArchimedesWith {A : P // A ∈ α} (TrEqual (P := {A : P // A ∈ α})
      {a : L // LiesInPlane (Point := P) a α}) →
      PascalTheorem {A : P // A ∈ α} (L := {a : L // LiesInPlane (Point := P) a α}) := by
  have := nonempty_lines_of_plane (P := P) (L := L) α
  exact fun hV => theorem36_plane (first_part_of_second.1 (planes_of_space_desarguesian α)) hV


/-! ## Pascal's theorem fails over a non-commutative division ring -/

section Coordinates

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The point `(x, y, 0)` of the coordinate space. -/
def p3 (x y : K) : Coord K 3 := AffPt.ofV ![x, y, 0]

theorem p3_inj {x y x' y' : K} : p3 x y = p3 x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h0 := congrFun (congrArg AffPt.toV h) 0
    have h1 := congrFun (congrArg AffPt.toV h) 1
    simp only [p3, AffPt.toV_ofV, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem p3_line (r x₁ y₁ x₂ y₂ : K) :
    r • (p3 x₂ y₂ - p3 x₁ y₁) + p3 x₁ y₁ = p3 (r * (x₂ - x₁) + x₁) (r * (y₂ - y₁) + y₁) := by
  apply AffPt.toV_injective
  funext i
  fin_cases i <;> simp [p3]

theorem mem_through_p3 {x₁ y₁ x₂ y₂ : K} (h : p3 x₁ y₁ ≠ p3 x₂ y₂) {X : Coord K 3} :
    X ∈ AffLine.through (p3 x₁ y₁) (p3 x₂ y₂) h ↔
      ∃ r : K, X = p3 (r * (x₂ - x₁) + x₁) (r * (y₂ - y₁) + y₁) := by
  rw [AffLine.mem_through_iff]
  simp only [p3_line]

/-- `ParPts` in a plane `α` of space, from two lines of space through the points without common
point. -/
theorem parPts_restrict {α : CoordPlane K 3} {X₁ X₂ Y₁ Y₂ : Coord K 3} (h₁ : X₁ ≠ X₂) (h₂ : Y₁ ≠ Y₂)
    (hX₁ : X₁ ∈ α) (hX₂ : X₂ ∈ α) (hY₁ : Y₁ ∈ α) (hY₂ : Y₂ ∈ α)
    (hno : ∀ Z, Z ∈ AffLine.through X₁ X₂ h₁ → Z ∈ AffLine.through Y₁ Y₂ h₂ → False) :
    ParPts (L := {a : CoordLine K 3 // LiesInPlane (Point := Coord K 3) a α})
      (⟨X₁, hX₁⟩ : {X : Coord K 3 // X ∈ α}) ⟨X₂, hX₂⟩ ⟨Y₁, hY₁⟩ ⟨Y₂, hY₂⟩ := by
  refine ⟨⟨AffLine.through X₁ X₂ h₁, liesInPlane_of_mem h₁ (AffLine.left_mem_through h₁)
      (AffLine.right_mem_through h₁) hX₁ hX₂⟩,
    ⟨AffLine.through Y₁ Y₂ h₂, liesInPlane_of_mem h₂ (AffLine.left_mem_through h₂)
      (AffLine.right_mem_through h₂) hY₁ hY₂⟩,
    AffLine.left_mem_through h₁, AffLine.right_mem_through h₁, AffLine.left_mem_through h₂,
    AffLine.right_mem_through h₂, ?_⟩
  rintro ⟨Z, hZ1, hZ2⟩
  exact hno Z.1 hZ1 hZ2

/-- Not `ParPts` in a plane `α` of space, from a common point of the two lines of space. -/
theorem not_parPts_restrict {α : CoordPlane K 3} {X₁ X₂ Y₁ Y₂ : Coord K 3} (h₁ : X₁ ≠ X₂)
    (h₂ : Y₁ ≠ Y₂) (hX₁ : X₁ ∈ α) (hX₂ : X₂ ∈ α) (hY₁ : Y₁ ∈ α) (hY₂ : Y₂ ∈ α) (Z : Coord K 3)
    (hZ1 : Z ∈ AffLine.through X₁ X₂ h₁) (hZ2 : Z ∈ AffLine.through Y₁ Y₂ h₂) :
    ¬ParPts (L := {a : CoordLine K 3 // LiesInPlane (Point := Coord K 3) a α})
      (⟨X₁, hX₁⟩ : {X : Coord K 3 // X ∈ α}) ⟨X₂, hX₂⟩ ⟨Y₁, hY₁⟩ ⟨Y₂, hY₂⟩ := by
  rintro ⟨a, b, ha1, ha2, hb1, hb2, hn⟩
  have ea : a.1 = AffLine.through X₁ X₂ h₁ := AffLine.eq_through a.1 h₁ ha1 ha2
  have eb : b.1 = AffLine.through Y₁ Y₂ h₂ := AffLine.eq_through b.1 h₂ hb1 hb2
  have hZa : Z ∈ a.1 := by rw [ea]; exact hZ1
  have hZb : Z ∈ b.1 := by rw [eb]; exact hZ2
  exact hn ⟨⟨Z, a.2 Z hZa⟩, hZa, hZb⟩

/-- **Pascal's theorem fails in a plane of the coordinate space over a non-commutative ordered
division ring** (the configuration: `O = (0,0)`, `C = (1,0)`, `A = (u,0)`, `B = (v,0)`,
`A' = (0,1)`, `C' = (0,u)`, `B' = (0,v⁻¹u)` in the plane `z = 0`, scalars acting on the left). -/
theorem not_pascal_of_noncomm {u v : K} (huv : u * v ≠ v * u) :
    ∃ α : CoordPlane K 3, ¬PascalTheorem {X : Coord K 3 // X ∈ α}
      (L := {a : CoordLine K 3 // LiesInPlane (Point := Coord K 3) a α}) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at huv
  have hv0 : v ≠ 0 := by rintro rfl; simp at huv
  have hu1 : u ≠ 1 := by rintro rfl; simp at huv
  have hv1 : v ≠ 1 := by rintro rfl; simp at huv
  have huv' : u ≠ v := by rintro rfl; exact huv rfl
  have hne : ∀ {x y x' y' : K}, (x ≠ x' ∨ y ≠ y') → p3 x y ≠ p3 x' y' := fun h e =>
    h.elim (fun h' => h' (p3_inj.1 e).1) (fun h' => h' (p3_inj.1 e).2)
  -- the points
  set O : Coord K 3 := p3 0 0
  set C : Coord K 3 := p3 1 0
  set A : Coord K 3 := p3 u 0
  set B : Coord K 3 := p3 v 0
  set A' : Coord K 3 := p3 0 1
  set C' : Coord K 3 := p3 0 u
  set B' : Coord K 3 := p3 0 (v⁻¹ * u)
  have hOC : O ≠ C := hne (Or.inl zero_ne_one)
  have hOA' : O ≠ A' := hne (Or.inr zero_ne_one)
  set g := AffLine.through O C hOC
  set h := AffLine.through O A' hOA'
  have mg : ∀ x : K, p3 x 0 ∈ g := fun x => (mem_through_p3 hOC).2 ⟨x, by simp⟩
  have mh : ∀ y : K, p3 0 y ∈ h := fun y => (mem_through_p3 hOA').2 ⟨y, by simp⟩
  have hnc : ¬Collinear O C A' := by
    rintro ⟨l, hO, hC, hA'⟩
    have hA'g : A' ∈ g := by
      have := hA'
      rw [AffLine.eq_through l hOC hO hC] at this
      exact this
    obtain ⟨r, hr⟩ := (mem_through_p3 hOC).1 hA'g
    have := (p3_inj.1 hr).2
    simp at this
  obtain ⟨α, hOα, hCα, hA'α⟩ := exists_plane hnc
  have hg : LiesInPlane (Point := Coord K 3) g α :=
    liesInPlane_of_mem hOC (AffLine.left_mem_through hOC) (AffLine.right_mem_through hOC) hOα hCα
  have hh : LiesInPlane (Point := Coord K 3) h α :=
    liesInPlane_of_mem hOA' (AffLine.left_mem_through hOA') (AffLine.right_mem_through hOA') hOα hA'α
  have ag : ∀ x : K, p3 x 0 ∈ α := fun x => hg _ (mg x)
  have ah : ∀ y : K, p3 0 y ∈ α := fun y => hh _ (mh y)
  refine ⟨α, fun hP => ?_⟩
  have hgh : (⟨g, hg⟩ : {a : CoordLine K 3 // LiesInPlane (Point := Coord K 3) a α}) ≠ ⟨h, hh⟩ :=
    fun e => hnc ⟨g, AffLine.left_mem_through hOC, AffLine.right_mem_through hOC, by
      have : g = h := congrArg Subtype.val e
      rw [this]; exact AffLine.right_mem_through hOA'⟩
  have hsub : ∀ {X Y : Coord K 3} {hX : X ∈ α} {hY : Y ∈ α}, X ≠ Y →
      (⟨X, hX⟩ : {X : Coord K 3 // X ∈ α}) ≠ ⟨Y, hY⟩ := fun h e => h (congrArg Subtype.val e)
  have hvu : v⁻¹ * u ≠ 0 := mul_ne_zero (inv_ne_zero hv0) hu0
  -- the first hypothesis: `CB' ∥ BC'`
  have hCB' : C ≠ B' := hne (Or.inl one_ne_zero)
  have hBC' : B ≠ C' := hne (Or.inl hv0)
  have hp1 := parPts_restrict (α := α) hCB' hBC' (ag 1) (ah _) (ag v) (ah u) fun Z hZ1 hZ2 => by
    obtain ⟨r, rfl⟩ := (mem_through_p3 hCB').1 hZ1
    obtain ⟨q, hq⟩ := (mem_through_p3 hBC').1 hZ2
    obtain ⟨e1, e2⟩ := p3_inj.1 hq
    simp only [sub_zero, add_zero, zero_sub, mul_neg, mul_one] at e1 e2
    have e3 : r * v⁻¹ = q := mul_right_cancel₀ hu0 (by rw [mul_assoc]; exact e2)
    rw [← e3, mul_assoc, inv_mul_cancel₀ hv0, mul_one] at e1
    exact hv1 (add_left_cancel e1).symm
  -- the second hypothesis: `CA' ∥ AC'`
  have hCA' : C ≠ A' := hne (Or.inl one_ne_zero)
  have hAC' : A ≠ C' := hne (Or.inl hu0)
  have hp2 := parPts_restrict (α := α) hCA' hAC' (ag 1) (ah 1) (ag u) (ah u) fun Z hZ1 hZ2 => by
    obtain ⟨r, rfl⟩ := (mem_through_p3 hCA').1 hZ1
    obtain ⟨q, hq⟩ := (mem_through_p3 hAC').1 hZ2
    obtain ⟨e1, e2⟩ := p3_inj.1 hq
    simp only [sub_zero, add_zero, zero_sub, mul_neg, mul_one] at e1 e2
    rw [e2] at e1
    exact hu1 (add_left_cancel e1).symm
  -- the conclusion fails: `BA'` and `AB'` meet
  have hBA' : B ≠ A' := hne (Or.inl hv0)
  have hAB' : A ≠ B' := hne (Or.inl hu0)
  set w := u - v⁻¹ * u * v with hw
  have hw0 : w ≠ 0 := by
    intro h0
    apply huv
    have e : u = v⁻¹ * u * v := sub_eq_zero.1 h0
    calc u * v = v * (v⁻¹ * u * v) := by rw [mul_assoc v⁻¹, mul_inv_cancel_left₀ hv0]
      _ = v * u := by rw [← e]
  set q := (u - v) * w⁻¹ with hq
  have hqw : q * w = u - v := by rw [hq, mul_assoc, inv_mul_cancel₀ hw0, mul_one]
  have hZ2 : p3 (q * (0 - u) + u) (q * (v⁻¹ * u - 0) + 0) ∈ AffLine.through A B' hAB' :=
    (mem_through_p3 hAB').2 ⟨q, rfl⟩
  have hZ1 : p3 (q * (0 - u) + u) (q * (v⁻¹ * u - 0) + 0) ∈ AffLine.through B A' hBA' := by
    refine (mem_through_p3 hBA').2 ⟨q * (v⁻¹ * u), p3_inj.2 ⟨?_, by simp⟩⟩
    have key : q * (0 - u) + u - (q * (v⁻¹ * u) * (0 - v) + v) = (u - v) - q * w := by
      rw [hw]; noncomm_ring
    rw [hqw, sub_self] at key
    exact sub_eq_zero.1 key
  exact not_parPts_restrict (α := α) hBA' hAB' (ag v) (ah 1) (ag u) (ah _) _ hZ1 hZ2
    (hP ⟨g, hg⟩ ⟨h, hh⟩ ⟨O, hOα⟩ ⟨A, ag u⟩ ⟨B, ag v⟩ ⟨C, ag 1⟩ ⟨A', ah 1⟩ ⟨B', ah _⟩ ⟨C', ah u⟩
      hgh (AffLine.left_mem_through hOC) (AffLine.left_mem_through hOA') (mg u) (mg v) (mg 1)
      (mh 1) (mh _) (mh u) (hsub (hne (Or.inl hu0))) (hsub (hne (Or.inl hv0)))
      (hsub (hne (Or.inl one_ne_zero))) (hsub (hne (Or.inr one_ne_zero)))
      (hsub (hne (Or.inr hvu))) (hsub (hne (Or.inr hu0))) (hsub (hne (Or.inl huv')))
      (hsub (hne (Or.inl hv1))) (hsub (hne (Or.inl hu1))) hp1 hp2)

end Coordinates

/-! ## The non-pascalian geometry over `Ω(s, t)` -/

/-- The order of `Ω(s, t)ᵐᵒᵖ` (that of `Ω(s, t)`). -/
noncomputable instance OmegaST.instLinearOrderOp : LinearOrder OmegaSTᵐᵒᵖ :=
  opLinearOrder OmegaST

instance OmegaST.instIsStrictOrderedRingOp : IsStrictOrderedRing OmegaSTᵐᵒᵖ :=
  opIsStrictOrderedRing OmegaST

/-- **The space of § 29 over `Ω(s, t)`** satisfies the axioms I, II, III, and Pascal's theorem fails
in one of its planes. -/
theorem omega_space_nonpascal :
    SpaceOrder (Coord OmegaSTᵐᵒᵖ 3) (CoordLine OmegaSTᵐᵒᵖ 3) (CoordPlane OmegaSTᵐᵒᵖ 3) ∧
      SpaceParallels (Coord OmegaSTᵐᵒᵖ 3) (CoordLine OmegaSTᵐᵒᵖ 3) (CoordPlane OmegaSTᵐᵒᵖ 3) ∧
      ∃ α : CoordPlane OmegaSTᵐᵒᵖ 3, ¬PascalTheorem {X : Coord OmegaSTᵐᵒᵖ 3 // X ∈ α}
        (L := {a : CoordLine OmegaSTᵐᵒᵖ 3 // LiesInPlane (Point := Coord OmegaSTᵐᵒᵖ 3) a α}) := by
  refine ⟨inferInstance, inferInstance, not_pascal_of_noncomm (u := MulOpposite.op OmegaST.t)
    (v := MulOpposite.op OmegaST.s) ?_⟩
  rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, ne_eq, MulOpposite.op_inj]
  exact fun h => OmegaST.t_mul_s_ne h.symm


/-! ## § 35: identities in the co-ordinates -/

/-- **An integral polynomial that vanishes at every point of `Ωʳ` where a non-zero polynomial `Dn`
does not vanish is the zero polynomial** (§ 35: "the expression `A(p₁, …, p_r)` must also vanish
identically"; `A = N / Dn`). -/
theorem eq_zero_of_vanishes_on_omega {r : ℕ} (N Dn : MvPolynomial (Fin r) ℤ) (hD : Dn ≠ 0)
    (h : ∀ x : Fin r → OmegaField, MvPolynomial.aeval x Dn ≠ 0 → MvPolynomial.aeval x N = 0) :
    N = 0 := by
  have hinj : Function.Injective (Int.castRingHom OmegaField) := Int.cast_injective
  have hprod : MvPolynomial.map (Int.castRingHom OmegaField) N *
      MvPolynomial.map (Int.castRingHom OmegaField) Dn = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_mul, MvPolynomial.eval_map, map_zero, mul_eq_zero]
    have e : ∀ p : MvPolynomial (Fin r) ℤ,
        MvPolynomial.eval₂ (Int.castRingHom OmegaField) x p = MvPolynomial.aeval x p := fun p => by
      rw [MvPolynomial.aeval_def]; congr 1
    rw [e, e]
    by_cases hx : MvPolynomial.aeval x Dn = 0
    · exact Or.inr hx
    · exact Or.inl (h x hx)
  rcases mul_eq_zero.1 hprod with h1 | h1
  · exact MvPolynomial.map_injective _ hinj (by rw [h1, map_zero])
  · exact absurd (MvPolynomial.map_injective _ hinj (by rw [h1, map_zero])) hD

/-- **An identity in the co-ordinates holds in every commutative number system** ("in accordance
with the laws 7–12 of § 13"). -/
theorem vanishes_of_vanishes_on_omega {r : ℕ} (N Dn : MvPolynomial (Fin r) ℤ) (hD : Dn ≠ 0)
    (h : ∀ x : Fin r → OmegaField, MvPolynomial.aeval x Dn ≠ 0 → MvPolynomial.aeval x N = 0)
    (R : Type*) [CommRing R] (x : Fin r → R) : MvPolynomial.aeval x N = 0 := by
  rw [eq_zero_of_vanishes_on_omega N Dn hD h, map_zero]

/-- The segments of a plane with I 1–2, II, III, the second part of Desargues's theorem and
Pascal's theorem form a commutative field. -/
@[instance_reducible] noncomputable def segField {P : Type u} {L : Type v} [HasLines P L]
    [HasBetween P] [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P)
    (hP : PascalTheorem P (L := L)) (F : Frame P) : Field (DesAlg.Seg F) :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  { (inferInstance : DivisionRing (DesAlg.Seg F)) with
    mul_comm := (pascal_iff_law12 hD).1 hP F }

/-- **An identity in the co-ordinates valid over `Ω` holds for the segments of every plane with
I 1–2, II, III in which the theorems of Desargues and Pascal hold.** -/
theorem identity_for_segments {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P)
    (hP : PascalTheorem P (L := L)) (F : Frame P) {r : ℕ} (N Dn : MvPolynomial (Fin r) ℤ)
    (hDn : Dn ≠ 0)
    (h : ∀ x : Fin r → OmegaField, MvPolynomial.aeval x Dn ≠ 0 → MvPolynomial.aeval x N = 0) :
    letI := segField hD hP F
    ∀ x : Fin r → DesAlg.Seg F, MvPolynomial.aeval x N = 0 := by
  let := segField hD hP F
  exact vanishes_of_vanishes_on_omega N Dn hDn h _


/-! ## The algebra of segments of the real analytic plane is the co-ordinate algebra -/

section RealPlane

open Coord

/-- The real plane has a line. -/
theorem realLine_nonempty : Nonempty (CoordLine ℝ 2) := ⟨Coord.lineOfEq 1 0 0 (Or.inl one_ne_zero)⟩

theorem pt2_line (r x₁ y₁ x₂ y₂ : ℝ) :
    r • (pt2 x₂ y₂ - pt2 x₁ y₁) + pt2 x₁ y₁ = pt2 (r * (x₂ - x₁) + x₁) (r * (y₂ - y₁) + y₁) :=
  ext2 (by simp) (by simp)

theorem pt2_ne {x y x' y' : ℝ} (h : x ≠ x' ∨ y ≠ y') : pt2 x y ≠ pt2 x' y' := fun e =>
  h.elim (fun h' => h' (by simpa using congrArg xc e)) (fun h' => h' (by simpa using congrArg yc e))

theorem mem_through_pt2 {x₁ y₁ x₂ y₂ : ℝ} (h : pt2 x₁ y₁ ≠ pt2 x₂ y₂) {X : Coord ℝ 2} :
    X ∈ AffLine.through (pt2 x₁ y₁) (pt2 x₂ y₂) h ↔
      ∃ r : ℝ, X = pt2 (r * (x₂ - x₁) + x₁) (r * (y₂ - y₁) + y₁) := by
  rw [AffLine.mem_through_iff]
  simp only [pt2_line]

section

attribute [local instance] realLine_nonempty

/-- **The parallel to `AB` through `X`** consists of the points `r (B - A) + X`. -/
theorem mem_pline_through {A B : Coord ℝ 2} (h : A ≠ B) (X : Coord ℝ 2) (r : ℝ) :
    r • (B - A) + X ∈ pline (AffLine.through A B h) X := by
  have hd : B - A ≠ 0 := sub_ne_zero.2 h.symm
  have hX : X ≠ (B - A) + X := fun e => hd (by
    have := congrArg (· - X) e; simpa using this.symm)
  set m := AffLine.through X ((B - A) + X) hX
  have hlpar : LPar (Coord ℝ 2) m (AffLine.through A B h) := by
    intro Z hZm hZl
    rw [AffLine.mem_through_iff] at hZm hZl
    obtain ⟨s, hs⟩ := hZm
    obtain ⟨t, ht⟩ := hZl
    have hZ : Z ≠ (B - A) + Z := fun e => hd (by
      have := congrArg (· - Z) e; simpa using this.symm)
    have e1 : m = AffLine.through Z ((B - A) + Z) hZ := by
      refine AffLine.eq_through m hZ ?_ ?_ <;> rw [AffLine.mem_through_iff]
      · exact ⟨s, hs⟩
      · refine ⟨s + 1, ?_⟩; rw [hs]; simp only [add_sub_cancel_right, add_smul, one_smul]; abel
    have e2 : AffLine.through A B h = AffLine.through Z ((B - A) + Z) hZ := by
      refine AffLine.eq_through _ hZ ?_ ?_ <;> rw [AffLine.mem_through_iff]
      · exact ⟨t, ht⟩
      · refine ⟨t + 1, ?_⟩; rw [ht, add_smul, one_smul]; abel
    rw [e1, e2]
  rw [← eq_pline (AffLine.left_mem_through hX) hlpar, AffLine.mem_through_iff]
  exact ⟨r, by rw [add_sub_cancel_right]⟩

/-- **In the analytic plane over `ℝ`, with the frame `O = (0,0)`, `E = (1,0)`, `E' = (0,1)`, the
sum and the product of segments of § 24 are the sum and product of the abscissae.** -/
theorem same_coordinates_real (F : Frame (Coord ℝ 2)) (hO : F.O = pt2 0 0) (hE : F.E = pt2 1 0)
    (hE' : F.E' = pt2 0 1) (a b : DesAlg.Seg (L := CoordLine ℝ 2) F) :
    xc (a + b).pt = xc a.pt + xc b.pt ∧ xc (a * b).pt = xc a.pt * xc b.pt := by
  have hOE : pt2 (0 : ℝ) 0 ≠ pt2 1 0 := pt2_ne (Or.inl zero_ne_one)
  have hOE' : pt2 (0 : ℝ) 0 ≠ pt2 0 1 := pt2_ne (Or.inr zero_ne_one)
  have hEE' : pt2 (1 : ℝ) 0 ≠ pt2 0 1 := pt2_ne (Or.inl one_ne_zero)
  have hxl : (F.xl : CoordLine ℝ 2) = AffLine.through _ _ hOE := by
    rw [Frame.xl, hO, hE]
    exact ln_eq hOE (AffLine.left_mem_through hOE) (AffLine.right_mem_through hOE)
  have hyl : (F.yl : CoordLine ℝ 2) = AffLine.through _ _ hOE' := by
    rw [Frame.yl, hO, hE']
    exact ln_eq hOE' (AffLine.left_mem_through hOE') (AffLine.right_mem_through hOE')
  have hul : (F.ul : CoordLine ℝ 2) = AffLine.through _ _ hEE' := by
    rw [Frame.ul, hE, hE']
    exact ln_eq hEE' (AffLine.left_mem_through hEE') (AffLine.right_mem_through hEE')
  -- points of the axes
  have onx : ∀ x : ℝ, pt2 x 0 ∈ (F.xl : CoordLine ℝ 2) := fun x => by
    rw [hxl, mem_through_pt2]; exact ⟨x, by simp⟩
  have ony : ∀ y : ℝ, pt2 0 y ∈ (F.yl : CoordLine ℝ 2) := fun y => by
    rw [hyl, mem_through_pt2]; exact ⟨y, by simp⟩
  have of_x : ∀ X : Coord ℝ 2, X ∈ (F.xl : CoordLine ℝ 2) → X = pt2 (xc X) 0 := fun X hX => by
    rw [hxl, mem_through_pt2] at hX
    obtain ⟨r, rfl⟩ := hX
    simp
  -- `toY (x, 0) = (0, x)` and `toX (x, y) = (x + y, 0)`
  have htoY : ∀ x : ℝ, F.toY (pt2 x 0) = pt2 0 x := fun x => by
    refine (F.toY_eq (ony x) ?_).symm
    rw [hul]
    convert mem_pline_through hEE' (pt2 x 0) x using 1
    exact ext2 (by simp only [xc_add, xc_smul, xc_sub, xc_pt2]; ring) (by simp only [yc_add, yc_smul, yc_sub, yc_pt2]; ring)
  have htoX : ∀ x y : ℝ, F.toX (pt2 x y) = pt2 (x + y) 0 := fun x y => by
    refine (F.toX_eq (onx (x + y)) ?_).symm
    rw [hul]
    convert mem_pline_through hEE' (pt2 x y) (-y) using 1
    exact ext2 (by simp only [xc_add, xc_smul, xc_sub, xc_pt2]; ring) (by simp only [yc_add, yc_smul, yc_sub, yc_pt2]; ring)
  set x := xc a.pt
  set y := xc b.pt
  have ha : a.pt = pt2 x 0 := of_x a.pt a.mem
  have hb : b.pt = pt2 y 0 := of_x b.pt b.mem
  constructor
  · -- the sum
    have hmeet : meet (pline (F.xl : CoordLine ℝ 2) (pt2 0 x)) (pline (F.yl : CoordLine ℝ 2)
        (pt2 y 0)) = pt2 y x := by
      refine (eq_meet (F.nl_pline_xy _ _) ?_ ?_).symm
      · rw [hxl]
        convert mem_pline_through hOE (pt2 0 x) y using 1
        exact ext2 (by simp only [xc_add, xc_smul, xc_sub, xc_pt2]; ring) (by simp only [yc_add, yc_smul, yc_sub, yc_pt2]; ring)
      · rw [hyl]
        convert mem_pline_through hOE' (pt2 y 0) x using 1
        exact ext2 (by simp only [xc_add, xc_smul, xc_sub, xc_pt2]; ring) (by simp only [yc_add, yc_smul, yc_sub, yc_pt2]; ring)
    rw [DesAlg.Seg.add_pt, Frame.hsumPt, ha, hb, htoY, hmeet, htoX, xc_pt2, add_comm]
  · -- the product
    have hE0 : pt2 (1 : ℝ) 0 ≠ pt2 0 x := pt2_ne (Or.inl one_ne_zero)
    have hln : (ln F.E (F.toY a.pt) : CoordLine ℝ 2) = AffLine.through _ _ hE0 := by
      rw [ha, htoY, hE]
      exact ln_eq hE0 (AffLine.left_mem_through hE0) (AffLine.right_mem_through hE0)
    have hnl := F.nl_EA' a.pt
    have hmeet : meet (F.yl : CoordLine ℝ 2) (pline (ln F.E (F.toY a.pt) : CoordLine ℝ 2) b.pt) =
        pt2 0 (y * x) := by
      refine (eq_meet (not_lpar_pline_right hnl _) (ony _) ?_).symm
      rw [hln, hb]
      convert mem_pline_through hE0 (pt2 y 0) y using 1
      exact ext2 (by simp only [xc_add, xc_smul, xc_sub, xc_pt2]; ring) (by simp only [yc_add, yc_smul, yc_sub, yc_pt2]; ring)
    rw [DesAlg.Seg.mul_pt, Frame.hmulPt, hmeet, htoX, xc_pt2, zero_add, mul_comm]

end

end RealPlane

end NonPascal
end HilbertFoundations
