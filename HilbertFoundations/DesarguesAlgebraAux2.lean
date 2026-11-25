import HilbertFoundations.DesarguesAlgebraAux

/-!
# Helper for §§ 24–28: Hilbert's algebra of segments in a desarguesian plane

Helper module of `DesarguesAlgebra.lean`. Throughout, `(P, L)` is a plane geometry satisfying
I 1–2, II, III (`LineOrder`, `PlaneParallels`; the order axioms are used only to have a third point
on each line) and `DesarguesII P` (the second part of Desargues's theorem).

* `Frame P`: Hilbert's two fixed lines through `O`, with the unit points `E`, `E'`.
* `Seg F`: Hilbert's segments, represented by their extremity on the first fixed line `OE`;
  `F.toY A` is the point `A'` of the second line with `AA' ∥ EE'` (Hilbert's "`OA = OA'`").
* **Hilbert's constructions** `hsumPt` (sum, § 24) and `hmulPt` (product, § 24), literally, with
  the instances `Add (Seg F)`, `Mul (Seg F)`, `Zero (Seg F)` (`O`), `One (Seg F)` (`E`).
* `trf O X`: the translation `O ↦ X`; `dl O E t`: the dilatation with centre `O` and `E ↦ t`.
  `hsumPt_eq`: Hilbert's sum `a + b` is `trf O b a`; `hmulPt_eq`: Hilbert's product `a b` is
  `dl O E b a`.
* `Vec F`: the points with the addition `X + Y = trf O X Y` (an abelian group), and a module over
  `(Seg F)ᵐᵒᵖ` (`X • t = dl O E t X`: the segments act on the right).
* `Seg F` is a division ring (`instDivisionRing`): the laws of §§ 25–26 are its axioms.
* `Vec F` has the basis `E, E'` (`basisEE'`), and the lines of the plane are the affine lines
  `{r • (B - A) + A}` (`mem_ln_iff_smul`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

namespace DesAlg

variable {P : Type u} {L : Type v} [HasLines P L]

/-- **Hilbert's frame** (§ 24): two fixed lines through `O`, the first through the unit point `E`,
the second through the unit point `E'`. -/
structure Frame (P : Type u) {L : Type v} [HasLines P L] where
  O : P
  E : P
  E' : P
  hOE : O ≠ E
  noncol : ¬Collinear O E E'

section Translations

variable [HasBetween P] [LineOrder P L] [PlaneParallels P L] [Nonempty L]

/-- The translation mapping `O` to `X`. -/
noncomputable def trf (O X : P) : P → P :=
  haveI : Nonempty (P → P) := ⟨id⟩
  Classical.epsilon (fun f => IsTr (L := L) f ∧ f O = X)

/-- The dilatation with centre `O` mapping `E` to `t`. -/
noncomputable def dl (O E t : P) : P → P :=
  haveI : Nonempty (P → P) := ⟨id⟩
  Classical.epsilon (fun f => IsDil (L := L) f ∧ f O = O ∧ f E = t)

variable (hD : DesarguesII P)
include hD

theorem trf_spec (O X : P) : IsTr (L := L) (trf O X) ∧ trf O X O = X := by
  have : Nonempty (P → P) := ⟨id⟩
  exact Classical.epsilon_spec (exists_tr hD O X)

theorem trf_isTr (O X : P) : IsTr (L := L) (trf O X) := (trf_spec hD O X).1

@[simp] theorem trf_O (O X : P) : trf O X O = X := (trf_spec hD O X).2

theorem trf_eq_of {O X : P} {f : P → P} (hf : IsTr (L := L) f) (h : f O = X) : f = trf O X :=
  tr_eq_of hf (trf_isTr hD O X) (by rw [h, trf_O hD])

theorem trf_self (O : P) : trf O O = id := (trf_eq_of hD isTr_id rfl).symm

theorem trf_comp (O X Y : P) : trf O X ∘ trf O Y = trf O (trf O X Y) :=
  trf_eq_of hD ((trf_isTr hD O X).comp (trf_isTr hD O Y)) (by simp [trf_O hD])

theorem trf_comm (O X Y : P) : trf O X Y = trf O Y X := by
  have := congrFun (tr_comm hD (trf_isTr hD O X) (trf_isTr hD O Y)) O
  simpa [trf_O hD] using this

theorem trf_assoc (O X Y Z : P) : trf O (trf O X Y) Z = trf O X (trf O Y Z) := by
  rw [← trf_comp hD]; rfl

theorem exists_trf_inv (O X : P) : ∃ Y : P, trf O X Y = O := by
  obtain ⟨g, -, -, hfg⟩ := tr_inv hD (trf_isTr hD O X)
  exact ⟨g O, by simpa using congrFun hfg O⟩

theorem trf_injective (O X : P) : Function.Injective (trf O X) := by
  obtain ⟨g, -, hgf, -⟩ := tr_inv hD (trf_isTr hD O X)
  exact Function.LeftInverse.injective (g := g) fun Y => by simpa using congrFun hgf Y

/-- A translation `O ↦ X` maps every line through `O` and `X` into itself. -/
theorem trf_mem_of {O X Y : P} {l : L} (hO : O ∈ l) (hX : X ∈ l) (hY : Y ∈ l) : trf O X Y ∈ l := by
  have := (trf_isTr hD O X).1.map_line hO hY
  rwa [trf_O hD, pline_of_mem hX] at this

/-- The trace of the translation `O ↦ X` through `Y` is parallel to every line through `O`, `X`. -/
theorem trf_trace {O X : P} {l : L} (hO : O ∈ l) (hX : X ∈ l) (Y : P) : trf O X Y ∈ pline l Y := by
  by_cases h : X = O
  · subst h; rw [trf_self hD]; exact mem_pline l Y
  · have := (trf_isTr hD O X).trace (X := O) (by rw [trf_O hD]; exact h) Y
    rwa [trf_O hD, ln_eq (Ne.symm h) hO hX] at this

theorem dl_spec {O E t : P} (hOE : O ≠ E) (ht : t ∈ (ln O E : L)) :
    IsDil (L := L) (dl O E t) ∧ dl O E t O = O ∧ dl O E t E = t := by
  have : Nonempty (P → P) := ⟨id⟩
  refine Classical.epsilon_spec (p := fun f => IsDil (L := L) f ∧ f O = O ∧ f E = t) ?_
  by_cases h : t = O
  · exact ⟨fun _ => O, isDil_const O, rfl, h.symm⟩
  · obtain ⟨f, hf, hfO, hfE⟩ := exists_cdil (L := L) hD (Ne.symm hOE) h ht
    exact ⟨f, hf, hfO, hfE⟩

theorem dl_eq_of {O E t : P} (hOE : O ≠ E) (ht : t ∈ (ln O E : L)) {f : P → P}
    (hf : IsDil (L := L) f) (hO : f O = O) (hE : f E = t) : f = dl O E t := by
  obtain ⟨h1, h2, h3⟩ := dl_spec hD hOE ht
  exact dil_eq_of_two hf h1 hOE (hO.trans h2.symm) (hE.trans h3.symm)

end Translations

/-! ## The frame and Hilbert's constructions -/

namespace Frame

variable [PlaneParallels P L] [Nonempty L] (F : Frame P)

/-- The first fixed line `OE`. -/
noncomputable def xl : L := ln F.O F.E

/-- The second fixed line `OE'`. -/
noncomputable def yl : L := ln F.O F.E'

/-- The unit line `EE'`. -/
noncomputable def ul : L := ln F.E F.E'

theorem O_xl : F.O ∈ (F.xl : L) := mem_ln_left _ _
theorem E_xl : F.E ∈ (F.xl : L) := mem_ln_right _ _
theorem O_yl : F.O ∈ (F.yl : L) := mem_ln_left _ _
theorem E'_yl : F.E' ∈ (F.yl : L) := mem_ln_right _ _
theorem E_ul : F.E ∈ (F.ul : L) := mem_ln_left _ _
theorem E'_ul : F.E' ∈ (F.ul : L) := mem_ln_right _ _

theorem E'_not_xl : F.E' ∉ (F.xl : L) := fun h => F.noncol ((collinear_iff_mem_ln F.hOE).2 h)

theorem hOE' : F.O ≠ F.E' := fun h => F.E'_not_xl (h ▸ F.O_xl)

theorem hEE' : F.E ≠ F.E' := fun h => F.E'_not_xl (h ▸ F.E_xl)

theorem E_not_yl : F.E ∉ (F.yl : L) := fun h => F.E'_not_xl (by
  have : (F.yl : L) = F.xl := (ln_eq F.hOE F.O_yl h).symm
  rw [← this]; exact F.E'_yl)

theorem O_not_ul : F.O ∉ (F.ul : L) := fun h => F.E'_not_xl (by
  have : (F.ul : L) = F.xl := (ln_eq F.hOE h F.E_ul).symm
  rw [← this]; exact F.E'_ul)

theorem xl_ne_yl : (F.xl : L) ≠ F.yl := fun h => F.E_not_yl (h ▸ F.E_xl)

theorem nl_xy : ¬LPar P (F.xl : L) F.yl := not_lpar_of F.O_xl F.O_yl F.xl_ne_yl

theorem nl_ux : ¬LPar P (F.ul : L) F.xl :=
  not_lpar_of F.E_ul F.E_xl fun h => F.E'_not_xl (h ▸ F.E'_ul)

theorem nl_uy : ¬LPar P (F.ul : L) F.yl :=
  not_lpar_of F.E'_ul F.E'_yl fun h => F.E_not_yl (h ▸ F.E_ul)

/-- The point `A'` of the second line with `AA' ∥ EE'` (Hilbert: the segments `OA`, `OA'` are
"equal"). -/
noncomputable def toY (A : P) : P := meet (F.yl : L) (pline (F.ul : L) A)

/-- The point `A` of the first line with `AA' ∥ EE'`. -/
noncomputable def toX (A' : P) : P := meet (F.xl : L) (pline (F.ul : L) A')

theorem toY_mem (A : P) : F.toY A ∈ (F.yl : L) :=
  meet_mem_left (not_lpar_pline_right (fun h => F.nl_uy h.symm) A)

theorem toY_par (A : P) : F.toY A ∈ pline (F.ul : L) A :=
  meet_mem_right (not_lpar_pline_right (fun h => F.nl_uy h.symm) A)

theorem toX_mem (A : P) : F.toX A ∈ (F.xl : L) :=
  meet_mem_left (not_lpar_pline_right (fun h => F.nl_ux h.symm) A)

theorem toX_par (A : P) : F.toX A ∈ pline (F.ul : L) A :=
  meet_mem_right (not_lpar_pline_right (fun h => F.nl_ux h.symm) A)

theorem toX_eq {A C : P} (hC : C ∈ (F.xl : L)) (h : C ∈ pline (F.ul : L) A) : C = F.toX A :=
  eq_meet (not_lpar_pline_right (fun h => F.nl_ux h.symm) A) hC h

theorem toY_eq {A C : P} (hC : C ∈ (F.yl : L)) (h : C ∈ pline (F.ul : L) A) : C = F.toY A :=
  eq_meet (not_lpar_pline_right (fun h => F.nl_uy h.symm) A) hC h

theorem toX_toY (A : P) (hA : A ∈ (F.xl : L)) : F.toX (F.toY A) = A :=
  (F.toX_eq hA (pline_symm (F.toY_par A))).symm

theorem toY_toX (A : P) (hA : A ∈ (F.yl : L)) : F.toY (F.toX A) = A :=
  (F.toY_eq hA (pline_symm (F.toX_par A))).symm

theorem toY_O : F.toY F.O = F.O := (F.toY_eq F.O_yl (mem_pline _ _)).symm

theorem toX_O : F.toX F.O = F.O := (F.toX_eq F.O_xl (mem_pline _ _)).symm

theorem toY_E : F.toY F.E = F.E' :=
  (F.toY_eq F.E'_yl (by rw [pline_of_mem F.E_ul]; exact F.E'_ul)).symm

/-- **Hilbert's sum** (§ 24) of the segments `a = OA` and `b = OB`: `AA' ∥ EE'`, the parallel to
`OE` through `A'` and the parallel to `OE'` through `B` meet in `A''`, and the parallel to `EE'`
through `A''` cuts `OE` in `C`. -/
noncomputable def hsumPt (A B : P) : P :=
  F.toX (meet (pline (F.xl : L) (F.toY A)) (pline (F.yl : L) B))

/-- **Hilbert's product** (§ 24) of `a = OA` by `b = OB`: `AA' ∥ EE'`, the parallel to `EA'`
through `B` cuts `OE'` in `C'`, and `c = OC'`, represented on `OE` by `C` with `CC' ∥ EE'`. -/
noncomputable def hmulPt (A B : P) : P :=
  F.toX (meet (F.yl : L) (pline (ln F.E (F.toY A) : L) B))

theorem nl_EA' (A : P) : ¬LPar P (F.yl : L) (ln F.E (F.toY A) : L) :=
  not_lpar_of (F.toY_mem A) (mem_ln_right _ _) fun h => F.E_not_yl (h ▸ mem_ln_left _ _)

end Frame

/-- **Hilbert's segments** (§ 24): the segments `OA` with `A` on the first fixed line (a segment
with extremity on the second line is "equal" to exactly one of these, `Frame.toY`). -/
@[ext] structure Seg [PlaneParallels P L] [Nonempty L] (F : Frame P) where
  /-- The extremity of the segment on the first fixed line. -/
  pt : P
  mem : pt ∈ (F.xl : L)

namespace Seg

variable [PlaneParallels P L] [Nonempty L] {F : Frame P}

instance : Zero (Seg F) := ⟨⟨F.O, F.O_xl⟩⟩
instance : One (Seg F) := ⟨⟨F.E, F.E_xl⟩⟩
noncomputable instance : Add (Seg F) := ⟨fun a b => ⟨F.hsumPt a.pt b.pt, F.toX_mem _⟩⟩
noncomputable instance : Mul (Seg F) := ⟨fun a b => ⟨F.hmulPt a.pt b.pt, F.toX_mem _⟩⟩

@[simp] theorem zero_pt : (0 : Seg F).pt = F.O := rfl
@[simp] theorem one_pt : (1 : Seg F).pt = F.E := rfl
theorem add_pt (a b : Seg F) : (a + b).pt = F.hsumPt a.pt b.pt := rfl
theorem mul_pt (a b : Seg F) : (a * b).pt = F.hmulPt a.pt b.pt := rfl

end Seg

/-! ## Hilbert's constructions are the translations and dilatations -/

section Bridge

variable [HasBetween P] [LineOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P)
  (F : Frame P)
include hD

/-- **Hilbert's sum is a translation**: `a + b = trf O b a`. -/
theorem hsumPt_eq {a b : P} (ha : a ∈ (F.xl : L)) (hb : b ∈ (F.xl : L)) :
    F.hsumPt a b = trf F.O b a := by
  set τ := trf F.O b
  have hτ := trf_isTr hD F.O b
  -- `τ A' = A''`
  have k1 : τ (F.toY a) ∈ pline (F.xl : L) (F.toY a) := trf_trace hD F.O_xl hb _
  have k2 : τ (F.toY a) ∈ pline (F.yl : L) b := by
    have := hτ.1.map_line F.O_yl (F.toY_mem a); rwa [trf_O hD] at this
  have hA'' : τ (F.toY a) = meet (pline (F.xl : L) (F.toY a)) (pline (F.yl : L) b) :=
    eq_meet (not_lpar_pline F.nl_xy _ _) k1 k2
  -- `τ a = C`
  have k3 : τ (F.toY a) ∈ pline (F.ul : L) (τ a) := by
    have := hτ.1.map_line (mem_pline (F.ul : L) a) (F.toY_par a)
    rwa [pline_pline] at this
  have k4 : τ a ∈ (F.xl : L) := trf_mem_of hD F.O_xl hb ha
  rw [Frame.hsumPt, ← hA'']
  exact (F.toX_eq k4 (pline_symm k3)).symm

/-- **Hilbert's product is a dilatation**: `a b = dl O E b a`. -/
theorem hmulPt_eq {a b : P} (ha : a ∈ (F.xl : L)) (hb : b ∈ (F.xl : L)) :
    F.hmulPt a b = dl F.O F.E b a := by
  obtain ⟨hσ, hσO, hσE⟩ := dl_spec hD F.hOE hb
  set σ := dl F.O F.E b
  have k1 : σ (F.toY a) ∈ (F.yl : L) := hσ.mem_of_fix hσO F.O_yl (F.toY_mem a)
  have k2 : σ (F.toY a) ∈ pline (ln F.E (F.toY a) : L) b := by
    have := hσ.map_line (mem_ln_left F.E (F.toY a)) (mem_ln_right F.E (F.toY a))
    rwa [hσE] at this
  have hC' : σ (F.toY a) = meet (F.yl : L) (pline (ln F.E (F.toY a) : L) b) :=
    eq_meet (not_lpar_pline_right (F.nl_EA' a) _) k1 k2
  have k3 : σ (F.toY a) ∈ pline (F.ul : L) (σ a) := by
    have := hσ.map_line (mem_pline (F.ul : L) a) (F.toY_par a)
    rwa [pline_pline] at this
  have k4 : σ a ∈ (F.xl : L) := hσ.mem_of_fix hσO F.O_xl ha
  rw [Frame.hmulPt, ← hC']
  exact (F.toX_eq k4 (pline_symm k3)).symm

theorem dl_E : dl F.O F.E F.E = (id : P → P) :=
  (dl_eq_of hD F.hOE F.E_xl isDil_id rfl rfl).symm

theorem dl_zero : dl F.O F.E F.O = (fun _ : P => F.O) :=
  (dl_eq_of hD F.hOE F.O_xl (isDil_const F.O) rfl rfl).symm

theorem dl_isDil {t : P} (ht : t ∈ (F.xl : L)) : IsDil (L := L) (dl F.O F.E t) :=
  (dl_spec hD F.hOE ht).1

@[simp] theorem dl_O {t : P} (ht : t ∈ (F.xl : L)) : dl F.O F.E t F.O = F.O :=
  (dl_spec hD F.hOE ht).2.1

@[simp] theorem dl_at_E {t : P} (ht : t ∈ (F.xl : L)) : dl F.O F.E t F.E = t :=
  (dl_spec hD F.hOE ht).2.2

theorem dl_mem {t X : P} {l : L} (ht : t ∈ (F.xl : L)) (hO : F.O ∈ l) (hX : X ∈ l) :
    dl F.O F.E t X ∈ l :=
  (dl_isDil hD F ht).mem_of_fix (dl_O hD F ht) hO hX

theorem dl_comp {s t : P} (hs : s ∈ (F.xl : L)) (ht : t ∈ (F.xl : L)) :
    dl F.O F.E t ∘ dl F.O F.E s = dl F.O F.E (dl F.O F.E t s) :=
  dl_eq_of hD F.hOE (dl_mem hD F ht F.O_xl hs) ((dl_isDil hD F ht).comp (dl_isDil hD F hs))
    (by simp [dl_O hD F hs, dl_O hD F ht]) (by simp [dl_at_E hD F hs])

/-- A dilatation with centre `O` is additive. -/
theorem dl_add {t : P} (ht : t ∈ (F.xl : L)) (X Y : P) :
    dl F.O F.E t (trf F.O X Y) = trf F.O (dl F.O F.E t X) (dl F.O F.E t Y) := by
  by_cases h0 : t = F.O
  · subst h0; rw [dl_zero hD F]; simp [trf_O hD]
  obtain ⟨g, hg, hgO, hgf, hfg⟩ := cdil_inv hD (dl_isDil hD F ht) (dl_O hD F ht) F.hOE.symm
    (by rw [dl_at_E hD F ht]; exact h0)
  have hc := IsTr.conj (dl_isDil hD F ht) hg hgf (trf_isTr hD F.O X)
  have e : dl F.O F.E t ∘ trf F.O X ∘ g = trf F.O (dl F.O F.E t X) :=
    trf_eq_of hD hc (by simp [hgO, trf_O hD])
  have k := congrFun hgf Y
  simp only [Function.comp, id] at k
  have := congrFun e (dl F.O F.E t Y)
  simp only [Function.comp] at this
  rw [k] at this
  exact this

/-- Sums of vectors parallel to a line are parallel to it. -/
theorem trf_par {X1 Y1 X2 Y2 : P} {l : L} (h1 : Y1 ∈ pline l X1) (h2 : Y2 ∈ pline l X2) :
    trf F.O Y1 Y2 ∈ pline l (trf F.O X1 X2) := by
  have a1 : trf F.O X2 Y1 ∈ pline l (trf F.O X2 X1) := by
    have := (trf_isTr hD F.O X2).1.map_line (mem_pline l X1) h1
    rwa [pline_pline] at this
  have a2 : trf F.O Y1 Y2 ∈ pline l (trf F.O Y1 X2) := by
    have := (trf_isTr hD F.O Y1).1.map_line (mem_pline l X2) h2
    rwa [pline_pline] at this
  rw [trf_comm hD F.O Y1 X2] at a2
  rw [trf_comm hD F.O X2 X1] at a1
  rw [← pline_eq_of_mem a1]; exact a2

/-- **The sum of two dilatations with centre `O`**: `dl (s + t) X = dl s X + dl t X`. -/
theorem dl_sum {s t : P} (hs : s ∈ (F.xl : L)) (ht : t ∈ (F.xl : L)) (X : P) :
    dl F.O F.E (trf F.O s t) X = trf F.O (dl F.O F.E s X) (dl F.O F.E t X) := by
  have hst : trf F.O s t ∈ (F.xl : L) := trf_mem_of hD F.O_xl hs ht
  have hφ : IsDil (L := L) (fun X => trf F.O (dl F.O F.E s X) (dl F.O F.E t X)) := by
    intro X Y hXY
    exact trf_par hD F ((dl_isDil hD F hs) X Y hXY) ((dl_isDil hD F ht) X Y hXY)
  have e := dl_eq_of hD F.hOE hst hφ (by simp [dl_O hD F hs, dl_O hD F ht, trf_O hD])
    (by simp [dl_at_E hD F hs, dl_at_E hD F ht])
  rw [← e]

/-- `dl t E' = (t)'`: the dilatation `E ↦ t` maps `E'` to the point of the second axis "equal" to
`t`. -/
theorem dl_E' {t : P} (ht : t ∈ (F.xl : L)) : dl F.O F.E t F.E' = F.toY t := by
  refine F.toY_eq (dl_mem hD F ht F.O_yl F.E'_yl) ?_
  have := (dl_isDil hD F ht).map_line F.E_ul F.E'_ul
  rwa [dl_at_E hD F ht] at this

end Bridge

/-! ## The division ring of segments -/

section SegRing

variable [HasBetween P] [LineOrder P L] [PlaneParallels P L] [Nonempty L]
  [hDF : Fact (DesarguesII P)] {F : Frame P}

namespace Seg

theorem add_pt' (a b : Seg F) : (a + b).pt = trf F.O b.pt a.pt :=
  hsumPt_eq hDF.out F a.mem b.mem

theorem mul_pt' (a b : Seg F) : (a * b).pt = dl F.O F.E b.pt a.pt :=
  hmulPt_eq hDF.out F a.mem b.mem

theorem exists_neg (a : Seg F) : ∃ b : Seg F, b + a = 0 := by
  obtain ⟨Y, hY⟩ := exists_trf_inv hDF.out F.O a.pt
  have hYl : Y ∈ (F.xl : L) := by
    by_cases ha : a.pt = F.O
    · rw [ha, trf_self hDF.out] at hY; simp only [id] at hY; rw [hY]; exact F.O_xl
    · -- `trf O a` maps `Y` to `O`; its trace through `Y` is parallel to `OE`
      have k := trf_trace hDF.out F.O_xl a.mem Y
      rw [hY] at k
      have e := pline_eq_of_mem k
      rw [pline_of_mem F.O_xl] at e
      rw [e]; exact mem_pline _ Y
  refine ⟨⟨Y, hYl⟩, Seg.ext ?_⟩
  rw [add_pt', zero_pt]; exact hY

noncomputable instance : Neg (Seg F) := ⟨fun a => (exists_neg a).choose⟩

theorem neg_add (a : Seg F) : -a + a = 0 := (exists_neg a).choose_spec

theorem exists_inv (a : Seg F) (ha : a ≠ 0) : ∃ b : Seg F, a * b = 1 := by
  have hD := hDF.out
  have ha' : a.pt ≠ F.O := fun h => ha (Seg.ext h)
  obtain ⟨g, hg, hgO, hgf, hfg⟩ := cdil_inv hD (dl_isDil hD F a.mem) (dl_O hD F a.mem)
    F.hOE.symm (by rw [dl_at_E hD F a.mem]; exact ha')
  have hgE : g F.E ∈ (F.xl : L) := hg.mem_of_fix hgO F.O_xl F.E_xl
  refine ⟨⟨g F.E, hgE⟩, Seg.ext ?_⟩
  rw [mul_pt', one_pt, ← dl_eq_of hD F.hOE hgE hg hgO rfl]
  have := congrFun hgf F.E
  simp only [Function.comp, id] at this
  rw [← dl_at_E hD F a.mem]; exact this

open Classical in
noncomputable instance : Inv (Seg F) :=
  ⟨fun a => if h : a = 0 then 0 else (exists_inv a h).choose⟩

open Classical in
theorem mul_inv (a : Seg F) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  show a * (if h : a = 0 then 0 else (exists_inv a h).choose) = 1
  split_ifs with h
  · exact absurd h ha
  · exact (exists_inv a h).choose_spec

open Classical in
theorem inv_zero' : (0 : Seg F)⁻¹ = 0 := by
  show (if h : (0 : Seg F) = 0 then 0 else (exists_inv 0 h).choose) = 0
  split_ifs with h
  · rfl
  · exact absurd rfl h

/-- **The segments form a division ring** (laws 1–11 of § 13, §§ 25–26, 28). -/
noncomputable instance instDivisionRing : DivisionRing (Seg F) where
  add_assoc a b c := Seg.ext (by
    simp only [add_pt']
    exact congrFun (trf_comp hDF.out F.O c.pt b.pt) a.pt)
  zero_add a := Seg.ext (by simp only [add_pt', zero_pt, trf_O hDF.out])
  add_zero a := Seg.ext (by simp only [add_pt', zero_pt, trf_self hDF.out, id])
  add_comm a b := Seg.ext (by simp only [add_pt']; exact trf_comm hDF.out _ _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := neg_add
  mul_assoc a b c := Seg.ext (by
    simp only [mul_pt']
    rw [← dl_comp hDF.out F b.mem c.mem]; rfl)
  one_mul a := Seg.ext (by simp only [mul_pt', one_pt, dl_at_E hDF.out F a.mem])
  mul_one a := Seg.ext (by simp only [mul_pt', one_pt, dl_E hDF.out F, id])
  left_distrib a b c := Seg.ext (by
    simp only [mul_pt', add_pt']
    rw [dl_sum hDF.out F c.mem b.mem, trf_comm hDF.out])
  right_distrib a b c := Seg.ext (by
    simp only [mul_pt', add_pt']
    exact dl_add hDF.out F c.mem _ _)
  zero_mul a := Seg.ext (by simp only [mul_pt', zero_pt, dl_O hDF.out F a.mem])
  mul_zero a := Seg.ext (by simp only [mul_pt', zero_pt, dl_zero hDF.out F])
  mul_inv_cancel := mul_inv
  inv_zero := inv_zero'
  exists_pair_ne := ⟨0, 1, fun h => F.hOE (congrArg Seg.pt h)⟩
  nnqsmul := _
  qsmul := _

end Seg

end SegRing


/-! ## Co-ordinates (§ 27) -/

namespace Frame

variable [PlaneParallels P L] [Nonempty L] (F : Frame P)

theorem nl_pline_xy (X Y : P) : ¬LPar P (pline (F.xl : L) X) (pline (F.yl : L) Y) :=
  not_lpar_pline F.nl_xy X Y

/-- **The first co-ordinate** of `X` (§ 27): the segment cut off on the first axis by the parallel
to the second axis through `X`. -/
noncomputable def xc (X : P) : Seg F :=
  ⟨meet (F.xl : L) (pline (F.yl : L) X), meet_mem_left (not_lpar_pline_right F.nl_xy X)⟩

/-- **The second co-ordinate** of `X` (§ 27): the segment cut off on the second axis by the
parallel to the first axis through `X` (represented on the first axis). -/
noncomputable def yc (X : P) : Seg F :=
  ⟨F.toX (meet (F.yl : L) (pline (F.xl : L) X)), F.toX_mem _⟩

theorem xc_par (X : P) : (F.xc X).pt ∈ pline (F.yl : L) X :=
  meet_mem_right (not_lpar_pline_right F.nl_xy X)

theorem yproj_mem (X : P) : meet (F.yl : L) (pline (F.xl : L) X) ∈ (F.yl : L) :=
  meet_mem_left (not_lpar_pline_right (fun h => F.nl_xy h.symm) X)

theorem yproj_par (X : P) : meet (F.yl : L) (pline (F.xl : L) X) ∈ pline (F.xl : L) X :=
  meet_mem_right (not_lpar_pline_right (fun h => F.nl_xy h.symm) X)

theorem toY_yc (X : P) : F.toY (F.yc X).pt = meet (F.yl : L) (pline (F.xl : L) X) :=
  F.toY_toX _ (F.yproj_mem X)

end Frame

/-! ## The plane as a vector space over the segments -/

/-- The points of the plane, regarded as vectors with origin `O`. -/
def Vec [PlaneParallels P L] [Nonempty L] (_F : Frame P) : Type u := P

section VecSpace

variable [HasBetween P] [LineOrder P L] [PlaneParallels P L] [Nonempty L]
  [hDF : Fact (DesarguesII P)] {F : Frame P}

namespace Vec

/-- A point as a vector. -/
def ofP (X : P) : Vec F := X

/-- A vector as a point. -/
def toP (X : Vec F) : P := X

@[simp] theorem toP_ofP (X : P) : toP (ofP (F := F) X) = X := rfl
@[simp] theorem ofP_toP (X : Vec F) : ofP (toP X) = X := rfl

theorem ofP_injective : Function.Injective (ofP (F := F)) := fun _ _ h => h

theorem exists_neg (X : Vec F) : ∃ Y : P, trf F.O Y (toP X) = F.O := by
  obtain ⟨Y, hY⟩ := exists_trf_inv hDF.out F.O (toP X)
  exact ⟨Y, by rw [trf_comm hDF.out]; exact hY⟩

noncomputable instance : Add (Vec F) := ⟨fun X Y => ofP (trf F.O (toP X) (toP Y))⟩

instance : Zero (Vec F) := ⟨ofP F.O⟩

noncomputable instance : Neg (Vec F) := ⟨fun X => ofP (exists_neg X).choose⟩

noncomputable instance instAddCommGroup : AddCommGroup (Vec F) where
  add_assoc X Y Z := trf_assoc hDF.out F.O X Y Z
  zero_add X := congrFun (trf_self hDF.out F.O) X
  add_zero X := trf_O hDF.out F.O X
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel X := (exists_neg X).choose_spec
  add_comm X Y := trf_comm hDF.out F.O X Y

theorem add_def (X Y : Vec F) : X + Y = ofP (trf F.O (toP X) (toP Y)) := rfl

theorem zero_def : (0 : Vec F) = ofP F.O := rfl

noncomputable instance instModule : Module (Seg F)ᵐᵒᵖ (Vec F) where
  smul r X := ofP (dl F.O F.E (MulOpposite.unop r).pt (toP X))
  one_smul X := congrFun (dl_E hDF.out F) X
  mul_smul r s X := by
    show ofP (dl F.O F.E (MulOpposite.unop (r * s)).pt (toP X)) =
      ofP (dl F.O F.E (MulOpposite.unop r).pt (dl F.O F.E (MulOpposite.unop s).pt (toP X)))
    rw [MulOpposite.unop_mul, Seg.mul_pt', ← dl_comp hDF.out F (MulOpposite.unop s).mem
      (MulOpposite.unop r).mem]
    rfl
  smul_zero r := dl_O hDF.out F (MulOpposite.unop r).mem
  smul_add r X Y := dl_add hDF.out F (MulOpposite.unop r).mem X Y
  add_smul r s X := by
    show ofP (dl F.O F.E (MulOpposite.unop (r + s)).pt (toP X)) =
      ofP (trf F.O (dl F.O F.E (MulOpposite.unop r).pt (toP X))
        (dl F.O F.E (MulOpposite.unop s).pt (toP X)))
    rw [MulOpposite.unop_add, Seg.add_pt', dl_sum hDF.out F (MulOpposite.unop s).mem
      (MulOpposite.unop r).mem, trf_comm hDF.out]
  zero_smul X := congrFun (dl_zero hDF.out F) X

theorem smul_def (r : (Seg F)ᵐᵒᵖ) (X : Vec F) :
    r • X = ofP (dl F.O F.E (MulOpposite.unop r).pt (toP X)) := rfl

theorem smul_E (t : Seg F) : (MulOpposite.op t) • (ofP F.E : Vec F) = ofP t.pt :=
  dl_at_E hDF.out F t.mem

theorem smul_E' (t : Seg F) : (MulOpposite.op t) • (ofP F.E' : Vec F) = ofP (F.toY t.pt) :=
  dl_E' hDF.out F t.mem

/-- **Every point is `x E + y E'`** with its co-ordinates `x`, `y`. -/
theorem decomp (X : P) :
    (ofP X : Vec F) = MulOpposite.op (F.xc X) • ofP F.E + MulOpposite.op (F.yc X) • ofP F.E' := by
  rw [smul_E, smul_E', F.toY_yc, add_def]
  simp only [toP_ofP]
  set x := (F.xc X).pt
  set Y' : P := meet (F.yl : L) (pline (F.xl : L) X)
  have k1 : trf (L := L) F.O x Y' ∈ pline (F.xl : L) Y' :=
    trf_trace hDF.out F.O_xl (F.xc X).mem Y'
  have k2 : trf (L := L) F.O x Y' ∈ pline (F.yl : L) x := by
    have := (trf_isTr hDF.out F.O x).1.map_line F.O_yl (F.yproj_mem X)
    rwa [trf_O hDF.out] at this
  have k3 : X ∈ pline (F.xl : L) Y' := pline_symm (F.yproj_par X)
  have k4 : X ∈ pline (F.yl : L) x := pline_symm (F.xc_par X)
  have := eq_of_mem_not_lpar (F.nl_pline_xy _ _) k3 k4 k1 k2
  exact this

theorem linearIndependent_EE' :
    LinearIndependent (Seg F)ᵐᵒᵖ ![(ofP F.E : Vec F), ofP F.E'] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hD := hDF.out
  set a := MulOpposite.unop s
  set b := MulOpposite.unop t
  have hs : s = MulOpposite.op a := rfl
  have ht : t = MulOpposite.op b := rfl
  rw [hs, ht, smul_E, smul_E', add_def, zero_def] at hst
  simp only [toP_ofP] at hst
  have ha : a.pt = F.O := by
    have k := (trf_isTr hD F.O a.pt).1.map_line F.O_yl (F.toY_mem b.pt)
    rw [trf_O hD] at k
    have hk : trf F.O a.pt (F.toY b.pt) = F.O := hst
    rw [hk] at k
    have e := pline_eq_of_mem k
    rw [pline_of_mem F.O_yl] at e
    have hay : a.pt ∈ (F.yl : L) := by rw [e]; exact mem_pline _ _
    exact eq_of_mem_not_lpar F.nl_xy a.mem hay F.O_xl F.O_yl
  have hb : b.pt = F.O := by
    have hk : trf F.O a.pt (F.toY b.pt) = F.O := hst
    rw [ha, trf_self hD] at hk
    simp only [id] at hk
    rw [← F.toX_toY b.pt b.mem, hk, F.toX_O]
  refine ⟨?_, ?_⟩
  · rw [hs]; exact congrArg MulOpposite.op (Seg.ext ha)
  · rw [ht]; exact congrArg MulOpposite.op (Seg.ext hb)

theorem span_EE' :
    ⊤ ≤ Submodule.span (Seg F)ᵐᵒᵖ (Set.range ![(ofP F.E : Vec F), ofP F.E']) := by
  intro X _
  rw [← ofP_toP X, decomp (toP X)]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- **The basis `E, E'`** of the plane over the segments. -/
noncomputable def basisEE' : Module.Basis (Fin 2) (Seg F)ᵐᵒᵖ (Vec F) :=
  Module.Basis.mk linearIndependent_EE' span_EE'

theorem finrank_eq_two : Module.finrank (Seg F)ᵐᵒᵖ (Vec F) = 2 := by
  rw [Module.finrank_eq_card_basis (basisEE' (F := F))]; simp

end Vec

/-! ### Lines are affine lines -/

open Vec in
/-- The points of the line through `O` and `W ≠ O` are the multiples of `W`. -/
theorem mem_ln_O_iff {W X : P} (hW : W ≠ F.O) :
    X ∈ (ln F.O W : L) ↔ ∃ r : (Seg F)ᵐᵒᵖ, (ofP X : Vec F) = r • ofP W := by
  have hD := hDF.out
  constructor
  · intro hX
    by_cases hX0 : X = F.O
    · exact ⟨0, by rw [zero_smul, hX0]; rfl⟩
    obtain ⟨σ, hσ, hσO, hσW⟩ := exists_cdil (L := L) hD hW hX0 hX
    have hσE : σ F.E ∈ (F.xl : L) := hσ.mem_of_fix hσO F.O_xl F.E_xl
    have e := dl_eq_of hD F.hOE hσE hσ hσO rfl
    refine ⟨MulOpposite.op ⟨σ F.E, hσE⟩, ?_⟩
    rw [smul_def]
    simp only [MulOpposite.unop_op, toP_ofP]
    rw [← e, hσW]
  · rintro ⟨r, hr⟩
    have h : X = dl F.O F.E (MulOpposite.unop r).pt W := hr
    have := dl_mem hD F (MulOpposite.unop r).mem (mem_ln_left F.O W) (mem_ln_right F.O W)
    rw [← h] at this; exact this

open Vec in
/-- **The lines of the plane are the affine lines** `{r (B - A) + A}` of the vector space. -/
theorem mem_ln_iff_smul {A B X : P} (hAB : A ≠ B) :
    X ∈ (ln A B : L) ↔
      ∃ r : (Seg F)ᵐᵒᵖ, (ofP X : Vec F) = r • (ofP B - ofP A) + ofP A := by
  have hD := hDF.out
  have hW : toP (ofP B - ofP A : Vec F) ≠ F.O := by
    intro h
    have : (ofP B - ofP A : Vec F) = 0 := h
    exact hAB (sub_eq_zero.1 this).symm
  have key : X ∈ (ln A B : L) ↔
      toP (ofP X - ofP A : Vec F) ∈ (ln F.O (toP (ofP B - ofP A : Vec F)) : L) := by
    constructor
    · intro hX
      have hτ := (trf_isTr hD F.O (toP (-(ofP A : Vec F)))).1
      have e1 : ∀ Y : P, trf F.O (toP (-(ofP A : Vec F))) Y = toP (ofP Y - ofP A : Vec F) :=
        fun Y => by rw [sub_eq_add_neg, add_comm]; rfl
      have h1 := hτ.map_line (mem_ln_left A B) hX
      have h2 := hτ.map_line (mem_ln_left A B) (mem_ln_right A B)
      have h0 : toP (0 : Vec F) = F.O := rfl
      rw [e1, e1, sub_self, h0] at h1 h2
      rw [← ln_eq (Ne.symm hW) (mem_pline _ _) h2] at h1
      exact h1
    · intro hX
      have hτ := (trf_isTr hD F.O A).1
      have e1 : ∀ Y : Vec F, trf F.O A (toP Y) = toP (Y + ofP A) := fun Y => by
        rw [add_comm]; rfl
      have h1 := hτ.map_line (mem_ln_left F.O _) hX
      have h2 := hτ.map_line (mem_ln_left F.O _) (mem_ln_right F.O (toP (ofP B - ofP A : Vec F)))
      rw [e1, sub_add_cancel] at h1
      rw [e1, sub_add_cancel] at h2
      have hO : trf F.O A F.O = A := trf_O hD F.O A
      rw [hO] at h1 h2
      rw [← ln_eq hAB (mem_pline _ _) h2] at h1
      exact h1
  rw [key, mem_ln_O_iff hW]
  simp only [ofP_toP]
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [← hr, sub_add_cancel]⟩
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [hr, add_sub_cancel_right]⟩

end VecSpace

end DesAlg

end HilbertFoundations
