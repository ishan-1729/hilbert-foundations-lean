import HilbertFoundations.AreasAux5

/-!
# Helper module for `Areas.lean`: polygons of equal measure are of equal content

This module contains no unit of Hilbert's text. Over a linearly ordered field `K`:

* **adding polygons of equal content** (`KEqContent.add`), with copies placed far away;
* **right triangles of equal measure** are of equal content (`rescale`, Hilbert's argument of § 21:
  the shear `BC'C`, `BC'B'` and the common triangle `ABC'`);
* every triangle is of equal content with a right triangle at the origin (`tri_to_rt`), and with
  the standard triangle `Tstd x g` of base `g` on the axis `x` and apex `(0, 2)` (measure `g`);
* every polygon is of equal content with a standard triangle (`poly_to_Tstd`), whence **polygons
  of equal measure are of equal content** (`KEqContent.of_kmeasure`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Adding polygons of equal content -/

theorem KComposed.sub_left {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) :
    ∀ p, S1 p → U p := by
  obtain ⟨l1, l2, -, -, h1, h2, hU⟩ := h
  intro p hp
  obtain ⟨r, hr, hrp⟩ := (h1.2.2 p).1 hp
  exact (hU.2.2 p).2 ⟨r, List.mem_append_left _ hr, hrp⟩

theorem KComposed.sub_right {U S1 S2 : K × K → Prop} (h : KComposed U S1 S2) :
    ∀ p, S2 p → U p := h.comm.sub_left

theorem perm_swap_mid {α : Type*} (l1 l2 l3 l4 : List α) :
    List.Perm (((l1 ++ l2) ++ l3) ++ l4) ((l1 ++ l3) ++ (l2 ++ l4)) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left l1 ?_
  have : List.Perm ((l2 ++ l3) ++ l4) ((l3 ++ l2) ++ l4) :=
    List.perm_append_comm.append_right l4
  simpa only [List.append_assoc] using this

/-- **Polygons composed of parts of equal content are of equal content.** -/
theorem KEqContent.add {U V S1 S2 T1 T2 : K × K → Prop} (hU : KComposed U S1 S2)
    (hV : KComposed V T1 T2) (h1 : KEqContent S1 T1) (h2 : KEqContent S2 T2) :
    KEqContent U V := by
  obtain ⟨S1', T1', U1, V1, pS1', pT1', e1', cU1, cV1, e1⟩ := h1
  obtain ⟨S2', T2', U2, V2, pS2', pT2', e2', cU2, cV2, e2⟩ := h2
  obtain ⟨l1, l2, n1, n2, d1, d2, dU⟩ := id hU
  obtain ⟨m1, m2, k1, k2, f1, f2, dV⟩ := id hV
  obtain ⟨lS1', nS1', dS1'⟩ := pS1'
  obtain ⟨lS2', nS2', dS2'⟩ := pS2'
  obtain ⟨lT1', nT1', dT1'⟩ := pT1'
  obtain ⟨lT2', nT2', dT2'⟩ := pT2'
  -- copies of the added polygons, far away from everything and from each other
  obtain ⟨φ1, hφ1⟩ := far_obst dS1' (l1 ++ l2) dU.1
  have dA1 := dS1'.mapI φ1
  set LA1 := lS1'.map (fun r => r.mapI φ1)
  obtain ⟨φ2, hφ2⟩ := far_obst dS2' ((l1 ++ l2) ++ LA1) (fun r hr => by
    rcases List.mem_append.1 hr with h | h
    · exact dU.1 r h
    · exact dA1.1 r h)
  have dA2 := dS2'.mapI φ2
  set LA2 := lS2'.map (fun r => r.mapI φ2)
  obtain ⟨ψ1, hψ1⟩ := far_obst dT1' (m1 ++ m2) dV.1
  have dB1 := dT1'.mapI ψ1
  set LB1 := lT1'.map (fun r => r.mapI ψ1)
  obtain ⟨ψ2, hψ2⟩ := far_obst dT2' ((m1 ++ m2) ++ LB1) (fun r hr => by
    rcases List.mem_append.1 hr with h | h
    · exact dV.1 r h
    · exact dB1.1 r h)
  have dB2 := dT2'.mapI ψ2
  set LB2 := lT2'.map (fun r => r.mapI ψ2)
  set A1 := imgI φ1 S1'
  set A2 := imgI φ2 S2'
  set B1 := imgI ψ1 T1'
  set B2 := imgI ψ2 T2'
  have nA1 : LA1 ≠ [] := by simp [LA1, nS1']
  have nA2 : LA2 ≠ [] := by simp [LA2, nS2']
  have nB1 : LB1 ≠ [] := by simp [LB1, nT1']
  have nB2 : LB2 ≠ [] := by simp [LB2, nT2']
  have UA1 := disj_of_obst dU (fun r hr => hr) hφ1
  have UA2 := disj_of_obst dU (fun r hr => List.mem_append_left _ hr) hφ2
  have A1A2 := disj_of_obst dA1 (fun r hr => List.mem_append_right _ hr) hφ2
  have VB1 := disj_of_obst dV (fun r hr => hr) hψ1
  have VB2 := disj_of_obst dV (fun r hr => List.mem_append_left _ hr) hψ2
  have B1B2 := disj_of_obst dB1 (fun r hr => List.mem_append_right _ hr) hψ2
  have sU1 := hU.sub_left
  have sU2 := hU.sub_right
  have sV1 := hV.sub_left
  have sV2 := hV.sub_right
  -- the parts with their copies
  have dX1 := d1.append_disjoint dA1 (fun p hp => UA1 p (sU1 p hp))
  have dX2 := d2.append_disjoint dA2 (fun p hp => UA2 p (sU2 p hp))
  have dY1 := f1.append_disjoint dB1 (fun p hp => VB1 p (sV1 p hp))
  have dY2 := f2.append_disjoint dB2 (fun p hp => VB2 p (sV2 p hp))
  have cX1 : KComposed (fun p => S1 p ∨ A1 p) S1 A1 := ⟨l1, LA1, n1, nA1, d1, dA1, dX1⟩
  have cX2 : KComposed (fun p => S2 p ∨ A2 p) S2 A2 := ⟨l2, LA2, n2, nA2, d2, dA2, dX2⟩
  have cY1 : KComposed (fun p => T1 p ∨ B1 p) T1 B1 := ⟨m1, LB1, k1, nB1, f1, dB1, dY1⟩
  have cY2 : KComposed (fun p => T2 p ∨ B2 p) T2 B2 := ⟨m2, LB2, k2, nB2, f2, dB2, dY2⟩
  have eX1 : KEqArea (fun p => S1 p ∨ A1 p) (fun p => T1 p ∨ B1 p) := by
    have a := KEqArea.combine cX1 cU1 (KEqArea.refl d1) (KEqArea.mapI dS1' φ1).symm
    have b := KEqArea.combine cV1 cY1 (KEqArea.refl f1) (KEqArea.mapI dT1' ψ1)
    exact KEqArea.trans (KEqArea.trans a e1.symm) b.symm
  have eX2 : KEqArea (fun p => S2 p ∨ A2 p) (fun p => T2 p ∨ B2 p) := by
    have a := KEqArea.combine cX2 cU2 (KEqArea.refl d2) (KEqArea.mapI dS2' φ2).symm
    have b := KEqArea.combine cV2 cY2 (KEqArea.refl f2) (KEqArea.mapI dT2' ψ2)
    exact KEqArea.trans (KEqArea.trans a e2.symm) b.symm
  -- the big polygons
  have dUA := (dU.append_disjoint dA1 UA1).append_disjoint dA2
    (fun p hp => hp.elim (UA2 p) (A1A2 p))
  have dVB := (dV.append_disjoint dB1 VB1).append_disjoint dB2
    (fun p hp => hp.elim (VB2 p) (B1B2 p))
  have cUs : KComposed (fun p => (U p ∨ A1 p) ∨ A2 p) (fun p => S1 p ∨ A1 p)
      (fun p => S2 p ∨ A2 p) :=
    ⟨l1 ++ LA1, l2 ++ LA2, by simp [n1], by simp [n2], dX1, dX2,
      dUA.perm (perm_swap_mid l1 l2 LA1 LA2)⟩
  have cVs : KComposed (fun p => (V p ∨ B1 p) ∨ B2 p) (fun p => T1 p ∨ B1 p)
      (fun p => T2 p ∨ B2 p) :=
    ⟨m1 ++ LB1, m2 ++ LB2, by simp [k1], by simp [k2], dY1, dY2,
      dVB.perm (perm_swap_mid m1 m2 LB1 LB2)⟩
  have dXs := dA1.append_disjoint dA2 A1A2
  have dYs := dB1.append_disjoint dB2 B1B2
  have cUX : KComposed (fun p => (U p ∨ A1 p) ∨ A2 p) U (fun p => A1 p ∨ A2 p) :=
    ⟨l1 ++ l2, LA1 ++ LA2, by simp [n1], by simp [nA1], dU, dXs, by
      simpa only [List.append_assoc] using dUA⟩
  have cVY : KComposed (fun p => (V p ∨ B1 p) ∨ B2 p) V (fun p => B1 p ∨ B2 p) :=
    ⟨m1 ++ m2, LB1 ++ LB2, by simp [k1], by simp [nB1], dV, dYs, by
      simpa only [List.append_assoc] using dVB⟩
  have eA1B1 : KEqArea A1 B1 :=
    KEqArea.trans (KEqArea.trans (KEqArea.mapI dS1' φ1).symm e1'.symm) (KEqArea.mapI dT1' ψ1).symm
  have eA2B2 : KEqArea A2 B2 :=
    KEqArea.trans (KEqArea.trans (KEqArea.mapI dS2' φ2).symm e2'.symm) (KEqArea.mapI dT2' ψ2).symm
  exact ⟨_, _, _, _, ⟨_, by simp [nA1], dXs⟩, ⟨_, by simp [nB1], dYs⟩,
    KEqArea.combine ⟨LA1, LA2, nA1, nA2, dA1, dA2, dXs⟩ ⟨LB1, LB2, nB1, nB2, dB1, dB2, dYs⟩
      eA1B1 eA2B2, cUX, cVY, KEqArea.combine cUs cVs eX1 eX2⟩

/-- Polygons with the same points are of equal content. -/
theorem KEqContent.of_iff {S T : K × K → Prop} (hS : KPoly S) (h : ∀ p, S p ↔ T p) :
    KEqContent S T :=
  (KEqContent.refl hS).congr (fun _ => Iff.rfl) h

theorem KEqContent.of_trEquiv {t t' : Tr K} (ht : t.nd) (h : TrEquiv t t') :
    KEqContent t.mem t'.mem := KEqContent.of_iff (KPoly.tri ht) h.2.1

/-- An isometric image of a triangle has equal content. -/
theorem KEqContent.of_iso {t : Tr K} (ht : t.nd) (φ : KIso K) :
    KEqContent t.mem (t.mapI φ).mem :=
  (KEqArea.toContent ⟨[t], [t.mapI φ], DecS.single ht, DecS.single ((Tr.nd_mapI φ).2 ht),
    List.Forall₂.cons (KCong.mapI t φ) List.Forall₂.nil⟩ (KPoly.tri ht))

/-! ### Right triangles -/

/-- The right triangle with the legs `β`, `γ` on the axes. -/
def rt (β γ : K) : Tr K := ⟨(0, 0), (β, 0), (0, γ)⟩

theorem rt_D (β γ : K) : (rt β γ).D = β * γ := by simp only [rt, Tr.D, det3]; ring

theorem rt_nd {β γ : K} (hβ : β ≠ 0) (hγ : γ ≠ 0) : (rt β γ).nd := by
  show (rt β γ).D ≠ 0; rw [rt_D]; exact mul_ne_zero hβ hγ

theorem rescale_lt {β γ β' γ' : K} (hβ : 0 < β) (hγ : 0 < γ) (hβ' : 0 < β') (hγ' : 0 < γ')
    (h : β * γ = β' * γ') (hlt : β < β') : KEqContent (rt β γ).mem (rt β' γ').mem := by
  have hγlt : γ' < γ := by
    by_contra hc; push Not at hc
    have : β * γ < β' * γ' := by nlinarith
    linarith
  set O : K × K := (0, 0)
  set B : K × K := (β, 0)
  set C : K × K := (0, γ)
  set B' : K × K := (β', 0)
  set C' : K × K := (0, γ')
  -- the first triangle: `BOC` cut at `C'`
  have n1 : (Tr.mk B O C).nd := by
    show det3 B O C ≠ 0
    rw [show det3 B O C = -(β * γ) by simp only [B, O, C, det3]; ring]
    exact neg_ne_zero.2 (mul_ne_zero hβ.ne' hγ.ne')
  have sp1 := split n1 (s := γ' / γ) (div_pos hγ' hγ) ((div_lt_one hγ).2 hγlt)
  have eC' : lerp (γ' / γ) O C = C' := by
    simp only [O, C, C', lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
  simp only at sp1
  rw [eC'] at sp1
  have dR1 : DecS (rt β γ).mem ([Tr.mk B O C'] ++ [Tr.mk B C' C]) :=
    sp1.congr (fun p => Tr.mem_swap (t := rt β γ))
  -- the second triangle: `C'OB'` cut at `B`
  have n2 : (Tr.mk C' O B').nd := by
    show det3 C' O B' ≠ 0
    rw [show det3 C' O B' = β' * γ' by simp only [C', O, B', det3]; ring]
    exact mul_ne_zero hβ'.ne' hγ'.ne'
  have sp2 := split n2 (s := β / β') (div_pos hβ hβ') ((div_lt_one hβ').2 hlt)
  have eB : lerp (β / β') O B' = B := by
    simp only [O, B, B', lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
  simp only at sp2
  rw [eB] at sp2
  have dR2 : DecS (rt β' γ').mem ([Tr.mk C' O B] ++ [Tr.mk C' B B']) :=
    sp2.congr (fun p => (TrEquiv.rot2 O B' C').2.1 p)
  have nBOC' : (Tr.mk B O C').nd := sp1.1 _ (by simp)
  have nBC'C : (Tr.mk B C' C).nd := sp1.1 _ (by simp)
  have nC'OB : (Tr.mk C' O B).nd := sp2.1 _ (by simp)
  have nC'BB' : (Tr.mk C' B B').nd := sp2.1 _ (by simp)
  have c1 : KComposed (rt β γ).mem (Tr.mk B O C').mem (Tr.mk B C' C).mem :=
    ⟨_, _, by simp, by simp, DecS.single nBOC', DecS.single nBC'C, dR1⟩
  have c2 : KComposed (rt β' γ').mem (Tr.mk C' O B).mem (Tr.mk C' B B').mem :=
    ⟨_, _, by simp, by simp, DecS.single nC'OB, DecS.single nC'BB', dR2⟩
  -- the common triangle
  have k1 : KEqContent (Tr.mk B O C').mem (Tr.mk C' O B).mem :=
    KEqContent.of_trEquiv nBOC'
      (((TrEquiv.swap (Tr.mk O C' B)).trans (TrEquiv.rot (Tr.mk B O C'))).symm)
  -- the shear of `BC'C` into `BC'B'`
  have hD : det3 B C' C ≠ 0 := nBC'C
  have k2 := shear_K hD (-(β' / β))
  have eB' : shift C B C' (-(β' / β)) = B' := by
    simp only [B, C, C', B', shift]
    have := hβ.ne'
    refine Prod.ext ?_ ?_ <;> simp only
    · field_simp
      ring
    · field_simp
      linear_combination h
  rw [eB'] at k2
  have k2' : KEqContent (Tr.mk B C' C).mem (Tr.mk C' B B').mem :=
    k2.congr (fun _ => Iff.rfl) (fun p => (TrEquiv.swap (Tr.mk C' B B')).2.1 p)
  exact KEqContent.add c1 c2 k1 k2'

/-- **Right triangles of equal measure are of equal content** (§ 21). -/
theorem rescale {β γ β' γ' : K} (hβ : 0 < β) (hγ : 0 < γ) (hβ' : 0 < β') (hγ' : 0 < γ')
    (h : β * γ = β' * γ') : KEqContent (rt β γ).mem (rt β' γ').mem := by
  rcases lt_trichotomy β β' with hlt | rfl | hlt
  · exact rescale_lt hβ hγ hβ' hγ' h hlt
  · have : γ = γ' := mul_left_cancel₀ hβ.ne' h
    subst this
    exact KEqContent.refl (KPoly.tri (rt_nd hβ.ne' hγ.ne'))
  · exact (rescale_lt hβ' hγ' hβ hγ h.symm hlt).symm

/-! ### Standard triangles -/

/-- The standard triangle with the base `[x, x + g]` on the axis `x` and the apex `(0, 2)`. -/
def Tstd (x g : K) : Tr K := ⟨(x, 0), (x + g, 0), (0, 2)⟩

theorem Tstd_D (x g : K) : (Tstd x g).D = 2 * g := by simp only [Tstd, Tr.D, det3]; ring

theorem Tstd_nd {x g : K} (hg : g ≠ 0) : (Tstd x g).nd := by
  show (Tstd x g).D ≠ 0; rw [Tstd_D]; exact mul_ne_zero two_ne_zero hg

theorem kmeasure_Tstd {x g : K} (hg : 0 < g) : kmeasure (Tstd x g).mem = g := by
  rw [kmeasure_of_decS (DecS.single (Tstd_nd hg.ne'))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Tstd_D]
  rw [abs_of_pos (by positivity : (0 : K) < 2 * g)]
  ring

/-- The fan: `Tstd x (g + h)` is composed of `Tstd x g` and `Tstd (x + g) h`. -/
theorem Tstd_fan {x g h : K} (hg : 0 < g) (hh : 0 < h) :
    KComposed (Tstd x (g + h)).mem (Tstd x g).mem (Tstd (x + g) h).mem := by
  have hgh : 0 < g + h := add_pos hg hh
  have n0 : (Tr.mk (0, 2) (x, 0) (x + (g + h), 0) : Tr K).nd := by
    show det3 _ _ _ ≠ 0
    rw [show det3 ((0 : K), (2 : K)) (x, 0) (x + (g + h), 0) = 2 * (g + h) by
      simp only [det3]; ring]
    exact mul_ne_zero two_ne_zero hgh.ne'
  have sp := split n0 (s := g / (g + h)) (div_pos hg hgh) ((div_lt_one hgh).2 (by linarith))
  have eX : lerp (g / (g + h)) (x, 0) (x + (g + h), 0) = ((x + g, 0) : K × K) := by
    simp only [lerp]; refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
  simp only at sp
  rw [eX] at sp
  have d := sp.congr (fun p => (TrEquiv.rot2 (x, 0) (x + (g + h), 0) (0, 2)).2.1 p)
  have d' : DecS (Tstd x (g + h)).mem ([Tstd x g] ++ [Tstd (x + g) h]) := by
    refine d.replace (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
    · exact TrEquiv.rot2 (x, 0) (x + g, 0) (0, 2)
    · have e : (Tr.mk (x + g, 0) (x + (g + h), 0) (0, 2) : Tr K) = Tstd (x + g) h := by
        simp only [Tstd]; refine Tr.ext rfl ?_ rfl; refine Prod.ext ?_ rfl; simp only; ring
      exact (TrEquiv.rot2 (x + g, 0) (x + (g + h), 0) (0, 2)).trans (TrEquiv.of_eq e)
  exact ⟨_, _, by simp, by simp, DecS.single (Tstd_nd hg.ne'), DecS.single (Tstd_nd hh.ne'), d'⟩

/-- Moving the base of a standard triangle along the axis `x`. -/
theorem Tstd_move {g : K} (hg : 0 < g) (x : K) :
    KEqContent (Tstd 0 g).mem (Tstd x g).mem := by
  -- translate by `(x, 0)`, then shear the apex back to `(0, 2)`
  let φ : KIso K := ⟨(0, 0), (x, 0), 1, 0, 1, by ring, by ring⟩
  have k1 := KEqContent.of_iso (Tstd_nd (x := 0) hg.ne') φ
  have e1 : (Tstd 0 g).mapI φ = Tr.mk (x, 0) (x + g, 0) (x, 2) := by
    simp only [Tstd, Tr.mapI, KIso.app, φ]
    refine Tr.ext ?_ ?_ ?_ <;> refine Prod.ext ?_ ?_ <;> simp only <;> ring
  rw [e1] at k1
  have hD : det3 ((x, 0) : K × K) (x + g, 0) (x, 2) ≠ 0 := by
    rw [show det3 ((x, 0) : K × K) (x + g, 0) (x, 2) = 2 * g by simp only [det3]; ring]
    exact mul_ne_zero two_ne_zero hg.ne'
  have k2 := shear_K hD (-(x / g))
  have e2 : shift ((x, 2) : K × K) (x, 0) (x + g, 0) (-(x / g)) = (0, 2) := by
    simp only [shift]; refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
  rw [e2] at k2
  exact KEqContent.trans k1 k2.symm

/-! ### Every triangle is of equal content with a standard triangle -/

/-- Reflections to make the legs positive. -/
theorem rt_abs {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    KEqContent (rt x y).mem (rt |x| |y|).mem := by
  set σ : K := if 0 < x then 1 else -1 with hσ
  set τ : K := if 0 < y then 1 else -1 with hτ
  have hσ2 : σ * σ = 1 := by simp only [hσ]; split_ifs <;> ring
  have hτ2 : τ * τ = 1 := by simp only [hτ]; split_ifs <;> ring
  have hσx : σ * x = |x| := by
    simp only [hσ]; split_ifs with h
    · rw [abs_of_pos h]; ring
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hx)]; ring
  have hτy : τ * y = |y| := by
    simp only [hτ]; split_ifs with h
    · rw [abs_of_pos h]; ring
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hy)]; ring
  let φ : KIso K := ⟨(0, 0), (0, 0), σ, 0, σ * τ, by linear_combination hσ2,
    by linear_combination τ * τ * hσ2 + hτ2⟩
  have k := KEqContent.of_iso (rt_nd hx hy) φ
  have e : (rt x y).mapI φ = rt |x| |y| := by
    simp only [rt, Tr.mapI, KIso.app, φ]
    refine Tr.ext ?_ ?_ ?_ <;> refine Prod.ext ?_ ?_ <;> simp only
    · ring
    · ring
    · rw [← hσx]; ring
    · ring
    · ring
    · rw [← hτy]; linear_combination y * τ * hσ2
  rw [e] at k
  exact k

/-- **Every triangle is of equal content with a right triangle with positive legs on the
axes.** -/
theorem tri_to_rt {t : Tr K} (ht : t.nd) :
    ∃ β γ : K, 0 < β ∧ 0 < γ ∧ KEqContent t.mem (rt β γ).mem := by
  -- move the vertex `a` to the origin
  let φ : KIso K := ⟨t.a, (0, 0), 1, 0, 1, by ring, by ring⟩
  have k1 := KEqContent.of_iso ht φ
  set u : K × K := (t.b.1 - t.a.1, t.b.2 - t.a.2)
  set w : K × K := (t.c.1 - t.a.1, t.c.2 - t.a.2)
  have e1 : t.mapI φ = Tr.mk (0, 0) u w := by
    simp only [Tr.mapI, KIso.app, φ, u, w]
    refine Tr.ext ?_ ?_ ?_ <;> refine Prod.ext ?_ ?_ <;> simp only <;> ring
  rw [e1] at k1
  have hD : u.1 * w.2 - u.2 * w.1 ≠ 0 := by
    have : t.D ≠ 0 := ht
    simp only [Tr.D, det3] at this
    simp only [u, w]; exact this
  -- a triangle `0, (x, 0), q` with `x ≠ 0`, `q.2 ≠ 0` is of equal content with `rt x q.2`
  have step : ∀ (x : K) (q : K × K), x ≠ 0 → q.2 ≠ 0 →
      KEqContent (Tr.mk (0, 0) (x, 0) q).mem (rt x q.2).mem := by
    intro x q hx hq
    have hD' : det3 ((0, 0) : K × K) (x, 0) q ≠ 0 := by
      rw [show det3 ((0, 0) : K × K) (x, 0) q = x * q.2 by simp only [det3]; ring]
      exact mul_ne_zero hx hq
    have k := shear_K hD' (-(q.1 / x))
    have e : shift q (0, 0) (x, 0) (-(q.1 / x)) = (0, q.2) := by
      simp only [shift]; refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
    rw [e] at k
    exact k
  -- reduce to a triangle with a side on the axis `x`
  have k2 : ∃ x y : K, x ≠ 0 ∧ y ≠ 0 ∧ KEqContent (Tr.mk (0, 0) u w).mem (rt x y).mem := by
    by_cases hu : u.2 = 0
    · have hx : u.1 ≠ 0 := by intro e; apply hD; rw [e, hu]; ring
      have hy : w.2 ≠ 0 := by intro e; apply hD; rw [e, hu]; ring
      have eu : u = (u.1, 0) := Prod.ext rfl hu
      refine ⟨u.1, w.2, hx, hy, ?_⟩
      have := step u.1 w hx hy
      rw [← eu] at this
      exact this
    · -- shear `w` onto the axis `x`
      have hD0 : det3 ((0, 0) : K × K) u w ≠ 0 := by
        rw [show det3 ((0, 0) : K × K) u w = u.1 * w.2 - u.2 * w.1 by simp only [det3]; ring]
        exact hD
      have ka := shear_K hD0 (-(w.2 / u.2))
      set x := w.1 - w.2 / u.2 * u.1
      have ew : shift w (0, 0) u (-(w.2 / u.2)) = (x, 0) := by
        simp only [shift, x]; refine Prod.ext ?_ ?_ <;> simp only <;> field_simp <;> ring
      rw [ew] at ka
      have hx : x ≠ 0 := by
        intro e
        apply hD
        simp only [x] at e
        field_simp at e
        linear_combination -e
      have kb : KEqContent (Tr.mk (0, 0) u (x, 0)).mem (Tr.mk (0, 0) (x, 0) u).mem :=
        KEqContent.of_trEquiv (by
          show det3 _ _ _ ≠ 0
          rw [show det3 ((0, 0) : K × K) u (x, 0) = -(x * u.2) by simp only [det3]; ring]
          exact neg_ne_zero.2 (mul_ne_zero hx hu)) (TrEquiv.swap23 (0, 0) (x, 0) u)
      exact ⟨x, u.2, hx, hu, KEqContent.trans (KEqContent.trans ka kb.symm) (step x u hx hu).symm⟩
  obtain ⟨x, y, hx, hy, k3⟩ := k2
  refine ⟨|x|, |y|, abs_pos.2 hx, abs_pos.2 hy, ?_⟩
  exact KEqContent.trans (KEqContent.trans k1 k3.symm) (rt_abs hx hy).symm

/-- **Every triangle is of equal content with the standard triangle of the same measure.** -/
theorem tri_to_Tstd {t : Tr K} (ht : t.nd) (x : K) :
    KEqContent t.mem (Tstd x (|t.D| / 2)).mem := by
  obtain ⟨β, γ, hβ, hγ, k1⟩ := tri_to_rt ht
  have hg : 0 < β * γ / 2 := by positivity
  have k2 := rescale hβ hγ hg two_pos (by ring : β * γ = (β * γ / 2) * 2)
  have e : rt (β * γ / 2) 2 = Tstd 0 (β * γ / 2) := by
    simp only [rt, Tstd, zero_add]
  rw [e] at k2
  have k3 := Tstd_move hg x
  have k := KEqContent.trans (KEqContent.trans k1 k2.symm) k3.symm
  -- the measure identifies the base
  have hm := k.kmeasure_eq
  rw [kmeasure_of_decS (DecS.single ht), kmeasure_Tstd hg] at hm
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hm
  rw [hm]
  exact k

/-- **Every polygon is of equal content with a standard triangle.** -/
theorem poly_to_Tstd : ∀ (l : List (Tr K)) (S : K × K → Prop) (x : K), DecS S l → l ≠ [] →
    KEqContent S (Tstd x ((l.map (fun r => |r.D|)).sum / 2)).mem
  | [], _, _, _, h => absurd rfl h
  | [t], S, x, h, _ => by
    have ht := h.1 t (by simp)
    have := tri_to_Tstd ht x
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact this.congr (fun p => by rw [h.2.2 p]; simp) (fun _ => Iff.rfl)
  | t :: t' :: l, S, x, h, _ => by
    have ht := h.1 t (by simp)
    have hl' : t' :: l ≠ [] := by simp
    have dS' : DecS (fun p => ∃ r ∈ t' :: l, r.mem p) (t' :: l) :=
      ⟨fun r hr => h.1 r (List.mem_cons_of_mem _ hr), (List.pairwise_cons.1 h.2.1).2,
        fun p => Iff.rfl⟩
    have cS : KComposed S t.mem (fun p => ∃ r ∈ t' :: l, r.mem p) :=
      ⟨[t], t' :: l, by simp, hl', DecS.single ht, dS', h⟩
    have hg : 0 < |t.D| / 2 := by have := abs_pos.2 ht; positivity
    have hG : 0 < ((t' :: l).map (fun r => |r.D|)).sum / 2 := by
      have := kmeasure_pos dS' hl'
      rwa [kmeasure_of_decS dS'] at this
    have ih := poly_to_Tstd (t' :: l) (fun p => ∃ r ∈ t' :: l, r.mem p) (x + |t.D| / 2) dS' hl'
    have fan := Tstd_fan (x := x) hg hG
    have e : ((t :: t' :: l).map (fun r => |r.D|)).sum / 2 =
        |t.D| / 2 + ((t' :: l).map (fun r => |r.D|)).sum / 2 := by
      rw [List.map_cons, List.sum_cons]; ring
    rw [e]
    exact KEqContent.add cS fan (tri_to_Tstd ht x) ih

/-- **Polygons of equal measure are of equal content.** -/
theorem KEqContent.of_kmeasure {S T : K × K → Prop} (hS : KPoly S) (hT : KPoly T)
    (h : kmeasure S = kmeasure T) : KEqContent S T := by
  obtain ⟨lS, nS, dS⟩ := hS
  obtain ⟨lT, nT, dT⟩ := hT
  have k1 := poly_to_Tstd lS S 0 dS nS
  have k2 := poly_to_Tstd lT T 0 dT nT
  rw [← kmeasure_of_decS dS] at k1
  rw [← kmeasure_of_decS dT, ← h] at k2
  exact KEqContent.trans k1 k2

end Areas

end HilbertFoundations
