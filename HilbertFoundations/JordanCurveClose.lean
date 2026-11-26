import HilbertFoundations.Commentary
import JordanPick.JordanCurve

/-!
# Appendix: Jordan's curve theorem

This file proves the unit `app.jordan_theorem` of `Commentary.lean`, which is only stated there:
`Appendix.jordanCurveTheorem : JordanCurveTheorem`. A closed Jordan curve `γ : ℝ → ℂ` (continuous,
of period `1`, injective on `[0, 1)`) divides the number plane into a bounded and an unbounded
connected component, and the curve is the frontier of each of them.

The Jordan curve theorem itself is not proved here. It is the proof in the library `JordanPick`
(directory `JordanPick/` of this repository): four files of the repository
<https://github.com/rkirov/jordan_pick> by Rado Kirov, under the Apache License 2.0, copied without
change (commit, list of files and checksums in `JordanPick/README.md`). They prove, for a
continuous injective map `r` of the unit circle `sphere 0 1` of `EuclideanSpace ℝ (Fin 2)` into
`EuclideanSpace ℝ (Fin 2)`, that the complement of `range r` has exactly two connected components
(`JordanCurve.jordan_curve`). The proof there is by Maehara's method (R. Maehara, *The Jordan curve
theorem via the Brouwer fixed point theorem*, Amer. Math. Monthly 91 (1984)), with the Brouwer
fixed point theorem for the plane proved from the lifting of paths along the covering of the
circle by the line. The statements used are

* `JordanCurve.exists_unbounded_component`, `JordanCurve.unbounded_component_unique`: there is
  exactly one unbounded component;
* `JordanCurve.step_A_exists_bounded`, `JordanCurve.step_B_bounded_unique`: there is exactly one
  bounded component;
* `JordanCurve.component_boundary_eq`: when there are two components, the frontier of each is the
  curve;
* `JordanCurve.Brouwer.brouwerFPT`: the Brouwer fixed point theorem for the plane
  (`JordanCurve.BrouwerFPT`), which `step_A_exists_bounded`, `step_B_bounded_unique` and
  `component_boundary_eq` take as a hypothesis.

What is proved here is the transport of these statements to the form of `JordanCurveTheorem`.

1. `IsClosedJordanCurve.exists_sphere_map`: a curve of period `1` is a function on the additive
   circle `AddCircle 1` (`Function.Periodic.lift`), continuous because `AddCircle 1` carries the
   quotient topology, and injective because every point of `AddCircle 1` has a representative in
   `[0, 1)`. Composed with the homeomorphisms `sphere 0 1 ≃ₜ Circle ≃ₜ AddCircle 1`
   (`JordanCurve.Arcs.circleHomeoSphere`, `AddCircle.homeomorphCircle`) and with the isometry
   `JordanCurve.Arcs.complexLIE : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`, it is a continuous injective
   map `r` of `sphere 0 1` whose range is the image of the curve under the isometry.
2. `jordanCurveTheorem_of_isometry`: for a set `J` of `ℂ` and its image `K` under a linear isometry
   `L` of `ℂ` onto `EuclideanSpace ℝ (Fin 2)`, the complement of `K` is the image of the complement
   of `J`, the components of the complement of `K` are the images of those of the complement of `J`
   (`Homeomorph.image_connectedComponentIn`), and `L` preserves boundedness and frontiers
   (`Homeomorph.image_frontier`). So the conclusion of Jordan's theorem for `J` follows from the
   five statements above for `K`.
3. `jordanCurveTheorem`: the two steps together.
-/

namespace HilbertFoundations

namespace Appendix

open Complex Set Metric Function Bornology

/-- A closed Jordan curve of the number plane as a continuous injective map of the unit circle of
`EuclideanSpace ℝ (Fin 2)`: its range is the image of the curve under the isometry
`JordanCurve.Arcs.complexLIE`. -/
theorem IsClosedJordanCurve.exists_sphere_map {γ : ℝ → ℂ} (h : IsClosedJordanCurve γ) :
    ∃ r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous r ∧ Injective r ∧ range r = JordanCurve.Arcs.complexLIE '' range γ := by
  obtain ⟨hc, hp, hi⟩ := h
  -- the curve on the additive circle `ℝ / ℤ`
  have hlc : Continuous (hp.lift : AddCircle (1 : ℝ) → ℂ) := hc.quotient_liftOn' _
  have hli : Injective (hp.lift : AddCircle (1 : ℝ) → ℂ) := by
    intro x y hxy
    have hx : x ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ico 0 (0 + 1) := by
      rw [AddCircle.coe_image_Ico_eq (1 : ℝ) 0]; exact mem_univ x
    have hy : y ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ico 0 (0 + 1) := by
      rw [AddCircle.coe_image_Ico_eq (1 : ℝ) 0]; exact mem_univ y
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    rw [zero_add] at hs ht
    rw [Periodic.lift_coe, Periodic.lift_coe] at hxy
    rw [hi hs ht hxy]
  have hlr : range (hp.lift : AddCircle (1 : ℝ) → ℂ) = range γ := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨(s : AddCircle (1 : ℝ)), rfl⟩
  -- the unit circle of the plane is homeomorphic to `ℝ / ℤ`
  let e : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ AddCircle (1 : ℝ) :=
    JordanCurve.Arcs.circleHomeoSphere.symm.trans (AddCircle.homeomorphCircle one_ne_zero).symm
  refine ⟨fun p => JordanCurve.Arcs.complexLIE (hp.lift (e p)), ?_, ?_, ?_⟩
  · exact JordanCurve.Arcs.complexLIE.continuous.comp (hlc.comp e.continuous)
  · exact JordanCurve.Arcs.complexLIE.injective.comp (hli.comp e.injective)
  · rw [show (fun p => JordanCurve.Arcs.complexLIE (hp.lift (e p)))
        = JordanCurve.Arcs.complexLIE ∘ hp.lift ∘ e from rfl,
      range_comp, range_comp, e.surjective.range_eq, image_univ, hlr]

/-- Transport of the conclusion of Jordan's theorem along a linear isometry `L` of `ℂ` onto
`EuclideanSpace ℝ (Fin 2)`: if the complement of `K = L '' J` has exactly one unbounded and exactly
one bounded component, and every component has frontier `K` as soon as there is another one, then
`J` divides `ℂ` into a bounded and an unbounded component, each with frontier `J`. -/
theorem jordanCurveTheorem_of_isometry (L : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) {J : Set ℂ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : K = L '' J)
    (hub : ∃ x ∈ Kᶜ, ¬IsBounded (connectedComponentIn Kᶜ x))
    (hbd : ∃ x ∈ Kᶜ, IsBounded (connectedComponentIn Kᶜ x))
    (huu : ∀ x y, ¬IsBounded (connectedComponentIn Kᶜ x) →
      ¬IsBounded (connectedComponentIn Kᶜ y) →
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y)
    (hbu : ∀ x ∈ Kᶜ, ∀ y ∈ Kᶜ, IsBounded (connectedComponentIn Kᶜ x) →
      IsBounded (connectedComponentIn Kᶜ y) →
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y)
    (hfr : ∀ x ∈ Kᶜ, (∃ y ∈ Kᶜ, connectedComponentIn Kᶜ y ≠ connectedComponentIn Kᶜ x) →
      frontier (connectedComponentIn Kᶜ x) = K) :
    ∃ z w : ℂ, z ∉ J ∧ w ∉ J ∧
      IsBounded (connectedComponentIn Jᶜ z) ∧ ¬IsBounded (connectedComponentIn Jᶜ w) ∧
      Jᶜ = connectedComponentIn Jᶜ z ∪ connectedComponentIn Jᶜ w ∧
      frontier (connectedComponentIn Jᶜ z) = J ∧ frontier (connectedComponentIn Jᶜ w) = J := by
  -- complements, components, boundedness and frontiers correspond under `L`
  have hKc : Kᶜ = L '' Jᶜ := by rw [hK, image_compl_eq L.bijective]
  have hmem : ∀ a : ℂ, L a ∈ Kᶜ ↔ a ∈ Jᶜ := fun a => by
    rw [hKc]; exact L.injective.mem_set_image
  have hcc : ∀ a ∈ Jᶜ, connectedComponentIn Kᶜ (L a) = L '' connectedComponentIn Jᶜ a :=
    fun a ha => by
      rw [hKc]; exact (L.toHomeomorph.image_connectedComponentIn ha).symm
  have hbdd : ∀ S : Set ℂ, IsBounded (L '' S) ↔ IsBounded S := fun S => by
    refine ⟨fun h => ?_, fun h => L.lipschitzWith.isBounded_image h⟩
    have h' := L.symm.lipschitzWith.isBounded_image h
    rwa [image_image, show (fun x => L.symm (L x)) = id from funext L.symm_apply_apply,
      image_id] at h'
  have hfront : ∀ S : Set ℂ, frontier (L '' S) = L '' J → frontier S = J := fun S h => by
    have h1 : L '' frontier S = frontier (L '' S) := L.toHomeomorph.image_frontier S
    exact image_injective.mpr L.injective (h1.trans h)
  -- the unbounded component is that of `L w`, the bounded one that of `L z`
  obtain ⟨x₀, hx₀, hx₀u⟩ := hub
  obtain ⟨x₁, hx₁, hx₁b⟩ := hbd
  obtain ⟨w, rfl⟩ := L.surjective x₀
  obtain ⟨z, rfl⟩ := L.surjective x₁
  have hw : w ∈ Jᶜ := (hmem w).1 hx₀
  have hz : z ∈ Jᶜ := (hmem z).1 hx₁
  have hne : connectedComponentIn Kᶜ (L w) ≠ connectedComponentIn Kᶜ (L z) :=
    fun h => hx₀u (h ▸ hx₁b)
  have hfz := hfr (L z) hx₁ ⟨L w, hx₀, hne⟩
  have hfw := hfr (L w) hx₀ ⟨L z, hx₁, hne.symm⟩
  rw [hcc z hz, hK] at hfz
  rw [hcc w hw, hK] at hfw
  refine ⟨z, w, hz, hw, (hbdd _).1 (hcc z hz ▸ hx₁b),
    fun h => hx₀u (by rw [hcc w hw]; exact (hbdd _).2 h), ?_, hfront _ hfz, hfront _ hfw⟩
  -- every point of the complement lies in one of the two components
  refine Subset.antisymm (fun a ha => ?_)
    (union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
  have haK : L a ∈ Kᶜ := (hmem a).2 ha
  have haa : L a ∈ connectedComponentIn Kᶜ (L a) := mem_connectedComponentIn haK
  by_cases hab : IsBounded (connectedComponentIn Kᶜ (L a))
  · left
    rw [hbu (L a) haK (L z) hx₁ hab hx₁b, hcc z hz] at haa
    exact L.injective.mem_set_image.1 haa
  · right
    rw [huu (L a) (L w) hab hx₀u, hcc w hw] at haa
    exact L.injective.mem_set_image.1 haa

/-- **Jordan's theorem** (unit `app.jordan_theorem`): a closed Jordan curve divides the number
plane into an inner (bounded) and an outer (unbounded) region, each bounded by the curve. -/
theorem jordanCurveTheorem : JordanCurveTheorem := by
  intro γ hγ
  obtain ⟨r, hcont, hinj, hrange⟩ := hγ.exists_sphere_map
  have hbr : JordanCurve.BrouwerFPT := JordanCurve.Brouwer.brouwerFPT
  exact jordanCurveTheorem_of_isometry JordanCurve.Arcs.complexLIE hrange
    (JordanCurve.exists_unbounded_component r hcont)
    (JordanCurve.step_A_exists_bounded hbr hcont hinj)
    (fun _ _ hx hy => JordanCurve.unbounded_component_unique r hcont hx hy)
    (JordanCurve.step_B_bounded_unique hbr hcont hinj)
    (fun _ hx hy => JordanCurve.component_boundary_eq hbr hcont hinj hx hy)

end Appendix

end HilbertFoundations
