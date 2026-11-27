module

import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Topology.Algebra.ProperAction.Torsor
import Mathlib.Topology.Separation.CompletelyRegular
public import Lib.Adelic.QuotientMeasure.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Monotonicity.Lemmas
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.Adelic.AutomorphicForms.Basic
public import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
import Lib.Adelic.Adeles.StrongApproximation
import Lib.Adelic.Reduction.DefiniteClassSums
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.Rigidity.KernelFixes

section
/-!
# Unfolding over orbits and integration in Iwasawa coordinates

This file proves integration formulas on a quotient `Γ \ G` by a discrete subgroup `Γ`. An integral
over `Γ \ G` of a sum over translates is unfolded to an integral over the quotient by the subgroup
that keeps a block, in particular by the stabiliser of a point. Integrals of functions invariant
under a closed subgroup `N` are then written in Iwasawa coordinates `G = N · i(M) · K`.

* `Γ.quotMeasure μ`: the measure on `G` that integrates left `Γ`-invariant functions over `Γ \ G`.
* `N.FixesLeft F`: `F (γ * g) = F g` for all `γ ∈ N` and `g ∈ G`.

## Main definitions and results

* `New.integral_tsum_eq_integral_tsum_block`: the integral over `Γ \ G` of the sum over all
  translates of a block `C` is the integral over `S \ G` of the sum over `C`, where `S` is the
  group that keeps `C`. `New.integral_tsum_block` adds integrability and termwise integration.
* `New.integral_tsum_orbit_eq_integral_stabilizer`: the case of one orbit, with `S` the image of the
  stabiliser of a point.
* `New.lintegral_iwasawa`: `dn dm dk` in the coordinates `i m * n * k` is a multiple of Haar
  measure.
* `New.integral_quotMeasure_iwasawa`: the integral over `Γ \ G` of a function `F` invariant under
  `N` and `Γ` is a nonzero constant times the integral of `w m * F (i m * k)`, where conjugation by
  `i m` scales the Haar measure of `N` by `w m`.

## Relation to the literature

Known result: The unfolding trick and the integration formula in Iwasawa coordinates on a quotient
by a discrete subgroup. Weil's formula for invariant integration on a quotient is in
`Lib.Adelic.QuotientMeasure.Basic`.
-/

@[expose] public section

/-!
## Unfolding a sum over an orbit

The unfolding trick for sums over a countable set `Y` with an action of a group `Λ`, which `i`
identifies with a discrete subgroup `Γ` of `G`. The summands `k y : G → ℂ` are measurable and
equivariant: `k (γ • y) (i γ * x) = k y x`.
-/

section OrbitUnfolding

open MeasureTheory Measure MulAction ProbabilityTheory ENNReal Set

open scoped Classical in
/-- Let `i` be injective, and let `γ` carry a point of `C` into `C` exactly when `i γ` lies in the
subgroup `S` of the range of `i`. If `β` has sum `1` over each `S`-orbit in `G`, then the sum of
`β (i γ * x)` over the `γ` that carry `y` into `C` is `1`, provided that there is such a `γ`. -/
lemma New.tsum_cutoff_smul_mem_eq_one {Λ G Y : Type*} [Group Λ] [Group G] [MulAction Λ Y]
    {i : Λ →* G} (hi : Function.Injective i) {S : Subgroup G} (hS : S ≤ i.range) {C : Set Y}
    (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S) {β : G → ℝ≥0∞}
    (hβ_one : ∀ x : G, ∑' s : S, β (s * x) = 1) {y : Y} {γ₀ : Λ} (hγ₀ : γ₀ • y ∈ C) (x : G) :
    ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0) = 1 := by
  -- The point `(γ * γ₀) • y` lies in `C` exactly when `i γ ∈ S`.
  let b : G → ℝ≥0∞ := (S : Set G).indicator fun g ↦ β (g * (i γ₀ * x))
  calc ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0)
    _ = ∑' γ : Λ, (if (γ * γ₀) • y ∈ C then β (i (γ * γ₀) * x) else 0) :=
        ((Equiv.mulRight γ₀).tsum_eq _).symm
    _ = ∑' γ : Λ, b (i γ) := by simp [b, indicator, mul_smul, mul_assoc, hC _ _ hγ₀]
    _ = ∑' g : G, b g := hi.tsum_eq fun g hg ↦ hS (support_indicator_subset hg)
    _ = ∑' s : S, β (s * (i γ₀ * x)) := (tsum_subtype (S : Set G) _).symm
    _ = 1 := hβ_one (i γ₀ * x)

/-- If the `k y` are measurable and `∑ ‖k y‖` has finite integral for `ν`, then `(x, y) ↦ k y x` is
integrable for the product of `ν` with the counting measure. -/
lemma New.integrable_prod_count_of_lintegral_lt_top {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y] {ν : Measure X} {k : Y → X → ℂ}
    (hk_meas : ∀ y : Y, Measurable (k y)) (h_fin : ∫⁻ x : X, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞) :
    Integrable (fun p : X × Y ↦ k p.2 p.1) (ν.prod count) := by
  have h_meas : Measurable fun p : X × Y ↦ k p.2 p.1 := measurable_from_prod_countable_left hk_meas
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ h_meas.eNorm.aemeasurable]
  simpa only [lintegral_count] using h_fin

/-- If the `k y` are measurable and `∑ ‖k y‖` has finite integral, then `∑ k y` is integrable. -/
lemma New.integrable_tsum_of_lintegral_lt_top {X Y : Type*} [MeasurableSpace X] [Countable Y]
    {ν : Measure X} {k : Y → X → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (h_fin : ∫⁻ x : X, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞) :
    Integrable (fun x : X ↦ ∑' y : Y, k y x) ν := by
  let : MeasurableSpace Y := ⊤
  have h_prod : Integrable (fun p : X × Y ↦ k p.2 p.1) (ν.prod count) :=
    integrable_prod_count_of_lintegral_lt_top hk_meas h_fin
  simpa only [integral_count_eq_tsum] using h_prod.integral_prod_left

variable {Λ G Y : Type*} [Group Λ] [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [MulAction Λ Y] [Countable Y] {i : Λ →* G}

omit [Group G] [TopologicalSpace G] in
/-- If the `k y` are almost everywhere strongly measurable and `∑ ‖k y‖` has finite integral, then
the integrals of the `k y` sum to the integral of `∑ k y`. -/
lemma New.hasSum_integral_of_lintegral_tsum_lt_top {k : Y → G → ℂ} {ν : Measure G}
    (h_fin : ∫⁻ x : G, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞)
    (h_meas : ∀ y : Y, AEStronglyMeasurable (k y) ν := by fun_prop) :
    HasSum (fun y : Y ↦ ∫ x : G, k y x ∂ν) (∫ x : G, ∑' y : Y, k y x ∂ν) := by
  rw [lintegral_tsum (by fun_prop)] at h_fin
  rw [integral_tsum h_meas h_fin.ne]
  have h_le : ∑' y : Y, ‖∫ x, k y x ∂ν‖ₑ ≤ ∑' y : Y, ∫⁻ x, ‖k y x‖ₑ ∂ν :=
    tsum_le_tsum fun y ↦ eNorm_integral_le_lintegral_eNorm (k y)
  exact (Summable.of_eNorm (h_le.trans_lt h_fin).ne).hasSum

open scoped Classical in
omit [MeasurableSpace G] [Countable Y] in
/-- Let `i` map `Λ` isomorphically onto `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in the subgroup `S` of `Γ`, and let `D` be the union of the translates of `C`. If `β` has
sum `1` over each `S`-orbit in `G`, then the sum of `β (i γ * x)` over the `γ` that carry `y` into
`C` is `1` if `y ∈ D` and `0` otherwise. -/
lemma New.tsum_cutoff_smul_mem_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {C D : Set Y} (hS : S ≤ Γ)
    (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S) (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
    {β : G → ℝ≥0∞} (hβ_one : ∀ x : G, ∑' s : S, β (s * x) = 1) (y : Y) (x : G) :
    ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0) = if y ∈ D then 1 else 0 := by
  subst hΓ
  split_ifs with hy
  · obtain ⟨γ₀, hγ₀⟩ := (hD y).1 hy
    exact tsum_cutoff_smul_mem_eq_one hi hS hC hβ_one hγ₀ x
  · simp [not_exists.1 (mt (hD y).2 hy)]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G]

/-- Unfolding of a sum of nonnegative terms over the translates of a block. Let `i` map `Λ`
isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. For measurable `g y` with
`g (γ • y) (i γ * x) = g y x`, the integral of `∑_D g y` over `Γ \ G` (that is, against
`Γ.quotMeasure μ`) is the integral of `∑_C g y` over `S \ G`. -/
lemma New.lintegral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
    {g : Y → G → ℝ≥0∞} (hg_meas : ∀ y : Y, Measurable (g y))
    (hg_inv : ∀ (γ : Λ) (y : Y) (x : G), g (γ • y) (i γ * x) = g y x) :
    ∫⁻ x : G, ∑' y : D, g y x ∂Γ.quotMeasure μ = ∫⁻ x : G, ∑' y : C, g y x ∂S.quotMeasure μ := by
  classical
  -- With `β` the cutoff of `S`, unfold the integral of `β x * ∑_C g y x` over `G` along `Γ` and
  -- substitute `y ↦ γ • y` in the term of `i γ`.
  have : DiscreteTopology S := .of_subset (s := Γ) inferInstance hS
  let β : G → ℝ≥0∞ := chosenCutoff (count : Measure S)
  obtain ⟨hβ_meas, hβ_int⟩ : IsCutoff (count : Measure S) β := isCutoff_chosenCutoff count
  have hβ_one (x : G) : ∑' s : S, β (s * x) = 1 := by
    simpa [lintegral_count, Subgroup.smul_def] using hβ_int x
  have h_term (γ : Λ) (x : G) : β (i γ * x) * ∑' y : C, g y (i γ * x) =
      ∑' y : Y, (if γ • y ∈ C then β (i γ * x) else 0) * g y x := by
    rw [tsum_subtype C fun y ↦ g y (i γ * x), ← (MulAction.toPerm γ).tsum_eq,
      ← ENNReal.tsum_mul_left]
    simp [indicator, hg_inv]
  have h_sum (x : G) : ∑' δ : Γ, β (δ * x) * ∑' y : C, g y (δ * x) = ∑' y : D, g y x := by
    subst hΓ
    calc ∑' δ : i.range, β (δ * x) * ∑' y : C, g y (δ * x)
      _ = ∑' γ : Λ, β (i γ * x) * ∑' y : C, g y (i γ * x) := ((i.ofInjective hi).tsum_eq _).symm
      _ = ∑' y : Y, (∑' γ : Λ, if γ • y ∈ C then β (i γ * x) else 0) * g y x := by
          simp only [h_term, ← ENNReal.tsum_mul_right]
          exact tsum_comm
      _ = ∑' y : D, g y x := by
          simp [tsum_cutoff_smul_mem_block hi rfl hS hC hD hβ_one, tsum_subtype D fun y ↦ g y x,
            indicator]
  have hS_meas : S.quotMeasure μ = μ.withDensity β := rfl
  calc ∫⁻ x, ∑' y : D, g y x ∂Γ.quotMeasure μ
    _ = ∫⁻ x, ∫⁻ δ : Γ, β (δ • x) * ∑' y : C, g y (δ • x) ∂count ∂Γ.quotMeasure μ := by
        simp only [lintegral_count, ← h_sum, Subgroup.smul_def, smul_eq_mul]
    _ = ∫⁻ x, β x * ∑' y : C, g y x ∂μ :=
        lintegral_orbitMeasure_lintegral (f := fun x ↦ β x * ∑' y : C, g y x) (by fun_prop)
    _ = ∫⁻ x, ∑' y : C, g y x ∂S.quotMeasure μ := by
        simp (disch := fun_prop) [hS_meas, lintegral_withDensity_eq_lintegral_mul]

/-- Let `i` map `Λ` isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into
`C` exactly when `i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. For
measurable `k y` with `k (γ • y) (i γ * x) = k y x`, the integral of `∑_D ‖k y‖` over `Γ \ G` is
the integral of `∑_C ‖k y‖` over `S \ G`. -/
lemma New.lintegral_tsum_enorm_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x) :
    ∫⁻ x : G, ∑' y : D, ‖k y x‖ₑ ∂Γ.quotMeasure μ = ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ :=
  lintegral_tsum_block hi hΓ hS hC hD (g := fun y x ↦ ‖k y x‖ₑ) (fun y ↦ (hk_meas y).eNorm)
    fun γ y x ↦ congrArg eNorm (hk γ y x)

/-- Unfolding of the integral of a sum over the translates of a block. Let `i` map `Λ`
isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. Let the `k y` be
measurable with `k (γ • y) (i γ * x) = k y x`. If `∑_C ‖k y‖` has finite integral over `S \ G`,
then the integral of `∑_D k y` over `Γ \ G` is the integral of `∑_C k y` over `S \ G`. -/
lemma New.integral_tsum_eq_integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    ∫ x : G, ∑' y : D, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  -- The functions `(x, y) ↦ k y x` on `(Γ \ G) × D` and on `(S \ G) × C` have the same
  -- distribution; the claim follows by Fubini.
  let : MeasurableSpace Y := ⊤
  have h_meas : Measurable fun p : Y × G ↦ k p.1 p.2 := measurable_from_prod_countable_right hk_meas
  have h_unfold (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
      ∫⁻ x, ∑' y : D, f (k y x) ∂Γ.quotMeasure μ = ∫⁻ x, ∑' y : C, f (k y x) ∂S.quotMeasure μ :=
    lintegral_tsum_block hi hΓ hS hC hD (g := fun y x ↦ f (k y x)) (by fun_prop) (by simp [hk])
  have h_dist : IdentDistrib (fun p : G × D ↦ k p.2 p.1) (fun p : G × C ↦ k p.2 p.1)
      ((Γ.quotMeasure μ).prod count) ((S.quotMeasure μ).prod count) := by
    refine ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    simpa (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count]
      using h_unfold f hf
  have hC_int : Integrable (fun p : G × C ↦ k p.2 p.1) ((S.quotMeasure μ).prod count) :=
    integrable_prod_count_of_lintegral_lt_top (fun y : C ↦ hk_meas y) h_fin
  have hD_int := h_dist.integrable_iff.2 hC_int
  calc ∫ x, ∑' y : D, k y x ∂Γ.quotMeasure μ
    _ = ∫ p : G × D, k p.2 p.1 ∂(Γ.quotMeasure μ).prod count := by
        simp only [integral_prod _ hD_int, integral_count_eq_tsum]
    _ = ∫ p : G × C, k p.2 p.1 ∂(S.quotMeasure μ).prod count := h_dist.integral_eq
    _ = ∫ x, ∑' y : C, k y x ∂S.quotMeasure μ := by
        simp only [integral_prod _ hC_int, integral_count_eq_tsum]

/-- Unfolding of a sum of integrals over the translates of a block. Let `i` map `Λ` isomorphically
onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when `i γ` lies in
`S ≤ Γ`, and let `D` be the union of the translates of `C`. Let the `k y` be measurable with
`k (γ • y) (i γ * x) = k y x`. If `∑_C ‖k y‖` has finite integral over `S \ G`, then the sum over
`D` of the integrals of `k y` against the measure of `Γ \ G` is the integral of `∑_C k y` over
`S \ G`. -/
lemma New.tsum_integral_eq_integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    ∑' y : D, ∫ x : G, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  rw [← integral_tsum_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin]
  rw [← lintegral_tsum_enorm_block hi hΓ hS hC hD hk_meas hk] at h_fin
  exact (hasSum_integral_of_lintegral_tsum_lt_top h_fin).tsum_eq

/-- Unfolding of a sum over the translates of a block. The group `Λ` acts on `Y` and `i` maps it
isomorphically onto the discrete subgroup `Γ` of `G`; the terms are measurable and satisfy
`k (γ • y) (i γ * x) = k y x`. The block `C ⊆ Y` is such that `γ` carries a point of `C` into `C`
exactly when `i γ` lies in `S ≤ Γ`, and `D` is the union of the translates of `C`. Suppose that
`∑_D ‖k y‖` has finite integral over `Γ \ G` or that `∑_C ‖k y‖` has finite integral over `S \ G`.
Then `∑_C k y` is integrable over `S \ G`. Its integral equals the integral of `∑_D k y` over
`Γ \ G`. It also equals the sum over `D` of the integrals of `k y` against the measure of `Γ \ G`.
-/
lemma New.integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : D, ‖k y x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨
      ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    Integrable (fun x : G ↦ ∑' y : C, k y x) (S.quotMeasure μ) ∧
    ∫ x : G, ∑' y : D, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ ∧
    ∑' y : D, ∫ x : G, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  -- The two finiteness hypotheses are equivalent.
  rw [lintegral_tsum_enorm_block hi hΓ hS hC hD hk_meas hk, or_self] at h_fin
  exact ⟨integrable_tsum_of_lintegral_lt_top (fun y : C ↦ hk_meas y) h_fin,
    integral_tsum_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin,
    tsum_integral_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [Countable Y] in
/-- If `k (γ • y) (i γ * x) = k y x`, then the term `k y` is invariant on the left under the image
`S` of the stabiliser of `y`. -/
lemma New.fixesLeft_map_stabilizer {S : Subgroup G} {k : Y → G → ℂ}
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) : S.FixesLeft (k y) := by
  subst h_stab
  rintro _ ⟨γ, hγ, rfl⟩ x
  rw [← hk γ y x, mem_stabilizer_iff.1 hγ]

/-- Unfolding of a sum over an orbit. Let `i` be injective with discrete range `Γ`, let the terms
`k z` be measurable and equivariant, and let `S` be the image under `i` of the stabiliser of `y`.
Suppose that the sum of the `‖k z‖` over the orbit of `y` has finite integral over `Γ \ G`, or that
`k y` is integrable over `S \ G`. Then `k y` is integrable over `S \ G`, and its integral equals the
integral over `Γ \ G` of the sum of the `k z` over the orbit, and also the sum of their
integrals. -/
lemma New.integral_tsum_orbit_eq_integral_stabilizer (hi : Function.Injective i)
    [DiscreteTopology i.range] {μ : Measure G} [IsHaarMeasure μ]
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x) {y : Y}
    (h_fin : ∫⁻ x : G, ∑' z : orbit Λ y, ‖k z x‖ₑ ∂i.range.quotMeasure μ < ∞ ∨
      Integrable (k y) (((stabilizer Λ y).map i).quotMeasure μ)) :
    Integrable (k y) (((stabilizer Λ y).map i).quotMeasure μ) ∧
    ∫ x : G, ∑' z : orbit Λ y, k z x ∂i.range.quotMeasure μ =
      ∫ x : G, k y x ∂((stabilizer Λ y).map i).quotMeasure μ ∧
    ∑' z : orbit Λ y, ∫ x : G, k z x ∂i.range.quotMeasure μ =
      ∫ x : G, k y x ∂((stabilizer Λ y).map i).quotMeasure μ := by
  -- The case `C = {y}` of `integral_tsum_block`: the orbit is the union of the translates of `{y}`.
  have hC : ∀ γ : Λ, ∀ z ∈ ({y} : Set Y),
      γ • z ∈ ({y} : Set Y) ↔ i γ ∈ (stabilizer Λ y).map i := by
    simp [Subgroup.mem_map_iff_mem hi]
  have hD (z : Y) : z ∈ orbit Λ y ↔ ∃ γ : Λ, γ • z ∈ ({y} : Set Y) := by
    simp [mem_orbit_symm (a₁ := z), mem_orbit_iff]
  have h_block : ∫⁻ x, ∑' z : orbit Λ y, ‖k z x‖ₑ ∂i.range.quotMeasure μ < ∞ ∨
      ∫⁻ x, ∑' z : ({y} : Set Y), ‖k z x‖ₑ ∂((stabilizer Λ y).map i).quotMeasure μ < ∞ :=
    h_fin.imp_right fun h_int ↦ by simpa [HasFiniteIntegral] using h_int.hasFiniteIntegral
  simpa using
    integral_tsum_block hi rfl ((stabilizer Λ y).map_le_range i) hC hD hk_meas hk h_block

/-- Unfolding of a sum over an orbit, with the subgroups and the orbit given by equations: `Γ` is
the discrete range of the injective map `i`, `S` the image of the stabiliser of `y`, and `D` the
orbit of `y`. Here `Γ.quotMeasure μ` is the measure on `G` that computes integrals over `Γ \ G`: the
Haar measure `μ` weighted by a cutoff for `Γ`, and likewise for `S`. The terms `k z` are measurable
and equivariant. Suppose that `∑ ‖k z‖`, over all `z : Y`, has finite integral over `Γ \ G` or that
`k y` is integrable over `S \ G`. Then `k y` is integrable over `S \ G`, and its integral equals the
integral of `∑_D k z` over `Γ \ G` and also the sum over `D` of the integrals of `k z` against
`Γ.quotMeasure μ`. -/
lemma New.integral_tsum_orbit_of_lt_top_or_integrable (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {D : Set Y}
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) (h_orbit : ∀ z : Y, z ∈ D ↔ y ∈ orbit Λ z)
    (h_fin : ∫⁻ x : G, ∑' z : Y, ‖k z x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨
      Integrable (k y) (S.quotMeasure μ)) :
    Integrable (k y) (S.quotMeasure μ) ∧
    ∫ x : G, ∑' z : D, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ ∧
    ∑' z : D, ∫ x : G, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ := by
  obtain rfl : D = orbit Λ y := Set.ext fun z ↦ (h_orbit z).trans mem_orbit_symm
  subst hΓ h_stab
  -- The sum over the orbit is at most the sum over all of `Y`.
  exact integral_tsum_orbit_eq_integral_stabilizer hi hk_meas hk <| h_fin.imp_left <|
    (lintegral_mono fun x ↦ tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans_lt

/-- Left invariance of `k y` and unfolding over the orbit `D` of `y`, as one statement. Here `i`
maps `Λ` isomorphically onto the discrete subgroup `Γ`, `S` is the image under `i` of the stabiliser
of `y`, and the `k z` are measurable and equivariant. The conclusion has two parts. The first says
that `k y` is left `S`-invariant (`S.FixesLeft (k y)`). The second is the implication proved in
`integral_tsum_orbit_of_lt_top_or_integrable`: if `∑ ‖k z‖` has finite integral over `Γ \ G` or
`k y` is integrable over `S \ G`, then `k y` is integrable over `S \ G`, and its integral equals
both the integral of `∑_D k z` over `Γ \ G` and the sum over `D` of the integrals of the `k z`. -/
lemma New.integral_tsum_orbit (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {D : Set Y}
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) (h_orbit : ∀ z : Y, z ∈ D ↔ y ∈ orbit Λ z) :
    S.FixesLeft (k y) ∧
    ((∫⁻ x : G, ∑' z : Y, ‖k z x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨ Integrable (k y) (S.quotMeasure μ)) →
      Integrable (k y) (S.quotMeasure μ) ∧
      ∫ x : G, ∑' z : D, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ ∧
      ∑' z : D, ∫ x : G, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ) :=
  ⟨fixesLeft_map_stabilizer hk h_stab,
    integral_tsum_orbit_of_lt_top_or_integrable hi hΓ hk_meas hk h_stab h_orbit⟩

end OrbitUnfolding

/-!
## Iwasawa integration formula

Integration in Iwasawa coordinates on a unimodular group `G = N · i(M) · K`, with `N` closed, `K`
compact and `i : M →* G` continuous. It is used for constant terms along a unipotent radical `N`.
-/

section IwasawaIntegration

open MeasureTheory Measure ENNReal NeZero ProbabilityTheory Function

/-- Let `J f x` be measurable in `x`, and let `J f x₀` be obtained from `J f y` by a finite nonzero
factor that depends on `y` only. Then this factor can be absorbed into a measurable weight: for
measurable `β` there is a measurable `g` with `g y * J f y = β y * J f x₀`. -/
lemma New.exists_measurable_mul_eq_of_scale {X : Type*} [MeasurableSpace X]
    {J : (X → ℝ≥0∞) → X → ℝ≥0∞} {x₀ : X} (hJ : ∀ f : X → ℝ≥0∞, Measurable f → Measurable (J f))
    (h_scale : ∀ y : X, ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧
      ∀ f : X → ℝ≥0∞, Measurable f → r * J f y = J f x₀)
    {β : X → ℝ≥0∞} (hβ : Measurable β) :
    ∃ g : X → ℝ≥0∞, Measurable g ∧
      ∀ (y : X) (f : X → ℝ≥0∞), Measurable f → g y * J f y = β y * J f x₀ := by
  by_cases! h_const : ∀ (y : X) (f : X → ℝ≥0∞), Measurable f → J f y = J f x₀
  · exact ⟨β, hβ, fun y f hf ↦ by rw [h_const y f hf]⟩
  -- Otherwise some `J f` is everywhere finite and nonzero; the factor at `x` is `J f x₀ / J f x`.
  obtain ⟨y₀, f, hf, h_ne⟩ := h_const
  obtain ⟨r, hr_zero, hr_top, hr⟩ := h_scale y₀
  have h_zero : J f x₀ ≠ 0 := fun h ↦ h_ne (by simpa [h, hr_zero] using hr f hf)
  have h_top : J f x₀ ≠ ∞ := fun h ↦
    h_ne (by simpa [h, hr_zero, hr_top, mul_eq_top] using hr f hf)
  refine ⟨fun x ↦ β x * (J f x₀ / J f x), hβ.mul (measurable_const.div (hJ f hf)),
    fun x φ hφ ↦ ?_⟩
  obtain ⟨s, hs_zero, -, hs⟩ := h_scale x
  have hx_zero : J f x ≠ 0 := fun h ↦ h_zero (by rw [← hs f hf, h, mul_zero])
  have hx_top : J f x ≠ ∞ := fun h ↦ h_top (by rw [← hs f hf, h, mul_top hs_zero])
  have h_div : J f x₀ / J f x = s := by
    rw [← hs f hf, ENNReal.mul_div_cancel_right hx_zero hx_top]
  simp only [h_div, mul_assoc, hs φ hφ]

/-- A function that is integrable for `∞ • q` vanishes `q`-almost everywhere. -/
lemma New.ae_eq_zero_of_integrable_top_smul {X : Type*} [MeasurableSpace X] {q : Measure X}
    {F : X → ℂ} (h_int : Integrable F (∞ • q)) : F =ᵐ[q] 0 := by
  have hF : AEStronglyMeasurable F q :=
    h_int.aestronglyMeasurable.mono_ac (absolutelyContinuous_smul top_ne_zero)
  have h_lt : ∞ * ∫⁻ x, ‖F x‖ₑ ∂q < ∞ := by
    simpa [HasFiniteIntegral] using h_int.hasFiniteIntegral
  have h_norm : ∫⁻ x, ‖F x‖ₑ ∂q = 0 := by simpa [mul_lt_top_iff] using h_lt
  filter_upwards [(lintegral_eq_zero_iff' hF.eNorm).1 h_norm] with x hx using by simpa using hx

/-- Division of an integral formula by a factor `c ∈ (0, ∞]` of the measure. For finite nonzero `V`
there is `a ≠ 0` such that, if `F` is measurable and integrable for `c • q` with integral `V * I`,
then `F` is integrable for `q` with integral `a * I`. -/
lemma New.exists_integral_eq_mul_of_smul_measure {X : Type*} [MeasurableSpace X] (q : Measure X)
    {c V : ℝ≥0∞} (hc : c ≠ 0) (hV_zero : V ≠ 0) (hV_top : V ≠ ∞) :
    ∃ a ≠ (0 : ℝ), ∀ (F : X → ℂ) (I : ℂ), Measurable F → Integrable F (c • q) →
      ∫ x : X, F x ∂(c • q) = V.toReal * I → Integrable F q ∧ ∫ x : X, F x ∂q = a * I := by
  have hV : V.toReal ≠ 0 := toReal_ne_zero.2 ⟨hV_zero, hV_top⟩
  rcases eq_or_ne c ∞ with rfl | hc_top
  · -- For `c = ∞`, integrability forces `F = 0` almost everywhere, and both sides vanish.
    refine ⟨1, one_ne_zero, fun F I _ h_int h_eq ↦ ?_⟩
    have hF_zero : F =ᵐ[q] 0 := ae_eq_zero_of_integrable_top_smul h_int
    obtain rfl : I = 0 := by simpa [hV] using h_eq
    exact ⟨(integrable_zero X ℂ q).congr hF_zero.symm, by simp [integral_eq_zero_of_ae hF_zero]⟩
  · have hc_real : c.toReal ≠ 0 := toReal_ne_zero.2 ⟨hc, hc_top⟩
    refine ⟨V.toReal / c.toReal, div_ne_zero hV hc_real,
      fun F I _ h_int h_eq ↦ ⟨(integrable_smul_measure hc hc_top).1 h_int, ?_⟩⟩
    rw [integral_smul_measure, Complex.real_smul] at h_eq
    simp [div_mul_eq_mul_div, ← h_eq, hc_real]

/-- Let `i a` lie in `N` only for `a = 1`, let `δ` be injective, and let `Γ` contain every `i (δ d)`
and lie in the union of the `N · i (δ d)⁻¹`. Then every element of `Γ` is uniquely `i (δ d) * γ`
with `γ ∈ Γ ∩ N`. -/
lemma New.exists_equiv_prod_subgroupOf {G M D : Type*} [Group G] [Group M] {N Γ : Subgroup G}
    {i : M →* G} (h_triv : ∀ a : M, i a ∈ N → a = 1) {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) :
    ∃ e : D × Γ.subgroupOf N ≃ Γ,
      ∀ (d : D) (γ : Γ.subgroupOf N), (e (d, γ) : G) = i (δ d) * (γ : N) := by
  let φ (p : D × Γ.subgroupOf N) : Γ :=
    ⟨i (δ p.1) * (p.2 : N), mul_mem (hδ_mem p.1) (Subgroup.mem_subgroupOf.1 p.2.property)⟩
  refine ⟨.ofBijective φ ⟨?_, fun g ↦ ?_⟩, fun d γ ↦ rfl⟩
  · rintro ⟨d, γ⟩ ⟨d', γ'⟩ h
    have h_eq : i (δ d) * (γ : N) = i (δ d') * (γ' : N) := congrArg Subtype.val h
    have h_mem : i ((δ d)⁻¹ * δ d') ∈ N := by
      simpa [QuotientGroup.eq] using congrArg (QuotientGroup.mk : G → G ⧸ N) h_eq
    obtain rfl : d = d' := hδ (inv_mul_eq_one.1 (h_triv _ h_mem))
    simpa using h_eq
  · obtain ⟨d, h_mem⟩ : ∃ d : D, (g : G)⁻¹ * i (δ d) ∈ N := hΓ _ (inv_mem g.property)
    let γ : Γ.subgroupOf N :=
      ⟨⟨(g : G)⁻¹ * i (δ d), h_mem⟩, mul_mem (inv_mem g.property) (hδ_mem d)⟩
    exact ⟨(d, γ⁻¹), by simp [φ, γ]⟩

variable {G M : Type*} [Group G] [Group M] [TopologicalSpace G] [IsTopologicalGroup G]
  [PolishSpace G] (w : M → ℝ) [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M]
  [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
  (ν : Measure M) [IsHaarMeasure ν]
  {N K Γ : Subgroup G} [IsMulRightInvariant ν] [CompactSpace K]
  (κ : Measure K) [IsHaarMeasure κ]
  {lam : Measure N} [IsHaarMeasure lam] (i : M →* G)

omit [IsHaarMeasure ν] [IsHaarMeasure lam] in
/-- Let `N` be unimodular, and let conjugation by `i m` multiply integrals over `N` by `w m`. The
integral of `f (i a * u * (n * i m * k) * l⁻¹)` over `K × M × N`, times `w m`, is the integral of
`f (i a * u * l⁻¹)`. -/
lemma New.ofReal_mul_lintegral_iwasawa_translate [IsMulRightInvariant lam]
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {f : G → ℝ≥0∞} (hf : Measurable f) (n : N) (m : M) (k : K) :
    ENNReal.ofReal (w m) *
        ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (n * i m * k) * l⁻¹) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
  -- Absorb `n` into `u`, move `i m` past `u`, then absorb `m` into `a` and `k` into `l`.
  have h_move (x z : G) : ENNReal.ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam =
      ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam :=
    calc ENNReal.ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam
      _ = ENNReal.ofReal (w m) * ∫⁻ u : N, f (x * u * i m * (k * z)) ∂lam := by
        rw [← lintegral_mul_right_eq_self (fun u : N ↦ f (x * u * i m * (k * z))) n]
        simp [mul_assoc]
      _ = ∫⁻ u : N, f (x * (i m * u * (i m)⁻¹) * i m * (k * z)) ∂lam :=
        (h_conj m (fun y ↦ f (x * y * i m * (k * z))) (by fun_prop)).symm
      _ = ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam := by simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i (a * m) * u * (k * l⁻¹)) ∂lam ∂ν ∂κ := by
      simp only [← lintegral_const_mul' _ _ ofReal_ne_top, map_mul, ← h_move]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam ∂ν ∂κ :=
      lintegral_congr fun l ↦
        lintegral_mul_right_eq_self (fun a : M ↦ ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam) m
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
      rw [← lintegral_mul_right_eq_self _ k]
      simp

omit [PolishSpace G] [IsMulRightInvariant ν] [CompactSpace K] in
/-- Suppose that conjugation by `i m` multiplies integrals over `N` by `w m`. The integral of
`g ((i a * u)⁻¹ * (x * l))` over `K × M × N` is the same for `x = n * i m * k` as for `x = 1`. -/
lemma New.lintegral_iwasawa_inv_mul_translate
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {g : G → ℝ≥0∞} (hg : Measurable g) (n : N) (m : M) (k : K) :
    ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (n * i m * k * l)) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ := by
  -- Move `(i a)⁻¹` past `u⁻¹` to absorb `n` into `u`; then absorb `m` into `a` and `k` into `l`.
  have h_absorb (a : M) (z : G) :
      ∫⁻ u : N, g ((i a * u)⁻¹ * (n * z)) ∂lam = ∫⁻ u : N, g ((i a * u)⁻¹ * z) ∂lam := by
    have h_move (y : G) : ∫⁻ u : N, g ((i a * u)⁻¹ * y) ∂lam =
        ENNReal.ofReal (w a) * ∫⁻ u : N, g ((i a)⁻¹ * ((u : G)⁻¹ * y)) ∂lam := by
      simpa [mul_assoc] using h_conj a (fun x ↦ g ((i a)⁻¹ * (x⁻¹ * y))) (by fun_prop)
    rw [h_move, h_move, ← lintegral_mul_left_eq_self _ n]
    simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (i m * (k * l))) ∂lam ∂ν ∂κ := by
      simp only [mul_assoc, h_absorb]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (k * l)) ∂lam ∂ν ∂κ := by
      refine lintegral_congr fun l ↦ ?_
      rw [← lintegral_mul_left_eq_self _ m]
      simp [mul_assoc]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ :=
      lintegral_mul_left_eq_self (fun l : K ↦ ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν) k

variable [LocallyCompactSpace G]

/-- Iwasawa integration formula. Let `G`, `M` and the closed subgroup `N` be unimodular, `K`
compact, `i : M →* G` continuous, and `w : M → ℝ`. Suppose that `G = N · i(M) · K` and that
conjugation by `i m` multiplies integrals over `N` by `w m > 0`. Then the measure `dn dm dk` in the
coordinates `i m * n * k` is `d` times the Haar measure `μ` on `G`, for some `d ∈ [0, ∞]` (`d` may
be infinite, for instance if `i` has noncompact kernel). Here `lam`, `ν`, `κ` are Haar measures on
`N`, `M`, `K`. -/
lemma New.lintegral_iwasawa [PolishSpace M] [LocallyCompactSpace M]
    (hN : IsClosed (N : Set G)) (hw_pos : ∀ m : M, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ n : N, ∃ m : M, ∃ k : K, g = n * i m * k)
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    [IsMulRightInvariant lam] :
    ∃ d : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ = d * ∫⁻ g : G, f g ∂μ := by
  -- Let `J f y` be the integral of `f (i m * n * y * k⁻¹)`; the left side is `J f 1`. Moving `y`
  -- only divides `J f y` by `w`, so `J f 1 = ∫ g y * J f y` for a suitable weight `g`. After Fubini
  -- and a translation of `y`, this is `∫ d x * f x`, where `d x`, an integral of `g`, is constant.
  obtain ⟨β, hβ, hβ_int⟩ := (inferInstance : HasCutoff μ G).out
  have hβ_one : ∫⁻ x, β x ∂μ = 1 := by simpa using hβ_int 1
  let π : Measure ((M × N) × K) := (ν.prod lam).prod κ
  let b (p : M × N) : G := i p.1 * p.2
  have hπ (φ : G → K → ℝ≥0∞) (hφ : Measurable (uncurry φ)) :
      ∫⁻ h, φ (b h.1) h.2 ∂π = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, φ (i m * n) k ∂lam ∂ν ∂κ := by
    rw [lintegral_prod_symm _ (by fun_prop)]
    exact lintegral_congr fun k ↦ lintegral_prod _ (by fun_prop)
  let J (f : G → ℝ≥0∞) (y : G) : ℝ≥0∞ := ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π
  have hJ (f : G → ℝ≥0∞) (hf : Measurable f) (y : G) :
      J f y = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * y * k⁻¹) ∂lam ∂ν ∂κ :=
    hπ (fun x k ↦ f (x * y * k⁻¹)) (by fun_prop)
  have h_scale (y : G) : ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧
      ∀ f : G → ℝ≥0∞, Measurable f → r * J f y = J f 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec y
    refine ⟨.ofReal (w m), (ofReal_pos.2 (hw_pos m)).ne', ofReal_ne_top, fun f hf ↦ ?_⟩
    simpa only [hJ f hf, mul_one] using
      ofReal_mul_lintegral_iwasawa_translate w ν κ i h_conj hf n m k
  -- The weight `g` satisfies `g y * J f y = β y * J f 1`.
  obtain ⟨g, hg, hgJ⟩ := exists_measurable_mul_eq_of_scale (fun f hf ↦ by fun_prop) h_scale hβ
  let d (x : G) : ℝ≥0∞ := ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π
  have hd (x : G) : d x = d 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec x
    have hd_eq (z : G) := hπ (fun y l ↦ g (y⁻¹ * (z * l))) (by fun_prop)
    simpa only [d, hd_eq, one_mul] using lintegral_iwasawa_inv_mul_translate w ν κ i h_conj hg n m k
  refine ⟨d 1, fun f hf ↦ ?_⟩
  calc ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ
    _ = J f 1 := by
      rw [hJ f hf, ← lintegral_inv_eq_self]
      simp
    _ = ∫⁻ y, g y * J f y ∂μ := by simp [hgJ _ f hf, lintegral_mul_const _ hβ, hβ_one]
    _ = ∫⁻ h, ∫⁻ y, g y * f (b h.1 * y * h.2⁻¹) ∂μ ∂π := by
      simp (disch := fun_prop) only [J, ← lintegral_const_mul]
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ h, ∫⁻ x, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂μ ∂π := by
      congr with ⟨p, k⟩
      rw [← lintegral_mul_left_eq_self _ (b p)⁻¹, ← lintegral_mul_right_eq_self _ (k : G)]
      simp [mul_assoc]
    _ = ∫⁻ x, ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂π ∂μ := lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x, d x * f x ∂μ := lintegral_congr fun x ↦ lintegral_mul_const _ (by fun_prop)
    _ = d 1 * ∫⁻ x, f x ∂μ := by simp_rw [hd, lintegral_const_mul _ hf]

omit [TopologicalSpace M] [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M] in
/-- Let `i a` lie in the closed unimodular subgroup `N` only for `a = 1`, let `δ` be injective, and
let the discrete group `Γ` contain every `i (δ d)` and lie in the union of the `N · i (δ d)⁻¹`.
Suppose that conjugation by `i m` multiplies integrals over `N` by `w m`. Then `w m` times the
integral over `(Γ ∩ N) \ N` (that is, against `quotMeasure lam`) of a sum over `Γ` unfolds to a sum
over `d` of integrals over `N` against the Haar measure `lam`. -/
lemma New.ofReal_mul_lintegral_quotMeasure_tsum
    (hN : IsClosed (N : Set G))
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*} [Countable D] {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) [DiscreteTopology Γ]
    {f : G → ℝ≥0∞} (hf : Measurable f) (m : M) (k : G) :
    ENNReal.ofReal (w m) *
        ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i m * k))) ∂(Γ.subgroupOf N).quotMeasure lam =
      ∑' d : D, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by
  -- Write the elements of `Γ` as `i (δ d) * γ` with `γ ∈ Γ ∩ N`, unfold the quotient measure to
  -- `lam`, and move `i m` past `n`.
  obtain ⟨e, he⟩ := exists_equiv_prod_subgroupOf h_triv hδ hδ_mem hΓ
  simp only [← e.tsum_eq, tsum_prod', he]
  rw [lintegral_tsum (by fun_prop), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun d ↦ ?_
  calc ENNReal.ofReal (w m) * ∫⁻ n : N, ∑' γ : Γ.subgroupOf N,
        f (i (δ d) * (γ : N) * (n * (i m * k))) ∂(Γ.subgroupOf N).quotMeasure lam
    _ = ENNReal.ofReal (w m) * ∫⁻ n : N, f (i (δ d) * n * i m * k) ∂lam := by
      rw [← lintegral_orbitMeasure_lintegral (ν := (count : Measure (Γ.subgroupOf N)))
        (f := fun n : N ↦ f (i (δ d) * n * i m * k)) (by fun_prop)]
      simp [lintegral_count, Subgroup.smul_def, mul_assoc]
    _ = ∫⁻ n : N, f (i (δ d) * (i m * n * (i m)⁻¹) * i m * k) ∂lam :=
      (h_conj m (fun y ↦ f (i (δ d) * y * i m * k)) (by fun_prop)).symm
    _ = ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by simp [mul_assoc]

/-- Unfolding in Iwasawa coordinates. Let `μ`, `ν`, `κ`, `lam` be Haar measures on the unimodular
group `G`, the unimodular group `M`, the compact subgroup `K` and the closed subgroup `N`, and let
`i` and `w` be continuous. Suppose that `G = N · i(M) · K`, that conjugation by `i m` multiplies
integrals over `N` by `w m > 0`, and that `i a` lies in `N` only for `a = 1`. Let `δ` be injective,
and let `Γ` be discrete, contain every `i (δ d)` and lie in the union of the `N · i (δ d)⁻¹`, with
`Γ ∩ N` cocompact in `N` (`IsCocompact`: every element of `N` has a left translate by `Γ ∩ N` in a
fixed compact set). Let `α` be a measure on `M` that unfolds to `ν` along `δ`. There is `c ≠ 0` such
that for measurable `F`, left invariant under `N` and `Γ` (`FixesLeft`): if
`(m, k) ↦ w m * F (i m * k)` is integrable for `α × κ`, then `F` is integrable over `Γ \ G` (against
`Γ.quotMeasure μ`), and its integral is `c` times the integral of `w m * F (i m * k)`. -/
lemma New.integral_quotMeasure_iwasawa [PolishSpace M] [LocallyCompactSpace M]
    (hN : IsClosed (N : Set G)) (hw : Continuous w) (hw_pos : ∀ m : M, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ n : N, ∃ m : M, ∃ k : K, g = n * i m * k)
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*}
    [Countable D] {δ : D → M} (hδ : δ.Injective) (α : Measure M) [SFinite α]
    (hα : ∀ f : M → ℝ≥0∞, Measurable f → ∫⁻ m : M, f m ∂ν = ∫⁻ m : M, ∑' d : D, f (δ d * m) ∂α)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) [DiscreteTopology Γ]
    (h_cocpt : (Γ.subgroupOf N).IsCocompact) :
    ∃ c ≠ (0 : ℝ), ∀ F : G → ℂ, Measurable F → N.FixesLeft F → Γ.FixesLeft F →
      Integrable (fun p : M × K ↦ (w p.1 : ℂ) * F (i p.1 * p.2)) (α.prod κ) →
      Integrable F (Γ.quotMeasure μ) ∧
      ∫ g : G, F g ∂Γ.quotMeasure μ =
        c * ∫ p : M × K, (w p.1 : ℂ) * F (i p.1 * p.2) ∂α.prod κ := by
  -- The Iwasawa formula with factor `r`, unfolded along `Γ = {i (δ d) * γ}`, says that the measure
  -- `w · (α × κ) × (Γ ∩ N)\N` in the coordinates `n * i m * k` is the quotient of `r • μ` by `Γ`.
  -- The cocompact subgroup `Γ ∩ N` is a lattice in `N`, so `N` is unimodular.
  let lam' : Measure N := (Γ.subgroupOf N).quotMeasure lam
  have h_finite : IsFiniteMeasure lam' := isFiniteMeasure_quotMeasure_of_cocompact lam h_cocpt
  have : lam.IsMulRightInvariant := isMulRightInvariant_of_finite_covolume h_finite
  obtain ⟨r, h_iwa⟩ := lintegral_iwasawa (lam := lam) w μ ν κ i hN hw_pos hi h_dec h_conj
  -- For `f = 1` the left side of `h_iwa` is a product of nonzero total masses.
  have hr : r ≠ 0 := fun h ↦ by simpa [h, NeZero.ne] using h_iwa 1 measurable_one
  have hw_meas : Measurable fun p : M × K ↦ ENNReal.ofReal (w p.1) := by fun_prop
  let ρ : Measure (M × K) := (α.prod κ).withDensity fun p ↦ .ofReal (w p.1)
  let σ (p : M × K) : G := i p.1 * p.2
  let τ (p : (M × K) × N) : G := p.2 * σ p.1
  have h_unfold : MeasurePreserving (fun p : ((M × K) × N) × Γ ↦ p.2 • τ p.1)
      ((ρ.prod lam').prod count) (r • μ) := by
    refine ⟨by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    calc
      _ = ∫⁻ p : M × K, ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i p.1 * p.2))) ∂lam' ∂ρ := by
        simp (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count,
          Subgroup.smul_def, smul_eq_mul, τ, σ]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∑' d : D, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam ∂α ∂κ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hw_meas (by fun_prop),
          lintegral_prod_symm _ (by fun_prop)]
        simp only [Pi.mul_apply, lam',
          ofReal_mul_lintegral_quotMeasure_tsum w i hN h_conj h_triv hδ hδ_mem hΓ hf]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ :=
        lintegral_congr fun k ↦ (hα (fun m ↦ ∫⁻ n : N, f (i m * n * k) ∂lam) (by fun_prop)).symm
      _ = ∫⁻ g, f g ∂(r • μ) := by rw [h_iwa f hf, lintegral_smul_measure, smul_eq_mul]
  obtain ⟨c, hc, h_div⟩ := exists_integral_eq_mul_of_smul_measure (Γ.quotMeasure μ) hr
    (NeZero.ne (lam' .univ)) (measure_ne_top lam' .univ)
  refine ⟨c, hc, fun F hF hFN hFΓ h_weighted ↦ ?_⟩
  -- By `h_unfold`, `F` on `Γ \ G` has the law of `F ∘ τ`, and `F ∘ τ` does not depend on `n`.
  have hFτ (p : (M × K) × N) : F (τ p) = F (σ p.1) := hFN p.2 p.2.property (σ p.1)
  have h_law : IdentDistrib F (fun p : M × K ↦ F (σ p)) (r • Γ.quotMeasure μ)
      (lam' .univ • ρ) := by
    rw [← show Γ.quotMeasure (r • μ) = r • Γ.quotMeasure μ from withDensity_smul_measure r _]
    refine (identDistrib_orbitMeasure_of_unfold (T := τ) (.id (count : Measure Γ)) h_unfold hF
      (by fun_prop) fun γ x ↦ hFΓ γ γ.property x).trans ⟨by fun_prop, by fun_prop, ?_⟩
    simp (disch := fun_prop) only [hFτ, ← map_fst_prod, map_map, comp_def]
  have h_int : Integrable (fun p : M × K ↦ F (σ p)) ρ := by
    simpa [ρ, integrable_withDensity_iff_integrable_smul' hw_meas, hw_pos, le_of_lt]
      using h_weighted
  refine h_div F _ hF (h_law.integrable_iff.2 (h_int.smul_measure (measure_ne_top lam' .univ))) ?_
  rw [h_law.integral_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hw_meas (by simp)]
  simp [σ, hw_pos, le_of_lt]
end IwasawaIntegration
end
end

/-!
# Convolution over real points, cusp kernels, the Petersson product and Poincaré series

Let G = G_∞ × G_f be the adelic unitary group, and let R(α)F(g) = ∫ α(x) F(gx) dx over G_∞ be right
convolution over the real points (`New.realConv`). For integrable α, R(α) preserves bounded
automorphic functions, and convolving with an idempotent kernel e produces forms of type e. The
product of discrete series kernels over the infinite places is a cusp kernel under a gap condition.
For the Petersson product, right translation is unitary, and a cusp kernel e projects every real
translate of a form of type e to a multiple of it. A bounded Poincaré series, projected term by
term, is a form.

## Main definitions and results

* `New.continuous_realConv`, `New.Space.isAutomorphic_realConv`: for integrable α, R(α)F is
  continuous when F is bounded, measurable and has an open level, and it is automorphic and bounded
  when F is also invariant under the rational points.
* `New.Space.exists_form_eq_realConv`: convolving with an idempotent kernel gives a form of type e.
* `New.IsCuspKernel`: minimal idempotents e on G_∞ with a moment of order B + 1 and decay of order
  B, and with α ∗ e = e for some continuous compactly supported α.
* `New.isCuspKernel_typeKernel`: the product kernel `New.typeKernel` over the infinite places is
  such a kernel when the parameters satisfy a gap condition.
* `New.Space.IsForm.realConv_translate`, `New.Space.IsForm.petersson_real_translate`: `e` projects
  each real translate of a form to a multiple of the form.
* `New.Space.exists_form_eq_tsum_of_fixesLeft`: if an absolutely bounded sum of measurable functions
  is left invariant under `V.Γ` and has level `K`, projecting each term by R(e) gives a form of type
  `e`; `New.Space.exists_form_eq_tsum` is the case of a sum over `V.Γ` of translates of one
  function. `New.levelSpace (V.formRep e) K` is the space of forms of type `e` fixed by the open
  subgroup `K` of the finite points.

Notions from other files:
* `New.Space.IsAutomorphic`: continuous, left invariant under the rational points `V.Γ`, and right
  invariant under some open subgroup of G_f.
* `New.HCParam.dsKernel`: for a parameter l = 2λ, the function e_λ on U(diag s), the formal degree
  times the conjugate of the discrete series coefficient c_λ (`New.HCParam.dsCoeff`).
* `New.IsIdempotentKernel` (part of `New.IsCuspKernel`): e is continuous and integrable, e(g⁻¹) is
  the conjugate of e(g), e(1) ≠ 0, and ∫ e(z)e(x⁻¹z⁻¹y) dz = e(x⁻¹)e(y)/e(1).
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.Space.quotMeasure`: the measure on `G` that computes integrals over `Γ \ G`.

## Relation to the literature

Known result: convolution over real points, cusp kernels, the Petersson product and Poincaré series
projected to forms, from the theory of cusp forms. For sources see
`Lib.Adelic.AutomorphicForms.Cuspidality`.
-/

@[expose] public section

/-! ## Convolution over the real points; cusp kernels -/

section RealConvolution

open MeasureTheory Finset Matrix.Norms.L2Operator CompactlySupported Asymptotics

namespace New

variable {E n : Type _} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {F : G E s → ℂ} {α : GInf E s → ℂ}

/-- For a bump function α_w on U(diag s) at each infinite place w, the product x ↦ ∏_w α_w(x_w⁻¹),
as a continuous compactly supported function on G_∞. -/
noncomputable def bumpProduct (α : NumberField.InfinitePlace E → DiscreteSeries.Bumps s) :
    C_c(GInf E s, ℂ) where
  toFun x := ∏ w : NumberField.InfinitePlace E, (α w).val.val (x w)⁻¹
  continuous_toFun := by fun_prop
  hasCompactSupport' := HasCompactSupport.intro (isCompact_univ_pi fun w ↦ (α w).property.inv)
    (fun x hx ↦ by
    obtain ⟨w, hw⟩ := not_forall.1 fun h ↦ hx (Set.mem_univ_pi.2 h)
    exact prod_eq_zero (mem_univ w) (image_eq_zero_of_notMem_tsupport hw))

/-- For `n` nonempty and `g` in G_∞, the product over the infinite places of the operator norms
‖g_w‖ is at least 1 and at least each of its factors. -/
theorem le_prod_opNorm [Nonempty n] (g : GInf E s) :
    1 ≤ ∏ w : NumberField.InfinitePlace E, ‖(g w).val.val‖ ∧
    ∀ w : NumberField.InfinitePlace E,
      ‖(g w).val.val‖ ≤ ∏ v : NumberField.InfinitePlace E, ‖(g v).val.val‖ := by
  have h_one (v : NumberField.InfinitePlace E) : 1 ≤ ‖(g v).val.val‖ := U.one_le_norm (g v)
  refine ⟨one_le_prod₀ fun v _ ↦ h_one v, fun w ↦ ?_⟩
  rw [← mul_prod_erase univ _ (mem_univ w)]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_prod₀ fun v _ ↦ h_one v)

/-- A cusp kernel of order B on G_∞: a minimal idempotent e (`New.IsIdempotentKernel`) such that,
with ‖x‖ = ∏_w ‖x_w‖ for the operator norms, (a) ‖x‖^(B+1) e(x) is integrable, (b) α ∗ e = e for
some continuous compactly supported α, and (c) ‖x‖^B e(x) is bounded. -/
structure IsCuspKernel (B : ℕ) (e : GInf E s → ℂ) extends IsIdempotentKernel e where
  /-- Moment: |e(x)| ‖x‖ ^ (B + 1) is integrable, where ‖x‖ is the product over the infinite places
  of the operator norms. -/
  integrable_moment :
      Integrable fun x : GInf E s ↦
        ‖e x‖ * (∏ w : NumberField.InfinitePlace E, ‖(x w).val.val‖) ^ (B + 1)
  /-- Some continuous compactly supported `α` reproduces `e` by convolution: α ∗ e = e. -/
  exists_bump : ∃ α : GInf E s →C_c ℂ, ∀ y : GInf E s, ∫ x : GInf E s, α x * e (x⁻¹ * y) = e y
  /-- Decay of order `B`: |e(x)| ‖x‖ ^ B is bounded. -/
  decay : ∃ C : ℝ, ∀ x : GInf E s,
    ‖e x‖ * (∏ w : NumberField.InfinitePlace E, ‖(x w).val.val‖) ^ B ≤ C

/-- The complex conjugate of a cusp kernel of order `B` is a cusp kernel of order `B`. -/
theorem IsCuspKernel.star {B : ℕ} {e : GInf E s → ℂ} (he : IsCuspKernel B e) :
    IsCuspKernel B (star e) where
  continuous := he.continuous.star
  integrable := (starL' ℝ).integrable_comp_iff.2 he.integrable
  apply_inv g := by simp [he.apply_inv]
  apply_one_ne_zero := by simpa using he.apply_one_ne_zero
  convolution_eq x y := by
    simpa [← integral_conj] using congrArg (starRingEnd ℂ) (he.convolution_eq x y)
  integrable_moment := by simpa using he.integrable_moment
  exists_bump := he.exists_bump.elim fun α hα ↦
    -- Conjugate the equation `α ∗ e = e`.
    ⟨Star.star α, fun y ↦ by simpa [← integral_conj] using congrArg (starRingEnd ℂ) (hα y)⟩
  decay := by simpa using he.decay

/-- For n nonempty, suppose that at every infinite place w the integer vector l_w = 2λ_w, read by
`toHCParam` as a doubled parameter for the signs s, is a parameter with gap 500|n|³ + B
(`HasLargeGap B`). Then `New.typeKernel` l s, the product over the infinite places of the discrete
series kernels e_(l_w), is an idempotent kernel on G_∞. That is, it is continuous and integrable,
e(g⁻¹) = conj(e(g)), e(1) ≠ 0, and ∫ e(z) e(x⁻¹z⁻¹y) dz = e(x⁻¹) e(y) / e(1). -/
theorem isIdempotentKernel_typeKernel [Nonempty n] {l : NumberField.InfinitePlace E → n → ℤ}
    {B : ℕ} (h : ∀ w : NumberField.InfinitePlace E, (toHCParam s (l w)).HasLargeGap B) :
    IsIdempotentKernel (typeKernel (E := E) l s) := by
  -- Every property is the product over the infinite places of the property of `HCParam.dsKernel`.
  have h_loc (w : NumberField.InfinitePlace E) :
      IsIdempotentKernel (toHCParam s (l w)).dsKernel := (h w).isIdempotentKernel_dsKernel
  exact
    { continuous := by fun_prop
      integrable := .fintype_prod fun w ↦ (h_loc w).integrable
      apply_inv := by simp [typeKernel, ← (h_loc _).apply_inv]
      apply_one_ne_zero := by simp [typeKernel, (h_loc _).apply_one_ne_zero, prod_eq_zero_iff]
      convolution_eq := by simp [typeKernel, mul_assoc, ← prod_mul_distrib, ← prod_div_distrib,
        ← integral_fintype_prod_volume_eq_prod, ← (h_loc _).convolution_eq] }

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let E be a CM field, n nonempty and s a family of signs. Suppose every l_w = 2λ_w is a
Harish-Chandra parameter whose entries λ_i, λ_j of different signs s are at least 500|n|³ + B apart.
Then `New.typeKernel` l s, the product over the infinite places of the discrete series kernels
e_(l_w), is a cusp kernel of order B: a minimal idempotent e on G_∞ such that, with ‖x‖ = ∏_w ‖x_w‖
the product of operator norms, ‖x‖^(B+1) e(x) is integrable, α ∗ e = e for some continuous compactly
supported α, and ‖x‖^B e(x) is bounded. -/
theorem isCuspKernel_typeKernel [Nonempty n] {l : NumberField.InfinitePlace E → n → ℤ} {B : ℕ}
    (h : ∀ w : NumberField.InfinitePlace E, (toHCParam s (l w)).HasLargeGap B) :
    IsCuspKernel B (typeKernel (E := E) l s) := by
  -- The moment, the bump function and the decay bound are products of the local ones.
  let e (w : NumberField.InfinitePlace E) : USign s → ℂ := (toHCParam s (l w)).dsKernel
  have h_prod (x : GInf E s) : typeKernel l s x = ∏ w, e w (x w) := rfl
  have h_moment : Integrable fun x : GInf E s ↦
      ‖typeKernel l s x‖ * (∏ w, ‖(x w).val.val‖) ^ (B + 1) := by
    have h_loc : Integrable fun x : GInf E s ↦
        ∏ w, e w (x w) * (‖(x w).val.val‖ : ℂ) ^ (B + 1) :=
      .fintype_prod fun w ↦ (h w).integrable_dsKernel_mul_norm_pow (B + 1) le_rfl
    simpa [h_prod, prod_mul_distrib, prod_pow] using h_loc.norm
  have h_bump (w : NumberField.InfinitePlace E) : ∃ α : DiscreteSeries.Bumps s,
      ∀ g : USign s, ∫ x : USign s, α.val.val x⁻¹ * e w (x⁻¹ * g) = e w g :=
    (h w).exists_bump_conv_dsKernel
  choose α hα using h_bump
  have h_fix (y : GInf E s) :
      ∫ x : GInf E s, bumpProduct α x * typeKernel l s (x⁻¹ * y) = typeKernel l s y :=
    calc
      _ = ∫ x : GInf E s, ∏ w, (α w).val.val (x w)⁻¹ * e w ((x w)⁻¹ * y w) := by
        simp [h_prod, bumpProduct, prod_mul_distrib]
      _ = ∏ w, ∫ x : USign s, (α w).val.val x⁻¹ * e w (x⁻¹ * y w) :=
        integral_fintype_prod_volume_eq_prod fun w x ↦ (α w).val.val x⁻¹ * e w (x⁻¹ * y w)
      _ = typeKernel l s y := by simp only [hα, h_prod]
  -- `e w` is the formal degree times the conjugate of the coefficient c, and |c(g)| ≤ (2 / ‖g‖)^B.
  have h_place (w : NumberField.InfinitePlace E) (g : USign s) :
      ‖e w g‖ * ‖g.val.val‖ ^ B ≤ ‖(toHCParam s (l w)).formalDegree‖ * 2 ^ B := by
    have h_pos : 0 < ‖g.val.val‖ := one_pos.trans_le (U.one_le_norm g)
    have h_coeff : ‖(toHCParam s (l w)).dsCoeff g‖ * ‖g.val.val‖ ^ B ≤ 2 ^ B := by
      rw [← le_div_iff₀ (pow_pos h_pos B), ← div_pow]
      exact DiscreteSeries.norm_dsCoeff_le_pow (h w) (by simp) g
    simpa [e, HCParam.dsKernel, mul_assoc] using
      mul_le_mul_of_nonneg_left h_coeff (norm_nonneg (toHCParam s (l w)).formalDegree)
  refine ⟨isIdempotentKernel_typeKernel h, h_moment, ⟨bumpProduct α, h_fix⟩,
    ∏ w, ‖(toHCParam s (l w)).formalDegree‖ * 2 ^ B, fun g ↦ ?_⟩
  rw [h_prod, norm_prod, ← prod_pow, ← prod_mul_distrib]
  exact prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦ h_place w (g w)

@[simp]
theorem Space.formRep_apply (k : Gf E n) (y : V.Form α) (g : G E s) :
    V.formRep α k y g = y (g * (1, k)) :=
  rfl

/-- A form of type `α` (a bounded automorphic function fixed by `realConv α` when α is integrable)
lies in `levelSpace (V.formRep α) J`, the vectors fixed by the subgroup `J` of G_f, if and only if
it has level `J`, that is, is invariant under right translation by `J`. -/
lemma Space.mem_levelSpace_formRep_iff {J : Subgroup (Gf E n)} {y : V.Form α} :
    y ∈ levelSpace (V.formRep α) J ↔ HasLevel y J := by
  have h_fix (k : Gf E n) : V.formRep α k y = y ↔ ∀ g : G E s, y (g * (1, k)) = y g :=
    Subtype.ext_iff.trans funext_iff
  simp [h_fix]

/-- If `F` is right invariant under the open subgroup `K` of G_f, then so is its real convolution
R(α)F, since real and finite points commute. -/
lemma hasLevel_realConv (K : OpenSubgroup (Gf E n)) (h_level : HasLevel F K) :
    HasLevel (realConv α F) K := by
  intro k hk g
  have h_comm (x : GInf E s) : g * (1, k) * (x, 1) = g * (x, 1) * (1, k) := by simp [Prod.ext_iff]
  simp only [realConv, h_comm, h_level k hk]

/-- The oscillation of an average is bounded by that of the kernel in L¹. Let α be integrable on
G_∞, F bounded and measurable on G, u a real point, real points sitting in G as x ↦ (x, 1), and
R(α)F(g) = ∫_{G_∞} α(x)F(gx) dx (`realConv`). If |F(gx)| ≤ C for all real x with
α(u⁻¹x) ≠ α(x), then |R(α)F(gu) − R(α)F(g)| ≤ ‖α(u⁻¹ ·) − α‖₁ C. -/
lemma norm_realConv_mul_sub_le (hF : IsBoundedMeasurable F) (hα : Integrable α) (g : G E s)
    (u : GInf E s) {C : ℝ}
    (hC : ∀ x : GInf E s, α (u⁻¹ * x) ≠ α x → ‖F (g * (x, 1))‖ ≤ C) :
    ‖realConv α F (g * (u, 1)) - realConv α F g‖ ≤
      (∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖) * C := by
  -- The difference of the averages is ∫ (α(u⁻¹x) - α(x)) F(gx) dx.
  have h_int {β : GInf E s → ℂ} (hβ : Integrable β) :
      Integrable fun x : GInf E s ↦ β x * F (g * (x, 1)) :=
    hF.integrable_mul_comp hβ (fun x : GInf E s ↦ g * (x, 1)) (by fun_prop)
  have h_shift : realConv α F (g * (u, 1)) = ∫ x, α (u⁻¹ * x) * F (g * (x, 1)) := by
    rw [← integral_mul_left_eq_self (fun x : GInf E s ↦ α (u⁻¹ * x) * F (g * (x, 1))) u]
    simp [realConv, mul_assoc]
  have h_eq : realConv α F (g * (u, 1)) - realConv α F g =
      ∫ x, (α (u⁻¹ * x) - α x) * F (g * (x, 1)) := by
    rw [h_shift, realConv, ← integral_sub (h_int (hα.comp_mul_left u⁻¹)) (h_int hα)]
    simp only [sub_mul]
  -- Where the first factor does not vanish, the second has norm at most `C`.
  have h_le (x : GInf E s) :
      ‖(α (u⁻¹ * x) - α x) * F (g * (x, 1))‖ ≤ ‖α (u⁻¹ * x) - α x‖ * C := by
    by_cases hx : α (u⁻¹ * x) = α x
    · simp [hx]
    · exact norm_mul_le_of_le le_rfl (hC x hx)
  rw [h_eq, ← integral_mul_const]
  exact norm_integral_le_of_norm_le (((hα.comp_mul_left u⁻¹).sub hα).norm.mul_const C)
    (.of_forall h_le)

/-- Translation is continuous on L¹: for α integrable on G_∞, ‖α(u⁻¹ ·) − α‖₁ tends to 0 as the
real point u tends to 1. -/
lemma tendsto_integral_norm_translate_sub (hα : Integrable α) :
    Filter.Tendsto (fun u : GInf E s ↦ ∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖) (nhds 1) (nhds 0) := by
  have : SMulInvariantMeasure (GInf E s) (GInf E s) volume :=
    Measure.IsMulLeftInvariant.smulInvariantMeasure
  let T (u : GInf E s) : Lp ℂ 1 (volume : Measure (GInf E s)) := DomMulAct.mk u⁻¹ • hα.toL1
  have h_cont : Continuous T :=
    -- `continuous_smul` for the action on L¹, whose instance is not found by unification here
    Lp.instContinuousSMulDomMulAct.continuous_smul.comp
      (f := fun u : GInf E s ↦ (DomMulAct.mk u⁻¹, hα.toL1)) (by fun_prop)
  have h_norm (u : GInf E s) : ‖T u - T 1‖ = ∫ x : GInf E s, ‖α (u⁻¹ * x) - α (1⁻¹ * x)‖ :=
    L1.norm_of_fun_eq_integral_norm ((hα.comp_mul_left u⁻¹).sub (hα.comp_mul_left 1⁻¹))
  simpa only [h_norm, inv_one, one_mul] using tendsto_iff_norm_sub_tendsto_zero.1 (h_cont.tendsto 1)

/-- Uniform continuity of averages. Let α be integrable on G_∞, K an open subgroup of G_f and ε > 0.
Let z be close enough to 1, with real part z_∞. If (a) F is measurable, bounded and right
K-invariant and (b) |F(gx)| ≤ C for all real x with α(z_∞⁻¹x) ≠ α(x), then
|R(α)F(gz) − R(α)F(g)| ≤ ε|C|. The neighbourhood of 1 does not depend on F, C or g. -/
lemma eventually_norm_realConv_sub_le (K : OpenSubgroup (Gf E n)) (hα : Integrable α) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ z : G E s in nhds 1, ∀ {F : G E s → ℂ} (C : ℝ), IsBoundedMeasurable F → HasLevel F K →
      ∀ g : G E s,
      (∀ x : GInf E s, α (z.1⁻¹ * x) ≠ α x → ‖F (g * (x, 1))‖ ≤ C) →
      ‖realConv α F (g * z) - realConv α F g‖ ≤ ε * ‖C‖ := by
  -- Near 1 the finite part a of z lies in K and drops out, and the real part u moves α by less
  -- than ε in L¹.
  have h_L1 : ∀ᶠ u : GInf E s in nhds 1, ∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖ < ε :=
    (tendsto_integral_norm_translate_sub hα).eventually_lt_const hε
  filter_upwards [continuousAt_snd K.mem_nhds_one, continuousAt_fst h_L1]
    with ⟨u, a⟩ ha hu F C hF h_level g hC
  have h_split : g * (u, a) = g * (u, 1) * (1, a) := by simp [mul_assoc]
  calc ‖realConv α F (g * (u, a)) - realConv α F g‖
      = ‖realConv α F (g * (u, 1)) - realConv α F g‖ := by
        rw [h_split, hasLevel_realConv K h_level a ha]
    _ ≤ (∫ x : GInf E s, ‖α (u⁻¹ * x) - α x‖) * ‖C‖ :=
        norm_realConv_mul_sub_le hF hα g u fun x hx ↦
          (hC x hx).trans C.le_norm_self
    _ ≤ ε * ‖C‖ := mul_le_mul_of_nonneg_right (le_of_lt hu) (norm_nonneg C)

/-- Fubini for right convolution: for c, α integrable, j measurable and F bounded measurable on
G, ∫ c(z) R(α)F(j z) dν(z) = ∫_{G_∞} α(x) ∫ c(z) F(j(z)x) dν(z) dx, with ν s-finite. -/
lemma integral_mul_realConv (hF : IsBoundedMeasurable F) (hα : Integrable α) {Z : Type*}
    [MeasurableSpace Z] {ν : Measure Z} [SFinite ν] {c : Z → ℂ} (hc : Integrable c ν)
    (j : Z → G E s) (hj : Measurable j := by fun_prop) :
    ∫ z : Z, c z * realConv α F (j z) ∂ν =
      ∫ x : GInf E s, α x * ∫ z : Z, c z * F (j z * (x, 1)) ∂ν := by
  -- The integrand `c z * α x * F (j z * (x, 1))` is an integrable product times a bounded
  -- measurable function.
  simp_rw [realConv, ← integral_const_mul, ← mul_assoc, mul_comm (α _)]
  exact integral_integral_swap (hF.integrable_mul_comp (hc.mul_prod hα) _ (by fun_prop))

/-- Averaging twice is averaging against a convolution: for F measurable and bounded, α and p
integrable and a in G_∞, applying R(p), then right translation by a, then R(α) is R of the function
y ↦ ∫ α(x) p((xa)⁻¹y) dx. Here R = `realConv` is right convolution over G_∞. -/
theorem realConv_realConv (hF : IsBoundedMeasurable F) (hα : Integrable α) {p : GInf E s → ℂ}
    (hp : Integrable p) (a : GInf E s) :
    realConv α (fun g : G E s ↦ realConv p F (g * (a, 1))) =
      realConv (fun y : GInf E s ↦ ∫ x : GInf E s, α x * p ((x * a)⁻¹ * y)) F := by
  ext ⟨g, k⟩
  -- Fubini's theorem and a left translation of the inner variable by `x * a`.
  have h_meas : Measurable fun x : GInf E s ↦ ((g * x, k) : G E s) := by fun_prop
  have h_conv := integral_smul_integral_eq_integral_conv_smul (fun x : GInf E s ↦ x * a) hα hp
      (hF.comp h_meas) (by fun_prop)
  simpa [realConv, mul_assoc, Prod.mul_def, smul_eq_mul] using h_conv

/-- For a cusp kernel e (an integrable idempotent kernel on G_∞ with decay, `IsCuspKernel`) there is
a continuous compactly supported α on G_∞ with α ∗ e = e, and so R(α)R(e)F = R(e)F for every bounded
measurable F on G. Here R(α)F(g) = ∫_{G_∞} α(x) F(gx) dx is `realConv`. -/
theorem IsCuspKernel.exists_realConv_realConv_eq {B : ℕ} {e : GInf E s → ℂ}
    (he : IsCuspKernel B e) :
    ∃ α : GInf E s →C_c ℂ,
      (∀ y : GInf E s, ∫ x : GInf E s, α x * e (x⁻¹ * y) = e y) ∧
      ∀ F : G E s → ℂ, IsBoundedMeasurable F → realConv α (realConv e F) = realConv e F := by
  obtain ⟨α, hα⟩ := he.exists_bump
  refine ⟨α, hα, fun F hF ↦ ?_⟩
  simpa [hα, Prod.mk_one_one] using realConv_realConv hF α.integrable he.integrable 1

/-- Rank one formula for operators. Let α be an idempotent kernel on G_∞ (continuous, integrable,
α(g⁻¹) = conj(α(g)), α(1) ≠ 0, and ∫ α(z) α(x⁻¹z⁻¹y) dz = α(x⁻¹) α(y) / α(1)), x a real point, and F
on G bounded and measurable. Then applying R(α)F(g) = ∫_{G_∞} α(z) F(gz) dz, then right translation
by (x, 1), then R(α) again gives conj(α(x))/α(1) times R(α)F. For the kernel e_λ of a discrete
series the factor is the coefficient c_λ(x). -/
theorem IsIdempotentKernel.realConv_translate_realConv (hα : IsIdempotentKernel α)
    (hF : IsBoundedMeasurable F) (x : GInf E s) (g : G E s) :
    realConv α (fun g' : G E s ↦ realConv α F (g' * (x, 1))) g =
      starRingEnd ℂ (α x) / α 1 * realConv α F g := by
  -- The two averages combine into one, against a function that `hα.convolution_eq` computes.
  calc
    _ = realConv (fun y : GInf E s ↦ ∫ z : GInf E s, α z * α ((z * x)⁻¹ * y)) F g :=
      congrFun (realConv_realConv hF hα.integrable hα.integrable x) g
    _ = realConv (fun y : GInf E s ↦ α x⁻¹ / α 1 * α y) F g := by simp only [hα.convolution_eq]
    _ = α x⁻¹ / α 1 * realConv α F g := by simp [realConv, ← integral_const_mul, mul_assoc]
    _ = starRingEnd ℂ (α x) / α 1 * realConv α F g := by rw [hα.apply_inv]

/-- For bounded measurable `F`, `F'` and integrable `α`, the convolution in the right argument may
be taken out of the Petersson product `V.petersson`, the integral of `conj F' * F` over `Γ \ G`. -/
theorem Space.petersson_realConv_right (hF : IsBoundedMeasurable F) (hα : Integrable α)
    {F' : G E s → ℂ} (hF' : IsBoundedMeasurable F') :
    V.petersson F' (realConv α F) =
      ∫ x : GInf E s, α x * V.petersson F' fun g : G E s ↦ F (g * (x, 1)) := by
  have hF'_int : Integrable (star F') V.quotMeasure := hF'.memLp_top.star.integrable le_top
  simpa [petersson] using integral_mul_realConv hF hα hF'_int id measurable_id

/-- If F on G is measurable, bounded and right invariant under an open subgroup of G_f, and α is
integrable on G_∞, then R(α)F is continuous. -/
theorem continuous_realConv (K : OpenSubgroup (Gf E n)) (hF : IsBoundedMeasurable F)
    (h_level : HasLevel F K) (hα : Integrable α) : Continuous (realConv α F) := by
  obtain ⟨C, hC⟩ := hF.bounded
  -- At `g`, the difference `R(α)F(gz) - R(α)F(g)` is `o(C)` as `z → 1`.
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  have h_small : (fun z : G E s ↦ realConv α F (g * z) - realConv α F g) =o[nhds 1]
      fun _ : G E s ↦ C := by
    refine .of_bound fun ε hε ↦ ?_
    filter_upwards [eventually_norm_realConv_sub_le K hα hε] with z hz
    exact hz C hF h_level g fun x _ ↦ hC (g * (x, 1))
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, ← map_mul_left_nhds_one g]
  exact Filter.tendsto_map' (h_small.tendsto_zero_of_tendsto tendsto_const_nhds)

/-- If F on G is measurable, bounded, left Γ-invariant and right invariant under an open
subgroup of G_f, and α is integrable on G_∞, then R(α)F is automorphic (continuous,
Γ-invariant, with a level) and bounded. -/
theorem Space.isAutomorphic_realConv (K : OpenSubgroup (Gf E n)) (hF : IsBoundedMeasurable F)
    (hF_rat : V.Γ.FixesLeft F) (hF_level : HasLevel F K) (hα : Integrable α) :
    V.IsAutomorphic (realConv α F) ∧ IsBoundedMeasurable (realConv α F) := by
  obtain ⟨C, hC⟩ := hF.bounded
  -- The bound is `C` times the L¹ norm of `α`; the invariances pass under the integral.
  have h_bound (g : G E s) : ‖realConv α F g‖ ≤ ∫ x, ‖α x‖ * C :=
    norm_integral_le_of_norm_le (hα.norm.mul_const C) (by simp [mul_le_mul, hC])
  have h_rat : V.Γ.FixesLeft (realConv α F) := fun γ hγ g ↦ by
    simp only [realConv, mul_assoc γ, hF_rat γ hγ]
  have h_cont : Continuous (realConv α F) := continuous_realConv K hF hF_level hα
  exact ⟨⟨h_cont, h_rat, K, hasLevel_realConv K hF_level⟩, .of_continuous ⟨_, h_bound⟩ h_cont⟩

/-- Let α be an idempotent kernel on G_∞ (`New.IsIdempotentKernel`: continuous, integrable,
α(g⁻¹) = conj(α(g)), α(1) ≠ 0, and ∫ α(z) α(x⁻¹z⁻¹y) dz = α(x⁻¹) α(y) / α(1)). Let K be an open
subgroup of G_f, and F on G bounded, measurable, left invariant under the subgroup `V.Γ` and right
invariant under K. Then R(α)F(g) = ∫_{G_∞} α(x) F(gx) dx is a form of type α (automorphic, bounded
and fixed by R(α)) fixed by right translation by K, that is an element of
`New.levelSpace (V.formRep α) K`. -/
theorem Space.exists_form_eq_realConv (K : OpenSubgroup (Gf E n)) (hF : IsBoundedMeasurable F)
    (hF_rat : V.Γ.FixesLeft F) (hF_level : HasLevel F K) (hα : IsIdempotentKernel α) :
    ∃ y : levelSpace (V.formRep α) K.toSubgroup, (y.val : G E s → ℂ) = realConv α F := by
  obtain ⟨h_aut, h_bdd⟩ := isAutomorphic_realConv K hF hF_rat hF_level hα.integrable
  -- R(α) fixes R(α)F because α * α = α.
  have h_fix : realConv α (realConv α F) = realConv α F := by
    simpa [Prod.mul_def, hα.convolution_self] using
      realConv_realConv hF hα.integrable hα.integrable 1
  exact ⟨⟨⟨realConv α F, h_aut, h_bdd.bounded, fun _ ↦ h_fix⟩,
    mem_levelSpace_formRep_iff.2 (hasLevel_realConv K hF_level)⟩, rfl⟩

end New

end RealConvolution

/-!
## The Petersson product under translation and convolution

The product `New.Space.petersson F F'` is the integral of `conj F * F'` over `Γ \ G`. A form of type
`e` (`New.Space.IsForm`) is a bounded automorphic function fixed by `realConv e` when `e` is
integrable.

In `New.Space.IsForm.realConv_translate`, `New.Space.IsForm.petersson_real_translate` and
`New.Space.IsForm.petersson_realConv_realConv`, `e` is taken to be a cusp kernel
(`New.IsCuspKernel`), though of its properties only those of an idempotent kernel are used.
-/

section Petersson

open MeasureTheory ComplexConjugate InnerProductSpace

namespace New.Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {e : GInf E s → ℂ} {F F' : G E s → ℂ} {B : ℕ}

/-! ### Translation -/

/-- For a continuous left `V.Γ`-invariant function F on G and x in G, the right translate
g ↦ F(gx) has the same integral over `Γ \ G` as F, and it is integrable if and only if F is. -/
lemma integral_comp_mul_right (x : G E s) (h_rat : V.Γ.FixesLeft F)
    (hF : Continuous F := by fun_prop) :
    ∫ g : G E s, F (g * x) ∂V.quotMeasure = ∫ g : G E s, F g ∂V.quotMeasure ∧
    (Integrable (fun g : G E s ↦ F (g * x)) V.quotMeasure ↔ Integrable F V.quotMeasure) := by
  have h : ProbabilityTheory.IdentDistrib (fun g ↦ F (g * x)) F V.quotMeasure V.quotMeasure :=
    identDistrib_orbitMeasure_mul_right x fun γ ↦ h_rat γ γ.property
  exact ⟨h.integral_eq, h.integrable_iff⟩

theorem inner_eq_petersson (y y' : V.Form e) : ⟪y, y'⟫_ℂ = V.petersson y y' := rfl

/-- For automorphic functions `F`, `F'` and the Petersson product, right translation by `x⁻¹` is
adjoint to right translation by `x`. -/
lemma IsAutomorphic.petersson_comp_mul_right (hF : V.IsAutomorphic F) (hF' : V.IsAutomorphic F')
    (x : G E s) :
    V.petersson (fun g : G E s ↦ F (g * x)) F' = V.petersson F (fun g : G E s ↦ F' (g * x⁻¹)) := by
  have h_inv : V.Γ.FixesLeft fun g : G E s ↦ conj (F g) * F' (g * x⁻¹) := fun γ hγ g ↦ by
    simp [mul_assoc γ, hF.rat_mul γ hγ, hF'.rat_mul γ hγ]
  have := hF.continuous
  have := hF'.continuous
  -- Translate the integrand `conj (F g) * F' (g * x⁻¹)` by `x`.
  simpa [petersson] using (integral_comp_mul_right x h_inv).1

/-- The finite points act on forms of type `e` by isometries of the Petersson product. -/
theorem inner_formRep (k : Gf E n) (y y' : V.Form e) :
    ⟪V.formRep e k y, V.formRep e k y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
  -- Move the translation by `(1, k)` from the left factor to the right one, where it cancels.
  change V.petersson (fun g ↦ y (g * (1, k))) (fun g ↦ y' (g * (1, k))) = V.petersson y y'
  simpa [-Prod.inv_mk] using
    y.prop.petersson_comp_mul_right (y'.prop.comp_mul_right k).toIsAutomorphic (1, k)

@[simp]
theorem conj_petersson : conj (V.petersson F F') = V.petersson F' F := by
  simp [petersson, mul_comm, ← integral_conj]

/-! ### Forms of type `e` -/

/-- Right convolution with an idempotent kernel `e` is self-adjoint for the Petersson product on
bounded automorphic functions, because `e y⁻¹ = conj (e y)`. -/
theorem petersson_realConv_comm (he : IsIdempotentKernel e) (hF_aut : V.IsAutomorphic F)
    (hF_bdd : IsBoundedMeasurable F) (hF'_aut : V.IsAutomorphic F')
    (hF'_bdd : IsBoundedMeasurable F') :
    V.petersson F (realConv e F') = V.petersson (realConv e F) F' := by
  -- Move the translation by `y` across the product, use `e y⁻¹ = conj (e y)`, and invert the
  -- variable.
  calc
    _ = ∫ y : GInf E s, e y * V.petersson F fun g : G E s ↦ F' (g * (y, 1)) :=
      petersson_realConv_right hF'_bdd he.integrable hF_bdd
    _ = ∫ y : GInf E s, e y * V.petersson (fun g : G E s ↦ F (g * (y⁻¹, 1))) F' := by
      simp [hF_aut.petersson_comp_mul_right hF'_aut]
    _ = conj (∫ y : GInf E s, e y⁻¹ * V.petersson F' fun g : G E s ↦ F (g * (y⁻¹, 1))) := by
      simp [he.apply_inv, ← integral_conj]
    _ = conj (∫ y : GInf E s, e y * V.petersson F' fun g : G E s ↦ F (g * (y, 1))) := by
      rw [integral_inv_eq_self (fun y ↦ e y * V.petersson F' fun g ↦ F (g * (y, 1))) volume]
    _ = V.petersson (realConv e F) F' := by
      rw [← petersson_realConv_right hF_bdd he.integrable hF'_bdd, conj_petersson]

/-- Let `e` be an idempotent kernel, `F` a form of type `e` and `T` a bounded automorphic function.
Replacing `T` by its right convolution `realConv e T` does not change the Petersson product of `F`
and `T`: convolution by `e` is self-adjoint and fixes `F`. -/
theorem IsForm.petersson_realConv (he : IsIdempotentKernel e) (hF : V.IsForm e F) {T : G E s → ℂ}
    (hT_aut : V.IsAutomorphic T) (hT_bdd : IsBoundedMeasurable T) :
    V.petersson F (realConv e T) = V.petersson F T := by
  rw [petersson_realConv_comm he hF.toIsAutomorphic hF.isBoundedMeasurable hT_aut hT_bdd,
    hF.realConv_eq he.integrable]

/-- For a hermitian space `V` over the CM field `E` with signs `s`, let `F` be a function on the
unitary group `G E s` that is a form of type `e`, where `e` is a function on the archimedean group
`GInf E s`. Being a form of type `e` means `F` is automorphic, bounded, and fixed by right
convolution with `e` when `e` is integrable. Then the complex conjugate `star F` is a form of type
`star e`. -/
theorem IsForm.conj (h : V.IsForm e F) : V.IsForm (star e) (star F) := by
  refine ⟨h.toIsAutomorphic.conj, h.bounded.imp (by simp), fun h_int ↦ funext fun g ↦ ?_⟩
  have h_fix : realConv e F = F := h.realConv_eq ((starL' ℝ).integrable_comp_iff.1 h_int)
  simpa [realConv, ← integral_conj] using congrArg (starRingEnd ℂ) (congrFun h_fix g)

/-- Rank one formula. Let `e` be a cusp kernel (a minimal idempotent on G_∞ with the decay
conditions of `IsCuspKernel`), `F` a form of type `e` (bounded automorphic on G, fixed by right
convolution with `e`), and `x` a real point. Convolution by `e` sends the translate `F (· * (x, 1))`
to `conj (e x) / e 1` times `F`. The left side is the value at `g` of `realConv e` applied to that
translate. For the kernel e_λ of a discrete series the factor is the coefficient c_λ(x). -/
theorem IsForm.realConv_translate (he : IsCuspKernel B e) (h : V.IsForm e F) (x : GInf E s)
    (g : G E s) :
    ∫ z : GInf E s, e z * F (g * (z, 1) * (x, 1)) = conj (e x) / e 1 * F g := by
  have h_fix : realConv e F = F := h.realConv_eq he.integrable
  calc
    _ = realConv e (fun g' : G E s ↦ realConv e F (g' * (x, 1))) g := by rw [h_fix, realConv]
    _ = conj (e x) / e 1 * F g := by
      rw [he.toIsIdempotentKernel.realConv_translate_realConv h.isBoundedMeasurable x g, h_fix]

/-- For a cusp kernel `e`, forms `F`, `F'` of type `e` and a real point `x`, the Petersson product
of `F` with the translate `F' (· * (x, 1))` is `conj (e x) / e 1` times the product of `F` and
`F'`. -/
theorem IsForm.petersson_real_translate (he : IsCuspKernel B e) (h : V.IsForm e F)
    (h' : V.IsForm e F') (x : GInf E s) :
    V.petersson F (fun g : G E s ↦ F' (g * (x, 1))) = conj (e x) / e 1 * V.petersson F F' := by
  have rank_one : realConv e (fun g : G E s ↦ F' (g * (x, 1))) =
      fun g : G E s ↦ conj (e x) / e 1 * F' g :=
    funext (h'.realConv_translate he x)
  -- Convolve the translate of `F'` with `e`, which does not change its product with `F`, and apply
  -- the rank one formula.
  rw [← h.petersson_realConv he.toIsIdempotentKernel (h'.toIsAutomorphic.comp_mul_right (x, 1))
    (h'.isBoundedMeasurable.comp (measurable_mul_const (x, 1))), rank_one]
  simp [petersson, mul_left_comm, ← integral_const_mul]

/-- For a cusp kernel `e`, forms `F`, `F'` of type `e` and integrable `α`, `β` on the real points,
the product of `realConv α F` and `realConv β F'` is the product of `F` and `F'` times
∫∫ conj(α(x)) β(y) conj(e(x⁻¹y))/e(1) dy dx. -/
theorem IsForm.petersson_realConv_realConv (he : IsCuspKernel B e) (h : V.IsForm e F)
    (h' : V.IsForm e F') {α β : GInf E s → ℂ} (hα : Integrable α) (hβ : Integrable β) :
    V.petersson (realConv α F) (realConv β F') =
      (∫ x : GInf E s, ∫ y : GInf E s, conj (α x) * β y * (conj (e (x⁻¹ * y)) / e 1)) *
        V.petersson F F' := by
  obtain ⟨K, hK⟩ := h'.exists_level
  have hβ_bdd : IsBoundedMeasurable (realConv β F') :=
    (isAutomorphic_realConv K h'.isBoundedMeasurable h'.rat_mul hK hβ).2
  -- The product of two real translates depends only on `x⁻¹ * y`, through the rank one idempotent.
  have h_translates (x y : GInf E s) :
      V.petersson (fun g : G E s ↦ F (g * (x, 1))) (fun g : G E s ↦ F' (g * (y, 1))) =
        conj (e (x⁻¹ * y)) / e 1 * V.petersson F F' := by
    rw [h.petersson_comp_mul_right (h'.toIsAutomorphic.comp_mul_right (y, 1)),
      ← h.petersson_real_translate he h']
    simp [mul_assoc]
  -- Unfold the convolution with `β` in the right argument.
  have h_right (x : GInf E s) :
      V.petersson (fun g : G E s ↦ F (g * (x, 1))) (realConv β F') =
        ∫ y : GInf E s, β y * (conj (e (x⁻¹ * y)) / e 1 * V.petersson F F') := by
    simp only [petersson_realConv_right h'.isBoundedMeasurable hβ
      (h.isBoundedMeasurable.comp (measurable_mul_const (x, 1))), h_translates]
  -- Conjugate symmetry moves the convolution with `α` to the right argument and back.
  calc
    _ = conj (∫ x, α x * V.petersson (realConv β F') fun g ↦ F (g * (x, 1))) := by
      rw [← conj_petersson, petersson_realConv_right h.isBoundedMeasurable hα hβ_bdd]
    _ = ∫ x, conj (α x) * V.petersson (fun g ↦ F (g * (x, 1))) (realConv β F') := by
      simp [← integral_conj]
    _ = _ := by simp [h_right, mul_assoc, ← integral_const_mul, ← integral_mul_const]

end New.Space

end Petersson

/-! ## Poincaré series projected to forms -/

section Poincare

open MeasureTheory ENNReal New
variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {V : Space E n s} {e : GInf E s → ℂ}

/-- Let `W i` be countably many measurable functions on `G` with `∑ i, ‖W i‖` bounded, whose sum is
left invariant under the rational points `V.Γ` and right invariant under the open subgroup `K` of
the finite points. Then the sum of the right convolutions of the `W i` with the idempotent kernel
`e` is an element of `levelSpace (V.formRep e) K`, that is a form of type `e` fixed by `K`. -/
theorem New.Space.exists_form_eq_tsum_of_fixesLeft (he : IsIdempotentKernel e)
    (K : OpenSubgroup (Gf E n)) {ι : Type*} [Countable ι] {W : ι → G E s → ℂ}
    (hW_meas : ∀ i : ι, Measurable (W i))
    (h_invariant : V.Γ.FixesLeft fun g : G E s ↦ ∑' i : ι, W i g)
    (h_level : HasLevel (fun g : G E s ↦ ∑' i : ι, W i g) K)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (h_le : ∀ g : G E s, ∑' i : ι, ‖W i g‖ₑ ≤ M) :
    ∃ y : levelSpace (V.formRep e) K.toSubgroup,
      (y.val : G E s → ℂ) = fun g : G E s ↦ ∑' i : ι, realConv e (W i) g := by
  -- The series is the convolution with `e` of the bounded sum of the `W i`.
  have h_bounded (g : G E s) : ‖∑' i : ι, W i g‖ ≤ M.toReal := by
    simpa using toReal_mono hM (eNorm_tsum_le_tsum_eNorm.trans (h_le g))
  -- Convolve term by term: the kernel is integrable and the sum of the norms is at most `M`.
  have h_termwise (g : G E s) :
      ∑' i : ι, realConv e (W i) g = realConv e (fun x : G E s ↦ ∑' i : ι, W i x) g := by
    have := he.continuous.measurable
    simp only [realConv, ← tsum_mul_left]
    refine (hasSum_integral_of_lintegral_tsum_lt_top ?_).tsum_eq
    calc ∫⁻ x : GInf E s, ∑' i : ι, ‖e x * W i (g * (x, 1))‖ₑ
        ≤ ∫⁻ x : GInf E s, ‖e x‖ₑ * M := by
          simp only [eNorm_mul, ENNReal.tsum_mul_left]
          grw [h_le]
      _ < ⊤ := by
          rw [lintegral_mul_const' _ _ hM]
          exact mul_lt_top he.integrable.hasFiniteIntegral hM.lt_top
  simp only [h_termwise]
  exact exists_form_eq_realConv K ⟨by fun_prop, M.toReal, h_bounded⟩ h_invariant h_level he

/-- **Poincaré series.** Let the sum of countably many measurable `W i`, with `∑ i, ‖W i‖` bounded,
be the sum over `V.Γ` of the left translates of one function `c` that is right invariant under the
open subgroup `K` of the finite points. Then the sum of the right convolutions of the `W i` with
the idempotent kernel `e` is a form of type `e` fixed by `K`. -/
theorem New.Space.exists_form_eq_tsum (he : IsIdempotentKernel e) (K : OpenSubgroup (Gf E n))
    {ι : Type*} [Countable ι] {W : ι → G E s → ℂ} (hW_meas : ∀ i : ι, Measurable (W i))
    {c : G E s → ℂ} (hc_level : HasLevel c K)
    (h_sum : ∀ g : G E s, ∑' γ : V.Γ, c (γ.val * g) = ∑' i : ι, W i g) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h_le : ∀ g : G E s, ∑' i : ι, ‖W i g‖ₑ ≤ M) :
    ∃ y : levelSpace (V.formRep e) K.toSubgroup,
      (y.val : G E s → ℂ) = fun g : G E s ↦ ∑' i : ι, realConv e (W i) g := by
  have h_invariant : V.Γ.FixesLeft fun g : G E s ↦ ∑' i : ι, W i g := fun γ hγ g ↦ by
    simpa [← h_sum, mul_assoc] using (Equiv.mulRight (⟨γ, hγ⟩ : V.Γ)).tsum_eq fun δ ↦ c (δ * g)
  have h_level : HasLevel (fun g : G E s ↦ ∑' i : ι, W i g) K := fun k hk g ↦ by
    simp only [← h_sum, ← mul_assoc, hc_level k hk]
  exact exists_form_eq_tsum_of_fixesLeft he K hW_meas h_invariant h_level hM h_le

end Poincare
