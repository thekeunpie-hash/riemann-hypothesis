module

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.UniformSpace.Uniformizable
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.NumberField.Countable
public import Lib.SiegelWeil.OneVector.SiegelClassSum
public import New.Spanning.Frames.TopFloor
public import New.Spanning.MainTerm.FillingLevel
import Lib.Shimura.ComplexTheta.AppellHumbertData
import New.Spanning.MainTerm.GlobalToLocal
public import New.Spanning.Unfolding.Climbing
import New.Spanning.Unfolding.ReducedGroups
import New.Spanning.Frames.FiniteShells
import New.Spanning.Frames.FixedLines
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Pi
public import New.Spanning.RemainingTerms.Size

section
/-!
# Siegel's formula as an upper bound, and domination of class sums by the density at the last entry

Finite-place estimate of the filling theorem: global sums are bounded by integrals over the product
of the completions at a finite set `T` of places, stable under conjugation.

* `New.Filling.adelicFrequency`, `New.Filling.localFrequency`: passage between skew-adjoint
  frequencies at `T` and self-adjoint finite adeles, through multiplication by `-ϖ⁻¹` and `-ϖ`,
  where `ϖ = S.deltaE` generates the different.
* `New.Filling.normDensity_indicator_eq_mul`: the density of a test function that is `Ψ` at `T` and
  the indicator of the lattice off `T` splits into an integral of Gauss sums of the lattice and the
  density of `Ψ` at `T`.
* `New.Filling.IsFillingData.enorm_normDensity_le_mul_lintegral_normFiberMeasure`: this density is
  at most `1 + b⁻⁶` times the volume of the lattice times the integral of `Ψ` over the sphere of `β`
  at `T`.
* `New.Filling.IsFillingData.siegel_sum_le_lintegral_sphere`: Siegel's formula bounds the sum of a
  step function over rational points with last entry `t` by a constant times its integral over the
  sphere of `t`.
* `New.Filling.IsFillingData.exists_step_sum_fiberPairing`: for any matrix `R`, the positive part of
  the real part of the sum of the fiber pairings against `R` is, on the top quadric, the restriction
  of a compactly supported invariant step function.
* `New.Filling.IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity`: the squared
  norms of class sums with one last entry `t` are bounded by `(1 + b⁻⁶) * S.scaledSiegelConst` times
  archimedean densities and densities at `T`, divided by the normalized mass.

The `IsFillingData` results assume `S` admissible, `S.ideleM⁻¹` integral off `T` and `F` filling
data. Conventions: `Φ v` is the embedding of the CM type at `v`. The last entry of `γ` is the
product of the last frame vector with its image under `γ`.

Notions from other files:
* `New.Floors.IntegralPlace`: A structure on `LocProd T`, the product of the completions at `T`: an
  open compact self-dual subring `R` of volume one, a character `ψ`, a trace-one element `τ`, a skew
  unit and the modulus `modulus`.
* `New.Filling.IsAdmissible`: The standing hypotheses: `sourceLevel` is the preimage of K(M),
  `reduction` is onto, and size inequalities hold between b and ϖ, κ_v, N, `besselDegree`, the
  second moments, the number of Bessel coordinates, an index and the mass.
* `New.Filling.latticeStabilizer`: The group `K` of integral points of the finite adelic unitary
  group; `New.Floors.PlaceData.congruenceSubgroup` is the group `K(M)` at `T`, the kernel of
  reduction modulo `M`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

namespace New.Filling

open NumberField MeasureTheory Matrix ENNReal NNReal Fintype Filter Topology Floors FloorGroups Set
  OpenAddSubgroup Finset Complex IntegralPlace CoordChange IsLargeLatticeData ComplexOrder

section

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {T : Finset (FinPlace E)} [T.StarStable]

section Factorisation

variable (S T) in
/-- A skew frequency `b` at the places of `T`, as a self-adjoint finite adele: extend by zero and
multiply by `-ϖ⁻¹`, where `ϖ = S.deltaE` generates the different. -/
noncomputable def adelicFrequency (b : skewAdjoint (LocProd T)) : selfAdjoint (𝔸f E) :=
  ⟨(-S.deltaE.val⁻¹ : E) * adeleOfLocal T b.val, by
    simp [selfAdjoint.mem_iff, ← adeleOfLocal_star, skewAdjoint.star_val_eq,
      ← coe_star_ringOfIntegers, S.star_deltaE]⟩

variable (S T) in
/-- The part at the places of `T` of a self-adjoint finite adele, multiplied by `-ϖ`, where `ϖ =
S.deltaE` generates the different. -/
noncomputable def localFrequency (z : selfAdjoint (𝔸f E)) : skewAdjoint (LocProd T) :=
  ⟨evalPlaces T ((-S.deltaE.val : E) * z.val), by
    simp [skewAdjoint.mem_iff, star_evalPlaces, ← coe_star_ringOfIntegers, S.star_deltaE]⟩

@[fun_prop] lemma continuous_adelicFrequency : Continuous (S.adelicFrequency T) :=
  .subtype_mk (by fun_prop) _

@[fun_prop] lemma continuous_localFrequency : Continuous (S.localFrequency T) :=
  .subtype_mk (by fun_prop) _

lemma adelicFrequency_add (b b' : skewAdjoint (LocProd T)) :
    S.adelicFrequency T (b + b') = S.adelicFrequency T b + S.adelicFrequency T b' :=
  Subtype.ext (by simp [adelicFrequency, mul_add])

/-- `adelicFrequency` is a section of `localFrequency`, compatibly with translations. -/
lemma localFrequency_adelicFrequency_add (b : skewAdjoint (LocProd T)) (z : selfAdjoint (𝔸f E)) :
    S.localFrequency T (S.adelicFrequency T b + z) = b + S.localFrequency T z := by
  ext1
  simp [localFrequency, adelicFrequency, mul_add, ← mul_assoc, ← map_mul (algebraMap E (𝔸f E))]

/-- The difference of a self-adjoint adele `z` and `adelicFrequency (localFrequency z)` vanishes at
`T`, so it kills the adeles that vanish off `T`. -/
lemma sub_adelicFrequency_mul_adeleOfLocal (z : selfAdjoint (𝔸f E)) (a : LocProd T) :
    (z.val - S.adelicFrequency T (S.localFrequency T z)) * adeleOfLocal T a = 0 := by
  have h_inv : ((-S.deltaE.val⁻¹ : E) : 𝔸f E) * (-S.deltaE.val : E) = 1 := by simp [← map_mul]
  have h_eval : evalPlaces T (z.val - S.adelicFrequency T (S.localFrequency T z)) = 0 := by
    simp only [adelicFrequency, localFrequency, map_sub, map_mul (evalPlaces T),
      evalPlaces_adeleOfLocal, ← mul_assoc]
    rw [← map_mul, h_inv, map_one, one_mul, sub_self]
  rw [← adeleOfLocal_evalPlaces_mul, h_eval, zero_mul, map_zero]

variable [P : IntegralPlace (LocProd T)]

/-- Let `b` be skew in `LocProd T`, let `b̃ = S.adelicFrequency T b` be `-ϖ⁻¹ b` extended by zero,
and let `y` be a self-adjoint finite adele. Then `ψf E (b̃ y / 2) = P.ψ (τ b y_T)`, where `y_T` is
the part of `y` at `T` and `τ = P.element` has `τ + τ̄ = 1`. `P` is a place structure on `LocProd T`
whose character `P.ψ` is `x ↦ ψf E (-x / ϖ)` (`S.charOnPlaces T`). -/
lemma ψf_adelicFrequency_mul (hψ : P.ψ = S.charOnPlaces T) (b : skewAdjoint (LocProd T)) {y : 𝔸f E}
    (hy : star y = y) :
    (ψf E ((2⁻¹ : E) * (S.adelicFrequency T b * y)) : ℂ) = P.ψ
      (P.element * b * evalPlaces T y) := by
  let x : 𝔸f E := (-S.deltaE.val⁻¹ : E) * adeleOfLocal T (P.element * b * evalPlaces T y)
  have h_local : P.element * b * evalPlaces T y - star (P.element * b * evalPlaces T y) =
      evalPlaces T y * b := by
    rw [star_mul', star_mul', star_evalPlaces, hy, skewAdjoint.star_val_eq]
    linear_combination (evalPlaces T y * b) * P.element_add_star
  have h_trace : x + star x = S.adelicFrequency T b * y := by
    rw [star_mul', star_neg_inv_deltaE, ← adeleOfLocal_star, neg_mul, ← sub_eq_add_neg, ← mul_sub,
      ← map_sub, h_local, adeleOfLocal_evalPlaces_mul, adelicFrequency, mul_assoc, mul_comm y]
  rw [← h_trace, ψf_inv_two_mul_add_star, hψ, charOnPlaces_apply_eq_ψf]

/-- The phase `ψf E (ζ (x* x - β) / 2)` that detects the quadric `x* x = β` is a product of a phase
off `T` and a phase at `T`. The frequency `ζ` is the sum of `S.adelicFrequency T b` and of a
self-adjoint adele `z` for which `S.localFrequency T z` is integral. The vector `x` is the sum of a
vector `y` at `T`, extended by zero (`adeleOfLocal`), and of an adelic vector `w` integral at `T`.
`P` is a place structure on `LocProd T` whose character `P.ψ` is `x ↦ ψf E (-x / ϖ)`
(`S.charOnPlaces T`). -/
lemma ψf_quadric_eq_mul (hψ : P.ψ = S.charOnPlaces T) {κ : Type} [Fintype κ] {β : 𝔸f E}
    (hβ : star β = β) (b : skewAdjoint (LocProd T)) {z : selfAdjoint (𝔸f E)}
    (hz : (S.localFrequency T z : LocProd T) ∈ P.integers) (y : κ → LocProd T) {w : κ → 𝔸f E}
    (hw : evalPlaces T ∘ w ∈ intVectors P.integers κ) :
    let x : κ → 𝔸f E := adeleOfLocal T ∘ y + w
    let y' : κ → LocProd T := y + evalPlaces T ∘ w
    (ψf E ((2⁻¹ : E) * ((S.adelicFrequency T b + z).val * (star x ⬝ᵥ x - β))) : ℂ) =
      ψf E ((2⁻¹ : E) * ((z : 𝔸f E) * (star w ⬝ᵥ w - (β - adeleOfLocal T (evalPlaces T β))))) *
        P.ψ (P.element * (b + S.localFrequency T z).val * (star y' ⬝ᵥ y' - evalPlaces T β)) := by
  intro x y'
  set β' : 𝔸f E := β - adeleOfLocal T (evalPlaces T β)
  set b' : skewAdjoint (LocProd T) := S.localFrequency T z
  have hβ' : star β' = β' := by simp [β', ← adeleOfLocal_star, hβ]
  have norm_star (v : κ → 𝔸f E) : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := (star_dotProduct v v).symm
  have eval_x : evalPlaces T (star x ⬝ᵥ x - β) = star y' ⬝ᵥ y' - evalPlaces T β := by
    simp [x, y', dotProduct, ← star_evalPlaces]
  -- the values of the form at `x` and `w` differ only at `T`
  have h_diff : star x ⬝ᵥ x - β - (star w ⬝ᵥ w - β') = adeleOfLocal T
      (star y ⬝ᵥ y' + star (evalPlaces T ∘ w) ⬝ᵥ y - evalPlaces T β) := by
    simp [x, y', β', dotProduct, Finset.sum_add_distrib, mul_add, add_mul, adeleOfLocal_star,
      adeleOfLocal_evalPlaces_mul, mul_comm _ (evalPlaces T _), mul_comm (w _)]
    ring
  have h_arg : (S.adelicFrequency T b + z).val * (star x ⬝ᵥ x - β) =
      z * (star w ⬝ᵥ w - β') + S.adelicFrequency T (b + b') * (star x ⬝ᵥ x - β) -
        S.adelicFrequency T b' * (star w ⬝ᵥ w - β') := by
    rw [adelicFrequency_add, AddSubgroup.coe_add, AddSubgroup.coe_add]
    linear_combination (z.val - S.adelicFrequency T b') * h_diff +
      S.sub_adelicFrequency_mul_adeleOfLocal (T := T) z _
  -- the last term is integral at `T`, so its phase is one
  have h_int : P.ψ (P.element * b' * evalPlaces T (star w ⬝ᵥ w - β')) = 1 := by
    have h_norm : evalPlaces T (star w ⬝ᵥ w - β') ∈ P.integers := by
      simpa [β', dotProduct, ← star_evalPlaces] using
        sum_mem fun i _ ↦ mul_mem (P.isAdelic.star_mem (hw i)) (hw i)
    obtain ⟨tau_mem : P.element ∈ P.integers, -⟩ := P.data_normalised
    exact (P.self_dual _).2 h_norm _ (mul_mem tau_mem hz)
  rw [h_arg, mul_sub, mul_add, AddChar.map_sub_eq_div, AddChar.map_add_eq_mul, Circle.coe_div,
    Circle.coe_mul, ψf_adelicFrequency_mul hψ _ (by simp [norm_star, hβ]),
    ψf_adelicFrequency_mul hψ _ (by simp [norm_star, hβ']), h_int, div_one, eval_x]

/-- Let `f` be the function on adelic vectors that is `Ψ` at `T` times the indicator of the vectors
integral off `T`, and let `β` be hermitian. The density `normDensity f β = ∫ z, ∫ x, f x * ψf E (z
(x* x - β) / 2)` is a product of two factors. The first is the integral of the Gauss sums of the
standard lattice over the self-adjoint `z` for which `S.localFrequency T z`, the part of `-ϖ z` at
`T`, is integral. The second is the density of `Ψ` at `T`, with `P.skewMeasure` the measure on skew
elements and `P.element` of trace `1`. `P` is a place structure on `LocProd T` whose character `P.ψ`
is `x ↦ ψf E (-x / ϖ)` (`S.charOnPlaces T`).

This is a two-factor form of the factorization of the finite adelic density into local densities,
as in Siegel–Weil theory: the density at `T` and one integral of Gauss sums, not split over the
remaining places. -/
lemma normDensity_indicator_eq_mul (hψ : P.ψ = S.charOnPlaces T) {κ : Type} [Fintype κ]
    {Ψ : (κ → LocProd T) → ℝ≥0} (hΨ : Continuous Ψ) {β : 𝔸f E} (hβ : star β = β) :
    normDensity ((intVectors (integralOff T) κ : Set (κ → 𝔸f E)).indicator
        fun x : κ → 𝔸f E ↦ Ψ (evalPlaces T ∘ x)) β =
      (∫ z : selfAdjoint (𝔸f E) in
          {z : selfAdjoint (𝔸f E) | (S.localFrequency T z : LocProd T) ∈ P.integers},
        ∫ w : κ → 𝔸f E in (stdLattice E κ : Set (κ → 𝔸f E)),
          (ψf E ((2⁻¹ : E) *
            ((z : 𝔸f E) * (star w ⬝ᵥ w - (β - adeleOfLocal T (evalPlaces T β))))) : ℂ)) *
      ∫ b : skewAdjoint (LocProd T), ∫ y : κ → LocProd T,
        Ψ y * P.ψ (P.element * (b : LocProd T) * (star y ⬝ᵥ y - evalPlaces T β))
        ∂volume ∂P.skewMeasure := by
  -- Split first the frequency and then the vector into their parts at `T` and off `T`.
  let L : Set (κ → 𝔸f E) := intVectors (integralOff T) κ
  have L_meas : MeasurableSet L := (isOpen_intVectors (isOpen_integralOff T)).measurableSet
  obtain ⟨lat_open, -, lat_vol⟩ := P.isOpen_isCompact_volume_intVectors (ι := κ)
  obtain ⟨-, -, -, -, skew_vol⟩ := P.data_normalised
  have lattice_eq : (stdLattice E κ : Set (κ → 𝔸f E)) =
      (evalPlaces T ∘ ·) ⁻¹' intVectors P.integers κ ∩ L := by
    ext
    simp [coe_stdLattice, L, intVectors, mem_Ô_iff T, forall_and]
  -- the frequency: `adelicFrequency` is a section of `localFrequency`
  rw [normDensity]
  refine integral_eq_mul_of_section P.skewMeasure (by fun_prop) (by fun_prop)
    localFrequency_adelicFrequency_add
    (SemilocalField.isOpen_O.preimage continuous_subtypeVal).measurableSet skew_vol fun b z hz ↦ ?_
  rw [integral_withDensity_eq_integral_smul (.indicator (by fun_prop) L_meas), lattice_eq,
    ← setIntegral_indicator L_meas]
  -- the vector: `adeleOfLocal T` is a section of `evalPlaces T`
  have h_section (y : κ → LocProd T) (x : κ → 𝔸f E) :
      evalPlaces T ∘ (adeleOfLocal T ∘ y + x) = y + evalPlaces T ∘ x := by simp [funext_iff]
  refine integral_eq_mul_of_section volume (ι := (adeleOfLocal T ∘ ·)) (by fun_prop) (by fun_prop)
    h_section lat_open.measurableSet lat_vol fun y w hw ↦ ?_
  have mem_L : adeleOfLocal T ∘ y + w ∈ L ↔ w ∈ L :=
    forall_congr' fun i ↦ add_mem_cancel_left (adeleOfLocal_mem_integralOff T (y i))
  rw [ψf_quadric_eq_mul hψ hβ b hz y hw]
  by_cases hw' : w ∈ L
  · rw [Set.indicator_of_mem (mem_L.2 hw'), Set.indicator_of_mem hw', h_section, NNReal.smul_def,
      real_smul, mul_left_comm]
  · rw [Set.indicator_of_notMem (mem_L.not.2 hw'), Set.indicator_of_notMem hw', zero_smul, zero_mul]

end Factorisation

variable (S T) in
/-- The finite idele `π = S.piN`, with `π π̄ = N`, read at the places of `T`. -/
noncomputable abbrev piNAt : (LocProd T)ˣ := S.piN.map (evalPlaces T)

lemma piNAt_mul_star : S.piNAt T * star (S.piNAt T).val = (S.N : LocProd T) := by
  simpa [star_evalPlaces] using congrArg (evalPlaces T) S.piN_mul_star

end

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {T : Finset (FinPlace E)} [T.StarStable]

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose character is that of
`S`. Let `K(M) = F.congruenceSubgroup` be the group of integral isometries at `T` of the form
`S.latticeMiddle` congruent to `1` modulo `M`, let `Z` be a group between `K(M)` and the integral
isometries, and let `Z.Cosets` be the cosets of `K(M)` in `Z`. Write `μ = F.groupMeasure` for the
measure of the unitary group at `T` and `μ_H = F.measureH` for that of `H = besselH`, the fixer of
all basis vectors outside the definite part `X₀`. Then there is a real `D > 0` with two properties.
The constant `S.scaledSiegelConst` is `D` times the number of classes times the constant
`S.siegelConst` of Siegel's formula. The normalized mass
`Z.massRatio = μ Z * μ K(M) / F.unipotentMass ^ 2`, where `F.unipotentMass` is the product of the
floor volumes below `ϱ`, is at most `μ_H K(M) * (μ K(M) ^ 2 * card Z.Cosets) * D`. -/
lemma IsFillingData.exists_scaledSiegelConst_eq_and_massRatio_le
    [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) :
    ∃ D : ℝ,
      0 < D ∧
      S.scaledSiegelConst = D * Fintype.card S.Classes * S.siegelConst ∧
      Z.massRatio ≤ F.measureH F.congruenceSubgroup *
        (F.groupMeasure F.congruenceSubgroup ^ 2 * Fintype.card Z.Cosets) * ENNReal.ofReal D := by
  -- In `Z.massRatio = F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup / F.unipotentMass ^ 2`
  -- cover `Z` by the cosets of `F.congruenceSubgroup` and use
  -- `S.unipotentOrder * F.unipotentMass = 1`. Here `D = card (reducedImage besselS) *
  -- S.unipotentOrder = card (reducedImage besselH) * S.unipotentOrder ^ 2`.
  refine ⟨Nat.card (S.reducedImage besselS) * S.unipotentOrder, ?_, rfl, div_le_of_le_mul ?_⟩
  · have hM : 0 < S.M := two_pos.trans_le two_le_M
    have h_card : 0 < Nat.card (S.reducedImage besselS) := Nat.card_pos
    positivity
  -- for `F.measureH`, the group `F.congruenceSubgroup` has index `card (reducedImage besselH)` in
  -- the integral points
  obtain ⟨h_carried : ∀ᵐ z ∂F.measureH, z ∈ besselH,
      h_invariant : ∀ s ∈ besselH, F.measureH ∗ₘ .dirac s = F.measureH, -⟩ :=
        F.measureH_mem_and_invariant_and_le_one
  obtain ⟨-, h_box : F.boxSet = unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram,
      h_box_mass : F.measureH F.boxSet = 1, -⟩ := hF.volume_le_and_boxSet_closePairs_positions_eq
  have h_lift : ∀ᵐ z ∂F.measureH, ∃ x ∈ besselH, S.toPlaces T x = z ∧ S.IsIntegralOff T x := by
    filter_upwards [h_carried] with z hz
    obtain ⟨x, h_eq, h_off, -, h_mem⟩ := exists_isIntegralOff_toPlaces_eq z
    exact ⟨x, h_mem hz, h_eq, h_off⟩
  have index : Nat.card (S.reducedImage besselH) * F.measureH F.congruenceSubgroup = 1 := by
    rw [← h_box_mass, h_box]
    exact hF.card_reducedImage_mul_measure_congruenceSubgroup_eq h_lift fun x hx ↦
      h_invariant _ (hx.map_mem_agreeWithOneOn _)
  have cover : (Z.val : Set (U (S.latticeMiddle (LocProd T)).splitGram)) ⊆
      ⋃ d : Z.Cosets, (· * d.out.val⁻¹) ⁻¹' F.congruenceSubgroup :=
    fun y hy ↦ Set.mem_iUnion.2 ((Z.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq hy).imp
      fun d hd ↦ (hd d).2 rfl)
  have h_Z : F.groupMeasure Z ≤ Fintype.card Z.Cosets * F.groupMeasure F.congruenceSubgroup := by
    grw [cover, measure_iUnion_fintype_le]
    simp
  calc F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup
    _ ≤ Fintype.card Z.Cosets * F.groupMeasure F.congruenceSubgroup * F.groupMeasure
      F.congruenceSubgroup := by
      gcongr
    _ = Nat.card (S.reducedImage besselH) * F.measureH F.congruenceSubgroup *
        (F.groupMeasure F.congruenceSubgroup ^ 2 * Fintype.card Z.Cosets) *
        (S.unipotentOrder * F.unipotentMass) ^ 2 := by
      rw [index, hF.unipotentOrder_mul_unipotentMass_eq_one]
      ring
    _ = F.measureH F.congruenceSubgroup *
      (F.groupMeasure F.congruenceSubgroup ^ 2 * Fintype.card Z.Cosets) *
        ENNReal.ofReal (Nat.card (S.reducedImage besselS) * S.unipotentOrder) *
        F.unipotentMass ^ 2 := by
      rw [← Nat.cast_mul, ENNReal.ofReal_natCast, card_reducedImage_besselS]
      push_cast
      ring

variable [ok : S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)]

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- Let `N⁻¹` be integral off `T`, for the prime `N = S.N`. Let `β = (t t̄ - N²) / N` be positive
under the embeddings `Φ v` of the CM type, and let `C` be the constant of Siegel's formula in rank
`k = card 𝔰.κ` at `β`; its first factor `classSum stdRatPoints S.sourceLevel 1` is the mass of the
set `S.Classes` of double cosets of the level `S.sourceLevel` in the definite unitary group. Let `u`
be a unit at `T` with `u ū = N`, and `P.modulus u` its modulus. Then `‖C‖` times `1 + S.b⁻⁶`, the
volume `volÔ E ^ k` of the standard lattice and `P.modulus u` is
`(1 + S.b⁻⁶) * card S.Classes * S.siegelConst` times `(∏ v, (|t|_v² - N²)) ^ (k - 1)`. Here `S.b` is
the size parameter of `S` and `S.siegelConst = (π^k / ((k - 1)! N^k))^f |disc E|^(1/4) (volÔ E)^k`,
with `f` the number of infinite places. -/
lemma siegel_constant_eq (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    [P : IntegralPlace (LocProd T)] {t : E} {u : (LocProd T)ˣ} (hu : u * star u.val = S.N)
    (hβ_pos : ∀ v : InfinitePlace E, 0 < (Φ v ((t * star t - S.N ^ 2) / S.N)).re) {C : ℂ}
    (hC : (classSum stdRatPoints S.sourceLevel 1 * √√|NumberField.discr E| *
      ∏ v : InfinitePlace E, Real.pi ^ card 𝔰.κ / (card 𝔰.κ - 1).factorial *
        (Φ v ((t * star t - S.N ^ 2) / S.N)).re ^ (card 𝔰.κ - 1) : ℝ) = C) :
    ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k) * P.modulus u =
      .ofReal ((1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst *
        (∏ v : InfinitePlace E, (‖Φ v t‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) := by
  have hN₀ : 0 < S.N := S.N_prime.pos
  obtain ⟨d, h_rank : 1000 * (2 * 𝔰.ϱ + 2) + d = 𝔰.k⟩ := S.thousand_mul_le_k.dest
  -- The product formula for `N = u ū` gives `P.modulus u` as a power of `N⁻¹`.
  have h_formula : P.modulus (evalPlaces T ((S.N : E) : 𝔸f E)) ^ (2⁻¹ : ℝ) =
      (∏ v : InfinitePlace E, ‖Φ v (S.N : E)‖ₑ)⁻¹ :=
    P.modulus_evalPlaces_rpow_half (x := .mk0 _ (by simp [Nat.Prime.ne_zero])) ⟨by simp, hT_N⟩
  have h_md : P.modulus u.val = (‖(S.N : ℂ)‖ₑ ^ card (InfinitePlace E))⁻¹ := by
    simpa [← hu, ← sq, ← ENNReal.rpow_natCast_mul] using h_formula
  -- both sides are finite, so they are compared as real numbers
  have h_finite : ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k) * P.modulus u ≠ ∞ := by
    simp [mul_eq_top]
  refine (ofReal_toReal h_finite).symm.trans (congrArg _ ?_)
  set β : E := (t * star t - S.N ^ 2) / S.N
  rw [h_md, ← hC]
  -- evaluate the class sum of `1`, then expand `S.siegelConst` and `β`
  simp (disch := positivity) [classSum_sourceLevel_eq_sum, abs_of_nonneg, abs_of_pos (hβ_pos _),
    prod_mul_distrib]
  simp [siegelConst, β, mul_conj', sq, div_pow, ← h_rank, mul_add, Finset.prod_pow]
  field

section Level

variable [P : IntegralPlace (LocProd T)]
  {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

omit [IntegralPlace (LocProd T)] in
/-- Let `Ψ` be a function of compact support on the vectors of the whole space over the product
`LocProd T` of the completions at `T`. For `x` in the definite part `X₀` (basis `𝔰.κ`) let
`vectorOfLastEntry π τ x` be `x - (π π̄)⁻¹ τ z` in the basis `besselLatticeBasis 𝔰 π`, with `z` the
last frame vector. Then the function on adelic vectors `y` of `X₀` that is
`Ψ (vectorOfLastEntry π τ y_T)`, with `y_T` the part of `y` at `T`, times the indicator of the
vectors integral off `T` has compact support. -/
lemma hasCompactSupport_testFunction {Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0}
    (hΨ : HasCompactSupport Ψ) (π : (LocProd T)ˣ) (τ : LocProd T) :
    HasCompactSupport ((intVectors (integralOff T) 𝔰.κ : Set (𝔰.κ → 𝔸f E)).indicator
      fun y : 𝔰.κ → 𝔸f E ↦ Ψ (vectorOfLastEntry π τ (evalPlaces T ∘ y))) := by
  -- A vector in the support is an integral vector plus the extension by zero of its part at
  -- `T`, and that part is read off a point of the support of `Ψ`.
  let part (e : 𝔰.BesselIndex → LocProd T) (i : 𝔰.κ) : 𝔸f E :=
    adeleOfLocal T (((besselLatticeBasis 𝔰 π).val *ᵥ e) (𝔰.indexX₀ i))
  refine .of_support_subset_isCompact
    ((hΨ.image (f := part) (by fun_prop)).add stdLattice.isCompact_stdLattice) ?_
  rw [support_indicator]
  rintro y ⟨hy_int, hy_supp⟩
  let e : 𝔰.BesselIndex → LocProd T := vectorOfLastEntry π τ (evalPlaces T ∘ y)
  have h_int : ∀ i : 𝔰.κ, (y - part e) i ∈ Ô E := fun i ↦ by
    simpa [e, part, vectorOfLastEntry, sub_adeleOfLocal_mem_iff] using hy_int i
  exact ⟨part e, ⟨e, subset_closure hy_supp, rfl⟩, y - part e, h_int, add_sub_cancel ..⟩

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose character is that of
`S`. Let `f` be the function on adelic vectors `x` of `X₀` that is `Ψ (x - N⁻¹ t z)` at `T`
(`vectorOfLastEntry`, for `N = π π̄`, `π = S.piN` and a rational `t`) times the indicator of the
vectors integral off `T`. If `Ψ` is invariant under `besselH ⊓ F.congruenceSubgroup`, then `f` is
invariant under the level `S.sourceLevel` of the finite adelic unitary group `Gf E 𝔰.κ` of `X₀`. -/
lemma IsFillingData.testFunction_mulVec (hF : S.IsFillingData T F)
    {Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0}
    (hΨ : ∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → LocProd T,
      Ψ (k.val.val *ᵥ x) = Ψ x)
    (t : E) {k : Gf E 𝔰.κ} (hk : k ∈ S.sourceLevel) (y : 𝔰.κ → 𝔸f E) :
    let f : (𝔰.κ → 𝔸f E) → ℝ≥0 := (intVectors (integralOff T) 𝔰.κ : Set (𝔰.κ → 𝔸f E)).indicator
      fun x : 𝔰.κ → 𝔸f E ↦ Ψ (vectorOfLastEntry (S.piN.map (evalPlaces T)) (evalPlaces T t)
        (evalPlaces T ∘ x))
    f ((k : Matrix 𝔰.κ 𝔰.κ (𝔸f E)) *ᵥ y) = f y := by
  classical
  have h_int : k.val ∈ intGL 𝔰.κ (integralOff T) := by
    have h_full : k.val ∈ intGL 𝔰.κ (Ô E) := S.isLevel_sourceLevel.le hk
    grind [mem_intGL, mem_Ô_iff T]
  -- at `T` the matrix `k` acts on the vectors with last entry `t` as an element `k'` of
  -- `F.congruenceSubgroup`
  let k' : U (S.latticeMiddle (LocProd T)).splitGram := S.toPlaces T (S.inclHFin k)
  have hk' : k' ∈ besselH ⊓ F.congruenceSubgroup :=
    ⟨(inclHFin_mem_besselH k).map_mem_agreeWithOneOn _,
      (hF.mem_principalLevel_iff.mp (ok.sourceLevel_eq.le hk)).2⟩
  let tail (x : 𝔰.κ → 𝔸f E) : 𝔰.BesselIndex → LocProd T :=
    vectorOfLastEntry (S.piN.map (evalPlaces T)) (evalPlaces T t) (evalPlaces T ∘ x)
  have h_tail : tail (k.val.val *ᵥ y) = k'.val.val *ᵥ tail y := by
    have h_map : k'.val.val = (S.inclHFin k).val.val.map (evalPlaces T) := rfl
    ext1
    simp only [tail, vectorOfLastEntry_evalPlaces, h_map, ← RingHom.map_mulVec]
    simp [vectorOfLastEntry, inclHFin, toLatticeBasis, ← mulVec_mulVec,
      mulVec_mulVec _ (besselLatticeBasis ..).val, toBesselH, fromBlocks_mulVec]
  exact if_congr (mulVec_mem_intVectors_iff h_int) ((congrArg Ψ h_tail).trans (hΨ k' hk' _)) rfl

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- Let `M = S.ideleM` be the level, and let `F` be a filling datum at `T`: a large lattice datum of
modulus `M` for the place structure `P`, whose character is that of `S`. Let `Ψ ≥ 0` be continuous
of compact support on the vectors of rank `k = card 𝔰.κ` over the product `LocProd T` of the
completions at `T`, and let `β` be hermitian. Let `f` be `Ψ` at `T` times the indicator of the
vectors integral off `T`. The density `normDensity f β = ∫ z, ∫ x, f x * ψf E (z (x* x - β) / 2)`
has norm at most `1 + S.b⁻⁶` times the volume `volÔ E ^ k` of the standard lattice times the
integral of `Ψ` over the sphere `y* y = β` at `T`. The sphere carries the fiber measure
`P.normFiberMeasure` with index `δβ`, the product of `δ = P.skewUnit` and the part of `β` at `T`.

This is an upper bound form of the factorization into local densities in Siegel–Weil theory: the
factor at `T` is kept, and the remaining factor is only bounded, by `(1 + S.b⁻⁶) volÔ E ^ k`. -/
lemma IsFillingData.enorm_normDensity_le_mul_lintegral_normFiberMeasure
    (hF : S.IsFillingData T F)
    {Ψ : (𝔰.κ → LocProd T) → ℝ≥0} (hΨ : Continuous Ψ) (h_supp : HasCompactSupport Ψ) {β : 𝔸f E}
    (hβ : star β = β) {δβ : skewAdjoint (LocProd T)}
    (hδβ : P.skewUnit⁻¹.val * δβ = evalPlaces T β) :
    ‖normDensity ((intVectors (integralOff T) 𝔰.κ : Set (𝔰.κ → 𝔸f E)).indicator
        fun x : 𝔰.κ → 𝔸f E ↦ Ψ (evalPlaces T ∘ x)) β‖ₑ ≤
      .ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k *
        ∫⁻ y : 𝔰.κ → LocProd T, Ψ y ∂P.normFiberMeasure 𝔰.κ δβ := by
  have h_rank : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
  -- the exponent of the ideal zeta sum is `μ = 3ϱ + 4`, and `2 (μ + 1) ≤ k`
  have h_degree : 1 * Module.finrank ℚ E ≤ 2 ^ (2 * 𝔰.ϱ) :=
    S.mul_finrank_le_pow.trans' (by gcongr; lia)
  have h_zeta : idealZeta (Ô E) (𝔰.ϱ + 2 * 𝔰.ϱ + 4) ≤ .ofReal (1 + S.b⁻¹ ^ 6) := by
    grw [← S.half_pow_le_inv_pow_six]
    simpa using idealZeta_intAdeles_pow_le 𝔰.ϱ h_degree
  have h_card : 2 * (𝔰.ϱ + 2 * 𝔰.ϱ + 4 + 1) ≤ card 𝔰.κ := by
    simpa using show 2 * (𝔰.ϱ + 2 * 𝔰.ϱ + 4 + 1) ≤ 𝔰.k by omega
  rw [normDensity_indicator_eq_mul hF.psi_eq hΨ hβ, eNorm_mul]
  gcongr
  · -- the integral of Gauss sums off `T`
    grw [eNorm_integral_le_lintegral_eNorm, setLIntegral_le_lintegral, ← h_zeta]
    exact lintegral_gauss_sum_le_idealZeta
      (le_two_of_pow_le_ofReal (idealZeta_intAdeles_pow_le 𝔰.ϱ h_degree)) h_card _
  · simpa only [one_mulVec, hδβ] using enorm_localDensity_le
      (P.isDisintegration_normFiberMeasure F.two_le_card) conjTranspose_one hF.psi_add_star hΨ
        h_supp δβ

omit [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] ok in
/-- Let `t` be in `E`, read at `T` as `ratToPlaces T t`, and let `π = S.piNAt T` be the unit at `T`
with `π π̄ = N = S.N`. Then the index `lastEntrySphereIndex π t` of the sphere
`ω* ω = t t̄ / N - N`, divided by `P.skewUnit`, is the value at `T` of `β = (t t̄ - N²) / N`. -/
lemma skewUnit_inv_mul_lastEntrySphereIndex_piNAt (t : E) :
    P.skewUnit⁻¹.val * lastEntrySphereIndex (S.piNAt T) (ratToPlaces T t) =
      evalPlaces T (((t * star t - S.N ^ 2) / S.N : E) : 𝔸f E) := by
  set π : (LocProd T)ˣ := S.piNAt T
  set β : E := (t * star t - S.N ^ 2) / S.N
  have hπ : π * star π.val = S.N := piNAt_mul_star
  have h_rat : t * star t = S.N * (β + S.N) := by field [S.N_prime.ne_zero]
  have h_coe : (lastEntrySphereIndex π (ratToPlaces T t)).val = P.skewUnit *
      ((π * star π)⁻¹.val * ratToPlaces T t * star (ratToPlaces T t) - π * star π.val) := rfl
  rw [h_coe, Units.inv_mul_cancel_left, sub_eq_iff_eq_add, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
  simpa [hπ] using congrArg (ratToPlaces T) h_rat

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose character is that of
`S`. The space has the hyperbolic pairs `e_a, e*_a` (`a < ϱ`), a definite part `X₀` with basis `𝔰.κ`
and a vector `z`; `floorGroup 𝔰.ϱ` is the group of isometries that fix the hyperbolic pairs. Let
`γ₁`, `γ₂` be elements of this group over `E` with the same product `⟨z, γ z⟩`
(`S.frameProducts γ 𝔰.top 𝔰.top`) and the same `X₀`-part of `γ z`. Let `h_c` be the representative
of the double coset `c`, and let the left classes `c₁`, `c₂` be equal. If the translates
`h_c⁻¹ γ h_c'` (`S.translateByClassReps`) are integral off `T` and lie in one coset of
`F.congruenceSubgroup` at `T`, then `γ₁ = γ₂` and the right classes `c₁'`, `c₂'` are equal. -/
lemma IsFillingData.classes_eq_and_eq_of_inv_mul_mem_congruenceSubgroup (hF : S.IsFillingData T F)
    {c₁ c₂ c₁' c₂' : S.Classes} {γ₁ γ₂ : S.G E} (h_leftClass : c₁ = c₂)
    (hγ₁ : γ₁ ∈ floorGroup 𝔰.ϱ) (hγ₂ : γ₂ ∈ floorGroup 𝔰.ϱ)
    (h_tail : S.frameProducts γ₁ 𝔰.top 𝔰.top = S.frameProducts γ₂ 𝔰.top 𝔰.top)
    (h_col : ∀ l : 𝔰.κ, γ₁.val.val (𝔰.indexX₀ l) 𝔰.z = γ₂.val.val (𝔰.indexX₀ l) 𝔰.z)
    (h_off₁ : S.IsIntegralOff T (S.translateByClassReps c₁ c₁' γ₁))
    (h_off₂ : S.IsIntegralOff T (S.translateByClassReps c₂ c₂' γ₂))
    (h_coset : (S.toPlaces T (S.translateByClassReps c₁ c₁' γ₁))⁻¹ *
      S.toPlaces T (S.translateByClassReps c₂ c₂' γ₂) ∈ F.congruenceSubgroup) :
    c₁' = c₂' ∧ γ₁ = γ₂ := by
  -- `γ₁⁻¹` and `γ₂⁻¹` give the same point `FloorGroups.orbitPoint 𝔰.top`, so `γ₁⁻¹ γ₂` lies in
  -- `floorGroup 𝔰.n`; its `translateByClassReps` lies in `S.principalLevel`, which forces
  -- `c₁' = c₂'` and makes it unipotent, hence trivial.
  have same_z : FloorGroups.orbitPoint 𝔰.top γ₁⁻¹ = FloorGroups.orbitPoint 𝔰.top γ₂⁻¹ := by
    simpa [funext_iff, Unique.forall_iff, FloorGroups.orbitPoint,
      apply_eq_one_apply_of_mem_floorGroup hγ₁,
      apply_eq_one_apply_of_mem_floorGroup hγ₂, h_col, frameGram, splitGram, Matrix.mul_apply,
      middleGram, Nat.Prime.ne_zero] using h_tail
  have fixes : γ₁⁻¹ * γ₂ ∈ floorGroup 𝔰.n :=
    partialUnitriangularGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq hγ₁ hγ₂ same_z)
  have level : S.translateByClassReps c₁' c₂' (γ₁⁻¹ * γ₂) ∈ S.principalLevel := by
    have h_quotient : S.translateByClassReps c₁' c₂' (γ₁⁻¹ * γ₂) =
        (S.translateByClassReps c₁ c₁' γ₁)⁻¹ * S.translateByClassReps c₂ c₂' γ₂ := by
      simp [translateByClassReps, h_leftClass, mul_assoc]
    rw [h_quotient]
    exact hF.mem_principalLevel_iff.mpr ⟨mul_mem (inv_mem h_off₁) h_off₂, by simpa using h_coset⟩
  obtain ⟨hc', hU : γ₁⁻¹ * γ₂ ∈ besselU, -⟩ :=
    eq_and_mem_classUnipotent_of_besselS (mem_partialUnitriangularGroup_of_mem_floorGroup fixes)
      level
  exact ⟨hc', inv_mul_eq_one.mp <|
    eq_one_of_mem_floorGroup_inf ⟨fixes, (unipotentBelow_eq_besselU le_rfl).ge hU⟩ (by simp)⟩

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- Let `Z` be a group between the congruence group `F.congruenceSubgroup` and the integral
isometries, `R` a matrix and `ω p` finitely many heads. The fiber pairing
`F.fiberPairing Z (ω p) (ω q)` is the pairing of the orbital integrals `F.scaledOrbitalIntegral Z`
of two heads, integrated over `besselH`, the fixer of all basis vectors outside the definite part
`X₀`. On the top quadric the positive part of the real part of their sum against `R` agrees with a
function `Ψ ≥ 0` of compact support, invariant under small translations and under
`besselH ⊓ F.congruenceSubgroup`. -/
lemma IsFillingData.exists_step_sum_fiberPairing (hF : S.IsFillingData T F)
    (Z : F.IntermediateGroup) {J : Type} [Fintype J] (R : Matrix J J ℂ) (ω : J → ℕ → (LocProd T)ˣ) :
    ∃ Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0,
      HasCompactSupport Ψ ∧
      (∀ᶠ v : 𝔰.BesselIndex → LocProd T in 𝓝 0, ∀ x : 𝔰.BesselIndex → LocProd T, Ψ (x + v) = Ψ x) ∧
      (∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → LocProd T,
        Ψ (k.val.val *ᵥ x) = Ψ x) ∧
      ∀ e ∈ lastVectorQuadric (S.latticeMiddle (LocProd T)),
        Ψ e = ENNReal.ofReal (∑ p : J, ∑ q : J, R p q * F.fiberPairing Z (ω p) (ω q) e).re := by
  choose Ψpair pair_supp pair_unif pair_inv pair_eq using
    fun p q : J ↦ exists_step_function_eqOn_fiberPairing Z (ω p) (ω q)
  refine ⟨fun e ↦ (∑ p, ∑ q, R p q * Ψpair p q e).re.toNNReal, ?_, ?_, fun k hk x ↦ ?_,
    fun e he ↦ ?_⟩
  · refine .intro (isCompact_iUnion fun p ↦ isCompact_iUnion fun q ↦ pair_supp p q) fun e he ↦ ?_
    simp only [mem_iUnion, not_exists] at he
    simp [fun p q ↦ image_eq_zero_of_notMem_tsupport (he p q)]
  · filter_upwards [eventually_all.2 fun p ↦ eventually_all.2 fun q ↦ pair_unif p q] with v hv x
    simp only [hv]
  · simp only [pair_inv _ _ k hk]
  · simp only [pair_eq _ _ e he, ENNReal.ofReal]

/-- Let the inverse of the level `M = S.ideleM` be integral off `T`, and let `F` be a filling datum
at `T`. Let `Z` be a group between the congruence group `F.congruenceSubgroup` and the integral
isometries at `T`. The heads `a p` (`p : J`) are sequences in `Eˣ`, with Weyl elements
`w_p = weylElem 𝔰.ϱ (a p)` and entries below `ϱ` that are units off `T`; `F.headDensity` is a
product of powers of the moduli of these entries at `T`. Let `W = S.besselFn side` be the Bessel
function at the infinite places or its cut, as `side` says, and let `R` be the Gram matrix of the
tensors `ρ p • ∫ W(y) ⊗ W((w_p γ)⁻¹ y)^* dy` (`besselOrbitalIntegral`). Let `ρ p` times the head
density be the same number `w` for all `p`. Let the integral elements `n i` (`i : ι`) lie in `Z` at
`T` and have distinct reductions `s i`. Then the squared norms of
`∑ p, S.cosetAmplitude side c (s i) c' (w_p γ)`, times `w ^ 2`, the number of cosets of
`F.congruenceSubgroup` in `Z` and the squared volume of `F.congruenceSubgroup`, add up to at most
`F.headSumNormSq` at `g⁻¹`, where `g = S.toPlaces T (S.translateByClassReps c c' γ)` for
`γ ∈ floorGroup 𝔰.ϱ` whose translate is integral off `T`: the pairings of the orbital integrals
`F.scaledOrbitalIntegral` at `T` of two heads, summed against `R`. -/
lemma IsFillingData.sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq [WeilData E]
    (hF : S.IsFillingData T F) {side : FullOrCut} {Z : F.IntermediateGroup}
    {ι J : Type} [Fintype ι] [Fintype J] {c c' : S.Classes} {γ : S.G E} (hγ : γ ∈ floorGroup 𝔰.ϱ)
    {n : ι → S.latticeStabilizer} (h_inj : (fun i : ι ↦ S.reduction (n i)).Injective)
    (hn : ∀ i : ι, S.toPlaces T (n i) ∈ Z.val) {a : J → ℕ → Eˣ} {ρ : J → ℝ} {w : ℝ}
    (h_weight : ∀ p : J,
      ρ p * (F.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ a p) 1).toReal = w)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' γ))
    (h_head : ∀ p : J, ∀ l < 𝔰.ϱ,
      (a p l : E) ∈ ratIntegralOff T ∧ ((a p l)⁻¹ : Eˣ).val ∈ ratIntegralOff T) :
    let R : Matrix J J ℂ := .gram ℂ fun p : J ↦ ρ p • besselOrbitalIntegral volume
      (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
      (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ))
    F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets *
        ∑ i : ι, ENNReal.ofReal (w ^ 2 * ‖∑ p : J, S.cosetAmplitude side c (S.reduction (n i)) c'
          (weylElem 𝔰.ϱ (a p) * γ)‖ ^ 2) ≤
      ENNReal.ofReal (F.headSumNormSq Z R (fun p : J ↦ Units.map (ratToPlaces T) ∘ a p)
        (S.toPlaces T (S.translateByClassReps c c' γ))⁻¹).re := by
  classical
  -- The entry `(b, A i b)` of the sum over the heads, with `A i b` the coset of `(n i)⁻¹ * b`, is,
  -- up to a constant, the squared norm of the class sum at the reduction of `n i`; these entries
  -- are distinct.
  intro R
  have h_coset (i : ι) (b : Z.Cosets) : ∃ b' : Z.Cosets,
      (S.toPlaces T (n i))⁻¹ * b.out.val * b'.out.val⁻¹ ∈ F.congruenceSubgroup :=
    (Z.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq (mul_mem (inv_mem (hn i)) b.out.2)).imp
      fun b' hb' ↦ (hb' b').2 rfl
  choose A hA using h_coset
  let v (x : Z.Cosets × Z.Cosets) (p : J) : ℂ :=
    F.scaledOrbitalIntegral Z (Units.map (ratToPlaces T) ∘ a p)
    (S.toPlaces T (S.translateByClassReps c c' γ))⁻¹ x
  have h_nonneg (x : Z.Cosets × Z.Cosets) : 0 ≤ (star (v x) ⬝ᵥ R *ᵥ v x).re :=
    (Complex.nonneg_iff.1 (PosSemidef.dotProduct_mulVec_nonneg (posSemidef_gram ..) (v x))).1
  have h_entry (i : ι) (b : Z.Cosets) : .ofReal (star (v (b, A i b)) ⬝ᵥ R *ᵥ v (b, A i b)).re =
      F.groupMeasure F.congruenceSubgroup ^ 2 * .ofReal (w ^ 2 * ‖∑ p, S.cosetAmplitude side c
        (S.reduction (n i)) c' (weylElem 𝔰.ϱ (a p) * γ)‖ ^ 2) := by
    -- by unfolding, the tensor behind the entry is `w` times the mass of `K(M)` times the class sum
    have h_tensor : ∑ p, v (b, A i b) p • (ρ p • besselOrbitalIntegral volume
          (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
          (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ))) =
        w • F.groupMeasure.real F.congruenceSubgroup • ∑ p, S.cosetAmplitude side c
          (S.reduction (n i)) c' (weylElem 𝔰.ϱ (a p) * γ) := by
      simp only [v, smul_comm (M := ℂ) (N := ℝ),
        hF.scaledOrbitalIntegral_smul_eq_cosetAmplitude hγ (fun l ↦ (h_head _ l l.isLt).2)
          (isIntegralOff_weylElem_mul (h_head _) h_off) (hA i b),
        smul_smul (ρ _), h_weight, ← smul_sum]
    simp only [R, star_dotProduct_gram_mulVec, h_tensor]
    simp (disch := positivity) [norm_smul, ← Complex.ofReal_pow, mul_pow, Measure.real,
      ofReal_toReal (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)]
    ring
  have h_distinct : (fun θ : ι × Z.Cosets ↦ (θ.2, A θ.1 θ.2)).Injective := by
    rintro ⟨i, b⟩ ⟨k, _⟩ h_eq
    obtain ⟨rfl, hAb⟩ := Prod.mk.inj h_eq
    have h_red : S.reduction (n i) = S.reduction (n k) :=
      (hF.reduction_eq_iff ..).2 (by simpa [hAb] using div_mem (hA i b) (hA k b))
    rw [h_inj h_red]
  calc
    _ = ∑ θ : ι × Z.Cosets, .ofReal (star (v (θ.2, A θ.1 θ.2)) ⬝ᵥ R *ᵥ v (θ.2, A θ.1 θ.2)).re := by
      simp only [sum_prod_type, h_entry, sum_const, card_univ, nsmul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    _ ≤ ∑ x, .ofReal (star (v x) ⬝ᵥ R *ᵥ v x).re := by
      rw [← sum_image (f := fun x ↦ ENNReal.ofReal (star (v x) ⬝ᵥ R *ᵥ v x).re) h_distinct.injOn]
      exact sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := by
      rw [PlaceData.headSumNormSq_eq_sum, Complex.re_sum, ofReal_sum_of_nonneg fun x _ ↦ h_nonneg x]

/-- The terms over one point `e`. Let the inverse of the level `M = S.ideleM` be integral off `T`,
and let `F` be a filling datum at `T`. Let `Z` be a group between the congruence group
`F.congruenceSubgroup` and the integral isometries at `T`. The heads `a p` (`p : J`) are sequences
in `Eˣ`, with Weyl elements `w_p = weylElem 𝔰.ϱ (a p)` and entries below `ϱ` that are units off `T`;
`F.headDensity` is a product of powers of the moduli of these entries at `T`. Let
`W = S.besselFn side` be the Bessel function at the infinite places or its cut, as `side` says. Let
the triples `(c' i, S.reduction (n i), γ i)`, `i : ι`, be distinct, with `γ i` rational and fixing
the `ϱ` hyperbolic pairs (`floorGroup 𝔰.ϱ`) and `n i` in `Z` at `T`. Let the translates
`h_c⁻¹ γ h_c'` by the class representatives be integral off `T` and send the last frame vector `z`
to `e` at `T` (`orbitPoint 𝔰.top g = g⁻¹ z`). Let the left class `c i`, the product `⟨z, γ i z⟩` and
the `X₀`-part of `γ i z` be the same for all `i`. Let `ρ p` times the head density be `w`. Let `R`
be positive semidefinite and, for every `i`, the Gram matrix of the tensors
`ρ p • ∫ W(y) ⊗ W((w_p γ i)⁻¹ y)^* dy`. Then the squared norms of the sums over `p` of
`S.cosetAmplitude` at `w_p γ i`, times `w ^ 2`, the `F.measureH`-mass and the squared
`F.groupMeasure`-mass of `F.congruenceSubgroup` and the number of its cosets in `Z`, add up to at
most the real part of `∑ p q, R p q * F.fiberPairing Z (ω p) (ω q) e`. Here `ω p` is `a p` read at
`T`, the fiber pairing is the pairing of the orbital integrals of two heads integrated over
`besselH`, and `S.cosetAmplitude side c s c' γ` is the sum of the amplitudes of the rational
`u γ u'⁻¹`, with `u`, `u'` unipotent, whose translate by the class representatives is integral with
reduction `s`. -/
lemma IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le_fiberPairing [WeilData E]
    (hF : S.IsFillingData T F) {side : FullOrCut}
    {Z : F.IntermediateGroup} {ι J : Type} [Fintype ι] [Fintype J] {c c' : ι → S.Classes}
    {γ : ι → S.G E} {n : ι → S.latticeStabilizer}
    (h_inj : (fun i : ι ↦ (c' i, S.reduction (n i), γ i)).Injective)
    (h_leftClass : ∀ i k : ι, c i = c k)
    (hγ : ∀ i : ι, γ i ∈ floorGroup 𝔰.ϱ)
    (h_tail : ∀ i k : ι, S.frameProducts (γ i) 𝔰.top 𝔰.top = S.frameProducts (γ k) 𝔰.top 𝔰.top)
    (h_col : ∀ (i k : ι) (l : 𝔰.κ),
      (γ i).val.val (𝔰.indexX₀ l) 𝔰.z = (γ k).val.val (𝔰.indexX₀ l) 𝔰.z)
    (hn : ∀ i : ι, S.toPlaces T (n i) ∈ Z.val)
    (h_off : ∀ i : ι, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (γ i)))
    {e : 𝔰.BesselIndex → LocProd T}
    (he : ∀ i : ι, orbitPoint 𝔰.top (S.toPlaces T (S.translateByClassReps (c i) (c' i) (γ i)))⁻¹ =
      e)
    {a : J → ℕ → Eˣ} {R : Matrix J J ℂ} (R_psd : R.PosSemidef) {ρ : J → ℝ} {w : ℝ}
    (hR : ∀ i : ι, R = .gram ℂ fun p : J ↦ ρ p • besselOrbitalIntegral volume
      (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
      (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ i)))
    (h_weight : ∀ p : J, ρ p * (F.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ a p) 1).toReal = w)
    (h_head : ∀ p : J, ∀ l < 𝔰.ϱ,
      (a p l : E) ∈ ratIntegralOff T ∧ ((a p l)⁻¹ : Eˣ).val ∈ ratIntegralOff T) :
    let ω (p : J) : ℕ → (LocProd T)ˣ := Units.map (ratToPlaces T) ∘ a p
    F.measureH F.congruenceSubgroup * (F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets) *
        ∑ i : ι, .ofReal (w ^ 2 * ‖∑ p : J, S.cosetAmplitude side (c i) (S.reduction (n i)) (c' i)
          (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2) ≤
      .ofReal (∑ p : J, ∑ q : J, R p q * F.fiberPairing Z (ω p) (ω q) e).re := by
  classical
  -- Group the classes by the pair of the right class and the rational element, and bound each
  -- group by `sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq`. Different pairs have positions in
  -- different cosets of `F.congruenceSubgroup`.
  intro ω
  obtain _ | ⟨⟨i₀⟩⟩ := isEmpty_or_nonempty ι
  · simp [Finset.univ_eq_empty (α := ι)]
  obtain ⟨c₀, rfl⟩ : ∃ c₀, c = fun _ ↦ c₀ := ⟨c i₀, funext (h_leftClass · i₀)⟩
  let pair (i : ι) : S.Classes × S.G E := (c' i, γ i)
  let pos (x : Set.range pair) : (S.latticeMiddle (LocProd T)).G :=
    (S.toPlaces T (S.translateByClassReps c₀ x.val.1 x.val.2))⁻¹
  have h_point (x : Set.range pair) :
      pos x ∈ floorGroup 𝔰.ϱ ∧ orbitPoint 𝔰.top (pos x) = e := by
    obtain ⟨_, i, rfl⟩ := x
    exact ⟨inv_mem (.map_mem_agreeWithOneOn _
      (translateByClassReps_mem_floorGroup (hγ i) c₀ (c' i))),
      he i⟩
  have h_sep (x x' : Set.range pair) (hK : pos x * (pos x')⁻¹ ∈ F.congruenceSubgroup) : x = x' := by
    obtain ⟨_, i, rfl⟩ := x
    obtain ⟨_, k, rfl⟩ := x'
    exact Subtype.ext (Prod.ext_iff.2 (hF.classes_eq_and_eq_of_inv_mul_mem_congruenceSubgroup rfl
      (hγ i) (hγ k)
      (h_tail i k) (h_col i k) (h_off i) (h_off k) (by simpa [pos, pair] using hK)))
  refine .trans ?_ (sum_headSumNormSq_le_fiberPairing Z R_psd ω h_point h_sep)
  rw [mul_assoc, ← Finset.sum_fiberwise univ (Set.rangeFactorization pair), mul_sum]
  gcongr with x
  obtain ⟨_, k, rfl⟩ := x
  have h_same (i : {i // pair i = pair k}) : c' i = c' k ∧ γ i = γ k := Prod.mk.inj i.property
  have h_inj_fiber : (fun i : {i // pair i = pair k} ↦ S.reduction (n i)).Injective :=
    fun i i' h ↦ Subtype.ext (h_inj (by simp [h_same i, h_same i', h]))
  rw [hR k]
  refine .trans (le_of_eq ?_) (hF.sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq (hγ k)
    h_inj_fiber (fun i ↦ hn i) h_weight (h_off k) h_head)
  rw [sum_subtype (F := inferInstance) (p := (pair · = pair k)) _ (by simp [Subtype.ext_iff])]
  simp only [h_same, pair]

omit [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)]
  [IntegralPlace (LocProd T)] in
/-- The space has the hyperbolic pairs `e_a, e*_a` (`a < ϱ`), a definite part `X₀` with basis `𝔰.κ`
and a vector `z`; `floorGroup 𝔰.ϱ` is the group of isometries that fix the hyperbolic pairs. Let `γ`
be an element of this group over `E` with `⟨z, γ z⟩ = t`, and `x` the `X₀`-part of `γ z`, moved by
the inverse of the representative of the class `c`. Then at `T` the translate `h_c⁻¹ γ h_c'` sends
`z` to `vectorOfLastEntry S.piN t x = x - N⁻¹ t z`, written in the lattice basis. -/
lemma orbitPoint_toPlaces_translateByClassReps {c c' : S.Classes} {γ : S.G E}
    (hγ : γ ∈ floorGroup 𝔰.ϱ) {t : E} (h_tail : S.frameProducts γ 𝔰.top 𝔰.top = t) :
    orbitPoint 𝔰.top (S.toPlaces T (S.translateByClassReps c c' γ))⁻¹ =
      evalPlaces T ∘ vectorOfLastEntry S.piN (algebraMap E (𝔸f E) t)
        (c.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ fun l : 𝔰.κ ↦ γ.val.val (𝔰.indexX₀ l) 𝔰.z) := by
  rw [← h_tail, ← orbitPoint_top_translateByClassReps_inv hγ c c']
  have h_map : (S.toPlaces T (S.translateByClassReps c c' γ)).val.val =
      (S.translateByClassReps c c' γ).val.val.map (evalPlaces T) := rfl
  ext l
  simp [orbitPoint, h_map]

end Level

variable [WeilData E]

/-- Siegel's formula as an upper bound. Let `S` be admissible, with the inverse of the level
`M = S.ideleM` integral off `T`, let `N⁻¹` be integral off `T`, where `N = S.N`, and let `F` be a
filling datum at `T`: a large lattice datum of modulus `M` for the place structure `P`, whose
character is that of `S`. Let `Ψ ≥ 0` be a function of compact support on the vectors over the
product `LocProd T` of the completions at `T`, invariant under small translations and under the
elements of `F.congruenceSubgroup` that fix all basis vectors outside the definite part `X₀`
(`besselH`). Let `|t|_v > N` under all embeddings `Φ v` of the CM type. For a pair `z = (class, v)`
let `x` be the rational vector `v` of `X₀` moved by the inverse of the representative of the class.
If the pairs in a finite set `s` have `N (v* v) = t t̄ - N²` and `x` integral off `T`, then the
values of `Ψ` at `vectorOfLastEntry S.piN t x` (`x` minus `N⁻¹ t` times the last frame vector) add
up to at most the product of `1 + S.b⁻⁶`, the number of classes, `S.siegelConst = (π^k / ((k - 1)!
N^k))^f |disc E|^(1/4) (volÔ E)^k`, `(∏ v, (|t|_v² - N²)) ^ (k - 1)`, the inverse modulus of
`S.piNAt T` (a unit of norm `N`) and the integral of `Ψ ∘ vectorOfLastEntry` over the sphere
`y* y = (t t̄ - N²) / N`, for the fiber measure `P.normFiberMeasure` with index
`lastEntrySphereIndex`. Here `S.b` is the size parameter of `S`, `k` the rank of `X₀` and `f` the
number of infinite places. -/
theorem IsFillingData.siegel_sum_le_lintegral_sphere (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) {Ψ : (𝔰.BesselIndex → LocProd T) → ℝ≥0}
    (Ψ_supp : HasCompactSupport Ψ)
    (Ψ_unif : ∀ᶠ v : 𝔰.BesselIndex → LocProd T in 𝓝 0,
      ∀ x : 𝔰.BesselIndex → LocProd T, Ψ (x + v) = Ψ x)
    (Ψ_inv : ∀ k ∈ besselH ⊓ F.congruenceSubgroup, ∀ x : 𝔰.BesselIndex → LocProd T,
      Ψ (k.val.val *ᵥ x) = Ψ x)
    {s : Finset (S.Classes × (𝔰.κ → E))} {t : E}
    (ht : ∀ v : InfinitePlace E, S.N ^ 2 < ‖Φ v t‖ ^ 2)
    (h_norm : ∀ z ∈ s, S.N * star z.2 ⬝ᵥ z.2 = t * star t - S.N ^ 2)
    (h_int : ∀ z ∈ s, ∀ i : 𝔰.κ,
      (z.1.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ z.2) i ∈ integralOff T) :
    (∑ z ∈ s, Ψ (evalPlaces T ∘
        vectorOfLastEntry S.piN t (z.1.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ z.2)) : ℝ≥0∞) ≤
      .ofReal ((1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst *
          (∏ v : InfinitePlace E, (‖Φ v t‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) *
        ((P.modulus (S.piNAt T))⁻¹ *
          ∫⁻ y : 𝔰.κ → LocProd T, Ψ (vectorOfLastEntry (S.piNAt T) (ratToPlaces T t) y)
          ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex (S.piNAt T) (ratToPlaces T t))) := by
  -- Apply `classSum_eq_mul_normDensity` at the norm `β = (t t̄ - N²) / N` to the test function `f`
  -- that is `Ψ` at `T` and the indicator of the integral vectors off `T`; bound the density by
  -- `enorm_normDensity_le_mul_lintegral_normFiberMeasure`.
  classical
  have hN₀ : 0 < S.N := S.N_prime.pos
  have h_rank : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
  set β : E := (t * star t - S.N ^ 2) / S.N
  set π : (LocProd T)ˣ := S.piNAt T
  let t' : LocProd T := evalPlaces T t
  have hβ : star β = β := by simp [β, field]
  have hβ_pos (v : InfinitePlace E) : 0 < (Φ v β).re := by simpa [β, mul_conj', sq, hN₀] using ht v
  have h_level : P.skewUnit⁻¹.val * lastEntrySphereIndex π t' = evalPlaces T β :=
    skewUnit_inv_mul_lastEntrySphereIndex_piNAt t
  have Ψ_lc : IsLocallyConstant Ψ := isLocallyConstant_of_eventually_add Ψ_unif
  -- the integral vectors off `T` form a clopen set
  let L : OpenAddSubgroup (𝔰.κ → 𝔸f E) :=
    ⟨(intVectors (integralOff T) 𝔰.κ).toAddSubgroup, isOpen_intVectors (isOpen_integralOff T)⟩
  let f : LocallyConstant (𝔰.κ → 𝔸f E) ℝ≥0 :=
    .indicator ⟨fun y ↦ Ψ (vectorOfLastEntry π t' (evalPlaces T ∘ y)),
      Ψ_lc.comp_continuous (by fun_prop)⟩
      (isClopen L)
  let C : ℂ := (classSum stdRatPoints S.sourceLevel 1 * √√|NumberField.discr E| *
    ∏ v : InfinitePlace E, Real.pi ^ card 𝔰.κ / (card 𝔰.κ - 1).factorial *
      (Φ v β).re ^ (card 𝔰.κ - 1) : ℝ)
  obtain ⟨h_summable, (h_siegel : ((classSum stdRatPoints S.sourceLevel fun h : Gf E 𝔰.κ ↦
      ((∑' v : 𝔰.κ → E, if star v ⬝ᵥ v = β then f (h⁻¹.val.val *ᵥ fun i ↦ (v i : 𝔸f E)) else 0 :
        ℝ≥0) : ℝ) : ℝ) : ℂ) = C * normDensity f β)⟩ :=
    classSum_eq_mul_normDensity (by lia) S.sourceLevel f
      (fun k hk ↦ hF.testFunction_mulVec Ψ_inv t hk)
      (hasCompactSupport_testFunction Ψ_supp π t') hβ hβ_pos
  set I : ℝ≥0∞ := ∫⁻ y, (Ψ (vectorOfLastEntry π (ratToPlaces T t) y) : ℝ≥0∞)
    ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π (ratToPlaces T t))
  calc
    _ ≤ ‖C * normDensity f β‖ₑ := by
      -- each pair `z ∈ s` has norm `β` and is integral off `T`, so it is a term of the class sum
      rw [← h_siegel]
      simp_rw [classSum_sourceLevel_eq_sum, ← NNReal.coe_sum, eNorm_eq_nnNorm, nnNorm_real,
        nnNorm_eq, ofNNReal_finsetSum, ENNReal.coe_tsum (h_summable _)]
      grw [← tsum_prod.trans (tsum_fintype _), ← sum_le_tsum s]
      gcongr with z hz
      have h_norm_eq : star z.2 ⬝ᵥ z.2 = β := by simp [β, ← h_norm z hz, Nat.Prime.ne_zero]
      grw [ite_eq_left h_norm_eq, ← vectorOfLastEntry_evalPlaces]
      exact (ite_eq_left (h_int z hz)).ge
    _ ≤ ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k * I) := by
      rw [eNorm_mul]
      gcongr
      exact hF.enorm_normDensity_le_mul_lintegral_normFiberMeasure
        (Ψ_lc.continuous.comp isClosedEmbedding_vectorOfLastEntry.continuous)
        (Ψ_supp.comp_isClosedEmbedding isClosedEmbedding_vectorOfLastEntry)
        (by rw [star_algebraMap_finAdele, hβ]) h_level
    _ = ‖C‖ₑ * (.ofReal (1 + S.b⁻¹ ^ 6) * volÔ E ^ 𝔰.k) * P.modulus π * ((P.modulus π)⁻¹ * I) := by
      rw [mul_assoc _ (P.modulus π), ENNReal.mul_inv_cancel_left (by simp) (by simp), ← mul_assoc]
    _ = _ := by rw [siegel_constant_eq hT_N piNAt_mul_star hβ_pos (C := C) rfl]

omit [WeilData E] [T.StarStable] [S.IsAdmissible] [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] in
/-- If the lattice basis and the translate `h_c⁻¹ γ h_c'` (`S.translateByClassReps`) of a rational
element `γ` of `floorGroup 𝔰.ϱ` are integral off `T`, then so is the `X₀`-part of the column of `γ`
at `z`, moved by the inverse of the representative of `c`. -/
lemma x₀Part_mem_integralOff (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    {c c' : S.Classes} {γ : S.G E} (hγ : γ ∈ floorGroup 𝔰.ϱ)
    (h_off : S.IsIntegralOff T (S.translateByClassReps c c' γ)) (i : 𝔰.κ) :
    (c.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ fun l : 𝔰.κ ↦ γ.val.val (𝔰.indexX₀ l) 𝔰.z) i ∈
      integralOff T := by
  have column : orbitPoint 𝔰.top (S.translateByClassReps c c' γ)⁻¹ ∈
      intVectors (integralOff T) 𝔰.BesselIndex :=
    fun l ↦ by simpa [orbitPoint] using h_off.isIntMatrix l 𝔰.z
  rw [orbitPoint_top_translateByClassReps_inv hγ] at column
  exact (mulVec_mem_intVectors_iff (inv_mem hT_basis)).1 column (𝔰.indexX₀ i)

/-- Siegel's step, for one last entry `t`. Let `S` be admissible, with the inverse of the level
`M = S.ideleM` integral off `T`, let `N⁻¹` and the lattice basis be integral off `T`, and let `F` be
a filling datum at `T`. Let `Z` be a group between the congruence group `F.congruenceSubgroup` and
the integral isometries at `T`. The heads `a p` (`p : J`) are sequences in `Eˣ`, with Weyl elements
`w_p = weylElem 𝔰.ϱ (a p)` and entries below `ϱ` that are units off `T`; `F.headDensity` is a
product of powers of the moduli of these entries at `T`. Let `W = S.besselFn side` be the Bessel
function at the infinite places or its cut, as `side` says. Let the terms
`(c i, c' i, S.reduction (n i), γ i)`, `i : j`, be distinct, with `γ i` rational, fixing the `ϱ`
hyperbolic pairs (`floorGroup 𝔰.ϱ`) and with `⟨z, γ i z⟩ = t`, translates by the class
representatives integral off `T` and `n i` in `Z` at `T`; there is at least one term, `i₀`. Let
`N < ‖t‖` at all infinite places, and let the heads have entry `t` at `ϱ`. Assume that `R` is, for
every `i`, the Gram matrix of the tensors `ρ p • ∫ W(y) ⊗ W((w_p γ i)⁻¹ y)^* dy`
(`besselOrbitalIntegral`), and that `ρ p` times the head density is `r * √G`, where
`G = (∏ v, (‖t‖_v² - N²)) ^ (k - 1)`. Then the squared norms of the sums over `p` of
`S.cosetAmplitude` at `w_p γ i`, times `r ^ 2`, add up to at most
`(1 + S.b⁻⁶) * S.scaledSiegelConst` times the real part of
`∑ p q, R p q * F.lastEntryDensity / Z.massRatio`. -/
theorem IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity
    (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) {side : FullOrCut} {Z : F.IntermediateGroup}
    {j J : Type} [Fintype j] [Fintype J] {c c' : j → S.Classes} {γ : j → S.G E}
    {n : j → S.latticeStabilizer} {t : Eˣ}
    (h_inj : (fun i : j ↦ (c i, c' i, S.reduction (n i), γ i)).Injective)
    (hγ : ∀ i : j, γ i ∈ floorGroup 𝔰.ϱ) (h_tail : ∀ i : j, S.frameProducts (γ i) 𝔰.top 𝔰.top = t)
    (ht : ∀ v : InfinitePlace E, S.N ^ 2 < ‖Φ v (t : E)‖ ^ 2)
    (hn : ∀ i : j, S.toPlaces T (n i) ∈ Z.val)
    (h_off : ∀ i : j, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (γ i))) (i₀ : j)
    {a : J → ℕ → Eˣ} (h_last : ∀ p : J, a p 𝔰.ϱ = t)
    (h_head : ∀ p : J, ∀ l < 𝔰.ϱ,
      (a p l : E) ∈ ratIntegralOff T ∧ ((a p l)⁻¹ : Eˣ).val ∈ ratIntegralOff T)
    {R : Matrix J J ℂ} {ρ : J → ℝ} {r : ℝ}
    (hR : ∀ i : j, R = .gram ℂ fun p : J ↦ ρ p • besselOrbitalIntegral volume
      (fun g : InfinitePlace E → 𝔰.G₁ ↦ .toLp 2 (S.besselFn side g))
      (S.ratToInf (weylElem 𝔰.ϱ (a p) * γ i)))
    (h_weight : ∀ p : J, ρ p * (F.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ a p) 1).toReal =
      r * √((∏ v : InfinitePlace E, (‖Φ v (t : E)‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1))) :
    ∑ i : j, r ^ 2 * ‖∑ p : J, S.cosetAmplitude side (c i) (S.reduction (n i)) (c' i)
        (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2 ≤
      (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst * (∑ p : J, ∑ q : J, R p q *
        (F.lastEntryDensity (S.piNAt T) Z (Units.map (ratToPlaces T) ∘ a p)
          (Units.map (ratToPlaces T) ∘ a q) / Z.massRatio.toReal)).re := by
  classical
  -- Group the classes by the point `g i` of Siegel's sum (the class and the `X₀`-part of `γ i z`).
  -- Over one point they are bounded by the value of a step function `Ψ`; Siegel's formula sums
  -- over the points, and the integral of `Ψ` over the sphere of `t`, divided by the modulus of
  -- `S.piNAt T`, is the real part of the sum `Q` of densities.
  let ω (p : J) : ℕ → (LocProd T)ˣ := Units.map (ratToPlaces T) ∘ a p
  let y (i : j) : ℝ := r ^ 2 * ‖∑ p : J, S.cosetAmplitude side (c i) (S.reduction (n i)) (c' i)
    (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2
  set G : ℝ := (∏ v : InfinitePlace E, (‖Φ v t.val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)
  let g (i : j) : S.Classes × (𝔰.κ → E) := (c i, fun l ↦ (γ i).val.val (𝔰.indexX₀ l) 𝔰.z)
  let x (z : S.Classes × (𝔰.κ → E)) : 𝔰.κ → 𝔸f E := z.1.out⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ z.2
  let Q : ℂ := ∑ p, ∑ q, R p q * F.lastEntryDensity (S.piNAt T) Z (ω p) (ω q)
  have R_psd : R.PosSemidef := by simpa only [hR i₀] using posSemidef_gram ℂ _
  have G_pos : 0 < G := by simp [G, ht, prod_pos]
  -- The translate of a term by the class representatives moves `z` to the vector with last entry
  -- `t` over `g i`, which has norm `(t t̄ - N²) / N` and is integral off `T`.
  have norm_eq (i : j) : S.N * star (g i).2 ⬝ᵥ (g i).2 = t.val * star t.val - S.N ^ 2 := by
    rw [← h_tail i]
    exact mul_star_dotProduct_eq_last_frameProducts (hγ i)
  have x_int (i : j) : ∀ l : 𝔰.κ, x (g i) l ∈ integralOff T :=
    x₀Part_mem_integralOff hT_basis (hγ i) (h_off i)
  have point_eq (i : j) : orbitPoint 𝔰.top
    (S.toPlaces T (S.translateByClassReps (c i) (c' i) (γ i)))⁻¹ =
      evalPlaces T ∘ vectorOfLastEntry S.piN t.val (x (g i)) :=
    orbitPoint_toPlaces_translateByClassReps (hγ i) (h_tail i)
  -- Extend the real part of the sum of the fiber pairings against `R` to a step function `Ψ`; its
  -- value at a point bounds the classes there.
  obtain ⟨Ψ, Ψ_supp, Ψ_unif, Ψ_inv, Ψ_eq : ∀ e ∈ lastVectorQuadric (S.latticeMiddle (LocProd T)),
      Ψ e = ENNReal.ofReal (∑ p, ∑ q, R p q * F.fiberPairing Z (ω p) (ω q) e).re⟩ :=
    hF.exists_step_sum_fiberPairing Z R ω
  obtain ⟨D, hD : 0 < D, h_const : S.scaledSiegelConst = D * card S.Classes * S.siegelConst,
      h_unit : Z.massRatio ≤ F.measureH F.congruenceSubgroup *
        (F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets) * .ofReal D⟩ :=
    hF.exists_scaledSiegelConst_eq_and_massRatio_le Z
  have le_Ψ (k₀ : j) :
      .ofReal G * (Z.massRatio / .ofReal D) * ∑ k with g k = g k₀, .ofReal (y k) ≤
        (Ψ (evalPlaces T ∘ vectorOfLastEntry S.piN t.val (x (g k₀))) : ℝ≥0∞) := by
    have same (k k' : {k // g k = g k₀}) :
        c k = c k' ∧ (g k).2 = (g k').2 := Prod.mk.inj (k.property.trans k'.property.symm)
    have point_mem : evalPlaces T ∘ vectorOfLastEntry S.piN t.val (x (g k₀)) ∈
        lastVectorQuadric (S.latticeMiddle (LocProd T)) := by
      rw [← point_eq]
      exact orbitPoint_mem_lastVectorQuadric (inv_mem (.map_mem_agreeWithOneOn _
        (translateByClassReps_mem_floorGroup (hγ k₀) (c k₀) (c' k₀))))
    have h_scale (k : j) : ENNReal.ofReal G * .ofReal (y k) =
        .ofReal ((r * √G) ^ 2 * ‖∑ p, S.cosetAmplitude side (c k) (S.reduction (n k)) (c' k)
          (weylElem 𝔰.ϱ (a p) * γ k)‖ ^ 2) := by
      rw [← ENNReal.ofReal_mul G_pos.le, mul_pow, Real.sq_sqrt G_pos.le, mul_left_comm, mul_assoc]
    suffices h_over : F.measureH F.congruenceSubgroup *
      (F.groupMeasure F.congruenceSubgroup ^ 2 * card Z.Cosets) *
        ∑ k : {k // g k = g k₀}, ENNReal.ofReal G * .ofReal (y k) ≤
          Ψ (evalPlaces T ∘ vectorOfLastEntry S.piN t.val (x (g k₀))) by
      grw [div_le_of_le_mul h_unit, mul_comm (ENNReal.ofReal G), mul_assoc _ (ENNReal.ofReal G),
        mul_sum, sum_subtype (F := inferInstance) (p := fun k ↦ g k = g k₀) _ mem_filter_univ,
        h_over]
    simp only [h_scale, Ψ_eq _ point_mem]
    exact hF.mul_sum_norm_sum_cosetAmplitude_sq_le_fiberPairing (ι := {k // g k = g k₀})
      (fun k k' h ↦ Subtype.ext (h_inj (Prod.ext (same k k').1 h))) (fun k k' ↦ (same k k').1)
      (fun k ↦ hγ k) (fun k k' ↦ by simp only [h_tail])
      (fun k k' ↦ congrFun (same k k').2) (fun k ↦ hn k) (fun k ↦ h_off k)
      (fun k ↦ by rw [point_eq, k.property]) R_psd (fun k ↦ hR k) h_weight h_head
  -- Siegel's formula sums over the points; the normalized integral over the sphere is `Q.re`.
  obtain ⟨⟨re_nonneg : 0 ≤ Q.re, -⟩, h_sphere⟩ :=
    sum_lastEntryDensity_nonneg_and_eq_inv_mul_lintegral Z piNAt_mul_star
    R_psd ω (t := t.map (ratToPlaces T)) fun p ↦ by simp [ω, h_last]
  have h_total : .ofReal G * (Z.massRatio / .ofReal D) * ∑ k, .ofReal (y k) ≤
      .ofReal ((1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst * G) * ENNReal.ofReal Q.re := by
    calc
      _ ≤ ∑ z ∈ univ.image g, (Ψ (evalPlaces T ∘ vectorOfLastEntry S.piN t.val (x z)) : ℝ≥0∞) := by
        rw [← sum_fiberwise_of_maps_to fun k _ ↦ mem_image_of_mem g (mem_univ k), mul_sum]
        exact sum_le_sum (forall_mem_image.2 fun k _ ↦ le_Ψ k)
      _ ≤ _ := hF.siegel_sum_le_lintegral_sphere hT_N Ψ_supp Ψ_unif Ψ_inv ht
        (forall_mem_image.2 fun k _ ↦ norm_eq k)
        (forall_mem_image.2 fun k _ ↦ x_int k)
      _ = _ := by
        -- almost every point of the sphere lies on the top quadric, where `Ψ_eq` gives `Ψ`
        rw [h_sphere, lintegral_congr_ae
          ((P.ae_vectorOfLastEntry_mem_lastVectorQuadric piNAt_mul_star F.two_le_card _).mono
            fun _ ↦ Ψ_eq _)]
        rfl
  -- pass to real numbers and cancel the constants
  have unit_pos : 0 < Z.massRatio.toReal := (massRatio_ne_zero_and_ne_top Z).elim toReal_pos
  have h_real : G * (Z.massRatio.toReal / D) * ∑ i, y i ≤
      (1 + S.b⁻¹ ^ 6) * card S.Classes * S.siegelConst * G * Q.re := by
    simpa (disch := finiteness) only [toReal_sum, toReal_mul, toReal_ofReal, toReal_div,
      siegelConst] using toReal_mono (by finiteness) h_total
  have h_re : (∑ p, ∑ q, R p q *
      (F.lastEntryDensity (S.piNAt T) Z (ω p) (ω q) / Z.massRatio.toReal)).re =
        Q.re / Z.massRatio.toReal := by
    simp [Q, ← mul_div_assoc, ← Finset.sum_div]
  refine le_of_mul_le_mul_left (h_real.trans_eq ?_) (by positivity)
  rw [h_re, h_const]
  field

end New.Filling
end
end

section
/-!
# The sieve system at the finite places

The finite half of the input of the sieve `New.Filling.sieve`.

* `New.Filling.IsFillingData.exists_intermediateGroup_sieveSystem`: read the completions at a finite
  set `T` of places as one ring `LocProd T`. There is a subgroup `Z` of the unitary group over it
  that contains the components at `T` of the integral elements fixing given vectors at a set `Sg` of
  chosen places, and for which the forms `New.Floors.PlaceData.floorForm` and the density
  `New.Floors.PlaceData.lastEntryDensity`, divided by `Z.massRatio`, satisfy `New.SieveSystem`.

The subgroup is that of `New.Filling.IsFillingData.exists_intermediateGroup_norm_floorForm_div_le`,
which bounds the form of floor `0`: it saves the power `b ^ (6 * 𝔰.k)` of the base `b` of the
filling for each place in a given set `Sg` of chosen places.

Notions from other files:
* `New.Filling.IsAdmissible`: the standing hypotheses on the level and the sizes of a filling `S`.
* `New.Filling.IsFillingData`: `F` is a large lattice datum over `LocProd T`, its modulus
  `g = F.levelUnit` is the component at `T` of `S.ideleM` (the product `S.M` of the two level primes
  as a finite idele), and the character is that of `S` at `T`.
* `New.Floors.PlaceData.massIntegral`: `ϰ(Z) = ∫ |∫_Z phase(y x y⁻¹) dy| ^ 2 dx`.
* `New.Floors.PlaceData.IntermediateGroup.massRatio`: `vol(Z) vol(K(g)) / unipotentMass ^ 2`, where
  `vol` is `New.Floors.PlaceData.groupMeasure` and `Z` lies between `K(g)` and the integral points.
* `New.SieveSystem`: the recursion, positivity, continuity and bounds that the sieve asks of a
  family of forms at a place.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

namespace New.Filling

open Finset ComplexOrder MeasureTheory Floors ENNReal PlaceData IntegralPlace.IsLargeLatticeData

/-- Let `S` be admissible filling data over the CM field `E`. Let `b = S.b` be the real number in
whose powers sizes are measured, `M = S.M` the product of the two level primes, `f = numInfPlaces E`
the number of infinite places, and `n = 𝔰.n = ϱ + 1` with `ϱ` the number of hyperbolic planes. Then
`(2 (M ^ f) ^ 2) ^ (n ^ 6) ≤ b ^ (n ^ 9 * f)`. -/
lemma two_mul_M_pow_sq_pow_le {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    (S : Filling E 𝔰) :
    (2 * ((S.M : ℝ) ^ numInfPlaces E) ^ 2) ^ 𝔰.n ^ 6 ≤ S.b ^ (𝔰.n ^ 9 * numInfPlaces E) := by
  have one_le_b : 1 ≤ S.b := S.one_le_b
  have exponent_le : 46 * numInfPlaces E + 1 ≤ 𝔰.n ^ 3 * numInfPlaces E := by
    grw [Shape.n, ← S.ten_pow_five_le_varrho]
    grind [S.k_le_f, S.pow_chain]
  calc
    _ ≤ (S.b * ((S.b ^ 23) ^ numInfPlaces E) ^ 2) ^ 𝔰.n ^ 6 := by
      grw [S.M_le_b_pow, show 2 ≤ S.b by linarith [S.thousand_le_b]]
    _ = S.b ^ ((46 * numInfPlaces E + 1) * 𝔰.n ^ 6) := by ring
    _ ≤ S.b ^ (𝔰.n ^ 3 * numInfPlaces E * 𝔰.n ^ 6) := by gcongr
    _ = S.b ^ (𝔰.n ^ 9 * numInfPlaces E) := by ring

/-- Let `S` be admissible filling data, `T` a conjugation-stable finite set of finite places, and
`F` a filling datum at `T`: measures and a modulus `g` for the unitary group `G` of the hermitian
form of `S` over the product `LocProd T` of the completions. Let `K` be the group of integral points
of `G`, `K(g) = F.congruenceSubgroup` its principal congruence subgroup and `vol = F.groupMeasure`
the Haar measure. Then `F.massIntegral K = ∫_G |∫_K χ(y x y⁻¹) dy| ^ 2 dx`, with
`χ = phase F.levelUnit` the generic character of the unipotent group `U` extended to `U K(g)` and by
zero, is at most `vol(K) vol(K(g)) (1 + b⁻¹ ^ 6)`, where `b = S.b` is the size parameter of `S`. -/
lemma IsFillingData.massIntegral_full_le {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) :
    let K := unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram
    F.massIntegral K ≤
      F.groupMeasure K * F.groupMeasure F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) := by
  intro K
  obtain ⟨-, h_box : F.boxSet = K, -⟩ := hF.volume_le_and_boxSet_closePairs_positions_eq
  -- `massIntegral_le_main_add_error` for `Z = K` and `Q = 2`
  have h_main_term : F.massIntegral K ≤
      F.groupMeasure K * F.groupMeasure F.congruenceSubgroup * (F.groupMeasure K + 2⁻¹ ^ 𝔰.n) :=
    massIntegral_le_main_add_error ⟨K, P.unitaryLevel_le_unitaryLevel_one, le_rfl⟩ le_rfl
      modulus_le_half (by grind [S.pow_chain, Nat.le_self_pow (n := 4) (by norm_num) 𝔰.n])
  grw [h_main_term, ← half_pow_le_inv_pow_six]
  gcongr
  calc F.groupMeasure K + 2⁻¹ ^ 𝔰.n
      ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n) + 2⁻¹ ^ 𝔰.n := by grw [← h_box, hF.groupMeasure_boxSet_le]
    _ = .ofReal (1 + 2⁻¹ ^ 𝔰.ϱ) := by
      simp [ofReal_add, pow_succ, add_assoc, ← mul_add, inv_two_add_inv_two, -inv_pow]

/-- Let `Z` be a group between the congruence subgroup of the place datum `F` and the integral
points, and let `c = Z.massRatio` be its normalising constant in `ℝ≥0∞`. A bound `‖x‖ₑ ≤ c * D` with
`D` finite gives `‖x / c.toReal‖ ≤ D.toReal`. -/
lemma norm_div_massRatio_le {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable] {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (Z : F.IntermediateGroup) {x : ℂ} {D : ℝ≥0∞} (hD : D ≠ ∞)
    (h_le : ‖x‖ₑ ≤ Z.massRatio * D) : ‖x / Z.massRatio.toReal‖ ≤ D.toReal := by
  simpa using toReal_mono hD (div_le_of_le_mul' h_le : ‖x‖ₑ / Z.massRatio ≤ D)

/-- Let `F` be a filling datum with modulus `g = F.levelUnit` on the unitary group over `LocProd T`,
the product of the completions at `T`, with integers `O`; let both level primes be units off `T`.
Let `Z` lie between `K(g)` and the integral points, `j ≤ ϱ`, let `p`, `q` be sequences of units and
`ξ` a unit. Let the weight `ω` be either `x ↦ P.ψ (ξ * G x j j)`, with `P.ψ` the additive character
of the place and `G x` the matrix of products of the frame with its image under `x`, or the constant
`1` with `j = i + 1` and `ξ = g⁻¹ * ((p i)⁻¹ - (q i)⁻¹)`. Take the orbital integral
`F.floorForm j p q` of floor `j` of `Z.besselVector` and divide it by `Z.massRatio = vol(Z)
vol(K(g)) / F.unipotentMass ^ 2`. The norm is at most `S.frequencyDecay T ξ = [O : ξ O] ^ ((k -
n⁷) / 2) / [O : O ∩ ξ⁻¹ O] ^ 3 * b ^ (n⁹ f)` times the weights `finHeadWeight (n ^ 6) j` of `p` and
`q`; that of `p` is the product over `l < j` of `[O : D O] ^ (n⁶ / 2)` for `D = p 0 * ⋯ * p l`, and
`0` if some `D` is not integral. Here `n = 𝔰.n = ϱ + 1`, `k = 𝔰.k`, `b = S.b`, `f` is the number of
infinite places, and `[O : ξ O]` is the generalised index `genIndex ξ`. -/
lemma IsFillingData.norm_floorForm_div_massRatio_le {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] (Z : F.IntermediateGroup)
    {j : ℕ} {p q : ℕ → (LocProd T)ˣ}
    {ξ : LocProd T} {ω : (S.latticeMiddle (LocProd T)).G → ℂ} (hj : j ≤ 𝔰.ϱ) (hξ : IsUnit ξ)
    (hω : (ω = fun x : (S.latticeMiddle (LocProd T)).G ↦
        P.ψ (ξ * ((S.latticeMiddle (LocProd T)).frameGram x.val.val).diag ⟨j, by lia⟩)) ∨
      ∃ i : ℕ, j = i + 1 ∧ ω = 1 ∧ ξ = F.levelUnit⁻¹.val * ((p i)⁻¹.val - (q i)⁻¹.val)) :
    ‖F.floorForm j p q Z.besselVector ω / Z.massRatio.toReal‖ ≤
      S.frequencyDecay T ξ * (finHeadWeight (𝔰.n ^ 6) j p * finHeadWeight (𝔰.n ^ 6) j q) := by
  obtain ⟨pow_four_le, half_pow_le_inv_pow_six, pow_seven_le⟩ : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 ∧
    3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k := S.pow_chain
  have h_bound : ‖F.floorForm j p q Z.besselVector ω‖ₑ ≤ Z.massRatio *
      (.ofReal √(genIndex ξ) ^ (𝔰.k - 𝔰.n ^ 7) * (denomIndex P.integers ξ : ℝ≥0∞)⁻¹ ^ 6 *
        (2 / P.modulus F.levelUnit) ^ 𝔰.n ^ 6 *
          .ofReal (finHeadWeight (𝔰.n ^ 6) j p * finHeadWeight (𝔰.n ^ 6) j q)) :=
    enorm_floorForm_le (ξ := hξ.unit) Z (𝔰.k - 𝔰.n ^ 7) hj (by omega) pow_four_le hω
  -- `frequencyDecay` keeps only the third power of the index of the denominator
  have h_cube : (denomIndex P.integers ξ : ℝ≥0∞)⁻¹ ^ 6 ≤ (denomIndex P.integers ξ : ℝ≥0∞)⁻¹ ^ 3 :=
    pow_le_pow_right_of_le_one' (by simp [Nat.one_le_iff_ne_zero, denomIndex_ne_zero]) (by norm_num)
  grw [h_cube] at h_bound
  grw [norm_div_massRatio_le Z (by simp [denomIndex_ne_zero, mul_eq_top, div_eq_top]) h_bound]
  -- the factors agree one by one, except the power of `2 / modulus F.levelUnit = 2 (S.M ^ f) ^ 2`
  -- (`modulus_levelUnit`), which is bounded by `two_mul_M_pow_sq_pow_le`
  simp (disch := positivity) only [modulus_levelUnit, frequencyDecay, finHeadWeight, toReal_mul,
    toReal_pow, toReal_ofReal, toReal_inv, inv_pow, toReal_div, div_inv_eq_mul]
  gcongr _ * ?_ * _
  exact S.two_mul_M_pow_sq_pow_le

/-- Let `F` be a filling datum with modulus `g` on the unitary group `G` over the completions at
`T`, and let `Z` lie between the congruence subgroup `K(g)` and the integral points. Take the
orbital integral `F.floorForm 0` of `Z.besselVector`, the vector of the translates of the generic
character `χ = phase F.levelUnit` by the cosets of `K(g)` in `Z`. Its norm times the square of
`F.unipotentMass` is at most `F.massIntegral Z = ∫_G |∫_Z χ(y x y⁻¹) dy| ^ 2 dx`. -/
lemma IsFillingData.enorm_floorForm_zero_mul_le {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) (p q : ℕ → (LocProd T)ˣ) :
    ‖F.floorForm 0 p q Z.besselVector 1‖ₑ * F.unipotentMass ^ 2 ≤ F.massIntegral Z := by
  -- Both sides are integrals of `|k₀|²`, up to the factor `F.unipotentMass ^ 2`.
  let k₀ (z : (S.latticeMiddle (LocProd T)).G) : ℂ :=
    F.partialCorrelation 0 (frameCorrelation Z.besselVector 1) 1 z
  have h_form : ‖F.floorForm 0 p q Z.besselVector 1‖ₑ ≤ ∫⁻ z, ‖k₀ z‖ₑ ^ 2 ∂F.groupMeasure := by
    rw [floorForm_zero_eq_integral hF.gauge (isCut_besselVector Z), ← integral_complex_ofReal]
    exact (eNorm_integral_le_lintegral_eNorm _).trans_eq (by simp [k₀, ← ofReal_norm])
  have h_floorZeroForm_eq :
      F.massIntegral Z = ∫⁻ z, ‖k₀ z‖ₑ ^ 2 * F.unipotentMass ^ 2 ∂F.groupMeasure := by
    simp only [massIntegral, enorm_integral_extendedBesselChar_eq_enorm_mul, mul_pow, k₀]
  grw [h_form, h_floorZeroForm_eq, lintegral_mul_const_le]

/-- Let `F` be a filling datum with modulus `g` on the unitary group `G` over the completions at
`T`, `K` the integral points, `vol = F.groupMeasure` the Haar measure, and `K(g) ≤ Z ≤ K`. Write
`ϰ(Z) = F.massIntegral Z = ∫_G |∫_Z χ(y x y⁻¹) dy| ^ 2 dx` with `χ = phase F.levelUnit` the generic
character, `b = S.b` for the size parameter and `k = 𝔰.k` for the rank of the definite summand. If
`ϰ(Z) vol(K) (b ^ (6 k)) ^ s ≤ ϰ(K) vol(Z)` for a natural number `s`, then the orbital integral
`F.floorForm 0` of `Z.besselVector`, divided by `Z.massRatio = vol(Z) vol(K(g)) / F.unipotentMass ^
2`, has norm at most `(1 + b⁻¹ ^ 6) / (b ^ (6 k)) ^ s`. -/
lemma IsFillingData.norm_floorForm_zero_div_massRatio_le {E : Type} {𝔰 : Shape} [Field E]
    [CMType E] {S : Filling E 𝔰} {T : Finset (FinPlace E)}
    [T.StarStable] {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) (s : ℕ)
    (h_floorZeroForm_le : let K := unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram
      F.massIntegral Z * F.groupMeasure K * .ofReal (S.b ^ (6 * 𝔰.k)) ^ s ≤
        F.massIntegral K * F.groupMeasure Z)
    (p q : ℕ → (LocProd T)ˣ) :
    ‖F.floorForm 0 p q Z.besselVector 1 / Z.massRatio.toReal‖ ≤
      (1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ s := by
  let K := unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram
  let vol : Measure (S.latticeMiddle (LocProd T)).G := F.groupMeasure
  have one_le_b : 1 ≤ S.b := S.one_le_b
  have h_cleared : ‖F.floorForm 0 p q Z.besselVector 1‖ₑ * F.unipotentMass ^ 2 *
        .ofReal (S.b ^ (6 * 𝔰.k)) ^ s * vol K ≤
      vol Z * vol F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) * vol K := calc
    _ ≤ F.massIntegral Z * vol K * .ofReal (S.b ^ (6 * 𝔰.k)) ^ s := by
      grw [hF.enorm_floorForm_zero_mul_le, mul_right_comm]
    _ ≤ F.massIntegral K * vol Z := h_floorZeroForm_le
    _ ≤ vol K * vol F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) * vol Z :=
      mul_le_mul_left hF.massIntegral_full_le _
    _ = vol Z * vol F.congruenceSubgroup * .ofReal (1 + S.b⁻¹ ^ 6) * vol K := by ring
  refine (norm_div_massRatio_le Z ofReal_ne_top ?_).trans_eq (toReal_ofReal (by positivity))
  -- clear the denominators and multiply by `vol K`, which is finite and nonzero
  rwa [ofReal_div_of_pos (by positivity), IntermediateGroup.massRatio,
    ← ENNReal.mul_div_mul_comm (by simp) (by simp),
    ENNReal.le_div_iff_mul_le (.inl (mul_ne_zero (by simp) (ofReal_pos.2 (by positivity)).ne'))
      (by simp [mul_eq_top]),
    ← ENNReal.mul_le_mul_iff_left (P.unitaryLevel_open_compact.1.measure_ne_zero _ (by simp))
      (hF.groupMeasure_ne_top le_rfl : vol K ≠ ∞), ← mul_assoc, ofReal_pow (by positivity)]

/-- Let `S` be admissible and `F` a filling datum (a large lattice datum on the unitary group over
the completions at `T`, whose modulus `g` is the component of `S.ideleM`, the product of the two
level primes of `S`), and let `S.ideleM⁻¹` be integral off `T`. Let `Sg` be a set of chosen places
above the first level prime, and for each such place `w` let `d w` be a nonzero vector of the span
of the frame modulo `w` or its conjugate. There is a subgroup `Z` between the congruence subgroup
`K(g)` and the integral points such that (a) `Z` contains the component at `T` of each integral
adelic element whose reduction lies in `S.fixer Sg d`, that is, fixes `d w` for all `w ∈ Sg`; (b)
the orbital integral `F.floorForm 0` of `Z.besselVector` (the translates of the generic character by
the cosets of `K(g)` in `Z`), divided by `Z.massRatio = vol(Z) vol(K(g)) / F.unipotentMass ^ 2`, is
a real number between `0` and `(1 + b⁻¹ ^ 6) / (b ^ (6 k)) ^ #Sg`, where `b = S.b` is the size
parameter and `k = 𝔰.k` the rank of the definite summand. -/
theorem IsFillingData.exists_intermediateGroup_norm_floorForm_div_le {E : Type} {𝔰 : Shape}
    [Field E] [CMType E]
    [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Sg : Finset (S.chosenPlaces 0))
    (d : ∀ w : S.chosenPlaces 0, S.FrameVector w) [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] :
    ∃ Z : F.IntermediateGroup,
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d → S.toPlaces T k ∈ Z.val) ∧
      ∀ p q : ℕ → (LocProd T)ˣ,
        0 ≤ F.floorForm 0 p q Z.besselVector 1 / Z.massRatio.toReal ∧
        ‖F.floorForm 0 p q Z.besselVector 1 / Z.massRatio.toReal‖ ≤
          (1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg := by
  obtain ⟨Z, h_mem, h_floorZeroForm_le⟩ := hF.exists_intermediateGroup_places Sg d Fact.out
  refine ⟨Z, h_mem, fun p q ↦
    ⟨?_, hF.norm_floorForm_zero_div_massRatio_le Z #Sg h_floorZeroForm_le p q⟩⟩
  rw [floorForm_zero_eq_integral hF.gauge (isCut_besselVector Z), ← Complex.ofReal_div]
  positivity

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `F` be a filling datum on the unitary group over the completions at `T`, and let `Z` lie
between its congruence subgroup and the integral points. Let `S.piNAt T` be the component at `T` of
the idele `π_N` with `π π̄ = N`, where `N = S.N` is the split rational prime of `S`. For sequences
of units `p`, `q`, the density `F.lastEntryDensity (S.piNAt T) Z p q` integrates the pairing of the
scaled orbital integrals of `p` and `q` over the vectors of the top quadric with last entry `p ϱ`.
On finitely many sequences `a i` with the same entry `t` at position `ϱ = 𝔰.ϱ`, the number of
hyperbolic planes, it is a positive semidefinite matrix. -/
lemma IsFillingData.posSemidef_lastEntryDensity {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Z : F.IntermediateGroup) {κ : Type} [Fintype κ]
    (a : κ → ℕ → (LocProd T)ˣ) (t : (LocProd T)ˣ) (ha : ∀ i : κ, a i 𝔰.ϱ = t) :
    (Matrix.of fun i j : κ ↦ F.lastEntryDensity (S.piNAt T) Z (a i) (a j)).PosSemidef := by
  classical
  refine ⟨.ext fun i j ↦ ?_, fun x ↦ ?_⟩
  · -- the pairing is Hermitian
    simp [lastEntryDensity, fiberPairing, ← integral_conj, apply_dite, ha]
  · -- the quadratic form of `x` is the integral of a nonnegative function
    have h_nonneg : 0 ≤ ∑ i : κ, ∑ j : κ,
        Matrix.vecMulVec (star ⇑x) ⇑x i j * F.lastEntryDensity (S.piNAt T) Z (a i) (a j) :=
      sum_lastEntryDensity_nonneg Z piNAt_mul_star (Matrix.posSemidef_vecMulVec_star_self x) a ha
    simpa [x.sum_fintype, Matrix.vecMulVec_apply, mul_right_comm] using h_nonneg

/-- Let `F` be a filling datum of admissible data `S` on the unitary group over `LocProd T`, the
product of the completions at the finite places `T`. Its modulus `g = F.levelUnit` is the component
at `T` of `S.ideleM`, the product `M = S.M` of the two level primes as a finite idele; let
`S.ideleM⁻¹` be integral off `T`. Let `Sg` be a set of chosen places above the first level prime and
`d w` a nonzero vector of the span of the frame modulo `w` or its conjugate. There is a subgroup `Z`
between the congruence subgroup `K(g)` and the integral points such that (a) `Z` contains the
component at `T` of each integral adelic element whose reduction lies in `S.fixer Sg d`, that is,
fixes `d w` for all `w ∈ Sg`; (b) the forms `J j p q` in two sequences of units, given by the
orbital integral `F.floorForm j` for `j ≤ ϱ` (the number of hyperbolic planes) and by the density
`F.lastEntryDensity` at the prime `S.piNAt T` above `S.N` for `j > ϱ`, divided by the ratio of
volumes `Z.massRatio`, are a `SieveSystem`. That is: `J j` is the integral of `J (j + 1)` over a
common entry `unitOrOne c` at position `j ≤ ϱ`; the same integral twisted by `ψ (ξ * c)` at a unit
`ξ`, and also `J (j + 1) p q` if `j < ϱ` and `ξ = M⁻¹ (p j)⁻¹ - M⁻¹ (q j)⁻¹` is a unit, are bounded
by `S.frequencyDecay T ξ` times the weights `finHeadWeight (n ^ 6)` of `p` and `q`; `J (ϱ + 1)` is
continuous, and positive semidefinite on sequences with a common entry at `ϱ`; and
`‖J 0 p q‖ ≤ (1 + b⁻¹ ^ 6) / (b ^ (6 k)) ^ #Sg`. Here `ψ = S.charOnPlaces T` is the additive
character of `S` restricted to `T`, `b = S.b` is the size parameter, `n = 𝔰.n = ϱ + 1` and `k = 𝔰.k`
is the rank of the definite summand. -/
lemma IsFillingData.exists_intermediateGroup_sieveSystem {E : Type} {𝔰 : Shape} [Field E] [CMType E]
    [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable]
    {P : IntegralPlace (LocProd T)}
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (hF : S.IsFillingData T F) (Sg : Finset (S.chosenPlaces 0))
    (d : ∀ w : S.chosenPlaces 0, S.FrameVector w) [Fact (↑S.ideleM⁻¹ ∈ integralOff T)] :
    ∃ Z : F.IntermediateGroup,
      -- (a)
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d → S.toPlaces T k ∈ Z.val) ∧
      -- (b)
      SieveSystem unitOrOne (fun u : (LocProd T)ˣ ↦ ratToPlaces T S.M⁻¹ * ↑u⁻¹) 𝔰.ϱ
        (fun (j : ℕ) (p q : ℕ → (LocProd T)ˣ) ↦ (if j ≤ 𝔰.ϱ then F.floorForm j p q Z.besselVector 1
          else F.lastEntryDensity (S.piNAt T) Z p q) / Z.massRatio.toReal)
        (S.charOnPlaces T) ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg)
        (finHeadWeight (𝔰.n ^ 6)) (S.frequencyDecay T) := by
  -- `Z` and the bottom bound come from the bound of floor `0`; the steps are the descent of the
  -- floors below the top and `integral_lastEntryDensity` at the top.
  obtain ⟨Z, h_mem, h_floor_zero⟩ := hF.exists_intermediateGroup_norm_floorForm_div_le Sg d
  obtain ⟨pow_four_le, half_pow_le_inv_pow_six, pow_seven_le⟩ : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 ∧
    3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k := S.pow_chain
  rw [← hF.psi_eq]
  refine ⟨Z, h_mem, by simp, fun j p q ξ hj ↦ ?step, fun a t ha ↦ ?posSemidef, ?continuous,
    fun p q ↦ ?bottom, fun j p q hj hξ ↦ ?off_diagonal⟩
  case step =>
    -- floor `j` is the integral of floor `j + 1`
    simp_rw [← mul_div_assoc, integral_div, ite_eq_left hj]
    split_ifs with hj'
    case' pos =>
      obtain ⟨h_int, h_eq⟩ := hF.gauge.integral_psi_mul_floorForm_succ (p := p) (q := q)
        (isCut_besselVector Z) ⟨j, hj'⟩ 1 ξ (hF.lintegral_formMajorant_ne_top Z 0 hj (by omega))
      simp only [one_mul] at h_int h_eq
    case' neg =>
      obtain rfl : j = 𝔰.ϱ := by omega
      obtain ⟨h_int, h_eq⟩ := integral_lastEntryDensity Z p q piNAt_mul_star ξ
    all_goals
      rw [h_eq]
      exact ⟨h_int.div_const _, fun hξ ↦ by simp [hξ, Pi.one_def],
        fun hξ ↦ hF.norm_floorForm_div_massRatio_le Z hj hξ (.inl rfl)⟩
  case posSemidef =>
    simp only [Nat.not_succ_le_self, ↓reduceIte, div_eq_inv_mul]
    exact .smul (α := ℂ) (hF.posSemidef_lastEntryDensity Z a t ha) (by positivity)
  case continuous =>
    simpa [Function.uncurry_def] using (continuous_lastEntryDensity Z piNAt_mul_star).div_const _
  case bottom => simpa only [ite_eq_left zero_le] using (h_floor_zero p q).2
  case off_diagonal =>
    -- the second case of `norm_floorForm_div_massRatio_le`
    rw [ite_eq_left (Nat.succ_le_of_lt hj)]
    refine hF.norm_floorForm_div_massRatio_le Z hj hξ (.inr ⟨j, rfl, rfl, ?_⟩)
    rw [hF.levelUnit_eq, mul_sub]
    rfl

end New.Filling
end
end

/-!
# Main-term bound for the second moment over open reductions fixing given vectors

This file proves the main-term estimate of the filling theorem. The subgroup
`New.Filling.fixer Sg D` consists of the reductions s that fix the given vectors `D w` modulo w or
its conjugate, at the chosen places `w ∈ Sg` above the first prime. It shows that every term over an
open reduction lies in the big cell. It then proves Siegel's step and uses it to bound the sum over
the open reductions that fix the vectors at `Sg`.

## Main definitions and results

* `New.Filling.IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le`: Siegel's step, which bounds the
  squared norms of finitely many class sums by densities at finite places weighted by the local
  bounds.
* `New.Filling.sum_norm_sum_cosetAmplitude_sq_le`: the estimate for finitely many distinct classes
  whose reductions fix the vectors at `Sg`. The bound is (1 + b⁻⁴) b^(−6 𝔰.k |Sg|) times the main
  second moment times `unipotentCovolume`².
* `New.Filling.linkSecondMoment_isOpenElement_le`: the squared norms of the class sums of the cut
  function add up to at most the same bound. The sum runs over all links, pairs of classes and
  reductions s that are open and fix the vectors at `Sg`; only terms with `termDisc γ ≠ 0` enter.

Notions from other files:
* `New.Filling.IsAdmissible`: The standing hypotheses: `sourceLevel` is the preimage of K(M),
  `reduction` is onto, and size inequalities hold between b, M and ϖ, κ_v, N, the constant
  `scaledSiegelConst`, the second moments, the number of Bessel coordinates and an index.
* `New.Filling.mainSecondMoment`: The real number `sourceDim`² / (`besselDegree` · mass), with the
  mass `New.mass` of the genus of the standard lattice of rank dim V.
* `New.Filling.termsOver` c s c': The terms over (c, s, c'): rational γ such that h_c⁻¹ γ h_c' lies
  in the stabiliser K of the lattice and has reduction s.

## Relation to the literature

In the unfolded second moment of the Poincaré series, the summed main terms are dominated by the
quadratic form of a positive kernel of local Bessel (orbital) integrals at a finite set of primes,
with a constant close to one. With the sieve this bounds the main term above. Kloosterman sums as
local orbital integrals, normal forms for Bessel double cosets and Siegel's formula are known in the
literature. Related work: Jacquet–Ye, Germs of Kloosterman integrals for GL(3), 1999; Y. Liu,
Relative trace formulae toward Bessel and Fourier–Jacobi periods, 2014; Siegel, Über die analytische
Theorie der quadratischen Formen, 1935.
-/

@[expose] public section

section MainTermEstimate

open MeasureTheory Real Finset Matrix Filter Fintype RingHom Complex

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- The leading minors of the frame products (the products of the frame of the middle form over
the lattice with its image under `X`) commute with ring maps. -/
lemma leadingMinor_frameGram_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) (l : Fin (𝔰.n + 1)) :
    leadingMinor ((S.latticeMiddle R').frameGram (X.map φ)) l =
      φ (leadingMinor ((S.latticeMiddle R).frameGram X) l) := by
  rw [leadingMinor, leadingMinor, map_det, Shape.Form.frameGram, Shape.Form.frameGram,
    ← S.map_splitGram_latticeMiddle φ, ← Matrix.map_mul, RingHom.mapMatrix_apply, submatrix_map,
    submatrix_map]

/-- If `γ ∈ S.termsOver c s c'`, that is, `h_c⁻¹ γ h_c'` lies in K and has reduction `s`, then for
each `l` the leading minor of order `l` of `S.frameProducts γ` is integral. At every place `w` in
`S.chosenPlaces i` its reduction `reduceAt w` equals the same minor of
`(S.latticeMiddle (ResField w)).frameGram (s i w)`. -/
lemma exists_leadingMinor_reduceAt_eq {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') (l : Fin (𝔰.n + 1)) :
    ∃ δ : Ô E, δ.val = algebraMap E (𝔸f E) (leadingMinor (S.frameProducts γ) l) ∧
      ∀ (i : Fin 2) (w : S.chosenPlaces i), reduceAt w.val δ =
        leadingMinor ((S.latticeMiddle (ResField w.val)).frameGram (s i w).val) l := by
  -- The translate of `γ` by class representatives has an integral matrix with the frame products of
  -- `γ` and reduction `s`.
  obtain ⟨k, rfl, hk⟩ := hγ
  let X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E) :=
    of fun a b ↦ ⟨k.val.val.val a b, (mem_intGL.1 k.property).1 a b⟩
  refine ⟨leadingMinor ((S.latticeMiddle (Ô E)).frameGram X) l, ?_, fun i w ↦ ?_⟩
  · have h_gram : (S.latticeMiddle (𝔸f E)).frameGram (X.map (Ô E).subtype) =
        (S.frameProducts γ).map (algebraMap E (𝔸f E)) :=
      (congrArg (fun g : S.GFin ↦ (S.latticeMiddle (𝔸f E)).frameGram g.val.val) hk).trans
        frameGram_translateByClassReps
    rw [← (Ô E).coe_subtype, ← leadingMinor_frameGram_map, h_gram, leadingMinor, leadingMinor,
      map_det, RingHom.mapMatrix_apply, submatrix_map]
  · rw [show (S.reduction k i w).val = X.map (reduceAt w.val) from rfl, leadingMinor_frameGram_map]

/-- If `s` is open, that is, at some chosen place above the first prime none of its proper leading
minors of frame products vanishes, then for every term `γ` over a block `(c, s, c')` no proper
leading minor of the frame products of `γ` vanishes: `γ` lies in the big cell. -/
lemma IsOpenElement.leadingMinor_ne_zero {c c' : S.Classes} {s : S.ResidueGL}
    (hs : S.IsOpenElement s) {γ : S.G E} (hγ : γ ∈ S.termsOver c s c') (l : Fin 𝔰.n) :
    leadingMinor (S.frameProducts γ) l.castSucc ≠ 0 := by
  obtain ⟨w, hw⟩ := hs
  obtain ⟨δ, hδ, h_red⟩ := exists_leadingMinor_reduceAt_eq hγ l.castSucc
  intro h_zero
  exact hw l (by rw [← h_red, show δ = 0 from Subtype.ext (by simp [hδ, h_zero]), map_zero])

/-- With `f` the number of infinite places, the factor `(1 + S.b⁻¹ ^ 10) ^ f` of the sieve is at
most `1 + S.b⁻¹ ^ 9`, because `f ≤ S.b / 1000` by the hypothesis `S.IsAdmissible`. -/
lemma one_add_inv_pow_ten_pow_le :
    (1 + S.b⁻¹ ^ 10) ^ Core.numInfPlaces E ≤ 1 + S.b⁻¹ ^ 9 := by
  have hb_one : 1 ≤ S.b := le_trans (by norm_num) S.thousand_le_b
  set u : ℝ := S.b⁻¹ ^ 9 / 1000 with hu_def
  have hu : 0 ≤ u := by positivity
  have h_le_one : S.b⁻¹ ^ 9 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hb_one)
  have h_exp : |rexp u - 1| ≤ 2 * |u| := abs_exp_sub_one_le (abs_le.2 ⟨by linarith, by linarith⟩)
  calc (1 + S.b⁻¹ ^ 10) ^ Core.numInfPlaces E
      ≤ rexp (S.b⁻¹ ^ 10) ^ Core.numInfPlaces E := by grw [add_comm, add_one_le_exp]
    _ = rexp (Core.numInfPlaces E * S.b⁻¹ ^ 10) := (Real.exp_natCast_mul _ _).symm
    _ ≤ rexp (S.b / 1000 * S.b⁻¹ ^ 10) := by grw [S.numInfPlaces_le_div]
    _ = rexp u := by simp [u, field]
    _ ≤ 1 + S.b⁻¹ ^ 9 := by linarith [le_abs_self (rexp u - 1), abs_of_nonneg hu]

/-- For `0 ≤ u ≤ 1 / 1000` one has `(1 + u⁶) ((1 + u⁹)² (1 + u⁶) + u¹⁰) ≤ 1 + u⁴`. With `u = b⁻¹`
this collects the error factors in `sieve_constant_le`. -/
lemma one_add_pow_six_mul_add_pow_ten_le_one_add_pow_four {u : ℝ} (hu : 0 ≤ u)
    (hu_le : u ≤ 1 / 1000) :
    (1 + u ^ 6) * ((1 + u ^ 9) * (1 + u ^ 9) * (1 + u ^ 6) + u ^ 10) ≤ 1 + u ^ 4 := by
  -- All powers on the left are at most `s = u ^ 4 / 100`.
  have hu_one : u ≤ 1 := by linarith
  set s : ℝ := u ^ 4 / 100 with hs_def
  have hs : 0 ≤ s := by positivity
  have hs_one : s ≤ 1 := by linarith [pow_le_one₀ hu hu_one (n := 4)]
  have h_six : u ^ 6 ≤ s := by
    have h_sq : u ^ 2 ≤ 1 / 100 := by nlinarith
    calc u ^ 6 = u ^ 4 * u ^ 2 := by ring
      _ ≤ u ^ 4 * (1 / 100) := by gcongr
      _ = s := by ring
  have h_nine : u ^ 9 ≤ s := (pow_le_pow_of_le_one hu hu_one (by norm_num)).trans h_six
  have h_ten : u ^ 10 ≤ s := (pow_le_pow_of_le_one hu hu_one (by norm_num)).trans h_six
  calc
    _ ≤ (1 + s) * ((1 + s) * (1 + s) * (1 + s) + s) := by gcongr
    _ = 1 + s * (5 + 7 * s + 4 * s ^ 2 + s ^ 3) := by ring
    _ ≤ 1 + s * (5 + 7 * 1 + 4 * 1 ^ 2 + 1 ^ 3) := by gcongr
    _ ≤ 1 + u ^ 4 := by linarith

/-- The normalising constant `r` of the main term, used with `k = 𝔰.k - 1`: the product over the
infinite places of √`openCellConst` and powers of the squared scales `frameScaleSq` of the frame
vectors, divided by the number of Bessel coordinates. -/
noncomputable abbrev normalizingConst (S : Filling E 𝔰) (k : ℕ) : ℝ :=
  (∏ v : NumberField.InfinitePlace E,
    √𝔰.openCellConst * ∏ a : Fin 𝔰.n, S.frameScaleSq v a ^ (k + 2 * a.rev)) /
      Fintype.card S.BesselCoord

/-- Assume `𝔰.k = kPred + 1`. The product of the Poisson summation constants
`S.poissonConst i` over `i < 𝔰.n` is `S.normalizingConst kPred ^ 2` times
`volÔ E ^ 𝔰.n (dim / Λ) ^ 2 / c_G ^ f`, where `dim = Fintype.card S.BesselCoord` is the number of
Bessel coordinates, `Λ = S.frameScaleProd`, `c_G = 𝔰.openCellConst` and `f` is the number of
infinite places. -/
lemma prod_poissonConst_eq {kPred : ℕ} (hk : 𝔰.k = kPred + 1) :
    ∏ i ∈ Finset.range 𝔰.n, S.poissonConst i =
      S.normalizingConst kPred ^ 2 *
        (volÔ E ^ 𝔰.n * (Fintype.card S.BesselCoord / S.frameScaleProd) ^ 2 /
          𝔰.openCellConst ^ Core.numInfPlaces E) := by
  have h_scale (v : NumberField.InfinitePlace E) (a : ℕ) : S.frameScaleSq v a ≠ 0 :=
    (S.frameScaleSq_pos v a).ne'
  have h_cell : 𝔰.openCellConst ≠ 0 := 𝔰.openCellConst_pos.ne'
  -- one factor `S.frameScaleSq v a` splits off each power in `S.frameScaleProd`
  have h_prod : S.frameScaleProd =
      (∏ v : NumberField.InfinitePlace E, ∏ a : Fin 𝔰.n,
        S.frameScaleSq v a ^ (kPred + 2 * a.rev)) *
        ∏ a : Fin 𝔰.n, ∏ v : NumberField.InfinitePlace E, S.frameScaleSq v a := by
    rw [Finset.prod_comm (s := univ) (t := univ) (f := fun (a : Fin 𝔰.n) v ↦ S.frameScaleSq v a)]
    simp only [frameScaleProd, hk, ← prod_mul_distrib, ← pow_succ, Fin.val_rev, Nat.succ_sub_succ,
      add_right_comm kPred 1]
  simp only [poissonConst, normalizingConst, prod_range, prod_div_distrib, prod_const, card_univ,
    card_range, prod_mul_distrib, prod_pow, h_prod, div_pow, mul_pow, ← pow_mul, mul_comm _ 2]
  rw [pow_mul √𝔰.openCellConst, sq_sqrt 𝔰.openCellConst_pos.le]
  field [prod_eq_zero_iff, h_scale]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- The error is measured against the identity second moment. Let `f` be the number of infinite
places, `n = 𝔰.n = ϱ + 1` the number of frame vectors, `k = 𝔰.k` and `dim` the number of Bessel
coordinates. The left side has three factors: the constant `scaledSiegelConst` of Siegel's step; the
quotient `vol(Ô) ^ n (dim / Λ)² / c_G ^ f` of the constants of Poisson summation by the squared
normalising constant, where `Λ = frameScaleProd` is a product of powers of the squared scales of the
frame vectors and `c_G = openCellConst = vol U(k)² / (vol U(k + 2ϱ + 1) vol U(k - 1))`; and
`decayConst`, the product over the infinite places `v` of a volume ratio of the shape times
`(|κ_v| ^ (2ϱ + 1) / (M N)) ^ (k - n⁷)` with `κ_v = S.realM v`. It is at most `b ^ (n⁹ f)` times
`dim * identitySecondMoment * unipotentCovolume²`. Here `identitySecondMoment` is the order of the
reduction of the Bessel subgroup times the number of classes times `dim`. -/
lemma scaledSiegelConst_mul_decayConst_le [S.IsAdmissible] :
    S.scaledSiegelConst * (volÔ E ^ 𝔰.n * (Fintype.card S.BesselCoord / S.frameScaleProd) ^ 2 /
        𝔰.openCellConst ^ Core.numInfPlaces E) * S.decayConst ≤
      S.b ^ (𝔰.n ^ 9 * Core.numInfPlaces E) *
        (Fintype.card S.BesselCoord * S.identitySecondMoment * S.unipotentCovolume ^ 2) := by
  -- Apart from the common factor `c`, both sides are `f`-th powers, of `A` and of `b ^ n⁹ * B`.
  have hb : 1 ≤ S.b := S.one_le_b
  have hM : (1 : ℝ) ≤ S.M := mod_cast one_le_two.trans two_le_M
  have hN : (1 : ℝ) ≤ S.N := mod_cast S.N_prime.pos
  obtain ⟨s, hs, hs_sq⟩ : ∃ s : ℝ, 1 ≤ s ∧ NumberField.rootDiscr E = s ^ 2 :=
    ⟨√(NumberField.rootDiscr E), Real.one_le_sqrt.2 (one_le_rootDiscr E),
      (sq_sqrt (rootDiscr_pos E).le).symm⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 𝔰.k = 𝔰.n ^ 7 + K := exists_add_of_le (by
    grw [← S.pow_le_k, Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num : 7 ≤ 9)]
    lia)
  -- `Q ^ f` is the product of the `|κ_v|` and `x` the base of the decay at one place. The power
  -- `S.M ^ D` is an explicit factor of `A`, and its square is a factor of `B`.
  let Q : ℝ := S.M * s ^ 2 / (2 * π)
  let x : ℝ := Q ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N)
  let D : ℕ := 𝔰.ϱ * (2 * 𝔰.k + 2 * 𝔰.ϱ + 1)
  let A : ℝ := S.M ^ D * (π ^ 𝔰.k / (𝔰.k - 1).factorial / S.N ^ 𝔰.k * s * (2 / s ^ 2) ^ 𝔰.k) *
    ((2 / s ^ 2) ^ 𝔰.n / 𝔰.openCellConst) * (𝔰.scaledVolumeRatio * x ^ K)
  let B : ℝ := (S.M ^ D / S.N ^ 𝔰.k * (s ^ 2 / 2) ^ (𝔰.ϱ * (𝔰.k + 𝔰.ϱ)) * s ^ 𝔰.ϱ) ^ 2
  let c : ℝ := Nat.card (S.reducedImage besselS) * card S.Classes *
    (card S.BesselCoord / S.frameScaleProd) ^ 2
  have h_kappa : ∏ v, |S.realM v| = Q ^ Core.numInfPlaces E := by rw [prod_abs_realM, hs_sq]
  have h_disc : √√|(NumberField.discr E : ℝ)| = s ^ Core.numInfPlaces E := by
    rw [abs_discr_eq_rootDiscr_pow, sqrt_sq (pow_pos (rootDiscr_pos E) _).le, hs_sq,
      pow_right_comm, sqrt_sq (by positivity)]
  have h_vol : (volÔ E : ℝ) = (2 / s ^ 2) ^ Core.numInfPlaces E := by
    rw [volÔ_eq, hs_sq, ← inv_pow, inv_div]
  have h_left : S.scaledSiegelConst * (volÔ E ^ 𝔰.n * (card S.BesselCoord / S.frameScaleProd) ^ 2 /
      𝔰.openCellConst ^ Core.numInfPlaces E) * S.decayConst = c * A ^ Core.numInfPlaces E := by
    rw [scaledSiegelConst, unipotentOrder, Nat.cast_pow]
    simp only [siegelConst, decayConst, show 𝔰.k - 𝔰.n ^ 7 = K by lia, prod_mul_distrib, prod_pow,
      prod_div_distrib, prod_const, card_univ, h_kappa, h_disc, h_vol, A, c, x, D, mul_pow, div_pow]
    ring
  have h_right : card S.BesselCoord * S.identitySecondMoment * S.unipotentCovolume ^ 2 =
      c * B ^ Core.numInfPlaces E := by
    have h_sum : ∑ a ∈ range 𝔰.ϱ, (a + (𝔰.k + 1) + a) = 𝔰.ϱ * (𝔰.k + 𝔰.ϱ) := by
      induction 𝔰.ϱ with
      | zero => simp
      | succ n ih => grind [sum_range_succ]
    simp only [identitySecondMoment, sourceDim, unipotentCovolume, h_sum, h_disc, h_vol,
      Nat.cast_mul, B, c, D, mul_pow, div_pow, div_div_eq_mul_div]
    ring
  -- At one place, `A` is `B` times factors that do not depend on `k`.
  have hQ : 1 ≤ Q :=
    (one_le_pow_iff_of_nonneg (by positivity) Fintype.card_ne_zero).1
      ((Finset.one_le_prod₀ fun v _ ↦ S.one_le_abs_realM v).trans_eq h_kappa)
  have h_place : A = B * ((2 / s ^ 2) ^ (𝔰.n + 2 * 𝔰.ϱ ^ 2) * (s / s ^ (2 * 𝔰.ϱ)) /
      (2 * S.M ^ (𝔰.ϱ * (2 * 𝔰.ϱ + 1))) * x⁻¹ ^ 𝔰.n ^ 7) := by
    have h_x : x ^ K = x ^ 𝔰.k * x⁻¹ ^ 𝔰.n ^ 7 := by
      simp [hK, pow_add, field]
    simp only [A, B, h_x]
    generalize x⁻¹ ^ 𝔰.n ^ 7 = y
    simp only [x, Q, D, Shape.openCellConst, Shape.scaledVolumeRatio, sphereDensity, one_pow,
      mul_pow, div_pow]
    field [(volU_pos _).ne']
  -- Those factors are at most `b ^ n⁹`: `2 / s²` is at most `b`, `s / s^(2ϱ)` at most `1` and
  -- `x⁻¹` at most a power of `b`.
  have h_factor : (2 / s ^ 2) ^ (𝔰.n + 2 * 𝔰.ϱ ^ 2) * (s / s ^ (2 * 𝔰.ϱ)) /
      (2 * S.M ^ (𝔰.ϱ * (2 * 𝔰.ϱ + 1))) * x⁻¹ ^ 𝔰.n ^ 7 ≤ S.b ^ 𝔰.n ^ 9 := by
    have h_two : 2 / s ^ 2 ≤ S.b := (div_le_self zero_le_two (one_le_pow₀ hs)).trans two_le_b
    have h_s : s / s ^ (2 * 𝔰.ϱ) ≤ 1 :=
      div_le_one_of_le₀ (le_self_pow₀ hs (by grind [S.ten_pow_five_le_varrho])) (by positivity)
    have h_inv : x⁻¹ ≤ S.b ^ 23 * S.b ^ (60 * 𝔰.n) := by
      grw [inv_div, div_le_self (by positivity) (one_le_pow₀ hQ), S.M_le_b_pow, S.N_le]
    grw [div_le_self (by positivity) (by bound), h_two, h_s, h_inv, mul_one, ← pow_add, ← pow_mul,
      ← pow_add]
    refine pow_le_pow_right₀ hb ?_
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 𝔰.ϱ = 10 ^ 5 + m := exists_add_of_le S.ten_pow_five_le_varrho
    simp only [Shape.n, hm]
    lia
  rw [h_left, h_right, pow_mul, mul_left_comm, ← mul_pow, h_place, mul_comm B]
  gcongr

/-- Let `S` be admissible with size parameter `b`, `kPred = 𝔰.k - 1`, and let the number `numSieved`
of places at which vectors are fixed be at most `f`, the number of infinite places. The theorem
`sieve` bounds a sum of last entry densities over pairs of heads by `(∏ i, poissonConst i) * ((∏ v,
(1 + b⁻¹⁰) / deg v) * m + ε)`. Here `poissonConst i`, the constant of Poisson summation in entry
`i`, is vol(Ô) over the Jacobian of the scaling at the infinite places; `deg v` is the degree of the
Bessel system at `v`; `m` bounds the mass at the finite places; and
`ε = b^(2403 𝔰.n⁹ f) * decayConst` is the error, `decayConst` being the product of the constants in
the decay at the infinite places. For `m = (1 + b⁻⁶) / b^(6 𝔰.k numSieved)`, this bound times the
constant `(1 + b⁻⁶) * scaledSiegelConst` of Siegel's step is at most `r² (1 + b⁻⁴) b^(-6 𝔰.k
numSieved) * mainSecondMoment * unipotentCovolume²`, where `r = S.normalizingConst kPred` and
`mainSecondMoment = sourceDim² / ((∏ v, deg v) * mass)`, with the mass of the genus of the standard
Hermitian lattice of rank `𝔰.r`. -/
lemma sieve_constant_le [S.IsAdmissible] {kPred numSieved : ℕ} (hk : 𝔰.k = kPred + 1)
    (h_numSieved : numSieved ≤ Core.numInfPlaces E) :
    (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst *
        ((∏ i ∈ Finset.range 𝔰.n, S.poissonConst i) *
          ((∏ v : NumberField.InfinitePlace E, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
              ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ numSieved) +
            S.b ^ (2403 * 𝔰.n ^ 9 * Core.numInfPlaces E) * S.decayConst)) ≤
      S.normalizingConst kPred ^ 2 *
        ((1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.mainSecondMoment *
          S.unipotentCovolume ^ 2) := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_main : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_deg : 0 < S.besselDegree := S.besselDegree_pos
  have h_cell : 0 < 𝔰.openCellConst := 𝔰.openCellConst_pos
  rw [prod_poissonConst_eq hk]
  set f : ℕ := Core.numInfPlaces E
  set r : ℝ := S.normalizingConst kPred
  set w : ℝ := volÔ E ^ 𝔰.n * (card S.BesselCoord / S.frameScaleProd) ^ 2 / 𝔰.openCellConst ^ f
  set y : ℝ := (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.mainSecondMoment * S.unipotentCovolume ^ 2
  -- The masses: the constants make up the main second moment.
  have h_const : S.scaledSiegelConst * w ≤
      (1 + S.b⁻¹ ^ 9) * S.mainSecondMoment * S.besselDegree * S.unipotentCovolume ^ 2 := by
    have h_scale : 0 < S.frameScaleProd :=
      prod_pos fun v _ ↦ prod_pos fun a _ ↦ pow_pos (S.frameScaleSq_pos v a) _
    grw [IsAdmissible.scaledSiegelConst_le]
    refine le_of_eq ?_
    simp only [w, f]
    field_simp [volÔ_ne_zero (E := E)]
  have h_mass : S.scaledSiegelConst * w * ((∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
      ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ numSieved)) ≤
        (1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 6) * y := by
    grw [prod_div_distrib, prod_const, card_univ, ← besselDegree, h_const,
      one_add_inv_pow_ten_pow_le]
    refine le_of_eq ?_
    simp only [y, inv_pow (S.b ^ (6 * 𝔰.k))]
    field_simp
  -- The errors: they are at most `b ^ (O(n⁹ f))` times `dim` times the identity second moment,
  -- which is at most `b ^ (-11 𝔰.k f)` times the main second moment.
  have h_error : S.scaledSiegelConst * w * (S.b ^ (2403 * 𝔰.n ^ 9 * f) * S.decayConst) ≤
      S.b⁻¹ ^ 10 * y := by
    have h_exp : 2403 * 𝔰.n ^ 9 * f + 𝔰.n ^ 9 * f + 2 * 𝔰.k * f + (10 + 6 * 𝔰.k * numSieved) ≤
        11 * (𝔰.k * f) := by
      have h_rank : 512000 * 𝔰.n ^ 9 ≤ 𝔰.k := S.pow_le_k.trans_eq' (by ring)
      linarith [Nat.mul_le_mul_right f h_rank, Nat.mul_le_mul_left 𝔰.k h_numSieved,
        show 0 < 𝔰.n ^ 9 * f from Nat.mul_pos (by positivity) Fintype.card_pos]
    calc
      _ = S.b ^ (2403 * 𝔰.n ^ 9 * f) * (S.scaledSiegelConst * w * S.decayConst) := by ring
      _ ≤ S.b ^ (2403 * 𝔰.n ^ 9 * f) * (S.b ^ (𝔰.n ^ 9 * f) *
          (S.b ^ (2 * 𝔰.k * f) * S.identitySecondMoment * S.unipotentCovolume ^ 2)) := by
        grw [scaledSiegelConst_mul_decayConst_le, IsAdmissible.card_besselCoord_le]
      _ = S.b ^ (2403 * 𝔰.n ^ 9 * f + 𝔰.n ^ 9 * f + 2 * 𝔰.k * f + (10 + 6 * 𝔰.k * numSieved)) *
          S.identitySecondMoment *
          (S.b⁻¹ ^ 10 * (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.unipotentCovolume ^ 2) := by
        simp only [pow_add, inv_pow, ← pow_mul]
        field_simp
      _ ≤ S.mainSecondMoment *
          (S.b⁻¹ ^ 10 * (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.unipotentCovolume ^ 2) := by
        grw [h_exp, IsAdmissible.mul_identitySecondMoment_le]
      _ = _ := by ring
  calc
    _ = r ^ 2 * ((1 + S.b⁻¹ ^ 6) *
        (S.scaledSiegelConst * w * ((∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
          ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ numSieved)) +
        S.scaledSiegelConst * w * (S.b ^ (2403 * 𝔰.n ^ 9 * f) * S.decayConst))) := by ring
    _ ≤ r ^ 2 * ((1 + S.b⁻¹ ^ 6) *
        ((1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 6) + S.b⁻¹ ^ 10) * y) := by
      grw [h_mass, h_error]
      exact le_of_eq (by ring)
    _ ≤ r ^ 2 * ((1 + S.b⁻¹ ^ 4) * y) := by
      grw [one_add_pow_six_mul_add_pow_ten_le_one_add_pow_four (by positivity)
        (by simpa using inv_anti₀ (by simp) S.thousand_le_b)]
    _ = _ := by ring

/-- The square of the normalising constant is positive. -/
lemma normalizingConst_sq_pos (kPred : ℕ) :
    0 < S.normalizingConst kPred ^ 2 := by
  have h_prod : 0 < ∏ v : NumberField.InfinitePlace E,
      √𝔰.openCellConst * ∏ a : Fin 𝔰.n, S.frameScaleSq v a ^ (kPred + 2 * a.rev) :=
    prod_pos fun v _ ↦ mul_pos (Real.sqrt_pos.2 𝔰.openCellConst_pos)
      (prod_pos fun a _ ↦ pow_pos (S.frameScaleSq_pos v a) _)
  unfold normalizingConst
  positivity

/-- Let `P` be a structure of finite place on the product of the completions at `T`, and `G` a
filling datum for it. Let the head have ϱ first entries `p`, units off `T`, and last entry `t` with
‖t‖² > N² at every infinite place; `x v a` is its entry of index `a` under `Φ v` times
`S.frameScaleSq v a = κ_v^(2(ϱ - a)) / N`, the squared scale of the frame vector `a`
(`κ_v = S.realM v`). The first factor on the left is the product over `v` of the scalars of
`normalizedOrbitalIntegral` at `x v`; in it `openCellConst` is a ratio of volumes of compact unitary
groups and `(S.besselSystem v).Index` indexes a basis of the value space of the Bessel functions at
`v`. The second factor `G.headDensity` is a product of powers of the moduli of `p` for `P`. Their
product is `S.normalizingConst kPred`, with `kPred = 𝔰.k - 1`, times the square root of (∏ (‖t‖² -
N²))^(𝔰.k - 1). By the product formula the powers of `p` cancel; the constant collects
√`openCellConst`, the powers of the squared scales and the numbers of indices. -/
lemma gramScalar_mul_headDensity
    {T : Finset (FinPlace E)} [T.StarStable] {P : Floors.IntegralPlace (LocProd T)}
    {G : Floors.PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
      (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)} {kPred : ℕ} (hk : 𝔰.k = kPred + 1)
    {T₀ : Finset Eˣ} (hT₀ : ∀ x ∈ T₀, x.val ∈ ratIntegralOff T ∧ x⁻¹.val ∈ ratIntegralOff T)
    {t : Eˣ} (h_large : ∀ v : NumberField.InfinitePlace E, S.N ^ 2 < ‖Φ v t.val‖ ^ 2)
    (p : Fin 𝔰.ϱ → T₀) :
    let x (v : NumberField.InfinitePlace E) (a : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t a).val)
    (∏ v : NumberField.InfinitePlace E, √𝔰.openCellConst *
        √(‖(x v 𝔰.ϱ).val‖ ^ 2 - 1) ^ (𝔰.k - 1) / Fintype.card (S.besselSystem v).Index *
        ∏ a ∈ Finset.range 𝔰.ϱ, ‖(x v a).val‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))) *
      (G.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t)
        1).toReal =
      S.normalizingConst kPred *
        √((∏ v : NumberField.InfinitePlace E, (‖Φ v t.val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) := by
  intro x
  have h_sqrt : √((∏ v : NumberField.InfinitePlace E, (‖Φ v t.val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) =
      (∏ v : NumberField.InfinitePlace E, √(‖Φ v t.val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1) := by
    simp [sqrt_eq_rpow, rpow_pow_comm, finsetProd_rpow, (h_large _).le, prod_nonneg]
  -- The product formula cancels the entries of the head.
  have h_product (a : Fin 𝔰.ϱ) :
      P.modulus (evalPlaces T (p a : Eˣ).val) ^ (2⁻¹ : ℝ) =
        (∏ v : NumberField.InfinitePlace E, ‖Φ v (p a : Eˣ).val‖ₑ)⁻¹ :=
    P.modulus_evalPlaces_rpow_half (hT₀ (p a) (p a).prop)
  have h_scale (v : NumberField.InfinitePlace E) (a : ℕ) : S.frameScaleSq v a ≠ 0 :=
    (S.frameScaleSq_pos v a).ne'
  -- In the normalising constant, split off the scale of the last frame vector.
  have h_const : S.normalizingConst kPred =
      (∏ v : NumberField.InfinitePlace E, √𝔰.openCellConst *
        ((∏ a : Fin 𝔰.ϱ, S.frameScaleSq v a ^ (kPred + 2 * (a.rev + 1))) *
          S.frameScaleSq v 𝔰.ϱ ^ kPred)) / Fintype.card S.BesselCoord := by
    simp only [normalizingConst, Fin.prod_univ_castSucc, Fin.rev_castSucc, Fin.rev_last,
      Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, mul_zero, add_zero]
  rw [h_sqrt, h_const]
  simp [x, frameScaleSq.eq_1 S _ 𝔰.ϱ, div_pow, div_mul_eq_mul_div, div_sub_one, -one_div, hk,
    mul_add, unitOrOne, mul_pow, abs_of_pos, pow_add, padTuple, prod_pow, prod_range, h_scale,
    Floors.PlaceData.headDensity, h_product,
    Finset.prod_comm (t := (univ : Finset (Fin 𝔰.ϱ))), prod_eq_zero_iff, field,
    Nat.Prime.ne_zero, prod_mul_distrib]

/-- Let `S` be an admissible filling, and `σ` a rational element of the floor group (it fixes the
hyperbolic basis vectors `e_a`, `e*_a` for `a < ϱ`) with last frame product `t`. A head is a tuple
`p` of ϱ entries from a finite set `T₀` of units of `E`, followed by `t`; `x v p a` is its entry of
index `a` under the embedding `Φ v`, times the squared scale `S.frameScaleSq v a` of the frame
vector `a` at `v`. The Weyl element `w_p` of the head sends `e_a` to `p_a e*_a` and `e*_a` to
`e_a / p̄_a` for `a < ϱ`. Let `W = S.besselFn .cut` be the product over the infinite places of the
cut Bessel functions W♭, which have bounded support modulo the Bessel subgroup, and let
`besselOrbitalIntegral volume W γ` be the tensor ∫ W(g) ⊗ W(γ⁻¹ g)^* dg. Let `R p q` be the product
over `v` of `bandLimit 𝔰.n`, the top one of the forms on pairs of heads that the Bessel system at
`v` provides for the sieve. Then `R` is the Gram matrix of the orbital integrals at `γ = w_p σ`,
each weighted by the product over `v` of the scalar of `normalizedOrbitalIntegral`, √c_G · (|x_ϱ|² -
1)^((k - 1)/2) · |I|⁻¹ · ∏_{a<ϱ} |x_a|^(k + 1 + 2(ϱ - a - 1)), where `x = x v p`, `k = 𝔰.k`,
`c_G = 𝔰.openCellConst` and `I` is the index set of the Bessel system at `v`. -/
lemma prod_bandLimit_eq_gram {T₀ : Finset Eˣ} {σ : S.G E} {t : Eˣ}
    (hσ : σ ∈ Shape.Form.floorGroup 𝔰.ϱ) (h_tail : S.frameProducts σ 𝔰.top 𝔰.top = t) :
    let x (v : NumberField.InfinitePlace E) (p : Fin 𝔰.ϱ → T₀) (a : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t a).val)
    let R : Matrix (Fin 𝔰.ϱ → T₀) (Fin 𝔰.ϱ → T₀) ℂ := fun p q : Fin 𝔰.ϱ → T₀ ↦
      ∏ v : NumberField.InfinitePlace E, (S.besselSystem v).bandLimit 𝔰.n (x v p) (x v q)
    R = Matrix.gram ℂ fun p : Fin 𝔰.ϱ → T₀ ↦
      (∏ v : NumberField.InfinitePlace E, √𝔰.openCellConst *
          √(‖(x v p 𝔰.ϱ).val‖ ^ 2 - 1) ^ (𝔰.k - 1) / Fintype.card (S.besselSystem v).Index *
          ∏ a ∈ Finset.range 𝔰.ϱ, ‖(x v p a).val‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))) •
        besselOrbitalIntegral volume
          (fun g : NumberField.InfinitePlace E → 𝔰.G₁ ↦ WithLp.toLp 2 (S.besselFn .cut g))
          (S.ratToInf
            (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) t) * σ)) := by
  intro x R
  ext p q
  -- At each infinite place both heads end in the last frame product of `σ`, so the band limit is an
  -- inner product of normalised orbital integrals.
  have h_local (v : NumberField.InfinitePlace E) :
      (S.besselSystem v).bandLimit 𝔰.n (x v p) (x v q) =
        inner ℂ (normalizedOrbitalIntegral (S.ratToInf σ v) ((S.besselSystem v).besselFn .cut)
          (x v p))
          (normalizedOrbitalIntegral (S.ratToInf σ v) ((S.besselSystem v).besselFn .cut)
            (x v q)) := by
    have h_last : realFrameGram (S.ratToInf σ v) 𝔰.top 𝔰.top = x v p 𝔰.ϱ := by
      simp [h_tail, x, frameScaleSq, padTuple, unitOrOne, S.N_prime.ne_zero]
    have h_same : x v q 𝔰.ϱ = x v p 𝔰.ϱ := by simp [x, padTuple]
    exact (S.besselSystem v).hasLocalBounds.right (S.ratToInf σ v)
      (hσ.ratToInf_mem_agreeWithOneOn v) (x v p) (x v q) h_last h_same
  refine (prod_congr rfl fun v _ ↦ h_local v).trans ?_
  -- the scaled orbital integrals of the product vector are the products of the local ones
  simp_rw [normalizedOrbitalIntegral, gram_apply, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
    real_smul]
  simp only [inner, besselFn, besselOrbitalIntegral, Pi.mul_apply, Pi.inv_apply, Complex.star_def,
    prod_univ_sum, ratToInf_weylElem_mul, prod_mul_distrib, ← map_prod, sum_prod_type,
    ← integral_fintype_prod_volume_eq_prod, ← ofReal_prod]
  rfl'

variable [WeilData E]

/-- Siegel's step. Let `S` be an admissible filling of shape `𝔰` over a CM field `E` with Weil data,
and let `kPred = 𝔰.k - 1`. Let `1 / M`, `1 / N`, the lattice basis and its inverse be integral off
the finite set of places `T`. Let `P` be a structure of finite place on the product of the
completions at `T`, `G` a filling datum for it, and `Y` a group between the congruence group of `G`
and the integral points. Take finitely many distinct classes `(c i, S.reduction (n i), c' i, σ i)`,
with `σ i` in the floor group, last entry `t i` with ‖t i‖² > N² at every infinite place, position
integral off `T` and lift `n i` in `Y` at `T`.

On the left, `S.cosetAmplitude .cut c s c' γ` is the sum of the amplitudes of the cut function at
`u γ u'⁻¹` over the rational unipotent `u`, `u'` for which this element lies over `(c, s, c')`. It
is summed over `γ = w_p σ`, for the Weyl elements `w_p` of the heads with first entries `p` in a
finite set `T₀` of units off `T`. The squared norms of these class sums, times `r²` for the
normalising constant `r`, add up to at most `(1 + b⁻⁶) * S.scaledSiegelConst` times the real part of
a sum over the last entries and the pairs of heads. The summand is the product of the top forms
`bandLimit 𝔰.n` of the Bessel systems at the infinite places with the density `G.lastEntryDensity`
at `T`, divided by `Y.massRatio = vol(Y) vol(K) / fl²`, where `K` is the congruence group of `G` and
`fl = G.unipotentMass`. -/
lemma IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le [S.IsAdmissible] {T : Finset (FinPlace E)}
    [T.StarStable] [Fact (S.ideleM⁻¹.val ∈ integralOff T)] {P : Floors.IntegralPlace (LocProd T)}
    {G : Floors.PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
      (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)} (hG : S.IsFillingData T G) (Y : G.IntermediateGroup)
    {kPred : ℕ} (hk : 𝔰.k = kPred + 1) {ι : Type} [Fintype ι] [DecidableEq Eˣ]
    {c c' : ι → S.Classes} {σ : ι → S.G E} {n : ι → S.latticeStabilizer} {t : ι → Eˣ}
    (h_inj : (fun i : ι ↦ (c i, c' i, S.reduction (n i), σ i)).Injective)
    (hσ : ∀ i : ι, σ i ∈ Shape.Form.floorGroup 𝔰.ϱ)
    (h_tail : ∀ i : ι, S.frameProducts (σ i) 𝔰.top 𝔰.top = t i)
    (h_large : ∀ (i : ι) (v : NumberField.InfinitePlace E), S.N ^ 2 < ‖Φ v (t i).val‖ ^ 2)
    (hn_mem_Y : ∀ i : ι, S.toPlaces T (n i) ∈ Y.val) {T₀ : Finset Eˣ}
    (hT₀ : ∀ x ∈ T₀, x.val ∈ ratIntegralOff T ∧ x⁻¹.val ∈ ratIntegralOff T)
    (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    (h_off : ∀ i : ι, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (σ i))) :
    let r : ℝ := S.normalizingConst kPred
    -- the heads at the infinite place `v` and at `T`
    let x (v : NumberField.InfinitePlace E) (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) (a : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t a).val)
    let y (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) : ℕ → (LocProd T)ˣ :=
      Units.map (ratToPlaces T) ∘ padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) t
    r ^ 2 * ∑ i : ι, ‖∑ p : Fin 𝔰.ϱ → T₀, S.cosetAmplitude .cut (c i) (S.reduction (n i)) (c' i)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) (t i)) *
          σ i)‖ ^ 2 ≤
      (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst *
        (∑ t' ∈ univ.image t, ∑ p : Fin 𝔰.ϱ → T₀, ∑ q : Fin 𝔰.ϱ → T₀,
          (∏ v : NumberField.InfinitePlace E,
            (S.besselSystem v).bandLimit 𝔰.n (x v p t') (x v q t')) *
          (G.lastEntryDensity (S.piNAt T) Y (y p t') (y q t') / Y.massRatio.toReal)).re := by
  -- Group the classes by their last entry, and apply
  -- `sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity` to each group. `R t` is the product of
  -- the top kernels at the infinite places, and `ρ t p` that of the scalars in
  -- `normalizedOrbitalIntegral`.
  intro r x y
  let R (t : Eˣ) : Matrix (Fin 𝔰.ϱ → T₀) (Fin 𝔰.ϱ → T₀) ℂ :=
    fun p q ↦ ∏ v, (S.besselSystem v).bandLimit 𝔰.n (x v p t) (x v q t)
  let ρ (t : Eˣ) (p : Fin 𝔰.ϱ → T₀) : ℝ :=
    ∏ v, √𝔰.openCellConst * √(‖(x v p t 𝔰.ϱ).val‖ ^ 2 - 1) ^ (𝔰.k - 1) /
      card (S.besselSystem v).Index *
      ∏ a ∈ range 𝔰.ϱ, ‖(x v p t a).val‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))
  have h_weight (i : ι) (p : Fin 𝔰.ϱ → T₀) :
      ρ (t i) p * (G.headDensity 𝔰.ϱ (y p (t i)) 1).toReal =
        r * √((∏ v, (‖Φ v (t i).val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) :=
    gramScalar_mul_headDensity hk hT₀ (h_large i) p
  -- the classes with the last entry of `i`
  have h_top (i : ι) :
      ∑ j : {j // t j = t i}, r ^ 2 * ‖∑ p : Fin 𝔰.ϱ → T₀, S.cosetAmplitude .cut (c j)
          (S.reduction (n j)) (c' j)
          (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).val) (t i)) * σ j)‖ ^ 2 ≤
        (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst * (∑ p, ∑ q, R (t i) p q *
          (G.lastEntryDensity (S.piNAt T) Y (y p (t i)) (y q (t i)) / Y.massRatio.toReal)).re := by
    have h_fiber_tail (j : {j // t j = t i}) : S.frameProducts (σ j) 𝔰.top 𝔰.top = t i := by
      rw [h_tail j, j.property]
    have h_fiber_gram (j : {j // t j = t i}) : R (t i) = .gram ℂ fun p : Fin 𝔰.ϱ → T₀ ↦
        ρ (t i) p • besselOrbitalIntegral volume (fun g ↦ .toLp 2 (S.besselFn .cut g))
          (S.ratToInf
            (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).val) (t i)) * σ j)) :=
      prod_bandLimit_eq_gram (hσ j) (h_fiber_tail j)
    have h_head (p : Fin 𝔰.ϱ → T₀) (l : ℕ) (hl : l < 𝔰.ϱ) :
        (padTuple (fun a ↦ (p a).val) (t i) l).val ∈ ratIntegralOff T ∧
          (padTuple (fun a ↦ (p a).val) (t i) l)⁻¹.val ∈ ratIntegralOff T := by
      simpa only [padTuple, dite_eq_left hl] using hT₀ _ (p ⟨l, hl⟩).property
    exact hG.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity hT_basis hT_N
      (j := {j // t j = t i})
      (c := (c ·)) (c' := (c' ·)) (h_inj.comp Subtype.val_injective) (hσ ·) h_fiber_tail (h_large i)
      (hn_mem_Y ·) (h_off ·) ⟨i, rfl⟩ (fun p ↦ by simp [padTuple]) h_head h_fiber_gram (h_weight i)
  rw [mul_sum, ← sum_fiberwise_of_maps_to fun i ↦ mem_image_of_mem t, re_sum, mul_sum]
  refine sum_le_sum (forall_mem_image.2 fun i _ ↦ ?_)
  rw [sum_subtype (p := fun j : ι ↦ t j = t i) (F := inferInstance) _ (by simp)]
  simpa only [Subtype.prop (p := (t · = t i))] using h_top i

/-- Let `S` be an admissible filling of shape `𝔰` over a CM field `E` with Weil data, with size
parameter `b = S.b`, and `Sg` a set of chosen places above the first level prime p₀
(`S.chosenPlaces 0`). Take finitely many distinct classes `(c i, S.reduction (n i), c' i, σ i)`
whose last entries `t i` lie in a finite set `T₀` of units off `T`, whose positions are integral off
`T` and whose reductions are in `S.fixer Sg D`. Here `σ i` is in the floor group, its last frame
product is `t i`, and ‖t i‖² > N² at every infinite place; `1 / M`, `1 / N`, the lattice basis and
its inverse are integral off `T`. The double coset sum `S.cosetAmplitude .cut c s c' γ` adds the
amplitudes of the cut Bessel function at `u γ u'⁻¹` over the rational unipotent `u`, `u'` for which
this element lies over `(c, s, c')`. These sums, added over the heads with entries in `T₀`, have
total square norm at most `(1 + b⁻⁴) b^(-6 𝔰.k |Sg|)` times
`mainSecondMoment = sourceDim² / (besselDegree * mass)` times `unipotentCovolume²`. -/
lemma sum_norm_sum_cosetAmplitude_sq_le [S.IsAdmissible] (Sg : Finset (S.chosenPlaces 0))
    (D : ∀ w : S.chosenPlaces 0, S.FrameVector w) {ι : Type} [Fintype ι] {c c' : ι → S.Classes}
    {σ : ι → S.G E} {n : ι → S.latticeStabilizer} {t : ι → Eˣ}
    (h_inj : (fun i : ι ↦ (c i, c' i, S.reduction (n i), σ i)).Injective)
    (hσ : ∀ i : ι, σ i ∈ Shape.Form.floorGroup 𝔰.ϱ)
    (h_tail : ∀ i : ι, S.frameProducts (σ i) 𝔰.top 𝔰.top = t i)
    (h_large : ∀ (i : ι) (v : NumberField.InfinitePlace E), S.N ^ 2 < ‖Φ v (t i).val‖ ^ 2)
    (hn_fix : ∀ i : ι, S.reduction (n i) ∈ S.fixer Sg D)
    {T₀ : Finset Eˣ} (ht : ∀ i : ι, t i ∈ T₀) {T : Finset (FinPlace E)} [T.StarStable]
    (hT₀ : ∀ x ∈ T₀, x.val ∈ ratIntegralOff T ∧ x⁻¹.val ∈ ratIntegralOff T)
    [hT_M : Fact (S.ideleM⁻¹.val ∈ integralOff T)]
    (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    (h_off : ∀ i : ι, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (σ i))) :
    ∑ i : ι, ‖∑ p : Fin 𝔰.ϱ → T₀, S.cosetAmplitude .cut (c i) (S.reduction (n i)) (c' i)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) (t i)) *
          σ i)‖ ^ 2 ≤
      (1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg * S.mainSecondMoment *
        S.unipotentCovolume ^ 2 := by
  classical
  -- Siegel's step bounds the sum by the top densities, `sieve` bounds these, and
  -- `sieve_constant_le` evaluates the constant.
  obtain ⟨kPred, hk⟩ : ∃ kPred : ℕ, 𝔰.k = kPred + 1 := ⟨𝔰.k - 1, by grind [S.thousand_mul_le_k]⟩
  -- at `T`: a filling datum `G`, and a group `Y` that contains the components of the `n i` and
  -- whose normalised forms are a system for the sieve, with the density at the last entry as top
  -- form
  obtain ⟨P, G, hG⟩ := S.exists_isFillingData T
  obtain ⟨Y, hY_mem, hY_sys⟩ := hG.exists_intermediateGroup_sieveSystem Sg D
  -- the heads at the infinite place `v` and at `T`, and the weighted sum of the top densities
  let x (v : NumberField.InfinitePlace E) (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) (a : ℕ) : ℂˣ :=
    unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b ↦ (p b).val) t a).val)
  let y (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) : ℕ → (LocProd T)ˣ :=
    Units.map (ratToPlaces T) ∘ padTuple (fun a ↦ (p a).val) t
  let topSum : ℝ := (∑ t' ∈ univ.image t, ∑ p : Fin 𝔰.ϱ → T₀, ∑ q : Fin 𝔰.ϱ → T₀,
    (∏ v, (S.besselSystem v).bandLimit 𝔰.n (x v p t') (x v q t')) *
      (G.lastEntryDensity (S.piNAt T) Y (y p t') (y q t') / Y.massRatio.toReal)).re
  have h_siegel : S.normalizingConst kPred ^ 2 * ∑ i : ι, ‖∑ p : Fin 𝔰.ϱ → T₀,
      S.cosetAmplitude .cut (c i) (S.reduction (n i)) (c' i)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).val) (t i)) * σ i)‖ ^ 2 ≤
      (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst * topSum :=
    hG.mul_sum_norm_sum_cosetAmplitude_sq_le Y hk h_inj hσ h_tail h_large
      (fun i ↦ hY_mem (n i) (hn_fix i)) hT₀ hT_basis hT_N h_off
  have h_sieve : topSum ≤ (∏ i ∈ range 𝔰.n, S.poissonConst i) *
      ((∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
          ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg) +
        S.b ^ (2403 * 𝔰.n ^ 9 * Core.numInfPlaces E) * S.decayConst) := by
    have h_top_index : ¬𝔰.n ≤ 𝔰.ϱ := Nat.not_succ_le_self 𝔰.ϱ
    simpa only [ite_eq_right h_top_index] using
      S.sieve T hT₀ hT_M.out hY_sys (U := univ.image t) (image_subset_iff.2 fun i _ ↦ ht i)
  have h_coeff : 0 ≤ (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst := by
    unfold scaledSiegelConst siegelConst
    positivity
  have hSg : #Sg ≤ Core.numInfPlaces E := Sg.card_le_univ.trans_eq (S.card_chosenPlaces 0)
  refine le_of_mul_le_mul_left (h_siegel.trans ?_) (normalizingConst_sq_pos kPred)
  exact (mul_le_mul_of_nonneg_left h_sieve h_coeff).trans (sieve_constant_le hk hSg)

/-- Let `S` be an admissible filling of shape `𝔰` over a CM field `E` with Weil data, `Sg` a set of
chosen places above the first level prime p₀, and `D w` a nonzero vector of the span of the frame
modulo `w` or modulo its conjugate. On the left, `linkSecondMoment` sums the squared norms of the
class sums of the cut function over all links, pairs of classes, and reductions `s` that are open
and fix `D w` for `w ∈ Sg`. With `X` the isotropic span of `e₁, …, e_ϱ`, the link of a term `γ` is
the module of pairs of classes in `X^⊥/X` of `t` and `γ⁻¹ t`, for `t` orthogonal to `X` and `γ X`;
each class sum runs over the terms of one link. Only terms `γ` with
`termDisc γ = |Δ|² - N² |Δ'|² ≠ 0` enter, where `Δ` is the determinant and `Δ'` the leading minor of
size ϱ of the frame products of `γ`. The bound is `(1 + b⁻⁴) b^(-6 𝔰.k |Sg|)` times
`mainSecondMoment = sourceDim² / (besselDegree * mass)` times `unipotentCovolume²`. Here `b` is the
size parameter of `S`, `𝔰.k` is the rank of X₀, `mass` is the mass of the genus of the standard
Hermitian lattice of rank `𝔰.r`, and `unipotentCovolume` is an explicit number which, if `E`
contains a primitive 5040th root of unity, is the integral of the cutoff `S.classCutoff c` over the
real unipotent group, for every class `c` (`lintegral_classCutoff_eq_unipotentCovolume`). -/
theorem linkSecondMoment_isOpenElement_le [S.IsAdmissible] (Sg : Finset (S.chosenPlaces 0))
    (D : ∀ w : S.chosenPlaces 0, S.FrameVector w) :
    linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0}
      {s : S.ResidueGL | s ∈ S.fixer Sg D ∧ S.IsOpenElement s} ≤
      .ofReal ((1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg * S.mainSecondMoment *
        S.unipotentCovolume ^ 2) := by
  -- The left side is a sum of squared norms of blocks. It suffices to bound finite sums `F` of
  -- nonzero blocks; each is a finite sum of double coset sums over the tuples `p` of entries in
  -- `S.entrySet`. These entries are units off the set `T` of places, and the inverses of the level
  -- and of `N` are integral there.
  obtain ⟨T, _, hT₀, hT_M, hT_basis, hT_N⟩ := S.exists_places_integralOff S.entrySet
  simp_rw [linkSecondMoment, ← tsum_prod]
  refine (tsum_subtype_support _).ge.trans (CompleteLattice.summable.tsum_le_of_sum_le fun F ↦ ?_)
  -- a block `j` has two classes, a reduction and a link
  let block (j : F) : S.Classes × S.Classes × {s | s ∈ S.fixer Sg D ∧ S.IsOpenElement s} ×
      Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) := j.val.val
  let c (j : F) : S.Classes := (block j).fst
  let c' (j : F) : S.Classes := (block j).snd.fst
  let s (j : F) : S.ResidueGL := (block j).snd.snd.fst
  let Λ (j : F) : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) := (block j).snd.snd.snd
  let classSum (j : F) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
    S.amplitudeSum .cut (S.termsOfLink (Λ j)) (c j) (s j) (c' j)
  have hs (j : F) : s j ∈ S.fixer Sg D ∧ S.IsOpenElement (s j) := (block j).snd.snd.fst.prop
  have h_ne (j : F) : classSum j ≠ 0 := by simpa using show ‖classSum j‖ₑ ^ 2 ≠ 0 from j.val.prop
  have h_class (j : F) : ∃ (t : Eˣ) (σ : S.G E) (n : S.latticeStabilizer),
      S.NamesLink T (c j) (s j) (c' j) (Λ j) t σ n ∧
      classSum j = ∑ p : Fin 𝔰.ϱ → S.entrySet, S.cosetAmplitude .cut (c j) (s j) (c' j)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).val) t) * σ) :=
    exists_amplitudeSum_eq_sum_cosetAmplitude hT₀ (h_ne j)
      fun _ ↦ (hs j).right.leadingMinor_ne_zero
  choose t σ n h_names h_sum using h_class
  have h_red (j : F) : S.reduction (n j) = s j := (h_names j).reduction_eq
  -- distinct blocks give distinct tuples `(c j, c' j, S.reduction (n j), σ j)`: `S.reduction (n j)`
  -- is the reduction of `j` and `σ j` determines its link
  have h_inj : (fun j ↦ (c j, c' j, S.reduction (n j), σ j)).Injective := by
    intro i j h
    obtain ⟨hc, hc', h_s, h_eq⟩ : c i = c j ∧ c' i = c' j ∧ s i = s j ∧ σ i = σ j := by
      simpa [h_red] using h
    have hΛ : Λ i = Λ j := by rw [(h_names i).link_eq, (h_names j).link_eq, h_eq]
    exact Subtype.ext (Subtype.ext (Prod.ext hc (Prod.ext hc' (Prod.ext (Subtype.ext h_s) hΛ))))
  have h_bound : ∑ j : F, ‖classSum j‖ ^ 2 ≤
      (1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg * S.mainSecondMoment *
        S.unipotentCovolume ^ 2 := by
    simpa only [h_sum, ← h_red] using sum_norm_sum_cosetAmplitude_sq_le Sg D h_inj
      (fun j ↦ (h_names j).mem_floorGroup)
      (fun j ↦ (h_names j).frameProducts_top_top) (fun j ↦ (h_names j).sq_lt_norm_sq)
      (by simpa only [h_red] using fun j ↦ (hs j).left)
      (fun j ↦ (h_names j).mem_entrySet) hT₀ hT_basis hT_N fun j ↦ (h_names j).isIntegralOff
  refine le_of_eq_of_le ?_ (ENNReal.ofReal_le_ofReal h_bound)
  simp only [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ sq_nonneg ‖classSum j‖,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  exact (F.sum_coe_sort _).symm

end New.Filling

end MainTermEstimate
