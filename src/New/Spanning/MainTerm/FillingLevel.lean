module

public import Aesop.BuiltinRules
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Topology.Sheaves.Presheaf
public import Lib.General.NumberTheory.EmbeddingsAndDifferent
import Lib.Adelic.Adeles.StrongApproximation
import Lib.ClassField.HeckeL.EulerProduct
import Lib.General.Analysis.PackingAndSobolev
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import TauCeti.NumberTheory.NumberField.Countable
public import New.Spanning.Unfolding.BesselLevelStructure
public import Lib.Adelic.Adeles.SemilocalProducts
import Lib.Cohomology.Etale.Basic
import Lib.Shimura.ComplexTheta.AppellHumbertData
import New.Spanning.RemainingTerms.Box
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Finset.Functor
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import New.Spanning.Frames.StandardLevel
import Lib.Adelic.Reduction.DefiniteClassSums

section
section
/-!
# Sums over frequencies

The frequencies are the elements `ν` of a totally complex number field `E`. If `E` has `f` infinite
places, the sum of `∏_v [ν]_v ^ (-3)` over any finite subset of `E` is at most `C ^ f` with
`C = 64 * 38 * e ^ 4`. At an infinite place `[ν]_v` is `(max 1 |ν|_v) ^ 2`, with `|ν|_v` the usual
absolute value, and the finite places together give the norm of the denominator of `ν`. The numbers
with a given denominator `𝔟` lie in `N 𝔟` cosets of the ring of integers, each coset is counted by
small squares, and the sum over `𝔟` is at most the value at `2` of the Dedekind zeta function.

Notions from other files:
* `Φ v`: the chosen complex embedding of `E` that induces the infinite place `v`
  (`PlaceEmbedding E`).
-/

@[expose] public section

open NumberField Finset

noncomputable section

namespace New

variable {E : Type} [Field E] [NumberField E]

/-- The denominator of `ν`: the ideal of the integers `a` such that `a ν` is integral. -/
def denominator (ν : E) : Ideal (𝓞 E) where
  carrier := {a : 𝓞 E | IsIntegral ℤ (algebraMap (𝓞 E) E a * ν)}
  zero_mem' := by simpa using isIntegral_zero
  add_mem' ha hb := by simpa [add_mul] using IsIntegral.add ha hb
  smul_mem' c a ha := by simpa [mul_assoc] using IsIntegral.mul c.isIntegral_coe ha

omit [NumberField E] in
lemma mem_denominator {ν : E} {a : 𝓞 E} :
    a ∈ denominator ν ↔ IsIntegral ℤ (algebraMap (𝓞 E) E a * ν) :=
  Iff.rfl

lemma denominator_ne_bot (ν : E) : denominator ν ≠ ⊥ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ν
  refine (Submodule.ne_bot_iff _).2 ⟨b, ?_, nonZeroDivisors.ne_zero hb⟩
  simpa [mem_denominator, mul_div_cancel₀, nonZeroDivisors.ne_zero hb] using a.isIntegral_coe

/-- Suppose that `(a) = 𝔟 𝔠` with `𝔟 ≠ 0` and that `r ν` is integral for all `r ∈ 𝔟`, that is,
`𝔟 ≤ denominator ν`. Then `a ν` is an integer in `𝔠`. -/
lemma exists_mem_algebraMap_eq_mul {a : 𝓞 E} {𝔟 𝔠 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥)
    (h𝔠 : Ideal.span {a} = 𝔟 * 𝔠) {ν : E} (hν : 𝔟 ≤ denominator ν) :
    ∃ x : 𝔠, algebraMap (𝓞 E) E (x : 𝓞 E) = algebraMap (𝓞 E) E a * ν := by
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, algebraMap (𝓞 E) E x = algebraMap (𝓞 E) E a * ν :=
    ⟨⟨_, mem_denominator.1 (hν (Ideal.dvd_span_singleton.1 ⟨𝔠, h𝔠⟩))⟩, rfl⟩
  refine ⟨⟨x, Ideal.dvd_span_singleton.1 <| (mul_dvd_mul_iff_left h𝔟).1 <|
    Ideal.dvd_iff_le.2 (h𝔠 ▸ mul_comm _ 𝔟 ▸ Ideal.span_singleton_mul_le_iff.2 fun r hr => ?_)⟩,
    hx⟩
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = algebraMap (𝓞 E) E r * ν :=
    ⟨⟨_, mem_denominator.1 (hν hr)⟩, rfl⟩
  exact Ideal.mem_span_singleton'.2 ⟨y, RingOfIntegers.coe_injective <| by
    simp only [map_mul, hx, hy, mul_left_comm, mul_comm]⟩

/-- For a nonzero ideal `𝔟`, the numbers `ν` whose denominator (the ideal of the integers `a`
with `a ν` integral) contains `𝔟` can be given `N 𝔟` labels so that two numbers with the same
label differ by an algebraic integer. -/
lemma exists_coset_label {𝔟 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∃ label : E → Fin (Ideal.absNorm 𝔟), ∀ ν ν' : E,
      𝔟 ≤ denominator ν → 𝔟 ≤ denominator ν' → label ν = label ν' → IsIntegral ℤ (ν - ν') := by
  -- Write `(a) = 𝔟 𝔠` with `a ≠ 0`. Multiplication by `a` maps these numbers into `𝔠` and the
  -- integers onto `(a)`, and `𝔠 / (a)` has `N 𝔟` elements.
  obtain ⟨a, ha, ha_ne⟩ := (Submodule.ne_bot_iff 𝔟).1 h𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {a} := Ideal.dvd_span_singleton.2 ha
  have h_mul (ν : E) (hν : 𝔟 ≤ denominator ν) :
      ∃ x : 𝔠, algebraMap (𝓞 E) E (x : 𝓞 E) = algebraMap (𝓞 E) E a * ν :=
    exists_mem_algebraMap_eq_mul h𝔟 h𝔠 hν
  choose! x hx using h_mul
  let A : AddSubgroup 𝔠 := (Ideal.span {a}).toAddSubgroup.addSubgroupOf 𝔠.toAddSubgroup
  have h_index : A.index = Ideal.absNorm 𝔟 := by
    -- the norm of an ideal is the index of its additive group
    have h_tower : A.index * Ideal.absNorm 𝔠 = Ideal.absNorm (Ideal.span {a}) := by
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
      exact AddSubgroup.relIndex_mul_index (h𝔠.trans_le Ideal.mul_le_right)
    have h𝔠_ne : 𝔠 ≠ ⊥ := fun h_bot ↦ ha_ne (by simpa [h_bot] using h𝔠)
    simpa [h𝔠, Ideal.absNorm_eq_zero_iff, h𝔠_ne] using h_tower
  have : Finite (𝔠 ⧸ A) := AddSubgroup.index_ne_zero_iff_finite.1 <| by
    rwa [h_index, Ne, Ideal.absNorm_eq_zero_iff]
  let e : 𝔠 ⧸ A ≃ Fin (Ideal.absNorm 𝔟) := Finite.equivFinOfCardEq h_index
  refine ⟨fun ν : E ↦ e (QuotientAddGroup.mk (x ν)), fun ν ν' hν hν' h_label ↦ ?_⟩
  have h_mem : x ν - x ν' ∈ A := QuotientAddGroup.eq_iff_sub_mem.1 (e.injective h_label)
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, t * a = x ν - x ν' :=
    Ideal.mem_span_singleton'.1 (AddSubgroup.mem_addSubgroupOf.1 h_mem)
  have h_eq : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a * (ν - ν') := by
    rw [mul_comm, ← map_mul, ht, map_sub, hx ν hν, hx ν' hν', mul_sub]
  rw [← mul_left_cancel₀ (by simpa using ha_ne) h_eq]
  exact t.isIntegral_coe

/-- The sum of `Ideal.absNorm 𝔟 ^ (-2)` over a finite set `s` of ideals of the ring of integers of
`E` is at most `exp (2 [E : ℚ])`, where `[E : ℚ] = Module.finrank ℚ E`: it is at most the value at
`2` of the Euler product with all coefficients equal to `1`, that is `ζ_E(2)`. -/
lemma sum_absNorm_inv_sq_le (s : Finset (Ideal (𝓞 E))) :
    ∑ 𝔟 ∈ s, (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 2 ≤ Real.exp (2 * Module.finrank ℚ E) := by
  let ζ : ℂ := eulerProd (fun _ : FinPlace E ↦ 1) 2
  have h_sum : HasSum (fun 𝔟 : Ideal (𝓞 E) ↦ (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 2) ζ.re := by
    have h_euler : HasSum (fun 𝔟 : Ideal (𝓞 E) ↦ (Ideal.absNorm 𝔟 : ℂ) ^ (-2 : ℂ)) ζ := by
      simpa using hasSum_eulerProd (K := E) (s := 2) 1 (by simp) (by simp)
    refine (Complex.hasSum_re h_euler).congr_fun fun 𝔟 ↦ ?_
    simp [Complex.cpow_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  have h_log : Real.log ‖ζ‖ ≤ 2 * Module.finrank ℚ E := by
    obtain ⟨-, h_abs⟩ : ζ ≠ 0 ∧ |Real.log ‖ζ‖| ≤ 2 * Module.finrank ℚ E * 2 ^ (2 - 2 : ℝ) :=
      eulerProd_ne_zero_and_abs_log_norm_le (s := 2) (by simp) le_rfl le_rfl
    simpa using le_of_abs_le h_abs
  calc _ ≤ ζ.re := sum_le_hasSum s (fun _ _ ↦ by positivity) h_sum
    _ ≤ ‖ζ‖ := Complex.re_le_norm ζ
    _ ≤ _ := Real.le_exp_of_log_le h_log

/-- The lower left corner `m.1 / 2 + (m.2 / 2) * I` of the square of side `1 / 2` with index
`m`. -/
def squareCorner (m : ℤ × ℤ) : ℂ := ⟨m.1 / 2, m.2 / 2⟩

/-- The index `(⌊2 * z.re⌋, ⌊2 * z.im⌋)` of the square of side `1 / 2` that contains `z`. The
square with index `(a, b)` is `[a / 2, (a + 1) / 2) × [b / 2, (b + 1) / 2)`. -/
def squareIndex (z : ℂ) : ℤ × ℤ := (⌊2 * z.re⌋, ⌊2 * z.im⌋)

lemma norm_lt_one_of_abs_lt {z : ℂ} (h_re : |z.re| < 1 / 2) (h_im : |z.im| < 1 / 2) : ‖z‖ < 1 := by
  linarith [Complex.norm_le_abs_re_add_abs_im z]

/-- If `z` and `w` have the same index `squareIndex z = (⌊2 * z.re⌋, ⌊2 * z.im⌋)`, that is, if they
lie in the same half-open square `[a / 2, (a + 1) / 2) × [b / 2, (b + 1) / 2)` with `a` and `b`
integers, then their distance is less than one. -/
lemma norm_sub_lt_one_of_squareIndex_eq {z w : ℂ} (h_index : squareIndex z = squareIndex w) :
    ‖z - w‖ < 1 := by
  obtain ⟨h_re, h_im⟩ : ⌊2 * z.re⌋ = ⌊2 * w.re⌋ ∧ ⌊2 * z.im⌋ = ⌊2 * w.im⌋ := by
    simpa [squareIndex] using h_index
  have h_half {a b : ℝ} (h_floor : ⌊2 * a⌋ = ⌊2 * b⌋) : |a - b| < 1 / 2 := by
    have h_double : |2 * a - 2 * b| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor h_floor
    rw [← mul_sub, abs_mul, abs_two] at h_double
    linarith
  exact norm_lt_one_of_abs_lt (by simpa using h_half h_re) (by simpa using h_half h_im)

/-- The corner `squareCorner m = m.1 / 2 + (m.2 / 2) * I` lies in the square with index `m`, where
`squareIndex z = (⌊2 * z.re⌋, ⌊2 * z.im⌋)`. -/
lemma squareIndex_squareCorner (m : ℤ × ℤ) : squareIndex (squareCorner m) = m := by
  simp [squareIndex, squareCorner, mul_div_cancel₀]

/-- The weight `(max 1 ‖z‖)⁻¹ ^ 6` of a complex number `z` is at most `64` times the weight of the
lower left corner of the square of side `1 / 2` that contains `z`. -/
lemma weight_le_weight_corner (z : ℂ) :
    (max 1 ‖z‖)⁻¹ ^ 6 ≤ 64 * (max 1 ‖squareCorner (squareIndex z)‖)⁻¹ ^ 6 := by
  have h_near : ‖squareCorner (squareIndex z) - z‖ < 1 :=
    norm_sub_lt_one_of_squareIndex_eq (squareIndex_squareCorner _)
  have h_le : max 1 ‖squareCorner (squareIndex z)‖ ≤ 2 * max 1 ‖z‖ := by
    have h_sub : ‖squareCorner (squareIndex z)‖ - ‖z‖ ≤ ‖squareCorner (squareIndex z) - z‖ :=
      norm_sub_norm_le _ _
    have h_one : 1 ≤ max 1 ‖z‖ := le_max_left 1 ‖z‖
    have h_norm : ‖z‖ ≤ max 1 ‖z‖ := le_max_right 1 ‖z‖
    exact max_le (by linarith) (by linarith)
  calc _ = 64 * (2 * max 1 ‖z‖)⁻¹ ^ 6 := by ring
    _ ≤ _ := by gcongr

/-- For distinct index pairs `m ≠ m'` in `ℤ × ℤ`, the grid corners
`squareCorner m = m.1 / 2 + (m.2 / 2) * I` and `squareCorner m'` have distance at least `1 / 2`. -/
lemma pairwise_half_le_norm_squareCorner_sub :
    Pairwise fun m m' : ℤ × ℤ ↦ 1 / 2 ≤ ‖squareCorner m - squareCorner m'‖ := by
  intro m m' h_ne
  by_contra! h_lt
  have h_eq {a b : ℤ} (h_half : |(a : ℝ) / 2 - b / 2| < 1 / 2) : a = b := by
    rw [← sub_div, abs_div, abs_two, div_lt_div_iff_of_pos_right two_pos] at h_half
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 (mod_cast h_half))
  refine h_ne (Prod.ext (h_eq ?_) (h_eq ?_))
  · simpa [squareCorner] using (Complex.abs_re_le_norm _).trans_lt h_lt
  · simpa [squareCorner] using (Complex.abs_im_le_norm _).trans_lt h_lt

/-- Over any finitely many indices `m`, the weights `(max 1 ‖z‖)⁻¹ ^ 6` at the grid points
`z = squareCorner m = m.1 / 2 + (m.2 / 2) * I` add up to at most `38`. -/
lemma sum_weight_corner_le (s : Finset (ℤ × ℤ)) :
    ∑ m ∈ s, (max 1 ‖squareCorner m‖)⁻¹ ^ 6 ≤ 38 := by
  -- Distinct corners have distance at least `1 / 2`, so the packing bound for separated points
  -- applies to the sum over all corners.
  let u (m : ℤ × ℤ) : ℝ := max 1 ‖squareCorner m‖
  obtain ⟨h_summable, h_tsum⟩ : Summable (fun m : ℤ × ℤ ↦ u m ^ (-6 : ℝ)) ∧
      ∑' m : ℤ × ℤ, u m ^ (-6 : ℝ) ≤ (1 + 2 * 1 / (1 / 2)) ^ Module.finrank ℝ ℂ * (3 / 2) :=
    tsum_le_of_separated (hf := pairwise_half_le_norm_squareCorner_sub) (hm := one_half_pos)
      (hR := zero_le_one) (hu_one := by simp [u]) (hu := by simp [u]) (hA := by norm_num)
      (hc := by norm_num)
  calc _ = ∑ m ∈ s, u m ^ (-6 : ℝ) := by simp [u, Real.rpow_neg_ofNat]
    _ ≤ ∑' m : ℤ × ℤ, u m ^ (-6 : ℝ) := h_summable.sum_le_tsum s fun _ _ ↦ by positivity
    _ ≤ (1 + 2 * 1 / (1 / 2)) ^ Module.finrank ℝ ℂ * (3 / 2) := h_tsum
    _ ≤ 38 := by norm_num

variable [PlaceEmbedding E]

/-- Let `X` be a finite subset of a totally complex field `E` any two elements of which differ by
an algebraic integer. Then the sum over `ν ∈ X` of the archimedean weights
`∏_v (max 1 ‖Φ v ν‖)⁻¹ ^ 6` is at most `(64 * 38) ^ f`, where `Φ v` is the chosen embedding at `v`
and `f` is the number of infinite places. -/
lemma sum_coset_weight_le [IsTotallyComplex E] {X : Finset E}
    (hX : ∀ ν ∈ X, ∀ ν' ∈ X, IsIntegral ℤ (ν - ν')) :
    ∑ ν ∈ X, ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 ≤ (64 * 38) ^ Core.numInfPlaces E := by
  -- A product of squares of side `1 / 2` holds at most one point of `X`, since the product of the
  -- absolute values of a nonzero algebraic integer is at least one. So the sum is at most a
  -- product of sums over squares.
  let cell (ν : E) (v : InfinitePlace E) : ℤ × ℤ := squareIndex (Φ v ν)
  let w (m : ℤ × ℤ) : ℝ := 64 * (max 1 ‖squareCorner m‖)⁻¹ ^ 6
  have h_inj : Set.InjOn cell X := by
    intro ν hν ν' hν' h_cell
    by_contra h_ne
    have h_lt : ∏ v : InfinitePlace E, ‖Φ v (ν - ν')‖ < ∏ _ : InfinitePlace E, 1 :=
      prod_lt_prod_of_nonempty₀ (fun v _ ↦ by simpa [sub_ne_zero] using (Φ v).injective.ne h_ne)
        (fun v _ ↦ by simpa using norm_sub_lt_one_of_squareIndex_eq (congrFun h_cell v))
        univ_nonempty
    exact (one_le_prod_norm_Φ (hX ν hν ν' hν') (sub_ne_zero.2 h_ne)).not_gt (by simpa using h_lt)
  let cells (v : InfinitePlace E) : Finset (ℤ × ℤ) := X.image fun ν : E ↦ cell ν v
  calc
    _ ≤ ∑ ν ∈ X, ∏ v : InfinitePlace E, w (cell ν v) := by grw [weight_le_weight_corner]
    _ = ∑ c ∈ X.image cell, ∏ v : InfinitePlace E, w (c v) := by rw [sum_image h_inj]
    _ ≤ ∑ c ∈ Fintype.piFinset cells, ∏ v : InfinitePlace E, w (c v) := by
      gcongr
      exact image_subset_iff.2 fun ν hν ↦ Fintype.mem_piFinset.2 fun v ↦ mem_image_of_mem _ hν
    _ = ∏ v : InfinitePlace E, ∑ m ∈ cells v, w m := (prod_univ_sum cells fun _ ↦ w).symm
    _ ≤ ∏ _ : InfinitePlace E, (64 * 38 : ℝ) := by
      gcongr with v
      grw [← mul_sum, sum_weight_corner_le]
    _ = _ := by simp

/-- Let `X` be a finite subset of a totally complex field `E`. The archimedean weights
`∏_v (max 1 ‖Φ v ν‖)⁻¹ ^ 6` of those `ν ∈ X` with a given nonzero denominator `𝔟` add up to at most
`Ideal.absNorm 𝔟 * (64 * 38) ^ Core.numInfPlaces E`, as these `ν` lie in at most `Ideal.absNorm 𝔟`
cosets of the integers. -/
lemma sum_weight_filter_denominator_eq_le [IsTotallyComplex E] [DecidableEq (Ideal (𝓞 E))]
    (X : Finset E) {𝔟 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∑ ν ∈ X with denominator ν = 𝔟, ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 ≤
      Ideal.absNorm 𝔟 * (64 * 38) ^ Core.numInfPlaces E := by
  obtain ⟨label, h_label⟩ : ∃ label : E → Fin (Ideal.absNorm 𝔟), ∀ ν ν' : E,
      𝔟 ≤ denominator ν → 𝔟 ≤ denominator ν' → label ν = label ν' → IsIntegral ℤ (ν - ν') :=
    exists_coset_label h𝔟
  calc
    _ = ∑ k : Fin (Ideal.absNorm 𝔟), ∑ ν ∈ {ν ∈ X | denominator ν = 𝔟} with label ν = k,
          ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 := by rw [sum_fiberwise]
    _ ≤ ∑ _ : Fin (Ideal.absNorm 𝔟), (64 * 38 : ℝ) ^ Core.numInfPlaces E := by
      -- numbers with denominator `𝔟` and the same label differ by an integer
      refine sum_le_sum fun k _ ↦ sum_coset_weight_le fun ν hν ν' hν' ↦ ?_
      simp only [mem_filter] at hν hν'
      obtain ⟨⟨-, h_den⟩, h_class⟩ := hν
      obtain ⟨⟨-, h_den'⟩, h_class'⟩ := hν'
      exact h_label ν ν' h_den.ge h_den'.ge (h_class.trans h_class'.symm)
    _ = _ := by simp

/-- Let `E` be a totally complex number field with `f = Core.numInfPlaces E` infinite places. For a
finite set `X ⊂ E`, the sum of `∏_v [ν]_v ^ (-3)` over `ν ∈ X` is at most
`(64 * 38 * e ^ 4) ^ f`. -/
theorem sum_height_inv_cube_le [IsTotallyComplex E] (X : Finset E) :
    ∑ ν ∈ X, (∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6) *
      (Ideal.absNorm (denominator ν) : ℝ)⁻¹ ^ 3 ≤
      (64 * 38 * Real.exp 4) ^ Core.numInfPlaces E := by
  -- Group the numbers by denominator. Those with denominator `𝔟` give at most `N 𝔟` sums over
  -- cosets, and what remains is the sum of `N 𝔟 ^ (-2)`.
  calc
    _ = ∑ 𝔟 ∈ X.image denominator, (∑ ν ∈ X with denominator ν = 𝔟,
          ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6) * (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 3 := by
      rw [← sum_fiberwise_of_maps_to fun ν hν ↦ mem_image_of_mem denominator hν]
      simp_rw [sum_mul]
      exact sum_congr rfl fun 𝔟 _ ↦ sum_congr rfl fun ν hν ↦ by rw [(mem_filter.1 hν).2]
    _ ≤ ∑ 𝔟 ∈ X.image denominator,
          (64 * 38) ^ Core.numInfPlaces E * (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 2 := by
      refine sum_le_sum (forall_mem_image.2 fun ν _ ↦ ?_)
      grw [sum_weight_filter_denominator_eq_le X (denominator_ne_bot ν)]
      exact le_of_eq (by field_simp)
    _ ≤ (64 * 38) ^ Core.numInfPlaces E * Real.exp (2 * Module.finrank ℚ E) := by
      grw [← mul_sum, sum_absNorm_inv_sq_le]
    _ = _ := by
      have h_rank : (2 * Module.finrank ℚ E : ℝ) = Core.numInfPlaces E * 4 := by
        rw [finrank_eq_two_mul_card_infinitePlace]
        push_cast
        ring
      rw [h_rank, Real.exp_natCast_mul, ← mul_pow]

end New

end
end
end

/-!
# One-sided Poisson summation, sums over frequencies, and the sieve over all places

The sieve over the infinite places of the CM field `E` and a finite set `T` of finite places, which
bounds the main term.

* `New.Filling.charOnPlaces`, `New.Filling.globalChar`: the character of the product of the
  completions at `T`, and its product with the characters at the infinite places.
* `New.Filling.sum_ratPoint_le_mul_add_integral_of_fourier_le`: one-sided Poisson summation over the
  infinite places and `T`, at rational points integral off `T`.
* `New.Filling.entryDensity`, `New.Filling.densitySum`: the sum of densities at a common next entry,
  and the sums of densities in which the first `i` entries are summed over `A`.
* `New.Filling.densitySum_succ_le_mul_densitySum_add`: each sum of densities is bounded by the one
  before plus an error, up to the constant of Poisson summation (`New.Filling.poissonConst`).
* `New.Filling.densitySum_le`: the bound after all entries are removed in turn.
* `New.Filling.sieve`: the sieve for the product of one system for each infinite place and one
  system at `T`, read at rational points (`New.Filling.ratPoint`).

Conventions: `𝔰.k` and `𝔰.n = 𝔰.ϱ + 1` are parameters of the shape `𝔰`; in
`New.Filling.frequency_term_le` and `New.Filling.sum_frequencies_le`, `k` is any natural number.
`Φ v` is the chosen embedding of `E` at the infinite place `v`.

Notions from other files:
* `New.Filling`: the data `S`, among them the size parameter `b = S.b`, the level `M = S.M`, the
  prime `N = S.N` and a generator `ϖ = S.deltaE` of the different of `E`.
* `New.Filling.IsAdmissible`: the standing hypotheses on `S`, among them `1 ≤ |S.realM v| ≤ b ^ 23`
  and `N ≤ b ^ (60 n)`.
* `New.ψf E`, written `ψ_f`: the character of the finite adeles with `ψ_f(x) = exp (2πi Tr a)` for
  any `a ∈ E` with `x - a` integral. `New.stdAddChar E` is the standard character of the adeles, and
  `New.Filling.selfDualChar` is `x ↦ ψ_f(-x / ϖ)`.
* `New.LocProd T`: the product of the completions at `T`, with integers `New.SemilocalField.O`;
  `New.evalPlaces T` and `New.ratToPlaces T` map the finite adeles and `E` to it.
* `New.integralOff T`, `New.Filling.ratIntegralOff T`: the finite adeles and the elements of `E`
  (the `T`-integers) that are integral at every finite place outside `T`.
* `New.genIndex a`, `New.denomIndex O a`: the generalised index `[O : a O]` and the denominator
  `[O : O ∩ a⁻¹ O]`.
* `New.SieveSystem`: the axioms of the sieve for a family of forms `J i` on pairs of heads, at a
  place or a product of places.

## Relation to the literature

A system of positive kernels, of one kind at archimedean and finite places, has each kernel the
integral of the next over a common last entry. Systems multiply over places, and one-sided Poisson
summation, entry by entry, bounds the sum over rational points by the mass times a factor near 1, up
to the constants of summation and a small error, as the main term of the second moment requires.
Inductive Fourier transforms of Kloosterman integrals and spectral large sieves losing a constant or
X^ε are known in the literature. Related work: Jacquet, Smooth transfer of Kloosterman integrals,
2003; Jacquet, Kloosterman identities over a quadratic extension, 2004; Blomer–Buttcane, Global
decomposition of GL(3) Kloosterman sums and the spectral large sieve, 2015; Deshouillers–Iwaniec,
Kloosterman sums and Fourier coefficients of cusp forms, 1982.
-/

@[expose] public section

namespace New.Filling

open NumberField ENNReal Finset Fintype MeasureTheory Measure Real AddSubgroup Matrix ComplexOrder
  SemilocalField Complex

/-- The character `S.selfDualChar` is `x ↦ ψ_f(-x / ϖ)`, where `ψ_f = ψf E` is the standard
character of the finite adeles and `ϖ = S.deltaE` generates the different of `E`. -/
lemma selfDualChar_apply {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
    (x : 𝔸f E) : S.selfDualChar x = ψf E (algebraMap E (𝔸f E) (-(S.deltaE : E)⁻¹) * x) := rfl

variable {E : Type} [Field E] [CMType E] [WeilData E] {𝔰 : Shape} (S : Filling E 𝔰)
  (T : Finset (FinPlace E)) [T.StarStable]

/-- The character `S.selfDualChar` of the finite adeles, `x ↦ ψ_f(-x / ϖ)`, read on the product of
the completions at `T` through extension by zero (`adeleOfLocal`). Here `ψ_f = ψf E` is the standard
character of the finite adeles, and `ϖ = S.deltaE` generates the different of `E`. -/
noncomputable def charOnPlaces : AddChar (LocProd T) ℂ :=
  S.selfDualChar.compAddMonoidHom (adeleOfLocal T)

section

omit [WeilData E] [T.StarStable]

/-- At a finite adele that is integral off `T`, the character `S.selfDualChar` depends only on the
components at `T`: it equals `S.charOnPlaces T` there. -/
lemma charOnPlaces_evalPlaces {x : 𝔸f E} (hx : x ∈ integralOff T) :
    S.charOnPlaces T (evalPlaces T x) = S.selfDualChar x := by
  refine (eq_of_div_eq_one ?_).symm
  rw [charOnPlaces, AddChar.compAddMonoidHom_apply, ← S.selfDualChar.map_sub_eq_div]
  exact S.selfDualChar_eq_one_of_mem _ ((sub_adeleOfLocal_mem_iff T).2 hx)

lemma continuous_charOnPlaces : Continuous (S.charOnPlaces T) :=
  continuous_ψf.subtypeVal.comp ((continuous_adeleOfLocal T).const_mul _)

/-- The character of the product of the infinite places and the completions at `T`: the product of
the characters `wave c = exp (c - conj c)` at the infinite places and of `S.charOnPlaces T`. -/
noncomputable def globalChar (x : (InfinitePlace E → ℂ) × LocProd T) : ℂ :=
  (∏ v : InfinitePlace E, wave (x.1 v)) * S.charOnPlaces T x.2

lemma continuous_globalChar : Continuous (S.globalChar T) :=
  .mul (by fun_prop [wave]) ((S.continuous_charOnPlaces T).comp continuous_snd)

/-- The decay factor at the places of `T` for a transform at the frequency `ξ`: the number
`[O : ξ O] ^ ((k - n⁷) / 2) / [O : O ∩ ξ⁻¹ O] ^ 3 * b ^ (n⁹ f)`, with `f` the number of infinite
places of `E`. -/
noncomputable def frequencyDecay (ξ : LocProd T) : ℝ :=
  √(genIndex ξ) ^ (𝔰.k - 𝔰.n ^ 7) / denomIndex O ξ ^ 3 * S.b ^ (𝔰.n ^ 9 * numInfPlaces E)

/-- The number `t`, read at the infinite places with the scales `l v` and at `T`: the point with
components `l v * Φ v t` and the image of `t` in the product of the completions at `T`. -/
noncomputable def ratPoint (l : InfinitePlace E → ℂ) (t : E) : (InfinitePlace E → ℂ) × LocProd T :=
  (fun v : InfinitePlace E ↦ l v * Φ v t, ratToPlaces T t)

/-- For `y` integral off `T`, the norm of the denominator ideal `{a ∈ 𝓞 E | a y ∈ 𝓞 E}` is at most
the index `[O : O ∩ y⁻¹ O]`, where `O` is the ring of integers of the completions at `T`. -/
lemma absNorm_denominator_le {y : E} (hy : y ∈ ratIntegralOff T) :
    Ideal.absNorm (denominator y) ≤ denomIndex O (ratToPlaces T y) := by
  -- The denominator of `y` is the preimage of the local one under `𝓞 E → O`.
  let f : 𝓞 E →+ LocProd T := ((ratToPlaces T).comp (algebraMap (𝓞 E) E)).toAddMonoidHom
  let D : AddSubgroup (LocProd T) := O.toAddSubgroup.comap (.mulLeft (ratToPlaces T y))
  have h_integral (a : 𝓞 E) : algebraMap E (𝔸f E) (algebraMap (𝓞 E) E a) ∈ Ô E :=
    algebraMap_mem_Ô.2 a.isIntegral_coe
  have h_comap : (denominator y).toAddSubgroup = D.comap f := by
    ext a
    have h_off : algebraMap E (𝔸f E) (algebraMap (𝓞 E) E a * y) ∈ integralOff T := by
      simpa only [map_mul] using mul_mem ((mem_Ô_iff T).1 (h_integral a)).right hy
    rw [Submodule.mem_toAddSubgroup, mem_denominator, ← algebraMap_mem_Ô, mem_Ô_iff T,
      and_iff_left h_off]
    simp [D, f, mul_comm]
  have h_range : f.range ≤ O.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    exact ((mem_Ô_iff T).1 (h_integral a)).left
  calc
    _ = (denominator y).toAddSubgroup.index := Ideal.absNorm_eq_natCard _
    _ = D.relIndex f.range := by rw [h_comap, index_comap]
    _ ≤ _ := relIndex_le_of_le_right h_range (denomIndex_ne_zero T _)

/-- Let `y ≠ 0` be integral off `T`, and let `‖c v‖⁻¹ ≤ |x v| ≤ B` with `1 ≤ B`. Take the product of
the decay factors of `y` at the infinite places (`dampedPower k r = r ^ k * min 1 r ^ 6` at
`r = ‖c v * Φ v y‖⁻¹`, `Φ v` the embedding at `v`) and at `T`. It is at most
`∏ v, |x v| ^ k * B ^ 6` times the inverse cube of the height of `y`, whose finite part is the norm
of the denominator ideal. -/
lemma frequency_term_le {B : ℝ} (k : ℕ) {c : InfinitePlace E → ℂ} {x : InfinitePlace E → ℝ}
    (hB : 1 ≤ B) (h_lower : ∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ |x v|)
    (h_upper : ∀ v : InfinitePlace E, |x v| ≤ B) {y : E} (hy₀ : y ≠ 0)
    (hyT : y ∈ ratIntegralOff T) :
    (∏ v : InfinitePlace E, dampedPower k ‖c v * Φ v y‖⁻¹) *
        (√(genIndex (ratToPlaces T y)) ^ k / denomIndex O (ratToPlaces T y) ^ 3) ≤
      (∏ v : InfinitePlace E, |x v| ^ k * B ^ 6) *
        ((∏ v : InfinitePlace E, (max 1 ‖Φ v y‖)⁻¹ ^ 6) *
          (Ideal.absNorm (denominator y) : ℝ)⁻¹ ^ 3) := by
  have h_inf (v : InfinitePlace E) : dampedPower k ‖c v * Φ v y‖⁻¹ * ‖Φ v y‖ ^ k ≤
      |x v| ^ k * B ^ 6 * (max 1 ‖Φ v y‖)⁻¹ ^ 6 := by
    have h_min : min 1 (‖c v‖⁻¹ * ‖Φ v y‖⁻¹) ≤ B * (max 1 ‖Φ v y‖)⁻¹ := by
      rcases le_total 1 ‖Φ v y‖ with h_ge | h_le
      · grw [min_le_right, h_lower v, h_upper v, max_eq_right h_ge]
      · grw [min_le_left, max_eq_left h_le, inv_one, mul_one, hB]
    have h_cancel : (‖c v‖⁻¹ * ‖Φ v y‖⁻¹) ^ k * ‖Φ v y‖ ^ k = ‖c v‖⁻¹ ^ k := by
      rw [← mul_pow, inv_mul_cancel_right₀ (by simpa using hy₀)]
    rw [dampedPower, norm_mul, mul_inv, mul_right_comm, h_cancel, mul_assoc, ← mul_pow]
    gcongr
    exact h_lower v
  set d : ℝ := (Ideal.absNorm (denominator y) : ℝ)
  have h_one_le : 1 ≤ d := by
    simpa [d, Nat.one_le_iff_ne_zero, Ideal.absNorm_eq_zero_iff] using denominator_ne_bot y
  have h_finite : ((denomIndex O (ratToPlaces T y) : ℝ) ^ 3)⁻¹ ≤ d⁻¹ ^ 3 := by
    grw [← absNorm_denominator_le T hyT, inv_pow]
  unfold dampedPower at h_inf ⊢
  calc
    _ ≤ (∏ v, ‖c v * Φ v y‖⁻¹ ^ k * min 1 ‖c v * Φ v y‖⁻¹ ^ 6) *
        ((∏ v, ‖Φ v y‖) ^ k * d⁻¹ ^ 3) := by
      grw [div_eq_mul_inv, h_finite, sqrt_genIndex_le_prod_norm T hy₀ hyT]
    _ = (∏ v, ‖c v * Φ v y‖⁻¹ ^ k * min 1 ‖c v * Φ v y‖⁻¹ ^ 6 * ‖Φ v y‖ ^ k) * d⁻¹ ^ 3 := by
      rw [← mul_assoc, ← prod_pow, ← prod_mul_distrib]
    _ ≤ _ := by grw [h_inf, prod_mul_distrib, mul_assoc]

/-- Let `X` be a finite set of nonzero elements of `E` that are integral off `T`, and let
`‖c v‖⁻¹ ≤ |x v| ≤ B` with `1 ≤ B`. The sum over `y ∈ X` of the product of the decay factors at the
infinite places and at `T` is at most `∏ v, (|x v| ^ k * (b B²)³)`. -/
theorem sum_frequencies_le (B : ℝ) (k : ℕ) (X : Finset E) (c : InfinitePlace E → ℂ)
    (x : InfinitePlace E → ℝ) (hB : 1 ≤ B) (h_lower : ∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ |x v|)
    (h_upper : ∀ v : InfinitePlace E, |x v| ≤ B) (hX₀ : ∀ y ∈ X, y ≠ 0)
    (hXT : ∀ y ∈ X, y ∈ ratIntegralOff T) :
    ∑ y ∈ X, (∏ v : InfinitePlace E, dampedPower k ‖c v * Φ v y‖⁻¹) *
        (√(genIndex (ratToPlaces T y)) ^ k / denomIndex O (ratToPlaces T y) ^ 3) ≤
      ∏ v : InfinitePlace E, |x v| ^ k * (S.b * B ^ 2) ^ 3 := by
  -- The inverse cubes of the heights have sum at most `64 * 38 * exp 4` per infinite place.
  have h_const : 64 * 38 * Real.exp 4 ≤ S.b ^ 3 := by
    have h_exp : Real.exp 4 = Real.exp 1 ^ 4 := by simp [← Real.exp_natCast_mul]
    grw [h_exp, Real.exp_one_lt_three.le, ← S.thousand_le_b]
    norm_num
  calc
    _ ≤ ∑ y ∈ X, (∏ v, |x v| ^ k * B ^ 6) *
        ((∏ v, (max 1 ‖Φ v y‖)⁻¹ ^ 6) * (Ideal.absNorm (denominator y) : ℝ)⁻¹ ^ 3) :=
      sum_le_sum fun y hy ↦ frequency_term_le T k hB h_lower h_upper (hX₀ y hy) (hXT y hy)
    _ ≤ (∏ v, |x v| ^ k * B ^ 6) * (64 * 38 * Real.exp 4) ^ numInfPlaces E := by
      grw [← mul_sum, sum_height_inv_cube_le]
    _ ≤ ∏ v, |x v| ^ k * B ^ 6 * S.b ^ 3 := by
      grw [h_const, prod_mul_distrib (g := fun _ ↦ S.b ^ 3), prod_const, card_univ]
    _ = _ := prod_congr rfl fun v _ ↦ by ring

/-- Scaling by `r > 0` at the infinite places and projecting to `T` maps the measure on the adeles
that are integral off `T` to `volÔ E / ∏ v, r v ^ 2` times the product measure, where `volÔ E` is
the volume of the integral finite adeles. -/
lemma measurePreserving_scale_evalPlaces {r : InfinitePlace E → ℝ}
    (hr : ∀ v : InfinitePlace E, 0 < r v) :
    MeasurePreserving (fun z : 𝔸 E ↦ (fun v : InfinitePlace E ↦ r v * z.1 v, evalPlaces T z.2))
      (volume.restrict (Set.univ ×ˢ (integralOff T : Set (𝔸f E))))
      (ENNReal.ofReal (volÔ E / ∏ v : InfinitePlace E, r v ^ 2) • volume) := by
  -- Scaling by `r` has determinant `∏ v, r v ^ 2`.
  let L : (InfinitePlace E → ℂ) →ₗ[ℝ] InfinitePlace E → ℂ :=
    .pi fun v ↦ (r v • (1 : ℂ →ₗ[ℝ] ℂ)).comp (.proj v)
  have h_det : LinearMap.det L = ∏ v, r v ^ 2 := by simp [L, LinearMap.det_pi]
  have h_pos : 0 < ∏ v, r v ^ 2 := prod_pos fun v _ ↦ pow_pos (hr v) 2
  have h_inf : MeasurePreserving L volume (ENNReal.ofReal (∏ v, r v ^ 2)⁻¹ • volume) :=
    ⟨by fun_prop, by rw [map_linearMap_addHaar_eq_smul_addHaar _ (h_det.trans_ne h_pos.ne'), h_det,
      abs_of_pos (inv_pos.2 h_pos)]⟩
  have h_fin : MeasurePreserving (evalPlaces T) (volume.restrict (integralOff T))
      (volÔ E • volume) := ⟨by fun_prop, map_evalPlaces_restrict_volume T⟩
  have h_map : (fun z : 𝔸 E ↦ (fun v ↦ r v * z.1 v, evalPlaces T z.2)) =
      Prod.map L (evalPlaces T) := by ext <;> simp [L]
  rw [h_map]
  simpa [volume_eq_prod, ← prod_restrict, prod_smul_left, prod_smul_right, div_eq_mul_inv,
    mul_smul] using h_inf.prod h_fin

end

/-- The standard character of the adeles at `x` is `exp (-2πi ∑ v, 2 Re x_v)`, with `x_v = x.1 v`
the components at the infinite places, times the standard character `ψf E` of the finite adeles at
the finite part `x.2`. -/
lemma coe_stdAddChar_apply {E : Type*} [Field E] [NumberField E] (x : 𝔸 E) :
    (New.stdAddChar E x : ℂ) = fourierChar (-∑ v : InfinitePlace E, 2 * (x.1 v).re) * ψf E x.2 :=
  Circle.coe_mul _ _

/-- The character `wave c = exp (c - conj c)` at `c = 2πi w` is `exp (2πi * 2 Re w)`. -/
lemma wave_two_pi_I_mul (w : ℂ) : wave (2 * π * .I * w) = fourierChar (2 * w.re) := by
  have h_im : (2 * π * .I * w : ℂ).im = 2 * π * w.re := by simp
  rw [wave, sub_conj, h_im, fourierChar_apply, mul_left_comm (2 * π)]

omit [WeilData E] [T.StarStable] in
/-- Let `ϖ = S.deltaE` be the generator of the different of `E` in the filling data `S`. For `y ∈ E`
and an adele `z`, both integral off `T`, the standard adelic character at `-y z / ϖ` is the product
of the characters `wave c = exp (c - conj c)` at the infinite places and of `S.charOnPlaces T`, the
character `x ↦ ψ_f(-x / ϖ)` on the product of the completions at `T`. -/
lemma stdAddChar_div_deltaE {y : E} (hy : y ∈ ratIntegralOff T) {z : 𝔸 E}
    (hz : z.2 ∈ integralOff T) :
    (New.stdAddChar E (toAdele (y / S.deltaE) * -z) : ℂ) =
      (∏ v : InfinitePlace E, wave (2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v)) *
        S.charOnPlaces T (ratToPlaces T y * evalPlaces T z.2) := by
  let w (v : InfinitePlace E) : ℂ := Φ v y / Φ v S.deltaE * z.1 v
  have h_inf : (fourierChar (-∑ v, 2 * ((toAdele (y / S.deltaE) * -z).1 v).re) : ℂ) =
      ∏ v : InfinitePlace E, wave (2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v) := by
    have h_arg (v : InfinitePlace E) : (toAdele (y / S.deltaE) * -z).1 v = -w v := by simp [w]
    have h_wave (v : InfinitePlace E) :
        2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v = 2 * π * .I * w v := by ring
    calc
      _ = (fourierChar (∑ v, 2 * (w v).re) : ℂ) := by
        simp_rw [h_arg, neg_re, mul_neg, sum_neg_distrib, neg_neg]
      _ = ∏ v, (fourierChar (2 * (w v).re) : ℂ) := by
        simp only [fourierChar_apply, mul_sum, ofReal_sum, sum_mul, Complex.exp_sum]
      _ = _ := by simp only [h_wave, wave_two_pi_I_mul]
  have h_fin : (ψf E (toAdele (y / S.deltaE) * -z).2 : ℂ) =
      S.charOnPlaces T (evalPlaces T (algebraMap E (𝔸f E) y * z.2)) := by
    rw [S.charOnPlaces_evalPlaces T (mul_mem hy hz), selfDualChar_apply]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm]
  rw [coe_stdAddChar_apply, h_inf, h_fin, map_mul (evalPlaces T), ratToPlaces, RingHom.comp_apply]

omit [WeilData E] [T.StarStable] in
/-- Let `G` be a function on the adeles that is invariant under the integral finite adeles that
vanish at `T`, written `a - adeleOfLocal T (evalPlaces T a)` (`a ∈ Ô E` integral, with its
components at `T` removed). If the Fourier transform of `G` at `y / ϖ` is not zero, then `y` is
integral off `T`. -/
lemma mem_ratIntegralOff_of_transform_ne_zero {G : 𝔸 E → ℂ}
    (hG : ∀ a ∈ Ô E, ∀ z : 𝔸 E, G ((0, a - adeleOfLocal T (evalPlaces T a)) + z) = G z) {y : E}
    (hy : ∫ z : 𝔸 E, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * G z ≠ 0) :
    y ∈ ratIntegralOff T := by
  rw [ratIntegralOff, Subring.mem_comap, ← sub_adeleOfLocal_mem_iff,
    ← S.forall_selfDualChar_mul_eq_one_iff]
  rintro ⟨a, ha⟩
  let a' : 𝔸 E := (0, a - adeleOfLocal T (evalPlaces T a))
  -- Translation by `a'` multiplies the transform by a character value, which must be `1`.
  suffices (New.stdAddChar E (toAdele (y / S.deltaE) * -a') : ℂ) = 1 by
    rw [← this, selfDualChar_apply]
    simp [New.stdAddChar, a', adeleOfLocal_evalPlaces, div_eq_mul_inv]
    exact congrArg _ (by ring)
  refine (mul_eq_right₀ hy).1 (Eq.symm ?_)
  rw [← integral_const_mul, ← integral_add_left_eq_self _ a']
  congr with z
  rw [hG a ha, neg_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]

/-- The function on the adeles that reads `F` after scaling by `r` at the infinite places and
projecting to `T`, on the adeles that are integral off `T`, and is zero elsewhere. -/
noncomputable def extendToAdeles (r : InfinitePlace E → ℝ)
    (F : (InfinitePlace E → ℂ) × LocProd T → ℝ) : 𝔸 E → ℝ :=
  (Set.univ ×ˢ (integralOff T : Set (𝔸f E))).indicator fun z : 𝔸 E ↦
    F (fun v : InfinitePlace E ↦ r v * z.1 v, evalPlaces T z.2)

section ExtendToAdeles

variable {r : InfinitePlace E → ℝ} {F : (InfinitePlace E → ℂ) × LocProd T → ℝ}

section

omit [WeilData E] [T.StarStable]

lemma extendToAdeles_of_mem {z : 𝔸 E} (hz : z.2 ∈ integralOff T) :
    extendToAdeles T r F z = F (fun v : InfinitePlace E ↦ r v * z.1 v, evalPlaces T z.2) := by
  simp [extendToAdeles, hz]

lemma extendToAdeles_of_notMem {z : 𝔸 E} (hz : z.2 ∉ integralOff T) :
    extendToAdeles T r F z = 0 := by simp [extendToAdeles, hz]

/-- At the diagonal image `toAdele y` of a number `y` that is integral off `T`, the extension of `F`
is the value of `F` at the point with components `r v * Φ v y` and the image of `y` at `T`. -/
lemma extendToAdeles_toAdele {y : E} (hy : y ∈ ratIntegralOff T) :
    extendToAdeles T r F (toAdele y) = F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) y) :=
  extendToAdeles_of_mem T hy

/-- Let `F` be a real function on the product of the infinite places and the completions at `T`, and
let `r v` be real scales. The extension `extendToAdeles T r F` reads `F` after scaling by `r` at
infinity and projecting to `T`, and is zero at adeles that are not integral off `T`. It is invariant
under the integral finite adeles that vanish at `T`, written `a - adeleOfLocal T (evalPlaces T a)`
with `a ∈ Ô E` integral. -/
lemma extendToAdeles_sub_adeleOfLocal_add {a : 𝔸f E} (ha : a ∈ Ô E) (z : 𝔸 E) :
    extendToAdeles T r F ((0, a - adeleOfLocal T (evalPlaces T a)) + z) =
      extendToAdeles T r F z := by
  have h_off : a - adeleOfLocal T (evalPlaces T a) ∈ integralOff T :=
    sub_mem ((mem_Ô_iff T).1 ha).right (adeleOfLocal_mem_integralOff T _)
  by_cases hz : z.2 ∈ integralOff T
  · rw [extendToAdeles_of_mem T hz, extendToAdeles_of_mem T (add_mem h_off hz)]
    simp
  · rw [extendToAdeles_of_notMem T hz,
      extendToAdeles_of_notMem T (mt (add_mem_cancel_left h_off).1 hz)]

/-- For positive scales `r`, the extension of an integrable function to the adeles is integrable. -/
lemma integrable_extendToAdeles (hr : ∀ v : InfinitePlace E, 0 < r v) (hF : Integrable F) :
    Integrable (extendToAdeles T r F) :=
  (integrable_indicator_iff (isOpen_univ.prod (isOpen_integralOff T)).measurableSet).2
    ((measurePreserving_scale_evalPlaces T hr).integrable_comp_of_integrable
      (hF.smul_measure ofReal_ne_top))

/-- Let `F` be a real function on the product of the infinite places and the completions at `T`, let
`r v` be real scales, and let `y ∈ E` be integral off `T`. Suppose `F` is lower semicontinuous at
the point (`ratPoint`) with components `r v * Φ v y` and the image of `y` at `T`. Then the extension
of `F` to the adeles is lower semicontinuous at the diagonal image `toAdele y`. -/
lemma lowerSemicontinuousAt_extendToAdeles {y : E} (hy : y ∈ ratIntegralOff T)
    (hF : LowerSemicontinuousAt F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) y)) :
    LowerSemicontinuousAt (extendToAdeles T r F) (toAdele y) := by
  have h_comp : LowerSemicontinuousAt
      (F ∘ fun z : 𝔸 E ↦ (fun v ↦ r v * z.1 v, evalPlaces T z.2)) (toAdele y) :=
    .comp hF (by fun_prop)
  intro s hs
  filter_upwards [((isOpen_integralOff T).preimage continuous_snd).mem_nhds hy,
    h_comp s (hs.trans_eq (extendToAdeles_toAdele T hy))] with z hz_mem hz_lt
  rwa [extendToAdeles_of_mem T hz_mem]

/-- Let `T` be a finite set of finite places of `E`, let `r > 0`, let `F` be integrable and let `y`
be integral off `T`. Extend `F` to the adeles. The Fourier transform of the extension at `y / ϖ`,
with `ϖ = S.deltaE` the generator of the different, is `volÔ E / ∏ v, r v ^ 2` times the transform
of `F` at the point `ξ` given by `y` and the scales `2πi / (Φ v ϖ * r v)`. -/
lemma integral_stdAddChar_mul_extendToAdeles (hr : ∀ v : InfinitePlace E, 0 < r v)
    (hF : Integrable F) {y : E} (hy : y ∈ ratIntegralOff T) {ξ : (InfinitePlace E → ℂ) × LocProd T}
    (hξ : ξ = ratPoint T (fun v : InfinitePlace E ↦ 2 * π * .I / Φ v S.deltaE / r v) y) :
    ∫ z : 𝔸 E, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * (extendToAdeles T r F z : ℂ) =
      (volÔ E / ∏ v : InfinitePlace E, r v ^ 2 : ℝ) •
        ∫ x : (InfinitePlace E → ℂ) × LocProd T, S.globalChar T (ξ * x) * F x := by
  -- Pull the right side back along `m` to an integral over `U`, and compare the integrands.
  let U : Set (𝔸 E) := Set.univ ×ˢ (integralOff T : Set (𝔸f E))
  let m (z : 𝔸 E) : (InfinitePlace E → ℂ) × LocProd T := (fun v ↦ r v * z.1 v, evalPlaces T z.2)
  let ψ (x : (InfinitePlace E → ℂ) × LocProd T) : ℂ := S.globalChar T (ξ * x)
  set c : ℝ := volÔ E / ∏ v, r v ^ 2
  have hU : MeasurableSet U := (isOpen_univ.prod (isOpen_integralOff T)).measurableSet
  have hm : MeasurePreserving m (volume.restrict U) (ENNReal.ofReal c • volume) :=
    measurePreserving_scale_evalPlaces T hr
  have hψ_cont : Continuous ψ := (S.continuous_globalChar T).comp (continuous_const_mul ξ)
  have h_char {z : 𝔸 E} (hz : z.2 ∈ integralOff T) :
      New.stdAddChar E (toAdele (y / S.deltaE) * -z) = ψ (m z) := by
    have h_arg (v : InfinitePlace E) :
        (ξ * m z).1 v = 2 * π * .I / Φ v S.deltaE * Φ v y * z.1 v := by
      have h_ne : (r v : ℂ) ≠ 0 := ofReal_ne_zero.2 (hr v).ne'
      simp [hξ, ratPoint, field]
    have h_snd : (ξ * m z).2 = ratToPlaces T y * evalPlaces T z.2 := by simp [hξ, m, ratPoint]
    simp only [ψ, globalChar, h_arg, h_snd, S.stdAddChar_div_deltaE T hy hz]
  calc
    _ = ∫ z in U, ψ (m z) * F (m z) := by
      rw [← integral_indicator hU]
      congr with z
      by_cases hz : z.2 ∈ integralOff T
      · rw [h_char hz, extendToAdeles_of_mem T hz]
        simp [U, m, hz]
      · simp [extendToAdeles_of_notMem T hz, U, hz]
    _ = ∫ x, ψ x * F x ∂(ENNReal.ofReal c • volume) := hm.hasLaw.integral_comp
      ((hψ_cont.aestronglyMeasurable.mul hF.ofReal.aestronglyMeasurable).smul_measure _)
    _ = c • ∫ x, ψ x * F x := by rw [integral_smul_measure, toReal_ofReal (by positivity)]

end

end ExtendToAdeles

omit [WeilData E] [T.StarStable] in
/-- One-sided Poisson summation over the infinite places and a finite set `T` of finite places. Let
the elements of `V` be integral off `T`, read as points (`ratPoint`) scaled by `r > 0` at infinity.
Let `F ≥ 0` be integrable and lower semicontinuous at these points. Let its Fourier transform at
each unit `ξ` have modulus at most `β ξ * M` with `0 ≤ M`. Let `ε` bound the finite sums of `β` over
nonzero `T`-integers, scaled by `2πi / (Φ v ϖ * r v)`. Then the sum of `F` over the points is at
most `volÔ E / ∏ v, r v ^ 2` times `ε * M + ∫ F`, with `volÔ E` the volume of the integral finite
adeles. -/
lemma sum_ratPoint_le_mul_add_integral_of_fourier_le {r : InfinitePlace E → ℝ}
  (hr : ∀ v : InfinitePlace E, 0 < r v)
    {V : Finset Eˣ} (hV : ∀ t ∈ V, (t : E) ∈ ratIntegralOff T)
    {β : (InfinitePlace E → ℂ) × LocProd T → ℝ} {ε M : ℝ}
    (hβ : ∀ X : Finset E, (∀ y ∈ X, y ≠ 0) → (∀ y ∈ X, y ∈ ratIntegralOff T) →
      ∑ y ∈ X, β (ratPoint T (fun v : InfinitePlace E ↦ 2 * π * .I / Φ v S.deltaE / r v) y) ≤ ε)
    {F : (InfinitePlace E → ℂ) × LocProd T → ℝ} (hF : Integrable F) (hF_nonneg : 0 ≤ F)
    (hM_nonneg : 0 ≤ M) (hF_lsc : ∀ t ∈ V,
      LowerSemicontinuousAt F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) (t : E)))
    (hF_hat : ∀ ξ : (InfinitePlace E → ℂ) × LocProd T, IsUnit ξ →
      ‖∫ x : (InfinitePlace E → ℂ) × LocProd T, S.globalChar T (ξ * x) * F x‖ ≤ β ξ * M) :
    ∑ t ∈ V, F (ratPoint T (fun v : InfinitePlace E ↦ (r v : ℂ)) (t : E)) ≤
      volÔ E / (∏ v : InfinitePlace E, r v ^ 2) *
        (ε * M + ∫ x : (InfinitePlace E → ℂ) × LocProd T, F x) := by
  classical
  -- Apply Poisson summation on the adeles to the extension `G` of `F`. Its transform `FG y` at
  -- `y / ϖ` is zero unless `y` is a `T`-integer, and then it is `c` times the transform `FF y` of
  -- `F` at the matching frequency `f y`.
  set c : ℝ := volÔ E / ∏ v, r v ^ 2
  let G : 𝔸 E → ℝ := extendToAdeles T r F
  let f : E → (InfinitePlace E → ℂ) × LocProd T := ratPoint T fun v ↦
    2 * π * .I / Φ v S.deltaE / r v
  let FG (y : E) : ℂ := ∫ z, New.stdAddChar E (toAdele (y / S.deltaE) * -z) * (G z : ℂ)
  let FF (y : E) : ℂ := ∫ x, S.globalChar T (f y * x) * F x
  have h_supp (y : E) (hy : ‖FG y‖ ≠ 0) : y ∈ ratIntegralOff T :=
    S.mem_ratIntegralOff_of_transform_ne_zero T
      (fun a ha z ↦ congrArg Complex.ofReal (extendToAdeles_sub_adeleOfLocal_add T ha z))
        (norm_ne_zero_iff.1 hy)
  have h_norm (y : E) (hy : y ∈ ratIntegralOff T) : ‖FG y‖ = c * ‖FF y‖ := by
    rw [show FG y = c • FF y from S.integral_stdAddChar_mul_extendToAdeles T hr hF hy rfl,
      norm_smul,
      Real.norm_of_nonneg (by positivity)]
  have h_zero : ‖FF 0‖ = ∫ x, F x := by
    simp [FF, f, ratPoint, globalChar, wave, integral_complex_ofReal, integral_nonneg hF_nonneg]
  have h_unit {y : E} (hy : y ≠ 0) : IsUnit (f y) := by
    simp [f, ratPoint, Prod.isUnit_iff, Pi.isUnit_iff, IsUnit.map, ne_of_gt, hr, hy]
  have h_bound (Y : Finset E) : ∑ y ∈ Y, ‖FG y‖ ≤ c * (ε * M + ∫ x, F x) := by
    let X : Finset E := {y ∈ Y | y ∈ ratIntegralOff T}.erase 0
    have h_freq : ∑ y ∈ X, β (f y) ≤ ε := hβ X (fun y hy ↦ ne_of_mem_erase hy)
      fun y hy ↦ (mem_filter.1 (mem_of_mem_erase hy)).2
    calc
      _ = ∑ y ∈ Y with y ∈ ratIntegralOff T, c * ‖FF y‖ := by
        rw [← sum_filter_of_ne fun y _ ↦ h_supp y]
        exact sum_congr rfl fun y hy ↦ h_norm y (mem_filter.1 hy).2
      _ ≤ ∑ y ∈ insert 0 X, c * ‖FF y‖ := by
        gcongr
        exact insert_erase_subset 0 _
      _ = c * (∫ x, F x) + ∑ y ∈ X, c * ‖FF y‖ := by rw [sum_insert (notMem_erase 0 _), h_zero]
      _ ≤ c * (∫ x, F x) + ∑ y ∈ X, c * (β (f y) * M) := by
        gcongr with y hy
        exact hF_hat (f y) (h_unit (ne_of_mem_erase hy))
      _ ≤ _ := by grw [← mul_sum, ← sum_mul, h_freq, mul_add, add_comm]
  -- The frequencies are reindexed by `y ↦ y / ϖ`.
  have h_all (Y : Finset E) :
      ∑ y ∈ Y, ‖∫ z, New.stdAddChar E (toAdele y * -z) * (G z : ℂ)‖ ≤ c * (ε * M + ∫ x, F x) := by
    simpa [FG, S.deltaE_ne_zero] using
      h_bound (Y.map (Equiv.mulRight₀ _ S.deltaE_ne_zero).toEmbedding)
  let ι : Eˣ ↪ ratAdeles E :=
    ⟨fun t ↦ ⟨toAdele (t : E), t, rfl⟩, fun t ↦ by simp [toAdele, Units.val_inj]⟩
  calc
    _ = ∑ t ∈ V.map ι, G t := by
      rw [sum_map]
      exact sum_congr rfl fun t ht ↦ (extendToAdeles_toAdele T (hV t ht)).symm
    _ ≤ _ := IsDualFamily.sum_le_of_fourier (integrable_extendToAdeles T hr hF)
      (Set.indicator_nonneg fun z _ ↦ hF_nonneg _) (V.map ι) (forall_mem_map.2 fun t ht ↦
        lowerSemicontinuousAt_extendToAdeles T (hV t ht) (hF_lsc t ht)) h_all

/-- A head is a sequence of entries on which the forms of the sieve are evaluated. Here each entry
is a unit at every infinite place together with a unit of the product of the completions at `T`. -/
abbrev GlobalHead : Type := ℕ → (InfinitePlace E → ℂˣ) × (LocProd T)ˣ

/-- A point of the product of the infinite places and `T` as a unit. A component at an infinite
place that is zero is replaced by `1`, and so is the component in `LocProd T` if it is not a
unit. -/
noncomputable abbrev unitOrOneAtPlaces (x : (InfinitePlace E → ℂ) × LocProd T) :
    (InfinitePlace E → ℂˣ) × (LocProd T)ˣ :=
  Prod.map (unitOrOne ∘ ·) unitOrOne x

/-- A sieve system on the product of the infinite places and `T`, for the character
`S.globalChar T`. The density `J i` pairs two heads and, for `i ≤ n`, is the integral of `J (i + 1)`
over a common entry at position `i`. The density at the last entry `J (n + 1)` is continuous, and
positive semidefinite on heads with a common entry at position `n`; the mass `J 0` has modulus at
most `En`. The transform of `J (i + 1)` in the common entry at a unit `ξ` has modulus at most the
decay `β ξ` times the weights `Λ i` of the two heads. For `i < n`, the same bound with weights
`Λ (i + 1)` holds for `J (i + 1)` at two heads with entries `t`, `s` at position `i`, if
`ξ = 1 / t - 1 / s` (divided by the level `M = S.M` at `T`) is a unit. -/
abbrev IsGlobalSieveSystem (n : ℕ) (J : ℕ → GlobalHead T → GlobalHead T → ℂ) (En : ℝ)
    (Λ : ℕ → GlobalHead T → ℝ) (β : (InfinitePlace E → ℂ) × LocProd T → ℝ) : Prop :=
  SieveSystem (unitOrOneAtPlaces T)
    (Prod.map (fun z : InfinitePlace E → ℂˣ ↦ (fun w : ℂˣ ↦ ((w⁻¹ : ℂˣ) : ℂ)) ∘ z)
      fun w : (LocProd T)ˣ ↦ ratToPlaces T (S.M : E)⁻¹ * ((w⁻¹ : (LocProd T)ˣ) : LocProd T))
    n J (S.globalChar T) En Λ β

/-- `ε` bounds the sums of the decay `β` over nonzero frequencies that are integral off `T`, at all
scales `c v / frameScaleSq v a` with `‖c v‖⁻¹ ≤ |realM v| / M`. These cover the frequencies of
Poisson summation (`c v = 2πi / Φ v ϖ`) and, when `1 ≤ |realM v|`, of two heads with different last
entries (`c v = M`). Here `M` is the level, `realM v` is the real number `M * Φ v ϖ / (2πi)`, and
`frameScaleSq v a = realM v ^ (2 (ϱ - a)) / N` scales the entry `a`. -/
def BoundsDecay (β : (InfinitePlace E → ℂ) × LocProd T → ℝ) (ε : ℝ) : Prop :=
  ∀ (a : ℕ) (c : InfinitePlace E → ℂ), (∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ |S.realM v| / S.M) →
    ∀ X : Finset E, (∀ y ∈ X, y ≠ 0) → (∀ y ∈ X, y ∈ ratIntegralOff T) →
      ∑ y ∈ X, β (ratPoint T (fun v : InfinitePlace E ↦ c v / S.frameScaleSq v a) y) ≤ ε

/-- The number `t` as the entry `a` of a head: scaled at the infinite place `v` by
`S.frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, with `κ_v = S.realM v`, and read at `T`. -/
noncomputable def scaledEntry (a : ℕ) (t : Eˣ) : (InfinitePlace E → ℂ) × LocProd T :=
  ratPoint T (fun v : InfinitePlace E ↦ (S.frameScaleSq v a : ℂ)) (t : E)

/-- The head with first entries `p`, next entry `t` and later entries `1`, read in the scaled frame
at the infinite places and at `T`. -/
noncomputable def scaledHead {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) (t : Eˣ) : GlobalHead T :=
  fun a : ℕ ↦ unitOrOneAtPlaces T (S.scaledEntry T a (padTuple (fun j : Fin i ↦ (p j : Eˣ)) t a))

/-- The constant of Poisson summation in the entry `a`: the volume of the integral finite adeles
divided by the Jacobian of the scaling at the infinite places. -/
noncomputable def poissonConst (a : ℕ) : ℝ :=
  volÔ E / ∏ v : InfinitePlace E, S.frameScaleSq v a ^ 2

omit [WeilData E] in
lemma poissonConst_nonneg (a : ℕ) : 0 ≤ S.poissonConst a :=
  div_nonneg (by positivity) (by positivity)

/-- The sum of the densities `J (i + 1)` over the pairs of heads of length `i` with entries in `A`,
at the common next entry `x`. -/
noncomputable def entryDensity (A : Finset Eˣ) (J : ℕ → GlobalHead T → GlobalHead T → ℂ) (i : ℕ)
    (x : (InfinitePlace E → ℂ) × LocProd T) : ℂ :=
  ∑ p : Fin i → A, ∑ q : Fin i → A, J (i + 1)
    (Function.update (S.scaledHead T p 1) i (unitOrOneAtPlaces T x))
    (Function.update (S.scaledHead T q 1) i (unitOrOneAtPlaces T x))

/-- The sum of densities in which `i` entries are still summed over `A`, the last of them common
to the two heads: the real part of the mass for `i = 0`, and of the sum of `entryDensity (i - 1)`
over `A` for `i > 0`. -/
noncomputable def densitySum (A : Finset Eˣ) (J : ℕ → GlobalHead T → GlobalHead T → ℂ) : ℕ → ℝ
  | 0 => (J 0 (S.scaledHead T (A := A) ![] 1) (S.scaledHead T (A := A) ![] 1)).re
  | i + 1 => ∑ t ∈ A, (S.entryDensity T A J i (S.scaledEntry T i t)).re

section OneEntryFewer

variable {A : Finset Eˣ} {n : ℕ} {J : ℕ → GlobalHead T → GlobalHead T → ℂ} {massBound ε : ℝ}
  {Λ : ℕ → GlobalHead T → ℝ} {β : (InfinitePlace E → ℂ) × LocProd T → ℝ}

omit [WeilData E] [T.StarStable]

/-- At the point `scaledEntry T i t` (the unit `t` as entry `i`, scaled at each infinite place `v`
by `frameScaleSq v i` and read at `T`), the entry density `entryDensity T A J i` is the sum of
`J (i + 1)` over the pairs of heads `scaledHead T p t`, `scaledHead T q t`. These heads have first
entries `p`, `q : Fin i → A`, common next entry `t`, and later entries `1`. -/
lemma entryDensity_scaledEntry (i : ℕ) (t : Eˣ) :
    S.entryDensity T A J i (S.scaledEntry T i t) =
      ∑ p : Fin i → A, ∑ q : Fin i → A, J (i + 1) (S.scaledHead T p t) (S.scaledHead T q t) := by
  have h_update (p : Fin i → A) : Function.update (S.scaledHead T p 1) i
      (unitOrOneAtPlaces T (S.scaledEntry T i t)) = S.scaledHead T p t := by
    simp +contextual [scaledHead, padTuple, Function.update_eq_iff]
  simp only [entryDensity, h_update]

/-- A head whose first entries are `p` followed by `t`, and whose later entries are `1`, is the head
with first entries `p` and next entry `t`. -/
lemma scaledHead_snoc {i : ℕ} (p : Fin i → A) (t : A) :
    S.scaledHead T (Fin.snoc p t : Fin (i + 1) → A) 1 = S.scaledHead T p t :=
  funext fun a ↦ by grind [scaledHead, padTuple, Fin.snoc, Fin.castLT]

/-- For a sieve system of length `n` with densities `J` and `i ≤ n`, the sum of `J (i + 1)` over the
pairs of heads with a common entry at position `i` is a nonnegative real number. -/
lemma entryDensity_nonneg (K : S.IsGlobalSieveSystem T n J massBound Λ β) {i : ℕ} (hi : i ≤ n) :
    0 ≤ S.entryDensity T A J i :=
  fun _ ↦ K.sum_nonneg hi _ fun _ ↦ Function.update_self ..

/-- Let `K` be a sieve system of length `n` with densities `J`, let `A` be a finite set of units of
`E`, and let `i ≤ n`. The entry density at `x` (`entryDensity`) is the sum of `J (i + 1)` over the
pairs of heads with first `i` entries in `A` and common entry `x` at position `i`. Its real part is
lower semicontinuous in `x` at each point `scaledEntry T i t`, which is the unit `t` scaled at each
infinite place `v` by `frameScaleSq v i = κ_v ^ (2 (ϱ - i)) / N` and read at `T`. -/
lemma lowerSemicontinuousAt_entryDensity (K : S.IsGlobalSieveSystem T n J massBound Λ β) {i : ℕ}
    (hi : i ≤ n) (t : Eˣ) :
    LowerSemicontinuousAt
      (fun x : (InfinitePlace E → ℂ) × LocProd T ↦ (S.entryDensity T A J i x).re)
      (S.scaledEntry T i t) := by
  -- The rational point is a unit, where passing to units is continuous.
  have h_cont : ContinuousAt (unitOrOneAtPlaces T) (S.scaledEntry T i t) :=
    .prodMap (.piMap fun v ↦ continuousAt_unitOrOne
        (.mk0 (S.frameScaleSq v i * Φ v t) (by simp [(S.frameScaleSq_pos v i).ne'])))
      (continuousAt_unitOrOne (t.map (ratToPlaces T).toMonoidHom))
  have h_lsc : LowerSemicontinuousAt
      (fun x ↦ ENNReal.ofReal (S.entryDensity T A J i x).re) (S.scaledEntry T i t) :=
    K.lowerSemicontinuousAt_sum hi _ (fun _ _ ↦ Function.update_self ..)
      fun _ ↦ continuousAt_const.update i h_cont
  -- The density is nonnegative, so `ENNReal.ofReal` loses nothing.
  intro y hy
  obtain hy_neg | hy_nonneg := lt_or_ge y 0
  · exact .of_forall fun x ↦ hy_neg.trans_le (S.entryDensity_nonneg T K hi x).1
  · simpa only [ofReal_lt_ofReal_iff_of_nonneg hy_nonneg] using
      h_lsc _ ((ofReal_lt_ofReal_iff_of_nonneg hy_nonneg).2 hy)

/-- Poisson summation in the entry `i ≤ n`. Let `S` satisfy the standing hypotheses
(`IsAdmissible`). Let `J` be the densities of a sieve system of length `n` with weights `Λ` and
decay `β`, summed to at most `ε` over nonzero frequencies (`BoundsDecay`), and let the elements of
`A` be integral off `T`. The head `scaledHead T p 1` has first entries `p` and later entries `1`,
with the entry `a` scaled at the infinite place `v` by `frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`.
The left side is the real part of the sum of `J (i + 1)` over the pairs of heads of length `i + 1`
with entries in `A` and a common last entry. Up to the constant `poissonConst i = volÔ E / ∏ v,
frameScaleSq v i ^ 2`, with `volÔ E` the volume of the integral finite adeles, the frequency `0`
gives the sum of `J i` over all pairs of heads of length `i`, and the other frequencies give at most
`ε` times the squared sum of the weights of these heads. -/
lemma densitySum_succ_le (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T)
    (K : S.IsGlobalSieveSystem T n J massBound Λ β) (hβ : S.BoundsDecay T β ε) {i : ℕ}
    (hi : i ≤ n) :
    S.densitySum T A J (i + 1) ≤ S.poissonConst i *
      (ε * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 +
        (∑ p : Fin i → A, ∑ q : Fin i → A, J i (S.scaledHead T p 1) (S.scaledHead T q 1)).re) := by
  set density : (InfinitePlace E → ℂ) × LocProd T → ℂ := S.entryDensity T A J i
  have h_nonneg : 0 ≤ density := S.entryDensity_nonneg T K hi
  have h_int : Integrable density := K.integrable_sum_update hi (S.scaledHead T · 1)
  have h_integral : ∫ x, (density x).re =
      (∑ p : Fin i → A, ∑ q : Fin i → A, J i (S.scaledHead T p 1) (S.scaledHead T q 1)).re :=
    (integral_re h_int).trans (congrArg re (K.integral_sum_update hi (S.scaledHead T · 1)))
  have h_hat (ξ : (InfinitePlace E → ℂ) × LocProd T) (hξ : IsUnit ξ) :
      ‖∫ x, S.globalChar T (ξ * x) * ((density x).re : ℂ)‖ ≤
        β ξ * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 := by
    -- The density is real.
    simp only [← eq_re_of_ofReal_le (h_nonneg _)]
    exact K.norm_integral_mul_sum_update_le hi (S.scaledHead T · 1) hξ
  have h_scale (v : InfinitePlace E) : ‖2 * π * .I / Φ v S.deltaE‖⁻¹ ≤ |S.realM v| / S.M := by
    simp [abs_realM_eq, div_right_comm _ (2 * π), abs_of_pos pi_pos, Nat.Prime.ne_zero]
  rw [← h_integral]
  exact S.sum_ratPoint_le_mul_add_integral_of_fourier_le T (F := fun x ↦ (density x).re)
    (S.frameScaleSq_pos · i) hA
    (hβ i _ h_scale) h_int.re (fun x ↦ (h_nonneg x).1) (sq_nonneg _)
    (fun t _ ↦ S.lowerSemicontinuousAt_entryDensity T K hi t) h_hat

/-- Let `J`, `Λ ≥ 0`, `β` be the densities, weights and decay of a sieve system of length `n`: for
`i < n`, the modulus of `J (i + 1)` at two heads is at most `β ξ` times their weights `Λ (i + 1)` if
the difference `ξ` of the inverses of their entries at position `i` (divided by the level `M = S.M`
at `T`) is a unit. Let `β` sum to at most `ε` over nonzero frequencies (`BoundsDecay`), and let the
inverses of `M` and of the elements of `A` be integral off `T`. At two heads with different entries
`t`, `s` at position `i < n`, the frequency comes from the nonzero `T`-integer
`(1 / t - 1 / s) / M`, so the real part of `J (i + 1)` is at most `ε` times the two weights. -/
lemma re_le_of_last_entries_ne [S.IsAdmissible]
    (hA : ∀ t ∈ A, ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {i : ℕ} (hi : i < n)
    {t s : A} (hts : t ≠ s) (p q : Fin i → A) :
    (J (i + 1) (S.scaledHead T p t) (S.scaledHead T q s)).re ≤
      ε * (Λ (i + 1) (S.scaledHead T p t) * Λ (i + 1) (S.scaledHead T q s)) := by
  let y : E := (S.M : E)⁻¹ * (t.val⁻¹.val - s.val⁻¹.val)
  let ξ : (InfinitePlace E → ℂ) × LocProd T := ratPoint T (fun v ↦ S.M / S.frameScaleSq v i) y
  have y_ne : y ≠ 0 := by
    simp [y, sub_eq_zero, Units.val_inj, hts, Nat.Prime.ne_zero]
  have y_mem : y ∈ ratIntegralOff T := mul_mem hM_inv (sub_mem (hA t t.property) (hA s s.property))
  have ξ_unit : IsUnit ξ := by
    simp [ξ, y_ne, ratPoint, Prod.isUnit_iff, Pi.isUnit_iff, IsUnit.map,
      (S.frameScaleSq_pos _ i).ne', Nat.Prime.ne_zero]
  have h_scale (v : InfinitePlace E) : ‖(S.M : ℂ)‖⁻¹ ≤ |S.realM v| / S.M := by
    grw [← one_le_abs_realM, Complex.norm_natCast, one_div]
  have hβ_le : β ξ ≤ ε := by
    simpa [ξ] using hβ i (fun _ ↦ S.M) h_scale {y} (by simpa using y_ne) (by simpa using y_mem)
  have h_off : ‖J (i + 1) (S.scaledHead T p t) (S.scaledHead T q s)‖ ≤
      β ξ * (Λ (i + 1) (S.scaledHead T p t) * Λ (i + 1) (S.scaledHead T q s)) := by
    have h_raw := K.norm_le_of_isUnit_sub i (S.scaledHead T p t) (S.scaledHead T q s) hi
    -- The frequency `ξ'` of the sieve system at these two heads is `ξ`.
    extract_lets ξ' at h_raw
    have hξ : ξ' = ξ := by
      simp [ξ', ξ, scaledHead, scaledEntry, ratPoint, padTuple, unitOrOne, y, field, funext_iff,
        IsUnit.map, (S.frameScaleSq_pos _ i).ne', ↓map_sub, ↓map_mul, ↓map_units_inv]
      intro v
      field [Nat.Prime.ne_zero]
    rw [hξ] at h_raw
    exact h_raw ξ_unit
  grw [re_le_norm, h_off, hβ_le]
  exact mul_nonneg (hΛ _ _) (hΛ _ _)

/-- Let `J`, `Λ ≥ 0`, `β` be the densities, weights and decay of a sieve system of length `n`. Let
`β` sum to at most `ε ≥ 0` over nonzero frequencies (`BoundsDecay`), and let the inverses of the
level `M = S.M` and of the elements of `A` be integral off `T`. For `i ≤ n`, sum the real part of
`J i` over the pairs of heads of length `i` with entries in `A`. The pairs with equal last entries
give `densitySum T A J i`, by definition, and the others give at most `ε` times the squared sum of
the weights. -/
lemma re_sum_sum_le_densitySum_add [S.IsAdmissible]
    (hA : ∀ t ∈ A, ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hε : 0 ≤ ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {i : ℕ}
    (hi : i ≤ n) :
    (∑ p : Fin i → A, ∑ q : Fin i → A, J i (S.scaledHead T p 1) (S.scaledHead T q 1)).re ≤
      S.densitySum T A J i + ε * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 := by
  classical
  obtain _ | i := i
  · -- There is a single pair of empty heads.
    simpa [densitySum, Subsingleton.elim default ![]] using mul_nonneg hε (sq_nonneg _)
  -- Write each head as its first entries and its last entry, and separate equal last entries.
  have h_split (f : (Fin (i + 1) → A) → ℝ) :
      ∑ p, f p = ∑ t : A, ∑ p : Fin i → A, f (Fin.snoc p t) := by
    simp [← (Fin.snocEquiv fun _ ↦ A).sum_comp, sum_prod_type, Fin.snocEquiv]
  let w (t : A) (p : Fin i → A) : ℝ := Λ (i + 1) (S.scaledHead T p t)
  let d (t s : A) (p q : Fin i → A) : ℝ :=
    (J (i + 1) (S.scaledHead T p t) (S.scaledHead T q s)).re
  calc
    _ = ∑ t, ∑ p, ∑ s, ∑ q, d t s p q := by simp only [d, re_sum, h_split, scaledHead_snoc]
    _ ≤ ∑ t, ∑ p, (∑ q, d t t p q + ∑ s ∈ univ.erase t, ∑ q, ε * (w t p * w s q)) := by
      gcongr with t _ p
      rw [← add_sum_erase _ _ (mem_univ t)]
      gcongr with s hs q
      exact S.re_le_of_last_entries_ne T hA hM_inv K hβ hΛ hi (ne_of_mem_erase hs).symm p q
    _ ≤ ∑ t, ∑ p, (∑ q, d t t p q + ∑ s, ∑ q, ε * (w t p * w s q)) := by
      gcongr
      · exact fun s _ _ ↦ Finset.sum_nonneg fun q _ ↦ mul_nonneg hε (mul_nonneg (hΛ _ _) (hΛ _ _))
      · exact erase_subset _ _
    _ = _ := by
      simp only [d, w, densitySum, entryDensity_scaledEntry, re_sum, h_split, scaledHead_snoc,
        sum_add_distrib, ← mul_sum, ← sum_mul, sq, ← A.sum_coe_sort]

/-- Let `J` be the densities of a sieve system with weights `Λ` and decay `β`, summed to at most
`ε`, and let `1 / M` and both `t` and `1 / t` for `t ∈ A` be integral off `T`. Up to the constant of
Poisson summation, each sum of densities is at most the one before plus an error from the nonzero
frequencies and from the pairs of heads with different last entries; each part of the error is at
most `ε` times the squared sum of the weights. -/
lemma densitySum_succ_le_mul_densitySum_add [S.IsAdmissible]
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T ∧ ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hε : 0 ≤ ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {i : ℕ}
    (hi : i ≤ n) :
    S.densitySum T A J (i + 1) ≤ S.poissonConst i *
      (S.densitySum T A J i + 2 * (ε * (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2)) := by
  have hc : 0 ≤ S.poissonConst i := S.poissonConst_nonneg i
  grw [S.densitySum_succ_le T (fun t ht ↦ (hA t ht).1) K hβ hi,
    S.re_sum_sum_le_densitySum_add T (fun t ht ↦ (hA t ht).2) hM_inv K hβ hε hΛ hi, two_mul,
      add_left_comm]

/-- Let `J` be the densities of a sieve system `K` (`IsGlobalSieveSystem`, so `massBound` bounds the
mass `J 0`) with weights `Λ` and decay `β` summed to at most `ε` (`BoundsDecay`), and let `1 / M`
and `t`, `1 / t` for `t ∈ A` be integral off `T`. Let `Γ` bound the squared sums of the weights,
relative to the constants of Poisson summation. Then the `i`-th sum of densities is at most the
product of the first `i` constants times `massBound + 2 i Γ ε`. -/
lemma densitySum_le [S.IsAdmissible]
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T ∧ ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T) (K : S.IsGlobalSieveSystem T n J massBound Λ β)
    (hβ : S.BoundsDecay T β ε) (hε : 0 ≤ ε) (hΛ : ∀ (i : ℕ) (p : GlobalHead T), 0 ≤ Λ i p) {Γ : ℝ}
    (hΓ : ∀ i ≤ n, (∑ p : Fin i → A, Λ i (S.scaledHead T p 1)) ^ 2 ≤
      Γ * ∏ a ∈ range i, S.poissonConst a) {i : ℕ} (hi : i ≤ n + 1) :
    S.densitySum T A J i ≤ (∏ a ∈ range i, S.poissonConst a) * (massBound + 2 * i * Γ * ε) := by
  induction i with
  | zero => simpa [densitySum] using (re_le_norm _).trans (K.norm_bot_le _ _)
  | succ i ih =>
    have hc : 0 ≤ S.poissonConst i := S.poissonConst_nonneg i
    have hi_le : i ≤ n := Nat.le_of_succ_le_succ hi
    grw [S.densitySum_succ_le_mul_densitySum_add T hA hM_inv K hβ hε hΛ hi_le,
      ih (Nat.le_succ_of_le hi_le), hΓ i hi_le, prod_range_succ, Nat.cast_succ]
    exact le_of_eq (by ring)

end OneEntryFewer

section

omit [WeilData E]

/-- Under the standing hypotheses `IsAdmissible`, each scale
`frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, where κ_v is the real number `realM v`, is at most
`|realM v| ^ (2 ϱ) / N`. -/
lemma frameScaleSq_le_realM_pow [S.IsAdmissible] (v : InfinitePlace E) (a : ℕ) :
    S.frameScaleSq v a ≤ |S.realM v| ^ (2 * 𝔰.ϱ) / S.N := by
  rw [frameScaleSq, ← pow_abs_two_mul]
  gcongr
  exacts [S.one_le_abs_realM v, Nat.sub_le _ _]

/-- The product of the absolute values of the numbers `κ_v = M Φ v ϖ / (2πi)` over the infinite
places is `(M rd / (2π)) ^ f`, because `ϖ` generates the different. Here `rd` is the root
discriminant of `E`, and `f` is the number of infinite places. -/
lemma prod_abs_realM : ∏ v : InfinitePlace E, |S.realM v| =
    (S.M * rootDiscr E / (2 * π)) ^ numInfPlaces E := by
  -- The square of `∏ ‖Φ v ϖ‖` is the norm of the different, that is `|discr E| = rd ^ (2 f)`.
  have h_absNorm : Ideal.absNorm (Ideal.span {S.deltaE}) = (discr E).natAbs := by
    rw [← S.span_deltaE, absNorm_differentIdeal E]
  have h_norm : |(Algebra.norm ℚ S.deltaE.val : ℝ)| = |(discr E : ℝ)| := by
    simpa [← Algebra.coe_norm_int] using congrArg (Nat.cast : ℕ → ℝ) h_absNorm
  have h_varpi : ∏ v : InfinitePlace E, v S.deltaE.val = rootDiscr E ^ numInfPlaces E := by
    rw [← sq_eq_sq₀ (by positivity) (pow_pos (rootDiscr_pos E) _).le,
      ← abs_discr_eq_rootDiscr_pow, ← h_norm]
    simpa [prod_pow] using InfinitePlace.prod_eq_abs_norm S.deltaE.val
  simp only [abs_realM_eq, ← InfinitePlace.apply, mk_Φ, Finset.prod_div_distrib,
    prod_mul_distrib, prod_const, card_univ, h_varpi, div_pow, mul_pow]

/-- The product over the infinite places of the constants in the decay: `scaledVolumeRatio`, a
constant of the shape, times the power `k - n⁷` of `|κ_v| ^ (2 ϱ + 1) / (M N)`, where
`κ_v = S.realM v` is the real number `M * Φ v ϖ / (2πi)`. For admissible `S`, the base of this power
bounds the inverses of the scales of the frequencies in `BoundsDecay`. -/
noncomputable def decayConst : ℝ :=
  ∏ v : InfinitePlace E,
    𝔰.scaledVolumeRatio * (|S.realM v| ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N)) ^ (𝔰.k - 𝔰.n ^ 7)

lemma decayConst_nonneg : 0 ≤ S.decayConst := by
  have ratio_pos : 0 < 𝔰.scaledVolumeRatio := by simp [Shape.scaledVolumeRatio, pi_pos]
  unfold decayConst
  positivity

omit [T.StarStable] in
/-- Let `κ_v = S.realM v` be the real number `M Φ v ϖ / (2πi)`, with `ϖ` the generator of the
different. Let `S` satisfy the standing hypotheses (`IsAdmissible`), among them
`1 ≤ |κ_v| ≤ b ^ 23`. For a frequency `ξ`, with components `ξ.1 v` at the infinite places `v` and
`ξ.2` in `LocProd T`, the product of the completions at `T`, let the decay at `ξ` be the product
over `v` of `scaledVolumeRatio * b ^ (2000 n⁹) * dampedPower (k - n⁷) ‖ξ.1 v‖⁻¹`, times
`frequencyDecay T ξ.2`. Its sum over any finite set of nonzero `T`-integers, read with the scales
`c v / frameScaleSq v a` for any entry `a` and any `c` with `‖c v‖⁻¹ ≤ |κ_v| / M` (`BoundsDecay`),
is at most `decayConst` times `b ^ (2002 n⁹ f)`, with `f` the number of infinite places. -/
lemma boundsDecay_prod [S.IsAdmissible] :
    S.BoundsDecay T
      (fun ξ : (InfinitePlace E → ℂ) × LocProd T ↦
        (∏ v : InfinitePlace E, 𝔰.scaledVolumeRatio * S.b ^ (2000 * 𝔰.n ^ 9) *
          dampedPower (𝔰.k - 𝔰.n ^ 7) ‖ξ.1 v‖⁻¹) * S.frequencyDecay T ξ.2)
      (S.decayConst * S.b ^ (2002 * 𝔰.n ^ 9 * numInfPlaces E)) := by
  -- Sum the frequencies with `x v = realM v ^ (2 * ϱ + 1) / (M * N)`, where `|x v| ≤ B`.
  intro a c hc X hX₀ hXT
  have hb : 1 ≤ S.b := S.one_le_b
  have MN_pos : 0 < S.M * S.N := by simp [Nat.pos_iff_ne_zero, Nat.Prime.ne_zero, S.N_prime.ne_zero]
  have ratio_pos : 0 < 𝔰.scaledVolumeRatio := by simp [Shape.scaledVolumeRatio, pi_pos]
  let x (v : InfinitePlace E) : ℝ := S.realM v ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N)
  let B : ℝ := (S.b ^ 23) ^ (2 * 𝔰.ϱ + 1)
  have abs_x (v : InfinitePlace E) : |x v| = |S.realM v| ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N) := by
    simp [x, abs_div]
  have lower (v : InfinitePlace E) : ‖c v / S.frameScaleSq v a‖⁻¹ ≤ |x v| := by
    have h_pos : 0 < S.frameScaleSq v a := S.frameScaleSq_pos v a
    calc
      _ = ‖c v‖⁻¹ * S.frameScaleSq v a := by simp [div_eq_inv_mul, abs_of_pos h_pos]
      _ ≤ |S.realM v| / S.M * (|S.realM v| ^ (2 * 𝔰.ϱ) / S.N) := by
        grw [hc v, S.frameScaleSq_le_realM_pow v a]
      _ = |x v| := by rw [abs_x, pow_succ', div_mul_div_comm]
  have upper (v : InfinitePlace E) : |x v| ≤ B := by
    grw [abs_x, div_le_self (by positivity) (mod_cast MN_pos), S.abs_realM_le]
  have hB : (S.b * B ^ 2) ^ 3 ≤ S.b ^ 𝔰.n ^ 9 := by
    -- Compare the exponents of `b`, using `n² ≤ n⁹` and that `ϱ` is large.
    simp only [B, ← pow_mul, ← pow_succ']
    gcongr
    grw [← Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num : 2 ≤ 9)]
    nlinarith only [S.ten_pow_five_le_varrho]
  have h_sum : ∑ y ∈ X,
      (∏ v, dampedPower (𝔰.k - 𝔰.n ^ 7) ‖c v / S.frameScaleSq v a * Φ v y‖⁻¹) *
        (√(genIndex (ratToPlaces T y)) ^ (𝔰.k - 𝔰.n ^ 7) / denomIndex O (ratToPlaces T y) ^ 3) ≤
      ∏ v, |x v| ^ (𝔰.k - 𝔰.n ^ 7) * S.b ^ 𝔰.n ^ 9 := by
    grw [S.sum_frequencies_le T B _ X _ x (by bound) lower upper hX₀ hXT, hB]
  -- Take the constants out of the sum; after the bound for it the two sides are equal.
  simp_rw [ratPoint, frequencyDecay, prod_mul_distrib, mul_assoc, ← mul_sum, ← mul_assoc, ← sum_mul]
  grw [h_sum]
  simp only [decayConst, abs_x, prod_mul_distrib, prod_const, card_univ]
  exact le_of_eq (by ring)

end

/-- The product of the first `j` entries of a head `p` with entries in `A`. -/
noncomputable def headProduct {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) (j : ℕ) : E :=
  ∏ a ∈ range j, (padTuple (fun l : Fin i ↦ (p l : Eˣ)) 1 a : Eˣ)

omit [CMType E] [WeilData E] in
lemma headProduct_ne_zero {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) (j : ℕ) : headProduct p j ≠ 0 :=
  prod_ne_zero_iff.2 fun _ _ ↦ Units.ne_zero _

omit [WeilData E] [T.StarStable] in
lemma headProduct_mem_ratIntegralOff {A : Finset Eˣ} (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T)
    {i : ℕ} (p : Fin i → A) (j : ℕ) : headProduct p j ∈ ratIntegralOff T := by
  simp [headProduct, hA, padTuple, prod_mem, apply_dite, -Subring.mem_comap]

omit [CMType E] [WeilData E] in
/-- A head `p : Fin i → A` (a tuple of `i` units from `A`) is determined by the products
`headProduct p (j + 1)` of its first `j + 1` entries, for `j < i`. -/
lemma headProduct_injective {A : Finset Eˣ} {i : ℕ} :
    Function.Injective fun (p : Fin i → A) (j : Fin i) ↦ headProduct p (j + 1) := by
  intro p q h_eq
  have h_all : ∀ k ≤ i, headProduct p k = headProduct q k
    | 0, _ => by simp [headProduct]
    | k + 1, hk => congrFun h_eq ⟨k, hk⟩
  -- `p j` is the quotient of two consecutive products.
  funext j
  have h_quot : headProduct p (j + 1) / headProduct p j =
      headProduct q (j + 1) / headProduct q j := by rw [h_all (j + 1) j.isLt, h_all j j.isLt.le]
  simpa [headProduct, prod_range_succ, padTuple, prod_eq_zero_iff, Units.val_inj] using h_quot

omit [WeilData E] [T.StarStable] in
/-- The product formula for the weights. Let `δ ≠ 0` be integral off `T`, and let `r` bound
`‖Φ v δ‖` and `‖c v‖⁻¹` at all infinite places. Then the product of the numbers
`max 1 ‖c v * Φ v δ‖⁻¹` and of the square root of the index `[O : δ O]` at `T` is at most `r ^ f`,
with `f` the number of infinite places. -/
lemma prod_max_inv_norm_mul_sqrt_genIndex_le {δ : E} (hδ₀ : δ ≠ 0) (hδT : δ ∈ ratIntegralOff T)
    {c : InfinitePlace E → ℂ} {r : ℝ} (hc : ∀ v : InfinitePlace E, ‖c v‖⁻¹ ≤ r)
    (hδ : ∀ v : InfinitePlace E, ‖Φ v δ‖ ≤ r) :
    (∏ v : InfinitePlace E, max 1 ‖c v * Φ v δ‖⁻¹) * √(genIndex (ratToPlaces T δ)) ≤
      r ^ numInfPlaces E := by
  have h_place (v : InfinitePlace E) : max 1 ‖c v * Φ v δ‖⁻¹ * ‖Φ v δ‖ ≤ r := by
    rw [max_mul_of_nonneg _ _ (norm_nonneg _), one_mul, norm_mul, mul_inv,
      inv_mul_cancel_right₀ (by simpa using hδ₀)]
    exact max_le (hδ v) (hc v)
  grw [sqrt_genIndex_le_prod_norm T hδ₀ hδT, ← prod_mul_distrib, h_place, prod_const, card_univ]

section

omit [WeilData E]

/-- Let `S` satisfy the standing hypotheses (`IsAdmissible`), among them `1 ≤ |κ_v|` and
`N ≤ b ^ (60 n)` for the prime `N = S.N`, the size parameter `b = S.b` and `n = ϱ + 1`. For `j ≤ ϱ`,
the inverse of the product of the scales `frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, `a < j`, is at
most `b ^ (60 n²)`. -/
lemma inv_norm_prod_frameScaleSq_le [S.IsAdmissible] (v : InfinitePlace E) {j : ℕ} (hj : j ≤ 𝔰.ϱ) :
    ‖(∏ a ∈ range j, S.frameScaleSq v a : ℂ)‖⁻¹ ≤ S.b ^ (60 * 𝔰.n ^ 2) :=
  calc
    _ = (S.N : ℝ) ^ j / ∏ a ∈ range j, |S.realM v| ^ (2 * (𝔰.ϱ - a)) := by simp [frameScaleSq]
    _ ≤ (S.N : ℝ) ^ j := div_le_self (by positivity)
      (Finset.one_le_prod₀ fun a _ ↦ one_le_pow₀ (S.one_le_abs_realM v))
    _ ≤ (S.b ^ (60 * 𝔰.n)) ^ 𝔰.n := by
      grw [N_le, pow_le_pow_right₀ (one_le_pow₀ S.one_le_b) (hj.trans 𝔰.ϱ.le_succ)]
    _ = _ := by ring

/-- The weight of a head `p` of length `i`, read at the infinite places and at `T`: a product over
the partial products `δ = p 0 * ⋯ * p l`, `l < i`. At an infinite place the factor (`headWeight`) is
`max 1 ‖δ‖⁻¹ ^ n⁶` if `‖δ‖ ≤ b ^ (60 n²)` and `0` otherwise. At `T` the factor (`finHeadWeight`) is
`[O : δ O] ^ (n⁶ / 2)` if `δ` lies in `O` and `0` otherwise. -/
noncomputable def globalWeight (i : ℕ) (p : GlobalHead T) : ℝ :=
  (∏ v : InfinitePlace E, headWeight (S.b ^ (60 * 𝔰.n ^ 2)) (𝔰.n ^ 6) i ((·.1 v) ∘ p)) *
    finHeadWeight (𝔰.n ^ 6) i ((·.2) ∘ p)

omit [T.StarStable] in
lemma globalWeight_nonneg (i : ℕ) (p : GlobalHead T) : 0 ≤ S.globalWeight T i p := by
  unfold globalWeight headWeight finHeadWeight
  positivity

open scoped Classical in
omit [T.StarStable] in
/-- Let `S` satisfy the standing hypotheses (`IsAdmissible`), with size parameter `b = S.b` and
`n = ϱ + 1`. The head `scaledHead T p 1` has first entries `p` and later entries `1`. The entry `a`
is scaled at the infinite place `v` by `frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N`, where
`κ_v = S.realM v` and `N = S.N`. Its weight (`globalWeight`) is a product over the products
`δ = headProduct p (j + 1)` of the first entries of `p`. At an infinite place `v`, let `Φ v` be the
chosen complex embedding inducing `v`, and let `c j v` be the product of the scales of these
entries. There the factor is `max 1 ‖c j v * Φ v δ‖⁻¹ ^ n⁶` if `‖c j v * Φ v δ‖ ≤ b ^ (60 n²)`, and
`0` otherwise. At `T` the factor is `[O : δ O] ^ (n⁶ / 2)` if `ratToPlaces T δ` lies in `O`, and `0`
otherwise. Here `O` is the ring of integers of the product of the completions at `T`. -/
lemma globalWeight_scaledHead {A : Finset Eˣ} {i : ℕ} (p : Fin i → A) :
    let c (j : Fin i) (v : InfinitePlace E) : ℂ := ∏ a ∈ range (j + 1), S.frameScaleSq v a
    S.globalWeight T i (S.scaledHead T p 1) = ∏ j : Fin i,
      (∏ v : InfinitePlace E,
        if ‖c j v * Φ v (headProduct p (j + 1))‖ ≤ S.b ^ (60 * 𝔰.n ^ 2) then
          max 1 ‖c j v * Φ v (headProduct p (j + 1))‖⁻¹ ^ 𝔰.n ^ 6 else 0) *
      if ratToPlaces T (headProduct p (j + 1)) ∈ O then
        √(genIndex (ratToPlaces T (headProduct p (j + 1)))) ^ 𝔰.n ^ 6 else 0 := by
  intro c
  have h_inf (j : Fin i) (v : InfinitePlace E) :
      ∏ a ∈ range (j + 1), ((S.scaledHead T p 1 a).1 v : ℂ) =
        c j v * Φ v (headProduct p (j + 1)) := by
    simp [c, headProduct, scaledHead, scaledEntry, ratPoint, unitOrOne,
      (S.frameScaleSq_pos _ _).ne', prod_mul_distrib]
  have h_fin (j : Fin i) : ∏ a ∈ range (j + 1), ((S.scaledHead T p 1 a).2 : LocProd T) =
      ratToPlaces T (headProduct p (j + 1)) := by
    simp [headProduct, scaledHead, scaledEntry, ratPoint, unitOrOne, IsUnit.map]
  simp only [globalWeight, headWeight, finHeadWeight, prod_range (n := i), Function.comp_apply,
    h_inf, h_fin]
  rw [Finset.prod_comm, ← prod_mul_distrib]

omit [T.StarStable] in
/-- Let `S` satisfy the standing hypotheses (`IsAdmissible`), and let `p` be a head of length
`i ≤ ϱ` with entries in a finite set `A` of numbers integral off `T`. Suppose the weight
(`globalWeight`) of `scaledHead T p 1`, the head with first entries `p` and later entries `1` read
in the scaled frame, is not zero. Then the products of the first entries of `p` are integers of `E`
of modulus at most `b ^ (120 n²)` at all infinite places. -/
lemma isIntegral_headProduct_and_norm_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) {p : Fin i → A}
    (hp : S.globalWeight T i (S.scaledHead T p 1) ≠ 0) (j : Fin i) :
    IsIntegral ℤ (headProduct p (j + 1)) ∧
      ∀ v : InfinitePlace E, ‖Φ v (headProduct p (j + 1))‖ ≤ S.b ^ (120 * 𝔰.n ^ 2) := by
  classical
  rw [globalWeight_scaledHead] at hp
  obtain ⟨h_inf, h_fin⟩ := mul_ne_zero_iff.1 (prod_ne_zero_iff.1 hp j (mem_univ j))
  refine ⟨?_, fun v ↦ ?_⟩
  · -- integral at `T` and off `T`
    rw [← algebraMap_mem_Ô, mem_Ô_iff T]
    exact ⟨(ite_ne_right_iff.1 h_fin).1, headProduct_mem_ratIntegralOff T hA p (j + 1)⟩
  · have hb : 1 ≤ S.b := S.one_le_b
    let c : ℂ := ∏ a ∈ range (j + 1), S.frameScaleSq v a
    have h_small : ‖c * Φ v (headProduct p (j + 1))‖ ≤ S.b ^ (60 * 𝔰.n ^ 2) :=
      (ite_ne_right_iff.1 (prod_ne_zero_iff.1 h_inf v (mem_univ v))).1
    calc
      _ = ‖c‖⁻¹ * ‖c * Φ v (headProduct p (j + 1))‖ := by
        simp [c, prod_ne_zero_iff, (S.frameScaleSq_pos v _).ne']
      _ ≤ S.b ^ (60 * 𝔰.n ^ 2) * S.b ^ (60 * 𝔰.n ^ 2) := by
        grw [h_small, S.inv_norm_prod_frameScaleSq_le v (j.isLt.trans_le hi)]
      _ = _ := by ring

omit [T.StarStable] in
/-- The largest weight. Let `S` satisfy the standing hypotheses (`IsAdmissible`), and let `p` be a
tuple of length `i ≤ ϱ` with entries integral off `T`. The head `scaledHead T p 1` has first entries
`p` and later entries `1`, with the entry `a` scaled at the infinite place `v` by
`frameScaleSq v a = κ_v ^ (2 (ϱ - a)) / N` (`κ_v = S.realM v`, `N = S.N`). Its weight
(`globalWeight`) is a product over the partial products `δ` of its first `i` entries, of
`max 1 ‖δ‖⁻¹ ^ n⁶` or `0` at each infinite place and of `[O : δ O] ^ (n⁶ / 2)` or `0` at `T`, with
`O` the integers at `T`. This weight is at most `b ^ (120 n⁸ f i)`. Here `b = S.b` is the size
parameter, `n = ϱ + 1`, and `f` is the number of infinite places. -/
lemma globalWeight_scaledHead_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) (p : Fin i → A) :
    S.globalWeight T i (S.scaledHead T p 1) ≤ S.b ^ (120 * 𝔰.n ^ 8 * numInfPlaces E * i) := by
  have hb : 1 ≤ S.b := S.one_le_b
  by_cases hp : S.globalWeight T i (S.scaledHead T p 1) = 0
  · exact hp.trans_le (by positivity)
  -- Each product `δ j` is small, so it contributes at most `(b ^ (120 n²)) ^ (f n⁶)`.
  let c (j : Fin i) (v : InfinitePlace E) : ℂ := ∏ a ∈ range (j + 1), S.frameScaleSq v a
  let δ (j : Fin i) : E := headProduct p (j + 1)
  have h_factor (j : Fin i) : (∏ v, max 1 ‖c j v * Φ v (δ j)‖⁻¹) *
      √(genIndex (ratToPlaces T (δ j))) ≤ (S.b ^ (120 * 𝔰.n ^ 2)) ^ numInfPlaces E :=
    prod_max_inv_norm_mul_sqrt_genIndex_le T (headProduct_ne_zero p _)
      (headProduct_mem_ratIntegralOff T hA p _)
      (fun v ↦ (S.inv_norm_prod_frameScaleSq_le v (j.isLt.trans_le hi)).trans
        (pow_le_pow_right₀ hb (by lia)))
      (S.isIntegral_headProduct_and_norm_le T hA hi hp j).2
  rw [globalWeight_scaledHead]
  calc
    _ ≤ ∏ j : Fin i, (∏ v, max 1 ‖c j v * Φ v (δ j)‖⁻¹ ^ 𝔰.n ^ 6) *
        √(genIndex (ratToPlaces T (δ j))) ^ 𝔰.n ^ 6 := by
      gcongr ∏ j, (∏ v, ?_) * ?_ with j _ v
      all_goals
        split_ifs
        exacts [le_rfl, by positivity]
    _ ≤ ∏ _j : Fin i, ((S.b ^ (120 * 𝔰.n ^ 2)) ^ numInfPlaces E) ^ 𝔰.n ^ 6 := by
      simp only [prod_pow (univ : Finset (InfinitePlace E)), ← mul_pow]
      grw [h_factor]
    _ = _ := by
      rw [prod_const, card_univ, Fintype.card_fin]
      ring

omit [T.StarStable] in
/-- The sum of the weights of the heads of length `i ≤ ϱ` with entries in a finite set `A` of
numbers integral off `T` is at most `b ^ (130 n⁹ f)`: the number of heads whose products are small
integers, times the largest weight. Here `b = S.b` is the size parameter of the admissible filling
data `S`, `n = ϱ + 1`, and `f` is the number of infinite places. -/
lemma sum_globalWeight_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) :
    ∑ p : Fin i → A, S.globalWeight T i (S.scaledHead T p 1) ≤
      S.b ^ (130 * 𝔰.n ^ 9 * numInfPlaces E) := by
  have hb : 1 ≤ S.b := S.one_le_b
  let P : Finset (Fin i → A) := {p | S.globalWeight T i (S.scaledHead T p 1) ≠ 0}
  have h_card : (#P : ℝ) ≤ (1 + 2 * S.b ^ (120 * 𝔰.n ^ 2)) ^ (i * numInfPlaces E * 2) := by
    rw [← ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_natCast]
    simpa using encard_le_of_isIntegral_norm_le (A := (P : Set (Fin i → A)))
      (fun p (j : Fin i) ↦ headProduct p (j + 1)) (by positivity)
      (fun p hp ↦ S.isIntegral_headProduct_and_norm_le T hA hi (mem_filter.1 hp).2)
      headProduct_injective.injOn
  have h_base : 1 + 2 * S.b ^ (120 * 𝔰.n ^ 2) ≤ S.b ^ (120 * 𝔰.n ^ 2 + 1) := by
    rw [pow_succ S.b]
    nlinarith only [S.thousand_le_b, one_le_pow₀ hb (n := 120 * 𝔰.n ^ 2)]
  calc
    _ = ∑ p ∈ P, S.globalWeight T i (S.scaledHead T p 1) := (sum_filter_ne_zero univ).symm
    _ ≤ #P * S.b ^ (120 * 𝔰.n ^ 8 * numInfPlaces E * i) := by
      grw [S.globalWeight_scaledHead_le T hA hi, sum_const, nsmul_eq_mul]
    _ ≤ (S.b ^ (120 * 𝔰.n ^ 2 + 1)) ^ (𝔰.n * numInfPlaces E * 2) *
        S.b ^ (120 * 𝔰.n ^ 8 * numInfPlaces E * 𝔰.n) := by
      grw [h_card, h_base, hi.trans 𝔰.ϱ.le_succ, hi.trans 𝔰.ϱ.le_succ]
      exact one_le_pow₀ hb
    _ ≤ _ := by
      rw [← pow_mul, ← pow_add]
      gcongr
      obtain ⟨m, hm⟩ : ∃ m : ℕ, 𝔰.ϱ = 10 ^ 5 + m := exists_add_of_le S.ten_pow_five_le_varrho
      simp only [Shape.n, hm]
      lia

/-- For `i ≤ ϱ`, the product of the first `i` constants of Poisson summation is at least
`b ^ (-100 n² f)`, with `f` the number of infinite places. -/
lemma one_le_pow_mul_prod_poissonConst [S.IsAdmissible] {i : ℕ} (hi : i ≤ 𝔰.ϱ) :
    1 ≤ S.b ^ (100 * 𝔰.n ^ 2 * numInfPlaces E) * ∏ a ∈ range i, S.poissonConst a := by
  -- Use `frameScaleSq v a ≤ b ^ (46 * ϱ)` and the value `(2 / rd) ^ f` of `volÔ E`.
  have hb : 1 ≤ S.b := S.one_le_b
  have rd_pos : 0 < rootDiscr E := rootDiscr_pos E
  have scale_le (v : InfinitePlace E) (a : ℕ) : S.frameScaleSq v a ≤ (S.b ^ 23) ^ (2 * 𝔰.ϱ) := by
    grw [S.frameScaleSq_le_realM_pow, div_le_self (by positivity) (mod_cast S.N_prime.pos),
      S.abs_realM_le]
  calc
    _ ≤ S.b ^ (100 * 𝔰.n ^ 2 * numInfPlaces E) * ∏ _a ∈ range i,
          (S.b ^ numInfPlaces E)⁻¹ / ∏ _v : InfinitePlace E, ((S.b ^ 23) ^ (2 * 𝔰.ϱ)) ^ 2 := by
      simp only [← pow_mul, prod_const, card_univ, Finset.card_range, div_pow, inv_pow, field,
        ← pow_add]
      gcongr
      grw [hi]
      lia
    _ ≤ _ := by
      simp only [poissonConst]
      grw [volÔ_eq, scale_le, half_le_self (by bound), S.rootDiscr_le_b]
      exacts [(S.frameScaleSq_pos _ _).le, prod_pos fun v _ ↦ pow_pos (S.frameScaleSq_pos v _) 2]

omit [T.StarStable] in
/-- Let `S` satisfy the standing hypotheses `IsAdmissible`. Let `b = S.b`, `ϱ = 𝔰.ϱ`, `n = ϱ + 1`,
and let `f` be the number of infinite places. Let `A` be a finite set of units of `E` integral off
`T`, and let `i ≤ ϱ`. Sum, over heads `p` of length `i` with entries in `A`, the weight
`globalWeight T i` of the head `scaledHead T p 1`. The square of this sum is at most
`b ^ (400 n⁹ f)` times the product of the first `i` constants `poissonConst a` of Poisson
summation. -/
lemma sq_sum_globalWeight_le [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T) {i : ℕ} (hi : i ≤ 𝔰.ϱ) :
    (∑ p : Fin i → A, S.globalWeight T i (S.scaledHead T p 1)) ^ 2 ≤
      S.b ^ (400 * 𝔰.n ^ 9 * numInfPlaces E) * ∏ a ∈ range i, S.poissonConst a := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_prod : 0 ≤ ∏ a ∈ range i, S.poissonConst a :=
    prod_nonneg fun a _ ↦ S.poissonConst_nonneg a
  have h_exp : 130 * 𝔰.n ^ 9 * numInfPlaces E * 2 + 100 * 𝔰.n ^ 2 * numInfPlaces E ≤
      400 * 𝔰.n ^ 9 * numInfPlaces E := by
    grw [Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num : 2 ≤ 9)]
    lia
  calc
    _ ≤ (S.b ^ (130 * 𝔰.n ^ 9 * numInfPlaces E)) ^ 2 *
        (S.b ^ (100 * 𝔰.n ^ 2 * numInfPlaces E) * ∏ a ∈ range i, S.poissonConst a) := by
      grw [← S.one_le_pow_mul_prod_poissonConst hi, mul_one, S.sum_globalWeight_le T hA hi]
      exact Finset.sum_nonneg fun p _ ↦ S.globalWeight_nonneg T i _
    _ ≤ _ := by grw [← mul_assoc, ← pow_mul, ← pow_add, h_exp]

end

omit [WeilData E] [T.StarStable] in
/-- The sieve. Let `b = S.b`, `M = S.M` and `N = S.N` be the size parameter, the level and the prime
of the admissible filling data `S`, let `k`, `ϱ`, `n = ϱ + 1` be the parameters of its shape `𝔰`,
and let `f` be the number of infinite places. Let `U ⊆ A`, and let `1 / M` and `t`, `1 / t` for
`t ∈ A` be integral off `T`. Let the forms `J_T i` on pairs of heads (sequences of units) at `T`
satisfy the axioms of the sieve (`SieveSystem`) in length `ϱ`: for `i ≤ ϱ`, `J_T i` is the integral
of `J_T (i + 1)` over a common entry at position `i`, read as a unit (`unitOrOne`); the top form
`J_T n` is continuous, and positive semidefinite on heads with a common entry at position `ϱ`; the
mass `J_T 0` has modulus at most `mass_T`; and the decay `frequencyDecay` times the weights
`finHeadWeight` bounds the transforms for `S.charOnPlaces T` and the forms at heads with entries
`w`, `w'` whose frequency `(1 / w - 1 / w') / M` is a unit. Multiply `J_T` by the forms `bandLimit`
that are part of the Bessel systems `S.besselSystem v` at the infinite places: they satisfy the same
axioms over `ℂ`, with mass at most `(1 + b ^ (-10)) / deg`.

The real part of the sum of the products of the top forms `bandLimit n` and `J_T n` over all pairs
of heads with entries in `A` and a common last entry in `U` is at most the product of the constants
of Poisson summation times the sum of the product of the bounds for the masses and of the error
`b ^ (2403 n⁹ f) * decayConst`. The heads have first entries `p`, then `t`, then `1` (`padTuple`).
At `T` they are `y p t`; at the infinite place `v` they are `x v p t`, with the entry `i` scaled by
`frameScaleSq v i = κ_v ^ (2 (ϱ - i)) / N`, where `κ_v = S.realM v`. The constants are `poissonConst
i = volÔ E / ∏ v, frameScaleSq v i ^ 2`, with `volÔ E` the volume of the integral finite adeles, and
`decayConst = ∏ v, scaledVolumeRatio * (|κ_v| ^ (2 ϱ + 1) / (M N)) ^ (k - n⁷)`. -/
theorem sieve [S.IsAdmissible] {A : Finset Eˣ}
    (hA : ∀ t ∈ A, (t : E) ∈ ratIntegralOff T ∧ ((t⁻¹ : Eˣ) : E) ∈ ratIntegralOff T)
    (hM_inv : (S.M : E)⁻¹ ∈ ratIntegralOff T)
    {J_T : ℕ → (ℕ → (LocProd T)ˣ) → (ℕ → (LocProd T)ˣ) → ℂ} {mass_T : ℝ} {U : Finset Eˣ}
    (hJ_T : SieveSystem unitOrOne
      (fun w : (LocProd T)ˣ ↦ ratToPlaces T (S.M : E)⁻¹ * ((w⁻¹ : (LocProd T)ˣ) : LocProd T))
      𝔰.ϱ J_T (S.charOnPlaces T) mass_T (finHeadWeight (𝔰.n ^ 6)) (S.frequencyDecay T))
    (hU : U ⊆ A) :
    -- the heads at the infinite place `v`
    let x (v : InfinitePlace E) (p : Fin 𝔰.ϱ → A) (t : Eˣ) (i : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v i * Φ v (padTuple (fun j : Fin 𝔰.ϱ ↦ (p j : Eˣ)) t i : Eˣ))
    -- the heads at `T`
    let y (p : Fin 𝔰.ϱ → A) (t : Eˣ) : ℕ → (LocProd T)ˣ :=
      Units.map (ratToPlaces T) ∘ padTuple (fun j : Fin 𝔰.ϱ ↦ (p j : Eˣ)) t
    (∑ t ∈ U, ∑ p : Fin 𝔰.ϱ → A, ∑ q : Fin 𝔰.ϱ → A,
        (∏ v : InfinitePlace E, (S.besselSystem v).bandLimit 𝔰.n (x v p t) (x v q t)) *
          J_T 𝔰.n (y p t) (y q t)).re ≤
      (∏ i ∈ range 𝔰.n, S.poissonConst i) *
        ((∏ v : InfinitePlace E, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) * mass_T +
          S.b ^ (2403 * 𝔰.n ^ 9 * numInfPlaces E) * S.decayConst) := by
  -- Remove all entries in the product system. The error is `2 n Γ ε`: here `ε` bounds the decay
  -- summed over the nonzero frequencies, and `Γ` times the product of the first `i` constants of
  -- Poisson summation bounds the squared sum of the weights of the heads of length `i`.
  have hb : 1 ≤ S.b := S.one_le_b
  have h_decay : 0 ≤ S.decayConst := S.decayConst_nonneg
  intro x y
  let J (i : ℕ) (p q : GlobalHead T) : ℂ :=
    (∏ v, (S.besselSystem v).bandLimit i ((·.1 v) ∘ p) ((·.1 v) ∘ q)) *
      J_T i ((·.2) ∘ p) ((·.2) ∘ q)
  let massBound : ℝ := (∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) * mass_T
  let Γ : ℝ := S.b ^ (400 * 𝔰.n ^ 9 * numInfPlaces E)
  let ε : ℝ := S.decayConst * S.b ^ (2002 * 𝔰.n ^ 9 * numInfPlaces E)
  have K : S.IsGlobalSieveSystem T 𝔰.ϱ J massBound (S.globalWeight T) fun ξ ↦
      (∏ v, 𝔰.scaledVolumeRatio * S.b ^ (2000 * 𝔰.n ^ 9) * dampedPower (𝔰.k - 𝔰.n ^ 7) ‖ξ.1 v‖⁻¹) *
        S.frequencyDecay T ξ.2 :=
    hJ_T.pi fun v ↦ (S.besselSystem v).hasLocalBounds.1
  have hx (v : InfinitePlace E) (p : Fin 𝔰.ϱ → A) (t : Eˣ) :
      (·.1 v) ∘ S.scaledHead T p t = x v p t := rfl
  have hy (p : Fin 𝔰.ϱ → A) (t : Eˣ) : (·.2) ∘ S.scaledHead T p t = y p t := by
    ext
    simp [y, scaledHead, scaledEntry, ratPoint, unitOrOne, IsUnit.map]
  have len_le : 2 * (𝔰.ϱ + 1 : ℕ) ≤ S.b ^ (𝔰.n ^ 9 * numInfPlaces E) := by
    have h_nat : 2 * (𝔰.ϱ + 1) ≤ 𝔰.k := by linarith [S.thousand_mul_le_k]
    calc
      _ ≤ (𝔰.k : ℝ) := mod_cast h_nat
      _ ≤ S.b := S.k_le_b
      _ ≤ _ := le_self_pow₀ hb (by simp [Fintype.card_ne_zero])
  calc
    _ = ∑ t ∈ U, (S.entryDensity T A J 𝔰.ϱ (S.scaledEntry T 𝔰.ϱ t)).re := by
      simp only [re_sum, entryDensity_scaledEntry, J, hx, hy]
    _ ≤ S.densitySum T A J 𝔰.n :=
      sum_le_sum_of_subset_of_nonneg hU fun t _ _ ↦ (S.entryDensity_nonneg T K le_rfl _).1
    _ ≤ (∏ a ∈ range 𝔰.n, S.poissonConst a) * (massBound + 2 * (𝔰.ϱ + 1 : ℕ) * Γ * ε) :=
      S.densitySum_le T hA hM_inv K (S.boundsDecay_prod T) (by positivity) (S.globalWeight_nonneg T)
        (fun i ↦ S.sq_sum_globalWeight_le T fun t ht ↦ (hA t ht).1) le_rfl
    _ ≤ (∏ a ∈ range 𝔰.n, S.poissonConst a) *
        (massBound + S.b ^ (𝔰.n ^ 9 * numInfPlaces E) * Γ * ε) := by
      grw [len_le]
      exact prod_nonneg fun a _ ↦ S.poissonConst_nonneg a
    _ = _ := by ring

end New.Filling
end
end

/-!
# The place and level of a set of primes, orbit sums and the set of entries

This file sets up the local theory at a finite set `T` of finite places, stable under conjugation.
It defines the projection `New.Filling.toPlaces` of the finite adelic unitary group to `T` and the
condition `New.Filling.IsIntegralOff` of being integral off `T`. It also defines the orbit sums
`New.Filling.cosetAmplitude`, the finite set `New.Filling.entrySet` of entries and the condition
`New.Filling.IsFillingData`. It shows that the product `New.LocProd T` of the completions at `T` is
a finite place that carries such a datum.

## Main definitions and results

* `New.Filling.exists_isIntegralOff_toPlaces_eq`: every point of the unitary group at `T` is the
  projection of a finite adelic point that is integral off `T`.
* `New.Filling.exists_isFillingData`: `New.LocProd T` is a finite place (`New.Floors.IntegralPlace`)
  with a place datum satisfying `New.Filling.IsFillingData`.

Notions from other files:
* `New.Filling.latticeStabilizer`, `New.Filling.principalLevel`: The group `K` of integral points of
  the finite adelic unitary group, and the kernel `K(M)` of its reduction modulo `M`;
  `New.Floors.PlaceData.congruenceSubgroup` is the group `K(M)` at `T`.
* `New.Filling.amplitude`: The integral of β_c(y) β_c'(γ⁻¹y) W(y) ⊗ W(γ⁻¹y)^* over the infinite
  points y, with β_c the cutoff `New.Filling.classCutoff` and W the full or the cut Bessel function
  at infinity, according to the argument `side`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

namespace New.Filling

open NumberField MeasureTheory Matrix ENNReal Fintype Floors FloorGroups Function
  ComplexOrder SemilocalField Measure Filter Complex Set

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape}

/-! ### Orbit sums, the set of entries and the projection to `T` -/

section

variable (S : Filling E 𝔰) (T : Finset (FinPlace E)) [T.StarStable]

/-- The element `x` of the finite adelic unitary group and its inverse have entries integral at
every place outside `T`. -/
abbrev IsIntegralOff (x : S.GFin) : Prop := x.val ∈ intGL 𝔰.BesselIndex (integralOff T)

/-- The sum of the amplitudes of `u γ u'⁻¹`, for the Bessel function named by `side` (full or cut),
over the pairs `(u, u')` of rational points of the unipotent group 𝖴 for which `u γ u'⁻¹` lies over
the block `(c, s, c')`. -/
noncomputable def cosetAmplitude (side : FullOrCut) (c : S.Classes) (s : S.ResidueGL)
    (c' : S.Classes) (γ : S.G E) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
  ∑' x : (S.ratMiddle E).besselU × (S.ratMiddle E).besselU,
    (S.termsOver c s c').indicator (S.amplitude side c c') (x.1.val * γ * x.2.val⁻¹)

/-- The nonzero integers `δ` of `E` with `‖δ‖ ^ 2 ≤ b ^ (270 n ^ 2)` at every infinite place. The
nonzero leading minors of a term with nonzero cut amplitude are such integers
(`New.Filling.leadingMinor_mem_boundedNonzeroIntegers`). -/
def boundedNonzeroIntegers : Set E :=
  {δ : E | δ ≠ 0 ∧ IsIntegral ℤ δ ∧ ∀ v : InfinitePlace E, ‖Φ v δ‖ ^ 2 ≤ S.b ^ (270 * 𝔰.n ^ 2)}

/-- The set `S.boundedNonzeroIntegers` is finite. It consists of the nonzero integers `δ` of `E`
with `‖δ‖ ^ 2 ≤ b ^ (270 n ^ 2)` at every infinite place of `E`. -/
lemma finite_boundedNonzeroIntegers : S.boundedNonzeroIntegers.Finite := by
  refine (Embeddings.finite_of_norm_le E ℂ √(S.b ^ (270 * 𝔰.n ^ 2))).subset ?_
  rintro δ ⟨-, h_int, h_le⟩
  refine ⟨h_int, fun φ ↦ Real.le_sqrt_of_sq_le ?_⟩
  rw [← InfinitePlace.apply, ← mk_Φ (InfinitePlace.mk φ), InfinitePlace.apply]
  exact h_le _

/-- There are finitely many quotients of two elements of `boundedNonzeroIntegers`. -/
lemma finite_quotient_boundedNonzeroIntegers :
    {t : Eˣ | ∃ δ ∈ S.boundedNonzeroIntegers, ∃ δ' ∈ S.boundedNonzeroIntegers, δ / δ' = t}.Finite :=
  Finite.preimage (f := Units.val) Units.val_injective.injOn
    (S.finite_boundedNonzeroIntegers.image2 (fun δ δ' : E ↦ δ / δ') S.finite_boundedNonzeroIntegers)

/-- The finite set 𝒯 of entries: the quotients of two elements of `boundedNonzeroIntegers`. -/
noncomputable def entrySet : Finset Eˣ := S.finite_quotient_boundedNonzeroIntegers.toFinset

/-- The homomorphism from the finite adelic unitary group (lattice basis) to the unitary group
over the product of the completions at T, taking components at T. -/
noncomputable def toPlaces :
    U (S.latticeMiddle (𝔸f E)).splitGram →* U (S.latticeMiddle (LocProd T)).splitGram :=
  U.map (evalPlaces T) (fun x ↦ (star_evalPlaces T x).symm)
    (S.map_splitGram_latticeMiddle (evalPlaces T))

/-- The place datum `F` on the product of the completions at `T` is built on the Gram matrix
`New.Filling.latticeMiddle`, with 3ϱ + 6 further hyperbolic pairs and an orthonormal part of size
`k - (6ϱ + 13)`. It is a large lattice datum for the chosen place structure, its modulus is the
component of `M` at `T`, and the character of the place is `New.Filling.charOnPlaces`. -/
class IsFillingData [P : IntegralPlace (LocProd T)]
    (F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
      (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)) :
    Prop extends P.IsLargeLatticeData F where
  /-- The character of the place is the character of `S` at `T`. -/
  psi_eq : P.ψ = S.charOnPlaces T
  /-- The modulus of `F` is the component of `M` at `T`. -/
  levelUnit_eq : F.levelUnit = S.ideleM.map (evalPlaces T)

/-- A finite adele is integral off T for all sufficiently large finite sets T of finite places. -/
lemma eventually_mem_integralOff (a : 𝔸f E) :
    ∀ᶠ T : Finset (FinPlace E) in Filter.atTop, a ∈ integralOff T := by
  -- It suffices that `T` contain the finitely many places where `a` is not integral.
  have h_fin : {w : FinPlace E | a w ∉ LocInt w}.Finite := a.property
  filter_upwards [eventually_ge_atTop h_fin.toFinset] with T hT
  have h_int (w : FinPlace E) (hw : w ∉ T) : a w ∈ LocInt w :=
    by_contra fun h_not ↦ hw (hT (h_fin.mem_toFinset.2 h_not))
  simpa [integralOff] using h_int

/-- For a finite set `T₀` of nonzero elements of `E` there is a finite set `T` of places, stable
under conjugation, off which the elements of `T₀` are units and the following are integral: the
inverse of the modulus `M`, the lattice basis with its inverse, and the inverse of the natural
number `S.N`. Here `ratIntegralOff T` is the ring of `T`-integers of `E`. -/
theorem exists_places_integralOff (T₀ : Finset Eˣ) :
    ∃ T : Finset (FinPlace E),
      T.StarStable ∧
      (∀ t ∈ T₀, t.val ∈ ratIntegralOff T ∧ t⁻¹.val ∈ ratIntegralOff T) ∧
      Fact (S.ideleM⁻¹.val ∈ integralOff T) ∧
      S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T) ∧
      (S.N : E)⁻¹ ∈ ratIntegralOff T := by
  classical
  -- Every `T` lies in the stable set `T ∪ star T`.
  have h_star : ∃ᶠ T : Finset (FinPlace E) in .atTop, T.StarStable := by
    refine frequently_atTop.2 fun T ↦ ⟨T ∪ T.image star, Finset.subset_union_left, ⟨?_⟩⟩
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem star hw)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
      rw [star_star]
      exact Finset.mem_union_left _ hv
  -- The other conditions ask finitely many adeles to be integral off `T`.
  refine (h_star.and_eventually ?_).exists
  simp [mem_intGL, eventually_mem_integralOff, fact_iff, -eventually_atTop, -Sum.forall]

end

variable [WeilData E] {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable] {x : S.GFin}

section

omit [WeilData E]

/-- Let `w_p = weylElem 𝔰.ϱ p` be the Weyl element with `e_a ↦ p_a e*_a` and `e*_a ↦ e_a / p̄_a` on
the `𝔰.ϱ` hyperbolic pairs of the hermitian space of `S`. At an infinite place `v` with chosen
embedding `Φ v`, its rescaled image `ratToInf` is `w_q`, where `q i` is `Φ v (p i)` times the square
`frameScaleSq v i` of the scale of the `i`-th frame vector, read as a unit by `unitOrOne`. -/
lemma ratToInf_weylElem (p : ℕ → Eˣ) (v : InfinitePlace E) :
    S.ratToInf (weylElem 𝔰.ϱ p) v =
      weylElem 𝔰.ϱ (fun i : ℕ ↦ unitOrOne (S.frameScaleSq v i * Φ v (p i))) := by
  -- Compare entries column by column; each column has one nonzero entry. Conjugating by the scales
  -- `basisScale` multiplies the entries on the pair of floor `a` by `S.frameScaleSq v a` or by its
  -- inverse, and keeps the others.
  ext i j
  simp only [ratToInf_apply, weylElem, weylOn, Matrix.of_apply, Units.isUnit, and_true, and_self]
  rcases j with a | (a | a) | a
  all_goals
    simp [BesselIndex.level, basisScale, frameScaleSq, unitOrOne, two_mul,
      pow_add, Nat.add_sub_assoc, Nat.Prime.ne_zero]
    split_ifs with hi
    · simp [field, ← Complex.ofReal_pow, hi, Nat.Prime.ne_zero]
    · simp

/-- At an infinite place `v`, the rescaled image of `w_p σ` is `w_q` times the rescaled image of
`σ`, where `q i` is `Φ v (p i)` times the squared scale `frameScaleSq v i`. -/
lemma ratToInf_weylElem_mul {σ : S.G E} {p : ℕ → Eˣ} (v : InfinitePlace E) :
    S.ratToInf (weylElem 𝔰.ϱ p * σ) v =
      weylElem 𝔰.ϱ (fun i : ℕ ↦ unitOrOne (S.frameScaleSq v i * Φ v (p i))) * S.ratToInf σ v := by
  rw [map_mul, Pi.mul_apply, ratToInf_weylElem]

/-- Every element `y` of the unitary group over the completions at `T` is the projection of a finite
adelic element `x` that is integral off `T`. Moreover, `x` lies in the unipotent group
`New.Shape.Form.besselU` if `y` does. It lies in `New.Shape.Form.besselH` if `y` does. -/
theorem exists_isIntegralOff_toPlaces_eq (y : U (S.latticeMiddle (LocProd T)).splitGram) :
    ∃ x : U (S.latticeMiddle (𝔸f E)).splitGram,
      S.toPlaces T x = y ∧ S.IsIntegralOff T x ∧
      (y ∈ besselU → x ∈ besselU) ∧
      (y ∈ besselH → x ∈ besselH) := by
  -- The lift of `y` is `1 + φ (y - 1)`, where `φ` extends each entry by zero.
  let φ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T) →ₙ+*
      Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) :=
    { toFun M := M.map (adeleOfLocal T)
      map_mul' := by simp
      map_zero' := by simp
      map_add' := Matrix.map_add _ (map_add _) }
  have hφ (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) (i j : 𝔰.BesselIndex) :
      φ M i j = adeleOfLocal T (M i j) := rfl
  let f : GL 𝔰.BesselIndex (LocProd T) →* GL 𝔰.BesselIndex (𝔸f E) := unitsMapNonUnital φ
  have hf (g : GL 𝔰.BesselIndex (LocProd T)) (i j : 𝔰.BesselIndex) :
      (f g).val i j = (1 : Matrix _ _ (𝔸f E)) i j +
        adeleOfLocal T (g.val i j - (1 : Matrix _ _ (LocProd T)) i j) := rfl
  have h_unitary : f y ∈ S.GFin := by
    let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.latticeMiddle (𝔸f E)).splitGram
    have h_left (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) :
        φ (J.map (evalPlaces T) * M) = J * φ M := by
      ext i j : 1
      simp only [hφ, Matrix.mul_apply, _root_.map_sum, Matrix.map_apply,
        adeleOfLocal_evalPlaces_mul]
    have h_right (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) :
        φ (M * J.map (evalPlaces T)) = φ M * J := by
      ext i j : 1
      simp only [hφ, Matrix.mul_apply, _root_.map_sum, Matrix.map_apply, mul_comm (M _ _),
        mul_comm (adeleOfLocal T _), adeleOfLocal_evalPlaces_mul]
    have h_star (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) : φ Mᴴ = (φ M)ᴴ := by
      ext i j : 1
      simp only [hφ, conjTranspose_apply, adeleOfLocal_star]
    -- For `y = 1 + z` the condition on `y` reads `zᴴ J z + zᴴ J + J z = 0`; apply `φ` to it.
    obtain ⟨z, hz⟩ : ∃ z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T), 1 + z = y.val.val :=
      add_left_surjective 1 y.val.val
    have hy : (1 + z)ᴴ * J.map (evalPlaces T) * (1 + z) = J.map (evalPlaces T) := by
      rw [hz, S.map_splitGram_latticeMiddle (evalPlaces T)]
      exact mem_unitaryGroupOf_iff.1 y.prop
    have h_zero : zᴴ * (J.map (evalPlaces T) * z) + zᴴ * J.map (evalPlaces T) +
        J.map (evalPlaces T) * z = 0 := by
      rw [conjTranspose_add, conjTranspose_one] at hy
      linear_combination (norm := noncomm_ring) hy
    have h_map : (φ z)ᴴ * (J * φ z) + (φ z)ᴴ * J + J * φ z = 0 := by
      rw [← h_star, ← h_left, ← h_right, ← map_mul, ← map_add, ← map_add, h_zero, map_zero]
    have hfy : (f y).val = 1 + φ z := by simp [f, ← hz]
    rw [mem_unitaryGroupOf_iff]
    change (f y).valᴴ * J * (f y).val = J
    rw [hfy, conjTranspose_add, conjTranspose_one]
    linear_combination (norm := noncomm_ring) h_map
  have h_int (g : GL 𝔰.BesselIndex (LocProd T)) : IsIntMatrix (integralOff T) (f g).val :=
    IsIntMatrix.one.add fun _ _ ↦ adeleOfLocal_mem_integralOff T _
  refine ⟨⟨f y, h_unitary⟩, ?_, mem_intGL.2 ⟨h_int y, h_int y⁻¹⟩, ?_⟩
  · ext i j : 2
    change evalPlaces T ((f y).val i j) = y.val.val i j
    simp [hf, Matrix.one_apply]
  · -- Both subgroups ask certain entries to be those of `1`, and `f` keeps this.
    have h_entry (i j : 𝔰.BesselIndex) (h : y.val.val i j = (1 : Matrix _ _ (LocProd T)) i j) :
        (f y).val i j = (1 : Matrix _ _ (𝔸f E)) i j := by
      rw [hf, h, sub_self, map_zero, add_zero]
    exact ⟨fun hy ↦ mem_besselU.2 fun i j h ↦ h_entry i j (mem_besselU.1 hy i j h),
      fun hy ↦ mem_floorGroup.2 fun i j h ↦ h_entry i j (mem_floorGroup.1 hy i j h)⟩

/-- Let `u` be a finite idele with `u⁻¹` integral off `T`. A finite adelic point `x` is integral and
congruent to `1` modulo `u` if and only if it is integral off `T` and its projection to `T` is
integral and congruent to `1` modulo the projection of `u`. -/
theorem mem_unitaryLevel_iff {u : (𝔸f E)ˣ} (hu : u⁻¹.val ∈ integralOff T) :
    x ∈ unitaryLevel (Ô E) u (S.latticeMiddle (𝔸f E)).splitGram ↔
      S.IsIntegralOff T x ∧
      S.toPlaces T x ∈
        unitaryLevel O (u.map (evalPlaces T)) (S.latticeMiddle (LocProd T)).splitGram := by
  have h_entry (i j : 𝔰.BesselIndex) :
      (S.toPlaces T x).val.val i j = evalPlaces T (x.val.val i j) := rfl
  have h_inv_entry (i j : 𝔰.BesselIndex) :
      (S.toPlaces T x).val⁻¹.val i j = evalPlaces T (x.val⁻¹.val i j) := rfl
  -- By `mem_Ô_iff` each condition splits into one at `T` and one off `T`.
  have h_split : x ∈ unitaryLevel (Ô E) u (S.latticeMiddle (𝔸f E)).splitGram ↔
      (S.IsIntegralOff T x ∧ IsIntMatrix (integralOff T) (u⁻¹.val • (x.val.val - 1))) ∧
      S.toPlaces T x ∈
        unitaryLevel O (u.map (evalPlaces T)) (S.latticeMiddle (LocProd T)).splitGram := by
    simp [unitaryLevel, mem_intGL, IsIntMatrix, mem_Ô_iff T, Units.smul_def, forall_and,
      Matrix.one_apply, Subgroup.copy, h_entry, h_inv_entry, -Sum.forall, -coe_units_inv]
    -- The two sides are now the same conditions on entries, in another order.
    tauto
  -- Off `T` the congruence modulo `u` follows from integrality, as `u⁻¹` is integral there.
  have h_cong (hx : S.IsIntegralOff T x) :
      IsIntMatrix (integralOff T) (u⁻¹.val • (x.val.val - 1)) :=
    (hx.isIntMatrix.sub .one).smul hu
  rw [h_split, and_iff_left_of_imp h_cong]

/-- A finite adelic point `x` lies in the group `K` of integral points if and only if it is integral
off `T` and its projection to `T` is integral. -/
lemma mem_latticeStabilizer_iff :
    x ∈ S.latticeStabilizer ↔
      S.IsIntegralOff T x ∧
      S.toPlaces T x ∈ unitaryLevel O 1 (S.latticeMiddle (LocProd T)).splitGram := by
  simp [latticeStabilizer, ← unitaryLevel_one, mem_unitaryLevel_iff (T := T)]

end

/-! ### The product of the completions at `T` as a finite place -/

/-- Let `i` and `τ` be integral at `T`, with `i² = -1`, `star i = -i` and `τ + star τ = 1`. There is
a Haar measure `ν` on the skew elements, of mass one on the integral ones, such that
`(a, b) ↦ τ i a + b` takes `ν.prod ν` to the volume. -/
lemma exists_isAddHaarMeasure_skewAdjoint {i τ : LocProd T} (hi : i ∈ O) (hτ : τ ∈ O)
    (h_sq : -i * i = 1) (h_skew : star i = -i) (h_tr : τ + star τ = 1) :
    ∃ ν : Measure (skewAdjoint (LocProd T)),
      ν.IsAddHaarMeasure ∧
      ν {b : skewAdjoint (LocProd T) | b.val ∈ O} = 1 ∧
      MeasurePreserving
        (fun p : skewAdjoint (LocProd T) × skewAdjoint (LocProd T) ↦ τ * i * p.1.val + p.2.val)
        (ν.prod ν) := by
  -- The map `π` is onto and `π ⁻¹' O = B ×ˢ B`, for `B` the set of integral skew elements. So it
  -- takes `ν.prod ν` to the Haar measure that gives `O` mass one.
  let B : Set (skewAdjoint (LocProd T)) := {b : skewAdjoint (LocProd T) | b.val ∈ O}
  let ν : Measure (skewAdjoint (LocProd T)) :=
    addHaarMeasure ⟨⟨B, isCompact_O.preimage_val isClosed_skewAdjoint⟩, 0,
      isOpen_O.preimage_val.interior_eq.ge (by simp [O.zero_mem])⟩
  have hν : ν B = 1 := addHaarMeasure_self
  let π : skewAdjoint (LocProd T) × skewAdjoint (LocProd T) →+ LocProd T :=
    .mk' (fun p ↦ τ * i * p.1.val + p.2.val) fun p q ↦ by simp [mul_add, add_add_add_comm]
  have h_lift : HasAddStableLifts π univ := by
    refine fun x ↦ ⟨(skewPart (-i * x), skewPart (star τ * x)), ?_, by simp⟩
    change τ * i * (-i * x - star (-i * x)) + (star τ * x - star (star τ * x)) = x
    simp only [star_mul', star_neg, star_star, h_skew]
    linear_combination τ * (x + star x) * h_sq + x * h_tr
  have h_pre : π ⁻¹' (O : Subring (LocProd T)) = B ×ˢ B := by
    ext ⟨a, b⟩
    let x : LocProd T := τ * i * a + b
    change x ∈ O ↔ a.val ∈ O ∧ b.val ∈ O
    refine ⟨fun hx ↦ ?_, fun ⟨ha, hb⟩ ↦ add_mem (mul_mem (mul_mem hτ hi) ha) hb⟩
    -- The trace of `x = π (a, b)` gives back `a`, so `x ∈ O` forces `a ∈ O`, then `b ∈ O`.
    have h_trace : a = -i * (x + star x) := by
      simp only [x, star_add, star_mul', h_skew, skewAdjoint.star_val_eq]
      linear_combination -(τ + star τ) * a.val * h_sq - a.val * h_tr
    have ha : a.val ∈ O :=
      mem_of_eq_of_mem h_trace (mul_mem (neg_mem hi) (add_mem hx (IsStarStable.star_mem hx)))
    exact ⟨ha, (add_mem_cancel_left (mul_mem (mul_mem hτ hi) ha)).1 hx⟩
  have h_map : (ν.prod ν).map π = volume := by
    simpa [h_pre, SemilocalField.volume_O, hν, Set.inter_univ] using
      measure_smul_map_restrict_eq_smul_neg (ν.prod ν) volume (by measurability) .univ h_lift
        isCompact_O.measurableSet
  exact ⟨ν, inferInstance, hν, by fun_prop, h_map⟩

/-- If the integers at `T` are self-dual for the character `ψ`, then there is a kernel `G` for
Plancherel's inequality. It is continuous, integrable and nonnegative, with `G 0 = 1`, and its
transform has mass at most one. -/
lemma exists_plancherel_kernel {ψ : AddChar (LocProd T) ℂ}
    (h_dual : ∀ a : LocProd T, (∀ r ∈ O, ψ (r * a) = 1) ↔ a ∈ O) :
    ∃ G : LocProd T → ℝ,
      Continuous G ∧ Integrable G ∧ 0 ≤ G ∧ G 0 = 1 ∧
      ∫⁻ z : LocProd T, ‖∫ v : LocProd T, G v * ψ (star v * z)‖ₑ ≤ 1 := by
  classical
  let G : LocProd T → ℝ := (O : Subring (LocProd T)).carrier.indicator 1
  -- Orthogonality of characters and self-duality: `G` is its own transform.
  have h_transform (z : LocProd T) : ∫ v : LocProd T, G v * ψ (star v * z) = G z := by
    have h_star : (∀ v ∈ O, ψ (star v * z) = 1) ↔ z ∈ O :=
      ⟨fun h ↦ (h_dual z).1 fun r hr ↦ by simpa using h _ (IsStarStable.star_mem hr),
        fun h v hv ↦ (h_dual z).2 h _ (IsStarStable.star_mem hv)⟩
    calc
      _ = ∫ v in (O : Subring (LocProd T)), ψ (star v * z) := by
        simp [G, ← integral_indicator isCompact_O.measurableSet, indicator_apply,
          apply_ite Complex.ofReal]
      _ = if ∀ v ∈ O, ψ (star v * z) = 1 then 1 else 0 := by
        simpa [real_def, volume_O] using setIntegral_char (ν := volume) (M := O.toAddSubgroup)
          isOpen_O (χ := fun v ↦ ψ (star v * z)) (by simp [add_mul, AddChar.map_add_eq_mul])
      _ = G z := by simp [G, h_star, indicator_apply, apply_ite Complex.ofReal]
  refine ⟨G, IsClopen.continuous_indicator ⟨isCompact_O.isClosed, isOpen_O⟩ continuous_one, ?_,
    fun _ ↦ indicator_nonneg (by simp) _, by simp [G], ?_⟩
  · simp [G, integrable_indicator_iff, isCompact_O.measurableSet, Pi.one_def, volume_O]
  · calc
      _ = ∫⁻ z : LocProd T, (O : Subring (LocProd T)).carrier.indicator 1 z := by
        simp_rw [h_transform]
        simp [G, indicator_apply, apply_ite eNorm, apply_ite Complex.ofReal]
      _ ≤ 1 := (lintegral_indicator_one_le _).trans_eq volume_O

section

omit [WeilData E] [T.StarStable]

/-- The integers at `T` are self-dual for the character `charOnPlaces`: `a` is integral if and only
if the character is trivial on the integral multiples of `a`. -/
lemma forall_charOnPlaces_mul_eq_one_iff (a : LocProd T) :
    (∀ r ∈ O, S.charOnPlaces T (r * a) = 1) ↔ a ∈ O :=
  -- Extension by zero reduces this to the self-duality of `Ô E`.
  calc
    _ ↔ ∀ r : Ô E, S.selfDualChar (r * adeleOfLocal T a) = 1 := by
      simp [locProd_O_eq_map_evalPlaces, charOnPlaces, adeleOfLocal_evalPlaces_mul, -map_mul]
    _ ↔ adeleOfLocal T a ∈ Ô E := S.forall_selfDualChar_mul_eq_one_iff _
    _ ↔ a ∈ O := by simp [mem_Ô_iff T]

open Valued in
/-- The product over the places `w` of `T` of the functions `1 + √(‖x w‖⁻¹ - 1)` is locally
integrable. -/
lemma locallyIntegrable_prod_one_add_sqrt :
    LocallyIntegrable fun x : LocProd T ↦ ∏ w : T, (1 + √(‖x w‖⁻¹ - 1)) := fun x ↦ by
  have h_loc (w : T) :
      ∃ C ∈ nhds (x w), IntegrableOn (fun y : LocField w.val ↦ 1 + √(‖y‖⁻¹ - 1)) C :=
    locallyIntegrable_one_add_sqrt_inv_norm_sub_one w.val (x w)
  choose C hC hC_int using h_loc
  exact ⟨Set.univ.pi C, set_pi_mem_nhds finite_univ fun w _ ↦ hC w,
    (Integrable.fintype_prod_dep hC_int).mono_measure (restrict_pi_pi _ C).le⟩

open Valued in
/-- Let `x` lie in the product `LocProd T` of the completions of `E` at the places `w` of `T`. The
generalized index of `x`, the inverse of `∏ w, ‖x w‖`, is at most the square of the product over
`w ∈ T` of the numbers `1 + √(‖x w‖⁻¹ - 1)`. -/
lemma ofReal_genIndex_le_enorm_prod_sq (x : LocProd T) :
    ENNReal.ofReal (genIndex x) ≤ ‖∏ w : T, (1 + √(‖x w‖⁻¹ - 1))‖ₑ ^ 2 := by
  have h_real (r : ℝ) : r ≤ (1 + √(r - 1)) ^ 2 := by grind [Real.sqrt_nonneg]
  calc
    _ = ENNReal.ofReal (∏ w : T, ‖x w‖⁻¹) := by
      rw [genIndex_eq_inv_prod_norm, Finset.prod_inv_distrib]
    _ ≤ ENNReal.ofReal (∏ w : T, (1 + √(‖x w‖⁻¹ - 1)) ^ 2) := by
      gcongr with w
      exact h_real _
    _ ≤ ‖∏ w : T, (1 + √(‖x w‖⁻¹ - 1)) ^ 2‖ₑ := Real.ofReal_le_eNorm _
    _ = _ := by rw [Finset.prod_pow, eNorm_pow]

end

variable (S T) in
open Valued Finset in
/-- The product of the completions of `E` at `T` carries the structure of a finite place whose
additive character is `S.charOnPlaces T`. This is `x ↦ ψ_f(-x / ϖ)` read at `T` through extension by
zero, where `ψ_f = ψf E` is the standard character of the finite adeles and `ϖ = S.deltaE` is the
generator of the different of `E` in the data `S`. -/
theorem exists_integralPlace : ∃ P : IntegralPlace (LocProd T), P.ψ = S.charOnPlaces T := by
  obtain ⟨i, hi, τ, hτ, h_sq, h_skew, h_tr⟩ :
      ∃ i ∈ O, ∃ τ ∈ O, -i * i = 1 ∧ star i = -i ∧ τ + star τ = 1 :=
    IsAdelic.exists_skew_unit (A := LocProd T)
  obtain ⟨ν, _, hν, h_split⟩ := exists_isAddHaarMeasure_skewAdjoint hi hτ h_sq h_skew h_tr
  let : TraceOne (LocProd T) := TraceOne.mk τ h_tr
  have h_dual (a : LocProd T) : (∀ r ∈ O, S.charOnPlaces T (r * a) = 1) ↔ a ∈ O :=
    forall_charOnPlaces_mul_eq_one_iff a
  -- The modulus is the inverse of the index, that is `∏ w, ‖x w‖` for a unit `x`.
  let modulus : LocProd T →* ℝ≥0∞ :=
    { toFun x := (ENNReal.ofReal (genIndex x))⁻¹
      map_one' := by simp
      map_mul' x y := by
        rw [map_mul]
        simp [ENNReal.mul_inv, genIndex_eq_inv_prod_norm, prod_nonneg] }
  have h_det (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n (LocProd T))
      (hM : IsUnit M.det) :
      volume.map (M *ᵥ ·) = (modulus M.det)⁻¹ • volume := by
    refine (map_smul_eq_inv_distribHaarChar_smul (GeneralLinearGroup.mk'' M hM)).trans ?_
    simp [modulus, inv_distribHaarChar_GL_eq_genIndex_det isOpen_O isCompact_O
      SemilocalField.isValuationPair]
  -- A locally integrable majorant of `modulus⁻¹ᐟ²`, as a product over the places.
  have h_le (u : (LocProd T)ˣ) : (modulus u)⁻¹ ≤ ‖∏ w : T, (1 + √(‖u.val w‖⁻¹ - 1))‖ₑ ^ 2 :=
    (inv_inv _).trans_le (ofReal_genIndex_le_enorm_prod_sq u.val)
  let P₀ : Floors.Place (LocProd T) :=
    { skewUnit := .mkOfMulEqOne _ _ h_sq
      skewMeasure := ν
      modulus := modulus
      ψ := S.charOnPlaces T
      kernelBound := 1
      continuous_psi := continuous_ψf.subtypeVal.comp ((continuous_adeleOfLocal T).const_mul _)
      measurable_modulus := by
        simp only [modulus, genIndex_eq_inv_prod_norm, MonoidHom.coe_mk, OneHom.coe_mk,
          measurable_inv_iff]
        fun_prop
      star_skewUnit := by simp [h_skew]
      measurePreserving_split := h_split
      modulus_star_and_neg := by
        simp [modulus]
        simp [genIndex_eq_inv_prod_norm]
      map_mulVec_volume := h_det
      ae_isUnit := by simpa [Pi.isUnit_iff, -Subtype.forall] using! fun w ↦ ae_eval_ne _ w 0
      exists_locallyIntegrable_bound := ⟨_, locallyIntegrable_prod_one_add_sqrt, h_le⟩
      norm_psi := by simp [charOnPlaces]
      exists_plancherel_kernel := exists_plancherel_kernel h_dual }
  exact ⟨{
      toPlace := P₀
      element_mem := hτ
      skewUnit_mem := neg_mem hi
      skewUnit_inv_mem := hi
      kernelBound_eq_one := rfl
      skewMeasure_setOf_mem := hν
      self_dual := h_dual
      modulus_eq_inv_genIndex := fun _ ↦ rfl }, rfl⟩

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
variable (S T) in
/-- Let `(S.latticeMiddle (LocProd T)).G` be the unitary group, over the product of the completions
at `T`, of `ϱ` hyperbolic planes plus the space `X₀ ⊕ E z` with its Gram matrix `S.latticeMiddle` in
the lattice basis. This group is unimodular: the inverse of a left Haar measure is left invariant.
Here `P` is any structure of a finite place on that product; its character plays no part. -/
theorem isMulLeftInvariant_haar_inv [P : IntegralPlace (LocProd T)] :
    (haar (G := (S.latticeMiddle (LocProd T)).G)).inv.IsMulLeftInvariant := by
  -- An orthonormal basis `k` over `Ô E` identifies the adelic group with `Gf E _`, whose measure is
  -- bi-invariant; push this measure forward from the points integral off `T`
  -- (`isMulLeftInvariant_measure_smul_inv`).
  obtain ⟨k, hk, hkJ⟩ :
      ∃ k ∈ intGL 𝔰.BesselIndex (Ô E), k.valᴴ * (S.latticeMiddle (𝔸f E)).splitGram * k.val = 1 :=
    exists_orthonormal_Ô (E := E) S.isUnimodular_latticeMiddle.splitGram
  let c : Gf E 𝔰.BesselIndex ≃* S.GFin := U.conj k hkJ
  have hc : Continuous c := .subtype_mk (by fun_prop) _
  have h_pr : Continuous (S.toPlaces T) := U.continuous_map
  let π : Gf E 𝔰.BesselIndex →* (S.latticeMiddle (LocProd T)).G := (S.toPlaces T).comp c.toMonoidHom
  let X : Set (Gf E 𝔰.BesselIndex) := {g | S.IsIntegralOff T (c g)}
  have hX : IsOpen X := (isOpen_intGL (isOpen_integralOff T)).preimage_val.preimage hc
  -- Each point at `T` has a lift that is integral off `T`.
  have h_lift : HasStableLifts π X := by
    intro y
    obtain ⟨x, hx, hx_off, -⟩ := exists_isIntegralOff_toPlaces_eq y
    refine ⟨c.symm x, ?_⟩
    simp [X, π, IsIntegralOff, mul_mem_cancel_left, mul_mem_cancel_right, hx, hx_off]
  -- Integral at `T` and off `T` means integral, and `k` normalizes the integral points.
  have h_int : π ⁻¹' unitaryLevel O 1 (S.latticeMiddle (LocProd T)).splitGram ∩ X =
      stdLevel E 𝔰.BesselIndex := by
    ext g
    exact (and_comm.trans (mem_latticeStabilizer_iff (x := c g)).symm).trans
      (Subgroup.le_normalizer hk g).symm
  -- The measure `volume (stdLevel E _) • haar.inv` is left invariant, and `stdLevel E _` has volume
  -- one.
  have h_inv :
      (volume (stdLevel E 𝔰.BesselIndex : Set (Gf E 𝔰.BesselIndex)) •
        (haar (G := (S.latticeMiddle (LocProd T)).G)).inv).IsMulLeftInvariant := by
    rw [← h_int]
    have hπ : Measurable π := (h_pr.comp hc).measurable
    exact isMulLeftInvariant_measure_smul_inv volume haar (π := π) hπ hX.measurableSet
      h_lift P.measurableSet_unitaryLevel
  simpa using h_inv

section

omit [WeilData E]

/-- The image in the finite adeles `𝔸f E` of `-ϖ⁻¹`, where `ϖ = S.deltaE`, is skew: its conjugate
under `star` is its negative. -/
lemma star_neg_inv_deltaE :
    star ((-S.deltaE.val⁻¹ : E) : 𝔸f E) = -((-S.deltaE.val⁻¹ : E) : 𝔸f E) := by
  simp [← coe_star_ringOfIntegers, S.star_deltaE]

omit [T.StarStable] in
/-- The character `S.charOnPlaces T` at `x` is `ψf E`, the standard character of the finite adeles,
at `-ϖ⁻¹` times `adeleOfLocal T x`, the extension of `x` by zero. Here `ϖ = S.deltaE`. -/
lemma charOnPlaces_apply_eq_ψf (x : LocProd T) :
    S.charOnPlaces T x = (ψf E ((-S.deltaE.val⁻¹ : E) * adeleOfLocal T x) : ℂ) := rfl

/-- The character `S.charOnPlaces T` is trivial on the traces `x + star x` for `x` in `LocProd T`.
This is because it reads a fixed character of the finite adeles through multiplication by the skew
element -ϖ⁻¹. -/
lemma charOnPlaces_add_star (x : LocProd T) : S.charOnPlaces T (x + star x) = 1 := by
  -- ϖ is skew and `ψf` takes the same value at conjugate adeles.
  have h_neg : ψf E ((-S.deltaE.val⁻¹ : E) * star (adeleOfLocal T x)) =
      ψf E (-((-S.deltaE.val⁻¹ : E) * adeleOfLocal T x)) := by
    rw [← ψf_star, star_mul', star_star, star_neg_inv_deltaE, neg_mul]
  rw [charOnPlaces_apply_eq_ψf, map_add, adeleOfLocal_star, mul_add, AddChar.map_add_eq_mul, h_neg,
    ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

end

variable (T) in
open Valued Finset in
/-- Let `ϱ = 𝔰.ϱ` be the number of hyperbolic planes, `k = 𝔰.k` the dimension of the definite
summand `X₀`, and `S.latticeMiddle` the Gram matrix of `X₀ ⊕ E z` in the lattice basis. The product
of the completions at a conjugation-stable finite set `T` is a finite place `P` with a place datum
`F`, with 3ϱ + 6 further hyperbolic pairs and an orthonormal part of size `k - (6ϱ + 13)`, that
satisfies `New.Filling.IsFillingData`. -/
theorem exists_isFillingData :
    ∃ _ : IntegralPlace (LocProd T),
      ∃ F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
        (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5),
      S.IsFillingData T F := by
  obtain ⟨P, hψ⟩ := S.exists_integralPlace T
  -- The lower bound on `𝔰.k` makes the subtraction of natural numbers exact.
  have h_k : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k := S.thousand_mul_le_k
  have h_card : 𝔰.k =
      Fintype.card (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) + 2 * (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5) + 1 := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨F, hF, hg⟩ :
      ∃ F : PlaceData _ (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5),
        P.IsLatticeData F ∧ F.levelUnit = S.ideleM.map (evalPlaces T) :=
    P.exists_isLatticeData (by simp) (by simp [ideleM_val, -Nat.cast_mul]) h_card
  -- The zeta value at `T` is at most the global one.
  have h_zeta : idealZeta P.integers (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 4) ^ 𝔰.n ≤ .ofReal (1 + 2⁻¹ ^ 𝔰.n) := by
    grw [idealZeta_locProd_le, idealZeta_intAdeles_pow_le _ S.mul_finrank_le_pow]
  have : P.IsLargeLatticeData F := by
    refine ⟨hF, ⟨h_zeta, ?_⟩, hψ ▸ charOnPlaces_add_star, haar.inv, ?_, inferInstance⟩
    · simp
      lia
    · exact { toIsMulLeftInvariant := S.isMulLeftInvariant_haar_inv T }
  exact ⟨P, F, { psi_eq := hψ, levelUnit_eq := hg }⟩

end New.Filling
