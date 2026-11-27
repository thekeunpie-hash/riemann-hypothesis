module

import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import New.Spanning.Bessel.LargeFunction
import Lib.DiscreteSeries.Bessel.SchurBound
import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
public import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability
import Lib.Shimura.ComplexTheta.AppellHumbertData
import Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Tactic.Monotonicity.Lemmas
public import New.UpperBound.Objects.Rows
public import New.Spanning.Frames.RealPlaceGauge
public import New.Spanning.Unfolding.Setup
import Lib.DiscreteSeries.Character.FormalDegree
import Lib.GLn.SchurModule.SchurNorm
import New.Determinant.AuxiliaryForms.DeepLevelPoincarePeriod
import New.Spanning.Frames.RealBandLimits
import New.Spanning.Unfolding.Climbing
import Lib.SiegelWeil.OneVector.SiegelClassSum
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import New.Spanning.Unfolding.PoincareSeries
public import New.UpperBound.Seesaw.EdgePairEvaluation
public import New.UpperBound.Size.ShortColumns
import Lib.General.Groups.IndexOfProduct
import New.Spanning.Unfolding.ReducedGroups

section
section
/-!
# The Bessel function at a real place: decay and cut

The file concerns Bessel functions (`New.IsBesselFunction`) on the real unitary group
G₁ = `New.Shape.G₁`: bounded functions to ℂ^I that transform on the left by a character of the
unipotent group 𝖴 = `New.Shape.Form.besselU` and by `rep` under H = U(κ). Throughout, p is a unitary
frame that diagonalises the form, c_λ = `New.HCParam.dsCoeffInFrame` is the discrete series
coefficient of a parameter l = 2λ with large gap (`New.HCParam.HasLargeGap`), v is a unit vector of
ℂ^I, and e = deg·c_λ with deg = `New.HCParam.formalDegree`. F is reproduced by e if F * e = F for
the convolution `New.convolve`: (F * e)(y) = ∫ e(a⁻¹) F(ya) da. The measure of 𝖴∖G₁ is
`New.besselQuotMeasure`. G₁ consists of r × r matrices with r = `𝔰.r`, ‖g‖ is the operator norm, and
n = `𝔰.n` = ϱ + 1 with ϱ the number of hyperbolic planes of the form.
* `New.exists_isDecayMajorant_besselAverage`: the normalised average of c_λ over the Bessel subgroup
  decays in the length, below a bounded integrable weight (`New.IsDecayMajorant`).
* `New.besselCut`: the cut of a function at length b^(6n+2); it is close to the function in L²
  (`New.IsDecayMajorant.lintegral_sq_besselCut_sub_le`).
* `New.exists_isCutPair_besselAverage`: a multiple of the average is reproduced by e and forms a cut
  pair (`New.IsCutPair`) with its cut.

Notions from other files:
* `New.besselLength`: for y in G₁, the infimum of ‖sy‖ + 1 over s in the Bessel subgroup S = 𝖴H
  (`New.Shape.Form.besselS`).
* `New.Shape.besselGraph`: the group 𝖴H as a graph, the pairs (g, k) in G₁ × U(κ) with k⁻¹g in 𝖴.
* `New.DiscreteSeries.besselAverage`: the function y ↦ ∫_S c_λ(x⁻¹ s y) π(s)⁻¹ v ds, where π is the
  character on 𝖴 and `rep` on H.
* `New.scaledBesselLength`: the larger of 1 and the length divided by b^(6n).

## Relation to the literature

A Bessel function at a real place, an average of a discrete series coefficient with a large period
integral, inherits the coefficient's decay. Normalised and multiplied by a scalar cut-off, it gives
a continuous approximant, close in L² and compactly supported modulo the unipotent group, with an
explicit tail bound. Related work: Muić, Fourier coefficients of automorphic forms and integrable
discrete series, 2015; Miličić, Asymptotic behavior of matrix coefficients of the discrete series,
1977; Wallach, Real Reductive Groups II, 1992.

See `New.Spanning.Bessel.FillingData` for related work.
-/

@[expose] public section

namespace New

open Matrix MeasureTheory ENNReal Norms.L2Operator Fintype CStarRing Set DiscreteSeries

variable {𝔰 : Shape} {I : Type} {ε : 𝔰.BesselIndex → ℤˣ} [Fintype I] [DecidableEq I]
  [p : UnitarySignFrame 𝔰 ε] {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {l : HCParam ε}
  {A L : ℕ}

private lemma sFinite_besselGraphMeasure {𝔰 : Shape} : SFinite 𝔰.besselGraphMeasure := by
  unfold Shape.besselGraphMeasure
  infer_instance

private lemma measurable_norm_U {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι ℂ} :
    Measurable fun g : U J ↦ ‖g.val.val‖ :=
  (Units.continuous_val.comp continuous_subtypeVal).norm.measurable

/-- The frame is unitary, so passing to it by `frameEquiv` (g ↦ p⁻¹ g p) keeps the operator
norm. -/
lemma norm_frameEquiv (g : 𝔰.G₁) : ‖(DiscreteSeries.frameEquiv g).val.val‖ = ‖g.val.val‖ := by
  have hp : p.matrix.val ∈ unitary (Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) := p.mem_unitary
  simp [DiscreteSeries.frameEquiv, U.conj, inv_eq_left_inv (Unitary.star_mul_self_of_mem hp), hp,
    norm_mul_mem_unitary, norm_mem_unitary_mul]

/-- Let `G₁` be the unitary group of `r × r` matrices of the shape `𝔰`, and `l` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. For a natural
number `M > 8 r ^ 2`, `b ≥ 2000` and `r + L + 1 ≤ b ^ 4`, the integral of `deg * (2 / ‖g‖) ^ M`
(operator norm) over `g` in `G₁` is at most `b ^ (50 r ^ 2 + 1) * 2 ^ M`. -/
lemma lintegral_formalDegree_mul_decay_le (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {b : ℝ} (hb_large : 2000 ≤ b)
    (hL_le : 𝔰.r + L + 1 ≤ b ^ 4) {M : ℕ} (hM : 8 * 𝔰.r ^ 2 < M) :
    ∫⁻ g : 𝔰.G₁, ENNReal.ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M) ≤
      ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1) * 2 ^ M) := by
  -- Transport `integral_tail_le` to G₁ by the frame; then `8` and `2000` are at most `b`.
  have h_deg : 0 < l.formalDegree := formalDegree_pos h_gap
  have hb8 : 8 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 ≤ b := zero_le_one.trans hb1
  obtain ⟨h_int, h_le⟩ := integral_tail_le hL M hM
  have h_meas : Measurable fun g : USign ε ↦
      ENNReal.ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M) :=
    (measurable_const.mul ((measurable_const.div measurable_norm_U).pow_const M)).ennreal_ofReal
  calc _ = ∫⁻ g : USign ε, ENNReal.ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M) := by
        refine (lintegral_congr fun g ↦ ?_).trans
          (measurePreserving_frameEquiv.lintegral_comp h_meas)
        rw [norm_frameEquiv]
    _ = ENNReal.ofReal (∫ g : USign ε, l.formalDegree * (2 / ‖g.val.val‖) ^ M) :=
        (ofReal_integral_eq_lintegral_ofReal h_int
          (.of_forall fun _ ↦
            mul_nonneg h_deg.le (pow_nonneg (div_nonneg zero_le_two (norm_nonneg _)) M))).symm
    _ ≤ ENNReal.ofReal (b * (b * (b ^ 4) ^ 6) ^ (2 * 𝔰.r ^ 2) * 2 ^ M) := by
        refine ofReal_le_ofReal
          (h_le.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg zero_le_two _)))
        have hL_nn : (0 : ℝ) ≤ 𝔰.r + L + 1 := by positivity
        refine mul_le_mul hb8
          (pow_le_pow_left₀ (mul_nonneg (by norm_num) (pow_nonneg hL_nn 6))
            (mul_le_mul hb_large (pow_le_pow_left₀ hL_nn hL_le 6) (pow_nonneg hL_nn 6) hb0) _)
          (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hL_nn 6)) _) hb0
    _ ≤ ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1) * 2 ^ M) := by
        rw [← pow_mul, ← pow_succ', ← pow_mul, ← pow_succ']
        exact ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb1 (by omega))
            (pow_nonneg zero_le_two _))

/-- Let `G₁` be the unitary group of `r × r` matrices of the shape `𝔰`, and `l` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. For
`M = 9 r ^ 2`, `b ≥ 2000` and `r + L + 1 ≤ b ^ 4`, the product of `deg`, the integral of
`(2 / ‖g‖) ^ M` (operator norm) over `g` in `G₁`, and `16 ^ M` is at most `b ^ (99 r ^ 2)`. -/
lemma formalDegree_mul_lintegral_decay_le (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {b : ℝ} (hb_large : 2000 ≤ b)
    (hL_le : 𝔰.r + L + 1 ≤ b ^ 4) {M : ℕ} (hM : M = 9 * 𝔰.r ^ 2) :
    ENNReal.ofReal l.formalDegree * (∫⁻ g : 𝔰.G₁, ENNReal.ofReal ((2 / ‖g.val.val‖) ^ M)) *
        ENNReal.ofReal (16 ^ M) ≤
      ENNReal.ofReal (b ^ (99 * 𝔰.r ^ 2)) := by
  have hb1 : 1 ≤ b := by linarith
  have hb2 : 2 ≤ b := by linarith
  have hb16 : 16 ≤ b := by linarith
  have hb0 : 0 ≤ b := zero_le_one.trans hb1
  have hr : 0 < 𝔰.r ^ 2 := pow_pos Fintype.card_pos 2
  have h_deg : 0 ≤ l.formalDegree := (formalDegree_pos h_gap).le
  have h1 : ENNReal.ofReal l.formalDegree *
        (∫⁻ g : 𝔰.G₁, ENNReal.ofReal ((2 / ‖g.val.val‖) ^ M)) ≤
      ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1) * 2 ^ M) :=
    (lintegral_const_mul_le _ _).trans <|
      (lintegral_congr fun g ↦ (ofReal_mul h_deg).symm).trans_le <|
        lintegral_formalDegree_mul_decay_le h_gap hL hb_large hL_le (by omega)
  calc _ ≤ ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1) * 2 ^ M) * ENNReal.ofReal (16 ^ M) :=
        mul_le_mul' h1 le_rfl
    _ ≤ ENNReal.ofReal (b ^ (50 * 𝔰.r ^ 2 + 1 + M + M)) := by
        rw [← ofReal_mul (mul_nonneg (pow_nonneg hb0 _) (pow_nonneg zero_le_two _))]
        refine ofReal_le_ofReal ?_
        rw [pow_add b (50 * 𝔰.r ^ 2 + 1 + M) M, pow_add b (50 * 𝔰.r ^ 2 + 1) M]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le_two hb2 M) (pow_nonneg hb0 _))
          (pow_le_pow_left₀ (by norm_num) hb16 M) (pow_nonneg (by norm_num) M)
          (mul_nonneg (pow_nonneg hb0 _) (pow_nonneg hb0 _))
    _ ≤ ENNReal.ofReal (b ^ (99 * 𝔰.r ^ 2)) :=
        ofReal_le_ofReal (pow_le_pow_right₀ hb1 (by omega))

/-- Let `G₁` be the unitary group of `r × r` matrices of the shape `𝔰`, and `l` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. If
`b ≥ 2000`, `r + L + 1 ≤ b ^ 4` and `T ≥ 1`, the set of `g` in `G₁` of operator norm at most `T` has
volume at most `T ^ (9 r ^ 2) * b ^ (99 r ^ 2) / deg`. -/
lemma formalDegree_mul_volume_ball_le (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {b : ℝ}
    (hb_large : 2000 ≤ b) (hL_le : 𝔰.r + L + 1 ≤ b ^ 4) {T : ℝ} (hT : 1 ≤ T) :
    ENNReal.ofReal l.formalDegree * volume {g : 𝔰.G₁ | ‖g.val.val‖ ≤ T} ≤
      ENNReal.ofReal (T ^ (9 * 𝔰.r ^ 2) * b ^ (99 * 𝔰.r ^ 2)) := by
  -- Chebyshev's inequality with `M = 9 r ^ 2`: on the ball `deg ≤ (T / 2) ^ M * φ g` for
  -- `φ g = deg * (2 / ‖g‖) ^ M`.
  have hb1 : 1 ≤ b := by linarith
  have hr : 0 < 𝔰.r ^ 2 := pow_pos Fintype.card_pos 2
  have h_deg : 0 < l.formalDegree := formalDegree_pos h_gap
  have hT2 : 0 ≤ (T / 2) ^ (9 * 𝔰.r ^ 2) :=
    pow_nonneg (div_nonneg (zero_le_one.trans hT) zero_le_two) _
  let M : ℕ := 9 * 𝔰.r ^ 2
  let φ (g : 𝔰.G₁) : ℝ≥0∞ := .ofReal (l.formalDegree * (2 / ‖g.val.val‖) ^ M)
  have h_meas : Measurable fun g : 𝔰.G₁ ↦ .ofReal ((T / 2) ^ M) * φ g :=
    measurable_const.mul
      (measurable_const.mul ((measurable_const.div measurable_norm_U).pow_const M)).ennreal_ofReal
  have h_tail : ∫⁻ g : 𝔰.G₁, φ g ≤ .ofReal (b ^ (99 * 𝔰.r ^ 2) * 2 ^ M) :=
    (lintegral_formalDegree_mul_decay_le h_gap hL hb_large hL_le (by omega)).trans
      (ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hb1 (by omega)) (pow_nonneg zero_le_two M)))
  have h_point (g : 𝔰.G₁) (hg_mem : g ∈ {g : 𝔰.G₁ | ‖g.val.val‖ ≤ T}) :
      .ofReal l.formalDegree ≤ .ofReal ((T / 2) ^ M) * φ g := by
    rw [← ofReal_mul hT2]
    refine ofReal_le_ofReal ?_
    rw [mul_left_comm, ← mul_pow, div_mul_div_cancel₀ two_ne_zero]
    exact le_mul_of_one_le_right h_deg.le
      (one_le_pow₀ ((one_le_div (one_pos.trans_le (U.one_le_norm g))).2 hg_mem))
  calc _ = ∫⁻ _ in {g : 𝔰.G₁ | ‖g.val.val‖ ≤ T}, ENNReal.ofReal l.formalDegree :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ g : 𝔰.G₁, .ofReal ((T / 2) ^ M) * φ g :=
        (setLIntegral_mono h_meas h_point).trans (setLIntegral_le_lintegral _ _)
    _ ≤ .ofReal ((T / 2) ^ M) * .ofReal (b ^ (99 * 𝔰.r ^ 2) * 2 ^ M) := by
        rw [lintegral_const_mul' _ _ ofReal_ne_top]
        exact mul_le_mul' le_rfl h_tail
    _ = ENNReal.ofReal (T ^ M * b ^ (99 * 𝔰.r ^ 2)) := by
        rw [← ofReal_mul hT2, mul_left_comm, ← mul_pow,
          div_mul_cancel₀ _ two_ne_zero, mul_comm]

/-- Let `s` be in the Bessel subgroup 𝖴H of `G₁` (the first component of a pair in `besselGraph`).
If `b ≥ 2` and the length `besselLength x` is at most `b ^ (5 n)`, with `n = ϱ + 1`, then the length
of `y` divided by `b ^ (6 n)` is at most `‖x⁻¹ s y‖ / 2`. -/
lemma besselLength_div_le_half_norm {b : ℝ} {x : 𝔰.G₁} (hb : 2 ≤ b)
    (hx : besselLength x ≤ b ^ (5 * 𝔰.n)) (s : 𝔰.besselGraph) (y : 𝔰.G₁) :
    besselLength y / b ^ (6 * 𝔰.n) ≤ ‖(x⁻¹ * (s.val.fst * y)).val.val‖ / 2 := by
  have hb_pos : 0 < b := two_pos.trans_le hb
  have h_pow : b ^ (5 * 𝔰.n + 1) ≤ b ^ (6 * 𝔰.n) :=
    pow_le_pow_right₀ (one_le_two.trans hb) (by dsimp only [Shape.n]; omega)
  set g : 𝔰.G₁ := x⁻¹ * (s.val.fst * y)
  rw [div_le_div_iff₀ (pow_pos hb_pos _) two_pos]
  calc _ = besselLength (s.val.fst * y) * 2 := by
        rw [besselLength_besselS_mul (besselGraph_fst_mem_besselS s)]
    _ ≤ ‖g.val.val‖ * b ^ (5 * 𝔰.n) * b :=
      mul_le_mul
        ((besselLength_le_norm_inv_mul_mul_besselLength x (s.val.fst * y)).trans
          (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))
        hb zero_le_two (mul_nonneg (norm_nonneg _) (pow_nonneg hb_pos.le _))
    _ ≤ ‖g.val.val‖ * b ^ (6 * 𝔰.n) := by
      rw [mul_assoc, ← pow_succ]
      exact mul_le_mul_of_nonneg_left h_pow (norm_nonneg _)

/-- Decay of `W = besselAverage l rep x v`, the average `W y = ∫ c_λ(x⁻¹ s y) π(s)⁻¹ v ds` of the
discrete series coefficient of `l = 2λ` over the Bessel subgroup 𝖴H of `G₁`, where π is a character
on 𝖴 and `rep` on H = U(κ). The integrals run over `besselGraph`, the pairs `(s, k)` of an element
`s` of 𝖴H and its component `k` in H. Let `r` be the size of the matrices of `G₁` and `n = ϱ + 1`.
Suppose `l` has gap `500 r ^ 3 + A`, `v` is a unit vector, `b ≥ 2`, `besselLength x ≤ b ^ (5 n)` and
`i ≤ A`. Then `‖W y‖` times the `i`-th power of `max 1 (besselLength y / b ^ (6 n))` (this is
`scaledBesselLength y b`) is at most `∫ (2 / ‖x⁻¹ s y‖) ^ (9 r ^ 2) ds`. -/
lemma scaledBesselLength_pow_mul_enorm_besselAverage_le (h_gap : l.HasLargeGap A) {b : ℝ} {x : 𝔰.G₁}
    {v : EuclideanSpace ℂ I} (hv : ‖v‖ = 1) (hb : 2 ≤ b) (hx : besselLength x ≤ b ^ (5 * 𝔰.n))
    {i : ℕ} (hi : i ≤ A) (y : 𝔰.G₁) :
    ENNReal.ofReal (scaledBesselLength y b ^ i) * ‖besselAverage l rep x v y‖ₑ ≤
      ∫⁻ s : 𝔰.besselGraph,
        ENNReal.ofReal ((2 / ‖(x⁻¹ * (s.val.fst * y)).val.val‖) ^ (9 * 𝔰.r ^ 2))
        ∂𝔰.besselGraphMeasure := by
  refine (mul_le_mul' le_rfl (enorm_besselAverage_le x hv y)).trans
    ((lintegral_const_mul_le _ _).trans (lintegral_mono fun s ↦ ?_))
  set g : 𝔰.G₁ := x⁻¹ * (s.val.fst * y)
  have h_decay (j : ℕ) (hj : j ≤ A) :
      ‖l.dsCoeffInFrame g‖ ≤ (2 / ‖g.val.val‖) ^ j * (2 / ‖g.val.val‖) ^ (9 * 𝔰.r ^ 2) := by
    rw [← pow_add, ← norm_frameEquiv g]
    exact norm_dsCoeffInFrame_le h_gap hj g
  -- The length of `y` is that of `x g`, at most `‖g‖ b ^ (5 n) ≤ ‖g‖ b ^ (6 n) / 2`.
  have h_size : besselLength y / b ^ (6 * 𝔰.n) ≤ ‖g.val.val‖ / 2 :=
    besselLength_div_le_half_norm hb hx s y
  rw [← ofReal_norm, ← ofReal_mul (pow_nonneg (zero_le_one.trans (one_le_scaledBesselLength ..)) i)]
  refine ofReal_le_ofReal ?_
  obtain h_small | h_large := le_total (besselLength y / b ^ (6 * 𝔰.n)) 1
  · rw [scaledBesselLength, max_eq_left h_small, one_pow, one_mul]
    exact (h_decay 0 (Nat.zero_le A)).trans_eq (by rw [pow_zero, one_mul])
  · rw [scaledBesselLength, max_eq_right h_large]
    have h_norm_pos : 0 < ‖g.val.val‖ := one_pos.trans_le (U.one_le_norm g)
    calc (besselLength y / b ^ (6 * 𝔰.n)) ^ i * ‖l.dsCoeffInFrame g‖
        ≤ (‖g.val.val‖ / 2) ^ i *
            ((2 / ‖g.val.val‖) ^ i * (2 / ‖g.val.val‖) ^ (9 * 𝔰.r ^ 2)) :=
          mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans h_large) h_size i)
            (h_decay i hi) (norm_nonneg _) (pow_nonneg (div_nonneg h_norm_pos.le zero_le_two) i)
      _ = (2 / ‖g.val.val‖) ^ (9 * 𝔰.r ^ 2) := by
          rw [← mul_assoc, ← mul_pow, div_mul_div_cancel₀ two_ne_zero,
            div_self h_norm_pos.ne', one_pow, one_mul]

/-- A Bessel function `Y` for `rep` is a bounded measurable function with `Y (n y) = ψ(n) Y y` for
`n` in `besselU` and `Y (h y) = rep h (Y y)` for `h` in `U(κ)`. If such `Y` is continuous, and `a`
is a continuous real function with `|a y| ≤ K` that is left invariant under the Bessel subgroup
`besselS`, then `a • Y` is a Bessel function for `rep`. -/
lemma IsBesselFunction.smul_of_invariant {Y : 𝔰.G₁ → EuclideanSpace ℂ I}
    (hY : IsBesselFunction rep Y) (hY_cont : Continuous Y)
    {a : 𝔰.G₁ → ℝ} (ha_cont : Continuous a) {K : ℝ} (ha_le : ∀ y : 𝔰.G₁, |a y| ≤ K)
    (ha_inv : ∀ s ∈ besselS, ∀ y : 𝔰.G₁, a (s * y) = a y) :
    IsBesselFunction rep fun y : 𝔰.G₁ ↦ a y • Y y := by
  obtain ⟨K', hK'⟩ := hY.bounded
  have h_bound (y : 𝔰.G₁) : ‖a y • Y y‖ ≤ K * K' := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (ha_le y) (hK' y) (norm_nonneg _) ((abs_nonneg _).trans (ha_le y))
  refine ⟨.of_continuous ⟨K * K', h_bound⟩ (ha_cont.smul hY_cont), fun s hs y ↦ ?_, fun h y ↦ ?_⟩
  · rw [ha_inv s (mem_partialUnitriangularGroup_of_mem_besselU hs), hY.map_unipotent_mul s hs,
    smul_comm]
  · rw [ha_inv (RealPlace.embedH h)
      (mem_partialUnitriangularGroup_of_mem_floorGroup (toBesselH_mem _)),
      hY.map_unitary_mul, ContinuousLinearMap.map_smul_of_tower]

/-- A finite nonzero `q` can be scaled to any natural number by the square of a real number. -/
lemma exists_enorm_sq_mul_eq {q : ℝ≥0∞} (hq_ne : q ≠ 0) (hq_fin : q ≠ ⊤) (k : ℕ) :
    ∃ c : ℝ, ‖c‖ₑ ^ 2 * q = k := by
  have hq_pos : 0 < q.toReal := toReal_pos hq_ne hq_fin
  use √(k / q.toReal)
  rw [← ofReal_norm, ← ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity), ofReal_div_of_pos hq_pos, ofReal_natCast, ofReal_toReal hq_fin,
    ENNReal.div_mul_cancel hq_ne hq_fin]

/-- The cutoff of radius `R > 0`: it is `1` up to `R / 2`, `0` from `R` on, and linear in
between. -/
noncomputable def besselCutoff (R t : ℝ) : ℝ := max 0 (min 1 (2 - 2 * t / R))

lemma besselCutoff_mem_Icc (R t : ℝ) : besselCutoff R t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left .., max_le zero_le_one (min_le_left ..)⟩

lemma besselCutoff_eq_one {R t : ℝ} (hR : 0 < R) (ht : t ≤ R / 2) : besselCutoff R t = 1 := by
  have h_le : 2 * t / R ≤ 1 := (div_le_one hR).2 (by linarith)
  rw [besselCutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

lemma besselCutoff_eq_zero {R t : ℝ} (hR : 0 < R) (ht : R ≤ t) : besselCutoff R t = 0 := by
  have h_ge : 2 ≤ 2 * t / R := (le_div_iff₀ hR).2 (by linarith)
  exact max_eq_left (min_le_of_right_le (by linarith))

/-- The cut `F♭` of `F`: the product of `F y` with the cutoff of radius `b ^ (6 n + 2)` evaluated at
the length `besselLength y`, where `n = ϱ + 1`. -/
noncomputable def besselCut (b : ℝ) (F : C(𝔰.G₁, EuclideanSpace ℂ I)) :
    C(𝔰.G₁, EuclideanSpace ℂ I) where
  toFun y := besselCutoff (b ^ (6 * 𝔰.n + 2)) (besselLength y) • F y
  continuous_toFun :=
    (continuous_const.max (continuous_const.min (continuous_const.sub
      ((continuous_const.mul continuous_besselLength).div_const
        (b ^ (6 * 𝔰.n + 2)))))).smul F.continuous

section Cut

variable {b : ℝ} {F : C(𝔰.G₁, EuclideanSpace ℂ I)}

section

omit [DecidableEq I]

lemma besselCut_apply (y : 𝔰.G₁) :
    besselCut b F y = besselCutoff (b ^ (6 * 𝔰.n + 2)) (besselLength y) • F y := rfl

/-- `besselCut b F y` is `F y` multiplied by a number in `[0, 1]`, so its norm is at most
`‖F y‖`. -/
lemma enorm_besselCut_le (y : 𝔰.G₁) : ‖besselCut b F y‖ₑ ≤ ‖F y‖ₑ := by
  obtain ⟨h_nonneg, h_le⟩ := besselCutoff_mem_Icc (b ^ (6 * 𝔰.n + 2)) (besselLength y)
  rw [besselCut_apply, eNorm_le_iff_norm_le, norm_smul, Real.norm_of_nonneg h_nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) h_le

/-- `besselCut b F y` is `F y` multiplied by a number in `[0, 1]` (a cutoff evaluated at
`besselLength y`), so it differs from `F y` by at most `‖F y‖`. -/
lemma enorm_besselCut_sub_le (y : 𝔰.G₁) : ‖besselCut b F y - F y‖ₑ ≤ ‖F y‖ₑ := by
  obtain ⟨h_nonneg, h_le⟩ := besselCutoff_mem_Icc (b ^ (6 * 𝔰.n + 2)) (besselLength y)
  nth_rw 1 [← one_smul ℝ (F y)]
  rw [besselCut_apply, ← sub_smul, eNorm_le_iff_norm_le, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.2 ⟨by linarith, by linarith⟩)

/-- Where the cut of `F` is nonzero, the length is at most `b ^ (6 n + 2)` (`InCut`). -/
lemma inCut_of_besselCut_ne_zero (hb : 0 < b) {y : 𝔰.G₁} (hy : besselCut b F y ≠ 0) :
    InCut y b := by
  contrapose! hy with h_large
  rw [besselCut_apply, besselCutoff_eq_zero (by positivity) h_large.le, zero_smul]

/-- Where the cut of `F` differs from `F`, the length exceeds `b ^ (6 n + 2) / 2`. -/
lemma lt_besselLength_of_besselCut_ne (hb : 0 < b) {y : 𝔰.G₁} (hy : besselCut b F y ≠ F y) :
    b ^ (6 * 𝔰.n + 2) / 2 < besselLength y := by
  contrapose! hy with h_small
  rw [besselCut_apply, besselCutoff_eq_one (by positivity) h_small, one_smul]

end

/-- The cut of a continuous Bessel function is a Bessel function, as the length is left invariant
under `besselS`. -/
lemma IsBesselFunction.besselCut (hF : IsBesselFunction rep F) :
    IsBesselFunction rep (besselCut b F) :=
  hF.smul_of_invariant F.continuous
    (continuous_const.max (continuous_const.min (continuous_const.sub
      ((continuous_const.mul continuous_besselLength).div_const (b ^ (6 * 𝔰.n + 2))))))
    (K := 1)
    (fun y ↦ abs_le.2 ⟨(neg_nonpos.2 zero_le_one).trans (besselCutoff_mem_Icc _ _).1,
      (besselCutoff_mem_Icc _ _).2⟩)
    fun s hs y ↦ by rw [besselLength_besselS_mul hs]

omit [DecidableEq I] in
/-- Let `F♭ = besselCut b F` be the product of `F : G₁ → ℂ^I` with a cutoff of the length
`besselLength` that is `1` up to `b ^ (6 n + 2) / 2`, where `n = ϱ + 1`, and let `r` be the size of
the matrices of `G₁`. Let `w ≤ a` be a decay majorant (`IsDecayMajorant`) of the pair `F`, `F♭`
(formed by `FullOrCut.select`): `‖F y‖` and `‖F♭ y‖`, each multiplied by
`max 1 (besselLength y / b ^ (6 n)) ^ (3 r ^ 3 f)`, are at most `w y`, and `a ∫ w` is at most
`b ^ (400 r ^ 2) * card I`. If `b ≥ 2`, `r ≥ 100` and `f ≠ 0`, then `‖F♭ - F‖₂ ^ 2` is at most
`b ^ (-2 r ^ 3 f) * card I`. The integrals are over 𝖴∖G₁. -/
lemma IsDecayMajorant.lintegral_sq_besselCut_sub_le {f : ℕ} [NeZero f] {w : 𝔰.G₁ → ℝ≥0∞}
    {a : ℝ≥0∞} (hw : IsDecayMajorant b f (FullOrCut.select F (besselCut b F)) w a)
    (hb : 2 ≤ b) (hr : 100 ≤ 𝔰.r) :
    ∫⁻ y : 𝔰.G₁, ‖besselCut b F y - F y‖ₑ ^ 2 ∂besselQuotMeasure ≤
      .ofReal (b⁻¹ ^ (𝔰.r ^ 3 * f)) ^ 2 * card I := by
  -- Where the cut acts the scaled length is at least `b`, so `b ^ (3 r ^ 3 f) ‖F♭ - F‖ ≤ w ≤ a`.
  -- Multiply the two bounds and integrate.
  have hb_pos : 0 < b := two_pos.trans_le hb
  have h_point (y : 𝔰.G₁) :
      .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2 * ‖besselCut b F y - F y‖ₑ ^ 2 ≤ a * w y := by
    obtain h_eq | h_ne := eq_or_ne (besselCut b F y) (F y)
    · rw [h_eq, sub_self, eNorm_zero, zero_pow two_ne_zero, mul_zero]
      exact zero_le
    have h_gain : .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) * ‖besselCut b F y - F y‖ₑ ≤ w y :=
      (mul_le_mul' (ofReal_le_ofReal (pow_le_pow_left₀ hb_pos.le
        (le_scaledBesselLength hb (lt_besselLength_of_besselCut_ne hb_pos h_ne)) _))
        (enorm_besselCut_sub_le y)).trans (hw.pow_mul_enorm_le .full y)
    rw [← mul_pow, sq]
    exact mul_le_mul' (h_gain.trans (hw.le_bound y)) h_gain
  -- Exponents: `400 r ^ 2 + 2 r ^ 3 f ≤ 6 r ^ 3 f`, as `100 r ^ 2 ≤ r ^ 3 ≤ r ^ 3 f`.
  have h_exponent : 100 * 𝔰.r ^ 2 ≤ 𝔰.r ^ 3 * f :=
    ((Nat.mul_le_mul_right (𝔰.r ^ 2) hr).trans_eq (pow_succ' 𝔰.r 2).symm).trans
      (Nat.le_mul_of_pos_right _ (NeZero.pos f))
  have h_power : b ^ (400 * 𝔰.r ^ 2) ≤ (b ^ (3 * 𝔰.r ^ 3 * f) * b⁻¹ ^ (𝔰.r ^ 3 * f)) ^ 2 := by
    have h_split : b ^ (3 * 𝔰.r ^ 3 * f) * b⁻¹ ^ (𝔰.r ^ 3 * f) = b ^ (2 * (𝔰.r ^ 3 * f)) := by
      rw [mul_assoc 3, show 3 * (𝔰.r ^ 3 * f) = 2 * (𝔰.r ^ 3 * f) + 𝔰.r ^ 3 * f by omega, pow_add,
        mul_assoc, ← mul_pow, mul_inv_cancel₀ hb_pos.ne', one_pow, mul_one]
    rw [h_split, ← pow_mul]
    exact pow_le_pow_right₀ (one_le_two.trans hb) (by omega)
  rw [← ENNReal.mul_le_mul_iff_right (a := .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2)
    (pow_ne_zero 2 (ENNReal.ofReal_pos.2 (pow_pos hb_pos _)).ne') (pow_ne_top ofReal_ne_top)]
  calc .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2 * ∫⁻ y, ‖besselCut b F y - F y‖ₑ ^ 2 ∂besselQuotMeasure
      ≤ ∫⁻ y, a * w y ∂besselQuotMeasure :=
        (lintegral_const_mul_le ..).trans (lintegral_mono h_point)
    _ ≤ .ofReal (b ^ (400 * 𝔰.r ^ 2)) * card I :=
        (lintegral_const_mul _ hw.measurable).trans_le hw.bound_mul_lintegral_le
    _ ≤ .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2 * (.ofReal (b⁻¹ ^ (𝔰.r ^ 3 * f)) ^ 2 * card I) := by
        rw [← mul_assoc]
        refine mul_le_mul' ((ofReal_le_ofReal h_power).trans_eq ?_) le_rfl
        rw [ofReal_pow (mul_nonneg (pow_nonneg hb_pos.le _)
            (pow_nonneg (inv_nonneg.2 hb_pos.le) _)),
          ofReal_mul (pow_nonneg hb_pos.le _), mul_pow]

end Cut

/-- For `t` in the Bessel subgroup `besselS`, the integral of `φ (x⁻¹ s y)` over `s` in that
subgroup does not change when `y` is replaced by `t y`, as the measure on `besselGraph` is right
invariant. -/
lemma lintegral_besselGraph_mul_eq {x : 𝔰.G₁} (φ : 𝔰.G₁ → ℝ≥0∞) {t : 𝔰.G₁} (ht : t ∈ besselS)
    (y : 𝔰.G₁) :
    ∫⁻ s : 𝔰.besselGraph, φ (x⁻¹ * (s.val.fst * (t * y))) ∂𝔰.besselGraphMeasure =
      ∫⁻ s : 𝔰.besselGraph, φ (x⁻¹ * (s.val.fst * y)) ∂𝔰.besselGraphMeasure := by
  have : MeasurableMul ↥𝔰.besselGraph := inferInstance
  obtain ⟨u, hu, k, rfl⟩ := exists_besselU_mul_toBesselH ht isUnit_one
  have h_mem : (u * toBesselH 𝔰 1 k, k) ∈ 𝔰.besselGraph := by
    rw [Shape.mem_besselGraph_iff_mul_inv_mem]
    dsimp only [RealPlace.embedH]
    rwa [mul_inv_cancel_right]
  have h_eq := lintegral_mul_right_eq_self (μ := 𝔰.besselGraphMeasure)
    (fun s ↦ φ (x⁻¹ * (s.val.fst * y))) ⟨(u * toBesselH 𝔰 1 k, k), h_mem⟩
  refine (lintegral_congr fun s ↦ ?_).trans h_eq
  exact congrArg (fun g ↦ φ (x⁻¹ * g)) (mul_assoc s.val.fst (u * toBesselH 𝔰 1 k) y).symm

/-- Let `r` be the size of the matrices of `G₁`, `n = ϱ + 1`, and `l = 2λ` a discrete series
parameter of gap `500 r ^ 3 + A`, with entries bounded by `L` and formal degree `deg`. Let
`W = besselAverage l rep x v` be the average of its coefficient `c_λ` over the Bessel subgroup 𝖴H at
a unit vector `v` and a point `x` with `besselLength x ≤ b ^ (5 n)`. Suppose that
`b ^ m * deg * ‖W‖₂ ^ 2` is at least `besselBallVolume x` (the volume of the `s` in 𝖴H with
`‖x⁻¹ s x - 1‖ ≤ 1`), that `F = c W` has `‖F‖₂ ^ 2 = card I`, and that `b ≥ 2000`,
`r + L + 1 ≤ b ^ 4`, `m ≤ 301 r ^ 2` and `3 r ^ 3 f ≤ A`. Then `F` and its cut `F♭ = besselCut b F`
have a decay majorant (`IsDecayMajorant`): a left 𝖴H-invariant function `w ≤ a < ∞` such that
`‖F y‖` and `‖F♭ y‖`, each multiplied by `max 1 (besselLength y / b ^ (6 n)) ^ (3 r ^ 3 f)`, are at
most `w y`, and `a ∫ w ≤ b ^ (400 r ^ 2) * card I`. -/
lemma exists_isDecayMajorant_besselAverage {f m : ℕ} {b : ℝ} {x : 𝔰.G₁} {v : EuclideanSpace ℂ I}
    (h_gap : l.HasLargeGap A) (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) (hv : ‖v‖ = 1)
    (h_volume : besselBallVolume (ε := ε) x ≤ ENNReal.ofReal (b ^ m) *
      (ENNReal.ofReal l.formalDegree *
        ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure))
    (hx : besselLength x ≤ b ^ (5 * 𝔰.n)) (hb_large : 2000 ≤ b)
    (hm : m + 99 * 𝔰.r ^ 2 ≤ 400 * 𝔰.r ^ 2) (hL_le : 𝔰.r + L + 1 ≤ b ^ 4)
    (hf : 3 * 𝔰.r ^ 3 * f ≤ A) {c : ℝ} {F : C(𝔰.G₁, EuclideanSpace ℂ I)}
    (hF : ∀ y : 𝔰.G₁, F y = c • besselAverage l rep x v y)
    (hc : ‖c‖ₑ ^ 2 * ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure = card I) :
    ∃ (w : 𝔰.G₁ → ℝ≥0∞) (a : ℝ≥0∞),
      IsDecayMajorant b f (FullOrCut.select F (besselCut b F)) w a := by
  -- With `φ g = (2 / ‖g‖) ^ M` and `Φ y = ∫ φ (x⁻¹ s y) ds`, the majorant is `|c| Φ`. It is bounded
  -- by `lintegral_decay_le_besselBallVolume`, and unfolding gives its integral; the volume of the
  -- ball cancels against the norm of `W`.
  have : SFinite 𝔰.besselGraphMeasure := sFinite_besselGraphMeasure
  obtain ⟨hb_one, hb_two⟩ : 1 ≤ b ∧ 2 ≤ b := ⟨by linarith, by linarith⟩
  let M : ℕ := 9 * 𝔰.r ^ 2
  let φ (g : 𝔰.G₁) : ℝ≥0∞ := .ofReal ((2 / ‖g.val.val‖) ^ M)
  have hφ_meas : Measurable φ :=
    ((measurable_const.div measurable_norm_U).pow_const M).ennreal_ofReal
  let Φ (y : 𝔰.G₁) : ℝ≥0∞ := ∫⁻ s, φ (x⁻¹ * (s.val.fst * y)) ∂𝔰.besselGraphMeasure
  have hΦ_meas : Measurable Φ :=
    (hφ_meas.comp
      (continuous_const.mul
        ((continuous_fst.comp (continuous_subtypeVal.comp continuous_fst)).mul
          continuous_snd)).measurable).lintegral_prod_left'
  let a : ℝ≥0∞ := ‖c‖ₑ * (.ofReal (16 ^ M) * besselBallVolume (ε := ε) x)
  have h_decay (y : 𝔰.G₁) :
      .ofReal (scaledBesselLength y b ^ (3 * 𝔰.r ^ 3 * f)) * ‖F y‖ₑ ≤ ‖c‖ₑ * Φ y := by
    rw [hF, eNorm_smul, mul_left_comm]
    exact mul_le_mul' le_rfl
      (scaledBesselLength_pow_mul_enorm_besselAverage_le h_gap hv hb_two hx hf y)
  have h_bound (y : 𝔰.G₁) : Φ y ≤ .ofReal (16 ^ M) * besselBallVolume (ε := ε) x :=
    (lintegral_congr fun s ↦ by dsimp only [φ]; rw [norm_frameEquiv]).trans_le
      (lintegral_decay_le_besselBallVolume x y)
  have h_integral : a * ∫⁻ y, ‖c‖ₑ * Φ y ∂besselQuotMeasure ≤
      .ofReal (b ^ (400 * 𝔰.r ^ 2)) * card I :=
    calc _ = ‖c‖ₑ ^ 2 * (.ofReal (16 ^ M) * besselBallVolume (ε := ε) x) * ∫⁻ g, φ g := by
          rw [lintegral_const_mul' _ _ eNorm_ne_top,
            lintegral_unfold_besselGraphMeasure (x := x⁻¹) φ hφ_meas]
          dsimp only [a]
          ring
      _ ≤ .ofReal (b ^ m) * (.ofReal l.formalDegree * (∫⁻ g, φ g) * .ofReal (16 ^ M)) *
            (‖c‖ₑ ^ 2 * ∫⁻ y, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure) := by
          refine (mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul' le_rfl h_volume)) le_rfl).trans_eq ?_
          ring
      _ ≤ .ofReal (b ^ (400 * 𝔰.r ^ 2)) * card I := by
          rw [hc]
          refine mul_le_mul' ((mul_le_mul' le_rfl
            (formalDegree_mul_lintegral_decay_le h_gap hL hb_large hL_le rfl)).trans ?_) le_rfl
          rw [← ofReal_mul (pow_nonneg (zero_le_one.trans hb_one) m), ← pow_add]
          exact ofReal_le_ofReal (pow_le_pow_right₀ hb_one hm)
  exact ⟨fun y ↦ ‖c‖ₑ * Φ y, a,
    { measurable := measurable_const.mul hΦ_meas
      fixesLeft s hs y := congrArg (‖c‖ₑ * ·) (lintegral_besselGraph_mul_eq φ hs y)
      pow_mul_enorm_le
        | .full, y => h_decay y
        | .cut, y => (mul_le_mul_right (enorm_besselCut_le y) _).trans (h_decay y)
      le_bound y := mul_le_mul_right (h_bound y) _
      bound_ne_top := ENNReal.mul_ne_top eNorm_ne_top
        (ENNReal.mul_ne_top ofReal_ne_top (besselBallVolume_ne_top (ε := ε) x))
      bound_mul_lintegral_le := h_integral }⟩

/-- The Bessel function and its cut. Fix a unitary matrix that takes the form of G₁ to the diagonal
form with signs `ε` (the instance `UnitarySignFrame 𝔰 ε`). Let `l = 2λ` be a parameter for `ε` of
gap `500 r ^ 3 + A` with entries bounded by `L`. Let `c_λ = l.dsCoeffInFrame` be its discrete series
coefficient in this frame, and `deg = l.formalDegree`. Let `rep` be a continuous unitary
representation of U(κ) on ℂ^I, where κ indexes the summand X₀. Let `W = besselAverage l rep x v` be
the average of `c_λ` over the Bessel subgroup at a unit vector `v` and a point `x` with
`besselLength x ≤ b ^ (5 n)`. Assume `deg ‖W‖₂ ^ 2` is at least `b ^ (-m)` times
`besselBallVolume x`. Suppose `b ≥ 2000`, `r + L + 1 ≤ b ^ 4`, `r ≥ 100`, `f ≠ 0`, `m ≤ 301 r ^ 2`
and `3 r ^ 3 f ≤ A`. Then a real multiple `F` of `W` is fixed by convolution with `deg * c_λ`. It
also forms a cut pair with its cut `besselCut b F`. Here `IsCutPair` means Bessel functions, the
first normalised, close in L², with a decay majorant. Here `r` is the size of the matrices of G₁,
`n = ϱ + 1` with ϱ the number of hyperbolic planes, and `‖·‖₂` is the norm of L²(𝖴∖G₁), 𝖴 the Bessel
unipotent group. -/
lemma exists_isCutPair_besselAverage {m : ℕ} {b : ℝ} {x : 𝔰.G₁} {v : EuclideanSpace ℂ I}
    (h_gap : l.HasLargeGap A) (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) (f : ℕ) [NeZero f]
    (h_cont : Continuous rep) (hv : ‖v‖ = 1)
    (h_volume : besselBallVolume (ε := ε) x ≤ ENNReal.ofReal (b ^ m) *
      (ENNReal.ofReal l.formalDegree *
        ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure))
    (hx : besselLength x ≤ b ^ (5 * 𝔰.n)) (hb_large : 2000 ≤ b) (hr : 100 ≤ 𝔰.r)
    (hm : m + 99 * 𝔰.r ^ 2 ≤ 400 * 𝔰.r ^ 2) (hL_le : 𝔰.r + L + 1 ≤ b ^ 4)
    (hf : 3 * 𝔰.r ^ 3 * f ≤ A) :
    ∃ (c : ℝ) (F : C(𝔰.G₁, EuclideanSpace ℂ I)),
      (∀ y : 𝔰.G₁, F y = c • besselAverage l rep x v y) ∧
      convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F ∧
      IsCutPair b f rep (FullOrCut.select F (besselCut b F)) := by
  set W : 𝔰.G₁ → EuclideanSpace ℂ I := besselAverage l rep x v
  set e : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  have hW : IsBesselFunction rep W := isBesselFunction_besselAverage x h_cont hv h_gap
  have h_repr : convolve W e = W := convolve_besselAverage x h_cont hv h_gap
  have hW_cont : Continuous W := by
    rw [← h_repr]
    exact hW.continuous_convolve (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
  have hW_int : Integrable W besselQuotMeasure := integrable_besselAverage x h_cont hv h_gap
  -- Normalisation: `W` is not zero in L², because the ball has positive volume.
  have h_ne_zero : ∫⁻ y, ‖W y‖ₑ ^ 2 ∂besselQuotMeasure ≠ 0 := fun h ↦ by
    rw [h, mul_zero, mul_zero, nonpos_iff_eq_zero] at h_volume
    exact besselBallVolume_ne_zero x h_volume
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ‖c‖ₑ ^ 2 * ∫⁻ y, ‖W y‖ₑ ^ 2 ∂besselQuotMeasure = card I :=
    exists_enorm_sq_mul_eq h_ne_zero
      ((lintegral_enorm_sq hW_int hW.memLp_top).trans_ne ofReal_ne_top) (card I)
  let F : C(𝔰.G₁, EuclideanSpace ℂ I) := ⟨fun y ↦ c • W y, hW_cont.const_smul c⟩
  have hF : IsBesselFunction rep F :=
    hW.smul_of_invariant hW_cont continuous_const (K := |c|) (fun _ ↦ le_rfl) fun _ _ _ ↦ rfl
  have hF_norm : ∫⁻ y, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure = card I := by
    trans ∫⁻ y, ‖c‖ₑ ^ 2 * ‖W y‖ₑ ^ 2 ∂besselQuotMeasure
    · exact lintegral_congr fun y ↦ by rw [ContinuousMap.coe_mk, eNorm_smul, mul_pow]
    · rw [lintegral_const_mul' _ _ (pow_ne_top eNorm_ne_top), hc]
  have hF_repr : convolve F e = F := by
    funext y
    calc convolve F e y = c • convolve W e y := by
          change ∫ a, e a⁻¹ • (c • W (y * a)) = c • ∫ a, e a⁻¹ • W (y * a)
          exact (integral_congr_ae (.of_forall fun a ↦ smul_comm (e a⁻¹) c (W (y * a)))).trans
            (integral_smul c (fun a ↦ e a⁻¹ • W (y * a)))
      _ = c • W y := by rw [h_repr]
  have hb_two : 2 ≤ b := by linarith
  have hb_pos : 0 < b := two_pos.trans_le hb_two
  obtain ⟨w, a, hw⟩ : ∃ (w : 𝔰.G₁ → ℝ≥0∞) (a : ℝ≥0∞),
      IsDecayMajorant b f (FullOrCut.select F (besselCut b F)) w a :=
    exists_isDecayMajorant_besselAverage h_gap hL hv h_volume hx hb_large hm hL_le hf
      (fun _ ↦ rfl) hc
  exact ⟨c, F, fun _ ↦ rfl, hF_repr,
    { isBesselFunction
        | .full => hF
        | .cut => hF.besselCut
      integrable := hW_int.smul c
      lintegral_sq_full_eq := hF_norm
      lintegral_sq_cut_le :=
        (lintegral_mono fun y ↦ pow_le_pow_left' (enorm_besselCut_le y) 2).trans_eq hF_norm
      inCut_of_ne_zero y := inCut_of_besselCut_ne_zero hb_pos
      lintegral_sq_sub_le := hw.lintegral_sq_besselCut_sub_le hb_two hr
      lt_besselLength_of_ne y := lt_besselLength_of_besselCut_ne hb_pos
      exists_majorant := ⟨w, a, hw⟩ }⟩

end New
end
end

section
/-!
# Schur's bound for a Bessel function and its derivatives

Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap and `c_λ` the coefficient `dsCoeff`
on `U(diag ε)` of its discrete series; the same letter stands for its pullback
`New.HCParam.dsCoeffInFrame` to `G₁` by the frame. Let `deg` be the formal degree
`New.HCParam.formalDegree`. Write `(F * k) y = ∫ k a⁻¹ • F (y a)` and `e = deg · c_λ`; as
`e a⁻¹ = deg · conj (c_λ a)`, the condition `F * e = F` says that `F` is fixed by the idempotent of
the discrete series. Such a bounded function has right derivatives of all orders, and they are
convolutions with kernels of controlled norm. Schur's bound in `L²(𝖴 ∖ G₁)` follows, `𝖴` being the
unipotent group `besselU`.

Notions from other files:
* `l : New.HCParam ε` is twice a Harish-Chandra parameter; `HasLargeGap A` bounds its gaps below.
* `p : UnitarySignFrame 𝔰 ε` is a unitary frame in which the form of `G₁` is `diag ε`.
* `frameEquiv : G₁ ≃ₜ* U(diag ε)` is conjugation by the frame.
* `Bumps ε` are the smooth compactly supported functions on `U(diag ε)`; `smear f` sends a bump `β`
  to the convolution of the continuous function `f` with `β`.
* `bumpDeriv` is the action of matrices on bumps by differentiation, `adTwist g` precomposes it with
  conjugation by `g`, and `word w` applies the action of the matrix units of the word `w`.
* `New.IsBesselFunction rep F`: `F` is bounded, measurable and transforms by a character under
  `besselU` and by `rep` under `U(κ)`.
* `𝔰.r` is the number of indices `BesselIndex` of `G₁`, and `𝔰.n` is one more than the number of
  hyperbolic planes of the shape `𝔰`.
* `RealPlace.HasSchurBound F rep B C`: `F` has right derivatives of all orders that are again Bessel
  functions, those of order `s ≤ 2 n ^ 2` satisfying Schur's `L²` bound with `B ^ (2 s) C`.
* `besselQuotMeasure` is the measure on `G₁` that represents integration over `besselU ∖ G₁`.

## Relation to the literature

Known result: Smoothness and Schur's orthogonality relations for vectors of a discrete series
representation (Harish-Chandra).
-/

@[expose] public section

namespace New

open Matrix MeasureTheory ENNReal Norms.L2Operator Fintype CStarRing Set DiscreteSeries
  InnerProductSpace

variable {𝔰 : Shape} {I : Type} {ε : 𝔰.BesselIndex → ℤˣ} [Fintype I] [DecidableEq I]
  [p : UnitarySignFrame 𝔰 ε]

section Kernels

variable {l : HCParam ε} {A L : ℕ}

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap, `c_λ = l.dsCoeffInFrame` the
coefficient on `G₁` of its discrete series and `deg = l.formalDegree` the formal degree. Then
`deg · c_λ` is bounded and measurable. -/
lemma isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame (h_gap : l.HasLargeGap A) :
    IsBoundedMeasurable fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g := by
  refine .of_continuous ⟨_, fun g ↦ (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
    (norm_dsCoeff_le_one h_gap _) (norm_nonneg _))⟩
      (isIdempotentKernel_dsCoeffInFrame h_gap).continuous

/-- For the unitary frame `p`, each matrix unit `Matrix.single i j 1` conjugated by it,
`p.matrix⁻¹ * Matrix.single i j 1 * p.matrix`, has norm one. -/
lemma norm_frame_conj_single (i j : 𝔰.BesselIndex) :
    ‖p.matrix⁻¹.val * Matrix.single i j (1 : ℂ) * p.matrix.val‖ = 1 := by
  rw [Units.inv_eq_of_mul_eq_one_left (Unitary.star_mul_self_of_mem p.mem_unitary),
    norm_mul_mem_unitary _ p.mem_unitary,
    norm_mem_unitary_mul _ (Unitary.star_mem p.mem_unitary)]
  simp [l2_opNorm_single]

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter with `l.HasLargeGap A` (gap `500 r³ + A`) and
entries bounded by `L`. Let `β` be a bump function whose convolution (`smear`) with `c_λ` is `c_λ`,
the generator of `U(𝔤) c_λ = l.DsModule`. Let `w` be a word of length `s` in the matrix units,
acting through `adTwist p.matrix⁻¹`. The convolution of `c_λ` with the derivative of `β` along `w`
is a vector `x` of step `s` of the filtration of `U(𝔤) c_λ`, with
`‖x‖ ≤ ((r + 1) ^ 4 (L + r + 1 + s)) ^ s`. Here `r = 𝔰.r` is the size of the matrices, and `‖x‖` is
the `L²` norm of `x` times the square root of the formal degree. -/
lemma exists_mem_filtration_smear_word (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) {β : Bumps ε}
    (hβ : (smear l.dsCoeffSmooth.val) β = (l.dsGenerator : USign ε → ℂ))
    (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
    ∃ x ∈ l.dsAction.filtration ε l.dsGenerator w.length,
      ‖x‖ ≤ ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ w.length ∧
      (smear l.dsCoeffSmooth.val) ((bumpDeriv.adTwist p.matrix⁻¹).word w β) =
        (x : USign ε → ℂ) := by
  -- A matrix of norm one moves step `s` of the filtration to step `s + 1` and multiplies the norm
  -- by at most `(r + 1) ^ 4 (L + r + 1 + s)`, since `L + r` bounds the lowest `K`-type.
  induction w with
  | nil => exact ⟨_, GlModule.self_mem_filtration, h_gap.norm_dsGenerator.le, hβ⟩
  | cons q w ih =>
    obtain ⟨x, x_mem, x_le, x_eq⟩ := ih
    -- Apply the conjugated matrix unit of the first letter of the word to `x`.
    let M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := p.matrix⁻¹.val * .single q.1 q.2 1 * p.matrix
    obtain ⟨step_mem,
      (step_le : ‖l.dsAction M x‖ ≤ (𝔰.r + 1) ^ 4 * ((L + 𝔰.r : ℕ) + 1 + w.length) * ‖M‖ * ‖x‖)⟩ :=
      (isKHighest_dsGenerator h_gap).norm_apply_le_of_mem_filtration h_gap.isUnitaryCasimirGe
        (abs_lowestKType_le h_gap hL) x_mem M
    refine ⟨l.dsAction M x, step_mem, step_le.trans ?_, rightDeriv_smear _ _ x_eq M⟩
    rw [show ‖M‖ = 1 from norm_frame_conj_single q.1 q.2, mul_one, List.length_cons,
      pow_succ' _ w.length]
    push_cast
    grw [x_le]
    gcongr <;> linarith

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap, `c_λ = l.dsCoeffInFrame` the
coefficient on `G₁` of its discrete series and `deg = l.formalDegree` the formal degree. Then
`deg · c_λ` is idempotent under convolution on `G₁`. -/
lemma convolve_formalDegree_mul_dsCoeffInFrame_self (h_gap : l.HasLargeGap A) :
    convolve (fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g)
        (fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g) =
      fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g := by
  set idem : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  have idem_ker : IsIdempotentKernel idem := isIdempotentKernel_dsCoeffInFrame h_gap
  ext y
  have h_repro : ∫ a : 𝔰.G₁, idem a⁻¹ * idem (y * (a * 1)) = idem y / idem 1 * idem 1 :=
    idem_ker.integral_inv_mul_translate y 1
  rw [div_mul_cancel₀ _ idem_ker.apply_one_ne_zero] at h_repro
  simpa only [mul_one, convolve, smul_eq_mul] using h_repro

/-- Let `l = 2λ` be a doubled Harish-Chandra parameter, `c_λ = l.dsCoeff` its coefficient on
`U(diag ε)`, `deg = l.formalDegree` the inverse of `∫ |c_λ| ^ 2`, and `β` a bump function on
`U(diag ε)`. The convolution on `G₁` of the pullbacks of `deg · c_λ` and `β` by the frame is the
pullback of `deg` times the convolution (`smear`) of `c_λ` with `β` on `U(diag ε)`. -/
lemma convolve_formalDegree_mul_dsCoeffInFrame_comp_frameEquiv (l : HCParam ε) (β : Bumps ε) :
    convolve (fun g : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame g)
        (fun g : 𝔰.G₁ ↦ (β : USign ε → ℂ) (frameEquiv g)) =
      fun g : 𝔰.G₁ ↦
        (l.formalDegree : ℂ) * (smear l.dsCoeffSmooth.val) β (frameEquiv g) := by
  -- The frame carries the Haar measure of `G₁` to that of `U(diag ε)`.
  let π : 𝔰.G₁ ≃ₜ* USign ε := frameEquiv
  ext y
  calc ∫ a : 𝔰.G₁, (β : USign ε → ℂ) (π a⁻¹) • ((l.formalDegree : ℂ) * l.dsCoeff (π (y * a)))
    _ = l.formalDegree *
        ∫ a : 𝔰.G₁, (β : USign ε → ℂ) (π a)⁻¹ • l.dsCoeff (π y * π a : USign ε) := by
      simp only [← integral_const_mul, map_mul, map_inv, mul_smul_comm]
    _ = l.formalDegree * (smear l.dsCoeffSmooth.val) β (π y) := by
      simp [smear_apply, π, ← integral_comp_frameEquiv (J := 𝔰.J₁)]

omit [UnitarySignFrame 𝔰 ε] in
/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap, `c_λ` the coefficient on
`U(diag ε)` of its discrete series and `deg = l.formalDegree` the formal degree. The squared norm
of a vector `x` of `U(𝔤) c_λ = l.DsModule`, a space of smooth functions on `U(diag ε)`, is `deg`
times the integral of `|x| ^ 2`. -/
lemma HCParam.HasLargeGap.norm_sq_eq_formalDegree_mul_integral (h_gap : l.HasLargeGap A)
    (x : l.DsModule) :
    ‖x‖ ^ 2 = l.formalDegree * ∫ g : USign ε, ‖(x : USign ε → ℂ) g‖ ^ 2 := by
  have h_inner : ⟪h_gap.toL2 x, rightRegularL2 1 (h_gap.toL2 x)⟫_ℂ = l.formalDegree *
      ∫ g : USign ε, (x : USign ε → ℂ) (g * 1) * starRingEnd ℂ ((x : USign ε → ℂ) g) :=
    h_gap.inner_toL2_rightRegularL2 x x 1
  -- The norm of `U(𝔤) c_λ` is by definition that of the image in `L²`.
  change ‖h_gap.toL2 x‖ ^ 2 = _
  simpa [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal] using
    congrArg Complex.re h_inner

omit [DecidableEq I] in
/-- Let `l = 2λ` be a doubled Harish-Chandra parameter of large gap with entries bounded by `L`,
`c_λ = l.dsCoeffInFrame` the coefficient on `G₁` of its discrete series, `deg = l.formalDegree` the
formal degree, and `r = 𝔰.r` the size of the matrices of `G₁`. To each word `w` in the matrix units
belongs an integrable kernel `X w`, with `X [] = deg · c_λ` and `X [] * X w = X w`. For a word of
length `s` the number `‖X w‖₂ ^ 2 / deg` is at most `((r + 1) ^ 4 (L + r + 1 + s)) ^ (2 s)`. For
every bounded measurable `F` with `F * X [] = F` the functions `F * X w` are the right derivatives
of `F`: along a curve `γ` with `γ' t = γ t · Z`, the derivative of `F * X w` at `t` is
`∑ Z a b • (F * X ((a, b) :: w)) (γ t)`. -/
theorem exists_derivative_kernels (h_gap : l.HasLargeGap A)
    (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L) :
    ∃ X : List (𝔰.BesselIndex × 𝔰.BesselIndex) → 𝔰.G₁ → ℂ,
      (X [] = fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) ∧
      (∀ w : List (𝔰.BesselIndex × 𝔰.BesselIndex), Integrable (X w)) ∧
      (∀ w : List (𝔰.BesselIndex × 𝔰.BesselIndex), convolve (X []) (X w) = X w) ∧
      (∀ w : List (𝔰.BesselIndex × 𝔰.BesselIndex),
        (∫ g : 𝔰.G₁, ‖X w g‖ ^ 2) / l.formalDegree ≤
          ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ (2 * w.length)) ∧
      ∀ F : 𝔰.G₁ → EuclideanSpace ℂ I, IsBoundedMeasurable F → convolve F (X []) = F →
        ∀ (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) (γ : ℝ → 𝔰.G₁)
          (Z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (t : ℝ),
          HasDerivAt (fun s : ℝ ↦ (γ s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) (γ t * Z) t →
          HasDerivAt (convolve F (X w) ∘ γ)
            (∑ a : 𝔰.BesselIndex, ∑ b : 𝔰.BesselIndex,
              Z a b • convolve F (X ((a, b) :: w)) (γ t)) t := by
  -- A bump `β` reproduces `c_λ`. Let `bump w` be its derivative along `w`, and
  -- `X w = idem * bump w` with `idem = deg · c_λ`. Then `X w / deg` is a vector of `U(𝔤) c_λ`,
  -- whose norm is bounded letter by letter.
  let idem : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  obtain ⟨β, hβ : (smear l.dsCoeffSmooth.val) β = (l.dsGenerator : USign ε → ℂ)⟩ :=
    exists_smear_dsCoeffSmooth_eq h_gap l.dsGenerator
  have idem_int : Integrable idem := (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
  have idem_bdd : IsBoundedMeasurable idem :=
    isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame h_gap
  let π : 𝔰.G₁ ≃ₜ* USign ε := frameEquiv
  let bump (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) : Bumps ε :=
    (bumpDeriv.adTwist p.matrix⁻¹).word w β
  let smearCoeff : Bumps ε →ₗ[ℂ] USign ε → ℂ := smear l.dsCoeffSmooth.val
  let X (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) (g : 𝔰.G₁) : ℂ :=
    l.formalDegree * smearCoeff (bump w) (π g)
  have bump_int (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
      Integrable ((bump w : USign ε → ℂ) ∘ π) :=
    measurePreserving_frameEquiv.integrable_comp_of_integrable (bump w).prop.integrable
  have X_eq (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
      convolve idem ((bump w : USign ε → ℂ) ∘ π) = X w :=
    convolve_formalDegree_mul_dsCoeffInFrame_comp_frameEquiv l (bump w)
  -- The generator is `dsCoeff`, whose pullback by the frame is `dsCoeffInFrame` by definition.
  have X_nil : X [] = idem := funext fun g ↦ congrArg (_ * ·) (congrFun hβ (π g))
  refine ⟨X, X_nil, fun w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_, fun F hF F_conv w γ Z t hZ ↦ ?_⟩
  · rw [← X_eq]
    exact integrable_convolve idem_int (bump_int w)
  · rw [X_nil, ← X_eq, ← idem_bdd.convolve_assoc idem_int (bump_int w),
      convolve_formalDegree_mul_dsCoeffInFrame_self h_gap]
  · obtain ⟨x, -, x_le, x_eq : smearCoeff (bump w) = (x : USign ε → ℂ)⟩ :=
      exists_mem_filtration_smear_word (p := p) h_gap hL hβ w
    have norm_sq : ‖x‖ ^ 2 = (∫ g : 𝔰.G₁, ‖X w g‖ ^ 2) / l.formalDegree := by
      rw [h_gap.norm_sq_eq_formalDegree_mul_integral, ← integral_comp_frameEquiv (J := 𝔰.J₁)]
      simp [X, x_eq, field, mul_pow, integral_const_mul]
    grw [← norm_sq, x_le, pow_mul']
  · -- `F * X w = F * bump w`; differentiate the bump and expand `Z` in matrix units.
    rw [X_nil] at F_conv
    have F_cont : Continuous (F ∘ π.invFun) := by
      simpa only [F_conv] using (hF.continuous_convolve idem_int).comp π.continuous_invFun
    have FX_eq (w : List (𝔰.BesselIndex × 𝔰.BesselIndex)) :
        convolve F (X w) = smear (F ∘ π.invFun) F_cont (bump w) ∘ π := by
      rw [← X_eq, ← hF.convolve_assoc idem_int (bump_int w), F_conv]
      simp [funext_iff, π, convolve, ← integral_comp_frameEquiv]
    rw [FX_eq w]
    refine .congr_deriv (hasDerivAt_smear _ _ F_cont (X := p.matrix⁻¹.val * Z * p.matrix) ?_) ?_
    · simpa [π, frameEquiv, U.conj, mul_assoc] using (hZ.const_mul p.matrix⁻¹.val).mul_const
        p.matrix.val
    · -- Conjugating by the frame twists the action; the letter `(a, b)` acts by a matrix unit.
      change smear _ F_cont (bumpDeriv.adTwist p.matrix⁻¹ Z (bump w)) (π (γ t)) = _
      rw [(bumpDeriv.adTwist p.matrix⁻¹).apply_eq_sum Z]
      simp only [FX_eq, Function.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
        map_smul, Finset.sum_apply, Pi.smul_apply]
      rfl

end Kernels

/-- Let `l = 2λ` satisfy `l.HasLargeGap A` (gap `500 r³ + A`), with coefficient `c_λ` on `G₁` and
formal degree `deg`. Let `rep` be a unitary representation of `U(κ)` on `ℂ^I`. Let `F` be a Bessel
function for `rep`, integrable over `𝖴 ∖ G₁` (`besselQuotMeasure`) and fixed by convolution with
`deg · c_λ`. The squared norm in `L²(G₁)` of the matrix coefficient `g ↦ ∫ ⟪F y, F (y g)⟫` is
`‖F‖₂ ^ 4 / deg`, as this coefficient is `c_λ` times `‖F‖₂ ^ 2`. The integral in `y` and the norm
`‖F‖₂` are taken over `𝖴 ∖ G₁`. -/
theorem IsBesselFunction.lintegral_enorm_sq_integral_inner_translate
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {l : HCParam ε} {A : ℕ}
    (h_gap : l.HasLargeGap A) {F : 𝔰.G₁ → EuclideanSpace ℂ I} (hF : IsBesselFunction rep F)
    (F_int : Integrable F besselQuotMeasure)
    (F_conv : convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F) :
    ∫⁻ g : 𝔰.G₁, ‖∫ y : 𝔰.G₁, ⟪F y, F (y * g)⟫_ℂ ∂besselQuotMeasure‖ₑ ^ 2 =
      ENNReal.ofReal l.formalDegree⁻¹ *
        (∫⁻ y : 𝔰.G₁, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) ^ 2 := by
  have h_deg : 0 < l.formalDegree := formalDegree_pos h_gap
  -- The matrix coefficient of `F` is `c_λ` times its squared norm.
  have h_coeff (g : 𝔰.G₁) : ∫ y, ⟪F y, F (y * g)⟫_ℂ ∂besselQuotMeasure =
      l.dsCoeffInFrame g * (∫ y, ‖F y‖ ^ 2 ∂besselQuotMeasure : ℝ) := by
    have h_inner : ∫ y, ⟪F (y * 1), F (y * g)⟫_ℂ ∂besselQuotMeasure =
        l.formalDegree * l.dsCoeffInFrame (1⁻¹ * g) / l.formalDegree *
          (∫ y, ‖F y‖ ^ 2 ∂besselQuotMeasure : ℝ) :=
      hF.integral_inner_translate rfl (by simp) hF.map_unipotent_mul F_int
        (isIdempotentKernel_dsCoeffInFrame h_gap) (by simp [HCParam.dsCoeffInFrame]) F_conv 1 g
    simpa [h_deg.ne'] using h_inner
  have h_norm : ∫⁻ g : 𝔰.G₁, ‖l.dsCoeffInFrame g‖ₑ ^ 2 = .ofReal l.formalDegree⁻¹ := by
    have h_int : Integrable (l.dsCoeffInFrame : 𝔰.G₁ → ℂ) := (integrable_const_mul_iff
      (by simp [h_deg.ne']) _).1 (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
    rw [lintegral_enorm_sq h_int
      (IsBoundedMeasurable.of_continuous ⟨1, fun _ ↦ norm_dsCoeff_le_one h_gap _⟩).memLp_top,
      HCParam.formalDegree, inv_inv, ← integral_comp_frameEquiv (J := 𝔰.J₁)]
    -- `formalDegree` is the inverse of the integral of `‖dsCoeff‖ ^ 2`.
    rfl
  simp_rw [h_coeff, eNorm_mul, mul_pow, lintegral_mul_const' _ _ (pow_ne_top eNorm_ne_top)]
  rw [h_norm, lintegral_enorm_sq F_int hF.memLp_top, ← ofReal_norm,
    Complex.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]

/-- Let `F` be a Bessel function on `G₁` for the unitary representation `rep` of `U(κ)`: bounded,
measurable, and transforming on the left by a character under `besselU` and by `rep` under `U(κ)`.
Its convolution with an integrable kernel `k` on `G₁` is again a Bessel function for `rep`. -/
lemma IsBesselFunction.convolve_of_integrable
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {F : 𝔰.G₁ → EuclideanSpace ℂ I}
    (hF : IsBesselFunction rep F) {k : 𝔰.G₁ → ℂ} (k_int : Integrable k) :
    IsBesselFunction rep (convolve F k) := by
  -- Left translations commute with the convolution, and so does each scalar or linear map.
  refine ⟨hF.convolve_right k_int, fun n hn y ↦ ?_, fun h y ↦ ?_⟩
  · simp [convolve, mul_assoc, hF.map_unipotent_mul n hn, smul_comm (k _), integral_smul]
  · simp [convolve, mul_assoc, hF.map_unitary_mul, ← ContinuousLinearMap.integral_comp_comm,
      hF.integrable_smul k_int.comp_inv]

/-- **Schur's bound for a Bessel function.** Let `l = 2λ` be a doubled Harish-Chandra parameter with
gap `500 r ^ 3 + A` (`l.HasLargeGap A`) and entries bounded by `L`. Its coefficient is
`c_λ = l.dsCoeffInFrame` on `G₁`, and its formal degree is `deg = l.formalDegree`. Let `rep` be a
unitary representation on `ℂ^I` of `U(κ)`, the unitary group of the positive definite middle part.
Let `F` be a Bessel function for `rep`, integrable over `𝖴 ∖ G₁` and fixed by convolution with
`deg · c_λ`. Let `B ≥ (r + 1) ^ 4 (L + r + 1 + 2 n ^ 2)`. Then `F` has right derivatives `V w` along
the words `w` in the matrix units, which are again Bessel functions for `rep`. Take
`s = |w| ≤ 2 n ^ 2` and `φ` integrable on `G₁`. Then the function `g ↦ ∫ φ y • V w (g y)` has
squared norm at most `B ^ (2 s) ‖F‖₂ ^ 2 ‖φ‖₂ ^ 2 / deg` in `L²(𝖴 ∖ G₁)`, with `‖F‖₂` taken over
`𝖴 ∖ G₁`. -/
theorem IsBesselFunction.hasSchurBound_of_convolve_eq
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {l : HCParam ε} {A L : ℕ}
    (h_gap : l.HasLargeGap A) (hL : ∀ a : 𝔰.BesselIndex, |l a| ≤ L)
    {F : 𝔰.G₁ → EuclideanSpace ℂ I} (hF : IsBesselFunction rep F)
    (F_int : Integrable F besselQuotMeasure) (B : ℝ)
    (F_conv : convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F)
    (hB : (𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + (2 * 𝔰.n ^ 2 : ℕ)) ≤ B) :
    RealPlace.HasSchurBound F rep B
      (ENNReal.ofReal l.formalDegree⁻¹ * ∫⁻ y : 𝔰.G₁, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) := by
  let idem : 𝔰.G₁ → ℂ := fun g ↦ l.formalDegree * l.dsCoeffInFrame g
  -- The derivatives are the convolutions of `F` with the kernels `X w`.
  obtain ⟨X, (X_nil : X [] = idem), X_int, X_conv, X_norm, X_deriv⟩ :=
    exists_derivative_kernels (I := I) h_gap hL
  have F_conv_nil : convolve F (X []) = F := by rw [X_nil, F_conv]
  refine ⟨fun w ↦ ⟨convolve F (X w), hF.continuous_convolve (X_int w)⟩, F_conv_nil.symm,
    fun w ↦ ⟨?_, X_deriv F hF.toIsBoundedMeasurable F_conv_nil w, fun hw φ φ_int ↦ ?_⟩⟩
  · exact hF.convolve_of_integrable (X_int w)
  · have idem_conv : convolve idem (X w) = X w := by rw [← X_nil, X_conv]
    have norm_le : (∫ g, ‖X w g‖ ^ 2) / l.formalDegree ≤ B ^ (2 * w.length) :=
      calc (∫ g, ‖X w g‖ ^ 2) / l.formalDegree
        _ ≤ ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ (2 * w.length) := X_norm w
        _ ≤ B ^ (2 * w.length) := by grw [← hB, ← hw]
    -- Schur orthogonality bounds the integral by the norms of `X w`, `F` and `φ`.
    calc ∫⁻ g, ‖∫ y, φ y • convolve F (X w) (g * y)‖ₑ ^ 2 ∂besselQuotMeasure
      _ = ∫⁻ y, ‖convolve (convolve F (X w)) (fun a ↦ φ a⁻¹) y‖ₑ ^ 2 ∂besselQuotMeasure := by
        simp only [convolve.eq_1 (convolve F (X w)), inv_inv]
      _ ≤ .ofReal ((∫ g, ‖X w g‖ ^ 2) / l.formalDegree) *
          (.ofReal l.formalDegree⁻¹ * ∫⁻ y, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) * ∫⁻ y, ‖φ y‖ₑ ^ 2 :=
        hF.lintegral_sq_convolve_convolve_le rfl (by simp) hF.map_unipotent_mul F_int (X_int w)
          (isIdempotentKernel_dsCoeffInFrame h_gap) (by simp [HCParam.dsCoeffInFrame]) F_conv
          (isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame h_gap) idem_conv φ_int
      _ ≤ _ := by grw [norm_le]

end New
end
end

/-!
# Filling data from admissible data, with Bessel systems at the real places

The filling theorem is stated for abstract data (`New.Filling`). This file builds such data from
admissible data D (`New.Data`). At each real place it constructs a Bessel system of the type fixed
by D. It then assembles these systems, the relevant primes and places, and the level `D.levelX 0`
into the filling data. It identifies that level with the preimage of the level K(M) of
`New.Filling.principalLevel`: here M = p₀ p₁, and K(M) includes a congruence modulo π.

## Main definitions and results

* `New.Data.exists_besselSystem`: the Bessel function at a real place, with its normalisation,
  Schur's bound, decay, cut and local bounds. That its coordinates are orthonormal is
  `New.BesselSystem.orthonormal`, in `New.Spanning.Bessel.Orthonormality`.
* `New.Data.filling`: the prime `New.Data.N`, the primes p₀, p₁ (field `levelPrime`) with their
  chosen places, the level `D.levelX 0` and a Bessel system at each infinite place.
* `New.Data.levelX_zero_eq_comap`: the level `D.levelX 0` is the preimage of the principal
  congruence subgroup K(M), that is `New.Filling.principalLevel`.

Notions from other files:
* `New.Data.piNIdele`: the principal finite idele of `π`, where `N = π π̄`; `New.Data.piNPlaces` is
  the set of places dividing `π`.
* `New.Data.piM`: the conjugate of the integer `D.piMBar` of norm `p₀ p₁`; the chosen places are its
  prime divisors.

## Relation to the literature

At a real place, integrals of a Bessel function on an indefinite unitary group against its
translates have Fourier transforms decaying beyond a band; the bounds themselves are proved in the
imported files. These integrals replace Petersson's J-Bessel kernel in showing that few translates
almost span the target forms. Rank one is classical, and Bessel kernels are studied for GL(n) and
GSp(4).

Related work: Petersson, Über die Entwicklungskoeffizienten der automorphen Formen, 1932; NIST DLMF
§10.22; Baruch, On Bessel distributions for quasi-split groups, 2001, and Bessel distributions for
GL(3) over the p-adics, 2004; Comtat et al., Effective Kuznetsov trace formula for GSp(4), 2025.
-/

@[expose] public section

namespace New.Data

/-!
## Bessel systems at the real places

The Bessel function at each real place is built at a stationary point given by
`New.DiscreteSeries.IsSteep.exists_stationary_point`.
-/

section BesselSystemExists

open MeasureTheory Matrix Finset Fintype Filling RealPlace DiscreteSeries Norms.L2Operator CStarRing
  MatrixOrder ConjAct

variable {P : Parameters} (D : Data P)

lemma card_X₀ : Fintype.card (D.X 0) = D.k := by grind [card_X, n]

/-- An orthonormal frame with the signs of `Y₀`. -/
noncomputable instance unitarySignFrameY : UnitarySignFrame D.shape (D.signsY 0 ·) :=
  Nonempty.some <|
  -- For a string of length `2 ϱ + 1`, `exists_conjTranspose_mul_gradedGram_mul_eq_signMatrix` asks
  -- for `ϱ + 1` minus signs.
  have ⟨p, hp_form, hp_unitary⟩ := Seesaw.exists_conjTranspose_mul_gradedGram_mul_eq_signMatrix
    D.shape.besselIndexEquiv (.id ℂ)
    one_pos ((D.negCount_gridSigns false 0 0).trans (by grind))
  ⟨{ matrix := (.mkOfMulEqOne _ _ (hp_unitary rfl))⁻¹
     gram_eq := by
       -- The two Gram matrices agree entry by entry.
       convert! hp_form
       simp [← ext_iff, gradedGram, Shape.besselIndexEquiv, splitGram, middleGram, Fin.rev,
         Matrix.one_apply]
       lia
     mem_unitary := ⟨hp_unitary rfl, Units.inv_mul _⟩ }⟩

/-- The Schur matrices of weight `w`, written in an orthonormal basis for their Gram form, give a
continuous unitary representation of U(n), with n = `𝔰.κ`, which is conjugate to the transposed
Schur matrices of transposes and is irreducible: only scalars commute with it. If `u` is the
Harish-Chandra parameter of the weight `w`, then `dsCoeff`, the coefficient attached to `u`, is a
diagonal matrix coefficient of it, seen as operators by `besselValueRep`. -/
lemma exists_unitary_schur_rep {𝔰 : Shape} {w : Unit → ℕ → ℕ} {u : Unit → HCParam (n := 𝔰.κ) 1}
    (hu : IsHCParam w 0 u) :
    ∃ rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup (WeylIndex 𝔰.κ w) ℂ,
      -- (a) `rep` is conjugate to the transposed Schur matrices of the transposes
      (∃ C : (Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ)ˣ, ∀ h : U 1,
        C.val * (rep h).val = (schur w fun _ : Unit ↦ h.val.valᵀ)ᵀ * C.val) ∧
      -- (b) only scalars commute with `rep`
      (∀ M : Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ,
        (∀ h : U 1, Commute M (rep h).val) → M ∈ Set.range (scalar (WeylIndex 𝔰.κ w))) ∧
      -- (c) continuity
      Continuous rep ∧
      -- (d) `dsCoeff` is a diagonal matrix coefficient
      ∃ v : EuclideanSpace ℂ (WeylIndex 𝔰.κ w), ∀ k : U 1,
        inner ℂ v ((besselValueRep rep k).val v) = (u ()).dsCoeff k := by
  -- Write the positive definite Gram matrix as `star B * B` and conjugate the Schur matrices by
  -- `B`: adjointness for the Gram form becomes adjointness for the standard form.
  obtain ⟨_, ⟨B, rfl⟩, h_gram⟩ : ∃ b : Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ,
      IsUnit b ∧ weylGramOver = star b * b :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp weylGramOver_posDef.isStrictlyPositive
  let φ :=
    MulSemiringAction.toAlgEquiv ℂ (Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ) (toConjAct B)
  have hφ (A : Matrix (WeylIndex 𝔰.κ w) (WeylIndex 𝔰.κ w) ℂ) : φ A = B.val * A * B.val⁻¹ := by
    simp [φ, units_smul_def]
  have h_unitary (g : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      φ (schur w fun _ : Unit ↦ g.val.val) ∈ unitaryGroup (WeylIndex 𝔰.κ w) ℂ := by
    -- The Schur matrix of a unitary `g` keeps the Gram form.
    have h_form : (schur w fun _ : Unit ↦ g.val.val)ᴴ *
        (weylGramOver * schur w fun _ : Unit ↦ g.val.val) = weylGramOver (R := ℂ) := by
      simpa [← U.inv_val_eq_conjTranspose] using GL.schur_conjTranspose_weylGram_schur .refl
        (κ := w) (fun _ : Unit ↦ g.val.val) (fun _ : Unit ↦ g.val.val)
    rw [mem_unitaryGroup_iff', hφ]
    simpa [h_gram, star_eq_conjTranspose, conjTranspose_nonsing_inv, mul_assoc] using
      congrArg (fun A ↦ B.valᴴ⁻¹ * A * B.val⁻¹) h_form
  let rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup (WeylIndex 𝔰.κ w) ℂ :=
    .mk' (fun g ↦ ⟨φ (schur w fun _ : Unit ↦ g.val.val), h_unitary g⟩) (by simp [schur_mul_left])
  refine ⟨rep, ⟨star B, fun g ↦ ?_⟩, fun M hM ↦ ?_, ?_,
    .toLp 2 (B.val *ᵥ highestVector w u), fun k ↦ ?_⟩
  · -- `star B = weylGramOver * B⁻¹`, so this is adjointness for the Gram form.
    have h_adjoint : (weylGramOver * schur w fun _ : Unit ↦ g.val.val) =
        (schur w fun _ : Unit ↦ g.val.valᵀ)ᵀ * weylGramOver := weylGramOver_mul_schur (R := ℂ) _
    rw [h_gram] at h_adjoint
    simp [rep, hφ, ← mul_assoc, h_adjoint]
  · -- Schur's lemma for `φ.symm M`.
    obtain ⟨c, hc⟩ : φ.symm M ∈ Set.range (scalar (WeylIndex 𝔰.κ w)) :=
      mem_range_scalar_of_commute_schur fun g hg ↦ by
        simpa [rep] using! (hM (U.of isUnit_one (g ()) (by simp [hg]))).map φ.symm
    exact ⟨c, (φ.commutes c).symm.trans (φ.eq_symm_apply.mp hc)⟩
  · refine Continuous.subtype_mk ?_ h_unitary
    simp only [hφ]
    fun_prop
  · -- The coefficient at `B x`, with `x` the highest vector, is that of `x` for the Gram form: a
    -- product of principal minors of `k` in the decreasing order `p` of `u ()`, as is `dsCoeff` on
    -- this group.
    obtain ⟨p, hp⟩ := exists_equiv_decreasingPosition (hu ()).1
    set x : WeylIndex 𝔰.κ w → ℂ := highestVector w u with hx
    calc _ = star (B.val *ᵥ x) ⬝ᵥ φ (schur w fun _ : Unit ↦ k.val.val) *ᵥ B.val *ᵥ x :=
          dotProduct_comm _ _
      _ = x ⬝ᵥ weylGramOver *ᵥ (schur w fun _ : Unit ↦ k.val.val) *ᵥ x := by
          simp [hx, hφ, h_gram, star_mulVec, star_highestVector, dotProduct_mulVec, mul_assoc,
            star_eq_conjTranspose]
      _ = (u ()).dsCoeff k := by
          simpa [hx, weylRep, hp, highestVector, funext (hu.lowestKType_eq _),
            dsCoeff_of_mem_maxCompactU (hu.hasGap () 0) (k := ⟨k, _⟩) k.prop] using!
            weylRep_coeff_eq_prod_weightMinors (κ := w) (e := 0) (fun _ : Unit ↦ p) _

/-- If the parameter `D.paramW v` of the discrete series at the place `v` has entries of size at
most `3 a`, then Weyl's dimension polynomial at it is at most `b ^ (2 r ^ 2)`, where `a` and `b` are
the size parameters of D and `r` is the number of its row indices. -/
lemma weylDimensionPoly_paramW_le (v : D.Φ)
    (h_abs : ∀ i : D.RowIndex, |D.paramW v i| ≤ ↑(3 * D.a)) :
    weylDimensionPoly (D.paramW v) ≤ D.b ^ (2 * D.r ^ 2) := by
  -- Each of the at most `r ^ 2` halved differences is at most `3 a ≤ b ^ 2`, and the denominator is
  -- at least one.
  have hb : 1 ≤ D.b ^ 2 := one_le_pow₀ D.le_of_hasLogBound
  have h_factor (i j : D.RowIndex) : |(D.paramW v i - D.paramW v j : ℝ) / 2| ≤ D.b ^ 2 := by
    rify at h_abs
    grw [abs_div, abs_sub, h_abs, h_abs, abs_two, add_self_div_two]
    exact D.le_of_hasLogBound
  have h_denom : (1 : ℝ) ≤ ∏ i ∈ Finset.range (Fintype.card D.RowIndex), ↑i.factorial :=
    Finset.one_le_prod₀ fun i _ ↦ mod_cast i.factorial_pos
  calc weylDimensionPoly (D.paramW v)
      ≤ ∏ i, ∏ j with D.paramW v j < D.paramW v i, |(D.paramW v i - D.paramW v j : ℝ) / 2| := by
        grw [weylDimensionPoly, le_abs_self (∏ _, _), ← h_denom, div_one]
        simp only [abs_prod, le_refl]
    _ ≤ ∏ _ : D.RowIndex, (D.b ^ 2) ^ D.r := by
        gcongr with i
        grw [h_factor, prod_const, card_filter_le, card_univ, card_rowIndex]
    _ = D.b ^ (2 * D.r ^ 2) := by
        rw [prod_const, card_univ, card_rowIndex, ← pow_mul, ← pow_mul, ← sq]

/-- The quotient of the volumes of U(k) and U(r) is at most `(b ^ r) ^ r`, where `k` and `r` are the
rank of X₀ and the number of row indices of D, and `b` is its size parameter. -/
lemma volU_div_volU_le : volU D.k / volU D.r ≤ (D.b ^ D.r) ^ D.r := by
  -- The quotient is a product of `r - k` numbers `i! / (2 π ^ (i + 1)) ≤ b ^ r`.
  have h_factor (i : ℕ) (hi : i < D.r) : (sphereDensity (i + 1) 1)⁻¹ ≤ D.b ^ D.r := by
    calc (sphereDensity (i + 1) 1)⁻¹ = i.factorial / (2 * Real.pi ^ (i + 1)) := by
          simp [sphereDensity, div_eq_mul_inv]
      _ ≤ (D.r : ℝ) ^ D.r := by
          grw [← show 1 ≤ 2 * Real.pi ^ (i + 1) by bound [Real.two_le_pi], div_one,
            Nat.factorial_le hi.le, Nat.factorial_le_pow, Nat.cast_pow]
      _ ≤ D.b ^ D.r := pow_le_pow_left₀ D.r.cast_nonneg D.le_of_hasLogBound _
  calc volU D.k / volU D.r = ∏ i ∈ Ico D.k D.r, (sphereDensity (i + 1) 1)⁻¹ := by
        rw [volU.eq_1 D.r, ← prod_range_mul_prod_Ico _ D.k_le_r, ← volU, prod_inv_distrib,
          div_mul_cancel_left₀ (volU_pos _).ne']
    _ ≤ ∏ _ ∈ Ico D.k D.r, D.b ^ D.r := by
        gcongr with i hi
        exact h_factor i (mem_Ico.1 hi).2
    _ ≤ (D.b ^ D.r) ^ D.r := by
        grw [prod_const, Nat.card_Ico, tsub_le_self]
        exact one_le_pow₀ D.le_of_hasLogBound

/-- The constant `scaledVolumeRatio` of the local bounds for the shape of D is at most
`b ^ (2 r ^ 2)`, where `b` is the size parameter of D and `r` the number of its row indices. -/
lemma scaledVolumeRatio_le : D.shape.scaledVolumeRatio ≤ D.b ^ (2 * D.r ^ 2) := by
  have hb : 1 ≤ D.b := D.le_of_hasLogBound
  have h_pi : Real.pi ≤ D.b := D.le_of_hasLogBound
  have h_mul : (2 * D.shape.ϱ + 1) * D.k ≤ D.r ^ 2 := D.nat_le_of_hasLogBound
  grw [Shape.scaledVolumeRatio, show D.shape.k = D.k from D.card_X₀,
    show D.shape.r = D.r from D.card_rowIndex, D.volU_div_volU_le, h_pi, h_mul]
  exact le_of_eq (by ring)

/-- If every entry `D.paramW v i` has absolute value at most `3 * D.a`, then Weyl's dimension
polynomial at `D.paramW v`, times the constant `D.shape.scaledVolumeRatio` of the local bounds, is
at most `D.b ^ (4 r ^ 2)`, where `r = D.shape.r` is the rank of G₁. -/
lemma weylDimensionPoly_mul_scaledVolumeRatio_le (v : D.Φ)
    (h_abs : ∀ i : D.RowIndex, |D.paramW v i| ≤ ↑(3 * D.a)) :
    weylDimensionPoly (D.paramW v) * D.shape.scaledVolumeRatio ≤ D.b ^ (4 * D.shape.r ^ 2) := by
  have h_nonneg : 0 ≤ D.shape.scaledVolumeRatio :=
    mul_nonneg (div_pos (volU_pos _) (volU_pos _)).le (by positivity)
  grw [D.weylDimensionPoly_paramW_le v h_abs, D.scaledVolumeRatio_le,
    show D.shape.r = D.r from D.card_rowIndex, ← pow_add]
  exact le_of_eq (by ring)

/-- The entries of `D.paramW v`, twice the Harish-Chandra parameter at the place `v` of the discrete
series on G₁, have absolute value at most `3 a`, where `a = D.a` is a size parameter of D. -/
lemma abs_paramW_le (v : D.Φ) (i : D.RowIndex) : |D.paramW v i| ≤ ↑(3 * D.a) :=
  (D.abs_gridParam_le (z := false) v bot_le bot_le i).trans (mod_cast D.nat_le_of_hasLogBound)

/-- Let `u ()`, indexed by the basis `D.shape.κ` of X₀, list twice the Harish-Chandra parameter of
the weight on the compact group U(X₀) that has `D.columnCount v h` columns of height `h` for each
`h` below the rank. Then the highest weight `lowestKType` attached to `u ()` is `D.columnCount v 1`
at one index `i` and `0` at the others, and the entries of `u ()` have absolute value at most
`3 * D.a`. Here the natural number `D.a` is a size parameter of the data D, the product
`D.natX * D.natB`. -/
lemma exists_lowestKType_eq_ite (v : D.Φ) {u : Unit → D.shape.κ → ℤ}
    (hu : IsHCParam (fun _ : Unit ↦ D.columnCount v) 0 u) :
    ∃ i : D.shape.κ,
      (∀ j : D.shape.κ, (toHCParam 1 (u ())).lowestKType j =
        ↑(if j = i then D.columnCount v 1 else 0 : ℕ)) ∧
      ∀ j : D.shape.κ, |u () j| ≤ ↑(3 * D.a) := by
  have h_card : card D.shape.κ = D.k := D.card_X₀
  -- The index `i` is the one at which `u` is largest.
  obtain ⟨i, hi⟩ := hu.exists_decreasingPosition_eq () card_pos
  have hk : D.k ≤ D.a := D.nat_le_of_hasLogBound
  -- Of the heights above `p` and below `k`, only height 1 has columns; so the sum vanishes
  -- unless `p = 0`.
  have h_column (p : ℕ) :
      ∑ q ∈ Ioo p (card D.shape.κ), D.columnCount v q = if p = 0 then D.columnCount v 1 else 0 := by
    rw [sum_eq_ite 1] <;> grind [columnCount]
  refine ⟨i, fun j ↦ ?_, fun j ↦ ?_⟩
  · have h_position : decreasingPosition (u ()) j = 0 ↔ j = i := by
      grind [(hu ()).1, hu.eq_hcParameter () j]
    rw [hu.lowestKType_eq, diagramWeight_apply, rankAt, h_column]
    simp [h_position]
  · -- The entry at `j` is the Harish-Chandra value at the position of `j`.
    rw [hu.eq_hcParameter () j, hcParameter, diagramWeight_apply, h_column, Pi.zero_apply]
    grind [columnCount, decreasingPosition]

/-- The size inequalities `Floors.RealPlaceSizes`, under which cut Bessel functions have local
bounds, hold for `D.shape` with box radius `b ^ (6 n + 2)`, exponent `k - (3 n + 6)` and base
`b = D.b`. Here `D.shape` describes the hermitian space Y₀, the sum of some hyperbolic planes, a
space X₀ and a line; `n = D.shape.n` is the number of planes plus one and `k = D.shape.k` is the
rank of X₀. -/
lemma realPlaceSizes : Floors.RealPlaceSizes D.shape (D.b ^ (6 * D.shape.n + 2))
    (D.shape.k - (3 * D.shape.n + 6)) D.b := by
  have h_card : D.shape.k = D.k := D.card_X₀
  have h_room : 10 ^ 9 * D.shape.n ^ 3 + (3 * D.shape.n + 6) < D.shape.k :=
    h_card.ge.trans_lt' D.nat_lt_of_hasLogBound
  exact {
    rho_eq := rfl, k_eq := by omega, mul_cube_lt_s := by omega
    eight_mul_r_le_rho := D.le_of_hasLogBound.trans (le_self_pow₀ D.le_of_hasLogBound nofun)
    pow_seven_le_k := h_card.ge.trans' D.nat_le_of_hasLogBound
    ten_pow_le_varrho := D.nat_le_of_hasLogBound
    two_le_b := D.le_of_hasLogBound }

/-- An inequality of exponents of `b = D.b`, where `r` and `k` are the ranks of G₁ and U(X₀): the
loss `3 * (20 * (r + k) ^ 2)` in the lower bound for the period and the further `99 r ^ 2` allowed
for cutting the Bessel function add up to at most `400 r ^ 2`. -/
lemma exponent_add_le_mul_sq_r :
    3 * (20 * (D.shape.r + D.shape.k) ^ 2) + 99 * D.shape.r ^ 2 ≤ 400 * D.shape.r ^ 2 := by
  have hk : D.shape.k ≤ D.shape.r := D.card_X₀.trans_le (D.k_le_r.trans D.card_rowIndex.ge)
  nlinarith

/-- At an infinite place `v`, three times `D.liftWeight 0 v`, which is the weight of the character
of the lift of index `0` (the first one), plus the number `D.columnCount v 1` of columns of height 1
in the weight on X₀ is at most `b ^ 2`, where `b = D.b` is the size parameter of D. -/
lemma liftWeight_add_columnCount_le (v : D.Φ) :
    3 * (D.liftWeight 0 v : ℝ) + D.columnCount v 1 ≤ D.b ^ 2 := by
  have h_count : D.columnCount v 1 ≤ D.a := by grind [columnCount]
  grw [h_count]
  exact D.le_of_hasLogBound

/-- The ranks `r` of G₁ and `k` of U(X₀) and the bound `3 a` on the entries of the parameters
`D.paramW v` add up to at most `b ^ 3`, where `a` and `b` are the size parameters of D. -/
lemma rank_add_le_cube : D.shape.r + D.shape.k + (3 * D.a : ℕ) ≤ D.b ^ 3 := by
  have h_card : D.shape.k = D.k := D.card_X₀
  rw [h_card]
  exact D.le_of_hasLogBound

/-- For the ranks `r` of G₁ and `k` of U(X₀) and the size parameter `b` of D, the number `r ^ 7`,
which bounds from below the gaps of the Harish-Chandra parameters at the real places, is at least
`10 ^ 30` times the cube of `(r + k) ^ 2 log (b ^ 3)`. -/
lemma rank_sq_mul_log_le :
    10 ^ 30 * ((D.shape.r + D.shape.k) ^ 2 * (D.b ^ 3).log) ^ 3 ≤ (D.r ^ 7 : ℕ) := by
  have h_card : D.shape.k = D.k := D.card_X₀
  rw [h_card]
  exact D.le_of_hasLogBound

/-- Let `l` be a parameter of large gap, with coefficient `c_l` on G₁ and formal degree `deg`. If a
Bessel function `F` is fixed by convolution with `deg * c_l`, then each coordinate of `F` is fixed
by right convolution with the kernel `l.dsKernel`, carried over from `USign ε` by the frame. -/
lemma _root_.New.IsBesselFunction.integral_dsKernel_mul_eq_of_convolve_eq {𝔰 : Shape}
    {ε : 𝔰.BesselIndex → ℤˣ} [SignFrame 𝔰.J₁ ε] [IsHermitianInvolution 𝔰.J₁] {I : Type}
    [Fintype I] [DecidableEq I] {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {F : 𝔰.G₁ → EuclideanSpace ℂ I} (hF : IsBesselFunction rep F) {l : HCParam ε} {A : ℕ}
    (h_gap : l.HasLargeGap A)
    (hF_fix : convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F)
    (y : 𝔰.G₁) (j : I) :
    ∫ g : USign ε, l.dsKernel g * F (y * frameEquiv.symm g) j = F y j := by
  have h_ker : IsIdempotentKernel fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g :=
    isIdempotentKernel_dsCoeffInFrame h_gap
  have h_inv (g : 𝔰.G₁) :
      l.formalDegree * l.dsCoeffInFrame g⁻¹ = l.dsKernel (frameEquiv g) :=
    (h_ker.apply_inv g).trans (by simp [HCParam.dsKernel, HCParam.dsCoeffInFrame])
  calc ∫ g : USign ε, l.dsKernel g * F (y * frameEquiv.symm g) j
      = ∫ g : 𝔰.G₁, ((l.formalDegree * l.dsCoeffInFrame g⁻¹) • F (y * g)) j := by
        simp [← integral_comp_frameEquiv (J := 𝔰.J₁), h_inv]
    _ = convolve F (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) y j :=
        (eval_integral_piLp (hF.integrable_smul h_ker.integrable.comp_inv y).eval_piLp j).symm
    _ = F y j := by rw [hF_fix]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- **Bessel functions at a real place**: for each infinite place `v : D.Φ` of the field of `D`
there is a Bessel system `B : BesselSystem D.shape D.b D.f`. Such a system is a full Bessel function
on the group G₁, the unitary group of the hermitian form of the shape `D.shape`, together with a cut
version of bounded support, and the two satisfy the bounds listed in `BesselSystem`. It is built for
the shape `D.shape` of the hermitian space Y₀ of `D`, with size parameter `D.b`, and the number
`D.f` of infinite places sets the rate of decay. Its type (`IsDiscreteSeriesBessel`) is
`(D.paramW v, D.columnCount v)`: the doubled parameter of the discrete series whose Bessel function
is the full function, and the numbers of columns of each height in the weight of the representation
on the values. -/
lemma exists_besselSystem (v : D.Φ) :
    ∃ B : BesselSystem D.shape D.b D.f, IsDiscreteSeriesBessel B (D.paramW v)
      (D.columnCount v) := by
  -- `F` is the normalised Bessel average `besselAverage` at a stationary point `x`; it is fixed by
  -- the kernel of the parameter `l`, and the second function of the system is its cut. The L² norm
  -- of `F` and the volume of balls give the local bounds of the cut.
  have : IsHermitianInvolution D.shape.J₁ := isHermitianInvolution_J₁
  -- The parameter `l` on `G₁`, in the frame of signs `ε`: size, gap and formal degree.
  let ε : D.shape.BesselIndex → ℤˣ := (D.signsY 0 ·)
  let frame : SignFrame D.shape.J₁ ε := D.unitarySignFrameY.toSignFrame
  let l : HCParam ε := toHCParam ε (D.paramW v)
  have h_abs : ∀ i : D.RowIndex, |D.paramW v i| ≤ ↑(3 * D.a) := D.abs_paramW_le v
  have h_gap : l.HasLargeGap (D.r ^ 7) := (D.hasGap_signsY_paramW v).mono D.nat_le_of_hasLogBound
  have h_deg_pos : 0 < l.formalDegree := formalDegree_pos h_gap
  have h_deg : l.formalDegree = weylDimensionPoly (D.paramW v) :=
    (Orbital.harish_chandra_degree_and_orbital (h_gap.mono D.nat_le_of_hasLogBound)).1
  -- The representation on the values, with a unit vector `e` at which its coefficient is `dsCoeff`.
  obtain ⟨u, hu⟩ : ∃ u : Unit → D.shape.κ → ℤ, IsHCParam (fun _ : Unit ↦ D.columnCount v) 0 u :=
    ⟨_, isHCParam_hcParameter D.shape.κ _ 0⟩
  obtain ⟨rep, ⟨C, hC⟩, h_irred, h_cont, e, h_coef⟩ := exists_unitary_schur_rep hu
  have he : ‖e‖ = 1 := by
    have h_sq : ‖e‖ ^ 2 = 1 := by simpa using congrArg norm (h_coef 1)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) two_ne_zero).1 h_sq
  -- A point `x` of length at most `b ^ (5 n)` where the volume of the unit ball is bounded by the
  -- L² norm of the average.
  obtain ⟨x, hx, h_volume⟩ : ∃ x : D.shape.G₁, besselLength x ≤ D.b ^ (5 * D.shape.n) ∧
      besselBallVolume (ε := ε) x ≤
        .ofReal (D.b ^ (3 * (20 * (D.shape.r + D.shape.k) ^ 2))) * (.ofReal l.formalDegree *
          ∫⁻ y : D.shape.G₁, ‖besselAverage l rep x e y‖ₑ ^ 2 ∂besselQuotMeasure) := by
    obtain ⟨i, h_weight, h_abs_u⟩ := D.exists_lowestKType_eq_ite v hu
    obtain ⟨numbering, h_steep⟩ := D.exists_isSteep false
    have hu_gap : (toHCParam 1 (u ())).HasLargeGap (D.r ^ 7) := hu.hasGap () _
    -- At the stationary point the period is large.
    obtain ⟨x, hx, h_period⟩ := (h_steep v).exists_stationary_point (.swap (.inr ()) i)
      (ha := by simpa using h_weight) (hB := D.le_of_hasLogBound)
      (hb := D.liftWeight_add_columnCount_le v) (hb_rank := D.le_of_hasLogBound) (hl := h_gap)
      (hu := hu_gap) (hL := h_abs) (hK := h_abs_u) (hβ := D.le_of_hasLogBound)
      (h_rank := D.rank_add_le_cube) (h_excess := D.rank_sq_mul_log_le)
    refine ⟨x, hx, ?_⟩
    rw [pow_mul]
    exact besselBallVolume_le_of_period x h_cont h_gap (by positivity) h_coef h_period
  -- The normalised average `F` is fixed by the kernel and forms a cut pair with its cut.
  let I : Type := WeylIndex D.shape.κ fun _ : Unit ↦ D.columnCount v
  obtain ⟨c, F, hF_eq, hF_fix, h_tail⟩ : ∃ (c : ℝ) (F : C(D.shape.G₁, EuclideanSpace ℂ I)),
      (∀ y : D.shape.G₁, F y = c • besselAverage l rep x e y) ∧
      convolve F (fun g : D.shape.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) = F ∧
      IsCutPair D.b D.f rep (FullOrCut.select F (besselCut D.b F)) :=
    exists_isCutPair_besselAverage h_gap h_abs D.f h_cont he h_volume hx
      (hb_large := D.le_of_hasLogBound) (hr := D.nat_le_of_hasLogBound)
      (hm := D.exponent_add_le_mul_sq_r) (hL_le := D.le_of_hasLogBound)
      (hf := D.nat_le_of_hasLogBound)
  have hF : IsBesselFunction rep F := h_tail.isBesselFunction .full
  have hF_norm : ∫⁻ y : D.shape.G₁, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure = card I :=
    h_tail.lintegral_sq_full_eq
  have h_schur (P : ℝ) (hP : D.b ^ 5 ≤ P) :
      HasSchurBound F rep P (.ofReal l.formalDegree⁻¹ * card I) := by
    rw [← hF_norm]
    exact hF.hasSchurBound_of_convolve_eq h_gap h_abs h_tail.integrable P hF_fix
      (D.le_of_hasLogBound.trans hP)
  have h_const : l.formalDegree * D.shape.scaledVolumeRatio ≤ D.b ^ (4 * D.shape.r ^ 2) := by
    grw [h_deg, D.weylDimensionPoly_mul_scaledVolumeRatio_le v h_abs]
  -- The local bounds use the norm of the matrix coefficient of `F` and the volume of balls.
  obtain ⟨J, h_band⟩ : ∃ J : ℕ → (ℕ → ℂˣ) → (ℕ → ℂˣ) → ℂ,
      HasLocalBounds D.b (besselCut D.b F) l.formalDegree J := by
    have h_coeff : ∫⁻ g : D.shape.G₁, ‖Floors.quotientPairing F F g‖ₑ ^ 2 =
        .ofReal l.formalDegree⁻¹ * card I ^ 2 := by
      rw [← hF_norm]
      exact hF.lintegral_enorm_sq_integral_inner_translate h_gap h_tail.integrable hF_fix
    exact Floors.exists_hasLocalBounds_of_isCutBessel ⟨h_tail, D.realPlaceSizes, h_irred⟩ h_deg_pos
      h_coeff.le h_const (fun _ ↦ formalDegree_mul_volume_ball_le h_gap h_abs D.le_of_hasLogBound
        D.le_of_hasLogBound) D.nat_le_of_hasLogBound
  refine ⟨{
      Index := I, besselFn := FullOrCut.select F (besselCut D.b F),
      deg := l.formalDegree, deg_pos := h_deg_pos, rep := rep, isCutPair := h_tail,
      irreducible := h_irred, hasSchurBound := h_schur, eight_mul_rank_le := D.le_of_hasLogBound,
      bandLimit := J, hasLocalBounds := h_band }, {
      deg_eq := h_deg, exists_conj_rep_eq_schur := ⟨C.val, C⁻¹.val, C.mul_inv, C.inv_mul, hC⟩,
      exists_eq_besselAverage :=
        ⟨c, x, e, fun y ↦ ⟨integrable_besselIntegrand x h_cont he h_gap y, hF_eq y⟩⟩,
      integral_dsKernel_mul := hF.integral_dsKernel_mul_eq_of_convolve_eq h_gap hF_fix }⟩

end BesselSystemExists

section FillingData

open Real Parameters Nat

variable {P : Parameters} (D : Data P)

/-- The prime `D.levelPrime i` divides an integral finite adele `r` (an element of `Ô D.E`) iff the
component of `r` has valuation less than 1 at each chosen place `w` above that prime (the type
`D.ChosenPlace i`) and at the conjugate place `star w`. -/
lemma natCast_levelPrime_dvd_iff (i : Fin 2) (r : Ô D.E) :
    ↑(D.levelPrime i) ∣ r ↔
      ∀ w : D.ChosenPlace i, Valued.v (r.val w) < 1 ∧ Valued.v (r.val (star w.val)) < 1 := by
  -- As the prime is unramified, it divides `r` iff `r` vanishes modulo every place above it.
  have h_red : ↑(D.levelPrime i) ∣ r ↔ ∀ w : FinPlace D.E,
    ↑(D.levelPrime i) ∈ w.asIdeal → Valued.v (r.val w) < 1 := by
    simpa using dvd_iff_reduceAt_eq_zero
      (intValuation_natCast_eq_exp_neg_one ·
        (not_dvd_q₁_mul_d_of_modEq_one (D.levelPrime_modEq_one i))) r
  refine h_red.trans ⟨fun h_vanish ⟨w, _, hw⟩ ↦ ⟨h_vanish w hw, h_vanish (star w) (by simpa)⟩,
    fun h_pairs w hw ↦ ?_⟩
  -- A place above the prime is chosen or is the conjugate of a chosen place.
  by_cases h_chosen : D.IsChosen w
  · exact (h_pairs ⟨w, h_chosen, hw⟩).1
  · have h_conj := (h_pairs ⟨star w, (isChosen_star_iff hw).2 h_chosen, by simpa⟩).2
    rwa [star_star] at h_conj

instance : D.HasLogLower (ofNat(2) ^ D.ϱ) (10 * D.logB) where
  out := by
    -- Take logarithms and replace log 2 by a rational lower bound, which `D.le_of_hasLogBound` can
    -- compare.
    suffices h : 10 * D.logB ≤ D.ϱ * Real.log 2 by simpa [← le_log_iff_exp_le] using h
    grw [← log_two_gt_d9]
    norm_num
    exact D.le_of_hasLogBound

/-- The filling data `New.Filling` attached to the admissible data D. They record the prime N, the
idele of π (in the field `piN`), the primes p₀, p₁ with chosen places, `deltaE`, and Bessel systems
chosen from `New.Data.exists_besselSystem`. The type of the chosen systems is stated in
`New.Data.isDiscreteSeriesBessel_filling_besselSystem`. -/
noncomputable def filling : Filling D.E D.shape where
  N := D.N
  levelPrime := D.levelPrime
  piN := D.piNIdele
  deltaE := P.deltaE D.towerExp
  b := D.b
  chosenPlaces i := {w | D.piM ∈ w.asIdeal ∧ ↑(D.levelPrime i) ∈ w.asIdeal}
  fintypeChosen i := inferInstanceAs (Fintype (D.ChosenPlace i))
  sourceLevel := D.levelX 0
  classAut_eq_bot := D.classAut_levelX_zero_eq_bot
  besselSystem v := (D.exists_besselSystem v).choose
  piN_mul_star := mod_cast D.isSplitSquarefree_piNIdele.algebraMap_eq_mul_star.symm
  N_prime := D.N_prime
  N_split w := by
    by_cases hw : w ∈ D.piNPlaces
    · refine .inr ⟨D.isSplitLevel_piNPlaces.q_eq w hw, ?_⟩
      rw [D.isSplitSquarefree_piNIdele.v_apply,
        ite_eq_right (D.isSplitSquarefree_piNIdele.star_notMem w hw)]
    · exact .inl (by rw [D.isSplitSquarefree_piNIdele.v_apply, ite_eq_right hw])
  piN_mem := coe_mem_Ô D.piN
  levelPrime_prime_and_ne i := ⟨D.levelPrime_prime i, D.nat_lt_of_hasLogBound.ne⟩
  le_levelPrime i := (D.levelPrime_mem i).1
  levelPrime_le i := (D.levelPrime_mem i).2
  chosenPlaces_q i w hw := D.q_eq_levelPrime hw.2
  chosenPlaces_injective := D.isConjApart_chosenPlace.injective
  star_notMem_chosenPlaces hw hw' := IsChosen.not_star hw.1 hw'.1
  M_dvd_iff r := by
    -- The primes `D.levelPrime 0` and `D.levelPrime 1` are distinct, so their product divides `r`
    -- iff both do.
    have h_prod : ↑(D.levelPrime 0 * D.levelPrime 1) ∣ r ↔ ∀ i : Fin 2, ↑(D.levelPrime i) ∣ r := by
      have h_cop : (D.levelPrime 0).Coprime (D.levelPrime 1) := by grind [coprime_primes, Data]
      simpa using ⟨fun h ↦ ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩,
        fun ⟨h₀, h₁⟩ ↦ h_cop.cast.mul_dvd h₀ h₁⟩
    rw [h_prod, Sigma.forall]
    exact forall_congr' fun i ↦ (D.natCast_levelPrime_dvd_iff i r).trans
      (forall_congr' fun w ↦ by simp)
  card_chosenPlaces := D.card_chosenPlace
  star_deltaE := P.star_deltaE
  span_deltaE := P.differentIdeal_eq_span_deltaE
  -- Each size inequality is compared on the logarithmic scale; `D.card_X₀` identifies the rank.
  ten_pow_five_le_varrho := D.nat_le_of_hasLogBound
  half_pow_le_inv_pow_six := by
                 rify [inv_pow]
                 exact D.le_of_hasLogBound
  mul_finrank_le_pow := by
             rify [finrank_eq_two_mul_card_infinitePlace, pow_mul']
             exact D.le_of_hasLogBound
  pow_le_k := D.nat_le_of_hasLogBound.trans D.card_X₀.ge
  k_le_f := D.card_X₀.trans_le D.nat_le_of_hasLogBound
  mul_rootDiscr_pow_le := by
                 rify [Shape.k, card_X₀]
                 exact D.le_of_hasLogBound
  numInfPlaces_le_div := D.le_of_hasLogBound
  k_le_b := (Nat.cast_le.2 D.card_X₀.le).trans D.le_of_hasLogBound
  rootDiscr_le_b := D.le_of_hasLogBound
  succ_le_b := D.le_of_hasLogBound
  thousand_le_b := D.le_of_hasLogBound
  one_le_b := D.le_of_hasLogBound
  M_le_b_pow := D.le_of_hasLogBound
  le_M := D.le_of_hasLogBound
  five_le_N := D.le_of_hasLogBound

/-- The Bessel system of `D.filling` at the infinite place `v` has type
`(D.paramW v, D.columnCount v)`: its full function is the Bessel function of the discrete series of
parameter `D.paramW v`, with values in the representation of U(X₀) of weight `D.columnCount v`. -/
lemma isDiscreteSeriesBessel_filling_besselSystem (v : D.Φ) :
    Filling.IsDiscreteSeriesBessel (D.filling.besselSystem v) (D.paramW v) (D.columnCount v) :=
  (D.exists_besselSystem v).choose_spec

/-- The level of index `0`, `D.levelX 0`, is a level on the first hermitian space X₀ of the sequence
X_j of D. It is the preimage, under the embedding `inclHFin` of the finite adelic points of U(X₀) in
those of U(Y₀), of `New.Filling.principalLevel`, the level K(M) of the elements that satisfy the
congruence modulo π and reduce to 1 at the chosen places. -/
lemma levelX_zero_eq_comap :
    D.levelX 0 = D.filling.principalLevel.comap D.filling.inclHFin := by
  -- Both sides say that `k` satisfies the congruence modulo `piN` and reduces to `1` at the chosen
  -- places; the left side also asks for `k ∈ stdLevel` (integrality), which the congruence
  -- contains.
  ext k
  -- The chosen places stay subtypes (`-Subtype.forall`), as the lemma on reductions is stated.
  simp [levelX, Filling.principalLevel, levelOf, Subgroup.mem_comap, funext_iff, Sigma.forall,
    D.filling.reduction_inclHFin_eq_one_iff, D.filling.inclHFin_mem_latticeStabilizer_iff,
      -Subtype.forall]
  exact ⟨fun ⟨⟨_, h_red⟩, h_cong⟩ ↦ ⟨h_cong, h_red⟩,
    fun ⟨h_cong, h_red⟩ ↦ ⟨⟨h_cong.1, h_red⟩, h_cong⟩⟩

end FillingData

end New.Data
end
end

section
/-!
# Masses of spheres and of frames

For the data `D` and an infinite place `v`, the file defines the mass `sph_l` of the unit sphere of
`ℂ ^ l` and the product `fr_v = N ^ k sph_{k+1} ⋯ sph_r`. By the approximate formula for the ratio
of masses in consecutive ranks, the product of the `fr_v` over the infinite places is at most
`N ^ (k f) mass_k / mass_r` up to a factor close to one, where `f` is the number of infinite places
and `mass_l` is the mass `New.mass` in rank `l`.

## Main definitions and results

* `New.Data.unitSphereMass`, `New.Data.frameMass`: the numbers `sph_l` and `fr_v`.
* `New.Data.prod_frameMass_mul_le`: the upper bound for the product of the `fr_v`.
* `New.Data.prod_frameMass_mul_openCellConst_eq`: the product of the `fr_v` in terms of the
  constants `New.Filling.siegelConst` and `New.Shape.openCellConst`.

Notions from other files:
* `New.Data`: the data: a CM field `E` with `f` infinite places (the type `D.Φ`) and root
  discriminant `rd = D.rootDisc`, a generator `P.deltaE D.towerExp` of its different, a prime level
  `N`, a weight `b`, the length `x` of the prime sum, and ranks `r = k + 2 ϱ + 1`.
* `New.Data.shape`: the shape of the hermitian space `Y₀` of rank `r`, which is the sum of `ϱ`
  hyperbolic planes, a space `X₀` of rank `k` and a line.
* `New.mass E l`: the mass of the genus of the standard hermitian lattice `O_E ^ l`.
* `New.Filling.siegelConst`: `c_S = (π ^ k / ((k - 1)! N ^ k)) ^ f |disc E| ^ (1/4) vol(Ô) ^ k`.
* `New.Shape.openCellConst`: `c_G = vol U(k) (2 π ^ k / (k - 1)!) / vol U(r)`.
* `New.volÔ E`: the volume `vol(Ô) = (2 / rd) ^ f` of the integral finite adeles.
-/

@[expose] public section

noncomputable section

namespace New.Data

open Finset Real Filling Shape NumberField

variable {P : Parameters} (D : Data P)

/-- For the prime level `N` and the rank `k ≥ 1` of the data, the logarithm of `N ^ k / (N ^ k - 1)`
is at most `2 / N`. -/
lemma log_pow_div_pow_sub_one_le : log (D.N ^ D.k / (D.N ^ D.k - 1)) ≤ (2 / D.N : ℝ) := by
  have two_le_N : 2 ≤ D.N := D.N_prime.two_le
  have N_le_pow : D.N ≤ D.N ^ D.k := Nat.le_self_pow D.k_pos.ne' D.N
  have pow_sub_one_pos : (0 : ℝ) < D.N ^ D.k - 1 :=
    sub_pos.mpr (one_lt_pow₀ (mod_cast D.N_prime.one_lt) D.k_pos.ne')
  calc _ ≤ (D.N ^ D.k : ℝ) / (D.N ^ D.k - 1) - 1 := log_le_sub_one_of_pos (by positivity)
    _ = 1 / (D.N ^ D.k - 1) := by field
    _ ≤ 2 / D.N := by
      field_simp
      norm_cast
      lia

/-- The `r - k` errors `2 / 2 ^ ϱ` of the mass formula in the ranks between `k` and `r` add up to at
most `log (1 + b⁻⁹) - 2 f · 2/N`. -/
lemma sum_two_div_two_pow_le_log_sub :
    ∑ _i ∈ Ico D.k D.r, (2 / 2 ^ D.ϱ : ℝ) ≤ log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := by
  have h_error_budget : (D.r - D.k) * (2 / 2 ^ D.ϱ) + 2 * (D.f * (2 / D.N)) ≤
      2 * D.b⁻¹ ^ 9 / (D.b⁻¹ ^ 9 + 2) := D.le_of_hasLogBound
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub D.k_le_r]
  linarith [le_log_one_add_of_nonneg (x := D.b⁻¹ ^ 9) (by positivity)]

/-- The main term of `log (mass_{i+1} / mass_i)`, with `mass_l` the mass of the genus of `O_E ^ l`,
is `f ((i + 1/2) log rd + log i! - (i + 1) log 2π)`, with `rd` the root discriminant and `f` the
number of infinite places of `E`. The sum over `k ≤ i < r` of the differences between logarithm and
main term has absolute value at most `log (1 + b⁻⁹) - 2 f · 2/N`. -/
lemma abs_sum_log_mass_ratio_sub_le :
    |∑ i ∈ Ico D.k D.r, (log (mass D.E (i + 1)) - log (mass D.E i) -
      D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π)))| ≤
      log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := by
  refine (abs_sum_le_sum_abs _ _).trans <|
    (sum_le_sum fun i hi ↦ abs_log_mass_ratio_sub_le D.E i D.ϱ D.nat_le_of_hasLogBound
      (le_trans D.nat_le_of_hasLogBound (mem_Ico.mp hi).1)).trans
      D.sum_two_div_two_pow_le_log_sub

/-- At every infinite place `v`, the generator `ϖ` of the different of `E` has `2 ≤ |ϖ|_v ≤ b`,
where `b` is the weight of the data. -/
lemma apply_deltaE_mem_Icc (v : D.Φ) : v (P.deltaE D.towerExp).val ∈ Set.Icc 2 D.b :=
  ⟨D.le_of_hasLogBound, D.le_of_hasLogBound⟩

/-- The number `sph_l = (2π) ^ l / (|ϖ|_v ^ (l - 1 / 2) (l - 1)!)` at the infinite place `v`, where
`ϖ` generates the different of `E`. For `l ≥ 1` it is the mass of the unit sphere of `ℂ ^ l` for
the fibre measure `dy / d⟨y, y⟩`, when `ℂ` carries `2 / |ϖ|_v` and `ℝ` carries `|ϖ|_v ^ (-1 / 2)`
times Lebesgue measure. -/
def unitSphereMass (l : ℕ) (v : D.Φ) : ℝ :=
  (2 * π) ^ l / (v (P.deltaE D.towerExp).val ^ (l - 1 / 2 : ℝ) * (l - 1).factorial)

/-- The number `fr_v = N ^ k sph_{k+1} ⋯ sph_r` at the infinite place `v`, where `N` is the level,
`k ≤ r` are the ranks of the data and `sph_l` is `New.Data.unitSphereMass`. -/
def frameMass (v : D.Φ) : ℝ :=
  D.N ^ D.k * ∏ i ∈ Ico D.k D.r, D.unitSphereMass (i + 1) v

lemma unitSphereMass_pos (l : ℕ) (v : D.Φ) : 0 < D.unitSphereMass l v := by
  have hϖ : 0 < v (P.deltaE D.towerExp).val := InfinitePlace.pos_iff.mpr D.filling.deltaE_ne_zero
  unfold unitSphereMass
  positivity

lemma frameMass_pos (v : D.Φ) : 0 < D.frameMass v :=
  mul_pos (pow_pos (mod_cast D.N_prime.pos) _) (prod_pos fun _ _ ↦ D.unitSphereMass_pos _ v)

/-- The rank `r` of the data equals `k + (2 ϱ + 1)`, where `k` is the smaller rank of the data and
`ϱ` the number of hyperbolic planes. -/
lemma r_eq_k_add_two_mul_varrho_add_one : D.r = D.k + (2 * D.ϱ + 1) := by
  linarith only [D.r_add_one, D.m_eq_two_mul_varrho_add_two]

/-- For the ranks `k ≤ r` of the data there are `2 ϱ + 1` integers `i` with `k ≤ i < r`, where `ϱ`
is the number of hyperbolic planes. -/
lemma cast_card_Ico_k_r : ((Ico D.k D.r).card : ℝ) = 2 * D.ϱ + 1 := by
  simp [D.r_eq_k_add_two_mul_varrho_add_one]

/-- The logarithm of the product of the sphere masses `sph_{i+1}` over the `f` infinite places is
`-f ((i + 1/2) log rd + log i! - (i + 1) log 2π)`, with `rd` the root discriminant of `E`. -/
lemma log_prod_unitSphereMass (i : ℕ) :
    log (∏ v : D.Φ, D.unitSphereMass (i + 1) v) =
      -(D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π))) := by
  have rd_pos : 0 < D.rootDisc := rootDiscr_pos D.E
  simp only [unitSphereMass, prod_div_distrib, prod_mul_distrib, prod_const, card_univ,
    Nat.add_sub_cancel]
  rw [Real.finsetProd_rpow _ _ fun v _ ↦ apply_nonneg v _, P.prod_deltaE_eq_rootDiscr_pow]
  simp (disch := positivity) only [log_div, log_mul, log_rpow, log_pow, Nat.cast_add, Nat.cast_one]
  ring

/-- The product of the sphere masses `sph_{i+1}` over the infinite places is `mass_i / mass_{i+1}`
up to a factor close to one: the logarithms differ by at most `2 / 2 ^ ϱ` for `i ≥ k`. -/
lemma abs_log_prod_unitSphereMass_sub_le {i : ℕ} (hi : D.k ≤ i) :
    |log (∏ v : D.Φ, D.unitSphereMass (i + 1) v) - (log (mass D.E i) - log (mass D.E (i + 1)))| ≤
      2 / 2 ^ D.ϱ := by
  have h_places : 8 * D.f ≤ 2 ^ D.ϱ := D.nat_le_of_hasLogBound
  have h_rank : 4 * D.ϱ + 12 ≤ D.k := D.nat_le_of_hasLogBound
  rw [log_prod_unitSphereMass, ← neg_sub (log (mass D.E (i + 1))), neg_sub_neg]
  exact abs_log_mass_ratio_sub_le D.E i D.ϱ h_places (h_rank.trans hi)

lemma prod_unitSphereMass_pos (l : ℕ) : 0 < ∏ v : D.Φ, D.unitSphereMass l v :=
  prod_pos fun v _ ↦ D.unitSphereMass_pos l v

/-- The product of the sphere masses `sph_{k+1}, …, sph_r` over all infinite places is positive. -/
lemma prod_prod_unitSphereMass_pos :
    0 < ∏ i ∈ Ico D.k D.r, ∏ v : D.Φ, D.unitSphereMass (i + 1) v :=
  prod_pos fun i _ ↦ D.prod_unitSphereMass_pos (i + 1)

/-- The product of `fr_v = D.frameMass v = N ^ k sph_{k+1} ⋯ sph_r` over the `f = D.f` infinite
places `v` in `D.Φ` equals `(N ^ k) ^ f` times the product, over `k ≤ i < r`, of the products of
`sph_{i+1}` over the infinite places. -/
lemma prod_frameMass_eq_mul_prod :
    ∏ v : D.Φ, D.frameMass v =
      (D.N ^ D.k) ^ D.f * ∏ i ∈ Ico D.k D.r, ∏ v : D.Φ, D.unitSphereMass (i + 1) v := by
  simp only [frameMass, prod_mul_distrib, prod_const, card_univ]
  rw [prod_comm]

/-- The product of the `fr_v = N ^ k sph_{k+1} ⋯ sph_r` over the `f` infinite places is at most
`(1 + b⁻⁹) (1 - N ^ (-k)) ^ (2 f) N ^ (k f) mass_k / mass_r`. The statement has `mass_r` and the
factor `(1 - N ^ (-k)) ^ (2 f)` moved to the left side. -/
lemma prod_frameMass_mul_le :
    (∏ v : D.Φ, D.frameMass v) * mass D.E D.r * (D.N ^ D.k / (D.N ^ D.k - 1)) ^ (2 * D.f) ≤
      (1 + D.b⁻¹ ^ 9) * ((D.N ^ D.k) ^ D.f * mass D.E D.k) := by
  -- Take logarithms: the product of the `sph_{i+1}` is `mass_i / mass_{i+1}` up to a small error,
  -- and these ratios telescope.
  let sphereProd : ℝ := ∏ i ∈ Ico D.k D.r, ∏ v : D.Φ, D.unitSphereMass (i + 1) v
  have sphereProd_pos : 0 < sphereProd := D.prod_prod_unitSphereMass_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have mass_r_pos : 0 < mass D.E D.r := mass_pos D.E D.r
  have ratio_pos : (0 : ℝ) < D.N ^ D.k / (D.N ^ D.k - 1) := div_pos
    (mod_cast pow_pos D.N_prime.pos _)
    (sub_pos.mpr (one_lt_pow₀ (mod_cast D.N_prime.one_lt) D.k_pos.ne'))
  have log_sphereProd_add_le : log (mass D.E D.r) - log (mass D.E D.k) + log sphereProd ≤
      log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := by
    rw [log_prod fun i _ ↦ (D.prod_unitSphereMass_pos (i + 1)).ne',
      ← sum_Ico_sub (fun i : ℕ ↦ log (mass D.E i)) D.k_le_r, ← sum_add_distrib]
    refine (sum_le_sum fun i hi ↦ ?_).trans D.sum_two_div_two_pow_le_log_sub
    linarith only [le_of_abs_le (D.abs_log_prod_unitSphereMass_sub_le (mem_Ico.mp hi).1)]
  have h_ratio : D.f * log (D.N ^ D.k / (D.N ^ D.k - 1)) ≤ D.f * (2 / D.N) :=
    mul_le_mul_of_nonneg_left D.log_pow_div_pow_sub_one_le D.f.cast_nonneg
  have sphereProd_mul_mass_le :
      sphereProd * mass D.E D.r * (D.N ^ D.k / (D.N ^ D.k - 1)) ^ (2 * D.f) ≤
        (1 + D.b⁻¹ ^ 9) * mass D.E D.k := by
    rw [← log_le_log_iff (by positivity) (by positivity)]
    simp (disch := positivity) only [log_mul, log_pow, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  rw [D.prod_frameMass_eq_mul_prod]
  linear_combination ((D.N : ℝ) ^ D.k) ^ D.f * sphereProd_mul_mass_le

/-- For the ranks `k` and `r = k + 2 ϱ + 1` of the data, the sum of the integers `i` with
`k ≤ i < r` is `(2 ϱ + 1) (k + ϱ)`, where `ϱ` is the number of hyperbolic planes. -/
lemma sum_Ico_k_r_cast : ∑ i ∈ Ico D.k D.r, (i : ℝ) = (2 * D.ϱ + 1) * (D.k + D.ϱ) := by
  have h_gauss : (∑ i ∈ range (2 * D.ϱ + 1), i) * 2 = (2 * D.ϱ + 1) * (2 * D.ϱ) :=
    sum_range_id_mul_two (2 * D.ϱ + 1)
  rw [← Nat.cast_sum _ fun i : ℕ ↦ i, sum_Ico_eq_sum_range, D.r_eq_k_add_two_mul_varrho_add_one,
    add_tsub_cancel_left, sum_add_distrib, sum_const, card_range, smul_eq_mul]
  norm_cast
  linarith

/-- The logarithm of the product of the `fr_v = N ^ k sph_{k+1} ⋯ sph_r` over the `f` infinite
places, as a linear form in the logarithms of `N`, `2`, `π`, the root discriminant and the `i!`. -/
lemma log_prod_frameMass :
    log (∏ v : D.Φ, D.frameMass v) =
      D.f * (D.k * log D.N - ∑ i ∈ Ico D.k D.r, log i.factorial + (2 * D.ϱ + 1) *
        ((D.k + D.ϱ + 1) * (log 2 + log π) - (D.k + D.ϱ + 1 / 2) * log D.rootDisc)) := by
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  rw [prod_frameMass_eq_mul_prod, log_mul (by positivity) D.prod_prod_unitSphereMass_pos.ne',
    log_prod fun i _ ↦ (D.prod_unitSphereMass_pos (i + 1)).ne', log_pow, log_pow]
  simp only [log_prod_unitSphereMass, sum_neg_distrib, ← mul_sum, sum_sub_distrib, sum_add_distrib,
    ← sum_mul, sum_const, nsmul_eq_mul, sum_Ico_k_r_cast, cast_card_Ico_k_r,
    log_mul two_ne_zero pi_ne_zero]
  ring

/-- The logarithm of `c_G = vol U(k) (2 π ^ k / (k - 1)!) / vol U(r)`, the constant of the open
cell, as a linear form in the logarithms of `2`, `π` and the factorials. Here `vol U(j)` is the
volume of the compact unitary group. The shape `D.shape` records the number `ϱ` of hyperbolic planes
and an index set with `k` elements. -/
lemma log_openCellConst :
    log D.shape.openCellConst =
      log 2 + D.k * log π - log (D.k - 1).factorial + ∑ i ∈ Ico D.k D.r, log i.factorial -
        (2 * D.ϱ + 1) * (log 2 + (D.k + D.ϱ + 1) * log π) := by
  have h_vol : volU D.r = volU D.k * ∏ i ∈ Ico D.k D.r, 2 * π ^ (i + 1) / i.factorial := by
    simp only [volU, sphereDensity, add_tsub_cancel_right, one_pow, mul_one,
      prod_range_mul_prod_Ico _ D.k_le_r]
  have h_cell : D.shape.openCellConst = (∏ i ∈ Ico D.k D.r, 2 * π ^ (i + 1) / i.factorial)⁻¹ *
      (2 * π ^ D.k / (D.k - 1).factorial) := by
    rw [openCellConst, Shape.k, Shape.r, card_X₀, card_rowIndex, h_vol,
      div_mul_cancel_left₀ (volU_pos _).ne', sphereDensity, one_pow, mul_one]
  rw [h_cell, log_mul (by positivity) (by positivity), log_inv, log_prod fun i _ ↦ by positivity]
  simp (disch := positivity) only [log_div, log_mul, log_pow, sum_sub_distrib, sum_add_distrib,
    ← sum_mul, sum_const, nsmul_eq_mul, Nat.cast_succ, sum_Ico_k_r_cast, cast_card_Ico_k_r]
  ring

/-- The product of the `fr_v = N ^ k sph_{k+1} ⋯ sph_r` over the `f` infinite places `v` of `E`
satisfies `(∏ fr_v) c_G ^ f |disc E| ^ (ϱ / 2) = c_S N ^ (2 k f) vol(Ô) ^ (ϱ + 1 + 2 ϱ (ϱ + k))`. -/
lemma prod_frameMass_mul_openCellConst_eq :
    (∏ v : D.Φ, D.frameMass v) *
        (D.shape.openCellConst ^ D.f * (√√|NumberField.discr D.E| ^ D.ϱ) ^ 2) =
      D.filling.siegelConst * ((D.N ^ D.k) ^ D.f) ^ 2 *
        volÔ D.E ^ (D.ϱ + 1 + 2 * (D.ϱ * (D.ϱ + D.k))) := by
  -- Both sides are positive, and their logarithms are linear in those of `2`, `π`, `N`, the root
  -- discriminant and the factorials.
  have rd_pos : 0 < D.rootDisc := rootDiscr_pos D.E
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  have frame_pos : 0 < ∏ v : D.Φ, D.frameMass v := prod_pos fun v _ ↦ D.frameMass_pos v
  have cell_pos : 0 < D.shape.openCellConst := D.shape.openCellConst_pos
  have h_root : √√|(NumberField.discr D.E : ℝ)| = √(D.rootDisc ^ D.f) := by
    rw [abs_discr_eq_rootDiscr_pow, sqrt_sq (by positivity)]
  have h_siegel : D.filling.siegelConst = (π ^ D.k / (D.k - 1).factorial / D.N ^ D.k) ^ D.f *
      √(D.rootDisc ^ D.f) * ((D.rootDisc / 2) ^ D.f)⁻¹ ^ D.k := by
    rw [siegelConst, volÔ_eq, h_root, Shape.k, card_X₀, show D.filling.N = D.N from rfl]
  rw [h_siegel, volÔ_eq, h_root]
  refine log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) ?_
  simp (disch := positivity) only [log_mul, log_div, log_pow, log_inv, log_sqrt,
    log_prod_frameMass, log_openCellConst]
  push_cast
  ring

end New.Data

end
end
end

/-!
# Filling data for admissible data: fit to Y₀, Bessel bounds, standing hypotheses

For admissible data `D`, the file shows that the filling data `New.Data.filling` fit the space `Y₀`.
It also shows that they satisfy the standing hypotheses `New.Filling.IsAdmissible`, so that the
general filling theorem applies.

## Main definitions and results

* `New.Data.filling_fits`: the filling data `New.Data.filling` fit the space `Y₀`
  (`New.Filling.Fits`).
* `New.Data.sourceFormCoords`: source forms in coordinates, indexed by pairs (class, Bessel
  coordinate).
* `New.Data.goodProjTranslate`: the map from forms of level `M` on `Y₀` to the image of the good
  idempotent `New.Data.e₀`. It is a translation followed by this idempotent, scaled by the order of
  the finite group `𝖦`.
* `New.Data.card_besselSystem_le_pow`, `New.Data.card_besselCoord_le_pow`: the Bessel system at one
  place has at most `b ^ (2 k)` coordinates, and their tensor product at most `b ^ (2 k f)`.
* `New.Data.log_filling_besselDegree_mem_Icc`: two-sided bounds for the logarithm of the degree of
  the Bessel systems.
* `New.Data.card_mul_card_classes_mul_prod_le`, `New.Data.card_sq_mul_mass_mul_prod_le`: two
  products built from group orders, class number, masses, dimensions and degrees are at most
  `(1 + b⁻⁹)` times `New.Filling.mainSecondMoment`.

Notions from other files:
* `New.Data.spaceY`: for an index `j`, the hermitian space `Y_j` with its adelic frame, hence its
  lattice `𝖬_j`, chosen as in `New.Data.exists_space_isStd_of_le_and_gram_eq_of_lt`. Only `j = 0`
  occurs in this file.
* `New.Data.chosenGL`: The finite group 𝖦 = ∏ GL_r(𝔽_w), over the chosen places w above p₀ and p₁.
* `New.Data.targetParameter`: The entry i (from 0) of the target parameter at v: k/2 − 1 − i for
  i < k − 1, and Δ/2 − w_{i+2−k}(v) otherwise, where Δ/2 = `D.halfGap` and
  w_j(v) = `D.liftWeight j v`.
* `New.Filling.besselDegree`: The product over infinite places of the degrees of the Bessel systems.
* `New.Data.logLevelTarget`: a number `λ`, built from the mean of the `log (D.weight v)`, from
  `log (M rootDisc / 2π)` and from `log b`, with `λ ≤ log N ≤ λ + √(log b)`.
-/

@[expose] public section

noncomputable section

/-! ## Fit to Y₀, source forms in coordinates and the projection to target forms -/

namespace New.Data

open Matrix Shape Unitary Units

variable {P : Parameters} (D : Data P)

/-- The filling data of D fit the hermitian space Y₀ = `D.spaceY 0` in the sense of
`New.Filling.Fits`. -/
lemma filling_fits :
    D.filling.Fits (D.spaceY 0) D.paramW D.columnCount (D.gradingY 0)
      (scalarFin D.shape.κ (D.latticeScale 0))⁻¹ := by
  -- The finite frame of `Y₀` is `gradedLatticeBasis` times an integral `γ` that is `≡ 1` at the
  -- chosen places, by the choice of `D.spaceY`.
  obtain ⟨γ, hγ_red, (hγ : (D.spaceY 0).xFin.val =
      gradedLatticeBasis D.shape.besselIndexEquiv D.ideleA D.piNIdele (D.latticeScale 0) *
        γ.val.val)⟩ :=
    D.exists_spaceY_xFin_eq 0 D.nat_le_of_hasLogBound
  -- `gradedLatticeBasis` scales only the string by `u = D.latticeScale 0`. So it is the lattice
  -- basis of the filling data scaled by `u` on the whole space and then by `u⁻¹` on `X₀`.
  have h_lat :
      gradedLatticeBasis D.shape.besselIndexEquiv D.ideleA D.piNIdele (D.latticeScale 0) =
        (Unitary.toUnits (D.latticeScale 0) •
            (toBesselH D.shape (D.N : 𝔸f D.E) (scalarFin D.shape.κ (D.latticeScale 0))⁻¹).val *
          D.filling.latticeBasis).val := by
    have h_embed (a : Gf D.E D.shape.κ) : (toBesselH D.shape (D.N : 𝔸f D.E) a).val.val =
        fromBlocks 1 0 0 (fromBlocks (fromBlocks a.val.val 0 0 1) 0 0 1) := rfl
    have h_unit (c : 𝔸f D.E) : (D.latticeScale 0).val * (star (D.latticeScale 0).val * c) = c := by
      simp [← mul_assoc]
    rw [Units.val_mul, Units.val_smul, smul_mul_assoc, h_embed, ← map_inv]
    -- Compare the entries: equal indices give the scalars, by `h_unit`. Otherwise both are 0, as
    -- the string indices `a`, `ϱ`, `2 ϱ - b` for `a, b < ϱ` are different.
    simp [h_unit, ← ext_iff, filling, besselLatticeBasis, fromBlocks_multiply, scalarFin,
      ← Unitary.star_eq_inv, besselIndexEquiv, gradedLatticeBasis, diagonal_apply, smul_def,
      fromBlocks_smul, Matrix.one_apply, Fin.ext_iff, Fin.val_rev]
    and_intros <;> grind
  rw [h_lat] at hγ
  exact
    { isDiscreteSeriesBessel := D.isDiscreteSeriesBessel_filling_besselSystem
      index_eq := rfl
      isIdempotentKernel := D.isCuspKernel_typeKernel_paramW.toIsIdempotentKernel
      exists_point_eq := ⟨γ, fun i w ↦ hγ_red ⟨i, w⟩, toUnits (D.latticeScale 0), ext hγ⟩
      central a := (Seesaw.commute_scalarFin a).inv_left }

/-- The isomorphism that applies the central translation by `D.latticeScale 0` to a source form on
X₀ and takes its values at the class representatives, in the coordinates of the Bessel systems. -/
def sourceFormCoords :
    ↥D.SourceForm ≃ₗ[ℂ] EuclideanSpace ℂ (D.filling.Classes × D.filling.BesselCoord) :=
  LinearEquiv.ofBijective (D.centralRep (D.latticeScale 0))
    (D.centralRep.apply_bijective (D.latticeScale 0)) ≪≫ₗ D.filling_fits.sourceFormCoords

/-- For s in 𝖦, the linear map from forms of parameter ς and level M on Y₀ to the image of the good
idempotent e₀. It is the translation by s, followed by |𝖦| times the action of e₀. -/
abbrev goodProjTranslate (s : D.chosenGL) :
    ↥(D.principalForms (D.spaceY 0)) →ₗ[ℂ]
      LinearMap.range ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀) :=
  (Nat.card D.chosenGL : ℂ) •
    ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀).rangeRestrict ∘ₗ D.principalRep (D.spaceY 0) s

end New.Data

/-!
## Bessel systems: number of coordinates, target parameter and degree

`New.Data.targetParameter v i` is numbered from 0, and `f` is the number of infinite places.
-/

section DegreeBounds

open Nat Finset Real

namespace New.Data

variable {P : Parameters} (D : Data P)

/-- At each infinite place `v`, the Bessel system of `D` has at most `(k + a) ^ k` coordinates, `k`
the rank of `X₀`. Their number is the dimension of the representation of `U(X₀)` at `v`, which is
that of a symmetric power of degree at most `a = D.a` of a space of dimension `k`. -/
lemma card_besselSystem_le_add_pow (v : D.Φ) :
    Fintype.card (D.filling.besselSystem v).Index ≤ (D.k + D.a) ^ D.k := by
  -- The coordinates correspond to a basis of the Schur module of weight `D.columnCount v` (`A`,
  -- `A'` are inverse matrices); this weight has no columns of height `2, …, k - 1`, so the basis is
  -- in bijection `e` with the monomials of degree `D.columnCount v 1` in the variables `D.X 0`.
  obtain ⟨A, A', hAA', hA'A, -⟩ := (D.filling_fits.isDiscreteSeriesBessel
    v).exists_conj_rep_eq_schur
  have h_degree : D.columnCount v 1 ≤ D.a := by by_cases hv : v ∈ D.aPlaces <;>
                                                  simp [columnCount, hv]
  have one_lt_k : 1 < D.k := D.nat_le_of_hasLogBound
  have h_row (i : ℕ) (_ : 0 < i) (hi_lt : i < Fintype.card (D.X 0)) :
      D.columnCount v i = if i = 1 then D.columnCount v 1 else 0 := by
    rw [D.card_X₀] at hi_lt
    by_cases hi_one : i = 1 <;> simp [columnCount, hi_one, hi_lt.ne, hi_lt.not_gt]
  obtain ⟨(e : WeylIndexFamily (fun _ ↦ D.X 0) (fun _ ↦ D.columnCount v) ≃ Monomials (D.X 0)
    (D.columnCount v 1)), -⟩ :=
    exists_equiv_schur_one_row_eq_symPowMatrix (.refl (D.X 0)) (one_lt_k.trans_eq D.card_X₀.symm)
      h_row
  -- There are `choose (k + a' - 1) a'` monomials of degree `a' ≤ a` in `k` variables.
  calc Fintype.card (D.filling.besselSystem v).Index
    _ = #((univ : Finset (D.X 0)).finsuppAntidiag (D.columnCount v 1)) := by
      rw [A'.square_of_invertible A hA'A hAA', ← card_eq_of_equiv_fintype e.symm]
    _ = (D.k + D.columnCount v 1 - 1).choose (D.columnCount v 1) := by
      rw [card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, D.card_X₀]
    _ ≤ (D.k + D.columnCount v 1).choose D.k := by grw [sub_le, choose_symm_add]
    _ ≤ (D.k + D.a) ^ D.k := by grw [choose_le_pow, h_degree]

/-- At each infinite place `v`, the number of coordinates of the Bessel system of `D`, that is the
dimension of the representation of `U(X₀)` at `v`, is at most `b ^ (2 k)`, `k` the rank of `X₀`. -/
lemma card_besselSystem_le_pow (v : D.Φ) :
    (Fintype.card (D.filling.besselSystem v).Index : ℝ) ≤ D.b ^ (2 * D.k) := by
  calc (Fintype.card (D.filling.besselSystem v).Index : ℝ)
    _ ≤ (D.k + D.a : ℝ) ^ D.k := mod_cast D.card_besselSystem_le_add_pow v
    _ ≤ (D.b ^ 2) ^ D.k := pow_le_pow_left₀ (by positivity) D.le_of_hasLogBound _
    _ = D.b ^ (2 * D.k) := (pow_mul _ _ _).symm

/-- The tensor product of the Bessel systems of `D` over the `f` infinite places has at most
`b ^ (2 k f)` coordinates, `k` the rank of `X₀`. -/
lemma card_besselCoord_le_pow :
    (Fintype.card D.filling.BesselCoord : ℝ) ≤ D.b ^ (2 * D.k * D.f) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _v : D.Φ, D.b ^ (2 * D.k) := by
      gcongr with v
      exact D.card_besselSystem_le_pow v
    _ = D.b ^ (2 * D.k * D.f) := by rw [prod_const, Finset.card_univ, ← pow_mul]

/-- For admissible data `D`, let `d` be the number of coordinates of the tensor product of the
Bessel systems, `k` the rank of `X₀`, `f` the number of infinite places and `b = D.b` the weight at
the `b`-places. Then `d ((k - 1)!)^f ≤ (b^{5/4})^{k f}`, where `b^{5/4}` is written `(√√b)^5`. -/
lemma card_besselCoord_mul_factorial_le :
    (Fintype.card D.filling.BesselCoord * (D.k - 1)! ^ D.f : ℝ) ≤ ((√√D.b ^ 5) ^ D.k) ^ D.f := by
  -- Multiply `card_besselSystem_le_add_pow` over the `f` places, with `(k - 1)! ≤ k ^ k` and
  -- `(k + a) * k ≤ √√b ^ 5`.
  have h_coords : Fintype.card D.filling.BesselCoord ≤ ((D.k + D.a) ^ D.k) ^ D.f := by
    simpa [Fintype.card_pi] using prod_le_pow_card univ _ _ fun v _ ↦
      D.card_besselSystem_le_add_pow v
  have h_factorial : (D.k - 1)! ≤ D.k ^ D.k := by grw [sub_le, factorial_le_pow]
  have h_size : (D.k + D.a : ℝ) * D.k ≤ √√D.b ^ 5 := D.le_of_hasLogBound
  calc
    _ ≤ ((D.k + D.a : ℝ) ^ D.k) ^ D.f * ((D.k : ℝ) ^ D.k) ^ D.f := by
      exact_mod_cast Nat.mul_le_mul h_coords (Nat.pow_le_pow_left h_factorial D.f)
    _ = (((D.k + D.a : ℝ) * D.k) ^ D.k) ^ D.f := by simp [mul_pow]
    _ ≤ ((√√D.b ^ 5) ^ D.k) ^ D.f := by gcongr

/-- For `i < l` and an infinite place `v`, the difference
`D.targetParameter v i - D.targetParameter v l` of entries of the target parameter lies between `1`
and the lift weight `D.liftWeight (l + 2 - D.k) v`. Here `k = D.k` is the rank of the source, and
`l + 2 - D.k` is truncated subtraction of natural numbers. -/
lemma targetParameter_sub_mem_Icc (v : D.Φ) {i l : ℕ} (hil : i < l) :
    (D.targetParameter v i - D.targetParameter v l : ℝ) ∈ Set.Icc 1
      ↑(D.liftWeight (l + 2 - D.k) v) := by
  -- `1 ≤`: the integers `D.targetParameter v i` strictly decrease. `≤ w`: unfold `targetParameter`;
  -- the entries numbered below `k - 1` are small, the others are `D.halfGap - w`.
  have h_anti : D.targetParameter v l < D.targetParameter v i := D.targetParameter_strictAnti v hil
  rw [Set.mem_Icc]
  norm_cast
  grind [targetParameter_eq]

/-- The degree `D.filling.besselDegree` of the Bessel systems of `D` is the exponential of the sum,
over the infinite places `v` and over `k - 1 ≤ l < r`, of `∑_{i<l} log (ς_i - ς_l) - log l!`. Here
`ς = D.targetParameter v` is the sequence of `r = D.r` entries from which the Harish-Chandra
parameters at `v` are read off, and `k = D.k`. -/
lemma filling_besselDegree_eq_exp_sum :
    D.filling.besselDegree = exp (∑ v : D.Φ, ∑ l ∈ Ico (D.k - 1) D.r,
      (∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) - Real.log l !)) := by
  push_cast [Filling.besselDegree, (D.filling_fits.isDiscreteSeriesBessel _).deg_eq, ↓card_rowIndex,
    exp_sum, exp_sub, weylDimensionPoly, ↓paramW_lt_iff, paramW]
  congr! with v
  -- Index the pairs by their numbers under `basisNumber`.
  simp [prod_comm, prod_filter, reindex_equiv D.basisNumber.symm, prod_fin_eq_prod_range,
    ← mem_range, ← prod_div_distrib]
  refine prod_congr_of_eq_on_inter (fun l hl hl' ↦ ?_)
    (fun l hl hl' ↦ absurd (mem_range.2 (mem_Ico.1 hl).2) hl') (fun l hl _ ↦ ?_)
  -- `l < k - 1`: the differences are `l - i`, with product `l!`.
  · field_simp
    norm_cast
    rw [min_eq_right (mem_range.1 hl).le, prod_congr rfl (g := fun i ↦ ((l - 1 - i : ℕ) : ℤ) + 1)
      fun i hi ↦ by grind [targetParameter_eq]]
    simp [prod_range_reflect (fun i : ℕ ↦ (i : ℤ) + 1), ← prod_range_add_one_eq_factorial]
  -- `k - 1 ≤ l < r`: the numbers under `log` are positive by `targetParameter_sub_mem_Icc`.
  · rw [min_eq_right (mem_range.1 hl).le, exp_log (mod_cast l.factorial_pos)]
    refine congrArg (· / (l ! : ℝ)) (prod_congr rfl fun i hi ↦ ?_)
    rw [exp_log (one_pos.trans_le (D.targetParameter_sub_mem_Icc v (mem_range.1 hi)).1)]
    ring

/-- The logarithm of the degree of the Bessel systems of `D`, plus `f` times the sum of `log l!`
over `k − 1 ≤ l < r`, lies between `∑_v m (k − 1) log W_v` and `∑_v m r (log W_v + 1/x)`. Here `v`
runs over the `f` infinite places, `k` is the rank of `X₀`, `r` is the number of entries of the
target parameter, `m = r - k + 1`, `x` is the parameter `D.x` of the data and `W_v` is
`D.weight v`. -/
lemma log_filling_besselDegree_mem_Icc :
    Real.log D.filling.besselDegree + D.f * ∑ l ∈ Ico (D.k - 1) D.r, Real.log l ! ∈ Set.Icc
      (∑ v : D.Φ, D.m * ((D.k - 1) * Real.log (D.weight v)))
      (∑ v : D.Φ, D.m * (D.r * (Real.log (D.weight v) + D.x⁻¹))) := by
  -- After inserting the formula for the degree the factorials cancel; it remains to bound, for each
  -- `l`, the sum of `log (ς_i - ς_l)` over `i < l`.
  have deg_eq : D.filling.besselDegree = exp (∑ v, ∑ l ∈ Ico (D.k - 1) D.r,
      (∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) - Real.log l !)) :=
    D.filling_besselDegree_eq_exp_sum
  have h_low (v : D.Φ) (l : ℕ) (hl : l ∈ Ico (D.k - 1) D.r) : (D.k - 1) * Real.log (D.weight v) ≤
      ∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) := by
    -- Keep only the terms `i < k - 1`; each of these differences is at least `weight v`.
    have h_diff (i : ℕ) (hi : i ∈ range (D.k - 1)) :
        (D.weight v : ℝ) ≤ D.targetParameter v i - D.targetParameter v l :=
      (D.weight_le_liftWeight_sub 0 v).trans (by norm_cast; grind [targetParameter_eq])
    calc
      _ ≤ ∑ i ∈ range (D.k - 1), log (D.targetParameter v i - D.targetParameter v l) := by
        simpa using sum_le_sum fun i hi ↦ log_le_log (HasLogBound.pos D) (h_diff i hi)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (mem_Ico.1 hl).1) fun i hi _ ↦
        log_nonneg (D.targetParameter_sub_mem_Icc v (mem_range.1 hi)).1
  have h_up (v : D.Φ) (l : ℕ) (hl : l ∈ Ico (D.k - 1) D.r) :
      ∑ i ∈ range l, log (D.targetParameter v i - D.targetParameter v l) ≤
        D.r * (Real.log (D.weight v) + D.x⁻¹) := by
    -- Each of the `l < r` differences is at most `liftWeight (l + 2 - k) v` by
    -- `targetParameter_sub_mem_Icc`.
    calc
      _ ≤ ∑ i ∈ range l, Real.log (D.liftWeight (l + 2 - D.k) v) := sum_le_sum fun i hi ↦ by
        obtain ⟨h_one_le, h_le_w⟩ := D.targetParameter_sub_mem_Icc v (mem_range.1 hi)
        exact log_le_log (one_pos.trans_le h_one_le) h_le_w
      _ = l * Real.log (D.liftWeight (l + 2 - D.k) v) := by simp
      _ ≤ D.r * (Real.log (D.weight v) + D.x⁻¹) := by
        grw [(mem_Ico.1 hl).2, D.log_liftWeight_le (by grind)]
  -- Sum both bounds over `v` and over the `m` values of `l`.
  have h_card : D.r - (D.k - 1) = D.m := by grind
  constructor
  · simpa [deg_eq, h_card] using sum_le_sum (s := univ) fun (v : D.Φ) _ ↦ sum_le_sum (h_low v)
  · simpa [deg_eq, h_card] using sum_le_sum (s := univ) fun (v : D.Φ) _ ↦ sum_le_sum (h_up v)

end New.Data

end DegreeBounds

/-!
## Number of classes, mean values and the standing hypotheses

The ratio of the main second moment to the second moment of the Bessel group is computed exactly
(`New.Data.mainSecondMoment_div_identitySecondMoment_eq`). The sizes of the degree, of the ratio of
the masses and of `N` then give the range of this ratio
(`New.Data.mainSecondMoment_div_identitySecondMoment_mem_Icc`).
-/

namespace New.Data

open Finset Real Filling Subgroup MulAction Fintype Shape NeZero NumberField

variable {P : Parameters} (D : Data P)

/-- The finite points of `U(X₀)` that `New.Filling.inclHFin` sends into the integral group
`New.Filling.latticeStabilizer` have index `(N^k - 1)^f` in the group `New.stdLevel` of integral
points, `N` being the prime level, `k` the rank of `X₀` and `f` the number of infinite places. -/
lemma relIndex_latticeStabilizer :
    (D.filling.latticeStabilizer.comap D.filling.inclHFin).relIndex (stdLevel D.E D.shape.κ) =
      (D.N ^ D.k - 1 : ℝ) ^ D.f := by
  -- An integral x lies in this preimage iff its row `k₀` is the unit vector modulo every place
  -- of `D.piNPlaces`; each such stabiliser has index N ^ k - 1, and there are f places.
  -- `H w` fixes the unit vector under the inverse transpose: row `k₀` is the unit vector.
  let H (w : D.piNPlaces) : Subgroup (GL (D.X 0) (ResField w.val)) :=
    (stabilizer _ (Pi.single D.shape.k₀ 1 : D.X 0 → ResField w.1)).comap invTransposeGL.toMonoidHom
  have h_level :
      D.filling.latticeStabilizer.comap D.filling.inclHFin = levelOf Subtype.val (pi ⊤ H) := by
    ext x
    rw [Subgroup.mem_comap, mem_levelOf, D.filling.inclHFin_mem_latticeStabilizer_iff]
    -- Both sides say that `x` is integral, with a condition on its row `k₀`.
    change (x.val ∈ intGL D.shape.κ (Ô D.E) ∧ ∀ (_ : Unit) (j : D.shape.κ),
      (x.val.val - 1) D.shape.k₀ j ∈ Ô D.E ∙ D.piNIdele.val) ↔ _
    refine exists_prop.symm.trans (exists_congr fun hx : x.val ∈ intGL D.shape.κ (Ô D.E) ↦ ?_)
    -- π divides an integral adele iff it reduces to zero at every place of `D.piNPlaces`, and `H w`
    -- says that the entries `r j` of row `k₀` of `x - 1` reduce to zero at `w`.
    let r (j : D.shape.κ) : Ô D.E :=
      ⟨x.val.val D.shape.k₀ j, hx.isIntMatrix D.shape.k₀ j⟩ - if j = D.shape.k₀ then 1 else 0
    have h_mem (j : D.shape.κ) : (x.val.val - 1) D.shape.k₀ j ∈ Ô D.E ∙ D.piNIdele.val ↔
        algebraMap (RingOfIntegers D.E) (Ô D.E) D.piN ∣ r j := by
      by_cases hj : j = D.shape.k₀ <;>
        simp [hj, Ne.symm, r, Submodule.mem_span_singleton, dvd_def, Subtype.ext_iff,
          Subring.smul_def, piNIdele] <;>
        exact exists_congr fun _ ↦ and_congr_right' (by rw [mul_comm, eq_comm])
    have h_fix (w : D.piNPlaces) : stdLevel.reduceFamily Subtype.val ⟨x, hx⟩ w ∈ H w ↔
        ∀ j : D.shape.κ, reduceAt w.val (r j) = 0 := by
      -- The inverse transpose fixes the unit vector iff row `k₀` of the reduction is that vector.
      have h_mem_H (M : GL (D.X 0) (ResField w.val)) : M ∈ H w ↔
          (transposeGL M)⁻¹ ∈ stabilizer _ (Pi.single D.shape.k₀ 1 : D.X 0 → ResField w.val) := .rfl
      rw [h_mem_H]
      have h_entry (j : D.shape.κ) : (stdLevel.reduceFamily Subtype.val ⟨x, hx⟩ w).1 D.shape.k₀ j =
          reduceAt w.val ⟨x.val.val D.shape.k₀ j, hx.isIntMatrix D.shape.k₀ j⟩ := rfl
      simp [r, h_entry, funext_iff, Units.smul_def, -reduceAt_eq_zero, sub_eq_zero]
    simp only [Subgroup.mem_pi, h_mem, dvd_iff_reduceAt_eq_zero D.intValuation_piN, h_fix,
      forall_const, ← mem_piNPlaces]
    exact ⟨fun h w _ j ↦ h j w.val w.property, fun h j w hw ↦ h ⟨w, hw⟩ trivial j⟩
  -- The index of a preimage under reduction is the product of the indices of the stabilisers.
  rw [h_level, relIndex_levelOf (h := ⟨by simp, by simp [D.isSplitLevel_piNPlaces.star_notMem]⟩)]
  simp [Seesaw.index_pi_univ, H, index_comap, index_stabilizer_GL_vector, card_ResField,
    D.isSplitLevel_piNPlaces.q_eq, ↓card_X₀, Fin.pos', card_piNPlaces]

/-- The number of classes of level `New.Data.levelX 0` on `U(X₀)` is `|H̄| (N^k - 1)^f` times
the mass `New.mass` in rank `k`, where `H̄` is the image (`New.Filling.reducedImage`) under
reduction of the integral points of `H = besselH`, the copy of `U(X₀)` in the unitary group, `N` is
the prime level and `f` is the number of infinite places. -/
lemma card_classes_eq_card_mul_pow_mul_mass :
    (Fintype.card D.filling.Classes : ℝ) =
      Nat.card (D.filling.reducedImage besselH) * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k := by
  -- The classes have trivial automorphism groups, so their number is the index of `D.levelX 0`
  -- in `stdLevel` times the mass; the index splits along
  -- `D.levelX 0 ≤ (preimage of latticeStabilizer) ≤ stdLevel`.
  rw [card_eq_nat_card]
  refine (card_classes_eq_classSum D.classAut_levelX_zero_eq_bot).trans ?_
  rw [classSum_one_of_le IsLevel.le, classSum_stdRatPoints_eq_mass, card_X₀,
    ← relIndex_mul_relIndex _ (D.filling.latticeStabilizer.comap D.filling.inclHFin) _
      (D.levelX_zero_eq_comap.trans_le (comap_mono (map_subtype_le _)))
      fun x hx ↦ (D.filling.inclHFin_mem_latticeStabilizer_iff.1 hx).1,
    levelX_zero_eq_comap, D.filling.relIndex_comap_principalLevel]
  simp [D.relIndex_latticeStabilizer]

/-- With `fr_v` the frame mass, and `d_v`, `deg_v` the dimension and the degree of the Bessel system
at `v`, the product of the `fr_v d_v ^ 2 / deg_v` is `(∏ fr_v) d ^ 2 / deg`, where `d` and `deg` are
the dimension and the degree of the tensor product of the Bessel systems. -/
lemma prod_frameMass_mul_div_eq :
    ∏ v : D.Φ, D.frameMass v * Fintype.card (D.filling.besselSystem v).Index ^ 2 /
        (D.filling.besselSystem v).deg =
      (∏ v : D.Φ, D.frameMass v) * Fintype.card D.filling.BesselCoord ^ 2 /
        D.filling.besselDegree := by
  rw [prod_div_distrib, prod_mul_distrib, prod_pow, Fintype.card_pi, Nat.cast_prod, besselDegree]

/-- At an infinite place `v`, let `fr_v` be the frame mass, `sph_k` the mass of the unit sphere in
the rank `k` of `X₀`, `d_v` and `deg_v` the number of coordinates and the degree of the Bessel
system, and `c_v = fr_v N ^ k d_v ^ 2 / (sph_k deg_v)`, with `N` the prime level. The product of
the `sph_k c_v` over the `f` infinite places is `N ^ (k f) (∏ fr_v) d ^ 2 / deg`, where
`d = ∏ d_v` and `deg = ∏ deg_v`: the masses `sph_k` cancel. -/
lemma prod_unitSphereMass_mul_div_eq :
    ∏ v : D.Φ, D.unitSphereMass D.k v * (D.frameMass v * D.N ^ D.k *
        Fintype.card (D.filling.besselSystem v).Index ^ 2 /
          (D.unitSphereMass D.k v * (D.filling.besselSystem v).deg)) =
      (D.N ^ D.k) ^ D.f * ((∏ v : D.Φ, D.frameMass v) * Fintype.card D.filling.BesselCoord ^ 2 /
        D.filling.besselDegree) := by
  have h_const : ((D.N : ℝ) ^ D.k) ^ D.f = ∏ _v : D.Φ, (D.N : ℝ) ^ D.k := by simp
  rw [← D.prod_frameMass_mul_div_eq, h_const, ← prod_mul_distrib]
  congr! 1 with v
  field_simp [(D.unitSphereMass_pos D.k v).ne']

/-- The main second moment of the filling data is
`(|H̄| (N ^ k - 1) ^ f mass_k d) ^ 2 / (deg mass_r)`, where `H̄` is the reduced image of `besselH`,
`mass_l` is `New.mass` in rank `l`, and `d`, `deg` are the dimension and the degree of the tensor
product of the Bessel systems. -/
lemma filling_mainSecondMoment_eq :
    D.filling.mainSecondMoment =
      (Nat.card (D.filling.reducedImage besselH) * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k *
        Fintype.card D.filling.BesselCoord) ^ 2 / (D.filling.besselDegree * mass D.E D.r) := by
  rw [mainSecondMoment, sourceDim, Nat.cast_mul, card_classes_eq_card_mul_pow_mul_mass, Shape.r,
    D.card_rowIndex]

/-- Since the prime level `N` is at least `2`, the number `N ^ k - 1` is positive. -/
lemma pow_sub_one_pos : (0 : ℝ) < D.N ^ D.k - 1 :=
  sub_pos.mpr (one_lt_pow₀ (mod_cast D.N_prime.one_lt) D.k_pos.ne')

/-- For the filling data of admissible data `D`, let `H̄` be the reduced image of `besselH`, `d_v`
and `deg_v` the dimension and the degree of the Bessel system at `v`, `fr_v` the frame mass, `sph_k`
the mass of the sphere in rank `k`, `mass_l` the mass `New.mass` in rank `l` and
`c_v = fr_v N ^ k d_v ^ 2 / (sph_k deg_v)`. Then `|H̄| ^ 2 mass_k ∏ sph_k c_v` is at most
`(1 + b⁻⁹)` times the main second moment `(n_X ∏ d_v) ^ 2 / (mass_r ∏ deg_v)`. Here `n_X` is the
number of classes, `k`, `r` are the ranks of `X₀`, `Y₀`, and `b = D.b` is the weight at the
`b`-places. -/
theorem card_sq_mul_mass_mul_prod_le :
    Nat.card (D.filling.reducedImage besselH) ^ 2 * mass D.E D.k *
        ∏ v : D.Φ, D.unitSphereMass D.k v * (D.frameMass v * D.N ^ D.k *
          Fintype.card (D.filling.besselSystem v).Index ^ 2 /
            (D.unitSphereMass D.k v * (D.filling.besselSystem v).deg)) ≤
      (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
  -- The left side is the left side of `prod_frameMass_mul_le` times the number `multiplier`.
  let multiplier : ℝ := D.filling.mainSecondMoment / ((D.N ^ D.k) ^ D.f * mass D.E D.k)
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have mass_r_pos : 0 < mass D.E D.r := mass_pos D.E D.r
  have pred_pos : (0 : ℝ) < D.N ^ D.k - 1 := D.pow_sub_one_pos
  have multiplier_nonneg : 0 ≤ multiplier := by
    simp only [multiplier, filling_mainSecondMoment_eq]
    positivity
  rw [D.prod_unitSphereMass_mul_div_eq]
  calc
    _ = (∏ v : D.Φ, D.frameMass v) * mass D.E D.r * (D.N ^ D.k / (D.N ^ D.k - 1)) ^ (2 * D.f) *
        multiplier := by
      simp only [multiplier, filling_mainSecondMoment_eq, div_pow, mul_comm 2 D.f, pow_mul]
      field_simp
    _ ≤ (1 + D.b⁻¹ ^ 9) * ((D.N ^ D.k) ^ D.f * mass D.E D.k) * multiplier :=
      mul_le_mul_of_nonneg_right D.prod_frameMass_mul_le multiplier_nonneg
    _ = (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
      simp only [multiplier]
      field_simp

/-- For the filling data of admissible data `D`, let `H̄` be the reduced image of `besselH`, `n_X`
the number of classes, `d_v` and `deg_v` the dimension and the degree of the Bessel system at `v`
and `fr_v` the frame mass. Then `|H̄| n_X ∏ fr_v d_v ^ 2 / deg_v` is at most `(1 + b⁻⁹)` times the
main second moment `(n_X ∏ d_v) ^ 2 / (mass_r ∏ deg_v)`. Here `mass_r` is the mass `New.mass` in the
rank `r` of `Y₀`, and `b = D.b` is the weight at the `b`-places. -/
theorem card_mul_card_classes_mul_prod_le :
    Nat.card (D.filling.reducedImage besselH) * Fintype.card D.filling.Classes *
        ∏ v : D.Φ, D.frameMass v * Fintype.card (D.filling.besselSystem v).Index ^ 2 /
          (D.filling.besselSystem v).deg ≤
      (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
  -- With `n_X = |H̄| (N ^ k - 1) ^ f mass_k` the left side is at most the left side of
  -- `card_sq_mul_mass_mul_prod_le`, which has `N ^ k` in place of `N ^ k - 1`.
  let H : ℝ := Nat.card (D.filling.reducedImage besselH)
  let Q : ℝ := (∏ v : D.Φ, D.frameMass v) * Fintype.card D.filling.BesselCoord ^ 2 /
    D.filling.besselDegree
  have frame_pos : 0 < ∏ v : D.Φ, D.frameMass v := prod_pos fun v _ ↦ D.frameMass_pos v
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have pred_pos : (0 : ℝ) < D.N ^ D.k - 1 := D.pow_sub_one_pos
  rw [D.prod_frameMass_mul_div_eq, card_classes_eq_card_mul_pow_mul_mass]
  calc
    _ = H ^ 2 * mass D.E D.k * ((D.N ^ D.k - 1) ^ D.f * Q) := by ring
    _ ≤ H ^ 2 * mass D.E D.k * ((D.N ^ D.k) ^ D.f * Q) := by
      gcongr
      linarith
    _ ≤ (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment := by
      rw [← D.prod_unitSphereMass_mul_div_eq]
      exact D.card_sq_mul_mass_mul_prod_le

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- For the filling data of admissible data `D`, the scaled Siegel constant `|S̄| |Ū| n_X c_S` is at
most `(1 + b⁻⁹)` times the main second moment `(n_X d)² / (deg mass_r)` times
`deg c^f / vol^n (cov Λ / d)²`. Here `S̄` is the reduced image of the Bessel subgroup `besselS`,
`|Ū| = unipotentOrder`, `n_X` is the number of classes, `c_S = siegelConst`, `b = D.b` is the weight
at the `b`-places, `d` and `deg` are the number of coordinates and the degree of the tensor product
of the Bessel systems, and `mass_r` is the mass in the rank `r` of `Y₀`. Further
`c = openCellConst`, `f` is the number of infinite places, `vol` the volume of the integral finite
adeles, `n` the number of frame vectors, `cov = unipotentCovolume` and `Λ = frameScaleProd`. -/
lemma scaledSiegelConst_le : D.filling.scaledSiegelConst ≤
    (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment * D.filling.besselDegree * D.shape.openCellConst ^
      D.f /
      volÔ D.E ^ D.shape.n * (D.filling.unipotentCovolume * D.filling.frameScaleProd /
        Fintype.card D.filling.BesselCoord) ^ 2 := by
  -- The scaled Siegel constant is the left side of `card_mul_card_classes_mul_prod_le` times
  -- `scale`.
  let scale : ℝ := D.filling.besselDegree * D.shape.openCellConst ^ D.f / volÔ D.E ^ D.shape.n *
    (D.filling.unipotentCovolume * D.filling.frameScaleProd / Fintype.card D.filling.BesselCoord) ^
      2
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have cell_pos : 0 < D.shape.openCellConst := D.shape.openCellConst_pos
  have vol_pos : (0 : ℝ) < volÔ D.E := by
    rw [volÔ_eq]
    positivity [rootDiscr_pos D.E]
  have N_pos : (0 : ℝ) < D.N := mod_cast D.N_prime.pos
  have h_rank : ∑ a ∈ range D.ϱ, (a + (D.k + 1) + a) = D.ϱ * (D.ϱ + D.k) := by
    induction D.ϱ with
    | zero => simp
    | succ n ih => grind [sum_range_succ]
  have h_covolume : D.filling.unipotentCovolume * D.filling.frameScaleProd =
      D.filling.unipotentOrder / (D.N ^ D.k) ^ D.f / volÔ D.E ^ (D.ϱ * (D.ϱ + D.k)) *
        √√|NumberField.discr D.E| ^ D.ϱ := by
    have h_order : ((D.filling.M : ℝ) ^ (2 * (D.ϱ * (D.ϱ + D.k)) + D.ϱ)) ^ D.f =
        D.filling.unipotentOrder := by
      rw [← pow_mul, unipotentOrder, Shape.k, card_X₀, Nat.cast_pow]
      ring
    -- The factor `frameScaleProd` cancels from the definition of the covolume.
    rw [Filling.unipotentCovolume, div_mul_cancel₀ _ D.filling.frameScaleProd_pos.ne', Shape.k,
      card_X₀, h_rank, div_pow]
    rw [h_order]
    rfl
  have h_siegel : D.filling.siegelConst = (∏ v : D.Φ, D.frameMass v) *
      (D.shape.openCellConst ^ D.f * (√√|NumberField.discr D.E| ^ D.ϱ) ^ 2) /
        (((D.N ^ D.k) ^ D.f) ^ 2 * volÔ D.E ^ (D.ϱ + 1 + 2 * (D.ϱ * (D.ϱ + D.k)))) := by
    rw [D.prod_frameMass_mul_openCellConst_eq, mul_assoc, mul_div_cancel_right₀ _ (by positivity)]
  calc
    _ = Nat.card (D.filling.reducedImage besselH) * Fintype.card D.filling.Classes *
        (∏ v : D.Φ, D.frameMass v * Fintype.card (D.filling.besselSystem v).Index ^ 2 /
          (D.filling.besselSystem v).deg) * scale := by
      -- Insert the constants; the powers of N, of the volume and of the discriminant cancel.
      rw [prod_frameMass_mul_div_eq, scaledSiegelConst, card_reducedImage_besselS, h_siegel]
      simp only [scale, h_covolume, Shape.n]
      push_cast
      field
    _ ≤ (1 + D.b⁻¹ ^ 9) * D.filling.mainSecondMoment * scale :=
      mul_le_mul_of_nonneg_right D.card_mul_card_classes_mul_prod_le (by positivity)
    _ = _ := by ring

/-- Reduction at the chosen places maps the integral group `New.Filling.latticeStabilizer` of the
filling data onto the finite group `New.Filling.ResidueGL`. -/
lemma filling_reduction_surjective : Function.Surjective D.filling.reduction := by
  intro x
  -- A preimage is the lift of the residues of `x`, written in the lattice basis of the filling.
  let lift : stdLevel D.E D.shape.BesselIndex := liftResidue (w := D.chosenPlace) (Sigma.uncurry x)
  obtain ⟨h_mem, h_reduction⟩ := (D.filling_fits.reduction_finiteEquiv_iff lift.val x).mpr
    ⟨lift.property, reduceFamily_liftResidue (w := D.chosenPlace) (Sigma.uncurry x)⟩
  exact ⟨⟨D.filling_fits.finiteEquiv lift.val, h_mem⟩, h_reduction⟩

/-- The main second moment of the filling data, divided by their identity second moment, is
`d (N ^ k - 1) ^ f mass_k / (deg mass_r |Ū|)`. Here `d` and `deg` are the number of coordinates and
the degree of the tensor product of the Bessel systems, `mass_l` is the mass in rank `l`, and `|Ū|`
is the order `unipotentOrder` of the reduced unipotent group; `N` is the prime level, `k` and `r`
are the ranks of `X₀` and `Y₀`, and `f` is the number of infinite places. -/
lemma mainSecondMoment_div_identitySecondMoment_eq :
    D.filling.mainSecondMoment / D.filling.identitySecondMoment =
      Fintype.card D.filling.BesselCoord * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k /
        (D.filling.besselDegree * mass D.E D.r * D.filling.unipotentOrder) := by
  have h_rank : D.shape.r = D.r := D.card_rowIndex
  have card_image_ne_zero : (Nat.card (D.filling.reducedImage besselH) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h_dim : (D.filling.sourceDim : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_pos Fintype.card_pos Fintype.card_pos).ne'
  calc
    _ = D.filling.sourceDim / (Nat.card (D.filling.reducedImage besselS) *
        (D.filling.besselDegree * mass D.E D.r)) := by
      rw [mainSecondMoment, identitySecondMoment, h_rank]
      field_simp
    _ = _ := by
      rw [sourceDim, card_reducedImage_besselS, Nat.cast_mul, Nat.cast_mul,
        card_classes_eq_card_mul_pow_mul_mass]
      field_simp

/-- Up to a factor `b ^ (± k f / 4)`, the ratio of the main second moment to the identity second
moment is `(M b ^ (-15 / 2)) ^ (k f) d ((k - 1)!) ^ f`. Here `b` is the weight at the `b`-places of
the admissible data `D`, `M = p₀ p₁` is the principal level, `d` is the number of coordinates of the
tensor product of the Bessel systems, `k` is the rank of `X₀` and `f` is the number of infinite
places. The statement is for the logarithms, with `D.logB = log b`. -/
lemma abs_log_mainSecondMoment_div_identitySecondMoment_sub_le :
    |log (D.filling.mainSecondMoment / D.filling.identitySecondMoment) -
        (D.f * D.k * (log D.M - 15 / 2 * D.logB) +
          log (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f))| ≤
      D.f * D.k * D.logB / 4 := by
  -- Insert the sizes of the degree, of the ratio of the masses and of `N` into the formula for the
  -- ratio. All factorials cancel except `(k - 1)!`.
  have k_le_r : D.k ≤ D.r := D.k_le_r
  have k_pos : 0 < D.k := D.k_pos
  have two_le_N : 2 ≤ D.N := D.N_prime.two_le
  have pred_pos : (0 : ℝ) < D.N ^ D.k - 1 := D.pow_sub_one_pos
  have M_pos : 0 < D.M := pos D.M
  have deg_pos : 0 < D.filling.besselDegree := D.filling.besselDegree_pos
  have rd_pos : 0 < rootDiscr D.E := rootDiscr_pos D.E
  have dim_pos : 0 < Fintype.card D.filling.BesselCoord := card_pos
  have mass_k_pos : 0 < mass D.E D.k := mass_pos D.E D.k
  have mass_r_pos : 0 < mass D.E D.r := mass_pos D.E D.r
  have h_order : (D.filling.unipotentOrder : ℝ) =
      D.M ^ (D.f * (D.ϱ * (2 * D.k + 2 * D.ϱ + 1))) := by
    rw [unipotentOrder, Shape.k, card_X₀, Nat.cast_pow]
    rfl
  -- The range of `N`, and `N ^ k - 1` against `N ^ k`.
  have log_N : (D.f * D.k) • log D.N ∈
      Set.Icc ((D.f * D.k) • D.logLevelTarget) ((D.f * D.k) • (D.logLevelTarget + √D.logB)) :=
    (nsmul_right_mono _).mapsTo_Icc D.log_N_mem_Icc_logLevelTarget
  have log_pred_le : D.f • log (D.N ^ D.k - 1) ≤ D.f • log (D.N ^ D.k) :=
    nsmul_le_nsmul_right (log_le_log pred_pos (sub_one_lt _).le) _
  have log_ratio : D.f • log (D.N ^ D.k / (D.N ^ D.k - 1)) ≤ D.f • (2 / D.N : ℝ) :=
    nsmul_le_nsmul_right D.log_pow_div_pow_sub_one_le _
  have mul_mean_log_weight_eq :
      D.k * D.m * (D.f * ((∑ v : D.Φ, log (D.weight v)) / D.f)) =
      D.k * D.m * ∑ v : D.Φ, log (D.weight v) := by rw [mul_div_cancel₀ _ (ne _)]
  -- The degree and the ratio of the masses, with their factorials.
  have log_deg : log D.filling.besselDegree + D.f * ∑ l ∈ Ico (D.k - 1) D.r, log l.factorial ∈
      Set.Icc (∑ v : D.Φ, D.m * ((D.k - 1) * log (D.weight v)))
        (∑ v : D.Φ, D.m * (D.r * (log (D.weight v) + D.x⁻¹))) :=
    D.log_filling_besselDegree_mem_Icc
  have mass_ratio : |∑ i ∈ Ico D.k D.r, (log (mass D.E (i + 1)) - log (mass D.E i) -
      D.f * ((i + 1 / 2) * log D.rootDisc + log i.factorial - (i + 1) * log (2 * π)))| ≤
        log (1 + D.b⁻¹ ^ 9) - 2 * (D.f * (2 / D.N)) := D.abs_sum_log_mass_ratio_sub_le
  have first_factorial : D.f * ∑ i ∈ Ico (D.k - 1) D.k, log i.factorial =
      D.f * ∑ i ∈ {D.k - 1}, log i.factorial := by rw [D.k.Ico_pred_singleton k_pos]
  -- The remaining terms are small against `f k log b`.
  have rest_small :
      |D.f * (D.m - 1) * (D.ϱ * log (D.M * D.rootDisc / 2 / π) + log (√D.rootDisc / 2 / π)) -
      D.m * ∑ v : D.Φ, log (D.weight v)| ≤ D.f * D.k * D.logB / 4 - (log (1 + D.b⁻¹ ^ 9) +
        D.m * (D.m * ∑ v : D.Φ, log (D.weight v) + D.f * D.r * D.x⁻¹) + D.f * D.k * √D.logB) :=
    le_sub_iff_add_le.mpr D.le_of_hasLogBound
  rw [mainSecondMoment_div_identitySecondMoment_eq, h_order]
  simp only [eq_tsub_of_add_eq D.r_add_one] at *
  -- Expand the logarithms and the sums: `sum_range_sub` telescopes the mass terms, and
  -- `sum_range_id` evaluates the sums of the indices. What is left is linear in the logarithms, in
  -- the sums of `log i!` and in `log b`.
  simp (disch := intros; first | positivity | omega) only [log_div, log_mul, log_pow, log_sqrt,
    sum_add_distrib, sum_const, Finset.card_range, nsmul_eq_mul, sum_range_id,
    ← Nat.choose_two_right, card_univ, logLevelTarget, New.Parameters.logLevelMin,
    abs_le, ↓sum_Ico_eq_sub, Set.mem_Icc, sum_sub_distrib, ← mul_sum,
    sum_singleton, ← sum_mul, ← Nat.cast_sum _ (·), ↓sum_range_sub (log <| mass D.E ·)] at *
  push_cast (disch := apply D.nat_le_of_hasLogBound) [Nat.cast_choose_two, ← add_assoc,
    m_eq_two_mul_varrho_add_two] at *
  constructor <;> linarith

/-- For admissible data `D`, the ratio of the main second moment to the identity second moment lies
between `b ^ (11 k f)` and `(M / b ^ 6) ^ (k f)`. Here `b = D.b` is the weight at the `b`-places,
`M = p₀ p₁` is the principal level, `k` the rank of `X₀` and `f` the number of infinite places. -/
theorem mainSecondMoment_div_identitySecondMoment_mem_Icc :
    D.filling.mainSecondMoment / D.filling.identitySecondMoment ∈
      Set.Icc (D.b ^ (11 * (D.k * D.f))) ((D.M / D.b ^ 6) ^ (D.k * D.f)) := by
  -- The factor `d ((k - 1)!) ^ f` lies between `1` and `b ^ (5 k f / 4)`, and `b ^ 19 ≤ M`.
  have M_pos : (0 : ℝ) < D.M := Nat.cast_pos.2 (pos D.M)
  have ratio_pos : 0 < D.filling.mainSecondMoment / D.filling.identitySecondMoment := by
    have order_pos : 0 < D.filling.unipotentOrder := by simp [← card_reducedImage_besselU]
    rw [mainSecondMoment_div_identitySecondMoment_eq]
    positivity [D.filling.besselDegree_pos, mass_pos D.E D.k, mass_pos D.E D.r, D.pow_sub_one_pos]
  have log_factor_nonneg :
      0 ≤ log (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f) :=
    mod_cast log_natCast_nonneg (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f)
  have log_factor_le : log (Fintype.card D.filling.BesselCoord * (D.k - 1).factorial ^ D.f) ≤
      D.f * D.k * (5 / 4 * D.logB) := by
    refine (log_le_log (by positivity) D.card_besselCoord_mul_factorial_le).trans_eq ?_
    rw [log_pow, log_pow, log_pow, log_sqrt (sqrt_nonneg _), log_sqrt (exp_nonneg _), log_exp]
    linarith
  have level_ge : (D.f * D.k : ℝ) * (19 * D.logB) ≤ D.f * D.k * log D.M := by
    gcongr
    simpa using log_le_log (by positivity) (D.le_of_hasLogBound : D.b ^ 19 ≤ D.M)
  have one_le_logB : 1 ≤ D.logB := D.le_of_hasLogBound
  obtain ⟨h_lower, h_upper⟩ := abs_le.1 D.abs_log_mainSecondMoment_div_identitySecondMoment_sub_le
  constructor
  · rw [← log_le_log_iff (by positivity) ratio_pos, log_pow, log_exp]
    push_cast
    linarith
  · rw [← log_le_log_iff ratio_pos (by positivity), log_pow, log_div M_pos.ne' (by positivity),
      log_pow, log_exp]
    push_cast
    linarith

/-- The prime level `N` is at most `b ^ (60 n)`, where `n` is `D.shape.n`. -/
lemma N_le_pow : (D.N : ℝ) ≤ D.b ^ (60 * D.shape.n) := by
  have h_log : log D.N ≤ 30 * (2 * D.ϱ + 2) * D.logB := by
    simpa [D.m_eq_two_mul_varrho_add_two] using D.log_N_mem_Icc.2
  rw [← log_le_log_iff (Nat.cast_pos.2 D.N_prime.pos) (by positivity), log_pow, log_exp]
  push_cast
  linarith

/-- Replacing `N ^ k` by `N ^ k - 1` loses at most the factor `b`, as both `b` and `N ^ k` are at
least `2`. -/
lemma pow_div_le_pow_sub_one : (D.N : ℝ) ^ D.k / D.b ≤ D.N ^ D.k - 1 := by
  have two_le_b : 2 ≤ D.b := D.le_of_hasLogBound
  have two_le_pow : (2 : ℝ) ≤ D.N ^ D.k :=
    mod_cast D.N_prime.two_le.trans (Nat.le_self_pow D.k_pos.ne' _)
  calc (D.N : ℝ) ^ D.k / D.b ≤ D.N ^ D.k / 2 := by gcongr
    _ ≤ D.N ^ D.k - 1 := by linarith

/-- The filling data of `D` satisfy the standing hypotheses `New.Filling.IsAdmissible`: the level
is the preimage of the principal level, reduction is onto, and the size inequalities hold. -/
instance : D.filling.IsAdmissible := by
  have h_energy : 0 < D.filling.identitySecondMoment :=
    mul_pos (Nat.cast_pos.2 Nat.card_pos)
      (Nat.cast_pos.2 (Nat.mul_pos Fintype.card_pos Fintype.card_pos))
  have h_rank : D.shape.k = D.k := D.card_X₀
  have h_b : D.filling.b = D.b := rfl
  have h_varpi (v : InfinitePlace D.E) : ‖Φ v D.filling.deltaE.val‖ = v
    (P.deltaE D.towerExp).val := by
    rw [← InfinitePlace.apply, mk_Φ]
    rfl
  have h_kappa (v : InfinitePlace D.E) :
      |D.filling.realM v| = D.M * v (P.deltaE D.towerExp).val / (2 * π) := by
    rw [abs_realM_eq, ← h_varpi v]
    rfl
  exact
    { sourceLevel_eq := D.levelX_zero_eq_comap
      reduction_surjective := D.filling_reduction_surjective
      norm_deltaE_le := fun v ↦ by
                  rw [h_varpi v, h_b]
                  exact (D.apply_deltaE_mem_Icc v).2
      one_le_abs_realM := fun v ↦ D.le_of_hasLogBound.trans_eq (h_kappa v).symm
      abs_realM_le := fun v ↦ by
        rw [h_kappa v, h_b]
        exact D.le_of_hasLogBound
      N_le := D.N_le_pow
      mul_identitySecondMoment_le := by
                    rw [h_rank]
                    exact (le_div_iff₀ h_energy).1
                      D.mainSecondMoment_div_identitySecondMoment_mem_Icc.1
      mainSecondMoment_le := by
              rw [h_rank]
              exact (div_le_iff₀ h_energy).1 D.mainSecondMoment_div_identitySecondMoment_mem_Icc.2
      card_besselCoord_le := by
        rw [h_rank]
        exact D.card_besselCoord_le_pow
      le_relIndex := by
        rw [D.relIndex_latticeStabilizer, h_rank]
        exact pow_le_pow_left₀ (by positivity) D.pow_div_le_pow_sub_one _
      scaledSiegelConst_le := D.scaledSiegelConst_le }

end New.Data

end
