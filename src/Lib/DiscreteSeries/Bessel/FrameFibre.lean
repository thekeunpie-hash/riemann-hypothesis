module

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Topology.Separation.CompletelyRegular
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.General.Measure.FibreMeasure
public import Lib.DiscreteSeries.Haar.TotalMass
import Lib.Adelic.Adeles.AdditiveCharacter
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Lib.DiscreteSeries.Bessel.Basic
import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure

section
/-!
# The fibre measure of the Gram map

Let `J` be a hermitian involution of size `r` and `G = U(J)`. The Gram map sends a tuple of vectors,
the columns of a matrix `Y`, to the real coordinates (`New.gramCoords`) of the hermitian matrix
`T = Yᴴ J Y`.

* `New.LeGramFiber J E m`: the law of `g E` under the measure `m` on `G` is at most the fibre
  measure `dY / dT` on the tuples with the Gram matrix of `E`.
* `New.LeGramFiber.le_haar`, `New.leGramFiber_haar`: on the bases with Gram matrix `J`, which form
  the group `G`, the largest measure below the fibre measure is `vol U(r) / 2 ^ r` times the compact
  dual Haar measure `New.haarU J`, which is the `volume` of `U(J)`. Here `vol U(r)` is `New.volU r`.
* `New.LeGramFiber.append`, `New.LeGramFiber.append_vector`, `New.LeGramFiber.insert`: lower bounds
  for the fibre measure by choosing some vectors, moving them to a fixed position by an isometry,
  and choosing the others.

Notions from other files:
* `New.LeFibreMeasure μ ν π b l`: the measure `l` is at most the fibre measure of `μ / ν` for the
  map `π` over the point `b`.
* `New.gramCoords J Y`: the real coordinates of the hermitian matrix `Yᴴ J Y`; `New.hermOfReal t` is
  the hermitian matrix with coordinates `t`.
* `New.IsGramSection J V σ`: a differentiable section `σ` of the Gram map on the open set `V` of
  coordinates, with invertible values.
* `joinCols e (E₁, E₂)`, `joinCol e (E, v)`: the matrix with the columns of `E₁` and `E₂`, or of `E`
  and `v`, in the places given by `e`; `inclMatrix ℂ u` has the columns `e_{u k}`.

## Relation to the literature

Known result: the invariant measure `dY / dT` on tuples of vectors with a given Gram matrix. Source:
C. L. Siegel, Über die analytische Theorie der quadratischen Formen, Ann. of Math. 36 (1935).
-/

@[expose] public section

noncomputable section

namespace New

open Matrix MeasureTheory Measure Complex Fintype ENNReal Norms.L2Operator Filter Topology

variable {ι n n₁ n₂ : Type} [Fintype ι] [Fintype n] [Fintype n₁] [Fintype n₂]
  [DecidableEq ι] [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂]
  {J : Matrix ι ι ℂ} [IsHermitianInvolution J]

/-! ### The fibre measure over `J` -/

variable (J) in
/-- The image of the measure `m` under `g ↦ g E` is at most the fibre measure `dY / dT` of the Gram
map on the tuples with the Gram matrix of `E`. -/
def LeGramFiber (E : Matrix ι n ℂ) (m : Measure (U J)) : Prop :=
  LeFibreMeasure volume volume (gramCoords J) (gramCoords J E)
    (m.map fun g : U J ↦ g.val.val * E)

omit [IsHermitianInvolution J] in
/-- For a section `σ` of the Gram map on `V`, the factor `γ = Y σ(T)⁻¹` depends continuously on
the matrix `Y` with Gram coordinates `T` in `V`. -/
theorem IsGramSection.continuousOn_mul_inv {V : Set (Matrix ι ι ℝ)}
    {σ : Matrix ι ι ℝ → Matrix ι ι ℂ} (hσ : IsGramSection J V σ) :
    ContinuousOn (fun Y : Matrix ι ι ℂ ↦ Y * (σ (gramCoords J Y))⁻¹) (gramCoords J ⁻¹' V) := by
  intro Y hY
  have h_inv : ContinuousAt (fun Z : Matrix ι ι ℂ ↦ Z⁻¹) (σ (gramCoords J Y)) :=
    continuousAt_matrix_inv _
      (NormedRing.inverse_continuousAt ((isUnit_iff_isUnit_det _).1 (hσ.isUnit hY)).unit)
  have h_section :=
    (hσ.differentiableAt hY).continuousAt.comp (continuous_gramCoords J).continuousAt
  exact (continuousAt_id.mul (h_inv.comp_of_eq h_section rfl)).continuousWithinAt

/-- A measure `m` on `U(J)` that is at most the fibre measure `dY / dT` of the Gram map on the bases
with Gram matrix `J` is at most `vol U(r) / 2 ^ r` times the compact dual Haar measure, which is
the `volume` of `U(J)`. Here `r` is the size of `J` and `vol U(r) = volU r`. -/
theorem LeGramFiber.le_haar {m : Measure (U J)} (h_fibre : LeGramFiber J (1 : Matrix ι ι ℂ) m) :
    m ≤ ENNReal.ofReal (volU (card ι) / 2 ^ card ι) • volume := by
  -- Test against the indicator function of the open set `W` of the `γ σ(T)` with `γ` in an open
  -- set `O` and `T` in `V`; then use the outer regularity of Haar measure.
  obtain ⟨V, σ, hσ, h_base, hσ_base⟩ := exists_isGramSection J
  set c : ℝ≥0∞ := ENNReal.ofReal (volU (card ι) / 2 ^ card ι)
  have h_open (O : Set (U J)) (hO : IsOpen O) : m O ≤ c * volume O := by
    obtain ⟨O', hO', hO_eq⟩ := isClosedEmbedding_U.isInducing.isOpen_iff.1 hO
    let W : Set (Matrix ι ι ℂ) :=
      gramCoords J ⁻¹' V ∩ (fun Y ↦ Y * (σ (gramCoords J Y))⁻¹) ⁻¹' O'
    have hW : IsOpen W := hσ.continuousOn_mul_inv.isOpen_inter_preimage
      (hσ.isOpen.preimage (continuous_gramCoords J)) hO'
    let K : Matrix ι ι ℂ → ℝ≥0∞ := W.indicator fun _ ↦ 1
    have hK : Measurable K := measurable_const.indicator hW.measurableSet
    have h_slice (μ : Measure (U J)) (t : Matrix ι ι ℝ) (ht : t ∈ V) :
        ∫⁻ g : U J, K (g.val.val * σ t) ∂μ = μ O := by
      have h_pre : (fun g : U J ↦ g.val.val * σ t) ⁻¹' W = O := Set.ext fun g ↦ by
        simp [W, ← hO_eq, gramCoords_U_mul, hσ.gramCoords_eq ht, ht,
          mul_nonsing_inv_cancel_right _ _ ((isUnit_iff_isUnit_det _).1 (hσ.isUnit ht))]
      rw [← lintegral_indicator_one hO.measurableSet, ← h_pre]
      exact lintegral_congr fun g ↦ (Set.indicator_comp_right _).symm
    calc m O = ∫⁻ g : U J, K (g.val.val * 1) ∂m := by rw [← h_slice m _ h_base, hσ_base]
      _ = ∫⁻ Y, K Y ∂m.map (fun g : U J ↦ g.val.val * 1) := (lintegral_map hK (by fun_prop)).symm
      _ ≤ c * volume O := by
          refine h_fibre _ (hW.lowerSemicontinuous_indicator zero_le_one) _ ?_
          filter_upwards [eventually_smallSets_subset.2 (hσ.isOpen.mem_nhds h_base)]
            with S hS hS_open
          rw [(hσ.mono hS_open hS).lintegral_eq hK,
            setLIntegral_congr_fun hS_open.measurableSet fun t ht ↦ h_slice volume t (hS ht),
            setLIntegral_const, mul_assoc]
  have h_regular : (c • (volume : Measure (U J))).OuterRegular := .smul _ ofReal_ne_top
  refine Measure.le_iff.2 fun A _ ↦ ?_
  rw [A.measure_eq_iInf_isOpen (c • volume)]
  exact le_iInf₂ fun O hAO ↦ le_iInf fun hO ↦ (measure_mono hAO).trans (h_open O hO)

/-- The measure `vol U(r) / 2 ^ r` times the compact dual Haar measure, which is the `volume` of
`U(J)`, is at most the fibre measure `dY / dT` of the Gram map on the bases with Gram matrix `J`
(`New.LeGramFiber`). Here `r` is the size of `J` and `vol U(r) = volU r`. -/
theorem leGramFiber_haar :
    LeGramFiber J (1 : Matrix ι ι ℂ) (ENNReal.ofReal (volU (card ι) / 2 ^ card ι) • volume) := by
  -- The products `g σ(T)` are coordinates near the bases with Gram matrix `J`, and the volume in
  -- them is `c` times the product of the Haar measure and `dT`.
  obtain ⟨V, σ, hσ, h_base, hσ_base⟩ := exists_isGramSection J
  set c : ℝ≥0∞ := ENNReal.ofReal (volU (card ι) / 2 ^ card ι)
  set T : Matrix ι ι ℝ := gramCoords J (1 : Matrix ι ι ℂ)
  have σ_meas : Measurable σ := hσ.measurable
  have h_gram : ∀ t ∈ V, ∀ g : U J, gramCoords J (g.val.val * σ t) = t := fun t ht g ↦
    (gramCoords_U_mul g _).trans (hσ.gramCoords_eq ht)
  have σ_cont : ContinuousAt σ T := (hσ.differentiableAt h_base).continuousAt
  have h_fibre : LeFibreMeasure volume volume (gramCoords J) T
      ((volume.withDensity fun _ : U J ↦ c).map fun g : U J ↦ g.val.val * σ T) := by
    refine .of_coordinates (ψ := fun t (g : U J) ↦ g.val.val * σ t) (w := fun _ _ ↦ c)
      (by fun_prop) (by fun_prop) measurable_const (hσ.isOpen.mem_nhds h_base)
      (fun t ht ↦ .of_forall fun g _ ↦ h_gram t ht g)
      (.of_forall fun g ↦ ⟨by fun_prop, continuousAt_const⟩) fun K hK ↦ ?_
    simp only [lintegral_const_mul' c _ ofReal_ne_top]
    exact (hσ.lintegral_eq hK).ge.trans (setLIntegral_le_lintegral _ _)
  rwa [withDensity_const, hσ_base] at h_fibre

/-! ### Choosing vectors in turn -/

omit [DecidableEq ι] [DecidableEq n] in
theorem sum_norm_sq_eq_re_trace (Y : Matrix ι n ℂ) :
    ∑ a : ι, ∑ b : n, ‖Y a b‖ ^ 2 = (Yᴴ * Y).trace.re := by
  simp [trace, Matrix.mul_apply, Finset.sum_comm (s := (Finset.univ : Finset ι)), conj_mul',
    ← Complex.ofReal_pow]

omit [DecidableEq ι] in
/-- If the columns of `D` and `R` together form an orthonormal basis of `ℂ ^ ι`, then
`(M, x) ↦ D M + R x` preserves the volume. -/
theorem measurePreserving_mul_add_mul {D : Matrix ι n₁ ℂ} {R : Matrix ι n₂ ℂ} (hD : Dᴴ * D = 1)
    (hR : Rᴴ * R = 1) (hDR : Dᴴ * R = 0) (h_card : card n₁ + card n₂ = card ι) :
    MeasurePreserving fun p : Matrix n₁ n ℂ × Matrix n₂ n ℂ ↦ D * p.1 + R * p.2 := by
  have hRD : Rᴴ * D = 0 := by simpa using congrArg conjTranspose hDR
  let f : (Matrix n₁ n ℂ × Matrix n₂ n ℂ) →ₗ[ℝ] Matrix ι n ℂ :=
    (mulLeftLinearMap n ℝ D).coprod (mulLeftLinearMap n ℝ R)
  have f_inj : Function.Injective f :=
    Function.LeftInverse.injective (g := fun y ↦ (Dᴴ * y, Rᴴ * y)) fun p ↦ by
      simp [f, Matrix.mul_add, ← Matrix.mul_assoc, hD, hR, hDR, hRD]
  have h_gram (p : Matrix n₁ n ℂ × Matrix n₂ n ℂ) : (f p)ᴴ * f p = p.1ᴴ * p.1 + p.2ᴴ * p.2 := by
    simp [f, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Dᴴ,
      ← Matrix.mul_assoc Rᴴ, hD, hR, hDR, hRD]
  have : IsAddHaarMeasure (volume : Measure (Matrix n₁ n ℂ × Matrix n₂ n ℂ)) :=
    prod.instIsAddHaarMeasure _ _
  refine HasGaussianIntegral.measurePreserving (f.linearEquivOfInjective f_inj ?_) fun p ↦ ?_
  · simp [Module.finrank_matrix, ← h_card, add_mul]
  · simp [sum_norm_sq_eq_re_trace, h_gram]

omit [Fintype n] in
theorem gramCoords_eq_iff {Y : Matrix ι n ℂ} {t : Matrix n n ℝ} :
    gramCoords J Y = t ↔ Yᴴ * J * Y = hermOfReal t := by
  refine ⟨fun h ↦ by rw [← h, hermOfReal_gramCoords IsHermitianInvolution.isHermitian], fun h ↦ ?_⟩
  rw [gramCoords, h, skewCoords_I_smul_hermOfReal]

/-- Coordinates adapted to the Gram products with `E`. If the columns of `J E` and `R` form an
orthonormal basis, then `(M, x) ↦ J E M + R x` preserves the volume. -/
theorem measurePreserving_mul_mul_add_mul {E : Matrix ι n₁ ℂ} {R : Matrix ι n₂ ℂ} (hE : Eᴴ * E = 1)
    (hR : Rᴴ * R = 1) (h_orth : Eᴴ * J * R = 0) (h_card : card n₁ + card n₂ = card ι) :
    MeasurePreserving fun p : Matrix n₁ n ℂ × Matrix n₂ n ℂ ↦ J * E * p.1 + R * p.2 := by
  have h_adj : (J * E)ᴴ = Eᴴ * J := by rw [conjTranspose_mul, IsHermitianInvolution.isHermitian.eq]
  refine measurePreserving_mul_add_mul ?_ hR (by rwa [h_adj]) h_card
  simp [h_adj, Matrix.mul_assoc, ← Matrix.mul_assoc J, IsHermitianInvolution.mul_self, hE]

/-- The fibre measure of the products with `E`. Let `J` be a hermitian involution, and suppose the
columns of `J E` and `R` form an orthonormal basis. Then the image `l` of Lebesgue measure under
`x ↦ J E M + R x` is at most the fibre measure of `y ↦ Eᴴ J y` over `M` (`New.LeFibreMeasure`). That
is, take a lower semicontinuous `K ≥ 0` with `∫_{Eᴴ J y ∈ S} K dy ≤ C·vol(S)` for all open `S` near
`M`; then `∫ K dl ≤ C`. -/
theorem leFiberMeasure_conjTranspose_mul_mul {E : Matrix ι n₁ ℂ} {R : Matrix ι n₂ ℂ}
    (hE : Eᴴ * E = 1)
    (hR : Rᴴ * R = 1) (h_orth : Eᴴ * J * R = 0) (h_card : card n₁ + card n₂ = card ι)
    (M : Matrix n₁ n ℂ) :
    LeFibreMeasure volume volume (fun y : Matrix ι n ℂ ↦ Eᴴ * J * y) M
      (volume.map fun x : Matrix n₂ n ℂ ↦ J * E * M + R * x) := by
  have h_proj (t : Matrix n₁ n ℂ) (x : Matrix n₂ n ℂ) : Eᴴ * J * (J * E * t + R * x) = t := by
    simp [Matrix.mul_add, ← Matrix.mul_assoc, h_orth, Matrix.mul_assoc _ J J,
      IsHermitianInvolution.mul_self, hE]
  exact .of_measurePreserving (measurePreserving_mul_mul_add_mul hE hR h_orth h_card)
    (by fun_prop) h_proj fun _ ↦ Continuous.continuousAt (by fun_prop)

omit [DecidableEq n] [DecidableEq n₁] in
/-- Choosing `g` with law `m` and completing `g E₁` by further columns with the Lebesgue measure, in
the places given by `e` (`joinCols`), is the same as completing `E₁` first and then moving all
columns by `g`. -/
theorem map_joinCols_prod_volume (e : n₁ ⊕ n₂ ≃ n) (E₁ : Matrix ι n₁ ℂ) (m : Measure (U J))
    [SFinite m] :
    (volume.prod (m.map fun g : U J ↦ g.val.val * E₁)).map
        (fun p : Matrix ι n₂ ℂ × Matrix ι n₁ ℂ ↦ joinCols e p.swap) =
      (m.prod volume).map fun p : U J × Matrix ι n₂ ℂ ↦ p.1.val.val * joinCols e (E₁, p.2) := by
  refine ext_of_lintegral _ fun K hK ↦ ?_
  rw [lintegral_map hK (by fun_prop), lintegral_prod_symm' _ (by fun_prop),
    lintegral_map (by fun_prop) (by fun_prop), lintegral_map hK (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  -- For fixed `g`, substitute `g y` for the further columns `y`.
  refine lintegral_congr fun g ↦ ?_
  have h_subst : ∫⁻ y : Matrix ι n₂ ℂ, K (joinCols e (g.val.val * E₁, g.val.val * y)) =
      ∫⁻ y : Matrix ι n₂ ℂ, K (joinCols e (g.val.val * E₁, y)) :=
    (measurePreserving_U_mul g).lintegral_comp
      (f := fun y : Matrix ι n₂ ℂ ↦ K (joinCols e (g.val.val * E₁, y))) (by fun_prop)
  simp only [mul_joinCols, Prod.swap_prod_mk, h_subst]

omit [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂] [IsHermitianInvolution J] in
/-- Let `E = joinCols e (E₁, E₂)` have the columns of `E₁` and `E₂`. If `m'` is carried by the
elements that fix `E₁`, then the law of `g (E₁, g' E₂)` under `m × m'` is the law of `g E` under
the convolution `m ∗ₘ m'`. -/
theorem map_mul_joinCols_prod_eq_map_mconv {E : Matrix ι n ℂ} {E₁ : Matrix ι n₁ ℂ}
    {E₂ : Matrix ι n₂ ℂ} (e : n₁ ⊕ n₂ ≃ n) (hE : joinCols e (E₁, E₂) = E) {m m' : Measure (U J)}
    [SFinite m'] (h_fix : ∀ᵐ g : U J ∂m', g.val.val * E₁ = E₁) :
    (m.prod (m'.map fun g : U J ↦ g.val.val * E₂)).map
        (fun p : U J × Matrix ι n₂ ℂ ↦ p.1.val.val * joinCols e (E₁, p.2)) =
      (m ∗ₘ m').map fun g : U J ↦ g.val.val * E := by
  have h_prod : m.prod (m'.map fun g : U J ↦ g.val.val * E₂) =
      (m.prod m').map (Prod.map id fun g : U J ↦ g.val.val * E₂) := by
    rw [← map_prod_map _ _ measurable_id (by fun_prop), m.map_id]
  have h_ae : ∀ᵐ p : U J × U J ∂m.prod m',
      p.1.val.val * joinCols e (E₁, p.2.val.val * E₂) = (p.1 * p.2).val.val * E :=
    (quasiMeasurePreserving_snd.ae h_fix).mono fun p hp ↦ by
      simp [← hE, mul_joinCols, Matrix.mul_assoc, hp]
  rw [h_prod, Measure.map_map (by fun_prop) (by fun_prop), mconv,
    Measure.map_map (by fun_prop) measurable_mul]
  exact map_congr h_ae

/-- Choosing vectors in turn. Let the tuple `E = joinCols e (E₁, E₂)` consist of `E₁` and `E₂`, in
the places given by `e`. Suppose that the law of `g E₁` under `m` is at most the fibre measure of
the Gram map (`New.LeGramFiber`), that `m'` is carried by the elements that fix `E₁`, and that the
law of `g' E₂` under `m'` is at most the fibre measure (`New.LeFibreMeasure`) of the map that sends
`y` to the products `E₁ᴴ J y` and to the coordinates `gramCoords J y` of its Gram matrix. Then the
law of `g g' E` is at most the fibre measure of the Gram map over the Gram matrix of `E`. -/
theorem LeGramFiber.append {E : Matrix ι n ℂ} {E₁ : Matrix ι n₁ ℂ} {E₂ : Matrix ι n₂ ℂ}
    (e : n₁ ⊕ n₂ ≃ n) (hE : joinCols e (E₁, E₂) = E) {m m' : Measure (U J)} [SFinite m]
    [SFinite m'] (h_first : LeGramFiber J E₁ m)
    (h_rest : LeFibreMeasure volume volume
      (fun y : Matrix ι n₂ ℂ ↦ (E₁ᴴ * J * y, gramCoords J y)) (E₁ᴴ * J * E₂, gramCoords J E₂)
      (m'.map fun g : U J ↦ g.val.val * E₂))
    (h_fix : ∀ᵐ g : U J ∂m', g.val.val * E₁ = E₁) :
    LeGramFiber J E (m ∗ₘ m') := by
  -- The Gram matrix consists of `π₁`, the Gram matrix of the first columns, and of `π₂`, the
  -- other two blocks. Take the fibre of `π₁`, and on it the fibre of `π₂`.
  let split (Y : Matrix ι n ℂ) : Matrix ι n₁ ℂ × Matrix ι n₂ ℂ := (joinCols e).symm Y
  let π₁ (Y : Matrix ι n ℂ) : Matrix n₁ n₁ ℝ := gramCoords J (split Y).1
  let π₂ (Y : Matrix ι n ℂ) : Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ :=
    ((split Y).1ᴴ * J * (split Y).2, gramCoords J (split Y).2)
  let move (p : U J × Matrix ι n₂ ℂ) : Matrix ι n ℂ := p.1.val.val * joinCols e (E₁, p.2)
  have split_cont : Continuous split := (joinCols e).symm.continuous_of_finiteDimensional
  have π₂_cont : Continuous π₂ := by fun_prop
  have h₁ : LeFibreMeasure volume volume π₁ (gramCoords J E₁) ((m.prod volume).map move) := by
    have join_vol : MeasurePreserving (fun p : Matrix ι n₂ ℂ × Matrix ι n₁ ℂ ↦ joinCols e p.swap)
        (volume.prod volume) := (measurePreserving_joinCols e).comp measurePreserving_swap
    rw [← map_joinCols_prod_volume, ← join_vol.map_eq]
    exact h_first.map_prod join_vol.measurable (fun y ↦ by fun_prop) (by fun_prop)
      (by simp [π₁, split])
  have h_law : (m.prod (m'.map fun g : U J ↦ g.val.val * E₂)).map move =
      (m ∗ₘ m').map fun g : U J ↦ g.val.val * E := map_mul_joinCols_prod_eq_map_mconv e hE h_fix
  -- The products in `π₂` do not change when all columns are moved by `g`.
  have h₂ : LeFibreMeasure ((m.prod volume).map move) volume π₂ (E₁ᴴ * J * E₂, gramCoords J E₂)
      ((m ∗ₘ m').map fun g : U J ↦ g.val.val * E) := by
    rw [← h_law]
    refine h_rest.map_prod (by fun_prop) (fun g ↦ by fun_prop) π₂_cont.measurable fun g y ↦ ?_
    simp only [π₂, split, move, mul_joinCols, LinearEquiv.symm_apply_apply, gramCoords_U_mul,
      U.gram_invariant]
  obtain ⟨φ, φ_vol, φ_apply⟩ :
      ∃ φ : Matrix n n ℝ ≃ₜ Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ,
      MeasurePreserving φ ∧ ∀ t : Matrix n n ℝ, φ t = (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
        (hermOfReal t).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr),
        t.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) :=
    exists_measurePreserving_hermBlocks e
  have φ_gram (Y : Matrix ι n ℂ) : (π₁ Y, π₂ Y) = φ (gramCoords J Y) := by
    rw [φ_apply, hermOfReal_gramCoords IsHermitianInvolution.isHermitian]
    simp [π₁, π₂, split, joinCols, gramCoords, skewCoords, Matrix.mul_apply, ← ext_iff]
  have h_base : (gramCoords J E₁, E₁ᴴ * J * E₂, gramCoords J E₂) = φ (gramCoords J E) := by
    simp only [← φ_gram, ← hE, π₁, π₂, split, LinearEquiv.symm_apply_apply]
  have h_both : LeFibreMeasure volume (volume.prod volume) (fun Y ↦ φ (gramCoords J Y))
      (φ (gramCoords J E)) ((m ∗ₘ m').map fun g : U J ↦ g.val.val * E) := by
    simpa only [h_base, φ_gram] using h₁.trans h₂ π₂_cont
  have : BorelSpace (Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ) := Prod.borelSpace
  simpa only [LeGramFiber, Function.comp_def, φ.symm_apply_apply] using
    h_both.comp_homeomorph φ.symm (φ_vol.symm φ.toMeasurableEquiv)

/-- Choosing one more vector `v`: the case of `New.LeGramFiber.append` in which the second tuple
has one member. Suppose that the law of `g E` under `m` is at most the fibre measure of the Gram
map, that `m'` is carried by the elements that fix `E`, and that the law of `g v` under `m'` is at
most the fibre measure of the map that sends `y` to the vector `Eᴴ J y` and the number `y* J y`.
Then the law of `g (E, v)` under `m ∗ m'` is at most the fibre measure of the Gram map, `(E, v)`
having its columns in the places given by `e`. -/
theorem LeGramFiber.append_vector {E : Matrix ι n₁ ℂ} {v : ι → ℂ} (e : n₁ ⊕ Unit ≃ n)
    {m m' : Measure (U J)} [SFinite m] [SFinite m'] (h_first : LeGramFiber J E m)
    (h_next : LeFibreMeasure volume volume
      (fun y : ι → ℂ ↦ (Eᴴ *ᵥ J *ᵥ y, (star y ⬝ᵥ J *ᵥ y).re)) (Eᴴ *ᵥ J *ᵥ v, (star v ⬝ᵥ J *ᵥ v).re)
      (m'.map fun g : U J ↦ g.val.val *ᵥ v))
    (h_fix : ∀ᵐ g : U J ∂m', g.val.val * E = E) :
    LeGramFiber J (joinCol e (E, v)) (m ∗ₘ m') := by
  -- Carry `h_next` from vectors to matrices with one column (`toCol`), and from pairs of a vector
  -- and a number to the two blocks of the Gram matrix (`toCorner`).
  have h_col (A : Matrix ι ι ℂ) (y : ι → ℂ) : A * toCol ι ℂ y = toCol ι ℂ (A *ᵥ y) := rfl
  have h_comm (y : ι → ℂ) : toCorner n₁ (Eᴴ *ᵥ J *ᵥ y, (star y ⬝ᵥ J *ᵥ y).re) =
      (Eᴴ * J * toCol ι ℂ y, gramCoords J (toCol ι ℂ y)) := by
    have h_real : (star y ⬝ᵥ J *ᵥ y).im = 0 :=
      IsHermitianInvolution.isHermitian.im_star_dotProduct_mulVec_self y
    have h_norm : ((toCol ι ℂ y)ᴴ * J * toCol ι ℂ y) () () = star y ⬝ᵥ J *ᵥ y := by
      rw [Matrix.mul_assoc, h_col]
      simp [Matrix.mul_apply, dotProduct]
    rw [toCorner_apply, mulVec_mulVec]
    refine Prod.ext rfl (Matrix.ext fun _ _ ↦ ?_)
    simp [gramCoords, skewCoords, h_norm, h_real]
  have h_moved : LeFibreMeasure volume volume
      ((fun y ↦ (Eᴴ * J * y, gramCoords J y)) ∘ toCol ι ℂ)
      (Eᴴ * J * toCol ι ℂ v, gramCoords J (toCol ι ℂ v)) (m'.map fun g ↦ g.val.val *ᵥ v) := by
    rw [← h_comm]
    exact (h_next.comp_homeomorph _ measurePreserving_toCorner).congr (.of_forall h_comm)
  refine h_first.append (E₂ := toCol ι ℂ v) e rfl ?_ h_fix
  simpa (disch := fun_prop) only [(measurePreserving_toCol ι ℂ).map_eq, Measure.map_map, h_col,
    Function.comp_def] using h_moved.map (by fun_prop) (by fun_prop) (by fun_prop)

omit [IsHermitianInvolution J] in
/-- For the empty tuple `E`, the law of `g E` under the unit mass at the identity of `U(J)` is at
most the fibre measure of the Gram map. -/
theorem leGramFiber_dirac [IsEmpty n] (E : Matrix ι n ℂ) : LeGramFiber J E (dirac 1) := by
  have h_vol : MeasurePreserving (fun _ : Matrix n n ℝ × Unit ↦ E) (volume.prod (dirac ())) :=
    ⟨measurable_const,
      by simp [volume_eq_dirac_of_isEmpty E, volume_eq_dirac_of_isEmpty (gramCoords J E)]⟩
  have h_fibre : LeFibreMeasure volume volume (gramCoords J) (gramCoords J E)
      ((dirac () : Measure Unit).map fun _ ↦ E) :=
    .of_measurePreserving h_vol (by fun_prop) (fun _ _ ↦ Subsingleton.elim _ _)
      fun _ ↦ continuousAt_const
  simpa [LeGramFiber] using h_fibre

/-- The bijection from `p` and one more point onto `q = p ∪ {j}`, for `j` outside `p`: the point
goes to `j`. -/
def subtypeInsertEquiv {α : Type} {p q : α → Prop} {j : α} (hj : ¬p j)
    (hq : ∀ i : α, q i ↔ p i ∨ i = j) : Subtype p ⊕ Unit ≃ Subtype q :=
  .ofBijective (Sum.elim (fun i ↦ ⟨i, (hq i).2 (.inl i.2)⟩) fun _ ↦ ⟨j, (hq j).2 (.inr rfl)⟩) <| by
    simp only [Function.Bijective, Function.Injective, Function.Surjective, Sum.forall,
      Sum.exists, Subtype.forall, Subtype.exists, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq]
    grind

/-- Choosing one more basis vector, `inclMatrix ℂ Subtype.val` being the matrix with the columns
`e_i` for the `i` in a set of indices. Let `p` be a set of indices, `j` an index outside it and
`q = p ∪ {j}`. Let the law of `g (e_i)_{i ∈ p}` under `m` be at most the fibre measure of the Gram
map. Let `m'` be carried by the elements that fix these `e_i`, and let the law of `g e_j` under
`m'` be at most the fibre measure of the `J`-products of a vector `y` with them and with itself.
Then the law of `g (e_i)_{i ∈ q}` under `m ∗ m'` is at most the fibre measure of the Gram map. -/
theorem LeGramFiber.insert {p q : ι → Prop} [DecidablePred p] [DecidablePred q] {j : ι}
    (hj : ¬p j) (hq : ∀ i : ι, q i ↔ p i ∨ i = j) {m m' : Measure (U J)} [SFinite m] [SFinite m']
    (h_first : LeGramFiber J (inclMatrix ℂ (Subtype.val : Subtype p → ι)) m)
    (h_next : LeFibreMeasure volume volume
      (fun y : ι → ℂ ↦ (fun i : Subtype p ↦ (J *ᵥ y) i, (star y ⬝ᵥ J *ᵥ y).re))
      (fun i : Subtype p ↦ J i j, (J j j).re) (m'.map fun g : U J ↦ g.val.val *ᵥ Pi.single j 1))
    (h_fix : ∀ᵐ g : U J ∂m', ∀ i k : ι, p k → g.val.val i k = (1 : Matrix ι ι ℂ) i k) :
    LeGramFiber J (inclMatrix ℂ (Subtype.val : Subtype q → ι)) (m ∗ₘ m') := by
  set E : Matrix ι (Subtype p) ℂ := inclMatrix ℂ Subtype.val
  have h_join :
      joinCol (subtypeInsertEquiv hj hq) (E, Pi.single j 1) = inclMatrix ℂ Subtype.val := by
    ext i k
    obtain ⟨k | ⟨⟩, rfl⟩ := (subtypeInsertEquiv hj hq).surjective k
    · exact joinCol_inl ..
    · exact (joinCol_inr ..).trans (Pi.single_apply j 1 i)
  have h_products (y : ι → ℂ) : Eᴴ *ᵥ y = fun i : Subtype p ↦ y i :=
    funext fun i ↦ by simp [E, inclMatrix, mulVec, dotProduct, Matrix.one_apply]
  rw [← h_join]
  refine h_first.append_vector _ ?_ (h_fix.mono fun g hg ↦
    (mul_inclMatrix g.val.val _).trans (Matrix.ext fun i k ↦ hg i k k.property))
  -- `mulVec_mulVec` would merge `Eᴴ` and `J` before `h_products` applies.
  simpa [h_products, -mulVec_mulVec] using h_next

end New

end
end
end

/-!
# Haar measure of G₁ and the fibre measure on frames

The group `New.Shape.G₁` is the unitary group of the form `New.Shape.J₁`, of rank `r`, with basis
`e_a`, `x_i`, `z`, `e*_a`: there are `ϱ` hyperbolic pairs `e_a, e*_a`, the span `X₀` of the `x_i` is
positive definite of rank `k`, and `z` is negative. The frame is `e_0, …, e_{ϱ-1}, z`, and 𝖴⁰ is the
unipotent group `New.Shape.Form.besselU0` that fixes it. The file compares Haar measure of G₁ with
the fibre measure of the Gram map on tuples of vectors.

Notions from other files:
* `New.LeGramFiber J E m` says that the image of `m` under `g ↦ g E` is at most the fibre measure of
  the Gram map `E' ↦ E'ᴴ J E'` over the Gram matrix of `E`.
* `New.LeFibreMeasure μ ν π b l` says that `l` is at most the fibre measure `dμ / dν` of `π` over
  `b`.
* `New.volU j` is `vol U(j)`; the measure `volume` on G₁ is Haar measure, normalised through the
  compact dual, and on the unitary group H = U(X₀) it is the Haar measure of mass one.

Main results:
* `New.LeGramFiber.mconv_embedH_le`: tuples with the Gram matrix of the basis vectors outside `X₀`.
  These vectors have fixer `H = U(X₀)`; if their image under `m` is below the fibre measure, then
  `m ∗ dh` is at most `vol U(r) / (2 ^ (r - k) vol U(k))` times Haar measure of G₁.
* `New.RealPlace.lintegral_eq_unipotent_coords`: Lebesgue measure on the `ϱ`-tuples dual to
  `e_0, …, e_{ϱ-1}` and orthogonal to `z`, in coordinates given by 𝖴⁰ and the Gram matrix.
* `New.LeGramFiber.mconv_fixerHaar_le`: frames. The standard frame has fixer 𝖴⁰ H, with the measure
  `ds = New.RealPlace.fixerHaar`; if the image of the frame under `m` is below the fibre measure,
  then `m ∗ ds` is at most `vol U(r) / (2 ^ (ϱ + 1) vol U(k))` times Haar measure of G₁.

## Relation to the literature

Known result: the fibre measure of the Gram map on tuples of vectors, in terms of Haar measure of
the unitary group. The file proves the inequality that is used. Siegel, Über die analytische Theorie
der quadratischen Formen, Ann. of Math. 36 (1935).
-/

@[expose] public section

noncomputable section

namespace New.RealPlace

open Matrix MeasureTheory Measure Complex Fintype ENNReal Norms.L2Operator

variable {𝔰 : Shape} {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix `J₁` of the form fixes the basis vectors `x_i` of `X₀`. -/
theorem J₁_mul_definiteCols : 𝔰.J₁ * 𝔰.definiteCols = 𝔰.definiteCols := by
  simp [J₁_eq, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc,
    conjTranspose_definiteCols_mul_self,
    inclMatrix_gram_eq_zero]

omit [DecidableEq n] in
/-- Let `f` be a measurable map to the unitary group `G₁` whose values all fix the tuple of
vectors given by the columns of `E`. Then almost every element for the image of `μ` under `f`
fixes this tuple. -/
theorem ae_map_mul_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → 𝔰.G₁}
    {E : Matrix 𝔰.BesselIndex n ℂ} (hf : Measurable f) (h_fix : ∀ x : X, (f x).val.val * E = E) :
    ∀ᵐ g : 𝔰.G₁ ∂μ.map f, g.val.val * E = E :=
  (ae_map_iff hf.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)).2
    (.of_forall h_fix)

/-! ### Tuples whose complement is definite -/

/-- The definite case, with `k` the dimension of `X₀`. On `k`-tuples of vectors of `X₀`, the image
under `h ↦ h (x_i)` of `vol U(k) / 2 ^ k` times the Haar probability measure of `H = U(X₀)`,
embedded in `G₁` by `embedH`, is at most the fibre measure (`LeFibreMeasure`) of the Gram map
`gramCoords` over the Gram matrix of the `x_i`, the columns of `definiteCols`. Here `volU k` is
`vol U(k)`. -/
theorem leFiberMeasure_definiteCols :
    LeFibreMeasure (volume.map fun x : Matrix 𝔰.κ 𝔰.κ ℂ ↦ 𝔰.definiteCols * x) volume
      (gramCoords 𝔰.J₁) (gramCoords 𝔰.J₁ 𝔰.definiteCols)
      ((ENNReal.ofReal (volU 𝔰.k / 2 ^ 𝔰.k) • volume.map embedH).map
        fun g : 𝔰.G₁ ↦ g.val.val * 𝔰.definiteCols) := by
  -- Transport the statement for `U(k)` along `x ↦ definiteCols * x`, which preserves Gram matrices.
  let φ : Matrix 𝔰.κ 𝔰.κ ℂ → Matrix 𝔰.BesselIndex 𝔰.κ ℂ := fun x ↦ 𝔰.definiteCols * x
  have h_gram (x : Matrix 𝔰.κ 𝔰.κ ℂ) : gramCoords 𝔰.J₁ (φ x) = gramCoords 1 x := by
    rw [gramCoords, gram_mul, Matrix.mul_assoc _ 𝔰.J₁, J₁_mul_definiteCols,
      conjTranspose_definiteCols_mul_self,
      gramCoords]
  have h_haar : LeFibreMeasure volume volume (gramCoords 𝔰.J₁ ∘ φ) (gramCoords 𝔰.J₁ (φ 1))
      ((ENNReal.ofReal (volU 𝔰.k / 2 ^ 𝔰.k) • volume).map
        fun h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦ h.val.val * (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) := by
    simpa only [LeGramFiber, Function.comp_def, h_gram] using leGramFiber_haar (J := 1)
  simpa (disch := fun_prop) only [φ, ← Measure.map_smul, Measure.map_map, Function.comp_def,
    Matrix.mul_one, embedH_mul_definiteCols] using
    h_haar.map (φ := φ) (by fun_prop) (by fun_prop) (by fun_prop)

/-- The fibre measure on tuples with a definite complement. `G₁` is the unitary group of the
hermitian form with Gram matrix `J₁`: ϱ hyperbolic pairs, the identity on `X₀` (basis `x_i`,
`i ∈ κ`) and `h(z, z) = −1`. Let `e` enumerate the basis, indexed by `BesselIndex`, with the `x_i`
last (`indexX₀ i` is the index of `x_i`), and let `E` be the tuple of the other `r - k = 2 ϱ + 1`
basis vectors. Suppose the image of `m` under `g ↦ g E` is at most the fibre measure `dY / dT` of
the Gram map over the Gram matrix of `E` (`LeGramFiber`). Then the convolution of `m` with the Haar
probability measure of `H = U(X₀)`, embedded in `G₁` by `embedH`, is at most
`vol U(r) / (vol U(k) 2 ^ (2 ϱ + 1))` times Haar measure of `G₁`, normalised through its compact
dual. Here `inclMatrix ℂ f` has the basis vectors with indices `f j` as columns and `volU j` is
`vol U(j)`. -/
theorem _root_.New.LeGramFiber.mconv_embedH_le (e : n ⊕ 𝔰.κ ≃ 𝔰.BesselIndex)
    (he : ∀ i : 𝔰.κ, e (Sum.inr i) = 𝔰.indexX₀ i) {m : Measure 𝔰.G₁} [SFinite m]
    (hm : LeGramFiber 𝔰.J₁ (inclMatrix ℂ (e ∘ Sum.inl)) m) :
    m ∗ₘ volume.map embedH ≤ ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1)) • volume := by
  -- Complete `g E` to a basis by `k` vectors orthogonal to it, which is the definite case, and
  -- compare with the fibre measure on bases.
  set E : Matrix 𝔰.BesselIndex n ℂ := inclMatrix ℂ (e ∘ Sum.inl)
  set c : ℝ := volU 𝔰.k / 2 ^ 𝔰.k
  have hc : 0 < c := div_pos (volU_pos _) (by positivity)
  have hXE : 𝔰.definiteColsᴴ * E = 0 := inclMatrix_gram_eq_zero fun i j ↦ by simp [← he]
  have h_orth : Eᴴ * 𝔰.J₁ * 𝔰.definiteCols = 0 := by
    simpa [Matrix.mul_assoc, J₁_mul_definiteCols] using congrArg conjTranspose hXE
  have h_basis : LeGramFiber 𝔰.J₁ (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)
      (m ∗ₘ (ENNReal.ofReal c • volume.map embedH)) := by
    refine hm.append e ?_ (LeFibreMeasure.trans ?_ leFiberMeasure_definiteCols (by fun_prop))
      (ae_smul_measure (ae_map_mul_eq (by fun_prop) fun u ↦ by
        simp [coe_embedH, actOnCols, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hXE]) _)
    · rw [← LinearEquiv.eq_symm_apply, Shape.definiteCols, ← funext he]
      rfl
    · simpa only [h_orth, Matrix.mul_zero, zero_add] using leFiberMeasure_conjTranspose_mul_mul
        (inclMatrix_gram_eq_one (e.injective.comp Sum.inl_injective))
        conjTranspose_definiteCols_mul_self h_orth (by simp [← card_congr e]) (0 : Matrix n 𝔰.κ ℂ)
  have h_const : volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1) =
      c⁻¹ * (volU (card 𝔰.BesselIndex) / 2 ^ card 𝔰.BesselIndex) := by
    rw [show 𝔰.r = card 𝔰.BesselIndex by simp,
      show card 𝔰.BesselIndex = 2 * 𝔰.ϱ + 1 + 𝔰.k by simp +arith]
    simp [c, pow_add, field]
  rw [show m ∗ₘ volume.map embedH =
      ENNReal.ofReal c⁻¹ • (m ∗ₘ (ENNReal.ofReal c • volume.map embedH)) by
        simp [mconv_smul_right, smul_smul, ← ENNReal.ofReal_mul (inv_pos.2 hc).le, hc.ne'],
    h_const, ENNReal.ofReal_mul (inv_pos.2 hc).le, mul_smul]
  gcongr
  exact h_basis.le_haar

/-! ### Coordinates adapted to the frame -/

/-- The matrix with the columns `e_0, …, e_{ϱ-1}` and `x_i`; they span the vectors orthogonal to the
frame `e_0, …, e_{ϱ-1}, z` for the form `J₁`. -/
abbrev _root_.New.Shape.freeCols (𝔰 : Shape) : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ ⊕ 𝔰.κ) ℂ :=
  fromCols 𝔰.isotropicCols 𝔰.definiteCols

/-- The columns of `frameCols`, the frame vectors `e_0, …, e_{ϱ-1}, z`, are orthonormal for the
standard hermitian form. -/
theorem conjTranspose_frameCols_mul_self : 𝔰.frameColsᴴ * 𝔰.frameCols = 1 :=
  inclMatrix_gram_eq_one (by simp [Fin.forall_fin_succ'])

/-- The columns `e_a, x_i` of `freeCols` are orthonormal for the standard hermitian form. -/
theorem conjTranspose_freeCols_mul_self : 𝔰.freeColsᴴ * 𝔰.freeCols = 1 := by
  simp [← ext_iff, inclMatrix, Matrix.mul_apply, Matrix.one_apply, eq_comm]

/-- The columns `e_a, x_i` of `freeCols` are orthogonal to the frame `e_0, …, e_{ϱ-1}, z` for
the form `J₁`. -/
theorem frameCols_gram_freeCols : 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.freeCols = 0 := by
  simp [← ext_iff, J₁_eq, inclMatrix, Matrix.mul_apply, Fin.forall_fin_succ']

/-- The `ϱ + 1` vectors of the frame and the `ϱ + k` columns of `freeCols` are together as many as
the basis vectors. -/
theorem card_frame_add_card_free :
    card (Fin (𝔰.ϱ + 1)) + card (Fin 𝔰.ϱ ⊕ 𝔰.κ) = card 𝔰.BesselIndex := by
  simp +arith

/-- For `q = (b, s)` in `UnipotentParams`, with `b` a complex `ϱ × k` matrix and `s` a real `ϱ × ϱ`
matrix, and `u = unipotentOf q` the element of 𝖴⁰ with parameters `q`, the tuple `u (e* + e a)` is
`e* + e (skewOfReal s + a - b bᴴ / 2) - x bᴴ`, where `e`, `x`, `e*` are the matrices
`isotropicCols`, `definiteCols`, `dualCols` with columns `e_i`, `x_i`, `e*_i`, and `skewOfReal s` is
the skew-hermitian matrix with real coordinates `s`. -/
theorem unipotentOf_mul_dualCols_add (q : 𝔰.UnipotentParams) (a : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ) :
    (unipotentOf q).val.val * (𝔰.dualCols + 𝔰.isotropicCols * a) =
      𝔰.dualCols + 𝔰.isotropicCols * (skewOfReal q.2 + a - (2⁻¹ : ℂ) • (q.1 * q.1ᴴ)) +
        𝔰.definiteCols * -q.1ᴴ := by
  simp [val_unipotentOf_coe, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, inclMatrix_gram_eq_one, inclMatrix_gram_eq_zero, inclMatrix_gram_mul_eq_zero]
  abel

/-- Coordinates on the `ϱ`-tuples `e* + e a + x c`, `p = (a, c)`, which are the tuples dual to
`e_0, …, e_{ϱ-1}` and orthogonal to `z`; `e*` is `dualCols`, `e` is `isotropicCols`, and `(e, x)` is
`freeCols`. Such a tuple is `u (e* + e T / 2)` with `u = unipotentOf q` in the unipotent group 𝖴⁰
and `T = hermOfReal t` its Gram matrix, the hermitian matrix with real coordinates `t`, and
`dp = 2 ^ (-ϱ) dt dq`, where `dq = db ds` is Lebesgue measure on the pairs `q = (b, s)` of
`UnipotentParams`. -/
theorem lintegral_eq_unipotent_coords {K : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ → ℝ≥0∞}
    (hK : Measurable K) :
    ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ, K (𝔰.dualCols + 𝔰.freeCols * p) =
      (2 ^ 𝔰.ϱ)⁻¹ * ∫⁻ t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ, ∫⁻ q : 𝔰.UnipotentParams,
        K ((unipotentOf q).val.val *
          (𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • hermOfReal t))) := by
  -- With `q = (b, s)` we have `c = -bᴴ` and `a = skewOfReal s + T / 2 - b bᴴ / 2`. For fixed `b`,
  -- translate `a` and split it into its skew-hermitian and hermitian parts.
  let F (a : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ) (b : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ) : ℝ≥0∞ :=
    K (𝔰.dualCols + (𝔰.isotropicCols * a + 𝔰.definiteCols * -bᴴ))
  have := Measure.IsAddHaarMeasure.isNegInvariant_of_regular
    (volume : Measure (Matrix 𝔰.κ (Fin 𝔰.ϱ) ℂ))
  have h_rows : MeasurePreserving
      fun x : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ × Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ ↦ fromRows x.1 (-x.2ᴴ) :=
    measurePreserving_fromRows.comp ((MeasurePreserving.id volume).prod
      ((measurePreserving_neg volume).comp measurePreserving_conjTranspose))
  calc
    _ = ∫⁻ b : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ, ∫⁻ a : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℂ, F a b := by
      simp (disch := fun_prop) only [← h_rows.lintegral_comp, fromCols_mul_fromRows]
      exact lintegral_prod_symm' F.uncurry (by fun_prop)
    _ = ∫⁻ b : Matrix (Fin 𝔰.ϱ) 𝔰.κ ℂ, (2 ^ 𝔰.ϱ)⁻¹ *
          ∫⁻ t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ, ∫⁻ s : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ,
            F (skewOfReal s + (2⁻¹ : ℂ) • hermOfReal t - (2⁻¹ : ℂ) • (b * bᴴ)) b := by
      refine lintegral_congr fun b ↦ ?_
      rw [← lintegral_sub_right_eq_self _ ((2⁻¹ : ℂ) • (b * bᴴ)),
        lintegral_eq_skewOfReal_add_hermOfReal (by fun_prop), card_fin]
    _ = _ := by
      simp (disch := first | fun_prop | simp) only [unipotentOf_mul_dualCols_add, volume_eq_prod,
        lintegral_prod, F, add_assoc, lintegral_const_mul']
      rw [lintegral_lintegral_swap (by fun_prop)]

/-! ### Frames -/

/-- The dual vectors `e*_a`, the columns of `dualCols`. On `ϱ`-tuples `y`, the image under
`u ↦ u (e*_0, …, e*_{ϱ-1})` of `2^(-ϱ)` times Haar measure `New.Shape.besselHaar₀` of the unipotent
group 𝖴⁰ is at most the fibre measure (`LeFibreMeasure`) of the map that sends `y` to its products
with the frame `e_0, …, e_{ϱ-1}, z` (columns of `frameCols`), and to the coordinates `gramCoords` of
its Gram matrix, over the image of `(e*_0, …, e*_{ϱ-1})`. -/
theorem leFiberMeasure_dualCols :
    LeFibreMeasure volume volume
      (fun y : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ ↦ (𝔰.frameColsᴴ * 𝔰.J₁ * y, gramCoords 𝔰.J₁ y))
      (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols, gramCoords 𝔰.J₁ 𝔰.dualCols)
      ((((2 : ℝ≥0∞) ^ 𝔰.ϱ)⁻¹ • 𝔰.besselHaar₀.map Subtype.val).map
        fun g : 𝔰.G₁ ↦ g.val.val * 𝔰.dualCols) := by
  -- Fix the products with the frame, then the Gram matrix.
  have h_dual : 𝔰.J₁ * 𝔰.frameCols * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols) = 𝔰.dualCols := by
    simp [← ext_iff, inclMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_castSucc]
  let μ : Measure (Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ) :=
    volume.map fun p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ ↦ 𝔰.dualCols + 𝔰.freeCols * p
  have h_linear : LeFibreMeasure volume volume (𝔰.frameColsᴴ * 𝔰.J₁ * ·)
      (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols) μ := by
    simpa only [h_dual] using leFiberMeasure_conjTranspose_mul_mul conjTranspose_frameCols_mul_self
      conjTranspose_freeCols_mul_self
      frameCols_gram_freeCols card_frame_add_card_free (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualCols)
  let ψ (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) (q : 𝔰.UnipotentParams) :
      Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ :=
    (unipotentOf q).val.val * (𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • hermOfReal t))
  have hψ_gram (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) (q : 𝔰.UnipotentParams) :
      gramCoords 𝔰.J₁ (ψ t q) = t := by
    -- `unipotentOf q` preserves the form, and the Gram matrix of `e* + e T / 2` is `T`.
    rw [gramCoords_U_mul, gramCoords_eq_iff]
    simp [J₁_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc,
      inclMatrix_gram_eq_one, inclMatrix_gram_eq_zero, inclMatrix_gram_mul_eq_zero,
      inclMatrix_gram_mul_eq_self]
    module
  have hψ_zero (q : 𝔰.UnipotentParams) : ψ 0 q = (unipotentOf q).val.val * 𝔰.dualCols := by
    simp [ψ, hermOfReal]
  have h_base : gramCoords 𝔰.J₁ 𝔰.dualCols = 0 := by
    simpa [hψ_zero, gramCoords_U_mul] using hψ_gram 0 0
  have h_gram : LeFibreMeasure μ volume (gramCoords 𝔰.J₁) 0
      ((volume.withDensity fun _ ↦ (2 ^ 𝔰.ϱ)⁻¹).map (ψ 0)) := by
    refine .of_coordinates (w := fun _ _ ↦ (2 ^ 𝔰.ϱ)⁻¹) (by fun_prop) (by fun_prop)
      measurable_const Filter.univ_mem (fun t _ ↦ .of_forall fun q _ ↦ hψ_gram t q)
      (.of_forall fun q ↦ ⟨Continuous.continuousAt (by fun_prop), continuousAt_const⟩) fun K hK ↦ ?_
    rw [lintegral_map hK (by fun_prop), lintegral_eq_unipotent_coords hK]
    simp [lintegral_const_mul', ψ]
  simpa (disch := fun_prop) only [withDensity_const, funext hψ_zero, h_base, Shape.besselHaar₀,
    ← Measure.map_smul, Measure.map_map, Function.comp_def, volume_eq_prod]
    using h_linear.trans h_gram (by fun_prop)

/-- The measure `ds = du dh` on the fixer 𝖴⁰ H of the frame, as a measure on `G₁`: the image under
`(u, h) ↦ u h` of the Haar measure `New.Shape.besselHaar₀` on 𝖴⁰ and the Haar measure of mass one on
`H = U(X₀)`. -/
def fixerHaar (𝔰 : Shape) : Measure 𝔰.G₁ := 𝔰.besselHaar₀.map Subtype.val ∗ₘ volume.map embedH

instance : SFinite (fixerHaar 𝔰) := by
  unfold fixerHaar
  infer_instance

/-- The fibre measure on frames. If the image of `m` under `g ↦ g F`, with `F = frameCols` the frame
`e_0, …, e_{ϱ-1}, z`, is at most the Gram map's fibre measure (`LeGramFiber`), then the convolution
of `m` with the measure `fixerHaar 𝔰` on the fixer 𝖴⁰ H of the frame is at most
`vol U(r) / (vol U(k) 2 ^ (ϱ + 1))` times Haar measure of `G₁`, normalised through its compact
dual. Here `r` is the rank, `k` the dimension of `X₀`, and `volU j` is `vol U(j)`. -/
theorem _root_.New.LeGramFiber.mconv_fixerHaar_le {m : Measure 𝔰.G₁} [SFinite m]
    (hm : LeGramFiber 𝔰.J₁ 𝔰.frameCols m) :
    m ∗ₘ fixerHaar 𝔰 ≤ ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k / 2 ^ (𝔰.ϱ + 1)) • volume := by
  -- Add the dual vectors to the frame; the complement of the tuple so obtained is definite.
  let e : (Fin (𝔰.ϱ + 1) ⊕ Fin 𝔰.ϱ) ⊕ 𝔰.κ ≃ 𝔰.BesselIndex :=
    .ofBijective (Sum.elim (Sum.elim 𝔰.besselFrame eStar) 𝔰.indexX₀) <|
      (bijective_iff_injective_and_card _).2
        ⟨by simp [Function.Injective, Fin.forall_fin_succ'], by simp +arith⟩
  let ν : Measure 𝔰.G₁ := 𝔰.besselHaar₀.map Subtype.val
  have h_fix : ∀ᵐ g : 𝔰.G₁ ∂ν, g.val.val * 𝔰.frameCols = 𝔰.frameCols := by
    refine ae_map_mul_eq measurable_subtypeVal fun u ↦ ?_
    obtain ⟨q, hq⟩ := mem_besselU0_iff_unipotentOf.1 u.property
    simp [hq, val_unipotentOf_coe, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc,
      inclMatrix_gram_eq_zero, Fin.forall_fin_succ']
  have h_pairs : LeGramFiber 𝔰.J₁ (inclMatrix ℂ (e ∘ Sum.inl)) (m ∗ₘ (((2 : ℝ≥0∞) ^ 𝔰.ϱ)⁻¹ • ν)) :=
    hm.append (.refl _) (by ext i (j | j) <;> rfl) leFiberMeasure_dualCols
      (ae_smul_measure h_fix _)
  have h_const : (2 : ℝ) ^ 𝔰.ϱ * (volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1)) =
      volU 𝔰.r / volU 𝔰.k / 2 ^ (𝔰.ϱ + 1) := by field
  calc
    _ = (2 : ℝ≥0∞) ^ 𝔰.ϱ • ((m ∗ₘ (((2 : ℝ≥0∞) ^ 𝔰.ϱ)⁻¹ • ν)) ∗ₘ volume.map embedH) := by
        simp [mconv_smul_right, mconv_smul_left, mconv_assoc, smul_smul, ENNReal.mul_inv_cancel,
          fixerHaar, ν]
    _ ≤ (2 : ℝ≥0∞) ^ 𝔰.ϱ •
        ENNReal.ofReal (volU 𝔰.r / volU 𝔰.k / 2 ^ (2 * 𝔰.ϱ + 1)) • volume := by
        gcongr
        exact h_pairs.mconv_embedH_le e fun _ ↦ rfl
    _ = _ := by
        rw [← h_const, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two]
        simp [smul_smul]

end New.RealPlace

end
