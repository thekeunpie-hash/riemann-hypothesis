module

public import TauCeti.Analysis.Matrix.MeasurableSpace
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import TauCeti.Topology.Instances.Matrix
public import Lib.General.LinearAlgebra.HermitianMatrices
public import Lib.DiscreteSeries.Haar.CayleyChart
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Separation.Connected
import Lib.Adelic.Witt.WittTheorem
import Lib.General.Analysis.GaussianIntegral
import Lib.General.Analysis.PackingAndSobolev
import Lib.General.Measure.IntegralOperators

section
section
/-!
# Coordinates for the Gram map

Let `J` be a hermitian matrix. The Gram map sends a tuple of vectors, the columns of a complex
matrix `Y`, to the hermitian matrix `T = Yᴴ J Y`. Tuples carry Lebesgue measure `dY`, and hermitian
matrices the product `dT` of the Lebesgue measures of the entries on and above the diagonal.

* `New.joinCols`, `New.joinCol`: joining two groups of columns into one matrix; this preserves
  volume (`New.measurePreserving_joinCols`, `New.measurePreserving_joinCol`).
* `New.hermOfReal`, `New.gramCoords`: real coordinates on hermitian matrices, and the Gram map in
  these coordinates.
* `New.lintegral_eq_skewOfReal_add_hermOfReal`: Lebesgue measure on matrices `Z = S + T / 2` of size
  `n`, with `S` skew-hermitian and `T` hermitian, is `2 ^ (-n) dS dT`.
* `New.exists_measurePreserving_hermBlocks`, `New.exists_measurePreserving_hermCorner`: cutting a
  hermitian matrix into the corresponding blocks preserves volume.

Notions from other files:
* `New.skewOfReal`: the skew-hermitian matrix with given real coordinates, normalised so that
  Lebesgue measure in the coordinates is that of the entries on and above the diagonal.
* `New.skewCoords`: the real-linear left inverse of `New.skewOfReal`, inverse to it on
  skew-hermitian matrices.
-/

@[expose] public section

noncomputable section

namespace New

open Matrix MeasureTheory Measure Complex Fintype ENNReal Norms.L2Operator Filter Topology

variable {ι n n₁ n₂ : Type}

/-! ### Columns and transposes -/

/-- The linear isomorphism that sends a pair of matrices to the matrix with the columns of both, in
the places given by `e`. -/
def joinCols (e : n₁ ⊕ n₂ ≃ n) : (Matrix ι n₁ ℂ × Matrix ι n₂ ℂ) ≃ₗ[ℝ] Matrix ι n ℂ where
  toFun p := (fromCols p.1 p.2).submatrix id e.symm
  invFun Y := (Y.submatrix id (e ∘ Sum.inl), Y.submatrix id (e ∘ Sum.inr))
  map_add' := by simp [← ext_iff, e.surjective.forall]
  map_smul' := by simp [← ext_iff, e.surjective.forall]
  left_inv := by simp [Function.LeftInverse, Prod.ext_iff, ← ext_iff]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, ← ext_iff, e.surjective.forall]

/-- Joining two groups of columns is continuous. -/
@[fun_prop]
theorem continuous_joinCols [Fintype ι] [Fintype n₁] [Fintype n₂] (e : n₁ ⊕ n₂ ≃ n) :
    Continuous (joinCols (ι := ι) e) := (joinCols e).continuous_of_finiteDimensional

/-- Joining two groups of complex columns (`joinCols`) preserves Lebesgue measure. -/
theorem measurePreserving_joinCols [Fintype ι] [Fintype n] [Fintype n₁] [Fintype n₂]
    (e : n₁ ⊕ n₂ ≃ n) : MeasurePreserving (joinCols (ι := ι) e) := by
  classical
  have h_norm (p : Matrix ι n₁ ℂ × Matrix ι n₂ ℂ) :
      ∑ a : ι, ∑ b : n, ‖joinCols e p a b‖ ^ 2 =
        ∑ a : ι, ∑ b : n₁, ‖p.1 a b‖ ^ 2 + ∑ a : ι, ∑ b : n₂, ‖p.2 a b‖ ^ 2 := by
    simp [joinCols, ← e.sum_comp, Finset.sum_add_distrib]
  have : IsAddHaarMeasure (volume : Measure (Matrix ι n₁ ℂ × Matrix ι n₂ ℂ)) :=
    prod.instIsAddHaarMeasure _ _
  exact HasGaussianIntegral.measurePreserving _ h_norm

/-- Placing one complex matrix above another preserves Lebesgue measure. -/
theorem measurePreserving_fromRows {l m k : Type} [Fintype l] [Fintype m] [Fintype k] :
    MeasurePreserving fun p : Matrix l k ℂ × Matrix m k ℂ ↦ fromRows p.1 p.2 :=
  volume_measurePreserving_sumPiEquivProdPi_symm fun _ ↦ k → ℂ

/-- Left multiplication by a matrix acts on each of two groups of columns separately. -/
theorem mul_joinCols {l : Type} [Fintype ι] (e : n₁ ⊕ n₂ ≃ n) (A : Matrix l ι ℂ)
    (x : Matrix ι n₁ ℂ) (y : Matrix ι n₂ ℂ) :
    A * joinCols e (x, y) = joinCols e (A * x, A * y) := by
  simp [← ext_iff, e.surjective.forall, joinCols, Matrix.mul_apply]

/-- A vector as a matrix with one column. -/
def toCol (κ R : Type) [TopologicalSpace R] : (κ → R) ≃ₜ Matrix κ Unit R :=
  .piCongrRight fun _ ↦ (Homeomorph.funUnique Unit R).symm

@[simp]
theorem toCol_apply {κ R : Type} [TopologicalSpace R] (v : κ → R) (i : κ) (u : Unit) :
    toCol κ R v i u = v i := rfl

/-- Reading a vector as a matrix with one column (`toCol`) preserves volume. -/
theorem measurePreserving_toCol (κ R : Type) [Fintype κ] [TopologicalSpace R] [MeasureSpace R]
    [SigmaFinite (volume : Measure R)] : MeasurePreserving (toCol κ R) :=
  volume_preserving_pi fun _ ↦ (volume_preserving_funUnique Unit R).symm

/-- A vector and a real number as a one-column matrix and a one-by-one matrix. -/
def toCorner (κ : Type) : ((κ → ℂ) × ℝ) ≃ₜ Matrix κ Unit ℂ × Matrix Unit Unit ℝ :=
  (toCol κ ℂ).prodCongr ((Homeomorph.funUnique Unit ℝ).symm.trans (toCol Unit ℝ))

theorem toCorner_apply {κ : Type} (v : κ → ℂ) (r : ℝ) :
    toCorner κ (v, r) = (toCol κ ℂ v, toCol Unit ℝ fun _ : Unit ↦ r) := rfl

theorem measurePreserving_toCorner [Fintype n] : MeasurePreserving (toCorner n) :=
  (measurePreserving_toCol n ℂ).prod
    ((measurePreserving_toCol Unit ℝ).comp (volume_preserving_funUnique Unit ℝ).symm)

/-- The matrix whose columns are those of `p.1` and the vector `p.2`, in the places given by `e`. -/
def joinCol (e : n₁ ⊕ Unit ≃ n) (p : Matrix ι n₁ ℂ × (ι → ℂ)) : Matrix ι n ℂ :=
  joinCols e (p.1, toCol ι ℂ p.2)

@[simp]
theorem joinCol_inl (e : n₁ ⊕ Unit ≃ n) (p : Matrix ι n₁ ℂ × (ι → ℂ)) (i : ι) (a : n₁) :
    joinCol e p i (e (.inl a)) = p.1 i a := by simp [joinCol, joinCols]

@[simp]
theorem joinCol_inr (e : n₁ ⊕ Unit ≃ n) (p : Matrix ι n₁ ℂ × (ι → ℂ)) (i : ι) :
    joinCol e p i (e (.inr ())) = p.2 i := by simp [joinCol, joinCols]

@[fun_prop]
theorem continuous_joinCol [Fintype ι] [Fintype n₁] (e : n₁ ⊕ Unit ≃ n) :
    Continuous (joinCol (ι := ι) e) := (continuous_joinCols e).comp (by fun_prop)

/-- Adjoining a complex vector as a further column (`joinCol`) preserves Lebesgue measure. -/
theorem measurePreserving_joinCol [Fintype ι] [Fintype n] [Fintype n₁] (e : n₁ ⊕ Unit ≃ n) :
    MeasurePreserving (joinCol (ι := ι) e) :=
  (measurePreserving_joinCols e).comp ((MeasurePreserving.id _).prod (measurePreserving_toCol ι ℂ))

/-- Left multiplication by a matrix acts separately on the given columns and on the adjoined
one. -/
theorem mul_joinCol {l : Type} [Fintype ι] (e : n₁ ⊕ Unit ≃ n) (A : Matrix l ι ℂ)
    (Y : Matrix ι n₁ ℂ) (v : ι → ℂ) : A * joinCol e (Y, v) = joinCol e (A * Y, A *ᵥ v) := by
  rw [joinCol, mul_joinCols]
  rfl

/-- On the matrices without columns, which form a single point, the volume is the unit mass. -/
theorem volume_eq_dirac_of_isEmpty [Fintype ι] [Fintype n] {R : Type} [MeasureSpace R]
    [SigmaFinite (volume : Measure R)] [IsEmpty n] (Y : Matrix ι n R) : volume = dirac Y := by
  refine ext_iff_singleton.2 fun Z ↦ ?_
  rw [Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty Z), measure_univ (μ := dirac Y)]
  exact (pi_univ _).trans (Finset.prod_eq_one fun _ _ ↦ pi_empty_univ _)

/-- The conjugate transpose preserves Lebesgue measure on complex matrices. -/
theorem measurePreserving_conjTranspose [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] :
    MeasurePreserving fun b : Matrix ι n ℂ ↦ bᴴ := by
  have h_norm (b : Matrix ι n ℂ) :
      ∑ a : n, ∑ i : ι, ‖bᴴ a i‖ ^ 2 = ∑ i : ι, ∑ a : n, ‖b i a‖ ^ 2 := by
    simpa using Finset.sum_comm
  let e : Matrix ι n ℂ ≃ₗ[ℝ] Matrix n ι ℂ :=
    { conjTransposeAddEquiv ι n ℂ with map_smul' := by simp [star_trivial] }
  exact HasGaussianIntegral.measurePreserving e h_norm

section Hermitian

variable [Fintype ι] [DecidableEq n]

/-! ### Measurability and linear changes of variables -/

omit [DecidableEq n] in
/-- The product of two measurable families of complex matrices is measurable. -/
@[fun_prop]
theorem _root_.Measurable.matrix_mul [Fintype n] {X : Type} [MeasurableSpace X] [Fintype n₁]
    {A : X → Matrix ι n₁ ℂ} {B : X → Matrix n₁ n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x : X ↦ A x * B x :=
  (continuous_fst.matrix_mul continuous_snd).measurable.comp (hA.prodMk hB)

@[fun_prop]
theorem measurable_matrix_det [Fintype n] : Measurable fun Z : Matrix n n ℂ ↦ Z.det :=
  continuous_id.matrix_det.measurable

/-- Substitution by an invertible real linear map `T` in an integral against an additive Haar
measure: the Jacobian is `|det T|`. -/
theorem lintegral_eq_abs_det_mul_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {T : V →ₗ[ℝ] V} (hT : T.det ≠ 0) {K : V → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ y : V, K y ∂μ = ENNReal.ofReal |T.det| * ∫⁻ y : V, K (T y) ∂μ := by
  have h_map : ∫⁻ y : V, K (T y) ∂μ = ENNReal.ofReal |T.det⁻¹| * ∫⁻ y : V, K y ∂μ := by
    rw [← lintegral_map hK T.continuous_of_finiteDimensional.measurable,
      map_linearMap_addHaar_eq_smul_addHaar μ hT, lintegral_smul_measure, smul_eq_mul]
  rw [h_map, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hT]
  simp

/-- Substitution `y ↦ P y Q` in an integral over complex matrices, for invertible `P` and `Q`: the
Jacobian is `|det P| ^ (2 |n|) |det Q| ^ (2 |ι|)`. -/
theorem lintegral_eq_det_mul_comp_mul_mul [Fintype n]
    [DecidableEq ι] {P : Matrix ι ι ℂ} {Q : Matrix n n ℂ}
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0) {K : Matrix ι n ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ y : Matrix ι n ℂ, K y =
      ‖P.det‖ₑ ^ (2 * card n) * ‖Q.det‖ₑ ^ (2 * card ι) * ∫⁻ y : Matrix ι n ℂ, K (P * y * Q) := by
  let L : Matrix ι n ℂ →ₗ[ℝ] Matrix ι n ℂ := mulRightLinearMap ι ℝ Q ∘ₗ mulLeftLinearMap n ℝ P
  have h_det : L.det = ‖P.det‖ ^ (2 * card n) * ‖Q.det‖ ^ (2 * card ι) :=
    det_mulLeft_mulRight_real P Q
  have h_ne : L.det ≠ 0 := h_det.trans_ne (by positivity)
  simp [lintegral_eq_abs_det_mul_comp volume h_ne hK, h_det, L, ENNReal.ofReal_mul,
    ENNReal.ofReal_pow]

/-! ### Hermitian coordinates -/

/-- The hermitian matrix with real coordinates `t`: it is `-i` times the skew-hermitian matrix
`skewOfReal t`, so its diagonal entries are those of `t`. Lebesgue measure in `t` is the product
of the Lebesgue measures of the entries on and above the diagonal. -/
def hermOfReal (t : Matrix n n ℝ) : Matrix n n ℂ := -I • skewOfReal t

/-- The Gram map: the real coordinates, in the sense of `hermOfReal`, of the Gram matrix
`Yᴴ J Y` of the columns of `Y`, for a hermitian `J` (`hermOfReal_gramCoords`). -/
def gramCoords (J : Matrix ι ι ℂ) (Y : Matrix ι n ℂ) : Matrix n n ℝ :=
  skewCoords (I • (Yᴴ * J * Y))

@[simp]
theorem conjTranspose_hermOfReal (t : Matrix n n ℝ) : (hermOfReal t)ᴴ = hermOfReal t := by
  simp [hermOfReal, conjTranspose_smul]

@[simp]
theorem skewCoords_I_smul_hermOfReal (t : Matrix n n ℝ) : skewCoords (I • hermOfReal t) = t := by
  simp [hermOfReal, smul_smul]

/-- For a hermitian `J`, the hermitian matrix with the real coordinates `gramCoords J Y` is the
Gram matrix `Yᴴ J Y`. -/
theorem hermOfReal_gramCoords {J : Matrix ι ι ℂ} (hJ : J.IsHermitian) (Y : Matrix ι n ℂ) :
    hermOfReal (gramCoords J Y) = Yᴴ * J * Y := by
  have h_skew : (I • (Yᴴ * J * Y))ᴴ = -(I • (Yᴴ * J * Y)) := by
    simp [conjTranspose_smul, hJ.eq, Matrix.mul_assoc]
  simp [hermOfReal, gramCoords, skewOfReal_skewCoords h_skew, smul_smul]

@[fun_prop]
theorem continuous_gramCoords [Fintype n] (J : Matrix ι ι ℂ) :
    Continuous (gramCoords J : Matrix ι n ℂ → Matrix n n ℝ) :=
  skewCoords.continuous_of_finiteDimensional.comp (by fun_prop)

@[fun_prop]
theorem continuous_hermOfReal [Fintype n] : Continuous (hermOfReal : Matrix n n ℝ → Matrix n n ℂ) :=
  skewOfReal.continuous_of_finiteDimensional.const_smul (-I)

/-- In the real coordinates `t` of hermitian matrices `T = hermOfReal t` of size `n`, the congruence
`T ↦ Cᴴ T C` has the Jacobian `|det C| ^ (2 n)`. -/
theorem lintegral_eq_det_mul_comp_congruence [Fintype n] {C : Matrix n n ℂ} (hC : C.det ≠ 0)
    {G : Matrix n n ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t : Matrix n n ℝ, G (hermOfReal t) =
      ‖C.det‖ₑ ^ (2 * card n) * ∫⁻ t : Matrix n n ℝ, G (Cᴴ * hermOfReal t * C) := by
  let L : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
    skewCoords ∘ₗ LinearMap.mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal
  -- `abs_det_skew_congruence` allows coordinate changes on both sides; here both are trivial.
  have h_det : |L.det| = ‖C.det‖ ^ (2 * card n) := by
    simpa using abs_det_skew_congruence (LinearEquiv.refl ℝ (Matrix n n ℝ)) C LinearMap.id
  have h_herm (t : Matrix n n ℝ) : hermOfReal (L t) = Cᴴ * hermOfReal t * C := by
    simp [L, hermOfReal, skewOfReal_skewCoords, Matrix.mul_assoc]
  have h_ne : L.det ≠ 0 := abs_ne_zero.1 (h_det.trans_ne (by positivity))
  simp [lintegral_eq_abs_det_mul_comp volume h_ne (show Measurable fun t ↦ G (hermOfReal t) by
    fun_prop), h_det, h_herm, ENNReal.ofReal_pow]

/-- The derivative of the Gram matrix `σᴴ J σ` of a differentiable family `σ` of matrices is
`σᴴ J dσ + dσᴴ J σ`, read in the coordinates of `gramCoords`. -/
theorem hasFDerivAt_gramCoords {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DecidableEq ι] (J : Matrix ι ι ℂ) {σ : V → Matrix ι ι ℂ} {σ' : V →L[ℝ] Matrix ι ι ℂ} {t : V}
    (hσ : HasFDerivAt σ σ' t) : ∃ D : V →L[ℝ] Matrix ι ι ℝ,
      HasFDerivAt (fun x : V ↦ gramCoords J (σ x)) D t ∧
      ∀ v : V, D v = skewCoords (I • ((σ t)ᴴ * J * σ' v + (σ' v)ᴴ * J * σ t)) :=
  -- the product rule, followed by the linear map `skewCoords`
  ⟨_, skewCoords.toContinuousLinearMap.hasFDerivAt.comp t
    (((hσ.star.mul_const' J).mul' hσ).const_smul I), fun _ ↦ rfl⟩

/-- The Gram map `Y ↦ Yᴴ J Y` on square matrices, read in the real coordinates of
`gramCoords`, is continuously differentiable. -/
theorem contDiff_gramCoords [DecidableEq ι] (J : Matrix ι ι ℂ) :
    ContDiff ℝ 1 (gramCoords J : Matrix ι ι ℂ → Matrix ι ι ℝ) := by
  have h_star : ContDiff ℝ 1 fun Y : Matrix ι ι ℂ ↦ Yᴴ := (starL' ℝ).contDiff
  exact skewCoords.toContinuousLinearMap.contDiff.comp
    (((h_star.mul contDiff_const).mul contDiff_id).const_smul I)

/-- The isomorphism `(t, s) ↦ S + T / 2` onto the complex matrices, where `S` is the skew-hermitian
matrix with coordinates `s` and `T` the hermitian matrix with coordinates `t`. The inverse reads
`T = Z + Zᴴ` and `S = (Z - Zᴴ) / 2`. -/
def skewAddHerm : (Matrix n n ℝ × Matrix n n ℝ) ≃ₗ[ℝ] Matrix n n ℂ where
  toFun p := skewOfReal p.2 + (2⁻¹ : ℂ) • hermOfReal p.1
  invFun Z := (skewCoords (I • (Z + Zᴴ)), skewCoords ((2⁻¹ : ℂ) • (Z - Zᴴ)))
  map_add' p q := by simp [hermOfReal, smul_add, add_add_add_comm]
  map_smul' c p := by simp [hermOfReal, smul_comm c]
  left_inv p := by
    have hZ : (skewOfReal p.2 + (2⁻¹ : ℂ) • hermOfReal p.1)ᴴ =
        -skewOfReal p.2 + (2⁻¹ : ℂ) • hermOfReal p.1 := by simp [conjTranspose_smul]
    refine Prod.ext ((congrArg skewCoords ?_).trans (skewCoords_I_smul_hermOfReal p.1))
      ((congrArg skewCoords ?_).trans (skewCoords_skewOfReal p.2))
    all_goals
      rw [hZ]
      module
  right_inv Z := by
    have h_herm : (I • (Z + Zᴴ))ᴴ = -(I • (Z + Zᴴ)) := by simp [conjTranspose_smul, add_comm]
    have h_skew : ((2⁻¹ : ℂ) • (Z - Zᴴ))ᴴ = -((2⁻¹ : ℂ) • (Z - Zᴴ)) := by
      simp [conjTranspose_smul, ← smul_neg]
    change skewOfReal (skewCoords ((2⁻¹ : ℂ) • (Z - Zᴴ))) +
      (2⁻¹ : ℂ) • hermOfReal (skewCoords (I • (Z + Zᴴ))) = Z
    simp only [hermOfReal, skewOfReal_skewCoords h_herm, skewOfReal_skewCoords h_skew,
      smul_smul (-I), neg_mul, I_mul_I, neg_neg, one_smul]
    module

theorem skewAddHerm_apply (t s : Matrix n n ℝ) :
    skewAddHerm (t, s) = skewOfReal s + (2⁻¹ : ℂ) • hermOfReal t := rfl

theorem skewAddHerm_symm_apply (Z : Matrix n n ℂ) :
    skewAddHerm.symm Z = (skewCoords (I • (Z + Zᴴ)), skewCoords ((2⁻¹ : ℂ) • (Z - Zᴴ))) := rfl

omit [DecidableEq n] in
/-- Scaling the entries of a real matrix by numbers `c a b` is a linear map with determinant
`∏ c a b`. -/
theorem exists_linearMap_scale_entries [Fintype n] (c : n → n → ℝ) :
    ∃ T : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ,
      (∀ (y : Matrix n n ℝ) (a b : n), T y a b = c a b * y a b) ∧
      T.det = ∏ a : n, ∏ b : n, c a b := by
  let L (a : n) : (n → ℝ) →ₗ[ℝ] n → ℝ :=
    LinearMap.pi fun b : n ↦ (c a b • LinearMap.id) ∘ₗ LinearMap.proj b
  refine ⟨LinearMap.pi fun a : n ↦ L a ∘ₗ LinearMap.proj a,
    fun y a b ↦ rfl, (LinearMap.det_pi _).trans ?_⟩
  simp [L, LinearMap.det_pi]

/-- The squared norms of the entries of `skewAddHerm (t', s')` in terms of `t` and `s`, when `t'`
and `s'` are `t` and `s` multiplied by `2 / d` and `1 / d` entrywise, with `d = 1` on the diagonal
and `d = √2` off it. -/
theorem norm_sq_skewAddHerm_of_scale {t s t' s' : Matrix n n ℝ}
    (ht : ∀ a b : n, t' a b = 2 / (if a = b then 1 else √2) * t a b)
    (hs : ∀ a b : n, s' a b = 1 / (if a = b then 1 else √2) * s a b) (a b : n) :
    ‖skewAddHerm (t', s') a b‖ ^ 2 = ((t a b + t b a + s a b - s b a) ^ 2 +
      (s a b + s b a + t b a - t a b) ^ 2) / 4 := by
  obtain rfl | hab := eq_or_ne a b
  · simp [skewAddHerm_apply, ht, hs, hermOfReal, skewOfReal, Complex.sq_norm, normSq_apply]
    ring
  · simp [skewAddHerm_apply, ht, hs, hermOfReal, skewOfReal, Complex.sq_norm, normSq_apply, hab,
      hab.symm, field]
    ring

variable [Fintype n]

/-- The isomorphism `skewAddHerm`, `(t, s) ↦ S + T / 2`, onto the complex matrices of size `n`
has Jacobian `2 ^ (-n)`; here `S` is the skew-hermitian matrix with coordinates `s` and `T` the
hermitian one with coordinates `t`. -/
theorem lintegral_eq_comp_skewAddHerm {K : Matrix n n ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Z : Matrix n n ℂ, K Z =
      (2 ^ card n)⁻¹ * ∫⁻ p : Matrix n n ℝ × Matrix n n ℝ, K (skewAddHerm p) := by
  -- After scaling the entries of `t` by `2 / d` and those of `s` by `1 / d`, with `d = 1` on the
  -- diagonal and `d = √2` off it, the map is an isometry for the sums of squares of the entries.
  let d (a b : n) : ℝ := if a = b then 1 else √2
  obtain ⟨T₁, hT₁, hT₁_det⟩ := exists_linearMap_scale_entries fun a b : n ↦ 2 / d a b
  obtain ⟨T₂, hT₂, hT₂_det⟩ := exists_linearMap_scale_entries fun a b : n ↦ 1 / d a b
  have h_det : (T₁.prodMap T₂).det = 2 ^ card n := by
    have h_entry (a b : n) : 2 / d a b * (1 / d a b) = if a = b then 2 else 1 := by
      by_cases hab : a = b <;> simp [d, hab, field]
    simp only [LinearMap.det_prodMap, hT₁_det, hT₂_det, ← Finset.prod_mul_distrib, h_entry]
    simp
  have h_ne : (T₁.prodMap T₂).det ≠ 0 := h_det.trans_ne (by positivity)
  have h_iso : MeasurePreserving (((T₁.prodMap T₂).equivOfDetNeZero h_ne).trans skewAddHerm) := by
    refine HasGaussianIntegral.measurePreserving _ fun p ↦ ?_
    let Z : Matrix n n ℂ := skewAddHerm (T₁ p.1, T₂ p.2)
    have h_sq (a b : n) : ‖Z a b‖ ^ 2 + ‖Z b a‖ ^ 2 =
        p.1 a b ^ 2 + p.2 a b ^ 2 + (p.1 b a ^ 2 + p.2 b a ^ 2) := by
      rw [norm_sq_skewAddHerm_of_scale (hT₁ p.1) (hT₂ p.2),
        norm_sq_skewAddHerm_of_scale (hT₁ p.1) (hT₂ p.2)]
      ring
    -- Sum over all `a`, `b`: each entry is counted twice on both sides.
    have h_sum : ∑ a : n, ∑ b : n, (‖Z a b‖ ^ 2 + ‖Z b a‖ ^ 2) =
        ∑ a : n, ∑ b : n, (p.1 a b ^ 2 + p.2 a b ^ 2 + (p.1 b a ^ 2 + p.2 b a ^ 2)) := by
      simp only [h_sq]
    change ∑ a : n, ∑ b : n, ‖Z a b‖ ^ 2 =
      ∑ a : n, ∑ b : n, p.1 a b ^ 2 + ∑ a : n, ∑ b : n, p.2 a b ^ 2
    simp only [Finset.sum_add_distrib, Finset.sum_comm (f := fun a b ↦ ‖Z b a‖ ^ 2),
      Finset.sum_comm (f := fun a b ↦ p.1 b a ^ 2),
      Finset.sum_comm (f := fun a b ↦ p.2 b a ^ 2)] at h_sum
    linarith
  have hK' : Measurable fun p : Matrix n n ℝ × Matrix n n ℝ ↦ K (skewAddHerm p) :=
    hK.comp skewAddHerm.toLinearMap.continuous_of_finiteDimensional.measurable
  have h_subst : ∫⁻ Z : Matrix n n ℂ, K Z = ∫⁻ p, K (skewAddHerm (T₁.prodMap T₂ p)) :=
    (h_iso.lintegral_comp hK).symm
  simp [h_subst, lintegral_eq_abs_det_mul_comp volume h_ne hK', h_det, ENNReal.ofReal_pow,
    ← mul_assoc, ENNReal.inv_mul_cancel]

/-- Lebesgue measure on the complex matrices `Z = S + T / 2` of size `n`, with `S = skewOfReal s`
skew-hermitian and `T = hermOfReal t` hermitian, is `2 ^ (-n) ds dt`. -/
theorem lintegral_eq_skewOfReal_add_hermOfReal {K : Matrix n n ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Z : Matrix n n ℂ, K Z =
      (2 ^ card n)⁻¹ * ∫⁻ t : Matrix n n ℝ, ∫⁻ s : Matrix n n ℝ,
        K (skewOfReal s + (2⁻¹ : ℂ) • hermOfReal t) := by
  rw [lintegral_eq_comp_skewAddHerm hK, volume_eq_prod, lintegral_prod]
  · simp only [skewAddHerm_apply]
  · exact (hK.comp skewAddHerm.toLinearMap.continuous_of_finiteDimensional.measurable).aemeasurable

/-! ### Blocks -/

/-- A hermitian matrix of size `n₁ + n₂` is given by its two diagonal blocks, which are hermitian,
and by one block off the diagonal. In the real coordinates `t`, for which the matrix itself is
`hermOfReal t`, this change of variables preserves volume. -/
theorem exists_measurePreserving_hermBlocks [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] (e : n₁ ⊕ n₂ ≃ n) :
    ∃ φ : Matrix n n ℝ ≃ₜ Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ,
      MeasurePreserving φ ∧
      ∀ t : Matrix n n ℝ, φ t = (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
        (hermOfReal t).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr),
        t.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
  -- The map is a linear isometry between Euclidean spaces of the same dimension.
  let f : Matrix n n ℝ →ₗ[ℝ] Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ :=
    { toFun t := (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
        (hermOfReal t).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr),
        t.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))
      map_add' := by simp [hermOfReal, submatrix_add]
      map_smul' := by simp [hermOfReal, submatrix_smul, submatrix_neg, smul_comm I] }
  have h_entry (t : Matrix n n ℝ) (a : n₁) (b : n₂) :
      ‖hermOfReal t (e (.inl a)) (e (.inr b))‖ ^ 2 =
        t (e (.inl a)) (e (.inr b)) ^ 2 + t (e (.inr b)) (e (.inl a)) ^ 2 := by
    simp [hermOfReal, skewOfReal, div_pow, RCLike.norm_sq_eq_def]
    ring
  have h_norm (t : Matrix n n ℝ) :
      ∑ a : n₁, ∑ b : n₁, t (e (.inl a)) (e (.inl b)) ^ 2 +
        (∑ a : n₁, ∑ b : n₂, ‖hermOfReal t (e (.inl a)) (e (.inr b))‖ ^ 2 +
          ∑ a : n₂, ∑ b : n₂, t (e (.inr a)) (e (.inr b)) ^ 2) =
        ∑ a : n, ∑ b : n, t a b ^ 2 := by
    simp only [h_entry, ← e.sum_comp, Fintype.sum_sum_type, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := (Finset.univ : Finset n₂)) (t := (Finset.univ : Finset n₁))]
    ring
  have h_rank : Module.finrank ℝ (Matrix n n ℝ) =
      Module.finrank ℝ (Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ) := by
    simp [Module.finrank_matrix, ← card_congr e]
    ring
  -- The instances for the triple product are found once those for its last two factors are known.
  have : IsAddHaarMeasure (volume : Measure (Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ)) :=
    prod.instIsAddHaarMeasure _ _
  have : BorelSpace (Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ) := Prod.borelSpace
  obtain ⟨φ, hφ, hφ_symm⟩ := HasGaussianIntegral.exists_measurePreserving_equiv f h_norm h_rank
  exact ⟨φ.symm.toContinuousLinearEquiv.toHomeomorph,
    hφ.symm φ.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv, congrFun hφ_symm⟩

end Hermitian

/-- A hermitian matrix `hermOfReal t` of size `n₁ + 1`, with the extra index placed by `e`, is given
by a hermitian block of size `n₁`, by the rest of the column at the extra index and by the real
diagonal entry there. In the real coordinates `t` this change of variables preserves volume. -/
theorem exists_measurePreserving_hermCorner [Fintype n] [Fintype n₁] [DecidableEq n]
    [DecidableEq n₁] (e : n₁ ⊕ Unit ≃ n) :
    ∃ φ : Matrix n n ℝ ≃ₜ Matrix n₁ n₁ ℝ × (n₁ → ℂ) × ℝ,
      MeasurePreserving φ ∧
      ∀ t : Matrix n n ℝ, φ t = (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
        fun a : n₁ ↦ hermOfReal t (e (.inl a)) (e (.inr ())), t (e (.inr ())) (e (.inr ()))) := by
  obtain ⟨φ, φ_vol, φ_apply⟩ := exists_measurePreserving_hermBlocks e
  refine ⟨φ.trans ((Homeomorph.refl _).prodCongr (toCorner n₁).symm), ((MeasurePreserving.id _).prod
    (measurePreserving_toCorner.symm (toCorner n₁).toMeasurableEquiv)).comp φ_vol, fun t ↦ ?_⟩
  simp [φ_apply]; rfl

end New

end
end
end

/-!
# The polar formula for the Gram map on bases

Let `J` be a hermitian involution of size `r` and `G = U(J)`, with the compact dual Haar measure
`dγ` (`New.haarU`). A basis `Y` whose Gram matrix `T = Yᴴ J Y` is near `J` is `γ σ(T)`, with `γ` in
`G` and `σ` a local section of the Gram map (`New.exists_isGramSection`).

* `New.IsGramSection.lintegral_eq`: the polar formula `dY = (vol U(r) / 2 ^ r) dγ dT`, where
  `vol U(r)` is `New.volU r`. The Jacobian is computed on tangent vectors: `Yᴴ J dY` has hermitian
  part `dT / 2`, and for fixed `T` it is `σᴴ (J γ⁻¹ dγ) σ`, which is skew-hermitian. The constant
  does not depend on the signature of `J`.

Notions from other files:
* `IsHermitianInvolution J`: the complex matrix `J` is hermitian and `J * J = 1`;
* `U J`: the group of `g` with `gᴴ * J * g = J`, where `volume` is the Haar measure `New.haarU J`,
  normalized so that it has mass `1` for `J = 1`;
* `gramCoords J Y`: the real coordinates of the hermitian matrix `Yᴴ * J * Y`;
* `cayleyChart J`: the Cayley parametrization of almost all of `U J` by real matrices `y` with
  `(cayleyDenom J y).det ≠ 0`; the density of the Haar measure there is `cayleyDensity J y` divided
  by `volU r`;
* `logDerivU (cayleyChart J) y`: the linear map `v ↦ γᴴ J dγ(v)`, with `γ = cayleyChart J y`;
* `skewAddHerm`: the linear equivalence from pairs of real matrices to complex matrices; its inverse
  sends `X` to the coordinates of the hermitian matrix `X + Xᴴ` and of the skew-hermitian matrix
  `(X - Xᴴ) / 2`.

## Relation to the literature

Known result: the invariant measure `dY / dT` on tuples of vectors with a given Gram matrix. Source:
C. L. Siegel, Über die analytische Theorie der quadratischen Formen, Ann. of Math. 36 (1935).
-/

@[expose] public section

noncomputable section

namespace New

open Matrix MeasureTheory Measure Complex Fintype ENNReal Norms.L2Operator Filter Topology

variable {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
  {J : Matrix ι ι ℂ} [IsHermitianInvolution J]

/-- The Haar measure of `U J` is invariant under right translations. -/
instance : (volume (α := U J)).IsMulRightInvariant :=
  ⟨fun g ↦ (measurePreserving_haarU 1 g 1 (.mulRight g)
    (by simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 g.property) (by simp)).map_eq⟩

theorem IsHermitianInvolution.norm_det : ‖J.det‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  rw [← norm_pow, sq, ← det_mul, IsHermitianInvolution.mul_self, det_one, norm_one]

/-- Left multiplication by an element of the unitary group `U J` preserves Lebesgue measure on
tuples of vectors. -/
theorem measurePreserving_U_mul (g : U J) :
    MeasurePreserving fun y : Matrix ι n ℂ ↦ (g : Matrix ι ι ℂ) * y := by
  refine ⟨by fun_prop, ext_of_lintegral _ fun K hK ↦ ?_⟩
  rw [lintegral_map hK (by fun_prop), lintegral_eq_det_mul_comp_mul_mul (P := (g : Matrix ι ι ℂ))
    (Q := 1) (norm_pos_iff.1 (by simp)) (by simp) hK]
  simp [← ofReal_norm]

omit [Fintype n] [IsHermitianInvolution J] in
theorem gramCoords_U_mul (g : U J) (Y : Matrix ι n ℂ) :
    gramCoords J ((g : Matrix ι ι ℂ) * Y) = gramCoords J Y := by
  rw [gramCoords, U.gram_invariant, gramCoords]

/-- Almost every element `g` of `U(J)`, for its Haar measure, has no eigenvalue `-1`. -/
theorem ae_isUnit_add_one : ∀ᵐ g : U J, IsUnit ((g : Matrix ι ι ℂ) + 1) := by
  have h_chart : ∀ᵐ g : U J, ∃ y, (cayleyDenom J y).det ≠ 0 ∧ cayleyChart J y = g :=
    measurableEmbedding_cayleyChart.ae_map_iff.2 (.of_forall fun ⟨y, hy⟩ ↦ ⟨y, hy, rfl⟩)
  filter_upwards [h_chart]
  rintro _ ⟨y, hy, rfl⟩
  have h_eq : (cayleyChart J y : Matrix ι ι ℂ) + 1 = (2 : ℂ) • (cayleyDenom J y)⁻¹ :=
    sub_add_cancel _ _
  simp [h_eq, isUnit_iff_isUnit_det, hy]

variable (J) in
/-- The map `σ` is a differentiable section of the Gram map over the open set `V` of real
coordinates `t` of hermitian matrices, and its values there are bases. -/
structure IsGramSection (V : Set (Matrix ι ι ℝ)) (σ : Matrix ι ι ℝ → Matrix ι ι ℂ) : Prop where
  /-- The set `V` is open. -/
  isOpen : IsOpen V
  /-- The map `σ` is measurable on the whole space. -/
  measurable : Measurable σ
  /-- The map `σ` is differentiable on `V`. -/
  differentiableAt {t : Matrix ι ι ℝ} : t ∈ V → DifferentiableAt ℝ σ t
  /-- For `t` in `V` the Gram matrix of `σ t` has the coordinates `t`. -/
  gramCoords_eq {t : Matrix ι ι ℝ} : t ∈ V → gramCoords J (σ t) = t
  /-- For `t` in `V` the matrix `σ t` is invertible. -/
  isUnit {t : Matrix ι ι ℝ} : t ∈ V → IsUnit (σ t)

variable (J) in
/-- There are an open set `V` of coordinates of Gram matrices, containing those of `1ᴴ * J * 1 = J`,
and a differentiable section of the Gram map over `V` through the standard basis `1`. -/
theorem exists_isGramSection :
    ∃ (V : Set (Matrix ι ι ℝ)) (σ : Matrix ι ι ℝ → Matrix ι ι ℂ),
      IsGramSection J V σ ∧
      gramCoords J (1 : Matrix ι ι ℂ) ∈ V ∧
      σ (gramCoords J (1 : Matrix ι ι ℂ)) = 1 := by
  -- On the slice `β x = 1 + J X / 2`, `X = hermOfReal x`, the Gram map has derivative the identity
  -- at `0`. The inverse function theorem inverts it near `0`.
  obtain ⟨N, hN⟩ : ∃ N : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℂ,
      ∀ x : Matrix ι ι ℝ, N x = J * ((2⁻¹ : ℂ) • hermOfReal x) :=
    ⟨(LinearMap.mulLeft ℝ J ∘ₗ ((2⁻¹ : ℂ) • -I • skewOfReal)).toContinuousLinearMap, fun _ ↦ rfl⟩
  let β (x : Matrix ι ι ℝ) : Matrix ι ι ℂ := 1 + N x
  have hβ : ContDiff ℝ 1 β := contDiff_const.add N.contDiff
  have hβ_zero : β 0 = 1 := by simp [β]
  have h_smooth : ContDiffAt ℝ 1 (fun x ↦ gramCoords J (β x)) 0 :=
    ((contDiff_gramCoords J).comp hβ).contDiffAt
  have h_deriv : HasFDerivAt (fun x ↦ gramCoords J (β x))
      (ContinuousLinearEquiv.refl ℝ (Matrix ι ι ℝ) : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ) 0 := by
    obtain ⟨D, hD, hD_apply⟩ :=
      hasFDerivAt_gramCoords J (σ := β) (t := 0) (N.hasFDerivAt.const_add 1)
    refine hD.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
    have h_sum : (β 0)ᴴ * J * N v + (N v)ᴴ * J * β 0 = hermOfReal v := by
      have h_left : (β 0)ᴴ * J * N v = (2⁻¹ : ℂ) • hermOfReal v := by
        simp [hN, hβ_zero, ← Matrix.mul_assoc, IsHermitianInvolution.mul_self]
      have h_right : (N v)ᴴ * J * β 0 = (2⁻¹ : ℂ) • hermOfReal v := by
        simp [hN, hβ_zero, Matrix.mul_assoc _ J J, IsHermitianInvolution.mul_self,
          IsHermitianInvolution.isHermitian.eq, conjTranspose_smul]
      rw [h_left, h_right]
      module
    rw [hD_apply, h_sum, skewCoords_I_smul_hermOfReal]
    rfl
  let σ (t : Matrix ι ι ℝ) : Matrix ι ι ℂ := β (h_smooth.localInverse h_deriv one_ne_zero t)
  have hσ_smooth : ContDiffAt ℝ 1 σ (gramCoords J (β 0)) :=
    hβ.contDiffAt.comp _ (h_smooth.to_localInverse h_deriv one_ne_zero)
  have hσ_base : σ (gramCoords J (β 0)) = 1 :=
    (congrArg β (h_smooth.localInverse_apply_image h_deriv one_ne_zero)).trans hβ_zero
  have h_near : ∀ᶠ t in 𝓝 (gramCoords J (β 0)),
      DifferentiableAt ℝ σ t ∧ gramCoords J (σ t) = t ∧ IsUnit (σ t) := by
    filter_upwards [hσ_smooth.eventually (by simp),
      (h_smooth.hasStrictFDerivAt h_deriv one_ne_zero).eventually_right_inverse,
      hσ_smooth.continuousAt.eventually_mem (Units.isOpen.mem_nhds (by simp [hσ_base]))]
      with t h_diff h_inv h_unit
    exact ⟨h_diff.differentiableAt one_ne_zero, h_inv, h_unit⟩
  rw [hβ_zero] at h_near hσ_base
  obtain ⟨V, hV, hV_open, h_base⟩ := eventually_nhds_iff.1 h_near
  -- Outside `V` put `σ = 1`, to make it measurable.
  classical
  choose h_diff h_gram h_unit using hV
  have h_eq : Set.EqOn (V.piecewise σ 1) σ V := V.piecewise_eqOn σ 1
  exact ⟨V, V.piecewise σ 1,
    { isOpen := hV_open
      measurable := ContinuousOn.measurable_piecewise
        (fun t ht ↦ (h_diff t ht).continuousAt.continuousWithinAt) continuousOn_const
        hV_open.measurableSet
      differentiableAt ht :=
        (h_diff _ ht).congr_of_eventuallyEq (h_eq.eventuallyEq_of_mem (hV_open.mem_nhds ht))
      gramCoords_eq ht := by rw [h_eq ht, h_gram _ ht]
      isUnit ht := by simpa only [h_eq ht] using h_unit _ ht },
    h_base, (h_eq h_base).trans hσ_base⟩

namespace IsGramSection

variable {V S : Set (Matrix ι ι ℝ)} {σ : Matrix ι ι ℝ → Matrix ι ι ℂ}

omit [IsHermitianInvolution J] in
/-- The identity `gramCoords J (σ t) = t` of a section, differentiated at `t ∈ V` in the
direction `v`. -/
theorem skewCoords_fderiv_gram (hσ : IsGramSection J V σ) {t : Matrix ι ι ℝ} (ht : t ∈ V)
    (v : Matrix ι ι ℝ) :
    skewCoords (I • ((σ t)ᴴ * J * fderiv ℝ σ t v + (fderiv ℝ σ t v)ᴴ * J * σ t)) = v := by
  obtain ⟨T, hT, hT_apply⟩ := hasFDerivAt_gramCoords J (hσ.differentiableAt ht).hasFDerivAt
  have hT_id : T = .id ℝ (Matrix ι ι ℝ) :=
    hT.unique ((hasFDerivAt_id t).congr_of_eventuallyEq
      (eventually_of_mem (hσ.isOpen.mem_nhds ht) fun _ ↦ hσ.gramCoords_eq))
  rw [← hT_apply, hT_id, ContinuousLinearMap.id_apply]

omit [IsHermitianInvolution J] in
/-- A section of the Gram map over `V` restricts to a section over each open subset of `V`. -/
theorem mono (hσ : IsGramSection J V σ) (hS : IsOpen S) (hSV : S ⊆ V) : IsGramSection J S σ :=
  ⟨hS, hσ.measurable, fun ht ↦ hσ.differentiableAt (hSV ht), fun ht ↦ hσ.gramCoords_eq (hSV ht),
    fun ht ↦ hσ.isUnit (hSV ht)⟩

omit [IsHermitianInvolution J] in
/-- Multiplying the values of a linear map `D` on the left by `P` multiplies its Jacobian, read in
the coordinates `skewAddHerm.symm`, by `‖det P‖ ^ (2 r)`, where `r` is the size of the matrices. -/
theorem abs_det_skewAddHerm_mulLeft_comp (P : Matrix ι ι ℂ)
    (D : Matrix ι ι ℝ × Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℂ) :
    |(skewAddHerm.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℝ P ∘ₗ D).det| =
      ‖P.det‖ ^ (2 * card ι) * |(skewAddHerm.symm.toLinearMap ∘ₗ D).det| := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ := mulRightLinearMap ι ℝ 1 ∘ₗ mulLeftLinearMap ι ℝ P
  have h_factor : skewAddHerm.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℝ P ∘ₗ D =
      (skewAddHerm.symm.toLinearMap ∘ₗ L ∘ₗ skewAddHerm.toLinearMap) *
        (skewAddHerm.symm.toLinearMap ∘ₗ D) :=
    LinearMap.ext fun p ↦ by simp [L]
  have h_conj : (skewAddHerm.symm.toLinearMap ∘ₗ L ∘ₗ skewAddHerm.toLinearMap).det = L.det :=
    LinearMap.det_conj L skewAddHerm.symm
  rw [h_factor, map_mul, h_conj, det_mulLeft_mulRight_real]
  simp

/-- Let `σ` be a differentiable section of the Gram map over the open set `V` (`IsGramSection`), and
let `γ = cayleyChart J`, with `cayleyDenom J y` invertible. At `t ∈ V`, let
`T(t', s) = σᴴ (γᴴ J dγ_y s) σ + σᴴ J dσ_t t'`. In coordinates via `skewAddHerm.symm`
(`Z ↦ (Z + Zᴴ, (Z - Zᴴ)/2)`), `|det T| = ‖det σ t‖ ^ (2 card ι) · cayleyDensity J y`. -/
theorem abs_det_skewAddHerm_symm_comp (hσ : IsGramSection J V σ) {t y : Matrix ι ι ℝ}
    (ht : t ∈ V) (hy : (cayleyDenom J y).det ≠ 0)
    {T : Matrix ι ι ℝ × Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℂ}
    (hT : ∀ p : Matrix ι ι ℝ × Matrix ι ι ℝ, T p =
      (σ t)ᴴ * logDerivU (cayleyChart J) y p.2 * σ t + (σ t)ᴴ * J * fderiv ℝ σ t p.1) :
    |(skewAddHerm.symm.toLinearMap ∘ₗ T).det| =
      ‖(σ t).det‖ ^ (2 * card ι) * cayleyDensity J y := by
  -- The first summand is skew-hermitian and the hermitian part of the second is `dt / 2`.
  obtain ⟨h_diff, h_density⟩ := abs_det_logDerivU_cayleyChart hy
  let W (v : Matrix ι ι ℝ) : Matrix ι ι ℂ := (σ t)ᴴ * logDerivU (cayleyChart J) y v * σ t
  have h_skew (v : Matrix ι ι ℝ) : (W v)ᴴ = -W v := by
    simp [W, conjTranspose_logDerivU h_diff, Matrix.mul_assoc]
  have h_herm (p : Matrix ι ι ℝ × Matrix ι ι ℝ) : (skewAddHerm.symm (T p)).1 = p.1 := by
    have h_sum : T p + (T p)ᴴ =
        (σ t)ᴴ * J * fderiv ℝ σ t p.1 + (fderiv ℝ σ t p.1)ᴴ * J * σ t := by
      rw [hT, conjTranspose_add, h_skew]
      simp only [W, conjTranspose_mul, conjTranspose_conjTranspose,
        IsHermitianInvolution.isHermitian.eq, Matrix.mul_assoc]
      abel
    rw [skewAddHerm_symm_apply, h_sum]
    exact hσ.skewCoords_fderiv_gram ht p.1
  let B : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ := skewCoords ∘ₗ LinearMap.mulLeftRight ℝ ((σ t)ᴴ, σ t) ∘ₗ
    skewOfReal ∘ₗ skewCoords ∘ₗ logDerivU (cayleyChart J) y
  have h_second (v : Matrix ι ι ℝ) : (skewAddHerm.symm (T (0, v))).2 = B v := by
    have h_half : (2⁻¹ : ℂ) • (T (0, v) - (T (0, v))ᴴ) = W v := by
      simp [hT, h_skew, ← two_smul ℂ, smul_smul, W]
    simp [B, W, skewAddHerm_symm_apply, h_half,
      skewOfReal_skewCoords (conjTranspose_logDerivU h_diff v)]
  rw [Haar.det_eq_mul_of_fst_eq_of_snd_eq LinearMap.id B h_herm h_second, LinearMap.det_id,
    one_mul, ← h_density]
  exact abs_det_skew_congruence (.refl ℝ (Matrix ι ι ℝ)) (σ t)
    (skewCoords ∘ₗ logDerivU (cayleyChart J) y)

/-- Let `J` be a hermitian involution, `σ` a section of the Gram map over `V`, `t ∈ V`, and `y` real
with `det (cayleyDenom J y) ≠ 0`. Then the map `(t, y) ↦ γ(y) σ(t)`, with `γ = cayleyChart J` the
Cayley chart, is differentiable at `(t, y)`. The absolute value of its Jacobian is the density
`New.cayleyDensity J y`, which is the absolute Jacobian of `J γ⁻¹ dγ`. The Jacobian is read in the
real coordinates `skewAddHerm.symm`, which send a complex matrix `Z` to the coordinates of the
hermitian matrix `Z + Zᴴ` and of the skew-hermitian matrix `(Z - Zᴴ) / 2`. -/
theorem exists_hasFDerivAt_cayleyChart_mul (hσ : IsGramSection J V σ) {t y : Matrix ι ι ℝ}
    (ht : t ∈ V) (hy : (cayleyDenom J y).det ≠ 0) :
    ∃ D : (Matrix ι ι ℝ × Matrix ι ι ℝ) →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt
        (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) D
        (t, y) ∧
      |(skewAddHerm.symm.toLinearMap ∘ₗ D.toLinearMap).det| = cayleyDensity J y := by
  -- Multiplication by `Yᴴ J`, with `Y = γ(y) σ(t)`, has the Jacobian `‖det σ‖ ^ (2 r)`, which is
  -- also the factor in the Jacobian of `Yᴴ J dY`.
  let g : Matrix ι ι ℂ := cayleyChart J y
  have h_fst := (hσ.differentiableAt ht).hasFDerivAt.comp (f := Prod.fst) (t, y) hasFDerivAt_fst
  have h_snd := (differentiableAtU_cayleyChart hy).hasFDerivAt.comp (f := Prod.snd) (t, y)
    hasFDerivAt_snd
  obtain ⟨D, hD, hD_apply⟩ : ∃ D, HasFDerivAt
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) D (t, y) ∧
      ∀ p, D p = g * fderiv ℝ σ t p.1 +
        fderiv ℝ (fun x ↦ (cayleyChart J x : Matrix ι ι ℂ)) y p.2 * σ t :=
    ⟨_, h_snd.mul' h_fst, fun _ ↦ rfl⟩
  refine ⟨D, hD, ?_⟩
  set P : Matrix ι ι ℂ := (g * σ t)ᴴ * J
  have h_tangent (p : Matrix ι ι ℝ × Matrix ι ι ℝ) : P * D p =
      (σ t)ᴴ * logDerivU (cayleyChart J) y p.2 * σ t + (σ t)ᴴ * J * fderiv ℝ σ t p.1 := by
    rw [hD_apply, Matrix.mul_add, U.gram_invariant, add_comm]
    -- By definition the logarithmic derivative is v ↦ γᴴ * J * dγ v.
    simp [P, g, logDerivU, conjTranspose_mul, Matrix.mul_assoc]
  have h_block : |(skewAddHerm.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℝ P ∘ₗ D.toLinearMap).det| =
      ‖(σ t).det‖ ^ (2 * card ι) * cayleyDensity J y :=
    hσ.abs_det_skewAddHerm_symm_comp ht hy h_tangent
  rw [abs_det_skewAddHerm_mulLeft_comp,
    show ‖P.det‖ = ‖(σ t).det‖ by simp [P, g, IsHermitianInvolution.norm_det]] at h_block
  have h_det : (σ t).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (hσ.isUnit ht)).ne_zero
  exact mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 h_det)) h_block

/-- Let `J` be a hermitian involution, and let `σ` be a differentiable section over the open set `V`
of the Gram map `gramCoords J` (the real coordinates of `Yᴴ J Y`), whose values `σ t` are
invertible. Then every complex matrix `Y` with `t = gramCoords J Y` in `V` is `γ σ(t)` for some `γ`
in `U(J)`. -/
theorem exists_mul_eq (hσ : IsGramSection J V σ) {Y : Matrix ι ι ℂ} (hY : gramCoords J Y ∈ V) :
    ∃ γ : U J, (γ : Matrix ι ι ℂ) * σ (gramCoords J Y) = Y := by
  set Z : Matrix ι ι ℂ := σ (gramCoords J Y)
  have h_unit : IsUnit Z.det := (isUnit_iff_isUnit_det Z).1 (hσ.isUnit hY)
  have h_gram : Yᴴ * J * Y = Zᴴ * J * Z := by
    simp only [← hermOfReal_gramCoords IsHermitianInvolution.isHermitian, Z, hσ.gramCoords_eq hY]
  have h_mem : (Y * Z⁻¹)ᴴ * J * (Y * Z⁻¹) = J := by
    rw [gram_mul, h_gram, ← gram_mul, mul_nonsing_inv Z h_unit, conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  exact ⟨U.of IsHermitianInvolution.isUnit _ h_mem, nonsing_inv_mul_cancel_right Z Y h_unit⟩

/-- Let `J` be a hermitian involution (`Jᴴ = J`, `J² = 1`). Let `σ` be a section of the Gram map
`gramCoords J` over the open set `V`: a differentiable map with invertible values, where
`gramCoords J Y` is the real coordinates, in the sense of `hermOfReal`, of `Yᴴ J Y`. For
Lebesgue-almost every complex matrix `Y` with `t = gramCoords J Y` in `V`, written `Y = γ σ(t)` with
`γ` in `U(J)`, the matrix `Y + σ(t) = (γ + 1) σ(t)` is invertible; that is, `γ` has no eigenvalue
`-1`. -/
theorem ae_isUnit_add (hσ : IsGramSection J V σ) :
    ∀ᵐ Y : Matrix ι ι ℂ, gramCoords J Y ∈ V → IsUnit (Y + σ (gramCoords J Y)) := by
  -- For each `Y` the claim holds at `g Y` for almost every `g` in `U(J)`. By Fubini's theorem it
  -- holds at almost every `g Y` for some `g`, and `g` preserves Lebesgue measure.
  let B : Set (Matrix ι ι ℂ) := {Y | gramCoords J Y ∈ V → IsUnit (Y + σ (gramCoords J Y))}
  have h_gram : Measurable (gramCoords J) := (continuous_gramCoords (n := ι) J).measurable
  have hB : MeasurableSet B := (h_gram hσ.isOpen.measurableSet).imp
    ((measurable_id.add (hσ.measurable.comp h_gram)) Units.isOpen.measurableSet)
  have h_orbit (Y : Matrix ι ι ℂ) : ∀ᵐ g : U J, (g : Matrix ι ι ℂ) * Y ∈ B := by
    by_cases hY : gramCoords J Y ∈ V
    · obtain ⟨γ, hγ⟩ := hσ.exists_mul_eq hY
      have h_translate : ∀ᵐ g : U J, IsUnit (((g * γ : U J) : Matrix ι ι ℂ) + 1) :=
        (measurePreserving_mul_right volume γ).quasiMeasurePreserving.ae ae_isUnit_add_one
      filter_upwards [h_translate] with g hg _
      have h_factor : (g : Matrix ι ι ℂ) * Y + σ (gramCoords J Y) =
          (((g * γ : U J) : Matrix ι ι ℂ) + 1) * σ (gramCoords J Y) := by
        simp [Matrix.add_mul, Matrix.mul_assoc, hγ]
      rw [gramCoords_U_mul, h_factor]
      exact hg.mul (hσ.isUnit hY)
    · simp [B, gramCoords_U_mul, hY]
  have h_comm : ∀ᵐ g : U J, ∀ᵐ Y : Matrix ι ι ℂ, (g : Matrix ι ι ℂ) * Y ∈ B :=
    (ae_ae_comm (p := fun Y (g : U J) ↦ (g : Matrix ι ι ℂ) * Y ∈ B)
      (((isClosedEmbedding_U.measurable.comp measurable_snd).mul measurable_fst) hB)).1
        (.of_forall h_orbit)
  obtain ⟨g, hg⟩ := h_comm.exists
  rw [← (measurePreserving_U_mul g).map_eq]
  exact (ae_map_iff (measurePreserving_U_mul g).measurable.aemeasurable hB).2 hg

/-- On `V` times the domain of the Cayley chart the map `(t, y) ↦ γ(y) σ(t)`, with `γ` the Cayley
chart, is injective. -/
theorem injOn_cayleyChart_mul (hσ : IsGramSection J V σ) :
    (V ×ˢ {y : Matrix ι ι ℝ | (cayleyDenom J y).det ≠ 0}).InjOn
      fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1 := by
  rintro ⟨t, y⟩ ⟨ht, hy⟩ ⟨t', y'⟩ ⟨ht', hy'⟩ h_image
  obtain rfl : t = t' := by
    simpa only [gramCoords_U_mul, hσ.gramCoords_eq ht, hσ.gramCoords_eq ht'] using
      congrArg (gramCoords J) h_image
  exact Prod.ext rfl (cayleyChart_injOn hy hy'
    (Subtype.ext (Units.ext ((hσ.isUnit ht).mul_right_cancel h_image))))

/-- Up to a null set, the matrices `Y` with `gramCoords J Y` in `V` are the products `γ(y) σ(t)`
with `t` in `V` and `y` in the domain of the Cayley chart `γ`. -/
theorem preimage_gramCoords_ae_eq_image (hσ : IsGramSection J V σ) :
    gramCoords J ⁻¹' V =ᵐ[volume]
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) ''
        (V ×ˢ {y : Matrix ι ι ℝ | (cayleyDenom J y).det ≠ 0}) := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hσ.ae_isUnit_add] with Y h_unit
  refine ⟨fun hY ↦ ?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := hσ.exists_mul_eq hY
    have hγ_unit : IsUnit ((γ : Matrix ι ι ℂ) + 1) :=
      isUnit_of_mul_isUnit_left (y := σ (gramCoords J Y))
        (by simpa only [Matrix.add_mul, hγ, Matrix.one_mul] using h_unit hY)
    obtain ⟨h_dom, h_chart⟩ := cayleyChart_cayleyChartInv γ hγ_unit
    exact ⟨(gramCoords J Y, cayleyChartInv γ), ⟨hY, h_dom⟩, by simp only [h_chart, hγ]⟩
  · rintro ⟨⟨t, y⟩, ⟨ht, -⟩, rfl⟩
    simpa only [Set.mem_preimage, gramCoords_U_mul, hσ.gramCoords_eq ht] using ht

/-- The polar formula in the Cayley chart. Let `J` be a hermitian involution, `gramCoords J Y` the
real coordinates of the Gram matrix `Yᴴ J Y`, and `σ` a section of the Gram map over `V`. For
measurable `K ≥ 0`, the integral of `K` over all of `gramCoords J ⁻¹' V` equals `2 ^ (-r)`, with
`r = card ι`, times the integral of `cayleyDensity J y * K (cayleyChart J y * σ t)` over `t ∈ V` and
`y` with `det (cayleyDenom J y) ≠ 0`. Here `cayleyDensity J y` is the Jacobian of the Cayley chart
`γ = cayleyChart J`. -/
theorem lintegral_eq_cayleyChart_mul (hσ : IsGramSection J V σ) {K : Matrix ι ι ℂ → ℝ≥0∞}
    (hK : Measurable K) :
    ∫⁻ Y : Matrix ι ι ℂ in gramCoords J ⁻¹' V, K Y =
      (2 ^ card ι)⁻¹ * ∫⁻ p : Matrix ι ι ℝ × Matrix ι ι ℝ in
          V ×ˢ {y : Matrix ι ι ℝ | (cayleyDenom J y).det ≠ 0},
        ENNReal.ofReal (cayleyDensity J p.2) * K ((cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1) := by
  -- The map `(t, y) ↦ γ(y) σ(t)` is injective on `A` and its image is the domain of integration up
  -- to a null set. Change variables along it, in the coordinates `skewAddHerm.symm`.
  set A : Set (Matrix ι ι ℝ × Matrix ι ι ℝ) := V ×ˢ {y | (cayleyDenom J y).det ≠ 0}
  let Φ (p : Matrix ι ι ℝ × Matrix ι ι ℝ) : Matrix ι ι ℂ :=
    (cayleyChart J p.2 : Matrix ι ι ℂ) * σ p.1
  have hA : MeasurableSet A :=
    (hσ.isOpen.prod continuous_cayleyDenom.matrix_det.isOpen_support).measurableSet
  have h_inj : A.InjOn Φ := hσ.injOn_cayleyChart_mul
  have h_jac : ∀ p ∈ A, ∃ D : (Matrix ι ι ℝ × Matrix ι ι ℝ) →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt Φ D p ∧
      |(skewAddHerm.symm.toLinearMap ∘ₗ D.toLinearMap).det| = cayleyDensity J p.2 :=
    fun _ ⟨ht, hy⟩ ↦ hσ.exists_hasFDerivAt_cayleyChart_mul ht hy
  choose! D hD hD_det using h_jac
  let e : Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℝ × Matrix ι ι ℝ := skewAddHerm.symm.toContinuousLinearEquiv
  calc ∫⁻ Y in gramCoords J ⁻¹' V, K Y = ∫⁻ Y in Φ '' A, K Y :=
        setLIntegral_congr hσ.preimage_gramCoords_ae_eq_image
    _ = (2 ^ card ι)⁻¹ * ∫⁻ p in (e ∘ Φ) '' A, K (e.symm p) := by
      have h_meas : MeasurableSet (Φ '' A) := hA.image_of_continuousOn_injOn
        (fun p hp ↦ (hD p hp).continuousAt.continuousWithinAt) h_inj
      rw [← lintegral_indicator h_meas, lintegral_eq_comp_skewAddHerm (hK.indicator h_meas),
        Set.image_comp, e.image_eq_preimage_symm,
        ← lintegral_indicator (e.symm.continuous.measurable h_meas)]
      simp only [← Function.comp_def K]
      rfl
    _ = (2 ^ card ι)⁻¹ * ∫⁻ p in A, ENNReal.ofReal (cayleyDensity J p.2) * K (Φ p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA (fun p hp ↦
        (e.hasFDerivAt.comp p (hD p hp)).hasFDerivWithinAt) (e.injective.comp_injOn h_inj)]
      congr 1
      refine setLIntegral_congr_fun hA fun p hp ↦ ?_
      rw [← hD_det p hp, Function.comp_apply, e.symm_apply_apply]
      -- The two determinants are those of one linear map, once as a continuous map.
      rfl

/-- The polar formula. Let `J` be a hermitian involution, let `σ` be a differentiable section with
invertible values over the open set `V` of the Gram map `gramCoords J` (the real coordinates, in the
sense of `hermOfReal`, of `Yᴴ J Y`), and let `K ≥ 0` be measurable. On the matrices `Y = γ σ(t)`
with `γ` in `U(J)` and `t = gramCoords J Y` in `V`, Lebesgue measure is
`dY = (vol U(r) / 2 ^ r) dγ dt`, where `r` is the size of the matrices, `vol U(r) = New.volU r` and
`dγ` is the compact dual Haar measure `New.haarU J`, the `volume` of `U J`; that is,
`∫ Y in gramCoords J ⁻¹' V, K Y` equals that constant times `∫ t in V, ∫ γ, K (γ σ(t))`. -/
theorem lintegral_eq (hσ : IsGramSection J V σ) {K : Matrix ι ι ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Y : Matrix ι ι ℂ in gramCoords J ⁻¹' V, K Y =
      ENNReal.ofReal (volU (card ι) / 2 ^ card ι) *
        ∫⁻ t : Matrix ι ι ℝ in V, ∫⁻ g : U J, K ((g : Matrix ι ι ℂ) * σ t) := by
  have hσ_meas : Measurable σ := hσ.measurable
  have h_const (x : ℝ) : (2 ^ card ι)⁻¹ * ENNReal.ofReal x =
      ENNReal.ofReal (volU (card ι) / 2 ^ card ι) * ENNReal.ofReal (x / volU (card ι)) := by
    have h_vol : 0 < volU (card ι) := volU_pos _
    rw [← ENNReal.ofReal_mul (by positivity),
      show volU (card ι) / 2 ^ card ι * (x / volU (card ι)) = x / 2 ^ card ι by field_simp,
      ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.div_eq_inv_mul]
  have h_inner (t : Matrix ι ι ℝ) :
      (2 ^ card ι)⁻¹ * ∫⁻ y : Matrix ι ι ℝ in {y | (cayleyDenom J y).det ≠ 0},
          ENNReal.ofReal (cayleyDensity J y) * K ((cayleyChart J y : Matrix ι ι ℂ) * σ t) =
        ENNReal.ofReal (volU (card ι) / 2 ^ card ι) *
          ∫⁻ g : U J, K ((g : Matrix ι ι ℂ) * σ t) := by
    simp (disch := finiteness) only [lintegral_eq_cayleyChart, ← lintegral_const_mul',
      ← mul_assoc, h_const]
  rw [hσ.lintegral_eq_cayleyChart_mul hK, volume_eq_prod, ← prod_restrict,
    lintegral_prod _ (by fun_prop)]
  simp (disch := finiteness) only [← lintegral_const_mul', h_inner]

end IsGramSection

end New

end
end
end

/-!
# Haar measure on U(J): U(n) has mass one, covering bounds for norm balls

The measure `volume` on `U J` is the compact dual measure `New.haarU J`, normalised by
`New.volU n = ∏ i < n, 2 π ^ (i + 1) / i!`, the product of the areas of the unit spheres of
`ℂ, …, ℂ ^ n`. The first part shows that U(n) has mass one, by computing the image of Lebesgue
measure under the Gram map in two ways. For the second part let `J` be a hermitian involution of
size `n`, `j : S →* U J` a proper homomorphism, and `ν` a right invariant measure on `S` that is
finite on compact sets. Then norm balls are compared by a covering argument, with operator norms
throughout.

## Main definitions and results

* `New.exists_hasGramDensity`: near the identity, the image of Lebesgue measure under the
  Gram map `Y ↦ Yᴴ Y` of square matrices is `volU n / 2 ^ n` times Lebesgue measure. One column
  ranges over a sphere, and the parts of the other columns orthogonal to it form a square matrix of
  size `n - 1`.
* `New.isProbabilityMeasure_haarU`: for `J = 1` the measure has mass one, by comparison with the
  polar formula `New.IsGramSection.lintegral_eq`. The same holds for the sign matrix with all signs
  equal to 1.
* `New.DiscreteSeries.measure_ball_le_covering`: for `D, R ≥ 1` the set `‖j s * y‖ ≤ R` has at most
  `(3 D R²) ^ (2 n²)` times the measure of the ball `‖j s - 1‖ ≤ 1 / D`.
* `New.DiscreteSeries.integral_decay_le`, `New.DiscreteSeries.lintegral_decay_le`: for `n ≥ 1` and a
  natural number `c > 8 n²` the function `(2 / ‖j s * y‖) ^ c` is integrable, with integral at most
  `16 ^ c` times the measure of `‖j s - 1‖ ≤ 1`.

Notions from other files:
* `New.gramCoords J Y`: the real coordinates `skewCoords (I • (Yᴴ J Y))` of the hermitian matrix
  `Yᴴ J Y`: with `x = I • (Yᴴ J Y)` they are `(x a b).re + (x a b).im`, divided by `√2` for `a ≠ b`.
* `New.U J`: the group of matrices `g` with `gᴴ J g = J`; thus `U 1` is the unitary group.
* `New.sphereDensity k r`: the number `2 π ^ k r ^ (k - 1) / (k - 1)!`.

## Relation to the literature

Known result: volume of U(n), polynomial volume growth of U(J).
Here J is any hermitian matrix with J² = 1, and the measure is normalised so that U(n) has mass one.
The covering bound for norm balls holds for any group with a right invariant measure and a
homomorphism to U(J), with an explicit crude constant. Source: L. K. Hua, Harmonic Analysis of
Functions of Several Complex Variables in the Classical Domains (1963), ch. III; I. G. Macdonald,
The volume of a compact Lie group, Invent. Math. 56 (1980); B. Gross, On the motive of a reductive
group, Invent. Math. 130 (1997).
-/

@[expose] public section

/-! ## U(n) has mass one -/

namespace New

open Matrix MeasureTheory Measure Fintype Real Complex Set ComplexOrder

variable {κ n n' : Type} [Fintype κ] [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']

/-- The unitary group of `ℂ^κ` takes a vector to any vector of the same norm. -/
lemma exists_unitary_mulVec_eq [DecidableEq κ]
    (ω : κ → ℂ) {v : κ → ℂ} (h_norm : star ω ⬝ᵥ ω = star v ⬝ᵥ v) :
    ∃ u : U (1 : Matrix κ κ ℂ), (u : Matrix κ κ ℂ) *ᵥ ω = v := by
  obtain rfl | hω := eq_or_ne ω 0
  · exact ⟨1, by simpa [eq_comm (b := v)] using h_norm.symm⟩
  -- Witt's theorem for the one-column matrices of `ω` and `v`
  have hv : v ≠ 0 := fun hv ↦ hω (by simpa [hv] using h_norm)
  obtain ⟨u, hu⟩ : ∃ u : U (1 : Matrix κ κ ℂ),
      (u : Matrix κ κ ℂ) * replicateCol Unit ω = replicateCol Unit v :=
    witt ⟨I, by simp⟩ conjTranspose_one isUnit_one (.of_ne_zero hω) (.of_ne_zero hv)
      (by simpa [← ext_iff, Matrix.mul_apply, dotProduct] using h_norm)
  exact ⟨u, by rwa [← replicateCol_mulVec, replicateCol_inj] at hu⟩

/-- For nonempty `κ` with `k` elements, the set `|ω|² < a` in `ℂ ^ κ` is the ball of radius `√a`, of
volume `(√a) ^ (2 k) π ^ k / k!`. -/
lemma volume_map_normSq_Iio [Nonempty κ] (a : ℝ) :
    volume.map (fun ω : κ → ℂ ↦ ‖star ω ⬝ᵥ ω‖) (Iio a) =
      ENNReal.ofReal √a ^ (2 * card κ) * ENNReal.ofReal (π ^ card κ / (card κ).factorial) := by
  have h_volume : volume {ω : κ → ℂ | (∑ i : κ, ‖ω i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < √a} =
      ENNReal.ofReal √a ^ (2 * card κ) * ENNReal.ofReal (π ^ card κ / (card κ).factorial) := by
    rw [Complex.volume_sum_rpow_lt κ one_le_two √a]
    simp [Real.Gamma_nat_eq_factorial, one_add_one_eq_two]
  rw [← h_volume]
  -- ↓ keeps simp from rewriting inside the square root and the dot product first
  simp (disch := first | positivity | measurability) [preimage, ↓← sqrt_eq_rpow,
    ↓Fock.star_dotProduct_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]

/-- For `k > 0` the integral of `sphereDensity k r / 2` over `[0, a]` is `a ^ k π ^ k / k!`. -/
lemma integral_sphereDensity_div_two {k : ℕ} (hk : 0 < k) (a : ℝ) :
    ∫ r : ℝ in 0..a, sphereDensity k r / 2 = a ^ k * (π ^ k / k.factorial) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp [Nat.factorial_succ, field]

/-- For nonempty `κ` with `k` elements, the map `ω ↦ |ω|²` carries Lebesgue measure on `ℂ ^ κ` to
the measure on `r > 0` with density `sphereDensity k r / 2 = π ^ k r ^ (k - 1) / (k - 1)!`. -/
lemma measurePreserving_normSq_sphereDensity [Nonempty κ] :
    MeasurePreserving (fun ω : κ → ℂ ↦ ‖star ω ⬝ᵥ ω‖) volume
      ((volume.restrict (Ioi 0)).withDensity fun r : ℝ ↦
        ENNReal.ofReal (sphereDensity (card κ) r / 2)) := by
  -- Both measures give the half-line `Iio a` the volume of the ball of radius `√a`.
  refine ⟨by fun_prop, ext_of_generateFrom_of_iUnion _ (fun n : ℕ ↦ Iio (n : ℝ))
    (borel_eq_generateFrom_Iio ℝ) isPiSystem_Iio (iUnion_eq_univ_iff.2 exists_nat_gt) (by simp)
    (fun n ↦ ?_) (forall_mem_range.2 fun a ↦ ?_)⟩
  · rw [volume_map_normSq_Iio]
    finiteness
  have h_inter : Iio a ∩ Ioi 0 = Ioo 0 (√a ^ 2) := by grind
  have h_nonneg : ∀ᵐ r : ℝ ∂volume.restrict (Ioc 0 (√a ^ 2)), 0 ≤ sphereDensity (card κ) r / 2 :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun r ⟨_, _⟩ ↦ by positivity
  rw [volume_map_normSq_Iio, withDensity_apply', restrict_restrict measurableSet_Iio, h_inter,
    restrict_Ioo_eq_restrict_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Ioc (by fun_prop)) h_nonneg,
    ← intervalIntegral.integral_of_le (sq_nonneg _), integral_sphereDensity_div_two card_pos,
    ENNReal.ofReal_mul (by positivity), ← pow_mul, ENNReal.ofReal_pow (by positivity)]

/-- The real coordinates of the hermitian matrix `w wᴴ` of rank at most one, in the same convention
as `New.gramCoords`. -/
noncomputable def outerCoords (w : n → ℂ) : Matrix n n ℝ := skewCoords (I • vecMulVec w (star w))

@[fun_prop]
theorem continuous_outerCoords : Continuous (outerCoords : (n → ℂ) → Matrix n n ℝ) :=
  skewCoords.continuous_of_finiteDimensional.comp (by fun_prop)

/-- The Gram map `Y ↦ gramCoords 1 Y`, the real coordinates of `Yᴴ Y` for square matrices `Y`, has
density `c` on the set `W` of real matrices: on `W` it carries Lebesgue measure to `c` times
Lebesgue measure. -/
def HasGramDensity (W : Set (Matrix n n ℝ)) (c : ENNReal) : Prop :=
  ∀ G : Matrix n n ℝ → ENNReal, Measurable G → G.support ⊆ W →
    ∫⁻ Y : Matrix n n ℂ, G (gramCoords 1 Y) = c * ∫⁻ t : Matrix n n ℝ, G t

/-- Let the index set `n` consist of `n'` and one further index, fix a vector `v` of squared norm
`r > 0` in `ℂ ^ n`, and let the Gram map in size `n'` have the density `c` on `W`. Let `k` be the
number of elements of `n'`. The map that sends `k` vectors `Y` of `ℂ ^ n` to the coordinates `t` of
their Gram matrix and their products `w` with `v` carries Lebesgue measure to `c / r ^ k` times
Lebesgue measure, on the set where `t - outerCoords w / r`, the coordinates of the Gram matrix
minus `w wᴴ / r`, lies in `W`. -/
theorem HasGramDensity.lintegral_conjTranspose_mulVec {W : Set (Matrix n' n' ℝ)} {c : ENNReal}
    (hW : HasGramDensity W c) (e : n' ⊕ Unit ≃ n) {v : n → ℂ} {r : ℝ} (hr : 0 < r)
    (hv : star v ⬝ᵥ v = r) {F : Matrix n' n' ℝ × (n' → ℂ) → ENNReal} (hF : Measurable F)
    (h_supp : ∀ p ∈ F.support, p.1 - r⁻¹ • outerCoords p.2 ∈ W) :
    ENNReal.ofReal (r ^ card n') * ∫⁻ Y : Matrix n n' ℂ, F (gramCoords 1 Y, Yᴴ *ᵥ v) =
      c * ∫⁻ p : Matrix n' n' ℝ × (n' → ℂ), F p := by
  -- Rotate `v` to `√r` times a basis vector. Then `Y` consists of a square matrix `X` and a row
  -- `wᴴ`; its Gram matrix is `Xᴴ X + w wᴴ` and its products with `v` are `√r w`.
  let v₀ : n → ℂ := √r • Pi.single (e (.inr ())) 1
  obtain ⟨u, hu⟩ : ∃ u : U (1 : Matrix n n ℂ), (u : Matrix n n ℂ) *ᵥ v₀ = v :=
    exists_unitary_mulVec_eq v₀ (by simp [v₀, hv, star_trivial, ← ofReal_mul, hr.le])
  let rows : Matrix n' n' ℂ × (n' → ℂ) → Matrix n n' ℂ := fun (X, w) ↦ (joinCol e (Xᴴ, w))ᴴ
  have h_rows : MeasurePreserving fun p ↦ (u : Matrix n n ℂ) * rows p :=
    (measurePreserving_U_mul u).comp <| measurePreserving_conjTranspose.comp <|
      (measurePreserving_joinCol e).comp (measurePreserving_conjTranspose.prod (.id _))
  have h_gram (X : Matrix n' n' ℂ) (w : n' → ℂ) :
      gramCoords 1 ((u : Matrix n n ℂ) * rows (X, w)) = gramCoords 1 X + outerCoords w := by
    have h_sum : (rows (X, w))ᴴ * rows (X, w) = Xᴴ * X + vecMulVec w (star w) := by
      simp [← ext_iff, rows, Matrix.mul_apply, ← e.sum_comp, vecMulVec_apply]
    rw [gramCoords_U_mul]
    simp [gramCoords, outerCoords, h_sum]
  have h_prod (X : Matrix n' n' ℂ) (w : n' → ℂ) :
      ((u : Matrix n n ℂ) * rows (X, w))ᴴ *ᵥ v = √r • w := by
    have h_unitary : (u : Matrix n n ℂ)ᴴ * u = 1 := by
      simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 u.property
    rw [← hu, mulVec_mulVec, conjTranspose_mul, Matrix.mul_assoc, h_unitary]
    simp [funext_iff, v₀, rows, mulVec_smul]
  have h_outer (w : n' → ℂ) : r⁻¹ • outerCoords (√r • w) = outerCoords w := by
    simp [outerCoords, star_trivial, smul_comm I, smul_smul, hr.le, hr.ne']
  -- For fixed `w`, the translate of `F` by `outerCoords w` is supported in `W`.
  have h_inner (w : n' → ℂ) : ∫⁻ X : Matrix n' n' ℂ, F (gramCoords 1 X + outerCoords w, √r • w) =
      c * ∫⁻ t, F (t, √r • w) := by
    rw [hW (fun t ↦ F (t + outerCoords w, √r • w)) (by fun_prop)
        fun t ht ↦ by simpa [h_outer] using h_supp _ ht,
      lintegral_add_right_eq_self fun t ↦ F (t, √r • w)]
  let T : (n' → ℂ) →ₗ[ℝ] n' → ℂ := √r • .id
  have hT : T.det = r ^ card n' := by simp [T, Module.finrank_pi_fintype, pow_mul', hr.le]
  calc _ = ENNReal.ofReal (r ^ card n') *
          ∫⁻ w, ∫⁻ X : Matrix n' n' ℂ, F (gramCoords 1 X + outerCoords w, √r • w) := by
        rw [← h_rows.lintegral_comp (hF.fun_comp (Continuous.measurable (by fun_prop)))]
        simp only [h_gram, h_prod]
        rw [volume_eq_prod, lintegral_prod_symm' _ (by fun_prop)]
    _ = ENNReal.ofReal (r ^ card n') * ∫⁻ w, c * ∫⁻ t, F (t, √r • w) := by simp only [h_inner]
    _ = ∫⁻ w, c * ∫⁻ t, F (t, w) := by
        rw [eq_comm, lintegral_eq_abs_det_mul_comp volume (hT.trans_ne (by positivity))
          (by fun_prop), hT]
        simp [T, abs_of_pos hr]
    _ = c * ∫⁻ p, F p := by
        rw [volume_eq_prod, lintegral_prod_symm' _ hF, lintegral_const_mul c (by fun_prop)]

/-- The step from size `n'` to size `n`, one more than `n'`. Let `φ` be a volume-preserving
homeomorphism that splits the coordinates of the Gram matrix of the columns `(Y, v)` (joined by
`joinCol e`, which puts column `a` of `Y` at index `e (.inl a)` and `v` at index `e (.inr ())`) into
the block `t = gramCoords 1 Y`, the column `w = Yᴴ v` and the corner `r = |v|²`. Suppose the Gram
map `Y ↦ gramCoords 1 Y` (real coordinates of `Yᴴ Y`) carries Lebesgue measure on `W` to `c` times
Lebesgue measure in size `n'`. Then in size `n` it does so with constant `sphereDensity (card n)
1 / 2 * c = (π^k / (k−1)!) c`, where `k = card n`, on the set where `r > 0` and
`t - outerCoords w / r` lies in `W`; here `outerCoords w` is the real coordinates of `w wᴴ`. -/
theorem HasGramDensity.succ {W : Set (Matrix n' n' ℝ)} {c : ENNReal} (hW : HasGramDensity W c)
    (e : n' ⊕ Unit ≃ n) {φ : Matrix n n ℝ ≃ₜ Matrix n' n' ℝ × (n' → ℂ) × ℝ}
    (φ_vol : MeasurePreserving φ)
    (φ_gram : ∀ (Y : Matrix n n' ℂ) (v : n → ℂ),
      φ (gramCoords 1 (joinCol e (Y, v))) = (gramCoords 1 Y, Yᴴ *ᵥ v, ‖star v ⬝ᵥ v‖)) :
    HasGramDensity (φ ⁻¹' {p : Matrix n' n' ℝ × (n' → ℂ) × ℝ |
        0 < p.2.2 ∧ p.1 - p.2.2⁻¹ • outerCoords p.2.1 ∈ W})
      (ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c) := by
  -- Let `m = card n'`. One column `v` ranges over the sphere `|v|² = r`, whose mass
  -- `π ^ (m + 1) r ^ m / m!` cancels the power of `r` that comes from the other `m` columns.
  intro G hG h_supp
  have : Nonempty n := ⟨e (.inr ())⟩
  let F (r : ℝ) (p : Matrix n' n' ℝ × (n' → ℂ)) : ENNReal := G (φ.symm (p.1, p.2, r))
  have hF_supp (r : ℝ) (p : Matrix n' n' ℝ × (n' → ℂ)) (hp : F r p ≠ 0) :
      0 < r ∧ p.1 - r⁻¹ • outerCoords p.2 ∈ W := by simpa using h_supp hp
  let H (r : ℝ) : ENNReal := ENNReal.ofReal (r ^ card n')⁻¹ * (c * ∫⁻ p, F r p)
  have h_column (v : n → ℂ) (hv : v ≠ 0) :
      ∫⁻ Y : Matrix n n' ℂ, G (gramCoords 1 (joinCol e (Y, v))) = H ‖star v ⬝ᵥ v‖ := by
    have hr : 0 < ‖star v ⬝ᵥ v‖ := by simpa using hv
    simp only [H]
    rw [← hW.lintegral_conjTranspose_mulVec e hr
      (norm_of_nonneg' (dotProduct_star_self_nonneg v)).symm (by fun_prop)
      fun p hp ↦ (hF_supp _ p hp).right, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    simp [F, ← φ_gram, hv]
  have h_mass (r : ℝ) (hr : 0 < r) :
      sphereDensity (card n) r / 2 * (r ^ card n')⁻¹ = sphereDensity (card n) 1 / 2 := by
    simp [← card_congr e, field]
  have hF_subset : (fun r : ℝ ↦ ∫⁻ p, F r p).support ⊆ Ioi 0 := fun r hr ↦ by
    obtain ⟨p, hp⟩ : ∃ p, F r p ≠ 0 := by_contra fun h ↦ hr (by simp_all)
    exact (hF_supp r p hp).left
  calc ∫⁻ Y, G (gramCoords 1 Y) = ∫⁻ v : n → ℂ, H ‖star v ⬝ᵥ v‖ := by
        rw [← (measurePreserving_joinCol e).lintegral_comp (by fun_prop), volume_eq_prod,
          lintegral_prod_symm' _ (by fun_prop)]
        exact lintegral_congr_ae ((ae_ne volume 0).mono h_column)
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (sphereDensity (card n) r / 2) * H r := by
        rw [measurePreserving_normSq_sphereDensity.lintegral_comp (by fun_prop)]
        exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c * ∫⁻ p, F r p := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        simp (disch := positivity) only [H, ← h_mass r hr, ENNReal.ofReal_mul, mul_assoc]
    _ = ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c * ∫⁻ r, ∫⁻ p, F r p := by
        rw [lintegral_const_mul _ (by fun_prop), setLIntegral_eq_of_support_subset hF_subset]
    _ = ENNReal.ofReal (sphereDensity (card n) 1 / 2) * c * ∫⁻ t : Matrix n n ℝ, G t := by
        rw [← (φ_vol.symm φ.toMeasurableEquiv).lintegral_comp hG,
          ← volume_preserving_prodAssoc.lintegral_comp (by fun_prop), volume_eq_prod _ ℝ,
          lintegral_prod_symm' _ (by fun_prop)]
        rfl

omit [Fintype n'] in
/-- The Gram matrix of columns `(Y, v)`, joined by `joinCol e`, in the coordinates `φ` of block,
column and corner, where the column entries are read from `hermOfReal t`, the hermitian matrix with
real coordinates `t`: they are `gramCoords 1 Y`, `Yᴴ v` and `|v|²`. -/
lemma apply_gramCoords_joinCol (e : n' ⊕ Unit ≃ n)
    {φ : Matrix n n ℝ ≃ₜ Matrix n' n' ℝ × (n' → ℂ) × ℝ}
    (φ_apply : ∀ t : Matrix n n ℝ, φ t = (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
      fun a : n' ↦ hermOfReal t (e (.inl a)) (e (.inr ())), t (e (.inr ())) (e (.inr ()))))
    (Y : Matrix n n' ℂ) (v : n → ℂ) :
    φ (gramCoords 1 (joinCol e (Y, v))) = (gramCoords 1 Y, Yᴴ *ᵥ v, ‖star v ⬝ᵥ v‖) := by
  have h_corner : ((joinCol e (Y, v))ᴴ * joinCol e (Y, v)) (e (.inr ())) (e (.inr ())) =
      ‖star v ⬝ᵥ v‖ := by
    rw [norm_of_nonneg' (dotProduct_star_self_nonneg v)]
    simp [Matrix.mul_apply, dotProduct]
  rw [φ_apply, hermOfReal_gramCoords isHermitian_one]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [← ext_iff, gramCoords, skewCoords, Matrix.mul_apply]
  · simp [funext_iff, Matrix.mul_apply, mulVec, dotProduct]
  · simp [gramCoords, skewCoords, h_corner]

/-- There is an open set `W` of real `n × n` matrices containing `gramCoords 1 1` on which the Gram
map `Y ↦ gramCoords 1 Y` has density `volU (card n) / 2 ^ card n`. Here `gramCoords 1 Y` is the
vector of real coordinates, in the sense of `hermOfReal` (which takes real coordinates back to the
hermitian matrix), of `Yᴴ Y` for complex square matrices `Y`. Having this density means that on `W`
the map carries Lebesgue measure to that constant times Lebesgue measure, where
`volU j = ∏ i < j, 2 π ^ (i + 1) / i!`. -/
theorem exists_hasGramDensity :
    ∃ W : Set (Matrix n n ℝ), IsOpen W ∧ gramCoords 1 (1 : Matrix n n ℂ) ∈ W ∧
      HasGramDensity W (ENNReal.ofReal (volU (card n) / 2 ^ card n)) := by
  induction hk : card n generalizing n with
  | zero =>
    rw [card_eq_zero_iff] at hk
    refine ⟨univ, isOpen_univ, trivial, fun G hG _ ↦ ?_⟩
    simp [volU, volume_eq_dirac_of_isEmpty (1 : Matrix n n ℂ),
      volume_eq_dirac_of_isEmpty (gramCoords 1 (1 : Matrix n n ℂ))]
  | succ k ih =>
    obtain ⟨k₀⟩ : Nonempty n := card_pos_iff.1 (by lia)
    let n' : Type := {a : n // a ≠ k₀}
    let e : n' ⊕ Unit ≃ n := (Equiv.optionEquivSumPUnit n').symm.trans (Equiv.optionSubtypeNe k₀)
    obtain ⟨W, hW_open, hW_one, hW⟩ := ih (n := n') (by simp [n', hk])
    -- `φ` splits the coordinates of a hermitian matrix into block, column and corner.
    obtain ⟨φ, φ_vol, φ_apply⟩ := exists_measurePreserving_hermCorner e
    have h_const : ENNReal.ofReal (volU (k + 1) / 2 ^ (k + 1)) =
        ENNReal.ofReal (sphereDensity (card n) 1 / 2) * ENNReal.ofReal (volU k / 2 ^ k) := by
      rw [← ENNReal.ofReal_mul (by positivity), hk, volU, Finset.prod_range_succ_comm, ← volU,
        pow_succ', mul_div_mul_comm]
    have h_open : IsOpen {p : Matrix n' n' ℝ × (n' → ℂ) × ℝ |
        0 < p.2.2 ∧ p.1 - p.2.2⁻¹ • outerCoords p.2.1 ∈ W} := by
      refine ContinuousOn.isOpen_inter_preimage (fun p hp ↦ ContinuousAt.continuousWithinAt ?_)
        (isOpen_Ioi.preimage continuous_snd.snd) hW_open
      fun_prop (disch := exact ne_of_gt hp)
    have h_one : φ (gramCoords 1 (1 : Matrix n n ℂ)) =
        (gramCoords 1 (1 : Matrix n' n' ℂ), 0, 1) := by
      rw [φ_apply, hermOfReal_gramCoords isHermitian_one]
      simp [← ext_iff, funext_iff, gramCoords, skewCoords, Matrix.one_apply]
    exact ⟨_, h_open.preimage φ.continuous, by simpa [h_one, outerCoords] using hW_one,
      by simpa only [h_const] using hW.succ e φ_vol (apply_gramCoords_joinCol e φ_apply)⟩

/-- The compact unitary group `U(n)` has total mass one for the measure `New.haarU 1`, which is
the `volume` of `U 1`. -/
instance isProbabilityMeasure_haarU :
    IsProbabilityMeasure (volume : Measure (U (1 : Matrix n n ℂ))) where
  measure_univ := by
    -- Compute the volume of the matrices with Gram matrix in a small open set `S` in two ways: by
    -- the polar formula over a section `σ`, and by the density of the Gram map near the identity.
    obtain ⟨W, hW_open, hW_one, hW⟩ := exists_hasGramDensity (n := n)
    obtain ⟨V, σ, hσ, hV_one, -⟩ := exists_isGramSection (1 : Matrix n n ℂ)
    obtain ⟨O, hO_one, hO_open, hO_fin⟩ :=
      exists_isOpen_measure_lt_top volume (gramCoords 1 (1 : Matrix n n ℂ))
    let S : Set (Matrix n n ℝ) := V ∩ W ∩ O
    have hS : IsOpen S := (hσ.isOpen.inter hW_open).inter hO_open
    have hS_pos : volume S ≠ 0 := hS.measure_ne_zero volume ⟨_, ⟨hV_one, hW_one⟩, hO_one⟩
    have hS_fin : volume S ≠ ⊤ := ((measure_mono inter_subset_right).trans_lt hO_fin).ne
    set c : ENNReal := ENNReal.ofReal (volU (card n) / 2 ^ card n)
    have hc : c ≠ 0 := by simp [c, volU_pos]
    rw [← ENNReal.mul_left_inj hS_pos hS_fin, ← ENNReal.mul_right_inj hc ENNReal.ofReal_ne_top]
    calc c * (volume (univ : Set (U (1 : Matrix n n ℂ))) * volume S)
        = c * ∫⁻ t : Matrix n n ℝ in S, ∫⁻ g : U (1 : Matrix n n ℂ), 1 := by
          simp [Set.univ_inter]
      _ = ∫⁻ Y : Matrix n n ℂ in gramCoords 1 ⁻¹' S, 1 :=
          ((hσ.mono hS (by grind)).lintegral_eq measurable_const).symm
      _ = ∫⁻ Y : Matrix n n ℂ, S.indicator 1 (gramCoords 1 Y) :=
          (lintegral_indicator ((continuous_gramCoords 1).measurable hS.measurableSet) _).symm
      _ = c * (1 * volume S) := by
          simpa [hS.measurableSet, Set.univ_inter] using
            hW _ (measurable_one.indicator hS.measurableSet)
              (support_indicator_subset.trans (by grind))

/-- For all signs equal to one, the unitary group of the sign matrix `signMatrix 1`, which equals
`1` by `signMatrix_one`, has total mass one. -/
instance : IsProbabilityMeasure (α := U (signMatrix (n := n) 1)) volume := by
  rw! [signMatrix_one]
  infer_instance

end New

/-!
## Covering bounds for norm balls in U(J) and integrals of (2/‖j s y‖)^c

The covering bound compares volumes of balls in the real space of matrices, of dimension `2 n²`. The
integral bound integrates it over the level sets of the norm.
-/

section HaarCovering

open New U MeasureTheory ENNReal Fintype Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} [IsHermitianInvolution J]
  {S : Type} [Group S] [MeasurableSpace S]

omit [IsHermitianInvolution J] in
theorem IsProperMap.monoidHom_id : IsProperMap (MonoidHom.id (U J)) := by simp

/-- The distance on `U J` is the operator norm of the difference of matrices. -/
noncomputable instance : MetricSpace (U J) := isClosedEmbedding_U.toIsEmbedding.comapMetricSpace _

/-- Closed balls of `U J` are compact, as `U J` is a closed set of matrices. -/
instance : ProperSpace (U J) where
  isCompact_closedBall x r :=
    isClosedEmbedding_U.isCompact_preimage (isCompact_closedBall (x : Matrix n n ℂ) r)

theorem New.isCompact_U_norm_le (T : ℝ) : IsCompact {y : U J | ‖(y : Matrix n n ℂ)‖ ≤ T} := by
  simpa [Set.preimage] using
    isClosedEmbedding_U.isCompact_preimage (isCompact_closedBall (0 : Matrix n n ℂ) T)

/-- The sublevel set `{s | f s ≤ r}` of a continuous function `f` has nonzero measure when
`f 1 < r`, for a measure `ν` that is positive on nonempty open sets. -/
lemma New.measure_sublevel_ne_zero (ν : Measure S) [TopologicalSpace S] [ν.IsOpenPosMeasure]
    {f : S → ℝ} {r : ℝ} (h_one : f 1 < r := by simp) (hf : Continuous f := by fun_prop) :
    ν {s : S | f s ≤ r} ≠ 0 :=
  (ν.measure_pos_of_mem_nhds (hf.tendsto 1 (ge_mem_nhds h_one))).ne'

namespace New.DiscreteSeries

/-- Covering bound. For `D, R ≥ 1` and `3 D R² ≤ K`, the set where `‖j s * y‖ ≤ R` has measure
at most `K ^ (2 n²)` times the measure of the set where `‖j s - 1‖ ≤ 1 / D`. Here `ν` is a
right invariant measure on `S`, `j` is a homomorphism to the unitary group `U J` of a hermitian
involution `J` of size `n`, and the norms are operator norms. -/
theorem measure_ball_le_covering (ν : Measure S) [MeasurableMul S] [ν.IsMulRightInvariant]
    (j : S →* U J) (y : U J) {D R K : ℝ} (hD : 1 ≤ D) (hR : 1 ≤ R) (hK : 3 * D * R ^ 2 ≤ K) :
    ν {s : S | ‖((j s * y : U J) : Matrix n n ℂ)‖ ≤ R} ≤
      ENNReal.ofReal (K ^ (2 * card n ^ 2)) * ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ D⁻¹} := by
  -- Among the `s` with `‖j s * y‖ ≤ R` take a maximal family `M` whose matrices `j s * y` are
  -- `1 / (D R)`-separated. The packing bound counts `M`, and by maximality the right translates
  -- of the small ball `B` by the points of `M` cover the set on the left.
  let f (s : S) : Matrix n n ℂ := ((j s * y : U J) : Matrix n n ℂ)
  set B : Set S := {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ D⁻¹}
  let IsFar (s t : {s : S // ‖f s‖ ≤ R}) : Prop := D⁻¹ / R ≤ ‖f s - f t‖
  obtain ⟨M, h_sep, h_max⟩ : ∃ M, IsMaxChain IsFar M := ⟨maxChain IsFar, maxChain_spec⟩
  have h_card : M.encard ≤ ENNReal.ofReal (K ^ (2 * card n ^ 2)) := by
    have h_pairwise : M.Pairwise IsFar := by simpa [IsChain, IsFar, norm_sub_rev] using h_sep
    have h_base : 1 + 2 * R / (D⁻¹ / R) ≤ K :=
      calc _ = 1 + 2 * D * R ^ 2 := by field
        _ ≤ K := by linarith [show 1 ≤ D * R ^ 2 by bound]
    calc _ ≤ ENNReal.ofReal ((1 + 2 * R / (D⁻¹ / R)) ^ Module.finrank ℝ (Matrix n n ℂ)) :=
          encard_le_of_separated (by positivity) (by positivity) h_pairwise fun s _ ↦ s.property
      _ ≤ ENNReal.ofReal (K ^ Module.finrank ℝ (Matrix n n ℂ)) := by gcongr
      _ = _ := by simp [Module.finrank_matrix, ← sq, mul_comm 2]
  have : Finite M := Set.Finite.to_subtype (by simpa using h_card.trans_lt ofReal_lt_top)
  have h_cover : {s : S | ‖f s‖ ≤ R} ⊆ ⋃ k : M, (· * (k : S)⁻¹) ⁻¹' B := by
    intro g hg
    by_contra h_not_mem
    -- Otherwise `g` is far from all of `M`: `j (g k⁻¹) - 1 = (f g - f k) (j k * y)⁻¹`, and an
    -- element of `U J` has the norm of its inverse.
    have h_far (k : M) : IsFar ⟨g, hg⟩ k := (div_le_iff₀ (by positivity)).2 <|
      calc D⁻¹ ≤ ‖(j (g * (k : S)⁻¹) : Matrix n n ℂ) - 1‖ :=
          le_of_not_ge fun h ↦ h_not_mem (Set.mem_iUnion.2 ⟨k, h⟩)
        _ = ‖(f g - f k) * (((j k * y)⁻¹ : U J) : Matrix n n ℂ)‖ := by simp [f, sub_mul, mul_assoc]
        _ ≤ ‖f g - f k‖ * R := by grw [norm_mul_le, U.norm_inv, k.val.property]
    -- Maximality puts `g` into `M`, so `g` is far from itself.
    have h_mem : ⟨g, hg⟩ ∈ M := Set.insert_eq_self.1
      (h_max (h_sep.insert fun k hk _ ↦ .inl (h_far ⟨k, hk⟩)) (Set.subset_insert ..)).symm
    have h_self : D⁻¹ / R ≤ 0 := by simpa [IsFar] using h_far ⟨_, h_mem⟩
    exact h_self.not_gt (by positivity)
  calc ν {s : S | ‖f s‖ ≤ R} ≤ ∑' k : M, ν ((· * (k : S)⁻¹) ⁻¹' B) :=
        (measure_mono h_cover).trans (measure_iUnion_le _)
    _ = M.encard * ν B := by simp only [measure_preimage_mul_right, tsum_set_const]
    _ ≤ ENNReal.ofReal (K ^ (2 * card n ^ 2)) * ν B := by gcongr

/-- For a proper homomorphism `j` to `U J` and a measure `ν` that is finite on compact sets, the
ball `‖j s - 1‖ ≤ R` in the operator norm has finite measure. -/
lemma measure_ball_ne_top_of_isProperMap (ν : Measure S)
    {j : S →* U J} [TopologicalSpace S] [IsFiniteMeasureOnCompacts ν]
    (hj : IsProperMap j) (R : ℝ) : ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ R} ≠ ⊤ := by
  have h_eq : {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ R} = j ⁻¹' Metric.closedBall 1 R :=
    Set.ext fun s ↦ (mem_closedBall_iff_norm (b := (j s : Matrix n n ℂ))).symm
  simpa only [h_eq] using (hj.isCompact_preimage (isCompact_closedBall 1 R)).measure_ne_top

/-- Let `J` be a hermitian involution of size `n ≥ 1`, let `j : S →* U J` be proper, let `ν` be
right invariant and finite on compact sets, and let `c > 8 n²` be a natural number. Then
`s ↦ (2 / ‖j s * y‖) ^ c` is integrable, and its integral is at most `16 ^ c` times the measure of
the set where `‖j s - 1‖ ≤ 1` (operator norms). The bound does not depend on `y`. -/
theorem integral_decay_le (ν : Measure S) [MeasurableMul S] [ν.IsMulRightInvariant]
    {j : S →* U J} [TopologicalSpace S] [IsFiniteMeasureOnCompacts ν] [BorelSpace S] [Nonempty n]
    (hj : IsProperMap j) {c : ℕ} (hc : 8 * card n ^ 2 < c) (y : U J) :
    Integrable (fun s : S ↦ (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c) ν ∧
      ∫ s : S, (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c ∂ν ≤
        16 ^ c * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
  -- By `measure_ball_le_covering` with `D = 1`, the set `‖j s * y‖ ≤ R` has measure at most
  -- `(3 R²) ^ (2 n²)` times that of `‖j s - 1‖ ≤ 1`. As `‖j s * y‖ ≥ 1` and `c ≤ 3 (c - 4 n²)`,
  -- integration by layers gives the factor `3 ^ (2 n²) * 3`.
  let N (s : S) : ℝ := ‖((j s * y : U J) : Matrix n n ℂ)‖
  have h_layers (R : ℝ) (hR : 1 ≤ R) : ν {s : S | N s ≤ R} ≤
      ENNReal.ofReal ((3 * 1 * R ^ 2) ^ (2 * card n ^ 2)) *
        ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1⁻¹} :=
    measure_ball_le_covering ν j y le_rfl hR le_rfl
  have hc_real : 8 * (card n : ℝ) ^ 2 < c := mod_cast hc
  have h_exp : (2 : ℕ) * (2 * card n ^ 2 : ℕ) < (c : ℝ) := mod_cast by lia
  have h_factor : (c : ℝ) ≤ 3 * (c - (2 : ℕ) * (2 * card n ^ 2 : ℕ)) := by grind
  obtain ⟨h_int, h_le⟩ : Integrable (fun s : S ↦ N s ^ (-c : ℝ)) ν ∧
      ∫ s : S, N s ^ (-c : ℝ) ∂ν ≤
        (3 * 1) ^ (2 * card n ^ 2) * 3 * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1⁻¹} :=
    integral_rpow_neg_le_of_measure_le (Continuous.measurable (by fun_prop)) (fun _ ↦ one_le_norm _)
      (by norm_num) (measure_ball_ne_top_of_isProperMap ν hj 1⁻¹) h_layers h_exp h_factor
  have h_split (s : S) :
      (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c = 2 ^ c * N s ^ (-c : ℝ) := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, div_pow, div_eq_mul_inv]
  have h_const : (2 : ℝ) ^ c * (3 ^ (2 * card n ^ 2) * 3) ≤ 16 ^ c :=
    calc _ ≤ (2 : ℝ) ^ c * 3 ^ c := by
          grw [← pow_succ, pow_le_pow_right₀ (by norm_num) (show 2 * card n ^ 2 + 1 ≤ c by lia)]
      _ ≤ 16 ^ c := by grw [← mul_pow, show (2 * 3 : ℝ) ≤ 16 by norm_num]
  simp only [h_split]
  refine ⟨h_int.const_mul _, ?_⟩
  calc ∫ s : S, 2 ^ c * N s ^ (-c : ℝ) ∂ν
      ≤ 2 ^ c * (3 ^ (2 * card n ^ 2) * 3) * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
        grw [integral_const_mul, h_le, mul_one, inv_one, ← mul_assoc]
    _ ≤ 16 ^ c * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by gcongr

/-- The bound of `integral_decay_le` for the lower Lebesgue integral: for a proper `j : S →* U J`,
`ν` right invariant and finite on compact sets, `n ≥ 1` and `c > 8 n²`, the integral of
`(2 / ‖j s * y‖) ^ c` is at most `16 ^ c` times the measure of the set where `‖j s - 1‖ ≤ 1`. -/
theorem lintegral_decay_le (ν : Measure S) [MeasurableMul S] [ν.IsMulRightInvariant]
    {j : S →* U J} [TopologicalSpace S] [IsFiniteMeasureOnCompacts ν] [BorelSpace S] [Nonempty n]
    (hj : IsProperMap j) {c : ℕ} (hc : 8 * card n ^ 2 < c) (y : U J) :
    ∫⁻ s : S, ENNReal.ofReal ((2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c) ∂ν ≤
      ENNReal.ofReal (16 ^ c) * ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
  obtain ⟨h_int, h_le⟩ := integral_decay_le ν hj hc y
  calc _ = ENNReal.ofReal (∫ s : S, (2 / ‖((j s * y : U J) : Matrix n n ℂ)‖) ^ c ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal h_int (.of_forall fun s ↦ by positivity)).symm
    _ ≤ ENNReal.ofReal (16 ^ c * ν.real {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1}) :=
        ENNReal.ofReal_le_ofReal h_le
    _ = ENNReal.ofReal (16 ^ c) * ν {s : S | ‖(j s : Matrix n n ℂ) - 1‖ ≤ 1} := by
        rw [ENNReal.ofReal_mul (by positivity),
          ofReal_measureReal (measure_ball_ne_top_of_isProperMap ν hj 1)]

end New.DiscreteSeries

end HaarCovering
