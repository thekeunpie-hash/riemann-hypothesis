module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Topology.UniformSpace.Uniformizable
public import New.Determinant.Exchange.LargeTriple
import Lib.Adelic.Unitary.RationalPoints
import Lib.General.Analysis.MeanValueAndTaylor
import Lib.PadicComparison.Descent.TestCategory
import Lib.Shimura.Uniformisation.HolomorphicFamilies
import Lib.Weil.MixedModel.ThetaInvariance
public import Lib.SiegelWeil.Tower.TestVector
public import Lib.SiegelWeil.Tower.LineGaussSums
public import Lib.Weil.DualPair.ThetaIntegrals
import Lib.Weil.Construction.CanonicalTheta
import New.Determinant.Exchange.RemovingPlanes
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.CategoryTheory.Countable
import Mathlib.Topology.Connected.Separation
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.Weil.DualPair.Flip
public import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.ClassField.HeckeCharacter.SplittingCharacters
import Lib.Weil.DualPair.ThetaLiftConvergence

section
/-!
# Smooth local Witt theorem and the exchange identity for `V' ⊕ W₁` and `V'`

Construction of the data at the real places for the identity `New.Exchange.RowColExchangeIdentity`
between the theta integrals of the pairs `(X, V' ⊕ W₁)` and `(X, V')`, where `X` splits over `W₁`.

* `New.Exchange.exists_isSchwartzVector_realSlice_eq`: a Schwartz Fock vector whose slices are a
  bump function times `realWeil 1 v`, scaled so that its slice at 0 for the opposite splitting is
  `v`.
* `New.Exchange.exists_contDiff_witt`: a local form of Witt's theorem for spans: frames near a
  nondegenerate frame `x` lie in the span of a unitary image of `x` that depends smoothly on them.
* `New.Exchange.exists_rowColExchangeIdentity_sum`: two vectors for which
  `New.Exchange.RowColExchangeIdentity` holds for these two pairs, one of them with a prescribed
  slice at 0.

Notions from other files:
* `New.Space.Splitting`: a decomposition V = (lE^p ⊕ kE^p) ⊥ iV₀ with dual isotropic frames l, k and
  an isometric embedding i of V₀; `New.Space.Splitting.symm` exchanges k and l. It is adapted
  (`New.Exchange.IsBaseAdapted`) if the frames are orthonormal at the infinite places and integral
  at the finite ones.
* `New.PairFock E s t`: the Fock space of matrices whose `(i, j)` coordinate has the sign
  `t i * s j`, repeated at every infinite place. These signs are `New.homSigns s t`, and repeating
  them at every place is `New.realSigns`.
* `New.realPairWeil γ γ'`: the Weil representation on this Fock space, restricted to a pair of
  unitary groups at the infinite places, twisted by the powers of the determinants with exponents
  `γ` on the second and `-γ'` on the first.
* `New.Exchange.IsSchwartzVector`: all moments of the Fock vector are finite.
* `New.Exchange.realSlice`: the slice of a vector in the mixed Schrödinger–Fock model of an adapted
  splitting.
* `New.Exchange.RowColExchangeIdentity`: two theta integrals are proportional on admissible data,
  with a formula for the absolute value of the factor.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work. See
`Lib.Adelic.Witt.IwasawaDecomposition` for sources.
-/

@[expose] public section

namespace New.Exchange

open Matrix NumberField MeasureTheory Complex Fock Space Filter ContDiff Norms.Elementwise Finset
  Function Splitting Measure MixedModel GeneralLinearGroup ENNReal IsHermitianInvolution U

private lemma contDiff_mat_mul {X l o k : Type*} {N : ℕ∞ω} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [Fintype l] [Fintype o] [Fintype k]
    {f : X → Matrix l o ℂ} {g : X → Matrix o k ℂ}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) : ContDiff ℝ N fun x ↦ f x * g x :=
  contDiff_matrix_mul.comp (hf.prodMk hg)

private lemma continuous_mat_mul {X l o k : Type*} [TopologicalSpace X] [Fintype l] [Fintype o]
    [Fintype k] {f : X → Matrix l o ℂ} {g : X → Matrix o k ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ f x * g x :=
  (contDiff_matrix_mul (N := 0)).continuous.comp (hf.prodMk hg)

private lemma contDiff_finset_prod {ι X : Type*} {N : ℕ∞ω} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : Finset ι} {f : ι → X → ℂ} (hf : ∀ i ∈ s, ContDiff ℝ N (f i)) :
    ContDiff ℝ N fun x ↦ ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.prod_empty] using contDiff_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private lemma contDiff_mat_det {X k : Type*} {N : ℕ∞ω} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype k] [DecidableEq k] {f : X → Matrix k k ℂ} (hf : ContDiff ℝ N f) :
    ContDiff ℝ N fun x ↦ (f x).det := by
  simp only [det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ ↦ contDiff_const.mul
    (contDiff_finset_prod fun i _ ↦ contDiff_pi.1 (contDiff_pi.1 hf (σ i)) i)

private lemma pi_mul_inv_apply {ι G : Type*} [Group G] (a b : ι → G) (w : ι) :
    (a * b)⁻¹ w = b⁻¹ w * a⁻¹ w := by
  rw [_root_.mul_inv_rev, Pi.mul_apply]

variable {E n a b m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
  {s : n → ℤˣ} {r : m → ℤˣ} {X : Space E m r} {W₁ : Space E n s}

/-- Let `τ ≥ 0` be smooth, compactly supported and nonzero at some `y`, and let `v` be a Schwartz
vector for `(W₁, V')`. Then there are a complex number `κ` and a Schwartz vector `Λ` for `(X, V')`
whose slice at each `x` is `τ x • κ` times `realWeil 1 v`, and whose slice at `0` for `D.symm`, the
splitting with the two isotropic frames exchanged, is `v`. -/
lemma exists_isSchwartzVector_realSlice_eq (D : X.Splitting W₁ b) [IsBaseAdapted D] {t' : a → ℤˣ}
    (V' : Space E a t') (τ : (InfinitePlace E × a × b → ℂ) → ℝ) (hτ : ContDiff ℝ ∞ τ)
    {v : fockSpace (realSigns E (homSigns s t'))} (hv : IsSchwartzVector v)
    (hsupp : HasCompactSupport τ) (hτ₀ : 0 ≤ τ) (y : InfinitePlace E × a × b → ℂ) (hy : τ y ≠ 0) :
    ∃ (κ : ℂ) (Λ : fockSpace (realSigns E (homSigns r t'))),
      IsSchwartzVector Λ ∧
      realSlice D.symm V' 0 Λ = v ∧
      ∀ x : InfinitePlace E × a × b → ℂ,
        (isAdapted_homSource D V').mixedModel.slice x Λ = (τ x • κ) • realWeil 1 v := by
  -- Choose `κ` so that `τ κ` and the Gaussian slices of the vacuum have the same integral. The
  -- slice at `0` for `D.symm` is the integral of all slices, so the section `τ κ • v` gives `v`.
  have hpos : 0 < ∫ x, τ x ∂normalizedVolume _ :=
    hτ.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hsupp hτ₀ hy
  set 𝓜 := (isAdapted_homSource D V').mixedModel
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ,
      ∫ x, 𝓜.slice x Fock.vacVector 0 ∂normalizedVolume _ = (∫ x, τ x ∂normalizedVolume _ : ℝ) *
        κ :=
    ⟨_, (mul_div_cancel₀ _ (ofReal_ne_zero.2 hpos.ne')).symm⟩
  obtain ⟨Λ, hΛ, hslice⟩ := 𝓜.exists_isSchwartzVector_slice_eq (hτ.smul_const κ) hsupp.smul_right
    (u := fun _ ↦ 1) contDiff_const hv
  -- It is enough to compare the two vectors after tensoring with zero terms.
  refine ⟨κ, Λ, hΛ, eq_of_integrated_zeroTerm_eq (isAdapted_homSource D.symm V') fun f ↦ ?_, hslice⟩
  -- Both sides are integrals of slices for `volume`, which is a multiple of the Haar measure
  -- `vacuumMeasure` moved by `star g`, for the change of frame `g`.
  let g : GL (a × b) (𝔸 E) := adaptedHomBasis b V'
  have : MeasurableConstSMul (GL (a × b) (𝔸 E)) (a × b → 𝔸 E) :=
    ContinuousConstSMul.toMeasurableConstSMul
  let ν : Measure (a × b → 𝔸 E) :=
    (DomMulAct.mk (star g) : (GL (a × b) (𝔸 E))ᵈᵐᵃ) • (vacuumMeasure : Measure (a × b → 𝔸 E))
  obtain ⟨c, hc⟩ : ∃ c : NNReal, volume = c • ν := ⟨_, isAddLeftInvariant_eq_smul volume ν⟩
  let term (x : a × b → 𝔸 E) : 𝒮 (X.hom V') → 𝒮 (W₁.hom V') :=
    (D.homSource V').slice ((g⁻¹ : GL (a × b) (𝔸 E)).valᴴ *ᵥ x)
  suffices h : ∫ x, term x ((X.hom V').integrated Λ f) ∂vacuumMeasure =
      ∫ x, (W₁.hom V').integrated v (term x ((X.hom V').projReal f)) ∂vacuumMeasure by
    calc _ = (D.symm.homSource V').zeroTerm ((X.hom V').integrated Λ f) :=
        (zeroTerm_integrated (isAdapted_homSource D.symm V') Λ f).symm
      _ = ∫ x, (D.homSource V').slice x ((X.hom V').integrated Λ f) :=
        symm_homSource_zeroTerm_eq_integral D V' _
      _ = ∫ x,
          (W₁.hom V').integrated v ((D.homSource V').slice x ((X.hom V').projReal f)) := by
        simpa [hc, ν, integral_domSMul, star, -coe_units_inv] using congrArg (c • ·) h
      _ = (W₁.hom V').integrated v ((D.symm.homSource V').zeroTerm ((X.hom V').projReal f)) := by
        rw [symm_homSource_zeroTerm_eq_integral,
          ← (integrated _ v).integral_comp_comm (by fun_prop)]
  -- In real and finite coordinates, both integrands are a function of the real variable times the
  -- same function `ψ` of the finite one.
  have term_eq (Φ : PairFock E r t') (x : a × b → 𝔸 E) : term x ((X.hom V').integrated Φ f) =
      (W₁.hom V').integrated (𝓜.slice (realCoord x) Φ) ((D.homSource V').slice
        (g⁻¹.valᴴ *ᵥ fun i ↦ (0, (x i).2)) ((X.hom V').projReal f)) :=
    slice_integrated (isAdapted_homSource D V') x Φ f
  let ψ (x : a × b → 𝔸f E) : 𝒮 (W₁.hom V') :=
    (W₁.hom V').integrated v ((D.homSource V').slice
      (g.val⁻¹ᴴ *ᵥ fun i ↦ (0, (WeilData.scaleIdele E).val.2 * x i)) ((X.hom V').projReal f))
  let μ := (normalizedVolume (InfinitePlace E × a × b)).prod (latticeMeasure E (a × b))
  -- Split off the real integrals (Fubini) and compare them by `hκ`.
  have h : ∫ x, ((τ x.1 : ℂ) * κ) • ψ x.2 ∂μ = ∫ x, 𝓜.slice x.1 Fock.vacVector 0 • ψ x.2 ∂μ := by
    rw [integral_prod_smul (fun x ↦ (τ x : ℂ) * κ) ψ, integral_mul_const, integral_complex_ofReal,
      integral_prod_smul (fun x ↦ 𝓜.slice x Fock.vacVector 0) ψ, hκ]
  -- Here `projReal` is `integrated` at the vacuum, so `term_eq` applies to both sides.
  simp only [term_eq]
  -- Insert the slice of `Λ` and split the adelic variable into real and finite parts.
  have h_real (y : (InfinitePlace E × a × b → ℂ) × (a × b → 𝔸f E)) :
      realCoord ((adelicSum E 1).equiv y) = y.1 := by
    funext p
    change ((WeilData.scaleIdele E).val.1 p.1 * y.1 p) / (WeilData.scaleIdele E).val.1 p.1 = y.1 p
    have hne : (WeilData.scaleIdele E).val.1 p.1 ≠ 0 := fun h0 ↦ by
      have h1 := congrFun (congrArg Prod.fst (WeilData.scaleIdele E).mul_inv) p.1
      simp only [Prod.fst_mul, Pi.mul_apply, h0, zero_mul, Prod.fst_one, Pi.one_apply,
        zero_ne_one] at h1
    exact mul_div_cancel_left₀ _ hne
  rw [(adelicSum E 1).integral_eq_integral_prod, (adelicSum E 1).integral_eq_integral_prod]
  have h_lhs (y : (InfinitePlace E × a × b → ℂ) × (a × b → 𝔸f E)) :
      (W₁.hom V').integrated (𝓜.slice (realCoord ((adelicSum E 1).equiv y)) Λ)
        ((D.homSource V').slice (g⁻¹.valᴴ *ᵥ fun i ↦ (0, ((adelicSum E 1).equiv y i).2))
          ((X.hom V').projReal f)) = ((τ y.1 : ℂ) * κ) • ψ y.2 := by
    rw [h_real, hslice, map_one, one_apply_eq_self, map_smul, _root_.smul_apply, real_smul,
      coe_units_inv]
    rfl
  have h_rhs (y : (InfinitePlace E × a × b → ℂ) × (a × b → 𝔸f E)) :
      (W₁.hom V').integrated v ((W₁.hom V').integrated
        (𝓜.slice (realCoord ((adelicSum E 1).equiv y)) Fock.vacVector)
        ((D.homSource V').slice (g⁻¹.valᴴ *ᵥ fun i ↦ (0, ((adelicSum E 1).equiv y i).2))
          ((X.hom V').projReal f))) = 𝓜.slice y.1 Fock.vacVector 0 • ψ y.2 := by
    rw [h_real]
    simp [ψ, g, adelicSum]
  simp only [h_lhs, h_rhs]
  exact h

/-- Taking the slice at `0` is onto on Schwartz vectors. Every Schwartz vector `v` (all moments
finite) in the Fock space `PairFock E s t'` of `(W₁, V')` is the slice at `0` of a Schwartz vector
in the Fock space `PairFock E r t'` of `(X, V')`. -/
lemma exists_isSchwartzVector_realSlice_zero_eq (A : X.Splitting W₁ b) [IsBaseAdapted A]
    {t' : a → ℤˣ} (V' : Space E a t') {v : PairFock E s t'} (hv : IsSchwartzVector v) :
    ∃ w : PairFock E r t', IsSchwartzVector w ∧ realSlice A V' 0 w = v := by
  -- Prescribe the slices along `A.symm`, with the standard smooth bump function. The splitting
  -- opposite to `A.symm` is `A` by definition.
  let τ : (InfinitePlace E × a × b → ℂ) → ℝ := ExistsContDiffBumpBase.u
  have hτ_zero : τ 0 ≠ 0 := (ExistsContDiffBumpBase.u_support _).ge (by simp)
  obtain ⟨-, w, hw, hw_zero, -⟩ := exists_isSchwartzVector_realSlice_eq A.symm V' τ
    (ExistsContDiffBumpBase.u_smooth _) hv (ExistsContDiffBumpBase.u_compact_support _)
    ExistsContDiffBumpBase.u_nonneg 0 hτ_zero
  exact ⟨w, hw, hw_zero⟩

/-- A smooth local form of Witt's theorem, for spans. Let `J` be Hermitian and `x` a frame
(a matrix of column vectors) with invertible Gram matrix `xᴴ * J * x`. There are elements `k y` of
the unitary group `U J`, indexed by all frames `y`, such that the matrix of `k y` is a smooth
function of `y` and, for `y` near `x`, the columns of `y` are linear combinations of those of
`k y * x`. -/
theorem exists_contDiff_witt {J : Matrix m m ℂ} (hJ : Jᴴ = J) {x : Matrix m b ℂ}
    (hdet : (xᴴ * J * x).det ≠ 0) :
    ∃ k : Matrix m b ℂ → U J,
      ContDiff ℝ ∞ (fun y : Matrix m b ℂ ↦ (k y : Matrix m m ℂ)) ∧
      ∀ᶠ y : Matrix m b ℂ in nhds x, ∃ c : Matrix b b ℂ, (k y : Matrix m m ℂ) * x * c = y := by
  -- `L a` lies in the Lie algebra of `U J`, and `a - L a` keeps the span of `x`. The map
  -- `T a = exp (L a) * (a - L a)` has derivative the identity at `1`, so it has a local inverse
  -- `A`; apply `A` to a matrix `z y` near `1` with `z y * x = y`.
  let w : Matrix b m ℂ := (xᴴ * J * x)⁻¹ * xᴴ
  have hw (y : Matrix m b ℂ) : y * w * J * x = y := by
    rw [Matrix.mul_assoc] at hdet
    simp only [w, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]
  let L (a : Matrix m m ℂ) : Matrix m m ℂ := (a * x * w - x * w * aᴴ) * J
  have hL (a : Matrix m m ℂ) : L a ∈ unitaryLie J := by
    change (L a)ᴴ * J + J * L a = 0
    simp only [L, w, conjTranspose_mul, conjTranspose_sub, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, hJ, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub,
      sub_add_sub_cancel, sub_self]
  have hL_span (a : Matrix m m ℂ) : (a - L a) * x = x * (w * aᴴ * J * x) := by
    simp only [L, Matrix.sub_mul, hw, _root_.sub_sub_cancel, Matrix.mul_assoc x]
  let T (a : Matrix m m ℂ) : Matrix m m ℂ := NormedSpace.exp (L a) * (a - L a)
  have hL₁ : L 1 = 0 := by
    simp only [L, Matrix.one_mul, conjTranspose_one, Matrix.mul_one, sub_self, Matrix.zero_mul]
  have hT₁ : T 1 = 1 := by
    simp only [T, hL₁, NormedSpace.exp_zero, sub_zero, Matrix.one_mul]
  have hL_smooth : ContDiff ℝ ω L :=
    contDiff_mat_mul
      ((contDiff_mat_mul (contDiff_mat_mul contDiff_id contDiff_const) contDiff_const).sub
        (contDiff_mat_mul contDiff_const (contDiff_conjTranspose.comp contDiff_id)))
      contDiff_const
  have hT' : HasFDerivAt T (ContinuousLinearEquiv.refl ℝ _).toContinuousLinearMap 1 := by
    obtain ⟨L', hL'⟩ := (hL_smooth.of_le le_top).differentiable_one 1
    open Norms.L2Operator in
      -- The product rule gives `(id - L') + L'`.
      refine ((HasFDerivAt.comp 1 (by simpa only [hL₁] using hasFDerivAt_exp_zero) hL').fun_mul'
        ((hasFDerivAt_id 1).fun_sub hL')).congr_fderiv ?_
      simp only [hL₁, Function.comp_apply, NormedSpace.exp_zero, sub_zero, id, one_smul,
        MulOpposite.op_one]
      exact sub_add_cancel _ L'
  obtain ⟨A, hA, hTA⟩ : ∃ A, ContDiff ℝ ∞ A ∧ ∀ᶠ z in nhds 1, T (A z) = z := by
    have hT : ContDiffAt ℝ ω T 1 :=
      (contDiff_mat_mul (contDiff_matrix_exp.comp hL_smooth)
        (contDiff_id.sub hL_smooth)).contDiffAt
    obtain ⟨A, hA, h_eq⟩ := exists_contDiff_eventuallyEq
      (hT.to_localInverse hT' (WithTop.coe_ne_top (a := (0 : ℕ∞))).symm)
    rw [← hT₁]
    exact ⟨A, hA, (h_eq.fun_comp T).trans (HasStrictFDerivAt.eventually_right_inverse _)⟩
  let z (y : Matrix m b ℂ) : Matrix m m ℂ := 1 - (x - y) * w * J
  have hz_smooth : ContDiff ℝ ∞ z :=
    contDiff_const.sub
      (contDiff_mat_mul (contDiff_mat_mul (contDiff_const.sub contDiff_id) contDiff_const)
        contDiff_const)
  have hz : Tendsto z (nhds x) (nhds 1) :=
    hz_smooth.continuous.tendsto' _ _ (by simp only [z, sub_self, Matrix.zero_mul, sub_zero])
  refine ⟨fun y ↦ expU ⟨L (A (z y)), hL _⟩,
    ((contDiff_matrix_exp.comp (hL_smooth.of_le le_top)).comp hA).comp hz_smooth,
    (hz.eventually hTA).mono fun y hy ↦ ⟨w * (A (z y))ᴴ * J * x, ?_⟩⟩
  calc NormedSpace.exp (L (A (z y))) * x * (w * (A (z y))ᴴ * J * x)
    _ = T (A (z y)) * x := by rw [Matrix.mul_assoc, ← hL_span, ← Matrix.mul_assoc]
    _ = z y * x := by rw [hy]
    _ = y := by rw [Matrix.sub_mul, Matrix.one_mul, hw, _root_.sub_sub_cancel]

/-- The external product `realBoxProd he v w` of two Schwartz Fock vectors (all moments finite), for
a splitting `e` of the coordinates compatible with the signs, is a Schwartz vector. -/
lemma isSchwartzVector_realBoxProd {ι ι₁ ι₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₁]
    [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {ε : ι → ℤˣ} {ε₁ : ι₁ → ℤˣ} {ε₂ : ι₂ → ℤˣ}
    {e : ι₁ ⊕ ι₂ ≃ ι}
    (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) {v : fockSpace ε₁} {w : fockSpace ε₂} (hv : IsSchwartzVector v)
    (hw : IsSchwartzVector w) : IsSchwartzVector (realBoxProd he v w) := by
  -- `realBoxProd he v w` is an iterated integral of translates of the vacuum, against `w` and then
  -- `v`; padding a vector with zeros does not increase its maximum norm.
  intro N
  have pad_left (x : ι₁ → ℂ) : ‖(realCoordSum he).equiv (x, 0)‖ₑ ≤ ‖x‖ₑ := by
    rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm, ENNReal.coe_le_coe, pi_nnNorm_le_iff]
    refine e.surjective.forall.2 (Sum.forall.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩)
    · change ‖(x ⊕ᵥ (0 : ι₂ → ℂ)) (e.symm (e (Sum.inl i)))‖₊ ≤ ‖x‖₊
      rw [e.symm_apply_apply, Sum.elim_inl]
      exact nnNorm_le_pi_nnNorm x i
    · change ‖(x ⊕ᵥ (0 : ι₂ → ℂ)) (e.symm (e (Sum.inr i)))‖₊ ≤ ‖x‖₊
      rw [e.symm_apply_apply, Sum.elim_inr, Pi.zero_apply, nnNorm_zero]
      exact bot_le
  have pad_right (y : ι₂ → ℂ) : ‖(realCoordSum he).equiv (0, y)‖ₑ ≤ ‖y‖ₑ := by
    rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm, ENNReal.coe_le_coe, pi_nnNorm_le_iff]
    refine e.surjective.forall.2 (Sum.forall.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩)
    · change ‖((0 : ι₁ → ℂ) ⊕ᵥ y) (e.symm (e (Sum.inl i)))‖₊ ≤ ‖y‖₊
      rw [e.symm_apply_apply, Sum.elim_inl, Pi.zero_apply, nnNorm_zero]
      exact bot_le
    · change ‖((0 : ι₁ → ℂ) ⊕ᵥ y) (e.symm (e (Sum.inr i)))‖₊ ≤ ‖y‖₊
      rw [e.symm_apply_apply, Sum.elim_inr]
      exact nnNorm_le_pi_nnNorm y i
  let inner : fockSpace ε := ∫ y, w y • realHeisenbergOp ((realCoordSum he).equiv (0, y))
    Fock.vacVector
    ∂normalizedVolume ι₂
  have inner_le : fockMoment N inner ≤
      fockMoment N (Fock.vacVector : fockSpace ε) * fockMoment N w := by
    refine (fockMoment_integral_le _).trans (lintegral_fockMoment_smul_le fun y ↦ ?_)
    exact ((fockMoment_realHeisenbergOp_le _ _ _).trans
      (mul_le_mul_left (pow_le_pow_left' (add_le_add_right (pad_right y) 1) N) _)).trans_eq
      (mul_comm _ _)
  have outer_le : fockMoment N (realBoxProd he v w) ≤
      fockMoment N (Fock.vacVector : fockSpace ε) * fockMoment N w * fockMoment N v := by
    refine (fockMoment_integral_le _).trans (lintegral_fockMoment_smul_le fun x ↦ ?_)
    change fockMoment N (realHeisenbergOp ((realCoordSum he).equiv (x, 0)) inner) ≤ _
    exact ((fockMoment_realHeisenbergOp_le _ _ _).trans
      (mul_le_mul' (pow_le_pow_left' (add_le_add_right (pad_left x) 1) N) inner_le)).trans_eq
      (mul_comm _ _)
  exact ne_top_of_le_ne_top (mul_ne_top (mul_ne_top (isSchwartzVector_vacVector N) (hw N)) (hv N))
    outer_le

/-- Matrix inversion agrees, near a matrix `A₀` of nonzero determinant, with a function that is
smooth on all matrices. -/
lemma exists_contDiff_eventuallyEq_inv {A₀ : Matrix b b ℂ} (hdet : A₀.det ≠ 0) :
    ∃ γ : Matrix b b ℂ → Matrix b b ℂ,
      ContDiff ℝ ∞ γ ∧ γ =ᶠ[nhds A₀] fun A : Matrix b b ℂ ↦ A⁻¹ := by
  -- The inverse is the adjugate, a polynomial in the entries, divided by the determinant.
  have det_smooth : ContDiffAt ℝ ω (fun A : Matrix b b ℂ ↦ A.det) A₀ :=
    (contDiff_mat_det contDiff_id).contDiffAt
  have adjugate_smooth : ContDiffAt ℝ ω (fun A : Matrix b b ℂ ↦ A.adjugate) A₀ := by
    refine (contDiff_pi.2 fun i : b ↦ contDiff_pi.2 fun j : b ↦ ?_).contDiffAt
    simp only [adjugate_apply]
    refine contDiff_mat_det (contDiff_pi.2 fun r ↦ contDiff_pi.2 fun c ↦ ?_)
    simp only [updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact (contDiff_pi.1 (contDiff_pi.1 contDiff_id r) c)
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact exists_contDiff_eventuallyEq ((det_smooth.inv hdet).smul adjugate_smooth)

/-- If `x * A` has an invertible Gram matrix for `J` and equals `g * x₀ * c` with `g` in the unitary
group `U J`, then `x` has the same form `g * x₀ * c'`, and `c'` carries the Gram matrix of `x₀` to
that of `x`. -/
lemma exists_mul_mul_eq_and_gram_eq {J : Matrix m m ℂ} (g : U J) {x₀ x : Matrix m b ℂ}
    {A c : Matrix b b ℂ}
    (hc : (g : Matrix m m ℂ) * x₀ * c = x * A) (hdet : ((x * A)ᴴ * J * (x * A)).det ≠ 0) :
    ∃ c' : Matrix b b ℂ,
      (g : Matrix m m ℂ) * x₀ * c' = x ∧ c'ᴴ * (x₀ᴴ * J * x₀) * c' = xᴴ * J * x := by
  rw [gram_mul, det_mul] at hdet
  have hx : (g : Matrix m m ℂ) * x₀ * (c * A⁻¹) = x := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hdet)), Matrix.mul_one]
  exact ⟨c * A⁻¹, hx, by conv_rhs => rw [← hx, gram_mul, U.gram_invariant]⟩

/-- Smooth data for Witt's theorem near a frame `x₀`, for a form `J`: a function `γ` on square
matrices, unitary elements `k y` indexed by frames `y`, and a bump function `σ` on families of
frames. For each member `y` of a family at which `σ` does not vanish, `γ` inverts the Gram matrix of
`y` and `y` lies in the span of `k y * x₀`. -/
structure IsWittBump {ι : Type*} [Fintype ι] (J : Matrix m m ℂ) (x₀ : Matrix m b ℂ)
    (γ : Matrix b b ℂ → Matrix b b ℂ) (k : Matrix m b ℂ → U J) (σ : (ι → Matrix m b ℂ) → ℝ) :
    Prop where
  /-- `γ` is smooth. -/
  contDiff_inv : ContDiff ℝ ∞ γ
  /-- `γ` inverts the Gram matrix of `x₀`. -/
  inv_gram_base : γ (x₀ᴴ * J * x₀) = (x₀ᴴ * J * x₀)⁻¹
  /-- The matrix of `k y` is a smooth function of `y`. -/
  contDiff_unitary : ContDiff ℝ ∞ fun y : Matrix m b ℂ ↦ (k y : Matrix m m ℂ)
  /-- `σ` is smooth. -/
  contDiff_bump : ContDiff ℝ ∞ σ
  /-- `σ` has compact support. -/
  hasCompactSupport_bump : HasCompactSupport σ
  /-- `σ` is nonnegative. -/
  bump_nonneg : ∀ x : ι → Matrix m b ℂ, 0 ≤ σ x
  /-- `σ` is `1` at the constant family `x₀`. -/
  bump_base : σ (fun _ : ι ↦ x₀) = 1
  /-- Where `σ` does not vanish, each frame `y` lies in the span of `k y * x₀`. -/
  exists_mul_eq : ∀ x : ι → Matrix m b ℂ, σ x ≠ 0 → ∀ i : ι,
    ∃ c : Matrix b b ℂ, (k (x i) : Matrix m m ℂ) * x₀ * c = x i
  /-- Where `σ` does not vanish, `γ` inverts the Gram matrix of each frame. -/
  inv_gram : ∀ x : ι → Matrix m b ℂ, σ x ≠ 0 → ∀ i : ι,
    γ ((x i)ᴴ * J * x i) = ((x i)ᴴ * J * x i)⁻¹
  /-- Where `σ` does not vanish, the Gram matrix of each frame is invertible. -/
  det_gram_ne_zero : ∀ x : ι → Matrix m b ℂ, σ x ≠ 0 → ∀ i : ι, ((x i)ᴴ * J * x i).det ≠ 0

/-- For `J` Hermitian and a frame `x₀` with invertible Gram matrix there are a smooth function `γ`,
elements `k y` of `U J` depending smoothly on the frame `y` and a bump function `σ`, equal to 1 at
the constant family `x₀`, such that for each member `y` of a family where `σ` is nonzero `γ` inverts
the invertible Gram matrix of `y` and `y` lies in the span of `k y * x₀` (`IsWittBump`). -/
lemma exists_contDiff_witt_and_bump {ι : Type*} [Fintype ι] {J : Matrix m m ℂ} (hJ : Jᴴ = J)
    {x₀ : Matrix m b ℂ} (hdet : (x₀ᴴ * J * x₀).det ≠ 0) :
    ∃ (γ : Matrix b b ℂ → Matrix b b ℂ) (k : Matrix m b ℂ → U J) (σ : (ι → Matrix m b ℂ) → ℝ),
      IsWittBump J x₀ γ k σ := by
  obtain ⟨γ, γ_smooth, γ_inv⟩ := exists_contDiff_eventuallyEq_inv hdet
  obtain ⟨k, k_smooth, span_near⟩ := exists_contDiff_witt hJ hdet
  obtain ⟨σ, σ_supp, σ_cpt, σ_smooth, σ_range, σ_one⟩ := exists_contDiff_tsupport_subset <|
    nhds_pi.le <| eventually_pi fun _ : ι ↦ span_near.and <|
      (by fun_prop : Continuous fun y : Matrix m b ℂ ↦ yᴴ * J * y).tendsto x₀ <|
        γ_inv.and (ContinuousAt.eventually_ne (by fun_prop) hdet)
  exact ⟨γ, k, σ, γ_smooth, γ_inv.eq_of_nhds, k_smooth, σ_smooth, σ_cpt,
    fun x ↦ (σ_range ⟨x, rfl⟩).1, σ_one,
    fun x hx i ↦ (σ_supp (subset_closure hx) i).1,
    fun x hx i ↦ (σ_supp (subset_closure hx) i).2.1,
    fun x hx i ↦ (σ_supp (subset_closure hx) i).2.2⟩

omit [DecidableEq m] in
/-- The `J`-orthogonal projection `x * (xᴴ * J * x)⁻¹ * xᴴ * J * x₀` of `x₀` to the span of a frame
`x` does not change when `x` is multiplied on the right by an invertible matrix. -/
lemma mul_gram_inv_mul_of_isUnit_det (J : Matrix m m ℂ) (x x₀ : Matrix m b ℂ) {C : Matrix b b ℂ}
    (hC : IsUnit C.det) :
    x * C * (((x * C)ᴴ * J * (x * C))⁻¹ * ((x * C)ᴴ * J * x₀)) =
      x * ((xᴴ * J * x)⁻¹ * (xᴴ * J * x₀)) := by
  have hC' : IsUnit Cᴴ.det := by rw [det_conjTranspose]; exact hC.map (starRingEnd ℂ)
  rw [gram_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, conjTranspose_mul]
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hC,
    nonsing_inv_mul_cancel_left _ _ hC']

/-- Let `g`, `k` be unitary for the diagonal form with signs `t' ⊕ᵥ s` and `u` unitary for the form
with signs `t'`. If `k * x₀ * u = g⁻¹ * x₀`, where `x₀ = fromRows 1 0` is the frame of the first
summand, then `g * k * diag(u, 1)` fixes `x₀` and so is `diag(1, q)` with `q` unitary for `s`. -/
lemma exists_sum_one_eq_mul_mul_sum {t' : b → ℤˣ}
    {g k : U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {u : U (signMatrix t' : Matrix b b ℂ)}
    (h_frame : (k : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) *
        (u : Matrix b b ℂ) =
      (↑g⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)) :
    ∃ q : U (signMatrix s : Matrix n n ℂ),
      U.sum (signMatrix_sum t' s) (1, q) = g * k * U.sum (signMatrix_sum t' s) (u, 1) := by
  refine (mem_range_sum_right (signMatrix_sum t' s) isUnit).2 ?_
  have h_fix : (g : Matrix (b ⊕ n) (b ⊕ n) ℂ) * ((k : Matrix (b ⊕ n) (b ⊕ n) ℂ) *
      fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * (u : Matrix b b ℂ)) = fromRows 1 0 := by
    rw [h_frame, ← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mul]
  have h_blk : (U.sum (signMatrix_sum t' s) (u, 1) : Matrix (b ⊕ n) (b ⊕ n) ℂ) =
      fromCols (fromRows (u : Matrix b b ℂ) 0) (fromRows 0 1) := by
    rw [fromCols_fromRows_eq_fromBlocks]
    rfl
  have h_u : fromRows (u : Matrix b b ℂ) (0 : Matrix n b ℂ) =
      fromRows (1 : Matrix b b ℂ) 0 * (u : Matrix b b ℂ) := by
    rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, h_blk,
    mul_fromCols, toCols₁_fromCols, h_u, Matrix.mul_assoc,
    ← Matrix.mul_assoc (k : Matrix (b ⊕ n) (b ⊕ n) ℂ), h_fix]

/-- The coordinates at the infinite places of an `a × b` matrix, read as one complex matrix for each
place. -/
noncomputable def placeMatrices (E a b : Type) [Field E] [CMType E] [Fintype a] [Fintype b] :
    (InfinitePlace E × a × b → ℂ) ≃L[ℝ] InfinitePlace E → Matrix a b ℂ :=
  (LinearEquiv.curry ℝ ℂ (InfinitePlace E) (a × b) ≪≫ₗ LinearEquiv.piCongrRight
    fun _ : InfinitePlace E ↦ LinearEquiv.curry ℝ ℂ a b).toContinuousLinearEquiv

/-- The real slice at an adelic matrix `x` is the slice at its coordinates at infinity. -/
lemma realSlice_eq_slice_placeMatrices_symm (D : X.Splitting W₁ b) [IsBaseAdapted D] {t : a → ℤˣ}
    (V : Space E a t) (x : Matrix a b (𝔸 E)) :
    realSlice D V x =
      (isAdapted_homSource D V).mixedModel.slice ((placeMatrices E a b).symm (atRealPlace x)) :=
  rfl

/-- For a function `γ` that inverts Gram matrices, the projection of the frame `fromRows 1 0` of the
first summand to the span of the frame `x`, orthogonal for the form with signs `t' ⊕ᵥ s`. -/
def frameProjection {t' : b → ℤˣ} (γ : Matrix b b ℂ → Matrix b b ℂ) (x : Matrix (b ⊕ n) b ℂ) :
    Matrix (b ⊕ n) b ℂ :=
  x * (γ (xᴴ * signMatrix (t' ⊕ᵥ s) * x) * (xᴴ * signMatrix (t' ⊕ᵥ s) * fromRows 1 0))

private lemma contDiff_frameProjection {t' : b → ℤˣ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    (hγ : ContDiff ℝ ∞ γ) : ContDiff ℝ ∞ (frameProjection (t' := t') (s := s) γ) := by
  have hJ : ContDiff ℝ ∞ fun x : Matrix (b ⊕ n) b ℂ ↦ xᴴ * signMatrix (t' ⊕ᵥ s) :=
    contDiff_mat_mul (contDiff_conjTranspose.comp contDiff_id) contDiff_const
  exact contDiff_mat_mul contDiff_id
    (contDiff_mat_mul (hγ.comp (contDiff_mat_mul hJ contDiff_id))
      (contDiff_mat_mul hJ contDiff_const))

/-- The family `x` of frames moved by the inverses of the unitary elements `k (y v)`. -/
def unitaryMovedFrame {t' : b → ℤˣ}
    (k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (y x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : InfinitePlace E → Matrix (b ⊕ n) b ℂ :=
  fun v : InfinitePlace E ↦ (↑(k (y v))⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x v

/-- For families `y`, `x` of frames, one for each infinite place `w`, unitary elements `k y` indexed
by frames, a constant `κ` and vectors `v`, `v₁` in the Fock spaces `PairFock` of the signs `(s, t')`
and `(s, s)`, the vector `(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * M w)) • ω (1, k ∘ y) (v ⊠
v₁)`, where `x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block,
`ω` is the real Weil representation `realPairWeil` twisted by `det ^ (j - M w)` on the unitary group
of `t' ⊕ᵥ s`, and `⊠` is the external product `realBoxProd`. In the applications `t'` and `s` are
the signs of spaces `V'` and `W₁`, `j` is half the rank of `W₁`, `M` is the weight of a character,
and this vector is a prescribed slice for the pair `(X, V' ⊕ W₁)`. -/
noncomputable def exchangeSection {t' : b → ℤˣ}
    (σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ)
    (k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) (v : PairFock E s t') (v₁ : PairFock E s s)
    (y x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : PairFock E s (t' ⊕ᵥ s) :=
  ((σ y * σ (unitaryMovedFrame k y x)) •
      ((∏ w : InfinitePlace E, (unitaryMovedFrame k y x w).toRows₁ᴴ.det ^ (M w * 2)) * κ)) •
    realPairWeil (fun w : InfinitePlace E ↦ (j : ℤ) - M w) 0 (1, k ∘ y)
      (realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl)) v v₁)

/-- Let `σ ≥ 0` be a smooth compactly supported function on families of frames in `V' ⊕ W₁`, equal
to 1 at the frame `(1, 0)` of `V'`, let `N` be a family of exponents and `v` a Schwartz vector (all
moments finite) in the Fock space `PairFock E s t'` of `(W₁, V')`. There are `κ` and a Schwartz
vector `Λ` for `(X, V')` whose slice at an adelic matrix with infinite components `x w`
(`atRealPlace`) is `σ (x, 0) * ‖∏ w, det (x w) ^ N w‖ ^ 2 * κ` times `v`, and whose slice at 0 for
`D.symm`, the splitting with the two isotropic frames exchanged, is `v`. -/
lemma exists_isSchwartzVector_realSlice_bump (D : X.Splitting W₁ b) [IsBaseAdapted D] {t' : b → ℤˣ}
    (V' : Space E b t') (N : InfinitePlace E → ℕ)
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (hσ_cpt : HasCompactSupport σ) (hσ₀ : ∀ x : InfinitePlace E → Matrix (b ⊕ n) b ℂ, 0 ≤ σ x)
    (hσ₁ : σ (fun _ : InfinitePlace E ↦ fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)) = 1)
    {v : PairFock E s t'} (hv : IsSchwartzVector v) :
    ∃ (κ : ℂ) (Λ : PairFock E r t'),
      IsSchwartzVector Λ ∧
      realSlice D.symm V' 0 Λ = v ∧
      ∀ x : Matrix b b (𝔸 E), realSlice D V' x Λ =
        ((σ (fun w : InfinitePlace E ↦ fromRows (1 : Matrix b b ℂ) 0 * atRealPlace x w) *
          ‖∏ w : InfinitePlace E, (atRealPlace x w).det ^ N w‖ ^ 2) • κ) • v := by
  let C := placeMatrices E b b
  let τ (x : InfinitePlace E → Matrix b b ℂ) : ℝ :=
    σ (fun w ↦ fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * x w) * ‖∏ w, (x w).det ^ N w‖ ^ 2
  have τ_smooth : ContDiff ℝ ∞ (τ ∘ C) :=
    (hσ.comp (contDiff_pi.2 fun w ↦ contDiff_mat_mul contDiff_const
      (contDiff_pi.1 C.contDiff w))).mul
      (.norm_sq ℂ (contDiff_finset_prod fun w _ ↦
        (contDiff_mat_det (contDiff_pi.1 C.contDiff w)).pow (N w)))
  -- `x` is recovered from the frame `(x, 0)`, which lies in the support of `σ`.
  have τ_cpt : HasCompactSupport (τ ∘ C) := by
    have h_cont : Continuous (C.symm ∘ fun (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) w ↦
        (fromRows 1 0 : Matrix (b ⊕ n) b ℂ)ᴴ * x w) :=
      C.symm.continuous.comp (continuous_pi fun w ↦
        continuous_mat_mul continuous_const (continuous_apply w))
    refine (hσ_cpt.image h_cont).closure_of_subset fun x hx ↦
      ⟨fun w ↦ fromRows 1 0 * C x w, subset_closure (left_ne_zero_of_mul hx), ?_⟩
    apply C.injective
    rw [Function.comp_apply, C.apply_symm_apply]
    funext w
    rw [← Matrix.mul_assoc, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
      conjTranspose_one, conjTranspose_zero, Matrix.one_mul, Matrix.zero_mul, add_zero,
      Matrix.one_mul]
  obtain ⟨κ, Λ, hΛ, hΛ₀, hΛ_slice⟩ := exists_isSchwartzVector_realSlice_eq D V' (τ ∘ C) τ_smooth hv
    τ_cpt
    (fun _ ↦ mul_nonneg (hσ₀ _) (sq_nonneg _)) (C.symm fun _ ↦ 1) (by
      simp only [Function.comp_apply, C.apply_symm_apply, τ, Matrix.mul_one, hσ₁, det_one, one_pow,
        prod_const_one, norm_one, mul_one, ne_eq, one_ne_zero, not_false_eq_true])
  exact ⟨κ, Λ, hΛ, hΛ₀, fun x ↦ by
    rw [realSlice_eq_slice_placeMatrices_symm, hΛ_slice, Function.comp_apply, C.apply_symm_apply,
      map_one, one_apply_eq_self]⟩

/-- Let `σ` be smooth with compact support, `z` and `k` smooth maps on frames, and `v`, `v₁`
Schwartz vectors (all moments finite) in the Fock spaces `PairFock` of `(W₁, V')` and `(W₁, W₁)`.
Then some Schwartz vector `Φ` in the Fock space of `(X, V' ⊕ W₁)` has slice
`exchangeSection σ k j M κ v v₁ y x` at every adelic matrix with infinite components `x`, for
`y = z ∘ x`. -/
lemma exists_isSchwartzVector_exchangeSection (D : X.Splitting W₁ b) [IsBaseAdapted D] {t' : b → ℤˣ}
    (V' : Space E b t') {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hσ_cpt : HasCompactSupport σ)
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    (hk : ContDiff ℝ ∞ fun y : Matrix (b ⊕ n) b ℂ ↦ (k y : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    {z : Matrix (b ⊕ n) b ℂ → Matrix (b ⊕ n) b ℂ} (hz : ContDiff ℝ ∞ z)
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) {v : PairFock E s t'} {v₁ : PairFock E s s}
    (hv : IsSchwartzVector v) (hv₁ : IsSchwartzVector v₁) :
    ∃ Φ : fockSpace (realSigns E (homSigns r (t' ⊕ᵥ s))),
      IsSchwartzVector Φ ∧
      ∀ x : Matrix (b ⊕ n) b (𝔸 E), realSlice D (V'.sum W₁) x Φ =
        exchangeSection σ k j M κ v v₁ (z ∘ atRealPlace x) (atRealPlace x) := by
  let C := placeMatrices E (b ⊕ n) b
  let S (y : Matrix (b ⊕ n) b ℂ) : Matrix (b ⊕ n) (b ⊕ n) ℂ := k y
  replace hk : ContDiff ℝ ∞ S := hk
  let w (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) := unitaryMovedFrame k (z ∘ x) x
  -- The scalar of the section, times the determinant factor of `realPairWeil`.
  let τ (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : ℂ := (σ (z ∘ x) * σ (w x)) •
    ((∏ p, star (w x p).toRows₁.det ^ (M p * 2)) * κ *
      ((∏ p, (S (z (x p))).det ^ j) * ∏ p, star (S (z (x p))).det ^ M p))
  have section_eq (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) :
      exchangeSection σ k j M κ v v₁ (z ∘ x) x = τ x • realWeil (pairHomInf (1, k ∘ z ∘ x))
        (realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl)) v v₁) := by
    have h_inv_det (p : InfinitePlace E) : ((S (z (x p))).det)⁻¹ = star (S (z (x p))).det := by
      have hd := congrArg Matrix.det (U.coe_inv IsHermitianInvolution.mul_self (k (z (x p))))
      rw [Subgroup.coe_inv, coe_units_inv, det_nonsing_inv, Ring.inverse_eq_inv',
        det_mul, det_mul, det_conjTranspose, mul_right_comm, ← det_mul,
        IsHermitianInvolution.mul_self, det_one, one_mul] at hd
      exact hd
    rw [exchangeSection, realPairWeil, MonoidHom.coe_mk, OneHom.coe_mk, _root_.smul_apply,
      smul_smul]
    congr 1
    dsimp only [τ, w]
    rw [smul_mul_assoc]
    congr 1
    congr 1
    · simp only [det_conjTranspose]
    · rw [← prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ ↦ ?_
      rw [Pi.zero_apply, neg_zero, zpow_zero, mul_one, Function.comp_apply, Function.comp_apply,
        zpow_sub₀ (GeneralLinearGroup.det_ne_zero (k (z (x p))).val), div_eq_mul_inv,
        zpow_natCast, zpow_natCast, ← inv_pow, h_inv_det p]
  -- `τ` is `σ * σ` times a polynomial in the entries of `x` and `k (z x)` and their conjugates.
  have τ_smooth : ContDiff ℝ ∞ (τ ∘ C) := by
    have w_eq (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) : w x = fun p ↦
        signMatrix (t' ⊕ᵥ s) * (S (z (x p)))ᴴ * signMatrix (t' ⊕ᵥ s) * x p :=
      funext fun p ↦ congrArg (· * x p) (U.coe_inv IsHermitianInvolution.mul_self _)
    simp only [τ, w_eq, comp_def, det_apply, Matrix.mul_assoc, toRows₁_apply, star_sum, star_smul,
      star_prod, star_def]
    fun_prop
  -- On the support, `x = k y * w x` with `y = z ∘ x` and `w x` in the support of `σ`.
  have τ_cpt : HasCompactSupport (τ ∘ C) := by
    have h_cont : Continuous (C.symm ∘ fun (p : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) ×
        (InfinitePlace E → Matrix (b ⊕ n) b ℂ)) v ↦ S (p.1 v) * p.2 v) :=
      C.symm.continuous.comp (continuous_pi fun v ↦
        continuous_mat_mul (hk.continuous.comp ((_root_.continuous_apply v).comp continuous_fst))
          ((_root_.continuous_apply v).comp continuous_snd))
    refine ((hσ_cpt.prod hσ_cpt).image h_cont).closure_of_subset fun x hx ↦ ?_
    have hσ_ne : σ (z ∘ C x) ≠ 0 ∧ σ (w (C x)) ≠ 0 := mul_ne_zero_iff.1 (left_ne_zero_of_smul hx)
    refine ⟨(z ∘ C x, w (C x)), closure_prod_eq.le (subset_closure hσ_ne), ?_⟩
    apply C.injective
    rw [Function.comp_apply, C.apply_symm_apply]
    funext v
    simp only [S, w, unitaryMovedFrame, Function.comp_apply, ← Matrix.mul_assoc, ← Units.val_mul,
      ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one, Matrix.one_mul]
  -- The entries of the unitary matrix are entries of `k (z x)` or `0`.
  have u_smooth : ContDiff ℝ ∞ fun x ↦ (pairHomInf (1, k ∘ z ∘ C x) : USign
      (realSigns E (homSigns s (t' ⊕ᵥ s)))).val.val := by
    refine contDiff_pi' fun p ↦ contDiff_pi' fun q ↦ ?_
    have h_eq : (fun x ↦ (pairHomInf (1, k ∘ z ∘ C x) : USign
        (realSigns E (homSigns s (t' ⊕ᵥ s)))).val.val p q) = fun x ↦
        if p.1 = q.1 then if p.2.2 = q.2.2 then S (z (C x p.1)) p.2.1 q.2.1 else 0 else 0 := by
      funext x
      change blockDiagonal (fun w ↦ (pairHom (t' ⊕ᵥ s) s (1, k (z (C x w))) :
        Matrix ((b ⊕ n) × n) ((b ⊕ n) × n) ℂ)) (p.2, p.1) (q.2, q.1) = _
      rw [blockDiagonal_apply]
      by_cases h1 : p.1 = q.1
      · rw [ite_eq_left h1, ite_eq_left h1, coe_pairHom, kroneckerMap_apply]
        have h_one : (1 : Matrix n n ℂ)⁻¹ = 1 := Matrix.inv_eq_left_inv (Matrix.one_mul 1)
        simp only [S, Subgroup.coe_one, Units.val_one, h_one, transpose_one,
          Matrix.one_apply, mul_ite, mul_one, mul_zero]
      · rw [ite_eq_right h1, ite_eq_right h1]
    rw [h_eq]
    split_ifs
    · exact contDiff_pi.1 (contDiff_pi.1
        (hk.comp (hz.comp (contDiff_pi.1 C.contDiff p.1))) p.2.1) q.2.1
    · exact contDiff_const
    · exact contDiff_const
  obtain ⟨Φ, hΦ, hΦ_slice⟩ := exists_isSchwartzVector_slice_eq
    (isAdapted_homSource D (V'.sum W₁)).mixedModel
    τ_smooth τ_cpt u_smooth (isSchwartzVector_realBoxProd _ hv hv₁)
  refine ⟨Φ, hΦ, fun x ↦ ?_⟩
  rw [realSlice_eq_slice_placeMatrices_symm, hΦ_slice, section_eq, Function.comp_apply,
    C.apply_symm_apply]

omit [WeilData E] in
/-- For families `y`, `x` of frames, one for each infinite place `w`, and vectors `v₀`, `v₁` in the
Fock spaces `PairFock` of the signs `(s, t')` and `(s, s)`, the value `exchangeSection σ k j M κ v₀
v₁ y x` is `(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * M w)) • ω (1, k ∘ y) (v₀ ⊠ v₁)`, where
`x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block, `ω` is the
real Weil representation `realPairWeil` twisted by `det ^ (j - M w)` on the unitary group of `t' ⊕ᵥ
s`, and `⊠` is the external product `realBoxProd`. Write `frameProjection γ x` for the projection of
the frame `(1, 0)` to the span of the frame `x`, with `γ` in the place of the inversion of the Gram
matrix. If `γ` inverts the Gram matrices of the frames on which `σ` is nonzero and of each `x w`,
then in the section with second argument `A w = x w * C w` (`C w` invertible) and first argument the
projections for `A`, these may be replaced by the projections for `x`. -/
lemma exchangeSection_frameProjection_mul {t' : b → ℤˣ}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    (k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (hγ_supp : ∀ y : InfinitePlace E → Matrix (b ⊕ n) b ℂ, σ y ≠ 0 → ∀ w : InfinitePlace E,
      γ ((y w)ᴴ * signMatrix (t' ⊕ᵥ s) * y w) = ((y w)ᴴ * signMatrix (t' ⊕ᵥ s) * y w)⁻¹)
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) (v₀ : PairFock E s t') (v₁ : PairFock E s s)
    (x : InfinitePlace E → Matrix (b ⊕ n) b ℂ) (C : InfinitePlace E → GL b ℂ)
    (hγx : ∀ w : InfinitePlace E,
      γ ((x w)ᴴ * signMatrix (t' ⊕ᵥ s) * x w) = ((x w)ᴴ * signMatrix (t' ⊕ᵥ s) * x w)⁻¹) :
    exchangeSection σ k j M κ v₀ v₁
        (frameProjection (t' := t') (s := s) γ ∘ fun w : InfinitePlace E ↦ x w * (C w).val)
        (fun w : InfinitePlace E ↦ x w * (C w).val) =
      exchangeSection σ k j M κ v₀ v₁ (frameProjection (t' := t') (s := s) γ ∘ x)
        (fun w : InfinitePlace E ↦ x w * (C w).val) := by
  set A : InfinitePlace E → Matrix (b ⊕ n) b ℂ := fun w ↦ x w * (C w).val
  rcases forall_or_exists_not fun y ↦ σ (unitaryMovedFrame k y A) = 0 with hσ_zero | ⟨y, hy⟩
  · simp only [exchangeSection, hσ_zero, mul_zero, zero_smul]
  -- It is enough to see that `A w` and `x w` give the same projection.
  refine congrArg (exchangeSection σ k j M κ v₀ v₁ · A) (funext fun w ↦ ?_)
  have hγA : γ ((A w)ᴴ * signMatrix (t' ⊕ᵥ s) * A w) = ((A w)ᴴ * signMatrix (t' ⊕ᵥ s) * A w)⁻¹ := by
    simpa only [unitaryMovedFrame, U.gram_invariant] using hγ_supp _ hy w
  simp only [Function.comp_apply, frameProjection, hγA, hγx, A]
  exact mul_gram_inv_mul_of_isUnit_det _ (x w) _ (isUnits_det_units _)

omit [CMType E] [WeilData E] in
/-- If each frame `(h v)⁻¹ * fromRows 1 0` is `k v * fromRows 1 0 * c` with `c` carrying the form
with signs `t'` to its Gram matrix, then `c` is a unitary `u v`, and for some unitary `q v` one has
`diag(u v, (q v)⁻¹) * h v * k v = 1`. -/
lemma exists_unitary_pair_of_frame {t' : b → ℤˣ}
    (h k : InfinitePlace E → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ))
    (hframe : ∀ v : InfinitePlace E, ∃ c : Matrix b b ℂ,
      (k v : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * c =
        (↑(h v)⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) ∧
      cᴴ * signMatrix t' * c = signMatrix t') :
    ∃ (u : InfinitePlace E → U (signMatrix t' : Matrix b b ℂ))
      (q : InfinitePlace E → U (signMatrix s : Matrix n n ℂ)),
      ∀ v : InfinitePlace E,
        (k v : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) *
            (u v : Matrix b b ℂ) =
          (↑(h v)⁻¹ : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) ∧
        U.sum (signMatrix_sum t' s) (u v, (q v)⁻¹) * h v * k v = 1 := by
  choose c hc c_gram using hframe
  choose u hu_eq using fun v ↦ exists_U_coe_eq (c_gram v)
  simp only [← hu_eq] at hc
  choose q hq using fun v ↦ exists_sum_one_eq_mul_mul_sum (hc v)
  refine ⟨u, q, fun v ↦ ⟨hc v, ?_⟩⟩
  let φ := U.sum (signMatrix_sum t' s)
  have hhk : h v * k v = φ ((1, q v) * (u v, 1)⁻¹) := by
    rw [φ.map_mul, φ.map_inv, hq, mul_inv_cancel_right]
  rw [mul_assoc, hhk, ← φ.map_mul]
  simp only [Prod.inv_mk, Prod.mk_mul_mk, one_mul, inv_one, mul_one, mul_inv_cancel,
    inv_mul_cancel, Prod.mk_one_one, φ.map_one]

omit [WeilData E] in
/-- Let `𝔠` be a tame character (`SplitTameChar`) of weight `μ ≥ 0` with automorphic character
`ν = 𝔠.character` of the norm-one ideles, so that `ν` has weight `μ w` at each infinite place `w`,
and let `z` be the idele with infinite part `ζ` and finite part 1. Then the product of the
`conj (ζ w) ^ (2 μ w)` is `‖∏ ζ w ^ (j + μ w)‖ ^ 2 / (ν(z / z̄) |z| ^ j)`. -/
lemma prod_conj_pow_eq_norm_div {μ : InfinitePlace E → ℕ}
    (𝔠 : SplitTameChar E fun w : InfinitePlace E ↦ (μ w : ℤ)) (j : ℕ) (ζ : (InfinitePlace E → ℂ)ˣ) :
    ∏ w : InfinitePlace E, star (ζ.val w) ^ (μ w * 2) =
      (‖∏ w : InfinitePlace E, ζ.val w ^ (j + μ w)‖ ^ 2 : ℝ) /
        ((𝔠.character.baseChange.val (ζ.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E))) : ℂ) *
          √(ideleAbs (ζ.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E)))) ^ (2 * j)) := by
  set z := ζ.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E))
  set P : ℂ := ∏ w, ζ.val w with hP
  set Q : ℂ := ∏ w, ζ.val w ^ μ w with hQ
  have hζ (w : InfinitePlace E) : ζ.val w ≠ 0 := (ζ.isUnit.apply w).ne_zero
  have hP₀ : (‖P‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 <| norm_ne_zero_iff.2 <|
    Finset.prod_ne_zero_iff.2 fun w _ ↦ hζ w
  have hQ₀ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ ↦ pow_ne_zero _ (hζ w)
  have h_char : (𝔠.character.baseChange.val z : ℂ) = Q ^ 2 / ‖Q‖ ^ 2 := by
    rw [𝔠.hasWeight.baseChange_apply_inf, hQ, norm_prod, Complex.ofReal_prod,
      ← prod_pow, ← prod_pow]
    trans ∏ w, (ζ.val w ^ μ w) ^ 2 / (‖ζ.val w ^ μ w‖ : ℂ) ^ 2
    · refine Finset.prod_congr rfl fun w _ ↦ ?_
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, _root_.zpow_mul, zpow_natCast,
        zpow_two, ← sq, div_pow, norm_pow, Complex.ofReal_pow, pow_right_comm _ 2]
    · exact Finset.prod_div_distrib _ _
  have h_abs : √(ideleAbs z) = ‖P‖ := by
    rw [ideleAbs_eq_prod_of_v_eq_one (fun w ↦ by change Valued.v (1 : _) = 1; exact map_one _),
      prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _), hP, norm_prod]
    rfl
  have h_lhs : ∏ w, star (ζ.val w) ^ (μ w * 2) = star Q ^ 2 := by
    simp only [hQ, pow_mul, ← prod_pow, star_prod, star_pow]
  have h_num : ∏ w, ζ.val w ^ (j + μ w) = P ^ j * Q := by
    simp only [hP, hQ, pow_add, prod_mul_distrib, prod_pow]
  have h_conj : star Q = ‖Q‖ ^ 2 / Q := by rw [eq_div_iff hQ₀, star_def, conj_mul']
  push_cast [h_lhs, h_char, h_abs, h_num, h_conj, norm_mul, norm_pow]
  field

omit [WeilData E] in
/-- For families `y`, `x` of frames, one for each infinite place `w`, and vectors `v`, `v₁` in the
Fock spaces `PairFock` of the signs `(s, t')` and `(s, s)`, the value `exchangeSection σ k j M κ v
v₁ y x` is `(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * M w)) • ω (1, k ∘ y) (v ⊠ v₁)`, where
`x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block, `ω` is the
real Weil representation `realPairWeil` twisted by `det ^ (j - M w)` on the unitary group of `t' ⊕ᵥ
s`, and `⊠` is the external product `realBoxProd` (its first argument is the proof that the signs
split accordingly). Suppose that `g * (k ∘ y) = 1` and `x' = (B, 0)` whenever `σ y ≠ 0`. Then `ω (1,
g)` carries this value to `σ y * σ (B, 0) * κ * ∏ w, conj (det (B w)) ^ (2 * M w)` times `v ⊠ v₁`.
-/
lemma realPairWeil_exchangeSection {t' : b → ℤˣ} {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    (j : ℕ) (M : InfinitePlace E → ℕ) (κ : ℂ) (v : PairFock E s t') (v₁ : PairFock E s s)
    {y x : InfinitePlace E → Matrix (b ⊕ n) b ℂ} {g : GInf E (t' ⊕ᵥ s)}
    {B : InfinitePlace E → Matrix b b ℂ} (hg : σ y ≠ 0 → g * (k ∘ y) = 1)
    (hx : σ y ≠ 0 → unitaryMovedFrame k y x = fun w : InfinitePlace E ↦ fromRows (B w) 0) :
    realPairWeil (fun w : InfinitePlace E ↦ (j : ℤ) - M w) 0 (1, g)
        (exchangeSection σ k j M κ v v₁ y x) =
      ((σ y * σ fun w : InfinitePlace E ↦ fromRows (B w) 0) •
          ((∏ w : InfinitePlace E, star (B w).det ^ (M w * 2)) * κ)) •
        realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl)) v v₁ := by
  by_cases hσ : σ y = 0
  · simp only [exchangeSection, hσ, zero_mul, zero_smul, map_zero]
  let ρ := realPairWeil (s := s) (s' := t' ⊕ᵥ s) (fun w : InfinitePlace E ↦ (j : ℤ) - M w) 0
  rw [exchangeSection, map_smul, ← mul_apply_eq_comp, ← ρ.map_mul, hx hσ, Prod.mk_mul_mk,
    one_mul, hg hσ, Prod.mk_one_one, ρ.map_one, one_apply_eq_self]
  simp only [toRows₁_fromRows, det_conjTranspose]

omit [WeilData E] in
/-- Let `h` be a point of `GInf E (t' ⊕ᵥ s)`, the unitary group for the signs `t' ⊕ᵥ s` at the
infinite places. Let `u`, `q` be points of `GInf E t'` and `GInf E s`. All three are completed by
`1` at the finite places to adelic points, and `G.sum` is the block sum of `u` and `q`. At each
infinite place `w`, the adelic matrix `(diag(u, q) * h)⁻¹ * fromRows B 0` has component
`h⁻¹ * fromRows 1 0 * u⁻¹ * B`. -/
lemma atRealPlace_inv_sum_mul_fromRows {t' : b → ℤˣ} (u : GInf E t') (q : GInf E s)
    (h : GInf E (t' ⊕ᵥ s)) (B : Matrix b b (𝔸 E)) (w : InfinitePlace E) :
    atRealPlace (G.adeleMatrix ((G.sum ((u, 1), q, 1)).1 * h, 1)⁻¹ * fromRows (m₂ := n) B 0) w =
      (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) *
        ((↑(u⁻¹ w) : Matrix b b ℂ) * atRealPlace B w) := by
  let φ : 𝔸 E →+* ℂ := (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
  have h_mul : atRealPlace (G.adeleMatrix ((G.sum ((u, 1), q, 1)).1 * h, 1)⁻¹ *
      fromRows (m₂ := n) B 0) w =
      atRealPlace (G.adeleMatrix ((G.sum ((u, 1), q, 1)).1 * h, 1)⁻¹) w *
        atRealPlace (fromRows (m₂ := n) B 0) w :=
    Matrix.map_mul (f := φ)
  have h_g : atRealPlace (G.adeleMatrix ((G.sum ((u, 1), q, 1)).1 * h, 1)⁻¹) w =
      (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) *
        fromBlocks (↑(u⁻¹ w) : Matrix b b ℂ) 0 0 (↑(q⁻¹ w) : Matrix n n ℂ) := by
    have h_sum : (((G.sum ((u, 1), q, 1)).1)⁻¹ w : Matrix (b ⊕ n) (b ⊕ n) ℂ) =
        fromBlocks (↑(u⁻¹ w) : Matrix b b ℂ) 0 0 (↑(q⁻¹ w) : Matrix n n ℂ) := by
      change (↑((U.sum (signMatrix_sum t' s) (u w, q w))⁻¹) : Matrix (b ⊕ n) (b ⊕ n) ℂ) = _
      rw [← (U.sum (signMatrix_sum t' s)).map_inv]
      rfl
    refine Matrix.ext fun i j ↦ ?_
    rw [atRealPlace, Matrix.map_apply, G.adeleMatrix_fst, Prod.inv_mk]
    dsimp only
    rw [pi_mul_inv_apply, Subgroup.coe_mul, Units.val_mul, h_sum]
  have h_rows : atRealPlace (fromRows (m₂ := n) B 0) w = fromRows (atRealPlace B w) 0 := by
    refine Matrix.ext fun i j ↦ ?_
    cases i <;> rfl
  have h_from : fromRows ((↑(u⁻¹ w) : Matrix b b ℂ) * atRealPlace B w) (0 : Matrix n b ℂ) =
      fromRows (1 : Matrix b b ℂ) 0 * ((↑(u⁻¹ w) : Matrix b b ℂ) * atRealPlace B w) := by
    rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  rw [h_mul, h_g, h_rows, Matrix.mul_assoc]
  simp only [fromBlocks_mul_fromRows, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [h_from, ← Matrix.mul_assoc]

/-- The Gram matrix of the frame `fromRows 1 0` of the first summand, for the form with signs
`t' ⊕ᵥ s`, is the form with signs `t'`. -/
lemma gram_signMatrix_fromRows_one_zero (t' : b → ℤˣ) (s : n → ℤˣ) :
    (fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ))ᴴ * signMatrix (t' ⊕ᵥ s) *
      fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) = signMatrix t' := by
  simp [← signMatrix_sum, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows]

omit [WeilData E] in
/-- Let `γ`, `k`, `σ` be smooth Witt data near `x₀ = fromRows 1 0` for the form with signs `t' ⊕ᵥ s`
(`IsWittBump`): for each member `z` of a family of frames where the bump function `σ` is nonzero,
`γ` inverts the Gram matrix of `z` and `z` lies in the span of `k z * x₀`, with `k z` unitary. Let
`y w = frameProjection γ (x w)` be the projection of `x₀` to the span of the frame `x w`, with `γ`
in the place of the inverse Gram matrix. If `σ y ≠ 0`, then `x w = k (y w) * x₀ * c` for a matrix
`c` that carries the form with signs `t'` to the Gram matrix of `x w`. -/
lemma IsWittBump.exists_mul_fromRows_mul_eq_of_ne_zero
    {t' : b → ℤˣ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hW : IsWittBump (signMatrix (t' ⊕ᵥ s)) (fromRows 1 0) γ k σ)
    {x : InfinitePlace E → Matrix (b ⊕ n) b ℂ}
    (hx : σ (frameProjection (t' := t') (s := s) γ ∘ x) ≠ 0) (w : InfinitePlace E) :
    ∃ c : Matrix b b ℂ,
      (k (frameProjection (t' := t') (s := s) γ (x w)) : Matrix (b ⊕ n) (b ⊕ n) ℂ) *
        fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ) * c = x w ∧
      cᴴ * signMatrix t' * c = (x w)ᴴ * signMatrix (t' ⊕ᵥ s) * x w := by
  obtain ⟨c, hc⟩ := hW.exists_mul_eq _ hx w
  rw [← gram_signMatrix_fromRows_one_zero t' s]
  exact exists_mul_mul_eq_and_gram_eq _ hc (hW.det_gram_ne_zero _ hx w)

omit [WeilData E] in
/-- Let `γ`, `k`, `σ` be smooth Witt data near `x₀ = fromRows 1 0` for the form with signs `t' ⊕ᵥ s`
(`IsWittBump`); in particular `γ` inverts the Gram matrix of `x₀` and the bump function `σ` is `1`
at the constant family `x₀`. For `h` near `1` in `GInf`, the product of the unitary groups of the
form over the infinite places, `σ` does not vanish at the family of projections `frameProjection γ`
of `x₀` to the spans of the frames `(h w)⁻¹ * x₀`, formed with `γ` in the place of the inverse Gram
matrix. -/
lemma IsWittBump.eventually_bump_frameProjection_ne_zero
    {t' : b → ℤˣ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hW : IsWittBump (signMatrix (t' ⊕ᵥ s)) (fromRows 1 0) γ k σ) :
    ∀ᶠ h : GInf E (t' ⊕ᵥ s) in nhds 1,
      σ (frameProjection (t' := t') (s := s) γ ∘ fun w : InfinitePlace E ↦
        (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * (fromRows 1 0 : Matrix (b ⊕ n) b ℂ)) ≠ 0 := by
  have γ_smooth : ContDiff ℝ ∞ γ := hW.contDiff_inv
  have σ_smooth : ContDiff ℝ ∞ σ := hW.contDiff_bump
  let x₀ : Matrix (b ⊕ n) b ℂ := fromRows 1 0
  have proj_base : frameProjection (t' := t') (s := s) γ x₀ = x₀ := by
    change x₀ * (γ (x₀ᴴ * signMatrix (t' ⊕ᵥ s) * x₀) * (x₀ᴴ * signMatrix (t' ⊕ᵥ s) * x₀)) = x₀
    rw [hW.inv_gram_base, gram_signMatrix_fromRows_one_zero,
      nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (IsHermitianInvolution.det_ne_zero (signMatrix t'))),
      Matrix.mul_one]
  have h_cont : Continuous fun h : GInf E (t' ⊕ᵥ s) ↦
      σ (frameProjection (t' := t') (s := s) γ ∘ fun w : InfinitePlace E ↦
        (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀) :=
    σ_smooth.continuous.comp (continuous_pi fun w ↦
      (contDiff_frameProjection γ_smooth).continuous.comp
        (continuous_mat_mul
          (Units.continuous_val.comp (continuous_subtypeVal.comp
            ((_root_.continuous_apply w).comp continuous_inv)))
          continuous_const))
  refine (h_cont.tendsto 1).eventually_ne ?_
  have h_at_one : (frameProjection (t' := t') (s := s) γ ∘ fun w : InfinitePlace E ↦
      (↑((1 : GInf E (t' ⊕ᵥ s))⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀) = fun _ ↦ x₀ := by
    funext w
    rw [Function.comp_apply, inv_one, Pi.one_apply, Subgroup.coe_one, Units.val_one,
      Matrix.one_mul, proj_base]
  rw [h_at_one, hW.bump_base]
  exact one_ne_zero

/-- Let `γ`, `k`, `σ` be smooth Witt data near `x₀ = fromRows 1 0` (`IsWittBump`): for frames `y`
where the bump function `σ` is nonzero, `y` lies in the span of `k y * x₀` with `k y` unitary, and
`γ` inverts the Gram matrix of `y`; `frameProjection γ x` is the projection of `x₀` to the span of
`x`, formed with `γ`. Let `D` be an adapted Witt decomposition of the Hermitian space `X` as `W₁`
plus `card b` hyperbolic planes, let `W₁` have rank `2 j` and split off a hyperbolic plane by `D₁`,
let `V'` have rank `card b`, and let `𝔠` be a tame character of weight `μ`, with automorphic
character `ν = 𝔠.character`. Let `v₁` be a Schwartz vector (all moments finite). Suppose that the
slice of `Φ` at `x` is `exchangeSection` at `x` and `y = frameProjection γ ∘ x`, namely
`(σ y * σ x' * κ * ∏ w, conj (det (x' w)₁) ^ (2 * μ w)) • ω (1, k ∘ y) (v ⊠ v₁)`, where
`x' w = (k (y w))⁻¹ * x w` (`unitaryMovedFrame`), `(x' w)₁` is its upper square block, `ω` is the
real Weil representation `realPairWeil` twisted by `det ^ (j - μ w)` on the unitary group of
`t' ⊕ᵥ s`, and `⊠` is the external product `realBoxProd`, and that the slice of `Λ` at `x` is
`σ (x, 0) * ‖∏ w, det (x w) ^ (j + μ w)‖ ^ 2 * κ` times `v`. Then `IsPeriodIdentity` holds: for each
`h` at infinity there is `p` in `U V' × U W₁` such that for all invertible `B` the theta functional
of the slice of `Φ` at `(p h)⁻¹ (B, 0)`, moved by `p h` and integrated over the adelic quotient of
`U W₁`, is `ρ h * I₀ / (ν(z / z̄) |z| ^ j)` times the theta functional of the slice of `Λ` at `B`.
Here `z` is the idele with infinite part `det B` and finite part 1, `ρ h` is `σ` at the projections
of `x₀` to the spans of `(h w)⁻¹ * x₀`, and the period `I₀` is the value at `1` of the theta
integral `thetaLarge` over `U W₁` with real part `v₁` and, at the ramified places of `𝔠`, the
function `stdColDatum`. -/
lemma IsWittBump.isPeriodIdentity {t' : b → ℤˣ} {γ : Matrix b b ℂ → Matrix b b ℂ}
    {k : Matrix (b ⊕ n) b ℂ → U (signMatrix (t' ⊕ᵥ s) : Matrix (b ⊕ n) (b ⊕ n) ℂ)}
    {σ : (InfinitePlace E → Matrix (b ⊕ n) b ℂ) → ℝ}
    (hW : IsWittBump (signMatrix (t' ⊕ᵥ s)) (fromRows 1 0) γ k σ)
    (D : X.Splitting W₁ b) [IsBaseAdapted D] {t : a → ℤˣ} {W : Space E a t}
    (D₁ : W₁.Splitting W Unit) [IsBaseAdapted D₁] (V' : Space E b t') {j : ℕ}
    (hj : Fintype.card n = 2 * j) {μ : InfinitePlace E → ℕ}
    (𝔠 : SplitTameChar E fun w : InfinitePlace E ↦ (μ w : ℤ)) {κ : ℂ} {v : PairFock E s t'}
    {v₁ : PairFock E s s} (hv₁ : IsSchwartzVector v₁) {Φ : PairFock E r (t' ⊕ᵥ s)}
    {Λ : PairFock E r t'}
    (hΦ : ∀ x : Matrix (b ⊕ n) b (𝔸 E), realSlice D (V'.sum W₁) x Φ = exchangeSection σ k j μ κ v v₁
      (frameProjection (t' := t') (s := s) γ ∘ atRealPlace x) (atRealPlace x))
    (hΛ : ∀ x : Matrix b b (𝔸 E), realSlice D V' x Λ =
      ((σ (fun w : InfinitePlace E ↦ fromRows (1 : Matrix b b ℂ) 0 * atRealPlace x w) *
        ‖∏ w : InfinitePlace E, (atRealPlace x w).det ^ (j + μ w)‖ ^ 2) • κ) • v) :
    IsPeriodIdentity X D V' 𝔠 Φ Λ
      (fun h : GInf E (t' ⊕ᵥ s) ↦ σ (frameProjection (t' := t') (s := s) γ ∘
        fun w : InfinitePlace E ↦ (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) *
          fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)))
      (thetaLarge W₁ W₁ 𝔠 v₁ (stdColDatum 𝔠.semilocalChar 1) 1) := by
  -- Fix `h` and let `y` be these projections. If `σ y ≠ 0`, then `h * k y` keeps the span of `x₀`,
  -- so it is block diagonal. Its blocks give a point at which the moved slice of `Φ` is a multiple
  -- of the product vector of `v` and `v₁`.
  intro h
  let x₀ : Matrix (b ⊕ n) b ℂ := fromRows 1 0
  let x₁ (w : InfinitePlace E) : Matrix (b ⊕ n) b ℂ := (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀
  have gram₁ (w : InfinitePlace E) : (x₁ w)ᴴ * signMatrix (t' ⊕ᵥ s) * x₁ w = signMatrix t' := by
    rw [U.gram_invariant, gram_signMatrix_fromRows_one_zero]
  have γ_inv (w : InfinitePlace E) : γ ((x₁ w)ᴴ * signMatrix (t' ⊕ᵥ s) * x₁ w) =
      ((x₁ w)ᴴ * signMatrix (t' ⊕ᵥ s) * x₁ w)⁻¹ := by
    rw [gram₁, ← gram_signMatrix_fromRows_one_zero t' s, hW.inv_gram_base]
  let y : InfinitePlace E → Matrix (b ⊕ n) b ℂ := frameProjection (t' := t') (s := s) γ ∘ x₁
  obtain ⟨u, q, huq⟩ : ∃ (u : GInf E t') (q : GInf E s), σ y ≠ 0 → ∀ w : InfinitePlace E,
      (k (y w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀ * (u w : Matrix b b ℂ) = x₁ w ∧
        U.sum (signMatrix_sum t' s) (u w, (q w)⁻¹) * h w * k (y w) = 1 := by
    by_cases hσ : σ y = 0
    · exact ⟨1, 1, fun h ↦ absurd hσ h⟩
    have hframe (w : InfinitePlace E) : ∃ c : Matrix b b ℂ,
        (k (y w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * x₀ * c = x₁ w ∧
          cᴴ * signMatrix t' * c = signMatrix t' :=
      (hW.exists_mul_fromRows_mul_eq_of_ne_zero hσ w).imp fun c hc ↦
        hc.imp_right (·.trans (gram₁ w))
    obtain ⟨u, q, huq⟩ := exists_unitary_pair_of_frame h (k ∘ y) hframe
    exact ⟨u, q, fun _ ↦ huq⟩
  refine ⟨((u, 1), q⁻¹, 1), fun B β f x g y' ↦ ?_⟩
  -- The slice of `Φ` is read at `A = h⁻¹ x₀ u⁻¹ B`, which spans the same space as `x₁ = h⁻¹ x₀`.
  let C (w : InfinitePlace E) : GL b ℂ := (u⁻¹ w).val * B.map (evalInf w)
  have C_val (w : InfinitePlace E) :
      (C w).val = (↑(u⁻¹ w) : Matrix b b ℂ) * atRealPlace B.val w := rfl
  let p : GInf E (t' ⊕ᵥ s) := (G.sum ((u, 1), q⁻¹, 1)).1 * h
  have re_A : atRealPlace (G.adeleMatrix (p, 1)⁻¹ * fromRows (m₂ := n) B.val 0) =
      fun w ↦ x₁ w * (C w).val := funext (atRealPlace_inv_sum_mul_fromRows u q⁻¹ h B.val)
  -- The group elements cancel, the moved frame is `(B, 0)`, and the period splits off `v₁`.
  have cancel (hσ : σ y ≠ 0) : p * (k ∘ y) = 1 := funext fun w ↦ (huq hσ w).2
  have moved_frame (hσ : σ y ≠ 0) : unitaryMovedFrame k y (fun w ↦ x₁ w * (C w).val) =
      fun w ↦ fromRows (atRealPlace B.val w) 0 := by
    funext w
    rw [unitaryMovedFrame, C_val, ← (huq hσ w).1]
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mul, Pi.inv_apply, mul_inv_cancel, x₀,
      fromRows_mul, Matrix.zero_mul]
  have weight_eq : (fun w ↦ (Fintype.card n : ℤ) / 2 - μ w) = fun w ↦ (j : ℤ) - μ w := by
    funext w
    rw [hj, Nat.cast_mul, Nat.cast_ofNat, Int.mul_ediv_cancel_left _ two_ne_zero]
  rw [hΦ, hΛ, re_A, exchangeSection_frameProjection_mul k hW.inv_gram j μ κ v v₁ x₁ C γ_inv,
    weight_eq, realPairWeil_exchangeSection j μ κ v v₁ cancel moved_frame]
  simp only [map_smul, smul_eq_mul, integral_const_mul, thetaOnRealData_boxProd_eq_mul]
  -- The factor of `v₁` integrates to a theta integral that does not depend on `g`.
  rw [← thetaLarge_eq_apply_one_of_even_rank D₁ 𝔠 (Dvd.intro j hj.symm) hv₁ g]
  simp only [thetaIntegral, ← infiniteDet_apply, y, x₁, x₀, prod_conj_pow_eq_norm_div 𝔠 j, hj,
    real_smul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  push_cast
  ring

/-- Let `D` be an adapted Witt decomposition of the Hermitian space `X` (signs `r`) as `W₁` (signs
`s`) plus `card b` hyperbolic planes, where `W₁` has even rank and an adapted splitting `D₁` along
an isotropic line, and let `V'` be a space with basis indexed by `b` and signs `t'`. Let `v` and
`v₁` be Schwartz vectors for `(W₁, V')` and `(W₁, W₁)`. Then there are vectors `Φ` for
`(X, V' ⊕ W₁)` and `Λ` for `(X, V')` with two properties. The slice `realSlice` of `Λ` at `0`, its
value at `0` in the mixed Schrödinger–Fock model of the splitting `D.symm` with the isotropic frames
exchanged, is `v`. And `RowColExchangeIdentity` holds: `Φ`, `Λ` are Schwartz and there is a real `C`
such that for each tame character `𝔠` of weight `μ` some `c : ℂ` has `C * ‖c‖ ^ 2 = lValueProdInt 𝔠
(rk (V' ⊕ W₁) - rk X / 2) * equalRankThetaRatio W₁ 𝔠 v₁`, and for all integral `z` the theta
integral of `Φ` and the row datum of `z` is `c` times that of `Λ` and the column datum of `z`. With
`χ` the character of `𝔠` at its ramified places, these data are `x ↦ χ⁻¹ (det)` of the matrix with
the rows of `z` and `x` ordered by `e`, and `x ↦ χ⁻¹ (det (z * x))`. -/
theorem exists_rowColExchangeIdentity_sum (D : X.Splitting W₁ b) [IsBaseAdapted D] {t : a → ℤˣ}
    {t' : b → ℤˣ} {W : Space E a t} (D₁ : W₁.Splitting W Unit) [IsBaseAdapted D₁]
    (V' : Space E b t') (e : b ⊕ b ⊕ n ≃ m) (hn : 2 ∣ Fintype.card n) (μ : InfinitePlace E → ℤ)
    {v : PairFock E s t'} {v₁ : PairFock E s s} (hv : IsSchwartzVector v)
    (hv₁ : IsSchwartzVector v₁) :
    ∃ (Φ : fockSpace (realSigns E (homSigns r (t' ⊕ᵥ s)))) (Λ : PairFock E r t'),
      realSlice D.symm V' 0 Λ = v ∧
      RowColExchangeIdentity X (V'.sum W₁) V' μ e Φ Λ fun 𝔠 : SplitTameChar E μ ↦
        equalRankThetaRatio W₁ 𝔠 v₁ := by
  -- A smooth unitary `k y` moves the span of `x₀ = fromRows 1 0` onto that of a nearby frame `y`.
  -- The vectors have bump functions as slices, the one for `V' ⊕ W₁` twisted by `k`, and
  -- `rowColExchangeIdentity_of_periods` compares periods.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Fintype.card n = 2 * j := exists_eq_mul_right_of_dvd hn
  obtain ⟨γ, k, σ, hW⟩ := exists_contDiff_witt_and_bump (ι := InfinitePlace E)
    (J := signMatrix (t' ⊕ᵥ s)) (x₀ := fromRows (1 : Matrix b b ℂ) (0 : Matrix n b ℂ)) isHermitian
    (by
      rw [gram_signMatrix_fromRows_one_zero]
      exact IsHermitianInvolution.det_ne_zero (signMatrix t'))
  let z : Matrix (b ⊕ n) b ℂ → Matrix (b ⊕ n) b ℂ := frameProjection (t' := t') (s := s) γ
  have γ_smooth : ContDiff ℝ ∞ γ := hW.contDiff_inv
  have z_smooth : ContDiff ℝ ∞ z := contDiff_frameProjection γ_smooth
  let M : InfinitePlace E → ℕ := Int.toNat ∘ μ
  obtain ⟨κ, Λ, hΛ, Λ_zero, Λ_slice⟩ :=
    exists_isSchwartzVector_realSlice_bump D V' (fun w ↦ j + M w)
      hW.contDiff_bump hW.hasCompactSupport_bump hW.bump_nonneg hW.bump_base hv
  obtain ⟨Φ, hΦ, Φ_slice⟩ := exists_isSchwartzVector_exchangeSection D V' hW.contDiff_bump
    hW.hasCompactSupport_bump hW.contDiff_unitary z_smooth j M κ hv hv₁
  -- Where the slice of `Φ` is nonzero, the frame is `k x₀ c`, and `c` represents its Gram matrix.
  have h_vanish : SlicesVanishOutside D (V'.sum W₁) t' Φ := fun x hx w ↦ by
    have hσ : σ (z ∘ atRealPlace x) ≠ 0 := fun h₀ ↦
      hx (by rw [Φ_slice, exchangeSection, h₀, zero_mul, zero_smul, zero_smul])
    obtain ⟨c, -, hc⟩ := hW.exists_mul_fromRows_mul_eq_of_ne_zero hσ w
    exact ⟨c, hc.trans (gram_atRealPlace _ w)⟩
  let ρ (h : GInf E (t' ⊕ᵥ s)) : ℝ := σ (z ∘ fun w ↦
    (↑(h⁻¹ w) : Matrix (b ⊕ n) (b ⊕ n) ℂ) * (fromRows 1 0 : Matrix (b ⊕ n) b ℂ))
  have h_period (𝔠 : SplitTameChar E μ) :
      IsPeriodIdentity X D V' 𝔠 Φ Λ ρ (thetaLarge W₁ W₁ 𝔠 v₁ (stdColDatum 𝔠.semilocalChar 1)
        1) := by
    lift μ to InfinitePlace E → ℕ using fun w ↦ (𝔠.weight_pos w).le
    exact hW.isPeriodIdentity D D₁ V' hj 𝔠 hv₁ Φ_slice Λ_slice
  exact ⟨Φ, Λ, Λ_zero, rowColExchangeIdentity_of_periods X D D₁ V' _ hn (fun _ ↦ hW.bump_nonneg _)
    hW.eventually_bump_frameProjection_ne_zero hΦ hΛ h_period (.inl h_vanish)⟩

end New.Exchange
end
end

section
/-!
# Vanishing of theta integrals descends along hyperbolic planes

If the theta integral of `(W ⊕ H, V ⊕ H)` vanishes on the multiples of the determinant vectors and
on all standard data, so does that of `(W, V)`, provided the rank of `W ⊕ H` is `2 (k + q)`, with
`q` its number of negative signs and `k ≤ min μ` a natural number. The constant term along the new
isotropic line is a non-zero multiple of the theta integral of `(W, V)` at a cone integral, formed
on the side of the summation formula on the line that the sign of `rk V - rk W / 2` selects, and
every multiple of a determinant vector of `(W, V)` is such a cone integral of one of
`(W ⊕ H, V ⊕ H)` (`exists_integral_coneIntegrand_detVector`). Only values of the `L`-function at
points `≥ 1` occur.
The file also computes the theta kernels of pairs in which one space is `0`, where the determinant
vector is the vacuum.

Notions from other files:
* `thetaLarge W V 𝔠 v Φ`: the theta integral over `[U(V)]` of `v ⊗ Φ`, a function on `G E s`;
* `stdRowDatum σ χ y`: the finite datum `x ↦ χ⁻¹ (det (y; x))`, supported where the square matrix
  `(y; x)`, with rows ordered by `σ`, is invertible and integral;
* `SplitTameChar E μ`: a tame character of weight `μ`, ramified at a finite set of split places;
* `negCount s`: the number of signs `-1` among `s`;
* `detVector s t k m F`: the determinant vector, the Fock vector of the polynomial with value the
  conjugate of `∏ w, det₊ (u₊ F w) ^ m w * det₋ (u₊ F w) ^ (m w + 2 k)` at `u`.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Exchange

open MeasureTheory Fintype Fock Space Set
open NumberField (InfinitePlace)

variable {E : Type} [Field E] [CMType E]

/-- For the tame part `χ` of a split tame character `𝔠`, the standard datum
`stdColDatum 𝔠.semilocalChar 1`, which sends an integral matrix `y` with unit determinant to
`χ⁻¹ (det y)` and all other matrices to zero, has the value `1` at the identity matrix. -/
lemma stdColDatum_one_one {n : Type} [Fintype n] [DecidableEq n] {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) :
    stdColDatum 𝔠.semilocalChar 1 (1 : Matrix n n (LocProd 𝔠.ramifiedPlaces)) = 1 := by
  simp [stdColDatum, IsIntMatrix.one, invOnUnits, IsIntegralUnit]

variable [WeilData E]

/-- For a space `W` of rank zero, the operator `W.schrodingerOp 𝔠.ramifiedPlaces Φ` (a combination
of Heisenberg operators at the ramified places `𝔠.ramifiedPlaces` that represents the function `Φ`
of finite adelic vectors) sends the vacuum `W.vacElem` to `Φ 0` times the vacuum. -/
lemma schrodingerOp_vacElem_of_isEmpty {n : Type} [Fintype n] [DecidableEq n] [IsEmpty n]
    {s : n → ℤˣ} (W : Space E n s) {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ)
    (Φ : (n → 𝔸f E) → ℂ) :
    W.schrodingerOp 𝔠.ramifiedPlaces Φ W.vacElem = Φ 0 • W.vacElem := by
  -- In rank zero `Φ` is a constant, so it is a multiple of the indicator function `boxIndicator`.
  have hΦ : Φ = Φ 0 • boxIndicator n 𝔠.ramifiedPlaces := by
    funext x
    simp [Subsingleton.eq_zero x, boxIndicator_apply]
  conv_lhs => rw [hΦ, map_smul, _root_.smul_apply,
    schrodingerOp_boxIndicator 𝔠.readsAt.disjoint_star, projOn_vacElem]

section RankZero

open Finset

variable {n : Type} [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-- For a hermitian space `W` of rank zero (`n` empty) over a CM field `E` with Weil data, the theta
functional `W.θ` takes the value `1` on the vacuum `W.vacElem` (the Gaussian times twisted lattice
indicator, as an element of 𝒮(W)). -/
lemma theta_vacElem_of_isEmpty (W : Space E n s) [IsEmpty n] : W.θ W.vacElem = 1 := by
  rw [theta_apply, vacElem_apply_eq_prod_lineTheta (fun _ ↦ Subsingleton.elim _ _), univ_eq_empty,
    Finset.prod_empty]

/-- Take the datum with the Fock vector `x` as archimedean part and the function `Φ` at the ramified
places of `𝔠`. The theta kernel of the pair `(W, 0)`, twisted by characters `α`, `β` of `[U(1)]`,
at this datum and at adelic unitary elements `(g, h)` is `β (det g)⁻¹ * Φ 0` times the theta
functional of the space `Hom(W, 0)` at the image of the vacuum under the integrated operator of
`x`. -/
lemma pairTheta_target_zero (W : Space E n s) (α β : AutChar E) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (x : PairFock E s (1 : Empty → ℤˣ))
    (Φ : Matrix Empty n (LocProd 𝔠.ramifiedPlaces) → ℂ) (g : G E s) (h : G E (1 : Empty → ℤˣ)) :
    pairTheta W (stdSpace E Empty) α β (localDatum W (stdSpace E Empty) x Φ 𝔠.readsAt) (g, h) =
      (β.val g.det : ℂ)⁻¹ * Φ 0 * (W.hom (stdSpace E Empty)).θ
        ((W.hom (stdSpace E Empty)).integrated x (W.hom (stdSpace E Empty)).vacElem) := by
  -- The space `H` of homomorphisms is `0`: the group acts trivially and `Φ` is read at `0`.
  set H : Space E (Empty × n) (homSigns s 1) := W.hom (stdSpace E Empty)
  have h_datum : localDatum W (stdSpace E Empty) x Φ 𝔠.readsAt =
      H.integrated x (Φ 0 • H.vacElem) := by
    rw [localDatum, schrodingerOp_vacElem_of_isEmpty, congrArg Φ (Subsingleton.eq_zero _)]
  rw [pairTheta, pairWeil_apply, Subsingleton.eq_one (G.onHom (g, h)), h_datum,
    Subsingleton.eq_one h]
  simp [H, mul_assoc]

/-- The theta kernel of the pair `(0, W)` twisted by `α` and `β`, at the datum with the vacuum as
archimedean part and the function `Ψ` at the ramified places of `𝔠`, is `α (det g) * Ψ 0`. -/
lemma pairTheta_source_zero (W : Space E n s) (α β : AutChar E) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (Ψ : Matrix n Empty (LocProd 𝔠.ramifiedPlaces) → ℂ)
    (h : G E (1 : Empty → ℤˣ)) (g : G E s) :
    pairTheta (stdSpace E Empty) W α β
        (localDatum (stdSpace E Empty) W vacVector Ψ 𝔠.readsAt) (h, g) =
      α.val g.det * Ψ 0 := by
  -- The space `H` of homomorphisms is `0`: the group acts trivially and `Ψ` is read at `0`.
  let H : Space E (n × Empty) (homSigns 1 s) := (stdSpace E Empty).hom W
  have h_datum : localDatum (stdSpace E Empty) W vacVector Ψ 𝔠.readsAt = Ψ 0 • H.vacElem := by
    rw [localDatum, schrodingerOp_vacElem_of_isEmpty, congrArg Ψ (Subsingleton.eq_zero _)]
    simp only [H, map_smul, projReal_eq_self_of_mem_finitePart, vacElem_mem_finitePart]
  rw [pairTheta, pairWeil_apply, Subsingleton.eq_one (G.onHom (h, g)), h_datum,
    Subsingleton.eq_one h, map_one, one_apply_eq_self, map_smul, map_smul,
    theta_vacElem_of_isEmpty H]
  simp

/-- For the pair `(W, 0)`, the theta integral at `1` of the datum with the vacuum as archimedean
part and the function `Φ` at the ramified places of `𝔠` is the volume of `[U(0)]`, the domain of
integration, times `Φ 0`. -/
lemma thetaLarge_stdSpace_empty_vacVector_one (W : Space E n s) {μ : InfinitePlace E → ℤ}
    (𝔠 : SplitTameChar E μ) (Φ : Matrix Empty n (LocProd 𝔠.ramifiedPlaces) → ℂ) :
    thetaLarge W (stdSpace E Empty) 𝔠 vacVector Φ 1 =
      (stdSpace E Empty).quotMeasure.real univ * Φ 0 := by
  have h_kernel (h : G E (1 : Empty → ℤˣ)) :
      pairTheta W (stdSpace E Empty) (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
        (localDatum W (stdSpace E Empty) vacVector Φ 𝔠.readsAt) (1, h) = Φ 0 := by
    simp only [pairTheta_target_zero, map_one, Circle.coe_one, inv_one, one_mul,
      projReal_eq_self_of_mem_finitePart, vacElem_mem_finitePart, theta_vacElem_of_isEmpty, mul_one]
  simp only [thetaLarge, thetaIntegral, h_kernel, integral_const, Complex.real_smul]

end RankZero

variable {n n' r r' b : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r']
  [DecidableEq r'] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ}
  {t' : r' → ℤˣ} {μ : InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}

variable (𝔠) in
/-- Let `W` and `V` be hermitian spaces over `E` with bases indexed by `n` and `r` and with signs
`s` and `t` at the infinite places. The theta integral of `(W, V)` for the split tame character `𝔠`,
a function on the adelic unitary group `G E s` of `W`, vanishes on all Schwartz vectors `v` (all
Fock moments finite) of the Fock space `PairFock E s t` of `Hom(W, V)` and all standard data
`stdRowDatum σ 𝔠.semilocalChar y`. Here `y` is any integral `b × n` matrix over the product of the
completions at the ramified places `𝔠.ramifiedPlaces`, and `σ` orders the rows of `y` and of an
`r × n` matrix into a square matrix. -/
def ThetaLargeVanishes (W : Space E n s) (V : Space E r t) (σ : b ⊕ r ≃ n) : Prop :=
  ∀ v : PairFock E s t, IsSchwartzVector v →
    ∀ y : Matrix b n (LocProd 𝔠.ramifiedPlaces), IsIntMatrix SemilocalField.O y →
      ∀ g : G E s, thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g = 0

variable (𝔠) in
/-- The theta integral of `(W, V)` for the split tame character `𝔠` of weight `μ` vanishes, at
every point of the adelic unitary group of `W`, on all multiples of the determinant vectors
`detVector s t k m F` with `m w = μ w - k`, and on all standard data
`stdRowDatum σ 𝔠.semilocalChar y` with `y` integral at the ramified places of `𝔠`. -/
def ThetaLargeVanishesOnDetVectors (k : ℕ) (W : Space E n s) (V : Space E r t) (σ : b ⊕ r ≃ n) :
    Prop :=
  ∀ (c : ℂ) (F : InfinitePlace E → Matrix n r ℂ) (y : Matrix b n (LocProd 𝔠.ramifiedPlaces)),
    IsIntMatrix SemilocalField.O y → ∀ g : G E s,
      thetaLarge W V 𝔠 (c • detVector s t k (fun w ↦ (μ w - k).toNat) F)
        (stdRowDatum σ 𝔠.semilocalChar y) g = 0

omit [Fintype b] [DecidableEq b] in
/-- A theta integral that vanishes on all Schwartz vectors vanishes on the multiples of the
determinant vectors. -/
lemma ThetaLargeVanishes.onDetVectors {W : Space E n s} {V : Space E r t} {σ : b ⊕ r ≃ n}
    (h_zero : ThetaLargeVanishes 𝔠 W V σ) (k : ℕ) : ThetaLargeVanishesOnDetVectors 𝔠 k W V σ :=
  fun c F ↦ h_zero _ (isSchwartzVector_smul_detVector c k _ F)

omit [Fintype b] [DecidableEq b] in
/-- Let `W`, `W₁` be hermitian spaces with the same signs `s`, and `V`, `V₁` with the same signs
`t`. If, for the split tame character `𝔠`, the theta integral of `(W, V)` at every point of the
unitary group of `W` vanishes on all multiples of determinant vectors and all standard data, so
does that of `(W₁, V₁)`. -/
lemma ThetaLargeVanishesOnDetVectors.congr_spaces {k : ℕ} {W : Space E n s} {V : Space E r t}
    {σ : b ⊕ r ≃ n} (h_zero : ThetaLargeVanishesOnDetVectors 𝔠 k W V σ) (W₁ : Space E n s)
    (V₁ : Space E r t) : ThetaLargeVanishesOnDetVectors 𝔠 k W₁ V₁ σ := by
  obtain ⟨γ, h_transport⟩ := exists_thetaLarge_thetaSmall_eq_circle_mul W W₁ V V₁ V V₁
  -- The integral of `(W₁, V₁)` at `g` is `u` times that of `(W, V)` at `γ * g`.
  obtain ⟨u, h_eq_mul⟩ := (h_transport 𝔠).left
  intro c F y hy g
  rw [h_eq_mul, h_zero c F y hy, mul_zero]

/-- Descent along one hyperbolic plane `H`. Let `A` and `X` be adapted splittings (orthonormal at
the infinite and integral at the finite places) `W' = W ⊕ H` and `V' = V ⊕ H` of hermitian spaces.
Let `W` be of even rank and `W'` of rank `2 (k + q')`, where `q'` is its number of negative signs
and `k ≤ μ w` at every infinite place `w`, for the weight `μ` of the split tame character `𝔠`.

If at every point of the unitary group of `W'` the theta integral of `(W', V')` vanishes on all
multiples of determinant vectors and all data `stdRowDatum σ' 𝔠.semilocalChar y'`, then at every
point of the unitary group of `W` that of `(W, V)` vanishes on all multiples of determinant vectors
and all data `stdRowDatum σ 𝔠.semilocalChar y`. Here `y'` and `y` are arbitrary integral matrices
at the ramified places of `𝔠`, with rows indexed by `b` and columns by the bases of `W'` and `W`;
the orderings `σ` and `σ'` of these rows and those indexed by the basis of `V`, respectively `V'`,
into a square matrix are arbitrary. -/
theorem ThetaLargeVanishesOnDetVectors.of_add_plane {k : ℕ} {W : Space E n s} {W' : Space E n' s'}
    {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
    [IsBaseAdapted A] [IsBaseAdapted X] (σ : b ⊕ r ≃ n) {σ' : b ⊕ r' ≃ n'} (hn_even : 2 ∣ card n)
    (hk_le : ∀ w : InfinitePlace E, k ≤ μ w) (h_card : card n' = 2 * (k + negCount s'))
    (h_zero : ThetaLargeVanishesOnDetVectors 𝔠 k W' V' σ') :
    ThetaLargeVanishesOnDetVectors 𝔠 k W V σ := by
  intro c F y hy g
  have hμ (w : InfinitePlace E) : μ w = k + ((μ w - k).toNat : ℕ) := by
    have h_le := hk_le w
    omega
  -- The sign of `rk V - rk W / 2` decides on which side of the summation formula on the line the
  -- cone is formed.
  obtain ⟨β, z, hz⟩ : ∃ (β : Bool) (z : ℕ),
      ((card r - card n / 2 : ℤ) + 1 : ℝ) = cond β (z + 1 : ℝ) (1 - (z + 1)) := by
    obtain ⟨z, hz | hz⟩ : ∃ z : ℕ,
        (card r - card n / 2 : ℤ) = z ∨ (card r - card n / 2 : ℤ) = -(z + 1) := by
      cases (card r - card n / 2 : ℤ) <;> simp [Int.negSucc_eq]
    · exact ⟨true, z, by simp [hz]⟩
    · exact ⟨false, z, by simp [hz]⟩
  -- The constant term of the theta integral of `(W', V')` is `γ ≠ 0` times the theta integral of
  -- `(W, V)` at the cone integral, and `c • detVector s t k m F` is such a cone integral.
  obtain ⟨C, hC_pos, h_plane⟩ := exists_planeConstantTerm_eq_thetaLarge A X σ' σ hn_even μ β hz
  obtain ⟨γ, hγ, h_term⟩ := h_plane 𝔠
  obtain ⟨c', h_cone⟩ := exists_integral_coneIntegrand_detVector A X β (z := (z : ℝ) + 1)
    (by positivity) h_card (fun w ↦ (μ w - k).toNat) hμ F c
  have h_const := h_term _ (isSchwartzVector_smul_detVector c' k (fun w ↦ (μ w - k).toNat)
    (liftFrame A X F)) y hy 1 g (.inl rfl)
  rw [h_cone] at h_const
  -- The constant term is that of a function that vanishes.
  have h_int := hy.mul (adaptedFrame 𝔠.readsAt A).blockRelations.isIntMatrix_dualI
  have h_left : planeConstantTerm 𝔠 V' A σ'
      (c' • detVector s' t' k (fun w ↦ (μ w - k).toNat) (liftFrame A X F)) y 1 g = 0 := by
    simp only [planeConstantTerm, h_zero c' (liftFrame A X F) _ h_int, integral_zero]
  have hγ_ne : γ ≠ 0 :=
    norm_pos_iff.1 ((mul_pos hC_pos (lSharp_pos 𝔠 (by simp))).trans_eq hγ.symm)
  exact (mul_eq_zero.1 (h_const.symm.trans h_left)).resolve_left hγ_ne

/-- Descent along any positive number `j` of hyperbolic planes `H`. Let the hermitian space `W'`
have the rank and number of negative signs of `W ⊕ H ^ j`, and let `V'` have the number of negative
signs of `V ⊕ H ^ j`; its rank is then that of `V ⊕ H ^ j` too, by `σ` and `σ'`. Let `W` have rank
`2 (k + q)`, where `q` is its number of negative signs, `k ≤ μ w` at every infinite place `w` and
`μ` is the weight of the split tame character `𝔠`.

If at every point of the unitary group of `W'` the theta integral of `(W', V')` vanishes on all
multiples of determinant vectors and all data `stdRowDatum σ' 𝔠.semilocalChar y'`, then at every
point of the unitary group of `W` that of `(W, V)` vanishes on all multiples of determinant vectors
and all data `stdRowDatum σ 𝔠.semilocalChar y`. Integrality at the ramified places of `𝔠` is the
only condition on the matrices `y'` and `y`; their rows are indexed by `b`, and `σ`, `σ'` order
these rows and those indexed by the basis of `V`, respectively `V'`, into a square matrix. -/
theorem ThetaLargeVanishesOnDetVectors.of_add_planes {k : ℕ} {W' : Space E n' s'}
    {V' : Space E r' t'} {σ' : b ⊕ r' ≃ n'} (h_zero : ThetaLargeVanishesOnDetVectors 𝔠 k W' V' σ')
    (hk_le : ∀ w : InfinitePlace E, k ≤ μ w) {j : ℕ} (hj : 1 ≤ j) (W : Space E n s)
    (V : Space E r t) (σ : b ⊕ r ≃ n) (h_card : card n = 2 * (k + negCount s))
    (h_rank : card n' = card n + 2 * j) (h_negCount_W : negCount s' = j + negCount s)
    (h_negCount_V : negCount t' = j + negCount t) : ThetaLargeVanishesOnDetVectors 𝔠 k W V σ := by
  induction j, hj using Nat.le_induction generalizing n r with
  | base =>
    have h_card_W : card b + card r = card n := card_sum.symm.trans (card_congr σ)
    have h_card_W' : card b + card r' = card n' := card_sum.symm.trans (card_congr σ')
    obtain ⟨W₁, A, _⟩ := exists_isBaseAdapted Unit W s' (by simp [h_rank]) (by simp [h_negCount_W])
    have h_rank_V : card r' = card r + 2 := by omega
    obtain ⟨V₁, X, _⟩ :=
      exists_isBaseAdapted Unit V t' (by simp [h_rank_V]) (by simp [h_negCount_V])
    exact (h_zero.congr_spaces W₁ V₁).of_add_plane A X σ ⟨_, h_card⟩ hk_le (by omega)
  | succ j _ ih =>
    -- Descend to `(H ⊕ W, H ⊕ V)`, then remove the last plane.
    have h_card_σ : card (b ⊕ r) = card n := card_congr σ
    let τ : b ⊕ (Unit ⊕ Unit) ⊕ r ≃ (Unit ⊕ Unit) ⊕ n :=
      equivOfCardEq (by simp +arith [← h_card_σ])
    -- One plane raises each rank by two and each number of negative signs by one.
    have h_card_above : card ((Unit ⊕ Unit) ⊕ n) =
        2 * (k + negCount (Sum.elim (hyperbolicSigns Unit) s)) := by simp +arith [h_card, two_mul]
    have h_above := ih (hyperbolicSum Unit W) (hyperbolicSum Unit V) τ h_card_above
      (by simp +arith [h_rank, two_mul]) (by simp +arith [h_negCount_W])
      (by simp +arith [h_negCount_V])
    exact h_above.of_add_plane (removePlanes Unit W) (removePlanes Unit V) σ ⟨_, h_card⟩ hk_le
      h_card_above

end New.Exchange
end
end
end

/-!
# Exchange of theta integrals for matched functions and for data modulo an ideal

The exchange identity compares the theta integrals to U(W) from two spaces of complementary ranks.
For matched functions at the ramified places of a tame character, it holds with a constant whose
absolute value is expressed, up to a factor free of the character, through L-values and the ratio
`New.Exchange.equalRankThetaRatio`. This ratio is the squared absolute value of the theta integral
in equal rank, divided by the product of L-values `L_*` at half the rank of the space. For a
suitable Schwartz vector it is a nonzero constant that does not depend on the character. Together
these give the exchange theorem for finite data given by functions on matrices over `O_E / 𝔪`.

## Main definitions and results

* `New.Exchange.exchange_of_matches`: the exchange identity, with the constant measured by
  `New.Exchange.lValueProdInt` and `New.Exchange.equalRankThetaRatio`.
* `New.Exchange.exists_equalRankThetaRatio_eq_const`: the value of that ratio on `H ⊕ W`, for `W` of
  rank `2 k + 2 q` with `q` negative signs and `k ≤ μ`.
* `New.Exchange.exchange_theorem`, `New.Exchange.exchange_identity`: the exchange theorem, for one
  choice and for all choices of splitting characters.

Notions from other files:
* `New.PairFock E s t` is the Fock space of real data for a pair of spaces with signs `s`, `t`. A
  vector is a Schwartz vector (`New.Exchange.IsSchwartzVector`) if all its moments `fockMoment N v`
  are finite.
* `New.Exchange.thetaIntegral S T a b f` is the function g ↦ ∫ θ^{S,T}_{a,b}(f)(g,h) dh on U(S), the
  integral of the theta kernel `New.pairTheta` over [U(T)]. `New.Exchange.thetaLarge` and
  `New.Exchange.thetaSmall` are its cases for a datum v ⊗ Φ: Φ is read at the ramified places of a
  tame character, or Φ of the transpose is read at their conjugates.
* `New.Exchange.SplitTameChar.semilocalChar` is the character t ↦ ν(t/t̄) of ∏_{w∈S} E_w, t read as
  an idele supported on S, extended by 0 to non-invertible elements.
* `New.Exchange.lValueProd` is the number `L_*(e)` = (∏_{w ∈ S} Nw)^(e²) · ∏_{z=1}^{e}
  |L^S(z, ν)|²; `New.Exchange.lValueProdInt` extends it to integers by `L_*(-e) = L_*(e)⁻¹`.
* `υ` is the splitting character of the Weil data, `upsilonU1` its restriction to the norm-one
  ideles, and `rankTwist a n` is the character `a υ ^ ⌊|n| / 2⌋` of [U(1)].
* `AreMatched O σ χ Φ Ψ` says that `Φ` and `Ψ` are supported on the last rows of `k⁻¹` and the first
  columns of `k`, for `k` invertible over `O` and split by `σ`, and differ there by `χ (det k)`.
* `stdRowDatum σ χ z` and `stdColDatum χ z` are the standard functions of an integral matrix `z`:
  they send `x` to `χ⁻¹` of the determinant of `z` stacked on `x`, respectively of `z * x`, and to
  zero where this is not defined over the integers.
* `localDatum S T v Φ r` is the vector with real part `v`, the function `Φ` at the places that `r`
  reads, and the vacuum elsewhere; `modDatum S T 𝔪 Φ v` is the same for a function `Φ` modulo `𝔪`.

## Relation to the literature

Let V and V' be hermitian spaces of type `New.Space` over a CM field with `New.WeilData` whose ranks
and negative signs add up to those of W, which has q negative signs, with 2q + 2 ≤ rk W and rk
V − rk V' = 2e ≥ 0, and let the weights μ satisfy rk W ≤ 2μ + 2q. Then theta integrals over U(V) and
U(V') agree on matched ramified data up to a nonzero constant c, so theta lifts can be exchanged.
Only |c|² is given, up to an uncomputed factor: it is sized by the conductor and the Hecke L-values
at 1,…,e. Equal theta lifts of characters of complementary groups are known for trivial characters
(Siegel–Weil) and for O(3), O(1) to Mp(2). Related work: Snitz, Theta correspondence of automorphic
characters, J. Number Theory 122 (2007), arXiv math/0509486; Erez, Matchings of theta lifts
associated to non-trivial automorphic characters of odd orthogonal groups, arXiv 2401.13469, 2024;
Gan–Qiu–Takeda, The regularized Siegel–Weil formula (second term identity) and the Rallis inner
product formula, 2014.
-/

@[expose] public section

noncomputable section

namespace New.Exchange

/-!
## The exchange identity for matched functions

`New.Exchange.exchange_of_matches` compares the theta integrals to U(W) from two spaces V and U of
complementary ranks. The identity at the top of the tower descends by removing planes
(`exists_rowColExchangeIdentity_of_even_rank`), passes from standard data to all matched functions
(`thetaLarge_eq_smul_of_areMatched`), and is translated from `(W, U⁻)` back to `(U, W)`
(`exists_mul_thetaSmall_adjointDatum_eq_mul_integral`).
-/

section ExchangeCore

open Matrix MeasureTheory NumberField Fintype Fock CoordChange Weil Seesaw

variable {E : Type} [Field E] [CMType E] [WeilData E] {n r b : Type} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {t : r → ℤˣ} {u : b → ℤˣ}

variable (E s u) in
/-- Passing to adjoint maps: the change of coordinates that carries data for the pair `(U, W)` to
data for `(W, U⁻)`. Here `W` has signs `s`, `U` has signs `u` and the opposite space `U⁻` has
signs `-u`. -/
abbrev adjointCoords : CoordChange E (.id ℂ) (homSigns u s) (homSigns s (-u)) :=
  flipCoords (E := E) (s := s) star_normNegOne_mul_self (t := u) rfl

/-- On finite adelic matrices `adjointCoords` is the conjugate transpose, scaled by the integral
unit `normNegOne` of norm `-1`. -/
lemma adjointCoords_finEquiv_apply (x : b × n → 𝔸f E) (i : n × b) :
    (adjointCoords E s u).finEquiv x i = (normNegOne (E := E) : Ô E) * star (x i.swap) :=
  rfl

/-- The real vector `y^ad` for `(W, U⁻)` that belongs to a real vector `y` for `(U, W)`: the image
of `y` under the real part of `adjointCoords`. -/
def adjointDatum (y : PairFock E u s) : PairFock E s (-u) := (adjointCoords E s u).realMap y

/-- Let `U`, `W` have signs `u`, `s` and let `y` be a vector of the real Fock space of `(U, W)` all
of whose moments are finite. Then so are all moments of `adjointDatum y`, the vector for `(W, U⁻)`
obtained by passing to adjoint maps; the opposite space `U⁻` has signs `-u`. -/
lemma IsSchwartzVector.adjointDatum {y : PairFock E u s} (hy : IsSchwartzVector y) :
    IsSchwartzVector (adjointDatum y) := by
  -- The real part `f.realEquiv` of the change of coordinates preserves the norm and the measure.
  let f : CoordChange E (.id ℂ) (homSigns u s) (homSigns s (-u)) := adjointCoords E s u
  have h_norm (x : InfinitePlace E × b × n → ℂ) : ‖f.realEquiv x‖₊ = ‖x‖₊ := by
    have h_coord (i : InfinitePlace E × n × b) : ‖f.realEquiv x i‖₊ = ‖x (i.1, i.2.swap)‖₊ := by
      simp [f, flipCoords, starCoordEquiv, nnNorm, Prod.map, abs_unit_intCast]
    refine eq_of_forall_ge_iff fun c ↦ ?_
    simp only [pi_nnNorm_le_iff, h_coord, Prod.forall, Prod.swap_prod_mk]
    exact forall_congr' fun _ ↦ forall_comm
  have h_measure : MeasurePreserving f.realEquiv (normalizedVolume _) (normalizedVolume _) :=
    Heisenberg.IsVacuum.measurePreserving_equiv (realHeisenberg 1) (realHeisenberg 1)
      f.vac_realEquiv
  intro N
  calc fockMoment N (Exchange.adjointDatum y)
      = ∫⁻ x, (1 + ‖f.realEquiv x‖ₑ) ^ N * ‖y (f.realEquiv x)‖ₑ ∂normalizedVolume _ := by
        simp only [eNorm_eq_nnNorm, h_norm]
        rfl
    _ = fockMoment N y := h_measure.lintegral_comp_emb f.realEquiv.measurableEmbedding
        fun x ↦ (1 + ‖x‖ₑ) ^ N * ‖y x‖ₑ
    _ ≠ ⊤ := hy N

/-- `New.G.neg` carries the rational points of `U` onto those of the opposite space
`U⁻ = flipSpace U`. -/
lemma neg_mem_flipSpace_Gamma_iff (U : Space E b u) (g : G E u) :
    G.neg g ∈ (flipSpace U).Γ ↔ g ∈ U.Γ := by
  simp [flipSpace, Space.mem_Gamma_iff_range, ← map_inv, ← smul_one_eq_diagonal, ← mul_assoc,
    ← star_mul]

omit [DecidableEq r] in
/-- Multiplying the argument by a unit `ε` of `O` divides the second of two matched functions by
`χ ε ^ card b`, the value of `χ` at the determinant of the scalar matrix `ε` of size `b`. -/
lemma _root_.New.AreMatched.right_eq_pow_mul_apply_smul {R : Type} [CommRing R] {O : Subring R}
    {σ : b ⊕ r ≃ n} {χ : MulChar R ℂ} {Φ : Matrix r n R → ℂ} {Ψ : Matrix n b R → ℂ}
    (h : AreMatched O σ χ Φ Ψ) (ε : Oˣ) (X : Matrix n b R) :
    Ψ X = χ ε ^ card b * Ψ ((ε.val : R) • X) := by
  have h_smul : (ε.val : R) • X = X * scalar b (ε.val : R) := by simp [← ext_iff, mul_comm]
  rw [h_smul, mul_comm]
  simpa [eq_comm] using h.right_mul _ ⟨.scalar b ε, rfl⟩ X

omit [DecidableEq r] in
/-- Let `σ` split `n` into `b` and `r`, let `𝔠` be a tame character: a character `ν = 𝔠.character`
of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set `S = 𝔠.ramifiedPlaces` of split
places, and let `y` lie in the real Fock space of `(U, W)`. There is a number `a` of modulus one
with the following property. Let `Ψ` be a Schwartz–Bruhat function on left invertible matrices that
is matched with some `Φ`: `Φ` is supported on the last rows of `k⁻¹` and `Ψ` on the first columns of
`k` (split by `σ`), for `k` in `GL_n` of the local integers at `S`, and there
`Φ = 𝔠.semilocalChar (det k) * Ψ`. Let `U⁻ = flipSpace U` be the opposite space, `adjointCoords` the
passage to adjoint maps from `(U, W)` to `(W, U⁻)`, and `y^ad = adjointDatum y` the image of `y`.
Then the datum with real part `y^ad`, the function `x ↦ Ψ xᵀ` at the conjugates of `S`
(`𝔠.readsAt.star`) and the vacuum elsewhere is `a` times the image of the datum with real part `y`,
the function `Ψ` at `S` (`𝔠.readsAt`) and the vacuum elsewhere. -/
lemma exists_localDatum_adjointDatum_eq_smul (W : Space E n s) (U : Space E b u) (σ : b ⊕ r ≃ n)
    {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) (y : PairFock E u s) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
      Ψ ∈ schwartzBruhat {y | HasLeftInv y} → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ →
        localDatum W (flipSpace U) (adjointDatum y)
            (fun x : Matrix b n (LocProd 𝔠.ramifiedPlaces) ↦ Ψ xᵀ) 𝔠.readsAt.star =
          a • (adjointCoords E s u).map (localDatum U W y Ψ 𝔠.readsAt) := by
  let f : CoordChange E (.id ℂ) (homSigns u s) (homSigns s (-u)) := adjointCoords E s u
  -- `ε` is the component at `𝔠.ramifiedPlaces` of the integral unit `normNegOne` of norm `-1`.
  let ε : (SemilocalField.O : Subring (LocProd 𝔠.ramifiedPlaces))ˣ :=
    normNegOne.map ((evalPlaces 𝔠.ramifiedPlaces).restrict _ _ evalPlaces_mem_O).toMonoidHom
  refine ⟨𝔠.semilocalChar ε ^ card b,
    by simp [TameLocalChar.norm_eq_one, IsIntegralUnit, isIntegralUnit_iff_isUnit.2],
    fun Φ Ψ hΨ hΦΨ ↦ ?_⟩
  -- The flip transposes the matrix and scales it by `ε`, dividing `Ψ` by
  -- `𝔠.semilocalChar ε ^ card b`.
  have h_scale (x : b × n → 𝔸f E) :
      Ψ ((vecToMatrix x).map ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))))ᵀ =
        𝔠.semilocalChar ε ^ card b * Ψ ((vecToMatrix (f.finEquiv x)).map
          (evalPlaces 𝔠.ramifiedPlaces)) := by
    have h_matrix : (vecToMatrix (f.finEquiv x)).map (evalPlaces 𝔠.ramifiedPlaces) =
      (ε.val : LocProd 𝔠.ramifiedPlaces) •
        ((vecToMatrix x).map ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))))ᵀ := by
      simp [f, adjointCoords_finEquiv_apply, vecToMatrix, starRingEnd_apply, ← ext_iff, ε]
    rw [h_matrix]
    exact hΦΨ.right_eq_pow_mul_apply_smul ε _
  rw [map_integrated, flipCoords_map_schrodingerOp _ _ U W (flipSpace U) 𝔠.readsAt.disjoint_star _
    (hΨ := 𝔠.readsAt.isSchwartzBruhat hΨ), ← map_smul, Space.smul_schrodingerOp]
  -- Both sides have real part `y^ad`; the functions that name their finite parts agree.
  change (W.hom (flipSpace U)).integrated (adjointDatum y) ((W.hom (flipSpace U)).schrodingerOp
      (star ⁻¹' (𝔠.ramifiedPlaces : Set (FinPlace E)))
      (fun x ↦ Ψ ((vecToMatrix x).map ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))))ᵀ)
        _) =
    (W.hom (flipSpace U)).integrated (adjointDatum y) ((W.hom (flipSpace U)).schrodingerOp _
      (fun x ↦ 𝔠.semilocalChar ε ^ card b * Ψ
        ((vecToMatrix (f.finEquiv x)).map (evalPlaces 𝔠.ramifiedPlaces))) _)
  simp only [h_scale]

omit [DecidableEq r] in
/-- Let `W` have even rank, split by `σ` into `b` and `r`, let `𝔠` be a tame character: a character
`ν = 𝔠.character` of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set
`S = 𝔠.ramifiedPlaces` of split places, and put `γ = rankTwist ν⁻¹ n = ν⁻¹ υ ^ (rk W / 2)`. There is
a number `d` of modulus one with the following property. Let `Ψ` be a Schwartz–Bruhat function on
left invertible matrices that is matched with some `Φ`: `Φ` is supported on the last rows of `k⁻¹`
and `Ψ` on the first columns of `k` (split by `σ`), for `k` in `GL_n` of the local integers at `S`,
and there `Φ = 𝔠.semilocalChar (det k) * Ψ`. Let `U⁻ = flipSpace U` be the opposite space and
`y^ad = adjointDatum y` the image of `y` under passage to adjoint maps. Then for `g` in the adelic
group `U(W) = G E s`, `γ (det g)` times `thetaSmall`, the theta integral of `(W, U⁻)` over `[U(U⁻)]`
with characters `ν υ ^ (rk W / 2)`, `υ ^ rk U`, real part `y^ad` and `x ↦ Ψ xᵀ` at the conjugates of
`S`, is `d` times the integral over the quotient `[U(U)]` of the theta kernel `pairTheta` of
`(U, W)` with characters `γ`, `γ`, real part `y` and `Ψ` at `S`. -/
lemma exists_mul_thetaSmall_adjointDatum_eq_mul_integral (W : Space E n s) (U : Space E b u)
    (σ : b ⊕ r ≃ n)
    (h_even : 2 ∣ card n) {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) (y : PairFock E u s) :
    ∃ d : ℂ, ‖d‖ = 1 ∧ ∀ (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
      Ψ ∈ schwartzBruhat {y | HasLeftInv y} → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ →
        ∀ g : G E s,
        (rankTwist 𝔠.character⁻¹ n).val g.det * thetaSmall W (flipSpace U) 𝔠 (adjointDatum y) Ψ g =
          d * ∫ h : G E u, pairTheta U W (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
            (localDatum U W y Ψ 𝔠.readsAt) (h, g) ∂U.quotMeasure := by
  -- The flip changes the theta kernel by a constant `d` and the datum by a constant `a`.
  obtain ⟨d, hd, h_flip⟩ :=
    exists_pairTheta_flip star_normNegOne_mul_self rfl U W (flipSpace U) 1
      (by simp [flipSpace, G.adeleMatrix_one, ← ext_iff]) (rankTwist 𝔠.character⁻¹ n)
  obtain ⟨a, ha, h_datum⟩ := exists_localDatum_adjointDatum_eq_smul W U σ 𝔠 y
  refine ⟨a * d, by rw [norm_mul, ha, hd, mul_one], fun Φ Ψ hΨ hΦΨ g ↦ ?_⟩
  obtain ⟨k, hk⟩ := h_even
  -- `G.neg` carries the integral over `[U(U⁻)]` to the one over `[U(U)]`; compare the characters.
  have h_neg (F : G E (-u) → ℂ) :
      ∫ h : G E (-u), F h ∂(flipSpace U).quotMeasure =
        ∫ h : G E u, F (G.neg h) ∂U.quotMeasure :=
    (isForm_neg_iff_and_integral_neg U (flipSpace U) (neg_mem_flipSpace_Gamma_iff U)).2 F
  rw [thetaSmall, thetaIntegral, h_datum Φ Ψ hΨ hΦΨ, h_neg, ← integral_const_mul,
    ← integral_const_mul]
  congr with h
  -- As `card n = 2 * k`, the characters of the two kernels differ by `γ (det g)`.
  rw [mul_assoc, ← h_flip _ _ h g h.neg (by simp [G.adeleMatrix_neg, G.adeleMatrix_one])]
  simp [pairTheta, pairWeil, pairChar_apply, circleChar_inv_apply, G.det_neg, rankTwist, hk,
    pow_mul', field]

/-- Let `W` have even rank `rk U + rk V` (`σ`, `h_even`), let `𝔠` be a tame character: a character
`ν = 𝔠.character` of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set
`S = 𝔠.ramifiedPlaces` of split places, put `χ = 𝔠.semilocalChar`, and let `v`, `y` be real Schwartz
vectors. The standard functions `stdRowDatum σ χ z`, `stdColDatum χ z` send `x` to `χ⁻¹` of the
determinant of `z` stacked on `x`, resp. of `z * x`. Suppose that `thetaLarge` is `c` times
`thetaSmall` on them for all `z` with integral entries. Then the same holds for all matched `Φ`, `Ψ`
with `Ψ` locally constant, and `Ψ` has compact support in the left invertible matrices. -/
lemma thetaLarge_eq_smul_of_areMatched (W : Space E n s) (V : Space E r t) (U : Space E b u)
    (σ : b ⊕ r ≃ n) (h_even : 2 ∣ card n) {μ : InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}
    {v : PairFock E s t} {y : PairFock E s u} (hv : IsSchwartzVector v) (hy : IsSchwartzVector y)
    {c : ℂ}
    (h_std : ∀ z : Matrix b n (LocProd 𝔠.ramifiedPlaces), IsIntMatrix SemilocalField.O z →
      thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar z) = c • thetaSmall W U 𝔠 y
        (stdColDatum 𝔠.semilocalChar z))
    {Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ} {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ) :
    Ψ ∈ schwartzBruhat {y | HasLeftInv y} ∧ thetaLarge W V 𝔠 v Φ = c • thetaSmall W U 𝔠 y Ψ := by
  -- The difference `𝒟 Ψ` of the two sides is equivariant, so its kernel is a stable space; it
  -- contains a standard datum, which generates.
  obtain ⟨M, 𝒟, h𝒟, h_diff⟩ : ∃ (M : Submodule ℂ (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ))
      (𝒟 : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ),
      IsEquivariantLift 𝔠 W M 𝒟 ∧
      ∀ {Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ}
        {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ},
        IsLocallyConstant Ψ → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ →
        Ψ ∈ M ∧ 𝒟 Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W U 𝔠 y Ψ :=
    exists_isEquivariantLift_eq_thetaLarge_sub_smul W V U 𝔠 σ h_even hv hy c
  obtain ⟨h_primitive, z, hz, h_inv⟩ :=
    isPrimitiveMatrix_firstCols σ (one_mem _ : (1 : GL n (LocProd 𝔠.ramifiedPlaces)) ∈ _)
  obtain ⟨h_mem, h_value⟩ :=
    h_diff (stdColDatum_mem_schwartzBruhat _ hz).1 (areMatched_stdRowDatum_stdColDatum σ hz)
  have h_std_ker : stdColDatum 𝔠.semilocalChar z ∈ M ⊓ 𝒟.ker :=
    ⟨h_mem, by simp [h_value, h_std z hz]⟩
  -- The standard datum is taken with multiplicity `1`.
  obtain ⟨hΨ_mem, hΨ_ker : 𝒟 Ψ = 0⟩ :=
    match_mem_of_stdColDatum h𝒟.comp_mul_mem_ker (inf_le_left.trans h𝒟.le_schwartzBruhat) hΨ hΦΨ
      h_std_ker h_primitive hz h_inv 1 (by simp) one_ne_zero
  obtain ⟨-, hΨ_value⟩ := h_diff hΨ hΦΨ
  exact ⟨h𝒟.le_schwartzBruhat hΨ_mem, sub_eq_zero.1 (hΨ_value.symm.trans hΨ_ker)⟩

/-- Let `W₀ = H ⊕ X` with `H` a hyperbolic plane, and let `A` be an adapted splitting of `W₀` over
`W` with `card p ≥ 1` hyperbolic planes (`h_planes` counts the negative signs); for `X = W` it is
`removePlanes Unit W`. Let `W` have even rank `rk U + rk V` (`σ`, `h_even`) and as many negative
signs (`negCount`) as `V ⊕ U⁻`, with `U⁻` the opposite space (`h_signs`). For real Schwartz vectors
`z` for `(W₀, W₀)` and `y` for `(W, U)` there is a vector `v`
for `(W, V)` with `RowColExchangeIdentity W V U μ σ v y`: `v` and `y` are Schwartz, and there is a
real `C` such that each tame character `𝔠` of weight `μ` has a number `c` with (a) and (b). (a)
`C |c| ^ 2` is `L_*(rk V - rk W / 2)` times the equal rank ratio `|I(z)(1)| ^ 2 / L_*(rk W₀ / 2)`,
where `I(z)` is the theta integral of `(W₀, W₀)` at `z` and `χ⁻¹(det)`, `χ = 𝔠.semilocalChar`. (b)
On the standard functions `stdRowDatum σ χ`, `stdColDatum χ` of each integral matrix (`χ⁻¹` of the
determinant that it completes), `thetaLarge` over `[U(V)]` at `v` is `c` times `thetaSmall` over
`[U(U)]` at `y`. -/
lemma exists_rowColExchangeIdentity_of_even_rank (W : Space E n s) (U : Space E b u)
    (μ : InfinitePlace E → ℤ) (V : Space E r t) (σ : b ⊕ r ≃ n) {n₁ p : Type} [Fintype n₁]
    [DecidableEq n₁] [Fintype p] [DecidableEq p] [Nonempty p] {s₁ : n₁ → ℤˣ} (X : Space E n₁ s₁)
    (A : (hyperbolicSum Unit X).Splitting W p) [IsBaseAdapted A]
    {z : PairFock E (hyperbolicSigns Unit ⊕ᵥ s₁) (hyperbolicSigns Unit ⊕ᵥ s₁)} {y : PairFock E s u}
    (hz : IsSchwartzVector z) (hy : IsSchwartzVector y)
    (h_signs : negCount u + negCount s = card b + negCount t) (h_even : 2 ∣ card n)
    (h_planes : 1 + negCount s₁ = card p + negCount s) :
    ∃ v : PairFock E s t, RowColExchangeIdentity W V U μ σ v y
      fun 𝔠 : SplitTameChar E μ ↦ equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 z := by
  -- The tower is `W`, `W₀`, `W₀ ⊕ H ^ rk U`. Take `w` on `W₀` with zero term `y`, and on top the
  -- vectors `x`, `x'` of the large triple, where `x'` has zero term `w`.
  obtain ⟨w, hw, hw_zero⟩ := exists_isSchwartzVector_realSlice_zero_eq A U hy
  have h_even₀ : 2 ∣ card ((Unit ⊕ Unit) ⊕ n₁) := by
    rw [A.card_eq]
    exact h_even.add (dvd_mul_right 2 _)
  let W₀ : Space E ((Unit ⊕ Unit) ⊕ n₁) (hyperbolicSigns Unit ⊕ᵥ s₁) := hyperbolicSum Unit X
  let σ' := (Equiv.sumAssoc b b ((Unit ⊕ Unit) ⊕ n₁)).symm
  obtain ⟨x, x', hx'_zero, h_top⟩ :=
    exists_rowColExchangeIdentity_sum (removePlanes b W₀) (removePlanes Unit X) U σ' h_even₀ μ hw hz
  -- Remove the `rk U + card p` planes; zero terms are taken in stages.
  have h_signs₀ : negCount (u ⊕ᵥ (hyperbolicSigns Unit ⊕ᵥ s₁)) = card (b ⊕ p) + negCount t := by
    have h_count :
        negCount (u ⊕ᵥ (hyperbolicSigns Unit ⊕ᵥ s₁)) = negCount u + (1 + negCount s₁) := by
      simp +arith [negCount_sumElim, negCount_one_and_neg_one]
    rw [h_count, card_sum]
    omega
  have : Nonempty (b ⊕ p) := ⟨.inr (Classical.arbitrary p)⟩
  have h_zero_term : realSlice ((removePlanes b W₀).symm.comp A) U 0 x' = y := by
    rw [realSlice_zero_comp U W (removePlanes b W₀).symm A x', hx'_zero, hw_zero]
  rw [← h_zero_term]
  exact exists_rowColExchangeIdentity_removing_planes U (U.sum W₀) ((removePlanes b W₀).symm.comp A)
    V σ h_signs₀ h_even h_top

/-- Let `W₀ = H ⊕ X` with `H` a hyperbolic plane, and let `A` be an adapted splitting of `W₀` over
`W` with `card p ≥ 1` hyperbolic planes (`h_planes` counts the negative signs); for `X = W` it is
`removePlanes Unit W`. Let `W` have even rank `rk U + rk V` (`σ`, `h_even`) and as many negative
signs as `U` and `V` together (`h_signs`). Let `z` for `(W₀, W₀)` and
`y` for `(U, W)` be real Schwartz vectors. There are `C` and a Schwartz vector `v` for `(W, V)` such
that each tame character `𝔠` of weight `μ` has a number `c` with (a) and (b). Put `ν = 𝔠.character`,
`S = 𝔠.ramifiedPlaces`, `χ = 𝔠.semilocalChar` and `γ = ν⁻¹ υ ^ (rk W / 2)`, where `υ` is the
splitting character of the Weil data on norm-one ideles (`upsilonU1`). (a) `C |c| ^ 2` is
`L_*(rk V - rk W / 2)` times the equal rank ratio `|I(z)(1)| ^ 2 / L_*(rk W₀ / 2)`, where `I(z)` is
the theta integral of `(W₀, W₀)` at `z` and `χ⁻¹(det)`, `L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2)
∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2` and `L_*(-e) = L_*(e)⁻¹` (`lValueProdInt`). (b) For all matched
functions `Φ`, `Ψ` with `Ψ` locally constant, the integral over `[U(V)]` of the theta kernel of
`(W, V)` with characters `γ`, `1` at `(v, Φ)` is `c` times the integral over `[U(U)]` of the theta
kernel of `(U, W)` with characters `γ`, `γ` at `(y, Ψ)`, as functions on `U(W) = G E s`. -/
lemma exchange_of_matches (W : Space E n s) (U : Space E b u) (μ : InfinitePlace E → ℤ)
    (V : Space E r t) (σ : b ⊕ r ≃ n) {n₁ p : Type} [Fintype n₁] [DecidableEq n₁] [Fintype p]
    [DecidableEq p] [Nonempty p] {s₁ : n₁ → ℤˣ} (X : Space E n₁ s₁)
    (A : (hyperbolicSum Unit X).Splitting W p) [IsBaseAdapted A]
    {z : PairFock E (hyperbolicSigns Unit ⊕ᵥ s₁) (hyperbolicSigns Unit ⊕ᵥ s₁)} {y : PairFock E u s}
    (hz : IsSchwartzVector z) (hy : IsSchwartzVector y)
    (h_signs : negCount s = negCount t + negCount u) (h_even : 2 ∣ card n)
    (h_planes : 1 + negCount s₁ = card p + negCount s) :
    ∃ (C : ℝ) (v : PairFock E s t), IsSchwartzVector v ∧ ∀ 𝔠 : SplitTameChar E μ,
      let γ : AutChar E := rankTwist 𝔠.character⁻¹ n
      ∃ c : ℂ,
        -- (a) the modulus of the constant
        C * ‖c‖ ^ 2 =
          lValueProdInt 𝔠 (card r - card n / 2) * equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 z ∧
        -- (b) the identity of theta integrals, for all matched functions
        ∀ (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ)
          (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
          IsLocallyConstant Ψ → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ → ∀ g : G E s,
          thetaIntegral W V γ 1 (localDatum W V v Φ 𝔠.readsAt) g =
            c * ∫ h : G E u, pairTheta U W γ γ (localDatum U W y Ψ 𝔠.readsAt) (h, g)
              ∂U.quotMeasure := by
  -- Descend on standard data for `(W, V, U⁻)`, pass to all matched functions, and return to
  -- `(U, W)`.
  have h_signs_flip : negCount (-u) + negCount s = card b + negCount t := by
    linarith [negCount_neg_add u]
  obtain ⟨v, hv, -, C, h_std⟩ :=
    exists_rowColExchangeIdentity_of_even_rank W (flipSpace U) μ V σ X A hz hy.adjointDatum
      h_signs_flip h_even h_planes
  refine ⟨C, v, hv, fun 𝔠 ↦ ?_⟩
  obtain ⟨c, hc, h_std_data⟩ := h_std 𝔠
  obtain ⟨d, hd, h_form⟩ := exists_mul_thetaSmall_adjointDatum_eq_mul_integral W U σ h_even 𝔠 y
  refine ⟨c * d, by rw [norm_mul, hd, mul_one, hc], fun Φ Ψ hΨ hΦΨ g ↦ ?_⟩
  obtain ⟨hΨ_mem, h_eq⟩ := thetaLarge_eq_smul_of_areMatched W V (flipSpace U) σ h_even hv
    hy.adjointDatum h_std_data hΨ hΦΨ
  -- In `thetaLarge` the second character enters as its inverse at `det g`.
  calc thetaIntegral W V (rankTwist 𝔠.character⁻¹ n) 1 (localDatum W V v Φ 𝔠.readsAt) g
      = (rankTwist 𝔠.character⁻¹ n).val g.det * thetaLarge W V 𝔠 v Φ g := by
        rw [thetaLarge, thetaIntegral, thetaIntegral, ← integral_const_mul]
        congr with h
        simp [pairTheta, pairWeil, pairChar_apply, field]
    _ = c * ((rankTwist 𝔠.character⁻¹ n).val g.det *
          thetaSmall W (flipSpace U) 𝔠 (adjointDatum y) Ψ g) := by
        rw [h_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm]
    _ = c * d * ∫ h : G E u, pairTheta U W (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
          (localDatum U W y Ψ 𝔠.readsAt) (h, g) ∂U.quotMeasure := by
        rw [h_form Φ Ψ hΨ_mem hΦΨ g, mul_assoc]

end ExchangeCore

/-!
## The value of the equal rank theta integral

For `W₀ = H ⊕ W` of even rank and a Schwartz vector `v`, the theta integral of `(W₀, W₀)` on `v` and
the datum `χ⁻¹(det)` is a constant `I₀(v)`. Let `rk W = 2 k + 2 q`, where `q` is the number of
negative signs of `W`, and `k ≤ μ`. We find `v` with `|I₀(v)| ^ 2 = C L_*(rk W₀ / 2)`, where `C ≠ 0`
does not depend on the character (`exists_equalRankThetaRatio_eq_const`). The value is found for a
space `X` with the signs of `W` that splits adaptedly over a positive definite space
(`exists_equalRankThetaRatio_const_ne_zero`); the ratio depends only on the signs of `W₀`
(`equalRankThetaRatio_eq_of_signs_eq`).

Let `J` be positive definite of rank `2 k`, `k ≤ μ`, let `X` be `J` plus `q` hyperbolic planes and
`Y = H ⊕ X`, so that `Y` splits over `J` with `q + 1` planes. For a space `X'` write
`r_X'(v) = |I(v)(1)| ^ 2 / L_*(rk X' / 2)` (`equalRankThetaRatio`), where `I(v)` is the theta
integral of `(X', X')`. Put `L_*(-k) = L_*(k)⁻¹`.

1. Non-vanishing (`exists_equalRankThetaRatio_ne_zero`). Fix the character, and suppose `r_Y(v) = 0`
   for all `v`. The periods that compute the Fourier coefficients for `(H ^ (2 k) ⊕ Y, J⁻ ⊕ Y)` are
   then zero, so this theta integral vanishes on standard data at every Schwartz vector
   (`thetaLargeVanishes_of_equalRankThetaRatio_eq_zero`). Vanishing on determinant vectors
   descends along the `2 k + 1 + q` planes to `(J, 0)`
   (`ThetaLargeVanishesOnDetVectors.of_add_planes`). But there the determinant vector is the
   vacuum, and its integral is a volume, not zero.
2. The identity used twice (`exists_equalRankThetaRatio_sq_eq`). Fix `v` for `(Y, Y)`. The identity
   for `(J, J, 0)`, reached from `Y` by removing its `q + 1` planes, gives `y` such that `I(y)` is
   a constant `c₁` times a volume, with
   `B |c₁| ^ 2 = L_*(k) r_Y(v)`. The identity for `(J, 0, J)`, with `y` on the right, gives a number
   `ξ` and `c₂` with `C |c₂| ^ 2 = L_*(-k) r_Y(v)`. Integrating the theta kernel of `y` over both
   groups, in both orders, gives `ξ = c₁ c₂`. So `r_Y(v) ^ 2 = B C |ξ| ^ 2`, where `B`, `C`, `ξ` do
   not depend on the character.
3. The value (`exists_equalRankThetaRatio_const_ne_zero`). For the `v` that step 1 gives for one
   character, `r_Y(v) ≥ 0` is one nonzero number for all characters.
-/

section EqualRankValue

open MeasureTheory NumberField Fintype Space Equiv Fock MixedModel Heisenberg OrthogonalSum

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-- Let `𝔠` be a tame character, `χ = 𝔠.semilocalChar` and `γ = rankTwist 𝔠.character⁻¹
n = 𝔠.character⁻¹ υ ^ ⌊rk W / 2⌋`. Suppose that `thetaLarge`, the theta integral of `(W, W)` over
the second `[U(W)]` with characters `γ`, `γ`, vanishes at the finite datum `χ⁻¹(det)`
(`stdColDatum χ 1`) for all real Schwartz vectors, and let `w` be such a vector for `(W, V.sum W)`.
Form `thetaOnRealData`, the theta series as a functional of the real vector, with characters `γ` and
`γ β` for any character `β`, and finite datum `f ⊗ χ⁻¹(det)` (`boxProd` of `f` for `(W, V)` and
`namedVector`, the vacuum with this function put in at the ramified places, which `𝔠.readsAt`
reads), after the Heisenberg translation by the adelic matrix with rows `x` for `V` and `0` for `W`.
Then for `g` in `U(W)` and `y` in `U(V)` its value at `w` and `(g, (y, l))` has integral zero over
`l` in `[U(W)]`. -/
lemma integral_thetaOnRealData_eq_zero (W : Space E n s) {μ : InfinitePlace E → ℤ}
    {𝔠 : SplitTameChar E μ}
    (h_zero : ∀ v : PairFock E s s, IsSchwartzVector v → ∀ g : G E s,
      thetaLarge W W 𝔠 v (stdColDatum 𝔠.semilocalChar 1) g = 0)
    {r : Type} [Fintype r] [DecidableEq r] {t : r → ℤˣ} (V : Space E r t)
    {w : PairFock E s (Sum.elim t s)} (hw : IsSchwartzVector w) (β : AutChar E) (f : 𝒮 (W.hom V))
    (x : Matrix r n (𝔸 E)) (g : G E s) (y : G E t) :
    ∫ l : G E s, thetaOnRealData W (V.sum W) (rankTwist 𝔠.character⁻¹ n)
      (rankTwist 𝔠.character⁻¹ n * β)
      (boxProd (homSigns_sum_target signs_comp_refl) f
        (namedVector W W (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt))
      (Matrix.fromRows x 0) (g, G.sum (y, l)) w ∂W.quotMeasure = 0 := by
  -- Expand `w` into coherent states `realHeisenbergOp u vacVector`. The isomorphism `φ` splits `u`
  -- into its coordinates for `V` and for `W`, and the state is the product of the two coherent
  -- states. Evaluating the first factor leaves the datum `∫ w u • F u` for `(W, W)`.
  let α : AutChar E := rankTwist 𝔠.character⁻¹ n
  let f₀ : 𝒮 (W.hom W) := namedVector W W (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt
  let T : PairFock E s t →L[ℂ] ℂ := thetaOnRealData W V α β f x (g, y)
  let φ : (InfinitePlace E × (r ⊕ n) × n → ℂ) ≃ₜ+
      (InfinitePlace E × r × n → ℂ) × (InfinitePlace E × n × n → ℂ) :=
    (realCoordSum (realSigns_comp_split (E := E)
      (homSigns_sum_target (s' := s) (signs_comp_refl : Sum.elim t s ∘ _ = _)))).equiv.symm
  let F (u : InfinitePlace E × (r ⊕ n) × n → ℂ) : PairFock E s s :=
    T (realHeisenbergOp (φ u).1 Fock.vacVector) • realHeisenbergOp (φ u).2 Fock.vacVector
  let C : ℝ := ‖T‖ * ‖(Fock.vacVector : PairFock E s t)‖
  have h_moment (N : ℕ) (u : InfinitePlace E × (r ⊕ n) × n → ℂ) : fockMoment N (F u) ≤
      fockMoment N (Fock.vacVector : PairFock E s s) * ENNReal.ofReal C * (1 + ‖u‖ₑ) ^ N := by
    have h_norm : ‖(φ u).2‖ₑ ≤ ‖u‖ₑ := eNorm_le_iff_norm_le.2 (pi_norm_comp_le u _)
    have h_coeff : ‖T (realHeisenbergOp (φ u).1 Fock.vacVector)‖ₑ ≤ ENNReal.ofReal C := by
      grw [← ofReal_norm, T.le_opNorm, Heisenberg.Rep.norm_map]
    calc fockMoment N (F u)
        ≤ ENNReal.ofReal C * ((1 + ‖(φ u).2‖ₑ) ^ N *
            fockMoment N (Fock.vacVector : PairFock E s s)) := by
          grw [fockMoment_smul, fockMoment_realHeisenbergOp_le, h_coeff]
      _ ≤ _ := by grw [h_norm, mul_comm, mul_rotate]
  have h_finite (N : ℕ) : ∫⁻ u, fockMoment N (w u • F u) ∂normalizedVolume _ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top, isSchwartzVector_vacVector _, hw _])
      (lintegral_fockMoment_smul_le (h_moment N))
  obtain ⟨h_integrable, h_schwartz⟩ := isSchwartzVector_integral (by fun_prop) h_finite
  have h_coherent (u : InfinitePlace E × (r ⊕ n) × n → ℂ) :
      (realHeisenbergOp u Fock.vacVector : PairFock E s (Sum.elim t s)) =
        realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl))
          (realHeisenbergOp (φ u).1 Fock.vacVector) (realHeisenbergOp (φ u).2 Fock.vacVector) := by
    rw [realBoxProd, ← heisenbergOp_tmul, tmul_vacElem]
  -- The integral is `thetaLarge` of that datum: compare the integrands at `l`.
  rw [← h_zero _ h_schwartz g]
  refine integral_congr_ae (.of_forall fun l ↦ ?_)
  let S : PairFock E s (Sum.elim t s) →L[ℂ] ℂ := thetaOnRealData W (V.sum W) α (α * β)
    (boxProd (homSigns_sum_target signs_comp_refl) f f₀) (Matrix.fromRows x 0) (g, G.sum (y, l))
  let L : PairFock E s s →L[ℂ] ℂ :=
    θ (W.hom W) ∘L pairWeil W W α α (g, l) ∘L (integrated (W.hom W)).flip f₀
  have h_product (u : InfinitePlace E × (r ⊕ n) × n → ℂ) :
      S (realHeisenbergOp u Fock.vacVector) = L (F u) := by
    rw [h_coherent, map_smul]
    exact thetaOnRealData_boxProd_eq_mul V α β f f₀ x g y _ _ l
  calc S w = ∫ u, w u • S (realHeisenbergOp u Fock.vacVector) ∂normalizedVolume _ :=
        IsVacuum.map_eq_integral w S
    _ = ∫ u, L (w u • F u) ∂normalizedVolume _ := by simp only [h_product, map_smul]
    _ = L (∫ u, w u • F u ∂normalizedVolume _) := L.integral_comp_comm h_integrable

omit [WeilData E] in
/-- The real Weil representation `realPairWeil` of a pair of unitary groups with signs `s`, `t` and
weights `γ`, `γ'` preserves the Fock vectors all of whose moments are finite. -/
lemma isSchwartzVector_realPairWeil {r : Type} [Fintype r] [DecidableEq r] {t : r → ℤˣ}
    (γ γ' : InfinitePlace E → ℤ) (p : GInf E s × GInf E t) {v : PairFock E s t}
    (hv : IsSchwartzVector v) : IsSchwartzVector (realPairWeil γ γ' p v) := by
  intro N
  have h_weil : fockMoment N (realWeil (pairHomInf p) v) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top, isSchwartzVector_vacVector N, hv N])
      (fockMoment_realWeil_le N (pairHomInf p))
  simp [realPairWeil_apply_apply, fockMoment_smul, ENNReal.mul_eq_top, h_weil]

variable {m : Type} [Fintype m] [DecidableEq m]

/-- Let `J = stdSpace E m` be positive definite, let `X` have even rank and at most half of its
signs negative, `Y = H ⊕ X = hyperbolicSum Unit X` with `H` a hyperbolic plane, and `𝔠` a tame
character: a character `ν = 𝔠.character` of `[U(1)]` of weight `μ`, tamely ramified exactly at a
finite set `S = 𝔠.ramifiedPlaces` of split places. Suppose that the equal rank ratio of `Y`, the
normalised square of the theta integral of `(Y, Y)` at `1`, is zero at every Schwartz vector. Then
the theta integral of the pair `(H ^ rk J ⊕ Y, J⁻ ⊕ Y)` vanishes at every Schwartz vector and every
standard datum: `𝔠.semilocalChar⁻¹` of the determinant of an integral `m`-row matrix completed by
a variable
one, the rows being ordered by `sumAssoc`. -/
lemma thetaLargeVanishes_of_equalRankThetaRatio_eq_zero {μ : InfinitePlace E → ℤ}
    (X : Space E n s) (hn : 2 ∣ card n) (h_neg : 2 * negCount s ≤ card n) {𝔠 : SplitTameChar E μ}
    (h_zero : ∀ v : PairFock E (Sum.elim (hyperbolicSigns Unit) s)
      (Sum.elim (hyperbolicSigns Unit) s),
      IsSchwartzVector v → equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v = 0) :
    ThetaLargeVanishes 𝔠 (hyperbolicSum m (hyperbolicSum Unit X))
      ((stdSpace E m).neg.sum (hyperbolicSum Unit X))
      (sumAssoc m m ((Unit ⊕ Unit) ⊕ n)).symm := by
  -- The periods over `[U(Y)]` of a Schwartz `v` are values of the equal rank integral, so they are
  -- zero. This is the identity of periods with period `0`, whose factor `C` is then zero.
  let Y : Space E ((Unit ⊕ Unit) ⊕ n) (Sum.elim (hyperbolicSigns Unit) s) := hyperbolicSum Unit X
  have h_even : 2 ∣ card ((Unit ⊕ Unit) ⊕ n) := by simpa using hn.add (dvd_refl 2)
  have h_theta (v : PairFock E (Sum.elim (hyperbolicSigns Unit) s)
    (Sum.elim (hyperbolicSigns Unit) s))
      (hv : IsSchwartzVector v) (g : G E (Sum.elim (hyperbolicSigns Unit) s)) :
      thetaLarge Y Y 𝔠 v (stdColDatum 𝔠.semilocalChar 1) g = 0 := by
    rw [thetaLarge_eq_apply_one_of_even_rank (removePlanes Unit X) _ h_even hv]
    simpa [equalRankThetaRatio, (lValueProdInt_pos 𝔠 _).ne'] using h_zero v hv
  intro v hv z hz g
  have h_period : IsPeriodIdentity (hyperbolicSum m Y) (removePlanes m Y) (stdSpace E m).neg 𝔠
      v vacVector 1 0 := by
    refine fun h ↦ ⟨1, fun B β f x g y ↦ ?_⟩
    rw [mul_zero, zero_div, zero_mul]
    let _ : DecidableEq ((m ⊕ (Unit ⊕ Unit) ⊕ n) × ((m ⊕ m) ⊕ (Unit ⊕ Unit) ⊕ n)) :=
      instDecidableEqProd
    exact integral_thetaOnRealData_eq_zero Y h_theta (stdSpace E m).neg
      (isSchwartzVector_realPairWeil _ _ _ (isSchwartzVector_slice _ _ hv)) β f x g y
  obtain ⟨K, -, h_identity⟩ :=
    exists_thetaLarge_eq_smul_of_isPeriodIdentity _ (removePlanes _ Y)
      (removePlanes Unit X)
      (stdSpace E m).neg (σ' := (sumAssoc m m ((Unit ⊕ Unit) ⊕ n)).symm) h_even (ρ := 1)
      zero_le_one (by simp) hv isSchwartzVector_vacVector
      (.inr (by simp +arith [negCount_sumElim, negCount_one_and_neg_one, h_neg]))
  obtain ⟨C, hC, h_eq⟩ := h_identity 𝔠 0 h_period
  obtain rfl : C = 0 := by simpa using hC
  rw [h_eq z hz, zero_smul, Pi.zero_apply]

/-- Non-vanishing: let `X` have rank `2 k + 2 q`, where `q` is its number of negative signs, let
`m` have `2 k` elements and let `k ≤ μ w` at every infinite place `w`. Let `𝔠` be a tame character:
a character of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set of split places.
There is a Schwartz vector `v` at which the equal rank ratio of `Y = H ⊕ X = hyperbolicSum Unit X`,
the normalised square of the theta integral of `(Y, Y)` at `1`, is not zero. -/
lemma exists_equalRankThetaRatio_ne_zero (μ : InfinitePlace E → ℤ) {k : ℕ}
    (hm : card m = 2 * k) (hμ : ∀ w : InfinitePlace E, k ≤ μ w) (X : Space E n s)
    (h_rank : card n = 2 * k + 2 * negCount s) (𝔠 : SplitTameChar E μ) :
    ∃ v : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s),
      IsSchwartzVector v ∧ equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v ≠ 0 := by
  -- Otherwise the theta integral of `(H ^ (2 k) ⊕ Y, J⁻ ⊕ Y)`, `Y = H ⊕ X`, vanishes at every
  -- Schwartz vector and standard datum. Vanishing on determinant vectors descends to `(J, 0)`, but
  -- there the determinant vector is the vacuum, whose integral is a volume, not zero.
  by_contra! h_zero
  have h_top : ThetaLargeVanishes 𝔠 (hyperbolicSum m (hyperbolicSum Unit X))
      ((stdSpace E m).neg.sum (hyperbolicSum Unit X))
      (sumAssoc m m ((Unit ⊕ Unit) ⊕ n)).symm :=
    thetaLargeVanishes_of_equalRankThetaRatio_eq_zero X ⟨k + negCount s, by omega⟩ (by omega)
      h_zero
  have h_bottom : ThetaLargeVanishesOnDetVectors 𝔠 k (stdSpace E m) (stdSpace E Empty)
      (sumEmpty m Empty) := by
    refine (h_top.onDetVectors k).of_add_planes hμ (j := 2 * k + 1 + negCount s) (by omega) _ _ _
      ?_ ?_ ?_ ?_
    all_goals simp +arith [hm, h_rank, negCount_sumElim, negCount_one_and_neg_one]
  have h_vanish : thetaLarge (stdSpace E m) (stdSpace E Empty) 𝔠 vacVector
      (stdRowDatum (sumEmpty m Empty) 𝔠.semilocalChar 1) 1 = 0 := by
    simpa [detVector_of_isEmpty] using h_bottom 1 0 1 .one 1
  have h_value : stdRowDatum (sumEmpty m Empty) 𝔠.semilocalChar 1 0 = 1 := stdColDatum_one_one 𝔠
  rw [thetaLarge_stdSpace_empty_vacVector_one, h_value, mul_one, Complex.ofReal_eq_zero] at h_vanish
  exact measureReal_univ_ne_zero h_vanish

/-- Let `J` be positive definite. Let the integral of the theta kernel of `(J, J)` over the target
group be the constant `a`, and let `c` times its integral over the source group be the constant `b`.
Then `b = c a`, by Fubini's theorem. -/
lemma eq_mul_of_integral_pairTheta (J : Space E n 1) (γ : AutChar E) (f : 𝒮 (J.hom J)) {a b c : ℂ}
    (h_target : ∀ g : G E (1 : n → ℤˣ),
      ∫ h : G E (1 : n → ℤˣ), pairTheta J J γ γ f (g, h) ∂J.quotMeasure = a)
    (h_source : ∀ g : G E (1 : n → ℤˣ),
      b = c * ∫ h : G E (1 : n → ℤˣ), pairTheta J J γ γ f (h, g) ∂J.quotMeasure) :
    b = c * a := by
  have h_swap : ∫ g, ∫ h, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure =
      ∫ h, ∫ g, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure := by
    have h_one : (fun _ ↦ 1) ∈ J.rapidFunctions :=
      (J.isAutomorphic_const 1).mem_rapidFunctions fun _ _ ↦ rfl
    simpa [lift, pairTheta] using
      (pairThetaKer J J γ γ).integral_mul_lift_eq_integral_mul_lift_swap (φ := f) h_one h_one
  have h_mean : ∫ _, b ∂J.quotMeasure = c * ∫ _, a ∂J.quotMeasure := calc
    _ = ∫ g, c * ∫ h, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure :=
        congrArg _ (funext h_source)
    _ = c * ∫ h, ∫ g, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure := by
        rw [integral_const_mul, h_swap]
    _ = _ := by simp only [h_target]
  simp only [integral_const, Complex.real_smul] at h_mean
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 measureReal_univ_ne_zero)
    (by linear_combination h_mean)

/-- The exchange identity for `(J, J, 0)`. Let `J` be positive definite of rank `2 k`, let
`Y = H ⊕ X`, with `H` a hyperbolic plane, split adaptedly over `J` with `1 + q` planes, where `q`
is the number of negative signs of `X`, and let `v` be a Schwartz vector for `(Y, Y)`. There are
`B` and a Schwartz `y`
for `(J, J)` such that, for each tame character `𝔠` of weight `μ`, the theta integral of `y` and the
finite datum `stdColDatum χ 1`, the function `χ⁻¹(det)` for `χ = 𝔠.semilocalChar`, is a constant `c`
times the volume of `[U(0)]`, where `B |c| ^ 2` is `L_*(k)` times the equal rank ratio
`|I(v)(1)| ^ 2 / L_*(rk Y / 2)`. Here `I(v)` is the theta integral at `v` and `χ⁻¹(det)`, and
`L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2` for `ν = 𝔠.character` and
`S = 𝔠.ramifiedPlaces`. -/
lemma exists_thetaLarge_eq_mul_quotMeasure (μ : InfinitePlace E → ℤ) {k : ℕ} (hm : card m = 2 * k)
    (J : Space E m 1) {p : Type} [Fintype p] [DecidableEq p] [Nonempty p] (X : Space E n s)
    (A : (hyperbolicSum Unit X).Splitting J p) [IsBaseAdapted A]
    (h_planes : 1 + negCount s = card p)
    {v : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s)}
    (hv : IsSchwartzVector v) :
    ∃ (B : ℝ) (y : PairFock E (1 : m → ℤˣ) 1), IsSchwartzVector y ∧
      ∀ 𝔠 : SplitTameChar E μ, ∃ c : ℂ,
        B * ‖c‖ ^ 2 = lValueProdInt 𝔠 k * equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v ∧
        ∀ g : G E (1 : m → ℤˣ), thetaLarge J J 𝔠 y (stdColDatum 𝔠.semilocalChar 1) g =
          c * (stdSpace E Empty).quotMeasure.real Set.univ := by
  let Z : Space E Empty 1 := stdSpace E Empty
  obtain ⟨B, y, hy, h_all⟩ := exchange_of_matches J Z μ J (emptySum Empty m) X A hv
    isSchwartzVector_vacVector (by simp [negCount_one_and_neg_one]) ⟨k, hm⟩ (by simp [h_planes])
  refine ⟨B, y, hy, fun 𝔠 ↦ ?_⟩
  obtain ⟨c, hc, h_exchange⟩ := h_all 𝔠
  have h_rank : (card m - card m / 2 : ℤ) = k := by omega
  refine ⟨c, by rw [hc, h_rank], fun g ↦ ?_⟩
  let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
  let f : 𝒮 (J.hom J) := localDatum J J y (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt
  have h_identity : thetaIntegral J J γ 1 f g = c * ∫ h, pairTheta Z J γ γ
      (localDatum Z J vacVector (stdColDatum 𝔠.semilocalChar 0) 𝔠.readsAt) (h, g) ∂Z.quotMeasure :=
    h_exchange (stdColDatum 𝔠.semilocalChar 1) (stdColDatum 𝔠.semilocalChar 0) (.of_discrete _)
      (areMatched_stdRowDatum_stdColDatum (emptySum Empty m) (s := 0) nofun) g
  -- The second character enters both sides as its inverse at `det g`.
  refine mul_left_cancel₀ (γ.val g.det).coe_ne_zero ?_
  calc γ.val g.det * thetaIntegral J J γ γ f g = thetaIntegral J J γ 1 f g := by
        rw [thetaIntegral, thetaIntegral, ← integral_const_mul]
        congr with h
        simp [pairTheta, pairWeil_apply, pairChar_apply, field]
    _ = γ.val g.det * (c * Z.quotMeasure.real Set.univ) := by
        rw [h_identity]
        simp [pairTheta_source_zero, stdColDatum, IsIntMatrix, invOnUnits, IsIntegralUnit, Z, γ,
          field]

/-- The exchange identity for `(J, 0, J)`. Let `J` be positive definite of rank `2 k`, let
`Y = H ⊕ X`, with `H` a hyperbolic plane, split adaptedly over `J` with `1 + q` planes, where `q`
is the number of negative signs of `X`, and let `v` for `(Y, Y)` and `y` for `(J, J)` be Schwartz
vectors. There
are `C` and a number `ξ` such that each tame character `𝔠` of weight `μ` has a number `c` as
follows. The volume of `[U(0)]` times `ξ` is `c` times the integral over the first `[U(J)]` of the
theta kernel of `(J, J)` with both characters `γ = ν⁻¹ υ ^ k` and datum `y` at the infinite places,
`χ⁻¹(det)` (`stdColDatum χ 1`) at `S` and the vacuum elsewhere (`localDatum`), and `C |c| ^ 2` is
`L_*(-k) = L_*(k)⁻¹` times the equal rank ratio `|I(v)(1)| ^ 2 / L_*(rk Y / 2)`. Here
`ν = 𝔠.character`, `S = 𝔠.ramifiedPlaces`, `χ = 𝔠.semilocalChar`, `υ` is the splitting character of
the Weil data on norm-one ideles, `I(v)` is the theta integral at `v` and `χ⁻¹(det)`, and
`L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2`. -/
lemma exists_quotMeasure_mul_eq_mul_integral_pairTheta (μ : InfinitePlace E → ℤ) {k : ℕ}
    (hm : card m = 2 * k) (J : Space E m 1) {p : Type} [Fintype p] [DecidableEq p] [Nonempty p]
    (X : Space E n s)
    (A : (hyperbolicSum Unit X).Splitting J p) [IsBaseAdapted A]
    (h_planes : 1 + negCount s = card p)
    {v : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s)}
    {y : PairFock E (1 : m → ℤˣ) 1} (hv : IsSchwartzVector v) (hy : IsSchwartzVector y) :
    ∃ (C : ℝ) (ξ : ℂ), ∀ 𝔠 : SplitTameChar E μ,
      let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
      ∃ c : ℂ,
        C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (-k) * equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v ∧
        ∀ g : G E (1 : m → ℤˣ), (stdSpace E Empty).quotMeasure.real Set.univ * ξ =
          c * ∫ h : G E (1 : m → ℤˣ), pairTheta J J γ γ
            (localDatum J J y (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt) (h, g) ∂J.quotMeasure := by
  let Z : Space E Empty 1 := stdSpace E Empty
  obtain ⟨C, x, -, h_all⟩ := exchange_of_matches J J μ Z
    (sumEmpty m Empty) X A hv hy (by simp [negCount_one_and_neg_one]) ⟨k, hm⟩ (by simp [h_planes])
  -- The vector `x` lies in the Fock space `ℂ` of `(J, 0)`, and `ξ` is its value.
  refine ⟨C, θ (J.hom Z) (integrated (J.hom Z) x (J.hom Z).vacElem), fun 𝔠 ↦ ?_⟩
  obtain ⟨c, hc, h_exchange⟩ := h_all 𝔠
  have h_size :
      C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (-k) * equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v := by
    simpa [hm] using hc
  refine ⟨c, h_size, fun g ↦ ?_⟩
  let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
  let Φ : Matrix Empty m (LocProd 𝔠.ramifiedPlaces) → ℂ :=
    stdRowDatum (sumEmpty m Empty) 𝔠.semilocalChar 1
  let Ψ : Matrix m m (LocProd 𝔠.ramifiedPlaces) → ℂ := stdColDatum 𝔠.semilocalChar 1
  have h_locally_const : IsLocallyConstant Ψ :=
    (stdColDatum_mem_schwartzBruhat 𝔠.semilocalChar .one).1
  have h_matched : AreMatched SemilocalField.O (sumEmpty m Empty) 𝔠.semilocalChar Φ Ψ :=
    areMatched_stdRowDatum_stdColDatum (sumEmpty m Empty) .one
  have h_identity : thetaIntegral J Z γ 1 (localDatum J Z x Φ 𝔠.readsAt) g =
      c * ∫ h : G E (1 : m → ℤˣ), pairTheta J J γ γ (localDatum J J y Ψ 𝔠.readsAt) (h, g)
        ∂J.quotMeasure :=
    h_exchange Φ Ψ h_locally_const h_matched g
  -- On the zero space the theta kernel only reads `Φ 0`, which is `1`.
  have h_value : Φ 0 = 1 := stdColDatum_one_one 𝔠
  simpa [thetaIntegral, pairTheta_target_zero, Z, h_value] using h_identity

/-- The exchange identity used twice. Let `J` be positive definite of rank `2 k`, let `Y = H ⊕ X`,
with `H` a hyperbolic plane, split adaptedly over `J` with `1 + q` planes, where `q` is the number
of negative signs of `X`, and let `v` be a Schwartz vector for `(Y, Y)`. As `𝔠` runs through the
tame characters of weight `μ`, the square of the equal rank ratio `|I(v)(1)| ^ 2 / L_*(rk Y / 2)`
is one number `D`. Here
`I(v)` is the theta integral `thetaLarge` with real part `v` and the function `χ⁻¹(det)` at the
ramified places, `χ = 𝔠.semilocalChar`, and `L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i,
ν)| ^ 2` for `ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`. -/
lemma exists_equalRankThetaRatio_sq_eq (μ : InfinitePlace E → ℤ) {k : ℕ} (hm : card m = 2 * k)
    (J : Space E m 1) {p : Type} [Fintype p] [DecidableEq p] [Nonempty p] (X : Space E n s)
    (A : (hyperbolicSum Unit X).Splitting J p) [IsBaseAdapted A]
    (h_planes : 1 + negCount s = card p)
    {v : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s)}
    (hv : IsSchwartzVector v) :
    ∃ D : ℝ, ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v ^ 2 = D := by
  let ratio (𝔠 : SplitTameChar E μ) : ℝ := equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v
  let vol : ℝ := (stdSpace E Empty).quotMeasure.real Set.univ
  have h_vol : (vol : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 measureReal_univ_ne_zero
  obtain ⟨B, y, hy, h_forward_exchange⟩ :=
    exists_thetaLarge_eq_mul_quotMeasure μ hm J X A h_planes hv
  obtain ⟨C, ξ, h_reverse_exchange⟩ :=
    exists_quotMeasure_mul_eq_mul_integral_pairTheta μ hm J X A h_planes hv hy
  refine ⟨B * C * ‖ξ‖ ^ 2, fun 𝔠 ↦ ?_⟩
  -- Compare the two exchange constants by integrating the same theta kernel over both
  -- groups in opposite orders.
  let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
  let f : 𝒮 (J.hom J) := localDatum J J y (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt
  obtain ⟨c₁, hc₁, h_forward_integral⟩ : ∃ c₁ : ℂ, B * ‖c₁‖ ^ 2 = lValueProdInt 𝔠 k * ratio 𝔠 ∧
      ∀ g : G E 1, thetaLarge J J 𝔠 y (stdColDatum 𝔠.semilocalChar 1) g = c₁ * vol :=
    h_forward_exchange 𝔠
  obtain ⟨c₂, hc₂, h_reverse_integral⟩ : ∃ c₂ : ℂ, C * ‖c₂‖ ^ 2 = lValueProdInt 𝔠 (-k) * ratio 𝔠 ∧
      ∀ g : G E 1, vol * ξ = c₂ * ∫ h, pairTheta J J γ γ f (h, g) ∂J.quotMeasure :=
    h_reverse_exchange 𝔠
  have h_integral_orders : vol * ξ = c₂ * (c₁ * vol) :=
    eq_mul_of_integral_pairTheta J γ f h_forward_integral h_reverse_integral
  have h_exchange_product : ξ = c₂ * c₁ :=
    mul_left_cancel₀ h_vol (by linear_combination h_integral_orders)
  -- Opposite rank differences give reciprocal L-value factors; the normalized ratio remains.
  have h_reciprocal_L_values : lValueProdInt 𝔠 k * lValueProdInt 𝔠 (-k) = 1 := by
    simp [lValueProdInt_natCast, lValueProdInt_neg_natCast, (lValueProd_pos 𝔠 k).ne']
  calc ratio 𝔠 ^ 2 = (lValueProdInt 𝔠 k * ratio 𝔠) * (lValueProdInt 𝔠 (-k) * ratio 𝔠) := by
        rw [mul_mul_mul_comm, h_reciprocal_L_values, one_mul, sq]
    _ = B * C * ‖ξ‖ ^ 2 := by
        simp only [ratio, ← hc₁, ← hc₂, h_exchange_product, norm_mul]
        ring

/-- The value for a space that splits over a definite one. Let `J` be the standard positive
definite space of rank `2 k`, with `k ≤ μ` at every infinite place, let `X` have rank
`2 k + 2 q`, where `q` is its number of negative signs, and let `A` be an adapted splitting of
`H ⊕ X` over `J` with `1 + q` hyperbolic planes. Some Schwartz vector `v` for `(H ⊕ X, H ⊕ X)` has
an equal rank ratio that is one number `C ≠ 0` for all tame characters of weight `μ`. -/
lemma exists_equalRankThetaRatio_const_ne_zero (μ : InfinitePlace E → ℤ) {k : ℕ}
    (hm : card m = 2 * k) (hμ : ∀ w : InfinitePlace E, k ≤ μ w) {p : Type} [Fintype p]
    [DecidableEq p] [Nonempty p] (X : Space E n s)
    (A : (hyperbolicSum Unit X).Splitting (stdSpace E m) p) [IsBaseAdapted A]
    (h_planes : 1 + negCount s = card p) (h_rank : card n = 2 * k + 2 * negCount s) :
    ∃ v : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s),
      IsSchwartzVector v ∧ ∃ C ≠ (0 : ℝ),
        ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v = C := by
  obtain h_empty | ⟨⟨𝔠₀⟩⟩ := isEmpty_or_nonempty (SplitTameChar E μ)
  · exact ⟨vacVector, isSchwartzVector_vacVector, 1, one_ne_zero, h_empty.elim⟩
  obtain ⟨v, hv, h_ne⟩ := exists_equalRankThetaRatio_ne_zero μ hm hμ X h_rank 𝔠₀
  -- The ratio of `v` is nonnegative and has constant square, so it is a nonzero constant.
  obtain ⟨D, h_sq⟩ := exists_equalRankThetaRatio_sq_eq μ hm _ X A h_planes hv
  have h_nonneg (𝔠 : SplitTameChar E μ) :
      0 ≤ equalRankThetaRatio (hyperbolicSum Unit X) 𝔠 v :=
    div_nonneg (sq_nonneg _) (lValueProdInt_pos 𝔠 _).le
  refine ⟨v, hv, _, h_ne, fun 𝔠 ↦ (sq_eq_sq₀ (h_nonneg 𝔠) (h_nonneg 𝔠₀)).1 ?_⟩
  rw [h_sq, h_sq]

/-- Let `Y` have even rank and let `A` be an adapted splitting `Y = W ⊕ H` with `H` a hyperbolic
plane (its frames are orthonormal at the infinite and integral at the finite places). Let `Y₁` be
any space with the signs of `Y`, `𝔠` a tame character and `v` a Schwartz vector (all Fock moments
finite). Then the equal rank ratio `|I(1)| ^ 2 / L_*(rank / 2)` is the same for `Y₁` and `Y`, where
`I` is the theta integral of `v` and `𝔠.semilocalChar⁻¹(det)` for the pair `(Y₁, Y₁)`, resp.
`(Y, Y)`, and `L_* = lValueProdInt 𝔠` is a product of partial L-values of `𝔠`. -/
lemma equalRankThetaRatio_eq_of_signs_eq {W : Space E n s} {μ : InfinitePlace E → ℤ}
    {n' : Type} [Fintype n'] [DecidableEq n'] {s' : n' → ℤˣ}
    {Y : Space E n' s'} (A : Y.Splitting W Unit) [IsBaseAdapted A] (Y₁ : Space E n' s')
    (h_even : 2 ∣ card n') (𝔠 : SplitTameChar E μ) {v : PairFock E s' s'}
    (hv : IsSchwartzVector v) :
    equalRankThetaRatio Y₁ 𝔠 v = equalRankThetaRatio Y 𝔠 v := by
  -- Changing the space moves the point and multiplies by a number of modulus one; the theta
  -- integral of `Y` is constant.
  obtain ⟨γ, hγ⟩ := exists_thetaLarge_thetaSmall_eq_circle_mul Y Y₁ Y Y₁ Y Y
  obtain ⟨⟨u, h_move⟩, -⟩ := hγ 𝔠
  simp [equalRankThetaRatio, h_move, thetaLarge_eq_apply_one_of_even_rank A 𝔠 h_even hv,
    Circle.norm_coe]

/-- The value of the equal rank ratio. Let `rk W = 2 k + 2 q`, where `q` is the number of negative
signs of `W`, and `k ≤ μ` at every infinite place. There are a Schwartz vector (all Fock moments
finite) `v` for `(H ⊕ W, H ⊕ W)`, with `H` a hyperbolic plane, and `C ≠ 0` such that
`|I(v)(1)| ^ 2 / L_*(rk W / 2 + 1) = C` for every tame character `𝔠` of weight `μ`. Here `I(v)` is
the theta integral `thetaLarge` with real part `v` and the function `χ⁻¹(det)` at the ramified
places, `χ = 𝔠.semilocalChar`, and `L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2`
for `ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`. -/
lemma exists_equalRankThetaRatio_eq_const (W : Space E n s) (μ : InfinitePlace E → ℤ) (k : ℕ)
    (h_rank : card n = 2 * k + 2 * negCount s) (hμ : ∀ w : InfinitePlace E, k ≤ μ w) :
    ∃ v : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s),
      IsSchwartzVector v ∧ ∃ C ≠ (0 : ℝ),
        ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 v = C := by
  -- A space `X` with the signs of `W` splits over the definite space `J` of rank `2 k`.
  have h_even : 2 ∣ card ((Unit ⊕ Unit) ⊕ n) := ⟨1 + k + negCount s, by simp +arith [h_rank]⟩
  obtain ⟨X, A, _⟩ := exists_isBaseAdapted (Fin (negCount s)) (stdSpace E (Fin (2 * k))) s
    (by simp [h_rank]) (by simp)
  obtain ⟨v, hv, C, hC, h_const⟩ := exists_equalRankThetaRatio_const_ne_zero μ (m := Fin (2 * k))
    (by simp) hμ X ((removePlanes Unit X).comp A) (by simp) h_rank
  refine ⟨v, hv, C, hC, fun 𝔠 ↦ ?_⟩
  rw [equalRankThetaRatio_eq_of_signs_eq (removePlanes Unit X) _ h_even 𝔠 hv, h_const]

end EqualRankValue

/-!
## The exchange theorem for data modulo an ideal

`New.Exchange.exchange_theorem` exchanges a theta integral over `[U(V)]` for one over `[U(V')]`, for
finite data given by functions on matrices over `O_E / 𝔪`. It is deduced from
`New.Exchange.exchange_of_matches`, the same exchange for data on the completions at the primes of
`𝔪`, and the value `New.Exchange.exists_equalRankThetaRatio_eq_const`.
-/

section ExchangeTheorem

open RingHom Fintype Rows Modulus IsLinearMap

/-- The space character `α.spaceChar p` is the Hecke character `x ↦ α (x / x̄) υ x ^ (-p)`. In even
rank `card N = p + q` those of `α` in rank `p` and of `α'` in rank `q` multiply to the inverse of
the base change `x ↦ ν (x / x̄)` exactly if `α * α' = rankTwist ν⁻¹ N = ν⁻¹ υ ^ (card N / 2)`. -/
lemma spaceChar_mul_spaceChar_eq_iff {E : Type} [Field E] [CMType E] [WeilData E]
    {N : Type} [Fintype N] {α α' ν : AutChar E} {p q : ℕ}
    (h_card : card N = p + q) (h_even : 2 ∣ card N) :
    α.spaceChar p * α'.spaceChar q = ν.baseChange⁻¹ ↔ α * α' = rankTwist ν⁻¹ N := by
  classical
  have h_mul : α.spaceChar p * α'.spaceChar q = (α * α').spaceChar (card N) := by
    rw [h_card, AutChar.spaceChar_mul]
  rw [h_mul, ← map_inv, ← spaceChar_rankTwist h_even]
  simp only [AutChar.spaceChar, mul_left_inj, AutChar.baseChange_injective.eq_iff]

variable {E : Type} [Field E] [CMType E] [WeilData E] {n a b : Type} [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {t : a → ℤˣ} {t' : b → ℤˣ}
  (W : Space E n s) (V : Space E a t) (V' : Space E b t')

/-- Let `W`, `V`, `V'` be spaces with coordinates indexed by `n`, `a`, `b`, split by
`σ : b ⊕ a ≃ n`, and let the tame character `𝔠` be ramified exactly at the primes of the modulus
`𝔪`. Let `Φ`, `Ψ` be matched functions over `O_E / 𝔪` for the product `χ` of the residue characters
of `𝔠`: `Φ` is supported on the last rows of `k⁻¹` and `Ψ` on the first columns of `k` (split by
`σ`), for `k` in `GL_n(O_E / 𝔪)` (the subring `⊤`), and there `Φ = χ (det k) * Ψ`. Then there are
functions `Φ'`, `Ψ'` on matrices over the completions at these primes, matched over the local
integers `SemilocalField.O` for `𝔠.semilocalChar`, with `Ψ'` locally constant, that give the same
adelic data as `Φ` for `(W, V)` and `Ψ` for `(V', W)`, whatever the real vector. -/
lemma exists_areMatched_modDatum_eq (σ : b ⊕ a ≃ n) {μ : NumberField.InfinitePlace E → ℤ}
    (𝔪 : Modulus E) (𝔠 : SplitTameChar E μ)
    (h_ramified : (𝔠.ramifiedPlaces : Set (FinPlace E)) = 𝔪.places)
    {Φ : Matrix a n 𝔪.ResidueRing → ℂ} {Ψ : Matrix n b 𝔪.ResidueRing → ℂ}
    (h_matched : AreMatched ⊤ σ (𝔪.charOfTamePart 𝔠.tamePart) Φ Ψ) :
    ∃ (Φ' : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (Ψ' : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
      IsLocallyConstant Ψ' ∧
      AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ' Ψ' ∧
      (∀ x : PairFock E s t, modDatum W V 𝔪 Φ x = localDatum W V x Φ' 𝔠.readsAt) ∧
      ∀ v : PairFock E t' s, modDatum V' W 𝔪 Ψ v = localDatum V' W v Ψ' 𝔠.readsAt := by
  -- `Φ'` and `Ψ'` are the lifts along the reduction `π` from the local integers to `𝔪.ResidueRing`.
  have h_reads : ReadsAt 𝔪.places (evalPlaces 𝔠.ramifiedPlaces) := by
    simpa only [h_ramified] using 𝔠.readsAt
  -- `ρ` is a continuous section of the projection `evalPlaces 𝔠.ramifiedPlaces` to the components
  -- at `𝔪`
  obtain ⟨ρ, hρ_cont, ev_ρ, ρ_ev⟩ := h_reads.exists_section.2
  let ev : Ô E →+* SemilocalField.O := (evalPlaces 𝔠.ramifiedPlaces).restrict _ _ evalPlaces_mem_O
  let sec (y : SemilocalField.O (F := LocProd 𝔠.ramifiedPlaces)) : Ô E :=
    ⟨ρ y, by simpa [← ρ_ev, ev_ρ] using (h_reads.mem_iff (ρ y)).1 (by simp [ev_ρ])⟩
  have h_sec : Function.RightInverse sec ev := fun y ↦ Subtype.ext (ev_ρ y)
  -- reduction modulo `𝔪` only sees these components, so it factors as `π ∘ ev`
  have h_ker : ker ev ≤ ker 𝔪.reduction := fun y hy ↦ by
    rw [mem_ker, ← map_zero 𝔪.reduction]
    exact 𝔪.reduction_congr fun w hw ↦
      congrFun (congrArg Subtype.val hy) ⟨w, h_ramified.ge hw⟩
  let π : SemilocalField.O →+* 𝔪.ResidueRing := ev.liftOfRightInverse sec h_sec ⟨𝔪.reduction, h_ker⟩
  -- `π` is compatible with the residue maps, so it detects units; it is onto since
  -- `𝔪.reduction` is onto
  have π_res (i : 𝔠.ramifiedPlaces) (u : SemilocalField.O) :
      modulusResidue 𝔪 (h_ramified.le i.property) (π u) = residueAt i u :=
    (modulusResidue_reduction 𝔪 (h_ramified.le i.property) (sec u)).trans
      (congrArg (IsLocalRing.residue (LocInt i.val)) (Subtype.ext (congrFun (ev_ρ u) i)))
  have π_local : IsLocalHom π := by
    refine ⟨fun u hu ↦ isUnit_iff_residueAt_ne_zero.2 fun i ↦ ?_⟩
    rw [← π_res]
    exact (hu.map _).ne_zero
  have π_surj : Function.Surjective π :=
    𝔪.reduction_surjective.forall.2 fun y ↦ ⟨ev y, liftOfRightInverse_comp_apply ..⟩
  -- on units both characters are the product of the residue characters `𝔠.tamePart`
  have π_char (u : SemilocalField.O) (hu : IsUnit u) :
      𝔠.semilocalChar u.val = 𝔪.charOfTamePart 𝔠.tamePart (π u) := calc
    _ = ∏ i : 𝔠.ramifiedPlaces, 𝔠.tamePart i (residueAt i u) :=
        𝔠.localChar_apply_of_isUnit _ u hu
    _ = ∏ᶠ i : 𝔠.ramifiedPlaces, 𝔠.tamePart i (modulusResidue 𝔪 (h_ramified.le i.2) (π u)) := by
        simp only [π_res, finprod_eq_prod_of_fintype]
    _ = ∏ᶠ w : 𝔪.places, 𝔠.tamePart w (modulusResidue 𝔪 w.property (π u)) :=
        finprod_comp_equiv (f := fun w : 𝔪.places ↦ 𝔠.tamePart w (modulusResidue 𝔪 w.2 (π u)))
          (.subtypeEquivRight (Set.ext_iff.1 h_ramified))
  -- lifting from `𝔪.ResidueRing` to adeles is lifting along `π`, then reading the components
  have π_ev (z : 𝔸f E) (hz : evalPlaces 𝔠.ramifiedPlaces z ∈ SemilocalField.O) :
      π ⟨evalPlaces 𝔠.ramifiedPlaces z, hz⟩ = 𝔪.reduction
        ⟨idem 𝔪.places * z, (h_reads.mem_iff z).1 hz⟩ :=
    congrArg 𝔪.reduction (Subtype.ext (ρ_ev z))
  have h_lift {n n' : Type} [Fintype n] [Fintype n'] (Φ : Matrix n' n 𝔪.ResidueRing → ℂ) :
      𝔪.liftFn (Φ ∘ vecToMatrix) = fun y ↦
        liftIntegralFn π Φ (vecToMatrix (evalPlaces 𝔠.ramifiedPlaces ∘ y)) := by
    ext y
    rw [liftFn_apply, liftIntegralFn, mk'_apply]
    have h_int : (∀ i : n' × n, idem 𝔪.places * y i ∈ Ô E) ↔
        ∀ (i : n') (j : n), vecToMatrix (evalPlaces 𝔠.ramifiedPlaces ∘ y) i j ∈
          SemilocalField.O := by
      simp [vecToMatrix, h_reads.mem_iff]
    by_cases h : ∀ i : n' × n, idem 𝔪.places * y i ∈ Ô E
    · rw [dite_eq_left h, dite_eq_left (h_int.1 h)]
      exact congrArg Φ (Matrix.ext fun i j ↦ (π_ev (y (i, j)) (h_int.1 h i j)).symm)
    · rw [dite_eq_right h, dite_eq_right (mt h_int.2 h)]
  have h_locally_const : IsLocallyConstant (liftIntegralFn π Ψ) := by
    have h_schwartz : IsSchwartzBruhat 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix)) :=
      isSchwartzBruhat_liftFn 𝔪 (Ψ ∘ vecToMatrix)
    rw [h_lift] at h_schwartz
    simpa [Function.comp_def, ev_ρ] using
      h_schwartz.locally_constant.comp_continuous (f := fun y ↦ ρ ∘ matrixToVec y)
        (by fun_prop [matrixToVec])
  refine ⟨liftIntegralFn π Φ, liftIntegralFn π Ψ, h_locally_const,
    h_matched.lift_of_reduction π π_local π_surj π_char, fun x ↦ ?_, fun v ↦ ?_⟩
  all_goals
    rw [modDatum, h_lift, ← h_ramified, localDatum]
    rfl

/-- Let `W`, `V`, `V'` have ranks `|n| = |b| + |a|` (split by `σ`), `|a| = |b| + 2e` and `|b|`. Let
`W` have as many negative signs `q` as `V` and `V'` together, with `2q + 2 ≤ |n|`. Let the weights
satisfy `|n| ≤ 2 μ + 2q`, and let `v` be a real Schwartz vector for `(V', W)`. There are `C` and a
Schwartz `x` for `(W, V)` such that every character `ν` of `[U(1)]` of weight `μ` that is tame for
`(𝔪, χ)` (ramified exactly at the primes of `𝔪`, with residue character `χ`) has some `c ≠ 0` with
(a) and (b). (a) `‖c‖²` is `C` times `lValueProd 𝔪.places ν e`, a power of the norm of the primes of
`𝔪` times the product of the squares of the partial L-values `|L^S(z, ν)|` for `z = 1, …, e`, with
`S` the primes of `𝔪`; so `C > 0` as soon as such a `ν` exists. (b) For all matched functions `Φ`,
`Ψ` modulo `𝔪`, the theta integral of `(x, Φ)` over `[U(V)]` is `c` times that of `(v, Ψ)` over
`[U(V')]`, as functions on `U(W)`. The left side has the characters `γ` and `1`, the right side `γ`
and `γ`, with `γ = rankTwist ν⁻¹ n = ν⁻¹ υ ^ (|n| / 2)`. -/
lemma exchange_theorem (σ : b ⊕ a ≃ n) (h_signs : negCount s = negCount t + negCount t') {e : ℕ}
    (h_rank : card a = card b + 2 * e) (h_few_neg : 2 * negCount s + 2 ≤ card n)
    {μ : NumberField.InfinitePlace E → ℤ}
    (hμ : ∀ τ : NumberField.InfinitePlace E, card n ≤ 2 * μ τ + 2 * negCount s)
    {v : Fock.fockSpace (realSigns E (homSigns t' s))} (hv : IsSchwartzVector v) :
    ∃ (C : ℝ) (x : Fock.fockSpace (realSigns E (homSigns s t))),
      IsSchwartzVector x ∧
      ∀ (𝔪 : Modulus E) (ν : AutChar E) (χ : MulChar 𝔪.ResidueRing ℂ), IsTameFor 𝔪 ν μ χ →
        let γ : AutChar E := rankTwist ν⁻¹ n
        ∃ c ≠ (0 : ℂ),
          -- (a) the size of the constant
          ‖c‖ ^ 2 = C * lValueProd 𝔪.places ν e ∧
          -- (b) the exchange of the two theta integrals on matched functions modulo `𝔪`
          ∀ (Φ : Matrix a n 𝔪.ResidueRing → ℂ) (Ψ : Matrix n b 𝔪.ResidueRing → ℂ),
            AreMatched ⊤ σ χ Φ Ψ →
            ∀ g : G E s,
            thetaIntegral W V γ 1 (modDatum W V 𝔪 Φ x) g =
              c *
                ∫ h : G E t', pairTheta V' W γ γ (modDatum V' W 𝔪 Ψ v) (h, g) ∂V'.quotMeasure := by
  -- Lift matched functions modulo `𝔪` to the completions at its primes and apply
  -- `exchange_of_matches`, at a `z` whose equal rank ratio is a nonzero constant.
  have h_card : card n = 2 * card b + 2 * e := by
    rw [← card_congr σ, card_sum, h_rank]
    ring
  have h_weight (w : NumberField.InfinitePlace E) : (card n / 2 - negCount s : ℕ) ≤ μ w := by
    have h_bound : (card n : ℤ) ≤ 2 * μ w + 2 * negCount s := hμ w
    omega
  obtain ⟨z, hz, C₀, hC₀, h_value⟩ :
      ∃ z : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s),
        IsSchwartzVector z ∧ ∃ C₀ ≠ (0 : ℝ),
          ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 z = C₀ :=
    exists_equalRankThetaRatio_eq_const W μ (card n / 2 - negCount s) (by omega) h_weight
  obtain ⟨C, x, hx, h_core⟩ := exchange_of_matches W V' μ V σ W (removePlanes Unit W) hz hv h_signs
    (by omega) (by simp)
  refine ⟨C₀ / C, x, hx, fun 𝔪 ν χ ⟨h_ne, ψ, hν, h_ram, hχ⟩ ↦ ?_⟩
  -- the tame character ramified at the primes of `𝔪`
  have h_places : 𝔪.places.toFinite.toFinset = 𝔪.places := 𝔪.places.toFinite.coe_toFinset
  let 𝔠 : SplitTameChar E μ :=
    { character := ν, tamePart := ψ, hasWeight := hν, ramifiedPlaces := 𝔪.places.toFinite.toFinset
      nonempty := 𝔪.places.toFinite.toFinset_nonempty.2 (Set.nonempty_coe_sort.1 h_ne)
      star_notMem := fun w hw hw' ↦ 𝔪.not_le_star w (h_places.le hw) (h_places.le hw')
      ne_one_iff := by simpa using h_ram
      weight_pos := fun w ↦ by linarith [hμ w] }
  obtain ⟨c, hc, h_exch⟩ := h_core 𝔠
  -- the size of `c`: the right side below is not zero, so neither `C` nor `c` is
  have hL : lValueProdInt 𝔠 e = lValueProd 𝔪.places ν e := by
    rw [lValueProdInt_natCast, h_places]
  replace hc : C * ‖c‖ ^ 2 = lValueProd 𝔪.places ν e * C₀ := by
    rw [hc, show (card a - card n / 2 : ℤ) = e by omega, hL, h_value]
  have hL_ne : lValueProd 𝔪.places ν e ≠ 0 := hL.symm.trans_ne (lValueProdInt_pos 𝔠 e).ne'
  obtain ⟨hC, hc_ne⟩ : C ≠ 0 ∧ c ≠ 0 := by simpa using hc.trans_ne (mul_ne_zero hL_ne hC₀)
  have h_size : ‖c‖ ^ 2 = C₀ / C * lValueProd 𝔪.places ν e := by
    field_simp
    linear_combination hc
  refine ⟨c, hc_ne, h_size, fun Φ Ψ h_matched ↦ ?_⟩
  -- matched functions modulo `𝔪` give the same data as matched functions on the completions
  obtain ⟨Φ', Ψ', h_locally_const, h_matched', hΦ, hΨ⟩ :
      ∃ (Φ' : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
        (Ψ' : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
        IsLocallyConstant Ψ' ∧ AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ' Ψ' ∧
        (∀ x, modDatum W V 𝔪 Φ x = localDatum W V x Φ' 𝔠.readsAt) ∧
        ∀ v, modDatum V' W 𝔪 Ψ v = localDatum V' W v Ψ' 𝔠.readsAt :=
    exists_areMatched_modDatum_eq W V V' σ 𝔪 𝔠 h_places (by rwa [hχ] at h_matched)
  simpa only [hΦ, hΨ] using h_exch Φ' Ψ' h_locally_const h_matched'

/-- Let `W`, `V`, `V'` have ranks `|n| = |b| + |a|` (split by `σ`), `|a| = |b| + 2e`, `|b|`. Let `W`
have as many negative signs `q` as `V` and `V'` together, with `2q + 2 ≤ |n| ≤ 2 μ + 2q`, and let
`v` be a real Schwartz vector for `(V', W)`. There are `C > 0` and a Schwartz vector `x` for
`(W, V)`, chosen before `𝔪` and `ν`, such that every character `ν` of `[U(1)]` of weight `μ` that is
tame for `(𝔪, χ)` has a number `c` as follows. Its size is `‖c‖² = C * lValueProd 𝔪.places ν e ≠ 0`.
For all `α`, `α'` such that the characters `α.spaceChar |a|` of `V` and `α'.spaceChar |b|` of `V'`
have product inverse to the base change `x ↦ ν (x / x̄)`, and all matched functions `Φ`, `Ψ` modulo
`𝔪`, the theta integral of `(x, Φ)` over `[U(V)]` is `c` times that of `(v, Ψ)` over `[U(V')]`, as
functions on `U(W)`. The character of `W` is `rankTwist ν⁻¹ n = ν⁻¹ υ ^ (|n| / 2)`, and `modDatum`
puts a function modulo `𝔪` at the primes of `𝔪` and the vacuum at the other finite places. -/
theorem exchange_identity (σ : b ⊕ a ≃ n) (h_signs : negCount s = negCount t + negCount t')
    {e : ℕ} (h_rank : card a = card b + 2 * e) (h_few_neg : 2 * negCount s + 2 ≤ card n)
    {μ : NumberField.InfinitePlace E → ℤ}
    (hμ : ∀ τ : NumberField.InfinitePlace E, card n ≤ 2 * μ τ + 2 * negCount s)
    {v : PairFock E t' s} (hv : IsSchwartzVector v) :
    ∃ C : ℝ, 0 < C ∧ ∃ x : PairFock E s t, IsSchwartzVector x ∧
      ∀ (𝔪 : Modulus E) (ν : AutChar E) (χ : MulChar 𝔪.ResidueRing ℂ), IsTameFor 𝔪 ν μ χ →
      ∃ c : ℂ,
        ‖c‖ ^ 2 = C * lValueProd 𝔪.places ν e ∧
        C * lValueProd 𝔪.places ν e ≠ 0 ∧
        ∀ α α' : AutChar E,
          α.spaceChar (card a) * α'.spaceChar (card b) = ν.baseChange⁻¹ →
          ∀ (Φ : Matrix a n 𝔪.ResidueRing → ℂ) (Ψ : Matrix n b 𝔪.ResidueRing → ℂ),
            AreMatched ⊤ σ χ Φ Ψ →
            ∀ g : G E s,
              thetaIntegral W V (rankTwist ν⁻¹ n) α (modDatum W V 𝔪 Φ x) g =
                c * ∫ h : G E t',
                  pairTheta V' W α' (rankTwist ν⁻¹ n) (modDatum V' W 𝔪 Ψ v) (h, g)
                  ∂V'.quotMeasure := by
  -- `exchange_theorem` is the case `α = 1`, `α' = rankTwist ν⁻¹ n`; other splitting characters
  -- multiply both sides by the same factor `α (det g)⁻¹`.
  obtain ⟨C, x, hx, h_exch⟩ := exchange_theorem W V V' σ h_signs h_rank h_few_neg hμ hv
  obtain hC | hC := le_or_gt C 0
  · -- If `C ≤ 0` there is no pair `(𝔪, ν)`: `‖c‖ ^ 2 > 0`, but `C` times the `L`-values is `≤ 0`.
    refine ⟨1, one_pos, x, hx, fun 𝔪 ν χ h_tame ↦ ?_⟩
    obtain ⟨c, hc, h_size, -⟩ := h_exch 𝔪 ν χ h_tame
    have h_L : 0 ≤ lValueProd 𝔪.places ν e := by
      unfold lValueProd
      positivity
    nlinarith [norm_pos_iff.mpr hc]
  refine ⟨C, hC, x, hx, fun 𝔪 ν χ h_tame ↦ ?_⟩
  obtain ⟨c, hc, h_size, h_base⟩ := h_exch 𝔪 ν χ h_tame
  refine ⟨c, h_size, by simp [← h_size, hc], fun α α' h_prod Φ Ψ h_matched g ↦ ?_⟩
  set γ : AutChar E := rankTwist ν⁻¹ n
  have h_card : card n = card a + card b := by rw [add_comm, ← card_sum, card_congr σ]
  -- The splitting characters determine `α * α' = γ`.
  have h_char : α * α' = γ :=
    (spaceChar_mul_spaceChar_eq_iff h_card ⟨card b + e, by omega⟩).1 h_prod
  have h_char' : γ * α⁻¹ = α' := by rw [← h_char, mul_inv_cancel_comm]
  -- The twist law on both kernels, with the factor `d = α (det g)⁻¹`.
  let d : ℂ := (α.val g.det : ℂ)⁻¹
  have h_left (h : G E t) : pairTheta W V γ α (modDatum W V 𝔪 Φ x) (g, h) =
      d * pairTheta W V γ 1 (modDatum W V 𝔪 Φ x) (g, h) := by
    simpa using pairTheta_twist W V γ 1 1 α (modDatum W V 𝔪 Φ x) g h
  have h_right (h : G E t') : pairTheta V' W α' γ (modDatum V' W 𝔪 Ψ v) (h, g) =
      d * pairTheta V' W γ γ (modDatum V' W 𝔪 Ψ v) (h, g) := by
    simpa [h_char', circleChar_inv_apply] using
      pairTheta_twist V' W γ γ α⁻¹ 1 (modDatum V' W 𝔪 Ψ v) h g
  calc thetaIntegral W V γ α (modDatum W V 𝔪 Φ x) g
      = d * thetaIntegral W V γ 1 (modDatum W V 𝔪 Φ x) g := by
        simp only [thetaIntegral, h_left, MeasureTheory.integral_const_mul]
    _ = c * ∫ h : G E t', pairTheta V' W α' γ (modDatum V' W 𝔪 Ψ v) (h, g) ∂V'.quotMeasure := by
        simp only [h_base Φ Ψ h_matched g, h_right, MeasureTheory.integral_const_mul, mul_left_comm]

end ExchangeTheorem

end New.Exchange

end
