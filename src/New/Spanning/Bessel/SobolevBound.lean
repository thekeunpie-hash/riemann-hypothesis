module

import TauCeti.Analysis.Matrix.L2OpNorm
public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.SqrtDeriv
public import New.Spanning.Bessel.Basic
import Lib.General.Analysis.GaussianIntegral
import Lib.General.Analysis.HolomorphicIntegrals
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.DiscreteSeries.Bessel.FrameFibre
import Lib.Adelic.Adeles.AdditiveCharacter
import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import Lib.DiscreteSeries.Bruhat.ComplexPlace
import Lib.DiscreteSeries.Haar.TotalMass
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Lib.DiscreteSeries.Bessel.SchurBound
import Lib.General.Analysis.PackingAndSobolev

section
section
/-!
# The Gram section γ_Z of the frame Gram matrix map on the unitary group G₁

For `γ` in the unitary group `New.Shape.G₁`, let `Z(γ) = New.realFrameGram γ = Fᴴ J₁ γ F` be the
matrix of products of the frame `F = (e₁, …, e_ϱ, z)` with its translate by `γ`. Let
`Ω = New.Shape.openCell` be the open set of invertible `Z` for which `ξ(Z) = invCorner Z`, the last
diagonal entry of `Z⁻¹`, has absolute value less than `1`. The file writes down an explicit matrix
`γ_Z` for `Z ∈ Ω` and proves that it is real differentiable with polynomial bounds.

## Main definitions and results

* `New.RealPlace.sectionMatrix`: a matrix in two variables `Z`, `W`, equal to `γ_Z` at `W = Zᴴ`.
* `New.RealPlace.differentiableAt_sectionMatrix`,
  `New.RealPlace.norm_sectionMatrix_le_and_norm_fderiv_le`: the matrix is real differentiable in
  `Z`, with polynomial bounds for it and its derivative.
  `New.RealPlace.IsBoundedInCell.norm_sectionMatrix_le` asks for bounds at the point `Z` only.
* `New.RealPlace.gramSection`: on `Ω` the matrix is an isometry of `J₁`
  (`New.RealPlace.sectionMatrix_isometry`), so it is the matrix of an
  element `γ_Z` of `G₁` (`New.RealPlace.coe_gramSection`).
* `New.RealPlace.measurable_gramSection`: the section is measurable.
* `New.RealPlace.realFrameGram_gramSection`: `Z(γ_Z) = Z` for `Z ∈ Ω`.
* `New.RealPlace.exists_eq_mul_gramSection_mul`: by Witt's theorem, `Z(γ) = Z ∈ Ω` determines `γ` up
  to factors `unipotentOf q * embedH k`, which fix the frame, on both sides.

Notions from other files:
* `New.Shape.BesselIndex`: the index set of the basis `e₁, …, e_ϱ`, `x_k` (`k ∈ κ`), `z`,
  `e*₁, …, e*_ϱ`; `k₀ = New.Shape.k₀` is a distinguished index in `κ`.
* `New.Shape.J₁`: the Gram matrix of the hermitian form defining `G₁`, with `ϱ` hyperbolic pairs
  `e_a, e*_a`, the identity on the span `X₀` of the `x_k` (`k ∈ κ`), and `h(z, z) = -1`.
* `New.Shape.frameCols`, `New.Shape.dualFrameCols`: the matrices `F` and `F'` whose columns are the
  basis vectors `(e₁, …, e_ϱ, z)` and `(e*₁, …, e*_ϱ, x_{k₀})`.
* `New.Shape.FrameMatrix`: the complex `(ϱ+1) × (ϱ+1)` matrices; `New.Shape.top` is the last index.
-/

@[expose] public section

noncomputable section

/-!
## The matrix γ_Z on Ω and bounds for it and its derivative

The matrices have a second argument `W`, and `γ_Z` is the value at `W = Zᴴ`. Norms of matrices are
`L²` operator norms.
-/

namespace New.RealPlace

open Matrix Function Fin Metric Real Complex Norms.L2Operator Shape

variable {𝔰 : Shape}

/-- For a (ϱ+1)×(ϱ+1) complex matrix Z, the last diagonal entry ξ(Z) of its inverse. -/
def invCorner (Z : 𝔰.FrameMatrix) : ℂ := Z⁻¹ 𝔰.top 𝔰.top

/-- The set Ω of invertible (ϱ+1)×(ϱ+1) complex matrices whose inverse has last diagonal entry of
absolute value less than 1. -/
def _root_.New.Shape.openCell : Set 𝔰.FrameMatrix :=
  {Z : 𝔰.FrameMatrix | det Z ≠ 0 ∧ ‖invCorner Z‖ < 1}

/-- For a (ϱ+1)×(ϱ+1) complex matrix Z, the real number ν(Z)² = 1 − |ξ|², ξ the last diagonal
entry of Z⁻¹. -/
def oneSubNormSqInvCorner (Z : 𝔰.FrameMatrix) : ℝ := 1 - ‖invCorner Z‖ ^ 2

/-- Z lies in Ω (`New.Shape.openCell`), and ‖Z⁻¹‖, ‖Z‖ (operator norms) and 1/ν(Z) are at most P,
where ν(Z)² = 1 − |ξ|², ξ the last diagonal entry of Z⁻¹. -/
structure IsBoundedInCell (Z : 𝔰.FrameMatrix) (P : ℝ) : Prop where
  /-- The matrix lies in Ω. -/
  mem_openCell : Z ∈ 𝔰.openCell
  /-- The inverse has operator norm at most P. -/
  norm_inv_le : ‖Z⁻¹‖ ≤ P
  /-- The matrix has operator norm at most P. -/
  norm_le : ‖Z‖ ≤ P
  /-- The number 1/ν(Z) is at most P. -/
  inv_sqrt_oneSubNormSqInvCorner_le : (√(oneSubNormSqInvCorner Z))⁻¹ ≤ P

/-- For a complex number x, the (ϱ+1)×(ϱ+1) diagonal matrix diag(1, …, 1, x). -/
def diagLast (x : ℂ) : 𝔰.FrameMatrix := diagonal (snoc 1 x)

/-- For matrices Z and W, the matrix Y(Z, W) with last row (0, …, 0, −1) and other entries
−(W⁻¹)_{a,last}(Z⁻¹)_{last,b}, halved unless b is last. For W = Zᴴ its columns are the coefficients
of the frame F = (e₁, …, e_ϱ, z) in a family F^∨(Z) that is dual to F and has the Gram matrix −ζᴴζ,
with ζ the last row of Z⁻¹. -/
def sectionCoeff (Z W : 𝔰.FrameMatrix) : 𝔰.FrameMatrix :=
  diagLast (𝔰 := 𝔰) 0 - 1 -
    diagLast (𝔰 := 𝔰) 0 * W⁻¹ * (1 - diagLast (𝔰 := 𝔰) 2⁻¹) * Z⁻¹ * diagLast (𝔰 := 𝔰) 2

/-- The matrix (F·Y + F'·diag(1, …, 1, s))·Z, with F the frame, F' = (e*₁, …, e*_ϱ, x_{k₀}),
Y = `New.RealPlace.sectionCoeff Z W` and s = (1 − ξ(Z) ξ(W))^{1/2}, ξ = `invCorner`. For Z in Ω
and W = Zᴴ the first factor is the family F^∨(Z) dual to F, and the columns of F^∨(Z)·Z are the
images of the frame under γ_Z. The rows are indexed by the basis e_a, x_i (i in κ), z, e*_a
(`BesselIndex`), and k₀ = `𝔰.k₀` is the distinguished index in κ. -/
def sectionFrame (Z W : 𝔰.FrameMatrix) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
  (𝔰.frameCols * sectionCoeff Z W +
      𝔰.dualFrameCols * diagLast (𝔰 := 𝔰) (1 - invCorner Z * invCorner W).sqrt) * Z

/-- The matrix 1 − FFᴴ − F'F'ᴴ + SFᴴ + (FW⁻¹ − S·Y(W, Z))·diag(1, …, 1, s⁻¹)·F'ᴴ, with F the
frame, F' = (e*₁, …, e*_ϱ, x_{k₀}), S = `New.RealPlace.sectionFrame Z W`,
Y = `New.RealPlace.sectionCoeff` and s = (1 − ξ(Z) ξ(W))^{1/2}, ξ = `invCorner`. For Z in Ω and
W = Zᴴ it is the matrix of γ_Z, and s = ν(Z). In that case it sends F to F^∨(Z)·Z and F^∨(Zᴴ) to
F·(Zᴴ)⁻¹, and it fixes the x_i with i ≠ k₀; here F^∨(Z) = F·Y(Z, Zᴴ) + F'·diag(1, …, 1, s) is dual
to the frame. Rows and columns are indexed by the basis e_a, x_i (i in κ), z, e*_a (`BesselIndex`),
and k₀ = `𝔰.k₀` is the distinguished index in κ. -/
def sectionMatrix (Z W : 𝔰.FrameMatrix) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ :=
  1 + (sectionFrame Z W - 𝔰.frameCols) * 𝔰.frameColsᴴ +
    ((𝔰.frameCols * W⁻¹ - sectionFrame Z W * sectionCoeff W Z) *
      diagLast (𝔰 := 𝔰) (1 - invCorner Z * invCorner W).sqrt⁻¹ - 𝔰.dualFrameCols) * 𝔰.dualFrameColsᴴ

/-! ### The open set `Ω` -/

lemma mem_openCell {Z : 𝔰.FrameMatrix} : Z ∈ 𝔰.openCell ↔ det Z ≠ 0 ∧ ‖invCorner Z‖ < 1 := Iff.rfl

lemma invCorner_conjTranspose (Z : 𝔰.FrameMatrix) : invCorner Zᴴ = star (invCorner Z) := by
  simp [invCorner, ← conjTranspose_nonsing_inv]

lemma conjTranspose_mem_openCell_iff {Z : 𝔰.FrameMatrix} : Zᴴ ∈ 𝔰.openCell ↔ Z ∈ 𝔰.openCell := by
  simp [mem_openCell, invCorner_conjTranspose]

/-- For invertible `Z`, the number `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`, with `D_ϱ` the
leading minor of order `ϱ`) equals `|det Z|² ν(Z)²`. -/
lemma gramDiscReal_eq_norm_det_sq_mul {Z : 𝔰.FrameMatrix} (hdet : det Z ≠ 0) :
    gramDiscReal Z = ‖det Z‖ ^ 2 * oneSubNormSqInvCorner Z := by
  have h_minor : leadingMinor Z 𝔰.top.castSucc = (Z.submatrix castSucc castSucc).det := rfl
  -- Cramer's rule
  have h_corner : invCorner Z = (Z.submatrix castSucc castSucc).det / det Z := by
    simp [invCorner, Z.inv_def, adjugate_fin_succ_eq_det_submatrix, div_eq_inv_mul]
  simp [gramDiscReal, frameDisc, oneSubNormSqInvCorner, h_minor, h_corner, mul_conj', ← ofReal_pow,
    field]

/-- The set Ω (`openCell`: `Z` invertible and the last diagonal entry of `Z⁻¹` of absolute value
less than `1`) is the set where `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`) is positive, with `D_ϱ`
the leading minor of order `ϱ`. -/
lemma mem_openCell_iff {Z : 𝔰.FrameMatrix} : Z ∈ 𝔰.openCell ↔ 0 < gramDiscReal Z := by
  by_cases hdet : Z.det = 0
  · simp [mem_openCell, gramDiscReal, frameDisc, hdet, mul_conj', ← ofReal_pow]
  · rw [gramDiscReal_eq_norm_det_sq_mul hdet, mul_pos_iff_of_pos_left (by positivity)]
    simp [mem_openCell, oneSubNormSqInvCorner, hdet]

/-- The number `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`, with `D_ϱ` the leading minor of order
`ϱ`) is a continuous function of `Z`. -/
@[fun_prop]
lemma continuous_gramDiscReal : Continuous (gramDiscReal : 𝔰.FrameMatrix → ℝ) := by
  fun_prop [gramDiscReal, frameDisc, leadingMinor]

lemma isOpen_openCell : IsOpen 𝔰.openCell := by
  rw [show 𝔰.openCell = gramDiscReal ⁻¹' Set.Ioi 0 from Set.ext fun _ ↦ mem_openCell_iff]
  exact isOpen_Ioi.preimage continuous_gramDiscReal

lemma oneSubNormSqInvCorner_pos {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    0 < oneSubNormSqInvCorner Z := by
  simpa [oneSubNormSqInvCorner] using (mem_openCell.1 hZ).2

/-- For `Z` in Ω (`openCell`) the complex root `(1 - ξ(Z) ξ(Zᴴ)) ^ (1 / 2)` is the real square root
`ν(Z)` of `1 - |ξ(Z)|²`, where `ξ(Z) = invCorner Z` is the last diagonal entry of `Z⁻¹`. -/
@[simp]
lemma sqrt_eq_sqrt_oneSubNormSqInvCorner {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    (1 - invCorner Z * invCorner Zᴴ).sqrt = √(oneSubNormSqInvCorner Z) := by
  have h_eq : 1 - invCorner Z * invCorner Zᴴ = oneSubNormSqInvCorner Z := by
    simp [invCorner_conjTranspose, oneSubNormSqInvCorner, mul_conj']
  simp [h_eq, Complex.sqrt, sqrt_eq_rpow, ofReal_cpow (oneSubNormSqInvCorner_pos hZ).le]

/-! ### Differentiability -/

/-- For `Z`, `W` in Ω the number `1 - ξ(Z) ξ(W)` lies in the slit plane. Here `ξ` is `invCorner`,
the last diagonal entry of the inverse. -/
lemma one_sub_invCorner_mul_mem_slitPlane {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) : 1 - invCorner Z * invCorner W ∈ slitPlane := by
  rw [sub_eq_add_neg]
  refine mem_slitPlane_of_norm_lt_one ?_
  grw [norm_neg, norm_mul, (mem_openCell.1 hW).2.le, mul_one, (mem_openCell.1 hZ).2]

lemma differentiable_diagLast_apply (i j : Fin (𝔰.ϱ + 1)) :
    Differentiable ℂ fun x : ℂ ↦ diagLast (𝔰 := 𝔰) x i j := by
  revert i j
  simp [diagonal, eq_comm, diagLast, forall_fin_succ']

/-- The matrix `sectionMatrix Z W` is holomorphic in `(Z, W)` on `Ω × Ω`, where `Ω` is
`𝔰.openCell`. -/
lemma differentiableAt_sectionMatrix_uncurry {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) : DifferentiableAt ℂ (uncurry sectionMatrix) (Z, W) := by
  -- Each entry is a polynomial in the entries of `Z`, `Z⁻¹`, `W⁻¹`, `diagLast s`, `diagLast s⁻¹`,
  -- where `s` is the square root of `1 - invCorner Z * invCorner W`.
  have hZ_unit : IsUnit Z := by simp [isUnit_iff_isUnit_det, (mem_openCell.1 hZ).1]
  have hW_unit : IsUnit W := by simp [isUnit_iff_isUnit_det, (mem_openCell.1 hW).1]
  have h_slit := one_sub_invCorner_mul_mem_slitPlane hZ hW
  have hs_ne : (1 - invCorner Z * invCorner W).sqrt ≠ 0 := by
    simp [Complex.sqrt, slitPlane_ne_zero h_slit]
  have h_diag := differentiable_diagLast_apply (𝔰 := 𝔰)
  refine differentiableAt_pi.2 fun i ↦ differentiableAt_pi.2 fun j ↦ ?_
  simp only [uncurry_def, sectionMatrix, sectionFrame, sectionCoeff, invCorner,
    nonsing_inv_eq_ringInverse] at h_slit hs_ne ⊢
  dsimp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply]
  fun_prop (disch := assumption)

/-- The matrix `sectionMatrix Y Yᴴ` of the section γ_Y (`gramSection`) is a real differentiable
function of `Y` at every point `Z` of Ω (`openCell`). -/
lemma differentiableAt_sectionMatrix {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    DifferentiableAt ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z := by
  -- Restrict the holomorphic map of two variables to the real subspace `W = Zᴴ`.
  exact ((differentiableAt_sectionMatrix_uncurry hZ
    (conjTranspose_mem_openCell_iff.2 hZ)).restrictScalars ℝ).comp Z
    (f := fun Y : 𝔰.FrameMatrix ↦ (Y, star Y)) (by fun_prop)

/-! ### Bounds -/

lemma norm_complex_sqrt_eq_sqrt_norm (z : ℂ) : ‖z.sqrt‖ = √‖z‖ := by
  simp [norm_cpow_of_imp, sqrt_eq_rpow, Complex.sqrt]

lemma norm_diagLast_le (s : ℂ) : ‖diagLast (𝔰 := 𝔰) s‖ ≤ 1 + ‖s‖ := by
  simp [pi_norm_le_iff_of_nonempty, diagLast, forall_fin_succ']

/-- If `‖Z⁻¹‖ ≤ P` and `‖W⁻¹‖ ≤ P` (operator norms), then `‖sectionCoeff Z W‖ ≤ 2 + 8 P²`. Here
`sectionCoeff Z W` is the matrix with last row `(0, …, 0, -1)` and other entries
`-(W⁻¹)_{a,last} (Z⁻¹)_{last,b}`, halved unless `b` is last. -/
lemma norm_sectionCoeff_le {Z W : 𝔰.FrameMatrix} {P : ℝ} (hZ : ‖Z⁻¹‖ ≤ P) (hW : ‖W⁻¹‖ ≤ P) :
    ‖sectionCoeff Z W‖ ≤ 2 + 8 * P ^ 2 := by
  have hP : 0 ≤ P := (norm_nonneg _).trans hZ
  have h_head : ‖(diagLast 0 - 1 : 𝔰.FrameMatrix)‖ ≤ 2 := by
    grw [norm_sub_le, norm_diagLast_le]
    norm_num
  have h_half : ‖(1 - diagLast 2⁻¹ : 𝔰.FrameMatrix)‖ ≤ 5 / 2 := by
    grw [norm_sub_le, norm_diagLast_le]
    norm_num
  calc _ ≤ 2 + (1 + ‖(0 : ℂ)‖) * P * (5 / 2) * P * (1 + ‖(2 : ℂ)‖) := by
        grw [sectionCoeff, norm_sub_le, h_head, norm_mul₃_le, norm_mul₃_le, hW, h_half, hZ,
          norm_diagLast_le, norm_diagLast_le]
    _ = 2 + 15 / 2 * P ^ 2 := by
        simp only [norm_zero, Complex.norm_ofNat]
        ring
    _ ≤ 2 + 8 * P ^ 2 := by linarith [sq_nonneg P]

/-- For `Z`, `W` in Ω the root `s = (1 - ξ(Z) ξ(W)) ^ (1 / 2)` satisfies `|s| ≤ 2`.
Here `ξ` is `invCorner`, the last diagonal entry of the inverse. -/
lemma norm_sqrt_one_sub_invCorner_mul_le {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) : ‖(1 - invCorner Z * invCorner W).sqrt‖ ≤ 2 := by
  rw [norm_complex_sqrt_eq_sqrt_norm, sqrt_le_left zero_le_two]
  grw [norm_sub_le, norm_mul, (mem_openCell.1 hZ).2, (mem_openCell.1 hW).2]
  norm_num

/-- For `Z`, `W` in Ω, the root `s = (1 - ξ(Z) ξ(W)) ^ (1 / 2)` satisfies `|s⁻¹| ≤ 2 / ν(Z)`. -/
lemma norm_inv_sqrt_one_sub_invCorner_mul_le {Z W : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell)
    (hW : W ∈ 𝔰.openCell) :
    ‖(1 - invCorner Z * invCorner W).sqrt⁻¹‖ ≤ 2 * (√(oneSubNormSqInvCorner Z))⁻¹ := by
  have h_lower : oneSubNormSqInvCorner Z / 2 ^ 2 ≤ ‖1 - invCorner Z * invCorner W‖ := by
    grw [← norm_sub_norm_le, norm_mul, (mem_openCell.1 hW).2, norm_one, oneSubNormSqInvCorner]
    nlinarith only [(mem_openCell.1 hZ).2]
  have hν_pos : 0 < oneSubNormSqInvCorner Z := oneSubNormSqInvCorner_pos hZ
  grw [norm_inv, norm_complex_sqrt_eq_sqrt_norm, ← h_lower]
  simp [div_eq_mul_inv]

/-- Let `P ≥ 8`. Let Ω = `𝔰.openCell` be the matrices that are invertible and whose inverse has last
diagonal entry of absolute value below 1. Let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at
most `P` (`IsBoundedInCell`). Let `W` lie in Ω with `‖W⁻¹‖ ≤ P`. Then `sectionMatrix Z W` has
operator norm at most `P ^ 12`. -/
lemma norm_sectionMatrix_le_pow {Z W : 𝔰.FrameMatrix} {P : ℝ} (hP : 8 ≤ P)
    (hZ : IsBoundedInCell Z P) (hW : W ∈ 𝔰.openCell) (hW_inv : ‖W⁻¹‖ ≤ P) :
    ‖sectionMatrix Z W‖ ≤ P ^ 12 := by
  have hF : ‖𝔰.frameCols‖ ≤ 1 := norm_inclMatrix_le_one (by simp [Injective, forall_fin_succ'])
  have hF' : ‖𝔰.dualFrameCols‖ ≤ 1 := norm_inclMatrix_le_one (by simp [Injective, forall_fin_succ'])
  set s : ℂ := (1 - invCorner Z * invCorner W).sqrt
  have hs : ‖s‖ ≤ 2 := norm_sqrt_one_sub_invCorner_mul_le hZ.mem_openCell hW
  have hs_inv : ‖s⁻¹‖ ≤ 2 * P := (norm_inv_sqrt_one_sub_invCorner_mul_le hZ.mem_openCell hW).trans
    (by grw [hZ.inv_sqrt_oneSubNormSqInvCorner_le])
  have h_frame : ‖sectionFrame Z W‖ ≤ (5 + 8 * P ^ 2) * P := by
    grw [sectionFrame, l2_opNorm_mul, norm_add_le, l2_opNorm_mul, l2_opNorm_mul, hF, hF',
      norm_sectionCoeff_le hZ.norm_inv_le hW_inv, norm_diagLast_le, hs, hZ.norm_le]
    linarith
  have h_dual : ‖(𝔰.frameCols * W⁻¹ - sectionFrame Z W * sectionCoeff W Z) *
      diagLast (𝔰 := 𝔰) s⁻¹‖ ≤ (P + (5 + 8 * P ^ 2) * P * (2 + 8 * P ^ 2)) * (1 + 2 * P) := by
    grw [l2_opNorm_mul, norm_sub_le, l2_opNorm_mul, l2_opNorm_mul, h_frame, hF,
      norm_sectionCoeff_le hW_inv hZ.norm_inv_le, hW_inv, norm_diagLast_le, hs_inv, one_mul]
  calc _ ≤ 3 + (5 + 8 * P ^ 2) * P + (P + (5 + 8 * P ^ 2) * P * (2 + 8 * P ^ 2)) * (1 + 2 * P) := by
        grw [sectionMatrix, norm_add_le, norm_add_le, l2_opNorm_mul, l2_opNorm_mul, norm_sub_le,
          norm_sub_le, h_dual, l2_opNorm_conjTranspose, l2_opNorm_conjTranspose, h_frame, hF, hF,
          hF', hF', norm_one]
        linarith
    _ ≤ P ^ 12 := by
      -- In `t = P - 8 ≥ 0` the difference has nonnegative coefficients.
      obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ 8 + t = P := exists_nonneg_add_of_le hP
      rw [← sub_nonneg]
      ring_nf
      positivity

/-- Let `P ≥ 8` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `P`
(`IsBoundedInCell`). Then the matrix `sectionMatrix Z Zᴴ` of γ_Z has operator norm at most
`P ^ 12`. -/
lemma IsBoundedInCell.norm_sectionMatrix_le_pow {Z : 𝔰.FrameMatrix} {P : ℝ}
    (hZ : IsBoundedInCell Z P) (hP : 8 ≤ P) : ‖sectionMatrix Z Zᴴ‖ ≤ P ^ 12 := by
  refine RealPlace.norm_sectionMatrix_le_pow hP hZ
    (conjTranspose_mem_openCell_iff.2 hZ.mem_openCell) ?_
  simpa [← conjTranspose_nonsing_inv, l2_opNorm_conjTranspose] using hZ.norm_inv_le

/-- Let r > 0 and P ≥ 8, and let every y within r of Z lie in Ω with ‖y⁻¹‖, ‖y‖ and 1/ν(y) at most P
(`IsBoundedInCell`). Then the real derivative at Z of the matrix `sectionMatrix Y Yᴴ` of γ_Y has
norm at most 2P¹²/r. -/
lemma norm_fderiv_sectionMatrix_le {Z : 𝔰.FrameMatrix} {P r : ℝ} (hr : 0 < r) (hP : 8 ≤ P)
    (hball : ∀ y ∈ ball Z r, IsBoundedInCell y P) :
    ‖fderiv ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z‖ ≤ 2 * P ^ 12 / r := by
  -- With an independent variable `w` for `xᴴ` the matrix is holomorphic in `(x, w)` and bounded by
  -- `P ^ 12` on the ball about `(Z, Zᴴ)`; the Schwarz lemma then bounds the derivative.
  have h_pair : ∀ p ∈ ball (Z, Zᴴ) r,
      DifferentiableAt ℂ (uncurry sectionMatrix) p ∧ ‖uncurry sectionMatrix p‖ ≤ P ^ 12 := by
    rintro ⟨x, w⟩ hp
    obtain ⟨hx, hw⟩ : x ∈ ball Z r ∧ wᴴ ∈ ball Z r := by
      -- Taking adjoints preserves the distance from `w` to `Zᴴ`.
      simpa [dist_eq_norm, ← l2_opNorm_conjTranspose (w - Zᴴ)] using hp
    have hw_mem : w ∈ 𝔰.openCell := conjTranspose_mem_openCell_iff.1 (hball wᴴ hw).mem_openCell
    have hw_inv : ‖w⁻¹‖ ≤ P := by
      simpa [← conjTranspose_nonsing_inv, l2_opNorm_conjTranspose] using (hball wᴴ hw).norm_inv_le
    exact ⟨differentiableAt_sectionMatrix_uncurry (hball x hx).mem_openCell hw_mem,
      norm_sectionMatrix_le_pow hP (hball x hx) hw_mem hw_inv⟩
  choose h_hol h_bound using h_pair
  refine norm_fderiv_le_of_lip' ℝ (by positivity) ?_
  filter_upwards [ball_mem_nhds Z hr] with y hy
  change ‖sectionMatrix y yᴴ - sectionMatrix Z Zᴴ‖ ≤ 2 * P ^ 12 / r * ‖y - Z‖
  have hy_pair : (y, yᴴ) ∈ ball (Z, Zᴴ) r := by
    simpa [← conjTranspose_sub, dist_eq_norm, l2_opNorm_conjTranspose] using hy
  simpa [← conjTranspose_sub, l2_opNorm_conjTranspose] using norm_sub_le_of_holomorphic_bdd
    (fun p hp ↦ (h_hol p hp).differentiableWithinAt) h_bound hy_pair

/-- Let `r > 0` and `P ≥ 8`. Suppose every `y` in `ball Z r` satisfies `IsBoundedInCell y P`: `y`
lies in Ω, meaning `y` is invertible and the last diagonal entry ξ(y) of y⁻¹ has modulus < 1, and
‖y⁻¹‖, ‖y‖ and 1/ν(y) are at most P. Then `sectionMatrix Z Zᴴ`, the matrix of the section γ_Z ∈ G₁,
has operator norm at most P¹². The real derivative of `Y ↦ sectionMatrix Y Yᴴ` at `Z` has norm at
most 2P¹²/r. -/
lemma norm_sectionMatrix_le_and_norm_fderiv_le {Z : 𝔰.FrameMatrix} {P r : ℝ} (hr : 0 < r)
    (hP : 8 ≤ P) (hball : ∀ y ∈ ball Z r, IsBoundedInCell y P) :
    ‖sectionMatrix Z Zᴴ‖ ≤ P ^ 12 ∧
      ‖fderiv ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z‖ ≤ 2 * P ^ 12 / r :=
  ⟨(hball Z (mem_ball_self hr)).norm_sectionMatrix_le_pow hP,
    norm_fderiv_sectionMatrix_le hr hP hball⟩

section Perturbation

/-- Let `T ≥ 4` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T`
(`IsBoundedInCell`). Then a matrix `Y` within `T ^ (-6)` of `Z` is invertible, `‖Y⁻¹‖ ≤ 2 T`, and
`Y⁻¹` is within `2 T ^ (-4)` of `Z⁻¹`. -/
lemma IsBoundedInCell.isUnit_det_and_norm_inv_le {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    IsUnit Y.det ∧ ‖Y⁻¹‖ ≤ 2 * T ∧ ‖Y⁻¹ - Z⁻¹‖ ≤ 2 * T⁻¹ ^ 4 := by
  -- `Y = Z (1 + Z⁻¹ (Y - Z))` is invertible, and `Y⁻¹ - Z⁻¹ = Y⁻¹ (Z - Y) Z⁻¹` is small.
  rw [mem_ball_iff_norm] at hY
  have hZ_unit : IsUnit Z.det := (RealPlace.mem_openCell.1 hZ.mem_openCell).1.isUnit
  have h_small : T * (T ^ 6)⁻¹ ≤ 2⁻¹ := by
    grw [show T * (T ^ 6)⁻¹ = (T ^ 5)⁻¹ by field, ← hT]
    norm_num
  have hY_unit : IsUnit Y.det := by
    have h_lt : ‖-(Z⁻¹ * (Y - Z))‖ < 1 := by
      grw [norm_neg, norm_mul_le, hZ.norm_inv_le, hY, h_small]
      norm_num
    rw [show Y = Z * (1 - -(Z⁻¹ * (Y - Z))) by
      simp [Matrix.mul_add, mul_nonsing_inv_cancel_left _ _ hZ_unit], det_mul]
    exact hZ_unit.mul ((isUnit_iff_isUnit_det _).1 (Units.oneSub _ h_lt).isUnit)
  have h_diff : ‖Y⁻¹ - Z⁻¹‖ ≤ ‖Y⁻¹‖ * (T * (T ^ 6)⁻¹) := by
    have h_eq : Y⁻¹ - Z⁻¹ = Y⁻¹ * -((Y - Z) * Z⁻¹) := by
      simp [sub_mul, mul_sub, mul_nonsing_inv _ hZ_unit, nonsing_inv_mul_cancel_left _ _ hY_unit]
    grw [h_eq, norm_mul_le, norm_neg, norm_mul_le, hY, hZ.norm_inv_le, mul_comm T]
  have hY_inv : ‖Y⁻¹‖ ≤ 2 * T := by
    grw [h_small] at h_diff
    linarith [norm_le_insert' Y⁻¹ Z⁻¹, hZ.norm_inv_le]
  refine ⟨hY_unit, hY_inv, ?_⟩
  grw [h_diff, hY_inv, show 2 * T * (T * (T ^ 6)⁻¹) = 2 * T⁻¹ ^ 4 by field]

/-- If `T > 0` and `Z` lies in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T` (`IsBoundedInCell`),
then `ν(Z)² = oneSubNormSqInvCorner Z` is at least `T ^ (-2)`. -/
lemma IsBoundedInCell.inv_sq_le_oneSubNormSqInvCorner {Z : 𝔰.FrameMatrix} {T : ℝ}
    (hZ : IsBoundedInCell Z T) (hT : 0 < T) : T⁻¹ ^ 2 ≤ oneSubNormSqInvCorner Z :=
  (le_sqrt' (by positivity)).1
    (inv_le_of_inv_le₀ (sqrt_pos.2 (oneSubNormSqInvCorner_pos hZ.mem_openCell))
      hZ.inv_sqrt_oneSubNormSqInvCorner_le)

/-- Write `ν(Z)² = 1 - |ξ(Z)|²` (`oneSubNormSqInvCorner`), with `ξ(Z)` the last diagonal entry of
`Z⁻¹`. Let `T ≥ 4` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T`
(`IsBoundedInCell`). Then `(1 - 8 / T ^ 2) ν(Z)² ≤ ν(Y)²` for `Y` within `T ^ (-6)` of `Z`. -/
lemma IsBoundedInCell.mul_oneSubNormSqInvCorner_le {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    (1 - 8 * T⁻¹ ^ 2) * oneSubNormSqInvCorner Z ≤ oneSubNormSqInvCorner Y := by
  -- The corner entry moves by at most `2 / T ^ 4`, while `oneSubNormSqInvCorner Z ≥ 1 / T ^ 2`.
  obtain ⟨-, -, h_diff⟩ := hZ.isUnit_det_and_norm_inv_le hT hY
  have h_corner : ‖invCorner Y‖ ≤ ‖invCorner Z‖ + 2 * T⁻¹ ^ 4 := by
    grw [norm_le_insert' (invCorner Y) (invCorner Z), ← h_diff]
    exact add_le_add_right (norm_apply_le_l2_opNorm (Y⁻¹ - Z⁻¹) 𝔰.top 𝔰.top) _
  have h_sq : ‖invCorner Y‖ ^ 2 ≤ ‖invCorner Z‖ ^ 2 + 8 * T⁻¹ ^ 4 := by
    have h_pow_le : T⁻¹ ^ 4 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
    grw [h_corner]
    nlinarith [(RealPlace.mem_openCell.1 hZ.mem_openCell).2, show 0 ≤ T⁻¹ ^ 4 by positivity]
  have h_lower : T⁻¹ ^ 2 ≤ oneSubNormSqInvCorner Z :=
    hZ.inv_sq_le_oneSubNormSqInvCorner (by linarith)
  simp only [oneSubNormSqInvCorner] at h_lower ⊢
  nlinarith

/-- Let `T ≥ 4` and let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T`
(`IsBoundedInCell`). Then every `Y` within `T ^ (-6)` of `Z` lies in Ω and satisfies the same bounds
with `2 T` in place of `T`. -/
lemma IsBoundedInCell.of_mem_ball {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    IsBoundedInCell Y (2 * T) := by
  obtain ⟨hY_unit, hY_inv, -⟩ := hZ.isUnit_det_and_norm_inv_le hT hY
  have hνY_lower : ((2 * T)⁻¹) ^ 2 ≤ oneSubNormSqInvCorner Y := by
    have h_inv : T⁻¹ ^ 2 ≤ 4⁻¹ ^ 2 := by gcongr
    calc ((2 * T)⁻¹) ^ 2 = 4⁻¹ * T⁻¹ ^ 2 := by ring
      _ ≤ (1 - 8 * T⁻¹ ^ 2) * oneSubNormSqInvCorner Z := by
        nlinarith [hZ.inv_sq_le_oneSubNormSqInvCorner (by linarith), sq_nonneg T⁻¹]
      _ ≤ oneSubNormSqInvCorner Y := hZ.mul_oneSubNormSqInvCorner_le hT hY
  have h_norm : ‖Y‖ ≤ 2 * T := by
    have h_radius : (T ^ 6)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    linarith [norm_le_insert' Y Z, hZ.norm_le, mem_ball_iff_norm.1 hY]
  have hνY_pos : 0 < oneSubNormSqInvCorner Y := hνY_lower.trans_lt' (by positivity)
  exact ⟨⟨hY_unit.ne_zero, by simpa [oneSubNormSqInvCorner] using hνY_pos⟩, hY_inv, h_norm,
    inv_le_of_inv_le₀ (by positivity) ((le_sqrt' (by positivity)).2 hνY_lower)⟩

/-- Let `Z` lie in Ω with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T` (`IsBoundedInCell`), where
`ν(Z)² = 1 - |ξ(Z)|²` and `ξ(Z)` is the last diagonal entry of `Z⁻¹`. Let `T` be at least `8` and
at least the number `𝔰.n = ϱ + 1` of rows of `Z`. Then `𝗀(Z) / 2 ≤ 𝗀(Y)` for `Y` within `T ^ (-6)`
of `Z`, where `𝗀(Z) = |det Z|² - |D_ϱ|²` (`gramDiscReal`, with `D_ϱ` the leading minor of order `ϱ`)
equals `|det Z|² ν(Z)²` for invertible `Z`. -/
lemma IsBoundedInCell.gramDiscReal_div_two_le {Z : 𝔰.FrameMatrix} {T : ℝ} {Y : 𝔰.FrameMatrix}
    (hZ : IsBoundedInCell Z T) (hT : 8 ≤ T) (hn : 𝔰.n ≤ T) (hY : Y ∈ ball Z (T ^ 6)⁻¹) :
    gramDiscReal Z / 2 ≤ gramDiscReal Y := by
  -- `Z = (1 - (Y - Z) Y⁻¹) Y` compares the determinants; `ν²` shrinks by at most the factor
  -- `1 - 8 / T ^ 2`.
  obtain ⟨hY_unit, hY_inv, -⟩ := hZ.isUnit_det_and_norm_inv_le (by linarith) hY
  let x : ℝ := (T ^ 6)⁻¹ * (2 * T)
  have h_norm : ‖1 - (Y - Z) * Y⁻¹‖ ≤ x + 1 := by
    grw [norm_sub_le, norm_one, norm_mul_le, mem_ball_iff_norm.1 hY, hY_inv, add_comm]
  have h_small : 𝔰.n * x ≤ 1 / 9 := by
    grw [hn, show T * x = 2 / T ^ 4 by simp only [x]; field, ← hT]
    norm_num
  have h_pow : (x + 1) ^ 𝔰.n ≤ 9 / 8 :=
    calc (x + 1) ^ 𝔰.n ≤ Real.exp x ^ 𝔰.n := by grw [Real.add_one_le_exp x]
      _ ≤ Real.exp (1 / 9) := by grw [← Real.exp_natCast_mul, h_small]
      _ ≤ 1 / (1 - 1 / 9) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 9 / 8 := by norm_num
  have h_det : ‖Z.det‖ ≤ 9 / 8 * ‖Y.det‖ := by
    have h_factor : Z = (1 - (Y - Z) * Y⁻¹) * Y := by
      simp [Matrix.sub_mul, nonsing_inv_mul_cancel_right _ _ hY_unit]
    conv_lhs => rw [h_factor]
    grw [det_mul, norm_mul, norm_det_le_norm_pow, h_norm, Fintype.card_fin, h_pow]
  have hνZ_pos : 0 < oneSubNormSqInvCorner Z := oneSubNormSqInvCorner_pos hZ.mem_openCell
  have hν_ratio : 7 / 8 * oneSubNormSqInvCorner Z ≤ oneSubNormSqInvCorner Y := by
    have h_inv : T⁻¹ ^ 2 ≤ 8⁻¹ ^ 2 := by gcongr
    nlinarith [hZ.mul_oneSubNormSqInvCorner_le (by linarith) hY]
  calc gramDiscReal Z / 2 ≤ (9 / 8 * ‖Y.det‖) ^ 2 * oneSubNormSqInvCorner Z / 2 := by
        grw [gramDiscReal_eq_norm_det_sq_mul (RealPlace.mem_openCell.1 hZ.mem_openCell).1, h_det]
    _ ≤ ‖Y.det‖ ^ 2 * (7 / 8 * oneSubNormSqInvCorner Z) := by
        linarith [mul_nonneg (sq_nonneg ‖Y.det‖) hνZ_pos.le]
    _ ≤ gramDiscReal Y := by grw [hν_ratio, gramDiscReal_eq_norm_det_sq_mul hY_unit.ne_zero]

end Perturbation

/-- Let `T ≥ 4` and let `𝔰` be a shape (ϱ, κ, k₀). Let `Z` be a complex `(ϱ+1) × (ϱ+1)` matrix in Ω,
with `‖Z⁻¹‖`, `‖Z‖` and `1 / ν(Z)` at most `T` (`IsBoundedInCell`). Then `sectionMatrix Z Zᴴ` has
operator norm at most `T ^ 18`, and its real derivative in `Z` has norm at most `T ^ 25`. -/
theorem IsBoundedInCell.norm_sectionMatrix_le {Z : 𝔰.FrameMatrix} {T : ℝ}
    (hZ : IsBoundedInCell Z T) (hT : 4 ≤ T) :
    ‖sectionMatrix Z Zᴴ‖ ≤ T ^ 18 ∧
      ‖fderiv ℝ (fun Y : 𝔰.FrameMatrix ↦ sectionMatrix Y Yᴴ) Z‖ ≤ T ^ 25 := by
  obtain ⟨h_value, h_deriv⟩ :=
    RealPlace.norm_sectionMatrix_le_and_norm_fderiv_le (by positivity) (by linarith) fun Y hY ↦
      hZ.of_mem_ball hT hY
  have h_two : (2 * T) ^ 12 ≤ T ^ 18 :=
    calc (2 * T) ^ 12 = 4 ^ 6 * T ^ 12 := by ring
      _ ≤ T ^ 6 * T ^ 12 := by gcongr
      _ = T ^ 18 := by ring
  refine ⟨h_value.trans h_two, h_deriv.trans ?_⟩
  calc 2 * (2 * T) ^ 12 / (T ^ 6)⁻¹ ≤ T * T ^ 18 * T ^ 6 := by
        grw [div_inv_eq_mul, h_two, show 2 ≤ T by linarith]
    _ = T ^ 25 := by ring

/-! ## The Gram section and double cosets over the open cell -/

open IsHermitianInvolution

/-- The matrix `sectionMatrix Z Zᴴ` sends the frame `F = (e₁, …, e_ϱ, z)` to the columns of
`sectionFrame Z Zᴴ = (F Y + F' diag(1, …, 1, s)) Z`. Here `F' = (e*₁, …, e*_ϱ, x_{k₀})`,
`Y = sectionCoeff Z Zᴴ` and `s = (1 - ξ(Z) ξ(Zᴴ)) ^ (1 / 2)` with `ξ = invCorner`. -/
theorem sectionMatrix_mul_frameCols {Z : 𝔰.FrameMatrix} :
    sectionMatrix Z Zᴴ * 𝔰.frameCols = sectionFrame Z Zᴴ := by
  simp [sectionMatrix, inclMatrix, Matrix.sub_mul, diagLast, Matrix.mul_assoc, Matrix.add_mul,
    ← ext_iff, Matrix.one_apply, Matrix.mul_apply, sum_univ_castSucc, diagonal_apply, Fin.ne_of_gt,
    forall_fin_succ']

/-- The Gram matrix of the frame `F = (e₁, …, e_ϱ, z)` for the form `𝔰.J₁` is
`diagLast 0 - 1 = diag(0, …, 0, -1)`. -/
lemma frameCols_gram_frameCols : 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols = diagLast 0 - 1 := by
  rw [conjTranspose_inclMatrix_mul_mul_inclMatrix]
  simp [splitGram, middleGram, diagLast, ← ext_iff, Matrix.one_apply, diagonal_apply,
    forall_fin_succ', Fin.ne_of_gt]

/-- The products for the form `𝔰.J₁` of the columns of `𝔰.frameCols` = (e₁, …, e_ϱ, z) with those of
`𝔰.dualFrameCols` = (e*₁, …, e*_ϱ, x_{k₀}) form the matrix `diagLast 0 = diag(1, …, 1, 0)`, that is,
`𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualFrameCols = diagLast 0`. -/
lemma frameCols_gram_dualFrameCols : 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualFrameCols = diagLast 0 := by
  rw [conjTranspose_inclMatrix_mul_mul_inclMatrix]
  simp [splitGram, middleGram, diagLast, ← ext_iff, Matrix.one_apply, diagonal_apply,
    forall_fin_succ', Fin.ne_of_gt]

/-- Let `Z` be any complex `(ϱ+1) × (ϱ+1)` matrix, not necessarily in the set Ω, and let
`M = sectionMatrix Z Zᴴ`. Then `Fᴴ J₁ M F = Z`. -/
theorem frameCols_gram_sectionMatrix {Z : 𝔰.FrameMatrix} :
    𝔰.frameColsᴴ * 𝔰.J₁ * (sectionMatrix Z Zᴴ * 𝔰.frameCols) = Z := by
  -- The factor `diagLast 0 - 1` keeps only the last row `(0, …, 0, -1)` of `sectionCoeff Z Zᴴ` and
  -- negates it; the factor `diagLast 0` keeps the other rows of `diag(1, …, 1, s)`.
  have h_one (s : ℂ) : (diagLast 0 - 1) * sectionCoeff Z Zᴴ + diagLast 0 * diagLast s = 1 := by
    simp [sectionCoeff, diagLast, ← ext_iff, Matrix.mul_apply, Matrix.one_apply, diagonal_apply,
      sum_univ_castSucc, forall_fin_succ', Fin.ne_of_gt]
  set s : ℂ := (1 - invCorner Z * invCorner Zᴴ).sqrt
  calc _ = (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols * sectionCoeff Z Zᴴ +
          𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.dualFrameCols * diagLast s) * Z := by
        simp only [sectionMatrix_mul_frameCols, sectionFrame, Matrix.mul_assoc, Matrix.mul_add,
          Matrix.add_mul, s]
    _ = Z := by rw [frameCols_gram_frameCols, frameCols_gram_dualFrameCols, h_one, Matrix.one_mul]

/-- Let `C` be a matrix with orthonormal columns, its rows indexed by the basis `e_a`, `x_i`, `z`,
`e*_a` (`BesselIndex`). Then `actOnCols C A = 1 - C Cᴴ + C A Cᴴ`, which acts by `A` on the span of
the columns and fixes its orthogonal complement, is compatible with congruence:
`(actOnCols C A)ᴴ * actOnCols C J * actOnCols C A = actOnCols C (Aᴴ J A)`. -/
theorem conjTranspose_actOnCols_mul_mul {m : Type} [Fintype m] [DecidableEq m]
    {C : Matrix 𝔰.BesselIndex m ℂ} (hC : Cᴴ * C = 1) (A J : Matrix m m ℂ) :
    (actOnCols C A)ᴴ * actOnCols C J * actOnCols C A = actOnCols C (Aᴴ * J * A) := by
  simp [actOnCols, mul_mul_eq_of_mul_eq hC, Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul]

/-- For `Z ∈ 𝔰.openCell`, the matrix `sectionMatrix Z Zᴴ`, which is the matrix of γ_Z, preserves the
hermitian form with Gram matrix `𝔰.J₁`: `Mᴴ * 𝔰.J₁ * M = 𝔰.J₁`. -/
theorem sectionMatrix_isometry {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    (sectionMatrix Z Zᴴ)ᴴ * 𝔰.J₁ * sectionMatrix Z Zᴴ = 𝔰.J₁ := by
  -- All happens in the span of the orthonormal columns `C = (F | F')`, where the form has the
  -- matrix `J`. There `sectionMatrix Z Zᴴ` acts by `y * x⁻¹`. The columns of `x` are `F Z⁻¹` and
  -- the family dual to `F` for `Zᴴ`; those of `y` are the family dual to `F` for `Z` and `F Zᴴ⁻¹`
  -- (the second halves times `Δ`). The two have the same Gram matrix.
  let ι : Type := Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1)
  let C : Matrix 𝔰.BesselIndex ι ℂ := fromCols 𝔰.frameCols 𝔰.dualFrameCols
  let J : Matrix ι ι ℂ := Cᴴ * 𝔰.J₁ * C
  let Δ : 𝔰.FrameMatrix := diagLast (√(oneSubNormSqInvCorner Z))⁻¹
  let x : Matrix ι ι ℂ := fromBlocks Z⁻¹ (sectionCoeff Zᴴ Z * Δ) 0 (1 : 𝔰.FrameMatrix)
  let y : Matrix ι ι ℂ :=
    fromBlocks (sectionCoeff Z Zᴴ) (Zᴴ⁻¹ * Δ) (diagLast √(oneSubNormSqInvCorner Z))
      (0 : 𝔰.FrameMatrix)
  have hdet : det Z ≠ 0 := (mem_openCell.1 hZ).1
  have hν_pos : 0 < oneSubNormSqInvCorner Z := oneSubNormSqInvCorner_pos hZ
  have hC : Cᴴ * C = 1 := by
    have h_symm (i j : Fin 𝔰.ϱ) : (if j = i then (1 : ℂ) else 0) = if i = j then 1 else 0 := by lia
    simpa [ι, C, ← ext_iff, inclMatrix, Matrix.one_apply, Matrix.mul_apply, forall_fin_succ',
      Fin.ne_of_gt] using h_symm
  have hJ : 𝔰.J₁ = actOnCols C J := by
    simp [ι, C, J, ← ext_iff, splitGram, middleGram, actOnCols, inclMatrix, Matrix.one_apply,
      Matrix.mul_apply, sum_univ_castSucc]
  have h_sec : sectionMatrix Z Zᴴ = actOnCols C (y * x⁻¹) := by
    simp [ι, x, y, C, Δ, inv_fromBlocks_zero₂₁_of_isUnit_iff, hZ, hdet, sectionMatrix, sectionFrame,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromBlocks, inclMatrix,
      diagLast, Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, actOnCols,
      fromCols_mul_fromRows, isUnit_iff_isUnit_det, fromBlocks_multiply, Matrix.mul_add]
    abel
  have hν_sq : (oneSubNormSqInvCorner Z : ℂ) =
      1 - starRingEnd ℂ (Z⁻¹ (last 𝔰.ϱ) (last 𝔰.ϱ)) * Z⁻¹ (last 𝔰.ϱ) (last 𝔰.ϱ) := by
    simp [oneSubNormSqInvCorner, invCorner, conj_mul']
  have h_gram : yᴴ * J * y = xᴴ * J * x := by
    -- Entry by entry these are polynomial identities in the entries of `Z⁻¹`, given `hν_sq`.
    simp [ι, x, y, J, C, Δ, ← ext_iff, sectionCoeff, map_ofNat, ← ofReal_pow, hν_pos.le,
      hν_pos.ne', ← conjTranspose_nonsing_inv, field, diagLast,
      Matrix.mul_sub, Matrix.mul_assoc, Matrix.sub_mul, fromBlocks_conjTranspose, inclMatrix,
      splitGram, middleGram, Matrix.mul_apply, Matrix.one_apply, sum_univ_castSucc,
      diagonal_apply, forall_fin_succ', Fin.ne_of_gt]
    grind
  have h_iso : (y * x⁻¹)ᴴ * J * (y * x⁻¹) = J :=
    calc _ = x⁻¹ᴴ * (yᴴ * J * y) * x⁻¹ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (x * x⁻¹)ᴴ * J * (x * x⁻¹) := by simp only [h_gram, conjTranspose_mul x, Matrix.mul_assoc]
      _ = J := by simp [mul_nonsing_inv x (by simp [ι, x, hdet])]
  rw [h_sec, hJ, conjTranspose_actOnCols_mul_mul hC, h_iso]

open scoped Classical in
/-- The section `γ_Z`. For `Z ∈ Ω` it is the element of `G₁` whose matrix is `sectionMatrix Z Zᴴ`
(see `New.RealPlace.coe_gramSection`). Off `Ω` it is the identity. -/
noncomputable def gramSection (Z : 𝔰.FrameMatrix) : 𝔰.G₁ :=
  U.of isUnit (if Z ∈ 𝔰.openCell then sectionMatrix Z Zᴴ else 1) <| by
    split_ifs with hZ
    · exact sectionMatrix_isometry hZ
    · simp

/-- The section `Z ↦ γ_Z` (`gramSection`), from the complex `(ϱ+1) × (ϱ+1)` matrices to the unitary
group `G₁` of the form `𝔰.J₁`, is measurable. Here `γ_Z` has the matrix `sectionMatrix Z Zᴴ` for `Z`
in the open set Ω (`openCell`) and is the identity off Ω. -/
@[fun_prop]
theorem measurable_gramSection : Measurable (gramSection : 𝔰.FrameMatrix → 𝔰.G₁) := by
  classical
  -- `sectionMatrix` is continuous on the open set `𝔰.openCell`; off it `gramSection` is constant.
  have h_cont : ContinuousOn (fun Z : 𝔰.FrameMatrix ↦ sectionMatrix Z Zᴴ) 𝔰.openCell := fun _ hZ ↦
    (differentiableAt_sectionMatrix hZ).continuousAt.continuousWithinAt
  have h_meas : Measurable fun Z : 𝔰.FrameMatrix ↦
    if Z ∈ 𝔰.openCell then sectionMatrix Z Zᴴ else 1 :=
    h_cont.measurable_piecewise continuousOn_const isOpen_openCell.measurableSet
  -- The σ-algebra of `𝔰.G₁` is the pullback of that of the matrices.
  exact .subtype_mk (measurable_comap_iff.2 h_meas)

/-- For `Z` in the open cell Ω (`𝔰.openCell`), the matrix of the section γ_Z = `gramSection Z` ∈ G₁
is the explicit matrix `sectionMatrix Z Zᴴ`. -/
theorem coe_gramSection {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    ((gramSection Z : GL 𝔰.BesselIndex ℂ) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) =
      sectionMatrix Z Zᴴ :=
  ite_eq_left hZ

/-- Near each `Z` in Ω, the matrix of `γ_Y` agrees with `New.RealPlace.sectionMatrix Y Yᴴ`. -/
lemma gramSection_eventuallyEq {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    (fun Y : 𝔰.FrameMatrix ↦ ((gramSection Y : GL 𝔰.BesselIndex ℂ) :
      Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) =ᶠ[nhds Z] fun Y : 𝔰.FrameMatrix ↦
        sectionMatrix Y Yᴴ :=
  .mono (isOpen_openCell.mem_nhds hZ) fun _ ↦ coe_gramSection

/-- On Ω the map `Z ↦ γ_Z` is a section of `γ ↦ Z(γ) = Fᴴ J₁ γ F` (`realFrameGram`, with `F` the
frame): `Z(γ_Z) = Z`. -/
theorem realFrameGram_gramSection {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    realFrameGram (gramSection Z) = Z := by
  rw [realFrameGram_eq_conjTranspose_mul, coe_gramSection hZ, frameCols_gram_sectionMatrix]

/-- For `γ ∈ G₁` the family `framePair γ = (F | γ F)` of the frame `F` and its image has, for the
form `𝔰.J₁`, the Gram matrix with diagonal blocks `diagLast 0 - 1 = diag(0, …, 0, -1)` and
off-diagonal blocks `Z(γ) = realFrameGram γ` and `Z(γ)ᴴ`. -/
lemma conjTranspose_framePair_mul_mul (γ : 𝔰.G₁) :
    (framePair γ)ᴴ * 𝔰.J₁ * framePair γ =
      fromBlocks (diagLast 0 - 1) (realFrameGram γ) (realFrameGram γ)ᴴ (diagLast 0 - 1) := by
  let g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := ↑(γ : GL 𝔰.BesselIndex ℂ)
  have h_pair : framePair γ = fromCols 𝔰.frameCols (g * 𝔰.frameCols) := by
    rw [mul_inclMatrix]
    rfl
  have h_upper : 𝔰.frameColsᴴ * 𝔰.J₁ * (g * 𝔰.frameCols) = realFrameGram γ :=
    (realFrameGram_eq_conjTranspose_mul γ).symm
  have h_lower : (g * 𝔰.frameCols)ᴴ * 𝔰.J₁ * 𝔰.frameCols = (realFrameGram γ)ᴴ := by
    simp [← h_upper, show 𝔰.J₁ᴴ = 𝔰.J₁ from isHermitian, Matrix.mul_assoc]
  -- The Gram matrix of `γ F` is that of `F` because `γ` is an isometry.
  have h_last : (g * 𝔰.frameCols)ᴴ * 𝔰.J₁ * (g * 𝔰.frameCols) = diagLast 0 - 1 :=
    calc _ = 𝔰.frameColsᴴ * (gᴴ * 𝔰.J₁ * g) * 𝔰.frameCols := by simp [Matrix.mul_assoc]
      _ = diagLast 0 - 1 := by
        rw [show gᴴ * 𝔰.J₁ * g = 𝔰.J₁ from mem_unitaryGroupOf_iff.1 γ.property,
            frameCols_gram_frameCols]
  rw [h_pair, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
    fromRows_mul_fromCols, frameCols_gram_frameCols, h_upper, h_lower, h_last]

/-- Let `γ ∈ G₁` have frame Gram matrix `Z(γ) = Fᴴ J₁ γ F` (`realFrameGram`) equal to `Z ∈ Ω`. Then
`γ = u k γ_Z (u' l)⁻¹`, where `γ_Z = gramSection Z`, `u = unipotentOf q` and `u' = unipotentOf r`.
The elements `k`, `l` lie in the unitary group `U 1` of the identity matrix of size `κ`, which
`embedH` lets act on the span of the `x_i` (`i ∈ κ`). -/
lemma exists_eq_mul_gramSection_mul {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) {γ : 𝔰.G₁}
    (hγ : realFrameGram γ = Z) :
    ∃ (q : 𝔰.UnipotentParams) (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (r : 𝔰.UnipotentParams)
      (l : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)),
      γ = unipotentOf q * embedH k * gramSection Z * (unipotentOf r * embedH l)⁻¹ := by
  -- `framePair s` is the frame `F` and its image `s F` side by side. For `γ` and `γ_Z` these
  -- families have the same invertible Gram matrix, so by Witt's theorem some `g` carries one to the
  -- other; then `g` and `γ_Z⁻¹ g γ` fix the frame.
  have h_disc : frameDisc 1 Z ≠ 0 := fun h_zero ↦
    (mem_openCell_iff.1 hZ).ne' (by rw [gramDiscReal, h_zero, zero_re])
  have h_left_inv {s : 𝔰.G₁} (hs : realFrameGram s = Z) : HasLeftInv (framePair s) := by
    -- the Gram determinant is `± 𝗀(Z) ≠ 0`
    refine .of_isUnit_gram (J := 𝔰.J₁) ((isUnit_iff_isUnit_det _).2 ?_)
    rw [realFrameGram] at hs
    rw [det_gram_framePair 1 (star_one ℂ), hs]
    simp [h_disc]
  have h_sec : realFrameGram (gramSection Z) = Z := realFrameGram_gramSection hZ
  obtain ⟨g, hg⟩ : ∃ g : 𝔰.G₁, g.val.val * framePair γ = framePair (gramSection Z) :=
    witt ⟨I, by simp⟩ isHermitian isUnit (h_left_inv hγ) (h_left_inv h_sec)
      (by simp only [conjTranspose_framePair_mul_mul, hγ, h_sec])
  obtain ⟨hg_fix, hg_move⟩ : g.val.val * 𝔰.frameCols = 𝔰.frameCols ∧
      g.val.val * (γ.val.val * 𝔰.frameCols) = (gramSection Z).val.val * 𝔰.frameCols := by
    simpa [fromCols_ext_iff, ← mul_inclMatrix] using hg
  have h_fix : ((gramSection Z)⁻¹ * g * γ).val.val * 𝔰.frameCols = 𝔰.frameCols := by
    simp [hg_move, Matrix.mul_assoc]
  obtain ⟨q, k, hk⟩ : ∃ (q : 𝔰.UnipotentParams) (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)),
      g * unipotentOf q = embedH k := exists_embedH_eq_of_fix_frameCols hg_fix
  obtain ⟨r, l, hl⟩ : ∃ (r : 𝔰.UnipotentParams) (l : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)),
      (gramSection Z)⁻¹ * g * γ * unipotentOf r = embedH l :=
    exists_embedH_eq_of_fix_frameCols h_fix
  refine ⟨q, k⁻¹, r, l⁻¹, ?_⟩
  simp only [map_inv, ← hk, ← hl]
  group

end New.RealPlace

end
end
end

/-!
# The mean value inequality over the Gram matrix of two frames

Let `G₁` be the real unitary group `New.Shape.G₁`, `e = (e₁, …, e_ϱ, z)` its frame, `R°` the fixer
of the frame, the product of the unipotent group `𝖴⁰ = New.Shape.Form.besselU0` and the compact
group `H = U(κ)`, and `γ_Z = New.RealPlace.gramSection Z` the section of the map that sends `γ` to
the matrix `Z` of the products of `e` with `γ e`, over the open set `Ω = New.Shape.openCell` of the
invertible `Z` whose inverse has last diagonal entry of absolute value less than `1`.

On the frames `y = γ e` the fibre measure of the Gram map is compared with Haar measure in
`New.LeGramFiber.mconv_fixerHaar_le`. This file bounds the same fibre measure from below, by `dZ`
times a measure on the frames whose products with `e` form the matrix `Z`. Such a frame is `y' Z`
with `y'` dual to `e`. The first `ϱ` vectors of `y'` are moved by `𝖴⁰`, and the part of the last one
in `X₀ = ℂ ^ κ` runs over a sphere.

One can find the measure on the frames over `Z` by letting both frames vary and dividing two
equalities of fibre measures, the one on pairs of frames, which are tuples of `2 (ϱ + 1)` vectors
with an invertible Gram matrix, by the one on frames. Here a fibre measure enters only through the
relation of being at most it (`New.LeFibreMeasure`); the measure over `Z` is computed directly in
coordinates as a lower bound, and the fibre measure on frames is used as an upper bound.

* `New.RealPlace.lintegral_eq_lintegral_sphereMass_mul_dualFrameOfGram`: Lebesgue measure on the
  tuples dual to the frame, in terms of their Gram matrix and of `R°`.
* `New.RealPlace.leGramFibre_gramSectionMeasure`: the law of `s γ_Z e`, with a density proportional
  to `New.RealPlace.gramDiscReal Z ^ (|κ| - 1)`, is at most the fibre measure.
* `New.RealPlace.lintegral_gramSection_le`: the mean value inequality for the integral of
  `f (s' γ_Z s)` over `s, s'` in `R°` and `Z` in `Ω`.

Notions from other files:
* `fixerHaar 𝔰`: the measure `du dh` on `R°`, with `u = unipotentOf q` for Lebesgue measure `dq` and
  `embedH h` for the Haar probability measure `dh` on `U(κ)`.
* `frameCols`, `dualCols`, `isotropicCols`, `definiteCols`, `freeCols`: the matrices with the
  columns `(e₁, …, e_ϱ, z)`, `e*_b`, `e_b`, `x_i`, and `(e_b, x_i)` respectively.
* `J₁`: the hermitian form on the space with the basis `e_b, x_i, z, e*_b`, which pairs `e_b` with
  `e*_b`, is the identity on `X₀` and is `-1` at `z`.
* `top`, `k`, `k₀`: the last index of the frame, the number `|κ|` and a chosen element of `κ`.
* `embedH h`: the element of `G₁` that acts by `h` on `X₀` and fixes the other basis vectors.
* `hermOfReal t`: the hermitian matrix with the real coordinates `t`.

## Relation to the literature

Part of the bound on the open cell for the Bessel integrals at a real place; see
`New.Spanning.Bessel.FillingData`. For fibre measures of the Gram map compare Siegel, Über die
analytische Theorie der quadratischen Formen, Ann. of Math. 36 (1935).
-/

@[expose] public section

noncomputable section

namespace New.RealPlace

open Matrix MeasureTheory Measure Shape ENNReal Complex Fin Fintype Norms.L2Operator
  Floors.FloorGroups

variable {𝔰 : Shape}

/-! ### The measure on the fixer of the frame -/

/-- The integral for `fixerHaar 𝔰`, the measure on the fixer of the frame, is the iterated integral
of the value at `u h`. Here `h` runs over `U(κ)` with Haar probability measure, and `u` runs over
the unipotent group `𝖴⁰` with `besselHaar₀`, the image of Lebesgue measure under `unipotentOf`. -/
theorem lintegral_fixerHaar {φ : 𝔰.G₁ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ s : 𝔰.G₁, φ s ∂fixerHaar 𝔰 =
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), ∫⁻ u : besselU0, φ (u.val * embedH h) ∂𝔰.besselHaar₀ := by
  rw [fixerHaar, Floors.lintegral_mconv_symm hφ, lintegral_map (by fun_prop) (by fun_prop)]
  exact lintegral_congr fun h ↦ lintegral_map (by fun_prop) measurable_subtypeVal

/-- The integral for `fixerHaar 𝔰`, the measure on the fixer of the frame, in coordinates: the
iterated integral of the value at `unipotentOf q * embedH h`, for Lebesgue measure in the parameter
`q` of the unipotent group and Haar measure in `h` on `U(κ)`. -/
theorem lintegral_fixerHaar_eq_unipotentOf {φ : 𝔰.G₁ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ s : 𝔰.G₁, φ s ∂fixerHaar 𝔰 =
      ∫⁻ q : 𝔰.UnipotentParams, ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), φ (unipotentOf q * embedH h) := by
  rw [lintegral_fixerHaar hφ, lintegral_lintegral_swap (by fun_prop)]
  exact lintegral_map (by fun_prop) (continuous_unipotentOf.subtype_mk _).measurable

/-- The measure `fixerHaar 𝔰`, that is `du dh` on the fixer `R° = 𝖴⁰ H` of the frame, is invariant
under inversion: the integral of `φ` is the iterated integral of `φ ((u h)⁻¹)`. -/
theorem lintegral_fixerHaar_eq_inv {φ : 𝔰.G₁ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ s : 𝔰.G₁, φ s ∂fixerHaar 𝔰 =
      ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), ∫⁻ u : besselU0, φ (u.val * embedH h)⁻¹ ∂𝔰.besselHaar₀ := by
  -- We have `(u h)⁻¹ = (h⁻¹ u⁻¹ h) h⁻¹`. Inversion keeps `du` and `dh`, and conjugation by `h`
  -- keeps `du`.
  rw [lintegral_fixerHaar hφ, ← lintegral_inv_eq_self]
  refine lintegral_congr fun h ↦ ?_
  have h_mem : embedH h⁻¹ ∈ besselS :=
    mem_besselS_of_mem_besselFixer (mem_besselFixer_of_mem_besselH (toBesselH_mem h⁻¹))
  rw [← ((measurePreserving_conj_bessel mem_besselU0_iff_apply besselS_le_normalizer_besselU0
    h_mem).comp (measurePreserving_inv 𝔰.besselHaar₀)).lintegral_comp (by fun_prop)]
  simp [mul_assoc]

/-! ### Tuples dual to the frame -/

theorem re_hermOfReal_apply_self {n : Type} [DecidableEq n] (t : Matrix n n ℝ) (a : n) :
    (hermOfReal t a a).re = t a a := by simp [hermOfReal, skewOfReal]

/-- Taking a principal submatrix along an injective map commutes with `hermOfReal`. -/
theorem submatrix_hermOfReal {m n : Type} [DecidableEq m] [DecidableEq n] (t : Matrix n n ℝ)
    {f : m → n} (hf : f.Injective) :
    (hermOfReal t).submatrix f f = hermOfReal (t.submatrix f f) := by
  simp [hermOfReal, skewOfReal, ← ext_iff, hf.eq_iff]

/-- The equivalence of `Fin j ⊕ Unit` with `Fin (j + 1)` that sends `inl b` to `b.castSucc` and the
point of `Unit` to `Fin.last j`. -/
def splitLast (j : ℕ) : Fin j ⊕ Unit ≃ Fin (j + 1) :=
  (Equiv.optionEquivSumPUnit _).symm.trans finSuccEquivLast.symm

/-- The matrix `joinCol (splitLast j) p`, made of the `j` columns of `p.1` followed by the vector
`p.2`, agrees with `p.1` in each column before the last. -/
@[simp]
theorem joinCol_castSucc {l : Type} {j : ℕ}
    (p : Matrix l (Fin j) ℂ × (l → ℂ)) (i : l) (b : Fin j) :
    joinCol (splitLast j) p i b.castSucc = p.1 i b := by
  simpa [splitLast] using joinCol_inl (splitLast j) p i b

/-- The matrix `joinCol (splitLast j) p`, made of the `j` columns of `p.1` followed by the vector
`p.2`, has the last column `p.2`. -/
@[simp]
theorem joinCol_last {l : Type} {j : ℕ}
    (p : Matrix l (Fin j) ℂ × (l → ℂ)) (i : l) : joinCol (splitLast j) p i (last j) = p.2 i := by
  simpa [splitLast] using joinCol_inr (splitLast j) p i

/-- For a hermitian matrix `T` of size `ϱ + 1` (a `FrameMatrix`), the tuple of the vectors
`e*_b + ½ ∑_a T_{ab} e_a`, `b < ϱ`, and `-z + ∑_a T_{a,last} e_a + √(1 + T_{last,last}) x_{k₀}`,
as the columns of a matrix whose rows are indexed by the basis `e_a, x_i, z, e*_a` (`BesselIndex`).
Here `x_{k₀}` is the chosen basis vector of `X₀`. The tuple is dual to the frame `(e₁, …, e_ϱ, z)`,
and it has the Gram matrix `T` if the number under the root is not negative
(`New.RealPlace.gram_dualFrameOfGram`). -/
def dualFrameOfGram (T : 𝔰.FrameMatrix) : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
  joinCol (splitLast 𝔰.ϱ)
    (𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • T.submatrix castSucc castSucc),
      -Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ (fun a : Fin 𝔰.ϱ ↦ T a.castSucc 𝔰.top) +
        𝔰.definiteCols *ᵥ √(1 + (T 𝔰.top 𝔰.top).re) • Pi.single 𝔰.k₀ 1)

@[fun_prop]
theorem continuous_dualFrameOfGram : Continuous (dualFrameOfGram (𝔰 := 𝔰)) := by
  unfold dualFrameOfGram
  fun_prop

/-- The coefficient of `e_a`, the basis vector with the index `.inl a`, in column `b` of
`dualFrameOfGram T` is the entry `T a.castSucc b` in row `a` of `T`, halved when `b ≠ top`, i.e. in
the first `ϱ` columns. -/
theorem dualFrameOfGram_apply_inl (T : 𝔰.FrameMatrix) (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
    dualFrameOfGram T (.inl a) b = (if b = 𝔰.top then 1 else 2⁻¹) * T a.castSucc b := by
  induction b using lastCases <;>
    simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec, dotProduct, Matrix.one_apply]

/-- The coefficient of `e*_a`, the basis vector with the index `eStar a`, in column `b` of
`dualFrameOfGram T` is `1` if `b = a` and `0` otherwise. -/
theorem dualFrameOfGram_apply_eStar (T : 𝔰.FrameMatrix) (a : Fin 𝔰.ϱ) (b : Fin (𝔰.ϱ + 1)) :
    dualFrameOfGram T (eStar a) b = if b = a.castSucc then 1 else 0 := by
  induction b using lastCases <;> simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec,
    dotProduct, Matrix.one_apply, (castSucc_lt_last a).ne, eq_comm]

/-- The coefficient of `z` in `dualFrameOfGram T` is `-1` in the last column and `0` in the
others. -/
theorem dualFrameOfGram_apply_z (T : 𝔰.FrameMatrix) (b : Fin (𝔰.ϱ + 1)) :
    dualFrameOfGram T 𝔰.z b = if b = 𝔰.top then -1 else 0 := by
  induction b using lastCases <;>
    simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec, dotProduct]

/-- The part in `X₀` of `dualFrameOfGram T` is `√(1 + T_{last,last}) x_{k₀}` in the last column and
zero in the others. Here `indexX₀ i` is the index of the basis vector `x_i` of `X₀`. -/
theorem dualFrameOfGram_apply_indexX₀ (T : 𝔰.FrameMatrix) (b : Fin (𝔰.ϱ + 1)) (i : 𝔰.κ) :
    dualFrameOfGram T (𝔰.indexX₀ i) b =
      if b = 𝔰.top ∧ i = 𝔰.k₀ then (√(1 + (T 𝔰.top 𝔰.top).re) : ℂ) else 0 := by
  induction b using lastCases <;> simp [dualFrameOfGram, inclMatrix, Matrix.mul_apply, mulVec,
    dotProduct, Matrix.one_apply, Pi.single_apply]

/-- Let `T` be a hermitian `(ϱ + 1)×(ϱ + 1)` matrix (`𝔰.FrameMatrix`) with `1 + Re T_{top,top} ≥ 0`.
Then the tuple `dualFrameOfGram T` has the Gram matrix `T` for `𝔰.J₁`. -/
theorem gram_dualFrameOfGram {T : 𝔰.FrameMatrix} (hT : Tᴴ = T)
    (h_top : 0 ≤ 1 + (T 𝔰.top 𝔰.top).re) : (dualFrameOfGram T)ᴴ * 𝔰.J₁ * dualFrameOfGram T = T := by
  have h_conj (a b : Fin (𝔰.ϱ + 1)) : starRingEnd ℂ (T a b) = T b a := congrFun₂ hT b a
  ext a b
  simp [Matrix.mul_apply, splitGram, middleGram, Matrix.one_apply, dualFrameOfGram_apply_inl,
    dualFrameOfGram_apply_eStar, dualFrameOfGram_apply_z, dualFrameOfGram_apply_indexX₀]
  -- Split into the `(last, last)` corner, cross terms, and the `castSucc` block.
  induction a using lastCases <;> induction b using lastCases
  · simp [← Complex.ofReal_mul, h_top, conj_eq_iff_re.1 (h_conj _ _), (castSucc_lt_last _).ne']
  · simp [h_conj, (castSucc_lt_last _).ne']
  · simp [(castSucc_lt_last _).ne']
  · simp [h_conj, map_ofNat]
    ring

/-- The mass `π ^ k r ^ (k - 1) / (k - 1)!` of the sphere `⟨x, x⟩ = r` in `ℂ ^ k` for the fibre
measure `dx / d⟨x, x⟩` if `r > 0`, and `0` if `r ≤ 0`. The mass is written as half of
`sphereDensity k r = 2 π ^ k r ^ (k - 1) / (k - 1)!`. -/
def sphereMass (k : ℕ) (r : ℝ) : ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun r : ℝ ↦ ENNReal.ofReal (sphereDensity k r / 2)) r

/-- For `r > 0` the mass of the sphere `⟨x, x⟩ = r` in `ℂ ^ k` is half of
`sphereDensity k r = 2 π ^ k r ^ (k - 1) / (k - 1)!`. -/
theorem sphereMass_of_pos {k : ℕ} {r : ℝ} (hr : 0 < r) :
    sphereMass k r = ENNReal.ofReal (sphereDensity k r / 2) := Set.indicator_of_mem hr _

@[fun_prop]
theorem measurable_sphereMass (k : ℕ) : Measurable (sphereMass k) :=
  Measurable.indicator (by fun_prop) measurableSet_Ioi

theorem continuousAt_sphereMass {k : ℕ} {r : ℝ} (hr : 0 < r) : ContinuousAt (sphereMass k) r := by
  have h_cont : Continuous fun x : ℝ ↦ ENNReal.ofReal (sphereDensity k x / 2) :=
    continuous_ofReal.comp (by fun_prop)
  refine h_cont.continuousAt.congr ?_
  filter_upwards [Ioi_mem_nhds hr] with x hx using (sphereMass_of_pos hx).symm

/-- Coordinates for the last vector `-z + ∑ a_b e_b + x` of a tuple dual to the frame
`(e₁, …, e_ϱ, z)`, where `v = (a, x)` and `x` lies in `X₀ = ℂ ^ κ`, of dimension `k = |κ|` and with
the basis `x_i`. Fix `u = unipotentOf q`, an element of the unipotent group `𝖴⁰` fixing the frame.
Write the vector as `u · embedH h` applied to `-z + ∑ c_b e_b + √(1 + r) x_{k₀}`, where `p = (c, r)`
and `r` is the product of the vector with itself. Here `k₀` is the chosen element of `κ`, `h` lies
in `U(κ)`, and `embedH h` acts as `h` on `X₀` and as the identity elsewhere. Then Lebesgue measure
`dv` is `sphereMass k (1 + r) dc dr dh`, with `dh` the Haar probability measure. -/
theorem lintegral_neg_single_add_freeCols_mulVec_eq {K : (𝔰.BesselIndex → ℂ) → ℝ≥0∞}
    (hK : Measurable K) (q : 𝔰.UnipotentParams) :
    ∫⁻ v : Fin 𝔰.ϱ ⊕ 𝔰.κ → ℂ, K (-Pi.single 𝔰.z (1 : ℂ) + 𝔰.freeCols *ᵥ v) =
      ∫⁻ p : (Fin 𝔰.ϱ → ℂ) × ℝ, sphereMass 𝔰.k (1 + p.2) * ∫⁻ h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
        K ((unipotentOf q * embedH h).val.val *ᵥ (-Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ p.1 +
          𝔰.definiteCols *ᵥ √(1 + p.2) • Pi.single 𝔰.k₀ 1)) := by
  -- On these vectors `h` rotates `x` and `u` translates `a`.
  have h_act (h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (a : Fin 𝔰.ϱ → ℂ) (x : 𝔰.κ → ℂ) :
      (unipotentOf q * embedH h).val.val *ᵥ
          (-Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ a + 𝔰.definiteCols *ᵥ x) =
        -Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ (a + q.1 *ᵥ h.val.val *ᵥ x) +
          𝔰.definiteCols *ᵥ h.val.val *ᵥ x := by
    simp [funext_iff, val_unipotentOf_coe, val_toBesselH_apply_coe, mulVec, dotProduct,
      inclMatrix, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply]
  let translated (a : Fin 𝔰.ϱ → ℂ) (x : 𝔰.κ → ℂ) : ℝ≥0∞ :=
    K (-Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ (a + q.1 *ᵥ x) + 𝔰.definiteCols *ᵥ x)
  calc
    -- split `v = (a, x)` and translate `a` by `q.1 x`
    _ = ∫⁻ x : 𝔰.κ → ℂ, ∫⁻ a : Fin 𝔰.ϱ → ℂ, translated a x := by
      rw [← Floors.measurePreserving_sumElim.lintegral_comp (by fun_prop), volume_eq_prod,
        lintegral_prod_symm _ (by fun_prop)]
      simp only [fromCols_mulVec_sumElim, ← add_assoc]
      exact lintegral_congr fun x : 𝔰.κ → ℂ ↦ (lintegral_add_right_eq_self _ (q.1 *ᵥ x)).symm
    -- polar coordinates in `x`
    _ = ∫⁻ r : ℝ, sphereMass 𝔰.k r *
          ∫⁻ h : U 1, ∫⁻ a, translated a (h.val.val *ᵥ √r • Pi.single 𝔰.k₀ 1) := by
      rw [Floors.lintegral_eq_polar 𝔰.k₀ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]
      simp only [sphereMass, Set.indicator_mul_left]
    -- shift `r` by one and integrate in `h` before `a`
    _ = ∫⁻ p : (Fin 𝔰.ϱ → ℂ) × ℝ, sphereMass 𝔰.k (1 + p.2) *
          ∫⁻ h : U 1, translated p.1 (h.val.val *ᵥ √(1 + p.2) • Pi.single 𝔰.k₀ 1) := by
      rw [← lintegral_add_left_eq_self _ 1, volume_eq_prod, lintegral_prod_symm _ (by fun_prop)]
      refine lintegral_congr fun r : ℝ ↦ ?_
      rw [lintegral_lintegral_swap (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
    _ = _ := by simp only [translated, h_act]

/-- Coordinates on the tuples dual to the frame `e = (e₁, …, e_ϱ, z)`, which are the `J₁ e + R p`:
here `e` is `frameCols`, and `R` is `freeCols`, whose columns are the `e_b` and the basis vectors
`x_i` of `X₀ = ℂ ^ κ`. Write such a tuple as `s y(T)`, where `T = hermOfReal t` is its Gram matrix,
with real coordinates `t`, `y(T) = dualFrameOfGram T` is the standard dual tuple with the Gram
matrix `T`, and `s` lies in the fixer `R°` of the frame, with its measure `ds = fixerHaar 𝔰`. Then
Lebesgue measure `dp` is `2 ^ (-ϱ) sphereMass k r dt ds`, where `k = |κ|` and
`r = 1 + T_{last,last}`. -/
theorem lintegral_eq_lintegral_sphereMass_mul_dualFrameOfGram
    {K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ, K (𝔰.J₁ * 𝔰.frameCols + 𝔰.freeCols * p) =
      ∫⁻ t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ,
        (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (1 + (hermOfReal t 𝔰.top 𝔰.top).re) *
          ∫⁻ s : 𝔰.G₁, K (s.val.val * dualFrameOfGram (hermOfReal t)) ∂fixerHaar 𝔰 := by
  -- Choose the first `ϱ` vectors, which fixes the upper left block of `T` and the unipotent part
  -- of `s`, and then the last vector.
  let firstCols (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ :=
    𝔰.dualCols + 𝔰.isotropicCols * ((2⁻¹ : ℂ) • hermOfReal t)
  let lastIntegral (Y : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) ℂ) : ℝ≥0∞ :=
    ∫⁻ v : Fin 𝔰.ϱ ⊕ 𝔰.κ → ℂ, K (joinCol (splitLast 𝔰.ϱ) (Y, -Pi.single 𝔰.z 1 + 𝔰.freeCols *ᵥ v))
  let tuple (p : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ × (Fin 𝔰.ϱ → ℂ) × ℝ) :
      Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
    joinCol (splitLast 𝔰.ϱ) (firstCols p.1, -Pi.single 𝔰.z 1 + 𝔰.isotropicCols *ᵥ p.2.1 +
      𝔰.definiteCols *ᵥ √(1 + p.2.2) • Pi.single 𝔰.k₀ 1)
  let movedIntegrand (p : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ × (Fin 𝔰.ϱ → ℂ) × ℝ) (s : 𝔰.G₁) : ℝ≥0∞ :=
    K (s.val.val * tuple p)
  -- A dual tuple is given by its first `ϱ` vectors and its last one.
  have h_split (p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ) (v : Fin 𝔰.ϱ ⊕ 𝔰.κ → ℂ) :
      𝔰.J₁ * 𝔰.frameCols + 𝔰.freeCols * joinCol (splitLast 𝔰.ϱ) (p, v) = joinCol (splitLast 𝔰.ϱ)
        (𝔰.dualCols + 𝔰.freeCols * p, -Pi.single 𝔰.z 1 + 𝔰.freeCols *ᵥ v) := by
    simp [← ext_iff, forall_fin_succ', mul_joinCol, splitGram, middleGram, inclMatrix,
      Matrix.mul_apply, Matrix.one_apply, Pi.single_apply]
  -- With the first `ϱ` vectors fixed, integrate over the last one; `h` fixes the first ones.
  have h_last_vector (t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ) (q : 𝔰.UnipotentParams) :
      lastIntegral ((unipotentOf q).val.val * firstCols t) =
        ∫⁻ p : (Fin 𝔰.ϱ → ℂ) × ℝ, sphereMass 𝔰.k (1 + p.2) *
          ∫⁻ h : U 1, movedIntegrand (t, p) (unipotentOf q * embedH h) := by
    have h_first (h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) : (unipotentOf q * embedH h).val.val * firstCols t =
        (unipotentOf q).val.val * firstCols t := by
      simp [firstCols, coe_embedH, actOnCols, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
        Matrix.sub_mul, inclMatrix_gram_eq_zero, inclMatrix_gram_mul_eq_zero]
    simp only [movedIntegrand, tuple, mul_joinCol, h_first]
    exact lintegral_neg_single_add_freeCols_mulVec_eq (K := fun v : 𝔰.BesselIndex → ℂ ↦
      K (joinCol (splitLast 𝔰.ϱ) ((unipotentOf q).val.val * firstCols t, v))) (by fun_prop) q
  -- The measure preserving `φ` gives `t` by its upper left block, the rest of the last column of
  -- `hermOfReal t` and its corner.
  obtain ⟨φ, φ_vol, φ_apply⟩ := exists_measurePreserving_hermCorner (splitLast 𝔰.ϱ)
  calc
    _ = ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin 𝔰.ϱ) ℂ, lastIntegral (𝔰.dualCols + 𝔰.freeCols * p) := by
      rw [← (measurePreserving_joinCol (splitLast 𝔰.ϱ)).lintegral_comp (by fun_prop),
        volume_eq_prod, lintegral_prod _ (by fun_prop)]
      simp only [lastIntegral, h_split]
    _ = (2 ^ 𝔰.ϱ)⁻¹ * ∫⁻ t : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ, ∫⁻ q : 𝔰.UnipotentParams,
          lastIntegral ((unipotentOf q).val.val * firstCols t) :=
      lintegral_eq_unipotent_coords (by fun_prop)
    _ = ∫⁻ p : Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ × (Fin 𝔰.ϱ → ℂ) × ℝ,
          (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (1 + p.2.2) *
            ∫⁻ s : 𝔰.G₁, movedIntegrand p s ∂fixerHaar 𝔰 := by
      rw [volume_eq_prod (Matrix (Fin 𝔰.ϱ) (Fin 𝔰.ϱ) ℝ), lintegral_prod _ (by fun_prop),
        ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun t ↦ ?_
      rw [lintegral_congr (h_last_vector t), lintegral_lintegral_swap (by fun_prop),
        ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_congr fun p ↦ ?_
      rw [lintegral_const_mul _ (by fun_prop), lintegral_fixerHaar_eq_unipotentOf (by fun_prop),
        mul_assoc]
    _ = _ := by
      rw [← φ_vol.lintegral_comp (by fun_prop)]
      refine lintegral_congr fun t ↦ ?_
      have h_tuple : tuple (φ t) = dualFrameOfGram (hermOfReal t) := by
        simp [φ_apply, tuple, firstCols, dualFrameOfGram, re_hermOfReal_apply_self,
          submatrix_hermOfReal t (castSucc_injective _), splitLast, Function.comp_def]
      simp only [movedIntegrand, h_tuple]
      simp [φ_apply, re_hermOfReal_apply_self, splitLast]

/-! ### The fibre measure on frames, over the matrix of products with the standard frame -/

/-- Coordinates on the tuples `y = J₁ e Z + R p` whose products with the frame
`e = (e₁, …, e_ϱ, z) = 𝔰.frameCols` form the invertible matrix `Z`, where `R = 𝔰.freeCols` has the
columns `e_b` and `x_i`. Write `y = y' Z`, so that `y'` is dual to the frame and has the Gram matrix
`T' = Z⁻¹ᴴ T Z⁻¹` if `y` has the Gram matrix `T = hermOfReal t`. Then `y' = s · dualFrameOfGram T'`
is the standard dual tuple with the Gram matrix `T'`, moved by an element `s` of the fixer `𝖴⁰ U(κ)`
of the frame, and Lebesgue measure `dp` is `|det Z| ^ (2 (k - 1)) 2 ^ (-ϱ) sphereMass k r dt ds`,
where `k = |κ|` and `r = 1 + T'_{last,last}`. Here `sphereMass k r` is the mass
`π ^ k r ^ (k - 1) / (k - 1)!` of the sphere `⟨x, x⟩ = r` in `ℂ ^ k` if `r > 0`, and `0` otherwise;
`ds = fixerHaar 𝔰` is Lebesgue measure in the parameter of `unipotentOf` on `𝖴⁰` times the Haar
probability measure on `U(κ)`; and `s.val.val` is the matrix of `s`. -/
theorem lintegral_eq_dualFrameOfGram_mul {Z : 𝔰.FrameMatrix} (hZ : Z.det ≠ 0)
    {K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ, K (𝔰.J₁ * 𝔰.frameCols * Z + 𝔰.freeCols * p) =
      ∫⁻ t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ,
        ‖Z.det‖ₑ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ *
            sphereMass 𝔰.k (1 + ((Z⁻¹ᴴ * hermOfReal t * Z⁻¹) 𝔰.top 𝔰.top).re) *
          ∫⁻ s : 𝔰.G₁, K (s.val.val * dualFrameOfGram (Z⁻¹ᴴ * hermOfReal t * Z⁻¹) * Z)
            ∂fixerHaar 𝔰 := by
  -- The substitution costs `|det Z| ^ (2 (ϱ + k))` in `dp` and `|det Z| ^ (2 (ϱ + 1))` in `dT`.
  let dualIntegrand (T : 𝔰.FrameMatrix) : ℝ≥0∞ :=
    (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (1 + (T 𝔰.top 𝔰.top).re) *
      ∫⁻ s : 𝔰.G₁, K (s.val.val * dualFrameOfGram T * Z) ∂fixerHaar 𝔰
  have h_exp : 2 * card (Fin 𝔰.ϱ ⊕ 𝔰.κ) = 2 * (𝔰.k - 1) + 2 * card (Fin (𝔰.ϱ + 1)) := by
    grind [card_sum, card_fin, card_pos_iff.2 (⟨𝔰.k₀⟩ : Nonempty 𝔰.κ)]
  calc
    _ = ‖Z.det‖ₑ ^ (2 * card (Fin 𝔰.ϱ ⊕ 𝔰.κ)) * ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ,
          K ((𝔰.J₁ * 𝔰.frameCols + 𝔰.freeCols * p) * Z) := by
      rw [lintegral_eq_det_mul_comp_mul_mul (P := 1) (by simp) hZ (by fun_prop)]
      simp [Matrix.add_mul, Matrix.mul_assoc]
    _ = ‖Z.det‖ₑ ^ (2 * card (Fin 𝔰.ϱ ⊕ 𝔰.κ)) * ∫⁻ t, dualIntegrand (hermOfReal t) := by
      rw [lintegral_eq_lintegral_sphereMass_mul_dualFrameOfGram (K := fun y ↦ K (y * Z))
        (by fun_prop)]
    _ = ‖Z.det‖ₑ ^ (2 * (𝔰.k - 1)) * ∫⁻ t, dualIntegrand (Z⁻¹ᴴ * hermOfReal t * Z⁻¹) := by
      rw [lintegral_eq_det_mul_comp_congruence hZ (G := fun T ↦ dualIntegrand (Z⁻¹ᴴ * T * Z⁻¹))
        (by fun_prop), h_exp, pow_add, mul_assoc]
      simp [← Matrix.mul_assoc, ← conjTranspose_mul, hZ]
    _ = _ := by simp (disch := finiteness) only [dualIntegrand, mul_assoc, lintegral_const_mul']

/-- The Gram matrix of the frame is `diag(0, …, 0, -1)`; so its congruence by `Z⁻¹` is `-ζᴴ ζ` for
the last row `ζ` of `Z⁻¹`. -/
theorem inv_frameGram_inv_apply (Z : 𝔰.FrameMatrix) (a b : Fin (𝔰.ϱ + 1)) :
    (Z⁻¹ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) * Z⁻¹) a b =
      -(starRingEnd ℂ (Z⁻¹ 𝔰.top a) * Z⁻¹ 𝔰.top b) := by
  simp [Matrix.mul_apply, splitGram, middleGram, inclMatrix, Matrix.one_apply, sum_univ_castSucc]

/-- For the congruence `T` by `Z⁻¹` of the Gram matrix of the frame, `1 + T_{last,last}` is
`oneSubNormSqInvCorner Z = 1 - |ξ|²`, with `ξ` the last diagonal entry of `Z⁻¹`. -/
theorem one_add_inv_frameGram_inv_top (Z : 𝔰.FrameMatrix) :
    1 + ((Z⁻¹ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) * Z⁻¹) 𝔰.top 𝔰.top).re =
      oneSubNormSqInvCorner Z := by
  rw [inv_frameGram_inv_apply, conj_mul', ← Complex.ofReal_pow, neg_re, ofReal_re,
    oneSubNormSqInvCorner, invCorner, sub_eq_add_neg]

/-- Let `ζ` be the last row of `Z⁻¹`. Row `a < ϱ` of `sectionCoeff Z Zᴴ` is row `a` of `-ζᴴ ζ`,
halved in the first `ϱ` columns. The matrix `sectionCoeff Z W` is built from the last row of `Z⁻¹`
and the last column of `W⁻¹`. -/
theorem sectionCoeff_conjTranspose_castSucc_apply (Z : 𝔰.FrameMatrix) (a : Fin 𝔰.ϱ)
    (b : Fin (𝔰.ϱ + 1)) :
    sectionCoeff Z Zᴴ a.castSucc b =
      (if b = 𝔰.top then 1 else 2⁻¹) * -(starRingEnd ℂ (Z⁻¹ 𝔰.top a.castSucc) * Z⁻¹ 𝔰.top b) := by
  -- The last factor of `sectionCoeff` doubles the last column of the product of the others.
  have h_prod : (diagLast (𝔰 := 𝔰) 0 * Zᴴ⁻¹ * (1 - diagLast (𝔰 := 𝔰) 2⁻¹) * Z⁻¹) a.castSucc b =
      2⁻¹ * (starRingEnd ℂ (Z⁻¹ 𝔰.top a.castSucc) * Z⁻¹ 𝔰.top b) := by
    simp [diagLast, Matrix.mul_apply, sum_univ_castSucc, Matrix.one_apply, diagonal_apply,
      (castSucc_lt_last _).ne', ← conjTranspose_nonsing_inv, mul_comm, mul_left_comm,
      show (1 - 2⁻¹ : ℂ) = 2⁻¹ by norm_num]
  have h_two : diagLast (𝔰 := 𝔰) 2 = diagonal (snoc 1 2) := rfl
  rw [sectionCoeff, h_two, Matrix.sub_apply, mul_diagonal, h_prod]
  induction b using lastCases <;> simp [diagLast, Matrix.one_apply, diagonal_apply,
    mul_right_comm _ _ (2 : ℂ)]

/-- The last row of `sectionCoeff Z Zᴴ` is `(0, …, 0, -1)`. For `Z` in the open cell, the columns of
`sectionCoeff Z W` at `W = Zᴴ` are the coefficients of `e₁, …, e_ϱ, z` in the tuple `y'` that is
dual to the frame `e` and has `γ_Z e = y' Z`. -/
theorem sectionCoeff_conjTranspose_top_apply (Z : 𝔰.FrameMatrix) (b : Fin (𝔰.ϱ + 1)) :
    sectionCoeff Z Zᴴ 𝔰.top b = if b = 𝔰.top then -1 else 0 := by
  induction b using lastCases <;>
    simp [sectionCoeff, diagLast, Matrix.mul_assoc, (castSucc_lt_last _).ne']

/-- For `Z` in the open cell and `γ_Z = gramSection Z`, the chosen element of `G₁` for which the
products of `e` with `γ_Z e` form `Z`, the image `γ_Z e` of the frame `e = 𝔰.frameCols` is `y' Z`,
where `y'` is the tuple dual to `e` that `New.RealPlace.dualFrameOfGram` attaches to the congruence
by `Z⁻¹` of the Gram matrix of `e`. -/
theorem dualFrameOfGram_mul_eq_gramSection_mul {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    dualFrameOfGram (Z⁻¹ᴴ * (𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols) * Z⁻¹) * Z =
      ((gramSection Z : GL 𝔰.BesselIndex ℂ) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *
        𝔰.frameCols := by
  -- Compare the coefficients of the vectors e_a, x_i, z and e*_a in the two tuples.
  rw [coe_gramSection hZ, sectionMatrix_mul_frameCols, sectionFrame,
    sqrt_eq_sqrt_oneSubNormSqInvCorner hZ]
  congr 1
  ext (a | (i | _) | a) b
  all_goals
    try rw [dualFrameOfGram_apply_inl, inv_frameGram_inv_apply,
      ← sectionCoeff_conjTranspose_castSucc_apply]
    try rw [dualFrameOfGram_apply_indexX₀, one_add_inv_frameGram_inv_top]
    try rw [dualFrameOfGram_apply_z, ← sectionCoeff_conjTranspose_top_apply Z]
    try rw [dualFrameOfGram_apply_eStar]
    induction b using lastCases <;>
      simp [Matrix.mul_apply, inclMatrix, Matrix.one_apply, sum_univ_castSucc, diagLast,
        diagonal_apply, eq_comm, (castSucc_lt_last _).ne]

/-- The measure on `G₁` that is the law of `s γ_Z`, for `Z` in the open cell and `s` in the fixer
`R°` of the frame, under `dZ ds` with the density `2 ^ (-ϱ) π ^ k 𝗀(Z) ^ (k - 1) / (k - 1)!`. Here
`γ_Z = New.RealPlace.gramSection Z` and `𝗀 = New.RealPlace.gramDiscReal`. -/
def gramSectionMeasure (𝔰 : Shape) : Measure 𝔰.G₁ :=
  (((volume.restrict 𝔰.openCell).prod (fixerHaar 𝔰)).withDensity
      fun p : 𝔰.FrameMatrix × 𝔰.G₁ ↦ ENNReal.ofReal
        (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal p.1 ^ (𝔰.k - 1))).map
    fun p : 𝔰.FrameMatrix × 𝔰.G₁ ↦ p.2 * gramSection p.1

instance : SFinite (gramSectionMeasure 𝔰) := by
  unfold gramSectionMeasure
  infer_instance

/-- Let `T = hermOfReal t`, let `Z` be invertible and put `T' = Z⁻¹ᴴ T Z⁻¹`. If
`1 + T'_{last,last} ≥ 0`, then for all `s` in `G₁` the tuple `s (dualFrameOfGram T') Z` has the
Gram matrix `T`, that is, its Gram coordinates `gramCoords` are `t`. -/
theorem gramCoords_dualFrameOfGram_mul {Z : 𝔰.FrameMatrix} (hZ : Z.det ≠ 0)
    {t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ}
    (h_corner : 0 ≤ 1 + ((Z⁻¹ᴴ * hermOfReal t * Z⁻¹) 𝔰.top 𝔰.top).re) (s : 𝔰.G₁) :
    gramCoords 𝔰.J₁ (s.val.val * dualFrameOfGram (Z⁻¹ᴴ * hermOfReal t * Z⁻¹) * Z) = t := by
  rw [Matrix.mul_assoc, gramCoords_U_mul, gramCoords_eq_iff, gram_mul,
    gram_dualFrameOfGram (by simp [Matrix.mul_assoc]) h_corner]
  simp [← Matrix.mul_assoc, ← conjTranspose_mul, hZ]

/-- A matrix in the open cell, the set of invertible `Z` whose inverse has last diagonal entry of
absolute value less than `1`, has nonzero determinant. -/
theorem det_ne_zero_of_mem_openCell {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) : Z.det ≠ 0 := hZ.left

/-- Let `𝔰` be a shape with `ϱ` hyperbolic pairs and index set `κ`, and let `k = |κ|`. Let `Z` lie
in the open cell `𝔰.openCell`: `Z` is invertible and the last diagonal entry of `Z⁻¹` has absolute
value less than 1. Let `𝗀(Z) = gramDiscReal Z` be `|det Z|²` minus the squared absolute value of the
leading minor of order `ϱ` of `Z`. Take the mass `sphereMass` of the sphere in `ℂ ^ k` of squared
radius `oneSubNormSqInvCorner Z = 𝗀(Z) / |det Z|²`, and multiply it by
`|det Z| ^ (2 (k - 1)) 2 ^ (-ϱ)`. The result is the density
`2 ^ (-(ϱ + 1)) sphereDensity k 1 · 𝗀(Z) ^ (k - 1)` of `New.RealPlace.gramSectionMeasure`. -/
theorem enorm_det_pow_mul_sphereMass {Z : 𝔰.FrameMatrix} (hZ : Z ∈ 𝔰.openCell) :
    ‖Z.det‖ₑ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ * sphereMass 𝔰.k (oneSubNormSqInvCorner Z) =
      ENNReal.ofReal (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1)) := by
  have h_real : sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1) =
      ‖Z.det‖ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ *
        (sphereDensity 𝔰.k (oneSubNormSqInvCorner Z) / 2) := by
    simp only [sphereDensity, gramDiscReal_eq_norm_det_sq_mul (det_ne_zero_of_mem_openCell hZ)]
    ring
  rw [h_real, sphereMass_of_pos (oneSubNormSqInvCorner_pos hZ), ENNReal.ofReal_mul (by positivity)]
  simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos]

/-- The integral of `K ≥ 0` over the tuples `J₁ e Z + R p` with `Z` in the open cell, where `e` is
the frame and `R = 𝔰.freeCols`, is at most its integral over all tuples. -/
theorem setLIntegral_openCell_frame_coords_le
    {K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Z : 𝔰.FrameMatrix in 𝔰.openCell, ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ,
        K (𝔰.J₁ * 𝔰.frameCols * Z + 𝔰.freeCols * p) ≤
      ∫⁻ y : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ, K y := by
  have h_vol : MeasurePreserving fun p : 𝔰.FrameMatrix × Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ ↦
      𝔰.J₁ * 𝔰.frameCols * p.1 + 𝔰.freeCols * p.2 :=
    measurePreserving_mul_mul_add_mul conjTranspose_frameCols_mul_self
      conjTranspose_freeCols_mul_self frameCols_gram_freeCols
      card_frame_add_card_free
  rw [← h_vol.lintegral_comp hK, volume_eq_prod, lintegral_prod _ (by fun_prop)]
  exact setLIntegral_le_lintegral _ _

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `e = 𝔰.frameCols` be the matrix with the columns `e₁, …, e_ϱ, z` of the frame and `𝔰.J₁` the
matrix of the hermitian form that defines `G₁`. The measure `gramSectionMeasure 𝔰` is the law of
`s γ_Z` under `2 ^ (-ϱ) π ^ k / (k - 1)! · 𝗀(Z) ^ (k - 1) dZ ds`, where `Z` runs over the open cell,
`s` over the fixer of `e` with `ds = fixerHaar 𝔰`, `γ_Z = gramSection Z`, `k = |κ|`, and
`𝗀(Z) = gramDiscReal Z` is `|det Z|²` less the squared absolute value of the leading minor of order
`ϱ`. The image `l` of this measure under `g ↦ g e` is at most the fibre measure `dY / dT` of the
Gram map `Y ↦ T = Yᴴ J₁ Y` over the Gram matrix `T₀` of `e`. Here `dY` is Lebesgue measure on the
matrices `Y` of the size of `e`, and `dT` is Lebesgue measure in the real coordinates of `T`
(`hermOfReal`). By the definition of `LeGramFiber` this means: if `K ≥ 0` is lower semicontinuous
and `∫_{T(Y) ∈ S} K dY ≤ C vol(S)` for all open `S` inside some neighbourhood of `T₀`, then
`∫ K dl ≤ C`. -/
theorem leGramFibre_gramSectionMeasure :
    LeGramFiber 𝔰.J₁ 𝔰.frameCols (gramSectionMeasure 𝔰) := by
  -- The tuples with `Z` in the open cell have the coordinates `tuple t (Z, s)`, with the density
  -- `density t (Z, s)` for `dt` and `μ = dZ ds`. At the coordinates `t₀` of the Gram matrix of `e`
  -- the point is `s γ_Z e` and the sphere has the squared radius `oneSubNormSqInvCorner Z`.
  let μ : Measure (𝔰.FrameMatrix × 𝔰.G₁) := (volume.restrict 𝔰.openCell).prod (fixerHaar 𝔰)
  let congrGram (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) (Z : 𝔰.FrameMatrix) :
      𝔰.FrameMatrix := Z⁻¹ᴴ * hermOfReal t * Z⁻¹
  let tuple (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) (p : 𝔰.FrameMatrix × 𝔰.G₁) :
      Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ :=
    p.2.val.val * dualFrameOfGram (congrGram t p.1) * p.1
  let density (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) (p : 𝔰.FrameMatrix × 𝔰.G₁) : ℝ≥0∞ :=
    ‖p.1.det‖ₑ ^ (2 * (𝔰.k - 1)) * (2 ^ 𝔰.ϱ)⁻¹ *
      sphereMass 𝔰.k (1 + (congrGram t p.1 𝔰.top 𝔰.top).re)
  let t₀ : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ := gramCoords 𝔰.J₁ 𝔰.frameCols
  have ht₀ : hermOfReal t₀ = 𝔰.frameColsᴴ * 𝔰.J₁ * 𝔰.frameCols :=
    hermOfReal_gramCoords IsHermitianInvolution.isHermitian _
  have h_cell : ∀ᵐ p ∂μ, p.1 ∈ 𝔰.openCell :=
    quasiMeasurePreserving_fst.ae (ae_restrict_mem isOpen_openCell.measurableSet)
  have h_corner (Z : 𝔰.FrameMatrix) :
      1 + (congrGram t₀ Z 𝔰.top 𝔰.top).re = oneSubNormSqInvCorner Z := by
    simp only [congrGram, ht₀, one_add_inv_frameGram_inv_top]
  have h_fibre (t : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) ℝ) :
      ∀ᵐ p ∂μ, density t p ≠ 0 → gramCoords 𝔰.J₁ (tuple t p) = t := by
    filter_upwards [h_cell] with p hp h_ne_zero
    have h_pos : 0 < 1 + (congrGram t p.1 𝔰.top 𝔰.top).re :=
      Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h_ne_zero)
    exact gramCoords_dualFrameOfGram_mul (det_ne_zero_of_mem_openCell hp) h_pos.le p.2
  have h_cont : ∀ᵐ p ∂μ, ContinuousAt (tuple · p) t₀ ∧ ContinuousAt (density · p) t₀ := by
    filter_upwards [h_cell] with p hp
    have h_mass : ContinuousAt (fun t ↦ sphereMass 𝔰.k (1 + (congrGram t p.1 𝔰.top 𝔰.top).re)) t₀ :=
      (continuousAt_sphereMass (oneSubNormSqInvCorner_pos hp)).comp_of_eq (by fun_prop)
        (h_corner p.1)
    exact ⟨by fun_prop, ENNReal.Tendsto.const_mul h_mass (.inr (by finiteness))⟩
  have h_le (K : Matrix 𝔰.BesselIndex (Fin (𝔰.ϱ + 1)) ℂ → ℝ≥0∞) (hK : Measurable K) :
      ∫⁻ t in Set.univ, ∫⁻ p, density t p * K (tuple t p) ∂μ ≤ ∫⁻ y, K y := calc
    _ = ∫⁻ Z in 𝔰.openCell, ∫⁻ t, ∫⁻ s, density t (Z, s) * K (tuple t (Z, s)) ∂fixerHaar 𝔰 := by
      rw [restrict_univ, lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
      exact lintegral_congr fun Z ↦ lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ Z in 𝔰.openCell, ∫⁻ p : Matrix (Fin 𝔰.ϱ ⊕ 𝔰.κ) (Fin (𝔰.ϱ + 1)) ℂ,
          K (𝔰.J₁ * 𝔰.frameCols * Z + 𝔰.freeCols * p) := by
      refine setLIntegral_congr_fun isOpen_openCell.measurableSet fun Z hZ ↦ ?_
      simp (disch := fun_prop) only [density, tuple, congrGram, lintegral_const_mul,
        lintegral_eq_dualFrameOfGram_mul (det_ne_zero_of_mem_openCell hZ) hK]
    _ ≤ ∫⁻ y, K y := setLIntegral_openCell_frame_coords_le hK
  have h_density : ∀ᵐ p ∂μ, density t₀ p =
      ENNReal.ofReal (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal p.1 ^ (𝔰.k - 1)) :=
    h_cell.mono fun p hp ↦ by simp only [density, h_corner, enorm_det_pow_mul_sphereMass hp]
  have h_point : ∀ᵐ p ∂μ, (p.2 * gramSection p.1).val.val * 𝔰.frameCols = tuple t₀ p :=
    h_cell.mono fun p hp ↦ by simp only [tuple, congrGram, ht₀, Subgroup.coe_mul, Units.val_mul,
      Matrix.mul_assoc p.2.val.val, dualFrameOfGram_mul_eq_gramSection_mul hp]
  have h_law : (gramSectionMeasure 𝔰).map (fun g : 𝔰.G₁ ↦ g.val.val * 𝔰.frameCols) =
      (μ.withDensity (density t₀)).map (tuple t₀) := by
    rw [gramSectionMeasure, Measure.map_map (by fun_prop) (by fun_prop),
      ← withDensity_congr_ae h_density]
    exact Measure.map_congr (withDensity_absolutelyContinuous μ (density t₀) h_point)
  rw [LeGramFiber, h_law]
  exact .of_coordinates (ψ := tuple) (w := density) (by fun_prop) (by fun_prop) (by fun_prop)
    Filter.univ_mem (fun t _ ↦ h_fibre t) h_cont h_le

/-- The mean value inequality. For measurable `f ≥ 0` on `G₁`, the integral of `f (s' γ_Z s)` over
`s, s'` in the fixer `R°` of the frame and `Z` in the open cell, with density `c 𝗀(Z) ^ (k - 1)`, is
at most the integral of `f` over `G₁` for Haar measure. Here `γ_Z = New.RealPlace.gramSection Z` is
the element with the matrix `Z` of products of the frame `e` with `γ_Z e`, `k = |κ|`,
`r = k + 2 ϱ + 1`, `c = New.Shape.openCellConst` is `vol U(k) / vol U(r)` times the area of the unit
sphere in `ℂ ^ k`, and `𝗀 = New.RealPlace.gramDiscReal` is `|det Z|²` less the squared absolute
value of the leading minor of order `ϱ`. -/
theorem lintegral_gramSection_le {f : 𝔰.G₁ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ Z : 𝔰.FrameMatrix in 𝔰.openCell,
        ENNReal.ofReal (𝔰.openCellConst * gramDiscReal Z ^ (𝔰.k - 1)) *
          ∫⁻ s' : 𝔰.G₁, ∫⁻ s : 𝔰.G₁, f (s' * gramSection Z * s) ∂fixerHaar 𝔰 ∂fixerHaar 𝔰 ≤
      ∫⁻ γ : 𝔰.G₁, f γ := by
  -- The image of `gramSectionMeasure 𝔰` is at most the fibre measure on frames, so its
  -- convolution with `fixerHaar 𝔰` is at most `ratio` times Haar measure.
  let ratio : ℝ := volU 𝔰.r / volU 𝔰.k / 2 ^ (𝔰.ϱ + 1)
  have h_volU_r_pos : 0 < volU 𝔰.r := volU_pos 𝔰.r
  have h_volU_k_pos : 0 < volU 𝔰.k := volU_pos 𝔰.k
  have h_ratio_pos : 0 < ratio := by positivity
  have h_const (Z : 𝔰.FrameMatrix) : ratio * (𝔰.openCellConst * gramDiscReal Z ^ (𝔰.k - 1)) =
      sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1) := by
    simp only [ratio, openCellConst]
    field
  rw [← ENNReal.mul_le_mul_iff_right (ofReal_pos.2 h_ratio_pos).ne' ofReal_ne_top]
  calc
    _ = ∫⁻ Z in 𝔰.openCell,
          ENNReal.ofReal (sphereDensity 𝔰.k 1 / 2 ^ (𝔰.ϱ + 1) * gramDiscReal Z ^ (𝔰.k - 1)) *
            ∫⁻ s', ∫⁻ s, f (s' * gramSection Z * s) ∂fixerHaar 𝔰 ∂fixerHaar 𝔰 := by
      rw [← lintegral_const_mul _ (by fun_prop)]
      simp only [← mul_assoc, ← ENNReal.ofReal_mul h_ratio_pos.le, h_const]
    _ = ∫⁻ g, ∫⁻ s, f (g * s) ∂fixerHaar 𝔰 ∂gramSectionMeasure 𝔰 := by
      rw [gramSectionMeasure, lintegral_map (by fun_prop) (by fun_prop),
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
        lintegral_prod _ (by fun_prop)]
      exact lintegral_congr fun Z ↦ (lintegral_const_mul _ (by fun_prop)).symm
    _ = ∫⁻ γ, f γ ∂gramSectionMeasure 𝔰 ∗ₘ fixerHaar 𝔰 := (lintegral_mconv hf).symm
    _ ≤ ENNReal.ofReal ratio * ∫⁻ γ, f γ := by
      grw [leGramFibre_gramSectionMeasure.mconv_fixerHaar_le, lintegral_smul_measure, smul_eq_mul]

end New.RealPlace

end
end
end

/-!
# Unfolding bounds over G₁ and the L² bound at the section γ_Z via Sobolev

`New.Shape.G₁` is the complex unitary group of the shape `𝔰`, with index set
`New.Shape.BesselIndex`. `𝖴 = New.Shape.Form.besselU` is its Bessel unipotent group, and
`𝖴⁰ = New.Shape.Form.besselU0` is the subgroup of `𝖴` fixing the frame e₁, …, e_ϱ, z; their Haar
measures are `New.Shape.besselHaar` and `New.Shape.besselHaar₀`. An unfolding inequality bounds
suitable integrals over `G₁` by integrals over `𝖴∖G₁`. An `L²` bound on the quotient `𝖴∖G₁` for
convolutions, the hypothesis `New.RealPlace.HasSchurBound`, then gives an `L²` bound on a bounded
part of the orbit of the section `γ_Z = New.RealPlace.gramSection Z`, at the price of a power of a
size bound `P`.

## Main definitions and results

* `New.lintegral_mul_le_of_frameMatrix_le`: the unfolding bound on `G₁`.
* `New.RealPlace.HasDerivWords`: families that behave like iterated right derivatives on `G₁`.
* `New.RealPlace.lintegral_gramSection_integral_le`: the bound for the convolution at `γ_Z (u h)⁻¹`,
  integrated over `h ∈ U(κ)` and the `u ∈ 𝖴⁰` with `‖u‖ ≤ P ^ 20`. Sobolev's inequality on a small
  cube at `Z` (`New.sobolev_trace_cube`) replaces the value at `Z` by mean squares of derivatives,
  which are bounded by integrals over `𝖴∖G₁`.

Notions from other files:
* `New.Shape.Form.besselS`: the Bessel subgroup, generated by `𝖴` and by the image of `U(κ)` under
  `New.RealPlace.embedH`.
* `New.besselQuotMeasure`: the measure on `G₁` that integrates a `𝖴`-invariant function over
  `𝖴∖G₁`.
* `New.RealPlace.gramDiscReal`: 𝗀(Z) = |det Z|² − |D_ϱ|², D_ϱ the leading principal minor of order
  ϱ. In the coordinates `γ_Z` Haar measure has density at least c_G 𝗀(Z)^{|κ|−1}, with
  c_G = `New.Shape.openCellConst` (`New.RealPlace.lintegral_gramSection_le`).
* `New.realFrameGram`: for y in `G₁`, the matrix of hermitian products of the frame vectors with
  their images under y; it sends `γ_Z` to Z when Z lies in the open cell Ω = `New.Shape.openCell`.
* `New.RealPlace.IsBoundedInCell Z P`: Z lies in Ω, and ‖Z⁻¹‖, ‖Z‖ and (1 − |ξ|²)^{−1/2} are at
  most P, where ξ is the last diagonal entry of Z⁻¹.

## Relation to the literature

See `New.Spanning.Bessel.FillingData` for related work.
-/

@[expose] public section

/-!
## An unfolding bound over G₁ for suitable weights

`New.frameMatrix` is the block of a matrix on the frame; the entries of that block above the
diagonal are coordinates on 𝖴⁰∖𝖴.
-/

section BoxVolume

open MeasureTheory New.RealPlace Subgroup

/-- For `1 ≤ R`, the box of families of entries above the diagonal of a `j × j` complex matrix, all
of norm at most `R`, has volume at most `(2 R) ^ (2 j ^ 2)`. -/
lemma New.volume_upperEntries_closedBall_le {j : ℕ} {R : ℝ} (hR : 1 ≤ R) :
    volume (Set.pi ⊤ fun _ : {p : Fin j × Fin j // p.1 < p.2} ↦ Metric.closedBall (0 : ℂ) R) ≤
      ENNReal.ofReal ((2 * R) ^ (2 * j ^ 2)) := by
  -- The box is a product of at most `j ^ 2` discs of area `π R ^ 2 ≤ (2 * R) ^ 2`.
  have h_disc : R ^ 2 * Real.pi ≤ (2 * R) ^ 2 := by nlinarith [Real.pi_le_four, sq_nonneg R]
  have h_card : Fintype.card {p : Fin j × Fin j // p.1 < p.2} ≤ j ^ 2 :=
    (Fintype.card_subtype_le _).trans (by simp [sq])
  suffices h_pow : (R ^ 2 * Real.pi) ^ Fintype.card {p : Fin j × Fin j // p.1 < p.2} ≤
      ((2 * R) ^ 2) ^ j ^ 2 by
    rw [volume_pi, Set.top_eq_univ, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
      Complex.volume_closedBall, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (sq_nonneg R),
      ← ENNReal.ofReal_pow (by positivity), pow_mul]
    exact ENNReal.ofReal_le_ofReal h_pow
  grw [h_disc, pow_le_pow_right₀ (by nlinarith) h_card]

/-- The frame is e₁, …, e_ϱ, z and `frameMatrix s` is the block of `s` on its rows and columns. Let
`w, φ ≥ 0` be measurable functions on `G₁`, `w` left invariant under the Bessel subgroup `besselS`
and `φ` of integral at most `K` on each orbit of `𝖴⁰ = besselU0`, the subgroup of the unipotent
group `𝖴 = besselU` fixing the frame. Suppose that every `s ∈ 𝖴` with `φ y ≠ 0` and `φ (s y) ≠ 0`
for some `y` has `frameMatrix s` with entries of norm at most `R`, where `1 ≤ R`. Then `∫ φ w` over
`G₁` is at most `K (2 R) ^ (2 n ^ 2)`, `n = ϱ + 1`, times the integral of `w` over 𝖴∖G₁. -/
lemma New.lintegral_mul_le_of_frameMatrix_le {𝔰 : Shape} {w φ : 𝔰.G₁ → ENNReal} {K : ENNReal}
    {R : ℝ} (hw : Measurable w) (hφ : Measurable φ) (hw_inv : besselS.FixesLeft w)
    (hK : ∀ y : 𝔰.G₁, ∫⁻ u : (𝔰.middleGram (1 : ℂ)).besselU0, φ (u * y) ∂𝔰.besselHaar₀ ≤ K)
    (hR : ∀ y : 𝔰.G₁, φ y ≠ 0 → ∀ s ∈ besselU, φ (s * y) ≠ 0 → ∀ a b : Fin (𝔰.ϱ + 1),
      ‖frameMatrix s a b‖ ≤ R) (h_one_le : 1 ≤ R) :
    ∫⁻ y : 𝔰.G₁, φ y * w y ≤
      K * ENNReal.ofReal ((2 * R) ^ (2 * 𝔰.n ^ 2)) * ∫⁻ y : 𝔰.G₁, w y ∂besselQuotMeasure := by
  -- Unfold along `besselU`; it suffices to bound the integral of `φ (s * y)` over `s ∈ besselU`.
  -- Write `s = u * liftUnitriangular x * u₀` with `u ∈ besselU0` and `φ (u₀ * y) ≠ 0`: the integral
  -- over `u` is at most `K`, and it vanishes unless all coordinates of `x` have norm at most `R`.
  let box : Set (UpperEntries 𝔰.n) := .pi ⊤ fun _ ↦ Metric.closedBall 0 R
  have inner_le (y : 𝔰.G₁) : ∫⁻ u : (𝔰.middleGram (1 : ℂ)).besselU, φ (u * y) ∂𝔰.besselHaar ≤
      K * .ofReal ((2 * R) ^ (2 * 𝔰.n ^ 2)) := by
    by_cases! hφy : ∀ u : (𝔰.middleGram (1 : ℂ)).besselU, φ (u * y) = 0
    · rw [lintegral_congr hφy, lintegral_zero]
      exact zero_le
    obtain ⟨u₀, hu₀⟩ := hφy
    -- Outside the box the integrand vanishes, by `hR` at `u₀ * y`.
    have h_zero (x : UpperEntries 𝔰.n) (hx : x ∉ box) (u : (𝔰.middleGram (1 : ℂ)).besselU0) :
        φ (u * (liftUnitriangular x * (u₀ * y))) = 0 := by
      refine by_contra fun hu ↦ hx fun ⟨(a, b), hab⟩ _ ↦ ?_
      obtain ⟨hu_mem, hu_frame⟩ := mem_besselU0_iff.1 u.prop
      have h_entry : ‖frameMatrix (u * liftUnitriangular x : 𝔰.G₁) a b‖ ≤ R :=
        hR _ hu₀ _ (mul_mem hu_mem (liftUnitriangular_mem_besselU x)) (by rwa [mul_assoc]) a b
      have h_frame : frameMatrix (u * liftUnitriangular x : 𝔰.G₁) = unitriangularMatrix x := by
        simp [frameMatrix_mul, liftUnitriangular_mem_besselU, hu_frame]
      simpa [h_frame, unitriangularMatrix, hab] using h_entry
    calc
      _ = ∫⁻ x, ∫⁻ u, φ (u.val * (liftUnitriangular x * (u₀.val * y))) ∂𝔰.besselHaar₀ := by
        have h_map : Continuous fun p : UpperEntries 𝔰.n × (𝔰.middleGram (1 : ℂ)).besselU0 ↦
            (⟨p.2.val * liftUnitriangular p.1,
              mul_mem (mem_besselU0_iff.1 p.2.prop).1 (liftUnitriangular_mem_besselU p.1)⟩ :
              (𝔰.middleGram (1 : ℂ)).besselU) :=
          ((continuous_subtypeVal.comp continuous_snd).mul
            (continuous_liftUnitriangular.comp continuous_fst)).subtype_mk _
        have h_fn : Measurable fun u : (𝔰.middleGram (1 : ℂ)).besselU ↦
            φ ((u * u₀ : (𝔰.middleGram (1 : ℂ)).besselU).val * y) :=
          hφ.comp ((continuous_subtypeVal.mul continuous_const).mul continuous_const).measurable
        have h_comp : AEMeasurable
            (fun a : UpperEntries 𝔰.n × (𝔰.middleGram (1 : ℂ)).besselU0 ↦
              φ ((⟨a.2.val * liftUnitriangular a.1,
                mul_mem (mem_besselU0_iff.1 a.2.prop).1 (liftUnitriangular_mem_besselU a.1)⟩ *
                u₀ : (𝔰.middleGram (1 : ℂ)).besselU).val * y))
            (volume.prod 𝔰.besselHaar₀) :=
          (h_fn.comp h_map.measurable).aemeasurable
        rw [← lintegral_mul_right_eq_self _ u₀, Shape.besselHaar,
          lintegral_map h_fn h_map.measurable, lintegral_prod _ h_comp]
        refine lintegral_congr fun x ↦ lintegral_congr fun u ↦ congrArg φ ?_
        simp only [Subgroup.coe_mul, mul_assoc]
      _ = ∫⁻ x in box, ∫⁻ u, φ (u.val * (liftUnitriangular x * (u₀.val * y))) ∂𝔰.besselHaar₀ :=
        (setLIntegral_eq_of_support_subset <|
          Function.support_subset_iff'.2 fun x hx ↦
            (lintegral_congr (h_zero x hx)).trans lintegral_zero).symm
      _ ≤ K * volume box := by grw [hK, setLIntegral_const]
      _ ≤ _ := mul_le_mul' le_rfl (volume_upperEntries_closedBall_le h_one_le)
  have : MeasurableSMul₂ (𝔰.middleGram (1 : ℂ)).besselU 𝔰.G₁ :=
    ⟨((continuous_subtypeVal.comp continuous_fst).mul continuous_snd).measurable⟩
  have : SMulInvariantMeasure (𝔰.middleGram (1 : ℂ)).besselU 𝔰.G₁ volume :=
    ⟨fun c s _ ↦ measure_preimage_mul volume c.val s⟩
  calc _ = ∫⁻ y, ∫⁻ u, φ (u • y) * w (u • y) ∂𝔰.besselHaar ∂besselQuotMeasure :=
      (lintegral_orbitMeasure_lintegral (hφ.mul hw)).symm
    -- The weight `w` is left invariant, so it leaves the inner integral.
    _ = ∫⁻ y, (∫⁻ u, φ (u.val * y) ∂𝔰.besselHaar) * w y ∂besselQuotMeasure := by
      refine lintegral_congr fun y ↦ ?_
      have h_meas : Measurable fun u : (𝔰.middleGram (1 : ℂ)).besselU ↦ φ (u.val * y) :=
        hφ.comp (continuous_subtypeVal.mul continuous_const).measurable
      rw [← lintegral_mul_const _ h_meas]
      refine lintegral_congr fun u ↦ ?_
      rw [smul_def, smul_eq_mul,
        hw_inv u.val (mem_besselS.2 ⟨u.val, u.prop, 1, one_mem _, (mul_one _).symm⟩)]
    _ ≤ _ := by grw [inner_le, lintegral_const_mul _ hw]

end BoxVolume

section SobolevCell

open Complex ComplexOrder Set Metric Function Fintype Matrix MeasureTheory Subgroup Norms.L2Operator
  Real

/-- The index set of the real coordinates on the complex matrices of size `ϱ + 1`: the index
`(0, a, b)` stands for the real part of the entry `(a, b)`, and `(1, a, b)` for its imaginary
part. -/
abbrev New.Shape.FrameCoord (𝔰 : Shape) : Type := Fin 2 × Fin (𝔰.ϱ + 1) × Fin (𝔰.ϱ + 1)

/-- The positions `(a, b)` of the entries of a matrix in `G₁`; they index the matrix units. -/
abbrev New.Shape.EntryIndex (𝔰 : Shape) : Type := 𝔰.BesselIndex × 𝔰.BesselIndex

/-- The product of the Haar measures of `U(κ)` and `𝖴⁰ = besselU0`, times the constant
`openCellConst * c ^ (|κ| - 1)`. The constant is the lower bound of `lintegral_gramSection_le` for
the density of Haar measure of `G₁`, in the coordinates of the open cell, at a matrix `Z` with
`gramDiscReal Z = c`. -/
noncomputable def New.Shape.fixerMeasure (𝔰 : Shape) (c : ℝ) :
    Measure (U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0) :=
  ENNReal.ofReal (𝔰.openCellConst * c ^ (𝔰.k - 1)) • volume.prod 𝔰.besselHaar₀

instance (𝔰 : New.Shape) (c : ℝ) : SFinite (𝔰.fixerMeasure c) :=
  inferInstanceAs (SFinite (_ • _))

/-- The pairs `(h, u)` in `U(κ) × 𝖴⁰`, `𝖴⁰ = besselU0`, such that `u` has operator norm at most
`R`. -/
def New.Shape.fixerBall (𝔰 : Shape) (R : ℝ) :
    Set (U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0) :=
  {ω | ‖(ω.2 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ R}

lemma New.Shape.mem_fixerBall {𝔰 : Shape} {R : ℝ}
    {ω : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0} :
    ω ∈ 𝔰.fixerBall R ↔ ‖(ω.2 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ R :=
  Iff.rfl

lemma New.Shape.measurableSet_fixerBall (𝔰 : Shape) (R : ℝ) : MeasurableSet (𝔰.fixerBall R) :=
  measurableSet_le
    ((Units.continuous_val.comp
      (continuous_subtypeVal.comp (continuous_subtypeVal.comp continuous_snd))).norm.measurable)
    measurable_const

/-- The complex matrices of size `ϱ + 1` have real linear coordinates `e` such that `x ↦ Z + e x`
preserves Lebesgue measure and the operator norm of `e x` is at most `2 (ϱ + 1) ^ 2` times the
supremum norm of `x`. -/
lemma New.RealPlace.exists_real_coordinates {𝔰 : Shape} (Z : 𝔰.FrameMatrix) :
    ∃ e : (𝔰.FrameCoord → ℝ) ≃L[ℝ] 𝔰.FrameMatrix,
      MeasurePreserving (fun x : 𝔰.FrameCoord → ℝ ↦ Z + e x) ∧
      ∀ x : 𝔰.FrameCoord → ℝ, ‖e x‖ ≤ 2 * (𝔰.ϱ + 1) ^ 2 * ‖x‖ := by
  let e : (𝔰.FrameCoord → ℝ) ≃L[ℝ] 𝔰.FrameMatrix :=
    (basisOneI.smulTower (A := 𝔰.FrameMatrix)
      (stdBasis ℂ (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)))).equivFun.symm.toContinuousLinearEquiv
  have e_apply (x : 𝔰.FrameCoord → ℝ) (a b : Fin (𝔰.ϱ + 1)) :
      e x a b = x (0, a, b) + x (1, a, b) * I := by
    simp [e, ite_and, sum_prod_type, stdBasis_eq_single, Matrix.sum_apply, single_apply]
  -- The map `e` matches the sums of squares, so it matches the volumes.
  have h_vol : MeasurePreserving e := HasGaussianIntegral.measurePreserving e.toLinearEquiv
    fun x ↦ show ∑ a, ∑ b, ‖e x a b‖ ^ 2 = ∑ i, x i ^ 2 by
      simp [e_apply, sum_prod_type, ← sq, RCLike.norm_sq_eq_def, Finset.sum_add_distrib]
  refine ⟨e, h_vol.add_left volume Z, fun x ↦ ?_⟩
  have entry_le (a b : Fin (𝔰.ϱ + 1)) : ‖e x a b‖ ≤ 2 * ‖x‖ := by
    grw [e_apply, norm_add_le, norm_mul, norm_I, mul_one, norm_real, norm_real, norm_le_pi_norm,
      norm_le_pi_norm, two_mul]
  grw [l2_opNorm_le_of_apply entry_le, Fintype.card_fin, Nat.cast_succ]
  linarith

/-- Let `8 ≤ P` and let `p` be a curve of complex matrices of size `ϱ + 1` whose derivative at `t`
has operator norm at most `P ^ 2 / 4`. Let `Y = p t` be invertible with |ξ| < 1, ξ the last diagonal
entry of `Y⁻¹` (the open cell), and with ‖Y‖, ‖Y⁻¹‖ and (1 − |ξ|²)^{−1/2} at most `P`
(`IsBoundedInCell`). If `‖k‖ ≤ P ^ 20`, then `g s = gramSection (p s) * k` is differentiable at `t`
and its logarithmic derivative `A = g⁻¹ g'` has norm at most `P ^ 85`. -/
lemma New.RealPlace.exists_hasDerivAt_gramSection_mul_norm_le {𝔰 : Shape} {P t : ℝ}
    {p : ℝ → 𝔰.FrameMatrix} {p' : 𝔰.FrameMatrix} (hP : 8 ≤ P) (hp : HasDerivAt p p' t)
    (hp' : 4 * ‖p'‖ ≤ P ^ 2) (h_cell : IsBoundedInCell (p t) P)
    {k : 𝔰.G₁} (hk : ‖(k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ P ^ 20) :
    ∃ A : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ,
      HasDerivAt
        (fun s : ℝ ↦ ((gramSection (p s) * k : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ))
        ((gramSection (p t) * k : 𝔰.G₁) * A) t ∧
      ‖A‖ ≤ P ^ 85 := by
  have hΩ : p t ∈ 𝔰.openCell := h_cell.mem_openCell
  let D : 𝔰.FrameMatrix →L[ℝ] Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ :=
    fderiv ℝ (fun Z ↦ sectionMatrix Z Zᴴ) (p t)
  obtain ⟨sec_le, D_le⟩ : ‖sectionMatrix (p t) (p t)ᴴ‖ ≤ P ^ 18 ∧ ‖D‖ ≤ P ^ 25 :=
    h_cell.norm_sectionMatrix_le (by linarith)
  have fderiv_sec : HasFDerivAt (fun Z ↦ ↑(gramSection Z)) D (p t) :=
    (differentiableAt_sectionMatrix hΩ).hasFDerivAt.congr_of_eventuallyEq
      (gramSection_eventuallyEq hΩ)
  let g : 𝔰.G₁ := gramSection (p t) * k
  let g' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := D p' * k
  have deriv_g : HasDerivAt (fun s ↦ ↑(gramSection (p s) * k)) g' t :=
    (fderiv_sec.comp_hasDerivAt t hp).mul_const _
  have norm_inv_g : ‖((g⁻¹ : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ P ^ 18 * P ^ 20 := by
    grw [U.norm_inv, coe_mul, Units.val_mul, norm_mul_le, coe_gramSection hΩ, sec_le, hk]
  have speed_le : ‖p'‖ ≤ P ^ 2 := by linarith [norm_nonneg p']
  have norm_g' : ‖g'‖ ≤ P ^ 25 * P ^ 2 * P ^ 20 := by
    grw [norm_mul_le, hk, D.le_opNorm, D_le, speed_le]
  refine ⟨(g⁻¹ : 𝔰.G₁) * g', deriv_g.congr_deriv (Units.mul_inv_cancel_left _ _).symm, ?_⟩
  exact (norm_mul_le_of_le norm_inv_g norm_g').trans_eq (by ring)

/-- Let `s` lie in the unipotent group `𝖴 = besselU`. If `realFrameGram y` and
`realFrameGram (s * y)` are invertible matrices `Z` with |ξ| < 1 and with ‖Z‖, ‖Z⁻¹‖ and
(1 − |ξ|²)^{−1/2} at most `P`, ξ the last diagonal entry of `Z⁻¹` (`IsBoundedInCell`), then the
entries of `frameMatrix s` have norm at most `P ^ 2`. -/
lemma New.RealPlace.norm_frameMatrix_le_of_isBoundedInCell {𝔰 : Shape} {P : ℝ} {s y : 𝔰.G₁}
    (hs : s ∈ besselU) (hy : IsBoundedInCell (realFrameGram y) P)
    (hsy : IsBoundedInCell (realFrameGram (s * y)) P) (a b : Fin (𝔰.ϱ + 1)) :
    ‖frameMatrix s a b‖ ≤ P ^ 2 := by
  have h_adjoint : realFrameGram y * (realFrameGram (s * y))⁻¹ = (frameMatrix s)ᴴ := by
    simp [realFrameGram_eq_frameMatrix_mul y hs, (mem_openCell.1 hsy.mem_openCell).1]
  calc ‖frameMatrix s a b‖
    _ = ‖(realFrameGram y * (realFrameGram (s * y))⁻¹) b a‖ := by simp [h_adjoint]
    _ ≤ ‖realFrameGram y * (realFrameGram (s * y))⁻¹‖ := norm_apply_le_l2_opNorm _ b a
    _ ≤ P * P := norm_mul_le_of_le hy.norm_le hsy.norm_inv_le
    _ = P ^ 2 := (sq P).symm

/-- Let `1 ≤ P` and let `Q` be a measurable set of invertible complex matrices `Z` of size
`n = ϱ + 1` with |ξ| < 1 and with ‖Z‖, ‖Z⁻¹‖ and (1 − |ξ|²)^{−1/2} at most `P`, ξ the last diagonal
entry of `Z⁻¹` (`IsBoundedInCell`), and with `0 < c ≤ gramDiscReal Z` = |det Z|² − |det Z₀|², Z₀ the
upper left `ϱ × ϱ` block. Let `w ≥ 0` be measurable and left invariant under the Bessel subgroup
`besselS`. Then the integral of `w (γ_Z (u h)⁻¹)` over `Z ∈ Q`, `h ∈ U(κ)` and `u ∈ 𝖴⁰ = besselU0`,
with the density `openCellConst * c ^ (|κ| - 1)`, is at most `(2 P ^ 2) ^ (2 n ^ 2)` times the
integral of `w` over 𝖴∖G₁ (`besselQuotMeasure`). -/
lemma New.RealPlace.lintegral_lintegral_gramSection_le {𝔰 : Shape} {P c : ℝ} (hP : 1 ≤ P)
    (hc : 0 < c) {Q : Set 𝔰.FrameMatrix} (hQ : MeasurableSet Q)
    (h_disc : ∀ Z ∈ Q, c ≤ gramDiscReal Z) (h_cell : ∀ Z ∈ Q, IsBoundedInCell Z P)
    {w : 𝔰.G₁ → ENNReal} (hw : Measurable w) (hw_inv : besselS.FixesLeft w) :
    ∫⁻ Z : 𝔰.FrameMatrix in Q,
        ∫⁻ ω : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0,
          w (gramSection Z * ((ω.2 : 𝔰.G₁) * embedH ω.1)⁻¹) ∂𝔰.fixerMeasure c ≤
      ENNReal.ofReal ((2 * P ^ 2) ^ (2 * 𝔰.n ^ 2)) * ∫⁻ γ : 𝔰.G₁, w γ ∂besselQuotMeasure := by
  classical
  -- Let `χ` be a cutoff function for `𝖴⁰` and `χQ` its restriction to `realFrameGram ⁻¹' Q`.
  -- Compare both sides with `∫ χQ w` over `G₁`: by the open cell coordinates and by unfolding.
  obtain ⟨χ, χ_meas, χ_orbit⟩ : ∃ χ : 𝔰.G₁ → ENNReal,
      Measurable χ ∧ ∀ γ, ∫⁻ u, χ (u.val * γ) ∂𝔰.besselHaar₀ = 1 := isUnimodularHaar_besselHaar₀.out
  let χQ : 𝔰.G₁ → ENNReal := (realFrameGram ⁻¹' Q).indicator χ
  have χQ_meas : Measurable χQ := χ_meas.indicator (hQ.preimage (by fun_prop [frameGram]))
  have Q_subset : Q ⊆ 𝔰.openCell := fun Z hZ ↦ (h_cell Z hZ).mem_openCell
  have χQ_orbit (y : 𝔰.G₁) : ∫⁻ u, χQ (u.val * y) ∂𝔰.besselHaar₀ ≤ 1 :=
    (lintegral_mono fun u ↦ indicator_le_self _ χ _).trans_eq (χ_orbit y)
  have χQ_cell (y : 𝔰.G₁) (hy : χQ y ≠ 0) : IsBoundedInCell (realFrameGram y) P :=
    h_cell _ (mem_preimage.1 (mem_of_indicator_ne_zero hy))
  -- Unfolding along `𝖴` costs the volume of the `s ∈ 𝖴`, modulo `𝖴⁰`, whose matrix on the frame
  -- has entries of norm at most `P ^ 2`.
  have unfolding : ∫⁻ γ, χQ γ * w γ ≤
      1 * .ofReal ((2 * P ^ 2) ^ (2 * 𝔰.n ^ 2)) * ∫⁻ γ, w γ ∂besselQuotMeasure :=
    lintegral_mul_le_of_frameMatrix_le hw χQ_meas hw_inv χQ_orbit (fun y hy s hs hsy ↦
      norm_frameMatrix_le_of_isBoundedInCell hs (χQ_cell y hy) (χQ_cell _ hsy)) (one_le_pow₀ hP)
  -- The integrand of `∫ χQ w` in the coordinates `γ_Z` of the open cell.
  let J (Z : 𝔰.FrameMatrix) : ENNReal := .ofReal (𝔰.openCellConst * gramDiscReal Z ^ (𝔰.k - 1)) *
    ∫⁻ s', ∫⁻ s, χQ (s' * gramSection Z * s) * w (s' * gramSection Z * s)
      ∂fixerHaar 𝔰 ∂fixerHaar 𝔰
  have h_xw : Measurable fun γ : 𝔰.G₁ ↦ χQ γ * w γ := χQ_meas.mul hw
  have le_J (Z : 𝔰.FrameMatrix) (hZ : Z ∈ Q) :
      ∫⁻ ω, w (gramSection Z * ((ω.2 : 𝔰.G₁) * embedH ω.1)⁻¹) ∂𝔰.fixerMeasure c ≤ J Z := by
    -- Along an orbit of the fixer only `χ` changes, and its integral over `𝖴⁰` is `1`.
    have h_orbit {r : 𝔰.G₁} (hr : r ∈ besselFixer) :
        ∫⁻ s, χQ (s * gramSection Z * r) * w (s * gramSection Z * r) ∂fixerHaar 𝔰 =
          w (gramSection Z * r) := by
      have h_fiber {s : 𝔰.G₁} (hs : s ∈ besselFixer) :
          χQ (s * gramSection Z * r) * w (s * gramSection Z * r) =
            χ (s * gramSection Z * r) * w (gramSection Z * r) := by
        have h_gram : realFrameGram (s * gramSection Z * r) = Z := by
          simp [(realFrameGram_mul_of_mem_besselFixer _ hr).2,
            (realFrameGram_mul_of_mem_besselFixer _ hs).1,
            realFrameGram_gramSection (Q_subset hZ)]
        simp only [χQ, indicator, mem_preimage, h_gram, ite_eq_left hZ]
        rw [mul_assoc s, hw_inv _ (mem_besselS_of_mem_besselFixer hs)]
      have h_f : Measurable fun s : 𝔰.G₁ ↦ χQ (s * gramSection Z * r) * w (s * gramSection Z * r) :=
        h_xw.comp ((measurable_id.mul_const _).mul_const _)
      rw [lintegral_fixerHaar h_f]
      simp_rw [h_fiber (mul_embedH_mem_besselFixer (Subtype.prop _) _)]
      refine (lintegral_congr fun h ↦ ?_).trans (by rw [lintegral_const, measure_univ, mul_one])
      have h_χ : Measurable fun u : (𝔰.middleGram (1 : ℂ)).besselU0 ↦
          χ (u.val * (embedH h * (gramSection Z * r))) :=
        χ_meas.comp (continuous_subtypeVal.mul continuous_const).measurable
      simp_rw [mul_assoc]
      rw [lintegral_mul_const _ h_χ, χ_orbit, one_mul]
    unfold J
    have h_prod_meas : Measurable fun p : 𝔰.G₁ × 𝔰.G₁ ↦
        χQ (p.1 * gramSection Z * p.2) * w (p.1 * gramSection Z * p.2) :=
      h_xw.comp ((measurable_fst.mul_const _).mul measurable_snd)
    have h_r : Measurable fun r : 𝔰.G₁ ↦
        ∫⁻ s, χQ (s * gramSection Z * r) * w (s * gramSection Z * r) ∂fixerHaar 𝔰 :=
      (h_prod_meas.comp measurable_swap).lintegral_prod_right'
    rw [lintegral_lintegral_swap h_prod_meas.aemeasurable, lintegral_fixerHaar_eq_inv h_r]
    simp_rw [h_orbit (inv_mem (mul_embedH_mem_besselFixer (Subtype.prop _) _))]
    -- On `Q` the density of the open cell is at least the one of `fixerMeasure c`.
    grw [Shape.fixerMeasure, lintegral_smul_measure, smul_eq_mul, ← h_disc Z hZ, lintegral_prod_le]
    exact 𝔰.openCellConst_pos.le
  calc _ ≤ ∫⁻ Z in Q, J Z := setLIntegral_mono' hQ le_J
    _ ≤ ∫⁻ Z in 𝔰.openCell, J Z := lintegral_mono_set Q_subset
    _ ≤ ∫⁻ γ, χQ γ * w γ := lintegral_gramSection_le (f := fun γ ↦ χQ γ * w γ) h_xw
    _ ≤ _ := by rwa [one_mul] at unfolding

/-- The family `V` of functions on `G₁`, indexed by the words in an alphabet `L`, behaves like the
iterated right derivatives of `V []`: along a curve `γ` in `G₁` with `γ' = γ X` and `‖X‖ ≤ C` near
`t`, the function `V w ∘ γ` is differentiable at `t`, with derivative of norm at most `Λ C` times
the sum over the letters `l` of the norms of `V (l :: w) (γ t)`. -/
def New.RealPlace.HasDerivWords {𝔰 : Shape} {I L : Type} [Fintype I] [Fintype L]
    (V : List L → 𝔰.G₁ → EuclideanSpace ℂ I) (Λ : ℝ) : Prop :=
  ∀ (w : List L) (γ : ℝ → 𝔰.G₁) (X : ℝ → Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (C t : ℝ),
    (∀ᶠ s : ℝ in nhds t,
      HasDerivAt (fun s : ℝ ↦ (γ s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) (γ s * X s) s ∧
        ‖X s‖ ≤ C) →
      ∃ v : EuclideanSpace ℂ I,
        HasDerivAt (fun s : ℝ ↦ V w (γ s)) v t ∧ ‖v‖ ≤ ∑ l : L, Λ * C * ‖V (l :: w) (γ t)‖

/-- Let the family `V` satisfy `HasDerivWords V Λ`: along a curve in `G₁` with `γ' = γ X` and
`‖X‖ ≤ C`, the derivative of `V w ∘ γ` exists and has norm at most `Λ C ∑ l, ‖V (l :: w) γ‖`. Let
`P ≥ 8`, and let every `Y` within `P⁻⁶` of `Z` be invertible with |ξ| < 1 and with ‖Y‖, ‖Y⁻¹‖ and
(1 − |ξ|²)^{−1/2} at most `P`, ξ the last diagonal entry of `Y⁻¹` (`IsBoundedInCell`); then
`gramSection Y ∈ G₁` has `Y` as the matrix of hermitian products of the frame vectors e₁, …, e_ϱ, z
with their images. Along a curve `p` of matrices with constant derivative of operator norm at
most `P ^ 2 / 4`, at a time `t₀` with `p t₀` within `P⁻⁶` of `Z`, the function
`t ↦ V w (gramSection (p t) * k)` with `‖k‖ ≤ P ^ 20` is differentiable, with derivative of norm
at most `Λ P ^ 85` times the sum of the norms of the `V (l :: w)` at `gramSection (p t₀) * k`. -/
lemma New.RealPlace.HasDerivWords.exists_hasDerivAt_gramSection_mul {𝔰 : Shape} {I L : Type}
    [Fintype I] [Fintype L] {P Λ t₀ : ℝ} {V : List L → 𝔰.G₁ → EuclideanSpace ℂ I}
    (hV : HasDerivWords V Λ) (hP : 8 ≤ P) {Z : 𝔰.FrameMatrix}
    (h_cell : ∀ Y ∈ ball Z (P ^ 6)⁻¹, IsBoundedInCell Y P)
    {p : ℝ → 𝔰.FrameMatrix} {p' : 𝔰.FrameMatrix}
    (hp : ∀ t : ℝ, HasDerivAt p p' t) (hp' : 4 * ‖p'‖ ≤ P ^ 2) (ht₀ : p t₀ ∈ ball Z (P ^ 6)⁻¹)
    {k : 𝔰.G₁} (hk : ‖(k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ P ^ 20) (w : List L) :
    ∃ v : EuclideanSpace ℂ I,
      HasDerivAt (fun t : ℝ ↦ V w (gramSection (p t) * k)) v t₀ ∧
      ‖v‖ ≤ ∑ l : L, Λ * P ^ 85 * ‖V (l :: w) (gramSection (p t₀) * k)‖ := by
  let γ (t : ℝ) : 𝔰.G₁ := gramSection (p t) * k
  have log_deriv (t : ℝ) (ht : p t ∈ ball Z (P ^ 6)⁻¹) :
      ∃ A : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ,
        HasDerivAt (fun s ↦ ↑(γ s)) (γ t * A) t ∧ ‖A‖ ≤ P ^ 85 :=
    exists_hasDerivAt_gramSection_mul_norm_le hP (hp t) hp' (h_cell _ ht) hk
  choose! X hX using log_deriv
  exact hV w γ X (P ^ 85) t₀ <|
    ((hp t₀).continuousAt.eventually_mem (isOpen_ball.mem_nhds ht₀)).mono hX

/-- The cost of one real coordinate: if `8 ≤ P` and `0 ≤ N Λ ≤ P ^ 44`, the factor
`2 (1 + (N Λ') ^ 2) / ε` of `sobolev_trace_cube` at `ε = P⁻⁸` and `Λ' = Λ P ^ 85`, times `2 P ^ 2`,
is at most `P ^ 275`. -/
lemma New.RealPlace.sobolev_const_mul_le_pow {P N Λ : ℝ} (hP : 8 ≤ P) (h_nonneg : 0 ≤ N * Λ)
    (h_le : N * Λ ≤ P ^ 44) :
    2 / (P ^ 8)⁻¹ * (1 + (N * (Λ * P ^ 85)) ^ 2) * (2 * P ^ 2) ≤ P ^ 275 := by
  have one_le : 1 ≤ P := by linarith
  calc
    _ = 4 * P ^ 10 * (1 + (N * Λ * P ^ 85) ^ 2) := by rw [div_inv_eq_mul]; ring
    _ ≤ 4 * P ^ 10 * (P ^ 258 + (P ^ 44 * P ^ 85) ^ 2) := by
      gcongr
      exact one_le_pow₀ one_le
    _ = 8 * P ^ 268 := by ring
    _ ≤ P ^ 275 := by grw [hP, ← pow_succ', pow_le_pow_right₀ one_le (by norm_num : 268 + 1 ≤ 275)]

/-- For `P ≥ 8 r`, where `r = 𝔰.r` is the size of the matrices in `G₁`, there are real coordinates
`x ↦ Z + e x` on the complex matrices of size `ϱ + 1`, preserving Lebesgue measure, in which the
coordinate vectors have operator norm at most `P ^ 2 / 4` and the cube of the `x` with all
coordinates in `[0, P⁻⁸]` lies within `P⁻⁶` of `Z`. -/
lemma New.RealPlace.exists_real_coordinates_mapsTo_ball {𝔰 : Shape} {P : ℝ} (hP : 8 * 𝔰.r ≤ P)
    (Z : 𝔰.FrameMatrix) :
    ∃ e : (𝔰.FrameCoord → ℝ) ≃L[ℝ] 𝔰.FrameMatrix,
      MeasurePreserving (fun x : 𝔰.FrameCoord → ℝ ↦ Z + e x) ∧
      (∀ j : 𝔰.FrameCoord, 4 * ‖e (Pi.single j 1)‖ ≤ P ^ 2) ∧
      MapsTo (fun x : 𝔰.FrameCoord → ℝ ↦ Z + e x) (Icc 0 fun _ : 𝔰.FrameCoord ↦ (P ^ 8)⁻¹)
        (ball Z (P ^ 6)⁻¹) := by
  -- The size of the matrices is `r = ϱ + (k + 1) + ϱ`.
  replace hP : 8 * ((𝔰.ϱ : ℝ) + (𝔰.k + 1 + 𝔰.ϱ)) ≤ P := by simpa using hP
  have P_pos : 0 < P := hP.trans_lt' (by positivity)
  have h_dim : (16 : ℝ) * (𝔰.ϱ + 1) ^ 2 ≤ P ^ 2 := by nlinarith only [hP]
  obtain ⟨e, e_preserving, norm_e_le⟩ : ∃ e : (𝔰.FrameCoord → ℝ) ≃L[ℝ] 𝔰.FrameMatrix,
      MeasurePreserving (fun x ↦ Z + e x) ∧ ∀ x, ‖e x‖ ≤ 2 * (𝔰.ϱ + 1) ^ 2 * ‖x‖ :=
    exists_real_coordinates Z
  replace norm_e_le (x : 𝔰.FrameCoord → ℝ) : ‖e x‖ ≤ P ^ 2 * ‖x‖ / 8 := by
    grw [norm_e_le, ← h_dim]
    linarith
  refine ⟨e, e_preserving, fun j ↦ ?_, fun x hx ↦ add_mem_ball_iff_norm.2 ?_⟩
  · grw [norm_e_le, Pi.norm_single, norm_one]
    linarith [sq_nonneg P]
  · have norm_x_le : ‖x‖ ≤ (P ^ 8)⁻¹ := by
      simpa [abs_of_pos P_pos] using dist_le_of_mem_pi_Icc hx (left_mem_Icc.2 (hx.1.trans hx.2))
    calc ‖e x‖ ≤ P ^ 2 * (P ^ 8)⁻¹ / 8 := by grw [norm_e_le, norm_x_le]
      _ = (P ^ 6)⁻¹ / 8 := by
        rw [show P ^ 8 = P ^ 2 * P ^ 6 by ring, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero 2 P_pos.ne'), one_mul]
      _ < (P ^ 6)⁻¹ := div_lt_self (by positivity) (by norm_num)

/-- Let `P ≥ 8 r`, where `r = 𝔰.r` is the size of the matrices in `G₁`, and let `n = ϱ + 1`. Let `Z`
be a complex `n × n` matrix (`FrameMatrix`) such that every `Y` within `P⁻⁶` of `Z` is invertible
with |ξ| < 1 and with ‖Y‖, ‖Y⁻¹‖ and (1 − |ξ|²)^{−1/2} at most `P`, ξ the last diagonal entry of
`Y⁻¹` (`IsBoundedInCell`), and has `0 < c ≤ gramDiscReal Y` = |det Y|² − |det Y₀|², Y₀ the upper
left `ϱ × ϱ` block of `Y`. Let `HasDerivWords V Λ` hold: along a curve in `G₁` with `γ' = γ X` and
`‖X‖ ≤ C`, the derivative of `V w ∘ γ` exists and has norm at most `Λ C ∑ l, ‖V (l :: w) γ‖`; let
`0 ≤ Λ` and `card L * Λ ≤ P ^ 44`. Let the `V w` be measurable with norms left invariant under the
Bessel subgroup `besselS`, and let `K` bound their squared norms in `L²(𝖴∖G₁)` (`besselQuotMeasure`)
for the words `w` of length at most `2 n ^ 2`. Then the integral of `‖V [] (γ_Z (u h)⁻¹)‖ ^ 2` over
the `ω = (h, u)` in `U(κ) × 𝖴⁰` with `‖u‖ ≤ P ^ 20` (`fixerBall`), for Haar measure times
`openCellConst * c ^ (|κ| - 1)` (`fixerMeasure`), is at most `P ^ (550 n ^ 2) K`. -/
theorem New.RealPlace.lintegral_gramSection_le_of_hasDerivWords {𝔰 : Shape} {I L : Type}
    [Fintype I] [Fintype L] {P c Λ : ℝ} {Z : 𝔰.FrameMatrix} (hP : 8 * 𝔰.r ≤ P) (hc : 0 < c)
    (h_disc : ∀ Y ∈ ball Z (P ^ 6)⁻¹, c ≤ gramDiscReal Y)
    (h_cell : ∀ Y ∈ ball Z (P ^ 6)⁻¹, IsBoundedInCell Y P)
    {V : List L → 𝔰.G₁ → EuclideanSpace ℂ I} (hV : HasDerivWords V Λ) (hΛ_nonneg : 0 ≤ Λ)
    (hΛ : card L * Λ ≤ P ^ 44) (hV_meas : ∀ w : List L, Measurable (V w))
    (hV_inv : ∀ w : List L, besselS.FixesLeft fun g : 𝔰.G₁ ↦ ‖V w g‖ₑ)
    {K : ENNReal} (hK : ∀ w : List L,
      w.length ≤ 2 * 𝔰.n ^ 2 → ∫⁻ g : 𝔰.G₁, ‖V w g‖ₑ ^ 2 ∂besselQuotMeasure ≤ K) :
    ∫⁻ ω : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0 in 𝔰.fixerBall (P ^ 20),
        ‖V [] (gramSection Z * ((ω.2 : 𝔰.G₁) * embedH ω.1)⁻¹)‖ₑ ^ 2 ∂𝔰.fixerMeasure c ≤
      ENNReal.ofReal (P ^ (550 * 𝔰.n ^ 2)) * K := by
  -- Sobolev's inequality on a cube of side `P⁻⁸` at `Z`, in the `2 n ^ 2` real coordinates of the
  -- matrix; the integrals over the cube are bounded by `lintegral_lintegral_gramSection_le`.
  have one_le_rank : (1 : ℝ) ≤ 𝔰.r := Nat.one_le_cast.2 card_pos
  obtain ⟨eight_le, one_le⟩ : 8 ≤ P ∧ 1 ≤ P := by constructor <;> linarith
  let cube : Set (𝔰.FrameCoord → ℝ) := Icc 0 fun _ ↦ (P ^ 8)⁻¹
  let Q : Set 𝔰.FrameMatrix := ball Z (P ^ 6)⁻¹
  obtain ⟨e, e_preserving, speed_le, e_mapsTo⟩ := exists_real_coordinates_mapsTo_ball hP Z
  have cube_subset : cube ⊆ (fun x ↦ Z + e x) ⁻¹' Q := e_mapsTo.subset_preimage
  let shift (ω : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0) : 𝔰.G₁ :=
    ((ω.2 : 𝔰.G₁) * embedH ω.1)⁻¹
  let f (w : List L) (x : 𝔰.FrameCoord → ℝ)
      (ω : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0) : EuclideanSpace ℂ I :=
    V w (gramSection (Z + e x) * shift ω)
  set μ := 𝔰.fixerMeasure c
  set B := 𝔰.fixerBall (P ^ 20)
  have deriv_bound (ω : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0) (hω : ω ∈ B)
      (w : List L) (j : 𝔰.FrameCoord) (x : 𝔰.FrameCoord → ℝ) (t₀ : ℝ) (ht₀ : update x j t₀ ∈ cube) :
      ∃ f' : EuclideanSpace ℂ I, HasDerivAt (fun t ↦ f w (update x j t) ω) f' t₀ ∧
        ‖f'‖ ≤ ∑ l, Λ * P ^ 85 * ‖f (l :: w) (update x j t₀) ω‖ := by
    have deriv_line (t : ℝ) : HasDerivAt (fun t ↦ Z + e (update x j t)) (e (Pi.single j 1)) t :=
      (e.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x j t)).const_add Z
    have norm_shift : ‖(shift ω : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ P ^ 20 := by
      simp only [shift, _root_.mul_inv_rev, ← map_inv, norm_embedH_mul, U.norm_inv]
      exact Shape.mem_fixerBall.1 hω
    exact hV.exists_hasDerivAt_gramSection_mul eight_le h_cell deriv_line (speed_le j)
      (cube_subset ht₀) norm_shift w
  have h_shift_meas : Measurable shift :=
    ((continuous_subtypeVal.comp continuous_snd).mul
      (continuous_embedH.comp continuous_fst)).inv.measurable
  have hf_meas (w : List L) : Measurable ↿(f w) :=
    (hV_meas w).comp
      (((measurable_gramSection.comp (measurable_const.add e.continuous.measurable)).comp
        measurable_fst).mul (h_shift_meas.comp measurable_snd))
  have cube_bound (w : List L) (hw : w.length ≤ 2 * 𝔰.n ^ 2) :
      ∫⁻ x in cube, ∫⁻ ω in B, ‖f w x ω‖ₑ ^ 2 ∂μ ≤ .ofReal ((2 * P ^ 2) ^ (2 * 𝔰.n ^ 2)) * K := by
    have hw_inv : besselS.FixesLeft fun g : 𝔰.G₁ ↦ ‖V w g‖ₑ ^ 2 :=
      fun s hs g ↦ congrArg (· ^ 2) (hV_inv w s hs g)
    calc
      _ ≤ ∫⁻ x in (fun x ↦ Z + e x) ⁻¹' Q, ∫⁻ ω, ‖f w x ω‖ₑ ^ 2 ∂μ := by
        grw [← cube_subset, setLIntegral_le_lintegral B]
      _ = ∫⁻ Y in Q, ∫⁻ ω, ‖V w (gramSection Y * shift ω)‖ₑ ^ 2 ∂μ :=
        e_preserving.setLIntegral_comp_preimage measurableSet_ball
          (f := fun Y ↦ ∫⁻ ω, ‖V w (gramSection Y * shift ω)‖ₑ ^ 2 ∂μ)
          ((((hV_meas w).comp ((measurable_gramSection.comp measurable_fst).mul
            (h_shift_meas.comp measurable_snd))).eNorm.pow_const 2).lintegral_prod_right')
      _ ≤ .ofReal ((2 * P ^ 2) ^ (2 * 𝔰.n ^ 2)) * ∫⁻ g, ‖V w g‖ₑ ^ 2 ∂besselQuotMeasure :=
        lintegral_lintegral_gramSection_le one_le hc measurableSet_ball h_disc h_cell
          ((hV_meas w).eNorm.pow_const 2) hw_inv
      _ ≤ _ := by grw [hK w hw]
  -- Each of the `2 n ^ 2` coordinates costs `a` in Sobolev's inequality and `2 P ^ 2` on the cube.
  have hcard : card 𝔰.FrameCoord = 2 * 𝔰.n ^ 2 := by
    simp only [Shape.FrameCoord, Shape.n, card_prod, Fintype.card_fin, sq]
  let a : ℝ := 2 / (P ^ 8)⁻¹ * (1 + (card L * (Λ * P ^ 85)) ^ 2)
  have cost_le : a * (2 * P ^ 2) ≤ P ^ 275 := sobolev_const_mul_le_pow eight_le (by positivity) hΛ
  calc
    _ = ∫⁻ ω in B, ‖f [] 0 ω‖ₑ ^ 2 ∂μ := by simp only [f, shift, B, μ, map_zero, add_zero]
    _ ≤ .ofReal (a ^ card 𝔰.FrameCoord) * (.ofReal ((2 * P ^ 2) ^ (2 * 𝔰.n ^ 2)) * K) :=
      sobolev_trace_cube f hf_meas (by positivity)
        (inv_le_one_of_one_le₀ (one_le_pow₀ one_le))
        (ae_restrict_of_forall_mem (𝔰.measurableSet_fixerBall _) deriv_bound)
        fun w hw ↦ cube_bound w (hcard ▸ hw)
    _ = .ofReal ((a * (2 * P ^ 2)) ^ (2 * 𝔰.n ^ 2)) * K := by
      rw [hcard, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    _ ≤ .ofReal ((P ^ 275) ^ (2 * 𝔰.n ^ 2)) * K := by gcongr
    _ = _ := by rw [← pow_mul, show 275 * (2 * 𝔰.n ^ 2) = 550 * 𝔰.n ^ 2 by ring]

/-- The letters `((a, b), c, d)` that index the derivatives of a convolution on `G₁`: `(a, b)` is
the matrix unit along which the function is differentiated, and `c`, `d` select the entries of `y`
and `y⁻¹` that the weight gains. -/
abbrev New.Shape.ConvolutionDerivIndex (𝔰 : Shape) : Type :=
  (𝔰.BesselIndex × 𝔰.BesselIndex) × 𝔰.BesselIndex × 𝔰.BesselIndex

/-- The weight on `G₁` attached to a word, starting from `φ` at the empty word: the letter
`((a, b), c, d)` multiplies the weight at `y` by the entry `(a, d)` of `y⁻¹` and the entry `(c, b)`
of `y`, over `R ^ 2`. -/
noncomputable def New.RealPlace.convolutionWeight {𝔰 : Shape} (R : ℝ) (φ : 𝔰.G₁ → ℂ) :
    List 𝔰.ConvolutionDerivIndex → 𝔰.G₁ → ℂ
  | [] => φ
  | ((a, b), c, d) :: i => fun y ↦ convolutionWeight R φ i y * (y⁻¹.val a d * y.val c b / R ^ 2)

lemma New.RealPlace.convolutionWeight_nil {𝔰 : Shape} (R : ℝ) (φ : 𝔰.G₁ → ℂ) :
    convolutionWeight R φ [] = φ :=
  rfl

lemma New.RealPlace.convolutionWeight_cons {𝔰 : Shape} (R : ℝ) (φ : 𝔰.G₁ → ℂ)
    (a b c d : 𝔰.BesselIndex) (i : List 𝔰.ConvolutionDerivIndex) (y : 𝔰.G₁) :
    convolutionWeight R φ (((a, b), c, d) :: i) y =
      convolutionWeight R φ i y * (y⁻¹.val a d * y.val c b / R ^ 2) :=
  rfl

lemma New.RealPlace.measurable_convolutionWeight {𝔰 : Shape} (R : ℝ) {φ : 𝔰.G₁ → ℂ}
    (hφ : Measurable φ) (i : List 𝔰.ConvolutionDerivIndex) :
      Measurable (convolutionWeight R φ i) := by
  induction i with
  | nil => exact hφ
  | cons l i ih =>
    have hM : Continuous fun y : 𝔰.G₁ ↦ (y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) :=
      Units.continuous_val.comp continuous_subtypeVal
    have h_fac : Continuous fun y : 𝔰.G₁ ↦
        y⁻¹.val l.1.1 l.2.2 * y.val l.2.1 l.1.2 / (R : ℂ) ^ 2 :=
      (((continuous_apply l.2.2).comp ((continuous_apply l.1.1).comp (hM.comp continuous_inv))).mul
        ((continuous_apply l.1.2).comp ((continuous_apply l.2.1).comp hM))).div_const _
    exact ih.mul h_fac.measurable

/-- Let `0 < R` and let the function `φ` on `G₁` vanish at every `y` of operator norm greater than
`R`. The weight `convolutionWeight R φ i` at `y` is `φ y` times one factor for each letter of the
word `i`: an entry of `y⁻¹` times an entry of `y`, divided by `R ^ 2`. Its norm at `y` is at most
`‖φ y‖`. -/
lemma New.RealPlace.norm_convolutionWeight_le {𝔰 : Shape} {R : ℝ} (hR : 0 < R) {φ : 𝔰.G₁ → ℂ}
    (hφ_supp : ∀ y : 𝔰.G₁, φ y ≠ 0 → ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ R)
    (i : List 𝔰.ConvolutionDerivIndex) (y : 𝔰.G₁) : ‖convolutionWeight R φ i y‖ ≤ ‖φ y‖ := by
  induction i with
  | nil => rfl
  | cons l i ih =>
    obtain ⟨⟨a, b⟩, c, d⟩ := l
    grw [convolutionWeight_cons, norm_mul, ih]
    by_cases hy : φ y = 0
    · simp [hy]
    -- Both entries have norm at most `‖y‖ = ‖y⁻¹‖ ≤ R`.
    have entry_le : ‖y.val c b‖ ≤ R := (norm_apply_le_l2_opNorm _ c b).trans (hφ_supp y hy)
    have inv_entry_le : ‖y⁻¹.val a d‖ ≤ R := by
      grw [norm_apply_le_l2_opNorm, U.norm_inv, hφ_supp y hy]
    grw [norm_div, norm_mul, entry_le, inv_entry_le]
    simp [abs_of_pos hR, hR.ne', ← sq]

/-- Let `V w` be bounded continuous functions on `G₁` such that along a curve `γ` in `G₁` with
`γ' = γ X` the derivative of `V w ∘ γ` is `∑ X a b • V ((a, b) :: w) ∘ γ`. Since
`g e^X y = g y e^(y⁻¹ X y)`, a derivative of `g ↦ ∫ ψ i y • V w (g y)` is a sum of such integrals in
which the weight gains an entry of `y⁻¹` and an entry of `y`. If the integrable weights `ψ` carry
these factors divided by `R ^ 2`, the integrals `W i g = ∫ ψ i y • V (i.map Prod.fst) (g y)` satisfy
`HasDerivWords W (R ^ 2)`: along a curve with `γ' = γ X` and `‖X‖ ≤ C` the derivative of `W i ∘ γ`
exists and has norm at most `R ^ 2 C ∑ l, ‖W (l :: i) γ‖`, over the letters `l = ((a, b), c, d)`. -/
lemma New.RealPlace.hasDerivWords_integral {𝔰 : Shape} {I : Type} [Fintype I] {R : ℝ} (hR : 0 < R)
    {V : List 𝔰.EntryIndex → C(𝔰.G₁, EuclideanSpace ℂ I)}
    (V_bounded : ∀ w : List 𝔰.EntryIndex, IsBoundedMeasurable (V w))
    (V_deriv : ∀ (w : List 𝔰.EntryIndex) (γ : ℝ → 𝔰.G₁)
      (X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) (t : ℝ),
      HasDerivAt (fun s : ℝ ↦ (γ s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)) (γ t * X) t →
      HasDerivAt (V w ∘ γ) (∑ a : 𝔰.BesselIndex, ∑ b : 𝔰.BesselIndex, X a b • V ((a, b) :: w) (γ t))
        t)
    {ψ : List 𝔰.ConvolutionDerivIndex → 𝔰.G₁ → ℂ}
    (ψ_cons : ∀ (a b c d : 𝔰.BesselIndex) (i : List 𝔰.ConvolutionDerivIndex) (y : 𝔰.G₁),
      ψ (((a, b), c, d) :: i) y = ψ i y * (y⁻¹.val a d * y.val c b / R ^ 2))
    (ψ_int : ∀ i : List 𝔰.ConvolutionDerivIndex, Integrable (ψ i)) :
    HasDerivWords
      (fun (i : List 𝔰.ConvolutionDerivIndex) (g : 𝔰.G₁) ↦ ∫ y : 𝔰.G₁,
        ψ i y • V (i.map Prod.fst) (g * y))
      (R ^ 2) := by
  -- Differentiate under the integral; the `V w` are bounded and the weights integrable.
  intro i γ X C t₀ h_curve
  let T (i : List 𝔰.ConvolutionDerivIndex) (g y : 𝔰.G₁) : EuclideanSpace ℂ I :=
    ψ i y • V (i.map Prod.fst) (g * y)
  have T_int (i : List 𝔰.ConvolutionDerivIndex) (g : 𝔰.G₁) : Integrable (T i g) :=
    (V_bounded _).integrable_smul (ψ_int i) g
  -- The letter `((a, b), c, d)` enters the derivative with the entry `(d, c)` of `R ^ 2 • X t`.
  let coeff (t : ℝ) : 𝔰.ConvolutionDerivIndex → ℂ := fun (_, c, d) ↦ (R ^ 2 • X t) d c
  let F' (t : ℝ) (y : 𝔰.G₁) : EuclideanSpace ℂ I := ∑ l, coeff t l • T (l :: i) (γ t) y
  let N : Set ℝ := {t | HasDerivAt (fun s ↦ (γ s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ))
    (γ t * X t) t ∧ ‖X t‖ ≤ C}
  have t₀_mem : t₀ ∈ N := h_curve.self_of_nhds
  have coeff_le (t : ℝ) (ht : t ∈ N) (l : 𝔰.ConvolutionDerivIndex) : ‖coeff t l‖ ≤ R ^ 2 * C := by
    grw [norm_apply_le_l2_opNorm, norm_smul, ht.2, Real.norm_of_nonneg (by positivity)]
  have T_deriv (y : 𝔰.G₁) (t : ℝ) (ht : t ∈ N) : HasDerivAt (fun t ↦ T i (γ t) y) (F' t y) t := by
    let Y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := y⁻¹ * X t * y
    have log_deriv : HasDerivAt (fun s ↦ ((γ s * y : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ))
        ((γ t * y : 𝔰.G₁) * Y) t := by simpa [Y, mul_assoc] using ht.1.mul_const _
    -- The entries of `Y = y⁻¹ * X t * y` bring the new factors of the weights.
    have Y_apply (a b : 𝔰.BesselIndex) :
        ψ i y * Y a b = ∑ c, ∑ d, coeff t ((a, b), c, d) * ψ (((a, b), c, d) :: i) y := by
      have hR' : (R : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.2 hR.ne')
      simp only [Y, coeff, ψ_cons, InvMemClass.coe_inv, coe_units_inv, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum, Matrix.smul_apply, real_smul, ofReal_pow]
      refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
      rw [mul_div_assoc', mul_div_assoc', mul_assoc ((R : ℂ) ^ 2), mul_div_cancel_left₀ _ hR']
      ring
    have F'_eq : ψ i y • ∑ a, ∑ b, Y a b • V ((a, b) :: i.map Prod.fst) (γ t * y) = F' t y := by
      simp only [F', T, sum_prod_type, List.map_cons, Finset.smul_sum, smul_smul, Y_apply,
        Finset.sum_smul]
    exact ((V_deriv _ (fun s ↦ γ s * y) Y t log_deriv).fun_const_smul (ψ i y)).congr_deriv F'_eq
  choose M hM using fun w ↦ (V_bounded w).bounded
  have hC : 0 ≤ C := (norm_nonneg _).trans t₀_mem.2
  have F'_le (y : 𝔰.G₁) (t : ℝ) (ht : t ∈ N) :
      ‖F' t y‖ ≤ ∑ l, R ^ 2 * C * (‖ψ (l :: i) y‖ * M ((l :: i).map Prod.fst)) := by
    grw [norm_sum_le, norm_smul_le, coeff_le t ht, norm_smul_le, hM]
  have F'_int : Integrable (F' t₀) :=
    integrable_finsetSum _ fun l _ ↦ (T_int (l :: i) (γ t₀)).smul (coeff t₀ l)
  have deriv_integral : HasDerivAt (fun t ↦ ∫ y, T i (γ t) y) (∫ y, F' t₀ y) t₀ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := N) h_curve
      (.of_forall fun x ↦ (T_int i (γ x)).aestronglyMeasurable)
      (T_int i (γ t₀)) F'_int.aestronglyMeasurable (.of_forall F'_le)
      (integrable_finsetSum _ fun l _ ↦ ((ψ_int (l :: i)).norm.mul_const _).const_mul _)
      (.of_forall T_deriv)).2
  refine ⟨∫ y, F' t₀ y, deriv_integral, ?_⟩
  calc
    _ = ‖∑ l, coeff t₀ l • ∫ y, T (l :: i) (γ t₀) y‖ := by
      rw [show ∫ y, F' t₀ y = ∑ l, coeff t₀ l • ∫ y, T (l :: i) (γ t₀) y from
        (integral_finsetSum (f := fun l y ↦ coeff t₀ l • T (l :: i) (γ t₀) y) Finset.univ
          fun l _ ↦ (T_int (l :: i) (γ t₀)).smul (coeff t₀ l)).trans
          (Finset.sum_congr rfl fun l _ ↦ integral_smul _ _)]
    _ ≤ _ := by grw [norm_sum_le, norm_smul_le, coeff_le t₀ t₀_mem]

/-- Let `P ≥ 8 r`, where `r = 𝔰.r` is the size of the matrices in `G₁`, and let `n = ϱ + 1`. Let `F`
and its iterated right derivatives `V w` be Bessel functions of type `rep`, that is, bounded
functions that transform on the left by a fixed character under the unipotent group `𝖴` and by the
unitary representation `rep` under `U(κ)`, such that `g ↦ ∫ ψ y • V w (g y)` has squared norm at
most `P ^ (2 |w|) D ∫ ‖ψ‖ ^ 2` in `L²(𝖴∖G₁)` when `|w| ≤ 2 n ^ 2` (`HasSchurBound`). Let `Z` be a
complex `n × n` matrix (`FrameMatrix`) such that every `Y` within `P⁻⁶` of `Z` is invertible with
|ξ| < 1 and with ‖Y‖, ‖Y⁻¹‖ and (1 − |ξ|²)^{−1/2} at most `P`, ξ the last diagonal entry of `Y⁻¹`
(`IsBoundedInCell`), and has `0 < c ≤ gramDiscReal Y` = |det Y|² − |det Y₀|², Y₀ the upper left
`ϱ × ϱ` block of `Y`. Let the measurable integrable function `φ` vanish where the operator norm
exceeds `P ^ 20`. Then the integral of `‖∫ φ y • F (γ_Z (u h)⁻¹ y)‖ ^ 2` over the `ω = (h, u)` in
`U(κ) × 𝖴⁰` with `‖u‖ ≤ P ^ 20` (`fixerBall`), for Haar measure times
`openCellConst * c ^ (|κ| - 1)` (`fixerMeasure`), is at most `P ^ (2000 n ^ 2) D ∫ ‖φ‖ ^ 2`. -/
theorem New.RealPlace.lintegral_gramSection_integral_le {𝔰 : Shape} {I : Type} [Fintype I]
    [DecidableEq I] {P c : ℝ} {D : ENNReal} {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ}
    {F : 𝔰.G₁ → EuclideanSpace ℂ I} {Z : 𝔰.FrameMatrix} (hP : 8 * 𝔰.r ≤ P)
    (hF_schur : HasSchurBound F rep P D) (hc : 0 < c)
    (h_disc : ∀ Y ∈ ball Z (P ^ 6)⁻¹, c ≤ gramDiscReal Y)
    (h_cell : ∀ Y ∈ ball Z (P ^ 6)⁻¹, IsBoundedInCell Y P)
    {φ : 𝔰.G₁ → ℂ} (hφ : Measurable φ) (hφ_int : Integrable φ)
    (hφ_supp : ∀ y : 𝔰.G₁, φ y ≠ 0 → ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ P ^ 20) :
    ∫⁻ ω : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0 in 𝔰.fixerBall (P ^ 20),
        ‖∫ y : 𝔰.G₁, φ y • F (gramSection Z * ((ω.2 : 𝔰.G₁) * embedH ω.1)⁻¹ * y)‖ₑ ^ 2
        ∂𝔰.fixerMeasure c ≤
      ENNReal.ofReal (P ^ (2000 * 𝔰.n ^ 2)) * D * ∫⁻ y : 𝔰.G₁, ‖φ y‖ₑ ^ 2 := by
  -- The weighted integrals of the derivatives `V w` of `F` form a family of derivatives whose
  -- first member is `g ↦ ∫ φ y • F (g y)`; apply `lintegral_gramSection_le_of_hasDerivWords`.
  have one_le_rank : (1 : ℝ) ≤ 𝔰.r := Nat.one_le_cast.2 card_pos
  have rank_le : (𝔰.r : ℝ) ≤ P := by linarith
  have one_le : 1 ≤ P := by linarith
  obtain ⟨V, hF, hV⟩ := hF_schur
  have V_bessel (w : List 𝔰.EntryIndex) : IsBesselFunction rep (V w) := (hV w).1
  have V_deriv (w : List 𝔰.EntryIndex) := (hV w).2.1
  have V_schur (w : List 𝔰.EntryIndex) := (hV w).2.2
  let ψ : List 𝔰.ConvolutionDerivIndex → 𝔰.G₁ → ℂ := convolutionWeight (P ^ 20) φ
  have ψ_meas (i : List 𝔰.ConvolutionDerivIndex) : Measurable (ψ i) :=
    measurable_convolutionWeight _ hφ i
  have norm_ψ_le (i : List 𝔰.ConvolutionDerivIndex) (y : 𝔰.G₁) : ‖ψ i y‖ ≤ ‖φ y‖ :=
    norm_convolutionWeight_le (by positivity) hφ_supp i y
  have ψ_int (i : List 𝔰.ConvolutionDerivIndex) : Integrable (ψ i) :=
    hφ_int.mono (ψ_meas i).aestronglyMeasurable (.of_forall (norm_ψ_le i))
  let W (i : List 𝔰.ConvolutionDerivIndex) (g : 𝔰.G₁) : EuclideanSpace ℂ I :=
    ∫ y, ψ i y • V (i.map Prod.fst) (g * y)
  have W_deriv : HasDerivWords W ((P ^ 20) ^ 2) :=
    hasDerivWords_integral (by positivity) (fun w ↦ (V_bessel w).toIsBoundedMeasurable) V_deriv
      (convolutionWeight_cons (P ^ 20) φ) ψ_int
  have W_inv (i : List 𝔰.ConvolutionDerivIndex) : besselS.FixesLeft fun g : 𝔰.G₁ ↦ ‖W i g‖ₑ :=
    fun s hs g ↦ (V_bessel (i.map Prod.fst)).enorm_integral_besselS_mul hs (ψ i) g
  -- There are `r ^ 4` letters, and each costs `(P ^ 20) ^ 2`.
  have letters_le : card 𝔰.ConvolutionDerivIndex * (P ^ 20) ^ 2 ≤ P ^ 44 := by
    calc
      _ = (𝔰.r : ℝ) ^ 4 * P ^ 40 := by
        simp only [card_prod, Nat.cast_mul]
        ring
      _ ≤ P ^ 44 := by grw [rank_le, ← pow_add]
  -- Schur's bound for the derivatives, at the price `P ^ 2` for each letter.
  have schur (i : List 𝔰.ConvolutionDerivIndex) (hi : i.length ≤ 2 * 𝔰.n ^ 2) :
      ∫⁻ g, ‖W i g‖ₑ ^ 2 ∂besselQuotMeasure ≤
        .ofReal (P ^ (2 * (2 * 𝔰.n ^ 2))) * D * ∫⁻ y, ‖φ y‖ₑ ^ 2 := by
    have h_len : (i.map Prod.fst).length ≤ 2 * 𝔰.n ^ 2 := by rwa [List.length_map]
    refine (V_schur (i.map Prod.fst) h_len (ψ i) (ψ_int i)).trans ?_
    rw [List.length_map]
    exact mul_le_mul'
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ one_le (Nat.mul_le_mul_left 2 hi)))
        le_rfl)
      (lintegral_mono fun y ↦ pow_le_pow_left' (eNorm_le_iff_norm_le.2 (norm_ψ_le i y)) 2)
  have W_meas (i : List 𝔰.ConvolutionDerivIndex) : Measurable (W i) :=
    ((((ψ_meas i).comp measurable_snd).smul
      ((V (i.map Prod.fst)).continuous.measurable.comp
        (measurable_fst.mul measurable_snd))).stronglyMeasurable.integral_prod_right').measurable
  calc
    _ ≤ .ofReal (P ^ (550 * 𝔰.n ^ 2)) *
        (.ofReal (P ^ (2 * (2 * 𝔰.n ^ 2))) * D * ∫⁻ y, ‖φ y‖ₑ ^ 2) := by
      simpa only [W, ψ, convolutionWeight_nil, List.map_nil, ← hF] using
        lintegral_gramSection_le_of_hasDerivWords hP hc h_disc h_cell W_deriv (by positivity)
          letters_le W_meas W_inv schur
    _ ≤ _ := by
      grw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← pow_add,
        show 550 * 𝔰.n ^ 2 + 2 * (2 * 𝔰.n ^ 2) ≤ 2000 * 𝔰.n ^ 2 by omega]

end SobolevCell
