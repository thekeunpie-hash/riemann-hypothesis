module

import TauCeti.Analysis.Matrix.L2OpNorm
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import New.Spanning.Bessel.SobolevBound
import Lib.DiscreteSeries.Bessel.SchurBound
import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import Lib.DiscreteSeries.Bruhat.ComplexPlace
import Lib.DiscreteSeries.Haar.TotalMass
import Lib.General.Analysis.GaussianIntegral
import Lib.Shimura.ComplexTheta.AppellHumbertData
import New.Spanning.Unfolding.Link
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Topology.UniformSpace.Uniformizable
public import New.Spanning.Bessel.Basic
import Lib.Adelic.Adeles.AdditiveCharacter
import Lib.Cohomology.Etale.Basic

section
/-!
# Bounds near a point of Ω and the open cell bound for a Bessel system

Write Ω = `New.Shape.openCell`, 𝗀(Z) = |det Z|² − |D_ϱ|² and ν(Z)² = 1 − |ξ|², where ξ is the last
diagonal entry of Z⁻¹. At and near a point `Z` of Ω (so `0 < 𝗀(Z)`) the matrix, its inverse, 𝗀 and ν
obey explicit size bounds. Such bounds on a ball supply the hypothesis of
`New.RealPlace.lintegral_gramSection_integral_le`. For a Bessel system, a family of kernels is then
shown to be an `L²` contraction at each `γ` in `New.Shape.G₁` whose frame Gram matrix lies in Ω,
provided that some `y` and `γ⁻¹ y` both lie in a frame box of large enough size.

## Main definitions and results

* `New.RealPlace.isBoundedInCell_of_inv_le_gramDiscReal`: if `M⁻¹ ≤ 𝗀(Z)` and the entries of `Z` are
  at most `M ^ 2`, a power of `M` bounds the matrix, its inverse and `1 / ν`.
* `New.RealPlace.gramDiscReal_div_two_le_and_isBoundedInCell`: on a small ball about such a `Z` the
  matrix stays in Ω with these bounds, and 𝗀 drops by at most a factor two.
* `New.BesselSystem.exists_isOpenCellBound`: the family of shifted kernels is a contraction from
  `L²(ν)` to `L²(m)`, with `m` a probability measure and `ν` of total mass at most `pairingBoundSq`
  (`New.BesselSystem.IsOpenCellBound`).

Notions from other files:
* `New.RealPlace.gramDiscReal`: 𝗀(Z) = |det Z|² − |D_ϱ|² for a (ϱ+1)×(ϱ+1) complex matrix Z
  (`New.Shape.FrameMatrix`), where D_l (`New.leadingMinor`) is the leading principal minor of order
  l.
* `New.Shape.openCell`: The set of invertible (ϱ+1)×(ϱ+1) complex matrices whose inverse has last
  diagonal entry ξ of absolute value less than 1; `New.RealPlace.oneSubNormSqInvCorner` is
  ν² = 1 − |ξ|².
* `New.RealPlace.gramSection`: For Z in Ω, an element γ_Z of G₁ whose frame Gram matrix
  (`New.realFrameGram`) is Z.
* `New.frameBox`: The set of y in G₁ such that every vector y⁻¹f_a of the moved frame
  (`New.frameVector`) has Euclidean norm at most a given bound.
* `New.besselLength`: For y in G₁, the infimum of ‖sy‖ + 1 over s in the Bessel subgroup S
  (`New.Shape.Form.besselS`).
* `New.BesselSystem 𝔰 B f`: a Bessel function `besselFn .full` on G₁ with values in ℂ^I, its cut
  `besselFn .cut` and their bounds. The real `B ≥ 8 r` (r the rank of G₁) sets the scale of the
  bounds, the natural number `f` the rate of decay, and |I| / `deg` is the constant of Schur's
  bound.

## Relation to the literature

See `New.Spanning.Bessel.FillingData` for related work.
-/

@[expose] public section

/-!
## Sizes at and near a point of Ω

Norms of matrices are `L²` operator norms.
-/

namespace New.RealPlace

open Real Matrix Complex Fintype Metric Norms.L2Operator

/-- A complex matrix of size `l ≤ M` with entries of norm at most `M ^ 2` has operator norm at most
`M ^ 4`. -/
lemma l2_opNorm_le_pow_four {l : ℕ} {M : ℝ} (hl : l ≤ M) {A : Matrix (Fin l) (Fin l) ℂ}
    (hA : ∀ a b : Fin l, ‖A a b‖ ≤ M ^ 2) : ‖A‖ ≤ M ^ 4 := by
  have hl0 : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hM0 : 0 ≤ M := hl0.trans hl
  calc ‖A‖ ≤ (card (Fin l) : ℝ) * card (Fin l) * M ^ 2 := l2_opNorm_le_of_apply hA
    _ = (l : ℝ) * l * M ^ 2 := by rw [card_fin]
    _ ≤ M * M * M ^ 2 := mul_le_mul_of_nonneg_right (mul_le_mul hl hl hl0 hM0) (sq_nonneg M)
    _ = M ^ 4 := by rw [← sq, ← pow_add]

lemma oneSubNormSqInvCorner_le_one {𝔰 : Shape} (Z : 𝔰.FrameMatrix) : oneSubNormSqInvCorner Z ≤ 1 :=
  sub_le_self 1 (sq_nonneg _)

/-- Sizes at a point of Ω. Let `Z` be a complex matrix of size `n = ϱ + 1 ≤ M` with entries of norm
at most `M ^ 2` and with `M⁻¹ ≤ 𝗀(Z)`. Then `Z` lies in Ω, and every `T ≥ M ^ (8 n)` bounds `‖Z⁻¹‖`,
`‖Z‖` and `1 / ν(Z)` (`IsBoundedInCell`). -/
lemma isBoundedInCell_of_inv_le_gramDiscReal {𝔰 : Shape} {M T : ℝ} {Z : 𝔰.FrameMatrix}
    (h_disc : M⁻¹ ≤ gramDiscReal Z) (hM : 𝔰.n ≤ M) (hZ : ∀ a b : Fin (𝔰.ϱ + 1), ‖Z a b‖ ≤ M ^ 2)
    (hT : M ^ (8 * 𝔰.n) ≤ T) : IsBoundedInCell Z T := by
  -- In `M⁻¹ ≤ 𝗀(Z) = |det Z|² ν(Z)²` each factor is bounded above, so each is bounded below.
  have hM_one : 1 ≤ M := (Nat.one_le_cast.2 𝔰.ϱ.succ_pos).trans hM
  have hM_pos : 0 < M := one_pos.trans_le hM_one
  have h_pow (k : ℕ) (hk : k ≤ 8 * 𝔰.n) : M ^ k ≤ T := (pow_le_pow_right₀ hM_one hk).trans hT
  have h_det_le {l : ℕ} (hl : l ≤ 𝔰.n) {A : Matrix (Fin l) (Fin l) ℂ}
      (hA : ∀ a b : Fin l, ‖A a b‖ ≤ M ^ 2) : ‖A.det‖ ≤ (M ^ 4) ^ l := by
    refine norm_det_le_norm_pow.trans ?_
    rw [card_fin]
    exact pow_le_pow_left₀ (norm_nonneg A)
      (l2_opNorm_le_pow_four ((Nat.cast_le.2 hl).trans hM) hA) l
  have h_mem : Z ∈ 𝔰.openCell := mem_openCell_iff.2 (h_disc.trans_lt' (inv_pos.2 hM_pos))
  have h_det_pos : 0 < ‖Z.det‖ := norm_pos_iff.2 h_mem.1
  have h_defect_pos : 0 < oneSubNormSqInvCorner Z := oneSubNormSqInvCorner_pos h_mem
  have h_inv : (‖Z.det‖ * √(oneSubNormSqInvCorner Z))⁻¹ ≤ M := by
    refine inv_le_of_inv_le₀ hM_pos
      (le_of_sq_le_sq ?_ (mul_nonneg h_det_pos.le (Real.sqrt_nonneg _)))
    calc M⁻¹ ^ 2 ≤ M⁻¹ :=
          pow_le_of_le_one (inv_nonneg.2 hM_pos.le) (inv_le_one_of_one_le₀ hM_one) two_ne_zero
      _ ≤ ‖Z.det‖ ^ 2 * oneSubNormSqInvCorner Z :=
        h_disc.trans_eq (gramDiscReal_eq_norm_det_sq_mul h_mem.1)
      _ = (‖Z.det‖ * √(oneSubNormSqInvCorner Z)) ^ 2 := by rw [mul_pow, sq_sqrt h_defect_pos.le]
  refine ⟨h_mem, ?_, (l2_opNorm_le_pow_four hM hZ).trans (h_pow 4 (by dsimp only [Shape.n]; omega)),
    ?_⟩
  · -- Cramer's rule: the entries of the adjugate are minors of size `𝔰.ϱ`, up to sign
    have h_det_inv : ‖Z.det‖⁻¹ ≤ M := by
      have h_le : ‖Z.det‖ * √(oneSubNormSqInvCorner Z) ≤ ‖Z.det‖ :=
        mul_le_of_le_one_right h_det_pos.le
          ((Real.sqrt_le_sqrt (oneSubNormSqInvCorner_le_one Z)).trans_eq Real.sqrt_one)
      exact (inv_anti₀ (mul_pos h_det_pos (Real.sqrt_pos.2 h_defect_pos)) h_le).trans h_inv
    have h_adj (a b : Fin (𝔰.ϱ + 1)) : ‖Z.adjugate a b‖ ≤ (M ^ 4) ^ 𝔰.ϱ := by
      rw [adjugate_fin_succ_eq_det_submatrix, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul]
      exact h_det_le (A := Z.submatrix b.succAbove a.succAbove) 𝔰.ϱ.le_succ fun i j ↦ hZ _ _
    have h_adj_norm : ‖Z.adjugate‖ ≤ M ^ 2 * (M ^ 4) ^ 𝔰.ϱ := by
      calc ‖Z.adjugate‖ ≤ (card (Fin (𝔰.ϱ + 1)) : ℝ) * card (Fin (𝔰.ϱ + 1)) * (M ^ 4) ^ 𝔰.ϱ :=
            l2_opNorm_le_of_apply h_adj
        _ = (𝔰.n : ℝ) * 𝔰.n * (M ^ 4) ^ 𝔰.ϱ := by rw [card_fin]
        _ ≤ M * M * (M ^ 4) ^ 𝔰.ϱ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hM hM (Nat.cast_nonneg _) hM_pos.le)
              (pow_nonneg (pow_nonneg hM_pos.le 4) _)
        _ = M ^ 2 * (M ^ 4) ^ 𝔰.ϱ := by rw [← sq]
    calc ‖Z⁻¹‖ = ‖Z.det‖⁻¹ * ‖Z.adjugate‖ := by
          rw [Z.inv_def, Ring.inverse_eq_inv', norm_smul, norm_inv]
      _ ≤ M * (M ^ 2 * (M ^ 4) ^ 𝔰.ϱ) :=
          mul_le_mul h_det_inv h_adj_norm (norm_nonneg _) hM_pos.le
      _ = M ^ (3 + 4 * 𝔰.ϱ) := by rw [← pow_mul, ← mul_assoc, ← pow_succ', ← pow_add]
      _ ≤ T := h_pow _ (by dsimp only [Shape.n]; omega)
  · calc (√(oneSubNormSqInvCorner Z))⁻¹ ≤ ‖Z.det‖ * M := by
          rwa [mul_inv, inv_mul_le_iff₀ h_det_pos] at h_inv
      _ ≤ M ^ (4 * 𝔰.n + 1) := by
          rw [pow_succ, pow_mul]
          exact mul_le_mul_of_nonneg_right (h_det_le le_rfl hZ) hM_pos.le
      _ ≤ T := h_pow _ (by dsimp only [Shape.n]; omega)

/-- Sizes near a point of Ω. Let `Z` be a complex matrix of size `n = ϱ + 1` and `M ≥ 8 n`, with
`M⁻¹ ≤ 𝗀(Z)` and entries of `Z` of norm at most `M ^ 2`; let `P ≥ M ^ (9 n)`. Every `Z'` at operator
distance less than `(P ^ 6)⁻¹` from `Z` has `𝗀(Z) / 2 ≤ 𝗀(Z')` and satisfies `IsBoundedInCell Z' P`:
it lies in Ω, and `‖Z'⁻¹‖`, `‖Z'‖`, `1 / ν(Z')` are at most `P`. -/
lemma gramDiscReal_div_two_le_and_isBoundedInCell {𝔰 : Shape} {M P : ℝ} {Z Z' : 𝔰.FrameMatrix}
    (h_disc : M⁻¹ ≤ gramDiscReal Z) (hM : 8 * (𝔰.ϱ + 1) ≤ M)
    (hZ : ∀ a b : Fin (𝔰.ϱ + 1), ‖Z a b‖ ≤ M ^ 2) (hP : M ^ (9 * 𝔰.n) ≤ P)
    (hZ' : Z' ∈ ball Z (P ^ 6)⁻¹) :
    gramDiscReal Z / 2 ≤ gramDiscReal Z' ∧ IsBoundedInCell Z' P := by
  -- The number `P / 2` bounds the sizes at `Z`, and `Z'` is a small perturbation of `Z`.
  have hnM : 𝔰.n ≤ M := (Nat.cast_succ 𝔰.ϱ).trans_le (by linarith)
  have hM_one : 1 ≤ M := by linarith
  have h_pow : M ^ (8 * 𝔰.n) ≤ P / 2 := by
    have h_succ : M ^ (8 * 𝔰.n + 1) ≤ P :=
      (pow_le_pow_right₀ hM_one (by dsimp only [Shape.n]; omega)).trans hP
    nlinarith [pow_pos (one_pos.trans_le hM_one) (8 * 𝔰.n), pow_succ M (8 * 𝔰.n)]
  have hM_half : M ≤ P / 2 :=
    (le_self_pow₀ hM_one (by dsimp only [Shape.n]; omega)).trans h_pow
  have h_cell : IsBoundedInCell Z (P / 2) :=
    isBoundedInCell_of_inv_le_gramDiscReal h_disc hnM hZ h_pow
  have hP_pos : 0 < P := by linarith
  have h_near : Z' ∈ ball Z ((P / 2) ^ 6)⁻¹ :=
    ball_subset_ball
      (inv_anti₀ (pow_pos (half_pos hP_pos) 6)
        (pow_le_pow_left₀ (half_pos hP_pos).le (half_le_self hP_pos.le) 6))
      hZ'
  refine ⟨h_cell.gramDiscReal_div_two_le (by linarith) (hnM.trans hM_half) h_near, ?_⟩
  simpa only [mul_div_cancel₀ P two_ne_zero] using h_cell.of_mem_ball (by linarith) h_near

theorem euclidean_enorm_sq_eq_sum {I : Type*} [Fintype I] (u : EuclideanSpace ℂ I) :
    ‖u‖ₑ ^ 2 = ∑ i : I, ‖u i‖ₑ ^ 2 := by
  simp [eNorm_eq_nnNorm, u.nnNorm_eq, ← ENNReal.coe_pow]

end New.RealPlace

/-!
## The open cell bound for a Bessel system

Let `γ` in `New.Shape.G₁` have its frame Gram matrix in the open cell, and let `X` be a Bessel
system (`New.BesselSystem`). For shifts `t` in `besselFixer`, the products of the values of
`X.besselFn` at `γ t y` and at `t y` form a kernel, which is integrated against `φ y` over a compact
set. The mean of its squared norm over the shifts is at most `∫ ‖φ‖² dν` for a finite measure `ν` of
total mass at most `pairingBoundSq`. In this part the letter `Ω` in the code denotes a subset of
`besselU0`.
-/

section OpenCellBound

open Finset Fintype Subgroup Matrix New.RealPlace MeasureTheory Norms.L2Operator ProbabilityTheory
  ENNReal Metric IdemSemiring Measure ComplexConjugate Fin

private lemma mul_conjTranspose_inclMatrix_apply {l m n : Type*} [Fintype m] [DecidableEq n]
    (M : Matrix l m ℂ) (u : m → n) (x : l) (j : n) :
    (M * (New.inclMatrix ℂ u)ᴴ) x j = ∑ k : m, if j = u k then M x k else 0 := by
  rw [Matrix.mul_apply]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [conjTranspose_apply, New.inclMatrix, submatrix_apply, id_eq, Matrix.one_apply,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]

private lemma mul_frameCols_conjTranspose_eStar {𝔰 : New.Shape} {l : Type*}
    (M : Matrix l (Fin (𝔰.ϱ + 1)) ℂ) (x : l) (a : Fin 𝔰.ϱ) :
    (M * 𝔰.frameColsᴴ) x (New.eStar a) = 0 := by
  rw [mul_conjTranspose_inclMatrix_apply]
  refine sum_eq_zero fun k _ ↦ ?_
  have h_ne : New.eStar a ≠ 𝔰.besselFrame k :=
    Fin.lastCases (by simp [New.Shape.besselFrame]) (fun _ ↦ by simp [New.Shape.besselFrame]) k
  simp only [h_ne, ↓reduceIte]

private lemma mul_dualFrameCols_conjTranspose_eStar {𝔰 : New.Shape} {l : Type*}
    (M : Matrix l (Fin (𝔰.ϱ + 1)) ℂ) (x : l) (a : Fin 𝔰.ϱ) :
    (M * 𝔰.dualFrameColsᴴ) x (New.eStar a) = M x a.castSucc := by
  rw [mul_conjTranspose_inclMatrix_apply, sum_univ_castSucc]
  simp only [snoc_castSucc, snoc_last, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, add_zero,
    Finset.sum_ite_eq, mem_univ]

/-- In the columns before the last, the ordinary rows of `sectionCoeff Zᴴ Z` have coefficient
`-1/2` and its last row vanishes. -/
private lemma sectionCoeff_apply_castSucc {𝔰 : New.Shape} (Z : 𝔰.FrameMatrix)
    (i : Fin (𝔰.ϱ + 1)) (a : Fin 𝔰.ϱ) :
    sectionCoeff Zᴴ Z i a.castSucc =
      -(snoc (α := fun _ ↦ ℂ) 1 0 i * (2⁻¹ * Z⁻¹ i 𝔰.top * Zᴴ⁻¹ 𝔰.top a.castSucc)) := by
  induction i using Fin.lastCases with
  | last =>
    simpa [castSucc_ne_last] using sectionCoeff_conjTranspose_top_apply Zᴴ a.castSucc
  | cast i =>
    have h_conj : starRingEnd ℂ (Zᴴ⁻¹ 𝔰.top i.castSucc) = Z⁻¹ i.castSucc 𝔰.top := by
      rw [← conjTranspose_nonsing_inv]
      simp
    simpa [castSucc_ne_last, h_conj, mul_neg, mul_assoc] using
      sectionCoeff_conjTranspose_castSucc_apply Zᴴ i a.castSucc

/-- Let `Z` lie in the open cell `𝔰.openCell`: `Z` is invertible and the last diagonal entry of
`Z⁻¹` has absolute value less than 1. Let `γ_Z = gramSection Z`, an element of the unitary group
`G₁` of the hermitian form `h`, whose frame Gram matrix (the matrix of the products
`h(f_j, γ_Z f_l)`) is `Z`. Let `w` be in `besselU`, the group of block upper unitriangular elements
of `G₁`. Let `Z' = realFrameGram (w γ_Z)`, the matrix of the products `h(f_j, w γ_Z f_l)`. For `z`
in `G₁`, the column of `z⁻¹` at the basis vector `e*_a` (dual to `f_a = e_a`) is a combination of
the moved frames at `w γ_Z z` and at `z`, with coefficients built from the entries of `Z'ᴴ⁻¹`, `Z⁻¹`
and `Zᴴ⁻¹`. Here `BesselIndex` indexes the basis `e_a`, `x_j` (`j` in `κ`), `z₀`, `e*_a`, the frame
is `(f_i) = (e₁, …, e_ϱ, z₀)`, and `frameVector y i = y⁻¹ f_i`. -/
lemma New.inv_apply_eStar_eq_sum_frameVector {𝔰 : Shape} {Z : 𝔰.FrameMatrix}
    (hZ_mem : Z ∈ 𝔰.openCell) {w : 𝔰.G₁} (hw : w ∈ besselU) (z : 𝔰.G₁) (a : Fin 𝔰.ϱ) :
    (WithLp.toLp 2 fun x : 𝔰.BesselIndex ↦ z⁻¹.val x (eStar a)) =
      ∑ i : Fin (𝔰.ϱ + 1), (realFrameGram (w * gramSection Z))ᴴ⁻¹ i a.castSucc •
          frameVector (w * (gramSection Z * z)) i +
        ∑ i : Fin 𝔰.ϱ, (2⁻¹ * Z⁻¹ i.castSucc (.last 𝔰.ϱ) * Zᴴ⁻¹ (.last 𝔰.ϱ) a.castSucc) •
          frameVector z i.castSucc := by
  -- Read the column off the formula `sectionMatrix` for `γ_Z` (`h_sec`), using that `w` acts on
  -- the frame by `frameMatrix w`, which cancels against the factor of `Z` (`h_frame`).
  set γ : 𝔰.G₁ := gramSection Z
  set Z' : 𝔰.FrameMatrix := realFrameGram (w * γ)
  have hZ : Z = (frameMatrix w)ᴴ * Z' :=
    (realFrameGram_gramSection hZ_mem).symm.trans (realFrameGram_eq_frameMatrix_mul _ hw)
  -- `V`, `N`, `L` are the matrices of `z⁻¹`, `(γ z)⁻¹`, `(w γ z)⁻¹`
  let V : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := z.val.val⁻¹
  let N : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := V * γ.val.val⁻¹
  let L : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := N * w.val.val⁻¹
  have hNγ : N * sectionMatrix Z Zᴴ = V := by simp [N, γ, ← coe_gramSection hZ_mem]
  have hLw : L * w.val.val = N := by simp [L]
  have h_sec : V = N + (V * 𝔰.frameCols - N * 𝔰.frameCols) * 𝔰.frameColsᴴ +
      ((N * 𝔰.frameCols * Zᴴ⁻¹ - V * 𝔰.frameCols * sectionCoeff Zᴴ Z) *
          diagLast (𝔰 := 𝔰) (1 - invCorner Z * invCorner Zᴴ).sqrt⁻¹ - N * 𝔰.dualFrameCols) *
        𝔰.dualFrameColsᴴ := by
    have h_cols : N * sectionFrame Z Zᴴ = V * 𝔰.frameCols := by
      rw [← sectionMatrix_mul_frameCols, ← Matrix.mul_assoc, hNγ]
    conv_lhs => rw [← hNγ, sectionMatrix]
    simp only [mul_add, mul_one, Matrix.mul_sub, ← Matrix.mul_assoc, h_cols]
  have h_frame : N * 𝔰.frameCols * Zᴴ⁻¹ = L * 𝔰.frameCols * Z'ᴴ⁻¹ := by
    have h_cancel : frameMatrix w * Zᴴ⁻¹ = Z'ᴴ⁻¹ := by
      rw [hZ, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_inv_rev]
      simp [det_eq_one_of_unitriangular (frameMatrix_unitriangular hw)]
    rw [← hLw, mul_inclMatrix, submatrix_mul_besselFrame hw, ← h_cancel, mul_inclMatrix,
      Matrix.mul_assoc]
  ext x
  have h_L_eq : L = (w * (γ * z))⁻¹.val.val := by
    dsimp only [L, N, V]
    rw [Subgroup.coe_inv, Matrix.coe_units_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Units.val_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have h_V_eq : V = z⁻¹.val.val := by
    dsimp only [V]
    rw [Subgroup.coe_inv, Matrix.coe_units_inv]
  suffices h_main : V x (eStar a) = ∑ i, Z'ᴴ⁻¹ i a.castSucc * L x (𝔰.besselFrame i) +
      ∑ i : Fin 𝔰.ϱ, 2⁻¹ * Z⁻¹ i.castSucc (.last 𝔰.ϱ) * Zᴴ⁻¹ (.last 𝔰.ϱ) a.castSucc *
        V x (.inl i) by
    simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, frameVector, ← h_L_eq, ← h_V_eq,
      Shape.besselFrame, snoc_castSucc]
    exact h_main
  -- the column of `𝔰.dualFrameColsᴴ` at `e*_a` selects the column `a`; that of `𝔰.frameColsᴴ` is 0
  have h_col : V x (eStar a) = (L * 𝔰.frameCols * Z'ᴴ⁻¹) x a.castSucc -
      (V * 𝔰.frameCols * sectionCoeff Zᴴ Z) x a.castSucc := by
    conv_lhs => rw [h_sec, h_frame]
    rw [Matrix.add_apply, Matrix.add_apply, mul_frameCols_conjTranspose_eStar, add_zero,
      mul_dualFrameCols_conjTranspose_eStar, Matrix.sub_apply, diagLast, Matrix.mul_diagonal]
    simp only [snoc_castSucc, Pi.one_apply, mul_one, Matrix.sub_apply, mul_inclMatrix,
      submatrix_apply, id_eq]
    ring
  rw [h_col, mul_inclMatrix, mul_inclMatrix, Matrix.mul_apply, Matrix.mul_apply, sub_eq_add_neg]
  congr 1
  · exact sum_congr rfl fun i _ ↦ by rw [submatrix_apply, id_eq, mul_comm]
  · rw [sum_univ_castSucc, sectionCoeff_apply_castSucc, snoc_last, zero_mul, neg_zero, mul_zero,
      add_zero, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [submatrix_apply, id_eq, Shape.besselFrame, snoc_castSucc, sectionCoeff_apply_castSucc,
      snoc_castSucc, Pi.one_apply, one_mul, mul_neg, neg_neg, mul_comm]

/-- A bound for `‖z‖` from the length of `γ_Z z`. Let `n = 𝔰.n = ϱ + 1`, `8 n ≤ M` and
`M ^ (9 n) ≤ R`. Let `M⁻¹ ≤ gramDiscReal Z`, the number |det Z|² − |D_ϱ|² with D_ϱ the leading
principal minor of order ϱ, so that `Z` lies in the open cell, and let `‖Z⁻¹‖ ≤ R`. Suppose that the
vectors `z⁻¹ f_a` of the moved frame have norm at most `M` (`frameBox`), where the frame
`(f_a) = (e₁, …, e_ϱ, z₀)` consists of ϱ + 1 fixed basis vectors of the space on which `G₁` acts,
and that `besselLength (γ_Z z)`, the infimum of `‖s γ_Z z‖ + 1` over `s` in the Bessel subgroup, is
at most `M`. Then the operator norm of `z` is at most `R ^ 5`. -/
lemma New.norm_le_of_besselLength_gramSection_mul_le {𝔰 : Shape} {M R : ℝ} {Z : 𝔰.FrameMatrix}
    {z : 𝔰.G₁} (h_size_le : 8 * (𝔰.ϱ + 1) ≤ M) (h_pow_le : M ^ (9 * 𝔰.n) ≤ R)
    (h_disc : M⁻¹ ≤ gramDiscReal Z) (hZ_inv : ‖Z⁻¹‖ ≤ R) (hz : z ∈ frameBox M)
    (h_length : besselLength (gramSection Z * z) ≤ M) :
    ‖(z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ R ^ 5 := by
  -- Move `gramSection Z * z` by a unipotent `w` to a point `y` of norm at most `M`. The columns of
  -- `z⁻¹` at the dual vectors are combinations of the frames at `y` and at `z` with bounded
  -- coefficients.
  have hM : 1 ≤ M := by linarith
  have hnM : 𝔰.n ≤ M := (Nat.cast_succ 𝔰.ϱ).trans_le (by linarith)
  have hMR : M ≤ R := (le_self_pow₀ hM (by dsimp only [Shape.n]; omega)).trans h_pow_le
  have hZ_mem : Z ∈ 𝔰.openCell :=
    mem_openCell_iff.2 (h_disc.trans_lt' (inv_pos.2 (one_pos.trans_le hM)))
  have hR : 1 ≤ R := hM.trans hMR
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hϱR : 8 * (𝔰.ϱ + 1) ≤ R := h_size_le.trans hMR
  obtain ⟨w, hw, hw_le⟩ := exists_norm_le_of_besselLength_le h_length
  set y : 𝔰.G₁ := w * (gramSection Z * z) with hy_def
  set Z' : 𝔰.FrameMatrix := realFrameGram (w * gramSection Z) with hZ'_def
  have hy_frame (a : Fin (𝔰.ϱ + 1)) : ‖frameVector y a‖ ≤ M := (norm_frameVector_le a).trans hw_le
  have hz_frame (a : Fin (𝔰.ϱ + 1)) : ‖frameVector z a‖ ≤ M := hz a
  -- `Z'` has entries at most `M ^ 2` and the same `gramDiscReal` as `Z`; this bounds its inverse.
  have hZ'_norm : ‖Z'⁻¹‖ ≤ R := by
    have h_disc_eq : gramDiscReal Z' = gramDiscReal Z := by
      have h1 := Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU
        (γ := w * gramSection Z) hw (one_mem _) 1
      rw [inv_mul_cancel_left, mul_one] at h1
      change frameDisc 1 (realFrameGram (gramSection Z)) = frameDisc 1 Z' at h1
      rw [realFrameGram_gramSection hZ_mem] at h1
      exact congrArg Complex.re h1.symm
    have h_entry (a b : Fin (𝔰.ϱ + 1)) : ‖Z' a b‖ ≤ M ^ 2 := by
      have hz_eq : (w * gramSection Z)⁻¹ * y = z := by
        rw [hy_def, ← mul_assoc w, inv_mul_cancel_left]
      refine (norm_realFrameGram_le_mul (w * gramSection Z) y a b).trans ?_
      rw [hz_eq, sq]
      exact mul_le_mul (hy_frame a) (hz_frame b) (norm_nonneg _) (zero_le_one.trans hM)
    exact (isBoundedInCell_of_inv_le_gramDiscReal (h_disc.trans_eq h_disc_eq.symm) hnM h_entry
      ((pow_le_pow_right₀ hM (by dsimp only [Shape.n]; omega)).trans h_pow_le)).norm_inv_le
  -- A column has norm at most `(ϱ + 1) R ^ 2 + ϱ R ^ 3 / 2 ≤ R ^ 4`.
  have h_col (a : Fin 𝔰.ϱ) :
      ‖WithLp.toLp 2 fun x : 𝔰.BesselIndex ↦ z⁻¹.val x (eStar a)‖ ≤ R ^ 4 := by
    have h_count : 𝔰.ϱ + 1 + 𝔰.ϱ * R / 2 ≤ R ^ 2 := by nlinarith only [hϱR, hR]
    rw [inv_apply_eStar_eq_sum_frameVector hZ_mem hw, ← hy_def, ← hZ'_def]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)).trans ?_
    calc _ ≤ ∑ i : Fin (𝔰.ϱ + 1), R * R + ∑ i : Fin 𝔰.ϱ, ‖(2⁻¹ : ℂ)‖ * R * R * R := by
          refine add_le_add (sum_le_sum fun i _ ↦ ?_) (sum_le_sum fun i _ ↦ ?_)
          · rw [norm_smul, ← conjTranspose_nonsing_inv, conjTranspose_apply, norm_star]
            exact mul_le_mul ((norm_apply_le_l2_opNorm _ _ _).trans hZ'_norm)
              ((hy_frame i).trans hMR) (norm_nonneg _) hR0
          · rw [norm_smul, norm_mul, norm_mul, ← conjTranspose_nonsing_inv, conjTranspose_apply,
              norm_star]
            refine mul_le_mul ?_ ((hz_frame i.castSucc).trans hMR) (norm_nonneg _)
              (mul_nonneg (mul_nonneg (norm_nonneg _) hR0) hR0)
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left ((norm_apply_le_l2_opNorm _ _ _).trans hZ_inv)
                (norm_nonneg _))
              ((norm_apply_le_l2_opNorm _ _ _).trans hZ_inv) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hR0)
      _ = R ^ 2 * (𝔰.ϱ + 1 + 𝔰.ϱ * R / 2) := by
          rw [Fin.sum_const, Fin.sum_const, nsmul_eq_mul, nsmul_eq_mul, norm_inv,
            Complex.norm_ofNat, Nat.cast_succ]
          ring
      _ ≤ R ^ 4 := (mul_le_mul_of_nonneg_left h_count (sq_nonneg R)).trans_eq (by rw [← pow_add])
  have hz_box : z ∈ frameBox (R ^ 4) :=
    fun a ↦ (hz a).trans (hMR.trans (le_self_pow₀ hR four_ne_zero))
  calc _ ≤ ‖(z : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ + 1 := (lt_add_one _).le
    _ ≤ 8 * (𝔰.ϱ + 1) * R ^ 4 := norm_add_one_le_of_mem_frameBox z hz_box (one_le_pow₀ hR) h_col
    _ ≤ R ^ 5 := (mul_le_mul_of_nonneg_right hϱR (pow_nonneg hR0 4)).trans_eq (pow_succ' R 4).symm

/-- Let `W` be a Bessel function on the unitary group `G₁` with values in `ℂ^I`. It is bounded and
measurable. Under left translation it transforms in two ways: by the character
`n ↦ wave (simpleRootSum n)` of the block unitriangular subgroup `besselU`, where `simpleRootSum n`
is the sum of the entries of `n` just above the diagonal on the frame; and by the unitary
representation `rep` of the unitary group `U(κ)` of the positive definite middle part. Let `ψ` be
integrable and let `s, t` lie in the Bessel subgroup `besselS`, which these two groups generate. The
squared Hilbert–Schmidt norm of the integral of `ψ y * W (s * g * y) ⊗ conj (W (t * y))` does not
depend on `s` and `t`. It equals the sum of the squared norms of the columns at `s = t = 1`. -/
lemma New.sum_enorm_sq_integral_mul_star {𝔰 : Shape} {I : Type*} [Fintype I] [DecidableEq I]
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {W : 𝔰.G₁ → EuclideanSpace ℂ I}
    (hW : IsBesselFunction rep W) {ψ : 𝔰.G₁ → ℂ} (hψ : Integrable ψ) {s t : 𝔰.G₁}
    (hs : s ∈ besselS) (ht : t ∈ besselS) (g : 𝔰.G₁) :
    ∑ i : I × I, ‖∫ y : 𝔰.G₁, ψ y * (W (s * g * y) i.1 * star (W (t * y) i.2))‖ₑ ^ 2 =
      ∑ j : I, ‖∫ y : 𝔰.G₁, (ψ y * star (W y j)) • W (g * y)‖ₑ ^ 2 := by
  -- the norm of a mean of `W` is invariant under `besselS`; read this in coordinates
  have h_coord {β : 𝔰.G₁ → ℂ} (hβ : Integrable β) (b : 𝔰.G₁) :
      ‖∫ y, β y • W (b * y)‖ₑ ^ 2 = ∑ i, ‖∫ y, β y * W (b * y) i‖ₑ ^ 2 := by
    simp only [euclidean_enorm_sq_eq_sum, eval_integral_piLp (hW.integrable_smul hβ b).eval_piLp,
      PiLp.smul_apply, smul_eq_mul]
  have h_invariant {β : 𝔰.G₁ → ℂ} (hβ : Integrable β) {a : 𝔰.G₁} (ha : a ∈ besselS) (b : 𝔰.G₁) :
      ∑ i, ‖∫ y, β y * W (a * b * y) i‖ₑ ^ 2 = ∑ i, ‖∫ y, β y * W (b * y) i‖ₑ ^ 2 := by
    rw [← h_coord hβ, hW.enorm_integral_besselS_mul ha, h_coord hβ]
  -- each row: conjugate the integrals and remove `t`
  have h_row (i : I) : ∑ j, ‖∫ y, ψ y * (W (s * g * y) i * star (W (t * y) j))‖ₑ ^ 2 =
      ∑ j, ‖∫ y, ψ y * star (W y j) * W (s * g * y) i‖ₑ ^ 2 := by
    have h_int : Integrable fun y ↦ star (ψ y * W (s * g * y) i) :=
      Complex.conjCLE.integrable_comp_iff.mpr ((hW.integrable_smul hψ (s * g)).eval_piLp i)
    have h_conj : ∑ j, ‖∫ y, conj (star (ψ y * W (s * g * y) i) * W (t * 1 * y) j)‖ₑ ^ 2 =
        ∑ j, ‖∫ y, conj (star (ψ y * W (s * g * y) i) * W (1 * y) j)‖ₑ ^ 2 := by
      simp only [integral_conj, RCLike.eNorm_conj, h_invariant h_int ht 1]
    have h_lhs (j : I) :
        (fun y : 𝔰.G₁ ↦ ψ y * (W (s * g * y) i * star (W (t * y) j))) =
        (fun y : 𝔰.G₁ ↦ conj (star (ψ y * W (s * g * y) i) * W (t * 1 * y) j)) := by
      funext y
      rw [mul_one, map_mul, Complex.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
        mul_assoc (ψ y)]
    have h_rhs (j : I) :
        (fun y : 𝔰.G₁ ↦ conj (star (ψ y * W (s * g * y) i) * W (1 * y) j)) =
        (fun y : 𝔰.G₁ ↦ ψ y * star (W y j) * W (s * g * y) i) := by
      funext y
      rw [one_mul, map_mul, Complex.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply,
        mul_assoc (ψ y), mul_comm (W (s * g * y) i), ← mul_assoc (ψ y)]
    simp_rw [h_lhs, ← h_rhs]
    exact h_conj
  -- each column: remove `s`
  have h_int (j : I) : Integrable fun y ↦ ψ y * star (W y j) :=
    hψ.mul_of_top_left (hW.memLp_top.eval_piLp j).star
  rw [sum_prod_type, sum_congr rfl fun i _ ↦ h_row i, Finset.sum_comm]
  exact sum_congr rfl fun j _ ↦ (h_invariant (h_int j) hs g).trans (h_coord (h_int j) g).symm

/-- Let `0 < 𝗀(Z)`, where 𝗀(Z) = |det Z|² − |D_ϱ|² is `gramDiscReal`, D_ϱ the leading principal
minor of order ϱ. If the entries of `Z` have norm at most `ρ ^ 2` and `n ≤ ρ`, where `n = ϱ + 1` is
the size of `Z`, then `𝗀(Z) ≤ ρ ^ (8 n)`. -/
lemma New.gramDiscReal_le_pow {𝔰 : Shape} {ρ : ℝ} {Z : 𝔰.FrameMatrix} (hZ : 0 < gramDiscReal Z)
    (hρ_n : 𝔰.n ≤ ρ) (hZρ : ∀ a c : Fin (𝔰.ϱ + 1), ‖Z a c‖ ≤ ρ ^ 2) :
    gramDiscReal Z ≤ ρ ^ (8 * 𝔰.n) := by
  have h_det : ‖Z.det‖ ≤ (ρ ^ 4) ^ 𝔰.n := by
    refine norm_det_le_norm_pow.trans ?_
    rw [Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg Z) (l2_opNorm_le_pow_four hρ_n hZρ) 𝔰.n
  calc gramDiscReal Z = ‖Z.det‖ ^ 2 * oneSubNormSqInvCorner Z :=
         gramDiscReal_eq_norm_det_sq_mul (mem_openCell_iff.2 hZ).1
    _ ≤ ((ρ ^ 4) ^ 𝔰.n) ^ 2 * 1 :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h_det 2) (oneSubNormSqInvCorner_le_one Z)
          (oneSubNormSqInvCorner_pos (mem_openCell_iff.2 hZ)).le (sq_nonneg _)
    _ = ρ ^ (8 * 𝔰.n) := by
        rw [mul_one, ← pow_mul, ← pow_mul, show 4 * (𝔰.n * 2) = 8 * 𝔰.n by omega]

/-- If `0 < 𝗀(Z)` and `1 ≤ ρ`, then `(ρ ^ N / 𝗀(Z))⁻¹ ≤ 𝗀(Z)`; here 𝗀(Z) is `gramDiscReal Z`, the
number |det Z|² − |D_ϱ|² with D_ϱ the leading principal minor of order ϱ. -/
lemma New.inv_pow_div_gramDiscReal_le {𝔰 : Shape} {ρ : ℝ} {Z : 𝔰.FrameMatrix}
    (hZ : 0 < gramDiscReal Z) (hρ_one : 1 ≤ ρ) (N : ℕ) :
    (ρ ^ N / gramDiscReal Z)⁻¹ ≤ gramDiscReal Z :=
  (inv_div _ _).trans_le (div_le_self hZ.le (one_le_pow₀ hρ_one))

/-- Let `0 < 𝗀(Z)`, where 𝗀(Z) = |det Z|² − |D_ϱ|² is `gramDiscReal`, D_ϱ the leading principal
minor of order ϱ. Let `n ≤ ρ` and `1 ≤ ρ` with `n = ϱ + 1`, and let the entries of `Z` have norm at
most `ρ ^ 2`. Then `ρ ≤ ρ ^ (9 n) / 𝗀(Z)`. -/
lemma New.le_pow_div_gramDiscReal {𝔰 : Shape} {ρ : ℝ} {Z : 𝔰.FrameMatrix} (hZ : 0 < gramDiscReal Z)
    (hρ_n : 𝔰.n ≤ ρ) (hρ_one : 1 ≤ ρ) (hZρ : ∀ a c : Fin (𝔰.ϱ + 1), ‖Z a c‖ ≤ ρ ^ 2) :
    ρ ≤ ρ ^ (9 * 𝔰.n) / gramDiscReal Z := by
  rw [le_div_iff₀ hZ]
  calc ρ * gramDiscReal Z ≤ ρ * ρ ^ (8 * 𝔰.n) :=
        mul_le_mul_of_nonneg_left (gramDiscReal_le_pow hZ hρ_n hZρ) (zero_le_one.trans hρ_one)
    _ = ρ ^ (8 * 𝔰.n + 1) := (pow_succ' ρ _).symm
    _ ≤ ρ ^ (9 * 𝔰.n) := pow_le_pow_right₀ hρ_one (by dsimp only [Shape.n]; omega)

/-- Let `W = X.besselFn .full` be the Bessel function of a Bessel system `X` before its cut, with
values in `ℂ^I`, `I = X.Index`; the scale `B` and the rate of decay `f` of `X` do not enter the
bound. Let `A` be a measurable set of elements of operator norm at most `R`, `1 ≤ R`, in `G₁`, the
unitary group of the form with middle block `middleGram 1 = diag(1, …, 1, -1)`. Suppose that for
every `y` the set of `u` in the frame-fixing unipotent subgroup `besselU0` with `u y ∈ A` has Haar
measure (`besselHaar₀`) at most `K`. Then `∫_A ‖W‖ ^ 2 ≤ K (2 R²) ^ (2 n²) |I|`, where
`n = 𝔰.n = ϱ + 1`. -/
lemma New.BesselSystem.lintegral_indicator_mul_enorm_sq_le {𝔰 : Shape} {B : ℝ} {f : ℕ}
    (X : BesselSystem 𝔰 B f) {A : Set 𝔰.G₁} {R : ℝ} {K : ℝ≥0∞} (hA : MeasurableSet A) (hR : 1 ≤ R)
    (hA_norm : ∀ y ∈ A, ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ R)
    (h_fibre : ∀ y : 𝔰.G₁, ∫⁻ u : besselU0 (T := 𝔰.middleGram (1 : ℂ)),
      A.indicator 1 (u * y) ∂𝔰.besselHaar₀ ≤ K) :
    ∫⁻ y : 𝔰.G₁, A.indicator 1 y * ‖X.besselFn .full y‖ₑ ^ 2 ≤
      K * .ofReal ((2 * (R * R)) ^ (2 * 𝔰.n ^ 2)) * card X.Index := by
  have hW : IsBesselFunction X.rep (X.besselFn .full) := X.isCutPair.isBesselFunction .full
  -- an `s` with `y` and `s * y` in `A` has norm at most `R * R`, so its entries lie in a disc
  have h_frame (y : 𝔰.G₁) (hy : A.indicator (1 : 𝔰.G₁ → ℝ≥0∞) y ≠ 0) (s : 𝔰.G₁) (_ : s ∈ besselU)
      (hsy : A.indicator (1 : 𝔰.G₁ → ℝ≥0∞) (s * y) ≠ 0) (a b : Fin (𝔰.ϱ + 1)) :
      ‖frameMatrix s a b‖ ≤ R * R :=
    (norm_apply_le_l2_opNorm _ (𝔰.besselFrame a) (𝔰.besselFrame b)).trans <| by
      simpa using norm_mul_le_of_le (hA_norm _ (Set.mem_of_indicator_ne_zero hsy))
        ((U.norm_inv y).trans_le (hA_norm y (Set.mem_of_indicator_ne_zero hy)))
  have h_invariant : besselS.FixesLeft fun y : 𝔰.G₁ ↦ ‖X.besselFn .full y‖ₑ ^ 2 :=
    fun s hs y ↦ by dsimp only; rw [hW.enorm_besselS_mul hs]
  -- unfold along `besselU0` (`h_fibre`), then along the frame entries, which lie in discs
  have h_le := lintegral_mul_le_of_frameMatrix_le (hW.stronglyMeasurable.eNorm.pow_const 2)
    (measurable_one.indicator hA) h_invariant h_fibre h_frame (one_le_mul_of_one_le_of_one_le hR hR)
  rwa [X.isCutPair.lintegral_sq_full_eq] at h_le

/-- Let `W` be a continuous Bessel function on the unitary group `G₁`. Let `A` be compact, `g`
measurable, and `s` and all `t x` in the Bessel subgroup `besselS`. Suppose that
`∫_S ‖∫ β y • W (g x * y)‖² dμ(x) ≤ K ∫ ‖β‖²` for all measurable integrable weights `β` that vanish
off `A`. Then the kernel `W (s * g x * y) ⊗ conj (W (t x * y))`, integrated against volume on `A`,
has operator norm at most one (`IsL2Contraction`) from `L²` of `(μ S)⁻¹ K` times the measure of
density `‖W‖²` on `A` to `L²` of `μ` conditioned on `S`. -/
lemma New.isL2Contraction_of_columns {𝔰 : Shape} {I : Type*} [Fintype I] [DecidableEq I]
    {rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ} {W : C(𝔰.G₁, EuclideanSpace ℂ I)}
    (hW : IsBesselFunction rep W) {A : Set 𝔰.G₁} (hA : IsCompact A)
    {T : Type*} [MeasurableSpace T] {μ : Measure T} {S : Set T} {s : 𝔰.G₁} {g t : T → 𝔰.G₁}
    (hs : s ∈ besselS) (ht : ∀ x : T, t x ∈ besselS) (hg : Measurable g) {K : ℝ≥0∞}
    (h_bound : ∀ β : 𝔰.G₁ → ℂ, Measurable β → Integrable β → Function.support β ⊆ A →
      ∫⁻ x : T in S, ‖∫ y : 𝔰.G₁, β y • W (g x * y)‖ₑ ^ 2 ∂μ ≤ K * ∫⁻ y : 𝔰.G₁, ‖β y‖ₑ ^ 2) :
    IsL2Contraction μ[|S] (volume.restrict A)
      (((μ S)⁻¹ * K) • volume.withDensity fun y : 𝔰.G₁ ↦ A.indicator 1 y * ‖W y‖ₑ ^ 2)
      fun (i : I × I) (x : T) (y : 𝔰.G₁) ↦ W (s * g x * y) i.1 * conj (W (t x * y) i.2) := by
  -- Apply `h_bound` column by column, to the weights `β j`.
  intro φ C hφ hC
  have hA_meas : MeasurableSet A := hA.measurableSet
  have hψ : Integrable (A.indicator φ) := (volume.integrableOn_of_bounded hA.measure_ne_top
    hφ.aestronglyMeasurable (.of_forall hC)).integrable_indicator hA_meas
  let β (j : I) (y : 𝔰.G₁) : ℂ := A.indicator φ y * star (W y j)
  have hβ_meas (j : I) : Measurable (β j) :=
    (hφ.indicator hA_meas).mul
      (continuous_star.comp ((PiLp.continuous_apply 2 _ j).comp W.continuous)).measurable
  have hβ (j : I) : Integrable (β j) := hψ.mul_of_top_left (hW.memLp_top.eval_piLp j).star
  have h_columns (x : T) :
      ∑ i : I × I, ‖∫ y in A, φ y * (W (s * g x * y) i.1 * star (W (t x * y) i.2))‖ₑ ^ 2 =
        ∑ j, ‖∫ y, β j y • W (g x * y)‖ₑ ^ 2 := by
    rw [← sum_enorm_sq_integral_mul_star hW hψ hs (ht x)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← integral_indicator hA_meas]
    congr 2
    exact integral_congr_ae (.of_forall fun y ↦ Set.indicator_mul_left A φ _)
  have h_column (j : I) :
      ∫⁻ x in S, ‖∫ y, β j y • W (g x * y)‖ₑ ^ 2 ∂μ ≤ K * ∫⁻ y, ‖β j y‖ₑ ^ 2 :=
    h_bound (β j) (hβ_meas j) (hβ j) fun y hy ↦
      Set.mem_of_indicator_ne_zero (left_ne_zero_of_mul hy)
  have h_dens_meas : Measurable fun y : 𝔰.G₁ ↦ A.indicator 1 y * ‖W y‖ₑ ^ 2 :=
    (measurable_one.indicator hA_meas).mul
      ((continuous_eNorm.comp W.continuous).measurable.pow_const 2)
  have h_weight : ∑ j, ∫⁻ y, ‖β j y‖ₑ ^ 2 =
      ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂volume.withDensity fun y ↦ A.indicator 1 y * ‖W y‖ₑ ^ 2 := by
    rw [← lintegral_finsetSum' _ fun j _ ↦ (hβ j).aestronglyMeasurable.eNorm.pow_const 2,
      lintegral_withDensity_eq_lintegral_mul _ h_dens_meas (hφ.eNorm.pow_const 2)]
    refine lintegral_congr fun y ↦ ?_
    rw [Pi.mul_apply]
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Pi.one_apply, one_mul, mul_comm (‖W y‖ₑ ^ 2),
        euclidean_enorm_sq_eq_sum, mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      dsimp only [β]
      rw [Set.indicator_of_mem hy, eNorm_mul, mul_pow, Complex.star_def, RCLike.eNorm_conj]
    · rw [Set.indicator_of_notMem hy, zero_mul, zero_mul]
      refine sum_eq_zero fun j _ ↦ ?_
      dsimp only [β]
      rw [Set.indicator_of_notMem hy, zero_mul, eNorm_zero, zero_pow two_ne_zero]
  have h_col_meas (j : I) : Measurable fun x : T ↦ ‖∫ y : 𝔰.G₁, β j y • W (g x * y)‖ₑ ^ 2 :=
    (continuous_eNorm.measurable.comp <| New.measurable_integral <|
      ((hβ_meas j).comp measurable_snd).smul <|
        W.continuous.measurable.comp
          ((hg.comp measurable_fst).mul measurable_snd)).pow_const 2
  calc ∫⁻ x, ∑ i : I × I, ‖∫ y in A, φ y * (W (s * g x * y) i.1 * star (W (t x * y) i.2))‖ₑ ^ 2
        ∂μ[|S]
      = (μ S)⁻¹ * ∑ j : I, ∫⁻ x in S, ‖∫ y, β j y • W (g x * y)‖ₑ ^ 2 ∂μ := by
        rw [lintegral_congr h_columns, ProbabilityTheory.cond, lintegral_smul_measure,
          smul_eq_mul, lintegral_finsetSum _ fun j _ ↦ h_col_meas j]
    _ ≤ (μ S)⁻¹ * ∑ j : I, (K * ∫⁻ y, ‖β j y‖ₑ ^ 2) :=
        mul_le_mul' le_rfl (sum_le_sum fun j _ ↦ h_column j)
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(((μ S)⁻¹ * K) •
          volume.withDensity fun y : 𝔰.G₁ ↦ A.indicator 1 y * ‖W y‖ₑ ^ 2) := by
        rw [← mul_sum, h_weight, lintegral_smul_measure, smul_eq_mul, ← mul_assoc]

/-- The pairs `(h, v)` with `h` in the unitary group `U(κ)` of the positive definite middle part and
`v` in the frame-fixing unipotent subgroup `besselU0` of `G₁`. -/
abbrev New.Shape.FixerFactors (𝔰 : Shape) : Type :=
  U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) × (𝔰.middleGram (1 : ℂ)).besselU0

/-- Schur's bound at the section `γ_Z = gramSection Z`, in operator form, for the uncut function
`W = X.besselFn .full` of a Bessel system `X` with scale `B`. For `P ≥ B ^ 5` the field
`X.hasSchurBound` gives `HasSchurBound` with the two constants `P` and `D = |I| / X.deg`: `W` and
its right derivatives `V` of each order `l ≤ 2 n²` are Bessel functions, and `φ ↦ ∫ φ(y) V(g y) dy`
has squared norm at most `P ^ (2 l) D` as a map from `L²(G₁)` to functions of `g` in
`L²(besselU∖G₁)` (`SchurLe`). Here `n = ϱ + 1` and `I = X.Index`.

Let `8 r ≤ P` and `B ^ 5 ≤ P`, where `r` is the size of the matrices in `G₁`, and let `0 < c`. On
the ball of radius `(P ^ 6)⁻¹` about `Z`, let `c ≤ gramDiscReal Y` and `IsBoundedInCell Y P` hold.
Let `A` be a compact set of norm at most `P ^ 20` that contains a subset `Ω` of the frame-fixing
unipotent subgroup `besselU0`, and let `s` and all `t x` lie in the Bessel subgroup. Let `μ` be
`openCellConst · c ^ (|κ| - 1)` times Haar measure (`fixerMeasure`) on the pairs `x = (h, v)` in
`U(κ) × besselU0` (`FixerFactors`). Let `K = P ^ (2000 n²) D`.

For `x` drawn from `m`, which is `μ` conditioned on `v ∈ Ω`, put `k_(i,j)(x, y) = W_i (s γ_Z (v h)⁻¹
y) · conj (W_j (t x * y))`. Then `IsL2Contraction` says that, for bounded measurable `φ`, the mean
over `m` of `∑_(i,j) |∫_A φ(y) k_(i,j)(x, y) dy|²` is at most `∫ |φ|²` with respect to
`(μ (U(κ) × Ω))⁻¹ K` times the measure of density `‖W‖²` on `A`. -/
lemma New.BesselSystem.isL2Contraction_gramSection {𝔰 : Shape} {B P c : ℝ} {f : ℕ}
    (X : BesselSystem 𝔰 B f) {Z : 𝔰.FrameMatrix} (hP : 8 * 𝔰.r ≤ P) (hBP : B ^ 5 ≤ P) (hc : 0 < c)
    (h_ball : ∀ {Y : 𝔰.FrameMatrix},
      Y ∈ ball Z (P ^ 6)⁻¹ → c ≤ gramDiscReal Y ∧ IsBoundedInCell Y P)
    {A : Set 𝔰.G₁} (hA : IsCompact A)
    (hA_norm : ∀ y ∈ A, ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ P ^ 20)
    {Ω : Set (𝔰.middleGram (1 : ℂ)).besselU0} (hΩ : ∀ v ∈ Ω, (v : 𝔰.G₁) ∈ A) {s : 𝔰.G₁}
    (hs : s ∈ besselS) {t : 𝔰.FixerFactors → 𝔰.G₁} (ht : ∀ x : 𝔰.FixerFactors, t x ∈ besselS)
    {μ : Measure 𝔰.FixerFactors} (hμ : μ = 𝔰.fixerMeasure c)
    {K : ℝ≥0∞} (hK : K = .ofReal (P ^ (2000 * 𝔰.n ^ 2)) * (.ofReal X.deg⁻¹ * card X.Index)) :
    IsL2Contraction μ[|.univ ×ˢ Ω] (volume.restrict A)
      (((μ (.univ ×ˢ Ω))⁻¹ * K) •
        volume.withDensity fun y : 𝔰.G₁ ↦ A.indicator 1 y * ‖X.besselFn .full y‖ₑ ^ 2)
      fun (i : X.Index × X.Index) (x : 𝔰.FixerFactors) (y : 𝔰.G₁) ↦
        X.besselFn .full (s * (gramSection Z * (x.2 * embedH x.1)⁻¹) * y) i.1 *
          conj (X.besselFn .full (t x * y) i.2) := by
  let g₀ (x : 𝔰.FixerFactors) : 𝔰.G₁ := gramSection Z * (x.2 * embedH x.1)⁻¹
  have hg₀_meas : Measurable g₀ :=
    (continuous_const.fun_mul
      ((continuous_subtypeVal.comp continuous_snd).fun_mul
        (continuous_embedH.comp continuous_fst)).inv).measurable
  have hΩ_ball : .univ ×ˢ Ω ⊆ 𝔰.fixerBall (P ^ 20) :=
    fun x hx ↦ Shape.mem_fixerBall.2 (hA_norm x.2 (hΩ x.2 hx.2))
  have h_schur (β : 𝔰.G₁ → ℂ) (hβ_meas : Measurable β) (hβ_int : Integrable β)
      (hβ_supp : Function.support β ⊆ A) :
      ∫⁻ x in .univ ×ˢ Ω, ‖∫ y, β y • X.besselFn .full (g₀ x * y)‖ₑ ^ 2 ∂μ ≤
        K * ∫⁻ y, ‖β y‖ₑ ^ 2 := by
    refine (lintegral_mono_set hΩ_ball).trans ?_
    rw [hμ, hK]
    exact lintegral_gramSection_integral_le hP (X.hasSchurBound P hBP) hc
      (fun Y hY ↦ (h_ball hY).1) (fun Y hY ↦ (h_ball hY).2) hβ_meas hβ_int
      fun y hy ↦ hA_norm y (hβ_supp hy)
  exact isL2Contraction_of_columns (X.isCutPair.isBesselFunction .full) hA hs ht hg₀_meas h_schur

/-- For `1 ≤ M`, `M₀ = M ^ (9 n)` and `P = (M₀ ^ 5) ^ n`, the product `P ^ (2000 n²) · M₀ ^
5 · (M · P ^ 20 · P ^ 20) ^ (2 n²)` equals `M ^ (93600 n⁴ + 2 n² + 45 n)`, hence is at most
`M ^ (10⁵ n⁴)`. -/
lemma New.scale_mul_le_pow {M M₀ P : ℝ} {n : ℕ} (hM : 1 ≤ M) (hM₀ : M₀ = M ^ (9 * n))
    (hP : P = (M₀ ^ 5) ^ n) :
    P ^ (2000 * n ^ 2) * (M₀ ^ 5 * (M * (P ^ 20 * P ^ 20)) ^ (2 * n ^ 2)) ≤
      M ^ (10 ^ 5 * n ^ 4) := by
  have h_le_pow_four : n ≤ n ^ 4 := Nat.le_self_pow four_ne_zero n
  have h_sq_le_pow_four : n ^ 2 ≤ n ^ 4 := by linarith [Nat.le_self_pow two_ne_zero (n ^ 2)]
  subst hM₀ hP
  calc _ = M ^ (93600 * n ^ 4 + 2 * n ^ 2 + 45 * n) := by ring
    _ ≤ M ^ (10 ^ 5 * n ^ 4) := pow_le_pow_right₀ hM (by omega)

/-- Let `a, b, p ≥ 0` and `c, δ > 0` be real, `d` natural. If `m ≤ a ω b d` in `ℝ≥0∞` with `ω`
finite and nonzero, then `ω` cancels: `(c ω)⁻¹ · (p d / δ) · m ≤ p a b d² / (δ c)` as reals. -/
lemma New.toReal_inv_mul_mul_le {m ω : ℝ≥0∞} {a b c p δ : ℝ} {d : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hp : 0 ≤ p) (hδ : 0 < δ) (hω_zero : ω ≠ 0) (hω_top : ω ≠ ∞)
    (hm : m ≤ .ofReal a * ω * .ofReal b * d) :
    ((.ofReal c * ω)⁻¹ * (.ofReal p * (.ofReal δ⁻¹ * d)) * m).toReal ≤
      p * (a * b) * (d ^ 2 / (δ * c)) := by
  have hcω_ne_zero : ENNReal.ofReal c * ω ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 hc).ne' hω_zero
  have h_ne_top : (.ofReal c * ω)⁻¹ * (.ofReal p * (.ofReal δ⁻¹ * d)) *
      (.ofReal a * ω * .ofReal b * d) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hcω_ne_zero)
        (ENNReal.mul_ne_top ofReal_ne_top (ENNReal.mul_ne_top ofReal_ne_top (natCast_ne_top d))))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ofReal_ne_top hω_top)
        ofReal_ne_top) (natCast_ne_top d))
  have h_le : ((.ofReal c * ω)⁻¹ * (.ofReal p * (.ofReal δ⁻¹ * d)) * m).toReal ≤
      ((.ofReal c * ω)⁻¹ * (.ofReal p * (.ofReal δ⁻¹ * d)) *
        (.ofReal a * ω * .ofReal b * d)).toReal :=
    ENNReal.toReal_mono h_ne_top (mul_le_mul' le_rfl hm)
  have hω_pos : 0 < ω.toReal := toReal_pos hω_zero hω_top
  refine h_le.trans_eq ?_
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_ofReal ha, toReal_ofReal hb,
    toReal_ofReal hc.le, toReal_ofReal hp, toReal_ofReal (inv_nonneg.2 hδ.le), toReal_natCast]
  field_simp [hc.ne', hδ.ne', hω_pos.ne']

/-- Let `8 n ≤ M` and `M ^ (9 n) ≤ R`, where `n = 𝔰.n = ϱ + 1`. Let `M⁻¹ ≤ gramDiscReal Z`, the
number |det Z|² − |D_ϱ|² with D_ϱ the leading principal minor of order ϱ, so that `Z` lies in the
open cell. Let `‖Z⁻¹‖ ≤ R`, and let `γ_Z = gramSection Z`, an element of the unitary group `G₁` with
frame Gram matrix `Z`. Let `s` lie in the Bessel subgroup `besselS`, `v` in the frame-fixing
unipotent group `besselU0` and `h` in `U(κ)`, embedded in `G₁` by `embedH`. Suppose that the moved
frame vectors `z⁻¹ f_a` have norm at most `M` (`frameBox`). If also
`besselLength (s γ_Z (v h)⁻¹ z) ≤ M`, then the operator norm of `v⁻¹ z` is at most `R ^ 5`. -/
lemma New.norm_inv_mul_le_of_besselLength_le {𝔰 : Shape} {M R : ℝ} {Z : 𝔰.FrameMatrix}
    {s v z : 𝔰.G₁} {h : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)} (h_size_le : 8 * (𝔰.ϱ + 1) ≤ M)
    (h_pow_le : M ^ (9 * 𝔰.n) ≤ R) (h_disc : M⁻¹ ≤ gramDiscReal Z) (hZ_inv : ‖Z⁻¹‖ ≤ R)
    (hs : s ∈ besselS) (hv : v ∈ besselU0) (hz : z ∈ frameBox M)
    (h_length : besselLength (s * (gramSection Z * (v * embedH h)⁻¹) * z) ≤ M) :
    ‖((v⁻¹ * z : 𝔰.G₁) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ R ^ 5 := by
  -- `(v h)⁻¹ z` has the frame of `z`, and differs from `v⁻¹ z` by the unitary `embedH h`
  have h_box : (v * embedH h)⁻¹ * z ∈ frameBox M := fun a ↦ by
    simpa only [frameVector_mul_of_mem_besselFixer (inv_mem (mul_embedH_mem_besselFixer hv h))]
      using hz a
  rw [mul_assoc, besselLength_besselS_mul hs, mul_assoc] at h_length
  rw [show v⁻¹ * z = embedH h * ((v * embedH h)⁻¹ * z) by
    rw [_root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul], norm_embedH_mul]
  exact norm_le_of_besselLength_gramSection_mul_le h_size_le h_pow_le h_disc hZ_inv h_box h_length

/-- Let `realFrameGram γ`, the matrix of the products `h(f_j, γ f_l)` of the frame
`(f_i) = (e₁, …, e_ϱ, z)` with its translate by `γ`, lie in the open cell `𝔰.openCell`. This means
it is invertible and its inverse has last diagonal entry of absolute value less than 1. Let
`γ_Z = gramSection (realFrameGram γ)` be its section. Then there are `s` in the Bessel subgroup
`besselS` and a measurable map `t`. The map `t` goes from `FixerFactors` (pairs `(h, v)` in
`U(κ) × besselU0`) into the fixer `besselFixer`, the elements fixing each frame vector. They satisfy
`γ t(h, v) = s γ_Z (v h)⁻¹` for all `h` and `v`. -/
lemma New.exists_mul_eq_mul_gramSection_mul {𝔰 : Shape} {γ : 𝔰.G₁}
    (hγ : realFrameGram γ ∈ 𝔰.openCell) :
    ∃ s ∈ besselS, ∃ t : 𝔰.FixerFactors → 𝔰.G₁,
      Measurable t ∧
      (∀ x : 𝔰.FixerFactors, t x ∈ besselFixer) ∧
      ∀ x : 𝔰.FixerFactors,
        γ * t x = s * (gramSection (realFrameGram γ) * (x.2 * embedH x.1)⁻¹) := by
  -- Write `γ = u k γ_Z (u' k')⁻¹`, and take `s = u k` and `t(h, v) = u' k' h⁻¹ v⁻¹`.
  obtain ⟨u, k, u', k', hγ_eq⟩ := exists_eq_mul_gramSection_mul (Z := realFrameGram γ) hγ rfl
  have ht_meas : Measurable fun x : 𝔰.FixerFactors ↦
      unipotentOf u' * embedH (k' * x.1⁻¹) * (x.2⁻¹ : besselU0) :=
    ((continuous_const.fun_mul
      (continuous_embedH.comp (continuous_const.fun_mul continuous_fst.inv))).fun_mul
      (continuous_subtypeVal.comp continuous_snd).inv).measurable
  refine ⟨unipotentOf u * embedH k,
    mem_besselS_of_mem_besselFixer (mul_embedH_mem_besselFixer (unipotentOf_mem_besselU0 u) k),
    fun x ↦ unipotentOf u' * embedH (k' * x.1⁻¹) * (x.2⁻¹ : besselU0), ht_meas,
    fun (h, v) ↦ mul_mem (mul_embedH_mem_besselFixer (unipotentOf_mem_besselU0 u') _)
      (mem_besselFixer_of_mem_besselU0 v⁻¹.prop), ?_⟩
  generalize realFrameGram γ = Z at hγ_eq ⊢
  intro ⟨h, v⟩
  have hkh : embedH (k' * h⁻¹) = embedH k' * (embedH h)⁻¹ :=
    ((toBesselH 𝔰 (1 : ℂ)).map_mul k' h⁻¹).trans
      (congrArg (embedH k' * ·) ((toBesselH 𝔰 (1 : ℂ)).map_inv h))
  dsimp only
  rw [hγ_eq, hkh, Subgroup.coe_inv, _root_.mul_inv_rev, _root_.mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- The conclusion of the open cell bound at `γ` in `G₁` and scale `ρ`, for the uncut function
`W = X.besselFn .full` of a Bessel system `X`. The shifts `t x`, with `x` drawn from `m`, fix the
frame, and the kernels `W (γ t z) ⊗ conj (W (t z))` on the set `A` are bounded on average by the
measure `ν`. Its mass is at most `pairingBoundSq`, the number
`(ρ ^ (9 n) / 𝗀) ^ (10⁵ n⁴) |I|² / (X.deg · openCellConst · (𝗀 / 2) ^ (k - 1))` with
`𝗀 = gramDiscReal (realFrameGram γ)`, `n = ϱ + 1`, `k = |κ|` and `I = X.Index`. -/
structure New.BesselSystem.IsOpenCellBound {𝔰 : Shape} {B : ℝ} {f : ℕ} (X : BesselSystem 𝔰 B f)
    (γ : 𝔰.G₁) (ρ : ℝ) {T : Type*} [MeasurableSpace T] (A : Set 𝔰.G₁) (ν : Measure 𝔰.G₁)
    (m : Measure T) (t : T → 𝔰.G₁) : Prop where
  /-- The domain `A` is compact. -/
  isCompact : IsCompact A
  /-- The shift is a measurable map. -/
  measurable : Measurable t
  /-- Every shift lies in the fixer of the frame. -/
  mem_besselFixer (x : T) : t x ∈ besselFixer
  /-- The shifts are averaged by a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure m
  /-- The mean over `m` of the squared Hilbert–Schmidt norm of
  `∫_A φ z • W (γ t z) ⊗ conj (W (t z))` is at most `∫ ‖φ‖ ^ 2 dν`, for bounded measurable `φ`. -/
  isL2Contraction : IsL2Contraction m (volume.restrict A) ν
    fun (i : X.Index × X.Index) (x : T) (z : 𝔰.G₁) ↦
      X.besselFn .full (γ * t x * z) i.1 * conj (X.besselFn .full (t x * z) i.2)
  /-- The bounding measure is finite. -/
  isFiniteMeasure : IsFiniteMeasure ν
  /-- The total mass of the bounding measure is at most `pairingBoundSq`. -/
  measureReal_univ_le : ν.real .univ ≤ pairingBoundSq γ X.deg ρ (card X.Index)
  /-- For almost every shift, `A` contains every `z` in `frameBox ρ` such that `γ t z` has
  `besselLength` at most `ρ`. -/
  ae_mem_of_besselLength_le :
    ∀ᵐ x : T ∂m, ∀ z ∈ frameBox ρ, besselLength (γ * t x * z) ≤ ρ → z ∈ A

/-- A mean `L²` bound for the kernels `W (g x * z) ⊗ conj (W (t x * z))`, where
`W = X.besselFn .full` is the uncut function of a Bessel system `X`, `x` is drawn from `m` and `z`
ranges over `A`. The bounding measure `ν` has mass at most `C`, and `A` captures the points of
Bessel length at most `M`. -/
structure New.BesselSystem.IsKernelBound {𝔰 : Shape} {B : ℝ} {f : ℕ} (X : BesselSystem 𝔰 B f)
    {T : Type*} [MeasurableSpace T] (g t : T → 𝔰.G₁) (M C : ℝ) (A : Set 𝔰.G₁) (ν : Measure 𝔰.G₁)
    (m : Measure T) : Prop where
  /-- The domain `A` is compact. -/
  isCompact : IsCompact A
  /-- The mean over `m` of the squared Hilbert–Schmidt norm of
  `∫_A φ z • W (g x * z) ⊗ conj (W (t x * z))` is at most `∫ ‖φ‖ ^ 2 dν`, for bounded measurable
  `φ`. -/
  isL2Contraction : IsL2Contraction m (volume.restrict A) ν
    fun (i : X.Index × X.Index) (x : T) (z : 𝔰.G₁) ↦
      X.besselFn .full (g x * z) i.1 * conj (X.besselFn .full (t x * z) i.2)
  /-- The parameters are averaged by a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure m
  /-- The bounding measure is finite. -/
  isFiniteMeasure : IsFiniteMeasure ν
  /-- The total mass of the bounding measure is at most `C`. -/
  measureReal_univ_le : ν.real .univ ≤ C
  /-- For almost every `x`, `A` contains every `z` in `frameBox M` such that `g x * z` has
  `besselLength` at most `M`. -/
  ae_mem_of_besselLength_le :
    ∀ᵐ x : T ∂m, ∀ z ∈ frameBox M, besselLength (g x * z) ≤ M → z ∈ A

private lemma cast_frameRank_le_rank {𝔰 : New.Shape} : (𝔰.n : ℝ) ≤ 𝔰.r :=
  Nat.cast_le.2 (by simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective 𝔰.besselFrame New.besselFrame_injective)

/-- The open cell bound at the section `γ_Z = gramSection Z`, for the uncut function
`W = X.besselFn .full` of a Bessel system `X` with scale `B`. Here `n = ϱ + 1` and `I = X.Index`.

Let `B ≤ M` and `M⁻¹ ≤ gramDiscReal Z = |det Z|² − |D_ϱ|²`, D_ϱ the leading principal minor of order
ϱ, let the entries of `Z` have norm at most `M ^ 2`, and let `s` and all `t x` lie in the Bessel
subgroup `besselS`. For `x = (h, v)` in `U(κ) × besselU0` (`FixerFactors`) put
`g x = s γ_Z (v h)⁻¹`. There are (`IsKernelBound`) a compact set `A`, a probability measure `m` and
a finite measure `ν` such that the kernel `W (g x * z) ⊗ conj (W (t x * z))`, integrated against
volume on `A`, has norm at most one from `L²(ν)` to `L²(m)` (`IsL2Contraction`). The mass of `ν` is
at most `M ^ (10⁵ n⁴) |I|² / (X.deg · openCellConst · (gramDiscReal Z / 2) ^ (k - 1))`, where
`k = |κ|` and `openCellConst` is vol U(k) · (2π^k/(k−1)!) / vol U(r), `r` the rank of `G₁`. Almost
surely `A` contains every `z` with all `‖z⁻¹ f_a‖ ≤ M` and `besselLength (g x * z) ≤ M`. -/
lemma New.BesselSystem.exists_isKernelBound_gramSection {𝔰 : Shape} {B M : ℝ} {f : ℕ}
    (X : BesselSystem 𝔰 B f) {Z : 𝔰.FrameMatrix} (hBM : B ≤ M) (h_disc : M⁻¹ ≤ gramDiscReal Z)
    (hZ : ∀ a c : Fin (𝔰.ϱ + 1), ‖Z a c‖ ≤ M ^ 2) {s : 𝔰.G₁} (hs : s ∈ besselS)
    {g t : 𝔰.FixerFactors → 𝔰.G₁} (ht : ∀ x : 𝔰.FixerFactors, t x ∈ besselS)
    (hg_eq : ∀ x : 𝔰.FixerFactors, g x = s * (gramSection Z * (x.2 * embedH x.1)⁻¹)) :
    ∃ (A : Set 𝔰.G₁) (ν : Measure 𝔰.G₁) (m : Measure 𝔰.FixerFactors),
      X.IsKernelBound g t M
        (M ^ (10 ^ 5 * 𝔰.n ^ 4) *
          (card X.Index ^ 2 / (X.deg * 𝔰.openCellConst * (gramDiscReal Z / 2) ^ (𝔰.k - 1))))
        A ν m := by
  -- Take for `A` a tube over a set `Ω ⊆ besselU0`, for `m` Haar measure conditioned on `v ∈ Ω`, and
  -- for `ν` a multiple of `‖W‖²` on `A`; Schur's bound gives the contraction.
  have hB : 8 * 𝔰.r ≤ B := X.eight_mul_rank_le
  have hM_eight : 8 * (𝔰.ϱ + 1) ≤ M := by
    rw [← Nat.cast_succ]
    linarith [cast_frameRank_le_rank (𝔰 := 𝔰)]
  have hM_two : 2 ≤ M := by linarith
  have h_disc_half : 0 < gramDiscReal Z / 2 :=
    half_pos (h_disc.trans_lt' (inv_pos.2 (by linarith)))
  -- the scales `M ≤ M₀ ≤ M₀ ^ 5 ≤ P`
  have hM_one : 1 ≤ M := one_le_two.trans hM_two
  set M₀ : ℝ := M ^ (9 * 𝔰.n) with hM₀_def
  set P : ℝ := (M₀ ^ 5) ^ 𝔰.n with hP_def
  have hM₀ : M ≤ M₀ := le_self_pow₀ hM_one (by dsimp only [Shape.n]; omega)
  have h_le_pow : M₀ ≤ M₀ ^ 5 := le_self_pow₀ (hM_one.trans hM₀) (by norm_num)
  have h_pow_le : M₀ ^ 5 ≤ P := le_self_pow₀ (by linarith) (by dsimp only [Shape.n]; omega)
  have hP_one : 1 ≤ P := hM_one.trans (hM₀.trans (h_le_pow.trans h_pow_le))
  obtain ⟨A, Ω, h_tube⟩ := exists_tube (𝔰 := 𝔰) (T := M₀ ^ 5) (by linarith)
  have hA_norm : ∀ y ∈ A, ‖(y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ P ^ 20 := fun y hy ↦
    (h_tube.norm_le y hy).trans
      ((pow_le_pow_left₀ (by linarith) h_pow_le 10).trans
        (pow_le_pow_right₀ hP_one (by norm_num)))
  have h_mass : ∫⁻ y, A.indicator 1 y * ‖X.besselFn .full y‖ₑ ^ 2 ≤
      .ofReal (M₀ ^ 5) * 𝔰.besselHaar₀ Ω * .ofReal ((M * (P ^ 20 * P ^ 20)) ^ (2 * 𝔰.n ^ 2)) *
        card X.Index := by
    have h1 := X.lintegral_indicator_mul_enorm_sq_le h_tube.isCompact.measurableSet
      (one_le_pow₀ hP_one) hA_norm h_tube.lintegral_indicator_le
    refine h1.trans (mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl)
    · exact mul_le_mul' (ofNat_le_ofReal.2 (by linarith)) le_rfl
    · refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
        (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (zero_le_one.trans hP_one) 20)
          (pow_nonneg (zero_le_one.trans hP_one) 20)))
        (mul_le_mul_of_nonneg_right hM_two (mul_nonneg (pow_nonneg (zero_le_one.trans hP_one) 20)
          (pow_nonneg (zero_le_one.trans hP_one) 20))) _)
  -- `μ` is the measure and `K` the constant of Schur's bound
  set c : ℝ := 𝔰.openCellConst * (gramDiscReal Z / 2) ^ (𝔰.k - 1) with hc_def
  have hc : 0 < c := mul_pos 𝔰.openCellConst_pos (pow_pos h_disc_half _)
  let μ : Measure 𝔰.FixerFactors := ENNReal.ofReal c • volume.prod 𝔰.besselHaar₀
  let K : ℝ≥0∞ := .ofReal (P ^ (2000 * 𝔰.n ^ 2)) * (.ofReal X.deg⁻¹ * card X.Index)
  have hμΩ : μ (.univ ×ˢ Ω) = .ofReal c * 𝔰.besselHaar₀ Ω := by
    rw [smul_apply, smul_eq_mul, Measure.prod_prod, measure_univ, one_mul]
  have hμ_ne_zero : μ (.univ ×ˢ Ω) ≠ 0 := by
    rw [hμΩ]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 hc).ne' h_tube.measure_ne_zero
  have hμ_ne_top : μ (.univ ×ˢ Ω) ≠ ∞ := by
    rw [hμΩ]
    exact ENNReal.mul_ne_top ofReal_ne_top h_tube.measure_ne_top
  let ν₀ : Measure 𝔰.G₁ := volume.withDensity fun y ↦ A.indicator 1 y * ‖X.besselFn .full y‖ₑ ^ 2
  refine ⟨A, ((μ (.univ ×ˢ Ω))⁻¹ * K) • ν₀, μ[|.univ ×ˢ Ω], h_tube.isCompact, ?_,
    cond_isProbabilityMeasure_of_finite hμ_ne_zero hμ_ne_top, ?_, ?_, ?_⟩
  · -- the contraction: the sizes stay bounded by `P` near `Z`, so Schur's bound applies
    have hΩA (v : besselU0) (hv : v ∈ Ω) : (v : 𝔰.G₁) ∈ A := by
      have h := h_tube.mul_mem v hv 1 (norm_one.trans_le (by linarith))
      rwa [mul_one] at h
    have hBP : B ^ 5 ≤ P :=
      (pow_le_pow_left₀ (by linarith [Nat.cast_nonneg (α := ℝ) 𝔰.r]) (hBM.trans hM₀) 5).trans
        h_pow_le
    rw [funext hg_eq]
    exact X.isL2Contraction_gramSection (by linarith) hBP h_disc_half
      (gramDiscReal_div_two_le_and_isBoundedInCell h_disc hM_eight hZ (h_le_pow.trans h_pow_le))
      h_tube.isCompact hA_norm hΩA hs ht rfl rfl
  · have h_lt : (∫⁻ y, A.indicator 1 y * ‖X.besselFn .full y‖ₑ ^ 2) < ∞ :=
      h_mass.trans_lt (mul_lt_top (mul_lt_top (mul_lt_top ofReal_lt_top
        h_tube.measure_ne_top.lt_top) ofReal_lt_top) (natCast_lt_top _))
    have : IsFiniteMeasure ν₀ := isFiniteMeasure_withDensity h_lt.ne
    exact smul_finite ν₀ (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hμ_ne_zero)
      (ENNReal.mul_ne_top ofReal_ne_top (ENNReal.mul_ne_top ofReal_ne_top (natCast_ne_top _))))
  · -- in the mass of `ν` the volume of `Ω` cancels
    have hν : (((μ (.univ ×ˢ Ω))⁻¹ * K) • ν₀).real .univ = ((μ (.univ ×ˢ Ω))⁻¹ * K *
        ∫⁻ y, A.indicator 1 y * ‖X.besselFn .full y‖ₑ ^ 2).toReal := by
      rw [Measure.real_def, smul_apply, smul_eq_mul,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have h_deg : 0 < X.deg := X.deg_pos
    rw [hν, hμΩ, mul_assoc X.deg, ← hc_def]
    refine (toReal_inv_mul_mul_le (pow_nonneg (by linarith) 5)
      (pow_nonneg (mul_nonneg (zero_le_one.trans hM_one)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hP_one) 20)
          (pow_nonneg (zero_le_one.trans hP_one) 20))) _)
      hc (pow_nonneg (zero_le_one.trans hP_one) _) h_deg
      h_tube.measure_ne_zero h_tube.measure_ne_top h_mass).trans ?_
    exact mul_le_mul_of_nonneg_right (scale_mul_le_pow hM_one hM₀_def hP_def)
      (div_nonneg (sq_nonneg _) (mul_pos h_deg hc).le)
  · -- since `z = v * (v⁻¹ * z)` and `‖v⁻¹ * z‖ ≤ M₀ ^ 5`, the tube property applies
    have h_cell : IsBoundedInCell Z M₀ := isBoundedInCell_of_inv_le_gramDiscReal h_disc
      ((Nat.cast_succ 𝔰.ϱ).trans_le (by linarith)) hZ
      (pow_le_pow_right₀ hM_one (by dsimp only [Shape.n]; omega))
    filter_upwards [ae_cond_mem (.prod .univ h_tube.measurableSet)] with ⟨h, v⟩ ⟨_, hv⟩ z hz hgz
    rw [hg_eq] at hgz
    have hmem := h_tube.mul_mem v hv ((v : 𝔰.G₁)⁻¹ * z)
      (norm_inv_mul_le_of_besselLength_le hM_eight le_rfl h_disc h_cell.norm_inv_le hs v.prop hz
        hgz)
    rwa [mul_inv_cancel_left] at hmem

/-- The open cell bound, for the uncut function `W = X.besselFn .full` of a Bessel system `X` of
scale `B`. Let `Z = realFrameGram γ`, the matrix of products of the frame `f_a` with its translate
by `γ`, have `0 < gramDiscReal Z`. Let `B ≤ ρ`, and let some `y` have all `‖y⁻¹ f_a‖` and
`‖y⁻¹ γ f_a‖` at most `ρ` (`frameBox ρ`). There are (`IsOpenCellBound`) a compact set `A`, a
probability measure `m` on the pairs `FixerFactors`, a measurable map `t` from them into the fixer
`besselFixer` of the frame, and a finite measure `ν` of mass at most `pairingBoundSq`, such that the
mean over `m` of the squared Hilbert–Schmidt norm of `∫_A φ z • W (γ t z) ⊗ conj (W (t z))` is at
most `∫ ‖φ‖ ^ 2 dν` for all bounded measurable `φ`. Almost surely `A` contains every
`z ∈ frameBox ρ` with `besselLength (γ t z) ≤ ρ`. With `𝗀 = gramDiscReal Z`, `n = ϱ + 1`, `k = |κ|`
and `I = X.Index`, the number `pairingBoundSq` is `(ρ ^ (9 n) / 𝗀) ^ (10⁵ n⁴)
|I|² / (X.deg · openCellConst · (𝗀 / 2) ^ (k - 1))`. -/
lemma New.BesselSystem.exists_isOpenCellBound {𝔰 : Shape} {B : ℝ} {f : ℕ} {ρ : ℝ} {γ y : 𝔰.G₁}
    (X : BesselSystem 𝔰 B f) (hγ : 0 < gramDiscReal (realFrameGram γ))
    (hy : y ∈ frameBox ρ) (hγy : γ⁻¹ * y ∈ frameBox ρ) (hρ : B ≤ ρ) :
    ∃ (A : Set 𝔰.G₁) (ν : Measure 𝔰.G₁) (m : Measure 𝔰.FixerFactors) (t : 𝔰.FixerFactors → 𝔰.G₁),
      X.IsOpenCellBound γ ρ A ν m t := by
  -- Reduce to the section: with `Z` the Gram matrix of the two frames, the shifts `t` satisfy
  -- `γ t(h, v) = s γ_Z (v h)⁻¹`. Use the scale `M = ρ ^ (9 n) / gramDiscReal Z`.
  have hρ_n : 𝔰.n ≤ ρ := by
    linarith [X.eight_mul_rank_le, Nat.cast_nonneg (α := ℝ) 𝔰.n, cast_frameRank_le_rank (𝔰 := 𝔰)]
  have hρ_one : 1 ≤ ρ := (Nat.one_le_cast.2 𝔰.ϱ.succ_pos).trans hρ_n
  have hZρ (a c : Fin (𝔰.ϱ + 1)) : ‖realFrameGram γ a c‖ ≤ ρ ^ 2 :=
    (norm_realFrameGram_le_mul γ y a c).trans
      ((mul_le_mul (hy a) (hγy c) (norm_nonneg _) (zero_le_one.trans hρ_one)).trans_eq (sq ρ).symm)
  set Z : 𝔰.FrameMatrix := realFrameGram γ
  let M : ℝ := ρ ^ (9 * 𝔰.n) / gramDiscReal Z
  have hρM : ρ ≤ M := le_pow_div_gramDiscReal hγ hρ_n hρ_one hZρ
  have hZM (a c : Fin (𝔰.ϱ + 1)) : ‖Z a c‖ ≤ M ^ 2 :=
    (hZρ a c).trans (pow_le_pow_left₀ (zero_le_one.trans hρ_one) hρM 2)
  obtain ⟨s, hs, t, h_meas, h_fixer, h_shift⟩ : ∃ s ∈ besselS, ∃ t : 𝔰.FixerFactors → 𝔰.G₁,
      Measurable t ∧ (∀ x, t x ∈ besselFixer) ∧
        ∀ x, γ * t x = s * (gramSection Z * (x.2 * embedH x.1)⁻¹) :=
    exists_mul_eq_mul_gramSection_mul (mem_openCell_iff.2 hγ)
  obtain ⟨A, ν, m, h_bound⟩ : ∃ (A : Set 𝔰.G₁) (ν : Measure 𝔰.G₁) (m : Measure 𝔰.FixerFactors),
      X.IsKernelBound (fun x ↦ γ * t x) t M (pairingBoundSq γ X.deg ρ (card X.Index)) A ν m :=
    X.exists_isKernelBound_gramSection (hρ.trans hρM) (inv_pow_div_gramDiscReal_le hγ hρ_one _)
      hZM hs (fun x ↦ mem_besselS_of_mem_besselFixer (h_fixer x)) h_shift
  exact ⟨A, ν, m, t, { h_bound with
    measurable := h_meas
    mem_besselFixer := h_fixer
    ae_mem_of_besselLength_le := h_bound.ae_mem_of_besselLength_le.mono fun x hx z hz_box hz_size ↦
      hx z (fun a ↦ (hz_box a).trans hρM) (hz_size.trans hρM) }⟩

end OpenCellBound
end
end

/-!
# One pairing on the open cell, at all places together

Let `X` be a finite family of Bessel systems (`New.BesselSystem`), `W` the tensor product of their
Bessel functions and `W♭` that of their cuts. Let `φ` be a function of `z` of modulus at most `1`,
left invariant under the fixers of the frames and not necessarily a product over the places, such
that `φ (z) W♭ (γ z) ⊗ W♭ (z)^*` vanishes outside boxes. The integral of this product is bounded by
the root of the product of the local bounds `New.pairingBoundSq`, plus the integral of `‖φ‖` times
the norm of the difference between the uncut and cut kernels.

The operator bounds of `New.BesselSystem.exists_isOpenCellBound` multiply over the places, and one
shift that is no worse than the mean gives the bound for `W`.

Notions from other files:
* `BesselSystem`: two continuous functions on the group `G₁`, `besselFn .full` and its cut
  `besselFn .cut`, with values in `ℂ^I`, parameters `b` and `f`, and a degree `deg`.
* `frameBox ρ`: the `y` with `‖y⁻¹ f_a‖ ≤ ρ` for every vector `f_a` of the frame; `besselFixer` is
  the subgroup that fixes these vectors.
* `besselLength y`: the infimum of `‖s y‖ + 1` over `s` in the Bessel subgroup.
* `realFrameGram γ`: the matrix of products `h(f_a, γ f_b)` for the hermitian form `h`;
  `gramDiscReal Z` is `|det Z| ^ 2 - |D| ^ 2`, with `D` the leading minor one size smaller.
* `pairingBoundSq γ deg ρ d`: the square of the bound of the open cell at one place, a power of
  `ρ ^ (9 n) / 𝗀` times `d ^ 2 / (deg * openCellConst * (𝗀 / 2) ^ (k - 1))`, where
  `𝗀 = gramDiscReal (realFrameGram γ)`, `n = 𝔰.n` and `k = 𝔰.k`.

## Main definitions and results

* `New.BesselSystem.pairKernel`: the matrix of `W (y) ⊗ W (γ⁻¹ y)^*`. Its adjoint is the matrix of
  `W (γ⁻¹ y) ⊗ W (y)^*`, which is `New.BesselSystem.piKernel` at `γ⁻¹`.
* `New.BesselSystem.enorm_integral_pairKernel_cut_le`: compact support and the bound for the pairing
  of the cut functions.

## Relation to the literature

See `New.Spanning.Bessel.FillingData` for related work.
-/

@[expose] public section

open Finset Fintype New.RealPlace MeasureTheory ENNReal Measure ComplexConjugate

namespace New.BesselSystem

variable {ι : Type} [Fintype ι] {𝔰 : Shape} {b : ℝ} {f : ℕ}

/-- The matrix of the operator `W (γ z) ⊗ W (z)^*`, as a vector with the Hilbert–Schmidt norm. Here
`W` is the tensor product, over a finite family `X` of Bessel systems, of the Bessel functions
(`σ = .full`) or of their cuts (`σ = .cut`). The adjoint of `piKernel X σ γ⁻¹ y` is
`pairKernel X σ γ y`. -/
noncomputable def piKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ z : ι → 𝔰.G₁) :
    EuclideanSpace ℂ (((v : ι) → (X v).Index) × ((v : ι) → (X v).Index)) :=
  WithLp.toLp 2 fun i ↦ ∏ v : ι, (X v).besselFn σ (γ v * z v) (i.1 v) * conj
    ((X v).besselFn σ (z v) (i.2 v))

lemma continuous_piKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ : ι → 𝔰.G₁) :
    Continuous (piKernel X σ γ) := by
  fun_prop [piKernel]

/-- The parameter `b` of a Bessel system is at least `1`, being at least eight times the rank. -/
lemma one_le_b (X : BesselSystem 𝔰 b f) : 1 ≤ b := by
  have h_rank : (𝔰.r : ℝ) = 𝔰.ϱ + (card 𝔰.κ + 1 + 𝔰.ϱ) := by simp
  linarith [X.eight_mul_rank_le]

/-- Where `piKernel X .cut γ z`, the matrix of the cut kernel `W♭ (γ z) ⊗ W♭ (z)^*`, is not zero,
every component of `γ z` satisfies `InCut`: its `besselLength` is at most `b ^ (6 n + 2)`, where
`n = 𝔰.n` is the number of vectors in the frame. -/
lemma inCut_of_piKernel_ne_zero (X : ι → BesselSystem 𝔰 b f) {γ z : ι → 𝔰.G₁}
    (h_ne : piKernel X .cut γ z ≠ 0) (v : ι) : InCut (γ v * z v) b := by
  have h_W : (X v).besselFn .cut (γ v * z v) ≠ 0 := fun h_zero ↦
    h_ne (PiLp.ext fun i ↦ prod_eq_zero (mem_univ v) (by simp [h_zero]))
  exact (X v).isCutPair.inCut_of_ne_zero _ h_W

variable [DecidableEq ι]

/-- For either side `σ` (uncut or cut), the product of `piKernel X σ γ` and a measurable function of
modulus at most `1`, both translated by `t`, is integrable on every compact set. -/
lemma integrableOn_smul_piKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ t : ι → 𝔰.G₁)
    {φ : (ι → 𝔰.G₁) → ℂ} (hφ_meas : Measurable φ) (hφ_le : ∀ z : ι → 𝔰.G₁, ‖φ z‖ ≤ 1)
    {A : Set (ι → 𝔰.G₁)} (hA : IsCompact A) :
    IntegrableOn (fun z : ι → 𝔰.G₁ ↦ φ (t * z) • piKernel X σ γ (t * z)) A := by
  have h_cont : Continuous fun z : ι → 𝔰.G₁ ↦ piKernel X σ γ (t * z) :=
    (continuous_piKernel X σ γ).comp (continuous_const_mul t)
  exact (h_cont.continuousOn.integrableOn_compact hA).bdd_smul 1
    (hφ_meas.comp (measurable_const_mul t)).aestronglyMeasurable (.of_forall fun z ↦ hφ_le (t * z))

/-- Let `X v` be Bessel systems with size parameter `b`, one for each place `v`, and `W` the tensor
product of their Bessel functions. Let the frame Gram matrix of each `γ v` have `0 < gramDiscReal`,
and let some `y` have both `y v` and `(γ v)⁻¹ * y v` in `frameBox (ρ v)`, where `b ≤ ρ v`. Let `φ`
be measurable, of modulus at most `1`, and left invariant under the fixer `besselFixer` of the frame
at each place. There are a compact set `A` and a point `t` of the fixer such that the integral over
`A` of `φ` times the kernel `piKernel X .full γ`, the matrix of `W (γ z) ⊗ W (z)^*`, both translated
by `t`, has Hilbert–Schmidt norm at most the root of the product of the local bounds
`pairingBoundSq` at the places; and `A` contains every `z` in the boxes for which the components `x`
of `γ t z` have `besselLength` at most the corresponding `ρ v`. -/
lemma exists_isCompact_enorm_integral_piKernel_le (X : ι → BesselSystem 𝔰 b f)
    {γ y : ι → 𝔰.G₁} {ρ : ι → ℝ} (h_disc : ∀ v : ι, 0 < gramDiscReal (realFrameGram (γ v)))
    (hy_box : ∀ v : ι, y v ∈ frameBox (ρ v)) (hγy_box : ∀ v : ι, (γ v)⁻¹ * y v ∈ frameBox (ρ v))
    (h_radius : ∀ v : ι, b ≤ ρ v) {φ : (ι → 𝔰.G₁) → ℂ} (hφ_meas : Measurable φ)
    (hφ_le : ∀ z : ι → 𝔰.G₁, ‖φ z‖ ≤ 1)
    (hφ_inv : ∀ s z : ι → 𝔰.G₁, (∀ v : ι, s v ∈ besselFixer) → φ (s * z) = φ z) :
    ∃ (A : Set (ι → 𝔰.G₁)) (t : ι → 𝔰.G₁),
      IsCompact A ∧
      (∀ v : ι, t v ∈ besselFixer) ∧
      (∀ z : ι → 𝔰.G₁, (∀ v : ι, z v ∈ frameBox (ρ v)) →
        (∀ v : ι, besselLength (γ v * t v * z v) ≤ ρ v) → z ∈ A) ∧
      ‖∫ z in A, φ (t * z) • piKernel X .full γ (t * z)‖ₑ ≤
        .ofReal √(∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) := by
  -- At each place `exists_isOpenCellBound` gives a compact `A v`, a finite measure `ν v` and a
  -- probability measure `m v` on the parameters of the shifts `t v` (see `IsOpenCellBound`). The
  -- operator bounds multiply, and some shift does as well as the mean over shifts.
  choose A ν m t h_cell using fun v : ι ↦
    (X v).exists_isOpenCellBound (h_disc v) (hy_box v) (hγy_box v) (h_radius v)
  have ht (v : ι) : Measurable (t v) := (h_cell v).measurable
  have h_prob (v : ι) : IsProbabilityMeasure (m v) := (h_cell v).isProbabilityMeasure
  have h_finite (v : ι) : IsFiniteMeasure (ν v) := (h_cell v).isFiniteMeasure
  have h_mass (v : ι) : (ν v).real .univ ≤ pairingBoundSq (γ v) (X v).deg (ρ v)
    (card (X v).Index) :=
    (h_cell v).measureReal_univ_le
  -- `N x` is the squared Hilbert–Schmidt norm of the pairing with the shifts `t v (x v)`.
  let N (x : ι → 𝔰.FixerFactors) : ℝ≥0∞ :=
    ∑ i : (v : ι) → (X v).Index × (X v).Index, ‖∫ z : ι → 𝔰.G₁, φ z * ∏ v : ι,
      (X v).besselFn .full (γ v * t v (x v) * z v) (i v).1 * conj
        ((X v).besselFn .full (t v (x v) * z v) (i v).2)
        ∂Measure.pi fun v ↦ volume.restrict (A v)‖ₑ ^ 2
  have h_mean : ∫⁻ x, N x ∂Measure.pi m ≤ ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂Measure.pi ν :=
    IsL2Contraction.pi (by fun_prop)
      (fun v i x ↦ ContinuousOn.integrableOn_compact (h_cell v).isCompact (by fun_prop))
      (fun v ↦ (h_cell v).isL2Contraction) φ 1 hφ_meas hφ_le
  have h_ae : ∀ᵐ x : ι → 𝔰.FixerFactors ∂Measure.pi m, ∀ v : ι, ∀ z ∈ frameBox (ρ v),
      besselLength (γ v * t v (x v) * z) ≤ ρ v → z ∈ A v :=
    ae_pi_le_pi (Filter.eventually_pi fun v ↦ (h_cell v).ae_mem_of_besselLength_le)
  obtain ⟨x, hx_mem, hx_le⟩ :=
    exists_notMem_null_le_lintegral (by fun_prop : Measurable N).aemeasurable h_ae
  let s : ι → 𝔰.G₁ := fun v ↦ t v (x v)
  have hx_good : ∀ v : ι, ∀ z ∈ frameBox (ρ v), besselLength (γ v * s v * z) ≤ ρ v → z ∈ A v :=
    not_not.1 hx_mem
  have hs (v : ι) : s v ∈ besselFixer := (h_cell v).mem_besselFixer (x v)
  have h_compact : IsCompact (Set.univ.pi A) := isCompact_univ_pi fun v ↦ (h_cell v).isCompact
  refine ⟨Set.univ.pi A, s, h_compact, hs,
    fun z hz hγz v _ ↦ hx_good v (z v) (hz v) (hγz v), ?_⟩
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
  calc
    _ = N x := by
      rw [euclidean_enorm_sq_eq_sum, ← (Equiv.arrowProdEquivProdArrow ..).sum_comp]
      simp only [eval_integral_piLp
        (integrableOn_smul_piKernel X .full γ s hφ_meas hφ_le h_compact).eval_piLp]
      simp [← restrict_pi_pi, volume_pi, piKernel, mul_assoc, N, s, hφ_inv s _ hs]
    _ ≤ ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂Measure.pi ν := hx_le.trans h_mean
    _ ≤ ∫⁻ _, 1 ∂Measure.pi ν :=
      lintegral_mono fun z ↦ pow_le_one' (by simpa [← ofReal_norm] using hφ_le z) 2
    _ = .ofReal (∏ v : ι, (ν v).real .univ) := by simp [Measure.pi_univ, ofReal_prod_of_nonneg]
    _ ≤ .ofReal (∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) :=
      ofReal_le_ofReal (prod_le_prod₀ (fun v _ ↦ measureReal_nonneg) fun v _ ↦ h_mass v)
    _ = _ := by rw [← ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (prod_nonneg fun v _ ↦ measureReal_nonneg.trans (h_mass v))]

/-- Let `X v` be Bessel systems with size parameter `b`, one for each place `v`, and `W`, `W♭` the
tensor products of their Bessel functions and of their cuts. Let the frame Gram matrix of each `γ v`
have `0 < gramDiscReal`, and let some `y` have both `y v` and `(γ v)⁻¹ * y v` in `frameBox (ρ v)`,
where `b ^ (6 n + 2) ≤ ρ v` and `n = 𝔰.n` is the number of vectors in the frame. Let `φ` be
measurable, of modulus at most `1`, left invariant under the fixer `besselFixer` of the frame at
each place, and such that `φ` times the cut kernel `piKernel X .cut γ`, the matrix of
`W♭ (γ z) ⊗ W♭ (z)^*`, vanishes unless `z` lies in the boxes. Then this product has compact support,
and the Hilbert–Schmidt norm of its integral is at most the root of the product of the local bounds
`pairingBoundSq` at the places, plus the integral of `‖φ‖` times the norm of the difference of the
uncut kernel `W (γ z) ⊗ W (z)^*` and the cut kernel. -/
lemma hasCompactSupport_and_enorm_integral_piKernel_le (X : ι → BesselSystem 𝔰 b f)
    {γ y : ι → 𝔰.G₁} {ρ : ι → ℝ} (h_disc : ∀ v : ι, 0 < gramDiscReal (realFrameGram (γ v)))
    (hy_box : ∀ v : ι, y v ∈ frameBox (ρ v)) (hγy_box : ∀ v : ι, (γ v)⁻¹ * y v ∈ frameBox (ρ v))
    (h_radius : ∀ v : ι, b ^ (6 * 𝔰.n + 2) ≤ ρ v) {φ : (ι → 𝔰.G₁) → ℂ}
    (hφ_meas : Measurable φ) (hφ_le : ∀ z : ι → 𝔰.G₁, ‖φ z‖ ≤ 1)
    (hφ_inv : ∀ s z : ι → 𝔰.G₁, (∀ v : ι, s v ∈ besselFixer) → φ (s * z) = φ z)
    (hφ_box : ∀ z : ι → 𝔰.G₁, φ z • piKernel X .cut γ z ≠ 0 → ∀ v : ι, z v ∈ frameBox (ρ v)) :
    HasCompactSupport (fun z : ι → 𝔰.G₁ ↦ φ z • piKernel X .cut γ z) ∧
    ‖∫ z : ι → 𝔰.G₁, φ z • piKernel X .cut γ z‖ₑ ≤
      .ofReal √(∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) +
        ∫⁻ z : ι → 𝔰.G₁, ‖φ z‖ₑ * ‖piKernel X .full γ z - piKernel X .cut γ z‖ₑ := by
  -- After a translation by `t` the cut integrand lives on the compact set `A`. There compare it
  -- with the uncut one.
  have hb_radius (v : ι) : b ≤ ρ v :=
    (le_self_pow₀ (X v).one_le_b (Nat.succ_ne_zero _)).trans (h_radius v)
  obtain ⟨A, t, hA, ht, h_mem, h_full⟩ := exists_isCompact_enorm_integral_piKernel_le X h_disc
    hy_box hγy_box hb_radius hφ_meas hφ_le hφ_inv
  let F (σ : FullOrCut) (z : ι → 𝔰.G₁) :
      EuclideanSpace ℂ (((v : ι) → (X v).Index) × ((v : ι) → (X v).Index)) := φ z • piKernel X σ γ z
  have h_supp (z : ι → 𝔰.G₁) (hz : z ∉ A) : F .cut (t * z) = 0 := by
    by_contra h_ne
    refine hz (h_mem z (fun (v : ι) (a : Fin (𝔰.ϱ + 1)) ↦ ?_) fun v ↦ ?_)
    · simpa [frameVector_mul_of_mem_besselFixer (ht v)] using hφ_box (t * z) h_ne v a
    · have h_inCut : InCut (γ v * (t * z) v) b :=
        inCut_of_piKernel_ne_zero X (right_ne_zero_of_smul h_ne) v
      simpa [mul_assoc] using h_inCut.trans (h_radius v)
  have h_int (σ : FullOrCut) : IntegrableOn (fun z ↦ F σ (t * z)) A :=
    integrableOn_smul_piKernel X σ γ t hφ_meas hφ_le hA
  have h_diff : ‖∫ z in A, F .full (t * z) - F .cut (t * z)‖ₑ ≤
      ∫⁻ z, ‖φ z‖ₑ * ‖piKernel X .full γ z - piKernel X .cut γ z‖ₑ := by
    rw [← lintegral_mul_left_eq_self _ t]
    refine ((eNorm_integral_le_lintegral_eNorm _).trans (setLIntegral_le_lintegral A _)).trans_eq ?_
    simp only [F, ← smul_sub, eNorm_smul]
  refine ⟨.intro (hA.image (continuous_const_mul t)) fun z hz ↦ ?_, ?_⟩
  · simpa [F] using h_supp (t⁻¹ * z) fun h_memA ↦ hz ⟨t⁻¹ * z, h_memA, mul_inv_cancel_left t z⟩
  · have h_translate : ∫ z, F .cut z = ∫ z in A, F .cut (t * z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_supp,
        integral_mul_left_eq_self (F .cut) t]
    calc ‖∫ z, F .cut z‖ₑ
      _ = ‖(∫ z in A, F .full (t * z)) - ∫ z in A, F .full (t * z) - F .cut (t * z)‖ₑ := by
        rw [h_translate, integral_sub (h_int .full) (h_int .cut), _root_.sub_sub_cancel]
      _ ≤ _ := eNorm_sub_le.trans (add_le_add h_full h_diff)

/-- The matrix of the operator `W (y) ⊗ W (γ⁻¹ y)^*`, as a vector with the Hilbert–Schmidt norm.
Here `W` is the tensor product, over a finite family `X` of Bessel systems, of the Bessel functions
(`σ = .full`) or of their cuts (`σ = .cut`). It is the adjoint of `piKernel X σ γ⁻¹ y`, the matrix
of `W (γ⁻¹ y) ⊗ W (y)^*`. -/
noncomputable def pairKernel (X : ι → BesselSystem 𝔰 b f) (σ : FullOrCut) (γ y : ι → 𝔰.G₁) :
    EuclideanSpace ℂ (((v : ι) → (X v).Index) × ((v : ι) → (X v).Index)) :=
  WithLp.toLp 2 fun i ↦ ∏ v : ι, (X v).besselFn σ (y v) (i.1 v) * conj
    ((X v).besselFn σ ((γ v)⁻¹ * y v) (i.2 v))

/-- The passage to the adjoint (conjugate transpose) of a complex matrix indexed by `I × I`, a real
linear isometry for the Hilbert–Schmidt norm. -/
noncomputable def adjointIsometry (I : Type) [Fintype I] :
    EuclideanSpace ℂ (I × I) →ₗᵢ[ℝ] EuclideanSpace ℂ (I × I) where
  toFun x := WithLp.toLp 2 fun i ↦ conj (x i.swap)
  map_add' x x' := by ext; simp
  map_smul' r x := by ext; simp
  norm_map' x := by
    simpa [EuclideanSpace.norm_eq] using
      congrArg (√·) ((Equiv.prodComm I I).sum_comp fun i ↦ ‖x i‖ ^ 2)

/-- **One pairing.** Let `X v` be Bessel systems with size parameter `b`, one for each place `v`,
and `W`, `W♭` the tensor products of their Bessel functions and of their cuts. Let the frame Gram
matrix of each `γ v` have `0 < gramDiscReal`, and let some `y'` have both `y' v` and
`(γ v)⁻¹ * y' v` in `frameBox (ρ v)`, where `b ^ (6 n + 2) ≤ ρ v` and `n = 𝔰.n` is the number of
vectors in the frame. Let `φ` be measurable, of modulus at most `1`, left invariant under the fixer
`besselFixer` of the frame at each place, and such that `φ` times the cut kernel
`pairKernel X .cut γ`, the matrix of `W♭ (y) ⊗ W♭ (γ⁻¹ y)^*`, vanishes unless `y` lies in the boxes.
Then this product has compact support, and the Hilbert–Schmidt norm of its integral is at most the
root of the product of the local bounds `pairingBoundSq`, plus the integral of `‖φ‖` times the norm
of the difference of the uncut kernel `W (y) ⊗ W (γ⁻¹ y)^*` and the cut kernel. -/
theorem enorm_integral_pairKernel_cut_le (X : ι → BesselSystem 𝔰 b f)
    {γ y' : ι → 𝔰.G₁} {ρ : ι → ℝ} (h_disc : ∀ v : ι, 0 < gramDiscReal (realFrameGram (γ v)))
    (hy_box : ∀ v : ι, y' v ∈ frameBox (ρ v)) (hγy_box : ∀ v : ι, (γ v)⁻¹ * y' v ∈ frameBox (ρ v))
    (h_radius : ∀ v : ι, b ^ (6 * 𝔰.n + 2) ≤ ρ v) {φ : (ι → 𝔰.G₁) → ℂ}
    (hφ_meas : Measurable φ) (hφ_le : ∀ y : ι → 𝔰.G₁, ‖φ y‖ ≤ 1)
    (hφ_inv : ∀ s y : ι → 𝔰.G₁, (∀ v : ι, s v ∈ besselFixer) → φ (s * y) = φ y)
    (hφ_box : ∀ y : ι → 𝔰.G₁, φ y • pairKernel X .cut γ y ≠ 0 → ∀ v : ι, y v ∈ frameBox (ρ v)) :
    HasCompactSupport (fun y : ι → 𝔰.G₁ ↦ φ y • pairKernel X .cut γ y) ∧
    ‖∫ y : ι → 𝔰.G₁, φ y • pairKernel X .cut γ y‖ₑ ≤
      .ofReal √(∏ v : ι, pairingBoundSq (γ v) (X v).deg (ρ v) (card (X v).Index)) +
        ∫⁻ y : ι → 𝔰.G₁, ‖φ y‖ₑ * ‖pairKernel X .full γ y - pairKernel X .cut γ y‖ₑ := by
  -- The kernel is the adjoint of `W (γ⁻¹ y) ⊗ W (y)^*`, and `γ⁻¹` has the same `gramDiscReal`.
  let T := adjointIsometry ((v : ι) → (X v).Index)
  have h_kernel (σ : FullOrCut) (y : ι → 𝔰.G₁) : pairKernel X σ γ y = T (piKernel X σ γ⁻¹ y) := by
    ext; simp [T, adjointIsometry, pairKernel, piKernel, mul_comm]
  have h_adjoint (y : ι → 𝔰.G₁) :
      φ y • pairKernel X .cut γ y = T (conj (φ y) • piKernel X .cut γ⁻¹ y) := by
    ext; simp [h_kernel, T, adjointIsometry]
  have h_disc_inv (v : ι) :
      gramDiscReal (realFrameGram (γ⁻¹ v)) = gramDiscReal (realFrameGram (γ v)) := by
    rw [Pi.inv_apply, realFrameGram, Filling.frameGram_inv]
    simp [gramDiscReal, frameDisc, leadingMinor, ← Matrix.conjTranspose_submatrix]
  obtain ⟨h_support, h_bound⟩ := hasCompactSupport_and_enorm_integral_piKernel_le X (γ := γ⁻¹)
    (y := γ⁻¹ * y')
    (φ := fun y ↦ conj (φ y)) (fun v ↦ by simpa only [h_disc_inv] using h_disc v) hγy_box
    (fun v ↦ by simpa using hy_box v) h_radius (Complex.continuous_conj.measurable.comp hφ_meas)
    (by simpa using hφ_le) (fun s y hs ↦ by rw [hφ_inv s y hs])
    fun y hy ↦ hφ_box y (by rwa [h_adjoint, map_ne_zero_iff T T.injective])
  simp only [h_adjoint]
  refine ⟨h_support.comp_left (map_zero T), ?_⟩
  rw [T.integral_comp_comm, T.eNorm_map]
  simpa only [h_kernel, ← map_sub, T.eNorm_map, pairingBoundSq, h_disc_inv,
    RCLike.eNorm_conj] using h_bound

end New.BesselSystem
