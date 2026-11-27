module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
public import Lib.General.LinearAlgebra.MatricesNearIdentity
import Lib.DiscreteSeries.FlenstedJensen.CasimirEigenfunction
import Lib.DiscreteSeries.Holomorphic.HighestVectorExtension
import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors
import Mathlib.Topology.Separation.CompletelyRegular
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import New.Appendix.DiscreteSeries.SteepParameters
import Lib.General.LinearAlgebra.PolarDecomposition
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Group.Matrix
public import Lib.Adelic.Unitary.ComponentsAndBlockSums
import Lib.DiscreteSeries.Haar.TotalMass

section
section
/-!
# One minor near the identity

For a unitary matrix `k` and a diagonal projection `P`, the principal minor of `k` on the range of
`P` has squared modulus at most `exp (-‖[P, k]‖² / 2)` (`norm_principalMinor_sq_le_exp`).

For `g` in `USign ε` near `1` and `X = g - 1`, the coefficient `l.dsCoeff g` is
`l.flenstedJensen 1 y` for a matrix `y = (1 - u) g (1 - v)` with `u`, `v` strictly triangular, and
each principal minor of `kᴴ y k` on a set of lowest entries of `l` is
`exp (tr (P logOneAdd X) + ‖[P, X]‖² / 4 + r)` with an explicit bound for `r`
(`exists_principalMinor_eq_exp`). This rests on an exact formula for `det (1 + P X)` through
`logOneAdd` (`exists_det_compress_eq_exp_logOneAdd`). The norm of a matrix is the entrywise `ℓ²`
norm (`Norms.Frobenius`).
-/

@[expose] public section

noncomputable section

section SizeOfOneMinor

open Matrix Finset Norms.Frobenius Complex

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {P k : Matrix n n ℂ} {p : n → Prop}
  [DecidablePred p]

/-! ### The size of one minor -/

/-- The square of `|det Y|` is at most `exp (tr (Yᴴ Y - 1))`; this trace is real. -/
lemma norm_det_sq_le_exp (Y : Matrix n n ℂ) :
    ‖Y.det‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
  -- Use `x ≤ exp (x - 1)` on the eigenvalues `x ≥ 0` of `Yᴴ Y`.
  have hY : (Yᴴ * Y).IsHermitian := isHermitian_conjTranspose_mul_self Y
  have nonneg : ∀ i, 0 ≤ hY.eigenvalues i := eigenvalues_conjTranspose_mul_self_nonneg Y
  have trace_eq : (Yᴴ * Y - 1).trace.re = ∑ i, (hY.eigenvalues i - 1) := by
    rw [trace_sub, hY.trace_eq_sum_eigenvalues]
    simp
  calc ‖Y.det‖ ^ 2 = ‖(Yᴴ * Y).det‖ := by
        rw [det_mul, det_conjTranspose, norm_mul, norm_star, sq]
    _ = ∏ i, hY.eigenvalues i := by
        simp [hY.det_eq_prod_eigenvalues, abs_of_nonneg (nonneg _)]
    _ ≤ ∏ i, Real.exp (hY.eigenvalues i - 1) :=
        prod_le_prod₀ (fun i _ ↦ nonneg i) fun i _ ↦ by
          linarith only [Real.add_one_le_exp (hY.eigenvalues i - 1)]
    _ = Real.exp (Yᴴ * Y - 1).trace.re := by rw [trace_eq, Real.exp_sum]

/-- The principal minor of `X` on the indices satisfying `p` is `det (1 + P (X - 1))`, where `P` is
the diagonal projection to these indices. -/
lemma principalMinor_eq_det_coordProj (X : Matrix n n ℂ) (p : n → Prop) [DecidablePred p] :
    principalMinor X p = (1 + coordProj p * (X - 1)).det := by
  rw [principalMinor_eq_det, coordProj, sub_eq_add_neg, ← mul_neg, neg_sub]

/-- For a unitary matrix `k` and an orthogonal projection `P`, the crossing block
`M = (1 - P) k P` satisfies `Mᴴ M = P - P kᴴ P k P`. -/
lemma conjTranspose_mul_self_one_sub_mul_mul (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P := by
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP_adj]
  linear_combination (norm := noncomm_ring) P * kᴴ * hPP * k * P + P * hk * P + hPP

/-- For a unitary matrix `k` and an orthogonal projection `P`, the Frobenius norms of the
commutator and of the block `(1 - P) k P` satisfy `‖[P, k]‖² = 2 ‖(1 - P) k P‖²`. -/
lemma norm_lie_sq_of_unitary (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ‖⁅P, k⁆‖ ^ 2 = 2 * ‖(1 - P) * k * P‖ ^ 2 := by
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  -- Both sides are `2 (tr P - tr (P kᴴ P k))`.
  have lie_eq : ⁅P, k⁆ᴴ * ⁅P, k⁆ = kᴴ * (P * k) - kᴴ * (P * k * P) - P * kᴴ * P * k + P := by
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hP_adj]
    linear_combination (norm := noncomm_ring) kᴴ * hPP * k + P * hk * P + hPP
  have trace_conj : (kᴴ * (P * k)).trace = P.trace := by
    rw [trace_mul_comm, mul_assoc, hk', mul_one]
  have trace_left : (kᴴ * (P * k * P)).trace = (P * kᴴ * P * k).trace := by
    simp only [← mul_assoc, trace_mul_comm _ P]
  have trace_right : (P * kᴴ * P * k * P).trace = (P * kᴴ * P * k).trace := by
    simp only [trace_mul_comm _ P, ← mul_assoc, hPP]
  have block_eq : ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P :=
    conjTranspose_mul_self_one_sub_mul_mul hP hk
  rw [← ofReal_inj, ofReal_mul, ← trace_star_mul_self_eq_norm_sq,
    ← trace_star_mul_self_eq_norm_sq, lie_eq, block_eq]
  simp only [trace_add, trace_sub, trace_conj, trace_left, trace_right, ofReal_ofNat]
  ring

/-- Size of one minor: let `k` be a unitary matrix, `S` the set of indices satisfying `p`, and
`P = coordProj p` the diagonal projection to `S`. Then the principal minor of `k` on `S` satisfies
`|det_S k|² ≤ exp (-‖[P, k]‖² / 2)`. -/
theorem norm_principalMinor_sq_le_exp (p : n → Prop) [DecidablePred p] (hk : kᴴ * k = 1) :
    ‖principalMinor k p‖ ^ 2 ≤ Real.exp (-(‖⁅coordProj p, k⁆‖ ^ 2 / 2)) := by
  -- With `M = (1 - P) k P` and `Y = (1 - P) + P k P` we have `det_S k = det Y` and
  -- `Yᴴ Y = (1 - P) + P kᴴ P k P = 1 - Mᴴ M`, while `‖[P, k]‖² = 2 ‖M‖²`.
  have hP : IsStarProjection (coordProj p) := isStarProjection_coordProj p
  set P : Matrix n n ℂ := coordProj p
  have hPP : P * P = P := hP.isIdempotentElem
  let M : Matrix n n ℂ := (1 - P) * k * P
  let Y : Matrix n n ℂ := 1 - P + P * k * P
  have minor_eq : principalMinor k p = Y.det := by
    have Y_eq : Y = 1 + P * (k - 1) * P := by
      simp [Y, mul_sub, sub_mul, hPP, sub_add_eq_add_sub, add_sub_assoc]
    rw [principalMinor_eq_det_coordProj, Y_eq, det_one_add_mul_comm (P * (k - 1)), ← mul_assoc, hPP]
  have Y_sq : Yᴴ * Y = 1 - P + P * kᴴ * P * k * P := by
    simp [Y, hP.isSelfAdjoint.star_eq, ← star_eq_conjTranspose, add_mul, mul_add, mul_sub, sub_mul,
      ← mul_assoc, mul_assoc _ P P, hPP]
  have gram_eq : Yᴴ * Y - 1 = -(Mᴴ * M) := by
    rw [Y_sq, conjTranspose_mul_self_one_sub_mul_mul hP hk]
    abel
  calc ‖principalMinor k p‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
        rw [minor_eq]
        exact norm_det_sq_le_exp Y
    _ = Real.exp (-‖M‖ ^ 2) := by
        rw [gram_eq, trace_neg, trace_star_mul_self_eq_norm_sq, neg_re, ofReal_re]
    _ = Real.exp (-(‖⁅P, k⁆‖ ^ 2 / 2)) := by
        rw [norm_lie_sq_of_unitary hP hk, mul_div_cancel_left₀ _ two_ne_zero]

/-- The entry `(i, j)` of the commutator of `X` with the diagonal projection to the indices
satisfying `p` has the norm of `X i j` if exactly one of `p i`, `p j` holds, else it is `0`. -/
lemma norm_lie_coordProj_apply (X : Matrix n n ℂ) (i j : n) :
    ‖⁅coordProj p, X⁆ i j‖ = if p i ↔ p j then 0 else ‖X i j‖ := by
  by_cases hi : p i <;> by_cases hj : p j <;> simp [coordProj, Ring.lie_def, hi, hj]

end New.DiscreteSeries

end SizeOfOneMinor

section DeterminantOfCompression

open Ring Matrix Norms.Frobenius Complex intervalIntegral

namespace New.DiscreteSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {P Q X Y : Matrix n n ℂ} {δ c : ℝ}

attribute [local simp] mul_add add_mul mul_assoc lie_def IsIdempotentElem.eq
  IsIdempotentElem.mul_self_mul IsStarProjection.isIdempotentElem

/-- Let `P` and `Q` be orthogonal projections, and let `‖X‖ ≤ δ ≤ 1 / 2`, `tr ([P, Q] Y) = 0`,
`‖[P, X] - Y‖ ≤ δ c`, `‖Y‖ ≤ c` and `‖Q - P‖ ≤ c`. Then
`det (1 + P X) = exp (tr (Q logOneAdd X) - tr (Y ^ 2) / 4 + r)` with `|r| ≤ 100 δ c ^ 2`. -/
lemma exists_det_compress_eq_exp_logOneAdd (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hδ : δ ≤ 2⁻¹) (hX : ‖X‖ ≤ δ) (h_comm : (⁅P, Q⁆ * Y).trace = 0)
    (h_near : ‖⁅P, X⁆ - Y‖ ≤ δ * c) (hY : ‖Y‖ ≤ c) (hPQ : ‖Q - P‖ ≤ c) :
    ∃ r : ℂ, (1 + P * X).det = cexp ((Q * logOneAdd X).trace - 4⁻¹ * (Y * Y).trace + r) ∧
      ‖r‖ ≤ 100 * δ * c ^ 2 := by
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg X).trans hX
  have hc_nonneg : 0 ≤ c := (norm_nonneg Y).trans hY
  have hPX : ‖P * X‖ ≤ δ := norm_proj_mul_le hP hX
  have h_lie : ‖⁅P, X⁆‖ ≤ c + 2⁻¹ * c := (norm_le_insert' _ Y).trans (by grw [hY, h_near, hδ])
  -- `log det (1 + P X)` is the integral over `[0, 1]` of `tr ((1 + s P X)⁻¹ P X)`, by
  -- `det_one_add_eq_exp_trace_logOneAdd`, and `tr (Q logOneAdd X)` is that of
  -- `tr (Q (1 + s X)⁻¹ X)`. So the remainder `r` is the integral of the difference, corrected by
  -- `s tr (Y ^ 2) / 2`.
  have h_int_P := intervalIntegrable_trace_mul_inv_one_add_smul_mul (hPX.trans hδ) 1
  have h_int_Q := intervalIntegrable_trace_mul_inv_one_add_smul_mul (hX.trans hδ) Q
  have h_int_Y : IntervalIntegrable (fun s : ℝ ↦ (s : ℂ) * (2⁻¹ * (Y * Y).trace))
      MeasureTheory.volume 0 1 :=
    (continuous_ofReal.intervalIntegrable ..).mul_const _
  have h_integral : ∫ s : ℝ in 0..1, ((1 * ((1 + s • (P * X))⁻¹ * (P * X))).trace -
        (Q * ((1 + s • X)⁻¹ * X)).trace + s * (2⁻¹ * (Y * Y).trace)) =
      (logOneAdd (P * X)).trace - (Q * logOneAdd X).trace + 4⁻¹ * (Y * Y).trace := by
    rw [integral_add (h_int_P.sub h_int_Q) h_int_Y, integral_sub h_int_P h_int_Q,
      integral_trace_mul_inv_one_add_smul_mul (hPX.trans hδ) 1,
      integral_trace_mul_inv_one_add_smul_mul (hX.trans hδ) Q, integral_mul_const,
      integral_ofReal, integral_id]
    norm_num
    ring
  refine ⟨(logOneAdd (P * X)).trace - (Q * logOneAdd X).trace + 4⁻¹ * (Y * Y).trace, ?_, ?_⟩
  · rw [det_one_add_eq_exp_trace_logOneAdd (hPX.trans hδ)]
    congr 1
    ring
  -- It remains to bound the integrand at each `s ∈ (0, 1]`.
  rw [← h_integral]
  refine (norm_integral_le_of_norm_le_const (C := 100 * δ * c ^ 2) fun s hs ↦ ?_).trans_eq
    (by simp)
  have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by grind
  have hs_half : s / 2 ∈ Set.Icc (0 : ℝ) 1 := by grind
  -- The resolvents `W = (1 + s X)⁻¹` and `V = (1 + s P X)⁻¹` are within `2 δ` of `1`.
  have hsX : ‖s • X‖ ≤ δ := norm_smul_le_of_le_one s hX hs_mem
  have hsPX : ‖s • (P * X)‖ ≤ δ := norm_smul_le_of_le_one s hPX hs_mem
  have hW_mul : (1 + s • X) * (1 + s • X)⁻¹ = 1 :=
    one_add_mul_inv_one_add (hsX.trans_lt (by linarith))
  have hW_mul' : (1 + s • X)⁻¹ * (1 + s • X) = 1 :=
    inv_one_add_mul_one_add (hsX.trans_lt (by linarith))
  have hW : ‖(1 + s • X)⁻¹ - 1‖ ≤ 2 * δ :=
    (norm_inv_one_add_sub_one_le (hsX.trans hδ)).trans (by linarith)
  have hV_mul : (1 + s • (P * X)) * (1 + s • (P * X))⁻¹ = 1 :=
    one_add_mul_inv_one_add (hsPX.trans_lt (by linarith))
  have hV_mul' : (1 + s • (P * X))⁻¹ * (1 + s • (P * X)) = 1 :=
    inv_one_add_mul_one_add (hsPX.trans_lt (by linarith))
  have hV : ‖(1 + s • (P * X))⁻¹ - 1‖ ≤ 2 * δ :=
    (norm_inv_one_add_sub_one_le (hsPX.trans hδ)).trans (by linarith)
  set W : Matrix n n ℂ := (1 + s • X)⁻¹
  set V : Matrix n n ℂ := (1 + s • (P * X))⁻¹
  set A : Matrix n n ℂ := ⁅P, X⁆
  set D : Matrix n n ℂ := Q - P
  let Z : Matrix n n ℂ := W - 1
  let N : Matrix n n ℂ := Z * (A * Z + A) + A * Z
  -- Rewrite the integrand as four traces, each of a product with one factor of size `δ` and two
  -- of size `c`. The identity uses `W (1 + s X) = 1`, `V (1 + s P X) = 1`, `P ^ 2 = P`,
  -- `Q ^ 2 = Q`, `tr ([P, Q] Y) = 0` and `tr (M M') = tr (M' M)`.
  have h_split : (1 * (V * (P * X))).trace - (Q * (W * X)).trace + s * (2⁻¹ * (Y * Y).trace) =
      trace ((P * D + Q * D - D) * (A - Y + Z * A - s • (N + A) * X)) -
        trace (s • (P * A) * ((N + A) * (V - 1) + N)) -
        trace ((D - P * D - P * D) * D * (X + Z * X)) -
        trace ((s / 2) • (A - Y) * (A + Y)) := by
    linear_combination (norm := (
      simp +zetaDelta only [hP, hQ, trace_mul_comm P, trace_mul_comm V, trace_mul_comm Y (_ * _),
        trace_mul_comm X (P * X), mul_sub, sub_mul, mul_add, add_mul, mul_assoc, one_mul, mul_one,
        lie_def, IsStarProjection.isIdempotentElem, IsIdempotentElem.eq,
        IsIdempotentElem.mul_self_mul, trace_sub, trace_add, trace_smul, smul_add,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, real_smul, ofReal_div, ofReal_ofNat]
      ring_nf))
      h_comm + congr(($hV_mul' * P * W * X * P +
        V * P * (A * ($hW_mul' * P * (1 - W) + W * P * $hW_mul) - $hW_mul * X * P) +
        (1 - P) * $hV_mul * P * X - ⁅P, D⁆ * ($hW_mul' * P * W - W * P * $hW_mul) * X).trace)
  rw [h_split]
  apply le_trans
  · apply_rules (transparency := .reducible) (maxDepth := 99)
      [norm_smul_le_of_le_one s (hρ := hs_mem), norm_smul_le_of_le_one (s / 2) (hρ := hs_half),
      norm_proj_mul_le hP, norm_proj_mul_le hQ, @norm_trace_mul_le, norm_sub_le_of_le,
      norm_add_le_of_le, norm_mul_le_of_le]
  · have hδc := mul_nonneg hδ_nonneg (sq_nonneg c)
    linarith [mul_le_mul_of_nonneg_right hδ hδc,
      mul_le_mul_of_nonneg_right hδ (mul_nonneg hδ_nonneg hδc)]

end New.DiscreteSeries

end DeterminantOfCompression

section MinorExpansion

open Ring Matrix Norms.Frobenius Complex ComplexConjugate

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {h : ℕ} {l : HCParam ε}
  {X : Matrix n n ℂ}

attribute [local simp] mul_add add_mul mul_assoc lie_def principalMinor_eq_det coordProj

/-- The determinant of a matrix that is triangular for an injective order `o` is the product of
its diagonal entries. -/
lemma det_eq_prod_diag_of_blockTriangular {b : Matrix n n ℂ} {o : n → ℤ} (ho : o.Injective) :
    b.BlockTriangular o → b.det = ∏ i, b i i :=
  let := LinearOrder.lift' o ho
  det_of_isUpperTriangular

/-- The value of `l.flenstedJensen 1` at `zᴴ` is the conjugate of its value at `z`. -/
lemma conj_flenstedJensen_one (z : Matrix n n ℂ) :
    conj (l.flenstedJensen 1 z) = l.flenstedJensen 1 zᴴ := by
  simp [flenstedJensen, conj_weightMinors, ← integral_conj, mul_comm, mul_assoc]

/-- Let `u` be block diagonal and strictly triangular: `u i j = 0` unless `l i < l j` and
`ε i = ε j`. If `X` and `(1 - u) * X` are accretive, then `l.flenstedJensen 1` at
`((1 - u) * X)ᴴ` is the conjugate of its value at `X`. -/
lemma flenstedJensen_shift_eq_conj (hl : l.HasGap h) {u : Matrix n n ℂ}
    (hu : ∀ i j, ¬(l i < l j ∧ ε i = ε j) → u i j = 0) (hX : X.IsAccretive)
    (huX : ((1 - u) * X).IsAccretive) :
    l.flenstedJensen 1 ((1 - u) * X)ᴴ = conj (l.flenstedJensen 1 X) := by
  have h_det : (1 - u).det ≠ 0 ∧ X.det ≠ 0 := by simpa [det_mul] using huX.det_ne_zero
  -- `1 - u` is block diagonal and triangular, with diagonal entries `1`.
  have hu_mem : 1 - u ∈ blockDiagAlg ε := mem_blockDiagAlg.2 fun i j hij ↦ by
    simp [one_apply_ne (show i ≠ j by rintro rfl; exact hij rfl), hu i j (by tauto)]
  have hu_borel : IsBorelMatrix (-(-l)) (1 - u) := ⟨fun i j hij ↦ by
    have h_lt : l j < l i := by simpa using hij
    simp [one_apply_ne (show i ≠ j by rintro rfl; exact lt_irrefl _ h_lt),
      hu i j fun h' ↦ lt_asymm h_lt h'.1], h_det.1⟩
  -- Move the factor `1 - u` from the second argument to the first, where it acts by a character
  -- with value `1`.
  have h_move : l.flenstedJensen (1 - u) X = l.flenstedJensen 1 ((1 - u) * X) := by
    have := flenstedJensen_eq_of_accretive hl (one_mem _) (by simpa using huX) hu_mem
      (g := (1 - u) * X) (by simp_all)
    simp_all
  have h_char : l.flenstedJensen (1 - u) X = l.flenstedJensen 1 X := by
    have h_minors (k : maxCompactU ε) :
        weightMinors l.lowestKType ((1 - u) * (k : Matrix n n ℂ)) =
          weightMinors l.lowestKType (k : Matrix n n ℂ) := by
      rw [hl.isKDominant_lowestKType.weightMinors_oppBorel_mul hl.neg.injective
        ((Matrix.isUnit_iff_isUnit_det _).1 k.val.val.isUnit).ne_zero hu_mem hu_borel]
      simp [diagChar, show ∀ i, u i i = 0 from fun i ↦ hu i i (by simp)]
    simp [flenstedJensen, h_minors]
  rw [← conj_flenstedJensen_one, ← h_move, h_char]

/-- Let `l` have gap `h` and let `X = g - 1` have norm less than `1 / 1000`. There is a matrix `y`
with `l.dsCoeff g = l.flenstedJensen 1 y` such that, for `k ∈ K = maxCompactU ε` and the diagonal
projection `P = coordProj p` to a set `p` of lowest entries of `l`, the principal minor of
`kᴴ y k` on `p` is `exp (tr (P logOneAdd X) + ‖[P, X]‖² / 4 + r)` with
`|r| ≤ 2 · 10⁵ ‖X‖ (‖[P, X]‖² + ‖[P, k]‖²)`. -/
lemma exists_principalMinor_eq_exp (hl : l.HasGap h) (g : USign ε)
    (hg : ‖(g : Matrix n n ℂ) - 1‖ < 1000⁻¹) :
    ∃ y : Matrix n n ℂ, l.dsCoeff g = l.flenstedJensen 1 y ∧
      ∀ (p : n → Prop) [DecidablePred p], (∀ i j, p i → ¬p j → l i < l j) →
        ∀ k : maxCompactU ε, ∃ r : ℂ,
          principalMinor ((k : Matrix n n ℂ)ᴴ * y * (k : Matrix n n ℂ)) p =
            cexp ((coordProj p * logOneAdd ((g : Matrix n n ℂ) - 1)).trace +
              ‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 / 4 + r) ∧
          ‖r‖ ≤ 200000 * ‖(g : Matrix n n ℂ) - 1‖ *
            (‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 +
              ‖⁅coordProj p, (k : Matrix n n ℂ)⁆‖ ^ 2) := by
  set X : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  have hX_nonneg : 0 ≤ ‖X‖ := norm_nonneg X
  have hX_half : ‖X‖ ≤ 2⁻¹ := by linarith
  have hX_four : 4 * ‖X‖ ≤ 2⁻¹ := by linarith
  -- `r c` is the part of `X` strictly below the diagonal for the order `c`, inside the blocks of
  -- `ε`. Multiply `g` by the unipotent factors `1 - u` and `1 - r c`.
  let r (c : n → ℤ) : Matrix n n ℂ := lowerMask ε c X
  let u : Matrix n n ℂ := r (-l)
  let y (c : n → ℤ) : Matrix n n ℂ := (1 - u) * g * (1 - r c)
  let m : Matrix n n ℂ := X - u - u * X
  have hu : ‖u‖ ≤ ‖X‖ := norm_entryMask_le
  have hr (c : n → ℤ) : ‖r c‖ ≤ ‖X‖ := norm_entryMask_le
  have hm : ‖m‖ ≤ ‖X‖ + ‖X‖ + ‖X‖ * ‖X‖ :=
    norm_sub_le_of_le (norm_sub_le_of_le (le_refl ‖X‖) hu) (norm_mul_le_of_le hu le_rfl)
  have hm' : ‖m‖ ≤ 3 * ‖X‖ := by nlinarith [mul_le_mul_of_nonneg_right hX_half hX_nonneg]
  have hy_near (c : n → ℤ) : ‖y c - 1‖ ≤ 4 * ‖X‖ := by
    have h_eq : y c - 1 = m - r c - m * r c := by
      have hgX : (g : Matrix n n ℂ) = 1 + X := by simp [X]
      simp only [y, m, hgX]
      noncomm_ring
    rw [h_eq]
    have := norm_sub_le_of_le (norm_sub_le_of_le hm (hr c)) (norm_mul_le_of_le hm (hr c))
    nlinarith [mul_le_mul_of_nonneg_right hg.le hX_nonneg,
      mul_le_mul_of_nonneg_right hg.le (mul_nonneg hX_nonneg hX_nonneg)]
  -- Step 1: the coefficient is `l.flenstedJensen 1 (y l)`. Removing either factor conjugates the
  -- value.
  have hy_acc (c : n → ℤ) : (y c).IsAccretive :=
    isAccretive_of_norm_sub_one_lt ((hy_near c).trans_lt (by linarith))
  have hg_acc : (g : Matrix n n ℂ).IsAccretive :=
    isAccretive_of_norm_sub_one_lt (hg.trans (by norm_num))
  have hug_acc : ((1 - u) * (g : Matrix n n ℂ)).IsAccretive := by
    simpa [y, show r 0 = 0 from rfl] using hy_acc 0
  have h_coeff : l.dsCoeff g = l.flenstedJensen 1 (y l) := by
    have h_left := flenstedJensen_shift_eq_conj hl (u := u) (by simp [u, r]; grind) hg_acc hug_acc
    have h_right := flenstedJensen_shift_eq_conj hl (u := (r l)ᴴ)
      (X := ((1 - u) * (g : Matrix n n ℂ))ᴴ) (by simp [r]; grind)
      (by simpa [IsAccretive, add_comm] using hug_acc)
      (by simpa [y, IsAccretive, add_comm] using hy_acc l)
    rw [dsCoeff_eq_flenstedJensen hl (one_mem _) (by simpa using hg_acc)]
    simpa [y] using (h_right.trans (congrArg _ h_left)).symm
  -- Step 2: on a set of highest entries of `l` the triangular factors do not change the minor.
  have h_minor (p : n → Prop) [DecidablePred p] (hp : ∀ i j, p i → ¬p j → l j < l i) :
      principalMinor (y l) p = principalMinor (g : Matrix n n ℂ) p := by
    clear * - hp hl
    rw [principalMinor_mul, principalMinor_mul, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hl.injective, mul_comm, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hl.neg.injective] <;>
      simp [u, r, BlockTriangular, Matrix.one_apply] <;> grind
  refine ⟨y l, h_coeff, fun p _ hp κ ↦ ?_⟩
  -- Step 3: one minor. Notation: `P` projects to `p`, `Q = k P kᴴ`, and `A`, `B`, `C` are the
  -- commutators of `P` with `X`, `u`, `r l`.
  set k : Matrix n n ℂ := (κ : Matrix n n ℂ)
  let s : Matrix n n ℂ := signMatrix ε
  have hk : kᴴ * k = 1 := (U_one_mem_unitaryGroup ⟨_, κ.property⟩).1
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hk_mem : k ∈ blockDiagAlg ε := mem_maxCompactU.1 κ.property
  have hP : IsStarProjection (coordProj p) := isStarProjection_coordProj p
  have hsP : Commute s (coordProj p) := commute_diagonal ..
  set P : Matrix n n ℂ := coordProj p
  set A : Matrix n n ℂ := ⁅P, X⁆
  set B : Matrix n n ℂ := ⁅P, u⁆
  set C : Matrix n n ℂ := ⁅P, r l⁆
  set G : Matrix n n ℂ := B * X + u * A
  let Q : Matrix n n ℂ := k * P * kᴴ
  let V : Matrix n n ℂ := (1 + X)⁻¹ - 1
  let H : Matrix n n ℂ := G + m * C - (G + B - A) * r l
  have ⟨h_mask, hB⟩ : (∀ c, ⁅P, r c⁆ = lowerMask ε c A) ∧ B = blockDiagPart ε A - C := by
    simp +zetaDelta [← ext_iff, blockDiagPart]
    grind
  have h_det_compl (x : Matrix n n ℂ) :
      (1 + (1 - P) * (x - 1)).det = principalMinor x (¬p ·) := by
    simp [P, det_apply, sub_mul]
    grind
  have hP_compl : IsStarProjection (1 - P) := hP.one_sub
  have hA_nonneg : 0 ≤ ‖A‖ := norm_nonneg A
  have hPk_nonneg : 0 ≤ ‖⁅P, k⁆‖ := norm_nonneg _
  have hP_star : Pᴴ = P := hP.isSelfAdjoint
  have hV : ‖V‖ ≤ 2 * ‖X‖ := norm_inv_one_add_sub_one_le hX_half
  have hB_le : ‖B‖ ≤ ‖A‖ := by
    rw [show B = lowerMask ε (-l) A from h_mask (-l)]
    exact norm_entryMask_le
  have hC_le : ‖C‖ ≤ ‖A‖ := by
    rw [show C = lowerMask ε l A from h_mask l]
    exact norm_entryMask_le
  have hg_inv : (g : Matrix n n ℂ)⁻¹ = signMatrix ε * (g : Matrix n n ℂ)ᴴ * signMatrix ε := by
    simp [← U.coe_inv (signMatrix_mul_self ε)]
  have hg_star : (g : Matrix n n ℂ)ᴴ = s * (g : Matrix n n ℂ)⁻¹ * s := by
    grind [signMatrix_mul_self]
  have hkPk : k * ⁅P, k⁆ᴴ = P - Q := by simp [Q, mul_sub, ← mul_assoc, hk', hP_star]
  have hPQ : ‖P - Q‖ ≤ ‖⁅P, k⁆‖ :=
    (hkPk ▸ frobenius_norm_mul_of_unitary hk _).trans_le (norm_star _).le
  -- `[P, y l - 1]` is `A - B - C` up to the second order term `H`.
  have hH : ‖H‖ ≤ 8 * ‖X‖ * ‖A‖ := by
    have hG : ‖G‖ ≤ ‖A‖ * ‖X‖ + ‖X‖ * ‖A‖ :=
      norm_add_le_of_le (norm_mul_le_of_le hB_le le_rfl) (norm_mul_le_of_le hu le_rfl)
    have := norm_sub_le_of_le (norm_add_le_of_le hG (norm_mul_le_of_le hm' hC_le))
      (norm_mul_le_of_le (norm_sub_le_of_le (norm_add_le_of_le hG hB_le) (le_refl ‖A‖)) (hr l))
    linarith [mul_nonneg hX_nonneg hA_nonneg,
      mul_le_mul_of_nonneg_right hX_half (mul_nonneg hX_nonneg hA_nonneg)]
  -- The complementary minor of `g`.
  let ⟨x, hx_eq, hx⟩ := exists_det_compress_eq_exp_logOneAdd (Y := -A) hP_compl hP_compl hX_half
    (le_refl ‖X‖) (by simp) (by simp [A, mul_sub, sub_mul, mul_nonneg]) (norm_neg A).le (by simp)
  -- The complementary minor of `y l`, which is that of `g`.
  have h_near_compl : ‖⁅1 - P, y l - 1⁆ - (B + C - A)‖ ≤ 4 * ‖X‖ * (4 * ‖A‖) := by
    rw [show ⁅1 - P, y l - 1⁆ - (B + C - A) = H by simp +zetaDelta only [lie_def]; noncomm_ring]
    linarith [mul_nonneg hX_nonneg hA_nonneg]
  let ⟨z, hz_eq, hz⟩ := exists_det_compress_eq_exp_logOneAdd (Y := B + C - A) hP_compl hP_compl
    hX_four (hy_near l) (by simp) h_near_compl
    (by linarith [norm_sub_le_of_le (norm_add_le_of_le hB_le hC_le) (le_refl ‖A‖)]) (by simp)
  -- The minor of `kᴴ (y l) k` on `p`, as `det (1 + Q (y l - 1))`.
  have h_comm : (⁅Q, P⁆ * (A - B - C)).trace = 0 := by
    simp [Q, s, hB, blockDiagPart_eq, hsP.eq, trace_mul_comm P,
      (mem_blockDiagAlg_iff_commute.1 hk_mem).left_comm,
      A, X, inv_eq_left_inv hk ▸ blockDiagAlg.inv_mem hk_mem _ rfl, trace_mul_comm k,
      trace_mul_comm kᴴ, trace_mul_comm s, signMatrix_mul_self, mul_sub, sub_mul]
    ring_nf
  have h_near : ‖⁅Q, y l - 1⁆ - (A - B - C)‖ ≤ 4 * ‖X‖ * (4 * (‖A‖ + ‖⁅P, k⁆‖)) := by
    rw [show ⁅Q, y l - 1⁆ - (A - B - C) = (y l - 1) * (P - Q) - (P - Q) * (y l - 1) - H by
      simp +zetaDelta only [lie_def]; noncomm_ring]
    have := norm_sub_le_of_le (norm_sub_le_of_le (norm_mul_le_of_le (hy_near l) hPQ)
      (norm_mul_le_of_le hPQ (hy_near l))) hH
    linarith [mul_nonneg hX_nonneg hA_nonneg, mul_nonneg hX_nonneg hPk_nonneg]
  let ⟨t, ht_eq, ht⟩ := exists_det_compress_eq_exp_logOneAdd (P := Q) (Y := A - B - C)
    (hP.map (Unitary.conjStarAlgAut ℂ _ ⟨k, hk, hk'⟩)) hP hX_four (hy_near l) h_comm h_near
    (by linarith [norm_sub_le_of_le (norm_sub_le_of_le (le_refl ‖A‖) hB_le) hC_le])
    (by linarith)
  rw [h_det_compl, h_minor _ (by tauto), ← h_det_compl, hx_eq] at hz_eq
  have h_conj : principalMinor (kᴴ * y l * k) p = (1 + Q * (y l - 1)).det := by
    simp only [mul_assoc, principalMinor_eq_det, coordProj, det_one_add_mul_comm k, Q, P]
    noncomm_ring [hk]
  have h_det_y : (1 + (y l - 1)).det = (1 + X).det := by
    simpa [principalMinor_of_forall, X] using h_minor ⊤
  have h_det : cexp (logOneAdd (y l - 1)).trace = cexp (logOneAdd X).trace := by
    rw [← det_one_add_eq_exp_trace_logOneAdd ((hy_near l).trans hX_four), h_det_y,
      det_one_add_eq_exp_trace_logOneAdd hX_half]
  -- The remainder: those of the three determinants, and the difference between `‖A‖ ^ 2` and
  -- `-tr (A ^ 2)`, which comes from `Xᴴ = s ((1 + X)⁻¹ - 1) s`.
  have h_corr : ‖((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace‖ ≤
      (2 * ‖X‖ * (‖A‖ * (2 * ‖X‖) + ‖A‖) + ‖A‖ * (2 * ‖X‖)) *
        (‖A‖ + ‖A‖ + ‖A‖ + ‖A‖ + ‖A‖) :=
    norm_trace_mul_le (norm_smul_le_of_le_one 4⁻¹ (norm_add_le_of_le (norm_mul_le_of_le hV
      (norm_add_le_of_le (norm_mul_le_of_le le_rfl hV) le_rfl)) (norm_mul_le_of_le le_rfl hV))
      ⟨by norm_num, by norm_num⟩) (norm_sub_le_of_le (norm_sub_le_of_le (norm_sub_le_of_le
      (norm_sub_le_of_le le_rfl hB_le) hC_le) hB_le) hC_le)
  refine ⟨t + z - x + ((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace,
    ?_, ?_⟩
  · -- Multiply by the complementary minor and by `det (y l) = det g`, and compare exponents.
    refine h_conj.trans (ht_eq.trans (mul_right_cancel₀ (by simp)
      (congr(_ * ($hz_eq * $h_det)).trans ?_)))
    simp [V, s, hg_star, hP_star, hB, blockDiagPart_eq, hsP.eq, trace_mul_comm P,
      ← ofReal_pow, A, X, trace_mul_comm s, signMatrix_mul_self, ← mul_assoc s s, ← exp_add,
      mul_sub, sub_mul, ← trace_star_mul_self_eq_norm_sq]
    ring_nf
  · have := norm_add_le_of_le (norm_sub_le_of_le (norm_add_le_of_le ht hz) hx) h_corr
    linarith [mul_nonneg hX_nonneg (sq_nonneg ‖A‖), mul_nonneg hX_nonneg (sq_nonneg ‖⁅P, k⁆‖),
      mul_nonneg hX_nonneg (sq_nonneg (‖A‖ - ‖⁅P, k⁆‖)),
      mul_le_mul_of_nonneg_right hX_half (mul_nonneg hX_nonneg (sq_nonneg ‖A‖))]

end New.DiscreteSeries

end MinorExpansion
end
end
end

/-!
# The Gaussian shape of the coefficient

Near `1` the coefficient `l.dsCoeff g` of a discrete series with a large gap is nearly the phase
`exp (tr μ log g)` times a number in `[0, 1]`, where `μ` is the weight `l.lowestKType`
(`exists_norm_dsCoeff_div_cexp_sub_le`). The coefficient is a mean over `K` of a quotient of
products of minors, and the estimates for one minor are multiplied over the sets `{i | t ≤ w i}` of
a weight `w`. In the comments, `λ^ρ` is `paramAddRho l` and `Q_w` is `gapWeightedNormSq w`.
The Gaussian is `exp (-q)` with `q = Q_{-λ^ρ} (g - 1) / 4`; note `Q_{-w} = Q_w`.
Except in the first section, the norm of a matrix is the Frobenius norm.

* `USign ε` is the unitary group of the form `diag ε`; `K = maxCompactU ε` is its subgroup of
  unitary matrices, with the Haar measure `haarK ε` of mass one.
* `l : HCParam ε` is a doubled Harish-Chandra parameter `2λ`; `paramAddRho l` is `λ + ρ` and
  `l.lowestKType` is `λ + ρ - 2ρ_c`.
* `weightMinors w g` is the product over `t : ℤ` of the principal minors of `g` on the sets
  `{i | t ≤ w i}`, those with `t ≤ 0` divided by `det g`; `w.kTypeNormSq` is the mean of its
  squared modulus over `K`.
* `l.flenstedJensen g z` is the mean over `k ∈ K` of
  `weightMinors μ (g k) * conj (weightMinors μ k) / weightMinors (-paramAddRho l) (kᴴ z k)`,
  divided by `μ.kTypeNormSq` (Flensted-Jensen's integral); the matrix coefficient `l.dsCoeff` is
  defined through it.

## Relation to the literature

See `New.Appendix.DiscreteSeries.Periods` for related work.
-/

@[expose] public section

open Matrix MeasureTheory Finset Fintype Ring Complex ComplexConjugate

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l : HCParam ε} {δ T q : ℝ}
  {h L A : ℕ} {a b : ℤ} {w : n → ℤ}

section Dimension

open Norms.L2Operator

/-- Let the parameter `l = 2λ` have gap `500 n ^ 3 + A` (the entries of `λ` are distinct, and those
with different signs `ε` are this far apart) and `|l i| ≤ L`. Then the mean `μ.kTypeNormSq` over
`K = maxCompactU ε` of the squared modulus of the highest weight coefficient `weightMinors μ`, for
`μ = l.lowestKType`, is at least `1 / (4 (2000 (n + L + 1) ^ 6) ^ (2 n ^ 2))`. -/
lemma one_le_pow_mul_kTypeNormSq [Nonempty n] (hl : l.HasLargeGap A) (hL : ∀ i : n, |l i| ≤ L) :
    1 ≤ (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * (4 * l.lowestKType.kTypeNormSq) := by
  -- Compare volume and integral on `K`, which has mass one: all of `K` lies in the unit ball for
  -- the operator norm (opened in this section), and `l.dsCoeff k = weightMinors μ k` there.
  have h_univ : {k : maxCompactU ε | ‖(k : Matrix n n ℂ)‖ ≤ 1} = Set.univ :=
    Set.eq_univ_of_forall fun k ↦
      (CStarRing.norm_of_mem_unitary (U_one_mem_unitaryGroup ⟨_, k.property⟩)).le
  have h_ball : haarK ε {k : maxCompactU ε | ‖(k : Matrix n n ℂ)‖ ≤ 1} ≤
      ENNReal.ofReal ((2000 * (card n + L + 1) ^ 6 * 1 ^ 2) ^ (2 * card n ^ 2)) *
        ENNReal.ofReal (∫ k : maxCompactU ε, 4 * ‖l.dsCoeff k‖ ^ 2 ∂haarK ε) :=
    measure_ball_le_integral_dsCoeff (hg := hl) hL (haarK ε) (maxCompactU ε).subtype
      integrable_of_compactSpace 1 le_rfl
  rw [← ENNReal.one_le_ofReal, ENNReal.ofReal_mul (by positivity)]
  simpa [h_univ, dsCoeff_of_mem_maxCompactU, integral_const_mul] using h_ball

/-- Let the parameter `l = 2λ` have gap `500 n ^ 3 + A` and `|l i| ≤ L`, and let `T` be at least
`1`, `n ^ 2` and `n ^ 2 log (n + L + 1)`. Then the mean `μ.kTypeNormSq` over `K = maxCompactU ε` of
the squared modulus of the highest weight coefficient `weightMinors μ`, for `μ = l.lowestKType`, is
at least `exp (-5000 T)`. The inverse of `μ.kTypeNormSq` plays the part of the dimension of the
lowest `K`-type, so this takes the place of the bound from Weyl's dimension formula. -/
lemma exp_neg_le_kTypeNormSq [Nonempty n] (hl : l.HasLargeGap A) (hL : ∀ i : n, |l i| ≤ L)
    (hT : 1 ≤ T) (hT_card : card n ^ 2 ≤ T)
    (hT_log : card n ^ 2 * Real.log (card n + L + 1) ≤ T) :
    Real.exp (-(5000 * T)) ≤ l.lowestKType.kTypeNormSq := by
  have h_pos : 0 < l.lowestKType.kTypeNormSq := kTypeNormSq_pos l.lowestKType
  -- Take logarithms in the lower bound.
  have h_log : 0 ≤ 2 * card n ^ 2 * (Real.log 2000 + 6 * Real.log (card n + L + 1)) +
      (Real.log 4 + Real.log l.lowestKType.kTypeNormSq) := by
    simpa (disch := positivity) [Real.log_mul, Real.log_pow] using
      Real.log_nonneg (one_le_pow_mul_kTypeNormSq hl hL)
  -- Here `log 2000 ≤ 2000` and `log 4 ≤ 4` suffice.
  have h_mul : (card n : ℝ) ^ 2 * Real.log 2000 ≤ card n ^ 2 * 2000 := by
    grw [Real.log_le_self (by norm_num)]
  exact (Real.le_log_iff_exp_le h_pos).1
    (by linarith [Real.log_le_self (zero_le_four : (0 : ℝ) ≤ 4)])

end Dimension

open Norms.Frobenius

/-- The quadratic form `Q_w (X) = ∑_{i, j} |w i - w j| |X i j| ^ 2`. -/
noncomputable abbrev gapWeightedNormSq (w : n → ℤ) (X : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, |w i - w j| * ‖X i j‖ ^ 2

omit [DecidableEq n] in
lemma gapWeightedNormSq_nonneg (w : n → ℤ) (X : Matrix n n ℂ) : 0 ≤ gapWeightedNormSq w X := by
  positivity

/-- Let the entries of `w` lie in `[a, b]`, and let `P_t = coordProj (t ≤ w ·)` be the projection
to the coordinates `{i | t ≤ w i}`. The squared Frobenius norms of the commutators `[P_t, X]`,
`a < t ≤ b`, add up to `Q_w (X) = ∑_{i, j} |w i - w j| |X i j| ^ 2`, because exactly
`|w i - w j|` of these sets separate `i` from `j`. -/
lemma sum_norm_lie_coordProj_sq (hw : ∀ i : n, a ≤ w i ∧ w i ≤ b) (X : Matrix n n ℂ) :
    ∑ t ∈ Ioc a b, ‖⁅coordProj (t ≤ w ·), X⁆‖ ^ 2 = gapWeightedNormSq w X := by
  have h_card (i j : n) : (#{t ∈ Ioc a b | ¬(t ≤ w i ↔ t ≤ w j)} : ℤ) = |w i - w j| := by
    rw [show {t ∈ Ioc a b | ¬(t ≤ w i ↔ t ≤ w j)} = Ioc (w i ⊓ w j) (w i ⊔ w j) by grind,
      Int.card_Ioc, max_sub_min_eq_abs', Int.toNat_of_nonneg (abs_nonneg _)]
  have h_entry (t : ℤ) (i j : n) :
      ‖⁅coordProj (t ≤ w ·), X⁆ i j‖ ^ 2 = if t ≤ w i ↔ t ≤ w j then 0 else ‖X i j‖ ^ 2 := by
    simp [norm_lie_coordProj_apply, ite_pow]
  simp only [frobenius_norm_sq_eq_sum_norm_sq, h_entry, (Ioc a b).sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by simp [sum_ite, ← h_card]

/-- If the entries of `w` lie in `[a, b]`, the projections `coordProj (t ≤ w ·)` to the coordinates
`{i | t ≤ w i}`, `a < t ≤ b`, add up to `diag w - a`; this is the resulting identity for their
traces against `X`. -/
lemma sum_trace_coordProj_mul (hw : ∀ i : n, a ≤ w i ∧ w i ≤ b) (X : Matrix n n ℂ) :
    ∑ t ∈ Ioc a b, (coordProj (t ≤ w ·) * X).trace = (intDiagonal w * X).trace - a * X.trace := by
  have h_card (i : n) : (#{t ∈ Ioc a b | t ≤ w i} : ℤ) = w i - a := by
    rw [show {t ∈ Ioc a b | t ≤ w i} = Ioc a (w i) by grind, Int.card_Ioc,
      Int.toNat_of_nonneg (sub_nonneg.2 (hw i).1)]
  simp only [trace, diag_apply, coordProj, diagonal_mul, (Ioc a b).sum_comm, mul_sum,
    ← sum_sub_distrib, ← sub_mul]
  exact sum_congr rfl fun i _ ↦ by simp [sum_ite, ← Int.cast_sub, ← h_card]

/-- An element of `K = maxCompactU ε` is a unitary matrix. -/
lemma maxCompactU_conjTranspose_mul_self (k : maxCompactU ε) :
    (k : Matrix n n ℂ)ᴴ * (k : Matrix n n ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (U_one_mem_unitaryGroup ⟨_, k.property⟩)

/-- On `K = maxCompactU ε`, the product of principal minors `weightMinors w` decays like a Gaussian:
its squared modulus at `k` is at most `exp (-Q_w (k) / 2)`. -/
lemma norm_weightMinors_sq_le_exp (w : n → ℤ) (k : maxCompactU ε) :
    ‖weightMinors w k‖ ^ 2 ≤ Real.exp (-(gapWeightedNormSq w k / 2)) := by
  -- Multiply the bounds for one minor, and use that `det k` has modulus one.
  let M : ℤ := ∑ j : n, |w j|
  have hw : ∀ i : n, -M ≤ w i ∧ w i ≤ M := neg_sum_abs_le_and_le_sum_abs w
  calc ‖weightMinors w k‖ ^ 2
      = ∏ t ∈ Ioc (-M) M, ‖principalMinor (k : Matrix n n ℂ) (t ≤ w ·)‖ ^ 2 := by
        rw [weightMinors_eq_det_zpow_mul_prod (GeneralLinearGroup.det_ne_zero _) _ _ hw, norm_mul,
          norm_zpow, U.norm_det, _root_.one_zpow, one_mul, norm_prod, prod_pow]
    _ ≤ ∏ t ∈ Ioc (-M) M, Real.exp (-(‖⁅coordProj (t ≤ w ·), (k : Matrix n n ℂ)⁆‖ ^ 2 / 2)) :=
        prod_le_prod₀ (fun t _ ↦ sq_nonneg _) fun t _ ↦
          norm_principalMinor_sq_le_exp _ (maxCompactU_conjTranspose_mul_self k)
    _ = Real.exp (-(gapWeightedNormSq w k / 2)) := by
        rw [← Real.exp_sum, sum_neg_distrib, ← sum_div, sum_norm_lie_coordProj_sq hw]

/-- The entries of `paramAddRho l - l.lowestKType = 2 ρ_c` (written `twoRho l (ε · = ε ·)`) are at
most `n` in modulus, so the traces of `Z` against the diagonal matrices of the two weights differ
by at most `n ^ 2 ‖Z‖` (Frobenius norm). -/
lemma norm_trace_paramAddRho_sub_trace_lowestKType_le (l : HCParam ε) (Z : Matrix n n ℂ) :
    ‖(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace‖ ≤
      card n ^ 2 * ‖Z‖ := by
  have h_rho (i : n) : ‖(twoRho l (ε · = ε ·) i : ℂ)‖ ≤ card n :=
    (norm_intCast _).trans_le (mod_cast abs_twoRho_le (ε · = ε ·) i l)
  calc _ = ‖∑ i : n, twoRho l (ε · = ε ·) i * Z i i‖ := by simp [trace, lowestKType, sub_mul]
    _ ≤ ∑ _i : n, card n * ‖Z‖ :=
        norm_sum_le_of_le _ fun i _ ↦ norm_mul_le_of_le (h_rho i) (norm_apply_le_frobenius_norm ..)
    _ = card n ^ 2 * ‖Z‖ := by simp [sq, mul_assoc]

/-- For `k ∈ K = maxCompactU ε` we have `Q_{-λ^ρ} (k) ≤ Q_μ (k) + 2 n ^ 2`. This holds because
`λ^ρ - μ = 2ρ_c` has entries at most `n` in modulus and `‖k‖ ^ 2 = n` (Frobenius norm). Here `2ρ_c`
is the sum of the compact roots (`ε i = ε j`) positive for `l`. -/
lemma gapWeightedNormSq_neg_paramAddRho_le (l : HCParam ε) (k : maxCompactU ε) :
    gapWeightedNormSq (-paramAddRho l) k ≤ gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2 := by
  have h_norm : ‖(k : Matrix n n ℂ)‖ ^ 2 = card n := by
    rw [← ofReal_inj, ← trace_star_mul_self_eq_norm_sq, maxCompactU_conjTranspose_mul_self,
      trace_one, ofReal_natCast]
  have h_diff (i j : n) : |(-paramAddRho l) i - (-paramAddRho l) j| ≤
      |l.lowestKType i - l.lowestKType j| + 2 * card n := by
    simp only [Pi.neg_apply, lowestKType]
    grind [abs_eq_max_neg, abs_twoRho_le (ε · = ε ·) i l, abs_twoRho_le (ε · = ε ·) j l]
  calc gapWeightedNormSq (-paramAddRho l) k
      ≤ ∑ i : n, ∑ j : n, (|l.lowestKType i - l.lowestKType j| + 2 * card n : ℤ) *
          ‖(k : Matrix n n ℂ) i j‖ ^ 2 :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_right (mod_cast h_diff i j) (sq_nonneg _)
    _ = gapWeightedNormSq l.lowestKType k + 2 * card n * ‖(k : Matrix n n ℂ)‖ ^ 2 := by
        simp [gapWeightedNormSq, frobenius_norm_sq_eq_sum_norm_sq, add_mul, mul_sum,
          sum_add_distrib]
    _ = gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2 := by rw [h_norm, mul_assoc, ← sq]

/-- Let `l = 2λ` be a parameter of gap `h` and let `g` in `USign ε` satisfy
`‖g - 1‖ ≤ δ ≤ 10 ^ (-12)` (Frobenius norm). Put `λ^ρ = paramAddRho l`, `μ = l.lowestKType`,
`Q_w (X) = ∑_{i, j} |w i - w j| |X i j| ^ 2` and `q = Q_{-λ^ρ} (g - 1) / 4`. Then
`l.dsCoeff g = l.flenstedJensen 1 y` for an invertible matrix `y` such that, for all
`k ∈ K = maxCompactU ε`, the product of principal minors `weightMinors (-λ^ρ) (kᴴ y k)` is
`exp (q - tr (μ logOneAdd (g - 1)) - r)` with `|r| ≤ 10 ^ 6 δ (q + Q_μ (k) + n ^ 2)`. -/
lemma exists_weightMinors_neg_paramAddRho_eq_cexp (hl : l.HasGap h) (g : USign ε)
    (hg : ‖(g : Matrix n n ℂ) - 1‖ ≤ δ) (hδ : δ ≤ 1e-12) :
    ∃ y : Matrix n n ℂ, l.dsCoeff g = l.flenstedJensen 1 y ∧ y.det ≠ 0 ∧
      ∀ k : maxCompactU ε, ∃ r : ℂ,
        weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * y * k) =
          cexp ((gapWeightedNormSq (-paramAddRho l) ((g : Matrix n n ℂ) - 1) / 4 : ℝ) -
            (intDiagonal l.lowestKType * logOneAdd ((g : Matrix n n ℂ) - 1)).trace - r) ∧
        ‖r‖ ≤ 10 ^ 6 * δ * (gapWeightedNormSq (-paramAddRho l) ((g : Matrix n n ℂ) - 1) / 4 +
          gapWeightedNormSq l.lowestKType k + card n ^ 2) := by
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg _).trans hg
  have hg_half : ‖(g : Matrix n n ℂ) - 1‖ ≤ 2⁻¹ := by linarith
  obtain ⟨y, h_coeff, h_minor⟩ := exists_principalMinor_eq_exp hl g (by linarith)
  set X : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  set Z : Matrix n n ℂ := logOneAdd X
  set w : n → ℤ := -paramAddRho l
  have hZ_le : ‖Z‖ ≤ 2 * δ := (norm_logOneAdd_le hg_half).trans (by linarith)
  -- The sets `{i | t ≤ w i}` consist of lowest entries of `l`.
  have h_order (t : ℤ) (i j : n) (hi : t ≤ w i) (hj : ¬t ≤ w j) : l i < l j :=
    hl.paramAddRho_lt_iff.1 (neg_lt_neg_iff.1 ((not_le.1 hj).trans_le hi))
  -- For the set of all indices the formula for one minor gives the determinant.
  have h_det (k : maxCompactU ε) :
      ((k : Matrix n n ℂ)ᴴ * y * (k : Matrix n n ℂ)).det = cexp Z.trace := by
    simpa [principalMinor_of_forall, coordProj, lie_def, -det_mul] using (h_minor ⊤ · k)
  have hy : y.det ≠ 0 := fun h_zero ↦
    (h_det 1).trans_ne (exp_ne_zero _) (by simp [h_zero])
  refine ⟨y, h_coeff, hy, fun k ↦ ?_⟩
  -- Multiply the formulas for one minor over the sets `{i | t ≤ w i}`.
  choose r hr_eq hr_le using fun t : ℤ ↦ h_minor (t ≤ w ·) (h_order t) k
  let M : ℤ := ∑ j : n, |w j|
  have h_range : ∀ i : n, -M ≤ w i ∧ w i ≤ M := neg_sum_abs_le_and_le_sum_abs w
  refine ⟨(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace -
    ∑ t ∈ Ioc (-M) M, r t, ?_, ?_⟩
  · have h_sq : (∑ t ∈ Ioc (-M) M, (‖⁅coordProj (t ≤ w ·), X⁆‖ : ℂ) ^ 2 / 4 : ℂ) =
        ((gapWeightedNormSq w X / 4 : ℝ) : ℂ) := by
      rw [← sum_norm_lie_coordProj_sq h_range X]
      push_cast
      rw [sum_div]
    have h_prod : ∏ t ∈ Ioc (-M) M,
        principalMinor ((k : Matrix n n ℂ)ᴴ * y * (k : Matrix n n ℂ)) (t ≤ w ·) =
          cexp ((intDiagonal w * Z).trace + M * Z.trace + (gapWeightedNormSq w X / 4 : ℝ) +
            ∑ t ∈ Ioc (-M) M, r t) := by
      rw [prod_congr rfl fun t _ ↦ hr_eq t, ← exp_sum, sum_add_distrib, sum_add_distrib, h_sq,
        sum_trace_coordProj_mul h_range, Int.cast_neg, neg_mul, sub_neg_eq_add]
    have h_neg : (intDiagonal w * Z).trace = -(intDiagonal (paramAddRho l) * Z).trace := by
      simp [w, trace]
    rw [weightMinors_eq_det_zpow_mul_prod ((h_det k).trans_ne (exp_ne_zero _)) _ _ h_range, h_det,
      h_prod, ← exp_intCast_mul, ← exp_add, Int.cast_neg, h_neg]
    exact congrArg cexp (by ring)
  · have h_sum : ‖∑ t ∈ Ioc (-M) M, r t‖ ≤
        200000 * ‖X‖ * (gapWeightedNormSq w X + gapWeightedNormSq w k) := by
      refine (norm_sum_le_of_le _ fun t _ ↦ hr_le t).trans_eq ?_
      simp only [← mul_sum, sum_add_distrib, sum_norm_lie_coordProj_sq h_range]
    have h_k : gapWeightedNormSq w k ≤ gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2 :=
      gapWeightedNormSq_neg_paramAddRho_le l k
    calc ‖(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace -
          ∑ t ∈ Ioc (-M) M, r t‖
        ≤ ‖(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace‖ +
            ‖∑ t ∈ Ioc (-M) M, r t‖ := norm_sub_le _ _
      _ ≤ card n ^ 2 * (2 * δ) + 200000 * δ *
            (gapWeightedNormSq w X + (gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2)) := by
          grw [norm_trace_paramAddRho_sub_trace_lowestKType_le, hZ_le, h_sum, hg, h_k]
      _ ≤ 10 ^ 6 * δ *
            (gapWeightedNormSq w X / 4 + gapWeightedNormSq l.lowestKType k + card n ^ 2) := by
          nlinarith [gapWeightedNormSq_nonneg l.lowestKType k, sq_nonneg (card n : ℝ),
            gapWeightedNormSq_nonneg w X]

/-- Let `y` be invertible. Flensted-Jensen's integral `l.flenstedJensen g y` at the identity matrix
`g = 1` is the mean over `k ∈ K = maxCompactU ε` of `|weightMinors μ k| ^ 2 / weightMinors
(-paramAddRho l) (kᴴ y k)`, divided by the mean `μ.kTypeNormSq` of `|weightMinors μ k| ^ 2`. Suppose
that the denominator of the integrand is `exp (q - θ - r k)` for all `k ∈ K`, with `q` real and `θ`,
`r k` complex. Then `l.flenstedJensen 1 y / exp θ` differs from `exp (-q)` by the mean over `K` of
`|weightMinors μ k| ^ 2 exp (-q) (exp (r k) - 1)`, divided by `μ.kTypeNormSq`. -/
lemma flenstedJensen_div_exp_sub {y : Matrix n n ℂ} {θ : ℂ} {r : maxCompactU ε → ℂ} (hy : y.det ≠ 0)
    (h_denom : ∀ k : maxCompactU ε,
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * y * k) = cexp (q - θ - r k)) :
    l.flenstedJensen 1 y / cexp θ - Real.exp (-q) =
      (∫ k : maxCompactU ε,
          (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  let F (k : maxCompactU ε) : ℂ :=
    weightMinors l.lowestKType (1 * k) * conj (weightMinors l.lowestKType k) /
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * y * k)
  have h_def : l.flenstedJensen 1 y =
      (∫ k : maxCompactU ε, F k ∂haarK ε) / l.lowestKType.kTypeNormSq := rfl
  have hF : Integrable F (haarK ε) := integrable_of_compactSpace <| by
    fun_prop (disch := simp [h_denom, hy, GeneralLinearGroup.det_ne_zero])
  have h_point (k : maxCompactU ε) :
      (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) =
        F k / cexp θ - (‖weightMinors l.lowestKType k‖ ^ 2 : ℝ) * Real.exp (-q) := by
    simp only [F, h_denom, one_mul, mul_conj', exp_sub, ofReal_mul, ofReal_pow, ofReal_exp,
      ofReal_neg, Complex.exp_neg]
    field_simp
  have h_sq : Integrable (fun k : maxCompactU ε ↦
      ((‖weightMinors l.lowestKType k‖ ^ 2 : ℝ) * Real.exp (-q) : ℂ)) (haarK ε) :=
    integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero]))
  have h_int : ∫ k : maxCompactU ε,
      (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) ∂haarK ε =
        (∫ k : maxCompactU ε, F k ∂haarK ε) / cexp θ -
          l.lowestKType.kTypeNormSq * Real.exp (-q) := by
    simp only [h_point]
    rw [integral_sub (hF.div_const _) h_sq, integral_div, integral_mul_const,
      integral_complex_ofReal]
  rw [h_int, h_def, sub_div,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.2 (kTypeNormSq_pos l.lowestKType).ne'), div_right_comm]

/-- Let `δ T ≤ 10 ^ (-12)`, `T ≥ 1`, `0 ≤ N ≤ T`, `0 ≤ m ≤ exp (-Q / 2)` and
`|r| ≤ 10 ^ 6 δ (q + Q + N)`, with `δ`, `q`, `Q` nonnegative. Then `m exp (-q) |exp r - 1|` is at
most `exp (-q) m / 10 + exp (-5100 T)`: either `r` is small, or `m exp (-q)` is. -/
lemma mul_norm_exp_sub_one_le {m Q N : ℝ} {r : ℂ} (hT : 1 ≤ T) (hδ_nonneg : 0 ≤ δ)
    (hδT : δ * T ≤ 1e-12) (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hN_nonneg : 0 ≤ N) (hN : N ≤ T)
    (hm_nonneg : 0 ≤ m) (hm : m ≤ Real.exp (-(Q / 2))) (hr : ‖r‖ ≤ 10 ^ 6 * δ * (q + Q + N)) :
    m * Real.exp (-q) * ‖cexp r - 1‖ ≤ Real.exp (-q) / 10 * m + Real.exp (-(5100 * T)) := by
  set s : ℝ := q + Q + N with hs
  rcases le_total s (50000 * T) with h_small | h_large
  · have hr_small : ‖r‖ ≤ 1 / 20 := by linarith [mul_le_mul_of_nonneg_left h_small hδ_nonneg]
    calc m * Real.exp (-q) * ‖cexp r - 1‖ ≤ m * Real.exp (-q) * (2 * (1 / 20)) := by
          grw [Complex.norm_exp_sub_one_le (hr_small.trans (by norm_num)), hr_small]
      _ ≤ _ := by linarith [Real.exp_nonneg (-(5100 * T))]
  · have hδ_le : δ ≤ 1e-12 := (le_mul_of_one_le_right hδ_nonneg hT).trans hδT
    have hr_quarter : ‖r‖ ≤ s / 4 := by
      linarith [mul_le_mul_of_nonneg_right hδ_le (show 0 ≤ s by positivity)]
    have h_exp : ‖cexp r - 1‖ ≤ Real.exp ‖r‖ - 1 := by
      simpa using r.norm_exp_sub_sum_le_exp_norm_sub_sum 1
    calc m * Real.exp (-q) * ‖cexp r - 1‖
        ≤ Real.exp (-(Q / 2)) * Real.exp (-q) * Real.exp (s / 4) := by
          grw [hm, h_exp, hr_quarter, sub_one_lt]
      _ ≤ Real.exp (-(5100 * T)) := by
          rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
          linarith
      _ ≤ Real.exp (-q) / 10 * m + Real.exp (-(5100 * T)) := le_add_of_nonneg_left (by positivity)

/-- **Gaussian shape.** Let the parameter `l = 2λ` have gap `500 n ^ 3 + A` and `|l i| ≤ L`, let `T`
be at least `1`, `n ^ 2` and `n ^ 2 log (n + L + 1)`, and let `δ T ≤ 10 ^ (-12)`. For `g` in the
unitary group `USign ε` of the form `diag ε` with `‖g - 1‖ ≤ δ` (Frobenius norm), the discrete
series coefficient `l.dsCoeff g`, divided by the phase `exp (tr μ log g)`, is within
`ϱ / 10 + exp (-100 T)` of a number `ϱ ∈ [0, 1]`; the proof takes a Gaussian in `g - 1` for `ϱ`. -/
lemma exists_norm_dsCoeff_div_cexp_sub_le [Nonempty n] (hl : l.HasLargeGap A)
    (hL : ∀ i : n, |l i| ≤ L)
    {g : USign ε} (hg : ‖(g : Matrix n n ℂ) - 1‖ ≤ δ) (hT : 1 ≤ T) (hT_card : card n ^ 2 ≤ T)
    (hT_log : card n ^ 2 * Real.log (card n + L + 1) ≤ T) (hδT : δ * T ≤ 1e-12) :
    ∃ ϱ ∈ Set.Icc (0 : ℝ) 1,
      ‖l.dsCoeff g / cexp (intDiagonal l.lowestKType * logOneAdd ((g : Matrix n n ℂ) - 1)).trace -
          ϱ‖ ≤ ϱ / 10 + Real.exp (-100 * T) := by
  -- Take `ϱ = exp (-q)` with `q = gapWeightedNormSq (-λ^ρ) (g - 1) / 4`, where
  -- `λ^ρ = paramAddRho l`.
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg _).trans hg
  have hδ_le : δ ≤ 1e-12 := (le_mul_of_one_le_right hδ_nonneg hT).trans hδT
  set Z : Matrix n n ℂ := logOneAdd ((g : Matrix n n ℂ) - 1)
  set q : ℝ := gapWeightedNormSq (-paramAddRho l) ((g : Matrix n n ℂ) - 1) / 4 with hq
  have hq_nonneg : 0 ≤ q := by positivity
  refine ⟨Real.exp (-q), ⟨Real.exp_nonneg _, Real.exp_le_one_iff.2 (by linarith)⟩, ?_⟩
  -- Step 1: a mean over `K`, at a matrix `y` whose products of minors are known.
  obtain ⟨y, h_dsCoeff_eq, hy, h_denom⟩ := exists_weightMinors_neg_paramAddRho_eq_cexp hl g hg hδ_le
  choose r hr_eq hr_le using h_denom
  have h_mean : l.dsCoeff g / cexp (intDiagonal l.lowestKType * Z).trace - Real.exp (-q) =
      (∫ k : maxCompactU ε,
          (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
    rw [h_dsCoeff_eq, flenstedJensen_div_exp_sub hy hr_eq]
  -- Step 2: the integrand is small where `r k` is not.
  have h_point (k : maxCompactU ε) :
      ‖(‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1)‖ ≤
        Real.exp (-q) / 10 * ‖weightMinors l.lowestKType k‖ ^ 2 + Real.exp (-(5100 * T)) := by
    rw [norm_mul, Complex.norm_of_nonneg (by positivity)]
    exact mul_norm_exp_sub_one_le hT hδ_nonneg hδT hq_nonneg (gapWeightedNormSq_nonneg _ _)
      (sq_nonneg _) hT_card (sq_nonneg _) (norm_weightMinors_sq_le_exp l.lowestKType k)
      (hr_le k)
  -- Integrate this bound, and use the lower bound for `l.lowestKType.kTypeNormSq`.
  have h_sq : Integrable (fun k : maxCompactU ε ↦
      Real.exp (-q) / 10 * ‖weightMinors l.lowestKType k‖ ^ 2) (haarK ε) :=
    integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero]))
  have h_pos : 0 < l.lowestKType.kTypeNormSq := kTypeNormSq_pos l.lowestKType
  rw [h_mean, norm_div, Complex.norm_of_nonneg h_pos.le, div_le_iff₀ h_pos]
  calc _ ≤ ∫ k : maxCompactU ε, Real.exp (-q) / 10 * ‖weightMinors l.lowestKType k‖ ^ 2 +
          Real.exp (-(5100 * T)) ∂haarK ε :=
        norm_integral_le_of_norm_le (h_sq.fun_add (integrable_const _)) (.of_forall h_point)
    _ = Real.exp (-q) / 10 * l.lowestKType.kTypeNormSq +
          Real.exp (-100 * T) * Real.exp (-(5000 * T)) := by
        rw [← Real.exp_add, show -100 * T + -(5000 * T) = -(5100 * T) by ring]
        simp [integral_add h_sq (integrable_const _), integral_const_mul]
    _ ≤ (Real.exp (-q) / 10 + Real.exp (-100 * T)) * l.lowestKType.kTypeNormSq := by
        grw [exp_neg_le_kTypeNormSq hl hL hT hT_card hT_log, add_mul]

end New.DiscreteSeries
end
end

section
/-!
# Localizing products of discrete series coefficients near the compact subgroups

This file treats a group `S` with a map `j : S →* U(ε) × U(η)` that satisfies
`New.DiscreteSeries.IsLaplaceDatum`. It proves facts about `New.HCParam.laplaceIntegrand`, the
product of the first discrete series coefficient, the conjugate of the second and `exp (-φ)`. It
shows that a coefficient with a large gap decays away from the maximal compact subgroup. It also
shows that, if `1 ≤ B` and both noncompact parts at `s` are small, the integrand takes the same
value at some `t` for which both components of `j t` are near `1`.

## Main definitions and results

* `New.DiscreteSeries.noncompactPart ε g`: the noncompact part `g - blockDiagPart ε g` of a
  matrix `g`.
* A coefficient with a large gap is small where the noncompact part of its argument is large
  (`New.DiscreteSeries.norm_dsCoeff_pow_four_le`).
* If `1 ≤ B` and both noncompact parts at `s` are small, then `laplaceIntegrand` takes the same
  value at some `t` for which both components of `j t` are near `1`
  (`New.DiscreteSeries.IsLaplaceDatum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le`).

Notions from other files:
* `New.USign ε`: the unitary group `U(ε)` of the diagonal matrix `signMatrix ε` of the signs `ε`.
* `New.blockDiagPart ε g`: the compact part of `g`, which keeps the entries `g i j` with
  `ε i = ε j`.
* `New.HCParam.lowestKType l`, `New.HCParam.dsCoeff l`: the highest weight of the lowest `K`-type
  of the parameter `l`, and the matrix coefficient of that `K`-type.
* `New.DiscreteSeries.IsLaplaceDatum`: the properties of `j` and `φ` that Laplace's method uses.
* `New.HCParam.laplaceIntegrand`: the function to which Laplace's method applies.

## Relation to the literature

This file uses the discrete series coefficient that is known as Flensted-Jensen's function, the
coefficient of the lowest `K`-type of a discrete series
(defined in `Lib.DiscreteSeries.FlenstedJensen.Defs`).
-/

@[expose] public section

noncomputable section

section Localization

open Finset Matrix Complex ComplexConjugate Set ComplexOrder Int New.HCParam

namespace New.DiscreteSeries

open Norms.Frobenius

variable {n m X S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  [DecidableEq X] [Group S] {ε : n → ℤˣ} {l : HCParam ε} {η : m → ℤˣ} {k : HCParam η}
  {j : S →* USign ε × USign η} {τ : X → m} {B : ℝ} {M : ℕ}

/-! ### The relation `g ε gᴴ = ε` row by row -/

variable (ε) in
/-- The noncompact part `A - blockDiagPart ε A` of a matrix `A` for the signs `ε`: it keeps the
entries `A i j` with `ε i ≠ ε j` and puts zero elsewhere. -/
def noncompactPart (A : Matrix n n ℂ) : Matrix n n ℂ := A - blockDiagPart ε A

/-- Let `ε : n → ℤˣ` be a vector of signs and let `g` be in `U(ε) = USign ε`, the unitary group of
the diagonal matrix of `ε`. The entry `(i, i)` of the relation `g ε gᴴ = ε` reads
`2 re (x i i) = 2 ∑ j, ‖y i j‖² - ∑ j, ‖x i j‖²`, where `x = g - 1` and `y = noncompactPart ε g`
keeps the entries `g i j` with `ε i ≠ ε j` and is zero elsewhere. -/
lemma two_mul_re_sub_one_apply (g : USign ε) (i : n) :
    2 * (((g : Matrix n n ℂ) - 1) i i).re =
      2 * ∑ j : n, ‖noncompactPart ε g i j‖ ^ 2 - ∑ j : n, ‖((g : Matrix n n ℂ) - 1) i j‖ ^ 2 := by
  have h_form : (g : Matrix n n ℂ) * (signMatrix ε * (g : Matrix n n ℂ)ᴴ * signMatrix ε) = 1 := by
    rw [← U.inv_coe_eq_mul_conjTranspose_mul, mul_nonsing_inv _ g.val.det_ne_zero.isUnit]
  generalize (g : Matrix n n ℂ) = A at h_form ⊢
  have h_signed : ∑ j : n, (‖A i j‖ ^ 2 - 2 * ‖noncompactPart ε A i j‖ ^ 2) = 1 := by
    have h_entry : (A * (signMatrix ε * Aᴴ * signMatrix ε)) i i = 1 := by simp [h_form]
    rw [← ofReal_inj, ofReal_one, ← h_entry, Matrix.mul_apply, ofReal_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rcases units_eq_one_or (ε i) with hi | hi <;> rcases units_eq_one_or (ε j) with hj | hj <;>
      simp [signMatrix, noncompactPart, blockDiagPart, hi, hj, mul_conj', two_mul]
  have h_shift (j : n) :
      ‖(A - 1) i j‖ ^ 2 = ‖A i j‖ ^ 2 + if i = j then 1 - 2 * (A i i).re else 0 := by
    rcases eq_or_ne i j with rfl | hij
    · simp [Complex.sq_norm, normSq_apply]
      ring
    · simp [hij]
  simp only [sum_sub_distrib, ← mul_sum] at h_signed
  rw [sum_congr rfl fun j _ ↦ h_shift j]
  simp [sum_add_distrib]
  linarith

/-- Let `g` be in `U(ε) = USign ε`, the unitary group of the diagonal matrix of the signs
`ε : n → ℤˣ`. Let `v`, `w` be integer vectors with `a (v i)² ≤ w i` for all `i` and `w i ≤ C` at
each index whose sign differs from that of some other index. Then, in Frobenius norms,
`a ‖v (g - 1)‖² + 2 re tr (w (g - 1)) ≤ 2 C ‖y‖²`. Here `v` and `w` act as the diagonal matrices
`intDiagonal v` and `intDiagonal w`, and `y = noncompactPart ε g` keeps the entries `g i j` with
`ε i ≠ ε j` and is zero elsewhere. -/
lemma norm_sq_add_re_trace_le (g : USign ε) (a C : ℝ) (v w : n → ℤ)
    (h_lower : ∀ i : n, a * v i ^ 2 ≤ w i) (h_upper : ∀ i j : n, ε i ≠ ε j → w i ≤ C) :
    a * ‖intDiagonal v * ((g : Matrix n n ℂ) - 1)‖ ^ 2 +
        2 * (intDiagonal w * ((g : Matrix n n ℂ) - 1)).trace.re ≤
      2 * C * ‖noncompactPart ε g‖ ^ 2 := by
  -- Multiply the relation `two_mul_re_sub_one_apply` in the row `i` by `w i` and sum over `i`.
  set x : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  set y : Matrix n n ℂ := noncompactPart ε g with hy
  have h_row (i : n) : 2 * (x i i).re = 2 * ∑ j : n, ‖y i j‖ ^ 2 - ∑ j : n, ‖x i j‖ ^ 2 :=
    two_mul_re_sub_one_apply g i
  have h_trace : 2 * (intDiagonal w * x).trace.re =
      ∑ i : n, w i * (2 * ∑ j : n, ‖y i j‖ ^ 2 - ∑ j : n, ‖x i j‖ ^ 2) := by
    simp only [← h_row]
    simp [trace, re_sum, mul_sum, mul_left_comm]
  have h_norm : ‖intDiagonal v * x‖ ^ 2 = ∑ i : n, v i ^ 2 * ∑ j : n, ‖x i j‖ ^ 2 := by
    simp [frobenius_norm_sq_eq_sum_norm_sq, diagonal_mul, mul_pow, sq_abs, mul_sum]
  have h_noncompact (i : n) : w i * ∑ j : n, ‖y i j‖ ^ 2 ≤ C * ∑ j : n, ‖y i j‖ ^ 2 := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun j _ ↦ ?_
    rcases eq_or_ne (ε i) (ε j) with hij | hij
    · simp [hy, noncompactPart, blockDiagPart, hij]
    · exact mul_le_mul_of_nonneg_right (h_upper i j hij) (sq_nonneg _)
  rw [h_trace, h_norm, frobenius_norm_sq_eq_sum_norm_sq, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ ↦ ?_
  have h_weight : a * v i ^ 2 * ∑ j : n, ‖x i j‖ ^ 2 ≤ w i * ∑ j : n, ‖x i j‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (h_lower i) (by positivity)
  linarith [h_noncompact i]

/-- Let `g` be in `U(ε) = USign ε`, the unitary group of the diagonal matrix of the signs
`ε : n → ℤˣ`. Then `‖g - 1‖² = 2 ‖y‖² - 2 re tr (g - 1)` in Frobenius norms, where
`y = noncompactPart ε g` keeps the entries `g i j` with `ε i ≠ ε j` and is zero elsewhere. -/
lemma norm_sub_one_sq (g : USign ε) :
    ‖(g : Matrix n n ℂ) - 1‖ ^ 2 =
      2 * ‖noncompactPart ε g‖ ^ 2 - 2 * ((g : Matrix n n ℂ) - 1).trace.re := by
  set x : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  set y : Matrix n n ℂ := noncompactPart ε g
  have h_row (i : n) : ∑ j : n, ‖x i j‖ ^ 2 = 2 * ∑ j : n, ‖y i j‖ ^ 2 - 2 * (x i i).re := by
    linarith only [two_mul_re_sub_one_apply g i]
  calc ‖x‖ ^ 2 = ∑ i : n, ∑ j : n, ‖x i j‖ ^ 2 := frobenius_norm_sq_eq_sum_norm_sq x
    _ = ∑ i : n, (2 * ∑ j : n, ‖y i j‖ ^ 2 - 2 * (x i i).re) := sum_congr rfl fun i _ ↦ h_row i
    _ = 2 * ‖y‖ ^ 2 - 2 * x.trace.re := by
      simp [frobenius_norm_sq_eq_sum_norm_sq, trace, re_sum, mul_sum, sum_sub_distrib]

lemma norm_signMatrix_mul (A : Matrix n n ℂ) : ‖signMatrix ε * A‖ = ‖A‖ :=
  frobenius_norm_mul_of_unitary (by rw [conjTranspose_signMatrix, signMatrix_mul_self]) A

lemma norm_signMatrix_mul_conjTranspose_mul_signMatrix (A : Matrix n n ℂ) :
    ‖signMatrix ε * Aᴴ * signMatrix ε‖ = ‖A‖ := by
  rw [mul_assoc, norm_signMatrix_mul, ← conjTranspose_signMatrix (ε := ε), ← conjTranspose_mul,
    frobenius_norm_conjTranspose, norm_signMatrix_mul]

/-- For `g` in `U(ε)`, the noncompact parts of `g⁻¹` and of `g` have the same Frobenius norm. -/
lemma norm_noncompactPart_inv (g : USign ε) :
    ‖noncompactPart ε (g⁻¹ : USign ε)‖ = ‖noncompactPart ε g‖ := by
  have h_inv : noncompactPart ε (g⁻¹ : USign ε) =
      signMatrix ε * (noncompactPart ε g)ᴴ * signMatrix ε := by
    rw [U.coe_inv (signMatrix_mul_self ε) g]
    ext i j
    by_cases hij : ε i = ε j <;> simp [signMatrix, noncompactPart, blockDiagPart, hij, Ne.symm]
  rw [h_inv, norm_signMatrix_mul_conjTranspose_mul_signMatrix]

/-! ### The block on `X` -/

/-- A positive semidefinite matrix `z` is at least as close to `1` as `z²`, in Frobenius norm. -/
lemma norm_sub_one_le_norm_mul_self_sub_one {z : Matrix X X ℂ} (hz : z.PosSemidef) :
    ‖z - 1‖ ≤ ‖z * z - 1‖ := by
  -- As `z² - 1 = (z + 1) (z - 1)` and `(z + 1)² - 1 = z² + 2 z ≥ 0`, the difference of the squares
  -- is the trace of a positive semidefinite matrix.
  have h_pos : ((z - 1)ᴴ * (zᴴ * z + (z + z)) * (z - 1)).PosSemidef :=
    ((posSemidef_conjTranspose_mul_self z).add (hz.add hz)).conjTranspose_mul_mul_same _
  have h_diff : (z - 1)ᴴ * (zᴴ * z + (z + z)) * (z - 1) =
      (z * z - 1)ᴴ * (z * z - 1) - (z - 1)ᴴ * (z - 1) := by
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_one, hz.isHermitian.eq]
    noncomm_ring
  have h_trace : (0 : ℂ) ≤ (‖z * z - 1‖ ^ 2 : ℝ) - (‖z - 1‖ ^ 2 : ℝ) := by
    rw [← trace_star_mul_self_eq_norm_sq, ← trace_star_mul_self_eq_norm_sq, ← trace_sub, ← h_diff]
    exact h_pos.trace_nonneg
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (real_le_real.1 (sub_nonneg.1 h_trace))

/-- The indicator function of the coordinates off `X`: under `e : X ⊕ Fin M ≃ n` it is `0` on the
image of `X` and `1` on the image of `Fin M`. -/
def offBlockIndicator (e : X ⊕ Fin M ≃ n) (i : n) : ℤ := (e.symm i).elim 0 1

/-- The block of a matrix with rows and columns in `X`, seen in `n` through `e : X ⊕ Fin M ≃ n`. -/
abbrev onBlock (e : X ⊕ Fin M ≃ n) (A : Matrix n n ℂ) : Matrix X X ℂ :=
  A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)

lemma norm_onBlock_le (e : X ⊕ Fin M ≃ n) (A : Matrix n n ℂ) : ‖onBlock e A‖ ≤ ‖A‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [frobenius_norm_sq_eq_sum_norm_sq, submatrix_apply, Function.comp_apply, ← e.sum_comp,
    Fintype.sum_sum_type, sum_add_distrib, add_assoc, le_add_iff_nonneg_right]
  positivity

/-- The square of the Frobenius norm of `A` is at most the sum of those of its rows off `X`, its
columns off `X` and its block `onBlock e A` on `X`, with `X` seen in `n` through `e`. Multiplication
by `intDiagonal (offBlockIndicator e)` on the left (right) keeps the rows (columns) off `X`. -/
lemma norm_sq_le_rows_add_columns_add_block (e : X ⊕ Fin M ≃ n) (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 ≤
      ‖intDiagonal (offBlockIndicator e) * A‖ ^ 2 + ‖A * intDiagonal (offBlockIndicator e)‖ ^ 2 +
        ‖onBlock e A‖ ^ 2 := by
  -- Only the entries in both a row and a column off `X` are counted twice on the right.
  have h_count :
      ‖intDiagonal (offBlockIndicator e) * A‖ ^ 2 + ‖A * intDiagonal (offBlockIndicator e)‖ ^ 2 +
          ‖onBlock e A‖ ^ 2 =
        ‖A‖ ^ 2 + ∑ a : Fin M, ∑ b : Fin M, ‖A (e (.inr a)) (e (.inr b))‖ ^ 2 := by
    simp [frobenius_norm_sq_eq_sum_norm_sq, ← e.sum_comp, offBlockIndicator, sum_add_distrib]
    ring
  rw [h_count, le_add_iff_nonneg_right]
  positivity

/-- Let `g` be in `U(ε)`, the signs being `+1` on `X`, and let `a = onBlock e g` be the block of `g`
on `X`. Then `‖aᴴ a - 1‖` is at most the square of the norm of the rows of `g - 1` off `X`, which
left multiplication by the diagonal matrix `intDiagonal (offBlockIndicator e)` keeps. -/
lemma norm_onBlock_gram_sub_one_le (e : X ⊕ Fin M ≃ n) (hε : ∀ x : X, ε (e (.inl x)) = 1)
    (g : USign ε) :
    ‖(onBlock e g)ᴴ * onBlock e g - 1‖ ≤
      ‖intDiagonal (offBlockIndicator e) * ((g : Matrix n n ℂ) - 1)‖ ^ 2 := by
  -- The block on `X` of `gᴴ ε g = ε` reads `aᴴ a + onBlock e (Wᴴ ε W) = 1`, where `W` consists of
  -- the rows of `g - 1` off `X`.
  have h_form : (g : Matrix n n ℂ)ᴴ * signMatrix ε * (g : Matrix n n ℂ) = signMatrix ε :=
    mem_unitaryGroupOf_iff.1 g.property
  generalize (g : Matrix n n ℂ) = A at h_form ⊢
  set W : Matrix n n ℂ := intDiagonal (offBlockIndicator e) * (A - 1) with hW
  have hW_on (x : X) (i : n) : W (e (.inl x)) i = 0 := by simp [hW, offBlockIndicator]
  have hW_off (a : Fin M) (x : X) : W (e (.inr a)) (e (.inl x)) = A (e (.inr a)) (e (.inl x)) := by
    simp [hW, offBlockIndicator]
  have h_split : onBlock e (Aᴴ * signMatrix ε * A) =
      (onBlock e A)ᴴ * onBlock e A + onBlock e (Wᴴ * signMatrix ε * W) := by
    ext x y
    simp [Matrix.mul_apply, signMatrix, diagonal_apply, ← e.sum_comp, hε, hW_on, hW_off]
  have h_one : onBlock e (signMatrix ε) = 1 := by
    ext
    simp [signMatrix, hε, Matrix.one_apply, diagonal_apply]
  rw [h_form, h_one] at h_split
  calc ‖(onBlock e A)ᴴ * onBlock e A - 1‖ = ‖onBlock e (Wᴴ * (signMatrix ε * W))‖ := by
        rw [h_split, sub_add_cancel_left, norm_neg, mul_assoc]
    _ ≤ ‖Wᴴ‖ * ‖signMatrix ε * W‖ := (norm_onBlock_le e _).trans (norm_mul_le _ _)
    _ = ‖W‖ ^ 2 := by rw [frobenius_norm_conjTranspose, norm_signMatrix_mul, sq]

/-- If `u` is unitary (`uᴴ * u = 1`) and `f : X ⊕ Y ≃ n` sends `X` to coordinates where `ε` is `1`,
then `u`, extended by `1` on the coordinates from `Y`, is an element `s` of `USign ε`: `s -
1 = inclMatrix ℂ (f ∘ .inl) * (u - 1) * (inclMatrix ℂ (f ∘ .inl))ᴴ`. Here `inclMatrix ℂ (f ∘ .inl)`
is the matrix of the inclusion of `X` in `n`. -/
lemma exists_unitary_sub_one_eq_inclMatrix {u : Matrix X X ℂ} {Y : Type}
    (f : X ⊕ Y ≃ n) (hε : ∀ x : X, ε (f (.inl x)) = 1) (hu : uᴴ * u = 1) :
    ∃ s : USign ε, (s : Matrix n n ℂ) - 1 =
      inclMatrix ℂ (f ∘ .inl) * (u - 1) * (inclMatrix ℂ (f ∘ .inl))ᴴ := by
  set Q : Matrix n X ℂ := inclMatrix ℂ (f ∘ .inl) with hQ
  have hQ_iso : Qᴴ * Q = 1 := by
    ext; simp [hQ, inclMatrix, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have hQ_sgn : signMatrix ε * Q = Q := by
    ext i x
    by_cases hi : i = f (.inl x) <;> simp [hQ, inclMatrix, signMatrix, Matrix.one_apply, hε, hi]
  have hQ_sgn' : Qᴴ * signMatrix ε = Qᴴ := by
    rw [← conjTranspose_signMatrix, ← conjTranspose_mul, hQ_sgn]
  have h_expand : (uᴴ - 1) + (u - 1) + (uᴴ - 1) * (u - 1) = uᴴ * u - 1 := by noncomm_ring
  suffices h_form : (1 + Q * (u - 1) * Qᴴ)ᴴ * signMatrix ε * (1 + Q * (u - 1) * Qᴴ) =
      signMatrix ε from
    ⟨U.of IsHermitianInvolution.isUnit _ h_form, by simp⟩
  calc (1 + Q * (u - 1) * Qᴴ)ᴴ * signMatrix ε * (1 + Q * (u - 1) * Qᴴ)
      = signMatrix ε + Q * (uᴴ - 1) * (Qᴴ * signMatrix ε) + signMatrix ε * Q * (u - 1) * Qᴴ +
          Q * (uᴴ - 1) * (Qᴴ * (signMatrix ε * Q)) * (u - 1) * Qᴴ := by
        simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
    _ = signMatrix ε + Q * ((uᴴ - 1) + (u - 1) + (uᴴ - 1) * (u - 1)) * Qᴴ := by
        simp [hQ_sgn, hQ_sgn', hQ_iso, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
    _ = signMatrix ε := by simp [h_expand, hu]

variable {e : X ⊕ Fin M ≃ n} {φ : S → ℂ}

/-! ### The phases at the logarithms -/

/-- For `‖A‖ ≤ 1 / 2` (Frobenius norm) and `0 ≤ r ≤ 1`, the geometric series of `(1 + r • A)⁻¹` may
be multiplied by `D` and `A` and traced term by term. -/
lemma hasSum_trace_geom {A : Matrix n n ℂ} (hA : ‖A‖ ≤ 2⁻¹) (D : Matrix n n ℂ) {r : ℝ}
    (hr : r ∈ Set.Icc 0 1) :
    HasSum (fun i : ℕ ↦ trace (D * ((-(r • A)) ^ i * A))) (trace (D * ((1 + r • A)⁻¹ * A))) := by
  have h_small : ‖-(r • A)‖ < 1 := by
    simpa using (norm_smul_le_of_le_one r hA hr).trans_lt two_inv_lt_one
  have h_geom : HasSum (fun i : ℕ ↦ D * ((-(r • A)) ^ i * A))
      (D * (Ring.inverse (1 - -(r • A)) * A)) :=
    ((hasSum_geom_series_inverse _ h_small).mul_right A).mul_left D
  simpa [← nonsing_inv_eq_ringInverse] using
    h_geom.mapL (traceLinearMap n ℂ ℂ).toContinuousLinearMap

/-- The difference `l.phase k (Y, Y') = tr (μ Y) - tr (μ' Y')` of the two phases, for the weights
`μ`, `μ'` of the lowest `K`-types of `l` and `k`, is compatible with subtraction of pairs. -/
lemma phase_sub (y z : Matrix n n ℂ × Matrix m m ℂ) :
    l.phase k (y - z) = l.phase k y - l.phase k z := by
  simp [phase, mul_sub, sub_sub_sub_comm]

/-- For a pair of matrices put `l.phase k (Y, Y') = tr (μ Y) - tr (μ' Y')`, where `μ` and `μ'` are
the diagonal matrices of the weights of the lowest `K`-types of the parameters `l` and `k`. Let
`j : S →* U(ε) × U(η)` and `φ : S → ℂ` satisfy `IsLaplaceDatum`, of which two conditions are used:
`φ` is additive, and `l.phase k (g - 1, g' - 1) = φ s` for `(g, g') = j s`. Then
`l.phase k ((g - 1) ^ (i + 1), (g' - 1) ^ (i + 1))` is `φ s` for `i = 0` and `0` for `i > 0`. -/
lemma IsLaplaceDatum.phase_pow_mul (hj : IsLaplaceDatum l k j τ B e φ) (s : S) (i : ℕ) :
    l.phase k (subOnePair j s ^ i * subOnePair j s) = 0 ^ i * φ s := by
  set x : Matrix n n ℂ × Matrix m m ℂ := subOnePair j s with hx
  -- For the induction, insert the factor `j t = 1 + subOnePair j t`; then put `t = 1`.
  suffices h_powers : ∀ t : S, l.phase k (x ^ i * x * (1 + subOnePair j t)) = 0 ^ i * φ s by
    rw [← h_powers 1, show subOnePair j 1 = 0 by simp, add_zero, mul_one]
  have h_step (t : S) : x * (1 + subOnePair j t) = subOnePair j (s * t) - subOnePair j t := by
    ext1 <;> simp [hx, sub_mul]
  intro t
  induction i generalizing t with
  | zero =>
    rw [pow_zero, one_mul, h_step, phase_sub, hj.phase_eq, hj.phase_eq, hj.phase_mul]
    ring
  | succ i ih =>
    have h_split : x ^ (i + 1) * x * (1 + subOnePair j t) =
        x ^ i * x * (1 + subOnePair j (s * t)) - x ^ i * x * (1 + subOnePair j t) := by
      rw [← mul_sub, add_sub_add_left_eq_sub, ← h_step, pow_succ, mul_assoc]
    rw [h_split, phase_sub, ih, ih]
    ring

/-- Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`. For a pair of matrices
put `l.phase k (Y, Y') = tr (μ Y) - tr (μ' Y')`, where `μ` and `μ'` are the diagonal matrices of the
weights of the lowest `K`-types of `l` and `k`. Let `j : S →* U(ε) × U(η)` and `φ : S → ℂ` satisfy
`IsLaplaceDatum`. In particular the function `φ` is additive, and `l.phase k (g - 1, g' - 1) = φ s`
for `(g, g') = j s`, where `(g - 1, g' - 1) = subOnePair j s`. If `g - 1` and `g' - 1` have
Frobenius norm at most `1 / 2`, then `l.phase k (log g, log g')` is again `φ s`. Here
`log g = logOneAdd (g - 1)`, and `logOneAdd Y` is the logarithm of `1 + Y`. -/
lemma IsLaplaceDatum.phase_logOneAdd (hj : IsLaplaceDatum l k j τ B e φ) (s : S)
    (h_fst : ‖(subOnePair j s).1‖ ≤ 2⁻¹) (h_snd : ‖(subOnePair j s).2‖ ≤ 2⁻¹) :
    l.phase k ((subOnePair j s).map logOneAdd logOneAdd) = φ s := by
  -- In the geometric series of `phase ((1 + r • x)⁻¹ * x)` only the term `phase x = φ s` is left,
  -- by `phase_pow_mul`; integrate over `r`.
  let D := intDiagonal l.lowestKType
  let D' := intDiagonal k.lowestKType
  rw [phase, Prod.map_fst, Prod.map_snd,
    ← integral_trace_mul_inv_one_add_smul_mul h_fst,
    ← integral_trace_mul_inv_one_add_smul_mul h_snd,
    ← intervalIntegral.integral_sub
      (intervalIntegrable_trace_mul_inv_one_add_smul_mul h_fst D)
      (intervalIntegrable_trace_mul_inv_one_add_smul_mul h_snd D')]
  refine (intervalIntegral.integral_congr (g := fun _ ↦ φ s) fun r hr ↦ ?_).trans (by simp)
  rw [Set.uIcc_of_le zero_le_one] at hr
  refine ((hasSum_trace_geom h_fst D hr).sub (hasSum_trace_geom h_snd D' hr)).unique ?_
  convert hasSum_ite_eq (0 : ℕ) (φ s) with i
  trans (-r : ℂ) ^ i * (0 ^ i * φ s)
  · rw [← hj.phase_pow_mul s i]
    simp [D, D', phase, ← neg_smul, smul_pow, mul_sub]
  · cases i <;> simp

/-! ### Left translation by `U(X)` -/

/-- If `x - 1` vanishes in the rows `i` with `w i ≠ 0`, then the principal minor of `x` on
`{i | c ≤ w i}` is `det x` for `c ≤ 0` and `1` for `c > 0`. -/
lemma principalMinor_eq_ite_det {w : n → ℤ} {x : Matrix n n ℂ}
    (hx : ∀ i j : n, w i ≠ 0 → (x - 1) i j = 0) (c : ℤ) :
    principalMinor x (fun i : n ↦ c ≤ w i) = if c ≤ 0 then x.det else 1 := by
  have h_cut : diagonal (fun i : n ↦ if c ≤ w i then 1 else 0) * (x - 1) =
      if c ≤ 0 then x - 1 else 0 := by
    ext i j
    by_cases hi : w i = 0
    · split_ifs with hc <;> simp [diagonal_mul, hi, hc]
    · split_ifs <;> simp [diagonal_mul, hx i j hi]
  rw [principalMinor_eq_det, ← neg_sub x, mul_neg, h_cut, sub_neg_eq_add]
  split_ifs <;> simp

/-- Let `x` be invertible, with `x i j = 0` for `w i ≠ w j` and with `x - 1` vanishing in the rows
`i` with `w i ≠ 0`. Then left multiplication by `x` preserves `weightMinors w`, the coefficient of
a highest vector of weight `w`. -/
lemma weightMinors_mul_eq_of_zero_weight_block {w : n → ℤ} {x : Matrix n n ℂ} (hx_det : x.det ≠ 0)
    (hx_block : ∀ i j : n, w i ≠ w j → x i j = 0) (hx_row : ∀ i j : n, w i ≠ 0 → (x - 1) i j = 0)
    (y : Matrix n n ℂ) : weightMinors w (x * y) = weightMinors w y := by
  refine finprod_congr fun c ↦ ?_
  have h_mul : principalMinor (x * y) (fun i : n ↦ c ≤ w i) =
      principalMinor x (fun i : n ↦ c ≤ w i) * principalMinor y (fun i : n ↦ c ≤ w i) :=
    principalMinor_mul fun i j _ hi hj _ ↦ .inl (hx_block i j (by omega))
  rw [h_mul, principalMinor_eq_ite_det hx_row]
  split_ifs
  · rw [det_mul, mul_div_mul_left _ _ hx_det]
  · rw [one_mul]

omit [Fintype n] [DecidableEq X] in
/-- A matrix `u` on `X`, placed by `inclMatrix` in the rows and columns in the image of `σ`,
vanishes in the other rows and in the other columns. -/
lemma inclMatrix_mul_mul_conjTranspose_apply_eq_zero {σ : X → n} (u : Matrix X X ℂ) {i j : n}
    (hij : i ∉ range σ ∨ j ∉ range σ) : (inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) i j = 0 := by
  simp only [Set.mem_range, not_exists] at hij
  rcases hij with hi | hj
  · simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply, fun x ↦ Ne.symm (hi x)]
  · simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply, hj]

omit [Fintype n] [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`. If a function `f` is constant on the image of `σ`, then `A i j = 0` for `f i ≠ f j`. -/
lemma apply_eq_zero_of_sub_one_eq_inclMatrix {α : Type*} {f : n → α} {c : α} {σ : X → n}
    (hσ : ∀ x : X, f (σ x) = c) {u : Matrix X X ℂ} {A : Matrix n n ℂ}
    (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) {i j : n} (hij : f i ≠ f j) :
    A i j = 0 := by
  have h_outside : i ∉ range σ ∨ j ∉ range σ := by grind
  calc A i j = (A - 1) i j := by simp [show i ≠ j by grind]
    _ = 0 := by rw [hA, inclMatrix_mul_mul_conjTranspose_apply_eq_zero u h_outside]

omit [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`, where the sign is `+1`. Then `A` is block diagonal for the signs `ε`. -/
lemma mem_blockDiagAlg_of_sub_one_eq_inclMatrix {σ : X → n} (hσ_sign : ∀ x : X, ε (σ x) = 1)
    {u : Matrix X X ℂ} {A : Matrix n n ℂ} (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) :
    A ∈ blockDiagAlg ε :=
  mem_blockDiagAlg.2 fun _ _ hij ↦ apply_eq_zero_of_sub_one_eq_inclMatrix hσ_sign hA hij

omit [Fintype n] [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`, where the weight `w` is `0`. Then `A - 1` vanishes in the rows `i` with `w i ≠ 0`. -/
lemma sub_one_apply_eq_zero_of_weight_ne_zero {w : n → ℤ} {σ : X → n}
    (hσ_weight : ∀ x : X, w (σ x) = 0) {u : Matrix X X ℂ} {A : Matrix n n ℂ}
    (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) (i j : n) (hi : w i ≠ 0) :
    (A - 1) i j = 0 := by
  have h_outside : i ∉ range σ := by grind
  rw [hA, inclMatrix_mul_mul_conjTranspose_apply_eq_zero u (.inl h_outside)]

omit [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`, where the weight `w` is `0`. Then the diagonal matrix of `w` kills `A - 1`. -/
lemma intDiagonal_mul_sub_one_eq_zero {w : n → ℤ} {σ : X → n} (hσ_weight : ∀ x : X, w (σ x) = 0)
    {u : Matrix X X ℂ} {A : Matrix n n ℂ} (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) :
    intDiagonal w * (A - 1) = 0 := by
  ext i j
  by_cases hi : w i = 0
  · simp [diagonal_mul, hi]
  · simp [diagonal_mul, sub_one_apply_eq_zero_of_weight_ne_zero hσ_weight hA i j hi]

omit [DecidableEq X] in
/-- Let `g₀ ∈ U(ε)` be such that `g₀ - 1` is a matrix `x` on `X` placed, by `inclMatrix`, in the
rows and columns in the image of `σ : X → n`, where the sign is `+1` and the weight `l.lowestKType`
of the lowest `K`-type of the parameter `l` is `0`. Then left translation by `g₀` preserves the
discrete series coefficient `l.dsCoeff`. -/
lemma dsCoeff_mul_eq_of_sub_one_eq_inclMatrix {σ : X → n} (hσ_sign : ∀ i : X, ε (σ i) = 1)
    (hσ_weight : ∀ i : X, l.lowestKType (σ i) = 0) {x : Matrix X X ℂ} {g₀ : USign ε}
    (hg₀ : (g₀ : Matrix n n ℂ) - 1 = inclMatrix ℂ σ * (x * (inclMatrix ℂ σ)ᴴ)) (g : USign ε) :
    l.dsCoeff (g₀ * g : USign ε) = l.dsCoeff g := by
  -- The matrix `g₀` is block diagonal both for the signs and for the weight.
  have hg₀_det : (g₀ : Matrix n n ℂ).det ≠ 0 := (g₀ : GL n ℂ).det_ne_zero
  have h_minors (y : Matrix n n ℂ) :
      weightMinors l.lowestKType (g₀ * y) = weightMinors l.lowestKType y :=
    weightMinors_mul_eq_of_zero_weight_block hg₀_det
      (fun i j hij ↦ apply_eq_zero_of_sub_one_eq_inclMatrix hσ_weight hg₀ hij)
      (sub_one_apply_eq_zero_of_weight_ne_zero hσ_weight hg₀) y
  have h_compact : blockDiagPart ε ((g₀ : Matrix n n ℂ) * g) = g₀ * blockDiagPart ε g :=
    blockDiagPart_mul_left (mem_blockDiagAlg_of_sub_one_eq_inclMatrix hσ_sign hg₀) _
  have h_quot : (blockDiagPart ε ((g₀ : Matrix n n ℂ) * g))⁻¹ * ((g₀ : Matrix n n ℂ) * g) =
      (blockDiagPart ε g)⁻¹ * g := by
    rw [h_compact, Matrix.mul_inv_rev, mul_assoc, nonsing_inv_mul_cancel_left _ _ hg₀_det.isUnit]
  rw [Subgroup.coe_mul, Units.val_mul, dsCoeff, dsCoeff, h_quot, h_compact]
  simp only [flenstedJensen, mul_assoc (g₀ : Matrix n n ℂ), h_minors]

/-- Left translation by a block diagonal element `g₀` of `U(ε)` preserves the Frobenius norm of the
noncompact part. -/
lemma norm_noncompactPart_mul_of_mem_blockDiagAlg {g₀ : USign ε}
    (hg₀ : (g₀ : Matrix n n ℂ) ∈ blockDiagAlg ε) (g : USign ε) :
    ‖noncompactPart ε (g₀ * g : USign ε)‖ = ‖noncompactPart ε g‖ := by
  have hg₀_unitary : (g₀ : Matrix n n ℂ) ∈ unitaryGroup n ℂ :=
    U_one_mem_unitaryGroup ⟨(g₀ : GL n ℂ), mem_maxCompactU.2 hg₀⟩
  have h_mul : noncompactPart ε (g₀ * g : USign ε) = g₀ * noncompactPart ε g := by
    rw [noncompactPart, noncompactPart, Subgroup.coe_mul, Units.val_mul,
      blockDiagPart_mul_left hg₀, mul_sub]
  rw [h_mul, frobenius_norm_mul_of_unitary (mem_unitaryGroup_iff'.1 hg₀_unitary)]

/-! ### Decay away from the maximal compact subgroup -/

/-- For nonnegative reals `μ i`, one has `1 + ∑ μ i ≤ ∏ (1 + μ i)`. -/
lemma one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ i : ι, 0 ≤ μ i) :
    1 + ∑ i ∈ s, μ i ≤ ∏ i ∈ s, (1 + μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    nlinarith [hμ a, s.sum_nonneg fun i _ ↦ hμ i]

/-- For a complex square matrix `A` with its Frobenius norm, `1 + ‖A‖² ≤ |det (1 + Aᴴ A)|`. -/
lemma one_add_norm_sq_le_norm_det_one_add (A : Matrix n n ℂ) :
    1 + ‖A‖ ^ 2 ≤ ‖(1 + Aᴴ * A).det‖ := by
  -- In terms of the eigenvalues `μ i ≥ 0` of `Aᴴ * A` this is `1 + ∑ μ i ≤ ∏ (1 + μ i)`.
  have hA := A.posSemidef_conjTranspose_mul_self
  convert one_add_sum_le_prod_one_add Finset.univ hA.eigenvalues_nonneg using 2
  · rw [← ofReal_inj, ← trace_star_mul_self_eq_norm_sq, hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  · rw [show ‖(1 + Aᴴ * A).det‖ = ‖(Aᴴ * A).charpoly.eval (-1)‖ from by
      rw [eval_charpoly, map_neg, map_one, ← neg_add', det_neg]
      simp, hA.isHermitian.charpoly_eq, Polynomial.eval_prod, norm_prod]
    exact prod_congr rfl fun i _ ↦ by
      simpa [← neg_add', ← ofReal_one, ← ofReal_add] using
        Complex.norm_of_nonneg (add_nonneg zero_le_one (hA.eigenvalues_nonneg i))

/-- The part of `gᴴ ε g = ε` that commutes with `ε` reads `aᴴ a = 1 + yᴴ y`, for the compact part
`a = blockDiagPart ε g` and the noncompact part `y = noncompactPart ε g`. -/
lemma conjTranspose_blockDiagPart_mul_blockDiagPart (g : USign ε) :
    (blockDiagPart ε g)ᴴ * blockDiagPart ε g =
      1 + (noncompactPart ε g)ᴴ * noncompactPart ε g := by
  -- With `g' = ε g ε` one has `a = (g + g') / 2`, `y = (g - g') / 2` and `gᴴ g' = g'ᴴ g = 1`.
  set g' : Matrix n n ℂ := signMatrix ε * g * signMatrix ε with hg'
  have h_right : (g : Matrix n n ℂ)ᴴ * g' = 1 := by
    rw [hg', ← mul_assoc, ← mul_assoc, ← star_eq_conjTranspose, mem_unitaryGroupOf_iff.1 g.property,
      signMatrix_mul_self]
  have h_left : g'ᴴ * (g : Matrix n n ℂ) = 1 := by simpa using congrArg conjTranspose h_right
  simp only [noncompactPart, blockDiagPart_eq, ← hg', conjTranspose_sub, conjTranspose_smul,
    conjTranspose_add, star_inv₀, star_ofNat, mul_add, add_mul, mul_sub, sub_mul, smul_add,
    smul_mul_assoc, mul_smul_comm, h_left, h_right]
  module

/-- Let the doubled Harish-Chandra parameter `l : HCParam ε` satisfy `l.HasLargeGap h`, i.e. have
gap `c = 500 (card n)³ + h`: its entries are distinct, have the parity of `card n - 1`, and differ
by at least `2 c` where the signs `ε` differ. Then for `g` in `USign ε`, the unitary group of
`diag ε`, `‖l.dsCoeff g‖ ^ 4` is at most `(1 + ‖y‖²)⁻¹ ^ h`, where the noncompact part
`y = noncompactPart ε g` keeps the entries `g i j` with `ε i ≠ ε j` and is zero elsewhere. -/
lemma norm_dsCoeff_pow_four_le {h : ℕ} [hg : l.HasLargeGap h] (g : USign ε) :
    ‖l.dsCoeff g‖ ^ 4 ≤ (1 + ‖noncompactPart ε g‖ ^ 2)⁻¹ ^ h := by
  set y : Matrix n n ℂ := noncompactPart ε g with hy
  have h_det : 1 + ‖y‖ ^ 2 ≤ ‖(blockDiagPart ε g).det‖ ^ 2 := by
    calc 1 + ‖y‖ ^ 2 ≤ ‖(1 + yᴴ * y).det‖ := one_add_norm_sq_le_norm_det_one_add y
      _ = ‖(blockDiagPart ε g).det‖ ^ 2 := by
          rw [hy, ← conjTranspose_blockDiagPart_mul_blockDiagPart, det_mul, det_conjTranspose,
            norm_mul, norm_star, sq]
  have h_coeff : ‖l.dsCoeff g‖ ^ 2 ≤ 1 / ‖(blockDiagPart ε g).det‖ ^ h :=
    (le_div_iff₀ (by simp)).2 (norm_dsCoeff_sq_mul_det_pow_le_one hg le_add_self g)
  calc ‖l.dsCoeff g‖ ^ 4 = (‖l.dsCoeff g‖ ^ 2) ^ 2 := by ring
    _ ≤ (1 / ‖(blockDiagPart ε g).det‖ ^ h) ^ 2 := by gcongr
    _ = (‖(blockDiagPart ε g).det‖ ^ 2)⁻¹ ^ h := by simp [sq, mul_pow]
    _ ≤ (1 + ‖y‖ ^ 2)⁻¹ ^ h := by gcongr

/-- Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`, and let
`j : S →* U(ε) × U(η)` (`U(ε) = USign ε`) satisfy `IsLaplaceDatum` for the splitting
`e : X ⊕ Fin M ≃ n` and the map `τ : X → m`. Then the weights `μ`, `μ'` of the lowest `K`-types of
`l` and `k` are `0` on the images of `X` under `e` and `τ`. Elsewhere `μ` is in `[-3 B, -B]`. `μ'`
is nonnegative, and at most `3 B` if `η` takes both signs. For `(g, g') = j s` the number
`φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))` is imaginary. Assume `1 ≤ B`. The rows of
`g - 1 = (subOnePair j s).1` off `X` have squared norm at most `6 (‖y‖² + ‖y'‖²)`. Here
`y = noncompactPart ε g` and `y' = noncompactPart η g'` keep the entries at indices of opposite
signs. -/
lemma IsLaplaceDatum.norm_intDiagonal_mul_subOnePair_sq_le (hj : IsLaplaceDatum l k j τ B e φ)
    (hB : 1 ≤ B) (s : S) :
    ‖intDiagonal (offBlockIndicator e) * (subOnePair j s).1‖ ^ 2 ≤
      6 * (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) := by
  -- Sum the row relations of `g` with the weights `-l.lowestKType`, those of `g'` with the weights
  -- `k.lowestKType`, and add: the real parts of the traces cancel.
  have h_fst := norm_sq_add_re_trace_le (j s).1 B (3 * B) (offBlockIndicator e) (-l.lowestKType)
    (fun i ↦ by
      obtain ⟨x | a, rfl⟩ := e.surjective i
      · simp [offBlockIndicator, hj.weight_eq_zero]
      · simpa [offBlockIndicator, le_neg] using (hj.weight_mem a).2)
    (fun i _ _ ↦ by
      obtain ⟨x | a, rfl⟩ := e.surjective i
      · simpa [hj.weight_eq_zero] using zero_le_one.trans hB
      · simpa [neg_le] using (hj.weight_mem a).1)
  have h_snd := norm_sq_add_re_trace_le (j s).2 0 (3 * B) 0 k.lowestKType
    (fun i ↦ by simpa using (hj.weight_nonneg_and_le i i).1)
    fun i i' ↦ (hj.weight_nonneg_and_le i i').2
  simp [← diagonal_neg] at h_fst h_snd
  -- The two weighted traces differ by `φ s`, which is imaginary.
  have h_traces := hj.re_phase_eq_zero s
  rw [← hj.phase_eq s, phase, sub_re] at h_traces
  exact le_of_mul_le_mul_left (by linarith) (zero_lt_one.trans_le hB)

/-- In the setting of `IsLaplaceDatum.norm_intDiagonal_mul_subOnePair_sq_le`, let `(g, g') = j s`.
The columns of `g - 1 = (subOnePair j s).1` off `X` have squared norm at most `6 (‖y‖² + ‖y'‖²)`,
for the noncompact parts `y = noncompactPart ε g` and `y' = noncompactPart η g'`. -/
lemma IsLaplaceDatum.norm_subOnePair_mul_intDiagonal_sq_le (hj : IsLaplaceDatum l k j τ B e φ)
    (hB : 1 ≤ B) (s : S) :
    ‖(subOnePair j s).1 * intDiagonal (offBlockIndicator e)‖ ^ 2 ≤
      6 * (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) := by
  -- Apply the bound for the rows to `g⁻¹ = ε gᴴ ε`.
  have h_inv : intDiagonal (offBlockIndicator e) * (subOnePair j s⁻¹).1 =
      signMatrix ε * ((subOnePair j s).1 * intDiagonal (offBlockIndicator e))ᴴ * signMatrix ε := by
    simp only [map_inv, Prod.fst_inv, U.coe_inv (signMatrix_mul_self ε) (j s).1]
    ext a b
    rcases eq_or_ne a b with rfl | hab
    · rcases units_eq_one_or (ε a) with ha | ha <;> simp [signMatrix, ha]
    · simp [signMatrix, hab, mul_comm, mul_left_comm]
  calc ‖(subOnePair j s).1 * intDiagonal (offBlockIndicator e)‖ ^ 2
      = ‖intDiagonal (offBlockIndicator e) * (subOnePair j s⁻¹).1‖ ^ 2 := by
        rw [h_inv, norm_signMatrix_mul_conjTranspose_mul_signMatrix]
    _ ≤ 6 * (‖noncompactPart ε (j s⁻¹).1‖ ^ 2 + ‖noncompactPart η (j s⁻¹).2‖ ^ 2) :=
        hj.norm_intDiagonal_mul_subOnePair_sq_le hB s⁻¹
    _ = 6 * (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) := by
        rw [map_inv, Prod.fst_inv, Prod.snd_inv, norm_noncompactPart_inv,
          norm_noncompactPart_inv]

/-- Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`, and let
`j : S →* U(ε) × U(η)` satisfy `IsLaplaceDatum`. Its image then contains `U(X)`, placed by
`e : X ⊕ Fin M ≃ n` in the first factor and by `τ : X → m` in the second, on indices where the sign
is `+1` and the weight of the lowest `K`-type is `0`; the bounds on the weights in terms of `B` are
not used. Let `u ∈ U(X)`. For each `s` there is `t` such that the block `onBlock e` on `X` of the
first component of `j t` is `u` times that of `j s`, while `laplaceIntegrand` and the norms of both
noncompact parts agree at `s` and `t`. -/
lemma IsLaplaceDatum.exists_laplaceIntegrand_eq_and_onBlock_eq (hj : IsLaplaceDatum l k j τ B e φ)
    {u : Matrix X X ℂ} (hu : u ∈ unitaryGroup X ℂ) (s : S) :
    ∃ t : S, l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
      onBlock e (j t).1 = u * onBlock e (j s).1 ∧
      ‖noncompactPart ε (j t).1‖ = ‖noncompactPart ε (j s).1‖ ∧
      ‖noncompactPart η (j t).2‖ = ‖noncompactPart η (j s).2‖ := by
  -- Take `t = s₀ s`, where `j s₀` is the diagonal copy of `u`.
  obtain ⟨s₀, hs₀⟩ := hj.exists_diagonal u hu
  obtain ⟨hs₀_fst, hs₀_snd⟩ :
      ((j s₀).1 : Matrix n n ℂ) - 1 =
          inclMatrix ℂ (e ∘ .inl) * ((u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ) ∧
        ((j s₀).2 : Matrix m m ℂ) - 1 = inclMatrix ℂ τ * ((u - 1) * (inclMatrix ℂ τ)ᴴ) := by
    simpa [Matrix.mul_assoc] using hs₀
  have hτ_sign (x : X) : η (τ x) = 1 := (hj.sign_weight_right x).1
  have hτ_weight (x : X) : k.lowestKType (τ x) = 0 := (hj.sign_weight_right x).2
  have h_phase : φ s₀ = 0 := by
    simp [← hj.phase_eq, phase, intDiagonal_mul_sub_one_eq_zero hj.weight_eq_zero hs₀_fst,
      intDiagonal_mul_sub_one_eq_zero hτ_weight hs₀_snd]
  have h_coeff_fst : l.dsCoeff (j (s₀ * s)).1 = l.dsCoeff (j s).1 := by
    rw [map_mul]
    exact dsCoeff_mul_eq_of_sub_one_eq_inclMatrix hj.sign_inl hj.weight_eq_zero hs₀_fst _
  have h_coeff_snd : k.dsCoeff (j (s₀ * s)).2 = k.dsCoeff (j s).2 := by
    rw [map_mul]
    exact dsCoeff_mul_eq_of_sub_one_eq_inclMatrix hτ_sign hτ_weight hs₀_snd _
  refine ⟨s₀ * s, ?_, ?_, ?_, ?_⟩
  · rw [laplaceIntegrand, laplaceIntegrand, h_coeff_fst, h_coeff_snd, hj.phase_mul, h_phase,
      zero_add]
  · rw [map_mul, Prod.fst_mul, Subgroup.coe_mul, Units.val_mul, eq_add_of_sub_eq hs₀_fst]
    ext x y
    simp [inclMatrix, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.one_apply, sub_mul]
  · rw [map_mul]
    exact norm_noncompactPart_mul_of_mem_blockDiagAlg
      (mem_blockDiagAlg_of_sub_one_eq_inclMatrix hj.sign_inl hs₀_fst) _
  · rw [map_mul]
    exact norm_noncompactPart_mul_of_mem_blockDiagAlg
      (mem_blockDiagAlg_of_sub_one_eq_inclMatrix hτ_sign hs₀_snd) _

/-- Let `j` satisfy `IsLaplaceDatum`, of which only `tr (g - 1) = tr (g' - 1)` is used. For
`(g, g') = j s` with noncompact parts `y = noncompactPart ε g` and `y' = noncompactPart η g'`, one
has `‖g' - 1‖² = ‖g - 1‖² - 2 ‖y‖² + 2 ‖y'‖²`. -/
lemma IsLaplaceDatum.norm_snd_sq (hj : IsLaplaceDatum l k j τ B e φ) (s : S) :
    ‖(subOnePair j s).2‖ ^ 2 =
      ‖(subOnePair j s).1‖ ^ 2 - 2 * ‖noncompactPart ε (j s).1‖ ^ 2 +
        2 * ‖noncompactPart η (j s).2‖ ^ 2 := by
  linarith [norm_sub_one_sq (j s).1, norm_sub_one_sq (j s).2,
    congrArg Complex.re (hj.trace_eq s)]

/-- **Localization.** Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`, with
weights `μ`, `μ'` of the lowest `K`-types, and let `j : S →* U(ε) × U(η)` satisfy `IsLaplaceDatum`:
its image contains `U(X)` diagonally on indices of weight `0`; for `(g, g') = j s` the traces of
`g - 1` and `g' - 1` agree and `φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))` is imaginary and additive
in `s`; `μ` lies in `[-3 B, -B]` off `X` and `μ'` is nonnegative and, if `η` takes both signs, at
most `3 B`. Let `1 ≤ B`, so that `μ` is negative off `X`, and `0 < r ≤ 1 / 6`. If the noncompact
parts `y`, `y'` of the components of `j s` have `‖y‖² + ‖y'‖² ≤ r²`, then `laplaceIntegrand` has the
same value at `s` and at some `t` such that both components of `subOnePair j t = j t - 1` have
Frobenius norm at most `4 r`. -/
lemma IsLaplaceDatum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le
    (hj : IsLaplaceDatum l k j τ B e φ) (r : ℝ) (hB : 1 ≤ B)
    (hr_pos : 0 < r) (hr_small : r ≤ 6⁻¹) (s : S)
    (hs : ‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2 ≤ r ^ 2) :
    ∃ t : S, l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
      ‖(subOnePair j t).1‖ ≤ 4 * r ∧
      ‖(subOnePair j t).2‖ ≤ 4 * r := by
  -- The block `a` of `(j s).1` on `X` is almost unitary, hence invertible as `r ≤ 1 / 6`. After
  -- translation by the inverse of its unitary part, the block on `X` is near `1`; the translation
  -- keeps the norms of the noncompact parts, so the rows and columns off `X` are still near those
  -- of `1`. The equality of the traces then bounds the second component.
  set a : Matrix X X ℂ := onBlock e (j s).1
  have h_gram : ‖aᴴ * a - 1‖ ≤ 6 * r ^ 2 :=
    calc ‖aᴴ * a - 1‖ ≤ ‖intDiagonal (offBlockIndicator e) * (subOnePair j s).1‖ ^ 2 :=
          norm_onBlock_gram_sub_one_le e hj.sign_inl (j s).1
      _ ≤ 6 * r ^ 2 := by linarith [hj.norm_intDiagonal_mul_subOnePair_sq_le hB s]
  have h_six : 6 * r ^ 2 ≤ r := by nlinarith
  have ha_unit : IsUnit a := by
    have h_small : ‖1 - aᴴ * a‖ < 1 := by linarith [norm_sub_rev (1 : Matrix X X ℂ) (aᴴ * a)]
    have h_unit : IsUnit (aᴴ * a) := by simpa using isUnit_one_sub_of_norm_lt_one h_small
    exact isUnit_of_mul_isUnit_right h_unit
  -- Write `a = k₁ * z₁` with `k₁` unitary and `z₁` positive semidefinite.
  obtain ⟨k₁, hk₁, z₁, hz₁, h_polar⟩ := exists_unitary_mul_posSemidef ha_unit
  have hk₁_inv : k₁ᴴ * k₁ = 1 := mem_unitaryGroup_iff'.1 hk₁
  have hz₁_near : ‖z₁ - 1‖ ≤ r := by
    have h_sq : aᴴ * a = z₁ * z₁ := by
      rw [h_polar, conjTranspose_mul, hz₁.isHermitian.eq, mul_assoc, ← mul_assoc k₁ᴴ, hk₁_inv,
        one_mul]
    rw [h_sq] at h_gram
    linarith [norm_sub_one_le_norm_mul_self_sub_one hz₁]
  obtain ⟨t, h_value, h_block, hy, hy'⟩ :
      ∃ t : S, l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
        onBlock e (j t).1 = star k₁ * a ∧
        ‖noncompactPart ε (j t).1‖ = ‖noncompactPart ε (j s).1‖ ∧
        ‖noncompactPart η (j t).2‖ = ‖noncompactPart η (j s).2‖ :=
    hj.exists_laplaceIntegrand_eq_and_onBlock_eq (Unitary.star_mem hk₁) s
  have h_on : onBlock e (subOnePair j t).1 = z₁ - 1 := by
    calc onBlock e (subOnePair j t).1 = onBlock e (j t).1 - 1 := by ext x y; simp [Matrix.one_apply]
      _ = k₁ᴴ * (k₁ * z₁) - 1 := by rw [h_block, ← h_polar, star_eq_conjTranspose]
      _ = z₁ - 1 := by rw [← mul_assoc, hk₁_inv, one_mul]
  rw [← hy, ← hy'] at hs
  -- The rows and the columns off `X` contribute `6 r²` each, the block on `X` contributes `r²`.
  have h_fst : ‖(subOnePair j t).1‖ ^ 2 ≤ 13 * r ^ 2 := by
    have h_block_le : ‖onBlock e (subOnePair j t).1‖ ^ 2 ≤ r ^ 2 := by rw [h_on]; gcongr
    linarith [norm_sq_le_rows_add_columns_add_block e (subOnePair j t).1,
      hj.norm_intDiagonal_mul_subOnePair_sq_le hB t, hj.norm_subOnePair_mul_intDiagonal_sq_le hB t]
  have h_snd : ‖(subOnePair j t).2‖ ^ 2 ≤ 15 * r ^ 2 := by
    linarith [hj.norm_snd_sq t, sq_nonneg ‖noncompactPart ε (j t).1‖]
  have h_root {x : ℝ} (hx : x ^ 2 ≤ 15 * r ^ 2) : x ≤ 4 * r :=
    le_of_sq_le_sq (by linarith [sq_nonneg r]) (by positivity)
  exact ⟨t, h_value, h_root (by linarith [sq_nonneg r]), h_root h_snd⟩

end New.DiscreteSeries

end Localization

end
end
end

/-!
# Lower bounds for periods by Laplace's method

This file proves lower bounds for periods of discrete series coefficients. Let
`j : S →* U(ε) × U(η)` be a homomorphism and write `θ` for the function `laplaceIntegrand` on `S`.
Laplace's method bounds the volume of a large ball by a power of `β` times `‖∫ θ‖`, where `β` bounds
the dimensions and the entries of the parameters.

## Main definitions and results

* The values of `θ` lie in a cone about the positive real axis, up to an exponentially small error
  (`IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add`). With the decay of the coefficients, `θ` is
  integrable and the volume of a large ball is at most a power of `β` times `‖∫ θ‖`
  (`IsLaplaceDatum.laplace_method`). The file `PositionGroup` applies this to the group of a
  stationary position.

Notions from other files:
* `USign ε` is the unitary group `U(ε)` of the diagonal form with signs `ε`, and
  `U.sum (signMatrix_sum ε η)` is the block embedding `(g, g') ↦ g ⊕ g'` of `U(ε) × U(η)`.
* `l.dsCoeff g` is the discrete series coefficient with doubled Harish-Chandra parameter
  `l = 2λ : HCParam ε`, given by Flensted-Jensen's integral and normalised to take the value `1`
  at the identity; `l.lowestKType` is the highest weight of its lowest `K`-type. On the maximal
  compact subgroup it is the coefficient at the highest weight vector of this `K`-type
  (`New.dsCoeff_of_mem_maxCompactU`).
* A parameter `l = 2λ` indexed by `n` has gap `A` if its entries are distinct and congruent to
  `card n - 1` mod 2, and `|λ a - λ b| ≥ A` whenever `ε a ≠ ε b`; `l.HasLargeGap h` says that `l`
  has gap `500 (card n)³ + h`.
* `l.laplaceIntegrand k j φ s` is the coefficient of `l` at the first component of `j s`, times the
  conjugate of the coefficient of `k` at the second, times `exp (-φ s)`.
* `IsLaplaceDatum l k j τ B e φ` collects the hypotheses of Laplace's method. Let `μ`, `μ'` be the
  weights `l.lowestKType`, `k.lowestKType` and let `j s = (g, g')`.
  - The parameter `l` is steep (`IsSteep`) for the splitting `e : X ⊕ Fin M ≃ n`: on `X` the sign is
    `+1` and `μ` is `0`; on the other `M` indices the signs are `+, -, +, …` and `μ` decreases
    strictly in `[-3 B, -B]`.
  - The weight `μ'` is nonnegative, at most `3 B` if `η` takes both signs, and `0` on the image of
    `τ : X → m`, where the sign is `+1`.
  - The phase `φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))` is additive and imaginary, and
    `tr (g - 1) = tr (g' - 1)`.
  - For each unitary `u` indexed by `X` there is an `s` such that `g - 1` and `g' - 1` are `u - 1`
    extended by zero along `e` and along `τ`.

## Relation to the literature

This file is the step of Laplace's method that makes restriction periods explicitly large. Near 1 a
discrete series coefficient of U(p,q) is an explicit phase times a number close to the interval
[0,1], up to a tenth of its size and an exponentially small error, so that the losses at the
archimedean places are at most powers of the weights. The integral formula for coefficients,
non-vanishing of periods and fixed-rank asymptotics for coherent states are known in the literature.
Related work: Nelson–Venkatesh, The orbit method and analysis of automorphic forms, 2021; H. He, On
the Gan–Gross–Prasad conjecture for U(p,q), 2017; B. Sun, Matrix coefficients of cohomologically
induced representations, 2007.
-/

@[expose] public section

section LaplaceMethod

open Matrix Fintype Complex Real MeasureTheory ComplexConjugate New.HCParam

namespace New.DiscreteSeries

/-- Let `a, c, t ∈ [0, 1]`. If `u` is within `a / 10 + t` of `a` and `v` within `c / 10 + t` of `c`,
then `u v` is within `0.21 a c + 4 t` of `a c`. -/
lemma norm_mul_sub_mul_le {a c t : ℝ} {u v : ℂ} (ha : a ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1)
    (ht : t ∈ Set.Icc 0 1) (hu : ‖u - a‖ ≤ a / 10 + t) (hv : ‖v - c‖ ≤ c / 10 + t) :
    ‖u * v - ↑(a * c)‖ ≤ 0.21 * (a * c) + 4 * t := by
  calc ‖u * v - ↑(a * c)‖
      = ‖a * (v - c) + (u - a) * c + (u - a) * (v - c)‖ := by rw [ofReal_mul]; ring_nf
    _ ≤ ‖a * (v - c)‖ + ‖(u - a) * c‖ + ‖(u - a) * (v - c)‖ := norm_add₃_le
    _ ≤ a * (c / 10 + t) + (a / 10 + t) * c + (a / 10 + t) * (c / 10 + t) := by
        simp only [norm_mul, Complex.norm_of_nonneg ha.1, Complex.norm_of_nonneg hc.1]
        gcongr <;> linarith [ha.1, hc.1, ht.1]
    _ ≤ 0.21 * (a * c) + 4 * t := by nlinarith [ha.1, hc.1, ht.1, ha.2, hc.2, ht.2]

/-- A complex number `z` within `0.21 p + 4 t` of a real number `p ≥ 0` lies in the cone
`‖z‖ ≤ 2 re z + 12 t`. -/
lemma norm_le_two_mul_re_add {p t : ℝ} {z : ℂ} (hp : 0 ≤ p) (hz : ‖z - p‖ ≤ 0.21 * p + 4 * t) :
    ‖z‖ ≤ 2 * z.re + 12 * t := by
  have h_norm : ‖z‖ ≤ p + ‖z - p‖ := by
    simpa [abs_of_nonneg hp] using norm_le_insert' z p
  have h_re : -‖z - p‖ ≤ z.re - p := by simpa using neg_le_of_abs_le (abs_re_le_norm (z - p))
  linarith

/-- If `T ≥ 1`, `T ρ = 10⁻¹³` and `h ≥ 10³⁰ T³`, then `(1 + ρ²) ^ (-h) ≤ exp (-100 T) ^ 4`. -/
lemma inv_one_add_sq_pow_le_exp_pow_four {T ρ : ℝ} {h : ℕ} (hT : 1 ≤ T) (hρ : T * ρ = 1e-13)
    (hh : 10 ^ 30 * T ^ 3 ≤ h) : (1 + ρ ^ 2)⁻¹ ^ h ≤ rexp (-100 * T) ^ 4 := by
  -- Take logarithms: `log (1 + ρ²) ≥ 2 ρ² / (ρ² + 2)`, `h ≥ 10³⁰ T³` and `ρ² T² = 10⁻²⁶`.
  have hρ_pos : 0 < ρ := by nlinarith
  have hρ_le : ρ ≤ 100⁻¹ := by nlinarith
  have h_gap : 400 * T ≤ 10 ^ 30 * T ^ 3 * (2 * ρ ^ 2 / (ρ ^ 2 + 2)) := by
    have h_sq : T ^ 2 * ρ ^ 2 = 1e-13 ^ 2 := by rw [← mul_pow, hρ]
    field_simp
    nlinarith
  have h_logs : 400 * T ≤ h * (1 + ρ ^ 2).log :=
    h_gap.trans (mul_le_mul hh (le_log_one_add_of_nonneg (sq_nonneg ρ)) (by positivity)
      (Nat.cast_nonneg h))
  rw [← log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_inv,
    Real.log_exp, Nat.cast_ofNat]
  linarith

/-- Let `β ≥ 16`, `N ≥ 1` and `V, I ≥ 0`; in the application `V` and `W` are the volumes of a large
and a small ball and `I` is the norm of an integral. If `V ≤ β ^ (16 N) W` and
`W / 4 ≤ 2 I + 6 β ^ (-50 N) 16 ^ (9 N) V`, then `V ≤ β ^ (20 N) I`, as the error term contributes
at most `V / 2`. -/
lemma le_pow_mul_of_le {β : ℝ} {N : ℕ} {V W I : ℝ} (hβ : 16 ≤ β) (hN : 1 ≤ N) (hV : 0 ≤ V)
    (hI : 0 ≤ I) (h_cover : V ≤ β ^ (16 * N) * W)
    (h_int : W / 4 ≤ 2 * I + 6 * β⁻¹ ^ (50 * N) * (16 ^ (9 * N) * V)) :
    V ≤ β ^ (20 * N) * I := by
  have hβ_one : 1 ≤ β := by linarith
  have h_main : 16 * β ^ (16 * N) ≤ β ^ (20 * N) :=
    calc 16 * β ^ (16 * N) ≤ β * β ^ (16 * N) := by gcongr
      _ ≤ β ^ (20 * N) := by
          rw [← pow_succ']
          exact pow_le_pow_right₀ hβ_one (by omega)
  have h_error : 48 * β ^ (16 * N) * 16 ^ (9 * N) ≤ β ^ (50 * N) :=
    calc 48 * β ^ (16 * N) * 16 ^ (9 * N) ≤ β ^ 2 * β ^ (16 * N) * β ^ (9 * N) := by
          gcongr
          nlinarith
      _ ≤ β ^ (50 * N) := by
          rw [← pow_add, ← pow_add]
          exact pow_le_pow_right₀ hβ_one (by omega)
  have h_half : β ^ (16 * N) * (24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N)) ≤ 1 / 2 := by
    rw [inv_pow]
    field_simp
    linarith
  have h_combined : V ≤ 8 * β ^ (16 * N) * I + 1 / 2 * V :=
    calc V ≤ β ^ (16 * N) * (8 * I + 24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N) * V) := by
          refine h_cover.trans ?_
          gcongr
          linarith
      _ = 8 * β ^ (16 * N) * I + β ^ (16 * N) * (24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N)) * V := by ring
      _ ≤ 8 * β ^ (16 * N) * I + 1 / 2 * V := by gcongr
  linarith [mul_le_mul_of_nonneg_right h_main hI]

/-- If `N ≥ 1`, `t ≥ 1` and `h ≥ 10³⁰ (N t)³`, then `h ≥ 18 N`. -/
lemma eighteen_mul_le_of_mul_pow_three_le {N h : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 1 ≤ t)
    (hh : 10 ^ 30 * (N * t) ^ 3 ≤ h) : 18 * N ≤ h := by
  have h_cube : N * t ≤ (N * t) ^ 3 :=
    le_self_pow₀ (one_le_mul_of_one_le_of_one_le (mod_cast hN) ht) three_ne_zero
  exact_mod_cast (by nlinarith : (18 * N : ℝ) ≤ h)

section Modulus

variable {n m X S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  [DecidableEq X] [Group S] {ε : n → ℤˣ} {η : m → ℤˣ} {l : HCParam ε} {k : HCParam η} {τ : X → m}
  {B T ρ : ℝ} {M h : ℕ} {e : X ⊕ Fin M ≃ n} {j : S →* USign ε × USign η} {φ : S → ℂ}

/-- Under `IsLaplaceDatum` the phase `φ` is imaginary, so the factor `exp (-φ s)` of
`laplaceIntegrand` has modulus one, and the modulus at `s` is the product of the moduli of the
discrete series coefficients at the two components of `j s`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand (h_datum : IsLaplaceDatum l k j τ B e φ) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ = ‖l.dsCoeff (j s).1‖ * ‖k.dsCoeff (j s).2‖ := by
  simp [laplaceIntegrand, Complex.norm_exp, h_datum.re_phase_eq_zero]

open Norms.Frobenius in
/-- **Away from the maximal compact subgroup.** Let `j` and `φ` satisfy `IsLaplaceDatum` (so `φ` is
imaginary), let `T ≥ 1` and `T ρ = 10⁻¹³`, and let both doubled parameters `l`, `k` have gap
`500 · (dimension)³ + h` with `h ≥ 10³⁰ T³`. If the noncompact parts `y`, `y'` of the components of
`j s` (the entries that join indices of opposite signs) have `‖y‖² + ‖y'‖² ≥ ρ²` in the Frobenius
norm, then `laplaceIntegrand` has modulus at most `exp (-100 T)` at `s`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_of_far (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hT : 1 ≤ T) (hρ : T * ρ = 1e-13)
    (hh : 10 ^ 30 * T ^ 3 ≤ h) {s : S}
    (h_far : ρ ^ 2 ≤ ‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ rexp (-100 * T) := by
  set y : ℝ := ‖noncompactPart ε (j s).1‖
  set y' : ℝ := ‖noncompactPart η (j s).2‖
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (exp_nonneg _) four_ne_zero).1 ?_
  calc ‖l.laplaceIntegrand k j φ s‖ ^ 4 = ‖l.dsCoeff (j s).1‖ ^ 4 * ‖k.dsCoeff (j s).2‖ ^ 4 := by
        rw [h_datum.norm_laplaceIntegrand, mul_pow]
    _ ≤ (1 + y ^ 2)⁻¹ ^ h * (1 + y' ^ 2)⁻¹ ^ h := by
        gcongr
        exacts [norm_dsCoeff_pow_four_le (hg := hl) _, norm_dsCoeff_pow_four_le (hg := hk) _]
    _ ≤ (1 + ρ ^ 2)⁻¹ ^ h := by
        rw [← mul_pow, ← mul_inv]
        gcongr
        linarith [mul_nonneg (sq_nonneg y) (sq_nonneg y')]
    _ ≤ rexp (-100 * T) ^ 4 := inv_one_add_sq_pow_le_exp_pow_four hT hρ hh

/-- The matrix of the block sum `U.sum (signMatrix_sum ε η) g` of `g.1` in `U(ε)` and `g.2` in
`U(η)` is the block diagonal matrix `fromBlocks g.1 0 0 g.2`. -/
lemma coe_sum_eq_fromBlocks (g : USign ε × USign η) :
    (U.sum (signMatrix_sum ε η) g : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      fromBlocks (g.1 : Matrix n n ℂ) 0 0 (g.2 : Matrix m m ℂ) :=
  rfl

open Norms.L2Operator in
/-- The operator norm of the block sum `g.1 ⊕ g.2` of elements of the unitary groups `U(ε)` and
`U(η)` is the larger of the two norms. -/
lemma norm_coe_sum_eq_max (g : USign ε × USign η) :
    ‖(U.sum (signMatrix_sum ε η) g : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖ =
      max ‖(g.1 : Matrix n n ℂ)‖ ‖(g.2 : Matrix m m ℂ)‖ := by
  rw [coe_sum_eq_fromBlocks, norm_fromBlocks_zero_zero]

open Norms.L2Operator in
/-- The distance to `1`, in the operator norm, of the block sum `g.1 ⊕ g.2` of elements of the
unitary groups `U(ε)` and `U(η)` is the larger of the two distances to `1`. -/
lemma norm_sum_sub_one (g : USign ε × USign η) :
    ‖(U.sum (signMatrix_sum ε η) g : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ =
      max ‖(g.1 : Matrix n n ℂ) - 1‖ ‖(g.2 : Matrix m m ℂ) - 1‖ := by
  rw [← norm_fromBlocks_zero_zero, coe_sum_eq_fromBlocks]
  congr 1
  ext (a | a) (b | b) <;> simp [Matrix.one_apply]

end Modulus

/-- Let `j s = (g, g')` in `U(ε) × U(η)`. If `s ↦ g` is proper and `s ↦ g'` is continuous, then the
block diagonal sum `s ↦ g ⊕ g'` is a proper map to `U(ε ⊕ η)`. -/
lemma isProperMap_sum {n m S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Group S] {ε : n → ℤˣ} {η : m → ℤˣ} {j : S →* USign ε × USign η} [TopologicalSpace S]
    (hj : IsProperMap fun s : S ↦ (j s).1) (hj' : Continuous fun s : S ↦ (j s).2) :
    IsProperMap ((U.sum (signMatrix_sum ε η)).comp j) := by
  have hj_cont : Continuous fun s : S ↦ (j s).1 := hj.continuous
  have h_cont : Continuous ((U.sum (signMatrix_sum ε η)).comp j) := by
    simp only [U.sum, MonoidHom.coe_comp, continuous_U_iff_matrix, Function.comp_apply,
      MonoidHom.codRestrict_apply, MonoidHom.coe_prodMap, Subgroup.coe_subtype, val_blockGL_apply,
      Prod.map_fst, Prod.map_snd]
    fun_prop
  -- Composing with the upper left block gives back the proper map `s ↦ g`.
  let block (x : USign (Sum.elim ε η)) : Matrix n n ℂ :=
    (x : Matrix (n ⊕ m) (n ⊕ m) ℂ).toBlocks₁₁
  have h_comp : IsProperMap (block ∘ (U.sum (signMatrix_sum ε η)).comp j) := by
    change IsProperMap ((fun g : USign ε ↦ (g : Matrix n n ℂ)) ∘ fun s : S ↦ (j s).1)
    exact isClosedEmbedding_U.isProperMap.comp hj
  exact isProperMap_of_comp_of_t2 h_cont (by fun_prop [toBlocks₁₁]) h_comp

open Norms.L2Operator in
/-- Let `j` and `φ`, defined on a group `S`, satisfy `IsLaplaceDatum` (so `φ` is imaginary). Let the
doubled parameters `l`, `k` have gap `500 · (dimension)³ + h` and entries bounded by `L`, with
`card n + card m + L ≤ β`. Suppose `j s = (g, g')` and the block diagonal sum `g ⊕ g'` is within
`(200 β⁵)⁻¹` of `1` in the operator norm. Then `laplaceIntegrand` at `s` has norm at least `1 / 4`,
as each coefficient has norm at least `1 / 2`. -/
lemma IsLaplaceDatum.one_div_four_le_norm_laplaceIntegrand {n m X S : Type} [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X] [DecidableEq X] [Group S] [Nonempty n]
    [Nonempty m] {ε : n → ℤˣ} {η : m → ℤˣ} {l : HCParam ε} {k : HCParam η} {τ : X → m} {B β : ℝ}
    {L M h : ℕ} {e : X ⊕ Fin M ≃ n} {j : S →* USign ε × USign η} {φ : S → ℂ}
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ_le : card n + card m + L ≤ β) {s : S}
    (hs : ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹) :
    1 / 4 ≤ ‖l.laplaceIntegrand k j φ s‖ := by
  have hn_pos : (1 : ℝ) ≤ card n := Nat.one_le_cast.2 Fintype.card_pos
  have hm_pos : (1 : ℝ) ≤ card m := Nat.one_le_cast.2 Fintype.card_pos
  obtain ⟨h_fst, h_snd⟩ : ‖((j s).1 : Matrix n n ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹ ∧
      ‖((j s).2 : Matrix m m ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹ := by
    rwa [norm_sum_sub_one, max_le_iff] at hs
  have hl_half : 2⁻¹ ≤ ‖l.dsCoeff (j s).1‖ := half_le_norm_dsCoeff hl_le (by linarith) h_fst
  have hk_half : 2⁻¹ ≤ ‖k.dsCoeff (j s).2‖ := half_le_norm_dsCoeff hk_le (by linarith) h_snd
  calc (1 / 4 : ℝ) = 2⁻¹ * 2⁻¹ := by norm_num
    _ ≤ ‖l.dsCoeff (j s).1‖ * ‖k.dsCoeff (j s).2‖ := by gcongr
    _ = ‖l.laplaceIntegrand k j φ s‖ := (h_datum.norm_laplaceIntegrand s).symm

variable {n m X S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  [DecidableEq X] [Group S] [Nonempty n] [Nonempty m] {ε : n → ℤˣ} {η : m → ℤˣ} {l : HCParam ε}
  {k : HCParam η} {τ : X → m} {B β T : ℝ} {L M h : ℕ} {e : X ⊕ Fin M ≃ n}
  {j : S →* USign ε × USign η} {φ : S → ℂ}

section Cone

open Norms.Frobenius

/-- **The cone near the identity.** Let `j` and `φ` satisfy `IsLaplaceDatum`: in particular `φ` is
additive, and for `(g, g') = j s` it is `φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))`. Let both
parameters have gap `500 · (dimension)³ + h` and entries bounded by `L`, let
`card n + card m + L ≤ β` and `log β ≥ 1`, put `T = (card n + card m)² log β` and let `δ T ≤ 10⁻¹²`.
If `g - 1` and `g' - 1` have Frobenius norm at most `δ`, then `z = laplaceIntegrand s` lies in the
cone `‖z‖ ≤ 2 re z + 12 exp (-100 T)`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add_of_near
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ_le : card n + card m + L ≤ β) (h_log_β : 1 ≤ β.log)
    (hT : T = (card n + card m : ℝ) ^ 2 * β.log) {δ : ℝ} (hδ : δ * T ≤ 1e-12)
    {s : S} (h_fst : ‖((j s).1 : Matrix n n ℂ) - 1‖ ≤ δ)
    (h_snd : ‖((j s).2 : Matrix m m ℂ) - 1‖ ≤ δ) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re + 12 * rexp (-100 * T) := by
  -- The phases cancel, so the value is close to a product of two numbers in `[0, 1]`.
  have hn_pos : (1 : ℝ) ≤ card n := Nat.one_le_cast.2 Fintype.card_pos
  have hm_pos : (1 : ℝ) ≤ card m := Nat.one_le_cast.2 Fintype.card_pos
  have hT_one : 1 ≤ T := by nlinarith
  have hδ_half : δ ≤ 2⁻¹ := by nlinarith [(norm_nonneg _).trans h_fst]
  have h_dim (d : ℝ) (hd : 1 ≤ d) (hd' : d + 1 ≤ card n + card m) :
      d ^ 2 ≤ T ∧ d ^ 2 * (d + L + 1).log ≤ T := by
    have h_sq : d ^ 2 ≤ (card n + card m : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h_log : (d + L + 1).log ≤ β.log := log_le_log (by positivity) (by linarith)
    refine ⟨by nlinarith, ?_⟩
    rw [hT]
    exact mul_le_mul h_sq h_log (log_nonneg (by linarith)) (sq_nonneg _)
  obtain ⟨hn_sq, hn_log⟩ := h_dim (card n) hn_pos (by linarith)
  obtain ⟨hm_sq, hm_log⟩ := h_dim (card m) hm_pos (by linarith)
  set ratio_l : ℂ := l.dsCoeff (j s).1 /
    cexp (intDiagonal l.lowestKType * logOneAdd (subOnePair j s).1).trace with h_ratio_l
  set ratio_k : ℂ := (-k).dsCoeff (j s).2 /
    cexp (intDiagonal (-k).lowestKType * logOneAdd (subOnePair j s).2).trace with h_ratio_k
  -- The phase at the matrix logarithms `logOneAdd` of the two components of `j s` is still `φ s`.
  have h_prod : l.laplaceIntegrand k j φ s = ratio_l * ratio_k := by
    have h_phase : l.phase k ((subOnePair j s).map logOneAdd logOneAdd) = φ s :=
      h_datum.phase_logOneAdd s (h_fst.trans hδ_half) (h_snd.trans hδ_half)
    rw [h_ratio_l, h_ratio_k, laplaceIntegrand, ← h_phase, dsCoeff_neg hk]
    -- Unfold the phase as a difference of traces and use `exp (x - y) = exp x / exp y`.
    simp [phase, intDiagonal, field, ← diagonal_neg, Complex.exp_sub, Complex.exp_neg]
  obtain ⟨a, ha, ha_near⟩ : ∃ a ∈ Set.Icc (0 : ℝ) 1, ‖ratio_l - a‖ ≤ a / 10 + rexp (-100 * T) :=
    exists_norm_dsCoeff_div_cexp_sub_le hl hl_le h_fst hT_one hn_sq hn_log hδ
  obtain ⟨c, hc, hc_near⟩ : ∃ c ∈ Set.Icc (0 : ℝ) 1, ‖ratio_k - c‖ ≤ c / 10 + rexp (-100 * T) :=
    exists_norm_dsCoeff_div_cexp_sub_le hk.neg (by simpa using hk_le) h_snd hT_one hm_sq hm_log hδ
  have h_exp : rexp (-100 * T) ∈ Set.Icc 0 1 := ⟨exp_nonneg _, exp_le_one_iff.2 (by linarith)⟩
  rw [h_prod]
  exact norm_le_two_mul_re_add (mul_nonneg ha.1 hc.1)
    (norm_mul_sub_mul_le ha hc h_exp ha_near hc_near)

/-- **The cone.** Let `j` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`: the weight of the lowest
`K`-type of `l` is `0` on `X` and decreases in `[-3 B, -B]` elsewhere, that of `k` is nonnegative
and `0` on `X`, the difference `φ` of the two phases is additive and imaginary, and the image of `j`
contains `U(X)`, placed in the two factors by `e` and `τ`. Let the entries of `l` and `k` be bounded
by `L`, let `card n + card m + L ≤ β` and `log β ≥ 1`, and put `T = (card n + card m)² log β`. Let
both doubled parameters have gap `500 · (dimension)³ + h` with `h ≥ 10³⁰ T³`. Then every value `z`
of `laplaceIntegrand` at an `s`, with `j s = (g, g')`, satisfies
`‖z‖ ≤ 2 re z + 12 exp (-100 T)`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h)
    (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L) (hk_le : ∀ a : m, |k a| ≤ L)
    (hβ_le : card n + card m + L ≤ β) (h_log_β : 1 ≤ β.log)
    (hT : T = (card n + card m : ℝ) ^ 2 * β.log) (hh : 10 ^ 30 * T ^ 3 ≤ h) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re + 12 * rexp (-100 * T) := by
  have hT_one : 1 ≤ T := by
    have h_card : (1 : ℝ) ≤ card n + card m := mod_cast Nat.add_pos_left Fintype.card_pos _
    nlinarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, T * ρ = 1e-13 := ⟨1e-13 / T, by field_simp⟩
  rcases le_total (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) (ρ ^ 2) with
    h_near | h_far
  · -- By localization the value at `s` is also taken at a `t` with `j t` within `4 ρ` of `1`.
    have hρ_pos : 0 < ρ := by nlinarith
    have hρ_le : ρ ≤ 6⁻¹ := by nlinarith
    obtain ⟨t, hθ, h_fst, h_snd⟩ : ∃ t : S,
        l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
        ‖(subOnePair j t).1‖ ≤ 4 * ρ ∧ ‖(subOnePair j t).2‖ ≤ 4 * ρ :=
      h_datum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le ρ hB hρ_pos hρ_le s h_near
    rw [hθ]
    exact h_datum.norm_laplaceIntegrand_le_mul_re_add_of_near hl hk hl_le hk_le hβ_le h_log_β hT
      (by linarith : 4 * ρ * T ≤ 1e-12) h_fst h_snd
  · -- Away from the maximal compact subgroups the gap makes the value itself small.
    have h_small : ‖l.laplaceIntegrand k j φ s‖ ≤ rexp (-100 * T) :=
      h_datum.norm_laplaceIntegrand_le_of_far hl hk hT_one hρ hh h_far
    linarith [exp_nonneg (-100 * T),
      neg_le_of_abs_le (abs_re_le_norm (l.laplaceIntegrand k j φ s))]

end Cone

open Norms.L2Operator

/-- **Decay.** Let `j` and `φ` satisfy `IsLaplaceDatum` (so `φ` is imaginary). Let `l` and `k`
satisfy `HasLargeGap h`, i.e. have gap `500 · (dimension)³ + h`. Let `c ≤ h` and `j s = (g, g')`,
and write `g ⊕ g'` for the block diagonal sum `U.sum (signMatrix_sum ε η) (j s)` in `U(ε ⊕ η)`. Then
the norm of `laplaceIntegrand` at `s` is at most `(2 / ‖g ⊕ g'‖) ^ c`, where `‖g ⊕ g'‖` is the
operator norm. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_pow (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) {c : ℕ} (hc : c ≤ h) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤
      (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ c := by
  -- Use the decay of the coefficient at the larger component; the other one is at most `1`.
  rw [h_datum.norm_laplaceIntegrand, norm_coe_sum_eq_max]
  rcases max_choice ‖((j s).1 : Matrix n n ℂ)‖ ‖((j s).2 : Matrix m m ℂ)‖ with h_max | h_max
  · rw [h_max]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_dsCoeff_le_one hk _)).trans
      (norm_dsCoeff_le_pow hl (hc.trans le_add_self) _)
  · rw [h_max]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_dsCoeff_le_one hl _)).trans
      (norm_dsCoeff_le_pow hk (hc.trans le_add_self) _)

/-- If `‖z‖ ≤ 2 re z + 12 E²` and `‖z‖ ≤ G²` with `E, G ≥ 0`, then `‖z‖ ≤ 2 re z + 6 E G`: this is
the geometric mean of the bounds `12 E²` and `3 G²` for `‖z‖ - 2 re z`. -/
lemma norm_le_two_mul_re_add_mul {z : ℂ} {E G : ℝ} (hE : 0 ≤ E) (hG : 0 ≤ G)
    (h_cone : ‖z‖ ≤ 2 * z.re + 12 * E ^ 2) (h_decay : ‖z‖ ≤ G ^ 2) :
    ‖z‖ ≤ 2 * z.re + 6 * E * G := by
  by_contra h_gt
  have h_nonneg : 0 ≤ 6 * E * G := by positivity
  have h_sq : (‖z‖ - 2 * z.re) * (‖z‖ - 2 * z.re) ≤ 12 * E ^ 2 * (3 * G ^ 2) :=
    mul_le_mul (by linarith) (by linarith [neg_le_of_abs_le (abs_re_le_norm z)]) (by linarith)
      (by positivity)
  linarith [mul_self_lt_mul_self h_nonneg (by linarith : 6 * E * G < ‖z‖ - 2 * z.re)]

/-- **The cone with a decaying error.** Let `j` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`. Let
the entries of `l` and `k` be bounded by `L`, let `log β ≥ 1` and `card n + card m + L ≤ β`, and put
`N = (card n + card m)²`. Let both doubled parameters have gap `500 · (dimension)³ + h`, with
`h ≥ 10³⁰ (N log β)³`. Write `j s = (g, g')` and `z` for the value at `s` of `laplaceIntegrand`.
Then `‖z‖ ≤ 2 re z + 6 β ^ (-50 N) (2 / ‖g ⊕ g'‖) ^ (9 N)`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add_mul_pow
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ_le : card n + card m + L ≤ β) (hβ : 1 ≤ β.log)
    (hh : 10 ^ 30 * ((card n + card m) ^ 2 * β.log) ^ 3 ≤ h) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re +
      6 * β⁻¹ ^ (50 * (card n + card m) ^ 2) *
        (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^
          (9 * (card n + card m) ^ 2) := by
  -- Combine the constant error of the cone with the decay `‖z‖ ≤ (2 / ‖g ⊕ g'‖) ^ (18 N)`.
  set N : ℕ := (card n + card m) ^ 2 with hN
  have hN_cast : (N : ℝ) = (card n + card m) ^ 2 := by simp [hN]
  have hβ_pos : 0 < β := lt_of_lt_of_le (by positivity) hβ_le
  have h_gap : 18 * N ≤ h := eighteen_mul_le_of_mul_pow_three_le
    (Nat.one_le_pow _ _ (Nat.add_pos_left card_pos _)) hβ (by rwa [hN_cast])
  have h_err : rexp (-100 * ((card n + card m : ℝ) ^ 2 * β.log)) = (β⁻¹ ^ (50 * N)) ^ 2 := by
    rw [← hN_cast, ← pow_mul, ← exp_log (inv_pos.2 hβ_pos), ← Real.exp_natCast_mul, Real.log_inv]
    push_cast
    ring_nf
  have h_cone : ‖l.laplaceIntegrand k j φ s‖ ≤
      2 * (l.laplaceIntegrand k j φ s).re + 12 * (β⁻¹ ^ (50 * N)) ^ 2 :=
    (h_datum.norm_laplaceIntegrand_le_mul_re_add hl hk hB hl_le hk_le hβ_le hβ rfl hh s).trans_eq
      (by rw [h_err])
  have h_decay : ‖l.laplaceIntegrand k j φ s‖ ≤
      ((2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N)) ^ 2 :=
    (h_datum.norm_laplaceIntegrand_le_pow hl hk (by omega) s).trans_eq (pow_mul _ _ 2)
  exact norm_le_two_mul_re_add_mul (by positivity) (by positivity) h_cone h_decay

/-- **The pointwise bounds.** Let `j` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`, let the entries
of `l` and `k` be bounded by `L`, let `β ≥ 3` and `card n + card m + L ≤ β`, put
`N = (card n + card m)²`, and let both parameters have gap `500 · (dimension)³ + h` with
`h ≥ 10³⁰ (N log β)³`. Write `j s = (g, g')`, `G = (2 / ‖g ⊕ g'‖) ^ (9 N)` in the operator norm and
`z` for the value at `s` of `laplaceIntegrand`. Then `‖z‖ ≤ G` and
`‖z‖ ≤ 2 re z + 6 β ^ (-50 N) G`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ : 3 ≤ β) (hβ_le : card n + card m + L ≤ β)
    (hh : 10 ^ 30 * ((card n + card m) ^ 2 * β.log) ^ 3 ≤ h)
    {N : ℕ} (hN : N = (card n + card m) ^ 2) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤
      (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N) ∧
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re + 6 * β⁻¹ ^ (50 * N) *
      (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N) := by
  have h_log : 1 ≤ β.log := (le_log_iff_exp_le (by linarith)).2 (exp_one_lt_three.le.trans hβ)
  subst hN
  have h_gap : 18 * (card n + card m) ^ 2 ≤ h := eighteen_mul_le_of_mul_pow_three_le
    (Nat.one_le_pow _ _ (Nat.add_pos_left card_pos _)) h_log (by simpa using hh)
  exact ⟨h_datum.norm_laplaceIntegrand_le_pow hl hk (by omega) s,
    h_datum.norm_laplaceIntegrand_le_two_mul_re_add_mul_pow hl hk hB hl_le hk_le hβ_le h_log hh s⟩

/-- Integration of the bound `‖f‖ ≤ 2 re f + c G`: if moreover `‖f‖ ≥ 1 / 4` on `A`, then
`ν(A) / 4 ≤ 2 ‖∫ f‖ + c ∫ G`. -/
lemma measureReal_div_four_le {α : Type} [MeasurableSpace α] (ν : Measure α) {f : α → ℂ}
    {G : α → ℝ} {c : ℝ} {A : Set α} (hf : Integrable f ν) (hG : Integrable G ν)
    (h_le : ∀ s : α, ‖f s‖ ≤ 2 * (f s).re + c * G s) (hA : ∀ s ∈ A, 1 / 4 ≤ ‖f s‖) :
    ν.real A / 4 ≤ 2 * ‖∫ s : α, f s ∂ν‖ + c * ∫ s : α, G s ∂ν := by
  have h_re : Integrable (fun s : α ↦ (f s).re) ν := hf.re
  calc ν.real A / 4 ≤ 1 / 4 * ν.real {s : α | 1 / 4 ≤ ‖f s‖} := by
        linarith [(measureReal_mono hA (hf.measure_norm_ge_lt_top (by norm_num)).ne :
          ν.real A ≤ ν.real {s : α | 1 / 4 ≤ ‖f s‖})]
    _ ≤ ∫ s, ‖f s‖ ∂ν :=
        mul_meas_ge_le_integral_of_nonneg (.of_forall fun s ↦ norm_nonneg (f s)) hf.norm (1 / 4)
    _ ≤ ∫ s, 2 * (f s).re + c * G s ∂ν :=
        integral_mono hf.norm ((h_re.const_mul 2).add (hG.const_mul c)) h_le
    _ = 2 * (∫ s, f s ∂ν).re + c * ∫ s, G s ∂ν := by
        rw [integral_add (h_re.const_mul 2) (hG.const_mul c), integral_const_mul,
          integral_const_mul, show ∫ s, (f s).re ∂ν = (∫ s, f s ∂ν).re from integral_re hf]
    _ ≤ 2 * ‖∫ s, f s ∂ν‖ + c * ∫ s, G s ∂ν := by linarith [re_le_norm (∫ s, f s ∂ν)]

variable [MeasurableSpace S] [MeasurableMul S] (ν : Measure S) [ν.IsMulRightInvariant]

/-- The covering bound for two radii, for a right invariant measure `ν` on `S` and the `L²` operator
norm: for `J : S →* U(ζ)` with `ζ` indexed by `ι` and `β ≥ 10¹²`, the volume of `{‖J s‖ ≤ β + 1}` is
at most `β ^ (16 (card ι)²)` times that of `{‖J s - 1‖ ≤ (200 β⁵)⁻¹}`. -/
lemma measure_large_ball_le_pow_mul_small_ball {ι : Type} [Fintype ι] [DecidableEq ι]
    {ζ : ι → ℤˣ} (J : S →* USign ζ) (hβ : 10 ^ 12 ≤ β) :
    ν {s : S | ‖(J s : Matrix ι ι ℂ)‖ ≤ β + 1} ≤ ENNReal.ofReal (β ^ (16 * card ι ^ 2)) *
      ν {s : S | ‖(J s : Matrix ι ι ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹} := by
  have h_radii : 3 * (200 * β ^ 5) * (β + 1) ^ 2 ≤ β ^ 8 := by
    field_simp
    nlinarith
  have h_one : 1 ≤ 200 * β ^ 5 := by linarith [one_le_pow₀ (n := 5) (by linarith : 1 ≤ β)]
  simpa only [mul_one, ← pow_mul, ← mul_assoc, Nat.reduceMul] using
    measure_ball_le_covering ν J 1 h_one (by linarith) h_radii

/-- **Laplace's method.** Let `j : S →* U(ε) × U(η)` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`:
the weight of the lowest `K`-type of `l` is `0` at the indices `e (inl x)`, `x : X`, and decreases
in `[-3 B, -B]` elsewhere, that of `k` is nonnegative and `0` on the image of `τ`, the difference
`φ` of the two phases is additive and imaginary, and the image of `j` contains `U(X)`, placed in the
two factors by `e` and `τ`. Let the first component of `j` be proper and the second continuous, and
let `ν` be a right invariant measure on `S` that is finite on compact sets. Let the entries of the
Harish-Chandra parameters `l = 2λ`, `k` (doubled) be bounded by `L`, let `β ≥ 10¹²` bound
`card n + card m + L`, and let both have gap `500 · (dimension)³ + h` with
`h ≥ 10³⁰ ((card n + card m)² log β)³`. Then the function `θ = laplaceIntegrand` is integrable, and
the volume of the set of `s` at which both components of `j s` have operator norm at most `β + 1` is
at most `β ^ (20 (card n + card m)²) ‖∫ θ‖`. -/
theorem IsLaplaceDatum.laplace_method [TopologicalSpace S] [BorelSpace S]
    [IsFiniteMeasureOnCompacts ν] (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hj : IsProperMap fun s : S ↦ (j s).1) (hj' : Continuous fun s : S ↦ (j s).2)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ : 10 ^ 12 ≤ β) (hβ_le : card n + card m + L ≤ β)
    (hh : 10 ^ 30 * ((card n + card m) ^ 2 * β.log) ^ 3 ≤ h) :
    Integrable (l.laplaceIntegrand k j φ) ν ∧
    ν {s : S | ‖((j s).1 : Matrix n n ℂ)‖ ≤ β + 1 ∧ ‖((j s).2 : Matrix m m ℂ)‖ ≤ β + 1} ≤
      ENNReal.ofReal (β ^ (20 * (card n + card m) ^ 2) *
        ‖∫ s : S, l.laplaceIntegrand k j φ s ∂ν‖) := by
  -- Integrate the pointwise bounds (cone and decay) along the proper map `J : s ↦ g ⊕ g'`, where
  -- `j s = (g, g')`, and compare the volumes of a large and a small ball by covering.
  have hβ16 : 16 ≤ β := le_trans (by norm_num) hβ
  set N : ℕ := (card n + card m) ^ 2 with hN
  let J : S →* USign (Sum.elim ε η) := (U.sum (signMatrix_sum ε η)).comp j
  have hJ : IsProperMap J := isProperMap_sum hj hj'
  let Large : Set S := {s : S | ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖ ≤ β + 1}
  let UnitBall : Set S := {s | ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ ≤ 1}
  let Small : Set S := {s : S | ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹}
  let G (s : S) : ℝ := (2 / ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N)
  have h_decay_cone : ∀ s : S, ‖l.laplaceIntegrand k j φ s‖ ≤ G s ∧ ‖l.laplaceIntegrand k j φ s‖ ≤
      2 * (l.laplaceIntegrand k j φ s).re + 6 * β⁻¹ ^ (50 * N) * G s :=
    h_datum.norm_laplaceIntegrand_le_two_mul_re_add hl hk hB hl_le hk_le (by linarith) hβ_le hh hN
  -- The decay makes `laplaceIntegrand` integrable.
  have hN_pos : 1 ≤ N := Nat.one_le_pow _ _ (Nat.add_pos_left card_pos _)
  obtain ⟨hG_int, hG_le⟩ : Integrable G ν ∧ ∫ s, G s ∂ν ≤ 16 ^ (9 * N) * ν.real UnitBall := by
    simpa only [mul_one] using integral_decay_le ν hJ (c := 9 * N) (by rw [card_sum]; omega) 1
  have hθ_cont : Continuous (l.laplaceIntegrand k j φ) := by
    have hj_cont : Continuous fun s : S ↦ (j s).1 := hj.continuous
    obtain rfl : (fun s : S ↦ l.phase k (subOnePair j s)) = φ := funext h_datum.phase_eq
    fun_prop [laplaceIntegrand, phase]
  have hθ_int : Integrable (l.laplaceIntegrand k j φ) ν :=
    hG_int.mono' hθ_cont.aestronglyMeasurable (.of_forall fun s ↦ (h_decay_cone s).1)
  -- The covering bound compares the large ball with the small one, on which the integrand has
  -- norm at least `1 / 4`.
  have h_small_fin : ν Small ≠ ⊤ := measure_ball_ne_top_of_isProperMap ν hJ _
  have h_cover : ν Large ≤ ENNReal.ofReal (β ^ (16 * N)) * ν Small := by
    simpa only [card_sum] using measure_large_ball_le_pow_mul_small_ball ν J hβ
  have h_cover_real : ν.real Large ≤ β ^ (16 * N) * ν.real Small := by
    simpa [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ β ^ (16 * N))] using
      ENNReal.toReal_mono (by finiteness) h_cover
  have h_large_fin : ν Large ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) h_cover
  have h_int : ν.real Small / 4 ≤ 2 * ‖∫ s, l.laplaceIntegrand k j φ s ∂ν‖ +
      6 * β⁻¹ ^ (50 * N) * (16 ^ (9 * N) * ν.real Large) := by
    refine (measureReal_div_four_le ν hθ_int hG_int (fun s ↦ (h_decay_cone s).2) fun s hs ↦
      h_datum.one_div_four_le_norm_laplaceIntegrand hl hk hl_le hk_le hβ_le hs).trans ?_
    grw [hG_le, measureReal_mono (s₁ := UnitBall) (s₂ := Large)
      (fun s hs ↦ (norm_le_norm_add_norm_sub' _ 1).trans (by
        simpa only [norm_one] using add_le_add (show 1 ≤ β by linarith) hs)) h_large_fin]
  refine ⟨hθ_int, (measure_mono fun s hs ↦ ?_).trans <|
    (ENNReal.le_ofReal_iff_toReal_le h_large_fin (by positivity)).2 <|
      le_pow_mul_of_le hβ16 hN_pos measureReal_nonneg (norm_nonneg _) h_cover_real h_int⟩
  simpa [Large, J, norm_coe_sum_eq_max] using hs

end New.DiscreteSeries

end LaplaceMethod
