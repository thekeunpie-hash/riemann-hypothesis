module

import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Order.CompletePartialOrder
public import Lib.General.NumberTheory.ImaginaryQuadraticField
import Lib.Analytic.EntireLFunction
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.LSeries.Nonvanishing

section
/-!
# Growth of Dirichlet L-functions near the line `re s = 1`

Let `χ` be a character modulo `N`, and let `𝖿_χ(s)` (`regularL χ s`) be `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. The right-half-plane bound from Tau Ceti gives
`|𝖿_χ(s)| ≤ 8 N |s|` in `re s ≥ 1 / 2`, and the three-lines theorem improves this to
`|𝖿_χ(s)| ≤ l²` for `re s ≥ 1 - 1 / l` and `|s| ≤ 3 e^l`, whenever `l ≥ 10¹⁰` and `N ≤ e^l`.

Notions from other files:
* `entireL χ`: the entire function equal to `L(s, χ)` if `χ` is not principal, and to the
  continuation of `(s - 1) L(s, χ)` if it is.

## Relation to the literature

Known result: the bound `L(s, χ) ≪ log (N |s|)` near `re s = 1` and away from the pole. It is proved
here for `𝖿_χ` and with a square in place of the first power. Source: Montgomery and Vaughan,
Multiplicative Number Theory I, 2007, Lemma 10.15.
-/

@[expose] public section

noncomputable section

open Complex Real Set Filter Topology MeasureTheory Metric Asymptotics DirichletCharacter
  HadamardThreeLines
open scoped Classical

namespace New

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}

omit [NeZero N] in
/-- If `re s ≥ 1 + 1 / A` with `A > 0`, then `|L(s, χ)| ≤ 1 + A`, since the Dirichlet series of
`χ` is dominated by `ζ(re s)`. -/
lemma norm_LSeries_char_le {A : ℝ} (hA : 0 < A) (hs : 1 + 1 / A ≤ s.re) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 1 + A := by
  have hs_one : 1 < s.re := by linarith [one_div_pos.2 hA]
  have h_sum : HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ s.re) (riemannZeta s.re).re := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _), one_div] using
      TauCeti.hasSum_nat_rpow_neg_riemannZeta_re hs_one
  have term_le (n : ℕ) : ‖LSeries.term (χ ·) s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
    rw [LSeries.norm_term_eq]
    split_ifs
    · positivity
    · exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  calc
    _ ≤ (riemannZeta s.re).re := tsum_of_norm_bounded h_sum term_le
    _ ≤ 1 + 1 / (s.re - 1) :=
      (TauCeti.riemannZeta_re_lt_one_add_one_div_sub_one (zero_lt_one.trans hs_one) hs_one.ne').le
    _ ≤ 1 + A := by linarith [(one_div_le hA (sub_pos.2 hs_one)).1 (by linarith)]

/-- `𝖿_χ(s)` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal. The entire function `entireL χ`
has the factor `s - 1` in that case; dividing by `s` keeps the size of `L(s, χ)` for large `|s|`. -/
def regularL (s : ℂ) : ℂ := entireL χ s / if χ = 1 then s else 1

/-- `𝖿_χ` (`regularL χ`: `L(s, χ)`, times `(s - 1) / s` if `χ` is principal) is holomorphic in
`re s > 0`. -/
lemma differentiableAt_regularL (hs : 0 < s.re) : DifferentiableAt ℂ (regularL χ) s := by
  have h_denom_diff : DifferentiableAt ℂ (fun z : ℂ ↦ if χ = 1 then z else 1) s := by
    split_ifs <;> fun_prop
  have h_denom_ne : (if χ = 1 then s else 1) ≠ 0 := by
    split_ifs
    exacts [ne_zero_of_re_pos hs, one_ne_zero]
  exact (analyticAt_entireL χ s).differentiableAt.div h_denom_diff h_denom_ne

/-- In `re s > 1` the regularised function `𝖿_χ` (`regularL χ`) is `L(s, χ) (s - δ) / s`, with
`δ = 1` if `χ` is principal and `δ = 0` otherwise. -/
lemma regularL_eq (hs : 1 < s.re) :
    regularL χ s = LSeries (fun n : ℕ ↦ χ n) s / s * (s - if χ = 1 then 1 else 0) := by
  have hs_zero : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  rw [regularL, entireL, ← χ.LFunction_eq_LSeries hs]
  split_ifs with hχ
  · rw [hχ, LFunctionTrivChar₁, Function.update_of_ne (ne_of_apply_ne re hs.ne')]
    ring
  · field

/-- `|s - δ| ≤ |s|` in `re s ≥ 1 / 2`, where `δ` is `1` or `0` as the proposition `p` holds or
not (in the uses, `p` says that a character is principal). -/
lemma norm_sub_ite_le {p : Prop} [Decidable p] (hs : 1 / 2 ≤ s.re) :
    ‖s - if p then 1 else 0‖ ≤ ‖s‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  split_ifs
  · simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, one_re, one_im]
    -- For `δ = 1` this is `(re s - 1)² ≤ (re s)²`.
    linarith
  · simp

/-- Linear growth bound: `|𝖿_χ(s)| ≤ 8 N |s|` in `re s ≥ 1 / 2`, where `𝖿_χ` (`regularL χ`) is
`L(s, χ)`, times `(s - 1) / s` if `χ` is principal, and `N` is the modulus of `χ`. -/
lemma norm_regularL_le_linear (hs : 1 / 2 ≤ s.re) : ‖regularL χ s‖ ≤ 8 * N * ‖s‖ := by
  have bound_ne {z : ℂ} (hz : 1 / 2 ≤ z.re) (hz1 : z ≠ 1) :
      ‖regularL χ z‖ ≤ 8 * N * ‖z‖ := by
    have hz_pos : 0 < z.re := by linarith
    have hz_norm : 1 / 2 ≤ ‖z‖ := hz.trans (re_le_norm z)
    by_cases hχ : χ = 1
    · have h_eq : regularL χ z = (z - 1) / z * χ.LFunction z := by
        simp [regularL, entireL, hχ, LFunctionTrivChar₁, Function.update_of_ne hz1]
        ring
      have h_sub : ‖z - 1‖ ≤ ‖z‖ := by simpa using norm_sub_ite_le (p := True) hz
      have h_inv : ‖z - 1‖ / ‖z‖ * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re) ≤ 8 * ‖z‖ := by
        have hz1_pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
        have h1_le : 1 / ‖z‖ ≤ 4 * ‖z‖ := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        have h2_le : ‖z - 1‖ / ‖z‖ ≤ 2 * ‖z‖ := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        have h3_le : ‖z - 1‖ / z.re ≤ 2 * ‖z‖ := by
          rw [div_le_iff₀ hz_pos]
          nlinarith
        calc
          ‖z - 1‖ / ‖z‖ * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re)
              = 1 / ‖z‖ + ‖z - 1‖ / ‖z‖ + ‖z - 1‖ / z.re := by
            field_simp [hz1_pos.ne', (show (0 : ℝ) < ‖z‖ by linarith).ne', hz_pos.ne']
          _ ≤ 8 * ‖z‖ := by linarith
      calc
        ‖regularL χ z‖ = ‖z - 1‖ / ‖z‖ * ‖χ.LFunction z‖ := by rw [h_eq, norm_mul, norm_div]
        _ ≤ ‖z - 1‖ / ‖z‖ * (N * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re)) := by
          gcongr
          exact χ.norm_LFunction_le hz_pos (.inl hz1)
        _ = N * (‖z - 1‖ / ‖z‖ * (‖z - 1‖⁻¹ + 1 + ‖z‖ / z.re)) := by ring
        _ ≤ N * (8 * ‖z‖) := by gcongr
        _ = 8 * N * ‖z‖ := by ring
    · have h_eq : regularL χ z = χ.LFunction z := by simp [regularL, entireL, hχ]
      calc
        ‖regularL χ z‖ = ‖χ.LFunction z‖ := by rw [h_eq]
        _ ≤ N * ‖z‖ / z.re := χ.norm_LFunction_le_level_mul_norm_div_re hχ hz_pos
        _ ≤ N * ‖z‖ / (1 / 2) := by gcongr
        _ ≤ 8 * N * ‖z‖ := by nlinarith [norm_nonneg z]
  -- Extend the estimate from the punctured open half-plane by continuity.
  have hs_closure : s ∈ closure ({z : ℂ | 1 / 2 < z.re} ∩ {1}ᶜ) :=
    closure_minimal
      ((dense_compl_singleton (1 : ℂ)).open_subset_closure_inter (isOpen_re_gt (1 / 2)))
      isClosed_closure (by simpa only [closure_setOfPred_lt_re, Set.mem_ofPred_eq] using hs)
  exact ContinuousWithinAt.closure_le (g := fun z : ℂ ↦ 8 * N * ‖z‖) hs_closure
    (differentiableAt_regularL χ (by linarith)).continuousAt.norm.continuousWithinAt
    (by fun_prop) (fun z hz ↦ bound_ne (le_of_lt hz.1) hz.2)

/-- For `l ≥ 1` and `re s > 1`, at distance at least `1 / l` from `1` if `χ` is principal, we have
`|L(s, χ)| ≤ 2 l |𝖿_χ(s)|`, where `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times `(s - 1) / s` if `χ` is
principal. -/
lemma norm_LSeries_le_mul_norm_regularL (hs : 1 < s.re) (hl : 1 ≤ l)
    (h_far : χ = 1 → 1 / l ≤ ‖s - 1‖) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 2 * l * ‖regularL χ s‖ := by
  have hs_norm : 1 < ‖s‖ := hs.trans_le (re_le_norm s)
  have norm_le : ‖s‖ ≤ 2 * l * ‖s - if χ = 1 then 1 else 0‖ := by
    split_ifs with hχ
    · have h_one : 1 ≤ ‖s - 1‖ * l := (div_le_iff₀ (by linarith)).1 (h_far hχ)
      nlinarith [norm_nonneg (s - 1), norm_le_norm_sub_add s 1, norm_one (α := ℂ)]
    · simpa using le_mul_of_one_le_left (norm_nonneg s) (by linarith : 1 ≤ 2 * l)
  calc
    ‖LSeries (χ ·) s‖ = ‖LSeries (χ ·) s‖ / ‖s‖ * ‖s‖ := by field
    _ ≤ ‖LSeries (χ ·) s‖ / ‖s‖ * (2 * l * ‖s - if χ = 1 then 1 else 0‖) := by gcongr
    _ = 2 * l * ‖regularL χ s‖ := by simp [regularL_eq χ hs]; ring

/-- If `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ(s)| ≤ l²` for
`re s ≥ 1 - 1 / l` and `|s| ≤ 3 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_regularL_le_sq (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l ≤ s.re)
    (h_norm : ‖s‖ ≤ 3 * rexp l) : ‖regularL χ s‖ ≤ l ^ 2 := by
  -- Apply the three-lines theorem to `g(z) = 𝖿_χ(z) / (z - s + 2)` on the strip
  -- `a ≤ re z ≤ a + 1 / 3` whose right edge lies at `re s + 2 / l ≥ 1 + 1 / l`. The left edge,
  -- where `|g| ≤ e^(3 l)`, has the weight `6 / l` at `s`. The denominator makes `g` bounded; it
  -- has modulus at least `1` on the strip and is `2` at `s`.
  have inv_pos : 0 < 1 / l := by positivity
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have exp_ge : l + 1 ≤ rexp l := add_one_le_exp l
  set a : ℝ := s.re + 2 * (1 / l) - 1 / 3 with ha
  let g (z : ℂ) : ℂ := regularL χ z / (z - (s - 2))
  have denom_ge (z : ℂ) (hz : a ≤ z.re) : 1 ≤ ‖z - (s - 2)‖ :=
    le_trans (by simp; linarith) (re_le_norm _)
  have g_le_exp_cube (z : ℂ) (hz : a ≤ z.re) : ‖g z‖ ≤ rexp l ^ 3 := by
    have h_denom : 1 ≤ ‖z - (s - 2)‖ := denom_ge z hz
    have hz_norm : ‖z‖ ≤ 4 * rexp l * ‖z - (s - 2)‖ := by
      have h_exp : 3 ≤ rexp l := by linarith only [hl, exp_ge]
      have h_center : ‖s - 2‖ ≤ 3 * rexp l + 2 := by
        calc
          ‖s - 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_sub_le s 2
          _ ≤ 3 * rexp l + 2 := by
              simpa only [Complex.norm_two] using add_le_add_left h_norm ‖(2 : ℂ)‖
      calc
        ‖z‖ ≤ ‖z - (s - 2)‖ + ‖s - 2‖ := norm_le_norm_sub_add z (s - 2)
        _ ≤ ‖z - (s - 2)‖ + (3 * rexp l + 2) := add_le_add_right h_center _
        _ ≤ ‖z - (s - 2)‖ + (3 * rexp l + 2) * ‖z - (s - 2)‖ := by
          exact add_le_add_right
              (le_mul_of_one_le_right (show 0 ≤ 3 * rexp l + 2 by positivity) h_denom) _
        _ = (3 * rexp l + 3) * ‖z - (s - 2)‖ := by ring
        _ ≤ 4 * rexp l * ‖z - (s - 2)‖ :=
          mul_le_mul_of_nonneg_right (by linarith only [h_exp]) (norm_nonneg _)
    rw [norm_div, div_le_iff₀ (by linarith)]
    calc
      ‖regularL χ z‖ ≤ 8 * N * ‖z‖ := norm_regularL_le_linear χ (by linarith)
      _ ≤ 8 * rexp l * (4 * rexp l * ‖z - (s - 2)‖) := by gcongr
      _ = 32 * rexp l ^ 2 * ‖z - (s - 2)‖ := by ring
      _ ≤ rexp l ^ 3 * ‖z - (s - 2)‖ := by
        gcongr
        nlinarith [sq_nonneg (rexp l), mul_le_mul exp_ge exp_ge]
  have right_edge (z : ℂ) (hz : z.re = a + 1 / 3) : ‖g z‖ ≤ 1 + l := by
    have hz_norm : 0 < ‖z‖ := by linarith [re_le_norm z]
    calc
      ‖g z‖ ≤ ‖regularL χ z‖ :=
        (norm_div _ _).trans_le (div_le_self (norm_nonneg _) (denom_ge z (by linarith)))
      _ ≤ ‖LSeries (χ ·) z‖ / ‖z‖ * ‖z‖ := by
        rw [regularL_eq χ (by linarith), norm_mul, norm_div]
        gcongr
        exact norm_sub_ite_le (by linarith)
      _ = ‖LSeries (χ ·) z‖ := div_mul_cancel₀ _ hz_norm.ne'
      _ ≤ 1 + l := by
        have h_re_right : 1 + 1 / l ≤ z.re := by linarith
        exact norm_LSeries_char_le χ (by linarith) h_re_right
  have g_diff : DiffContOnCl ℂ g (verticalStrip a (a + 1 / 3)) := by
    refine DifferentiableOn.diffContOnCl fun z hz ↦ ?_
    rw [verticalStrip, closure_preimage_re, closure_Ioo (by linarith)] at hz
    obtain ⟨hz_left, -⟩ : a ≤ z.re ∧ z.re ≤ a + 1 / 3 := hz
    have hz_pos : 0 < z.re := by linarith
    have h_denom : z - (s - 2) ≠ 0 := norm_pos_iff.1 (one_pos.trans_le (denom_ge z hz_left))
    exact ((differentiableAt_regularL χ hz_pos).fun_div (by fun_prop)
      h_denom).differentiableWithinAt
  have weight : (s.re - a) / (a + 1 / 3 - a) = 1 - 6 / l := by rw [ha]; ring
  have three_lines : ‖g s‖ ≤ (rexp l ^ 3) ^ (1 - (1 - 6 / l)) * (1 + l) ^ (1 - 6 / l) := by
    have hs_strip : s ∈ verticalClosedStrip a (a + 1 / 3) := ⟨by linarith, by linarith⟩
    have g_bdd : BddAbove ((norm ∘ g) '' verticalClosedStrip a (a + 1 / 3)) :=
      ⟨rexp l ^ 3, forall_mem_image.2 fun z ⟨hz, _⟩ ↦ g_le_exp_cube z hz⟩
    rw [← weight]
    exact norm_le_interp_of_mem_verticalClosedStrip' (by linarith) hs_strip g_diff g_bdd
      (fun z hz ↦ g_le_exp_cube z hz.ge) right_edge
  have left_factor : (rexp l ^ 3) ^ (1 - (1 - 6 / l)) ≤ 3 ^ 18 := by
    have h_exp : ((3 : ℕ) * l) * (1 - (1 - 6 / l)) = (18 : ℕ) * 1 := by field
    rw [← Real.exp_natCast_mul, ← Real.exp_mul, h_exp, Real.exp_natCast_mul]
    exact pow_le_pow_left₀ (exp_nonneg 1) exp_one_lt_three.le 18
  have right_factor : (1 + l) ^ (1 - 6 / l) ≤ 1 + l :=
    rpow_le_self_of_one_le (by linarith) (sub_le_self 1 (by positivity))
  calc
    ‖regularL χ s‖ = 2 * ‖g s‖ := by simp [g, mul_div_cancel₀]
    _ ≤ 2 * (3 ^ 18 * (1 + l)) := by grw [three_lines, left_factor, right_factor]
    _ ≤ l ^ 2 := by nlinarith

/-- Cauchy's estimate: if `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ'(s)| ≤ 2 l³`
for `re s ≥ 1 - 1 / (2 l)` and `|s| ≤ 2 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_deriv_regularL_le (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l / 2 ≤ s.re)
    (h_norm : ‖s‖ ≤ 2 * rexp l) : ‖deriv (regularL χ) s‖ ≤ 2 * l ^ 3 := by
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have disc {z : ℂ} (hz : z ∈ closedBall s (1 / l / 2)) : 1 - 1 / l ≤ z.re ∧ ‖z‖ ≤ 3 * rexp l :=
    ⟨by linarith [mem_closedBall_iff_norm.mp hz, neg_le_of_abs_le (abs_re_le_norm (z - s)),
        sub_re z s],
      by linarith [mem_closedBall_iff_norm.mp hz, norm_le_norm_sub_add z s, add_one_le_exp l]⟩
  refine ((norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
    (DifferentiableOn.diffContOnCl_ball (fun _ hz ↦ (differentiableAt_regularL χ
      (by linarith [(disc hz).1])).differentiableWithinAt) subset_rfl)
    fun _ hz ↦ norm_regularL_le_sq χ hl hN (disc (sphere_subset_closedBall hz)).1
      (disc (sphere_subset_closedBall hz)).2 : _ ≤ l ^ 2 / (1 / l / 2))).trans_eq (by field)

end New

end
end
end

/-!
# A zero-free region for Dirichlet L-functions

For a Dirichlet character `χ` and large `l`, the function `L(s, χ)` has no zero with
`re s ≥ 1 - l⁻²⁵` and `|s| ≤ e^l`, and its logarithmic derivative, with the pole removed, is at most
`2 l²⁵` there. The inequality `|L(σ, 1)³ L(σ + i t, χ)⁴ L(σ + 2 i t, χ²)| ≥ 1` bounds `L` from below
to the right of `re s = 1`, and the bound for the derivative carries this across the line. If `χ²`
is principal, the points near `1` are treated by `𝖿_χ(1) ≠ 0` and continuity; so how large `l` must
be depends on `χ`.

Notions from other files:
* `entireL χ`: the entire function `L(s, χ)`, or `(s - 1) L(s, χ)` if `χ` is principal;
* `regularL χ`, written `𝖿_χ` in comments: `entireL χ`, divided by `s` if `χ` is principal.

## Relation to the literature

Known result: the classical zero-free region, in the crude form with a power of the logarithm that
the 3-4-1 inequality gives directly. Source: Montgomery and Vaughan, Multiplicative Number Theory I,
2007, ch. 11.
-/

@[expose] public section

open Complex Real Filter Topology Metric
namespace New

variable {N : ℕ} [NeZero N]

/-- For all sufficiently small real `r`, the regularized L-function `regularL χ` (`L(s, χ)`, times
`(s - 1) / s` if `χ` is principal) has absolute value at least `r` within distance `r` of `1`. -/
lemma eventually_le_norm_regularL (χ : DirichletCharacter ℂ N) :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ s : ℂ, ‖s - 1‖ ≤ r → r ≤ ‖regularL χ s‖ := by
  have h_pos : 0 < ‖regularL χ 1‖ := by simp [regularL, entireL_ne_zero χ (s := 1) le_rfl]
  have h_near : ∀ᶠ s : ℂ in 𝓝 1, ‖regularL χ 1‖ / 2 ≤ ‖regularL χ s‖ :=
    (differentiableAt_regularL χ one_pos).continuousAt.norm.eventually_const_le (half_lt_self h_pos)
  filter_upwards [eventually_le_nhds (half_pos h_pos), eventually_closedBall_subset h_near]
    with r hr h_ball s hs using hr.trans (h_ball (mem_closedBall_iff_norm.2 hs))

/-- A lower bound from the 3-4-1 inequality. Let `l ≥ 10¹⁰`, `N ≤ e^l` and `0 < η ≤ 1`, and write
`𝖿_χ` for `regularL χ`, that is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal. Then
`η³ ≤ 256 l⁷ |𝖿_χ(s)|⁴` for `re s ≥ 1 + η` and `|s| ≤ 3 e^l / 2`, if `χ²` is not principal or
`|s - 1| ≥ 1 / l`. -/
lemma pow_three_le_mul_norm_regularL_pow (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) {η : ℝ} (hη : 0 < η) (hη_le : η ≤ 1)
    (h_far : χ ^ 2 = 1 → 1 / l ≤ ‖s - 1‖) (h_re : 1 + η ≤ s.re)
    (h_norm : ‖s‖ ≤ 3 / 2 * rexp l) :
    η ^ 3 ≤ 256 * l ^ 7 * ‖regularL χ s‖ ^ 4 := by
  have hl_one : 1 ≤ l := by linarith
  -- the three points are `re s`, `s` and `s₂ = re s + 2 i im s`
  let s₂ : ℂ := s + s.im * I
  have re_s₂ : s₂.re = s.re := by simp [s₂]
  have norm_s₂ : ‖s₂‖ ≤ 3 * rexp l := by
    have h_im : ‖s.im * I‖ ≤ ‖s‖ := by simpa using abs_im_le_norm s
    linarith [norm_add_le s (s.im * I)]
  have dist_s₂ : ‖s - 1‖ ≤ ‖s₂ - 1‖ := by
    have h_sq : ‖s₂ - 1‖ ^ 2 = ‖s - 1‖ ^ 2 + 3 * s.im ^ 2 := by
      have im_s₂ : s₂.im = 2 * s.im := by simp [s₂, two_mul]
      simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, re_s₂, im_s₂, one_im]
      ring
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith [sq_nonneg s.im])
  have product : 1 ≤ ‖LSeries ((1 : DirichletCharacter ℂ N) ·) s.re‖ ^ 3 * ‖LSeries (χ ·) s‖ ^ 4 *
      ‖LSeries ((χ ^ 2) ·) s₂‖ := by
    have at_re : (1 : ℂ) + (s.re - 1 : ℝ) = s.re := by simp
    have at_s : s.re + I * s.im = s := by rw [mul_comm, re_add_im]
    have at_s₂ : s.re + 2 * I * s.im = s₂ := by linear_combination at_s
    simpa only [at_re, at_s, at_s₂, norm_mul, norm_pow] using
      χ.norm_LSeries_product_ge_one (by linarith : 0 < s.re - 1) s.im
  have trivial_char_le : ‖LSeries ((1 : DirichletCharacter ℂ N) ·) s.re‖ ≤ 2 / η := calc
    _ ≤ 1 + 1 / η := norm_LSeries_char_le 1 (one_div_pos.2 hη) (by simpa using h_re)
    _ ≤ 1 / η + 1 / η := by linarith [one_le_one_div hη hη_le]
    _ = 2 / η := by ring
  have char_le : ‖LSeries (χ ·) s‖ ≤ 2 * l * ‖regularL χ s‖ :=
    norm_LSeries_le_mul_norm_regularL χ (by linarith) hl_one fun hχ ↦ h_far (by simp [hχ])
  have sq_char_le : ‖LSeries ((χ ^ 2) ·) s₂‖ ≤ 2 * l * l ^ 2 := by
    have h_far₂ : χ ^ 2 = 1 → 1 / l ≤ ‖s₂ - 1‖ := fun hχ ↦ (h_far hχ).trans dist_s₂
    have re_s₂_ge : 1 - 1 / l ≤ s₂.re := by linarith [one_div_pos.2 (one_pos.trans_le hl_one)]
    grw [norm_LSeries_le_mul_norm_regularL (χ ^ 2) (by linarith) hl_one h_far₂,
      norm_regularL_le_sq (χ ^ 2) hl hN re_s₂_ge norm_s₂]
  calc η ^ 3 ≤ η ^ 3 * ((2 / η) ^ 3 * (2 * l * ‖regularL χ s‖) ^ 4 * (2 * l * l ^ 2)) := by
        grw [← trivial_char_le, ← char_le, ← sq_char_le, ← product, mul_one]
    _ = 256 * l ^ 7 * ‖regularL χ s‖ ^ 4 := by field

/-- Let `l ≥ 10¹⁰` and `N ≤ e^l`; if `χ²` is principal, let `|𝖿_χ| ≥ 1 / l` within `1 / l` of `1`,
where `𝖿_χ = regularL χ` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal.
Then `|𝖿_χ(s)| ≥ 12 / l²²` for `re s ≥ 1 + l⁻²⁵` and `|s| ≤ 3 e^l / 2`. -/
lemma div_pow_le_norm_regularL (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖)
    (h_re : 1 + 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ 3 / 2 * rexp l) :
    12 / l ^ 22 ≤ ‖regularL χ s‖ := by
  have hl_one : 1 ≤ l := by linarith
  by_cases! h_far : χ ^ 2 = 1 → 1 / l ≤ ‖s - 1‖
  · -- if `χ²` is not principal or `s` is not near `1`, the 3-4-1 bound with `η = l⁻²⁵` applies
    have hη_le : 1 / l ^ 25 ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ hl_one) (by positivity)
    have h_const : 256 * 12 ^ 4 ≤ l ^ 6 := by linarith [le_self_pow₀ hl_one (by norm_num : 6 ≠ 0)]
    have h_mul : 256 * l ^ 7 * (12 / l ^ 22) ^ 4 ≤ 256 * l ^ 7 * ‖regularL χ s‖ ^ 4 := calc
      _ = 256 * 12 ^ 4 / l ^ 81 := by field
      _ ≤ l ^ 6 / l ^ 81 := by gcongr
      _ = (1 / l ^ 25) ^ 3 := by field
      _ ≤ _ := pow_three_le_mul_norm_regularL_pow χ hl hN (by positivity) hη_le h_far h_re h_norm
    exact le_of_pow_le_pow_left₀ four_ne_zero (norm_nonneg _)
      (le_of_mul_le_mul_left h_mul (by positivity))
  · obtain ⟨hχ, h_close⟩ : χ ^ 2 = 1 ∧ ‖s - 1‖ < 1 / l := h_far
    calc 12 / l ^ 22 ≤ l / l ^ 2 := by gcongr <;> linarith
      _ = 1 / l := by field
      _ ≤ ‖regularL χ s‖ := h_near hχ s h_close.le

/-- Let `l ≥ 10¹⁰` and `N ≤ e^l`; if `χ²` is principal, let `|𝖿_χ| ≥ 1 / l` within `1 / l` of `1`,
where `𝖿_χ = regularL χ` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal.
Then `𝖿_χ(s) ≠ 0` and `|𝖿_χ'(s) / 𝖿_χ(s)| ≤ l²⁵` for `re s ≥ 1 - l⁻²⁵` and `|s| ≤ e^l`. -/
lemma norm_logDeriv_regularL_le (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖)
    (h_re : 1 - 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ rexp l) :
    regularL χ s ≠ 0 ∧ ‖logDeriv (regularL χ) s‖ ≤ l ^ 25 := by
  -- Compare `s` with `v = s + 2 η`, `η = l⁻²⁵`: between them `𝖿_χ` changes by at most
  -- `2 l³ · 2 η = 4 / l²²`, and `|𝖿_χ(v)| ≥ 12 / l²²`.
  have exp_ge : l + 1 ≤ rexp l := add_one_le_exp l
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  let η : ℝ := 1 / l ^ 25
  have hη_pos : 0 < η := by positivity
  have hη_le : η ≤ 1 / l / 6 := calc
    1 / l ^ 25 ≤ 1 / l ^ 2 := by gcongr <;> linarith
    _ = 1 / l * (1 / l) := by ring
    _ ≤ 1 / l / 6 := by grw [div_eq_mul_one_div (1 / l) 6, ← inv_le]
  have bounds (z : ℂ) (hz : z ∈ closedBall s (2 * η)) :
      1 - 1 / l / 2 ≤ z.re ∧ ‖z‖ ≤ 2 * rexp l := by
    rw [mem_closedBall_iff_norm] at hz
    have h_dist : |z.re - s.re| ≤ ‖z - s‖ := by simpa using abs_re_le_norm (z - s)
    exact ⟨by linarith [(abs_le.1 h_dist).1], by linarith [norm_le_norm_sub_add z s]⟩
  have deriv_le (z : ℂ) (hz : z ∈ closedBall s (2 * η)) : ‖deriv (regularL χ) z‖ ≤ 2 * l ^ 3 :=
    norm_deriv_regularL_le χ hl hN (bounds z hz).1 (bounds z hz).2
  have hs_mem : s ∈ closedBall s (2 * η) := mem_closedBall_self (by positivity)
  let v : ℂ := s + (2 * η : ℝ)
  have dist_v : ‖v - s‖ = 2 * η := by simp [v, hη_pos.le]
  have re_v : v.re = s.re + 2 * η := by simp [v]
  have change_le : ‖regularL χ v - regularL χ s‖ ≤ 4 / l ^ 22 := calc
    _ ≤ 2 * l ^ 3 * ‖v - s‖ :=
      (convex_closedBall s (2 * η)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz ↦ differentiableAt_regularL χ (by linarith [(bounds z hz).1])) deriv_le hs_mem
        (mem_closedBall_iff_norm.2 dist_v.le)
    _ = 4 / l ^ 22 := by
      rw [dist_v]
      field
  have large_v : 12 / l ^ 22 ≤ ‖regularL χ v‖ :=
    div_pow_le_norm_regularL χ hl hN h_near (by linarith) (by linarith [norm_le_norm_sub_add v s])
  have large_s : 8 / l ^ 22 ≤ ‖regularL χ s‖ := calc
    _ = 12 / l ^ 22 - 4 / l ^ 22 := by ring
    _ ≤ ‖regularL χ s‖ := by linarith [norm_sub_norm_le (regularL χ v) (regularL χ s)]
  refine ⟨norm_pos_iff.1 (lt_of_lt_of_le (by positivity) large_s), ?_⟩
  calc ‖logDeriv (regularL χ) s‖ ≤ 2 * l ^ 3 / (8 / l ^ 22) := by
        grw [logDeriv_apply, norm_div, deriv_le s hs_mem, ← large_s]
    _ = l ^ 25 / 4 := by field
    _ ≤ l ^ 25 := div_le_self (by positivity) (by norm_num)

/-- Let `χ` be a Dirichlet character mod `N ≥ 1`, `l ≥ 10¹⁰` and `N ≤ e^l`. If `χ²` is principal,
assume `|regularL χ z| ≥ 1 / l` whenever `|z - 1| ≤ 1 / l`, where `regularL χ` is `L(s, χ)` times
`(s - 1) / s` if `χ` is principal and `L(s, χ)` otherwise. Then for `re s ≥ 1 - l⁻²⁵` and
`|s| ≤ e^l`, the entire function `entireL χ` (equal to `L(s, χ)`, or to the continuation of
`(s - 1) L(s, χ)` if `χ` is principal) does not vanish at `s`, and its logarithmic derivative there
has norm at most `2 l²⁵`. -/
lemma norm_logDeriv_entireL_le (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}
    (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l)
    (h_near : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖)
    (h_re : 1 - 1 / l ^ 25 ≤ s.re) (h_norm : ‖s‖ ≤ rexp l) :
    entireL χ s ≠ 0 ∧ ‖logDeriv (entireL χ) s‖ ≤ 2 * l ^ 25 := by
  have two_le : 2 ≤ l ^ 25 := by
    linarith [le_self_pow₀ (by linarith : 1 ≤ l) (by norm_num : 25 ≠ 0)]
  obtain ⟨h_ne, h_bound⟩ := norm_logDeriv_regularL_le χ hl hN h_near h_re h_norm
  -- `regularL χ` is `entireL χ` divided by the factor `u`, which is `s` or `1`
  let u (z : ℂ) : ℂ := if χ = 1 then z else 1
  have h_eq : regularL χ = fun z : ℂ ↦ entireL χ z / u z := by
    ext z
    by_cases hχ : χ = 1 <;> simp [regularL, u, hχ]
  obtain ⟨h_entire, hu⟩ : entireL χ s ≠ 0 ∧ u s ≠ 0 := by rwa [h_eq, div_ne_zero_iff] at h_ne
  have u_diff : DifferentiableAt ℂ u s := by by_cases hχ : χ = 1 <;> simp [u, hχ]
  have h_split : logDeriv (entireL χ) s = logDeriv (regularL χ) s + logDeriv u s := by
    have h_div : logDeriv (fun z : ℂ ↦ entireL χ z / u z) s =
        logDeriv (entireL χ) s - logDeriv u s :=
      logDeriv_div s h_entire hu (analyticAt_entireL χ s).differentiableAt u_diff
    rw [h_eq, h_div, sub_add_cancel]
  have u_bound : ‖logDeriv u s‖ ≤ 2 := by
    have hs_norm : 1 / 2 ≤ ‖s‖ := by
      linarith [re_le_norm s, one_div_le_one_div_of_le two_pos two_le]
    by_cases hχ : χ = 1
    · simpa [u, hχ] using (one_div_le (by linarith) two_pos).2 hs_norm
    · simp [u, hχ]
  refine ⟨h_entire, ?_⟩
  rw [h_split]
  linarith [norm_add_le (logDeriv (regularL χ) s) (logDeriv u s)]

/-- **Zero-free region** for a fixed character: for all large `l`, on `re s ≥ 1 - l⁻²⁵`,
`|s| ≤ e^l` the function `entireL χ` (`L(s, χ)` with the pole removed) does not vanish and its
logarithmic derivative is at most `2 l²⁵`. -/
theorem eventually_norm_logDeriv_entireL_le (χ : DirichletCharacter ℂ N) :
    ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ 25 ≤ s.re → ‖s‖ ≤ rexp l →
      entireL χ s ≠ 0 ∧ ‖logDeriv (entireL χ) s‖ ≤ 2 * l ^ 25 := by
  have inv_tendsto : Tendsto (fun l : ℝ ↦ 1 / l) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_ge_atTop (10 ^ 10), eventually_ge_atTop (N : ℝ),
    inv_tendsto.eventually (eventually_le_norm_regularL χ)] with l hl hN h_near s
  exact norm_logDeriv_entireL_le χ hl (by linarith [add_one_le_exp l]) fun _ ↦ h_near

end New
