module

public import Mathlib.NumberTheory.Padics.Complex
public import Lib.CM.Sigma.Basic
public import Lib.CM.Sigma.ThetaSections
public import Lib.General.Algebra.AdicCompletion
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PiTensorProduct
import Lib.CM.GoodReduction
public import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.Completeness
import TauCeti.RingTheory.PowerSeries.Rescale
import TauCeti.RingTheory.PowerSeries.Substitution
public import Lib.General.Algebra.IntegralPowerSeries

section
section
/-!
# Doubling formulas for θ and σ and the quartic forms of doubling

The file expresses `θ(2 z)` and `σ(2 z) ^ 2` in `θ(z)` and `σ(z)`. The quartic forms of doubling,
`doublingForms c`, are defined over any commutative ring; over `ℂ` with `c = a₁`, their values at
`(θ², σ²)` are the square of the formula for `θ(2 z)` and the formula for `σ(2 z) ^ 2`. These facts
serve to prove that doubling raises the naive height to the fourth power; see
`Lib.CM.Integrality.TorsionValues`.

Notions from other files:
* `C : CMLattice d`: a lattice `Λ = C.Λ` in `ℂ` with a point `t = C.t` of order two modulo `Λ`,
  scaled so that `℘''(t) = 2`, and a square root `a₁ = C.a₁` of `12 ℘(t)`.
* `C.σ`, `C.θ`: the sigma function of `Λ`, and its twisted translate by `t` normalised to `1` at
  `0`; the zeros of `θ` are the `z` with `z + t ∈ Λ`.
* `C.translatedX`: the function `x(z) = ℘(z + t) - ℘(t)`, equal to `σ² / θ²` off `t + Λ`.
* `C.twistedTranslate m y`: the translation `T_y` by `y`, twisted by the exponential factor of
  degree `m`.

## Main definitions and results

* `New.doublingForms c`: the pair of quartic forms of doubling.
* `New.CMLattice.sigma_two_mul_eq`: `σ(2 z) = x' θ ^ 4` off `t + Λ`.
* `New.CMLattice.theta_two_mul`, `New.CMLattice.sigma_two_mul_sq`: `θ(2 z)` and `σ(2 z) ^ 2` as
  polynomials in `θ` and `σ`.
* `New.norm_doublingForms`: if `c` is integral and `c ^ 4 - 64` is a unit, the forms raise the
  maximum norm of a pair to the fourth power.

## Relation to the literature

Known result: the duplication formulas for theta and sigma functions. Source: DLMF, Chapters 20 and
23.

Known result: good reduction of the duplication map on the `x`-coordinate of an elliptic curve.
Source: Silverman, *The Arithmetic of Dynamical Systems* (GTM 241, Springer, 2007), Chapters 2 and
6.
-/

@[expose] public section

/-!
## Doubling formulas for θ and σ

The formula `θ(2 z) = θ ^ 4 - σ ^ 4` is the addition formula for `θ` on the diagonal. The formula
`σ(2 z) = x' θ ^ 4` is the duplication formula of `σ` at `z + t`; it uses that the number
`c₀ = (T_t σ)(0)` is a fourth root of unity.
-/

section Doubling

open Complex ComplexConjugate PeriodPair

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d)

/-- For a CM lattice with point `t` of order two, the number `c₀ = (T_t σ)(0)` is nonzero. -/
lemma twistedTranslate_t_sigma_zero_ne_zero : C.twistedTranslate 1 C.t C.σ 0 ≠ 0 := by
  simp [thetaShift_apply, C.t_notMem]

/-- The identity `T_t σ = c₀ θ` with `c₀ = (T_t σ)(0)`, with the exponential factor of the twisted
translation `T_t` written out. -/
lemma sigma_add_t (z : ℂ) :
    C.σ (z + C.t) = exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) *
      (C.twistedTranslate 1 C.t C.σ 0 * C.θ z) := by
  rw [θ, mul_div_cancel₀ _ C.twistedTranslate_t_sigma_zero_ne_zero, twistedTranslate,
    thetaShift_apply_apply, one_smul, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- The identity `c₀ T_t θ = -σ` with `c₀ = (T_t σ)(0)`, with the exponential factor of the twisted
translation `T_t` written out. -/
lemma theta_add_t (z : ℂ) :
    C.twistedTranslate 1 C.t C.σ 0 * C.θ (z + C.t) =
      -exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) * C.σ z := by
  have h_exponent : -(C.hermitianForm C.t (z + C.t) + C.hermitianForm C.t C.t / 2) +
      (2 * C.hermitianForm C.t z + 2 * C.hermitianForm C.t C.t) =
      C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2 := by
    simp only [map_add]
    ring
  rw [θ, mul_div_cancel₀ _ C.twistedTranslate_t_sigma_zero_ne_zero, twistedTranslate,
    thetaShift_apply_apply, one_smul, add_assoc z, C.sigma_add_two_t, ← h_exponent]
  simp only [exp_add]
  ring

/-- For a CM lattice `C` with point `t` of order two, the number `c₀ = (T_t σ)(0)` is a fourth root
of unity: `c₀ ^ 4 = 1`. Here `T_t` is the twisted translation of degree `1` by `t`, so
`c₀ = exp(−π |t|² / (2A)) σ(t)`, where `A` is the area of `Λ`. -/
lemma twistedTranslate_t_sigma_zero_pow_four : C.twistedTranslate 1 C.t C.σ 0 ^ 4 = 1 := by
  -- Translation by `t` turns `x θ² = σ²` into `x(z + t) σ² = c₀ ^ 4 θ²`, so that
  -- `c₀ ^ 4 = x(z) x(z + t) = 1`. We take `z = t / 2`.
  set c₀ : ℂ := C.twistedTranslate 1 C.t C.σ 0
  let z : ℂ := C.t / 2
  have hz : z ∉ C.Λ := fun h ↦ C.t_notMem (by simpa only [z, add_halves] using add_mem h h)
  have hzt : z + C.t ∉ C.Λ := fun h ↦ C.t_notMem <| by
    have ht : C.t = z + C.t + (z + C.t) - (C.t + C.t) := by
      simp only [z]
      ring
    rw [ht]
    exact sub_mem (add_mem h h) C.two_t_mem
  have hztt : z + C.t + C.t ∉ C.Λ := by rwa [add_assoc, add_mem_cancel_right C.two_t_mem]
  set e : ℂ := exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2)
  have h_translate : C.translatedX (z + C.t) * C.σ z ^ 2 = c₀ ^ 4 * C.θ z ^ 2 := by
    have h_sq : C.σ (z + C.t) ^ 2 = C.translatedX (z + C.t) * C.θ (z + C.t) ^ 2 :=
      C.sigma_sq_eq_translatedX_mul_theta_sq hztt
    have hσ : C.σ (z + C.t) = e * (c₀ * C.θ z) := C.sigma_add_t z
    have hθ : c₀ * C.θ (z + C.t) = -e * C.σ z := C.theta_add_t z
    refine mul_left_cancel₀ (pow_ne_zero 2 (exp_ne_zero _ : e ≠ 0)) ?_
    calc e ^ 2 * (C.translatedX (z + C.t) * C.σ z ^ 2)
        = C.translatedX (z + C.t) * (-e * C.σ z) ^ 2 := by ring
      _ = c₀ ^ 2 * (C.translatedX (z + C.t) * C.θ (z + C.t) ^ 2) := by
        rw [← hθ]
        ring
      _ = e ^ 2 * (c₀ ^ 4 * C.θ z ^ 2) := by
        rw [← h_sq, hσ]
        ring
  have hθ_ne : C.θ z ≠ 0 := mt C.theta_eq_zero_iff.1 hzt
  refine mul_right_cancel₀ (pow_ne_zero 2 hθ_ne) ?_
  calc c₀ ^ 4 * C.θ z ^ 2 = C.translatedX z * C.translatedX (z + C.t) * C.θ z ^ 2 := by
        rw [← h_translate, C.sigma_sq_eq_translatedX_mul_theta_sq hzt]
        ring
    _ = 1 * C.θ z ^ 2 := by rw [C.translatedX_mul_translatedX_add_t hz hzt]

/-- Doubling for the normalised twisted translate `θ` of the sigma function `σ` of `C`:
`θ(2 z) = θ(z) ^ 4 - σ(z) ^ 4`. -/
lemma theta_two_mul (z : ℂ) : C.θ (2 * z) = C.θ z ^ 4 - C.σ z ^ 4 := by
  -- Both sides are entire. Off `t + Λ` this is the addition formula for `θ` at `(z, z)`, with
  -- `x θ² = σ²`.
  revert z
  refine C.eq_of_eq_off_lattice C.t (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  have h_add : C.θ (z + z) * C.θ (z - z) =
      C.θ z ^ 2 * (C.θ z ^ 2 - C.translatedX z * C.σ z ^ 2) :=
    C.theta_add_mul_theta_sub hz z
  have hσ : C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := C.sigma_sq_eq_translatedX_mul_theta_sq hz
  rw [sub_self, theta_zero, mul_one, ← two_mul] at h_add
  linear_combination h_add + C.σ z ^ 2 * hσ

/-- Doubling for the sigma function `σ` of `C`: `σ(2 z) = x'(z) θ(z) ^ 4` away from the poles
`t + Λ` of `x(z) = ℘(z + t) - ℘(t)`, where `θ` is the normalised twisted translate of `σ` by `t`. -/
lemma sigma_two_mul_eq {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    C.σ (2 * z) = deriv C.translatedX z * C.θ z ^ 4 := by
  -- This is the duplication formula `σ(2 w) = -℘'(w) σ(w) ^ 4` at `w = z + t`. The exponential
  -- factors cancel, the period `2 t` gives a sign, and `c₀ ^ 4 = 1` for `c₀ = (T_t σ)(0)`.
  set e : ℂ := exp (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2)
  have h_period : C.σ (2 * (z + C.t)) = -e ^ 4 * C.σ (2 * z) := by
    have h_exponent : 2 * C.hermitianForm C.t (2 * z) + 2 * C.hermitianForm C.t C.t =
        (4 : ℕ) * (C.hermitianForm C.t z + C.hermitianForm C.t C.t / 2) := by
      rw [two_mul z, map_add]
      push_cast
      ring
    rw [mul_add, two_mul C.t, C.sigma_add_two_t, h_exponent, exp_natCast_mul]
  have h_fourth : C.σ (z + C.t) ^ 4 = e ^ 4 * C.θ z ^ 4 := by
    rw [C.sigma_add_t, mul_pow, mul_pow, C.twistedTranslate_t_sigma_zero_pow_four, one_mul]
  have h_deriv : deriv C.translatedX z = ℘'[C.periodPair] (z + C.t) := by
    rw [deriv_translatedX, translatedY]
    ring
  have h_double : C.σ (2 * (z + C.t)) = -℘'[C.periodPair] (z + C.t) * C.σ (z + C.t) ^ 4 :=
    sigma_two_mul C.periodPair hz
  rw [h_period, h_fourth, ← h_deriv] at h_double
  refine mul_left_cancel₀ (pow_ne_zero 4 (exp_ne_zero _ : e ≠ 0)) ?_
  linear_combination -h_double

/-- Doubling for the sigma function `σ` of `C`, in terms of `σ` and its normalised twisted translate
`θ` by `t`: `σ(2 z)² = θ² σ² (4 θ ^ 4 + a₁² θ² σ² + 4 σ ^ 4)` at `z`. -/
lemma sigma_two_mul_sq (z : ℂ) :
    C.σ (2 * z) ^ 2 = C.θ z ^ 2 * C.σ z ^ 2 *
      (4 * C.θ z ^ 4 + C.a₁ ^ 2 * C.θ z ^ 2 * C.σ z ^ 2 + 4 * C.σ z ^ 4) := by
  -- Both sides are entire, so it suffices to compare them off `t + Λ`.
  revert z
  refine C.eq_of_eq_off_lattice C.t (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  have hσ : C.σ z ^ 2 = C.translatedX z * C.θ z ^ 2 := C.sigma_sq_eq_translatedX_mul_theta_sq hz
  rw [C.sigma_two_mul_eq hz, mul_pow, C.deriv_translatedX_sq hz, hσ, pow_mul (C.σ z) 2 2, hσ]
  ring

end New.CMLattice

end Doubling

/-!
## The quartic forms of doubling over ℂ_p

If `c` is integral and `c ^ 4 - 64` is a unit, the two forms are not both of norm less than `1` at
a pair of norm `1`: combinations of `w₀² - w₁²` and the second form with integral coefficients are
`(c ^ 4 - 64) w₀ ^ 5` and `(c ^ 4 - 64) w₁ ^ 5`.
-/

section DoublingForms

namespace New

section Forms
variable {R : Type*} [CommRing R]

/-- The pair of quartic forms `B₀ = (w₀² - w₁²)²` and `B₁ = w₀ w₁ (4 w₀² + c² w₀ w₁ + 4 w₁²)` at
`w = (w₀, w₁)`. -/
def doublingForms (c : R) (w : R × R) : R × R :=
  ((w.1 ^ 2 - w.2 ^ 2) ^ 2, w.1 * w.2 * (4 * w.1 ^ 2 + c ^ 2 * w.1 * w.2 + 4 * w.2 ^ 2))

/-- The forms `doublingForms c` are homogeneous of degree `4`. -/
lemma doublingForms_smul (c a : R) (w : R × R) :
    doublingForms c (a • w) = a ^ 4 • doublingForms c w := by
  ext <;> simp only [doublingForms, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

end Forms

variable {p : ℕ} [Fact p.Prime]

/-- If `c ∈ ℂ_p` is integral and `c ^ 4 - 64` is a unit, the quartic forms `doublingForms c` take
pairs of maximum norm `1` to pairs of maximum norm `1`. -/
lemma norm_doublingForms_eq_one {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1)
    {w : ℂ_[p] × ℂ_[p]} (hw : ‖w‖ = 1) : ‖doublingForms c w‖ = 1 := by
  have hc_mem : c ∈ valRingCp p := hc
  -- If `u`, `v` are integral and `u² - v²` and the second form at `(u, v)` have norm less than
  -- `1`, so has `u`: a combination of the two with integral coefficients is `(c ^ 4 - 64) u ^ 5`.
  have h_small {u v : ℂ_[p]} (hu : u ∈ valRingCp p) (hv : v ∈ valRingCp p)
      (h₀ : ‖u ^ 2 - v ^ 2‖ < 1)
      (h₁ : ‖u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)‖ < 1) : ‖u‖ < 1 := by
    let x : ℂ_[p] := c ^ 2 * u - 8 * v
    let y : ℂ_[p] := (x * (c ^ 2 * u + 4 * v) - 64 * u ^ 2) * u
    have hcu : c ^ 2 * u ∈ valRingCp p := mul_mem (pow_mem hc_mem 2) hu
    have hx : x ∈ valRingCp p := sub_mem hcu (mul_mem (ofNat_mem _ 8) hv)
    have hy : y ∈ valRingCp p :=
      mul_mem (sub_mem (mul_mem hx (add_mem hcu (mul_mem (ofNat_mem _ 4) hv)))
        (mul_mem (ofNat_mem _ 64) (pow_mem hu 2))) hu
    have h_eq : (c ^ 4 - 64) * u ^ 5 =
        x * (u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)) + y * (u ^ 2 - v ^ 2) := by
      simp only [x, y]
      ring
    have h_lt : ‖(c ^ 4 - 64) * u ^ 5‖ < 1 := by
      rw [h_eq]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · exact (norm_mul _ _).trans_lt ((mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt h₁)
      · exact (norm_mul _ _).trans_lt ((mul_le_of_le_one_left (norm_nonneg _) hy).trans_lt h₀)
    rw [norm_mul, h_disc, one_mul, norm_pow] at h_lt
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg u) (by norm_num)).1 h_lt
  obtain ⟨u, v⟩ := w
  have hu : u ∈ valRingCp p := (norm_fst_le (u, v)).trans hw.le
  have hv : v ∈ valRingCp p := (norm_snd_le (u, v)).trans hw.le
  refine le_antisymm (max_le ?_ ?_) (not_lt.1 fun h_lt ↦ ?_)
  · exact pow_mem (sub_mem (pow_mem hu 2) (pow_mem hv 2)) 2
  · exact mul_mem (mul_mem hu hv) (add_mem (add_mem (mul_mem (ofNat_mem _ 4) (pow_mem hu 2))
      (mul_mem (mul_mem (pow_mem hc_mem 2) hu) hv)) (mul_mem (ofNat_mem _ 4) (pow_mem hv 2)))
  -- Otherwise both coordinates of the pair have norm less than `1`.
  · obtain ⟨h₀, h₁⟩ : ‖(u ^ 2 - v ^ 2) ^ 2‖ < 1 ∧
        ‖u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)‖ < 1 := max_lt_iff.1 h_lt
    rw [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h₀
    have hu_lt : ‖u‖ < 1 := h_small hu hv h₀ h₁
    have hv_lt : ‖v‖ < 1 := h_small hv hu (by rwa [norm_sub_rev]) (by
      rwa [show v * u * (4 * v ^ 2 + c ^ 2 * v * u + 4 * u ^ 2) =
        u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2) by ring])
    exact (max_lt hu_lt hv_lt).ne hw

/-- If `c ∈ ℂ_p` is integral and `c ^ 4 - 64` is a unit, the quartic forms `doublingForms c` raise
the maximum norm of a pair to the fourth power. -/
lemma norm_doublingForms {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1)
    (w : ℂ_[p] × ℂ_[p]) : ‖doublingForms c w‖ = ‖w‖ ^ 4 := by
  -- By homogeneity, divide by the coordinate of larger norm.
  obtain ⟨a, ha⟩ : ∃ a : ℂ_[p], ‖w‖ = ‖a‖ :=
    (max_choice ‖w.1‖ ‖w.2‖).elim (fun h ↦ ⟨w.1, h⟩) (fun h ↦ ⟨w.2, h⟩)
  obtain rfl | ha_ne := eq_or_ne a 0
  · obtain rfl : w = 0 := by simpa using ha
    simp [doublingForms]
  · have h_unit : ‖a⁻¹ • w‖ = 1 := by simp [norm_smul, ha, ha_ne]
    calc ‖doublingForms c w‖ = ‖doublingForms c (a • a⁻¹ • w)‖ := by rw [smul_inv_smul₀ ha_ne]
      _ = ‖a‖ ^ 4 * ‖doublingForms c (a⁻¹ • w)‖ := by rw [doublingForms_smul, norm_smul, norm_pow]
      _ = ‖w‖ ^ 4 := by rw [norm_doublingForms_eq_one hc h_disc h_unit, mul_one, ha]

end New

end DoublingForms
end
end

/-!
# Integrality of values of sections at torsion points

The file defines the value `torsionValue` at a point of a function with a degree `n` (the function
value times an exponential factor that depends on `n`), which is used for sections at torsion
points, and the property `HasIntegralValues`. For a prime `d ≡ 7 (mod 8)` the file shows that `a₁`
is integral and that monomials in `θ`, `σ²` and the section `translatedYThetaCube` have integral
torsion values. Here `translatedYThetaCube` is `y θ³`, where `y` is the coordinate `translatedY` in
the cubic `y² + a₁ x y = x³ + x`.

The proof uses the naive height `h(w) = max (|σ(w)|_p, |θ(w)|_p)` of a complex number `w`. Because
`a₁ ^ 4 - 64` is a unit, doubling raises the height to the fourth power exactly. From this the file
proves the height comparison: the height of a pull-back along an isogeny of degree `N` is at most
the `N`-th power of the height, and a twisted translation by a torsion point does not increase the
height. At `0` the height is `1`, which gives the integrality of torsion values.

Notions from other files:
* `CMLattice d`: a lattice `Λ` with a point `t` of order two in `ℂ / Λ` and a coefficient `a₁` of
  its cubic. For `d ≠ 0` the lattice has complex multiplication by the integers of `ℚ(√-d)`.
* `σ` and `θ`: the sigma function of `Λ`, normalised so that twisted translation by a period
  multiplies it by a sign, and the theta function that vanishes exactly on `-t + Λ`.
* `twistedTranslate n v G`: the translate of a function `G` by `v`, multiplied by the `n`-th power
  of the exponential factor `exp (-(H(v, z) + H(v, v) / 2))`, where `H(l, z) = (π / area Λ) l̄ z` is
  the Hermitian form.
* `C.sections m`: the sections of degree `m`, spanned by the monomials `monomialSection` in `θ`,
  `σ²` and `translatedYThetaCube`.
* `ιₚ`: the fixed embedding of `ℂ` into `ℂ_p` (`PadicPlace p`); integral means of norm at most `1`,
  that is, lying in `valRingCp p`, the set of elements of `ℂ_p` of norm at most `1`.

## Main definitions and results

* `New.CMLattice.torsionValue`, `New.CMLattice.HasIntegralValues`: the torsion value `G[u]` and the
  property that all of these are integral at torsion points.
* `New.CMLattice.norm_a₁_le_one`: `a₁` is integral, because `a₁ ^ 4 - 64` is a unit.
* `New.CMLattice.naiveHeight`, `New.CMLattice.naiveHeight_two_mul`: the height `h`, and
  `h(2 w) = h(w) ^ 4`.
* `New.CMLattice.naiveHeight_mul_le`, `New.CMLattice.translateHeight_le_naiveHeight`: the height
  comparison for an isogeny and for a translation by a torsion point.
* `New.CMLattice.norm_twistedTranslate_mul_le`: if `|g|_p ≤ h' ^ m` on `ℂ`, then the twisted
  translate of `g` by a torsion point, pulled back along an isogeny of degree `N`, is at most
  `h ^ (m N)`.
* `New.CMLattice.hasIntegralValues_monomialSection`: monomials have integral torsion values.

## Relation to the literature

Known result: the Weber invariants of discriminant `-d` with `d ≡ 7 mod 8` are integral. Source:
Birch, *Weber's class invariants*.

Known result: the integrality of Siegel functions at torsion points. Source: Kubert and Lang,
*Modular Units*.
-/

@[expose] public section

/-! ## Integrality of the coefficient `a₁` -/

namespace New.CMLattice

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime]

/-- If `g ^ 2 + u g = v` in `ℂ_p` with `‖u‖ ≤ c` and `‖v‖ ≤ c ^ 2`, then `‖g‖ ≤ c`: a root of a
monic quadratic whose coefficients are bounded by `c` and `c ^ 2` is bounded by `c`. -/
lemma norm_le_of_sq_add_mul_eq {g u v : ℂ_[p]} {c : ℝ} (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c ^ 2)
    (hg : g ^ 2 + u * g = v) : ‖g‖ ≤ c := by
  by_contra! h_lt
  have hc : 0 ≤ c := (norm_nonneg u).trans hu
  have h_eq : g ^ 2 = u * -g + v := by linear_combination hg
  have h_sq : ‖g‖ ^ 2 ≤ c * ‖g‖ := calc
    ‖g‖ ^ 2 = ‖u * -g + v‖ := by rw [← norm_pow, h_eq]
    _ ≤ max (‖u‖ * ‖g‖) ‖v‖ := by grw [IsUltrametricDist.norm_add_le_max, norm_mul, norm_neg]
    _ ≤ max (c * ‖g‖) (c ^ 2) := by gcongr
    _ = c * ‖g‖ := max_eq_left (by nlinarith)
  nlinarith

/-- For a prime `d ≡ 7 (mod 8)` the coefficient `a₁` of the cubic of a CM lattice is integral in
`ℂ_p`. -/
lemma norm_a₁_le_one [PadicPlace p] : ‖ιₚ C.a₁‖ ≤ 1 := by
  -- `a₁ ^ 4 = (a₁ ^ 4 - 64) + 64` is a sum of two integral elements.
  have h_pow : ιₚ C.a₁ ^ 4 - 64 + 64 ∈ valRingCp p :=
    add_mem (mem_valRingCp.2 (C.norm_disc_eq_one ιₚ).le) (ofNat_mem _ 64)
  rwa [sub_add_cancel, mem_valRingCp, norm_pow,
    pow_le_one_iff_of_nonneg (norm_nonneg _) four_ne_zero] at h_pow

end New.CMLattice

/-!
## Torsion values

The torsion value of a function with a degree, and its rules for powers and pull-backs.
-/

section TorsionValues

open Complex ComplexConjugate
open scoped Real

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d)

/-- `u` lies in `ℚ Λ`, that is, it represents a torsion point of `ℂ / Λ`. -/
def IsTorsion (u : ℂ) : Prop := ∃ n : ℕ, n ≠ 0 ∧ n * u ∈ C.Λ

/-- The torsion value `G[u]` of a function `G` with the degree `n`: the value at `0` of the twisted
translate of `G` by `u` for `n` times the Hermitian form of the lattice. -/
noncomputable def torsionValue (n : ℕ) (G : ℂ → ℂ) (u : ℂ) : ℂ := C.twistedTranslate n u G 0

/-- The torsion value of `G` at `u` is `G(u) exp (-n π |u|² / (2 area Λ))`. -/
lemma torsionValue_eq (n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue n G u = G u * exp (-(π * ‖u‖ ^ 2 / (2 * C.area))) ^ n := by
  have h_exponent : -((n • C.hermitianForm) u u / 2) = n * -(π * ‖u‖ ^ 2 / (2 * C.area)) := by
    change -(n • C.hermitianForm u u / 2) = _
    rw [nsmul_eq_mul, hermitianForm_apply, mul_conj']
    ring
  simp only [torsionValue, thetaShift_apply, zero_add, neg_zero, add_zero, map_zero,
    ← exp_natCast_mul, ← h_exponent, mul_comm (G u)]

lemma torsionValue_pow (k n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue (k * n) (G ^ k) u = C.torsionValue n G u ^ k := by
  simp only [torsionValue_eq, Pi.pow_apply]
  ring

/-- Pull-backs: if `z ↦ a z` is an isogeny of degree `N` from the lattice of `C` to that of `C'`,
then with the degree `n N` the function `G(a z)` has at `u` the torsion value `G[a u]`. -/
lemma torsionValue_comp_isogeny {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h : C.IsIsogeny C'.periodPair a N) (n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue (n * N) (fun z : ℂ ↦ G (a * z)) u = C'.torsionValue n G (a * u) := by
  simp only [torsionValue, C.twistedTranslate_comp_isogeny h, mul_zero]

variable {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- The torsion values of `G` with the degree `n` are all integral in `ℂ_p`: for every torsion
point `u`, the image of `G[u]` under `ιₚ` has norm at most `1`. -/
def HasIntegralValues (n : ℕ) (G : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, C.IsTorsion u → ‖ιₚ (C.torsionValue n G u)‖ ≤ 1

end New.CMLattice

end TorsionValues

namespace New

/-- A bounded real `r` with some value at least `r z ^ 2` whenever `r z > 1` is at most `1`. -/
lemma le_one_of_forall_exists_sq_le {α : Type*} {r : α → ℝ} {K : ℝ} (h_bdd : ∀ z : α, r z ≤ K)
    (h_sq : ∀ z : α, 1 < r z → ∃ z' : α, r z ^ 2 ≤ r z') (z : α) : r z ≤ 1 := by
  by_contra! h_lt
  have h_iterate (k : ℕ) : ∃ z' : α, r z ^ 2 ^ k ≤ r z' := by
    induction k with
    | zero => exact ⟨z, by simp⟩
    | succ k ih =>
      obtain ⟨z₁, h₁⟩ := ih
      obtain ⟨z₂, h₂⟩ := h_sq z₁ ((one_lt_pow₀ h_lt (by positivity)).trans_le h₁)
      refine ⟨z₂, le_trans ?_ h₂⟩
      rw [pow_succ, pow_mul]
      exact pow_le_pow_left₀ (by positivity) h₁ 2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, K < r z ^ n := pow_unbounded_of_one_lt K h_lt
  obtain ⟨z', hz'⟩ := h_iterate n
  have h_exp : r z ^ n ≤ r z ^ 2 ^ n := pow_le_pow_right₀ h_lt.le Nat.lt_two_pow_self.le
  exact (hn.trans_le (h_exp.trans hz')).not_ge (h_bdd z')

end New

/-!
## The naive height

The height `h(w) = max (|σ(w)|_p, |θ(w)|_p)` is positive, and `h(2 w) = h(w) ^ 4` by the doubling
formulas. The monomials of degree `m` are at most `h ^ m`, so every section of degree `m` is at
most a constant times `h ^ m`.
-/

section NaiveHeight

open Complex

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- The naive height `h(w) = max (‖ιₚ (σ w)‖, ‖ιₚ (θ w)‖)` of a complex number `w`. -/
noncomputable def naiveHeight (w : ℂ) : ℝ := max ‖ιₚ (C.σ w)‖ ‖ιₚ (C.θ w)‖

/-- The value of `σ` is at most the naive height. -/
lemma norm_sigma_le_naiveHeight (w : ℂ) : ‖ιₚ (C.σ w)‖ ≤ C.naiveHeight w := le_max_left _ _

/-- The value of `θ` is at most the naive height. -/
lemma norm_theta_le_naiveHeight (w : ℂ) : ‖ιₚ (C.θ w)‖ ≤ C.naiveHeight w := le_max_right _ _

/-- The naive height is positive, because `σ` and `θ` have no common zero: `t ∉ Λ`. -/
lemma naiveHeight_pos (w : ℂ) : 0 < C.naiveHeight w := by
  by_cases hw : w ∈ C.Λ
  · have hθ : C.θ w ≠ 0 := fun h ↦
      C.t_notMem ((add_mem_cancel_left hw).1 (C.theta_eq_zero_iff.1 h))
    exact lt_max_of_lt_right (by simpa using hθ)
  · have hσ : C.σ w ≠ 0 := mt sigma_eq_zero_iff.1 hw
    exact lt_max_of_lt_left (by simpa using hσ)

variable [PrimeSevenModEight d]

/-- Doubling raises the naive height to the fourth power: `h(2 w) = h(w) ^ 4`. -/
lemma naiveHeight_two_mul (w : ℂ) : C.naiveHeight (2 * w) = C.naiveHeight w ^ 4 := by
  -- Doubling acts on the pair `(θ², σ²)` through the quartic forms `doublingForms`, which raise
  -- the norm of a pair to the fourth power; the norm of the pair is the square of the height.
  let v : ℂ → ℂ_[p] × ℂ_[p] := fun z : ℂ ↦ (ιₚ (C.θ z) ^ 2, ιₚ (C.σ z) ^ 2)
  have h_norm (z : ℂ) : ‖v z‖ = C.naiveHeight z ^ 2 := by
    simp only [v, Prod.norm_mk, norm_pow, naiveHeight, max_comm ‖ιₚ (C.σ z)‖]
    exact (pow_left_monotoneOn.map_max (norm_nonneg _) (norm_nonneg _)).symm
  have h_double : v (2 * w) = doublingForms (ιₚ C.a₁) (v w) := by
    ext
    · simp only [v, doublingForms, C.theta_two_mul w, map_sub, map_pow, ← pow_mul]
    · simpa only [v, doublingForms, map_mul, map_add, map_pow, map_ofNat, ← pow_mul]
        using congrArg ιₚ (C.sigma_two_mul_sq w)
  have h_sq : C.naiveHeight (2 * w) ^ 2 = (C.naiveHeight w ^ 4) ^ 2 := by
    rw [← h_norm, h_double, norm_doublingForms C.norm_a₁_le_one (C.norm_disc_eq_one ιₚ), h_norm]
    ring
  exact (sq_eq_sq₀ (C.naiveHeight_pos _).le (pow_pos (C.naiveHeight_pos w) 4).le).1 h_sq

/-- The section `y θ³` (`translatedYThetaCube`) is at most `h ^ 3`. -/
lemma norm_translatedYThetaCube_le (w : ℂ) :
    ‖ιₚ (C.translatedYThetaCube w)‖ ≤ C.naiveHeight w ^ 3 := by
  have hσ : ‖ιₚ (C.σ w)‖ ≤ C.naiveHeight w := C.norm_sigma_le_naiveHeight w
  have hθ : ‖ιₚ (C.θ w)‖ ≤ C.naiveHeight w := C.norm_theta_le_naiveHeight w
  have h_pos : 0 < C.naiveHeight w := C.naiveHeight_pos w
  have h_linear : ‖ιₚ C.a₁ * ιₚ (C.σ w) ^ 2 * ιₚ (C.θ w)‖ ≤ C.naiveHeight w ^ 3 := by
    grw [norm_mul, norm_mul, norm_pow, C.norm_a₁_le_one, hσ, hθ, one_mul, ← pow_succ]
  have h_const :
      ‖ιₚ (C.σ w) ^ 6 + ιₚ (C.σ w) ^ 2 * ιₚ (C.θ w) ^ 4‖ ≤ (C.naiveHeight w ^ 3) ^ 2 := by
    grw [IsUltrametricDist.norm_add_le_max, norm_mul, norm_pow, norm_pow, norm_pow, hσ, hθ,
      ← pow_add, max_self, ← pow_mul]
  exact norm_le_of_sq_add_mul_eq h_linear h_const <| by
    simpa only [map_add, map_mul, map_pow] using congrArg ιₚ (C.translatedYThetaCube_sq_add w)

/-- The monomial `θ^a (σ²)^b G^c` (`monomialSection`) is at most `h ^ (a + 2b + 3c)`. -/
lemma norm_monomialSection_le (x : ℕ × ℕ × ℕ) (w : ℂ) :
    ‖ιₚ (C.monomialSection x w)‖ ≤ C.naiveHeight w ^ monomialDeg x := by
  obtain ⟨a, b, c⟩ := x
  have hσ : ‖ιₚ (C.σ w)‖ ≤ C.naiveHeight w := C.norm_sigma_le_naiveHeight w
  have hθ : ‖ιₚ (C.θ w)‖ ≤ C.naiveHeight w := C.norm_theta_le_naiveHeight w
  have hG : ‖ιₚ (C.translatedYThetaCube w)‖ ≤ C.naiveHeight w ^ 3 :=
    C.norm_translatedYThetaCube_le w
  have h_pos : 0 < C.naiveHeight w := C.naiveHeight_pos w
  simp only [monomialSection, monomialDeg, Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, norm_mul,
    norm_pow, pow_add, pow_mul', mul_assoc]
  gcongr

/-- A section `g` of degree `m` is at most a constant times `h ^ m`. -/
lemma exists_norm_le_mul_naiveHeight_pow {m : ℕ} {g : ℂ → ℂ} (hg : g ∈ C.sections m) :
    ∃ K : ℝ, ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ K * C.naiveHeight w ^ m := by
  refine Submodule.span_induction ?_ ⟨0, by simp⟩ ?_ ?_ (C.sections_le_span_monomialSection m hg)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨1, fun w ↦ by simpa only [one_mul, ← hx.2] using C.norm_monomialSection_le x w⟩
  · rintro f₁ f₂ - - ⟨K₁, h₁⟩ ⟨K₂, h₂⟩
    refine ⟨max K₁ K₂, fun w ↦ ?_⟩
    calc ‖ιₚ ((f₁ + f₂) w)‖ ≤ max ‖ιₚ (f₁ w)‖ ‖ιₚ (f₂ w)‖ := by
          rw [Pi.add_apply, map_add]
          exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (K₁ * C.naiveHeight w ^ m) (K₂ * C.naiveHeight w ^ m) := max_le_max (h₁ w) (h₂ w)
      _ = max K₁ K₂ * C.naiveHeight w ^ m :=
          (max_mul_of_nonneg _ _ (pow_pos (C.naiveHeight_pos w) m).le).symm
  · rintro c f - ⟨K, hK⟩
    refine ⟨‖ιₚ c‖ * K, fun w ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK w) (norm_nonneg _)

/-- If `g ^ e` (`e ≠ 0`) is a section of degree `e m`, `g` is at most a constant times `h ^ m`. -/
lemma exists_norm_le_of_pow_mem_sections {e m : ℕ} (he : e ≠ 0) {g : ℂ → ℂ}
    (hg : g ^ e ∈ C.sections (e * m)) :
    ∃ K : ℝ, ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ K * C.naiveHeight w ^ m := by
  obtain ⟨K, hK⟩ := C.exists_norm_le_mul_naiveHeight_pow (p := p) hg
  -- Replace the constant `K` by `max 1 K`, which is at most its own `e`-th power.
  refine ⟨max 1 K, fun w ↦ ?_⟩
  have h_pos : 0 < C.naiveHeight w := C.naiveHeight_pos w
  have h_pow : ‖ιₚ (g w)‖ ^ e ≤ (max 1 K * C.naiveHeight w ^ m) ^ e := calc
    ‖ιₚ (g w)‖ ^ e = ‖ιₚ ((g ^ e) w)‖ := by rw [Pi.pow_apply, map_pow, norm_pow]
    _ ≤ K * C.naiveHeight w ^ (e * m) := hK w
    _ ≤ max 1 K ^ e * C.naiveHeight w ^ (e * m) := by
      gcongr
      exact (le_max_right 1 K).trans (le_self_pow₀ (le_max_left 1 K) he)
    _ = (max 1 K * C.naiveHeight w ^ m) ^ e := by rw [mul_pow, ← pow_mul, mul_comm e m]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) he).1 h_pow

end New.CMLattice

end NaiveHeight

/-!
## Height comparison

Let `r` be the ratio of the height of a pull-back, or of a translate, to the bound that is claimed
for it. The ratio is bounded, because powers of the functions involved are sections. Doubling
raises the height to the fourth power, which gives `r(z) ^ 4 = r(2 z)` for a pull-back and
`r(z) ^ 4 = r(2 z + y) r(2 z)` for the translation by `y`. A bounded function with such a law is
at most `1`.
-/

section HeightComparison

open Complex

namespace New.CMLattice
variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- An isogeny `z ↦ a z` of degree `N` from `C` to `C'` satisfies `h'(a z) ≤ h(z) ^ N`. -/
lemma naiveHeight_mul_le {C' : CMLattice d} {a : ℂ} {N : ℕ} (h : C.IsIsogeny C'.periodPair a N)
    (z : ℂ) : C'.naiveHeight (p := p) (a * z) ≤ C.naiveHeight z ^ N := by
  -- The pull-backs of `σ'²` and `θ'` are sections of degrees `2 N` and `N`, so the ratio
  -- `r(z) = h'(a z) / h(z) ^ N` is bounded.
  have hσ_mem : (fun z : ℂ ↦ C'.σ (a * z) ^ 2) ∈ C.sections (2 * N) := by
    simpa [monomialSection] using C.comp_mul_mem_sections h (C'.monomialSection_mem (0, 1, 0))
  have hθ_mem : (fun z : ℂ ↦ C'.θ (a * z)) ^ 1 ∈ C.sections (1 * N) := by
    simpa only [pow_one] using C.comp_mul_mem_sections h C'.theta_mem
  obtain ⟨K₁, h₁⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) two_ne_zero
    (g := fun z : ℂ ↦ C'.σ (a * z)) hσ_mem
  obtain ⟨K₂, h₂⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) one_ne_zero hθ_mem
  let r : ℂ → ℝ := fun z : ℂ ↦ C'.naiveHeight (a * z) / C.naiveHeight z ^ N
  have h_pos (z : ℂ) : 0 < C.naiveHeight z ^ N := pow_pos (C.naiveHeight_pos z) N
  have h_bdd (z : ℂ) : r z ≤ max K₁ K₂ := by
    rw [div_le_iff₀ (h_pos z), max_mul_of_nonneg _ _ (h_pos z).le]
    exact max_le_max (h₁ z) (h₂ z)
  -- Doubling raises both heights to the fourth power.
  have h_four (z : ℂ) : r z ^ 4 = r (2 * z) := by
    simp only [r]
    rw [div_pow, ← C'.naiveHeight_two_mul, ← pow_mul, mul_comm N 4, pow_mul,
      ← C.naiveHeight_two_mul, mul_left_comm]
  refine (div_le_one (h_pos z)).1 (le_one_of_forall_exists_sq_le h_bdd (fun z hz ↦ ⟨2 * z, ?_⟩) z)
  rw [← h_four]
  exact pow_le_pow_right₀ hz.le (by norm_num)

/-- Height of the twisted translate by `y`: `h(w + y)` times the norm of its exponential factor. -/
noncomputable def translateHeight (y w : ℂ) : ℝ :=
  ‖ιₚ (exp (-(C.hermitianForm y w + C.hermitianForm y y / 2)))‖ * C.naiveHeight (w + y)

omit [PrimeSevenModEight d] in
/-- The degree `m` twisted translate is the translate times `exp (-(H(y, w) + H(y, y) / 2)) ^ m`. -/
lemma twistedTranslate_eq_exp_pow_mul (m : ℕ) (y : ℂ) (g : ℂ → ℂ) (w : ℂ) :
    C.twistedTranslate m y g w =
      exp (-(C.hermitianForm y w + C.hermitianForm y y / 2)) ^ m * g (w + y) := by
  rw [twistedTranslate, thetaShift_apply_apply, ← exp_natCast_mul]
  simp [mul_add, mul_div_assoc]

omit [PrimeSevenModEight d] in
/-- If `g` is at most `h ^ m`, its degree `m` twisted translate is at most `translateHeight ^ m`. -/
lemma norm_twistedTranslate_le_translateHeight_pow {m : ℕ} {g : ℂ → ℂ}
    (hg : ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ C.naiveHeight w ^ m) (y w : ℂ) :
    ‖ιₚ (C.twistedTranslate m y g w)‖ ≤ C.translateHeight y w ^ m := by
  rw [C.twistedTranslate_eq_exp_pow_mul, map_mul, map_pow, norm_mul, norm_pow, translateHeight,
    mul_pow]
  exact mul_le_mul_of_nonneg_left (hg _) (by positivity)

/-- The height `k` of the translate by `y` satisfies `k(w) ^ 4 h(2 w + y) = k(2 w + y) k(2 w)`. -/
lemma translateHeight_pow_four_mul (y w : ℂ) :
    C.translateHeight y w ^ 4 * C.naiveHeight (2 * w + y) =
      C.translateHeight (p := p) y (2 * w + y) * C.translateHeight y (2 * w) := by
  have h_factor : exp (-(C.hermitianForm y w + C.hermitianForm y y / 2)) ^ 4 =
      exp (-(C.hermitianForm y (2 * w + y) + C.hermitianForm y y / 2)) *
        exp (-(C.hermitianForm y (2 * w) + C.hermitianForm y y / 2)) := by
    rw [← exp_natCast_mul, ← exp_add]
    simp only [hermitianForm_apply]
    ring_nf
  simp only [translateHeight]
  rw [mul_pow, ← norm_pow, ← map_pow, h_factor, map_mul, norm_mul, ← C.naiveHeight_two_mul,
    mul_add 2 w y, two_mul y, ← add_assoc]
  ring

/-- For a torsion point `y`, the height of the translate by `y` is at most the naive height. -/
lemma translateHeight_le_naiveHeight {y : ℂ} (hy : C.IsTorsion y) (w : ℂ) :
    C.translateHeight (p := p) y w ≤ C.naiveHeight w := by
  obtain ⟨n, hn, hny⟩ := hy
  -- If `f ^ (2 n)` is a section of degree `2 n`, so is the `2 n`-th power of the twisted translate
  -- of `f` by `y`, because `2 n y` lies in the lattice. This holds for `f = σ` and `f = θ`.
  have h_mem {f : ℂ → ℂ} (hf : f ^ (n * 2) ∈ C.sections (n * 2)) :
      C.twistedTranslate 1 y f ^ (n * 2) ∈ C.sections (n * 2 * 1) := by
    have h_lattice : (n * 2) • y ∈ C.Λ := by
      have h_two : (n * 2) • y = 2 • ((n : ℂ) * y) := by
        simp only [nsmul_eq_mul]
        push_cast
        ring
      exact h_two ▸ nsmul_mem hny 2
    have h_dual : y ∈ ((n * 2) • C.hermitianForm).dualLattice :=
      ThetaTori.mem_dualLattice_nsmul.2 (C.isAppellHumbert_multiplier.le_dualLattice h_lattice)
    rw [mul_one, twistedTranslate, one_smul, ← thetaShift_pow]
    exact (C.isAppellHumbert_multiplier.nsmul (n * 2)).thetaShift_mem_of_mem_dualLattice h_dual hf
  have hσ_mem : C.σ ^ (n * 2) ∈ C.sections (n * 2) := by
    simpa [monomialSection, ← pow_mul, mul_comm 2 n] using C.monomialSection_mem (0, n, 0)
  have hθ_mem : C.θ ^ (n * 2) ∈ C.sections (n * 2) := by
    simpa [monomialSection] using C.monomialSection_mem (n * 2, 0, 0)
  have h_ne : n * 2 ≠ 0 := mul_ne_zero hn two_ne_zero
  obtain ⟨K₁, h₁⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) h_ne (h_mem hσ_mem)
  obtain ⟨K₂, h₂⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) h_ne (h_mem hθ_mem)
  -- So the ratio `r(z) = k(z) / h(z)` is bounded, where `k` is the height of the translate.
  let r : ℂ → ℝ := fun z : ℂ ↦ C.translateHeight y z / C.naiveHeight z
  have h_pos (z : ℂ) : 0 < C.naiveHeight z := C.naiveHeight_pos z
  have hr_nonneg (z : ℂ) : 0 ≤ r z :=
    div_nonneg (mul_nonneg (norm_nonneg _) (h_pos _).le) (h_pos z).le
  have h_bdd (z : ℂ) : r z ≤ max K₁ K₂ := by
    rw [div_le_iff₀ (h_pos z), max_mul_of_nonneg _ _ (h_pos z).le, translateHeight, naiveHeight,
      mul_max_of_nonneg _ _ (norm_nonneg _), ← norm_mul, ← norm_mul, ← map_mul, ← map_mul]
    simpa only [C.twistedTranslate_eq_exp_pow_mul, pow_one] using max_le_max (h₁ z) (h₂ z)
  -- Doubling gives `r(z) ^ 4 = r(2 z + y) r(2 z)`.
  have h_four (z : ℂ) : r z ^ 4 = r (2 * z + y) * r (2 * z) := by
    simp only [r]
    rw [div_pow, ← C.naiveHeight_two_mul, div_mul_div_comm, div_eq_div_iff (h_pos _).ne'
      (mul_pos (h_pos _) (h_pos _)).ne', ← C.translateHeight_pow_four_mul]
    ring
  refine (div_le_one (h_pos w)).1 (le_one_of_forall_exists_sq_le h_bdd (fun z hz ↦ ?_) w)
  -- One of the two factors of `r(z) ^ 4` is at least `r(z) ^ 2`.
  by_contra! h_lt
  have h_mul : r (2 * z + y) * r (2 * z) < r z ^ 2 * r z ^ 2 :=
    mul_lt_mul'' (h_lt _) (h_lt _) (hr_nonneg _) (hr_nonneg _)
  rw [← h_four, ← pow_add] at h_mul
  exact lt_irrefl _ h_mul

/-- If `g ≤ h' ^ m`, a torsion translate of `g` along an isogeny of degree `N` is `≤ h ^ (m N)`. -/
theorem norm_twistedTranslate_mul_le {C' : CMLattice d} {a : ℂ} {N m : ℕ}
    (h : C.IsIsogeny C'.periodPair a N) {y : ℂ} (hy : C'.IsTorsion y) {g : ℂ → ℂ}
    (hg : ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ C'.naiveHeight w ^ m) (z : ℂ) :
    ‖ιₚ (C'.twistedTranslate m y g (a * z))‖ ≤ C.naiveHeight z ^ (m * N) := by
  have h_nonneg : 0 ≤ C'.translateHeight (p := p) y (a * z) :=
    mul_nonneg (norm_nonneg _) (C'.naiveHeight_pos _).le
  calc ‖ιₚ (C'.twistedTranslate m y g (a * z))‖
      ≤ C'.translateHeight y (a * z) ^ m := C'.norm_twistedTranslate_le_translateHeight_pow hg y _
    _ ≤ C'.naiveHeight (a * z) ^ m :=
        pow_le_pow_left₀ h_nonneg (C'.translateHeight_le_naiveHeight hy _) m
    _ ≤ (C.naiveHeight z ^ N) ^ m :=
        pow_le_pow_left₀ (C'.naiveHeight_pos _).le (C.naiveHeight_mul_le h z) m
    _ = C.naiveHeight z ^ (m * N) := by rw [← pow_mul, mul_comm]

end New.CMLattice

end HeightComparison

/-! ## Integral torsion values of monomials -/

namespace New.CMLattice
variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- For `d` a prime `≡ 7 (mod 8)` and a `p`-adic place `ιₚ`, take a triple `(a, b, c)` and the
monomial `θ^a (σ²)^b G^c` (`monomialSection`), a section of degree `a + 2b + 3c`. Here `σ` is the
sigma function of the lattice and `G = translatedYThetaCube` is the entire function equal to `y θ³`
off `t + Λ`. For every torsion point `u`, the torsion value of this monomial in degree `a + 2b + 3c`
at `u` has `ιₚ`-image of norm at most `1`. -/
lemma hasIntegralValues_monomialSection (x : ℕ × ℕ × ℕ) :
    C.HasIntegralValues (p := p) (monomialDeg x) (C.monomialSection x) := by
  -- The torsion value is the value at `0` of the twisted translate, and the height of `0` is `1`.
  intro u hu
  have h_zero : C.naiveHeight (p := p) 0 = 1 := by simp [naiveHeight, theta_zero]
  calc ‖ιₚ (C.torsionValue (monomialDeg x) (C.monomialSection x) u)‖
      ≤ C.translateHeight u 0 ^ monomialDeg x :=
        C.norm_twistedTranslate_le_translateHeight_pow (C.norm_monomialSection_le x) u 0
    _ ≤ C.naiveHeight 0 ^ monomialDeg x :=
        pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (C.naiveHeight_pos _).le)
          (C.translateHeight_le_naiveHeight hu 0) _
    _ = 1 := by rw [h_zero, one_pow]

end New.CMLattice
end
end

/-!
# Integral series rings 𝔬[[T]], congruence parts of power series, a functional equation

Let `𝔬` (`New.valRingCp p`) be the valuation ring of `ℂ_[p]`, and let `𝔬[[X]]` be the range of the
inclusion `New.seriesToCp` into `ℂ_[p]⟦X⟧`. For a series `T = X + ⋯`, the file studies the ring
`𝔬[[T]]` of integral series in `T`. For the coordinate `y` of a CM curve, it shows that `𝔬[[y]]`
contains `x` and is stable under `d/dz`. It then treats the part of a series in the degrees of one
class mod `m`, and the integrality of the solutions of a functional equation `Y(π z) = π G(Y)`.

## Main definitions and results

* `New.IsSeriesGenerator A T`: the series `T = X + ⋯` generates `A`, that is, `A = 𝔬[[T]]`. Such a
  ring is closed under integral scalars. It is closed under `f ↦ f(a X)` when it contains `T(a X)`.
  Its elements whose constant term has norm `1` are invertible. Any series `f = X + ⋯` in `A`
  generates it too (`New.IsSeriesGenerator.of_mem`).
* `New.CMLattice.integralSeriesRing C`: the ring `𝔬[[y]]`. Here `y` (`New.CMLattice.translatedY`)
  and `x` (`New.CMLattice.translatedX`) are the coordinates of the CM curve `y² + a₁ x y = x³ + x`.
  `New.taylorVia ιₚ f` is the Taylor series of `f` at `0` with the p-adic place `ιₚ : ℂ →+* ℂ_[p]`
  applied to the coefficients.
* `New.CMLattice.taylorVia_translatedX_mem_integralSeriesRing`,
  `New.CMLattice.derivative_mem_integralSeriesRing`: `𝔬[[y]]` contains `x` and is stable under
  `d/dz`.
* `New.congruencePart_eq_sum`: for `m ≠ 0`, the part of a series in the degrees of one class mod `m`
  is a mean over the `m`-th roots of unity; `New.congruencePart_subst`: taking it commutes with the
  substitution of a series `T` with `T(0) = 0` that has only degrees `≡ 1` mod `m`.
* `New.exists_seriesToCp_eq_of_rescale_eq`: for `0 < |π| < 1`, `q > 1` and `E` integral of order at
  least two, a solution `Y = z + ⋯` of `Y(π z) / π = Y - Y ^ q + π E(Y)` is integral, by induction
  on the degree (`New.mem_range_seriesToCp_of_rescale_eq_X_sub_X_pow`), and `Y - Y ^ q ≡ z` modulo
  `π` (`New.C_dvd_sub_pow_sub_X_of_rescale_eq`).
* `New.dvd_coeff_sub_of_C_dvd_sub_pow_sub_X`: let `π` be a non-unit dividing `p` and `q > 1` a power
  of `p`. If `Y(0) = 0` and `Y - Y ^ q ≡ z` modulo `π`, then `Y ≡ ∑ z ^ q ^ j` modulo `π`.

Notions from other files:
* `New.CMLattice d`: a lattice `Λ` stable under the integers of `ℚ(√-d)`, with a point `t` of order
  two modulo `Λ` such that `ω t`, `ω̄ t ∉ Λ` for `ω = (1 + √-d) / 2`, scaled so that `℘''(t) = 2`,
  and a square root `a₁` of `12 ℘(t)`.
* `New.PrimeSevenModEight d`: the number `d` is a prime congruent to `7` modulo `8`.

## Relation to the literature

Known result: elementary facts on power series; the induction is that of the functional equation of
a Lubin–Tate group. Source: Lubin–Tate, Formal complex multiplication in local fields.

The statements on the CM curve use only that `a₁` is integral; `x ∈ 𝔬[[y]]` is Hensel's lemma for
the cubic.
-/

@[expose] public section

/-! ## Rings of integral series in a generating parameter -/

section IntegralParameter

open PowerSeries WithPiTopology

namespace New

variable {p : ℕ} [Fact p.Prime]

lemma seriesToCp_eq_map (g : (valRingCp p)⟦X⟧) :
    seriesToCp g = PowerSeries.map (valRingCp p).subtype g := rfl

lemma coeff_seriesToCp (n : ℕ) (g : (valRingCp p)⟦X⟧) :
    coeff n (seriesToCp g) = (coeff n g : valRingCp p) := rfl

lemma constantCoeff_seriesToCp (g : (valRingCp p)⟦X⟧) :
    constantCoeff (seriesToCp g) = (constantCoeff g : valRingCp p) := rfl

lemma derivative_seriesToCp (g : (valRingCp p)⟦X⟧) :
    d⁄dX (seriesToCp g) = seriesToCp (d⁄dX g) :=
  (map_pderiv (valRingCp p).subtype () g).symm

/-- The series `T = X + ⋯` generates the subring `A` of `ℂ_[p]⟦X⟧`: `A = 𝔬[[T]]` consists exactly
of the `g(T)` with `g` a series over the valuation ring `𝔬` of `ℂ_[p]`. -/
structure IsSeriesGenerator (A : Subring ℂ_[p]⟦X⟧) (T : ℂ_[p]⟦X⟧) : Prop where
  /-- The constant term of `T` is `0`. -/
  constantCoeff_eq_zero : constantCoeff T = 0
  /-- The linear coefficient of `T` is `1`. -/
  coeff_one : coeff 1 T = 1
  /-- The elements of `A` are the series `g(T)` with `g` integral. -/
  mem_iff (f : ℂ_[p]⟦X⟧) : f ∈ A ↔ ∃ g : (valRingCp p)⟦X⟧, f = subst T (seriesToCp g)

/-- The series `f(T)` and `f` have the same constant term, if `T(0) = 0`. -/
@[simp]
lemma constantCoeff_subst_eq {T : ℂ_[p]⟦X⟧} (hT₀ : T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧} :
    constantCoeff (f.subst T) = f.constantCoeff :=
  PowerSeries.constantCoeff_subst_of_constantCoeff_zero hT₀ f

/-- Substituting `a X` in `f(T)` gives `f(T(a X))`, if `T(0) = 0`. -/
lemma rescale_subst {a : ℂ_[p]} {T : ℂ_[p]⟦X⟧} (hT₀ : T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧} :
    rescale a (f.subst T) = f.subst (rescale a T) := by
  rw [rescale_eq_subst, rescale_eq_subst,
    subst_comp_subst_apply (.of_constantCoeff_zero' hT₀) (.of_constantCoeff_zero' (by simp))]

/-- For integral series `F`, `G` and a series `T` with `F(0) = T(0) = 0`, the composite `G ∘ F`
formed over `𝔬` satisfies `(G ∘ F)(T) = G(F(T))`. -/
lemma subst_seriesToCp_subst {T : ℂ_[p]⟦X⟧} (hT₀ : constantCoeff T = 0) {F : (valRingCp p)⟦X⟧}
    (hF₀ : constantCoeff F = 0) (G : (valRingCp p)⟦X⟧) :
    subst T (seriesToCp (subst F G)) = subst (subst T (seriesToCp F)) (seriesToCp G) := by
  rw [map_subst (.of_constantCoeff_zero' hF₀), ← seriesToCp_eq_map, subst_comp_subst_apply
    (.of_constantCoeff_zero' (by simp [constantCoeff_seriesToCp, hF₀]))
    (.of_constantCoeff_zero' hT₀)]

/-- If `T` may be substituted into series, the substitution `f ↦ f(T)` is continuous for the
topology of coefficientwise convergence. -/
@[fun_prop]
lemma continuous_subst {T : ℂ_[p]⟦X⟧} (hT : HasSubst T) :
    Continuous (subst T : ℂ_[p]⟦X⟧ → ℂ_[p]⟦X⟧) :=
  continuous_id.powerSeries_subst continuous_const fun _ ↦ isNilpotent_iff_eq_zero.mp hT

namespace IsSeriesGenerator

variable {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧}

/-! ### Properties of `𝔬[[T]]` -/

/-- Let `B = 𝔬[[T]]`, with `𝔬` the valuation ring of `ℂ_[p]`. The generator `T` has a
compositional inverse `Z`, and `f ∈ B` exactly when `f(Z)` has integral coefficients. -/
lemma exists_subst_inverse (hB : IsSeriesGenerator B T) :
    ∃ Z : ℂ_[p]⟦X⟧,
      constantCoeff Z = 0 ∧
      subst Z T = X ∧
      subst T Z = X ∧
      ∀ {f : ℂ_[p]⟦X⟧}, f ∈ B ↔ subst Z f ∈ seriesToCp.range := by
  -- `Z` is the compositional inverse of `T`, so `f = g(T)` if and only if `f(Z) = g`.
  have h_unit : IsUnit (coeff 1 T) := by simp [hB.coeff_one]
  let Z : ℂ_[p]⟦X⟧ := T.substInvOfIsUnit h_unit
  have hZT : subst Z T = X := subst_substInvOfIsUnit_right T hB.constantCoeff_eq_zero h_unit
  have hTZ : subst T Z = X := subst_substInvOfIsUnit_left T hB.constantCoeff_eq_zero h_unit
  have hT : HasSubst T := .of_constantCoeff_zero' hB.constantCoeff_eq_zero
  have hZ : HasSubst Z := .of_constantCoeff_zero' (by simp [Z])
  refine ⟨Z, by simp [Z], hZT, hTZ, fun {f} ↦
    (hB.mem_iff f).trans (exists_congr fun g ↦ ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩)⟩
  · rw [hg, subst_comp_subst_apply hT hZ, hZT, X_subst]
  · rw [hg, subst_comp_subst_apply hZ hT, hTZ, X_subst]

lemma generator_mem (hB : IsSeriesGenerator B T) : T ∈ B := by
  exact (hB.mem_iff T).2
    ⟨X, by simp [seriesToCp_eq_map, subst_X (.of_constantCoeff_zero' hB.constantCoeff_eq_zero)]⟩

/-- Let `B = 𝔬[[T]]` be the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`. If
`c` has norm at most one and `f ∈ B`, then `c • f ∈ B`. -/
lemma smul_mem (hB : IsSeriesGenerator B T) {c : ℂ_[p]} {f : ℂ_[p]⟦X⟧} (hc : ‖c‖ ≤ 1)
    (hf : f ∈ B) : c • f ∈ B := by
  -- After substituting the inverse `Z` of `T`, membership is a norm bound on each coefficient.
  obtain ⟨Z, hZ₀, -, -, h_mem⟩ := hB.exists_subst_inverse
  rw [h_mem, mem_range_seriesToCp] at hf ⊢
  intro n
  rw [subst_smul (.of_constantCoeff_zero' hZ₀), coeff_smul, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hf n)

lemma norm_coeff_one_le_one (hB : IsSeriesGenerator B T) {f : ℂ_[p]⟦X⟧} (hf : f ∈ B) :
    ‖f.coeff 1‖ ≤ 1 := by
  -- The linear coefficient of `f = g(T)` is that of the integral series `g`, as `T = X + ⋯`.
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  simpa [coeff_one_subst hB.constantCoeff_eq_zero, hB.coeff_one] using
    mem_range_seriesToCp.1 ⟨g, rfl⟩ 1

/-- Let `B = 𝔬[[T]]` be the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`. Any
`f = X + ⋯` in `B` generates the same ring: `𝔬[[f]] = B`. -/
lemma of_mem (hB : IsSeriesGenerator B T) {f : ℂ_[p]⟦X⟧} (hf : f ∈ B) (hf₀ : f.constantCoeff = 0)
    (hf₁ : f.coeff 1 = 1) : IsSeriesGenerator B f := by
  -- Write `f = F(T)` with `F` integral. As `T = X + ⋯`, also `F = X + ⋯`, so `F` has a
  -- compositional inverse over `𝔬` and substituting `F` is onto: every `G(T)` is some `G'(f)`.
  have hT₀ : constantCoeff T = 0 := hB.constantCoeff_eq_zero
  obtain ⟨F, rfl⟩ := (hB.mem_iff f).1 hf
  have hF₀ : constantCoeff F = 0 := by simpa [hT₀, constantCoeff_seriesToCp] using hf₀
  have hF₁ : coeff 1 F = 1 := by
    simpa [coeff_one_subst hT₀, hB.coeff_one, coeff_seriesToCp] using hf₁
  have h_surj : (subst F : (valRingCp p)⟦X⟧ → (valRingCp p)⟦X⟧).Surjective := fun G ↦
    ⟨subst (F.substInvOfIsUnit (by simp [hF₁])) G, by
      rw [subst_comp_subst_apply (.of_constantCoeff_zero' (by simp)) (.of_constantCoeff_zero' hF₀),
        subst_substInvOfIsUnit_left F hF₀, X_subst]⟩
  refine ⟨hf₀, hf₁, fun S ↦ ?_⟩
  rw [hB.mem_iff, h_surj.exists]
  simp only [subst_seriesToCp_subst hT₀ hF₀]

/-- An element of `B = 𝔬[[T]]`, the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`,
whose constant term has norm `1` is invertible in `B`. -/
lemma exists_mul_eq_one (hB : IsSeriesGenerator B T) {f : ℂ_[p]⟦X⟧} (hf : f ∈ B)
    (h_norm : ‖f.constantCoeff‖ = 1) : ∃ v ∈ B, f * v = 1 := by
  -- Write `f = g(T)`; the constant term of `g` is a unit of the valuation ring, so `g` is a unit.
  have hT₀ : constantCoeff T = 0 := hB.constantCoeff_eq_zero
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  have hg₀ : IsUnit (constantCoeff g) := by simpa [hT₀, constantCoeff_seriesToCp] using h_norm
  obtain ⟨v, hv : g * v = 1⟩ := (isUnit_iff_constantCoeff.2 hg₀).exists_right_inv
  refine ⟨subst T (seriesToCp v), (hB.mem_iff _).2 ⟨v, rfl⟩, ?_⟩
  simp [← coe_substAlgHom (.of_constantCoeff_zero' hT₀), ← map_mul, hv]

/-- Let `B = 𝔬[[T]]` be the ring of series in `T` over the valuation ring `𝔬` of `ℂ_[p]`. If
`T(a X)` lies in `B`, then `B` is stable under `f ↦ f(a X)`. -/
lemma rescale_mem (hB : IsSeriesGenerator B T) {a : ℂ_[p]} {f : ℂ_[p]⟦X⟧} (hT : rescale a T ∈ B)
    (hf : f ∈ B) : rescale a f ∈ B := by
  -- If `T(a X) = u(T)` and `f = g(T)`, then `f(a X) = (g ∘ u)(T)`.
  have hT₀ : constantCoeff T = 0 := hB.constantCoeff_eq_zero
  obtain ⟨u, hu⟩ := (hB.mem_iff _).1 hT
  obtain ⟨g, rfl⟩ := (hB.mem_iff f).1 hf
  have hu₀ : constantCoeff u = 0 := by
    simpa [hT₀, constantCoeff_seriesToCp] using (congrArg constantCoeff hu).symm
  refine (hB.mem_iff _).2 ⟨subst u g, ?_⟩
  rw [rescale_subst hT₀, hu, subst_seriesToCp_subst hT₀ hu₀]

end IsSeriesGenerator

namespace CMLattice

variable {d : ℕ} (C : CMLattice d) [PadicPlace p]

/-! ### The ring `𝔬[[y]]` of a CM curve -/

/-- The subring `𝔬[[y]]` of `ℂ_[p]⟦X⟧` of integral power series in the Taylor series of the
coordinate `y = C.translatedY`, with the `p`-adic place `ιₚ` applied to its coefficients. -/
noncomputable def integralSeriesRing : Subring ℂ_[p]⟦X⟧ :=
  ((substAlgHom (a := taylorVia ιₚ C.translatedY)
    (.of_constantCoeff_zero' (by simp))).toRingHom.comp (seriesToCp (p := p))).range

/-- The elements of `𝔬[[y]]` are the series `g(y)` with `g` integral. -/
lemma mem_integralSeriesRing {f : ℂ_[p]⟦X⟧} : f ∈ C.integralSeriesRing ↔
    ∃ g : (valRingCp p)⟦X⟧, f = subst (taylorVia ιₚ C.translatedY) (seriesToCp g) := by
  simp [integralSeriesRing, eq_comm, coe_substAlgHom]

/-- The Taylor series of `y = C.translatedY` in `ℂ_[p]⟦X⟧` begins with `X` and generates
`𝔬[[y]]`. -/
lemma isSeriesGenerator_translatedY :
    IsSeriesGenerator C.integralSeriesRing (taylorVia ιₚ C.translatedY) where
  constantCoeff_eq_zero := by simp
  coeff_one := by simp
  mem_iff _ := C.mem_integralSeriesRing

variable [PrimeSevenModEight d]

omit [PadicPlace p] in
/-- For `a` in the valuation ring `𝔬` of `ℂ_[p]`, the cubic `Y³ + (1 - a X) Y - X²` over `𝔬[[X]]`
has a root without constant term, by Hensel's lemma. -/
lemma _root_.New.exists_isRoot_cubic_constantCoeff_eq_zero (a : valRingCp p) :
    ∃ y : (valRingCp p)⟦X⟧,
      (⟨1, 0, 1 - .C a * X, -X * X⟩ : Cubic (valRingCp p)⟦X⟧).toPoly.IsRoot y ∧
      constantCoeff y = 0 := by
  set F : Cubic (valRingCp p)⟦X⟧ := ⟨1, 0, 1 - .C a * X, -X * X⟩ with hF
  have h_approx : F.toPoly.eval 0 ∈ Ideal.span {X} := by
    simp [hF, Cubic.toPoly, Ideal.mem_span_singleton]
  have h_simple : IsUnit (Ideal.Quotient.mk (Ideal.span {X}) (F.toPoly.derivative.eval 0)) := by
    simp [hF, Cubic.toPoly]
  obtain ⟨y, hy_root, hy_mem : y - 0 ∈ Ideal.span {X}⟩ :=
    HenselianRing.is_henselian F.toPoly Cubic.monic_of_a_eq_one' 0 h_approx h_simple
  exact ⟨y, hy_root, by simpa [Ideal.mem_span_singleton, X_dvd_iff] using hy_mem⟩

/-- For a `CMLattice` `C`, consisting of a lattice `Λ`, a point `t` of order two modulo `Λ` and `a₁`
with `a₁² = 12 ℘(t)`, let `x(z) = ℘(z + t) − ℘(t)` be `C.translatedX` and `y = C.translatedY` the
companion coordinate, with Taylor series `y = X + ⋯` and `y' = 1 + 3 x² - a₁ y`, so that `(x, y)`
lies on the CM curve `y² + a₁ x y = x³ + x`. Then the Taylor series of `x` at `z = 0`, with the
`p`-adic place `ιₚ` applied to its coefficients, lies in `C.integralSeriesRing`. That is, it is a
power series in the likewise expanded `y` with coefficients in the ring of integers `𝔬` of
`ℂ_[p]`. -/
lemma taylorVia_translatedX_mem_integralSeriesRing :
    taylorVia ιₚ C.translatedX ∈ C.integralSeriesRing := by
  -- The equation of the curve says that `x` is a root of `Y³ + (1 - a₁ y) Y - y²`. The cubic
  -- `Y³ + (1 - a₁ X) Y - X²` has a root `r` in `X 𝔬[[X]]`, and `r(y)` is the same root: over a
  -- local ring two roots that are congruent and simple modulo the maximal ideal agree.
  let a₁ : valRingCp p := ⟨ιₚ C.a₁, C.norm_a₁_le_one⟩
  let F : Cubic (valRingCp p)⟦X⟧ := ⟨1, 0, 1 - .C a₁ * X, -X * X⟩
  obtain ⟨r, hr_root : F.toPoly.IsRoot r, hr₀⟩ := exists_isRoot_cubic_constantCoeff_eq_zero a₁
  set y : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedY with hy
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX with hx
  have hy₀ : constantCoeff y = 0 := by simp [hy]
  have hy_subst : HasSubst y := .of_constantCoeff_zero' hy₀
  let Φ : (valRingCp p)⟦X⟧ →+* ℂ_[p]⟦X⟧ := (substAlgHom hy_subst).toRingHom.comp seriesToCp
  have hΦ (g : (valRingCp p)⟦X⟧) : Φ g = subst y (seriesToCp g) := by simp [Φ, coe_substAlgHom]
  have hΦr₀ : constantCoeff (Φ r) = 0 := by simp [hΦ, hy₀, constantCoeff_seriesToCp, hr₀]
  have h_map : F.toPoly.map Φ =
      Polynomial.X ^ 3 + .C (1 - .C (ιₚ C.a₁) * y) * Polynomial.X - .C (y * y) := by
    have hΦ_C : Φ (.C a₁) = .C (ιₚ C.a₁) := by
      rw [hΦ, seriesToCp_eq_map, map_C, subst_C]
      rfl
    have hΦ_X : Φ X = y := by rw [hΦ, seriesToCp_eq_map, map_X, subst_X hy_subst]
    simp [F, Cubic.toPoly, hΦ_X, hΦ_C, sub_eq_add_neg]
  have hx_root : (F.toPoly.map Φ).eval x = 0 := by
    have h_curve : x ^ 3 + (1 - .C (ιₚ C.a₁) * y) * x - y * y = 0 := by
      linear_combination -C.taylorVia_curve_eq ιₚ
    simpa [h_map] using h_curve
  have h_congr : ¬IsUnit (Φ r - x) := by simp [isUnit_iff_constantCoeff, hΦr₀, hx, translatedX]
  have h_simple : IsUnit ((F.toPoly.map Φ).derivative.eval (Φ r)) := by
    simp [h_map, isUnit_iff_constantCoeff, hΦr₀, hy₀]
  have h_eq : Φ r = x :=
    IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (hr_root.map Φ) hx_root h_congr h_simple
  exact C.mem_integralSeriesRing.2 ⟨r, by rw [← hΦ, h_eq]⟩

/-- For a `CMLattice` `C` (a lattice `Λ` with a point `t` of order two modulo `Λ`), let
`y = C.translatedY` be the `y`-coordinate of the CM curve `y² + a₁ x y = x³ + x`, where
`x(z) = ℘(z + t) − ℘(t)`. Expand `y` at `z = 0` and apply the `p`-adic place `ιₚ` to its
coefficients to get a series in `ℂ_[p]⟦X⟧`. The ring `C.integralSeriesRing` is the ring `𝔬[[y]]` of
power series in this `y` with coefficients in the ring of integers `𝔬` of `ℂ_[p]`. This ring is
stable under the derivative `d/dz`. -/
lemma derivative_mem_integralSeriesRing {f : ℂ_[p]⟦X⟧} (hf : f ∈ C.integralSeriesRing) :
    d⁄dX f ∈ C.integralSeriesRing := by
  obtain ⟨g, rfl⟩ := C.mem_integralSeriesRing.1 hf
  have hy := C.isSeriesGenerator_translatedY (p := p)
  -- Chain rule: `(g ∘ y)' = (g' ∘ y) y'` with `g'` integral and `y' = 1 + 3 x² - a₁ y`.
  rw [derivative_subst (.of_constantCoeff_zero' hy.constantCoeff_eq_zero), derivative_seriesToCp,
    derivative_taylorVia_translatedY, ← smul_eq_C_mul]
  refine mul_mem (C.mem_integralSeriesRing.2 ⟨d⁄dX g, rfl⟩) (sub_mem ?_ ?_)
  · exact add_mem (one_mem _)
      (mul_mem (ofNat_mem _ 3) (pow_mem C.taylorVia_translatedX_mem_integralSeriesRing 2))
  · exact hy.smul_mem C.norm_a₁_le_one hy.generator_mem

end CMLattice

end New

end IntegralParameter

/-! ## Congruence parts and integral solutions of a functional equation -/

section SeriesParts

open PowerSeries Finset

namespace New

variable {p : ℕ} [Fact p.Prime] {m r n : ℕ} {f T : ℂ_[p]⟦X⟧}

lemma seriesToCp_injective : Function.Injective (seriesToCp : (valRingCp p)⟦X⟧ → ℂ_[p]⟦X⟧) :=
  map_injective (valRingCp p).subtype Subtype.coe_injective

/-- The part of `f` in degrees `≡ r` mod `m`. -/
noncomputable def congruencePart (m r : ℕ) (f : ℂ_[p]⟦X⟧) : ℂ_[p]⟦X⟧ :=
  mk fun n ↦ if n ≡ r [MOD m] then f.coeff n else 0

lemma coeff_congruencePart (f : ℂ_[p]⟦X⟧) :
    coeff n (congruencePart m r f) = if n ≡ r [MOD m] then coeff n f else 0 := coeff_mk n _

lemma congruencePart_congruencePart (f : ℂ_[p]⟦X⟧) :
    congruencePart m r (congruencePart m r f) = congruencePart m r f := by
  ext n
  simp +contextual [coeff_congruencePart]

/-- The substitution `f ↦ f(a X)` commutes with taking the part in degrees `≡ r` mod `m`. -/
lemma congruencePart_rescale (a : ℂ_[p]) (f : ℂ_[p]⟦X⟧) :
    congruencePart m r (rescale a f) = rescale a (congruencePart m r f) := by
  ext n
  simp [coeff_congruencePart, coeff_rescale]

/-- If `ζ ^ m = 1`, then replacing `X` by `ζ X` multiplies the part of a series in degrees `≡ r`
mod `m` by `ζ ^ r`. -/
lemma rescale_congruencePart_of_pow_eq_one {ζ : ℂ_[p]} (hζ : ζ ^ m = 1) (r : ℕ) (f : ℂ_[p]⟦X⟧) :
    rescale ζ (congruencePart m r f) = ζ ^ r • congruencePart m r f := by
  ext n
  simp +contextual [coeff_congruencePart, coeff_rescale, pow_eq_pow_of_modEq (b := r) _ hζ]

/-- For `m ≠ 0` and a primitive `m`-th root of unity `ζ`, the part of `f` in degrees `≡ r` mod `m`
is the mean over `i < m` of the series `η ^ (-r) f(η z)` with `η = ζ ^ i`. -/
lemma congruencePart_eq_sum {m : ℕ} [NeZero m] {ζ : ℂ_[p]} (hζ : IsPrimitiveRoot ζ m) (r : ℕ)
    (f : ℂ_[p]⟦X⟧) :
    congruencePart m r f = (m : ℂ_[p])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • rescale (ζ ^ i) f := by
  -- Compare the coefficients of `X ^ n`: the factor of `coeff n f` on the right is the average of
  -- the powers of the `m`-th root of unity `ξ = ζ⁻¹ ^ r * ζ ^ n`, which is `1` iff `n ≡ r [MOD m]`.
  ext n
  have hm : m ≠ 0 := NeZero.ne m
  set ξ : ℂ_[p] := ζ⁻¹ ^ r * ζ ^ n with hξ
  have h_one : ξ = 1 ↔ n ≡ r [MOD m] := by
    rw [hξ, inv_pow, inv_mul_eq_one₀ (pow_ne_zero r (hζ.ne_zero hm)), eq_comm,
      (hζ.isOfFinOrder hm).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
  have h_root : ξ ^ m = 1 := by simp [hξ, mul_pow, pow_right_comm _ _ m, hζ.pow_eq_one]
  have h_avg : (m : ℂ_[p])⁻¹ * ∑ i ∈ range m, ξ ^ i = if n ≡ r [MOD m] then 1 else 0 := by
    split_ifs with h_modEq
    · simp [h_one.2 h_modEq, hm]
    · simp [geom_sum_eq (mt h_one.1 h_modEq), h_root]
  calc coeff n (congruencePart m r f) = ((m : ℂ_[p])⁻¹ * ∑ i ∈ range m, ξ ^ i) * coeff n f := by
        simp [h_avg, coeff_congruencePart]
    _ = coeff n ((m : ℂ_[p])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • rescale (ζ ^ i) f) := by
        simp [hξ, mul_assoc, sum_mul, ← inv_pow, pow_right_comm, mul_pow]

/-- Let `m ≠ 0`. If `T` has constant term `0` and only degrees `≡ 1` mod `m`, then substituting `T`
commutes with taking the part of a series in the degrees `≡ r` mod `m`. -/
lemma congruencePart_subst {m : ℕ} {T : ℂ_[p]⟦X⟧} [NeZero m] (hT₀ : constantCoeff T = 0)
    (hT : congruencePart m 1 T = T) (r : ℕ) (g : ℂ_[p]⟦X⟧) :
    congruencePart m r (subst T g) = subst T (congruencePart m r g) := by
  obtain ⟨ζ : ℂ_[p], hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] m
  have hT_subst : HasSubst T := .of_constantCoeff_zero' hT₀
  have h_rescale (i : ℕ) : rescale (ζ ^ i) T = ζ ^ i • T := by
    have h_root : (ζ ^ i) ^ m = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    simpa only [hT, pow_one] using rescale_congruencePart_of_pow_eq_one h_root 1 T
  have h_comm (i : ℕ) : rescale (ζ ^ i) (subst T g) = subst T (rescale (ζ ^ i) g) := by
    rw [rescale_subst hT₀, h_rescale, subst_rescale_eq_subst_smul T hT_subst]
  calc congruencePart m r (subst T g)
      = (m : ℂ_[p])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • subst T (rescale (ζ ^ i) g) := by
        simp only [congruencePart_eq_sum hζ, h_comm]
    _ = subst T (congruencePart m r g) := by
        simp only [congruencePart_eq_sum hζ, ← coe_substAlgHom hT_subst, map_smul, map_sum]

/-- If `T` generates `B`, that is `B = 𝔬[[T]]` with `T = X + ⋯`, then `f ↦ f(T)` is injective. -/
lemma IsSeriesGenerator.subst_injective {T : ℂ_[p]⟦X⟧} {B : Subring ℂ_[p]⟦X⟧}
    (hT : IsSeriesGenerator B T) : (subst T : ℂ_[p]⟦X⟧ → ℂ_[p]⟦X⟧).Injective := by
  obtain ⟨Z, hZ₀, hZ : subst Z T = X, -, -⟩ := hT.exists_subst_inverse
  refine Function.LeftInverse.injective (g := subst Z) fun f ↦ ?_
  rw [subst_comp_subst_apply (.of_constantCoeff_zero' hT.constantCoeff_eq_zero)
    (.of_constantCoeff_zero' hZ₀), hZ, X_subst]

variable (p) in
/-- The ring of the power series whose coefficients in degrees below `n` are integral. -/
def integralBelow (n : ℕ) : Subring ℂ_[p]⟦X⟧ where
  carrier := {f : ℂ_[p]⟦X⟧ | ∀ k < n, coeff k f ∈ valRingCp p}
  zero_mem' k _ := by simp
  one_mem' k _ := by simp [coeff_one, apply_ite (· ∈ valRingCp p)]
  add_mem' hf hg k hk := by simpa using add_mem (hf k hk) (hg k hk)
  neg_mem' hf k hk := by simpa using hf k hk
  mul_mem' hf hg k hk := by
    rw [coeff_mul]
    refine sum_mem fun ⟨i, j⟩ hij ↦ ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hij
    exact mul_mem (hf i (by omega)) (hg j (by omega))

lemma mem_integralBelow : f ∈ integralBelow p n ↔ ∀ k < n, ‖coeff k f‖ ≤ 1 := Iff.rfl

lemma X_mul_mem_integralBelow : X * f ∈ integralBelow p (n + 1) ↔ f ∈ integralBelow p n := by
  rw [mem_integralBelow, Nat.forall_lt_succ_left]
  simp [mem_integralBelow, coeff_succ_X_mul]

/-- For `T : ℂ_[p]⟦X⟧` and `n : ℕ`: if `T(0) = 0`, the coefficients of `T` in degrees below `n` have
norm at most one and `g` is a series over the valuation ring of `ℂ_[p]`, then the coefficients of
`g(T)` in degrees below `n` have norm at most one. -/
lemma subst_seriesToCp_mem_integralBelow (hT₀ : constantCoeff T = 0) (hT : T ∈ integralBelow p n)
    (g : (valRingCp p)⟦X⟧) : subst T (seriesToCp g) ∈ integralBelow p n := by
  intro k hk
  rw [coeff_subst' (.of_constantCoeff_zero' hT₀)]
  exact finsum_induction (· ∈ valRingCp p) (zero_mem _) (fun _ _ ↦ add_mem)
    fun i ↦ mul_mem (SetLike.coe_mem (coeff i g)) (pow_mem hT i k hk)

lemma integralBelow_anti {k n : ℕ} (hkn : k ≤ n) : integralBelow p n ≤ integralBelow p k :=
  fun _ hf j hj ↦ hf j (hj.trans_le hkn)

lemma norm_pow_sub_one_eq_one {π : ℂ_[p]} (hπ : ‖π‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖π ^ n - 1‖ = 1 := by
  have h_lt : ‖π ^ n‖ < ‖(-1 : ℂ_[p])‖ := by simpa using pow_lt_one₀ (norm_nonneg π) hπ hn
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_lt.ne,
    max_eq_right h_lt.le, norm_neg, norm_one]

/-- Let `0 < |π| < 1` and let `G = z + ⋯` be a series over the valuation ring of `ℂ_[p]`, which
`seriesToCp` maps to `ℂ_[p]⟦X⟧`. A series `Y = z + ⋯` with `Y(π z) = π G(Y)` has coefficients in
the valuation ring, that is, lies in the range of `seriesToCp`. -/
lemma mem_range_seriesToCp_of_rescale_eq {π : ℂ_[p]} (hπ₀ : π ≠ 0) (hπ : ‖π‖ < 1) {Y : ℂ_[p]⟦X⟧}
    (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1) {G : (valRingCp p)⟦X⟧} (hG : X ^ 2 ∣ G - X)
    (h_rescale : rescale π Y = π • subst Y (seriesToCp G)) : Y ∈ seriesToCp.range := by
  -- Induction on the degree: with `G = X + X ^ 2 H`, the equation in degree `n` expresses
  -- `(π ^ (n - 1) - 1) coeff n Y` by coefficients of lower degree, and `π ^ (n - 1) - 1` is a
  -- unit for `n ≥ 2`.
  obtain ⟨H : (valRingCp p)⟦X⟧, hH : G - X = X ^ 2 * H⟩ := hG
  obtain ⟨Y₁ : ℂ_[p]⟦X⟧, hY : Y = X * Y₁⟩ := X_dvd_iff.2 hY₀
  have hY_subst : HasSubst Y := .of_constantCoeff_zero' hY₀
  set R : ℂ_[p]⟦X⟧ := X * (X * (Y₁ ^ 2 * subst Y (seriesToCp H))) with hR
  have h_higher : subst Y (seriesToCp G) = Y + R := by
    have h_map : seriesToCp G = X + X ^ 2 * seriesToCp H := by
      simp [seriesToCp_eq_map, eq_add_of_sub_eq' hH]
    rw [h_map, subst_add hY_subst, subst_mul hY_subst, subst_pow hY_subst, subst_X hY_subst, hR]
    linear_combination (Y + X * Y₁) * subst Y (seriesToCp H) * hY
  suffices h_below : ∀ n : ℕ, Y ∈ integralBelow p (n + 2) from
    mem_range_seriesToCp.2 fun n ↦ mem_integralBelow.1 (h_below n) n (by omega)
  intro n
  induction n with
  | zero =>
    rw [mem_integralBelow, Nat.forall_lt_succ_left, Nat.forall_lt_succ_left]
    simp [hY₀, hY₁]
  | succ n ih =>
    -- The higher terms involve in degree `n + 2` only coefficients of `Y` of lower degree.
    have h_rest : R ∈ integralBelow p (n + 3) := by
      have hY₁_below : Y₁ ∈ integralBelow p (n + 1) := by rwa [← X_mul_mem_integralBelow, ← hY]
      rw [hR, X_mul_mem_integralBelow, X_mul_mem_integralBelow]
      exact mul_mem (pow_mem hY₁_below 2)
        (integralBelow_anti (by omega) (subst_seriesToCp_mem_integralBelow hY₀ ih H))
    have h_coeff : (π ^ (n + 1) - 1) * coeff (n + 2) Y = coeff (n + 2) R := by
      have h_eq : π ^ (n + 2) * coeff (n + 2) Y = π * (coeff (n + 2) Y + coeff (n + 2) R) := by
        rw [← map_add, ← h_higher, ← coeff_rescale, h_rescale, coeff_smul, smul_eq_mul]
      exact mul_left_cancel₀ hπ₀ (by linear_combination h_eq)
    have h_norm : ‖coeff (n + 2) Y‖ = ‖coeff (n + 2) R‖ := by
      rw [← h_coeff, norm_mul, norm_pow_sub_one_eq_one hπ n.succ_ne_zero, one_mul]
    rw [mem_integralBelow, Nat.forall_lt_succ_right, h_norm]
    exact ⟨mem_integralBelow.1 ih, mem_integralBelow.1 h_rest (n + 2) (by omega)⟩

/-- Let `m ≠ 0` and let `π ≠ 0` lie in the valuation ring `𝔬` of `ℂ_[p]`. Let
`g = π z + b₁ z ^ (1 + m) + ∑_{i ≥ 2} bᵢ z ^ (1 + i m)` have coefficients in `𝔬`, with `b₁` a unit,
and let `ϖ ^ m = -π / b₁`. Then `g(ϖ z) = ϖ π (z - z ^ (1 + m) + π E)` for an integral series `E`
of order at least two. -/
lemma exists_rescale_eq_smul_X_sub_X_pow {m : ℕ} (hm : m ≠ 0) {π : valRingCp p} (hπ₀ : π ≠ 0)
    {g : (valRingCp p)⟦X⟧} (h_degree : ∀ n : ℕ, coeff n g ≠ 0 → ∃ i : ℕ, n = 1 + i * m)
    (hg₁ : coeff 1 g = π) {b₁ : (valRingCp p)ˣ} (hb₁ : coeff (1 + m) g = b₁) {ϖ : ℂ_[p]}
    (hϖ : ϖ ^ m = (π * -b₁⁻¹ : valRingCp p)) :
    ∃ E : (valRingCp p)⟦X⟧,
      X ^ 2 ∣ E ∧
      rescale ϖ (seriesToCp g) = (ϖ * π) • seriesToCp (X - X ^ (1 + m) + C π * E) := by
  -- The coefficient of `E` in degree `1 + i m`, `i ≥ 2`, is `bᵢ (-b₁) ^ (-i) π ^ (i - 2)`.
  let E : (valRingCp p)⟦X⟧ := mk fun n : ℕ ↦ if 1 + m < n then
    coeff n g * (-b₁⁻¹) ^ ((n - 1) / m) * π ^ ((n - 1) / m - 2) else 0
  refine ⟨E, X_pow_dvd_iff.2 fun n hn ↦ by rw [coeff_mk, ite_eq_right (by omega)], ext fun n ↦ ?_⟩
  -- In degree `n` the identity is an equation in `ℂ_[p]` between elements of `𝔬`.
  suffices h_coeff : ϖ ^ n * coeff n g = ϖ * π * ((if n = 1 then 1 else 0) -
      (if n = 1 + m then 1 else 0) + (π * coeff n E : valRingCp p)) by
    simp only [coeff_rescale, coeff_smul, coeff_seriesToCp, map_add, map_sub, coeff_X, coeff_X_pow,
      coeff_C_mul, smul_eq_mul]
    simpa [apply_ite (Subtype.val : valRingCp p → ℂ_[p])] using h_coeff
  rw [coeff_mk]
  by_cases hn : coeff n g = 0
  · have hn₁ : n ≠ 1 := fun h ↦ hπ₀ (by rw [← hg₁, ← h, hn])
    have hn₂ : n ≠ 1 + m := fun h ↦ b₁.ne_zero (by rw [← hb₁, ← h, hn])
    simp [hn, hn₁, hn₂]
  obtain ⟨i, rfl⟩ := h_degree n hn
  rw [pow_add, pow_mul', hϖ, Nat.add_sub_cancel_left, Nat.mul_div_cancel i hm.bot_lt]
  rcases i with _ | _ | i
  · -- Degree one.
    simp [hg₁, hm]
  · -- Degree `1 + m`.
    have h_inv : ((b₁⁻¹ : (valRingCp p)ˣ) : ℂ_[p]) * b₁ = 1 := mod_cast b₁.inv_mul
    simp [hb₁, hm, mul_assoc, h_inv]
  · -- Degree `1 + (i + 2) m`, the only degrees in which `E` can be nonzero.
    have h_lt : 1 + m < 1 + (i + 1 + 1) * m := by nlinarith [hm.bot_lt]
    simp [h_lt, hm]
    ring

/-- Let `π ≠ 0` be an element of a domain. If `Y = z + ⋯` and `Y(π z) = π W`, then `W ≡ z`
modulo `π`. -/
lemma C_dvd_sub_X_of_rescale_eq {R : Type*} [CommRing R] [IsDomain R] {π : R} (hπ₀ : π ≠ 0)
    {Y W : R⟦X⟧} (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1)
    (h_rescale : rescale π Y = π • W) : C π ∣ W - X := by
  refine ⟨mk fun n : ℕ ↦ if 2 ≤ n then π ^ (n - 2) * coeff n Y else 0, ext fun n ↦ ?_⟩
  have h_coeff : π ^ n * coeff n Y = π * coeff n W := by
    rw [← coeff_rescale, h_rescale, coeff_smul, smul_eq_mul]
  apply mul_left_cancel₀ hπ₀
  rw [map_sub, mul_sub, ← h_coeff, coeff_C_mul, coeff_mk, coeff_X]
  rcases n with _ | _ | n <;> simp [hY₀, hY₁, pow_succ', mul_assoc]

/-- Let `π ≠ 0` be an element of a domain. If `S = z + ⋯` and
`S(π z) = π (S - S ^ q + π E(S))`, then `S - S ^ q ≡ z` modulo `π`. -/
lemma C_dvd_sub_pow_sub_X_of_rescale_eq {R : Type*} [CommRing R] [IsDomain R] {π : R}
    (hπ₀ : π ≠ 0) {q : ℕ} {E S : R⟦X⟧} (hS₀ : constantCoeff S = 0) (hS₁ : coeff 1 S = 1)
    (h_rescale : rescale π S = π • subst S (X - X ^ q + C π * E)) : C π ∣ S - S ^ q - X := by
  have hS : HasSubst S := .of_constantCoeff_zero' hS₀
  have h_dvd : C π ∣ S - S ^ q - X + C π * subst S E := by
    simpa only [subst_add hS, subst_sub hS, subst_pow hS, subst_mul hS, subst_X hS, subst_C,
      ← C.eq_def, add_sub_right_comm] using C_dvd_sub_X_of_rescale_eq hπ₀ hS₀ hS₁ h_rescale
  exact (dvd_add_left (dvd_mul_right (C π) (subst S E))).1 h_dvd

/-- Let `0 < |π| < 1`, `q > 1` and let `E` be integral of order at least two. A series `Y = z + ⋯`
with `Y(π z) / π = Y - Y ^ q + π E(Y)` is integral. -/
lemma mem_range_seriesToCp_of_rescale_eq_X_sub_X_pow {π : valRingCp p} (hπ₀ : π ≠ 0)
    (hπ : ‖(π : ℂ_[p])‖ < 1) {q : ℕ} (hq : 1 < q) {E : (valRingCp p)⟦X⟧} (hE : X ^ 2 ∣ E)
    {Y : ℂ_[p]⟦X⟧} (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1)
    (h_rescale : rescale (π : ℂ_[p]) Y = (π : ℂ_[p]) • subst Y (seriesToCp (X - X ^ q + C π * E))) :
    Y ∈ seriesToCp.range := by
  have h_order : X ^ 2 ∣ X - X ^ q + C π * E - X := by
    rw [show X - X ^ q + C π * E - X = C π * E - X ^ q by ring]
    exact (hE.mul_left _).sub (pow_dvd_pow X hq)
  exact mem_range_seriesToCp_of_rescale_eq (mod_cast hπ₀) hπ hY₀ hY₁ h_order h_rescale

/-- Let `0 < |π| < 1`, `q > 1` and let `E` be integral of order at least two. A series `Y = z + ⋯`
with `Y(π z) / π = Y - Y ^ q + π E(Y)` comes from an integral series `S`, and `S - S ^ q ≡ z`
modulo `π`. -/
lemma exists_seriesToCp_eq_of_rescale_eq {π : valRingCp p} (hπ₀ : π ≠ 0) (hπ : ‖(π : ℂ_[p])‖ < 1)
    {q : ℕ} (hq : 1 < q) {E : (valRingCp p)⟦X⟧} (hE : X ^ 2 ∣ E) {Y : ℂ_[p]⟦X⟧}
    (hY₀ : constantCoeff Y = 0) (hY₁ : coeff 1 Y = 1)
    (h_rescale : rescale (π : ℂ_[p]) Y = (π : ℂ_[p]) • subst Y (seriesToCp (X - X ^ q + C π * E))) :
    ∃ S : (valRingCp p)⟦X⟧, seriesToCp S = Y ∧ C π ∣ S - S ^ q - X := by
  obtain ⟨S, rfl⟩ : Y ∈ seriesToCp.range :=
    mem_range_seriesToCp_of_rescale_eq_X_sub_X_pow hπ₀ hπ hq hE hY₀ hY₁ h_rescale
  have hS₀ : constantCoeff S = 0 := by simpa [constantCoeff_seriesToCp] using hY₀
  have hS₁ : coeff 1 S = 1 := by simpa [coeff_seriesToCp] using hY₁
  -- The functional equation descends to `𝔬[[X]]`.
  have h_int : rescale π S = π • subst S (X - X ^ q + C π * E) := seriesToCp_injective <| by
    rwa [seriesToCp_smul, map_subst (.of_constantCoeff_zero' hS₀), seriesToCp_eq_map, ← rescale_map]
  exact ⟨S, rfl, C_dvd_sub_pow_sub_X_of_rescale_eq hπ₀ hS₀ hS₁ h_int⟩

/-- In characteristic `p`, if `s - s ^ q = x` with `q = p ^ e`, then
`s = ∑_{l < B} x ^ q ^ l + s ^ q ^ B` for every `B`. -/
lemma eq_sum_pow_of_sub_pow_eq {R : Type*} [CommRing R] [CharP R p] {x s : R} {e : ℕ}
    (hs : s - s ^ p ^ e = x) (B : ℕ) : s = ∑ l ∈ range B, x ^ p ^ (e * l) + s ^ p ^ (e * B) := by
  -- The sum telescopes.
  have h_term (l : ℕ) : x ^ p ^ (e * l) = s ^ p ^ (e * l) - s ^ p ^ (e * (l + 1)) := by
    simp [← hs, sub_pow_char_pow, ← pow_mul, ← pow_add, mul_add, add_comm]
  simp [h_term, sum_range_sub' fun l ↦ s ^ p ^ (e * l)]

open scoped Classical in
/-- In prime characteristic `p`, let `q = p ^ e` with `e ≠ 0`. If `S(0) = 0` and `S - S ^ q = z`,
then `S = ∑ z ^ q ^ j`: the coefficient of degree `n` is `1` if `n` is a power of `q`, else `0`. -/
lemma coeff_eq_of_sub_pow_eq_X {R : Type*} [CommRing R] [CharP R p] {S : R⟦X⟧} {e : ℕ}
    (he : e ≠ 0) (hS₀ : constantCoeff S = 0) (hS : S - S ^ p ^ e = X) (n : ℕ) :
    coeff n S = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  have : CharP R⟦X⟧ p := charP_of_injective_ringHom C_injective p
  have hq : 1 < p ^ e := Nat.one_lt_pow he (Fact.out : p.Prime).one_lt
  have h_tail : coeff n (S ^ (p ^ e) ^ n) = 0 := coeff_of_lt_order n
    (lt_of_lt_of_le (mod_cast Nat.lt_pow_self hq) (le_order_pow_of_constantCoeff_eq_zero _ hS₀))
  have h_sum : coeff n S = ∑ l ∈ range n, if n = (p ^ e) ^ l then 1 else 0 := by
    conv_lhs => rw [eq_sum_pow_of_sub_pow_eq hS n]
    simp [pow_mul p e, coeff_X_pow, h_tail]
  rw [h_sum]
  split_ifs with hn
  · obtain ⟨j, rfl⟩ := hn
    simp [Nat.pow_right_inj hq, Nat.lt_pow_self hq]
  · exact sum_eq_zero fun l _ ↦ ite_eq_right fun hl ↦ hn ⟨l, hl⟩

open scoped Classical in
/-- If `π` is a non-unit that divides `p`, `q = p ^ e` with `e ≠ 0`, `S(0) = 0` and
`S - S ^ q ≡ z` modulo `π`, then `S ≡ ∑ z ^ q ^ j` modulo `π`. -/
lemma dvd_coeff_sub_of_C_dvd_sub_pow_sub_X {R : Type*} [CommRing R] {π : R} (hπ : ¬IsUnit π)
    (hπp : π ∣ p) {S : R⟦X⟧} {e : ℕ} (he : e ≠ 0) (hS₀ : constantCoeff S = 0)
    (hS : C π ∣ S - S ^ p ^ e - X) (n : ℕ) :
    π ∣ coeff n S - if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  -- Reduce modulo `π`: the quotient has characteristic `p`, where the equation determines `S`.
  let φ : R →+* R ⧸ Ideal.span {π} := Ideal.Quotient.mk (Ideal.span {π})
  have hφ {x : R} : φ x = 0 ↔ π ∣ x := Ideal.Quotient.eq_zero_iff_dvd π x
  have : Nontrivial (R ⧸ Ideal.span {π}) :=
    Ideal.Quotient.nontrivial_iff.2 (mt Ideal.span_singleton_eq_top.1 hπ)
  have : CharP (R ⧸ Ideal.span {π}) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by simpa using hφ.2 hπp)
  have h_map : S.map φ - S.map φ ^ p ^ e = X := by
    simpa [hφ.2 dvd_rfl, sub_eq_zero] using map_dvd (PowerSeries.map φ) hS
  have h_coeff : coeff n (S.map φ) = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 :=
    coeff_eq_of_sub_pow_eq_X he (by simp [← coeff_zero_eq_constantCoeff_apply, hS₀]) h_map n
  rw [← hφ, map_sub, ← coeff_map, h_coeff, apply_ite φ, map_one, map_zero, sub_self]

end New

end SeriesParts
