module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Tactic.Monotonicity.Lemmas
public import New.Derivatives.Divisibility.Count
public import New.UpperBound.Size.ShortColumns
import New.Derivatives.Sharpness.NearPairs
import New.Reduction.Data.Sizes

section
/-!
# A lower bound for the divisibility bound by the gain

Fix a prime `p`. The divisibility bound of stage `j` at `p` measures the `p`-divisibility of a lift;
it depends on a set `S` (also written `ev`) of places whose long rows are removed.

This file defines it and bounds it from below by the gain at `p` when `p < x₁` is non-split. Apart
from an error term, only collisions lose; a collision is a pair `(τ, e)` with `e ∈ I_p` (`e` odd, or
`p = d`) such that `τ` and `(-p ^ e) τ` are `a`-places outside `ev`. In `lowColumns` and `lowBoxes`
a column is a column of a diagram; they count the columns of height below `n_{j+1}` and different
from `1`, and the boxes in them.

## Main definitions and results

* `New.Data.divisibilityBound`: the divisibility bound at `p` of stage `j`, for a set `S` of places.
* `New.Data.le_divisibilityBound`: the lower bound for the divisibility bound by the gain at `p`.

Notions from other files:
* `New.Data.aPlaces`: The `a`-places: the infinite places of `E` whose class in `(ℤ/q₁)ˣ` is `1`
  modulo `q₀`.
* `New.Data.IsExceptional`, `New.Data.ceilLogLifts`: A condition on `p` alone: `(p/d) = -1`,
  `p ≢ ±1` modulo `m`, and the order `o₀` of `-p` modulo `q₀` is odd and at most `𝔯`, the least
  natural number with `m ≤ p^𝔯`.
* `New.Data.placeOfInt`: The infinite place of E named by the class of the integer ν modulo q₁ if ν
  is prime to q₁, and the identity place otherwise.
-/

@[expose] public section

noncomputable section

namespace New.Data

section DivisibilityBound

open Finset Real Nat

variable {P : Parameters} {D : Data P}

/-- The number of columns at τ of height below n_{j+1} and different from 1: the sum of
`columnCount τ h` over h < n_{j+1}, h ≠ 1. -/
def lowColumns (j : ℕ) (τ : D.Φ) : ℕ := ∑ h ∈ range (D.n (j + 1)),
  if h = 1 then 0 else D.columnCount τ h

/-- The number of boxes in the columns counted by `New.Data.lowColumns` j τ: the sum of
h·`columnCount τ h` over h < n_{j+1}, h ≠ 1. -/
def lowBoxes (j : ℕ) (τ : D.Φ) : ℕ := ∑ h ∈ range (D.n (j + 1)),
  h * if h = 1 then 0 else D.columnCount τ h

/-- The divisibility bound at `p` of stage `j`, for a set `ev` of places. Remove the columns of
height one at the places of `ev` from the diagrams `D.columnCount`, read at heights below
`n = D.n (j + 1)`. The bound is the predicted divisibility of what remains, plus the full gain
`γ_p = gammaPrime P.d p` for each removed box, less `f n ^ 3 (1 + log_p (max B 1))`. Here `B` is the
number of boxes before the removal. -/
noncomputable def divisibilityBound (p j : ℕ) (ev : Finset D.Φ) : ℝ :=
  predictedDivisibility P.d p (P.partner D.towerExp p) (eraseHeightOne D.columnCount ev)
    (D.n (j + 1)) +
    gammaPrime P.d p * (boxes D.columnCount (D.n (j + 1)) - boxes (eraseHeightOne D.columnCount ev)
      (D.n (j + 1))) -
    D.f * D.n (j + 1) ^ 3 * (1 + logb p (max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ))

/-- The length of the long row at `τ` (the `a` columns of height one at an `a`-place) after removing
the long rows at the places of `ev`. -/
noncomputable def longRow (ev : Finset D.Φ) (τ : D.Φ) : ℝ := if τ ∈ D.aPlaces \ ev then D.a else 0

/-- The term of the place `τ` and the exponent `e` in the predicted divisibility of stage `j`, after
removing the long rows at the places of `ev` and without the factor `v(π_p)`. It is zero unless
`e ∈ I_p = positivePartnerExponents P.d p`, and `P.partner D.towerExp p e τ` is the place
`(-p ^ e) τ`. -/
noncomputable def partnerTerm (p j : ℕ) (ev : Finset D.Φ) (τ : D.Φ) (e : ℕ) : ℝ :=
  if e ∈ positivePartnerExponents P.d p then
    (longRow ev τ / p ^ e - longRow ev (P.partner D.towerExp p e τ) -
        D.lowColumns j (P.partner D.towerExp p e τ))⁺ +
      (D.lowBoxes j τ / p ^ e - D.lowBoxes j (P.partner D.towerExp p e τ) : ℝ)⁺ - D.lowColumns j τ /
        p ^ e
  else 0

variable {p : ℕ} [q : Fact p.Prime]

/-- The terms `partnerTerm p j S τ e = (L τ / p ^ e - L τ' - c τ')₊ + (l τ / p ^ e - l τ')₊ - c
τ / p ^ e`, where `τ' = (-p ^ e) τ`, `L = longRow S`, `c = lowColumns j` and `l = lowBoxes j` (zero
unless `e ∈ positivePartnerExponents P.d p`), are summable over `e`. -/
lemma summable_partnerTerm (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    Summable (partnerTerm p j S τ) := by
  -- Each term is bounded in absolute value by a constant times `1 / p ^ e`.
  refine (hasSum_div_pow_positivePartnerExponents P.d p
    (longRow S τ + D.lowBoxes j τ + D.lowColumns j τ)).summable.of_norm_bounded fun e ↦ ?_
  have h_abs {a a' b b' c : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb : 0 ≤ b) (hb' : 0 ≤ b')
      (hc : 0 ≤ c) : |(a - a')⁺ + (b - b')⁺ - c| ≤ a + b + c := by grind [posPart_def]
  rw [partnerTerm, sub_sub, add_div, add_div, norm_eq_abs]
  split_ifs
  · unfold longRow
    apply h_abs <;> positivity
  · simp

/-- After removing the long rows at the places of `S`, the number of columns of height one at `τ`
below `n_{j+1}` is `longRow S τ`. -/
lemma heightOneColumns_eraseHeightOne (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    (heightOneColumns (eraseHeightOne D.columnCount S) (D.n (j + 1)) τ : ℝ) = longRow S τ := by
  have h_one : 1 < D.n (j + 1) := by grind [n]
  by_cases τ ∈ S <;> simp [heightOneColumns, eraseHeightOne, longRow, columnCount, *]

/-- Erasing the columns of height one at the places of `S` from `D.columnCount` keeps the number of
low columns: `lowColumnCount` at height bound `D.n (j + 1)` equals `D.lowColumns j τ`. -/
lemma lowColumnCount_eraseHeightOne (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    lowColumnCount (eraseHeightOne D.columnCount S) (D.n (j + 1)) τ = D.lowColumns j τ :=
  sum_congr rfl fun h _ ↦ by simp +contextual [eraseHeightOne]

/-- Erasing the columns of height one at the places of `S` from `D.columnCount` keeps the number of
boxes in the low columns: `lowBoxCount` at height bound `D.n (j + 1)` equals `D.lowBoxes j τ`. -/
lemma lowBoxCount_eraseHeightOne (j : ℕ) (S : Finset D.Φ) (τ : D.Φ) :
    lowBoxCount (eraseHeightOne D.columnCount S) (D.n (j + 1)) τ = D.lowBoxes j τ :=
  sum_congr rfl fun h _ ↦ by simp +contextual [eraseHeightOne]

variable (D) in
/-- The loss `D.loss p` is at least `f * logB ^ 2 * (a / p)`: for `p ≡ ±1` modulo `m` it carries
the additional factor `m ≥ 1`. -/
lemma le_loss (p : ℕ) : D.f * D.logB ^ 2 * (D.a / p) ≤ D.loss p := by
  unfold loss
  bound [D.ten_thousand_le_m]

variable (D) in
/-- For odd `e` and an `a`-place `τ`, the place `D.placeOfInt (-p ^ e) * τ` is an `a`-place if and
only if `D.o₀ p` divides `e`. -/
lemma placeOfInt_mul_mem_aPlaces_iff {p e : ℕ} (he : Odd e) (τ : D.Φ) (hτ : τ ∈ D.aPlaces) :
    D.placeOfInt (-p ^ e) * τ ∈ D.aPlaces ↔ D.o₀ p ∣ e := by
  simp_all [← he.neg_pow, ← Parameters.placeOfInt_pow, o₀, aPlaces, orderOf_dvd_iff_pow_eq_one]

/-- If `(τ, e)` is a collision at `p` outside `S`, that is, `τ` and `placeOfInt (-p ^ e) * τ` are
`a`-places outside `S` and `e ∈ I_p` (it is odd, or `p = d`), then `p ≠ d`, and `e` is odd and
divisible by the order `o₀ p` of `-p` modulo `q₀`. -/
lemma IsCollision.ne_and_odd_and_dvd {p : ℕ} {S : Finset D.Φ} {τ : D.Φ} {e : ℕ}
    (h : D.IsCollision p S τ e) : p ≠ P.d ∧ Odd e ∧ D.o₀ p ∣ e := by
  grind [IsCollision, mem_positivePartnerExponents, mem_partnerExponents, aPlaces,
    ne_d_of_placeClass_eq, placeOfInt_mul_mem_aPlaces_iff]

/-- Let `p` be a prime and `S` a set of infinite places of `E` (`D.Φ` is the type of these places,
`f` their number). If every collision has `e ≥ o`, then `collisionSum p S`, the sum of `a / p ^ e`
over the collisions, is at most `2 f a / p ^ o`; here `a = D.a` is the length of a long row. -/
lemma collisionSum_le {S : Finset D.Φ} {o : ℕ}
    (h_le : ∀ {τ : D.Φ} {e : ℕ}, D.IsCollision p S τ e → o ≤ e) :
    D.collisionSum p S ≤ 2 * D.f * D.a / p ^ o := by
  classical
  -- At each of the `f` places the series starts at `e = o`, and as `p ≥ 2` its terms are at most
  -- those of the geometric series with first term `a / p ^ o` and ratio `1 / 2`.
  have h_place (τ : D.Φ) :
      ∑' e : ℕ, ite (D.IsCollision p S τ e) (D.a / p ^ e : ℝ) 0 ≤ D.a / p ^ o * 2 := by
    set t : ℕ → ℝ := fun e ↦ ite (D.IsCollision p S τ e) (D.a / p ^ e : ℝ) 0
    have h_support : Function.support t ⊆ Set.range (o + ·) :=
      fun e he ↦ le.dest (by grind)
    have h_bound (e : ℕ) : ‖t (o + e)‖ ≤ D.a / p ^ o * 2 / 2 / 2 ^ e :=
      calc ‖t (o + e)‖ ≤ (D.a / p ^ o / p ^ e : ℝ) := by
            unfold t
            split
            · simp [pow_add, ← div_div]
            · rw [norm_zero]; positivity
        _ ≤ D.a / p ^ o / 2 ^ e := by gcongr; exact mod_cast q.out.two_le
        _ = _ := by ring
    grw [← (add_right_injective o).tsum_eq h_support, le_norm_self (tsum _)]
    exact tsum_of_norm_bounded (hasSum_geometric_two' _) h_bound
  grw [collisionSum, h_place]
  simp [field]

/-- Let the prime `p` be below the cut-off `x₁`, non-split in `K = ℚ(√-d)` and not exceptional. Then
`m * collisionSum p ∅ ≤ loss p`, where `loss p` is `m f a (log b)² / p` if `p ≡ ±1` modulo `m` and
`f a (log b)² / p` otherwise. Here `m` is the number of lifts, `f` the number of infinite places of
`E`, and `a = x b` is the product of the scales `x` and `b` of the data. -/
lemma mul_collisionSum_le_loss (hp : D.IsSmallNonsplit p)
    (h_not_exceptional : ¬D.IsExceptional p) :
    D.m * D.collisionSum p ∅ ≤ D.loss p := by
  grw [loss, ← (D.le_of_hasLogBound : 2 ≤ D.logB ^ 2)]
  split
  · -- If `p ≡ ±1` modulo `m`, the loss has the factor `m`, and it is enough that exponents are
    -- positive.
    grw [collisionSum_le (o := 1) (by grind [IsCollision, mem_positivePartnerExponents])]
    grind
  · -- Otherwise a collision has `e` an odd multiple of `o₀`. So either there is none, or `o₀` is
    -- odd and exceeds `ceilLogLifts p`, as `p` is not exceptional; and `m ≤ p ^ ceilLogLifts p`.
    have h_far {τ : D.Φ} {e : ℕ} (hc : D.IsCollision p ∅ τ e) : D.ceilLogLifts p + 1 ≤ e := by
      obtain ⟨h_ne, h_odd, h_dvd⟩ := hc.ne_and_odd_and_dvd
      grind [IsExceptional, chiK_cases, Odd.of_dvd_nat, Nat.le_of_dvd h_odd.pos h_dvd]
    grw [collisionSum_le h_far, le_pow_clog q.out.one_lt D.m, ← ceilLogLifts]
    have hp_ne : p ≠ 0 := q.out.ne_zero
    simp [pow_succ, field]

/-- The least height `k` of a low column is below `n_{j+1}`. -/
lemma k_mem_range_n_succ (j : ℕ) : D.k ∈ range (D.n (j + 1)) := by simp [n]

variable {j : ℕ}

/-- The number `lowBoxes j σ` of boxes in the low columns at `σ` is at least `k w`, where
`w = D.weight σ` and `k` is the least height of a low column: the columns of height `k` alone have
that many boxes. -/
lemma mul_weight_le_lowBoxes (j : ℕ) (σ : D.Φ) : D.k * (D.weight σ : ℝ) ≤ D.lowBoxes j σ := by
  have h_single : D.k * (if D.k = 1 then 0 else D.columnCount σ D.k) ≤ D.lowBoxes j σ :=
    single_le_sum (f := fun h : ℕ ↦ h * if h = 1 then 0 else D.columnCount σ h) (by simp)
      (k_mem_range_n_succ j)
  grw [← h_single, weight_le_liftWeight_sub _ 1]
  rify
  gcongr
  norm_cast
  grind [columnCount]

/-- Let `j < m`, with `m = D.m` the number of lifts, and `σ : D.Φ` an infinite place of `E`. The
number `D.lowColumns j σ` of columns at `σ` of height below `n_{j+1}` and other than `1` is at most
`D.weight σ + x ^ 60`, where `x` is the scale `D.x`: there are about `D.weight σ` of height `k` and
at most `D.gap` of every other height. -/
lemma lowColumns_le (hj : j < D.m) (σ : D.Φ) :
    D.lowColumns j σ ≤ (D.weight σ : ℝ) + D.x ^ 60 := by
  -- The size of the rank, as an instance for `D.le_of_hasLogBound`, which compares orders of
  -- magnitude.
  have := D.hasLogUpper_of_le (D.n_mono hj)
  calc (D.lowColumns j σ : ℝ) ≤ D.liftWeight 1 σ + D.n (j + 1) * D.gap := by
        grw [lowColumns, columnCount_le]
        simp [k_mem_range_n_succ j, sum_add_distrib]
    _ ≤ D.weight σ + D.x ^ 60 := by
        grw [D.liftWeight_le_weight_add D.nat_le_of_hasLogBound, add_assoc]
        exact add_le_add le_rfl D.le_of_hasLogBound

/-- For `j < D.m`, the number `D.lowBoxes j σ` of boxes in the columns at `σ` of height below
`n_{j+1}` and different from `1` is at most `D.k * D.weight σ + D.x ^ 60`. -/
lemma lowBoxes_le (hj : j < D.m) (σ : D.Φ) :
    D.lowBoxes j σ ≤ D.k * (D.weight σ : ℝ) + D.x ^ 60 := by
  have := D.hasLogUpper_of_le (D.n_mono hj)
  calc (D.lowBoxes j σ : ℝ) ≤
        D.k * D.liftWeight 1 σ + (D.n (j + 1) * (D.n (j + 1) - 1) / 2 : ℕ) * D.gap := by
        grw [lowBoxes, columnCount_le]
        simp [k_mem_range_n_succ j, mul_add, sum_add_distrib, ← sum_mul, sum_range_id]
    _ ≤ D.k * D.weight σ + D.x ^ 60 := by
        grw [D.liftWeight_le_weight_add D.nat_le_of_hasLogBound, Nat.div_le_self, sub_le, mul_add,
          add_assoc]
        exact add_le_add le_rfl D.le_of_hasLogBound

/-- The number `boxes D.columnCount (D.n (j + 1))` of boxes in the columns of height
below `D.n (j + 1)` equals `D.a` times the number of a-places `D.aPlaces`, plus the sum over `σ` of
`D.lowBoxes j σ`, the boxes in columns at `σ` of height below `D.n (j + 1)` other than `1`. -/
lemma boxes_eq_aPlaces_add_low :
    (boxes D.columnCount (D.n (j + 1)) : ℝ) = #D.aPlaces * D.a + ∑ σ : D.Φ,
      (D.lowBoxes j σ : ℝ) := by
  have h_one : 1 < D.n (j + 1) := by grind [n]
  have h_split (σ : D.Φ) (h : ℕ) : h * D.columnCount σ h =
      (if h = 1 then if σ ∈ D.aPlaces then D.a else 0 else 0) + h * if h = 1 then 0 else
        D.columnCount σ h := by
    split_ifs <;> simp_all [columnCount]
  simp_rw [boxes, h_split, sum_add_distrib]
  simp [lowBoxes, h_one, Finset.univ_inter _]

/-- The boxes removed with the columns of height one at the places of `S` are the `a`
boxes at each a-place in `S`. -/
lemma boxes_sub_boxes_eraseHeightOne (S : Finset D.Φ) :
    (boxes D.columnCount (D.n (j + 1)) - boxes (eraseHeightOne D.columnCount S) (D.n (j + 1)) : ℝ)
      =
      #(D.aPlaces ∩ S) * D.a := by
  have h_card : (#D.aPlaces : ℝ) = #(D.aPlaces \ S) + #(D.aPlaces ∩ S) :=
    mod_cast (card_sdiff_add_card_inter D.aPlaces S).symm
  rw [boxes_eq_aPlaces_add_low]
  simp [-Nat.cast_sum, boxes_eq_sum, heightOneColumns_eraseHeightOne,
    lowBoxCount_eraseHeightOne, sum_add_distrib, longRow, h_card, add_mul, sum_ite_mem, -mem_sdiff,
    Finset.univ_inter _]

/-- Let `p` be a prime and `j < m`, the number of lifts. The diagram at an infinite place `τ` of `E`
has `D.columnCount τ h` columns of height `h`. Let `B` be the number of boxes of these diagrams, at
all places, in the columns of height below the rank `n_{j+1} = D.n (j + 1)`. Then
`1 + log_p (max B 1)` is at most `(log b) ^ 2`, where `b` is the largest scale of the data and
`log b = D.logB`. -/
lemma one_add_logb_boxes_le (hj : j < D.m) :
    1 + logb p (max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ) ≤ D.logB ^ 2 := by
  have h_low (σ : D.Φ) : (D.lowBoxes j σ : ℝ) ≤ D.M :=
    (lowBoxes_le hj σ).trans D.le_of_hasLogBound
  have h_boxes : ((max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ) : ℝ) ≤ D.f * D.a + D.f * D.M +
    1 := by
    grw [max_le_add_of_nonneg (Nat.zero_le _) zero_le_one, cast_add_one,
      boxes_eq_aPlaces_add_low,
      h_low, card_le_univ]
    simp [f, Core.numInfPlaces]
  have h_log : 1 / 2 ≤ Real.log p := by
    grw [← q.out.two_le]
    linarith only [Real.log_two_gt_d9]
  calc _ ≤ 1 + Real.log (D.f * D.a + D.f * D.M + 1) / (1 / 2) := by
        grw [logb, ← h_log, h_boxes]
    _ ≤ D.logB ^ 2 := D.le_of_hasLogBound

/-- Let `j < m`, let the prime `p` be below the cut-off `x₁` and non-split in `K = ℚ(√-d)`, let
`e ∈ positivePartnerExponents P.d p`, let `S` be a set of infinite places of `E`, and let
`τ' = D.placeOfInt (-p ^ e) * τ` be the product of `τ` with the place of the class of `-p ^ e`
modulo `q₁`. With `a = x b` the product of the scales `x` and `b`, the weight `w = D.weight` is
`a / x` at the b-places and `a / x₁` elsewhere. Let `L = longRow S` be `a` at the a-places outside
`S` and `0` elsewhere, and let `c = lowColumns j` count the columns of height below `n_{j+1}` other
than `1`. For an a-place `τ` the number `(a / p ^ e - w τ')₊` is at most
`(L τ / p ^ e - L τ' - c τ')₊ + x ^ 60`, plus `a / p ^ e` if `τ ∈ S` or if `(τ, e)` is a collision.
For `τ ∈ S` and `e = 1` the bound still holds with `a / x₁` added on the left. -/
lemma posPart_sub_weight_le_posPart_longRow (hj : j < D.m) (hp : D.IsSmallNonsplit p)
    (S : Finset D.Φ) (τ : D.Φ) {e : ℕ} (he : e ∈ positivePartnerExponents P.d p)
    [Decidable (D.IsCollision p S τ e)] :
    (if τ ∈ D.aPlaces then (D.a / p ^ e - D.weight (D.placeOfInt (-p ^ e) * τ) : ℝ)⁺ else 0) +
        (if e = 1 ∧ τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
      (longRow S τ / p ^ e - longRow S (D.placeOfInt (-p ^ e) * τ) -
          D.lowColumns j (D.placeOfInt (-p ^ e) * τ))⁺ +
        (if τ ∈ D.aPlaces ∩ S then (D.a / p ^ e : ℝ) else 0) +
        (if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) + D.x ^ 60 := by
  set τ' : D.Φ := D.placeOfInt (-p ^ e) * τ with hτ'
  have hp_pos : (0 : ℝ) < p := mod_cast q.out.pos
  have h_quot : (0 : ℝ) ≤ D.a / p ^ e := by positivity
  have h_err : 0 ≤ D.x ^ 60 := by positivity
  have h_weight : (D.a / D.x₁ : ℝ) ≤ D.weight τ' := (D.weight_mem_Icc τ').1
  by_cases h_aPlace : τ ∈ D.aPlaces
  swap
  · simp only [h_aPlace, mem_inter, false_and, and_false, ite_false, add_zero]
    positivity
  have h_nonneg : (0 : ℝ) ≤ D.weight τ' := Nat.cast_nonneg _
  simp only [IsCollision, ← hτ', mem_inter, h_aPlace, he, posPart_def, longRow]
  by_cases h_removed : τ ∈ S
  · -- A removed row: only the surplus at `e = 1` is to be absorbed.
    have h_surplus (h_one : e = 1) : (D.a / D.x₁ : ℝ) ≤ D.a / p ^ e := by
      simpa [h_one] using div_le_div_of_nonneg_left (Nat.cast_nonneg D.a) hp_pos hp.1.le
    grind
  · -- A row that stays: `τ'` is an a-place outside `S` (a collision), or its long row is empty.
    grind [lowColumns_le hj τ']

/-- For `j < m` and `z > 0`, the second term of the gain, `k (w(τ) / z - w(τ'))₊` with `w` the
weight and `k` the least height of a column other than `1`, exceeds the same expression in the boxes
of the low columns by at most `x ^ 60`. -/
lemma mul_posPart_weight_le (hj : j < D.m) (τ τ' : D.Φ) {z : ℝ} (hz : 0 < z) :
    D.k * (D.weight τ / z - D.weight τ')⁺ ≤ (D.lowBoxes j τ / z - D.lowBoxes j τ')⁺ + D.x ^ 60 := by
  have h_lower : D.k * (D.weight τ / z) ≤ D.lowBoxes j τ / z := by
    grw [← mul_div_assoc, mul_weight_le_lowBoxes j τ]
  rw [posPart_def, posPart_def, mul_max_of_nonneg _ _ (Nat.cast_nonneg _), mul_zero, mul_sub]
  grind [lowBoxes_le hj τ', show 0 ≤ D.x ^ 60 by positivity]

/-- Let `j < m`, the number of lifts, let `S` be a set of places, and let
`-τ = P.partner D.towerExp P.d 0 τ` be the product of `τ` with the place named by `-1`. Let
`L = longRow S` be `a = D.a` at the a-places outside `S` and `0` elsewhere, let `c = lowColumns j`
count the columns of height below `n_{j+1}` other than `1`, and let `l = lowBoxes j` count the boxes
in these columns. Then `min (L τ) (L (-τ) + c (-τ)) + c τ + min (l τ) (l (-τ))` is at most
`3 a / (d m)`, because `τ` and `-τ` are neither both a-places nor both b-places (class `-1`). -/
lemma min_longRow_add_lowColumns_add_min_lowBoxes_le (hj : j < D.m) (S : Finset D.Φ) (τ : D.Φ) :
    min (longRow S τ) (longRow S (P.partner D.towerExp P.d 0 τ) +
          D.lowColumns j (P.partner D.towerExp P.d 0 τ)) + D.lowColumns j τ +
        min (D.lowBoxes j τ : ℝ) (D.lowBoxes j (P.partner D.towerExp P.d 0 τ)) ≤
      3 * (D.a / P.d / D.m) := by
  set τ' : D.Φ := P.partner D.towerExp P.d 0 τ
  have h_class : P.placeClass ⟨towerDeg D.towerExp, rfl⟩ τ' ≠ P.placeClass
    ⟨towerDeg D.towerExp, rfl⟩ τ :=
    fun h_eq ↦ D.ne_d_of_placeClass_eq h_eq rfl
  set u : ℝ := D.a / P.d / D.m
  have h_columns (σ : D.Φ) : (D.lowColumns j σ : ℝ) ≤ u :=
    (lowColumns_le hj σ).trans D.le_of_hasLogBound
  have h_boxes (σ : D.Φ) (hσ : σ ∉ D.bPlaces) : (D.lowBoxes j σ : ℝ) ≤ u :=
    (lowBoxes_le hj σ).trans (by simpa [cast_weight, hσ] using D.le_of_hasLogBound)
  have h_rows : min (longRow S τ) (longRow S τ' + D.lowColumns j τ') ≤ u := by
    obtain h_not | h_not : τ ∉ D.aPlaces ∨ τ' ∉ D.aPlaces := by grind [aPlaces]
    · exact min_le_of_left_le (by simpa [longRow, h_not] using by positivity)
    · exact min_le_of_right_le (by simpa [longRow, h_not] using h_columns τ')
  have h_min : min (D.lowBoxes j τ : ℝ) (D.lowBoxes j τ') ≤ u := by
    obtain h_not | h_not : τ ∉ D.bPlaces ∨ τ' ∉ D.bPlaces := by grind [placeClass_of_mem_bPlaces]
    · exact min_le_of_left_le (h_boxes τ h_not)
    · exact min_le_of_right_le (h_boxes τ' h_not)
  linarith [h_columns τ]

/-- Let `p` be a prime, `j < m` (the number of lifts) and `S` a set of infinite places of `E`.
Remove from the diagrams `D.columnCount` the columns of height one at the places of `S`, and read
them at heights below `n_{j+1}`. Their `predictedDivisibility` at `p`, for the partner map
`P.partner D.towerExp p e τ = (-p ^ e) τ`, is by definition `v(π_p) = piPrimeValuation P.d p` times
the sum over all `e` and `τ` of `partnerTerm p j S τ e`, the term that compares the diagram at `τ`
with that at its partner, less a correction if `p = d`. The correction is at most `2 a / (p m)` for
each of the `f` places, where `a = D.a` is the length of a long row. -/
lemma sub_le_predictedDivisibility (hj : j < D.m) (S : Finset D.Φ) :
    piPrimeValuation P.d p * ∑ τ : D.Φ, ∑' e : ℕ, partnerTerm p j S τ e -
        D.f * (2 * (D.a / p / D.m)) ≤
      predictedDivisibility P.d p (P.partner D.towerExp p) (eraseHeightOne D.columnCount S)
        (D.n (j + 1)) := by
  simp only [predictedDivisibility, heightOneColumns_eraseHeightOne,
    lowColumnCount_eraseHeightOne, lowBoxCount_eraseHeightOne]
  rw [← Summable.tsum_finsetSum fun τ _ ↦ summable_partnerTerm j S τ]
  refine sub_le_sub (by simp only [partnerTerm, sum_ite_irrel, sum_const_zero, le_refl]) ?_
  split_ifs with h_ramified
  · subst h_ramified
    grw [sum_le_card_nsmul univ _ _ fun τ _ ↦
      min_longRow_add_lowColumns_add_min_lowBoxes_le hj S τ, nsmul_eq_mul]
    change (1 / 2 * (D.f * (3 * (D.a / P.d / D.m))) : ℝ) ≤ D.f * (2 * (D.a / P.d / D.m))
    linarith only [show (0 : ℝ) ≤ D.f * (D.a / P.d / D.m) by positivity]
  · positivity

/-- For `j < D.m` and a place `τ`, the number `γ_p = gammaPrime P.d p` times the number
`D.lowColumns j τ` of columns at `τ` of height below `n_{j+1}` and different from `1` is at most
`D.a / p / D.m`. -/
lemma gammaPrime_mul_lowColumns_le (hj : j < D.m) (τ : D.Φ) :
    gammaPrime P.d p * D.lowColumns j τ ≤ D.a / p / D.m := by
  have h_inv : (1 / (p - 1) : ℝ) ≤ 2 / p := by
    rw [div_le_div_iff₀] <;> linarith [show (2 : ℝ) ≤ p from mod_cast q.out.two_le]
  calc _ ≤ 2 / p * (D.weight τ + D.x ^ 60) := by
        grw [gammaPrime_le_one_div, h_inv, lowColumns_le hj τ]
    _ ≤ D.a / p / D.m := by
        rw [div_mul_eq_mul_div, div_right_comm]
        exact div_le_div_of_nonneg_right D.le_of_hasLogBound p.cast_nonneg

open scoped Classical in
/-- The bound for the gain `D.gain p` at one infinite place `τ` of `E`. Let `j < m`, let the prime
`p` be below the cut-off `x₁` and non-split in `K = ℚ(√-d)`, and let `S` be a set of places whose
long rows are removed. Let `I_p = positivePartnerExponents P.d p`, `v = piPrimeValuation P.d p` and
`γ_p = gammaPrime P.d p = v ∑_{e ∈ I_p} 1 / p ^ e`. The weight `w = D.weight` is `a / x` at the
b-places and `a / x₁` elsewhere, `a = x b` being the product of two scales of the data, and
`s_p = localPrimeSum p` is the series `s_p(y, τ) = v ∑_{e ∈ I_p} (y / p ^ e - w((-p ^ e) τ))₊`. The
left side is the share of `τ` in `gain p / m`, namely `s_p(a, τ)` (for an a-place only, that is, of
class `1` modulo `q₀`) plus `k s_p(w(τ), τ)` with `k` the rank of the source, increased by
`v a / x₁` if `τ` is an a-place in `S`. It is at most `v` times the sum of three terms, plus `γ_p`
times the number `lowColumns j τ` of columns of height below `n_{j+1}` other than `1`, plus `γ_p a`
if `τ` is an a-place in `S`. The three terms are the series of `partnerTerm p j S τ e`, the series
of `a / p ^ e` over the `e ∈ I_p` such that `τ` and `(-p ^ e) τ` are a-places outside `S`
(collisions), and `2 x ^ 60` for each of the `clog p ⌈x₁⌉₊` exponents `e` with `p ^ e < x₁`. -/
lemma localPrimeSum_add_le_mul_tsum_partnerTerm_add (hj : j < D.m) (hp : D.IsSmallNonsplit p)
    (S : Finset D.Φ) (τ : D.Φ) :
    (if τ ∈ D.aPlaces then D.localPrimeSum p D.a τ else 0) +
        D.k * D.localPrimeSum p (D.weight τ) τ +
        piPrimeValuation P.d p * (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
      piPrimeValuation P.d p * ((∑' e : ℕ, partnerTerm p j S τ e) +
          (∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) +
          clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60)) +
        gammaPrime P.d p * (D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) := by
  -- Divide by `v`. Each of the seven terms is then the sum of a series in `e`; compare the series
  -- term by term.
  have hv_pos : 0 < piPrimeValuation P.d p := piPrimeValuation_pos P.d p
  suffices h_div :
      (if τ ∈ D.aPlaces then 1 else 0) * (D.localPrimeSum p D.a τ / piPrimeValuation P.d p) +
          D.k * (D.localPrimeSum p (D.weight τ) τ / piPrimeValuation P.d p) +
          (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
        ∑' e : ℕ, partnerTerm p j S τ e +
          (D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) * gammaPrime P.d p /
            piPrimeValuation P.d p +
          (∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) +
          clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60) by
    rw [← boole_mul (τ ∈ D.aPlaces)]
    refine le_of_eq_of_le ?_ ((mul_le_mul_of_nonneg_left h_div hv_pos.le).trans_eq ?_)
    · field
    · field
  have h_gain (y : ℝ) : HasSum (fun e : ℕ ↦ if e ∈ positivePartnerExponents P.d p then
        (y / p ^ e - D.weight (D.placeOfInt (-p ^ e) * τ))⁺ else 0)
      (D.localPrimeSum p y τ / piPrimeValuation P.d p) := by
    rw [localPrimeSum, mul_div_cancel_left₀ _ hv_pos.ne']
    exact (D.summable_posPart_sub_weight p y τ).hasSum
  have h_surplus : HasSum
      (fun e : ℕ ↦ if e = 1 then (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) else 0)
      (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) :=
    hasSum_ite_eq 1 _
  have h_full : HasSum (fun e : ℕ ↦ if e ∈ positivePartnerExponents P.d p then
        ((D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) / p ^ e : ℝ) else 0)
      ((D.lowColumns j τ + if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) * gammaPrime P.d p /
        piPrimeValuation P.d p) :=
    hasSum_div_pow_positivePartnerExponents P.d p _
  have h_coll : Summable fun e : ℕ ↦ if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0 := by
    refine (hasSum_div_pow_positivePartnerExponents P.d p D.a).summable.of_nonneg_of_le
      (fun e ↦ by positivity) fun e ↦ ?_
    by_cases h_collision : D.IsCollision p S τ e
    · rw [ite_eq_left h_collision, ite_eq_left h_collision.1]
    · rw [ite_eq_right h_collision]
      positivity
  have h_err : HasSum (fun e : ℕ ↦ if e ∈ range (clog p ⌈D.x₁⌉₊) then 2 * D.x ^ 60 else 0)
      (clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60)) := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (s := range (clog p ⌈D.x₁⌉₊)) (fun e he ↦ ite_eq_right he) using 1
    simp [sum_ite_of_true]
  refine hasSum_le (fun e ↦ ?_)
    ((((h_gain D.a).mul_left _).add ((h_gain (D.weight τ)).mul_left _)).add h_surplus)
    ((((summable_partnerTerm j S τ).hasSum.add h_full).add h_coll.hasSum).add h_err)
  by_cases he : e ∈ positivePartnerExponents P.d p
  swap
  · have h_ne : e ≠ 1 := fun h_one ↦
      he (by simpa [h_one] using one_mem_positivePartnerExponents hp.2)
    simpa [partnerTerm, IsCollision, he, h_ne] using by positivity
  simp only [partnerTerm, he, ite_true, add_div, ite_div, zero_div, ite_mul, one_mul, zero_mul,
    ← ite_and, Parameters.partner]
  by_cases h_small : e ∈ range (clog p ⌈D.x₁⌉₊)
  · rw [ite_eq_left h_small]
    linarith [posPart_sub_weight_le_posPart_longRow hj hp S τ he, mul_posPart_weight_le hj τ
      (D.placeOfInt (-p ^ e) * τ) (pow_pos (Nat.cast_pos.2 q.out.pos) e)]
  · -- Here `p ^ e ≥ x₁`, so the terms of the gain vanish, as every weight is at least `a / x₁`.
    have h_pow : D.x₁ ≤ p ^ e := (Nat.le_ceil D.x₁).trans <| mod_cast
      (le_pow_clog q.out.one_lt _).trans (Nat.pow_le_pow_right q.out.pos (by simpa using h_small))
    have h_zero {y : ℝ} (hy : y ≤ D.a) (σ : D.Φ) : (y / p ^ e - D.weight σ)⁺ = 0 :=
      posPart_eq_zero.2 <| sub_nonpos.2 <|
        (div_le_div₀ (Nat.cast_nonneg _) hy (HasLogBound.pos D) h_pow).trans (D.weight_mem_Icc σ).1
    have h_ne : e ≠ 1 := fun h_one ↦ hp.1.not_ge (by simpa [h_one] using h_pow)
    simp only [h_zero le_rfl, h_zero (D.le_of_hasLogBound : (D.weight τ : ℝ) ≤ D.a), h_ne, h_small,
      false_and, ite_false, ite_self, mul_zero, add_zero, ← add_assoc, sub_add_cancel]
    positivity

/-- **Only collisions lose.** Let the prime `p` be below the cut-off `x₁` and non-split in
`K = ℚ(√-d)`, let `j < m`, the number of lifts, and let `S` be any set of infinite places of `E`.
The bound `divisibilityBound p j S` is the predicted divisibility at `p` of the diagrams
`D.columnCount`, read below height `n_{j+1}` and with the columns of height one at `S` removed, plus
`γ_p` for each removed box, less a logarithmic term. It is at least
`gain p / m = ∑_τ s_p(a, τ) + k ∑_σ s_p(w(σ), σ)` (with `τ` an a-place, that is, of class `1` modulo
`q₀`, `σ` any place, `s_p = localPrimeSum p` and `w = D.weight`), less `collisionSum p S`, the sum
of `a / p ^ e` over the pairs `(τ, e)` with `e ∈ I_p` and both `τ` and `(-p ^ e) τ` a-places outside
`S`, plus `v(π_p) a / x₁` for each a-place in `S`, less `f a (log b)² / (m p)`. Here
`v(π_p) = piPrimeValuation P.d p`, `a = x b` is the length of a long row, `log b = D.logB`, and `f`
is the number of infinite places of `E`. -/
lemma le_divisibilityBound (hj : j < D.m) (hp : D.IsSmallNonsplit p) (S : Finset D.Φ) :
    D.gain p / D.m - D.collisionSum p S +
        piPrimeValuation P.d p * #(D.aPlaces ∩ S) * (D.a / D.x₁) -
        D.f * D.logB ^ 2 * (D.a / p) / D.m ≤
      D.divisibilityBound p j S := by
  classical
  -- Put `u = a / (p m)`. Apart from collisions the losses at one place add up to at most `5 u`.
  -- The sizes of the rank and of `p`, as instances for `D.le_of_hasLogBound`.
  have := D.hasLogUpper_of_le (D.n_mono hj)
  have hp_size : D.HasLogUpper p D.logX₁ := D.hasLogUpper_of_le_of_nonneg hp.1.le p.cast_nonneg
  set u : ℝ := D.a / p / D.m with hu
  set γ : ℝ := gammaPrime P.d p
  set v : ℝ := piPrimeValuation P.d p
  have hv_le : v ≤ 1 := piPrimeValuation_le_one P.d p
  have h_err : v * (clog p ⌈D.x₁⌉₊ * (2 * D.x ^ 60)) ≤ u := by
    grw [hv_le, one_mul, clog_le_of_le_pow (Nat.lt_pow_self q.out.one_lt).le,
      Nat.ceil_lt_add_one (HasLogBound.pos D).le]
    exact D.le_of_hasLogBound
  have h_place (τ : D.Φ) :
      (if τ ∈ D.aPlaces then D.localPrimeSum p D.a τ else 0) +
          D.k * D.localPrimeSum p (D.weight τ) τ +
          v * (if τ ∈ D.aPlaces ∩ S then D.a / D.x₁ else 0) ≤
        v * ∑' e, partnerTerm p j S τ e + γ * (if τ ∈ D.aPlaces ∩ S then (D.a : ℝ) else 0) +
          (∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) + 2 * u := by
    -- A collision costs at most `v ≤ 1` times its term.
    linarith [localPrimeSum_add_le_mul_tsum_partnerTerm_add hj hp S τ,
      gammaPrime_mul_lowColumns_le (p := p) hj τ,
      mul_le_of_le_one_left (tsum_nonneg fun e ↦ by positivity :
        0 ≤ ∑' e : ℕ, if D.IsCollision p S τ e then (D.a / p ^ e : ℝ) else 0) hv_le]
  have h_sum : ∑ τ ∈ D.aPlaces, D.localPrimeSum p D.a τ + D.k * D.localPrimeSumTotal p +
        v * #(D.aPlaces ∩ S) * (D.a / D.x₁) ≤
      v * ∑ τ, ∑' e, partnerTerm p j S τ e + γ * (#(D.aPlaces ∩ S) * D.a) + D.collisionSum p S +
        D.f * (2 * u) := by
    simpa [sum_add_distrib, ← mul_sum, localPrimeSumTotal, collisionSum, mul_assoc, mul_left_comm,
      f,
      Core.numInfPlaces, -mem_inter, Finset.univ_inter _] using
      sum_le_sum (s := univ) fun τ _ ↦ h_place τ
  have h_count : D.n (j + 1) ^ 3 * (1 + logb p (max (boxes D.columnCount (D.n (j + 1))) 1 : ℕ)) ≤
    u := by
    grw [one_add_logb_boxes_le hj]
    exact D.le_of_hasLogBound
  have h_losses : D.f * (5 * u) ≤ D.f * D.logB ^ 2 * (D.a / p) / D.m := by
    grw [mul_div_assoc, mul_assoc, ← hu, (D.le_of_hasLogBound : 5 ≤ D.logB ^ 2)]
  rw [divisibilityBound, boxes_sub_boxes_eraseHeightOne, gain,
    mul_div_cancel_left₀ _ (HasLogBound.pos D).ne', mul_assoc (D.f : ℝ) (_ ^ 3)]
  have h_predicted : v * ∑ τ, ∑' e, partnerTerm p j S τ e - D.f * (2 * u) ≤
      predictedDivisibility P.d p (P.partner D.towerExp p) (eraseHeightOne D.columnCount S)
        (D.n (j + 1)) :=
    sub_le_predictedDivisibility (p := p) hj S
  linarith [mul_le_mul_of_nonneg_left h_count (D.f.cast_nonneg (α := ℝ))]

end DivisibilityBound

end New.Data

end
end
end

/-!
# Marked primes above `p`, full marks and the scaled Hecke operator

Fix a prime `p` and an embedding `ι : ℂ → ℂ_[p]`. Each infinite place of `E` then induces a prime
above `p`. A finite set `Λ` of such primes is marked if it is disjoint from its conjugate and each
member is induced by an a-place; the definition also asks that `p` be exceptional and below `x₁`.
A *full mark* is a marked set that contains, for each a-place, the prime it induces or the
conjugate of that prime.
This file shows that a full mark exists and defines, with `A_𝔩` the number
`New.Data.heckeScalingExponent` of a prime `𝔩`, a scaled Hecke operator on the space
`D.SourceForm` of source forms.

## Main definitions and results

* `New.Data.IsFullMark`: a marked set that meets each pair of a prime induced by an a-place and its
  conjugate.
* `New.Data.exists_isFullMark`: a full mark exists for every exceptional `p < x₁`.
* `New.Data.IsMarked.scaledHeckeOperator`: the operator `p ^ A_𝔩 • T_{𝔩,𝔯}` at a marked prime, on
  the space of source forms.

Notions from other files:
* `New.Data.aPlaces`: The `a`-places: the infinite places of `E` whose class in `(ℤ/q₁)ˣ` is `1`
  modulo `q₀`.
* `New.Data.IsExceptional`, `New.Data.ceilLogLifts`: A condition on `p` alone: `(p/d) = -1`,
  `p ≢ ±1` modulo `m`, and the order `o₀` of `-p` modulo `q₀` is odd and at most `𝔯`, the least
  natural number with `m ≤ p^𝔯`.
* `New.placeOfEmb`: The prime of `E` induced by an embedding `σ : E →+* F` into an ultrametric
  normed field over `ℚ_p`: the centre on the integers of `E` of the valuation ring
  `{x : E | ‖σ x‖ ≤ 1}`.
* `New.Data.placeOfInt`: The infinite place of E named by the class of the integer ν modulo q₁ if ν
  is prime to q₁, and the identity place otherwise.
* `New.Data.lowColumns`: the number of columns at `τ` of height below `n_{j+1}` and different
  from `1`.
-/

@[expose] public section

noncomputable section

namespace New.Data

/-! ## Induced primes and marked sets -/

section MarkedDefs

open Finset

variable {P : Parameters} {D : Data P} {p : ℕ} [Fact p.Prime] [PadicPlace p]
  (Λ : Finset (FinPlace D.E))

/-- The prime of `E` above `p` induced by the embedding `ι ∘ σ` of `E` into `ℂ_p`, where the
infinite place `σ` is read as the embedding of `E` into `ℂ` that the CM type selects. -/
def inducedPlace (σ : D.Φ) : FinPlace D.E := placeOfEmb (ιₚ.comp (Φ σ))

/-- A marked set of primes of `E` at `ι`: `Λ` is disjoint from its complex conjugate, and each prime
of `Λ` is induced by an a-place. Moreover `p` is exceptional and below `x₁`. -/
structure IsMarked where
  /-- `Λ` is disjoint from its complex conjugate. -/
  star_notMem : ∀ l ∈ Λ, star l ∉ Λ
  /-- `p` is exceptional. -/
  isExceptional : D.IsExceptional p
  /-- Each prime of `Λ` is induced by an a-place. -/
  induced_by_aPlace : ∀ l ∈ Λ, ∃ τ ∈ D.aPlaces, inducedPlace τ = l
  /-- `p` is below `x₁` and `χ_K(p) ≠ 1`. -/
  isSmallNonsplit : D.IsSmallNonsplit p

/-- A full mark: a marked set that contains, for each a-place `τ`, the prime induced by `τ` or its
conjugate. -/
structure IsFullMark extends D.IsMarked Λ where
  /-- For each a-place, `Λ` contains its induced prime or the conjugate of that prime. -/
  mem_or_star_mem : ∀ τ ∈ D.aPlaces, inducedPlace τ ∈ Λ ∨ star (inducedPlace τ) ∈ Λ

/-- The module of integral source forms: the elements of `D.SourceForm` of gauge at most `1`. -/
abbrev integralSourceForms : Submodule embValRing D.SourceForm :=
  (integralFormsAt D.SourceForm 1).comap (D.SourceForm.subtype.restrictScalars embValRing)

open scoped Classical in
/-- The places inducing a prime of `Λ`: the infinite places of `E` whose induced prime above `p`
lies in `Λ`. -/
abbrev placesInducing : Finset D.Φ := {σ : D.Φ | inducedPlace σ ∈ Λ}

open scoped Classical in
/-- The places inducing the conjugate of a prime of `Λ`: the infinite places of `E` whose induced
prime above `p` is conjugate to a prime of `Λ`. -/
abbrev placesInducingConj : Finset D.Φ := {σ : D.Φ | star (inducedPlace σ) ∈ Λ}

open scoped Classical in
/-- The number `A_𝔩`: the integer `D.a` times the number of a-places (places of class `1` modulo
`q₀`) that induce the prime `𝔩` at `ι`. -/
def heckeScalingExponent (l : FinPlace D.E) : ℕ := D.a * #{τ ∈ D.aPlaces | inducedPlace τ = l}

/-- The numbers `A_𝔩` for `𝔩 ∈ Λ` add up to `a` times the number of a-places whose induced prime
lies in `Λ`. -/
lemma sum_heckeScalingExponent : ∑ l ∈ Λ,
  heckeScalingExponent l = D.a * #(D.aPlaces ∩ placesInducing Λ) := by
  classical
  simp only [heckeScalingExponent, ← mul_sum, inter_filter, inter_univ]
  -- The `convert` only matches the decidability instances of the two filters.
  convert congrArg (D.a * ·) (sum_card_fiberwise_eq_card_filter D.aPlaces Λ inducedPlace) using 4

end MarkedDefs

/-! ## Existence and properties of marked sets above a non-split prime -/

section MarkedPrimes

open Finset Parameters Real Nat

variable {P : Parameters} {D : Data P} {p : ℕ} [hq : Fact p.Prime]

/-- An exceptional prime is inert in `K`: its Legendre symbol `(p/d)` is `-1`. -/
lemma IsExceptional.chiK_eq_neg_one {p : ℕ} (h : D.IsExceptional p) : chiK P.d p = -1 := h.1

/-- For an exceptional prime `p` the order `o₀` of `-p` modulo `q₀` is odd. -/
lemma IsExceptional.odd_o₀ {p : ℕ} (h : D.IsExceptional p) : Odd (D.o₀ p) := by
  grind [IsExceptional]

/-- `D.ceilLogLifts p`, the least natural number `k` with `m ≤ p ^ k`, is at most `D.towerExp`, the
exponent `s` with `2 ^ s = m ^ 22`. -/
lemma ceilLogLifts_le_towerExp : D.ceilLogLifts p ≤ D.towerExp := by
  obtain ⟨e, hm, hs⟩ := D.exists_m_eq_two_pow
  refine clog_le_of_le_pow (hm.trans_le ?_)
  exact (Nat.pow_le_pow_right two_pos (by lia)).trans (Nat.pow_le_pow_left hq.out.two_le D.towerExp)

/-- The least `r` with `m ≤ p ^ r` is at most `l₀`, the least power of `3` above `27 s`, because
`m ≤ 2 ^ l₀`. -/
lemma ceilLogLifts_le_l₀ : D.ceilLogLifts p ≤ l₀ D.towerExp := by
  refine clog_le_of_le_pow ?_
  calc D.m ≤ D.m ^ 594 := Nat.le_self_pow (by norm_num) _
    _ ≤ 2 ^ l₀ D.towerExp := D.m_pow_le_two_pow_l₀
    _ ≤ p ^ l₀ D.towerExp := Nat.pow_le_pow_left hq.out.two_le _

/-- The number `ceilLogLifts p`, the least `𝔯` with `m ≤ p ^ 𝔯`, is bounded in order of magnitude by
`log (log x₁)`: it is at most `s` (`ceilLogLifts_le_towerExp`). -/
instance : D.HasLogUpper (D.ceilLogLifts p) (Real.log D.logX₁) :=
  D.hasLogUpper_of_le (A := D.towerExp) ceilLogLifts_le_towerExp

/-- If `2 ^ s` divides a product of two natural numbers, where `2 * e < s`, and `2 ^ (e + 1)` does
not divide the first factor, then `2 ^ (e + 1)` divides the second. -/
lemma two_pow_dvd_right_of_dvd_mul {e s q o : ℕ} (hs : 2 * e < s) (h_dvd : 2 ^ s ∣ q * o)
    (hq : ¬2 ^ (e + 1) ∣ q) : 2 ^ (e + 1) ∣ o := by
  -- Compare `2`-adic valuations: that of `q` is at most `e`, that of `q * o` at least `s`.
  simp only [multiplicity_dvd_iff, mul_eq_zero, not_or, not_le] at h_dvd hq ⊢
  grind [Nat.multiplicity_mul]

/-- Let `p` be an exceptional prime: inert in `K = ℚ(√-d)`, not congruent to `±1` modulo the number
`m` of lifts, and such that the order `o₀` of `-p` modulo `q₀` is odd and at most `ceilLogLifts p`,
the least `r` with `m ≤ p ^ r`. Then the power of two `m` divides the order of `D.placeOfInt (-p)`,
the class of `-p` in the group `Gal(E/K) = (ℤ/q₁)ˣ` of infinite places of `E = K(ζ_{q₁})`. -/
lemma IsExceptional.m_dvd_orderOf (h : D.IsExceptional p) : D.m ∣ orderOf (D.placeOfInt (-p)) := by
  -- With `o` the order of `-p`, lifting the exponent gives `2 ^ s ∣ (-p ± 1) * o`. Here `m` is a
  -- power of `2`, `2 ^ s = m ^ 22` and `m` does not divide `p ± 1`, so `m` divides `o`.
  obtain ⟨e, (hm : D.m = 2 ^ (e + 1)), (hs : D.towerExp = (e + 1) * 22)⟩ := D.exists_m_eq_two_pow
  obtain ⟨(h_inert : chiK P.d p = -1), (h_not_pm_one : ¬D.IsPlusMinusOneModLifts p), -⟩ := h
  set o : ℕ := orderOf (D.placeOfInt (-p))
  have h_not_dvd : ¬p ∣ P.q₁ 0 := by grind [not_dvd_q₁_mul_d_of_inert h_inert (s := 0)]
  have h_pow : ((-p : ℤ) : ZMod (2 ^ (D.towerExp + 1))) ^ o = 1 := by
    rw [← placeClass_placeOfInt (h_dvd := two_pow_dvd_q₁)
        (isCoprime_q₀_of_not_dvd h_not_dvd).neg_left,
      ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  obtain ⟨h_sub, h_add⟩ : ¬2 ^ (e + 1) ∣ p - 1 ∧ ¬2 ^ (e + 1) ∣ p + 1 := by
    simpa [IsPlusMinusOneModLifts, hm] using h_not_pm_one
  have hp_one : 1 ≤ p := hq.out.one_le
  rw [hm]
  rcases two_pow_dvd_or_of_pow_eq_one (orderOf_pos _) h_pow with h_dvd | h_dvd <;>
    rw [hm, ← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at *
  · rw [show ((-p : ℤ) - 1).natAbs = p + 1 by lia] at h_dvd
    exact two_pow_dvd_right_of_dvd_mul (by lia) h_dvd h_add
  · rw [show ((-p : ℤ) + 1).natAbs = p - 1 by lia] at h_dvd
    exact two_pow_dvd_right_of_dvd_mul (by lia) h_dvd h_sub

/-- For an exceptional prime `p`, no prime `w` of `E` above `p` is equal to its complex
conjugate. -/
lemma IsExceptional.star_ne (h : D.IsExceptional p) {w : FinPlace D.E} (hw : ↑p ∈ w.asIdeal) :
    star w ≠ w := by
  -- The places that send `w` to its conjugate are the odd powers of `-p`. The order of `-p` is
  -- even, so the identity is not one of them.
  intro h_eq
  -- The action on primes is a bare `SMul`, so `one_smul` does not apply.
  have h_one : (1 : D.Φ) • w = w := (smul_eq_self_iff_of_inert hw h.chiK_eq_neg_one).2 ⟨0, by simp⟩
  obtain ⟨i, hi_eq, hi_odd⟩ : ∃ i : ℕ, 1 = D.placeOfInt (-p) ^ i ∧ Odd i :=
    (smul_eq_star_iff_of_inert hw h.chiK_eq_neg_one).1 (h_one.trans h_eq.symm)
  exact hi_odd.not_two_dvd_nat
    ((D.m_even.two_dvd.trans h.m_dvd_orderOf).trans (orderOf_dvd_of_pow_eq_one hi_eq.symm))

/-- A non-split prime `p < x₁` divides neither `D.M` (the product of the two level primes
`D.levelPrime i`) nor `D.M * D.N`, and differs from `N`: the prime factors of `D.M * D.N` are at
least `x₁`. -/
lemma IsSmallNonsplit.not_dvd_M_mul_N (h : D.IsSmallNonsplit p) :
    ¬p ∣ D.M ∧ p ≠ D.N ∧ ¬p ∣ D.M * D.N := by
  have hN : D.x₁ ≤ D.N := D.le_of_hasLogBound
  have hg (i : Fin 2) : D.x₁ ≤ D.levelPrime i := D.le_of_hasLogBound
  have h_ne : p ≠ D.levelPrime 0 ∧ p ≠ D.levelPrime 1 ∧ p ≠ D.N := by grind [h.1]
  grind [M, hq.out, levelPrime_prime, N_prime, Nat.Prime.dvd_mul, Nat.prime_dvd_prime_iff_eq]

variable (D) [PadicPlace p]

/-! ### Induced primes and the existence of a marked set -/

/-- The prime induced by an infinite place lies above `p`. -/
lemma p_mem_inducedPlace (σ : D.Φ) : ↑p ∈ (D.inducedPlace σ).asIdeal := natCast_mem_placeOfEmb _

/-- Multiplying `σ` by `τ` pulls the induced prime back along `τ` in `Gal(E/K)`, that is, moves it
by `τ⁻¹`. The action `•` of infinite places on primes is this pullback. -/
lemma inducedPlace_mul (σ τ : D.Φ) : D.inducedPlace (σ * τ) = τ • inducedPlace σ := by
  ext
  simp [inducedPlace, phi_mul]

/-- For p inert in K and e odd, the prime induced by (−p^e)σ is the conjugate of the prime
induced by σ. -/
lemma inducedPlace_neg_pow_mul_of_odd (h_inert : chiK P.d p = -1) {e : ℕ} (he : Odd e) (σ : D.Φ) :
    D.inducedPlace (D.placeOfInt (-p ^ e) * σ) = star (inducedPlace σ) := by
  rw [mul_comm, inducedPlace_mul]
  exact (smul_eq_star_iff_of_inert (D.p_mem_inducedPlace σ) h_inert).2
    ⟨e, by rw [placeOfInt_pow, he.neg_pow], he⟩

/-- Let `p` be a prime below the cut-off `x₁` that is exceptional: `(p/d) = -1`, `p ≢ ±1` modulo
`m`, and the order of `-p` modulo `q₀` is odd and at most `ceilLogLifts p`, the least `r` with
`m ≤ p ^ r`. Then there is a full mark: a finite set of primes of `E` induced by a-places and
disjoint from its conjugate, which contains `𝔩` or its conjugate for each prime `𝔩` induced by an
a-place. -/
lemma exists_isFullMark (hp_lt : p < D.x₁) (h_exceptional : D.IsExceptional p) :
    ∃ Λ : Finset (FinPlace D.E), D.IsFullMark Λ := by
  -- Take the primes induced by a-places that are smaller than their conjugates, for some linear
  -- order on the primes.
  obtain ⟨(_ : LinearOrder (FinPlace D.E)), -⟩ := exists_wellFoundedLT (FinPlace D.E)
  refine ⟨{l ∈ D.aPlaces.image inducedPlace | l < star l},
    { star_notMem := by grind [star_star], isExceptional := h_exceptional,
      induced_by_aPlace := by grind,
      isSmallNonsplit := ⟨hp_lt, by simp [h_exceptional.chiK_eq_neg_one]⟩ }, fun τ hτ ↦ ?_⟩
  -- As `o₀` is odd, `-p ^ o₀ * τ` is an a-place that induces the conjugate prime.
  grind [star_star, (D.placeOfInt_mul_mem_aPlaces_iff h_exceptional.odd_o₀ τ hτ).2 dvd_rfl,
    D.inducedPlace_neg_pow_mul_of_odd h_exceptional.chiK_eq_neg_one h_exceptional.odd_o₀ τ,
    h_exceptional.star_ne (D.p_mem_inducedPlace τ)]

variable {D} {Λ : Finset (FinPlace D.E)} {l : FinPlace D.E}

/-- Let `p` be a prime with `(p/d) = -1`. Two places induce the same prime or conjugate primes
exactly when they differ by a power of `D.placeOfInt (-p)`, the place of the class of `-p` modulo
`q₁`. -/
lemma inducedPlace_eq_or_star_iff (h_inert : chiK P.d p = -1) (σ τ : D.Φ) :
    D.inducedPlace σ = inducedPlace τ ∨ inducedPlace σ = star (inducedPlace τ) ↔
      ∃ i : ℕ, σ = D.placeOfInt (-p) ^ i * τ := by
  -- Even powers of `-p` fix a prime above `p` (`smul_eq_self_iff_of_inert`), odd powers conjugate
  -- it.
  have h_div : inducedPlace σ = (σ / τ) • inducedPlace τ := by
    rw [← inducedPlace_mul, mul_div_cancel]
  rw [h_div, smul_eq_self_iff_of_inert (D.p_mem_inducedPlace τ) h_inert,
    smul_eq_star_iff_of_inert (D.p_mem_inducedPlace τ) h_inert]
  grind [Nat.even_or_odd, div_eq_iff_eq_mul]

/-- The properties of the orbits of the place named by `-p` that hold at an exceptional prime `p`.
Write `o₀ = D.o₀ p` for the order of `-p` modulo `q₀`, `o` for the order of the place named by `-p`
and `r = D.ceilLogLifts p` for the least number with `m ≤ p ^ r`. -/
structure HasExceptionalOrbits (D : Data P) (p : ℕ) [Fact p.Prime] [PadicPlace p] : Prop where
  /-- `o₀` is odd. -/
  odd_o₀ : Odd (D.o₀ p)
  /-- `o₀ ≤ r`. -/
  o₀_le_ceilLogLifts : D.o₀ p ≤ D.ceilLogLifts p
  /-- `m` divides `o`. -/
  m_dvd_orderOf : D.m ∣ orderOf (D.placeOfInt (-p))

/-- Let `p` be an exceptional prime: `(p/d) = -1`, `p ≢ ±1` modulo `m`, and the order `o₀` of `-p`
modulo `q₀` is odd and at most `r = ceilLogLifts p`, the least number with `m ≤ p ^ r`. Then the
properties of `New.Data.HasExceptionalOrbits` hold: `o₀` is odd, `o₀ ≤ r`, and the order `o` of
the place named by `-p` is a multiple of `m`. -/
theorem IsExceptional.hasExceptionalOrbits (h : D.IsExceptional p) :
    D.HasExceptionalOrbits p where
  odd_o₀ := h.odd_o₀
  o₀_le_ceilLogLifts := by grind [IsExceptional]
  m_dvd_orderOf := h.m_dvd_orderOf

/-! ### Properties of marked sets -/

/-- A marked set has at most `f` primes, `f` being the number of infinite places of `E`: each of its
primes is induced by one of them. -/
lemma IsMarked.card_le (h : D.IsMarked Λ) : #Λ ≤ D.f :=
  card_le_card_of_surjOn inducedPlace fun l hl ↦
    (h.induced_by_aPlace l hl).imp fun τ hτ ↦ ⟨mem_univ τ, hτ.2⟩

/-- For a marked set `Λ`, the prime `p` divides neither `D.M` nor `D.M * D.N`, and differs
from `N`. -/
lemma IsMarked.not_dvd_M_mul_N (h : D.IsMarked Λ) : ¬p ∣ D.M ∧ p ≠ D.N ∧ ¬p ∣ D.M * D.N :=
  h.isSmallNonsplit.not_dvd_M_mul_N

/-- If `Λ` is a marked set above `p`, multiplying a place by the place named by `-p` conjugates the
induced prime, because `p` is inert in `K`. -/
lemma IsMarked.inducedPlace_placeOfInt_neg_mul (h : D.IsMarked Λ) (σ : D.Φ) :
    inducedPlace (D.placeOfInt (-p) * σ) = star (inducedPlace σ) := by
  simpa using D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one odd_one σ

/-- For a marked set `Λ` and odd `e`, multiplication by the place named by `-p ^ e` carries the
places whose conjugate induced prime lies in `Λ` onto the places whose induced prime lies in `Λ`. -/
lemma IsMarked.neg_pow_mul_mem_placesInducing_iff (h : D.IsMarked Λ) {e : ℕ} (he : Odd e)
    (σ : D.Φ) :
    D.placeOfInt (-p ^ e) * σ ∈ placesInducing Λ ↔ σ ∈ placesInducingConj Λ := by
  simp [D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one he]

/-- For a marked set `Λ` and odd `e`, multiplication by the place named by `-p ^ e` carries the
places whose induced prime lies in `Λ` onto the places whose conjugate induced prime lies in `Λ`. -/
lemma IsMarked.neg_pow_mul_mem_placesInducingConj_iff (h : D.IsMarked Λ) {e : ℕ} (he : Odd e)
    (σ : D.Φ) :
    D.placeOfInt (-p ^ e) * σ ∈ placesInducingConj Λ ↔ σ ∈ placesInducing Λ := by
  simp [D.inducedPlace_neg_pow_mul_of_odd h.isExceptional.chiK_eq_neg_one he]

/-- Let `Λ` be a marked set of primes of `E`: in particular each prime of `Λ` is induced by an
a-place, and `p` is exceptional, so it is inert in `K` and `-p` has odd order modulo `q₀`. If
`inducedPlace σ` or its conjugate lies in `Λ`, then `σ` is not a b-place. -/
lemma IsMarked.notMem_bPlaces (h : D.IsMarked Λ) (σ : D.Φ)
    (hσ : inducedPlace σ ∈ Λ ∨ star (inducedPlace σ) ∈ Λ) : σ ∉ D.bPlaces := by
  intro h_bPlace
  -- An a-place induces the prime of `σ` or its conjugate, so it lies on the `-p`-orbit of `σ`.
  obtain ⟨τ, h_aPlace, h_ind⟩ : ∃ τ ∈ D.aPlaces, inducedPlace τ = inducedPlace σ ∨
      inducedPlace τ = star (inducedPlace σ) := by grind [h.induced_by_aPlace]
  obtain ⟨i, rfl⟩ := (inducedPlace_eq_or_star_iff h.isExceptional.chiK_eq_neg_one τ σ).1 h_ind
  -- Modulo `q₀`, `(-p) ^ i ≡ -1`; raising to the odd order `o₀` of `-p` gives `-1 ≡ 1`.
  have h_neg : -P.placeClass (P.q₀.dvd_mul_right _) (D.placeOfInt (-p)) ^ i = 1 := by
    simpa [aPlaces, placeClass_of_mem_bPlaces, h_bPlace] using h_aPlace
  have h_neg := congrArg (· ^ D.o₀ p) h_neg
  rw [h.isExceptional.odd_o₀.neg_pow, pow_right_comm, o₀, pow_orderOf_eq_one] at h_neg
  exact P.d_pow_ne_neg_one 0 (by simpa using congrArg Units.val h_neg.symm)

/-- At a place whose induced prime, or its conjugate, lies in a marked set, the weight is `a / x₁`,
because such a place is not a b-place. -/
lemma IsMarked.cast_weight_eq (h : D.IsMarked Λ) (σ : D.Φ)
    (hσ : inducedPlace σ ∈ Λ ∨ star (inducedPlace σ) ∈ Λ) :
    (D.weight σ : ℝ) = D.a / D.x₁ := by
  rw [cast_weight, ite_eq_right (h.notMem_bPlaces σ hσ)]

open scoped Classical in
/-- Let `l` be a prime of a set `Λ` that is marked: it is disjoint from its conjugate, its primes
are induced by a-places, and `p < x₁` is exceptional. For any function `G`, the sum of
`G (D.liftWeight j τ)` over the places `τ` that induce `l` equals the sum over the places that
induce the conjugate of `l`. Here `D.liftWeight j τ = D.weight τ + (j + 1/2) D.gap` is the weight at
`τ` of the character of the `j`-th lift in the chain. -/
lemma IsMarked.sum_inducedPlace_eq_sum_star (h : D.IsMarked Λ) (hl : l ∈ Λ) (j : ℕ) (G : ℕ → ℝ) :
    ∑ τ : D.Φ with inducedPlace τ = l, G (D.liftWeight j τ) =
      ∑ τ : D.Φ with inducedPlace τ = star l, G (D.liftWeight j τ) := by
  -- Multiplication by the place named by `-p` carries the places inducing `l` onto those inducing
  -- its conjugate.
  refine sum_equiv (.mulLeft (D.placeOfInt (-p)))
    (fun τ ↦ by simp [h.inducedPlace_placeOfInt_neg_mul]) fun τ hτ ↦ ?_
  have h_mem : inducedPlace τ ∈ Λ := by rwa [(mem_filter.1 hτ).2]
  -- Both `τ` and `-p τ` have the weight `a / x₁`.
  have h_weight : (D.weight τ : ℝ) = D.weight (D.placeOfInt (-p) * τ) := by
    simp [h.cast_weight_eq, h.inducedPlace_placeOfInt_neg_mul, h_mem]
  simp [liftWeight_eq, Nat.cast_injective h_weight]

open scoped Classical in
/-- Let the set `Λ` of primes of `E` be marked: it is disjoint from its conjugate, its primes are
induced by a-places, and `p < x₁` is exceptional. Let `w_j(τ) = D.liftWeight j τ` be the weight at
`τ` of the character of the `j`-th lift. For any function `G` of a weight and a prime, the sum of
`G (w_j(τ), 𝔩)` over the places `τ` whose induced prime `𝔩` lies in `Λ` (`placesInducing Λ`) equals
the sum of `G (w_j(τ), 𝔩̄)` over the places `τ` for which the conjugate `𝔩̄` of the induced prime
lies in `Λ`. -/
lemma IsMarked.sum_placesInducing_eq_sum_placesInducingConj (h : D.IsMarked Λ) (j : ℕ)
    (G : ℕ → FinPlace D.E → ℝ) :
    ∑ τ ∈ placesInducing Λ, G (D.liftWeight j τ) (inducedPlace τ) =
      ∑ τ ∈ placesInducingConj Λ, G (D.liftWeight j τ) (star (inducedPlace τ)) := by
  -- Group each sum by the prime of `Λ` that occurs, and use the balance at that prime.
  have h_group (f : D.Φ → FinPlace D.E) :
      ∑ τ : D.Φ with f τ ∈ Λ, G (D.liftWeight j τ) (f τ) =
        ∑ l ∈ Λ, ∑ τ : D.Φ with f τ = l, G (D.liftWeight j τ) l := by
    simp_rw [sum_filter]
    rw [sum_comm]
    simp
  rw [h_group, h_group fun τ ↦ star (inducedPlace τ)]
  refine sum_congr rfl fun l hl ↦ ?_
  simp [h.sum_inducedPlace_eq_sum_star hl j fun c ↦ G c l,
    star_eq_iff_star_eq (r := inducedPlace _), eq_comm (a := star l)]

open scoped Classical in
/-- The balance `IsMarked.sum_placesInducing_eq_sum_placesInducingConj` as one sum over all infinite
places `τ`: with `𝔩 = inducedPlace τ`, add `G (D.liftWeight j τ) 𝔩` if `𝔩 ∈ Λ` and subtract
`G (D.liftWeight j τ) (star 𝔩)` if `star 𝔩 ∈ Λ`. The total is zero. -/
lemma IsMarked.sum_inducedPlace_sub_star_eq_zero (h : D.IsMarked Λ) (j : ℕ)
    (G : ℕ → FinPlace D.E → ℝ) :
    ∑ τ : D.Φ, ((if inducedPlace τ ∈ Λ then G (D.liftWeight j τ) (inducedPlace τ) else 0) -
      (if star (inducedPlace τ) ∈ Λ then G (D.liftWeight j τ) (star (inducedPlace τ)) else 0)) =
        0 := by
  simp [sum_sub_distrib, ← sum_filter, h.sum_placesInducing_eq_sum_placesInducingConj j G]

/-- A prime of a marked set lies above `p`. -/
lemma IsMarked.natCast_mem_asIdeal (h : D.IsMarked Λ) (hl : l ∈ Λ) : ↑p ∈ l.asIdeal := by
  obtain ⟨τ, -, rfl⟩ := h.induced_by_aPlace l hl
  exact D.p_mem_inducedPlace τ

/-- For a marked set `Λ` (`D.IsMarked Λ`) and `l ∈ Λ`, `p` is a uniformiser at `l`: its `l`-adic
valuation is `exp (-1)`. The reason is that the prime `p` of a marked set divides neither `q₁` nor
`d`. -/
lemma IsMarked.valuation_natCast_eq_exp_neg_one (h : D.IsMarked Λ) (hl : l ∈ Λ) :
    l.valuation D.E p = WithZero.exp (-1) := by
  -- `l` lies above `p`, which is inert in `K` and so does not divide `q₁ * d`: it is unramified.
  rw [← map_natCast (algebraMap (NumberField.RingOfIntegers D.E) D.E), l.valuation_of_algebraMap]
  exact intValuation_natCast_eq_exp_neg_one (h.natCast_mem_asIdeal hl)
    (not_dvd_q₁_mul_d_of_inert h.isExceptional.chiK_eq_neg_one)

/-- Every prime `l` of a marked set `Λ` (disjoint from its complex conjugate, each prime induced by
an a-place) is split (`l.IsSplit`): `l` differs from its complex conjugate. -/
lemma IsMarked.isSplit (h : D.IsMarked Λ) (hl : l ∈ Λ) : l.IsSplit :=
  fun h_eq : star l = l ↦ h.star_notMem l hl (by rwa [h_eq])

/-- Let `Λ` be a marked set of primes of `E` above `p` and `l ∈ Λ`. In the finite adelic unitary
group with basis indexed by `D.X 0`, the group `maxCompactAt (D.X 0) l` of elements of the standard
maximal compact subgroup that are trivial away from `l` and `star l` lies in `D.levelX 0`, the level
that fixes the forms of `D.SourceForm`. -/
lemma IsMarked.maxCompactAt_le_levelX (h : D.IsMarked Λ) (hl : l ∈ Λ) :
    maxCompactAt (D.X 0) l ≤ D.levelX 0 := by
  -- Neither `l` nor its conjugate contains `piM * piN`, whose norm `M * N` is prime to `p`.
  have h_notMem (v : FinPlace D.E) (hv : ↑p ∈ v.asIdeal) : D.piM * D.piN ∉ v.asIdeal := by
    intro h_mem
    have h_norm : ((D.M * D.N : ℕ) : NumberField.RingOfIntegers D.E) ∈ v.asIdeal := by
      rw [Nat.cast_mul, ← piM_mul_star, ← piN_mul_star, mul_mul_mul_comm]
      exact v.asIdeal.mul_mem_right _ h_mem
    obtain ⟨-, -, h_ndvd⟩ := h.not_dvd_M_mul_N
    exact h_ndvd ((v.natCast_mem_iff_dvd hv).1 h_norm)
  have h_le : maxCompactAt (D.X 0) l ≤ principalLevel (D.X 0) (D.piM * D.piN) := by
    refine inf_supportedOn_le_principalLevel fun w hw ↦ ?_
    obtain rfl : w = l := hw
    exact ⟨h_notMem w (h.natCast_mem_asIdeal hl),
      h_notMem (star w) (by simpa [mem_star_place] using h.natCast_mem_asIdeal hl)⟩
  exact h_le.trans (D.principalLevel_le_levelX 0)

/-- The operator `p ^ A_𝔩 • T_{𝔩,𝔯}` on `D.SourceForm`, as an endomorphism over `embValRing`; here
`T_{𝔩,𝔯}` is the Hecke operator at the marked prime `𝔩` of index `𝔯 = D.ceilLogLifts p`, which
preserves `D.SourceForm`. -/
noncomputable def IsMarked.scaledHeckeOperator (h : D.IsMarked Λ) (l : Λ) :
    Module.End embValRing D.SourceForm :=
  LinearMap.restrictScalars embValRing <|
    (p : ℂ) ^ heckeScalingExponent l.val •
      (heckeSplit (algFormRep D.columnCount (D.lastEntry 0)) (h.isSplit l.property)
        (D.ceilLogLifts p)).restrict
        fun _ hv ↦
          -- a vector of level `D.levelX 0` is spherical at `l`, by
          -- `maxCompactAt_le_levelX`
          heckeSplit_mem_levelSpace _ (D.ceilLogLifts p)
            (levelSpace_anti (h.maxCompactAt_le_levelX l.property) hv) IsLevel.le hv

/-! ### Collisions and full marks -/

/-- Let `Λ` be a full mark: a marked set that contains, for each a-place, the induced prime or its
conjugate. A collision outside `placesInducing Λ` is a pair `(τ, e)` with `e` odd such that `τ` and
its product with the place `D.placeOfInt (-p ^ e)` are a-places that induce no prime of `Λ`. Then
`collisionSum`, the sum of `D.a / p ^ e` over these collisions, is zero. -/
lemma IsFullMark.collisionSum_placesInducing_eq_zero (h : D.IsFullMark Λ) :
    D.collisionSum p (placesInducing Λ) = 0 := by
  -- In a collision `(τ, e)` the a-place `τ` induces no prime of `Λ`, so it induces the conjugate of
  -- one. As `e` is odd, the partner `-p ^ e τ` then induces a prime of `Λ`: there is no collision.
  have h_none (τ : D.Φ) (e : ℕ) : ¬D.IsCollision p (placesInducing Λ) τ e := by
    intro hc
    obtain ⟨-, h_odd, -⟩ := hc.ne_and_odd_and_dvd
    obtain ⟨-, hτ, h_partner⟩ := hc
    obtain ⟨h_aPlace, h_notMem⟩ : τ ∈ D.aPlaces ∧ τ ∉ placesInducing Λ := mem_sdiff.1 hτ
    have h_conj : τ ∈ placesInducingConj Λ := by
      simpa using (h.mem_or_star_mem τ h_aPlace).resolve_left (by simpa using h_notMem)
    exact notMem_sdiff_of_mem_right
      ((h.toIsMarked.neg_pow_mul_mem_placesInducing_iff h_odd τ).2 h_conj) h_partner
  simp [collisionSum, h_none]

end MarkedPrimes

/-! ## The cost of the low columns at the places inducing `Λ` -/

section LowColumns

open Finset Real Nat

variable {P : Parameters} {D : Data P} {p : ℕ} [q : Fact p.Prime] {j : ℕ}

/-- Let `j < m`, the number of lifts, and let the set `Λ` of primes of `E` be marked: it is disjoint
from its conjugate, its primes are induced by a-places, and `p < x₁` is exceptional. Let `L` be the
number of low columns, those of height below the rank `n_{j+1}` and other than `1`, in the diagrams
`D.columnCount` at the places that induce a prime of `Λ`. Let `r = ceilLogLifts p` be least with
`m ≤ p ^ r`, and `ν_p = transferExponent p = r f (n_m + r)`, where `f` is the number of infinite
places and `n_i = D.n i`. Then `#Λ ν_p + r L` is at most `loss p / m`, plus `a / x₁` for each
a-place inducing a prime of `Λ`. Here `a = x b` is the product of two scales of the data, and
`loss p` is `f a (log b)² / p`, times `m` if `p ≡ ±1` modulo `m`. -/
lemma IsMarked.card_mul_transferExponent_add_sum_lowColumns_le (hj : j < D.m) [PadicPlace p]
    {Λ : Finset (FinPlace D.E)} (hΛ : D.IsMarked Λ) :
    #Λ * D.transferExponent p + D.ceilLogLifts p * ∑ σ ∈ placesInducing Λ, D.lowColumns j σ ≤
      D.loss p / D.m + #(D.aPlaces ∩ placesInducing Λ) * (D.a / D.x₁) := by
  -- The size of `p < x₁`, as an instance for `D.le_of_hasLogBound`.
  have hp_size : D.HasLogUpper p D.logX₁ :=
    D.hasLogUpper_of_le_of_nonneg hΛ.isSmallNonsplit.1.le p.cast_nonneg
  have hp : 0 < p := q.out.pos
  have h_place (σ : D.Φ) (hσ : σ ∈ placesInducing Λ) :
      D.ceilLogLifts p * (D.lowColumns j σ : ℝ) ≤ D.a / p / D.m + ite (σ ∈ D.aPlaces) (D.a / D.x₁)
        0 := by
    obtain ⟨h_inert, -, h_odd, h_order⟩ := hΛ.isExceptional
    -- A place inducing a prime of `Λ` is not a b-place, so it has about `a / x₁` low columns.
    grw [lowColumns_le hj σ, hΛ.cast_weight_eq σ (.inl (by simpa using hσ))]
    obtain hpm | hmp := le_total p D.m
    · grw [hpm]
      split <;> simpa using D.le_of_hasLogBound
    · -- Here `ceilLogLifts p = 1`, so the odd number `o₀ p ≤ ceilLogLifts p` is `1`: the orbit of
      -- the a-place that induces `inducedPlace σ` under `-p` consists of a-places, and `σ` lies on
      -- it.
      have h_one : D.ceilLogLifts p = 1 := clog_eq_one D.nat_le_of_hasLogBound hmp
      have h_aPlace : σ ∈ D.aPlaces := by
        grind [inducedPlace_eq_or_star_iff, hΛ.induced_by_aPlace, aPlaces, one_pow, o₀,
          orderOf_eq_one_iff]
      grw [h_one, ite_eq_left h_aPlace, add_comm]
      simpa using D.le_of_hasLogBound
  grw [cast_sum, mul_sum, sum_le_sum h_place, ← le_loss, hΛ.card_le, transferExponent]
  -- What remains once the sums over the a-places cancel holds by orders of magnitude.
  suffices (D.f ^ 2 * D.ceilLogLifts p * (D.n D.m + D.ceilLogLifts p) * p +
      #(placesInducing Λ) * D.a / D.m : ℝ) ≤ D.f * D.a * D.logB ^ 2 / D.m by
    simpa [inter_comm, ← add_assoc, sum_add_distrib, field]
  exact D.le_of_hasLogBound

end LowColumns

end New.Data

end
