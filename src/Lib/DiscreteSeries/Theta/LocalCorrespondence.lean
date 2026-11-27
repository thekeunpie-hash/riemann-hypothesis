module

import Mathlib.Algebra.Order.Star.Int
public import Lib.DiscreteSeries.Theta.FockDualPair
import Mathlib.Data.Finset.Slice
import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.Casimir
import Mathlib.Topology.Sheaves.Presheaf
public import Lib.DiscreteSeries.Rigidity.KernelFixes
public import Lib.Weil.Fock.OscillatorPair
import Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration

section
/-!
# Weights of matched pairs and uniqueness of joint harmonics in Fock space

This file studies the weights of matched pairs of the parameters `l` and `l'` of a dual pair
`T : New.FockDualPair`. It proves that the joint harmonic is unique up to a scalar, and that one of
its two weights suffices for this. Here `New.FockDualPair.IsMatchedPair` says that row `r` is
matched with column `c`.

The proof of uniqueness has three steps.
* The weights relative to the vacuum: `New.IsMatch.relWeight_eq_neg`,
  `New.IsMatch.sign_mul_relWeight_nonneg`.
* Both polarisations in a raising operator kill a highest harmonic polynomial, and a row has
  variables of one sign: `New.DiscreteSeries.polarization_eq_zero_of_isCompactPrimitive`,
  `New.DiscreteSeries.polarization_self_eq_smul_of_isCompactPrimitive`.
* Such a polynomial does not vanish at the 0-1 matrix of the matching:
  `New.IsMatch.eval_matchingPoint_ne_zero`.

## Main definitions and results

* `New.IsMatch.unique`, `New.IsJointHarmonic.exists_eq_smul_of_row_weight`: the joint harmonic is
  unique up to a scalar, and its row weight suffices for this.
* `New.IsMatch.eval_matchingPoint_ne_zero`: a pre-joint harmonic does not vanish at the point
  `New.FockDualPair.matchingPoint`, the 0-1 matrix of the matching.

Notions from other files:
* `New.HCParam.HasGap`: `l.HasGap h` says that the entries of `l = 2λ` are distinct and congruent to
  `n − 1` mod 2, where `n` is their number, and `|λ_i − λ_j| ≥ h` whenever `ε_i ≠ ε_j`.
* `New.HCParam.IsKHighest`: `x` is a `K`-highest vector of weight `ν`: each `E a a` acts on it by
  `ν a`, and it is killed by the compact raising operators, the `E a b` with `ε a = ε b` and
  `l b < l a`. The second condition alone is `New.GlModule.IsCompactPrimitive`.
* `New.HCParam.lowestKType`: for a parameter `l = 2λ`, the integer vector `λ + ρ − 2ρ_c`, which is
  the highest weight of the lowest `K`-type.
* `New.FockDualPair.IsPreJointHarmonic`: `Φ ≠ 0` is killed by the compact raising operators of the
  columns and by the Laplacians of both sides, and is `K`-highest of weight `l.lowestKType` for
  rows.
* `New.FockDualPair.relWeight`: the entry in row `r` of the lowest `K`-type for `l`, minus the
  weight of the vacuum on a row of sign `ε r`.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Theta.LocalCorrespondence` for sources.
-/

@[expose] public section

noncomputable section

section JointHarmonicUnique

open Fintype (card)

namespace New

variable {R C ι : Type} [Fintype R] [Fintype C]
  {ε : R → ℤˣ} {ε' : C → ℤˣ} {l : HCParam ε} {l' : HCParam ε'} {T : FockDualPair ε ε' ι}

@[local grind .] theorem DiscreteSeries.int_unit_val_eq_one_or_neg_one (x : ℤˣ) :
    (x : ℤ) = 1 ∨ (x : ℤ) = -1 :=
  Int.isUnit_iff.1 x.isUnit

open MvPolynomial Finset InnerProductSpace ComplexOrder Fischer Fock Int Units DiscreteSeries
  FockDualPair

/-! ### The weights of rows and columns relative to the vacuum -/

/-- Let `l` be a parameter with a gap (only distinctness and parity of its entries matter). Twice
`T.relWeight l r`, the entry of the lowest `K`-type minus the weight of the vacuum in row `r`, is
`l r + ∑ j, ε r * ε j * sign (l j - l r) - 2γ + card C - ∑ c, η (r, c)`, where `γ` is the constant
of the row action and `η (r, c)` the sign of the variable `(r, c)`. -/
@[local grind .] theorem HCParam.HasGap.two_mul_relWeight {h : ℕ} (r : R) (hg : l.HasGap h) :
    2 * T.relWeight l r = l r + ∑ j : R, ε r * ε j * (l j - l r).sign -
      (2 * T.rowShift - (card C - ∑ c : C, (T.varSign (r, c) : ℤ))) := by
  have rows : twoRho l (fun a b : R ↦ ε a ≠ ε b) r - twoRho l (fun a b : R ↦ ε a = ε b) r =
      ∑ j : R, ε r * ε j * (l j - l r).sign := by
    push_cast [twoRho, card_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [ne_eq, Units.ext_iff]
    grind
  have cols : (2 * #{c : C | T.globalSign * ε r * ε' c ≠ 1} : ℤ) =
      card C - ∑ c : C, (T.varSign (r, c) : ℤ) := by
    push_cast [Fintype.card_eq_sum_ones, card_filter, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    obtain h_sign | h_sign := units_eq_one_or (T.globalSign * ε r * ε' c) <;>
      simp [pairSign, h_sign]
  rw [relWeight, mul_sub, two_mul_lowestKType hg, vacuumWeight, ← rows, ← cols]
  ring

/-- If the parameters `l` of the rows and `l'` of the columns are matched, then `l` has the gap
`500 * card R ^ 3 + A` for every `A` up to the number `card ι` of variables. -/
theorem IsMatch.hasLargeGap [Fintype ι] (hm : IsMatch T l l') {A : ℕ} (hA : A ≤ Fintype.card ι) :
    l.HasLargeGap A := by
  -- A matching has the gap `500 * (card R + card C) ^ 3`, and `A ≤ card ι = card R * card C`.
  have card_eq : Fintype.card ι = card R * card C := by
    rw [← Fintype.card_congr T.varEquiv, Fintype.card_prod]
  have mul_le : card R * card C ≤ card R * card C ^ 2 :=
    Nat.mul_le_mul_left (card R) (Nat.le_self_pow two_ne_zero (card C))
  refine hm.hasGap_row.mono ?_
  calc gapThreshold R A
      ≤ 500 * card R ^ 3 + card R * card C ^ 2 :=
        Nat.add_le_add_left ((hA.trans_eq card_eq).trans mul_le) _
    _ ≤ 500 * (card R + card C) ^ 3 := by ring_nf; lia

/-- If `l` and `l'` match, a row is matched with at most one column. -/
theorem IsMatch.col_eq_of_isMatchedPair (hm : IsMatch T l l') {r : R} {c d : C}
    (hc : T.IsMatchedPair l l' r c) (hd : T.IsMatchedPair l l' r d) : c = d := by
  grind [hm.hasGap_column.injective]

/-- If `l` and `l'` match, a column is matched with at most one row. -/
theorem IsMatch.row_eq_of_isMatchedPair (hm : IsMatch T l l') {a r : R} {c : C}
    (ha : T.IsMatchedPair l l' a c) (hr : T.IsMatchedPair l l' r c) : a = r := by
  grind [hm.hasGap_row.injective]

/-- Let `l`, `l'` match. Then `∑ c, G c ≤ ∑ r, F r`, provided that `G c ≤ F r` when row `r` is
matched with column `c`, that `0 ≤ F r` when the centred parameter `l r - 2γ + card C` is less than
`card R - card C` in absolute value, and that `G c ≤ 0` when `l' c - 2γ' + card R` is less than
`card C - card R` in absolute value. -/
theorem IsMatch.sum_cols_le_sum_rows (hm : IsMatch T l l') (F : R → ℤ) (G : C → ℤ)
    (h_matched : ∀ (r : R) (c : C), T.IsMatchedPair l l' r c → G c ≤ F r)
    (h_rows : ∀ r : R, |T.centeredParam l r| < card R - card C → 0 ≤ F r)
    (h_cols : ∀ c : C, |T.swap.centeredParam l' c| < card C - card R → G c ≤ 0) :
    ∑ c : C, G c ≤ ∑ r : R, F r := by
  -- The matching is a partial bijection. Compare both sides with the sum of `F r` over the matched
  -- pairs `(r, c)`.
  calc ∑ c : C, G c ≤ ∑ c : C, ∑ r : R, if T.IsMatchedPair l l' r c then F r else 0 := by
        gcongr with c
        obtain ⟨r, hr⟩ | h_free := hm.right c
        · rw [sum_eq_single_of_mem r (mem_univ r) fun a _ ha ↦
            ite_eq_right fun hac ↦ ha (hm.row_eq_of_isMatchedPair hac hr), ite_eq_left hr]
          exact h_matched r c hr
        · rw [sum_eq_zero fun r _ ↦ ite_eq_right (show ¬T.IsMatchedPair l l' r c by grind)]
          exact h_cols c h_free
    _ = ∑ r : R, ∑ c : C, if T.IsMatchedPair l l' r c then F r else 0 := sum_comm
    _ ≤ ∑ r : R, F r := by
        gcongr with r
        obtain ⟨c, hc⟩ | h_free := hm.left r
        · rw [sum_eq_single_of_mem c (mem_univ c) fun d _ hd ↦
            ite_eq_right fun hrd ↦ hd (hm.col_eq_of_isMatchedPair hrd hc), ite_eq_left hc]
        · rw [sum_eq_zero fun c _ ↦ ite_eq_right (show ¬T.IsMatchedPair l l' r c by grind)]
          exact h_rows r h_free

/-- Let `l`, `l'` match. If row `r` is matched with column `c`, then Λ_r − v_r = −(Λ'_c − v'_c),
where Λ, Λ' are the lowest `K`-types of `l`, `l'` and v, v' the weights of the vacuum `1` for the
row and the column action. -/
theorem IsMatch.relWeight_eq_neg (hm : IsMatch T l l') {r : R} {c : C}
    (hrc : T.IsMatchedPair l l' r c) :
    T.relWeight l r = -T.swap.relWeight l' c := by
  -- By `HasGap.two_mul_relWeight` the claim is `∑ d, G d = ∑ j, F j`. This holds
  -- termwise: matched terms agree and unmatched terms vanish, since by `hrc` the centred parameter
  -- of `r` is the negative of that of `c` and exceeds `|card R - card C|` in absolute value.
  let F (j : R) : ℤ := T.swap.varSign (c, j) - ε r * ε j * (l j - l r).sign
  let G (d : C) : ℤ := ε' c * ε' d * (l' d - l' c).sign - T.varSign (r, d)
  have hle (s : ℤ) : ∑ d : C, s * G d ≤ ∑ j : R, s * F j :=
    hm.sum_cols_le_sum_rows (fun j ↦ s * F j) (fun d ↦ s * G d)
      (fun j d hjd ↦ by grind [pairSign, val_mul, Units.val_neg])
      (fun j hj ↦ by grind [pairSign, val_mul, Units.val_neg])
      (fun d hd ↦ by grind [pairSign, val_mul, Units.val_neg])
  have h1 := hle 1
  have h2 := hle (-1)
  have param : l r - 2 * T.rowShift + card C = -(l' c - 2 * T.columnShift + card R) := hrc.1
  simp only [F, G, one_mul, neg_mul, sum_neg_distrib, sum_sub_distrib] at h1 h2
  linarith [hm.hasGap_row.two_mul_relWeight (T := T) r,
    hm.hasGap_column.two_mul_relWeight (T := T.swap) c]

/-- Let `l`, `l'` match and let `s` be a sign. If `s` times the centred parameter
`l r - 2 * γ + card C` exceeds `card C - card R`, then `T.relWeight l r`, the weight of the lowest
`K`-type in row `r` relative to the vacuum, has the sign `s` or is zero. -/
theorem IsMatch.sign_mul_relWeight_nonneg (hm : IsMatch T l l') (r : R) (s : ℤˣ)
    (hr : card C - card R < (s : ℤ) * T.centeredParam l r) :
    0 ≤ s * T.relWeight l r := by
  have inj : Function.Injective l := hm.hasGap_row.injective
  have parity (j : R) : Even (l j + card R - 1) := hm.hasGap_row.parity j
  have gap (i j : R) (hij : (ε i : ℤ) ≠ ε j) : 2 * card R ≤ |l i - l j| := by
    have hg : l.HasGap (card R) := hm.hasGap_row.mono (mod_cast by cases card R <;> lia)
    exact_mod_cast hg.gap i j fun h_eq ↦ hij (by rw [h_eq])
  -- The numbers `s * T.centeredParam l j + card R - card C` are odd and distinct; write them as
  -- `2 * v j + 1`. At most `v r + 1` rows have `0 ≤ v j ≤ v r`.
  let v (j : R) : ℤ := (s * T.centeredParam l j + card R - card C) / 2
  let S : Finset ℤ := Icc 0 (v r)
  have card_le : #{j : R | v j ∈ S} ≤ #S :=
    card_le_card_of_injOn v (fun j hj ↦ by simpa using hj) fun i _ j _ hij ↦ by grind
  specialize parity r
  -- Termwise comparison. Column terms are `≤ 0`, and row terms with `v j ∈ S` are `≥ 0`. For
  -- `v j ∉ S` a matched row has the term of its column, and an unmatched row is close to `r`, so
  -- `ε j = ε r` by `gap` and its term is `0`.
  let F (j : R) : ℤ := s * (ε r * ε j * (l j - l r).sign) + (if v j ∈ S then 2 else 0) - 1
  let G (c : C) : ℤ := s * T.varSign (r, c) - 1
  have matched (j : R) (c : C) (hjc : T.IsMatchedPair l l' j c) : G c ≤ F j := by
    have j_large : |(card R - card C : ℤ)| < T.globalSign * ε j * ε' c * T.centeredParam l j :=
        hjc.2
    have sign_rc : (T.varSign (r, c) : ℤ) = T.globalSign * ε r * ε' c := by simp [pairSign]
    grind
  have free_row (j : R) (hj : |T.centeredParam l j| < card R - card C) : 0 ≤ F j := by
    grind [gap r j]
  have key : s * ∑ c : C, (T.varSign (r, c) : ℤ) ≤
      s * ∑ j : R, ε r * ε j * (l j - l r).sign + #{j : R | v j ∈ S} * 2 - card R + card C := by
    simpa [F, G, ← mul_sum, sum_ite, sum_add_distrib] using
      hm.sum_cols_le_sum_rows F G matched free_row fun c _ ↦ show G c ≤ 0 by grind
  have two_mul_eq : 2 * T.relWeight l r = l r + ∑ j : R, ε r * ε j * (l j - l r).sign -
      (2 * T.rowShift - (card C - ∑ c : C, (T.varSign (r, c) : ℤ))) :=
    hm.hasGap_row.two_mul_relWeight r
  -- Twice the right side of the goal is at least `2 * v r + 1 - 2 * #S = -1`.
  have lower_bound : 2 * v r + 1 - 2 * #S ≤ 2 * (s * T.relWeight l r) := by grind
  have card_S : (#S : ℤ) = v r + 1 := by grind [card_Icc]
  lia

/-! ### Highest harmonic polynomials

A compact raising operator `E a b` is the difference of two polarisations. -/

/-- Let `P` be killed by the compact raising operators of the rows for `l`, and let `ε a = ε b` and
`l b < l a`. Then the two polarisations whose difference is `E a b P` are equal: `∑ X_ac ∂_bc P`
over the columns `c` where `(b, c)` has sign `1`, and `∑ X_bc ∂_ac P` over those where it has sign
`-1`. -/
theorem DiscreteSeries.polarization_one_eq_of_lt [DecidableEq R] [DecidableEq C]
    {P : MvPolynomial ι ℂ}
    (h_prim : T.oscRows.IsCompactPrimitive l P) {a b : R} (hab : ε a = ε b) (h_lt : l b < l a) :
    T.polarization P a b 1 = T.polarization P b a (-1) := by
  have h_ne : a ≠ b := fun h ↦ h_lt.ne (congrArg l h.symm)
  have h_E : T.oscRows.E a b P = T.polarization P a b 1 - T.polarization P b a (-1) +
      (if a = b then (T.vacuumWeight (ε a) : ℂ) else 0) • P :=
    oscRows_E_eq_polarization_sub hab
  rw [h_prim a b hab h_lt, ite_eq_right h_ne, zero_smul, add_zero] at h_E
  exact sub_eq_zero.1 h_E.symm

/-- Let the entries of `l` be distinct, let `P` be killed by the compact raising operators of the
rows for `l` and by the Laplacians of the columns. For rows `a`, `b` of equal sign, the
polarisations `∑ X_bc ∂_ac P` over the columns `c` where `(a, c)` has sign `-s` and `∑ X_ac ∂_bc P`
over those where it has sign `s` are orthogonal for the Fischer inner product. For `s = 1` and
`a ≠ b` these are the two parts of `E a b P`. -/
theorem DiscreteSeries.inner_polarization_eq_zero [DecidableEq R] [DecidableEq C]
    {P : MvPolynomial ι ℂ} (hl : l.Injective)
    (h_prim : T.oscRows.IsCompactPrimitive l P) (h_harm : T.swap.IsLaplaceHarmonic P) (s : ℤˣ)
    {a b : R} (hab : ε a = ε b) :
    ⟪T.polarization P b a (-s), T.polarization P a b s⟫_ℂ = 0 := by
  -- The pairing in the claim is `N s a b`, which does not depend on `s`. The numbers `N 1 a b` are
  -- `≥ 0`, and their sum over the rows `b` with `ε b = ε a` is a pairing with the Laplacians of the
  -- columns, which is `0`. So all of them vanish.
  let u (a : R) (c d : C) : MvPolynomial ι ℂ :=
    pderiv (T.varEquiv (a, c)) (pderiv (T.varEquiv (a, d)) P)
  let N (s : ℤˣ) (a b : R) : ℂ :=
    ∑ d with T.varSign (a, d) = -s, ∑ c with T.varSign (a, c) = s, ⟪u a c d, u b c d⟫_ℂ
  have u_comm (a : R) (c d : C) : u a c d = u a d c := pderiv_comm ..
  have N_neg (s : ℤˣ) (a b : R) : N (-s) a b = N s a b := by
    simp only [N, neg_neg]
    rw [sum_comm]
    simp only [u_comm a, u_comm b]
  -- `X` is adjoint to `pderiv`; no commutator term arises, as the two columns have opposite signs.
  have inner_pol (s : ℤˣ) {a b : R} (hab : ε a = ε b) :
      ⟪T.polarization P b a (-s), T.polarization P a b s⟫_ℂ = N s a b := by
    have sign_eq (c : C) : T.varSign (b, c) = T.varSign (a, c) := by simp only [pairSign, hab]
    simp only [polarization, sum_inner, sign_eq, N]
    refine sum_congr rfl fun d hd ↦ (inner_sum ..).trans (sum_congr rfl fun c hc ↦ ?_)
    have hcd : T.varEquiv (a, c) ≠ T.varEquiv (b, d) := by
      grind [T.varEquiv.injective.eq_iff, neg_units_ne_self]
    rw [inner_X_mul.1, pderiv_mul, pderiv_X_of_ne hcd, zero_mul, zero_add, inner_X_mul.2,
      u_comm b]
  -- `N 1 a b` is a sum of squared norms for `a = b`, and one squared norm by
  -- `polarization_one_eq_of_lt` otherwise.
  have N_nonneg (a b : R) (hb : b ∈ univ.filter (ε · = ε a)) : 0 ≤ N 1 a b := by
    have hab : ε a = ε b := (mem_filter.1 hb).2.symm
    obtain h_lt | h_eq | h_gt := lt_trichotomy (l b) (l a)
    · rw [← inner_pol 1 hab, polarization_one_eq_of_lt h_prim hab h_lt]
      exact CStarModule.inner_self_nonneg
    · obtain rfl : b = a := hl h_eq
      exact sum_nonneg fun d _ ↦ sum_nonneg fun c _ ↦ CStarModule.inner_self_nonneg
    · rw [← N_neg, ← inner_pol (-1) hab, neg_neg, polarization_one_eq_of_lt h_prim hab.symm h_gt]
      exact CStarModule.inner_self_nonneg
  -- Summing `u b c d` over the block of `a` gives a Laplacian of `P`, up to sign.
  have N_sum (a : R) : ∑ b with ε b = ε a, N 1 a b = 0 := by
    simp only [N]
    refine sum_comm.trans <| sum_eq_zero fun d hd ↦ sum_comm.trans <| sum_eq_zero fun c hc ↦ ?_
    have sign_c {b : R} (hb : ε b = ε a) : T.varSign (b, c) = 1 := by
      simpa only [pairSign, hb] using (mem_filter.1 hc).2
    have sign_d {b : R} (hb : ε b = ε a) : T.varSign (b, d) = -1 := by
      simpa only [pairSign, hb] using (mem_filter.1 hd).2
    have hcd : ε' c ≠ ε' d := by grind [pairSign, neg_units_ne_self]
    have block (b : R) : T.swap.varSign (c, b) = -1 ↔ ε b = ε a := by
      have sign_a : T.globalSign * ε' c * ε a = 1 := (mul_right_comm ..).trans (sign_c rfl)
      simp only [pairSign, neg_mul, neg_inj]
      rw [← sign_a, _root_.mul_right_inj]
    have laplacian : T.swap.fockLaplacian c d P = -∑ b with ε b = ε a, u b c d := by
      rw [fockLaplacian, LinearMap.sum_apply, filter_congr fun b _ ↦ block b, ← sum_neg_distrib]
      refine sum_congr rfl fun b hb ↦ ?_
      have swap_d : T.swap.varSign (d, b) = 1 := by
        simpa [mul_right_comm T.globalSign, neg_eq_iff_eq_neg, pairSign] using sign_d
          (mem_filter.1 hb).2
      simp [u, (block b).2 (mem_filter.1 hb).2, swap_d, glOp, raiseOp, lowerOp]
    rw [← inner_sum, neg_eq_zero.1 (laplacian.symm.trans (h_harm c d hcd)), inner_zero_right]
  have N_zero : N 1 a b = 0 :=
    (sum_eq_zero_iff_of_nonneg (N_nonneg a)).1 (N_sum a) b (mem_filter.2 ⟨mem_univ b, hab.symm⟩)
  rw [inner_pol s hab]
  obtain rfl | rfl := units_eq_one_or s <;> simp only [N_neg, N_zero]

/-- Let the entries of `l` be distinct, let `P` be killed by the compact raising operators of the
rows for `l` and by the Laplacians of the columns. If the rows `a`, `b` have equal sign and
`s * l b < s * l a`, then the polarisation `∑ X_ac ∂_bc P` over the columns `c` where `(b, c)` has
sign `s` is zero. -/
theorem DiscreteSeries.polarization_eq_zero_of_isCompactPrimitive [DecidableEq R] [DecidableEq C]
    {P : MvPolynomial ι ℂ} (hl : l.Injective) (h_prim : T.oscRows.IsCompactPrimitive l P)
    (h_harm : T.swap.IsLaplaceHarmonic P) {s : ℤˣ} {a b : R} (hab : ε a = ε b)
    (h_lt : s * l b < s * l a) :
    T.polarization P a b s = 0 := by
  -- The two parts of a raising operator are equal on `P`, and they are orthogonal.
  have pol_eq : T.polarization P b a (-s) = T.polarization P a b s := by
    obtain rfl | rfl := units_eq_one_or s
    · exact (polarization_one_eq_of_lt h_prim hab (by simpa using h_lt)).symm
    · exact polarization_one_eq_of_lt h_prim hab.symm (by simpa using h_lt)
  rw [← inner_self_eq_zero (𝕜 := ℂ)]
  simpa only [pol_eq] using inner_polarization_eq_zero hl h_prim h_harm s hab

/-- Let the entries of `l` be distinct, let `P` be killed by the compact raising operators of the
rows for `l` and by the Laplacians of the columns, and let `E a a` act on it by the entry `Λ_a` of
the lowest `K`-type. Put `k = s * (Λ_a - v)`, where `v` is the weight of the vacuum in row `a`. If
`k ≥ 0`, then `P` has degree `k` in the variables of sign `s` of row `a`, and it does not depend on
the variables of sign `-s` of that row. -/
theorem DiscreteSeries.polarization_self_eq_smul_of_isCompactPrimitive [DecidableEq R]
    [DecidableEq C] {P : MvPolynomial ι ℂ}
    (hl : l.Injective) (h_prim : T.oscRows.IsCompactPrimitive l P)
    (h_harm : T.swap.IsLaplaceHarmonic P) {s : ℤˣ} {a : R}
    (h_wt : T.oscRows.E a a P = (l.lowestKType a : ℂ) • P) (h_nonneg : 0 ≤ s * T.relWeight l a) :
    T.polarization P a a s = ((s * T.relWeight l a : ℤ) : ℂ) • P ∧
      ∀ c : C, T.varSign (a, c) = -s → pderiv (T.varEquiv (a, c)) P = 0 := by
  set k : ℤ := s * T.relWeight l a with hk
  have pol_diag : T.polarization P a a s = T.polarization P a a (-s) + (k : ℂ) • P := by
    have h_E : T.oscRows.E a a P = T.polarization P a a 1 - T.polarization P a a (-1) +
        (T.vacuumWeight (ε a) : ℂ) • P := by simp [oscRows_E_eq_polarization_sub]
    obtain rfl | rfl := units_eq_one_or s <;> simp [hk, sub_smul, ← h_wt, h_E]
  -- Orthogonality reads `‖Q‖ ^ 2 + k * ⟪Q, P⟫ = 0` for `Q = polarization P a a (-s)`, and `⟪Q, P⟫`
  -- is the sum of the squared norms of the derivatives in question.
  have inner_eq : ⟪T.polarization P a a (-s), P⟫_ℂ = ∑ c with T.varSign (a, c) = -s,
      ⟪pderiv (T.varEquiv (a, c)) P, pderiv (T.varEquiv (a, c)) P⟫_ℂ := by
    simp only [polarization, sum_inner, inner_X_mul.1]
  have inner_nonneg : 0 ≤ (k : ℂ) * ⟪T.polarization P a a (-s), P⟫_ℂ := by
    rw [inner_eq]
    exact mul_nonneg (mod_cast h_nonneg) (sum_nonneg fun c _ ↦ CStarModule.inner_self_nonneg)
  have orth : ⟪T.polarization P a a (-s), T.polarization P a a (-s)⟫_ℂ +
      (k : ℂ) * ⟪T.polarization P a a (-s), P⟫_ℂ = 0 := by
    rw [← inner_smul_right, ← inner_add_right, ← pol_diag]
    exact inner_polarization_eq_zero hl h_prim h_harm s rfl
  have pol_zero : T.polarization P a a (-s) = 0 := inner_self_eq_zero.1
    ((add_eq_zero_iff_of_nonneg CStarModule.inner_self_nonneg inner_nonneg).1 orth).1
  refine ⟨by rw [pol_diag, pol_zero, zero_add], fun c hc ↦ ?_⟩
  rw [pol_zero, inner_zero_left] at inner_eq
  exact inner_self_eq_zero.1
    ((sum_eq_zero_iff_of_nonneg fun c _ ↦ CStarModule.inner_self_nonneg).1 inner_eq.symm c
      (mem_filter.2 ⟨mem_univ c, hc⟩))

omit [Fintype R] in
/-- If each mixed derivative `∂_ac ∂_bc Φ` with `ε a ≠ ε b` vanishes, then the Laplacians of the
rows, which are sums of such derivatives up to sign, kill `Φ`. -/
theorem FockDualPair.IsTermwiseHarmonic.isLaplaceHarmonic {Φ : MvPolynomial ι ℂ}
    (hΦ : T.IsTermwiseHarmonic Φ) : T.IsLaplaceHarmonic Φ := by
  intro a b hab
  rw [fockLaplacian, LinearMap.sum_apply]
  refine sum_eq_zero fun c hc ↦ ?_
  have sign_a : T.varSign (a, c) = -1 := (mem_filter.1 hc).2
  have sign_b : T.varSign (b, c) = 1 := by
    simpa [pairSign, units_ne_iff_eq_neg.1 hab] using sign_a
  simp [glOp, raiseOp, lowerOp, sign_a, sign_b, hΦ a b c hab]

/-- Let `Φ ≠ 0` be termwise harmonic along rows and columns and `K`-highest for both actions, with
the lowest `K`-type of `l` as weight for the row action and any weight `ν` for the column action.
Then `Φ` is a pre-joint harmonic: nonzero, killed by the compact raising operators of the columns
and by the Laplacians of both sides, and highest of weight `l.lowestKType` for the rows. -/
lemma FockDualPair.IsJointHighest.isPreJointHarmonic [DecidableEq R] [DecidableEq C]
    {Φ : MvPolynomial ι ℂ} {ν : C → ℤ} (hΦ : T.IsJointHighest l l' Φ l.lowestKType ν) :
    T.IsPreJointHarmonic l l' Φ := by
  obtain ⟨-, raise_col⟩ := hΦ.isKHighest_cols
  exact ⟨hΦ.ne_zero, raise_col, hΦ.isTermwiseHarmonic.isLaplaceHarmonic, hΦ.isKHighest_rows,
    hΦ.isTermwiseHarmonic_swap.isLaplaceHarmonic⟩

/-- A combination `P - c • Q` of pre-joint harmonics (nonzero polynomials killed by the Laplacians
and the compact raising operators of both sides, of weight `l.lowestKType` for the rows) is again
one, unless it is zero. -/
theorem FockDualPair.IsPreJointHarmonic.sub_smul [DecidableEq R] [DecidableEq C]
    {P Q : MvPolynomial ι ℂ} {c : ℂ}
    (hP : T.IsPreJointHarmonic l l' P) (hQ : T.IsPreJointHarmonic l l' Q) (h_ne : P ≠ c • Q) :
    T.IsPreJointHarmonic l l' (P - c • Q) := by
  obtain ⟨-, P_raise_col, P_harm_row, ⟨P_weight, P_raise_row⟩, P_harm_col⟩ := hP
  obtain ⟨-, Q_raise_col, Q_harm_row, ⟨Q_weight, Q_raise_row⟩, Q_harm_col⟩ := hQ
  refine ⟨sub_ne_zero.2 h_ne, fun a b hab h_lt ↦ ?_, fun a b hab ↦ ?_,
    ⟨fun a ↦ ?_, fun a b hab h_lt ↦ ?_⟩, fun a b hab ↦ ?_⟩
  · simp [P_raise_col a b hab h_lt, Q_raise_col a b hab h_lt]
  · simp [P_harm_row a b hab, Q_harm_row a b hab]
  · simp [P_weight a, Q_weight a, smul_sub, smul_comm c]
  · simp [P_raise_row a b hab h_lt, Q_raise_row a b hab h_lt]
  · simp [P_harm_col a b hab, Q_harm_col a b hab]

/-! ### The value at the matrix of the matching -/

/-- The 0-1 matrix of the matching, as a point of `ι → ℂ`: the coordinate of the variable `(r, c)`
is `1` if row `r` is matched with column `c`, and `0` if not. -/
noncomputable def FockDualPair.matchingPoint (T : FockDualPair ε ε' ι) (l : HCParam ε)
    (l' : HCParam ε') (i : ι) : ℂ :=
  if T.IsMatchedPair l l' (T.varEquiv.symm i).1 (T.varEquiv.symm i).2 then 1 else 0

/-- The coordinate `(r, c)` of the 0-1 matrix of the matching is nonzero exactly when row `r` is
matched with column `c`. -/
theorem FockDualPair.matchingPoint_ne_zero_iff (r : R) (c : C) :
    T.matchingPoint l l' (T.varEquiv (r, c)) ≠ 0 ↔ T.IsMatchedPair l l' r c := by
  rw [matchingPoint, Equiv.symm_apply_apply, ite_ne_right_iff, and_iff_left one_ne_zero]

/-- The variable `i` is an eigendirection of `F` at the point `x` if `F` is an eigenvector of a
linear vector field `∑ k ∈ S, X (a k) * ∂ (b k)` of which exactly one term, a multiple of `∂ i`,
is nonzero at `x`. -/
inductive DiscreteSeries.IsEigenDirection (F : MvPolynomial ι ℂ) (x : ι → ℂ) (i : ι) : Prop
  /-- The vector field has the terms `X (a k) * ∂ (b k)` for `k ∈ S` and the eigenvalue `μ` on
  `F`. Its term of index `j` differentiates in `i`, and `X (a k)` is nonzero at `x` only for
  `k = j`. -/
  | intro (κ : Type) (S : Finset κ) (a b : κ → ι) (j : κ) (μ : ℂ)
      (mem : j ∈ S) (direction_eq : b j = i) (ne_zero_iff : ∀ k : κ, x (a k) ≠ 0 ↔ k = j)
      (eigen : ∑ k ∈ S, X (a k) * pderiv (b k) F = μ • F) : DiscreteSeries.IsEigenDirection F x i

/-- The translation `G ↦ G (X + x)` commutes with partial derivatives. -/
theorem DiscreteSeries.bind₁_X_add_C_pderiv {τ : Type*} (x : τ → ℂ) (G : MvPolynomial τ ℂ) (i : τ) :
    aeval (fun j : τ ↦ X j + MvPolynomial.C (x j)) (pderiv i G) =
      pderiv i (aeval (fun j : τ ↦ X j + MvPolynomial.C (x j)) G) := by
  induction G using induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    obtain rfl | h_ne := eq_or_ne n i <;> simp [*]

/-- The constant coefficient of `G (X + x)` is the value of `G` at `x`. -/
theorem DiscreteSeries.coeff_zero_bind₁_X_add_C {τ : Type*} (x : τ → ℂ) (G : MvPolynomial τ ℂ) :
    (aeval (fun j : τ ↦ X j + MvPolynomial.C (x j)) G).coeff 0 = eval x G := by
  rw [← constantCoeff_eq]
  induction G using induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp [hp]

/-- A nonzero polynomial `F` that vanishes at `x` depends on a variable `i` that is not an
eigendirection at `x`: `F` is an eigenvector of no linear vector field `∑ k, X (a k) * ∂ (b k)`
whose only nonzero term at `x` is a multiple of `∂ i`. -/
theorem DiscreteSeries.exists_not_isEigenDirection {F : MvPolynomial ι ℂ} {x : ι → ℂ}
    (hF : F ≠ 0) (hx : eval x F = 0) :
    ∃ i : ι, pderiv i F ≠ 0 ∧ ¬IsEigenDirection F x i := by
  classical
  -- Take a monomial of least degree in the Taylor series `H = F (X + x)`. It is not constant, so
  -- its exponent is `t + single i 1` for some variable `i`. Compare the coefficients of `t`.
  let shift (y : ι → ℂ) : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
    aeval fun i ↦ X i + MvPolynomial.C (y i)
  have shift_pderiv (G : MvPolynomial ι ℂ) (i : ι) : shift x (pderiv i G) = pderiv i (shift x G) :=
    bind₁_X_add_C_pderiv x G i
  set H : MvPolynomial ι ℂ := shift x F with hH
  have shift_back : shift (-x) H = F := by simp [hH, shift, comp_aeval_apply, aeval_X_left_apply]
  have H_ne : H ≠ 0 := fun h_zero ↦ hF (by rw [← shift_back, h_zero, map_zero])
  obtain ⟨n, n_mem, n_min⟩ := H.support.exists_min_image Finsupp.degree (support_nonempty.2 H_ne)
  have n_ne : n ≠ 0 := by
    rintro rfl
    exact mem_support_iff.1 n_mem ((coeff_zero_bind₁_X_add_C x F).trans hx)
  obtain ⟨i, hi⟩ : ∃ i : ι, n i ≠ 0 := Finsupp.ne_iff.1 n_ne
  obtain ⟨t, rfl⟩ : ∃ t : ι →₀ ℕ, n = t + Finsupp.single i 1 :=
    le_iff_exists_add'.1 (Finsupp.single_le_iff.2 hi.pos)
  have coeff_low (m : ι →₀ ℕ) (h_le : m.degree ≤ t.degree) : H.coeff m = 0 := by
    by_contra h_ne
    grind [n_min m (mem_support_iff.2 h_ne), Finsupp.degree_single]
  have coeff_pderiv_ne : (pderiv i H).coeff t ≠ 0 := by
    simpa [coeff_pderiv, Nat.cast_add_one_ne_zero] using mem_support_iff.1 n_mem
  refine ⟨i, fun h_zero ↦ coeff_pderiv_ne (by simp [hH, ← shift_pderiv, h_zero]), ?_⟩
  rintro ⟨κ, S, a, b, j, μ, hj, rfl, only_j, eigen⟩
  -- The operators `X u * ∂ v` keep the degree, so they do not contribute to the coefficient of `t`.
  have coeff_X_mul_pderiv (u v : ι) : (X u * pderiv v H).coeff t = 0 := by
    rw [coeff_X_mul']
    refine ite_eq_right_iff.2 fun hu ↦ ?_
    have h_deg : (t - Finsupp.single u 1 + Finsupp.single v 1).degree = t.degree := by
      conv_rhs => rw [← t.sub_add_single_one_cancel (Finsupp.mem_support_iff.1 hu)]
      simp only [map_add, Finsupp.degree_single]
    rw [coeff_pderiv, coeff_low _ h_deg.le, zero_mul]
  refine mul_ne_zero ((only_j j).2 rfl) coeff_pderiv_ne ?_
  calc x (a j) * (pderiv (b j) H).coeff t
      = ∑ k ∈ S, x (a k) * (pderiv (b k) H).coeff t := by
        symm
        refine sum_eq_single_of_mem j hj fun k _ hk ↦ ?_
        rw [of_not_not (mt (only_j k).1 hk), zero_mul]
    _ = (shift x (∑ k ∈ S, X (a k) * pderiv (b k) F)).coeff t := by
        simp only [map_sum, map_mul, shift_pderiv, ← hH, coeff_sum]
        simp [shift, add_mul, coeff_X_mul_pderiv]
    _ = 0 := by simp [eigen, ← hH, coeff_low t le_rfl]

/-- Let `l`, `l'` match and let `s` be the sign of the variable `(r, c)`. Call an integer large if
it exceeds `card C - card R`, and let `ξ = l r - 2γ + card C`, with `γ = T.rowShift` the constant of
the row action, be the centred parameter of row `r`. Either `-s * ξ` is large, or one of three pairs
is matched: `(r, c)` itself, with `s * ξ` large; a pair `(r, d)` with `ε' d = ε' c` and
`s * l' d < s * l' c`; or a pair `(a, c)` with `ε a = ε r` and `s * l r < s * l a`. -/
theorem IsMatch.lt_or_exists_isMatchedPair (hm : IsMatch T l l') (r : R) (c : C) {s : ℤˣ}
    (hs : T.varSign (r, c) = s) :
    card C - card R < -(s : ℤ) * T.centeredParam l r ∨
      (card C - card R < (s : ℤ) * T.centeredParam l r ∧ T.IsMatchedPair l l' r c) ∨
      (∃ d : C, ε' d = ε' c ∧ s * l' d < s * l' c ∧ T.IsMatchedPair l l' r d) ∨
      ∃ a : R, ε a = ε r ∧ s * l r < s * l a ∧ T.IsMatchedPair l l' a c := by
  refine or_iff_not_imp_left.2 fun h_small ↦ ?_
  -- Row `r` is matched with a column `d`, and the variable `(r, d)` has the sign `s`.
  have r_not_free : ¬|T.centeredParam l r| < card R - card C := by grind [Units.val_neg]
  obtain ⟨d, hrd⟩ : ∃ d : C, T.IsMatchedPair l l' r d := (hm.left r).resolve_right r_not_free
  have sign_rd : T.varSign (r, d) = s := by grind [Units.val_neg, Units.ext_iff]
  have block_d : ε' d = ε' c := mul_left_cancel (sign_rd.trans hs.symm)
  have r_large : |(card R - card C : ℤ)| < s * T.centeredParam l r := by
    simpa only [sign_rd] using hrd.2
  obtain h_lt | h_eq | h_gt := lt_trichotomy (s * l' d) (s * l' c)
  · exact .inr (.inl ⟨d, block_d, h_lt, hrd⟩)
  · obtain rfl : d = c := hm.hasGap_column.injective (mul_left_cancel₀ s.ne_zero h_eq)
    exact .inl ⟨((le_abs_self _).trans_eq (abs_sub_comm _ _)).trans_lt r_large, hrd⟩
  · -- The parameter of column `c` is further out than that of `d`, so `c` is matched too.
    have c_not_free : ¬|T.swap.centeredParam l' c| < card C - card R := by grind
    obtain ⟨a, hac⟩ : ∃ a : R, T.IsMatchedPair l l' a c := (hm.right c).resolve_right c_not_free
    have a_above : s * l r < s * l a := by grind
    have sign_ac : T.varSign (a, c) = s := by grind [Units.ext_iff]
    have block_a : ε a = ε r := mul_left_cancel (mul_right_cancel (sign_ac.trans hs.symm))
    exact .inr (.inr ⟨a, block_a, a_above, hac⟩)

/-- Let `l`, `l'` match and let row `a` be matched with column `c`. If `F` is an eigenvector of the
polarisation `∑ X_ad ∂_rd` from row `r` to row `a`, summed over the columns `d` where `(r, d)` has
the sign of `(r, c)`, then `(r, c)` is an eigendirection of `F` at the 0-1 matrix of the
matching. -/
theorem IsMatch.isEigenDirection_of_polarization (hm : IsMatch T l l') {F : MvPolynomial ι ℂ}
    {a r : R} {c : C} {μ : ℂ} (hac : T.IsMatchedPair l l' a c)
    (h_eigen : T.polarization F a r (T.varSign (r, c)) = μ • F) :
    IsEigenDirection F (T.matchingPoint l l') (T.varEquiv (r, c)) := by
  have only_c (d : C) : T.matchingPoint l l' (T.varEquiv (a, d)) ≠ 0 ↔ d = c := by
    grind [matchingPoint_ne_zero_iff, hm.col_eq_of_isMatchedPair]
  have field : ∑ d with T.varSign (r, d) = T.varSign (r, c),
      X (T.varEquiv (a, d)) * pderiv (T.varEquiv (r, d)) F = μ • F := h_eigen
  exact ⟨C, _, fun d ↦ T.varEquiv (a, d), fun d ↦ T.varEquiv (r, d), c, μ, by simp, rfl, only_c,
    field⟩

/-- Let `l`, `l'` match and let row `r` be matched with column `d`. If `F` is an eigenvector of the
polarisation from column `c` to column `d` over the variables with the sign of `(r, c)`, then
`(r, c)` is an eigendirection of `F` at the 0-1 matrix of the matching. -/
theorem IsMatch.isEigenDirection_of_swap_polarization (hm : IsMatch T l l') {F : MvPolynomial ι ℂ}
    {r : R} {c d : C} {μ : ℂ} (hrd : T.IsMatchedPair l l' r d)
    (h_eigen : T.swap.polarization F d c (T.swap.varSign (c, r)) = μ • F) :
    IsEigenDirection F (T.matchingPoint l l') (T.varEquiv (r, c)) := by
  have h_point : T.swap.matchingPoint l' l = T.matchingPoint l l' := by
    funext i
    obtain ⟨⟨a, b⟩, rfl⟩ := T.varEquiv.surjective i
    have h_pair : T.swap.IsMatchedPair l' l b a ↔ T.IsMatchedPair l l' a b :=
      ⟨fun h ↦ by simpa only [T.swap_swap] using h.swap, fun h ↦ h.swap⟩
    change T.swap.matchingPoint l' l (T.swap.varEquiv (b, a)) = _
    simp only [matchingPoint, Equiv.symm_apply_apply, h_pair]
  rw [← h_point]
  exact hm.swap.isEigenDirection_of_polarization hrd.swap h_eigen

variable [DecidableEq R] [DecidableEq C]

/-- Let `l`, `l'` match. A pre-joint harmonic `F` (nonzero, killed by the Laplacians and the compact
raising operators of both sides, of weight `l.lowestKType` for the rows) does not vanish at the
point `T.matchingPoint l l'`, the 0-1 matrix of the matching. -/
theorem IsMatch.eval_matchingPoint_ne_zero (hm : IsMatch T l l') {F : MvPolynomial ι ℂ}
    (hF : T.IsPreJointHarmonic l l' F) :
    eval (T.matchingPoint l l') F ≠ 0 := by
  -- Otherwise `F` depends on a variable `(r, c)` that is not an eigendirection at the point. In
  -- each case of `lt_or_exists_isMatchedPair` a polarisation contradicts this.
  intro value_zero
  obtain ⟨F_ne, raise_col, harm_row, ⟨weight, raise_row⟩, harm_col⟩ := hF
  replace harm_row : T.swap.swap.IsLaplaceHarmonic F := by rwa [swap_swap]
  obtain ⟨i, pderiv_ne, not_eigen⟩ := exists_not_isEigenDirection F_ne value_zero
  obtain ⟨⟨r, c⟩, rfl⟩ := T.varEquiv.surjective i
  let s : ℤˣ := T.varSign (r, c)
  -- If `u` times the centred parameter of row `r` exceeds `card C - card R`, then of the variables
  -- of row `r`, `F` contains only those of sign `u`, and it is an eigenvector of Euler's field on
  -- them.
  have pure (u : ℤˣ) (hu : card C - card R < (u : ℤ) * T.centeredParam l r) :
      T.polarization F r r u = ((u * T.relWeight l r : ℤ) : ℂ) • F ∧
        ∀ d : C, T.varSign (r, d) = -u → pderiv (T.varEquiv (r, d)) F = 0 :=
    polarization_self_eq_smul_of_isCompactPrimitive hm.hasGap_row.injective raise_row harm_col
      (weight r)
      (hm.sign_mul_relWeight_nonneg r u hu)
  obtain h_large | ⟨h_large, hrc⟩ | ⟨d, block_d, h_lt, hrd⟩ | ⟨a, block_a, h_lt, hac⟩ :=
    hm.lt_or_exists_isMatchedPair r c (s := s) rfl
  · exact pderiv_ne ((pure (-s) h_large).2 c (neg_neg s).symm)
  · exact not_eigen (hm.isEigenDirection_of_polarization hrc (pure s h_large).1)
  · -- The part of sign `s` of a raising operator of the columns kills `F`.
    have kill : T.swap.polarization F d c (T.swap.varSign (c, r)) = (0 : ℂ) • F := by
      rw [zero_smul, show T.swap.varSign (c, r) = -s by
        simp [s, mul_right_comm T.globalSign, pairSign]]
      exact polarization_eq_zero_of_isCompactPrimitive hm.hasGap_column.injective raise_col harm_row
        block_d
        (by simpa using h_lt)
    exact not_eigen (hm.isEigenDirection_of_swap_polarization hrd kill)
  · -- So does the part of sign `s` of a raising operator of the rows.
    have kill : T.polarization F a r s = (0 : ℂ) • F := by
      rw [zero_smul]
      exact polarization_eq_zero_of_isCompactPrimitive hm.hasGap_row.injective raise_row harm_col
        block_a
        h_lt
    exact not_eigen (hm.isEigenDirection_of_polarization hac kill)

/-- Uniqueness of the joint harmonic up to a scalar. If the parameters `l` of the rows and `l'` of
the columns match, then any two pre-joint harmonics of `T` (nonzero polynomials killed by the
Laplacians and the compact raising operators of both sides, of weight `l.lowestKType` for the rows)
are proportional.

This proves the case of the multiplicity one part of Howe's (GL, GL)-duality that is used. -/
theorem IsMatch.unique (hm : IsMatch T l l') {P Q : MvPolynomial ι ℂ}
    (hP : T.IsPreJointHarmonic l l' P) (hQ : T.IsPreJointHarmonic l l' Q) :
    ∃ c : ℂ, P = c • Q := by
  -- Let `x` be the 0-1 matrix of the matching. The polynomial `P - (P x / Q x) • Q` vanishes at
  -- `x`. If it were not zero, it would be a pre-joint harmonic, and these do not vanish at `x`.
  let x : ι → ℂ := T.matchingPoint l l'
  let c : ℂ := eval x P / eval x Q
  have value_zero : eval x (P - c • Q) = 0 := by
    rw [map_sub, smul_eval, div_mul_cancel₀ _ (hm.eval_matchingPoint_ne_zero hQ), sub_self]
  exact ⟨c, by_contra fun h_ne ↦ hm.eval_matchingPoint_ne_zero (hP.sub_smul hQ h_ne) value_zero⟩

/-- Let `Φ` be a joint harmonic for `T`, `l`, `l'`: a nonzero polynomial, with `l` and `l'`
matching, that is `K`-highest for the row and column actions with the weights of the two lowest
`K`-types, and termwise harmonic for `T` and `T.swap`. Termwise harmonic means no monomial contains
two variables of one column from rows of opposite signs, or two variables of one row from columns of
opposite signs. Then every polynomial `P` that is termwise harmonic in both ways, is `K`-highest of
weight `l.lowestKType` for the row action `T.oscRows`, and is killed by the compact raising
operators for `l'` of the column action `T.swap.oscRows` is a scalar multiple `c • Φ`. -/
theorem IsJointHarmonic.exists_eq_smul_of_row_weight {Φ P : MvPolynomial ι ℂ}
    (hΦ : IsJointHarmonic T l l' Φ) (h_harmonic : T.IsTermwiseHarmonic P)
    (h_harmonic_swap : T.swap.IsTermwiseHarmonic P)
    (h_rows : l.IsKHighest T.oscRows l.lowestKType P)
    (h_cols : T.swap.oscRows.IsCompactPrimitive l' P) :
    ∃ c : ℂ, P = c • Φ := by
  obtain rfl | h_ne := eq_or_ne P 0
  · exact ⟨0, (zero_smul ℂ Φ).symm⟩
  · have hP : T.IsPreJointHarmonic l l' P := ⟨h_ne, h_cols, h_harmonic.isLaplaceHarmonic, h_rows,
      h_harmonic_swap.isLaplaceHarmonic⟩
    exact hΦ.unique hP hΦ.isJointHighest.isPreJointHarmonic

end New

end JointHarmonicUnique

end
end
end

section
/-!
# The Casimir elements of an oscillator pair

An oscillator pair is given by a `FockDualPair` `T` with `n = card R` rows and `n' = card C`
columns; the first group acts on the rows. This file proves that, with the centres (the weights of
the twisting characters) removed, the Casimir elements of the two groups differ by the constant
`n n' (n - n') / 4`, and that for matching parameters the numbers `|u|² - |ρ|²` and `|u'|² - |ρ'|²`
differ by the same constant, where `u`, `u'` are the centred parameters, that is, the entries
shifted by the centres. By `HCParam.HasGap.casimirValue_sub_center` these numbers are the centred
Casimir values.

The notions that the statements use:
* a parameter `l : HCParam ε` is an integer vector that stands for `l = 2λ`; `l.HasGap h` says that
  its entries are distinct, of the parity of `n - 1`, and at least `2h` apart where the signs `ε`
  differ;
* for symmetric `r`, `twoRho l r` is the sum of the roots selected by `r` that are positive for `l`,
  so `twoRho l ⊤` is `2ρ`, and `l.casimirValue` is `|λ|² - |ρ|²`;
* `T.oscRows` is the oscillator action of `gl R` on polynomials, and `T.swap` is the same pair with
  rows and columns exchanged;
* `T.centeredParam l r` is `2u_r = l r - 2γ + n'` with `γ = T.rowShift` the scalar on the diagonal
  of the row action (`T.columnShift` is that of the column action `T.swap.oscRows`), and
  `IsMatch T l l'` says that `l` and `l'` have gap `500 (n + n')³`, that each row is matched with a
  column or has `|2u_r| < n - n'`, and that each column is matched with a row or has
  `|2u'_c| < n' - n`; the row `r` and the column `c` are matched if `u_r = -u'_c` and
  `T.globalSign * ε r * ε' c * 2u_r > |n - n'|`.

## Relation to the literature

Known result: the constant difference of the centred Casimir elements of the two groups of an
oscillator pair, a case of the correspondence of infinitesimal characters. Source: compare A. Paul,
First occurrence for the dual pairs (U(p,q), U(r,s)), Canad. J. Math. 51 (1999), Theorem 2.11.

See also `Lib.DiscreteSeries.Theta.LocalCorrespondence`.
-/

@[expose] public section

namespace New

open Finset Fock
open Fintype (card)

section SumsOfSquares

/-- The sum `∑ (2k - c)²` over `k < d`, times `3`, in closed form. -/
theorem three_mul_sum_range_two_mul_sub_sq (c : ℤ) (d : ℕ) :
    3 * ∑ k ∈ range d, (2 * (k : ℤ) - c) ^ 2 =
      2 * d * (d - 1) * (2 * d - 1) - 6 * c * d * (d - 1) + 3 * d * c ^ 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, mul_add, ih]
    grind

/-- A set of `d` distinct integers of the parity of `d - 1` and of modulus below `d` is
`{1 - d, 3 - d, …, d - 1}`, so the sum of their squares is `d (d² - 1) / 3`. -/
theorem three_mul_sum_sq_of_injOn {α : Type*} (s : Finset α) (f : α → ℤ) (h_inj : Set.InjOn f s)
    (h_parity : ∀ i ∈ s, Even (f i + #s - 1)) (h_bound : ∀ i ∈ s, |f i| < #s) :
    3 * ∑ i ∈ s, f i ^ 2 = #s * (#s ^ 2 - 1) := by
  let g (k : ℕ) : ℤ := 2 * k - (#s - 1)
  have hg_inj : Function.Injective g := fun j k hjk ↦ by simpa [g] using hjk
  have h_subset : s.image f ⊆ (range #s).image g := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hz
    obtain ⟨k, hk⟩ := h_parity i hi
    have hi_bound := abs_lt.1 (h_bound i hi)
    exact mem_image.2 ⟨k.toNat, mem_range.2 (by lia), by grind⟩
  have h_image : s.image f = (range #s).image g := eq_of_subset_of_card_le h_subset <| by
    simp [card_image_of_injective _ hg_inj, card_image_of_injOn h_inj]
  calc 3 * ∑ i ∈ s, f i ^ 2 = 3 * ∑ z ∈ s.image f, z ^ 2 := by rw [sum_image h_inj]
    _ = 3 * ∑ k ∈ range #s, g k ^ 2 := by rw [h_image, sum_image hg_inj.injOn]
    _ = #s * (#s ^ 2 - 1) := by linear_combination three_mul_sum_range_two_mul_sub_sq (#s - 1) #s

variable {n : Type} [Fintype n]

/-- For a vector `l` with distinct entries, `twoRho l ⊤ = 2ρ` is the sum of the roots positive for
`l`. The squares of its entries sum to `N (N² - 1) / 3` with `N = card n`, that is,
`|ρ|² = N (N² - 1) / 12`. -/
theorem three_mul_sum_twoRho_sq {l : n → ℤ} (hl : l.Injective) :
    3 * ∑ i : n, twoRho l ⊤ i ^ 2 = card n * (card n ^ 2 - 1) := by
  classical
  have h_count (i : n) : (#{j | l j < l i} + #{j | l i < l j} + 1 : ℤ) = card n :=
    mod_cast card_lt_add_card_gt_add_one hl i
  have h_value (i : n) : twoRho l ⊤ i = #{j | l j < l i} - #{j | l i < l j} := by
    simp [twoRho]
  have h_inj : Function.Injective (twoRho l ⊤) := by
    intro a b hab
    obtain h | h | h := lt_trichotomy (l a) (l b)
    exacts [absurd hab (twoRho_lt_twoRho h).ne, hl h, absurd hab (twoRho_lt_twoRho h).ne']
  have h_parity (i : n) : Even (twoRho l ⊤ i + card n - 1) :=
    ⟨#{j | l j < l i}, by linear_combination h_value i - h_count i⟩
  have h_bound (i : n) : |twoRho l ⊤ i| < card n := by grind
  exact three_mul_sum_sq_of_injOn univ _ h_inj.injOn (fun i _ ↦ h_parity i) fun i _ ↦ h_bound i

/-- For a symmetric relation `r`, the entries of `twoRho l r` sum to zero. -/
theorem sum_twoRho_eq_zero (l : n → ℤ) (r : n → n → Prop) [DecidableRel r]
    (hr : ∀ i j : n, r i j → r j i) : ∑ i : n, twoRho l r i = 0 := by
  -- Both counts run over the pairs with `r`, ordered by `l`.
  simp only [twoRho, sum_sub_distrib, card_filter, Nat.cast_sum, sub_eq_zero]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [Iff.intro (hr j i) (hr i j)]

/-- For a parameter `l = 2λ` with a gap (distinct entries of the parity of `n - 1`, those of
different signs `ε` far apart), the lowest K-type and `λ` have the same sum of entries. -/
theorem HCParam.HasGap.two_mul_sum_lowestKType {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}
    (hg : l.HasGap h) : 2 * ∑ i : n, l.lowestKType i = ∑ i : n, l i := by
  have h_noncompact : ∑ i, twoRho l (fun i j ↦ ε i ≠ ε j) i = 0 :=
    sum_twoRho_eq_zero l _ fun i j ↦ Ne.symm
  have h_compact : ∑ i, twoRho l (fun i j ↦ ε i = ε j) i = 0 :=
    sum_twoRho_eq_zero l _ fun i j ↦ Eq.symm
  simp [mul_sum, two_mul_lowestKType hg, sum_sub_distrib, sum_add_distrib, h_noncompact, h_compact]

/-- Let `l = 2λ` be a parameter with a gap (distinct entries of the parity of `n - 1`, those of
different signs far apart), with Casimir value `κ = |λ|² - |ρ|²` and lowest K-type `μ`. For any
scalar `w`, the value with the centre `w` removed, `κ - 2w ∑ μ_a + n w²`, is
`∑ (λ_a - w)² - n (n² - 1) / 12`, where `n` is the number of entries. -/
theorem HCParam.HasGap.casimirValue_sub_center {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}
    (hg : l.HasGap h) (w : ℂ) :
    l.casimirValue - 2 * w * ∑ a : n, (l.lowestKType a : ℂ) + card n * w ^ 2 =
      ∑ a : n, (l a / 2 - w) ^ 2 - (card n * (card n ^ 2 - 1) / 12 : ℂ) := by
  have h_rho : 3 * ∑ a, (twoRho l ⊤ a : ℂ) ^ 2 = card n * (card n ^ 2 - 1) :=
    mod_cast three_mul_sum_twoRho_sq hg.injective
  have h_sum : 2 * ∑ a, (l.lowestKType a : ℂ) = ∑ a, (l a : ℂ) :=
    mod_cast hg.two_mul_sum_lowestKType
  have h_value : (l.casimirValue : ℂ) =
      (∑ a, (l a : ℂ) ^ 2 - ∑ a, (twoRho l ⊤ a : ℂ) ^ 2) / 4 := by
    simp [casimirValue, ← sum_div, sum_sub_distrib]
  have h_term (a : n) : (l a / 2 - w : ℂ) ^ 2 = (l a : ℂ) ^ 2 / 4 - w * l a + w ^ 2 := by ring
  have h_square : ∑ a, (l a / 2 - w : ℂ) ^ 2 =
      (∑ a, (l a : ℂ) ^ 2) / 4 - w * ∑ a, (l a : ℂ) + card n * w ^ 2 := by
    simp [h_term, sum_add_distrib, ← sum_div, ← mul_sum]
  rw [h_value, h_square]
  linear_combination -w * h_sum - h_rho / 12

end SumsOfSquares

section Casimir

variable {R C ι : Type} [Fintype R] [DecidableEq R] [Fintype C] {ε : R → ℤˣ} {ε' : C → ℤˣ}

omit [Fintype R] [DecidableEq R] in
/-- The centred parameters `l r - 2γ + card C` of a vector `l` with distinct entries are
distinct. -/
theorem FockDualPair.centeredParam_injective (T : FockDualPair ε ε' ι) {l : HCParam ε}
    (hl : Function.Injective l) : Function.Injective (T.centeredParam l) :=
  fun a b hab ↦ hl (by simpa [FockDualPair.centeredParam] using hab)

/-- Let `l`, `l'` be matching parameters of the pair `T`: they have a large gap, and each row and
column is matched, with opposite centred parameters, or has a small one. Let `n' ≤ n` for
`n = card R` and `n' = card C`. The squares of the centred parameters `l r - 2 T.rowShift + n'` of
the rows and `l' c - 2 T.columnShift + n` of the columns (the rows of `T.swap`) differ in sum by
`d₀ (d₀² - 1) / 3` with `d₀ = n - n'`, the share of the unmatched rows. -/
theorem IsMatch.three_mul_sum_sq_sub_of_le {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') (h_le : card C ≤ card R) :
    3 * (∑ r : R, T.centeredParam l r ^ 2 - ∑ c : C, T.swap.centeredParam l' c ^ 2) =
      (card R - card C) * ((card R - card C) ^ 2 - 1) := by
  -- Every index of the smaller group is matched, with one row `m c`.
  have h_matched (c : C) : ∃ r : R, T.centeredParam l r = -T.swap.centeredParam l' c := by
    obtain ⟨r, h_eq, -⟩ | h_lt := hm.right c
    · exact ⟨r, h_eq⟩
    · grind [abs_nonneg]
  choose m h_opposite using h_matched
  have h_row_inj : Function.Injective (T.centeredParam l) :=
    T.centeredParam_injective hm.hasGap_row.injective
  have hm_inj : Function.Injective m := by
    refine fun c c' hc ↦
        T.swap.centeredParam_injective hm.hasGap_column.injective (neg_injective ?_)
    rw [← h_opposite c, ← h_opposite c', hc]
  -- So the larger group has `n - n'` unmatched entries.
  set free : Finset R := (univ.image m)ᶜ with h_free
  have h_card : (#free : ℤ) = card R - card C := by
    simp [h_free, card_compl, card_image_of_injective _ hm_inj, h_le]
  have h_split : ∑ r, T.centeredParam l r ^ 2 =
      ∑ c, T.swap.centeredParam l' c ^ 2 + ∑ r ∈ free, T.centeredParam l r ^ 2 := by
    rw [← sum_add_sum_compl (univ.image m), sum_image hm_inj.injOn]
    simp only [h_opposite, neg_sq, h_free]
  -- They are distinct, of the parity of `n - n' - 1` and of modulus below `n - n'`.
  have h_small (r : R) (hr : r ∈ free) : |T.centeredParam l r| < #free := by
    rw [h_card]
    refine (hm.left r).resolve_left ?_
    rintro ⟨c, hr_eq, -⟩
    have h_eq : m c = r := h_row_inj ((h_opposite c).trans hr_eq.symm)
    exact mem_compl.1 hr (mem_image.2 ⟨c, mem_univ c, h_eq⟩)
  have h_parity (r : R) (_ : r ∈ free) : Even (T.centeredParam l r + #free - 1) := by
    obtain ⟨k, hk⟩ : Even (l r + card R - 1) := hm.hasGap_row.parity r
    refine ⟨k - T.rowShift, ?_⟩
    rw [h_card, FockDualPair.centeredParam]
    lia
  rw [h_split, add_sub_cancel_left, ← h_card]
  exact three_mul_sum_sq_of_injOn free _ h_row_inj.injOn h_parity h_small

/-- For matching parameters `l`, `l'` of the pair `T`, the squares of the centred parameters
`l r - 2γ + n'` of the rows and `l' c - 2γ' + n` of the columns differ in sum by `d₀ (d₀² - 1) / 3`,
where `n = card R`, `n' = card C`, and `d₀ = n - n'` may have either sign. -/
theorem IsMatch.three_mul_sum_sq_sub [DecidableEq C] {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') :
    3 * (∑ r : R, T.centeredParam l r ^ 2 - ∑ c : C, T.swap.centeredParam l' c ^ 2) =
      (card R - card C) * ((card R - card C) ^ 2 - 1) := by
  obtain h_le | h_le := le_total (card C) (card R)
  · exact hm.three_mul_sum_sq_sub_of_le h_le
  · have h_swap : 3 * (∑ c, T.swap.centeredParam l' c ^ 2 - ∑ r, T.centeredParam l r ^ 2) =
        (card C - card R : ℤ) * ((card C - card R : ℤ) ^ 2 - 1) := by
      simpa only [T.swap_swap] using hm.swap.three_mul_sum_sq_sub_of_le h_le
    linear_combination -h_swap

variable [DecidableEq C] {A : Type*} [Ring A] [Algebra ℂ A]

/-- Normal ordering. Let `x`, `d` be arrays in a complex algebra with
`d_rc x_rc' = x_rc' d_rc + δ_cc'`. With `n = card R` and `n' = card C`, the Casimir sum of the
elements `∑ c, x_ac d_bc + (n'/2) δ_ab` is `D₄ + (n + n') D₂ + n n'² / 4`, where
`D₄ = ∑ x_ac x_bc' d_bc d_ac'` and `D₂ = ∑ x_rc d_rc`. -/
theorem sum_mul_eq_normal_order (x d : R → C → A)
    (h_comm : ∀ (r : R) (c c' : C), d r c * x r c' = x r c' * d r c + if c = c' then 1 else 0) :
    ∑ a : R, ∑ b : R, (∑ c : C, x a c * d b c + if a = b then (card C / 2 : ℂ) • 1 else 0) *
        (∑ c : C, x b c * d a c + if b = a then (card C / 2 : ℂ) • 1 else 0) =
      ∑ a : R, ∑ b : R, ∑ c : C, ∑ c' : C, x a c * x b c' * d b c * d a c' +
        (card R + card C : ℂ) • ∑ r : R, ∑ c : C, x r c * d r c +
          (card R * card C ^ 2 / 4 : ℂ) • (1 : A) := by
  rw [TauCeti.sum_mul_eq_normal_order x d _ h_comm]
  module

/-- The Casimir element with the centre `w` removed: it is formed with `E_ab - w δ_ab` in place of
`E_ab`. -/
noncomputable def GlModule.centeredCasimir {M : Type*} [AddCommGroup M] [Module ℂ M]
    (ρ : GlModule R M) (w : ℂ) : Module.End ℂ M :=
  ∑ a : R, ∑ b : R, (ρ.E a b - if a = b then w • 1 else 0) * (ρ.E b a - if b = a then w • 1 else 0)

/-- On a vector of weight `ν`, the Casimir element with the centre `w` removed is
`Ω - 2w ∑ ν_a + n w²`, where `n = card R`. Here `Ω = ρ.casimirK 1` is the full Casimir element
`∑ E_ab E_ba`: all signs are `1`, so every pair of indices counts. -/
theorem GlModule.centeredCasimir_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (ρ : GlModule R M) (w : ℂ) {ν : R → ℤ} {v : M} (hv : ∀ a : R, ρ.E a a v = (ν a : ℂ) • v) :
    ρ.centeredCasimir w v =
      ρ.casimirK 1 v - (2 * w * ∑ a : R, (ν a : ℂ)) • v + (card R * w ^ 2) • v := by
  have h_expand : ρ.centeredCasimir w =
      ρ.casimirK 1 + (2 * -w) • ∑ a, ρ.E a a + (card R * (-w) ^ 2) • 1 := by
    have h_casimir : ρ.casimirK 1 = ∑ a, ∑ b, ρ.E a b * ρ.E b a := by
      simp [GlModule.casimir]
    rw [h_casimir, ← TauCeti.sum_add_scalar_mul_add_scalar]
    simp only [centeredCasimir, sub_eq_add_neg, neg_ite, neg_zero, neg_smul]
  simp [h_expand, hv, ← sum_smul]
  module

namespace FockDualPair

variable (T : FockDualPair ε ε' ι)

/-- The centre `w` of the action on the rows: the scalar `T.rowShift` on the diagonal is `w + n'/2`.
It is the weight of the character of the determinant by which the action is twisted. -/
noncomputable def center : ℂ := T.rowShift - card C / 2

/-- The operator `x_rc`: for the variable `T.varEquiv (r, c)` of `MvPolynomial ι ℂ` attached to the
entry `(r, c)`, multiplication by the variable where its sign `T.indexSign` is `+`, minus the
derivative where it is `-`. -/
noncomputable abbrev raise (r : R) (c : C) : Module.End ℂ (MvPolynomial ι ℂ) :=
  raiseOp T.indexSign (T.varEquiv (r, c))

/-- The operator `d_rc`: for the variable `T.varEquiv (r, c)` of `MvPolynomial ι ℂ` attached to the
entry `(r, c)`, the derivative where the sign `T.indexSign` of the variable is `+`, multiplication
by the variable where it is `-`. -/
noncomputable abbrev lower (r : R) (c : C) : Module.End ℂ (MvPolynomial ι ℂ) :=
  lowerOp T.indexSign (T.varEquiv (r, c))

/-- The operator `D₄ = ∑ x_ac x_bc' d_bc d_ac'` of a Fock dual pair, over all rows `a`, `b` and
columns `c`, `c'`. -/
noncomputable def quarticOp : Module.End ℂ (MvPolynomial ι ℂ) :=
  ∑ a : R, ∑ b : R, ∑ c : C, ∑ c' : C, T.raise a c * T.raise b c' * T.lower b c * T.lower a c'

/-- The operator `D₂ = ∑ x_rc d_rc` of a Fock dual pair, over all rows `r` and columns `c`. -/
noncomputable def quadraticOp : Module.End ℂ (MvPolynomial ι ℂ) :=
  ∑ r : R, ∑ c : C, T.raise r c * T.lower r c

omit [Fintype R] [Fintype C] in
/-- The canonical commutation relation `d_rc x_r'c' = x_r'c' d_rc + δ_rr' δ_cc'` of the operators
`T.lower` and `T.raise`. -/
theorem lower_mul_raise (r r' : R) (c c' : C) : T.lower r c * T.raise r' c' =
    T.raise r' c' * T.lower r c + if r = r' ∧ c = c' then 1 else 0 := by
  classical
  refine LinearMap.ext fun P ↦ ?_
  split_ifs with h <;> simp_all [lowerOp_raiseOp]

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem lower_mul_lower (r r' : R) (c c' : C) :
    T.lower r c * T.lower r' c' = T.lower r' c' * T.lower r c := by
  classical
  exact LinearMap.ext fun P ↦ lowerOp_comm T.indexSign _ _ P

omit [DecidableEq R] [DecidableEq C] in
/-- `D₄` summed first over the columns: since the `d_rc` commute, the last two factors may be
exchanged. -/
theorem sum_columns_eq_quarticOp :
    ∑ c : C, ∑ c' : C, ∑ a : R, ∑ b : R,
      T.raise a c * T.raise b c' * T.lower a c' * T.lower b c = T.quarticOp := by
  rw [quarticOp]
  refine sum_comm_cycle.trans (sum_congr rfl fun a _ ↦ sum_comm_cycle.trans
    (sum_congr rfl fun b _ ↦ sum_congr rfl fun c _ ↦ sum_congr rfl fun c' _ ↦ ?_))
  rw [mul_assoc, T.lower_mul_lower, ← mul_assoc]

/-- For signs `δ` and a sign `s` (read in `ℂ`), the factor that is `1` if `δ a = δ b` and `s`
otherwise, times the same factor for `(b, a)`, is `1`. So these factors drop out of a Casimir
element. -/
theorem sign_mul_sign {n : Type*} (δ : n → ℤˣ) (s : ℤˣ) (a b : n) :
    (if δ a = δ b then 1 else s : ℂ) * (if δ b = δ a then 1 else s : ℂ) = 1 :=
  (ite_units_eq_mul_ite_units_eq s _ _ _).trans (ite_eq_left rfl)

/-- The row action of the matrix unit `(a, b)` less `T.centre = T.rowShift - n'/2` on the diagonal
is `∑ c, x_ac d_bc + (n'/2) δ_ab`, times the sign `T.globalSign` of the pair where the signs `ε a`,
`ε b` differ; here `n' = card C`, `x = T.raise` and `d = T.lower`. -/
theorem oscRows_E_sub_center (a b : R) :
    (T.oscRows.E a b - if a = b then T.center • 1 else 0) =
      (if ε a = ε b then 1 else T.globalSign : ℂ) •
      (∑ c : C, T.raise a c * T.lower b c + if a = b then (card C / 2 : ℂ) • 1 else 0) := by
  have h_unit : T.oscRows.E a b = (if ε a = ε b then 1 else T.globalSign : ℂ) •
      ∑ c, T.raise a c * T.lower b c + if a = b then (T.rowShift : ℂ) • 1 else 0 := by
    simp [oscRows_E, oscRowsUnit, glOp, Int.cast_smul_eq_zsmul]
  rw [h_unit]
  obtain rfl | hab := eq_or_ne a b
  · simp only [ite_true, center]
    module
  · simp [hab]

/-- The column action of the matrix unit `(a, b)` less `T.swap.centre = T.columnShift - n/2` on the
diagonal is `-(∑ r, x_rb d_ra + (n/2) δ_ab)`, times the sign `T.globalSign` of the pair where the
signs `ε' a`, `ε' b` differ; here `n = card R`, `x = T.raise`, `d = T.lower`, and `T.swap` is `T`
with rows and columns exchanged. -/
theorem swap_oscRows_E_sub_center (a b : C) :
    (T.swap.oscRows.E a b - if a = b then T.swap.center • 1 else 0) =
      -(if ε' a = ε' b then 1 else T.globalSign : ℂ) •
        (∑ r : R, T.raise r b * T.lower r a + if b = a then (card R / 2 : ℂ) • 1 else 0) := by
  have h_unit : T.swap.oscRows.E a b = (if ε' a = ε' b then 1 else T.globalSign : ℂ) •
      -∑ r, T.lower r a * T.raise r b + if a = b then (T.columnShift : ℂ) • 1 else 0 := by
    simp [swap_oscRows_E, Int.cast_smul_eq_zsmul]
  rw [h_unit, show T.swap.center = T.columnShift - card R / 2 from rfl]
  simp only [lower_mul_raise, true_and, sum_add_distrib, sum_const, card_univ]
  obtain rfl | hab := eq_or_ne a b
  · simp only [ite_true, ← Nat.cast_smul_eq_nsmul ℂ]
    module
  · simp [hab, hab.symm]

/-- The Casimir element of the row action `T.oscRows` with the centre `T.center` removed is
`D₄ + (n + n') D₂ + n n'² / 4`, where `D₄ = T.quarticOp`, `D₂ = T.quadraticOp`, `n = card R` and
`n' = card C`. -/
theorem centeredCasimir_oscRows : T.oscRows.centeredCasimir T.center =
    T.quarticOp + (card R + card C : ℂ) • T.quadraticOp +
      (card R * card C ^ 2 / 4 : ℂ) • 1 := by
  have h_comm (r : R) (c c' : C) : T.lower r c * T.raise r c' =
      T.raise r c' * T.lower r c + if c = c' then 1 else 0 := by simp [lower_mul_raise]
  -- The sign factors cancel in the products.
  have h_unsigned : T.oscRows.centeredCasimir T.center = ∑ a, ∑ b,
      (∑ c, T.raise a c * T.lower b c + if a = b then (card C / 2 : ℂ) • 1 else 0) *
        (∑ c, T.raise b c * T.lower a c + if b = a then (card C / 2 : ℂ) • 1 else 0) := by
    simp only [GlModule.centeredCasimir, oscRows_E_sub_center, smul_mul_smul_comm, sign_mul_sign,
      one_smul]
  rw [h_unsigned, sum_mul_eq_normal_order T.raise T.lower h_comm, quarticOp, quadraticOp]

/-- The Casimir element of the column action `T.swap.oscRows` with the centre `T.swap.center`
removed is `D₄ + (n + n') D₂ + n² n' / 4`, where `D₄ = T.quarticOp`, `D₂ = T.quadraticOp`,
`n = card R` and `n' = card C`. -/
theorem centeredCasimir_swap_oscRows : T.swap.oscRows.centeredCasimir T.swap.center =
    T.quarticOp + (card R + card C : ℂ) • T.quadraticOp +
      (card R ^ 2 * card C / 4 : ℂ) • 1 := by
  -- Normal ordering with the roles of rows and columns exchanged gives the same `D₄` and `D₂`.
  have h_comm (c : C) (r r' : R) : T.lower r c * T.raise r' c =
      T.raise r' c * T.lower r c + if r = r' then 1 else 0 := by simp [lower_mul_raise]
  have h_quadratic : ∑ c, ∑ r, T.raise r c * T.lower r c = T.quadraticOp := sum_comm
  -- The sign factors cancel in the products.
  have h_unsigned : T.swap.oscRows.centeredCasimir T.swap.center = ∑ a, ∑ b,
      (∑ r, T.raise r b * T.lower r a + if b = a then (card R / 2 : ℂ) • 1 else 0) *
        (∑ r, T.raise r a * T.lower r b + if a = b then (card R / 2 : ℂ) • 1 else 0) := by
    simp only [GlModule.centeredCasimir, swap_oscRows_E_sub_center, smul_mul_smul_comm,
      neg_mul_neg, sign_mul_sign, one_smul]
  rw [h_unsigned, sum_comm,
    sum_mul_eq_normal_order (fun c r ↦ T.raise r c) (fun c r ↦ T.lower r c) h_comm,
    T.sum_columns_eq_quarticOp, h_quadratic]
  module

/-- The centred Casimir element of the column action `T.swap.oscRows` is that of the row action
`T.oscRows` plus the constant `n n' d₀ / 4`, where `n = card R`, `n' = card C` and `d₀ = n - n'`. -/
theorem centeredCasimir_swap_oscRows_eq_add : T.swap.oscRows.centeredCasimir T.swap.center =
    T.oscRows.centeredCasimir T.center + (card R * card C * (card R - card C) / 4 : ℂ) • 1 := by
  rw [centeredCasimir_swap_oscRows, centeredCasimir_oscRows]
  module

omit [DecidableEq R] [DecidableEq C] in
/-- The squares of the centred parameters `T.centeredParam l r = l r - 2γ + n'` (with
`γ = T.rowShift`, `n' = card C`) sum to four times the sum of the squares of `λ_r - T.center`, for
`l = 2λ`. -/
theorem sum_centeredParam_sq (l : HCParam ε) :
    ∑ r : R, (T.centeredParam l r : ℂ) ^ 2 = 4 * ∑ r : R, (l r / 2 - T.center) ^ 2 := by
  rw [mul_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  push_cast [center]
  ring

end FockDualPair

/-- For matching parameters `l = 2λ`, `l' = 2λ'` of the pair `T` (both of large gap, with centred
parameters that are opposite or small), `|u|² - |ρ|² + n n' d₀ / 4 = |u'|² - |ρ'|²`. Here
`u = λ - T.center` and `u' = λ' - T.swap.center`, with the centres `T.rowShift - n'/2` and
`T.columnShift - n/2` of the row and column actions; `|u|²` is the sum of squares, `n = card R`,
`n' = card C`, `d₀ = n - n'`, and `n (n² - 1) / 12`, `n' (n'² - 1) / 12` are `|ρ|²`, `|ρ'|²`. -/
theorem IsMatch.centered_casimirValue_eq {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') :
    (∑ r : R, (l r / 2 - T.center) ^ 2 - card R * (card R ^ 2 - 1) / 12 +
        card R * card C * (card R - card C) / 4 : ℂ) =
      (∑ c : C, (l' c / 2 - T.swap.center) ^ 2 - card C * (card C ^ 2 - 1) / 12 : ℂ) := by
  have h_unmatched :
      3 * (∑ r, (T.centeredParam l r : ℂ) ^ 2 - ∑ c, (T.swap.centeredParam l' c : ℂ) ^ 2) =
        (card R - card C) * ((card R - card C) ^ 2 - 1) :=
    mod_cast hm.three_mul_sum_sq_sub
  -- What remains is `n³ - n'³ - d₀³ = 3 n n' d₀`.
  rw [T.sum_centeredParam_sq, T.swap.sum_centeredParam_sq] at h_unmatched
  linear_combination h_unmatched / 12

end Casimir

end New
end
end

/-!
# Existence of joint harmonics, Howe's argument and the local theta correspondence

This file works in the polynomial (Fock) model of a dual pair of unitary groups. For matching
parameters, a joint harmonic is built as a product of minors along layers. For an oscillator pair,
the projection of a joint harmonic by the discrete series kernel is then nonzero, is fixed by
`π'(f)` for functions `f` that reproduce the kernel of the second group, and generates all projected
polynomial vectors under bump functions of the second group.

## Main definitions and results

* `New.IsLayering`: finitely many layers, each a list of rows paired with columns, of weight `ν`.
* `New.IsMatch.isLayering`: for matching parameters (`New.IsMatch`) the sets of variables
  `New.FockDualPair.Layer` are layers of weight `New.HCParam.lowestKType l`.
* `New.IsMatch.exists_isJointHarmonic`: hence a joint harmonic (`New.IsJointHarmonic`) exists.
* `New.IsJointHarmonic.howe_argument`: in the polynomial (Fock) model with its row action
  `T.oscRows` and column action `T.swap.oscRows`, a subspace that is stable under the columns,
  contains a joint harmonic (`New.IsJointHarmonic`) and contains certain images of the row operators
  is the whole space.
* `New.OscillatorPair.re_inner_integratedRep_pos`: for a joint harmonic `Φ` and `Φ₁ = π(e_λ) Φ`,
  with `e_λ` the discrete series kernel, `⟨Φ, Φ₁⟩` has positive real part.
* `New.OscillatorPair.integratedRep_integratedRep_eq_self`: `π'(f) Φ₁ = Φ₁` for every `f` of
  suitable decay that reproduces `e_λ'`; the proof compares the Casimir operators of the two groups
  on `Φ` and uses `New.integratedRep_fix_of_isKHighest`.
* `New.OscillatorPair.exists_bump_integratedRep_eq`: every `π(e_λ) P` is obtained from `Φ₁` by a
  bump function of the second group; the proof rests on `New.IsJointHarmonic.howe_argument`.

Notions from other files:
* `New.HCParam.IsKHighest`: each matrix unit `E a a` acts on `x` by `ν a`, and `x` is killed by the
  compact raising operators, the `E a b` with `ε a = ε b` and `l b < l a`.
* `New.IsJointHarmonic`: `l` and `l'` match (`New.IsMatch`), and `Φ ≠ 0` is highest for rows and
  columns, of the weights of the two lowest `K`-types, and harmonic along rows and columns.
* `New.OscillatorPair`: two commuting oscillator representations on one Fock space, one acting on
  the rows and one on the columns.
* `New.pairSign`: the sign `σ * ε r * ε' c` of the variable in row `r` and column `c`, with
  `σ = T.globalSign`; `T.varSign (r, c)` is this sign.
* `New.FockDualPair.IsMatchedPair`: the row `r` is matched with the column `c`: with `n = card R`,
  `n' = card C`, `γ = T.rowShift`, `γ' = T.columnShift` and `a = l r - 2γ + n'`, one
  has `a = -(l' c - 2γ' + n)` and `|n - n'| < σ * ε r * ε' c * a`.
* `New.HCParam.lowestKType`: the integer vector Λ = λ+ρ−2ρ_c for a parameter l = 2λ, the highest
  weight of the lowest K-type.

## Relation to the literature

Known result: Theta correspondence of discrete series for real unitary dual pairs, with joint
harmonics. Only matched parameters with large gaps on Fock space are treated. The joint harmonic
exists and is unique up to scalar, and its projection is fixed by the partner's `π'(f)` for every
`f` of suitable decay that reproduces the partner's discrete series kernel. The projection of every
polynomial vector is a compactly supported smoothing, under the second group, of the projected joint
harmonic. Source: J.-S. Li, Theta lifting for unitary representations with nonzero cohomology, Duke
Math. J. 61 (1990) 913-937; R. Howe, Transcending classical invariant theory, J. Amer. Math. Soc. 2
(1989); A. Paul, First occurrence for the dual pairs (U(p,q), U(r,s)), Canad. J. Math. 51 (1999)
636-657, Theorem 2.7.
-/

@[expose] public section

/-!
## Products of minors along layers and existence of joint harmonics

Existence of joint harmonics in the Fock model `T` of a dual pair of unitary groups. Polynomials in
the variables `X (T.varEquiv (r, c))` carry two actions. `New.FockDualPair.oscRows` is an action of
`gl R` (rows `r`, signs `ε`). `New.FockDualPair.vacuumWeight` is the weight of the vacuum `1`.
`New.FockDualPair.IsTermwiseHarmonic` forbids, in a monomial, two variables in one column from rows
of opposite signs; for `T.swap` it is the same with rows and columns exchanged.

A matched pair (row `r`, column `c`) occurs in `|New.FockDualPair.relWeight l r|` layers, one at
each level below that number. The signs cut the variables into four quadrants; the layers of one
pair of signs are nested and give the leading minors of that quadrant.
-/

section JointHarmonicExists

namespace New

open Matrix MvPolynomial Finset Units DiscreteSeries Function Fischer

variable {L : Type*} [Fintype L] {I : L → Type} [∀ t : L, Fintype (I t)]
  [∀ t : L, DecidableEq (I t)] {R C : Type} [Fintype C] [DecidableEq C]
  {ε : R → ℤˣ} {ε' : C → ℤˣ} {ι : Type} [Fintype ι] {T : FockDualPair ε ε' ι} {l ν : HCParam ε}
  {l' ν' : HCParam ε'} {ρ : (t : L) → I t → R} {κ : (t : L) → I t → C}

/-- A derivation of a polynomial ring sends a finite product to the sum of the products in which
one factor is replaced by its derivative. -/
theorem derivation_apply_prod {α : Type*} [DecidableEq α]
    (D : Derivation ℂ (MvPolynomial R ℂ) (MvPolynomial R ℂ)) (s : Finset α)
    (f : α → MvPolynomial R ℂ) :
    D (s.prod f) = ∑ i ∈ s, s.prod (update f i (D (f i))) := by
  induction s using cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have h_tail : ∀ i ∈ s, (cons a s ha).prod (update f i (D (f i))) =
        f a * s.prod (update f i (D (f i))) := fun i hi ↦ by grind
    calc D ((cons a s ha).prod f) = D (f a) * s.prod f + f a * D (s.prod f) := by
          simp [prod_cons, D.leibniz, mul_comm, add_comm, -cons_eq_insert]
      _ = D (f a) * s.prod f + ∑ i ∈ s, f a * s.prod (update f i (D (f i))) := by rw [ih, mul_sum]
      _ = ∑ i ∈ cons a s ha, (cons a s ha).prod (update f i (D (f i))) := by
          rw [sum_cons, prod_cons, update_self, prod_update_of_notMem ha, sum_congr rfl h_tail]

/-- If a derivation `D` acts on the columns of each matrix `M t` of polynomials through the matrix
`N t` (column `i` goes to `∑ j, N t i j •` column `j`), then it multiplies `∏ t, det (M t)` by
the sum of the traces of the `N t`. -/
theorem derivation_prod_det (D : Derivation ℂ (MvPolynomial R ℂ) (MvPolynomial R ℂ))
    (N M : (t : L) → Matrix (I t) (I t) (MvPolynomial R ℂ))
    (h_col : ∀ (t : L) (i k : I t), D (M t k i) = ∑ j : I t, N t i j • M t k j) :
    D (∏ t : L, det (M t)) = (∑ t : L, ∑ i : I t, N t i i) * ∏ t : L, det (M t) := by
  -- Each determinant is an eigenvector of `D` with eigenvalue the trace of `N t`; by the Leibniz
  -- rule the eigenvalues add up on the product.
  have h_det {t : L} : D (M t).det = ∑ i : I t, N t i i • (M t).det := by
    -- Expanding the determinant, `D` acts on one column at a time; replacing column `i` by a
    -- combination of the columns scales the determinant by `N t i i`.
    calc D (M t).det = ∑ i, ((M t).updateCol i fun k : I t ↦ ∑ j : I t, N t i j • M t k j).det := by
          simp +contextual [det_apply', updateCol, update_apply, mul_sum, derivation_apply_prod,
            h_col, sum_comm (α := I t)]
      _ = ∑ i : I t, N t i i • (M t).det := by simp only [det_updateCol_sum]
  induction (univ : Finset L) using cons_induction with
  | empty => simp
  | cons t s ht ih =>
    simp only [prod_cons, D.leibniz, ih, h_det, sum_cons, _root_.smul_eq_mul, ← sum_mul]
    ring

variable [DecidableEq R]

/-- Finitely many layers `t`, each pairing distinct rows `ρ t` with columns `κ t`. Layers that share
a row have columns of one sign. With each of its rows a layer contains all rows of the same sign as
that row that lie further out in `l` than it, in the direction given by the sign
`New.FockDualPair.varSign` of its variable in that layer. The total weight is `ν`. -/
structure IsLayering (T : FockDualPair ε ε' ι) (l ν : HCParam ε) (ρ : (t : L) → I t → R)
    (κ : (t : L) → I t → C) : Prop where
  /-- The rows of a layer are distinct. -/
  injective (t : L) : Injective (ρ t)
  /-- Two layers (possibly the same) that share a row have all their columns of one sign. -/
  sign_eq (t u : L) (i : I t) (j : I u) (k : I t) (m : I u) :
      ρ t i = ρ u j → ε' (κ t k) = ε' (κ u m)
  /-- A layer with the row `ρ t i` has every row `r` of the same sign with `l r > l (ρ t i)` if
  `New.FockDualPair.varSign` is `1` at `(ρ t i, κ t i)`, with `l r < l (ρ t i)` if it is `-1`. -/
  closed (t : L) (i : I t) (r : R) :
      ε r = ε (ρ t i) → 0 < T.varSign (ρ t i, κ t i) * (l r - l (ρ t i)) → ∃ j : I t, ρ t j = r
  /-- The weight `ν r` is that of the vacuum plus the signs `New.FockDualPair.varSign` at the pairs
  `(r, κ t i)`, over all `(t, i)` with row `ρ t i = r`. -/
  weight_eq (r : R) :
      ν r = T.vacuumWeight (ε r) + ∑ t : L, ∑ i : I t with ρ t i = r, (T.varSign (r, κ t i)).val

omit [Fintype ι] in
/-- Let `(ρ, κ)` be layers and let `P` be the product of their minors, with the matrices transposed.
If `a = b`, or `a` has the sign of `b` and lies further out than `b` in the direction `s`, then the
polarisation `∑ X (a, c) * ∂P/∂X (b, c)`, over the columns `c` where the variable `(b, c)` has sign
`s`, is `P` times the number of `(t, i)` with `ρ t i = a = b` and `T.varSign (b, κ t i) = s`. -/
theorem IsLayering.polarization_prod_det (H : IsLayering T l ν ρ κ) {P : MvPolynomial ι ℂ}
    (hP : P = ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))ᵀ)
    (a b : R) (s : ℤˣ) (hε : ε a = ε b) (hab : a = b ∨ s * l b < s * l a) :
    T.polarization P a b s =
      (∑ t : L, ∑ i : I t,
        if ρ t i = b ∧ ρ t i = a ∧ T.varSign (b, κ t i) = s then 1 else 0) * P := by
  classical
  -- The polarisation is a derivation, so `derivation_prod_det` applies.
  let D : Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) :=
    .mk' (∑ c with T.varSign (b, c) = s,
        (X (T.varEquiv (a, c)) : MvPolynomial ι ℂ) • (pderiv (T.varEquiv (b, c))).toLinearMap)
      (by simp [mul_sum, ← sum_add_distrib, mul_add, mul_left_comm])
  -- In each layer `D` sends row `b` to row `a` or to zero, and kills the other rows.
  have hD (t : L) (i k : I t) : D (X (T.varEquiv (ρ t i, κ t k))) =
      ∑ j : I t, (if ρ t i = b ∧ ρ t j = a ∧ T.varSign (b, κ t i) = s
        then (1 : MvPolynomial ι ℂ) else 0) • X (T.varEquiv (ρ t j, κ t k)) := by
    have h_col_sign : ε' (κ t k) = ε' (κ t i) := H.sign_eq t t i i k i rfl
    obtain ⟨j, rfl⟩ | ha := em (∃ j : I t, ρ t j = a)
    · simp [D, (H.injective t).eq_iff, pairSign, h_col_sign, Pi.single_apply, ite_and]
    · -- row `a` is missing, so by `H.closed` row `b` is missing too or has the wrong sign
      have h_wrong_sign : ρ t i = b → T.globalSign * ε b * ε' (κ t i) ≠ s := fun hb hs ↦ hab.elim
        (fun h_eq ↦ ha ⟨i, hb.trans h_eq.symm⟩) fun h_out ↦
          ha (H.closed t i a (by rw [hb, hε]) (by simpa [hb, hs, pairSign, mul_sub] using h_out))
      simp +contextual [D, pairSign, Pi.single_apply, ite_and, not_exists.1 ha, h_col_sign,
        h_wrong_sign]
  simpa [D, hP, FockDualPair.polarization, -sum_boole] using
    derivation_prod_det D _ (fun t : L ↦ (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))ᵀ) hD

variable [Fintype R]

omit [Fintype ι] in
/-- Let `(ρ, κ)` be a layering of weight `ν` for `l`: finitely many layers `t`, each pairing
distinct rows `ρ t` with columns `κ t`, such that layers sharing a row have columns of one sign,
each layer contains with each of its rows all rows of the same sign lying further out in `l` in the
direction of the sign of its variable, and the total weight is `ν`. The product `P` over `t` of the
minors of the variables with rows `ρ t` and columns `κ t`, written here with the transposed
matrices, is `K`-highest of weight `ν` for the row action `T.oscRows` and `l`. Also, no monomial of
`P` has two variables in one row whose columns have opposite signs. -/
theorem IsLayering.isKHighest_and_isTermwiseHarmonic (H : IsLayering T l ν ρ κ)
    {P : MvPolynomial ι ℂ}
    (hP : P = ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))ᵀ) :
    l.IsKHighest T.oscRows ν P ∧ T.swap.IsTermwiseHarmonic P := by
  classical
  -- By `oscRows_E_eq_polarization_sub` the compact matrix unit `E a b` is the polarisation for
  -- `a, b, 1` minus the one for `b, a, -1`, plus the weight of the vacuum if `a = b`. Both
  -- polarisations act on `P` by scalars (`IsLayering.polarization_prod_det`).
  refine ⟨⟨fun a ↦ ?_, fun a b hε hl ↦ ?_⟩, fun a b c hε ↦ ?_⟩
  · -- weight: the two counts differ by the sum of signs in `H.weight_eq`
    have h_sign (t : L) (i : I t) :
        ((if ρ t i = a then if T.varSign (a, κ t i) = 1 then 1 else 0 else 0) -
            if ρ t i = a then if T.varSign (a, κ t i) = -1 then 1 else 0 else 0 :
            MvPolynomial ι ℂ) =
          MvPolynomial.C (if ρ t i = a then ((T.varSign (a, κ t i)).val : ℂ) else 0) := by
      split_ifs <;> simp_all [Int.units_ne_iff_eq_neg]
    -- so the difference of the two counts is the sum of the signs
    rw [oscRows_E_eq_polarization_sub rfl, H.polarization_prod_det hP a a 1 rfl (.inl rfl),
      H.polarization_prod_det hP a a (-1) rfl (.inl rfl), ← sub_mul]
    simp [← sum_sub_distrib, sum_filter, h_sign, ite_and, -sum_boole, H.weight_eq, ← C_mul',
      ← add_mul, add_comm]
  · -- raising operators: `a ≠ b`, so both counts vanish
    have hne : a ≠ b := fun h ↦ hl.ne (by rw [h])
    simp +contextual [oscRows_E_eq_polarization_sub hε, hne, hne.symm, ite_and,
      H.polarization_prod_det hP a b 1 hε (.inr (by simpa using hl)),
      H.polarization_prod_det hP b a (-1) hε.symm (.inr (by simpa using hl))]
  · have h_absent (x : R × C) (hx : ∀ (t : L) (i j : I t), (ρ t i, κ t j) ≠ x) :
        pderiv (T.varEquiv x) P = 0 := by
      simp [hP, hx, derivation_prod_det _ 0]
    change pderiv (T.varEquiv (c, a)) (pderiv (T.varEquiv (c, b)) P) = 0
    -- by `H.sign_eq` one of the variables `(c, a)`, `(c, b)` does not occur
    by_cases h_occurs : ∃ (t : L) (i j : I t), (ρ t i, κ t j) = (c, b)
    · obtain ⟨t, i, j, h_eq⟩ := h_occurs
      rw [pderiv_comm, h_absent (c, a) fun u k m h_eq' ↦ hε (by grind [H.sign_eq u t k i m j]),
        map_zero]
    · rw [h_absent (c, b) fun t i j h_eq ↦ h_occurs ⟨t, i, j, h_eq⟩, map_zero]

omit [Fintype ι] in
/-- Let `(ρ, κ)` be layers of weight `ν` for the rows and `(κ, ρ)` layers of weight `ν'` for the
columns. Then the product over `t` of the minors of the variables with rows `ρ t` and columns `κ t`
is nonzero, highest of weight `ν` for the rows and `ν'` for the columns, and harmonic both ways. -/
theorem IsLayering.isJointHighest_prod_det (H : IsLayering T l ν ρ κ)
    (h_swap : IsLayering T.swap l' ν' κ ρ) :
    T.IsJointHighest l l' (∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j))))
      ν ν' := by
  set P : MvPolynomial ι ℂ := ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))
    with hP
  have h_ne : P ≠ 0 := by
    -- Each minor is the generic determinant with its variables renamed injectively.
    have h_inj (t : L) : Injective (T.varEquiv ∘ Prod.map (ρ t) (κ t)) :=
      T.varEquiv.injective.comp ((H.injective t).prodMap (h_swap.injective t))
    have h_minor (t : L) :
        rename (T.varEquiv ∘ Prod.map (ρ t) (κ t)) (mvPolynomialX (I t) (I t) ℂ).det ≠ 0 :=
      (map_ne_zero_iff _ (rename_injective _ (h_inj t))).2 (det_mvPolynomialX_ne_zero (I t) ℂ)
    simpa [hP, prod_eq_zero_iff, det_apply] using h_minor
  -- `IsLayering.isKHighest_and_isTermwiseHarmonic` applies to the columns as it stands, and to the
  -- rows after transposing the minors.
  obtain ⟨h_col_highest, h_col_harmonic⟩ := h_swap.isKHighest_and_isTermwiseHarmonic hP
  obtain ⟨h_row_highest, h_row_harmonic⟩ :=
    H.isKHighest_and_isTermwiseHarmonic (P := P) (by simp only [hP, det_transpose])
  exact ⟨h_ne, h_col_highest, h_col_harmonic, h_row_highest, h_row_harmonic⟩

omit [Fintype ι] in
/-- Version of `IsLayering.isJointHighest_prod_det` for a polynomial `P` that is given as the
product of the minors: `P` is nonzero, highest of weight `ν` for the rows and `ν'` for the columns,
and harmonic both ways. -/
theorem IsLayering.isJointHighest_of_eq_prod_det (H : IsLayering T l ν ρ κ)
    (h_swap : IsLayering T.swap l' ν' κ ρ) {P : MvPolynomial ι ℂ}
    (hP : P = ∏ t : L, det (of fun i j : I t ↦ X (T.varEquiv (ρ t i, κ t j)))) :
    T.IsJointHighest l l' P ν ν' := by
  subst hP
  exact H.isJointHighest_prod_det h_swap

omit [DecidableEq R] [DecidableEq C] [Fintype ι] in
/-- Let the parameters `l` and `l'` match: each row and each column is either matched, that is, its
centred parameter (`l r - 2 γ + card C` for a row) is large and opposite to that of its partner, or
has a small one. Then a row `r` of nonzero weight `T.relWeight l r` (the lowest `K`-type relative to
the vacuum) is matched with a column `c`, and the weight has the sign of the variable `(r, c)`. -/
theorem IsMatch.exists_isMatchedPair_of_relWeight_ne_zero (hm : IsMatch T l l') {r : R}
    (h_ne : T.relWeight l r ≠ 0) :
    ∃ c : C, T.IsMatchedPair l l' r c ∧ T.varSign (r, c) = (T.relWeight l r).sign := by
  obtain ⟨c, h_pair⟩ | h_free := hm.left r
  · have h_sign := hm.sign_mul_relWeight_nonneg r (T.varSign (r, c))
      (by linarith [h_pair.right, neg_le_abs (Fintype.card R - Fintype.card C : ℤ)])
    refine ⟨c, h_pair, ?_⟩
    rcases Int.units_eq_one_or (T.varSign (r, c)) with h | h <;> grind [Units.val_neg, val_one]
  · -- an unmatched row has weight both `≥ 0` and `≤ 0`
    have hf := abs_lt.1 h_free
    have h1 := hm.sign_mul_relWeight_nonneg r 1 (by grind [val_one])
    have h2 := hm.sign_mul_relWeight_nonneg r (-1) (by grind [Units.val_neg, val_one])
    grind [Units.val_neg, val_one]

omit [DecidableEq R] [DecidableEq C] [Fintype ι] in
/-- Let the row `r` be matched with the column `c` and have nonzero weight `T.relWeight l r`. A row
`r'` of the same sign that lies further out in `l`, in the direction of the sign of the variable
`(r, c)`, is matched with a column of the sign of `c`, and its weight is at least as large in
absolute value. -/
theorem IsMatch.exists_isMatchedPair_of_outer (hm : IsMatch T l l') {r r' : R} {c : C}
    (h_pair : T.IsMatchedPair l l' r c) (h_ne : T.relWeight l r ≠ 0) (h_row : ε r' = ε r)
    (h_out : 0 < T.varSign (r, c) * (l r' - l r)) :
    ∃ c' : C, T.IsMatchedPair l l' r' c' ∧ ε' c' = ε' c ∧
      (T.relWeight l r).natAbs ≤ (T.relWeight l r').natAbs := by
  -- The highest weight of the lowest `K`-type is dominant for the order of `l`.
  have h_dom : ∀ a b : R, ε a = ε b → l b < l a → l.lowestKType b ≤ l.lowestKType a := by
    simpa [IsKDominant] using hm.hasGap_row.isKDominant_lowestKType
  obtain ⟨c₀, h_pair₀, h_sign⟩ := hm.exists_isMatchedPair_of_relWeight_ne_zero h_ne
  obtain rfl : c₀ = c := hm.col_eq_of_isMatchedPair h_pair₀ h_pair
  -- By `h_dom` the weight moves in the direction of its sign.
  have h_mono : T.varSign (r, c₀) * T.relWeight l r ≤ T.varSign (r, c₀) * T.relWeight l r' := by
    grind [h_dom r r', h_dom r' r]
  have h_same_sign : (T.relWeight l r').sign = (T.relWeight l r).sign := by grind
  obtain ⟨c', h_pair', h_sign'⟩ :=
    hm.exists_isMatchedPair_of_relWeight_ne_zero (r := r') (by grind)
  have h_var : T.varSign (r', c') = T.varSign (r, c₀) :=
    Units.ext (h_sign'.trans (h_same_sign.trans h_sign.symm))
  exact ⟨c', h_pair', by simpa [pairSign, h_row] using h_var, by grind⟩

namespace FockDualPair

variable (T) (s : Equiv.Perm (ℤˣ × ℤˣ)) (w : ι → ℕ) (t : Fin (univ.sup w) × ℤˣ × ℤˣ)

/-- The layer `t` for the heights `w` of the variables. Here `t` is a level below the largest height
together with a pair of signs. The layer consists of the variables of height above that level whose
signs `(ε r, ε' c)`, for row `r` and column `c`, are sent to that pair by `s`. -/
abbrev Layer : Type :=
  {x : ι // t.1 < w x ∧ s ((T.varEquiv.symm x).map ε ε') = t.2}

/-- The row of a variable of the layer `t`. -/
def layerRow (x : T.Layer s w t) : R := (T.varEquiv.symm x).1

/-- The column of a variable of the layer `t`. -/
def layerCol (x : T.Layer s w t) : C := (T.varEquiv.symm x).2

variable {T s w t}

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem varEquiv_layerRow_layerCol (x : T.Layer s w t) :
    T.varEquiv (T.layerRow s w t x, T.layerCol s w t x) = x :=
  T.varEquiv.apply_symm_apply x

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem sign_layerCol_eq (x y : T.Layer s w t) :
    ε' (T.layerCol s w t x) = ε' (T.layerCol s w t y) :=
  congrArg Prod.snd (s.injective (x.property.right.trans y.property.right.symm))

end FockDualPair

omit [DecidableEq C] in
/-- Let `l = 2λ`, `l' = 2λ'` match (`IsMatch`): with `n = card R` and `n' = card C` both have gap
`500(n+n')³`, and with `ξ r = λ r − γ + n'/2` and `ξ' c = λ' c − γ' + n/2`, rows and columns pair
off as `ξ r = −ξ' c` with `σ ε r ε' c ξ r > |n−n'|/2`, the rest having small `|ξ|`. Let the height
`w` of the variable of `(r, c)` be `|T.relWeight l r|` (row-`r` entry of the lowest `K`-type minus
the vacuum weight) if `(r, c)` is matched, and `0` otherwise. Then the layers, with rows
`T.layerRow s w` and columns `T.layerCol s w`, form an `IsLayering` of weight `l.lowestKType`. The
permutation `s` of the pairs of signs lets the rows and the columns use the same layers. -/
theorem IsMatch.isLayering (hm : IsMatch T l l') (s : Equiv.Perm (ℤˣ × ℤˣ)) (w : ι → ℕ)
    (hw : ∀ (r : R) (c : C),
      w (T.varEquiv (r, c)) = if T.IsMatchedPair l l' r c then (T.relWeight l r).natAbs else 0) :
    IsLayering T l l.lowestKType (T.layerRow s w) (T.layerCol s w) := by
  -- The variable `(r, c)` lies in a layer of level `m` exactly when the pair is matched and
  -- `m < |T.relWeight l r|`.
  have h_level (r : R) (c : C) (m : ℕ) :
      m < w (T.varEquiv (r, c)) ↔ T.IsMatchedPair l l' r c ∧ m < (T.relWeight l r).natAbs := by
    grind
  have h_mem {t : Fin (univ.sup w) × ℤˣ × ℤˣ} (x : T.Layer s w t) {r : R}
      (h_row : T.layerRow s w t x = r) :
      T.IsMatchedPair l l' r (T.layerCol s w t x) ∧ t.1 < (T.relWeight l r).natAbs := by
    rw [← h_level, ← h_row, FockDualPair.varEquiv_layerRow_layerCol]
    exact x.property.left
  -- Variables of layers with the same row have the same column, so they are equal.
  have h_col {t u : Fin (univ.sup w) × ℤˣ × ℤˣ} {x : T.Layer s w t} {y : T.Layer s w u}
      (h_row : T.layerRow s w t x = T.layerRow s w u y) :
      T.layerCol s w t x = T.layerCol s w u y :=
    hm.col_eq_of_isMatchedPair (h_mem x h_row).left (h_mem y rfl).left
  have h_var {t u : Fin (univ.sup w) × ℤˣ × ℤˣ} {x : T.Layer s w t} {y : T.Layer s w u}
      (h_row : T.layerRow s w t x = T.layerRow s w u y) : (x : ι) = y := by
    grind [FockDualPair.varEquiv_layerRow_layerCol]
  refine ⟨fun t x y h_row ↦ Subtype.ext (h_var h_row), fun t u x y x' y' h_row ↦ by
    rw [FockDualPair.sign_layerCol_eq x' x, h_col h_row, FockDualPair.sign_layerCol_eq y y'],
    ?_, fun r ↦ ?_⟩
  · -- A row further out is matched with a column of the same sign and reaches the same level.
    intro t x r' h_row h_out
    obtain ⟨h_pair, h_lt⟩ := h_mem x rfl
    obtain ⟨c', h_pair', h_sign, h_le⟩ :=
      hm.exists_isMatchedPair_of_outer h_pair (by lia) h_row h_out
    exact ⟨⟨T.varEquiv (r', c'), (h_level r' c' t.1).2 ⟨h_pair', h_lt.trans_le h_le⟩, by
      simpa [h_row, h_sign, FockDualPair.layerRow, FockDualPair.layerCol, Prod.map] using
        x.property.right⟩,
      by simp [FockDualPair.layerRow]⟩
  · -- The indices with row `r` correspond, by their level, to the numbers below
    -- `|T.relWeight l r|`, and each adds the sign of `T.relWeight l r`.
    trans T.vacuumWeight (ε r) + ∑ _m ∈ range (T.relWeight l r).natAbs, (T.relWeight l r).sign
    · rw [sum_const, card_range, nsmul_eq_mul, mul_comm, Int.sign_mul_natAbs, add_sub_cancel]
    rw [add_right_inj, sum_sigma', eq_comm]
    refine sum_of_injOn (fun ⟨t, _⟩ ↦ (t.1 : ℕ)) ?_ ?_ ?_ ?_
    · -- the level determines the index
      rintro ⟨t, x⟩ hx ⟨u, y⟩ hy h_eq
      simp only [Finset.mem_coe, mem_sigma, mem_filter, mem_univ, true_and] at hx hy
      have h_xy : (x : ι) = y := h_var (hx.trans hy.symm)
      obtain rfl : t = u :=
        Prod.ext (Fin.ext h_eq) (by rw [← x.property.right, ← y.property.right, h_xy])
      rw [Subtype.ext h_xy]
    · -- the level lies below `|T.relWeight l r|`
      exact fun ⟨t, x⟩ hx ↦ by simpa using (h_mem x (r := r) (by simpa using hx)).right
    · -- every level below `|T.relWeight l r|` occurs, at the column matched with `r`
      intro m h_range h_missing
      obtain ⟨c, h_pair, -⟩ :=
        hm.exists_isMatchedPair_of_relWeight_ne_zero (r := r) (by grind)
      have h_height : m < w (T.varEquiv (r, c)) := (h_level r c m).2 ⟨h_pair, mem_range.1 h_range⟩
      let x : T.Layer s w (⟨m, h_height.trans_le (le_sup (mem_univ _))⟩, s (ε r, ε' c)) :=
        ⟨T.varEquiv (r, c), h_height, by simp⟩
      have h_row : T.layerRow s w _ x = r := by simp [x, FockDualPair.layerRow]
      exact absurd ⟨⟨_, x⟩, by simpa using h_row, rfl⟩ h_missing
    · -- the sign of the variable is that of the weight
      rintro ⟨t, x⟩ hx
      obtain ⟨h_pair, h_lt⟩ := h_mem x (r := r) (by simpa using hx)
      obtain ⟨c, h_pair', h_sign⟩ := hm.exists_isMatchedPair_of_relWeight_ne_zero (r := r) (by lia)
      rwa [hm.col_eq_of_isMatchedPair h_pair' h_pair] at h_sign

/-- If the parameters `l = 2λ`, `l' = 2λ'` match, there is a joint harmonic. With `n = card R` and
`n' = card C`, matching means that both have gap `500(n+n')³`, and the entries
`ξ r = λ r − γ + n'/2`, `ξ' c = λ' c − γ' + n/2` pair off as `ξ r = −ξ' c` with
`σ ε r ε' c ξ r > |n−n'|/2`, the rest having small `|ξ|`. A joint harmonic is a nonzero polynomial
that is highest of weights `New.HCParam.lowestKType l` for the rows and
`New.HCParam.lowestKType l'` for the columns, and satisfies `New.FockDualPair.IsTermwiseHarmonic`
along columns and along rows (for `T` and `T.swap`).

This is the existence part of the known correspondence of discrete series by joint harmonics. -/
theorem IsMatch.exists_isJointHarmonic (hm : IsMatch T l l') :
    ∃ Φ : MvPolynomial ι ℂ, IsJointHarmonic T l l' Φ := by
  classical
  -- Take the product of the minors of the layers of `IsMatch.isLayering`. The same layers serve
  -- for the columns, with the two signs exchanged, since matched weights are opposite.
  let w : ι → ℕ := fun x ↦ let (r, c) := T.varEquiv.symm x
    if T.IsMatchedPair l l' r c then (T.relWeight l r).natAbs else 0
  refine ⟨_, hm, (hm.isLayering 1 w fun _ _ ↦ by simp [w]).isJointHighest_prod_det
    (hm.swap.isLayering (Equiv.prodComm ℤˣ ℤˣ) w fun c r ↦ ?_)⟩
  change w (T.varEquiv (r, c)) = _
  simp only [w, Equiv.symm_apply_apply]
  grind [hm.relWeight_eq_neg, Int.natAbs_neg, pairSign, int_unit_val_eq_one_or_neg_one,
    val_mul, Units.val_neg]

end New

end JointHarmonicExists

/-!
## Howe's argument in Fock space

The proof is an induction on the degree with the Fischer inner product, ending in the uniqueness of
the joint harmonic.
-/

section HoweArgument

open New MvPolynomial Submodule Int Fischer DiscreteSeries Fock

variable {R C ι : Type} [Fintype R] [Fintype C] {ε : R → ℤˣ} {ε' : C → ℤˣ}
  {T : FockDualPair ε ε' ι} {l : HCParam ε} {l' : HCParam ε'}

omit [Fintype R] in
/-- For rows `a` and `b` with `ε a ≠ ε b`: if row `b` of `Q` has no variable of sign `1`, or row `a`
has none of sign `-1`, then the Laplacian `T.fockLaplacian a b` kills `Q`. It is a sum, over the
columns `c` with `T.varSign (a, c) = -1`, of terms built from `∂/∂X(a,c) ∂/∂X(b,c)`. -/
theorem New.Fischer.fockLaplacian_eq_zero_of_pderiv_eq_zero {Q : MvPolynomial ι ℂ} {a b : R}
    (hab : ε a ≠ ε b)
    (h_pure : (∀ c : C, T.varSign (b, c) = 1 → pderiv (T.varEquiv (b, c)) Q = 0) ∨
      ∀ c : C, T.varSign (a, c) = -1 → pderiv (T.varEquiv (a, c)) Q = 0) :
    T.fockLaplacian a b Q = 0 := by
  rw [FockDualPair.fockLaplacian, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun c hc ↦ ?_
  have ha : T.varSign (a, c) = -1 := (Finset.mem_filter.1 hc).2
  have hb : T.varSign (b, c) = 1 := by
    rw [← neg_neg (1 : ℤˣ), ← ha]
    simp [units_ne_iff_eq_neg.1 hab, pairSign]
  suffices pderiv (T.varEquiv (a, c)) (pderiv (T.varEquiv (b, c)) Q) = 0 by
    simpa [glOp, ha, hb, raiseOp, lowerOp]
  rcases h_pure with h_row_b | h_row_a
  · rw [h_row_b c hb, map_zero]
  · rw [pderiv_comm, h_row_a c ha, map_zero]

/-- For matched parameters (each row is matched with a column or has a small centred parameter) and
`l b ≤ l a`, the centred parameter `l b - 2γ + card C` of row `b` is below `card R - card C` or that
of row `a` is above `card C - card R`. -/
theorem New.IsMatch.centeredParam_lt_or_lt (hm : IsMatch T l l') {a b : R} (h_le : l b ≤ l a) :
    (Fintype.card C - Fintype.card R : ℤ) < -T.centeredParam l b ∨
      (Fintype.card C - Fintype.card R : ℤ) < T.centeredParam l a := by
  have h_abs := neg_le_abs (Fintype.card R - Fintype.card C : ℤ)
  obtain ⟨c, -, h_large⟩ | h_free := hm.left a
  · -- Row `a` is matched: its centred parameter, times the sign of the variable, is large.
    rcases int_unit_val_eq_one_or_neg_one (T.varSign (a, c)) with h_sign | h_sign <;>
      rw [h_sign] at h_large
    · exact .inr (by linarith)
    · exact .inl (by linarith)
  · exact .inr (by linarith [(abs_lt.1 h_free).1])

variable [Fintype ι]

/-- If `G` does not contain all polynomials of degree at most `j`, then some nonzero one of them is
orthogonal to those in `G` for the Fischer inner product. -/
theorem New.Fischer.perpInDegree_ne_bot {j : ℤ} {G : Submodule ℂ (MvPolynomial ι ℂ)}
    (hj : ¬ polyDegreeLE j ≤ G) : perpInDegree j G ≠ ⊥ := by
  intro h_bot
  have h_split : polyDegreeLE j ⊓ G ⊔ perpInDegree j G = polyDegreeLE j :=
    sup_orthogonal_inf_of_hasOrthogonalProjection inf_le_left
  exact hj (by simpa [h_bot] using h_split)

omit [Fintype ι] in
/-- Let `Q` be highest of the weight `Λ` of the lowest `K`-type for the rows and harmonic for the
columns (each `T.swap.fockLaplacian c d` with `ε' c ≠ ε' d` kills `Q`). If `s` times the centred
parameter `l r - 2γ + card C` of row `r` exceeds `card C - card R`, then `Q` has no variable of sign
`-s` in that row. -/
theorem New.IsMatch.pderiv_eq_zero_of_lt_centeredParam [DecidableEq C] [DecidableEq R]
    (hm : IsMatch T l l') {Q : MvPolynomial ι ℂ}
    (h_highest : l.IsKHighest T.oscRows l.lowestKType Q) (h_harm : T.swap.IsLaplaceHarmonic Q)
    (r : R) (s : ℤˣ) (hr : Fintype.card C - Fintype.card R < (s : ℤ) * T.centeredParam l r)
    (c : C) (hc : T.varSign (r, c) = -s) : pderiv (T.varEquiv (r, c)) Q = 0 := by
  obtain ⟨h_weight, h_row⟩ := h_highest
  exact (polarization_self_eq_smul_of_isCompactPrimitive hm.hasGap_row.injective h_row h_harm
    (h_weight r) (hm.sign_mul_relWeight_nonneg r s hr)).2 c hc

/-- Howe's argument: a column-stable subspace that contains a joint harmonic and the images (a)–(c)
below is the whole space.

Let `Φ` be a joint harmonic of the dual pair `T`, that is, a nonzero polynomial, highest of the
weights of the lowest `K`-types and harmonic for rows and columns. Let `G` be a space of polynomials
that is stable under the action `T.swap.oscRows` on the columns and contains `Φ`. Write `ρ` for the
action `T.oscRows` on the rows and `Λ` for `l.lowestKType`. Suppose that `G` contains
(a) `ρ X P` for every matrix `X` and every highest vector `P` of a weight `ν` with `ν - Λ` outside
`l.rootCone`, the cone of the positive roots,
(b) the images of the `E b a` with `ε a = ε b` and `l b < l a`,
(c) the images of the `E a a - Λ a`.
Then `G` is the whole space. -/
theorem New.IsJointHarmonic.howe_argument [DecidableEq C] [DecidableEq R] {Φ : MvPolynomial ι ℂ}
    (hΦ : IsJointHarmonic T l l' Φ) (G : Submodule ℂ (MvPolynomial ι ℂ))
    (hG_cols : ∀ Y : Matrix C C ℂ, G ∈ (T.swap.oscRows Y).invtSubmodule) (hΦ_mem : Φ ∈ G)
    (h_off_cone : ∀ (ν : R → ℤ) (P : MvPolynomial ι ℂ), l.IsKHighest T.oscRows ν P →
      ν - l.lowestKType ∉ l.rootCone → ∀ X : Matrix R R ℂ, T.oscRows X P ∈ G)
    (h_lower : ∀ a b : R, ε a = ε b → l b < l a →
      ∀ P : MvPolynomial ι ℂ, T.oscRows.E b a P ∈ G)
    (h_diag : ∀ (a : R) (P : MvPolynomial ι ℂ),
      T.oscRows.E a a P - (l.lowestKType a : ℂ) • P ∈ G) :
    G = ⊤ := by
  -- Induct on the degree. If `G` missed a polynomial of degree at most `j`, the orthogonal
  -- complement `perpInDegree j G` would contain a vector `Q ≠ 0` highest for the columns; it has
  -- all the properties that characterize the joint harmonic `Φ ∈ G` up to a scalar, so `Q ∈ G`
  -- and `Q = 0`.
  suffices h_deg : ∀ j : ℤ, polyDegreeLE j ≤ G by
    exact eq_top_iff'.2 fun P ↦ h_deg P.totalDegree fun d hd ↦ ofNat_le.2 (le_totalDegree hd)
  refine Int.strongRec (m := 0) (fun j hj_neg ↦ ?_) fun j _ ih ↦ ?_
  · have h_empty : {d : ι →₀ ℕ | (d.degree : ℤ) ≤ j} = ∅ := by ext; simp; lia
    simp [polyDegreeLE, restrictSupport_eq_span, h_empty]
  by_contra hj
  obtain ⟨-, Q, hQ, hQ_ne, -, h_col⟩ := l'.exists_highest_vector (ρ := T.swap.oscRows)
    (perpInDegree j G) (perpInDegree_ne_bot hj) fun _ _ hcd ↦
      (Module.End.mem_invtSubmodule_iff_mapsTo _).2 (mapsTo_perpInDegree hcd (hG_cols _))
  -- `Q` is highest of weight `Λ` for the rows: take adjoints in `h_diag` and `h_lower`. If
  -- `E b a` maps `N` into `G`, then `E a b` maps the complement of `G` into that of `N`
  -- (`mapsTo_perpInDegree`).
  have h_weight (a : R) : T.oscRows.E a a Q = (l.lowestKType a : ℂ) • Q := by
    have h_stable : G ≤ G.comap (T.oscRows.E a a) :=
      fun P hP ↦ (G.sub_mem_iff_left (G.smul_mem _ hP)).1 (h_diag a P)
    exact sub_eq_zero.1 (eq_zero_of_mem_perpInDegree
      (sub_mem (mapsTo_perpInDegree rfl h_stable hQ) (smul_mem _ _ hQ)) (h_diag a Q))
  have h_row : T.oscRows.IsCompactPrimitive l Q := fun a b hab hl ↦
    eq_zero_of_mem_perpInDegree
      (mapsTo_perpInDegree hab (fun P _ ↦ h_lower a b hab hl P) hQ) mem_top
  have h_highest : l.IsKHighest T.oscRows l.lowestKType Q := ⟨h_weight, h_row⟩
  -- The Laplacians of the columns kill `Q` by Fischer's decomposition, as `G` is stable under the
  -- columns.
  have h_harm_col : T.swap.IsLaplaceHarmonic Q :=
    fun _ _ hcd ↦ fockLaplacian_eq_zero ih hQ hcd rfl fun h_mem ↦ hG_cols _ h_mem
  -- The Laplacians of the rows kill `Q`: it suffices to treat one whose value is a highest vector,
  -- of weight `Λ + e_a - e_b`.
  have h_harm_row : T.IsLaplaceHarmonic Q := by
    refine isLaplaceHarmonic_of_isKHighest h_highest fun a b hab h_highest' ↦ ?_
    by_cases h_cone :
        l.lowestKType + Pi.single a 1 - Pi.single b 1 - l.lowestKType ∈ l.rootCone
    · -- In the cone `l b ≤ l a` (pair with `-l`), so row `b` or row `a` of `Q` has variables of
      -- one sign only.
      have h_le : l b ≤ l a := by simpa [add_assoc] using h_cone (-l) (by simp)
      refine fockLaplacian_eq_zero_of_pderiv_eq_zero hab ?_
      have h_pure := hΦ.pderiv_eq_zero_of_lt_centeredParam h_highest h_harm_col
      rcases hΦ.centeredParam_lt_or_lt h_le with h_small | h_large
      · exact .inl fun c hc ↦ h_pure b (-1) (by simpa using h_small) c (by simpa using hc)
      · exact .inr (h_pure a 1 (by simpa using h_large))
    · -- Off the cone `h_off_cone` lets Fischer's decomposition apply again.
      exact fockLaplacian_eq_zero ih hQ hab rfl fun _ ↦ h_off_cone _ _ h_highest' h_cone _
  -- By uniqueness `Q = c • Φ`, so `Q ∈ G`.
  obtain ⟨c, rfl⟩ : ∃ c : ℂ, Q = c • Φ := hΦ.unique
    ⟨hQ_ne, h_col, h_harm_row, h_highest, h_harm_col⟩ hΦ.isJointHighest.isPreJointHarmonic
  exact hQ_ne (eq_zero_of_mem_perpInDegree hQ (G.smul_mem c hΦ_mem))

end HoweArgument

/-!
## The projected joint harmonic and the local theta correspondence

The analytic part of the local theta correspondence. Let `π`, `π'` be an oscillator pair on Fock
space (`New.OscillatorPair`), `Φ` a joint harmonic of parameters `l`, `l'`
(`New.IsJointHarmonic`), and `Φ₁ = π(e_λ) Φ`, where `π(f) = ∫ f g • π g` is
`New.integratedRep π f`, `e_λ` is `New.HCParam.dsKernel l` (the signs come from the type of `l`),
and a polynomial is read as a vector of Fock space by `New.Fock.polyVector`.

The results are stated for the projection `π(e_λ)` of the first group, which acts on the rows; those
for the second group follow by `New.OscillatorPair.swap`. To work with `-λ` in place of `λ`, apply
them to the parameters `-l` and `-l'`; the kernel `e_{-λ}` is the conjugate of `e_λ`.
-/

namespace New.OscillatorPair

variable {R C I : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] [Fintype I]
  [DecidableEq I] {η : I → ℤˣ} {ε : R → ℤˣ} {ε' : C → ℤˣ} {l : HCParam ε} {l' : HCParam ε'}
  {Φ : MvPolynomial I ℂ} {T : FockDualPair (R := R) (C := C) ε ε' I}
  {π : USign ε →* Fock.fockSpace η →L[ℂ] Fock.fockSpace η}
  {π' : USign ε' →* Fock.fockSpace η →L[ℂ] Fock.fockSpace η}

open DiscreteSeries Fock Finset MeasureTheory Fintype GlModule Matrix.Norms.L2Operator

/-- Let `T` be the data of a dual pair in Fock space: a sign `T.globalSign`, integers `T.rowShift`
and `T.columnShift`, and variables indexed by `R × C`, with `R` and `C` nonempty. If `π` of `U(ε)`
and `π'` of `U(ε')` form an oscillator pair for `T` (two commuting oscillator representations on
one Fock space, `π` on the rows and `π'` on the columns), then `π'` and `π` form an oscillator pair
for `T.swap`. `T.swap` exchanges rows and columns, has sign `-T.globalSign`, row shift
`T.columnShift` and column shift `T.rowShift`. -/
theorem swap (hp : OscillatorPair T π π') :
    OscillatorPair T.swap π' π where
  toOscillatorRep := hp.column_rep
  column_rep := by
    rw [T.swap_swap]
    exact hp.toOscillatorRep
  commute g h := (hp.commute h g).symm

/-- The operator `π(e_λ)` commutes with the action of the second group. -/
theorem map_integratedRep_dsKernel (hp : OscillatorPair T π π') [Nonempty R]
    (hΦ : IsJointHarmonic T l l' Φ) (g' : USign ε') (x : fockSpace η) :
    π' g' (integratedRep π l.dsKernel x) = integratedRep π l.dsKernel (π' g' x) := by
  -- `π(e_λ)` is an integral over the first group, and `π' g'` commutes with each `π g`.
  have h_int (L : fockSpace η →L[ℂ] fockSpace η) (y : fockSpace η) :
      L (integratedRep π l.dsKernel y) = ∫ g : USign ε, l.dsKernel g • L (π g y) :=
    map_integratedRep hp.unitary_rep
      ((hΦ.hasLargeGap le_rfl).integrable_dsKernel_mul_norm_pow _ (Nat.le_succ _)) L y
  calc π' g' (integratedRep π l.dsKernel x) = ∫ g : USign ε, l.dsKernel g • π g (π' g' x) := by
        simp only [h_int, ← mul_apply_eq_comp, (hp.commute _ g').eq]
    _ = integratedRep π l.dsKernel (π' g' x) := (h_int 1 _).symm

/-- Along the map `P ↦ π(e_λ) P` from polynomials to Fock space, the representation `π'` of the
second group has the column action `T.swap.oscRows` as its derived action. -/
theorem isDerivedAction_integratedRep (hp : OscillatorPair T π π') [Nonempty R]
    (hΦ : IsJointHarmonic T l l' Φ) :
    IsDerivedAction π' ((integratedRep π l.dsKernel).toLinearMap ∘ₗ polyVector η)
      T.swap.oscRows := by
  intro Y v
  -- `π(e_λ)` may be applied to the derivative of `π'` along `polyVector`.
  simpa [hp.map_integratedRep_dsKernel hΦ] using
    (hp.column_rep.derives Y v).map_clm (integratedRep π l.dsKernel)

/-- For an oscillator pair π, π' on Fock space and a joint harmonic Φ of parameters `l = 2λ` and
`l' = 2λ'`, the real part of ⟨Φ, π(e_λ)Φ⟩ is positive. Here `π(e_λ)` is the operator `∫ e_λ g • π g`
of the discrete series kernel `e_λ` (`New.HCParam.dsKernel`). -/
theorem re_inner_integratedRep_pos (hp : OscillatorPair T π π') [Nonempty R]
    (hΦ : IsJointHarmonic T l l' Φ) :
    0 < (fockInner Φ (integratedRep π l.dsKernel Φ)).re := by
  -- `Φ` is highest of weight `Λ` and `⟨Φ, π z Φ⟩ > 0` for positive definite `z`
  obtain ⟨h_ne, -, h_harmonic, h_highest, -⟩ := hΦ.isJointHighest
  exact re_integratedRep_dsKernel_pos (hΦ.hasLargeGap le_rfl) hp.unitary_rep hp.derives h_highest
    fun z ↦ hp.inner_pos Φ z h_ne h_harmonic

/-- Let `Φ` be a joint harmonic (nonzero, highest of the lowest `K`-types and harmonic on both
sides) of an oscillator pair `π`, `π'` (commuting oscillator representations) and `f` a function on
the second group such that `g ↦ f g ‖g‖ ^ card I` is integrable and `f * e_λ' = e_λ'`, where `e_λ`
and `e_λ'` are the discrete series kernels of the parameters `l` and `l'`. Then the operator `π'(f)`
fixes `π(e_λ) Φ`. This applies to `f = e_λ'` and to bump functions that reproduce `e_λ'`. -/
theorem integratedRep_integratedRep_eq_self (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) {f : USign ε' → ℂ}
    (hf : Integrable fun g : USign ε' ↦ f g * ‖g.val.val‖ ^ Fintype.card I)
    (h_repro : ∀ g : USign ε', ∫ y : USign ε', f y * l'.dsKernel (y⁻¹ * g) = l'.dsKernel g) :
    integratedRep π' f (integratedRep π l.dsKernel Φ) = integratedRep π l.dsKernel Φ := by
  -- Put `proj P = π(e_λ) P`. The polynomial `Φ` is highest of weight `Λ'` for the second group, so
  -- by rigidity it suffices that `proj Φ` has the Casimir value `l'.casimirValue`. Compare the
  -- centred Casimir elements of the two groups.
  obtain ⟨-, highest', -, ⟨h_weight, -⟩, -⟩ := hΦ.isJointHighest
  let proj : MvPolynomial I ℂ →ₗ[ℂ] fockSpace η :=
    (integratedRep π l.dsKernel).toLinearMap ∘ₗ polyVector η
  have h_casimir : proj (T.oscRows.casimirK 1 Φ) = (l.casimirValue : ℂ) • proj Φ :=
    integratedRep_dsKernel_casimir (hΦ.hasLargeGap le_rfl) hp.unitary_rep hp.derives
  have h_first : proj (T.oscRows.centeredCasimir T.center Φ) =
      (∑ r, (l r / 2 - T.center) ^ 2 - card R * (card R ^ 2 - 1) / 12 : ℂ) • proj Φ := by
    rw [centeredCasimir_apply _ _ h_weight, map_add, map_sub, map_smul, map_smul, h_casimir,
      ← hΦ.hasGap_row.casimirValue_sub_center, add_smul, sub_smul]
  have h_second : proj (T.swap.oscRows.centeredCasimir T.swap.center Φ) =
      (∑ c, (l' c / 2 - T.swap.center) ^ 2 - card C * (card C ^ 2 - 1) / 12 : ℂ) • proj Φ := by
    rw [T.centeredCasimir_swap_oscRows_eq_add, LinearMap.add_apply, map_add, h_first,
      LinearMap.smul_apply, one_apply_eq_self, map_smul, ← add_smul,
      hΦ.centered_casimirValue_eq]
  -- Restore the centre of the second group.
  have h_casimir' : proj (T.swap.oscRows.casimirK 1 Φ) = (l'.casimirValue : ℂ) • proj Φ := by
    rw [centeredCasimir_apply _ _ highest'.1, map_add, map_sub, map_smul, map_smul,
      ← hΦ.hasGap_column.casimirValue_sub_center, add_smul, sub_smul] at h_second
    exact sub_left_injective (add_right_cancel h_second)
  exact integratedRep_fix_of_isKHighest (ι := proj) (hΦ.swap.hasLargeGap le_rfl)
    hp.column_rep.unitary_rep (hp.isDerivedAction_integratedRep hΦ) hf highest' h_casimir' le_rfl
    h_repro

/-- If `Q` is highest of a weight `ν` with `ν - Λ` outside the cone of the positive roots, where `Λ`
is the lowest `K`-type of `l`, then `π(e_λ)` kills every derivative `Y Q` of `Q` along the rows. -/
theorem integratedRep_oscRows_eq_zero (hp : OscillatorPair T π π') [Nonempty R]
    (hΦ : IsJointHarmonic T l l' Φ) {ν : R → ℤ} {Q : MvPolynomial I ℂ}
    (hQ : l.IsKHighest T.oscRows ν Q) (hν : ν - l.lowestKType ∉ l.rootCone) (Y : Matrix R R ℂ) :
    integratedRep π l.dsKernel (polyVector η (T.oscRows Y Q)) = 0 := by
  -- `π(e_λ)` kills the orbit of `Q`, hence also its derivatives.
  have h_unitary (Z : unitaryLie (signMatrix ε)) :
      integratedRep π l.dsKernel (polyVector η (T.oscRows Z Q)) = 0 := by
    have h_deriv : HasDerivAt
        (fun t : ℝ ↦ integratedRep π l.dsKernel (π (expU (t • Z)) (polyVector η Q))) _ 0 :=
      (hp.derives Z Q).map_clm (integratedRep π l.dsKernel)
    simp [← h_deriv.deriv, integratedRep_eq_zero_of_notMem_rootCone (hΦ.hasLargeGap le_rfl)
      hp.unitary_rep hp.derives hQ hν]
  rw [eq_unitaryLiePart_add_I_smul ε Y]
  simp [h_unitary]

/-- Let `π`, `π'` be an oscillator pair for `T`: commuting representations of `U(ε)` and `U(ε')` on
one Fock space, acting on the rows and columns. Let `R`, `C` be nonempty. Let `Φ` be a joint
harmonic: `l`, `l'` match, and `Φ ≠ 0` is `K`-highest of the lowest `K`-type weights and termwise
harmonic for `T` and `T.swap`. Then for every polynomial `P` there is a smooth compactly supported
`α` on the second group (an element of `Bumps ε'`) with `π(e_λ) P = π'(α') π(e_λ) Φ`, where
`α' g = α g⁻¹` and `e_λ` is the discrete series kernel. The inversion is the convention of
`DiscreteSeries.smear`; `α'` is again smooth with compact support.

This smoothing statement is used in place of Howe's duality theorem for real unitary pairs (R. Howe,
Transcending classical invariant theory). It is proved by Howe's argument
(`New.IsJointHarmonic.howe_argument`) instead of through irreducibility. -/
theorem exists_bump_integratedRep_eq (hp : OscillatorPair T π π') [Nonempty R] [Nonempty C]
    (hΦ : IsJointHarmonic T l l' Φ) (P : MvPolynomial I ℂ) : ∃ α : Bumps ε',
    integratedRep π l.dsKernel (polyVector η P) = integratedRep π'
      (fun g : USign ε' ↦ α.val.val g⁻¹) (integratedRep π l.dsKernel Φ) := by
  -- Let `proj = π(e_λ) ∘ polyVector`, and let `smearΦ α` be `π'(g ↦ α g⁻¹)` applied to `proj Φ`.
  -- The polynomials that `proj` sends into the range of `smearΦ` satisfy the conditions of Howe's
  -- argument `IsJointHarmonic.howe_argument`, so every polynomial is among them.
  have hrep : IsUnitaryRep (Fintype.card I) π' fockInner := hp.column_rep.unitary_rep
  let proj : MvPolynomial I ℂ →ₗ[ℂ] fockSpace η :=
    (integratedRep π l.dsKernel).toLinearMap ∘ₗ polyVector η
  -- Integration by parts: `π(e_λ) = A ψ` for the generator `ψ = (-l).dsGenerator`, and
  -- `A f (Y v) = -A (Y f) v`. The generator is highest of weight `(-l).lowestKType` for `-l`.
  obtain ⟨A, hA, hA_parts⟩ :
      ∃ A : (-l).DsModule →ₗ[ℂ] fockSpace η →L[ℂ] fockSpace η,
        integratedRep π l.dsKernel = A (-l).dsGenerator ∧
        ∀ (Y : Matrix R R ℂ) (f : (-l).DsModule) (v : MvPolynomial I ℂ),
          A f (polyVector η (T.oscRows Y v)) = -A ((-l).dsAction Y f) (polyVector η v) :=
    exists_integration_by_parts (hΦ.hasLargeGap le_rfl) hp.unitary_rep hp.derives
  obtain ⟨hweight, hkill⟩ :
      (-l).IsKHighest (-l).dsAction (-l).lowestKType (-l).dsGenerator :=
    isKHighest_dsGenerator hΦ.hasGap_row.neg
  let smearΦ : Bumps ε' →ₗ[ℂ] fockSpace η :=
    .proj 1 ∘ₗ smear (fun g : USign ε' ↦ π' g (proj Φ)) (hrep.continuous (proj Φ))
  have h_smear (α : Bumps ε') :
      integratedRep π' (fun g ↦ α.val.val g⁻¹) (proj Φ) = smearΦ α := by
    simpa [smearΦ] using map_integratedRep hrep (integrable_bump_inv_smul _ α) (.id ℂ _) (proj Φ)
  suffices h_top : smearΦ.range.comap proj = ⊤ by
    obtain ⟨α, hα⟩ := h_top.ge (x := P) trivial
    exact ⟨α, hα.symm.trans (h_smear α).symm⟩
  refine hΦ.howe_argument _ ?_ ?_ ?_ ?_ ?_
  · -- Stable under the columns: if `proj y = smearΦ β`, differentiate `π'(exp tZ) (proj y)` at
    -- `t = 0` in two ways; the derivative moves onto `β` (`hasDerivAt_smear`). A general `Y` is
    -- `Z₁ + i Z₂` by `eq_unitaryLiePart_add_I_smul`.
    rintro Y y ⟨β, hβ⟩
    have hZ (Z : unitaryLie (signMatrix ε')) :
        proj (T.swap.oscRows Z y) = smearΦ (bumpDeriv (Z : Matrix C C ℂ) β) := by
      have h_orbit (g : USign ε') : π' g (proj y) =
          smear (fun x : USign ε' ↦ π' x (proj Φ)) (hrep.continuous (proj Φ)) β g := by
        simp [← hβ, ← h_smear β, map_integratedRep hrep (integrable_bump_inv_smul ..) (π' g)]
      have h_right : HasDerivAt (fun t : ℝ ↦ π' (expU (t • Z)) (proj y))
          (smearΦ (bumpDeriv Z.val β)) 0 := by
        simpa [smearΦ, h_orbit] using
          hasDerivAt_smear _ β (hrep.continuous (proj Φ)) (hasDerivAt_expU Z 1 0)
      exact (hp.isDerivedAction_integratedRep hΦ Z y).unique h_right
    refine ⟨bumpDeriv Y β, ?_⟩
    rw [eq_unitaryLiePart_add_I_smul ε' Y]
    simp [map_add, hZ]
  · -- Contains `Φ`: a bump function that reproduces `e_{λ'}` fixes `proj Φ`.
    obtain ⟨α, hα⟩ : ∃ α : Bumps ε', ∀ g : USign ε',
        ∫ x : USign ε', α.val.val x⁻¹ * l'.dsKernel (x⁻¹ * g) = l'.dsKernel g :=
      (hΦ.swap.hasLargeGap le_rfl).exists_bump_conv_dsKernel
    have h_fix : integratedRep π' (fun g : USign ε' ↦ α.val.val g⁻¹) (proj Φ) = proj Φ :=
      hp.integratedRep_integratedRep_eq_self hΦ (integrable_bump_inv_smul _ α) hα
    exact ⟨α, (h_smear α).symm.trans h_fix⟩
  · -- If `Q` is highest of a weight outside `Λ + cone`, then `π(e_λ)` kills its derivatives.
    intro ν Q hQ hν Y
    have h_zero : proj (T.oscRows Y Q) = 0 := hp.integratedRep_oscRows_eq_zero hΦ hQ hν Y
    exact ⟨0, by simp [h_zero]⟩
  · -- By parts, the compact lowering operators of `l` move onto `ψ`, which they kill.
    intro a b hab hl P
    have h_zero : proj (T.oscRows.E b a P) = 0 := by
      simp [proj, hA, hA_parts, hkill b a hab.symm (by simpa using hl)]
    exact ⟨0, by simp [h_zero]⟩
  · -- By parts, `E a a` moves onto `ψ`, which has weight `-Λ`.
    intro a P
    have h_gap : l.HasGap _ := hΦ.hasGap_row
    have h_zero : proj (T.oscRows.E a a P - (l.lowestKType a : ℂ) • P) = 0 := by
      simp [proj, hA, hA_parts, hweight]
    exact ⟨0, by simp [h_zero]⟩

end New.OscillatorPair
