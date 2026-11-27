module

import Mathlib.Algebra.Order.Star.Int
public import New.Reduction.Data.LevelAndTwists
import Mathlib.Data.Rat.Cast.OfScientific
public import Lib.Adelic.Reduction.DefiniteClassSums
public import Lib.Weil.CompactLift.ThetaKernelDefs
public import New.UpperBound.Objects.LabelsAndIndexTypes
public import Lib.General.LinearAlgebra.TensorChains
public import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.Shimura.HeckeTower.HeckeData
import New.Reduction.Data.Sizes
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import Lib.GLn.Branching.IntegralMap
public import New.UpperBound.Seesaw.AdmissibleCombinations
public import New.UpperBound.Objects.LiftLawsModuloN
public import Lib.SiegelWeil.SingularForms.CentreCoefficients
public import Lib.Weil.DualPair.FiniteAction
import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.GLn.SchurModule.SchurNorm
import Lib.General.Algebra.LevelModulus
import Lib.PadicComparison.Descent.TestCategory

section
/-!
# Harish-Chandra parameters, weights and lift diagrams of the definite spaces

A weight is given by its last entry and by the number of columns of each height of its Young diagram
at each infinite place of `E`. This file fixes the weights on the spaces `X_j` and `Y_m`. It defines
the Harish-Chandra parameters of the `X_j` and of `Y_m` in decreasing order, the highest weights
`μ(X_j)` and `μ(Y_m)`, and the diagrams of the lifts between the `X_j`. It computes the columns and
bounds the rows of these diagrams, and it shows that `μ(X_m)` and `μ(Y_m)` interlace. It also
computes `n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|`, where `|·|` is the sum of the entries.

## Main definitions and results

* `New.Data.columnCount`, `New.Data.lastEntry`: the columns and the last entry of the weight on
  `X_j`.
* `New.Data.keptColumns`, `New.Data.columnsY`: the columns of the weight on `Y_m`, obtained by
  branching.
* `New.Data.paramX`, `New.Data.weightX`, `New.Data.liftDiagram`: the doubled parameters and the
  weights of the `X_j`, and the diagrams of the lifts.
* `New.Data.weightX_eq`, `New.Data.weightY_eq`: the weights in terms of their columns.
* `New.Data.branchExponent_eq`: the formula for `n_τ`.

Notions from other files:
* `New.Data`: data `D` for parameters `P : New.Parameters`. They give a CM field `E`, the number
  `m = D.m` of lifts and a rank `r = D.r`. From these come `k = D.k = r + 1 - m`, `t = D.t = 5 r`,
  the ranks `n_j = D.n j = k + j (t + 1)` and the gap `Δ = D.gap = 2 * D.halfGap = 2 r ^ 8`.
* `X_j`, `Y_m`: the standard definite hermitian spaces over `E` of ranks `n_j` and `n_m - 1`. Lift
  `j + 1` is the theta lift from forms on `U(X_j)` to forms on `U(X_{j+1})`. Branching is the
  restriction of representations from `U(X_m)` to `U(Y_m)`. This file has only their weights.
* `New.Data.Φ`: the set of infinite places of `E`.
* `New.Data.a`, `New.Data.aPlaces`: the integer `a = x b`, for the scales `x` and `b` of the data,
  and the set of `a`-places, the places `≡ 1` modulo `P.q₀`.
* `New.Data.liftWeight`: the weight `κ_j(σ) = κ(σ) + (j + 1/2) Δ` at `σ`, with `κ = D.weight`. It is
  not to be confused with the column count `New.Data.columnCount`.
* `New.Data.targetParameter`: the sequence `λ^Y = (k/2 - 1, …, 1 - k/2; -κ_{1/2}, -κ_{3/2}, …)` at a
  place, where `κ_{i - 1/2} = κ_i - Δ / 2`.
-/

@[expose] public section

noncomputable section

/-! ## The column diagrams of the weights -/

namespace New.Data

variable {P : Parameters} (D : Data P)

/-- The number of columns of height `h` at the place `τ` of the weight on the definite space `X_j`
of rank `n_j = k + j (t + 1)`, for `h < n_j` (see `weightX_eq`); here `k = D.k` and `t = D.t`. For
`h = 1` it is `D.a` at the places in `D.aPlaces` and `0` elsewhere; for `h = k ≠ 1` it is
`κ_1(τ) − ⌊(k + t + 1) / 2⌋`, with `κ_1(τ) = D.liftWeight 1 τ`; for `h > k` with `h ≡ k` mod `t + 1`
it is the gap `D.gap` minus `t + 1`; else it is `0`. Subtraction is that of natural numbers. -/
def columnCount (τ : D.Φ) (h : ℕ) : ℕ :=
  if h = 1 then
    (if τ ∈ D.aPlaces then D.a else 0)
  else if h = D.k then
    D.liftWeight 1 τ - (D.k + D.t + 1) / 2
  else if D.k < h ∧ D.t + 1 ∣ h - D.k then D.gap - (D.t + 1) else 0

/-- Bound on the number of columns of height `h` at `τ`, with the count at height one replaced by
`a`: `D.columnCount τ h` (or `a` if `h = 1`) is at most `a` (if `h = 1`) plus `D.liftWeight 1 τ` (if
`h = D.k`) plus the gap `D.gap`. -/
lemma columnCount_le (τ : D.Φ) (h a : ℕ) :
    (if h = 1 then a else D.columnCount τ h) ≤
      (if h = 1 then a else 0) + (if h = D.k then D.liftWeight 1 τ else 0) + D.gap := by
  grind [columnCount]

/-- The last entry of the weight on `X_j` at the place `τ` (see `weightX_eq`): it is `0` for
`j = 0`, else `⌊n_{j−1} / 2⌋ − κ_j(τ)`, with `n_j = D.n j` the rank `k + j (t + 1)` and
`κ_j(τ) = D.liftWeight j τ`. -/
def lastEntry (j : ℕ) (τ : D.Φ) : ℤ := if j = 0 then 0 else (D.n (j - 1) / 2 - D.liftWeight j τ : ℤ)

/-- Let `m = D.m` be the number of lifts, and let `X_m`, `Y_m` be the definite spaces of ranks `n_m`
and `n_m - 1`. For `h < n_m` this is the number of columns of height `h` of the weight on `X_m` that
keep their height under branching to `Y_m` (see `weightY_eq`). It is `Δ / 2 − (t + 1) / 2`, with
`Δ / 2 = D.halfGap` half the gap, if `h ≥ k` and `h ≡ k` mod `t + 1`, and `0` otherwise. -/
def keptColumns (h : ℕ) : ℕ := if D.k ≤ h ∧ D.t + 1 ∣ h - D.k then D.reducedHalfGap else 0

/-- The number of columns of height `h` at `τ` of the weight on `Y_m`, for `h < n_m - 1` (see
`weightY_eq`): the kept columns of height `h`, and the columns of height `h + 1` of the weight on
`X_m` that are not kept. -/
def columnsY (τ : D.Φ) (h : ℕ) : ℕ :=
  D.keptColumns h + (D.columnCount τ (h + 1) - D.keptColumns (h + 1))

end New.Data

/-!
## Parameters, weights and lift diagrams of the definite spaces

Parameters are doubled, so that they are integers; weights are not doubled. Entries and rows are
numbered from `0`.
-/

section Diagrams

open Finset

namespace New

/-- Twice the entry `p` of the block `[n] = ((n - 1) / 2, (n - 3) / 2, …, (1 - n) / 2)`. -/
def twiceBlockEntry (n p : ℕ) : ℤ := n - 1 - 2 * p

/-- The entries of the block `[n]` have sum `0`. -/
lemma sum_twiceBlockEntry (n : ℕ) : ∑ p ∈ range n, twiceBlockEntry n p = 0 := by
  have h_gauss : (∑ p ∈ range n, (p : ℤ)) * 2 = n * (n - 1) := by
    induction n with
    | zero => simp
    | succ n ih => grind [sum_range_succ]
  simp only [twiceBlockEntry, sum_sub_distrib, sum_const, card_range, ← mul_sum, nsmul_eq_mul]
  linarith

namespace Data

variable {P : Parameters} (D : Data P)

lemma n_zero : D.n 0 = D.k := by simp [n]

lemma n_succ (j : ℕ) : D.n (j + 1) = D.n j + (D.t + 1) := by grind [n]

lemma k_le_n (j : ℕ) : D.k ≤ D.n j := by simp [n]

lemma n_pos (j : ℕ) : 0 < D.n j := D.k_pos.trans_le (D.k_le_n j)

/-- Each rank `n_j = k + j (t + 1)` is even, as `k` is even and `t` is odd. -/
lemma n_even (j : ℕ) : Even (D.n j) := D.k_even.add (D.t_odd.add_one.mul_left j)

lemma liftWeight_add (j : ℕ) (τ : D.Φ) (i : ℕ) :
    D.liftWeight (j + i) τ = D.liftWeight j τ + i * D.gap := by
  simp only [liftWeight_eq]
  ring

lemma liftWeight_succ (j : ℕ) (τ : D.Φ) : D.liftWeight (j + 1) τ = D.liftWeight j τ + D.gap := by
  rw [liftWeight_add, one_mul]

lemma halfGap_le_liftWeight (j : ℕ) (τ : D.Φ) :
    D.halfGap ≤ D.liftWeight j τ := by simp [liftWeight_eq]

/-! ### The parameters and weights of the spaces `X_j` -/

/-- The number `a_τ`: it is `a` at the places in `D.aPlaces` (the `a`-places) and `0` elsewhere. -/
def firstRowExcess (τ : D.Φ) : ℕ := if τ ∈ D.aPlaces then D.a else 0

/-- Twice the Harish-Chandra parameters of the `X_j` at the place `τ`, in decreasing order: first
`λ^X = [k] + (a_τ, 0, …, 0)`, then the blocks `-κ_i + [t + 1]` for `i = 1, 2, …`. The parameter of
`X_j` consists of the first `n_j` entries. That they decrease follows from `weightX_eq`. -/
def paramX (τ : D.Φ) (p : ℕ) : ℤ :=
  if p < D.k then
    twiceBlockEntry D.k p + if p = 0 then 2 * (D.firstRowExcess τ : ℤ) else 0
  else
    twiceBlockEntry (D.t + 1) ((p - D.k) % (D.t + 1)) -
      2 * D.liftWeight ((p - D.k) / (D.t + 1) + 1) τ

/-- The sequence `D.paramX τ` lists twice the Harish-Chandra parameters of the definite spaces `X_i`
at the place `τ`. For `b < t + 1`, with `t = D.t`, its entry at position `n_j + b` is twice entry
`b` of the block `-κ_{j+1} + [t + 1]`. Here `n_j = D.n j` is the rank of `X_j`,
`κ_{j+1} = D.liftWeight (j + 1) τ` and `[t + 1] = (t / 2, (t - 2) / 2, …, -t / 2)`. -/
lemma paramX_block (j : ℕ) (τ : D.Φ) {b : ℕ} (hb : b < D.t + 1) :
    D.paramX τ (D.n j + b) = twiceBlockEntry (D.t + 1) b - 2 * D.liftWeight (j + 1) τ := by
  have h_le : D.k ≤ D.n j + b := (D.k_le_n j).trans (Nat.le_add_right _ _)
  have h_index : D.n j + b - D.k = b + (D.t + 1) * j := by grind [n]
  have h_mod : (b + (D.t + 1) * j) % (D.t + 1) = b := by simp [Nat.mod_eq_of_lt hb]
  have h_div : (b + (D.t + 1) * j) / (D.t + 1) = j := by
    rw [Nat.add_mul_div_left _ _ D.t.succ_pos, Nat.div_eq_of_lt hb, zero_add]
  rw [paramX, ite_eq_right h_le.not_gt, h_index, h_mod, h_div]

/-- Entry `p` of the highest weight `μ(X_j)` at the place `τ`: the decreasing parameter less the
block `[n_j]`, where `n_j = D.n j` is the rank of `X_j`. Both `D.paramX τ` and `twiceBlockEntry` are
doubled, and the division by `2` is exact (`two_mul_weightX`). -/
def weightX (j : ℕ) (τ : D.Φ) (p : ℕ) : ℤ := (D.paramX τ p - twiceBlockEntry (D.n j) p) / 2

/-- The division by `2` in the definition of the weight `μ(X_j) = D.weightX j τ` is exact: twice the
weight is the doubled parameter `D.paramX τ` less the doubled block `[n_j]`. -/
lemma two_mul_weightX (j : ℕ) (τ : D.Φ) {p : ℕ} :
    2 * D.weightX j τ p = D.paramX τ p - twiceBlockEntry (D.n j) p := by
  obtain ⟨u, hu⟩ : Even (D.n j) := D.n_even j
  obtain ⟨v, hv⟩ : Even D.k := D.k_even
  obtain ⟨s, hs⟩ : Odd D.t := D.t_odd
  -- The ranks `k`, `t + 1` and `n_j` are even, so both terms on the right are odd.
  simp only [weightX, paramX, twiceBlockEntry]
  split_ifs <;> omega

/-- Row `p` at the place `τ` of the diagram `μ_{j+1}^+ = μ(X_j) + κ_{j+1} - n_{j+1} / 2` of lift
`j + 1`, the theta lift from forms on `U(X_j)` to forms on `U(X_{j+1})`. Here `μ(X_j)` is the weight
`D.weightX j τ`, `κ_{j+1} = D.liftWeight (j + 1) τ` and `n_j = D.n j` is the rank of `X_j`. The
diagram has `n_j` rows and is continued by `0`. -/
def liftDiagram (j : ℕ) (τ : D.Φ) (p : ℕ) : ℤ :=
  if p < D.n j then D.weightX j τ p + D.liftWeight (j + 1) τ - D.n (j + 1) / 2 else 0

/-- For each entry `p < n_{j+1}`, the weight `μ(X_{j+1})` is
`(μ_{j+1}^+, 0, …, 0) + n_j / 2 - κ_{j+1}`, where `μ_{j+1}^+` is `D.liftDiagram j τ`, `n_j` is the
rank `D.n j` and `κ_{j+1}` is `D.liftWeight (j + 1) τ`. -/
lemma weightX_succ (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n (j + 1)) :
    D.weightX (j + 1) τ p = D.liftDiagram j τ p + (D.n j / 2 - D.liftWeight (j + 1) τ) := by
  obtain ⟨s, hs⟩ : Odd D.t := D.t_odd
  have h_rank : D.n (j + 1) = D.n j + (D.t + 1) := D.n_succ j
  rcases lt_or_ge p (D.n j) with h_old | h_new
  · -- The first `n_j` entries of `[n_{j+1}]` are `[n_j] + (t + 1) / 2`.
    have h_shift : twiceBlockEntry (D.n (j + 1)) p = twiceBlockEntry (D.n j) p + (D.t + 1) := by
      grind [twiceBlockEntry]
    rw [liftDiagram, ite_eq_left h_old, weightX, weightX, h_shift]
    omega
  · -- The last `t + 1` entries of `[n_{j+1}]` are `[t + 1] - n_j / 2`.
    obtain ⟨b, rfl⟩ : ∃ b, p = D.n j + b := Nat.exists_eq_add_of_le h_new
    have h_shift :
        twiceBlockEntry (D.n (j + 1)) (D.n j + b) = twiceBlockEntry (D.t + 1) b - D.n j := by
      grind [twiceBlockEntry]
    rw [liftDiagram, ite_eq_right h_new.not_gt, weightX, h_shift, D.paramX_block j τ (by omega)]
    omega

/-- For `p < k` the rows of the first diagram are given by
`μ_1^+ = (a_τ, 0, …, 0) + κ_1 - n_1 / 2`, where `a_τ` is `D.firstRowExcess τ`, `κ_1` is
`D.liftWeight 1 τ` and `n_1` is the rank `D.n 1`. -/
lemma liftDiagram_zero (τ : D.Φ) {p : ℕ} (hp : p < D.k) :
    D.liftDiagram 0 τ p =
      (if p = 0 then (D.firstRowExcess τ : ℤ) else 0) + (D.liftWeight 1 τ - D.n 1 / 2) := by
  grind [liftDiagram, weightX, n_zero, paramX]

/-- The recursion `μ_{j+2}^+ = (μ_{j+1}^+, 0, …, 0) + Δ - t - 1` of the lift diagrams, in the rows
`p < n_{j+1}`: each further lift adds the gap `Δ = D.gap` less the step `t + 1` of the ranks. -/
lemma liftDiagram_succ (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n (j + 1)) :
    D.liftDiagram (j + 1) τ p = D.liftDiagram j τ p + (D.gap - (D.t + 1)) := by
  have h_ranks : D.n (j + 1 + 1) = D.n j + 2 * (D.t + 1) := by grind [n_succ]
  rw [liftDiagram, ite_eq_left hp, D.weightX_succ j τ hp, D.liftWeight_succ (j + 1), h_ranks]
  -- Halving `n_j + 2 (t + 1)` gives `n_j / 2 + (t + 1)`.
  omega

/-! ### The columns and rows of the diagrams -/

lemma columnCount_one (τ : D.Φ) : D.columnCount τ 1 = D.firstRowExcess τ := by
  simp [columnCount, firstRowExcess]

lemma one_lt_k : 1 < D.k := by grind [D.ten_thousand_le_m, D.hundred_mul_m_le_k]

/-- There are `κ_1 - n_1 / 2` columns of height `k`; this number is not negative. -/
lemma cast_columnCount_k (τ : D.Φ) : (D.columnCount τ D.k : ℤ) = D.liftWeight 1 τ - D.n 1 / 2 := by
  have h_le : D.k + D.t + 1 ≤ D.liftWeight 1 τ :=
    D.k_add_t_add_one_le_halfGap.trans (D.halfGap_le_liftWeight 1 τ)
  rw [columnCount, ite_eq_right D.one_lt_k.ne', ite_eq_left rfl, n_succ, n_zero]
  omega

/-- There are `Δ - t - 1` columns of height `n_{j+1}`; this number is not negative. -/
lemma cast_columnCount_n_succ (j : ℕ) (τ : D.Φ) :
    (D.columnCount τ (D.n (j + 1)) : ℤ) = D.gap - (D.t + 1) := by
  have h_le : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_lt : D.k < D.n (j + 1) := by grind [n_succ, D.k_le_n j]
  have h_dvd : D.t + 1 ∣ D.n (j + 1) - D.k := by simp [n]
  rw [columnCount, ite_eq_right (D.one_lt_k.trans h_lt).ne', ite_eq_right h_lt.ne',
    ite_eq_left ⟨h_lt, h_dvd⟩, Data.gap]
  omega

/-- No column has a height below `k` other than `1`. -/
lemma columnCount_eq_zero_of_lt_k (τ : D.Φ) {u : ℕ} (h_one : u ≠ 1) (hu : u < D.k) :
    D.columnCount τ u = 0 := by
  simp [columnCount, h_one, hu.ne, hu.not_gt]

/-- A height `u` strictly between `n_j` and `n_{j+1}` is none of the ranks `n_i`: the step
`t + 1` of the ranks does not divide `u - k`. -/
lemma not_dvd_sub_k (j : ℕ) {u : ℕ} (hu : u ∈ Ioo (D.n j) (D.n (j + 1))) : ¬D.t + 1 ∣ u - D.k := by
  rw [mem_Ioo, n, n, mul_comm j, mul_comm (j + 1)] at hu
  exact Nat.not_dvd_of_lt_of_lt_mul_succ (k := j) (by omega) (by omega)

/-- No column has a height strictly between the ranks `n_j` and `n_{j+1}`. -/
lemma columnCount_eq_zero_of_mem_Ioo (j : ℕ) (τ : D.Φ) {u : ℕ}
    (hu : u ∈ Ioo (D.n j) (D.n (j + 1))) :
    D.columnCount τ u = 0 := by
  have h_lt : D.k < u := (D.k_le_n j).trans_lt (mem_Ioo.1 hu).1
  simp [columnCount, (D.one_lt_k.trans h_lt).ne', h_lt.ne', D.not_dvd_sub_k j hu]

/-- The number of columns of height strictly between `p` and `k` is `a_τ = D.firstRowExcess τ` for
`p = 0` and `0` otherwise, as only the height `1` occurs below `k`. -/
lemma cast_sum_columnCount_Ioo_k (τ : D.Φ) {p : ℕ} :
    ((∑ u ∈ Ioo p D.k, D.columnCount τ u : ℕ) : ℤ) =
      if p = 0 then (D.firstRowExcess τ : ℤ) else 0 := by
  rw [sum_eq_ite 1 fun u hu h_one ↦ D.columnCount_eq_zero_of_lt_k τ h_one (mem_Ioo.1 hu).2]
  simp [columnCount_one, D.one_lt_k]

/-- For `p < n_j`, the columns of height strictly between `p` and `n_{j+1}` are those of height
strictly between `p` and `n_j` and those of height `n_j`. -/
lemma sum_columnCount_Ioo_succ (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n j) :
    ∑ u ∈ Ioo p (D.n (j + 1)), D.columnCount τ u =
      ∑ u ∈ Ioo p (D.n j), D.columnCount τ u + D.columnCount τ (D.n j) := by
  have h_subset : Ioc p (D.n j) ⊆ Ioo p (D.n (j + 1)) := Ioc_subset_Ioo_right (by simp [n_succ])
  have h_zero : ∀ u ∈ Ioo p (D.n (j + 1)), u ∉ Ioc p (D.n j) → D.columnCount τ u = 0 :=
    fun u hu hu_not_mem ↦ D.columnCount_eq_zero_of_mem_Ioo j τ (by grind)
  rw [sum_Ioo_add_eq_sum_Ioc hp, sum_subset h_subset h_zero]

/-- Let `μ_{j+1}^+ = D.liftDiagram j τ` be the Young diagram of lift `j + 1` at the place `τ`. It
has `D.columnCount τ u` columns of each height `u` below the rank `n_{j+1} = D.n (j + 1)`, and no
others: row `p`, numbered from `0`, has one box for each such column of height above `p`. The
numbers `D.columnCount τ u` are common to all lifts; only the range of heights depends on `j`. -/
lemma liftDiagram_eq_sum_columnCount (j : ℕ) (τ : D.Φ) (p : ℕ) :
    D.liftDiagram j τ p = (∑ u ∈ Ioo p (D.n (j + 1)), D.columnCount τ u : ℕ) := by
  -- The rows from `n_j` on are empty, and no column has a height strictly between `n_j` and
  -- `n_{j+1}`.
  have h_short (i : ℕ) (hp : D.n i ≤ p) :
      D.liftDiagram i τ p = (∑ u ∈ Ioo p (D.n (i + 1)), D.columnCount τ u : ℕ) := by
    rw [liftDiagram, ite_eq_right hp.not_gt, sum_eq_zero, Nat.cast_zero]
    exact fun u hu ↦ D.columnCount_eq_zero_of_mem_Ioo i τ (Ioo_subset_Ioo_left hp hu)
  induction j with
  | zero =>
    rcases le_or_gt (D.n 0) p with hp | hp
    · exact h_short 0 hp
    · rw [D.liftDiagram_zero τ (hp.trans_eq D.n_zero), D.sum_columnCount_Ioo_succ 0 τ hp, n_zero,
        Nat.cast_add, cast_sum_columnCount_Ioo_k, cast_columnCount_k]
  | succ j ih =>
    rcases le_or_gt (D.n (j + 1)) p with hp | hp
    · exact h_short (j + 1) hp
    · rw [D.liftDiagram_succ j τ hp, ih, D.sum_columnCount_Ioo_succ (j + 1) τ hp, Nat.cast_add,
        cast_columnCount_n_succ]

/-- Let `j < D.m`, where `D.m` is the number of lifts. Row `p` of the diagram
`μ_{j+1}^+ = D.liftDiagram j τ` of lift `j + 1` has a bound that depends on `p`. For `p = 0` the row
is at most `a_τ + κ_{j+1}`. For `0 < p < D.k` it is at most `κ_{j+1}`. Otherwise it is at most
`D.m * Δ`. -/
lemma liftDiagram_le {j : ℕ} (τ : D.Φ) (hj : j < D.m) (p : ℕ) :
    D.liftDiagram j τ p ≤
      if p = 0 then (D.firstRowExcess τ + D.liftWeight (j + 1) τ : ℤ)
      else if p < D.k then (D.liftWeight (j + 1) τ : ℤ) else D.m * D.gap := by
  -- There are at most `κ_1` columns of height `k`, and each further lift adds at most `Δ` columns.
  have h_count (i : ℕ) : D.liftDiagram i τ p ≤ (if p = 0 then (D.firstRowExcess τ : ℤ) else 0) +
      (if p < D.k then (D.liftWeight 1 τ : ℤ) else 0) + i * D.gap := by
    induction i with
    | zero =>
      rcases lt_or_ge p D.k with hp | hp
      · rw [D.liftDiagram_zero τ hp, ite_eq_left hp]
        omega
      · rw [liftDiagram, n_zero, ite_eq_right hp.not_gt]
        positivity
    | succ i ih =>
      rcases lt_or_ge p (D.n (i + 1)) with hp | hp
      · grind [D.liftDiagram_succ i τ hp]
      · rw [liftDiagram, ite_eq_right hp.not_gt]
        positivity
  have h_weight : D.liftWeight (j + 1) τ = D.liftWeight 1 τ + j * D.gap := by
    rw [add_comm j, liftWeight_add]
  have h_gap : (j * D.gap : ℤ) ≤ D.m * D.gap := by gcongr
  -- Compare the two bounds in the three ranges of rows.
  grind [h_count j, D.k_pos]

/-- The weight `μ(X_j)` at `τ` has `D.columnCount τ u` columns of each height `u < n_j`, and its
last entry is `D.lastEntry j τ`: for `p < n_j` the entry `p` is the last entry plus the number of
columns of height above `p`. -/
lemma weightX_eq (j : ℕ) (τ : D.Φ) {p : ℕ} (hp : p < D.n j) :
    D.weightX j τ p = D.lastEntry j τ + (∑ u ∈ Ioo p (D.n j), D.columnCount τ u : ℕ) := by
  cases j with
  | zero =>
    rw [n_zero] at hp ⊢
    have h_double : 2 * D.weightX 0 τ p = 2 * if p = 0 then (D.firstRowExcess τ : ℤ) else 0 := by
      simp [two_mul_weightX, paramX, n_zero, hp]
    rw [cast_sum_columnCount_Ioo_k, lastEntry, ite_eq_left rfl, zero_add]
    omega
  | succ j =>
    rw [D.weightX_succ j τ hp, liftDiagram_eq_sum_columnCount, add_comm, lastEntry,
      ite_eq_right j.succ_ne_zero, Nat.add_sub_cancel]

/-- The last entry of the weight `μ(X_j)` at `τ` is `n_{j+1} / 2 - κ_{j+1}` plus the number
`D.columnCount τ (D.n j)` of columns of full height `n_j` in the diagram `D.liftDiagram j τ` of lift
`j + 1`, which has `n_j` rows. Here `n_j = D.n j` is the (even) rank of `X_j` and
`κ_{j+1} = D.liftWeight (j + 1) τ` is the weight of the character of lift `j + 1`. -/
lemma lastEntry_eq (j : ℕ) (τ : D.Φ) :
    D.lastEntry j τ = D.n (j + 1) / 2 - D.liftWeight (j + 1) τ + D.columnCount τ (D.n j) := by
  have h_last : D.n j - 1 < D.n j := Nat.sub_one_lt (D.n_pos j).ne'
  have h_empty : Ioo (D.n j - 1) (D.n j) = ∅ := by
    grind
  -- The last row of the lift diagram has one box for each column of height `n_j`.
  have h_row : D.liftDiagram j τ (D.n j - 1) = D.columnCount τ (D.n j) := by
    simp [liftDiagram_eq_sum_columnCount, D.sum_columnCount_Ioo_succ j τ h_last, h_empty]
  have h_entry : D.weightX j τ (D.n j - 1) = D.lastEntry j τ := by
    simp [D.weightX_eq j τ h_last, h_empty]
  have h_diagram : D.liftDiagram j τ (D.n j - 1) =
      D.lastEntry j τ + D.liftWeight (j + 1) τ - D.n (j + 1) / 2 := by
    rw [liftDiagram, ite_eq_left h_last, h_entry]
  omega

/-! ### The parameter and the weight of `Y_m` -/

/-- The first `k - 1` entries of the sequence `λ^Y = D.targetParameter τ` form the block
`[k - 1] = (k / 2 - 1, …, 1 - k / 2)`, where `k = D.k` is the (even) rank of `X_0`; both sides are
doubled. -/
lemma two_mul_targetParameter_of_lt (τ : D.Φ) {p : ℕ} (hp : p + 1 < D.k) :
    2 * D.targetParameter τ p = twiceBlockEntry (D.k - 1) p := by
  obtain ⟨v, hv⟩ : Even D.k := D.k_even
  rw [targetParameter, ite_eq_left hp, twiceBlockEntry]
  omega

/-- Twice the Harish-Chandra parameter of `Y_m` at the place `τ`, in decreasing order: first
`[k - 1]`, then for `i = 1, 2, …` the entry `-κ_{i - 1/2}` followed by the block `-κ_i + [t]`. Here
`[n] = ((n - 1) / 2, …, (1 - n) / 2)` is the block of `twiceBlockEntry`, `κ_i = D.liftWeight i τ`
and `κ_{i - 1/2} = κ_i - D.halfGap`. The block `[k - 1]` and the `-κ_{i - 1/2}` are the entries of
`D.targetParameter τ`. The parameter consists of the first `n_m - 1` entries. -/
def sortedParamY (τ : D.Φ) (p : ℕ) : ℤ :=
  if p + 1 < D.k then
    2 * D.targetParameter τ p
  else if D.t + 1 ∣ p + 1 - D.k then
    2 * D.targetParameter τ (D.k - 1 + (p + 1 - D.k) / (D.t + 1))
  else
    twiceBlockEntry D.t ((p + 1 - D.k) % (D.t + 1) - 1) -
      2 * D.liftWeight ((p + 1 - D.k) / (D.t + 1) + 1) τ

/-- In `D.sortedParamY τ`, twice the Harish-Chandra parameter of `Y_m` (the definite space of rank
`n_m - 1`, `m = D.m`) at `τ` in decreasing order, entry `k - 1 + j` of `λ^Y = D.targetParameter τ`
stands at position `n_j - 1`. Here `n_j = D.n j = k + j (t + 1)` with `k = D.k` and `t = D.t`; both
sides are doubled. -/
lemma sortedParamY_n_sub_one (j : ℕ) (τ : D.Φ) :
    D.sortedParamY τ (D.n j - 1) = 2 * D.targetParameter τ (D.k - 1 + j) := by
  have hk : 0 < D.k := D.k_pos
  have h_index : D.n j - 1 + 1 - D.k = (D.t + 1) * j := by
    rw [n, mul_comm]
    omega
  have h_not_lt : ¬D.n j - 1 + 1 < D.k := by grind [D.k_le_n j]
  rw [sortedParamY, ite_eq_right h_not_lt, h_index, ite_eq_left (dvd_mul_right _ _),
    Nat.mul_div_cancel_left _ D.t.succ_pos]

/-- In `D.sortedParamY τ`, twice the Harish-Chandra parameter of `Y_m` at `τ` in decreasing order,
entry `b < t` of the block `-κ_{j+1} + [t]` stands at position `n_j + b`, with `t = D.t`; both sides
are doubled. -/
lemma sortedParamY_block (j : ℕ) (τ : D.Φ) {b : ℕ} (hb : b < D.t) :
    D.sortedParamY τ (D.n j + b) = twiceBlockEntry D.t b - 2 * D.liftWeight (j + 1) τ := by
  have h_index : D.n j + b + 1 - D.k = b + 1 + (D.t + 1) * j := by
    rw [n, mul_comm]
    omega
  have h_not_lt : ¬D.n j + b + 1 < D.k := by grind [D.k_le_n j]
  have h_lt : b + 1 < D.t + 1 := Nat.succ_lt_succ hb
  have h_mod : (b + 1 + (D.t + 1) * j) % (D.t + 1) = b + 1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_lt]
  have h_div : (b + 1 + (D.t + 1) * j) / (D.t + 1) = j := by
    rw [Nat.add_mul_div_left _ _ D.t.succ_pos, Nat.div_eq_of_lt h_lt, zero_add]
  simp [sortedParamY, h_not_lt, h_index, Nat.dvd_iff_mod_eq_zero, h_mod, h_div]

/-- Entry `p` of the highest weight `μ(Y_m)` at the place `τ`: the decreasing parameter less the
block `[n] = ((n - 1) / 2, …, (1 - n) / 2)` for the rank `n = n_m - 1` of `Y_m`. Both
`D.sortedParamY τ` and `twiceBlockEntry` are doubled, and the division by `2` is exact
(`two_mul_weightY`). -/
def weightY (τ : D.Φ) (p : ℕ) : ℤ := (D.sortedParamY τ p - twiceBlockEntry (D.n D.m - 1) p) / 2

/-- Let `λ`, `λ'` be the decreasing Harish-Chandra parameters of `X_m` and `Y_m` at the place `τ`,
so that `D.paramX τ` and `D.sortedParamY τ` are `2 λ` and `2 λ'`, with entries numbered from `0`.
Then `λ'_p - λ_{p+1} - 1 / 2` is the number `D.keptColumns (p + 1)` of columns of height `p + 1` of
the weight on `X_m` that keep their height under branching to `Y_m`; both sides are doubled. -/
lemma sortedParamY_sub_paramX (τ : D.Φ) (p : ℕ) :
    D.sortedParamY τ p - D.paramX τ (p + 1) - 1 = 2 * D.keptColumns (p + 1) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, D.t = 2 * s + 1 := D.t_odd
  have h_gap : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  rw [sortedParamY, paramX, keptColumns]
  by_cases h_head : p + 1 < D.k
  · -- `λ'_p` is an entry of `[k - 1]`.
    simp only [ite_eq_left h_head, D.two_mul_targetParameter_of_lt τ h_head, h_head.not_ge,
      false_and, twiceBlockEntry, p.succ_ne_zero, ite_false]
    omega
  by_cases h_dvd : D.t + 1 ∣ p + 1 - D.k
  · -- `λ'_p` is an entry `-κ_{i - 1/2}`.
    have h_kept : D.k ≤ p + 1 ∧ D.t + 1 ∣ p + 1 - D.k := ⟨not_lt.1 h_head, h_dvd⟩
    simp only [ite_eq_right h_head, ite_eq_left h_dvd, ite_eq_left h_kept,
      targetParameter_sub_one_add, Nat.mod_eq_zero_of_dvd h_dvd, twiceBlockEntry, reducedHalfGap]
    omega
  · -- `λ'_p` lies in a block `-κ_i + [t]`.
    simp only [ite_eq_right h_head, h_dvd, and_false, ite_false, twiceBlockEntry]
    omega

/-- The block `[n_m - 1]` is `[n_m]` without its first entry, raised by `1 / 2`; both sides are
doubled. Here `[n] = ((n - 1) / 2, …, (1 - n) / 2)` and `n_m = D.n D.m` is the rank of `X_m`. -/
lemma twiceBlockEntry_n_sub_one (p : ℕ) :
    twiceBlockEntry (D.n D.m - 1) p = twiceBlockEntry (D.n D.m) (p + 1) + 1 := by
  grind [twiceBlockEntry, D.n_pos D.m]

/-- The highest weights `μ = μ(X_m)` and `μ' = μ(Y_m)` at `τ` satisfy
`μ'_p = μ_{p+1} + D.keptColumns (p + 1)`, where the last term counts the columns of height `p + 1`
that keep their height under branching. -/
lemma weightY_eq_weightX_add (τ : D.Φ) (p : ℕ) :
    D.weightY τ p = D.weightX D.m τ (p + 1) + D.keptColumns (p + 1) := by
  have h_param : D.sortedParamY τ p - D.paramX τ (p + 1) - 1 = 2 * D.keptColumns (p + 1) :=
    D.sortedParamY_sub_paramX τ p
  rw [weightY, weightX, twiceBlockEntry_n_sub_one]
  omega

/-- The division by `2` in the definition of the weight `μ(Y_m) = D.weightY τ` is exact: twice the
weight is the doubled parameter `D.sortedParamY τ` less the doubled block `[n_m - 1]`. -/
lemma two_mul_weightY (τ : D.Φ) {p : ℕ} :
    2 * D.weightY τ p = D.sortedParamY τ p - twiceBlockEntry (D.n D.m - 1) p := by
  rw [weightY_eq_weightX_add, mul_add, two_mul_weightX, twiceBlockEntry_n_sub_one,
    ← D.sortedParamY_sub_paramX τ p]
  ring

/-- The columns of height `u` that keep their height under branching are at most as many as all
columns of height `u` at `τ`. With `μ = μ(X_m)`, `μ' = μ(Y_m)` and `u = p + 1 < n_m` this is
`μ'_p - μ_{p+1} ≤ μ_p - μ_{p+1}`. Together with `μ_{p+1} ≤ μ'_p` (`weightY_eq_weightX_add`) it says
that the weights interlace. -/
lemma keptColumns_le_columnCount (τ : D.Φ) (u : ℕ) : D.keptColumns u ≤ D.columnCount τ u := by
  have h_gap : D.k + D.t + 1 ≤ D.halfGap := D.k_add_t_add_one_le_halfGap
  have h_weight : D.liftWeight 1 τ = D.liftWeight 0 τ + 2 * D.halfGap := D.liftWeight_succ 0 τ
  grind [keptColumns, columnCount, reducedHalfGap, Data.gap, D.one_lt_k]

/-- No column of height `u < k` keeps its height under branching, where `k = D.k` is the rank of
`X_0`. -/
lemma keptColumns_eq_zero_of_lt_k {u : ℕ} (hu : u < D.k) : D.keptColumns u = 0 :=
  ite_eq_right fun h_block ↦ hu.not_ge h_block.1

/-- With `m = D.m` and `n_m = D.n D.m`, `D.keptColumns (n_m - 1) = 0`: no column of height `n_m - 1`
of the weight on `X_m` keeps its height under branching to `Y_m`. Hence the weights `μ(X_m)` and
`μ(Y_m)` have the same last entry. -/
lemma keptColumns_n_sub_one : D.keptColumns (D.n D.m - 1) = 0 := by
  obtain ⟨l, hl⟩ : ∃ l : ℕ, D.m = l + 1 :=
    Nat.exists_eq_add_one.2 (by linarith [D.ten_thousand_le_m])
  obtain ⟨s, hs⟩ : Odd D.t := D.t_odd
  have h_rank : D.n (l + 1) = D.n l + (D.t + 1) := D.n_succ l
  have h_between : D.n D.m - 1 ∈ Ioo (D.n l) (D.n (l + 1)) := by
    rw [hl, mem_Ioo]
    omega
  exact ite_eq_right fun h_block ↦ D.not_dvd_sub_k l h_between h_block.2

/-- For `u ≤ N`, the sum of `D.columnsY τ v` over heights `u ≤ v < N`, plus `D.keptColumns N`,
equals the sum of `D.columnCount τ v` over `u < v ≤ N`, plus `D.keptColumns u`. The `keptColumns`
terms telescope. -/
lemma sum_columnsY_add_keptColumns (τ : D.Φ) {u N : ℕ} (hN : u ≤ N) :
    ∑ v ∈ Ico u N, D.columnsY τ v + D.keptColumns N =
      ∑ v ∈ Ico (u + 1) (N + 1), D.columnCount τ v + D.keptColumns u := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Ico_succ_top hN, sum_Ico_succ_top (Nat.add_le_add_right hN 1), columnsY]
    grind [D.keptColumns_le_columnCount τ (N + 1)]

/-- The weight `μ(Y_m) = D.weightY τ` at `τ` has `D.columnsY τ u` columns of each height
`u < n_m - 1`, and its last entry is `D.lastEntry D.m τ`, the last entry of `μ(X_m)`: for
`p < n_m - 1` the entry `p` is the last entry plus the number of columns of height above `p`. -/
lemma weightY_eq (τ : D.Φ) {p : ℕ} (hp : p < D.n D.m - 1) :
    D.weightY τ p = D.lastEntry D.m τ + (∑ u ∈ Ioo p (D.n D.m - 1), D.columnsY τ u : ℕ) := by
  have h_telescope : ∑ u ∈ Ioo p (D.n D.m - 1), D.columnsY τ u =
      ∑ u ∈ Ioo (p + 1) (D.n D.m), D.columnCount τ u + D.keptColumns (p + 1) := by
    simpa only [keptColumns_n_sub_one, Nat.sub_add_cancel (D.n_pos D.m), Ico_add_one_left_eq_Ioo,
      add_zero] using D.sum_columnsY_add_keptColumns τ (u := p + 1) hp
  rw [weightY_eq_weightX_add, D.weightX_eq D.m τ (Nat.add_lt_of_lt_sub hp), h_telescope,
    Nat.cast_add, add_assoc]

/-- At most `Δ / 2 = D.halfGap` columns of each height keep their height under branching. -/
lemma keptColumns_le_halfGap (u : ℕ) : D.keptColumns u ≤ D.halfGap := by
  grind [keptColumns, reducedHalfGap]

/-- At most `Δ / 2 = D.halfGap` columns of each height `u > k` lose a box under branching. -/
lemma columnCount_sub_keptColumns_le_halfGap (τ : D.Φ) {u : ℕ} (hu : D.k < u) :
    D.columnCount τ u - D.keptColumns u ≤ D.halfGap := by
  grind [keptColumns, columnCount, reducedHalfGap, Data.gap, D.one_lt_k]

/-- The weight `μ(Y_m)` at `τ` has at most `Δ = D.gap` columns of each height `u ≥ k`. -/
lemma columnsY_le (τ : D.Φ) {u : ℕ} (hu : D.k ≤ u) : D.columnsY τ u ≤ D.gap := by
  rw [columnsY, Data.gap, two_mul]
  exact add_le_add (D.keptColumns_le_halfGap u)
    (D.columnCount_sub_keptColumns_le_halfGap τ (Nat.lt_succ_of_le hu))

/-! ### The exponent of the branching map -/

/-- The number `n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|`, where `|μ|` is the sum of the entries of `μ`. -/
def branchExponent (τ : D.Φ) : ℤ :=
  ∑ p ∈ range (D.n D.m), D.weightX D.m τ p - ∑ p ∈ range (D.n D.m - 1), D.weightY τ p

/-- The first `n_j = D.n j` entries of `D.paramX τ` are twice the Harish-Chandra parameter of `X_j`
at `τ`. Their sum is twice `a_τ - (t + 1) (κ_1 + ⋯ + κ_j)`. -/
lemma sum_paramX (j : ℕ) (τ : D.Φ) :
    ∑ p ∈ range (D.n j), D.paramX τ p =
      2 * D.firstRowExcess τ - 2 * (D.t + 1) * ∑ i ∈ range j, (D.liftWeight (i + 1) τ : ℤ) := by
  induction j with
  | zero =>
    have h_head (p : ℕ) (hp : p ∈ range D.k) : D.paramX τ p =
        twiceBlockEntry D.k p + if p = 0 then 2 * (D.firstRowExcess τ : ℤ) else 0 :=
      ite_eq_left (mem_range.1 hp)
    simp [n_zero, sum_congr rfl h_head, sum_add_distrib, sum_twiceBlockEntry, D.k_pos]
  | succ j ih =>
    have h_block : ∑ b ∈ range (D.t + 1), D.paramX τ (D.n j + b) =
        -2 * (D.t + 1) * D.liftWeight (j + 1) τ := by
      rw [sum_congr rfl fun b hb ↦ D.paramX_block j τ (mem_range.1 hb), sum_sub_distrib,
        sum_twiceBlockEntry, sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [n_succ, sum_range_add, ih, h_block, sum_range_succ]
    ring

/-- The first `n_m - 1` entries of `D.sortedParamY τ` are twice the Harish-Chandra parameter of the
definite space `Y_m` at the place `τ`, in decreasing order. For each `j`, the sum of the first
`n_j - 1` entries is twice `-(κ_{1/2} + ⋯ + κ_{j - 1/2}) - t (κ_1 + ⋯ + κ_j)`. The case `j = m` is
twice the sum of the entries of the parameter of `Y_m`. -/
lemma sum_sortedParamY (j : ℕ) (τ : D.Φ) :
    ∑ p ∈ range (D.n j - 1), D.sortedParamY τ p =
      -2 * ∑ i ∈ range j, (D.liftWeight (i + 1) τ - D.halfGap : ℤ) -
        2 * D.t * ∑ i ∈ range j, (D.liftWeight (i + 1) τ : ℤ) := by
  induction j with
  | zero =>
    have h_head (p : ℕ) (hp : p ∈ range (D.k - 1)) :
        D.sortedParamY τ p = twiceBlockEntry (D.k - 1) p := by
      have hp_lt : p + 1 < D.k := Nat.add_lt_of_lt_sub (mem_range.1 hp)
      rw [sortedParamY, ite_eq_left hp_lt, D.two_mul_targetParameter_of_lt τ hp_lt]
    simp [n_zero, sum_congr rfl h_head, sum_twiceBlockEntry]
  | succ j ih =>
    have h_rank : D.n (j + 1) - 1 = D.n j + D.t := by rw [n_succ, ← add_assoc, Nat.add_sub_cancel]
    have h_first : ∑ p ∈ range (D.n j), D.sortedParamY τ p =
        ∑ p ∈ range (D.n j - 1), D.sortedParamY τ p + D.sortedParamY τ (D.n j - 1) := by
      rw [← sum_range_succ, Nat.sub_add_cancel (D.n_pos j)]
    have h_block : ∑ b ∈ range D.t, D.sortedParamY τ (D.n j + b) =
        -2 * D.t * D.liftWeight (j + 1) τ := by
      rw [sum_congr rfl fun b hb ↦ D.sortedParamY_block j τ (mem_range.1 hb), sum_sub_distrib,
        sum_twiceBlockEntry, sum_const, card_range, nsmul_eq_mul]
      ring
    rw [h_rank, sum_range_add, h_first, ih, sortedParamY_n_sub_one, targetParameter_sub_one_add,
      h_block, sum_range_succ, sum_range_succ]
    ring

/-- The exponent `n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|`, where `|μ|` is the sum of the entries of the
weight `μ`, equals `a_τ - m Δ / 2`. -/
lemma branchExponent_eq (τ : D.Φ) : D.branchExponent τ = D.firstRowExcess τ - D.m * D.halfGap := by
  -- The blocks have sum `0`, so `n_τ` is the difference of the sums of the parameters.
  have h_params : 2 * D.branchExponent τ = ∑ p ∈ range (D.n D.m), D.paramX τ p -
      ∑ p ∈ range (D.n D.m - 1), D.sortedParamY τ p := by
    simp only [branchExponent, mul_sub, mul_sum, two_mul_weightX, two_mul_weightY, sum_sub_distrib,
      sum_twiceBlockEntry, sub_zero]
  rw [sum_paramX, sum_sortedParamY, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    at h_params
  linarith

/-- Let `|μ|` be the sum of the entries of a weight `μ`. The exponent
`n_τ = |μ(X_m)_τ| - |μ(Y_m)_τ|` is the number of columns of `μ(X_m)` that lose a box under branching
to `Y_m`, plus the last entry of `μ(X_m)`. Of the `D.columnCount τ u` columns of height
`u < n_m = D.n D.m`, all but `D.keptColumns u` lose a box. This is the form of the exponent in
`New.exists_branching_matrix`. -/
lemma branchExponent_eq_sum_columns (τ : D.Φ) :
    D.branchExponent τ =
      (∑ u ∈ Ioo 0 (D.n D.m), (D.columnCount τ u - D.keptColumns u) : ℕ) + D.lastEntry D.m τ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, D.n D.m = N + 1 := Nat.exists_eq_add_one.2 (D.n_pos D.m)
  -- Pair entry `p` of `μ(Y_m)` with entry `p + 1` of `μ(X_m)`; entry `0` of `μ(X_m)` is left over.
  have h_pair : D.branchExponent τ =
      D.weightX D.m τ 0 - ∑ p ∈ range N, (D.keptColumns (p + 1) : ℤ) := by
    simp [branchExponent, hN, sum_range_succ', weightY_eq_weightX_add, sum_add_distrib]
  have h_shift : ∑ p ∈ range N, (D.keptColumns (p + 1) : ℤ) =
      ∑ u ∈ Ioo 0 (D.n D.m), (D.keptColumns u : ℤ) := by
    rw [hN, ← Ico_add_one_left_eq_Ioo, ← sum_Ico_add', range_eq_Ico]
  push_cast [h_pair, h_shift, D.weightX_eq D.m τ (D.n_pos D.m), D.keptColumns_le_columnCount τ,
    sum_sub_distrib]
  ring

/-- The sum of the exponents `n_τ` over the `f` infinite places of `E` is `#Φ_a · a - f m Δ / 2`,
where `Φ_a = D.aPlaces` is the set of `a`-places and `Δ / 2 = D.halfGap`. -/
lemma sum_branchExponent :
    (∑ τ : D.Φ, D.branchExponent τ : ℝ) = #D.aPlaces * D.a - D.f * (D.m * D.halfGap) := by
  simp [branchExponent_eq, firstRowExcess, sum_sub_distrib, Finset.univ_inter]

end Data

end New

end Diagrams

end
end
end

section
/-!
# Chains of theta lifts, jointly invariant combinations, and free levels

This file treats chains of theta lifts and their jointly invariant combinations for a general
tower of finite adelic unitary groups joined by theta kernels. It shows that, in bounded rank, the
levels that reduce to `1` at the chosen places are free, that is, that they have trivial
stabilisers `New.classAut`. The chosen places of `E = D.E` are the prime divisors of
`New.Data.piM`; `D.f` is the number of infinite places of `E`. For every integral level in bounded
rank, the orders of the stabilisers divide `New.Data.chosenGroupOrder`.

## Main definitions and results

* `New.chain`: the composite of the first `j` lifts. It is equivariant (`New.chain_equivariant`),
  and its values are linear in the pure tensor of the data
  (`New.exists_linearMap_chain_eq_apply_pure`).
* `New.IsJointlyInvariant.sum_chain_mem_nsmul`: at free levels, a jointly invariant combination of
  chains is a sum with one term for each tuple of double cosets, with no denominators.
* `New.Data.principalLevel_le_chosenLevel`, `New.Data.classAut_eq_bot_of_le_chosenLevel`: in bounded
  rank, levels that reduce to `1` at the chosen places are free.
* `New.Data.card_classAut_dvd_chosenGroupOrder`: in rank at most `2 * D.n D.m` and for every
  integral level the stabilisers have order dividing `chosenGroupOrder`.

Notions from other files:
* `New.TensorChain`: The complex tensor product S_{j−1} ⊗ ⋯ ⊗ S_0, equal to ℂ for j = 0.
* `New.classAut`: `classAut Γ K g` is Γ ∩ gKg⁻¹, the stabiliser in Γ of the coset gK; here
  Γ = `stdRatPoints` is the rational unitary group of the standard definite space `New.stdSpace`,
  inside the finite adelic group.
* `New.Data.n`: The rank 𝗇_j = k + j(t + 1) of X_j.
-/

@[expose] public section

noncomputable section

/-!
## Chains of theta lifts and jointly invariant combinations

A tower of finite adelic unitary groups `Gf E (n j)` is joined by theta kernels `k j`
(`New.Kernel`). Each kernel lifts forms on `Gf E (n j)` to forms on `Gf E (n (j + 1))`
(`New.Kernel.lift`). The forms of stage `j` take values in the Weyl module
`WeylIndex (n j) κ → ℂ` of weight `(κ, e j)`. The kernel `k j` has a space of data `S j`, an action
`ω` of the pair of groups on `S j`, and a map `jetMap` that sends a datum to a linear map from the
Weyl module of stage `j` to that of stage `j + 1`.

For a set `A`, `n • A` is the set of sums of `n` elements of `A`.
-/

namespace New

open Finset Pointwise TensorProduct TensorChain Kernel

variable {E : Type} {M : Type*} [Field E] [CMType E] [AddCommGroup M] [Module ℚ M]
  [Module ℂ M] {n S : ℕ → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  [∀ j, AddCommGroup (S j)] [∀ j, Module ℂ (S j)] {κ : NumberField.InfinitePlace E → ℕ → ℕ}
  {e : ℕ → NumberField.InfinitePlace E → ℤ} {K : (j : ℕ) → Subgroup (Gf E (n j))}
  (k : ∀ j : ℕ, Kernel (n j) (n (j + 1)) κ (e j) (e (j + 1)) (K j) (S j)) [∀ j, IsLevel (K j)]

/-- The chain of j theta lifts with data Φ_0, …, Φ_{j−1}. It is the composite linear map from
algebraic forms of stage 0 to algebraic forms of stage j. The forms `AlgForm (n j) κ (e j)` of
stage j are the smooth functions on `Gf E (n j)` that transform under the rational points by the
weight with `κ τ h` columns of height `h` and the power `e j τ` of the determinant at `τ`. -/
def chain (Φ : (j : ℕ) → S j) : ∀ j : ℕ, AlgForm (n 0) κ (e 0) →ₗ[ℂ] AlgForm (n j) κ (e j) :=
  compUpTo fun j ↦ (k j).lift (Φ j)

/-- Equivariance of the chain of lifts. For each `j`, `k j` is a theta kernel with data `S j` from
algebraic forms on `Gf E (n j)` of weight `(κ, e j)` to forms on `Gf E (n (j + 1))` of weight
`(κ, e (j + 1))`. Its lift `(k j).lift` sends a datum and a form to the lifted form. Its action
`(k j).ω` is an action of `Gf E (n j) × Gf E (n (j + 1))` on `S j`. The chain `lift` applies the
first `m` lifts in turn to a form `φ`, using the factors of a tensor `t` of data. Let `a j` lie in
`Gf E (n j)` for every `j`, and move each factor `j` of `t` by `(k j).ω (a j, a (j + 1))`. The chain
with the moved data, applied to the right translate of `φ` by `a 0`, is the right translate by `a m`
of the chain with the data `t` applied to `φ`. -/
theorem TensorChain.lift_kernelLift_map_omega (a : ∀ j : ℕ, Gf E (n j))
    (φ : AlgForm (n 0) κ (e 0)) (m : ℕ) (t : TensorChain S m) :
    lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (a 0) φ) m
        (map (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) m t) =
      algFormRep κ (e m) (a m) (lift (fun i : ℕ ↦ (k i).lift) φ m t) := by
  induction m with
  | zero =>
    -- A tensor of length `0` is a scalar `c`, and both sides are `c` times the translate of `φ`.
    change ((show ℂ from t) * 1) • algFormRep κ (e 0) (a 0) φ =
      algFormRep κ (e 0) (a 0) ((show ℂ from t) • φ)
    rw [mul_one, map_smul]
  | succ m ih =>
    -- Both sides are linear in `t`; on `s ⊗ r` use the equivariance of the last lift.
    have h_tmul (s : S m) (r : TensorChain S m) :
        (k m).lift ((k m).ω (a m, a (m + 1)) s)
            (lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (a 0) φ) m
              (map (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) m r)) =
          algFormRep κ (e (m + 1)) (a (m + 1))
            ((k m).lift s (lift (fun i : ℕ ↦ (k i).lift) φ m r)) := by
      rw [ih r, lift_equivariant]
    have h_maps : lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (a 0) φ) (m + 1) ∘ₗ
          map (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) (m + 1) =
        algFormRep κ (e (m + 1)) (a (m + 1)) ∘ₗ lift (fun i : ℕ ↦ (k i).lift) φ (m + 1) :=
      TensorProduct.ext' (M := S m) (N := TensorChain S m) h_tmul
    exact LinearMap.congr_fun h_maps t

/-- Moving an element to the source of a chain of lifts. Let `z i` lie in the group of stage `i`,
with `ω(z i, z (i + 1)) = 1` for every lift, let `t` be any tensor of the data of the first `m`
lifts, and let `j < m`. If `ω(1, z (j + 1))`, acting alone on the factor of the lift from stage
`j` to stage `j + 1`, fixes `t`, then the chain with data `t` has the same value at `φ` and at
the right translate of `φ` by `z 0`. -/
theorem TensorChain.lift_algFormRep_of_map_eq {z : ∀ i : ℕ, Gf E (n i)}
    (hz : ∀ i : ℕ, (k i).ω (z i, z (i + 1)) = 1) {m j : ℕ} (hj : j < m) {t : TensorChain S m}
    (h_fix : map (fun i : ℕ ↦ if i = j then (k i).ω (1, z (i + 1)) else 1) m t = t)
    (φ : AlgForm (n 0) κ (e 0)) :
    lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (z 0) φ) m t =
      lift (fun i : ℕ ↦ (k i).lift) φ m t := by
  -- As every `ω(z i, z (i + 1))` is trivial, `ω(1, z (j + 1))` on factor `j` is the action of the
  -- tuple `a` that is `(z i)⁻¹` up to stage `j` and `1` after it.
  set a : ∀ i : ℕ, Gf E (n i) := fun i ↦ if i ≤ j then (z i)⁻¹ else 1 with ha
  have h_absorb (i : ℕ) (g : Gf E (n i)) (g' : Gf E (n (i + 1))) :
      (k i).ω (g, g') = (k i).ω (g * z i, g' * z (i + 1)) := by
    rw [← Prod.mk_mul_mk, map_mul, hz i, mul_one]
  have h_factors : (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) =
      fun i : ℕ ↦ if i = j then (k i).ω (1, z (i + 1)) else 1 := by
    funext i
    rcases lt_trichotomy i j with h_lt | rfl | h_gt
    · simpa [ha, h_lt.le, h_lt.ne, Nat.succ_le_of_lt h_lt, Prod.mk_one_one] using
        h_absorb i (a i) (a (i + 1))
    · simpa [ha] using h_absorb i (z i)⁻¹ 1
    · simp [ha, h_gt.not_ge, h_gt.ne', (Nat.lt_succ_of_lt h_gt).not_ge, Prod.mk_one_one]
  have h_equivariant := lift_kernelLift_map_omega k a (algFormRep κ (e 0) (z 0) φ) m t
  rw [h_factors, h_fix] at h_equivariant
  simpa [ha, hj.not_ge] using h_equivariant.symm

/-- Let `φ` be fixed by the level `K 0`, and let each `a j` lie in `K j`. Acting on each datum `Φ i`
by `(a i, a (i + 1))` and applying the chain to `φ` gives the right translate by `a j` of the chain
applied to `φ`. -/
lemma chain_equivariant {φ : AlgForm (n 0) κ (e 0)}
    (hφ : φ ∈ levelSpace (algFormRep κ (e 0)) (K 0)) (a : ∀ j : ℕ, K j)
    (Φ : (j : ℕ) → S j) (j : ℕ) :
    chain k (fun i : ℕ ↦ (k i).ω (a i, (a (i + 1)).val) (Φ i)) j φ =
      algFormRep κ (e j) (a j).val (chain k Φ j φ) := by
  have h_fix : algFormRep κ (e 0) (a 0).val φ = φ := by simpa using hφ (a 0)
  simpa [chain, h_fix] using lift_kernelLift_map_omega k (fun i : ℕ ↦ (a i).val) φ j (pure Φ j)

/-- The chain of p pairs of theta lifts, the i-th pair with datum Φ_i in S_{2i} ⊗ S_{2i+1}: a
linear map from forms of stage 0 to forms of stage 2p. -/
def doubleLiftChain (Φ : (j : ℕ) → S (2 * j) ⊗[ℂ] S (2 * j + 1)) :
    ∀ p : ℕ, AlgForm (n (2 * 0)) κ (e (2 * 0)) →ₗ[ℂ] AlgForm (n (2 * p)) κ (e (2 * p)) :=
  compUpTo fun i ↦ liftInPairs (fun j ↦ (k j).lift) i (Φ i)

/-- For a_j in `Gf E (n j)`, the operator ω(a_{2i}, a_{2i+1}) ⊗ ω(a_{2i+1}, a_{2i+2}) on the space
S_{2i} ⊗ S_{2i+1}. -/
def twoKernelAction (a : ∀ j : ℕ, Gf E (n j)) (i : ℕ) :
    S (2 * i) ⊗[ℂ] S (2 * i + 1) →ₗ[ℂ] S (2 * i) ⊗[ℂ] S (2 * i + 1) :=
  map ((k (2 * i)).ω (a (2 * i), a (2 * i + 1)))
    ((k (2 * i + 1)).ω (a (2 * i + 1), a (2 * i + 1 + 1)))

/-- Fix `φ` and `g`. The value at `g` of the chain applied to `φ` is a linear function
`β : TensorChain S j →ₗ[ℂ] (WeylIndex (n j) κ → ℂ)` of the pure tensor `Φ (j - 1) ⊗ ⋯ ⊗ Φ 0` of the
data. -/
lemma exists_linearMap_chain_eq_apply_pure (j : ℕ) (φ : AlgForm (n 0) κ (e 0)) (g : Gf E (n j)) :
    ∃ β : TensorChain S j →ₗ[ℂ] WeylIndex (n j) κ → ℂ, ∀ Φ : (j : ℕ) → S j,
      (chain k Φ j φ).val g = β (TensorChain.pure Φ j) :=
  -- `β` is the linear map `TensorChain.lift` of the lifts at `φ`, followed by evaluation at `g`
  ⟨.proj g ∘ₗ Submodule.subtype _ ∘ₗ lift (fun i : ℕ ↦ (k i).lift) φ j, by simp [chain]⟩

/-- Joint invariance: the tensor ∑_{x∈s} L_x ⊗ Φ_{x,m−1} ⊗ ⋯ ⊗ Φ_{x,0} is unchanged by the joint
action of every tuple a with a_j ∈ K_j and a_j = 1 for j ≥ m, as tested against all linear maps β
from S_{m−1} ⊗ ⋯ ⊗ S_0 to the Weyl module `WeylIndex (n m) κ → ℂ` of stage m. Here a acts on Φ_{x,j}
by ω(a_j, a_{j+1}), and the coefficients L_x are linear maps from that Weyl module to `M`. -/
def IsJointlyInvariant {X : Type*} (m : ℕ) (s : Finset X) (L : X → (WeylIndex (n m) κ → ℂ) →ₗ[ℂ] M)
    (Φ : X → ∀ j : ℕ, S j) : Prop :=
  ∀ a : ∀ j : ℕ, K j, (∀ j ≥ m, a j = 1) → ∀ β : TensorChain S m →ₗ[ℂ] WeylIndex (n m) κ → ℂ,
    ∑ x ∈ s, L x (β (TensorChain.pure (fun j : ℕ ↦ (k j).ω (a j, a (j + 1)) (Φ x j)) m)) =
      ∑ x ∈ s, L x (β (TensorChain.pure (Φ x) m))

/-- Representatives of the classes `c j` for `j < m`, followed by the points `g j` for `m ≤ j`. -/
def classPoints {m : ℕ} (c : ∀ j : Fin m, StdClasses (K j)) (g : ∀ j : ℕ, Gf E (n j)) (j : ℕ) :
    Gf E (n j) :=
  if h : j < m then (c ⟨j, h⟩).out else g j

omit [∀ j, IsLevel (K j)] in
lemma classPoints_of_le {m j : ℕ} (c : ∀ j : Fin m, StdClasses (K j)) (g : ∀ j : ℕ, Gf E (n j))
    (h_le : m ≤ j) : classPoints c g j = g j := dite_eq_right h_le.not_gt

/-- The product of the first `m` kernels, applied to the value of `φ` at `g 0`. Factor `j` is the
linear map `jetMap` between the Weyl modules of stages `j` and `j + 1` that belongs to the datum
`Φ j` moved by the action `ω` of the pair of points `(g j, g (j + 1))`. -/
def kernelProduct (Φ : (j : ℕ) → S j) (φ : AlgForm (n 0) κ (e 0)) (g : ∀ j : ℕ, Gf E (n j))
    (m : ℕ) : WeylIndex (n m) κ → ℂ :=
  compUpTo (fun j ↦ (k j).jetMap ((k j).ω (g j, g (j + 1)) (Φ j))) m (φ.val (g 0))

omit [Module ℚ M] [Module ℂ M] in
/-- A sum over tuples of `m + 1` double cosets, sorted by the last one. For a tuple `c` of classes
`c j` in `StdClasses (K j)`, the family `classPoints c g` lists their chosen representatives and
continues with the points `g j`. The sum of `F` over the tuples of length `m + 1` is the sum, over
the last class `r`, of the sums over the tuples of length `m`, where the point `g m` is replaced by
the representative `r.out`. -/
lemma sum_classPoints_succ (m : ℕ) (F : (∀ j : ℕ, Gf E (n j)) → M) (g : ∀ j : ℕ, Gf E (n j)) :
    ∑ c : ∀ j : Fin (m + 1), StdClasses (K j), F (classPoints c g) =
      ∑ r : StdClasses (K m), ∑ c : ∀ j : Fin m, StdClasses (K j),
        F (classPoints c (Function.update g m r.out)) := by
  rw [← Fintype.sum_prod_type']
  -- a tuple of `m + 1` classes is a last class with a tuple of `m` classes
  refine Fintype.sum_equiv (Fin.snocEquiv fun j : Fin (m + 1) ↦ StdClasses (K j)).symm _ _
    fun c ↦ congrArg F (funext fun j ↦ ?_)
  obtain h_lt | rfl | h_gt := lt_trichotomy j m
  · simp [classPoints, h_lt, h_lt.trans m.lt_succ_self, Fin.init]
  · simp [classPoints, Fin.last]
  · simp [classPoints, h_gt.not_gt, Nat.not_lt.2 h_gt, h_gt.ne']

/-- **A chain of lifts is a plain sum.** Let `k j` be theta kernels from stage `j` to stage `j + 1`,
and let `φ : AlgForm (n 0) κ (e 0)` be an algebraic form of stage `0` fixed by the level `K 0`. Let
`∑ x ∈ s, L x ⊗ Φ x` be jointly invariant: it is unchanged when elements `a j ∈ K j`, `j < m`, move
each datum `Φ x j` by `ω(a j, a (j + 1))`, with `a m = 1`. Let the levels `K j`, `j < m`, have
trivial stabilisers `classAut`. Then ∑_x L_x(value at `g m` of the chain with data `Φ x` applied to
`φ`) is the sum, over tuples `c` of double cosets `StdClasses (K j)`, `j < m`, of ∑_x
L_x(`kernelProduct`). -/
theorem IsJointlyInvariant.sum_chain_eq_sum_kernelProduct
    {X : Type*} {m : ℕ} {s : Finset X}
    {L : X → (WeylIndex (n m) κ → ℂ) →ₗ[ℂ] M} {Φ : X → ∀ j : ℕ, S j}
    (h_inv : IsJointlyInvariant k m s L Φ)
    (h_free : ∀ j < m, ∀ g : Gf E (n j), classAut stdRatPoints (K j) g = ⊥)
    {φ : AlgForm (n 0) κ (e 0)} (hφ : φ ∈ levelSpace (algFormRep κ (e 0)) (K 0))
    (g : ∀ j : ℕ, Gf E (n j)) :
    ∑ x ∈ s, L x ((chain k (Φ x) m φ).val (g m)) =
      ∑ c : ∀ j : Fin m, StdClasses (K j), ∑ x ∈ s,
        L x (kernelProduct k (Φ x) φ (classPoints c g) m) := by
  -- The integral over all points is taken one variable at a time, by induction on the length of
  -- the chain. The last lift is an integral whose integrand is constant on classes, and each class
  -- has volume `1`; each value of the integrand is a shorter chain.
  induction m generalizing g with
  | zero => simp [kernelProduct, classPoints, chain, compUpTo]
  | succ j ih =>
    -- `T a β` applies `β` to the first `j` factors, then the kernel at `(a, g (j + 1))` with the
    -- last one.
    let T (a : Gf E (n j)) (β : TensorChain S j →ₗ[ℂ] WeylIndex (n j) κ → ℂ) :
        TensorChain S (j + 1) →ₗ[ℂ] WeylIndex (n (j + 1)) κ → ℂ :=
      lift ((k j).jetMap.compl₁₂ ((k j).ω (a, g (j + 1))) β)
    have hT (a : Gf E (n j)) (β : TensorChain S j →ₗ[ℂ] WeylIndex (n j) κ → ℂ)
        (f : ∀ i : ℕ, S i) :
        T a β (pure f (j + 1)) = (k j).jetMap ((k j).ω (a, g (j + 1)) (f j)) (β (pure f j)) :=
      lift.tmul _ (pure f j)
    -- `F` is the integrand of the last lift, summed over `x`.
    let integrand (x : X) (a : Gf E (n j)) : WeylIndex (n (j + 1)) κ → ℂ :=
      (k j).jetMap ((k j).ω (a, g (j + 1)) (Φ x j)) ((chain k (Φ x) j φ).val a)
    let F (a : Gf E (n j)) : M := ∑ x ∈ s, L x (integrand x a)
    have h_integral : classIntegral stdRatPoints (K j) F =
        ∑ x ∈ s, L x ((chain k (Φ x) (j + 1) φ).val (g (j + 1))) :=
      classIntegral_sum (f := integrand) s (fun x : X ↦ (L x).toAddMonoidHom) (fun _ ↦ 1)
        (fun x ↦ (k j).integrand_mem_smoothInvariants ..) (by simp [F])
    -- The integrand is right `K j`-invariant: joint invariance for `b` in the slot `j` alone.
    have h_const : K j ≤ rightStabilizer F := fun b hb a ↦ by
      -- `β` is the linear map that gives the value at `a` of the chain of length `j`.
      obtain ⟨β, hβ⟩ := exists_linearMap_chain_eq_apply_pure k j φ a
      have h_eq := h_inv (Pi.mulSingle j ⟨b, hb⟩) (by simp +contextual [ne_of_gt]) (T a β)
      simp only [hT, ← hβ, chain_equivariant k hφ] at h_eq
      simpa [integrand, omega_omega] using h_eq
    have h_classes : classIntegral stdRatPoints (K j) F = ∑ r : StdClasses (K j), F r.out := by
      rw [classIntegral_eq_classSum h_const, classSum, finsum_eq_sum_of_fintype]
      exact sum_congr rfl fun r _ ↦ by simp [h_free j]
    rw [← h_integral, h_classes,
      sum_classPoints_succ j fun p ↦ ∑ x ∈ s, L x (kernelProduct k (Φ x) φ p (j + 1))]
    refine sum_congr rfl fun r _ ↦ ?_
    -- The value at `r` is a chain of length `j`, with the kernel absorbed in the coefficients.
    let L' (x : X) : (WeylIndex (n j) κ → ℂ) →ₗ[ℂ] M :=
      L x ∘ₗ (k j).jetMap ((k j).ω (r.out, g (j + 1)) (Φ x j))
    have h_inv' : IsJointlyInvariant k j s L' Φ := fun a ha β ↦ by
      simpa [L', hT, ha, Prod.mk_one_one] using h_inv a (fun i hi ↦ ha i (by omega)) (T r.out β)
    simpa [F, integrand, L', kernelProduct, classPoints, compUpTo] using
      ih h_inv' (fun i hi ↦ h_free i (by omega)) (Function.update g j r.out)

omit [∀ j, IsLevel (K j)] in
/-- Let `P j g v` be a property of a point `g` of the group of stage `j` and a vector `v` of the
Weyl module of stage `j`. If `P` holds for the values of the form `φ`, and each of the first `m`
kernels `k j` with datum `Φ j` takes vectors with `P` at stage `j` to vectors with `P` at stage
`j + 1`, then `P` holds for the product `kernelProduct` of these kernels at any tuple of points. -/
lemma kernelProduct_induction (P : ∀ j : ℕ, Gf E (n j) → (WeylIndex (n j) κ → ℂ) → Prop)
    {Φ : ∀ j : ℕ, S j} {m : ℕ}
    (h_step : ∀ j < m, ∀ (g : Gf E (n j)) (g' : Gf E (n (j + 1))) (v : WeylIndex (n j) κ → ℂ),
      P j g v → P (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ j)) v))
    {φ : AlgForm (n 0) κ (e 0)} (h_base : ∀ g : Gf E (n 0), P 0 g (φ.val g))
    (g : ∀ j : ℕ, Gf E (n j)) :
    P m (g m) (kernelProduct k Φ φ g m) := by
  induction m with
  | zero => exact h_base (g 0)
  | succ j ih => exact h_step j j.lt_succ_self _ _ _ (ih fun i hi ↦ h_step i (by omega))

omit [∀ j, IsLevel (K j)] in
/-- Let `size j g v` be a size of a vector `v` of the Weyl module of stage `j` at a point `g`, and
let `r j ≥ 0` for every `j`. If the kernel `k j` with datum `Φ j` multiplies the size by at most
`r j` for `j < m`, and the values of the form `φ` have size at most `B`, then the product
`kernelProduct` of the first `m` kernels has size at most `(∏ j < m, r j) * B`. -/
lemma apply_kernelProduct_le_prod_mul (size : ∀ j : ℕ, Gf E (n j) → (WeylIndex (n j) κ → ℂ) → ℝ)
    {r : ℕ → ℝ} (hr : ∀ j : ℕ, 0 ≤ r j) {Φ : ∀ j : ℕ, S j} {m : ℕ}
    (h_step : ∀ j < m, ∀ (g : Gf E (n j)) (g' : Gf E (n (j + 1))) (v : WeylIndex (n j) κ → ℂ),
      size (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ j)) v) ≤ r j * size j g v)
    {φ : AlgForm (n 0) κ (e 0)} {B : ℝ} (h_base : ∀ g : Gf E (n 0), size 0 g (φ.val g) ≤ B)
    (g : ∀ j : ℕ, Gf E (n j)) :
    size m (g m) (kernelProduct k Φ φ g m) ≤ (∏ j ∈ range m, r j) * B := by
  refine kernelProduct_induction k (fun j g v ↦ size j g v ≤ (∏ i ∈ range j, r i) * B)
    (fun j hj g g' v hv ↦ ?_) (by simpa using h_base) g
  calc size (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ j)) v)
      ≤ r j * size j g v := h_step j hj g g' v
    _ ≤ r j * ((∏ i ∈ range j, r i) * B) := mul_le_mul_of_nonneg_left hv (hr j)
    _ = (∏ i ∈ range (j + 1), r i) * B := by rw [prod_range_succ_comm, mul_assoc]

/-- Let `φ : AlgForm (n 0) κ (e 0)` be an algebraic form of stage `0` fixed by the level `K 0`. Let
`∑ x ∈ s, L x ⊗ Φ x` be jointly invariant for the theta kernels `k j`: it is unchanged when
`a j ∈ K j`, `j < m`, move each datum `Φ x j` by `ω(a j, a (j + 1))`, with `a m = 1`. Let the levels
`K j`, `j < m`, have trivial stabilisers `classAut`. Let the property `P` hold for the values of
`φ`, and let each kernel preserve `P`. Let `p` be a point of the group of stage `m`, and let
`∑ x ∈ s, L x (v x)` lie in `A` whenever the vectors `v x` have `P` at `p` and are the images of the
pure tensors of the data `Φ x` under one linear map. Then the value at `p` of the combination of the
chains applied to `φ` is a sum of elements of `A`, one for each tuple of double cosets in
`StdClasses (K j)`, `j < m`. -/
lemma IsJointlyInvariant.sum_chain_mem_nsmul {X : Type*} {m : ℕ} {s : Finset X}
    {L : X → (WeylIndex (n m) κ → ℂ) →ₗ[ℂ] M} {Φ : X → ∀ j : ℕ, S j}
    (h_inv : IsJointlyInvariant k m s L Φ)
    (h_free : ∀ j < m, ∀ g : Gf E (n j), classAut stdRatPoints (K j) g = ⊥)
    {φ : AlgForm (n 0) κ (e 0)} (hφ : φ ∈ levelSpace (algFormRep κ (e 0)) (K 0))
    (P : ∀ j : ℕ, Gf E (n j) → (WeylIndex (n j) κ → ℂ) → Prop)
    (h_step : ∀ x ∈ s, ∀ j < m, ∀ (g : Gf E (n j)) (g' : Gf E (n (j + 1)))
      (v : WeylIndex (n j) κ → ℂ),
      P j g v → P (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ x j)) v))
    (h_base : ∀ g : Gf E (n 0), P 0 g (φ.val g)) {p : Gf E (n m)} {A : Set M}
    (hA : ∀ β : TensorChain S m →ₗ[ℂ] WeylIndex (n m) κ → ℂ,
      let v (x : X) : WeylIndex (n m) κ → ℂ := β (pure (Φ x) m)
      (∀ x ∈ s, P m p (v x)) → ∑ x ∈ s, L x (v x) ∈ A) :
    ∑ x ∈ s, L x ((chain k (Φ x) m φ).val p) ∈
      (∏ j ∈ range m, Nat.card (StdClasses (K j))) • A := by
  obtain ⟨g, rfl⟩ : ∃ g : ∀ j : ℕ, Gf E (n j), g m = p := ⟨Pi.mulSingle m p, by simp⟩
  have h_term (c : ∀ j : Fin m, StdClasses (K j)) :
      ∑ x ∈ s, L x (kernelProduct k (Φ x) φ (classPoints c g) m) ∈ A := by
    let q : ∀ j : ℕ, Gf E (n j) := classPoints c g
    -- The product of the kernels is linear in the tensor of the data.
    let β : TensorChain S m →ₗ[ℂ] WeylIndex (n m) κ → ℂ :=
      lift (fun j : ℕ ↦ (k j).jetMap ∘ₗ (k j).ω (q j, q (j + 1))) (φ.val (q 0)) m
    have hβ (x : X) : β (pure (Φ x) m) = kernelProduct k (Φ x) φ q m := by simp [β, kernelProduct]
    simpa only [hβ] using hA β fun x hx ↦ by
      simpa [hβ, q, classPoints_of_le] using kernelProduct_induction k P (h_step x hx) h_base q
  rw [h_inv.sum_chain_eq_sum_kernelProduct k h_free hφ g]
  simpa [prod_range] using Set.finsetSum_mem_finsetSum univ _ _ fun c _ ↦ h_term c

end New

/-!
## Chosen places, the chosen group order and free levels

These are facts on the places of `E` that the data single out: the places above the level prime
`D.N`, and the chosen places, with `D.ChosenPlace i` the chosen places above the prime
p_i = `D.levelPrime i`. The map `D.chosenPlace` sends a pair `(i, w)` to the place `w`.

* `New.Data.chosenGroupOrder`: the order of the product of the groups `GL (r t)` over the residue
  fields at the chosen places.
* `New.Data.card_pi_GL_chosenPlace`, `New.Data.log_chosenGroupOrder_le`: the order of such a product
  in terms of the primes p_i, and the bound `log chosenGroupOrder ≤ D.x ^ 32`.
-/

namespace New.Data

open Parameters Real Finset Subgroup Fintype Function Embedding

variable {P : Parameters} {D : Data P} (i : Fin 2) {w : FinPlace D.E} {n : Type} [Fintype n]
  [DecidableEq n]

/-! ### Places above the level and chosen places -/

/-- The infinite places `D.Φ` of E are in bijection with the chosen places above the prime
p_i = `D.levelPrime i`. -/
lemma nonempty_infinitePlace_equiv_chosenPlace (i : Fin 2) : Nonempty (D.Φ ≃ D.ChosenPlace i) := by
  obtain ⟨c, h_norm, h_coprime⟩ := D.exists_piM_mul_star_eq_levelPrime_mul_coprime (i := i)
  exact nonempty_infinitePlace_equiv_finPlace (levelPrime_modEq_one D i) h_norm h_coprime

/-- A chosen bijection from the infinite places of E to the chosen places above p_i. -/
def chosenEquiv : D.Φ ≃ D.ChosenPlace i := (nonempty_infinitePlace_equiv_chosenPlace i).some

lemma card_chosenPlace : Fintype.card (D.ChosenPlace i) = D.f :=
  (card_congr (D.chosenEquiv i)).symm

/-- The level prime N is a uniformiser at each finite place w of E above it: its valuation in the
completion at w is exp(−1). -/
lemma v_N_eq_exp_neg_one (hN_mem : ↑D.N ∈ w.asIdeal) :
    Valued.v (D.N : LocField w) = WithZero.exp (-1) := by
  simpa [← v_algebraMap_eq_intValuation] using
    intValuation_natCast_eq_exp_neg_one hN_mem (not_dvd_q₁_mul_d_of_modEq_one D.N_modEq_one)

/-- The equation π π̄ = N for π = `D.piN`, with the cofactor `1` written out, as the lemmas on
primes `≡ 1` modulo `P.q₁ D.towerExp * P.d` take it. -/
lemma piN_mul_star_eq_N_mul_one : D.piN * star D.piN = D.N * (1 : ℕ) := by simp [D.piN_mul_star]

/-- The factor π = `D.piN` of the level N = π π̄ is a uniformiser at each finite place `w` that
divides it: if `D.piN ∈ w`, then `w.intValuation D.piN = exp (-1)`. -/
lemma intValuation_piN (hπ_mem : D.piN ∈ w.asIdeal) : w.intValuation D.piN = WithZero.exp (-1) := by
  -- `π * star π = N`, so `w` lies above `N`, and the cofactor of `N` is `1`.
  refine intValuation_eq_of_mul_star D.N_modEq_one ?_ D.piN_mul_star_eq_N_mul_one
    D.N.coprime_one_right hπ_mem
  simpa [D.piN_mul_star] using w.asIdeal.mul_mem_right (star D.piN) hπ_mem

/-- The integer `D.piM`, whose prime divisors are the chosen places, is a uniformiser at each place
that divides it. -/
lemma intValuation_piM (hπ_mem : D.piM ∈ w.asIdeal) :
    w.intValuation D.piM = WithZero.exp (-1) := by
  -- `w` lies above one of the two primes `p = D.levelPrime k`, and `D.piM * star D.piM` is `p`
  -- times a number prime to `p`.
  obtain ⟨k, -, hp_mem⟩ := (D.isChosen_iff (w := w)).1 hπ_mem
  obtain ⟨c, h_norm, h_coprime⟩ :
      ∃ c : ℕ, D.piM * star D.piM = D.levelPrime k * c ∧ (D.levelPrime k).Coprime c :=
    D.exists_piM_mul_star_eq_levelPrime_mul_coprime
  exact intValuation_eq_of_mul_star (levelPrime_modEq_one D k) hp_mem h_norm h_coprime hπ_mem

/-- The product, over the chosen places above `D.levelPrime 0` and `D.levelPrime 1`, of the orders
of the groups `GL (r t)` over the residue fields, for the rank r = `D.r` and t = `D.t` = 5 r. It is
a common multiple of the orders of the stabilisers in
`New.Data.card_classAut_dvd_chosenGroupOrder`. -/
def chosenGroupOrder : ℕ :=
  Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL (Fin (D.r * D.t)) (ResField (D.chosenPlace x)))
  deriving NeZero

/-- The norms `w.q` of the chosen places `w` above p₀ and p₁ have product M^f, where
M = `D.M` = p₀ p₁ and f = `D.f` is the number of infinite places of E. -/
lemma prod_q_chosenPlace : ∏ x : (i : Fin 2) × D.ChosenPlace i,
  (D.chosenPlace x).q = D.M ^ D.f := by
  -- There are `f` chosen places above p_i, each of norm p_i.
  have h_norm (i : Fin 2) (w : D.ChosenPlace i) : w.val.q = D.levelPrime i :=
    D.q_eq_levelPrime w.property.right
  simp [chosenPlace, Fintype.prod_sigma, h_norm, card_chosenPlace, Data.M, mul_pow]

/-- At a chosen place `w` above the prime p_i = `D.levelPrime i`, the group GL_l over the residue
field at `w` has the same order as GL_l over the field with p_i elements. -/
lemma card_GL_resField_eq_card_GL_zmod (w : D.ChosenPlace i) (l : ℕ) :
    Nat.card (GL (Fin l) (ResField w.val)) = Nat.card (GL (Fin l) (ZMod (D.levelPrime i))) := by
  -- The residue field has p_i elements, and p_i is prime, so it is isomorphic to
  -- `ZMod (D.levelPrime i)`.
  let : Fintype (ResField w.val) := Fintype.ofFinite _
  have h_card : Fintype.card (ResField w.val) = D.levelPrime i := by
    rw [Fintype.card_eq_nat_card, card_ResField, D.q_eq_levelPrime w.property.right]
  let e : ZMod (D.levelPrime i) ≃+* ResField w.val :=
    ZMod.ringEquivOfPrime _ (D.levelPrime_prime i) h_card
  exact Nat.card_congr (Units.mapEquiv e.symm.mapMatrix.toMulEquiv).toEquiv

variable (D) in
/-- The product of the groups GL_l(𝔽_w) over the chosen places w above p₀ and p₁ has order
∏_i |GL_l(𝔽_{p_i})|^f, where p_i = `D.levelPrime i` and f is the number of infinite places of E:
there are f chosen places above each p_i. -/
lemma card_pi_GL_chosenPlace (l : ℕ) :
    Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL (Fin l) (ResField (D.chosenPlace x))) =
      ∏ i : Fin 2, Nat.card (GL (Fin l) (ZMod (D.levelPrime i))) ^ D.f :=
  calc Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL (Fin l) (ResField (D.chosenPlace x)))
      = ∏ i : Fin 2, ∏ w : D.ChosenPlace i, Nat.card (GL (Fin l) (ResField w.val)) :=
        Nat.card_pi.trans (Fintype.prod_sigma _)
    _ = ∏ i : Fin 2, Nat.card (GL (Fin l) (ZMod (D.levelPrime i))) ^ D.f := by
        simp only [card_GL_resField_eq_card_GL_zmod, prod_const, card_univ, card_chosenPlace]

/-! ### The principal level and the orders of stabilisers -/

/-- The elements of the finite adelic unitary group on the index set `n` that are integral and
reduce to `1` at every chosen place, that is, at every prime divisor of `D.piM`. -/
abbrev chosenLevel : Subgroup (Gf D.E n) := levelOf (n := n) D.chosenPlace ⊥

variable {K : Subgroup (Gf D.E n)}

/-- Of a place `w` above the prime `D.levelPrime i` and its conjugate, exactly one is chosen. -/
lemma isChosen_star_iff {i : Fin 2} {w : FinPlace D.E} (hw : ↑(D.levelPrime i) ∈ w.asIdeal) :
    D.IsChosen (star w) ↔ ¬D.IsChosen w := by
  obtain ⟨c, h_norm, h_coprime⟩ := D.exists_piM_mul_star_eq_levelPrime_mul_coprime (i := i)
  exact star_mem_iff_notMem (levelPrime_modEq_one D i) hw h_norm h_coprime

/-- For a finite index type `n` with at most `D.r * D.t` elements, the order of the product of the
groups `GL n (ResField w)`, over the chosen places w above `D.levelPrime 0` and `D.levelPrime 1`,
divides `D.chosenGroupOrder`. -/
lemma card_GL_dvd_chosenGroupOrder (hn : Fintype.card n ≤ D.r * D.t) :
    Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL n (ResField (D.chosenPlace x))) ∣
      D.chosenGroupOrder := by
  -- `g ↦ diag (g, 1)` embeds `GL n` in `GL (Fin (r * t))` at every chosen place.
  obtain ⟨u⟩ : Nonempty (n ↪ Fin (D.r * D.t)) := nonempty_of_card_le (by simpa)
  exact card_dvd_of_injective (.piMap fun _ ↦ extendGL u) (.piMap fun _ ↦ extendGL_injective u)

/-- The chosen places, indexed by the pairs (i, w) with w a chosen place above p_i, are pairwise
distinct, and none is the conjugate of one of them. -/
instance isConjApart_chosenPlace : IsConjApart D.chosenPlace where
  injective := by
    -- The norm of a chosen place above p_i is p_i, so the place determines `i`.
    rintro ⟨i, w, hw, hw_mem⟩ ⟨i', w', hw', hw'_mem⟩ (rfl : w = w')
    obtain rfl : i = i' :=
      D.levelPrime_injective ((D.q_eq_levelPrime hw_mem).symm.trans (D.q_eq_levelPrime hw'_mem))
    rfl
  star_ne := by
    -- The conjugate of a chosen place is not chosen.
    rintro ⟨i, w, hw, hw_mem⟩ ⟨i', w', hw', hw'_mem⟩ (rfl : star w = w')
    exact (D.isChosen_star_iff hw_mem).1 hw' hw

/-- The places `D.chosenPlace x`, for x = (i, w) with w a chosen place above p_i, are exactly the
chosen places. -/
lemma range_chosenPlace : Set.range D.chosenPlace = {w : FinPlace D.E | D.IsChosen w} := by
  ext w
  change w ∈ Set.range D.chosenPlace ↔ D.IsChosen w
  rw [Set.mem_range, isChosen_iff]
  refine ⟨?_, fun ⟨i, hw⟩ ↦ ⟨⟨i, w, hw⟩, rfl⟩⟩
  rintro ⟨⟨i, w, hw⟩, rfl⟩
  exact ⟨i, hw⟩

/-- If `D.piM`, whose prime divisors are the chosen places, divides the integer `a` of E, the
principal congruence subgroup of level `a` is contained in `New.Data.chosenLevel`. -/
lemma principalLevel_le_chosenLevel {a : NumberField.RingOfIntegers D.E} (ha : D.piM ∣ a) :
    principalLevel n a ≤ D.chosenLevel :=
  principalLevel_le_levelOf fun ⟨_, w, hw, _⟩ ↦ Ideal.mem_of_dvd w.asIdeal ha hw

/-- Let K be a subgroup of the integral points of the finite adelic unitary group on `n` whose
elements reduce to `1` at the chosen places above the prime `D.levelPrime i`. If `n` has at most
`4 * D.n D.m` elements, four times the rank of the last stage, the stabiliser of each coset gK in
the rational unitary group is trivial. -/
theorem classAut_eq_bot_of_le_levelOf_chosenPlace (i : Fin 2)
    (hK : K ≤ levelOf (n := n) (fun w : D.ChosenPlace i ↦ w.val) ⊥)
    (hn : Fintype.card n ≤ 4 * D.n D.m) (g : Gf D.E n) : classAut stdRatPoints K g = ⊥ := by
  -- `Variety.classAut_eq_bot` asks that the norms of the places multiply to more than
  -- `(2 * card n) ^ [E : ℚ]`. The `f` places have norm p_i, and `[E : ℚ] = 2 * f`.
  have h_size : (2 * (4 * D.n D.m)) ^ 2 < D.levelPrime i := D.nat_lt_of_hasLogBound
  refine Variety.classAut_eq_bot Subtype.val_injective ?_ hK g
  calc (2 * Fintype.card n) ^ Module.finrank ℚ D.E
      ≤ ((2 * (4 * D.n D.m)) ^ 2) ^ D.f := by
        rw [finrank_eq_two_mul_card_infinitePlace, pow_mul]
        gcongr
    _ < D.levelPrime i ^ D.f := by gcongr
    _ = ∏ w : D.ChosenPlace i, w.val.q := by
        simp [fun w : D.ChosenPlace i ↦ D.q_eq_levelPrime w.property.right, D.card_chosenPlace]

/-- If n has at most `2 * D.n D.m` elements, every subgroup K of `New.Data.chosenLevel` is
sufficiently small: the stabiliser of each point gK in the rational unitary group is trivial. -/
lemma classAut_eq_bot_of_le_chosenLevel (hK : K ≤ D.chosenLevel)
    (hn : Fintype.card n ≤ 2 * D.n D.m) : ∀ g : Gf D.E n, classAut stdRatPoints K g = ⊥ := by
  have h_le : D.chosenLevel ≤ levelOf (n := n) (fun w : D.ChosenPlace 0 ↦ w.val) ⊥ := by
    intro k hk
    obtain ⟨hk_int, hk_red⟩ := mem_levelOf.1 hk
    exact mem_levelOf.2 ⟨hk_int, mem_bot.2 (funext fun w ↦ congrFun (mem_bot.1 hk_red) ⟨0, w⟩)⟩
  exact D.classAut_eq_bot_of_le_levelOf_chosenPlace 0 (hK.trans h_le) (by lia)

/-- For the standard definite hermitian space on an index set `n` with at most `2 * D.n D.m`
elements, a subgroup K of the stabiliser of the standard lattice and any finite adelic g, the
stabiliser of gK in the rational unitary group has order dividing `New.Data.chosenGroupOrder`.

A consequence of a unitary variant of Minkowski's lemma on integral matrices of finite order. -/
lemma card_classAut_dvd_chosenGroupOrder (hn : Fintype.card n ≤ 2 * D.n D.m)
    (hK : K ≤ stdLevel D.E n) (g : Gf D.E n) :
    Nat.card (classAut stdRatPoints K g) ∣ D.chosenGroupOrder := by
  -- Conjugate by `g⁻¹` into `K ≤ stdLevel`, then reduce at the chosen places.
  let conj : Gf D.E n →* Gf D.E n := (MulAut.conj g⁻¹).toMonoidHom
  have h_le : classAut stdRatPoints K g ≤ (stdLevel D.E n).comap conj :=
    inf_le_right.trans (comap_mono hK)
  let red : classAut stdRatPoints K g →*
      ∀ x : (i : Fin 2) × D.ChosenPlace i, GL n (ResField (D.chosenPlace x)) :=
    (stdLevel.reduceFamily D.chosenPlace).comp
      ((conj.subgroupComap (stdLevel D.E n)).comp (inclusion h_le))
  -- The kernel lies in the stabiliser for `D.chosenLevel`, which is trivial.
  have h_inj : Injective red := (injective_iff_map_eq_one red).2 fun ⟨γ, hγ_rat, hγ_K⟩ h_red ↦ by
    have h_mem : γ ∈ classAut stdRatPoints D.chosenLevel g :=
      ⟨hγ_rat, mem_levelOf.2 ⟨hK hγ_K, h_red⟩⟩
    exact Subtype.ext (by simpa [D.classAut_eq_bot_of_le_chosenLevel le_rfl hn g] using h_mem)
  have h_rank : 2 * D.n D.m ≤ D.r * D.t := D.nat_le_of_hasLogBound
  exact (card_dvd_of_injective _ h_inj).trans (D.card_GL_dvd_chosenGroupOrder (hn.trans h_rank))

/-! ### The residue characters, and size bounds -/

lemma IsChosen.not_star (hw : D.IsChosen w) : ¬D.IsChosen (star w) := by
  obtain ⟨i, -, hw_mem⟩ := D.isChosen_iff.1 hw
  exact fun hw_star ↦ (isChosen_star_iff hw_mem).1 hw_star hw

/-- The character `D.chiMLocal w` of the residue field at `w` is trivial unless `w` is chosen, and
then it has order `P.q₂ D.towerExp = (P.q₀ * P.d) ^ (D.towerExp + 6)`, which exceeds `8 * D.m`. For
an integer `n` with `n ≠ 0` and `|n| ≤ 8 * D.m`, where `D.m` is the number of lifts, its `n`-th
power is nontrivial exactly when `w` is chosen. -/
lemma chiMLocal_zpow_ne_one_iff_isChosen (n : ℤ) (hn_ne : n ≠ 0) (hn_le : n.natAbs ≤ 8 * D.m)
    (w : FinPlace D.E) : (D.chiMLocal ^ n) w ≠ 1 ↔ D.IsChosen w := by
  by_cases hw : D.IsChosen w
  · -- `D.chiMLocal w` has order `q₂`, a multiple of `q₁ d > 8 m ≥ |n|`.
    have h_size : 8 * D.m < P.q₁ D.towerExp * P.d := D.nat_lt_of_hasLogBound
    have h_not : ¬P.q₂ D.towerExp ∣ n.natAbs := fun h_dvd ↦
      Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.2 hn_ne) (hn_le.trans_lt h_size)
        (q₁_mul_d_dvd_q₂.trans h_dvd)
    have h_ne : D.chiMLocal w ^ n ≠ 1 := by
      rwa [Ne, ← orderOf_dvd_iff_zpow_eq_one, D.orderOf_chiMLocal hw, Int.natCast_dvd]
    exact iff_of_true h_ne hw
  · simp [hw]

/-- The number `q₂ = (q₀ d) ^ (s + 6)` with `s = D.towerExp`, which is the order of the residue
characters `D.chiMLocal w` at the chosen places, is at most `exp (log b / 9)`, where
`log b = D.logB`. -/
instance : D.HasLogUpper (P.q₂ D.towerExp) (D.logB / 9) := by
  -- `q₂` is at most a fixed power of `x`, and `log x ≤ log x₁` is negligible against `log b`.
  have h_scale : D.logX ≤ D.logX₁ := by grind [D.scale_inequalities]
  have h_pow : D.x ^ (33 * (P.q₀ * P.d)) ≤ exp (D.logB / 9) := by
    rw [← exp_natCast_mul, exp_le_exp]
    calc _ ≤ (33 * (P.q₀ * P.d) : ℕ) * D.logX₁ := by gcongr
      _ ≤ D.logB / 9 := D.le_of_hasLogBound
  exact hasLogUpper_of_le_of_nonneg (D.q₂_le.trans h_pow) (Nat.cast_nonneg _)

variable (D) in
/-- The logarithm of `D.chosenGroupOrder` is at most `D.x ^ 32`, where `D.x = exp D.logX` is a scale
of the data `D`. -/
lemma log_chosenGroupOrder_le : log D.chosenGroupOrder ≤ D.x ^ 32 := by
  -- `GL n` over a field with `q` elements has at most `q ^ n²` elements.
  have h_order : D.chosenGroupOrder ≤ D.M ^ ((D.r * D.t) ^ 2 * D.f) :=
    calc _ = ∏ i : Fin 2, Nat.card (GL (Fin (D.r * D.t)) (ZMod (D.levelPrime i))) ^ D.f :=
          D.card_pi_GL_chosenPlace (D.r * D.t)
      _ ≤ ∏ i : Fin 2, (D.levelPrime i ^ (D.r * D.t) ^ 2) ^ D.f := by
          gcongr with i
          simpa using card_GL_le (n := Fin (D.r * D.t)) (ZMod (D.levelPrime i))
      _ = D.M ^ ((D.r * D.t) ^ 2 * D.f) := by
          simp only [← pow_mul, Fin.prod_univ_two, Data.M, mul_pow (D.levelPrime 0)]
  calc log D.chosenGroupOrder ≤ log (D.M ^ ((D.r * D.t) ^ 2 * D.f) : ℕ) :=
        log_le_log (Nat.cast_pos.2 (NeZero.pos _)) (Nat.cast_le.2 h_order)
    _ = (D.r * D.t) ^ 2 * D.f * log D.M := by simp
    _ ≤ exp (32 * D.logX) := D.le_of_hasLogBound
    _ = D.x ^ 32 := exp_natCast_mul 32 D.logX

/-- The bound `log chosenGroupOrder ≤ D.x ^ 32 = exp (32 * D.logX)`, as a logarithmic upper
bound. -/
instance : D.HasLogUpper (log D.chosenGroupOrder) (32 * D.logX) :=
  hasLogUpper_of_le_of_nonneg D.log_chosenGroupOrder_le (log_natCast_nonneg _)

end New.Data

end
end
end

/-!
# Levels of the chain, chain data, and the composite lift

The map `New.Data.compositeLift` on source forms is built from chains of `m` theta lifts
`X_0 → X_1 → ⋯ → X_m` between definite unitary groups, followed by restriction to the block `Y_m` of
one rank less. Here `X_j` is an index set of `𝗇_j = k + j(t + 1)` elements. The weight at stage `j`
is given by the column numbers `New.Data.columnCount` and the determinant exponents
`New.Data.lastEntry`. This file defines the levels and spaces of forms of the stages, the
restriction from `X_m` to `Y_m`, the kernels of the lifts, the glued datum at `N` in the
Schrödinger model, and chain data.

## Main definitions and results

* `New.Data.restrictedChain`: ∑_x Ψ(x) · (chain with the data of x), then `New.Data.restrictToY`.
* `New.Data.IsChainDatum`, `New.Data.compositeLift`: chain data, and the same map for the data glued
  above `N` in each double lift.

Notions from other files:
* `New.classAut`: `classAut Γ K g` is Γ ∩ gKg⁻¹, the stabiliser in Γ of the coset gK; here
  Γ = `stdRatPoints` is the rational unitary group of the standard definite space `New.stdSpace`,
  inside the finite adelic group.
* `New.Data.n`: The rank 𝗇_j = k + j(t + 1) of X_j.
* `New.Data.columnCount`: The number of columns of height h < 𝗇_j at the infinite place τ in the
  weight on X_j; it does not depend on j. For h = 1 it is `D.a` at the places in `New.Data.aPlaces`
  and 0 elsewhere; for h = k ≠ 1 it is κ_1(τ) − ⌊𝗇_1 / 2⌋, with κ_j = `D.liftWeight j`; for h > k
  with h ≡ k mod t + 1 it is `D.gap` − (t + 1); otherwise it is 0.
* `New.chain` (in `New.UpperBound.Objects.LiftChains`): the composite of the first `j` theta lifts.
* `New.Data.chosenLevel` (in `New.UpperBound.Objects.LiftChains`): the integral elements that
  reduce to `1` at every chosen place, that is, at every prime divisor of `D.piM`.

## Relation to the literature

This file sets up the objects of the upper bound. Related work is listed with the results on them,
in `New.UpperBound.Divisibility.LocalDivisibility`, `New.UpperBound.Seesaw.SeesawIdentity` and
`New.UpperBound.Divisibility.ValuationAtLevel`.
-/

@[expose] public section

noncomputable section

/-!
## The glued datum at `N` in the Schrödinger model

For a set `P` with one place of each conjugate pair above `N`, functions of matrices at `P` define
operators on finite data (`IsSplitLevel.schrodingerOpAt`). For a double lift, the seesaw produces
the sum of translates `doubleLiftGluing`; read in the model at any such `P`, this sum is the glued
datum, with no constant.
-/

namespace New

open Matrix GeneralLinearGroup Fintype WeilData Exchange Finset Gf stdLattice Space Seesaw
  SemilocalField
open scoped TensorProduct

variable {E n n' : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] {P S : Finset (FinPlace E)} {N : ℕ} [Fact N.Prime]
  {m : Type} [Fintype m] [DecidableEq m]

omit [WeilData E] in
/-- The component at a finite place `w` of the scalar element `ν` is the scalar matrix `ν w`. -/
@[simp] lemma scalarFin_atPlace (ν : unitary (𝔸f E)) (w : FinPlace E) :
    ((scalarFin n ν).atPlace w).val = diagonal fun _ : n ↦ ν.val w :=
  diagonal_map rfl

/-- Let `ν`, `ν'` be finite adeles of norm one. The Weil action with characters `a`, `b` of the pair
of scalar matrices `(ν, ν')` on the finite part for the standard spaces on `n` and `n'` is the value
of the character `pairChar a b`, `(g, h) ↦ a (det h) * (b (det g))⁻¹`, at this pair, times the
action with trivial characters of the pair of scalar matrices `(1, ν' / ν)`. -/
lemma Seesaw.pairWeilFinite_scalarFin (a b : AutChar E) (ν ν' : unitary (𝔸f E)) :
    pairWeilFinite (stdSpace E n) (stdSpace E n') a b (scalarFin n ν, scalarFin n' ν') =
      pairChar (s := 1) (s' := 1) a b ((1, scalarFin n ν), 1, scalarFin n' ν') •
        pairWeilFinite (stdSpace E n) (stdSpace E n') 1 1 (1, scalarFin n' (ν' / ν)) := by
  -- The characters factor out, and on `Hom` both pairs of scalars act by the scalar `ν' / ν`.
  have h_onHom : G.onHom (s := 1) (s' := 1) ((1, scalarFin n ν), 1, scalarFin n' ν') =
      G.onHom (s := 1) (s' := 1) ((1, (1 : Gf E n)), 1, scalarFin n' (ν' / ν)) := by
    rw [← map_one (scalarFin n), G.onHom_scalarFin, G.onHom_scalarFin, div_one]
  ext v x
  simp [pairWeil, h_onHom]

variable {E n : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)} in
variable (n) in
/-- The finite adelic matrix whose last column is `-y / N` at the places of `P` and zero at the
other places, and whose other columns are zero. -/
abbrev Seesaw.poleColumn (y : n' → P → ZMod N) : n' × (n ⊕ Unit) → 𝔸f E :=
  fun p ↦ if p.2.isRight then -residueOverN (y p.1) else 0

variable (m) in
/-- The finite adelic matrix whose last row is the conjugate of `-y / N`, supported at the
conjugates of the places of `P`, and whose other rows are zero. -/
abbrev Seesaw.poleRow (y : n' → P → ZMod N) : (m ⊕ Unit) × n' → 𝔸f E :=
  fun p ↦ if p.1.isRight then -star (residueOverN (y p.2)) else 0

omit [WeilData E] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fact N.Prime] in
/-- The entries of `poleColumn n y` vanish at the places outside `P`. -/
lemma Seesaw.poleColumn_apply_eq_zero (y : n' → P → ZMod N) (k : n' × (n ⊕ Unit)) (w : FinPlace E)
    (hw : w ∉ P) : poleColumn n y k w = 0 := by
  simp [poleColumn, apply_ite, ite_apply, hw]

omit [WeilData E] [Fintype n'] [DecidableEq n'] [Fact N.Prime] [Fintype m] [DecidableEq m] in
/-- The entries of `poleRow m y` vanish at the places whose conjugate is outside `P`. -/
lemma Seesaw.poleRow_apply_eq_zero (y : n' → P → ZMod N) (k : (m ⊕ Unit) × n') (w : FinPlace E)
    (hw_star : star w ∉ P) : poleRow m y k w = 0 := by
  simp [poleRow, apply_ite, ite_apply, hw_star]

open scoped Classical in
variable (n n' P N m) in
/-- For a double lift, the sum over the vectors `y / N` with at most simple poles at `P`, modulo
integral vectors, of the translation of the first datum by the last column `-y / N` and of the
second by the last row `-ȳ / N`. -/
def Seesaw.doubleLiftGluing : Module.End ℂ
    (((stdSpace E (n ⊕ Unit)).hom (stdSpace E n')).finitePart ⊗[ℂ]
      ((stdSpace E n').hom (stdSpace E (m ⊕ Unit))).finitePart) :=
  ∑ y : n' → P → ZMod N,
    TensorProduct.map (heisenbergFinPart _ (poleColumn n y)) (heisenbergFinPart _ (poleRow m y))

/-- The projection `V.projOn S` on the vacuum at the places of `S` and their conjugates, restricted
to the finite part of the data space of `V`. -/
abbrev Space.vacuumProjFinPart {s : n → ℤˣ} (V : Space E n s) (S : Set (FinPlace E)) :
    Module.End ℂ V.finitePart :=
  (V.projOn S).toLinearMap.restrict fun _ ↦ projOn_mem_finitePart

namespace IsSplitLevel

/-- The character `g ↦ χ (det g) |det g| ^ (-k / 2)` of `GL n` over `LocProd P`, the product of the
completions of `E` at the places of `P`. -/
def detCharAt (χ : HeckeChar E) (k : ℕ) : GL n (LocProd P) →* ℂˣ :=
  (localChar P χ (-k)).toUnitHom.comp det

/-- The operator `v ↦ Ψ ⊗ v` of the Schrödinger model at `P` on the finite part for the standard
spaces on `n` and `n'`, as a linear function of the function `Ψ` of matrices over `LocProd P`. Here
`Ψ` is read as a function of finite adelic matrices through their components at `P`. -/
def schrodingerOpAt : (Matrix n' n (LocProd P) → ℂ) →ₗ[ℂ]
    Module.End ℂ ((stdSpace E n).hom (stdSpace E n')).finitePart :=
  LinearMap.mk₂ ℂ
    (fun Ψ v ↦ ⟨_, schrodingerOp_mem_finitePart P (Ψ ∘ fun T ↦ (vecToMatrix T).map (evalPlaces P))
      v.property⟩)
    (by simp [Pi.add_comp]) (by simp [Pi.smul_comp]) (by simp) (by simp)

variable [h : IsSplitLevel P N]

/-- The element of the finite adelic unitary group that is supported above `N` and has the given
components at `P`. -/
def embedGL : GL n (LocProd P) →* Gf E n :=
  (ofSplitPlaces h.star_notMem).comp (.pi fun w ↦ map (Pi.evalRingHom _ w))

omit [WeilData E] [Fact N.Prime] in
@[simp] lemma atPlaces_embedGL (g : GL n (LocProd P)) : atPlaces P (embedGL g) = g := by
  ext i j w : 3
  have h_at : (embedGL g).atPlace w = GeneralLinearGroup.map (Pi.evalRingHom _ w) g :=
    atPlace_ofSplitPlaces star_notMem _ w
  exact congrArg (fun k : GL n (LocField w.val) ↦ k i j) h_at

open scoped Classical in
omit [WeilData E] in
/-- At a place `w` of `P`, the component `atPlace w` of `embedGL (diagN (P := P) (N := N) n S)` is
`diag (1, …, 1, N)` if `w` is in `S`, and `1` otherwise. -/
lemma atPlace_embedGL_diagN (w : P) : (embedGL (diagN (P := P) (N := N) n S)).atPlace w =
    diagGL fun i : n ⊕ Unit ↦
      if i.isLeft then 1 else if ↑w ∈ S then .mk0 (N : LocField w.val) NeZero.out else 1 :=
  (atPlace_ofSplitPlaces star_notMem _ w).trans (by simp [diagN, Units.ext_iff])

omit [WeilData E] [Fact N.Prime] in
lemma embedGL_mem_supportedOn (g : GL n (LocProd P)) : embedGL g ∈ supportedOn n P :=
  ofSplitPlaces_mem_supportedOn star_notMem _

include h

section

omit [WeilData E] [Fact N.Prime]

lemma isConjDisjoint : Set.IsConjDisjoint (E := E) P := by grind [star_notMem]

lemma natCast_level_mem : ∀ w ∈ P, ↑N ∈ w.asIdeal := fun w hw ↦ (h.natCast_mem_iff w).2 (.inl hw)

/-- Let `P` hold one place of each conjugate pair above the prime `N` (`IsSplitLevel P N`). An
element `g` of the finite adelic unitary group whose component at `P` is an integral invertible
matrix `a` (through `inclGL`) is integral at all places above `N`, that is,
`g ∈ integralAbove n N`. -/
lemma mem_integralAbove_of_inclGL_eq {g : Gf E n} {a : GL n (O (F := LocProd P))}
    (ha : inclGL a = atPlaces P g) : g ∈ integralAbove n N := by
  intro w hw
  have h_at (u : FinPlace E) (hu : u ∈ P) : g.atPlace u ∈ localIntGL n u :=
    let ⟨h_int, h_inv⟩ := mem_intGL.1 (⟨a, ha⟩ : atPlaces P g ∈ intGL n O)
    mem_intGL.2 ⟨fun i j ↦ h_int i j ⟨u, hu⟩ ⟨⟩, fun i j ↦ h_inv i j ⟨u, hu⟩ ⟨⟩⟩
  -- A place above `N` or its conjugate lies in `P`, and integrality passes to the conjugate.
  exact ((h.natCast_mem_iff w).1 hw).elim (h_at w) (atPlace_star_mem_iff.1 <| h_at _ ·)

end

section

omit [WeilData E]

/-- Let `x` be the component at `P` of `N u`, assumed integral. Its reduction modulo `N` is `c`
exactly when `u - c / N` is integral at `P`, with `c / N = residueOverN c`. -/
lemma reduction_eq_iff_idem_mul_mem {x : O (F := LocProd P)} {c : P → ZMod N} {u : 𝔸f E}
    (hx : x.val = evalPlaces P (N * u)) :
    h.reduction x = c ↔ idem P * (u - residueOverN c) ∈ Ô E := by
  simp +contextual [hx, reduction_eq_iff, sub_div, idem_mul_mem_Ô, NeZero.ne]

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`), and let `w` be in `P`. Let `ν` be an integral finite adele of norm one that
is `1` away from `w` and `w̄`. Then there is a unit `x` of the integers at `P`, with reduction `1`
modulo `N` at the places of `P` other than `w`, such that the scalar matrix `ν` is the unitary
element `embedGL` supported above `N` whose component at `P` is the scalar matrix `x`. -/
lemma exists_embedGL_scalar_eq_scalarFin [h : IsSplitLevel P N] {ν : unitary (𝔸f E)} (w : P)
    (h_int : ν.val ∈ Ô E) (h_supp : ∀ v : FinPlace E, v ≠ w.val → star v ≠ w.val → ν.val v = 1) :
    ∃ x : (O (F := LocProd P))ˣ, (∀ v : P, v ≠ w → h.reduction x v = 1) ∧
      h.embedGL (inclGL (scalar n x)) = scalarFin n ν := by
  -- `x` is the component of `ν` at `P`; its inverse is the component of `star ν`.
  have h_inv : evalPlaces P ν.val * evalPlaces P (star ν.val) = 1 := by
    rw [← map_mul, ν.property.right, map_one]
  let x : (O (F := LocProd P))ˣ :=
    .mkOfMulEqOne ⟨_, evalPlaces_mem_O _ h_int⟩ ⟨_, evalPlaces_mem_O _ (star_mem_Ô h_int)⟩
      (Subtype.ext h_inv)
  refine ⟨x, fun v hv ↦ ?_, eq_of_supportedOn (embedGL_mem_supportedOn _) ?_ ?_⟩
  · -- `P` contains no pair of conjugate places, so `v` is neither `w` nor its conjugate.
    have h_one : ν.val v = 1 := h_supp v (by grind) (by grind [star_notMem])
    have h_residue : residueAt v (x : O (F := LocProd P)) = 1 :=
      (congrArg (IsLocalRing.residue (LocInt v.val)) (Subtype.ext h_one)).trans (map_one _)
    exact (residueEquiv v).map_eq_one_iff.2 h_residue
  · simp +contextual (disch := grind) [Units.ext_iff, h_supp]
  · simp [x, Subtype.forall', embedGL, Units.ext_iff]

omit h [DecidableEq n] [DecidableEq n'] in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`), so that `residueEquiv` identifies the residue fields at `P` with `ZMod N`.
Let `f` be a function of matrices modulo `N`, and `h.liftFn f` the function of matrices at `P` that
is `f` of the reduction on integral matrices and zero elsewhere. Evaluated on finite adelic matrices
through their components at `P`, it is the residue datum of `f`: the value of `f` at the residues
at `P` if the matrix is integral there, and zero otherwise. -/
lemma liftFn_eq_residueDatum [h : IsSplitLevel P N] (f : Matrix n' n (P → ZMod N) → ℂ) :
    (h.liftFn f ∘ fun T : n' × n → 𝔸f E ↦ (vecToMatrix T).map (evalPlaces P)) =
    residueDatum (fun w : P ↦ w.val) fun T : (w : P) → Matrix n' n (ResField w.val) ↦
      f (of fun (i : n') (j : n) (w : P) ↦ residueEquiv w (T w i j)) := by
  classical
  -- The conditions of integrality at `P` agree, and on integral entries so do the residue maps.
  refine funext fun x ↦ .symm (dite_congr ?_ (fun h_int ↦ ?_) (by simp))
  · simpa [mem_O_locProd] using
      ⟨fun h_int i j w hw ↦ h_int w hw i j, fun h_int w hw i j ↦ h_int i j w hw⟩
  · congr!
    exact congrArg _ (dite_eq_left _)

/-- The composite of `h.liftFn f` with the map sending `T` to the entrywise image of `vecToMatrix T`
under `evalPlaces P` is a Schwartz–Bruhat function at `P`. -/
instance isSchwartzBruhat_liftFn (f : Matrix n' n (P → ZMod N) → ℂ) :
    IsSchwartzBruhat P (h.liftFn f ∘ fun T : n' × n → 𝔸f E ↦
      (vecToMatrix T).map (evalPlaces P)) := by
  simpa [liftFn_eq_residueDatum] using
    isSchwartzBruhat_residueDatum (w := fun w : P ↦ w.val) _ (by grind [star_notMem])

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). Let `f` be a function of matrices modulo `N`, and `h.liftFn f` the function of
matrices at `P` that is `f` of the reduction on integral matrices and zero elsewhere. For invertible
matrices `g` and `k` at `P`, the function `T ↦ h.liftFn f (k⁻¹ T g)` of finite adelic matrices, read
through their components at `P`, is Schwartz–Bruhat at `P`. -/
lemma isSchwartzBruhat_liftFn_mul [h : IsSplitLevel P N] (g : GL n (LocProd P))
    (f : Matrix n' n (P → ZMod N) → ℂ) (k : GL n' (LocProd P)) :
    IsSchwartzBruhat P fun T : n' × n → 𝔸f E ↦
      h.liftFn f (k⁻¹.val * (vecToMatrix T).map (evalPlaces P) * g.val) := by
  rw [← atPlaces_embedGL g, ← atPlaces_embedGL k]
  -- The substitution `T ↦ k⁻¹ T g` is multiplication of the vector `T` by an invertible matrix.
  let M := (G.onHom (s := 1) (s' := 1) ((1, embedGL g), 1, embedGL k)).2⁻¹.val
  simpa only [M, onHom_snd_inv_mulVec, vecToMatrix_matrixToVec, Matrix.map_mul, Function.comp_def]
    using!
    (h.isSchwartzBruhat_liftFn f).comp_mulVec M

end

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). Let `Ψ = liftFn f` be `f` of the reduction modulo `N` on integral matrices at
`P` and zero elsewhere. Let `v` lie in the finite part of the Schwartz space of
`(stdSpace E n).hom (stdSpace E n')`, the matrices between the standard definite spaces, and let
`Ψ ⊗ v = schrodingerOpAt Ψ v` in the Schrödinger model at `P`. The Weil action `pairWeilFinite` with
characters `a`, `b` of the unitary elements above `N` with components `g`, `k` at `P` turns `Ψ ⊗ v`
into `(T ↦ Ψ (k⁻¹ T g)) ⊗ v`, times a scalar. The scalar is a quotient of values of
`detCharAt χ l : x ↦ χ (det x) |det x| ^ (-l / 2)`, for `χ = c.spaceChar l` the base change of `c`
divided by `υ ^ l`, with `υ` the splitting character: the value at `k` for `c = a`, `l = card n`,
over the value at `g` for `c = b`, `l = card n'`. -/
lemma pairWeilFinite_schrodingerOpAt [h : IsSplitLevel P N] (g : GL n (LocProd P))
    (f : Matrix n' n (P → ZMod N) → ℂ) (a b : AutChar E) (k : GL n' (LocProd P))
    (v : ((stdSpace E n).hom (stdSpace E n')).finitePart) :
    pairWeilFinite (stdSpace E n) (stdSpace E n') a b (h.embedGL g, h.embedGL k)
        (schrodingerOpAt (P := P) (h.liftFn f) v) =
      ((detCharAt (b.spaceChar (card n')) (card n') g)⁻¹ *
          detCharAt (a.spaceChar (card n)) (card n) k) •
        schrodingerOpAt (P := P)
          (fun T : Matrix n' n (LocProd P) ↦ h.liftFn f (k⁻¹.val * T * g.val)) v := by
  -- Read `g` and `k` on the right as the components at `P` of their lifts; then this is
  -- `pairWeil_schrodingerOp_of_mem_supportedOn`.
  nth_rw 2 3 [← atPlaces_embedGL g, ← atPlaces_embedGL k]
  ext1
  simp [schrodingerOpAt, detCharAt, pairWeil_schrodingerOp_of_mem_supportedOn, h.isConjDisjoint,
    embedGL_mem_supportedOn,
    -coe_units_inv, -atPlaces_embedGL]
  -- The two functions of matrices agree, and the two scalars differ only in notation.
  congr 1
  simp [-atPlaces_embedGL, field]

omit h [Fact N.Prime] in
/-- Suppose the base change of `a` is unramified at every place of `P`. Let
`χ = a.spaceChar i` be this base change divided by the `i`-th power of the splitting character `υ`.
The character `detCharAt χ k: x ↦ χ (det x) |det x| ^ (-k / 2)` of the invertible matrices at `P` is
trivial on those that are invertible over the integers, which `inclGL` includes. -/
lemma detCharAt_inclGL (a : AutChar E)
    (h_unr : ∀ w ∈ P, CharUnramifiedAt a.baseChange.finPart w) (i k : ℕ)
    (g : GL n (O (F := LocProd P))) : detCharAt (a.spaceChar i) k (inclGL g) = 1 := by
  -- The determinant is a unit at each place of `P`, where both characters in `spaceChar` are
  -- unramified.
  have h_unit : ∀ w : P, Valued.v ((g.val.det : LocProd P) w) = 1 :=
    isIntegralUnit_iff_v_eq_one.1 (isIntegralUnit_iff_isUnit.2 g.det.isUnit)
  have h_space (w : P) (u : (LocField w.val)ˣ) (hu : Valued.v u.val = 1) :
      (a.spaceChar i).finPart (locIdele w.val u) = 1 := by
    simp [AutChar.spaceChar, h_unr w w.property u hu, charUnramifiedAt_upsilon w.val u hu]
  ext
  simp [detCharAt, localChar, g.map_det, norm_locField_eq_q_zpow, h_unit, h_space]

section

omit [WeilData E]

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). The character `detCharAt χ k` is `g ↦ χ (det g) |det g| ^ (-k / 2)` over the
completions at `P`, and `diagN (P := P) (N := N) n S` is `diag (1, …, 1, N)` at `P ∩ S` and `1` at
`P \ S`. For an embedding `ι` of `ℂ` into `ℂ_[N]` and `k ≤ k'`, the `N`-adic size of
`detCharAt χ k'` at this matrix is at most that of `detCharAt χ k`, whatever the sizes of the two
matrices. -/
lemma norm_detCharAt_diagN_anti [h : IsSplitLevel P N] {ι : ℂ →+* ℂ_[N]} {χ : HeckeChar E}
    {k k' : ℕ} (hk : k ≤ k') :
    ‖ι (detCharAt χ k' (diagN (P := P) (N := N) n S))‖ ≤
      ‖ι (detCharAt χ k (diagN (P := P) (N := N) n' S))‖ := by
  classical
  -- The local determinant `d w` is `N` or `1`, of norm `N⁻¹` or `1`; the square root of this norm
  -- has `N`-adic size at least `1`, and it occurs with the exponent `-k`.
  let d (w : P) : (LocField w.val)ˣ := if ↑w ∈ S then .mk0 N NeZero.out else 1
  have hd_one_le (w : P) : 1 ≤ ‖ι √‖(d w).val‖‖ := by
    rw [← one_le_sq_iff₀ (by simp), ← norm_pow, ← map_pow]
    norm_cast
    by_cases hw : ↑w ∈ S
    · simp [d, hw, norm_locField_eq_q_zpow, h.q_eq, h.v_natCast, norm_p_eq_inv, NeZero.one_le,
        NeZero.ne]
    · simp [d, hw]
  -- In every rank the value is a product over `P` of local factors at the determinants `d w`.
  have h_norm {r : Type} [Fintype r] [DecidableEq r] (l : ℕ) :
      ‖ι (detCharAt χ l (diagN (P := P) (N := N) r S))‖ = ∏ w : P,
        ‖ι (χ.finPart (locIdele w.val (d w)) : ℂ)‖ * (‖ι √‖(d w).val‖‖ ^ l)⁻¹ := by
    have h_det : (detCharAt χ l (diagN (P := P) (N := N) r S) : ℂ) =
        localChar P χ (-l) (MulEquiv.piUnits.symm d : (LocProd P)ˣ) := by
      simp [diagN, detCharAt, d]
    have h_component (w : P) : Units.map (Pi.evalMonoidHom (fun v : P ↦ LocField v.val) w)
        (MulEquiv.piUnits.symm d) = d w := rfl
    simp [h_det, localChar, h_component]
  rw [h_norm, h_norm]
  gcongr with w
  · simp
  · exact hd_one_le w

open scoped Classical in
omit h in
/-- The matrix `diag (1, …, 1, N)` at all of `P` is the product of those at `P \ S` and at `S`. -/
lemma diagN_eq_sdiff_mul (S : Finset (FinPlace E)) :
    diagN (P := P) (N := N) n P =
      diagN (P := P) (N := N) n (P \ S) * diagN (P := P) (N := N) n S := by
  simp +contextual [diagN, ← map_mul, Pi.mul_def]

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). An adele is integral at `P` if it lies in the integral adeles `Ô E` after
multiplication by `idem P`, the adele that is `1` at `P` and `0` elsewhere. If `N z` is integral at
`P`, then `z - y / N` is integral at `P` for exactly one class `y` modulo `N`, and otherwise for
none. -/
lemma exists_sub_residueOverN_mem_iff [h : IsSplitLevel P N] (z : 𝔸f E) :
    ∃ b : P → ZMod N, ∀ y : P → ZMod N,
      idem P * (z - residueOverN y) ∈ Ô E ↔ idem P * ((N : 𝔸f E) * z) ∈ Ô E ∧ b = y := by
  -- `b` is the residue of `N z` at `P` when `N z` is integral there.
  let x : O (F := LocProd P) := Function.invFun Subtype.val (evalPlaces P (N * z))
  refine ⟨h.reduction x, fun y ↦ ?_⟩
  -- If `z - y / N` is integral at `P`, so is `N z = N (z - y / N) + y`.
  have h_int (hz : idem P * (z - residueOverN y) ∈ Ô E) : idem P * ((N : 𝔸f E) * z) ∈ Ô E := by
    simpa [mul_sub, mul_div_cancel₀, mem_O_locProd, idem_mul_mem_Ô, idem_apply, NeZero.ne] using
      add_mem (nsmul_mem (evalPlaces_mem_O _ hz) N)
        (mem_O_locProd.2 fun w ↦ natCast_mem (LocInt _) (y w).val)
  refine (iff_and_self.2 h_int).trans (and_congr_right fun hz ↦ ?_)
  have hx : x.val = evalPlaces P (N * z) :=
    Function.invFun_eq (by simpa [mem_O_locProd, idem_mul_mem_Ô] using hz)
  exact (reduction_eq_iff_idem_mul_mem hx).symm

/-- The finite adele `residueOverN y`, which is `y w / N` at each `w ∈ P` and `0` elsewhere,
multiplied on the left by its conjugate `star (residueOverN y)`, is zero. -/
lemma star_residueOverN_mul_self (y : P → ZMod N) : star (residueOverN y) * residueOverN y = 0 := by
  rw [← idem_mul_residueOverN y, star_mul', mul_mul_mul_comm, mul_comm (star (idem _)),
    idem_mul_star h.isConjDisjoint, zero_mul]

end

section Glued

omit h

omit [WeilData E] [Fact N.Prime] in
/-- The idempotent of the places in `P` and their conjugates is that of the places in `S` and their
conjugates, both being the places above `N`. -/
lemma idem_add_star_eq [hP : IsSplitLevel P N] (hS : IsSplitLevel S N) :
    (idem P + star (idem P) : 𝔸f E) = idem S + star (idem S) := by
  ext w
  simp [idem_apply]
  grind [hP.star_notMem w, hS.star_notMem w, hP.natCast_mem_iff w, hS.natCast_mem_iff w]

omit [WeilData E] in
/-- Let `P` and `S` each hold one place of every conjugate pair above the prime `N`, all unramified
of degree one (`IsSplitLevel`). Let `y / N = residueOverN y` run over the classes with simple poles
at `S`. Let `p` be `N` at `S` and `1` elsewhere, so that `N + 1 - p` is `1` at `S` and `N`
elsewhere. If `t p` and `(N + 1 - p) s` are integral at `P`, then `t - y / N` and `s - ȳ / N` are
both integral at `P` for exactly one class `y`; otherwise for none. -/
lemma exists_sub_mem_and_sub_star_mem_iff [hP : IsSplitLevel P N] (hS : IsSplitLevel S N)
    {p : 𝔸f E} (hp : p = 1 + idem S * ((N : 𝔸f E) - 1)) (t s : 𝔸f E) :
    ∃ b : S → ZMod N, ∀ y : S → ZMod N,
      idem P * (t - residueOverN y) ∈ Ô E ∧ idem P * (s - star (residueOverN y)) ∈ Ô E ↔
        (idem P * (t * p) ∈ Ô E ∧ idem P * (((N : 𝔸f E) + 1 - p) * s) ∈ Ô E) ∧ b = y := by
  -- Integrality of an adele and its conjugate at `P` means integrality at all places above `N`.
  have h_closure (x : 𝔸f E) : idem P * x ∈ Ô E ∧ idem P * star x ∈ Ô E ↔
      idem S * x ∈ Ô E ∧ idem S * star x ∈ Ô E := by
    grind [IsSplitLevel, star_star, idem_mul_mem_Ô, v_star_apply]
  -- `b` is the class at `S` of the adele `z` that is `t` on `P` and `s̄` on the conjugates of `P`.
  let z : 𝔸f E := idem P * t + star (idem P * s)
  obtain ⟨b, hb⟩ := hS.exists_sub_residueOverN_mem_iff z
  refine ⟨b, fun y ↦ ?_⟩
  -- Apply this to `z - y / N` and to `p z`.
  have h_sub := h_closure (z - residueOverN y)
  have h_mul := h_closure (p * z)
  simp only [z, hp, star_sub, star_add, star_mul', star_star, star_one, star_natCast] at h_sub h_mul
  grind [hb y, idem_mul_star hP.isConjDisjoint, idem_mul_star hS.isConjDisjoint,
    hP.idem_add_star_eq hS, idem_mul_residueOverN, idem_mul_self, star_mul']

open scoped Classical in
/-- Let `P` and `S` each hold one place of every conjugate pair above the prime `N`, all unramified
of degree one (`IsSplitLevel`); neither need contain the other. Translate the indicators of the
matrices integral at `P`, in the Schrödinger model at `P`, by `poleColumn` and `poleRow` (last
column `-y / N` at `S`, last row its conjugate). The products of their values at `T` and `R`, summed
over `y`, give `gluedDatum T' R'` at `T' = T diag (1, …, 1, N)_S` and
`R' = diag (1, …, 1, N)_{P \ S} R`. This is zero unless `T'` and `R'` are integral at `P`, and then
it is `ψ_N c`, where `c` is the residue modulo `N` at `P` of the entry of `R' T'` in the last row
and last column. Here `ψ_N c = ψ₀ (-c / N)` (`psiN`), with `ψ₀` the additive character
`stdLattice.selfDualAddChar E`. So the sum is supported on the pairs `(T, R)` that are integral at
`P` up to simple poles in the last column of `T` at `P ∩ S` and in the last row of `R` at
`P \ S`. -/
lemma sum_translate_eq_gluedDatum [hP : IsSplitLevel P N] (hS : IsSplitLevel S N)
    (T : n' × (n ⊕ Unit) → 𝔸f E) (R : (m ⊕ Unit) × n' → 𝔸f E) :
    ∑ y : n' → S → ZMod N,
        schrodingerAct P (poleColumn n y) (boxIndicator (n' × (n ⊕ Unit)) P) T *
          schrodingerAct P (poleRow m y) (boxIndicator ((m ⊕ Unit) × n') P) R =
      hP.gluedDatum ((vecToMatrix T).map (evalPlaces P) * (diagN (P := P) (N := N) n S).val)
        ((diagN (P := P) (N := N) m (P \ S)).val * (vecToMatrix R).map (evalPlaces P)) := by
  -- Let `t` be the last column of `T` and `r` the last row of `R`. At most one class `b` makes
  -- `t - b / N` and `r - b̄ / N` integral at `P`, and its term is `ψ₀ (-r ⬝ t)`.
  let j : 𝔸f E := idem P
  let p : 𝔸f E := 1 + idem S * ((N : 𝔸f E) - 1)
  choose b hb using fun i : n' ↦
    hP.exists_sub_mem_and_sub_star_mem_iff hS (p := p) rfl (T (i, .inr ())) (R (.inr (), i))
  have hD_S : (diagN (P := P) (N := N) n S).val =
      diagonal fun i ↦ evalPlaces P (if i.isLeft then 1 else p) := by
    simp +contextual [diagN, funext_iff, apply_ite, p, idem_apply]
  have hD_PS : (diagN (P := P) (N := N) m (P \ S)).val =
      diagonal fun i ↦ evalPlaces P (if i.isLeft then 1 else N + 1 - p) := by
    simp +contextual [diagN, funext_iff, apply_ite, p, idem_apply]
  have h_int (x : 𝔸f E) : evalPlaces P x ∈ O ↔ j * x ∈ Ô E := by
    simp [j, mem_O_locProd, idem_mul_mem_Ô]
  have h_norm (i : n') : star (residueOverN (b i)) * residueOverN (b i) = 0 :=
    hS.star_residueOverN_mul_self (b i)
  have hj_idem : j * j = j := idem_mul_self _
  have hp_mul : p * (N + 1 - p) = N := by grind [idem_mul_self]
  -- Each term is a character value on a set given by integrality conditions, and zero off it.
  simp [gluedDatum, charDatum, poleColumn, poleRow, hD_S, hD_PS, h_int, ← map_mul, vecToMatrix,
    schrodingerAct, ← ite_and, mem_integralBox, ← AddChar.map_add_eq_mul, liftFn_apply, ← map_sum,
    sum_prod_type, dotProduct, mul_sum]
  -- Only the class `b` contributes.
  rw [Fintype.sum_eq_single b fun y hy ↦ ite_eq_right fun h_y ↦
    hy (funext fun i ↦ ((hb i (y i)).1 (by grind)).right.symm)]
  replace hb (i : n') := hb i (b i)
  repeat split
  · -- Let `c` be the residue of `N r ⬝ t`. The two phases differ by
    -- `(t - b / N) ⬝ (r - b̄ / N) - (r ⬝ t - c / N)` at `P`, which is integral.
    generalize hc : hP.reduction _ = c
    have h_prod : ∑ i, j * (T (i, .inr ()) - residueOverN (b i)) *
        (j * (R (.inr (), i) - star (residueOverN (b i)))) ∈ Ô E :=
      sum_mem fun i _ ↦ ((hb i).2 (by grind)).elim mul_mem
    have h_red : j * (∑ i, R (.inr (), i) * T (i, .inr ()) - residueOverN c) ∈ Ô E := by
      refine (reduction_eq_iff_idem_mul_mem ?_).1 hc
      simp [-map_mul, mul_sum]
      grind
    apply selfDualAddChar_congr 0 (sub_mem h_prod h_red)
    simp [← sum_add_distrib, ← sum_neg_distrib, ← sum_sub_distrib, ← sub_add, mul_sub, mul_sum]
    grind [idem_mul_residueOverN]
  -- By `hb` the two supports agree.
  all_goals grind

open scoped Classical in
/-- **The glued datum in any model.** Let `P` and `S` each hold one place of every conjugate pair
above the prime `N`, all unramified of degree one (`IsSplitLevel`). Let `v`, `v'` be finite data of
`Hom (n + 1, n')` and `Hom (n', m + 1)`. Average each over the Heisenberg operators of the integral
vectors supported above `N` (`vacuumProjFinPart`), and apply `doubleLiftGluing`, the sum over `y`
modulo `N` at `S` of the translations by the last column `-y / N` and the last row `-ȳ / N`. The
result is given in the Schrödinger model at `P` by a sum over the vectors `z` modulo `N` at `P`.
Here `lastColDatum z` is the indicator of the matrices integral at `P` whose last column reduces to
`z` modulo `N`. The function `charDatum z` is zero off the integral matrices, and on these it is
`ψ_N (r ⬝ᵥ z)`, with `r` the reduction of the last row and `ψ_N c = ψ₀ (-c / N)` (`psiN`) for the
additive character `ψ₀ = stdLattice.selfDualAddChar E`. The matrices are first multiplied by
`diagN (P := P) (N := N) n S` and `diagN (P := P) (N := N) m (P \ S)`, which are `diag (1, …, 1, N)`
at `P ∩ S` and at `P \ S` respectively, and `1` at the other places of `P`. -/
lemma doubleLiftGluing_eq_sum_schrodingerOpAt [hP : IsSplitLevel P N] (hS : IsSplitLevel S N)
    (v : ((stdSpace E (n ⊕ Unit)).hom (stdSpace E n')).finitePart)
    (v' : ((stdSpace E n').hom (stdSpace E (m ⊕ Unit))).finitePart) :
    doubleLiftGluing n n' S N m
        (vacuumProjFinPart ((stdSpace E (n ⊕ Unit)).hom (stdSpace E n')) S v ⊗ₜ[ℂ]
          vacuumProjFinPart ((stdSpace E n').hom (stdSpace E (m ⊕ Unit))) S v') =
      ∑ z : n' → P → ZMod N,
        schrodingerOpAt (P := P) (fun T : Matrix n' (n ⊕ Unit) (LocProd P) ↦
            hP.lastColDatum z (T * (diagN (P := P) (N := N) n S).val)) v ⊗ₜ[ℂ]
          schrodingerOpAt (P := P) (fun R : Matrix (m ⊕ Unit) n' (LocProd P) ↦
            hP.charDatum z ((diagN (P := P) (N := N) m (P \ S)).val * R)) v' := by
  -- Both sides come from tensors of functions, and these tensors have the same values.
  let F (y : n' → S → ZMod N) := schrodingerAct P (poleColumn n y) (boxIndicator _ P)
  let G (y : n' → S → ZMod N) := schrodingerAct P (poleRow m y) (boxIndicator _ P)
  let F' (z : n' → P → ZMod N) (T : n' × (n ⊕ Unit) → 𝔸f E) : ℂ :=
    hP.lastColDatum z ((vecToMatrix T).map (evalPlaces P) * (diagN (P := P) (N := N) n S).val)
  let G' (z : n' → P → ZMod N) (R : (m ⊕ Unit) × n' → 𝔸f E) : ℂ :=
    hP.charDatum z ((diagN (P := P) (N := N) m (P \ S)).val * (vecToMatrix R).map (evalPlaces P))
  have h_kernel : ∑ y, F y ⊗ₜ[ℂ] G y = ∑ z, F' z ⊗ₜ G' z := by
    refine sub_eq_zero.1
      (tensor_eq_zero_of_separating (f := .proj) funext _ fun T ↦ funext fun R ↦ ?_)
    simpa [sub_eq_zero, gluedDatum_eq_sum] using hP.sum_translate_eq_gluedDatum hS T R
  have h_supp (y : S → ZMod N) :
      (idem S + star (idem S)) * residueOverN y = residueOverN y ∧
      (idem S + star (idem S)) * star (residueOverN y) = star (residueOverN y) := by
    grind [idem_mul_star hS.isConjDisjoint, idem_mul_residueOverN, star_mul']
  let applyModel := TensorProduct.map
    ((ContinuousLinearMap.apply ℂ _ v.val).toLinearMap ∘ₗ Space.schrodingerOp _ P)
    ((ContinuousLinearMap.apply ℂ _ v'.val).toLinearMap ∘ₗ Space.schrodingerOp _ P)
  apply Module.Flat.tensorProduct_mapIncl_injective_of_left
  calc
    _ = applyModel (∑ y, F y ⊗ₜ G y) := by
      -- A translated indicator gives a translate of the projection on vacua, and this projection
      -- is the same for `P` and `S`.
      simp [applyModel, F, G, doubleLiftGluing, poleColumn, poleRow, hP.idem_add_star_eq hS, h_supp,
        hS.star_residueOverN_mul_self, mul_comm (residueOverN _), projOn, finHeisenbergOp, semichar,
        idem_conjClosure_eq_add_star, schrodingerOp_schrodingerAct_boxIndicator,
        isConjDisjoint (N := N), Pi.smul_def, apply_ite, dotProduct]
    _ = applyModel (∑ z, F' z ⊗ₜ G' z) := congrArg applyModel h_kernel
    _ = _ := by simp [applyModel, F', G', schrodingerOpAt, Function.comp_def]

end Glued

end IsSplitLevel

end New

/-!
## Levels, spaces of forms and branching along the chain

* `New.Data.IsBranchingMap`: the properties of an integral branching matrix from `X_m` to `Y_m`.
  It intertwines the actions up to the character with exponents `New.Data.branchExponent`. Its
  operator norm is bounded, and over `ℂ` it spans the equivariant maps.

A weight is a pair `(κ, e)`: `κ τ h` counts the columns of height `h` of the diagram at `τ`, and
`e τ` is the power of the determinant (`New.weylRep`).
-/

section ColumnDefs

open Matrix Finset Subgroup Ideal Fintype

namespace New.Data

variable {P : Parameters} (D : Data P) (j : ℕ) {w : FinPlace D.E}

/-! ### The primes dividing `π` -/

@[simp] lemma piN_ne_zero : D.piN ≠ 0 := by grind [piN_mul_star, NeZero.natCast_ne]

/-- The finite set of primes w of E dividing π = `D.piN`, the integer of E with π π̄ = N. -/
def piNPlaces : Finset (FinPlace D.E) :=
  (finite_factors (span_singleton_eq_bot.ne.mpr D.piN_ne_zero)).toFinset

lemma mem_piNPlaces : w ∈ D.piNPlaces ↔ D.piN ∈ w.asIdeal := by simp [piNPlaces]

/-- Of a place `w` above the prime `D.N` and its conjugate `star w`, exactly one lies in
`D.piNPlaces`, that is, divides the integer `D.piN` of E. -/
lemma star_mem_piNPlaces_iff (hN_mem : ↑D.N ∈ w.asIdeal) :
    star w ∈ D.piNPlaces ↔ w ∉ D.piNPlaces := by
  rw [mem_piNPlaces, mem_piNPlaces, mem_star_place]
  exact P.star_mem_iff_notMem D.N_modEq_one hN_mem D.piN_mul_star_eq_N_mul_one D.N.coprime_one_right

/-- The primes `D.piNPlaces` dividing `π = D.piN`, the integer of `E` with `π π̄ = N`, are split of
degree one above `N = D.N` (`IsSplitLevel`): none is conjugate to one of them, each has norm `N`,
and `N` is a uniformiser at each. -/
protected lemma isSplitLevel_piNPlaces : IsSplitLevel D.piNPlaces D.N := by
  -- As `π * star π = N` and `N` splits completely, a place above `N` has norm `N` and contains
  -- exactly one of `π` and `star π`.
  have N_mem {w : FinPlace D.E} (hw : w ∈ D.piNPlaces) : ↑D.N ∈ w.asIdeal := by
    simpa only [piN_mul_star] using w.asIdeal.mul_mem_right (star D.piN) (D.mem_piNPlaces.1 hw)
  refine
    { star_notMem := fun w hw h_star ↦ (D.star_mem_piNPlaces_iff (N_mem hw)).1 h_star hw
      q_eq := fun w hw ↦ P.q_eq_of_modEq_one D.N_modEq_one (N_mem hw)
      v_natCast := fun w hw ↦ v_N_eq_exp_neg_one (N_mem hw)
      natCast_mem_iff := fun w ↦ ⟨fun hw ↦ by simp [D.star_mem_piNPlaces_iff hw, em], ?_⟩ }
  exact fun h_or ↦ h_or.elim N_mem fun h_star ↦ by
    simpa only [mem_star_place, star_natCast] using N_mem h_star

/-- The number of primes of E dividing π = `D.piN` (the set `D.piNPlaces`) equals `D.f`, the number
of infinite places of E. -/
lemma card_piNPlaces : #D.piNPlaces = D.f := by
  -- The infinite places are in bijection with the finite places containing both `π` and `N`.
  obtain ⟨e⟩ : Nonempty (D.Φ ≃ {w : FinPlace D.E // D.piN ∈ w.asIdeal ∧ ↑D.N ∈ w.asIdeal}) :=
    P.nonempty_infinitePlace_equiv_finPlace D.N_modEq_one D.piN_mul_star_eq_N_mul_one
      D.N.coprime_one_right
  simpa [and_iff_left_of_imp (D.isSplitLevel_piNPlaces.natCast_level_mem _), ← mem_piNPlaces] using
    e.cardinal_eq.symm

/-! ### The level of stage `j` -/

/-- The level of stage j: elements of the chosen level `New.Data.chosenLevel` on X_j whose last row
is congruent to (0, …, 0, 1) modulo π. -/
def levelX : Subgroup (Gf D.E (D.X j)) :=
  D.chosenLevel (n := D.X j) ⊓
    (congruenceGL (Ô D.E ∙ algebraMap (NumberField.RingOfIntegers D.E) (𝔸f D.E) D.piN)
        Sum.inr).subgroupOf (U 1)

lemma principalLevel_le_levelX : principalLevel (D.X j) (D.piM * D.piN) ≤ D.levelX j := by
  -- Level `piM * π` lies in level `piM` and in level `π`; the latter constrains every row.
  intro g hg
  have hg_π : g ∈ principalLevel (D.X j) D.piN := principalLevel_le_of_dvd (dvd_mul_left ..) hg
  exact ⟨D.principalLevel_le_chosenLevel (by simp) hg, hg_π.imp_right (by simp)⟩

/-- The level of stage j is a level: it lies in `New.stdLevel` and is open. -/
instance isLevel_levelX {j : ℕ} : IsLevel (D.levelX j) where
  le := inf_le_of_left_le levelOf_le_stdLevel
  isOpen := isOpen_mono (D.principalLevel_le_levelX j) (isOpen_principalLevel (by simp))

/-- A chosen bijection between the finite index sets Y_m and `InitIndex m`, which have the same
cardinality. -/
def lastIndexEquiv : D.Y D.m ≃ D.InitIndex D.m :=
  Fintype.equivOfCardEq <| by
    simp only [BlockIndex.card, card_sum, Fintype.card_fin, card_unique]
    grind [ϱ, n]

lemma card_X : card (D.X j) = D.n j := by
  simpa using Nat.sub_add_cancel (by grind [n] : 1 ≤ D.n j)

lemma card_Y_m : card (D.Y D.m) = D.n D.m - 1 :=
  (card_congr D.lastIndexEquiv).trans (Fintype.card_fin _)

/-- For each `i`, the `i`-th row length of the diagram with `D.columnCount τ u` columns of each
height `u < n_{j+1}` (`New.diagramWeight`; `rankAt` gives the rank at `τ`) is row `i` of the diagram
`New.Data.liftDiagram` of lift `j + 1`. -/
lemma cast_diagramWeight_columnCount (τ : D.Φ) (i : ℕ) :
    (diagramWeight (rankAt fun _ : D.Φ ↦ D.X (j + 1)) D.columnCount (τ, i) : ℤ) =
      D.liftDiagram j τ i := by
  rw [diagramWeight_apply, rankAt, card_X, liftDiagram_eq_sum_columnCount]

/-- The properties of a branching map from the Weyl module of the weight `μ(X_m)` to that of
`μ(Y_m)`. The weights have the column numbers `D.columnCount` and `D.columnsY`, and both have the
determinant exponents `D.lastEntry D.m`. -/
structure IsBranchingMap
    (br : Matrix (WeylIndex (D.Y D.m) D.columnsY) (WeylIndex (D.X D.m) D.columnCount) ℤ) :
      Prop where
  /-- Over every field of characteristic zero, `br` takes the action of `y = diag (g, z)` to
  `∏ τ, z τ ^ n_τ` times the action of `g`, where `n_τ = D.branchExponent τ` is the sum of the
  entries of `μ(X_m)` at `τ` less that of `μ(Y_m)`. -/
  mul_weylRep (R : Type) [Field R] [CharZero R] (g : D.Φ → GL (D.Y D.m) R) (z : D.Φ → Rˣ)
    (y : D.Φ → GL (D.X D.m) R)
    (hy : ∀ τ : D.Φ, (y τ).val = GL.blockScalar (fun _ ↦ D.lastIndexEquiv.sumCongr (.refl Unit))
      (fun τ : D.Φ ↦ (g τ).val) (fun τ : D.Φ ↦ (z τ).val) τ) :
    br.map ((↑) : ℤ → R) * weylRep D.columnCount (D.lastEntry D.m) y =
      (∏ τ : D.Φ, z τ ^ D.branchExponent τ) •
        (weylRep D.columnsY (D.lastEntry D.m) g * br.map ((↑) : ℤ → R))
  /-- The square of the operator norm of `br` is at most `exp (x ^ 70)`, with `x = D.x` the length
  of the prime sum. -/
  weylNormSq_le (ξ : WeylIndex (D.X D.m) D.columnCount → ℂ) :
    weylNormSq (br.map (↑) *ᵥ ξ) ≤ Real.exp (D.x ^ 70) * weylNormSq ξ
  /-- Every complex matrix that is equivariant for the elements `diag (g, 1)`, `g` unitary, is a
  multiple of `br`. -/
  spans : SpansBranchingMaps (fun _ ↦ D.lastIndexEquiv.sumCongr (.refl Unit)) (D.lastEntry D.m)
    (D.lastEntry D.m) (br.map (↑))

/-- The weight on `Y_m` has `D.columnsY τ u` columns of height `u` at the infinite place `τ`. There
is a number `l` that bounds the boxes in the columns of height at least `k` and less than
`n_m - 1`, summed over `τ`, and satisfies `((l ^ l) ^ 3) ^ 2 ≤ exp (x ^ 70)`, with `x = D.x` the
length of the prime sum. -/
lemma exists_sum_columnsY_le_and_pow_le_exp :
    ∃ l : ℕ, (∑ τ : D.Φ, ∑ u ∈ Ico D.k (card (D.Y D.m)), u * D.columnsY τ u ≤ l) ∧
      (((l : ℝ) ^ l) ^ 3) ^ 2 ≤ Real.exp (D.x ^ 70) := by
  -- Take `l = f n_m² Δ`, with `Δ = D.gap`.
  refine ⟨∑ _ : D.Φ, D.n D.m * (D.n D.m * D.gap), sum_le_sum fun τ _ ↦ ?_, ?_⟩
  · -- at most `n_m` heights, each below `n_m`, and at most `Δ` columns of each height
    rw [card_Y_m]
    refine (sum_le_card_nsmul _ _ (D.n D.m * D.gap) fun u hu ↦ ?_).trans ?_
    · exact Nat.mul_le_mul (by grind) (D.columnsY_le τ (mem_Ico.1 hu).1)
    · exact Nat.mul_le_mul_right _ (by grind [Nat.card_Ico])
  · refine Real.le_exp_of_log_le ?_
    push_cast [sum_const, card_univ, smul_eq_mul, Real.log_pow]
    exact D.le_of_hasLogBound

/-- There is an integer matrix `br` from the Weyl module on `X_m` to that on `Y_m` that is a
branching map (`IsBranchingMap`). It is equivariant for the block matrices `diag (g, z)` up to the
character `∏ τ, z τ ^ n_τ`, where `n_τ = D.branchExponent τ` is the sum of the entries of the weight
on `X_m` at `τ` less that on `Y_m`. The square of its operator norm is at most `exp (x ^ 70)`, with
`x = D.x` the length of the prime sum. Over `ℂ` it spans the maps that are equivariant for
`diag (g, 1)`, `g` unitary. -/
lemma exists_isBranchingMap :
    ∃ br : Matrix (WeylIndex (D.Y D.m) D.columnsY) (WeylIndex (D.X D.m) D.columnCount) ℤ,
      D.IsBranchingMap br := by
  -- The weights interlace: the columns counted by `keptColumns` keep their height, the others lose
  -- a box. As `keptColumns` vanishes below height `k`, the norm bound omits the heights below `k`.
  have h_split : (D.columnCount - fun _ ↦ D.keptColumns) + (fun _ ↦ D.keptColumns) =
    D.columnCount :=
    tsub_add_cancel_of_le fun τ u ↦ D.keptColumns_le_columnCount τ u
  have h_last (τ : D.Φ) :
      D.lastEntry D.m τ = D.lastEntry D.m τ + D.keptColumns (card (D.Y D.m)) := by
    rw [card_Y_m, keptColumns_n_sub_one, Nat.cast_zero, add_zero]
  have h_interlace (τ : D.Φ) (u : ℕ) (_ : u ∈ Ioo 0 (card (D.Y D.m))) :
      D.columnsY τ u = D.keptColumns u + (D.columnCount τ (u + 1) - D.keptColumns (u + 1)) := rfl
  obtain ⟨br, h_equivariant, h_norm, h_span⟩ := exists_branching_matrix
    (fun _ : D.Φ ↦ D.lastIndexEquiv.sumCongr (.refl Unit)) D.columnsY D.k (D.lastEntry D.m)
    (D.lastEntry D.m) h_split h_interlace (fun _ _ ↦ D.keptColumns_eq_zero_of_lt_k) h_last
  refine ⟨br, fun R _ _ g z y hy ↦ ?_, fun ξ ↦ ?_, h_span⟩
  · rw [h_equivariant R g z y hy]
    simp only [diagramWeight_apply, rankAt, card_X, branchExponent_eq_sum_columns, Pi.sub_apply]
  · obtain ⟨l, h_boxes, h_exp⟩ := D.exists_sum_columnsY_le_and_pow_le_exp
    exact (h_norm l h_boxes ξ).trans (mul_le_mul_of_nonneg_right h_exp (weylNormSq_nonneg ξ))

/-- A fixed branching map `br` from the Weyl module of `μ(X_m)` to that of `μ(Y_m)`. -/
def branching : Matrix (WeylIndex (D.Y D.m) D.columnsY) (WeylIndex (D.X D.m) D.columnCount) ℤ :=
  D.exists_isBranchingMap.choose

lemma isBranchingMap_branching : D.IsBranchingMap D.branching :=
  D.exists_isBranchingMap.choose_spec

/-- The level of stage 0 is free: for the group `Γ` of rational points and this level `K`, the
groups `Γ ∩ g K g⁻¹` are trivial. -/
lemma classAut_levelX_zero_eq_bot :
    ∀ g : Gf D.E (D.X 0), classAut stdRatPoints (D.levelX 0) g = ⊥ :=
  D.classAut_eq_bot_of_le_chosenLevel inf_le_left (by grind [card_X, n])

/-! ### Source forms and smooth forms -/

/-- The space of source forms: algebraic forms on X_0 of weight (`D.columnCount`, `D.lastEntry 0`)
(column numbers, determinant exponents) fixed by the level `New.Data.levelX` of stage 0. -/
abbrev SourceForm := levelSpace (algFormRep D.columnCount (D.lastEntry 0)) (D.levelX 0)

/-- The space of smooth algebraic forms on X_j of weight (`D.columnCount`, `D.lastEntry j`): column
numbers and determinant exponents. -/
abbrev FormX : Submodule ℂ (Gf D.E (D.X j) → WeylIndex (D.X j) D.columnCount → ℂ) :=
  AlgForm (D.X j) D.columnCount (D.lastEntry j)

/-! ### Restriction of forms from `X_m` to `Y_m` -/

/-- The homomorphism g ↦ diag(g, 1) from the finite adelic unitary group on Y_m to that on X_m,
relabelling along `New.Data.lastIndexEquiv`. -/
def borderU :
    U (1 : Matrix (D.Y D.m) (D.Y D.m) (𝔸f D.E)) →*
      U (1 : Matrix (D.InitIndex D.m ⊕ Unit) (D.InitIndex D.m ⊕ Unit) (𝔸f D.E)) :=
  (U.block (R := 𝔸f D.E) (D.lastIndexEquiv.sumCongr (Equiv.refl Unit))).comp
    (MonoidHom.inl (U 1) (U (1 : Matrix Unit Unit (𝔸f D.E))))

/-- The restriction of algebraic forms from X_m to Y_m: restrict to points diag(h,1), apply the
branching matrix, and multiply by ∏_τ τ(π̄)^{−n_τ}, τ read as its embedding in the CM type. -/
def restrictToY :
    AlgForm (D.InitIndex D.m ⊕ Unit) D.columnCount (D.lastEntry D.m) →ₗ[ℂ]
      AlgForm (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
  (∏ τ : NumberField.InfinitePlace D.E, Φ τ (star ↑D.piN) ^ (-D.branchExponent τ)) •
    ((D.branching.map (↑)).mulVecLin.compLeft (U 1) ∘ₗ
      .funLeft ℂ (WeylIndex (D.X D.m) D.columnCount → ℂ) D.borderU).restrict
      (p := AlgForm (D.InitIndex D.m ⊕ Unit) D.columnCount (D.lastEntry D.m))
      (q := AlgForm (D.Y D.m) D.columnsY (D.lastEntry D.m)) (by
    rintro ψ ⟨smooth, equivariant⟩
    refine ⟨?_, fun γ g ↦ ?_⟩
    · -- the stabiliser contains the preimage under `borderU` of the open stabiliser of `ψ`
      have cont : Continuous D.borderU := by
        refine (Matrix.unitaryGroupOf.isClosedEmbedding_val isUnit_one).continuous_iff.2
            (.matrix_reindex ?_ ..)
        -- each entry of `diag (g, 1)` is a constant or an entry of `g`
        simp only [U.sum, MonoidHom.inl_apply, MonoidHom.codRestrict_apply, MonoidHom.coe_comp,
          MonoidHom.coe_prodMap, Function.comp_apply, val_blockGL_apply]
        fun_prop
      exact ((rightStabilizer ψ).comap D.borderU).isOpen_mono (fun _ hk ↦ by simp [hk _])
        (smooth.preimage cont)
    -- `branching` intertwines the action of `diag (γ, 1)` with that of `γ`
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compLeft_apply,
      LinearMap.funLeft_apply, map_mul, mulVecBilin_apply, stdSpace_weightRep_apply, mulVec_mulVec]
    let ε := D.lastIndexEquiv.sumCongr (Equiv.refl Unit)
    have h_block : D.borderU ((stdSpace D.E (D.Y D.m)).embFin γ) =
        (stdSpace D.E (D.InitIndex D.m ⊕ Unit)).embFin (U.block ε (γ, 1)) :=
      block_embFin ε γ
    rw [h_block]
    refine (congrArg (D.branching.map (↑) *ᵥ ·)
      (equivariant (U.block ε (γ, 1)) (D.borderU g))).trans ?_
    refine (congrArg (D.branching.map (↑) *ᵥ ·)
      (stdSpace_weightRep_apply (γ := U.block ε (γ, 1)) (v := ψ (D.borderU g)))).trans ?_
    rw [mulVec_mulVec, D.isBranchingMap_branching.mul_weylRep _ _ 1, Finset.prod_eq_one,
      one_smul] <;>
      simp [← ext_iff, GL.blockScalar, ε])

end New.Data

end ColumnDefs

namespace New.Data

/-!
## Kernels of the lifts of source forms, translated data and combinations of chains

* `New.Data.liftKernel`: the kernel of lift j + 1, built from `New.thetaKernel`.
* `New.Data.Translations`, `New.Data.translateDatum`: tuples of translations, and the translated
  vacua they define.
* `New.Data.restrictedChain`: a combination of chains with such data, restricted to `Y_m`.
-/

section LiftKernelDefs

variable {P : Parameters} {D : Data P} (ϑ : D.TameChar) (j : ℕ)

/-- The column numbers `D.columnCount` and determinant exponents `D.lastEntry j` form a lift weight
(`IsLiftWeight`) from `X_j = D.X j` to `X_{j+1}` along the exponent ⌊n_{j+1} / 2⌋ - κ_{j+1}. That
is, n_j < n_{j+1}, and no column has a height strictly between n_j and n_{j+1}. Also,
`D.lastEntry j τ` is this exponent plus the number of columns of height n_j at `τ`. -/
lemma isLiftWeight_columnCount (j : ℕ) : IsLiftWeight (D.X j) (D.X (j + 1)) D.columnCount
    (fun τ : D.Φ ↦ (Fintype.card (D.X (j + 1)) / 2 : ℕ) - D.liftWeight (j + 1) τ)
      (D.lastEntry j) := by
  have h_rank : Fintype.card (D.X j) < Fintype.card (D.X (j + 1)) := by grind [card_X, n_succ]
  refine ⟨fun τ ↦ ⟨h_rank.le, fun u hu ↦ D.columnCount_eq_zero_of_mem_Ioo j τ ?_⟩, h_rank,
    funext fun τ ↦ ?_⟩
  · simpa only [rankAt, card_X] using hu
  · rw [lastEntry_eq, card_X, card_X, Int.natCast_ediv, Nat.cast_ofNat]

/-- The hermitian space Hom(X_j, X_{j+1}) of the standard definite spaces on the index sets X_j
and X_{j+1}. -/
abbrev homX : Space D.E (D.X (j + 1) × D.X j) (homSigns 1 1) :=
  (stdSpace D.E (D.X j)).hom (stdSpace D.E (D.X (j + 1)))

/-- The theta kernel of lift j + 1, for a character ϑ of U(1)(𝔸) of weight 0 with given tame part
(`New.Data.TameChar`). It goes from forms on X_j to forms on X_{j+1}, and its level on X_j is
`D.levelX j`. Its two characters are the twists `New.rankTwist`, by the ranks of X_j and X_{j+1}, of
`D.chainChar ϑ (j + 1)`, the product of `D.untwistedLiftChar (j + 1)` and ϑ^{j+1}. Derivatives are
scaled by π_M times the period `P.jetScale D.towerExp`, where π_M is the conjugate of the integer
`D.piMBar` of K of norm `D.M`. -/
@[simps! -isSimp ω]
def liftKernel :
    Kernel (D.X j) (D.X (j + 1)) D.columnCount (D.lastEntry j) (D.lastEntry (j + 1))
      (D.levelX j)
      (D.homX j).finitePart := by
  -- Both characters are twists of `chainChar ϑ (j + 1)`, whose weight is
  -- `-D.liftWeight (j + 1)`; the twist by the rank `n_j` raises this weight to `lastEntry (j + 1)`.
  obtain weight :
      (D.chainChar ϑ j.succ).HasWeight (-D.liftWeight j.succ ·)
        (D.liftTamePart (ϑ.pow j.succ) j.succ) :=
    D.hasWeight_liftChar
  exact thetaKernel (D.isLiftWeight_columnCount j) (star ↑D.piMBar * P.jetScale D.towerExp)
    ((weight.hasWeight_rankTwist (n := D.X j)).of_weight_eq (funext fun _ ↦ by
      grind [lastEntry, card_X]))
    weight.hasWeight_rankTwist (D.levelX j)

/-- Tuples (x_j) of finite adelic matrices with rows X_{j+1} and columns X_j, the translations
that define the data of a chain. -/
abbrev Translations : Type := ∀ j : ℕ, D.X (j + 1) × D.X j → 𝔸f D.E

/-- The j-th datum of the tuple x: the normalised vacuum `New.Parameters.intVacuum` of Hom(X_j,
X_{j+1}) translated by the finite Heisenberg operator of x_j. -/
def translateDatum (x : D.Translations) (j : ℕ) : (D.homX j).finitePart :=
  (D.homX j).heisenbergFinPart (x j) ⟨P.intVacuum (homX j), SMulMemClass.smul_mem _ (by simp)⟩

/-- The linear map ∑_x Ψ(x)·C_x from algebraic forms of stage 0 to stage j, where C_x is the chain
(`New.chain`) of j theta lifts with data Φ x. -/
abbrev chainCombination (Ψ : D.Translations →₀ ℂ)
    (Φ : D.Translations → ∀ i : ℕ, (D.homX i).finitePart) (j : ℕ) : D.FormX 0 →ₗ[ℂ] D.FormX j :=
  Ψ.sum fun x c ↦ c • chain (D.liftKernel ϑ) (Φ x) j

/-- The combination `Ψ` of the chains of `m` lifts whose data are translates of the integral vacuum,
followed by the restriction to `Y_m`. The composite lift of a chain datum has this form, with `Ψ`
obtained by expanding its glued tensor (`IsChainDatum.exists_isWeakChainDatum_compositeLift_eq`). -/
def restrictedChain (Ψ : D.Translations →₀ ℂ) :
    D.SourceForm →ₗ[ℂ] AlgForm (E := D.E) (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
  D.restrictToY ∘ₗ chainCombination ϑ Ψ D.translateDatum D.m ∘ₗ D.SourceForm.subtype

variable (D) in
/-- The number of lifts satisfies m = 2ϱ + 2, where ϱ = `New.Data.ϱ` is ⌊m/2⌋ − 1 truncated at
zero; so m is even and at least 2. -/
@[grind! .]
lemma m_eq_two_mul_varrho_add_two : D.m = 2 * D.ϱ + 2 := by grind [ϱ]

end LiftKernelDefs

/-!
## Chain data

A chain datum is a finitely supported function `Ψ` on tuples of translations, with conditions on
denominators, integrality and size, whose glued tensor `Glue φ♭` is jointly invariant. Here `φ♭` is
the combination `Ψ` of translates of the integral vacuum, and `Glue` applies to each double lift a
sum of translates with simple poles above `N` (`gluedDoubleLiftDatum`).
-/

section GoodDatumDefs

open Seesaw Space
open scoped TensorProduct

variable {P : Parameters} {D : Data P} (ϑ : D.Twist)

/-- The gluing for the double lift `X_{2i} → X_{2i+1} → X_{2i+2}`: the sum `doubleLiftGluing` of the
translates of `v (2 i) ⊗ v (2 i + 1)`, with simple poles at the places `w ∣ π` in the first factor
and at their conjugates in the second. -/
noncomputable def gluedDoubleLiftDatum (v : ∀ j : ℕ, (D.homX j).finitePart) (i : ℕ) :
    (D.homX (2 * i)).finitePart ⊗[ℂ] (D.homX (2 * i + 1)).finitePart :=
  doubleLiftGluing (D.InitIndex (2 * i)) (D.X (2 * i + 1)) D.piNPlaces D.N
    (D.InitIndex (2 * i + 1 + 1))
    (v (2 * i) ⊗ₜ v (2 * i + 1))

/-- The tuples of translations that become integral at all places prime to `q` after multiplication
by the conjugate of `D.piM`. -/
def admissibleTranslations (q : ℕ) : Set D.Translations :=
  {t : D.Translations | ∀ j : ℕ, t j ∈ translations (D.X (j + 1) × D.X j) q (star ↑D.piM)}

/-- Tensors of finite data for the chain `X_0 → ⋯ → X_m`, grouped by double lifts. -/
abbrev ChainTensor (D : Data P) : Type :=
  TensorChain (fun i : ℕ ↦ (D.homX (2 * i)).finitePart ⊗[ℂ] (D.homX (2 * i + 1)).finitePart)
    (D.ϱ + 1)

/-- A tensor is jointly invariant if the levels of `X_0, …, X_{m-1}` fix it under the Weil actions
for `ϑ`, with the identity on `X_m`. -/
def ChainTensor.IsInvariant (ϑ : D.TameChar) (w : D.ChainTensor) : Prop :=
  ∀ b : ∀ j : ℕ, D.levelX j, b (2 * D.ϱ + 2) = 1 →
    TensorChain.map (twoKernelAction (D.liftKernel ϑ) fun j : ℕ ↦ b j) (D.ϱ + 1) w = w

variable (D) in
/-- The tensor of the translates of the integral vacuum by `t`, glued in each double lift. -/
noncomputable def gluedVacuum (t : D.Translations) : D.ChainTensor :=
  TensorChain.pure (D.gluedDoubleLiftDatum (D.translateDatum t)) (D.ϱ + 1)

/-- The tensor `φ♭ = ∑ x, Ψ x • ⊗ⱼ translateDatum x j`. -/
noncomputable def plainTensor (Ψ : D.Translations →₀ ℂ) : D.ChainTensor :=
  Ψ.sum fun (x : D.Translations) (c : ℂ) ↦ c • TensorChain.pure
    (fun i : ℕ ↦ D.translateDatum x (2 * i) ⊗ₜ D.translateDatum x (2 * i + 1)) (D.ϱ + 1)

/-- The glued tensor `φ^ch = Glue φ♭`, with `Glue` applied to each term of `φ♭`. -/
noncomputable def gluedTensor (Ψ : D.Translations →₀ ℂ) : D.ChainTensor :=
  Ψ.sum fun (x : D.Translations) (c : ℂ) ↦ c • D.gluedVacuum x

/-- The tuples of translations that vanish at all places prime to `q`. -/
def supportedTranslations (q : ℕ) : Set D.Translations :=
  {t | ∀ (j : ℕ) (i : D.X (j + 1) × D.X j) (w : FinPlace D.E), ↑q ∉ w.asIdeal → t j i w = 0}

/-- `Ψ` is a chain datum for the twist `ϑ`, a character of weight 0 whose tame part is non-trivial
exactly at the places of the finite set `ϑ.Q`. Let `q` be the product of their norms and `M` the
principal level `D.M`. The translations in the support of `Ψ` vanish at the places prime to `M q`
and lie in `admissibleTranslations q`; the values of `Ψ` are integral away from `q`, with
denominator `1`; if `ϑ.Q` is empty, then `∑ x, |σ (Ψ x)| ≤ M ^ (3 f m n_m²)` for every automorphism
`σ` of `ℂ`; and the glued tensor is jointly invariant. -/
structure IsChainDatum (Ψ : D.Translations →₀ ℂ) : Prop extends IsAdmissibleCoeffs
    (D.admissibleTranslations ϑ.normQ ∩ D.supportedTranslations (D.M * ϑ.normQ))
    ϑ.normQ 1 (ϑ.Q = ∅) (D.M ^ (3 * D.f * D.m * D.n D.m ^ 2)) Ψ where
  /-- The glued tensor is jointly invariant. -/
  isInvariant : (gluedTensor Ψ).IsInvariant ϑ

/-- The translations in the support of a chain datum for `ϑ` are admissible for the norm of its
set `Q` of places: times the conjugate of `D.piM` they are integral away from that norm. -/
lemma IsChainDatum.mem_admissibleTranslations {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
    (hΨ : IsChainDatum ϑ Ψ) {x : D.Translations} (hx : x ∈ Ψ.support) :
    x ∈ D.admissibleTranslations ϑ.normQ :=
  Set.inter_subset_left (hΨ.support_subset x hx)

/-- The restriction map `restrictToY` on forms on `X_l`, for a number `l` equal to `m`. -/
noncomputable def restrictToYOfEq {l : ℕ} (hl : D.m = l) :
    D.FormX l →ₗ[ℂ] AlgForm (E := D.E) (D.Y D.m) D.columnsY (D.lastEntry D.m) := by
  subst hl
  exact D.restrictToY

/-- At `F l` with `l = m`, the map `restrictToYOfEq` takes the value `restrictToY (F m)`. -/
lemma restrictToYOfEq_apply {l : ℕ} (hl : D.m = l) (F : ∀ j : ℕ, D.FormX j) :
    restrictToYOfEq hl (F l) = D.restrictToY (F D.m) := by
  subst hl
  rfl

/-- The chain of double lifts of a form on `X_0`, as a linear function of the tensor of data. -/
noncomputable abbrev chainOfTensor (ϑ : D.TameChar) (φ : D.FormX 0) :
    D.ChainTensor →ₗ[ℂ] D.FormX (2 * D.ϱ + 2) :=
  TensorChain.lift (TensorChain.liftInPairs fun j : ℕ ↦ (D.liftKernel ϑ j).lift) φ (D.ϱ + 1)

/-- The composite lift: the chain of double lifts with the glued tensor of `Ψ` as data, followed by
the restriction of forms from `X_m` to `Y_m`. -/
noncomputable def compositeLift (ϑ : D.TameChar) (Ψ : D.Translations →₀ ℂ) (φ : D.SourceForm) :
    AlgForm (E := D.E) (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
  restrictToYOfEq D.m_eq_two_mul_varrho_add_two (chainOfTensor ϑ φ (gluedTensor Ψ))

/-- A weak chain datum: the coefficients `Ψ` of a jointly invariant sum of translates of the
integral vacuum. The conditions are those of a chain datum, but there is no gluing, the translations
need not vanish anywhere and may have denominators above `N`, and the size is at most
`exp (D.x ^ 60)` if `ϑ.Q` is empty. For a chain datum, both `φ♭` and the expansion of `Glue φ♭` have
this form. -/
structure IsWeakChainDatum (Ψ : D.Translations →₀ ℂ) : Prop extends
    IsAdmissibleCoeffs (D.admissibleTranslations (ϑ.normQ * D.N)) ϑ.normQ 1 (ϑ.Q = ∅)
      (Real.exp (D.x ^ 60)) Ψ where
  /-- The tensor `∑ x, Ψ x • ⊗ⱼ translateDatum x j` is jointly invariant. -/
  isJointlyInvariant : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support
    (fun x : D.Translations ↦ Ψ x • .id) D.translateDatum

end GoodDatumDefs

end New.Data

end
