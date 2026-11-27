module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import New.OneLift.ComparisonOperator.DeterminantProducts
public import New.OneLift.ComparisonOperator.GluedLattices
public import Lib.General.LinearAlgebra.MinorProducts
import Lib.PadicComparison.Descent.TestCategory
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
public import New.UpperBound.Kernels.DefiniteKernelSize
import Lib.GLn.SchurModule.SchurNorm
import Lib.General.LinearAlgebra.MatrixNormBounds
import New.Determinant.Twist.FitTwists
import New.UpperBound.Kernels.ThetaLiftGauge
import New.UpperBound.Size.Estimates

section
/-!
# The polynomial map ζ, the datum Ψ^add and the series Υ; norm, degree and denominator of ζ

Fix admissible data `D`, a tame character `ϑ` and an index `1 ≤ j ≤ m`. Write `E^n` for the standard
definite space of rank `n`, V″ for the one on `New.Data.FirstFactorIndex` and
W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m} for the one on `New.Data.AddedIndex`. Throughout, k = `D.k`,
m = `D.m`, M = `D.M`, and W_j is the space on `D.RowIndex` with r₊ = `D.posRank j` = k + j − 1 plus
signs. This file defines the constant rows 𝖼, the datum Ψ^add and the series Υ, which is built from
theta kernels of definite spaces. It also defines the polynomial map ζ to the Weyl module of μ⁺ with
P_V = P_{ζ(z)}(X). Here P_V has one determinant det(𝖼; X z) for each column of μ⁺, with variables X
in the positive basis vectors of W_j and variables z in W^add. This file bounds the norm, the degree
and the denominator of ζ.

## Main definitions and results

* `New.HasWeightNormSqLe`, `New.HasWeightNormSqLeIf`: "F has weight κ and squared norm at most b",
  outright or under a condition. Under finite products the weights add and the bounds multiply.
* `New.Data.constantRows`, `New.Data.stackedDetProdCoords`: the matrices 𝖼 of 2m constant rows, one
  for each column of μ⁺ at each infinite place (`New.Data.DetIndex`), and the coordinates of ζ.
* `New.Data.addedDatum`, `New.Data.leftSideSeries`: the datum Ψ^add on W^add and the series Υ.
* `New.Data.toPoly_stackedDetProdCoords`, `New.Data.weylNormSq_comp_eval_stackedDetProdCoords_le`:
  P_V is the polynomial of ζ, and when the entries of Y and the values of z are small, the squared
  norm of ζ(z) is bounded.
* `New.Data.exists_isHomogeneousOverEntries_smul_stackedDetProdCoords`: ζ is homogeneous of one
  degree `d`, and one integer `H ≤ (d ^ d) ^ 3` clears its denominators.

Notions from other files:
* `New.toPoly`, `New.weylNormSq`: the polynomial of a coordinate vector of weight κ, and the squared
  norm of the vector for the Gram matrix of κ. Here `κ τ h` counts the columns of height `h` at `τ`.
* `New.Data.DetIndex`: the columns of μ⁺ at the place τ. The number of those of height h < r₊ is
  `(untwistedDescentPair j).colsPlus τ h`, and Δ′ = `D.reducedHalfGap` have height r₊.
* `New.Data.FirstFactorIndex`: the indices of W_j, (E^j)⁻, E^{3m−j} and W♭ = E^{6m+1}.
* `New.Data.ChoiceIndex`: the choices, each a matrix Λ modulo ϖ² with a class h♭ of U(W♭) and rows
  for the columns of height r₊ (`New.Data.RowChoice`).
* `New.Data.TameChar`, `New.Data.twistModulus`: a character `ϑ` of U(1)(𝔸) of weight 0 with tame
  part on a finite set Q = `ϑ.Q` of places, and the moduli ϖ^c Q.

## Relation to the literature

See `New.OneLift.ComparisonOperator.FirstFactors` for related work.
-/

@[expose] public section

noncomputable section

/-! ## Norm bounds for products of semi-invariants -/

section SemiInvariantNorm

variable {Φ n : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n] [DecidableEq n]

/-- `F` is the polynomial (`toPoly`) of a coordinate vector `ξ` of weight `κ` whose squared norm for
the Gram matrix of `κ` (`weylNormSq`) is at most `b`. -/
def New.HasWeightNormSqLe (κ : Φ → ℕ → ℕ) (F : MatrixPoly (Σ _ : Φ, n) ℂ) (b : ℝ) : Prop :=
  ∃ ξ : WeylIndex n κ → ℂ, toPoly (fun _ : Φ ↦ n) κ ξ = F ∧ weylNormSq ξ ≤ b

/-- A bound on the squared norm of a coordinate vector is nonnegative. -/
lemma New.HasWeightNormSqLe.nonneg {κ : Φ → ℕ → ℕ} {F : MatrixPoly (Σ _ : Φ, n) ℂ} {b : ℝ}
    (hF : HasWeightNormSqLe κ F b) : 0 ≤ b := by
  obtain ⟨ξ, -, hξ_le⟩ := hF
  exact (weylNormSq_nonneg ξ).trans hξ_le

lemma New.HasWeightNormSqLe.one :
    HasWeightNormSqLe (0 : Φ → ℕ → ℕ) (1 : MatrixPoly (Σ _ : Φ, n) ℂ) 1 := by
  -- The coordinate vector is evaluation at `0`; its polynomial is an empty product of minors.
  have h_kernel : weylKernel (fun _ : Φ ↦ n) 0 (0 : (Σ _ : Φ, n) × ℕ → ℂ) = 1 := by
    simp [weylKernel, highestPoly, tableauPoly]
  refine ⟨weylEval (fun _ ↦ n) 0 0, by rw [toPoly_weylEval, h_kernel], ?_⟩
  simp [weylNormSq, GL.star_weylEval, h_kernel]

/-- If `F` is the polynomial of a vector of the Weyl module of weight `κ` with squared norm for the
Gram matrix at most `b` (`HasWeightNormSqLe`), and likewise `G` for `κ'` and `c`, then `F * G` has
weight `κ + κ'` and squared norm at most `b * c`. -/
lemma New.HasWeightNormSqLe.mul {κ κ' : Φ → ℕ → ℕ} {F G : MatrixPoly (Σ _ : Φ, n) ℂ} {b c : ℝ}
    (hF : HasWeightNormSqLe κ F b) (hG : HasWeightNormSqLe κ' G c) :
    HasWeightNormSqLe (κ + κ') (F * G) (b * c) := by
  obtain ⟨ξ, hξ, hξ_le⟩ := hF
  obtain ⟨η, hη, hη_le⟩ := hG
  -- The product of two semi-invariants is a semi-invariant of the sum of the weights.
  have hFG_mem : F * G ∈ nablaFamily ℂ (fun _ : Φ ↦ n) (κ + κ') := by
    rw [nablaFamily, diagramWeight_add]
    exact SetLike.mul_mem_graded (range_toPoly.le ⟨ξ, hξ⟩) (range_toPoly.le ⟨η, hη⟩)
  obtain ⟨ζ, hζ : toPoly (fun _ ↦ n) (κ + κ') ζ = F * G⟩ := range_toPoly.ge hFG_mem
  have hζ_le : weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η :=
    weylNormSq_le_mul_of_toPoly_eq (by rw [hζ, hξ, hη])
  exact ⟨ζ, hζ, hζ_le.trans
    (mul_le_mul hξ_le hη_le (weylNormSq_nonneg η) ((weylNormSq_nonneg ξ).trans hξ_le))⟩

/-- Under a finite product the weights add and the bounds on the squared norm multiply. -/
lemma New.HasWeightNormSqLe.prod {ι : Type*} {s : Finset ι} {κ : ι → Φ → ℕ → ℕ}
    {F : ι → MatrixPoly (Σ _ : Φ, n) ℂ} {b : ι → ℝ}
    (hF : ∀ i ∈ s, HasWeightNormSqLe (κ i) (F i) (b i)) :
    HasWeightNormSqLe (∑ i ∈ s, κ i) (∏ i ∈ s, F i) (∏ i ∈ s, b i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using HasWeightNormSqLe.one
  | cons i s hi ih => simpa using (hF i (by simp)).mul (ih fun j hj ↦ hF j (by simp [hj]))

/-- `F` is the polynomial of a coordinate vector `ξ` of weight `κ`, and if the condition `p` holds,
the squared norm of `ξ` is at most `b`. -/
def New.HasWeightNormSqLeIf (p : Prop) (κ : Φ → ℕ → ℕ) (F : MatrixPoly (Σ _ : Φ, n) ℂ) (b : ℝ) :
    Prop :=
  ∃ ξ : WeylIndex n κ → ℂ, toPoly (fun _ : Φ ↦ n) κ ξ = F ∧ (p → weylNormSq ξ ≤ b)

/-- `F` has weight `κ` and, under `p`, squared norm at most `b` exactly when it has weight `κ` and
squared norm at most some `c` with `c ≤ b` under `p`. -/
lemma New.hasWeightNormSqLeIf_iff {p : Prop} {κ : Φ → ℕ → ℕ} {F : MatrixPoly (Σ _ : Φ, n) ℂ}
    {b : ℝ} :
    HasWeightNormSqLeIf p κ F b ↔ ∃ c : ℝ, HasWeightNormSqLe κ F c ∧ (p → c ≤ b) :=
  ⟨fun ⟨ξ, hξ, hξ_le⟩ ↦ ⟨weylNormSq ξ, ⟨ξ, hξ, le_rfl⟩, hξ_le⟩,
    fun ⟨_, ⟨ξ, hξ, hξ_le⟩, hc_le⟩ ↦ ⟨ξ, hξ, fun hp ↦ hξ_le.trans (hc_le hp)⟩⟩

/-- If each `F i` has weight `κ i` and, under `p`, squared norm at most `b i`, then the product has
weight `∑ κ i` and, under `p`, squared norm at most `∏ b i`. -/
lemma New.HasWeightNormSqLeIf.prod {p : Prop} {ι : Type*} {s : Finset ι} {κ : ι → Φ → ℕ → ℕ}
    {F : ι → MatrixPoly (Σ _ : Φ, n) ℂ} {b : ι → ℝ}
    (hF : ∀ i ∈ s, HasWeightNormSqLeIf p (κ i) (F i) (b i)) :
    HasWeightNormSqLeIf p (∑ i ∈ s, κ i) (∏ i ∈ s, F i) (∏ i ∈ s, b i) := by
  -- Each factor has an unconditional bound `c i`, and `c i ≤ b i` under `p`.
  choose! c hc hc_le using fun i hi ↦ hasWeightNormSqLeIf_iff.1 (hF i hi)
  refine hasWeightNormSqLeIf_iff.2 ⟨∏ i ∈ s, c i, HasWeightNormSqLe.prod hc, fun hp ↦ ?_⟩
  exact Finset.prod_le_prod₀ (fun i hi ↦ (hc i hi).nonneg) fun i hi ↦ hc_le i hi hp

open Matrix in
/-- For the weight with one column of height `h < card N` at `τ`, the kernel `weylKernel` at `y`
(the highest weight polynomial at `yᵀ x`) is the leading `h × h` minor of `yᵀ x` in block `τ`. -/
lemma New.eval_weylKernel_single_eq_det {N : Type} [Fintype N] (τ : Φ) {h : ℕ}
    (h_lt : h < Fintype.card N) (y x : (Σ _ : Φ, N) × ℕ → ℂ) :
    (weylKernel (fun _ : Φ ↦ N) (Pi.single τ (Pi.single h 1)) y).eval x =
      (of fun a b : Fin h ↦ ∑ u : N, y (⟨τ, u⟩, a) * x (⟨τ, u⟩, b)).det := by
  -- Of the leading minors in `highestPoly`, only the one of size `h` at `τ` has nonzero exponent.
  simp [weylKernel, highestPoly, tableauPoly, minor, det_apply, rowSubst,
    Fin.val_eq_val _ ⟨h, h_lt⟩, Pi.single_apply, ite_apply, apply_ite]

open Matrix in
/-- Let a function `F` of `h` columns be the sum, over the `h`-subsets `S` of `N`, of the minor on
`S` times the value of `F` at the unit columns on `S`. Take the weight whose diagram is one column
of height `h < card N` at the place `τ` in `Φ` and is empty at the other places; `WeylIndex` indexes
a basis of its Weyl module. Then `F` is the polynomial `toPoly ξ` = ∑ (G ξ)ᵢ bᵢ of a vector `ξ`,
where G is the Gram matrix and the bᵢ are the basis products of minors, and the squared norm
`weylNormSq ξ` = ξ* G ξ is the sum of the squared moduli of these values. -/
lemma New.exists_toPoly_single_eq {N : Type} [Fintype N] [LinearOrder N] [DecidableEq N]
    (τ : Φ) {h : ℕ} (h_lt : h < Fintype.card N) (F : Matrix N (Fin h) ℂ → ℂ)
    (h_expand : ∀ X : Matrix N (Fin h) ℂ, F X = ∑ S : Set.powersetCard N h,
      (X.submatrix (enumSubset S) id).det * F ((1 : Matrix N N ℂ).submatrix id (enumSubset S))) :
    ∃ ξ : WeylIndex N (Pi.single τ (Pi.single h 1) : Φ → ℕ → ℕ) → ℂ,
      (∀ x : (Σ _ : Φ, N) × ℕ → ℂ,
        (toPoly (fun _ : Φ ↦ N) (Pi.single τ (Pi.single h 1)) ξ).eval x =
          F (.of fun (u : N) (a : Fin h) ↦ x (⟨τ, u⟩, a))) ∧
      weylNormSq ξ = ∑ S : Set.powersetCard N h,
        ‖F ((1 : Matrix N N ℂ).submatrix id (enumSubset S))‖ ^ 2 := by
  -- `unit S` is the array of the unit columns on `S`; evaluation at it has the minor on `S` as its
  -- polynomial. The vector `ξ` combines these evaluations with the values `c S` of `F`.
  let κ : Φ → ℕ → ℕ := Pi.single τ (Pi.single h 1)
  let unit (S : Set.powersetCard N h) : (Σ _ : Φ, N) × ℕ → ℂ := fun (⟨_, u⟩, a) ↦
    if ha : a < h then (1 : Matrix N N ℂ) u (enumSubset S ⟨a, ha⟩) else 0
  have h_minor (S : Set.powersetCard N h) (x : (Σ _ : Φ, N) × ℕ → ℂ) :
      (weylKernel (fun _ ↦ N) κ (unit S)).eval x =
        ((of fun u (a : Fin h) ↦ x (⟨τ, u⟩, a)).submatrix (enumSubset S) id).det := by
    rw [eval_weylKernel_single_eq_det τ h_lt]
    simp [unit, Matrix.one_apply, Matrix.submatrix]
  let c (S : Set.powersetCard N h) : ℂ := F ((1 : Matrix N N ℂ).submatrix id (enumSubset S))
  let ξ : WeylIndex N κ → ℂ := ∑ S, c S • weylEval (fun _ ↦ N) κ (unit S)
  have h_eval (x : (Σ _ : Φ, N) × ℕ → ℂ) :
      (toPoly (fun _ ↦ N) κ ξ).eval x = F (.of fun u a ↦ x (⟨τ, u⟩, a)) := by
    rw [h_expand]
    simp [ξ, c, toPoly_weylEval, MvPolynomial.smul_eval, h_minor, mul_comm]
  refine ⟨ξ, h_eval, ?_⟩
  -- The pairing of `ξ` with evaluation at `unit S` is the value `c S` of its polynomial there.
  have h_pair (S : Set.powersetCard N h) :
      weylEval (fun _ ↦ N) κ (unit S) ⬝ᵥ (weylGram (fun _ ↦ N) κ).map (↑) *ᵥ ξ = c S := by
    simp [← GL.eval_toPoly, h_eval, c, unit, Matrix.submatrix, Matrix.one_apply]
  have h_unit (S : Set.powersetCard N h) : star (unit S) = unit S := by
    ext ⟨⟨τ', u⟩, a⟩
    simp [unit, Matrix.one_apply, apply_dite (starRingEnd ℂ), apply_ite (starRingEnd ℂ)]
  have h_star : star ξ = ∑ S, star (c S) • weylEval (fun _ ↦ N) κ (unit S) := by
    simp_rw [ξ, star_sum, star_smul, GL.star_weylEval, h_unit]
  have h_sum : star ξ ⬝ᵥ (weylGram (fun _ ↦ N) κ).map (↑) *ᵥ ξ = ∑ S, star (c S) * c S := by
    simp_rw [h_star, sum_dotProduct, smul_dotProduct, h_pair, smul_eq_mul]
  rw [weylNormSq, h_sum]
  simp [c, Complex.conj_mul', ← Complex.ofReal_pow]

open Matrix in
/-- Take the weight whose diagram is one column of height `h < card N` at the place `τ` in `Φ` and
is empty at the other places; `WeylIndex` indexes a basis of its Weyl module. The determinant of the
matrix `((0; X) | Z)`, with variables `X` in `h` columns and with columns indexed through `e`, is
the polynomial `toPoly ξ` = ∑ (G ξ)ᵢ bᵢ of a vector `ξ`, where G is the Gram matrix and the bᵢ are
the basis products of minors. The squared norm `weylNormSq ξ` = ξ* G ξ is at most the product of the
squared lengths of the columns of `Z`. -/
lemma New.exists_toPoly_eq_det_and_weylNormSq_le {a N c : Type} [Fintype a] [DecidableEq a]
    [Fintype N] [DecidableEq N] [Fintype c] (τ : Φ) {h : ℕ} (h_lt : h < Fintype.card N)
    (e : a ⊕ N ≃ Fin h ⊕ c) (Z : Matrix (a ⊕ N) c ℂ) :
    ∃ ξ : WeylIndex N (Pi.single τ (Pi.single h 1) : Φ → ℕ → ℕ) → ℂ,
      (∀ x : (Σ _ : Φ, N) × ℕ → ℂ,
        (toPoly (fun _ : Φ ↦ N) (Pi.single τ (Pi.single h 1)) ξ).eval x =
          (((fromRows 0 (of fun (u : N) (b : Fin h) ↦ x (⟨τ, u⟩, b))).fromCols Z).submatrix
            id e).det) ∧
      weylNormSq ξ ≤ ∏ b : c, ∑ x : a ⊕ N, ‖Z x b‖ ^ 2 := by
  -- Expand along the first `h` columns. Up to sign the coordinates are the complementary minors;
  -- the Cauchy–Binet formula and Hadamard's inequality bound the sum of their squared moduli.
  let _ : LinearOrder N := .lift' (Fintype.equivFin N) (Equiv.injective _)
  let one : Matrix (a ⊕ N) (a ⊕ N) ℂ := 1
  let F (X : Matrix N (Fin h) ℂ) : ℂ :=
    ((fromCols (one.submatrix id Sum.inr * X) Z).submatrix id e).det
  have h_rows (X : Matrix N (Fin h) ℂ) : one.submatrix id Sum.inr * X = fromRows 0 X := by
    ext (u | u) b <;> simp [one, Matrix.mul_apply, Matrix.one_apply]
  have h_unit (S : Set.powersetCard N h) :
      one.submatrix id Sum.inr * (1 : Matrix N N ℂ).submatrix id (enumSubset S) =
        one.submatrix id (Sum.inr ∘ enumSubset S) := by
    ext
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h_expand (X : Matrix N (Fin h) ℂ) : F X = ∑ S : Set.powersetCard N h,
      (X.submatrix (enumSubset S) id).det *
        F ((1 : Matrix N N ℂ).submatrix id (enumSubset S)) := by
    simp only [F, h_unit]
    exact det_fromCols_eq_sum_minors e Sum.inr X Z
  obtain ⟨ξ, h_eval, h_norm⟩ := exists_toPoly_single_eq τ h_lt F h_expand
  refine ⟨ξ, fun x ↦ by simp only [h_eval, F, h_rows], ?_⟩
  calc weylNormSq ξ = ∑ S : Set.powersetCard N h,
        ‖((fromCols (one.submatrix id (Sum.inr ∘ enumSubset S)) Z).submatrix id e).det‖ ^ 2 := by
        simp only [h_norm, F, h_unit]
    _ ≤ ∏ b, ∑ x, ‖Z x b‖ ^ 2 := sum_norm_det_fromCols_sq_le e .inr Z

end SemiInvariantNorm

namespace New.Data

/-!
## Index sets, constant rows, datum and series

`modKernelStdSpace S a b 𝔪 Ψ P` is the theta kernel of a space `S` and a standard definite space,
with characters `a`, `b`, a function `Ψ` on matrices modulo `𝔪` and a polynomial `P`.
`New.stdClassSum K` is the class sum of level `K` on a standard definite space. `New.inclMatrix` is
the matrix of a map of index sets.
-/

section LineDefs

open Matrix Rows WeilData Fintype U Sum Equiv

variable {P : Parameters} {D : Data P} (ϑ : D.TameChar) (j : D.LiftIndex)

/-- The chosen representative h♭ in U(W♭)(𝔸_f) of the class in `i`. -/
abbrev RowChoice.classRep (i : D.RowChoice) : Gf D.E D.FlatIndex := i.1.out

/-- The row indices chosen in `i`: `i.rows τ k` is the k-th list of 2m rows at the place τ. -/
abbrev RowChoice.rows (i : D.RowChoice) :
    D.Φ → Fin D.reducedHalfGap → Fin (2 * D.m) → D.FlatIndex := i.2

/-- The matrix Λ modulo ϖ² of the choice `i`. -/
abbrev ChoiceIndex.matrix {j : D.LiftIndex} (i : ChoiceIndex j) :
    Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing := i.1

/-- The class h♭ and the rows of the choice `i`. -/
abbrev ChoiceIndex.rowChoice {j : D.LiftIndex} (i : ChoiceIndex j) : D.RowChoice := i.2

/-- The index set of the definite space W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m}, with W♭ = E^{6m+1}. -/
abbrev AddedIndex : Type := Fin (2 * D.m + (D.m - j)) ⊕ D.FlatIndex ⊕ D.CarrierIndex

/-- The two groupings of the summands of W: as W_j ⊕ (E^j)⁻ ⊕ W^add, and as E^{3m} ⊕ W′, where
E^{3m} is on `D.CarrierIndex` and W′ = W_j ⊕ (E^j)⁻ ⊕ E^{3m−j} ⊕ W♭ is on `D.FirstFactorIndex j`. -/
def regroupEquiv : D.RowIndex ⊕ Fin j ⊕ AddedIndex j ≃ D.CarrierIndex ⊕ FirstFactorIndex j :=
  -- the inverse moves `D.CarrierIndex` to the end and reassociates
  ((sumComm ..).trans ((sumAssoc ..).trans
    ((sumAssoc ..).trans (sumCongr (Equiv.refl D.RowIndex) (sumAssoc ..))))).symm

/-- A bijection, chosen from equality of cardinalities, from 2m indices together with those of V″
to `D.posRank j = k + j − 1` indices together with those of W^add. -/
def posEquiv : Fin (2 * D.m) ⊕ FirstFactorIndex j ≃ Fin (D.posRank j) ⊕ AddedIndex j :=
  equivOfCardEq <| by
    -- `↓` counts `D.RowIndex` as a whole; what is left is `D.r + j = D.posRank j + D.m`
    simp [↓card_rowIndex]
    grind

/-- The constant rows: a matrix 𝖼 with 2m rows for each column of μ⁺ at the place τ
(`DetIndex j τ`). Its columns are the r₊ = `D.posRank j` positive indices of W_j and the indices of
W^add. For a column of height h < r₊, row a is the basis vector of W_j at the positive index h + a
if h + a < r₊, and the basis vector number a of E^{3m−j} otherwise. For the l-th column of height
r₊, the rows are the rows `i.rows τ l` of τ(Y), placed in the columns of W♭. -/
def constantRows (i : D.RowChoice) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (τ : NumberField.InfinitePlace D.E) :
    DetIndex j τ → Matrix (Fin (2 * D.m)) (Fin (D.posRank j) ⊕ AddedIndex j) ℂ :=
  (fun h ↦ (inclMatrix ℂ fun a : Fin (2 * D.m) ↦
      if ha : (h.1 + a : ℕ) < D.posRank j then Sum.inl ⟨h.1 + a, ha⟩
      else inr (Sum.inl (a.castAdd (D.m - j))))ᵀ) ⊕ᵥ
    fun k : Fin D.reducedHalfGap ↦
      fromCols 0 (fromCols 0 (fromCols ((Y.map (Φ τ)).submatrix (i.rows τ k) id) 0))

/-- The polynomial map ζ: the coordinates, in the columns X at the positive indices of W_j
(`firstColsCoord`), of the product P_V of the determinants det(𝖼; X z), with 𝖼 from
`constantRows j i Y` and the rows of variables indexed by V″. Here `firstColsCoord` reads P_V as a
polynomial in X with coefficients in z (`inFirstCols`) and takes its coordinate at a basis index of
weight μ⁺ (`WeylIndexFamily`). So each coordinate is a polynomial in the variables z in the columns
of W^add. -/
abbrev stackedDetProdCoords (i : D.RowChoice) (Y : Matrix D.FlatIndex D.FlatIndex D.E) :
    WeylIndexFamily (fun _ : NumberField.InfinitePlace D.E ↦ FirstFactorIndex j)
      (untwistedDescentPair j).colsPlus →
      MvPolynomial (NumberField.InfinitePlace D.E × FirstFactorIndex j × AddedIndex j) ℂ :=
  firstColsCoord (untwistedDescentPair j).colsPlus
    (stackedDetProd (posEquiv j) (constantRows j i Y))

/-- The reduction homomorphism O_E/ϖ²Q → O_E/ϖ², where ϖ is the product of the chosen places and Q
the product of the places in `ϑ.Q`. -/
abbrev forgetTwist : (D.twistModulus ϑ 2).ResidueRing →+* (D.untwistedModulus 2).ResidueRing :=
  reduceToChosenModulusSq

/-- The datum Ψ^add on matrices `z` modulo ϖ²Q with columns in W^add, for the matrix Λ = `u` modulo
ϖ² (`D.untwistedModulus 2`, ϖ the product of the chosen places). It is `0` unless
the columns on E^{3m−j} and W♭ are those of the identity matrix on `FirstFactorIndex j`. In that
case it is ψ_Λ^inv(z′), the sum over `g` in GL_{3m}(O_E/ϖ²) of ψ_Λ (`New.Rows.traceChar u`,
y ↦ ψ(tr(y Λ)) for a primitive additive character ψ) at z′ g, where z′ consists of the columns on
E^{3m} modulo ϖ². -/
def addedDatum (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
    (z : Matrix (FirstFactorIndex j) (AddedIndex j) (D.twistModulus ϑ 2).ResidueRing) : ℂ :=
  if z.submatrix id (Sum.map id Sum.inl) = inclMatrix (D.twistModulus ϑ 2).ResidueRing
    (.map (inr ∘ inr) id)
    then
    ∑ g : GL D.CarrierIndex _, traceChar u (z.toCols₂.toCols₂.map (forgetTwist ϑ) * g.val)
  else 0

/-- The coordinate l of the series Υ at h, for the choice `i`: the kernel of ((E^j)⁻, V″)
at (1, h), whose datum is the indicator of the columns of the identity matrix, times the class sum
over h′ in U(E^{3m}) of 𝖺(h′) χ′(h′) 𝖪[ζ_l]((1, h♭, h′), h). Here 𝖺χ′ is `New.Rows.carrierCoeff` at
the character χ′ = χ^j ϑ (`twistedChiMPow`), a class sum of theta kernels of (E^m, E^{3m}). 𝖪 is the
kernel of (W^add, V″) with both characters ν″ = `firstFactorChar` and the datum Ψ^add =
`New.Data.addedDatum` for the matrix Λ of `i`, and ζ = `New.Data.stackedDetProdCoords` is formed
with the short basis `D.shortRows` at the class h♭ of `i`. The first kernel has characters
`upsilonU1 ^ j` (υ on the norm-one ideles) and ν″, and `blockSumOne` forms the block diagonal point
(1, h♭, h′). -/
def leftSideSeries (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j))
    (l : WeylIndexFamily (fun _ : NumberField.InfinitePlace D.E ↦ FirstFactorIndex j)
      (untwistedDescentPair j).colsPlus) : ℂ :=
  modKernelStdSpace (stdSpace D.E (Fin j)).neg (upsilonU1 ^ j.val) (firstFactorChar ϑ j)
    (D.twistModulus ϑ 2)
      (Pi.single (inclMatrix (D.twistModulus ϑ 2).ResidueRing (Sum.inl ∘ inr ∘ Sum.inl)) 1) 1 1 h *
    stdClassSum (stdLevel D.E D.CarrierIndex) fun c : Gf D.E D.CarrierIndex ↦
      carrierCoeff D.m (twistedChiMPow ϑ j) c *
        modKernelStdSpace (stdSpace D.E (AddedIndex j)) (firstFactorChar ϑ j) (firstFactorChar ϑ j)
          (D.twistModulus ϑ 2)
          (addedDatum ϑ j i.matrix) (stackedDetProdCoords j i.rowChoice (D.shortRows i.rowChoice) l)
          (1, blockSumOne (1, blockSumOne (i.rowChoice.classRep, c))) h

end LineDefs

/-!
## The polynomial map ζ

The polynomial P_V, which is `New.Rows.stackedDetProd` for the constant rows at `j`, `i` and `Y`, is
a product of determinants det(𝖼; X z). Each has `2 m` constant rows `𝖼` stacked over rows of
variables, one row for each index in `D.FirstFactorIndex j`.
-/

section LineCoordinates

open Matrix MvPolynomial Rows Fintype «GL» ComplexOrder Norms.L2Operator Complex Matrix.Module
open Finset hiding map

variable {P : Parameters} {D : Data P}

/-- Let μ⁺ be the diagram with `(untwistedDescentPair j).colsPlus τ h` columns of height `h` at the
infinite place `τ`, from the data of the `j`-th theta lift of `D`. The set `DetIndex j τ`, which
indexes the determinants at `τ`, has one element for each column of μ⁺: its cardinality is the sum
of the column counts over the heights below the rank `card (FirstFactorIndex j)` of V″. -/
lemma card_detIndex_eq_sum (j : D.LiftIndex) (τ : NumberField.InfinitePlace D.E) :
    Fintype.card (DetIndex j τ) =
      ∑ h ∈ range (Fintype.card (FirstFactorIndex j)), (untwistedDescentPair j).colsPlus τ h := by
  -- The weight is `D.reducedHalfGap` at the height `D.posRank j` and vanishes beyond.
  have h_lt : D.posRank j < Fintype.card (FirstFactorIndex j) := by
    grind [card_sum, Fintype.card_fin, card_rowIndex, targetParameter_eq]
  have h_zero : ∀ h ≥ D.posRank j + 1, (untwistedDescentPair j).colsPlus τ h = 0 := by
    grind [descentPair]
  have h_top : (untwistedDescentPair j).colsPlus τ (D.posRank j) = D.reducedHalfGap := by
    grind [descentPair, reducedHalfGap, targetParameter_eq]
  calc Fintype.card (DetIndex j τ)
    _ = ∑ h ∈ range (D.posRank j), (untwistedDescentPair j).colsPlus τ h + D.reducedHalfGap := by
        simp [← sum_range]
    _ = ∑ h ∈ range (D.posRank j + 1), (untwistedDescentPair j).colsPlus τ h := by
        rw [sum_range_succ, h_top]
    _ = ∑ h ∈ range (Fintype.card (FirstFactorIndex j)), (untwistedDescentPair j).colsPlus τ h :=
        (eventually_constant_sum h_zero h_lt).symm

/-- The number of determinants at the infinite place `τ` is at most `natB + offWeight + Δ + m Δ`:
`D.natB` is the weight b at the b-places as a natural number, `D.offWeight` the weight at the other
places, and Δ = `D.gap` = 2 r⁸ the gap of the data. -/
lemma card_detIndex_le (j : D.LiftIndex) (τ : NumberField.InfinitePlace D.E) :
    Fintype.card (DetIndex j τ) ≤ D.natB + D.offWeight + D.gap + D.m * D.gap := by
  -- By `card_detIndex_add_firstFactorCharExp` the count is at most the weight `D.liftWeight j τ`,
  -- and `j ≤ m`.
  have h_mul : j * D.gap ≤ D.m * D.gap := mul_le_mul_left j.property.2 D.gap
  grind [card_detIndex_add_firstFactorCharExp j τ, D.weight_le_natB_add_offWeight τ]

/-- Let `Z` have the `2 m + card (FirstFactorIndex j)` rows of a determinant det(𝖼; X z) at `j`, and
as columns the last `D.posRank j - h ≤ j` of the `D.posRank j` positive indices of W_j and the
indices `AddedIndex j` of W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m}, at most `12 m + 1` columns in all. If its
entries are at most `M ^ 4`, for the integers `m = D.m` and `M = D.M` of the data, the product of
the squared lengths of its columns is at most `(M ^ 9) ^ (12 m + 1)`. -/
lemma prod_sum_norm_sq_le_M_pow (j : D.LiftIndex) {h : ℕ} (h_rest : D.posRank j - h ≤ j)
    {Z : Matrix (Fin (2 * D.m) ⊕ FirstFactorIndex j) (Fin (D.posRank j - h) ⊕ AddedIndex j) ℂ}
    (hZ : ∀ (a : Fin (2 * D.m) ⊕ FirstFactorIndex j) (b : Fin (D.posRank j - h) ⊕ AddedIndex j),
      ‖Z a b‖ ≤ D.M ^ 4) :
    ∏ b : Fin (D.posRank j - h) ⊕ AddedIndex j,
      ∑ a : Fin (2 * D.m) ⊕ FirstFactorIndex j, ‖Z a b‖ ^ 2 ≤
      (↑(D.M ^ 9) : ℝ) ^ (12 * D.m + 1) := by
  have h_rows : card (Fin (2 * D.m) ⊕ FirstFactorIndex j) = D.r + 11 * D.m + 1 := by
    grind [card_sum, Fintype.card_fin, card_rowIndex]
  have h_cols : card (Fin (D.posRank j - h) ⊕ AddedIndex j) ≤ 12 * D.m + 1 := by
    grind [card_sum, Fintype.card_fin]
  -- Each column has squared length at most `(r + 11 m + 1) M ^ 8 ≤ M ^ 9`.
  have h_col (b : Fin (D.posRank j - h) ⊕ AddedIndex j) :
      ∑ a, ‖Z a b‖ ^ 2 ≤ (D.M ^ 9 : ℝ) := calc
    _ ≤ ∑ _a : Fin (2 * D.m) ⊕ FirstFactorIndex j, (D.M ^ 4 : ℝ) ^ 2 :=
        sum_le_sum fun a _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hZ a b) 2
    _ = (D.r + 11 * D.m + 1 : ℕ) * (D.M ^ 4 : ℝ) ^ 2 := by
        rw [sum_const, card_univ, h_rows, nsmul_eq_mul]
    _ ≤ D.M ^ 9 := D.le_of_hasLogBound
  refine (prod_le_prod₀ (fun b _ ↦ by positivity) fun b _ ↦ h_col b).trans ?_
  simpa using pow_le_pow_right₀ (D.le_of_hasLogBound : (1 : ℝ) ≤ D.M ^ 9) h_cols

/-- The entries that a specialisation by `z` and `φ` puts into the determinants have norm at most
`M ^ 4`, where `M = D.M`. -/
structure IsSmallSpecialization (j : D.LiftIndex) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (φ : ℂ →+* ℂ) (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) : Prop where
  /-- `φ` of every conjugate of an entry of `Y` has norm at most `M ^ 4`. -/
  norm_entry_le (τ : D.Φ) (a b : D.FlatIndex) : ‖φ (Φ τ (Y a b))‖ ≤ D.M ^ 4
  /-- `φ` of every value of `z` has norm at most `M ^ 4`. -/
  norm_value_le (x : D.Φ × FirstFactorIndex j × AddedIndex j) : ‖φ (z x)‖ ≤ D.M ^ 4

/-- Let `l` be a column of μ⁺ and `h` its height. The factor `stackedDet` for `l` is the determinant
of the constant rows `constantRows j i Y τ l` stacked over rows of variables, with `posEquiv j`
matching rows and columns; `inFirstCols` reads it as a polynomial in the first r₊ columns X with
coefficients in the others, z. Specialised by `z` and `φ`, it is the polynomial of a vector whose
weight is one column of height `h` at `τ`, and the squared norm of this vector is at most
`(M ^ 9) ^ (12 m + 1)` if the values of `φ` at the conjugates of the entries of `Y` and at the
values of `z` are at most `M ^ 4`. -/
lemma hasWeightNormSqLeIf_stackedDet (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) (φ : ℂ →+* ℂ)
    (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) (τ : D.Φ) (l : DetIndex j τ) {h : ℕ}
    (h_height : Sum.elim
      (fun x : Σ a : Fin (D.posRank j), Fin ((untwistedDescentPair j).colsPlus τ a) ↦ (x.fst : ℕ))
      (fun _ : Fin D.reducedHalfGap ↦ D.posRank j) l = h) :
    HasWeightNormSqLeIf (n := FirstFactorIndex j) (IsSmallSpecialization j Y φ z)
      (Pi.single τ (Pi.single h 1))
      (.map (φ.comp (eval z)) (inFirstCols (stackedDet τ (constantRows j i Y τ l) (posEquiv j))))
      (↑(D.M ^ 9) ^ (12 * D.m + 1)) := by
  classical
  -- Clear the columns of `X` after the first `h` by their unit rows, and apply
  -- `exists_toPoly_eq_det_and_weylNormSq_le` to the cleared matrix.
  have h_le : h ≤ D.posRank j := by cases l <;> grind [descentPair]
  have h_rest : D.posRank j - h ≤ j := by
    cases l <;> grind [Fin, Sigma, descentPair, targetParameter_eq]
  have h_lt : h < card (FirstFactorIndex j) := by
    grind [card_sum, Fintype.card_fin, card_rowIndex, targetParameter_eq]
  -- `colSplit` splits off the first `h` columns; `Z` is the rest after clearing.
  let firstCols : Fin (D.posRank j) ≃ Fin h ⊕ Fin (D.posRank j - h) :=
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h_le))).symm
  let colSplit : Fin (D.posRank j) ⊕ AddedIndex j ≃ Fin h ⊕ Fin (D.posRank j - h) ⊕ AddedIndex j :=
    (firstCols.sumCongr (.refl _)).trans (.sumAssoc ..)
  let Z : Matrix (Fin (2 * D.m) ⊕ FirstFactorIndex j) (Fin (D.posRank j - h) ⊕ AddedIndex j) ℂ :=
    of fun a b ↦
      φ ((constantRows j i Y τ l).fromRows (fromCols 0 (of fun u c ↦ z (τ, u, c))) a
        (colSplit.symm (.inr b)))
  have h_clear (x : (Σ _ : D.Φ, FirstFactorIndex j) × ℕ → ℂ) :
      eval x (MvPolynomial.map (φ.comp (eval z))
        (inFirstCols (stackedDet τ (constantRows j i Y τ l) (posEquiv j)))) =
      (((fromRows 0 (of fun u (c : Fin h) ↦ x (⟨τ, u⟩, c))).fromCols Z).submatrix id
        ((posEquiv j).trans colSplit)).det := by
    simp only [stackedDet, constantRows, inclMatrix, transpose_submatrix, transpose_one,
      AlgHom.map_det, AlgHom.mapMatrix_apply, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_map, Equiv.coe_trans]
    -- The two matrices differ by the unipotent factor (1 0; T 1), where T holds the cleared
    -- variables: it adds multiples of the upper rows.
    let T : Matrix (FirstFactorIndex j) (Fin (2 * D.m)) ℂ :=
      of fun u a ↦ if h + a < D.posRank j then x (⟨τ, u⟩, h + a) else 0
    refine det_eq_of_eq_det_one_mul (fromBlocks 1 0 T 1) (by simp)
      (ext fun a ↦ ((posEquiv j).trans colSplit).forall_congr_left.mpr ?_)
    -- in a cleared column the sum over the upper rows has a single nonzero term
    have h_single (u : FirstFactorIndex j) (b : Fin (D.posRank j - h)) :
        ∑ a : Fin (2 * D.m), (if h + a < D.posRank j then
          if (a : ℕ) = b then x (⟨τ, u⟩, h + b) else 0 else 0) = x (⟨τ, u⟩, h + b) := by
      have hb_lt : (b : ℕ) < 2 * D.m := by grind
      have hb_pos : h + b < D.posRank j := by lia
      rw [Fintype.sum_eq_single ⟨b, hb_lt⟩]
      · simp [hb_pos]
      · intro a ha
        simp [Fin.val_ne_of_ne ha]
    -- Compare entries, by the kind of the factor and of the row.
    cases l <;> cases a
    all_goals
      simp [T, Z, Matrix.one_apply, ↓ Matrix.mul_apply, ↓ constantRows, ↓ inclMatrix,
        fromCols_map] at h_height ⊢
      simp +contextual [colSplit, firstCols, inFirstCols, h_height, Fin.cast, h_single]
    · -- an upper row vanishes in the first `h` columns
      lia
    · -- if `h = posRank j` there is no cleared column
      lia
  obtain ⟨ξ, h_eval, h_norm⟩ := exists_toPoly_eq_det_and_weylNormSq_le τ h_lt
    ((posEquiv j).trans colSplit) Z
  refine ⟨ξ, funext fun x ↦ by rw [h_eval, h_clear], ?_⟩
  rintro ⟨hY_small, hz_small⟩
  have hZ : ∀ a b, ‖Z a b‖ ≤ D.M ^ 4 := by
    -- Each entry is `0`, `1`, an entry of `Y` or a value of `z`.
    cases l <;> simp [Z, colSplit, firstCols, apply_ite, hY_small, hz_small, NeZero.one_le,
      one_le_pow₀, ↓ constantRows, ↓ inclMatrix, Matrix.one_apply, ↓ ite_apply]
  exact h_norm.trans (prod_sum_norm_sq_le_M_pow j h_rest hZ)

/-- At the `j`-th lift, take the product of the determinants of the constant rows
`constantRows j i Y` stacked over variables with rows `FirstFactorIndex j`, as a polynomial in the
first `D.posRank j` columns. Specialise the columns on `AddedIndex j` by `z` and apply `φ`. The
result is the polynomial of a vector of weight μ⁺, the diagram with
`(untwistedDescentPair j).colsPlus τ h` columns of height `h` at `τ`, whose squared norm is at most
`(M ^ 9) ^ ((12 m + 1) N)` if the specialised entries of `Y` and `z` are at most `M ^ 4`. Here `i`
chooses the rows of `Y`, `M = D.M`, and `N` is the total number of determinants over all places. -/
lemma hasWeightNormSqLeIf_stackedDetProd (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) (φ : ℂ →+* ℂ)
    (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) :
    HasWeightNormSqLeIf (n := FirstFactorIndex j) (IsSmallSpecialization j Y φ z)
      (untwistedDescentPair j).colsPlus
      (.map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y))))
      (↑(D.M ^ 9) ^ ((12 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ))) := by
  -- `stackedDetProd` is a product of determinants; `HasWeightNormSqLeIf.prod` adds their weights
  -- and multiplies the bounds.
  let height (τ : D.Φ) : DetIndex j τ → ℕ := Sum.elim (fun x ↦ (x.fst : ℕ)) fun _ ↦ D.posRank j
  have h_factors : HasWeightNormSqLeIf (n := FirstFactorIndex j) (IsSmallSpecialization j Y φ z)
      (∑ τ, ∑ l, Pi.single τ (Pi.single (height τ l) 1))
      (∏ τ, ∏ l,
        .map (φ.comp (eval z)) (inFirstCols (stackedDet τ (constantRows j i Y τ l) (posEquiv j))))
      (∏ τ : D.Φ, ∏ _l : DetIndex j τ, ↑(D.M ^ 9) ^ (12 * D.m + 1)) :=
    .prod fun τ _ ↦ .prod fun l _ ↦ hasWeightNormSqLeIf_stackedDet j i Y φ z τ l rfl
  -- The columns of all the factors together make up the diagram
  -- `(untwistedDescentPair j).colsPlus`.
  have h_weight : (∑ τ : D.Φ, ∑ l : DetIndex j τ, Pi.single τ (Pi.single (height τ l) 1)) =
      (untwistedDescentPair j).colsPlus := by
    -- Below `posRank j` a height occurs once for each such column; at `posRank j` it occurs
    -- `reducedHalfGap` times, which is the column count of the descent pair there.
    simp [height, funext_iff, Fintype.sum_sigma, sum_fin_eq_sum_range, ← mem_range,
      sum_add_distrib, Pi.single_apply]
    grind [descentPair, reducedHalfGap, targetParameter_eq]
  rw [h_weight] at h_factors
  simpa [stackedDetProd, map_prod, mul_sum, ← prod_pow_eq_pow_sum, pow_mul] using h_factors

/-- Take the product of the determinants of the constant rows `constantRows j i Y`, some of them
rows of the matrix `Y` chosen by `i`, stacked over rows of variables. Its coordinates in the first
`D.posRank j` columns of variables form the vector `stackedDetProdCoords j i Y` of polynomials in
the other columns. Give these other variables the values `z` and apply the ring map `φ`. If the
product becomes the polynomial (`toPoly`) of a vector `ξ`, then the vector of coordinates becomes
`ξ`. -/
lemma comp_eval_stackedDetProdCoords_eq_of_toPoly_eq (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) {φ : ℂ →+* ℂ}
    {z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ}
    {ξ : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ}
    (hξ : toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus ξ =
      .map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y)))) :
    φ ∘ eval z ∘ stackedDetProdCoords j i Y = ξ := by
  -- Coordinates commute with `φ` and with evaluation at `z`, and those of the polynomial of `ξ`
  -- are `ξ`.
  simp [funext_iff, firstColsCoord, map_fockPairing, MvPolynomial.map_map, ← hξ]

/-- Specialise the coordinates `stackedDetProdCoords j i Y` by values `z` for the remaining
variables and a ring map `φ`. The polynomial of the result is the specialised product of
determinants. -/
lemma toPoly_comp_eval_stackedDetProdCoords (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) (φ : ℂ →+* ℂ)
    (z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ) :
    toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus
        (φ ∘ eval z ∘ stackedDetProdCoords j i Y) =
      .map (φ.comp (eval z)) (inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y))) := by
  obtain ⟨ξ, hξ, -⟩ := hasWeightNormSqLeIf_stackedDetProd j i Y φ z
  rw [comp_eval_stackedDetProdCoords_eq_of_toPoly_eq j i Y hξ, hξ]

/-- Specialise the coordinates `stackedDetProdCoords j i Y` by values `z` for the remaining
variables and a ring map `φ`. Suppose `φ` of every image `Φ τ (Y a b)` of an entry of `Y` and of
every value `z x` has norm at most `M ^ 4`. Then the squared norm `weylNormSq` of the result is at
most `(M ^ 9) ^ ((12 m + 1) · ∑ τ, card (DetIndex j τ))`. -/
lemma weylNormSq_comp_eval_stackedDetProdCoords_le (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) {φ : ℂ →+* ℂ}
    {z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ}
    (hY_small : ∀ (τ : D.Φ) (a b : D.FlatIndex), ‖φ (Φ τ (Y a b))‖ ≤ D.M ^ 4)
    (hz_small : ∀ x : D.Φ × FirstFactorIndex j × AddedIndex j, ‖φ (z x)‖ ≤ D.M ^ 4) :
    weylNormSq (φ ∘ eval z ∘ stackedDetProdCoords j i Y) ≤
      ↑(D.M ^ 9) ^ ((12 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ)) := by
  obtain ⟨ξ, hξ, h_norm⟩ := hasWeightNormSqLeIf_stackedDetProd j i Y φ z
  rw [comp_eval_stackedDetProdCoords_eq_of_toPoly_eq j i Y hξ]
  exact h_norm ⟨hY_small, hz_small⟩

/-- Take the product of the determinants of the constant rows `constantRows j i Y`, some of them
rows of the matrix `Y` chosen by `i`, stacked over rows of variables (`stackedDetProd`). Read it as
a polynomial in the first `D.posRank j` columns of variables, with coefficients polynomials in the
other columns (`inFirstCols`). It is the polynomial (`toPoly`) of its vector of coordinates
`stackedDetProdCoords j i Y`, of weight `(untwistedDescentPair j).colsPlus`. -/
lemma toPoly_stackedDetProdCoords (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) :
    toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus
      (stackedDetProdCoords j i Y) =
      inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y)) := by
  -- Compare coefficients at every point `z`, using `toPoly_comp_eval_stackedDetProdCoords` for the
  -- identity of `ℂ`.
  refine MvPolynomial.ext _ _ fun d ↦ MvPolynomial.funext fun z ↦ ?_
  have h_spec : toPoly (fun _ : D.Φ ↦ FirstFactorIndex j) (untwistedDescentPair j).colsPlus
      (eval z ∘ stackedDetProdCoords j i Y) =
      MvPolynomial.map (eval z) (inFirstCols
        (stackedDetProd (posEquiv j) (constantRows j i Y))) := by
    simpa using toPoly_comp_eval_stackedDetProdCoords j i Y (RingHom.id ℂ) z
  rw [← coeff_map, ← coeff_map, map_toPoly, h_spec]

/-- Replacing the variables `x` by `c • x` multiplies each coordinate `stackedDetProdCoords j i Y l`
at the `j`-th lift by `c ^ d` for the degree `d = ∑ τ, ∑ h, (N - h) κ(τ, h)`, where `N` is the
number of rows of variables, indexed by `FirstFactorIndex j`, and `κ` the weight
`(untwistedDescentPair j).colsPlus`. -/
lemma aeval_smul_X_stackedDetProdCoords (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus) {c : ℂ} (hc : c ≠ 0) :
    aeval (fun x : D.Φ × FirstFactorIndex j × AddedIndex j ↦ c • MvPolynomial.X x)
        (stackedDetProdCoords j i Y l) =
      c ^ (∑ τ : D.Φ, ∑ h ∈ range (card (FirstFactorIndex j)),
          (card (FirstFactorIndex j) - h) * (untwistedDescentPair j).colsPlus τ h) •
        stackedDetProdCoords j i Y l := by
  -- The product of determinants is multiplied by `c ^ (N ∑ κ(h))` and the Schur matrix of `c • 1`
  -- is the scalar `c ^ ∑ h κ(h)`; the quotient of the two is `c ^ d`.
  let κ : D.Φ → ℕ → ℕ := (untwistedDescentPair j).colsPlus
  let N : ℕ := card (FirstFactorIndex j)
  have h_schur : schur (n := fun _ ↦ FirstFactorIndex j) (n' := fun _ ↦ FirstFactorIndex j) κ
      (c • 1 : D.Φ → Matrix (FirstFactorIndex j) (FirstFactorIndex j) ℂ) =
      c ^ (∑ τ, ∑ h ∈ range N, h * κ τ h) • 1 := by
    simp [Pi.smul_def, schur_smul, prod_pow_eq_pow_sum, rankAt, N]
  have h_subst : c ^ (∑ τ, ∑ h ∈ range N, h * κ τ h) •
      aeval (fun x ↦ c • MvPolynomial.X x) (stackedDetProdCoords j i Y l) =
      c ^ (∑ τ, ∑ h ∈ range N, N * κ τ h) • stackedDetProdCoords j i Y l := by
    simpa [twoSidedSubst, h_schur, ↓ card_detIndex_eq_sum, -card_sum, prod_pow_eq_pow_sum, mul_sum,
      ← pow_mul, Matrix.one_apply, N, κ] using
      twoSidedSubst_firstColsCoord (c • 1) 1
        (twoSidedSubst_stackedDetProd (posEquiv j) (constantRows j i Y) ..) κ l
  have h_exp : ∑ τ, ∑ h ∈ range N, N * κ τ h =
      (∑ τ, ∑ h ∈ range N, h * κ τ h) + ∑ τ, ∑ h ∈ range N, (N - h) * κ τ h := by
    simp_rw [← sum_add_distrib, ← add_mul]
    exact sum_congr rfl fun τ _ ↦ sum_congr rfl fun h hh ↦ by grind
  rw [h_exp, pow_add, mul_smul] at h_subst
  exact smul_right_injective _ (pow_ne_zero _ hc) h_subst

/-- Take the product of the determinants of the constant rows `constantRows j i Y` stacked over
variables, with `posEquiv j` matching rows and columns. Read as a polynomial in the first
`D.posRank j` columns over the polynomials in the others (`inFirstCols`), it has coefficients in
every subring `A` of `ℂ` that contains all the conjugates `Φ τ (Y a b)`. -/
lemma inFirstCols_stackedDetProd_mem_range (j : D.LiftIndex) (i : D.RowChoice)
    (Y : Matrix D.FlatIndex D.FlatIndex D.E) {A : Subring ℂ}
    (hA : ∀ (τ : D.Φ) (a b : D.FlatIndex), Φ τ (Y a b) ∈ A) :
    inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y)) ∈
      (MvPolynomial.map (MvPolynomial.map A.subtype)).range := by
  suffices stackedDetProd (posEquiv j) (constantRows j i Y) ∈
      (MvPolynomial.map (MvPolynomial.map A.subtype)).range.comap inFirstCols.toRingHom from this
  refine prod_mem fun τ _ ↦ prod_mem fun k _ ↦ IsIntMatrix.det_mem fun a b ↦ ?_
  rcases a with a | a
  · -- a row of constants
    have h_entry : ∀ u : Fin (D.posRank j) ⊕ AddedIndex j, constantRows j i Y τ k a u ∈ A := by
      cases k <;> simp [apply_ite, hA, ↓ constantRows, ↓ inclMatrix, Matrix.one_apply]
    exact ⟨C (C ⟨_, h_entry (posEquiv j b)⟩), by simp [inFirstCols]⟩
  · -- a row of variables
    simp only [AlgHom.toRingHom_eq_coe, Subring.mem_comap, submatrix_apply]
    rcases posEquiv j b with b | b
    · exact ⟨MvPolynomial.X (⟨τ, a⟩, b.val), by simp [inFirstCols]⟩
    · exact ⟨C (MvPolynomial.X (τ, a, b)), by simp [inFirstCols]⟩

/-- The polynomial `Q` in the variables of the columns of W^add is homogeneous of degree `d`, and
its coefficients lie in the ring generated by the conjugates of the entries of `Y`. -/
structure IsHomogeneousOverEntries (j : D.LiftIndex) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
    (d : ℕ) (Q : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ) : Prop where
  /-- `Q` is multiplied by `c ^ d` when the variables are multiplied by `c ≠ 0`. -/
  aeval_smul_X (c : ℂ) (hc : c ≠ 0) :
    aeval (fun x : D.Φ × FirstFactorIndex j × AddedIndex j ↦ c • MvPolynomial.X x) Q = c ^ d • Q
  /-- `Q` has its coefficients in every subring of `ℂ` that contains all the `Φ τ (Y a b)`. -/
  mem_range (A : Subring ℂ) (hA : ∀ (τ : D.Φ) (a b : D.FlatIndex), Φ τ (Y a b) ∈ A) :
    Q ∈ (MvPolynomial.map A.subtype).range

/-- There are a degree `d`, at most `10 m + 1` times the number of determinants over the infinite
places `D.Φ` of the CM field `D.E`, and an integer `0 < H ≤ (d ^ d) ^ 3`, both independent of `i`
and `Y`, such that every `H • stackedDetProdCoords j i Y l` is homogeneous of degree `d` and has its
coefficients in every subring of `ℂ` that contains all the conjugates `Φ τ (Y a b)`. -/
lemma exists_isHomogeneousOverEntries_smul_stackedDetProdCoords (j : D.LiftIndex) :
    ∃ d : ℕ, d ≤ (10 * D.m + 1) * ∑ τ : D.Φ, Fintype.card (DetIndex j τ) ∧
      ∃ H : ℤ, 0 < H ∧ H ≤ (d ^ d) ^ 3 ∧
        ∀ (i : D.RowChoice) (Y : Matrix D.FlatIndex D.FlatIndex D.E)
          (l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus),
          IsHomogeneousOverEntries j Y d (H • stackedDetProdCoords j i Y l) := by
  -- Let `N` be the number of rows of variables and `κ` the weight. The degree is
  -- `d = ∑ (N - h) κ(h)`, and `H` is the hook number of the complementary diagram `h ↦ κ(N - h)`,
  -- which has at most `d` boxes.
  let N : ℕ := card (FirstFactorIndex j)
  let κ : D.Φ → ℕ → ℕ := (untwistedDescentPair j).colsPlus
  let d : ℕ := ∑ τ, ∑ h ∈ range N, (N - h) * κ τ h
  let H : ℤ := hookNumber (fun τ h ↦ κ τ (N - h)) fun _ ↦ N
  have h_factor (τ : D.Φ) (h : ℕ) : (N - h) * κ τ h ≤ (10 * D.m + 1) * κ τ h := by
    -- `N - h ≤ 10 m + 1` whenever `κ(h) ≠ 0`.
    simp only [card_sum, ↓card_rowIndex, Fintype.card_fin, N, κ]
    grind [Nat.mul_lt_mul_right, descentPair, targetParameter]
  have hd_le : d ≤ (10 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ) := by
    simp only [↓card_detIndex_eq_sum, mul_sum]
    exact sum_le_sum fun τ _ ↦ sum_le_sum fun h _ ↦ h_factor τ h
  have hH_le : H ≤ (d ^ d) ^ 3 := by
    -- Count the boxes at each place, reversing the order of summation.
    refine hookNumber_le (sum_mono fun τ ↦ ?_)
    calc
      _ ≤ ∑ h ∈ range (N + 1), h * κ τ (N - h) := by
        grw [range_mono le_self_add]
      _ = ∑ h ∈ range (N + 1), (N - h) * κ τ (N - (N - h)) := by
        rw [← sum_flip]
      _ ≤ ∑ h ∈ range N, (N - h) * κ τ h := by
        grind only [sum_range_succ]
  refine ⟨d, hd_le, H, hookNumber_pos, hH_le, fun i Y l ↦ ⟨fun c hc ↦ ?_, fun A hA ↦ ?_⟩⟩
  · -- Homogeneity.
    rw [map_zsmul, aeval_smul_X_stackedDetProdCoords j i Y l hc, smul_comm]
  · -- Integrality: the product of determinants has coefficients in `A`, hence so have its
    -- coordinates `c` in the basis of products of minors.
    obtain ⟨F, hF : map (map A.subtype) F =
        inFirstCols (stackedDetProd (posEquiv j) (constantRows j i Y))⟩ :=
      inFirstCols_stackedDetProd_mem_range j i Y hA
    have h_coord (k : WeylIndex (FirstFactorIndex j) κ) :
        (weylGramOver *ᵥ stackedDetProdCoords j i Y) k ∈ (map A.subtype).range := by
      refine coord_mem_of_coeff_mem (map A.subtype).range.toAddSubgroup 0
        (f := map (map A.subtype) F) ?_ (by simp [coeff_map]) k
      rw [hF, ← toPoly_stackedDetProdCoords j i Y, ← nablaCombination_weylGramOver_mulVec]
      simp [detPow, Fintype.linearCombination_apply, κ]
    choose c hc using h_coord
    -- Over the polynomials with coefficients in `A`, the combination with coordinates `c`, times
    -- `H`, is the polynomial of a vector `ζ`.
    obtain ⟨ζ, hζ⟩ : ∃ ζ : WeylIndex (FirstFactorIndex j) κ →
        MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) A,
        toPoly (fun _ ↦ FirstFactorIndex j) κ ζ = H • nablaCombination κ c :=
      exists_toPoly_eq_hookNumber_dual_smul (fun _ _ _ ↦ rfl) (range_nablaCombination.le ⟨c, rfl⟩)
    have h_map : map (map A.subtype) (nablaCombination κ c) =
        toPoly (fun _ ↦ FirstFactorIndex j) κ (stackedDetProdCoords j i Y) := by
      rw [← nablaCombination_weylGramOver_mulVec, ← funext hc]
      simp [Fintype.linearCombination_apply, ← C_mul']
    -- A vector is determined by its polynomial, so `ζ` maps to `H • stackedDetProdCoords`.
    have h_eq : map A.subtype ∘ ζ = H • stackedDetProdCoords j i Y :=
      toPoly_injective (by rw [← map_toPoly, hζ, map_zsmul, h_map, map_zsmul])
    exact ⟨ζ l, congrFun h_eq l⟩

end LineCoordinates

end New.Data

end
end
end

/-!
# The first factors: P_V along W_j and W^add, integrality and size

Fix admissible data `D`, a tame character `ϑ` and an index `1 ≤ j ≤ m`. Write `E^n` for
the standard definite space of rank `n`, V″ for the one on `New.Data.FirstFactorIndex` and
W^add = E^{3m−j} ⊕ W♭ ⊕ E^{3m} for the one on `New.Data.AddedIndex`. Throughout, k = `D.k`,
m = `D.m`, M = `D.M`, and W_j is the space on `D.RowIndex` with r₊ = `D.posRank j` = k + j − 1
plus signs. This file writes P_V as a sum of products of a polynomial in X and a coordinate of
ζ(z), where X are the variables in the positive basis vectors of W_j and z those in W^add. Each
value of Υ is a double class sum of products of three theta kernels of definite spaces, and this
file bounds these kernels. By `New.Data.exists_isIntegralAndSmall_leftSideSeries`, for one constant
`c″ ≠ 0` the first factors φ″, the complex conjugates of c″Υ, are integral away from the norm of Q
and, if Q is empty, all their images under automorphisms of ℂ are small
(`New.Data.IsIntegralAndSmall`).

## Main definitions and results

* `New.Data.renameRowsCols_stackedDetProd_eq_sum`: P_V as a sum of products of a polynomial in X and
  a coordinate of ζ(z).
* `New.Data.exists_isIntegralAndSmall_leftSideSeries`: for 1 ≤ j ≤ m there is one c ≠ 0, independent
  of i, ϑ and h, such that every first factor y = conj (c · Υ) is integral and small in the sense of
  `New.Data.IsIntegralAndSmall`.

Notions from other files:
* `New.toPoly`, `New.weylNormSq`: the polynomial of a coordinate vector of weight κ, and the squared
  norm of the vector for the Gram matrix of κ. Here `κ τ h` counts the columns of height `h` at `τ`.
* `New.Data.FirstFactorIndex`: the indices of W_j, (E^j)⁻, E^{3m−j} and W♭ = E^{6m+1}.
* `New.Data.TameChar`, `New.Data.twistModulus`: a character `ϑ` of U(1)(𝔸) of weight 0 with tame
  part on a finite set Q = `ϑ.Q` of places, and the moduli ϖ^c Q.
* `New.Data.stackedDetProdCoords`: the coordinates of the polynomial map ζ.
* `New.Data.leftSideSeries`: the series Υ, built from theta kernels of definite spaces.

## Relation to the literature

The first factors enter the comparison of twisted theta forms on U(W_j) with twist-free ones,
`New.Data.exists_mul_thirdExchangeLeftSide_eq_choiceFn` in
`New.OneLift.ComparisonOperator.ThreeExchanges`: for every twist, an explicit theta form times a
number is a twist-free function, and the squared modulus of the number is a constant independent of
the twist divided by a product of squared Hecke L-values and powers of norms of places. This file
proves that the first factors are integral off the conductor and small when untwisted. The rank one
case (the lift is a scalar of square modulus an L-value), twisting on a square block and integral
theta data are known in the literature. Related work: T. Yang, Theta liftings and Hecke L-functions,
1997; Böcherer–Schmidt, p-adic measures attached to Siegel modular forms, 2000; Harris–Li–Skinner,
The Rallis inner product formula and p-adic L-functions, 2005.
-/

@[expose] public section

noncomputable section

/-!
## The product of determinants as a sum of products, along W_j and W^add
-/

section LineLeftSide

open Matrix MvPolynomial New Rows Finset

/-- The determinant product `New.Rows.stackedDetProd` of the matrices `New.Data.constantRows` for
the short basis `D.shortRows i` at the class chosen by `i` has its columns renamed. `f` renames the
positive indices of W_j, the space of the `j`-th lift with indices `D.RowIndex`. `g` renames the
indices `AddedIndex j` of W^add. The result equals the sum over `l` of the products of two factors:
the letter polynomial (`New.letterPoly`) of the `l`-th unit vector in the letters of sign `1`,
renamed by `f`, and the `l`-th coordinate `New.Data.stackedDetProdCoords`, renamed by `g`. -/
lemma New.Data.renameRowsCols_stackedDetProd_eq_sum {P : Parameters} {D : Data P}
    (j : D.LiftIndex) (i : D.RowChoice) {n : Type*} (f : D.RowIndex → n) (g : AddedIndex j → n) :
    renameRowsCols id (f ∘ D.rowIndexOfNumber ∘ Fin.val ⊕ᵥ g)
        (stackedDetProd (posEquiv j) (constantRows j i (D.shortRows i))) =
      ∑ l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus,
        renameRowsCols id f (letterPoly (D.signsW j) (untwistedDescentPair j).numbering 1
            (untwistedDescentPair j).colsPlus (Pi.single l 1)) *
          renameRowsCols id g (stackedDetProdCoords j i (D.shortRows i) l) := by
  -- The renaming factors through `inFirstCols`: the first columns go to the letters of sign `1` on
  -- `D.RowIndex`, placed by `f`, and the coefficients to the variables on `AddedIndex j`, placed by
  -- `g`.
  have rename_eq : renameRowsCols (id : FirstFactorIndex j → FirstFactorIndex j)
        (f ∘ D.rowIndexOfNumber ∘ Fin.val ⊕ᵥ g) =
      (aevalTower (renameRowsCols id g) fun x : ((_ : D.Φ) × FirstFactorIndex j) × ℕ ↦
          renameRowsCols id f (fockLetters (D.signsW j) (untwistedDescentPair j).numbering 1
            (.X x))).comp
        (inFirstCols (Φ := D.Φ) (p := D.posRank j)) := by
    ext1 ⟨τ, a, s | s⟩
    · -- exactly one index has sign `1` and number `s`, namely `D.rowIndexOfNumber s`
      simp only [rename_X, Prod.map_apply, id_eq, Sum.elim_inl, Function.comp_apply,
        fockLetters, descentPair, Int.pred_toNat, aeval_X, map_sum, inFirstCols,
        AlgHom.coe_comp, aevalTower_X]
      rw [sum_eq_single] <;> grind [rowIndexOfNumber, D.basisNumber.eq_symm_apply, signsW]
    · simp [inFirstCols]
  -- `toPoly_stackedDetProdCoords` expands `inFirstCols (stackedDetProd …)` in the basis
  -- `nablaBasis` with coordinates `stackedDetProdCoords`; both sides become the same double sum, up
  -- to the order of summation.
  rw [rename_eq]
  simp only [AlgHom.coe_comp, Function.comp_apply, ← toPoly_stackedDetProdCoords, toPoly,
    Matrix.map, LinearMap.coe_comp, mulVecBilin_apply, Fintype.linearCombination_apply, mulVec,
    dotProduct, of_apply, nablaBasis, tableauPoly, minor, smul_eq_C_mul, map_sum,
    map_intCast, sum_mul, map_mul, aevalTower_C, map_prod, AlgHom.map_det, AlgHom.mapMatrix_apply,
    aevalTower_X, mul_right_comm _ (rename _ _), letterPoly, AlgHom.coe_toLinearMap,
    mulVec_single, MulOpposite.op_one, col_of, one_smul]
  exact sum_comm

end LineLeftSide

/-!
## Integrality and size of the first factors

Each value of Υ is a double class sum of products of three theta kernels of definite pairs, to which
`New.Rows.exists_ne_zero_isModKernelScale` applies; the third is evaluated on the polynomial
coordinates `New.Data.stackedDetProdCoords`, whose degree and denominator come from
`New.Data.exists_isHomogeneousOverEntries_smul_stackedDetProdCoords`.

`New.weylGauge κ e h y ≤ 1` says that `y` is `p`-integral for the lattice at `h`, read through the
embedding `ιₚ : ℂ → ℂ_[p]` given by the instance `[PadicPlace p]`.
-/

namespace New.Data

open Real Matrix Finset Rows MvPolynomial Ideal ComplexConjugate Sum Fintype NeZero RingHom

variable {P : Parameters} {D : Data P} {ϑ : D.TameChar}

/-- With `M = D.M`, the integer `ϑ.normQ * M ^ c` lies in the ideal of the modulus
`D.twistModulus ϑ c`: the `c`-th power of the product of the chosen places (the places
`D.chosenPlace` of the data) times the product of the places in `ϑ.Q`. -/
lemma normQ_mul_M_pow_mem_modulus {c : ℕ} :
    ↑(ϑ.normQ * D.M ^ c) ∈ (D.twistModulus ϑ c).ideal := by
  -- `D.M` lies in the product `(D.piM)` of the chosen places, and each norm `w.q` in `w`.
  have hM_mem : ↑D.M ∈ ∏ i, (D.chosenPlace i).asIdeal := by
    rw [← span_piM D, mem_span_singleton]
    exact Dvd.intro _ D.piM_mul_star
  rw [TameChar.normQ, ← ϑ.Q.prod_coe_sort FinPlace.q, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
  exact mul_mem_mul_rev (pow_mem_pow hM_mem c) (prod_mem_prod fun w _ ↦ absNorm_mem w.val.asIdeal)

/-- Replacing the matrix Y by Y·Bᵀ multiplies the matrices `constantRows` on the right by the
transpose of the block diagonal matrix (1, 1, τB, τA) at each τ, whatever A is. -/
lemma constantRows_mul_transpose_eq_mul_fromBlocks (j : D.LiftIndex) (i : D.RowChoice)
    (Y B : Matrix D.FlatIndex D.FlatIndex D.E) (A : Matrix D.CarrierIndex D.CarrierIndex D.E) :
    constantRows j i (Y * Bᵀ) = fun (τ : D.Φ) (k : DetIndex j τ) ↦
      constantRows j i Y τ k *
        (fromBlocks 1 0 0 ((fromBlocks 1 0 0 (fromBlocks B 0 0 A)).map (Φ τ)))ᵀ := by
  ext τ k x z
  -- Write the entry of the product on the right as a sum.
  refine .trans ?_ Matrix.mul_apply.symm
  obtain k | k := k
  · -- A row that is a standard basis vector, in a block where the matrix is the identity.
    obtain z | z | z | z := z
    all_goals
      simp only [constantRows, inclMatrix, transpose_submatrix, transpose_one, Matrix.map_mul,
        elim_inl, submatrix_apply, Matrix.one_apply, id_eq, transpose_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq, mem_univ, ↓reduceIte]
      split <;> simp only [eq_comm, inl.injEq, inr.injEq, reduceCtorEq, ↓reduceIte,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        Matrix.one_apply, Matrix.zero_apply, map_apply, map_zero,
        MonoidWithZeroHom.map_ite_one_zero]
  · -- A row of τ(Y), supported on the block of B.
    obtain z | z | z | z := z <;> simp only [constantRows, Matrix.map_mul, elim_inr,
      fromCols_apply_inl, fromCols_apply_inr, Matrix.zero_apply, transpose_apply, sum_sum_type,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      submatrix_apply, id_eq, Matrix.mul_apply, map_apply, map_zero, zero_mul, mul_zero,
      sum_const_zero, add_zero, zero_add]

/-- Let `q` be the bound on the number of determinants, `n ≤ (10 m + 1) q` a degree with `n ≤ D.M`
and `0 < H ≤ (n ^ n) ^ 3` a denominator. Then the constant `chosenGroupOrder ^ 2`, the two class
numbers, three kernel bounds `exp x₁`, the order of GL_{3m} over the residue ring and the bound on
`H` times the coordinates give at most exp(f m b log² b) after squaring. Here f = `D.f` is the
number of infinite places, b = `D.b` and `D.natB` the weight at the b-places, log b = `D.logB`,
`D.offWeight` the weight at the other places, `D.gap` = 2 r⁸ the gap, x₁ = `D.x₁` the second cut-off
and `D.chosenGroupOrder` a common multiple of the orders of the stabilisers. -/
lemma firstFactorSize_sq_le_exp {q n : ℕ} {H : ℤ}
    (hq : q = Fintype.card D.Φ * (D.natB + D.offWeight + D.gap + D.m * D.gap))
    (hn : n ≤ (10 * D.m + 1) * q) (hn_le_M : n ≤ D.M) (H_pos : 0 < H)
    (H_le : H ≤ (n ^ n) ^ 3) (φ : ℂ ≃+* ℂ) :
    ‖φ (D.chosenGroupOrder ^ 2)‖ ^ 2 *
        (Nat.card (StdClasses (stdLevel D.E D.CarrierIndex)) *
          (Nat.card (StdClasses (stdLevel D.E (Fin D.m))) *
            (rexp D.x₁ * rexp D.x₁ *
              (rexp D.x₁ * Fintype.card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) *
                √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q)))))) ^ 2 ≤
      rexp (D.f * D.m * D.b * D.logB ^ 2) := by
  -- With M = `D.M` and R the residue ring of `D.untwistedModulus 2`: both class numbers are at
  -- most exp(x³⁰), H ≤ n³ⁿ ≤ M³ⁿ, |GL(R)| ≤ |R|^{(3m)²}, and |R| ≤ (M²)^{2e} with
  -- e = `Core.numInfPlaces D.E`. The logarithm of the product is then the left side of `h_scale`,
  -- and with n ≤ (10 m + 1) q the scale inequalities of the data put it below f m b log² b.
  have h_scale :
      4 * log D.chosenGroupOrder +
        2 * (D.x ^ 30 + (D.x ^ 30 + (D.x₁ + D.x₁ +
          (D.x₁ + 2 * (2 * Core.numInfPlaces D.E * (2 * D.m + D.m) ^ 2) * log D.M +
            (n * 3 * 2 * log D.M / 2 + 9 * ((12 * D.m + 1) * q) * log D.M / 2))))) ≤
      D.f * D.m * D.b * D.logB ^ 2 := by
    grw [hn, hq]
    exact D.le_of_hasLogBound
  have h_carrier : card D.CarrierIndex ≤ D.n D.m := by simpa using D.nat_le_of_hasLogBound
  have h_fin : card (Fin D.m) ≤ D.n D.m := by simpa using D.nat_le_of_hasLogBound
  grw [D.card_stdClasses_le_exp principalLevel_le_stdLevel h_carrier,
    D.card_stdClasses_le_exp principalLevel_le_stdLevel h_fin]
  grw [H_le, hn_le_M, card_eq_nat_card, card_GL_le,
    Modulus.card_residueRing_le (levelModulus_ideal_le normQ_mul_M_pow_mem_modulus),
    ← le_exp_of_log_le]
  -- The goals left are the inequality of logarithms, which is `h_scale`, and positivity conditions.
  · simp only [map_pow, map_natCast, norm_pow, RCLike.norm_natCast, ← pow_mul, Nat.reduceMul,
      card_sum, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul, Nat.cast_prod,
      toAutChar_one_and_toTwist_one_and_Q_one, Finset.prod_empty, one_mul, Int.cast_pow,
      Int.cast_natCast, Nat.cast_nonneg, pow_nonneg, sqrt_mul, ne_eq, ne, not_false_eq_true,
      pow_eq_zero_iff, mul_eq_zero, exp_ne_zero, or_self, sqrt_eq_zero',
      false_or, not_or, not_le, Nat.cast_pos, pos, pow_pos, and_self, log_mul, log_pow,
      Nat.cast_ofNat, log_exp, Nat.cast_add, log_sqrt, Nat.cast_one]
    exact h_scale
  simp only [CanonicallyOrderedAdd.prod_pos, toAutChar_one_and_toTwist_one_and_Q_one,
    notMem_empty, FinPlace.q_bounds, implies_true, mul_pos_iff_of_pos_left, pos]

/-- Equivariance under rational points. Let Γ and γ' be rational unitary points of the definite
spaces W^add and V″, and let the constant rows built from Y' be those built from Y multiplied by
diag(1, Γ)ᵀ at each place. Then γ'⁻¹, acting on vectors of weight μ⁺, carries the complex conjugate
of the vector l ↦ c 𝖪[H·ζ_l](Γ g, γ' h) for Y' to that of l ↦ c 𝖪[H·ζ_l](g, h) for Y. Here 𝖪 is the
theta kernel `modKernelBilin` of (W^add, V″) for the datum Ψ modulo 𝔪, with both characters
`firstFactorChar ϑ j`, and ζ = `stackedDetProdCoords`. -/
lemma modKernelBilin_stackedDetProdCoords_equivariant (j : D.LiftIndex) (i : D.RowChoice)
    {Y Y' : Matrix D.FlatIndex D.FlatIndex D.E} {𝔪 : Modulus D.E}
    (Ψ : Matrix (FirstFactorIndex j) (AddedIndex j) 𝔪.ResidueRing → ℂ)
    (Γ : U (stdSpace D.E (AddedIndex j)).J) (γ' : U (stdSpace D.E (FirstFactorIndex j)).J)
    (g : Gf D.E (AddedIndex j)) (h : Gf D.E (FirstFactorIndex j)) (c : ℂ) (H : ℤ)
    (h_rows : constantRows j i Y' = fun (τ : D.Φ) (k : DetIndex j τ) ↦
      constantRows j i Y τ k *
        (fromBlocks 1 0 0 ((Γ : Matrix (AddedIndex j) (AddedIndex j) D.E).map (Φ τ)))ᵀ) :
    (stdSpace D.E (FirstFactorIndex j)).weightRep (untwistedDescentPair j).colsPlus 0 γ'⁻¹
        (star (c • modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
          (firstFactorChar ϑ j) (firstFactorChar ϑ j) 𝔪
            (1, (stdSpace D.E (AddedIndex j)).embFin Γ * g)
          (1, (stdSpace D.E (FirstFactorIndex j)).embFin γ' * h) Ψ ∘
            (H • stackedDetProdCoords j i Y'))) =
      star (c • modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
        (firstFactorChar ϑ j) (firstFactorChar ϑ j) 𝔪 (1, g) (1, h) Ψ ∘
          (H • stackedDetProdCoords j i Y)) := by
  -- The substitution by `γ'⁻¹` and `Γ` carries the coordinates for `Y'`, mixed by the Schur matrix
  -- of `γ'⁻¹`, to those for `Y` up to determinants, and these cancel against the change of the
  -- characters.
  have h_char : (firstFactorChar ϑ j).HasWeight
    (fun τ : D.Φ ↦ firstFactorCharExp j + -D.liftWeight j τ)
      (D.liftTamePart ϑ j) := inferInstance
  -- `A`, `B` and `B'` are the images of `γ'⁻¹`, `Γ` and diag(1, Γ) at the infinite places.
  let A (τ : D.Φ) : Matrix (FirstFactorIndex j) (FirstFactorIndex j) ℂ :=
    (↑γ'⁻¹ : Matrix (FirstFactorIndex j) (FirstFactorIndex j) D.E).map (Φ τ)
  let B (τ : D.Φ) : Matrix (AddedIndex j) (AddedIndex j) ℂ :=
    (Γ : Matrix (AddedIndex j) (AddedIndex j) D.E).map (Φ τ)
  let B' (τ : D.Φ) :
      Matrix (Fin (D.posRank j) ⊕ AddedIndex j) (Fin (D.posRank j) ⊕ AddedIndex j) ℂ :=
    fromBlocks 1 0 0 (B τ)
  have h_subst : twoSidedSubst A B' (stackedDetProd (posEquiv j) (constantRows j i Y')) =
      (∏ τ : D.Φ, ((A τ).det * (B' τ).det) ^ card (DetIndex j τ)) •
        stackedDetProd (posEquiv j) (constantRows j i Y) := by
    rw [h_rows]
    exact twoSidedSubst_stackedDetProd (posEquiv j) (constantRows j i Y) A B'
  -- The kernel of the mixed coordinates for `Y'` at the translated points is the kernel of the
  -- coordinates for `Y` at `(g, h)`.
  let θ' : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ] ℂ :=
    modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
      (firstFactorChar ϑ j)
      (firstFactorChar ϑ j) 𝔪 (1, (stdSpace D.E (AddedIndex j)).embFin Γ * g)
      (1, (stdSpace D.E (FirstFactorIndex j)).embFin γ' * h) Ψ
  let θ : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ] ℂ :=
    modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
      (firstFactorChar ϑ j)
      (firstFactorChar ϑ j) 𝔪 (1, g) (1, h) Ψ
  have h_kernel (l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus) :
      θ' (∑ k, schur (untwistedDescentPair j).colsPlus A l k • stackedDetProdCoords j i Y' k) =
        θ (stackedDetProdCoords j i Y l) := by
    refine (modKernelStdSpace_embFin_mul h_char h_char 𝔪 Ψ _ Γ γ' g h).trans ?_
    rw [twoSidedSubst_firstColsCoord A B h_subst]
    -- the powers of the determinants cancel
    simp only [Nat.cast_add, Int.natCast_ediv, add_pos_iff, k_pos, or_true, Nat.cast_pred,
      Nat.cast_ofNat, ← card_detIndex_add_firstFactorCharExp, neg_add_rev, add_assoc,
      add_neg_cancel_left, neg_neg, zpow_natCast, _root_.zpow_neg, prod_mul_distrib,
      prod_inv_distrib, InvMemClass.coe_inv, coe_units_inv, ← mapMatrix_apply, ← map_det,
      det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, det_fromBlocks_zero₂₁, det_one, one_mul,
      mul_pow, inv_pow, ← modKernelBilin_apply, map_smul, smul_eq_mul, A, B', B, θ]
    field_simp [prod_ne_zero_iff, GeneralLinearGroup.det_ne_zero]
  -- On complex conjugates `γ'⁻¹` acts by the Schur matrix of `A`.
  have h_rep (v : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ) :
      (stdSpace D.E (FirstFactorIndex j)).weightRep (untwistedDescentPair j).colsPlus 0 γ'⁻¹
        (star v) =
        star (schur (untwistedDescentPair j).colsPlus A *ᵥ v) := by
    have h_conj (τ : D.Φ) : ((starRingEnd ℂ).comp (Φ τ)).comp (starRingEnd D.E) = Φ τ :=
      RingHom.ext fun x ↦ by simp [starRingEnd_apply (R := D.E)]
    have hA : A = fun τ : D.Φ ↦
        (GeneralLinearGroup.map (Φ τ) (↑γ'⁻¹ : GL (FirstFactorIndex j) D.E)).val := rfl
    have h_star : conj ∘ star v = v := star_star v
    refine star_injective ((map_weightRep conj γ'⁻¹ (star v)).trans ?_)
    simp [weylRep, h_conj, hA, h_star]
  have h_coords : schur (untwistedDescentPair j).colsPlus A *ᵥ θ' ∘ stackedDetProdCoords j i Y' =
      θ ∘ stackedDetProdCoords j i Y := by
    ext l
    simpa [mulVec, dotProduct] using h_kernel l
  have h_smul (θ₀ : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ] ℂ)
      (Y₀ : Matrix D.FlatIndex D.FlatIndex D.E) :
      θ₀ ∘ (H • stackedDetProdCoords j i Y₀) = H • θ₀ ∘ stackedDetProdCoords j i Y₀ := by
    ext l
    simp only [Function.comp_apply, Pi.smul_apply, map_zsmul]
  rw [h_rep, h_smul, h_smul, mulVec_smul, mulVec_smul, h_coords]

/-- Let `i` be a class with its short basis, whose vectors are the rows of `D.shortRows i`, and let
`γ` be a rational unitary point that moves the representative of the class into the points integral
above `p`. Then the entries of `D.shortRows i * γᵀ` are `p`-integral under every embedding `σ`. -/
lemma norm_shortRows_mul_transpose_le_one (i : D.RowChoice) {p : ℕ} [Fact p.Prime]
    (σ : D.E →+* ℂ_[p]) {γ : U (stdSpace D.E D.FlatIndex).J}
    (hγ : (stdSpace D.E D.FlatIndex).embFin γ * i.classRep ∈ integralAbove D.FlatIndex p)
    (x z : D.FlatIndex) :
    ‖σ ((D.shortRows i * (γ : Matrix D.FlatIndex D.FlatIndex D.E)ᵀ) x z)‖ ≤ 1 := by
  -- With Y = `D.shortRows i`, the matrix γ Yᵀ = (γ g)(g⁻¹ Yᵀ) is a product of integral matrices.
  -- Here g is the representative of the class, and `Z` is g⁻¹ Yᵀ.
  let Z : Matrix D.FlatIndex D.FlatIndex (𝔸f D.E) :=
    ((i.classRep⁻¹ : Gf D.E D.FlatIndex) : Matrix D.FlatIndex D.FlatIndex (𝔸f D.E)) *
      (D.shortRows i)ᵀ.map (algebraMap D.E (𝔸f D.E))
  have hZ_int : IsIntMatrix (Ô D.E) Z :=
    (Space.exists_short_basis_stdSpace P.conductor_mem_differentIdeal i.classRep).choose_spec.left
  have hZ_map : IsIntMatrix NormedField.valuation.integer (Z.map (adeleExtension σ)) :=
    fun a b ↦ norm_adeleExtension_le_one σ (hZ_int a b)
  have h_prod : IsIntMatrix NormedField.valuation.integer
      (((γ : Matrix D.FlatIndex D.FlatIndex D.E) * (D.shortRows i)ᵀ).map σ) := by
    simpa [Z, ← Matrix.map_mul, mul_assoc, Function.comp_def] using
      (adeleExtension_mem_intGL σ hγ).isIntMatrix.mul hZ_map
  have h_entry :
      ‖σ (((γ : Matrix D.FlatIndex D.FlatIndex D.E) * (D.shortRows i)ᵀ) z x)‖ ≤ 1 := h_prod z x
  simpa [Matrix.mul_apply, mul_comm] using h_entry

/-- Let v(Y, g, h) be the vector l ↦ conj (c 𝖪[H·ζ_l](g, h)). Here ζ = `stackedDetProdCoords j i Y`,
and 𝖪 is the theta kernel of the standard definite spaces W^add on `AddedIndex j` and V″ on
`FirstFactorIndex j`, with both characters `firstFactorChar ϑ j` for the tame character `ϑ` and a
datum `Ψ` on matrices modulo the modulus `𝔪`. Suppose that v(Y, g', h') has `p`-integral coordinates
under `ιₚ : ℂ → ℂ_[p]` whenever the finite adelic points `g'`, `h'` have integral components at the
primes above `p` (`integralAbove`) and the entries of `Y`, embedded in ℂ by `Φ τ`, are `p`-integral
under `ιₚ ∘ conj`. Let g be the block diagonal point (`U.blockSumOne`) with blocks `1`, the
representative in U(W♭) of the class of `i`, and `w` in U(E^{3m}). Then v(`D.shortRows i`, g, h) has
gauge at most one at every `h` (`weylGauge`): all coordinates of h⁻¹ · ιₚ(v) have norm at most
one. -/
lemma weylGauge_modKernelBilin_stackedDetProdCoords_le_one (j : D.LiftIndex) (i : D.RowChoice)
    {𝔪 : Modulus D.E} (Ψ : Matrix (FirstFactorIndex j) (AddedIndex j) 𝔪.ResidueRing → ℂ)
    {p : ℕ} [Fact p.Prime] [PadicPlace p] (c : ℂ) (H : ℤ)
    (h_int : ∀ g' ∈ integralAbove (AddedIndex j) p, ∀ h' ∈ integralAbove (FirstFactorIndex j) p,
      ∀ Y : Matrix D.FlatIndex D.FlatIndex D.E,
        (∀ (τ : D.Φ) (x z : D.FlatIndex), ‖ιₚ (conj (Φ τ (Y x z)))‖ ≤ 1) →
        ∀ l : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus,
          ‖ιₚ (conj (c * modKernelStdSpace (stdSpace D.E (AddedIndex j)) (firstFactorChar ϑ j)
            (firstFactorChar ϑ j) 𝔪 Ψ (H • stackedDetProdCoords j i Y l) (1, g') h'))‖ ≤ 1)
    (w : Gf D.E D.CarrierIndex) (h : Gf D.E (FirstFactorIndex j)) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h
      (star (c • modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
        (firstFactorChar ϑ j) (firstFactorChar ϑ j) 𝔪
          (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) (1, h)
        Ψ ∘ (H • stackedDetProdCoords j i (D.shortRows i)))) ≤ 1 := by
  -- Weak approximation: rational points move the two blocks and h into the integral points.
  obtain ⟨γ₁, hγ₁, -⟩ := exists_mul_mem_integralAbove p i.classRep 1 (stdSpace D.E D.FlatIndex)
  obtain ⟨γ₂, hγ₂, -⟩ := exists_mul_mem_integralAbove p w 1 (stdSpace D.E D.CarrierIndex)
  obtain ⟨γ', hγ', -⟩ := exists_mul_mem_integralAbove p h 1 (stdSpace D.E (FirstFactorIndex j))
  -- Move `g` by the block matrix Γ; the short basis becomes Y'.
  let g : Gf D.E (AddedIndex j) := U.blockSumOne (1, U.blockSumOne (i.classRep, w))
  let Γ : U (stdSpace D.E (AddedIndex j)).J := U.blockSumOne (1, U.blockSumOne (γ₁, γ₂))
  let Y' : Matrix D.FlatIndex D.FlatIndex D.E :=
    D.shortRows i * (γ₁ : Matrix D.FlatIndex D.FlatIndex D.E)ᵀ
  have hΓ : (stdSpace D.E (AddedIndex j)).embFin Γ * g ∈ integralAbove (AddedIndex j) p :=
    blockSumOne_mul_mem_integralAbove (γ := 1) (by simp) (blockSumOne_mul_mem_integralAbove hγ₁ hγ₂)
  have h_rows : constantRows j i Y' = fun (τ : D.Φ) (k : DetIndex j τ) ↦
      constantRows j i (D.shortRows i) τ k *
        (fromBlocks 1 0 0 ((Γ : Matrix (AddedIndex j) (AddedIndex j) D.E).map (Φ τ)))ᵀ :=
    constantRows_mul_transpose_eq_mul_fromBlocks ..
  have hY' (τ : D.Φ) (x z : D.FlatIndex) : ‖ιₚ (conj (Φ τ (Y' x z)))‖ ≤ 1 :=
    norm_shortRows_mul_transpose_le_one i ((ιₚ.comp conj).comp (Φ τ)) hγ₁ x z
  -- By equivariance the gauge at h is the gauge of the vector for Y' at the integral point γ' h,
  -- where gauge ≤ 1 means that all coordinates are integral.
  rw [← modKernelBilin_stackedDetProdCoords_equivariant j i Ψ Γ γ' g h c H h_rows,
    ← weylGauge_embFin,
    Representation.self_inv_apply, weylGauge_le_one_iff _ hγ']
  exact h_int _ hΓ _ hγ' Y' hY'

/-- Let `ϑ` be a tame character with set of places Q, let ϖ be the product of the chosen places, and
let `u`, `x` be matrices modulo ϖ² and ϖ²Q. The datum `addedDatum ϑ j u x` is `0` or a sum, over
GL_{3m}(O_E/ϖ²), of values of the additive character attached to `u`. For each `n` it has norm at
most one under all ring maps `ℂ → ℂ_[l]` with `l` a prime coprime to `n`
(`New.Seesaw.integralAway`). -/
lemma addedDatum_mem_integralAway {ϑ : D.TameChar} (j : D.LiftIndex)
    (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
    (x : Matrix (FirstFactorIndex j) (AddedIndex j) (D.twistModulus ϑ 2).ResidueRing) (n : ℕ) :
    addedDatum ϑ j u x ∈ Seesaw.integralAway n := by
  -- The values of an additive character of a finite group are roots of unity.
  have h_char (y : Matrix (FirstFactorIndex j) D.CarrierIndex (D.untwistedModulus 2).ResidueRing) :
      traceChar u y ∈ Seesaw.integralAway n := fun l _ _ ι ↦
    ((ι.compAddChar _).norm_apply _).le
  rw [addedDatum]
  split
  · exact sum_mem fun g _ ↦ h_char _
  · exact zero_mem _

/-- Every conjugate of a value of `New.Data.addedDatum`, for a matrix `u` modulo ϖ², has absolute
value at most the order of GL over the residue ring of `D.untwistedModulus 2` (the modulus ϖ², ϖ
the product of the chosen places), the number of terms in the sum defining it. -/
lemma norm_map_addedDatum_le (j : D.LiftIndex)
    (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
      (σ : ℂ ≃+* ℂ)
    (x : Matrix (FirstFactorIndex j) (AddedIndex j) (D.twistModulus ϑ 2).ResidueRing) :
    ‖σ (addedDatum ϑ j u x)‖ ≤ card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) := by
  -- The value is 0 or a sum, over this group, of values of an additive character.
  rw [addedDatum]
  split
  · simpa using! norm_sum_le_of_le univ fun _ _ ↦ ((σ.toRingHom.compAddChar _).norm_apply _).le
  · simp

/-- The ranks of the five spaces in the three kernels are at most the gap `Δ = D.gap`. -/
lemma card_le_gap (j : D.LiftIndex) :
    card (Fin D.m) ≤ D.gap ∧
    card D.CarrierIndex ≤ D.gap ∧
    card (Fin j) ≤ D.gap ∧
    card (FirstFactorIndex j) ≤ D.gap ∧
    card (AddedIndex j) ≤ D.gap := by
  have h_gap : 40 * D.k ≤ D.gap := mod_cast (D.le_of_hasLogBound : (40 * D.k : ℝ) ≤ D.gap)
  grind [card_sum, card_rowIndex, Fintype.card_fin]

/-- Let ζ = `stackedDetProdCoords j i (D.shortRows i)` be the vector of coordinates of the product
of determinants, polynomials in variables indexed by an infinite place in `D.Φ`, a row in
`FirstFactorIndex j` and a column in `AddedIndex j`. Evaluate `H • ζ` at a point `z` whose
`σ`-conjugates are at most `M ^ 4`, where `M = D.M`, and apply `σ`. If `q` bounds the total number
of determinants, the root of the squared norm (`New.weylNormSq`) of the result is at most
`√(H ^ 2 (M ^ 9) ^ ((12 m + 1) q))`, with `m = D.m`. -/
lemma sqrt_weylNormSq_smul_eval_stackedDetProdCoords_le (j : D.LiftIndex) (i : D.RowChoice) {q : ℕ}
    (hq : ∑ τ : D.Φ, card (DetIndex j τ) ≤ q) (H : ℤ) (σ : ℂ ≃+* ℂ)
    {z : D.Φ × FirstFactorIndex j × AddedIndex j → ℂ}
    (hz : ∀ x : D.Φ × FirstFactorIndex j × AddedIndex j, ‖σ (z x)‖ ≤ D.M ^ 4) :
    √(weylNormSq (σ ∘ eval z ∘ (H • stackedDetProdCoords j i (D.shortRows i)))) ≤
      √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q)) := by
  -- The rows `D.shortRows i` form a short basis, so their entries are small too.
  have hY_small (ψ : D.E →+* ℂ) (x y : D.FlatIndex) :
      ‖ψ (D.shortRows i x y)‖ ≤ Space.shortBasisConst D.E D.FlatIndex (P.q₁ D.towerExp * P.d) :=
    (Space.exists_short_basis_stdSpace P.conductor_mem_differentIdeal i.1.out).choose_spec.2 ψ y x
  have hY_le (τ : D.Φ) (x y : D.FlatIndex) : ‖σ (Φ τ (D.shortRows i x y))‖ ≤ D.M ^ 4 :=
    (hY_small (.comp σ (Φ τ)) x y).trans (by simpa using D.le_of_hasLogBound)
  have h_coords : weylNormSq ((σ : ℂ →+* ℂ) ∘ eval z ∘ stackedDetProdCoords j i (D.shortRows i)) ≤
      ↑(D.M ^ 9) ^ ((12 * D.m + 1) * ∑ τ : D.Φ, card (DetIndex j τ)) :=
    weylNormSq_comp_eval_stackedDetProdCoords_le j i (D.shortRows i) hY_le hz
  have h_smul : eval z ∘ (H • stackedDetProdCoords j i (D.shortRows i)) =
      (H : ℂ) • eval z ∘ stackedDetProdCoords j i (D.shortRows i) := by simp [funext_iff]
  -- The scalar `H` multiplies the squared norm by `H ^ 2`, and `M ^ 9 ≥ 1` lets `q` replace the
  -- number of determinants.
  grw (transparency := default) [h_smul, weylNormSq_comp_smul, h_coords, hq]
  · simp
  · exact D.le_of_hasLogBound

/-- Duality for a vector `v` of homogeneous polynomials of degree `n`. Its coordinates are indexed
by the basis `WeylIndex N κ` of the Weyl module of GL_N whose diagram at each `τ : T` has `κ τ h`
columns of height `h`. The norm of a coordinate vector is the square root of `weylNormSq`, its
squared norm for the positive definite Hermitian form of the Gram matrix. Let `σ` be a ring
automorphism of ℂ. Suppose that the `σ`-conjugates of the values of `v` on a set `S` have norm at
most `B`. Suppose also that a linear form `θ` has `‖σ (θ Q)‖ ≤ C` for every homogeneous `Q` of
degree `n` with `‖σ (Q z)‖ ≤ B` on `S`. Then the `σ`-conjugate of `θ ∘ v` has norm at most `C`. -/
lemma sqrt_weylNormSq_comp_le_of_eval_le {T N ι : Type} [Fintype T] [DecidableEq T] [Fintype N]
    [DecidableEq N] {κ : T → ℕ → ℕ} (σ : ℂ ≃+* ℂ) (θ : MvPolynomial ι ℂ →ₗ[ℂ] ℂ)
    {v : WeylIndex N κ → MvPolynomial ι ℂ} {n : ℕ} {S : Set (ι → ℂ)} {B C : ℝ}
    (hv_hom : ∀ l : WeylIndex N κ, (v l).IsHomogeneous n)
    (hv_le : ∀ z ∈ S, √(weylNormSq (σ ∘ eval z ∘ v)) ≤ B)
    (hθ : ∀ Q : MvPolynomial ι ℂ, Q.IsHomogeneous n → (∀ z ∈ S, ‖σ (Q.eval z)‖ ≤ B) →
      ‖σ (θ Q)‖ ≤ C) :
    √(weylNormSq (σ ∘ θ ∘ v)) ≤ C := by
  -- Test against a functional f of norm at most one, and apply `hθ` to Q = ∑ f l • v l.
  refine sqrt_weylNormSq_le_of_dual σ fun f hf ↦ ?_
  have hQ_hom : (∑ l, f l • v l).IsHomogeneous n :=
    (homogeneousSubmodule ι ℂ n).sum_mem fun l _ ↦ Submodule.smul_mem _ (f l) (hv_hom l)
  have hQ_le (z : ι → ℂ) (hz : z ∈ S) : ‖σ ((∑ l, f l • v l).eval z)‖ ≤ B := by
    simpa [dotProduct] using (hf (eval z ∘ v)).trans (hv_le z hz)
  simpa [dotProduct] using hθ _ hQ_hom hQ_le

/-- Let `p` be a prime with an embedding `ιₚ : ℂ → ℂ_[p]` (`PadicPlace p`). A vector `y` of weight
μ⁺ = `(untwistedDescentPair j).colsPlus` is `p`-integral at `h` if `weylGauge μ⁺ 0 h y ≤ 1`: all
coordinates of h⁻¹ · ιₚ(y) have norm at most one. Let every `f w v` be `p`-integral at `h`. Then so
is their double class sum over U(E^{3m}) and U(E^m) (`stdClassSum`, the sum of the values at class
representatives divided by the orders of the stabilisers), multiplied by the square of
`D.chosenGroupOrder`, which is a common multiple of these orders. -/
lemma weylGauge_stdClassSum_stdClassSum_le_one {j : D.LiftIndex} {p : ℕ} [Fact p.Prime]
    [PadicPlace p] (h : Gf D.E (FirstFactorIndex j))
    {f : Gf D.E D.CarrierIndex → Gf D.E (Fin D.m) →
      WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ}
    (hf : ∀ (w : Gf D.E D.CarrierIndex) (v : Gf D.E (Fin D.m)),
      weylGauge (untwistedDescentPair j).colsPlus 0 h (f w v) ≤ 1) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h
      ((D.chosenGroupOrder ^ 2 : ℂ) •
        stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
          stdClassSum (stdLevel D.E (Fin D.m)) (f w)) ≤ 1 := by
  -- Each of the two class sums takes one factor `D.chosenGroupOrder`, a multiple of the orders of
  -- all the stabilisers.
  let A : ℕ := D.chosenGroupOrder
  have h_carrier : card D.CarrierIndex ≤ 2 * D.n D.m := by simpa using D.nat_le_of_hasLogBound
  have h_fin : card (Fin D.m) ≤ 2 * D.n D.m := by simpa using D.nat_le_of_hasLogBound
  have h_inner (w : Gf D.E D.CarrierIndex) :
      weylGauge (untwistedDescentPair j).colsPlus 0 h
        ((A : ℂ) • stdClassSum (stdLevel D.E (Fin D.m)) (f w)) ≤ 1 := by
    simpa [A] using weylGauge_classSum_le_one h (card_classAut_dvd_chosenGroupOrder h_fin le_rfl)
      (c := 1) (f := f w) fun v ↦ by simpa using hf w v
  simpa [A, sq] using
    weylGauge_classSum_le_one h (card_classAut_dvd_chosenGroupOrder h_carrier le_rfl) h_inner

/-- Let `q` = |D.Φ| (natB + offWeight + Δ + m Δ) be the bound on the number of determinants, with
the weights `D.natB`, `D.offWeight` and the gap Δ = `D.gap`. Let `n ≤ (10 m + 1) q`, `n ≤ M` for
M = `D.M`, and `0 < H ≤ (n ^ n) ^ 3`. Let every vector `F w v` have `φ`-conjugate of norm at most
exp(3 x₁) |GL_{3m}(O_E/ϖ²)| √(H² M^{9 (12 m + 1) q}), where x₁ = `D.x₁` is a size parameter of the
data and ϖ² = `D.untwistedModulus 2` is the square of the product of the chosen places. Then the
double class sum of `F`, multiplied by the square of `D.chosenGroupOrder` (a common multiple of the
orders of the stabilisers), has `φ`-conjugate of squared norm at most exp(f m b log² b), for the
number f = `D.f` of infinite places, the weight b = `D.b` and log b = `D.logB`. -/
lemma weylNormSq_stdClassSum_stdClassSum_le {j : D.LiftIndex} {q n : ℕ} {H : ℤ}
    (hq : q = Fintype.card D.Φ * (D.natB + D.offWeight + D.gap + D.m * D.gap))
    (hn : n ≤ (10 * D.m + 1) * q) (hn_le_M : n ≤ D.M) (H_pos : 0 < H)
    (H_le : H ≤ (n ^ n) ^ 3) (φ : ℂ ≃+* ℂ)
    {F : Gf D.E D.CarrierIndex → Gf D.E (Fin D.m) →
      WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ}
    (hF : ∀ (w : Gf D.E D.CarrierIndex) (v : Gf D.E (Fin D.m)),
      √(weylNormSq (φ ∘ F w v)) ≤ rexp D.x₁ * rexp D.x₁ *
        (rexp D.x₁ * card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) *
          √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q)))) :
    weylNormSq (φ ∘ ((D.chosenGroupOrder ^ 2 : ℂ) •
        stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
          stdClassSum (stdLevel D.E (Fin D.m)) (F w))) ≤
      rexp (D.f * D.m * D.b * D.logB ^ 2) := by
  -- Each class sum multiplies the bound by its class number; the rest is numerical.
  have h_sum : √(weylNormSq (φ ∘ stdClassSum (stdLevel D.E D.CarrierIndex)
        fun w : Gf D.E D.CarrierIndex ↦ stdClassSum (stdLevel D.E (Fin D.m)) (F w))) ≤
      Nat.card (StdClasses (stdLevel D.E D.CarrierIndex)) *
        (Nat.card (StdClasses (stdLevel D.E (Fin D.m))) *
        (rexp D.x₁ * rexp D.x₁ *
          (rexp D.x₁ * card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing) *
            √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q))))) :=
    sqrt_weylNormSq_classSum_le φ fun w ↦ sqrt_weylNormSq_classSum_le φ (hF w)
  grw (transparency := default) [weylNormSq_comp_smul, (sqrt_le_iff.1 h_sum).2]
  exact firstFactorSize_sq_le_exp hq hn hn_le_M H_pos H_le φ

/-- The vector `y` of weight `(untwistedDescentPair j).colsPlus` is integral at `h` away from the
norm `ϑ.normQ` of Q (the product of the norms of the places in `ϑ.Q`), and has small conjugates if
`ϑ.Q` is empty: the bound is exp(f m b log² b), for the number f = `D.f` of infinite places, the
weight b = `D.b` and log b = `D.logB`. -/
structure IsIntegralAndSmall (ϑ : D.TameChar) (j : D.LiftIndex) (h : Gf D.E (FirstFactorIndex j))
    (y : WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ) : Prop where
  /-- `y` is `p`-integral at `h` for every prime `p` that does not divide `ϑ.normQ`. -/
  weylGauge_le_one (p : ℕ) [Fact p.Prime] [PadicPlace p] (hp : p.Coprime ϑ.normQ) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h y ≤ 1
  /-- If `ϑ.Q` is empty, all conjugates of `y` have squared norm at most exp(f m b log² b). -/
  weylNormSq_le (hQ : ϑ.Q = ∅) (φ : ℂ ≃+* ℂ) :
    weylNormSq (φ ∘ y) ≤ Real.exp (D.f * D.m * D.b * D.logB ^ 2)

/-- Let `ϑ` be a tame character and χ′ = χ^j ϑ, where χ = `D.chiM` is the fixed character of U(1)(𝔸)
of weight `0` and tame part `D.chiMLocal`. Take the theta kernel of the standard definite spaces
(E^m, E^{3m}) with characters χ′ and `1`, unit modulus, datum `1` and polynomial `1`, and a constant
`c` that normalises such kernels. For every prime `p` with an embedding `ιₚ : ℂ → ℂ_[p]`, the image
of `c` times the kernel has norm at most one at all finite adelic points `v`, `w`. -/
lemma norm_mul_modKernelStdSpace_twistedChiMPow_le_one {ϑ : D.TameChar} {j : D.LiftIndex} {c : ℂ}
    (hc : IsModKernelScale (Fin D.m) D.CarrierIndex D 0 c) {p : ℕ} [Fact p.Prime] [PadicPlace p]
    (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) :
    ‖ιₚ (c * modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
      (1, v) w)‖ ≤ 1 := by
  -- Move v and w into the integral points; the kernel does not change, as the polynomial is 1 and
  -- both characters have weight 0.
  obtain ⟨γv, hγv, -⟩ := exists_mul_mem_integralAbove p v 1 (stdSpace D.E (Fin D.m))
  obtain ⟨γw, hγw, -⟩ := exists_mul_mem_integralAbove p w 1 (stdSpace D.E D.CarrierIndex)
  have h_char := twistedChiMPow_hasWeight ϑ j
  have h_inv : modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E)
      1 1 (1, (stdSpace D.E (Fin D.m)).embFin γv * v)
        ((stdSpace D.E D.CarrierIndex).embFin γw * w) =
      modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
        (1, v) w := by
    simp [modKernelStdSpace_embFin_mul h_char .one]
  rw [← h_inv]
  exact hc.norm_le_one (q := 1) h_char .one Submodule.mem_top (by simp) (isHomogeneous_one _ _)
    p.coprime_one_right hγv hγw (one_mem _)

/-- Take the theta kernel `modKernelStdSpace` of (E^j, V″), with V″ the standard definite space on
the index set `FirstFactorIndex j`, for the characters `1` and `b`, a datum `Ψ` modulo `𝔪` and the
polynomial `1`. Let `c` be a constant that normalises such kernels. Let `b` have weight `e` at the
infinite places `D.Φ` and tame part `ψ`, a character of the residue field `ResField w` at each
finite place `w`. Let `𝔪` contain `q * D.M ^ 2`, with `D.M` the integer `M` of the data. Let the
values of `Ψ` have norm at most one under all ring maps `ℂ → ℂ_[l]` with `l` a prime coprime to `q`.
Let `p` be a prime coprime to `q`, and let `h` lie in `Gf D.E (FirstFactorIndex j)`, the finite
adelic unitary group of V″. Then the image under `ιₚ : ℂ → ℂ_[p]` of `c` times the kernel at `1` and
`h` has norm at most one. -/
lemma norm_mul_modKernelStdSpace_one_le_one {j : D.LiftIndex} {c : ℂ}
    (hc : IsModKernelScale (Fin j) (FirstFactorIndex j) D 0 c) {b : AutChar D.E} {e : D.Φ → ℤ}
    {ψ : (w : FinPlace D.E) → MulChar (ResField w) ℂ} (hb : b.HasWeight e ψ) {q : ℕ}
    {𝔪 : Modulus D.E} (h𝔪 : ↑(q * D.M ^ 2) ∈ 𝔪.ideal)
    {Ψ : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing → ℂ}
    (hΨ : ∀ x : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing, Ψ x ∈ Seesaw.integralAway q)
    {p : ℕ} [Fact p.Prime] [PadicPlace p] (hp : p.Coprime q) (h : Gf D.E (FirstFactorIndex j)) :
    ‖ιₚ (c * modKernelStdSpace (stdSpace D.E (Fin j)) 1 b 𝔪 Ψ 1 (1, 1) h)‖ ≤ 1 := by
  -- Move h into the integral points; the kernel does not change, as the polynomial and the first
  -- character are 1.
  obtain ⟨γ, hγ, -⟩ := exists_mul_mem_integralAbove p h 1 (stdSpace D.E (FirstFactorIndex j))
  have h_inv : modKernelStdSpace (stdSpace D.E (Fin j)) 1 b 𝔪 Ψ 1 1
      ((stdSpace D.E (FirstFactorIndex j)).embFin γ * h) =
      modKernelStdSpace (stdSpace D.E (Fin j)) 1 b 𝔪 Ψ 1 1 h := by
    simpa [Prod.mk_one_one] using modKernelStdSpace_embFin_mul .one hb 𝔪 Ψ 1 1 γ 1 h
  simpa [h_inv, Prod.mk_one_one] using
    hc.norm_le_one .one hb h𝔪 hΨ (isHomogeneous_one _ _) hp (one_mem _) hγ (one_mem _)

/-- Expansion of the conjugate of a multiple of the series Υ = `leftSideSeries ϑ j (u, i) h`, for a
tame character `ϑ`, a matrix `u` modulo ϖ² (`D.untwistedModulus 2`, ϖ the product of the chosen
places) and a class with rows `i`. Let g = `D.chosenGroupOrder`, a common multiple of the orders of
the stabilisers. There is `c` of modulus one, depending only on `j`, such that the conjugate of g²
c₂ H c₀ conj(c₁) c Υ is g² times a double class sum over U(E^{3m}) and U(E^m) of conjugates of
products of three theta kernels of definite spaces: `k₀` of (E^m, E^{3m}), the conjugate of `k₁` of
(E^j, V″), and c₂ times the kernel of (W^add, V″) at the polynomial vector
`H • stackedDetProdCoords j i (D.shortRows i)`, formed with a short basis of the class. V″ and W^add
are the spaces on `FirstFactorIndex j` and `AddedIndex j`, and the last two kernels have modulus
ϖ²Q. Here `Ψ x` is the conjugate, at `normNegOne • x` (a chosen element of norm −1, reduced), of the
indicator of the matrix of the inclusion E^j → V″ (`inclMatrix`), and `b'` is the inverse of the
character `firstFactorChar ϑ j` times the power rank V″ of `upsilonU1` (υ on the norm-one ideles).
The scalars `c₀`, `c₁`, `c₂` and the integer `H` are arbitrary. -/
lemma exists_star_leftSideSeries_eq_classSum (j : D.LiftIndex) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ (c₀ c₁ c₂ : ℂ) (H : ℤ)
      (u : Matrix D.CarrierIndex (FirstFactorIndex j) (D.untwistedModulus 2).ResidueRing)
      (i : D.RowChoice) (ϑ : D.TameChar) (h : Gf D.E (FirstFactorIndex j)),
      let Ψ : Matrix (FirstFactorIndex j) (Fin j) (D.twistModulus ϑ 2).ResidueRing → ℂ := fun x ↦
        (conj ∘ Pi.single (inclMatrix (D.twistModulus ϑ 2).ResidueRing (inl ∘ inr ∘ inl)) 1)
          ((D.twistModulus ϑ 2).normNegOne • x)
      let b' : AutChar D.E := (firstFactorChar ϑ j)⁻¹ * WeilData.upsilonU1 ^ Nat.card
        (FirstFactorIndex j)
      let k₀ (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) : ℂ :=
        c₀ * modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
          (1, v) w
      let k₁ : ℂ := c₁ * modKernelStdSpace (stdSpace D.E (Fin j)) 1 b' (D.twistModulus ϑ 2) Ψ 1
        (1, 1) h
      star ((D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ * c : ℂ) •
          leftSideSeries ϑ j (u, i) h) =
        (D.chosenGroupOrder ^ 2 : ℂ) •
          stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
            stdClassSum (stdLevel D.E (Fin D.m)) fun v : Gf D.E (Fin D.m) ↦
              star ((k₀ v w * conj k₁) • c₂ •
                modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
                  (firstFactorChar ϑ j) (firstFactorChar ϑ j) (D.twistModulus ϑ 2)
                  (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) (1, h)
                  (addedDatum ϑ j u) ∘
                (H • stackedDetProdCoords j i (D.shortRows i))) := by
  -- The first factor of Υ, a kernel of ((E^j)⁻, V″), is a multiple of conj k₁. The other factor is
  -- a double class sum once `carrierCoeff` is expanded. Then conjugate term by term.
  obtain ⟨c, hc, h_neg⟩ :=
    exists_conj_modKernel_eq_mul_modKernel_neg (stdSpace D.E (Fin j))
      (stdSpace D.E (FirstFactorIndex j))
  refine ⟨c, hc, fun c₀ c₁ c₂ H u i ϑ h ↦ ?_⟩
  intro Ψ b' k₀ k₁
  ext l
  have h_char : b'⁻¹ * WeilData.upsilonU1 ^ card (FirstFactorIndex j) = firstFactorChar ϑ j := by
    rw [← Nat.card_eq_fintype_card, mul_inv, inv_inv, inv_mul_cancel_right]
  have h_first : conj k₁ = conj c₁ * c *
      modKernelStdSpace (stdSpace D.E (Fin j)).neg (WeilData.upsilonU1 ^ j.val)
        (firstFactorChar ϑ j) (D.twistModulus ϑ 2)
        (Pi.single (inclMatrix (D.twistModulus ϑ 2).ResidueRing (inl ∘ inr ∘ inl)) 1) 1 1 h := by
    rw [map_mul, h_neg, h_char, mul_assoc]
    simp [Ψ, Prod.mk_one_one]
  -- `θ w` is the kernel of (W^add, V″) at the coordinate `l` of ζ.
  let θ (w : Gf D.E D.CarrierIndex) : ℂ :=
    modKernelStdSpace (stdSpace D.E (AddedIndex j)) (firstFactorChar ϑ j) (firstFactorChar ϑ j)
      (D.twistModulus ϑ 2) (addedDatum ϑ j u) (stackedDetProdCoords j i (D.shortRows i) l)
      (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) h
  have h_series : c₂ * H * c₀ * conj c₁ * c * leftSideSeries ϑ j (u, i) h l =
      stdClassSum (stdLevel D.E D.CarrierIndex) fun w : Gf D.E D.CarrierIndex ↦
        stdClassSum (stdLevel D.E (Fin D.m)) fun v : Gf D.E (Fin D.m) ↦
          k₀ v w * conj k₁ * (c₂ * (H * θ w)) := by
    simp only [leftSideSeries, carrierCoeff, classSum_mul, mul_classSum, h_first, k₀, θ]
    ac_rfl
  -- Class sums of vectors are computed coordinate by coordinate.
  have h_coord {n : Type} [Fintype n] [DecidableEq n]
      (F : Gf D.E n → WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ) :
      stdClassSum (stdLevel D.E n) F l = stdClassSum (stdLevel D.E n) fun g : Gf D.E n ↦ F g l :=
    map_classSum (Pi.evalAddMonoidHom (fun _ ↦ ℂ) l) F
  have h_scalar : D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ * c *
      leftSideSeries ϑ j (u, i) h l =
        D.chosenGroupOrder ^ 2 * (c₂ * H * c₀ * conj c₁ * c * leftSideSeries ϑ j (u, i) h l) := by
    ring
  rw [Pi.star_apply, Pi.smul_apply, smul_eq_mul, h_scalar, h_series]
  simp [h_coord, map_classSum, θ, ← Int.cast_smul_eq_zsmul ℂ H]

/-- For 1 ≤ j ≤ m there is one c ≠ 0, independent of i, ϑ and h, such that every vector y = conj
(c · Υ) is integral and small in the sense of `New.Data.IsIntegralAndSmall`: for every prime p that
does not divide `ϑ.normQ`, the product of the norms of the places in `ϑ.Q`, the coordinates of
h⁻¹ · ιₚ(y) are `p`-integral (`New.weylGauge` ≤ 1), and if `ϑ.Q = ∅`, every conjugate φ ∘ y,
φ ∈ Aut(ℂ), has squared norm at most exp(f m b log² b), with the number f = `D.f` of infinite
places, m = `D.m`, the weight b = `D.b` and log b = `D.logB`. -/
lemma exists_isIntegralAndSmall_leftSideSeries (j : D.LiftIndex) :
    ∃ c ≠ (0 : ℂ), ∀ (i : ChoiceIndex j) (ϑ : D.TameChar) (h : Gf D.E (FirstFactorIndex j)),
      IsIntegralAndSmall ϑ j h (star (c • leftSideSeries ϑ j i h)) := by
  -- Write the vector y as a double class sum of terms conj(k₀ · conj k₁ · k₂), three kernels of
  -- definite pairs, each made integral by a constant from `exists_ne_zero_isModKernelScale`;
  -- the last is evaluated on H·`stackedDetProdCoords`. Integrality: move the classes into the
  -- p-integral points and multiply the three bounds. Size: bound each term by duality, count the
  -- classes, via `weylNormSq_stdClassSum_stdClassSum_le`. `q` bounds the total number of
  -- determinants, over the infinite places.
  let q : ℕ := card D.Φ * (D.natB + D.offWeight + D.gap + D.m * D.gap)
  have h_detCount : ∑ τ : D.Φ, card (DetIndex j τ) ≤ q :=
    sum_le_card_nsmul _ _ _ fun τ _ ↦ card_detIndex_le j τ
  -- The degree n ≤ (10 m + 1) q and the denominator 0 < H ≤ n³ⁿ of ζ: by `h_denom`, each
  -- `H • stackedDetProdCoords j i Y l` is homogeneous of degree n, with coefficients in every
  -- subring of ℂ that contains the conjugates of the entries of `Y`.
  obtain ⟨n, hn, H, H_pos, H_le, h_denom⟩ :=
    exists_isHomogeneousOverEntries_smul_stackedDetProdCoords j
  grw [h_detCount] at hn
  have hn_le_M : n ≤ D.M := hn.trans D.nat_le_of_hasLogBound
  -- The constants of the three kernels: by `K₀`, `K₁`, `K₂`, cᵢ times the kernel is integral at
  -- p-integral points and has bounded conjugates.
  obtain ⟨c₀, hc₀, K₀⟩ := exists_ne_zero_isModKernelScale (Fin D.m) D.CarrierIndex D 0
  obtain ⟨c₁, hc₁, K₁⟩ := exists_ne_zero_isModKernelScale (Fin j) (FirstFactorIndex j) D 0
  obtain ⟨c₂, hc₂, K₂⟩ := exists_ne_zero_isModKernelScale (AddedIndex j) (FirstFactorIndex j) D
    n
  obtain ⟨c, hc, h_expand⟩ := exists_star_leftSideSeries_eq_classSum j
  let scale : ℂ := D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ * c
  refine ⟨scale, ?_, ?_⟩
  · simp [scale, H_pos.ne', ne, ← norm_pos_iff, hc, hc₀, hc₁, hc₂]
  intro ⟨u, i⟩ ϑ h
  -- The characters and the data of the kernels; the data are integral away from `ϑ.normQ`.
  let 𝔪 : Modulus D.E := D.twistModulus ϑ 2
  let b' : AutChar D.E := (firstFactorChar ϑ j)⁻¹ * WeilData.upsilonU1 ^ Nat.card
    (FirstFactorIndex j)
  have hb : (firstFactorChar ϑ j).HasWeight (firstFactorCharExp j + -D.liftWeight j ·)
    (D.liftTamePart ϑ j) :=
    inferInstance
  have hb' : b'.HasWeight _ (D.liftTamePart ϑ j)⁻¹ := hb.inv.mul_upsilonU1_pow _
  let Ψ : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing → ℂ := fun x ↦
    (conj ∘ Pi.single (inclMatrix 𝔪.ResidueRing (inl ∘ inr ∘ inl)) 1) (𝔪.normNegOne • x)
  have hΨ (x : Matrix (FirstFactorIndex j) (Fin j) 𝔪.ResidueRing) :
    Ψ x ∈ Seesaw.integralAway ϑ.normQ := by
    simp [Ψ, apply_ite, Pi.single_apply]
  have h𝔪 : ↑(ϑ.normQ * D.M ^ 2) ∈ 𝔪.ideal := normQ_mul_M_pow_mem_modulus
  -- The kernels: `k₀`, `k₁` with their constants, and `θ w` as a linear map on polynomials.
  let k₀ (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) : ℂ :=
    c₀ * modKernelStdSpace (stdSpace D.E (Fin D.m)) (twistedChiMPow ϑ j) 1 (unitModulus D.E) 1 1
      (1, v)
      w
  let k₁ : ℂ := c₁ * modKernelStdSpace (stdSpace D.E (Fin j)) 1 b' 𝔪 Ψ 1 (1, 1) h
  let θ (w : Gf D.E D.CarrierIndex) : MvPolynomial (D.Φ × FirstFactorIndex j × AddedIndex j) ℂ →ₗ[ℂ]
    ℂ :=
    modKernelBilin (stdSpace D.E (AddedIndex j)) (stdSpace D.E (FirstFactorIndex j))
      (firstFactorChar ϑ j)
      (firstFactorChar ϑ j) 𝔪 (1, U.blockSumOne (1, U.blockSumOne (i.classRep, w))) (1, h)
      (addedDatum ϑ j u)
  have hy : star (scale • leftSideSeries ϑ j (u, i) h) =
      (D.chosenGroupOrder ^ 2 : ℂ) •
        stdClassSum (stdLevel D.E D.CarrierIndex) fun w ↦
          stdClassSum (stdLevel D.E (Fin D.m)) fun v ↦
          star ((k₀ v w * conj k₁) • c₂ • θ w ∘ (H • stackedDetProdCoords j i (D.shortRows i))) :=
    h_expand c₀ c₁ c₂ H u i ϑ h
  rw [hy]
  refine ⟨fun p _ _ hp ↦ ?_, fun hQ_empty φ ↦ ?_⟩
  · -- Integrality of each term of the double class sum.
    refine weylGauge_stdClassSum_stdClassSum_le_one h fun w v ↦ ?_
    -- The vector is a complex conjugate, so its factors are read at the place ι = `ιₚ ∘ conj`.
    let ι : ℂ →+* ℂ_[p] := ιₚ.comp conj
    have int₀ : ‖ι (k₀ v w)‖ ≤ 1 :=
      let _ : PadicPlace p := ⟨ι⟩
      norm_mul_modKernelStdSpace_twistedChiMPow_le_one K₀ v w
    have int₁ : ‖ιₚ k₁‖ ≤ 1 := norm_mul_modKernelStdSpace_one_le_one K₁ hb' h𝔪 hΨ hp h
    have gauge₂ : weylGauge (untwistedDescentPair j).colsPlus 0 h
        (star (c₂ • θ w ∘ (H • stackedDetProdCoords j i (D.shortRows i)))) ≤ 1 := by
      refine weylGauge_modKernelBilin_stackedDetProdCoords_le_one j i _ c₂ H
        (fun g' hg' h' hh' Y hY l ↦ ?_) w h
      let _ : PadicPlace p := ⟨ι⟩
      exact K₂.norm_le_one hb hb h𝔪 (addedDatum_mem_integralAway j u · ϑ.normQ)
        (isHomogeneous_iff_aeval_smul_X.2 (h_denom i Y l).aeval_smul_X) hp hg' hh'
        ((h_denom i Y l).mem_range _ hY)
    rw [star_smul, weylGauge_smul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans gauge₂
    simpa [ι] using (mul_le_of_le_one_left (norm_nonneg _) int₀).trans int₁
  · -- Size. With σ = φ ∘ conj, bound the σ-conjugates of the three kernels.
    let σ : ℂ ≃+* ℂ := starRingAut.trans φ
    have h_level : ϑ.normQ = 1 := by simp [hQ_empty]
    rw [h_level, one_mul] at h𝔪
    obtain ⟨hm, h_carrier, hj, h_first, h_added⟩ := card_le_gap j
    have size₀ (v : Gf D.E (Fin D.m)) (w : Gf D.E D.CarrierIndex) : ‖σ (k₀ v w)‖ ≤ rexp D.x₁ := by
      simpa [k₀] using K₀.norm_map_le hm h_carrier (Nat.zero_le _) (twistedChiMPow_hasWeight ϑ j)
        .one
        (𝔪 := unitModulus D.E) (Ψ := 1) (A := 1) (B := 1) Submodule.mem_top (by simp)
        (isHomogeneous_one _ _) σ (by simp) v w
    have size₁ : ‖σ (conj k₁)‖ ≤ rexp D.x₁ := by
      simpa [k₁] using K₁.norm_map_le hj h_first (Nat.zero_le _) .one hb' h𝔪 (Ψ := Ψ) (A := 1)
        (B := 1) (by simp [Ψ, apply_ite, ite_apply, Pi.single_apply]) (isHomogeneous_one _ _)
        (starRingAut.trans σ) (by simp) 1 h
    -- N bounds the datum `addedDatum`, and B the vector H·`stackedDetProdCoords` at small points.
    let N : ℕ := card (GL D.CarrierIndex (D.untwistedModulus 2).ResidueRing)
    let B : ℝ := √((H : ℝ) ^ 2 * (D.M ^ 9) ^ ((12 * D.m + 1) * q))
    -- By duality it is enough to bound the kernel at every Q that is small at the small points.
    refine weylNormSq_stdClassSum_stdClassSum_le rfl hn hn_le_M H_pos H_le φ fun w v ↦
      sqrt_weylNormSq_comp_le_of_eval_le σ ((k₀ v w * conj k₁) • c₂ • θ w)
        (S := {z | ∀ x, ‖σ (z x)‖ ≤ D.M ^ 4})
        (fun l ↦ isHomogeneous_iff_aeval_smul_X.2 (h_denom i (D.shortRows i) l).aeval_smul_X)
        (fun z hz ↦ sqrt_weylNormSq_smul_eval_stackedDetProdCoords_le j i h_detCount H σ hz)
        fun Q hQ_hom hQ_le ↦ ?_
    have size₂ : ‖σ (c₂ * θ w Q)‖ ≤ rexp D.x₁ * N * B :=
      K₂.norm_map_le h_added h_first hn_le_M hb hb h𝔪 (norm_map_addedDatum_le j u) hQ_hom σ hQ_le
        _ h
    simpa [mul_assoc] using norm_mul_le_of_le (norm_mul_le_of_le (size₀ v w) size₁) size₂

end New.Data

end
