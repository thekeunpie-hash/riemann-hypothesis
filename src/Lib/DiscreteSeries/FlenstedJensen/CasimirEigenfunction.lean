module

import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Separation.CompletelyRegular
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.DiscreteSeries.Holomorphic.HighestVectorExtension
public import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors
public import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
import Lib.DiscreteSeries.Haar.TotalMass
import Lib.General.LinearAlgebra.PolarDecomposition
import Lib.General.Measure.IdempotentKernel
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Germ
public import Lib.General.Analysis.GaussianIntegral
public import Lib.General.Analysis.HolomorphicIntegrals
import Lib.General.Analysis.MeanValueAndTaylor

section
/-!
# Integrals of densities over unitary groups and over the flag variety of `K_ℂ`

We study integrals over unitary groups `G = U(diag ε)` (`New.USign ε`) of functions that are
continuous on invertible matrices and transform under triangular matrices by the modulus character.
Here `New.IsBorelMatrix o b` says that `b` is invertible and upper triangular for the order `o`, `B`
denotes these triangular matrices, `New.diagChar (New.twoRho o _) b = ∏ i, b i i ^ (2ρ) i`, and `o`
is assumed injective. Integrals of such functions over `G` become integrals over an open part of
`U(n)`, and their integral over `U(n)` is invariant under left translation by invertible matrices.
As a consequence, a continuous function on the invertible block diagonal matrices `K_ℂ` that obeys
the same rule block by block has an integral over `K` that is invariant under `K_ℂ`.

## Main definitions and results

* `New.openOrbit`: the set `G B` of products of an element of `G` and a triangular matrix.
* `New.IsFlagDensity`: the transformation rule under triangular matrices.
* `New.integral_mul_left_eq_setIntegral_openOrbit`: the integral over `G` of a translate
  `F (x * g)` equals the integral over the part of `U(n)` in `x G B`.
* `New.integral_unitary_mul_left_of_density`: the integral over `U(n)` of such a function is
  invariant under left translation by an invertible matrix.
* `New.integral_haarK_mul_left_of_density`: the same for densities on `K_ℂ`, integrated over `K`.

Notions from other files:
* `New.USign ε`: the unitary group `U(J)` of the diagonal matrix of signs `J = New.signMatrix ε`.
* `New.twoRho l r`: the sum of the roots selected by `r` that are positive for `l`; its `i`-th entry
  is `#{j | r i j ∧ l j < l i} - #{j | r i j ∧ l i < l j}`.
* `New.lowerLiePart ε 1 o 2⁻¹`: the projection `X ↦ N - J Nᴴ J` to the Lie algebra of `U(J)`, where
  `N` is the part of `X` below the diagonal plus half its diagonal. `New.skewOfReal y` is the
  skew-Hermitian matrix with real coordinates `y`; `New.skewCoords` reads them back (real plus
  imaginary part over `√2` off the diagonal).
* `New.maxCompactU ε`, `New.haarK ε`: the group `K` of the elements of `U(J)` that commute with `J`,
  and its Haar measure of mass one.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Character.FormalDegree` and
`Lib.DiscreteSeries.FlenstedJensen.PsiKTypes` for sources.
-/

@[expose] public section

namespace New

/-!
## The open orbit of U(p,q) on flags and change of variables

* `New.lintegral_openOrbit_le`: an inequality between integrals over two unitary groups, each
  restricted to a translate of an open orbit.

The inequality holds for any two signatures, so using it both ways gives an equality.
-/

section OpenFlagOrbit

open Matrix MeasureTheory Complex ComplexOrder Norms.L2Operator LinearMap Finset U

variable {n : Type} [Fintype n] [DecidableEq n] {o : n → ℤ} {b c : Matrix n n ℂ}

/-- The set `G B` of matrices `g * b` with `g` in `U(diag ε)` and `b` invertible and upper
triangular for the order `o`: the preimage of an open orbit of `G` on flags. -/
def openOrbit (ε : n → ℤˣ) (o : n → ℤ) : Set (Matrix n n ℂ) :=
  {y : Matrix n n ℂ | ∃ g : USign ε, ∃ b : Matrix n n ℂ, IsBorelMatrix o b ∧ y = g * b}

/-- The function `F` on matrices is a density on the flags of the order `o`:
`F (y * b) = |∏ i, b i i ^ (2ρ) i| ^ 2 • F y` for `y` invertible and `b` invertible and upper
triangular for `o`, where `2ρ = twoRho o ⊤`. The matrices `b` are upper triangular in the order of
increasing `o`, so this `2ρ` is minus the sum of the roots of the triangular group. -/
def IsFlagDensity {E : Type*} [SMul ℝ E] (o : n → ℤ) (F : Matrix n n ℂ → E) : Prop :=
  ∀ (y : GL n ℂ) (b : Matrix n n ℂ), IsBorelMatrix o b →
    F (y * b) = ‖diagChar (twoRho o ⊤) b‖ ^ 2 • F y

/-- Uniqueness of the factorisation. Let `o` be injective. If `g * b = g' * c` with `g`, `g'` in
`U(diag ε)`, `b`, `c` triangular and all ratios `c i i / b i i` positive reals, then `g = g'`. -/
lemma IsBorelMatrix.unitary_eq_of_mul_eq (ho : o.Injective) (ε : n → ℤˣ) {g g' : USign ε}
    (hb : IsBorelMatrix o b) (hc : IsBorelMatrix o c) (h_eq : g * b = g' * c)
    (h_pos : ∀ i : n, 0 < c i i / b i i) : g = g' := by
  -- Write `g = g' * t`. Then `t = c * b⁻¹` is triangular and in the group, hence diagonal with
  -- entries `exp (θ i * I)` of norm one; these are the positive numbers `c i i / b i i`.
  obtain ⟨t, rfl⟩ : ∃ t : USign ε, g' * t = g := mul_left_surjective g' g
  obtain rfl : t * b = c := by simpa [mul_assoc] using h_eq
  have ht : IsBorelMatrix o t := by simpa [hb.right] using hc.mul hb.inv
  obtain ⟨θ, hθ⟩ : ∃ θ : n → ℝ, (t : Matrix n n ℂ) = diagonal fun i : n ↦ cexp (θ i * I) :=
    ht.exists_eq_diagonal_exp ho
  have h_one (i : n) : cexp (θ i * I) = 1 := by
    simpa [hθ, hb.diag_ne_zero ho] using eq_coe_norm_of_nonneg (h_pos i).le
  exact Subtype.ext (Units.ext (by simp [hθ, h_one]))

/-- Let `o` be injective and `b` triangular. If `y` vanishes at all entries further below the
diagonal than `(i, j)`, then conjugation by `b` multiplies the entry `(i, j)` of `y` by
`b i i * b⁻¹ j j`. -/
lemma IsBorelMatrix.mul_mul_inv_apply (ho : o.Injective) (hb : IsBorelMatrix o b)
    {y : Matrix n n ℂ} {i j : n} (hy : ∀ k l : n, o i - o j < o k - o l → y k l = 0) :
    (b * y * b⁻¹) i j = b i i * y i j * b⁻¹ j j := by
  simp_rw [Matrix.mul_apply, sum_mul, ← sum_product']
  refine sum_eq_single_of_mem (j, i) (by simp) fun ⟨l, k⟩ _ h_ne ↦ ?_
  -- An outer factor vanishes unless `o i ≤ o k` and `o l ≤ o j`; in that case `y k l` vanishes.
  have b_tri : o k < o i → b i k = 0 := fun h ↦ hb.left h
  have inv_tri : o j < o l → b⁻¹ l j = 0 := fun h ↦ hb.inv.left h
  have h_further : o i ≤ o k → o l ≤ o j → o i - o j < o k - o l := by grind [Function.Injective]
  change b i k * y k l * b⁻¹ l j = 0
  grind

/-- Let `o` be injective and `J = diag ε`. The real coordinates (`skewCoords`: real plus imaginary
part, divided by `√2` off the diagonal) of `J * (N - J Nᴴ J)`, where `N` is the part of `Z` below
the diagonal plus half its diagonal, in terms of the entries of `Z` on and below the diagonal. -/
lemma skewCoords_signMatrix_mul_lowerLiePart_apply (ho : o.Injective) (ε : n → ℤˣ)
    (Z : Matrix n n ℂ) (i j : n) :
    skewCoords (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i j =
      if o j < o i then ε i * ((Z i j).re + (Z i j).im) / √2
      else if o i < o j then ε j * ((Z j i).im - (Z j i).re) / √2
      else ε i * (Z i i).im := by
  -- With `N` the part of `Z` below the diagonal plus half its diagonal, the matrix is
  -- `J * (N - J * Nᴴ * J) = J * N - Nᴴ * J`. In each case we compute its entry `(i, j)`.
  have h_sign : (ε i * ε i : ℂ) = 1 := by exact_mod_cast Int.units_coe_mul_self (ε i)
  rcases lt_trichotomy (o i) (o j) with h_lt | h_eq | h_gt
  · have h_ne : i ≠ j := ne_of_apply_ne o h_lt.ne
    have h_entry : (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i j = -(star (Z j i) * ε j) := by
      simp [lowerLiePart, signMatrix, h_lt, h_lt.not_gt, h_ne.symm, h_ne, ← mul_assoc, h_sign]
    simp [skewCoords, h_entry, h_lt, h_lt.not_gt, h_ne, field, neg_add_eq_sub]
  · obtain rfl : i = j := ho h_eq
    have h_entry : (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i i = ε i * (Z i i).im * I := by
      simp [lowerLiePart, signMatrix, mul_sub, ← mul_assoc, h_sign, im_eq_sub_conj, field]
    simp [skewCoords, h_entry]
  · have h_ne : i ≠ j := ne_of_apply_ne o h_gt.ne'
    have h_entry : (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ Z) i j = ε i * Z i j := by
      simp [lowerLiePart, signMatrix, h_gt, h_gt.not_gt, h_ne.symm, h_ne]
    simp [skewCoords, h_entry, h_gt, h_ne, mul_add]

section

omit [Fintype n]

/-- Off the diagonal, the coordinate `y i j` is read off from the entry `(i, j)` of
`skewOfReal y`. -/
lemma re_add_im_skewOfReal_div (y : Matrix n n ℝ) {i j : n} (h_ne : i ≠ j) :
    ((skewOfReal y i j).re + (skewOfReal y i j).im) / √2 = y i j := by
  simp [skewOfReal, h_ne, ← add_div, div_div]

/-- Off the diagonal, the coordinate `y i j` is read off from the entry `(j, i)` of
`skewOfReal y`. -/
lemma im_sub_re_skewOfReal_swap_div (y : Matrix n n ℝ) {i j : n} (h_ne : i ≠ j) :
    ((skewOfReal y j i).im - (skewOfReal y j i).re) / √2 = y i j := by
  simp [skewOfReal, h_ne.symm, ← sub_div, div_div]

lemma im_skewOfReal_diag (y : Matrix n n ℝ) (i : n) : (skewOfReal y i i).im = y i i := by
  simp [skewOfReal]

end

omit [DecidableEq n] in
/-- Let `o` be injective and `d` a vector with nonzero entries. The product over all pairs
`(i, j)` of the ratio of `d` at the later index to `d` at the earlier index is
`(∏ i, d i ^ (2ρ) i) ^ 2`, where `2ρ = twoRho o ⊤`. -/
lemma prod_prod_ite_div_eq_prod_zpow_twoRho_sq (ho : o.Injective) {d : n → ℝ}
    (hd : ∀ i : n, d i ≠ 0) :
    (∏ i : n, ∏ j : n, if o i < o j then d j / d i else d i / d j) =
      (∏ i : n, d i ^ twoRho o ⊤ i) ^ 2 := by
  let r (i j : n) : ℝ := (if o j < o i then d i else 1) / if o i < o j then d i else 1
  have h_row (i : n) : d i ^ twoRho o ⊤ i = ∏ j : n, r i j := by
    simp [r, twoRho, zpow_sub₀ (hd i), prod_div_distrib, ← prod_filter]
  have h_pair (i j : n) : (if o i < o j then d j / d i else d i / d j) = r i j * r j i := by
    rcases lt_trichotomy (o i) (o j) with h_lt | h_eq | h_gt
    · simp [r, h_lt, h_lt.not_gt, div_eq_inv_mul]
    · simp [r, hd, ho h_eq]
    · simp [r, h_gt, h_gt.not_gt, div_eq_mul_inv]
  calc _ = (∏ i : n, ∏ j : n, r i j) * ∏ i : n, ∏ j : n, r j i := by
        simp only [h_pair, prod_mul_distrib]
    _ = (∏ i : n, ∏ j : n, r i j) ^ 2 := by rw [sq, prod_comm (f := fun i j : n ↦ r j i)]
    _ = (∏ i : n, d i ^ twoRho o ⊤ i) ^ 2 := by simp only [h_row]

/-- The Jacobian. Let `o` be injective, `b` triangular with positive diagonal, `J = diag ε`,
`J' = diag ε'`. Take a skew-Hermitian `Y` (real coordinates `New.skewOfReal`), conjugate `J' * Y` by
`b`, and project to the Lie algebra of `U(J)` by `New.lowerLiePart ε 1 o 2⁻¹`, the map
`X ↦ N - J Nᴴ J` with `N = lowerMask 1 o X` plus half the diagonal of `X`. Then multiply by `J` and
read off coordinates by `New.skewCoords`. The determinant of this real linear map has absolute value
`|∏ i, b i i ^ (2ρ) i| ^ 2`, where `(2ρ) i = #{j | o j < o i} - #{j | o i < o j}`. -/
lemma abs_det_lowerLiePart (ho : o.Injective) (ε : n → ℤˣ) (hb : IsBorelMatrix o b)
    (h_pos : ∀ i : n, 0 < b i i) (ε' : n → ℤˣ) :
    |(skewCoords ∘ₗ mulLeft ℝ (signMatrix ε) ∘ₗ lowerLiePart ε 1 o 2⁻¹ ∘ₗ
        mulLeftRight ℝ (b, b⁻¹) ∘ₗ mulLeft ℝ (signMatrix ε') ∘ₗ skewOfReal).det| =
      ‖diagChar (twoRho o ⊤) b‖ ^ 2 := by
  -- Order the pairs `(i, j)` first by their distance `|o i - o j|` from the diagonal. Conjugation
  -- by `b` multiplies an entry by `b i i / b j j` and adds only entries further below the diagonal,
  -- so the matrix `T` of the map is triangular, and we multiply its diagonal entries.
  let key (p : n × n) : ℤ ×ₗ ℤ ×ₗ ℤ := toLex (|o p.1 - o p.2|, toLex (o p.1, o p.2))
  have key_inj : key.Injective := fun p q h_key ↦ by simp_all [key, ho.eq_iff, Prod.ext_iff]
  let pairOrder : LinearOrder (n × n) := .lift' key key_inj
  have h_real (i : n) : ∃ d : ℝ, 0 < d ∧ (d : ℂ) = b i i := RCLike.pos_iff_exists_ofReal.1 (h_pos i)
  choose d hd_pos hd using h_real
  rw [← det_toMatrix (stdBasis ℝ n n)]
  set T : Matrix (n × n) (n × n) ℝ := toMatrix (stdBasis ℝ n n) (stdBasis ℝ n n) _ with hT_def
  -- Column `q` of `T` holds the coordinates of the image of `Z q = b * (J' * Y q) * b⁻¹`.
  let Y (q : n × n) : Matrix n n ℂ := skewOfReal (Matrix.single q.1 q.2 1)
  let Z (q : n × n) : Matrix n n ℂ := b * (signMatrix ε' * Y q) * b⁻¹
  have T_apply (p q : n × n) :
      T p q = skewCoords (signMatrix ε * lowerLiePart ε 1 o 2⁻¹ (Z q)) p.1 p.2 := by
    simp [hT_def, Z, Y, toMatrix_apply, stdBasis, single_eq_of_single_single]
  have Z_apply (q : n × n) (i j : n) (h_dist : |o q.1 - o q.2| ≤ o i - o j) :
      Z q i j = (ε' i * d i / d j : ℝ) * Y q i j := by
    have h_zero (k l : n) (h_further : o i - o j < o k - o l) : (signMatrix ε' * Y q) k l = 0 := by
      have h_ne : ¬(q.1 = k ∧ q.2 = l) ∧ ¬(q.1 = l ∧ q.2 = k) := by grind
      simp [Y, signMatrix, skewOfReal, Matrix.single_apply, h_ne]
    calc Z q i j = b i i * (signMatrix ε' * Y q) i j * b⁻¹ j j := hb.mul_mul_inv_apply ho h_zero
      _ = _ := by simp [signMatrix, hb.inv_apply_diag ho, hd, field]
  -- The entries of `T` on and below its diagonal.
  let x (i j : n) : ℝ := ε i * (ε' i * d i / d j)
  have hT (i j : n) (q : n × n) (hq : q ≤ (i, j)) :
      T (i, j) q = (if o i < o j then x j i else x i j) * Matrix.single q.1 q.2 1 i j := by
    have h_dist : |o q.1 - o q.2| ≤ |o i - o j| := Prod.Lex.monotone_fst _ _ hq
    rw [T_apply, skewCoords_signMatrix_mul_lowerLiePart_apply ho]
    rcases lt_trichotomy (o i) (o j) with h_lt | h_eq | h_gt
    · rw [ite_eq_right h_lt.not_gt, ite_eq_left h_lt, ite_eq_left h_lt, Z_apply q j i (by grind),
        re_ofReal_mul, im_ofReal_mul,
        ← im_sub_re_skewOfReal_swap_div (Matrix.single q.1 q.2 1) (ne_of_apply_ne o h_lt.ne)]
      ring
    · obtain rfl : i = j := ho h_eq
      simp [Z_apply q i i (by simpa using h_dist), Y, im_skewOfReal_diag, x, mul_assoc]
    · rw [ite_eq_left h_gt, ite_eq_right h_gt.not_gt, Z_apply q i j (by grind), re_ofReal_mul,
        im_ofReal_mul, ← re_add_im_skewOfReal_div (Matrix.single q.1 q.2 1)
          (ne_of_apply_ne o h_gt.ne')]
      ring
  have h_tri : T.IsUpperTriangular := fun p q (hq : q < p) ↦ by
    rw [hT p.1 p.2 q hq.le, single_apply_of_ne _ _ _ _ _ (Prod.ext_iff.not.1 hq.ne), mul_zero]
  have h_abs (i j : n) : |T (i, j) (i, j)| = if o i < o j then d j / d i else d i / d j := by
    simp [hT, x, apply_ite abs, abs_div, abs_mul, abs_unit_intCast, abs_of_pos (hd_pos _)]
  calc |T.det| = ∏ i : n, ∏ j : n, if o i < o j then d j / d i else d i / d j := by
        simp only [det_of_isUpperTriangular h_tri, abs_prod, Fintype.prod_prod_type, h_abs]
    _ = (∏ i : n, d i ^ twoRho o ⊤ i) ^ 2 :=
        prod_prod_ite_div_eq_prod_zpow_twoRho_sq ho fun i ↦ (hd_pos i).ne'
    _ = ‖diagChar (twoRho o ⊤) b‖ ^ 2 := by simp [diagChar, ← hd, abs_of_pos (hd_pos _)]

/-- For injective `o`, a point of the open orbit is `g * b` with `g` in `U(diag ε)` and `b`
triangular with positive diagonal. -/
lemma exists_mul_isBorelMatrix_of_mem_openOrbit (ho : o.Injective) (ε : n → ℤˣ) {y : Matrix n n ℂ}
    (hy : y ∈ openOrbit ε o) :
    ∃ g : USign ε, ∃ b : Matrix n n ℂ, IsBorelMatrix o b ∧ (∀ i : n, 0 < b i i) ∧ g * b = y := by
  obtain ⟨g, b, hb, rfl⟩ := hy
  -- Move the phases of the diagonal of `b` into `g`.
  let t : USign ε := diagTorus ε fun i : n ↦
    ⟨‖b i i‖ / b i i, by simp [Submonoid.unitSphere, hb.diag_ne_zero ho]⟩
  have ht : IsBorelMatrix o t := ⟨blockTriangular_diagonal _, GeneralLinearGroup.det_ne_zero t.val⟩
  refine ⟨g * t⁻¹, t * b, ht.mul hb, fun i ↦ ?_, by simp [mul_assoc]⟩
  simp [t, diagTorus, hb.diag_ne_zero ho]

/-- A chart at `1` for the factorisation. There is `ψ` with `ψ 1 = 0` and derivative the identity
at `1` such that each matrix `x` near `1` is `exp (L (ψ x)) * b`, where
`L = lowerLiePart ε 1 o 2⁻¹` takes values in the Lie algebra of `U(diag ε)` and `b` is triangular
with positive diagonal. -/
lemma exists_chart_exp_lowerLiePart_mul_borel (ε : n → ℤˣ) (o : n → ℤ) :
    ∃ ψ : Matrix n n ℂ → Matrix n n ℂ,
      HasFDerivAt ψ (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) 1 ∧ ψ 1 = 0 ∧
      ∀ᶠ x : Matrix n n ℂ in nhds 1, ∃ b : Matrix n n ℂ, IsBorelMatrix o b ∧
        (∀ i : n, 0 < b i i) ∧ x = NormedSpace.exp (lowerLiePart ε 1 o 2⁻¹ (ψ x)) * b := by
  set L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := lowerLiePart ε 1 o 2⁻¹
  have L_lower (Z : Matrix n n ℂ) : lowerMask 1 o (L Z) = lowerMask 1 o Z := by
    simp [L, lowerLiePart, signMatrix]
    grind
  obtain ⟨ψ, ⟨ψ_deriv, ψ_one⟩, chart⟩ :=
    exists_borel_chart 1 o L hasStrictFDerivAt_exp_zero NormedSpace.exp_zero (by simp) L_lower
  have accretive : ∀ᶠ x : Matrix n n ℂ in nhds 1, (1 + ψ x).IsAccretive :=
    ψ_deriv.continuousAt.const_add 1
      (IsAccretive.setOf_mem_nhds (by simp [ψ_one, PosDef.one.isAccretive]))
  refine ⟨ψ, ψ_deriv, ψ_one, (chart.and accretive).mono fun x ⟨hx, x_accretive⟩ ↦ ?_⟩
  obtain ⟨tri, -, x_eq⟩ := hx (by simp)
  refine ⟨1 + (1 - L) (ψ x), tri, fun i ↦ ?_, x_eq⟩
  -- The diagonal of `1 + (1 - L) (ψ x)` is the real part of that of `1 + ψ x`.
  simpa [L, lowerLiePart, lt_def, ← two_mul, signMatrix, mul_right_comm, ← Int.cast_mul]
    using x_accretive.diag_pos

/-- The set `openOrbit ε o = G B` is a neighbourhood of each of its points. -/
lemma openOrbit_mem_nhds (ε : n → ℤˣ) {y : Matrix n n ℂ} (hy : y ∈ openOrbit ε o) :
    openOrbit ε o ∈ nhds y := by
  obtain ⟨g, c, hc, rfl⟩ := hy
  obtain ⟨ψ, -, -, chart⟩ := exists_chart_exp_lowerLiePart_mul_borel ε o
  -- Carry the chart at `1` to `g * c` by the map `A` that takes `g * c` to `1`.
  let A : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := .mulLeftRight ℝ _ (g : Matrix n n ℂ)⁻¹ c⁻¹
  have A_tendsto : Filter.Tendsto A (nhds (g * c)) (nhds 1) :=
    A.cont.tendsto' (g * c) 1 (by simp [A, hc.2])
  filter_upwards [A_tendsto.eventually chart] with x ⟨b, hb, _, A_x⟩
  let u : USign ε := expU ⟨_, lowerLiePart_mem_unitaryLie ε 1 o 2⁻¹ (ψ (A x))⟩
  refine ⟨g * u, b * c, hb.mul hc, ?_⟩
  calc x = g * A x * c := by simp [A, mul_assoc, hc.2]
    _ = (g * u : USign ε) * (b * c) := by
      rw [A_x]
      simp [u, mul_assoc]

/-- Let `o` be injective and `y = Φ y * B y` for `y` in the open orbit, with `Φ y` in `U(diag ε)`
and `B y` triangular with positive diagonal. Then at each point `y` of the orbit `Φ` has the
derivative `Z ↦ Φ y * L ((Φ y)⁻¹ * Z * (B y)⁻¹)`, where `L = lowerLiePart ε 1 o 2⁻¹`. -/
lemma hasFDerivAt_unitary_factor_of_mem_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {Φ : Matrix n n ℂ → USign ε} {B : Matrix n n ℂ → Matrix n n ℂ}
    (tri : ∀ y ∈ openOrbit ε o, IsBorelMatrix o (B y))
    (pos : ∀ y ∈ openOrbit ε o, ∀ i : n, 0 < B y i i) (factor : ∀ y ∈ openOrbit ε o, Φ y * B y = y)
    {y : Matrix n n ℂ} (hy : y ∈ openOrbit ε o) :
    HasFDerivAt (fun x : Matrix n n ℂ ↦ (Φ x : Matrix n n ℂ))
      ((Φ y : Matrix n n ℂ) • lowerLiePart ε 1 o 2⁻¹ ∘L
        ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (Φ y : Matrix n n ℂ)⁻¹ (B y)⁻¹) y := by
  obtain ⟨ψ, ψ_deriv, ψ_one, chart⟩ := exists_chart_exp_lowerLiePart_mul_borel ε o
  set L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := lowerLiePart ε 1 o 2⁻¹
  -- Carry the chart at `1` to `y` by the map `A` that takes `y` to `1`.
  let A : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := .mulLeftRight ℝ _ (Φ y : Matrix n n ℂ)⁻¹ (B y)⁻¹
  have A_y : A y = 1 := by simpa [A, (tri y hy).2] using (congrArg A (factor y hy)).symm
  have near : ∀ᶠ x : Matrix n n ℂ in nhds y,
      (Φ x : Matrix n n ℂ) = Φ y * NormedSpace.exp (L (ψ (A x))) := by
    filter_upwards [(A.cont.tendsto' y 1 A_y).eventually chart, openOrbit_mem_nhds ε hy]
      with x ⟨b, tri_b, pos_b, (A_x : A x = NormedSpace.exp (L (ψ (A x))) * b)⟩ hx
    let u : USign ε := expU ⟨L (ψ (A x)), lowerLiePart_mem_unitaryLie ε 1 o 2⁻¹ (ψ (A x))⟩
    have x_eq : Φ x * B x = (Φ y * u : USign ε) * (b * B y) := by
      simpa [factor x hx, A, u, mul_assoc, (tri y hy).2]
        using congrArg ((Φ y : Matrix n n ℂ) * · * B y) A_x
    -- Both factorisations of `x` have positive diagonal, so they agree.
    rw [(tri x hx).unitary_eq_of_mul_eq ho ε (tri_b.mul (tri y hy)) x_eq fun i ↦ ?_]
    · simp [u]
    · simp [tri_b.mul_apply_diag ho (tri y hy), pos_b, pos y hy, pos x hx]
  -- So near `y` the map `Φ` is `Φ y * exp (L (ψ (A x)))`; differentiate.
  have exp_deriv : HasFDerivAt (fun x : Matrix n n ℂ ↦ NormedSpace.exp (L (ψ x))) L (A y) := by
    rw [A_y]
    exact HasFDerivAt.comp 1 (g' := 1) (by simpa [ψ_one] using hasFDerivAt_exp_zero)
      (L.hasFDerivAt.comp 1 ψ_deriv)
  exact ((exp_deriv.comp y A.hasFDerivAt).const_mul (Φ y)).congr_of_eventuallyEq near

lemma isOpen_openOrbit (ε : n → ℤˣ) (o : n → ℤ) : IsOpen (openOrbit ε o) :=
  isOpen_iff_mem_nhds.2 fun _ hy ↦ openOrbit_mem_nhds ε hy

/-- Let `o` be injective and `y = Φ y * B y` for `y` in the open orbit, with `Φ y` in `U(diag ε)`
and `B y` triangular with positive diagonal. Let `c` map real matrices to `U(diag ε')`, be
differentiable at `y`, and let `x * c y` lie in the orbit. Then the Jacobian of `z ↦ Φ (x * c z)` at
`y` (the absolute value of the determinant of the logarithmic derivative
`logDerivU f y v = (f y)ᴴ * J * f' v` (`J` the sign matrix of the group of `f`, `f'` the derivative
of `f` at `y`) in the real coordinates `skewCoords`) is `|∏ i, b i i ^ (2ρ) i| ^ 2` times that of
`c`, where `b = B (x * c y)` and `2ρ = twoRho o ⊤`. -/
lemma abs_det_logDerivU_unitary_factor (ho : o.Injective) {ε ε' : n → ℤˣ}
    {Φ : Matrix n n ℂ → USign ε} {B : Matrix n n ℂ → Matrix n n ℂ}
    (tri : ∀ y ∈ openOrbit ε o, IsBorelMatrix o (B y))
    (pos : ∀ y ∈ openOrbit ε o, ∀ i : n, 0 < B y i i) (factor : ∀ y ∈ openOrbit ε o, Φ y * B y = y)
    (x : GL n ℂ) {c : Matrix n n ℝ → USign ε'} {y : Matrix n n ℝ} (c_diff : DifferentiableAtU c y)
    (hy : (x : Matrix n n ℂ) * c y ∈ openOrbit ε o) :
    |(skewCoords ∘ₗ logDerivU (fun z : Matrix n n ℝ ↦ Φ (x * c z)) y).det| =
      ‖diagChar (twoRho o ⊤) (B (x * c y))‖ ^ 2 * |(skewCoords ∘ₗ logDerivU c y).det| := by
  -- Write `x * c y = u * b`, `J = signMatrix ε`, `J' = signMatrix ε'` and `dc` for the derivative
  -- of `c`. The derivative of `Φ (x * c z)` is `u * L (u⁻¹ * x * dc * b⁻¹)`, and
  -- `u⁻¹ * x * dc = b * J' * logDerivU c y` with `logDerivU c y` skew-Hermitian.
  set L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := lowerLiePart ε 1 o 2⁻¹
  let u : USign ε := Φ (x * c y)
  let b : Matrix n n ℂ := B (x * c y)
  let dc : Matrix n n ℝ →L[ℝ] Matrix n n ℂ := fderiv ℝ (fun z ↦ (c z : Matrix n n ℂ)) y
  have deriv : HasFDerivAt (fun z : Matrix n n ℝ ↦ (Φ (x * c z) : Matrix n n ℂ))
      (((u : Matrix n n ℂ) • L ∘L .mulLeftRight ℝ _ (u : Matrix n n ℂ)⁻¹ b⁻¹) ∘L
        ((x : Matrix n n ℂ) • dc)) y :=
    (hasFDerivAt_unitary_factor_of_mem_openOrbit ho ε tri pos factor hy).comp y
      (f := fun z ↦ (x : Matrix n n ℂ) * c z) (c_diff.hasFDerivAt.const_mul _)
  have x_eq : (x : Matrix n n ℂ) = u * b * (c y : Matrix n n ℂ)⁻¹ := by simp [u, b, factor _ hy]
  have h_log (v : Matrix n n ℝ) : logDerivU (fun z : Matrix n n ℝ ↦ Φ (x * c z)) y v =
      signMatrix ε * L (b * (signMatrix ε' * logDerivU c y v) * b⁻¹) :=
    calc _ = (u : Matrix n n ℂ)ᴴ * signMatrix ε * u * L ((u : Matrix n n ℂ)⁻¹ * (x * dc v) * b⁻¹) :=
        by simp [logDerivU, deriv.fderiv, u, mul_assoc]
      _ = _ := by simp [show (u : Matrix n n ℂ)ᴴ * _ * _ = _ from mem_unitaryGroupOf_iff.1 u.prop,
          x_eq, dc, logDerivU, inv_coe_eq_mul_conjTranspose_mul (c y),
        ← mul_assoc]
  have h_comp : skewCoords ∘ₗ logDerivU (fun z : Matrix n n ℝ ↦ Φ (x * c z)) y =
      (skewCoords ∘ₗ mulLeft ℝ (signMatrix ε) ∘ₗ L ∘ₗ mulLeftRight ℝ (b, b⁻¹) ∘ₗ
        mulLeft ℝ (signMatrix ε') ∘ₗ skewOfReal) ∘ₗ skewCoords ∘ₗ logDerivU c y :=
    LinearMap.ext fun v ↦ by simp [h_log, conjTranspose_logDerivU c_diff]
  rw [h_comp, det_comp, abs_mul, abs_det_lowerLiePart ho ε (tri _ hy) (pos _ hy) ε']

/-- Change of variables on flags. Let `o` be injective, `B` its triangular group, `x` invertible and
`f` a real density on flags (it scales under `B` by the modulus character). Then the integral of the
positive part of `f` over `x U(ε') ∩ U(ε) B`, for the Haar measure `volume` of `U(ε')` (in Cayley's
chart `cayleyChart`, the density `cayleyDensity / volU (card n)`, as for every signature) moved by
`x`, is at most that over `U(ε) ∩ x U(ε') B`. -/
lemma lintegral_openOrbit_le (ho : o.Injective) (ε ε' : n → ℤˣ) (x : GL n ℂ) (f : Matrix n n ℂ → ℝ)
    (hf : IsFlagDensity o f) :
    ∫⁻ g : USign ε', (openOrbit ε o).indicator (ENNReal.ofReal ∘ f) (x * g) ≤
      ∫⁻ g : USign ε, {y : Matrix n n ℂ | (x : Matrix n n ℂ)⁻¹ * y ∈ openOrbit ε' o}.indicator
        (ENNReal.ofReal ∘ f) g := by
  -- Factor each `y` of the orbit as `Φ y * B y`, with `B y` triangular with positive diagonal.
  choose! Φ B tri pos factor using fun y : Matrix n n ℂ ↦
    exists_mul_isBorelMatrix_of_mem_openOrbit ho ε (y := y)
  have Φ_eq (y : Matrix n n ℂ) (hy : y ∈ openOrbit ε o) : y * (B y)⁻¹ = Φ y := by
    simpa [(tri y hy).2] using congrArg (· * (B y)⁻¹) (factor y hy).symm
  -- Change variables by `g ↦ Φ (x * g)` from `U(ε')`, in Cayley's chart `c` on `D`, to `U(ε)`.
  let c : Matrix n n ℝ → USign ε' := cayleyChart (signMatrix ε')
  let D : Set (Matrix n n ℝ) := {y | (cayleyDenom (signMatrix ε') y).det ≠ 0}
  let S : Set (Matrix n n ℝ) := {y | (x : Matrix n n ℂ) * c y ∈ openOrbit ε o}
  have h_open : IsOpen {g : USign ε' | (x : Matrix n n ℂ) * g ∈ openOrbit ε o} :=
    (isOpen_openOrbit ε o).preimage (by fun_prop)
  have hS : MeasurableSet S := measurable_cayleyChart h_open.measurableSet
  -- `c y * (B (x * c y))⁻¹ = x⁻¹ * Φ (x * c y)` is a factorisation for `U(ε')`, which is unique.
  have inj : (S ∩ D).InjOn fun y ↦ Φ (x * c y) := by
    rintro z ⟨hzS, hzD⟩ y ⟨hyS, hyD⟩ (hΦ : Φ (x * c z) = Φ (x * c y))
    have h_eq : c z * (B (x * c z))⁻¹ = c y * (B (x * c y))⁻¹ :=
      x.isUnit.mul_left_cancel (by simp only [← mul_assoc, Φ_eq _ hzS, Φ_eq _ hyS, hΦ])
    have h_pos (i : n) : 0 < (B (x * c y))⁻¹ i i / (B (x * c z))⁻¹ i i := by
      simp [(tri _ hzS).inv_apply_diag ho, (tri _ hyS).inv_apply_diag ho, pos _ hzS, pos _ hyS]
    exact cayleyChart_injOn hzD hyD
      ((tri _ hzS).inv.unitary_eq_of_mul_eq ho ε' (tri _ hyS).inv h_eq h_pos)
  -- The Jacobian is the density `w y` of `c` times the modulus character `m y` of `B (x * c y)`.
  let w (y : Matrix n n ℝ) : ℝ := cayleyDensity (signMatrix ε') y
  let m (y : Matrix n n ℝ) : ℝ := ‖diagChar (twoRho o ⊤) (B (x * c y))‖ ^ 2
  have jac (y : Matrix n n ℝ) (hy : y ∈ S ∩ D) : DifferentiableAtU (fun z ↦ Φ (x * c z)) y ∧
      |(skewCoords ∘ₗ logDerivU (fun z ↦ Φ (x * c z)) y).det| = m y * w y := by
    obtain ⟨hyS, hyD⟩ := hy
    obtain ⟨c_diff : DifferentiableAtU c y, c_jac⟩ := abs_det_logDerivU_cayleyChart hyD
    have Φ_diff : DifferentiableAt ℝ (fun v : Matrix n n ℂ ↦ (Φ v : Matrix n n ℂ)) (x * c y) :=
      (hasFDerivAt_unitary_factor_of_mem_openOrbit ho ε tri pos factor hyS).differentiableAt
    refine ⟨Φ_diff.comp (f := fun z ↦ (x : Matrix n n ℂ) * c z) y (c_diff.const_mul _), ?_⟩
    rw [abs_det_logDerivU_unitary_factor ho tri pos factor x c_diff hyS, c_jac]
  -- Change of variables, up to a scalar `u = exp (i t)` that left invariance removes again.
  let vol : ℝ := volU (Fintype.card n)
  obtain ⟨u, change⟩ : ∃ u : USign ε, ∀ F : USign ε → ENNReal,
      ∫⁻ y in S ∩ D, .ofReal (m y * w y / vol) * F (u * Φ (x * c y)) ≤ ∫⁻ g, F g :=
    (Haar.lintegral_chart_rotate_le (.refl ℝ (Matrix n n ℝ)) (.id volume)
      (hS.inter (by measurability)) inj (fun y hy ↦ (jac y hy).1)
      fun y hy ↦ (jac y hy).2).exists.elim fun t ht ↦ ⟨circleScalar t, ht⟩
  let F (g : USign ε) : ENNReal :=
    {y : Matrix n n ℂ | (x : Matrix n n ℂ)⁻¹ * y ∈ openOrbit ε' o}.indicator (.ofReal ∘ f) g
  have pointwise (y : Matrix n n ℝ) :
      .ofReal (w y / vol) * (openOrbit ε o).indicator (ENNReal.ofReal ∘ f) (x * c y) =
        S.indicator (fun y ↦ .ofReal (m y * w y / vol) * F (Φ (x * c y))) y := by
    -- For `g = c y`: `x⁻¹ Φ (x g) = g (B (x g))⁻¹` lies in `U(ε') B`, and `x g = Φ (x g) B (x g)`.
    by_cases mem : (x : Matrix n n ℂ) * c y ∈ openOrbit ε o
    · have mem_inv : (x : Matrix n n ℂ)⁻¹ * Φ (x * c y) ∈ openOrbit ε' o :=
        ⟨c y, (B (x * c y))⁻¹, (tri _ mem).inv, by simp [← Φ_eq _ mem, mul_assoc]⟩
      have f_eq : f (x * c y) = m y * f (Φ (x * c y)) := by
        simpa only [factor _ mem, smul_eq_mul] using hf (Φ (x * c y)) (B (x * c y)) (tri _ mem)
      simp [S, F, m, mem_inv, mem, f_eq, mul_left_comm, mul_assoc, mul_div_assoc]
    · simp [S, mem]
  calc _ = ∫⁻ y in D, .ofReal (w y / vol) * (openOrbit ε o).indicator (.ofReal ∘ f) (x * c y) :=
        lintegral_eq_cayleyChart _
    _ = ∫⁻ y in S ∩ D, .ofReal (m y * w y / vol) * F (Φ (x * c y)) := by
        rw [lintegral_congr pointwise, setLIntegral_indicator hS]
    _ ≤ ∫⁻ g, F (u⁻¹ * g) := by simpa only [inv_mul_cancel_left] using change fun g ↦ F (u⁻¹ * g)
    _ = ∫⁻ g, F g := lintegral_mul_left_eq_self F u⁻¹

/-- By Gram-Schmidt every invertible matrix is a unitary times a triangular matrix. -/
lemma mem_openOrbit_one (o : n → ℤ) (y : GL n ℂ) : (y : Matrix n n ℂ) ∈ openOrbit 1 o := by
  obtain ⟨b, b_tri, b_unit⟩ := exists_orthonormal_mul o ⟨y.inv, y.inv_val⟩
  exact ⟨⟨y * b, by simpa [mem_unitaryGroupOf_iff, star_eq_conjTranspose] using b_unit⟩,
      (b : Matrix n n ℂ)⁻¹,
    IsBorelMatrix.inv ⟨b_tri, GeneralLinearGroup.det_ne_zero b⟩, by simp⟩
end OpenFlagOrbit

/-!
## Integrals of densities over unitary groups

Both directions of the inequality `New.lintegral_openOrbit_le` give an integral formula for complex
valued densities on the flags of `GL n ℂ`.
-/

section UnitaryIntegrals

open Matrix MeasureTheory Complex ComplexOrder Norms.L2Operator LinearMap Finset U

variable {n : Type} [Fintype n] [DecidableEq n] {o : n → ℤ}
/-- Let `o` be injective, `B` its triangular group, `f` a real density on flags and `x`
invertible. Then the integral of the positive part of `g ↦ f (x * g)` over `U(ε)` is that of the
positive part of `f` over `U(n) ∩ x U(ε) B`. -/
lemma lintegral_mul_left_eq_setLIntegral_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {f : Matrix n n ℂ → ℝ} (hf : IsFlagDensity o f) (x : GL n ℂ) :
    ∫⁻ g : USign ε, ENNReal.ofReal (f (x * g)) =
      ∫⁻ k in {k : USign (1 : n → ℤˣ) | (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit ε o},
        ENNReal.ofReal (f k) := by
  classical
  have h_meas : MeasurableSet {k : USign (1 : n → ℤˣ) | (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit ε o} :=
    ((isOpen_openOrbit ε o).preimage (by fun_prop)).measurableSet
  have h_mem (g : USign ε) : (x : Matrix n n ℂ) * g ∈ openOrbit 1 o := mem_openOrbit_one o (x * g)
  have hf_translate : IsFlagDensity o fun y : Matrix n n ℂ ↦ f (x * y) :=
    fun y b hb ↦ by simpa [mul_assoc] using hf (x * y) b hb
  rw [← lintegral_indicator h_meas]
  apply le_antisymm
  · simpa [h_mem, Set.indicator] using lintegral_openOrbit_le ho 1 ε x f hf
  · simpa [h_mem, Set.indicator, ← mul_assoc] using lintegral_openOrbit_le ho ε 1 x⁻¹ _ hf_translate

/-- Let `o` be injective, `F` a density on flags that is continuous on `GL n ℂ`, and `x`
invertible. Then `g ↦ F (x * g)` is integrable on `U(ε)`. -/
lemma integrable_mul_left_of_isFlagDensity (ho : o.Injective) (ε : n → ℤˣ) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) (x : GL n ℂ) :
    Integrable fun g : USign ε ↦ F (x * g) := by
  -- The integral of `‖F (x * g)‖` equals an integral over a part of the compact group `U(n)`.
  have h_norm : IsFlagDensity o fun y : Matrix n n ℂ ↦ ‖F y‖ :=
    fun y b hb ↦ by simp [hF_density y b hb]
  have int_K : Integrable fun k : USign (1 : n → ℤˣ) ↦ F k :=
    DiscreteSeries.integrable_of_compactSpace (hF_cont.comp' continuous_subtypeVal)
  refine ⟨(hF_cont.comp' (f := fun g : USign ε ↦ x * g) (by fun_prop)).aestronglyMeasurable, ?_⟩
  simpa [HasFiniteIntegral, ← ofReal_norm, lintegral_mul_left_eq_setLIntegral_openOrbit ho ε h_norm]
    using int_K.restrict.hasFiniteIntegral

/-- Let `o` be injective, `B` its triangular group, `F` a density on flags that is continuous on
`GL n ℂ`, and `x` invertible. Then the integral of `g ↦ F (x * g)` over `U(ε)` is that of `F` over
`U(n) ∩ x U(ε) B`. -/
lemma integral_mul_left_eq_setIntegral_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {F : Matrix n n ℂ → ℂ} (hF_density : IsFlagDensity o F)
    (hF_cont : Continuous fun y : GL n ℂ ↦ F y) (x : GL n ℂ) :
    ∫ g : USign ε, F (x * g) =
      ∫ k in {k : USign (1 : n → ℤˣ) | (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit ε o}, F k := by
  have int_K : Integrable fun k : USign (1 : n → ℤˣ) ↦ F k :=
    DiscreteSeries.integrable_of_compactSpace (hF_cont.comp' continuous_subtypeVal)
  have int_G := integrable_mul_left_of_isFlagDensity ho ε hF_density hF_cont x
  -- Test against real linear forms `φ`, and split `φ ∘ F` into its positive and negative parts.
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ ↦ ?_
  have hφ (ψ : ℂ →L[ℝ] ℝ) : IsFlagDensity o fun y : Matrix n n ℂ ↦ ψ (F y) :=
    fun y b hb ↦ by simp only [hF_density y b hb, map_smul]
  rw [← φ.integral_comp_comm int_G, ← φ.integral_comp_comm int_K.restrict,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (φ.integrable_comp int_G),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (φ.integrable_comp int_K.restrict),
    lintegral_mul_left_eq_setLIntegral_openOrbit ho ε (hφ φ),
    lintegral_mul_left_eq_setLIntegral_openOrbit ho ε (f := fun y ↦ -φ (F y)) (hφ (-φ))]

/-- Let `o` be injective and `F` a density on flags that is continuous on `GL n ℂ`. Then `F` is
integrable on `U(diag ε)`. -/
lemma integrable_haar_of_isFlagDensity (ho : o.Injective) (ε : n → ℤˣ) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) :
    Integrable fun g : USign ε ↦ F g := by
  simpa using integrable_mul_left_of_isFlagDensity ho ε hF_density hF_cont 1

/-- Let `G = U(diag ε)`, let `o` be injective, `B` its triangular group and `F` a density on flags
that is continuous on `GL n ℂ`. Then the integral of `F` over `G` is its integral over the part of
`U(n)` in `openOrbit ε o = G B`. Both groups carry their Haar measure `volume`, which in Cayley's
chart has density `cayleyDensity (signMatrix ε) / volU (card n)`, the same rule for every `ε`. -/
lemma integral_haar_eq_setIntegral_openOrbit (ho : o.Injective) (ε : n → ℤˣ) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) :
    ∫ g : USign ε, F g =
      ∫ k in {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε o}, F k := by
  simpa using integral_mul_left_eq_setIntegral_openOrbit ho ε hF_density hF_cont 1

/-- Let `o` be injective and `F` a density on flags that is continuous on `GL n ℂ`. Then `F` is
integrable on `U(diag ε)`, and its integral is the integral over `U(n)` less the integral over the
part of `U(n)` outside `openOrbit ε o`. -/
lemma integral_eq_sub_setIntegral_compl_openOrbit (ho : o.Injective) (ε : n → ℤˣ)
    {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) :
    Integrable (fun g : USign ε ↦ F g) ∧
    ∫ g : USign ε, F g = (∫ k : USign (1 : n → ℤˣ), F k) -
      ∫ k in {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε o}ᶜ, F k := by
  have h_meas : MeasurableSet {k : USign (1 : n → ℤˣ) | (k : Matrix n n ℂ) ∈ openOrbit ε o} :=
    ((isOpen_openOrbit ε o).preimage (by fun_prop)).measurableSet
  refine ⟨integrable_haar_of_isFlagDensity ho ε hF_density hF_cont, ?_⟩
  rw [integral_haar_eq_setIntegral_openOrbit ho ε hF_density hF_cont, eq_sub_iff_add_eq,
    integral_add_compl h_meas (integrable_haar_of_isFlagDensity ho 1 hF_density hF_cont)]

/-- Let `o` be injective and `F` a density on flags that is continuous on `GL n ℂ`. Then its
integral over `U(n)` is invariant under left translation by any invertible matrix. -/
lemma integral_unitary_mul_left_of_density (ho : o.Injective) {F : Matrix n n ℂ → ℂ}
    (hF_density : IsFlagDensity o F) (hF_cont : Continuous fun y : GL n ℂ ↦ F y) (x : GL n ℂ) :
    ∫ k : USign (1 : n → ℤˣ), F (x * k) = ∫ k : USign (1 : n → ℤˣ), F k := by
  have h_mem (k : USign (1 : n → ℤˣ)) : (x : Matrix n n ℂ)⁻¹ * k ∈ openOrbit 1 o := by
    simpa using mem_openOrbit_one o (x⁻¹ * k)
  simp [integral_mul_left_eq_setIntegral_openOrbit ho 1 hF_density hF_cont, h_mem]

end UnitaryIntegrals

/-!
## Densities on the flag variety of `K_ℂ`

The group `K = maxCompactU ε` is a product of two unitary groups, one for each sign, and the
invariance follows from the case of one unitary group by Fubini's theorem.
-/

section Densities

open Matrix MeasureTheory Finset

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

/-- The indices `i` of sign `ε i = 1`. -/
abbrev PosIndex (ε : n → ℤˣ) : Type := {i : n // ε i = 1}

/-- The indices `i` of sign `ε i ≠ 1`, that is `ε i = -1`. -/
abbrev NegIndex (ε : n → ℤˣ) : Type := {i : n // ¬ε i = 1}

/-- The block diagonal matrix with the block `a` on the indices of sign `1` and the block `b` on
the others. -/
noncomputable def signBlocks (ε : n → ℤˣ) (a : Matrix (PosIndex ε) (PosIndex ε) ℂ)
    (b : Matrix (NegIndex ε) (NegIndex ε) ℂ) : Matrix n n ℂ :=
  reindex (Equiv.sumCompl (ε · = 1)) (Equiv.sumCompl (ε · = 1)) (fromBlocks a 0 0 b)

section

variable {a a' : Matrix (PosIndex ε) (PosIndex ε) ℂ} {b b' : Matrix (NegIndex ε) (NegIndex ε) ℂ}

omit [DecidableEq n] in
theorem signBlocks_mul :
    signBlocks ε a b * signBlocks ε a' b' = signBlocks ε (a * a') (b * b') := by
  simp [signBlocks, fromBlocks_multiply]

theorem det_signBlocks : (signBlocks ε a b).det = a.det * b.det := by simp [signBlocks]

section

omit [Fintype n]

theorem signBlocks_one : signBlocks ε 1 1 = 1 := by simp [signBlocks]

omit [DecidableEq n] in
theorem conjTranspose_signBlocks : (signBlocks ε a b)ᴴ = signBlocks ε aᴴ bᴴ := by
  simp [signBlocks, fromBlocks_conjTranspose]

omit [DecidableEq n] in
/-- The entries of `signBlocks ε a b`: those of `a` or `b` at indices of equal sign, else zero. -/
theorem signBlocks_apply (i j : n) : signBlocks ε a b i j =
    if hi : ε i = 1 then if hj : ε j = 1 then a ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else if hj : ε j = 1 then 0 else b ⟨i, hi⟩ ⟨j, hj⟩ := by
  by_cases hi : ε i = 1 <;> by_cases hj : ε j = 1 <;> simp [signBlocks, hi, hj]

end

/-- The matrix `signBlocks ε a b` lies in `blockDiagAlg ε`: its entries vanish at indices of
different sign. -/
theorem signBlocks_mem_blockDiagAlg : signBlocks ε a b ∈ blockDiagAlg ε :=
  mem_blockDiagAlg.2 fun i j h_ne ↦ by
    grind [signBlocks_apply, Int.units_eq_one_or (ε i), Int.units_eq_one_or (ε j)]

omit [Fintype n] in
theorem signBlocks_eq_one_iff : signBlocks ε a b = 1 ↔ a = 1 ∧ b = 1 := by
  rw [← signBlocks_one (ε := ε), signBlocks, signBlocks, Equiv.apply_eq_iff_eq, fromBlocks_inj]
  simp

/-- A block diagonal matrix with unitary blocks preserves the form `signMatrix ε = diag ε`. -/
theorem signBlocks_preserves_form (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) :
    (signBlocks ε a b)ᴴ * signMatrix ε * signBlocks ε a b = signMatrix ε := by
  rw [mul_assoc, DiscreteSeries.mem_blockDiagAlg_iff_commute.1 signBlocks_mem_blockDiagAlg,
    ← mul_assoc,
    conjTranspose_signBlocks, signBlocks_mul, ha, hb, signBlocks_one, one_mul]

/-- A block diagonal matrix is invertible and triangular for the order `o` if both blocks are. -/
theorem isBorelMatrix_signBlocks {o : n → ℤ} (ha : IsBorelMatrix (fun i : PosIndex ε ↦ o i) a)
    (hb : IsBorelMatrix (fun i : NegIndex ε ↦ o i) b) : IsBorelMatrix o (signBlocks ε a b) := by
  obtain ⟨ha_tri, ha_det⟩ := ha
  obtain ⟨hb_tri, hb_det⟩ := hb
  refine ⟨fun i j h_lt ↦ ?_, by simp [det_signBlocks, ha_det, hb_det]⟩
  rw [signBlocks_apply]
  split_ifs
  exacts [ha_tri h_lt, rfl, rfl, hb_tri h_lt]

omit [DecidableEq n] in
/-- The product `diagChar w m = ∏ i, m i i ^ w i` of a block diagonal matrix splits over the two
blocks. -/
theorem diagChar_signBlocks (w : n → ℤ) : diagChar w (signBlocks ε a b) =
    diagChar (fun i : PosIndex ε ↦ w i) a * diagChar (fun i : NegIndex ε ↦ w i) b := by
  simp [diagChar, ← (Equiv.sumCompl fun i : n ↦ ε i = 1).prod_comp, signBlocks]

end

/-- Every matrix in `blockDiagAlg ε` (entries vanish at indices of different sign) has the form
`signBlocks ε a b`. -/
theorem exists_eq_signBlocks {y : Matrix n n ℂ} (hy : y ∈ blockDiagAlg ε) :
    ∃ (a : Matrix (PosIndex ε) (PosIndex ε) ℂ) (b : Matrix (NegIndex ε) (NegIndex ε) ℂ),
      y = signBlocks ε a b := by
  refine ⟨y.toBlock (ε · = 1) (ε · = 1), y.toBlock (¬ε · = 1) (¬ε · = 1), ext fun i j ↦ ?_⟩
  grind [signBlocks_apply, toBlock_apply, mem_blockDiagAlg.1 hy i j]

omit [Fintype n] [DecidableEq n] in
/-- A block diagonal matrix depends continuously on its two blocks. -/
@[fun_prop] theorem continuous_signBlocks {X : Type*} [TopologicalSpace X]
    {a : X → Matrix (PosIndex ε) (PosIndex ε) ℂ} {b : X → Matrix (NegIndex ε) (NegIndex ε) ℂ}
    (ha : Continuous a) (hb : Continuous b) : Continuous fun x : X ↦ signBlocks ε (a x) (b x) := by
  unfold signBlocks
  fun_prop

/-- The homomorphism `U(p) × U(q) → K = maxCompactU ε` that puts two unitary matrices on the
diagonal; `p` and `q` count the indices of sign `1` and `-1`. -/
noncomputable def signBlocksHom (ε : n → ℤˣ) :
    USign (1 : PosIndex ε → ℤˣ) × USign (1 : NegIndex ε → ℤˣ) →* maxCompactU ε :=
  MonoidHom.mk'
    (fun u ↦ ⟨U.of IsHermitianInvolution.isUnit (signBlocks ε u.1 u.2)
        (signBlocks_preserves_form
          (by simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 u.1.property)
          (by simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 u.2.property)),
      mem_maxCompactU.2 signBlocks_mem_blockDiagAlg⟩)
    fun u v ↦ Subtype.ext <| Subtype.ext <| Units.ext (by simp [signBlocks_mul])

theorem coe_signBlocksHom (u : USign (1 : PosIndex ε → ℤˣ)) (v : USign (1 : NegIndex ε → ℤˣ)) :
    (signBlocksHom ε (u, v) : Matrix n n ℂ) = signBlocks ε u v := rfl

theorem continuous_signBlocksHom : Continuous (signBlocksHom ε) := by
  rw [continuous_induced_rng, continuous_U_iff_matrix]
  exact continuous_signBlocks (by fun_prop) (by fun_prop)

/-- Every element of `K = maxCompactU ε` is block diagonal with unitary blocks. -/
theorem signBlocksHom_surjective : Function.Surjective (signBlocksHom ε) := by
  intro k
  obtain ⟨a, b, hk : (k : Matrix n n ℂ) = signBlocks ε a b⟩ :=
    exists_eq_signBlocks (mem_maxCompactU.1 k.prop)
  have h_unitary : signBlocks ε (aᴴ * a) (bᴴ * b) = 1 := by
    rw [← signBlocks_mul, ← conjTranspose_signBlocks, ← hk, ← maxCompactU.coe_inv,
      nonsing_inv_mul _ (by simp [GeneralLinearGroup.det_ne_zero])]
  obtain ⟨ha, hb⟩ := signBlocks_eq_one_iff.1 h_unitary
  refine ⟨(U.of IsHermitianInvolution.isUnit a (by simpa using ha),
    U.of IsHermitianInvolution.isUnit b (by simpa using hb)), ?_⟩
  ext : 3
  simp [coe_signBlocksHom, hk]

/-- The map `U(p) × U(q) → K = maxCompactU ε`, `(a, b) ↦ signBlocks ε a b`, carries the product of
the Haar measures of mass one to the Haar measure `haarK ε` of mass one. -/
theorem measurePreserving_signBlocksHom :
    MeasurePreserving (signBlocksHom ε) (volume.prod volume) (haarK ε) :=
  MonoidHom.measurePreserving continuous_signBlocksHom signBlocksHom_surjective (by simp)

/-- Fubini's theorem on `K = maxCompactU ε ≃ U(p) × U(q)`: the integral of a continuous function
over `K` is the double integral over the unitary blocks. -/
theorem integral_haarK_eq_integral_signBlocksHom {φ : maxCompactU ε → ℂ} (hφ : Continuous φ) :
    ∫ k : maxCompactU ε, φ k ∂haarK ε = ∫ u : USign (1 : PosIndex ε → ℤˣ),
      ∫ v : USign (1 : NegIndex ε → ℤˣ), φ (signBlocksHom ε (u, v)) :=
  (measurePreserving_signBlocksHom.fubini (DiscreteSeries.integrable_of_compactSpace hφ)).right.symm

omit [DecidableEq n] in
/-- Let `p` select the indices of one sign. On these indices `-2 ρ_c`, minus the sum of the compact
roots (those `e i - e j` with `ε i = ε j`) positive for `l`, is the sum `2 ρ` of all roots of the
block positive for `-l`. -/
theorem twoRho_subtype (l : n → ℤ) {p : n → Prop} [DecidablePred p]
    (hp : ∀ i j : n, p i → (p j ↔ ε i = ε j)) :
    twoRho (fun i : {i : n // p i} ↦ (-l) i) ⊤ =
      fun i : {i : n // p i} ↦ (-twoRho l fun i j : n ↦ ε i = ε j) i := by
  ext i
  have h_class (j : n) : ε i = ε j ↔ p j := (hp i j i.prop).symm
  have h_card (q : n → Prop) [DecidablePred q] :
      #{j : {i : n // p i} | q j} = #{j : n | ε i = ε j ∧ q j} :=
    card_bij (fun j _ ↦ (j : n)) (by simp +contextual [h_class, Subtype.property]) (by simp)
      (by simp +contextual [h_class])
  simp [twoRho, ← h_card]

/-- Let `K_ℂ` be the group of invertible matrices in `blockDiagAlg ε` (entries vanish at indices of
different sign), let `K = maxCompactU ε` be its unitary subgroup with Haar measure `haarK ε`, and
let `l` have distinct entries. Let `B_K` be the subgroup of `K_ℂ` of matrices upper triangular in
the order of decreasing `l`, and let `2 ρ_c` be the sum of the compact roots (those `e i - e j` with
`ε i = ε j`) positive for `l`. If `F` is continuous on `K_ℂ` and
`F (y * b) = |∏ i, b i i ^ (-2 ρ_c) i| ^ 2 * F y` for `y` in `K_ℂ` and `b` in `B_K`, then the
integral of `F (x * k)` over `K` equals that of `F k`, for all `x` in `K_ℂ`.

Classically this invariance follows from the Iwasawa decomposition `K_ℂ = K B_K` and the form
`dk d_r b` of the Haar measure of `K_ℂ`; here the invariance is proved block by block, by Fubini's
theorem and `integral_unitary_mul_left_of_density`, without using the Haar measure of `K_ℂ`. -/
theorem integral_haarK_mul_left_of_density {l : n → ℤ} (hl : l.Injective) {F : Matrix n n ℂ → ℂ}
    (hF_cont : ContinuousOn F {y : Matrix n n ℂ | y ∈ blockDiagAlg ε ∧ y.det ≠ 0})
    (hF_borel : ∀ y ∈ blockDiagAlg ε, y.det ≠ 0 → ∀ b ∈ blockDiagAlg ε, IsBorelMatrix (-l) b →
      F (y * b) = ‖diagChar (-twoRho l fun i j : n ↦ ε i = ε j) b‖ ^ 2 * F y)
    {x : Matrix n n ℂ} (hx_mem : x ∈ blockDiagAlg ε) (hx_det : x.det ≠ 0) :
    ∫ k : maxCompactU ε, F (x * k) ∂haarK ε = ∫ k : maxCompactU ε, F k ∂haarK ε := by
  -- Let `f y z` be `F` at the matrix with blocks `y`, `z`. It is a density in each variable (for
  -- the orders `op`, `oq` that `-l` induces on the blocks), and the integral over `K` is the double
  -- integral over the unitary groups `Up`, `Uq` of the blocks.
  let f (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) : ℂ := F (signBlocks ε y z)
  let Up : Subgroup (GL (PosIndex ε) ℂ) := USign 1
  let Uq : Subgroup (GL (NegIndex ε) ℂ) := USign 1
  let op (i : PosIndex ε) : ℤ := (-l) i
  let oq (i : NegIndex ε) : ℤ := (-l) i
  have h_det (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) : (signBlocks ε y z).det ≠ 0 := by
    simp [det_signBlocks, GeneralLinearGroup.det_ne_zero]
  have hf_cont : Continuous f.uncurry :=
    hF_cont.comp_continuous (by fun_prop) fun (y, z) ↦ ⟨signBlocks_mem_blockDiagAlg, h_det y z⟩
  have sign_pos (i j : n) (hi : ε i = 1) : ε j = 1 ↔ ε i = ε j := by grind
  have sign_neg (i j : n) (hi : ¬ε i = 1) : ¬ε j = 1 ↔ ε i = ε j := by
    grind [Int.units_eq_one_or (ε i), Int.units_eq_one_or (ε j)]
  have h_inj : (-l).Injective := neg_injective.comp hl
  -- The rule for `F` on block matrices; on each block `-2 ρ_c` is the `2 ρ` of the block.
  have h_rule (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ)
      {s : Matrix (PosIndex ε) (PosIndex ε) ℂ} {t : Matrix (NegIndex ε) (NegIndex ε) ℂ}
      (hs : IsBorelMatrix op s) (ht : IsBorelMatrix oq t) :
      F (signBlocks ε (y * s) (z * t)) =
        ‖diagChar (twoRho op ⊤) s * diagChar (twoRho oq ⊤) t‖ ^ 2 * f y z := by
    rw [twoRho_subtype l sign_pos, twoRho_subtype l sign_neg, ← signBlocks_mul,
      ← diagChar_signBlocks]
    exact hF_borel _ signBlocks_mem_blockDiagAlg (h_det y z) _ signBlocks_mem_blockDiagAlg
      (isBorelMatrix_signBlocks hs ht)
  have h_pos (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) :
      ∫ u : Up, f (y * u) z = ∫ u : Up, f u z := by
    have density : IsFlagDensity op fun s ↦ F (signBlocks ε s z) := fun y' s hs ↦ by
      simpa [diagChar] using h_rule y' z hs ⟨blockTriangular_one, by simp⟩
    exact integral_unitary_mul_left_of_density (h_inj.comp Subtype.val_injective) density
      (hf_cont.uncurry_right z) y
  have h_neg (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) :
      ∫ v : Uq, f y (z * v) = ∫ v : Uq, f y v := by
    have density : IsFlagDensity oq fun t ↦ F (signBlocks ε y t) := fun z' t ht ↦ by
      simpa [diagChar] using h_rule y z' ⟨blockTriangular_one, by simp⟩ ht
    exact integral_unitary_mul_left_of_density (h_inj.comp Subtype.val_injective) density
      (hf_cont.uncurry_left y) z
  have h_fubini (y : GL (PosIndex ε) ℂ) (z : GL (NegIndex ε) ℂ) :
      ∫ k : maxCompactU ε, F (signBlocks ε y z * k) ∂haarK ε =
        ∫ u : Up, ∫ v : Uq, f (y * u) (z * v) := by
    have h_cont : Continuous fun k : maxCompactU ε ↦ F (signBlocks ε y z * k) := by
      refine hF_cont.comp_continuous (by fun_prop) fun k ↦ ⟨?_, ?_⟩
      · exact mul_mem signBlocks_mem_blockDiagAlg (mem_maxCompactU.1 k.prop)
      · simp [h_det, GeneralLinearGroup.det_ne_zero]
    simp [integral_haarK_eq_integral_signBlocksHom h_cont, coe_signBlocksHom, signBlocks_mul, f, Up,
      Uq]
  have h_swap (y : GL (PosIndex ε) ℂ) :
      ∫ u : Up, ∫ v : Uq, f (y * u) v = ∫ v : Uq, ∫ u : Up, f (y * u) v :=
    integral_integral_swap (DiscreteSeries.integrable_of_compactSpace (by fun_prop))
  obtain ⟨a, b, rfl⟩ := exists_eq_signBlocks hx_mem
  obtain ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩ : IsUnit a ∧ IsUnit b := by
    simpa [det_signBlocks, isUnit_iff_isUnit_det] using hx_det
  calc _ = ∫ u : Up, ∫ v : Uq, f (y * u) (z * v) := h_fubini y z
    _ = ∫ u : Up, ∫ v : Uq, f (1 * u) v := by simp only [h_neg, h_swap, h_pos]
    _ = ∫ k : maxCompactU ε, F k ∂haarK ε := by simpa [signBlocks_one] using (h_fubini 1 1).symm

end Densities

end New
end
end

/-!
# Flensted-Jensen's integral, analyticity of c_λ and its Casimir eigenvalue

This file studies the coefficient c_λ = `New.HCParam.dsCoeff l`, with `l = 2λ`, on the group
`U(diag ε)`, where `K = U(diag ε) ∩ U(n)`. It proves that c_λ is complex analytic, so defines a
smooth function `New.HCParam.dsCoeffSmooth` in `New.SmoothU`. For a parameter with a gap
(`New.HCParam.HasGap`, assumed in all results listed below), Flensted-Jensen's integral over `K`,
which gives c_λ, does not depend on the admissible block diagonal factor, and c_λ is an
eigenfunction of the Casimir operator of `gl_n`.

## Main definitions and results

* `New.flenstedJensen_eq_of_accretive`, `New.dsCoeff_eq_flenstedJensen`: any block diagonal `a` with
  `a⁻¹ g` accretive (`Matrix.IsAccretive`: `z + zᴴ` positive definite) gives the same value. The
  integrand is a density on the flag variety of `K_ℂ`; polarization makes the integral locally
  constant, and the admissible `a` form a convex set.
* `New.flenstedJensen_eq_integral_of_eq_mul_mul_conjTranspose`,
  `New.dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose`: the value as an integral over `K` for any
  splitting `g = p z qᴴ` with `p`, `q` block diagonal and `z` accretive.
* `New.DiscreteSeries.splitCoeff_triangular_mul_mul_triangular`,
  `New.DiscreteSeries.flenstedJensen_triangular_mul_mul_triangular`: block diagonal triangular
  factors, lower on the left and upper on the right, come out as characters.
* `New.casimir_dsCoeffSmooth`: the function c_λ (`New.HCParam.dsCoeffSmooth`, l = 2λ) on U(diag ε)
  is an eigenfunction of the Casimir operator Σ_{a,b} E_ab E_ba of gl_n, acting by right derivatives
  (`New.rightDeriv`), with eigenvalue `New.HCParam.casimirValue` l = |λ|² − |ρ|². Near a point c_λ
  is an average over k in K = `New.maxCompactU` of functions that are lowest weight vectors of
  weight λ + ρ (highest vectors for the roots positive for −l) in the basis k E_ab k⁻¹ of gl_n, and
  the Casimir operator does not depend on the basis.

Notions from other files:
* `New.USign`: For a vector of signs ε, the unitary group U(J) of the diagonal matrix J=diag(ε).
* `New.SmoothU`: Smooth functions on `U(diag ε)`: the restrictions of the smooth functions on all
  matrices.
* `New.HCParam.HasGap`: the entries of `l = 2λ` are distinct, of the parity of `card n - 1`, and
  those with different signs differ by at least `2h`.
* `New.blockDiagAlg ε`: the matrices that commute with `diag ε`, the block diagonal matrices.

## Relation to the literature

Known; see `Lib.DiscreteSeries.FlenstedJensen.PsiKTypes` for sources.
-/

@[expose] public section

/-!
## Flensted-Jensen's integral and analyticity of the coefficient

Flensted-Jensen's integral `New.HCParam.flenstedJensen l a z` is the integral over
`K = U(diag ε) ∩ U(n)` of `m_Λ(a k) * conj m_Λ(k) / m_{-λ-ρ}(kᴴ z k)`, normalised by `∫ |m_Λ|²`,
where `m_w = New.weightMinors w` is a product of principal minors, `Λ = New.HCParam.lowestKType l`
and `λ + ρ = New.paramAddRho l`. The function `New.HCParam.dsCoeff l g` is its value at
`(a, a⁻¹ g)` with `a = New.blockDiagPart ε g` the block diagonal part of `g`.

For a parameter of some gap the value is the same for every block diagonal `a` with `a⁻¹ g`
accretive: these `a` form a convex set, so it is enough that the derivative in `a` vanishes. Up to
the normalising constant the integral is `I(a, 1)`, where `I = New.HCParam.splittingIntegral l g` is
analytic at each pair `(p, r)` with `r g⁻¹ p` accretive. For a parameter of some gap the integrand
of `I` is a density for the triangular subgroup of `K_ℂ`, so `I(p x, xᴴ r) = I(p, r)` for invertible
block diagonal `x`. Polarization of this invariance shows that the derivative of `I` in `p` vanishes
in the block diagonal directions.
-/

namespace New

open Matrix MeasureTheory Finset ComplexConjugate ComplexOrder DiscreteSeries Norms.L2Operator
  ContinuousMap

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l : HCParam ε}

@[fun_prop]
theorem DiscreteSeries.analyticAt_matrix_inv {s : Matrix n n ℂ} (hs : s.det ≠ 0) :
    AnalyticAt ℂ (·⁻¹) s := by
  obtain ⟨u, rfl⟩ : IsUnit s := (isUnit_iff_isUnit_det s).2 hs.isUnit
  simpa only [funext nonsing_inv_eq_ringInverse] using analyticAt_inverse (𝕜 := ℂ) u

/-- The derivative of an equivariant function in an elementary direction. Let `f` have derivative
`D` at `s`. Suppose that `f (c b) = diagChar w b * f s`, with `diagChar w b = ∏ a, b a a ^ w a`,
whenever `c b` is near `s` and `b` is block diagonal, invertible and triangular for the order
`-o`. Suppose also that `c` maps the line `1 + t • single i j 1`, where `ε i = ε j` and
`o j ≤ o i`, to the line `s + t • v`. Then `D v` is `w i * f s` if `i = j`, and `0` otherwise. -/
theorem fderiv_eq_of_borel_equivariant (ε : n → ℤˣ) {s v : Matrix n n ℂ} {f : Matrix n n ℂ → ℂ}
    {o w : n → ℤ} {D : Matrix n n ℂ →L[ℂ] ℂ} {i j : n} (hf : HasFDerivAt f D s) (h_le : o j ≤ o i)
    (h_sign : ε i = ε j) (c : Matrix n n ℂ → Matrix n n ℂ)
    (h_equivariant : ∀ᶠ x : Matrix n n ℂ in nhds s, ∀ b ∈ blockDiagAlg ε,
      IsBorelMatrix (-o) b → x = c b → f x = diagChar w b * f s)
    (h_direction : ∀ t : ℂ, s + t • v = c (1 + t • single i j 1)) :
    D v = (if i = j then (w i : ℂ) else 0) * f s := by
  -- For small `t` the matrix `b t = 1 + t • single i j 1` is invertible and triangular, so along
  -- the line `s + t • v` the function is `∏ a, b t a a ^ w a * f s`. Differentiate at `t = 0`.
  let Y : Matrix n n ℂ := single i j 1
  have h_factor (a : n) : HasDerivAt (fun t : ℂ ↦ (1 + t * Y a a) ^ w a) (w a * Y a a) 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_zpow (w a) _ (by simp)).comp 0 ((hasDerivAt_mul_const (Y a a)).const_add 1)
  have h_prod : HasDerivAt (fun t : ℂ ↦ ∏ a, (1 + t * Y a a) ^ w a)
      (if i = j then (w i : ℂ) else 0) 0 := by
    simpa [Y, single, ite_and, comm] using
      HasDerivAt.fun_finsetProd (u := univ) fun a _ ↦ h_factor a
  have h_det : ∀ᶠ t : ℂ in nhds 0, (1 + t • Y).det ≠ 0 :=
    ContinuousAt.eventually_ne (by fun_prop) (by simp)
  refine (hf.hasLineDerivAt v).unique ((h_prod.mul_const (f s)).congr_of_eventuallyEq ?_)
  have h_line : Filter.Tendsto (fun t : ℂ ↦ s + t • v) (nhds 0) (nhds s) :=
    Continuous.tendsto' (by fun_prop) 0 s (by simp)
  filter_upwards [h_line.eventually h_equivariant, h_det] with t ht ht_det
  have h_entry (a b : n) : (1 + t • Y) a b = (if a = b then 1 else 0) +
      (if i = a ∧ j = b then t else 0) := by simp [Y, single, Matrix.one_apply]
  have h_mem : 1 + t • Y ∈ blockDiagAlg ε := mem_blockDiagAlg.2 fun a b hab ↦ by grind
  have h_tri : (1 + t • Y).BlockTriangular (-o) := fun a b (hab : -o b < -o a) ↦ by grind
  simpa [diagChar] using ht (1 + t • Y) h_mem ⟨h_tri, ht_det⟩ (h_direction t)

/-! ### Analyticity of the coefficient -/

/-- Let `a` be analytic at the matrix `g` with `(a g)⁻¹ g` accretive (positive definite Hermitian
part). Then the integrand of `New.HCParam.flenstedJensen l (a x) ((a x)⁻¹ * x)`, made of the
products of principal minors `weightMinors` of weights `Λ = l.lowestKType` and `-(λ + ρ)`, is an
analytic family in `x` near `g`: it is given by an analytic function with values in `C(K, ℂ)`,
`K = maxCompactU ε` being the compact group `U(diag ε) ∩ U(n)`. -/
theorem isAnalyticFamily_flenstedJensen (l : HCParam ε) {g : Matrix n n ℂ}
    {a : Matrix n n ℂ → Matrix n n ℂ} (ha : AnalyticAt ℂ a g)
    (h_acc : ((a g)⁻¹ * g).IsAccretive) :
    IsAnalyticFamily
      (fun (x : Matrix n n ℂ) (k : maxCompactU ε) ↦
        weightMinors l.lowestKType (a x * k) * conj (weightMinors l.lowestKType k) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * ((a x)⁻¹ * x) * k))
      g := by
  obtain ⟨ha_det, -⟩ : (a g).det ≠ 0 ∧ g.det ≠ 0 := by simpa using h_acc.det_ne_zero
  -- The integrand is an analytic function `Θ` of `x` and the pair `(k, kᴴ)`.
  let Θ : Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ → ℂ := fun (x, y, z) ↦
    weightMinors l.lowestKType (a x * y) * weightMinors l.lowestKType z /
      weightMinors (-paramAddRho l) (z * ((a x)⁻¹ * x) * y)
  simp only [conj_weightMinors]
  refine IsAnalyticFamily.of_analyticAt (by fun_prop) Θ
    (ι := fun k : maxCompactU ε ↦ ((k : Matrix n n ℂ), (k : Matrix n n ℂ)ᴴ)) fun k ↦ ?_
  have hz : ((k : Matrix n n ℂ)ᴴ * ((a g)⁻¹ * g) * k).IsAccretive :=
    h_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)
  -- The side conditions of `fun_prop` are the nonvanishing of minors and determinants; `det_mul`
  -- is applied only where it does not hide the product in `hz`.
  fun_prop (disch := simp [ha_det, hz, hz.det_ne_zero, -det_mul, det_mul (a g),
    GeneralLinearGroup.det_ne_zero])

/-- For all signs ε and integer vectors l = 2λ, the function c_λ = `l.dsCoeff`, Flensted-Jensen's
integral with the block diagonal part of the matrix as factor, is complex analytic at every point
g of U(diag ε). -/
theorem HCParam.analyticAt_dsCoeff (g : USign ε) : AnalyticAt ℂ l.dsCoeff g := by
  -- Differentiate under the integral sign, with the block diagonal part as the analytic factor.
  unfold HCParam.dsCoeff HCParam.flenstedJensen
  exact ((isAnalyticFamily_flenstedJensen l (a := fun x ↦ blockDiagPart ε x) (by fun_prop)
    (isAccretive_blockDiagPart_inv_mul g).2).analyticAt_integral (haarK ε)).div_const

-- `grind` may use that `2ρ` is ordered as `l` wherever two entries of `λ + ρ` occur.
grind_pattern twoRho_lt_twoRho => paramAddRho l a, paramAddRho l b

/-! ### Dominance of the weights -/

section

omit [DecidableEq n]

/-- For a parameter `l = 2λ` of gap `h`, the entries of `λ + ρ = paramAddRho l`, with ρ the half sum
of the roots positive for `l`, are ordered as those of `l`. -/
theorem HCParam.HasGap.paramAddRho_lt_iff {h : ℕ} (hl : l.HasGap h) {i j : n} :
    paramAddRho l i < paramAddRho l j ↔ l i < l j := by
  grind [paramAddRho, HasGap]

/-- For a parameter `l = 2λ` of gap `h`, the weight `-(λ + ρ)` is dominant for the order `l` with
all signs equal: its entries decrease as those of `l` increase. -/
theorem HCParam.HasGap.isKDominant_neg_paramAddRho {h : ℕ} (hl : l.HasGap h) :
    IsKDominant 1 l (-paramAddRho l) := by
  simp_all [IsKDominant, hl.paramAddRho_lt_iff, le_of_lt]

/-- For a parameter l = 2λ of gap h, the weight Λ = λ+ρ−2ρ_c, with 2ρ_c the sum of the roots
e_i − e_j with ε_i = ε_j that are positive for l, is K-dominant for the order −l: Λ_j ≤ Λ_i whenever
ε_i = ε_j and l_j < l_i. -/
theorem HCParam.HasGap.isKDominant_lowestKType {h : ℕ} (hl : l.HasGap h) :
    IsKDominant ε (-l) l.lowestKType := by
  intro i j h_sign (h_lt : -l i < -l j)
  -- The entries of `l` are distinct and of one parity, so the numbers `l a` and `l a - 1` are all
  -- distinct, and at most `l i - l j` of them lie in `Ico (l j) (l i)`.
  let s : Finset (n × Fin 2) := {x | l x.1 - x.2 ∈ Ico (l j) (l i)}
  have h_card : #s ≤ #(Ico (l j) (l i)) :=
    card_le_card_of_injOn (fun x ↦ l x.1 - x.2) (by grind [Set.MapsTo]) fun _ ↦ by grind [HasGap]
  have h_count : (#s : ℤ) = ∑ a : n,
      ((if l j ≤ l a ∧ l a < l i then 1 else 0) + (if l j < l a ∧ l a ≤ l i then 1 else 0)) := by
    simp [s, ← sum_boole, Fintype.sum_prod_type]
  have h_value (m : n) : 2 * l.lowestKType m - l m =
      twoRho l (fun a b ↦ ε a ≠ ε b) m - twoRho l (fun a b ↦ ε a = ε b) m := by
    linarith [two_mul_lowestKType hl m]
  -- `2 * l.lowestKType - l` is a difference of `twoRho` terms. To its value at `j` less its value
  -- at `i`, each index `a` contributes at most the number of `l a`, `l a - 1` in that interval.
  have h_diff : 2 * l.lowestKType j - l j - (2 * l.lowestKType i - l i) ≤ #s := by
    simp only [h_value, twoRho, h_count, ← sum_boole, h_sign, ← sum_sub_distrib]
    refine sum_le_sum fun a _ ↦ ?_
    lia
  grind [Int.card_Ico]

end

/-! ### The splitting integral -/

/-- The function `F(y) = m_Λ(p y) · conj m_Λ(q y) / m_{λ+ρ}(yᴴ qᴴ g⁻¹ p y)`, written in `r = qᴴ`
so that it depends holomorphically on the pair `(p, r)`. Here `l = 2λ`, `Λ = l.lowestKType` and
`m_w = weightMinors w` is the product of principal minors of weight `w`. -/
noncomputable def HCParam.splittingIntegrand (l : HCParam ε) (g p r y : Matrix n n ℂ) : ℂ :=
  weightMinors l.lowestKType (p * y) * weightMinors l.lowestKType (yᴴ * r) /
    weightMinors (paramAddRho l) (yᴴ * (r * g⁻¹ * p) * y)

/-- The integral `I(p, r)` of `splittingIntegrand` over `K = U(diag ε) ∩ U(n)` for its Haar measure
`haarK ε` of mass one, as a function of the pair `(p, r)`, where `r` stands for `qᴴ`. -/
noncomputable def HCParam.splittingIntegral (l : HCParam ε) (g : Matrix n n ℂ)
    (pr : Matrix n n ℂ × Matrix n n ℂ) : ℂ :=
  ∫ k : maxCompactU ε, l.splittingIntegrand g pr.1 pr.2 (k : Matrix n n ℂ) ∂haarK ε

/-- For a matrix `a` with `a⁻¹ g` accretive, Flensted-Jensen's normalised integral at `(a, a⁻¹ g)`
is the integral `I(a, 1) = l.splittingIntegral g (a, 1)` divided by
`Λ.kTypeNormSq = ∫_K |m_Λ|²`, where `Λ = l.lowestKType`. -/
theorem flenstedJensen_eq_splittingIntegral {g a : Matrix n n ℂ} (ha_acc : (a⁻¹ * g).IsAccretive) :
    l.flenstedJensen a (a⁻¹ * g) = l.splittingIntegral g (a, 1) / l.lowestKType.kTypeNormSq := by
  obtain ⟨ha_det, -⟩ : a.det ≠ 0 ∧ g.det ≠ 0 := by simpa using ha_acc.det_ne_zero
  have h_inv (k : maxCompactU ε) :
      ((k : Matrix n n ℂ)ᴴ * (a⁻¹ * g) * k)⁻¹ = (k : Matrix n n ℂ)ᴴ * (1 * g⁻¹ * a) * k := by
    simp [← maxCompactU.coe_inv, Matrix.mul_inv_rev, ha_det, mul_assoc]
  simp only [flenstedJensen, HCParam.splittingIntegral, HCParam.splittingIntegrand,
    weightMinors_neg (ha_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)).det_ne_zero,
    h_inv, conj_weightMinors, mul_one]

lemma DiscreteSeries.conjTranspose_mem_blockDiagAlg {X : Matrix n n ℂ} (hX : X ∈ blockDiagAlg ε) :
    Xᴴ ∈ blockDiagAlg ε :=
  mem_blockDiagAlg.2 fun i j hij ↦ by simp [mem_blockDiagAlg.1 hX j i hij.symm]

/-- The adjoint of an invertible matrix that is lower triangular for the order `o` is invertible
and upper triangular for `o`. -/
lemma DiscreteSeries.isBorelMatrix_conjTranspose {o : n → ℤ} {X : Matrix n n ℂ}
    (hX : IsBorelMatrix (-o) X) : IsBorelMatrix o Xᴴ :=
  ⟨fun i j hij ↦ by simp [hX.left (neg_lt_neg hij)], by simpa using hX.right⟩

/-- Let `l = 2λ` be a parameter of some gap `h` (distinct entries congruent to `card n - 1` mod 2).
Let `F = l.splittingIntegrand g p r` be the function
`F(y) = m_Λ(p y) · conj m_Λ(q y) / m_{λ+ρ}(yᴴ qᴴ g⁻¹ p y)`,
written with `r = qᴴ`, where `Λ = l.lowestKType` and `m_w` is the product of principal
minors of weight `w`. If `r g⁻¹ p` is accretive and `y` is invertible, then
`F(y b) = |b^(-2ρ_c)|² F(y)` for every invertible block diagonal `b` (commuting with diag ε) that is
upper triangular in the order of decreasing `l`, so `F` is a density. Here `2ρ_c` is the sum of the
compact positive roots (the roots e_i − e_j with `ε i = ε j` that are positive for `l`), and
`b^w = diagChar w b` is ∏ b_ii^(w_i). -/
theorem splittingIntegrand_mul_borel {h : ℕ} (hl : l.HasGap h) {g p r y b : Matrix n n ℂ}
    (h_acc : (r * g⁻¹ * p).IsAccretive) (hy : y.det ≠ 0)
    (hb_mem : b ∈ blockDiagAlg ε) (hb : IsBorelMatrix (-l) b) :
    l.splittingIntegrand g p r (y * b) =
      ‖diagChar (-twoRho l fun i j : n ↦ ε i = ε j) b‖ ^ 2 * l.splittingIntegrand g p r y := by
  -- Each of the three products of minors in `F` is multiplied by a character of `b` (or `bᴴ`).
  have h_inj : (-l).Injective := hl.neg.injective
  have h_low : IsKDominant ε (-l) l.lowestKType := hl.isKDominant_lowestKType
  have h_rho : IsKDominant ε (-l) (paramAddRho l) :=
    fun i j _ hij ↦ (hl.paramAddRho_lt_iff.2 (neg_lt_neg_iff.1 hij)).le
  obtain ⟨⟨hr, -⟩, hp⟩ : (r.det ≠ 0 ∧ g.det ≠ 0) ∧ p.det ≠ 0 := by simpa using h_acc.det_ne_zero
  have hz : (yᴴ * (r * g⁻¹ * p) * y).det ≠ 0 := (h_acc.conjTranspose_mul_mul hy).det_ne_zero
  have hzb : (yᴴ * (r * g⁻¹ * p) * y * b).det ≠ 0 :=
    (det_mul _ b).trans_ne (mul_ne_zero hz hb.right)
  have hb'_mem : bᴴ ∈ blockDiagAlg ε := conjTranspose_mem_blockDiagAlg hb_mem
  have hb_adj : IsBorelMatrix (- -l) bᴴ := isBorelMatrix_conjTranspose (by rwa [neg_neg])
  have h_adj (w : n → ℤ) : diagChar w bᴴ = conj (diagChar w b) := by simp [diagChar]
  -- The rule `m_w(b' z b) = b'^w b^w m_w(z)` for `b'` lower and `b` upper triangular, applied to
  -- each of the three factors.
  have h_p_factor : weightMinors l.lowestKType (p * (y * b)) =
      weightMinors l.lowestKType (p * y) * diagChar l.lowestKType b := by
    rw [← mul_assoc, h_low.weightMinors_mul_borel h_inj (by simp [hp, hy]) hb_mem hb]
  have h_r_factor : weightMinors l.lowestKType ((y * b)ᴴ * r) =
      conj (diagChar l.lowestKType b) * weightMinors l.lowestKType (yᴴ * r) := by
    rw [conjTranspose_mul, mul_assoc,
      h_low.weightMinors_oppBorel_mul h_inj (by simp [hr, hy]) hb'_mem hb_adj, h_adj]
  have h_denom : weightMinors (paramAddRho l) ((y * b)ᴴ * (r * g⁻¹ * p) * (y * b)) =
      conj (diagChar (paramAddRho l) b) * (weightMinors (paramAddRho l) (yᴴ * (r * g⁻¹ * p) * y) *
        diagChar (paramAddRho l) b) := by
    rw [← h_rho.weightMinors_mul_borel h_inj hz hb_mem hb, ← h_adj,
      ← h_rho.weightMinors_oppBorel_mul h_inj hzb hb'_mem hb_adj]
    simp only [conjTranspose_mul, mul_assoc]
  -- The characters combine because `Λ = (λ + ρ) - 2 ρ_c` with `λ + ρ = paramAddRho l`.
  have h_char : diagChar l.lowestKType b =
      diagChar (paramAddRho l) b * diagChar (-twoRho l fun i j ↦ ε i = ε j) b := by
    simp [lowestKType, zpow_sub₀, hb.diag_ne_zero h_inj, div_eq_mul_inv, prod_mul_distrib, diagChar]
  have h_ne : diagChar (paramAddRho l) b ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ ↦ zpow_ne_zero _ (hb.diag_ne_zero h_inj i)
  simp only [HCParam.splittingIntegrand, h_p_factor, h_r_factor, h_denom, h_char, map_mul,
    ← Complex.mul_conj']
  field_simp [h_ne, (map_ne_zero conj).2 h_ne]

/-- Invariance: for a parameter `l` of gap `h`, a matrix `r g⁻¹ p` that is accretive and an
invertible block diagonal `x`, one has `I(p x, xᴴ r) = I(p, r)`, where
`I = l.splittingIntegral g` and a matrix `z` is accretive if `z + zᴴ` is positive definite. -/
theorem splittingIntegral_mul_conjTranspose_mul {h : ℕ} (hl : l.HasGap h) {g p r x : Matrix n n ℂ}
    (h_acc : (r * g⁻¹ * p).IsAccretive) (hx_mem : x ∈ blockDiagAlg ε) (hx_det : x.det ≠ 0) :
    l.splittingIntegral g (p * x, xᴴ * r) = l.splittingIntegral g (p, r) := by
  obtain ⟨⟨hr, -⟩, hp⟩ : (r.det ≠ 0 ∧ g.det ≠ 0) ∧ p.det ≠ 0 := by simpa using h_acc.det_ne_zero
  have h_cont : ContinuousOn (l.splittingIntegrand g p r) {y | y ∈ blockDiagAlg ε ∧ y.det ≠ 0} := by
    rintro y ⟨-, hy⟩
    have hz : (yᴴ * (r * g⁻¹ * p) * y).IsAccretive := h_acc.conjTranspose_mul_mul hy
    have h_minors (w : n → ℤ) {u : Matrix n n ℂ → Matrix n n ℂ} (hu : Continuous u)
        (hu_det : (u y).det ≠ 0) : ContinuousAt (fun y ↦ weightMinors w (u y)) y :=
      (analyticAt_weightMinors hu_det).continuousAt.comp hu.continuousAt
    exact ContinuousAt.continuousWithinAt (.div
      (.mul (h_minors _ (u := (p * ·)) (by fun_prop) (by simp [hp, hy]))
        (h_minors _ (u := (·ᴴ * r)) (by fun_prop) (by simp [hr, hy])))
      (h_minors _ (by fun_prop) hz.det_ne_zero) (hz.weightMinors_ne_zero _))
  -- Replacing `(p, r)` by `(p x, xᴴ r)` replaces `F(y)` by `F(x y)`.
  have h_shift (y : Matrix n n ℂ) :
      l.splittingIntegrand g (p * x) (xᴴ * r) y = l.splittingIntegrand g p r (x * y) := by
    simp only [HCParam.splittingIntegrand, conjTranspose_mul, mul_assoc]
  simpa only [HCParam.splittingIntegral, h_shift] using
    integral_haarK_mul_left_of_density hl.injective h_cont
      (fun y _ hy b hb_mem hb ↦ splittingIntegrand_mul_borel hl h_acc hy hb_mem hb) hx_mem hx_det

/-- The integral `I = HCParam.splittingIntegral l g` over `K` is complex analytic at each pair
`(p, r)` for which `r g⁻¹ p` is accretive. -/
theorem analyticAt_splittingIntegral {l : HCParam ε} {g p r : Matrix n n ℂ}
    (h_acc : (r * g⁻¹ * p).IsAccretive) :
    AnalyticAt ℂ (l.splittingIntegral g) (p, r) := by
  obtain ⟨⟨hr, -⟩, hp⟩ : (r.det ≠ 0 ∧ g.det ≠ 0) ∧ p.det ≠ 0 := by simpa using h_acc.det_ne_zero
  -- The integrand is an analytic function `Θ` of `(p, r)` and the pair `(k, kᴴ)`.
  let Θ : (Matrix n n ℂ × Matrix n n ℂ) × Matrix n n ℂ × Matrix n n ℂ → ℂ := fun ((p, r), y, z) ↦
    weightMinors l.lowestKType (p * y) * weightMinors l.lowestKType (z * r) /
      weightMinors (paramAddRho l) (z * (r * g⁻¹ * p) * y)
  refine (IsAnalyticFamily.of_analyticAt (by fun_prop) Θ
    (ι := fun k : maxCompactU ε ↦ ((k : Matrix n n ℂ), (k : Matrix n n ℂ)ᴴ))
    fun k ↦ ?_).analyticAt_integral _
  have hz : ((k : Matrix n n ℂ)ᴴ * (r * g⁻¹ * p) * k).IsAccretive :=
    h_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)
  -- The side conditions of `fun_prop` are the nonvanishing of minors and determinants; `det_mul`
  -- is applied only where it does not hide the product in `hz`.
  fun_prop (disch := simp [hp, hr, hz, hz.det_ne_zero, -det_mul, det_mul p, det_mul _ r,
    GeneralLinearGroup.det_ne_zero])

/-- Polarization: a complex linear form on pairs that vanishes at `(p Y, Yᴴ)` for all `Y` in a
complex subspace vanishes at `(p X, 0)` for each `X` in it, since `Y ↦ Yᴴ` is antilinear. -/
theorem apply_mul_zero_eq_zero_of_polarization {D : Matrix n n ℂ × Matrix n n ℂ →L[ℂ] ℂ}
    {S : Submodule ℂ (Matrix n n ℂ)} {p X : Matrix n n ℂ}
    (hD : ∀ Y ∈ S, D (p * Y, Yᴴ) = 0) (hX : X ∈ S) : D (p * X, 0) = 0 := by
  have h_sum : D (p * X, 0) + D (0, Xᴴ) = 0 := by simpa [← map_add] using hD X hX
  have h_pair : ((p * (Complex.I • X), (Complex.I • X)ᴴ) : Matrix n n ℂ × Matrix n n ℂ) =
      Complex.I • ((p * X, 0) - (0, Xᴴ)) := by simp
  have h_diff : D (p * X, 0) - D (0, Xᴴ) = 0 := by
    rw [← smul_eq_zero_iff_right Complex.I_ne_zero, ← map_sub, ← map_smul, ← h_pair]
    exact hD _ (S.smul_mem Complex.I hX)
  linear_combination (h_sum + h_diff) / 2

/-- Let `l` have gap `h`, let `p` be block diagonal for the signs and let `g⁻¹ p` be accretive.
Then the derivative at `(p, 1)` of `I = HCParam.splittingIntegral l g` vanishes at `(X, 0)` for
each block diagonal `X`. -/
theorem fderiv_splittingIntegral_eq_zero {l : HCParam ε} {h : ℕ} (hl : l.HasGap h)
    {g p X : Matrix n n ℂ} (hp : p ∈ blockDiagAlg ε) (h_acc : (g⁻¹ * p).IsAccretive)
    (hX : X ∈ blockDiagAlg ε) :
    fderiv ℂ (l.splittingIntegral g) (p, 1) (X, 0) = 0 := by
  have h_acc' : (1 * g⁻¹ * p).IsAccretive := by rwa [one_mul]
  have h_diff : DifferentiableAt ℂ (l.splittingIntegral g) (p, 1) :=
    (analyticAt_splittingIntegral h_acc').differentiableAt
  -- By invariance `I` is constant along `t ↦ (p x, xᴴ)`, `x = 1 + t Y`, for small real `t`.
  have h_real (Y : Matrix n n ℂ) (hY : Y ∈ (blockDiagAlg ε).toSubmodule) :
      fderiv ℂ (l.splittingIntegral g) (p, 1) (p * Y, Yᴴ) = 0 := by
    refine ((h_diff.hasFDerivAt.restrictScalars ℝ).hasLineDerivAt (p * Y, Yᴴ)).unique
      ((hasDerivAt_const 0 (l.splittingIntegral g (p, 1))).congr_of_eventuallyEq ?_)
    have h_det : ∀ᶠ t : ℝ in nhds 0, (1 + t • Y).det ≠ 0 :=
      ContinuousAt.eventually_ne (by fun_prop) (by simp)
    filter_upwards [h_det] with t ht
    simpa [mul_add, star_trivial] using splittingIntegral_mul_conjTranspose_mul hl h_acc'
      (add_mem (one_mem _) ((blockDiagAlg ε).smul_mem hY (t : ℂ)) : 1 + t • Y ∈ blockDiagAlg ε) ht
  simpa [h_acc.det_ne_zero_and_inv_mul.1] using apply_mul_zero_eq_zero_of_polarization h_real
    (mul_mem (blockDiagAlg.inv_mem hp) hX : p⁻¹ * X ∈ blockDiagAlg ε)

/-! ### Independence of the splitting -/

/-- Independence of the splitting: let `l = 2λ` have gap `h` (distinct entries ≡ `card n - 1` mod 2,
`|λ i - λ j| ≥ h` when `ε i ≠ ε j`) and let `g` be any complex matrix. Then Flensted-Jensen's
integral `l.flenstedJensen a z = ∫_K m_Λ(ak) conj(m_Λ(k)) / m_{−λ−ρ}(kᴴzk) dk / ∫_K |m_Λ|²` at
`z = a⁻¹ g` is the same for all `a` commuting with `diag ε` with `a⁻¹ g` accretive (`z + zᴴ`
positive definite). -/
theorem flenstedJensen_eq_of_accretive {l : HCParam ε} {h : ℕ} (hl : l.HasGap h)
    {g a b : Matrix n n ℂ} (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive)
    (hb : b ∈ blockDiagAlg ε) (hb_acc : (b⁻¹ * g).IsAccretive) :
    l.flenstedJensen b (b⁻¹ * g) = l.flenstedJensen a (a⁻¹ * g) := by
  -- The `p` that commute with the signs and make `g⁻¹ p` accretive form a convex set, and
  -- `p ↦ I(p, 1)` has derivative zero along it; so it is constant on the segment from `a` to `b`.
  have h_convex : Convex ℝ {p : Matrix n n ℂ | (g⁻¹ * p).IsAccretive} :=
    convex_iff_forall_pos.2 fun x hx y hy s t hs ht _ ↦ by
      simpa [IsAccretive, mul_add, add_mul, add_add_add_comm, star_trivial] using
        (hx.smul hs).add (hy.smul ht)
  have h_deriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ l.splittingIntegral g (a + t • (b - a), 1)) 0 t := by
    have h_mem : a + t • (b - a) ∈ blockDiagAlg ε :=
      add_mem ha ((blockDiagAlg ε).smul_mem (sub_mem hb ha) (t : ℂ))
    have h_acc : (g⁻¹ * (a + t • (b - a))).IsAccretive := h_convex.add_smul_sub_mem
      ha_acc.det_ne_zero_and_inv_mul.2 hb_acc.det_ne_zero_and_inv_mul.2 ht
    have h_line : HasDerivAt (fun t : ℝ ↦ (a + t • (b - a), (1 : Matrix n n ℂ))) (b - a, 0) t := by
      simpa using (((hasDerivAt_id t).smul_const (b - a)).const_add a).prodMk (hasDerivAt_const t 1)
    have h_diff : DifferentiableAt ℂ (l.splittingIntegral g) (a + t • (b - a), 1) :=
      (analyticAt_splittingIntegral (by rwa [one_mul])).differentiableAt
    exact ((h_diff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t h_line).congr_deriv
      (fderiv_splittingIntegral_eq_zero hl h_mem h_acc (sub_mem hb ha))
  have h_const : l.splittingIntegral g (b, 1) = l.splittingIntegral g (a, 1) := by
    simpa using constant_of_has_deriv_right_zero (HasDerivAt.continuousOn h_deriv)
      (fun t ht ↦ (h_deriv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 (by simp)
  simp [flenstedJensen_eq_splittingIntegral, ha_acc, hb_acc, h_const]

/-- Let `l = 2λ` be a parameter of some gap `m` (distinct entries of one parity, those of `λ` at
opposite signs at least `m` apart) and `g` in `U(diag ε)`. Then c_λ(g) = `l.dsCoeff g` is
Flensted-Jensen's integral at `(a, a⁻¹ g)` for any block diagonal `a` such that `a⁻¹ g` is
accretive (positive definite Hermitian part). -/
theorem dsCoeff_eq_flenstedJensen {l : HCParam ε} {m : ℕ} (hl : l.HasGap m) {g : USign ε}
    {a : Matrix n n ℂ} (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive) :
    l.dsCoeff g = l.flenstedJensen a (a⁻¹ * g) :=
  flenstedJensen_eq_of_accretive hl ha ha_acc (blockDiagPart_mem _) (by simp)

/-- Let `l = 2λ` be a parameter of gap `h` and `g = p z qᴴ` with `p`, `q` block diagonal and `z`
accretive (`z + zᴴ > 0`). For block diagonal `a` with `a⁻¹ g` accretive, Flensted-Jensen's integral
at `(a, a⁻¹ g)` is `∫_K m_Λ(p k) conj m_Λ(q k) / m_{-λ-ρ}(kᴴ z k) dk / ∫_K |m_Λ|²`, with the
products of minors `m_w = weightMinors w`, `Λ = l.lowestKType` and `λ + ρ = paramAddRho l`. For
invertible `p`, `q` one such `a` is `p q⁻¹`, so the integral depends only on the product
`p z qᴴ`. -/
theorem flenstedJensen_eq_integral_of_eq_mul_mul_conjTranspose {h : ℕ} (hl : l.HasGap h)
    {g a p q z : Matrix n n ℂ} (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive)
    (hp : p ∈ blockDiagAlg ε) (hq : q ∈ blockDiagAlg ε) (hz : z.IsAccretive)
    (h_split : g = p * z * qᴴ) :
    l.flenstedJensen a (a⁻¹ * g) =
      (∫ k : maxCompactU ε, weightMinors l.lowestKType (p * k) *
          conj (weightMinors l.lowestKType (q * k)) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  -- The integral is `I(p, qᴴ)`, `I = l.splittingIntegral g`. By invariance it is `I(p q⁻¹, 1)`,
  -- the value at the splitting `g = (p q⁻¹) (q z qᴴ)`, which does not depend on the left factor.
  obtain ⟨hp_det, hq_det⟩ : p.det ≠ 0 ∧ q.det ≠ 0 := by
    simpa [h_split, hz.det_ne_zero] using ha_acc.det_ne_zero_and_inv_mul.1
  have h_left : (p * q⁻¹)⁻¹ * g = q * z * qᴴ := by
    simp [h_split, Matrix.mul_inv_rev, mul_assoc, hp_det, hq_det]
  have h_acc : ((p * q⁻¹)⁻¹ * g).IsAccretive := by
    simpa [h_left] using hz.conjTranspose_mul_mul (show qᴴ.det ≠ 0 by simp [hq_det])
  have h_invariance : l.splittingIntegral g (p * q⁻¹, 1) = l.splittingIntegral g (p, qᴴ) := by
    have h_shift :
        l.splittingIntegral g (p * q⁻¹ * q, qᴴ * 1) = l.splittingIntegral g (p * q⁻¹, 1) :=
      splittingIntegral_mul_conjTranspose_mul hl (by simpa using h_acc.det_ne_zero_and_inv_mul.2) hq
        hq_det
    rw [← h_shift, nonsing_inv_mul_cancel_right q p hq_det.isUnit, mul_one]
  have h_value : l.flenstedJensen a (a⁻¹ * g) =
      l.splittingIntegral g (p, qᴴ) / l.lowestKType.kTypeNormSq := by
    rw [flenstedJensen_eq_of_accretive hl (mul_mem hp (blockDiagAlg.inv_mem hq)) h_acc ha ha_acc,
      flenstedJensen_eq_splittingIntegral h_acc, h_invariance]
  -- It remains to compare the denominators of the two integrands.
  have h_middle : qᴴ * g⁻¹ * p = z⁻¹ := by
    simp [h_split, Matrix.mul_inv_rev, mul_assoc, hp_det, hq_det]
  have h_denom (k : maxCompactU ε) :
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) =
        weightMinors (paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z⁻¹ * k) := by
    have h_inv : ((k : Matrix n n ℂ)ᴴ * z * k)⁻¹ = (k : Matrix n n ℂ)ᴴ * z⁻¹ * k := by
      simp [← maxCompactU.coe_inv, Matrix.mul_inv_rev, mul_assoc]
    rw [weightMinors_neg (hz.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)).det_ne_zero,
      h_inv]
  simp only [h_value, HCParam.splittingIntegral, HCParam.splittingIntegrand, h_middle, h_denom,
    conj_weightMinors, conjTranspose_mul]

/-! ### The coefficient as a holomorphic function on the set of products -/

variable (ε) in
/-- The set of the matrices `g` for which `z = a⁻¹ g` is accretive (`z + zᴴ > 0`) for some `a` that
is block diagonal for the signs `ε`; such an `a` is invertible. These are the products `p z qᴴ` with
`p`, `q` invertible and block diagonal and `z` accretive; see `New.mem_splittable_iff`. -/
def splittable : Set (Matrix n n ℂ) :=
  {g : Matrix n n ℂ | ∃ a ∈ blockDiagAlg ε, (a⁻¹ * g).IsAccretive}

/-- A matrix lies in `New.splittable ε` if and only if it is a product `p z qᴴ` with `p`, `q`
invertible and block diagonal for the signs `ε` and `z` accretive. -/
theorem mem_splittable_iff {g : Matrix n n ℂ} :
    g ∈ splittable ε ↔ ∃ p ∈ blockDiagAlg ε, ∃ q ∈ blockDiagAlg ε, ∃ z : Matrix n n ℂ,
      p.det ≠ 0 ∧ q.det ≠ 0 ∧ z.IsAccretive ∧ g = p * z * qᴴ := by
  constructor
  · rintro ⟨a, ha, ha_acc⟩
    obtain ⟨ha_det, -⟩ : a.det ≠ 0 ∧ g.det ≠ 0 := by simpa using ha_acc.det_ne_zero
    exact ⟨a, ha, 1, one_mem _, a⁻¹ * g, ha_det, by simp, ha_acc, by simp [ha_det]⟩
  · rintro ⟨p, hp, q, hq, z, hp_det, hq_det, hz, rfl⟩
    have h_left : (p * q⁻¹)⁻¹ * (p * z * qᴴ) = qᴴᴴ * z * qᴴ := by
      simp [Matrix.mul_inv_rev, mul_assoc, hp_det, hq_det]
    refine ⟨p * q⁻¹, mul_mem hp (blockDiagAlg.inv_mem hq), ?_⟩
    rw [h_left]
    exact hz.conjTranspose_mul_mul (by simp [hq_det])

/-- If `a⁻¹ g` is accretive, then so is `a⁻¹ x` for all `x` near `g`. -/
theorem eventually_isAccretive_inv_mul {a g : Matrix n n ℂ} (h_acc : (a⁻¹ * g).IsAccretive) :
    ∀ᶠ x : Matrix n n ℂ in nhds g, (a⁻¹ * x).IsAccretive :=
  (continuous_const_mul a⁻¹).continuousAt.eventually h_acc.setOf_mem_nhds

open scoped Classical in
/-- The coefficient on the set `New.splittable ε` of products: Flensted-Jensen's integral at
`(a, a⁻¹ g)` for a chosen block diagonal `a` with `a⁻¹ g` accretive, and `0` off this set. -/
noncomputable def HCParam.splitCoeff (l : HCParam ε) (g : Matrix n n ℂ) : ℂ :=
  if h_mem : g ∈ splittable ε then l.flenstedJensen h_mem.choose (h_mem.choose⁻¹ * g) else 0

/-- For a parameter `l` of gap `h`, the coefficient `l.splitCoeff g` is Flensted-Jensen's integral
at `(a, a⁻¹ g)` for every block diagonal `a` with `a⁻¹ g` accretive. -/
theorem splitCoeff_eq_flenstedJensen {h : ℕ} (hl : l.HasGap h) {g a : Matrix n n ℂ}
    (ha : a ∈ blockDiagAlg ε) (ha_acc : (a⁻¹ * g).IsAccretive) :
    l.splitCoeff g = l.flenstedJensen a (a⁻¹ * g) := by
  have h_mem : g ∈ splittable ε := ⟨a, ha, ha_acc⟩
  rw [HCParam.splitCoeff, dite_eq_left h_mem]
  obtain ⟨hb, hb_acc⟩ := h_mem.choose_spec
  exact flenstedJensen_eq_of_accretive hl ha ha_acc hb hb_acc

/-- The coefficient at a product. Let `l = 2λ` be a parameter of gap `h`: its entries are distinct
and congruent to `card n - 1` mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Let `p`, `q` be
invertible and block diagonal (commuting with `diag ε`) and `z` accretive (`z + zᴴ > 0`). Consider
`l.splitCoeff`, which at a matrix `g` with `a⁻¹ g` accretive for some block diagonal `a` is
Flensted-Jensen's integral at `(a, a⁻¹ g)` for a chosen such `a`, and is `0` elsewhere. Then
`l.splitCoeff (p z qᴴ)` is `∫_K m_Λ(p k) conj m_Λ(q k) / m_{-λ-ρ}(kᴴ z k) dk / ∫_K |m_Λ|²`; here
`K = U(diag ε) ∩ U(n)` carries its Haar measure of mass one, `m_w = weightMinors w` is the product
of principal minors of weight `w`, `Λ = l.lowestKType` and `λ + ρ = paramAddRho l`. -/
theorem splitCoeff_mul_mul_conjTranspose {h : ℕ} (hl : l.HasGap h) {p q z : Matrix n n ℂ}
    (hp : p ∈ blockDiagAlg ε) (hq : q ∈ blockDiagAlg ε) (hp_det : p.det ≠ 0) (hq_det : q.det ≠ 0)
    (hz : z.IsAccretive) :
    l.splitCoeff (p * z * qᴴ) =
      (∫ k : maxCompactU ε, weightMinors l.lowestKType (p * k) *
          conj (weightMinors l.lowestKType (q * k)) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  obtain ⟨a, ha, ha_acc⟩ := mem_splittable_iff.2 ⟨p, hp, q, hq, z, hp_det, hq_det, hz, rfl⟩
  rw [splitCoeff_eq_flenstedJensen hl ha ha_acc]
  exact flenstedJensen_eq_integral_of_eq_mul_mul_conjTranspose hl ha ha_acc hp hq hz rfl

/-- Let `l = 2λ` be a parameter of gap `h`: its entries are distinct and congruent to `card n - 1`
mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Then for every `g` in `U(diag ε)`,
`l.splitCoeff g = l.dsCoeff g`. Here `splitCoeff` is Flensted-Jensen's integral at `(a, a⁻¹ g)` for
a block diagonal `a` with `a⁻¹ g` accretive (and `0` if there is none), and `dsCoeff` is
`c_λ(g) = Ξ(a, a⁻¹ g)` with `a` the block diagonal part of `g`. -/
theorem splitCoeff_eq_dsCoeff {h : ℕ} (hl : l.HasGap h) (g : USign ε) :
    l.splitCoeff g = l.dsCoeff g :=
  splitCoeff_eq_flenstedJensen hl (blockDiagPart_mem _) (isAccretive_blockDiagPart_inv_mul g).2

/-- The coefficient in any splitting. Let `l = 2λ` be a parameter of gap `m`: its entries are
distinct and congruent to `card n - 1` mod 2, and `|λ i - λ j| ≥ m` whenever `ε i ≠ ε j`. Let `g` in
`U(diag ε)` be a product `p z qᴴ` with `p`, `q` block diagonal (commuting with `diag ε`) and `z`
accretive (`z + zᴴ > 0`). Then `l.dsCoeff g`, the function `c_λ(g) = Ξ(a, a⁻¹g)` with `a` the block
diagonal part of `g` and `Ξ` Flensted-Jensen's normalised integral, is `∫_K m_Λ(p k) conj m_Λ(q
k) / m_{-λ-ρ}(kᴴ z k) dk / ∫_K |m_Λ|²`; here `K = U(diag ε) ∩ U(n)` carries its Haar measure of mass
one, `m_w = weightMinors w` is the product of principal minors of weight `w`, `Λ = l.lowestKType`
and `λ + ρ = paramAddRho l`. -/
theorem dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose {m : ℕ} (hl : l.HasGap m) {g : USign ε}
    {p q z : Matrix n n ℂ} (hp : p ∈ blockDiagAlg ε) (hq : q ∈ blockDiagAlg ε)
    (hz : z.IsAccretive) (h_split : (g : Matrix n n ℂ) = p * z * qᴴ) :
    l.dsCoeff g =
      (∫ k : maxCompactU ε, weightMinors l.lowestKType (p * k) *
          conj (weightMinors l.lowestKType (q * k)) /
          weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * z * k) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  obtain ⟨hp_det, hq_det⟩ : p.det ≠ 0 ∧ q.det ≠ 0 := by
    simpa [h_split, hz.det_ne_zero] using GeneralLinearGroup.det_ne_zero (g : GL n ℂ)
  rw [← splitCoeff_eq_dsCoeff hl, h_split]
  exact splitCoeff_mul_mul_conjTranspose hl hp hq hp_det hq_det hz

end New

/-! ## Triangular factors -/

namespace New.DiscreteSeries

open Matrix MeasureTheory ComplexConjugate ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {h : ℕ}

/-- Let `l = 2λ` be a parameter of gap `h` (in particular with distinct entries), and let `b'` and
`b` be block diagonal and invertible, with `b'` lower and `b` upper triangular in the order of
decreasing `l`. Let `c = l.splitCoeff` be Flensted-Jensen's integral at `(a, a⁻¹ g)` for a block
diagonal `a` with `a⁻¹ g` accretive, on the open set `New.splittable ε` of the products `p z qᴴ`
with `p`, `q` invertible and block diagonal and `z` accretive (`z + zᴴ > 0`). Then for `g` in this
set, `c (b' g b) = b' ^ Λ b ^ Λ c g`, where `b ^ Λ = ∏ i, b i i ^ Λ i` and `Λ = l.lowestKType` is
the highest weight of the lowest `K`-type. -/
theorem splitCoeff_triangular_mul_mul_triangular {l : HCParam ε} (hl : l.HasGap h)
    {b' g b : Matrix n n ℂ} (hb'_mem : b' ∈ blockDiagAlg ε) (hb' : IsBorelMatrix l b')
    (hb_mem : b ∈ blockDiagAlg ε) (hb : IsBorelMatrix (-l) b) (hg : g ∈ splittable ε) :
    l.splitCoeff (b' * g * b) =
      diagChar l.lowestKType b' * diagChar l.lowestKType b * l.splitCoeff g := by
  -- Replace `p`, `q` by `b' p`, `bᴴ q` in the integral; both factors come out of the minors.
  obtain ⟨p, hp, q, hq, z, hp_det, hq_det, hz, rfl⟩ := mem_splittable_iff.1 hg
  have hb_adj_mem : bᴴ ∈ blockDiagAlg ε := conjTranspose_mem_blockDiagAlg hb_mem
  have hb_adj : IsBorelMatrix l bᴴ := isBorelMatrix_conjTranspose hb
  have h_minors {a x : Matrix n n ℂ} (ha_mem : a ∈ blockDiagAlg ε) (ha : IsBorelMatrix l a)
      (hx : x.det ≠ 0) (k : maxCompactU ε) : weightMinors l.lowestKType (a * x * k) =
        diagChar l.lowestKType a * weightMinors l.lowestKType (x * k) := by
    rw [mul_assoc]
    exact hl.isKDominant_lowestKType.weightMinors_oppBorel_mul hl.neg.injective
      (by simp [hx, GeneralLinearGroup.det_ne_zero]) ha_mem (by rwa [neg_neg])
  have h_char : conj (diagChar l.lowestKType bᴴ) = diagChar l.lowestKType b := by simp [diagChar]
  have h_split : b' * (p * z * qᴴ) * b = b' * p * z * (bᴴ * q)ᴴ := by simp [mul_assoc]
  have hb'p : (b' * p).det ≠ 0 := by simp [hb'.right, hp_det]
  have hbq : (bᴴ * q).det ≠ 0 := by simp [hb.right, hq_det]
  rw [h_split, splitCoeff_mul_mul_conjTranspose hl hp hq hp_det hq_det hz,
    splitCoeff_mul_mul_conjTranspose hl (mul_mem hb'_mem hp) (mul_mem hb_adj_mem hq) hb'p hbq hz,
    ← mul_div_assoc, ← integral_const_mul]
  -- Both sides now have the same denominator, and the integrands agree at each `k`.
  congr 1
  refine integral_congr_ae (.of_forall fun k ↦ ?_)
  simp only [h_minors hb'_mem hb' hp_det, h_minors hb_adj_mem hb_adj hq_det, map_mul, h_char]
  ring

/-- Let `l = 2λ` be a parameter of gap `h` (in particular with distinct entries), and
let `b'` and `b` be block diagonal and invertible, `b'` lower and `b` upper triangular in the order
of decreasing `l`. If `y` and `b' y b` are accretive (positive definite Hermitian part), then
Flensted-Jensen's coefficient `c = l.flenstedJensen 1` satisfies `c (b' y b) = b' ^ Λ b ^ Λ c y`,
where `b ^ Λ = ∏ i, b i i ^ Λ i` for the highest weight `Λ` of the lowest `K`-type. -/
theorem flenstedJensen_triangular_mul_mul_triangular {l : HCParam ε} (hl : l.HasGap h)
    {b' y b : Matrix n n ℂ} (hb'_mem : b' ∈ blockDiagAlg ε) (hb' : IsBorelMatrix l b')
    (hb_mem : b ∈ blockDiagAlg ε) (hb : IsBorelMatrix (-l) b) (hy : y.IsAccretive)
    (hb'yb : (b' * y * b).IsAccretive) :
    l.flenstedJensen 1 (b' * y * b) =
      diagChar l.lowestKType b' * diagChar l.lowestKType b * l.flenstedJensen 1 y := by
  -- At an accretive matrix the left factor `1` is admissible.
  have h_value {x : Matrix n n ℂ} (hx : x.IsAccretive) : l.flenstedJensen 1 x = l.splitCoeff x := by
    simpa using (splitCoeff_eq_flenstedJensen hl (one_mem _) (by simpa using hx)).symm
  rw [h_value hy, h_value hb'yb]
  exact splitCoeff_triangular_mul_mul_triangular hl hb'_mem hb' hb_mem hb
    ⟨1, one_mem _, by simpa using hy⟩

end New.DiscreteSeries

/-! ## c_λ as a smooth function on U(diag ε) -/

section PsiSmooth

open Set Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (l : New.HCParam (n := n) ε)

/-- The function c_λ, l = 2λ, regarded as an element of the space of smooth complex functions on
U(diag ε). -/
@[simps]
noncomputable def New.HCParam.dsCoeffSmooth : SmoothU ε ℂ :=
  ⟨(l.dsCoeff ·),
    -- Multiply `dsCoeff` by a smooth cutoff that is `1` on the closed image of the group and is
    -- supported where `dsCoeff` is analytic.
    have ⟨f, hf⟩ : ∃ f : SmoothPartitionOfUnity Unit (modelWithCornersSelf ℝ (Matrix n n ℂ))
          (Matrix n n ℂ) (range fun x : U (signMatrix ε) ↦ x),
        f.IsSubordinate fun _ : Unit ↦ {x : Matrix n n ℂ | AnalyticAt ℂ l.dsCoeff x} :=
      SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ (Matrix n n ℂ))
        isClosedEmbedding_U.isClosed_range _ (fun _ ↦ isOpen_analyticAt ℂ l.dsCoeff)
        (subset_iUnion_of_subset () (range_subset_iff.mpr analyticAt_dsCoeff))
    ⟨⟨_, (f.contMDiff_finsum_smul fun i _ hx ↦
        (hf i hx).restrictScalars.contDiffAt.contMDiffAt).contDiff⟩,
      funext (by simp [↓← finsum_smul, f.sum_eq_one])⟩⟩

/-- The function c_λ = `HCParam.dsCoeff l` is continuous on U(diag ε): its composite with any
continuous map `f : X → U(diag ε)` is continuous. Here c_λ(g) = Ξ(a, a⁻¹g), with `a` the block
diagonal part of `g` and Ξ Flensted-Jensen's normalised integral. -/
@[fun_prop]
lemma New.continuous_dsCoeff {X : Type*} [TopologicalSpace X] {f : X → USign ε}
    (hf : Continuous f) : Continuous (fun x : X ↦ l.dsCoeff (f x)) :=
  (SmoothU.continuous l.dsCoeffSmooth).comp hf

end PsiSmooth

/-! ## The Casimir eigenvalue of c_λ -/

namespace New

open Matrix Filter Norms.L2Operator ContinuousMap GlModule U HCParam

variable {n : Type _} [Fintype n] {ε : n → ℤˣ} {h : ℕ}

/-- The indices can be numbered so that an injective integer vector l is strictly increasing. -/
theorem exists_equiv_fin_lt_iff {l : n → ℤ} (hl : l.Injective) :
    ∃ e : Fin (Fintype.card n) ≃ n, ∀ a b : Fin (Fintype.card n), l (e a) < l (e b) ↔ a < b := by
  -- Enumerate `n` increasingly for the linear order pulled back along `l`.
  let _ : LinearOrder n := .lift' l hl
  exact ⟨(monoEquivOfFin n rfl).toEquiv, fun a b ↦ (monoEquivOfFin n rfl).lt_iff_lt⟩

/-- For a parameter `l = 2λ` of gap `h`, the eigenvalue |λ|² − |ρ|² = `HCParam.casimirValue l` is
the value `casimirKValue` that the Casimir operator takes on a lowest weight vector of weight
`λ + ρ`, that is, a highest vector for the roots positive for `-l`, all pairs of indices counting
as compact (`compactForm`). -/
theorem casimirValue_eq_casimirKValue_paramAddRho {l : HCParam (n := n) ε}
    (hl : l.HasGap h) :
    (l.casimirValue : ℂ) = (-l).compactForm.casimirKValue (paramAddRho l) := by
  -- Substitute `l = 2 (λ + ρ) - 2ρ`; the positive roots for `-l` are the negatives of those of `l`.
  simp [casimirKValue, casimirValue, twoRho_neg, ← sub_eq_of_eq_add (two_mul_paramAddRho hl _)]
  simp only [twoRho, Pi.top_apply, Prop.top_eq_true, true_and]
  grind

/-- Let `l` have gap `h`, let `y` be in U(diag ε), `k` in K and `a⁻¹ y` accretive. Let `F`, with
values in continuous functions on K, be differentiable at `y`, and let `F x k` agree for matrices
`x` near `y` with the integrand of Flensted-Jensen's integral at `(a, a⁻¹ x)`, a quotient of
products of principal minors `weightMinors`. For `l i ≤ l j`, the derivative of `F` in the direction
`y (k E_ij k⁻¹)`, evaluated at `k`, is `(λ + ρ) i` times `F y k` if `i = j` and zero otherwise,
where λ + ρ = `paramAddRho l`. -/
theorem fderiv_flenstedJensen_integrand_single [DecidableEq n] {l : HCParam (n := n) ε}
    (hl : l.HasGap h) {a : Matrix n n ℂ} {F : Matrix n n ℂ → C(maxCompactU ε, ℂ)} {y : USign ε}
    (k : maxCompactU ε)
    (hF : ∀ᶠ x : Matrix n n ℂ in nhds (y : Matrix n n ℂ), F x k =
      weightMinors l.lowestKType (a * k) * starRingEnd ℂ (weightMinors l.lowestKType k) /
        weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * (a⁻¹ * x) * k))
    (hF_diff : DifferentiableAt ℂ F y) (h_acc : (a⁻¹ * y).IsAccretive) {i j : n} (hij : l i ≤ l j) :
    fderiv ℂ F y ((y : Matrix n n ℂ) * ((k : Matrix n n ℂ) * single i j 1 * (k : GL n ℂ)⁻¹.val)) k =
      (if i = j then (paramAddRho l i : ℂ) else 0) * F y k := by
  -- Under `y ↦ c t = y * (k * t * k⁻¹)` with `t` triangular for `l` the integrand is multiplied by
  -- `diagChar (paramAddRho l) t`, because the argument of `weightMinors (-paramAddRho l)` is
  -- multiplied by `t` on the right.
  let c : Matrix n n ℂ → Matrix n n ℂ := fun t ↦ y * (k * t * (k : GL n ℂ)⁻¹.val)
  have h_equivariant : ∀ᶠ x : Matrix n n ℂ in nhds (y : Matrix n n ℂ), ∀ t ∈ blockDiagAlg 1,
      IsBorelMatrix (- -l) t → x = c t → F x k = diagChar (paramAddRho l) t * F y k := by
    filter_upwards [hF] with x hx t t_mem t_tri x_eq
    have h_arg :
        (k : Matrix n n ℂ)ᴴ * (a⁻¹ * c t) * k = (k : Matrix n n ℂ)ᴴ * (a⁻¹ * y) * k * t := by
      simp [c, mul_assoc, GeneralLinearGroup.det_ne_zero]
    rw [hx, hF.self_of_nhds, x_eq, h_arg,
      hl.isKDominant_neg_paramAddRho.weightMinors_mul_borel hl.injective
        (h_acc.conjTranspose_mul_mul (GeneralLinearGroup.det_ne_zero _)).det_ne_zero t_mem
        (by rwa [neg_neg] at t_tri)]
    simp [diagChar, field]
  -- Differentiate along `t = 1 + s • single i j 1`, which is triangular as `l i ≤ l j`.
  have h_direction (s : ℂ) : ↑y + s • c (single i j 1) = c (1 + s • single i j 1) := by
    simp [c, mul_add, add_mul, -smul_single]
  exact fderiv_eq_of_borel_equivariant 1 (f := evalCLM ℂ k ∘ F) (o := -l)
    ((evalCLM ℂ k).hasFDerivAt.comp _ hF_diff.hasFDerivAt) (neg_le_neg hij) rfl c h_equivariant
    h_direction

/-- Let `l = 2λ` have gap `h` (distinct entries congruent to `card n - 1` mod 2, with
|λ_i − λ_j| ≥ h whenever ε_i ≠ ε_j), let `f` be a smooth function on U(diag ε) with values in `E`,
let `L` be a continuous linear form on `E` and `k` an invertible matrix. Suppose that near `g` the
function `L ∘ f` is a lowest weight vector of weight λ + ρ = `paramAddRho l` in the basis
`k E_ab k⁻¹` of gl_n, acting by right derivatives. Then the Casimir operator `casimirK 1` of gl_n
multiplies the value of `L ∘ f` at `g` by |λ|² − |ρ|² = `l.casimirValue`. -/
theorem apply_casimirK_rightDeriv_of_lowest_weight [DecidableEq n] {l : HCParam (n := n) ε}
    (hl : l.HasGap h) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : SmoothU ε E)
    (L : E →L[ℂ] ℂ) (k : GL n ℂ) (g : USign ε)
    (h_lowest : ∀ a b : n, l a ≤ l b → ∀ᶠ y : USign ε in nhds g,
      L ((rightDeriv ε E (k.val * single a b 1 * k⁻¹.val) f).val y) =
        (if a = b then (paramAddRho l a : ℂ) else 0) * L (f.val y)) :
    L (((rightDeriv ε E).casimirK 1 f).val g) = l.casimirValue * L (f.val g) := by
  -- The germs at `g` of the functions `L ∘ u` form a module `σ`, as right derivatives are local.
  let germ : SmoothU ε E →ₗ[ℂ] Germ (nhds g) ℂ :=
    { toFun u := Germ.ofFun (L ∘ u.val)
      map_add' u v := congrArg Germ.ofFun (funext fun y ↦ L.map_add (u.val y) (v.val y))
      map_smul' c u := congrArg Germ.ofFun (funext fun y ↦ L.map_smul c (u.val y)) }
  have h_ker (X : Matrix n n ℂ) (u : SmoothU ε E) (hu : germ u = 0) :
      germ (rightDeriv ε E X u) = 0 :=
    have h_zero : (0 : SmoothU ε ℂ).val =ᶠ[nhds g] L ∘ u.val := Germ.coe_eq.1 hu.symm
    have h_deriv : (rightDeriv ε ℂ X 0).val =ᶠ[nhds g] L ∘ (rightDeriv ε E X u).val :=
      rightDeriv_comp_clm L h_zero
    h_deriv.germ_eq.symm.trans (by simp)
  obtain ⟨σ, hσ⟩ : ∃ σ : GlModule n germ.range, ∀ (X : Matrix n n ℂ) (u : SmoothU ε E),
      σ X (germ.rangeRestrict u) = germ.rangeRestrict (rightDeriv ε E X u) :=
    (rightDeriv ε E).exists_action_on_range germ h_ker
  -- In the basis `k E_ab k⁻¹`, given by `σ.adTwist k`, the germ of `L ∘ f` is a highest vector.
  have highest : (-l).compactForm.IsKHighest (σ.adTwist k) (paramAddRho l)
      (germ.rangeRestrict f) := by
    refine .of_E_eq_smul fun a b _ hab ↦ (hσ _ f).trans (Subtype.ext ?_)
    -- As germs at `g`, this is the hypothesis on `L ∘ f`.
    exact Germ.coe_eq.2 (h_lowest a b (neg_le_neg_iff.1 hab))
  -- On a highest vector the Casimir, which does not depend on the basis, is a scalar.
  have h_germ : germ.rangeRestrict ((rightDeriv ε E).casimirK 1 f) =
      (l.casimirValue : ℂ) • germ.rangeRestrict f := by
    rw [casimirValue_eq_casimirKValue_paramAddRho hl,
      ← highest.casimirK_eq_smul (hg := hl.neg.signs_one), casimirK_one_adTwist]
    simp [GlModule.casimir, hσ]
  exact congrArg (fun v : germ.range ↦ v.val.value) h_germ

/-- Let `l = 2λ` be a parameter of gap `h`: its entries are distinct and congruent to `card n - 1`
mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Then the Casimir operator Ω = Σ_{a,b} E_ab E_ba
of gl_n, acting on smooth functions on U(diag ε) by complexified right derivatives, satisfies
Ωc_λ = (|λ|² − |ρ|²) c_λ. Here c_λ is `HCParam.dsCoeffSmooth l`, ρ is the half sum of the roots
positive for `l`, and the eigenvalue is `HCParam.casimirValue l`. The operator
`New.GlModule.casimirK` sums over the pairs with equal signs; for the constant sign vector 1 these
are all pairs, so `casimirK 1` is Ω.

This proves the Casimir eigenvalue formula of Harish-Chandra's discrete series in the case of the
explicit function c_λ on U(p,q) (Flensted-Jensen's function), for any gap. -/
theorem casimir_dsCoeffSmooth [DecidableEq n] {l : HCParam (n := n) ε} [hl : l.HasGap h] :
    (rightDeriv ε ℂ).casimirK 1 l.dsCoeffSmooth = (l.casimirValue : ℂ) • l.dsCoeffSmooth := by
  -- Near `g`, `l.dsCoeffSmooth` is the average over `k` of the integrand `Φ · k` of
  -- `flenstedJensen`, with the block diagonal factor frozen at `blockDiagPart ε g`. For fixed
  -- `k` the germ of `Φ · k` is a lowest weight vector in the basis `k E_ij k⁻¹`.
  ext g
  let Φ (x : Matrix n n ℂ) (k : maxCompactU ε) : ℂ :=
    weightMinors l.lowestKType (blockDiagPart ε g * k) *
      starRingEnd ℂ (weightMinors l.lowestKType k) /
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * ((blockDiagPart ε g)⁻¹ * x) * k)
  -- Near `g`, `Φ` is given by an analytic map `F₀` into `C(K, ℂ)`, so by a globally smooth `F`.
  obtain ⟨F₀, F₀_an, F₀_eq⟩ : DiscreteSeries.IsAnalyticFamily Φ g :=
    isAnalyticFamily_flenstedJensen l analyticAt_const (isAccretive_blockDiagPart_inv_mul g).2
  obtain ⟨F, F_smooth, F_eq⟩ := exists_contDiff_eventuallyEq F₀_an.restrictScalars.contDiffAt
  have F_Φ : ∀ᶠ x : Matrix n n ℂ in nhds (g : Matrix n n ℂ), F x = Φ x := by
    filter_upwards [F₀_eq, F_eq] with x hx₀ hx using by rw [hx, hx₀]
  have near : ∀ᶠ y : USign ε in nhds g, (∀ᶠ x in nhds (y : Matrix n n ℂ), F x = Φ x) ∧
      AnalyticAt ℂ F y ∧ ((blockDiagPart ε g)⁻¹ * y).IsAccretive :=
    continuous_mat.tendsto g <| F_Φ.eventually_nhds.and <|
      (F₀_an.congr F_eq.symm).eventually_analyticAt.and <|
        eventually_isAccretive_inv_mul (isAccretive_blockDiagPart_inv_mul g).2
  -- `f` is the restriction of `F` to the group.
  let f : SmoothU ε C(maxCompactU ε, ℂ) := ⟨fun y : USign ε ↦ F y, ⟨F, F_smooth⟩, rfl⟩
  have f_eigen :
      ((rightDeriv ε C(_, ℂ)).casimirK 1 f).val g = (l.casimirValue : ℂ) • f.val g := by
    ext k
    refine apply_casimirK_rightDeriv_of_lowest_weight hl f (evalCLM ℂ k) k g fun i j hij ↦ ?_
    filter_upwards [near] with y ⟨hy, y_an, y_acc⟩
    rw [rightDeriv_apply_eq_of_hasFDerivAt (f := f) y_an.differentiableAt.hasFDerivAt fun _ ↦ rfl]
    exact fderiv_flenstedJensen_integrand_single hl k (hy.mono fun x hx ↦ congrFun hx k)
      y_an.differentiableAt y_acc hij
  -- `L` is the normalised integral over `K`; it commutes with right derivatives.
  obtain ⟨L, psi_eq⟩ : ∃ L : C(maxCompactU ε, ℂ) →L[ℂ] ℂ,
      l.dsCoeffSmooth.val =ᶠ[nhds g] L ∘ f.val := by
    refine ⟨l.lowestKType.kTypeNormSq⁻¹ • strongIntegral (haarK ε) (evalCLM ℂ), ?_⟩
    filter_upwards [near] with y ⟨hy, _, y_acc⟩
    simp [f, Φ, strongIntegral_eval, hy.self_of_nhds,
      dsCoeff_eq_flenstedJensen hl (blockDiagPart_mem g), y_acc, flenstedJensen, field]
  -- Right derivatives are local and commute with `L`.
  have h_casimir : ((rightDeriv ε ℂ).casimirK 1 l.dsCoeffSmooth).val g =
      L (((rightDeriv ε C(_, ℂ)).casimirK 1 f).val g) := by
    simp [GlModule.casimir, fun X Y : Matrix n n ℂ ↦ (rightDeriv_comp_clm (X := X) L
      (rightDeriv_comp_clm (X := Y) L psi_eq)).eq_of_nhds]
  rw [h_casimir, f_eigen, map_smul, SetLike.val_smul, Pi.smul_apply, psi_eq.eq_of_nhds,
    Function.comp_apply]

end New
