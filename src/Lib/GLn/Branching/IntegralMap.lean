module

import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
public import Lib.GLn.SchurModule.GramMatrix
import Lib.Base
public import Lib.GLn.SchurModule.SchurMatrix
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.Style
import Lib.General.Analysis.HolomorphicIntegrals

section
/-!
# Branching from GL(n+1) to GL(n) × GL(1): the branching vector and the norm bound

This file treats the branching from `GL(n + 1)` to `GL(n) × GL(1)` for the representations of
`∏ τ, GL (N τ)`. The rows `N τ` are the rows `n τ` together with one new row, given by `ι τ`. A
weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`. This file
defines the branching vector and shows that a hook number times a product of two kernels is the
polynomial of an integral vector, through the multiplication matrix `New.GL.comulMatrix`. It
proves the norm bound for an equivariant matrix from the fact that the matrix times its adjoint
commutes with the smaller group, so is a scalar.

## Main definitions and results

* `New.GL.branchVector`: the product of the leading minors to the powers `γ`, with the new row
  first, so that every column of positive height contains it, and to the powers `κ`, with the new
  row last, so that no column contains it.
* `New.GL.weylNormSq_mulVec_le_of_equivariant`: the norm bound for an equivariant matrix whose
  transpose sends the extremal vector to a multiple of the branching vector.

Notions from other files:
* `New.MatrixPoly`: Polynomials over `R` in an array of variables `X (a, i)`, with rows `a : m` and
  columns `i : ℕ`.
* `New.rankAt`: The number of elements of the finite row type n_τ at the place τ;
  `New.GL.rowEquivFin n τ : n τ ≃ Fin (rankAt n τ)` is the fixed numbering of these rows, and a
  row's position is its number.
* `New.permArray`: For maps e_τ from rows to natural numbers, the array over R whose entry at row
  (τ,a), column i is 1 if e_τ(a)=i and 0 otherwise.
* `New.toPoly`: The linear map from coordinate vectors ξ to polynomials, ξ ↦ Σ_i (Gξ)_i b_i, with G
  the Gram matrix `New.weylGram` (`New.weylGramOver` is its image over another ring) and b_i the
  basis `New.nablaBasis` of products of minors; `New.GL.nablaCombination` is ξ ↦ Σ_i ξ_i b_i.
* `New.weylEval`: For an array y, the evaluation vector `ev_y` with entries b_i(y); its polynomial
  under `New.toPoly` is `New.weylKernel n κ y`.

## Relation to the literature

Known; see `Lib.GLn.Branching.IntegralMap` for sources.
-/

@[expose] public section

noncomputable section

/-!
## The branching vector and integrality of products of minors

A weight `κ` is given by the numbers `κ τ h` of columns of height `h` at the place `τ`.
`New.weylKernel n κ (permArray e)` is the product over `h < rankAt n τ` of the minors on the first
`h` rows in the order `e` and the first `h` columns, to the powers `κ τ h`; `New.rowSubst z f` is
`y ↦ f (z y)`; `New.toPoly n κ` sends a coordinate vector `ξ` to `∑ i, (G ξ) i • b i`, with `G` the
Gram matrix and `b` the basis of minor products.
-/

section BranchingVector

open Finset Matrix

namespace New.GL

variable {Φ : Type} (R : Type) [CommRing R] [Fintype Φ] {n N : Φ → Type}
  [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ}

open scoped Classical in
/-- The numbering of the rows `N τ` by `0, …, rankAt N τ - 1` that gives the added row the number
`i τ` and keeps the rows of `n τ` in their fixed order. -/
def newRowOrder (i : ∀ τ : Φ, Fin (rankAt n τ + 1)) (τ : Φ) : N τ ≃ Fin (rankAt N τ) :=
  -- Insert the new row at position `i τ` into the fixed numbering `rowEquivFin n τ`, then invert.
  finCongr (rankAt_eq_succ ι τ)
    |>.trans (finSuccEquiv' (i τ))
    |>.trans (rowEquivFin n τ).symm.optionCongr
    |>.trans (Equiv.optionEquivSumPUnit (n τ))
    |>.trans (ι τ)
    |>.symm

/-- The product over `τ` and `h < rankAt N τ` of the leading `h × h` minors to the power `γ τ h`
with the added row first, and to the power `κ τ h` with it last. -/
def branchVector (γ κ : Φ → ℕ → ℕ) : MatrixPoly ((τ : Φ) × N τ) R :=
  weylKernel N γ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι 0 τ i : ℕ)) *
    weylKernel (R := R) N κ (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι ⊤ τ i : ℕ))

/-- Multiplying the new row by `s τ` (substituting the matrix `blockScalar ι 1 s`, that is
`diag(1, s τ)` at each `τ`) multiplies `branchVector R ι γ κ'` by the product over `τ` of `s τ` to
the power `diagramWeight (rankAt N) γ (τ, 0)`, the number of columns of `γ` of height
`1, …, rankAt n τ`. -/
lemma rowSubst_branchVector (s : Φ → R) :
    rowSubst (blockScalar ι 1 s) (branchVector R ι γ κ') =
      (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) • branchVector R ι γ κ' := by
  classical
  -- `blockScalar ι 1 s` is diagonal, so it multiplies each kernel by a power of `s`. The new row is
  -- first in the order for `γ`, so it lies in all columns of positive height; it is last in the
  -- order for `κ'`, so it lies in none.
  have h_triangular (e : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ)) (τ : Φ) :
      (blockScalar (R := R) ι 1 s τ)ᵀ.BlockTriangular (e τ) := by
    have h_diagonal : blockScalar (R := R) ι 1 s τ =
        diagonal (Sum.elim (fun _ : n τ ↦ (1 : R)) (fun _ : Unit ↦ s τ) ∘ (ι τ).symm) := by
      rw [blockScalar, Pi.one_apply, ← diagonal_one, fromBlocks_diagonal, reindex_apply,
        submatrix_diagonal_equiv]
    rw [h_diagonal, diagonal_transpose]
    exact blockTriangular_diagonal _
  rw [branchVector, map_mul, rowSubst_weylKernel_permArray _ _ (h_triangular _),
    rowSubst_weylKernel_permArray _ _ (h_triangular _)]
  simp [newRowOrder, blockScalar, rankAt_eq_succ ι, reindex_equiv (ι _), diagramWeight_apply,
    Nat.Ioo_eq_range']

/-! ### The product of the two kernels through the multiplication matrix -/

open scoped Kronecker

variable {R} {κ β α : Φ → ℕ → ℕ}

omit [∀ τ, DecidableEq (n τ)] in
/-- If `β τ h ≤ γ τ h` for every height `h < rankAt n τ`, the kernel of `β` divides the kernel of
`γ` at every array `y`: both are products of the same minors, to the powers `β τ h` and `γ τ h`. -/
lemma weylKernel_dvd_weylKernel (y : ((τ : Φ) × n τ) × ℕ → R)
    (h_le : ∀ τ : Φ, ∀ h < rankAt n τ, β τ h ≤ γ τ h) :
    weylKernel n β y ∣ weylKernel n γ y := by
  simp only [weylKernel, rowSubst_highestPoly]
  exact prod_dvd_prod_of_dvd _ _ fun τ _ ↦ prod_dvd_prod_of_dvd _ _ fun h h_mem ↦
    pow_dvd_pow _ (h_le τ h (mem_range.mp h_mem))

/-- Let the polynomial of the integral vector `ζ` be a multiple of the product of the kernel of `γ`
at the row order `e` and the kernel of `κ'` at the row order `e'`. Then `ζ` is a weight vector:
the matrix `schur κ` of the diagonal matrices with entries `x τ a` multiplies it by the product of
the `x τ a` to the powers `λ_γ(τ, e τ a) + λ_κ'(τ, e' τ a)`, with `λ = New.diagramWeight`. -/
lemma schur_diagonal_mulVec_eq_smul_of_toPoly_eq [DecidableEq Φ]
    (e e' : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) {ζ : WeylIndexFamily n κ → ℤ} {c : ℤ}
    (hζ : toPoly n κ ζ =
      c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (e' τ a : ℕ))))
    (x : ∀ τ : Φ, n τ → ℤ) :
    schur κ (fun τ : Φ ↦ diagonal (x τ)) *ᵥ ζ =
      (∏ τ : Φ, ∏ a : n τ, x τ a ^ (diagramWeight (rankAt n) γ (τ, e τ a) +
        diagramWeight (rankAt n) κ' (τ, e' τ a))) • ζ := by
  -- A diagonal matrix is triangular for every row order, so it scales both kernels.
  have h_triangular (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) (τ : Φ) :
      (diagonal (x τ))ᵀ.BlockTriangular (e τ) := by
    rw [diagonal_transpose]
    exact blockTriangular_diagonal _
  have h_subst : toPoly n κ (schur κ (fun τ : Φ ↦ diagonal (x τ)) *ᵥ ζ) =
      rowSubst (fun τ : Φ ↦ diagonal (x τ)) (toPoly n κ ζ) := by
    simp [toPoly_schur FitsRanks.refl, detPow]
  refine toPoly_injective ?_
  rw [h_subst, map_smul, hζ, map_smul, map_mul,
    rowSubst_weylKernel_permArray _ _ (h_triangular e),
    rowSubst_weylKernel_permArray _ _ (h_triangular e'), smul_mul_smul_comm, smul_comm c]
  simp only [diagonal_apply_eq, pow_add, prod_mul_distrib]

/-- Let `ζ` be an integral weight vector of weight `w` for `κ + κ'`: the matrix `schur (κ + κ')`
of the diagonal matrices with entries `x τ a` multiplies it by the product of the `x τ a ^ w τ a`.
If the multiplication matrix `comulMatrix ℤ n κ κ'` sends `ζ` to a vector with a nonzero entry at
`(i, i')`, the numbers of entries equal to `a` in the fillings `i` and `i'` add up to `w τ a`. -/
lemma tableauWeight_add_eq_of_comulMatrix_mulVec_ne_zero [DecidableEq Φ]
    {ζ : WeylIndexFamily n (κ + κ') → ℤ} {w : ∀ τ : Φ, n τ → ℕ}
    (h_weight : ∀ x : ∀ τ : Φ, n τ → ℤ, schur (κ + κ') (fun τ : Φ ↦ diagonal (x τ)) *ᵥ ζ =
      (∏ τ : Φ, ∏ a : n τ, x τ a ^ w τ a) • ζ)
    {i : WeylIndexFamily n κ} {i' : WeylIndexFamily n κ'}
    (h_ne : (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') ≠ 0) (τ : Φ) (a : n τ) :
    tableauWeight i τ a + tableauWeight i' τ a = w τ a := by
  -- Multiply the row `(τ, a)` by `2` and leave the others: a product of powers of the entries is
  -- then a power of `2`.
  let x (σ : Φ) (b : n σ) : ℤ := if (⟨σ, b⟩ : Σ σ : Φ, n σ) = ⟨τ, a⟩ then 2 else 1
  have h_prod (w : ∀ σ : Φ, n σ → ℕ) : ∏ σ : Φ, ∏ b : n σ, x σ b ^ w σ b = 2 ^ w τ a :=
    calc ∏ σ : Φ, ∏ b : n σ, x σ b ^ w σ b
      _ = ∏ p : Σ σ : Φ, n σ, x p.1 p.2 ^ w p.1 p.2 :=
        (Fintype.prod_sigma fun p : Σ σ : Φ, n σ ↦ x p.1 p.2 ^ w p.1 p.2).symm
      _ = 2 ^ w τ a := by
        have h_other (p : Σ σ : Φ, n σ) (hp : p ≠ ⟨τ, a⟩) : x p.1 p.2 ^ w p.1 p.2 = 1 := by
          simp only [x, ite_eq_right hp, one_pow]
        rw [Fintype.prod_eq_single ⟨τ, a⟩ h_other]
        simp only [x, ite_true]
  -- The entry at `(i, i')` of both sides of the equivariance of the multiplication matrix.
  have h_left : ((schur κ (fun σ : Φ ↦ diagonal (x σ)) ⊗ₖ schur κ' fun σ : Φ ↦ diagonal (x σ)) *ᵥ
        comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') =
      2 ^ (tableauWeight i τ a + tableauWeight i' τ a) * (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') := by
    simp only [schur_diagonal, h_prod, diagonal_kronecker_diagonal, mulVec_diagonal, pow_add]
  have h_right : (comulMatrix ℤ n κ κ' *ᵥ schur (κ + κ') (fun σ : Φ ↦ diagonal (x σ)) *ᵥ ζ)
        (i, i') = 2 ^ w τ a * (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') := by
    rw [h_weight, h_prod, mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have h_eq : (2 : ℤ) ^ (tableauWeight i τ a + tableauWeight i' τ a) *
        (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') =
      2 ^ w τ a * (comulMatrix ℤ n κ κ' *ᵥ ζ) (i, i') := by
    rw [← h_left, ← h_right, mulVec_mulVec, mulVec_mulVec, comulMatrix_equivariant]
  exact pow_right_injective₀ (by norm_num : (0 : ℤ) < 2) (by norm_num) (mul_right_cancel₀ h_ne h_eq)

/-- Let `v` be an integral vector for `κ` whose nonzero coordinates `v i` lie at fillings `i` in
which every row `(τ, a)` occurs at least `λ(τ, e τ a)` times, with `λ = New.diagramWeight`. Then
`v` is a multiple of the evaluation vector `weylEval n κ y` at the permutation array `y` of the row
order `e`, with factor the pairing of `v` with that vector under the matrix `weylGramOver`. -/
lemma eq_smul_weylEval_of_diagramWeight_le [DecidableEq Φ] (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (v : WeylIndexFamily n κ → ℤ)
    (h_wt : ∀ i : WeylIndexFamily n κ, v i ≠ 0 → ∀ (τ : Φ) (a : n τ),
      diagramWeight (rankAt n) κ (τ, e τ a) ≤ tableauWeight i τ a) :
    v = (v ⬝ᵥ weylGramOver *ᵥ weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))) •
      weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) := by
  -- Pairing with the polynomial of `v` under `fockPairing` is a linear form with the values
  -- `hookNumber κ (rankAt n) * v i` on the basis; apply
  -- `map_nablaBasis_eq_map_weylKernel_mul_weylEval` to it and cancel the hook number.
  funext i
  have h_form := map_nablaBasis_eq_map_weylKernel_mul_weylEval e i (fockPairing ℤ (toPoly n κ v))
    fun h_ne τ a ↦ h_wt i (by
      rw [fockPairing_toPoly_nablaBasis] at h_ne
      exact right_ne_zero_of_mul h_ne) τ a
  rw [fockPairing_toPoly_nablaBasis, ← toPoly_weylEval, fockPairing_toPoly_toPoly, mul_assoc]
    at h_form
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hookNumber_pos.ne') h_form

/-- Let the polynomial of the integral vector `ζ` for `β + α` be a multiple of the product of the
kernel of `γ` at the row order `e` and the kernel of `κ'` at the row order `e'`. Suppose that for
every row `(τ, a)` with `λ_β(τ, e τ a) ≠ 0` the sum `λ_β(τ, e τ a) + λ_α(τ, 0)` is at most
`λ_γ(τ, e τ a) + λ_κ'(τ, e' τ a)`, with `λ = New.diagramWeight`. Then the multiplication matrix
`comulMatrix ℤ n β α` sends `ζ` to a pure tensor whose factor for `β` is the evaluation vector at
the permutation array of `e`. -/
lemma exists_comulMatrix_mulVec_eq_vec [DecidableEq Φ] (e e' : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    {ζ : WeylIndexFamily n (β + α) → ℤ} {c : ℤ}
    (hζ : toPoly n (β + α) ζ =
      c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (e' τ a : ℕ))))
    (h_wt : ∀ (τ : Φ) (a : n τ), diagramWeight (rankAt n) β (τ, e τ a) ≠ 0 →
      diagramWeight (rankAt n) β (τ, e τ a) + diagramWeight (rankAt n) α (τ, 0) ≤
        diagramWeight (rankAt n) γ (τ, e τ a) + diagramWeight (rankAt n) κ' (τ, e' τ a)) :
    ∃ a : WeylIndexFamily n α → ℤ, comulMatrix ℤ n β α *ᵥ ζ =
      (vecMulVec a (weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)))).vec := by
  -- For each filling `i'` for `α`, the entries at `(·, i')` form a vector `v i'` for `β`.
  let v (i' : WeylIndexFamily n α) (i : WeylIndexFamily n β) : ℤ :=
    (comulMatrix ℤ n β α *ᵥ ζ) (i, i')
  -- At a nonzero entry the weights of `i` and `i'` add up to the weight of `ζ`, and a row occurs
  -- in `i'` at most `λ_α(τ, 0)` times; so it occurs in `i` at least `λ_β(τ, e τ a)` times.
  have h_low (i' : WeylIndexFamily n α) (i : WeylIndexFamily n β) (h_ne : v i' i ≠ 0) (τ : Φ)
      (a : n τ) : diagramWeight (rankAt n) β (τ, e τ a) ≤ tableauWeight i τ a := by
    obtain h_zero | h_pos := Nat.eq_zero_or_pos (diagramWeight (rankAt n) β (τ, e τ a))
    · rw [h_zero]
      exact Nat.zero_le _
    have h_sum : tableauWeight i τ a + tableauWeight i' τ a =
        diagramWeight (rankAt n) γ (τ, e τ a) + diagramWeight (rankAt n) κ' (τ, e' τ a) :=
      tableauWeight_add_eq_of_comulMatrix_mulVec_ne_zero
        (schur_diagonal_mulVec_eq_smul_of_toPoly_eq e e' hζ) h_ne τ a
    have h_single : tableauWeight i' τ a ≤ diagramWeight (rankAt n) α (τ, 0) := by
      simpa using (sum_tableauWeight_le i' τ {a}).1
    have h_count := h_wt τ a h_pos.ne'
    omega
  refine ⟨fun i' ↦ v i' ⬝ᵥ weylGramOver *ᵥ
    weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)), funext fun ⟨i, i'⟩ ↦ ?_⟩
  exact congrFun (eq_smul_weylEval_of_diagramWeight_le e (v i') (h_low i')) i

/-- Over an infinite domain, if the multiplication matrix `comulMatrix R n κ κ'` sends the vector
`ζ` for `κ + κ'` to the pure tensor of `ξ` and `η`, the polynomial `toPoly n (κ + κ') ζ` is the
product of the polynomials of `ξ` and `η`. -/
lemma toPoly_eq_mul_of_comulMatrix_mulVec_eq [IsDomain R] [Infinite R] [DecidableEq Φ]
    {ζ : WeylIndexFamily n (κ + κ') → R} {ξ : WeylIndexFamily n κ → R}
    {η : WeylIndexFamily n κ' → R}
    (h_tensor : comulMatrix R n κ κ' *ᵥ ζ = (vecMulVec η ξ).vec) :
    toPoly n (κ + κ') ζ = toPoly n κ ξ * toPoly n κ' η := by
  -- The multiplication matrix is an isometry, so its transpose sends `G ξ ⊗ G η` to `G ζ`.
  have h_coord : (vecMulVec (weylGramOver *ᵥ η) (weylGramOver *ᵥ ξ)).vec ᵥ* comulMatrix R n κ κ' =
      weylGramOver *ᵥ ζ :=
    calc (vecMulVec (weylGramOver *ᵥ η) (weylGramOver *ᵥ ξ)).vec ᵥ* comulMatrix R n κ κ'
      _ = (comulMatrix R n κ κ')ᵀ *ᵥ ((weylGram n κ).map (Int.cast : ℤ → R) ⊗ₖ
            (weylGram n κ').map (Int.cast : ℤ → R)) *ᵥ (vecMulVec η ξ).vec := by
        simp only [kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
          mulVec_transpose]
      _ = weylGramOver *ᵥ ζ := by
        rw [← h_tensor, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, comulMatrix_isometry]
  exact (vecMul_comulMatrix_eq_iff.mp h_coord).symm

omit [∀ τ, DecidableEq (n τ)] in
/-- Let `e` be a row order in which every row stands at most one place before its place in
`rowEquivFin`. Let `κ'` have no column of height below `q`, let `β` have none of height `q` or
more and `α` none of a height `h` with `0 < h < q`, and let `β τ h + α τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. For a row `(τ, a)` with `λ_β(τ, e τ a) ≠ 0`, the sum
`λ_β(τ, e τ a) + λ_α(τ, 0)` is at most `λ_γ(τ, e τ a)` plus `λ_κ'` at the place of the row in
`rowEquivFin`, with `λ = New.diagramWeight`. -/
lemma diagramWeight_add_le_of_ne_zero {q : ℕ} (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (he : ∀ (τ : Φ) (a : n τ), (rowEquivFin n τ a : ℕ) ≤ e τ a + 1)
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hβ : ∀ (τ : Φ) (h : ℕ), q ≤ h → β τ h = 0)
    (hα : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), h < q → α τ h = 0)
    (h_sum : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), (β + α) τ h = (κ' + γ) τ h)
    (τ : Φ) (a : n τ) (h_ne : diagramWeight (rankAt n) β (τ, e τ a) ≠ 0) :
    diagramWeight (rankAt n) β (τ, e τ a) + diagramWeight (rankAt n) α (τ, 0) ≤
      diagramWeight (rankAt n) γ (τ, e τ a) +
        diagramWeight (rankAt n) κ' (τ, rowEquivFin n τ a) := by
  simp only [diagramWeight_apply] at h_ne ⊢
  -- Some column of `β` is higher than `e τ a`, so `e τ a + 1 < q`, and the row stands before
  -- the place `q` in `rowEquivFin`.
  obtain ⟨h₀, h₀_mem, h₀_ne⟩ := exists_ne_zero_of_sum_ne_zero h_ne
  have h_lt : (e τ a : ℕ) + 1 < q := by
    by_contra! h_ge
    exact h₀_ne (hβ τ h₀ (h_ge.trans (mem_Ioo.mp h₀_mem).1))
  -- The columns of `α` of positive height are higher than `e τ a`.
  have h_α : ∑ h ∈ Ioo 0 (rankAt n τ), α τ h ≤ ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), α τ h := by
    refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
    refine mem_Ioo.mpr ⟨lt_of_not_ge fun h_le ↦ h_ne (hα τ h h_mem ?_), (mem_Ioo.mp h_mem).2⟩
    omega
  -- So are the columns of `κ'` beyond the place of the row in `rowEquivFin`.
  have h_κ' : ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), κ' τ h ≤
      ∑ h ∈ Ioo (rowEquivFin n τ a : ℕ) (rankAt n τ), κ' τ h := by
    refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
    refine mem_Ioo.mpr ⟨lt_of_not_ge fun h_le ↦ h_ne (hq τ h ?_), (mem_Ioo.mp h_mem).2⟩
    have h_place := he τ a
    omega
  have h_split : ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), β τ h +
        ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), α τ h =
      ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), κ' τ h + ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), γ τ h := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun h h_mem ↦ h_sum τ h (mem_Ioo.mpr ⟨?_, (mem_Ioo.mp h_mem).2⟩)
    exact (Nat.zero_le _).trans_lt (mem_Ioo.mp h_mem).1
  calc ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), β τ h + ∑ h ∈ Ioo 0 (rankAt n τ), α τ h
    _ ≤ ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), β τ h +
        ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), α τ h := Nat.add_le_add_left h_α _
    _ = ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), γ τ h +
        ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), κ' τ h := h_split.trans (add_comm _ _)
    _ ≤ ∑ h ∈ Ioo (e τ a : ℕ) (rankAt n τ), γ τ h +
        ∑ h ∈ Ioo (rowEquivFin n τ a : ℕ) (rankAt n τ), κ' τ h := Nat.add_le_add_left h_κ' _

/-- Let `e` be a row order in which every row stands at most one place before its place in
`rowEquivFin`. Let `κ'` have no column of height below `q`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Then some integer `c` with `0 < c` (a hook number) satisfies two claims.
(a) `c ≤ (L ^ L) ^ 3` for every bound `L` of the number of boxes of `κ₀` in the columns of height
`h` with `q ≤ h < rankAt n τ`. (b) `c` times the kernel of `γ` at the permutation array of `e`,
times the kernel of `κ'` at that of `rowEquivFin`, equals `toPoly n κ₀ η` for some
`η : WeylIndexFamily n κ₀ → ℤ`. -/
lemma exists_smul_weylKernel_mul_weylKernel_eq_toPoly [DecidableEq Φ] {q : ℕ}
    (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (he : ∀ (τ : Φ) (a : n τ), (rowEquivFin n τ a : ℕ) ≤ e τ a + 1)
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ c : ℤ, 0 < c ∧
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧
      ∃ η : WeylIndexFamily n κ₀ → ℤ,
        c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) *
            weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) :
              MatrixPoly (Σ τ : Φ, n τ) ℤ) =
          toPoly n κ₀ η := by
  -- Split `κ₀ = β + α`: `β` holds the columns of `γ` of height below `q`, and `α` the others.
  let β : Φ → ℕ → ℕ := fun τ h ↦ if h ∈ Ioo 0 (min q (rankAt n τ)) then γ τ h else 0
  have hβ_le : β ≤ κ₀ := fun τ h ↦ by
    by_cases h_mem : h ∈ Ioo 0 (min q (rankAt n τ))
    · have h_split := hκ₀ τ h (mem_Ioo.mpr ⟨(mem_Ioo.mp h_mem).1,
        (mem_Ioo.mp h_mem).2.trans_le (min_le_right _ _)⟩)
      simp only [β, ite_eq_left h_mem, h_split, Pi.add_apply, le_add_iff_nonneg_left, zero_le]
    · simp only [β, ite_eq_right h_mem, zero_le]
  obtain ⟨α, rfl⟩ := exists_add_of_le hβ_le
  have hβ (τ : Φ) (h : ℕ) (h_le : q ≤ h) : β τ h = 0 :=
    ite_eq_right fun h_mem ↦ h_le.not_gt ((mem_Ioo.mp h_mem).2.trans_le (min_le_left _ _))
  have hα (τ : Φ) (h : ℕ) (h_mem : h ∈ Ioo 0 (rankAt n τ)) (h_lt : h < q) : α τ h = 0 := by
    have h_split : β τ h + α τ h = κ' τ h + γ τ h := hκ₀ τ h h_mem
    have h_low : β τ h = γ τ h :=
      ite_eq_left (mem_Ioo.mpr ⟨(mem_Ioo.mp h_mem).1, lt_min h_lt (mem_Ioo.mp h_mem).2⟩)
    have h_zero := hq τ h h_lt
    omega
  set K_γ : MatrixPoly (Σ τ : Φ, n τ) ℤ :=
    weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))
  set K_κ' : MatrixPoly (Σ τ : Φ, n τ) ℤ :=
    weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ))
  let K_β : MatrixPoly (Σ τ : Φ, n τ) ℤ :=
    weylKernel n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))
  -- The kernel of `β` divides that of `γ`, and is not zero.
  obtain ⟨F, hF⟩ : K_β ∣ K_γ := weylKernel_dvd_weylKernel _ fun τ h _ ↦ by
    by_cases h_mem : h ∈ Ioo 0 (min q (rankAt n τ))
    · simp only [β, ite_eq_left h_mem, le_refl]
    · simp only [β, ite_eq_right h_mem, zero_le]
  have hK_ne : K_β ≠ 0 := fun h_zero ↦ by
    simpa [K_β, h_zero] using eval_weylKernel_permArray (R := ℤ) (κ := β) e
  -- The product of the kernels has the weight of `β + α`, so the hook number of `β + α` times it
  -- is the polynomial of an integral vector `ζ`.
  have h_weight : diagramWeight (rankAt n) (β + α) =
      diagramWeight (rankAt n) γ + diagramWeight (rankAt n) κ' := by
    ext ⟨τ, i⟩
    rw [Finsupp.add_apply, diagramWeight_apply, diagramWeight_apply, diagramWeight_apply,
      ← sum_add_distrib]
    refine sum_congr rfl fun h h_mem ↦ (hκ₀ τ h (mem_Ioo.mpr ⟨?_, (mem_Ioo.mp h_mem).2⟩)).trans
      (add_comm _ _)
    exact (Nat.zero_le _).trans_lt (mem_Ioo.mp h_mem).1
  have h_mem : K_γ * K_κ' ∈ nablaFamily ℤ n (β + α) := by
    rw [nablaFamily, h_weight]
    exact SetLike.mul_mem_graded (weylKernel_mem_nablaFamily _) (weylKernel_mem_nablaFamily _)
  obtain ⟨ζ, hζ⟩ := exists_toPoly_eq_hookNumber_smul h_mem
  -- The multiplication matrix sends `ζ` to a pure tensor `a ⊗ ev`, with `ev` the evaluation
  -- vector for `β`, whose polynomial is the kernel of `β`. Divide by that kernel.
  obtain ⟨a, ha⟩ := exists_comulMatrix_mulVec_eq_vec e (rowEquivFin n) hζ
    (diagramWeight_add_le_of_ne_zero e he hq hβ hα hκ₀)
  have h_quot : toPoly n α a = hookNumber (β + α) (rankAt n) • (F * K_κ') := by
    have h_eval : toPoly n β (weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))) =
        K_β := toPoly_weylEval _
    refine mul_left_cancel₀ hK_ne ?_
    rw [← h_eval, ← toPoly_eq_mul_of_comulMatrix_mulVec_eq ha, hζ, hF, h_eval, mul_assoc,
      mul_smul_comm]
  -- Pair with the basis for `α`: the hook number of `α` times `a` is the hook number of `β + α`
  -- times an integral vector `a₀`.
  let a₀ : WeylIndexFamily n α → ℤ := fun j ↦ fockPairing ℤ (F * K_κ') (nablaBasis ℤ n α j)
  have h_coeff : hookNumber α (rankAt n) • a = hookNumber (β + α) (rankAt n) • a₀ := by
    funext j
    simpa [a₀, -zsmul_eq_mul] using congrArg (fun P ↦ fockPairing ℤ P (nablaBasis ℤ n α j)) h_quot
  -- An integer left inverse `M` of the multiplication matrix recovers `ζ` from the tensor.
  obtain ⟨M, hM⟩ := hasLeftInv_comulMatrix (n := n) (κ := β) (κ' := α)
  let η : WeylIndexFamily n (β + α) → ℤ := M *ᵥ (vecMulVec a₀
    (weylEval n β (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)))).vec
  have h_η : hookNumber (β + α) (rankAt n) • η = hookNumber α (rankAt n) • ζ := by
    rw [← one_mulVec ζ, ← hM, ← mulVec_mulVec, ha, ← mulVec_smul, ← mulVec_smul, ← vec_smul,
      ← vec_smul, ← smul_vecMulVec, ← smul_vecMulVec, h_coeff]
  refine ⟨hookNumber α (rankAt n), hookNumber_pos, fun L hL ↦ ?_, η, ?_⟩
  · -- A column of `α` of positive height below `q` does not occur.
    have h_boxes (τ : Φ) : ∑ h ∈ range (rankAt n τ), h * α τ h ≤
        ∑ h ∈ Ico q (rankAt n τ), h * (β + α) τ h :=
      calc ∑ h ∈ range (rankAt n τ), h * α τ h
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), h * α τ h := by
          refine sum_le_sum_of_ne_zero fun h h_mem h_ne ↦ ?_
          have h_pos : 0 < h := Nat.pos_of_ne_zero (left_ne_zero_of_mul h_ne)
          have h_rank : h < rankAt n τ := mem_range.mp h_mem
          refine mem_Ico.mpr ⟨le_of_not_gt fun h_lt ↦ right_ne_zero_of_mul h_ne ?_, h_rank⟩
          exact hα τ h (mem_Ioo.mpr ⟨h_pos, h_rank⟩) h_lt
        _ ≤ ∑ h ∈ Ico q (rankAt n τ), h * (β + α) τ h :=
          sum_le_sum fun h _ ↦ Nat.mul_le_mul_left h (Nat.le_add_left _ _)
    exact hookNumber_le ((sum_le_sum fun τ _ ↦ h_boxes τ).trans hL)
  · refine smul_right_injective _ (hookNumber_pos (κ := β + α) (N := rankAt n)).ne' ?_
    change hookNumber (β + α) (rankAt n) • hookNumber α (rankAt n) • (K_γ * K_κ') =
      hookNumber (β + α) (rankAt n) • toPoly n (β + α) η
    rw [← map_smul, h_η, map_smul, hζ, smul_comm]

/-- Let `κ'` have no column of height below `q`, and let `κ₀ τ h = κ' τ h + γ τ h` for
`0 < h < rankAt n τ`. Here `weylKernel n κ y` is the polynomial `f(yᵀx)` in `x`, with `f` the
product of leading minors for `κ`, and `toPoly n κ₀ η` is `Σ_i (Gη)_i b_i` for a Weyl vector `η`
(Gram matrix `G`, basis minor products `b_i`). Then some integer `c` with `0 < c` (a hook number)
satisfies two claims. (a) `c ≤ (L ^ L) ^ 3` for every bound `L` of the number of boxes of `κ₀` in
the columns of height `h` with `q ≤ h < rankAt n τ`. (b) `c` times `weylKernel n γ` at the
permutation array of `rowEquivFin` shifted cyclically by one, times `weylKernel n κ'` at that of
`rowEquivFin`, equals `toPoly n κ₀ η` for some `η : WeylIndexFamily n κ₀ → ℤ`. -/
lemma exists_smul_weylKernel_mul_eq_toPoly [DecidableEq Φ] {q : ℕ}
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = (κ' + γ) τ h) :
    ∃ c : ℤ, 0 < c ∧
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L → c ≤ (L ^ L) ^ 3) ∧
      ∃ η : WeylIndexFamily n κ₀ → ℤ,
        c • (weylKernel n γ (permArray fun (τ : Φ) (a : n τ) ↦
              ((finRotate (rankAt n τ)).symm (rowEquivFin n τ a) : ℕ)) *
            weylKernel n κ' (permArray fun (τ : Φ) (a : n τ) ↦ (rowEquivFin n τ a : ℕ)) :
              MatrixPoly (Σ τ : Φ, n τ) ℤ) =
          toPoly n κ₀ η := by
  -- The cyclic shift moves every row but the first one place back, so
  -- `exists_smul_weylKernel_mul_weylKernel_eq_toPoly` applies to the shifted row order.
  have h_rotate (M : ℕ) (i : Fin M) : (finRotate M i : ℕ) ≤ i + 1 := by
    cases M with
    | zero => exact i.elim0
    | succ M =>
      rw [coe_finRotate]
      split_ifs <;> omega
  refine exists_smul_weylKernel_mul_weylKernel_eq_toPoly
    (fun τ : Φ ↦ (rowEquivFin n τ).trans (finRotate (rankAt n τ)).symm) (fun τ a ↦ ?_) hq hκ₀
  obtain ⟨i, hi⟩ := (finRotate (rankAt n τ)).surjective (rowEquivFin n τ a)
  rw [Equiv.trans_apply, ← hi, Equiv.symm_apply_apply]
  exact h_rotate _ i

end New.GL

end BranchingVector

/-!
## The norm of a branching map

Let `T` be the matrix of a branching map over `ℂ` and `C` its adjoint for the forms of the two
matrices `weylGramOver`. By equivariance `T * C` commutes with every `schur κ₀ g`, so it is a scalar
(`New.mem_range_scalar_of_commute_schur`). This scalar is the squared norm of the image under `C`
of the evaluation vector at the permutation array, and the hypothesis on the top vector bounds it.
The norm bound follows from the inequality `New.GL.posDef_cauchy_schwarz`.
-/

section NormBound

open Matrix ComplexOrder

namespace New.GL

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n N : Φ → Type} [∀ τ : Φ, Fintype (n τ)]
  [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)] [∀ τ : Φ, DecidableEq (N τ)]
  (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ₀ γ κ' : Φ → ℕ → ℕ}

/-- Let `B` be an integral matrix with
`B * schur (γ + κ') (diag(g, 1)) = (∏ τ, det (g τ) ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B)`
for all complex `g`, with `diag(g, 1)` built by `blockScalar ι`. Let `v` be the Gram matrix
`weylGramOver` times `weylEval` at the permutation array of `rowEquivFin`, and assume also that the
row vector `v ᵥ* B` has the polynomial `c • branchVector ℂ ι γ κ'` under `nablaCombination`
(ξ ↦ Σ ξ_i b_i over the basis products of minors). Then
`weylNormSq (B *ᵥ ξ) ≤ c ^ 2 * weylNormSq ξ` for every complex vector `ξ`. -/
lemma weylNormSq_mulVec_le_of_equivariant {c : ℤ}
    {B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ}
    (B_top : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
          B.map (Int.cast : ℤ → ℂ)) =
      (c : ℂ) • branchVector ℂ ι γ κ')
    (B_block : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ,
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ)))
    (ξ : WeylIndexFamily N (γ + κ') → ℂ) :
    weylNormSq (B.map (Int.cast : ℤ → ℂ) *ᵥ ξ) ≤ (c : ℝ) ^ 2 * weylNormSq ξ := by
  -- Let `G₀`, `G` be the two matrices `weylGramOver` and `T` the matrix `B` over `ℂ`. The adjoint
  -- `C` of `T` for their forms is given by `G * C = Tᵀ * G₀`. By equivariance `T * C` commutes with
  -- every `schur κ₀ g`, so it is a scalar `m`. Then `‖C x‖² = m ‖x‖²`, and `m = ‖C v‖² ≤ c ^ 2` for
  -- the evaluation vector `v` of norm 1. The inequality `posDef_cauchy_schwarz` for `ξ` and
  -- `C (T ξ)` gives the bound.
  obtain ⟨T, hT⟩ : ∃ T : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℂ,
      T = B.map (Int.cast : ℤ → ℂ) := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ,
      G₀ = weylGramOver := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Matrix (WeylIndexFamily N (γ + κ')) (WeylIndexFamily N (γ + κ')) ℂ,
      G = weylGramOver := ⟨_, rfl⟩
  simp only [← hT] at B_block ⊢
  rw [← hT, ← hG₀] at B_top
  have hT_real : Tᴴ = Tᵀ := by
    rw [hT]
    ext i j
    simp
  have hG_posDef : G.PosDef := hG ▸ weylGramOver_posDef
  have hG₀_herm : G₀ᴴ = G₀ := by rw [hG₀, weylGramOver_posDef.isHermitian.eq]
  have hG_det : IsUnit G.det := (isUnit_iff_isUnit_det G).1 hG_posDef.isUnit
  have h_coe (x : WeylIndexFamily N (γ + κ') → ℂ) : (weylNormSq x : ℂ) = star x ⬝ᵥ G *ᵥ x := by
    rw [hG, coe_weylNormSq]
  have h_coe₀ (x : WeylIndexFamily n κ₀ → ℂ) : (weylNormSq x : ℂ) = star x ⬝ᵥ G₀ *ᵥ x := by
    rw [hG₀, coe_weylNormSq]
  obtain ⟨C, hGC⟩ : ∃ C : Matrix (WeylIndexFamily N (γ + κ')) (WeylIndexFamily n κ₀) ℂ,
      G * C = Tᵀ * G₀ :=
    ⟨G⁻¹ * (Tᵀ * G₀), mul_nonsing_inv_cancel_left _ _ hG_det⟩
  have hCG : Cᴴ * G = G₀ * T := by
    have h := congrArg conjTranspose hGC
    rwa [← hT_real, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hG_posDef.isHermitian.eq, hG₀_herm] at h
  -- `schur (γ + κ') (diag(g, 1)) * C = det • (C * schur κ₀ g)`: the adjoint of the equivariance.
  have h_adj (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      schur (γ + κ') (blockScalar ι g 1) * C =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g) := by
    have h_tr : (fun τ : Φ ↦ (blockScalar ι g 1 τ)ᵀ) = blockScalar ι (fun τ : Φ ↦ (g τ)ᵀ) 1 := by
      funext τ
      simp [blockScalar, fromBlocks_transpose]
    have h_cancel : G * (schur (γ + κ') (blockScalar ι g 1) * C) =
        G * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) := by
      calc G * (schur (γ + κ') (blockScalar ι g 1) * C)
        _ = (T * schur (γ + κ') (blockScalar ι (fun τ : Φ ↦ (g τ)ᵀ) 1))ᵀ * G₀ := by
          rw [← Matrix.mul_assoc, hG, weylGramOver_mul_schur, ← hG, h_tr, Matrix.mul_assoc, hGC,
            ← Matrix.mul_assoc, transpose_mul]
        _ = (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (Tᵀ * (G₀ * schur κ₀ g)) := by
          rw [B_block, hG₀, weylGramOver_mul_schur]
          simp only [transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_assoc,
            det_transpose]
        _ = G * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) := by
          rw [← Matrix.mul_assoc, ← hGC, Matrix.mul_smul, Matrix.mul_assoc]
    calc schur (γ + κ') (blockScalar ι g 1) * C
      _ = G⁻¹ * (G * (schur (γ + κ') (blockScalar ι g 1) * C)) :=
        (nonsing_inv_mul_cancel_left _ _ hG_det).symm
      _ = (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g) := by
        rw [h_cancel, nonsing_inv_mul_cancel_left _ _ hG_det]
  obtain ⟨m, hm⟩ := mem_range_scalar_of_commute_schur (T := T * C) fun g hg ↦ by
    have h_det : (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ ↦ pow_ne_zero _ (det_ne_zero_of_left_inverse (hg τ))
    have h_left : T * ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (C * schur κ₀ g)) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * T) * C := by
      rw [← h_adj g, ← Matrix.mul_assoc, B_block]
    have h_smul : (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (T * C * schur κ₀ g) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * (T * C)) := by
      rw [Matrix.mul_assoc T C, ← Matrix.mul_smul T, h_left, Matrix.smul_mul, Matrix.mul_assoc]
    exact smul_right_injective _ h_det h_smul
  have hTC : T * C = m • (1 : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ) := by
    rw [← hm, scalar_apply, smul_one_eq_diagonal]
  have h_CGC : Cᴴ * (G * C) = m • G₀ := by
    rw [← Matrix.mul_assoc, hCG, Matrix.mul_assoc, hTC, Matrix.mul_smul, Matrix.mul_one]
  have h_C (x : WeylIndexFamily n κ₀ → ℂ) : (weylNormSq (C *ᵥ x) : ℂ) = m * weylNormSq x := by
    rw [h_coe, h_coe₀, star_mulVec_dotProduct]
    simp only [mulVec_mulVec, h_CGC, smul_mulVec, dotProduct_smul, smul_eq_mul]
  -- The scalar is the squared norm of `C v`, which is at most `c ^ 2`.
  have h_toPoly : toPoly N (γ + κ') (C *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      toPoly N γ ((c : ℂ) • weylEval N γ
          (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι 0 τ i : ℕ))) *
        toPoly N κ' (weylEval N κ'
          (permArray fun (τ : Φ) (i : N τ) ↦ (newRowOrder ι ⊤ τ i : ℕ))) := by
    rw [map_smul, toPoly_weylEval, toPoly_weylEval, ← nablaCombination_weylGramOver_mulVec, ← hG,
      mulVec_mulVec, hGC, ← mulVec_mulVec, mulVec_transpose, B_top, branchVector, smul_mul_assoc]
  have h_m : (m : ℂ) = (weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) : ℝ) := by
    rw [h_C, weylNormSq_weylEval_permArray (rowEquivFin n), Complex.ofReal_one, mul_one]
  have h_m_le : weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ≤ (c : ℝ) ^ 2 := by
    refine (weylNormSq_le_mul_of_toPoly_eq h_toPoly).trans_eq ?_
    rw [weylNormSq_smul, weylNormSq_weylEval_permArray (newRowOrder ι 0),
      weylNormSq_weylEval_permArray (newRowOrder ι ⊤), mul_one, mul_one, Complex.norm_intCast,
      sq_abs]
  -- The pairing of `ξ` and `C (T ξ)` is `‖T ξ‖²`.
  have h_GCT : G * (C * T) = Tᵀ * (G₀ * T) := by
    rw [← Matrix.mul_assoc, hGC, Matrix.mul_assoc]
  have h_pair : star ξ ⬝ᵥ G *ᵥ (C *ᵥ (T *ᵥ ξ)) = (weylNormSq (T *ᵥ ξ) : ℂ) := by
    rw [h_coe₀, star_mulVec_dotProduct, hT_real]
    simp only [mulVec_mulVec, h_GCT]
  have h_norm : weylNormSq (C *ᵥ (T *ᵥ ξ)) = weylNormSq (C *ᵥ weylEval n κ₀
      (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) * weylNormSq (T *ᵥ ξ) := by
    have h := h_C (T *ᵥ ξ)
    rw [h_m] at h
    exact_mod_cast h
  have h_cs : weylNormSq (T *ᵥ ξ) ^ 2 ≤ weylNormSq (C *ᵥ (T *ᵥ ξ)) * weylNormSq ξ := by
    have h := posDef_cauchy_schwarz hG_posDef ξ (C *ᵥ (T *ᵥ ξ))
    rwa [h_pair, ← h_coe, ← h_coe, Complex.ofReal_re, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] at h
  rcases (weylNormSq_nonneg (T *ᵥ ξ)).eq_or_lt with h_zero | h_pos
  · rw [← h_zero]
    exact mul_nonneg (sq_nonneg _) (weylNormSq_nonneg ξ)
  · refine le_trans (le_of_mul_le_mul_right ?_ h_pos)
      (mul_le_mul_of_nonneg_right h_m_le (weylNormSq_nonneg ξ))
    rw [h_norm] at h_cs
    linarith

end New.GL

end NormBound

end
end
end

/-!
# Branching from GL(n+1) to GL(n) × GL(1): integral equivariant branching maps

This file constructs the integral branching map from `GL(n + 1)` to `GL(n) × GL(1)` from its
value at one point, proves its norm bound, and shows that it spans the maps that are equivariant
for the unitary block group. Vectors are coordinates indexed by `New.WeylIndexFamily n κ`
(standard fillings), and `New.schur κ z` is the matrix of `z` in these coordinates. `New.weylRep κ
e` is its twist by `det ^ e` on invertible matrices, `New.weylNormSq` is the squared norm for the
Gram matrix, and `New.GL.blockScalar ι g s` is the matrix `diag(g, s)`.

## Main definitions and results

* `New.SpansBranchingMaps`: a matrix spans the maps that are equivariant for the unitary block
  group.
* `New.GL.exists_int_branching_of_weylKernel`: an integral equivariant matrix from its value at one
  point.
* `New.exists_branching_matrix`: the branching map, its norm bound and its uniqueness.

Notions from other files:
* `New.rankAt`: The number of elements of the finite row type n_τ at the place τ;
  `New.GL.rowEquivFin n τ : n τ ≃ Fin (rankAt n τ)` is the fixed numbering of these rows, and a
  row's position is its number.
* `New.permArray`: For maps e_τ from rows to natural numbers, the array over R whose entry at row
  (τ,a), column i is 1 if e_τ(a)=i and 0 otherwise.
* `New.toPoly`: The linear map from coordinate vectors ξ to polynomials, ξ ↦ Σ_i (Gξ)_i b_i, with G
  the Gram matrix `New.weylGram` (`New.weylGramOver` is its image over another ring) and b_i the
  basis `New.nablaBasis` of products of minors; `New.GL.nablaCombination` is ξ ↦ Σ_i ξ_i b_i.
* `New.weylEval`: For an array y, the evaluation vector `ev_y` with entries b_i(y); its polynomial
  under `New.toPoly` is `New.weylKernel n κ y`.
* `New.GL.branchVector`: the product of the leading minors to the powers `γ` with the new row first
  and to the powers `κ'` with the new row last.

## Relation to the literature

Branching from GL(n+1) to GL(n) with multiplicity one. Here the branching map is given for one
interlacing pair as an integer matrix that is equivariant over every field of characteristic 0 and
satisfies an explicit norm bound, and every unitarily equivariant map is a multiple of it. That it
is non-zero is not part of the statement. Source: Goodman, Wallach 2009, Theorem 8.1.1;
Zhelobenko, Compact Lie Groups and their Representations, 1973, ch. X; Molev, Gelfand-Tsetlin bases
for classical Lie algebras, arXiv math/0211289.
-/

@[expose] public section

noncomputable section

section Branching

open MvPolynomial Finset Fintype Matrix ComplexOrder Norms.L2Operator RingHom

namespace New.GL

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ]
  {n N : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (N τ)]
  [∀ τ : Φ, DecidableEq (N τ)] (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ N τ) {κ κ₀ γ κ' : Φ → ℕ → ℕ}

/-- `New.SpansBranchingMaps ι e₀ e A` says that `A` spans the complex maps that are equivariant for
the unitary points of the block group: let `T` be a complex matrix such that, for every tuple `g`
of unitary matrices (`(g τ)ᴴ * g τ = 1`), some `x` with blocks `x τ = diag(g τ, 1)` along `ι`
satisfies `T * ρ_{κ,e}(x) = ρ_{κ₀,e₀}(g) * T`; then `T` is a multiple of `A`. Here `ρ_{κ,e}` is
`New.weylRep κ e`, the Schur matrix times the powers `e τ` of the determinants, and
`New.GL.blockScalar ι g 1` is the block matrix `diag(g τ, 1)`. -/
def _root_.New.SpansBranchingMaps (e₀ e : Φ → ℤ)
    (A : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N κ) ℂ) : Prop :=
  ∀ T : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N κ) ℂ,
    (∀ g : ∀ τ : Φ, GL (n τ) ℂ, (∀ τ : Φ, (g τ).valᴴ * (g τ).val = 1) →
      ∃ x : (τ : Φ) → GL (N τ) ℂ,
        (∀ τ : Φ, (x τ).val = blockScalar ι (fun τ : Φ ↦ (g τ).val) 1 τ) ∧
        T * weylRep κ e x = weylRep κ₀ e₀ g * T) →
    ∃ a : ℂ, T = a • A

/-- There is a complex vector `v` whose images `schur κ (diag(g, 1)) *ᵥ v`, for `g` ranging over
tuples of lower triangular matrices on the rows `n τ`, span the whole space: a row vector `r`
killing all of them is zero. Here `schur κ` is the Schur matrix, acting on the vectors indexed by
`WeylIndexFamily N κ`, `diag(g, 1)` is `blockScalar ι g 1`, and "lower triangular" is written
`(g τ)ᵀ.BlockTriangular (rowEquivFin n τ)` for the fixed numbering `rowEquivFin n τ` of the rows.

This cyclic vector gives multiplicity at most one in the branching rule from GL (n + 1) to GL n
(`New.GL.spansBranchingMaps_of_equivariant`). -/
lemma exists_cyclic_lower_triangular (κ : Φ → ℕ → ℕ) :
    ∃ v : WeylIndexFamily N κ → ℂ, ∀ r : WeylIndexFamily N κ → ℂ,
      (∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᵀ.BlockTriangular (rowEquivFin n τ)) →
        r ⬝ᵥ schur κ (blockScalar ι g 1) *ᵥ v = 0) →
      r = 0 := by
  -- Let `u` be the identity matrix with new row `(1, …, 1)` and `v` the evaluation vector at the
  -- permutation array `permArray E` of the row order `E` (new row last); the cyclic vector is
  -- `schur κ u *ᵥ v`.
  -- The map `M ↦ (u + M - u * U M) * (1 + U M)` is a submersion at `0`, and the polynomial
  -- function `z ↦ r ⬝ᵥ schur κ z *ᵥ v` vanishes on its image, hence everywhere.
  -- Below, `(1 - u • U) M` is `M - u * U M`.
  let E : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ) := newRowOrder ι ⊤
  let u (τ : Φ) : Matrix (N τ) (N τ) ℂ := of fun a c ↦ if a = ι τ (.inr ()) ∨ a = c then 1 else 0
  let v : WeylIndexFamily N κ → ℂ := weylEval N κ (permArray fun (τ : Φ) (a : N τ) ↦ (E τ a : ℕ))
  -- `U M` is upper triangular for the order `E`, equals `M` above the diagonal, and its column
  -- sums are the new row of `M`.
  let U₀ (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) (τ : Φ) : Matrix (N τ) (N τ) ℂ := of fun a c ↦
    (if E τ a < E τ c then M τ a c else 0) +
      if a = c then M τ (ι τ (.inr ())) c - ∑ d with E τ d < E τ c, M τ d c else 0
  have hU₀_linear : IsLinearMap ℂ U₀ := by
    constructor
    · simp only [Pi.add_apply, Matrix.add_apply, sum_add_distrib, funext_iff, of_add_of,
      EmbeddingLike.apply_eq_iff_eq, U₀]
      intro x y τ a c
      split_ifs <;> ring
    · simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ← mul_sum, funext_iff, smul_of,
      EmbeddingLike.apply_eq_iff_eq, U₀]
      intro c x τ a c'
      split_ifs <;> ring
  let U : (∀ τ : Φ, Matrix (N τ) (N τ) ℂ) →L[ℂ] ∀ τ : Φ, Matrix (N τ) (N τ) ℂ :=
    (hU₀_linear.mk' U₀).toContinuousLinearMap
  refine ⟨schur κ u *ᵥ v, fun r hr ↦ ?_⟩
  -- The new row of `u * U M` is that of `M` and its other rows are those of `U M`; so the first
  -- factor has new row `(1, …, 1)` and zeros above the diagonal in the other rows.
  have h_factor (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) :
      ∃ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᵀ.BlockTriangular (rowEquivFin n τ)) ∧
        u + (1 - u • U) M = blockScalar ι g 1 * u := by
    refine ⟨fun τ ↦ ((1 + M - U M) τ).submatrix (ι τ ∘ .inl) (ι τ ∘ .inl), ?_⟩
    simp only [BlockTriangular, newRowOrder, Pi.top_apply, Fin.top_eq_last, Equiv.optionCongr_symm,
      Equiv.symm_trans, Equiv.symm_symm, finCongr_symm, Equiv.trans_apply, Equiv.optionCongr_apply,
      finCongr_apply, Fin.cast_lt_cast, sum_filter, reindex_equiv (ι _), Equiv.symm_apply_apply,
      sum_sum_type, Equiv.optionEquivSumPUnit_symm_inl, Option.map_some, finSuccEquiv'_symm_some,
      Fin.succAbove_last, univ_unique, PUnit.default_eq_unit, Equiv.optionEquivSumPUnit_symm_inr,
      Option.map_none, finSuccEquiv'_symm_none, sum_singleton, LinearMap.coe_toContinuousLinearMap',
      IsLinearMap.mk'_apply, Pi.sub_apply, Pi.add_apply, Pi.one_apply, transpose_apply,
      submatrix_apply, Function.comp_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, of_apply, Fin.castSucc_lt_castSucc_iff,
      sub_eq_zero, sub_apply, one_apply_eq_self, smul_apply, smul_eq_mul, blockScalar.eq_unfold,
      reindex_apply, diagonal_one, funext_iff, Pi.mul_apply, ← ext_iff, Matrix.mul_apply, ite_mul,
      one_mul, zero_mul, or_self, sum_ite_irrel, sum_add_distrib, sum_const_zero, mul_ite, mul_one,
      mul_zero, reduceCtorEq, false_or, true_or, ↓reduceIte, Sum.forall, add_zero,
      Finset.sum_ite_eq', mem_univ, Fin.castSucc_lt_last, lt_self_iff_false, zero_add,
      Finset.sum_ite_eq, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, sub_self,
      implies_true, and_true, or_false, fromBlocks_apply₂₁, fromBlocks_apply₂₂, add_eq_left,
      add_sub_cancel, U, U₀, E, u]
    refine ⟨fun τ i j hlt ↦ ?_, fun x ↦ ⟨fun a a₁ ↦ (add_sub_assoc _ _ _).symm,
      fun b a ↦ ?_⟩⟩
    · have hne : j ≠ i := fun h ↦ by subst h; exact lt_irrefl _ hlt
      simp only [hne, ↓reduceIte, zero_add, hlt, add_zero]
    · cases b
      ring
  -- The upper triangular second factor only scales `v`.
  have h_eigen (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) : schur κ (fun τ : Φ ↦ 1 + U M τ) *ᵥ v =
      (∏ τ : Φ, ∏ a : N τ, (1 + U M) τ a a ^ diagramWeight (rankAt N) κ (τ, E τ a)) • v := by
    have h_upper (τ : Φ) : (1 + U M τ)ᵀᵀ.BlockTriangular (E τ) := by
      simp only [BlockTriangular, LinearMap.coe_toContinuousLinearMap', IsLinearMap.mk'_apply,
        transpose_add, transpose_one, transpose_of, transpose_apply, Matrix.add_apply,
        Matrix.one_apply, of_apply, U, U₀]
      intro i j hlt
      have hne : j ≠ i := fun h ↦ by subst h; exact lt_irrefl _ hlt
      have hnot : ¬ E τ i < E τ j := not_lt_of_gt hlt
      simp only [Function.swap, hne, hne.symm, hnot, ↓reduceIte, add_zero]
    -- Both sides are coordinates of the kernel at `permArray E`, substituted by `1 + U M`.
    exact toPoly_injective (by simpa [v] using rowSubst_weylKernel_permArray E _ h_upper)
  let P : MvPolynomial ((τ : Φ) × N τ × N τ) ℂ := C ∘ r ⬝ᵥ schur κ (genericMatrixAt ℂ N) *ᵥ C ∘ v
  have hP (z : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) : evalMatrix z P = r ⬝ᵥ schur κ z *ᵥ v := by
    simp [P, Function.comp_def, map_dotProduct, map_mulVec]
  have h_vanish (M : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) :
      evalMatrix ((u + (1 - u • U) M) * (1 + U M)) P = 0 := by
    obtain ⟨g, hg, hM⟩ := h_factor M
    rw [hM, hP]
    simp [Pi.mul_def, hr g hg, schur_mul_left, h_eigen, ← mulVec_mulVec, mulVec_smul]
  have h_zero (z : ∀ τ : Φ, Matrix (N τ) (N τ) ℂ) : r ⬝ᵥ schur κ z *ᵥ v = 0 := by
    rw [← hP]
    refine eq_zero_of_submersion analyticOnNhd_evalMatrix
      (((1 - u • U).hasStrictFDerivAt.const_add u).fun_mul' (U.hasStrictFDerivAt.const_add 1))
      (a := 0) ?_ (.of_forall h_vanish) z
    -- Product rule; as `U 0 = 0`, the derivative at `0` is `u * U M + (M - u * U M) = M`.
    simp [Module.End.one_eq_id]
  -- The vectors `schur κ g *ᵥ v` span (`ext_schur_weylEval`), and `r` is orthogonal to all of them.
  refine (dotProductEquiv ℂ (WeylIndexFamily N κ)).injective (ext_schur_weylEval E fun g ↦ ?_)
  simpa [v] using h_zero fun τ : Φ ↦ (g τ).val

/-- The kernel of the branching map: for arrays `x` (rows `n`) and `y` (rows `N`) over a commutative
ring `S`, the value of `branchVector S ι γ κ'` at `diag(xᵀ, 1) y`, where `xᵀ` is the transposed
square part of `x` in the row order `rowEquivFin`. -/
private def branchKernel (γ κ' : Φ → ℕ → ℕ) {S : Type} [CommRing S] (x : Sigma n × ℕ → S)
    (y : Sigma N × ℕ → S) : S :=
  eval y (rowSubst (blockScalar ι (fun τ : Φ ↦ (squarePart (rowEquivFin n) x τ)ᵀ) 1)
    (branchVector S ι γ κ'))

variable (n) in
/-- The linear map `θ ↦ toPoly n κ₀ θ * detPow S n d` with `d τ = κ' τ (rankAt n τ)`: the
polynomial of the coordinate vector `θ` times the powers `d τ` of the determinants. -/
private def detPowToPoly (κ₀ κ' : Φ → ℕ → ℕ) (S : Type) [CommRing S] :
    (WeylIndexFamily n κ₀ → S) →ₗ[S] MatrixPoly (Sigma n) S :=
  .mulRight S (detPow S n fun τ : Φ ↦ κ' τ (rankAt n τ)) ∘ₗ toPoly n κ₀

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (N τ)] [∀ τ : Φ, DecidableEq (n τ)] in
/-- A ring homomorphism `φ` commutes with `branchKernel`: it sends the kernel at `x` and `y` to
the kernel at `φ ∘ x` and `φ ∘ y`. -/
private lemma map_branchKernel {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : Sigma n × ℕ → S) (y : Sigma N × ℕ → S) :
    φ (branchKernel ι γ κ' x y) =
      branchKernel ι γ κ' (fun p : Sigma n × ℕ ↦ φ (x p)) fun p : Sigma N × ℕ ↦ φ (y p) := by
  simp only [branchKernel, blockScalar.eq_unfold, reindex_apply, squarePart, transpose_of,
    Pi.one_apply, diagonal_one, branchVector, weylKernel, permArray, map_mul, eval_rowSubst,
    submatrix_apply, reindex_equiv (ι _), Equiv.symm_apply_apply, sum_sum_type, univ_unique,
    PUnit.default_eq_unit, sum_singleton, of_apply, ite_mul, one_mul, zero_mul, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Matrix.zero_apply, add_zero, fromBlocks_apply₂₁, sum_const_zero,
    fromBlocks_apply₂₂, one_apply_eq, zero_add, apply_ite, map_eval, Function.comp_def, map_add,
    map_sum, map_zero, map_highestPoly]

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (N τ)] [∀ τ : Φ, DecidableEq (n τ)] in
/-- In `y`, `branchKernel` is a semi-invariant of the upper triangular group: replacing `y` by
`borelMul Sigma.fst b y` multiplies it by the diagonal entries of `b` to the powers given by the
weights of `γ` and `κ'`. -/
private lemma branchKernel_borelMul {S : Type} [CommRing S] (b : Φ × ℕ × ℕ → S)
    (x : Sigma n × ℕ → S) (y : Sigma N × ℕ → S) :
    branchKernel ι γ κ' x (borelMul Sigma.fst b y) =
      ((diagramWeight (rankAt N) γ + diagramWeight (rankAt N) κ').prod
        fun (p : Φ × ℕ) (k : ℕ) ↦ b (p.1, p.2, p.2) ^ k) * branchKernel ι γ κ' x y := by
  -- `branchVector` is a product of two kernels, each a semi-invariant; so is its substitution.
  have h_mem : branchVector S ι γ κ' ∈
      nabla S Sigma.fst (diagramWeight (rankAt N) γ + diagramWeight (rankAt N) κ') :=
    SetLike.mul_mem_graded (weylKernel_mem_nablaFamily _) (weylKernel_mem_nablaFamily _)
  simpa only [aeval_eq_eval, branchKernel] using mem_nabla.mp (rowSubst_mem_nabla _ h_mem) S b y

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (N τ)] in
/-- Let `y'` be the array `diag(g, s) y` and `x'` the array `gᵀ x`. The kernel at `x` and `y'` is
the kernel at `x'` and `y` times the product of the powers
`s τ ^ diagramWeight (rankAt N) γ (τ, 0)`. -/
private lemma branchKernel_blockScalar {S : Type} [CommRing S] (g : ∀ τ : Φ, Matrix (n τ) (n τ) S)
    (s : Φ → S) (x : Sigma n × ℕ → S) (y : Sigma N × ℕ → S) :
    branchKernel ι γ κ' x (fun p : Sigma N × ℕ ↦
        ∑ a : N p.1.fst, blockScalar ι g s p.1.fst p.1.snd a * y (⟨p.1.fst, a⟩, p.2)) =
      (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0)) *
        branchKernel ι γ κ' (fun p : Sigma n × ℕ ↦
          ∑ a : n p.1.fst, (g p.1.fst)ᵀ p.1.snd a * x (⟨p.1.fst, a⟩, p.2)) y := by
  -- With `a` the transposed square part of `x`, that of `gᵀ x` is `a g`. Now
  -- `diag(a, 1) diag(g, s) = diag(1, s) diag(a g, 1)`, and `diag(1, s)` scales `branchVector`.
  let a (τ : Φ) : Matrix (n τ) (n τ) S := (squarePart (rowEquivFin n) x τ)ᵀ
  have h_square : (fun τ : Φ ↦ (squarePart (rowEquivFin n) (fun p : Sigma n × ℕ ↦
      ∑ b : n p.1.fst, (g p.1.fst)ᵀ p.1.snd b * x (⟨p.1.fst, b⟩, p.2)) τ)ᵀ) =
        fun τ : Φ ↦ a τ * g τ := by
    ext τ i j
    simp [a, squarePart, Matrix.mul_apply, mul_comm]
  have h_block : (fun τ : Φ ↦ blockScalar ι a 1 τ * blockScalar ι g s τ) =
      fun τ : Φ ↦ blockScalar ι 1 s τ * blockScalar ι (fun σ : Φ ↦ a σ * g σ) 1 τ := by
    funext τ
    simp [blockScalar, fromBlocks_multiply]
  rw [branchKernel, branchKernel, h_square, ← eval_rowSubst, rowSubst_rowSubst, h_block,
    ← rowSubst_rowSubst, rowSubst_branchVector, map_smul, smul_eval]

/-- Up to the factor `∏ τ, det (g τ) ^ κ' τ (rankAt n τ)`, the Schur matrix of `g` acts on
`detPowToPoly n κ₀ κ' S θ` as the substitution `x ↦ gᵀ x`. -/
private lemma detPowToPoly_smul_schur_mulVec {S : Type} [CommRing S] [IsDomain S] [CharZero S]
    (g : ∀ τ : Φ, Matrix (n τ) (n τ) S) (θ : WeylIndexFamily n κ₀ → S) :
    detPowToPoly n κ₀ κ' S ((∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • schur κ₀ g *ᵥ θ) =
      rowSubst (fun τ : Φ ↦ (g τ)ᵀ) (detPowToPoly n κ₀ κ' S θ) := by
  -- By `toPoly_schur` the Schur matrix becomes the substitution (with no power of `det`, as the
  -- ranks agree), and by `rowSubst_detPow` the substitution scales `detPow` by
  -- `∏ τ, det (g τ) ^ κ' τ (rankAt n τ)`.
  simp [detPowToPoly, toPoly_schur, rowSubst_detPow, det_transpose]

omit [∀ τ : Φ, DecidableEq (N τ)] in
/-- Let `c` times the product of the two kernels in `hη` be `toPoly n κ₀ η`, and let `y` have new
row `(t, 0, 0, …)` and block `g` on the rows `n τ`. Expanding the minors along the new row,
`branchKernel ι γ κ' x y` is a power of `t` times the product of those two kernels and of
`det ^ d`, with `d τ = κ' τ (rankAt n τ)`, all at `gᵀ x`. So `c` times it is `detPowToPoly` of
a coordinate vector: `η` moved by `g` and scaled. -/
private lemma exists_eval_detPowToPoly_eq_mul_branchKernel {c : ℤ} {η : WeylIndexFamily n κ₀ → ℤ}
    (hη : c • (weylKernel n (fun (τ : Φ) (h : ℕ) ↦ γ τ (h + 1)) (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (Fintype.card (n τ))).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      toPoly n κ₀ η)
    (y : Sigma N × ℕ → MatrixPoly (Sigma N) ℤ)
    (hy : ∀ (τ : Φ) (j : ℕ), y (⟨τ, ι τ (.inr ())⟩, j + 1) = 0) :
    ∃ θ : WeylIndexFamily n κ₀ → MatrixPoly (Sigma N) ℤ, ∀ x : Sigma n × ℕ → MatrixPoly (Sigma N) ℤ,
      eval x (detPowToPoly n κ₀ κ' (MatrixPoly (Sigma N) ℤ) θ) = c * branchKernel ι γ κ' x y := by
  let g (τ : Φ) : Matrix (n τ) (n τ) (MatrixPoly (Sigma N) ℤ) :=
    of fun a b ↦ y (⟨τ, ι τ (.inl a)⟩, rowEquivFin n τ b)
  refine ⟨(∏ τ, ∏ h ∈ range (rankAt n τ), y (⟨τ, ι τ (.inr ())⟩, 0) ^ γ τ (h + 1)) •
    (∏ τ, (g τ).det ^ κ' τ (rankAt n τ)) • schur κ₀ g *ᵥ C ∘ η, fun x ↦ ?_⟩
  rw [map_smul, detPowToPoly_smul_schur_mulVec, detPowToPoly, LinearMap.comp_apply]
  -- Expand both sides into minors. The flags `↓←` and `-finRotate_symm_apply` keep `toPoly` and
  -- `finRotate.symm` in the form that `hη` has, for `← hη`.
  simp only [transpose_of, detPow, minor, ↓← map_toPoly, ← hη, weylKernel, rowSubst_highestPoly,
    zsmul_eq_mul, map_mul, map_intCast, map_prod, map_pow, map_det, mapMatrix_apply, Matrix.map,
    of_apply, map_sum, map_X, LinearMap.mulRight_apply, mul_assoc, smul_eval, eval_rowSubst,
    mul_comm _ (x _), eval_X, branchKernel, blockScalar.eq_unfold, reindex_apply, squarePart,
    Pi.one_apply, diagonal_one, branchVector, rankAt_eq_succ ι, prod_range_succ' (_ ^ γ _ ·),
    det_fin_zero, one_pow, mul_one, prod_range_succ, prod_mul_distrib, submatrix_apply, g]
  simp only [permArray, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    newRowOrder, Pi.zero_apply, Equiv.optionCongr_symm, Equiv.symm_trans, Equiv.symm_symm,
    finCongr_symm, Equiv.trans_apply, Equiv.optionCongr_apply, finCongr_apply, Fin.val_cast,
    reindex_equiv (ι _), Equiv.symm_apply_apply, sum_sum_type, univ_unique, PUnit.default_eq_unit,
    sum_singleton, Equiv.optionEquivSumPUnit_symm_inl, Option.map_some, finSuccEquiv'_symm_some,
    Fin.zero_succAbove, Fin.val_succ, fromBlocks_apply₁₁, of_apply, fromBlocks_apply₁₂,
    Matrix.zero_apply, add_zero, Equiv.optionEquivSumPUnit_symm_inr, Option.map_none,
    finSuccEquiv'_symm_none, Fin.coe_ofNat_eq_mod, Nat.zero_mod, fromBlocks_apply₂₁, sum_const_zero,
    fromBlocks_apply₂₂, one_apply_eq, zero_add, sum_ite_irrel, det_succ_row_zero,
    Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, submatrix,
    Nat.add_right_cancel_iff, Nat.right_eq_add, mul_assoc, Fin.sum_univ_succ, pow_zero, hy,
    mul_zero, mul_pow, prod_mul_distrib, Pi.top_apply, Fin.top_eq_last, Fin.succAbove_last,
    Fin.val_castSucc, Fin.val_last]
  rw [mul_left_comm]
  -- The minors on both sides agree up to transposition and the numbering of the rows: `congr!`
  -- pairs the factors, and each pair is closed by the same call. The hypotheses are cleared because
  -- `grind` below would also read them.
  clear g hη hy
  conv_rhs => simp +singlePass [← det_transpose, -finRotate_symm_apply]
  congr! <;> simp +instances (disch := grind) [ite_eq_right, ← Fin.eq_mk_iff_val_eq,
    Nat.mod_eq_of_lt, Fin.add_def, -finRotate_symm_apply, ← Equiv.eq_symm_apply,
    Function.swap]

/-- Let `c • (weylKernel n γ₁ P₁ * weylKernel n κ' P) = toPoly n κ₀ η` for an integer `c` and an
integer vector `η`, where `γ₁ τ h = γ τ (h + 1)`, `P` is the permutation array of the row order
`rowEquivFin` and `P₁` that of `rowEquivFin` shifted cyclically by one. (`New.weylKernel` is the
product of the leading minors to the powers given by the weight; `New.toPoly n κ₀` sends a
coordinate vector to its polynomial.) Then there is an integral matrix `B` with two properties. (a)
Applied on the right to `weylGramOver *ᵥ weylEval n κ₀ P`, the coordinates of `weylKernel n κ₀ P`,
it gives a vector ξ whose polynomial `nablaCombination (γ + κ')` ξ = Σ ξ_i b_i (b_i the basis minor
products) is `c • branchVector ℂ ι γ κ'`; the latter is the product of leading h×h minors to the
powers γ τ h with the added row first and κ' τ h with it last. (b) Over every field of
characteristic zero, `B * schur (γ + κ') (diag(g, s)) = χ • (schur κ₀ g * B)` with `χ = ∏ τ, s τ ^
diagramWeight (rankAt N) γ (τ, 0) * det (g τ) ^ κ' τ (rankAt n τ)`. Here `schur` is the Schur matrix
on the Weyl module and `diag(g, s)` is `blockScalar ι g s`. -/
lemma exists_int_branching_of_weylKernel {c : ℤ} {η : WeylIndexFamily n κ₀ → ℤ}
    (hη : c • (weylKernel n (fun (τ : Φ) (h : ℕ) ↦ γ τ (h + 1)) (permArray fun (τ : Φ) (a : n τ) ↦
          ((finRotate (Fintype.card (n τ))).symm (rowEquivFin n τ a) : ℕ)) *
        weylKernel n κ' (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      toPoly n κ₀ η) :
    ∃ B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ,
      -- (a)
      nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
          (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
            B.map (Int.cast : ℤ → ℂ)) =
        (c : ℂ) • branchVector ℂ ι γ κ' ∧
      -- (b)
      ∀ (R : Type) [Field R] [CharZero R] (g : (τ : Φ) → Matrix (n τ) (n τ) R) (s : Φ → R),
        B.map (Int.cast : ℤ → R) * schur (γ + κ') (blockScalar ι g s) =
          (∏ τ : Φ, s τ ^ diagramWeight (rankAt N) γ (τ, 0) * (g τ).det ^ κ' τ (rankAt n τ)) •
            (schur κ₀ g * B.map (Int.cast : ℤ → R)) := by
  -- Say that `θ` represents `m` times the kernel at `y` if `detPowToPoly n κ₀ κ' S θ` has the
  -- values `m * branchKernel ι γ κ' x y`. We move `η` to the generic point, read off `B` from the
  -- coefficients of the kernel, and get both claims from one fact: `B ev_y` represents `c` times
  -- the kernel at `y`.
  -- Column operations on the generic point `X`, with `X₀ τ` and `X_j τ` its entries in the new row
  -- and columns `0` and `j`: column `0` is multiplied by `X₀ τ`, and column `j > 0` becomes
  -- `X₀ τ * column j - X_j τ * column 0`. They clear the new row beyond its first entry and
  -- multiply the kernel by a monomial `y ^ μ`.
  let β : Φ × ℕ × ℕ → MatrixPoly (Sigma N) ℤ := fun (τ, i, j) ↦
    (if i = j then 1 else if i = 0 then -1 else 0) * X (⟨τ, ι τ (.inr ())⟩, j - i)
  have h_new_row (τ : Φ) (j : ℕ) : borelMul Sigma.fst β X (⟨τ, ι τ (.inr ())⟩, j + 1) = 0 := by
    simp only [borelMul, ite_mul, one_mul, neg_mul, zero_mul, mul_ite, mul_neg, mul_comm,
      sum_range_succ', Nat.add_right_cancel_iff, Nat.reduceSubDiff, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_range,
      lt_add_iff_pos_right, Order.lt_one_iff, tsub_self, Nat.right_eq_add, tsub_zero,
      add_neg_cancel, β]
  obtain ⟨θ, μ, hθ⟩ : ∃ (θ : WeylIndexFamily n κ₀ → MatrixPoly (Sigma N) ℤ) (μ : Sigma N × ℕ →₀ ℕ),
      ∀ x : Sigma n × ℕ → MatrixPoly (Sigma N) ℤ,
        eval x (detPowToPoly n κ₀ κ' (MatrixPoly (Sigma N) ℤ) θ) =
          monomial μ 1 * (branchKernel ι γ κ' x X * (c : MatrixPoly (Sigma N) ℤ)) := by
    obtain ⟨θ, hθ⟩ := exists_eval_detPowToPoly_eq_mul_branchKernel ι hη _ h_new_row
    -- `μ` is the exponent of the monomial that `branchKernel_borelMul` gives for `β`; it is found
    -- by unification in the `simpa`, so it is left as a hole.
    exact ⟨θ, _, by simpa only [ite_mul, one_mul, neg_mul, zero_mul, branchKernel_borelMul,
      Finsupp.prod, ↓reduceIte, tsub_self, Finsupp.coe_add, Pi.add_apply, X_pow_eq_monomial,
      Finsupp.single_add, ← monomial_sum_one, sum_add_distrib, Int.cast_comm, mul_assoc,
      β] using hθ⟩
  -- `c` times the kernel at generic `x` and `y` is a polynomial in `y` over `ℤ[x]`. As a
  -- semi-invariant it is a combination of the basis `nablaBasis`, with coordinates `f`. The weight
  -- is written with the zero sum that `nabla_le_span_nablaBasis_mul_detPow 0` expects.
  have h_semi : c • branchKernel ι γ κ' (C ∘ (X : Sigma n × ℕ → MatrixPoly (Sigma n) ℤ)) X ∈
      nabla (MatrixPoly (Sigma n) ℤ) Sigma.fst (diagramWeight (rankAt N) (γ + κ') +
        ∑ τ : Φ, (0 : Φ → ℕ) τ • ∑ i ∈ range (rankAt N τ), Finsupp.single (τ, i) 1) := by
    simp only [diagramWeight_add, Pi.zero_apply, zero_nsmul, sum_const_zero, add_zero, zsmul_eq_mul,
      mem_nabla, aeval_def, eval₂_mul, ← coe_eval₂Hom, map_intCast, map_branchKernel,
      Function.comp_apply, eval₂Hom_C, eval₂Hom_X', branchKernel_borelMul, mul_left_comm,
      implies_true]
  obtain ⟨f, hf⟩ := LinearMap.mem_range.mp (nabla_le_span_nablaBasis_mul_detPow 0 h_semi)
  -- Compare the coefficients of `y ^ (μ + δ)` in `hθ`: the coefficient of `y ^ δ` in that
  -- polynomial lies in the range of `detPowToPoly n κ₀ κ' ℤ`. By `coord_mem_of_coeff_mem` so do the
  -- coordinates `f j`; their preimages `B j` are the columns of the matrix.
  have h_coeff (δ : Sigma N × ℕ →₀ ℕ) :
      (c • branchKernel ι γ κ' (C ∘ (X : Sigma n × ℕ → MatrixPoly (Sigma n) ℤ)) X).coeff δ ∈
        (detPowToPoly n κ₀ κ' ℤ).range.toAddSubgroup := by
    refine ⟨fun i ↦ (θ i).coeff (μ + δ), MvPolynomial.funext fun x ↦ ?_⟩
    have h_shift : (eval (C ∘ x) (detPowToPoly n κ₀ κ' (MatrixPoly (Sigma N) ℤ) θ)).coeff (μ + δ) =
        (branchKernel ι γ κ' (fun p : Sigma n × ℕ ↦ (x p : MatrixPoly (Sigma N) ℤ)) X *
          (c : MatrixPoly (Sigma N) ℤ)).coeff δ := by
      rw [hθ, coeff_monomial_mul, one_mul]
      -- On `ℤ` the map `C` is the cast by definition.
      rfl
    simpa only [detPowToPoly, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      map_mul, eval_toPoly, dotProduct, weylEval, mulVec, map_apply, Int.cast_eq,
      mul_comm (eval x _), AddMonoidAlgebra.coeff_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eval,
      ← coeff_map, map_branchKernel, map_C, eval_X, eq_intCast, map_X, ← map_detPow C,
      ← map_nablaBasis C, eval_map, ← eval₂_comp, ← zsmul_eq_mul, ← Int.cast_comm,
      AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply, Int.zsmul_eq_mul]
      using h_shift
  have h_coord : ∀ j : WeylIndexFamily N (γ + κ'), ∃ b : WeylIndexFamily n κ₀ → ℤ,
      detPowToPoly n κ₀ κ' ℤ b = f j :=
    coord_mem_of_coeff_mem _ _ hf h_coeff
  choose B hB using h_coord
  -- Specialise `hf` at points `x` and `y` over any ring.
  have hB_kernel {T : Type} [CommRing T] (y : Sigma N × ℕ → T) (x : Sigma n × ℕ → T) :
      eval x (detPowToPoly n κ₀ κ' T ((of B)ᵀ.map (↑) *ᵥ weylEval N (γ + κ') y)) =
        c * branchKernel ι γ κ' x y := by
    simpa only [detPowToPoly, transpose_of, mulVec_eq_sum, weylEval, op_smul_eq_smul, map_sum,
      map_smul, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, smul_eq_C_mul,
      map_mul, eval_C, eval_toPoly, dotProduct, transpose_apply, map_apply, of_apply,
      MulOpposite.op_intCast, Finset.sum_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_intCast, mul_comm (eval y _), AlgHom.toRingHom_eq_coe, detPow_zero, mul_one,
      linearCombination_apply, ← hB, C_mul, ← eval_map, map_C, coe_coe, aeval_def,
      algebraMap_int_eq, map_toPoly, Int.coe_castRingHom, map_intCast, map_detPow, map_nablaBasis,
      zsmul_eq_mul, map_branchKernel, map_X, eval_X] using congrArg (eval₂ (aeval x).toRingHom y) hf
  refine ⟨(of B)ᵀ, MvPolynomial.funext fun y ↦ ?_, ?_⟩
  · -- For `x` the identity matrix, `det x = 1` and the kernel is `branchVector` evaluated at `y`.
    simpa only [transpose_of, map.eq_1 (of _), of_apply, vecMul_mulVec, ← transpose_map,
      weylGram_isSymm.eq, linearCombination_apply, map_sum, smul_eval, ← weylEval.eq_1,
      ← dotProduct.eq_1, detPowToPoly, detPow, minor, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, map_mul, eval_toPoly, mulVec_mulVec, dotProduct_mulVec, map_prod,
      map_pow, map_det, mapMatrix_apply, eval_X, permArray, Equiv.apply_symm_apply, Fin.val_inj,
      ← diagonal.eq_1, diagonal_one, det_one, one_pow, prod_const_one, mul_one, branchKernel,
      blockScalar.eq_unfold, reindex_apply, squarePart, EmbeddingLike.apply_eq_iff_eq,
      transpose_one, Pi.one_apply, fromBlocks_one, submatrix_one_equiv, rowSubst_one]
      using hB_kernel y (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))
  intro S _ _ g s
  -- It suffices to compare the two sides on the vectors `ev_y`, and there after applying
  -- `detPowToPoly n κ₀ κ' S`, which is injective because the product of the powers
  -- `det ^ κ' τ (rankAt n τ)` is not a zero divisor.
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  refine toPoly_injective
    ((isRegular_detPow (R := S) (n := n) (e := fun τ : Φ ↦ κ' τ (rankAt n τ))).right ?_)
  change detPowToPoly n κ₀ κ' S _ = detPowToPoly n κ₀ κ' S _
  refine MvPolynomial.funext fun x ↦ ?_
  -- By `hB_kernel` the left side is `c` times the kernel at `x` and `diag(g, s) y`, and the right
  -- side is a power of `s` times `c` times the kernel at `gᵀ x` and `y`.
  simp only [toLin'_mul, LinearMap.coe_comp, Function.comp_apply, toLin'_apply, FitsRanks.refl,
    schurDetExp_self, schur_mulVec_weylEval_of_schurDetExp_eq_zero, hB_kernel,
    branchKernel_blockScalar ι g s x y, transpose_apply, prod_mul_distrib, mul_smul, map_smul,
    LinearMap.smul_apply, detPowToPoly_smul_schur_mulVec g, smul_eval, eval_rowSubst,
    mul_left_comm]

/-- Let `v` be the Gram matrix `weylGramOver` times the evaluation vector at the permutation array
of `rowEquivFin`. Let `B` be an integral matrix such that `nablaCombination` (ξ ↦ Σ ξ_i b_i over the
basis products of minors) sends the row vector `v ᵥ* B` to `c • branchVector ℂ ι γ κ'` with `c ≠ 0`.
Here `branchVector` is the product of the leading minors to the powers `γ`, with the added row
first, and of those to the powers `κ'`, with the added row last. Let `B` also be equivariant over
`ℂ`: `B * schur (γ + κ') (diag(g, 1)) = (∏ τ, det (g τ) ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B)`
for all `g`, where `diag(g, 1)` is `blockScalar ι g 1`. If `e₀ τ = e τ + κ' τ (rankAt n τ)`, then
every complex matrix intertwining weights `(γ + κ', e)` and `(κ₀, e₀)` on the unitary points of the
block group is a multiple of `B` (`New.SpansBranchingMaps`). -/
lemma spansBranchingMaps_of_equivariant {c : ℤ} (hc : c ≠ 0) {e e₀ : Φ → ℤ}
    (he₀ : ∀ τ : Φ, e₀ τ = e τ + κ' τ (rankAt n τ))
    {B : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℤ}
    (B_top : nablaCombination (γ + κ') ((weylGramOver *ᵥ weylEval n κ₀
        (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) ᵥ*
          B.map (Int.cast : ℤ → ℂ)) =
      (c : ℂ) • branchVector ℂ ι γ κ')
    (B_block : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ,
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ))) :
    SpansBranchingMaps ι e₀ e (B.map (Int.cast : ℤ → ℂ)) := by
  -- `D g T` is the defect of equivariance of `T` at `g`. An equivariant `T` is determined by the
  -- number `x ᵥ* T ⬝ᵥ v`, with `x` the coordinates of `weylKernel n κ₀ (permArray (rowEquivFin n))`
  -- in the basis `nablaBasis` and `v` the cyclic vector.
  intro T hT
  set G₀ : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily n κ₀) ℂ := weylGramOver
  set x : WeylIndexFamily n κ₀ → ℂ :=
    G₀ *ᵥ weylEval n κ₀ (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))
  let d (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) : ℂ := ∏ τ, (g τ).det ^ κ' τ (rankAt n τ)
  obtain ⟨v, v_cyclic⟩ : ∃ v : WeylIndexFamily N (γ + κ') → ℂ, ∀ r : WeylIndexFamily N (γ + κ') → ℂ,
      (∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᵀ.BlockTriangular (rowEquivFin n τ)) →
        r ⬝ᵥ schur (γ + κ') (blockScalar ι g 1) *ᵥ v = 0) →
      r = 0 :=
    exists_cyclic_lower_triangular ι (γ + κ')
  let D {R : Type} [CommRing R] (g : (τ : Φ) → Matrix (n τ) (n τ) R) :
      Module.End R (Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) R) :=
    mulRightLinearMap _ R (schur (γ + κ') (blockScalar (R := R) ι g 1)) -
      (∏ τ, (g τ).det ^ κ' τ (rankAt n τ)) • mulLeftLinearMap _ R (schur κ₀ g)
  have eq_zero (T' : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N (γ + κ')) ℂ)
      (hT' : ∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ, D g T' = 0) (h_value_zero : x ᵥ* T' ⬝ᵥ v = 0) :
      T' = 0 := by
    have h_row (g : (τ : Φ) → Matrix (n τ) (n τ) ℂ) :
        x ᵥ* T' ᵥ* schur (γ + κ') (blockScalar ι g 1) = d g • x ᵥ* schur κ₀ g ᵥ* T' := by
      simpa only [D, d, vecMul_vecMul, Pi.add_apply, LinearMap.sub_apply, mulRightLinearMap_apply,
        LinearMap.smul_apply, mulLeftLinearMap_apply, vecMul_sub, vecMul_smul, vecMul_zero,
        sub_eq_zero] using congrArg (x ᵥ* ·) (hT' g)
    -- `x` is an eigenvector of the lower triangular group, under which `v` is cyclic.
    have x_mul_T : x ᵥ* T' = 0 := by
      refine v_cyclic _ fun g hg ↦ ?_
      -- The eigenvalue is the scalar of `rowSubst_weylKernel_permArray`; it is found by
      -- unification, so it is left as a hole.
      obtain ⟨a, ha⟩ : ∃ a : ℂ, x ᵥ* schur κ₀ g = a • x :=
        ⟨_, by simpa [vecMul_schur_eq_iff, x, G₀, nablaCombination_weylGramOver_mulVec] using
          rowSubst_weylKernel_permArray _ _ hg⟩
      simp only [dotProduct_mulVec, h_row, ha, smul_vecMul, smul_dotProduct, h_value_zero,
        smul_eq_mul, mul_zero]
    -- By `h_row`, `T'` kills all `x ᵥ* schur κ₀ g` with `g` invertible, and these span.
    have T_mul_gram : T'ᵀ * G₀ = 0 := by
      refine toLin'.injective (ext_schur_weylEval (rowEquivFin n) fun g ↦ ?_)
      simpa only [d, G₀, toLin'_mul, LinearMap.coe_comp, Function.comp_apply, toLin'_apply,
        mulVec_mulVec _ weylGramOver, weylGramOver_mul_schur, ← mulVec_mulVec, mulVec_transpose,
        vecMul_vecMul, map_zero, LinearMap.zero_apply, det_transpose, x_mul_T, zero_vecMul,
        isUnit_iff_ne_zero, ne_eq, prod_eq_zero_iff, mem_univ, pow_eq_zero_iff',
        GeneralLinearGroup.det_ne_zero, false_and, and_false, exists_false, not_false_eq_true,
        IsUnit.smul_eq_zero] using (h_row fun τ ↦ (g τ).valᵀ).symm
    let G₀_invertible : Invertible G₀ := weylGramOver_posDef.isUnit.invertible (a := G₀)
    simpa using congrArg (fun M ↦ M * ⅟G₀) T_mul_gram
  -- `T` is equivariant for unitary `g`, hence for all `g` by Zariski density: an entry of the
  -- defect is a polynomial in `g`, and at a unitary `g` the factor `det ^ e` cancels from `hT`.
  have T_equiv (g : (τ : Φ) → Matrix (n τ) (n τ) ℂ) : D g T = 0 := by
    ext i j
    have h_eval (z : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
        evalMatrix z (D (genericMatrixAt ℂ n) (T.map C) i j) = D z T i j := by
      simp only [Pi.add_apply, blockScalar.eq_unfold, reindex_apply, Pi.one_apply, diagonal_one,
        LinearMap.sub_apply, mulRightLinearMap_apply, LinearMap.smul_apply, mulLeftLinearMap_apply,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_matrix_mul, Matrix.map_map,
        Function.comp_def, eval_C, map_id', FitsRanks.refl, ← schur_map, ← submatrix_map,
        fromBlocks_map, genericMatrixAt_map_evalMatrix, map_zero, Matrix.map_zero, map_one,
        Matrix.map_one, map_mul, map_prod, map_pow, map_det, mapMatrix_apply, D]
    have h_unitary (z : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) (hz : ∀ τ : Φ, (z τ)ᴴ * z τ = 1) :
        D z T i j = 0 := by
      obtain ⟨y, hy, h_equiv⟩ := hT (fun τ ↦ ⟨z τ, (z τ)ᴴ, mul_eq_one_symm (hz τ), hz τ⟩) hz
      simpa only [D, Pi.add_apply, blockScalar.eq_unfold, reindex_apply, Pi.one_apply, diagonal_one,
        LinearMap.sub_apply, mulRightLinearMap_apply, LinearMap.smul_apply, mulLeftLinearMap_apply,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_eq_zero, weylRep, Units.smul_def,
        Units.coe_prod, Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply,
        MonoidHom.coe_mk, OneHom.coe_mk, hy, det_submatrix_equiv_self, det_fromBlocks_one₂₂,
        Matrix.mul_zero, sub_zero, Matrix.mul_smul, he₀, _root_.zpow_add, zpow_natCast,
        prod_mul_distrib, Units.val_mul, Units.val_pow_eq_pow_val, smul_mul, mul_assoc,
        mul_eq_mul_left_iff, prod_eq_zero_iff, mem_univ, ne_eq, det_ne_zero_of_left_inverse (hz _),
        not_false_eq_true, zpow_ne_zero, and_false, exists_false, or_false]
        using congrFun₂ h_equiv i j
    rw [← h_eval]
    exact zariski_dense_unitary g _ fun z hz ↦ (h_eval z).trans (h_unitary z hz)
  have B_defect (g : (τ : Φ) → Matrix (n τ) (n τ) ℂ) : D g (B.map (Int.cast : ℤ → ℂ)) = 0 :=
    sub_eq_zero.mpr (B_block g)
  -- `B ≠ 0` because `c • branchVector ℂ ι γ κ' ≠ 0`, so `x ᵥ* B ⬝ᵥ v ≠ 0`.
  have h_kernel_ne (κ : Φ → ℕ → ℕ) (e : ∀ τ : Φ, N τ ≃ Fin (rankAt N τ)) :
      weylKernel (R := ℂ) N κ (permArray fun (τ : Φ) (a : N τ) ↦ (e τ a : ℕ)) ≠ 0 :=
    ne_zero_of_map (ne_zero_of_eq_one (eval_weylKernel_permArray e))
  have value_ne : x ᵥ* B.map (↑) ⬝ᵥ v ≠ 0 := by
    intro h
    simpa [eq_zero _ B_defect h, branchVector, hc, h_kernel_ne] using B_top.symm
  -- `T - a • B` is equivariant and `x ᵥ* (T - a • B) ⬝ᵥ v = 0`, so it is zero.
  set a : ℂ := x ᵥ* T ⬝ᵥ v / x ᵥ* B.map (↑) ⬝ᵥ v with ha
  refine ⟨a, sub_eq_zero.mp (eq_zero _ (fun g ↦ ?_) ?_)⟩
  · show D g (T - a • B.map Int.cast) = 0
    simp [T_equiv, B_defect]
  · show x ᵥ* (T - a • B.map Int.cast) ⬝ᵥ v = 0
    simp [ha, value_ne, vecMul_sub, vecMul_smul]

/-- Branching from `GL (n + 1)` to `GL n`. Write `κ = γ + κ'`: of the `κ τ h` columns of height `h`,
`γ τ h` lose a box and `κ' τ h` keep theirs, and `κ₀ τ h = κ' τ h + γ τ (h + 1)` for
`0 < h < rankAt n τ`. Columns of height `rankAt n τ` that keep their box become powers of `det`:
`e₀ τ = e τ + κ' τ (rankAt n τ)`. Let all columns of height below `q` lose a box. Write
`ρ = weylRep κ e` and `ρ₀ = weylRep κ₀ e₀`. Then some integral matrix `br` has three properties. (a)
Over every field of characteristic zero, `br ρ(diag(g, s)) = (∏ τ, s τ ^ (diagramWeight (rankAt N) γ
(τ, 0) + e τ)) ρ₀(g) br`. (b) Its operator norm for the Gram norms is at most `L ^ (3 L)` if `L`
bounds the number of boxes of `κ₀` in columns of height `h` with `q ≤ h < rankAt n τ`; the bound is
stated for squared norms. (c) It spans the maps over `ℂ` that are equivariant for the unitary block
group.

Part of the multiplicity-one branching rule from GL (n + 1) to GL n: for a given interlacing pair,
an integral equivariant matrix exists and the multiplicity is at most one. -/
lemma _root_.New.exists_branching_matrix (κ₀ : Φ → ℕ → ℕ) (q : ℕ) (e e₀ : Φ → ℤ) (hκ : γ + κ' = κ)
    (hκ₀ : ∀ τ : Φ, ∀ h ∈ Ioo 0 (rankAt n τ), κ₀ τ h = κ' τ h + γ τ (h + 1))
    (hq : ∀ τ : Φ, ∀ i < q, κ' τ i = 0) (he₀ : ∀ τ : Φ, e₀ τ = e τ + κ' τ (rankAt n τ)) :
    ∃ br : Matrix (WeylIndexFamily n κ₀) (WeylIndexFamily N κ) ℤ,
      -- (a)
      (∀ (R : Type) [Field R] [CharZero R] (g : (τ : Φ) → GL (n τ) R) (s : Φ → Rˣ)
        (x : (τ : Φ) → GL (N τ) R),
        (∀ τ : Φ, (x τ).val = blockScalar ι (fun τ : Φ ↦ (g τ).val) (fun τ : Φ ↦ (s τ).val) τ) →
        br.map (Int.cast : ℤ → R) * weylRep κ e x =
          (∏ τ : Φ, s τ ^ (diagramWeight (rankAt N) γ (τ, 0) + e τ)) •
            (weylRep κ₀ e₀ g * br.map (Int.cast : ℤ → R))) ∧
      -- (b)
      (∀ L : ℕ, ∑ τ : Φ, ∑ h ∈ Ico q (rankAt n τ), h * κ₀ τ h ≤ L →
        ∀ ξ : WeylIndexFamily N κ → ℂ,
          weylNormSq (br.map (Int.cast : ℤ → ℂ) *ᵥ ξ) ≤ ((L ^ L) ^ 3) ^ 2 * weylNormSq ξ) ∧
      -- (c)
      SpansBranchingMaps ι e₀ e (br.map (Int.cast : ℤ → ℂ)) := by
  -- The matrix is the `B` of `exists_int_branching_of_weylKernel`, for the vector `η` and the
  -- denominator `0 < c ≤ L ^ (3 L)` of `exists_smul_weylKernel_mul_eq_toPoly`.
  subst hκ
  obtain ⟨c, c_pos, c_le, η, hη⟩ :=
    exists_smul_weylKernel_mul_eq_toPoly (n := n) (γ := fun (τ : Φ) (h : ℕ) ↦ γ τ (h + 1)) hq hκ₀
  obtain ⟨B, B_top, B_equiv⟩ := exists_int_branching_of_weylKernel ι hη
  -- Equivariance over `ℂ` for `diag(g, 1)`.
  have B_block (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      B.map (Int.cast : ℤ → ℂ) * schur (γ + κ') (blockScalar ι g 1) =
        (∏ τ : Φ, (g τ).det ^ κ' τ (rankAt n τ)) • (schur κ₀ g * B.map (Int.cast : ℤ → ℂ)) := by
    simpa using B_equiv ℂ g 1
  refine ⟨B, fun R _ _ g s x hx ↦ ?_, fun L hL ξ ↦ ?_,
    spansBranchingMaps_of_equivariant ι c_pos.ne' he₀ B_top B_block⟩
  · -- Multiply `B_equiv` by the powers of the determinants, with `det (x τ) = det (g τ) * s τ`.
    have h_schur : B.map (Int.cast : ℤ → R) * schur (γ + κ') (fun τ : Φ ↦ (x τ).val) =
        (∏ τ : Φ, (s τ).val ^ diagramWeight (rankAt N) γ (τ, 0) *
            (g τ).val.det ^ κ' τ (rankAt n τ)) •
          (schur κ₀ (fun τ : Φ ↦ (g τ).val) * B.map (Int.cast : ℤ → R)) := by
      rw [funext hx]
      exact B_equiv R (fun τ : Φ ↦ (g τ).val) fun τ : Φ ↦ (s τ).val
    have h_det (τ : Φ) : (x τ).val.det = (g τ).val.det * (s τ).val := by
      simp [hx τ, blockScalar]
    simp [weylRep, h_schur, h_det, he₀, Units.smul_def, mul_zpow, _root_.zpow_add, smul_smul,
      prod_mul_distrib, mul_assoc, mul_left_comm]
  · have hc_le : (c : ℝ) ≤ ((L : ℝ) ^ L) ^ 3 := by exact_mod_cast c_le L hL
    calc weylNormSq (B.map (Int.cast : ℤ → ℂ) *ᵥ ξ)
      _ ≤ (c : ℝ) ^ 2 * weylNormSq ξ := weylNormSq_mulVec_le_of_equivariant ι B_top B_block ξ
      _ ≤ (((L : ℝ) ^ L) ^ 3) ^ 2 * weylNormSq ξ := by
        gcongr
        exact weylNormSq_nonneg ξ

end New.GL

end Branching

end
