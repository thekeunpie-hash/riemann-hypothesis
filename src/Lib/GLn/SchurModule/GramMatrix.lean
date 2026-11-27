module

public import Aesop.BuiltinRules
public import Lib.GLn.SchurModule.Basic
import Lib.GLn.SchurModule.SchurMatrix
import Lib.General.LinearAlgebra.MinorProducts
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Lib.General.Analysis.HolomorphicIntegrals
import Lib.General.Groups.CongruenceSubgroups
import Lib.Shimura.ComplexTheta.AppellHumbertData
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
public import Lib.General.LinearAlgebra.IntegralLattices

section
section
/-!
# The Weyl module inside the tensors of its diagram

A tensor in the product of exterior powers, one factor for each column of the diagram, is written as
a function on the column fillings `New.ColumnFilling`, which index the basis tensors.

* `New.fillingMatrix`: the integral matrix that embeds the Weyl module into tensors. Its row at a
  column filling holds the coordinates, in the standard basis, of the product of minors
  `New.fillingPoly` of that filling.
* `New.fillingMatrixOver_mul_schur`: the Schur matrix of a family of square matrices, one for each
  place `τ`, is the restriction of their action `New.minorsMatrix` on tensors.
* `New.span_fillingPoly`: the products of minors span the module of Borel semi-invariants, whose
  dual is the Weyl module.
* `New.exists_fillingMatrix_leftInverse`: the Weyl module is a direct summand of the integral
  tensors.

Notions from other files:
* A `Tableau` lists the entries of each column; `tableauPoly R e T` is the product, over the columns
  of the tableau `T`, of the `minor` whose rows are the images under `e` of the entries. Here
  `minor R I` is the determinant of the variables `y` in the rows `I` and the first columns;
  `MatrixPoly ι R` is the ring of polynomials in these variables `y`, indexed by `ι × ℕ` (a row and
  a column number).
* `nablaBasis R n κ`, the standard basis, is a chosen basis of products of minors of the module
  `nablaFamily R n κ`, indexed by `WeylIndexFamily n κ`; `nablaCombination κ` takes a coordinate
  vector to its combination of this basis. A vector of the Weyl module is given by its coordinates
  `WeylIndexFamily n κ → R` in the dual basis.
* `rowSubst z` substitutes `z y` for `y`, and row `i` of `schur κ z` holds the coordinates of
  `rowSubst z` of the basis element `i`; so `schur κ z` acts on the Weyl module.

## Relation to the literature

Known result: the Weyl module over `ℤ` as a direct summand as a ℤ-module of a tensor product of
exterior powers. Source: Akin, Buchsbaum and Weyman, Schur functors and Schur complexes.
-/

@[expose] public section

noncomputable section

open MvPolynomial Finset Matrix Fintype Function New «GL»

namespace New

section Tensors

variable {Φ R : Type} [CommRing R] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}

/-- The strictly increasing sequences of length `h` in `Fin N`. -/
abbrev IncreasingMap (N h : ℕ) : Type := {f : Fin h → Fin N // StrictMono f}

/-- The Cauchy–Binet formula as a sum over increasing sequences: the determinant of the product of
an `h × N` and an `N × h` matrix is the sum, over the increasing sequences `I` of length `h`, of
the products of the two minors at `I`. -/
lemma det_mul_eq_sum_increasing {N h : ℕ}
    (A : Matrix (Fin h) (Fin N) R) (B : Matrix (Fin N) (Fin h) R) :
    (A * B).det =
      ∑ I : IncreasingMap N h, (A.submatrix id I.val).det * (B.submatrix I.val id).det := by
  -- A set `S` of `h` indices is the same as its increasing enumeration `enumSubset S`.
  let enum (S : Set.powersetCard (Fin N) h) : IncreasingMap N h :=
    ⟨enumSubset S, (Set.powersetCard.ofFinEmbEquiv.symm S).strictMono⟩
  have h_bij : Function.Bijective enum :=
    ⟨fun S S' h_eq ↦ Set.powersetCard.ofFinEmbEquiv.symm.injective
        (DFunLike.coe_injective (congrArg Subtype.val h_eq)),
      fun ⟨f, hf⟩ ↦ ⟨Set.powersetCard.ofFinEmbEquiv (.ofStrictMono f hf),
        by simp [enum, enumSubset]⟩⟩
  rw [det_mul_eq_sum_minors]
  exact Fintype.sum_bijective enum h_bij _ _ fun _ ↦ mul_comm _ _

/-- For an `h` by `n τ` matrix `c`, the determinant of `c y`, where `y` consists of the first `h`
columns of the variables at the place `τ`, is the sum over increasing row numbers `I` of the minor
of `c` with columns `I` times the minor of `y` with rows `I`. Here `rankAt n τ` is the number of
elements of `n τ`, and the row numbers are read as elements of `n τ` through their numbering
`rowEquivFin n τ`. -/
lemma det_sum_smul_X (τ : Φ) {h : ℕ} (c : Matrix (Fin h) (n τ) R) :
    (of fun s t : Fin h ↦ ∑ a : n τ, c s a • X (R := R) ((⟨τ, a⟩ : Σ τ : Φ, n τ), (t : ℕ))).det =
      ∑ I : IncreasingMap (rankAt n τ) h, (c.submatrix id ((rowEquivFin n τ).symm ∘ I.val)).det •
        minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘ I.val) := by
  have hproduct : (of fun s t : Fin h ↦
      ∑ a : n τ, c s a • X (R := R) ((⟨τ, a⟩ : Σ τ, n τ), (t : ℕ))) =
        ((c.submatrix id (rowEquivFin n τ).symm).map C :
            Matrix (Fin h) (Fin (rankAt n τ)) (MatrixPoly (Σ τ : Φ, n τ) R)) *
          of fun (a : Fin (rankAt n τ)) (t : Fin h) ↦
            X (R := R) ((⟨τ, (rowEquivFin n τ).symm a⟩ : Σ τ, n τ), (t : ℕ)) := by
    ext s t : 1
    simp only [of_apply, smul_eq_C_mul]
    exact (Equiv.sum_comp (rowEquivFin n τ).symm _).symm
  rw [hproduct, det_mul_eq_sum_increasing]
  -- Both sides are products of the same minors, by the definition of the matrix of variables.
  exact Finset.sum_congr rfl fun I _ ↦ by
    simp [smul_eq_C_mul, RingHom.map_det, minor, Matrix.submatrix, Matrix.map,
      Function.comp_def]

variable (n κ) in
/-- The index set of the basis tensors for the diagram with `κ τ h` columns of height `h` at `τ`,
for the heights below the rank `rankAt n τ`, the number of elements of `n τ`: an increasing sequence
of `h` row numbers for each column. -/
abbrev ColumnFilling : Type :=
  ∀ (τ : Φ) (h : Fin (rankAt n τ)), Fin (κ τ h) → IncreasingMap (rankAt n τ) h

/-- The tableau of a column filling at `τ`, with row numbers read as rows through `rowEquivFin n τ`,
the numbering of `n τ` by `Fin (rankAt n τ)`. -/
def fillingRows (T : ColumnFilling n κ) (τ : Φ) : Tableau (n τ) (rankAt n τ) (κ τ) :=
  fun (h : Fin (rankAt n τ)) (j : Fin (κ τ h)) (s : Fin h) ↦ (rowEquivFin n τ).symm ((T τ h j).1 s)

variable [Fintype Φ]

variable (R) in
/-- The product of the minors of the variables on the columns of a filling: a column of height `h`
gives the minor with the rows of its entries and the first `h` columns of variables. -/
def fillingPoly (T : ColumnFilling n κ) : MatrixPoly (Σ τ : Φ, n τ) R :=
  ∏ τ : Φ, tableauPoly R (Sigma.mk τ) (fillingRows T τ)

variable (κ) in
/-- The matrix by which `z` acts on tensors: the entry at `(T, T')` is the product, over the
columns of the diagram, of the minor of `z τ` with rows from `T` and columns from `T'`, where `τ`
is the place of the column. -/
def minorsMatrix (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    Matrix (ColumnFilling n κ) (ColumnFilling n κ) R :=
  of fun T T' : ColumnFilling n κ ↦ ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
    ((z τ).submatrix (fillingRows T τ h j) (fillingRows T' τ h j)).det

end Tensors

section Action

variable {Φ R : Type} [CommRing R] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}
  [Fintype Φ]

/-- The action `minorsMatrix` of transposed matrices on tensors is the transpose of the action. -/
lemma minorsMatrix_transpose (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    minorsMatrix κ (fun τ : Φ ↦ (z τ)ᵀ) = (minorsMatrix κ z)ᵀ := by
  ext T T'
  simp only [minorsMatrix, of_apply, transpose_apply, ← transpose_submatrix, det_transpose]

variable [DecidableEq Φ]

omit [DecidableEq Φ] [Fintype Φ] in
/-- Substituting `z y` for the variables `y` in the minor with rows `J` at the place `τ` gives the
sum, over increasing row numbers `I`, of the minor of `z τ` with rows `J` and columns `I` times the
minor of `y` with rows `I`. -/
lemma rowSubst_minor_comp_sigmaMk (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) (τ : Φ) {h : ℕ}
    (J : Fin h → n τ) :
    rowSubst z (minor R (Sigma.mk τ ∘ J)) = ∑ I : IncreasingMap (rankAt n τ) h,
      ((z τ).submatrix J ((rowEquivFin n τ).symm ∘ I.val)).det •
        minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘ I.val) := by
  refine Eq.trans ?_ (det_sum_smul_X τ ((z τ).submatrix J id))
  simp [minor, AlgHom.map_det, rowSubst, Matrix.map]

/-- For a family of tableaux `U`, substituting `z y` for the variables `y` in the product of the
minors on the columns of `U` gives the sum over column fillings `T` of the product of minors
`fillingPoly` of `T`, times the product over the columns of the minor of `z τ` with rows from `U`
and columns from `T`, where `τ` is the place of the column. -/
lemma rowSubst_prod_tableauPoly (z : ∀ τ : Φ, Matrix (n τ) (n τ) R)
    (U : ∀ τ : Φ, Tableau (n τ) (rankAt n τ) (κ τ)) :
    rowSubst z (∏ τ : Φ, tableauPoly R (Sigma.mk τ) (U τ)) =
      ∑ T : ColumnFilling n κ, (∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
        ((z τ).submatrix (U τ h j) (fillingRows T τ h j)).det) • fillingPoly R T := by
  simp only [fillingPoly, tableauPoly, map_prod, rowSubst_minor_comp_sigmaMk, Fintype.prod_sum,
    Finset.prod_smul]
  -- The rows of the column filling are `fillingRows T` by definition.
  rfl

/-- Substituting `z y` for `y` in the product of minors `fillingPoly` of a column filling `T` gives
the combination of these products with row `T` of the matrix `minorsMatrix` as coefficients. -/
lemma rowSubst_fillingPoly (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) (T : ColumnFilling n κ) :
    rowSubst z (fillingPoly R T) =
      ∑ T' : ColumnFilling n κ, minorsMatrix κ z T T' • fillingPoly R T' :=
  rowSubst_prod_tableauPoly z (fillingRows T)

end Action

section Embedding

variable {Φ R : Type} [CommRing R] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}
  [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)]

variable (n κ) in
/-- The integral matrix of the embedding of the Weyl module into tensors: row `T` holds the
coordinates, in the standard basis, of the product of minors of `T`. -/
def fillingMatrix : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) ℤ :=
  of fun T : ColumnFilling n κ ↦ invFun (nablaCombination (R := ℤ) κ) (fillingPoly ℤ T)

variable (R n κ) in
/-- The matrix `fillingMatrix` with its entries mapped into `R`. -/
abbrev fillingMatrixOver : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) R :=
  (fillingMatrix n κ).map (Int.cast : ℤ → R)

omit [(τ : Φ) → DecidableEq (n τ)] in
lemma fillingMatrixOver_int : fillingMatrixOver ℤ n κ = fillingMatrix n κ := by
  ext T i
  simp

/-- For a column filling `T` (an increasing sequence of rows in each column of the diagram `κ`), the
row `T` of the embedding `fillingMatrixOver` of the Weyl module into tensors is the coordinate
vector of the product of minors `fillingPoly R T`: the map `nablaCombination`, which takes
coordinates to the combination of the standard basis of products of minors, sends it to that
product. -/
lemma nablaCombination_fillingMatrixOver (T : ColumnFilling n κ) :
    nablaCombination κ (fillingMatrixOver R n κ T : WeylIndexFamily n κ → R) = fillingPoly R T := by
  -- By definition, row `T` of `fillingMatrix` holds coordinates of `fillingPoly ℤ T`.
  have hZ : ∑ i : WeylIndexFamily n κ, fillingMatrix n κ T i • nablaBasis ℤ n κ i =
      fillingPoly ℤ T :=
    sum_coords_nablaBasis (prod_tableauPoly_mem_nabla (T := fillingRows T))
  have hmap : MvPolynomial.map (Int.castRingHom R) (fillingPoly ℤ T) = fillingPoly R T := by
    simp [fillingPoly, tableauPoly, minor, RingHom.map_det, Matrix.map]
  -- Apply the change of rings from `ℤ` to `R` to the expansion over `ℤ`.
  simp [← hmap, ← hZ, Fintype.linearCombination_apply, smul_eq_C_mul]

/-- The embedding `fillingMatrixOver` of the Weyl module into tensors sends the vector `weylEval`,
of the values at `y` of the standard basis of products of minors, to the vector whose coordinate at
a column filling `T` is the value at `y` of the product of minors `fillingPoly R T`. -/
lemma fillingMatrixOver_mulVec_weylEval (y : (Σ τ : Φ, n τ) × ℕ → R) (T : ColumnFilling n κ) :
    (fillingMatrixOver R n κ *ᵥ weylEval n κ y) T = eval y (fillingPoly R T) := by
  simp [← nablaCombination_fillingMatrixOver T, Fintype.linearCombination_apply, mulVec, dotProduct,
    weylEval]

/-- For a tensor `v`, given by its values on column fillings, the transposed embedding
`(fillingMatrixOver R n κ)ᵀ` takes `v` to the coordinates of the combination with coefficients `v`
of the products of minors `fillingPoly`. Here `nablaCombination` takes coordinates to the
combination of the standard basis of products of minors. -/
lemma nablaCombination_transpose_mulVec (v : ColumnFilling n κ → R) :
    nablaCombination κ ((fillingMatrixOver R n κ)ᵀ *ᵥ v) =
      ∑ T : ColumnFilling n κ, v T • fillingPoly R T := by
  -- The transposed matrix sends `v` to the combination of the rows with coefficients `v`.
  simp only [mulVec_transpose, vecMul_eq_sum, map_sum, map_smul, nablaCombination_fillingMatrixOver]

/-- For a family `z` of square matrices, the embedding `fillingMatrixOver` of the Weyl module into
tensors intertwines the Schur matrix `schur κ z`, the action of `z` on the Weyl module, with
`minorsMatrix κ z`, the action of `z` on tensors by products of minors. -/
lemma fillingMatrixOver_mul_schur (z : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    fillingMatrixOver R n κ * schur κ z = minorsMatrix κ z * fillingMatrixOver R n κ := by
  refine funext fun T : ColumnFilling n κ ↦ ?_
  -- Both rows are compared as combinations of the standard basis, which is independent.
  apply nablaCombination_injective
  calc nablaCombination κ ((fillingMatrixOver R n κ * schur κ z) T)
      = rowSubst z (nablaCombination κ (fillingMatrixOver R n κ T)) := by
        simp [mul_apply_eq_vecMul, vecMul_eq_sum,
          Fintype.linearCombination_apply]
    _ = nablaCombination κ ((minorsMatrix κ z * fillingMatrixOver R n κ) T) := by
        simp [nablaCombination_fillingMatrixOver, rowSubst_fillingPoly, mul_apply_eq_vecMul,
          vecMul_eq_sum]

variable (R n κ) in
/-- The module `nablaFamily R n κ` of Borel semi-invariants is the span of the products of minors
`fillingPoly R T` over all column fillings `T`, the coordinates of the tensor of the variables. -/
lemma span_fillingPoly :
    Submodule.span R (Set.range fun T : ColumnFilling n κ ↦ fillingPoly R T) =
      nablaFamily R n κ := by
  apply le_antisymm
  · exact Submodule.span_le.2 <| Set.range_subset_iff.2 fun T ↦
      prod_tableauPoly_mem_nabla (T := fillingRows T)
  · rw [← range_nablaCombination, Fintype.range_linearCombination, Submodule.span_le,
      Set.range_subset_iff]
    intro i
    -- Substituting the identity matrices into a basis element, a product of minors with rows in
    -- any order, expands it in the products with increasing rows.
    have h_expand : nablaBasis R n κ i =
        ∑ T : ColumnFilling n κ, (∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h),
          ((1 : Matrix (n τ) (n τ) R).submatrix ((i τ).val h j) (fillingRows T τ h j)).det) •
            fillingPoly R T :=
      (rowSubst_one _).symm.trans (rowSubst_prod_tableauPoly (fun _ ↦ 1) fun τ : Φ ↦ (i τ).val)
    rw [h_expand]
    exact Submodule.sum_mem _ fun T _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

/-- The integral matrix `fillingMatrix`, which embeds the Weyl module of the diagram `κ` (with basis
indexed by `WeylIndexFamily n κ`) into tensors (with basis indexed by column fillings), has an
integral left inverse. So the Weyl module is a direct summand of the integral tensors. -/
lemma exists_fillingMatrix_leftInverse :
    ∃ Q : Matrix (WeylIndexFamily n κ) (ColumnFilling n κ) ℤ, Q * fillingMatrix n κ = 1 := by
  -- The map from tensors onto the span of the products of minors splits, as its target is free:
  -- choose a tensor `v i` over each basis element.
  have h_onto (i : WeylIndexFamily n κ) : ∃ v : ColumnFilling n κ → ℤ,
      ∑ T : ColumnFilling n κ, v T • fillingPoly ℤ T = nablaBasis ℤ n κ i := by
    rw [← Submodule.mem_span_range_iff_exists_fun, span_fillingPoly, nablaBasis]
    exact prod_tableauPoly_mem_nabla
  choose v hv using h_onto
  refine ⟨of v, funext fun i : WeylIndexFamily n κ ↦ ?_⟩
  apply nablaCombination_injective
  have h_row : (of v * fillingMatrix n κ) i = (fillingMatrixOver ℤ n κ)ᵀ *ᵥ v i := by
    rw [fillingMatrixOver_int, mulVec_transpose, mul_apply_eq_vecMul]
    rfl
  rw [h_row, nablaCombination_transpose_mulVec, hv]
  simp [Matrix.one_apply, Fintype.linearCombination_apply]

end Embedding

end New
end
end
end

/-!
# The Weyl kernel and its Gram matrix: the hook number bound, positivity, Schur's lemma

This file studies the reproducing kernel `K(x, y) = f(yᵀ x)` (`New.weylKernel`), where
`f = New.highestPoly` is the product of leading principal minors. `G = New.weylGram` is the integer
Gram matrix of `K` in the basis `b_i = New.nablaBasis` (products of minors) of the semi-invariants
`New.nablaFamily`. The hook number `New.hookNumber κ N = ⟨f, f⟩ = f(∂) f(0)` is the Fock pairing
of `f` with itself. It is positive and at most `(L ^ L) ^ 3` when the diagrams have at most `L`
boxes in total (`New.hookNumber_pos`, `New.hookNumber_le`). This file also proves that the unitary
group is Zariski dense, and derives Schur's lemma for the Schur matrices.

## Main definitions and results

* `New.toPoly_weylEval`, `New.toPoly_schur`: `New.toPoly`, `ξ ↦ ∑ (G ξ)_i b_i`, sends the vector
  `ev_y = (b_i(y))` (`New.weylEval`) to `K(·, y)`. It turns the Schur matrix of `z` into
  substitution of `zᵀ`, applied after multiplying by the determinant powers `New.detPow` with
  exponents `New.schurDetExp`.
* `New.fillingMatrix_transpose_mul_self`: `G` is the matrix of the form restricted from tensors.
  Hence `G` is symmetric, positive definite, and makes the Schur matrices of `g` and `gᵀ` adjoint
  (`New.weylGram_isSymm`, `New.weylGramOver_posDef`, `New.weylGramOver_mul_schur`).
* `New.mem_range_scalar_of_commute_schur`: a matrix that commutes with `New.schur κ g` for all
  unitary `g` is scalar.

Notions from other files:
* `New.WeylIndexFamily n κ`: families that choose, for each place `τ`, a standard filling with rows
  `n τ`; they index the basis `b_i`.
* `New.schur κ z`: the Schur matrix `S_κ(z)` of matrices `z τ` of size `n' τ × n τ`. Row `i`
  holds the coordinates of `b'_i(z y)` in the products `b_j(y) · ∏_τ det(y_τ)^{d_τ}`, where `b'` is
  the basis for the rows `n'` and `d = New.schurDetExp n n' κ`.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.SchurNorm` and `Lib.GLn.Dual` for sources.
-/

@[expose] public section

/-!
## Positivity and a bound for the hook number

* `New.hookNumber_pos`, `New.hookNumber_le`: the hook number is positive, and at most
  `(L ^ L) ^ 3` when the diagrams have at most `L` boxes in total.
-/

section Hook

open MvPolynomial Finset Matrix Finsupp Nat RingHom

namespace New

variable {Φ : Type} [Fintype Φ] {κ : Φ → ℕ → ℕ} {N : Φ → ℕ} {L : ℕ}

/-- The hook number, the Fock pairing of `New.highestPoly ℤ κ N` with itself, is positive. -/
@[simp]
lemma hookNumber_pos : 0 < hookNumber κ N := by
  -- `highestPoly ℤ κ N` is nonzero, since its value at the identity array is `1`.
  have h_eval : eval (permArray fun τ (i : Fin (N τ)) ↦ (i : ℕ)) (highestPoly ℤ κ N) = 1 := by
    simp [highestPoly, tableauPoly, minor, map_det, Matrix.map, permArray, Fin.val_inj,
      ← diagonal.eq_1]
  have h_ne : highestPoly ℤ κ N ≠ 0 := fun h_zero ↦ by simp [h_zero] at h_eval
  -- Over `ℤ` conjugation is trivial, so `fockPairing_star_self_pos` is the claim.
  have h_star : MvPolynomial.map (starRingEnd ℤ) (highestPoly ℤ κ N) = highestPoly ℤ κ N :=
    MvPolynomial.ext _ _ fun d ↦ by simp
  simpa only [hookNumber, h_star] using fockPairing_star_self_pos h_ne

@[simp]
lemma hookNumber_ne_zero : hookNumber κ N ≠ 0 := hookNumber_pos.ne'

lemma prod_factorial_le_factorial_sum {ι : Type} (s : Finset ι) (a : ι → ℕ) :
    ∏ i ∈ s, (a i)! ≤ (∑ i ∈ s, a i)! :=
  le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s a)

/-- Two monomials with coefficients `± 1` have Fock pairing at most `d !`, where `d` is the degree
of the first. -/
lemma fockPairing_monomial_monomial_le {σ : Type} (α β : σ →₀ ℕ) (ε ε' : ℤˣ) :
    fockPairing ℤ (monomial α (ε : ℤ)) (monomial β (ε' : ℤ)) ≤ (α.degree)! := by
  classical
  have h_factorial : (α.prod fun _ a ↦ a !) ≤ (α.degree)! :=
    prod_factorial_le_factorial_sum α.support α
  have h_unit : (ε : ℤ) * ε' ≤ 1 := Int.le_of_dvd one_pos (ε.isUnit.mul ε'.isUnit).dvd
  have h_coeff : (ε : ℤ) * (monomial β (ε' : ℤ)).coeff α ≤ 1 := by grind [coeff_monomial]
  grw [fockPairing_monomial, h_coeff, mul_one, h_factorial]

/-- Take at each place `τ` a filling `T τ` with `κ τ h` columns of height `h` for `h < N τ`, and
multiply the minors of all columns. If the degree `∑ τ, ∑ h < N τ, h * κ τ h` of this product is at
most `L`, then its Fock pairing with itself is at most `L ^ (3 * L)`. -/
lemma fockPairing_tableauPoly_le {n : Φ → Type} (T : ∀ τ : Φ, Tableau (n τ) (N τ) (κ τ))
    (h_degree : ∑ τ : Φ, ∑ h ∈ range (N τ), h * κ τ h ≤ L) :
    fockPairing ℤ (∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ) (T τ))
      (∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ) (T τ)) ≤ (L : ℤ) ^ (3 * L) := by
  classical
  -- Expand each minor over permutations. The product becomes a sum of signed monomials of degree
  -- `d`, one for each choice `s : S` of a permutation for every column, and `card S ≤ d !`.
  let S : Type := ∀ (τ : Φ) (h : Fin (N τ)), Fin (κ τ h) → Equiv.Perm (Fin h)
  let α (s : S) : (Σ τ : Φ, n τ) × ℕ →₀ ℕ :=
    ∑ τ : Φ, ∑ h : Fin (N τ), ∑ j : Fin (κ τ h), ∑ i : Fin h, single (⟨τ, T τ h j (s τ h j i)⟩, i) 1
  let ε (s : S) : ℤˣ := ∏ τ : Φ, ∏ h : Fin (N τ), ∏ j : Fin (κ τ h), (s τ h j).sign
  let d : ℕ := ∑ τ : Φ, ∑ h : Fin (N τ), κ τ h * h
  have h_expand :
      ∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ) (T τ) = ∑ s : S, monomial (α s) (ε s : ℤ) := by
    simp_rw [tableauPoly, minor, det_apply, prod_univ_sum, prod_smul, of_apply, X,
      ← monomial_sum_one, smul_monomial]
    simp [α, ε, S, Units.smul_def]
  have h_degree_eq (s : S) : (α s).degree = d := by simp [α, d]
  have h_card : Fintype.card S ≤ d ! := by
    -- the product over all columns of (height)! is at most the factorial of the sum of the heights
    let height : (Σ (τ : Φ) (h : Fin (N τ)), Fin (κ τ h)) → ℕ := fun ⟨_, h, _⟩ ↦ h
    simpa [S, height, Fintype.card_perm, Fintype.prod_sigma, Fintype.sum_sigma] using
      prod_factorial_le_factorial_sum univ height
  have h_d_le : d ≤ L := by simpa only [d, sum_range, mul_comm] using h_degree
  rw [h_expand]
  calc
    _ = ∑ s : S, ∑ t : S, fockPairing ℤ (monomial (α s) (ε s : ℤ)) (monomial (α t) (ε t : ℤ)) := by
      simp_rw [LinearMap.map_sum₂, map_sum]
    _ ≤ ∑ _s : S, ∑ _t : S, (d ! : ℤ) := by
      gcongr with s _ t
      grw [fockPairing_monomial_monomial_le, h_degree_eq]
    _ = Fintype.card S * (Fintype.card S * (d ! : ℤ)) := by simp
    _ ≤ (d ! : ℤ) ^ 3 := by grw [h_card, h_card, pow_three]
    _ ≤ ((L : ℤ) ^ L) ^ 3 := by grw [h_d_le, factorial_le_pow, cast_pow]
    _ = (L : ℤ) ^ (3 * L) := by rw [← pow_mul, mul_comm]

/-- Suppose the diagrams with `κ τ h` columns of height `h < N τ` have at most `L` boxes in total,
that is, Σ_τ Σ_{h<N τ} h·κ τ h ≤ L. Then `hookNumber κ N` is at most `(L ^ L) ^ 3`. Here
`hookNumber κ N` is the integer ⟨f,f⟩ = f(∂)f(0), where f is the product over places τ and heights
h < N τ of the leading principal h×h minors raised to the power κ τ h. -/
lemma hookNumber_le (h_degree : ∑ τ : Φ, ∑ h ∈ range (N τ), h * κ τ h ≤ L) :
    hookNumber κ N ≤ ((L : ℤ) ^ L) ^ 3 := by
  -- `highestPoly ℤ κ N` is the product of minors for the fillings `T` with `i` in row `i`.
  let T : ∀ τ : Φ, Tableau (Fin (N τ)) (N τ) (κ τ) := fun _ h _ ↦ Fin.castLE h.is_le'
  rw [← pow_mul, mul_comm, hookNumber, highestPoly]
  exact fockPairing_tableauPoly_le T h_degree

end New

end Hook

/-!
## The kernel and the Gram matrix

Linear identities are tested on the vectors `weylEval n κ y` (`New.GL.ext_weylEval`). An array `y`
has rows `(τ, a)` and columns in `ℕ`; `New.diagramWeight` is the partition with `κ τ h` columns of
height `h`.
-/

section Gram

open MvPolynomial Module New «GL» ComplexOrder Sigma Function Fintype Equiv Finset Matrix

variable {Φ : Type}
  {R S : Type _} [CommRing R] [CommRing S] [Fintype Φ] [DecidableEq Φ]
  {n n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] {κ : Φ → ℕ → ℕ}
  (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) (φ : R →+* S)
  (N : Φ → ℕ) (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ n' τ) (g : ∀ τ : Φ, Matrix (n τ) (n τ) R)
  (ξ η : WeylIndexFamily n κ → R) (s : Φ → R) (y : (Σ τ : Φ, n τ) × ℕ → R)

namespace New.GL

/-! ### Evaluation vectors and the kernel -/

/-- For an array `y` and enumerations `e τ` of the rows, the square matrix at the place `τ` with
`(a, b)` entry `y((τ, a), e τ b)`: the columns of block `τ` numbered below `|n τ|`. -/
def squarePart (τ : Φ) : Matrix (n τ) (n τ) R := of fun a b : n τ ↦ y (⟨τ, a⟩, e τ b)

/-- Every evaluation vector `ev_y` is the image of the evaluation vector at the permutation array
of `e` under the Schur matrix of the square part `New.GL.squarePart e y` of `y`. -/
lemma schur_squarePart_mulVec :
    schur κ (squarePart e y) *ᵥ weylEval n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)) =
      weylEval n κ y := by
  -- `squarePart e y` times the permutation array `permArray e` agrees with `y` in the columns below
  -- `rankAt n τ`, the only ones that the basis minors read.
  set w : (Σ τ : Φ, n τ) × ℕ → R := permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)
  have h_frame : schur κ (squarePart e y) *ᵥ weylEval n κ w =
      weylEval n κ fun ⟨⟨τ, i⟩, k⟩ ↦ ∑ a : n τ, squarePart e y τ i a * w (⟨τ, a⟩, k) := by
    simpa only [schurDetExp_self, detPow_zero, map_one, one_smul] using
      schur_mulVec_weylEval (FitsRanks.refl (κ := κ)) (squarePart e y) w
  have h_agree (τ : Φ) (i : n τ) (k : ℕ) (hk : k < rankAt n τ) :
      ∑ a : n τ, squarePart e y τ i a * w (⟨τ, a⟩, k) = y (⟨τ, i⟩, k) := by
    lift k to Fin (rankAt n τ) using hk
    simp [squarePart, w, permArray, Fin.val_inj, ← eq_symm_apply]
  rw [h_frame]
  ext i
  simp (disch := omega) only [weylEval, nablaBasis, tableauPoly, minor, map_prod, RingHom.map_det,
    RingHom.mapMatrix_apply, Matrix.map, of_apply, eval_X, Function.comp_apply, h_agree]

/-- Two linear maps `L`, `L'` into a free module over a domain are equal if they agree on the
evaluation vectors `weylEval n κ y`. It is enough to take the arrays `y` whose entries lie in an
infinite set `s` and at which `detPow R n d`, the product of the powers `d τ` of the determinants
of the square blocks, does not vanish. -/
lemma ext_weylEval [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    {L L' : (WeylIndexFamily n κ → R) →ₗ[R] M} {s : Set R} (d : Φ → ℕ)
    (h_agree : ∀ y : (Σ τ : Φ, n τ) × ℕ → R, (∀ p : (Σ τ : Φ, n τ) × ℕ, y p ∈ s) →
      eval y (detPow R n d) ≠ 0 → L (weylEval n κ y) = L' (weylEval n κ y))
    (hs_infinite : s.Infinite) : L = L' := by
  -- As `M` is free, it suffices to compare `ℓ (L eᵢ)` and `ℓ (L' eᵢ)` for linear forms `ℓ`.
  ext i
  refine eval_apply_injective R (LinearMap.ext fun ℓ ↦ ?_)
  -- These are the coefficients of two combinations `P L`, `P L'` of the independent `b_j * D`, with
  -- `D = detPow R n d`, which agree at every `y` with entries in the infinite set `s`: by
  -- `h_agree` if `D y ≠ 0`, and trivially if `D y = 0`.
  let P (F : (WeylIndexFamily n κ → R) →ₗ[R] M) : MatrixPoly (Σ τ : Φ, n τ) R :=
    ∑ j : WeylIndexFamily n κ, ℓ (F (Pi.single j 1)) • (nablaBasis R n κ j * detPow R n d)
  have h_value (F : (WeylIndexFamily n κ → R) →ₗ[R] M) (y : (Σ τ : Φ, n τ) × ℕ → R) :
      eval y (P F) = ℓ (F (weylEval n κ y)) * eval y (detPow R n d) := by
    rw [pi_eq_sum_univ' (weylEval n κ y)]
    simp [P, ← mul_assoc, sum_mul, mul_comm _ (ℓ _), weylEval]
  have h_poly : P L = P L' := funext_set (fun _ ↦ s) (fun _ ↦ hs_infinite) fun y hy ↦ by
    by_cases hD : eval y (detPow R n d) = 0
    · simp [h_value, hD]
    · rw [h_value, h_value, h_agree y (fun p ↦ hy p (Set.mem_univ p)) hD]
  exact (linearIndependent_nablaBasis_mul_detPow d).eq_coords_of_eq h_poly i

section

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)]

lemma map_weylKernel : MvPolynomial.map φ (weylKernel n κ y) = weylKernel n κ (φ ∘ y) := by
  simp [weylKernel, rowSubst, map_aeval_eq_aeval_map_map, -map_aeval, ← C_mul']

/-- `f(yᵀ x)` as a polynomial in `x`: the product of the leading minors of `yᵀ x`. -/
lemma rowSubst_highestPoly :
    rowSubst (fun τ : Φ ↦ of fun (i : Fin (N τ)) (a : n τ) ↦ y (⟨τ, a⟩, i)) (highestPoly R κ N) =
      ∏ τ : Φ, ∏ h ∈ range (N τ),
        (of fun s t : Fin h ↦ ∑ a : n τ, y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det ^ κ τ h := by
  simp [highestPoly, prod_range, rowSubst, tableauPoly, minor, AlgHom.map_det, Matrix.map]

/-- The kernel is symmetric in `x` and `y`: `K(·, y)` is the generic kernel, whose coefficients are
polynomials in the variables for `y`, with `y` put in for its variables `x`, and the coefficient
variables kept as the new variables. -/
lemma weylKernel_symm :
    weylKernel n κ y = MvPolynomial.eval (C ∘ y)
      (weylKernel n κ (X : (Σ τ : Φ, n τ) × ℕ → MatrixPoly (Σ τ : Φ, n τ) R)) := by
  simp [weylKernel, rowSubst_highestPoly, ← C_mul', mul_comm, RingHom.map_det, Matrix.map]
  -- The minors of `yᵀ X` and `Xᵀ y` are determinants of transposed matrices.
  refine prod_congr rfl fun τ _ ↦ prod_congr rfl fun k _ ↦ ?_
  exact congrArg (fun M ↦ M ^ κ τ k) (det_transpose _).symm

end

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- Multiplying `y` on the right by the upper triangular part of `b` scales the kernel `K(·, y)`
by `∏ b(τ, i, i) ^ λ(τ, i)`, with `λ = New.diagramWeight (rankAt n) κ`. -/
lemma weylKernel_borelMul (b : Φ × ℕ × ℕ → R) :
    weylKernel n κ (borelMul fst b y) =
      ((diagramWeight (rankAt n) κ).prod fun (p : Φ × ℕ) (k : ℕ) ↦ b (p.1, p.2, p.2) ^ k) •
        weylKernel n κ y := by
  -- By symmetry of the kernel, `weylKernel n κ y` is the generic kernel `K` with `y` put in for its
  -- polynomial variables, and in these variables `K` is semi-invariant.
  let A : Type _ := MatrixPoly (Σ τ : Φ, n τ) R
  let K : MatrixPoly (Σ τ : Φ, n τ) A := weylKernel n κ (X : (Σ τ : Φ, n τ) × ℕ → A)
  have h_semi : aeval (borelMul fst (C ∘ b) (C ∘ y) : (Σ τ : Φ, n τ) × ℕ → A) K =
      ((diagramWeight (rankAt n) κ).prod fun p k ↦ C (b (p.1, p.2, p.2)) ^ k) * aeval (C ∘ y) K :=
    mem_nabla.mp (weylKernel_mem_nablaFamily X) A (C ∘ b) (C ∘ y)
  have h_C_borelMul :
      (borelMul fst (C ∘ b) (C ∘ y) : (Σ τ : Φ, n τ) × ℕ → A) = C ∘ borelMul fst b y :=
    funext fun x ↦ by simp [borelMul]
  simp only [MvPolynomial.aeval_eq_eval, h_C_borelMul] at h_semi
  simpa [K, ← C_mul', map_finsuppProd, weylKernel_symm (R := R), comp_def] using h_semi

omit [(τ : Φ) → DecidableEq (n τ)] in
/-- For a vector ξ of the Weyl module over a commutative ring `R` and an array `y` over `R`, the
value at `y` of the polynomial `toPoly n κ ξ = Σ_i (Gξ)_i b_i` equals ev_yᵀ G ξ. Here the b_i are
the basis products of minors `nablaBasis`, indexed by `WeylIndexFamily n κ`, and
ev_y = `weylEval n κ y` is the vector of values b_i(y). G is the integer Gram matrix `weylGram`, the
coefficients of the generic kernel in the products b_i(x) b_j(y), mapped into `R`. -/
@[simp ←]
lemma eval_toPoly : MvPolynomial.eval y (toPoly n κ ξ) = weylEval n κ y ⬝ᵥ weylGramOver *ᵥ ξ := by
  simp [toPoly, mul_comm, linearCombination_apply, dotProduct, weylEval]

omit [(τ : Φ) → DecidableEq (n τ)] in
lemma nablaCombination_weylGramOver_mulVec :
    nablaCombination κ (weylGramOver *ᵥ ξ) = toPoly n κ ξ := rfl

/-- For square matrices `g τ` and scalars `s τ`, the block diagonal matrix `diag(g τ, s τ)`,
reindexed by `n' τ` through the bijection `ι τ : n τ ⊕ Unit ≃ n' τ`. -/
noncomputable def blockScalar (τ : Φ) : Matrix (n' τ) (n' τ) R :=
  ((g τ).fromBlocks 0 0 (diagonal fun _ ↦ s τ)).reindex (ι τ) (ι τ)

omit [DecidableEq Φ] in
/-- The weight at `(τ, i)` is the weight at `(τ, i + 1)` plus `κ τ (i + 1)` when `i + 1 < N τ`:
the columns of height `i + 1` are counted at `i` but not at `i + 1`. -/
@[grind =]
lemma diagramWeight_eq_succ_add (τ : Φ) (i : ℕ) :
    diagramWeight N κ (τ, i) =
      diagramWeight N κ (τ, i + 1) + if i + 1 < N τ then κ τ (i + 1) else 0 := by
  grind [diagramWeight_apply, =_ Ico_add_one_left_eq_Ioo, sum_eq_sum_Ico_succ_bot, Ico_eq_empty]

/-- The kernel `weylKernel n κ y` is the polynomial f(yᵀx) in x, with f the product of leading
minors; here y is the permutation array of `e` (entry 1 at row (τ,a), column `e τ a`, else 0). If
`g τ a b = 0` whenever `e τ a < e τ b`, substituting x ↦ g x in the kernel (`rowSubst g`) scales it
by `∏ g τ a a ^ λ(τ, e τ a)`, with `λ = New.diagramWeight (rankAt n) κ`. -/
lemma rowSubst_weylKernel_permArray (hg_tri : ∀ τ : Φ, (g τ)ᵀ.BlockTriangular (e τ)) :
    rowSubst g (weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ))) =
      (∏ τ : Φ, ∏ a : n τ, g τ a a ^ diagramWeight (rankAt n) κ (τ, e τ a)) •
        weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)) := by
  -- Substituting `g` multiplies the array on the right by the triangular array `t` of the entries
  -- of `g` in the numbering `e`; by `weylKernel_borelMul` this scales the kernel by a monomial in
  -- the diagonal entries. In the product defining `t` the condition selects at most one factor.
  set w : (Σ τ : Φ, n τ) × ℕ → R := permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)
  let t (x : Φ × ℕ × ℕ) : R :=
    ∏ τ : Φ, ∏ a : n τ, ∏ b : n τ, if x = (τ, (e τ a : ℕ), (e τ b : ℕ)) then g τ b a else 1
  have h_sub : rowSubst g (weylKernel n κ w) = weylKernel n κ (borelMul fst t w) := by
    have h_tri (τ : Φ) (a b : n τ) (hab : e τ a < e τ b) : g τ a b = 0 := hg_tri τ hab
    rw [weylKernel, rowSubst_rowSubst, weylKernel]
    congr 2
    -- Entrywise, `borelMul` keeps only the entries on one side of the diagonal; the others vanish.
    simpa +instances [t, w, funext_iff, ← ext_iff, (e _).surjective.forall, borelMul, permArray,
      Fin.val_inj, ite_and, Matrix.mul_apply] using h_tri
  have h_diag : ((diagramWeight (rankAt n) κ).prod fun p k ↦ t (p.1, p.2, p.2) ^ k) =
      ∏ τ, ∏ a, g τ a a ^ diagramWeight (rankAt n) κ (τ, e τ a) := by
    simp [t, ← prod_pow, Finsupp.prod_finsetProd_comm, ← and_assoc,
      ← Prod.ext_iff (y := (_, _)), ite_and, Fin.val_inj]
    -- Outside the support of the weight the exponent is zero.
    exact prod_congr rfl fun τ _ ↦ prod_congr rfl fun a _ ↦
      ite_eq_right_iff.2 fun h_zero ↦ by rw [h_zero, pow_zero]
  rw [h_sub, weylKernel_borelMul, h_diag]

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
lemma rankAt_eq_succ (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ n' τ) (τ : Φ) : rankAt n' τ = rankAt n τ + 1 := by
  simp [← card_congr (ι τ)]

end «GL»

/-! ### The kernel formula -/

/-- The polynomial attached by the Gram matrix to the evaluation vector ev_y is the kernel x ↦
f(yᵀx), f the highest weight product of leading minors. -/
@[simp]
lemma toPoly_weylEval : toPoly n κ (weylEval n κ y) = weylKernel n κ y := by
  -- Expand the generic kernel `K` in the basis, with coefficients `c i` in `A = ℤ[Y]`; expand the
  -- `c i` in the basis again, which gives the Gram matrix; then specialise `Y` to `y`.
  let A : Type := MatrixPoly (Σ τ : Φ, n τ) ℤ
  let K : MatrixPoly (Σ τ : Φ, n τ) A := weylKernel n κ (X : (Σ τ : Φ, n τ) × ℕ → A)
  let c : WeylIndexFamily n κ → A := invFun (nablaCombination κ) K
  have hK : ∑ i, c i • nablaBasis A n κ i = K :=
    sum_coords_nablaBasis (weylKernel_mem_nablaFamily X)
  -- The monomial coefficients of `K` are semi-invariant in `Y` (`weylKernel_borelMul`), hence so is
  -- `c i`: the coordinates lie in any subgroup that holds all coefficients.
  have h_coeff (d : (Σ τ : Φ, n τ) × ℕ →₀ ℕ) : K.coeff d ∈ (nablaFamily ℤ n κ).toAddSubgroup := by
    simp [A, K, mem_nabla, aeval_eq_eval₂Hom, ← coeff_map, map_weylKernel, weylKernel_borelMul,
      comp_def]
  have hc (i : WeylIndexFamily n κ) : c i ∈ nablaFamily ℤ n κ :=
    coord_mem_of_coeff_mem _ 0 (by simpa [detPow_zero] using hK) h_coeff i
  have h_gram (i : WeylIndexFamily n κ) : ∑ j, weylGram n κ i j • nablaBasis ℤ n κ j = c i :=
    sum_coords_nablaBasis (hc i)
  -- Put `y` in for the variables `Y` of the coefficients.
  have hK_at_y : ∑ i, aeval y (c i) • nablaBasis R n κ i = weylKernel n κ y := by
    simpa [A, K, map_weylKernel, ← C_mul', comp_def] using congrArg (mapAlgHom (aeval y)) hK
  have hc_at_y (i : WeylIndexFamily n κ) :
      aeval y (c i) = (weylGramOver *ᵥ weylEval n κ y) i := by
    simp [← h_gram, ← eval_map, aeval_def, mulVec, dotProduct, weylEval]
  simp [← hK_at_y, hc_at_y, toPoly, linearCombination_apply]

/-- The Gram matrix `New.weylGram` does not depend on the labelling of the places: for a bijection
`p` from `Φ` to `Ψ`, the Gram matrix of `(n, κ)` is that of the data transported to `Ψ`, with rows
and columns reindexed along `p`. -/
lemma GL.weylGram_eq_submatrix {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (κ : Φ → ℕ → ℕ) (p : Φ ≃ Ψ) :
    weylGram n κ =
      (weylGram (fun σ : Ψ ↦ n (p.symm σ)) fun σ : Ψ ↦ κ (p.symm σ)).submatrix
        (p.piCongrLeft' fun τ : Φ ↦ BasisTableau (n τ) (rankAt n τ) (κ τ))
        (p.piCongrLeft' fun τ : Φ ↦ BasisTableau (n τ) (rankAt n τ) (κ τ)) := by
  -- Compare the two matrices on the vectors `weylEval n κ y`, through the injective
  -- `nablaCombination κ`. For `Φ` this gives the kernel at `y` (`toPoly_weylEval`); for `Ψ` the
  -- same after renaming the variables.
  let e : (Σ σ, n (p.symm σ)) × ℕ → (Σ τ, n τ) × ℕ := Prod.map p.symm.sigmaCongrLeft id
  -- Renaming the variables by `e` sends each basis product for `Ψ` to the one for `Φ`.
  have h_basis (i : WeylIndexFamily (fun σ ↦ n (p.symm σ)) fun σ ↦ κ (p.symm σ)) :
      rename e (nablaBasis ℤ (fun σ ↦ n (p.symm σ)) (fun σ ↦ κ (p.symm σ)) i) =
        nablaBasis ℤ n κ
          ((p.piCongrLeft' fun τ ↦ BasisTableau (n τ) (rankAt n τ) (κ τ)).symm i) := by
    simp [nablaBasis, tableauPoly, minor, e, AlgHom.map_det, Matrix.map, reindex_equiv p.symm]
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  refine nablaCombination_injective ((toPoly_weylEval y).trans ?_)
  have h_eval (i : WeylIndexFamily (fun σ ↦ n (p.symm σ)) fun σ ↦ κ (p.symm σ)) :
      eval (y ∘ e) (nablaBasis ℤ (fun σ ↦ n (p.symm σ)) (fun σ ↦ κ (p.symm σ)) i) =
        eval y (nablaBasis ℤ n κ
          ((p.piCongrLeft' fun τ ↦ BasisTableau (n τ) (rankAt n τ) (κ τ)).symm i)) := by
    rw [← eval_rename, h_basis]
  have h := congrArg (rename (R := ℤ) e)
    (toPoly_weylEval (κ := fun σ ↦ κ (p.symm σ)) (y ∘ e)).symm
  simp [toPoly, rowSubst, e, weylKernel, highestPoly, reindex_equiv p.symm,
    reindex_equiv (p.piCongrLeft' _).symm, tableauPoly, minor, AlgHom.map_det, Matrix.map,
    linearCombination_apply, mulVec, dotProduct, weylEval, h_basis, h_eval] at h ⊢
  exact h

@[simp]
lemma map_toPoly : MvPolynomial.map φ (toPoly n κ ξ) = toPoly n κ (φ ∘ ξ) := by
  simp [toPoly, ← C_mul', linearCombination_apply, mulVec, dotProduct]

/-! ### The form restricted from tensors -/

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- The kernel at `y` is the pairing of the tensor of `y` with the tensor of the variables. -/
lemma weylKernel_eq_sum_fillingPoly (y : (Σ τ : Φ, n τ) × ℕ → R) :
    weylKernel n κ y = ∑ T : ColumnFilling n κ, eval y (fillingPoly R T) • fillingPoly R T := by
  -- the Cauchy–Binet formula for one leading minor of `yᵀ x`
  let m (τ : Φ) (h : ℕ) (I : IncreasingMap (rankAt n τ) h) : MatrixPoly (Σ τ : Φ, n τ) R :=
    minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘ I.val)
  have hminor (τ : Φ) (h : ℕ) :
      (of fun s t : Fin h ↦ ∑ a : n τ, y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det =
        ∑ I : IncreasingMap (rankAt n τ) h, eval y (m τ h I) • m τ h I := by
    refine (det_sum_smul_X τ (of fun s a ↦ y (⟨τ, a⟩, s))).trans (sum_congr rfl fun I _ ↦ ?_)
    rw [← det_transpose]
    simp only [m, minor, RingHom.map_det]
    congr 2
    exact Matrix.ext fun s t ↦ by simp
  simp_rw [weylKernel, rowSubst_highestPoly, prod_range, ← Fin.prod_const, hminor, Fintype.prod_sum]
  refine sum_congr rfl fun T _ ↦ ?_
  simp [prod_smul, fillingPoly, tableauPoly, m, fillingRows, comp_def]

/-- Let F = `fillingMatrix n κ` be the integral matrix of the embedding of the Weyl module into
tensors, whose row `T` holds the coordinates of the product of minors of `T` in the standard basis.
Then FᵀF = `weylGram n κ`: the Gram matrix is that of the form on tensors for which the basis
tensors are orthonormal, restricted to the Weyl module. -/
lemma fillingMatrix_transpose_mul_self :
    (fillingMatrix n κ)ᵀ * fillingMatrix n κ = weylGram n κ := by
  -- Compare the polynomials of both matrices applied to an evaluation vector: each is the kernel.
  refine toLin'.injective
    (ext_weylEval 0 (fun y _ _ ↦ nablaCombination_injective ?_) Set.infinite_univ)
  have h_int : weylGramOver (R := ℤ) = weylGram n κ := Matrix.ext fun i j ↦ by simp
  have h_gram : nablaCombination κ (weylGram n κ *ᵥ weylEval n κ y) = weylKernel n κ y := by
    rw [← h_int, nablaCombination_weylGramOver_mulVec, toPoly_weylEval]
  rw [toLin'_apply, toLin'_apply, h_gram, weylKernel_eq_sum_fillingPoly, ← mulVec_mulVec,
    ← fillingMatrixOver_int, nablaCombination_transpose_mulVec]
  simp only [fillingMatrixOver_mulVec_weylEval]

/-- The Gram matrix `weylGramOver` over `R`, which is the integer matrix `New.weylGram` mapped into
`R`, equals FᵀF. Here F = `fillingMatrixOver R n κ` is the integer matrix `fillingMatrix` mapped
into `R`. Thus the Gram matrix is that of the form restricted from tensors. -/
lemma weylGramOver_eq_transpose_mul :
    (weylGramOver : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R) =
      (fillingMatrixOver R n κ)ᵀ * fillingMatrixOver R n κ := by
  rw [weylGramOver, ← fillingMatrix_transpose_mul_self]
  exact Matrix.map_mul (f := Int.castRingHom R)

/-- The integer Gram matrix `weylGram n κ` is symmetric. Its entries are the chosen coefficients of
the generic kernel `weylKernel n κ` in the products b_i(x) b_j(y) of the basis minor products
b = `nablaBasis`, indexed by `WeylIndexFamily n κ`. -/
lemma weylGram_isSymm : (weylGram n κ).IsSymm := by
  rw [← fillingMatrix_transpose_mul_self, IsSymm, transpose_mul, transpose_transpose]

/-- The Gram matrix `weylGram n κ` of the Weyl module, indexed by `WeylIndexFamily n κ` and with
entries mapped into `ℂ` (`weylGramOver`), is positive definite. It is the Gram matrix of the
restriction to the Weyl module of the form on tensors for which the standard basis tensors are
orthonormal (see `fillingMatrix_transpose_mul_self`). -/
lemma weylGramOver_posDef :
    (weylGramOver : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ).PosDef := by
  -- The form is restricted from tensors along a real matrix `F` with a left inverse.
  let F : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) ℂ := fillingMatrixOver ℂ n κ
  obtain ⟨Q, hQ⟩ := exists_fillingMatrix_leftInverse (n := n) (κ := κ)
  have h_left : Q.map (Int.cast : ℤ → ℂ) * F = 1 :=
    (Matrix.map_mul (f := Int.castRingHom ℂ)).symm.trans (by simp [hQ])
  have h_inj : Injective F.mulVec := LeftInverse.injective (g := (Q.map Int.cast).mulVec) fun ξ ↦ by
    rw [mulVec_mulVec, h_left, one_mulVec]
  have h_real : Fᵀ = Fᴴ := Matrix.ext fun i T ↦ by simp [F]
  rw [weylGramOver_eq_transpose_mul, h_real]
  exact PosDef.conjTranspose_mul_self F h_inj

/-- For a family `g` of square matrices `g τ`, let `G = weylGramOver` be the integer Gram matrix
`New.weylGram` for rows `n` and column counts `κ`, mapped into `R` and indexed by
`WeylIndexFamily n κ`. Let `schur κ g` be the Schur matrix S_κ(g) of `g` acting on the Weyl module.
Then G·S_κ(g) = S_κ(gᵀ)ᵀ·G, so the Schur matrices of `g` and of the transposes `(g τ)ᵀ` are adjoint
for the form with Gram matrix G. -/
lemma weylGramOver_mul_schur :
    weylGramOver * schur κ g = (schur κ fun τ : Φ ↦ (g τ)ᵀ)ᵀ * weylGramOver := by
  -- Adjointness is inherited from the action on tensors.
  let F : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) R := fillingMatrixOver R n κ
  calc weylGramOver * schur κ g
    _ = Fᵀ * (minorsMatrix κ g * F) := by
      rw [weylGramOver_eq_transpose_mul, Matrix.mul_assoc, fillingMatrixOver_mul_schur]
    _ = (minorsMatrix κ (fun τ : Φ ↦ (g τ)ᵀ) * F)ᵀ * F := by
      rw [minorsMatrix_transpose, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    _ = (schur κ fun τ : Φ ↦ (g τ)ᵀ)ᵀ * weylGramOver := by
      rw [← fillingMatrixOver_mul_schur, transpose_mul, weylGramOver_eq_transpose_mul,
        Matrix.mul_assoc]

/-! ### Schur matrices and substitution -/

/-- If the ranks fit `κ`, then `c ᵥ* S_κ(z) = x` if and only if the substitution `y ↦ z y` sends
`Σ_i c_i b'_i` to `(Σ_j x_j b_j) · ∏_τ det(y_τ)^{d_τ}`, with `d = New.schurDetExp n n' κ`. -/
lemma GL.vecMul_schur_eq_iff (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    {c : WeylIndexFamily n' κ → R} {x : WeylIndexFamily n κ → R} :
    c ᵥ* schur κ z = x ↔
      rowSubst z (nablaCombination κ c) =
        nablaCombination κ x * detPow R n (schurDetExp n n' κ) := by
  have h_subst : rowSubst z (nablaCombination κ c) =
      nablaCombination κ (c ᵥ* schur κ z) * detPow R n (schurDetExp n n' κ) := by
    simp [← sum_schur_smul_nablaBasis h_fits, vecMul_eq_sum, sum_mul, linearCombination_apply]
  -- The determinant factor cancels, and `nablaCombination κ` is injective.
  rw [h_subst, isRegular_detPow.right.eq_iff, nablaCombination_injective.eq_iff]

/-- Let `R` be a domain of characteristic zero, and assume `FitsRanks n n' κ`: at each place τ,
|n_τ| ≤ |n'_τ| and `κ τ h = 0` for |n_τ| < h < |n'_τ|. For a family `z τ` of `n' τ × n τ` matrices
and a Weyl module vector ξ, the polynomial `toPoly n' κ` of S_κ(z)ξ, where S_κ(z) = `schur κ z` is
the Schur matrix, is x ↦ (ξ̂·D)(zᵀx). Here ξ̂ = `toPoly n κ ξ` = Σ_i (Gξ)_i b_i (G the Gram matrix,
b_i the basis minor products), and D = ∏_τ det_τ^{d_τ}, with det_τ the determinant of the variables
in block τ and its first |n_τ| columns. The exponent is d_τ = `schurDetExp n n' κ τ`, equal to
`κ τ |n_τ|` if |n_τ| < |n'_τ| and 0 otherwise. -/
@[simp]
lemma toPoly_schur (h_fits : FitsRanks n n' κ) [IsDomain R] [CharZero R]
    (z : (τ : Φ) → Matrix (n' τ) (n τ) R) (ξ : WeylIndexFamily n κ → R) :
    toPoly n' κ (schur κ z *ᵥ ξ) =
      rowSubst (fun τ : Φ ↦ (z τ)ᵀ) (toPoly n κ ξ * detPow R n (schurDetExp n n' κ)) := by
  -- Both sides are linear in `ξ`, so by `ext_weylEval` take `ξ = ev_y` with `D y ≠ 0`, and multiply
  -- by `D y`: the left side becomes the kernel at `z y`, that is `highestPoly` of rank `n'` at
  -- `yᵀ zᵀ x`.
  let D : MatrixPoly (Σ τ : Φ, n τ) R := detPow R n (schurDetExp n n' κ)
  -- The minors of `yᵀ x` of size below `rankAt n τ` give the kernel in rank `n`, the minor of size
  -- `rankAt n τ` is `det y * det x`, and the larger ones have exponent `0` by `h_fits`.
  have h_minors (y : (Σ τ : Φ, n τ) × ℕ → R) :
      ∏ τ : Φ, ∏ k ∈ range (rankAt n' τ),
        (of fun s t : Fin k ↦ ∑ a : n τ, y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det ^ κ τ k =
      D.eval y • (weylKernel n κ y * D) := by
    simp only [D, smul_eq_C_mul, detPow, minor, map_prod, map_pow, RingHom.map_det, weylKernel,
      rowSubst_highestPoly, ← prod_mul_distrib]
    congr with τ
    -- split the product at `k = rankAt n τ`; the factors after that one are `1`
    rw [← prod_range_mul_prod_Ico _ (h_fits τ).1, schurDetExp, mul_left_comm, ← mul_pow,
      (Ico ..).prod_eq_ite (rankAt n τ) (by simp_all [FitsRanks, Ne.lt_of_le']),
      ← (C.mapMatrix _).det_transpose, ← det_mul]
    simp [-det_mul, ← (equivFin (n τ)).symm.sum_comp, Matrix.map]
    rfl
  suffices h_lin : toPoly n' κ ∘ₗ toLin' (schur κ z) =
      (rowSubst fun τ ↦ (z τ)ᵀ).toLinearMap ∘ₗ LinearMap.mulRight R D ∘ₗ toPoly n κ from
    LinearMap.congr_fun h_lin ξ
  refine ext_weylEval (schurDetExp n n' κ) (fun y _ (hy : D.eval y ≠ 0) ↦ ?_) Set.infinite_univ
  change toPoly n' κ (schur κ z *ᵥ weylEval n κ y) =
    rowSubst (fun τ ↦ (z τ)ᵀ) (toPoly n κ (weylEval n κ y) * D)
  rw [← smul_right_inj hy, ← map_smul, ← map_smul, schur_mulVec_weylEval h_fits, toPoly_weylEval,
    toPoly_weylEval, ← h_minors, ← rowSubst_highestPoly, rowSubst_rowSubst, weylKernel]
  simp [mul_comm (z ..)]
  rfl

variable [IsDomain R] [CharZero R]

/-- Over a domain of characteristic zero, the map sending a coordinate vector ξ to the
polynomial ∑ (Gξ)_i b_i, G the Gram matrix, is injective. -/
lemma toPoly_injective : Function.Injective (toPoly (R := R) n κ) := by
  -- The integer `det G` is not zero, since `G` is positive definite over `ℂ`.
  have h_int : (weylGram n κ).det ≠ 0 := by
    simpa [weylGramOver, ← Int.cast_det] using (weylGramOver_posDef (n := n) (κ := κ)).det_pos.ne'
  have h_det : (weylGramOver : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R).det ≠ 0 := by
    rwa [weylGramOver, ← Int.cast_det, Int.cast_ne_zero]
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦
    eq_zero_of_mulVec_eq_zero h_det (nablaCombination_injective ?_)
  rw [nablaCombination_weylGramOver_mulVec, hξ, map_zero]

/-- Let `toPoly n κ` be the map on the Weyl module `WeylIndexFamily n κ → ℂ` sending ξ to Σ_i (Gξ)_i
b_i. Here G is the Gram matrix `weylGramOver` (the integer matrix `New.weylGram` mapped into ℂ), and
b_i = `nablaBasis ℂ n κ i` are the basis minor products. Over ℂ, its range is exactly the module
`New.nablaFamily ℂ n κ` of Borel semi-invariant polynomials of the weight given by κ. -/
lemma range_toPoly : (toPoly n κ).range = nablaFamily ℂ n κ :=
  -- The Gram matrix is invertible, so the range is that of `nablaCombination κ`, the span of the
  -- basis.
  ((toLinearEquiv' _ weylGramOver_posDef.isUnit.invertible).range_comp _).trans
    range_nablaCombination

end New

end Gram

/-!
## Zariski density of the unitary group and Schur's lemma

`New.weylEval n κ y` is the vector of the values at the array `y` of the basis minor products.
-/

section SchurLemma

namespace New

open MvPolynomial Matrix «GL» RingHom Function

variable {Φ : Type} {K : Type _} [Field K] [CharZero K] [Fintype Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] {κ : Φ → ℕ → ℕ}

section Density

open Complex Norms.L2Operator NormedSpace ComplexStarModule

/-- For a complex polynomial P in the entries of a family of square matrices, its value
`evalMatrix g P` at the family `g` is an entire function of `g`. -/
lemma GL.analyticOnNhd_evalMatrix {P : MvPolynomial ((τ : Φ) × n τ × n τ) ℂ} :
    AnalyticOnNhd ℂ (fun g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ ↦ evalMatrix g P) ⊤ :=
  -- `evalMatrix g P` is `P` evaluated at the entries of `g`, which are linear functions of `g`.
  .eval_linearMap ⟨⟨_, by tauto⟩, by tauto⟩ P

/-- The unitary group is Zariski dense. Let P be a complex polynomial in the entries of a family
of square matrices `g τ`, and write `evalMatrix g P` for its value at `g`. If P vanishes at every
family of unitary matrices (`(g τ)ᴴ * g τ = 1` for all τ), then it vanishes at every family x. -/
lemma GL.zariski_dense_unitary (x : (τ : Φ) → Matrix (n τ) (n τ) ℂ)
    (P : MvPolynomial ((τ : Φ) × n τ × n τ) ℂ)
    (hP : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᴴ * g τ = 1) → evalMatrix g P = 0) :
    evalMatrix x P = 0 := by
  -- `P` is entire and `exp` is a submersion at `0`, so it is enough that `P` vanish at each
  -- `exp y`.
  -- The entire function `s ↦ P (exp (I • (s • -ℜ y + ℑ y)))` vanishes for real `s`, where the
  -- exponential is unitary, hence everywhere; and at `s = I` the exponent is `y`.
  refine eq_zero_of_submersion analyticOnNhd_evalMatrix hasStrictFDerivAt_exp_zero (by bound)
    (.of_forall fun y ↦ ?_) x
  let path (s : ℂ) : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ := I • (s • (-ℜ y).val + ℑ y)
  have h_entire : AnalyticOnNhd ℂ (fun s : ℂ ↦ evalMatrix (NormedSpace.exp (path s)) P) Set.univ :=
    analyticOnNhd_evalMatrix.comp (fun _ _ ↦ .comp (exp_analytic _) (f := path) (by fun_prop))
      (by simp)
  have h_real (t : ℝ) : evalMatrix (NormedSpace.exp (path t)) P = 0 := by
    -- at real `s` the exponent is skew-adjoint, so its exponential is unitary
    have h_unitary : star (NormedSpace.exp (path t)) * NormedSpace.exp (path t) = 1 :=
      Unitary.star_mul_self_of_mem (selfAdjoint.expUnitary (t • -ℜ y + ℑ y)).prop
    exact hP _ (congrFun h_unitary)
  -- The real points accumulate at `0`, so the identity theorem applies.
  have h_zero : (fun s : ℂ ↦ evalMatrix (NormedSpace.exp (path s)) P) = fun _ ↦ 0 :=
    h_entire.eq_of_frequently_eq analyticOnNhd_const
      (((hasDerivAt_id 0).ofReal_comp.tendsto_nhdsNE one_ne_zero).frequently (.of_forall h_real))
  have h_path_I : path I = y := by simp [path, smul_smul, realPart_add_I_smul_imaginaryPart]
  simpa [h_path_I] using congrFun h_zero I

end Density

variable [DecidableEq Φ]

/-- Over a field `K` of characteristic zero, let `v₀` be the frame vector of the enumerations `e`,
the evaluation vector at the permutation array of `e`. Two linear maps that agree on
`schur κ g *ᵥ v₀` for all tuples `g` of invertible matrices are equal.

So the translates of the frame vector under the product of general linear groups span the module.
The reason is duality: they are the evaluation vectors at invertible arrays, and a polynomial that
vanishes on invertible matrices is zero.

In other words, the frame vector is cyclic for the product of the general linear groups. -/
lemma GL.ext_schur_weylEval (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    {M : Type*} [AddCommGroup M] [Module K M] {L L' : (WeylIndexFamily n κ → K) →ₗ[K] M}
    (h_agree : ∀ g : ∀ τ : Φ, GL (n τ) K,
      L (schur κ (fun τ : Φ ↦ (g τ).val) *ᵥ
          weylEval n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ))) =
        L' (schur κ (fun τ : Φ ↦ (g τ).val) *ᵥ
          weylEval n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)))) : L = L' := by
  -- By `ext_weylEval` it suffices to treat the vectors `weylEval n κ y` with `detPow K n 1`, the
  -- product of the determinants of the square blocks, non-zero at `y`. Such a vector is
  -- `schur κ g` applied to the frame vector, with `g = squarePart e y` invertible.
  refine ext_weylEval 1 (fun y _ hy ↦ ?_) Set.infinite_univ
  have h_unit (τ : Φ) : IsUnit (squarePart e y τ) := by
    -- After renumbering rows and columns, its determinant is the factor of `detPow` at `τ`.
    apply (isUnit_submatrix_equiv (rowEquivFin n τ).symm (e τ).symm).1
    simp_all [squarePart, detPow, minor, det_apply, isUnit_iff_isUnit_det, Finset.prod_eq_zero_iff]
  rw [← schur_squarePart_mulVec e y]
  exact h_agree fun τ ↦ (h_unit τ).unit

/-- Schur's lemma for the unitary group: a complex matrix `T` that commutes with `schur κ g` for
every tuple `g` of unitary matrices is a scalar matrix.

A form of Weyl's theorem on irreducibility of the complex Schur module: the commutant of the Schur
matrices of all tuples of unitary matrices consists of scalars. -/
lemma mem_range_scalar_of_commute_schur {T : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ}
    (hT : ∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ,
      (∀ τ : Φ, (g τ)ᴴ * g τ = 1) → Commute T (schur κ g)) :
    T ∈ Set.range (scalar (WeylIndexFamily n κ)) := by
  classical
  -- The frame vector `v` spans the highest weight space, which `T` preserves, so `T v = c • v`.
  -- The translates of `v` are then eigenvectors for the same `c`, and they span the whole space.
  let v : WeylIndexFamily n κ → ℂ := weylEval n κ (permArray fun τ i ↦ (rowEquivFin n τ i : ℕ))
  -- The entries of the commutator are polynomials in `g`, and unitary tuples are Zariski dense.
  have h_comm (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      schur κ g *ᵥ T *ᵥ v = T *ᵥ schur κ g *ᵥ v := by
    ext i
    simpa +contextual [Ring.lie_def, ↓map_mulVec, Matrix.map_sub, (hT ..).eq, comp_def,
      ← mulVec_mulVec, sub_eq_zero, sub_mulVec] using!
      zariski_dense_unitary (n := n) g ((⁅schur κ (genericMatrixAt ℂ n), T.map C⁆ *ᵥ C ∘ v) i)
  -- The diagonal tuple `D` with `2` at `(τ, a)` and `1` elsewhere scales coordinate `i` by
  -- `2 ^ tableauWeight i τ a`, and `v`, hence `T v`, by `2` to the highest weight.
  have h_weight (i : WeylIndexFamily n κ) (hi : (T *ᵥ v) i ≠ 0) (τ : Φ) (a : n τ) :
      tableauWeight i τ a = diagramWeight (rankAt n) κ (τ, rowEquivFin n τ a) := by
    let D (σ : Φ) : Matrix (n σ) (n σ) ℂ := diagonal fun b ↦ if σ = τ ∧ b ≍ a then 2 else 1
    let m : ℕ := diagramWeight (rankAt n) κ (τ, rowEquivFin n τ a)
    have hD : schur κ D *ᵥ v = (2 : ℂ) ^ m • v := toPoly_injective (by
      simp [v, D, m, rowSubst_weylKernel_permArray, ite_and, blockTriangular_diagonal])
    have h_norm : ‖(schur κ D *ᵥ T *ᵥ v) i‖ = ‖(T *ᵥ (2 : ℂ) ^ m • v) i‖ := by rw [h_comm, hD]
    simp_all [D, m, schur_diagonal, ite_and, mulVec_diagonal, mulVec_smul]
  -- As the `b_i` are independent, a linear form `φ` on polynomials has the values `(T v)_i` on
  -- them. It sees only the highest weight, so on the `b_i` it is `c` times evaluation at the frame.
  obtain ⟨L, hL⟩ : ∃ L : MatrixPoly (Σ τ : Φ, n τ) ℂ →ₗ[ℂ] WeylIndexFamily n κ → ℂ,
      L ∘ₗ nablaCombination κ = .id :=
    LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 nablaCombination_injective)
  let φ : MatrixPoly (Σ τ : Φ, n τ) ℂ →ₗ[ℂ] ℂ := dotProductBilin ℂ ℂ (T *ᵥ v) ∘ₗ L
  have hφ (i : WeylIndexFamily n κ) : φ (nablaBasis ℂ n κ i) = (T *ᵥ v) i := by
    simpa [φ] using congrArg (dotProduct (T *ᵥ v)) (LinearMap.congr_fun hL (Pi.single i 1))
  let c : ℂ := φ (weylKernel n κ (permArray fun τ i ↦ (rowEquivFin n τ i : ℕ)))
  have h_eigen : T *ᵥ v = c • v := by
    ext i
    rw [← hφ]
    exact map_nablaBasis_eq_map_weylKernel_mul_weylEval (rowEquivFin n) i φ fun hi τ a ↦
      (h_weight i (by rwa [← hφ]) τ a).ge
  have h_translate (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      T *ᵥ schur κ g *ᵥ v = c • schur κ g *ᵥ v := by rw [← h_comm, h_eigen, mulVec_smul]
  refine ⟨c, toLin'.injective (ext_schur_weylEval (rowEquivFin n) fun g ↦ ?_)⟩
  simpa [v, ← mulVec_mulVec] using (h_translate fun τ ↦ (g τ).val).symm

end New

end SchurLemma
end
end

/-!
# Fock pairing, Hermitian norm and Cartan products for the Gram matrix of the Weyl kernel

This file uses the Fock pairing `⟨P, Q⟩ = P(∂) Q (0)` (`New.fockPairing`) and Schur's lemma to show
that the Gram matrix `G = New.weylGram` times the matrix of the Fock pairings of the basis
`b_i = New.nablaBasis` (products of minors) of the semi-invariants `New.nablaFamily` is the hook
number `New.hookNumber κ N = ⟨f, f⟩`, the Fock pairing of `f = New.highestPoly` with itself.
It treats weights with one row at each place. It defines the squared
norm `New.weylNormSq ξ = re (ξ* G ξ)` and builds a tight frame of integral vectors. It shows that
this norm is submultiplicative under Cartan multiplication of polynomials of weights `κ` and `κ'`,
and defines the products of determinants `New.pairedDetProd`.

## Main definitions and results

* `New.weylGram_mul_fockPairing`, `New.fockPairing_toPoly_nablaBasis`: by Schur's lemma, `G` times
  the matrix of the Fock pairings `⟨b_i, b_j⟩` is the hook number `New.hookNumber`.
* `New.GL.comulMatrix`: the matrix `C`, in the bases `New.nablaBasis`, of multiplication of
  polynomials of weights `κ` and `κ'` into those of weight `κ + κ'`;
  `New.GL.vecMul_comulMatrix_eq_iff`: acting on row vectors, `C` multiplies polynomials;
  `New.GL.comulMatrix_mulVec_weylEval`: acting on columns, it sends an evaluation vector to a tensor
  product of two.
* `New.GL.comulMatrix_isometry`, `New.GL.comulMatrix_equivariant`, `New.GL.hasLeftInv_comulMatrix`:
  `C` is an isometry for the Gram matrices, intertwines the Schur matrices, and has a left inverse
  over `ℤ`.

Notions from other files:
* `New.WeylIndexFamily n κ`: families that choose, for each place `τ`, a standard filling with rows
  `n τ`; they index the basis `b_i`.
* `New.schur κ z`: the Schur matrix `S_κ(z)` of matrices `z τ` of size `n' τ × n τ`. Row `i`
  holds the coordinates of `b'_i(z y)` in the products `b_j(y) · ∏_τ det(y_τ)^{d_τ}`, where `b'` is
  the basis for the rows `n'` and `d = New.schurDetExp n n' κ`.
* `New.mem_range_scalar_of_commute_schur` (`Lib.GLn.SchurModule.WeylKernel`): Schur's lemma, a
  matrix that commutes with `New.schur κ g` for all unitary `g` is scalar.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.SchurNorm` and `Lib.GLn.Dual` for sources.
-/

@[expose] public section

/-!
## The Fock form and the Gram matrix

A vector `ξ` pairs with a polynomial `P = ∑ c_k b_k` in two ways, by `ξ(P) = ∑ ξ_k c_k` and by the
Fock pairing `⟨ξ̂, P⟩` with `ξ̂ = New.toPoly n κ ξ`. By Schur's lemma the two are proportional, and
the factor is the hook number.
-/

section FockForm

namespace New

open MvPolynomial «GL» Fintype Finset Matrix

variable {Φ : Type} {R : Type _} [CommRing R] [Fintype Φ] [DecidableEq Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] {κ : Φ → ℕ → ℕ}
  (ξ η : WeylIndexFamily n κ → R)

/-- The Fock pairing of the polynomial Σ_i (Gξ)_i b_i attached to ξ with b_k is the coordinate k of
HᵀGξ, where G is the Gram matrix and H the integer matrix of the Fock pairings ⟨b_i, b_j⟩. -/
lemma fockPairing_toPoly_nablaBasis_eq_mulVec (k : WeylIndexFamily n κ) :
    fockPairing R (toPoly n κ ξ) (nablaBasis R n κ k) =
      (((of fun i j : WeylIndexFamily n κ ↦
          fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j))ᵀ * weylGram n κ).map
        (Int.cast : ℤ → R) *ᵥ ξ) k := by
  have h_entry (i : WeylIndexFamily n κ) :
      (fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ k) : R) =
        fockPairing R (nablaBasis R n κ i) (nablaBasis R n κ k) := by
    simpa using map_fockPairing (Int.castRingHom R) (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ k)
  rw [map_mul_intCast, ← mulVec_mulVec, ← nablaCombination_weylGramOver_mulVec]
  simp [Fintype.linearCombination_apply, mulVec.eq_1 _ (weylGramOver *ᵥ ξ), dotProduct, h_entry,
    mul_comm]

omit [DecidableEq Φ] in
/-- The kernel at the permutation array of the row numbering `rowEquivFin` is the product of the
leading minors with the rows renamed, so its Fock pairing with itself is the hook number. -/
lemma fockPairing_weylKernel_permArray_self :
    fockPairing R (weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ)))
        (weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      hookNumber κ (rankAt n) := by
  let p (τ : Φ) : Matrix (Fin (rankAt n τ)) (n τ) R :=
    of fun i a ↦ permArray (fun (σ : Φ) (b : n σ) ↦ (rowEquivFin n σ b : ℕ)) (⟨τ, a⟩, i)
  have h_orth (τ : Φ) : p τ * (p τ)ᵀ = 1 := by
    ext i j
    rw [Matrix.mul_apply, ← (rowEquivFin n τ).symm.sum_comp]
    simp [p, permArray, Fin.val_inj, Matrix.one_apply, eq_comm]
  let f : MatrixPoly (Σ τ : Φ, Fin (rankAt n τ)) R := highestPoly R κ (rankAt n)
  calc fockPairing R (rowSubst p f) (rowSubst p f)
    _ = fockPairing R f f := by
      simp only [fockPairing_rowSubst p, rowSubst_rowSubst, h_orth, rowSubst_one]
    _ = hookNumber κ (rankAt n) := by
      simpa [f, hookNumber] using (map_fockPairing (Int.castRingHom R) (highestPoly ℤ κ (rankAt n))
        (highestPoly ℤ κ (rankAt n))).symm

/-- The Gram matrix `weylGram n κ` has as entries the integer coefficients of the generic kernel
`weylKernel` in the products b_i(x)·b_j(y), where b = `nablaBasis` are the basis minor products. It
times the matrix of Fock pairings ⟨b_i,b_j⟩ = b_i(∂)b_j(0) equals the hook number
`hookNumber κ (rankAt n)` times the identity matrix. -/
lemma weylGram_mul_fockPairing :
    (weylGram n κ * of fun i j : WeylIndexFamily n κ ↦
        fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)) =
      hookNumber κ (rankAt n) • 1 := by
  -- Over `ℂ` let `T` be the map with `⟨ξ̂, P⟩ = (T ξ)(P)`. Both pairings make the Schur matrix of
  -- `g` adjoint to the substitution `P ↦ P(g ·)`, so `T` commutes with it and is a scalar `c`.
  let H : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℤ :=
    of fun i j : WeylIndexFamily n κ ↦ fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)
  let T : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ := (Hᵀ * weylGram n κ).map Int.cast
  have hT (ξ : WeylIndexFamily n κ → ℂ) (k : WeylIndexFamily n κ) :
      (T *ᵥ ξ) k = fockPairing ℂ (toPoly n κ ξ) (nablaBasis ℂ n κ k) :=
    (fockPairing_toPoly_nablaBasis_eq_mulVec ξ k).symm
  have h_comm (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) : T * schur κ g = schur κ g * T := by
    refine ext_iff_mulVec.2 fun ξ ↦ funext fun k ↦ ?_
    have h_expand : rowSubst g (nablaBasis ℂ n κ k) =
        ∑ j : WeylIndexFamily n κ, schur κ g k j • nablaBasis ℂ n κ j := by
      simp [← sum_schur_smul_nablaBasis FitsRanks.refl, detPow]
    calc ((T * schur κ g) *ᵥ ξ) k
      _ = fockPairing ℂ (rowSubst (fun τ : Φ ↦ (g τ)ᵀ) (toPoly n κ ξ)) (nablaBasis ℂ n κ k) := by
        simp [← mulVec_mulVec, hT, toPoly_schur FitsRanks.refl, detPow]
      _ = fockPairing ℂ (toPoly n κ ξ) (rowSubst g (nablaBasis ℂ n κ k)) :=
        fockPairing_rowSubst _ _ _
      _ = ((schur κ g * T) *ᵥ ξ) k := by
        simp [h_expand, ← hT, ← mulVec_mulVec, mulVec.eq_1 (schur κ g), dotProduct]
  obtain ⟨c, hc⟩ : T ∈ Set.range (scalar (WeylIndexFamily n κ)) :=
    mem_range_scalar_of_commute_schur fun g _ ↦ h_comm g
  -- The frame vector `v` has the polynomial `K` with `v(K) = 1` and `⟨K, K⟩` the hook number.
  let w : (Σ τ : Φ, n τ) × ℕ → ℂ := permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ)
  let v : WeylIndexFamily n κ → ℂ := weylEval n κ w
  have h_const : (hookNumber κ (rankAt n) : ℂ) = c :=
    calc (hookNumber κ (rankAt n) : ℂ)
      _ = fockPairing ℂ (toPoly n κ v) (nablaCombination κ (weylGramOver *ᵥ v)) := by
        rw [nablaCombination_weylGramOver_mulVec, toPoly_weylEval,
          fockPairing_weylKernel_permArray_self]
      _ = (T *ᵥ v) ⬝ᵥ weylGramOver *ᵥ v := by
        simp [Fintype.linearCombination_apply, hT, dotProduct, mul_comm]
      _ = c * eval w (weylKernel n κ w) := by
        rw [← toPoly_weylEval, eval_toPoly, ← hc]
        simp [v]
      _ = c := by rw [eval_weylKernel_permArray, mul_one]
  -- This is an identity of integer matrices; transpose it, using that `G` is symmetric.
  have h_int : Hᵀ * weylGram n κ = hookNumber κ (rankAt n) • 1 := by
    refine map_injective (Int.cast_injective (α := ℂ)) (hc.symm.trans ?_)
    simp [← h_const, Matrix.map_intCast, diagonal_intCast]
  simpa [weylGram_isSymm.eq] using congrArg transpose h_int

/-- Let ξ be a vector of the Weyl module `WeylIndexFamily n κ → R` over any commutative ring `R`,
and let `toPoly n κ ξ` be its polynomial Σ_i (Gξ)_i b_i. Here G is the Gram matrix `weylGramOver`
and b_i = `nablaBasis R n κ i` are the basis minor products. For each index k, the Fock pairing
⟨P,Q⟩ = P(∂)Q(0) of `toPoly n κ ξ` with b_k equals `hookNumber κ (rankAt n)` times the coordinate
ξ_k. -/
@[simp]
lemma fockPairing_toPoly_nablaBasis (k : WeylIndexFamily n κ) :
    fockPairing R (toPoly n κ ξ) (nablaBasis R n κ k) = hookNumber κ (rankAt n) * ξ k := by
  rw [fockPairing_toPoly_nablaBasis_eq_mulVec, ← weylGram_isSymm.eq, ← transpose_mul,
    weylGram_mul_fockPairing]
  simp [Matrix.map_intCast, mulVec_diagonal]

/-- For vectors ξ, η of the Weyl module over a commutative ring `R` (functions on
`WeylIndexFamily n κ`), the Fock pairing ⟨P,Q⟩ = P(∂)Q(0) of the polynomials
`toPoly n κ ξ = Σ_i (Gξ)_i b_i` and `toPoly n κ η` equals the hook number times ξᵀ G η. Here the b_i
are the basis products of minors `nablaBasis`, indexed by `WeylIndexFamily n κ`. G is the integer
Gram matrix `weylGram`, the coefficients of the generic kernel `weylKernel` in the products b_i(x)
b_j(y), mapped into `R`. The hook number is ⟨f,f⟩, where f is the product over places τ of the
leading principal h×h minors raised to κ_τ(h), for h < |n_τ|. -/
@[simp]
lemma fockPairing_toPoly_toPoly :
    fockPairing R (toPoly n κ ξ) (toPoly n κ η) =
      hookNumber κ (rankAt n) * ξ ⬝ᵥ weylGramOver *ᵥ η := by
  simp [← nablaCombination_weylGramOver_mulVec η, mul_rotate', linearCombination_apply, dotProduct,
    mul_sum]

/-- The orthogonal projection of an integral tensor `v` to the Weyl module becomes integral after
multiplication by the hook number: some integral vector has the same pairings with the Weyl module
as that multiple of `v`. -/
lemma exists_weylGram_mulVec_eq_hookNumber_smul (v : ColumnFilling n κ → ℤ) :
    ∃ η : WeylIndexFamily n κ → ℤ,
      weylGram n κ *ᵥ η = hookNumber κ (rankAt n) • ((fillingMatrix n κ)ᵀ *ᵥ v) := by
  -- The matrix of Fock pairings is the hook number times the inverse of the Gram matrix.
  refine ⟨(of fun i j ↦ fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)) *ᵥ
    (fillingMatrix n κ)ᵀ *ᵥ v, ?_⟩
  rw [mulVec_mulVec, weylGram_mul_fockPairing, smul_mulVec, one_mulVec]

end New

end FockForm

/-!
## Weights with one row at each place

If only columns of height one occur, with `κ τ 1` of them at `τ`, the basis polynomials are
monomials in the first columns `z_τ` of variables.
-/

section OneRow

namespace New

open MvPolynomial Finset Matrix Nat

variable {Φ R : Type} [Fintype Φ] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}

/-- The exponent of the monomial `∏ z_τ ^ α_τ`, where `z_τ` is the first column of variables at
`τ`. -/
noncomputable def firstColumnExponent (α : ∀ τ : Φ, n τ → ℕ) : ((τ : Φ) × n τ) × ℕ →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm fun x : (τ : Φ) × n τ ↦ α x.1 x.2).embDomain
    (Function.Embedding.sectL ((τ : Φ) × n τ) 0)

/-- A product over the exponent `firstColumnExponent α` runs over the variables in the first
columns. -/
lemma prod_firstColumnExponent {M : Type} [CommMonoid M] (α : ∀ τ : Φ, n τ → ℕ)
    (f : ((τ : Φ) × n τ) × ℕ → ℕ → M) (hf : ∀ x : ((τ : Φ) × n τ) × ℕ, f x 0 = 1) :
    (firstColumnExponent α).prod f = ∏ τ : Φ, ∏ b : n τ, f (⟨τ, b⟩, 0) (α τ b) := by
  rw [firstColumnExponent, Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ fun x ↦ hf _,
    Fintype.prod_sigma]
  rfl

variable [∀ τ : Φ, DecidableEq (n τ)]

/-- Suppose only columns of height at most one occur (`κ τ h = 0` for 1 < h < `N τ`). Then the
product over τ of the polynomials `tableauPoly` of the fillings `T τ` (products of minors on the
rows given by the columns' entries) is a monomial in the first column of variables at each τ. Its
exponent at (τ, b) is the number of height-one columns of `T τ` with entry b. -/
lemma prod_tableauPoly_one_row [CommRing R] {N : Φ → ℕ} (hN : ∀ τ : Φ, 1 < N τ)
    (hκ : ∀ (τ : Φ) (h : ℕ), 1 < h → h < N τ → κ τ h = 0)
    (T : ∀ τ : Φ, Tableau (n τ) (N τ) (κ τ)) :
    ∏ τ : Φ, tableauPoly (m := (τ : Φ) × n τ) R (Sigma.mk τ) (T τ) =
      monomial (firstColumnExponent fun τ b ↦ #{j | T τ ⟨1, hN τ⟩ j (0 : Fin 1) = b}) 1 := by
  rw [monomial_eq, C_1, one_mul, prod_firstColumnExponent _ _ fun x ↦ pow_zero _]
  refine prod_congr rfl fun τ _ ↦ ?_
  rw [tableauPoly, Fintype.prod_eq_single ⟨1, hN τ⟩]
  · -- A minor of size one is a variable; sort the columns of height one by their entry.
    simp [minor, ← prod_fiberwise' univ (fun j ↦ T τ ⟨1, hN τ⟩ j (0 : Fin 1))
      fun b ↦ (X (⟨τ, b⟩, 0) : MatrixPoly ((τ : Φ) × n τ) R)]
  · -- Minors of size zero are `1`, and there are no columns of height above one.
    rintro ⟨_ | _ | h, h_lt⟩ h_ne
    · simp [minor]
    · exact (h_ne rfl).elim
    · exact prod_eq_one fun j _ ↦ (Fin.cast (hκ τ (h + 2) (by omega) h_lt) j).elim0

/-- The hook number of a weight with one row at each place is the product of the factorials of the
row lengths. -/
lemma hookNumber_one_row [DecidableEq Φ] {N : Φ → ℕ} (hN : ∀ τ : Φ, 1 < N τ)
    (hκ : ∀ (τ : Φ) (h : ℕ), 1 < h → h < N τ → κ τ h = 0) :
    hookNumber κ N = (∏ τ : Φ, (κ τ 1)! : ℕ) := by
  rw [hookNumber, highestPoly, prod_tableauPoly_one_row hN hκ, fockPairing_monomial,
    prod_firstColumnExponent _ _ fun _ ↦ by simp, coeff_monomial, ite_eq_left rfl]
  simp only [mul_one, cast_prod]
  refine prod_congr rfl fun τ _ ↦ ?_
  rw [Fintype.prod_eq_single (Fin.castLE (hN τ).le 0) fun b hb ↦ by simp [hb.symm]]
  simp

variable [DecidableEq Φ] [Field R] [CharZero R]

end New

end OneRow

/-!
## The Hermitian norm

* `New.weylNormSq`: the squared norm `re (ξ* G ξ)` of a complex coordinate vector `ξ`.
* `New.GL.weylNormSq_weylEval_permArray`: the evaluation vector `New.weylEval` at the permutation
  array of enumerations of the rows has norm `1`.
* `New.GL.exists_tightFrame`: the hook number times the orthogonal projections of the basis tensors
  to the Weyl module form a tight frame of integral vectors; `New.GL.card_columnFilling_le` bounds
  the number of basis tensors.
-/

namespace New

open MvPolynomial Matrix Complex ComplexOrder

variable {Φ : Type} {R : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  {κ : Φ → ℕ → ℕ} (ξ : WeylIndexFamily n κ → ℂ)

/-- For a complex coordinate vector ξ, the real part of ξ* G ξ, where G is the integer Gram
matrix. It is the squared norm of ξ for the Hermitian form of G, which is positive definite. -/
noncomputable def weylNormSq : ℝ :=
  re (star ξ ⬝ᵥ (weylGram n κ).map (Int.cast : ℤ → ℂ) *ᵥ ξ)

@[simp]
lemma weylNormSq_nonneg : 0 ≤ weylNormSq ξ := weylGramOver_posDef.posSemidef.re_dotProduct_nonneg ξ

omit [(τ : Φ) → DecidableEq (n τ)] in
lemma weylNormSq_smul (t : ℂ) : weylNormSq (t • ξ) = ‖t‖ ^ 2 * weylNormSq ξ := by
  simp [weylNormSq, mulVec_smul, ← mul_assoc, mul_conj', sq]

omit [(τ : Φ) → DecidableEq (n τ)] in
/-- The squared Gram norm of `σ ∘ (t • ξ)` is `‖σ t‖ ^ 2` times that of `σ ∘ ξ`, for multiplicative
`σ`. -/
@[simp]
lemma weylNormSq_comp_smul {F : Type*} [FunLike F ℂ ℂ] [MulHomClass F ℂ ℂ] (σ : F) (t : ℂ) :
    weylNormSq (σ ∘ (t • ξ)) = ‖σ t‖ ^ 2 * weylNormSq (σ ∘ ξ) := by
  have h_comp : σ ∘ (t • ξ) = σ t • (σ ∘ ξ) := funext fun i ↦ map_mul σ t (ξ i)
  rw [h_comp, weylNormSq_smul]

namespace «GL»

/-- Cauchy–Schwarz for the Hermitian form of a positive definite complex matrix M:
`‖x* M y‖ ^ 2 ≤ re (y* M y) * re (x* M x)`. -/
lemma posDef_cauchy_schwarz {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (h_posDef : PosDef M)
    (x y : ι → ℂ) :
    ‖star x ⬝ᵥ M *ᵥ y‖ ^ 2 ≤ (star y ⬝ᵥ M *ᵥ y).re * (star x ⬝ᵥ M *ᵥ x).re := by
  -- the Cauchy–Schwarz inequality of the inner product `⟪u, v⟫ = u* M v` that `M` defines
  have h_cs := h_posDef.star_dotProduct_mulVec_mul_le x y
  rw [eq_re_of_ofReal_le (h_posDef.posSemidef.dotProduct_mulVec_nonneg x),
    eq_re_of_ofReal_le (h_posDef.posSemidef.dotProduct_mulVec_nonneg y)] at h_cs
  simpa [mul_conj', mul_comm, ← ofReal_pow, ← ofReal_mul, real_le_real] using h_cs

/-- As a complex number, the squared Gram norm `weylNormSq ξ` is `ξ* G ξ` itself: its imaginary part
is zero because G is positive semidefinite. -/
lemma coe_weylNormSq : weylNormSq ξ = star ξ ⬝ᵥ weylGramOver *ᵥ ξ :=
  (eq_re_of_ofReal_le (weylGramOver_posDef.posSemidef.dotProduct_mulVec_nonneg ξ)).symm

omit [DecidableEq Φ] in
/-- The complex conjugate of the evaluation vector at y (the values `b_i y` of the basis minor
products) is the evaluation vector at the conjugate array, since the `b_i` have integer
coefficients. -/
lemma star_weylEval (y : ((τ : Φ) × n τ) × ℕ → ℂ) :
    star (weylEval n κ y) = weylEval n κ (star y) := by
  ext i
  simp [weylEval, map_eval, Function.comp_def, Pi.star_def]

/-- For enumerations `e τ` of the rows, the evaluation vector at the permutation array of e (entry
1 at row `(τ, a)` and column `e τ a`, and 0 elsewhere) has Gram norm 1. -/
lemma weylNormSq_weylEval_permArray (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) :
    weylNormSq (weylEval n κ (permArray e)) = 1 := by
  -- The array `y = permArray e` is real, so the vector is its own conjugate; its Gram form is the
  -- kernel at `y` evaluated at `y`, which is `1`.
  set y : ((τ : Φ) × n τ) × ℕ → ℂ := permArray e with hy_def
  have h_star : star (weylEval n κ y) = weylEval n κ y := by
    rw [star_weylEval]
    congr 1
    ext x
    simp [hy_def, permArray, apply_ite]
  have h_form : star (weylEval n κ y) ⬝ᵥ weylGramOver *ᵥ weylEval n κ y = 1 := by
    rw [h_star, ← eval_toPoly, toPoly_weylEval]
    exact eval_weylKernel_permArray e
  change re (star (weylEval n κ y) ⬝ᵥ weylGramOver *ᵥ weylEval n κ y) = 1
  rw [h_form, one_re]

/-- A tight frame of integral vectors. Let `hk` be the hook number and `⟨ξ, ξ'⟩ = ξ* G ξ'` the form
of the Gram matrix. There are integral vectors `η T`, one for each basis tensor `T`
(`New.ColumnFilling`), with `∑ T, ⟨η T, ξ⟩ η T = hk² ξ` for all `ξ` and of norm at most `hk`. -/
lemma exists_tightFrame : ∃ η : ColumnFilling n κ → WeylIndexFamily n κ → ℤ,
    (∀ ξ : WeylIndexFamily n κ → ℂ,
      ∑ T : ColumnFilling n κ, (star (Int.cast ∘ η T) ⬝ᵥ weylGramOver *ᵥ ξ) • (Int.cast ∘ η T) =
        (hookNumber κ (rankAt n) : ℂ) ^ 2 • ξ) ∧
    ∀ T : ColumnFilling n κ,
      weylNormSq (Int.cast ∘ η T) ≤ (hookNumber κ (rankAt n) : ℝ) ^ 2 := by
  -- Take for `η T` the hook number times the orthogonal projection of `T` to the Weyl module.
  -- With `F` the embedding into tensors and `G = Fᵀ F`, this means `G (η T) = hk Fᵀ T`, so
  -- `⟨η T, ξ⟩` is `hk` times the coordinate `T` of the tensor `F ξ`.
  classical
  set hk : ℤ := hookNumber κ (rankAt n)
  let F : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) ℂ := fillingMatrixOver ℂ n κ
  have h_exists (T : ColumnFilling n κ) :
      ∃ η : WeylIndexFamily n κ → ℤ, weylGram n κ *ᵥ η = hk • fillingMatrix n κ T := by
    simpa [hk, row] using exists_weylGram_mulVec_eq_hookNumber_smul (Pi.single T 1)
  choose η hη using h_exists
  refine ⟨η, fun ξ ↦ ?_, fun T ↦ ?_⟩
  · have h_gram (T : ColumnFilling n κ) : weylGramOver *ᵥ (Int.cast ∘ η T) = (hk : ℂ) • F T := by
      funext i
      simpa [F, mulVec, dotProduct] using congrArg (Int.cast : ℤ → ℂ) (congrFun (hη T) i)
    have h_pair (T : ColumnFilling n κ) :
        star (Int.cast ∘ η T) ⬝ᵥ weylGramOver *ᵥ ξ = hk * F T ⬝ᵥ ξ := by
      have h_real : star (Int.cast ∘ η T : WeylIndexFamily n κ → ℂ) = Int.cast ∘ η T :=
        funext fun i ↦ by simp
      rw [h_real, dotProduct_mulVec, ← mulVec_transpose, (weylGram_isSymm.map _).eq, h_gram,
        smul_dotProduct, smul_eq_mul]
    refine mulVec_injective_iff_isUnit.2 weylGramOver_posDef.isUnit ?_
    calc weylGramOver *ᵥ ∑ T : ColumnFilling n κ,
          (star (Int.cast ∘ η T) ⬝ᵥ weylGramOver *ᵥ ξ) • (Int.cast ∘ η T : WeylIndexFamily n κ → ℂ)
      _ = ∑ T : ColumnFilling n κ, (hk * F T ⬝ᵥ ξ) • (hk : ℂ) • F T := by
        simp only [mulVec_sum, mulVec_smul, h_pair, h_gram]
      _ = (hk : ℂ) ^ 2 • Fᵀ *ᵥ F *ᵥ ξ := by
        rw [mulVec_transpose, vecMul_eq_sum, Finset.smul_sum]
        simp only [smul_smul, mul_right_comm (hk : ℂ), ← sq, mulVec]
      _ = weylGramOver *ᵥ ((hk : ℂ) ^ 2 • ξ) := by
        rw [mulVec_smul, mulVec_mulVec, ← weylGramOver_eq_transpose_mul]
  · -- The squared norm is `hk * w T` and also `w ⬝ᵥ w ≥ w T ^ 2`, for the tensor `w` of `η T`.
    let w : ColumnFilling n κ → ℤ := fillingMatrix n κ *ᵥ η T
    have h_coord : η T ⬝ᵥ weylGram n κ *ᵥ η T = hk * w T := by
      rw [hη, dotProduct_smul, smul_eq_mul, dotProduct_comm]
      rfl
    have h_sum : η T ⬝ᵥ weylGram n κ *ᵥ η T = w ⬝ᵥ w := by
      rw [← fillingMatrix_transpose_mul_self, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    have h_single : w T * w T ≤ w ⬝ᵥ w :=
      Finset.single_le_sum (fun S _ ↦ mul_self_nonneg (w S)) (Finset.mem_univ T)
    have h_le : η T ⬝ᵥ weylGram n κ *ᵥ η T ≤ hk ^ 2 := by linarith [sq_nonneg (hk - w T)]
    simpa [weylNormSq, dotProduct, mulVec] using (Int.cast_le (R := ℝ)).2 h_le

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- If all ranks are at most `t ≥ 1` and the diagrams have at most `L` boxes in total, there are at
most `t ^ L` basis tensors (`New.ColumnFilling`). -/
lemma card_columnFilling_le {t L : ℕ} (ht : 1 ≤ t) (h_rank : ∀ τ : Φ, rankAt n τ ≤ t)
    (h_degree : ∑ τ : Φ, ∑ h ∈ Finset.range (rankAt n τ), h * κ τ h ≤ L) :
    Nat.card (ColumnFilling n κ) ≤ t ^ L := by
  have h_column (τ : Φ) (h : ℕ) : Nat.card (IncreasingMap (rankAt n τ) h) ≤ t ^ h := by
    grw [Finite.card_subtype_le, Nat.card_fun, Nat.card_fin, Nat.card_fin, h_rank]
  calc Nat.card (ColumnFilling n κ)
    _ = ∏ τ : Φ, ∏ h : Fin (rankAt n τ), Nat.card (IncreasingMap (rankAt n τ) h) ^ κ τ h := by
      simp only [Nat.card_pi, Finset.prod_const, Finset.card_fin]
    _ ≤ t ^ ∑ τ : Φ, ∑ h ∈ Finset.range (rankAt n τ), h * κ τ h := by
      grw [h_column]
      simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.sum_range, le_refl]
    _ ≤ t ^ L := Nat.pow_le_pow_right ht h_degree

/-- Over any commutative ring, let f be a Borel semi-invariant of the weight given by κ
(`New.nablaFamily`). Then the hook number times f is `toPoly n κ ζ` for some coordinate vector ζ,
where `New.toPoly` sends ζ to `∑ i, (G ζ) i • b i` (G the Gram matrix, b the basis minor
products). -/
lemma exists_toPoly_eq_hookNumber_smul {f : MatrixPoly (Sigma n) R} (hf : f ∈ nablaFamily R n κ) :
    ∃ ζ : WeylIndexFamily n κ → R, toPoly n κ ζ = hookNumber κ (rankAt n) • f := by
  -- With `c` the coordinates of `f` in `nablaBasis` and `F` the matrix of Fock pairings of
  -- `nablaBasis`, take `ζ = F *ᵥ c`: the Gram matrix times `F` is the hook number times the
  -- identity.
  obtain ⟨c, rfl⟩ : f ∈ (nablaCombination κ).range := range_nablaCombination.ge hf
  let F : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℤ :=
    of fun i j ↦ fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)
  refine ⟨F.map (↑) *ᵥ c, ?_⟩
  rw [← nablaCombination_weylGramOver_mulVec, mulVec_mulVec, ← map_mul_intCast,
    weylGram_mul_fockPairing]
  simp [Matrix.map_intCast, ← Int.cast_smul_eq_zsmul R]

end «GL»

end New

/-!
## Cartan multiplication and norms of products

`New.WeylIndexFamily n κ` indexes the basis, and `New.weylEval n κ y` is the vector of values of the
basis at `y`. The tensor product `(p, q) ↦ a p * b q` is written `(vecMulVec b a).vec`, since
`Matrix.vec` swaps the two indices.
-/

section Cartan

open Matrix Kronecker SetLike

namespace New.GL

variable {Φ R : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] {κ κ' : Φ → ℕ → ℕ}

variable (R n κ κ') in
/-- The matrix of multiplication: row `(p, q)` holds the integer coordinates of the product of the
basis elements `nablaBasis ℤ n κ p` and `nablaBasis ℤ n κ' q` in the basis for `κ + κ'`, cast to
`R`. -/
noncomputable def comulMatrix :
    Matrix (WeylIndexFamily n κ × WeylIndexFamily n κ') (WeylIndexFamily n (κ + κ')) R :=
  of fun (p, q) k ↦
    (Function.invFun (nablaCombination (κ + κ')) (nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q) k : ℤ)

/-- The multiplication matrix sends the evaluation vector at `y` for `κ + κ'` to the tensor product
of those for `κ` and `κ'`: the right side is `(p, q) ↦ weylEval n κ' y q * weylEval n κ y p`. -/
lemma comulMatrix_mulVec_weylEval (y : (Σ τ : Φ, n τ) × ℕ → R) :
    comulMatrix R n κ κ' *ᵥ weylEval n (κ + κ') y =
      (vecMulVec (weylEval n κ' y) (weylEval n κ y)).vec := by
  -- Expand the product of two basis elements in the basis for `κ + κ'` over `ℤ`, then map to `R`
  -- and evaluate at `y`.
  funext ⟨p, q⟩
  have h_mem : nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q ∈ nablaFamily ℤ n (κ + κ') := by
    rw [nablaFamily, diagramWeight_add]
    exact mul_mem_graded prod_tableauPoly_mem_nabla prod_tableauPoly_mem_nabla
  have h_expand : ∑ k : WeylIndexFamily n (κ + κ'), comulMatrix ℤ n κ κ' (p, q) k •
      nablaBasis ℤ n (κ + κ') k = nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q :=
    sum_coords_nablaBasis h_mem
  simpa [comulMatrix, mulVec, dotProduct, weylEval, vecMulVec_apply, mul_comm] using
    congrArg (fun P ↦ (P.map (algebraMap ℤ R)).eval y) h_expand

variable [IsDomain R] [Infinite R]

/-- Work over an infinite domain, and let `a ⊗ b` be the row vector `(vecMulVec b a).vec`, with
entry `b q * a p` at `(p, q)`. Then `a ⊗ b` times the multiplication matrix is `x` exactly when the
product of the polynomials with coordinates `a` (basis for `κ`) and `b` (basis for `κ'`) has
coordinates `x` (basis for `κ + κ'`). -/
lemma vecMul_comulMatrix_eq_iff {a : WeylIndexFamily n κ → R} {b : WeylIndexFamily n κ' → R}
    {x : WeylIndexFamily n (κ + κ') → R} :
    (vecMulVec b a).vec ᵥ* comulMatrix R n κ κ' = x ↔
      nablaCombination κ a * nablaCombination κ' b = nablaCombination (κ + κ') x := by
  -- Both sides say that the polynomials agree at every `y`: pair with `weylEval n (κ + κ') y` and
  -- use `comulMatrix_mulVec_weylEval`.
  have h_eval_product (y : ((τ : Φ) × n τ) × ℕ → R) :
      MvPolynomial.eval y
          (nablaCombination (κ + κ') ((vecMulVec b a).vec ᵥ* comulMatrix R n κ κ')) =
        MvPolynomial.eval y (nablaCombination κ a * nablaCombination κ' b) := by
    simp [comulMatrix_mulVec_weylEval, ← weylEval.eq_1, Fintype.linearCombination,
      ← dotProduct.eq_1,
      ← dotProduct_mulVec, mul_comm (a ⬝ᵥ _), vec_dotProduct_vec, mul_vecMulVec, vecMulVec_mulVec]
  rw [← nablaCombination_injective.eq_iff, MvPolynomial.funext_iff, MvPolynomial.funext_iff]
  simp only [h_eval_product]

/-- Over an infinite domain, the multiplication matrix `C` is an isometry for the Gram forms:
`Cᵀ (G κ ⊗ G κ') C = G (κ + κ')`, where `G` is the Gram matrix `weylGram` mapped into `R`. -/
lemma comulMatrix_isometry :
    (comulMatrix R n κ κ')ᵀ * ((weylGram n κ).map (Int.cast : ℤ → R) ⊗ₖ
        (weylGram n κ').map (Int.cast : ℤ → R) * comulMatrix R n κ κ') = weylGramOver := by
  -- Test on the evaluation vectors, which `C` sends to tensor products
  -- (`comulMatrix_mulVec_weylEval`).
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  -- The kernel for `κ + κ'` is the product of the kernels for `κ` and `κ'`.
  simp [comulMatrix_mulVec_weylEval, vecMul_comulMatrix_eq_iff,
    nablaCombination_weylGramOver_mulVec,
    pow_add, kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
    mulVec_transpose, weylKernel, highestPoly, tableauPoly, Finset.prod_mul_distrib]

/-- Over an infinite domain, the multiplication matrix `C` is equivariant: for the Schur matrices
`S` of a family `g` of square matrices, `(S κ g ⊗ S κ' g) C = C * S (κ + κ') g`. -/
lemma comulMatrix_equivariant (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    schur κ g ⊗ₖ schur κ' g * comulMatrix R n κ κ' =
      comulMatrix R n κ κ' * schur (κ + κ') g := by
  -- Test on the evaluation vectors, which `C` sends to tensor products
  -- (`comulMatrix_mulVec_weylEval`).
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  simp [comulMatrix_mulVec_weylEval, schur_mulVec_weylEval_of_schurDetExp_eq_zero,
    kronecker_mulVec_vec,
    mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

/-- The integer matrix whose row (p, q) lists the coordinates of the product of the basis minor
products b_p for κ and b_q for κ', in the basis for κ + κ', has an integer left inverse. -/
lemma hasLeftInv_comulMatrix : HasLeftInv (comulMatrix ℤ n κ κ') := by
  -- A basis tableau for `κ + κ'` splits into its first `κ` and last `κ'` columns of each height.
  -- `f k` and `g k` are the minor products of these columns; `f k * g k` is the basis element.
  let f (k : WeylIndexFamily n (κ + κ')) : MatrixPoly ((τ : Φ) × n τ) ℤ :=
    ∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ)
      (fun h j ↦ (k τ).val h (Fin.castAdd _ j) : Tableau (n τ) (rankAt n τ) (κ τ))
  let g (k : WeylIndexFamily n (κ + κ')) : MatrixPoly ((τ : Φ) × n τ) ℤ :=
    ∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ)
      (fun h j ↦ (k τ).val h (Fin.natAdd _ j) : Tableau (n τ) (rankAt n τ) (κ' τ))
  have hf (k : WeylIndexFamily n (κ + κ')) : f k ∈ nablaFamily ℤ n κ := prod_tableauPoly_mem_nabla
  have hg (k : WeylIndexFamily n (κ + κ')) : g k ∈ nablaFamily ℤ n κ' := prod_tableauPoly_mem_nabla
  have hfg (k : WeylIndexFamily n (κ + κ')) : f k * g k = nablaBasis ℤ n (κ + κ') k := by
    simp [f, g, nablaBasis, Fin.prod_univ_add, tableauPoly, Finset.prod_mul_distrib]
  -- Row `k` of the left inverse is the tensor product of the coordinates of the two factors.
  refine ⟨fun k ↦ (vecMulVec (Function.invFun (nablaCombination κ') (g k))
      (Function.invFun (nablaCombination κ) (f k))).vec,
    ext_row fun k ↦ vecMul_comulMatrix_eq_iff.mpr ?_⟩
  simp [Fintype.linearCombination_apply, ↓sum_coords_nablaBasis, hf, hg, hfg, Matrix.one_apply]

/-- Let ξ, η, ζ be complex vectors of the Weyl modules of weights κ, κ' and κ+κ'. Assume the
polynomial of ζ is the product of those of ξ and η, where the polynomial `toPoly` of a vector ξ is
Σ_i (Gξ)_i b_i, with G the integer Gram matrix and b_i the basis minor products. Then
`weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η`, where `weylNormSq ξ` is the real part of ξ* G ξ, the
squared norm for the positive definite Hermitian form of G. -/
lemma _root_.New.weylNormSq_le_mul_of_toPoly_eq {ξ : WeylIndexFamily n κ → ℂ}
    {η : WeylIndexFamily n κ' → ℂ} {ζ : WeylIndexFamily n (κ + κ') → ℂ}
    (h_toPoly_eq : toPoly n (κ + κ') ζ = toPoly n κ ξ * toPoly n κ' η) :
    weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η := by
  -- Cauchy–Schwarz for the form `B = G κ ⊗ G κ'` on `C *ᵥ ζ` and `v = ξ ⊗ η`: their pairing is
  -- `weylNormSq ζ` by `h_toPoly_eq`, and `C` is an isometry by `comulMatrix_isometry`.
  let C := comulMatrix ℂ n κ κ'
  let B := (weylGram n κ).map (Int.cast : ℤ → ℂ) ⊗ₖ (weylGram n κ').map (Int.cast : ℤ → ℂ)
  let v : WeylIndexFamily n κ × WeylIndexFamily n κ' → ℂ := (vecMulVec η ξ).vec
  have hC_real : Cᴴ = Cᵀ := by
    ext i j
    simp [C, comulMatrix]
  -- The hypothesis in coordinates: multiplication sends `G ξ ⊗ G η` to `G ζ`.
  have h_coord : (vecMulVec (weylGramOver *ᵥ η) (weylGramOver *ᵥ ξ)).vec ᵥ* C = weylGramOver *ᵥ ζ :=
    vecMul_comulMatrix_eq_iff.mpr h_toPoly_eq.symm
  have h_tensorVec : B *ᵥ v = (vecMulVec (weylGramOver *ᵥ η) (weylGramOver *ᵥ ξ)).vec := by
    simp [B, v, vecMul_transpose _ ξ, kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul]
  have h_pair : star (C *ᵥ ζ) ⬝ᵥ B *ᵥ v = weylNormSq ζ := by
    rw [h_tensorVec]
    simp [star_mulVec, ← dotProduct_mulVec, h_coord, ← coe_weylNormSq, hC_real, mulVec_transpose]
  have h_tensor : (star v ⬝ᵥ B *ᵥ v).re = weylNormSq η * weylNormSq ξ := by
    rw [h_tensorVec]
    simp [v, ← coe_weylNormSq, ↓map_vecMulVec_star, star_vec, vec_dotProduct_vec,
      vecMulVec_mul_vecMulVec, mul_comm]
  have h_isom : (star (C *ᵥ ζ) ⬝ᵥ B *ᵥ (C *ᵥ ζ)).re = weylNormSq ζ := by
    simp [B, C, star_mulVec, ← dotProduct_mulVec, hC_real, mulVec_mulVec, comulMatrix_isometry,
      ← coe_weylNormSq]
  have h_sq : weylNormSq ζ ^ 2 ≤ weylNormSq η * weylNormSq ξ * weylNormSq ζ := by
    simpa only [h_pair, h_tensor, h_isom, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      posDef_cauchy_schwarz (M := B) (weylGramOver_posDef.kronecker weylGramOver_posDef) (C *ᵥ ζ) v
  -- Cancel one factor `weylNormSq ζ`; if it is not positive, the right side is still nonnegative.
  nlinarith [mul_nonneg (weylNormSq_nonneg ξ) (weylNormSq_nonneg η)]

end New.GL

end Cartan

/-!
## Products of determinants

* `New.pairedDetProd`: the product of the determinants `det (η τ k * Y τ)`, with one matrix `Y τ`
  for each `τ : Φ`.
-/

namespace New

open Matrix

variable {Φ n a S : Type} [Fintype Φ] [Fintype n] [CommRing S] [Algebra ℂ S] [Fintype a]
  [DecidableEq a] {ι : Φ → Type} [∀ τ : Φ, Fintype (ι τ)]
  (Y : Φ → n → a → S) (η : ∀ τ : Φ, ι τ → Matrix a n ℂ)

/-- The element ∏_τ ∏_k det(η_{τk} Y_τ) of the ℂ-algebra S, for n×a matrices Y_τ over S and
complex a×n matrices η_{τk}. -/
noncomputable def pairedDetProd : S :=
  ∏ τ : Φ, ∏ k : ι τ, ((η τ k).map (algebraMap ℂ S) * of (Y τ)).det

end New
