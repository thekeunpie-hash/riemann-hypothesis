module

import Mathlib.Data.Finset.Slice
public import New.OneLift.ComparisonOperator.GluedLattices
import Lib.General.LinearAlgebra.MatrixNormBounds
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Tactic.Monotonicity.Lemmas
public import New.OneLift.ComparisonOperator.ProductsSpan
public import New.Determinant.Twist.FitTwists
public import New.OneLift.ComparisonOperator.FirstFactors
public import New.OneLift.ComparisonOperator.ThreeExchanges
import New.OneLift.FalseLifts.PeriodsOfFalseLifts
import New.Spanning.Multiplicities.EqualMultiplicities
import New.Spanning.SecondMoment.SpanningTheorem
import New.UpperBound.Kernels.ThetaLiftGauge
import New.UpperBound.Size.Estimates
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import New.Determinant.Chain.NormOfChain
import Lib.GLn.SchurModule.SchurNorm
import New.Congruences.GaloisRepresentations.SelmerHypotheses
import New.OneLift.HeckeValues.TwistedValueHeights

section
section
/-!
# Gluing: the descent of product forms and the denominators

This file treats forms on the definite space `V = V″ ⊕ V°` glued, in
`New.OneLift.ComparisonOperator.GluedLattices`, from a vector for `V″` and a vector for `V°`
across a change of lattice at the chosen places.

The data are a descent pair `O` (`New.DescentPair`), with the space `W = O.W` of rank `r`, and a
splitting `V : New.Rows.DividedSplitting N m a O z`. Here `N` indexes `V″`, `m` indexes `V°`,
`z : r ↪ m` marks `r` basis vectors of `V°`, and `a` indexes the rows of a matrix `s` modulo `ϖ²`,
the linear forms on `V″` on which a finer congruence is imposed. The idele `ϖ = O.genIdele`
generates the product of the chosen places `O.chosenPlace i`, and `Q` is the product of the places
`O.twistPlace i`. We write `(1; 0)` for an inclusion matrix `New.inclMatrix` with `r` columns.

The datum of the theta lift from `W` to `V` asks for `x ≡ (1; 0)` modulo `ϖ`. A product datum asks
for conditions modulo `ϖ²` on the two blocks of `x`. The lattice that connects them is spanned by
the columns of the matrix that is `(1; 0)` on both summands, by `L″_s = {u | s u ≡ 0 modulo ϖ}` in
`V″` and by `ϖ` times the standard lattice of `V°`. The matrix of a basis is called `γ`, and it is
handled through the integral matrix `ϖ γ⁻¹`.

This file computes the descent to `W` of product forms on a glued lattice, from which the slices
of a lift are read off. It also bounds the p-adic gauge of the Cartan product at the point
`(h, h') γ`.

## Main definitions and results

* Slices of lifts. `New.Rows.DividedSplitting.normalizedDescent_productForm`: if `V.IsGlued s L` and
  `b * b' = O.charV`, the descent to `W` of a product form is the complex conjugate of the product
  of `L.weilScalar` with a sum over the congruence group, whose terms are products of a kernel on
  `V″` and one on `V°`. `New.Rows.DividedSplitting.normalizedDescent_stdClassSum_productForm`: the
  same for the sum of product forms over the classes, with `New.Rows.kernelClassSum` on `V″`.
* The denominators. `New.Rows.DividedSplitting.weylGauge_cartanProduct_le`: for a glued lattice, a
  natural number `M ≠ 0` divisible by `ϖ` and points `h`, `h'` on the two summands, the gauge of
  the product of two vectors at the point `(h, h') γ` (with `(h, h')` made block diagonal along
  `V.ε : N ⊕ m ≃ n`) is at most `‖M‖⁻¹ ^ V.denominatorExponent` times their gauges.

Notions from other files:
* `New.DescentPair`: A descent pair: chosen places and twist places, a space W of rank r with
  numbered basis vectors, an embedding of indices into n > r, two diagrams given by their numbers of
  columns of each height, and a character μ whose tame part, a character `O.tamePart w` of the
  residue field at each place w, is trivial off these places.
* `New.LevelPlaces.levelModulus`, `New.Rows.liftMod`: `levelModulus c` is the modulus ϖ^c·Q, and
  `levelModulus c false` is ϖ^c. `liftMod` is a chosen lift of an invertible matrix modulo an
  ideal to an integral point of G_f that is 1 outside the places dividing the ideal and their
  conjugates.
* `New.inclMatrix`: For a map u: m → n of index sets, the n×m matrix whose j-th column is the
  standard basis vector e_{u(j)}.
* `New.modKernel`: The theta kernel at (g, h) of the datum given by a function on matrices modulo an
  ideal and the Fock vector of a polynomial.
* `New.WeylIndex`: `WeylIndex n κ` indexes the standard basis of the vectors of weight κ in n
  letters. Here `κ τ h` is the number of columns of height h at the infinite place τ.

## Relation to the literature

See `New.OneLift.ComparisonOperator.GluingMaps` and
`New.OneLift.ComparisonOperator.FirstFactors` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Rows

/-!
## The descent of product forms

The descent `O.normalizedDescent` pairs a form on `V` with the theta kernel; it is adjoint to the
lift from `W`. So the slices of a lift are read off from the descents of product forms.

* `New.Rows.DividedSplitting.normalizedDescent_classForm_mul`: the descent of the form supported on
  the class of `h * L.point` is the complex conjugate of the product of `L.weilScalar` with a kernel
  at `h`. The datum of the kernel at `S` is nonzero only when `(ϖ γ⁻¹) S ≡ ϖ (1; 0)` modulo `ϖ²`.
  There it is a product of values of `O.tamePart` on determinants at the places of `Q`.
* `New.Rows.fockPoly_cartanProduct`: the Fock polynomial of the product of a vector on `V″` and a
  vector on `V°` is the product of their polynomials.
-/

section GluedFormTheta

open Matrix ComplexConjugate Finset Modulus MvPolynomial Sum

variable {E r n N m a : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] [Fintype N] [DecidableEq N] [Fintype m]
  {O : DescentPair E r n} {z : r ↪ m} (V : DividedSplitting N m a O z) {L : DividedLattice O}

omit [DecidableEq n] in
/-- The kernel `kernelClassSum` of `c • y` is `c` times that of `y`. It is the sum, over classes `h`
of the level fixing the rows `w` and the columns off `e`, of the theta kernel of W (signs `O.signs`)
and the standard space on `m`, with character `b` on the latter and the polynomial of `y h`. -/
lemma kernelClassSum_smul [DecidableEq m] [WeilData E]
    (b : AutChar E) (w : Matrix a m O.chosenModulusSq.ResidueRing) (e : r ↪ m)
    (c : ℂ) (y : Gf E m → WeylIndex m O.colsPlus → ℂ) (g : G E O.signs) :
    kernelClassSum O b w e (fun h : Gf E m ↦ c • y h) g = c * kernelClassSum O b w e y g := by
  simp [kernelClassSum, mul_classSum, ← modKernelBilin_apply]

omit [DecidableEq r] in
/-- Let `f : N → n` map the letters `N` to the letters `n`, and let `κ` satisfy
`HasColumnsBelow n N κ`: `#N ≤ #n`, and `κ` has no column of a height `h` with `#N ≤ h < #n`. The
polynomial `letterPoly` of the image of `y` under the Schur matrix of the inclusion matrix of `f` is
the polynomial of `y` with the rows of its variables renamed along `f`. -/
lemma letterPoly_schur_inclMatrix_mulVec {Φ : Type} [Fintype Φ] [DecidableEq Φ] {κ : Φ → ℕ → ℕ}
    (hκ : HasColumnsBelow n N κ) (s : r → ℤˣ) (ord : r → ℕ) (c : ℤˣ) (f : N → n)
    (y : WeylIndex N κ → ℂ) :
    letterPoly s ord c κ (schur κ (fun _ : Φ ↦ inclMatrix ℂ f) *ᵥ y) =
      renameRowsCols f id (letterPoly s ord c κ y) := by
  -- The Schur matrix acts on polynomials by substituting the transpose, with no determinant factor.
  have h_toPoly : toPoly (fun _ : Φ ↦ n) κ (schur κ (fun _ : Φ ↦ inclMatrix ℂ f) *ᵥ y) =
      rowSubst (fun _ : Φ ↦ (inclMatrix ℂ f)ᵀ) (toPoly (fun _ : Φ ↦ N) κ y) := by
    rw [toPoly_schur hκ.fitsRanks, hκ.schurDetExp_eq_zero, detPow_zero, mul_one]
  -- This substitution sends the variable in row `i` to that in row `f i`.
  rw [letterPoly, letterPoly, LinearMap.comp_apply, LinearMap.comp_apply, h_toPoly]
  simp [rowSubst, fockLetters, inclMatrix, comp_aeval_apply, Matrix.one_apply]

/-- Let `ε : N ⊕ m ≃ n` split the indices of `V = V″ ⊕ V°`, and let `O.colsPlus` and `O.colsMinus`
satisfy `HasColumnsBelow`: each column of height below the rank of `V` has height below the rank of
`V″`, respectively of `V°`. For `y` of weight `O.colsPlus` on `V″` and `η` of weight `O.colsMinus`
on `V°`, the polynomial `O.fockPoly` of `cartanProduct ε 1 y η` is the polynomial `letterPoly` of
`y` in the variables of the basis vectors of `O.W` of sign `1` on the rows of `V″`, times that of
`η` in the variables of sign `-1` on the rows of `V°`. -/
lemma fockPoly_cartanProduct [DecidableEq m] (h_plus : HasColumnsBelow n N O.colsPlus)
    (h_minus : HasColumnsBelow n m O.colsMinus) (ε : N ⊕ m ≃ n)
    (y : WeylIndex N O.colsPlus → ℂ) (η : WeylIndex m O.colsMinus → ℂ) :
    O.fockPoly (cartanProduct ε 1 y η) =
      renameRowsCols (ε ∘ inl) id (letterPoly O.signs O.numbering 1 O.colsPlus y) *
        renameRowsCols (ε ∘ inr) id (letterPoly O.signs O.numbering (-1) O.colsMinus η) := by
  -- The polynomial is read on the image under `mixedCartan`, the tensor of the included vectors.
  calc O.fockPoly (cartanProduct ε 1 y η)
    _ = O.tensorPoly ((mixedCartan n O.colsPlus O.colsMinus).matrix.map (↑) *ᵥ
          cartanProduct ε 1 y η) := rfl
    _ = letterPoly O.signs O.numbering 1 O.colsPlus
            (schur O.colsPlus (fun _ ↦ inclMatrix ℂ (ε ∘ inl)) *ᵥ y) *
          letterPoly O.signs O.numbering (-1) O.colsMinus
            (schur O.colsMinus (fun _ ↦ inclMatrix ℂ (ε ∘ inr)) *ᵥ η) := by
      rw [mixedCartan_mulVec_cartanProduct h_plus h_minus, transpose_vecMulVec,
        DescentPair.tensorPoly_vecMulVec]
    _ = _ := by
      rw [letterPoly_schur_inclMatrix_mulVec h_plus, letterPoly_schur_inclMatrix_mulVec h_minus]

namespace DividedSplitting

/-- Let `ϖ` generate the product of the chosen places of `O`, let `Q` be the product of its twist
places, and let `idem` be the adele that is `1` at the places dividing `ϖ² Q = O.levelModulus 2` and
`0` elsewhere. Let `γ = L.point` be a unitary point at the chosen places with `ϖ γ⁻¹` integral. If
`idem * (γ⁻¹ x)` has integral entries, then so has `idem * x`. -/
lemma idem_mul_mem_of_inv_mul_mem (x : Matrix n r (𝔸f E))
    (hx : ∀ (k : n) (j : r),
      idem (O.levelModulus 2).places * (L.point⁻¹.val.val * x) k j ∈ Ô E) (i : n) (j : r) :
    idem (O.levelModulus 2).places * x i j ∈ Ô E := by
  -- By unitarity the conjugate of `ϖ γ⁻¹` is `conj ϖ • γᵀ`, which is integral. Here `conj ϖ` is
  -- `1` at a place `w` of the level, as `star w` is not a chosen place.
  refine idem_mul_mem_Ô.2 fun w hw ↦ ?_
  have hπ : O.genIdele.val (star w) = 1 :=
    genIdele_apply_of_notMem fun ⟨t, ht⟩ ↦
      (isConjDisjoint_places _).le_bot ⟨hw, places_levelModulus.ge ⟨inl t, ht⟩⟩
  have h_int (k : n) : star (O.genIdele * L.point.val.valᴴ k i) ∈ Ô E := by
    rw [← U.inv_val_eq_conjTranspose]
    exact star_mem_Ô (L.mul_inv_mem k i)
  have h_sum : ∑ k : n, star (O.genIdele * L.point.val.valᴴ k i) *
      (idem (O.levelModulus 2).places * (L.point⁻¹.val.val * x) k j) ∈ Ô E :=
    sum_mem fun k _ ↦ mul_mem (h_int k) (hx k j)
  simpa [mul_assoc, mul_left_comm _ (idem _), ← mul_sum, ← Matrix.mul_apply,
    ← Matrix.mul_assoc, hw, hπ] using mem_Ô.1 h_sum w

omit [DecidableEq N] in
/-- Let `ϖ` generate the product of the chosen places, with class `V.genResidue` modulo `ϖ²`, let
`Q` be the product of the twist places, and let `ι` be the inclusion matrix of `O.incl : r ↪ n`. The
map `liftFn` extends a function on matrices modulo `ϖ² Q` to adelic vectors `x`, by `0` where `x` is
not integral at the places of `ϖ² Q`. Consider two functions of `T`, supported on `ϖ T ≡ ϖ ι` and on
`(ϖ γ⁻¹) T ≡ ϖ ι` modulo `ϖ²`, where `γ = L.point` and `L.reducedInverse` is `ϖ γ⁻¹` modulo `ϖ²`. On
its support each is the product over the twist places of the residue characters `O.tamePart` at the
determinant of the rows `O.incl` of `T`. Then the extension of the first at `γ⁻¹ x` equals that of
the second at `x`. -/
lemma liftFn_datum_point_inv_mul (x : n × r → 𝔸f E) :
    (O.levelModulus 2).liftFn
        ((fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if V.genResidue • T.map reduceToChosenModulusSq =
              V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
            ∏ i : O.TwistIndex, O.tamePart (O.placeAt (inr i))
              ((T.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0) ∘ vecToMatrix)
        (matrixToVec (L.point⁻¹.val.val * vecToMatrix x)) =
      (O.levelModulus 2).liftFn
        ((fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if L.reducedInverse * T.map reduceToChosenModulusSq =
              V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
            ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
              ((T.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0) ∘ vecToMatrix) x := by
  classical
  -- Each side is `0` unless its vector, `γ⁻¹ x` or `x`, is integral on the level.
  simp only [liftFn_apply, Function.comp_apply, Prod.forall]
  have h_entry (hx : ∀ (i : n) (j : r), idem (O.levelModulus 2).places * x (i, j) ∈ Ô E)
      (i : n) (j : r) :
      (L.reducedInverse *
          (vecToMatrix fun p ↦ (O.levelModulus 2).reduction
            ⟨idem (O.levelModulus 2).places * x p, hx p.1 p.2⟩).map reduceToChosenModulusSq) i j =
        O.chosenModulusSq.reduction
          (∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
            ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩) := by
    rw [Matrix.mul_apply]
    change _ = O.chosenModulusSq.reduction.toAddMonoidHom _
    rw [map_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [DividedLattice.reducedInverse, of_apply, Matrix.map_apply, vecToMatrix, of_apply,
      factor_reduction]
    exact (RingHom.map_mul ..).symm
  have h_sum_val (hx : ∀ (i : n) (j : r), idem (O.levelModulus 2).places * x (i, j) ∈ Ô E)
      (i : n) (j : r) :
      ((∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
          ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩ : Ô E) : 𝔸f E) =
        O.genIdele.val *
          (idem (O.levelModulus 2).places * (L.point⁻¹.val.val * vecToMatrix x) i j) := by
    change (Ô E).subtype.toAddMonoidHom _ = _
    rw [map_sum, Matrix.mul_apply, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    change (O.genIdele.val * L.point⁻¹.val.val i k) * (idem (O.levelModulus 2).places * x (k, j)) =
      O.genIdele.val * (idem (O.levelModulus 2).places * (L.point⁻¹.val.val i k * x (k, j)))
    rw [mul_mul_mul_comm, mul_assoc]
  split
  next h_inv_mul =>
    have hx : ∀ (i : n) (j : r), idem (O.levelModulus 2).places * x (i, j) ∈ Ô E :=
      idem_mul_mem_of_inv_mul_mem (vecToMatrix x) h_inv_mul
    rw [dite_eq_left hx]
    refine ite_congr (propext ?_) (fun _ ↦ prod_congr rfl fun l _ ↦ ?_) fun _ ↦ rfl
    · -- The two conditions agree, as `genIdele γ⁻¹ x = (genIdele γ⁻¹) x` entrywise.
      rw [← ext_iff, ← ext_iff]
      refine forall₂_congr fun i j ↦ ?_
      rw [Matrix.smul_apply, Matrix.map_apply, vecToMatrix, of_apply, factor_reduction,
        smul_eq_mul, ← RingHom.map_mul, h_entry hx i j]
      have h_eq : (O.genIntAdele * ⟨idem (O.levelModulus 2).places *
          matrixToVec (L.point⁻¹.val.val * vecToMatrix x) (i, j), h_inv_mul i j⟩ : Ô E) =
          ∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
            ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩ :=
        Subtype.ext (h_sum_val hx i j).symm
      rw [h_eq]
    · -- At a place of `Q` the matrix `γ⁻¹` is `1`, so `γ⁻¹ x` and `x` have the same component.
      congr 3 with i j
      simp only [Matrix.map_apply, vecToMatrix, of_apply, modulusResidue_reduction, matrixToVec]
      congrm ⟦⟨_ * ?_, _⟩⟧
      have h_one : L.point⁻¹.val.val.map (evalAt (O.twistPlace l)) = 1 :=
        congrArg Units.val (atPlace_twistPlace_eq_one (inv_mem L.mem_supportedOn) l)
      have h_comp : (L.point⁻¹.val.val * vecToMatrix x).map (evalAt (O.twistPlace l)) =
          (vecToMatrix x).map (evalAt (O.twistPlace l)) := by
        rw [Matrix.map_mul, h_one, Matrix.one_mul]
      exact congrFun₂ h_comp i j
  next h_inv_mul =>
    split_ifs with hx h_cond
    · -- If `x` is integral and satisfies the condition, multiply the condition by `genResidue`:
      -- as `genResidue ^ 2 = 0`, the entries of `genIdele ^ 2 γ⁻¹ x` vanish modulo `ϖ²`, so
      -- `γ⁻¹ x` is integral (`reduction_levelModulus_eq_zero_iff`), against `h_inv_mul`.
      have h_gen_sq : V.genResidue * V.genResidue = 0 := by
        rw [← RingHom.map_mul, reduction_levelModulus_eq_zero_iff]
        change O.genIdele⁻¹.val ^ 2 * (O.genIdele.val * O.genIdele.val) ∈ Ô E
        rw [sq, mul_mul_mul_comm, Units.inv_mul, mul_one]
        exact one_mem _
      refine (h_inv_mul fun i j ↦ ?_).elim
      have h_mul : O.chosenModulusSq.reduction (O.genIntAdele *
          ∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
            ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩) = 0 := by
        rw [RingHom.map_mul, ← h_entry hx i j, congrFun₂ h_cond i j, Matrix.smul_apply, smul_eq_mul,
          ← mul_assoc, h_gen_sq, zero_mul]
      have h_mem := reduction_levelModulus_eq_zero_iff.1 h_mul
      change O.genIdele⁻¹.val ^ 2 * (O.genIdele.val * _) ∈ Ô E at h_mem
      rw [h_sum_val hx i j, sq, mul_assoc O.genIdele⁻¹.val,
        ← mul_assoc O.genIdele⁻¹.val O.genIdele.val, Units.inv_mul, one_mul,
        ← mul_assoc, Units.inv_mul, one_mul] at h_mem
      exact h_mem
    all_goals rfl

omit [DecidableEq N] in
/-- Let `v` be a vector of the weight whose columns are counted by `O.columnCount`, and let
`γ = L.point`, so that `L.reducedInverse` is `ϖ γ⁻¹` modulo `ϖ²`, with `ϖ` generating the product of
the chosen places. The form `classForm O (h γ) v` on the standard definite space of rank `n` is
supported on the class of `h γ`. Its descent `O.normalizedDescent` to the space `O.W` is, at `g`,
the complex conjugate of a product of two factors. One is `L.weilScalar = χ(δ) / √|δ| ^ #r`, with
`δ` the determinant of `γ` at the chosen places and `χ` the character attached to `O.charW`. The
other is the theta kernel `modKernelStdSpace` of `O.W` and the standard space at `(g, h)`, for the
characters `O.charW`, `O.charV` of the two spaces, the Fock polynomial `O.fockPoly (star v)` of the
conjugate vector, and the following function of `S` modulo `ϖ² Q`. It is `0` unless
`(ϖ γ⁻¹) S ≡ ϖ • inclMatrix _ O.incl` modulo `ϖ²`, and it is then the product over the twist places,
those of `Q`, of the residue characters `O.tamePart` at the determinant of the rows `O.incl` of
`S`. -/
lemma normalizedDescent_classForm_mul [WeilData E]
    (v : WeylIndex n O.columnCount → ℂ) (g : G E O.signs) (h : Gf E n) :
    O.normalizedDescent (classForm O (h * L.point) v) g =
      conj (L.weilScalar * modKernelStdSpace O.W O.charW O.charV (O.levelModulus 2)
        (fun S : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if L.reducedInverse * S.map reduceToChosenModulusSq =
            V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
          ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
            ((S.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0)
        (O.fockPoly (star v)) g h) := by
  -- Split off `L.point` from the point `(g, h γ)`. By `pairWeil_schrodingerOp_of_mem_supportedOn`
  -- it acts on the finite datum by the scalar `L.weilScalar` and the substitution `y ↦ γ⁻¹ y`, and
  -- `liftFn_datum_point_inv_mul` compares the data.
  have h_supp_level : L.point ∈ Gf.supportedOn n (O.levelModulus 2).places :=
    Gf.supportedOn_mono (places_levelModulus.ge.trans' (by
      rintro _ ⟨i, rfl⟩; exact ⟨inl i, rfl⟩)) L.mem_supportedOn
  -- `γ` lies at the places of the level and is `1` at those of `Q`, which do not change `det γ`.
  have h_det : detOn (O.levelModulus 2).places L.point.val =
      detOn (Set.range O.chosenPlace) L.point.val := by
    ext w
    · simp [detOn]
    · simp only [detOn_apply, places_levelModulus, Set.Sum.elim_range]
      by_cases hw : w ∈ Set.range O.chosenPlace
      · simp [hw]
      · by_cases htw : w ∈ Set.range O.twistPlace
        · rcases htw with ⟨i, rfl⟩
          simp [hw, atPlace_twistPlace_eq_one L.mem_supportedOn i]
        · simp [hw, htw]
  rw [normalizedDescent_classForm]
  refine congrArg conj ?_
  -- Write the point as `(g, h) * (1, γ)`, so that `γ` acts on the datum.
  have h_pt : (g, ((1 : GInf E (fun _ : n ↦ 1)), h * L.point)) =
      (g, (1, h)) * (((1 : GInf E O.signs), (1 : Gf E r)), (1, L.point)) := by
    simp only [Prod.mk_mul_mk, mul_one, Prod.mk_one_one]
  have h_scalar :
      ((O.charW.spaceChar (Fintype.card r)).val (detOn (O.levelModulus 2).places L.point.val) /
          (O.charV.spaceChar (Fintype.card n)).val
            (detOn (O.levelModulus 2).places (1 : Gf E r).val) *
          √(ideleAbs (detOn (O.levelModulus 2).places (1 : Gf E r).val)) ^ Fintype.card n /
          √(ideleAbs (detOn (O.levelModulus 2).places L.point.val)) ^ Fintype.card r : ℂ) =
        L.weilScalar := by
    simp [h_det, DividedLattice.weilScalar]
  have h_fn :
      (fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
        O.residueBlockDatum fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ T.map (levelResidueAt i)) =
      (fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
        if V.genResidue • T.map reduceToChosenModulusSq =
            V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
          ∏ i : O.TwistIndex, O.tamePart (O.placeAt (inr i))
            ((T.map (levelResidueAt (inr i))).submatrix O.incl id).det
        else 0) := by
    funext T
    simp only [DescentPair.residueBlockDatum, ← V.genResidue_smul_eq_inclMatrix_iff]
  have h_lift :
      (fun x : n × r → 𝔸f E ↦
        (O.levelModulus 2).liftFn
          ((fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
            O.residueBlockDatum fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ T.map (levelResidueAt i)) ∘
            vecToMatrix)
          (matrixToVec (L.point⁻¹.val.val * vecToMatrix x * (1 : Gf E r).val.val))) =
      (O.levelModulus 2).liftFn
        ((fun S : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if L.reducedInverse * S.map reduceToChosenModulusSq =
              V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
            ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
              ((S.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0) ∘ vecToMatrix) := by
    funext x
    rw [OneMemClass.coe_one, Units.val_one, Matrix.mul_one, h_fn]
    exact V.liftFn_datum_point_inv_mul x
  rw [modKernel, modDatum, h_pt, pairTheta_mul, pairWeil_integrated_fin,
    pairWeil_schrodingerOp_of_mem_supportedOn (isConjDisjoint_places _) (one_mem _) h_supp_level,
    h_scalar, h_lift, map_smul, pairTheta, map_smul, map_smul, smul_eq_mul]
  rfl

omit [DecidableEq n] in
/-- Let `Y` be invertible modulo `ϖ²` and `1` modulo `ϖ`, let `k = liftMod Y` be its chosen lift to
an integral unitary point, reduced at a place by `stdLevel.reduceAt`, and let `x` be a matrix modulo
`ϖ² Q`. Suppose that the rows `S` of `x Y` in `N` satisfy `w S = w ι` modulo `ϖ²`, where
`w = V.stackOverGenScalar s` is `s` stacked above `ϖ • 1` and `ι` is the inclusion matrix of
`V.fixedEmb`. Then the product over the twist places of the residue characters `O.tamePart` at the
determinant of the rows `O.incl` of `x` is `χ` of the determinant of the same rows of `x k`, divided
by the product of `O.tamePart (det k)` over the twist places. Here `χ = charOfTamePart` is the
product of the `O.tamePart` over all places dividing `ϖ² Q`. -/
lemma prod_twist_det_eq_inv_mul_charOfTamePart {s : Matrix a N O.chosenModulusSq.ResidueRing}
    (x : Matrix n r (O.levelModulus 2).ResidueRing) (Y : V.congruenceGroup)
    (h_stack_mul_eq : V.stackOverGenScalar s *
        (x.map reduceToChosenModulusSq * Y.val.val).submatrix (V.ε ∘ inl) id =
      V.stackOverGenScalar s * inclMatrix O.chosenModulusSq.ResidueRing V.fixedEmb) :
    ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
        ((x.map (levelResidueAt (inr i))).submatrix O.incl id).det =
      (∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
          (stdLevel.reduceAt ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i)) (liftMod Y.val)).val.det)⁻¹ *
        charOfTamePart (O.levelModulus 2) O.tamePart
          ((x * ((O.levelModulus 2).reductionGL (liftMod Y.val)).val).submatrix
            ((V.ε ∘ inl) ∘ V.fixedEmb) id).det := by
  -- The character modulo `ϖ² Q` is the product of the `O.tamePart` over the places of the level.
  have h_char (t : (O.levelModulus 2).ResidueRing) :
      charOfTamePart (O.levelModulus 2) O.tamePart t =
        ∏ᶠ j, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) j) (levelResidueAt j t) :=
    (finprod_comp_equiv (.trans (.ofInjective _ O.apart.injective)
      (.subtypeEquivRight fun _ ↦ by rw [places_levelModulus]))).symm
  -- The rows `V.genResidue • 1` in `V.stackOverGenScalar s` give `S ≡ inclMatrix V.fixedEmb`
  -- modulo `ϖ` for the rows `S` of `x Y` in `N`.
  let S : Matrix N r (O.levelModulus 2).ResidueRing :=
    (x * ((O.levelModulus 2).reductionGL (liftMod Y.val)).val).submatrix (V.ε ∘ inl) id
  have hS : V.genResidue • S.map reduceToChosenModulusSq =
      V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing V.fixedEmb := by
    have h_eq : S.map reduceToChosenModulusSq =
        (x.map reduceToChosenModulusSq * Y.val.val).submatrix (V.ε ∘ inl) id := by
      simp only [S, ← submatrix_map, Matrix.map_mul, factor_reductionGL, reductionGL_liftMod]
    rw [h_eq]
    simpa only [stackOverGenScalar, fromRows_mul, toRows₂_fromRows, Matrix.smul_mul, Matrix.one_mul]
      using congrArg toRows₂ h_stack_mul_eq
  -- So at the chosen places the rows `V.fixedEmb` of `S` have determinant `1`.
  have h_tame (i : O.ChosenIndex) :
      O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inl i))
        (levelResidueAt (inl i) (S.submatrix V.fixedEmb id).det) = 1 := by
    simp [RingHom.map_det, ← submatrix_map, (V.genResidue_smul_eq_inclMatrix_iff S V.fixedEmb).1 hS,
      inclMatrix, -elim_inl]
  -- At the places of `Q` the lift of `Y` reduces to `1`.
  have h_lift (i : O.TwistIndex) :
    stdLevel.reduceAt ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i)) (liftMod Y.val) = 1 :=
    stdLevel.reduceAt_eq_one_of_atPlace (atPlace_twistPlace_eq_one (liftMod_mem_supportedOn Y.val)
      i)
  change _ = _ * charOfTamePart (O.levelModulus 2) O.tamePart (S.submatrix V.fixedEmb id).det
  rw [h_char, finprod_eq_prod_of_fintype, Fintype.prod_sum_type, prod_eq_one fun i _ ↦ h_tame i]
  simp [S, RingHom.map_det, ← submatrix_map, h_lift, Function.comp_def, V.equiv_inl_fixedEmb,
    -elim_inr]

variable {s : Matrix a N O.chosenModulusSq.ResidueRing} {b b' : AutChar E}

open scoped Classical in
/-- Let `V.ε : N ⊕ m ≃ n` split the standard definite space on `n` as `V″ ⊕ V°`, with indices `N`
and `m`. Let `ϖ` generate the product of the chosen places, let the lattice `L` with point `γ` be
glued for `s` (`IsGlued`), and let the characters `b`, `b'` have product `O.charV`. The product form
is the form supported on the class of `diag(h, h') γ` built from the Cartan product of `y` and `η`.
Its descent to `O.W` is, at `g`, the complex conjugate of `L.weilScalar = χ(δ) / √|δ| ^ #r` (`δ` the
determinant of `γ` at the chosen places, `χ` attached to `O.charW`) times a sum over `Y` in
`V.congruenceGroup`, the invertible matrices modulo `ϖ²` that are `1` modulo `ϖ`. The term of `Y` is
a product of two theta kernels `modKernelStdSpace` of `O.W` with a standard space, at `g` times the
integral lift `liftMod Y`.
* On `V″`, at `h`: the finite datum `columnDatum` at `σ` is the character `charOfTamePart` of the
determinant of the rows `e = V.fixedEmb` of `σ` if `w σ ≡ w * inclMatrix _ e` modulo `ϖ²`, where
`w = V.stackOverGenScalar s` is `s` above `ϖ • 1`, and `0` otherwise. The polynomial is that of
`star y` in the basis vectors of `O.W` of sign `1`.
* On `V°`, at `h'`: the datum is the indicator of the inclusion matrix of `z : r ↪ m`, and the
polynomial is that of `star η` in the basis vectors of sign `-1`. -/
lemma normalizedDescent_productForm [DecidableEq m] [Fintype a] [WeilData E]
    (hL : V.IsGlued s L) (hb : b * b' = O.charV) (h : Gf E N)
    (h' : Gf E m) (y : WeylIndex N O.colsPlus → ℂ) (η : WeylIndex m O.colsMinus → ℂ)
    (g : G E O.signs) :
    O.normalizedDescent (V.productForm L (h, h') y η) g =
      conj (L.weilScalar * ∑ Y : V.congruenceGroup,
        modKernelStdSpace O.W O.charW b (O.levelModulus 2)
            (columnDatum (charOfTamePart (O.levelModulus 2) O.tamePart) reduceToChosenModulusSq
              (V.stackOverGenScalar s) V.fixedEmb)
            (letterPoly O.signs O.numbering 1 O.colsPlus (star y)) (g * (liftMod Y.val).val) h *
          modKernelStdSpace O.W O.charW b' O.chosenModulusSq
            (Pi.single (inclMatrix O.chosenModulusSq.ResidueRing z) 1)
            (letterPoly O.signs O.numbering (-1) O.colsMinus (star η))
            (g * (liftMod Y.val).val) h') := by
  -- Apply `normalizedDescent_classForm_mul` on the left. On the right, join the two kernels by the
  -- rule for sums `modKernelStdSpace_block` and move the lift of `Y` into the finite datum. Both
  -- sides are then values of the bilinear form `modKernelBilin`, and it remains to compare the
  -- finite data and the polynomials.
  change O.normalizedDescent (classForm O (U.block V.ε (h, h') * L.point) (cartanProduct V.ε 1 y η))
    g =
    _
  rw [V.normalizedDescent_classForm_mul]
  simp_rw [← modKernel_factor levelModulus_ideal_le, ← modKernelStdSpace_block V.ε, hb,
    modKernel_mul_stdLevel_left, ← modKernelBilin_apply, ← LinearMap.sum_apply, ← map_sum]
  refine congrArg conj (congrArg (L.weilScalar * ·)
    (congrArg₂ (fun Ψ P ↦ modKernelBilin _ _ _ _ _ _ _ Ψ P) ?_ ?_))
  · -- The finite data at a matrix `x`. By `hL.indicator_eq_sum` the left datum is a sum over `Y`
    -- with the same support conditions as on the right; compare the values on the support.
    ext x
    simp [← ite_and, ← submatrix_map, columnDatum, reduceAt_liftMod_congruenceGroup,
      hL.indicator_eq_sum, IsBlockNormalized,
      O.hasWeight.hasWeight_rankTwist.apply_det_eq_prod O.apart.injective O.tame_eq_one,
      Pi.single_apply, -elim_inl, -elim_inr]
    refine sum_congr rfl fun Y _ ↦ ite_congr rfl (fun h_supp ↦ ?_) fun _ ↦ rfl
    exact V.prod_twist_det_eq_inv_mul_charOfTamePart x Y h_supp.2
  · -- Conjugation commutes with the product `cartanProduct`, and the polynomial of a product is the
    -- product of the polynomials.
    have h_star : star (cartanProduct V.ε 1 y η) = cartanProduct V.ε 1 (star y) (star η) :=
      map_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2 _ _ _ conj
    rw [h_star, fockPoly_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2]

open scoped Classical in
/-- Let the lattice `L` with point `γ` be glued for `s`, and let `b * b' = O.charV`. Fix a point
`h'` of `Gf E m` on `V°`. Sum (`stdClassSum`) the forms supported on the class of `diag(h, h') γ`
and built from `φ h` and `η` (`productForm`) over the classes `h` of level `rowFixingLevel`. The
descent `O.normalizedDescent` of this sum to `O.W` is, at `g`, the complex conjugate of
`L.weilScalar` times a sum over the invertible matrices `Y` modulo `ϖ²` that are `1` modulo `ϖ`. The
term of `Y` is `kernelClassSum`, the theta kernel of `O.W` and `V″` summed over those classes, times
the theta kernel `modKernelStdSpace` of `O.W` and `V°` at `h'`. Both are taken at `g` times
`liftMod Y`, an integral lift of `Y`. -/
lemma normalizedDescent_stdClassSum_productForm [DecidableEq m] [Fintype a] [WeilData E]
    (hL : V.IsGlued s L) (hb : b * b' = O.charV)
    (h' : Gf E m) (φ : Gf E N → WeylIndex N O.colsPlus → ℂ) (η : WeylIndex m O.colsMinus → ℂ)
    (g : G E O.signs) :
    O.normalizedDescent
        (stdClassSum (rowFixingLevel O.toLevelPlaces (V.stackOverGenScalar s) V.fixedEmb)
          fun h : Gf E N ↦ V.productForm L (h, h') (φ h) η) g =
      conj (L.weilScalar * ∑ Y : V.congruenceGroup,
        kernelClassSum O b (V.stackOverGenScalar s) V.fixedEmb (fun h : Gf E N ↦ star (φ h))
            (g * (liftMod Y.val).val) *
          modKernelStdSpace O.W O.charW b' O.chosenModulusSq
            (Pi.single (inclMatrix O.chosenModulusSq.ResidueRing z) 1)
            (letterPoly O.signs O.numbering (-1) O.colsMinus (star η))
            (g * (liftMod Y.val).val) h') := by
  -- Apply `normalizedDescent_productForm` to each class; `O.normalizedDescent` and evaluation at
  -- `g` are linear.
  change (.proj g ∘ₗ O.normalizedDescent) _ = _
  simp [kernelClassSum, map_classSum, ← classSum_sum, mul_classSum,
    ↓V.normalizedDescent_productForm hL hb,
    mul_sum]

end DividedSplitting

end GluedFormTheta

end New.Rows

/-!
## A p-adic gauge bound for the Cartan product

In this section `V` is a divided splitting of the descent pair `O` along `z`, `p` is a prime, `ι` is
a p-adic place (an embedding of ℂ in ℂ_p) and `M` is a nonzero natural number. The bounds assume
that `M` is divisible by `ϖ`.

* `New.Rows.DividedSplitting.denominatorExponent`: the exponent of `M` that the change of lattice
  costs. On `V″`, where the columns of the diagram are long, it costs `card a` for each column,
  whatever the height.

The gauge `New.weylGauge κ e g ξ` is the largest `p`-adic absolute value of a coordinate of `g⁻¹`
applied to `ι ∘ ξ` in the weight `(κ, e)`. The place `ι` is not a positional argument. It comes from
the `PadicPlace p` instance, or it is given by name as `(ι := …)`.
-/

namespace New.Rows.DividedSplitting

open Matrix ComplexConjugate Finset Fintype IsUltrametricDist Ideal Modulus

variable {E r n N m a : Type} {l : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r]
  [Fintype n] [DecidableEq n] [Fintype N] [Fintype m] [Fintype a] [Fintype l]
  {O : DescentPair E r n} {z : r ↪ m} (V : DividedSplitting N m a O z)
  {p : ℕ} [Fact p.Prime] [ι : PadicPlace p] {M : ℕ} [NeZero M]

/-- The exponent of `M` in the denominator: at each infinite place `τ`, `card a` times the number of
columns of `O.colsPlus` of height below `card N` (a column has distinct entries, so at most `card a`
of them lie in the range of `V.dividedEmb`, the copy of `a` in `N`), plus `card m` times the number
of columns of `O.colsMinus` of height below `card m`, a bound for the number of their boxes. In both
diagrams the entry at `τ h` counts the columns of height `h`. -/
noncomputable def denominatorExponent : ℕ :=
  ∑ τ : NumberField.InfinitePlace E,
    (#(univ.map V.dividedEmb) * ∑ h ∈ range (Fintype.card N), O.colsPlus τ h +
      Fintype.card m * ∑ h ∈ range (Fintype.card m), O.colsMinus τ h)

omit [PadicPlace p] in
/-- For a prime `p`, a natural number `M ≠ 0` and a set `S` of indices, the Schur matrix of weight
`κ` over `ℂ_[p]` of the diagonal matrix that is `M⁻¹` on `S` and `1` elsewhere has entries of p-adic
norm at most `‖M‖⁻¹ ^ (Σ_τ #S · c_τ)`, with c_τ the number of columns of `κ τ` of height below
`card l` (`κ τ h` counts those of height `h`). -/
lemma norm_schur_diagonal_piecewise_inv_le [DecidableEq l] (S : Finset l)
    (κ : NumberField.InfinitePlace E → ℕ → ℕ) (i j : WeylIndex l κ) :
    ‖schur κ (fun _ : NumberField.InfinitePlace E ↦
        diagonal (S.piecewise (M : l → ℂ_[p])⁻¹ 1)) i j‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^
        (∑ τ : NumberField.InfinitePlace E, #S * (range (card l)).sum (κ τ)) := by
  -- The diagonal entry at a filling `i` is `M⁻¹` to the number of entries of `i` in `S`. These
  -- number at most the boxes in the first `#S` rows, and a row has one box at most in each column.
  simp only [schur_diagonal, diagonal_apply]
  split_ifs with hij
  swap
  · simp
  have h_entry : ∏ τ : NumberField.InfinitePlace E, ∏ b : l,
      S.piecewise (M : l → ℂ_[p])⁻¹ 1 b ^ tableauWeight i τ b =
        (M : ℂ_[p])⁻¹ ^ ∑ τ : NumberField.InfinitePlace E, ∑ b ∈ S, tableauWeight i τ b := by
    simp [piecewise, prod_pow_eq_pow_sum, Finset.univ_inter]
  rw [h_entry, norm_pow, norm_inv] -- the exponent is the number of entries in `S`
  gcongr with τ
  · simp [one_le_inv₀, NeZero.ne, norm_natCast_le_one]
  · calc
      _ ≤ ∑ k ∈ range #S, diagramWeight _ κ (τ, k) := (sum_tableauWeight_le i τ S).1
      _ ≤ ∑ _k ∈ range #S, (range (Fintype.card l)).sum (κ τ) := sum_le_sum fun k _ ↦ by
        simpa only [diagramWeight_apply] using sum_le_sum_of_subset fun h hh ↦ by simp_all
      _ = _ := by simp

omit [Fintype a] in
/-- The bound for one block of columns `f : l → n`. Let `ι` be a p-adic place, with map
`ιₚ : ℂ → ℂ_[p]`, and let `M ≠ 0` lie in the ideal `(ϖ) = O.levelModulus 1 false`, the product of
the chosen places of `O`. Let `κ` have no column of height in `[card l, card n)`. Let `γ = L.point`
be a point of the finite adelic unitary group `Gf E n` at the chosen places with `ϖ γ⁻¹` integral,
and `L.reducedInverse` the matrix `ϖ γ⁻¹` modulo `ϖ²`. After an invertible change of its
`f`-columns, let those with index `j ∉ S` be killed by `V.genResidue`, the class of `ϖ`. Let the
`f`-columns of `g⁻¹` be those of `h⁻¹` placed along `f`. Read the `f`-columns of `(g γ)⁻¹` in
`ℂ_[p]` at each `τ` by the extension (`adeleExtension`) of the embedding `weightEmbedding ιₚ τ` of
`E` to the finite adeles. Then their Schur matrix sends `ιₚ ∘ v` to a vector of norm at most
`‖M‖⁻¹ ^ (Σ_τ #S · c_τ)` times `weylGauge κ 0 h v`, the sup norm of `h⁻¹` applied to `ιₚ ∘ v` in
weight `κ` twisted by the power `0` of the determinant. Here c_τ is the number of columns of `κ τ`
of height below `card l`. -/
lemma norm_schur_inv_cols_le_weylGauge [DecidableEq l]
    (hM : (M : NumberField.RingOfIntegers E) ∈ (O.levelModulus 1 false).ideal)
    (L : DividedLattice O) {κ : NumberField.InfinitePlace E → ℕ → ℕ} {h : Gf E l}
    {v : WeylIndex l κ → ℂ} {g : Gf E n} {S : Finset l} {f : l → n}
    (hκ_cols : HasColumnsBelow n l κ)
    (hS : ∃ K : GL l O.chosenModulusSq.ResidueRing, ∀ i : n, ∀ j : l, j ∉ S →
      V.genResidue * (L.reducedInverse.submatrix id f * K.val) i j = 0)
    (h_cols : g⁻¹.val.val.submatrix id f = inclMatrix (𝔸f E) f * h⁻¹.val.val) :
    ‖schur κ (fun τ : NumberField.InfinitePlace E ↦
        ((g * L.point)⁻¹.val.val.submatrix id f).map
          (adeleExtension (weightEmbedding ιₚ τ))) *ᵥ ιₚ ∘ v‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^
          (∑ τ : NumberField.InfinitePlace E, #S * (range (Fintype.card l)).sum (κ τ)) *
        weylGauge κ 0 h v := by
  -- Lift `K` to an integral `k` and write `h = h' k⁻¹`; the gauges at `h` and `h'` agree. With
  -- `h'` again called `h`, the `f`-columns of `(g γ)⁻¹` factor as `A * Δ * h⁻¹`, with `A` integral
  -- at all places and `Δ` diagonal (`M⁻¹` on `S`, `1` elsewhere). The Schur matrix of `A` does not
  -- increase norms; that of `Δ` is diagonal.
  obtain ⟨k, hk⟩ : ∃ k : stdLevel E l, ∀ i : n, ∀ j : l, j ∉ S →
      V.genResidue *
        (L.reducedInverse.submatrix id f * (O.chosenModulusSq.reductionGL k).val) i j = 0 :=
    reductionGL_surjective.exists.1 hS
  obtain ⟨h, rfl⟩ := mul_right_surjective k⁻¹.val h
  rw [weylGauge_mul_of_mem_integralAbove h (stdLevel_le_localLevel k⁻¹.property)]
  let A : Matrix n l (𝔸f E) := of fun (i : n) (j : l) ↦
    (L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j * if j ∈ S then (M : 𝔸f E) else 1
  let Δ : Matrix l l ℂ_[p] := diagonal (S.piecewise (M : l → ℂ_[p])⁻¹ 1)
  have hM_red : (O.levelModulus 1 false).reduction (M : Ô E) = 0 := by
    rw [← map_natCast (algebraMap (NumberField.RingOfIntegers E) (Ô E)), reduction_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hM
  -- `A` is integral because `ϖ A` vanishes modulo `ϖ` (on `S`, via `M`) and `ϖ² A` vanishes
  -- modulo `ϖ²` (off `S`, via `hk`).
  have hA (i : n) (j : l) : A i j ∈ Ô E := by
    let X : Ô E := ∑ c : l, ⟨O.genIdele * L.point⁻¹.val.val i (f c), L.mul_inv_mem i (f c)⟩ *
      ⟨k.val.val.val c j, k.property.isIntMatrix c j⟩
    have hX_val : (X : 𝔸f E) =
        O.genIdele.val * (L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j := by
      change (Ô E).subtype.toAddMonoidHom _ = _
      rw [map_sum, Matrix.mul_apply, mul_sum]
      refine sum_congr rfl fun c _ ↦ ?_
      change (O.genIdele.val * L.point⁻¹.val.val i (f c)) * k.val.val.val c j =
        O.genIdele.val * (L.point⁻¹.val.val i (f c) * k.val.val.val c j)
      rw [mul_assoc]
    by_cases hj : j ∈ S
    · have h_red : (O.levelModulus 1 false).reduction (X * (M : Ô E)) = 0 := by
        rw [RingHom.map_mul, hM_red, mul_zero]
      have h_mem := reduction_levelModulus_eq_zero_iff.1 h_red
      rw [pow_one, Subring.coe_mul, Subring.coe_natCast, hX_val, ← mul_assoc, ← mul_assoc,
        Units.inv_mul, one_mul] at h_mem
      simpa only [A, of_apply, hj, ↓reduceIte] using h_mem
    · have hX_red : O.chosenModulusSq.reduction X =
          (L.reducedInverse.submatrix id f * (O.chosenModulusSq.reductionGL k).val) i j := by
        rw [Matrix.mul_apply]
        change O.chosenModulusSq.reduction.toAddMonoidHom _ = _
        rw [map_sum]
        refine sum_congr rfl fun c _ ↦ ?_
        exact RingHom.map_mul ..
      have h_red : O.chosenModulusSq.reduction (O.genIntAdele * X) = 0 := by
        rw [RingHom.map_mul, hX_red]
        exact hk i j hj
      have h_mem := reduction_levelModulus_eq_zero_iff.1 h_red
      change O.genIdele⁻¹.val ^ 2 * (O.genIdele.val * (X : 𝔸f E)) ∈ Ô E at h_mem
      rw [hX_val, sq, mul_assoc O.genIdele⁻¹.val, ← mul_assoc O.genIdele⁻¹.val O.genIdele.val,
        Units.inv_mul, one_mul, ← mul_assoc, Units.inv_mul, one_mul] at h_mem
      simpa only [A, of_apply, hj, ↓reduceIte, mul_one] using h_mem
  let φ (τ : NumberField.InfinitePlace E) := adeleExtension (E := E) (weightEmbedding ιₚ τ)
  have h_inv : (g * L.point)⁻¹.val.val.submatrix id f =
      L.point⁻¹.val.val.submatrix id f * k.val.val.val * h⁻¹.val.val := by
    rw [_root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul,
      submatrix_mul _ _ id id f Function.bijective_id, submatrix_id_id, h_cols,
      ← Matrix.mul_assoc, mul_inclMatrix, _root_.mul_inv_rev, Subgroup.coe_inv _ k, inv_inv,
      Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  have h_factor (τ : NumberField.InfinitePlace E) :
      ((g * L.point)⁻¹.val.val.submatrix id f).map (φ τ) =
        A.map (φ τ) * Δ * h⁻¹.val.val.map (φ τ) := by
    rw [h_inv, Matrix.map_mul]
    congr 1 with i j
    rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.map_apply]
    change φ τ ((L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j) =
      φ τ ((L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j *
        if j ∈ S then (M : 𝔸f E) else 1) * S.piecewise (M : l → ℂ_[p])⁻¹ 1 j
    rw [RingHom.map_mul, mul_assoc]
    by_cases hj : j ∈ S
    · simp only [hj, ↓reduceIte, Finset.piecewise, Pi.inv_apply, Pi.natCast_apply, map_natCast,
        mul_inv_cancel₀ (Nat.cast_ne_zero (R := ℂ_[p]).2 (NeZero.ne M)), mul_one]
    · simp only [hj, ↓reduceIte, Finset.piecewise, Pi.one_apply, map_one, mul_one]
  -- the vector whose norm is the gauge of `v` at `h`
  let w : WeylIndex l κ → ℂ_[p] :=
    schur κ (fun τ : NumberField.InfinitePlace E ↦ h⁻¹.val.val.map (φ τ)) *ᵥ ιₚ ∘ v
  calc
    _ = ‖schur κ (fun τ ↦ A.map (φ τ)) *ᵥ schur κ (fun _ ↦ Δ) *ᵥ w‖ := by
      simp only [w, mulVec_mulVec, ← Matrix.mul_assoc, hκ_cols.schur_mul_schur, ← h_factor, φ]
    _ ≤ ‖schur κ (fun _ ↦ Δ) *ᵥ w‖ :=
      norm_schur_mulVec_le hκ_cols.1 (fun τ i j ↦ norm_adeleExtension_le_one _ (hA i j)) _
    _ ≤ _ * ‖w‖ := norm_mulVec_le (norm_schur_diagonal_piecewise_inv_le (M := M) S κ) w
    _ = _ := by simp [weylGauge, weylRep, w, φ, -map_inv]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `V.ε : N ⊕ m ≃ n` split the indices, let `ι` be a p-adic place, and let `M ≠ 0` lie in the
ideal of `O.levelModulus 1 false`, the product of the chosen places of `O`. Let the lattice `L` with
point `γ = L.point` be glued for `s`. The diagrams `O.colsPlus` and `O.colsMinus` count the columns
of each height at each infinite place. The vector `y` has the first weight in the letters `N` and
`η` has the second in the letters `m`. Their product `cartanProduct V.ε 1 y η` includes both in the
letters `n` (it is moved by `1`) and projects their tensor product to the weight with column numbers
`O.columnCount` and determinant exponents `O.detExp`. Then the gauge of the product at
`U.block V.ε (h, h') * γ`, with `U.block` the block diagonal matrix, is at most
`‖M‖⁻¹ ^ V.denominatorExponent` times the gauge of `y` at `h` and the gauge of `star η` at `h'`, the
latter through the conjugate embedding. -/
lemma weylGauge_cartanProduct_le [DecidableEq m] [DecidableEq N]
    (hM : (M : NumberField.RingOfIntegers E) ∈ (O.levelModulus 1 false).ideal)
    {s : Matrix a N O.chosenModulusSq.ResidueRing} {L : DividedLattice O} (hL : V.IsGlued s L)
    (h : Gf E N) (h' : Gf E m) (y : WeylIndex N O.colsPlus → ℂ)
    (η : WeylIndex m O.colsMinus → ℂ) :
    weylGauge (ι := ι) O.columnCount O.detExp (U.block V.ε (h, h') * L.point)
        (cartanProduct V.ε 1 y η) ≤
      ‖(M : ℂ_[p])‖⁻¹ ^ V.denominatorExponent *
        (weylGauge (ι := ι) O.colsPlus 0 h y *
          weylGauge (ι := ⟨ιₚ.comp conj⟩) O.colsMinus 0 h' (star η)) := by
  -- `cartanProduct` is an integral matrix applied to the tensor product of two Schur images, one
  -- for each block of `V.ε`; so its norm is at most the product of their norms.
  -- `norm_schur_inv_cols_le_weylGauge` bounds each.
  set g : Gf E n := U.block V.ε (h, h') * L.point
  -- The block `N`: only the columns in the image of `V.dividedEmb` cost a power of `M`.
  have h_big : ‖schur O.colsPlus (fun τ : NumberField.InfinitePlace E ↦
        (g⁻¹.val.val.submatrix id (V.ε ∘ .inl)).map
          (adeleExtension (weightEmbedding ιₚ τ))) *ᵥ ιₚ ∘ y‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^ (∑ τ : NumberField.InfinitePlace E,
          #(univ.map V.dividedEmb) * (range (card N)).sum (O.colsPlus τ)) *
        weylGauge (ι := ι) O.colsPlus 0 h y :=
    V.norm_schur_inv_cols_le_weylGauge hM L V.hasColumnsBelow.1 hL.exists_cols_eq_zero <| by
      rw [← map_inv, Prod.inv_mk, U.block_val]
      refine Matrix.ext fun i j ↦ ?_
      obtain ⟨i' | i', rfl⟩ := V.ε.surjective i
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₁₁, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, ↓reduceIte, zero_mul, Finset.sum_const_zero]
  -- The block `m`, read through the conjugate embedding: every column may cost a power of `M`.
  have h_small : ‖schur O.colsMinus (fun τ : NumberField.InfinitePlace E ↦
        (g⁻¹.val.val.submatrix id (V.ε ∘ .inr)).map
          (adeleExtension (weightEmbedding (ιₚ.comp conj) τ))) *ᵥ ιₚ.comp conj ∘ star η‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^ (∑ τ : NumberField.InfinitePlace E,
          card m * (range (card m)).sum (O.colsMinus τ)) *
        weylGauge (ι := ⟨ιₚ.comp conj⟩) O.colsMinus 0 h' (star η) :=
    V.norm_schur_inv_cols_le_weylGauge (ι := ⟨ιₚ.comp conj⟩) (S := univ) hM L V.hasColumnsBelow.2
      ⟨1, fun _ _ h ↦ (h (mem_univ _)).elim⟩ <| by
      rw [← map_inv, Prod.inv_mk, U.block_val]
      refine Matrix.ext fun i j ↦ ?_
      obtain ⟨i' | i', rfl⟩ := V.ε.surjective i
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, ↓reduceIte, zero_mul, Finset.sum_const_zero]
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₂₂, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  -- Move the action of `g⁻¹` into `cartanProduct` (`weylRep_mulVec_cartanProduct`) and split the
  -- power of `M` by blocks.
  have hη : ιₚ ∘ η = ιₚ.comp conj ∘ star η :=
    funext fun x ↦ congrArg ιₚ (star_star (η x)).symm
  rw [weylGauge, map_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2 (f := ιₚ), hη]
  change ‖weylRep (mixedWeight n O.colsPlus O.colsMinus)
      (fun τ : NumberField.InfinitePlace E ↦ -∑ i ∈ Finset.Ico 1 (card n), O.colsMinus τ i) _ *ᵥ
    _‖ ≤ _
  rw [weylRep_mulVec_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2]
  rw [denominatorExponent, sum_add_distrib, pow_add, mul_mul_mul_comm]
  refine (norm_mulVec_le (c := 1) (by simp [norm_intCast_le_one]) _).trans
    ((one_mul _).trans_le ?_)
  -- `g` is unitary, so the transpose of `g` is the conjugate of `g⁻¹`, and conjugation on `E`
  -- turns the conjugate embedding back into the given one.
  have h_conj (τ : NumberField.InfinitePlace E) :
      (weightEmbedding (E := E) (ιₚ.comp conj) τ).comp conj = weightEmbedding ιₚ τ :=
    RingHom.ext (by simp [starRingEnd_apply (R := E)])
  have h_transpose (τ : NumberField.InfinitePlace E) :
      ((GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ))
          g⁻¹.val)⁻¹).valᵀ.submatrix id (V.ε ∘ .inr) =
        (g⁻¹.val.val.submatrix id (V.ε ∘ .inr)).map
          (adeleExtension (weightEmbedding (ιₚ.comp conj) τ)) := by
    rw [U.inv_val_eq_conjTranspose]
    ext i j
    exact ((adeleExtension_star ..).trans (by rw [h_conj]; rfl)).symm
  exact norm_mul_le_of_le ((pi_norm_comp_le (_ *ᵥ _) _).trans h_big)
    ((pi_norm_comp_le (_ *ᵥ _) _).trans (by simpa only [h_transpose] using h_small))

end New.Rows.DividedSplitting

end
end
end

/-!
# The first factors and the gluing maps

The first factors `φ″_{ϑ,i}` on `V″` are integral away from `Q` and small for `ϑ = 1`, and their
theta series satisfy `c′_ϑ Ξ_{ϑ,i} = c″ 𝖥_i` with functions `𝖥_i` that do not depend on the twist.
Gluing them to forms on `V°` gives the map `glue_ϑ` to forms on `V_j`. Its adjoint, the period,
satisfies `c′_ϑ glue_ϑ* Θ_{j,ϑ} = Θ°`, where `Θ°` does not depend on the twist and is injective,
because products span. The map `glue_ϑ` keeps integrality away from `Q`, is short for `ϑ = 1`, and
takes the image of `Θ°` to forms orthogonal to the false lifts. The comparison operator, an integer
multiple of `glue_ϑ glue_ϑ*`, is built from it in `New.OneLift.LiftVolumeHeight`.

In the code `φ″` is `firstFactor`, `Ξ` is `firstFactorPairing`, `𝖥` is `choiceFn`, `glue_ϑ` is
`glue j ϑ` and `Θ°` is `periodLift`. The integer `M` is `D.M`, its factor `ϖ` is `D.piM`, and `Q` is
the set of places of the twist `ϑ`.

Notions from other files:
* `descentPair ϑ j`: the spaces `W_j` and `V_j` with the characters and levels for the twist `ϑ`;
  `untwistedDescentPair j` is its untwisted form. The diagram of the values of the forms on `V″` is
  `μ⁺` (`colsPlus`), that on `V°` is `μ⁻` (`colsMinus`).
* `ChoiceIndex j`: the choices `i`, each a matrix `Λ` with a class `h♭` and constant rows.
* `FirstFactorIndex j` indexes the basis of `V″`, `D.SecondFactorIndex` that of `V°`, and
  `D.SecondFactorClasses` is the set of classes of `U(V°)` at the level `J (ϖ²)`.
* `goodLift ϑ j`: the theta lift `Θ_{j,ϑ}` from good forms on `W_j` to forms on `V_j`.
* `normalizedDescent`: the descent, which sends a form on `V_j` to a function on `U(W_j)` by pairing
  it with the theta kernel over the classes of `U(V_j)`.
* `weylGauge`, `weylNormSq`: the gauge at a place over `l` and the squared norm of a vector in a
  representation given by a diagram.

## Relation to the literature

Integral forms pairing with a lift to an explicit L-value (pullback, seesaw) are known in the
literature in low rank.

Related work: Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; Y.-S. Lee,
Hida family of theta lift from U(1) to definite U(2), 2024; Prasanna, Integrality of a ratio of
Petersson norms and level-lowering congruences, 2006.
-/

@[expose] public section

noncomputable section

namespace New.Rows

open Finset Real ComplexConjugate Data WeilData Submodule Function.Embedding MeasureTheory

open LinearMap Fintype LevelPlaces DescentPair

variable {P : Parameters} {D : Data P} (j : D.LiftIndex)

/-! ### Tuples of forms on `V°`, the splitting and the lattices -/

/-- The hook number `hk` of the diagram `μ⁻`, which gives the weight of the forms on `V°`. -/
abbrev hookNumberMinus : ℤ :=
  hookNumber (untwistedDescentPair j).colsMinus (rankAt fun _ ↦ D.SecondFactorIndex)

/-- The values of the forms on `V°`, with the invariant metric. -/
@[implicit_reducible] def SecondFactorFormValues : Type :=
  WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℂ

instance : NormedAddCommGroup (SecondFactorFormValues j) :=
  Matrix.toNormedAddCommGroup _ weylGramOver_posDef

instance : InnerProductSpace ℂ (SecondFactorFormValues j) := .ofCore (F := _ → ℂ) _

instance : Module.Finite ℂ (SecondFactorFormValues j) := .pi

/-- `𝒜^⊕`: one copy of the forms on `V°` for each choice. The level `J (ϖ²)` is sufficiently small
(all stabilisers of classes are trivial), so a form is the table of its values at representatives
of the classes, and an inner product is a plain sum over the classes. -/
abbrev _root_.New.Data.FormTuples : Type := PiLp 2 fun _ : ChoiceIndex j × D.SecondFactorClasses ↦
  SecondFactorFormValues j

variable {j} in
/-- A tuple of forms on `V°` is integral at the place `φ` over `l` if all its values are, that is,
have `weylGauge` at most `1`. A matrix acts on the values by its inverse transpose, so the gauge is
that of the conjugate vector at the conjugate place. -/
def IsIntegralFormTuple {l : ℕ} [Fact l.Prime] (φ : PadicPlace l) (ζ : FormTuples j) : Prop :=
  ∀ b : ChoiceIndex j × D.SecondFactorClasses,
    weylGauge (ι := ⟨φ.ιₚ.comp conj⟩) (untwistedDescentPair j).colsMinus 0 b.2.out (star (ζ b)) ≤ 1

variable {j} in
/-- The squared norm `‖ζ‖_σ²` of a tuple of forms on `V°`: a plain sum over the classes. -/
def formTupleNormSq (σ : ℂ ≃+* ℂ) (ζ : FormTuples j) : ℝ :=
  ∑ b : ChoiceIndex j × D.SecondFactorClasses, weylNormSq (σ ∘ ζ b)

/-- The rank `r + 9 m + 1` of `V″` is at most `2 n_m`. -/
lemma card_firstFactorIndex_le_two_mul_n : card (FirstFactorIndex j) ≤ 2 * D.n D.m := by
  rw [card_firstFactorIndex]
  linarith only [D.six_mul_r_le_n, D.r_add_one, D.hundred_mul_m_add_nine_lt_k]

variable (D) in
/-- The rank `r + t = 6 r` of `V_j` is at most `2 n_m`. -/
lemma card_rowIndex_sum_fin_le_two_mul_n : card (D.RowIndex ⊕ Fin D.t) ≤ 2 * D.n D.m := by
  rw [D.card_rowIndex_sum_fin]
  linarith only [D.six_mul_r_le_n, D.t_eq_five_mul_r]

/-- The basis of `V″` is large enough to hold the divided directions: `D.CarrierIndex` embeds in
`FirstFactorIndex j`. -/
lemma nonempty_carrierIndex_embedding_firstFactorIndex :
    Nonempty (D.CarrierIndex ↪ FirstFactorIndex j) := by
  refine nonempty_of_card_le ?_
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- If `card N ≤ card n` and the diagram `κ` has no column of height at least `card N`, then
`HasColumnsBelow n N κ` holds. -/
lemma hasColumnsBelow_of_eq_zero {Φ n N : Type} [Fintype n] [Fintype N] {κ : Φ → ℕ → ℕ}
    (h_card : card N ≤ card n) (h_zero : ∀ (τ : Φ) (h : ℕ), card N ≤ h → κ τ h = 0) :
    HasColumnsBelow n N κ := by
  refine ⟨fun τ ↦ ⟨h_card, fun h h_mem ↦ h_zero τ h (mem_Ioo.1 h_mem).1.le⟩, funext fun τ ↦ ?_⟩
  simp [schurDetExp, h_zero τ (card N) le_rfl]

/-- The indices of `V″ ⊕ V°` other than those of `W_j` in `V″` are `t` in number. -/
lemma card_padIndex_sum_flatIndex_sum_secondFactorIndex :
    card (PadIndex j ⊕ D.FlatIndex ⊕ D.SecondFactorIndex) = D.t := by
  have k_large : 100 * D.m + 9 < D.k := D.hundred_mul_m_add_nine_lt_k
  have r_add_one : D.r + 1 = D.k + D.m := D.r_add_one
  have t_eq : D.t = 5 * D.r := D.t_eq_five_mul_r
  have j_le : j.val ≤ D.m := j.property.2
  simp only [Fintype.card_sum, Fintype.card_fin, D.card_rowIndex]
  omega

variable (ϑ : D.Twist)

/-- For the `j`-th pair `W_j, V_j` and the summand `V″` of `V_j` with basis `FirstFactorIndex j`:
the rank of `V″` is at most that of `V_j`, and the diagram `μ⁺`, given by its numbers `colsPlus τ h`
of columns of height `h` at the infinite place `τ`, has no column whose height is at least the rank
of `V″` and below the rank of `V_j`. -/
lemma hasColumnsBelow_colsPlus :
    HasColumnsBelow (D.RowIndex ⊕ Fin D.t) (FirstFactorIndex j) (D.descentPair ϑ j).colsPlus := by
  have k_large : 100 * D.m + 9 < D.k := D.hundred_mul_m_add_nine_lt_k
  have r_add_one : D.r + 1 = D.k + D.m := D.r_add_one
  refine hasColumnsBelow_of_eq_zero ?_ fun τ h h_le ↦ ?_
  · have t_eq : D.t = 5 * D.r := D.t_eq_five_mul_r
    rw [card_firstFactorIndex, D.card_rowIndex_sum_fin]
    omega
  · -- the entry `h - 1` of the row parameter lies below `-w_j`
    have h_rank : D.posRank j ≤ h - 1 := by
      have j_le : j.val ≤ D.m := j.property.2
      rw [card_firstFactorIndex] at h_le
      rw [posRank]
      omega
    have h_below : D.targetParameter τ (h - 1) + D.liftWeight j τ ≤ -D.halfGap :=
      D.targetParameter_add_liftWeight_le_neg_halfGap τ h_rank
    simp only [descentPair]
    omega

/-- For `D.descentPair ϑ j`, its diagram `μ⁻` (`colsMinus`) satisfies `HasColumnsBelow`: the rank of
`V°` is at most that of `V_j` (`D.RowIndex ⊕ Fin D.t`), and `μ⁻` has no column whose height is at
least the rank of `V°` and below the rank of `V_j`. -/
lemma hasColumnsBelow_colsMinus :
    HasColumnsBelow (D.RowIndex ⊕ Fin D.t) D.SecondFactorIndex (D.descentPair ϑ j).colsMinus := by
  refine hasColumnsBelow_of_eq_zero ?_ fun τ h h_le ↦ ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · -- as `r ≤ h`, both entries of the row parameter in the formula are the entry `0`
    have h_index : D.r - h - 1 = D.r - h := by
      rw [Fintype.card_sum, D.card_rowIndex] at h_le
      omega
    simp only [descentPair, h_index]
    omega

/-- The splitting `V_j = V″ ⊕ V°` of the basis, for the pair `descentPair ϑ j`. The indices of `W_j`
come first in `V″`. The divided directions are given by an arbitrary embedding of `D.CarrierIndex`
in `FirstFactorIndex j`. The splitting and both embeddings in `FirstFactorIndex j` do not depend on
the twist. -/
def splittingV : DividedSplitting (FirstFactorIndex j) D.SecondFactorIndex D.CarrierIndex
  (D.descentPair ϑ j)
    Function.Embedding.inl where
  -- keep the indices of `W_j`, which come first in `V″`, and number the remaining ones
  ε := (Equiv.sumAssoc ..).trans <| (Equiv.sumAssoc ..).trans <|
    Equiv.sumCongr 1 (Fintype.equivFinOfCardEq
      (card_padIndex_sum_flatIndex_sum_secondFactorIndex j))
  fixedEmb := inl.trans Function.Embedding.inl
  equiv_inl_fixedEmb _ := rfl
  dividedEmb := (nonempty_carrierIndex_embedding_firstFactorIndex j).some
  hasColumnsBelow := ⟨hasColumnsBelow_colsPlus j ϑ, hasColumnsBelow_colsMinus j ϑ⟩

/-- The level `J_Λ` on `V″` of a matrix `Λ` modulo `ϖ²`. It is `rowFixingLevel` for the rows of `Λ`
and of `ϖ • 1`: its elements are `1` modulo `ϖ` and fix `Λ` modulo `ϖ²`, and modulo `ϖ² Q`, for `Q`
the product of the twist places, their columns off the indices of `W_j` are those of the identity
matrix. -/
abbrev gluingLevel
    (Λ : Matrix D.CarrierIndex (FirstFactorIndex j)
      (D.descentPair ϑ j).chosenModulusSq.ResidueRing) :
    Subgroup (Gf D.E (FirstFactorIndex j)) :=
  rowFixingLevel (D.descentPair ϑ j).toLevelPlaces ((splittingV j ϑ).stackOverGenScalar Λ)
    (splittingV j ϑ).fixedEmb

/-- The level `J_Λ` (`gluingLevel`) is sufficiently small: at every point `g` the stabiliser
`classAut` is trivial. -/
lemma classAut_gluingLevel_eq_bot
    (Λ : Matrix D.CarrierIndex (FirstFactorIndex j) (D.descentPair ϑ j).chosenModulusSq.ResidueRing)
    (g : Gf D.E (FirstFactorIndex j)) :
    classAut (stdSpace D.E (FirstFactorIndex j)).embFin.range (gluingLevel j ϑ Λ) g = ⊥ := by
  have h_le : gluingLevel j ϑ Λ ≤ D.chosenLevel := rowFixingLevel_le_levelOf (splittingV j ϑ) Λ
  exact D.classAut_eq_bot_of_le_chosenLevel h_le (card_firstFactorIndex_le_two_mul_n j) g

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- The lattice `L_Λ` of a choice `i` with matrix `Λ = i.1`, given by the matrix `𝗀` (the field
`point`) of a basis. It is chosen once, for the trivial twist, and read as a lattice for the twist
`ϑ`. -/
def glueLattice (i : ChoiceIndex j) : DividedLattice (D.descentPair ϑ j) :=
  { ((splittingV j 1).exists_isGlued i.1).choose with }

/-- A lattice that is glued for the twist `ϑ'` is glued for the twist `ϑ`. -/
lemma isGlued_splittingV_of_isGlued {ϑ' : D.Twist}
    {Λ : Matrix D.CarrierIndex (FirstFactorIndex j) (D.descentPair ϑ'
      j).chosenModulusSq.ResidueRing}
    {L : DividedLattice (D.descentPair ϑ' j)} (hL : (splittingV j ϑ').IsGlued Λ L) :
    (splittingV j ϑ).IsGlued Λ { L with } :=
  -- the conditions on a lattice do not involve the twist, up to unfolding
  { hL with }

/-- The lattice `glueLattice j ϑ i` is glued for the matrix `Λ = i.1` (`IsGlued`): the congruence
modulo `ϖ` that defines it is, after a translation by a unique element of `congruenceGroup`, a
pair of conditions on the blocks `V″` and `V°`, and its inverse is integral on most of `V″`. -/
lemma isGlued_glueLattice (i : ChoiceIndex j) : (splittingV j ϑ).IsGlued i.1 (glueLattice j ϑ i) :=
  isGlued_splittingV_of_isGlued j ϑ ((splittingV j 1).exists_isGlued i.1).choose_spec

/-! ### The first factors -/

/-- The constant `c″ ≠ 0` that makes the vectors `c″ Υ_{ϑ,i} (h)` integral away from `Q`, and small
for `ϑ = 1`. Here `Υ_{ϑ,i}` is `leftSideSeries`, a theta kernel times a class sum of theta kernels
formed from the choice `i`. The constant depends neither on the twist nor on the choice. -/
def firstFactorScale : ℂ := (exists_isIntegralAndSmall_leftSideSeries j).choose

lemma firstFactorScale_ne_zero : firstFactorScale j ≠ 0 :=
  (exists_isIntegralAndSmall_leftSideSeries j).choose_spec.1

/-- The first factor `φ″_{ϑ,i}`, the complex conjugate of `c″ Υ_{ϑ,i}`, where `Υ_{ϑ,i}`
(`leftSideSeries`) is a function on the finite points of `U(V″)` and `c″ = firstFactorScale j`. -/
def firstFactor (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) :
    WeylIndex (FirstFactorIndex j) (untwistedDescentPair j).colsPlus → ℂ :=
  star (firstFactorScale j • leftSideSeries ϑ j i h)

/-- The theta series `Ξ_{ϑ,i} (g) = ⟨φ″_{ϑ,i}, θ″_{ϑ,Λ} (g, ·)⟩` on `U(W_j)`. It is the sum
(`kernelClassSum`) over the classes `h` of level `J_Λ` of the theta kernel `θ″_{ϑ,Λ}` of
`(W_j, V″)` at `(g, h)`, with datum given by the rows of `Λ` stacked over those of `ϖ • 1`
(`stackOverGenScalar`) and polynomial given by `φ″_{ϑ,i} (h)`. -/
def firstFactorPairing (i : ChoiceIndex j) (g : G D.E (D.signsW j)) : ℂ :=
  kernelClassSum (D.descentPair ϑ j) (firstFactorChar ϑ j) ((splittingV j ϑ).stackOverGenScalar i.1)
    (splittingV j ϑ).fixedEmb (fun h ↦ star (firstFactor j ϑ i h)) g

/-- The series `Ξ_{ϑ,i}` is `c″` times the left side `thirdExchangeLeftSide` of the third exchange,
the class sum over `U(V″)` whose multiple by a number is the twist-free function `choiceFn`. -/
lemma firstFactorPairing_eq_mul_thirdExchangeLeftSide (i : ChoiceIndex j) (g : G D.E (D.signsW j)) :
    firstFactorPairing j ϑ i g = firstFactorScale j * thirdExchangeLeftSide ϑ j i g := by
  have h_star : (fun h : Gf D.E (FirstFactorIndex j) ↦ star (firstFactor j ϑ i h)) =
      fun h ↦ firstFactorScale j • leftSideSeries ϑ j i h := funext fun h ↦ star_star _
  rw [firstFactorPairing]
  -- rewrite by `h_star` with `congrArg`, as the motive of `rw` is not type correct
  refine ((congrArg (kernelClassSum (D.descentPair ϑ j) (firstFactorChar ϑ j) _ _ · g) h_star).trans
    (kernelClassSum_smul (O := D.descentPair ϑ j) ..)).trans
    (congrArg (firstFactorScale j * ·)
      (thirdExchangeLeftSide_eq_kernelClassSum ϑ j (u := Matrix.fromCols 1 0) ?_ g).symm)
  exact (Matrix.fromCols_mul_fromRows 1 0 i.1 _).trans
    ((congrArg₂ (· + ·) (Matrix.one_mul i.1) (Matrix.zero_mul (l := D.CarrierIndex) _)).trans
      (add_zero _))

/-- Let `y` be a good form on the hermitian space `W_j = D.spaceW j`. The theta series
`firstFactorPairing j ϑ i` on `U(W_j)` of a twist `ϑ` and a choice `i` is a finite combination of
theta kernels, so its product with `y` is a rapidly decreasing automorphic function. -/
lemma mul_firstFactorPairing_mem_rapidFunctions (y : D.goodForms (D.spaceW j)) (i : ChoiceIndex j) :
    (y : G D.E (D.signsW j) → ℂ) * firstFactorPairing j ϑ i ∈ (D.spaceW j).rapidFunctions := by
  obtain ⟨hy, -⟩ := goodForms_mem_rapidOfLevel y dvd_rfl
  have h_tame (w : FinPlace D.E) (hw : w ∉ ((D.descentPair ϑ j).levelModulus 2).places) :
      (D.descentPair ϑ j).tamePart w = 1 :=
        (D.descentPair ϑ j).tame_eq_one w (places_levelModulus.ge.mt hw)
  -- the class sum is a finite sum of multiples of the products of `y` with a theta kernel
  simp only [firstFactorPairing, kernelClassSum, classSum, finsum_eq_sum_of_fintype, Pi.mul_def,
    Finset.mul_sum, mul_smul_comm, ← Finset.sum_fn]
  refine (D.spaceW j).rapidFunctions.toSubmodule.sum_mem fun h _ ↦ ?_
  rw [← Pi.smul_def]
  exact Submodule.smul_of_tower_mem _ _
    (mul_modKernel_mem_rapidFunctions inferInstance h_tame hy _ _ (1, h.out))

/-- The theta series `firstFactorPairing j ϑ i` on `U(W_j)` depends on the twist `ϑ` only through a
scalar: there are numbers `c ϑ` such that `c ϑ` times the series is `firstFactorScale j` times the
function `choiceFn j i`, neither of which involves `ϑ`, for all choices `i`. Moreover `|c ϑ|²` is a
constant `C`, possibly `0`, divided by `heckeValueProd j ϑ`, a product of three Hecke L-value
factors twisted by `ϑ`. -/
lemma exists_mul_firstFactorPairing_eq : ∃ (C : ℂ) (c : D.Twist → ℂ), ∀ ϑ : D.Twist,
    ‖c ϑ‖ ^ 2 = C / heckeValueProd j ϑ ∧
    ∀ (i : ChoiceIndex j) (g : G D.E (D.signsW j)),
      c ϑ * firstFactorPairing j ϑ i g = firstFactorScale j * choiceFn j i g := by
  obtain ⟨C, c, h_third⟩ := exists_mul_thirdExchangeLeftSide_eq_choiceFn j
  refine ⟨C, c, fun ϑ : D.Twist ↦ ?_⟩
  obtain ⟨h_norm, h_eq⟩ := h_third ϑ
  refine ⟨h_norm, fun i g ↦ ?_⟩
  calc c ϑ * firstFactorPairing j ϑ i g = firstFactorScale j *
         (c ϑ * thirdExchangeLeftSide ϑ j i g) := by
        rw [firstFactorPairing_eq_mul_thirdExchangeLeftSide, mul_left_comm]
    _ = firstFactorScale j * choiceFn j i g := by rw [h_eq]

/-- The number `c′_ϑ` with `c′_ϑ Ξ_{ϑ,i} = c″ 𝖥_i` for all `i`. -/
def twistFactor : D.Twist → ℂ := (exists_mul_firstFactorPairing_eq j).choose_spec.choose

/-- There is a constant `C`, possibly `0`, with `|c′_ϑ|² = C / heckeValueProd j ϑ` for every twist
`ϑ`; the denominator is the product of the Hecke values of the three exchanges. -/
lemma exists_norm_twistFactor_sq_eq :
    ∃ C : ℂ, ∀ ϑ : D.Twist, ‖twistFactor j ϑ‖ ^ 2 = C / heckeValueProd j ϑ :=
  ⟨_, fun ϑ ↦ ((exists_mul_firstFactorPairing_eq j).choose_spec.choose_spec ϑ).1⟩

/-- The defining equation `c′_ϑ Ξ_{ϑ,i} (g) = c″ 𝖥_i (g)` of `twistFactor`, where `𝖥_i`
(`choiceFn`) is a function on `U(W_j)` that does not depend on the twist. -/
lemma twistFactor_mul_firstFactorPairing (i : ChoiceIndex j) (g : G D.E (D.signsW j)) :
    twistFactor j ϑ * firstFactorPairing j ϑ i g = firstFactorScale j * choiceFn j i g :=
  ((exists_mul_firstFactorPairing_eq j).choose_spec.choose_spec ϑ).2 i g

/-- The values of the first factor `φ″_{ϑ,i}` are integral away from the level of `ϑ`, and, if `Q`
is empty, their conjugates have squared norm at most `exp (f m b log² b)` (`IsIntegralAndSmall`). -/
lemma isIntegralAndSmall_firstFactor (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) :
    IsIntegralAndSmall ϑ j h (firstFactor j ϑ i h) :=
  (exists_isIntegralAndSmall_leftSideSeries j).choose_spec.2 i ϑ h

/-- Arithmetic of the first factors: the value of `φ″_{ϑ,i}` at `h` is integral (`weylGauge` at
most `1`) at a place above a prime `l` that does not divide the norm of the level of `ϑ`. -/
lemma weylGauge_firstFactor_le_one (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) (l : ℕ)
    [Fact l.Prime] [PadicPlace l] (hl : l.Coprime ϑ.toTameChar.normQ) :
    weylGauge (untwistedDescentPair j).colsPlus 0 h (firstFactor j ϑ i h) ≤ 1 :=
  (isIntegralAndSmall_firstFactor j ϑ i h).weylGauge_le_one l hl

/-- Arithmetic of the first factors: for the trivial twist, every conjugate
`σ ∘ firstFactor j 1 i h` of the values of `φ″_{1,i}` has squared norm (`weylNormSq`) at most
`exp (D.f * D.m * D.b * D.logB ^ 2)`. -/
lemma weylNormSq_firstFactor_le (i : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j))
    (σ : ℂ ≃+* ℂ) :
    weylNormSq (σ ∘ firstFactor j 1 i h) ≤ exp (D.f * D.m * D.b * D.logB ^ 2) :=
  (isIntegralAndSmall_firstFactor j 1 i h).weylNormSq_le rfl σ

/-! ### The gluing map and the slices of lifts -/

/-- The gluing map `glue_ϑ`. For `ζ` in the copy `i` of the forms on `V°` it is `M ^ l₁` times the
sum, over the classes `h` of level `J_Λ` and `h°` of level `J (ϖ²)`, of the forms supported on the
class of `(h, h°) 𝗀` formed from the product vector `φ″ (h) · ζ (h°)` (`productForm`). Here `𝗀`
is the matrix of `glueLattice j ϑ i`, `M = D.M`, and `l₁` is
`DividedSplitting.denominatorExponent`, the exponent that repays the denominators of `𝗀`. -/
@[simps -isSimp] def glue : FormTuples j →ₗ[ℂ] (D.descentPair ϑ j).FormV where
  toFun ζ := (D.M ^ (splittingV j ϑ).denominatorExponent : ℂ) • ∑ b :
    ChoiceIndex j × D.SecondFactorClasses,
    stdClassSum (gluingLevel j ϑ b.1.1) fun h : Gf D.E (FirstFactorIndex j) ↦
      (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h) (ζ b)
  map_add' x y := by
    have h_sum_add {K : Subgroup (Gf D.E (FirstFactorIndex j))} [IsLevel K]
        (f g : Gf D.E (FirstFactorIndex j) → (D.descentPair ϑ j).FormV) :
        stdClassSum K (fun h ↦ f h + g h) = stdClassSum K f + stdClassSum K g := by
      simp only [classSum, finsum_eq_sum_of_fintype, smul_add, sum_add_distrib]
    rw [← smul_add, ← sum_add_distrib]
    refine congrArg _ (sum_congr rfl fun b _ ↦ ?_)
    have h_pt (h : Gf D.E (FirstFactorIndex j)) :
        (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h)
            ((x + y) b) =
          (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h)
            (x b) +
          (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h)
            (y b) :=
      map_add _ (x b : WeylIndex _ (D.descentPair ϑ j).colsMinus → ℂ) (y b)
    exact (congrArg (stdClassSum _) (funext h_pt)).trans (h_sum_add _ _)
  map_smul' a x := by
    have h_sum_smul {K : Subgroup (Gf D.E (FirstFactorIndex j))} [IsLevel K]
        (f : Gf D.E (FirstFactorIndex j) → (D.descentPair ϑ j).FormV) :
        stdClassSum K (fun h ↦ a • f h) = a • stdClassSum K f := by
      simp only [classSum, finsum_eq_sum_of_fintype, smul_comm a, smul_sum]
    rw [RingHom.id_apply, smul_comm a]
    congr 1
    rw [smul_sum]
    refine sum_congr rfl fun b _ ↦ ?_
    have h_pt (h : Gf D.E (FirstFactorIndex j)) :
        (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h)
            ((a • x) b) =
          a • (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out)
            (firstFactor j ϑ b.1 h) (x b) :=
      map_smul _ a (x b : WeylIndex _ (D.descentPair ϑ j).colsMinus → ℂ)
    exact (congrArg (stdClassSum _) (funext h_pt)).trans (h_sum_smul _)

/-- The period is a sum of slices. Let `φ` be a form on `V_j = V″ ⊕ V°` and `ζ` a tuple of forms on
`V°`. The inner product of `ζ` with the adjoint of the gluing map `glue j ϑ` at `φ` is `M ^ l₁`
(`M = D.M`, `l₁ = denominatorExponent`) times the sum, over the choices `i` with matrix `Λ = i.1`,
the classes `c` of `U(V°)` with representative `h° = c.out` and the classes `h` of `U(V″)` of level
`J_Λ = gluingLevel j ϑ Λ` (`stdClassSum`), of `⟨φ″ (h) · ζ (i, c), φ ((h, h°) 𝗀)⟩` (`gramForm`).
Here `φ″ = firstFactor j ϑ i`, `ε` splits the basis of `V_j` into those of `V″` and `V°`, the
product of vectors is `cartanProduct ε 1`, the point `(h, h°)` is the block matrix
`U.block ε (h, h°)`, and `𝗀` is the matrix of the lattice `glueLattice j ϑ i`. -/
lemma inner_adjoint_glue (φ : (D.descentPair ϑ j).FormV) (ζ : FormTuples j) :
    inner ℂ ζ ((glue j ϑ).adjoint φ) =
      D.M ^ (splittingV j ϑ).denominatorExponent * ∑ i : ChoiceIndex j, ∑ c : D.SecondFactorClasses,
        stdClassSum (gluingLevel j ϑ i.1) fun h : Gf D.E (FirstFactorIndex j) ↦
          gramForm (cartanProduct (splittingV j ϑ).ε 1 (firstFactor j ϑ i h) (ζ (i, c)))
            (φ (U.block (splittingV j ϑ).ε (h, c.out) * (glueLattice j ϑ i).point)) := by
  have h_sum {K : Subgroup (Gf D.E (FirstFactorIndex j))} [IsLevel K]
      (f : Gf D.E (FirstFactorIndex j) → (D.descentPair ϑ j).FormV)
      (g : Gf D.E (FirstFactorIndex j) → ℂ) (hfg : ∀ h, inner ℂ (f h) φ = g h) :
      inner ℂ (stdClassSum K f) φ = stdClassSum K g := by
    simp only [classSum, finsum_eq_sum_of_fintype, sum_inner]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ, inner_smul_left,
      map_ratCast, hfg, smul_eq_mul]
  rw [adjoint_inner_right, glue_apply, inner_smul_left, map_pow, map_natCast, sum_inner,
    sum_prod_type]
  refine congrArg _ (sum_congr rfl fun i _ ↦ sum_congr rfl fun c _ ↦ h_sum _ _ fun h ↦ ?_)
  exact inner_classForm _ _ _

/-- The character of the lift to `V_j = V″ ⊕ V°`: the product of `ν″ = firstFactorChar` and
`ν° = ν_η ^ (m / 2 - j)` is the character `charV` of `descentPair ϑ j`. All are characters of
`U(1)`, and `ν_η = upsilonU1` is the restriction of the character `υ` to the norm-one ideles. -/
lemma firstFactorChar_mul_upsilonU1_zpow :
    firstFactorChar ϑ j * upsilonU1 ^ (D.m / 2 - j : ℤ) = (D.descentPair ϑ j).charV := by
  -- `m` is even and `k - 1 = r - m`
  have h_exp : (j + (5 * D.r + D.k - 1) / 2 + (D.m / 2 - j) : ℤ) = (D.r + 5 * D.r) / 2 := by
    grind [D.m_eq_two_mul_varrho_add_two, D.r_add_one]
  have t_eq : D.t = 5 * D.r := D.t_eq_five_mul_r
  simp [firstFactorChar, firstFactorCharExp, rankTwist, mul_assoc, ← zpow_natCast, ← zpow_add, t_eq,
    D.card_rowIndex, h_exp]
  -- what remains, `D.liftChar = μ`, is the definition of `descentPair`
  rfl

/-- A good form on `W_j` is invariant under the lifts `liftMod 𝗎` of the elements `𝗎` of the group
`J̄¹` (`congruenceGroup`) of matrices modulo `ϖ²` that are `1` modulo `ϖ`, since these lifts lie in
the level `J (ϖ)` that fixes it. -/
lemma goodForm_mul_liftMod_congruenceGroup (y : D.goodForms (D.spaceW j))
    (u : (splittingV j 1).congruenceGroup) (g : G D.E (D.signsW j)) :
    (y : G D.E (D.signsW j) → ℂ) (g * (1, (liftMod u.val : Gf D.E D.RowIndex))) =
      (y : G D.E (D.signsW j) → ℂ) g := by
  have h_level : (liftMod u.val : Gf D.E D.RowIndex) ∈ levelOf D.chosenPlace ⊥ :=
    mem_levelOf.2 ⟨(liftMod u.val).prop,
      funext ((splittingV j 1).reduceAt_liftMod_congruenceGroup u)⟩
  exact Space.mem_levelSpace_formRep_iff.1 (y : D.principalForms (D.spaceW j)).prop _ h_level g

open scoped Classical in
/-- The descent to `U(W_j)` of the form `glue j ϑ ζ` on `V_j` glued from a tuple `ζ` of forms on
`V°` at the twist `ϑ`. Its conjugate at `g` is the sum, over the choices `i` and the matrices `u`
modulo `ϖ²` that are `1` modulo `ϖ` (`congruenceGroup`), of `M ^ l₁ c Ξ_i (g u) ⟨ζ_i, θ° (g u, ·)⟩`.
Here `M = D.M`, `l₁ = denominatorExponent`, `c` is the scalar `weilScalar` of the lattice of `i`,
`Ξ_i` is the theta series `firstFactorPairing j ϑ i`, the last factor is the pairing
`thetaKernelPairing` of the copy `i` of `ζ` with the theta kernel `θ°` of `W_j, V°`, and `g u` is
`g` times the lift `liftMod u`. -/
lemma conj_normalizedDescent_glue (ϑ' : D.Twist) (ζ : FormTuples j) (g : G D.E (D.signsW j)) :
    conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) =
      ∑ i : ChoiceIndex j, ∑ u : (splittingV j ϑ').congruenceGroup,
        D.M ^ (splittingV j ϑ').denominatorExponent * (glueLattice j ϑ' i).weilScalar *
          (firstFactorPairing j ϑ i *
            thetaKernelPairing j fun c : D.SecondFactorClasses ↦ ζ (i, c))
              (g * (1, (liftMod u.val : Gf D.E D.RowIndex))) := by
  -- The descent of one term of `glue ζ` is a sum over `u` of products of two kernels.
  let Ξ (b : ChoiceIndex j × D.SecondFactorClasses) : (D.descentPair ϑ j).FormV :=
    stdClassSum (gluingLevel j ϑ b.1.1) fun h : Gf D.E (FirstFactorIndex j) ↦
      (splittingV j ϑ).productForm (glueLattice j ϑ b.1) (h, b.2.out) (firstFactor j ϑ b.1 h) (ζ b)
  let gu (u : (splittingV j ϑ').congruenceGroup) : G D.E (D.signsW j) :=
    g * (1, (liftMod u.val : Gf D.E D.RowIndex))
  let θ (b : ChoiceIndex j × D.SecondFactorClasses) (g' : G D.E (D.signsW j)) : ℂ :=
    modKernelStdSpace (D.spaceW j) (untwistedDescentPair j).charW (upsilonU1 ^ (D.m / 2 - j : ℤ))
      (D.untwistedModulus 2) (Pi.single (inclMatrix (D.untwistedModulus 2).ResidueRing .inl) 1)
      (letterPoly (D.signsW j) (untwistedDescentPair j).numbering (-1)
        (untwistedDescentPair j).colsMinus (star (ζ b))) g' b.2.out
  have h_glue : glue j ϑ ζ = (D.M ^ (splittingV j ϑ').denominatorExponent : ℂ) • ∑ b, Ξ b :=
    glue_apply j ϑ ζ
  have h_term (b : ChoiceIndex j × D.SecondFactorClasses) :
      (D.descentPair ϑ j).normalizedDescent (Ξ b) g = conj ((glueLattice j ϑ' b.1).weilScalar *
        ∑ u, firstFactorPairing j ϑ b.1 (gu u) * θ b (gu u)) :=
    (splittingV j ϑ).normalizedDescent_stdClassSum_productForm (isGlued_glueLattice j ϑ b.1)
      (firstFactorChar_mul_upsilonU1_zpow j ϑ) b.2.out (firstFactor j ϑ b.1) (ζ b) g
  have h_pairing (i : ChoiceIndex j) (g' : G D.E (D.signsW j)) :
      thetaKernelPairing j (fun c ↦ ζ (i, c)) g' = ∑ c, θ (i, c) g' := rfl
  have h_descent : (D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g =
      (D.M ^ (splittingV j ϑ').denominatorExponent : ℂ) *
        ∑ b, (D.descentPair ϑ j).normalizedDescent (Ξ b) g := by
    rw [h_glue, map_smul, map_sum]
    exact congrArg (fun z : ℂ ↦ (D.M ^ (splittingV j ϑ').denominatorExponent : ℂ) * z)
      (Finset.sum_apply g univ fun b ↦ (D.descentPair ϑ j).normalizedDescent (Ξ b))
  simp only [h_descent, h_term, h_pairing, Pi.mul_apply, mul_sum, map_sum, map_mul,
    map_pow, map_natCast, Complex.conj_conj, sum_prod_type (α₂ := D.SecondFactorClasses), mul_assoc]
  exact sum_congr rfl fun i _ ↦ sum_comm

/-- Let `y` be a good form on `W_j`, `D.goodLift ϑ j y` its theta lift to `V_j` at the twist `ϑ`,
and `ζ` a tuple of forms on `V°`. The inner product of `ζ` with the adjoint of the gluing map
`glue j ϑ` at the lift is the integral, over `U(W_j)` modulo its rational points (`quotMeasure`), of
`y` against the conjugate of the descent `normalizedDescent` of `glue j ϑ ζ`, its pairing with the
theta kernel. -/
lemma inner_adjoint_glue_goodLift_eq_integral (y : D.goodForms (D.spaceW j)) (ζ : FormTuples j) :
    inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y)) =
      ∫ g : G D.E (D.signsW j), (y : G D.E (D.signsW j) → ℂ) g *
        conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) ∂(D.spaceW j).quotMeasure := by
  -- The lift of `y` is `∫ y(g) θ(g, ·) dg`, and `⟨θ(g, ·), glue ζ⟩` is the descent of `glue ζ`.
  set μ : Measure (G D.E (D.signsW j)) := (D.spaceW j).quotMeasure
  let θ (g : G D.E (D.signsW j)) : (D.descentPair ϑ j).FormV :=
    (D.descentPair ϑ j).vectorKernelForm g
  have h_lift : D.goodLift ϑ j y = ∫ g, (y : G D.E (D.signsW j) → ℂ) g • θ g ∂μ :=
    D.singleLift_eq_integral ϑ y.val
  have h_integrable : Integrable (fun g ↦ (y : G D.E (D.signsW j) → ℂ) g • θ g) μ :=
    (D.descentPair ϑ j).integrable_smul_vectorKernelForm (D.fitsParams_descentPair ϑ j) y.val.val
  have h_descent (g : G D.E (D.signsW j)) :
      (D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g = inner ℂ (θ g) (glue j ϑ ζ) :=
    (D.descentPair ϑ j).normalizedDescent_eq_inner_vectorKernelForm (glue j ϑ ζ) g
  rw [adjoint_inner_right, h_lift, ← integral_inner h_integrable]
  simp [h_descent, inner_smul_right]

/-- The product of a good form `y` on `W_j`, the series `Ξ_i = firstFactorPairing j ϑ i` and the
pairing `⟨ζ, θ° (g, ·)⟩` (`thetaKernelPairing`) is a rapidly decreasing automorphic function. -/
lemma mul_mul_thetaKernelPairing_mem_rapidFunctions (y : D.goodForms (D.spaceW j))
    (i : ChoiceIndex j) (ζ : D.SecondFactorClasses → SecondFactorFormValues j) :
    (y : G D.E (D.signsW j) → ℂ) * firstFactorPairing j ϑ i * thetaKernelPairing j ζ ∈
      (D.spaceW j).rapidFunctions := by
  -- the pairing is a finite sum of theta kernels
  simp only [funext (thetaKernelPairing.eq_1 j ζ), ← Finset.sum_fn, Finset.mul_sum]
  exact (D.spaceW j).rapidFunctions.toSubmodule.sum_mem fun c _ ↦
    mul_modKernel_mem_rapidFunctions (hasWeight_upsilonU1_zpow _) (by simp)
      (mul_firstFactorPairing_mem_rapidFunctions j ϑ y i) _ _ (1, c.out)

/-- Let `y` be a good form on `W_j`, `D.goodLift ϑ j y` its theta lift to `V_j` at the twist `ϑ`,
and `ζ` a tuple of forms on `V°` with one copy `ζ_i` for each choice `i`. The inner product of `ζ`
with the adjoint of the gluing map `glue j ϑ` at the lift is the sum over `i` of
`M ^ l₁ c #J̄¹ ∫ y (g) Ξ_i (g) ⟨ζ_i, θ° (g, ·)⟩ dg`. Here `M = D.M` is the principal level,
`l₁ = denominatorExponent`, `c` is the scalar `weilScalar` of the lattice of `i` and `J̄¹`
(`congruenceGroup`) the group of matrices modulo `ϖ²` that are `1` modulo `ϖ`, all taken at the
trivial twist `1`. The series `Ξ_i` is `firstFactorPairing j ϑ i`, `thetaKernelPairing` pairs with
the theta kernel `θ°` of `W_j, V°`, and `quotMeasure` integrates over the quotient of `U(W_j)` by
its rational points. -/
lemma inner_adjoint_glue_goodLift_eq_sum_integral (y : D.goodForms (D.spaceW j))
    (ζ : FormTuples j) :
    inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y)) =
      ∑ i : ChoiceIndex j, D.M ^ (splittingV j 1).denominatorExponent *
        (glueLattice j 1 i).weilScalar *
        Nat.card (splittingV j 1).congruenceGroup *
        ∫ g : G D.E (D.signsW j),
          (y : G D.E (D.signsW j) → ℂ) g * firstFactorPairing j ϑ i g *
            thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ ζ (i, c)) g
              ∂(D.spaceW j).quotMeasure := by
  classical
  -- Write the theta integral of `glue j ϑ ζ` against `y` as a sum over `i` and `𝗎 ∈ J̄¹` of
  -- translates of `a i * f i`. Translation does not change the integral, so both sides are the
  -- sum of `a i * ∫ f i` over all `i` and all `𝗎`.
  let V := splittingV j 1
  set μ : Measure (G D.E (D.signsW j)) := (D.spaceW j).quotMeasure
  let f (i : ChoiceIndex j) : G D.E (D.signsW j) → ℂ :=
    (y : G D.E (D.signsW j) → ℂ) * firstFactorPairing j ϑ i * thetaKernelPairing j fun c ↦ ζ (i, c)
  let a (i : ChoiceIndex j) : ℂ := D.M ^ V.denominatorExponent * (glueLattice j 1 i).weilScalar
  -- the point `(1, 𝗎)` of `U(W_j)` given by the lift of `𝗎 ∈ J̄¹`
  let k (u : V.congruenceGroup) : G D.E (D.signsW j) := (1, (liftMod u.val : Gf D.E D.RowIndex))
  -- The measure is invariant under right translation, so all `𝗎` give the same integral.
  have h_same (i : ChoiceIndex j) (u : V.congruenceGroup) :
      ∫ g, f i (g * k u) ∂μ = ∫ g, f i g ∂μ ∧ Integrable (fun g ↦ f i (g * k u)) μ := by
    obtain ⟨⟨h_cont, h_rat⟩, h_rapid⟩ :=
      mul_mul_thetaKernelPairing_mem_rapidFunctions j ϑ y i fun c ↦ ζ (i, c)
    exact (Space.integral_comp_mul_right (V := D.spaceW j) (liftMod u.val) h_rat h_cont).imp_right
      fun ⟨_, h_integrable⟩ ↦ h_integrable (h_rapid.integrable h_cont)
  -- Expand the descent of the glued form; the form `y` is invariant under the points `k u`.
  have h_point (g : G D.E (D.signsW j)) :
      (y : G D.E (D.signsW j) → ℂ) g * conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) =
      ∑ x : ChoiceIndex j × V.congruenceGroup, a x.1 * f x.1 (g * k x.2) := by
    rw [conj_normalizedDescent_glue j ϑ 1, sum_prod_type (α₂ := V.congruenceGroup)]
    simp only [a, f, k, V, Pi.mul_apply, goodForm_mul_liftMod_congruenceGroup j y, mul_sum,
      mul_assoc, mul_left_comm ((y : G D.E (D.signsW j) → ℂ) g)]
  calc inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y))
      = ∫ g, (y : G D.E (D.signsW j) → ℂ) g *
          conj ((D.descentPair ϑ j).normalizedDescent (glue j ϑ ζ) g) ∂μ :=
        inner_adjoint_glue_goodLift_eq_integral j ϑ y ζ
    _ = ∑ x : ChoiceIndex j × V.congruenceGroup, a x.1 * ∫ g, f x.1 g ∂μ := by
        rw [funext h_point, integral_finsetSum _ fun x _ ↦ (h_same ..).2.const_mul (a x.1)]
        simp only [integral_const_mul, h_same]
    _ = ∑ i : ChoiceIndex j, a i * Nat.card V.congruenceGroup * ∫ g, f i g ∂μ := by
        simp [sum_prod_type (α₂ := V.congruenceGroup), mul_assoc,
          mul_left_comm (Fintype.card _ : ℂ)]
    _ = _ := by simp only [a, f, V, Pi.mul_apply]

/-! ### Integrality and size of the gluing map -/

/-- The gluing map `glue j ϑ`, from tuples of forms on `V°` to forms on `V_j`, keeps integrality.
Let `l` be a prime coprime to `ϑ.1.normQ`, the product of the norms of the places in the set Q of
the twist `ϑ`. Let `φ` be an embedding of `ℂ` in `ℂ_l` (`PadicPlace l`). If all values of the tuple
`ζ` are integral at `φ`, so are all values of `glue j ϑ ζ`. -/
lemma glue_mem_integralForms {l : ℕ} [Fact l.Prime] (φ : PadicPlace l)
    (hl : l.Coprime ϑ.toTameChar.normQ) {ζ : FormTuples j} (hζ : IsIntegralFormTuple φ ζ) :
    glue j ϑ ζ ∈ LevelForm.integralForms φ := by
  -- All stabilisers are trivial, so `glue ζ` is `M ^ l₁` times a plain sum of forms supported on
  -- one class, and it is enough to bound the gauge of each term.
  simp_rw [glue_apply, classSum, finsum_eq_sum_of_fintype, smul_sum]
  refine sum_mem fun b _ ↦ sum_mem fun h _ g ↦ ?_
  simp only [classAut_gluingLevel_eq_bot j ϑ b.1.1, Subgroup.card_bot, Nat.cast_one, inv_one,
    one_smul]
  have h_M_mem : ↑D.M ∈ ((D.descentPair ϑ j).levelModulus 1 false).ideal :=
    D.ideal_untwistedModulus_eq_span.ge (by simp [← piM_mul_star, Ideal.mul_mem_right])
  -- The gauge of such a form is at most that of its vector `φ″ (h) · ζ (h°)`, and this is at most
  -- `‖M‖⁻¹ ^ l₁` times the gauges of the two integral factors. Default transparency is needed to
  -- recognise that product vector inside the form.
  grw (transparency := default) [weylGauge_smul, weylGauge_deltaForm_le isOfFinOrder_level_char,
    (splittingV j ϑ).weylGauge_cartanProduct_le h_M_mem (isGlued_glueLattice j ϑ b.1),
    weylGauge_firstFactor_le_one j ϑ _ _ l hl, hζ b]
  · simp [mul_inv_le_one]
  · simp [weylGauge]

/-- For the untwisted descent pair `untwistedDescentPair j`, at each infinite place `τ` and height
`i`, the number `colsMinus τ i` of columns of the diagram `μ⁻` is at most `D.gap`. -/
lemma colsMinus_le (τ : NumberField.InfinitePlace D.E) (i : ℕ) :
    (untwistedDescentPair j).colsMinus τ i ≤ D.gap := by
      grind [add_mul, descentPair, targetParameter_eq]

variable (D) in
/-- The rank of `V°` is at most `t = 5 r`. -/
lemma card_secondFactorIndex_le : card D.SecondFactorIndex ≤ D.t := by
  rw [Fintype.card_sum, Fintype.card_fin, D.card_rowIndex]
  grind [D.hundred_mul_m_add_nine_lt_k, D.r_add_one, D.t_eq_five_mul_r]

variable (D) in
private lemma card_secondFactorIndex_le_two_mul_n : card D.SecondFactorIndex ≤ 2 * D.n D.m := by
  have ht : D.t ≤ 6 * D.r := by rw [D.t_eq_five_mul_r]; omega
  exact (card_secondFactorIndex_le D).trans (ht.trans (D.six_mul_r_le_n.trans (by omega)))

/-- The diagram `μ⁻` has few boxes: at each place it has at most `D.gap` columns of each height, and
the heights are below the rank of `V°`, which is at most `t`. -/
lemma sum_mul_colsMinus_le :
    ∑ τ : D.Φ, ∑ i ∈ range (card D.SecondFactorIndex), i * (untwistedDescentPair j).colsMinus τ i ≤
      card D.Φ * (D.t * (D.t * D.gap)) := by
  have h_rank : card D.SecondFactorIndex ≤ D.t := card_secondFactorIndex_le D
  have h_term (τ : NumberField.InfinitePlace D.E) (i : ℕ)
    (hi : i ∈ range (card D.SecondFactorIndex)) :
      i * (untwistedDescentPair j).colsMinus τ i ≤ D.t * D.gap :=
    Nat.mul_le_mul ((mem_range_le hi).trans h_rank) (colsMinus_le j τ i)
  grw [sum_le_sum fun τ _ ↦ sum_le_card_nsmul _ _ _ (h_term τ), h_rank]
  simp

/-- The diagram `μ⁻` has few boxes, so its hook number (`hookNumberMinus`) is at most
`exp (x ^ 999)`, with `x = D.x` the length of the prime sum. -/
lemma hookNumberMinus_le : (hookNumberMinus j : ℝ) ≤ exp (D.x ^ 999) := by
  set L : ℕ := card D.Φ * (D.t * (D.t * D.gap)) with hL
  have h_hook : hookNumberMinus j ≤ ((L : ℤ) ^ L) ^ 3 := hookNumber_le (sum_mul_colsMinus_le j)
  have h_size : (3 : ℝ) * (L * L) ≤ D.x ^ 999 := by simpa [hL] using D.le_of_hasLogBound
  calc (hookNumberMinus j : ℝ) ≤ ((L : ℝ) ^ L) ^ 3 := mod_cast h_hook
    _ ≤ exp (3 * (L * L)) := by
        refine le_exp_of_log_le ?_
        grw [log_pow, log_pow, log_le_self (Nat.cast_nonneg L), Nat.cast_ofNat]
    _ ≤ exp (D.x ^ 999) := exp_le_exp.2 h_size

/-- The diagram `μ⁻` has few boxes, so the number of basis tensors of its shape with rows indexed by
the basis `D.SecondFactorIndex` of `V°` (`ColumnFilling`) is at most `exp (x ^ 999)`, with `x = D.x`
the length of the prime sum. -/
lemma card_columnFilling_colsMinus_le :
    (Nat.card (ColumnFilling (fun _ : NumberField.InfinitePlace D.E ↦ D.SecondFactorIndex)
      (untwistedDescentPair j).colsMinus) : ℝ) ≤ exp (D.x ^ 999) := by
  set L : ℕ := card D.Φ * (D.t * (D.t * D.gap)) with hL
  have h_card : Nat.card (ColumnFilling (fun _ ↦ D.SecondFactorIndex)
      (untwistedDescentPair j).colsMinus) ≤ (D.t + 1) ^ L :=
    GL.card_columnFilling_le (by omega)
      (fun _ ↦ (card_secondFactorIndex_le D).trans D.t.le_succ) (sum_mul_colsMinus_le j)
  have h_size : (L : ℝ) * (D.t + 1 : ℕ) ≤ D.x ^ 999 := by simpa [hL] using D.le_of_hasLogBound
  grw [h_card]
  refine le_exp_of_log_le ?_
  grw [← h_size, Nat.cast_pow, log_pow,
    log_le_self (Nat.cast_nonneg _)]

variable {j} in
/-- If the index type `n` has at most `2 * D.n D.m` elements, a level `K` that contains `J (ϖ²)`
(`principalLevel n (D.piM ^ 2)`) has at most `exp D.b` classes (`StdClasses K`). -/
lemma card_stdClasses_le_exp_of_le {n : Type} [Fintype n] [DecidableEq n] {K : Subgroup (Gf D.E n)}
    (hK : principalLevel n (D.piM ^ 2) ≤ K) (hn : card n ≤ 2 * D.n D.m) :
    Nat.card (StdClasses K) ≤ exp D.b := by
  have hK' : principalLevel n ((D.M ^ 2 : ℕ) : NumberField.RingOfIntegers D.E) ≤ K :=
    (principalLevel_le_of_dvd (by simp [← piM_mul_star])).trans hK
  exact (D.card_stdClasses_le_exp_mul_log _ hn hK').trans (exp_le_exp.2 D.le_of_hasLogBound)

/-- At the trivial twist the level `J_Λ` (`gluingLevel`) of a choice, whose matrix `Λ` is its
first component, contains `J (ϖ²)`. -/
lemma principalLevel_le_gluingLevel (i : ChoiceIndex j) :
    principalLevel (FirstFactorIndex j) (D.piM ^ 2) ≤ gluingLevel j 1 i.1 := by
  -- At the trivial twist the modulus of the level unfolds to `ϖ²`.
  with_unfolding_all
    exact Modulus.principalLevel_le_levelOfSubgroup (D.ideal_untwistedModulus_eq_span.ge (by simp))

/-- The bound `(M ^ l₁)² · exp b · (n · exp b · G)² ≤ exp (f m b log² b)`. Here `M = D.M` is the
principal level, `l₁ = DividedSplitting.denominatorExponent` the exponent of `M` in the denominator
for the splitting `V_j = V″ ⊕ V°`, `exp b` bounds the numbers of classes of `U(V_j)` and `U(V″)`,
`n` the number of pairs of a choice and a class of `U(V°)`, `G = D.chosenGroupOrder` the bound on
the orders of the stabilisers, `f = D.f` the number of infinite places, `m = D.m` the number of
lifts and `b = D.b` the weight at the `b`-places, with `log b = D.logB`. -/
lemma M_pow_denominatorExponent_sq_mul_le_exp :
    (D.M ^ (splittingV j 1).denominatorExponent) ^ 2 * (exp D.b *
      (card (ChoiceIndex j × D.SecondFactorClasses) * (exp D.b * D.chosenGroupOrder)) ^ 2) ≤
      exp (D.f * D.m * D.b * D.logB ^ 2) := by
  have hM : (1 : ℝ) ≤ D.M := mod_cast NeZero.one_le
  have h_aut : 0 < D.chosenGroupOrder := NeZero.pos _
  set L : ℕ := card D.Φ * (D.t * (D.t * D.gap)) with hL
  have h_det (τ : NumberField.InfinitePlace D.E) :
      ∑ i ∈ range (card (FirstFactorIndex j)), (untwistedDescentPair j).colsPlus τ i ≤
        D.natB + D.offWeight + D.gap + D.m * D.gap := by
    grind [card_detIndex_eq_sum j τ, card_detIndex_le j τ]
  set e : ℕ := card D.Φ * (3 * D.m * (D.natB + D.offWeight + D.gap + D.m * D.gap)) + L with he
  have h_exponent : (splittingV j 1).denominatorExponent ≤ e := by
    grw [DividedSplitting.denominatorExponent, h_det, colsMinus_le]
    simp only [sum_const, Finset.card_range, card_univ, smul_eq_mul]
    grw [card_secondFactorIndex_le D]
    simp [he, hL, mul_add, ← Nat.succ_mul]
  have h_ring : Nat.card (D.untwistedModulus 2).ResidueRing ≤
      (D.M ^ 2) ^ (2 * Core.numInfPlaces (P.E D.towerExp)) :=
    Modulus.card_residueRing_le (D.ideal_untwistedModulus_eq_span.ge
      (by simp [← piM_mul_star, Ideal.mem_span_singleton])) (NeZero.pos _)
  have h_card : card (ChoiceIndex j × D.SecondFactorClasses) ≤
      (Nat.card (D.untwistedModulus 2).ResidueRing ^ card (FirstFactorIndex j)) ^ card
        D.CarrierIndex *
        (exp D.b * ((card D.FlatIndex ^ (2 * D.m)) ^ D.reducedHalfGap) ^ card D.Φ) * exp D.b := by
    -- Each of the two sets of classes has at most `exp b` elements.
    have h_flat : Nat.card (StdClasses (principalLevel D.FlatIndex (D.piM ^ 2))) ≤ exp D.b :=
      card_stdClasses_le_exp_of_le le_rfl (by
        grind [Fintype.card_fin, D.six_mul_r_le_n, D.hundred_mul_m_add_nine_lt_k, D.r_add_one])
    have h_second :
        Nat.card (StdClasses (principalLevel D.SecondFactorIndex (D.piM ^ 2))) ≤ exp D.b :=
      card_stdClasses_le_exp_of_le le_rfl (card_secondFactorIndex_le_two_mul_n D)
    nth_grw 1 [← h_flat]
    grw [← h_second]
    -- What is left counts the matrices, the two sets of classes and the selections of rows.
    simp [↓Nat.card_prod, ↓card_eq_nat_card (α := _ × _), Matrix, mul_assoc]
  -- The logarithms of the bounds on the number of matrices and of selections of rows.
  set a : ℝ := card D.CarrierIndex * (card (FirstFactorIndex j) *
    ((2 * Core.numInfPlaces (P.E D.towerExp) : ℕ) * (2 * log D.M))) with ha
  have h_rows : card D.Φ * (D.reducedHalfGap * ((2 * D.m : ℕ) * log (card D.FlatIndex))) ≤
      card D.Φ * (D.halfGap * ((2 * D.m : ℕ) * (card D.FlatIndex : ℝ))) := by
    grw [log_le_self (Nat.cast_nonneg _), reducedHalfGap, Nat.sub_le]
  have h_size : 2 * (e * log D.M) + (D.b + 2 * (a + (D.b +
      card D.Φ * (D.halfGap * ((2 * D.m : ℕ) * (card D.FlatIndex : ℝ)))) + D.b +
      (D.b + log D.chosenGroupOrder))) ≤ D.f * D.m * D.b * D.logB ^ 2 := by
    simpa [ha, he, hL, D.t_eq_five_mul_r, card_firstFactorIndex j, add_assoc] using
      D.le_of_hasLogBound
  grw [h_exponent, h_card, h_ring]
  refine le_exp_of_log_le ?_
  grw [← h_size, ← h_rows]
  simp (disch := positivity) only [ha, log_mul, log_pow, log_exp, Nat.cast_pow, Nat.cast_ofNat,
    le_refl]

/-- One term of the gluing map at the trivial twist. Let `p = (i, c)` be a choice and a class of
`U(V°)`, `h` a finite point of `U(V″)` and `g` one of `U(V_j)`. Take the form on `V_j`
(`productForm`) supported on the class of `(h, c.out)` times the matrix of `glueLattice j 1 i`, made
from the product of the vectors `firstFactor j 1 i h` and `ζ p`. Let `σ` be a field automorphism of
`ℂ`. The squared norm (`weylNormSq`) of the value of this form at `g`, moved by `σ`, is at most
`A² exp (f m b log² b) ‖ζ‖_σ²`. Here `‖ζ‖_σ² = formTupleNormSq σ ζ`, `A = D.chosenGroupOrder` bounds
the orders of the stabilisers, `f` is the number of infinite places, `m` the number of lifts and `b`
the weight `exp D.logB`. -/
lemma weylNormSq_evalForm_productForm_le (ζ : FormTuples j) (σ : ℂ ≃+* ℂ)
    (p : ChoiceIndex j × D.SecondFactorClasses) (h : Gf D.E (FirstFactorIndex j))
    (g : Gf D.E (D.RowIndex ⊕ Fin D.t)) :
    weylNormSq (σ ∘ evalForm g ((splittingV j 1).productForm (glueLattice j 1 p.1) (h, p.2.out)
        (firstFactor j 1 p.1 h) (ζ p))) ≤
      D.chosenGroupOrder ^ 2 * (exp (D.f * D.m * D.b * D.logB ^ 2) * formTupleNormSq σ ζ) := by
  obtain ⟨h_plus, h_minus⟩ := (splittingV j 1).hasColumnsBelow
  let V := splittingV j 1
  let x : Gf D.E (D.RowIndex ⊕ Fin D.t) := U.block V.ε (h, p.2.out) * (glueLattice j 1 p.1).point
  let a : ℕ := Nat.card (classAut stdEmbFin.range (D.descentPair (1 : D.Twist) j).levelGroup x)
  have h_aut : a ≤ D.chosenGroupOrder :=
    Nat.le_of_dvd (NeZero.pos _) (D.card_classAut_dvd_chosenGroupOrder
      (card_rowIndex_sum_fin_le_two_mul_n D) levelOf_le_stdLevel x)
  have h_map : σ ∘ cartanProduct V.ε 1 (firstFactor j 1 p.1 h) (ζ p) =
      cartanProduct V.ε 1 (σ ∘ firstFactor j 1 p.1 h) (σ ∘ ζ p) :=
    map_cartanProduct h_plus h_minus V.ε (firstFactor j 1 p.1 h) (ζ p) σ.toRingHom
  have h_first : weylNormSq (σ ∘ firstFactor j 1 p.1 h) ≤ exp (D.f * D.m * D.b * D.logB ^ 2) :=
    weylNormSq_firstFactor_le j p.1 h σ
  have h_second : weylNormSq (σ ∘ ζ p) ≤ formTupleNormSq σ ζ :=
    single_le_sum (fun q _ ↦ weylNormSq_nonneg (σ ∘ ζ q)) (mem_univ p)
  -- A form supported on one class costs the order of a stabiliser, and the norm of the product
  -- vector is the product of the norms.
  calc _ ≤ a ^ 2 * weylNormSq (σ ∘ cartanProduct V.ε 1 (firstFactor j 1 p.1 h) (ζ p)) :=
        weylNormSq_deltaForm_le isOfFinOrder_level_char σ x _ g
    _ = a ^ 2 * (weylNormSq (σ ∘ firstFactor j 1 p.1 h) * weylNormSq (σ ∘ ζ p)) :=
        by rw [h_map, weylNormSq_cartanProduct h_plus h_minus]
    _ ≤ _ := mul_le_mul (by gcongr)
        (mul_le_mul h_first h_second (weylNormSq_nonneg _) (exp_pos _).le)
        (mul_nonneg (weylNormSq_nonneg _) (weylNormSq_nonneg _)) (sq_nonneg _)

/-- At the trivial twist `1`, every place `placeAt i` of the level of `V_j` (the places of
`descentPair 1 j`) contains `piM ^ 2`. -/
lemma piM_sq_mem_placeAt_descentPair_one
    (i : (D.descentPair (1 : D.Twist) j).ChosenIndex ⊕ (D.descentPair (1 : D.Twist) j).TwistIndex) :
    D.piM ^ 2 ∈ ((D.descentPair (1 : D.Twist) j).placeAt i).asIdeal := by
  obtain ⟨w, -, h_mem, -⟩ | i := i
  · exact Ideal.pow_mem_of_mem _ h_mem 2 two_pos
  · exact nomatch i

/-- Norm bound for the gluing map at the trivial twist: for a tuple `ζ` of forms on `V°` and an
automorphism `σ` of `ℂ`, the squared norm `normSqAt σ` of the form `glue j 1 ζ` on `V_j` is at most
`exp (2 f m b log² b)` times `‖ζ‖_σ²` (`formTupleNormSq`). Here `f` is the number of infinite
places, `m` the number of lifts and `b` the weight `exp D.logB`. -/
lemma normSqAt_glue_le (ζ : FormTuples j) (σ : ℂ ≃+* ℂ) :
    (glue j (1 : D.Twist) ζ).normSqAt σ ≤
      exp (2 * (D.f * D.m * D.b * D.logB ^ 2)) * formTupleNormSq σ ζ := by
  -- Each value of each term of `glue ζ` has norm at most `√(chosenGroupOrder ^ 2 * S)`. The norm of
  -- a sum is at most its number of terms times this; `M_pow_denominatorExponent_sq_mul_le_exp`
  -- collects these numbers and `M ^ l₁`.
  rw [two_mul, exp_add, mul_assoc]
  set S : ℝ := exp (D.f * D.m * D.b * D.logB ^ 2) * formTupleNormSq σ ζ
  have hS : 0 ≤ S := by simp [S, formTupleNormSq, exp_pos, Finset.sum_nonneg]
  let v (g : Gf D.E (D.RowIndex ⊕ Fin D.t)) := ∑ p : ChoiceIndex j × D.SecondFactorClasses,
    stdClassSum (gluingLevel j 1 p.1.1) fun h ↦ evalForm g ((splittingV j 1).productForm
      (glueLattice j 1 p.1) (h, p.2.out) (firstFactor j 1 p.1 h) (ζ p))
  set N : ℕ := card (ChoiceIndex j × D.SecondFactorClasses)
  set c : ℝ := (D.M ^ (splittingV j 1).denominatorExponent) ^ 2 with hc
  let K : Subgroup (Gf D.E (D.RowIndex ⊕ Fin D.t)) := (D.descentPair (1 : D.Twist) j).levelGroup
  have h_value (g : Gf D.E (D.RowIndex ⊕ Fin D.t)) :
      √(weylNormSq (σ ∘ v g)) ≤ N • (exp D.b * √(D.chosenGroupOrder ^ 2 * S)) := by
    refine (sqrt_weylNormSq_sum_le ..).trans (sum_le_card_nsmul _ _ _ fun p _ ↦ ?_)
    grw [← card_stdClasses_le_exp_of_le (principalLevel_le_gluingLevel j p.1)
      (card_firstFactorIndex_le_two_mul_n j)]
    exact sqrt_weylNormSq_classSum_le σ fun h ↦
      sqrt_le_sqrt (weylNormSq_evalForm_productForm_le j ζ σ p h g)
  have h_classes : Nat.card (DoubleCosets stdRatPoints K) ≤ exp D.b :=
    card_stdClasses_le_exp_of_le (principalLevel_le_levelOf (piM_sq_mem_placeAt_descentPair_one j))
      (card_rowIndex_sum_fin_le_two_mul_n D)
  calc (glue j (1 : D.Twist) ζ).normSqAt σ
      = c * classSum stdRatPoints K fun g ↦ weylNormSq (σ ∘ v g) := by
        simp only [glue_apply, LevelForm.normSqAt, apply_eq_evalForm]
        simp [hc, v, K, ← mul_classSum, map_classSum]
    _ ≤ c * (exp D.b * (N • (exp D.b * √(D.chosenGroupOrder ^ 2 * S))) ^ 2) := by
        grw [classSum_le_card_mul_sq h_value, h_classes]
    _ = c * (exp D.b * (N * (exp D.b * D.chosenGroupOrder)) ^ 2) * S := by
        simp (disch := positivity) [mul_pow, sq_sqrt, mul_assoc]
    _ ≤ exp (D.f * D.m * D.b * D.logB ^ 2) * S := by
        grw [M_pow_denominatorExponent_sq_mul_le_exp j]

/-! ### Periods of false lifts -/

open scoped Classical in
/-- Let `Ξ` be a form on `V_j`, for the pair `W_j, V_j` at the twist `ϑ` (`descentPair ϑ j`), in the
image of the idempotent `D.e₀` of the group algebra of `∏ GL_r (k_w)` over the residue fields `k_w`
of the chosen places `w`. Let `v` give a vector in `k_w ^ r` at each chosen place, not `0` at the
place `i`. Then `Ξ` is killed by the pure tensor of the elements `∑ χ_w (det h)⁻¹ h`, summed over
the invertible `h = 1 + u vᵀ` (`hyperplaneSum`), where `χ_w` is the residue character `tamePart`. -/
lemma hyperplaneSum_apply_eq_zero {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (groupAlgAction (D.descentPair ϑ j) D.e₀).range) (i : (D.descentPair ϑ j).ChosenIndex)
    (v : ∀ k : (D.descentPair ϑ j).ChosenIndex,
      D.RowIndex → ResField ((D.descentPair ϑ j).chosenPlace k)) (hv : v i ≠ 0) :
    (D.descentPair ϑ j).formAction.asAlgebraHom
      (piTensorElem fun k : (D.descentPair ϑ j).ChosenIndex ↦
        hyperplaneSum ((D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).chosenPlace k)) (v k)) Ξ =
          0 := by
  obtain ⟨x, rfl⟩ := hΞ
  have h_mem : D.piM ∈ (D.chosenPlace i).asIdeal := by
    obtain ⟨k, w, h_mem, -⟩ := i
    exact h_mem
  have h_tame : ϑ.tamePart (D.chosenPlace i) = 1 := ϑ.tamePart_eq_one _ fun h_mem_Q ↦ by
    obtain ⟨-, h_notMem, -⟩ := D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl h_mem_Q)
    exact h_notMem h_mem
  set T : MonoidAlgebra ℂ ((D.descentPair ϑ j).ChosenGL D.RowIndex) := piTensorElem fun k ↦
    hyperplaneSum ((D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).chosenPlace k)) (v k)
  let e₀ : MonoidAlgebra ℂ ((D.descentPair ϑ j).ChosenGL D.RowIndex) := D.e₀
  have h_kill : T * e₀ = 0 :=
    D.hyperplaneSum_mul_e₀ (x := fun k ↦ hyperplaneSum
      ((D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).chosenPlace k)) (v k))
      i (D.chiMLocal_zpow_mul_pow_eq_one j h_tame) hv rfl
  let ρ := (D.descentPair ϑ j).formAction.asAlgebraHom
  calc ρ T (ρ e₀ x) = ρ (T * e₀) x := (LinearMap.congr_fun (map_mul ρ T e₀) x).symm
    _ = 0 := by rw [h_kill, map_zero, LinearMap.zero_apply]

/-- Let `Ξ` be a form on `V_j`, for the pair `W_j, V_j` at the twist `ϑ` (`descentPair ϑ j`). If `Ξ`
lies in the image of the idempotent `D.e₀` and is orthogonal to the theta lifts `D.goodLift ϑ j y`
of all good forms `y` on `W_j` (principal level, in the image of `D.e₀`), then its descent
`normalizedDescent Ξ`, the function on `U(W_j)` that pairs `Ξ` with the theta kernel, vanishes. -/
lemma normalizedDescent_eq_zero_of_mem_orthogonal {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (groupAlgAction (D.descentPair ϑ j) D.e₀).range)
    (h_orth : Ξ ∈ (D.goodLift ϑ j).rangeᗮ) : (D.descentPair ϑ j).normalizedDescent Ξ = 0 := by
  -- For every `y`, `⟨Θ y, Ξ⟩ = ⟨Θ y, e₀ Ξ⟩ = ⟨e₀ Θ y, Ξ⟩`, and `e₀ Θ y` is the lift of a good form.
  have h_fix : (D.descentPair ϑ j).groupAlgAction D.e₀ Ξ = Ξ :=
    (D.isCentralProj_e₀.1.map _).mem_range_iff.1 hΞ
  refine D.normalizedDescent_eq_zero_of_inner_eq_zero ϑ Ξ fun y ↦ ?_
  have h_lift : (D.descentPair ϑ j).groupAlgAction D.e₀ (D.singleLift ϑ j y) ∈
    (D.goodLift ϑ j).range :=
    ⟨⟨_, _, rfl⟩, singleLift_asAlgebraHom ..⟩
  calc _ = inner ℂ (D.singleLift ϑ j y) ((D.descentPair ϑ j).groupAlgAction D.e₀ Ξ) := by rw [h_fix]
    _ = inner ℂ ((D.descentPair ϑ j).groupAlgAction D.e₀ (D.singleLift ϑ j y)) Ξ :=
        (innerAt_groupAlgAction _ D.isCentralProj_e₀ ..).symm
    _ = 0 := h_orth _ h_lift

/-- For the pair `descentPair ϑ j`, its `tamePart` is not `1` at any place `twistPlace i`, that is,
at any place of its set `Q`. -/
lemma tamePart_twistPlace_ne_one (i : (D.descentPair ϑ j).TwistIndex) :
    (D.descentPair ϑ j).tamePart ((D.descentPair ϑ j).twistPlace i) ≠ 1 :=
  (liftTamePart_eq_of_mem_Q ..).trans_ne (ϑ.tamePart_ne_one _ i.property)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Slices of false lifts vanish. Let `w` be a split place (`star w ≠ w`) off the level of the pair
`descentPair ϑ j`, and let `Ξ` be a false lift at `w`: a form on `V_j = V″ ⊕ V°` in the image of the
projection `e₀` that is killed by the Hecke polynomial operator at `w` and is orthogonal to the
lifts of good forms. Let `h` be a finite point of `U(V″)`, `y` any vector of weight `μ⁺`
(`colsPlus`) on `V″` and `g` a point of `U(W_j)`. Then the sum, over the classes of `U(V°)` with
representative `h° = c.out`, of the pairing of `Ξ ((h, h°) 𝗀)` with the product (`cartanProduct`) of
`y` and `θ° (g, h°)` is `0`. Here `θ°`, the conjugate of `kernelVector`, is the theta kernel of
`W_j, V°` of weight `μ⁻` (`colsMinus`), any datum `Ψ` modulo `ϖ²` (`ϖ = D.piM`) and any character
`b`, and `𝗀 = L.point` is the matrix of a lattice `L` between `ϖ 𝒪ⁿ` and `𝒪ⁿ`. -/
lemma sum_slice_eq_zero_of_mem_falseLiftsAt {w : FinPlace D.E} {hw : star w ≠ w}
    {hS : w ∉ (D.descentPair ϑ j).places.conjClosure} {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (D.descentPair ϑ j).falseLiftsAt hw hS D.e₀ (D.goodLift ϑ j).rangeᗮ)
    (L : DividedLattice (D.descentPair ϑ j)) (h : Gf D.E (FirstFactorIndex j))
    (y : WeylIndex (FirstFactorIndex j) (D.descentPair ϑ j).colsPlus → ℂ) (b : AutChar D.E)
    (Ψ : Matrix D.SecondFactorIndex D.RowIndex (D.descentPair ϑ j).chosenModulusSq.ResidueRing → ℂ)
    (g : G D.E (D.signsW j)) :
    ∑ c : D.SecondFactorClasses, gramForm
      (cartanProduct (splittingV j ϑ).ε 1 y (star (kernelVector (D.descentPair ϑ j) b
        (D.descentPair ϑ j).chosenModulusSq Ψ (D.descentPair ϑ j).colsMinus g c.out)))
      (Ξ (U.block (splittingV j ϑ).ε (h, c.out) * L.point)) = 0 := by
  classical
  obtain ⟨⟨hΞ_range, hΞ_ker⟩, hΞ_orth⟩ := hΞ
  have h_gap : 2 * card D.RowIndex + 2 * card (FirstFactorIndex j) + 3 < card
    (D.RowIndex ⊕ Fin D.t) := by
    rw [D.card_rowIndex_sum_fin, D.card_rowIndex, card_firstFactorIndex]
    grind [D.hundred_mul_m_add_nine_lt_k, D.r_add_one, D.t_eq_five_mul_r]
  -- Periods of false lifts vanish, here for the point `(h, h°) 𝗀`, the map `ζ ↦ y · ζ` and the
  -- level `J (ϖ²)`, which fixes the pairing, as its conjugate by `𝗀` fixes `Ξ`.
  have h_period : stdClassSum (principalLevel D.SecondFactorIndex (D.piM ^ 2))
      (fun h' : Gf D.E D.SecondFactorIndex ↦ inner ℂ ((splittingV j ϑ).productForm L (h, h') y
        (star (kernelVector (D.descentPair ϑ j) b (D.descentPair ϑ j).chosenModulusSq Ψ
          (D.descentPair ϑ j).colsMinus g h'))) Ξ) = 0 :=
    (splittingV j ϑ).stdClassSum_inner_productForm_eq_zero (D.fitsParams_descentPair ϑ j)
      (tamePart_twistPlace_ne_one j ϑ) (hyperplaneSum_apply_eq_zero j ϑ hΞ_range)
      (normalizedDescent_eq_zero_of_mem_orthogonal j ϑ hΞ_range hΞ_orth) hΞ_ker h_gap
      D.ideal_untwistedModulus_eq_span L h y b Ψ g
  -- The level `J (ϖ²)` on `V°` is sufficiently small, so the class sum is a plain sum.
  have h_small (h' : Gf D.E D.SecondFactorIndex) :
      classAut stdRatPoints (principalLevel D.SecondFactorIndex (D.piM ^ 2)) h' = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel (D.principalLevel_le_chosenLevel ⟨_, sq _⟩)
      (card_secondFactorIndex_le_two_mul_n D) h'
  -- The inner product with a form supported on one class is the pairing with the value there.
  simpa [↓h_small, classSum, ↓ finsum_eq_sum_of_fintype, DividedSplitting.productForm,
    inner_classForm] using! h_period

/-- Let `Ξ` be a false lift on `V_j` at a split place `w` off the level of `descentPair ϑ j`: a form
in the image of `D.e₀` that is killed by the Hecke polynomial operator at `w` and is orthogonal to
the lifts of good forms. The adjoint of the gluing map `glue j ϑ` takes `Ξ` to a tuple of forms on
`V°`, one for each choice `i`, given by values at the classes `c`. Each of them has pairing `0` with
the theta kernel `θ° (g, ·)` of `W_j, V°` at every `g` in `U(W_j)`. -/
lemma thetaKernelPairing_adjoint_glue_eq_zero {w : FinPlace D.E} {hw : star w ≠ w}
    {hS : w ∉ (D.descentPair ϑ j).places.conjClosure} {Ξ : (D.descentPair ϑ j).FormV}
    (hΞ : Ξ ∈ (D.descentPair ϑ j).falseLiftsAt hw hS D.e₀ (D.goodLift ϑ j).rangeᗮ)
    (i : ChoiceIndex j) (g : G D.E (D.signsW j)) :
    thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ (glue j ϑ).adjoint Ξ (i, c)) g = 0 := by
  classical
  -- The conjugate of the value is the product of the period with the tuple `η` of the values of
  -- `θ° (g, ·)` in the copy `i`, and the period is a sum of slices of `Ξ`.
  let θ (c : D.SecondFactorClasses) : SecondFactorFormValues j :=
    star ∘ kernelVector (untwistedDescentPair j) (upsilonU1 ^ (D.m / 2 - j : ℤ))
      (D.untwistedModulus 2) (Pi.single (inclMatrix _ inl) 1) (untwistedDescentPair j).colsMinus g
      c.out
  let η : FormTuples j := .toLp 2 fun b ↦ if b.1 = i then θ b.2 else 0
  have h_slice (i' : ChoiceIndex j) (h : Gf D.E (FirstFactorIndex j)) :
      ∑ c : D.SecondFactorClasses,
        gramForm (cartanProduct (splittingV j ϑ).ε 1 (firstFactor j ϑ i' h) (η (i', c)))
          (Ξ (U.block (splittingV j ϑ).ε (h, c.out) * (glueLattice j ϑ i').point)) = 0 := by
    by_cases hi : i' = i
    · simp only [η, ite_eq_left hi]
      exact sum_slice_eq_zero_of_mem_falseLiftsAt j ϑ hΞ (glueLattice j ϑ i') h _ _ _ g
    · simp only [η, hi, ↓reduceIte, map_zero]
      exact Finset.sum_eq_zero fun _ _ ↦ rfl
  refine star_eq_zero.1 ?_
  calc star (thetaKernelPairing j (fun c ↦ (glue j ϑ).adjoint Ξ (i, c)) g)
      = ∑ c, inner ℂ (θ c) ((glue j ϑ).adjoint Ξ (i, c)) := by
        -- The kernel is linear in its polynomial; expand both sides in the basis of weight `μ⁻`.
        simp [θ, thetaKernelPairing, kernelVector, inner, letterPoly, toPoly,
          linearCombination_apply, ← modKernelBilin_apply, Matrix.mulVec, dotProduct]
        rfl
    _ = ∑ i', ∑ c, inner ℂ (η (i', c)) ((glue j ϑ).adjoint Ξ (i', c)) := by
        rw [Fintype.sum_eq_single i (by simp +contextual [η])]
        simp [η]
    _ = inner ℂ η ((glue j ϑ).adjoint Ξ) := by
        rw [PiLp.inner_apply, sum_prod_type (α₂ := D.SecondFactorClasses)]
    _ = 0 := by
        rw [inner_adjoint_glue]
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i' _ ↦ ?_)
        simp only [classSum, finsum_eq_sum_of_fintype]
        rw [sum_comm]
        refine Finset.sum_eq_zero fun h _ ↦ ?_
        rw [← smul_sum, h_slice, smul_zero]

/-! ### The map `Θ°`, the seesaw identity and the false lifts -/

/-- The number `c°_i = M ^ l₁ c_𝗀 #J̄¹ c″` of the choice `i`, with `c_𝗀` the scalar of the lattice,
`J̄¹` the group `congruenceGroup` and `c″ = firstFactorScale j`. It does not depend on the twist. -/
def glueFactor (i : ChoiceIndex j) : ℂ :=
  D.M ^ (splittingV j 1).denominatorExponent * (glueLattice j 1 i).weilScalar *
    Nat.card (splittingV j 1).congruenceGroup * firstFactorScale j

lemma glueFactor_ne_zero (i : ChoiceIndex j) : glueFactor j i ≠ 0 := by
  simp [glueFactor, DividedLattice.weilScalar, NeZero.ne, firstFactorScale_ne_zero]

/-- Let `y` be a good form on `W_j` and `ζ` a tuple of forms on `V°`. Take the inner product of `ζ`
with the adjoint of the gluing map `glue j ϑ` at the theta lift of `y`, and multiply it by
`twistFactor j ϑ`, the scalar that carries the dependence of the series `firstFactorPairing` on the
twist `ϑ`. The result is the sum over the choices `i` of the number `glueFactor j i` times the
integral over `U(W_j)` modulo rational points of `y`, the function `choiceFn j i` and the pairing of
the copy `i` of `ζ` with the theta kernel of `W_j, V°`. -/
lemma twistFactor_mul_inner_adjoint_glue (y : D.goodForms (D.spaceW j)) (ζ : FormTuples j) :
    twistFactor j ϑ * inner ℂ ζ ((glue j ϑ).adjoint (D.goodLift ϑ j y)) =
      ∑ i : ChoiceIndex j, glueFactor j i *
        ∫ g : G D.E (D.signsW j), (y : G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
          thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ ζ (i, c)) g
            ∂(D.spaceW j).quotMeasure := by
  rw [inner_adjoint_glue_goodLift_eq_sum_integral, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_left_comm, glueFactor, mul_assoc _ (firstFactorScale j),
    ← integral_const_mul (firstFactorScale j),
    ← integral_const_mul (twistFactor j ϑ)]
  refine congrArg _ (integral_congr_ae (.of_forall fun g ↦ ?_))
  have h_series : twistFactor j ϑ * firstFactorPairing j ϑ i g = firstFactorScale j * choiceFn j i
    g :=
    twistFactor_mul_firstFactorPairing j ϑ i g
  linear_combination
    (y : G D.E (D.signsW j) → ℂ) g * thetaKernelPairing j (fun c ↦ ζ (i, c)) g * h_series

/-- The map `Θ°` from the good forms on `W_j` to tuples of forms on `V°` whose copy `i` is
`c°_i ∫ y (g) 𝖥_i (g) θ° (g, ·) dg` (`inner_periodLift`). It is defined as `c′_1 glue_1* Θ_{j,1}`,
the left side of the seesaw identity at the trivial twist. -/
def periodLift : D.goodForms (D.spaceW j) →ₗ[ℂ] FormTuples j :=
  twistFactor j 1 • (glue j 1).adjoint ∘ₗ D.goodLift (1 : D.Twist) j

/-- The product of `Θ° y` with a tuple `ζ` is the sum over the choices `i` of `c°_i` times the
integral of `y 𝖥_i` against the pairing of `θ° (g, ·)` with the copy `i` of `ζ`. -/
lemma inner_periodLift (y : D.goodForms (D.spaceW j)) (ζ : FormTuples j) :
    inner ℂ ζ (periodLift j y) = ∑ i : ChoiceIndex j, glueFactor j i *
      ∫ g : G D.E (D.signsW j), (y : G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
        thetaKernelPairing j (fun c : D.SecondFactorClasses ↦ ζ (i, c)) g
          ∂(D.spaceW j).quotMeasure := by
  simpa [periodLift] using twistFactor_mul_inner_adjoint_glue j 1 y ζ

/-- The seesaw identity `c′_ϑ glue_ϑ* Θ_{j,ϑ} = Θ°`: the number `twistFactor j ϑ` times the
composite of the lift `goodLift` with the adjoint of the gluing map `glue` is the map
`periodLift`, which does not depend on the twist. -/
theorem twistFactor_smul_adjoint_glue_comp :
    twistFactor j ϑ • (glue j ϑ).adjoint ∘ₗ D.goodLift ϑ j = periodLift j := by
  refine ext fun y ↦ ext_inner_left ℂ fun ζ ↦ ?_
  simpa [inner_periodLift, inner_smul_right] using twistFactor_mul_inner_adjoint_glue j ϑ y ζ

/-- For a good form `y` on `W_j`, the glued form `glue j ϑ (periodLift j y)` is orthogonal to the
false lifts at every split place off the level: the forms in the image of `e₀` that are killed by
the Hecke polynomial operator and are orthogonal to the lifts. -/
theorem isOrthogonalToFalseLifts_glue_periodLift (y : D.goodForms (D.spaceW j)) :
    IsOrthogonalToFalseLifts (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).rangeᗮ
      (glue j ϑ (periodLift j y)) := by
  intro w hw hS φ hφ
  -- `⟨φ, glue Θ° y⟩ = ⟨glue* φ, Θ° y⟩` is an integral against the products of the period of `φ`
  -- with the kernels `θ° (g, ·)`, and these vanish.
  rw [← adjoint_inner_left, inner_periodLift]
  simp [thetaKernelPairing_adjoint_glue_eq_zero j ϑ hφ]

/-! ### Injectivity of `Θ°` -/

/-- The map `periodLift j` from good forms on `W_j` to tuples of forms on `V°` is injective. -/
theorem periodLift_injective : Function.Injective (periodLift j) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦
    eq_zero_of_integral_choiceFn_thetaKernelPairing y fun i ζ ↦ ?_
  -- Test `Θ° y = 0` against the tuple that is `ζ` in the copy `i` and zero elsewhere.
  let η : FormTuples j := .toLp 2 fun b : ChoiceIndex j × D.SecondFactorClasses ↦
    if b.1 = i then ζ b.2 else 0
  have h_test := inner_periodLift j y η
  -- The copies other than `i` contribute nothing.
  rw [hy, inner_zero_right, Fintype.sum_eq_single i fun i' hi' ↦ by
    simp [η, hi', thetaKernelPairing, ← modKernelBilin_apply]] at h_test
  -- What is left is `c°_i` times the integral to be shown `0`.
  simpa [η, glueFactor_ne_zero] using h_test.symm

/-- The number `twistFactor j ϑ` is not `0`, since `Θ° = periodLift j` is injective and there is a
nonzero good form. -/
theorem twistFactor_ne_zero : twistFactor j ϑ ≠ 0 := by
  intro h_zero
  have h_lift : periodLift j = 0 := by simp [← twistFactor_smul_adjoint_glue_comp j ϑ, h_zero]
  exact D.finrank_targetForms_ne_zero <| (D.targetDim_eq_finrank_goodForms_spaceW j).trans <|
    finrank_zero_iff_forall_zero.2 fun y ↦ periodLift_injective j (by simp [h_lift])

end New.Rows

end
end
end

/-!
# The cost of one lift: a height bound for Z_j(1)/Z_j(ξ^j)

The comparison operators `U_ϑ = n_Aut hk² glue_ϑ glue_ϑ*` take lifts to forms orthogonal to the
false lifts. A tight frame of integral tuples writes them as sums of operators of rank one, so they
keep integrality away from `Q` and `U_1` is short (`IsComparisonOperator`). The product
`Z_j (ϑ) det (pr U_ϑ)` depends on the twist `ϑ` only through Hecke values. Eigenvalue bounds control
the denominator of `det (pr U_ϑ)` at `ι` and the conjugates of `det (pr U_1)`; this bounds the
height of `Z_j (1) / Z_j (ξ_ι ^ j)`, for m-fold twists `ξ_ι`.

Notions from other files:
* `D : Data P` fixes a CM field `E = D.E`, weights at its infinite places, a level, and the ranks:
  `m = D.m` lifts, from hermitian spaces `W_j = D.spaceW j` (`1 ≤ j ≤ m`) of rank `r = D.r` to the
  standard definite space `V_j` of rank `r + t`, where `t = D.t = 5 r`. The datum of the lift at a
  twist `ϑ` is `D.descentPair ϑ j`, and its `FormV` is the space of forms on `V_j`.
* `D.goodLift ϑ j` is the lift at the twist `ϑ` on the good forms on `W_j` (the range of the
  idempotent `D.e₀`), with values in the forms on `V_j`. `D.liftDeterminant ξ j`, written
  `Z_j (ξ ^ j)` for an m-fold twist `ξ`, is, at `ϑ = ξ ^ j`, the Gram determinant of this lift.
* `IsOrthogonalToFalseLifts O D.e₀ Z φ` says that the form `φ` is orthogonal to the false lifts: the
  forms that satisfy the conditions on a lift from `D.e₀` and lie in `Z`, here the complement of the
  lifts.
* `glue j ϑ` is the gluing map `glue_ϑ` from tuples of forms on `V°` (`FormTuples j`) to forms on
  `V_j`; `periodLift j` is `twistFactor j 1` times its adjoint after the lift, at the trivial twist.
  Here `V°` is the standard definite space with basis `D.SecondFactorIndex`.
* `heckeValueProd j ϑ` is a product of three real numbers `Exchange.lValueProd` (norms of places
  times squared moduli of partial Hecke `L`-values at integers), for the three characters of
  `exchangePair j` twisted by `ϑ` or its inverse.

## Relation to the literature

Bounding the norm of a lift by an integral form and a congruence denominator is known in the
literature for one eigenform.

Related work: Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; X. Zhang,
Special L-values and Selmer groups of Siegel modular forms of genus 2, 2018; Hida, Congruences of
cusp forms and special values of their zeta functions, 1981.
-/

@[expose] public section

namespace New.Data

open Matrix NumberField Function ComplexConjugate IsAlgClosed Module Real Finset DescentPair Rows
open LinearMap Space «GL» LevelPlaces.LevelForm Selmer IsUltrametricDist
open scoped ComplexOrder

/-- Let `u : U → V` be an injective linear map of finite-dimensional complex inner product spaces,
`pr` the orthogonal projection of `V` to the range of `u`, and `T` an operator on `V`. The
determinant of `pr T` on the range of `u`, times `u.normDet ^ 2 = det (u* u)`, is `det (u* T u)`. -/
lemma normDet_sq_mul_det_compression {U V : Type}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [Module.Finite ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Module.Finite ℂ V]
    (T : End ℂ V) {u : U →ₗ[ℂ] V} (hu : Injective u) :
    u.normDet ^ 2 * (u.range.orthogonalProjectionOnto.toLinearMap ∘ₗ T.domRestrict u.range).det =
      (u.adjoint ∘ₗ T ∘ₗ u).det := by
  -- `u*` kills the orthogonal complement of the range, so `u* u (u⁻¹ pr T u) = u* T u`.
  let e : U ≃ₗ[ℂ] u.range := .ofInjective u hu
  let S : End ℂ u.range := u.range.orthogonalProjectionOnto.toLinearMap ∘ₗ T.domRestrict u.range
  have h_apply (z : u.range) : u (e.symm z) = z := congrArg Subtype.val (e.apply_symm_apply z)
  have h_comp : u.adjoint ∘ₗ T ∘ₗ u =
      (u.adjoint ∘ₗ u) ∘ₗ (e.symm.toLinearMap ∘ₗ S ∘ₗ e.symm.symm.toLinearMap) := by
    refine LinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_
    have h_proj : inner ℂ (u x) (u.range.starProjection (T (u y))) = inner ℂ (u x) (T (u y)) :=
      u.range.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨u x, x, rfl⟩ (T (u y))
    simpa [adjoint_inner_right, h_apply, S, e] using h_proj.symm
  rw [h_comp, det_comp, LinearMap.det_conj, ← normDet_sq, RCLike.ofReal_pow]
  rfl

/-- A determinant is the product of the eigenvalues. So if `‖f α‖ ≤ B` for every eigenvalue `α` of
`u` (`h_eigen`), then `‖f u.det‖ ≤ B ^ finrank ℂ L`, for the ring map `f : ℂ →+* K` into a normed
field. -/
lemma norm_map_det_le_pow {K L : Type} [NormedField K] [AddCommGroup L] [Module ℂ L]
    [Module.Finite ℂ L] (f : ℂ →+* K) (u : End ℂ L) {B : ℝ}
    (h_eigen : ∀ (α : ℂ) (z : L), u.HasEigenvector α z → ‖f α‖ ≤ B) :
    ‖f u.det‖ ≤ B ^ finrank ℂ L := by
  let N : ℂ →* ℝ := (normHom (α := K)).toMonoidHom.comp f.toMonoidHom
  change N u.det ≤ B ^ finrank ℂ L
  rw [End.det_eq_prod_roots_charpoly_of_splits (splits _), map_multiset_prod,
    ← u.charpoly_natDegree, ← card_roots_eq_natDegree]
  refine Multiset.prod_map_le_pow_card (fun α _ ↦ norm_nonneg (f α)) fun α hα ↦ ?_
  obtain ⟨z, hz⟩ := ((End.hasEigenvalue_iff_isRoot_charpoly u α).2
    (Polynomial.isRoot_of_mem_roots hα)).exists_hasEigenvector
  exact h_eigen α z hz

/-- The squared norm `φ.normSqAt σ` of a form (the weighted sum over classes of the squared norms
of the values after applying `σ`) is not negative. -/
lemma _root_.New.LevelPlaces.LevelForm.normSqAt_nonneg {E r n : Type} [Field E] [CMType E]
    [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair E r n}
    (φ : O.FormV) (σ : ℂ ≃+* ℂ) :
    0 ≤ φ.normSqAt σ := by
  rw [normSqAt, classSum]
  exact finsum_nonneg fun _ ↦ smul_nonneg (by positivity) (weylNormSq_nonneg _)

/-- Let `E` be a CM field with a CM type and Weil data, and `O` a descent pair over `E`: the datum
of a lift from a hermitian space `W` with basis indexed by `r` to the standard space `V` with basis
indexed by `n`. For `φ ≠ 0` in `O.FormV`, the algebraic forms on `V` of the weight and level of `O`,
the squared norm `φ.normSqAt σ` is positive at every automorphism `σ` of `ℂ`. -/
lemma _root_.New.LevelPlaces.LevelForm.normSqAt_pos {E r n : Type} [Field E] [CMType E]
    [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n] {O : DescentPair E r n}
    {φ : O.FormV} (hφ : φ ≠ 0) (σ : ℂ ≃+* ℂ) :
    0 < φ.normSqAt σ := by
  obtain ⟨c, hc⟩ : ∃ c : StdClasses (levelOf O.placeAt
    (descentResidueLevel O.toLevelPlaces O.incl)),
      φ c.out ≠ 0 := by
    by_contra! h
    exact hφ (levelSpace_ext_doubleCosets Quot.out_eq h)
  exact classSum_pos (c := c) (by simp)
    (weylGramOver_posDef.re_dotProduct_pos (by simpa [funext_iff] using hc : σ ∘ φ c.out ≠ 0))

/-- A nonzero form `φ` in the space `O.FormV` of forms on `V` of a descent pair `O` over the CM
field `E` can be scaled to valuation `0` at a place `ι` (an embedding `ι.ιₚ` of `ℂ` into `ℂ_[l]`):
there is `c ≠ 0` such that `c • φ` is integral at `ι`, and `α • c • φ` is integral only if
`‖ι.ιₚ α‖ ≤ 1`. -/
lemma _root_.New.DescentPair.exists_smul_mem_integralForms_maximal {E r n : Type} [Field E]
    [CMType E] [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
    {O : DescentPair E r n} {φ : O.FormV} (hφ : φ ≠ 0) {l : ℕ} [Fact l.Prime] (ι : PadicPlace l) :
    ∃ c : ℂ, c ≠ 0 ∧ c • φ ∈ integralForms ι ∧
      ∀ α : ℂ, α • c • φ ∈ integralForms ι → ‖ι.ιₚ α‖ ≤ 1 := by
  -- Divide by a coordinate of least valuation at representatives that are integral above `l`.
  let K : Subgroup (Gf E n) := levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)
  obtain ⟨s, hs_mk, hs_int⟩ := exists_reps_integralAbove (K := K) l
  obtain ⟨x₁, hx₁⟩ : ∃ x : StdClasses K × WeylIndex n O.columnCount, φ (s x.1) x.2 ≠ 0 := by
    by_contra! h
    exact hφ (levelSpace_ext_doubleCosets hs_mk fun q ↦ funext fun i ↦ h (q, i))
  have : Nonempty (StdClasses K × WeylIndex n O.columnCount) := ⟨x₁⟩
  obtain ⟨x, h_max⟩ :=
    Finite.exists_max fun y : StdClasses K × WeylIndex n O.columnCount ↦ ‖ι.ιₚ (φ (s y.1) y.2)‖
  have hx : 0 < ‖ι.ιₚ (φ (s x.1) x.2)‖ := lt_of_lt_of_le (by simpa using hx₁) (h_max x₁)
  have hx_ne : φ (s x.1) x.2 ≠ 0 := by simpa using hx
  have h_smul (c : ℂ) (ψ : O.FormV) (g : Gf E n) : (c • ψ) g = c • ψ g := rfl
  refine ⟨(φ (s x.1) x.2)⁻¹, inv_ne_zero hx_ne, fun g ↦ ?_, fun α hα ↦ ?_⟩
  · -- Write `g = γ (s q) k` with `γ` rational and `k` in the level; the gauge is that at `s q`.
    let q : StdClasses K := DoubleCoset.mk _ _ g
    let ψ : O.FormV := (φ (s x.1) x.2)⁻¹ • φ
    obtain ⟨_, ⟨γ, rfl⟩, k, hk, hg⟩ :
        ∃ γ' ∈ (stdSpace E n).Γf, ∃ k ∈ K, g = γ' * s q * k :=
      (DoubleCoset.eq ..).1 (hs_mk q)
    have h_char : ‖ι.ιₚ (O.levelChar ⟨k, hk⟩)‖ = 1 :=
      (ι.ιₚ.isOfFinOrder (LevelPlaces.isOfFinOrder_level_char _)).norm_eq_one
    have h_bound (i : WeylIndex n O.columnCount) : ‖ι.ιₚ (ψ (s q) i)‖ ≤ 1 := by
      simpa [ψ, h_smul, ← div_eq_inv_mul] using (div_le_one hx).2 (h_max (q, i))
    have h_value : ψ g =
        O.levelChar ⟨k, hk⟩ • (stdSpace E n).weightRep O.columnCount O.detExp γ (ψ (s q)) := by
      rw [hg]
      exact levelSpace_smoothFormRep_apply ψ.property γ (s q) ⟨k, hk⟩
    calc weylGauge O.columnCount O.detExp g (ψ g)
      _ = weylGauge O.columnCount O.detExp (s q) (ψ (s q)) := by
        rw [h_value, weylGauge_smul, h_char, one_mul, hg,
          weylGauge_mul_of_mem_integralAbove _ (stdLevel_le_localLevel (levelOf_le_stdLevel hk)),
            weylGauge_embFin]
      _ ≤ 1 := (weylGauge_le_one_iff _ (hs_int q)).2 h_bound
  · simpa [h_smul, hx_ne] using (weylGauge_le_one_iff _ (hs_int x.1)).1 (hα (s x.1)) x.2

section Operator

variable {P : Parameters} {D : Data P}

/-- A comparison operator for the lift from `W_j`: a family of operators `U_ϑ` on the forms on `V_j`
through which the lifts `Θ_ϑ = D.goodLift ϑ j` at the twists `ϑ` are compared with the untwisted
one. In the bound, `f = D.f` is the number of infinite places, `m = D.m` the number of lifts in the
chain and `b = D.b`, with `log b = D.logB`, the weight at the infinite places in `D.bPlaces`. -/
structure IsComparisonOperator (j : D.LiftIndex)
    (U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV) : Prop where
  /-- The ratio of the twisted to the untwisted Hecke values of the lift is not `0`. -/
  ratio_ne_zero (ϑ : D.Twist) : heckeValueProd j ϑ / heckeValueProd j 1 ≠ 0
  /-- `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩` is this ratio times `⟨y', U° y⟩`, for a positive definite operator `U°`
  on the good forms that does not depend on `ϑ`. The shape of the ratio is given by
  `exists_heckeValueProd_eq_mul_prod_ratio`. -/
  exists_inner_eq : ∃ U₀ : End ℂ (D.goodForms (D.spaceW j)),
    (∀ y : D.goodForms (D.spaceW j), y ≠ 0 → 0 < inner ℂ y (U₀ y)) ∧
    ∀ (ϑ : D.Twist) (y' y : D.goodForms (D.spaceW j)),
      inner ℂ (D.goodLift ϑ j y') (U ϑ (D.goodLift ϑ j y)) =
        heckeValueProd j ϑ / heckeValueProd j 1 * inner ℂ y' (U₀ y)
  /-- `U_ϑ` takes lifts to forms that are orthogonal to the false lifts
  (`IsOrthogonalToFalseLifts`). -/
  isOrthogonalToFalseLifts (ϑ : D.Twist) (z : (D.goodLift ϑ j).range) :
    IsOrthogonalToFalseLifts (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).rangeᗮ (U ϑ z)
  /-- `U_ϑ` keeps integrality above every prime that does not divide `ϑ.normQ`, the product
  of the norms of the places in the set `Q` of `ϑ`. -/
  mem_integralForms (ϑ : D.Twist) (l : ℕ) [Fact l.Prime] (ι : PadicPlace l)
    (hl : l.Coprime ϑ.normQ) : ∀ φ ∈ integralForms ι, U ϑ φ ∈ integralForms ι
  /-- `U_1` multiplies norms at every `σ` by at most `exp (3 f m b log² b)`. -/
  normSqAt_le (φ : (D.descentPair (1 : D.Twist) j).FormV) (σ : ℂ ≃+* ℂ) :
    (U 1 φ).normSqAt σ ≤ exp (3 * (D.f * D.m * D.b * D.logB ^ 2)) ^ 2 * φ.normSqAt σ

/-- The operator `U_ϑ = n_Aut hk² glue_ϑ glue_ϑ*` on the forms on `V_j`. Here `glue_ϑ = glue j ϑ`
is the linear map that builds a form on `V_j` from a tuple of forms on `V°`,
`hk = hookNumberMinus j` is the hook number of the diagram `μ⁻` (the weight of the forms on `V°`),
and `n_Aut = D.chosenGroupOrder` is a multiple of the orders of all stabilisers. -/
noncomputable def comparisonOp (j : D.LiftIndex) (ϑ : D.Twist) : End ℂ (D.descentPair ϑ j).FormV :=
  (D.chosenGroupOrder * hookNumberMinus j ^ 2 : ℂ) •
    glue j ϑ ∘ₗ (glue j ϑ).adjoint

/-- The ratio of the twisted to the untwisted product of Hecke values (`heckeValueProd`) is
`|c′_1|² / |c′_ϑ|²`, where `c′_ϑ = twistFactor j ϑ` is the nonzero scalar that normalises the
series of the gluing at the twist `ϑ`. -/
lemma heckeValueProd_div_eq (j : D.LiftIndex) (ϑ : D.Twist) :
    heckeValueProd j ϑ / heckeValueProd j 1 =
      ‖Rows.twistFactor j 1‖ ^ 2 / ‖Rows.twistFactor j ϑ‖ ^ 2 := by
  obtain ⟨C, hC⟩ : ∃ C : ℂ, ∀ ϑ : D.Twist,
      (‖Rows.twistFactor j ϑ‖ : ℂ) ^ 2 = C / heckeValueProd j ϑ := exists_norm_twistFactor_sq_eq j
  have hC_ne : C ≠ 0 := fun h ↦ by simpa [h, twistFactor_ne_zero] using hC 1
  rw [hC, hC, div_div_div_cancel_left₀ _ _ hC_ne]

/-- The adjoint of the gluing map `glue j ϑ` takes the lift of `y` at the twist `ϑ` to
`c′_ϑ⁻¹ Θ° y`, where `c′_ϑ = twistFactor j ϑ` and `Θ° = periodLift j`. -/
lemma adjoint_glue_goodLift (j : D.LiftIndex) (ϑ : D.Twist) (y : D.goodForms (D.spaceW j)) :
    (glue j ϑ).adjoint (D.goodLift ϑ j y) = (Rows.twistFactor j ϑ)⁻¹ • periodLift j y := by
  rw [eq_inv_smul_iff₀ (twistFactor_ne_zero j ϑ)]
  exact LinearMap.congr_fun (twistFactor_smul_adjoint_glue_comp j ϑ) y

end Operator

/-- Let `D` be the data of the chain of lifts, `1 ≤ j ≤ D.m`, `ϑ` a twist, and `y'`, `y` good forms
on the hermitian space `W_j = D.spaceW j`. Let `Θ_ϑ = D.goodLift ϑ j` be the theta lift to forms on
the definite space `V_j`, and `glue_ϑ = glue j ϑ` the linear map that builds a form on `V_j` from a
tuple of forms on the smaller definite space `V°`, with adjoint `glue_ϑ*`. For
`U_ϑ = comparisonOp j ϑ = n_Aut hk² glue_ϑ glue_ϑ*` we have `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩ = n_Aut hk²
|c′_ϑ|⁻² ⟨Θ° y', Θ° y⟩`. Here `n_Aut = D.chosenGroupOrder` is a multiple of the orders of all
stabilisers, `hk = hookNumberMinus j` is the hook number of the weight of the forms on `V°`, and
`c′_ϑ = twistFactor j ϑ` is the nonzero scalar for which `c′_ϑ glue_ϑ* Θ_ϑ` does not depend on `ϑ`;
this common map is `Θ° = periodLift j`. -/
lemma inner_goodLift_comparisonOp {P : Parameters} {D : Data P} (j : D.LiftIndex) (ϑ : D.Twist)
    (y' y : D.goodForms (D.spaceW j)) :
    inner ℂ (D.goodLift ϑ j y') (comparisonOp j ϑ (D.goodLift ϑ j y)) =
      D.chosenGroupOrder * hookNumberMinus j ^ 2 / ‖Rows.twistFactor j ϑ‖ ^ 2 *
        inner ℂ (periodLift j y') (periodLift j y) := by
  calc
    _ = D.chosenGroupOrder * hookNumberMinus j ^ 2 *
        inner ℂ ((glue j ϑ).adjoint (D.goodLift ϑ j y'))
          ((glue j ϑ).adjoint (D.goodLift ϑ j y)) := by
      simp only [comparisonOp, LinearMap.smul_apply, inner_smul_right, LinearMap.comp_apply,
        adjoint_inner_left]
    _ = _ := by
      rw [adjoint_glue_goodLift, adjoint_glue_goodLift, inner_smul_left,
        inner_smul_right, ← Complex.conj_mul', map_inv₀]
      ring

/-- Let `D` be the data of the chain of lifts, `1 ≤ j ≤ D.m` and `ϑ` a twist. Let `z` be a lift: a
form on `V_j` in the range of the theta lift `D.goodLift ϑ j` of the good forms on `W_j`;
`D.descentPair ϑ j` is the datum of this lift. Then the image of `z` under `comparisonOp j ϑ`, a
positive multiple of the gluing map `glue j ϑ` after its adjoint, is orthogonal to the false
lifts. -/
lemma isOrthogonalToFalseLifts_comparisonOp {P : Parameters} {D : Data P} {j : D.LiftIndex}
    {ϑ : D.Twist} (z : (D.goodLift ϑ j).range) :
    IsOrthogonalToFalseLifts (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).rangeᗮ
      (comparisonOp j ϑ z) := by
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 z.property
  have h_op : comparisonOp j ϑ z = ((D.chosenGroupOrder : ℂ) * hookNumberMinus j ^ 2 *
      (Rows.twistFactor j ϑ)⁻¹) • glue j ϑ (periodLift j y) := by
    rw [← hy, comparisonOp, LinearMap.smul_apply, LinearMap.comp_apply, adjoint_glue_goodLift,
      map_smul, smul_smul]
  intro w hw hS
  rw [h_op]
  exact Submodule.smul_mem _ _ (isOrthogonalToFalseLifts_glue_periodLift j ϑ y w hw hS)

variable {P : Parameters} {D : Data P}

section Gluing

/-- The index set of the frame of tuples of forms on `V°`: an index `ChoiceIndex j` of a component
of the tuple (a matrix modulo `D.piM ^ 2` with a row choice), a class of `U(V°)` at principal level
`D.piM ^ 2`, and a basis tensor of the shape `μ⁻ = (untwistedDescentPair j).colsMinus`, the column
counts of the negative sign for the descent pair at the trivial twist. -/
abbrev TightFrameIndex (j : D.LiftIndex) : Type :=
  (ChoiceIndex j × D.SecondFactorClasses) ×
    ColumnFilling (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus

/-- Let `V° = stdSpace D.E D.SecondFactorIndex` be the standard definite hermitian space over the CM
field `D.E` of the data `D`, with basis `D.SecondFactorIndex`. Let `γ` be an element of its rational
unitary group `U (stdSpace D.E D.SecondFactorIndex).J`. Let
`μ⁻ = (untwistedDescentPair j).colsMinus` be the family of Young diagrams, one at each infinite
place and given by its column counts. The group acts by `weightRep μ⁻ 0` on coordinate vectors
indexed by the standard fillings `WeylIndex` of `μ⁻`. There is a tight frame of such vectors `η T`,
one for each filling `T` of `μ⁻` with increasing columns (`ColumnFilling`): (a)
`∑ T, ⟨η T, ξ⟩ η T = hk² ξ` for all `ξ`, where `hk = hookNumberMinus j` is the hook number of `μ⁻`
and `⟨·, ·⟩ = gramForm` is the Hermitian form of the integer Gram matrix; (b) `γ` takes the complex
conjugate of each `η T` to an integer vector; (c) each has squared norm (`weylNormSq`, for that
form) at most `hk²` after every automorphism of `ℂ`. -/
lemma exists_frame_weightRep_eq_intCast (j : D.LiftIndex)
    (γ : U (stdSpace D.E D.SecondFactorIndex).J) :
    ∃ η : ColumnFilling (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus →
        WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℂ,
      (∀ ξ : WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℂ,
        ∑ T : ColumnFilling (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus,
          gramForm (η T) ξ • η T = (hookNumberMinus j : ℂ) ^ 2 • ξ) ∧
      (∀ T : ColumnFilling (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus,
        ∃ z : WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℤ,
          (stdSpace D.E D.SecondFactorIndex).weightRep (untwistedDescentPair j).colsMinus 0 γ
            (star (η T)) = Int.cast ∘ z) ∧
      ∀ (T : ColumnFilling (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus)
        (σ : ℂ ≃+* ℂ),
        weylNormSq (σ ∘ η T) ≤ (hookNumberMinus j : ℝ) ^ 2 := by
  -- Move the integral frame of `exists_tightFrame` by the unitary map `ξ ↦ star (γ⁻¹ (star ξ))`.
  classical
  let W : Type := WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℂ
  obtain ⟨η, h_frame, h_norm⟩ :
      ∃ η : ColumnFilling (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus →
          WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℤ,
        (∀ ξ : W, ∑ T, gramForm (Int.cast ∘ η T) ξ • (Int.cast ∘ η T : W) =
          (hookNumberMinus j : ℂ) ^ 2 • ξ) ∧
        ∀ T, weylNormSq (Int.cast ∘ η T) ≤ (hookNumberMinus j : ℝ) ^ 2 :=
    exists_tightFrame
  let ρ : Representation ℂ (U (stdSpace D.E D.SecondFactorIndex).J) W :=
    (stdSpace D.E D.SecondFactorIndex).weightRep (untwistedDescentPair j).colsMinus 0
  let u (δ : U (stdSpace D.E D.SecondFactorIndex).J) : W →ₗ[ℂ] W :=
    { toFun := fun ξ ↦ star (ρ δ (star ξ))
      map_add' ξ ξ' := by rw [star_add, map_add, star_add]
      map_smul' := by simp }
  have h_inv (δ : U (stdSpace D.E D.SecondFactorIndex).J) (ξ : W) : u δ⁻¹ (u δ ξ) = ξ := by simp [u]
  refine ⟨fun T ↦ u γ⁻¹ (Int.cast ∘ η T), fun ξ ↦ ?_, fun T ↦ ⟨η T, ?_⟩, fun T σ ↦ ?_⟩
  · have h_unitary (ξ' : W) : gramForm (u γ⁻¹ ξ') ξ = gramForm ξ' (u γ ξ) := by
      have h_conj : gramForm (u γ⁻¹ ξ') (u γ⁻¹ (u γ ξ)) =
          gramForm (star (star ξ')) (star (star (u γ ξ))) :=
        gramForm_map_weightRep (e := 0) conj γ⁻¹ (star ξ') (star (u γ ξ))
      rwa [h_inv, star_star, star_star] at h_conj
    calc ∑ T, gramForm (u γ⁻¹ (Int.cast ∘ η T)) ξ • u γ⁻¹ (Int.cast ∘ η T)
      _ = u γ⁻¹ (∑ T, gramForm (Int.cast ∘ η T) (u γ ξ) • Int.cast ∘ η T) := by simp [h_unitary]
      _ = (hookNumberMinus j : ℂ) ^ 2 • ξ := by rw [h_frame, map_smul, h_inv]
  · have h_real : star (Int.cast ∘ η T : W) = Int.cast ∘ η T := funext fun _ ↦ by simp
    simp [u, ρ, h_real]
  · -- After `σ` the map `u` is still unitary, and `σ` fixes the integer vector `ξ`.
    let ξ : W := Int.cast ∘ η T
    have h_fix : σ ∘ ξ = ξ := funext fun i ↦ map_intCast σ (η T i)
    have h_value : (weylNormSq (σ ∘ u γ⁻¹ ξ) : ℂ) = weylNormSq (σ ∘ star (star ξ)) := by
      rw [coe_weylNormSq, coe_weylNormSq]
      exact gramForm_map_weightRep (e := 0) (σ.toRingHom.comp conj) γ⁻¹ (star ξ) (star ξ)
    rw [star_star, h_fix] at h_value
    exact (Complex.ofReal_injective h_value).le.trans (h_norm T)

/-- A tuple (`FormTuples j`) has one form for each `i` in the finite set `ChoiceIndex j`, given by
its values at the classes `c` in `D.SecondFactorClasses`, the double cosets of `U(V°)(𝔸_f)` by the
rational points and a principal congruence subgroup. The values are coordinate vectors, indexed by
standard fillings (`WeylIndex`), of the representation `weightRep` whose weight is the family of
Young diagrams `μ⁻ = (untwistedDescentPair j).colsMinus`. Let `δ c` be an element of the rational
unitary group of `V°` for each class `c`. There are tuples `f a`, for `a` in `TightFrameIndex j`,
with (a) `∑ a, ⟨f a, ζ⟩ f a = hk² ζ` for all `ζ`, where `hk` is the hook number of `μ⁻`; (b) `δ c`
takes the complex conjugate of the value of `f a` at `(i, c)` to an integer vector; (c) squared norm
(`formTupleNormSq`) at most `hk²` at every automorphism of `ℂ`. -/
lemma exists_tight_frame_formTuples (j : D.LiftIndex)
    (δ : D.SecondFactorClasses → U (stdSpace D.E D.SecondFactorIndex).J) :
    ∃ f : TightFrameIndex j → FormTuples j,
      (∀ ζ : FormTuples j,
        ∑ a : TightFrameIndex j, inner ℂ (f a) ζ • f a = (hookNumberMinus j : ℂ) ^ 2 • ζ) ∧
      (∀ (a : TightFrameIndex j) (i : ChoiceIndex j) (c : D.SecondFactorClasses),
        ∃ z : WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℤ,
          (stdSpace D.E D.SecondFactorIndex).weightRep (untwistedDescentPair j).colsMinus 0 (δ c)
            (star (f a (i, c))) = Int.cast ∘ z) ∧
      ∀ (a : TightFrameIndex j) (σ : ℂ ≃+* ℂ),
        formTupleNormSq σ (f a) ≤ (hookNumberMinus j : ℝ) ^ 2 := by
  -- The tuple `f (b, T)` is the vector `η b T` of the moved frame at `b`, and `0` elsewhere.
  classical
  choose η h_frame h_coord h_norm using
    fun b : ChoiceIndex j × D.SecondFactorClasses ↦ exists_frame_weightRep_eq_intCast j (δ b.2)
  let f (a : TightFrameIndex j) : FormTuples j := .toLp 2 (Pi.single a.1 (η a.1 a.2))
  -- The metric of `SecondFactorFormValues` is the form of the Gram matrix.
  have h_inner (ξ ξ' : SecondFactorFormValues j) : inner ℂ ξ ξ' = gramForm ξ ξ' :=
    dotProduct_comm ..
  refine ⟨f, fun ζ ↦ ?_, fun a i c ↦ ?_, fun a σ ↦ ?_⟩
  · have h_coeff (a : TightFrameIndex j) : inner ℂ (f a) ζ = gramForm (η a.1 a.2) (ζ a.1) := by
      rw [← h_inner, PiLp.inner_apply, Fintype.sum_eq_single a.1 fun b hb ↦ by simp [f, hb]]
      simp [f]
    ext1 b
    calc (∑ a : TightFrameIndex j, inner ℂ (f a) ζ • f a) b
      _ = ∑ T, gramForm (η b T) (ζ b) • η b T := by
        simp only [h_coeff]
        simp [Fintype.sum_prod_type (α₁ := ChoiceIndex j × D.SecondFactorClasses), f,
          Pi.single_apply]
      _ = ((hookNumberMinus j : ℂ) ^ 2 • ζ) b := h_frame b (ζ b)
  · rcases eq_or_ne (i, c) a.1 with hb | hb
    · simpa [f, ← hb] using h_coord (i, c) a.2
    · exact ⟨0, by simp [f, hb]⟩
  · rw [formTupleNormSq, Fintype.sum_eq_single a.1 fun b hb ↦ by simp [f, hb, weylNormSq]]
    simpa [f] using h_norm a.1 a.2 σ

/-- The operator `U_ϑ = comparisonOp j ϑ` is a sum of operators of rank one: if the tuples `f a`
satisfy `∑ a, ⟨f a, ζ⟩ f a = hk² ζ` for all tuples `ζ` of forms on `V°`, with the hook number
`hk = hookNumberMinus j`, then `U_ϑ φ = ∑ n_Aut ⟨φ′, φ⟩ φ′`. Here `n_Aut = D.chosenGroupOrder` and
`φ′` runs over the glued forms `glue_ϑ (f a) = glue j ϑ (f a)`. -/
lemma comparisonOp_eq_sum {j : D.LiftIndex} {ϑ : D.Twist} {f : TightFrameIndex j → FormTuples j}
    (h_frame : ∀ ζ : FormTuples j,
      ∑ a : TightFrameIndex j, inner ℂ (f a) ζ • f a = (hookNumberMinus j : ℂ) ^ 2 • ζ)
    (φ : (D.descentPair ϑ j).FormV) :
    comparisonOp j ϑ φ = ∑ a : TightFrameIndex j,
      (D.chosenGroupOrder • inner ℂ (glue j ϑ (f a)) φ) • glue j ϑ (f a) := by
  have h_sum : ∑ a : TightFrameIndex j, inner ℂ (glue j ϑ (f a)) φ • glue j ϑ (f a) =
      (hookNumberMinus j : ℂ) ^ 2 • glue j ϑ ((glue j ϑ).adjoint φ) := by
    simp only [← adjoint_inner_right, ← map_smul, ← map_sum, h_frame]
  simp [comparisonOp, mul_smul, nsmul_eq_mul, ← smul_sum, ← h_sum]

/-- Let `ϑ` be a twist (a tame character of `U(1)`, ramified at a finite set `Q` of places), `l` a
prime that does not divide the product `ϑ.normQ` of the norms of the places in `Q`, and `ι` a ring
homomorphism `ℂ → ℂ_[l]`. A form on `V_j`, the target of the `j`-th lift, is integral at `ι`
(`integralForms ι`) if for every `g` the vector `g⁻¹ ι (φ g)` has coordinates of norm at most `1`.
The operator `comparisonOp j ϑ`, an integer multiple of the gluing map `glue j ϑ` after its adjoint,
takes integral forms to integral forms. -/
lemma comparisonOp_mem_integralForms {j : D.LiftIndex} {ϑ : D.Twist} {l : ℕ} [Fact l.Prime]
    (ι : PadicPlace l) (hl : l.Coprime ϑ.normQ) {φ : (D.descentPair ϑ j).FormV}
    (hφ : φ ∈ integralForms ι) :
    comparisonOp j ϑ φ ∈ integralForms ι := by
  -- Take the frame `f` at representatives that are integral above `l`. The forms `φ′ = glue (f a)`
  -- are integral at `ι` and at its conjugate, so the coefficients `n_Aut ⟨φ′, φ⟩` are integral.
  have h_exists (c : D.SecondFactorClasses) : ∃ γ : U (stdSpace D.E D.SecondFactorIndex).J,
      (stdSpace D.E D.SecondFactorIndex).embFin γ * c.out ∈ integralAbove D.SecondFactorIndex l :=
    (exists_mul_mem_integralAbove l c.out 1).imp fun _ ↦ And.left
  choose δ hδ using h_exists
  obtain ⟨f, h_frame, h_coord, -⟩ := exists_tight_frame_formTuples j δ
  have h_int (ι' : PadicPlace l) (a : TightFrameIndex j) :
      glue j ϑ (f a) ∈ integralForms ι' := by
    refine glue_mem_integralForms j ϑ ι' hl fun b ↦ ?_
    obtain ⟨z, hz⟩ : ∃ z : WeylIndex D.SecondFactorIndex (untwistedDescentPair j).colsMinus → ℤ,
        (stdSpace D.E D.SecondFactorIndex).weightRep (untwistedDescentPair j).colsMinus 0 (δ b.2)
          (star (f a b)) = Int.cast ∘ z := h_coord a b.1 b.2
    -- The gauge at a rational translate is the gauge of the translated vector.
    rw [← weylGauge_embFin, weylGauge_le_one_iff (ι := ⟨ι'.ιₚ.comp conj⟩) _ (hδ b.2), hz]
    simp [IsUltrametricDist.norm_intCast_le_one]
  rw [comparisonOp_eq_sum h_frame]
  refine sum_mem fun a _ ↦ ?_
  have h_conj : glue j ϑ (f a) ∈ integralForms ⟨ι.ιₚ.comp conj⟩ := h_int _ a
  have h_coeff : ‖ι.ιₚ (D.chosenGroupOrder • inner ℂ (glue j ϑ (f a)) φ)‖ ≤ 1 :=
    (glue j ϑ (f a)).norm_nsmul_inner_le_one φ ι (D.card_classAut_dvd_chosenGroupOrder
      (card_rowIndex_sum_fin_le_two_mul_n D) levelOf_le_stdLevel) h_conj hφ
  exact (integralForms ι).smul_mem ⟨_, h_coeff⟩ (h_int ι a)

/-- A tuple of forms on the definite space `V°` has one value for each pair of an index in
`ChoiceIndex j` and a class in `D.SecondFactorClasses`. The number of these pairs, times the square
of `#(TightFrameIndex j) n_Aut hk²`, is at most `exp (2 f m b log² b)`. Here `TightFrameIndex j` is
the set of such pairs together with a filling with increasing columns of the Young diagrams `μ⁻`
that give the weight of the forms on `V°`, `hk = hookNumberMinus j` is the hook number of `μ⁻` and
`n_Aut = D.chosenGroupOrder` is a multiple of the orders of all stabilisers; `f = D.f` is the number
of infinite places, `m = D.m` the number of lifts in the chain and `b = D.b`, with `log b = D.logB`,
the weight at the infinite places in `D.bPlaces`. -/
lemma card_prod_mul_card_tightFrameIndex_mul_sq_le (j : D.LiftIndex) :
    Fintype.card (ChoiceIndex j × D.SecondFactorClasses) *
        (Fintype.card (TightFrameIndex j) * (D.chosenGroupOrder * hookNumberMinus j ^ 2) : ℝ) ^ 2 ≤
      exp (2 * (D.f * D.m * D.b * D.logB ^ 2)) := by
  set A : ℝ := D.f * D.m * D.b * D.logB ^ 2 with hA
  set N : ℝ := Nat.cast (Fintype.card (ChoiceIndex j × D.SecondFactorClasses))
  have h_aut : (1 : ℝ) ≤ D.chosenGroupOrder := mod_cast NeZero.one_le
  have h_hook : (0 : ℝ) < hookNumberMinus j := Int.cast_pos.2 hookNumber_pos
  have h_classes : (N * D.chosenGroupOrder) ^ 2 ≤ exp A := by
    have hM : (1 : ℝ) ≤ D.M := mod_cast NeZero.one_le
    have hb : 1 ≤ exp D.b := one_le_exp (exp_pos _).le
    -- `M_pow_denominatorExponent_sq_mul_le_exp` has further factors `M` and `exp b`, all of which
    -- are at least `1`.
    calc (N * D.chosenGroupOrder) ^ 2
      _ = (1 ^ (splittingV j 1).denominatorExponent) ^ 2 *
        (1 * (N * (1 * D.chosenGroupOrder)) ^ 2) := by simp
      _ ≤ (D.M ^ (splittingV j 1).denominatorExponent) ^ 2 *
          (exp D.b * (N * (exp D.b * D.chosenGroupOrder)) ^ 2) := by gcongr
      _ ≤ exp A := M_pow_denominatorExponent_sq_mul_le_exp j
  have h_root : N * D.chosenGroupOrder ≤ exp (A / 2) := by
    refine le_of_sq_le_sq ?_ (exp_pos _).le
    rwa [← exp_natCast_mul, Nat.cast_two, mul_div_cancel₀ _ two_ne_zero]
  have h_card : N ≤ exp (A / 2) := (le_mul_of_one_le_right (Nat.cast_nonneg _) h_aut).trans h_root
  have h_pow_x_le : 6 * D.x ^ 999 ≤ A / 2 := by simpa [hA] using D.le_of_hasLogBound
  calc
    _ = N * (N * D.chosenGroupOrder) ^ 2 * (Nat.card (ColumnFilling (fun _ ↦ D.SecondFactorIndex)
        (untwistedDescentPair j).colsMinus) * hookNumberMinus j ^ 2) ^ 2 := by
      rw [Fintype.card_prod _ (ColumnFilling _ _), Nat.card_eq_fintype_card, Nat.cast_mul]
      ring
    _ ≤ exp (A / 2) * exp A * (exp (D.x ^ 999) * exp (D.x ^ 999) ^ 2) ^ 2 := by
      grw [h_classes, h_card, card_columnFilling_colsMinus_le, hookNumberMinus_le]
    _ = exp (A / 2 + A + 6 * D.x ^ 999) := by
      simp only [← exp_natCast_mul, ← exp_add]
      ring_nf
    _ ≤ exp (2 * A) := exp_le_exp.2 (by linarith)

/-- Let `φ` be a form on `V_j`, the target of the `j`-th lift at the trivial twist `1`, and
`φ.normSqAt σ` the weighted sum over classes of the squared norms of its values after applying an
automorphism `σ` of `ℂ`. The operator `U_1 = comparisonOp j 1`, a multiple of the gluing map
`glue j 1` after its adjoint, multiplies this number by at most `exp (6 f m b log² b)`. Here
`f = D.f` is the number of infinite places, `m = D.m` the number of lifts and `b = D.b` the weight
parameter, with `log b = D.logB`. -/
lemma normSqAt_comparisonOp_le (j : D.LiftIndex) (φ : (D.descentPair (1 : D.Twist) j).FormV)
    (σ : ℂ ≃+* ℂ) :
    (comparisonOp j 1 φ).normSqAt σ ≤
      exp (3 * (D.f * D.m * D.b * D.logB ^ 2)) ^ 2 * φ.normSqAt σ := by
  -- `U_1 φ` is glued from the tuple `∑ c a • f a` with `c a = n_Aut ⟨glue (f a), φ⟩`.
  -- Cauchy–Schwarz bounds `σ (c a)`, and there are few terms.
  set A : ℝ := D.f * D.m * D.b * D.logB ^ 2
  obtain ⟨f, h_frame, h_norm⟩ : ∃ f : TightFrameIndex j → FormTuples j,
      (∀ ζ : FormTuples j,
        ∑ a : TightFrameIndex j, inner ℂ (f a) ζ • f a = (hookNumberMinus j : ℂ) ^ 2 • ζ) ∧
      ∀ (a : TightFrameIndex j) (τ : ℂ ≃+* ℂ),
        formTupleNormSq τ (f a) ≤ (hookNumberMinus j : ℝ) ^ 2 :=
    (exists_tight_frame_formTuples j 1).imp fun _ h ↦ h.imp_right And.right
  -- `formTupleNormSq` is the sum of the Gram norms `weylNormSq` of the values of a tuple.
  let hk : ℝ := hookNumberMinus j
  let c (a : TightFrameIndex j) : ℂ := D.chosenGroupOrder • inner ℂ (glue j 1 (f a)) φ
  let S : ℝ := exp (2 * A) * φ.normSqAt σ
  have h_hook : 0 < hk := Int.cast_pos.2 hookNumber_pos
  have h_normSq_nonneg : 0 ≤ φ.normSqAt σ := φ.normSqAt_nonneg σ
  have h_coeff (a : TightFrameIndex j) : ‖σ (c a)‖ ≤ D.chosenGroupOrder * (√S * hk) := by
    calc ‖σ (c a)‖
      _ = D.chosenGroupOrder * ‖σ (inner ℂ (glue j 1 (f a)) φ)‖ := by
        rw [map_nsmul, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
      _ ≤ D.chosenGroupOrder * (√(φ.normSqAt σ) * √(exp (2 * A) * hk ^ 2)) := by
        grw [norm_map_inner_le, normSqAt_glue_le, h_norm]
      _ = _ := by
        rw [sqrt_mul (exp_pos _).le, sqrt_mul (exp_pos _).le, sqrt_sq h_hook.le]
        ring
  have h_value (b : ChoiceIndex j × D.SecondFactorClasses) :
      √(weylNormSq (σ ∘ (∑ a : TightFrameIndex j, c a • f a) b)) ≤
        Fintype.card (TightFrameIndex j) * (D.chosenGroupOrder * hk ^ 2) * √S := by
    have h_term (a : TightFrameIndex j) :
        √(weylNormSq (σ ∘ (c a • f a b))) ≤ D.chosenGroupOrder * hk ^ 2 * √S := by
      have h_single : weylNormSq (σ ∘ f a b) ≤ formTupleNormSq σ (f a) :=
        single_le_sum (fun b _ ↦ weylNormSq_nonneg (σ ∘ f a b)) (mem_univ b)
      calc √(weylNormSq (σ ∘ (c a • f a b)))
        _ = ‖σ (c a)‖ * √(weylNormSq (σ ∘ f a b)) := by
          rw [weylNormSq_comp_smul, sqrt_mul (sq_nonneg _), sqrt_sq (norm_nonneg _)]
        _ ≤ D.chosenGroupOrder * (√S * hk) * √(hk ^ 2) := by grw [h_coeff, h_single, h_norm a σ]
        _ = _ := by
          rw [sqrt_sq h_hook.le]
          ring
    rw [WithLp.ofLp_sum, Finset.sum_apply, mul_assoc, ← nsmul_eq_mul]
    exact (sqrt_weylNormSq_sum_le σ univ _).trans (sum_le_card_nsmul _ _ _ fun a _ ↦ h_term a)
  have h_tupleNormSq : formTupleNormSq σ (∑ a : TightFrameIndex j, c a • f a) ≤
      Fintype.card (ChoiceIndex j × D.SecondFactorClasses) *
        (Fintype.card (TightFrameIndex j) * (D.chosenGroupOrder * hk ^ 2)) ^ 2 * S := by
    rw [mul_assoc, ← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun b _ ↦ ?_
    grw [(sqrt_le_left (by positivity)).1 (h_value b), mul_pow, sq_sqrt (by positivity)]
  calc
    _ = (glue j 1 (∑ a : TightFrameIndex j, c a • f a)).normSqAt σ := by
      simp only [comparisonOp_eq_sum h_frame, map_sum, map_smul, c]
    _ ≤ exp (2 * A) * (exp (2 * A) * S) := by
      grw [normSqAt_glue_le, h_tupleNormSq, card_prod_mul_card_tightFrameIndex_mul_sq_le]
    _ = _ := by
      simp only [S, ← exp_natCast_mul, ← mul_assoc, ← exp_add]
      ring_nf

/-- The operators `U_ϑ = comparisonOp j ϑ = n_Aut hk² glue_ϑ glue_ϑ*` on the forms on `V_j`, one for
each twist `ϑ`, satisfy `IsComparisonOperator`. Here `glue_ϑ = glue j ϑ` builds a form on `V_j` from
a tuple of forms on `V°`, `n_Aut = D.chosenGroupOrder` and `hk = hookNumberMinus j`. That is, for
the theta lift `Θ_ϑ = D.goodLift ϑ j` and the nonzero ratio
`ρ_ϑ = heckeValueProd j ϑ / heckeValueProd j 1` of Hecke values,
`⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩ = ρ_ϑ ⟨y', U° y⟩` with `U°` positive definite and independent of `ϑ`. Also,
`U_ϑ` takes lifts to forms orthogonal to the false lifts, which are the forms orthogonal to the
lifts with the same idempotent and Hecke conditions at a split place. `U_ϑ` keeps integrality above
the primes that do not divide `ϑ.normQ`, and `U_1` multiplies norms by at most
`exp (3 f m b log² b)`, with `f = D.f`, `m = D.m` and `b = D.b`. -/
theorem isComparisonOperator_comparisonOp (j : D.LiftIndex) :
    IsComparisonOperator j (comparisonOp j) where
  ratio_ne_zero ϑ := by simp [heckeValueProd_div_eq, twistFactor_ne_zero]
  exists_inner_eq := by
    -- Take `U° = n_Aut hk² |c′_1|⁻² Θ°* Θ°`; it is positive definite, as `Θ°` is injective.
    let scale : ℝ := D.chosenGroupOrder * hookNumberMinus j ^ 2 / ‖Rows.twistFactor j 1‖ ^ 2
    have h_scale_pos : 0 < scale := div_pos (mul_pos (Nat.cast_pos.2 (NeZero.pos _))
      (sq_pos_of_pos (Int.cast_pos.2 hookNumber_pos))) (by simp [twistFactor_ne_zero])
    refine ⟨(scale : ℂ) • (periodLift j).adjoint ∘ₗ periodLift j, fun y hy ↦ ?_, fun ϑ y' y ↦ ?_⟩
    · have h_norm : 0 < ‖periodLift j y‖ :=
        norm_pos_iff.2 ((map_ne_zero_iff _ (periodLift_injective j)).2 hy)
      rw [LinearMap.smul_apply, inner_smul_right, LinearMap.comp_apply, adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      exact mul_pos (Complex.zero_lt_real.2 h_scale_pos) (pow_pos (Complex.zero_lt_real.2 h_norm) 2)
    · rw [inner_goodLift_comparisonOp, heckeValueProd_div_eq, LinearMap.smul_apply,
        inner_smul_right, LinearMap.comp_apply, adjoint_inner_right]
      have h_ne : (‖Rows.twistFactor j 1‖ : ℂ) ≠ 0 := by simp [twistFactor_ne_zero]
      push_cast [scale]
      field_simp
  isOrthogonalToFalseLifts _ := isOrthogonalToFalseLifts_comparisonOp
  mem_integralForms ϑ l _ ι hl φ hφ := comparisonOp_mem_integralForms ι hl hφ
  normSqAt_le := normSqAt_comparisonOp_le j

end Gluing

/-- The lift `D.goodLift ϑ j` is injective, so the lifts have the dimension of the good forms on
`W_j`. -/
lemma finrank_range_goodLift (j : D.LiftIndex) (ϑ : D.Twist) :
    finrank ℂ (D.goodLift ϑ j).range = finrank ℂ (D.goodForms (D.spaceW j)) :=
  finrank_range_of_inj (by simp [singleLift_injective])

/-- For a split place `w` off the level, the lifts lie in the image of the idempotent `e₀ = D.e₀`
that cuts out the good forms and are killed by the Hecke polynomial `heckePolyOnForms` at
`liftHeckeRoot w`, a power of the norm of `w` times a power of the value of the Weil data's
character at `w`. -/
lemma range_goodLift_le_range_inf_ker {j : D.LiftIndex} {ϑ : D.Twist} {w : FinPlace D.E}
    (hw : star w ≠ w) (hS : w ∉ (D.descentPair ϑ j).places.conjClosure) :
    (D.goodLift ϑ j).range ≤ ((D.descentPair ϑ j).groupAlgAction D.e₀).range ⊓
      ((D.descentPair ϑ j).heckePolyOnForms hw hS ((D.descentPair ϑ j).liftHeckeRoot w)).ker := by
  refine D.range_goodLift_le fun eigensystem y hy c hc h_mem ↦ ?_
  exact ⟨D.range_tupleIdem_le hc h_mem, D.heckePolyOnForms_liftHeckeRoot_singleLift_eq_zero ϑ hw hS
    y⟩

/-- Let `y` be a form on `V_j` that is orthogonal to the false lifts. Then the orthogonal projection
of `y` to the lifts has norm (`normSqAt`) at most that of `y`, at every automorphism `σ` of `ℂ`. -/
lemma normSqAt_starProjection_range_goodLift_le {j : D.LiftIndex} {ϑ : D.Twist}
    {y : (D.descentPair ϑ j).FormV}
    (hy : (D.descentPair ϑ j).IsOrthogonalToFalseLifts D.e₀ (D.goodLift ϑ j).rangeᗮ y)
    (σ : ℂ ≃+* ℂ) :
    normSqAt ((D.goodLift ϑ j).range.starProjection y) σ ≤ normSqAt y σ := by
  obtain ⟨w, hw, hw_off⟩ := (frequently_isSplit_notMem_places (D.descentPair ϑ j)).exists
  exact normSqAt_starProjection_le _ hw hw_off D.isCentralProj_e₀
    (range_goodLift_le_range_inf_ker hw hw_off) hy σ

/-- For operators `U_ϑ` on the forms on `V_j`, the operator `pr U_ϑ` on the lifts (the range of
`D.goodLift ϑ j`), with `pr` the orthogonal projection to them. -/
noncomputable def liftCompression {j : D.LiftIndex}
    (U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV) (ϑ : D.Twist) :
    End ℂ (D.goodLift ϑ j).range :=
  (D.goodLift ϑ j).range.orthogonalProjectionOnto.toLinearMap ∘ₗ
    (U ϑ).domRestrict (D.goodLift ϑ j).range

section Comparison

/-- Let `Θ_ϑ = D.goodLift ϑ j` be the theta lift at the twist `ϑ` to the forms on `V_j`. Its source
is the good forms (the image of the idempotent `D.e₀`, a space of dimension `d`) on the hermitian
space `W_j = D.spaceW j`. Let `ρ_ϑ` be the ratio of the values at `ϑ` and at `1` of
`heckeValueProd j`. Let `U` be a comparison operator, so that `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩ = ρ_ϑ ⟨y', U° y⟩`
with `U°` positive definite. Then the Gram determinant `Θ_ϑ.normDet ^ 2 = det (Θ_ϑ* Θ_ϑ)`, times the
determinant of `pr U_ϑ = liftCompression U ϑ`, is `C ρ_ϑ ^ d` for a constant `C ≠ 0` that does not
depend on `ϑ`. -/
lemma IsComparisonOperator.exists_normDet_sq_mul_det_eq {j : D.LiftIndex}
    {U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV} (hU : IsComparisonOperator j U) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ ϑ : D.Twist,
      (D.goodLift ϑ j).normDet ^ 2 * (liftCompression U ϑ).det =
        C * (heckeValueProd j ϑ / heckeValueProd j 1) ^ finrank ℂ (D.goodForms (D.spaceW j)) := by
  -- `U₀` is positive definite and gives the inner products `⟨Θ_ϑ y', U_ϑ Θ_ϑ y⟩` up to the ratio.
  obtain ⟨U₀, h_pos, h_inner⟩ := hU.exists_inner_eq
  have h_ker : ker U₀ = ⊥ :=
    ker_eq_bot'.2 fun y hy ↦ by_contra fun hy_ne ↦ by simpa [hy] using h_pos y hy_ne
  have h_det : U₀.det ≠ 0 := fun h ↦ (bot_lt_ker_of_det_eq_zero h).ne' h_ker
  refine ⟨U₀.det, h_det, fun ϑ ↦ ?_⟩
  have h_comp : (D.goodLift ϑ j).adjoint ∘ₗ U ϑ ∘ₗ D.goodLift ϑ j =
      (heckeValueProd j ϑ / heckeValueProd j 1) • U₀ := by
    refine LinearMap.ext fun y ↦ ext_inner_left ℂ fun y' ↦ ?_
    rw [LinearMap.smul_apply, inner_smul_right, ← h_inner]
    exact (D.goodLift ϑ j).adjoint_inner_right y' (U ϑ (D.goodLift ϑ j y))
  rw [liftCompression, normDet_sq_mul_det_compression _ (by simp [singleLift_injective]), h_comp,
    LinearMap.det_smul, mul_comm]

/-- Let `ϑ` be a twist, ramified at a finite set `Q` of places with product of norms `ϑ.normQ`, and
`ι` an isomorphism of `ℂ` with `ℚ̄_l` for a prime `l` that does not divide `ϑ.normQ`. Let `U` be a
comparison operator: `U_ϑ` takes lifts to forms orthogonal to the false lifts and keeps integrality
at `ι`. Let `ClearsProjection` hold with `β`: for some operator `Λ` on the lifts with
`|ι (det Λ)| ≥ exp (-d r β)` and the orthogonal projection `pr` to the lifts, `Λ (pr y)` is integral
at `ι` for all integral `y` orthogonal to the false lifts. Then `det (pr U_ϑ)`, with
`pr U_ϑ = liftCompression U ϑ`, has norm at most `exp (d r β)` at `ι`, with `d` the dimension of the
good forms on `W_j = D.spaceW j` and `r = D.r` the rank of `W_j`. -/
lemma IsComparisonOperator.norm_padic_det_liftCompression_le {j : D.LiftIndex}
    {U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV} (hU : IsComparisonOperator j U)
    (ϑ : D.Twist) (ι : PrimePadicIso) (hι : (ι.prime : ℕ).Coprime ϑ.normQ) {β : ℝ}
    (h_clears : D.ClearsProjection ι.iso ϑ j β) :
    ‖ι.iso (liftCompression U ϑ).det‖ ≤
      exp (finrank ℂ (D.goodForms (D.spaceW j)) * (D.r * β)) := by
  -- If `Λ` clears the denominator of the projection, then `Λ pr U_ϑ` keeps the integral lifts, so
  -- its eigenvalues are integral.
  obtain ⟨Λ, h_det, hΛ_integral⟩ := h_clears
  have h_one : ‖ι.iso (Λ * liftCompression U ϑ).det‖ ≤ 1 ^ finrank ℂ (D.goodLift ϑ j).range := by
    refine norm_map_det_le_pow ι.iso.toRingHom _ fun α z hz ↦ ?_
    let ιp : PadicPlace ι.prime := ⟨(algebraMap _ ℂ_[ι.prime]).comp ι.iso.toRingHom⟩
    obtain ⟨c, -, h_int, h_least⟩ : ∃ c : ℂ, c ≠ 0 ∧ c • z.val ∈ integralForms ιp ∧
        ∀ μ : ℂ, μ • c • z.val ∈ integralForms ιp → ‖ιp.ιₚ μ‖ ≤ 1 :=
      DescentPair.exists_smul_mem_integralForms_maximal (Subtype.coe_ne_coe.2 hz.2) ιp
    have h_image : (Λ ((D.goodLift ϑ j).range.orthogonalProjectionOnto (U ϑ (c • z.val))) :
        (D.descentPair ϑ j).FormV) ∈ integralForms ιp :=
      -- `U_ϑ (c • z)` is integral and orthogonal to the false lifts.
      hΛ_integral _ (hU.mem_integralForms ϑ ι.prime ιp hι _ h_int)
        (hU.isOrthogonalToFalseLifts ϑ (c • z))
    have h_apply : Λ ((D.goodLift ϑ j).range.orthogonalProjectionOnto (U ϑ z.val)) = α • z :=
      hz.apply_eq_smul
    have h_eigen : (Λ ((D.goodLift ϑ j).range.orthogonalProjectionOnto (U ϑ (c • z.val))) :
        (D.descentPair ϑ j).FormV) = α • c • z.val := by
      rw [map_smul, map_smul, map_smul, h_apply, smul_comm α c]
      rfl
    rw [h_eigen] at h_image
    -- The place `ιp` is `ι` followed by the isometric inclusion of `ℚ̄_l` into `ℂ_l`.
    have h_norm : ‖algebraMap (PadicAlgCl ι.prime) ℂ_[ι.prime] (ι.iso α)‖ ≤ 1 := h_least α h_image
    simpa using h_norm
  rw [map_mul, map_mul, norm_mul, one_pow] at h_one
  rw [finrank_range_goodLift] at h_det
  set d : ℕ := finrank ℂ (D.goodForms (D.spaceW j))
  have h_mul : exp (-(d * (D.r * β))) * ‖ι.iso (liftCompression U ϑ).det‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_right h_det (norm_nonneg _)).trans h_one
  rwa [Real.exp_neg, inv_mul_le_iff₀ (exp_pos _), mul_one] at h_mul

/-- Let `U` be a comparison operator on the forms on `V_j`, the target of the `j`-th lift, and
`pr U_1 = liftCompression U 1` its compression to the range of the untwisted lift. The image of
`det (pr U_1)` under every ring automorphism `σ` of `ℂ` has modulus at most
`exp (3 d f m b log² b)`. Here `d` is the dimension of the good forms on `W_j = D.spaceW j`,
`f = D.f` the number of infinite places, `m = D.m` the number of lifts in the chain and `b = D.b`,
with `log b = D.logB`, the weight at the infinite places in `D.bPlaces`. -/
lemma IsComparisonOperator.norm_map_det_liftCompression_le {j : D.LiftIndex}
    {U : ∀ ϑ : D.Twist, End ℂ (D.descentPair ϑ j).FormV} (hU : IsComparisonOperator j U)
    (σ : ℂ ≃+* ℂ) :
    ‖σ (liftCompression U 1).det‖ ≤
      exp (finrank ℂ (D.goodForms (D.spaceW j)) * (3 * (D.f * D.m * D.b * D.logB ^ 2))) := by
  rw [exp_natCast_mul, ← finrank_range_goodLift j 1]
  refine norm_map_det_le_pow σ.toRingHom _ fun α z hz ↦ ?_
  have hz_pos : 0 < normSqAt z.val σ := normSqAt_pos (Subtype.coe_ne_coe.2 hz.2) σ
  -- `U_1 z` is orthogonal to the false lifts, so projecting it does not raise its norm at `σ`.
  have h_proj : normSqAt ((D.goodLift (1 : D.Twist) j).range.starProjection (U 1 z)) σ ≤
      normSqAt (U 1 z) σ :=
    normSqAt_starProjection_range_goodLift_le (hU.isOrthogonalToFalseLifts 1 z) σ
  have h_eigen : (D.goodLift (1 : D.Twist) j).range.starProjection (U 1 z) = α • z.val :=
    congrArg Subtype.val hz.apply_eq_smul
  rw [h_eigen, normSqAt_smul] at h_proj
  have h_sq : ‖σ α‖ ^ 2 ≤ exp (3 * (D.f * D.m * D.b * D.logB ^ 2)) ^ 2 :=
    le_of_mul_le_mul_right (h_proj.trans (hU.normSqAt_le z σ)) hz_pos
  exact le_of_sq_le_sq h_sq (exp_pos _).le

end Comparison

/-- The `j`-th power of the trivial `m`-fold twist, formed as a tame character (`TameChar.pow`), is
the trivial tame character `TameChar.one`. -/
lemma mFoldTwist_one_pow (j : ℕ) : (1 : D.MFoldTwist).pow j = (TameChar.one : D.TameChar) := by
  rw [TameChar.pow]
  congr 1 <;> exact one_pow j

/-- The cost of one lift: for a family of twists `ξ_ι = θ ι` as in `IsRegularFamily`, the ratio
`Z_j (1) / Z_j (ξ_ι ^ j)` has height at most `d k (log b · denominatorBudget - directionAmount)`.
Here `d = D.targetDim` is the dimension of the good forms, `k = D.k = D.r + 1 - D.m`,
`log b = D.logB` is a parameter, `denominatorBudget = D.denominatorBudget` is the budget for
denominators and `directionAmount = D.directionAmount` is the sum over the infinite places `σ`, of
weight `κ = D.weight σ`, of `D.jetSize κ = log κ! + κ log (M / Ω)`, the size of a derivative of
order `κ`, less the prime sum `D.primeSum κ σ` that measures its divisibility. -/
lemma heightLe_liftDeterminant_ratio {θ : PrimePadicIso → D.MFoldTwist} (hθ : D.IsRegularFamily θ)
    (j : D.LiftIndex) :
    HeightLe (D.targetDim * (D.k * (D.logB * D.denominatorBudget - D.directionAmount)))
      fun ι : PrimePadicIso ↦ D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j := by
  -- The ratio is `det (pr U_ξ) / det (pr U_1)` times the `d`-th power of the inverse ratio of
  -- Hecke values.
  obtain ⟨β, hβ_sum, hβ_denom⟩ : ∃ β : ℕ → ℝ, D.IsDenominatorBound θ j β :=
    hθ.exists_denominator_bound j
  rw [D.targetDim_eq_finrank_goodForms_spaceW j]
  have hU : IsComparisonOperator j (comparisonOp j) := isComparisonOperator_comparisonOp j
  set d : ℕ := finrank ℂ (D.goodForms (D.spaceW j))
  obtain ⟨C, hC, h_cancel⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ ϑ : D.Twist,
      (D.goodLift ϑ j).normDet ^ 2 * (liftCompression (comparisonOp j) ϑ).det =
        C * (heckeValueProd j ϑ / heckeValueProd j 1) ^ d :=
    hU.exists_normDet_sq_mul_det_eq
  set A : ℝ := D.f * D.m * D.b * D.logB ^ 2
  let Δ (ϑ : D.Twist) : ℂ := (liftCompression (comparisonOp j) ϑ).det
  have h_ratio : ∀ ϑ : D.Twist, heckeValueProd j ϑ / heckeValueProd j 1 ≠ 0 := hU.ratio_ne_zero
  have hΔ_ne (ϑ : D.Twist) : Δ ϑ ≠ 0 :=
    right_ne_zero_of_mul ((h_cancel ϑ).trans_ne (mul_ne_zero hC (pow_ne_zero d (h_ratio ϑ))))
  have h_arch (σ : ℂ ≃+* ℂ) : ‖σ (Δ 1)‖ ≤ exp (d * (3 * A)) := hU.norm_map_det_liftCompression_le σ
  have h_padic (ι : PrimePadicIso) :
      ‖ι.iso (Δ ((θ ι).powTwist j))‖ ≤ exp (d * (D.r * β ι.prime)) :=
    hU.norm_padic_det_liftCompression_le ((θ ι).powTwist j) ι (hθ.coprime ι)
      (hβ_denom ι).clearsProjection
  -- Take `Δ 1` as the denominator; its conjugates and the norms of `Δ ξ` at `ι` bound the height.
  have h_height : HeightLe (d * (3 * A) + d * (D.r * D.denominatorBudget))
      fun ι : PrimePadicIso ↦ Δ ((θ ι).powTwist j) / Δ 1 := by
    refine .of_mul_le (e := fun l : ℕ ↦ d * (D.r * β l)) (hΔ_ne 1) h_arch (fun ι ↦ ?_)
      fun T hT ↦ ?_
    · simpa only [mul_div_cancel₀ _ (hΔ_ne 1)] using h_padic ι
    · grw [← mul_sum, ← mul_sum, hβ_sum T hT]
  refine (h_height.mul ((heightLe_inv_heckeValueProd_div hθ j).pow d)).mono ?_ fun ι ↦ ?_
  · have h_bound : 3 * A + D.r * D.denominatorBudget +
      (10 * D.m * D.x₁ + D.k * (6 * D.denominatorBudget - D.directionAmount)) ≤
        D.k * (D.logB * D.denominatorBudget - D.directionAmount) := by
      simpa [A, mul_sub, add_sub] using D.le_of_hasLogBound
    rw [← mul_add, ← mul_add]
    gcongr
  · set ρ : ℂ := heckeValueProd j ((θ ι).powTwist j) / heckeValueProd j 1
    have h_twist : D.liftDeterminant (θ ι) j * Δ ((θ ι).powTwist j) = C * ρ ^ d :=
      h_cancel ((θ ι).powTwist j)
    have h_trivial : D.liftDeterminant 1 j * Δ 1 = C := by
      rw [liftDeterminant, mFoldTwist_one_pow]
      exact (h_cancel 1).trans (by simp [(div_ne_zero_iff.1 (h_ratio 1)).2])
    have hρ : ρ ≠ 0 := h_ratio ((θ ι).powTwist j)
    have h_eq : D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j =
        Δ ((θ ι).powTwist j) / Δ 1 * ρ⁻¹ ^ d := by
      rw [eq_div_of_mul_eq (hΔ_ne _) h_twist, eq_div_of_mul_eq (hΔ_ne _) h_trivial, inv_pow]
      field [hΔ_ne, pow_ne_zero d hρ]
    rw [h_eq, Pi.mul_apply, Pi.pow_apply]

end New.Data
