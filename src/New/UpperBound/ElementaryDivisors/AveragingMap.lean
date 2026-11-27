module

import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import New.UpperBound.ElementaryDivisors.RootLemma
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
public import New.UpperBound.ElementaryDivisors.TwistingData
import Lib.General.LinearAlgebra.HermiteForm
public import New.UpperBound.ElementaryDivisors.InvariantAverage
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

section
/-!
# The substitution by Frobenius powers of generic matrices; weight and defect

Fix a Frobenius cycle `T` (`New.FrobeniusCycle`; letters `s : ZMod N`, even or odd, `P` a power of
the prime `p`, `q = P ^ N`, `w ^ 2 = p`). The twists `T.embedding s g` are not algebraic in `g`, but
modulo `p` they are entrywise powers of one another. So we take one generic `k × k` matrix for each
letter (a copy) and let the copy `s - d`, `0 ≤ d ≤ ℓ`, act on the letter `s` through its entrywise
power `P ^ d`, or through the cofactor matrix of this power if `s` is odd; the last factor, `d = ℓ`,
acts on the deep variables only. The matrix of this substitution on forms is
`New.FrobeniusCycle.substitutionOperator` at the factors `New.FrobeniusCycle.frobGenericMatrix`.
Matrices act on vectors of coefficients, so they are the transposes of the matrices that are
substituted in the variables: the row index of an entry here is its column index there.

* `New.FrobeniusCycle.substitutionOperator_map_eq_conj`: conjugation of the factors by a block
  diagonal matrix.
* `New.FrobeniusCycle.copyWeight`: the weight of a monomial in the entries of all copies.
* `New.FrobeniusCycle.abs_defect_sub_copyWeight_le`: let `a' = a + 1`, `ℓ ≤ N` and
  `N n k (ℓ + 2) ≤ P ^ ℓ`, and take an entry in row `β` of the operator with `r = a'` at the factors
  `New.FrobeniusCycle.conjFrobGenericMatrix h` (the generic factors after a change of frame by `h`).
  If the coefficient of a monomial in it is not divisible by `w ^ c`, the weight of the monomial at
  the copy `i` is within `c* = 3 k c` of the defect of `β` at the letter `i + ℓ`.

A term of an entry of a product of matrices belongs to a path of indices. The weight of a step is a
difference of two scaled index weights (`New.FrobeniusCycle.scaledIndexWeight`) up to `1 / P ^ ℓ`,
so the weights telescope along a path and leave the scaled index weight of its last index, up to
`(ℓ + 2) / P ^ ℓ`. For an even letter this scaled index weight is `1 - 1 / q` times the defect
weight. For an odd letter the cofactor matrix changes its sign, which again gives this multiple of
the defect weight, and multiplies the loss by at most `k`. What remains, the defect divided by `q`,
has size at most `1`, as `2 n ≤ q`. `New.FrobeniusCycle.substitutionOperator_mem` carries this out
for all terms at once. An element has level `t` in a filtration `G` (`New.IsRealFiltration`) if it
lies in `G t`, and the levels of the entries are bounded from the levels of the factors. The main
filtrations used are `New.gaussFiltration (New.adicFiltration w) ω`: divisibility of coefficients by
powers of `w`, shifted by weights `ω` of the variables. They also absorb the error terms, which are
multiples of `p` (`New.FrobeniusCycle.conjFrobGenericMatrix_mem_gaussFiltration`). With `0` in place
of `w` the level bounds the weights of the monomials that occur.

Notions from other files:
* `New.FrobeniusCycle.deepIndicator`: the indicator of the deep variables `(b, s)`: it is `1` if `s`
  is even and `r ≤ b`, or `s` is odd and `b < r`, and `0` otherwise.
* `New.FrobeniusCycle.defectWeight i a a'`: the weight of `(b, s)` is
  `± P ^ ((s - i) mod N) / (q - 1)` for `b = a, a'` (with the sign `+` at `a'` for even and at `a`
  for odd `s`, and `1` added to the positive weight at `s = i`), and `0` for other `b`. The defect
  of a monomial at the letter `i` is the sum of these weights over its variables.
* `New.exponentOf`: a family `β` of exponent vectors, one for each letter, as one exponent vector on
  the variables `(b, s)`.
* `New.levi W (New.twoBlock k r)`: the block diagonal matrices in `GL_k(W)` with blocks of sizes `r`
  and `k - r`.

## Notation

Here `h` is a matrix in `GL_k(W)`, not a form.
-/

@[expose] public section

noncomputable section

namespace New.FrobeniusCycle

open MvPolynomial Matrix Finsupp SetLike IsRealFiltration Ideal.Quotient Fintype Function List Nat

variable {N k : ℕ} {W O R : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
  [CommRing R] (T : FrobeniusCycle N W O)

/-! ### The substitution and the weights -/

/-- The generic matrix of the copy `s - d`, whose entries are the variables `X (s - d, b, c)`, with
its entries raised to the power `P ^ d`. -/
abbrev frobGenericMatrix (s : ZMod N) (d : ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (ZMod N × Fin k × Fin k) O) :=
  of fun b c : Fin k ↦ X (s - d, b, c) ^ T.P ^ d

/-- The matrix `M` if the letter `s` is even, and the transposed adjugate of `M` if `s` is odd. -/
def parityCofactor (s : ZMod N) (M : Matrix (Fin k) (Fin k) R) : Matrix (Fin k) (Fin k) R :=
  if T.isEven s then M else M.adjugateᵀ

/-- The matrix of the letter `s` in `substitutionOperator`. Its row `b` is row `b` of
`T.parityCofactor s` of the product `ψ s (m - 1) * ⋯ * ψ s 0`, where `m = ℓ + 1` if the variable
`(b, s)` is deep (`T.deepIndicator r (b, s) = 1`) and `m = ℓ` if not. -/
def substitutionLetterMatrix (r ℓ : ℕ) (ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R) (s : ZMod N) :
    Matrix (Fin k) (Fin k) R :=
  of fun b c : Fin k ↦
    T.parityCofactor s ((range (ℓ + T.deepIndicator r (b, s))).map (ψ s)).reverse.prod b c

/-- The Kronecker product over the letters `s` of the `n`-th symmetric powers of the matrices
`T.substitutionLetterMatrix r ℓ ψ s`. In use the factors `ψ s d` are the entrywise powers `P ^ d` of
the copies `s - d` (`frobGenericMatrix`), or these after a change of frame
(`conjFrobGenericMatrix`). -/
def substitutionOperator (r ℓ n : ℕ) (ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R) :
    Matrix (Exponents N k n) (Exponents N k n) R :=
  kroneckerPi fun s : ZMod N ↦ symPowMatrix n (T.substitutionLetterMatrix r ℓ ψ s)

/-- Conjugation `M ↦ ι(h) M ι(h)⁻¹` by the image of `h` under `ι = T.embedding s`. -/
def letterConj (h : GL (Fin k) W) (s : ZMod N) :
    Matrix (Fin k) (Fin k) O →* Matrix (Fin k) (Fin k) O where
  toFun M := h.val.map (T.embedding s) * M * h⁻¹.val.map (T.embedding s)
  map_one' := by simp
  map_mul' := by simp [mul_assoc, ← (h.val⁻¹.map _).mul_assoc]

/-- The integer vector `ρ = e_{a'} - e_a`: its entry at `a'` is `1`, at `a` it is `-1`, and the
other entries are `0` (for `a ≠ a'`). For `a' = a + 1` it is minus the simple root
`e_a - e_{a + 1}` of `GL_k`. -/
def _root_.New.rootVector (a a' b : Fin k) : ℤ :=
  (if b = a' then 1 else 0) - if b = a then 1 else 0

/-- The weight of the index `b`: the entry at `b` of `ρ = New.rootVector a a'`, divided by
`P ^ ℓ`. -/
def indexWeight (ℓ : ℕ) (a a' b : Fin k) : ℝ :=
  rootVector a a' b / (T.P ^ ℓ : ℝ)

/-- The weight at the copy `i` of a monomial `ν` in the entries of all the generic matrices. For a
monomial in one matrix let `row` and `col` be the sums of the entries of
`ρ = New.rootVector a a'` over its row indices and over its column indices. The weight is
`P ^ (-ℓ)` times the sum of `row` at the copy `i` and of `P ^ (-u) (row - col)` at the copies
`i - u`, `0 < u < N`. -/
def copyWeight (ℓ : ℕ) (a a' : Fin k) (i : ZMod N) (ν : ZMod N × Fin k × Fin k →₀ ℕ) : ℝ :=
  ((weight (fun v : Fin k × Fin k ↦ rootVector a a' v.1) (ν.curry i) : ℤ) +
    ∑ j ∈ Finset.univ.erase i, (T.P ^ (j - i).val / T.q : ℝ) *
      ((weight (fun v : Fin k × Fin k ↦ rootVector a a' v.1) (ν.curry j) : ℤ) -
        (weight (fun v : Fin k × Fin k ↦ rootVector a a' v.2) (ν.curry j) : ℤ))) / T.P ^ ℓ

/-- The scaled index weight of the index `b` at the exponent `m`: its weight
`New.FrobeniusCycle.indexWeight` times `P ^ m / q`. -/
def scaledIndexWeight (ℓ : ℕ) (a a' : Fin k) (m : ℕ) (b : Fin k) : ℝ :=
  T.indexWeight ℓ a a' b * (T.P ^ m / T.q)

/-- The weight at the copy `i` of the entry `(b, c)` of the generic matrix of the copy `j`: the
weight of the row `b` if `j = i`, and else the difference of the scaled index weights of `b` and `c`
at the exponent `(j - i) mod N`. -/
def entryWeight (ℓ : ℕ) (a a' : Fin k) (i : ZMod N) (v : ZMod N × Fin k × Fin k) : ℝ :=
  if v.1 = i then T.indexWeight ℓ a a' v.2.1
  else T.scaledIndexWeight ℓ a a' (v.1 - i).val v.2.1 - T.scaledIndexWeight ℓ a a' (v.1 - i).val
    v.2.2

/-- The adjugate commutes with conjugation: if `A B = 1`, then `B adj(A M B) A = adj(M)`. -/
lemma _root_.New.mul_adjugate_conj_mul {A B : Matrix (Fin k) (Fin k) R} (hAB : A * B = 1)
    (M : Matrix (Fin k) (Fin k) R) : B * (A * M * B).adjugate * A = M.adjugate :=
  calc B * (A * M * B).adjugate * A
      = B * B.adjugate * M.adjugate * (A.adjugate * A) := by
        simp only [adjugate_mul_distrib, mul_assoc]
    _ = M.adjugate := by simp [mul_adjugate, adjugate_mul, smul_smul, ← det_mul, hAB]

section

omit [NeZero N]

variable {h : GL (Fin k) W} {s : ZMod N} {r : ℕ}

/-- Let `T` be a Frobenius cycle, with ring maps `ι = T.embedding s : W → O` for the letters
`s : ZMod N`, each even or odd, and let `h` be in `GL_k(W)`. For even `s`, `T.parityCofactor s M`
is `M` and `T.letterMatrix s h` is `ι(h)`; for odd `s` they are the transposed adjugate of `M` and
the inverse transpose of `ι(h)`. Conjugation by `T.letterMatrix s h` undoes the conjugation
`T.letterConj h s M = ι(h) M ι(h)⁻¹` inside `T.parityCofactor s`. -/
lemma letterMatrix_mul_parityCofactor_letterConj_mul (M : Matrix (Fin k) (Fin k) O) :
    T.letterMatrix s h⁻¹ * T.parityCofactor s (T.letterConj h s M) * T.letterMatrix s h =
      T.parityCofactor s M := by
  let A : Matrix (Fin k) (Fin k) O := h.val.map (T.embedding s)
  let B : Matrix (Fin k) (Fin k) O := h⁻¹.val.map (T.embedding s)
  have hAB : A * B = 1 := by simp [A, B]
  rw [show T.letterConj h s M = A * M * B from rfl, parityCofactor, parityCofactor,
    letterMatrix_apply, letterMatrix_apply, inv_inv]
  split_ifs
  · calc B * (A * M * B) * A = B * A * M * (B * A) := by simp only [mul_assoc]
      _ = M := by rw [mul_eq_one_comm.1 hAB, one_mul, mul_one]
  · calc Aᵀ * (A * M * B).adjugateᵀ * Bᵀ = (B * (A * M * B).adjugate * A)ᵀ := by
          simp only [transpose_mul, mul_assoc]
      _ = M.adjugateᵀ := by rw [mul_adjugate_conj_mul hAB]

/-- The map `T.parityCofactor s` commutes with applying a ring map to all entries. -/
lemma parityCofactor_map (χ : R →+* O) (M : Matrix (Fin k) (Fin k) R) :
    (T.parityCofactor s M).map χ = T.parityCofactor s (M.map χ) := by
  unfold parityCofactor
  split_ifs
  exacts [rfl, congrArg Matrix.transpose (χ.map_adjugate M)]

/-- If `h` is block diagonal with blocks cut at `r`, then `T.letterMatrix s h⁻¹` mixes row `b` only
with the rows `x` for which `(x, s)` has the same depth `T.deepIndicator r` as `(b, s)`. -/
lemma letterMatrix_inv_apply_eq_zero (h_levi : h ∈ levi W (twoBlock k r)) {b x : Fin k}
    (h_depth : T.deepIndicator r (b, s) ≠ T.deepIndicator r (x, s)) :
    T.letterMatrix s h⁻¹ b x = 0 := by
  have h_ne : twoBlock k r b ≠ twoBlock k r x := by grind [deepIndicator, twoBlock]
  rw [letterMatrix_apply]
  split_ifs
  · rw [map_apply, show h⁻¹.val b x = 0 from inv_mem h_levi b x h_ne, map_zero]
  · simp [show h.val x b = 0 from h_levi x b h_ne.symm]

end

section

variable {h : GL (Fin k) W} {r ℓ n : ℕ} {ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R}

omit [NeZero N] in
/-- Let `T` be a Frobenius cycle, with ring maps `ι = T.embedding s : W → O` for the letters `s`,
and let `h` in `GL_k(W)` be block diagonal with blocks of sizes `r` and `k - r`. Row `b` of
`T.substitutionLetterMatrix r ℓ ψ s` is row `b` of `ψ s (m - 1) * ⋯ * ψ s 0` for even `s`, and of
its transposed adjugate for odd `s`, where `m = ℓ + T.deepIndicator r (b, s)` is `ℓ` on one block
and `ℓ + 1` on the other. Apply a ring map `χ` to all entries. If `S` is this matrix and `S'` the
one formed from the factors `ι(h) (ψ s d) ι(h)⁻¹` (`T.letterConj`), then `S = H⁻¹ S' H`, where
`H = T.letterMatrix s h` is `ι(h)` for even `s` and its inverse transpose for odd `s`. -/
lemma substitutionLetterMatrix_map (χ : R →+* O) (h_levi : h ∈ levi W (twoBlock k r)) (s : ZMod N) :
    (T.substitutionLetterMatrix r ℓ ψ s).map χ =
      T.letterMatrix s h⁻¹ *
        T.substitutionLetterMatrix r ℓ
          (fun (t : ZMod N) (d : ℕ) ↦ T.letterConj h t ((ψ t d).map χ)) s *
        T.letterMatrix s h := by
  -- The length of the product in row `b` depends only on `T.deepIndicator r (b, s)`, and
  -- `T.letterMatrix s h⁻¹` mixes only rows with the same value of it.
  have h_prod (m : ℕ) : (T.parityCofactor s ((range m).map (ψ s)).reverse.prod).map χ =
      T.letterMatrix s h⁻¹ *
        T.parityCofactor s
          ((range m).map fun d : ℕ ↦ T.letterConj h s ((ψ s d).map χ)).reverse.prod *
        T.letterMatrix s h := by
    rw [parityCofactor_map, ← RingHom.mapMatrix_apply,
      ← letterMatrix_mul_parityCofactor_letterConj_mul (h := h)]
    simp only [map_list_prod, List.map_reverse, List.map_map, comp_def, RingHom.mapMatrix_apply]
  have h_row (ψ' : ZMod N → ℕ → Matrix (Fin k) (Fin k) O) (b y : Fin k) :
      (T.letterMatrix s h⁻¹ * T.substitutionLetterMatrix r ℓ ψ' s) b y =
        (T.letterMatrix s h⁻¹ * T.parityCofactor s
          ((range (ℓ + T.deepIndicator r (b, s))).map (ψ' s)).reverse.prod) b y := by
    simp only [Matrix.mul_apply, substitutionLetterMatrix, of_apply]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h_depth : T.deepIndicator r (b, s) = T.deepIndicator r (x, s)
    · rw [h_depth]
    · simp [T.letterMatrix_inv_apply_eq_zero h_levi h_depth]
  ext b c
  rw [map_apply, substitutionLetterMatrix, of_apply, ← map_apply (f := χ), h_prod]
  simp only [Matrix.mul_apply (M := _ * _), h_row]

/-- Apply a ring map `χ` to all entries, and let `h` be block diagonal with blocks cut at `r`.
Conjugating each factor `ψ s d` by `h` through `T.embedding s` conjugates `T.substitutionOperator`
by `T.letterRep n h`, the matrix of `h` on forms of degree `n` in each letter. -/
lemma substitutionOperator_map_eq_conj (χ : R →+* O) (h_levi : h ∈ levi W (twoBlock k r)) :
    (T.substitutionOperator r ℓ n ψ).map χ =
      T.letterRep n h⁻¹ *
        T.substitutionOperator r ℓ n (fun (s : ZMod N) (d : ℕ) ↦ T.letterConj h s ((ψ s d).map χ)) *
        T.letterRep n h := by
  simp_rw [letterRep_apply, substitutionOperator, ← kroneckerPi_mul, ← map_mul, ← kroneckerPi_map,
    ← symPowMatrix_map, T.substitutionLetterMatrix_map χ h_levi]

/-- Applying a ring map to the Frobenius cycle does not change the operator, which uses only the
parities of the letters. -/
lemma substitutionOperator_frobeniusCycle_map {O' : Type} [CommRing O'] (χ : O →+* O') :
    (T.map χ).substitutionOperator r ℓ n ψ = T.substitutionOperator r ℓ n ψ :=
  rfl

/-- If all factors `ψ s d` are the identity matrix, then the substitution operator
`T.substitutionOperator r ℓ n ψ` is the identity matrix. -/
lemma substitutionOperator_one :
    T.substitutionOperator r ℓ n (fun (_ : ZMod N) (_ : ℕ) ↦ (1 : Matrix (Fin k) (Fin k) R)) =
      1 := by
  have h_letter (s : ZMod N) :
      T.substitutionLetterMatrix (k := k) (R := R) r ℓ (fun _ _ ↦ 1) s = 1 :=
    Matrix.ext fun b c ↦ by simp [substitutionLetterMatrix, parityCofactor]
  simp [substitutionOperator, h_letter]

end

/-! ### Levels of the entries in a filtration -/

section

variable {h : GL (Fin k) W} {s : ZMod N} {r ℓ n d : ℕ} {a a' : Fin k}
  {ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R}

/-- Let each entry of row `b` of `M` lie in `G (x b - v)` for the filtration `G`, where `v ≥ 0` and
the `x b` add up to `0`. Then each entry of row `b` of the transposed adjugate `M.adjugateᵀ` (the
cofactor matrix) lies in `G (-x b - k * v)`. -/
lemma _root_.New.adjugate_transpose_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {M : Matrix (Fin k) (Fin k) R} {x : Fin k → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hx_sum : ∑ b : Fin k, x b = 0) (hM : ∀ b c : Fin k, M b c ∈ G (x b - v)) (b c : Fin k) :
    M.adjugateᵀ b c ∈ G (-x b - k * v) := by
  -- A cofactor in row `b` is a sum of products of entries of the other rows.
  rw [transpose_apply, adjugate_apply, ← det_transpose, det_apply]
  refine sum_mem fun π _ ↦ zsmul_mem (antitone ?_ <|
    prod_mem_graded G (update (fun i ↦ x i - v) b 0) _ fun i _ ↦ ?_) _
  · simp [Finset.sum_update_of_mem, Finset.sum_sub_distrib, hx_sum, Finset.card_sdiff,
      Finset.inter_univ, cast_pred b.pos]
    linarith
  · obtain rfl | hi := eq_or_ne i b
    · by_cases hc : π i = c <;> simp [hc, one_mem_graded G]
    · simpa [hi] using hM i (π i)

/-- Let the entries of row `b` of `M` have level `y b` in the filtration `G`. Rows and columns of
the `n`-th symmetric power of `M` are indexed by exponent vectors of degree `n`, and row `β` has
level `∑ b, β b * y b`. -/
lemma _root_.New.symPowMatrix_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {M : Matrix (Fin k) (Fin k) R} {y : Fin k → ℝ} (hM : ∀ b c : Fin k, M b c ∈ G (y b))
    (β γ : Monomials (Fin k) n) : symPowMatrix n M β γ ∈ G (weight y β.val) := by
  -- Give the variable `b` the weight `-y b`. The image of each variable has Gauss level `0`, hence
  -- so has the image of each monomial.
  have h_var (c : Fin k) : ∑ b : Fin k, M b c • X b ∈ gaussFiltration G (-y) 0 := by
    refine sum_mem fun b _ ↦ ?_
    rw [X, smul_monomial, smul_eq_mul, mul_one]
    exact monomial_mem_gaussFiltration (by simpa [weight_single] using hM b c)
  have h_monomial : linSubst M (monomial γ.val 1) ∈ gaussFiltration G (-y) 0 := by
    simpa [linSubst, aeval_monomial, Finsupp.prod] using
      prod_pow_mem_graded (gaussFiltration G (-y)) 0 _ γ.val fun c _ ↦ h_var c
  change (linSubst M (monomial γ.val 1)).coeff β.val ∈ G (weight y β.val)
  simpa [weight_eq_sum] using h_monomial β.val

/-- Filtration levels add up along a product. Suppose that for `d < m` each entry `(b, c)` of `A d`
lies in `G (α (d + 1) b - α d c - u)` for the filtration `G`, and that `α 0 b ≤ u` for all `b`. Then
each entry of row `b` of `A (m - 1) * ⋯ * A 0` lies in `G (α m b - (m + 1) * u)`. -/
lemma _root_.New.reverse_prod_map_range_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {A : ℕ → Matrix (Fin k) (Fin k) R} {α : ℕ → Fin k → ℝ} {u : ℝ} {m : ℕ}
    (hα_zero : ∀ b : Fin k, α 0 b ≤ u)
    (hA : ∀ d < m, ∀ b c : Fin k, A d b c ∈ G (α (d + 1) b - α d c - u)) (b c : Fin k) :
    ((range m).map A).reverse.prod b c ∈ G (α m b - (m + 1) * u) := by
  induction m generalizing b with
  | zero =>
    simp only [range_zero, List.map_nil, List.reverse_nil, List.prod_nil, Matrix.one_apply]
    split_ifs
    exacts [antitone (by simpa using hα_zero b) (one_mem_graded G), zero_mem _]
  | succ m ih =>
    simp only [range_succ, List.map_append, List.reverse_append, List.prod_append,
      List.map_singleton, List.reverse_singleton, List.prod_singleton, Matrix.mul_apply]
    refine sum_mem fun y _ ↦ ?_
    rw [show α (m + 1) b - ((m + 1 : ℕ) + 1) * u =
      α (m + 1) b - α m y - u + (α m y - (m + 1) * u) by grind]
    exact mul_mem_graded (hA m m.lt_succ_self b y) (ih (fun d hd ↦ hA d (lt_succ_of_lt hd)) y)

omit [NeZero N] in
/-- Let the entries of row `b` of the `k × k` matrix `M` have level `x b - v` in the filtration `G`
(that is, lie in `G (x b - v)`), where `v ≥ 0` and the `x b` add up to `0`. The matrix
`T.parityCofactor s M` is `M` for an even letter `s` and the transposed adjugate of `M` for an odd
one. Its row `b` has level `± x b - k v`, with the sign `+` for even and `-` for odd `s`. -/
lemma parityCofactor_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    {M : Matrix (Fin k) (Fin k) R} {x : Fin k → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hx_sum : ∑ b : Fin k, x b = 0) (hM : ∀ b c : Fin k, M b c ∈ G (x b - v)) (b c : Fin k) :
    T.parityCofactor s M b c ∈ G ((if T.isEven s then 1 else -1) * x b - k * v) := by
  unfold parityCofactor
  split_ifs
  · have hk : (1 : ℝ) ≤ k := by exact_mod_cast b.pos
    exact antitone (by nlinarith) (hM b c)
  · simpa only [neg_one_mul] using adjugate_transpose_mem G hv hx_sum hM b c

/-- Let `T` be a Frobenius cycle, whose letters `s : ZMod N` are even or odd (`T.isEven`). The
variable `(b, s)` is deep (`T.deepIndicator r (b, s) = 1`, else `0`) if `r ≤ b` for even and `b < r`
for odd `s`. The matrix `T.substitutionOperator r ℓ n ψ` is the Kronecker product over `s` of the
`n`-th symmetric powers of the matrices whose row `b` is that of `ψ s (m - 1) * ⋯ * ψ s 0` (of its
transposed adjugate for odd `s`), with `m = ℓ + 1` or `ℓ` as `(b, s)` is deep or not. Its rows are
indexed by families `β` of exponent vectors `β s` of degree `n`, and `exponentOf β` sends `(b, s)`
to `β s b`. Let `G` be a filtration of `R` (an element of `G t` has level `t`), `u ≥ 0`, and
`α s d` real vectors of sum zero (potentials) with `|α s 0 b| ≤ u`. Let entry `(b, c)` of `ψ s d`
have level `α s (d + 1) b - α s d c - u` for `d ≤ ℓ`, and let `x (b, s) = ± α s m b`, with `+` for
even `s`. Then row `β` has level `∑ b s, β s b * x (b, s) - N n k (ℓ + 2) u`. -/
lemma substitutionOperator_mem (G : ℝ → AddSubgroup R) [IsRealFiltration G]
    (α : ZMod N → ℕ → Fin k → ℝ) (x : Fin k × ZMod N → ℝ) (u : ℝ) {β γ : Exponents N k n}
    (hα_zero : ∀ (s : ZMod N) (b : Fin k), |α s 0 b| ≤ u)
    (hα_sum : ∀ (s : ZMod N) (d : ℕ), ∑ b : Fin k, α s d b = 0)
    (hx : ∀ (b : Fin k) (s : ZMod N),
      x (b, s) = (if T.isEven s then 1 else -1) * α s (ℓ + T.deepIndicator r (b, s)) b)
    (hψ : ∀ s : ZMod N, ∀ d ≤ ℓ, ∀ b c : Fin k, ψ s d b c ∈ G (α s (d + 1) b - α s d c - u))
    (hu : 0 ≤ u) :
    T.substitutionOperator r ℓ n ψ β γ ∈
      G (weight x (exponentOf β) - N * n * k * (ℓ + 2) * u) := by
  let K : ℝ := k * ((ℓ + 2) * u)
  -- The potentials telescope along the product of `m ≤ ℓ + 1` factors.
  have h_prod (s : ZMod N) (m : ℕ) (hm : m ≤ ℓ + 1) (b c : Fin k) :
      ((range m).map (ψ s)).reverse.prod b c ∈ G (α s m b - (ℓ + 2) * u) := by
    have h_loss : (m + 1) * u ≤ (ℓ + 2) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast succ_le_succ hm) hu
    exact antitone (sub_le_sub_left h_loss (α s m b)) (reverse_prod_map_range_mem G
      (fun b ↦ le_of_abs_le (hα_zero s b)) (fun d hd ↦ hψ s d (by lia)) b c)
  have h_row (s : ZMod N) (b c : Fin k) :
    T.substitutionLetterMatrix r ℓ ψ s b c ∈ G (x (b, s) - K) := by
    rw [hx, substitutionLetterMatrix, of_apply]
    exact T.parityCofactor_mem G (by positivity) (hα_sum s _)
      (h_prod s _ (by grind [deepIndicator])) b c
  -- Pass to the symmetric powers, whose rows have degree `n`, and multiply over the letters.
  have h_letter (s : ZMod N) : weight (fun b : Fin k ↦ x (b, s) - K) (β s).val =
      weight (fun b : Fin k ↦ x (b, s)) (β s).val - n * K := by
    simp [weight_eq_sum, mul_sub, ← Finset.sum_mul, ← cast_sum, ← degree_eq_sum,
      Monomials.degree_eq]
  have h_split : weight x (exponentOf β) =
      ∑ s : ZMod N, weight (fun b : Fin k ↦ x (b, s)) (β s).val := by
    simp [exponentOf, weight_eq_sum, sum_prod_type_right]
  have h_level : weight x (exponentOf β) - N * n * k * (ℓ + 2) * u =
      ∑ s : ZMod N, weight (fun b : Fin k ↦ x (b, s) - K) (β s).val := by
    simp [h_letter, h_split, Finset.sum_sub_distrib, K]
    ring
  rw [h_level, substitutionOperator, kroneckerPi, of_apply]
  exact prod_mem_graded G _ _ fun s _ ↦ symPowMatrix_mem G (h_row s) (β s) (γ s)

/-! ### Weights of indices and the Gauss filtration -/

omit [NeZero N] in
lemma abs_indexWeight_le (b : Fin k) : |T.indexWeight ℓ a a' b| ≤ 1 / T.P ^ ℓ := by
  rw [indexWeight, abs_div, abs_pow, abs_cast]
  gcongr
  unfold rootVector
  split_ifs <;> simp

/-- Let `T` be a Frobenius cycle: its letters `s : ZMod N` are alternately even and odd
(`T.isEven`), `P = T.P` is its prime power and `q = T.q = P ^ N`. Let `a' = a + 1`. The defect
weight `T.defectWeight j a a' (b, s)` at a letter `j` is `± P ^ ((s - j) mod N) / (q - 1)` for
`b = a, a'` (positive at `a'` for even and at `a` for odd `s`, with `1` added to the positive weight
if `s = j`) and `0` for other `b`. For `j = i + ℓ`, this weight times `1 - 1 / q` is
`± ρ b / P ^ ℓ * P ^ (d + m) / q`, with `+` for even and `-` for odd `s`. Here `ρ b` is `1` at `a'`,
`-1` at `a` and else `0`, `ρ b / P ^ ℓ` is the index weight of `b`, `m = (s - d - i) mod N`, and
`d = ℓ + 1` or `ℓ` as `(b, s)` is deep for the cut at `a'` or not. -/
lemma mul_defectWeight_eq_indexWeight_mul (ha : (a : ℕ) + 1 = (a' : ℕ)) (i : ZMod N) (b : Fin k) :
    (1 - 1 / T.q) * T.defectWeight (i + ℓ) a a' (b, s) =
      (if T.isEven s then 1 else -1) * T.indexWeight ℓ a a' b *
        (T.P ^ (ℓ + T.deepIndicator a' (b, s) +
          (s - (ℓ + T.deepIndicator a' (b, s) : ℕ) - i).val) / T.q) := by
  have hlt : a < a' := Fin.lt_def.2 (by lia)
  -- The factor `P ^ ℓ` cancels against the denominator of the index weight, and
  -- `1 - 1 / q = (q - 1) / q`, so it is enough to compare the numerators.
  have h_cancel (e : ℕ) :
      T.indexWeight ℓ a a' b * (T.P ^ (ℓ + e + (s - (ℓ + e : ℕ) - i).val) / T.q) =
        rootVector a a' b * T.P ^ (e + (s - e - (i + ℓ)).val) / T.q := by
    have hP : (T.P : ℝ) ≠ 0 := (zero_lt_one.trans T.one_lt_P).ne'
    rw [show s - (ℓ + e : ℕ) - i = s - e - (i + ℓ) by grind, indexWeight, add_assoc, pow_add]
    field_simp
  suffices h_num :
      (if (b, s) = T.rootVar a a' s then (T.P : ℝ) ^ (1 + (s - 1 - (i + ℓ)).val) else 0) -
          (if (b, s) = T.rootVar a' a s then (T.P : ℝ) ^ (s - (i + ℓ)).val else 0) =
        (if T.isEven s then 1 else -1) * (rootVector a a' b * T.P ^ (T.deepIndicator a' (b, s) +
          (s - T.deepIndicator a' (b, s) - (i + ℓ)).val)) by
    have hq : (T.q : ℝ) - 1 ≠ 0 := (sub_pos.2 T.one_lt_q).ne'
    rw [mul_assoc, h_cancel, ← mul_div_assoc, ← h_num, defectWeight]
    have hq_ne : (T.q : ℝ) ≠ 0 := (zero_lt_one.trans T.one_lt_q).ne'
    field_simp
  -- Both sides vanish outside the rows `a`, `a'`. One of the variables `(a, s)`, `(a', s)` is deep
  -- and the other is not, which gives the two exponents in `defectWeight`.
  obtain rfl | rfl | ⟨hb, hb'⟩ : b = a ∨ b = a' ∨ (b ≠ a ∧ b ≠ a') := by tauto
  all_goals by_cases h_even : T.isEven s <;>
    simp [rootVar, rootVector, deepIndicator, hlt.ne, hlt.ne', hlt.not_ge, *]

/-- A polynomial has level `t` in the Gauss filtration over the `w`-adic filtration if and only if
its coefficient at each monomial `μ` is divisible by `w ^ ⌈t - weight ω μ⌉₊`. -/
lemma _root_.New.mem_gaussFiltration_adicFiltration_iff {σ : Type*} {w : O} {ω : σ → ℝ} {t : ℝ}
    {f : MvPolynomial σ O} :
    f ∈ gaussFiltration (adicFiltration w) ω t ↔
      ∀ μ : σ →₀ ℕ, w ^ ⌈t - weight ω μ⌉₊ ∣ f.coeff μ :=
  Iff.rfl

/-- If `f` lies at level `t` of the Gauss filtration with variable weights `ω` over
`adicFiltration 0`, then every monomial `μ` with `f.coeff μ ≠ 0` has `t ≤ weight ω μ`. -/
lemma _root_.New.le_weight_of_mem_gaussFiltration_zero {σ : Type*} {ω : σ → ℝ} {t : ℝ}
    {f : MvPolynomial σ O} (hf : f ∈ gaussFiltration (adicFiltration (0 : O)) ω t) {μ : σ →₀ ℕ}
    (hμ : f.coeff μ ≠ 0) : t ≤ weight ω μ := by
  by_contra! h_lt
  exact hμ (by simpa [zero_pow (ceil_pos.2 (sub_pos.2 h_lt)).ne'] using hf μ)

/-- The variable `X v` has level `ω v` in the Gauss filtration with variable weights `ω` over the
`w`-adic filtration. -/
lemma X_mem_gaussFiltration {σ : Type*} {w : O} {ω : σ → ℝ} {v : σ} :
    (X v : MvPolynomial σ O) ∈ gaussFiltration (adicFiltration w) ω (ω v) :=
  monomial_mem_gaussFiltration (by simp [weight_single])

/-! ### Change of frame -/

section

omit [NeZero N]

/-- Conjugate `Y` by `h⁻¹` through `T.embedding (s - d)`, raise the entries to the power `P ^ d`,
and conjugate by `h` through `T.embedding s`. Modulo `p` this is the entrywise `P ^ d`-th power of
`Y`, as `T.embedding (s - d)` to the power `P ^ d` is `T.embedding s` modulo `p`. -/
lemma p_dvd_letterConj_pow_sub {Y : Matrix (Fin k) (Fin k) O} {b c : Fin k} :
    (T.p : O) ∣ T.letterConj h s ((T.letterConj h⁻¹ (s - d) Y).map (· ^ T.P ^ d)) b c -
      Y b c ^ T.P ^ d := by
  -- Modulo `p` the power `P ^ d` is a ring map `f`, and it carries `T.embedding (s - d)` to
  -- `T.embedding s`. So the two conjugations cancel.
  let Q : Type := O ⧸ Ideal.span {(T.p : O)}
  let π : O →+* Q := Ideal.Quotient.mk _
  have hp : π T.p = 0 := (eq_zero_iff_dvd _ _).2 dvd_rfl
  have h_add (x y : O) : π ((x + y) ^ T.P ^ d) = π (x ^ T.P ^ d) + π (y ^ T.P ^ d) := by
    simp only [← pow_mul, add_pow_prime_pow_eq T.prime, map_add, map_mul, hp, zero_mul, add_zero]
  let f : O →+* Q := RingHom.mk' (π.toMonoidHom.comp (powMonoidHom (T.P ^ d))) h_add
  have hf (x : O) : f x = π (x ^ T.P ^ d) := rfl
  have h_frob (x : W) : f (T.embedding (s - d) x) = π (T.embedding s x) := by
    rw [hf, eq_comm, ← sub_eq_zero, ← map_sub, eq_zero_iff_dvd]
    simpa using T.frobenius_pow_congr d (s - d) x
  let A : Matrix (Fin k) (Fin k) Q := h.val.map (π.comp (T.embedding s))
  let B : Matrix (Fin k) (Fin k) Q := h⁻¹.val.map (π.comp (T.embedding s))
  have hAB : A * B = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have h_outer (Z : Matrix (Fin k) (Fin k) O) : (T.letterConj h s Z).map π = A * Z.map π * B := by
    simp [letterConj, A, B, Matrix.map_mul]
  have h_inner : (T.letterConj h⁻¹ (s - d) Y).map f = B * Y.map f * A := by
    simp [letterConj, A, B, Matrix.map_mul, comp_def, h_frob]
  have h_pow (Z : Matrix (Fin k) (Fin k) O) : (Z.map (· ^ T.P ^ d)).map π = Z.map f :=
    Matrix.ext fun i j ↦ (hf (Z i j)).symm
  have h_cancel : (T.letterConj h s ((T.letterConj h⁻¹ (s - d) Y).map (· ^ T.P ^ d))).map π =
      (Y.map (· ^ T.P ^ d)).map π :=
    calc _ = A * (B * Y.map f * A) * B := by rw [h_outer, h_pow, h_inner]
      _ = A * B * Y.map f * (A * B) := by simp only [mul_assoc]
      _ = (Y.map (· ^ T.P ^ d)).map π := by rw [hAB, one_mul, mul_one, h_pow]
  rw [← eq_zero_iff_dvd, map_sub, sub_eq_zero]
  exact congrFun₂ h_cancel b c

/-- The matrix `T.frobGenericMatrix s d` with a change of frame by `h`: the generic matrix of the
copy `s - d` is conjugated by `h⁻¹` through `T.embedding (s - d)`, its entries are raised to the
power `P ^ d`, and the result is conjugated by `h` through `T.embedding s`. -/
def conjFrobGenericMatrix (h : GL (Fin k) W) (s : ZMod N) (d : ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (ZMod N × Fin k × Fin k) O) :=
  (T.map C).letterConj h s
    (((T.map C).letterConj h⁻¹ (s - d) (of fun b c : Fin k ↦ X (s - d, b, c))).map (· ^ T.P ^ d))

lemma conjFrobGenericMatrix_one :
    T.conjFrobGenericMatrix (1 : GL (Fin k) W) = T.frobGenericMatrix := by
  ext s d b c : 4
  simp [conjFrobGenericMatrix, letterConj]

/-- A polynomial over `O` has level `t` (lies in `gaussFiltration (adicFiltration w) ω t`) if its
coefficient at each monomial `μ` is divisible by `w ^ ⌈t - weight ω μ⌉₊`. If all entries of `Y` have
level `t`, so have those of `ι(h) Y ι(h)⁻¹`, where `h` is in `GL_k(W)` and `ι = T.embedding s` maps
`W` to `O`, seen as constant polynomials (`T.map C`). -/
lemma letterConj_mem_gaussFiltration {σ : Type} {w : O} {ω : σ → ℝ} {t : ℝ}
    {Y : Matrix (Fin k) (Fin k) (MvPolynomial σ O)}
    (hY : ∀ b c : Fin k, Y b c ∈ gaussFiltration (adicFiltration w) ω t) (b c : Fin k) :
    (T.map C).letterConj h s Y b c ∈ gaussFiltration (adicFiltration w) ω t := by
  have hC (x : O) : C x ∈ gaussFiltration (adicFiltration w) ω 0 :=
    monomial_mem_gaussFiltration (by simp)
  have h_entry : (T.map C).letterConj h s Y b c =
      ∑ j : Fin k, ∑ i : Fin k,
        C (T.embedding s (h.val b i)) * Y i j * C (T.embedding s (h⁻¹.val j c)) := by
    simp [letterConj, map, Matrix.mul_apply, Finset.sum_mul]
  rw [h_entry]
  exact sum_mem fun j _ ↦ sum_mem fun i _ ↦ by
    simpa using mul_mem_graded (mul_mem_graded (hC _) (hY i j)) (hC _)

/-- Let all variable weights `ω v` have size at most `1 / T.P ^ d`. Then the entry `(b, c)` of
`T.conjFrobGenericMatrix h s d` has the level `t = T.P ^ d • ω (s - d, b, c)` of the same entry
`X (s - d, b, c) ^ T.P ^ d` without the conjugations: its coefficient at a monomial `μ` is divisible
by `T.sqrtPrime ^ ⌈t - weight ω μ⌉₊`. -/
lemma conjFrobGenericMatrix_mem_gaussFiltration {ω : ZMod N × Fin k × Fin k → ℝ}
    (hω : ∀ v : ZMod N × Fin k × Fin k, |ω v| ≤ 1 / T.P ^ d) (b c : Fin k) :
    T.conjFrobGenericMatrix h s d b c ∈
      gaussFiltration (adicFiltration T.sqrtPrime) ω (T.P ^ d • ω (s - d, b, c)) := by
  -- Only monomials of weight at least `-1` occur. At these the wanted power of `T.sqrtPrime`
  -- divides `T.sqrtPrime ^ 2 = p`, and modulo `p` the conjugations cancel.
  let G : ℝ → AddSubgroup (MvPolynomial (ZMod N × Fin k × Fin k) O) :=
    gaussFiltration (adicFiltration 0) ω
  set M : MvPolynomial (ZMod N × Fin k × Fin k) O := T.conjFrobGenericMatrix h s d b c
  set t : ℝ := T.P ^ d • ω (s - d, b, c)
  have hX (v : ZMod N × Fin k × Fin k) : X v ∈ G (-(1 / T.P ^ d)) :=
    antitone (neg_le_of_abs_le (hω v)) X_mem_gaussFiltration
  have h_supp : M ∈ G (T.P ^ d • -(1 / T.P ^ d)) :=
    T.letterConj_mem_gaussFiltration (fun i j ↦ pow_mem_graded _
      (T.letterConj_mem_gaussFiltration (fun x y ↦ hX (s - d, x, y)) i j)) b c
  refine mem_gaussFiltration_adicFiltration_iff.2 fun μ ↦ ?_
  obtain hμ | hμ := eq_or_ne (M.coeff μ) 0
  · simp [hμ]
  have h_weight : -1 ≤ weight ω μ := by
    simpa [T.prime.ne_zero] using le_weight_of_mem_gaussFiltration_zero h_supp hμ
  have h_level : t ≤ 1 := by
    have hp : T.p ≠ 0 := T.prime.ne_zero
    simpa [t, field, mul_comm] using le_of_abs_le (hω (s - d, b, c))
  have h_le : ⌈t - weight ω μ⌉₊ ≤ 2 := ceil_le.2 (by push_cast; linarith)
  have h_mod : C (T.sqrtPrime ^ 2) ∣ M - X (s - d, b, c) ^ T.P ^ d := by
    rw [T.sqrtPrime_sq, map_natCast]
    exact (T.map C).p_dvd_letterConj_pow_sub
  have h_error : T.sqrtPrime ^ 2 ∣ M.coeff μ - (X (s - d, b, c) ^ T.P ^ d).coeff μ := by
    simpa only [AddMonoidAlgebra.coeff_sub_apply] using (C_dvd_iff_dvd_coeff _ _).1 h_mod μ
  have h_main : T.sqrtPrime ^ ⌈t - weight ω μ⌉₊ ∣ (X (s - d, b, c) ^ T.P ^ d).coeff μ :=
    mem_gaussFiltration_adicFiltration_iff.1 (pow_mem_graded _ X_mem_gaussFiltration) μ
  exact (dvd_sub_left h_main).1 ((pow_dvd_pow _ h_le).trans h_error)

end

/-- Let `ν` be a monomial in the variables `(j, b, c)`, the entries of `N` generic `k × k` matrices,
let `P = T.P`, `q = P ^ N` and `ρ = rootVector a a' = e_{a'} - e_a`. The weight
`T.entryWeight ℓ a a' i (j, b, c)` is `ρ b / P ^ ℓ` if `j = i` and else
`P ^ ((j - i) mod N) / q * (ρ b - ρ c) / P ^ ℓ`. Its sum over the variables of `ν` equals
`T.copyWeight ℓ a a' i ν`, which is defined copy by copy from the sums of `ρ` over the row indices
and over the column indices. -/
lemma weight_entryWeight (i : ZMod N) (ν : ZMod N × Fin k × Fin k →₀ ℕ) :
    weight (T.entryWeight ℓ a a' i) ν = T.copyWeight ℓ a a' i ν := by
  rw [weight_eq_sum, sum_prod_type (α₁ := ZMod N), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    copyWeight, add_div, Finset.sum_div]
  congr 1
  · simp [entryWeight, indexWeight, weight_eq_sum, Finsupp.curry_apply, Finset.sum_div,
      mul_div_assoc]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [entryWeight, scaledIndexWeight, ite_eq_right (Finset.ne_of_mem_erase hj),
      indexWeight, weight_eq_sum, Finsupp.curry_apply, Int.cast_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_div, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    exact Finset.sum_congr rfl fun v _ ↦ by ring

/-- The scaled index weight of an index at an exponent `m ≤ N` has size at most `1 / P ^ ℓ`. -/
lemma abs_scaledIndexWeight_le {m : ℕ} (hm : m ≤ N) (b : Fin k) :
    |T.scaledIndexWeight ℓ a a' m b| ≤ 1 / T.P ^ ℓ := by
  rw [scaledIndexWeight, abs_mul]
  refine (mul_le_of_le_one_right (abs_nonneg _) ?_).trans (T.abs_indexWeight_le b)
  rw [abs_of_nonneg (by positivity), div_le_one (zero_lt_one.trans T.one_lt_q), cast_pow T.P N]
  exact pow_le_pow_right₀ T.one_lt_P.le hm

/-- For every copy `i` and every entry `v` (a copy together with a row and a column index), the
weight `T.entryWeight ℓ a a' i v` has absolute value at most `2 / T.P ^ ℓ`. -/
lemma abs_entryWeight_le (i : ZMod N) (v : ZMod N × Fin k × Fin k) :
    |T.entryWeight ℓ a a' i v| ≤ 2 / T.P ^ ℓ := by
  rw [entryWeight, show (2 / T.P ^ ℓ : ℝ) = 1 / T.P ^ ℓ + 1 / T.P ^ ℓ by ring]
  split_ifs
  · exact (T.abs_indexWeight_le _).trans (le_add_of_nonneg_left (by positivity))
  · have hm : (v.1 - i).val ≤ N := (v.1 - i).val_lt.le
    grw [abs_sub, T.abs_scaledIndexWeight_le hm, T.abs_scaledIndexWeight_le hm]

/-- Let `P = T.P`. The entry `(b, c)` of
`T.frobGenericMatrix s d` is the variable `(s - d, b, c)` to the power `P ^ d`, so its weight at the
copy `i` is `P ^ d` times `T.entryWeight`. For `d ≤ N` this weight differs by at most `1 / P ^ ℓ`
from the scaled index weight of `b` at the exponent `d + 1 + (s - (d + 1) - i) mod N` less that of
`c` at the exponent `d + (s - d - i) mod N`. -/
lemma abs_scaledIndexWeight_sub_scaledIndexWeight_sub_entryWeight_le (hd : d ≤ N) (i : ZMod N)
    (b c : Fin k) :
    |T.scaledIndexWeight ℓ a a' (d + 1 + (s - (d + 1 : ℕ) - i).val) b -
        T.scaledIndexWeight ℓ a a' (d + (s - d - i).val) c -
      T.P ^ d * T.entryWeight ℓ a a' i (s - d, b, c)| ≤ 1 / T.P ^ ℓ := by
  have h_shift (m : ℕ) (b : Fin k) :
      T.scaledIndexWeight ℓ a a' (d + m) b = T.P ^ d * T.scaledIndexWeight ℓ a a' m b := by
    unfold scaledIndexWeight
    ring
  have h_succ : d + 1 + (s - (d + 1 : ℕ) - i).val =
      d + if s - d = i then N else (s - d - i).val := by
    rw [add_assoc, cast_succ, ← sub_sub, one_add_val_sub_one_sub]
  rw [h_succ, entryWeight]
  split_ifs with h_copy
  · -- Only the scaled index weight of `c` is left.
    have h_full : T.scaledIndexWeight ℓ a a' N b = T.indexWeight ℓ a a' b := by
      rw [scaledIndexWeight, ← cast_pow T.P N, div_self (zero_lt_one.trans T.one_lt_q).ne', mul_one]
    simpa [h_copy, h_shift, h_full] using T.abs_scaledIndexWeight_le hd c
  · -- The difference of the scaled index weights is exactly the weight of the entry.
    simp [h_shift, mul_sub]

end

variable {r ℓ n : ℕ} {a a' : Fin k}

/-- Let `T` be a Frobenius cycle, with letters `s : ZMod N`, prime power `P = T.P`, `q = P ^ N` and
`w = T.sqrtPrime`, `w ^ 2 = p`. Let `a' = a + 1`, `ℓ ≤ N`, `|ε| ≤ 1 / 2` and `ρ = e_{a'} - e_a`.
Take a generic matrix `X_j` for each `j : ZMod N`, and give its entry `(b, c)` the weight `ε` times
`T.entryWeight ℓ a a' i (j, b, c)`, which is `ρ b / P ^ ℓ` if `j = i` and else
`P ^ ((j - i) mod N) / q * (ρ b - ρ c) / P ^ ℓ`. The matrix `T.substitutionOperator` is the
Kronecker product over `s` of `n`-th symmetric powers of products (transposed adjugates of products
for odd `s`) of the entrywise powers `P ^ d`, `d ≤ ℓ` in deep rows and `d < ℓ` in the others, of the
`X_{s - d}`, taken between conjugations by `h⁻¹` and `h`; its rows `β` are monomials of degree `n`
in the variables `(b, s)` of each letter `s`. The defect of `β` at `i + ℓ` is the sum over its
variables of `T.defectWeight`, which is `± P ^ ((s - i - ℓ) mod N) / (q - 1)` for `b = a, a'` (`+`
at `a'` for even and at `a` for odd `s`, plus `1` there if `s = i + ℓ`) and else `0`. Then the
entries of row `β` have level `t = ε (1 - 1 / q) defect - N n k (ℓ + 2) / (2 P ^ ℓ)`: the
coefficient of a monomial `ν` is divisible by `w ^ ⌈t - weight of ν⌉₊`. -/
lemma substitutionOperator_conj_mem_gaussFiltration (ha : (a : ℕ) + 1 = (a' : ℕ)) (i : ZMod N)
    (hℓ_le : ℓ ≤ N) (h : GL (Fin k) W) {ε : ℝ} (hε : |ε| ≤ 2⁻¹) (β γ : Exponents N k n) :
    T.substitutionOperator a' ℓ n (T.conjFrobGenericMatrix h) β γ ∈
      gaussFiltration (adicFiltration T.sqrtPrime) (ε • T.entryWeight ℓ a a' i)
        (weight ((ε * (1 - 1 / T.q)) • T.defectWeight (i + ℓ) a a') (exponentOf β) -
          N * n * k * (ℓ + 2) / (2 * T.P ^ ℓ)) := by
  set ω : ZMod N × Fin k × Fin k → ℝ := ε • T.entryWeight ℓ a a' i
  set u : ℝ := 2⁻¹ * (1 / T.P ^ ℓ)
  have h_scale {y z : ℝ} (hy : |y| ≤ z) : |ε * y| ≤ 2⁻¹ * z :=
    (abs_mul ε y).trans_le (mul_le_mul hε hy (abs_nonneg y) (by norm_num))
  have h_small {d : ℕ} (hd : d ≤ ℓ) (v : ZMod N × Fin k × Fin k) : |ω v| ≤ 1 / T.P ^ d :=
    calc |ω v| ≤ 2⁻¹ * (2 / T.P ^ ℓ) := h_scale (T.abs_entryWeight_le i v)
      _ = 1 / T.P ^ ℓ := by ring
      _ ≤ 1 / T.P ^ d := one_div_pow_le_one_div_pow_of_le T.one_lt_P.le hd
  -- The potential of the factor `d` at the letter `s` has the exponent `d + m`, where
  -- `s - d = i + m` and `m < N`.
  let α (s : ZMod N) (d : ℕ) (b : Fin k) : ℝ :=
    ε * T.scaledIndexWeight ℓ a a' (d + (s - d - i).val) b
  have hα_zero (s : ZMod N) (b : Fin k) : |α s 0 b| ≤ u :=
    h_scale (T.abs_scaledIndexWeight_le (by simpa using (ZMod.val_lt _).le) b)
  have hα_sum (s : ZMod N) (d : ℕ) : ∑ b : Fin k, α s d b = 0 := by
    simp [α, scaledIndexWeight, indexWeight, rootVector, ← Finset.mul_sum, ← Finset.sum_mul,
      ← Finset.sum_div]
  have h_last (b : Fin k) (s : ZMod N) :
      ((ε * (1 - 1 / T.q)) • T.defectWeight (i + ℓ) a a') (b, s) =
        (if T.isEven s then 1 else -1) * α s (ℓ + T.deepIndicator a' (b, s)) b := by
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc, T.mul_defectWeight_eq_indexWeight_mul ha i]
    simp only [α, scaledIndexWeight]
    ring
  have h_step (s : ZMod N) (d : ℕ) (hd : d ≤ ℓ) (b c : Fin k) :
      α s (d + 1) b - α s d c - u ≤ T.P ^ d • ω (s - d, b, c) := by
    have h_close : |α s (d + 1) b - α s d c - T.P ^ d • ω (s - d, b, c)| ≤ u := by
      simpa only [α, ω, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, cast_pow T.P d, mul_sub,
        mul_left_comm ε] using
        h_scale (T.abs_scaledIndexWeight_sub_scaledIndexWeight_sub_entryWeight_le
          (hd.trans hℓ_le) i b c)
    linarith [le_of_abs_le h_close]
  have h_factor (s : ZMod N) (d : ℕ) (hd : d ≤ ℓ) (b c : Fin k) :
      T.conjFrobGenericMatrix h s d b c ∈
        gaussFiltration (adicFiltration T.sqrtPrime) ω (α s (d + 1) b - α s d c - u) :=
    antitone (h_step s d hd b c) (T.conjFrobGenericMatrix_mem_gaussFiltration (h_small hd) b c)
  rw [show (N * n * k * (ℓ + 2) / (2 * T.P ^ ℓ) : ℝ) = N * n * k * (ℓ + 2) * u by ring]
  exact T.substitutionOperator_mem _ α _ u hα_zero hα_sum h_last h_factor (by positivity)

/-- If `2 n ≤ T.q`, the defect `Δ` at the letter `i` along the root `(a, a')` of a monomial `β` of
degree `n` in each letter (the sum of `T.defectWeight i a a'` over `exponentOf β`) satisfies
`|Δ - (1 - 1 / T.q) Δ| ≤ 1`. -/
lemma abs_defect_sub_mul_le_one (i : ZMod N) (β : Exponents N k n) (hn : 2 * n ≤ T.q) :
    |weight (T.defectWeight i a a') (exponentOf β) -
      (1 - 1 / T.q) * weight (T.defectWeight i a a') (exponentOf β)| ≤ 1 := by
  set Δ : ℝ := weight (T.defectWeight i a a') (exponentOf β)
  have hq : (0 : ℝ) < T.q := zero_lt_one.trans T.one_lt_q
  have h_size : |Δ| ≤ 2 * n := T.abs_weight_defectWeight_le fun s ↦ by
    simpa [exponentOf, degree_eq_sum, ← cast_sum] using (β s).degree_eq.le
  rw [show Δ - (1 - 1 / T.q) * Δ = Δ / T.q by ring, abs_div, abs_of_pos hq, div_le_one hq]
  exact h_size.trans (by exact_mod_cast hn)

/-- Weight and defect. Let `T` be a Frobenius cycle, with letters `s : ZMod N` (even or odd), ring
maps `W → O`, prime `p`, the power `P = T.P` of `p`, `q = P ^ N` and `w = T.sqrtPrime` in `O` with
`w ^ 2 = p`. Let `a' = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ`, `ℓ ≤ N` and `h` in `GL_k(W)`. Take a generic
matrix `X_j` for each `j : ZMod N` (a copy). The matrix `T.substitutionOperator a' ℓ n` is the
Kronecker product over `s` of `n`-th symmetric powers of products (transposed adjugates of products
for odd `s`) of the entrywise powers `P ^ d` of the `X_{s - d}`, taken between conjugations by `h⁻¹`
and `h` (`T.conjFrobGenericMatrix h`); here `d ≤ ℓ` in the rows `b ≥ a'` for even and `b < a'` for
odd `s`, and `d < ℓ` in the others. Its rows `β` are monomials of degree `n` in the variables
`(b, s)` of each letter `s`.

* The defect of `β` at `i + ℓ` is the sum over its variables of `T.defectWeight`, which is
  `± P ^ ((s - i - ℓ) mod N) / (q - 1)` for `b = a, a'` (`+` at `a'` for even and at `a` for odd
  `s`, plus `1` there if `s = i + ℓ`) and else `0`.
* The weight `T.copyWeight` at the copy `i` of a monomial `ν` in the entries of the `X_j` is the sum
  over its variables `(j, b, c)` of `ρ b / P ^ ℓ` if `j = i` and else of
  `P ^ ((j - i) mod N) / q * (ρ b - ρ c) / P ^ ℓ`, where `ρ = e_{a'} - e_a`.

If the coefficient of `ν` in the entry `(β, γ)` is not divisible by `w ^ c`, then the weight of `ν`
is within `defectThreshold k c = 3 k c` of the defect of `β`. -/
lemma abs_defect_sub_copyWeight_le (ha : (a : ℕ) + 1 = (a' : ℕ)) (i : ZMod N)
    (hn_le : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ_le : ℓ ≤ N) (h : GL (Fin k) W) {c : ℕ}
    {β γ : Exponents N k n} {ν : ZMod N × Fin k × Fin k →₀ ℕ}
    (h_coeff : ¬T.sqrtPrime ^ c ∣
      (T.substitutionOperator a' ℓ n (T.conjFrobGenericMatrix h) β γ).coeff ν) :
    |weight (T.defectWeight (i + ℓ) a a') (exponentOf β) - T.copyWeight ℓ a a' i ν| ≤
      defectThreshold k c := by
  -- Let `D` be the weight of `ν` and `E` be `1 - 1 / q` times the defect `Δ`. For `ε = ± 1 / 2`
  -- the coefficient is divisible by `w ^ ⌈ε (E - D) - L⌉₊`, where `L ≤ 1 / 2`. This
  -- exponent is at most `c`, so `|E - D| ≤ 2 c + 1`. Also `|Δ - E| ≤ 1`, and `2 c + 2 ≤ 3 k c`
  -- because `k ≥ 2` and `c ≥ 1`.
  set Δ : ℝ := weight (T.defectWeight (i + ℓ) a a') (exponentOf β) with hΔ
  let E : ℝ := (1 - 1 / T.q) * Δ
  set D : ℝ := T.copyWeight ℓ a a' i ν with hD
  let L : ℝ := N * n * k * (ℓ + 2) / (2 * T.P ^ ℓ)
  have h_loss : L ≤ 2⁻¹ := by
    have h_cast : (N * n * k * (ℓ + 2) : ℝ) ≤ T.P ^ ℓ := by exact_mod_cast hn_le
    rw [div_le_iff₀ (mul_pos two_pos (pow_pos (zero_lt_one.trans T.one_lt_P) ℓ))]
    linarith
  have hn_le_q : 2 * n ≤ T.q :=
    calc 2 * n = 1 * n * 1 * 2 := by ring
      _ ≤ N * n * k * (ℓ + 2) := by
        gcongr
        exacts [NeZero.pos N, a.pos, Nat.le_add_left 2 ℓ]
      _ ≤ T.q := hn_le.trans (Nat.pow_le_pow_right (pow_pos T.prime.pos T.frobExp) hℓ_le)
  have h_bound {ε : ℝ} (hε : |ε| ≤ 2⁻¹) : ε * (E - D) ≤ c + 2⁻¹ := by
    have h_defect :
        weight ((ε * (1 - 1 / T.q)) • T.defectWeight (i + ℓ) a a') (exponentOf β) = ε * E := by
      simp [E, hΔ, weight_eq_sum, Finset.mul_sum, mul_left_comm, mul_assoc]
    have h_weight : weight (ε • T.entryWeight ℓ a a' i) ν = ε * D := by
      simp [hD, ← T.weight_entryWeight, weight_eq_sum, Finset.mul_sum, mul_left_comm]
    have h_dvd : T.sqrtPrime ^ ⌈ε * E - L - ε * D⌉₊ ∣
        (T.substitutionOperator a' ℓ n (T.conjFrobGenericMatrix h) β γ).coeff ν := by
      rw [← h_defect, ← h_weight]
      exact mem_gaussFiltration_adicFiltration_iff.1
        (T.substitutionOperator_conj_mem_gaussFiltration ha i hℓ_le h hε β γ) ν
    by_contra! h_large
    exact h_coeff ((pow_dvd_pow _ (lt_ceil.2 (by linarith)).le).trans h_dvd)
  have h_pos : 2⁻¹ * (E - D) ≤ c + 2⁻¹ := h_bound (by norm_num)
  have h_neg : -2⁻¹ * (E - D) ≤ c + 2⁻¹ := h_bound (by norm_num)
  obtain ⟨h_rest_lower, h_rest_upper⟩ : -1 ≤ Δ - E ∧ Δ - E ≤ 1 :=
    abs_le.1 (T.abs_defect_sub_mul_le_one (i + ℓ) β hn_le_q)
  have h_threshold : (2 * c + 2 : ℝ) ≤ defectThreshold k c := by
    have hc : 1 ≤ c := Nat.pos_of_ne_zero fun h_zero ↦ h_coeff (by simp [h_zero])
    exact_mod_cast (by nlinarith [show 2 ≤ k by lia] : 2 * c + 2 ≤ 3 * k * c)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ### Degrees -/

/-- Let `T` be a Frobenius cycle with letters `s : ZMod N` and prime power `P = T.P`. Take a generic
matrix with entries `X (j, b, c)` for each `j : ZMod N` (a copy); `T.frobGenericMatrix s d` is the
entrywise power `P ^ d` of the copy `s - d`. The matrix `T.substitutionOperator r ℓ n` is the
Kronecker product over `s` of `n`-th symmetric powers of products (transposed adjugates of products
for odd `s`) of these for `d < ℓ + 1` or `d < ℓ`, as the side of `r` on which the row lies and the
parity of `s` decide. Its rows and columns `β`, `γ` are families of exponent vectors of degree `n`,
one for each letter. A monomial `ν` that occurs in an entry has degree at most
`N n k (ℓ + 2) P ^ ℓ` in the variables of each copy `j`. -/
lemma degree_le_of_coeff_substitutionOperator {β γ : Exponents N k n}
    {ν : ZMod N × Fin k × Fin k →₀ ℕ}
    (hν : (T.substitutionOperator r ℓ n T.frobGenericMatrix β γ).coeff ν ≠ 0) (j : ZMod N) :
    degree (ν.curry j) ≤ N * n * k * (ℓ + 2) * T.P ^ ℓ := by
  -- Give the variables of the copy `j` weight `-1`. Level `-t` of the Gauss filtration over
  -- `adicFiltration 0` consists of the polynomials of degree at most `t` in the copy `j`.
  let ω (v : ZMod N × Fin k × Fin k) : ℝ := if v.1 = j then -1 else 0
  have h_mem := T.substitutionOperator_mem (gaussFiltration (adicFiltration (0 : O)) ω)
    (α := 0) (x := 0) (u := T.P ^ ℓ) (β := β) (γ := γ) (r := r) (ℓ := ℓ) (n := n)
    (ψ := T.frobGenericMatrix) (hα_zero := by simp) (hα_sum := by simp) (hx := by simp)
    (hu := by positivity) (hψ := fun s d hd b c => by
      refine antitone (le_trans ?_ (nsmul_le_nsmul_right (a := (-1 : ℝ)) (by grind) _))
        (pow_mem_graded _ X_mem_gaussFiltration)
      simpa using pow_le_pow_right₀ T.one_lt_P.le hd)
  rify
  simpa [ω, degree_eq_sum, sum_prod_type_right, weight_eq_sum] using
    le_weight_of_mem_gaussFiltration_zero h_mem hν

end New.FrobeniusCycle

end
end
end

section
/-!
# Edges, halfway lattices and duality

An edge is a pair of lattices `L' ⊆ L` with `p L ⊆ L'` and `L / L'` of dimension `r` over the
residue field; `L'` is its origin. Let `w ^ 2 = p`, and consider forms of degree `n` in each of `N`
letters, with `k` variables in each letter. In a basis of `L'` adapted to the edge, the forms that
are integral for the lattice `L' + w L`, times `w ^ (-n N / 2)`, have as basis the normalized
monomials `w ^ (-depth β) z ^ β`, where the depth is the degree in the deep variables
(`New.FrobeniusCycle.deepIndicator`). This module of forms is the halfway lattice of the edge. The
file works with coefficient vectors in the normalized monomials, so the halfway lattice is the
module of all vectors.

* `New.FrobeniusCycle.allEdgesForms`: the forms that lie in the halfway lattices of all edges from
  `L'`.
* `New.FrobeniusCycle.IsEdgePairing`: weights of a pairing for which `ρ(g)` and `ρ(gᵀ)` are adjoint;
  it pairs the halfway lattices of an edge and its dual.
* `New.FrobeniusCycle.edgeRestriction`, `New.FrobeniusCycle.originFunctions`: functions on origins
  as functions on edges, and the functions on edges that depend only on the origin.
* `New.FrobeniusCycle.exists_originFunctions_factorization_det_dvd`,
  `New.FrobeniusCycle.mulVec_mulVec_eq_self_of_mem_originFunctions`: if every edge occurs, these
  functions form a direct summand, in which the integral functions on origins have small colength.
* `New.FrobeniusCycle.pow_dvd_letterRep_mulVec_of_mem_allEdgesForms`,
  `New.FrobeniusCycle.IsEdgePairing.pow_dvd_pairing_letterRep`: vectors in `allEdgesForms` have
  coefficients divisible by a power of `w` at monomials of large defect, and pair with these
  monomials to multiples of a power of `w`.

Notions from other files:
* `New.FrobeniusCycle`: a prime `p`, ring maps from `W` to `O` indexed by the letters `s ∈ ℤ/N`,
  which are alternately even and odd, and an element `w` of `O` with `w ^ 2 = p`.
* `New.FrobeniusCycle.letterRep`: the matrix `ρ(g)` of `g ∈ GL_k(W)` on coefficient vectors. It
  substitutes the image of `g` in even letters and of its inverse transpose in odd letters;
  `ρ(g) h` is the translate of `h` by `g`.
* `New.twoBlock`: the blocks of sizes `r` and `k - r`; `New.parahoric`, `New.levi`: the stabilizer
  of the edge and the block diagonal subgroup.
* `New.FrobeniusCycle.translatesIn`: vectors whose translates by a Levi subgroup have coefficients
  in an ideal at a set of monomials. Two cases are `New.FrobeniusCycle.deepForms` (no translate has
  a monomial of depth below a bound) and `New.FrobeniusCycle.defectConditions`.
* `New.FrobeniusCycle.defectWeight`: real weights on the two variables of a root in each letter; the
  defect of a monomial is its weighted degree, and `defectConditions` is the condition on block
  diagonal translates at the monomials of large defect.

## Relation to the literature

See `New.UpperBound.Divisibility.LocalDivisibility` for related work.
-/

@[expose] public section

noncomputable section

namespace New

open MvPolynomial Matrix IsLocalRing Function Module Finset Fintype Ideal

/-- The left cosets of the parahoric subgroup with blocks of sizes `r` and `k - r`. For `r ≤ k` they
index the edges into the lattice `W ^ k`, that is, the sublattices that contain `𝔪 W ^ k`, for the
maximal ideal `𝔪` of `W`, and have a quotient of dimension `r` over the residue field: the
parahoric subgroup is the stabilizer of one of them. As matrices act transposed, the same cosets
index the edges from a lattice, which is how they are used here. -/
abbrev ParahoricCosets (W : Type) [CommRing W] [IsLocalRing W] (k r : ℕ) : Type :=
  GL (Fin k) W ⧸ parahoric W (twoBlock k r)

/-! ### Linear algebra and divisibility -/

/-- Elementary divisors of a matrix `J` over a valuation domain with at least as many rows as
columns, as witnessed by an embedding `ι` of the column indices in the row indices: there are an
invertible `P` and a matrix `Q` with a left inverse `R` such that column `i` of `J * P⁻¹` is `t i`
times column `i` of `Q`. -/
lemma exists_mul_inv_eq_mul_diagonal {O I I' : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (ι : I ↪ I') (J : Matrix I' I O) :
    ∃ (Q : Matrix I' I O) (R : Matrix I I' O) (P : GL I O) (t : I → O),
      R * Q = 1 ∧ J * P⁻¹.val = Q * diagonal t := by
  -- A Hermite form reduces `J` to a square matrix `D`, which has a Smith form.
  obtain ⟨U, -, D, -, hJ : J = U.val.submatrix id ι * D, -⟩ := isValuationPair_top.hermite ι J
  obtain ⟨K, -, P, -, t, rfl : D = K.val * diagonal t * P.val⟩ :=
    isValuationPair_top.smith_normal_form D
  have hU : U⁻¹.val.submatrix ι id * U.val.submatrix id ι = 1 := by
    rw [← submatrix_mul U⁻¹.val U.val ι id ι bijective_id, U.inv_mul, submatrix_one_embedding]
  refine ⟨U.val.submatrix id ι * K.val, K⁻¹.val * U⁻¹.val.submatrix ι id, P, t, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ K.val, hU, Matrix.one_mul, K.inv_mul]
  · simp only [hJ, Matrix.mul_assoc, P.mul_inv, Matrix.mul_one]

/-- Vectors with dual rows are independent modulo the maximal ideal. Let the columns `j ∈ s` of `Q`
have dual rows in `R`, that is, column `j` of `R * Q` is the `j`-th unit vector. Suppose that for
each `x ∈ X` the block `i ↦ Q (x, i) j` of such a column reduces into the subspace `S` over the
residue field. Then `s` has at most `|X| dim S` elements. -/
lemma card_le_mul_finrank_of_dual_rows {O X I E : Type*} [CommRing O] [IsLocalRing O] [Fintype X]
    [Fintype I] [DecidableEq E] (Q : Matrix (X × I) E O) (R : Matrix E (X × I) O) {s : Finset E}
    {S : Submodule (ResidueField O) (I → ResidueField O)}
    (h_dual : ∀ j ∈ s, ∀ i : E, (R * Q) i j = if i = j then 1 else 0)
    (h_mem : ∀ j ∈ s, ∀ x : X, (fun i : I ↦ residue O (Q (x, i) j)) ∈ S) :
    #s ≤ Fintype.card X * finrank (ResidueField O) S := by
  let v (j : s) (x : X) : S := ⟨fun i ↦ residue O (Q (x, i) j), h_mem j (coe_mem j) x⟩
  have h_indep : LinearIndependent (ResidueField O) v := by
    refine Fintype.linearIndependent_iff.2 fun c hc i ↦ ?_
    have h_entry (y : X × I) : ∑ j : s, c j * residue O (Q y j) = 0 := by
      simpa [v] using congrArg (fun f : X → S ↦ S.subtype (f y.1) y.2) hc
    -- Pair the relation with row `i` of `R`: only the coefficient `c i` survives.
    calc c i = ∑ j : s, c j * residue O ((R * Q) i j) := by
          simp [h_dual]
      _ = ∑ y : X × I, residue O (R i y) * ∑ j : s, c j * residue O (Q y j) := by
          simp only [Matrix.mul_apply, map_sum, mul_sum, mul_left_comm]
          exact sum_comm
      _ = 0 := by simp only [h_entry, mul_zero, sum_const_zero]
  simpa [finrank_pi_fintype] using h_indep.fintype_card_le_finrank

/-- If every `t i` divides `w ^ x`, then their product divides `w ^ l`, where `l` counts the pairs
`(i, δ)` with `δ < x` such that `t i` does not divide `w ^ δ`. -/
lemma prod_dvd_pow_sum_card {O I : Type*} [CommRing O] [DecidableRel fun y z : O ↦ y ∣ z]
    [Fintype I] {t : I → O} {w : O} {x : ℕ} (ht : ∀ i : I, t i ∣ w ^ x) :
    ∏ i : I, t i ∣ w ^ ∑ δ ∈ range x, #{i : I | ¬t i ∣ w ^ δ} := by
  -- The least `l` with `t i ∣ w ^ l` is at most the number of `δ < x` with `¬t i ∣ w ^ δ`.
  have h_one (i : I) : t i ∣ w ^ #{δ ∈ range x | ¬t i ∣ w ^ δ} := by
    have h_ex : ∃ l : ℕ, t i ∣ w ^ l := ⟨x, ht i⟩
    have h_range : range (Nat.find h_ex) ⊆ {δ ∈ range x | ¬t i ∣ w ^ δ} := by
      simp only [subset_iff, mem_filter, Finset.mem_range]
      exact fun δ hδ ↦ ⟨hδ.trans_le (Nat.find_min' h_ex (ht i)), Nat.find_min h_ex hδ⟩
    refine (Nat.find_spec h_ex).trans (pow_dvd_pow w ?_)
    simpa only [Finset.card_range] using card_le_card h_range
  have h_count : ∑ i : I, #{δ ∈ range x | ¬t i ∣ w ^ δ} =
      ∑ δ ∈ range x, #{i : I | ¬t i ∣ w ^ δ} := by simp only [card_filter, sum_comm (s := range x)]
  rw [← h_count, ← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun i _ ↦ h_one i

/-- Cancelling a power of `w ≠ 0` in a divisibility: if `w ^ m` divides `w ^ d * x`, then
`w ^ (m - d)` divides `x`, with truncated subtraction. -/
lemma pow_sub_dvd_of_pow_dvd_pow_mul {O : Type} [CommRing O] [IsDomain O] {w x : O} (hw : w ≠ 0)
    {m d : ℕ} (h_dvd : w ^ m ∣ w ^ d * x) : w ^ (m - d) ∣ x := by
  obtain hmd | hdm := le_total m d
  · simp [Nat.sub_eq_zero_of_le hmd]
  · rwa [← Nat.add_sub_cancel' hdm, pow_add, mul_dvd_mul_iff_left (pow_ne_zero d hw)] at h_dvd

namespace FrobeniusCycle

section Edges
variable {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
  (T : FrobeniusCycle N W O)

/-- A coefficient vector `v` lies in `T.translatesIn n τ I B` if and only if its translates by the
Levi subgroup of the labelling `τ` have their coefficients at the exponents in `B` in `I`. -/
lemma mem_translatesIn_iff {τ : Fin k → ℕ} {I : Ideal O} {B : Set (Exponents N k n)}
    {v : Exponents N k n → O} :
    v ∈ T.translatesIn n τ I B ↔ ∀ g ∈ levi W τ, ∀ β ∈ B, (T.letterRep n g *ᵥ v) β ∈ I :=
  Iff.rfl

/-- Let `v` be a coefficient vector whose translates `T.letterRep n g *ᵥ v`, for `g` in the Levi
subgroup of the labelling `τ`, have their coefficients at the exponents in `B` in the maximal ideal
of `O`. Then the translates of the reduction of `v`, for the Frobenius cycle pushed to the residue
field, have their coefficients at `B` in the zero ideal. -/
lemma residue_mem_translatesIn [IsLocalRing O] {τ : Fin k → ℕ} {B : Set (Exponents N k n)}
    {v : Exponents N k n → O} (hv : v ∈ T.translatesIn n τ (maximalIdeal O) B) :
    (fun β : Exponents N k n ↦ residue O (v β)) ∈
      (T.map (residue O)).translatesIn n τ (⊥ : Ideal (ResidueField O)) B := by
  rw [mem_translatesIn_iff] at hv ⊢
  intro g hg β hβ
  have h_residue : ((T.map (residue O)).letterRep n g *ᵥ fun α ↦ residue O (v α)) β =
      residue O ((T.letterRep n g *ᵥ v) β) := by simp [letterRep_map, mulVec, dotProduct]
  simpa only [h_residue, Submodule.mem_bot, residue_eq_zero_iff] using hv g hg β hβ

/-! ### One edge -/

/-- The matrix that takes coefficients in the monomials `z ^ β` to coefficients in the normalized
monomials `w ^ (-depth β) z ^ β`, which form a basis of the halfway lattice of the edge. It is
diagonal with entries `w ^ depth β`, where `depth β` is the degree of `z ^ β` in the deep
variables. The variable `b` of the letter `s`, with `b` counted from `0`, is deep if `s` is even
and `r ≤ b`, or `s` is odd and `b < r`. -/
def depthScaling (k n r : ℕ) : Matrix (Exponents N k n) (Exponents N k n) O :=
  diagonal fun β : Exponents N k n ↦ T.sqrtPrime ^ T.depth k n r β

/-- The normalized coefficient at `β`, namely the `β` entry of `T.depthScaling k n r *ᵥ h`, is
`T.sqrtPrime ^ T.depth k n r β` times the coefficient `h β`. -/
lemma depthScaling_mulVec_apply (r : ℕ) (h : Exponents N k n → O) (β : Exponents N k n) :
    (T.depthScaling k n r *ᵥ h) β = T.sqrtPrime ^ T.depth k n r β * h β := mulVec_diagonal _ h β

/-- The matrix `T.depthScaling k n r` scales the deep variables of each letter by `T.sqrtPrime`.
These are the variables where `T.deepIndicator r` is `1`. It is the Kronecker product over the
letters `s` of the `n`-th symmetric powers of the diagonal matrices with entry `T.sqrtPrime` at the
deep variables and `1` at the others. -/
lemma depthScaling_eq_kroneckerPi (r : ℕ) :
    T.depthScaling k n r = kroneckerPi fun s : ZMod N ↦
      symPowMatrix n (diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s)) :=
  T.diagonal_pow_depth T.sqrtPrime

/-- The stabilizer of the edge preserves its halfway lattice, spanned by the monomials
`w ^ (-depth β) z ^ β`. The diagonal matrix `Δ = T.depthScaling k n r` has entries `w ^ depth β`. If
`u` lies in the parahoric subgroup for the blocks of sizes `r` and `k - r`, which stabilizes the
edge, then `Δ ρ(u) = A Δ` for a matrix `A` over `O`. -/
lemma exists_depthScaling_mul_letterRep_eq {r : ℕ} {u : GL (Fin k) W}
    (hu : u ∈ parahoric W (twoBlock k r)) :
    ∃ A : Matrix (Exponents N k n) (Exponents N k n) O,
      T.depthScaling k n r * T.letterRep n u = A * T.depthScaling k n r := by
  -- The entries in a shallow row and a deep column are divisible by `p = w ^ 2`.
  have h_dvd (s : ZMod N) (i j : Fin k) : T.sqrtPrime ^ T.deepIndicator r (j, s) ∣
      T.sqrtPrime ^ T.deepIndicator r (i, s) * T.letterMatrix s u i j := by
    obtain hij | hij := le_or_gt (T.deepIndicator r (j, s)) (T.deepIndicator r (i, s))
    · exact (pow_dvd_pow T.sqrtPrime hij).mul_right _
    · -- The deep block is the second one for `s` even and the first one for `s` odd.
      have h_even (hs : T.isEven s = true) : twoBlock k r i < twoBlock k r j := by
        grind [deepIndicator, twoBlock]
      have h_odd (hs : T.isEven s = false) : twoBlock k r j < twoBlock k r i := by
        grind [deepIndicator, twoBlock]
      have hp : T.sqrtPrime ^ 2 ∣ T.letterMatrix s u i j := by
        rw [T.sqrtPrime_sq]
        exact T.p_dvd_letterMatrix_of_mem_parahoric s hu i j h_even h_odd
      exact ((pow_dvd_pow T.sqrtPrime (by grind [deepIndicator])).trans hp).mul_left _
  -- The quotients form the integral matrix `A s` of the letter `s`.
  choose A hA using fun s i j ↦ exists_eq_mul_left_of_dvd (h_dvd s i j)
  have h_letter (s : ZMod N) :
      (diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s)) * T.letterMatrix s u =
        of (A s) * diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s) :=
    Matrix.ext fun i j ↦ by rw [diagonal_mul, mul_diagonal, hA, of_apply]
  refine ⟨kroneckerPi fun s : ZMod N ↦ symPowMatrix n (of (A s)), ?_⟩
  simp only [depthScaling_eq_kroneckerPi, letterRep_apply, ← kroneckerPi_mul, ← map_mul, h_letter]

omit [NeZero N] in
/-- If `g` lies in the Levi subgroup of the labelling `τ`, then the matrix of `g` on the letter `s`,
the image of `g` or of its inverse transpose, vanishes at `(i, j)` when `τ i ≠ τ j`. -/
lemma letterMatrix_eq_zero_of_mem_levi {τ : Fin k → ℕ} {g : GL (Fin k) W} (hg : g ∈ levi W τ)
    (s : ZMod N) {i j : Fin k} (hij : τ i ≠ τ j) : T.letterMatrix s g i j = 0 := by
  have h_inv : g⁻¹ j i = 0 := inv_mem hg j i hij.symm
  rw [letterMatrix_apply, Matrix.map_apply]
  split_ifs <;> simp only [transpose_apply, hg i j hij, h_inv, map_zero]

/-- The block diagonal subgroup preserves depth. Here `T` is a Frobenius cycle, with letters
`s ∈ ℤ/N`, alternately even and odd, and `w = T.sqrtPrime` a square root of its prime. The matrix
`T.letterRep n g` acts on the coefficient vectors of forms of degree `n` in each letter, in `k`
variables, by the image of `g` in even letters and of its inverse transpose in odd letters. Let
`g ∈ GL_k(W)` be block diagonal with blocks of sizes `r` and `k - r` (`levi W (twoBlock k r)`).
Then this matrix commutes with the diagonal matrix `T.depthScaling k n r`, whose entry at the
exponent `β` is `w ^ depth β`, where `depth β` is the degree in the variables of index `b ≥ r` in
even letters and `b < r` in odd letters. -/
lemma commute_depthScaling_letterRep {r : ℕ} {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r)) :
    Commute (T.depthScaling k n r) (T.letterRep n g) := by
  have h_letter (s : ZMod N) :
      (diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s)) * T.letterMatrix s g =
        T.letterMatrix s g * diagonal fun b : Fin k ↦ T.sqrtPrime ^ T.deepIndicator r (b, s) := by
    ext i j
    rw [diagonal_mul, mul_diagonal, mul_comm]
    by_cases hij : twoBlock k r i = twoBlock k r j
    · have h_depth : T.deepIndicator r (i, s) = T.deepIndicator r (j, s) := by
        grind [deepIndicator, twoBlock]
      rw [h_depth]
    · simp [T.letterMatrix_eq_zero_of_mem_levi hg s hij]
  simp only [commute_iff_eq, depthScaling_eq_kroneckerPi, letterRep_apply, ← kroneckerPi_mul,
    ← map_mul, h_letter]

/-- The forms that lie in the halfway lattices of all edges from the origin, in the normalized
coefficients `v` of one edge. The form is `w ^ (-m) h` for an integral form `h`; every edge from
the origin has an adapted basis in which it becomes a translate by some `g ∈ GL_k(W)`, and the
normalized coefficients of all these translates are integral. -/
def allEdgesForms (k n r : ℕ) : Submodule O (Exponents N k n → O) where
  carrier := {v : Exponents N k n → O | ∃ (m : ℕ) (h : Exponents N k n → O),
    T.sqrtPrime ^ m • v = T.depthScaling k n r *ᵥ h ∧
    ∀ (g : GL (Fin k) W) (β : Exponents N k n),
      T.sqrtPrime ^ m ∣ (T.depthScaling k n r *ᵥ T.letterRep n g *ᵥ h) β}
  add_mem' := by
    rintro v v' ⟨m, h, hv, h_dvd⟩ ⟨m', h', hv', h_dvd'⟩
    refine ⟨m + m', T.sqrtPrime ^ m' • h + T.sqrtPrime ^ m • h', ?_, fun g β ↦ ?_⟩
    · simp only [mulVec_add, mulVec_smul, ← hv, ← hv', pow_add]
      module
    · simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_add]
      exact dvd_add (by simpa [mul_comm] using mul_dvd_mul_left (T.sqrtPrime ^ m') (h_dvd g β))
        (mul_dvd_mul_left _ (h_dvd' g β))
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  smul_mem' := by
    rintro c v ⟨m, h, hv, h_dvd⟩
    refine ⟨m, c • h, ?_, fun g β ↦ ?_⟩
    · rw [mulVec_smul, ← hv, smul_comm]
    · simpa only [mulVec_smul, Pi.smul_apply, smul_eq_mul] using (h_dvd g β).mul_left c

/-! ### Duality -/

/-- The number `c₀ = k² log_p q`, where `q = p ^ (T.frobExp * N)` is the size of the residue field
of `W`. Here `T.frobExp` is the exponent of the power `P = p ^ T.frobExp` that links consecutive
letters: the ring map of the letter `s + 1` is the `P`-th power of that of `s` modulo `p`. A
multinomial coefficient of degree less than `q` with at most `k²` parts has `p`-adic valuation at
most `c₀`. -/
def multinomialExponent (k : ℕ) : ℕ := k ^ 2 * (T.frobExp * N)

/-- The weights `b` define a pairing `⟨h, h'⟩ = ∑_β h'_β b_β h_β` on coefficient vectors for which
the matrices `ρ(g) = T.letterRep n g` and `ρ(gᵀ)` are adjoint, and the vector `b'` inverts `b` up to
the factor `p ^ (N c₀)`, where `c₀ = T.multinomialExponent k`. It is used as the pairing, in
normalized coefficients, of the halfway lattices of an edge and of the edge of dual lattices. -/
structure IsEdgePairing (b b' : Exponents N k n → O) : Prop where
  /-- The adjoint of `ρ(g)` is `ρ(gᵀ)`: entry by entry, `diag(b) ρ(gᵀ) = ρ(g)ᵀ diag(b)`. -/
  adjoint : ∀ (g : GL (Fin k) W) (α β : Exponents N k n),
    b β * T.letterRep n (transposeGL g) β α = b α * T.letterRep n g α β
  /-- The pairing is perfect up to `p ^ (N c₀)`. -/
  mul_eq_pow : ∀ β : Exponents N k n, b β * b' β = (T.p : O) ^ (N * T.multinomialExponent k)

/-- Let `⟨h, h'⟩ = ∑_β h'_β b_β h_β`, where the weights `b` satisfy `diag(b) ρ(gᵀ) = ρ(g)ᵀ diag(b)`
for `ρ = T.letterRep n`. Then translation by `g` is adjoint to translation by the transpose of `g`:
`⟨ρ(g) h, h'⟩ = ⟨h, ρ(gᵀ) h'⟩`. -/
lemma IsEdgePairing.dotProduct_letterRep_mulVec {T : FrobeniusCycle N W O}
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') (g : GL (Fin k) W)
    (h h' : Exponents N k n → O) :
    h' ⬝ᵥ (b * T.letterRep n g *ᵥ h) = (T.letterRep n (transposeGL g) *ᵥ h') ⬝ᵥ (b * h) := by
  have h_diag (v : Exponents N k n → O) : b * v = diagonal b *ᵥ v :=
    funext fun β ↦ (mulVec_diagonal b v β).symm
  have h_adj : diagonal b * T.letterRep n g = (T.letterRep n (transposeGL g))ᵀ * diagonal b :=
    Matrix.ext fun α β ↦ by rw [diagonal_mul, mul_diagonal, transpose_apply, ← hb.adjoint, mul_comm]
  rw [h_diag, h_diag, mulVec_mulVec, h_adj, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The pairing `⟨h, h'⟩ = ∑_β h'_β b_β h_β` is perfect up to `p ^ (N c₀)`, where
`c₀ = T.multinomialExponent k` and `b_β b'_β = p ^ (N c₀)` for all `β`: every linear form
`h' ↦ h' ⬝ᵥ η`, times `p ^ (N c₀)`, is the pairing with the vector `h = b' * η`. -/
lemma IsEdgePairing.pairing_mul_eq_pow_mul_dotProduct {T : FrobeniusCycle N W O}
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') (η h' : Exponents N k n → O) :
    h' ⬝ᵥ (b * (b' * η)) = (T.p : O) ^ (N * T.multinomialExponent k) * h' ⬝ᵥ η := by
  have h_mul : b * (b' * η) = (T.p : O) ^ (N * T.multinomialExponent k) • η :=
    funext fun β ↦ by simp [← mul_assoc, hb.mul_eq_pow]
  simp [h_mul]

/-- For a Frobenius cycle `T` over a valuation domain `O` of characteristic zero, a pairing of an
edge with the edge of dual lattices exists if `p = T.p` is not a unit in `O` and the degree `n` in
each letter is less than `q = T.q`, the number of elements of the residue field of `W`. -/
lemma exists_isEdgePairing [IsDomain O] [ValuationRing O] [CharZero O] (hp : ¬IsUnit (T.p : O))
    (hn : n < T.q) : ∃ b b' : Exponents N k n → O, T.IsEdgePairing b b' := by
  -- In one letter, `b₀ γ` is `p ^ (k log_p q)` divided by a multinomial coefficient.
  obtain ⟨b₀, hb₀_mul, hb₀_adj⟩ :=
    Average.exists_isAdjointWeight (Fin k) T.prime hp (T.frobExp * N)
  -- The factor `u` raises the exponent `k log_p q` to `c₀ = k² log_p q`.
  let u : O := (T.p : O) ^ ((k - 1) * k * (T.frobExp * N))
  refine ⟨fun β ↦ ∏ s, u * b₀ (β s).val, fun β ↦ ∏ s, ((β s).val.multinomial : O),
    fun g α β ↦ ?_, fun β ↦ ?_⟩
  · simp only [letterRep_apply, kroneckerPi, of_apply, ← prod_mul_distrib]
    refine prod_congr rfl fun s _ ↦ ?_
    have h_tr : T.letterMatrix s (transposeGL g) = (T.letterMatrix s g)ᵀ := by
      by_cases hs : T.isEven s <;>
        simp [letterMatrix_apply, hs, transposeGL, transpose_map, -coe_units_inv]
    simpa [h_tr, symPowMatrix, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (u * ·) (hb₀_adj (T.letterMatrix s g) (α s).val (β s).val).symm
  · have h (s : ZMod N) :
        u * b₀ (β s).val * (β s).val.multinomial = (T.p : O) ^ T.multinomialExponent k := by
      rw [mul_assoc, mul_comm (b₀ _), ← hb₀_mul _ (by rwa [Monomials.degree_eq, pow_mul]),
        Fintype.card_fin, ← pow_add, multinomialExponent, ← add_mul, Nat.sub_one_mul,
        Nat.sub_add_cancel k.le_mul_self, sq]
    simp only [← prod_mul_distrib, h, prod_const, card_univ, ZMod.card, ← pow_mul, mul_comm N]

/-! ### Functions on edges -/

section Global

variable {X E : Type*} [Fintype X] [DecidableEq X]

/-- The map from the integral functions on the set `X` of origins to the functions on the set `E`
of edges. The edge `e` has the origin `src e`, and `g e` passes to a basis adapted to `e`. The
value at `e` is the vector of normalized coefficients of the translate by `g e` of the value at
`src e`. -/
def edgeRestriction (n r : ℕ) (src : E → X) (g : E → GL (Fin k) W) :
    Matrix (E × Exponents N k n) (X × Exponents N k n) O :=
  of fun (x : E × Exponents N k n) (y : X × Exponents N k n) ↦
    if src x.1 = y.1 then (T.depthScaling k n r * T.letterRep n (g x.1)) x.2 y.2 else 0

/-- The functions `ψ` on edges, with values in the halfway lattices, that depend only on the origin:
some `sqrtPrime ^ m • ψ` is the image under `edgeRestriction` of an integral function `φ` on
origins. -/
def originFunctions (n r : ℕ) (src : E → X) (g : E → GL (Fin k) W) :
    Submodule O (E × Exponents N k n → O) where
  carrier := {ψ : E × Exponents N k n → O | ∃ (m : ℕ) (φ : X × Exponents N k n → O),
    T.sqrtPrime ^ m • ψ = T.edgeRestriction n r src g *ᵥ φ}
  add_mem' := by
    rintro ψ ψ' ⟨m, φ, hψ⟩ ⟨m', φ', hψ'⟩
    refine ⟨m + m', T.sqrtPrime ^ m' • φ + T.sqrtPrime ^ m • φ', ?_⟩
    rw [mulVec_add, mulVec_smul, mulVec_smul, ← hψ, ← hψ', pow_add]
    module
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c ψ ⟨m, φ, hψ⟩
    exact ⟨m, c • φ, by rw [mulVec_smul, ← hψ, smul_comm]⟩

/-- The value at `(e, β)` of `T.edgeRestriction n r src g *ᵥ φ` is the `β` entry of `Δ ρ(g e)`
applied to `α ↦ φ (src e, α)`, where `Δ = T.depthScaling k n r` and `ρ = T.letterRep n`. So it is
the translate by `g e` of the value of `φ` at the origin `src e` of the edge `e`, with coefficients
rescaled by powers of `T.sqrtPrime`. -/
lemma edgeRestriction_mulVec_apply {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (φ : X × Exponents N k n → O) (e : E) (β : Exponents N k n) :
    (T.edgeRestriction n r src g *ᵥ φ) (e, β) =
      (T.depthScaling k n r *ᵥ T.letterRep n (g e) *ᵥ
        fun α : Exponents N k n ↦ φ (src e, α)) β := by
  rw [mulVec_mulVec]
  simp [edgeRestriction, mulVec, dotProduct, sum_prod_type]

omit [Fintype X] in
/-- The transpose of `edgeRestriction`: its value on `ψ` at the origin `x` is the sum over the edges
`e` from `x` of `(Δ ρ(g e))ᵀ ψ(e)`, where `Δ = T.depthScaling k n r` and `ρ = T.letterRep n`. -/
lemma transpose_edgeRestriction_mulVec [Fintype E] {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (ψ : E × Exponents N k n → O) (x : X) (α : Exponents N k n) :
    ((T.edgeRestriction n r src g)ᵀ *ᵥ ψ) (x, α) = ∑ e : E with src e = x,
      ((T.depthScaling k n r * T.letterRep n (g e))ᵀ *ᵥ
        fun β : Exponents N k n ↦ ψ (e, β)) α := by
  simp [edgeRestriction, mulVec, dotProduct, Fintype.sum_prod_type, sum_filter, -transpose_mul]

/-- From edges to all bases. Let the edge `e : E` have the origin `src e : X` and a change of basis
`g e ∈ GL_k(W)`. With `ρ = T.letterRep n` and the diagonal matrix `Δ = T.depthScaling k n r`, which
multiplies the coefficient at `β` by `T.sqrtPrime ^ depth β`, the restriction
`T.edgeRestriction n r src g` sends `φ` to the function with value `Δ ρ(g e) φ(src e)` at `e`.
Suppose that every edge from every origin occurs: each pair of a point of `X` and a left coset of
the parahoric subgroup for the blocks of sizes `r` and `k - r` (`ParahoricCosets`) is
`(src e, (g e)⁻¹)` for some `e`. If `z` divides every coefficient of the restriction of `φ`, then it
divides those of `Δ ρ(γ) φ(y)` for all `y ∈ X` and `γ ∈ GL_k(W)`. -/
lemma dvd_depthScaling_mulVec_of_dvd_edgeRestriction {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (h_surj : Surjective fun e : E ↦ ((src e, ↑(g e)⁻¹) : X × ParahoricCosets W k r))
    {z : O} {φ : X × Exponents N k n → O}
    (hz : ∀ x : E × Exponents N k n, z ∣ (T.edgeRestriction n r src g *ᵥ φ) x) (y : X)
    (γ : GL (Fin k) W) (β : Exponents N k n) :
    z ∣ (T.depthScaling k n r *ᵥ T.letterRep n γ *ᵥ fun α : Exponents N k n ↦ φ (y, α)) β := by
  -- Write `γ = u * g e` with `u` parahoric and `src e = y`.
  obtain ⟨e, rfl, he⟩ : ∃ e : E, src e = y ∧ g e * γ⁻¹ ∈ parahoric W (twoBlock k r) := by
    simpa [QuotientGroup.eq] using h_surj (y, ↑γ⁻¹)
  have hu : γ * (g e)⁻¹ ∈ parahoric W (twoBlock k r) := by simpa using inv_mem he
  obtain ⟨A, hA : T.depthScaling k n r * T.letterRep n (γ * (g e)⁻¹) = A * T.depthScaling k n r⟩ :=
    T.exists_depthScaling_mul_letterRep_eq hu
  have h_translate : T.depthScaling k n r * T.letterRep n γ =
      A * (T.depthScaling k n r * T.letterRep n (g e)) := by
    rw [← mul_assoc, ← hA, mul_assoc, ← map_mul, inv_mul_cancel_right]
  rw [mulVec_mulVec, h_translate, ← mulVec_mulVec, ← mulVec_mulVec]
  refine dvd_sum fun α _ ↦ Dvd.dvd.mul_left ?_ _
  simpa only [edgeRestriction_mulVec_apply] using hz (e, α)

/-- Let `ψ` be in `T.originFunctions n r src g`: for some `m`, the multiple `w ^ m • ψ` is the
restriction to edges (`edgeRestriction`) of a function `φ` on the origins with values in `O`, where
`w = T.sqrtPrime` and the value of the restriction at the edge `e` is `Δ ρ(g e) φ(src e)`, for
`Δ = T.depthScaling k n r` and `ρ = T.letterRep n`. Suppose that every edge from every origin
occurs: each pair of a point of `X` and a left coset of the parahoric subgroup is
`(src e, (g e)⁻¹)` for some `e`. Then each value `v = ψ(e)` lies in the halfway lattices of all
edges (`allEdgesForms`): for some `m` and some `h` with `w ^ m • v = Δ h`, the power `w ^ m`
divides all coefficients of `Δ ρ(γ) h` for every `γ ∈ GL_k(W)`. -/
lemma apply_mem_allEdgesForms {r : ℕ} {src : E → X} {g : E → GL (Fin k) W}
    (h_surj : Surjective fun e : E ↦ ((src e, ↑(g e)⁻¹) : X × ParahoricCosets W k r))
    {ψ : E × Exponents N k n → O} (hψ : ψ ∈ T.originFunctions n r src g) (e : E) :
    (fun β : Exponents N k n ↦ ψ (e, β)) ∈ T.allEdgesForms k n r := by
  obtain ⟨m, φ, hφ : T.sqrtPrime ^ m • ψ = T.edgeRestriction n r src g *ᵥ φ⟩ := hψ
  refine ⟨m, T.letterRep n (g e) *ᵥ fun α : Exponents N k n ↦ φ (src e, α), ?_, fun γ β ↦ ?_⟩
  · exact funext fun β ↦ by simp [← edgeRestriction_mulVec_apply, ← hφ]
  · rw [mulVec_mulVec _ (T.letterRep n γ), ← map_mul]
    exact T.dvd_depthScaling_mulVec_of_dvd_edgeRestriction h_surj (fun x ↦ by simp [← hφ])
      (src e) (γ * g e) β

/-- If `z` divides `c` times every entry of one column of an invertible matrix, it divides `c`. -/
lemma dvd_of_forall_dvd_mul_inv_apply {I : Type*} [Fintype I] [DecidableEq I] (P : GL I O)
    {z c : O} {i : I} (h_col : ∀ j : I, z ∣ c * P⁻¹.val j i) : z ∣ c := by
  have h_diag : ∑ j : I, P.val i j * (c * P⁻¹.val j i) = c := by
    simp only [mul_left_comm, ← mul_sum, ← Matrix.mul_apply, P.mul_inv, one_apply_eq, mul_one]
  rw [← h_diag]
  exact dvd_sum fun j _ ↦ (h_col j).mul_left _

/-- The integral functions on origins have small colength in the functions on edges that depend only
on the origin. Here `O` is a valuation domain and `T` is a Frobenius cycle from the local ring `W`
to `O`. `w = T.sqrtPrime` squares to the prime `T.p`. The edge `e : E` has the origin `src e : X`
and a change of basis `g e ∈ GL_k(W)`. The matrix `T.edgeRestriction n r src g` sends a function `φ`
on origins to `e ↦ Δ ρ(g e) φ(src e)`. Here `ρ = T.letterRep n`, and `Δ` multiplies the coefficient
at `β` by `w ^ depth β`. `T.originFunctions n r src g` consists of the `ψ` with some `w ^ m • ψ` in
the image of this matrix.

Suppose that every edge from every origin occurs. That is, each pair of a point of `X` and a left
coset in `ParahoricCosets W k r` is `(src e, (g e)⁻¹)` for some `e`. Suppose also that all depths
are at most `x`. Then there are matrices `Q` and `R` with `R * Q = 1`, such that `Q *ᵥ φ` lies in
`originFunctions` for every `φ`. Moreover `Q * d = edgeRestriction` for a `d` whose determinant
divides `w ^ l`. Here `l` is `|X|` times the sum over `1 ≤ δ ≤ x` of the dimensions of the spaces
`deepForms`. These are the forms over the residue field of `O` all of whose translates have only
monomials of depth at least `δ`. -/
lemma exists_originFunctions_factorization_det_dvd [Fintype E] [DecidableEq E] {r : ℕ} {src : E → X}
    {g : E → GL (Fin k) W} [IsDomain O] [ValuationRing O]
    (h_surj : Surjective fun e : E ↦ ((src e, ↑(g e)⁻¹) : X × ParahoricCosets W k r))
    {x : ℕ} (h_depth : ∀ β : Exponents N k n, T.depth k n r β ≤ x) :
    ∃ (Q : Matrix (E × Exponents N k n) (X × Exponents N k n) O)
      (R : Matrix (X × Exponents N k n) (E × Exponents N k n) O)
      (d : Matrix (X × Exponents N k n) (X × Exponents N k n) O),
      (∀ φ : X × Exponents N k n → O, Q *ᵥ φ ∈ T.originFunctions n r src g) ∧
      R * Q = 1 ∧
      Q * d = T.edgeRestriction n r src g ∧
      d.det ∣ T.sqrtPrime ^ (Fintype.card X * ∑ δ ∈ range x,
        finrank (ResidueField O) ((T.map (residue O)).deepForms k n r (δ + 1))) := by
  classical
  -- Elementary divisors: `J * P⁻¹ = Q * diagonal t` for the inclusion `J`.
  set J : Matrix (E × Exponents N k n) (X × Exponents N k n) O := T.edgeRestriction n r src g
  let ι : X × Exponents N k n ↪ E × Exponents N k n :=
    .ofSurjective _ ((Prod.fst_surjective.comp h_surj).prodMap surjective_id)
  obtain ⟨Q, R, P, t, hRQ : R * Q = 1, hJP : J * P⁻¹.val = Q * diagonal t⟩ :=
    exists_mul_inv_eq_mul_diagonal ι J
  -- So `t i` divides the normalized coefficients of all translates of column `i` of `P⁻¹`.
  have ht_dvd (i : X × Exponents N k n) (y : X) (γ : GL (Fin k) W) (β : Exponents N k n) :
      t i ∣ T.sqrtPrime ^ T.depth k n r β * (T.letterRep n γ *ᵥ fun α ↦ P⁻¹.val (y, α) i) β := by
    rw [← depthScaling_mulVec_apply]
    refine T.dvd_depthScaling_mulVec_of_dvd_edgeRestriction (φ := P⁻¹.val.col i) h_surj
      (fun e ↦ ?_) y γ β
    change t i ∣ (J * P⁻¹.val) e i
    simp [hJP, -coe_units_inv]
  -- With `γ = 1`, it divides `w ^ x` times a column of an invertible matrix, hence `w ^ x`.
  have ht_pow (i : X × Exponents N k n) : t i ∣ T.sqrtPrime ^ x := by
    refine dvd_of_forall_dvd_mul_inv_apply P (i := i) fun ⟨y, β⟩ ↦ ?_
    have h_mul : t i ∣ T.sqrtPrime ^ T.depth k n r β * P⁻¹.val (y, β) i := by
      simpa using ht_dvd i y 1 β
    exact h_mul.trans (mul_dvd_mul_right (pow_dvd_pow T.sqrtPrime (h_depth β)) _)
  refine ⟨Q, R, diagonal t * P.val, fun φ ↦ ?_, hRQ, ?_, ?_⟩
  · -- With `w ^ x = t i * t' i`, the vector `w ^ x • Q φ` is a value of `J`.
    choose t' ht' using (ht_pow : ∀ i : X × Exponents N k n, ∃ c : O, T.sqrtPrime ^ x = t i * c)
    have h_scalar : diagonal t *ᵥ diagonal t' *ᵥ φ = T.sqrtPrime ^ x • φ :=
      funext fun i ↦ by simp [mulVec_diagonal, ← mul_assoc, ← ht']
    exact ⟨x, P⁻¹.val *ᵥ diagonal t' *ᵥ φ,
      by rw [mulVec_mulVec, hJP, ← mulVec_mulVec, h_scalar, mulVec_smul]⟩
  · rw [← Matrix.mul_assoc, ← hJP, Matrix.mul_assoc, P.inv_mul, Matrix.mul_one]
  -- If `t j` does not divide `w ^ δ`, column `j` has only depths above `δ` modulo `𝔪_O`.
  have h_deep (δ : ℕ) (j : X × Exponents N k n) (hj : ¬t j ∣ T.sqrtPrime ^ δ) (y : X) :
      (fun α ↦ P⁻¹.val (y, α) j) ∈
        T.translatesIn n 0 (maximalIdeal O) {β | T.depth k n r β < δ + 1} := by
    intro γ _ β hβ
    refine (mem_maximalIdeal _).2 fun h_unit ↦ hj ?_
    exact (h_unit.dvd_mul_right.1 (ht_dvd j y γ β)).trans
      (pow_dvd_pow T.sqrtPrime (Nat.le_of_lt_succ hβ))
  -- The columns of `P⁻¹` are independent modulo `𝔪_O`, which bounds the number of these `j`.
  have h_card (δ : ℕ) : #{i : X × Exponents N k n | ¬t i ∣ T.sqrtPrime ^ δ} ≤ Fintype.card X *
      finrank (ResidueField O) ((T.map (residue O)).deepForms k n r (δ + 1)) :=
    card_le_mul_finrank_of_dual_rows P⁻¹.val P.val
      (fun j _ i ↦ by rw [P.mul_inv, Matrix.one_apply])
      fun j hj y ↦ T.residue_mem_translatesIn (h_deep δ j (mem_filter.1 hj).2 y)
  rw [det_mul, det_diagonal, (isUnits_det_units P).mul_right_dvd, mul_sum]
  exact (prod_dvd_pow_sum_card ht_pow).trans
    (pow_dvd_pow T.sqrtPrime (sum_le_sum fun δ _ ↦ h_card δ))

/-- Let the edge `e : E` have the origin `src e : X` and a change of basis `g e ∈ GL_k(W)`. Let
`T.edgeRestriction n r src g` be the matrix that sends a function `φ` on origins to
`e ↦ Δ ρ(g e) φ(src e)`, for `ρ = T.letterRep n` and `Δ = T.depthScaling k n r`, and let
`T.originFunctions n r src g` be the module of the `ψ` with `T.sqrtPrime ^ m • ψ` in its image for
some `m`. If `O` is a domain of characteristic zero, `Q` has a left inverse `R` and this matrix
factors as `Q * d`, then `Q R` fixes every such `ψ`. -/
lemma mulVec_mulVec_eq_self_of_mem_originFunctions [Fintype E] {r : ℕ} {src : E → X}
    {g : E → GL (Fin k) W} [IsDomain O] [CharZero O]
    {Q : Matrix (E × Exponents N k n) (X × Exponents N k n) O}
    {R : Matrix (X × Exponents N k n) (E × Exponents N k n) O}
    {d : Matrix (X × Exponents N k n) (X × Exponents N k n) O} (hRQ : R * Q = 1)
    (hQd : Q * d = T.edgeRestriction n r src g) {ψ : E × Exponents N k n → O}
    (hψ : ψ ∈ T.originFunctions n r src g) :
    Q *ᵥ R *ᵥ ψ = ψ := by
  obtain ⟨m, φ, hφ : T.sqrtPrime ^ m • ψ = T.edgeRestriction n r src g *ᵥ φ⟩ := hψ
  refine smul_right_injective _ (pow_ne_zero m T.sqrtPrime_ne_zero)
    (?_ : T.sqrtPrime ^ m • Q *ᵥ R *ᵥ ψ = T.sqrtPrime ^ m • ψ)
  -- Both sides become `Q (d φ)`, as `R Q = 1`.
  rw [← mulVec_smul, ← mulVec_smul, hφ, ← hQd, ← mulVec_mulVec, mulVec_mulVec _ R, hRQ, one_mulVec]

end Global

end Edges

/-! ### Large defect -/

variable {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
variable (T : FrobeniusCycle N W O) [IsDomain O] [CharZero O]
variable {a r : Fin k}

/-- A large defect forces a divisible coefficient. Let `O` be a domain of characteristic zero, `T` a
Frobenius cycle and `w = T.sqrtPrime`, so `w ^ 2 = p`. Let `a < r` be indices of variables, so `a`
is in the first and `r` in the second of the blocks `b < r`, `b ≥ r`. In a letter `s` let
`(u_s, ū_s)` be `(r, a)` if `s` is even and `(a, r)` if it is odd. The defect of `β` at the letter
`i`, which is its weight for `T.defectWeight i a r`, is `β_i(u_i) + ∑_s P ^ ((s - i) mod N)
(β_s(u_s) - β_s(ū_s)) / (q - 1)`, for `P = p ^ T.frobExp` and `q = P ^ N`.

If `w ^ m` divides `w ^ depth β * (ρ(g) F) β` for all `g` and `β`, where `ρ = T.letterRep n`, then
`w ^ (m + j)` divides it at the exponents `β` of defect at least `3 j`. -/
lemma pow_add_dvd_of_le_defect {m j : ℕ} (i : ZMod N) (ha : a < r) {F : Exponents N k n → O}
    (hF : ∀ (g : GL (Fin k) W) (β : Exponents N k n),
      T.sqrtPrime ^ m ∣ T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β)
    {β : Exponents N k n} {g : GL (Fin k) W}
    (hβ : 3 * j ≤ (exponentOf β).weight (T.defectWeight i a r)) :
    T.sqrtPrime ^ (m + j) ∣ T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β := by
  -- The depth rises by `1` along the root `(a, r)` in each letter.
  have h_depth (δ : Exponents N k n) : (exponentOf δ).weight (fun x : Fin k × ZMod N ↦
      (T.deepIndicator r x : ℝ)) = T.depth k n r δ := by simp [depth, Finsupp.weight_eq_sum]
  have h_step (s : ZMod N) :
      (T.deepIndicator r (T.rootVar a r s) : ℝ) - T.deepIndicator r (T.rootVar r a s) = 1 := by
    by_cases h_even : T.isEven s <;> simp [deepIndicator, rootVar, h_even, ha]
  have h_translates (γ : GL (Fin k) W) (_ : γ ∈ rootSL W a r) :
      T.polyAction γ (polyOfCoeffs (T.letterRep n g *ᵥ F)) ∈
        gaussFiltration (adicFiltration T.sqrtPrime)
          (fun x : Fin k × ZMod N ↦ (T.deepIndicator r x : ℝ)) m := by
    rw [polyAction_polyOfCoeffs, mulVec_mulVec, ← map_mul, polyOfCoeffs, LinearMap.sum_apply]
    refine _root_.sum_mem fun δ _ ↦ monomial_mem_gaussFiltration ?_
    change T.sqrtPrime ^ ⌈m - (exponentOf δ).weight fun x ↦ (T.deepIndicator r x : ℝ)⌉₊ ∣ _
    rw [h_depth, Nat.ceil_sub_natCast, Nat.ceil_natCast]
    exact pow_sub_dvd_of_pow_dvd_pow_mul T.sqrtPrime_ne_zero (hF (γ * g) δ)
  -- Hence the depth may be lowered by a third of the defect.
  set defect : ℝ := (exponentOf β).weight (T.defectWeight i a r) with h_defect
  have h_gain : T.sqrtPrime ^ ⌈m - (T.depth k n r β - defect / 3)⌉₊ ∣ (T.letterRep n g *ᵥ F) β := by
    simpa [h_defect, weight_sub_defectWeight_div_three, h_depth, polyOfCoeffs, coeff_sum] using
      T.mem_gaussFiltration_sub_defect_div_three i ha.ne h_step h_translates (exponentOf β)
  have h_exponent : m + j ≤ T.depth k n r β + ⌈m - (T.depth k n r β - defect / 3)⌉₊ := by
    rify
    linarith [Nat.le_ceil (m - (T.depth k n r β - defect / 3))]
  exact (pow_dvd_pow T.sqrtPrime h_exponent).trans
    (by simpa only [pow_add] using mul_dvd_mul_left _ h_gain)

/-- Let `O` be a domain of characteristic zero, `w = T.sqrtPrime` the square root of the prime of
the Frobenius cycle `T`, and `a < r` indices of variables, one in each of the blocks `b < r`,
`b ≥ r`. Let `v` lie in `T.allEdgesForms k n r`: for some `m` and some `h` with `w ^ m • v = Δ h`,
the power `w ^ m` divides all coefficients of `Δ ρ(γ) h` for every `γ ∈ GL_k(W)`. Here
`ρ = T.letterRep n` and `Δ = T.depthScaling k n r` multiplies the coefficient at `β` by
`w ^ depth β`. Let `g` be block diagonal (`levi`). If `β` has defect at least `3 j` at the letter
`i`, that is, `β_i(u_i) + ∑_s P ^ ((s - i) mod N) (β_s(u_s) - β_s(ū_s)) / (q - 1) ≥ 3 j` with
`(u_s, ū_s)` equal to `(r, a)` for even and `(a, r)` for odd `s` (`T.defectWeight i a r`;
`P = p ^ T.frobExp`, `q = P ^ N`), then `w ^ j` divides the coefficient at `β` of `ρ(g) v`. -/
lemma pow_dvd_letterRep_mulVec_of_mem_allEdgesForms (ha : a < r) {v : Exponents N k n → O}
    (hv : v ∈ T.allEdgesForms k n r) {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r)) {j : ℕ}
    {i : ZMod N} {β : Exponents N k n}
    (hβ : 3 * j ≤ (exponentOf β).weight (T.defectWeight i a r)) :
    T.sqrtPrime ^ j ∣ (T.letterRep n g *ᵥ v) β := by
  obtain ⟨m, F, hvF : T.sqrtPrime ^ m • v = T.depthScaling k n r *ᵥ F, h_dvd⟩ := hv
  have h_normalized (γ : GL (Fin k) W) (δ : Exponents N k n) :
      T.sqrtPrime ^ m ∣ T.sqrtPrime ^ T.depth k n r δ * (T.letterRep n γ *ᵥ F) δ := by
    simpa only [depthScaling_mulVec_apply] using h_dvd γ δ
  have h_translate : T.sqrtPrime ^ m * (T.letterRep n g *ᵥ v) β =
      T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β :=
    calc T.sqrtPrime ^ m * (T.letterRep n g *ᵥ v) β
      _ = (T.letterRep n g *ᵥ T.depthScaling k n r *ᵥ F) β := by simp [← hvF, mulVec_smul]
      _ = T.sqrtPrime ^ T.depth k n r β * (T.letterRep n g *ᵥ F) β := by
          rw [mulVec_mulVec, ← (T.commute_depthScaling_letterRep hg).eq, ← mulVec_mulVec,
            depthScaling_mulVec_apply]
  rw [← mul_dvd_mul_iff_left (pow_ne_zero m T.sqrtPrime_ne_zero), ← pow_add, h_translate]
  exact T.pow_add_dvd_of_le_defect i ha h_normalized hβ

/-- Above any cutoff at least `defectThreshold k c`, every Levi translate of an all-edges
form has coefficients divisible by `T.sqrtPrime ^ c`. -/
private lemma allEdgesForms_le_defectConditions_of_threshold_le (ha : a < r) (c : ℕ)
    {d : ℝ} (hd : (defectThreshold k c : ℝ) ≤ d) :
    T.allEdgesForms k n r ≤ T.defectConditions n a r (span {T.sqrtPrime ^ c}) d := by
  rintro v hv g hg β ⟨i, hi⟩
  have hc : (3 * c : ℝ) ≤ defectThreshold k c := mod_cast three_mul_le_defectThreshold a.pos c
  exact mem_span_singleton.2
    (T.pow_dvd_letterRep_mulVec_of_mem_allEdgesForms ha hv hg (hc.trans (hd.trans hi.le)))

/-- Let `O` be a domain of characteristic zero. The forms in the halfway lattices of all edges
(`allEdgesForms`) satisfy the conditions on an edge (`defectConditions`): their block diagonal
translates have, modulo `sqrtPrime ^ c`, no term of defect above `3 c*` along the root `(a, r)`,
where `c* = 3 k c` is `defectThreshold k c` and `a < r` are indices, one in each block. -/
lemma allEdgesForms_le_defectConditions (ha : a < r) (c : ℕ) :
    T.allEdgesForms k n r ≤ T.defectConditions n a r (span {T.sqrtPrime ^ c})
      (3 * defectThreshold k c) :=
  T.allEdgesForms_le_defectConditions_of_threshold_le ha c
    (le_mul_of_one_le_left (by positivity) (by norm_num))

/-- Let `O` be a domain of characteristic zero, `w = T.sqrtPrime` (so `w ^ 2 = p`) and
`ρ = T.letterRep n`. Let `(b, b')` be an edge pairing: `ρ(g)` and `ρ(gᵀ)` are adjoint for
`∑_β h'_β b_β h_β`, and `b_β b'_β` is a fixed power of `p` (`IsEdgePairing`). Let `v` lie in
`T.allEdgesForms k n r`: for some `m` and some `h` with `w ^ m • v = Δ h`, the power `w ^ m` divides
all coefficients of `Δ ρ(γ) h` for every `γ`, where `Δ = T.depthScaling k n r`. Let `a < r` be
indices of variables, one in each of the blocks `b < r`, `b ≥ r`, let `g` be block diagonal, and let
`β` have defect above `c* = 3 k c` (`defectThreshold k c`) at the letter `i`. This defect, the
weight for `T.defectWeight i a r`, is `β_i(u_i) + ∑_s P ^ ((s - i) mod N) (β_s(u_s) -
β_s(ū_s)) / (q - 1)`, with `(u_s, ū_s) = (r, a)` for even and `(a, r)` for odd `s`,
`P = p ^ T.frobExp`, `q = P ^ N`. Then `w ^ c` divides the pairing, by the weights `b`, of `v` with
the image under `ρ(g)` of the unit vector at `β`. -/
lemma IsEdgePairing.pow_dvd_pairing_letterRep {b b' : Exponents N k n → O}
    (hb : T.IsEdgePairing b b') (ha : a < r) {v : Exponents N k n → O}
    (hv : v ∈ T.allEdgesForms k n r) {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r)) {c : ℕ}
    {i : ZMod N} {β : Exponents N k n}
    (hβ : defectThreshold k c < (exponentOf β).weight (T.defectWeight i a r)) :
    T.sqrtPrime ^ c ∣ v ⬝ᵥ (b * T.letterRep n g *ᵥ Pi.single β 1) := by
  have hg' : transposeGL g ∈ levi W (twoBlock k r) := fun i j hij ↦ hg j i hij.symm
  -- The pairing is `b β` times the coefficient at `β` of the translate of `v` by the transpose.
  have h_pairing : v ⬝ᵥ (b * T.letterRep n g *ᵥ Pi.single β 1) =
      (T.letterRep n (transposeGL g) *ᵥ v) β * b β := by
    rw [hb.dotProduct_letterRep_mulVec]
    simp [dotProduct, Pi.single_apply]
  have h_coeff := T.allEdgesForms_le_defectConditions_of_threshold_le ha c le_rfl hv
    (transposeGL g) hg' β ⟨i, hβ⟩
  rw [h_pairing]
  exact (mem_span_singleton.1 h_coeff).mul_right _

end FrobeniusCycle

end New

end
end
end

/-!
# Averaging: removing the terms of large defect in all Levi translates at once

Fix a Frobenius cycle `T` over `W` and `O` (`New.FrobeniusCycle`; `N = 2 ℓ` letters, `P` a power of
the prime `p`, `w ^ 2 = p`) and an edge, with the Levi subgroup `G` of blocks of sizes `r` and
`k - r`. Forms are written in the normalized monomials of the edge with weights `b_β`, and
`⟨h, h'⟩ = ∑_β h'_β b_β h_β` is the pairing with the forms of the dual edge
(`New.FrobeniusCycle.IsEdgePairing`). Fix `c : ℕ` and put `c* = 3 k c` (`New.defectThreshold`) and
`c₀ = T.multinomialExponent k`. Let `O` be a valuation domain of characteristic `0` in which `p` is
not a unit, and let `P ^ ℓ` be large. The main result
`New.FrobeniusCycle.exists_average_mem_defectConditions_and_dvd_sub` gives a matrix `Av` such that
no `G(W)`-translate of `Av h` has a term of defect above `3 c*` modulo `w ^ c`, while
`⟨Av h, h'⟩ ≡ p ^ (N c₀) ⟨h, h'⟩` modulo `w ^ c` for all `h'` in the halfway lattices of all edges
from the origin of the dual edge (`New.FrobeniusCycle.allEdgesForms`).

Substitute generic matrices, one copy for each letter, in `h`
(`New.FrobeniusCycle.substitutionOperator`). For a set `J` of copies, `Av_J h`
(`New.FrobeniusCycle.partialAverage`) is obtained by applying the average (`New.Average.IsAverage`)
in the copies `j ∈ J` and `p ^ c₀` times the evaluation at `1` in the others. Then
`Av_∅ h = p ^ (N c₀) h`, and `Av` is `Av_J` for the set of all copies. A monomial in one copy is bad
if its row weight for `New.rootVector a r`, `r = a + 1`, is above `2 c* P ^ ℓ`. The substitution in
the frame `g ∈ G(W)` is the one formed from the factors
`New.FrobeniusCycle.conjFrobGenericMatrix g`.

* `New.FrobeniusCycle.contractOtherCopies`, `New.FrobeniusCycle.conjSubst_contractOtherCopies_one`:
  the linear forms are applied in all copies but one, in a frame `g`; the change of frame conjugates
  the remaining copy.
* `New.FrobeniusCycle.abs_weight_div_sub_defect_le`: let the forms be invariant under `G(W)`. If the
  coefficient of `α` in the entry `β` of `contractOtherCopies` is not divisible by `w ^ c`, then the
  row weight of `α` over `P ^ ℓ` is within `c*` of the defect of `β` at the letter `j + ℓ`, for the
  remaining copy `j`.
* `New.FrobeniusCycle.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies`: hence a defect
  of `β` above `3 c*` makes `α` bad, and a bad `α` makes the defect exceed `c*`.
* `New.FrobeniusCycle.pow_dvd_pairing_partialAverage_insert_sub`: one more copy in `J` does not
  change the pairing modulo `w ^ c`. The main result adds these differences along a chain of
  subsets.

Notions from other files:
* `New.FrobeniusCycle.letterRep`: the matrix of `g ∈ GL_k(W)` on the forms, which have degree `n` in
  each letter and are twisted at the letter `s` by `T.embedding s`.
* `New.FrobeniusCycle.substitutionOperator`: the Kronecker product over the letters `s` of the
  matrices on forms of degree `n` that are built from given factors `ψ s d`; with
  `New.FrobeniusCycle.frobGenericMatrix` the factor is the entrywise power `P ^ d` of the copy
  `s - d` of the generic matrix, and odd letters take the cofactor matrix of the product.
* `New.Average.IsAverage`: a linear form that is invariant under conjugation by the Levi subgroup
  and vanishes on bad monomials. If a polynomial of bounded degree has all bad coefficients of its
  Levi conjugates in an ideal, the form agrees on it with a multiple of the evaluation at `1` modulo
  this ideal.
* `New.FrobeniusCycle.defectConditions`: the vectors whose `G(W)`-translates have their coefficients
  of defect above a bound in a given ideal.

## Relation to the literature

Linear forms on polynomials in a generic matrix that are invariant under the Levi subgroup split
evaluation at the identity by weight, up to a power of `p`. This gives a map into the forms without
terms of large defect that keeps the pairing up to `p ^ (N c₀)` modulo `w ^ c`. The Schur algebra as
dual of polynomials in a generic matrix, its spanning by finite points in low degree, and truncation
by weights are known in the literature. Related work: Benson–Doty, Schur–Weyl duality over finite
fields, 2009; Green, Polynomial representations of GL_n, 1980; Donkin, On Schur algebras and related
algebras I, 1986.
-/

@[expose] public section

noncomputable section

namespace New

open MvPolynomial Matrix IsLocalRing Function Module PiTensorProduct Finset Fintype Ideal Average

/-! ### Tensor products of linear forms on polynomials -/

section TensorDual

private lemma algHom_map_sum {R A B κ : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (s : Finset κ) (g : κ → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) :=
  map_sum f.toRingHom.toAddMonoidHom g s

private lemma algHom_map_prod {R A B κ : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (s : Finset κ) (g : κ → A) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) :=
  map_prod f.toRingHom.toMonoidHom g s

private lemma algHom_map_pow {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (a : A) (n : ℕ) :
    f (a ^ n) = f a ^ n :=
  map_pow f.toRingHom.toMonoidHom a n

private lemma algHom_map_smul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (r : R) (a : A) :
    f (r • a) = r • f a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, f.commutes]

private lemma linearMap_map_sum {R M N κ : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (f : M →ₗ[R] N) (s : Finset κ) (g : κ → M) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) :=
  map_sum f.toAddMonoidHom g s

variable {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A linear form on polynomials is determined by its values on the monomials. -/
lemma map_eq_sum_coeff_mul (m : Dual R (MvPolynomial σ R)) (ψ : MvPolynomial σ R) :
    m ψ = ∑ α ∈ ψ.support, ψ.coeff α * m (monomial α 1) := by
  refine (congrArg m ψ.as_sum).trans
    ((linearMap_map_sum m _ _).trans (sum_congr rfl fun α _ ↦ ?_))
  rw [← smul_eq_mul, ← LinearMap.map_smul, smul_monomial, smul_eq_mul, mul_one]

/-- If for each exponent `α` either `z` divides the coefficient of `α` in `ψ` or the linear form `m`
vanishes on the monomial of exponent `α`, then `z` divides `m ψ`. -/
lemma dvd_map_of_forall_monomial {m : Dual R (MvPolynomial σ R)} {ψ : MvPolynomial σ R} {z : R}
    (h_all : ∀ α : σ →₀ ℕ, ¬z ∣ ψ.coeff α → m (monomial α 1) = 0) : z ∣ m ψ := by
  rw [map_eq_sum_coeff_mul]
  refine dvd_sum fun α _ ↦ ?_
  by_cases h_dvd : z ∣ ψ.coeff α
  · exact dvd_mul_of_dvd_left h_dvd _
  · rw [h_all α h_dvd, mul_zero]
    exact dvd_zero z

/-- The tensor product of linear forms `l j` on polynomials in disjoint blocks of variables: the
product of the forms on `⨂_ι R[X_σ]`, pulled back along `R[X_{ι × σ}] → ⨂_ι R[X_σ]`. -/
def tensorDual (l : ι → Dual R (MvPolynomial σ R)) : Dual R (MvPolynomial (ι × σ) R) :=
  dualDistrib (tprod R l) ∘ₗ
    (aeval fun v : ι × σ ↦ singleAlgHom v.1 (X v.2) :
      MvPolynomial (ι × σ) R →ₐ[R] PiTensorProduct R fun _ : ι ↦ MvPolynomial σ R).toLinearMap

/-- On a product of polynomials `f j`, one in each block, the tensor product of the forms `l j` is
the product of the values `l j (f j)`. -/
lemma tensorDual_prod_rename (l : ι → Dual R (MvPolynomial σ R)) (f : ι → MvPolynomial σ R) :
    tensorDual l (∏ j : ι, rename (fun v : σ ↦ (j, v)) (f j)) = ∏ j : ι, l j (f j) := by
  let Ψ : MvPolynomial (ι × σ) R →ₐ[R] PiTensorProduct R fun _ : ι ↦ MvPolynomial σ R :=
    aeval fun v : ι × σ ↦ singleAlgHom v.1 (X v.2)
  have h_block (j : ι) : Ψ.comp (rename fun v : σ ↦ (j, v)) =
      singleAlgHom (A := fun _ : ι ↦ MvPolynomial σ R) j :=
    algHom_ext fun v ↦ by rw [AlgHom.comp_apply, rename_X, aeval_X]
  have hΨ : Ψ (∏ j : ι, rename (fun v : σ ↦ (j, v)) (f j)) = tprod R f := by
    rw [algHom_map_prod]
    have h_eq (j : ι) : Ψ (rename (fun v : σ ↦ (j, v)) (f j)) =
        tprod R (MonoidHom.mulSingle (fun _ : ι ↦ MvPolynomial σ R) j (f j)) :=
      (AlgHom.comp_apply Ψ _ _).symm.trans ((AlgHom.congr_fun (h_block j) (f j)).trans
        (singleAlgHom_apply (R := R) (A := fun _ : ι ↦ MvPolynomial σ R) j (f j)))
    rw [Finset.prod_congr rfl fun j _ ↦ h_eq j, ← tprod_prod]
    exact congrArg (PiTensorProduct.tprod R) (univ_prod_mulSingle f)
  rw [tensorDual, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hΨ, dualDistrib_apply]

/-- On the monomial of exponent `ν`, the tensor product of the forms `l j` is the product of the
values of `l j` at the monomials of exponent `ν.curry j`, the parts of `ν` in the blocks. -/
lemma tensorDual_monomial [Fintype σ] (l : ι → Dual R (MvPolynomial σ R)) (ν : ι × σ →₀ ℕ) :
    tensorDual l (monomial ν 1) = ∏ j : ι, l j (monomial (ν.curry j) 1) := by
  rw [← tensorDual_prod_rename]
  refine congrArg (tensorDual l) ?_
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, prod_prod_type]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, algHom_map_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [algHom_map_pow, rename_X, Finsupp.curry_apply]

/-- The value of the tensor product of the forms `l j` at `f` is the sum over the monomials of `f`
of the coefficient times the product of the values of the `l j` at the parts of the monomial. -/
lemma tensorDual_eq_sum [Fintype σ] (l : ι → Dual R (MvPolynomial σ R))
    (f : MvPolynomial (ι × σ) R) :
    tensorDual l f = ∑ ν ∈ f.support, f.coeff ν * ∏ j : ι, l j (monomial (ν.curry j) 1) := by
  rw [map_eq_sum_coeff_mul (tensorDual l) f]
  exact sum_congr rfl fun ν _ ↦ congrArg (f.coeff ν * ·) (tensorDual_monomial l ν)

/-- If the form in each block is `evalAtOne z`, that is `z` times the evaluation at the identity
matrix, then the tensor product of the forms is `z` to the number of blocks times the evaluation at
the identity matrix in every block. -/
lemma tensorDual_evalAtOne {k : ℕ} {A : Type} [CommRing A] (z : A)
    (f : MvPolynomial (ι × Fin k × Fin k) A) :
    tensorDual (fun _ : ι ↦ evalAtOne z) f = z ^ Fintype.card ι *
      eval (fun v : ι × Fin k × Fin k ↦ vec (1 : Matrix (Fin k) (Fin k) A) v.2) f := by
  rw [tensorDual_eq_sum, eval_eq', mul_sum]
  refine sum_congr rfl fun ν _ ↦ ?_
  have h_term (j : ι) : evalAtOne z (monomial (ν.curry j) 1) =
      z * ∏ v : Fin k × Fin k, vec (1 : Matrix (Fin k) (Fin k) A) v ^ ν (j, v) := by
    rw [evalAtOne_apply, eval_monomial, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
    exact congrArg (z * ·) (Finset.prod_congr rfl fun v _ ↦ by rw [Finsupp.curry_apply])
  rw [Finset.prod_congr rfl fun j _ ↦ h_term j, prod_mul_distrib, prod_const, card_univ,
    prod_prod_type, mul_left_comm]

/-- Apply the forms `l i` in all blocks `i ≠ j` of variables; a polynomial in the block `j`
remains. A monomial of exponent `ν` gives the product of the values of the `l i` at its parts
`ν.curry i`, times the monomial of exponent `ν.curry j`. -/
def tensorDualExcept (l : ι → Dual R (MvPolynomial σ R)) (j : ι) (f : MvPolynomial (ι × σ) R) :
    MvPolynomial σ R :=
  ∑ ν ∈ f.support,
    (f.coeff ν * ∏ i ∈ univ.erase j, l i (monomial (ν.curry i) 1)) • monomial (ν.curry j) 1

/-- Applying a form `m` to `tensorDualExcept l j f`, the polynomial left in the block `j` after the
forms `l i` are applied in the other blocks, gives `tensorDual (update l j m) f`: the tensor product
of the forms with `l j` replaced by `m`. -/
lemma map_tensorDualExcept [Fintype σ] (l : ι → Dual R (MvPolynomial σ R)) (j : ι)
    (m : Dual R (MvPolynomial σ R)) (f : MvPolynomial (ι × σ) R) :
    m (tensorDualExcept l j f) = tensorDual (update l j m) f := by
  rw [tensorDual_eq_sum, tensorDualExcept, linearMap_map_sum]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [LinearMap.map_smul, smul_eq_mul, mul_assoc, ← prod_erase_mul _ _ (mem_univ j), update_self]
  refine congrArg (f.coeff ν * ·) (congrArg (· * m (monomial (ν.curry j) 1)) ?_)
  exact Finset.prod_congr rfl fun i hi ↦ by rw [update_of_ne (ne_of_mem_erase hi)]

/-- Let `f` be a polynomial in blocks of variables indexed by `ι`, and let `tensorDualExcept l j f`
be the polynomial in the block `j` obtained by applying the linear forms `l i` in all blocks
`i ≠ j`. If `z` does not divide its coefficient of `α`, then `α` is the part in the block `j` of a
monomial `ν` whose coefficient in `f` is not divisible by `z` and whose other parts are not killed
by the forms `l i`. -/
lemma exists_of_not_dvd_coeff_tensorDualExcept {l : ι → Dual R (MvPolynomial σ R)} {j : ι}
    {f : MvPolynomial (ι × σ) R} {z : R} {α : σ →₀ ℕ}
    (h_coeff : ¬z ∣ (tensorDualExcept l j f).coeff α) :
    ∃ ν : ι × σ →₀ ℕ, ν.curry j = α ∧ ¬z ∣ f.coeff ν ∧
      ∀ i ≠ j, l i (monomial (ν.curry i) 1) ≠ 0 := by
  classical
  contrapose! h_coeff with h_all
  rw [tensorDualExcept, coeff_sum]
  refine dvd_sum fun ν _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeff_monomial]
  -- Each summand has `z` as a factor of its coefficient, or a factor `0`.
  by_cases h_part : ν.curry j = α
  · rw [ite_eq_left h_part, mul_one]
    by_cases h_dvd : z ∣ f.coeff ν
    · exact h_dvd.mul_right _
    · obtain ⟨i, hi, h_zero⟩ := h_all ν h_part h_dvd
      rw [prod_eq_zero (mem_erase.2 ⟨hi, mem_univ i⟩) h_zero, mul_zero]
      exact dvd_zero z
  · rw [ite_eq_right h_part, mul_zero]
    exact dvd_zero z

/-- The polynomial in the block `j` that remains of `f` after the forms `l i` are applied in the
blocks `i ≠ j` has at most the degree of `f` in the block `j`. -/
lemma tensorDualExcept_mem_restrictTotalDegree (l : ι → Dual R (MvPolynomial σ R)) (j : ι)
    {f : MvPolynomial (ι × σ) R} {D : ℕ}
    (h_degree : ∀ ν : ι × σ →₀ ℕ, f.coeff ν ≠ 0 → (ν.curry j).degree ≤ D) :
    tensorDualExcept l j f ∈ restrictTotalDegree σ R D := by
  exact Submodule.sum_mem _ fun ν hν ↦ Submodule.smul_mem _ _ <| (mem_restrictTotalDegree ..).2 <|
    (totalDegree_monomial_le _ _).trans (h_degree ν (mem_support_iff.1 hν))

end TensorDual

namespace FrobeniusCycle

variable {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
  (T : FrobeniusCycle N W O)

/-! ### Linear forms applied to the substitution -/

/-- The entries of `T.substitutionOperator r ℓ n T.frobGenericMatrix` are polynomials in `N` generic
`k × k` matrices, the copies, one for each letter `j ∈ ℤ/N`. This is the matrix over `O` obtained by
applying to each entry the tensor product of linear forms `l j`, one for each copy. Its rows and
columns are indexed by the monomials of degree `n` in each of `N` groups of `k` variables. -/
def frobContraction (n r ℓ : ℕ) (l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)) :
    Matrix (Exponents N k n) (Exponents N k n) O :=
  (T.substitutionOperator r ℓ n T.frobGenericMatrix).map (tensorDual l)

/-- The matrix `T.frobContraction n r ℓ l`, indexed by the monomials of degree `n` in each of `N`
groups of `k` variables (`Exponents N k n`), arises from the substitution of `N` generic `k × k`
matrices by applying a linear form `l j` in the entries of the `j`-th one. If each form is `z` times
the evaluation at the identity matrix (`evalAtOne z`), it is the scalar matrix `z ^ N`. -/
lemma frobContraction_evalAtOne (r ℓ : ℕ) (z : O) :
    T.frobContraction (k := k) n r ℓ (fun _ : ZMod N ↦ evalAtOne z) =
      z ^ N • (1 : Matrix (Exponents N k n) (Exponents N k n) O) := by
  -- At the identity matrices `substitutionOperator` is `1`.
  let ev : MvPolynomial (ZMod N × Fin k × Fin k) O →+* O :=
    eval fun v : ZMod N × Fin k × Fin k ↦ vec (1 : Matrix (Fin k) (Fin k) O) v.2
  have h_factor (s : ZMod N) (d : ℕ) : (T.frobGenericMatrix s d).map ev = 1 := by
    ext b c
    rw [Matrix.map_apply, frobGenericMatrix, of_apply, map_pow, eval_X, Matrix.one_apply]
    dsimp only [vec]
    by_cases h : b = c
    · subst h
      rw [ite_eq_left rfl, Matrix.one_apply_eq, one_pow]
    · rw [ite_eq_right h, Matrix.one_apply_ne (Ne.symm h),
        zero_pow (pow_ne_zero d (pow_ne_zero _ T.prime.ne_zero))]
  have h_one : (T.substitutionOperator (k := k) r ℓ n T.frobGenericMatrix).map ev = 1 := by
    -- `substitutionOperator_map_eq_conj` at `g = 1` moves `ev` into the factors.
    rw [T.substitutionOperator_map_eq_conj ev (one_mem _), inv_one, MonoidHom.map_one,
      Matrix.one_mul, Matrix.mul_one]
    have h_fn : (fun s d ↦ T.letterConj 1 s ((T.frobGenericMatrix s d).map ev)) =
        fun _ _ ↦ 1 := by
      funext s d
      rw [h_factor, MonoidHom.map_one]
    rw [h_fn, substitutionOperator_one]
  ext β β'
  rw [frobContraction, Matrix.map_apply, tensorDual_evalAtOne, ZMod.card, Matrix.smul_apply,
    smul_eq_mul, ← h_one, Matrix.map_apply]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `T` be a Frobenius cycle, with ring maps `T.embedding j : W →+* O` for the letters
`j ∈ ℤ/N`, and let `ρ(g) = T.letterRep n g` be the matrix of `g ∈ GL_k(W)` on polynomials of degree
`n` in each of `N` groups of `k` variables. For a family `ψ` of factors,
`S(ψ) = T.substitutionOperator r ℓ n ψ` is a matrix of the same size; here its entries are
polynomials in `N` generic matrices `X_j`. Write `l(S)` for `S.map (tensorDual l)`, the matrix over
`O` obtained by applying the linear form `l j` in the entries of `X_j` for every `j`. Let `g` be
block diagonal with blocks of sizes `r` and `k - r`, and let `m j` be `l j` composed with
`X ↦ g⁻¹ X g` through `T.embedding j` (`conjSubst`). Then `ρ(g) m(S(ψ₁)) = l(S(ψ_g)) ρ(g)`. Here
`ψ₁ = T.frobGenericMatrix` consists of the entrywise powers `P ^ d` of the `X_j`, so that
`m(S(ψ₁)) = T.frobContraction n r ℓ m`, and `ψ_g = T.conjFrobGenericMatrix g` is the same family
with the powers taken in the basis given by `g`. -/
lemma letterRep_mul_frobContraction {r ℓ : ℕ} {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r))
    {l m : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hm : ∀ (j : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O),
      m j ψ = l j (conjSubst (T.embedding j) g ψ)) :
    T.letterRep n g * T.frobContraction n r ℓ m =
      (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g)).map (tensorDual l) *
        T.letterRep n g := by
  -- Move the conjugation by `g` from the forms to the generic matrices.
  let conj :
      MvPolynomial (ZMod N × Fin k × Fin k) O →ₐ[O] MvPolynomial (ZMod N × Fin k × Fin k) O :=
    aeval fun v : ZMod N × Fin k × Fin k ↦
      rename (fun u : Fin k × Fin k ↦ (v.1, u)) (conjSubst (T.embedding v.1) g (X v.2))
  have h_monomial (ν : ZMod N × Fin k × Fin k →₀ ℕ) : conj (monomial ν 1) = ∏ j : ZMod N,
      rename (fun u : Fin k × Fin k ↦ (j, u))
        (conjSubst (T.embedding j) g (monomial (ν.curry j) 1)) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, algHom_map_prod,
      prod_prod_type]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, algHom_map_prod,
      algHom_map_prod]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [algHom_map_pow, aeval_X, algHom_map_pow, algHom_map_pow, Finsupp.curry_apply]
  have h_forms : tensorDual m = tensorDual l ∘ₗ conj.toLinearMap :=
    linearMap_ext fun ν ↦ LinearMap.ext_ring <| by
      change tensorDual m (monomial ν 1) = tensorDual l (conj (monomial ν 1))
      rw [tensorDual_monomial, h_monomial, tensorDual_prod_rename]
      exact Finset.prod_congr rfl fun j _ ↦ hm j _
  let T' : FrobeniusCycle N W (MvPolynomial (ZMod N × Fin k × Fin k) O) := T.map C
  have h_entry (s : ZMod N) (b c : Fin k) :
      conj (X (s, b, c)) = T'.letterConj g⁻¹ s (of fun b' c' : Fin k ↦ X (s, b', c')) b c := by
    have h_lhs : conj (X (s, b, c)) = ∑ b' : Fin k, ∑ c' : Fin k,
        C (T.embedding s (g⁻¹.val b b')) * C (T.embedding s (g.val c' c)) * X (s, b', c') := by
      rw [show conj (X (s, b, c)) =
          rename (fun u : Fin k × Fin k ↦ (s, u)) (conjSubst (T.embedding s) g (X (b, c))) from
          aeval_X _ _,
        conjSubst, linSubst, aeval_X, algHom_map_sum, sum_prod_type]
      refine sum_congr rfl fun b' _ ↦ sum_congr rfl fun c' _ ↦ ?_
      rw [algHom_map_smul, rename_X, kroneckerMap_apply, transpose_apply, smul_eq_C_mul, C_mul]
    rw [h_lhs, sum_comm, letterConj, MonoidHom.coe_mk, OneHom.coe_mk, inv_inv, Matrix.mul_apply]
    refine sum_congr rfl fun c' _ ↦ ?_
    rw [Matrix.mul_apply, sum_mul]
    refine sum_congr rfl fun b' _ ↦ ?_
    rw [Matrix.map_apply, Matrix.map_apply, of_apply, mul_right_comm]
    rfl
  have h_frame : (fun (s : ZMod N) (d : ℕ) ↦
      T'.letterConj g s ((T.frobGenericMatrix s d).map conj.toRingHom)) =
        T.conjFrobGenericMatrix g := by
    funext s d
    rw [conjFrobGenericMatrix]
    refine congrArg (T'.letterConj g s) (Matrix.ext fun b c ↦ ?_)
    rw [Matrix.map_apply, frobGenericMatrix, of_apply, Matrix.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algHom_map_pow, h_entry]
  -- After `conj`, the operator is a conjugate of the operator `F` in the frame `g`.
  set F := T.substitutionOperator (k := k) r ℓ n (T.conjFrobGenericMatrix g)
  have h_op : (T.substitutionOperator r ℓ n T.frobGenericMatrix).map conj.toRingHom =
      (T.letterRep n g⁻¹).map C * F * (T.letterRep n g).map C := by
    rw [← substitutionOperator_frobeniusCycle_map T C, substitutionOperator_map_eq_conj _ _ hg,
      h_frame, letterRep_map, letterRep_map, substitutionOperator_frobeniusCycle_map]
  have h_contraction : T.frobContraction n r ℓ m =
      T.letterRep n g⁻¹ * F.map (tensorDual l) * T.letterRep n g := by
    rw [← map_C_mul_mul_C, ← h_op, frobContraction, h_forms, Matrix.map_map, LinearMap.coe_comp,
      AlgHom.coe_toLinearMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h_contraction, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← MonoidHom.map_mul, mul_inv_cancel,
    MonoidHom.map_one, Matrix.one_mul]

/-! ### One copy at a time -/

/-- The substitution in the frame `g`, that is `T.substitutionOperator` at the factors
`T.conjFrobGenericMatrix g`, is a matrix of polynomials in `N` generic matrices, the copies. It is
applied to the translate `T.letterRep n g *ᵥ h`, and the linear forms `l i` are applied in all
copies `i ≠ j`. The result is a vector, indexed by `β`, of polynomials in the entries of the copy
`j`. -/
def contractOtherCopies (r ℓ : ℕ) (l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O))
    (j : ZMod N) (g : GL (Fin k) W) (h : Exponents N k n → O) (β : Exponents N k n) :
    MvPolynomial (Fin k × Fin k) O :=
  ∑ γ : Exponents N k n, (T.letterRep n g *ᵥ h) γ •
    tensorDualExcept l j (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g) β γ)

/-- Let `g` be block diagonal with blocks of sizes `r` and `k - r`, and let each `l i` be invariant
under `X ↦ g⁻¹ X g` through `T.embedding i` (`conjSubst`). Then a form `m` applied to the entries of
`T.contractOtherCopies r ℓ l j g h` gives the translate by `g` of `T.frobContraction n r ℓ l' *ᵥ h`,
where `l'` is `l` with `l j` replaced by `m` composed with the conjugation. -/
lemma map_contractOtherCopies {r ℓ : ℕ} {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    {j : ZMod N} {g : GL (Fin k) W} (hg : g ∈ levi W (twoBlock k r))
    (hl : ∀ (i : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O),
      l i (conjSubst (T.embedding i) g ψ) = l i ψ)
    (m : Dual O (MvPolynomial (Fin k × Fin k) O)) (h : Exponents N k n → O) (β : Exponents N k n) :
    m (T.contractOtherCopies r ℓ l j g h β) =
      (T.letterRep n g *ᵥ T.frobContraction n r ℓ
        (update l j (m ∘ₗ (conjSubst (T.embedding j) g).toLinearMap)) *ᵥ h) β := by
  have h_update (i : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O) :
      update l j (m ∘ₗ (conjSubst (T.embedding j) g).toLinearMap) i ψ =
        update l j m i (conjSubst (T.embedding i) g ψ) := by
    obtain rfl | hi := eq_or_ne i j
    · rw [update_self, update_self, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    · rw [update_of_ne hi, update_of_ne hi, hl i]
  rw [mulVec_mulVec, T.letterRep_mul_frobContraction hg h_update, ← mulVec_mulVec,
    contractOtherCopies, linearMap_map_sum, mulVec, dotProduct]
  refine sum_congr rfl fun γ _ ↦ ?_
  rw [LinearMap.map_smul, map_tensorDualExcept, smul_eq_mul, Matrix.map_apply, mul_comm]

/-- The entries of `T.contractOtherCopies r ℓ l j 1 h` are the polynomials in the `j`-th generic
matrix that are left when the forms `l i` are applied in the others. A form `m` applied to them
gives `T.frobContraction`, with `m` at the place `j` and `l i` at the others, applied to `h`. -/
lemma map_contractOtherCopies_one {r ℓ : ℕ} {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    {j : ZMod N} (m : Dual O (MvPolynomial (Fin k × Fin k) O)) (h : Exponents N k n → O)
    (β : Exponents N k n) :
    m (T.contractOtherCopies r ℓ l j 1 h β) = (T.frobContraction n r ℓ (update l j m) *ᵥ h) β := by
  rw [contractOtherCopies, conjFrobGenericMatrix_one, MonoidHom.map_one, one_mulVec,
    linearMap_map_sum, frobContraction, mulVec, dotProduct]
  refine sum_congr rfl fun γ _ ↦ ?_
  rw [LinearMap.map_smul, map_tensorDualExcept, smul_eq_mul, Matrix.map_apply, mul_comm]

/-- Change of basis. Let `F_g = T.contractOtherCopies r ℓ l j g h` be the vector of polynomials in
one generic matrix `X` that arises by substituting `N` generic matrices, in the basis given by `g`,
in the translate of `h` by `g`, and applying the linear forms `l i` in all of them but the `j`-th.
Let `g` be block diagonal with blocks of sizes `r` and `k - r`, and let each `l i` be invariant
under `X ↦ g⁻¹ X g` through `T.embedding i` (`conjSubst`). Then `F_1(g⁻¹ X g)`, with the conjugation
through `T.embedding j`, is the translate of `F_g(X)` by `g⁻¹`. -/
lemma conjSubst_contractOtherCopies_one {r ℓ : ℕ}
    {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)} {j : ZMod N} {g : GL (Fin k) W}
    (hg : g ∈ levi W (twoBlock k r))
    (hl : ∀ (i : ZMod N) (ψ : MvPolynomial (Fin k × Fin k) O),
      l i (conjSubst (T.embedding i) g ψ) = l i ψ)
    (h : Exponents N k n → O) (γ : Exponents N k n) :
    conjSubst (T.embedding j) g (T.contractOtherCopies r ℓ l j 1 h γ) =
      ∑ β : Exponents N k n, T.letterRep n g⁻¹ γ β • T.contractOtherCopies r ℓ l j g h β := by
  ext α
  let v : Exponents N k n → O := T.frobContraction n r ℓ
    (update l j (lcoeff O α ∘ₗ (conjSubst (T.embedding j) g).toLinearMap)) *ᵥ h
  have h_frame (β : Exponents N k n) :
      (T.contractOtherCopies r ℓ l j g h β).coeff α = (T.letterRep n g *ᵥ v) β :=
    T.map_contractOtherCopies hg hl (lcoeff O α) h β
  have h_lhs : (conjSubst (T.embedding j) g (T.contractOtherCopies r ℓ l j 1 h γ)).coeff α = v γ :=
    T.map_contractOtherCopies_one (lcoeff O α ∘ₗ (conjSubst (T.embedding j) g).toLinearMap) h γ
  have h_mul : (T.letterRep n g⁻¹ *ᵥ T.letterRep n g *ᵥ v) γ = v γ := by
    rw [mulVec_mulVec, ← MonoidHom.map_mul, inv_mul_cancel, MonoidHom.map_one, one_mulVec]
  rw [h_lhs, ← h_mul, coeff_sum, mulVec, dotProduct]
  refine sum_congr rfl fun β _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, h_frame]

/-- Each polynomial `T.contractOtherCopies r ℓ l j 1 h β`, which is left in the `j`-th generic
matrix when the forms `l i` are applied in the others, has total degree at most
`N n k (ℓ + 2) P ^ ℓ`. -/
lemma contractOtherCopies_one_mem_restrictTotalDegree {r ℓ : ℕ}
    {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)} {j : ZMod N} (h : Exponents N k n → O)
    (β : Exponents N k n) :
    T.contractOtherCopies r ℓ l j 1 h β ∈
      restrictTotalDegree (Fin k × Fin k) O (N * n * k * (ℓ + 2) * T.P ^ ℓ) := by
  rw [contractOtherCopies, conjFrobGenericMatrix_one]
  exact Submodule.sum_mem _ fun γ _ ↦ Submodule.smul_mem _ _ <|
    tensorDualExcept_mem_restrictTotalDegree l j fun _ hν ↦
      T.degree_le_of_coeff_substitutionOperator hν j

/-- Weight and defect in one copy. Let `T` be a Frobenius cycle (`P = T.P`, `w = T.sqrtPrime`,
`w ^ 2 = p`) from a local ring `W` to a domain
`O` of characteristic `0` in which `p` is not a unit. Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and
`ℓ ≤ N`. Let each linear form `l i` be invariant under conjugation, through `T.embedding i`, by the
Levi subgroup of the blocks of sizes `r` and `k - r`. Let `β` be a monomial of degree `n` in each
letter. The polynomial `T.contractOtherCopies r ℓ l j g h β` in one generic matrix is the entry `β`
of the vector obtained from `T.letterRep n g *ᵥ h` by substituting the `N` generic matrices
conjugated by `g` and applying the `l i` in all of them but the `j`-th. Let its coefficient of `α`
not be divisible by `w ^ c`. Then the row weight of `α` (its degree in the row `r` minus its degree
in the row `a`), divided by `P ^ ℓ`, is within `defectThreshold k c = 3 k c` of the defect of `β` at
the letter `j + ℓ`. The defect is a weighted sum over all letters of the degrees of `β` in the
variables `a` and `r`, with the real weights `T.defectWeight (j + ℓ) a r`; `exponentOf β` is `β` as
one exponent vector. -/
lemma abs_weight_div_sub_defect_le [IsDomain O] [CharZero O] {a r : Fin k} {ℓ c : ℕ}
    (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.val) (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ)
    (hℓ : ℓ ≤ N) {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hl : ∀ i : ZMod N, ∀ u ∈ levi W (twoBlock k r), ∀ ψ : MvPolynomial (Fin k × Fin k) O,
      l i (conjSubst (T.embedding i) u ψ) = l i ψ)
    {j : ZMod N} {g : GL (Fin k) W} {h : Exponents N k n → O} {β : Exponents N k n}
    {α : Fin k × Fin k →₀ ℕ}
    (h_coeff : ¬T.sqrtPrime ^ c ∣ (T.contractOtherCopies r ℓ l j g h β).coeff α) :
    |(α.weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) : ℤ) / (T.P : ℝ) ^ ℓ -
      (exponentOf β).weight (T.defectWeight (j + ℓ) a r)| ≤ defectThreshold k c := by
  -- Some monomial `ν` in all copies, with the part `α` in the copy `j`, has a coefficient that is
  -- not divisible by `w ^ c`, and for `i ≠ j` no `l i` kills its part in the copy `i`.
  obtain ⟨γ, hγ⟩ : ∃ γ : Exponents N k n, ¬T.sqrtPrime ^ c ∣ (tensorDualExcept l j
      (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g) β γ)).coeff α := by
    contrapose! h_coeff with h_all
    rw [contractOtherCopies, coeff_sum]
    refine dvd_sum fun γ _ ↦ ?_
    rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    exact (h_all γ).mul_left _
  obtain ⟨ν, rfl, hν, h_ne_zero⟩ : ∃ ν : ZMod N × Fin k × Fin k →₀ ℕ, ν.curry j = α ∧
      ¬T.sqrtPrime ^ c ∣ (T.substitutionOperator r ℓ n (T.conjFrobGenericMatrix g) β γ).coeff ν ∧
      ∀ i ≠ j, l i (monomial (ν.curry i) 1) ≠ 0 := exists_of_not_dvd_coeff_tensorDualExcept hγ
  -- An invariant form kills the monomials whose row and column weights differ, so the copies
  -- `i ≠ j` contribute nothing to the weight of `ν`.
  have h_balanced (i : ZMod N) (hi : i ∈ univ.erase j) :
      (ν.curry i).weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) =
        (ν.curry i).weight (fun v : Fin k × Fin k ↦ rootVector a r v.2) := by
    by_contra h_ne
    exact h_ne_zero i (ne_of_mem_erase hi) (apply_monomial_eq_zero_of_weight_ne (twoBlock k r)
      (T.embedding i) T.prime.pos hp (rootVector a r) (hl i) h_ne)
  have h_weight : T.copyWeight ℓ a r j ν =
      ((ν.curry j).weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) : ℤ) / T.P ^ ℓ := by
    rw [copyWeight,
      Finset.sum_eq_zero fun i hi ↦ by rw [h_balanced i hi, sub_self, mul_zero], add_zero]
  rw [← h_weight, abs_sub_comm]
  exact T.abs_defect_sub_copyWeight_le ha j h_size hℓ g hν

/-- Let `T` be a Frobenius cycle from a local ring `W` to a domain `O` of characteristic `0` in
which `p` is not a unit. Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and `ℓ ≤ N`. Let each linear form
`l i` be invariant under conjugation, through `T.embedding i`, by the Levi subgroup of the blocks of
sizes `r` and `k - r`. Let `β` be a monomial of degree `n` in each letter. The polynomial
`T.contractOtherCopies r ℓ l j g h β` in one generic matrix is the entry `β` of the vector obtained
from `T.letterRep n g *ᵥ h` by substituting the `N` generic matrices conjugated by `g` and applying
the `l i` in all of them but the `j`-th. Let its coefficient of `α` not be divisible by `w ^ c`, and
put `c* = 3 k c`. The row weight of `α` is its degree in the row `r` minus its degree in the row
`a`, and the defect of `β` at the letter `j + ℓ` is its weighted degree for the weights
`T.defectWeight (j + ℓ) a r`. If the defect is above `3 c*`, then the row weight is above
`2 c* P ^ ℓ`; if the row weight is above `2 c* P ^ ℓ`, then the defect is above `c*`. -/
lemma lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies [IsDomain O] [CharZero O]
    {a r : Fin k} {ℓ c : ℕ} (hp : ¬IsUnit (T.p : O))
    (ha : a + 1 = r.val) (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ : ℓ ≤ N)
    {l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hl : ∀ i : ZMod N, ∀ u ∈ levi W (twoBlock k r), ∀ ψ : MvPolynomial (Fin k × Fin k) O,
      l i (conjSubst (T.embedding i) u ψ) = l i ψ)
    {j : ZMod N} {g : GL (Fin k) W} {h : Exponents N k n → O} {β : Exponents N k n}
    {α : Fin k × Fin k →₀ ℕ}
    (h_coeff : ¬T.sqrtPrime ^ c ∣ (T.contractOtherCopies r ℓ l j g h β).coeff α) :
    (3 * defectThreshold k c < (exponentOf β).weight (T.defectWeight (j + ℓ) a r) →
      2 * defectThreshold k c * (T.P : ℤ) ^ ℓ <
        α.weight (fun v : Fin k × Fin k ↦ rootVector a r v.1)) ∧
    (2 * defectThreshold k c * (T.P : ℤ) ^ ℓ <
        α.weight (fun v : Fin k × Fin k ↦ rootVector a r v.1) →
      defectThreshold k c < (exponentOf β).weight (T.defectWeight (j + ℓ) a r)) := by
  set wt : ℤ := α.weight fun v : Fin k × Fin k ↦ rootVector a r v.1
  have h_bad_iff : 2 * defectThreshold k c * (T.P : ℤ) ^ ℓ < wt ↔
      2 * defectThreshold k c < wt / (T.P : ℝ) ^ ℓ := by
    rw [lt_div_iff₀ (pow_pos (zero_lt_one.trans T.one_lt_P) ℓ), ← Int.cast_lt (R := ℝ),
      Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast, Int.cast_ofNat]
  obtain ⟨h_lower, h_upper⟩ :=
    abs_le.1 (T.abs_weight_div_sub_defect_le hp ha h_size hℓ hl h_coeff)
  rw [h_bad_iff]
  have h3 : (3 : ℝ) * defectThreshold k c = 2 * defectThreshold k c + defectThreshold k c := by
    rw [← Nat.cast_ofNat (n := 3), show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one, add_mul, one_mul]
  refine ⟨fun h1 ↦ lt_of_add_lt_add_right (a := (defectThreshold k c : ℝ)) ?_,
    fun h2 ↦ lt_of_add_lt_add_left (a := (defectThreshold k c : ℝ)) ?_⟩
  · rw [← h3]
    exact h1.trans_le (neg_le_sub_iff_le_add.1 h_lower)
  · rw [← two_mul]
    exact h2.trans_le (sub_le_iff_le_add.1 h_upper)

/-! ### The averaging map -/

/-- The map `Av_J`: the substitution `T.substitutionOperator` at generic matrices, one for each
letter, is applied, then the forms `I j` (averages, in the applications) in the copies `j ∈ J` and
`p ^ c₀` times the evaluation at the identity matrix in the other copies,
`c₀ = T.multinomialExponent k`. -/
def partialAverage (n r ℓ : ℕ) (I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O))
    (J : Finset (ZMod N)) : Matrix (Exponents N k n) (Exponents N k n) O :=
  T.frobContraction n r ℓ
    (J.piecewise I fun _ : ZMod N ↦ evalAtOne ((T.p : O) ^ T.multinomialExponent k))

/-- With no average, the map `Av_∅` is `p ^ (N c₀)` times the identity, where
`c₀ = T.multinomialExponent k`. -/
lemma partialAverage_empty {ℓ : ℕ} (r : ℕ) (I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)) :
    T.partialAverage n r ℓ I ∅ = (T.p : O) ^ (N * T.multinomialExponent k) • 1 := by
  rw [partialAverage, piecewise_empty, frobContraction_evalAtOne, ← pow_mul, mul_comm]

/-- Let `T` be a Frobenius cycle over a domain `O` of characteristic `0` in which `p` is not a unit.
Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and `ℓ ≤ N`, and put `c* = 3 k c`. Let the `I j` be
averages; they are linear forms on polynomials in a generic matrix, invariant under the Levi
subgroup of the blocks of sizes `r` and `k - r`, that vanish on the monomials of row weight above
`2 c* P ^ ℓ`. Let `Av = T.partialAverage n r ℓ I univ` be the matrix obtained from the substitution
of `N` generic matrices by applying `I j` in the `j`-th one for every `j`. Then for every
coefficient vector `h`, `w ^ c` divides the coefficient in each Levi translate of `Av h` of each
monomial with defect above `3 c*` at some letter; the defect is the weighted degree for
`T.defectWeight`. -/
lemma partialAverage_univ_mulVec_mem_defectConditions [IsDomain O] [CharZero O] {a r : Fin k}
    {ℓ c : ℕ} (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.val)
    (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ : ℓ ≤ N) {D : ℕ}
    {I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hI : ∀ j : ZMod N, IsAverage (twoBlock k r) (T.embedding j) (rootVector a r)
      (2 * defectThreshold k c * T.P ^ ℓ) ((T.p : O) ^ T.multinomialExponent k) D (I j))
    (h : Exponents N k n → O) :
    T.partialAverage n r ℓ I univ *ᵥ h ∈
      T.defectConditions n a r (span {T.sqrtPrime ^ c}) (3 * defectThreshold k c) := by
  rintro g hg β ⟨i, h_defect⟩
  obtain ⟨j, rfl⟩ : ∃ j : ZMod N, j + ℓ = i := ⟨i - ℓ, sub_add_cancel i ℓ⟩
  -- The translate by `g` is `I j` applied to the polynomial that remains in the copy `j`.
  have h_invariant : I j ∘ₗ (conjSubst (T.embedding j) g).toLinearMap = I j :=
    LinearMap.ext ((hI j).map_conjSubst g hg)
  have h_value : (T.letterRep n g *ᵥ T.partialAverage n r ℓ I univ *ᵥ h) β =
      I j (T.contractOtherCopies r ℓ I j g h β) := by
    rw [T.map_contractOtherCopies hg fun i ↦ (hI i).map_conjSubst g hg, h_invariant, update_eq_self,
      partialAverage, piecewise_univ]
  rw [mem_span_singleton, h_value]
  -- Modulo `w ^ c` this polynomial has only bad monomials, on which `I j` vanishes.
  refine dvd_map_of_forall_monomial fun α h_coeff ↦ (hI j).map_monomial_eq_zero α ?_
  exact (T.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies hp ha h_size hℓ
    (fun i ↦ (hI i).map_conjSubst) h_coeff).1 h_defect

/-- Let `T` be a Frobenius cycle over a valuation domain `O` of characteristic `0` in which `p` is
not a unit. Let `r = a + 1`, `N n k (ℓ + 2) ≤ P ^ ℓ` and `ℓ ≤ N`, and put `c* = 3 k c` and
`c₀ = T.multinomialExponent k`. Let the `I j` be averages up to the degree `N n k (ℓ + 2) P ^ ℓ`,
whose bad monomials are those of row weight above `2 c* P ^ ℓ`. The matrix
`Av_J = T.partialAverage n r ℓ I J` arises from the substitution of `N` generic matrices by applying
`I i` in the `i`-th one for `i ∈ J`, and `p ^ c₀` times the evaluation at `1` for `i ∉ J`. Let the
weights `b` define a pairing `⟨h, h'⟩ = ∑_β h'_β b_β h_β` that makes the matrices of `g` and `gᵀ`
adjoint, with `b b' = p ^ (N c₀)`. Let `h' ∈ T.allEdgesForms k n r`: it is `w ^ (-m) Δ f` for a
vector `f` over `O` with `w ^ (-m) Δ g f` integral for all `g ∈ GL_k(W)`, where
`Δ = T.depthScaling k n r` is a diagonal matrix of powers of `w`. Then
`⟨Av_{J ∪ {j}} h, h'⟩ ≡ ⟨Av_J h, h'⟩` modulo `w ^ c` for `j ∉ J`. -/
lemma pow_dvd_pairing_partialAverage_insert_sub [IsDomain O] [CharZero O] {a r : Fin k} {ℓ c : ℕ}
    (hp : ¬IsUnit (T.p : O))
    (ha : a + 1 = r.val) (h_size : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ) (hℓ : ℓ ≤ N)
    {I : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hI : ∀ j : ZMod N, IsAverage (twoBlock k r) (T.embedding j) (rootVector a r)
      (2 * defectThreshold k c * T.P ^ ℓ) ((T.p : O) ^ T.multinomialExponent k)
      (N * n * k * (ℓ + 2) * T.P ^ ℓ) (I j))
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') {J : Finset (ZMod N)} {j : ZMod N}
    (hj : j ∉ J) (h : Exponents N k n → O) {h' : Exponents N k n → O}
    (hh' : h' ∈ T.allEdgesForms k n r) :
    T.sqrtPrime ^ c ∣ h' ⬝ᵥ (b * T.partialAverage n r ℓ I (insert j J) *ᵥ h) -
      h' ⬝ᵥ (b * T.partialAverage n r ℓ I J *ᵥ h) := by
  -- The difference is `(I j - ev) ψ` for the pairing `ψ` of `h'` with the polynomials that remain
  -- in the copy `j`. It is enough to show that the bad monomials of the conjugates of `ψ` have
  -- coefficients divisible by `w ^ c`.
  let ev : Dual O (MvPolynomial (Fin k × Fin k) O) :=
    evalAtOne ((T.p : O) ^ T.multinomialExponent k)
  let l : ZMod N → Dual O (MvPolynomial (Fin k × Fin k) O) := J.piecewise I fun _ ↦ ev
  have hl (i : ZMod N) (u : GL (Fin k) W) (hu : u ∈ levi W (twoBlock k r))
      (φ : MvPolynomial (Fin k × Fin k) O) : l i (conjSubst (T.embedding i) u φ) = l i φ := by
    dsimp only [l]
    by_cases hi : i ∈ J
    · rw [piecewise_eq_of_mem J I _ hi, (hI i).map_conjSubst u hu]
    · rw [piecewise_eq_of_notMem J I _ hi, evalAtOne_conjSubst]
  let ψ : MvPolynomial (Fin k × Fin k) O :=
    ∑ β : Exponents N k n, (h' β * b β) • T.contractOtherCopies r ℓ l j 1 h β
  have hψ (m : Dual O (MvPolynomial (Fin k × Fin k) O)) :
      m ψ = h' ⬝ᵥ (b * T.frobContraction n r ℓ (update l j m) *ᵥ h) := by
    rw [linearMap_map_sum, dotProduct]
    refine sum_congr rfl fun β _ ↦ ?_
    rw [LinearMap.map_smul, smul_eq_mul, T.map_contractOtherCopies_one, Pi.mul_apply, mul_assoc]
  have h_degree : ψ.totalDegree ≤ N * n * k * (ℓ + 2) * T.P ^ ℓ := (mem_restrictTotalDegree ..).1 <|
    sum_mem fun β _ ↦ Submodule.smul_mem _ _ (T.contractOtherCopies_one_mem_restrictTotalDegree h β)
  have h_update_ev : update l j ev = l :=
    update_eq_self_iff.2 (piecewise_eq_of_notMem J I (fun _ ↦ ev) hj).symm
  suffices h_mem : I j ψ - ev ψ ∈ span {T.sqrtPrime ^ c} by
    rwa [hψ, hψ, h_update_ev, mem_span_singleton, ← piecewise_insert] at h_mem
  refine (hI j).sub_evalAtOne_mem (span {T.sqrtPrime ^ c}) ψ h_degree fun g hg α h_bad ↦ ?_
  -- The coefficient of `α` in the conjugate of `ψ` is a combination of the pairings of `h'` with
  -- the translates by `g⁻¹` of the monomials `β`. The scalars are coefficients of
  -- `contractOtherCopies` in the frame `g`.
  have h_coeff : (conjSubst (T.embedding j) g ψ).coeff α = ∑ β : Exponents N k n,
      (T.contractOtherCopies r ℓ l j g h β).coeff α *
        h' ⬝ᵥ (b * T.letterRep n g⁻¹ *ᵥ Pi.single β 1) := by
    have h_lhs : (conjSubst (T.embedding j) g ψ).coeff α =
        ∑ γ : Exponents N k n, ∑ β : Exponents N k n,
          (h' γ * b γ) * (T.letterRep n g⁻¹ γ β *
            (T.contractOtherCopies r ℓ l j g h β).coeff α) := by
      rw [algHom_map_sum, coeff_sum]
      refine sum_congr rfl fun γ _ ↦ ?_
      rw [algHom_map_smul, T.conjSubst_contractOtherCopies_one hg fun i ↦ hl i g hg,
        AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeff_sum, mul_sum]
      refine sum_congr rfl fun β _ ↦ ?_
      rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rw [h_lhs, sum_comm]
    refine sum_congr rfl fun β _ ↦ ?_
    rw [mulVec_single_one, dotProduct, mul_sum]
    refine sum_congr rfl fun γ _ ↦ ?_
    rw [Pi.mul_apply, col_apply, ← mul_assoc,
      mul_comm _ ((T.contractOtherCopies r ℓ l j g h β).coeff α), mul_assoc]
  rw [mem_span_singleton, h_coeff]
  refine dvd_sum fun β _ ↦ ?_
  by_cases h_dvd : T.sqrtPrime ^ c ∣ (T.contractOtherCopies r ℓ l j g h β).coeff α
  · exact h_dvd.mul_right _
  · -- As `α` is bad, the defect of `β` is large, so the pairing is divisible by `w ^ c`.
    have h_defect : defectThreshold k c < (exponentOf β).weight (T.defectWeight (j + ℓ) a r) :=
      (T.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies hp ha h_size hℓ hl
        h_dvd).2 h_bad
    have h_lt : a < r := Fin.lt_def.2 (ha ▸ Nat.lt_succ_self a.val)
    exact (hb.pow_dvd_pairing_letterRep T h_lt hh' (inv_mem hg) h_defect).mul_left _

/-- The averaging map. Let `T` be a Frobenius cycle (`P = T.P`, `w = T.sqrtPrime`, `w ^ 2 = p`)
over a valuation domain `O` of characteristic
`0` in which `p` is not a unit. Vectors are coefficient vectors of polynomials of degree `n` in each
of `N` groups of `k` variables, on which `GL_k(W)` acts by `T.letterRep n`. Let `r = a + 1`,
`N = 2 ℓ` and `N k (ℓ + 2) n + n + k < P ^ ℓ`. Put `c* = 3 k c` and
`c₀ = T.multinomialExponent k = k² log_p P^N`. Let the weights `b` define a pairing
`⟨h, h'⟩ = ∑_β h'_β b_β h_β` that makes the matrices of `g` and `gᵀ` adjoint, with
`b b' = p ^ (N c₀)`. For every `c` there is a matrix `Av` with two properties.
* For all `h` and all `g` in the Levi subgroup of the blocks of sizes `r` and `k - r`, `w ^ c`
  divides the coefficient in `g Av h` of each monomial with defect above `3 c*` at some letter `i`;
  the defect is the weighted degree for the weights `T.defectWeight i a r`.
* `⟨Av h, h'⟩ ≡ p ^ (N c₀) ⟨h, h'⟩` modulo `w ^ c` for all `h` and all
  `h' ∈ T.allEdgesForms k n r`. -/
theorem exists_average_mem_defectConditions_and_dvd_sub [IsDomain O] [CharZero O] {a r : Fin k}
    [ValuationRing O] (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.val) {ℓ : ℕ}
    (hℓ : ℓ + ℓ = N) (h_size : N * k * (ℓ + 2) * n + n + k < T.P ^ ℓ)
    {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') (c : ℕ) :
    ∃ Av : Matrix (Exponents N k n) (Exponents N k n) O,
      (∀ h : Exponents N k n → O,
        Av *ᵥ h ∈ T.defectConditions n a r (span {T.sqrtPrime ^ c}) (3 * defectThreshold k c)) ∧
      ∀ (h : Exponents N k n → O), ∀ h' ∈ T.allEdgesForms k n r,
        T.sqrtPrime ^ c ∣ h' ⬝ᵥ (b * Av *ᵥ h) -
          (T.p : O) ^ (N * T.multinomialExponent k) * h' ⬝ᵥ (b * h) := by
  have h_eq : N * n * k * (ℓ + 2) = N * k * (ℓ + 2) * n := by
    rw [mul_right_comm N n k, mul_right_comm (N * k) n (ℓ + 2)]
  have h_small : N * n * k * (ℓ + 2) ≤ T.P ^ ℓ := by
    rw [h_eq]
    exact ((Nat.le_add_right _ n).trans (Nat.le_add_right _ k)).trans h_size.le
  have hℓ_le : ℓ ≤ N := hℓ ▸ Nat.le_add_right ℓ ℓ
  -- `D` bounds the degree in one copy; it is small against `P ^ N`, so the averages exist.
  let D : ℕ := N * n * k * (ℓ + 2) * T.P ^ ℓ
  have hD : D + k < T.P ^ N := by
    have h1 : D + k < (N * k * (ℓ + 2) * n + 1) * T.P ^ ℓ := by
      rw [add_mul, one_mul, ← h_eq]
      exact Nat.add_lt_add_left ((Nat.le_add_left k _).trans_lt h_size) D
    have h2 : (N * k * (ℓ + 2) * n + 1) * T.P ^ ℓ ≤ T.P ^ N :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt
        (((Nat.le_add_right _ n).trans (Nat.le_add_right _ k)).trans_lt h_size))).trans_eq
        (by rw [← pow_add, hℓ])
    exact h1.trans_le h2
  have hD_pow : D < T.p ^ (T.frobExp * N) := by
    rw [pow_mul]
    exact (Nat.le_add_right D k).trans_lt hD
  have h_exists (j : ZMod N) : ∃ I : Dual O (MvPolynomial (Fin k × Fin k) O),
      IsAverage (twoBlock k r) (T.embedding j) (rootVector a r) (2 * defectThreshold k c * T.P ^ ℓ)
        ((T.p : O) ^ T.multinomialExponent k) D I :=
    exists_isAverage (twoBlock k r) (T.embedding j) T.prime hp (T.frobExp * N) hD_pow
      (hD.le.trans_eq T.card_residueField.symm) _ _
  choose I hI using h_exists
  refine ⟨T.partialAverage n r ℓ I univ,
    T.partialAverage_univ_mulVec_mem_defectConditions hp ha h_small hℓ_le hI, fun h h' hh' ↦ ?_⟩
  -- Add the differences along a chain of subsets that starts at `∅`.
  have h_chain (J : Finset (ZMod N)) :
      T.sqrtPrime ^ c ∣ h' ⬝ᵥ (b * T.partialAverage n r ℓ I J *ᵥ h) -
        (T.p : O) ^ (N * T.multinomialExponent k) * h' ⬝ᵥ (b * h) := by
    induction J using Finset.induction_on with
    | empty =>
      rw [partialAverage_empty, smul_mulVec, one_mulVec, mul_smul_comm, dotProduct_smul,
        smul_eq_mul, sub_self]
      exact dvd_zero _
    | insert j J hj ih =>
      have h_add := dvd_add
        (T.pow_dvd_pairing_partialAverage_insert_sub hp ha h_small hℓ_le hI hb hj h hh') ih
      rwa [sub_add_sub_cancel] at h_add
  exact h_chain univ

end FrobeniusCycle

end New

end
