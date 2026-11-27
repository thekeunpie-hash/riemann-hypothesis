module

import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Order.Grade
public import Lib.GLn.SchurModule.Basic
public import TauCeti.RingTheory.MvPolynomial.HasLeadingTerm
import Mathlib.Algebra.Order.Ring.Opposite
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Finset.Slice
import Lib.General.Groups.CongruenceSubgroups

section
/-!
# A basis of minor products for Borel semi-invariants over any ring, by induction on rows

Polynomials are in variables `X (a, i)`, where `a` is a row with colour `c a` and `i : ℕ` is a
column (`New.MatrixPoly`). For finitely many rows and `l = New.GL.columnWeight τ h`, the module
`New.nabla R c l` of Borel semi-invariants has a basis of products of minors that does not depend on
the ring `R`. The proof takes leading terms in one row: bordering lifts a family of minor products,
and a leading-term analysis describes the leading term of a semi-invariant.

## Main definitions and results

* Leading terms are Tau Ceti's `MonomialOrder.HasLeadingTerm` for `New.GL.columnOrder`;
  `New.GL.rowExpansion x` expands in row `x`.
* `New.GL.columnWeight`, `New.GL.ColoredTableau`, `New.GL.minorProduct`: the weight of a family of
  coloured columns, its fillings by rows, and the product of the minors of a filling.
* `New.GL.interlacing l`: the exponents `γ` with `γ i ≤ l i - l (i + 1)` (truncated subtraction).
  For antitone `l`, these are the `γ ≤ l` such that `l - γ` interlaces `l`.
* `New.GL.exists_bordering`: a filling that avoids `x` is lifted to one whose product of minors has,
  in the variables of row `x`, leading term `X ^ γ` times the old product.
* `New.GL.degree_rowExpansion_mem_interlacing`: the leading exponent of a Borel semi-invariant in
  the variables of one row `x` lies in `New.GL.interlacing` of its weight at the colour of `x`.
* `New.GL.HasLeadingTerm.leadingCoeff_mem_nabla`: the leading coefficient of a semi-invariant in row
  `x` is a semi-invariant in the other rows, of the weight lowered by that exponent.
* `New.GL.exists_isStdMinorFamily`: some finite family of fillings has products of minors that are
  linearly independent and span the semi-invariants of its weight over every ring, recorded as
  `New.GL.IsStdMinorFamily`.

Notions from other files:
* `New.nabla`: For a row colouring c and weight l, the module of Borel semi-invariants: polynomials
  f with f(yβ) = ∏β_{τ,ii}^{l(τ,i)} f(y) for generic upper triangular matrices β_τ, one per colour.
* `New.minor`: For an h-tuple I of rows, the polynomial determinant of the h×h matrix of variables
  in rows I and the first h columns.
* `New.GL.alternant`: For x in ℂ^N and l : ℕ → ℕ, the alternant det(x_i^{l(N−1−j)+j}), 0 ≤ i, j < N,
  if l(N) = 0, and zero otherwise.

## Relation to the literature

Known result: The standard basis theorem for Schur (dual Weyl) modules over any ring, with their
character. Here the module is the space of polynomials on matrices that are semi-invariant under a
triangular group, for several row colours at once. It lies in the span of a set of products of
minors built one row at a time rather than the semistandard tableaux, and this set is linearly
independent over every ring. For a single colour its character is given by Weyl's quotient of
alternants. Source: De Concini, Eisenbud, Procesi, Young diagrams and determinantal varieties,
Invent. Math. 56 (1980); Akin, Buchsbaum, Weyman, Schur functors and Schur complexes, Adv. Math. 44
(1982), II.2.16, II.4.11.

See also `Lib.DiscreteSeries.Character.WeylCharacterFormula`.
-/

@[expose] public section

noncomputable section

/-! ## Leading terms of products of minors and bordering -/

section Bordering

open MvPolynomial Finset MonomialOrder Finsupp Matrix Fin

namespace New.GL

variable {Φ J m R : Type} [DecidableEq m] [CommRing R] {γ : ℕ →₀ ℕ}

/-! ### Leading terms -/

/-- The lexicographic monomial order on variables indexed by ℕ that compares exponents at the
highest index first, so that x₀ ≺ x₁ ≺ …. -/
def columnOrder : MonomialOrder ℕ := lex (σ := ℕᵒᵈ)

/-- If the exponents `γ` and `δ` agree in the columns beyond `i` and `γ i < δ i`, then `γ` is
below `δ` in `New.GL.columnOrder`. -/
lemma columnOrder_lt_of_eq_above {γ : ℕ →₀ ℕ} (i : ℕ) (δ : ℕ →₀ ℕ) (h_eq : ∀ j > i, γ j = δ j)
    (h_lt : γ i < δ i) : γ ≺[columnOrder] δ :=
  ⟨OrderDual.toDual i, h_eq, h_lt⟩

/-- If each `u j` has leading term `b j` times the variable `x j` (exponent `single j 1`),
then the product of the powers `u j ^ n j` has leading term `∏ b j ^ n j` times the monomial of
exponent `n`. -/
lemma HasLeadingTerm.finsuppProd_pow {u : ℕ → MvPolynomial ℕ R} {b : ℕ → R}
    (hu_lead : ∀ j : ℕ, columnOrder.HasLeadingTerm (u j) (Finsupp.single j 1) (b j)) (n : ℕ →₀ ℕ) :
    columnOrder.HasLeadingTerm (n.prod fun j e : ℕ ↦ u j ^ e) n (n.prod fun j e : ℕ ↦ b j ^ e) := by
  have h_pow (j : ℕ) :
      columnOrder.HasLeadingTerm (u j ^ n j) (Finsupp.single j (n j)) (b j ^ n j) := by
    simpa using HasLeadingTerm.prod (s := range (n j)) fun _ _ ↦ hu_lead j
  have h_sum_single : ∑ j ∈ n.support, Finsupp.single j (n j) = n := n.sum_single
  simpa only [Finsupp.prod, h_sum_single] using
    HasLeadingTerm.prod (s := n.support) fun j _ ↦ h_pow j

variable [Fintype J] {c : m → Φ} {τ : J → Φ} {h : J → ℕ} {x : m} (l : ℕ →₀ ℕ)

/-! ### Columns, fillings and products of minors -/

/-- For a row x, the R-algebra isomorphism writing a polynomial in the y_{a,i} as a polynomial
in the y_{x,i}, i ∈ ℕ, over the polynomials in the other rows. -/
def rowExpansion (x : m) : MatrixPoly m R ≃ₐ[R] MvPolynomial ℕ (MatrixPoly {a // a ≠ x} R) :=
  -- split the variables into those of row `x` and the others
  (renameEquiv R (((Equiv.optionSubtypeNe x).symm.prodCongr 1).trans optionProdEquiv)).trans
    (sumAlgEquiv R ℕ ({a // a ≠ x} × ℕ))

/-- The finite set of the `γ` with `γ i ≤ l i - l (i + 1)` (truncated subtraction) for all `i`. For
antitone `l` these are the `γ ≤ l` such that `μ = l - γ` interlaces `l`: `l (i + 1) ≤ μ i ≤ l i`. -/
def interlacing : Finset (ℕ →₀ ℕ) := Icc 0 (l - l.comapDomain Nat.succ (by simp))

lemma mem_interlacing_iff {γ : ℕ →₀ ℕ} : γ ∈ interlacing l ↔ ∀ i : ℕ, γ i ≤ l i - l (i + 1) := by
  simp [interlacing, Finsupp.le_def]

/-- For finitely many columns j with colour τ_j and height h_j, the weight whose value at (τ,i)
counts the columns of colour τ with height exceeding i. -/
def columnWeight (τ : J → Φ) (h : J → ℕ) : Φ × ℕ →₀ ℕ :=
  ∑ j : J, ∑ i ∈ range (h j), Finsupp.single ((τ j : Φ), i) 1

/-- The type of assignments giving each column j an h_j-tuple of rows, all of colour τ_j. -/
abbrev ColoredTableau (c : m → Φ) (τ : J → Φ) (h : J → ℕ) : Type :=
  ∀ j : J, Fin (h j) → {a // c a = τ j}

variable (S : Type) [CommRing S] (I : ColoredTableau c τ h)

/-- For a coloured column filling I, the polynomial over S that is the product over columns j of
the minor with rows I_j on the first h_j columns. -/
def minorProduct : MatrixPoly m S := ∏ j : J, minor S fun s ↦ (I j s).val

/-- The weight `New.diagramWeight N κ` equals the weight `New.GL.columnWeight` of the family having
`κ τ h` columns of colour `τ` and height `h`, for every `τ` and `h < N τ`: its columns are the
triples `⟨τ, h, j⟩` with `j < κ τ h`, of colour `τ` and height `h`. -/
lemma diagramWeight_eq_columnWeight [Fintype Φ] (N : Φ → ℕ) (κ : Φ → ℕ → ℕ) :
    diagramWeight N κ =
      columnWeight (fun j : Σ τ : Φ, Σ h : Fin (N τ), Fin (κ τ h) ↦ j.fst)
        fun j : Σ τ : Φ, Σ h : Fin (N τ), Fin (κ τ h) ↦ (j.snd.fst : ℕ) := by
  -- `↓`: the sums over the sigma type must be split before the definitions unfold
  simp [↓Fintype.sum_sigma, diagramWeight, sum_range, columnWeight]

omit [DecidableEq m] in
/-- For an assignment I of h_j rows of colour τ_j to each column j, the product of minors
`New.GL.minorProduct` of I is a Borel semi-invariant: it lies in `New.nabla` for the weight
`New.GL.columnWeight` of τ, h. -/
lemma minorProduct_mem_nabla : minorProduct R I ∈ nabla R c (columnWeight τ h) := by
  -- each minor is a semi-invariant, and semi-invariants form a graded monoid
  rw [minorProduct, columnWeight]
  apply SetLike.prod_mem_graded
  exact fun j _ ↦ minor_mem_nabla fun s ↦ (I j s).prop

/-- Bordering one minor: take a tuple `I` of `k` rows other than `x` and append the row `x` if
`e = 1`. After `New.GL.rowExpansion x`, the new minor has leading term `X k ^ e` times the old
minor, where `X k` is the variable of row `x` in column `k`. -/
lemma hasLeadingTerm_rowExpansion_minor_border {k e : ℕ} (I : Fin k → {a : m // a ≠ x})
    (he_le_one : e ≤ 1) :
    columnOrder.HasLeadingTerm
      (rowExpansion x (minor S fun s : Fin (k + e) ↦ if hs : s < k then (I ⟨s, hs⟩).val else x))
      (Finsupp.single k e) (minor S I) := by
  interval_cases e
  · -- the minor does not involve row `x`
    have h_const : rowExpansion x (minor S fun s : Fin (k + 0) ↦
        if hs : s < k then (I ⟨s, hs⟩).val else x) = monomial (Finsupp.single k 0) (minor S I) := by
      simp [rowExpansion, (I _).prop, monomial_eq, minor, det_apply']
    rw [h_const]
    exact hasLeadingTerm_monomial _ _
  · -- Expand along the last row: column `s` contributes a cofactor times `X (x, s)`.
    let cofactor (s : Fin (k + 1)) : MatrixPoly {a // a ≠ x} S :=
      (-1) ^ (k + s.val) * det (of fun a t ↦ X (I a, (s.succAbove t).val))
    -- The variable of the last column is the largest.
    have h_lt (s : Fin (k + 1)) (hs : s ≠ last k) :
        Finsupp.single s.val 1 ≺[columnOrder] Finsupp.single k 1 := by
      grind [columnOrder_lt_of_eq_above k]
    have h_expand : rowExpansion x (minor S fun s : Fin (k + 1) ↦
        if hs : s < k then (I ⟨s, hs⟩).val else x) =
          ∑ s : Fin (k + 1), monomial (Finsupp.single s.val 1) (cofactor s) := by
      rw [minor, det_succ_row _ (last k), map_sum]
      refine sum_congr rfl fun s _ ↦ ?_
      simp [cofactor, rowExpansion, (I _).prop, monomial_eq, mul_comm, mul_left_comm,
        mul_assoc, det_apply']
    have h_last : cofactor (last k) = minor S I := by simp [cofactor, minor]
    rw [h_expand, ← h_last]
    exact .sum (γ := fun s : Fin (k + 1) ↦ Finsupp.single s.val 1) (a := cofactor)
      (fun s ↦ hasLeadingTerm_monomial _ _) (last k) (fun s _ ↦ h_lt s) (absurd (mem_univ (last k)))

/-- Bordering. Let `γ` lie in `interlacing` of the weight `l` of the columns at the colour of the
row `x`, that is `γ i ≤ l i - l (i + 1)` for all `i`, so `γ` is the amount by which `l` is lowered
to an interlacing weight. Then (a) there are heights `k` whose column weight is that of `h` minus
`γ` placed in colour `c x`. For every filling `I` of heights `k` by rows other than `x` there is a
filling `K` of heights `h` such that (b) over every commutative ring `R`, the expansion of
`minorProduct R K` in the variables of row `x` has no monomial above the one of exponent `γ` in
`columnOrder`, and the coefficient of that monomial is `minorProduct R I`, and (c) the entries of
`K` are those of `I` together with `degree γ` copies of `x`. -/
lemma exists_bordering (h : J → ℕ) (hγ : γ ∈ interlacing ((columnWeight τ h).curry (c x))) :
    ∃ k : J → ℕ,
      -- (a)
      columnWeight τ h = γ.mapDomain (fun i : ℕ ↦ (c x, i)) + columnWeight τ k ∧
      -- every filling `I` of heights `k` that avoids `x` has a lift `K` of heights `h` such that
      ∀ I : ColoredTableau (c ∘ ((↑) : {a : m // a ≠ x} → m)) τ k, ∃ K : ColoredTableau c τ h,
        -- (b)
        (∀ (R : Type) [CommRing R],
          columnOrder.HasLeadingTerm (rowExpansion x (minorProduct R K)) γ (minorProduct R I)) ∧
        -- (c)
        ∀ y : m → ℂ,
          ∏ j : J, ∏ s : Fin (h j), y (K j s) =
            y x ^ Finsupp.degree γ * ∏ j : J, ∏ s : Fin (k j), y (I j s) := by
  classical
  -- Among the columns of the colour of `x` and of height `i + 1` choose `γ i` and shorten them by
  -- one. A filling `I` of the shortened columns is lifted by putting `x` back at the end.
  let taller (i : ℕ) : Finset J := {j ∈ {j | τ j = c x} | i < h j}
  have h_weight (i : ℕ) : (columnWeight τ h).curry (c x) i = #(taller i) := by
    simp [columnWeight, taller, Finsupp.single_apply, sum_ite, ite_and]
  -- interlacing says that at least `γ i` columns of this colour have height exactly `i + 1`
  have h_count (i : ℕ) : γ i ≤ #(taller i) - #(taller (i + 1)) := by
    simpa only [h_weight] using (mem_interlacing_iff _).mp hγ i
  have h_exists_S (i : ℕ) : ∃ S ⊆ taller i \ taller (i + 1), #S = γ i :=
    exists_subset_card_eq ((h_count i).trans (le_card_sdiff (taller (i + 1)) (taller i)))
  choose S h_S_sub card_S using h_exists_S
  have h_of_mem_S {i : ℕ} {j : J} (hj : j ∈ S i) : τ j = c x ∧ h j = i + 1 := by grind
  clear hγ h_S_sub h_count h_weight taller
  -- `e j = 1` for the chosen columns and `0` for the others; `k` are the new heights.
  let e (j : J) : ℕ := if ∀ i, j ∉ S i then 0 else 1
  have h_e_le_one (j : J) : e j ≤ 1 := by grind
  obtain ⟨k, rfl⟩ : ∃ k : J → ℕ, h = k + e := le_iff_exists_add'.mp (by grind [Pi.le_def])
  -- `γ i` counts the columns chosen at height `i + 1`, which now have height `k j = i`
  have h_γ_eq : γ = ∑ j, Finsupp.single (k j) (e j) := by
    ext i
    have h_chosen (j : J) : (if j ∈ S i then 1 else 0) = Finsupp.single (k j) (e j) i := by
      grind [Pi.add_apply]
    simp [Finsupp.finsetSum_apply, ← h_chosen, card_S, Finset.univ_inter]
  subst h_γ_eq
  refine ⟨k, ?weights, fun I ↦
    ⟨fun j s ↦ ⟨if hs : s < k j then I j ⟨s, hs⟩ else x, ?colour⟩, fun R _ ↦ ?lead, ?entries⟩⟩
  case weights =>
    -- a chosen column loses the entry `(c x, k j)` of its weight
    have h_column (j : J) :
        ∑ i ∈ range (k j + e j), Finsupp.single (τ j, i) 1 =
          Finsupp.single (c x, k j) (e j) + ∑ i ∈ range (k j), Finsupp.single (τ j, i) 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h_e_le_one j) with h_e_zero | h_e_one
      · simp [h_e_zero]
      · have h_colour : τ j = c x := by grind
        rw [h_e_one, sum_range_succ, h_colour, add_comm]
    simp only [columnWeight, mapDomain_finsetSum, mapDomain_single, Pi.add_apply, h_column,
      sum_add_distrib]
  case colour =>
    -- the appended row `x` has the colour of its column
    grind [Pi.add_apply]
  case lead =>
    -- leading terms multiply, column by column
    simp only [minorProduct, map_prod]
    exact .prod fun j ↦ by simpa using hasLeadingTerm_rowExpansion_minor_border R
                             (fun s ↦ (I j s).val) (h_e_le_one j)
  case entries =>
    -- in each column, the lifted filling adds `e j` copies of `x`
    simp [prod_univ_add, mul_comm, prod_mul_distrib, prod_pow_eq_pow_sum]

/-! ### The recursion for alternants -/

/-- Column reduction for a matrix of powers. Let `p` be a monotone family of exponents and `i` a
row. Subtracting from each column `j + 1` the power `x i ^ (p (j + 1) - p j)` times column `j`
keeps the determinant of `(x a ^ p j)`, and turns the entry `x a ^ p (j + 1)` into `x a - x i`
times the sum of `x a ^ k * x i ^ (p (j + 1) - 1 - k)` over `p j ≤ k < p (j + 1)`. -/
lemma _root_.Matrix.det_pow_eq_det_sub_mul_geom_sum {N : ℕ} (x : Fin (N + 1) → R)
    (i : Fin (N + 1)) (p : Fin (N + 1) → ℕ) (h_mono : ∀ j : Fin N, p j.castSucc ≤ p j.succ) :
    det (of fun a j : Fin (N + 1) ↦ x a ^ p j) =
      det (of fun a : Fin (N + 1) ↦ vecCons (x a ^ p 0) fun j : Fin N ↦ (x a - x i) *
        ∑ k ∈ Ico (p j.castSucc) (p j.succ), x a ^ k * x i ^ (p j.succ - 1 - k)) := by
  refine det_eq_of_forall_col_eq_smul_add_pred (fun j ↦ x i ^ (p j.succ - p j.castSucc))
    (fun _ ↦ rfl) fun a j ↦ ?_
  simp only [of_apply, cons_val_succ, mul_geom_sum₂_Ico _ _ (h_mono j)]
  ring

/-- The branching rule for alternants. Here `alternant x l` for `x : Fin (N + 1) → ℂ` is
`det (x a ^ (l (N - j) + j))` over `0 ≤ a, j ≤ N`, or zero if `l (N + 1) ≠ 0`, and `interlacing l`
is the set of `γ` with `γ k ≤ l k - l (k + 1)` for all `k`, so that `l - γ` interlaces `l`. For
antitone `l` and an index `i`, the alternant of `l` is `(-1) ^ i * ∏ a ≠ i, (x a - x i)` times the
sum, over `γ ∈ interlacing l`, of `x i ^ |γ|` times the alternant of `l - γ` in the other `N`
variables. -/
lemma alternant_succ {N : ℕ} (hl_anti : Antitone l) (i : Fin (N + 1)) (x : Fin (N + 1) → ℂ) :
    alternant x l =
      (-1) ^ i.val * (∏ a : Fin N, (x (i.succAbove a) - x i)) *
        ∑ γ ∈ interlacing l, x i ^ Finsupp.degree γ * alternant (x ∘ i.succAbove) (l - γ) := by
  -- Column `j` has exponent `p j`. Subtract from each column but the first a power of `x i` times
  -- the column before: row `i` becomes `(x i ^ l N, 0, …, 0)` and the entry `(a, j + 1)` becomes
  -- `x a - x i` times a geometric sum. Expand along row `i`, then each geometric sum.
  -- used by `grind` in the bijection below
  have h_beyond {n : ℕ} (hn : N + 1 ≤ n) : l n ≤ l (N + 1) := hl_anti hn
  let p (j : Fin (N + 1)) : ℕ := l j.rev + j
  have h_mono (j : Fin N) : p j.castSucc ≤ p j.succ := add_le_add (hl_anti (by grind)) (by simp)
  rw [alternant, interlacing, det_pow_eq_det_sub_mul_geom_sum x i p h_mono, det_succ_row _ i]
  -- Write both sides as sums over permutations, the left side also over the exponents `g`.
  simp [p, alternant, sum_univ_succ, det_apply', prod_univ_sum, Finset.mul_sum,
    Equiv.prod_comp _ fun a ↦ x (i.succAbove a) - x i, -val_rev, prod_mul_distrib,
    prod_pow_eq_pow_sum]
  rw [univ.sum_comm, ite_sum_zero, ← sum_filter, ← sum_filter]
  -- Both sides are now sums over permutations `σ` of `Fin N`: on the left also over the exponents
  -- `g j` chosen from the geometric sums, on the right also over the interlacing `γ`.
  change ∑ g ∈ Fintype.piFinset (fun j : Fin N ↦ Ico (p j.castSucc) (p j.succ)) with l (N + 1) = 0,
      ∑ σ : Equiv.Perm (Fin N), (-1) ^ (i : ℕ) * x i ^ l N * (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ((∏ a : Fin N, (x (i.succAbove a) - x i)) * ((∏ j : Fin N, x (i.succAbove (σ j)) ^ g j) *
          x i ^ ∑ j : Fin N, (l (j.succ.rev : ℕ) + (j : ℕ) - g j)))) =
    ∑ γ ∈ interlacing l with l N - γ N = 0,
      ∑ σ : Equiv.Perm (Fin N), ((-1) ^ (i : ℕ) * ∏ a : Fin N, (x (i.succAbove a) - x i)) *
        (x i ^ Finsupp.degree γ * (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ j : Fin N, x (i.succAbove (σ j)) ^ (l (j.rev : ℕ) - γ (j.rev : ℕ) + (j : ℕ))))
  -- A choice of one exponent `g j` from each geometric sum is the same as an interlacing `γ` with
  -- `γ N = l N`: the partition `μ = l - γ` has `μ (N - 1 - j) + j = g j`.
  -- (`alternant` of `μ` vanishes unless `μ N = 0`. If `l (N + 1) ≠ 0` there is no such `γ`, and
  -- the left side is zero too.)
  clear h_mono
  let μ (g : Fin N → ℕ) (n : ℕ) : ℕ := if hn : n < N then g (rev ⟨n, hn⟩) - rev ⟨n, hn⟩ else 0
  refine sum_bij' (fun g hg ↦ onFinset (range (N + 1)) (fun n ↦ l n - μ g n) ?support)
    (fun γ _ j ↦ (l - γ) j.rev + j) ?to_mem ?inv_mem ?left_inv ?right_inv ?terms
  case support => grind
  -- the four conditions of the bijection are one computation with `μ`
  case to_mem | inv_mem | left_inv | right_inv =>
    simp [μ, interlacing, le_tsub_iff_left (hl_anti _), -val_rev, Finsupp.le_def]
    grind
  case terms =>
    simp [μ, degree_eq_weight_one, weight_apply, sum_range_succ, sum_range,
      ← rev_bijective.sum_comp (l · - _), -val_rev]
    grind

end New.GL

end Bordering

/-!
## The leading term of a semi-invariant in one row

Throughout, `f` is a Borel semi-invariant and `G * X_x ^ γ` is its leading term in the variables
`X (x, i)` of one row `x`, where `X_x ^ γ` is the monomial of exponent `γ` in these variables.
-/

section Interlacing

open MvPolynomial Finset Finsupp Algebra MonomialOrder

namespace New.GL

/-- Let the exponents `n` and `γ` agree outside the columns `i` and `i + 1` and have the same sum
`n i + n (i + 1) = γ i + γ (i + 1)`, in the pointwise form that a comparison of coefficients
gives. If `n i ≤ γ i` and `n ≠ γ`, then `γ` is below `n` for `columnOrder`. -/
private lemma columnOrder_lt_of_forall_add_ite_eq {γ n : ℕ →₀ ℕ} {i : ℕ}
    (h_eq : ∀ a : ℕ, (if i + 1 = a then n i else 0) + ((if i = a then n (i + 1) else 0) + n a) =
      (if i + 1 = a then γ i else 0) + ((if i = a then γ (i + 1) else 0) + γ a))
    (h_le : n i ≤ γ i) (h_ne : n ≠ γ) : γ ≺[columnOrder] n := by
  have h_sum : n (i + 1) + n i = γ (i + 1) + γ i := by simpa using h_eq i
  have h_off (a : ℕ) (ha : a ≠ i) (ha' : a ≠ i + 1) : n a = γ a := by
    simpa [Ne.symm ha, Ne.symm ha'] using h_eq a
  -- `n i = γ i` would force `n = γ`, so `n i < γ i` and hence `γ (i + 1) < n (i + 1)`.
  have h_lt_i : n i < γ i := by
    refine h_le.lt_of_ne fun h_eq_i ↦ h_ne (Finsupp.ext fun a ↦ ?_)
    rcases eq_or_ne a i with rfl | ha
    · exact h_eq_i
    rcases eq_or_ne a (i + 1) with rfl | ha'
    · lia
    exact h_off a ha ha'
  have h_lt_succ : γ (i + 1) < n (i + 1) := by lia
  exact columnOrder_lt_of_eq_above (i + 1) n (fun a ha ↦ (h_off a (by lia) (by lia)).symm) h_lt_succ

variable {Φ m : Type} [DecidableEq m] {R : Type} [CommRing R]
  {c : m → Φ} {x : m} {l : Φ × ℕ →₀ ℕ} {f : MatrixPoly m R}

/-- Let `f` be a Borel semi-invariant of weight `l` for the row colouring `c` (`f ∈ nabla R c l`),
and let `γ` be the leading exponent of `f` in the variables `X (x, i)` of the row `x`, for the order
`columnOrder` (which compares the highest column first). Then `γ i ≤ l (c x, i) - l (c x, i + 1)`
for every column `i`, with truncated subtraction: `γ` lies in `interlacing` of the weight at the
colour of `x`. -/
lemma degree_rowExpansion_mem_interlacing (hf : f ∈ nabla R c l) :
    columnOrder.degree (rowExpansion x f) ∈ interlacing (l.curry (c x)) := by
  classical
  -- Let `v, v'` be the columns `i, i + 1` of the colour of `x`. Semi-invariance under the block
  -- `!![s, -1; 0, T]` gives `f (s v + s T v', -v) = s ^ l i * T ^ l (i + 1) * f (v + T v', v')`.
  -- On the left `T` enters only as `s T`, so no term has more `T` than `s`. On the right, if
  -- `G X_x ^ γ` is the leading term of `f` in row `x`, then `G` is a coefficient of
  -- `T ^ (l (i + 1) + γ i) * s ^ l i`.
  set γ : ℕ →₀ ℕ := columnOrder.degree (rowExpansion x f)
  suffices h_bound : ∀ i : ℕ, γ i ≤ l.curry (c x) i - l.curry (c x) (i + 1) by
    exact (mem_interlacing_iff _).mpr h_bound
  intro i
  rw [Finsupp.curry_apply, Finsupp.curry_apply]
  by_contra! h_lt : l (c x, i) - l (c x, i + 1) < γ i
  -- As `γ ≠ 0`, the polynomial `rowExpansion x f` is not zero, nor is its leading coefficient `G`.
  have hG : (rowExpansion x f).coeff γ ≠ 0 := by grind [degree_zero, coeff_degree_eq_zero_iff]
  -- Coefficients lie in `P`, polynomials in `s` and `T`: `T` is `Polynomial.X` and `s` is `.C .X`.
  -- `θ` replaces `v` by `v + T v'` in the rows other than `x`.
  let P : Type _ := Polynomial (Polynomial (MatrixPoly {a // a ≠ x} R))
  let θ : MatrixPoly {a // a ≠ x} R →ₐ[R] P :=
    aeval fun y ↦ .CC (X y) + .X * .CC (single (c x, i) (X (y.1, i + 1)) (c y.1, y.2))
  have hθ (p : MatrixPoly {a // a ≠ x} R) : (θ p).coeff 0 = .C p := by
    induction p using MvPolynomial.induction_on with
    | C r => simp [P, θ, Polynomial.algebraMap_apply]
    | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add]
    | mul_X p y hp =>
      have h_X : (θ (X y)).coeff 0 = .C (X y) := by simp [P, θ]
      rw [map_mul, Polynomial.mul_coeff_zero, hp, h_X, map_mul]
  -- `Ψ` does the same in row `x`, at `v = 0` and `v' = X i * X (i + 1)`.
  let Ψ : MatrixPoly m R →ₐ[R] MvPolynomial ℕ P :=
    (aevalTower ((mapAlgHom θ).comp
        (algHom R (MatrixPoly {a // a ≠ x} R) (MvPolynomial ℕ (MatrixPoly {a // a ≠ x} R)))) fun j ↦
        (C Polynomial.X * X (i + 1)) ^ single i 1 j * X i ^ single (i + 1) 1 j * X j).comp
      (rowExpansion x).toAlgHom
  -- `b` is the identity matrix but for the block `!![s, -1; 0, T]`.
  let b : Φ × ℕ × ℕ → MvPolynomial ℕ P := fun (τ, j, k) ↦
    single j (C (.C .X ^ single (c x, i) 1 (τ, j) * .X ^ single (c x, i + 1) 1 (τ, j))) k -
      single (c x, i) (single (j + 1) 1 k) (τ, j)
  -- `Ψ` sends `X_x ^ γ` to `T ^ γ i` times the monomial of exponent `δ`.
  let δ : ℕ →₀ ℕ := single (i + 1) (γ i) + (single i (γ (i + 1)) + γ)
  -- Left side: the substitution factors through `scale : T ↦ s T`. An entry of `y b` (`y = Ψ ∘ X`)
  -- is `scale` of the entry of `y` plus the value at `T = 0` of the entry of `y b - y`.
  let scale : P →ₐ[R] P :=
    .restrictScalars R (Polynomial.aeval (R := Polynomial (MatrixPoly {a // a ≠ x} R)) (.C .X * .X))
  have h_factor : aeval (borelMul c b (Ψ ∘ X)) = (mapAlgHom scale).comp
      (aeval (mapAlgHom (Polynomial.aeval 0) ∘ (borelMul c b (Ψ ∘ X) - Ψ ∘ X) + Ψ ∘ X)) := by
    -- Multiplying by `b` scales the columns `i` and `i + 1` of the colour of `x` by `s` and `T`,
    -- and subtracts column `i` from column `i + 1`.
    have h_mul (Y : m × ℕ → MvPolynomial ℕ P) (y : m) (j : ℕ) : borelMul c b Y (y, j) =
        Y (y, j) * C (.C .X ^ single (c x, i) 1 (c y, j) * .X ^ single (c x, i + 1) 1 (c y, j)) -
          if (c x, i + 1) = (c y, j) then Y (y, i) else 0 := by
      rcases eq_or_ne (i + 1) j with rfl | hj
      · simp [borelMul, b, mul_sub, sum_sub_distrib, single_apply, ite_and]
      · simp [borelMul, b, mul_sub, sum_sub_distrib, single_apply, ite_and, hj]
    -- The values of `Ψ` on the variables of the row `x` and of another row `y`.
    have hΨx (j : ℕ) : Ψ (X (x, j)) =
        (C Polynomial.X * X (i + 1)) ^ single i 1 j * X i ^ single (i + 1) 1 j * X j := by
      simp [Ψ, rowExpansion]
    have hΨy (y : m) (hy : y ≠ x) (j : ℕ) : Ψ (X (y, j)) = C (θ (X (⟨y, hy⟩, j))) := by
      simp [Ψ, rowExpansion, hy, algHom]
    refine algHom_ext fun ⟨y, j⟩ ↦ ?_
    by_cases hy : y = x
    · -- Row `x`: casework on the column `j` against `i` and `i + 1`; each case is a ring identity.
      by_cases hj : j = i
      · simp [h_mul, hΨx, scale, P, hy, hj]
        ring
      by_cases hj' : j = i + 1
      · simp [h_mul, hΨx, scale, P, hy, hj']
        ring
      · simp [h_mul, hΨx, scale, P, hy, Ne.symm hj, Ne.symm hj']
    · -- Another row: the entries are constants `C p`, so this is an identity in `P`. Casework on
      -- `(c y, j)` against `(c x, i)` and `(c x, i + 1)`.
      simp only [aeval_X, AlgHom.comp_apply, mapAlgHom_apply, Pi.add_apply, Pi.sub_apply,
        Function.comp_apply, h_mul, hΨy _ hy, ← apply_ite C, ← C_0, ← C_mul, ← C_sub, ← C_add,
        map_C]
      refine congrArg C ?_
      by_cases hα : (c x, i) = (c y, j)
      · obtain ⟨hc, rfl⟩ := Prod.mk.inj hα
        simp [θ, scale, P, hc]
        ring
      by_cases hβ : (c x, i + 1) = (c y, j)
      · obtain ⟨hc, rfl⟩ := Prod.mk.inj hβ
        simp [θ, scale, P, hc]
      · simp [θ, scale, P, hα, hβ]
  -- After `T ↦ s T` the coefficient of `T ^ a` is divisible by `s ^ a`.
  have h_scale (p : P) {a k : ℕ} (hk : k < a) : ((scale p).coeff a).coeff k = 0 := by
    simp [P, scale, ← Polynomial.comp_eq_aeval, Polynomial.coeff_mul_X_pow', hk.not_ge]
  have h_left : (((aeval (borelMul c b (Ψ ∘ X)) f).coeff δ).coeff (l (c x, i + 1) + γ i)).coeff
      (l (c x, i)) = 0 := by
    have h_deg_lt : l (c x, i) < l (c x, i + 1) + γ i := by lia
    rw [h_factor, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
    exact h_scale _ h_deg_lt
  -- Right side: the weight factor, and the coefficient of `T ^ γ i` at `δ` in `Ψ f`.
  have h_weight :
      (l.prod fun p k ↦ b (p.1, p.2, p.2) ^ k) = C (.C .X ^ l (c x, i) * .X ^ l (c x, i + 1)) := by
    -- The flags stop `simp` from splitting the powers `s ^ [p = (c x, i)]` into cases, and from
    -- rewriting `C (a ^ n)` as `C a ^ n`.
    simp [b, prod_mul_distrib, -pow_ite, -Prod.mk.injEq, prod_pow_eq_pow_sum, ↓if_mem_support, prod,
      single_apply, mul_pow, ← pow_mul, -C_pow]
  have h_top : (((Ψ f).coeff δ).coeff (γ i)).coeff 0 = (rowExpansion x f).coeff γ := by
    -- Expand `f` along row `x` and apply `Ψ` term by term; only the term of `γ` contributes.
    have h_expand : (Ψ f).coeff δ = ∑ n ∈ (rowExpansion x f).support,
        θ ((rowExpansion x f).coeff n) *
          (.X ^ n i * (X (i + 1) ^ n i * (X i ^ n (i + 1) * monomial n 1) : MvPolynomial ℕ P).coeff
            δ) := by
      rw [AlgHom.comp_apply]
      change (eval₂ _ _ ((rowExpansion x).toAlgHom f) : MvPolynomial ℕ P).coeff δ = _
      rw [eval₂_eq]
      -- Flags as in `h_weight`; `-map_aeval` keeps `θ` applied to the coefficients.
      simp [prod_mul_distrib, -pow_ite, prod_pow_eq_pow_sum, -map_aeval, ↓if_mem_support,
        algHom, single_apply, mul_pow, ← map_pow, mul_assoc, ← pow_mul, ← map_prod, -C_pow]
    rw [h_expand, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, Finset.sum_eq_single γ]
    · simp [P, δ, hθ, X_pow_eq_monomial, Polynomial.coeff_mul_X_pow']
    · -- Another exponent `n` reaching `δ` with `n i ≤ γ i` has `n i < γ i`, hence
      -- `γ (i + 1) < n (i + 1)` and equal entries beyond: it exceeds the leading exponent `γ`.
      intro n hn hne
      have h_not_lt : ¬ γ ≺[columnOrder] n := fun h_lt ↦
        MvPolynomial.mem_support_iff.mp hn (coeff_eq_zero_of_lt h_lt)
      -- The term of `n` is nonzero only if `n` reaches `δ` with `n i ≤ γ i`.
      suffices h_vanish : (∀ a : ℕ,
          (if i + 1 = a then n i else 0) + ((if i = a then n (i + 1) else 0) + n a) =
            (if i + 1 = a then γ i else 0) + ((if i = a then γ (i + 1) else 0) + γ a)) →
          n i ≤ γ i → ((θ ((rowExpansion x f).coeff n)).coeff (γ i - n i)).coeff 0 = 0 by
        simpa [P, δ, X_pow_eq_monomial, Polynomial.coeff_mul_X_pow', Finsupp.ext_iff,
          apply_ite AddMonoidAlgebra.coeff, DFunLike.ite_apply, single_apply, ite_apply] using
          h_vanish
      intro h_shape h_le
      exact absurd (columnOrder_lt_of_forall_add_ite_eq h_shape h_le hne) h_not_lt
    · intro hγ
      exact absurd (MvPolynomial.mem_support_iff.mpr hG) hγ
  -- By semi-invariance the coefficient in `h_left` is the one in `h_top`, so `G = 0`.
  apply hG
  rw [← h_top, ← h_left, mem_nabla.mp hf (MvPolynomial ℕ P) b (Ψ ∘ X), h_weight, ← aeval_unique]
  -- `← map_pow` gathers powers inside `C`, which `C_pow` would undo.
  simp [P, Polynomial.coeff_X_pow_mul', ← map_pow, mul_assoc, -C_pow]

/-- Let `γ` be the leading exponent of `f` in the variables of the row `x` (for `columnOrder`, the
lexicographic order that compares exponents at the highest column first), and let `f` be a Borel
semi-invariant of weight `γ + l`, where `γ` is placed at the colour `c x` (`γ.mapDomain (c x, ·)`).
Then the leading coefficient `G` of `f` in the row `x`, a polynomial in the other rows, is a Borel
semi-invariant of weight `l` for the colouring `c` restricted to the rows other than `x`. -/
lemma HasLeadingTerm.leadingCoeff_mem_nabla
    (hf : f ∈ nabla R c
      ((columnOrder.degree (rowExpansion x f)).mapDomain (fun i : ℕ ↦ (c x, i)) + l)) :
    columnOrder.leadingCoeff (rowExpansion x f) ∈ nabla R (c ∘ (↑)) l := by
  -- Let `G X_x ^ γ` be the leading term of `f` in row `x`. Compare the coefficients of `X_x ^ γ`
  -- in `f (y β) = ∏ β ^ (γ + l) * f y` for a generic upper triangular `β`. As `(y β) (x, j)` is
  -- `β j j * y (x, j)` plus smaller terms, the left one is `G (y β) * ∏ β j j ^ γ j`; the factor
  -- `∏ β j j ^ γ j` cancels.
  set γ : ℕ →₀ ℕ := columnOrder.degree (rowExpansion x f)
  let A : Type _ := MatrixPoly {a // a ≠ x} (MvPolynomial (Φ × ℕ × ℕ) R)
  let β : Φ × ℕ × ℕ → A := C ∘ X
  -- `ρ` substitutes `y β` in the rows other than `x`; `u j` is the entry `(x, j)` of `y β`.
  let ρ : MatrixPoly {a // a ≠ x} R →ₐ[R] A := aeval (borelMul (c ∘ (↑)) β X)
  let u (j : ℕ) : MvPolynomial ℕ A := borelMul c (C ∘ β) (fun p ↦ X p.2) (x, j)
  have hu_lead (j : ℕ) : columnOrder.HasLeadingTerm (u j) (single j 1) (β (c x, j, j)) := by
    -- `u j` is the sum of the `X i * C (β (c x, i, j))` over `i ≤ j`.
    have h_term (i : ℕ) :
        columnOrder.HasLeadingTerm (X i * C (β (c x, i, j))) (single i 1) (β (c x, i, j)) := by
      rw [X, C_apply, monomial_mul_monomial, add_zero, one_mul]
      exact hasLeadingTerm_monomial _ _
    have h_lt : ∀ i ∈ range (j + 1), i ≠ j → single i 1 ≺[columnOrder] single j 1 := by
      grind [columnOrder_lt_of_eq_above j]
    simpa only [u, borelMul, Function.comp_apply] using
      HasLeadingTerm.sum (s := range (j + 1)) h_term j h_lt (absurd (self_mem_range_succ j))
  -- `subst` substitutes `y β` in `f` and expands along row `x`; by the definitions of
  -- `aevalTower` and `eval₂`, `subst f` is a sum over the exponents of `f` in row `x`.
  let subst : MatrixPoly m R →ₐ[R] MvPolynomial ℕ A :=
    (aevalTower ((algHom R A (MvPolynomial ℕ A)).comp ρ) u).comp (rowExpansion x).toAlgHom
  have h_eval : subst f = ∑ n ∈ (rowExpansion x f).support,
      C (ρ ((rowExpansion x f).coeff n)) * n.prod fun j e ↦ u j ^ e :=
    rfl
  -- In this sum the term of `γ` leads.
  have h_lead : columnOrder.HasLeadingTerm (subst f) γ
      (ρ ((rowExpansion x f).coeff γ) * γ.prod fun j e ↦ β (c x, j, j) ^ e) := by
    rw [h_eval]
    refine HasLeadingTerm.sum (γ := fun n ↦ n)
      (a := fun n ↦ ρ ((rowExpansion x f).coeff n) * n.prod _) (fun n ↦ ?_) γ
      (fun n hn hne ↦ ?_) fun hγ ↦ ?_
    · simpa using (hasLeadingTerm_monomial 0 _).mul (finsuppProd_pow hu_lead n)
    · exact lt_of_le_of_ne (columnOrder.le_degree hn) (columnOrder.toSyn.injective.ne hne)
    · simp [MvPolynomial.notMem_support_iff.mp hγ]
  -- The semi-invariance of `f`, with both sides expanded along row `x`; `W` is the weight factor.
  let Ψ : MatrixPoly m R →ₐ[R] MvPolynomial ℕ A :=
    (mapAlgHom (aeval X)).comp (rowExpansion x).toAlgHom
  let W : MvPolynomial ℕ A := (γ.mapDomain (fun i : ℕ ↦ (c x, i)) + l).prod
    fun (p : Φ × ℕ) (k : ℕ) ↦ (C ∘ β) (p.1, p.2, p.2) ^ k
  have h_subst : aeval (borelMul c (C ∘ β) (Ψ ∘ X)) = subst := by
    refine algHom_ext fun ⟨y, j⟩ ↦ ?_
    by_cases hy : y = x <;> simp [rowExpansion, Ψ, ρ, u, subst, hy, borelMul, algHom]
  have h_semi : subst f = W * Ψ f := by
    have h_nabla : aeval (borelMul c (C ∘ β) (Ψ ∘ X)) f = W * aeval (Ψ ∘ X) f :=
      mem_nabla.mp hf (MvPolynomial ℕ A) (C ∘ β) (Ψ ∘ X)
    rwa [← aeval_unique, h_subst] at h_nabla
  -- The factor to cancel is a monomial in the generic entries, hence regular.
  have h_reg : IsRegular (γ.prod fun j e ↦ β (c x, j, j) ^ e) := by
    simpa [β, Finsupp.prod, ← map_pow, ← map_prod, -C_pow] using .monomial (.prod (by simp))
  -- Membership in `nabla` is by definition the identity `ρ G = ∏ β ^ l * G` for the generic `β`.
  -- Multiplied by the regular factor, its left side is the coefficient at `γ` of `subst f` (by
  -- `h_lead`), and the right side that of `W * Ψ f`.
  have h_rhs : (W * Ψ f).coeff γ =
      ((l.prod fun (p : Φ × ℕ) (k : ℕ) ↦ (X (p.1, p.2, p.2) : MvPolynomial (Φ × ℕ × ℕ) R) ^ k) •
        (aeval X : MatrixPoly {a // a ≠ x} R →ₐ[R] A)
          (columnOrder.leadingCoeff (rowExpansion x f))) *
        γ.prod fun j e ↦ β (c x, j, j) ^ e := by
    -- `W` is a constant, so it comes out of the coefficient; it is the product of the factors for
    -- `l` and for `γ`. `↓` splits this product before the definitions unfold.
    simp [A, β, Ψ, γ, W, leadingCoeff, ↓prod_add_index', pow_add, ↓prod_mapDomain_index,
      ← map_pow, Finsupp.prod, ← map_prod, mul_assoc, coeff_map, -C_pow, Algebra.smul_def,
      MvPolynomial.algebraMap_eq]
    ring
  rw [← h_semi, h_lead.coeff_eq] at h_rhs
  exact h_reg.right h_rhs

end New.GL

end Interlacing

/-!
## The basis theorem and the character identity

The proof of `New.GL.exists_isStdMinorFamily` is an induction on the number of rows by leading
terms in one row.
-/

section MinorBasis

open MvPolynomial Finset MonomialOrder Submodule Finsupp Nat

namespace New.GL

/-- A standard family of fillings `I` for rows coloured by `c` and columns `j` of colour `τ j` and
height `h j`: each `I i` (a `ColoredTableau`) gives column `j` an `h j`-tuple of rows of colour
`τ j`; `minorProduct R (I i)` is the product of the minors on these rows and the first `h j`
columns. -/
structure IsStdMinorFamily {Φ J m ι : Type} [Fintype m] [Fintype J] [Fintype ι]
    {c : m → Φ} {τ : J → Φ} {h : J → ℕ} (I : ι → ColoredTableau c τ h) : Prop where
  /-- Over every commutative ring the products of minors are linearly independent. -/
  linearIndependent (R : Type) [CommRing R] :
    LinearIndependent R fun i : ι ↦ minorProduct R (I i)
  /-- Over every commutative ring the span of the products of minors contains the
  semi-invariants of weight `columnWeight τ h`. -/
  nabla_le_span (R : Type) [CommRing R] :
    nabla R c (columnWeight τ h) ≤ span R (Set.range fun i : ι ↦ minorProduct R (I i))
  /-- If `t` is the only colour and `e` enumerates the rows, then the sum over the fillings of the
  products of the `x a` over their entries `a`, times the alternant of the zero weight, is the
  alternant of the weight `columnWeight τ h (t, ·)`. -/
  character [Subsingleton Φ] (t : Φ) (N : ℕ) (e : Fin N ≃ m) (x : m → ℂ) :
    (∑ i : ι, ∏ j : J, ∏ s : Fin (h j), x (I i j s)) * alternant (x ∘ e) 0 =
      alternant (x ∘ e) fun k : ℕ ↦ columnWeight τ h (t, k)

section LeadingTerms

variable {Φ m R : Type} [DecidableEq m] [CommRing R] {y : m}

/-- If `p i` has leading term `q i` times the monomial of exponent `γ` in the row `y` for every `i`,
then a combination of the `p i` has as leading term the same combination of the `q i`, times that
monomial. Here `columnOrder.HasLeadingTerm F γ G` says that no exponent of `F` exceeds `γ` for
`columnOrder` (lexicographic, comparing exponents at the highest column first) and that the
coefficient of the monomial of exponent `γ` is `G`; `rowExpansion y` writes a polynomial as one in
the variables of the row `y` over the polynomials in the other rows. -/
lemma HasLeadingTerm.rowExpansion_combination {ι : Type} {γ : ℕ →₀ ℕ} {p : ι → MatrixPoly m R}
    {q : ι → MatrixPoly {a : m // a ≠ y} R}
    (h_lead : ∀ i : ι, columnOrder.HasLeadingTerm (rowExpansion y (p i)) γ (q i)) (a : ι →₀ R) :
    columnOrder.HasLeadingTerm (rowExpansion y (a.sum fun (i : ι) (r : R) ↦ r • p i)) γ
      (a.sum fun (i : ι) (r : R) ↦ r • q i) := by
  have h_above (i : ι) (δ : ℕ →₀ ℕ) (hδ : γ ≺[columnOrder] δ) :
      (rowExpansion y (p i)).coeff δ = 0 :=
    coeff_eq_zero_of_lt ((h_lead i).degree_le.trans_lt hδ)
  refine .mk ?_ ?_
  · -- No exponent above `γ` occurs in any `p i`, hence none in the combination.
    simp +contextual [Finsupp.sum, degree_le_iff, not_imp_comm, h_above]
  · simp [Finsupp.sum, fun i ↦ (h_lead i).coeff_eq]

/-- Polynomials `p γ i` with leading terms `q γ i` times the monomial of exponent `γ` in the row `y`
(`columnOrder.HasLeadingTerm`), for distinct exponents `γ` from a finite set `Γ`, are linearly
independent if for each exponent `γ` the coefficients `q γ i` are. -/
lemma linearIndependent_of_hasLeadingTerm {Γ : Finset (ℕ →₀ ℕ)} {ι : Γ → Type}
    {p : ∀ γ : Γ, ι γ → MatrixPoly m R} {q : ∀ γ : Γ, ι γ → MatrixPoly {a : m // a ≠ y} R}
    (h_lead : ∀ (γ : Γ) (i : ι γ), columnOrder.HasLeadingTerm (rowExpansion y (p γ i)) γ (q γ i))
    (h_indep : ∀ γ : Γ, LinearIndependent R (q γ)) :
    LinearIndependent R fun i : Σ γ : Γ, ι γ ↦ p i.fst i.snd := by
  -- In a relation `a ≠ 0` take the largest `γ` that occurs. The coefficient of that monomial is a
  -- relation among the `q γ i`, so the `γ`-part of `a` vanishes.
  refine linearIndependent_iff.mpr fun a ha ↦ by_contra fun ha_ne ↦ ?_
  have h_nonempty : a.splitSupport.Nonempty := by simpa [splitSupport] using ha_ne
  obtain ⟨γ, hγ, hγ_max⟩ :=
    a.splitSupport.exists_max_image (fun δ ↦ columnOrder.toSyn δ.val) h_nonempty
  have h_lt : ∀ δ ∈ a.splitSupport, δ ≠ γ → δ.val ≺[columnOrder] γ.val := fun δ hδ h_ne ↦
    lt_of_le_of_ne (hγ_max δ hδ) fun h_eq ↦ h_ne (Subtype.ext (columnOrder.toSyn.injective h_eq))
  have h_top : columnOrder.HasLeadingTerm
      (∑ δ ∈ a.splitSupport, rowExpansion y ((a.split δ).sum fun i r ↦ r • p δ i))
      γ ((a.split γ).sum fun i r ↦ r • q γ i) :=
    .sum (fun δ ↦ HasLeadingTerm.rowExpansion_combination (h_lead δ) (a.split δ)) γ h_lt (absurd hγ)
  have h_rel : (a.split γ).sum (fun i r ↦ r • q γ i) = 0 := by
    rw [linearCombination_apply, sigma_sum] at ha
    simp [← h_top.coeff_eq, ← map_sum, ha]
  exact (mem_splitSupport_iff_ne_zero a γ).mp hγ (linearIndependent_iff.mp (h_indep γ) _ h_rel)

/-- Let `γ` run over the exponents interlacing the weight `l` at the colour of the row `y`, and let
`l' γ` be `l` lowered by `γ`. Borel semi-invariants (`nabla`) `p γ i` of weight `l` with leading
terms `q γ i` times the monomial of exponent `γ` in the row `y` span all semi-invariants of weight
`l`, if for each `γ` the span of the `q γ i` contains the semi-invariants of weight `l' γ` in the
other rows. -/
lemma nabla_le_span_of_hasLeadingTerm {c : m → Φ} {l : Φ × ℕ →₀ ℕ}
    {ι : interlacing (l.curry (c y)) → Type} {l' : interlacing (l.curry (c y)) → Φ × ℕ →₀ ℕ}
    {p : ∀ γ : interlacing (l.curry (c y)), ι γ → MatrixPoly m R}
    {q : ∀ γ : interlacing (l.curry (c y)), ι γ → MatrixPoly {a : m // a ≠ y} R}
    (h_weight : ∀ γ : interlacing (l.curry (c y)),
      l = γ.val.mapDomain (fun k : ℕ ↦ (c y, k)) + l' γ)
    (h_mem : ∀ (γ : interlacing (l.curry (c y))) (i : ι γ), p γ i ∈ nabla R c l)
    (h_lead : ∀ (γ : interlacing (l.curry (c y))) (i : ι γ),
      columnOrder.HasLeadingTerm (rowExpansion y (p γ i)) γ (q γ i))
    (h_span : ∀ γ : interlacing (l.curry (c y)),
      nabla R (fun a : {a : m // a ≠ y} ↦ c a) (l' γ) ≤ span R (Set.range (q γ))) :
    nabla R c l ≤
      span R (Set.range fun i : Σ γ : interlacing (l.curry (c y)), ι γ ↦ p i.fst i.snd) := by
  -- Induction on the leading exponent of `f` in the variables of row `y`.
  intro f
  induction f using (wellFounded_lt.onFun
    (f := fun f ↦ columnOrder.toSyn (columnOrder.degree (rowExpansion y f)))).induction with
  | h f ih =>
    intro hf
    -- The leading exponent `γ` interlaces, and the leading coefficient is a semi-invariant for
    -- the other rows, hence a combination `a` of the `q γ i`.
    let γ : interlacing (l.curry (c y)) :=
      ⟨columnOrder.degree (rowExpansion y f), degree_rowExpansion_mem_interlacing hf⟩
    have h_coeff_mem : columnOrder.leadingCoeff (rowExpansion y f) ∈
        nabla R (fun a : {a : m // a ≠ y} ↦ c a) (l' γ) :=
      HasLeadingTerm.leadingCoeff_mem_nabla (by rwa [← h_weight γ])
    obtain ⟨a, ha⟩ : ∃ a : ι γ →₀ R,
        (a.sum fun i r ↦ r • q γ i) = columnOrder.leadingCoeff (rowExpansion y f) :=
      mem_span_range_iff_exists_finsupp.mp (h_span γ h_coeff_mem)
    -- The same combination `g` of the `p γ i` has the same leading term as `f`.
    let g : MatrixPoly m R := a.sum fun i r ↦ r • p γ i
    have hg_span :
        g ∈ span R (Set.range fun i : Σ δ : interlacing (l.curry (c y)), ι δ ↦ p i.fst i.snd) :=
      mem_span_range_iff_exists_finsupp.mpr
        ⟨a.mapDomain (Sigma.mk γ), sum_mapDomain_index_inj sigma_mk_injective⟩
    have hg_mem : g ∈ nabla R c l := sum_mem fun i _ ↦ smul_mem _ _ (h_mem γ i)
    have hg_lead :
        columnOrder.HasLeadingTerm (rowExpansion y g) γ
          (columnOrder.leadingCoeff (rowExpansion y f)) := by
      rw [← ha]
      exact HasLeadingTerm.rowExpansion_combination (h_lead γ) a
    -- So `f - g` has a smaller leading exponent or is zero.
    have h_le : columnOrder.degree (rowExpansion y (f - g)) ≼[columnOrder] γ.val := by
      rw [map_sub]
      exact degree_sub_le.trans (sup_le le_rfl hg_lead.degree_le)
    have h_coeff : (rowExpansion y (f - g)).coeff γ = 0 := by
      rw [map_sub, AddMonoidAlgebra.coeff_sub_apply, hg_lead.coeff_eq]
      exact sub_self _
    refine (sub_mem_iff_left _ hg_span).mp ?_
    rcases h_le.lt_or_eq with h_lt | h_eq
    · exact ih (f - g) h_lt (sub_mem hf hg_mem)
    · -- The leading coefficient of `f - g` vanishes, so `f - g = 0`.
      rw [← columnOrder.toSyn.injective h_eq, coeff_degree_eq_zero_iff,
        EmbeddingLike.map_eq_zero_iff] at h_coeff
      simp [h_coeff]

end LeadingTerms

/-- At each colour `t` the number of columns of height above `k` does not increase with `k`. -/
lemma antitone_columnWeight_curry {Φ J : Type} [Fintype J] (τ : J → Φ) (h : J → ℕ) (t : Φ) :
    Antitone ((columnWeight τ h).curry t) := by
  classical
  have h_count (k : ℕ) : (columnWeight τ h).curry t k = #{j : J | τ j = t ∧ k < h j} := by
    simp [columnWeight, card_filter, ite_and, single_apply]
  intro a b hab
  rw [h_count, h_count]
  -- A column of height above `b` also has height above any `a ≤ b`.
  gcongr

/-- Rows `m` are coloured by `c`; column `j : J` has colour `τ j` and height `h j`, and a
`ColoredTableau c τ h` gives it an `h j`-tuple of rows of colour `τ j`. With no rows there is a
standard family (`IsStdMinorFamily`) of these: the one empty filling if all heights are zero, and
the empty family otherwise. -/
lemma exists_isStdMinorFamily_of_isEmpty {Φ J m : Type} [Fintype m] [IsEmpty m] [Fintype J]
    (c : m → Φ) (τ : J → Φ) (h : J → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → ColoredTableau c τ h), IsStdMinorFamily I := by
  -- Polynomials are constants, and an enumeration `Fin N ≃ m` forces `N = 0`.
  rcases eq_or_ne h 0 with rfl | h_ne
  · refine ⟨Unit, inferInstance, nofun, ⟨?indep, ?span, ?character⟩⟩
    case indep =>
      intro R _
      simp [Fintype.linearIndependent_iff, minorProduct, minor, ← C_mul', Unique.forall_iff]
    case span =>
      intro R _ f _
      rw [f.eq_C_of_isEmpty]
      simp [minorProduct, minor, ← one_eq_span]
    case character =>
      intro _ t N e x
      obtain rfl : N = 0 := by simpa using Fintype.card_congr e
      simp [alternant, columnWeight, univ_eq_empty]
  · have h_sum : ∑ j, h j ≠ 0 := by simpa using Function.ne_iff.mp h_ne
    refine ⟨Empty, inferInstance, nofun,
      fun R _ ↦ linearIndependent_empty_type, fun R _ f hf ↦ ?_, fun t N e x ↦ ?_⟩
    · -- The weight is not zero, so semi-invariance for the zero matrix kills every constant.
      obtain ⟨r, rfl⟩ : ∃ r : R, f = C r := ⟨f.coeff 0, f.eq_C_of_isEmpty⟩
      have h_semi : r = ((columnWeight τ h).prod fun (p : Φ × ℕ) (k : ℕ) ↦ (0 : R) ^ k) * r := by
        simpa using mem_nabla.mp hf R 0 0
      have h_prod_zero : ((columnWeight τ h).prod fun (p : Φ × ℕ) (k : ℕ) ↦ (0 : R) ^ k) = 0 := by
        simp [columnWeight, pow_add, ← prod_finsetSum_index, prod_pow_eq_pow_sum, h_sum]
      have h_r : r = 0 := by rwa [h_prod_zero, zero_mul] at h_semi
      simp [h_r]
    · obtain rfl : N = 0 := by simpa using Fintype.card_congr e
      simpa [alternant, columnWeight, univ_eq_empty, Subsingleton.elim _ t, single_apply] using
        Function.ne_iff.mp h_ne

/-- Take finitely many rows coloured by `c`, and finitely many columns `j` of colour `τ j` and
height `h j`. Then there is a finite type `ι` and a family `I` of fillings indexed by it that is
standard in the sense of `IsStdMinorFamily`. Each `I i` gives column `j` an `h j`-tuple of rows of
colour `τ j`, and has minor product `minorProduct R (I i)`: the product of the minors on these rows
and the first `h j` columns.

This is an existence form of the standard basis theorem for Schur modules (Akin–Buchsbaum–Weyman),
stated for products of minors with coloured rows; the index type is not identified with the
semistandard tableaux. -/
lemma exists_isStdMinorFamily {Φ J m : Type} [Fintype m] [Fintype J] (c : m → Φ)
    (τ : J → Φ) (h : J → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → ColoredTableau c τ h), IsStdMinorFamily I := by
  classical
  -- Induction on the number of rows. Fix a row `y` and expand polynomials in its variables. For
  -- each exponent `γ` interlacing the weight, take the family for the other rows and the weight
  -- lowered by `γ`, and lift its members by `exists_bordering`; the lifts have leading terms `y^γ`
  -- times the smaller products, which gives independence and spanning.
  induction h_card : Nat.card m using Nat.strongRec generalizing m h with | ind n ih => ?_
  rcases isEmpty_or_nonempty m with hm | ⟨⟨y⟩⟩
  · exact exists_isStdMinorFamily_of_isEmpty c τ h
  -- For each `γ`, the heights `k γ` give the weight lowered by `γ` (`h_weight`), and `lift γ`
  -- borders the fillings that avoid `y` (`h_lift`, `h_monomial`), by `exists_bordering`.
  have h_border (γ : interlacing ((columnWeight τ h).curry (c y))) :=
    exists_bordering h γ.prop
  choose k h_weight lift h_lift h_monomial using h_border
  -- The induction hypothesis: standard families `I γ` for the other rows.
  have h_fewer : Nat.card {a : m // a ≠ y} < n :=
    h_card.subst (Finite.card_subtype_lt (x := y) (not_not_intro rfl))
  have h_family : ∀ γ : interlacing ((columnWeight τ h).curry (c y)),
      ∃ (ι : Type) (_ : Fintype ι)
        (I : ι → ColoredTableau (c ∘ (↑) : {a : m // a ≠ y} → Φ) τ (k γ)), IsStdMinorFamily I :=
    fun γ ↦ ih _ h_fewer (c ∘ (↑) : {a : m // a ≠ y} → Φ) (k γ) rfl
  choose ι hι_fintype I hI using h_family
  refine ⟨Sigma ι, inferInstance, fun i ↦ lift i.fst (I i.fst i.snd), fun R _ ↦ ?_,
    fun R _ ↦ ?_, ?_⟩
  · exact linearIndependent_of_hasLeadingTerm (p := fun γ i ↦ minorProduct R (lift γ (I γ i)))
      (fun γ i ↦ h_lift γ (I γ i) R) fun γ ↦ (hI γ).linearIndependent R
  · exact nabla_le_span_of_hasLeadingTerm (p := fun γ i ↦ minorProduct R (lift γ (I γ i)))
      h_weight (fun γ i ↦ minorProduct_mem_nabla (lift γ (I γ i)))
      (fun γ i ↦ h_lift γ (I γ i) R) fun γ ↦ (hI γ).nabla_le_span R
  · -- The character: both sides obey the same recursion `alternant_succ` in the row `y`.
    intro _ t N e x
    rcases N with _ | N
    · exact nomatch e.symm y
    have h_only : interlacing 0 = {0} := by simp [interlacing]
    obtain rfl : t = c y := Subsingleton.elim t (c y)
    -- Write both weights as finitely supported functions, the form that `alternant_succ` takes.
    change _ * alternant (x ∘ e) ⇑(0 : ℕ →₀ ℕ) =
      alternant (x ∘ e) ⇑((columnWeight τ h).curry (c y))
    -- Expand both alternants at the index of `y`; the common factor `± ∏ (x a - x y)` cancels and
    -- the two sums over `γ` are compared term by term.
    rw [alternant_succ _ (antitone_columnWeight_curry τ h (c y)) (e.symm y),
      ← (interlacing _).sum_coe_sort, alternant_succ 0 antitone_const (e.symm y),
      h_only, mul_left_comm, Fintype.sum_sigma, univ.sum_mul]
    congr with γ
    -- For each `γ` use the identity for the other rows, enumerated by `e` with `y` left out.
    let e' : Fin N ≃ {a : m // a ≠ y} :=
      .optionSubtype _ ⟨(finSuccEquiv' (e.symm y)).symm.trans e, e.apply_symm_apply y⟩
    have h_rest := (hI γ).character (c y) N e' fun a ↦ x a
    -- `e'` is `e` composed with the embedding that skips the index of `y`.
    have h_e' : (fun a : {a : m // a ≠ y} ↦ x a) ∘ e' =
        (x ∘ e) ∘ (e.symm y).succAbove := by
      simp [funext_iff, e', finSuccEquiv'_symm_some]
    rw [h_e'] at h_rest
    -- The weight lowered by `γ` is that of `k γ` (`h_weight γ`), and a lift adds `x y ^ |γ|` to the
    -- product over the entries (`h_monomial`); so both sides are `x y ^ |γ|` times the sides of
    -- `h_rest`.
    have h_lowered : (⇑((columnWeight τ h).curry (c y)) - ⇑γ.val) =
        fun n : ℕ ↦ columnWeight τ (k γ) (c y, n) := by
      simp [funext_iff, h_weight γ, Prod.mk_right_injective]
    rw [h_lowered, ← h_rest]
    simp [h_monomial, ← univ.mul_sum, mul_assoc]

end New.GL

end MinorBasis

end
end
end

/-!
# Schur matrices, the standard basis of ∇, its weights and the highest vector

Polynomials are taken in the entries of an array y with rows (τ, a). Here κ_τ(h) is the number of
columns of height h at the place τ; `New.rankAt n τ` = |n_τ|, and
λ = `New.diagramWeight (rankAt n) κ` has λ(τ, k) = Σ_{k<h<|n_τ|} κ_τ(h). The products
b_i = `New.nablaBasis` of minors of y along standard fillings form a basis of the module
∇ = `New.nablaFamily` of Borel semi-invariants. The Schur matrix S_κ(z) = `New.schur κ z` of a
family of matrices z_τ records the expansion of b'_i(zy); for square z this gives a polynomial
representation of ∏_τ GL(n_τ), which `New.weylRep` twists by integer powers of determinants. For one
place and a one-row shape, S_κ over ℂ is a symmetric power, and, over a topological ring, S_κ(z) is
continuous in z for square z.

## Main definitions and results

* `New.linearIndependent_nablaBasis`, `New.range_nablaCombination`: the b_i form a basis of ∇ over
  every commutative ring.
* `New.sum_schur_smul_nablaBasis`, `New.GL.schur_eq_of_expansion`: row i of S_κ(z) is characterised
  by the expansion of b'_i(zy) in the products b_j(y) ∏_τ det(y_τ)^{d_τ}, with
  d = `New.schurDetExp`.
* `New.schur_map`, `New.schur_mul_left`, `New.schur_mul_right`, `New.schur_apply_eq_prod`: base
  change, multiplicativity, and the product over the places τ.
* `New.schur_diagonal`, `New.weyl_character`: diagonal matrices and Weyl's character formula.
* `New.weylRep κ e` is the matrix representation of `∏ τ, GL (n τ) R` of weight `(κ, e)`: the Schur
  matrix `New.schur κ g` twisted by the powers `det (g τ) ^ e τ`, with integer exponents `e τ`.
* `New.map_nablaBasis_eq_map_weylKernel_mul_weylEval`: fix enumerations e_τ of the rows. Let φ be a
  linear form with φ(b_i) ≠ 0 only if λ(τ, e_τ(a)) ≤ `New.tableauWeight` i τ a for every row (τ, a).
  Then φ(b_i) = φ(k)·b_i(y). Here y is the permutation array of e (`New.permArray`), and k is the
  kernel `New.weylKernel` at y, a substitution (`New.rowSubst`) of the product `New.highestPoly` of
  leading minors, with value k(y) = 1. So on the span of the b_i, φ is determined by its value on k.

Notions from other files:
* `New.schur`: The Schur matrix S_κ(z) of matrices z_τ of size n'_τ×n_τ. Row i holds chosen
  coordinates of b'_i(zy) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}. Here b'_i and b_j are the
  standard basis polynomials in the rows n' and n, and d is given by `New.schurDetExp`.
* `New.rowSubst`: For matrices z_τ of size n'_τ×n_τ, the algebra homomorphism f ↦ f(zy) sending
  variable y_{(τ,b),i} to Σ_a z_τ(b,a) y_{(τ,a),i}.
* `New.WeylIndexFamily`: The type of families choosing, for each place τ, a filling in the chosen
  standard set with rows n_τ, heights below |n_τ| and multiplicities κ_τ.
* `New.schurDetExp`: The natural number κ_τ(|n_τ|) if |n_τ| < |n'_τ|, and 0 otherwise, as a function
  of the place τ.
* `New.FitsRanks`: For row families n and n', the condition, at every place τ, that |n_τ| ≤ |n'_τ|
  and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|.
* `New.detPow`: The product over places τ of the determinant of the variables in all rows of block τ
  (fixed enumeration) and first |n_τ| columns, raised to e_τ.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.MinorBasis` for sources.
-/

@[expose] public section

/-!
## The standard basis of ∇ and Schur matrices

Rectangular z_τ, of size n'_τ × n_τ, are allowed under the condition `New.FitsRanks`.
-/

namespace New

open MvPolynomial Finset Matrix «GL» Submodule Equiv Fintype Function Sigma

variable {Φ : Type}
  {R S F : Type _} [CommRing R] [CommRing S] [Fintype Φ]
  {n n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] {κ : Φ → ℕ → ℕ}
  (e : Φ → ℕ) (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) (x : ∀ τ : Φ, n τ → R)

/-! ### The standard basis of ∇ -/

omit [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- For each place τ, let `T τ` be a filling with entries in `n' τ` that has `κ τ h` columns of
height `h` for each `h < M τ`. Take the product over τ of the minor products of `T τ`, taken in the
rows (τ, ·). This product lies in `nabla R Sigma.fst (diagramWeight M κ)`. That is, with rows
coloured by τ, it satisfies f(yβ) = ∏ β_{τ,ii}^{l(τ,i)} f(y) for upper triangular β_τ, where l(τ, i)
is the sum of `κ τ h` over i < h < M τ. -/
lemma prod_tableauPoly_mem_nabla
    {M : Φ → ℕ} {T : ∀ τ : Φ, Tableau (n' τ) (M τ) (κ τ)} :
    ∏ τ : Φ, tableauPoly R (Sigma.mk τ) (T τ) ∈ nabla R Sigma.fst (diagramWeight M κ) := by
  -- The product is the product `minorProduct` of the minors over all columns of all colours.
  let I : ColoredTableau (J := Σ τ : Φ, Σ h : Fin (M τ), Fin (κ τ h)) fst (fun j ↦ j.fst)
      (fun j ↦ j.snd.fst) :=
    fun j s ↦ ⟨⟨j.fst, T j.fst j.snd.fst j.snd.snd s⟩, rfl⟩
  have h_prod : minorProduct R I = ∏ τ : Φ, tableauPoly R (Sigma.mk τ) (T τ) := by
    simp [I, tableauPoly, minor, minorProduct, Fintype.prod_sigma]
  rw [← h_prod, diagramWeight_eq_columnWeight]
  exact minorProduct_mem_nabla I

/-- Let ι be a finite alphabet and fix a shape with `k h` columns of height h for each h < M. A
filling (`New.Tableau ι M k`) assigns to each column an h-tuple in ι, with no ordering condition.
Some finite set s of fillings satisfies two conditions: (a) over every commutative ring, the minor
products of the fillings in s form a basis of the span of all minor products; (b) for every
enumeration e of ι and every x : ι → ℂ, (Σ_{T∈s} x^T)·a_0(x) = a_λ(x), where x^T is the product of x
over the entries of T, a is the alternant `New.GL.alternant`, and λ(i) = Σ_{i<h<M} k(h). -/
lemma exists_isTableauBasis {ι : Type} [Fintype ι] {M : ℕ} {k : ℕ → ℕ} :
    ∃ s : Finset (Tableau ι M k), IsTableauBasis s := by
  classical
  -- `exists_isStdMinorFamily`, with one colour and `k h` columns of each height `h`, gives a
  -- standard family `I` of fillings: its minor products are independent and span `nabla` over
  -- every ring and satisfy the character formula. Read it as a set of fillings.
  let J : Type := Σ _ : Unit, Σ h : Fin M, Fin (k h)
  obtain ⟨ι', h_fintype, I, hI⟩ :=
    exists_isStdMinorFamily (J := J) (m := ι) 0 fst (fun j ↦ j.snd.fst)
  let fill (i : ι') : Tableau ι M k := fun h j s ↦ I i ⟨(), h, j⟩ s
  have h_prod (R : Type) [CommRing R] : tableauPoly R id ∘ fill = fun i ↦ minorProduct R (I i) :=
    funext fun i ↦ by simp [fill, J, tableauPoly, minorProduct, Fintype.prod_sigma]
  have h_indep (R : Type) [CommRing R] : LinearIndependent R (tableauPoly R id ∘ fill) := by
    rw [h_prod R]
    exact hI.linearIndependent R
  -- Independent vectors are distinct, so distinct indices give distinct fillings.
  have fill_inj : Injective fill := .of_comp (h_indep ℤ).injective
  refine ⟨univ.map ⟨fill, fill_inj⟩,
    .of_linearIndepOn_of_mem_span_of_character (fun R _ ↦ ?_) (fun R _ T ↦ ?_) ?_⟩
  · simpa using (linearIndepOn_univ_iff.mpr (h_indep R)).image_of_comp
  · -- The minor product of any filling `T` lies in `nabla` for this weight, so in the span.
    let cols_T : ColoredTableau (J := J) 0 fst (fun j ↦ j.snd.fst) :=
      fun j s ↦ ⟨T j.snd.fst j.snd.snd s, rfl⟩
    have h_tableau : tableauPoly R id T = minorProduct R cols_T := by
      simp [tableauPoly, minorProduct, cols_T, J, Fintype.prod_sigma]
    rw [h_tableau]
    simpa [← Set.range_comp, h_prod] using
      hI.nabla_le_span R (minorProduct_mem_nabla cols_T)
  · simpa [J, Fintype.prod_sigma, ← diagramWeight_eq_columnWeight, diagramWeight_apply] using
      hI.character ()

/-- Over a finite alphabet `ι`, consider the set of fillings chosen by `Classical.epsilon` (heights
below `M`, `k h` columns of height `h`), which is the set behind `BasisTableau`. This set is a
standard set: (a) over every commutative ring its minor products form a basis of the span of all
minor products; (b) for every enumeration of the rows and every x : ι → ℂ, (Σ_{T∈s} x^T)
a_0(x) = a_λ(x). Here x^T is the product of x over the entries of T, a is the alternant, and λ(i) is
the sum of k(h) over i < h < M.

A weaker form of the standard basis theorem for products of minors. The basis is chosen abstractly,
not described by standard tableaux. -/
lemma isTableauBasis_epsilon {ι : Type} [Fintype ι] {M : ℕ} {k : ℕ → ℕ} :
    IsTableauBasis (Classical.epsilon IsTableauBasis : Finset (Tableau ι M k)) :=
  Classical.epsilon_spec exists_isTableauBasis

/-- The minor products of the chosen fillings `New.BasisTableau` are linearly independent over
every ring. -/
lemma linearIndependent_basisTableau {ι : Type} [Fintype ι] {M : ℕ} {k : ℕ → ℕ}
    (R : Type) [CommRing R] :
    LinearIndependent R fun T : BasisTableau ι M k ↦ tableauPoly R id T.val := by
  -- `BasisTableau ι M k` is the subtype of the members of the chosen set.
  exact (isTableauBasis_epsilon (ι := ι) (M := M) (k := k)).linearIndepOn R

/-- The minor product of any filling is a linear combination of those of the standard fillings. -/
lemma exists_sum_basisTableau_smul_eq {ι : Type} [Fintype ι] {M : ℕ} {k : ℕ → ℕ}
    (R : Type) [CommRing R] (T : Tableau ι M k) :
    ∃ c : BasisTableau ι M k → R,
      ∑ U : BasisTableau ι M k, c U • tableauPoly R id U.val = tableauPoly R id T := by
  -- The chosen set of fillings spans all minor products.
  exact (mem_span_image_finset_iff_exists_fun R).mp (isTableauBasis_epsilon.mem_span R T)

/-- The character formula for the standard fillings: the sum of their monomials, times the
alternant of weight zero, is the alternant of the weight whose `i`-th entry counts the columns of
height greater than `i`. -/
lemma sum_basisTableau_mul_alternant {ι : Type} [Fintype ι] {M : ℕ} {k : ℕ → ℕ}
    {a : ℕ} (e : Fin a ≃ ι) (x : ι → ℂ) :
    (∑ T : BasisTableau ι M k, ∏ h : Fin M, ∏ j : Fin (k h), ∏ s : Fin h, x (T.val h j s)) *
        alternant (x ∘ e) 0 =
      alternant (x ∘ e) fun i : ℕ ↦ ∑ h ∈ Finset.Ioo i M, k h := by
  -- Read the sum over the subtype as a sum over the chosen set of fillings.
  exact (congrArg (· * _) (sum_coe_sort _ _)).trans
    (isTableauBasis_epsilon.weyl_character_formula a e x)

/-- Over any commutative ring `R`, the polynomials `nablaBasis R n κ` are linearly independent. For
a family `i` of chosen standard fillings, `nablaBasis R n κ i` is the product over places `τ` of the
minor product of `i τ` in the rows of block `τ`.

Part of the standard basis theorem for Schur (dual Weyl) modules over any ring. -/
lemma linearIndependent_nablaBasis [DecidableEq Φ] : LinearIndependent R (nablaBasis R n κ) := by
  -- Induction on the number of places. Single out a place `τ` and view polynomials in all rows as
  -- polynomials in the rows of the other places, over the polynomials in the rows of `τ`; then a
  -- basis product is a scalar (its factor at `τ`) times a basis product for the other places.
  induction hk : card Φ using Nat.strongRec generalizing Φ R with | ind k ih => ?_
  rcases isEmpty_or_nonempty Φ with hΦ | ⟨⟨τ⟩⟩
  · -- With no place there is a single, empty product, equal to `1`.
    exact .of_subsingleton' default fun r h_zero ↦ by
      simpa [nablaBasis, univ_eq_empty, ← C_mul'] using h_zero
  let P : Type := MatrixPoly (n τ) R
  let split : MatrixPoly (Σ σ, n σ) R →ₐ[R] MatrixPoly (Σ σ : {σ // σ ≠ τ}, n σ) P :=
    aeval fun (⟨σ, a⟩, j) ↦
      if hσ : σ = τ then C (X ⟨cast (congrArg n hσ) a, j⟩) else X ⟨⟨⟨σ, hσ⟩, a⟩, j⟩
  -- The factors at `τ` are independent over `R` by the choice of the standard set, the products
  -- over the other places are independent over the larger ring by induction.
  have h_card_lt : card {σ : Φ // σ ≠ τ} < k :=
    (card_subtype_lt (x := τ) fun h_ne ↦ h_ne rfl).trans_eq hk
  have h_rest : LinearIndependent P (nablaBasis P (fun σ : {σ : Φ // σ ≠ τ} ↦ n σ) fun σ ↦ κ σ) :=
    ih _ h_card_lt rfl
  -- `split` carries each basis product to the corresponding product of the two families.
  have h_split (i : WeylIndexFamily n κ) :
      split (nablaBasis R n κ i) =
        (tableauPoly R id (i τ).val : P) •
          nablaBasis P (fun σ : {σ : Φ // σ ≠ τ} ↦ n σ) (fun σ ↦ κ σ) (fun σ ↦ i σ) := by
    have h_ne (σ : {σ : Φ // σ ≠ τ}) : (σ : Φ) ≠ τ := σ.prop
    simp [P, split, nablaBasis, prod_eq_mul_prod_subtype_ne _ τ, h_ne, tableauPoly, minor, ← C_mul',
      RingHom.map_det, Matrix.map, AlgHom.map_det]
  have h_one :
      LinearIndependent R fun T : BasisTableau (n τ) (rankAt n τ) (κ τ) ↦ tableauPoly R id T.val :=
    linearIndependent_basisTableau R
  refine .of_comp split.toLinearMap
    ((linearIndependent_equiv' (piSplitAt τ _) ?_).mpr (linearIndependent_smul h_one h_rest))
  funext i
  exact (h_split i).symm

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- Over any commutative ring, the polynomial ∏_τ det(y_τ)^{e_τ} is a regular element (not a
zero divisor) of the polynomial ring. -/
lemma isRegular_detPow {e : Φ → ℕ} : IsRegular (detPow R n e) := by
  -- The involution `y ↦ 1 - y` of the polynomial ring (`1` the array of identity matrices) gives
  -- the product of determinants the constant term `1`, so that its image in the power series
  -- ring is not a zero divisor.
  let reflect : MatrixPoly (Σ τ, n τ) R →ₐ[R] MatrixPoly (Σ τ, n τ) R :=
    aeval (permArray (fun τ a ↦ rowEquivFin n τ a) - X)
  have h_reflect : Involutive reflect := fun f ↦ by
    simp [reflect, comp_aeval_apply, permArray, aeval_X_left_apply]
  have h_inj : Injective ((coeToMvPowerSeries.algHom R).comp reflect) :=
    (coe_injective _ R).comp h_reflect.injective
  rw [isRegular_iff_mem_nonZeroDivisors]
  refine mem_nonZeroDivisors_of_injective h_inj
    (MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff ?_)
  -- The constant coefficient of the image is `1`.
  simp [reflect, map_pow, map_sub, detPow, minor, AlgHom.map_det, Matrix.map,
    permArray, ← Fin.ext_iff, RingHom.map_det, ← diagonal.eq_1]

omit [Fintype Φ]
  [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- For I a tuple of |n_τ| rows of n'_τ, the substitution y ↦ zy sends the minor on rows I
(determinant of the variables in rows (τ, I a) and columns 0, …, |n_τ|−1) to det(z_τ[I, ·]) times
the minor on the rows of n_τ, both taken in the fixed enumeration `New.GL.rowEquivFin n τ` of
n_τ. -/
lemma GL.rowSubst_minor (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) (τ : Φ)
    (I : Fin (Fintype.card (n τ)) → n' τ) :
    rowSubst z (minor R fun a : Fin (Fintype.card (n τ)) ↦ ⟨τ, I a⟩) =
      det ((z τ).submatrix I (rowEquivFin n τ).symm) •
        minor R fun a : Fin (Fintype.card (n τ)) ↦ ⟨τ, (rowEquivFin n τ).symm a⟩ := by
  -- The substitution multiplies the matrix of variables on the left by the rows `I` of `z τ`.
  simp only [rowSubst, reindex_equiv (rowEquivFin n τ).symm, ← C_mul', minor, AlgHom.map_det,
    AlgHom.mapMatrix_apply, Matrix.map, of_apply, aeval_X, RingHom.map_det, ← det_mul]
  -- Both sides are the determinant of the same matrix: once entrywise, once as a product.
  change (of fun (a b : Fin (Fintype.card (n τ))) ↦ ∑ c : Fin (Fintype.card (n τ)),
        C (z τ (I a) ((rowEquivFin n τ).symm c)) *
          X ((⟨τ, (rowEquivFin n τ).symm c⟩ : Σ σ : Φ, n σ), (b : ℕ))).det =
      ((of fun (a c : Fin (Fintype.card (n τ))) ↦ C (z τ (I a) ((rowEquivFin n τ).symm c))) *
        of fun (c b : Fin (Fintype.card (n τ))) ↦
          X ((⟨τ, (rowEquivFin n τ).symm c⟩ : Σ σ : Φ, n σ), (b : ℕ))).det
  refine congrArg det (Matrix.ext fun a b ↦ ?_)
  rw [Matrix.mul_apply]
  simp

/-- Substituting y ↦ g y, for square matrices g_τ of size n_τ, multiplies the product
∏_τ det(y_τ)^{e_τ} of determinants by the scalar ∏_τ det(g_τ)^{e_τ}. -/
@[simp]
lemma rowSubst_detPow : rowSubst g (detPow R n e) = (∏ τ : Φ, (g τ).det ^ e τ) • detPow R n e := by
  simp [rowSubst_minor, mul_pow, detPow, ← C_mul', prod_mul_distrib]

variable [DecidableEq Φ]

/-- Consider polynomials over `R` in a matrix of variables whose rows, indexed by pairs (τ, row of
`n τ`), are coloured by the place τ. Let f be a Borel semi-invariant (`nabla`) whose weight is
`diagramWeight (rankAt n) κ` plus `e τ` at each column i < |n τ| of each place τ, i.e. the weight of
`κ` with `e τ` further full-height columns at τ. Then f is an `R`-linear combination of the products
`nablaBasis R n κ U * detPow R n e` over `U : WeylIndexFamily n κ`, where `detPow` is the product
over τ of the `e τ`-th powers of the determinants of the block-τ variables in the first |n τ|
columns. -/
lemma nabla_le_span_nablaBasis_mul_detPow (e : Φ → ℕ) :
    nabla R Sigma.fst (diagramWeight (rankAt n) κ +
        ∑ τ : Φ, e τ • ∑ i ∈ range (rankAt n τ), Finsupp.single (τ, i) 1) ≤
      (Fintype.linearCombination R fun U : WeylIndexFamily n κ ↦
        nablaBasis R n κ U * detPow R n e).range := by
  -- The weight is that of the columns of `κ` together with `e τ` further columns of full height at
  -- each `τ`, so the module lies in a span of products of minors on these columns. In a product
  -- the minors on the columns of `κ` expand in the standard ones, and a minor of full height is a
  -- multiple of the determinant.
  let J : Type := (Σ τ : Φ, Σ h : Fin (rankAt n τ), Fin (κ τ h)) ⊕ Σ τ : Φ, Fin (e τ)
  let colour : J → Φ := Sigma.fst ⊕ᵥ Sigma.fst
  let height : J → ℕ := (fun j ↦ j.snd.fst) ⊕ᵥ fun j ↦ rankAt n j.fst
  have h_weight : columnWeight colour height =
      diagramWeight (rankAt n) κ +
        ∑ τ : Φ, e τ • ∑ i ∈ range (rankAt n τ), Finsupp.single (τ, i) 1 := by
    simp_rw [← Fin.sum_const, ← Fintype.sum_sigma', diagramWeight_eq_columnWeight]
    exact sum_sum_type _
  obtain ⟨ι, h_fintype, I, hI⟩ : ∃ (ι : Type) (_ : Fintype ι)
      (I : ι → ColoredTableau (fst : (Σ τ : Φ, n τ) → Φ) colour height), IsStdMinorFamily I :=
    exists_isStdMinorFamily (m := Σ τ : Φ, n τ) fst colour height
  rw [← h_weight]
  refine (hI.nabla_le_span R).trans ?_
  rw [span_le, Set.range_subset_iff]
  intro i
  -- The entries of the filling `I i` are the rows `⟨colour j, T j s⟩`.
  have h_rows (j : J) (s : Fin (height j)) :
      ∃ a : n (colour j), (sigmaSubtype (colour j)).symm a = I i j s :=
    (sigmaSubtype (colour j)).symm.surjective (I i j s)
  choose T hT using h_rows
  have h_expand (τ : Φ) : ∃ a : BasisTableau (n τ) (rankAt n τ) (κ τ) → R,
      ∑ U : BasisTableau (n τ) (rankAt n τ) (κ τ), a U • tableauPoly R id U.val =
        tableauPoly R id fun h j ↦ T (.inl ⟨τ, h, j⟩) :=
    exists_sum_basisTableau_smul_eq R _
  choose a ha using h_expand
  -- A minor of full height is a multiple of the determinant (`rowSubst_minor` with `z = 1`).
  have h_full (j : Σ τ : Φ, Fin (e τ)) : ∃ b_j : R,
      (minor R fun s ↦ (⟨j.fst, T (.inr j) s⟩ : Σ τ : Φ, n τ)) =
        b_j • minor R fun s ↦ (⟨j.fst, (rowEquivFin n j.fst).symm s⟩ : Σ τ : Φ, n τ) :=
    by
    refine ⟨det ((1 : Matrix (n j.fst) (n j.fst) R).submatrix (T (.inr j))
      (rowEquivFin n j.fst).symm), ?_⟩
    exact (rowSubst_one _).symm.trans (rowSubst_minor (R := R) (fun _ ↦ 1) j.fst (T (.inr j)))
  choose b hb using h_full
  -- Multiply all these expansions together.
  rw [← funext₂ hT]
  refine ⟨fun U ↦ (∏ j, b j) * ∏ τ, a τ (U τ), ?_⟩
  have h_prod :
      (∏ τ : Φ, rename (Prod.map (Sigma.mk τ) id)
          (∑ U : BasisTableau (n τ) (rankAt n τ) (κ τ), a τ U • tableauPoly R id U.val)) *
          ∏ j : Σ τ : Φ, Fin (e τ),
            b j • minor R (fun s ↦ (⟨j.fst, (rowEquivFin n j.fst).symm s⟩ : Σ τ : Φ, n τ)) =
        (∏ τ : Φ, rename (Prod.map (Sigma.mk τ) id)
          (tableauPoly R id fun h j ↦ T (.inl ⟨τ, h, j⟩))) *
          ∏ j : Σ τ : Φ, Fin (e τ), minor R fun s ↦ (⟨j.fst, T (.inr j) s⟩ : Σ τ : Φ, n τ) := by
    simp only [ha, hb]
  -- The rows of the filling, as elements of the sigma type.
  have h_entry (τ : Φ) (t : n τ) : ((sigmaSubtype τ).symm t : Σ σ : Φ, n σ) = ⟨τ, t⟩ := rfl
  -- The left side of `h_prod` is the combination of the `nablaBasis R n κ U * detPow R n e` with
  -- the coefficients above, the right side the minor product of the filling, after unfolding `J`.
  -- `using!`: after simp the two sides differ only by `(id ∘ T j) s` against `T j s` inside a
  -- dependent pair, where simp does not rewrite.
  simpa [linearCombination_apply, ← Fin.prod_const, -prod_const, J, colour, height,
    nablaBasis, h_entry, rowEquivFin, minor, AlgHom.map_det, Matrix.map, detPow, Fintype.prod_sigma,
    minorProduct, tableauPoly, prod_univ_sum, prod_smul, sum_mul, smul_sum,
    ← mul_smul] using! h_prod

/-- The map `New.GL.nablaCombination` κ, which sends coefficients to the linear combination of the
basis minor products b_i, is injective. -/
lemma GL.nablaCombination_injective : Injective (nablaCombination (R := R) (n := n) κ) :=
  linearIndependent_nablaBasis.fintypeLinearCombination_injective

/-- The R-linear map `nablaCombination κ`, sending ξ to Σ_i ξ_i b_i with b_i the basis products of
minors `nablaBasis` (indexed by families of chosen standard fillings), has range exactly
`nablaFamily R n κ`. That is the module of Borel semi-invariant polynomials in rows (τ,a), coloured
by τ, whose weight is the partition tuple built from κ using heights below |n_τ|, over any
commutative ring R. -/
lemma range_nablaCombination : (nablaCombination κ).range = nablaFamily R n κ := by
  -- The basis products lie in `∇` (`prod_tableauPoly_mem_nabla`), and
  -- `nabla_le_span_nablaBasis_mul_detPow` with `e = 0` is the converse.
  refine le_antisymm ?_ ?_
  · rw [nablaCombination, Fintype.range_linearCombination, span_le, Set.range_subset_iff]
    exact fun i ↦ prod_tableauPoly_mem_nabla
  · -- For `e = 0` the extra weight is `0` and `detPow R n 0 = 1`.
    simpa [nablaFamily, nablaCombination] using
      nabla_le_span_nablaBasis_mul_detPow (R := R) (n := n) (κ := κ) 0

/-- For f in ∇ = `New.nablaFamily`, the coordinates chosen by `invFun` of the linear combination map
`New.GL.nablaCombination` give back f as a combination of the basis products b_i. -/
lemma sum_coords_nablaBasis {f : MatrixPoly (Sigma n) R} (hf : f ∈ nablaFamily R n κ) :
    ∑ i : WeylIndexFamily n κ, invFun (nablaCombination κ) f i • nablaBasis R n κ i = f :=
  invFun_eq (range_nablaCombination.ge hf)

/-- Over any commutative ring R and for any exponents e_τ, the polynomials b_i · ∏_τ
det(y_τ)^{e_τ}, with b_i the basis minor products for κ, are linearly independent over R. -/
lemma GL.linearIndependent_nablaBasis_mul_detPow :
    LinearIndependent R fun i : WeylIndexFamily n κ ↦ nablaBasis R n κ i * detPow R n e :=
  linearIndependent_nablaBasis.map_injOn (LinearMap.mulRight R (detPow R n e))
    isRegular_detPow.right.injOn

/-- If all coefficients of a combination of the basis products times `detPow R n e` lie in an
additive subgroup `A` of `R`, then so do the coordinates of the combination.

A consequence of the standard basis theorem for products of minors, stated for membership in an
additive subgroup A and with a determinant-power factor. -/
lemma GL.coord_mem_of_coeff_mem (A : AddSubgroup R) (e : Φ → ℕ) {f : MatrixPoly (Σ τ : Φ, n τ) R}
    {x : WeylIndexFamily n κ → R}
    (h_sum : ∑ j : WeylIndexFamily n κ, x j • (nablaBasis R n κ j * detPow R n e) = f)
    (h_coeff : ∀ d : (Σ τ : Φ, n τ) × ℕ →₀ ℕ, f.coeff d ∈ A) (i : WeylIndexFamily n κ) :
      x i ∈ A := by
  -- `A` need not be an ideal, so pass to the ring `Q = ℤ ⊕ R ⧸ A` with `(R ⧸ A)² = 0`. The products
  -- have integer coefficients and stay independent over `Q`, and the classes of the `x j` form a
  -- linear relation among them.
  have h_int (S : Type) [CommRing S] (j : WeylIndexFamily n κ) (d : (Σ τ, n τ) × ℕ →₀ ℕ) :
      (nablaBasis S n κ j * detPow S n e).coeff d =
        ((nablaBasis ℤ n κ j * detPow ℤ n e).coeff d : ℤ) := by
    simpa using (nablaBasis ℤ n κ j * detPow ℤ n e).coeff_map (algebraMap ℤ S) d
  let Q : Type := TrivSqZeroExt ℤᵐᵒᵖ (TensorProduct ℤ ℤᵐᵒᵖ (R ⧸ A))
  let φ : R ⧸ A → Q := TrivSqZeroExt.inrHom ℤᵐᵒᵖ _ ∘ TensorProduct.mk ℤ ℤᵐᵒᵖ (R ⧸ A) 1
  have h_rel : ∑ j, φ (x j) • (nablaBasis Q n κ j * detPow Q n e) = 0 := by
    ext1 d
    -- The class of `f.coeff d` in `R ⧸ A` is zero; expand `f` by `h_sum` and apply `φ`.
    have h_class : ((f.coeff d : R) : R ⧸ A) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr (h_coeff d)
    simpa [φ, Q, ← h_sum, coeff_sum, h_int R, h_int Q, ← zsmul_eq_mul'] using congrArg φ h_class
  have h_zero : φ (x i) = 0 :=
    linearIndependent_iff.mp (linearIndependent_nablaBasis_mul_detPow e) (fun j ↦ φ (x j)) h_rel i
  -- `φ` is injective: its value at `x i` is zero only if the class of `x i` is.
  have h_class_zero : ((x i : R) : R ⧸ A) = 0 := by simpa [φ, Q, TrivSqZeroExt.ext_iff] using h_zero
  exact (QuotientAddGroup.eq_zero_iff _).mp h_class_zero

/-! ### Characterisation of Schur matrices and diagonal matrices -/

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- A family of row types fits itself: no height lies strictly between |n_τ| and |n_τ|. -/
@[simp]
lemma FitsRanks.refl : FitsRanks n n κ := by grind

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- For equal row families no extra power of the determinants occurs. -/
@[simp]
lemma schurDetExp_self : schurDetExp n n κ = 0 := funext (by simp [schurDetExp])

omit [(τ : Φ) → DecidableEq (n' τ)] in
/-- Let M be a matrix whose row i gives coordinates of b'_i(zy) in the family
b_j(y)·∏_τ det(y_τ)^{d_τ}, with b, b' the basis products `New.nablaBasis` for the rows n and n' and
d = `New.schurDetExp`. Then M is the Schur matrix S_κ(z): the family is linearly independent, so
these coordinates are unique. -/
lemma GL.schur_eq_of_expansion {M : Matrix (WeylIndexFamily n' κ) (WeylIndexFamily n κ) R}
    {z : ∀ τ : Φ, Matrix (n' τ) (n τ) R}
    (h_expand : ∀ i : WeylIndexFamily n' κ,
      ∑ j : WeylIndexFamily n κ, M i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
        rowSubst z (nablaBasis R n' κ i)) :
    schur κ z = M := by
  -- Row `i` of either matrix holds coordinates of the same polynomial in an independent family.
  funext i
  apply (linearIndependent_nablaBasis_mul_detPow _).fintypeLinearCombination_injective
  exact (sum_schur_smul_eq_rowSubst_of_exists κ z i ⟨M i, h_expand i⟩).trans (h_expand i).symm

/-- The Schur matrix of diagonal matrices diag(x_τ) is diagonal; its entry at i is the product of
x_τ over all entries of the fillings i_τ. -/
@[local simp]
lemma schur_diagonal_eq_prod :
    schur κ (fun τ : Φ ↦ diagonal (x τ)) =
      diagonal fun i : WeylIndexFamily n κ ↦
        ∏ τ : Φ, ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), ∏ s : Fin h, x τ ((i τ).val h j s) := by
  -- Each minor of `b_i` is multiplied by the product of the `x` over its rows, and the
  -- determinant factor is trivial.
  refine schur_eq_of_expansion fun i ↦ ?_
  simp [diagonal, nablaBasis, rowSubst, ← prod_mul_distrib, tableauPoly, minor, detPow, ← C_mul',
    ← det_mul_column, AlgHom.map_det, Matrix.map]

/-- Weyl's character formula over ℂ, for polynomial weights and with the Vandermonde denominator
cleared. Let e_τ enumerate the a_τ rows at each place τ, let x_τ be complex numbers indexed by these
rows, and let λ = `New.diagramWeight`, so λ(τ, k) = Σ_{k<h<|n_τ|} κ_τ(h). The trace of the Schur
matrix `schur κ` of the diagonal matrices diag(x_τ), times the product over τ of the Vandermonde
determinants of x_τ ∘ e_τ, is the product over τ of the determinants of the matrices with (i, j)
entry x_τ(e_τ(i))^{λ(τ, a_τ − 1 − j) + j}. -/
lemma weyl_character {a : Φ → ℕ} (e : ∀ τ : Φ, Fin (a τ) ≃ n τ) (x : ∀ τ : Φ, n τ → ℂ) :
    (schur κ fun τ : Φ ↦ Matrix.diagonal (x τ)).trace *
        ∏ τ : Φ, (vandermonde (x τ ∘ e τ)).det =
      ∏ τ : Φ, det (of fun i j : Fin (a τ) ↦
        x τ (e τ i) ^ (diagramWeight (rankAt n) κ (τ, j.rev) + j)) := by
  -- At each place the character identity is part of the choice of the standard set. By
  -- `schur_diagonal_eq_prod` the trace is the product over the places of the sums over these sets.
  have h_place (τ : Φ) :
      (∑ T : BasisTableau (n τ) (rankAt n τ) (κ τ),
          ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), ∏ s : Fin h, x τ (T.val h j s)) *
          (vandermonde (x τ ∘ e τ)).det =
        det (of fun i j : Fin (a τ) ↦
          x τ (e τ i) ^ (diagramWeight (rankAt n) κ (τ, j.rev) + j)) := by
    have h_card : a τ = rankAt n τ := by simpa using card_congr (e τ)
    -- The alternant of weight zero is the Vandermonde determinant, the other one that on the right.
    simpa [alternant, vandermonde, h_card, diagramWeight_apply] using
      sum_basisTableau_mul_alternant (M := rankAt n τ) (k := κ τ) (e τ) (x τ)
  have h_trace : (schur κ fun τ : Φ ↦ Matrix.diagonal (x τ)).trace =
      ∏ τ : Φ, ∑ T : BasisTableau (n τ) (rankAt n τ) (κ τ),
        ∏ h : Fin (rankAt n τ), ∏ j : Fin (κ τ h), ∏ s : Fin h, x τ (T.val h j s) := by
    rw [schur_diagonal_eq_prod, trace_diagonal, Fintype.prod_sum]
  rw [h_trace, ← prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ ↦ h_place τ

/-- The Schur matrix of a family of identity matrices is the identity matrix. -/
@[simp]
lemma schur_one (hg : ∀ τ : Φ, g τ = 1) : schur κ g = 1 := by
  -- With `g = 1` the substitution is the identity and there is no determinant factor.
  refine schur_eq_of_expansion fun i ↦ ?_
  simp [hg, rowSubst, Matrix.one_apply, detPow, minor, aeval_X_left_apply]

/-- The Schur matrix of a tuple of diagonal matrices diag(x_τ) is diagonal, with i-th entry ∏_τ
∏_a x_τ(a)^{w}, where w is the number of entries equal to a in the filling i_τ. -/
lemma schur_diagonal :
    schur κ (fun τ : Φ ↦ Matrix.diagonal (x τ)) =
      Matrix.diagonal fun i : WeylIndexFamily n κ ↦
        ∏ τ : Φ, ∏ a : n τ, x τ a ^ tableauWeight i τ a := by
  -- (`sum_boole` is removed: it undoes `card_filter`)
  simp [tableauWeight, prod_comm (γ := n _), card_filter, -sum_boole, ← prod_pow_eq_pow_sum]

/-! ### Base change and multiplicativity -/

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
/-- If the sizes fit κ, the weight of κ in the larger ranks is its weight in the smaller ranks plus
that of the power `schurDetExp n n' κ` of the determinants. -/
lemma GL.diagramWeight_eq_of_fitsRanks (h : FitsRanks n n' κ) :
    diagramWeight (rankAt n') κ =
      diagramWeight (rankAt n) κ +
        ∑ τ : Φ,
          schurDetExp n n' κ τ • ∑ i ∈ Finset.range (rankAt n τ), Finsupp.single ⟨τ, i⟩ 1 := by
  -- At `τ` the heights from `rankAt n τ` to `rankAt n' τ - 1` are new; by the hypothesis `h` only
  -- the height `rankAt n τ` can have columns, and `schurDetExp n n' κ τ` counts them.
  rw [diagramWeight, diagramWeight, ← sum_add_distrib]
  refine sum_congr rfl fun τ _ ↦ ?_
  obtain ⟨h_le, h_zero_between⟩ :
      rankAt n τ ≤ rankAt n' τ ∧ ∀ k ∈ Ioo (rankAt n τ) (rankAt n' τ), κ τ k = 0 := h τ
  grind [zero_smul, schurDetExp, sum_eq_ite (rankAt n τ), sum_range_add_sum_Ico _ h_le]

omit [(τ : Φ) → DecidableEq (n' τ)] in
/-- Assume `FitsRanks n n' κ`: for every τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|.
Let b = `nablaBasis` for `n`, b' = `nablaBasis` for `n'`, and let d τ be κ_τ(|n_τ|) if
|n_τ| < |n'_τ| and 0 otherwise. Then for matrices z_τ of size n'_τ × n_τ, row `i` of the Schur
matrix `schur κ z` expresses b'_i(zy) as Σ_j S_{ij} b_j(y) ∏_τ det(y_τ)^{d τ}, where
y_{(τ,b),k} ↦ Σ_a z_τ(b,a) y_{(τ,a),k} defines zy and y_τ is the block of rows (τ, ·) and the first
|n_τ| columns. -/
@[simp ← low] lemma sum_schur_smul_nablaBasis (h : FitsRanks n n' κ)
    (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) (i : WeylIndexFamily n' κ) :
    ∑ j : WeylIndexFamily n κ, schur κ z i j •
      (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
      rowSubst z (nablaBasis R n' κ i) := by
  -- The substituted polynomial is again semi-invariant, of the weight of the products on the left.
  have h_mem : rowSubst z (nablaBasis R n' κ i) ∈ nabla R Sigma.fst (diagramWeight (rankAt n) κ +
      ∑ τ : Φ, schurDetExp n n' κ τ • ∑ k ∈ range (rankAt n τ), Finsupp.single (τ, k) 1) := by
    rw [← diagramWeight_eq_of_fitsRanks h, nablaBasis]
    exact rowSubst_mem_nabla z prod_tableauPoly_mem_nabla
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (nabla_le_span_nablaBasis_mul_detPow _ h_mem)
  exact sum_schur_smul_eq_rowSubst_of_exists κ z i
    ⟨w, by simpa [Fintype.linearCombination_apply] using hw⟩

/-- Base change: assume `FitsRanks n n' κ`, that is, for every τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. Then for a ring homomorphism φ, the Schur matrix of φ(z) (φ applied entrywise)
is φ applied entrywise to the Schur matrix S_κ(z). Here S_κ(z) = `schur κ z` has as row i the
coordinates of b'_i(zy) in the family b_j(y) ∏_τ det(y_τ)^{d τ}, where b and b' are the `nablaBasis`
for `n` and `n'`, and d = `schurDetExp n n' κ`. -/
@[simp ←]
lemma schur_map (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    [FunLike F R S] [RingHomClass F R S] (φ : F) :
    schur κ (fun τ : Φ ↦ (z τ).map φ) = (schur κ z).map φ := by
  -- Apply `φ` to the coefficients in the expansion `sum_schur_smul_nablaBasis`.
  refine schur_eq_of_expansion fun i ↦ ?_
  simpa [rowSubst, map_aeval_eq_aeval_map_map, -map_aeval, minor, ← C_mul', RingHom.map_det] using
    congrArg (MvPolynomial.map (φ : R →+* S)) (sum_schur_smul_nablaBasis h_fits z i)

/-- Entrywise form of `New.schur_map`: φ applied to an entry of S_κ(z) is the same entry of the
Schur matrix of the matrices with entries φ(z_τ(a, b)). -/
lemma map_schur (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    [FunLike F R S] [RingHomClass F R S] (φ : F) (i : WeylIndexFamily n' κ)
      (j : WeylIndexFamily n κ) :
    φ (schur κ z i j) = schur κ (fun τ : Φ ↦ of fun (a : n' τ) (b : n τ) ↦ φ (z τ a b)) i j := by
  rw [← Matrix.map_apply (f := φ), ← schur_map h_fits z φ]
  rfl

/-- Assume `FitsRanks n n' κ`: at every place τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. Let S_κ(z) = `schur κ z` be the matrix whose row i holds the coordinates of
b'_i(z y) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}, where b and b' are `nablaBasis` for n and n', and
d is `schurDetExp`. Then S_κ(g z) = S_κ(g) S_κ(z) for square matrices g_τ of size n'_τ and matrices
z_τ of size n'_τ × n_τ over R. -/
@[simp ←]
lemma schur_mul_left (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    (g : ∀ τ : Φ, Matrix (n' τ) (n' τ) R) :
    (schur κ fun τ : Φ ↦ g τ * z τ) = schur κ g * schur κ z := by
  -- Substitute `g`, then `z` (`rowSubst_rowSubst`), and expand both times by
  -- `sum_schur_smul_nablaBasis`.
  refine schur_eq_of_expansion fun i ↦ ?_
  rw [← rowSubst_rowSubst, ← sum_schur_smul_nablaBasis FitsRanks.refl g i]
  simpa [schurDetExp_self, detPow_zero, ← sum_schur_smul_nablaBasis h_fits z,
    Matrix.mul_apply, sum_smul, smul_sum, mul_smul] using sum_comm

/-- Assume `FitsRanks n n' κ`: at every place τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. Let S_κ(z) = `schur κ z` be the matrix whose row i holds the coordinates of
b'_i(z y) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}, where b and b' are `nablaBasis` for n and n', and
d_τ = `schurDetExp n n' κ τ` is κ_τ(|n_τ|) if |n_τ| < |n'_τ| and 0 otherwise. Then S_κ(z g) = ∏_τ
det(g_τ)^{d_τ} · S_κ(z) S_κ(g) for z_τ of size n'_τ × n_τ and square g_τ of size n_τ over R. -/
lemma schur_mul_right (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    schur κ (fun τ : Φ ↦ z τ * g τ) =
      (∏ τ : Φ, (g τ).det ^ schurDetExp n n' κ τ) • (schur κ z * schur κ g) := by
  -- Substitute `z`, then `g`, and expand both times by `sum_schur_smul_nablaBasis`; `g` multiplies
  -- the power of the determinants in the first expansion by the scalar (`rowSubst_detPow`).
  refine schur_eq_of_expansion fun i ↦ ?_
  calc ∑ j : WeylIndexFamily n κ, ((∏ τ : Φ, (g τ).det ^ schurDetExp n n' κ τ) •
          (schur κ z * schur κ g)) i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ))
      = ∑ k : WeylIndexFamily n κ, schur κ z i k •
          rowSubst g (nablaBasis R n κ k * detPow R n (schurDetExp n n' κ)) := by
        simpa [mul_sum, mul_left_comm, Matrix.mul_apply, sum_smul, sum_mul, smul_sum,
          ← mul_smul] using sum_comm
    _ = rowSubst g (rowSubst z (nablaBasis R n' κ i)) := by
        simp only [← sum_schur_smul_nablaBasis h_fits z i, map_sum, map_smul]
    _ = rowSubst (fun τ : Φ ↦ z τ * g τ) (nablaBasis R n' κ i) := rowSubst_rowSubst ..

/-- Assume `FitsRanks n n' κ`: at every place τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for
|n_τ| < h < |n'_τ|. For matrices z_τ of size n'_τ × n_τ, row i of the Schur matrix `schur κ z` holds
the coordinates of b'_i(z y) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}, where b and b' are
`nablaBasis` for n and n', and d is `schurDetExp n n' κ`. Its (i, j) entry equals the product over τ
of the (i τ, j τ) entries of the one-place Schur matrices, namely those of the families over `Unit`
with data κ τ and z τ. -/
lemma schur_apply_eq_prod (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    (i : WeylIndexFamily n' κ) (j : WeylIndexFamily n κ) :
    schur κ z i j =
      ∏ τ : Φ, schur (fun _ : Unit ↦ κ τ) (fun _ : Unit ↦ z τ) (fun _ : Unit ↦ i τ)
        fun _ : Unit ↦ j τ := by
  -- Check that the product of the one-place entries satisfies the expansion that characterises the
  -- Schur matrix (`schur_eq_of_expansion`): it is the product over `τ` of the one-place expansions.
  let S (τ : Φ) : Matrix (WeylIndexFamily (fun _ : Unit ↦ n' τ) fun _ : Unit ↦ κ τ)
      (WeylIndexFamily (fun _ : Unit ↦ n τ) fun _ : Unit ↦ κ τ) R :=
    schur (fun _ : Unit ↦ κ τ) fun _ : Unit ↦ z τ
  suffices h_schur : schur κ z = fun (i : WeylIndexFamily n' κ) (j : WeylIndexFamily n κ) ↦
      ∏ τ : Φ, S τ (fun _ : Unit ↦ i τ) fun _ : Unit ↦ j τ from congrFun₂ h_schur i j
  refine schur_eq_of_expansion fun i ↦ ?_
  have one_place (τ : Φ) :
      ∑ a : BasisTableau (n τ) (rankAt n τ) (κ τ), S τ (fun _ ↦ i τ) (fun _ ↦ a) •
          (nablaBasis R (fun _ : Unit ↦ n τ) (fun _ ↦ κ τ) (fun _ ↦ a) *
            detPow R _ (schurDetExp (fun _ ↦ n τ) (fun _ ↦ n' τ) fun _ ↦ κ τ)) =
        rowSubst (fun _ : Unit ↦ z τ) (nablaBasis R (fun _ ↦ n' τ) (fun _ ↦ κ τ) fun _ ↦ i τ) :=
    ((piUnique _).symm.sum_comp _).trans (sum_schur_smul_nablaBasis (fun _ : Unit ↦ h_fits τ)
      (fun _ : Unit ↦ z τ) fun _ : Unit ↦ i τ)
  -- Move each expansion into the variables of colour `τ`, multiply, and expand the product of sums.
  have h_prod := prod_congr rfl fun (τ : Φ) (_ : τ ∈ univ) ↦
    congrArg (rename (Prod.map (fun p : (Σ _ : Unit, n τ) ↦ (⟨τ, p.snd⟩ : Σ σ : Φ, n σ)) id))
      (one_place τ)
  simpa [nablaBasis, rowSubst, prod_mul_distrib, tableauPoly, minor, detPow, ← C_mul',
    AlgHom.map_det, Matrix.map, prod_univ_sum] using! h_prod

/-- If the sizes fit κ, scaling z_τ by t_τ scales S_κ(z) by the product of the t_τ^{|κ_τ|}, where
|κ_τ| = Σ_{h < |n'_τ|} h κ_τ(h) is the number of boxes at τ. -/
lemma schur_smul (h_fits : FitsRanks n n' κ) (t : Φ → R) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) :
    (schur κ fun τ : Φ ↦ t τ • z τ) =
      (∏ τ : Φ, t τ ^ ∑ i ∈ range (rankAt n' τ), i * κ τ i) • schur κ z := by
  -- A scalar is a diagonal matrix, whose Schur matrix is again a scalar.
  simp [smul_eq_diagonal_mul, schur_mul_left h_fits, sum_range, ← pow_mul, ← prod_pow_eq_pow_sum]

end New

/-! ## Schur representations twisted by determinants -/

/-- The action on the Weyl module of a dominant weight μ, given as (κ, e): κ_τ(h) = μ_h − μ_{h+1} is
the number of columns of height h < |n_τ| at the place τ, and the integer e_τ is the last entry of
μ_τ. The monoid homomorphism sends a family g of invertible matrices g_τ ∈ GL(n_τ, R) to ∏_τ
det(g_τ)^{e_τ} times the Schur matrix S_κ(g). -/
noncomputable def New.weylRep {Φ R : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ]
    {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] (κ : Φ → ℕ → ℕ)
    (e : Φ → ℤ) :
    ((τ : Φ) → GL (n τ) R) →* Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R :=
  MonoidHom.mk
    { toFun := fun g : ∀ τ : Φ, GL (n τ) R ↦
        (∏ τ : Φ, (g τ).det ^ e τ) • schur κ fun τ : Φ ↦ (g τ : Matrix (n τ) (n τ) R)
      map_one' := by simp }
    (by simp [mul_zpow, smul_mul_smul, Finset.prod_mul_distrib])

/-!
## Weights of the basis, evaluation vectors, the highest basis vector, one-row shapes

Weights of the standard basis b_i = `New.nablaBasis` of the module ∇ = `New.nablaFamily`.

* `New.sum_tableauWeight_le`: the weight of each b_i is dominated by the partition
  λ = `New.diagramWeight`.
* `New.schur_mulVec_weylEval`: the Schur matrix of z carries the vector of values b_j(y)
  (`New.weylEval`) to the vector of values at zy, up to a power of determinants of y.
* `New.map_nablaBasis_eq_map_weylKernel_mul_weylEval`: a linear form that sees only basis vectors of
  highest weight is determined by its value on the kernel `New.weylKernel`.
-/

namespace New

variable {Φ : Type}
  {R : Type} [CommRing R] [Fintype Φ]
  {n : Φ → Type} {n' : Φ → Type _}
  {κ : Φ → ℕ → ℕ} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)]

open MvPolynomial Finset Matrix «GL» Equiv Fintype

/-- Let i be a family of chosen standard fillings (`New.WeylIndexFamily`). At a place τ, the column
j of height h of the filling i_τ is an h-tuple of rows; its entries are distinct. -/
lemma tableau_col_injective [DecidableEq Φ] (i : WeylIndexFamily n κ) (τ : Φ) (h : Fin (rankAt n τ))
    (j : Fin (κ τ h)) :
    Function.Injective ((i τ).val h j) := by
  -- A repeated entry gives a minor with two equal rows, so b_i = 0 over ℤ; but the basis products
  -- are linearly independent, hence not zero.
  intro s s' h_eq
  by_contra h_ne
  have h_minor : minor (m := Σ τ : Φ, n τ) ℤ (Sigma.mk τ ∘ (i τ).val h j) = 0 :=
    det_zero_of_row_eq h_ne (by ext b; simp [h_eq])
  apply (linearIndependent_nablaBasis (R := ℤ)).ne_zero i
  simp only [nablaBasis, tableauPoly]
  exact prod_eq_zero (mem_univ τ) (prod_eq_zero (mem_univ h) (prod_eq_zero (mem_univ j) h_minor))

omit [Fintype Φ] in
/-- Let i be a family of chosen standard fillings (`New.WeylIndexFamily`) and τ a place. The number
`New.tableauWeight i τ a` of entries of i_τ equal to the row a, summed over all rows a, is the
number of boxes Σ_{h<|n_τ|} h·κ_τ(h). -/
lemma sum_tableauWeight (i : WeylIndexFamily n κ) (τ : Φ) :
    ∑ a : n τ, tableauWeight i τ a = ∑ h ∈ range (rankAt n τ), h * κ τ h := by
  simp [sum_comm, sum_range, mul_comm, tableauWeight, sum_card_fiberwise_eq_card_filter]

/-- Let i be a family of chosen standard fillings (`New.WeylIndexFamily`) and A a set of rows at the
place τ. Write λ = `New.diagramWeight`, so λ(τ,k) = Σ_{k<h<|n_τ|} κ_τ(h).
(a) The number of entries of i_τ lying in A (counted by `New.tableauWeight`) is at most
Σ_{k<|A|} λ(τ,k).
(b) If equality holds, every entry of a column of height h ≤ |A| lies in A. -/
lemma sum_tableauWeight_le [DecidableEq Φ] (i : WeylIndexFamily n κ) (τ : Φ) (A : Finset (n τ)) :
    -- (a)
    ∑ a ∈ A, tableauWeight i τ a ≤ ∑ k ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, k⟩ ∧
    -- (b)
    (∑ k ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, k⟩ ≤ ∑ a ∈ A, tableauWeight i τ a →
     ∀ (h : Fin (rankAt n τ)) (j : Fin (κ τ h)) (s : Fin h),
       (h : ℕ) ≤ #A → (i τ).val h j s ∈ A) := by
  -- Count column by column: a column of height `h` has distinct entries, so at most `min #A h` of
  -- them lie in `A`. Summed over the columns, the two sides are the two sides of the claim.
  let count (p : Σ h : Fin (rankAt n τ), Fin (κ τ h)) : ℕ := #{s | (i τ).val p.fst p.snd s ∈ A}
  have h_col (p : Σ h : Fin (rankAt n τ), Fin (κ τ h)) : count p ≤ min #A p.fst := by
    apply le_min
    · -- the entries of the column that lie in `A` are distinct elements of `A`
      exact card_le_card_of_injOn _ (fun s hs ↦ by simpa using hs)
        (tableau_col_injective i τ p.fst p.snd).injOn
    · exact card_finset_fin_le _
  have h_left : ∑ a ∈ A, tableauWeight i τ a = ∑ p, count p := by
    simp [count, Fintype.sum_sigma, sum_comm, tableauWeight, sum_card_fiberwise_eq_card_filter]
  have h_right : ∑ k ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, k⟩ =
      ∑ p : Σ h : Fin (rankAt n τ), Fin (κ τ h), min #A p.fst := by
    -- (`mem_range` is removed: with it simp applies `sum_comm` back and forth)
    simp [-mem_range, mul_comm, Fintype.sum_sigma, sum_range (n := rankAt n τ), sum_comm,
      diagramWeight, Finsupp.single_apply, ite_and]
  rw [h_left, h_right]
  refine ⟨sum_mono h_col, ?_⟩
  intro h_ge h j s h_le
  -- In the case of equality every column attains its bound, which is `h` when `h ≤ #A`.
  have h_all : ∀ p ∈ (univ : Finset (Σ h : Fin (rankAt n τ), Fin (κ τ h))),
      count p = min #A p.fst :=
    (sum_eq_sum_iff_of_le fun p _ ↦ h_col p).mp ((sum_mono h_col).antisymm h_ge)
  have h_full : count ⟨h, j⟩ = #(univ : Finset (Fin h)) := by
    simpa [h_le] using h_all ⟨h, j⟩ (mem_univ _)
  exact card_filter_eq_iff.mp h_full s (mem_univ s)

omit [Fintype Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, Fintype (n' τ)]
  [∀ τ : Φ, DecidableEq (n' τ)] in
/-- Let z_τ be matrices of size n'_τ×n_τ, y an array over R with rows (τ, a), and f a polynomial
in an array with rows (τ, b). Then `New.rowSubst z f` evaluated at y is f evaluated at the product
array zy, whose entry at row (τ, b) and column k is Σ_a z_τ(b,a)·y((τ,a),k). -/
lemma GL.eval_rowSubst (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R) (y : ((τ : Φ) × n τ) × ℕ → R)
    (f : MatrixPoly ((τ : Φ) × n' τ) R) :
    eval y (rowSubst z f) = eval (fun x : ((τ : Φ) × n' τ) × ℕ ↦
      ∑ a : n x.1.fst, z x.1.fst x.1.snd a * y (⟨x.1.fst, a⟩, x.2)) f := by
  -- Evaluation after a substitution evaluates the substituted polynomials.
  simp only [rowSubst, ← aeval_eq_eval, comp_aeval_apply]
  simp

/-- Assume `FitsRanks n n' κ`: for every τ, |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|.
Let z_τ be matrices of size n'_τ × n_τ, let y be an array with rows (τ, a), and let zy be the array
with entries (zy)_{(τ,b),k} = Σ_a z_τ(b,a) y_{(τ,a),k}. Write ev_y for the vector of values b_j(y)
of the basis products of minors `nablaBasis` (`weylEval`) and d τ = κ_τ(|n_τ|) if |n_τ| < |n'_τ|,
else 0. Then ∏_τ det(y_τ)^{d τ} · S_κ(z) ev_y = ev_{zy}, where y_τ is the square block of the first
|n_τ| columns of y at τ and S_κ(z) = `schur κ z` is the matrix expressing each b'_i(zy) in the
b_j(y) ∏_τ det(y_τ)^{d τ}. -/
lemma schur_mulVec_weylEval [DecidableEq Φ]
    (h_fits : FitsRanks n n' κ) (z : (τ : Φ) → Matrix (n' τ) (n τ) R)
    (y : ((τ : Φ) × n τ) × ℕ → R) :
    (detPow R n (schurDetExp n n' κ)).eval y • schur κ z *ᵥ weylEval n κ y =
      weylEval n' κ fun x : ((τ : Φ) × n' τ) × ℕ ↦
        ∑ a : n x.1.fst, z x.1.fst x.1.snd a * y (⟨x.1.fst, a⟩, x.2) := by
  -- Evaluate at `y` the expansion `b'_i(zy) = Σ_j S(z)_{ij} b_j(y) ∏ det(y_τ)^{d_τ}` of
  -- `sum_schur_smul_nablaBasis`, one row `i` at a time.
  funext i
  simpa [weylEval, GL.eval_rowSubst, mulVec, dotProduct, mul_sum, mul_rotate'] using
    congrArg (eval y) (sum_schur_smul_nablaBasis h_fits z i)

/-- Suppose the sizes fit κ (`New.FitsRanks`) and the determinant exponents `New.schurDetExp` are
all zero. Then the Schur matrix S_κ(z) carries the evaluation vector `New.weylEval` at y to the
evaluation vector at the product array zy. -/
lemma schur_mulVec_weylEval_of_schurDetExp_eq_zero [DecidableEq Φ] (h_fits : FitsRanks n n' κ)
    (h_detExp : schurDetExp n n' κ = 0) (z : (τ : Φ) → Matrix (n' τ) (n τ) R)
    (y : ((τ : Φ) × n τ) × ℕ → R) :
    schur κ z *ᵥ weylEval n κ y =
      weylEval n' κ fun x : ((τ : Φ) × n' τ) × ℕ ↦
        ∑ a : n x.1.fst, z x.1.fst x.1.snd a * y (⟨x.1.fst, a⟩, x.2) := by
  simp [← schur_mulVec_weylEval h_fits, h_detExp]

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- For every array y over R with rows (τ, a), the kernel `New.weylKernel` at y lies in the module
∇ = `New.nablaFamily` of Borel semi-invariants: it is a substitution of the product of leading
minors `New.highestPoly`. -/
lemma weylKernel_mem_nablaFamily (y : ((τ : Φ) × n τ) × ℕ → R) :
    weylKernel n κ y ∈ nablaFamily R n κ := by
  rw [weylKernel, highestPoly]
  exact rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla

/-- Let e_τ enumerate the rows at each place τ, and let y be the permutation array of e
(`New.permArray`): y((τ,a),k) is 1 if e_τ(a) = k and 0 otherwise. The kernel `New.weylKernel` at
y, evaluated at y, equals 1. -/
lemma GL.eval_weylKernel_permArray (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) :
    (weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))).eval
      (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) =
      (1 : R) := by
  -- At y, the substituted array of the kernel is the identity matrix, whose leading minors are 1.
  simp [← eq_symm_apply, ← diagonal.eq_1, weylKernel, rowSubst, permArray, Fin.val_inj, highestPoly,
    tableauPoly, minor, AlgHom.map_det, Matrix.map, RingHom.map_det]

/-- Let e_τ enumerate the rows at each place τ, and let y be the permutation array of e
(`New.permArray`). Let i be a family of chosen standard fillings (`New.WeylIndexFamily`) in which
every entry of a column of height k of i_τ has position below k in the enumeration e_τ. Then the
basis vector b_i = `New.nablaBasis` is its value b_i(y) (`New.weylEval`) times the kernel
`New.weylKernel` at y. -/
lemma nablaBasis_eq_weylEval_smul_weylKernel_of_lt (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (i : WeylIndexFamily n κ)
    (h_lt : ∀ (τ : Φ) (k : Fin (rankAt n τ)) (j : Fin (κ τ k)) (s : Fin k),
      e τ ((i τ).val k j s) < k) :
    nablaBasis R n κ i =
      (weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) i : R) •
        weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) := by
  -- The rows of each minor are among the first `k` rows, so the minor is its value at y times the
  -- leading minor of the substituted array, by multiplying determinants.
  -- (`prod_const` is left out: it turns the equal factors into a power before the determinants are
  -- multiplied)
  simp [nablaBasis, ← C_mul', ← prod_mul_distrib, ← det_mul, -prod_const, tableauPoly, minor,
    weylEval, RingHom.map_det, Matrix.map, permArray, weylKernel, rowSubst, Fin.val_inj,
    highestPoly, AlgHom.map_det]
  -- For each column, the matrix of variables is the product of the 0/1 matrix of the positions of
  -- its rows (the value at y) and the matrix of the substituted array.
  congr!
  ext a b
  -- In entry `(a, b)` of the product only the position of row `a` of the column contributes; it
  -- is below the height by `h_lt`.
  rw [Matrix.mul_apply, sum_eq_ite ⟨_, h_lt ..⟩]
  · -- the term at that position is the variable of entry `(a, b)`
    aesop
  · -- the terms at the other positions are zero
    aesop

omit [(τ : Φ) → DecidableEq (n τ)] in
/-- Let e_τ enumerate the rows at each place τ, and let y be the permutation array of e
(`New.permArray`). If, for a family i of chosen standard fillings, some entry of a column of height
k of i_τ has position at least k in the enumeration e_τ, then the value b_i(y) of the basis vector
(`New.weylEval`) is zero. -/
lemma weylEval_permArray_eq_zero_of_le (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (i : WeylIndexFamily n κ) (τ : Φ) (k : Fin (rankAt n τ)) (j : Fin (κ τ k)) (s : Fin k)
    (h_le : k ≤ e τ ((i τ).val k j s)) :
    weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) i = (0 : R) := by
  -- Row `s` of the minor of column `(τ, k, j)` is zero at `y`: its entry in a column `b < k` is
  -- 1 only if the position of the row is `b`, but that position is at least `k`.
  have h_minor : eval (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))
      (minor (m := Σ τ : Φ, n τ) R (Sigma.mk τ ∘ (i τ).val k j)) = 0 := by
    rw [minor, RingHom.map_det]
    apply det_eq_zero_of_row_eq_zero s
    intro b
    have h_ne : (e τ ((i τ).val k j s) : ℕ) ≠ b := by omega
    simp [permArray, h_ne]
  simp only [weylEval, nablaBasis, tableauPoly, map_prod]
  exact prod_eq_zero (mem_univ τ) (prod_eq_zero (mem_univ k) (prod_eq_zero (mem_univ j) h_minor))

/-- Let e_τ enumerate the rows at each place τ, let i be a family of chosen standard fillings
(`New.WeylIndexFamily`) with basis vector b_i = `New.nablaBasis`, and let φ be an R-linear form on
polynomials. Suppose that φ(b_i) ≠ 0 only when, at each row (τ, a), the number of entries of i_τ
equal to a (`New.tableauWeight`) is at least λ(τ, e_τ(a)), where λ = `New.diagramWeight`. Then
φ(b_i) = φ(k)·b_i(y), where y is the permutation array of e (`New.permArray`), k is the kernel
`New.weylKernel` at y, and b_i(y) = `New.weylEval`. -/
lemma map_nablaBasis_eq_map_weylKernel_mul_weylEval [DecidableEq Φ]
    (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    (i : WeylIndexFamily n κ) (φ : MatrixPoly (Σ τ : Φ, n τ) R →ₗ[R] R)
    (h_wt :
      φ (nablaBasis R n κ i) ≠ 0 →
      ∀ (τ : Φ) (a : n τ), diagramWeight (rankAt n) κ (τ, e τ a) ≤ tableauWeight i τ a) :
    φ (nablaBasis R n κ i) =
      φ (weylKernel n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ))) *
        weylEval n κ (permArray fun (τ : Φ) (a : n τ) ↦ (e τ a : ℕ)) i := by
  by_cases! h_lt : ∀ (τ : Φ) (k : Fin (rankAt n τ)) (j : Fin (κ τ k)) (s : Fin k),
      e τ ((i τ).val k j s) < k
  · -- Every column of height `k` has its entries among the first `k` rows.
    rw [nablaBasis_eq_weylEval_smul_weylKernel_of_lt e i h_lt, map_smul, smul_eq_mul, mul_comm]
  obtain ⟨τ, k, j, s, h_le⟩ := h_lt
  rw [weylEval_permArray_eq_zero_of_le e i τ k j s h_le, mul_zero]
  -- If `φ` saw this basis product, equality would hold in `sum_tableauWeight_le` for the set `A`
  -- of the first `k` rows, so the entry `s` would lie in `A`, against `h_le`.
  by_contra h_ne
  let A : Finset (n τ) := (Iio k).map (e τ).symm.toEmbedding
  have h_ge : ∑ l ∈ range #A, diagramWeight (rankAt n) κ ⟨τ, l⟩ ≤ ∑ a ∈ A, tableauWeight i τ a := by
    grw [← h_wt h_ne]
    simp [A, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, diagramWeight, Finsupp.single_apply,
      ite_and]
  have h_mem : (i τ).val k j s ∈ A := (sum_tableauWeight_le i τ A).2 h_ge k j s (by simp [A])
  exact h_le.not_gt (by simpa [A] using h_mem)

/-- One place (Φ = Unit) with a row type m of size |m| > 1, and column multiplicities k with
k(1) = a and k(h) = 0 for 1 < h < |m|: the shape is one row of length a. `New.WeylIndexFamily`
indexes the basis `nablaBasis` b, and S_k(z) (`New.schur`) is the matrix whose row i holds chosen
coordinates of b_i(z y) in the family b_j(y)·det(y)^d. Let q : σ ≃ m be a bijection. Then there is a
bijection φ from these basis indices to the exponents of degree a in σ (`New.Monomials`) such that,
for all complex c and square z, c^a·S_k(z)_{ij} is the (φ j, φ i) entry of the a-th symmetric power
`New.symPowMatrix` of c·zᵀ reindexed along q. -/
lemma exists_equiv_schur_one_row_eq_symPowMatrix {a : ℕ} {m σ : Type} [Fintype m] [DecidableEq m]
    [Fintype σ] [DecidableEq σ] {k : ℕ → ℕ} (q : σ ≃ m) (h_card : 1 < Fintype.card m)
    (h_k_eq : ∀ i : ℕ, i > 0 → i < Fintype.card m → k i = if i = 1 then a else 0) :
    ∃ φ : WeylIndexFamily (fun _ : Unit ↦ m) (fun () ↦ k) ≃ Monomials σ a,
      ∀ (c : ℂ) (z : Matrix m m ℂ) (i j : WeylIndexFamily (fun _ : Unit ↦ m) fun _ : Unit ↦ k),
        c ^ a * schur (fun () ↦ k) (fun _ ↦ z) i j =
          symPowMatrix a (c • zᵀ.submatrix q q) (φ j) (φ i) := by
  -- Only columns of height `1` count, so each basis vector is a monomial of degree `a` in the
  -- first column of variables, and all such monomials occur. In this basis `schur` is the matrix
  -- of a linear substitution on forms of degree `a`.
  have h_size : ∑ h ∈ range (card m), h * k h = a := by grind [sum_eq_ite 1]
  -- The exponent at `b` counts entries equal to `q b`. The total degree is the number of boxes.
  let φ (i : WeylIndexFamily (fun _ : Unit ↦ m) fun () ↦ k) : Monomials σ a :=
    ⟨∑ h, ∑ j, ∑ s, Finsupp.single (q.symm ((i ()).val h j s)) 1, by
      simp [sum_comm (γ := σ), ← h_size, sum_range, mul_comm]⟩
  have hφ (i) : nablaBasis ℂ (fun _ ↦ m) (fun () ↦ k) i =
      aeval (R := ℂ) (fun b ↦ X (⟨(), q b⟩, 0)) (monomial (φ i) 1) := by
    -- Unfolded, the left side is the product of the minors of the columns, the right side the
    -- product of the variables `X (entry, 0)` over all entries.
    simp only [φ, nablaBasis, monomial_sum_one, ← X.eq_1, tableauPoly, minor, univ_unique,
      prod_singleton, map_prod, aeval_X]
    -- Compare column by column, by the height of the column: minors of size `0` and `1` are the
    -- products of their variables, and there are no columns of height at least `2`.
    congr! with ⟨_ | _ | _⟩
    · -- height `0`: the empty determinant and the empty product
      simp [univ_eq_empty]
    · -- height `1`: a `1 × 1` determinant
      simp
    · -- height at least `2`: `k h = 0` by `h_k_eq`
      grind [cases Fin]
  -- Distinct basis vectors are distinct monomials.
  have h_inj : Function.Injective φ := fun i j h_eq ↦
    (linearIndependent_nablaBasis (R := ℂ)).injective (by rw [hφ, hφ, h_eq])
  have h_surj : Function.Surjective φ := by
    rintro ⟨d, hd⟩
    -- A monomial of degree `a` in the first column is semi-invariant of the right weight.
    have h_mem : aeval (R := ℂ) (fun b ↦ X (⟨(), q b⟩, 0)) (monomial d 1) ∈
        nablaFamily ℂ (fun _ ↦ m) fun () ↦ k := by
      -- Only columns of height `1` count, `k 1 = a` of them: the weight is `a` at `((), 0)`.
      have h_wt : diagramWeight (rankAt fun _ : Unit ↦ m) (fun () ↦ k) =
          Finsupp.single ((), 0) a := by
        simp only [diagramWeight, Fintype.sum_unique, PUnit.default_eq_unit]
        rw [sum_eq_ite 1]
        · simp [h_card, h_k_eq 1 one_pos h_card]
        · intro h h_mem_range h_ne_one
          rcases Nat.eq_zero_or_pos h with h_zero | h_pos
          · simp [h_zero]
          · simp [h_k_eq h h_pos (mem_range.mp h_mem_range), h_ne_one]
      simp_all [mem_nabla, monomial_eq, borelMul, mul_pow, prod_pow_eq_pow_sum,
        prod_mul_distrib, mul_comm]
    -- so it is a combination `Σ_i c_i b_i` of the basis vectors, which are the monomials `φ i`.
    by_contra h_miss
    -- Rename the first-column variables back to σ and take the coefficient of the missing monomial.
    have h_coeff := congrArg
      (fun g ↦ (rename (fun x : ((_ : Unit) × m) × ℕ ↦ q.symm x.1.snd) g).coeff d)
      (sum_coords_nablaBasis h_mem)
    have h_ne : ∀ i, (φ i : σ →₀ ℕ) ≠ d := fun i h_eq ↦ h_miss ⟨i, Subtype.ext h_eq⟩
    -- With the coefficients computed, `h_coeff` reads `0 = 1`.
    simp [hφ, rename_aeval, aeval_X_left_apply, h_ne] at h_coeff
  have h_bij : Function.Bijective φ := ⟨h_inj, h_surj⟩
  refine ⟨.ofBijective φ h_bij, ?_⟩
  intro c z i j
  -- The scalar `c` comes out of the Schur matrix as `c ^ a` (`schur_smul`).
  have h_scalar : c ^ a * schur (fun () ↦ k) (fun _ ↦ z) i j =
      schur (fun () ↦ k) (fun () ↦ c • z) i j := by simp [schur_smul, h_size]
  rw [h_scalar]
  -- By `schur_eq_of_expansion`, the Schur matrix is the matrix that expands the substituted basis.
  apply congrFun₂ (schur_eq_of_expansion fun i ↦ ?_)
  let f : MvPolynomial σ ℂ := linSubst (c • zᵀ.submatrix q q) (monomial (φ i).val 1)
  have h_expand : ∑ β : Monomials σ a, f.coeff β • monomial β 1 = f :=
    sum_monomials_eq_of_isHomogeneous ((φ i).isHomogeneous_linSubst _)
  -- Substitute the first column of variables into this expansion of `f`.
  have h_subst := congrArg
    (aeval (R := ℂ) (fun b ↦ X (R := ℂ) ((⟨(), q b⟩ : Σ _ : Unit, m), 0))) h_expand
  -- Reindex the sum over monomials by the bijection `φ`.
  rw [← h_bij.sum_comp (fun β : Monomials σ a ↦ f.coeff β • monomial (β : σ →₀ ℕ) 1)] at h_subst
  simpa [f, hφ, comp_aeval_apply, monomial_eq, reindex_equiv q, symPowMatrix,
    linSubst, rowSubst] using h_subst

end New

/-! ## Continuity of Schur matrices -/

/-- Over a topological ring R, the Schur matrix S_κ(g) = `New.schur κ g` of a family g of square
matrices g_τ of size n_τ is continuous in g: by base change (`New.schur_map`) each of its entries is
a polynomial in the entries of g. -/
@[fun_prop]
lemma New.continuous_schur {Φ : Type} {n : Φ → Type} {κ : Φ → ℕ → ℕ} {R : Type} [Fintype Φ]
    [DecidableEq Φ] [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (schur κ : (∀ τ : Φ, Matrix (n τ) (n τ) R) →
      Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R) := by
  -- By base change (`schur_map`), the entries of `schur κ g` are the polynomial entries of the
  -- Schur matrix of the generic matrices `GL.genericMatrixAt R n`, evaluated at the entries of `g`.
  have h_eval (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
      (schur κ (GL.genericMatrixAt R n)).map (GL.evalMatrix g) = schur κ g := by
    simp [← schur_map .refl]
  refine .congr (continuous_matrix fun i j ↦ ?_) h_eval
  simp only [Matrix.map_apply, MvPolynomial.eval_eq]
  fun_prop
