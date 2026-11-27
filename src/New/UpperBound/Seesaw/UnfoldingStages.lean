module

public import Lib.Weil.Periods.StringPowers
public import New.UpperBound.Seesaw.AdmissibleCombinations
import Mathlib.Tactic.Linter.Style
public import Lib.Weil.DualPair.FiniteAction
public import Lib.Weil.Periods.PointLattice
import Lib.Weil.Periods.GradedLattice
public import New.UpperBound.Seesaw.EdgePairEvaluation
public import Lib.Weil.Periods.ConstantTerm
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import New.UpperBound.Objects.RowChain
public import New.UpperBound.Size.ShortColumns
import Lib.Adelic.Unitary.RationalPoints
import Lib.Adelic.Unitary.WeakApproximation
import Lib.General.Algebra.MultivariatePolynomials
import Lib.General.Measure.IntegralOperators
import Lib.Weil.CompactLift.DefiniteThetaLift
import Lib.Weil.Periods.Unfolding
import New.OneLift.ComparisonOperator.ExchangeData
import New.UpperBound.Objects.CharactersAtLevel
import New.UpperBound.Seesaw.LevelIdeles

section
section
/-!
# The standard lattice of a graded space, line by line

Let `Y` grade the hermitian space `V` by an index set `X ⊕ Unit` of grade `0` and a string of `s`
basis vectors, and let the finite frame of `V` span the same lattice `Λ` as the standard basis
`New.gradedLatticeBasis`. The intersection `Λ⁻` of `Λ` with the span of the string and its
projection `Λ⁺` to this span are sums of lines.

* `New.Grading.SpansLattice.isGraded`: `Λ` is graded.
* `New.Grading.SpansLattice.mem_latticeMinus_iff`, `New.Grading.SpansLattice.mem_latticePlus_iff`:
  the generators of the lines; they differ only by `N⁻¹` at the middle vector of the string.
* `New.Grading.SpansLattice.stringSum_mem_latticeMinus_iff`,
  `New.Grading.SpansLattice.stringSum_mem_latticePlus_iff`: the generators on the lines of the
  vectors `𝔢 ^ i`, for the scale `u = (a / ā) ^ ⌊(s + 2) / 2⌋` and when the constant `c` of `Y`
  has the valuations of `a ā`.
* `New.Grading.SpansLattice.map_stringMapFin_latticePlus`: under the same conditions, the shift to
  a space with a string of `s - 1` vectors and the same constant `c` takes `Λ⁺` onto `a Λ'⁻`.
* `New.Grading.SpansLattice.odd_of_notMem_latticeMinus`: a vector of `Λ⁺` outside `Λ⁻` exists
  only for odd `s`.
* `New.Grading.SpansLattice.exists_place_generates_of_notMem_latticeMinus`: such a vector
  generates `Λ⁺` over `Λ⁻` at some place above `N`.

The results on `Λ⁺` assume that `N` is split and squarefree (`IsSplitSquarefree P N π`).

Notions from other files:
* `Y.SpansLattice a π u`: the lattice `Λ = V.lattice 1` has the standard basis
  `New.gradedLatticeBasis Y.indexEquiv a π u` over the integral finite adeles `Ô E`. This basis
  consists of the vectors of `X`, the multiples of the string vectors `b` by `lineIdele a u b`, and
  the last vector `e₀` of `X ⊕ Unit`, replaced for odd `s` by `e₀ / π̄ + u z / (π π̄)`, where `z`
  is the middle vector of the string.
* `IsSplitSquarefree P N π`: `N = π π̄`, where `π` is a uniformiser at the places of `P`, a unit
  elsewhere, and no place of `P` has its conjugate in `P`.
* `Y.stringSum t`: the vector `∑ t i • 𝔢 ^ i`, where `𝔢 ^ i = Y.stringPower i` is a multiple of
  the string vector `i` by an element of `E`.
* `Y.genericConst`: the constant `c` of the grading, a nonzero element of `E` fixed by conjugation.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

@[expose] public section

open Matrix Pointwise Valued

noncomputable section

namespace New

open Seesaw

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  {Y : Grading V N (X ⊕ Unit) s} {Y' : Grading V' N (X' ⊕ Unit) (s - 1)} {a π : (𝔸f E)ˣ}
  {u : unitary (𝔸f E)} {P : Finset (FinPlace E)}

/-- The diagonal entry of `New.gradedLatticeBasis` at the string vector `b`, as an idele: `u` for
odd `s`; for even `s` it is `u a⁻¹` on the first half of the string and `u ā` on the second half.
It generates the part of `Λ⁻` on the line of this vector. -/
def lineIdele (a : (𝔸f E)ˣ) (u : unitary (𝔸f E)) (b : Fin s) : (𝔸f E)ˣ :=
  Unitary.toUnits u * if Odd s then 1 else if 2 * b.val < s then a⁻¹ else star a

/-- The idele `a ^ (s - i) ā ^ (-1 - i)`. The docstrings of the membership criteria below write
`𝔩_i` for the fractional ideal that it generates. -/
def powerIdele (a : (𝔸f E)ˣ) (s i : ℕ) : (𝔸f E)ˣ := a ^ (s - i : ℤ) * star a ^ (-1 - i : ℤ)

lemma powerIdele_eq_mul (hs : 0 < s) (i : ℕ) : powerIdele a s i = a * powerIdele a (s - 1) i := by
  rw [powerIdele, powerIdele, show (s - i : ℤ) = 1 + ((s - 1 : ℕ) - i : ℤ) by omega,
    _root_.zpow_one_add, mul_assoc]

/-- Multiplying `powerIdele a s i = a ^ (s - i) ā ^ (-1 - i)` by `(a ā) ^ n` adds `n` to both
exponents. -/
lemma powerIdele_mul_zpow (i : ℕ) (n : ℤ) : powerIdele a s i * (a * star a) ^ n =
    a ^ (s - i + n : ℤ) * star a ^ (-1 - i + n : ℤ) := by
  rw [powerIdele, mul_zpow, mul_mul_mul_comm, ← _root_.zpow_add, ← _root_.zpow_add]

lemma toUnits_divStar_pow (k : ℕ) :
    Unitary.toUnits (divStar a ^ k) = a ^ (k : ℤ) * star a ^ (-k : ℤ) := by
  rw [map_pow, show Unitary.toUnits (divStar a) = a * (star a)⁻¹ from Units.ext (coe_divStar a),
    ← zpow_natCast, mul_zpow, _root_.inv_zpow']

/-- Let `s` be the number of vectors in a string, indexed by `b : Fin s`, and `a` a finite idele.
For the scale `u = (a / ā) ^ ⌊(s + 2) / 2⌋`, where `divStar a = a / ā`, the idele `lineIdele a u b`
(which is `u` for odd `s`, and `u a⁻¹` or `u ā` on the two halves of the string for even `s`) is
`powerIdele a s b = a ^ (s - b) ā ^ (-1 - b)` times a power of `a ā`. -/
lemma lineIdele_divStar_pow (b : Fin s) :
    lineIdele a (divStar a ^ ((s + 2) / 2)) b = powerIdele a s b *
      (a * star a) ^ (b - (if 2 * b.val < s then s else s - 1 : ℤ) / 2 : ℤ) := by
  set k : ℕ := (s + 2) / 2 with hk
  set n : ℤ := b - (if 2 * b.val < s then s else s - 1 : ℤ) / 2 with hn
  -- Both sides are a power of `a` times a power of `ā`; compare the exponents in each case.
  rw [lineIdele, toUnits_divStar_pow, powerIdele_mul_zpow]
  by_cases hs : Odd s
  · have hs_mod : s % 2 = 1 := Nat.odd_iff.1 hs
    obtain ⟨h_left, h_right⟩ : (s - b + n : ℤ) = k ∧ (-1 - b + n : ℤ) = -k := by omega
    rw [ite_eq_left hs, h_left, h_right, mul_one]
  have hs_mod : s % 2 = 0 := Nat.not_odd_iff.1 hs
  by_cases hb : 2 * b.val < s
  · obtain ⟨h_left, h_right⟩ : (s - b + n : ℤ) = k - 1 ∧ (-1 - b + n : ℤ) = -k := by omega
    simp [hs, hb, h_left, h_right, _root_.zpow_sub_one, mul_right_comm]
  · obtain ⟨h_left, h_right⟩ : (s - b + n : ℤ) = k ∧ (-1 - b + n : ℤ) = -k + 1 := by omega
    simp [hs, hb, h_left, h_right, _root_.zpow_add_one, mul_assoc]

lemma eq_rev_iff (b : Fin s) : b = b.rev ↔ 2 * b.val + 1 = s := by
  rw [Fin.ext_iff, Fin.val_rev]
  omega

lemma odd_of_eq_rev {b : Fin s} (hb : b = b.rev) : Odd s :=
  ⟨b.val, ((eq_rev_iff b).1 hb).symm⟩

lemma eq_of_eq_rev {b b' : Fin s} (hb : b = b.rev) (hb' : b' = b'.rev) : b = b' := by
  rw [eq_rev_iff] at hb hb'
  exact Fin.ext (by omega)

open scoped Classical in
/-- Let `N = π π̄`, with `π` a uniformiser at the places of `P` and a unit elsewhere, and no place
of `P` conjugate to a place of `P`. Then `N` is a uniformiser at the places of `P` and their
conjugates, and a unit elsewhere. -/
lemma Seesaw.IsSplitSquarefree.v_algebraMap (hπ : IsSplitSquarefree P N π) (w : FinPlace E) :
    v (algebraMap E (𝔸f E) N w) = if w ∈ P ∨ star w ∈ P then WithZero.exp (-1) else 1 := by
  rw [hπ.algebraMap_eq_mul_star, finAdele_mul_apply, map_mul, v_star_apply, hπ.v_apply,
    hπ.v_apply]
  by_cases hw : w ∈ P <;> simp +contextual [hw, hπ.star_notMem w]

/-- Under `IsSplitSquarefree P N π` the element `N = π π̄` is integral, being a uniformiser or a
unit at every place. -/
lemma Seesaw.IsSplitSquarefree.algebraMap_mem_Ô (hπ : IsSplitSquarefree P N π) :
    algebraMap E (𝔸f E) N ∈ Ô E := by
  refine mem_Ô.2 fun w ↦ ?_
  rw [hπ.v_algebraMap]
  split_ifs <;> simp [← WithZero.exp_zero]

omit [Fintype X] in
/-- The grading `Y` indexes a basis of a hermitian space through `Y.indexEquiv`, with a string of
`s` vectors `b : Fin s` of grade `s - 1 - 2 b`; `N` is the element of `E` in its Gram matrix, and
its constant `c = Y.genericConst` is assumed to have the valuation `v` of `a ā` at every finite
place `w` of `E`. The vector `𝔢 ^ i` is a multiple of the string vector `i` by an element of `E`,
and `Y.stringSum t = ∑ t i • 𝔢 ^ i`. The claim: a coordinate of this vector at the string vector
`b` lies in the fractional ideal of `lineIdele a u b`, where `u = (a / ā) ^ ⌊(s + 2) / 2⌋` and
`divStar a = a / ā`, if and only if `t b` lies in that of `powerIdele a s b`, times `N⁻¹` in
negative grade (`s ≤ 2 b`). The same holds with both sides multiplied by any adele `r`. -/
lemma Grading.lineIdele_inv_mul_stringSum_mem_iff
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w))
    (r : 𝔸f E) (t : ℕ → 𝔸f E) (b : Fin s) :
    r * ((lineIdele a (divStar a ^ ((s + 2) / 2)) b)⁻¹.val *
        Y.stringSum t (Y.indexEquiv (.inr b))) ∈ Ô E ↔
      r * (if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) *
        ((powerIdele a s b)⁻¹.val * t b) ∈ Ô E := by
  rw [stringSum_apply_inr, lineIdele_divStar_pow]
  set n : ℤ := b - (if 2 * b.val < s then s else s - 1 : ℤ) / 2 with hn
  have h_val (w : FinPlace E) : v (algebraMap E (𝔸f E) (Y.powerCoeff b) w) =
      v (((if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) * ((a * star a) ^ n).val) w) := by
    have h_unit : ((a * star a) ^ n).val w = (a.val * star a.val) w ^ n :=
      map_zpow ((evalAt w).toMonoidHom.comp (Units.coeHom (𝔸f E))) (a * star a) n
    rw [finAdele_mul_apply, h_unit, map_mul, map_zpow₀, ← hc]
    split_ifs with hb <;> simp [powerCoeff, hn, hb]
  -- At each place the valuation of `(a ā) ^ n` cancels.
  have h_cancel (w : FinPlace E) :
      v ((r * ((powerIdele a s b * (a * star a) ^ n)⁻¹.val *
          (algebraMap E (𝔸f E) (Y.powerCoeff b) * t b))) w) =
        v ((r * (if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) *
          ((powerIdele a s b)⁻¹.val * t b)) w) := by
    simp only [finAdele_mul_apply, map_mul, h_val, idele_inv_apply_and_ne_zero, Units.val_mul,
      map_inv₀]
    have h_ne : v (((a * star a) ^ n).val w) ≠ 0 := by simp [idele_inv_apply_and_ne_zero]
    field_simp
  simp only [mem_Ô, h_cancel]

omit [DecidableEq ι] in
/-- The coordinates with index in `X ⊕ Unit` of a combination of the vectors of
`New.gradedLatticeBasis`: only the last one is rescaled, by `π̄⁻¹`, and only for odd `s`. -/
lemma gradedLatticeBasis_mulVec_apply_inl (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) (c : ι → 𝔸f E)
    (i : X ⊕ Unit) :
    (gradedLatticeBasis e a π u *ᵥ c) (e (.inl i)) =
      (if Odd s ∧ i = .inr () then (star π)⁻¹.val else 1) * c (e (.inl i)) := by
  rw [gradedLatticeBasis]
  by_cases hs : Odd s <;> cases i <;>
    simp [hs, submatrix_mulVec_equiv, fromBlocks_mulVec, mulVec_diagonal]

omit [DecidableEq ι] in
/-- The string coordinates of a combination of the vectors of `New.gradedLatticeBasis`: the
coordinate of `gradedLatticeBasis e a π u *ᵥ c` at the string vector `b` is `lineIdele a u b` times
the coefficient `c` at `b`. For the middle vector, with `b = b.rev`, there is an added term:
`u (π̄ π)⁻¹` times the coefficient `c` at the last index `.inr ()` of `X ⊕ Unit`. -/
lemma gradedLatticeBasis_mulVec_apply_inr (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) (c : ι → 𝔸f E) (b : Fin s) :
    (gradedLatticeBasis e a π u *ᵥ c) (e (.inr b)) =
      (if b = b.rev then u.val * (star π * π)⁻¹.val else 0) * c (e (.inl (.inr ()))) +
        (lineIdele a u b).val * c (e (.inr b)) := by
  simp [gradedLatticeBasis, lineIdele, mulVec, dotProduct, ← e.sum_comp, diagonal_apply,
    apply_ite Units.val]

namespace Grading.SpansLattice

omit [Fintype X] in
/-- Suppose `hL : Y.SpansLattice a π u`, that is, the lattice `V.lattice 1` is spanned over `Ô E` by
the columns of `gradedLatticeBasis Y.indexEquiv a π u`. Then every vector `y : ι → 𝔸f E` has
coordinates `c` in this basis. Moreover, `y` lies in `V.lattice 1` if and only if every `c i` lies
in `Ô E`. -/
lemma exists_gradedLatticeBasis_mulVec_eq (hL : Y.SpansLattice a π u) (y : ι → 𝔸f E) :
    ∃ c : ι → 𝔸f E, gradedLatticeBasis Y.indexEquiv a π u *ᵥ c = y ∧
      (y ∈ V.lattice 1 ↔ ∀ i : ι, c i ∈ Ô E) := by
  obtain ⟨k, hk, h_frame⟩ : ∃ k ∈ intGL ι (Ô E),
      V.xFin.val = gradedLatticeBasis Y.indexEquiv a π u * k.val := hL
  obtain ⟨hk_int, hk_inv⟩ : IsIntMatrix (Ô E) k.val ∧ IsIntMatrix (Ô E) k⁻¹.val := mem_intGL.1 hk
  refine ⟨k.val *ᵥ V.xFin⁻¹.val *ᵥ y, ?_, ?_⟩
  · rw [mulVec_mulVec, ← h_frame, mulVec_mulVec, Units.mul_inv, one_mulVec]
  · rw [Space.mem_lattice, OneMemClass.coe_one, mul_one]
    refine ⟨hk_int.mulVec, fun hc i ↦ ?_⟩
    simpa only [mulVec_mulVec, Units.inv_mul_cancel_left] using hk_inv.mulVec hc i

/-- The hypothesis `hL` says that `Λ` has, over the integral finite adeles `Ô E`, the standard basis
attached to the ideles `a`, `π` and the unitary scale `u`: the vectors of `X`, the string vectors
`b` times `lineIdele a u b`, and the last vector `e₀` of `X ⊕ Unit`, replaced for odd `s` by
`e₀ / π̄ + u z / (π π̄)`, with `z` the middle vector of the string. So `y` lies in `Λ` if and only
if three conditions hold, on its coordinates at `X`, at the last index, and on the string. The only
condition that links two coordinates glues the last index to the middle, the `b` with
`b = b.rev`. -/
lemma mem_lattice_iff {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u) :
    y ∈ V.lattice 1 ↔
      (∀ i : X, y (Y.indexEquiv (.inl (.inl i))) ∈ Ô E) ∧
      (if Odd s then star π.val else 1) * y (Y.indexEquiv (.inl (.inr ()))) ∈ Ô E ∧
      ∀ b : Fin s, (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) -
        (if b = b.rev then π⁻¹.val * y (Y.indexEquiv (.inl (.inr ()))) else 0) ∈ Ô E := by
  -- The three expressions are the coordinates `c` of `y` in the basis.
  obtain ⟨c, hc, h_mem⟩ : ∃ c : ι → 𝔸f E, gradedLatticeBasis Y.indexEquiv a π u *ᵥ c = y ∧
      (y ∈ V.lattice 1 ↔ ∀ i : ι, c i ∈ Ô E) := hL.exists_gradedLatticeBasis_mulVec_eq y
  set y₀ : 𝔸f E := y (Y.indexEquiv (.inl (.inr ()))) with hy₀
  set c₀ : 𝔸f E := c (Y.indexEquiv (.inl (.inr ())))
  have h_first (i : X) : y (Y.indexEquiv (.inl (.inl i))) = c (Y.indexEquiv (.inl (.inl i))) := by
    simp [← hc, gradedLatticeBasis_mulVec_apply_inl]
  have h_last : (if Odd s then star π.val else 1) * y₀ = c₀ := by
    rw [hy₀, ← hc, gradedLatticeBasis_mulVec_apply_inl]
    by_cases hs : Odd s <;> simp [c₀, hs, ← mul_assoc, ← star_mul]
  have h_line (b : Fin s) : (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) -
      (if b = b.rev then π⁻¹.val * y₀ else 0) = c (Y.indexEquiv (.inr b)) := by
    have hy_inr : y (Y.indexEquiv (.inr b)) = (if b = b.rev then u.val * (star π * π)⁻¹.val
        else 0) * c₀ + (lineIdele a u b).val * c (Y.indexEquiv (.inr b)) := by
      rw [← hc, gradedLatticeBasis_mulVec_apply_inr]
    rw [hy_inr, mul_add, Units.inv_mul_cancel_left]
    by_cases hb : b = b.rev
    · have hu : (lineIdele a u b).val = u.val := by simp [lineIdele, odd_of_eq_rev hb]
      have h_inv : (star π * π)⁻¹.val * star π.val = π⁻¹.val := by simp [mul_assoc, ← star_mul]
      have h_glue : (lineIdele a u b)⁻¹.val * (u.val * (star π * π)⁻¹.val * c₀) = π⁻¹.val * y₀ :=
        calc _ = (star π * π)⁻¹.val * c₀ := by rw [← hu, mul_assoc, Units.inv_mul_cancel_left]
          _ = (star π * π)⁻¹.val * (star π.val * y₀) := by
              rw [← h_last, ite_eq_left (odd_of_eq_rev hb)]
          _ = π⁻¹.val * y₀ := by rw [← mul_assoc, h_inv]
      rw [ite_eq_left hb, ite_eq_left hb, h_glue, add_sub_cancel_left]
    · simp [hb]
  simp only [h_mem, h_first, h_last, h_line, Y.indexEquiv.surjective.forall, Sum.forall,
    Unique.forall_iff, and_assoc, c₀]

/-- The grading `Y` of the hermitian space `V` gives each basis vector an integer grade: `0` on
`X ⊕ Unit` and `s - 1 - 2 b` at the vector `b` of the string of length `s`. If the lattice
`V.lattice 1` has the standard basis for `a`, `π`, `u` (the basis vectors rescaled, except that for
odd `s` the last vector of `X ⊕ Unit` is combined with the middle string vector), then it contains
the part in each grade of each of its vectors, since both combined vectors have grade `0`. -/
lemma isGraded (hL : Y.SpansLattice a π u) : Y.IsGraded (V.lattice 1) := by
  intro d y hy
  have h_proj (i : ι) : Y.gradeProj d y i = if Y.gradeOf i = d then y i else 0 := by
    simp [gradeProj, mulVec_diagonal]
  rw [hL.mem_lattice_iff] at hy ⊢
  obtain ⟨h_first, h_last, h_line⟩ := hy
  simp only [h_proj, gradeOf_inl, gradeOf_inr]
  refine ⟨fun i ↦ ?_, ?_, fun b ↦ ?_⟩
  · simp [ite_mem, h_first i]
  · rw [mul_ite, mul_zero]
    exact ite_mem.2 ⟨fun _ ↦ h_last, fun _ ↦ zero_mem _⟩
  · specialize h_line b
    by_cases hb : b = b.rev
    · have hb_val : 2 * b.val + 1 = s := (eq_rev_iff b).1 hb
      have h_grade : (s - 1 - 2 * b.val : ℤ) = 0 := by omega
      rw [ite_eq_left hb] at h_line ⊢
      by_cases hd : 0 = d <;> simp [h_grade, hd, h_line]
    · rw [ite_eq_right hb, sub_zero] at h_line ⊢
      simp [mul_ite, ite_mem, h_line]

/-- Let the lattice be spanned by `New.gradedLatticeBasis`. Its intersection
`Λ⁻ = Y.latticeMinus 1` with the span of the string, onto which `Y.stringProj` projects, is the sum
of its lines: the multiples of the string vector `b` by the fractional ideal of
`lineIdele a u b`. -/
lemma mem_latticeMinus_iff {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u) :
    y ∈ Y.latticeMinus 1 ↔ Y.stringProj y = y ∧
      ∀ b : Fin s, (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) ∈ Ô E := by
  rw [mem_latticeMinus, and_comm, hL.mem_lattice_iff]
  refine and_congr_right fun hy ↦ ?_
  simp [stringProj_eq_self_iff.1 hy]

/-- Let `Λ = V.lattice 1` have the standard basis for the ideles `a`, `π` and the unitary scale `u`,
in which the string vector `b` is multiplied by `lineIdele a u b` and, for odd `s`, the last vector
of `X ⊕ Unit` is combined with the middle one. Let `N = π π̄` be split and squarefree, `P` being the
places of `π`. Then the projection `Λ⁺ = Y.latticePlus 1` of `Λ` by `Y.stringProj` to the span of
the string is the sum of its lines: the multiples of the string vector `b` by the fractional ideal
of `lineIdele a u b`, times `N⁻¹` at the middle vector, the `b` with `b = b.rev`. -/
lemma mem_latticePlus_iff {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) :
    y ∈ Y.latticePlus 1 ↔ Y.stringProj y = y ∧ ∀ b : Fin s,
      (if b = b.rev then algebraMap E (𝔸f E) N else 1) *
        ((lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b))) ∈ Ô E := by
  constructor
  · intro hy
    refine ⟨stringProj_eq_of_mem_latticePlus hy, fun b ↦ ?_⟩
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ V.lattice 1, Y.stringProj z = y := mem_latticePlus.1 hy
    obtain ⟨-, h_last, h_line⟩ := hL.mem_lattice_iff.1 hz
    specialize h_line b
    rw [stringProj_apply_inr]
    by_cases hb : b = b.rev
    · rw [ite_eq_left hb] at h_line ⊢
      rw [ite_eq_left (odd_of_eq_rev hb)] at h_last
      have h_star_eq : star π.val = algebraMap E (𝔸f E) N * π⁻¹.val := by
        rw [hπ.algebraMap_eq_mul_star, mul_comm, Units.inv_mul_cancel_left]
      rw [h_star_eq, mul_assoc] at h_last
      simpa only [mul_sub, sub_add_cancel] using
        add_mem (mul_mem hπ.algebraMap_mem_Ô h_line) h_last
    · simpa [hb] using h_line
  · rintro ⟨hy, h_line⟩
    have hy_zero := stringProj_eq_self_iff.1 hy
    -- Let `η` be the middle coordinate divided by its generator, or `0` for even `s`. The
    -- coordinate `π η` at the last index of `X ⊕ Unit` glues `y` to a vector `z` of the lattice.
    let η : 𝔸f E := ∑ b : Fin s with b = b.rev,
      (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b))
    have hη (b : Fin s) (hb : b = b.rev) :
        η = (lineIdele a u b)⁻¹.val * y (Y.indexEquiv (.inr b)) :=
      Finset.sum_eq_single_of_mem b (by simpa using hb) fun b' hb' h_ne ↦
        (h_ne (eq_of_eq_rev (by simpa using hb') hb)).elim
    have hη_mem : (if Odd s then star π.val else 1) * (π.val * η) ∈ Ô E := by
      rw [← mul_assoc, Finset.mul_sum]
      refine sum_mem fun b hb_mem ↦ ?_
      have hb : b = b.rev := by simpa using hb_mem
      rw [ite_eq_left (odd_of_eq_rev hb), mul_comm (star π.val), ← hπ.algebraMap_eq_mul_star]
      simpa only [ite_eq_left hb] using h_line b
    let z : ι → 𝔸f E := Function.update y (Y.indexEquiv (.inl (.inr ()))) (π.val * η)
    have hz : z ∈ V.lattice 1 := by
      refine hL.mem_lattice_iff.2 ⟨fun i ↦ by simp [z, hy_zero],
        by simpa only [z, Function.update_self] using hη_mem, fun b ↦ ?_⟩
      by_cases hb : b = b.rev
      · simp [z, ite_eq_left hb, hη b hb]
      · simpa [z, hb] using h_line b
    refine mem_latticePlus.2 ⟨z, hz, funext fun i ↦ ?_⟩
    obtain ⟨i | b, rfl⟩ := Y.indexEquiv.surjective i <;>
      simp [z, stringProj_apply_inl, stringProj_apply_inr, hy_zero]

/-- The grading `Y` of the hermitian space `V` has a string of `s` basis vectors; `𝔢 ^ i` is a
multiple of the string vector `i` by an element of `E` and has grade `s - 1 - 2 i`, and `N` is the
element of `E` in the Gram matrix. Let the lattice `Λ = V.lattice 1` have the standard basis of
`gradedLatticeBasis` for the ideles `a`, `π` and the scale `(a / ā) ^ ⌊(s + 2) / 2⌋`, and let the
constant `c` of `Y` have the valuations of `a ā`. Then `Y.stringSum t = ∑ t i • 𝔢 ^ i` lies in
`Λ⁻ = Y.latticeMinus 1`, the intersection of `Λ` with the span of the string, if and only if each
`t i` lies in the fractional ideal `𝔩_i` of `powerIdele a s i` in grade at least `0`, and in
`N⁻¹ 𝔩_i` in negative grade. -/
lemma stringSum_mem_latticeMinus_iff (hL : Y.SpansLattice a π (divStar a ^ ((s + 2) / 2)))
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w))
    (t : ℕ → 𝔸f E) :
    Y.stringSum t ∈ Y.latticeMinus 1 ↔ ∀ i : ℕ, i < s →
      (if 2 * i < s then 1 else algebraMap E (𝔸f E) N) *
        ((powerIdele a s i)⁻¹.val * t i) ∈ Ô E := by
  rw [hL.mem_latticeMinus_iff, and_iff_right (stringProj_stringSum t), Nat.forall_lt_iff_fin]
  refine forall_congr' fun b ↦ ?_
  simpa only [one_mul] using lineIdele_inv_mul_stringSum_mem_iff hc 1 t b

/-- The grading `Y` of the hermitian space `V` has a string of `s` basis vectors; `𝔢 ^ i` is a
multiple of the string vector `i` by an element of `E` and has grade `s - 1 - 2 i`. Let the lattice
`Λ = V.lattice 1` have the standard basis of `gradedLatticeBasis` for the ideles `a`, `π` and the
scale `(a / ā) ^ ⌊(s + 2) / 2⌋`, let the constant `c` of `Y` have the valuations of `a ā`, and let
`N = π π̄`, with `π` a uniformiser at the places of `P`, a unit elsewhere, and no place of `P`
conjugate to another or to itself. Then `Y.stringSum t = ∑ t i • 𝔢 ^ i` lies in
`Λ⁺ = Y.latticePlus 1`, the projection of `Λ` to the span of the string, if and only if each `t i`
lies in the fractional ideal `𝔩_i` of `powerIdele a s i` in positive grade, and in `N⁻¹ 𝔩_i` in
grade at most `0`. -/
lemma stringSum_mem_latticePlus_iff (hL : Y.SpansLattice a π (divStar a ^ ((s + 2) / 2)))
    (hπ : IsSplitSquarefree P N π)
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w))
    (t : ℕ → 𝔸f E) :
    Y.stringSum t ∈ Y.latticePlus 1 ↔ ∀ i : ℕ, i < s →
      (if 2 * i + 1 < s then 1 else algebraMap E (𝔸f E) N) *
        ((powerIdele a s i)⁻¹.val * t i) ∈ Ô E := by
  rw [hL.mem_latticePlus_iff hπ, and_iff_right (stringProj_stringSum t), Nat.forall_lt_iff_fin]
  refine forall_congr' fun b ↦ ?_
  have h_factor : ((if b = b.rev then algebraMap E (𝔸f E) N else 1) *
      if 2 * b.val < s then 1 else algebraMap E (𝔸f E) N) =
        if 2 * b.val + 1 < s then 1 else algebraMap E (𝔸f E) N := by
    grind [eq_rev_iff]
  rw [lineIdele_inv_mul_stringSum_mem_iff hc, h_factor]

/-- `sh Λ⁺ = a Λ'⁻`: let `Y`, `Y'` be gradings of the hermitian spaces `V`, `V'` with strings of
`s`, `s - 1` basis vectors and the same constant `genericConst`, which has the valuations of `a ā`.
Let `N = π π̄` be split and squarefree, with `P` the places where `π` is a uniformiser. Suppose
`Y.SpansLattice` and `Y'.SpansLattice` hold: the lattices `Λ`, `Λ'` of `1` have, up to `GL(Ô)`, the
bases `gradedLatticeBasis` at the scales `(a / ā) ^ ⌊(s + 2) / 2⌋` and
`(a / ā) ^ ⌊(s - 1 + 2) / 2⌋`. The shift `sh = Y.stringMapFin Y'` kills `X ⊕ Unit` and sends each
string vector of `V` to a multiple of the string vector of `V'` with the same number, if there is
one. It takes the projection `Λ⁺` of `Λ` to the span of the string onto `a` times the intersection
`Λ'⁻` of `Λ'` with the span of the string. -/
lemma map_stringMapFin_latticePlus (hL : Y.SpansLattice a π (divStar a ^ ((s + 2) / 2)))
    (hL' : Y'.SpansLattice a π (divStar a ^ ((s - 1 + 2) / 2))) (hπ : IsSplitSquarefree P N π)
    (hconst_eq : Y'.genericConst = Y.genericConst)
    (hc : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y.genericConst.val w) = v
      ((a.val * star a.val) w)) :
    (Y.latticePlus 1).map ((Y.stringMapFin Y').restrictScalars (Ô E)) =
      a.val • Y'.latticeMinus 1 := by
  -- On the line of `𝔢 ^ i` with `i < s - 1` the conditions for `Λ⁺` and for `a Λ'⁻` are the same.
  have h_line (i : ℕ) (hi : i < s - 1) (x : 𝔸f E) :
      (if 2 * i + 1 < s then 1 else algebraMap E (𝔸f E) N) *
          ((powerIdele a s i)⁻¹.val * (a.val * x)) =
        (if 2 * i < s - 1 then 1 else algebraMap E (𝔸f E) N) *
          ((powerIdele a (s - 1) i)⁻¹.val * x) := by
    simp [powerIdele_eq_mul (show 0 < s by omega), Nat.lt_sub_iff_add_lt, mul_assoc]
  have hc' : ∀ w : FinPlace E, v (algebraMap E (𝔸f E) Y'.genericConst.val w) = v
    ((a.val * star a.val) w) := by
    rwa [hconst_eq]
  have h_smul (t : ℕ → 𝔸f E) : a.val • Y'.stringSum t = Y'.stringSum fun i ↦ a.val * t i := by
    simp only [stringSum, Finset.smul_sum, smul_smul]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := exists_stringSum_eq (stringProj_eq_of_mem_latticePlus hy)
    refine ⟨Y'.stringSum fun i ↦ a⁻¹.val * t i, ?_,
      by simp [h_smul, stringMapFin_stringSum hconst_eq]⟩
    refine (hL'.stringSum_mem_latticeMinus_iff hc' _).2 fun i hi ↦ ?_
    rw [← h_line i hi, Units.mul_inv_cancel_left]
    exact (hL.stringSum_mem_latticePlus_iff hπ hc t).1 hy i (by omega)
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨t, rfl⟩ := exists_stringSum_eq (mem_latticeMinus.1 hz).right
    let t' (i : ℕ) : 𝔸f E := if i < s - 1 then a.val * t i else 0
    have h_mem : Y.stringSum t' ∈ Y.latticePlus 1 := by
      refine (hL.stringSum_mem_latticePlus_iff hπ hc t').2 fun i _ ↦ ?_
      by_cases hi : i < s - 1
      · simpa [t', hi, h_line i hi] using (hL'.stringSum_mem_latticeMinus_iff hc' t).1 hz i hi
      · simp [t', hi]
    have h_shift : Y.stringMapFin Y' (Y.stringSum t') = a.val • Y'.stringSum t := by
      rw [stringMapFin_stringSum hconst_eq, h_smul, stringSum, stringSum]
      exact Finset.sum_congr rfl fun i hi ↦ by simp only [t', ite_eq_left (Finset.mem_range.1 hi)]
    exact ⟨Y.stringSum t', h_mem, h_shift⟩

/-- Let `Λ⁻ = Y.latticeMinus 1` and `Λ⁺ = Y.latticePlus 1` be the intersection with and the
projection to the span of the string of the lattice with standard basis `gradedLatticeBasis` for
`a`, `π` and any unitary scale `u`, in which the string vector `b` is multiplied by
`lineIdele a u b`. Let `N = π π̄` be split and squarefree. For `y` in `Λ⁺` outside `Λ⁻`, the string
has a middle index `m = m.rev`, and the coordinate of `y` there, divided by `lineIdele a u m`, which
generates `Λ⁻` on this line, has a pole at a place `w` above `N`: a place of `P` or a conjugate of
one. -/
lemma exists_pole_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    ∃ (m : Fin s) (w : FinPlace E), m = m.rev ∧ (w ∈ P ∨ star w ∈ P) ∧
      1 < v (((lineIdele a u m)⁻¹.val * y (Y.indexEquiv (.inr m))) w) := by
  obtain ⟨hy_string, hy_line⟩ := (hL.mem_latticePlus_iff hπ).1 hy
  simp only [hL.mem_latticeMinus_iff, hy_string, true_and, mem_Ô, not_forall, not_le] at hy_notMem
  obtain ⟨m, w, h_pole⟩ := hy_notMem
  have h_mem := mem_Ô.1 (hy_line m) w
  have hm : m = m.rev := by_contra fun hm ↦ h_pole.not_ge (by simpa [hm] using h_mem)
  refine ⟨m, w, hm, by_contra fun hw ↦ h_pole.not_ge ?_, h_pole⟩
  simpa only [ite_eq_left hm, finAdele_mul_apply (algebraMap E (𝔸f E) N), map_mul,
    hπ.v_algebraMap, ite_eq_right hw, one_mul] using h_mem

/-- Let `Λ⁻ = Y.latticeMinus 1` and `Λ⁺ = Y.latticePlus 1` be the intersection with and the
projection to the span of the string of the lattice with basis `New.gradedLatticeBasis`, and let
`N = π π̄` be split and squarefree. If some vector of `Λ⁺` lies outside `Λ⁻`, then the length `s`
of the string is odd. -/
lemma odd_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    Odd s := by
  obtain ⟨m, -, hm, -⟩ := hL.exists_pole_of_notMem_latticeMinus hπ hy hy_notMem
  exact odd_of_eq_rev hm

/-- Suppose `Y.SpansLattice a π u`: the lattice of `1` has, up to `GL(Ô)`, the basis
`gradedLatticeBasis` built from `a`, `π` and the unitary scale `u`. Let `Λ⁻ = Y.latticeMinus 1` and
`Λ⁺ = Y.latticePlus 1` be its intersection with and its projection to the span of the string. Let
`N = π π̄` be split and squarefree. A vector `y` of `Λ⁺` outside `Λ⁻` generates `Λ⁺` over `Λ⁻` at
some place `w` above `N`: every `z` in `Λ⁺` differs from a multiple `c • y` with `c ∈ Ô E` by a
vector whose component at `w` lies in `Λ⁻`. -/
lemma exists_place_generates_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    ∃ w : FinPlace E, (w ∈ P ∨ star w ∈ P) ∧ ∀ z ∈ Y.latticePlus 1,
      ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • y) ∈ Y.latticeMinus 1 := by
  -- At a place `w` where the middle coordinate of `y` has a pole, it divides that of `z`.
  let coord (x : ι → 𝔸f E) (b : Fin s) : 𝔸f E :=
    (lineIdele a u b)⁻¹.val * x (Y.indexEquiv (.inr b))
  have h_plus (x : ι → 𝔸f E) : x ∈ Y.latticePlus 1 ↔ Y.stringProj x = x ∧
      ∀ b : Fin s, (if b = b.rev then algebraMap E (𝔸f E) N else 1) * coord x b ∈ Ô E :=
    hL.mem_latticePlus_iff hπ
  obtain ⟨hy_string, hy_line⟩ := (h_plus y).1 hy
  obtain ⟨m, w, hm, hw, (h_pole : 1 < v (coord y m w))⟩ :=
    hL.exists_pole_of_notMem_latticeMinus hπ hy hy_notMem
  refine ⟨w, hw, fun z hz ↦ ?_⟩
  obtain ⟨hz_string, hz_line⟩ := (h_plus z).1 hz
  -- The pole of the middle coordinate of `z` at `w` is at most simple.
  have hz_bound : WithZero.exp (-1) * v (coord z m w) ≤ 1 := by
    simpa only [ite_eq_left hm, finAdele_mul_apply (algebraMap E (𝔸f E) N), map_mul,
      hπ.v_algebraMap, ite_eq_left hw] using mem_Ô.1 (hz_line m) w
  have h_le_pole : v (coord z m w) ≤ v (coord y m w) :=
    calc v (coord z m w)
      _ ≤ WithZero.exp 1 := by rwa [WithZero.exp_neg, inv_mul_le_one₀ WithZero.exp_pos] at hz_bound
      _ ≤ v (coord y m w) := by
        simpa [← WithZero.lt_mul_exp_iff_le (zero_lt_one.trans h_pole).ne'] using h_pole
  obtain ⟨c, hc, h_quot⟩ : ∃ c ∈ Ô E, idem {w} * coord z m = coord y m * c := by
    refine exists_eq_mul_iff_v_le.2 fun w' ↦ ?_
    obtain rfl | hw' := eq_or_ne w' w
    · simpa [finAdele_mul_apply] using h_le_pole
    · simp [hw']
  refine ⟨c, hc, hL.mem_latticeMinus_iff.2 ⟨by simp [hy_string, hz_string], fun b ↦ ?_⟩⟩
  suffices idem {w} * (coord z b - c * coord y b) ∈ Ô E by
    simpa [coord, mul_sub, mul_left_comm] using this
  by_cases hb : b = b.rev
  · -- The middle index is unique.
    obtain rfl : b = m := eq_of_eq_rev hb hm
    simp [mul_comm c, ← h_quot, mul_sub, ← mul_assoc, idem_mul_self]
  · exact mul_mem (idem_mem_Ô _) (sub_mem (by simpa [hb] using hz_line b)
      (mul_mem hc (by simpa [hb] using hy_line b)))

/-- Let `Λ⁻ = Y.latticeMinus 1` and `Λ⁺ = Y.latticePlus 1` be the intersection with and the
projection to the span of the string of the lattice with basis `New.gradedLatticeBasis`. If `y` is
a vector of `Λ⁺` outside `Λ⁻`, then `s` is odd and `y` generates `Λ⁺` over `Λ⁻` at some place `w`
above `N = π π̄`, that is, a place of `P` or a conjugate of one. -/
lemma odd_and_exists_place_of_notMem_latticeMinus {y : ι → 𝔸f E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (hy : y ∈ Y.latticePlus 1) (hy_notMem : y ∉ Y.latticeMinus 1) :
    Odd s ∧
      ∃ w : FinPlace E, (w ∈ P ∨ star w ∈ P) ∧ ∀ z ∈ Y.latticePlus 1,
        ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • y) ∈ Y.latticeMinus 1 :=
  ⟨hL.odd_of_notMem_latticeMinus hπ hy hy_notMem,
    hL.exists_place_generates_of_notMem_latticeMinus hπ hy hy_notMem⟩

end Grading.SpansLattice

end New

end
end
end

/-!
# Bounds for the lattices of points on graded spaces

Let `Λ'` be the lattice `V.lattice x` of a finite point `x` of a graded space and `Λ` the lattice
of the point `1`. The file proves lattice steps of the induction for the bounds
`Q̄ ^ k Λ⁻ ⊆ Λ'⁻ ⊆ Q ^ (-k) Λ⁻`, where `q` generates `Q`.

* `New.Grading.smul_latticeMinus_le_of_map_latticePlus`: if `sh Λ⁺` is `a` times the `Λ⁻` of the
  next space, then the upper bound on one space and an inclusion `(q̄ / a) sh Λ'⁺ ⊆ Λ''⁻`, with
  `Λ''` the lattice of a point on the next space, give the lower bound on the next space.
* `New.Grading.SpansLattice.hasLatticeBounds_or_latticeSplitsAt`: for a grading over `X ⊕ Unit`,
  duality turns the lower bound into both bounds, unless `s` is odd and `Λ'` splits along `X ⊕ Unit`
  at a place above `N`.
* `New.Grading.LatticeSplitsAt.conj_scalarFin_mem`: if `Λ'` splits along `X` at a place `w ≠ w̄`,
  then the integral scalings of `X` supported at `w` and `w̄` preserve `Λ'`.

Notions from other files:

* `Gf E ι`: the finite adelic unitary group in the variables `ι`, whose elements are the finite
  points. The lattice `V.lattice x` is spanned over `Ô E` by the columns of `V.xFin * x`, where
  `V.xFin` is the finite frame of the hermitian space `V`.
* `New.Grading V N X s`: a splitting of the basis `ι` of `V` into an orthonormal part `X` of grade
  `0` and a string of `s` vectors, where vector `i` pairs only with vector `s - 1 - i`, to `1`,
  except that the middle vector (for odd `s`) pairs with itself to `-N`.
* `Y.latticePlus x`, `Y.latticeMinus x`: the projection `Λ'⁺` of the lattice of `x` to `X^⊥` and
  its intersection `Λ'⁻` with `X^⊥`, the span of the string.
* `Y.stringMapFin Y'`: the shift `sh` from the vectors of one graded space to those of the next.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

@[expose] public section

open Matrix Pointwise Valued

noncomputable section

namespace New

open Seesaw Gf Space

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}

namespace Grading

section Splitting

/-- Let `Y` split the basis of `V` into `X` and a string spanning `X^⊥`, and let `Λ' = V.lattice x`
be the lattice of the point `x` of the finite adelic unitary group. Then `Λ'` splits along `X` at
the place `w` if there the projection `Λ'⁺` of `Λ'` to `X^⊥` lies in the intersection `Λ'⁻` of `Λ'`
with `X^⊥`, so the two are equal. The idempotent `idem {w}` cuts out the component at `w`. -/
def LatticeSplitsAt (Y : Grading V N X s) (w : FinPlace E) (x : Gf E ι) : Prop :=
  (idem {w} : 𝔸f E) • Y.latticePlus x ≤ Y.latticeMinus x

/-- If the lattice of `x` splits along `X` at the place `w`, then it splits at the complex conjugate
place `star w` too. -/
lemma LatticeSplitsAt.conj {Y : Grading V N X s} {w : FinPlace E} {x : Gf E ι}
    (h_split : Y.LatticeSplitsAt w x) : Y.LatticeSplitsAt (star w) x := by
  have h_idem : (idem {star w} : 𝔸f E) = star (idem {w}) := by
    rw [star_idem]
    congr with u
    exact eq_star_iff_eq_star.trans eq_comm
  simpa only [LatticeSplitsAt, h_idem] using star_smul_latticePlus_le_latticeMinus h_split

/-- In rational coordinates, the finite point `Y.inclXFin (scalarFin X z)` of `U(V)`, which scales
`X` by `z`, sends a vector `y` to `y + (z - 1) (y - p y)`, where `p = Y.stringProj` is the
projection to `X^⊥`. -/
lemma inclXFin_scalarFin_mulVec {Y : Grading V N X s} (z : unitary (𝔸f E)) (y : ι → 𝔸f E) :
    V.ratCoordMatrixFin (Y.inclXFin (scalarFin X z)) *ᵥ y =
      y + (z.val - 1) • (y - Y.stringProj y) := by
  ext1 i
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective i <;>
    simp [ratCoordMatrixFin_inclXFin, submatrix_mulVec_equiv, fromBlocks_mulVec,
      stringProj_apply_inl, stringProj_apply_inr, sub_mul, scalarFin]

omit [Fintype X] in
/-- Let the lattice of `x` split along `X` at the place `w`: there its projection to `X^⊥` lies in
the lattice. For every vector `y` of the lattice, the component at `w` (cut out by `idem {w}`) of
the part `y - Y.stringProj y` of `y` in `X` lies in the lattice. -/
lemma LatticeSplitsAt.idem_smul_sub_stringProj_mem {Y : Grading V N X s} {w : FinPlace E}
    {x : Gf E ι} (h_split : Y.LatticeSplitsAt w x) {y : ι → 𝔸f E} (hy : y ∈ V.lattice x) :
    (idem {w} : 𝔸f E) • (y - Y.stringProj y) ∈ V.lattice x := by
  have h_minus : (idem {w} : 𝔸f E) • Y.stringProj y ∈ Y.latticeMinus x :=
    smul_le_iff_forall.1 h_split _ (Submodule.mem_map_of_mem hy)
  rw [smul_sub]
  exact sub_mem ((V.lattice x).smul_mem ⟨_, idem_mem_Ô _⟩ hy) (mem_latticeMinus.1 h_minus).1

/-- At a place `u` where the unitary adele `z` is `1`, the finite point that scales `X` by `z`,
conjugated by the finite frame `V.xFin` into rational coordinates, has the identity matrix. -/
lemma inclXFin_scalarFin_map_evalAt {Y : Grading V N X s} {z : unitary (𝔸f E)} {u : FinPlace E}
    (hz : z.val u = 1) :
    (V.xFin * Y.inclXFin (scalarFin X z) * V.xFin⁻¹).map (evalAt u) = 1 := by
  refine Units.ext ?_
  change (V.ratCoordMatrixFin (Y.inclXFin (scalarFin X z))).map (evalAt u) = 1
  ext i j : 1
  have h := congrArg (fun v : ι → 𝔸f E ↦ evalAt u (v i))
    (inclXFin_scalarFin_mulVec (Y := Y) z (Pi.single j 1))
  by_cases hij : i = j <;>
    simpa [Matrix.mulVec_single_one, Matrix.col, hz, Pi.single_apply, Matrix.one_apply, hij,
      eq_comm] using h

/-- Let `x` be a point of the finite adelic unitary group `Gf E ι` whose lattice, spanned by the
columns of `V.xFin * x`, splits along `X` at a place `w ≠ w̄`: there its projection to `X^⊥` lies in
the lattice. Let `z` be an integral unitary adele that is `1` off `w` and `w̄`. Then the conjugate
by `x` of the scaling `Y.inclXFin (scalarFin X z)` of `X` by `z` lies in `maxCompactAt ι w`: it is
integral and trivial off `w` and `w̄`. -/
lemma LatticeSplitsAt.conj_scalarFin_mem {Y : Grading V N X s} {w : FinPlace E} {x : Gf E ι}
    (h_split : Y.LatticeSplitsAt w x) (hw : star w ≠ w)
    {z : unitary (𝔸f E)} (hz_int : z.val ∈ Ô E)
    (hz_off : ∀ u : FinPlace E, u ≠ w → star u ≠ w → z.val u = 1) :
    x⁻¹ * (Y.inclXFin (scalarFin X z) * x) ∈ maxCompactAt ι w := by
  refine ⟨V.conj_mem_stdLevel_of_mapsTo_lattice fun y hy ↦ ?_, mem_supportedOn.2 fun u hu hu' ↦ ?_⟩
  · -- The conjugate is integral, as the scaling by `z` maps the lattice of `x` into itself.
    show V.ratCoordMatrixFin (Y.inclXFin (scalarFin X z)) *ᵥ y ∈ V.lattice x
    have h_supp : z.val - 1 = (z.val - 1) * (idem {w} + idem {star w}) := by
      ext u
      by_cases hu : u = w
      · simp [hu, hw.symm]
      by_cases hu' : u = star w
      · simp [hu', hw]
      -- At a place other than `w` and `w̄` both sides are `0`.
      have h_off : z.val u = 1 := hz_off u hu fun h_eq ↦ hu' (eq_star_of_eq_star h_eq.symm)
      simp [h_off]
    rw [inclXFin_scalarFin_mulVec, h_supp, mul_smul, add_smul]
    -- The two components of the part of `y` in `X`, at `w` and at `w̄`, lie in the lattice.
    exact add_mem hy ((V.lattice x).smul_mem ⟨_, sub_mem hz_int (one_mem _)⟩ (add_mem
      (h_split.idem_smul_sub_stringProj_mem hy) (h_split.conj.idem_smul_sub_stringProj_mem hy)))
  · -- The conjugate is trivial at a place other than `w` and `w̄`, where `z` is `1`.
    have h_scaling : atPlace u (Y.inclXFin (scalarFin X z)) = 1 := by
      simpa [atPlace] using inclXFin_scalarFin_map_evalAt (hz_off u hu hu')
    simp [h_scaling]

end Splitting

/-- Write `Λ⁺` and `Λ'⁺` for the projections to `X^⊥` of the lattices of `1` and `x`, `Λ⁻` and `Λ'⁻`
for their intersections with `X^⊥`, and `M⁻` and `M'⁻` for the intersections with `X'^⊥` of the
lattices of `1` and `x'` in `V'`. Let `sh Λ⁺ = a M⁻` and `(q̄ / a) sh Λ'⁺ ⊆ M'⁻` for finite ideles
`a`, `q`. Then the upper bound `q ^ k Λ'⁻ ⊆ Λ⁻` on `V` gives `q̄ ^ (k + 1) M⁻ ⊆ M'⁻` on `V'`. -/
lemma smul_latticeMinus_le_of_map_latticePlus {Y : Grading V N X s} {Y' : Grading V' N X' (s - 1)}
    {a q : (𝔸f E)ˣ} {k : ℕ} {x : Gf E ι} {x' : Gf E ι'}
    (h_shift_one_eq : (Y.latticePlus 1).map ((Y.stringMapFin Y').restrictScalars (Ô E)) =
      a.val • Y'.latticeMinus 1)
    (h_upper : q.val ^ k • Y.latticeMinus x ≤ Y.latticeMinus 1)
    (h_shift_le : (star q / a).val •
      (Y.latticePlus x).map ((Y.stringMapFin Y').restrictScalars (Ô E)) ≤ Y'.latticeMinus x') :
    star q.val ^ (k + 1) • Y'.latticeMinus 1 ≤ Y'.latticeMinus x' := by
  refine smul_le_iff_forall.2 fun y hy ↦ ?_
  obtain ⟨z, hz, hzy⟩ : ∃ z ∈ Y.latticePlus 1, Y.stringMapFin Y' z = a.val • y :=
    h_shift_one_eq.ge (Submodule.smul_mem_pointwise_smul y a.val _ hy)
  -- The dual `q̄ ^ k Λ⁺ ⊆ Λ'⁺` of the upper bound puts `q̄ ^ k z` into `Λ'⁺`.
  have h_mem : star (q.val ^ k) • z ∈ Y.latticePlus x :=
    smul_le_iff_forall.1 (star_smul_latticePlus_le h_upper) z hz
  have h_eq : star q.val ^ (k + 1) • y =
      (star q / a).val • Y.stringMapFin Y' (star (q.val ^ k) • z) := by
    rw [map_smul, hzy, smul_smul, smul_smul, mul_right_comm, ← Units.val_mul, div_mul_cancel,
      Units.coe_star, star_pow, pow_succ']
  rw [h_eq]
  exact smul_le_iff_forall.1 h_shift_le _ (Submodule.mem_map_of_mem h_mem)

omit [Fintype X] in
/-- Write `Λ±` and `Λ'±` for the projection to `X^⊥` (`+`) and the intersection with it (`-`) of the
lattices of `1` and `x`, and `v` for the valuation at a place. Let `q` and `q̄` be units at `w`, let
`q̄ ^ k Λ⁻ ⊆ Λ'⁻` and `q ^ k Λ'⁺ ⊆ Λ⁺`, and let `y ∈ Λ'⁻` be such that `q ^ k y` generates `Λ⁺` over
`Λ⁻` at `w`. Then the lattice of `x` splits at `w`: there `Λ'⁺ ⊆ Λ⁺ = Λ⁻ + Ô y ⊆ Λ'⁻`. -/
lemma latticeSplitsAt_of_generates {Y : Grading V N X s} {q : (𝔸f E)ˣ} {k : ℕ} {x : Gf E ι}
    {w : FinPlace E} {y : ι → 𝔸f E}
    (h_lower : star q.val ^ k • Y.latticeMinus 1 ≤ Y.latticeMinus x)
    (h_dual : q.val ^ k • Y.latticePlus x ≤ Y.latticePlus 1)
    (hy : y ∈ Y.latticeMinus x) (hq : v (q.val w) = 1) (hq_star : v (q.val (star w)) = 1)
    (h_gen : ∀ z ∈ Y.latticePlus 1,
      ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • q.val ^ k • y) ∈ Y.latticeMinus 1) :
    Y.LatticeSplitsAt w x := by
  refine smul_le_iff_forall.2 fun z hz ↦ ?_
  obtain ⟨c, hc, h_sub⟩ : ∃ c ∈ Ô E,
      (idem {w} : 𝔸f E) • (q.val ^ k • z - c • q.val ^ k • y) ∈ Y.latticeMinus 1 :=
    h_gen (q.val ^ k • z) (smul_le_iff_forall.1 h_dual z hz)
  -- The norm `n = (q̄ q) ^ k` is a unit at `w`, so its inverse is integral there.
  let n : (𝔸f E)ˣ := (star q * q) ^ k
  have hn : idem {w} * n⁻¹.val ∈ Ô E := by
    simp [idem_mul_mem_Ô, n, ← inv_pow, idele_inv_apply_and_ne_zero, hq, hq_star]
  have h_inv : n⁻¹.val * (star q.val ^ k * q.val ^ k) = 1 := by
    rw [← mul_pow]
    exact n.inv_mul
  -- Split the component of `z` at `w` into its parts from `Λ⁻` and from `y`.
  have h_eq : (idem {w} : 𝔸f E) • z = (idem {w} * n⁻¹.val) • star q.val ^ k •
      (idem {w} : 𝔸f E) • (q.val ^ k • z - c • q.val ^ k • y) + (idem {w} * c) • y := by
    linear_combination (norm := module)
      (-(idem {w} * idem {w}) * h_inv - idem_mul_self (E := E) {w}) • (z - c • y)
  have h_sub_mem : star q.val ^ k • (idem {w} : 𝔸f E) • (q.val ^ k • z - c • q.val ^ k • y) ∈
      Y.latticeMinus x :=
    smul_le_iff_forall.1 h_lower _ h_sub
  rw [h_eq]
  exact add_mem ((Y.latticeMinus x).smul_mem ⟨_, hn⟩ h_sub_mem)
    ((Y.latticeMinus x).smul_mem ⟨_, mul_mem (idem_mem_Ô _) hc⟩ hy)

/-- Let the lattice of `1` have the basis `gradedLatticeBasis` built from the ideles `a`, `π` and
the unitary adele `u`. Let `N = π π̄` with `π` a uniformiser at the places of `P`, none of which has
its conjugate in `P`, and a unit elsewhere, and let `q` be a unit at the places of `P` and their
conjugates. Write `Λ⁻` and `Λ'⁻` for the intersections of the lattices of `1` and `x` with
`(X ⊕ Unit)^⊥`, and assume the lower bound `q̄ ^ k Λ⁻ ⊆ Λ'⁻`. Then the upper bound `q ^ k Λ'⁻ ⊆ Λ⁻`
holds too, or `s` is odd and the lattice of `x` splits at some `w ∈ P`: there its projection to
`(X ⊕ Unit)^⊥` lies in `Λ'⁻`. -/
lemma SpansLattice.hasLatticeBounds_or_latticeSplitsAt {Y : Grading V N (X ⊕ Unit) s}
    {a π q : (𝔸f E)ˣ} {u : unitary (𝔸f E)} {P : Finset (FinPlace E)} {k : ℕ} {x : Gf E ι}
    (hL : Y.SpansLattice a π u) (hπ : IsSplitSquarefree P N π)
    (hq : ∀ w : FinPlace E, w ∈ P ∨ star w ∈ P → v (q.val w) = 1)
    (h_lower : star q.val ^ k • Y.latticeMinus 1 ≤ Y.latticeMinus x) :
    Y.HasLatticeBounds q.val k x ∨ Odd s ∧ ∃ w ∈ P, Y.LatticeSplitsAt w x := by
  have h_dual : q.val ^ k • Y.latticePlus x ≤ Y.latticePlus 1 := by
    simpa only [star_pow, star_star] using star_smul_latticePlus_le h_lower
  refine or_iff_not_imp_left.2 fun h_fail ↦ ?_
  obtain ⟨y, hy, hy_notMem⟩ : ∃ y ∈ Y.latticeMinus x, q.val ^ k • y ∉ Y.latticeMinus 1 := by
    by_contra! h_upper
    exact h_fail ⟨h_lower, smul_le_iff_forall.2 h_upper⟩
  -- The vector `q ^ k y` of `Λ⁺` is not in `Λ⁻`, so it generates `Λ⁺` over `Λ⁻` at some `w ∣ N`.
  have h_plus : q.val ^ k • y ∈ Y.latticePlus 1 :=
    smul_le_iff_forall.1 h_dual y (latticeMinus_le_latticePlus hy)
  obtain ⟨hs, w, hw, h_gen⟩ : Odd s ∧ ∃ w : FinPlace E, (w ∈ P ∨ star w ∈ P) ∧
      ∀ z ∈ Y.latticePlus 1,
        ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • q.val ^ k • y) ∈ Y.latticeMinus 1 :=
    hL.odd_and_exists_place_of_notMem_latticeMinus hπ h_plus hy_notMem
  have hw_star : star w ∈ P ∨ star (star w) ∈ P := by simpa [or_comm] using hw
  have h_split : Y.LatticeSplitsAt w x :=
    latticeSplitsAt_of_generates h_lower h_dual hy (hq w hw) (hq (star w) hw_star) h_gen
  rcases hw with hw | hw
  · exact ⟨hs, w, hw, h_split⟩
  · exact ⟨hs, star w, hw, h_split.conj⟩

/-- Suppose that each translate `r x` by the finite Bessel subgroup `Y.besselFin` whose lattice is
graded (closed under the projections to the grades) has the bounds `Y.HasLatticeBounds q k`. Then
the orbit of `x` is bounded: some translate has both properties, as every orbit has a graded
lattice. The field `E` is assumed to contain a primitive root of unity of order `5040`. -/
lemma HasBoundedOrbit.of_forall [HasPrimitiveRoot5040 E] {Y : Grading V N X s} {q : 𝔸f E} {k : ℕ}
    {x : Gf E ι} (h_bounds : ∀ r ∈ Y.besselFin,
      Y.IsGraded (V.lattice (r * x)) → Y.HasLatticeBounds q k (r * x)) :
    Y.HasBoundedOrbit q k x := by
  obtain ⟨u, hu, h_graded⟩ :
      ∃ u : Gf E ι, ((1, u) : G E ε) ∈ Y.unipotent ∧ Y.IsGraded (V.lattice (u * x)) :=
    Y.exists_isGraded x
  have hu_bessel : u ∈ Y.besselFin := Y.unipotent_le_besselGroup hu
  exact ⟨u, hu_bessel, h_graded, h_bounds u hu_bessel h_graded⟩

/-- Let the lattice of `1`, spanned by the finite frame `V.xFin`, have the basis
`gradedLatticeBasis` with parameters `a`, `π`, `u`. If the orbit of the finite point `x` under the
finite Bessel subgroup `Y.besselFin` has an integral point `r x ∈ stdLevel E ι`, then some point of
the orbit has a graded lattice with the bounds for `k = 0`: the lattice of `r x` is the one of
`1`. -/
lemma SpansLattice.hasBoundedOrbit_zero {Y : Grading V N (X ⊕ Unit) s} {a π : (𝔸f E)ˣ}
    {u : unitary (𝔸f E)} (hL : Y.SpansLattice a π u) (q : 𝔸f E) {r x : Gf E ι}
    (hr : r ∈ Y.besselFin) (hx : r * x ∈ stdLevel E ι) : Y.HasBoundedOrbit q 0 x := by
  have h_lattice : V.lattice (r * x) = V.lattice 1 := (lattice_eq_iff.2 (by simpa using hx)).symm
  have h_minus : Y.latticeMinus (r * x) = Y.latticeMinus 1 := by simp [latticeMinus, h_lattice]
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · simpa [h_lattice] using hL.isGraded
  · simp [h_minus]
  · simp [h_minus]

end Grading

end New

end
end
end

section
/-!
# The shift at a nonzero constant term maps lattices into lattices

`Y` and `Y'` present the spaces `V` and `V'` as a block plus a string, of lengths `s` and `s - 1`,
and `sh = Y.stringMap Y'` is the shift between the strings, of degree `-1`.

* `New.Grading.IsGraded.mulVec_mem_of_homogeneous`: a homogeneous part of a map between graded
  lattices maps the first lattice into the second.
* `New.Grading.exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap`: let the constant term of
  `t ⊗ f` at `sh` not vanish at `(x, x')`, with `f` fixed by the Heisenberg operators of
  `b Ô ^ (ι' × ι)`; then modulo degree at least `0` the multiple `(b̄ / α) sh` maps the lattice of
  `x` into that of `x'`.
* `New.Grading.smul_map_stringMapFin_latticePlus_le`: at graded points this multiple of `sh` maps
  `Λ'⁺` of the first point into `Λ'⁻` of the second.

Notions from other files:
* `Y.gradeOf` is the grade of a basis index: `0` on the block `X` and `s - 1 - 2 i` on the string
  vector `i`; `HasDegreeGe w' w d A` says that the entry `(p, q)` of `A` is `0` if
  `w' p < w q + d`.
* `V.lattice g`, for a finite point `g`, is the lattice `g Λ` in rational coordinates;
  `Y.latticePlus g` is its projection `Λ'⁺` to `X^⊥` and `Y.latticeMinus g` is its intersection
  `Λ'⁻` with `X^⊥`.
* `Y.mapDegree Y'.gradeOf (p, q)` is the degree of the entry `(p, q)`, and `Y.constTerm` is the
  constant term along the entries of positive degree.
* `matrixToVec` and `vecToMatrix` pass between matrices and vectors indexed by `ι' × ι`.
* `Y.IsGraded L` says that the lattice `L` contains each graded part of each of its vectors.
* `Y.constTermAtStringMap Y' μ F x x'` is the constant term at `sh`, for the weights `Y'.gradeOf`,
  of the Weil translate of `F` by `(x, x')`, twisted by the characters `μ`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

@[expose] public section

open Matrix Pointwise Kronecker

noncomputable section

namespace New

open Seesaw Space WeilData

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  {Y : Grading V N X s} {Y' : Grading V' N X' (s - 1)}

/-- Let `D` be a Witt decomposition of the Hermitian space `V` into two dual isotropic subspaces,
with bases indexed by `p`, and an isometric image of `V'` orthogonal to both. The columns of `D.k`
are the basis of the first isotropic subspace, and `D.isotropicBasisFin` is this basis over the
finite adeles, written in lattice coordinates. Its adjoint is `D.kᴴ * V.J * V.xFin`. -/
lemma Space.Splitting.conjTranspose_isotropicBasisFin {p : Type} [Fintype p] [DecidableEq p]
    (D : V.Splitting V' p) : D.isotropicBasisFinᴴ = (D.kᴴ * V.J).map (algebraMap E (𝔸f E)) *
      V.xFin.val := by
  -- By definition `D.isotropicBasisFin` is the finite component of the product `V.x⁻¹ * D.k` over
  -- the adeles.
  have h_frame : D.isotropicBasisFin = V.xFin⁻¹.val * D.k.map (algebraMap E (𝔸f E)) :=
    Matrix.map_mul (f := RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))
  have h_dual : V.xFin⁻¹.valᴴ = V.J.map (algebraMap E (𝔸f E)) * V.xFin.val := by
    rw [← gram_inv_of_gram_eq gram_xFin, mul_one, Units.inv_mul_cancel_right]
  rw [h_frame, conjTranspose_mul, h_dual, Matrix.map_mul, Matrix.mul_assoc,
    conjTranspose_map _ fun a ↦ (star_algebraMap_finAdele a).symm]

namespace Grading

omit [Fintype X] in
/-- Let the bases of `V` and `V'` carry the integer grades `Y.gradeOf` and `Y'.gradeOf`, and let `W`
map a lattice `L` into a lattice `L'`, both graded. Then the part `T` of `W` of degree `e`, whose
entry `(p, q)` is that of `W` if the grade of `p` is that of `q` plus `e` and is `0` otherwise, also
maps `L` into `L'`. -/
lemma IsGraded.mulVec_mem_of_homogeneous {L : Submodule (Ô E) (ι → 𝔸f E)}
    {L' : Submodule (Ô E) (ι' → 𝔸f E)} (hL : Y.IsGraded L) (hL' : Y'.IsGraded L')
    {W T : Matrix ι' ι (𝔸f E)} {e : ℤ} (hW : ∀ y ∈ L, W *ᵥ y ∈ L')
    (hT : ∀ (p : ι') (q : ι), T p q = if Y'.gradeOf p = Y.gradeOf q + e then W p q else 0)
    {y : ι → 𝔸f E} (hy : y ∈ L) : T *ᵥ y ∈ L' := by
  -- `T` is the sum over the grades `d` of the part of `W` from grade `d` to grade `d + e`.
  have h_sum : T *ᵥ y = ∑ d ∈ (Finset.univ.image Y.gradeOf : Finset ℤ),
      Y'.gradeProj (d + e) (W *ᵥ Y.gradeProj d y) := by
    simp only [gradeProj, mulVecLin_apply, mulVec_mulVec, ← Matrix.sum_mulVec]
    congr 1
    ext p q : 2
    -- Only the summand of the grade of `q` contributes to the entry `(p, q)`.
    simp [Matrix.sum_apply, hT, ← Matrix.mul_assoc]
  rw [h_sum]
  exact L'.sum_mem fun d _ ↦ hL' (d + e) _ (hW _ (hL d y hy))

omit [Fintype X] in
/-- The shift `Y.stringMap Y'` from the string of basis vectors of `V` to that of `V'` is
homogeneous of degree `-1`: its entry `(p, q)` vanishes unless the grade of `p` is one less than
that of `q`. -/
lemma stringMap_eq_zero_of_gradeOf_ne {p : ι'} {q : ι} (h_grade : Y'.gradeOf p ≠ Y.gradeOf q + -1) :
    Y.stringMap Y' p q = 0 := by
  obtain ⟨b | b, rfl⟩ := Y'.indexEquiv.surjective p
  · obtain ⟨a | a, rfl⟩ := Y.indexEquiv.surjective q <;> simp [stringMap]
  obtain ⟨a | a, rfl⟩ := Y.indexEquiv.surjective q
  · simp [stringMap]
  have h_ne : b.val ≠ a.val := by
    simp only [gradeOf, Equiv.symm_apply_apply, Sum.elim_inr] at h_grade
    omega
  simp [stringMap, h_ne]

omit [Fintype X] in
/-- The finite part `Y.stringMapFin Y'` of the shift between the strings kills the block `X`, so it
does not change under composition with the projection `Y.stringProj` to the span `X^⊥` of the string
of `V`. -/
lemma stringMapFin_stringProj [Finite X] (y : ι → 𝔸f E) :
    Y.stringMapFin Y' (Y.stringProj y) = Y.stringMapFin Y' y := by
  let := Fintype.ofFinite X
  funext p
  have h_inl (a : X) : Y.stringMap Y' p (Y.indexEquiv (.inl a)) = 0 := by
    obtain ⟨b | b, rfl⟩ := Y'.indexEquiv.surjective p <;> simp [stringMap]
  simp [stringMapFin, mulVec, dotProduct, reindex_equiv Y.indexEquiv, stringProj_apply_inr, h_inl]

omit [Fintype X] in
/-- The finite part `Y.stringMapFin Y'` of the shift between the strings takes its values in the
span `X'^⊥` of the string of `V'`, so they are fixed by the projection `Y'.stringProj` to it. -/
lemma stringProj_stringMapFin [Finite X] (y : ι → 𝔸f E) :
    Y'.stringProj (Y.stringMapFin Y' y) = Y.stringMapFin Y' y := by
  let := Fintype.ofFinite X
  simp [stringProj_eq_self_iff, stringMapFin, stringMap, mulVec, dotProduct,
    reindex_equiv Y.indexEquiv]

omit [Fintype X] in
/-- Let `r` be a finite point of the Bessel group of the grading `Y` of `V`, that is, `r` fixes each
string vector of grade `≥ 0` up to vectors of higher grade. Then the matrix of `r` in rational
coordinates does not lower grades. -/
lemma hasDegreeGe_zero_ratCoordMatrixFin [Finite X] {r : Gf E ι} (hr : r ∈ Y.besselFin) :
    HasDegreeGe Y.gradeOf Y.gradeOf 0 (V.ratCoordMatrixFin r) := fun p q h ↦ by
  let := Fintype.ofFinite X
  -- This is the finite component of the same fact for the adelic point `(1, r)`.
  have h_mem : ((1, r) : G E ε) ∈ Y.besselGroup := hr
  simpa [ratCoordMatrix_inr] using
    congrArg Prod.snd (Y.hasDegreeGe_zero_of_mem_besselGroup h_mem p q h)

omit [Fintype X] in
/-- The Bessel group of a grading fixes each string vector of grade `≥ 0` up to vectors of higher
grade. If `W` agrees with `c` times the finite part of the shift up to a matrix that does not lower
grades, then so does `r' W r`, read in rational coordinates. Here `r ∈ Y.besselFin` and
`r' ∈ Y'.besselFin` are finite points of the Bessel groups of `Y` and `Y'`. -/
lemma hasDegreeGe_zero_mul_mul_sub [Finite X] [Finite X'] {W : Matrix ι' ι (𝔸f E)}
    {c : 𝔸f E}
    (hW : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (W - c • (Y.stringMap Y').map Prod.snd))
    {r : Gf E ι} (hr : r ∈ Y.besselFin) {r' : Gf E ι'} (hr' : r' ∈ Y'.besselFin) :
    HasDegreeGe Y'.gradeOf Y.gradeOf 0
      (V'.ratCoordMatrixFin r' * (W * V.ratCoordMatrixFin r) -
        c • (Y.stringMap Y').map Prod.snd) := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite X'
  set sh : Matrix ι' ι (𝔸f E) := (Y.stringMap Y').map Prod.snd
  set A : Matrix ι ι (𝔸f E) := V.ratCoordMatrixFin r
  set A' : Matrix ι' ι' (𝔸f E) := V'.ratCoordMatrixFin r'
  have h_fixed : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (A' * (sh * A) - sh) := fun p q h ↦ by
    simpa [ratCoordMatrix_inr, Matrix.mul_apply, Prod.snd_sum, sh, A, A'] using
      congrArg Prod.snd (Y.hasDegreeGe_zero_mul_stringMap_mul_sub hr hr' p q h)
  have h_split : A' * (W * A) - c • sh = A' * ((W - c • sh) * A) + c • (A' * (sh * A) - sh) := by
    simp [Matrix.sub_mul, Matrix.mul_sub, smul_sub]
  -- Degrees add under multiplication, so all three factors together have degree at least `0`.
  have h_error : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (A' * ((W - c • sh) * A)) :=
    (hasDegreeGe_zero_ratCoordMatrixFin hr').mul
      (hW.mul (hasDegreeGe_zero_ratCoordMatrixFin hr) (zero_add 0).ge) (zero_add 0).ge
  intro p q h
  rw [h_split, Matrix.add_apply, Matrix.smul_apply, h_error p q h, h_fixed p q h, smul_zero,
    add_zero]

variable [WeilData E]

omit [Fintype X] in
/-- Let `D` be a Witt decomposition of `Hom (V, V')` with isotropic basis `D.k` indexed by the
entries of positive degree and with complement `V₀`. The zero term
`D.zeroTerm : 𝒮 (Hom (V, V')) → 𝒮 V₀` averages theta functions along `D.k`, and `zeroTermFin D F` is
the zero term of `v ⊗ F` for a fixed translate `v` of the Fock vacuum. Assume that the constant term
is the theta value on `V₀` of the zero term. Let `t` be a vector of the real Fock space of
`Hom (V, V')`, `f` a vector of the Weil representation `𝒮 (V.hom V')` and
`t ⊗ f = (V.hom V').integrated t f`. Translate `t ⊗ f` by adelic points `(x, x')` of `U(V) × U(V')`
in the Weil representation twisted by the characters `μ ι`, `μ ι'` of `[U(1)]`. If the constant term
of this translate at `sh`, `Y.constTermAtStringMap Y' μ (t ⊗ f) x x'`, is nonzero, then
`zeroTermFin D` does not kill the translate of `f` by the finite part of `(x, x')` and then by the
finite Heisenberg operator of `sh`. -/
lemma zeroTermFin_finHeisenbergOp_stringMap_ne_zero {μ : (n : Type) → [Fintype n] → AutChar E}
    {t : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε')))}
    {f : 𝒮 (V.hom V')} {x : G E ε} {x' : G E ε'}
    {m : ℕ} {s₀ : Fin m → ℤˣ} {V₀ : Space E (Fin m) s₀}
    {D : (V.hom V').Splitting V₀ {r : ι' × ι // 0 < Y.mapDegree Y'.gradeOf r}}
    (h_theta : ∀ (F : 𝒮 (V.hom V')) (w : Matrix ι' ι (𝔸 E)),
      Y.constTerm Y'.gradeOf F w = V₀.θ (D.zeroTerm (homHeisenbergOp w F)))
    (h_ne : Y.constTermAtStringMap Y' μ ((V.hom V').integrated t f) x x' ≠ 0) :
    zeroTermFin D ((V.hom V').finHeisenbergOp (finCoord (V.homAtPoint V' (Y.stringMap Y')))
      ((V.hom V').ω (1, (G.onHom (x, x')).2) f)) ≠ 0 := by
  let v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε'))) :=
    Fock.realWeil (Fock.blockU (G.onHom (x, x')).1) t
  let y : ι' × ι → 𝔸 E := V.homAtPoint V' (Y.stringMap Y')
  -- Each operation acts separately on the real and on the finite factor of a pure tensor.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E s₀)),
      ∀ F : 𝒮 (V.hom V'), D.zeroTerm ((V.hom V').ϱ y ((V.hom V').integrated v F)) =
        V₀.integrated t₀ (zeroTermFin D ((V.hom V').finHeisenbergOp (finCoord y) F)) :=
    exists_zeroTerm_rho_integrated_eq D y v
  have h_omega : (V.hom V').ω (G.onHom (x, x')) ((V.hom V').integrated t f) =
      (V.hom V').integrated v ((V.hom V').ω (1, (G.onHom (x, x')).2) f) := by
    simp [omega_integrated, v]
  intro h_zero
  have h_zeroTerm :
      D.zeroTerm ((V.hom V').ϱ y ((V.hom V').ω (G.onHom (x, x')) ((V.hom V').integrated t f))) =
        0 := by
    rw [h_omega, ht₀, h_zero, map_zero]
  -- The characters only contribute a scalar factor, and the theta value of `0` is `0`.
  apply h_ne
  simp [h_theta, pairWeil_apply, h_zeroTerm, y]

/-- Let `M` be an adelic matrix and `l` a finite vector. Subtract `c g l`, where `g` is the finite
part of `(x, x')` acting on `Hom (V, V')`, from the finite coordinates of the point of
`Hom (V, V')` given by `M`. In rational coordinates the difference is the finite part of `M`
divided by the idele `α` of the Weil data, less `c` times the product of `V'.xFin x'.2`, the matrix
of `l` and the inverse of `V.xFin x.2`. -/
lemma xFin_mulVec_finCoord_homAtPoint_sub {x : G E ε} {x' : G E ε'} (M : Matrix ι' ι (𝔸 E))
    (l : ι' × ι → 𝔸f E) (c : 𝔸f E) :
    (V.hom V').xFin.val *ᵥ (finCoord (V.homAtPoint V' M) -
        (c • ((G.onHom (x, x')).2 : Matrix (ι' × ι) (ι' × ι) (𝔸f E))) *ᵥ l) =
      matrixToVec ((α : (𝔸f E)ˣ)⁻¹.val • M.map Prod.snd -
        c • ((V'.xFin * x'.2.val).val * vecToMatrix l * (V.xFin * x.2.val)⁻¹.val)) := by
  have h_xFin : (V.hom V').xFin.val = V'.xFin.val ⊗ₖ V.xFin⁻¹.valᵀ := rfl
  have h_cancel (A : Matrix ι' ι (𝔸f E)) : V'.xFin.val * (V'.xFin⁻¹.val * A) = A := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h_xFin, finCoord_homAtPoint, G.onHom_snd, smul_mulVec, mulVec_sub, mulVec_smul]
  simp only [kronecker_mulVec_eq_matrixToVec, vecToMatrix_matrixToVec]
  funext pq
  -- `coe_units_inv` would turn the inverse units into matrix inverses and hide the cancellations.
  simp [matrixToVec, Matrix.mul_assoc, -coe_units_inv, h_cancel]

omit [Fintype X] in
/-- Let `t` be a vector of the real Fock space of `Hom (V, V')`, let `f ∈ 𝒮 (V.hom V')` and
`t ⊗ f = (V.hom V').integrated t f`. Translate `t ⊗ f` by adelic points `(x, x')` of `U(V) × U(V')`
in the Weil representation twisted by the characters `μ ι`, `μ ι'` of `[U(1)]`. Let the constant
term of this translate at `sh` be nonzero, and let `f` be fixed by the finite Heisenberg operators
of `b Ô ^ (ι' × ι)`. Then some matrix `W` maps the lattice `V.lattice x.2` into `V'.lattice x'.2`
and agrees with `b̄ / α` times the finite part of `sh` up to a matrix that does not lower grades.
Here `α` is the finite idele of `WeilData E` that makes `Ô` self-dual. -/
lemma exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap [Finite X] [Finite X']
    {μ : (n : Type) → [Fintype n] → AutChar E}
    {t : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε')))}
    {f : 𝒮 (V.hom V')} {x : G E ε} {x' : G E ε'}
    (h_ne : Y.constTermAtStringMap Y' μ ((V.hom V').integrated t f) x x' ≠ 0) (b : (𝔸f E)ˣ)
    (hf : ∀ y ∈ stdLattice E (ι' × ι), finHeisenbergOp (V.hom V') (b.val • y) f = f) :
    ∃ W : Matrix ι' ι (𝔸f E), (∀ y ∈ V.lattice x.2, W *ᵥ y ∈ V'.lattice x'.2) ∧
      HasDegreeGe Y'.gradeOf Y.gradeOf 0
        (W - (star b / α).val • (Y.stringMap Y').map Prod.snd) := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite X'
  -- Take a splitting `D` along the maps of positive degree. The constant term is a theta value of
  -- the zero term, so the finite zero term does not vanish at `sh`, and `sh` lies in its support.
  obtain ⟨m, s₀, V₀, D, -, h_proj, h_theta⟩ :
      ∃ (m : ℕ) (s₀ : Fin m → ℤˣ) (V₀ : Space E (Fin m) s₀)
        (D : (V.hom V').Splitting V₀ {r : ι' × ι // 0 < Y.mapDegree Y'.gradeOf r}),
        D.k = inclMatrix E Subtype.val ∧
        (V.hom V').J⁻¹ * (D.k * (D.kᴴ * (V.hom V').J)) =
          diagonal (fun r : ι' × ι ↦ if Y.mapDegree Y'.gradeOf r < 0 then 1 else 0) ∧
        ∀ (F : 𝒮 (V.hom V')) (w : Matrix ι' ι (𝔸 E)),
          Y.constTerm Y'.gradeOf F w = V₀.θ (D.zeroTerm (homHeisenbergOp w F)) :=
    Y.exists_splitting_constTerm Y'.gradeOf_stringReversal
  let g : Gf E (ι' × ι) := (G.onHom (x, x')).2
  have h_period (y : ι' × ι → 𝔸f E) (hy : y ∈ stdLattice E (ι' × ι)) :
      (V.hom V').finHeisenbergOp ((b.val • g.val.val) *ᵥ y) ((V.hom V').ω (1, g) f) =
        (V.hom V').ω (1, g) f := by
    simpa [omega_finHeisenbergOp, smul_mulVec, mulVec_smul] using
      congrArg ((V.hom V').ω (1, g)) (hf y hy)
  have h_unitary : (b.val • g.val.val) * (star b⁻¹.val • g.val.val)ᴴ = 1 := by
    simp [← U.inv_val_eq_conjTranspose, smul_smul]
  -- The finite coordinates `z` of `sh` are, up to the orthogonal of `D.k`, a vector `b̄⁻¹ g l` of
  -- the dual lattice. In rational coordinates `l` becomes the matrix `W`.
  let z : ι' × ι → 𝔸f E := finCoord (V.homAtPoint V' (Y.stringMap Y'))
  have h_zeroTerm : zeroTermFin D ((V.hom V').finHeisenbergOp z ((V.hom V').ω (1, g) f)) ≠ 0 :=
    zeroTermFin_finHeisenbergOp_stringMap_ne_zero h_theta h_ne
  obtain ⟨l, hl, h_supp⟩ :
      ∃ l ∈ stdLattice E (ι' × ι), D.isotropicBasisFinᴴ *ᵥ (z - (star b⁻¹.val • g.val.val) *ᵥ l) =
        0 :=
    exists_sub_orthogonal_of_zeroTermFin_ne_zero D _ _ h_zeroTerm h_unitary h_period
  set sh : Matrix ι' ι (𝔸f E) := (Y.stringMap Y').map Prod.snd
  let W : Matrix ι' ι (𝔸f E) := (V'.xFin * x'.2.val).val * vecToMatrix l * (V.xFin * x.2.val)⁻¹.val
  have h_rat : (V.hom V').xFin.val *ᵥ (z - (star b⁻¹.val • g.val.val) *ᵥ l) =
      matrixToVec ((α : (𝔸f E)ˣ)⁻¹.val • sh - star b⁻¹.val • W) :=
    xFin_mulVec_finCoord_homAtPoint_sub (Y.stringMap Y') l (star b⁻¹.val)
  -- Applying `J⁻¹ * D.k` to `h_supp` keeps the entries of negative degree.
  have h_neg :
      (diagonal fun r : ι' × ι ↦ if Y.mapDegree Y'.gradeOf r < 0 then (1 : E) else 0).map
        (algebraMap E (𝔸f E)) *ᵥ matrixToVec ((α : (𝔸f E)ˣ)⁻¹.val • sh - star b⁻¹.val • W) = 0 := by
    rw [D.conjTranspose_isotropicBasisFin, ← mulVec_mulVec, h_rat] at h_supp
    rw [← h_proj, Matrix.map_mul, Matrix.map_mul, ← mulVec_mulVec, ← mulVec_mulVec, h_supp,
      mulVec_zero, mulVec_zero]
  refine ⟨W, fun y hy ↦ ?_, fun p q h_deg ↦ ?_⟩
  · rw [mem_lattice, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact IsIntMatrix.mulVec (fun p q ↦ hl (p, q)) hy
  · have h_entry : (α : (𝔸f E)ˣ)⁻¹.val * sh p q = star b⁻¹.val * W p q := by
      have h_lt : Y'.gradeOf p < Y.gradeOf q := by lia
      simpa [mulVec_diagonal, mapDegree, h_lt, matrixToVec, sub_eq_zero] using congrFun h_neg (p, q)
    calc (W - (star b / α).val • sh) p q
      _ = W p q - (star b).val * ((α : (𝔸f E)ˣ)⁻¹.val * sh p q) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = 0 := by simp [h_entry, ← mul_assoc, ← star_mul]

omit [Fintype X] in
/-- The gradings `Y`, `Y'` split the bases of the Hermitian spaces `V`, `V'` (of signs `ε`, `ε'` at
the infinite places) into blocks `X`, `X'` of grade `0` and strings of `s` and `s - 1` vectors,
which span `X^⊥` and `X'^⊥`. The shift `sh = Y.stringMap Y'`, with finite part `Y.stringMapFin Y'`,
is the rational map `V → V'` that kills `X` and sends each string vector to a multiple of the one
with the same number; it lowers grades by one. The constant term at `sh` of a vector of the Weil
representation `𝒮 (V.hom V')` is the mean of its theta function, translated by `sh`, over the adelic
maps `V → V'` that raise grades, modulo rational ones.

Let `t` be a vector of the real Fock space of `Hom (V, V')`, whose signs are the products of those
of `ε` and `ε'`, let `f ∈ 𝒮 (V.hom V')` and `t ⊗ f = (V.hom V').integrated t f`. Translate `t ⊗ f`
by adelic points `(x, x')` of `U(V) × U(V')` in the Weil representation twisted by the characters
`μ ι`, `μ ι'` of `[U(1)]`. Let the constant term of this translate at `sh` be nonzero, and let `f`
be fixed by the finite Heisenberg operators of `b Ô ^ (ι' × ι)`. Let `r`, `r'` be finite points of
the Bessel groups (which fix each string vector of grade `≥ 0` up to vectors of higher grade) such
that the lattices of `r x.2` and `r' x'.2` are graded, that is, contain the part in each grade of
each of their vectors. Then `b̄ / α` times the finite part of `sh` maps the projection to `X^⊥` of
the lattice of `r x.2` into the intersection with `X'^⊥` of the lattice of `r' x'.2`. Here `α` is
the finite idele of `WeilData E` that makes `Ô` self-dual. -/
lemma smul_map_stringMapFin_latticePlus_le [Finite X] [Finite X']
    {μ : (n : Type) → [Fintype n] → AutChar E}
    {t : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns ε ε')))}
    {f : 𝒮 (V.hom V')} {x : G E ε} {x' : G E ε'}
    (h_ne : Y.constTermAtStringMap Y' μ ((V.hom V').integrated t f) x x' ≠ 0) (b : (𝔸f E)ˣ)
    (hf : ∀ y ∈ stdLattice E (ι' × ι), finHeisenbergOp (V.hom V') (b.val • y) f = f)
    {r : Gf E ι} (hr : r ∈ Y.besselFin) (h_graded : Y.IsGraded (V.lattice (r * x.2)))
    {r' : Gf E ι'} (hr' : r' ∈ Y'.besselFin) (h_graded' : Y'.IsGraded (V'.lattice (r' * x'.2))) :
    (star b / α).val • (Y.latticePlus (r * x.2)).map ((Y.stringMapFin Y').restrictScalars (Ô E)) ≤
      Y'.latticeMinus (r' * x'.2) := by
  set c : 𝔸f E := (star b / α).val
  obtain ⟨W, hW_mem, hW_deg⟩ : ∃ W : Matrix ι' ι (𝔸f E),
      (∀ y ∈ V.lattice x.2, W *ᵥ y ∈ V'.lattice x'.2) ∧
      HasDegreeGe Y'.gradeOf Y.gradeOf 0 (W - c • (Y.stringMap Y').map Prod.snd) :=
    exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap h_ne b hf
  -- Move `W` to the graded points; `c sh` is its part of degree `-1`.
  let W₀ : Matrix ι' ι (𝔸f E) := V'.ratCoordMatrixFin r' * (W * V.ratCoordMatrixFin r⁻¹)
  have hW₀_mem : ∀ y ∈ V.lattice (r * x.2), W₀ *ᵥ y ∈ V'.lattice (r' * x'.2) := fun y hy ↦ by
    rw [← mulVec_mem_lattice_mul (g := r⁻¹), inv_mul_cancel_left] at hy
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_mem_lattice_mul]
    exact hW_mem _ hy
  have hW₀_deg : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (W₀ - c • (Y.stringMap Y').map Prod.snd) :=
    hasDegreeGe_zero_mul_mul_sub hW_deg (inv_mem hr) hr'
  have h_part (p : ι') (q : ι) : (c • (Y.stringMap Y').map Prod.snd) p q =
      if Y'.gradeOf p = Y.gradeOf q + -1 then W₀ p q else 0 := by
    split_ifs with h
    · exact (sub_eq_zero.1 (hW₀_deg p q (by lia))).symm
    · simp [stringMap_eq_zero_of_gradeOf_ne h]
  -- An element of the left side is `c sh y'` with `y'` the projection of a lattice vector `y`.
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  change c • Y.stringMapFin Y' (Y.stringProj y) ∈ Y'.latticeMinus (r' * x'.2)
  have h_mem : (c • (Y.stringMap Y').map Prod.snd) *ᵥ y ∈ V'.lattice (r' * x'.2) :=
    h_graded.mulVec_mem_of_homogeneous h_graded' hW₀_mem h_part hy
  rw [stringMapFin_stringProj, mem_latticeMinus, map_smul, stringProj_stringMapFin]
  exact ⟨by simpa [stringMapFin, smul_mulVec] using h_mem, rfl⟩

end Grading

end New

end
end
end

section
/-!
# Congruence levels inside the stabilizer of a glued lattice

A grading `Y` of a hermitian space `V` (a choice of basis vectors with a fixed Gram matrix) embeds
the finite adelic unitary group on `X ⊕ Unit` into that of `V`. When the lattice of `V` is the glued
lattice of `Y`, this file gives congruences on an element of the small group that put its image
into the stabilizer of the lattice, or into a congruence level of it.

Notions from other files:
* `Grading V N (X ⊕ Unit) s` splits the index set `ι` of the basis of `V` into `X ⊕ Unit`, on
  which the Gram matrix is `1`, and a string of `s` vectors, orthogonal to it and with a fixed Gram
  matrix that depends on `N`; `Y.inclXFin` is the resulting map on finite adelic unitary groups.
* The glued lattice of `Y` is the `Ô`-span of the columns of
  `gradedLatticeBasis Y.indexEquiv a π u`. For odd `s` it glues the last vector of `X ⊕ Unit` to
  the middle vector of the string.
* `Y.SpansLattice a π u`: the frame `V.xFin` of `V` spans the glued lattice. So in coordinates of
  this frame the glued lattice is the standard lattice `Ô^ι`.
* `IsSplitSquarefree P N π`: `N = π π̄`, the idele `π` is a uniformizer at the places in `P` and a
  unit elsewhere, and `P` contains no place together with its conjugate.
* `congruenceGL M e`: the integral invertible matrices whose rows `e i` agree with those of `1`
  modulo `M`.
* `stdLevel E ι` is the stabilizer of `Ô^ι` in the finite adelic unitary group `Gf E ι`, and
  `levelOf w ⊥` is the subgroup of its elements congruent to `1` at every place `w i`.

## Relation to the literature

Related work: `Grading.inclXFin_mem_stdLevel` is related to Nikulin's criterion for extending
isometries to an overlattice: the congruence on `h` plays the part of the condition that an isometry
preserve the gluing.
-/

@[expose] public section

namespace New

open Filling Matrix Seesaw Space
variable {E X ι : Type _} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype X]
  [DecidableEq X] {ε : ι → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} (Y : Grading V N (X ⊕ Unit) s)
  {a π : (𝔸f E)ˣ}

/-- Let the grading `Y` split the index set `ι` of a basis of the hermitian space `V` over `E` into
`X ⊕ Unit` and a string of `s` vectors with a fixed Gram matrix depending on `N`. It gives the map
`Y.inclXFin` from the finite adelic unitary group `Gf E (X ⊕ Unit)` to `Gf E ι`, that of `V` in the
coordinates of its frame `V.xFin`. Assume that this frame spans the glued lattice of `Y`, that is,
the `Ô`-span of the basis `gradedLatticeBasis Y.indexEquiv a π u`, with ideles `a`, `π` and a
unitary adele `u` as parameters (`SpansLattice`).

Then there is an integral matrix `R` such that the image of every `h` is the matrix `1 + Rᴴ M R`.
Here `M = h - 1` if `s` is even; if `s` is odd, the last row (index `Sum.inr ()`) of `h - 1` is
divided by `π` and its last column by `star π` (`scaleAt p o` is the diagonal matrix with `p` at
`o` and `1` elsewhere). -/
lemma Grading.exists_inclXFin_sub_one_eq {u : unitary (𝔸f E)} (hL : Y.SpansLattice a π u) :
    ∃ R : Matrix (X ⊕ Unit) ι (𝔸f E), IsIntMatrix (Ô E) R ∧ ∀ h : Gf E (X ⊕ Unit),
      (Y.inclXFin h).val.val - 1 = Rᴴ * ((if Odd s then
        scaleAt π⁻¹.val (Sum.inr ()) * ((h.val.val - 1) * scaleAt (star π⁻¹.val) (Sum.inr ()))
        else h.val.val - 1) * R) := by
  -- In rational coordinates the element acts as `h` on `X ⊕ Unit` and as `1` on the string, so its
  -- matrix is `1 + Aᴴ (h - 1) A`, with `A` the rows of `V.xFin = gradedLatticeBasis · k` indexed by
  -- `X ⊕ Unit`. These are the rows `R` of `k`, the last divided by `star π` when `s` is odd.
  obtain ⟨k, hk, xFin_eq⟩ := hL
  set e : (X ⊕ Unit) ⊕ Fin s ≃ ι := Y.indexEquiv with he
  set R : Matrix (X ⊕ Unit) ι (𝔸f E) := of fun x ↦ k.val (e (Sum.inl x)) with hR
  refine ⟨R, fun x ↦ hk.isIntMatrix _, fun h ↦ ?_⟩
  have h_conj : (Y.inclXFin h).val.val - 1 =
      V.xFin⁻¹ * (V.ratCoordMatrixFin (Y.inclXFin h) - 1) * V.xFin := by
    simp [ratCoordMatrixFin, sub_mul, mul_sub, mul_assoc]
  set D : Matrix (X ⊕ Unit) (X ⊕ Unit) (𝔸f E) :=
    if Odd s then scaleAt (star π⁻¹.val) (Sum.inr ()) else 1 with hD
  -- The Gram matrix times `(h ⊕ 1) - 1` lives on the block `X ⊕ Unit`, where it is `h - 1`.
  have h_block : V.J.map (↑) * (gradedBlocks e e h.val.val 1 - 1) =
      reindex e e (fromBlocks (h.val.val - 1) 0 0 0) := by
    ext i j
    obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := e.surjective i, e.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Y.gram_eq, ← he, gradedGram, gradedBlocks, Matrix.mul_apply, (reindex_equiv e).2,
        Matrix.one_apply, mul_sub]
  -- The rows of `V.xFin` in that block are those of `R`, the last divided by `star π` for odd `s`.
  have h_rows : V.xFin.val.submatrix (e ∘ Sum.inl) id = D * R := by
    ext (x | x) j <;> by_cases hs : Odd s <;>
      simp [xFin_eq, hD, hR, hs, Matrix.mul_apply, gradedLatticeBasis, diagonal,
        (reindex_equiv e).2]
  have h_restrict (A : Matrix (X ⊕ Unit) (X ⊕ Unit) (𝔸f E)) :
      V.xFin.valᴴ * reindex e e (fromBlocks A 0 0 0) * V.xFin.val = (D * R)ᴴ * A * (D * R) := by
    rw [← h_rows]
    ext i j
    simp [Matrix.mul_apply, (reindex_equiv e).2]
  rw [h_conj, Units.inv_eq_of_mul_eq_one_left gram_xFin, Y.ratCoordMatrixFin_inclXFin,
    Matrix.mul_assoc _ (V.J.map _), h_block, h_restrict, hD]
  split <;> simp [conjTranspose_mul, Matrix.mul_assoc, Pi.star_def, apply_ite star]

/-- Suppose that the frame `V.xFin` of `V` spans the glued lattice, the `Ô`-span of the explicit
basis `gradedLatticeBasis Y.indexEquiv a π u` (`SpansLattice`). Suppose also that `N = π π̄` and
that the idele `π` is a uniformizer at the places of `P`, a set without conjugate pairs, and a unit
elsewhere (`IsSplitSquarefree`).

If a unitary `h` on `X ⊕ Unit` is integral and its last row (index `Sum.inr ()`) is that of `1`
modulo `π` (`congruenceGL`), then its image `Y.inclXFin h` in `Gf E ι` stabilizes the glued lattice:
in the coordinates of `V.xFin` this is `Ô^ι`, with stabilizer `stdLevel E ι`. -/
lemma Grading.inclXFin_mem_stdLevel {P : Finset (FinPlace E)} {u : unitary (𝔸f E)}
    {h : Gf E (X ⊕ Unit)} (hL : Y.SpansLattice a π u) (hπ : IsSplitSquarefree P N π)
    (h_cong : h.val ∈ congruenceGL (Ô E ∙ π.val) Sum.inr) :
    Y.inclXFin h ∈ stdLevel E ι := by
  obtain ⟨R, R_int, h_eq⟩ := Y.exists_inclXFin_sub_one_eq hL
  rw [mem_stdLevel, sub_eq_iff_eq_add.mp (h_eq h)]
  suffices M_int : IsIntMatrix (Ô E) (if Odd s then
      scaleAt π⁻¹.val (Sum.inr ()) * ((h.val.val - 1) * scaleAt (star π⁻¹.val) (Sum.inr ()))
      else h.val.val - 1) from
    (R_int.conjTranspose.mul (M_int.mul R_int)).add .one
  -- At every place `π` or its conjugate is a unit.
  have h_unit (w : FinPlace E) : Valued.v (π.val w) = 1 ∨ Valued.v (π.val (star w)) = 1 := by
    by_cases hw : w ∈ P <;> simp [hπ.v_apply, hw, hπ.star_notMem w]
  -- For odd `s`, as `h` is unitary, the congruence on its last row absorbs both divisions.
  split
  · exact isIntMatrix_scaleAt_mul_sub_one_mul_scaleAt π (Sum.inr ()) h_unit h_cong
  · exact h_cong.1.isIntMatrix.sub .one

omit [CMType E] in
/-- An element of the finite adelic unitary group lies in `levelOf w ⊥`, the integral elements whose
reduction modulo every place `w i` is trivial, if and only if it is integral (`stdLevel`) and each
entry of its matrix minus `1` has valuation less than `1` in the completion at each `w i` (taken by
`evalAt`). -/
lemma mem_levelOf_bot [NumberField E] [NumberField.IsCMField E] {I : Type} {w : I → FinPlace E}
    {g : Gf E ι} :
    g ∈ levelOf w ⊥ ↔ g ∈ stdLevel E ι ∧
      ∀ (i : I) (b c : ι), Valued.v (evalAt (w i) ((g.val.val - 1) b c)) < 1 := by
  simp only [mem_levelOf, ← exists_prop, Subgroup.mem_bot, funext_iff]
  exact exists_congr fun hg ↦ forall_congr' fun i ↦
    (stdLevel.map_eq_one ι).trans (forall₂_congr fun b c ↦ reduceAt_eq_zero)

/-- Suppose that the frame `V.xFin` of `V` spans the glued lattice, the `Ô`-span of the explicit
basis `gradedLatticeBasis Y.indexEquiv a π u` (`SpansLattice`), that `N = π π̄` with `π` a
uniformizer at the places of `P` and a unit elsewhere, `P` being without conjugate pairs
(`IsSplitSquarefree`), and that the places `w i` and their conjugates lie outside `P`.

If a unitary `h` on `X ⊕ Unit` is integral, its last row (index `Sum.inr ()`) is that of `1` modulo
`π` (`congruenceGL`) and it is congruent to `1` at every `w i`, then so is its image `Y.inclXFin h`
in the coordinates of `V.xFin`: it is integral and congruent to `1` at every `w i`. -/
lemma Grading.inclXFin_mem_levelOf {P : Finset (FinPlace E)} {u : unitary (𝔸f E)}
    {h : Gf E (X ⊕ Unit)} {I : Type} {w : I → FinPlace E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (h_cong : h.val ∈ congruenceGL (Ô E ∙ π.val) Sum.inr)
    (hw : ∀ i : I, w i ∉ P) (hw_star : ∀ i : I, star (w i) ∉ P) (h_level : h ∈ levelOf w ⊥) :
    Y.inclXFin h ∈ levelOf w ⊥ := by
  obtain ⟨R, R_int, h_eq⟩ := Y.exists_inclXFin_sub_one_eq hL
  refine mem_levelOf_bot.mpr ⟨Y.inclXFin_mem_stdLevel hL hπ h_cong, fun i b c ↦ ?_⟩
  obtain ⟨-, h_small⟩ := mem_levelOf_bot.mp h_level
  rw [h_eq h]
  set M : Matrix (X ⊕ Unit) (X ⊕ Unit) (𝔸f E) := if Odd s then
    scaleAt π⁻¹.val (Sum.inr ()) * ((h.val.val - 1) * scaleAt (star π⁻¹.val) (Sum.inr ()))
    else h.val.val - 1 with hM
  have M_small (x x' : X ⊕ Unit) : Valued.v (evalAt (w i) (M x x')) < 1 := by
    rw [hM]
    split
    · -- An entry is multiplied by some of `π⁻¹` and `star π⁻¹`, which are units at `w i`.
      simp only [scaleAt, diagonal_mul, mul_diagonal]
      split_ifs <;>
        simpa [idele_inv_apply_and_ne_zero, hπ.v_apply, hw, hw_star] using h_small i x x'
    · exact h_small i x x'
  -- Each entry of `Rᴴ M R` is a sum of products of an entry of `M` with two integral elements.
  simp only [Matrix.mul_apply, Finset.mul_sum, map_sum, map_mul]
  refine Valued.v.map_sum_lt one_ne_zero fun x _ ↦ Valued.v.map_sum_lt one_ne_zero fun x' _ ↦ ?_
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_left' (mem_Ô.1 (R_int.conjTranspose b x) (w i))).trans_lt
    ((mul_le_of_le_one_right' (mem_Ô.1 (R_int x' c) (w i))).trans_lt (M_small x x'))

end New
end
end

/-!
# Unfolding the chain of lifts: double lifts and the functions of the unfolding

A double theta integral over two definite unitary groups is a coefficient of the composite of two
lifts. Two unfolding steps give the double lift of the finite evaluation. Starting from `𝒲_φ`, each
unfolding step then gives an equivariant function on the next group `R_j`. Their supports are
bounded when the source form is ramified.

## Main definitions and results

* `New.Seesaw.DoubleLiftData.exists_integral_constTermAtStringMap_mul_eq`: take the product of two
  constant terms. Integrate it over the Bessel subgroup `New.Grading.besselGroup` of `Y'`, and over
  that of `Y` against an equivariant function `W`. The result is an integral over the unitary group
  of `X`. Its integrand is `W` times a constant times a theta integral over the unitary group of
  `X'`. The theta integral is of the datum translated by `New.Seesaw.stackedStringMap` and cut down
  along `New.Seesaw.DoubleLiftData.splitting`.
* `New.Data.unfoldStage`: the function `𝒲_{k+1}` that the first `k + 1` unfolding steps leave;
  `New.Data.exists_unfoldStage_eq_algFormCoeff` evaluates it after each double lift.
* `New.Data.hasLatticeBounds_of_unfoldStage_ne_zero`: the support lemma, in terms of graded
  lattices.

Notions from other files:
* `New.Grading`: A presentation of a hermitian space as a definite part `X` (grade 0) plus a string
  of `s` graded basis vectors; `Y.inclX` embeds the unitary group of `X`.
* `New.Seesaw.DoubleLiftData`: For gradings `Y, Y', Y''` of `V, V', V''`, it identifies the
  grade-zero part of V⁻ ⊕ V'' with X⁻ ⊕ X'' plus hyperbolic planes.
* `New.Space.Splitting.zeroTerm`: For a splitting with frames `i`, `k`, the map that sends a datum f
  to y ↦ the mean of f(i y + k b) over adelic vectors b modulo rational ones.
* `New.Seesaw.flipSum`: For hermitian spaces V and V'', the orthogonal sum V⁻ ⊕ V'' of V with its
  form negated and V''.
* `New.Seesaw.stackedStringMap`: The adelic map (T*, T') from V' to V⁻ ⊕ V'', where
  `T = Y.stringMap Y'` and `T' = Y'.stringMap Y''`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work. See
`Lib.Weil.CompactLift.DefiniteThetaLift` for sources.
-/

@[expose] public section

/-!
## Two unfolding steps and the double lift of the finite evaluation

Notation as in `New.UpperBound.Seesaw.EdgePairEvaluation`. `D : New.Seesaw.DoubleLiftData X'' q Y Y'
Y''` describes three graded spaces `V, V', V''` with definite parts. `New.Seesaw.arrowProduct` joins
data on `Hom (V, V')` and `Hom (V', V'')`, and `New.Seesaw.tripleWeil` is the joint Weil action.
`New.stdSpace E X` is the standard definite space on `X`, and `(stdSpace E X).quotMeasure`
integrates over its unitary group modulo rational points. `New.Grading.constTermAtStringMap` is the
constant term at the map `Y.stringMap Y'` along maps of positive degree. `New.algFormCoeff 1 t φ` is
the coefficient of an algebraic form `φ` at a linear form `t`.
-/

namespace New.Seesaw

open Matrix MeasureTheory Space Subtype Fintype Exchange Splitting Grading LinearMap MvPolynomial
  Subgroup Fock CoordChange Finset

variable {E ι ι' ι'' X X' X'' X₀ q : Type} [Field E] [CMType E] [WeilData E] [Fintype ι]
  [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι''] [Fintype X]
  [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X''] [Fintype X₀]
  [DecidableEq X₀] [Fintype q] [DecidableEq q] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {N : E}
  {s s' s'' : ℕ} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}
  {Y : Grading V N X s} {Y' : Grading V' N X' s'} {Y'' : Grading V'' N X₀ s''}

omit [WeilData E] in
private lemma continuous_pairChar (a b : AutChar E) :
    Continuous (pairChar (E := E) (s := ε) (s' := ε') a b) :=
  continuous_subtypeVal.comp
    (((b⁻¹.val.continuous.comp G.continuous_det).comp continuous_fst).mul
      ((a.val.continuous.comp G.continuous_det).comp continuous_snd))

private lemma continuous_theta_tripleWeil (a b : AutChar E)
    (f : 𝒮 (V'.hom (flipSum V V''))) :
    Continuous fun p : G E ε × G E ε' × G E ε'' ↦
      θ (V'.hom (flipSum V V'')) (tripleWeil (V := V) (V' := V') (V'' := V'') a b p f) := by
  have h_sum : Continuous (G.sum : G E (-ε) × G E ε'' → G E (-ε ⊕ᵥ ε'')) := by
    rw [G.continuous_iff]
    simp only [G.adeleMatrix_sum]
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    rcases i with i | i <;> rcases j with j | j
    · exact ((continuous_apply j).comp ((continuous_apply i).comp
        G.continuous_adeleMatrix)).comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact ((continuous_apply j).comp ((continuous_apply i).comp
        G.continuous_adeleMatrix)).comp continuous_snd
  have h_c1 : Continuous fun p : G E ε × G E ε' × G E ε'' ↦
      pairChar (rankTwist a ι) (rankTwist a ι') (p.1, p.2.1) :=
    (continuous_pairChar _ _).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h_c2 : Continuous fun p : G E ε × G E ε' × G E ε'' ↦
      pairChar (rankTwist b ι') (rankTwist b ι'') p.2 :=
    (continuous_pairChar _ _).comp continuous_snd
  have h_c3 : Continuous fun p : G E ε × G E ε' × G E ε'' ↦
      pairChar (WeilData.upsilonU1 ^ card ι') (WeilData.upsilonU1 ^ card ι) (p.2.1, p.1) :=
    (continuous_pairChar _ _).comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst)
  have h_onHom : Continuous fun p : G E ε × G E ε' × G E ε'' ↦
      G.onHom (p.2.1, G.sum (p.1.neg, p.2.2)) :=
    G.continuous_onHom.comp ((continuous_fst.comp continuous_snd).prodMk
      (h_sum.comp ((G.continuous_neg.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd))))
  have h_ω : Continuous fun p : G E ε × G E ε' × G E ε'' ↦
      θ (V'.hom (flipSum V V''))
        ((V'.hom (flipSum V V'')).ω (G.onHom (p.2.1, G.sum (p.1.neg, p.2.2))) f) :=
    (θ _).continuous.comp
      ((Space.continuous_omega (V := V'.hom (flipSum V V''))).comp
        (h_onHom.prodMk continuous_const))
  simpa only [tripleWeil, _root_.smul_apply, map_smul, smul_eq_mul, Pi.mul_def, Pi.mul_apply] using
    ((h_c1.mul h_c2).mul h_c3).mul h_ω

/-- A coefficient of an algebraic form times the theta function of a triple Weil translate is
integrable over the compact quotients of the two definite unitary groups. -/
lemma integrable_algFormCoeff_mul_theta_tripleWeil {κ : NumberField.InfinitePlace E → ℕ → ℕ}
    {e : NumberField.InfinitePlace E → ℤ} (a b : AutChar E)
    (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) (φ : ↥(AlgForm X κ e)) (g : G E (1 : X'' → ℤˣ))
    (f : 𝒮 ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))) :
    Integrable (fun x : G E (1 : X → ℤˣ) × G E (1 : X' → ℤˣ) ↦ algFormCoeff 1 t φ x.1 *
        θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
          (tripleWeil a b (x.1, x.2, g) f))
      ((stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure) := by
  obtain ⟨h_cont, h_rat, -⟩ := (stdSpace E X).isAutomorphic_algFormCoeff (L := t) φ
  refine integrable_of_isCocompact (isCocompact_prod (stdSpace E X).isCocompact_Gamma
    (stdSpace E X').isCocompact_Gamma) ?_ ?_
  · -- the coefficient is continuous and the Weil action is continuous in the group points
    exact (h_cont.comp continuous_fst).mul
      ((continuous_theta_tripleWeil a b f).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))
  · -- both factors are invariant under rational points
    rintro ⟨γ, δ⟩ ⟨hγ, hδ⟩ ⟨x, r⟩
    simp only [Prod.mk_mul_mk, h_rat γ hγ x, theta_tripleWeil_rat_mul a b f hγ hδ x r g]

/-- Write `P ⊗ Φ` for `integrated` applied to the Fock vector `polyVector P` and the finite datum
`Φ`. Combining with `arrowProduct` the data `P ⊗ Φ` on `Hom(X, X')` and `Q ⊗ Φ'` on `Hom(X', X'')`,
for polynomials `P` and `Q`, gives the datum `P Q ⊗ arrowTensor (Φ ⊗ Φ')` on `Hom(X', X⁻ ⊕ X'')`.
The variables of `P` are transposed into the block of `X`, and those of `Q` go into the block of
`X''`. -/
lemma arrowProduct_integrated_polyVector (P : MvPolynomial (NumberField.InfinitePlace E × X' × X) ℂ)
    (Q : MvPolynomial (NumberField.InfinitePlace E × X'' × X') ℂ)
    (Φ : ((stdSpace E X).hom (stdSpace E X')).finitePart)
    (Φ' : ((stdSpace E X').hom (stdSpace E X'')).finitePart) :
    arrowProduct
        (integrated ((stdSpace E X).hom (stdSpace E X'))
          (polyVector (realSigns E (homSigns (1 : X → ℤˣ) (1 : X' → ℤˣ))) P) Φ)
        (integrated ((stdSpace E X').hom (stdSpace E X''))
          (polyVector (realSigns E (homSigns (1 : X' → ℤˣ) (1 : X'' → ℤˣ))) Q) Φ') =
      integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
        (polyVector (realSigns E (homSigns (1 : X' → ℤˣ) (-(1 : X → ℤˣ) ⊕ᵥ (1 : X'' → ℤˣ))))
          (rename (fun (v, j, i) ↦ (v, Sum.inl i, j)) P *
            rename (fun (v, i, j) ↦ (v, Sum.inr i, j)) Q))
        (arrowTensor (Φ ⊗ₜ Φ')) := by
  simp [arrowProduct, flipPoly, pairSign, rename_eq_aeval, comp_aeval_apply, map_integrated,
    realMap_flipCoords_polyVector, boxProd_integrated, realBoxProd_polyVector]
  -- the two descriptions of the renamed variables of `P` and `Q` agree by definition
  rfl

/-- Write U(X) for the adelic unitary group of the standard definite space `stdSpace E X`, and
`flipSum` for the sum X⁻ ⊕ X'' of X with its form negated and X''. Let the families `k`, `k'`
compute the theta lifts of algebraic forms from `X` to `X'` and from `X'` to `X''` (`IsThetaLift`)
for the characters `rankTwist (a o)` and `rankTwist (b o)`, the twists of the automorphic characters
`a o`, `b o` of U(1) by a power of a fixed character that depends on the rank. Let `L o` be the
composite lift, which sends `Φ ⊗ Φ'` to `k' o Φ' ∘ k o Φ`. For every vector `u` of the Fock space of
`Hom(X', X⁻ ⊕ X'')` and every linear form `t` there is a linear form `t''` with the following
property for all `o`, finite data `y`, forms `φ` and points `g` of U(X''). Carry `y` to
`Hom(X', X⁻ ⊕ X'')` by `arrowTensor`, tensor it with `u` (`integrated`), and move it by `(x, r, g)`
under the Weil action `tripleWeil (a o) (b o)` of U(X) × U(X') × U(X''). Integrate its theta value
over `r`, and then over `x` against the coefficient of `φ` at `t`, both modulo rational points. The
result is the coefficient of `L o y φ` at `t''`, taken at `g`. -/
lemma integral_theta_tripleWeil_eq_lift_comp {κ : NumberField.InfinitePlace E → ℕ → ℕ}
    {e e' e'' : NumberField.InfinitePlace E → ℤ} {O : Type*}
    {k : O → ↥((stdSpace E X).hom (stdSpace E X')).finitePart →ₗ[ℂ]
      ↥(AlgForm X κ e) →ₗ[ℂ] ↥(AlgForm X' κ e')}
    {k' : O → ↥((stdSpace E X').hom (stdSpace E X'')).finitePart →ₗ[ℂ]
      ↥(AlgForm X' κ e') →ₗ[ℂ] ↥(AlgForm X'' κ e'')}
    {a b : O → AutChar E} (hk : IsThetaLift κ e e' (fun o : O ↦ rankTwist (a o)) k)
    (hk' : IsThetaLift κ e' e'' (fun o : O ↦ rankTwist (b o)) k')
    (u : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E
      (homSigns (1 : X' → ℤˣ) (-(1 : X → ℤˣ) ⊕ᵥ (1 : X'' → ℤˣ))))))
    (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) :
    -- the composite lift: `L o (Φ ⊗ₜ Φ')` is `k' o Φ'` after `k o Φ`
    let L (o : O) : TensorProduct ℂ ↥((stdSpace E X).hom (stdSpace E X')).finitePart
        ↥((stdSpace E X').hom (stdSpace E X'')).finitePart →ₗ[ℂ]
          ↥(AlgForm X κ e) →ₗ[ℂ] ↥(AlgForm X'' κ e'') :=
      TensorProduct.lift (LinearMap.flip
        (compl₁₂ (llcomp ℂ (AlgForm X κ e) (AlgForm X' κ e') (AlgForm X'' κ e'')) (k' o) (k o)))
    ∃ t'' : (WeylIndex X'' κ → ℂ) →ₗ[ℂ] ℂ, ∀ (o : O)
      (y : TensorProduct ℂ ↥((stdSpace E X).hom (stdSpace E X')).finitePart
        ↥((stdSpace E X').hom (stdSpace E X'')).finitePart)
      (φ : ↥(AlgForm X κ e)) (g : G E (1 : X'' → ℤˣ)),
      ∫ x : G E (1 : X → ℤˣ), algFormCoeff 1 t φ x *
          ∫ r : G E (1 : X' → ℤˣ),
            θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
              (tripleWeil (V'' := stdSpace E X'') (a o) (b o) (x, r, g)
                (integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) u
                  (arrowTensor y))) ∂(stdSpace E X').quotMeasure
        ∂(stdSpace E X).quotMeasure =
      algFormCoeff 1 t'' (L o y φ) g := by
  -- The families given by a linear form `t''` make up a finite-dimensional, hence closed, space,
  -- and the family of integrals `J u` is continuous in `u`. So it suffices to take for `u` a Fock
  -- polynomial, a sum of products `P Q`, and then the double integral is an iterated theta lift.
  intro L
  obtain ⟨z, -, hz⟩ := theta_arrowProduct (stdSpace E X) (stdSpace E X') (stdSpace E X'')
  let F (o : O) (φ : AlgForm X κ e) (g : G E (1 : X'' → ℤˣ))
      (x : G E (1 : X → ℤˣ) × G E (1 : X' → ℤˣ)) :
      𝒮 ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) →L[ℂ] ℂ :=
    algFormCoeff 1 t φ x.1 •
      θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) ∘L
        tripleWeil (V'' := stdSpace E X'') (a o) (b o) (x.1, x.2, g)
  have hF {o : O} {φ : AlgForm X κ e} {g : G E (1 : X'' → ℤˣ)}
      (f : 𝒮 ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))) :
      Integrable (F o φ g · f) ((stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure) :=
    integrable_algFormCoeff_mul_theta_tripleWeil (a o) (b o) t φ g f
  let J (u : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E
        (homSigns (1 : X' → ℤˣ) (-(1 : X → ℤˣ) ⊕ᵥ (1 : X'' → ℤˣ)))))) (o : O)
      (y : TensorProduct ℂ ↥((stdSpace E X).hom (stdSpace E X')).finitePart
        ↥((stdSpace E X').hom (stdSpace E X'')).finitePart)
      (φ : AlgForm X κ e) (g : G E (1 : X'' → ℤˣ)) : ℂ :=
    strongIntegral ((stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure) (F o φ g)
      (integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) u (arrowTensor y))
  have hJ (u) (o : O) (y) (φ : AlgForm X κ e) (g : G E (1 : X'' → ℤˣ)) : J u o y φ g =
      ∫ x : G E (1 : X → ℤˣ) × G E (1 : X' → ℤˣ), F o φ g x
        (integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) u
          (arrowTensor y)) ∂(stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure := by
    simp [J, strongIntegral_apply, hF]
  -- `Λ t''` is the family on the right side of the claim, a linear function of `t''`.
  let Λ := IsLinearMap.mk' (R := ℂ)
    (fun (t'' : (WeylIndex X'' κ → ℂ) →ₗ[ℂ] ℂ) (o : O) y (φ : AlgForm X κ e) ↦
      algFormCoeff 1 t'' (L o y φ))
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  suffices h_mem : ∀ u, J u ∈ Λ.range by
    obtain ⟨t'', ht''⟩ := h_mem u
    refine ⟨t'', fun o y φ g ↦ ?_⟩
    have h_eq : J u o y φ g = algFormCoeff 1 t'' (L o y φ) g := by
      rw [← ht'']
      rfl
    rw [← h_eq, hJ, integral_prod _ (hF _)]
    simp [F, integral_const_mul]
  refine isClosed_property denseRange_polyVector
    (Λ.range.isClosed_of_finiteDimensional.preimage_of_continuous (f := J)) fun R ↦ ?_
  -- `R` is a sum of products of a polynomial on `Hom(X, X')` and one on `Hom(X', X'')`.
  let inl : NumberField.InfinitePlace E × X' × X → NumberField.InfinitePlace E × (X ⊕ X'') × X' :=
    fun (v, j, i) ↦ (v, Sum.inl i, j)
  let inr : NumberField.InfinitePlace E × X'' × X' → NumberField.InfinitePlace E × (X ⊕ X'') × X' :=
    fun (v, i, j) ↦ (v, Sum.inr i, j)
  have hR : R ∈ (rename inl).range.toSubmodule * (rename (R := ℂ) inr).range.toSubmodule :=
    mem_rename_range_mul inl inr (by
      rintro ⟨v, i | i, j⟩
      · exact Or.inl ⟨(v, j, i), rfl⟩
      · exact Or.inr ⟨(v, i, j), rfl⟩) R
  -- the polynomials that satisfy the claim are closed under addition, so products suffice
  have h_add (u₁ u₂) : J (u₁ + u₂) = J u₁ + J u₂ := by
    ext
    simp [J]
  refine Submodule.mul_induction_on hR ?_ fun P₁ P₂ h₁ h₂ ↦ by
    simpa only [Set.mem_preimage, SetLike.mem_coe, map_add, h_add] using add_mem h₁ h₂
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  obtain ⟨t', ht'⟩ := hk P t
  obtain ⟨t'', ht''⟩ := hk' (z • Q) t'
  use t''
  ext o y φ g
  change algFormCoeff 1 t'' (L o y φ) g = _
  induction y with
  | tmul Φ Φ' =>
    -- Unfold the left side by `ht''` and `ht'`: both sides are iterated integrals, and by `hz`
    -- the kernel of `P Q` is `z` times the product of the two theta kernels.
    have h_lift : L o (Φ ⊗ₜ Φ') φ = k' o Φ' (k o Φ φ) := by simp [L]
    rw [h_lift, ← ht'', hJ, integral_prod_symm _ (hF _)]
    refine integral_congr_ae (.of_forall fun r ↦ ?_)
    simp only [← ht', ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [F, map_smul, smul_eq_mul, mul_assoc, _root_.smul_apply,
      ContinuousLinearMap.comp_apply]
    have h_reorder (θQ θP c : ℂ) : z * (θQ * (θP * c)) = c * (z * (θP * θQ)) := by ring
    rw [h_reorder, ← hz, arrowProduct_twistedPairWeil, arrowProduct_integrated_polyVector]
    rfl
  | add y y' ih ih' =>
    rw [map_add, LinearMap.add_apply, map_add, Pi.add_apply, ih, ih']
    simp [J]

/-- Let `Y, Y', Y''` be gradings of the hermitian spaces `V, V', V''`, and let `D` be data for two
consecutive lifts. The constant term `Y.constTerm Y'.gradeOf f w` is the mean of the theta function
of `f`, Heisenberg translated by `w` (`homHeisenbergOp w`), over the maps `V → V'` that raise
grades. The datum `arrowProduct f f'` on `Hom(V', V⁻ ⊕ V'')` joins `f` and `f'`, where `V⁻` is `V`
with its form negated; by `hθ` its theta value is `z ≠ 0` times the product of those of `f` and
`f'`. The splitting `D.homZeroPart.splitting` cuts `Hom(V', V⁻ ⊕ V'')` down to its part of degree
zero, and its zero term is the mean over the maps of positive degree. Then the product of the
constant terms of `f` at `w` and of `f'` at `w'` is `z⁻¹` times the value at 0 of the zero term of
the join of the two translates. -/
lemma DoubleLiftData.constTerm_mul_constTerm_eq_inv_mul_zeroTerm (D : DoubleLiftData X'' q Y Y' Y'')
    {z : ℂ} (hz : z ≠ 0)
    (hθ : ∀ (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')),
      θ (V'.hom (flipSum V V'')) (arrowProduct f f') = z * ((V.hom V').θ f * (V'.hom V'').θ f'))
    (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')) (w : Matrix ι' ι (𝔸 E)) (w' : Matrix ι'' ι' (𝔸 E)) :
    Y.constTerm Y'.gradeOf f w * Y'.constTerm Y''.gradeOf f' w' = z⁻¹ *
      D.homZeroPart.splitting.zeroTerm
        (arrowProduct (homHeisenbergOp w f) (homHeisenbergOp w' f')) 0 := by
  -- The right side is a mean over the maps V' → V⁻ ⊕ V'' of positive degree. Such a map is a pair
  -- (a*, a') with a : V → V' and a' : V' → V'', so the mean is an iterated mean over a and a',
  -- and `hθ` factors the integrand.
  -- `φ (a, a')` is the map (a*, a'), cut down to its entries of positive degree
  let φ : (ι' × ι → 𝔸 E) × (ι'' × ι' → 𝔸 E) →+
      ({r : (ι ⊕ ι'') × ι' // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) r.1 - Y'.gradeOf r.2} → 𝔸 E) :=
    .mk' (fun a ↦ matrixToVec ((V.formAdjoint V' (vecToMatrix a.1)).fromRows (vecToMatrix a.2)) ∘
      val)
      (by simp [funext_iff, Y.formAdjoint_apply Y', mul_add, add_mul, vecToMatrix, matrixToVec])
  have h_cont : Continuous φ := by
    simp [continuous_pi_iff, φ, Y.formAdjoint_apply Y', -continuous_prodMk, vecToMatrix,
      matrixToVec, mul_assoc]
    exact ⟨by fun_prop, by fun_prop⟩
  have h_rat : ∀ a ∈ ratVectors E (ι' × ι), ∀ a' ∈ ratVectors E (ι'' × ι'),
      φ (a, a') ∈ ratVectors E _ := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    simp [mem_ratVectors, φ, Y.formAdjoint_apply Y', ← map_mul, ratAdeles, vecToMatrix, matrixToVec]
  have h_onto : Function.Surjective φ := by
    intro b₀
    obtain ⟨b, rfl⟩ := val_injective.surjective_comp_right b₀
    -- every entry comes from the pair (rows₁ b)*, rows₂ b
    use (matrixToVec (V'.formAdjoint V (vecToMatrix b).toRows₁),
      matrixToVec (vecToMatrix b).toRows₂)
    change matrixToVec (fromRows _ _) ∘ val = _
    simp [formAdjoint_formAdjoint]
  rw [eq_inv_mul_iff_mul_eq₀ hz, Splitting.zeroTerm_apply,
    ← quotMean_quotMean (ratVectors E (ι' × ι)) (isContPeriodic_along_k ..)
      (ratVectors E (ι'' × ι')) φ h_cont h_rat h_onto]
  -- both sides become double integrals of `θ` of one translate of `arrowProduct f f'`
  simp_rw [constTerm, quotMean, ← integral_mul_const, ← integral_const_mul, ← theta_rho, ← hθ,
    ← homHeisenbergOp_arrowProduct, homHeisenbergOp, ← x_inv_mulVec_matrixToVec, mulVec_zero,
    zero_add]
  congr! with a a'
  -- the translation vectors agree: (a*, a') has positive degree when a and a' have
  rw [← kAdelic_mulVec D.homZeroPart.splitting rfl]
  · congr 1
    simp +contextual [_root_.funext_iff, φ, Y.formAdjoint_apply Y', matrixToVec, vecToMatrix]
  · simp +contextual [Y.formAdjoint_apply Y', matrixToVec, vecToMatrix, LE.le.not_gt]

/-- The adjoint of a map (A, B) into V⁻ ⊕ V'' is (−A*, B*). -/
lemma formAdjoint_fromRows (A : Matrix ι ι' (𝔸 E)) (B : Matrix ι'' ι' (𝔸 E)) :
    V'.formAdjoint (flipSum V V'') (A.fromRows B) =
      (-V'.formAdjoint V A).fromCols (V'.formAdjoint V'' B) := by
  have hJ : (flipSum V V'').J.map toAdele =
      (-(V.J.map toAdele)).fromBlocks 0 0 (V''.J.map toAdele) := by
    refine Matrix.ext fun a b ↦ ?_
    rcases a with a | a <;> rcases b with b | b <;>
      simp [flipSum, flipSpace, Space.sum]
  have hM : V'.J⁻¹.map toAdele * (A.fromRows B)ᴴ =
      (V'.J⁻¹.map toAdele * Aᴴ).fromCols (V'.J⁻¹.map toAdele * Bᴴ) := by
    refine Matrix.ext fun i j ↦ ?_
    rcases j with j | j <;> simp [Matrix.mul_apply]
  rw [formAdjoint, formAdjoint, formAdjoint, hJ, hM]
  refine Matrix.ext fun i j ↦ ?_
  rcases j with j | j
  · rw [fromCols_apply_inl, Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fintype.sum_sum_type]
    simp only [fromCols_apply_inl, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero, Matrix.neg_apply, mul_neg,
      Finset.sum_neg_distrib]
  · rw [fromCols_apply_inr, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [fromCols_apply_inr, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add]

/-- Let `D` be data for the two consecutive lifts `Y → Y' → Y''`, and let `n` be a unipotent element
of U(V'), with matrix `V'.ratCoordMatrix n` in rational coordinates. Let
`S = stackedStringMap Y Y' Y''` be the map (T*, T') from V' to V⁻ ⊕ V'' made of the maps `T`, `T'`
between consecutive strings. As a vector of `Hom(V', V⁻ ⊕ V'')` in adelic coordinates
(`homAtPoint`), the map `S (n - 1)` is a sum of two parts. The first is a map of positive degree,
with entries `y`. The second is a map of degree zero that sends `X'` into an isotropic half of the
hyperbolic planes indexed by `q`. Its matrix is `Y'.genericConst`, the constant of the grading,
times the block of `n - 1` whose rows are the basis vectors `D.gradeOne` of grade one and whose
columns are `X'`. -/
lemma DoubleLiftData.exists_add_eq_homAtPoint_stackedStringMap (D : DoubleLiftData X'' q Y Y' Y'')
    {n : G E ε'} (hn : n ∈ Y'.unipotent) :
    ∃ y : { i : (ι ⊕ ι'') × ι' // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i.1 - Y'.gradeOf i.2 } → 𝔸 E,
      D.homZeroPart.splitting.kAdelic *ᵥ y +
          D.homZeroPart.splitting.iAdelic *ᵥ ((removePlanes q (flipSum (stdSpace E X)
            (stdSpace E X''))).homTarget (stdSpace E X')).kAdelic *ᵥ (fun p : q × X' ↦
            ↑Y'.genericConst * (V'.ratCoordMatrix n - 1) (D.gradeOne p.1)
              (Y'.indexEquiv (Sum.inl p.2))) =
        V'.homAtPoint (flipSum V V'') (stackedStringMap Y Y' Y'' * (V'.ratCoordMatrix n - 1)) := by
  obtain rfl : s' = s - 1 := D.length_middle
  obtain rfl : s'' = s - 1 - 1 := D.length_last
  -- in rational coordinates, the difference u of the two vectors lives in positive degree
  let σ := D.homZeroPart.splitting
  let planes := (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget (stdSpace E X')
  let u : (ι ⊕ ι'') × ι' → 𝔸 E :=
    matrixToVec (stackedStringMap Y Y' Y'' * (V'.ratCoordMatrix n - 1)) -
      (σ.i.map toAdele *
        ((stdSpace E X').hom (hyperbolicSum q (flipSum (stdSpace E X) (stdSpace E X'')))).x.val) *ᵥ
        planes.kAdelic *ᵥ fun p : q × X' ↦
          ↑Y'.genericConst * (V'.ratCoordMatrix n - 1) (D.gradeOne p.1) (Y'.indexEquiv (.inl p.2))
  have hu (p) (hp : ¬0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) p.1 - Y'.gradeOf p.2) : u p = 0 := by
    obtain h_ne | ⟨⟨i, l⟩, rfl⟩ := not_or_of_imp (D.homZeroPart.mem_range_index p).mpr
    · -- negative degree: `stackedStringMap` has degree ≥ -1 and n - 1 has degree ≥ 1, so the first
      -- term vanishes; the second term lives in degree zero
      have h_deg : HasDegreeGe (Y.gradeOf ⊕ᵥ Y''.gradeOf) Y'.gradeOf (-1)
          (stackedStringMap Y Y' Y'') := by
        rintro (i | i)
        · simp +contextual [stackedStringMap, Y.formAdjoint_apply Y',
            Y.hasDegreeGe_neg_one_stringMap _, add_comm]
        · exact Y'.hasDegreeGe_neg_one_stringMap i
      simp [u, σ, D.homZeroPart.incl_eq_zero, h_ne,
        ↓h_deg.mul (Y'.mem_unipotent.mp hn) le_rfl p.1 p.2 (by omega), GradeZeroPart.splitting,
        matrixToVec, Matrix.mul_apply, mulVec, dotProduct]
    · -- degree zero: p is a basis vector of the weight-zero part; compute the entry by
      -- `D.stackedStringMap_apply`
      simp [u, σ, planes, homZeroPart, GradeZeroPart.hom, D.stackedStringMap_apply, homTarget,
        removePlanes, inclMatrix, sum_prod_type, apply_ite toAdele, sum_mul, sum_comm, kAdelic,
        Matrix.mul_assoc, GradeZeroPart.splitting, Matrix.one_apply, matrixToVec, Matrix.mul_apply,
        mulVec, dotProduct, mul_assoc]
  -- the frame `k` returns `u`, and the frame `i` adds back what was subtracted
  use u ∘ val
  rw [show σ.kAdelic *ᵥ u ∘ val = (↑(V'.hom (flipSum V V'')).x⁻¹ : Matrix _ _ _) *ᵥ u from
    kAdelic_mulVec σ rfl hu, iAdelic, Space.ratMap, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_add,
    sub_add_cancel, x_inv_mulVec_matrixToVec]

/-- The stacked map `stackedStringMap Y Y' Y''` = (T*, T'), with `T = Y.stringMap Y'` and
`T' = Y'.stringMap Y''`, is isotropic. Its `formAdjoint` for `flipSum V V''` times it is -T T* + T'*
T' = 0: given the double-lift data `D`, both products depend only on `Y'` and the common constant
`genericConst`. -/
lemma formAdjoint_stackedStringMap_mul_stackedStringMap (D : DoubleLiftData X'' q Y Y' Y'') :
    V'.formAdjoint (flipSum V V'') (stackedStringMap Y Y' Y'') * stackedStringMap Y Y' Y'' = 0 := by
  obtain rfl : s' = s - 1 := D.length_middle
  obtain rfl : s'' = s - 1 - 1 := D.length_last
  simp [stackedStringMap, formAdjoint_fromRows, formAdjoint_stringMap_mul_stringMap, D.c_eq,
    formAdjoint_formAdjoint, fromCols_mul_fromRows]

/-- In the second argument `h` of `constTermAtStringMap`, a unipotent `n` in `Y'.unipotent` moves
into the map at which `constTerm` is taken: `Y.stringMap Y'` is multiplied on the left by the matrix
of `n⁻¹` in rational coordinates. -/
lemma constTermAtStringMap_unipotent_mul_right {Y' : Grading V' N X' (s - 1)}
    (α : (n : Type) → [Fintype n] → AutChar E) (f : 𝒮 (V.hom V')) {n : G E ε'}
    (hn : n ∈ Y'.unipotent) (g : G E ε) (h : G E ε') :
    Y.constTermAtStringMap Y' α f g (n * h) = Y.constTerm Y'.gradeOf
      (twistedPairWeil α (g, h) f) (V'.ratCoordMatrix n⁻¹ * Y.stringMap Y') := by
  simpa using Y.constTerm_mul (Y' := Y') Y'.gradeOf_stringReversal
    (.inr ⟨one_mem _, Y'.mem_unipotent.1 hn⟩) g h _

/-- For `n` in `Y.unipotent`, `Y.constTermAtStringMap Y' α f (n * g) h` is `Y.constTerm` for the
weights `Y'.gradeOf` of `twistedPairWeil α (g, h) f` at `Y.stringMap Y' * V.ratCoordMatrix n`: the
factor `n` moves into the point of the constant term, on the right. -/
lemma constTermAtStringMap_unipotent_mul_left {Y' : Grading V' N X' (s - 1)}
    (α : (n : Type) → [Fintype n] → AutChar E) (f : 𝒮 (V.hom V')) {n : G E ε}
    (hn : n ∈ Y.unipotent) (g : G E ε) (h : G E ε') :
    Y.constTermAtStringMap Y' α f (n * g) h = Y.constTerm Y'.gradeOf
      (twistedPairWeil α (g, h) f) (Y.stringMap Y' * V.ratCoordMatrix n) := by
  simpa using Y.constTerm_mul (Y' := Y') Y'.gradeOf_stringReversal
    (.inr ⟨hn, Y'.mem_unipotent.1 (one_mem _)⟩) g h _

/-- For odd `s` and `W` equivariant for `Y` (left translation by unipotents acts by a character),
the product of `W` and the constant term at `Y.stringMap Y'`, with the characters `rankTwist a`, is
invariant under the unipotent group of `Y`: the two characters cancel. -/
lemma mul_constTermAtStringMap_unipotent_mul {Y' : Grading V' N X' (s - 1)} (h_odd : Odd s)
    (a : AutChar E) (f : 𝒮 (V.hom V')) {W : Y.besselGroup → ℂ} (hW : Y.IsEquivariant W) {n : G E ε}
    (hn : n ∈ Y.unipotent) (g : Y.besselGroup) (r : G E ε') :
    W (⟨n, Y.unipotent_le_besselGroup hn⟩ * g) *
        Y.constTermAtStringMap Y' (rankTwist a) f (n * g.val) r =
      W g * Y.constTermAtStringMap Y' (rankTwist a) f g.val r := by
  have h_deg : HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix n - 1) :=
    Y.hasDegreeGe_two_of_odd h_odd hn
  simp [constTermAtStringMap, homBicharacter_eq, hW.unipotent_mul_constTerm
    Y'.gradeOf_stringReversal (u := ⟨n, Y.unipotent_le_besselGroup hn⟩) h_deg
    (Y.hasDegreeGe_neg_one_stringMap.mul h_deg (by omega))]

/-- Let `D` be data for the two consecutive lifts `Y → Y' → Y''`. Let `n` be a unipotent element of
U(V'), with matrix `V'.ratCoordMatrix n` in rational coordinates, and put `T = Y.stringMap Y'`,
`T' = Y'.stringMap Y''`. Join `f` and `f'` to the datum `arrowProduct f f'` on `Hom(V', V⁻ ⊕ V'')`;
by `hθ`, its theta value is `z ≠ 0` times the product of those of `f` and `f'`. Translate this datum
by the map `stackedStringMap Y Y' Y''` = (T*, T'). Then take the zero term along
`D.homZeroPart.splitting`, which is the mean over the maps of positive degree. Evaluate the result
at the map from `X'` to an isotropic half of the hyperbolic planes indexed by `q`. Its matrix is
`Y'.genericConst` times the block of `n - 1` whose rows are the basis vectors `D.gradeOne` of grade
one and whose columns are `X'`. Then `z⁻¹` times this value is the product of the constant terms of
`f` at `n⁻¹ T` and of `f'` at `T' n`. -/
lemma DoubleLiftData.zeroTerm_stackedStringMap_planes (D : DoubleLiftData X'' q Y Y' Y'') {z : ℂ}
    (hz : z ≠ 0)
    (hθ : ∀ (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')),
      θ (V'.hom (flipSum V V'')) (arrowProduct f f') = z * ((V.hom V').θ f * (V'.hom V'').θ f'))
    (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')) {n : G E ε'} (hn : n ∈ Y'.unipotent) :
    let planes : Splitting
        ((stdSpace E X').hom (hyperbolicSum q (flipSum (stdSpace E X) (stdSpace E X''))))
        ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) (q × X') :=
      (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget (stdSpace E X')
    z⁻¹ * D.homZeroPart.splitting.zeroTerm
        (homHeisenbergOp (stackedStringMap Y Y' Y'') (arrowProduct f f'))
        (planes.kAdelic *ᵥ fun p : q × X' ↦
          ↑Y'.genericConst * (V'.ratCoordMatrix n - 1) (D.gradeOne p.1)
            (Y'.indexEquiv (Sum.inl p.2))) =
      Y.constTerm Y'.gradeOf f (V'.ratCoordMatrix n⁻¹ * Y.stringMap Y') *
        Y'.constTerm Y''.gradeOf f' (Y'.stringMap Y'' * V'.ratCoordMatrix n) := by
  intro planes
  -- The zero term ignores translations along `kAdelic`; add the one that completes the
  -- translation vector to `stackedStringMap * (n - 1)`. The two translations compose without a
  -- phase.
  obtain ⟨y, hy⟩ := D.exists_add_eq_homAtPoint_stackedStringMap hn
  have h_beta (v : ((q ⊕ q) ⊕ X ⊕ X'') × X' → 𝔸 E) :
      (adelicHeisenberg E (homSigns ε' (-ε ⊕ᵥ ε''))).β
      (D.homZeroPart.splitting.kAdelic *ᵥ y) (D.homZeroPart.splitting.iAdelic *ᵥ v) = 1 := by
    simp [D.homZeroPart.splitting.beta_eq_coords]
  rw [← theta_rho, ← zeroTerm_rho_iAdelic, ← zeroTerm_rho_kAdelic y, (heisenbergRep _).mul, h_beta,
    one_smul, hy]
  -- Compose with the translation by `stackedStringMap`, which gives `stackedStringMap * n`. The
  -- phase is 1, because (T*, T')* (T*, T') = -T T* + T'* T' = 0.
  rw [(heisenbergRep _).mul, ← homBicharacter, homBicharacter_eq, ← Matrix.mul_assoc,
    formAdjoint_stackedStringMap_mul_stackedStringMap D]
  simp [D.constTerm_mul_constTerm_eq_inv_mul_zeroTerm hz hθ, stackedStringMap, Matrix.mul_sub,
    ← homHeisenbergOp_arrowProduct, formAdjoint_ratCoordMatrix_mul, GradeZeroPart.splitting]

/-- Let `Y, Y', Y''` be gradings of the hermitian spaces `V, V', V''` over `E` with definite parts
`X, X', X₀`, and let `D` be data for two consecutive lifts. There is a constant `z` with the
following property. Let `a`, `b` be automorphic characters of U(1), which normalise the two Weil
actions; let `f`, `f'` be data on `Hom(V, V')` and `Hom(V', V'')`, and `k` a point of U(X₀). Let `W`
be a continuous function on the Bessel (Fourier–Jacobi) subgroup of `Y`, invariant under rational
points and equivariant for the unipotent character (`Y.IsEquivariant W`). Let `F g r` be `W g` times
the constant terms of the Weil translates of `f` by `(g, r)` and of `f'` by `(r, Y''.inclX k)`. The
integral of `F` over the Bessel subgroups of `Y` and `Y'` is the integral over `g` in U(X) of
`W (Y.inclX g)` times `z` times a theta integral over `r` in U(X'), all modulo rational points. Its
datum is made from the join `arrowProduct f f'` on `Hom(V', V⁻ ⊕ V'')`: translate by
`stackedStringMap Y Y' Y''`, the map V' → V⁻ ⊕ V'' along the strings; cut down to
`Hom(X', X⁻ ⊕ X'')` by the mean over the isotropic part of `D.splitting` (`zeroTerm`); and act by
`(g, r, D.embX k)` under the joint Weil action `tripleWeil a b`. -/
lemma DoubleLiftData.exists_integral_constTermAtStringMap_mul_eq
    (D : DoubleLiftData X'' q Y Y' Y'') :
    ∃ z : ℂ, ∀ (a b : AutChar E) (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V''))
      (k : G E (1 : X₀ → ℤˣ)) (W : Y.besselGroup → ℂ), Y.IsEquivariant W →
      let F (g : Y.besselGroup) (r : Y'.besselGroup) :=
        W g * Y.constTermAtStringMap Y' (rankTwist a) f g r *
          Y'.constTermAtStringMap Y'' (rankTwist b) f' r (Y''.inclX k)
      ∫ r : Y'.besselGroup, ∫ g : Y.besselGroup, F g r ∂Y.besselMeasure ∂Y'.besselMeasure =
        ∫ g : G E (1 : X → ℤˣ), W ⟨Y.inclX g, Y.inclX_mem_besselGroup g⟩ *
          (z * ∫ r : G E (1 : X' → ℤˣ),
            θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
            (tripleWeil a b (g, r, D.embX k)
              (D.splitting.zeroTerm (homHeisenbergOp (stackedStringMap Y Y' Y'')
                (arrowProduct f f'))))
            ∂(stdSpace E X').quotMeasure) ∂(stdSpace E X).quotMeasure := by
  -- Apply `integral_besselMeasure_eq_of_mean` twice. Over the unipotent group of `Y` the character
  -- of the kernel cancels that of `W`. Over that of `Y'` the mean turns the zero term along
  -- `D.homZeroPart.splitting` into the zero term along `D.splitting`.
  obtain ⟨z, hz_ne, hθ⟩ := theta_arrowProduct V V' V''
  have h_odd : Odd s := D.odd_length
  obtain rfl : s' = s - 1 := D.length_middle
  obtain rfl : s'' = s - 1 - 1 := D.length_last
  -- `hκ`, `hκ'`: if `φ (n * x) = f x (row n)` for unipotent n and x in U(X) or U(X'), where the
  -- row is a block of `n - 1`, and `f x` has mean `M x`, then `∫ φ = κ * ∫ M` (under continuity and
  -- invariance hypotheses)
  obtain ⟨κ, hκ⟩ := Y.integral_besselMeasure_eq_of_mean (.refl _)
  obtain ⟨κ', hκ'⟩ := Y'.integral_besselMeasure_eq_of_mean D.gradeOne
  refine ⟨κ * κ' * z⁻¹, fun a b f f' k W hW ↦ ?_⟩
  intro F
  have h_cont : Continuous ↿F := by
    have := hW.continuous
    simp only [F, mul_assoc, D.constTerm_mul_constTerm_eq_inv_mul_zeroTerm hz_ne hθ]
    fun_prop
  have h_fix_left (r : Y'.besselGroup) :
      (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft (fun g ↦ F g r) := fun γ hγ g ↦ by
    simp [F, hW.rat_mul γ hγ.1, ← constTermAtStringMap_rat_mul ⟨γ.val, hγ⟩ 1 g.val]
  have h_fix_right (g : Y.besselGroup) :
      (Y'.ratBessel.subgroupOf Y'.besselGroup).FixesLeft (F g) := fun δ hδ r ↦ by
    simp [F, ← constTermAtStringMap_rat_mul 1 ⟨δ.val, hδ⟩ g.val r.val,
      ← constTermAtStringMap_rat_mul ⟨δ.val, hδ⟩ 1 r.val]
  let ι₀ := Y.inclX.codRestrict Y.besselGroup Y.inclX_mem_besselGroup
  have ι₀_cont : Continuous ι₀ := Y.continuous_inclX.subtype_mk _
  have h_fix_levi (r : Y'.besselGroup) :
      (stdSpace E X).Γ.FixesLeft fun x ↦ F (ι₀ x) r := fun γ hγ x ↦ by
    have h := h_fix_left r (ι₀ γ) (Y.inclX_mem_ratBessel hγ) (ι₀ x)
    rwa [← map_mul] at h
  -- for odd `s` the characters of `W` and of the kernel cancel on unipotent elements
  have h_unip (r : Y'.besselGroup) (n : G E ε) (hn : n ∈ Y.unipotent) (x : G E 1) :
      F (⟨n, Y.unipotent_le_besselGroup hn⟩ * ι₀ x) r = F (ι₀ x) r := by
    simp [F, mul_constTermAtStringMap_unipotent_mul h_odd a f hW hn (ι₀ x) r.val]
  have h_inner (r : Y'.besselGroup) :
      ∫ g, F g r ∂Y.besselMeasure = κ * ∫ x, F (ι₀ x) r ∂(stdSpace E X).quotMeasure :=
    hκ (f := fun x _ ↦ F (ι₀ x) r) (h_fix_left r) h_cont.along_fst (h_unip r)
      (by simp [IsContPeriodic, continuous_const]) (by fun_prop) (h_fix_levi r)
  have h_int : Integrable (Function.uncurry fun r x ↦ F (ι₀ x) r)
      (Y'.besselMeasure.prod (stdSpace E X).quotMeasure) :=
    integrable_of_isCocompact
      (isCocompact_prod Y'.isCocompact_ratBessel (stdSpace E X).isCocompact_Gamma)
      (by fun_prop) (by simp +contextual [h_fix_levi, h_fix_right, -map_mul, mem_prod])
  rw [funext h_inner, integral_const_mul, integral_integral_swap h_int]
  -- pull the constants `κ`, `κ'` and `z⁻¹` to where they arise
  simp_rw [mul_assoc, ← integral_const_mul z⁻¹, mul_left_comm (W _), ← integral_const_mul (W _),
    integral_const_mul κ]
  congr with x
  -- `hκ'` applies to the integral over the Bessel group of `Y'`
  -- `Φ g`: the zero term along `D.homZeroPart.splitting` of the joined datum, moved by (x, g, k)
  -- through `ω g` and `ω' g`, scaled and translated by `stackedStringMap`
  let ω g := twistedPairWeil (rankTwist a) (Y.inclX x, Y'.inclX g) (V := V) (V' := V')
  let ω' g := twistedPairWeil (rankTwist b) (Y'.inclX g, Y''.inclX k) (V := V') (V' := V'')
  let Φ g := D.homZeroPart.splitting.zeroTerm <| homHeisenbergOp (stackedStringMap Y Y' Y'') <|
    arrowProduct (ω g f) (ω' g (W (ι₀ x) • z⁻¹ • f'))
  let planes := (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget (stdSpace E X')
  refine hκ' (f := fun g y ↦ Φ g (planes.iAdelic *ᵥ 0 + planes.kAdelic *ᵥ y))
    (φ_inv := h_fix_right _) (φ_cont := h_cont.along_snd) (φ_eq := fun n hn g ↦ ?_)
    (f_mean := fun g ↦ ⟨isContPeriodic_along_k .., ?_⟩) (M_cont := ?_) (M_inv := fun γ hγ g ↦ ?_)
  · -- `F (ι₀ x) (n * Y'.inclX g)` is a value of `Φ g`. Both constant terms absorb n into their
    -- frequency.
    simpa [F, ι₀, Φ, planes, ω, ω', constTermAtStringMap_unipotent_mul_right (hn := hn),
      constTermAtStringMap_unipotent_mul_left (hn := hn), mul_assoc] using congrArg (W (ι₀ x) * ·)
        (D.zeroTerm_stackedStringMap_planes hz_ne hθ (ω g f) (ω' g f') hn).symm
  · -- the mean over the planes is the zero term along `D.splitting`, which intertwines the actions
    rw [← Splitting.zeroTerm_apply, ← D.zeroTerm_splitting_tripleWeil]
    -- split the triple action into the two pair actions, which commute with `stackedStringMap`
    simp_rw [stackedStringMap, homHeisenbergOp_arrowProduct, ← arrowProduct_twistedPairWeil,
      pairWeil_homHeisenbergOp, inclX_mul_stringMap_mul_inclX_inv, ← homHeisenbergOp_arrowProduct,
      ← smul_eq_mul, ← map_smul, splitting, zeroTerm_comp]
    rfl
  · -- the mean is continuous in the point of U(X')
    exact continuous_const.mul (continuous_const.mul
      ((continuous_theta_tripleWeil a b _).comp
        (continuous_const.prodMk (continuous_id.prodMk continuous_const))))
  · -- and invariant under its rational points
    congr 2
    simpa only [one_mul] using theta_tripleWeil_rat_mul a b _ (γ := 1) (one_mem _) hγ x g _

end New.Seesaw

/-! ## The functions produced by the unfolding -/

namespace New.Data

open scoped Pointwise

open MeasureTheory Function UniqueFactorizationMonoid Multiset IsDedekindDomain.HeightOneSpectrum
  Seesaw Space Grading stdLattice Rows Prod Modulus ProbabilityTheory TensorChain
variable {P : Parameters} {D : Data P}

section Stages

variable (ϑ : D.TameChar) (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
  (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))

/-- The embedding `inclXFin` of the finite points of `U(X_k)` in those of `U(Y_k)` maps the level
`D.levelX k` into the level `D.chosenLevel`. -/
lemma inclXFin_mem_chosenLevel {k : ℕ} {hk : k ≤ 2 * D.ϱ + 1} {a : Gf D.E (D.X k)}
    (ha : a ∈ D.levelX k) : (D.gradingY k hk).inclXFin a ∈ D.chosenLevel := by
  -- The chosen places and their conjugates do not lie above `N`.
  have not_chosen {w : FinPlace D.E} (hw : w ∈ D.piNPlaces) :
      ¬D.IsChosen w ∧ ¬D.IsChosen (star w) :=
    D.not_isChosen_of_N_mem (D.isSplitLevel_piNPlaces.natCast_level_mem w hw)
  have is_chosen (i : Σ i : Fin 2, D.ChosenPlace i) : D.IsChosen (D.chosenPlace i) := by
    obtain ⟨-, -, h_chosen, -⟩ := i
    exact h_chosen
  exact inclXFin_mem_levelOf _ (D.spansLattice_gradingY k hk) D.isSplitSquarefree_piNIdele ha.2
    (fun i hi ↦ (not_chosen hi).1 (is_chosen i))
    (fun i hi ↦ (not_chosen hi).2 (by simpa using is_chosen i)) ha.1

/-- The datum of lift `k + 1` (`New.Data.datumY`) moved by the outer variable `g_k = (ξ k, y k)`,
which acts on `Y_k`. -/
noncomputable def movedDatum (k : ℕ) : 𝒮 ((D.spaceY k).hom (D.spaceY (k + 1))) :=
  twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) ((ξ k, y k), 1) (datumY ϑ k)

/-- The action of `(g, h)` on the moved datum of lift `k + 1` is that of `(g * g_k, h)` on the
original datum, where `g_k = (ξ k, y k)`. -/
lemma twistedPairWeil_movedDatum (k : ℕ) (g : New.G D.E (D.signsY k))
    (h : New.G D.E (D.signsY (k + 1))) :
    twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) (g, h) (movedDatum ϑ ξ y k) =
      twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) (g * (ξ k, y k), h) (datumY ϑ k) := by
  rw [movedDatum, rep_apply_apply, mk_mul_mk, mul_one]

/-- In the constant term `constTermAtStringMap` of the moved datum at `(g, g' * a)`, the point `a`
may be moved into the datum: it is the constant term at `(g, g')` of `datumY` acted on by
`(g_k, a)`, where `g_k = (ξ k, y k)`. -/
lemma constTermAtStringMap_movedDatum {k : ℕ} {hk : k ≤ 2 * D.ϱ + 1} {X : Type} {s : ℕ}
    [DecidableEq X] (Y' : Grading (D.spaceY (k + 1)) D.N X s) (g : New.G D.E (D.signsY k))
    (g' a : New.G D.E (D.signsY (k + 1))) :
    (D.gradingY k hk).constTermAtStringMap Y' (rankTwist (D.chainChar ϑ (k + 1)))
        (movedDatum ϑ ξ y k) g (g' * a) =
      (D.gradingY k hk).constTermAtStringMap Y' (rankTwist (D.chainChar ϑ (k + 1)))
        (twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) ((ξ k, y k), a) (datumY ϑ k))
        g g' := by
  simp only [constTermAtStringMap, twistedPairWeil_movedDatum, rep_apply_apply, mk_mul_mk]

/-- The function on `R_k` that enters step `k + 1` of the unfolding: `𝒲_φ` for `k = 0`, and
`γ ↦ 𝒲_k (γ g_k)` with `g_k = (ξ k, y k)` for `k > 0`. -/
noncomputable def unfoldStageOn :
    ∀ (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1), (D.gradingY k hk).besselGroup → ℂ
  | 0, _ => (D.gradingY 0).sourceFn t φ.val
  | k + 1, hk => fun γ ↦
    (D.gradingY k).unfoldStep (D.gradingY (k + 1) hk) (rankTwist (D.chainChar ϑ (k + 1)))
      (movedDatum ϑ ξ y k) (unfoldStageOn k (by omega)) (γ.val * (ξ (k + 1), y (k + 1)))

/-- The function `𝒲_{k+1}` on `U(Y_{k+1})` that the first `k + 1` unfolding steps leave. -/
noncomputable def unfoldStage (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} {s : ℕ}
    [DecidableEq X] (Y' : Grading (D.spaceY (k + 1)) D.N X s) : New.G D.E (D.signsY (k + 1)) → ℂ :=
  (D.gradingY k hk).unfoldStep Y' (rankTwist (D.chainChar ϑ (k + 1))) (movedDatum ϑ ξ y k)
    (unfoldStageOn ϑ t φ ξ y k hk)

/-- On `R_{k+1}`, the Bessel group of `D.gradingY (k + 1) hk`, the function `unfoldStageOn` of the
unfolding is `γ ↦ 𝒲_{k+1} (γ g_{k+1})`, where `𝒲_{k+1}` is `unfoldStage` at `k` and
`g_{k+1} = (ξ (k + 1), y (k + 1))`. -/
lemma unfoldStageOn_succ (k : ℕ) (hk : k + 1 ≤ 2 * D.ϱ + 1)
    (γ : (D.gradingY (k + 1) hk).besselGroup) :
    unfoldStageOn ϑ t φ ξ y (k + 1) hk γ =
      unfoldStage ϑ t φ ξ y k (by omega) (D.gradingY (k + 1) hk) (γ.val * (ξ (k + 1), y (k + 1))) :=
  rfl

/-- For `k < l`, the function `unfoldStageOn` on `R_k` does not change when the points `ξ l` and
`y l` of stage `l` are replaced by any `a` and `b`. -/
lemma unfoldStageOn_update {l : ℕ} (a : GInf D.E (D.signsY l)) (b : Gf D.E (D.Y l)) (k : ℕ)
    (hk : k ≤ 2 * D.ϱ + 1) (hkl : k < l) :
    unfoldStageOn ϑ t φ (update ξ l a) (update y l b) k hk = unfoldStageOn ϑ t φ ξ y k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldStageOn, movedDatum, ih _ (by omega), update_of_ne hkl.ne,
      update_of_ne (by omega : k ≠ l)]

/-- The function `𝒲_{k+1}` (`unfoldStage`) depends only on the outer variables `g_j = (ξ j, y j)`
for `j ≤ k`: changing `ξ` and `y` at an index `l > k` does not change it. -/
lemma unfoldStage_update {l : ℕ} (a : GInf D.E (D.signsY l)) (b : Gf D.E (D.Y l)) (k : ℕ)
    (hk : k ≤ 2 * D.ϱ + 1) (hkl : k < l) {X : Type} {s : ℕ} [DecidableEq X]
    (Y' : Grading (D.spaceY (k + 1)) D.N X s) :
    unfoldStage ϑ t φ (update ξ l a) (update y l b) k hk Y' = unfoldStage ϑ t φ ξ y k hk Y' := by
  simp only [unfoldStage, movedDatum, unfoldStageOn_update ϑ t φ ξ y a b k hk hkl,
    update_of_ne hkl.ne]

/-- The function `unfoldStageOn` on the Bessel group `R_k` of `D.gradingY k hk` is equivariant under
the unipotent character and invariant under the rational points (`New.Grading.IsEquivariant`). -/
lemma isEquivariant_unfoldStageOn (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) :
    (D.gradingY k hk).IsEquivariant (unfoldStageOn ϑ t φ ξ y k hk) := by
  induction k with
  | zero => exact (D.gradingY 0).isEquivariant_sourceFn (by simp) t φ.val
  | succ k ih => exact isEquivariant_unfoldStep (ih (by omega)) rfl (ξ (k + 1), y (k + 1))

section

variable (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} [Fintype X] [DecidableEq X]
  (Y' : Grading (D.spaceY (k + 1)) D.N X (2 * D.ϱ + 1 - (k + 1)))

lemma continuous_unfoldStage : Continuous (unfoldStage ϑ t φ ξ y k hk Y') :=
  continuous_unfoldStep (isEquivariant_unfoldStageOn ϑ t φ ξ y k hk)

/-- The function `𝒲_{k+1}` is invariant on the left under the rational points of `R_{k+1}`, the
Bessel group of `Y'`. -/
lemma fixesLeft_ratBessel_unfoldStage : Y'.ratBessel.FixesLeft (unfoldStage ϑ t φ ξ y k hk Y') :=
  unfoldStep_rat_mul

end

/-- Fix a tame character `ϑ`, a source form `φ` on U(X_0) with a linear form `t` on its values, and
adelic points `g_k = (ξ k, y k)` of the unitary groups U(Y_k). Let `Y'` be a grading of `Y_{k+1}`
with a string of length `2 ϱ + 1 - (k + 1)`, and let `𝒲_{k+1}` be the function `unfoldStage` on
U(Y_{k+1}) that `k + 1` unfolding steps leave, the last one with `Y'`. Let `z` be automorphic and
rapidly decreasing on U(Y_{k+1}). Take the theta lift of `z` to U(Y_k) with the datum `datumY ϑ k`
on `Hom(Y_k, Y_{k+1})` and the Weil action `twistedPairWeil` normalised by the character
`D.chainChar ϑ (k + 1)`, and translate the lift on the right by `g_k`. Its integral against the
function `unfoldStageOn` of the previous stage, over the Bessel group `R_k` of `D.gradingY k` modulo
rational points, is the integral of `𝒲_{k+1} z` over U(Y_{k+1}) modulo the rational points
`Y'.ratBessel` of the Bessel group of `Y'`. The latter integral converges absolutely. -/
lemma integral_unfoldStageOn (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} [Fintype X] [DecidableEq X]
    (Y' : Grading (D.spaceY (k + 1)) D.N X (2 * D.ϱ + 1 - (k + 1)))
    {z : New.G D.E (D.signsY (k + 1)) → ℂ}
    (hz_aut : (D.spaceY (k + 1)).IsAutomorphic z) (hz_rapid : (D.spaceY (k + 1)).IsRapid z) :
    Integrable (unfoldStage ϑ t φ ξ y k hk Y' * z) Y'.ratBessel.quotMeasure ∧
      ∫ r : (D.gradingY k hk).besselGroup, unfoldStageOn ϑ t φ ξ y k hk r *
        ∫ h : New.G D.E (D.signsY (k + 1)), θ ((D.spaceY k).hom (D.spaceY (k + 1)))
          (twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) (r.1 * (ξ k, y k), h) (datumY ϑ k)) *
            z h ∂(D.spaceY (k + 1)).quotMeasure ∂(D.gradingY k hk).besselMeasure =
      Y'.ratBessel.quotMeasure[unfoldStage ϑ t φ ξ y k hk Y' * z] := by
  simpa only [unfoldStage, twistedPairWeil_movedDatum, Pi.mul_def]
    using integral_besselGroup_unfold Y' (rankTwist (D.chainChar ϑ (k + 1))) (movedDatum ϑ ξ y k)
      (isEquivariant_unfoldStageOn ϑ t φ ξ y k hk) hz_aut hz_rapid

/-- Decidable equality on the sum of `q × X_{2i+1}` and the type of pairs `(a, b)` of an index `a`
of `Y_{2i} ⊕ Y_{2i+2}` and an index `b` of `Y_{2i+1}` whose grades have positive difference, built
from the instances for sums, products and subtypes. -/
noncomputable local instance instDecidableEqDoubleLiftSplitting (i : ℕ) (hi : 2 * i < 2 * D.ϱ + 1)
    {X q : Type} {s : ℕ} [Fintype X] [DecidableEq X] [Fintype q] [DecidableEq q]
    {Y : Grading (D.spaceY (2 * i + 2)) D.N X s} :
    DecidableEq ({ i_1 : (D.Y (2 * i) ⊕ D.Y (2 * i + 2)) × D.Y (2 * i + 1) //
        0 < Sum.elim (D.gradingY (2 * i) hi.le).gradeOf Y.gradeOf i_1.1 -
          (D.gradingY (2 * i + 1) hi).gradeOf i_1.2 } ⊕ q × D.X (2 * i + 1)) :=
  @instDecidableEqSum _ _ Subtype.instDecidableEq instDecidableEqProd

/-- Let `R` be data for the two lifts `Y_{2i} → Y_{2i+1} → Y_{2i+2}`, the last space with the
grading `Y`. Suppose that the linear map `D.doubleLiftEvalY i` on finite data is `R.finEval`, the
finite analogue of the translation and zero term below. Fix archimedean points `ξ k` of U(Y_k) and
`x` of U(Y_{2i+2}). Move the data `datumY` of lifts `2 i + 1` and `2 i + 2` under the Weil action by
`(ξ k, y k)` for `k = 2 i, 2 i + 1` and by `(x, y (2 i + 2))`. Join them (`arrowProduct`), translate
by the map `stackedStringMap` along the strings, and cut down to
`Hom(X_{2i+1}, X_{2i}⁻ ⊕ X_{2i+2})` by the mean over the isotropic part of `R.splitting`
(`zeroTerm`). The result is a pure tensor (`integrated`) of a vector `v` of the Fock space,
independent of the tame character `ϑ` and the finite points `y`, and of `evaluatedDatum ϑ y i`, the
value of `D.doubleLiftEvalY i` on the finite factors, carried to this space by `arrowTensor`. -/
lemma exists_zeroTerm_eq_integrated (ξ : ∀ k : ℕ, GInf D.E (D.signsY k))
    (i : ℕ) (hi : 2 * i < 2 * D.ϱ + 1) {X q : Type} {s : ℕ}
    [Fintype X] [DecidableEq X] [Fintype q] [DecidableEq q]
    {Y : Grading (D.spaceY (2 * i + 2)) D.N X s}
    (R : DoubleLiftData (D.X (2 * i + 2)) q (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi)
      Y)
    (hR : D.doubleLiftEvalY i = R.finEval) (x : GInf D.E (D.signsY (2 * i + 2))) :
    ∃ v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns D.E
      (homSigns (1 : D.X (2 * i + 1) → ℤˣ)
        (Sum.elim (-(1 : D.X (2 * i) → ℤˣ)) (1 : D.X (2 * i + 2) → ℤˣ))))),
      ∀ (ϑ : D.TameChar) (y : ∀ k : ℕ, Gf D.E (D.Y k)),
      R.splitting.zeroTerm (homHeisenbergOp
        (stackedStringMap (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi) Y)
        (arrowProduct
          (twistedPairWeil (rankTwist (D.chainChar ϑ (2 * i + 1)))
            ((ξ (2 * i), y (2 * i)), ξ (2 * i + 1), y (2 * i + 1)) (datumY ϑ (2 * i)))
          (twistedPairWeil (rankTwist (D.chainChar ϑ (2 * i + 1 + 1)))
            ((ξ (2 * i + 1), y (2 * i + 1)), x, y (2 * i + 2)) (datumY ϑ (2 * i + 1))))) =
        integrated ((stdSpace D.E (D.X (2 * i + 1))).hom
            (flipSum (stdSpace D.E (D.X (2 * i))) (stdSpace D.E (D.X (2 * i + 2))))) v
          (arrowTensor (evaluatedDatum ϑ y i)) := by
  -- Each operation acts separately on the real and on the finite factor. On the real factor the
  -- characters act through their weights, which do not depend on `ϑ`.
  -- The zero term of a translated pure tensor has real factor `u w v`.
  choose u ev_eq using exists_zeroTerm_rho_integrated_eq R.splitting
  simp only [evaluatedDatum, hR, R.arrowTensor_finEval]
  simp +instances only [pairWeil_integrated_all, arrowProduct, ContinuousLinearMap.comp_apply,
    CoordChange.map_integrated, boxProd_integrated, ev_eq]
  -- Both sides are now pure tensors with one finite factor; `v` is the real factor on the left.
  exact ⟨_, fun _ _ ↦ rfl⟩

-- Without this, comparing the index types of neighbouring stages unfolds `Finset.univ`.
seal Finset.univ in
/-- A double unfolding step. Let `R` be data for the two lifts `Y_{2i} → Y_{2i+1} → Y_{2i+2}`, the
last space with a grading `Y` of definite part `X`. Suppose that `D.doubleLiftEvalY i`, the linear
map that turns finite data for the spaces `Y_k` into finite data for their definite parts `X_k`, is
the map `R.finEval` of `R`. Fix archimedean points `ξ k` of U(Y_k) and `x` of U(Y_{2i+2}), and a
linear form `l` on the values of algebraic forms on U(X_{2i}). There is a linear form `l''`,
independent of `ϑ`, `t`, `φ`, `y` and `ψ`, with the following property. Suppose the function
`unfoldStageOn` on the Bessel group of the grading of `Y_{2i}` is `sourceFn l ψ`. This is the
function that is equivariant for the unipotent character and equals the coefficient
`algFormCoeff 1 l ψ` of the form `ψ` on U(X_{2i}). Then for `g` in U(X), the value of `𝒲_{2i+2}` at
`Y.inclX g * (x, y (2 i + 2))` is the coefficient at `l''` of `Θ ψ`, taken at the image `R.embX g`
of `g` in U(X_{2i+2}). Here `Θ` is the composite (`liftInPairs`) of the theta lifts
`X_{2i} → X_{2i+1} → X_{2i+2}`, with kernels `D.liftKernel ϑ` and datum `evaluatedDatum ϑ y i`. -/
lemma exists_unfoldStage_eq_algFormCoeff_of_sourceFn (ξ : ∀ k : ℕ, GInf D.E (D.signsY k))
    (i : ℕ) (hi : 2 * i < 2 * D.ϱ + 1)
    {X q : Type} {s : ℕ} [Fintype X] [DecidableEq X] [Fintype q] [DecidableEq q]
    {Y : Grading (D.spaceY (2 * i + 2)) D.N X s}
    (R : DoubleLiftData (D.X (2 * i + 2)) q (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi)
      Y)
    (hR : D.doubleLiftEvalY i = R.finEval) (x : GInf D.E (D.signsY (2 * i + 2)))
    (l : (WeylIndex (D.X (2 * i)) D.columnCount → ℂ) →ₗ[ℂ] ℂ) :
    ∃ l'' : (WeylIndex (D.X (2 * i + 2)) D.columnCount → ℂ) →ₗ[ℂ] ℂ,
      ∀ (ϑ : D.TameChar) (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
        (y : ∀ k : ℕ, Gf D.E (D.Y k))
        (ψ : AlgForm (E := D.E) (D.X (2 * i)) D.columnCount (D.lastEntry (2 * i))),
      unfoldStageOn ϑ t φ ξ y (2 * i) hi.le = (D.gradingY (2 * i) hi.le).sourceFn l ψ →
      ∀ g : New.G D.E (1 : X → ℤˣ),
        unfoldStage ϑ t φ ξ y (2 * i + 1) hi Y (Y.inclX g * (x, y (2 * i + 2))) =
        algFormCoeff 1 l'' (liftInPairs (fun j : ℕ ↦ (D.liftKernel ϑ j).lift) i
          (evaluatedDatum ϑ y i) ψ) (R.embX g) := by
  -- The integrals over the two unipotent groups leave `z` times a double theta integral over
  -- U(X_{2i}) × U(X_{2i+1}) (`h_mean`). Its datum is a real vector `v` times the evaluated finite
  -- datum (`hv`), and such an integral against the coefficient `l` is a coefficient `l''` of the
  -- double lift (`hl''`).
  choose z h_mean using R.exists_integral_constTermAtStringMap_mul_eq
  choose v hv using exists_zeroTerm_eq_integrated ξ i hi R hR x
  have lift (j : ℕ) : IsThetaLift D.columnCount (D.lastEntry j) (D.lastEntry (j + 1))
      (fun ϑ : D.TameChar ↦ rankTwist (D.chainChar ϑ (j + 1)))
      fun ϑ : D.TameChar ↦ (D.liftKernel ϑ j).lift :=
    isThetaLift_thetaKernel
      (mul_ne_zero (star_ne_zero.mpr fun h0 ↦ D.piMBar_ne_zero (Subtype.ext (Subtype.ext h0)))
        Parameters.jetScale_ne_zero)
  choose l'' hl'' using
    integral_theta_tripleWeil_eq_lift_comp (lift (2 * i)) (lift (2 * i + 1)) (z • v) l
  refine ⟨l'', fun ϑ t φ y ψ hψ g ↦ ?_⟩
  refine .trans ?_ (hl'' ϑ (evaluatedDatum ϑ y i) ψ (R.embX g))
  -- Write the two steps as an iterated integral of a product of two constant terms and apply
  -- `h_mean`.
  simp only [unfoldStage, unfoldStageOn_succ, unfoldStep, constTermAtStringMap_movedDatum,
    ← integral_mul_const]
  refine (h_mean _ _ _ _ _ _ (isEquivariant_unfoldStageOn ϑ t φ ξ y (2 * i) hi.le)).trans ?_
  simp only [hψ, hv, sourceFn_inclX, map_smul, _root_.smul_apply, smul_eq_mul, integral_const_mul]

-- Without this, comparing the index types of neighbouring stages unfolds `Finset.univ`.
seal Finset.univ in
/-- At an even stage `2 i` there is a linear form `l`, independent of the tame character `ϑ`, the
source form `φ` and the finite points `y`, such that the function `unfoldStageOn` that `2 i`
unfolding steps leave on the Bessel group `R_{2i}` is `sourceFn l (Θ φ)`: it is equivariant for the
unipotent character and equals the coefficient of `Θ φ` at `l` on U(X_{2i}). Here `Θ` is the
composite `doubleLiftChain` of the first `i` pairs of theta lifts between the definite spaces `X_k`,
with kernels `D.liftKernel ϑ` and finite data `evaluatedDatum ϑ y`. -/
lemma exists_unfoldStageOn_even_eq_sourceFn (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (i : ℕ) (hi : 2 * i ≤ 2 * D.ϱ + 1) :
    ∃ l : (WeylIndex (D.X (2 * i)) D.columnCount → ℂ) →ₗ[ℂ] ℂ,
      ∀ (ϑ : D.TameChar) (φ : D.SourceForm) (y : ∀ k : ℕ, Gf D.E (D.Y k)),
        unfoldStageOn ϑ t φ ξ y (2 * i) hi =
          (D.gradingY (2 * i) hi).sourceFn l
            (doubleLiftChain (D.liftKernel ϑ) (evaluatedDatum ϑ y) i φ) := by
  induction i with
  | zero => exact ⟨t, fun _ _ _ ↦ rfl⟩
  | succ i ih =>
    choose l hl using ih (by omega)
    choose l'' hl'' using exists_unfoldStage_eq_algFormCoeff_of_sourceFn ξ i
      (show 2 * i < 2 * D.ϱ + 1 by omega) _ (dite_eq_left (by omega)) (ξ (2 * i + 2)) l
    -- The function is equivariant for the unipotent character (`IsEquivariant`), so it is
    -- determined by its values on the image of U(X_{2i+2}) under `inclX`.
    exact ⟨l'', fun ϑ φ y ↦ (isEquivariant_unfoldStageOn ϑ t φ ξ y _ hi).eq_sourceFn
      ⟨D.ϱ - (i + 1), by omega⟩ (hl'' ϑ t φ y _ (hl ϑ φ y))⟩

-- Without this, comparing the index types of neighbouring stages unfolds `Finset.univ`.
seal Finset.univ in
/-- Let `R` be data for the two lifts `Y_{2i} → Y_{2i+1} → Y_{2i+2}`, the last space with a grading
`Y` of definite part `X`. Suppose that `D.doubleLiftEvalY i`, the linear map that turns finite data
for the spaces `Y_k` into finite data for their definite parts `X_k`, is the map `R.finEval` of `R`.
Fix a linear form `t` on the values of source forms and archimedean points `ξ k` of U(Y_k) and `x`
of U(Y_{2i+2}). There is a linear form `l`, independent of `ϑ`, `φ` and `y`, such that for `g` in
U(X) the value of `𝒲_{2i+2}` (`unfoldStage`) at `Y.inclX g * (x, y (2 i + 2))` is the coefficient
`algFormCoeff 1 l (Θ φ)` of `Θ φ` at `l`, taken at `R.embX g`. Here `Y.inclX` and `R.embX` map U(X)
to U(Y_{2i+2}) and to U(X_{2i+2}), and `Θ` is the composite `doubleLiftChain` of the first `i + 1`
pairs of theta lifts between the spaces `X_k`, with kernels `D.liftKernel ϑ` and finite data
`evaluatedDatum ϑ y`. -/
lemma exists_unfoldStage_eq_algFormCoeff (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (i : ℕ) (hi : 2 * i < 2 * D.ϱ + 1) {X q : Type} {s : ℕ}
    [Fintype X] [DecidableEq X] [Fintype q] [DecidableEq q]
    {Y : Grading (D.spaceY (2 * i + 2)) D.N X s}
    (R : DoubleLiftData (D.X (2 * i + 2)) q (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi)
      Y)
    (hR : D.doubleLiftEvalY i = R.finEval) (x : GInf D.E (D.signsY (2 * i + 2))) :
    ∃ l : (WeylIndex (D.X (2 * i + 2)) D.columnCount → ℂ) →ₗ[ℂ] ℂ,
      ∀ (ϑ : D.TameChar) (φ : D.SourceForm) (y : ∀ k : ℕ, Gf D.E (D.Y k))
        (g : New.G D.E (1 : X → ℤˣ)),
      unfoldStage ϑ t φ ξ y (2 * i + 1) hi Y (Y.inclX g * (x, y (2 * i + 2))) =
        algFormCoeff 1 l (doubleLiftChain (D.liftKernel ϑ) (evaluatedDatum ϑ y) (i + 1) φ)
          (R.embX g) := by
  choose l hl using exists_unfoldStageOn_even_eq_sourceFn t ξ i hi.le
  choose l'' hl'' using exists_unfoldStage_eq_algFormCoeff_of_sourceFn ξ i hi R hR x l
  exact ⟨l'', fun ϑ φ y ↦ hl'' ϑ t φ y _ (hl ϑ φ y)⟩

/-- Elements of the levels at `Y_k` and `Y_{k+1}` fix the datum `pointDatumY ϑ k` of lift `k + 1` of
the lower chain. -/
lemma liftWeilFin_pointDatumY (k : ℕ) {u : Gf D.E (D.Y k)} {u' : Gf D.E (D.Y (k + 1))}
    (hu : u ∈ levelY ϑ k) (hu' : u' ∈ levelY ϑ (k + 1)) :
    liftWeilFin (D.chainChar ϑ (k + 1)) (u, u') (pointDatumY ϑ k) = pointDatumY ϑ k := by
  -- `u` and `u'` reduce to 1 at every place of the level, so the factor in the action is 1.
  obtain ⟨hu_int, hu_red⟩ := mem_levelOf.1 hu
  obtain ⟨hu'_int, hu'_red⟩ := mem_levelOf.1 hu'
  ext1
  simpa using! thetaKernelY_omega_pointDatumY_eq_smul ϑ k hu_red hu'_red fun _ ↦
    (Matrix.mul_one _).symm

/-- The map `D.doubleLiftEvalY i` sends the join `arrowProduct Φ Φ'` of finite data `Φ`, `Φ'` on
`Hom(Y_{2i}, Y_{2i+1})` and `Hom(Y_{2i+1}, Y_{2i+2})` to a tensor of finite data on
`Hom(X_{2i}, X_{2i+1})` and `Hom(X_{2i+1}, X_{2i+2})`. If `2 i + 2 ≤ 2 ϱ + 1`, so that `Y_{2i+2}` is
graded by `D.gradingY`, it is equivariant for the finite points `u` of U(X_{2i+2}): acting on `Φ'`
by the image of `u` in U(Y_{2i+2}) before the map is acting by `u` on the second factor after it. -/
lemma doubleLiftEvalY_inclXFin (i : ℕ) (hi : 2 * i + 1 + 1 ≤ 2 * D.ϱ + 1) (b : AutChar D.E)
    (u : Gf D.E (D.X (2 * i + 1 + 1)))
    (Φ : ((D.spaceY (2 * i)).hom (D.spaceY (2 * i + 1))).finitePart)
    (Φ' : ((D.spaceY (2 * i + 1)).hom (D.spaceY (2 * i + 1 + 1))).finitePart) :
    D.doubleLiftEvalY i
        (arrowProduct Φ.1 (liftWeilFin b (1, (D.gradingY (2 * i + 1 + 1) hi).inclXFin u) Φ').1) =
      TensorProduct.map .id (liftWeilFin b (1, u))
        (D.doubleLiftEvalY i (arrowProduct Φ.val Φ'.val)) := by
  -- Before the last pair, `doubleLiftEvalY i` is by definition the evaluation of a double lift
  -- datum `R`.
  obtain ⟨q, _, _, R, hR, h_emb⟩ : ∃ (q : Type) (_ : Fintype q) (_ : DecidableEq q)
      (R : DoubleLiftData (D.X (2 * i + 1 + 1)) q
        (D.gradingY (2 * i)) (D.gradingY (2 * i + 1)) (D.gradingY _ hi)),
      D.doubleLiftEvalY i = R.finEval ∧ R.embX (1, u) = (1, u) :=
    ⟨_, _, _, _, dite_eq_left (by omega), rfl⟩
  -- `using!`: the two index types `2 * i + 1 + 1` and `2 * i + 2` agree only after unfolding.
  simpa only [hR, MonoidHom.map_one, Prod.mk_one_one, one_apply_eq_self] using!
    R.finEval_arrowProduct_equivariant 1 b (g := 1) (g' := 1) h_emb Φ Φ'

/-- If `z`, conjugated by `y (j + 1)`, lies in the level `levelY ϑ (j + 1)`, then `(1, z)` fixes the
translated datum `translatedPointDatumY ϑ y j` of lift `j + 1` under the finite Weil representation
`liftWeilFin` with the character `D.chainChar ϑ (j + 1)`. -/
lemma liftWeilFin_translatedPointDatumY (j : ℕ) {z : Gf D.E (D.Y (j + 1))}
    (hz : (y (j + 1))⁻¹ * (z * y (j + 1)) ∈ levelY ϑ (j + 1)) :
    liftWeilFin (D.chainChar ϑ (j + 1)) (1, z) (translatedPointDatumY ϑ y j) =
      translatedPointDatumY ϑ y j := by
  have h_conj : (1, z) * (y j, y (j + 1)) =
      (y j, y (j + 1)) * (1, (y (j + 1))⁻¹ * (z * y (j + 1))) := by simp
  rw [translatedPointDatumY, ← mul_apply_eq_comp, ← map_mul, h_conj, map_mul,
    mul_apply_eq_comp,
    liftWeilFin_pointDatumY ϑ _ (one_mem _) hz]

/-- Let `ϑ` be a tame character and `y k` finite points of U(Y_k). The tensor
`evaluatedDatum ϑ y i` is the finite datum of the two theta lifts `X_{2i} → X_{2i+1} → X_{2i+2}`.
Let `u` be a finite point of U(X_{2i+2}) whose image in U(Y_{2i+2}), conjugated by `y (2 * i + 2)`,
lies in `levelY ϑ`: it is integral and reduces to `1` at the chosen places and at those of `ϑ.Q`.
Then `(1, u)`, acting on the second tensor factor through the Weil action `ω` of the theta kernel
`D.liftKernel ϑ (2 * i + 1)`, fixes `evaluatedDatum ϑ y i`. -/
lemma map_evaluatedDatum_of_conj_mem (ϑ : D.TameChar) (y : ∀ k : ℕ, Gf D.E (D.Y k)) (i : ℕ)
    (hi : 2 * i + 1 + 1 ≤ 2 * D.ϱ + 1) {u : Gf D.E (D.X (2 * i + 1 + 1))}
    (hu : (y (2 * i + 1 + 1))⁻¹ * ((D.gradingY (2 * i + 1 + 1) hi).inclXFin u * y (2 * i + 1 + 1)) ∈
      levelY ϑ (2 * i + 1 + 1)) :
    TensorProduct.map .id ((D.liftKernel ϑ (2 * i + 1)).ω (1, u)) (evaluatedDatum ϑ y i) =
      evaluatedDatum ϑ y i := by
  -- The evaluation carries `ω(1, z)` on the data for the `Y_k` to `ω(1, u)`, where `z` is the image
  -- of `u`; the former fixes the translated datum, as the level fixes `pointDatumY`.
  let Φ (j : ℕ) : ((D.spaceY j).hom (D.spaceY (j + 1))).finitePart := translatedPointDatumY ϑ y j
  have fix_lower :
      liftWeilFin (D.chainChar ϑ (2 * i + 1 + 1)) (1, (D.gradingY _ hi).inclXFin u)
        (Φ (2 * i + 1)) = Φ (2 * i + 1) :=
    liftWeilFin_translatedPointDatumY ϑ y (2 * i + 1) hu
  have equivariant := doubleLiftEvalY_inclXFin i hi (D.chainChar ϑ (2 * i + 1 + 1)) u
    (Φ (2 * i)) (Φ (2 * i + 1))
  rw [fix_lower] at equivariant
  exact equivariant.symm

/-- The evaluated data do not change if each `y k` is replaced by the chosen representative of its
class modulo the level `levelY ϑ k`. -/
lemma evaluatedDatum_out :
    evaluatedDatum ϑ (fun k : ℕ ↦ (y k : Gf D.E (D.Y k) ⧸ levelY ϑ k).out) =
      evaluatedDatum ϑ y := by
  -- Each representative is `y k * u k` with `u k ∈ levelY ϑ k`, and such elements fix the data.
  choose u out_eq using fun k : ℕ ↦ QuotientGroup.mk_out_eq_mul (levelY ϑ k) (y k)
  simp [funext_iff, evaluatedDatum, translatedPointDatumY, out_eq, ← mk_mul_mk,
    liftWeilFin_pointDatumY ϑ _ (u _).property (u _).property]

/-- An idele that generates the ideal `Q`: the generator of `π_M Q` divided by that of `π_M`. -/
noncomputable def twistIdele : (𝔸f D.E)ˣ := (D.twistModulus ϑ 1).generator / D.chosenIdele

open scoped Classical in
/-- At the places of `ϑ.Q` the idele `twistIdele ϑ` has the valuation of a uniformiser, and at all
other places it is a unit. -/
lemma valued_twistIdele (w : FinPlace D.E) :
    Valued.v ((twistIdele ϑ).val w) = if w ∈ ϑ.Q then WithZero.exp (-1) else 1 := by
  -- The modulus is `D.piM` times the product of the distinct primes of `ϑ.Q`.
  let 𝔪 : Modulus D.E := D.twistModulus ϑ 1
  have h_mult : multiplicity w.asIdeal 𝔪.ideal =
      multiplicity w.asIdeal (Ideal.span {D.piM}) + if w ∈ ϑ.Q then 1 else 0 := by
    have h_Q : multiplicity w.asIdeal (∏ v ∈ ϑ.Q, v.asIdeal) = if w ∈ ϑ.Q then 1 else 0 := by
      rw [← count_normalizedFactors_eq_multiplicity
        (Finset.prod_ne_zero_iff.2 fun v _ ↦ v.prime.ne_zero), Finset.prod,
        normalizedFactors_prod_of_prime (by simp [prime])]
      -- the places of `ϑ.Q` are distinct, so `w` occurs in their product at most once
      simp [count_map_eq_count', asIdeal_injective, count_eq_of_nodup ϑ.Q.nodup]
    have h_ideal : 𝔪.ideal = Ideal.span {D.piM} * ∏ v ∈ ϑ.Q, v.asIdeal := by
      change ((∏ i : (k : Fin 2) × D.ChosenPlace k, (D.chosenPlace i).asIdeal) ^ 1) *
        ∏ v : ϑ.Q, v.val.asIdeal = _
      rw [pow_one, ← span_piM, ϑ.Q.prod_coe_sort]
    rw [h_ideal, multiplicity_mul w.prime (.of_prime_left w.prime (h_ideal ▸ 𝔪.ne_bot)), h_Q]
  have h_mul : (twistIdele ϑ).val * D.chosenIdele.val = 𝔪.generator.val := by
    rw [← Units.val_mul, twistIdele, div_mul_cancel]
  have h_val : Valued.v ((twistIdele ϑ).val w) * Valued.v (D.chosenIdele.val w) =
      Valued.v (𝔪.generator.val w) := by
    rw [← h_mul, ← map_mul]
    rfl
  rw [valued_chosenIdele, valued_generator, h_mult, Nat.cast_add, neg_add, WithZero.exp_add,
    mul_comm, mul_right_inj' WithZero.exp_ne_zero] at h_val
  split_ifs at h_val ⊢ with hw <;> simp [h_val]

/-- The modulus `D.twistModulus ϑ 1` is the product of the chosen places and the places of `ϑ.Q`.
The finite datum `pointDatumY ϑ k` on `Hom(Y_k, Y_{k+1})` is the indicator function of the inclusion
matrix modulo it, and the vacuum at the other places. This datum is fixed by the Heisenberg
translation `finHeisenbergOp` by the generator of the modulus times any integral vector `x`. -/
lemma finHeisenbergOp_generator_smul_pointDatumY (k : ℕ) {x : D.Y (k + 1) × D.Y k → 𝔸f D.E}
    (hx : x ∈ stdLattice D.E (D.Y (k + 1) × D.Y k)) :
    finHeisenbergOp ((D.spaceY k).hom (D.spaceY (k + 1))) ((D.twistModulus ϑ 1).generator.val • x)
      (pointDatumY ϑ k).val = (pointDatumY ϑ k).val := by
  set 𝔪 : Modulus D.E := D.twistModulus ϑ 1
  -- The datum is a combination of translates `finHeisenbergOp t vacElem` of the vacuum, with
  -- `star 𝔪.generator • t` integral.
  obtain ⟨c, hc, h_sum⟩ : IsAdmissibleCombination
      (fun t : D.Y (k + 1) × D.Y k → 𝔸f D.E ↦
        finHeisenbergOp ((D.spaceY k).hom (D.spaceY (k + 1))) t
          ((D.spaceY k).hom (D.spaceY (k + 1))).vacElem)
      (translations (D.Y (k + 1) × D.Y k) 1 (star 𝔪.generator.val)) 1 _ _ 0 (pointDatumY ϑ k).val :=
    isAdmissibleCombination_schrodingerOp_of_reduction _ _ (g := 0) (hg := by simp)
      (hΨ_int := by simp [ite_mem, Pi.single_apply]) (hΨ_size := id) (huv := projOn_vacElem _)
      (d := ⟨𝔪.generator.val, 𝔪.generator_mem⟩)
      (hd := by simp [𝔪, reduction_eq_zero_iff_generator_inv_mul_mem])
  rw [h_sum, map_finsuppSum]
  refine Finsupp.sum_congr fun t ht ↦ ?_
  have h_int : star 𝔪.generator.val • t ∈ stdLattice D.E (D.Y (k + 1) × D.Y k) := fun i ↦
    mem_Ô.mpr (hc.support_subset t ht i · (mod_cast Ideal.one_notMem _))
  -- So the translation by `𝔪.generator • x` commutes with the one by `t`, and it fixes the vacuum.
  have h_comm : stdLattice.selfDualAddChar D.E (𝔪.generator.val * star t ⬝ᵥ x) = 1 := by
    simpa using mem_stdLattice_iff_selfDualAddChar.mp hx (star 𝔪.generator.val • t) h_int
  simp [finHeisenbergOp_comm _ (_ • x), h_comm,
    finHeisenbergOp_vacElem (smul_mem_stdLattice 𝔪.generator_mem hx)]

end Stages

/-- Let `𝒲_{2j+2}` be the function `unfoldStage` on `U(Y_{2j+2})` built from a ramified source form
`φ`, the linear form `t` and the points `(ξ k, y k)` of U(Y_k). Let `w` be a place dividing
`π_N = D.piN`. View the chosen scaling `z_w = D.scalingGenerator w`, a finite adele of norm one, as
the point `inclXFin (scalarFin z_w)` of `U(Y_{2j+2})` that is the scalar `z_w` on the definite part
`X_{2j+2}` and the identity on the string. Suppose `x⁻¹ z_w x` lies in `levelY`: it is integral and
reduces to `1` at the chosen places and at those of `ϑ.Q`. Then `𝒲_{2j+2}` vanishes at `γ (a, x)`
for every `γ` in the Bessel group `R_{2j+2}` and every archimedean point `a`. -/
lemma unfoldStage_eq_zero_of_scalingGenerator (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (hφ : φ ∈ D.ramifiedSourceForms) (j : ℕ)
    (hj : 2 * j + 1 + 1 ≤ 2 * D.ϱ + 1) (w : D.piNPlaces)
    (γ : (D.gradingY (2 * j + 1 + 1) hj).besselGroup)
    (a : GInf D.E (D.signsY (2 * j + 1 + 1))) {x : Gf D.E (D.Y (2 * j + 1 + 1))}
    (hx : x⁻¹ * ((D.gradingY (2 * j + 1 + 1) hj).inclXFin
      (scalarFin (D.X (2 * j + 1 + 1)) (D.scalingGenerator w)) * x) ∈ levelY ϑ (2 * j + 1 + 1)) :
    unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY (2 * j + 1 + 1) hj) (γ.val * (a, x)) =
      0 := by
  -- Take `(a, x)` as the outer variable: the function is a coefficient of a chain of lifts of `φ`.
  let y' : ∀ k : ℕ, Gf D.E (D.Y k) := update y (2 * j + 1 + 1) x
  let ξ' : ∀ k : ℕ, GInf D.E (D.signsY k) := update ξ (2 * j + 1 + 1) a
  choose l hl using exists_unfoldStageOn_even_eq_sourceFn t ξ' (j + 1) hj
  have h_succ : unfoldStageOn ϑ t φ ξ' y' (2 * j + 1 + 1) hj γ =
      unfoldStage ϑ t φ ξ' y' (2 * j + 1) (by omega) (D.gradingY _ hj) (γ.val * (a, x)) := by
    simp only [unfoldStageOn_succ, ξ', y', update_self]
  have value : unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY _ hj) (γ.val * (a, x)) =
      (D.gradingY _ hj).sourceFn l
        (doubleLiftChain (D.liftKernel ϑ) (evaluatedDatum ϑ y') (j + 1) φ.val) γ := by
    rw [← unfoldStage_update ϑ t φ ξ y a x _ _ (Nat.lt_add_one _), ← h_succ]
    exact congrFun (hl ϑ φ y') γ
  -- `ω(1, z_w)`, acting on the last lift alone, fixes the data, so the chain annihilates `φ`.
  have h_fix := map_evaluatedDatum_of_conj_mem ϑ y' j hj (by simpa only [y', update_self] using hx)
  simp [value, D.doubleLiftChain_eq_zero_of_ramified ϑ w j.lt_succ_self h_fix hφ,
    sourceFn, algFormCoeff_apply]

/-- For consecutive gradings `D.gradingY k` and `D.gradingY (k + 1)`, the finite string map
`stringMapFin` between them sends `latticePlus 1` of `Y_k` (the projection `Λ_k⁺` of the standard
lattice to the span of the string) onto `D.ideleA • latticeMinus 1` of `Y_{k+1}`, that is onto
`𝔞 Λ_{k+1}⁻`, where the idele `D.ideleA` generates `𝔞`. -/
lemma map_stringMapFin_latticePlus_gradingY (k : ℕ) (hk : k + 1 ≤ 2 * D.ϱ + 1) :
    ((D.gradingY k).latticePlus 1).map
        (((D.gradingY k).stringMapFin (D.gradingY (k + 1) hk)).restrictScalars (Ô D.E)) =
      D.ideleA.val • (D.gradingY (k + 1) hk).latticeMinus 1 := by
  have h_spans (j : ℕ) (hj : j ≤ 2 * D.ϱ + 1) : (D.gradingY j hj).SpansLattice D.ideleA D.piNIdele
      (divStar D.ideleA ^ ((2 * D.ϱ + 1 - j + 2) / 2)) := by
    rw [show 2 * D.ϱ + 1 - j + 2 = D.m - j + 1 by have := D.m_eq_two_mul_varrho_add_two; omega]
    exact D.spansLattice_gradingY j hj
  exact (h_spans k _).map_stringMapFin_latticePlus (h_spans (k + 1) hk)
    D.isSplitSquarefree_piNIdele rfl D.v_gradingY_genericConst_eq_ideleA_mul_star

/-- A place `w` with `w` or its conjugate `star w` in `D.piNPlaces` (the places dividing `D.piN`) is
not among the places `ϑ.Q` of the tame character `ϑ`. -/
lemma notMem_Q_of_mem_piNPlaces (ϑ : D.TameChar) {w : FinPlace D.E}
    (hw : w ∈ D.piNPlaces ∨ star w ∈ D.piNPlaces) : w ∉ ϑ.Q := by
  intro hQ
  obtain ⟨-, -, hN⟩ := D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl hQ)
  exact hN ((D.isSplitLevel_piNPlaces.natCast_mem_iff w).2 hw)

/-- Let `𝒲_{2j+2}` be the function `unfoldStage` on `U(Y_{2j+2})` built from the character `ϑ`, a
ramified source form `φ`, the linear form `t` and the archimedean and finite points `(ξ k, y k)` of
U(Y_k). Let `w` be a place dividing `π_N = D.piN`, and let `x` be a finite point whose lattice `Λ'`
splits along `X_{2j+2}` at `w`: there the projection of `Λ'` to the span of the string lies in `Λ'`.
Then `𝒲_{2j+2}` vanishes at `γ (a, x)` for every `γ` in the Bessel group `R_{2j+2}` and every
archimedean point `a`. -/
lemma unfoldStage_eq_zero_of_latticeSplitsAt (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (hφ : φ ∈ D.ramifiedSourceForms) (j : ℕ)
    (hj : 2 * j + 1 + 1 ≤ 2 * D.ϱ + 1) (w : D.piNPlaces)
    (γ : (D.gradingY (2 * j + 1 + 1) hj).besselGroup)
    (a : GInf D.E (D.signsY (2 * j + 1 + 1))) {x : Gf D.E (D.Y (2 * j + 1 + 1))}
    (hx : (D.gradingY (2 * j + 1 + 1) hj).LatticeSplitsAt w x) :
    unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY (2 * j + 1 + 1) hj) (γ.val * (a, x)) =
      0 := by
  obtain ⟨hz_int, hz_off⟩ := D.isScalingAt_scalingGenerator w
  have hw_ne : star w.val ≠ w.val := fun h ↦
    D.isSplitSquarefree_piNIdele.star_notMem w w.property (by simp [h])
  -- The level is maximal above `w`.
  have w_notMem : w.val ∉ (Set.range (D.levelPlaces ϑ).placeAt).conjClosure := by
    suffices (¬D.IsChosen w.val ∧ w.val ∉ ϑ.Q) ∧ ¬D.IsChosen (star w.val) ∧ star w.val ∉ ϑ.Q by
      simpa [levelPlaces, range_chosenPlace]
    obtain ⟨h_chosen, h_chosen_star⟩ :=
      D.not_isChosen_of_N_mem (D.isSplitLevel_piNPlaces.natCast_level_mem w.val w.property)
    exact ⟨⟨h_chosen, notMem_Q_of_mem_piNPlaces ϑ (.inl w.property)⟩, h_chosen_star,
      notMem_Q_of_mem_piNPlaces ϑ (.inr (by simp))⟩
  exact unfoldStage_eq_zero_of_scalingGenerator ϑ t φ ξ y hφ j hj w γ a
    (maxCompactAt_le_levelOf w_notMem (hx.conj_scalarFin_mem hw_ne hz_int hz_off))

/-- **Support**. Let `j = k + 1 ≤ 2 ϱ + 1`, so that `D.gradingY j` presents the hermitian space
`Y_j` as a definite part `X_j` of grade zero plus a string of `2 ϱ + 1 - j` graded basis vectors.
Let `𝒲_j` be the function `unfoldStage` on U(Y_j) that `j` unfolding steps leave. It is built from a
tame character `ϑ` of modulus `ϑ.Q`, a source form `φ` on U(X_0) with a linear form `t` on its
values, and adelic points `(ξ i, y i)` of U(Y_i). Assume that `φ` is ramified and that `y 0` is
integral and reduces to `1` at the chosen places (`D.chosenLevel`). Suppose `𝒲_j (a, x) ≠ 0` for an
archimedean point `a` and a finite point `x`, and let `r'` be a finite point of the Bessel subgroup
of the grading such that the lattice `Λ'` of `r' x` is graded: it contains the part in each grade of
each of its vectors. Then `q̄ ^ j Λ⁻ ⊆ Λ'⁻` and `q ^ j Λ'⁻ ⊆ Λ⁻`. Here the idele `q = twistIdele ϑ`
generates the product of the places of `ϑ.Q`, `q̄` is its complex conjugate, `Λ` is the lattice of
`1` in `Y_j`, and `Λ⁻`, `Λ'⁻` (`latticeMinus`) are the intersections with the span of the string. -/
lemma hasLatticeBounds_of_unfoldStage_ne_zero (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (hφ : φ ∈ D.ramifiedSourceForms)
    (hy₀ : y 0 ∈ D.chosenLevel) (k : ℕ) (hk : k + 1 ≤ 2 * D.ϱ + 1)
    (a : GInf D.E (D.signsY (k + 1))) (x : Gf D.E (D.Y (k + 1)))
    (h_ne : unfoldStage ϑ t φ ξ y k (by omega) (D.gradingY (k + 1) hk) (a, x) ≠ 0)
    {r' : Gf D.E (D.Y (k + 1))} (hr' : r' ∈ (D.gradingY (k + 1) hk).besselFin)
    (h_graded' : (D.gradingY (k + 1) hk).IsGraded ((D.spaceY (k + 1)).lattice (r' * x))) :
    (D.gradingY (k + 1) hk).HasLatticeBounds (twistIdele ϑ).val (k + 1) (r' * x) := by
  induction k using Nat.strongRec with | ind k ih =>
  -- At some point `γ g_k` the function of the previous stage and the partial theta sum are both
  -- non-zero. The orbit of this point has a graded lattice with the bounds for `k`.
  obtain ⟨γ, hγ⟩ : ∃ γ : (D.gradingY k).besselGroup,
      unfoldStageOn ϑ t φ ξ y k (by omega) γ *
        (D.gradingY k).constTermAtStringMap (D.gradingY (k + 1) hk)
          (rankTwist (D.chainChar ϑ (k + 1))) (movedDatum ϑ ξ y k) γ.val (a, x) ≠ 0 :=
    exists_ne_zero_of_integral_ne_zero h_ne
  obtain ⟨r, hr, h_graded, h_bounds⟩ :
      (D.gradingY k).HasBoundedOrbit (twistIdele ϑ).val k (γ.val * (ξ k, y k)).2 := by
    cases k with
    | zero =>
      exact (D.spansLattice_gradingY 0 _).hasBoundedOrbit_zero _ (snd_mem_besselFin _ γ⁻¹.property)
        (by simpa using levelOf_le_stdLevel hy₀)
    | succ k =>
      -- `unfoldStageOn` at stage `k + 1` is a value of `𝒲_{k+1}`, so the induction hypothesis
      -- applies to every graded lattice in the orbit.
      let g : New.G D.E (D.signsY (k + 1)) := γ.val * (ξ (k + 1), y (k + 1))
      have h_prev : unfoldStage ϑ t φ ξ y k (by omega) (D.gradingY (k + 1) (by omega)) g ≠ 0 :=
        left_ne_zero_of_mul hγ
      exact .of_forall fun r ↦ ih k .refl _ g.1 g.2 h_prev
  have term_ne : (D.gradingY k).constTermAtStringMap (D.gradingY (k + 1) hk)
      (rankTwist (D.chainChar ϑ (k + 1))) (datumY ϑ k) (γ.val * (ξ k, y k)) (a, x) ≠ 0 := by
    simpa only [constTermAtStringMap, twistedPairWeil_movedDatum] using right_ne_zero_of_mul hγ
  -- Frequency: a non-zero term forces the shifted projection `Λ⁺`, scaled by
  -- `star (twistIdele ϑ) / D.ideleA`, of the lattice at stage `k` into `latticeMinus` at stage
  -- `k + 1`.
  have h_freq : (star (twistIdele ϑ) / D.ideleA).val •
      ((D.gradingY k).latticePlus (r * (γ.val * (ξ k, y k)).2)).map
        (((D.gradingY k).stringMapFin (D.gradingY (k + 1) hk)).restrictScalars (Ô D.E)) ≤
      (D.gradingY (k + 1) hk).latticeMinus (r' * x) := by
    rw [ideleA, twistIdele, star_div, div_div_div_cancel_right]
    exact smul_map_stringMapFin_latticePlus_le term_ne (D.twistModulus ϑ 1).generator
      (fun _ ↦ finHeisenbergOp_generator_smul_pointDatumY ϑ k) hr h_graded hr' h_graded'
  -- Sandwich: with the upper bound at stage `k` this gives the lower bound at stage `k + 1`.
  have h_lower : star (twistIdele ϑ).val ^ (k + 1) • (D.gradingY (k + 1) hk).latticeMinus 1 ≤
      (D.gradingY (k + 1) hk).latticeMinus (r' * x) :=
    smul_latticeMinus_le_of_map_latticePlus (map_stringMapFin_latticePlus_gradingY k hk)
      h_bounds.upper
      h_freq
  have hq_unit (w : FinPlace D.E) (hw : w ∈ D.piNPlaces ∨ star w ∈ D.piNPlaces) :
      Valued.v ((twistIdele ϑ).val w) = 1 := by
    rw [valued_twistIdele, ite_eq_right (notMem_Q_of_mem_piNPlaces ϑ hw)]
  obtain h_bounds' | ⟨h_odd, w, hw, h_split⟩ :=
    (D.spansLattice_gradingY (k + 1) hk).hasLatticeBounds_or_latticeSplitsAt
      D.isSplitSquarefree_piNIdele
      hq_unit h_lower
  · exact h_bounds'
  -- Otherwise the lattice splits at a place above `π_N`, where ramification makes `𝒲_j` vanish.
  obtain ⟨j, rfl⟩ : Odd k := ⟨k / 2, h_odd.elim (by omega)⟩
  let r₀ : (D.gradingY (2 * j + 1 + 1) hk).besselGroup := ⟨(1, r'), hr'⟩
  have h_zero : unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY (2 * j + 1 + 1) hk)
      (a, x) = 0 := by
    simpa [r₀] using unfoldStage_eq_zero_of_latticeSplitsAt ϑ t φ ξ y hφ j hk ⟨w, hw⟩ r₀⁻¹ a h_split
  exact absurd h_zero h_ne

end New.Data
