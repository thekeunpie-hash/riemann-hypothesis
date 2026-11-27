module

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Order
import Mathlib.RingTheory.PicardGroup
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import Lib.Weil.Periods.DescentVanishing
import Lib.Adelic.Witt.WittTheorem
import Lib.Cohomology.Etale.Basic
import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors
import Lib.General.Analysis.MeanValueAndTaylor
public import New.Determinant.Exchange.MatchingPartners
public import Lib.Weil.DualPair.ThetaIntegrals
public import Lib.Weil.DualPair.WeilAction
import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.SiegelWeil.Tower.LineGaussSums
import Mathlib.Algebra.Order.Star.Int
import Mathlib.CategoryTheory.Countable
public import New.Determinant.Exchange.StableSpacesStandardData
public import Lib.SiegelWeil.Tower.FiniteTateIntegral
public import Lib.Weil.DualPair.FiniteAction
import Lib.Adelic.Reduction.DefiniteClassSums
import Lib.Adelic.Unitary.RationalPoints
import Lib.SiegelWeil.Formula.StrongApproximation
import Lib.SiegelWeil.Tower.LargeSideConstantTerm

section
/-!
# Theta coefficients vanish off negative forms

This file finds a unit vector, supported on the negative signs, that kills the columns of a
frame. The rotations of its line lie in the maximal compact subgroup of `U (signMatrix s)`. It
shows that a polynomial whose Fock vector is fixed by the compact stabiliser of the frame is zero.
It proves that right translation by an element of a compact subgroup preserves the left Haar
measure. Here `New.Exchange.negCount s` is the number of signs `-1`.

## Main definitions and results

* `New.Exchange.centreCoeff_eq_zero_of_not_representedBy`: a Fourier coefficient of the theta
  integral `New.Exchange.thetaIntegral` vanishes, under conditions on weights, signs and
  integrability, at an invertible form that fails to be negative definite at some real place. After
  unfolding, the coefficient is an integral modulo the stabiliser of a frame, and the mean of the
  integrand over a compact subgroup is an invariant functional on Fock space, which is zero.
* `New.Exchange.apply_eq_zero_of_forall_fixed_eq_zero`: let a compact group act by bounded operators
  `ρ g` on a Banach space, and let `W` be a stable subspace of finite dimension in which only `0` is
  fixed. Then an invariant bounded functional `l` vanishes at every vector of `W` with continuous
  orbit: the mean of the orbit is a fixed vector of `W`.

Notions from other files:
* `thetaIntegral S T α β f`: the integral over `[U(T)]` of the theta kernel of the datum `f`.
* `PairFock E s t`, `realPairWeil`: the Fock space of the pair and its real Weil representation.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

@[expose] public section

section NonnegativeVanishing

open New Matrix MeasureTheory Measure Space Pointwise Pi Fintype MulAction ComplexConjugate
  ComplexOrder MatrixOrder Fock Heisenberg.IsVacuum Finset CStarAlgebra Exchange DiscreteSeries

section Rotation

open MvPolynomial hiding funext_iff

variable {E : Type} [Field E] [NumberField E] {a b n : Type} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] {s : n → ℤˣ} {t : a → ℤˣ}
  {μ : NumberField.InfinitePlace E → ℤ}

/-- Let `s` be a vector of signs and `U (signMatrix s)` the unitary group of the diagonal Hermitian
form with entries `s` (`u.val.val` is the matrix of `u`). If the Gram matrix of the columns of `x`
for this form is not of the form `-cᴴ * c` for any `c`, then some element of the group carries a
vector in the span of the columns to the positive basis vector `i`. -/
lemma New.Exchange.exists_unitary_mulVec_eq_single {i : n} (hs_pos : s i = 1) {x : Matrix n b ℂ}
    (hx : ¬∃ c : Matrix b b ℂ, cᴴ * signMatrix (-1 : b → ℤˣ) * c = xᴴ * signMatrix s * x) :
    ∃ (u : U (signMatrix s)) (v : b → ℂ), (u.val.val * x) *ᵥ v = Pi.single i 1 := by
  have hs_herm : (signMatrix s)ᴴ = signMatrix s := conjTranspose_signMatrix
  have h_herm : (xᴴ * signMatrix s * x).IsHermitian := isHermitian_conjTranspose_mul_mul x hs_herm
  -- the Gram form is not negative semidefinite, so it represents `1`
  have h_not_nsd : ¬(-(xᴴ * signMatrix s * x)).PosSemidef := fun h_psd ↦ by
    obtain ⟨c, hc⟩ := nonneg_iff_eq_star_mul_self.mp h_psd.nonneg
    exact hx ⟨c, by simpa [neg_eq_iff_eq_neg, star_eq_conjTranspose] using hc.symm⟩
  obtain ⟨v, -, hv⟩ := exists_mem_dotProduct_mulVec_eq_one h_herm ⊤ fun h_nonpos ↦ h_not_nsd <|
    .of_dotProduct_mulVec_nonneg h_herm.neg fun v ↦ by simpa [neg_mulVec] using h_nonpos v trivial
  -- `x v` and the basis vector `i` both have length `1`, so Witt's theorem maps one to the other
  have x_length : star (x *ᵥ v) ⬝ᵥ signMatrix s *ᵥ x *ᵥ v = 1 := by
    rw [← hv, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have i_length : star (basisFun ℂ n i) ⬝ᵥ signMatrix s *ᵥ basisFun ℂ n i = 1 := by
    simp [signMatrix, hs_pos]
  obtain ⟨u, hu⟩ : ∃ u : U (signMatrix s),
      u.val.val * replicateCol Unit (x *ᵥ v) = replicateCol Unit (basisFun ℂ n i) := by
    refine witt ⟨.I, by simp⟩ hs_herm IsHermitianInvolution.isUnit
      (.of_ne_zero fun h ↦ by simp [h] at x_length) (.of_ne_zero ((basisFun ℂ n).ne_zero i)) ?_
    ext
    simp only [conjTranspose_replicateCol, ← replicateRow_vecMul,
      replicateRow_mul_replicateCol_apply, ← dotProduct_mulVec, x_length, i_length]
  exact ⟨u, v, by simpa [← replicateCol_mulVec] using hu⟩

/-- Let `s` have `card b` more negative signs than `t`, and let the positive basis vector `i` be in
the span of the columns of `x`. There is a unit vector `r`, supported on the negative signs of `s`,
that kills the columns of `x` and the columns `j` of `y` with `t j = -1`. -/
lemma New.Exchange.exists_unit_dotProduct_col_eq_zero {a b n : Type} [Fintype a] [Fintype b]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {t : a → ℤˣ} {i : n} (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s) {x : Matrix n b ℂ} {v : b → ℂ}
    (hv : x *ᵥ v = Pi.single i 1) (y : n → a → ℂ) :
    ∃ r : n → ℂ, (∀ j : b, (r ⬝ᵥ fun k : n ↦ x k j) = 0) ∧
      (∀ j : a, t j = -1 → (r ⬝ᵥ fun k : n ↦ y k j) = 0) ∧
      (∀ k : n, s k ≠ -1 → r k = 0) ∧ r ⬝ᵥ star r = 1 := by
  -- the kernel of `f` is cut out by the three linear conditions
  let f : (n → ℂ) →ₗ[ℂ] ((b → ℂ) × ({j // t j = -1} → ℂ)) × ({k // s k ≠ -1} → ℂ) :=
    (x.vecMulLinear.prod (of fun k (j : {j // t j = -1}) ↦ y k j).vecMulLinear).prod
      (.funLeft ℂ ℂ Subtype.val)
  suffices h_ker : ∃ r ∈ f.ker, star r ⬝ᵥ (1 : Matrix n n ℂ) *ᵥ r = 1 by
    simpa [f, funext_iff, dotProduct_comm (star _), and_assoc, vecMul] using h_ker
  -- otherwise `f` is injective, so onto by `h_negCount`; but `hv` ties two of its coordinates
  refine exists_mem_dotProduct_mulVec_eq_one isHermitian_one f.ker fun h_nonpos ↦ ?_
  have f_inj : Function.Injective f := (injective_iff_map_eq_zero f).2 fun r hr ↦ by
    simpa [(dotProduct_star_self_nonneg r).ge_iff_eq'] using h_nonpos r hr
  have h_rank : Module.finrank ℂ (n → ℂ) =
      Module.finrank ℂ (((b → ℂ) × ({j // t j = -1} → ℂ)) × ({k // s k ≠ -1} → ℂ)) := by
    have h_count : card b + card {j // t j = -1} = card {k // s k = -1} := h_negCount
    simp [h_count, Nat.add_sub_cancel' (card_subtype_le _)]
  obtain ⟨r, hr⟩ : ∃ r : n → ℂ, f r = (0, 1) := (f.linearEquivOfInjective f_inj h_rank).surjective _
  obtain ⟨⟨r_x, -⟩, r_eq_one⟩ : (r ᵥ* x = 0 ∧ ∀ j : a, t j = -1 → (r ⬝ᵥ fun k ↦ y k j) = 0) ∧
      ∀ k : n, s k ≠ -1 → r k = 1 := by
    simpa [f, funext_iff, vecMul] using hr
  have h_coord : r i = r ᵥ* x ⬝ᵥ v := by simp [← dotProduct_mulVec, hv]
  simp [r_x, r_eq_one i (by simp [hs_pos])] at h_coord

/-- Let `s` be a vector of signs and `U (signMatrix s)` the unitary group of the diagonal Hermitian
form with entries `s`; its maximal compact subgroup `maxCompactU s` consists of its elements that
are also unitary for the standard form. Let `r` be a unit vector supported on the negative signs,
and `|η| = 1`. The rotation by `conj η` of the line of `star r` lies in `maxCompactU s`. -/
lemma New.Exchange.exists_mem_maxCompactU_eq_rotation {r : n → ℂ}
    (r_supp : ∀ k : n, s k ≠ -1 → r k = 0) (r_unit : r ⬝ᵥ star r = 1) {η : ℂ}
    (hη : η * conj η = 1) :
    ∃ c ∈ maxCompactU s, c.val.val = 1 + (conj η - 1) • vecMulVec (star r) r := by
  set P : Matrix n n ℂ := vecMulVec (star r) r with hP
  have P_herm : Pᴴ = P := by simp [hP]
  have P_sq : P * P = P := by simp [hP, vecMulVec_mul_vecMulVec, r_unit]
  have sign_P : signMatrix s * P = -P := by
    ext j k
    by_cases hj : s j = -1 <;> simp [hP, signMatrix, vecMulVec_apply, hj, r_supp j]
  have P_sign : P * signMatrix s = -P := by simpa [P_herm] using congrArg conjTranspose sign_P
  have h_adjoint : (1 + (conj η - 1) • P)ᴴ = 1 + (η - 1) • P := by simp [P_herm]
  -- the rotation preserves every form `J` with `J * P = P * J = ε • P`, as `η * conj η = 1`
  have h_form {J : Matrix n n ℂ} (ε : ℂ) (h_left : J * P = ε • P) (h_right : P * J = ε • P) :
      (1 + (conj η - 1) • P)ᴴ * J * (1 + (conj η - 1) • P) = J := by
    simp only [h_adjoint, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      h_left, h_right, P_sq]
    linear_combination (norm := module) hη • ε • P
  exact ⟨U.of IsHermitianInvolution.isUnit _ (h_form (-1) (by simp [sign_P]) (by simp [P_sign])),
    mem_unitaryGroupOf_iff.2 (h_form 1 (by simp) (by simp)), rfl⟩

open NumberField (InfinitePlace)

omit [NumberField E] in
/-- An element of the maximal compact subgroup, placed at `τ`, is block diagonal at every place. -/
lemma New.Exchange.mulSingle_mem_blockDiagAlg (τ : InfinitePlace E) {c : U (signMatrix s)}
    (c_mem : c ∈ maxCompactU s) (w : InfinitePlace E) :
    ((mulSingle τ c : GInf E s) w).val.val ∈ blockDiagAlg s := by
  obtain rfl | hw := eq_or_ne w τ <;> simp [mem_maxCompactU.mp c_mem, *]

/-- Let `c` be the rotation by `conj η`, `|η| = 1`, of the line of `star r`, for a unit vector `r`
supported on the negative signs of `s`. Placed at `τ`, it acts on the vector of `P` by a
substitution times `η ^ N`, where `N` is the number of positive signs of `t` minus `μ τ`. For each
`j` the substitution multiplies `∑ i, conj (r i) • X (τ, i, j)` by `conj η` if `t j = -1`, and
`∑ i, r i • X (τ, i, j)` by `η` if `t j = 1`. It fixes the combinations of the `X (τ, i, j)`
orthogonal to these, and all variables at other places. -/
lemma New.Exchange.realPairWeil_rotation_polyVector {τ : InfinitePlace E} {N : ℕ}
    (hN : μ τ + N = negCount (-t)) {r : n → ℂ} (r_supp : ∀ k : n, s k ≠ -1 → r k = 0)
    (r_unit : r ⬝ᵥ star r = 1) {η : ℂ} (hη : η * conj η = 1) {c : U (signMatrix s)}
    (c_mem : c ∈ maxCompactU s) (hc : c.val.val = 1 + (conj η - 1) • vecMulVec (star r) r)
    (P : MvPolynomial (InfinitePlace E × n × a) ℂ) :
    realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) =
      η ^ N • polyVector (realSigns E (homSigns t s)) (aeval (fun (w, k, j) ↦ X (w, k, j) +
        if w ≠ τ then 0
        else if t j = -1 then ((conj η - 1) * r k) • ∑ i : n, conj (r i) • X (τ, i, j)
        else ((η - 1) * conj (r k)) • ∑ i : n, r i • X (τ, i, j)) P) := by
  have c_inv : c⁻¹.val.val = 1 + (η - 1) • vecMulVec (star r) r :=
    ((coe_units_inv c.val).trans (maxCompactU.coe_inv ⟨c, c_mem⟩)).trans (by simp [hc])
  -- the positive block of `c` is `1`, and the negative block has determinant `η⁻¹`
  have pos_det : principalMinor c.val.val (s · = 1) = 1 := by
    have proj_r : posProj s *ᵥ star r = 0 := by
      simp +contextual [funext_iff, posProj, r_supp, mulVec]
    simp [hc, principalMinor_eq_det, ← posProj.eq_1, mul_vecMulVec, proj_r]
  have neg_det : principalMinor c.val.val (s · = -1) = η⁻¹ := by
    have neg_r : (diagonal fun k : n ↦ if s k = -1 then (1 : ℂ) else 0) *ᵥ star r = star r :=
      funext fun k ↦ by simpa [mulVec_diagonal, eq_comm (a := (0 : ℂ))] using r_supp k
    -- a rank one update of the identity
    have c_det : (1 + (conj η - 1) • vecMulVec (star r) r).det = η⁻¹ := by
      rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_mul_comm]
      simp [r_unit, eq_inv_of_mul_eq_one_right hη]
    simp [hc, principalMinor_eq_det, mul_vecMulVec, neg_r, c_det]
  rw [realPairWeil_polyVector (hx := by simp) (hy := mulSingle_mem_blockDiagAlg τ c_mem),
    Fintype.prod_eq_single τ fun w hw ↦ by simp [hw]]
  congr 1
  · simp [pos_det, neg_det, eq_sub_of_add_eq hN, negCount]
  -- a variable is moved by a column of `c` if `s k = t j`, and by a row of `c⁻¹` otherwise
  refine congrArg (fun σ ↦ polyVector _ (aeval σ P)) (funext fun ⟨w, k, j⟩ ↦ ?_)
  obtain rfl | hw := eq_or_ne w τ
  · simp only [mulSingle_eq_same, c_inv, hc]
    by_cases hk : s k = -1
    · by_cases hj : t j = -1 <;>
        simp [hk, hj, eq_comm (a := (-1 : ℤˣ)), Matrix.one_apply, vecMulVec_apply, add_smul,
          sum_add_distrib, smul_sum, smul_smul, mul_assoc, mul_comm (r k)]
    · simp [r_supp k hk, Matrix.one_apply, vecMulVec_apply]
  · simp [hw, Matrix.one_apply]

/-- Let `μ τ` be less than the number `negCount (-t)` of positive signs of `t`, and let `r` be a
unit vector supported on the negative signs of `s`. If the elements `1 + δ • star r rᵀ` of the
maximal compact subgroup `maxCompactU s`, placed at `τ` (`mulSingle`) and `1` elsewhere, fix the
vector of `P`, then `P` vanishes at every point `z` at which the variables
`∑ k, conj (r k) • X (τ, k, j)` with `t j = -1` vanish. -/
lemma New.Exchange.eval_eq_zero_of_rotation_fixed {τ : InfinitePlace E}
    (hμ : μ τ < negCount (-t)) {r : n → ℂ} (r_supp : ∀ k : n, s k ≠ -1 → r k = 0)
    (r_unit : r ⬝ᵥ star r = 1) {P : MvPolynomial (InfinitePlace E × n × a) ℂ}
    (h_fixed : ∀ c ∈ maxCompactU s, ∀ δ : ℂ, c.val.val = 1 + δ • vecMulVec (star r) r →
      realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) =
        polyVector (realSigns E (homSigns t s)) P)
    {z : InfinitePlace E × n × a → ℂ}
    (hz : ∀ j : a, t j = -1 → ∑ k : n, conj (r k) * z (τ, k, j) = 0) : eval z P = 0 := by
  -- At `z` the rotation by `conj η` brings in only nonnegative powers of `η`, and the vacuum a
  -- positive power. So `eval z P` is the value on the unit circle of a polynomial `g` with
  -- `g 0 = 0`, which is zero by the mean value property.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, μ τ + M.succ = negCount (-t) := hμ.dest
  -- the substitution moves `z` to `z + (η - 1) • z'`
  let z' : InfinitePlace E × n × a → ℂ := fun (w, k, j) ↦
    if w ≠ τ ∨ t j = -1 then 0 else conj (r k) * ∑ i : n, r i * z (τ, i, j)
  let g (η : ℂ) : ℂ := η ^ M.succ * eval (z + (η - 1) • z') P
  have h_circle (η : ℂ) (hη : η * conj η = 1) : g η = eval z P := by
    obtain ⟨c, c_mem, hc⟩ := exists_mem_maxCompactU_eq_rotation r_supp r_unit hη
    let σ : InfinitePlace E × n × a → MvPolynomial (InfinitePlace E × n × a) ℂ :=
      fun (w, k, j) ↦ X (w, k, j) + if w ≠ τ then 0
        else if t j = -1 then ((conj η - 1) * r k) • ∑ i : n, conj (r i) • X (τ, i, j)
        else ((η - 1) * conj (r k)) • ∑ i : n, r i • X (τ, i, j)
    have h_poly : η ^ M.succ • aeval σ P = P :=
      polyVector_injective (ε := realSigns E (homSigns t s)) <| by
        rw [map_smul, ← realPairWeil_rotation_polyVector hM r_supp r_unit hη c_mem hc,
          h_fixed c c_mem _ hc]
    have h_point : (fun p ↦ aeval z (σ p)) = z + (η - 1) • z' := by
      funext ⟨w, k, j⟩
      by_cases hw : w = τ <;> by_cases hj : t j = -1 <;> simp [σ, z', hw, hj, hz j, mul_assoc]
    calc g η = η ^ M.succ * aeval z (aeval σ P) := by rw [comp_aeval_apply, h_point, aeval_eq_eval]
      _ = eval z P := by rw [aeval_eq_eval, ← smul_eval, h_poly]
  have g_diff : Differentiable ℂ g := by simpa only [g, eval_eq'] using by fun_prop
  calc eval z P = ∫ θ : UnitAddCircle, g θ.toCircle := by
        simp [h_circle, Circle.norm_coe, RCLike.mul_conj, Measure.real]
    _ = 0 := by simp [integral_comp_toCircle_eq_apply_zero g_diff.differentiableOn, g]

/-- Let a compact group act by bounded operators `ρ g` on a Banach space, and let `W` be a stable
subspace of finite dimension in which only `0` is fixed. Then an invariant bounded functional `l`
vanishes at every vector of `W` with continuous orbit: the mean of the orbit is a fixed vector of
`W`. -/
lemma New.Exchange.apply_eq_zero_of_forall_fixed_eq_zero {G V : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (ρ : G →* V →L[ℂ] V) {W : Submodule ℂ V}
    [FiniteDimensional ℂ W] (h_stable : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W)
    (h_fixed : ∀ w ∈ W, (∀ g : G, ρ g w = w) → w = 0) {l : V →L[ℂ] ℂ}
    (l_inv : ∀ (g : G) (v : V), l (ρ g v) = l v) {v : V} (hv : v ∈ W)
    (h_cont : Continuous fun g : G ↦ ρ g v) : l v = 0 := by
  borelize G
  let κ : Measure G := haarMeasure ⊤
  have : IsProbabilityMeasure κ := ⟨haarMeasure_self⟩
  have h_int : Integrable (fun g : G ↦ ρ g v) κ := integrable_of_compactSpace h_cont
  have mean_mem : ∫ g : G, ρ g v ∂κ ∈ W :=
    (W.restrictScalars ℝ).convex.integral_mem W.isClosed_of_finiteDimensional
      (.of_forall fun g ↦ h_stable g v hv) h_int
  have mean_fixed (k : G) : ρ k (∫ g : G, ρ g v ∂κ) = ∫ g : G, ρ g v ∂κ := by
    simpa [← (ρ k).integral_comp_comm h_int] using integral_mul_left_eq_self (ρ · v) k
  calc l v = l (∫ g : G, ρ g v ∂κ) := by simp [← l.integral_comp_comm h_int, l_inv]
    _ = 0 := by rw [h_fixed _ mean_mem mean_fixed, map_zero]

omit [DecidableEq b] in
/-- Let the weight `μ τ` be less than the number `negCount (-t)` of positive signs of `t`. Let `s`
have `card b` more negative signs than `t`, and let the positive basis vector `i` be in the span of
the columns of `x`. Suppose every `c` in `maxCompactU s` with `c * x = x`, placed at `τ` and acting
by `realPairWeil μ 0`, fixes the Fock vector `polyVector` of a polynomial `P`. Then `P = 0`. -/
lemma New.Exchange.eq_zero_of_stabilizer_fixes_polyVector {τ : InfinitePlace E}
    (hμ : μ τ < negCount (-t)) {i : n} (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s) {x : Matrix n b ℂ} {v : b → ℂ}
    (hv : x *ᵥ v = Pi.single i 1) {P : MvPolynomial (InfinitePlace E × n × a) ℂ}
    (h_fixed : ∀ c ∈ maxCompactU s, c.val.val * x = x →
      realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) =
        polyVector (realSigns E (homSigns t s)) P) : P = 0 := by
  -- For each point `z`, counting dimensions gives a line in the span of the negative basis vectors,
  -- spanned by `star r`, that is orthogonal to `x` and whose variables with `t j = -1` vanish at
  -- `z`. The rotations of this line fix `x`.
  refine MvPolynomial.funext fun z ↦ ?_
  obtain ⟨r, r_x, r_z, r_supp, r_unit⟩ :=
    exists_unit_dotProduct_col_eq_zero hs_pos h_negCount hv fun k j ↦ conj (z (τ, k, j))
  have rotation_fixes (δ : ℂ) : (1 + δ • vecMulVec (star r) r) * x = x := by
    simp [← Matrix.ext_iff, r_x, Matrix.add_mul, vecMulVec_mul, vecMulVec_apply, vecMul]
  have hz (j : a) (hj : t j = -1) : ∑ k : n, conj (r k) * z (τ, k, j) = 0 := by
    simpa [dotProduct] using congrArg conj (r_z j hj)
  refine eval_eq_zero_of_rotation_fixed hμ r_supp r_unit (fun c c_mem δ hc ↦ ?_) hz
  exact h_fixed c c_mem (by rw [hc, rotation_fixes])

/-- An element `c` of the maximal compact subgroup, placed at `τ`, maps the Fock vector of a
homogeneous polynomial of degree `d` to the Fock vector of another such polynomial. -/
lemma New.Exchange.realPairWeil_mulSingle_mem_map_homogeneousSubmodule (τ : InfinitePlace E)
    {c : U (signMatrix s)} (c_mem : c ∈ maxCompactU s) {d : ℕ}
    {P : MvPolynomial (InfinitePlace E × n × a) ℂ} (hP : P.IsHomogeneous d) :
    realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) ∈
      (homogeneousSubmodule (InfinitePlace E × n × a) ℂ d).map
        (polyVector (realSigns E (homSigns t s))) := by
  -- `c` acts by a scalar times a linear substitution, which keeps the degree
  rw [realPairWeil_polyVector (hx := by simp) (hy := mulSingle_mem_blockDiagAlg τ c_mem)]
  refine Submodule.smul_mem _ _ (Submodule.mem_map_of_mem ?_)
  rw [mem_homogeneousSubmodule, ← one_mul d]
  refine hP.aeval _ fun p ↦ ?_
  -- each variable goes to a linear form
  exact IsHomogeneous.sum _ _ 1 fun i _ ↦ IsHomogeneous.sum _ _ 1 fun j _ ↦
    (homogeneousSubmodule _ ℂ 1).smul_mem _ (isHomogeneous_X ℂ _)

/-- Let the weight `μ τ` be less than the number `negCount (-t)` of positive signs of `t`. Let `s`
have a positive sign, and `card b` more negative signs than `t`. Let the Gram matrix of the columns
of `x` not be of the form `-cᴴ * c`. For some isometry `u` at the place `τ`, a functional on Fock
space that is invariant under the compact stabiliser of `u * x`, acting by the real Weil
representation of weight `μ` (`realPairWeil`), is zero. -/
lemma New.Exchange.exists_isometry_fock_functional_eq_zero (τ : InfinitePlace E)
    (hμ : μ τ < negCount (-t)) {i : n} (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s) {x : Matrix n b ℂ}
    (hx : ¬∃ c : Matrix b b ℂ, cᴴ * signMatrix (-1 : b → ℤˣ) * c = xᴴ * signMatrix s * x) :
    ∃ u : U (signMatrix s), ∀ l : PairFock E t s →L[ℂ] ℂ,
      (∀ c ∈ maxCompactU s, c.val.val * (u.val.val * x) = u.val.val * x →
        ∀ v : PairFock E t s, l (realPairWeil μ 0 (1, mulSingle τ c) v) = l v) → l = 0 := by
  -- By Witt's theorem choose `u` with the positive basis vector `i` in the span of `u x`. The
  -- compact stabiliser `C` of `u x` acts on the polynomial vectors of each degree, and these span
  -- a dense subspace, so it suffices that `C` fixes no nonzero polynomial vector.
  obtain ⟨u, v, hu⟩ := exists_unitary_mulVec_eq_single hs_pos hx
  refine ⟨u, fun l l_inv ↦ ?_⟩
  let C : Subgroup (maxCompactU s) := stabilizer (maxCompactU s) (u.val.val * x)
  have hC : IsClosed (C : Set (maxCompactU s)) := isClosed_singleton.preimage
    (f := fun c : maxCompactU s ↦ c.val.val.val * (u.val.val * x)) (by fun_prop)
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  let ρ : C →* PairFock E t s →L[ℂ] PairFock E t s := (realPairWeil μ 0).comp <|
    (MonoidHom.inr _ _).comp <| (MonoidHom.mulSingle _ τ).comp <|
      (maxCompactU s).subtype.comp C.subtype
  let ε : InfinitePlace E × n × a → ℤˣ := realSigns E (homSigns t s)
  have homogeneous_zero (d : ℕ) (P : MvPolynomial (InfinitePlace E × n × a) ℂ)
      (hP : P.IsHomogeneous d) : l (polyVector ε P) = 0 := by
    let W : Submodule ℂ (PairFock E t s) := (homogeneousSubmodule _ ℂ d).map (polyVector ε)
    have : FiniteDimensional ℂ W := Module.Finite.of_fg ((homogeneousSubmodule_fg _ ℂ d).map _)
    have h_stable (c : C) : ∀ w ∈ W, ρ c w ∈ W := by
      rintro _ ⟨Q, hQ, rfl⟩
      exact realPairWeil_mulSingle_mem_map_homogeneousSubmodule τ c.val.prop hQ
    have h_fixed : ∀ w ∈ W, (∀ c : C, ρ c w = w) → w = 0 := by
      rintro _ ⟨Q, -, rfl⟩ hQ
      rw [eq_zero_of_stabilizer_fixes_polyVector (P := Q) hμ hs_pos h_negCount hu
        fun c c_mem c_fix ↦ hQ ⟨⟨c, c_mem⟩, c_fix⟩, map_zero]
    have h_cont : Continuous fun c : C ↦
        realPairWeil μ 0 (1, mulSingle τ c.val.val) (polyVector ε P) := by
      have := continuous_mulSingle (A := fun _ : InfinitePlace E ↦ U (signMatrix s)) τ
      fun_prop
    exact apply_eq_zero_of_forall_fixed_eq_zero ρ h_stable h_fixed
      (fun ⟨⟨c, c_mem⟩, c_fix⟩ ↦ l_inv c c_mem c_fix) (Submodule.mem_map_of_mem hP) h_cont
  -- a polynomial is the sum of its homogeneous components, and polynomial vectors are dense
  refine ContinuousLinearMap.ext (isClosed_property denseRange_polyVector l.isClosed_ker fun P ↦ ?_)
  rw [← P.sum_homogeneousComponent, _root_.map_sum]
  exact l.ker.sum_mem fun d _ ↦ homogeneous_zero d _ (homogeneousComponent_isHomogeneous d P)

end Rotation

open NumberField (InfinitePlace)

/-- Right translation by an element of a compact subgroup preserves the left Haar measure of a
locally compact group: the modular function is `1` on compact subgroups. -/
lemma New.Exchange.haar_map_mul_right_of_isCompact {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] {C : Subgroup H} (hC : IsCompact (C : Set H)) (k : C) :
    (haar : Measure H).map (· * (k : H)) = haar := by
  -- both sides are Haar measures, and they agree on the compact neighbourhood `A * C`, which is
  -- stable under right translation by `k`
  obtain ⟨A, hA, hCA⟩ := exists_compact_superset hC
  let K : TopologicalSpace.PositiveCompacts H := ⟨⟨A * C, hA.mul hC⟩,
    (k : H) * k, subset_interior_mul_left (Set.mul_mem_mul (hCA k.prop) k.prop)⟩
  have h_eq : (haar : Measure H).map (· * (k : H)) K = haar (K : Set H) := by
    simp [K, Set.preimage, (measurableEmbedding_mulRight _).map_apply,
      ← QuotientGroup.preimage_image_mk_eq_mul]
  rw [haarMeasure_unique (map _ _) K, h_eq, ← haarMeasure_unique]

variable {E : Type} [Field E] [CMType E] [H : WeilData E] {a b m n : Type} [Fintype a]
  [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

omit [DecidableEq b] in
/-- Let `C` be the elements of the stabiliser of an adelic frame `x'` that lie in the conjugate of
`maxCompact E s` by `u⁻¹` at the real place `τ`, with an invariant probability measure `κ`. Suppose
that only the zero functional on Fock space is invariant, for the weight `μ` of `ν`, under the
compact stabiliser of `u x'` at `τ`. Then the theta functional `θ` of the Weil representation with
characters `ν`, `δ` has mean zero over `k C u⁻¹`. -/
lemma New.Exchange.integral_theta_pairWeil_stabilizer_eq_zero {s : n → ℤˣ} {t : a → ℤˣ}
    {Y : Space E n s} {Z : Space E a t} {μ : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} (ν δ : AutChar E) [AutChar.HasWeight ν μ ψ]
    {x' : Matrix n b (𝔸 E)} {τ : InfinitePlace E} {u : U (signMatrix s)}
    (h_no_invariant_functional : ∀ l : PairFock E t s →L[ℂ] ℂ, (∀ c ∈ maxCompactU s,
      c.val.val * (u.val.val * atRealPlace x' τ) = u.val.val * atRealPlace x' τ →
        ∀ v : PairFock E t s, l (realPairWeil μ 0 (1, mulSingle τ c) v) = l v) → l = 0)
    (κ : Measure ((ConjAct.toConjAct ((mulSingle τ u⁻¹, 1) : G E s) • maxCompact E s).subgroupOf
      (stabilizer (G E s) x')))
    [IsProbabilityMeasure κ] [κ.IsMulRightInvariant] (k : stabilizer (G E s) x') (φ : 𝒮 (Z.hom Y)) :
    ∫ c, θ (Z.hom Y) (pairWeil Z Y ν δ (1, (k : G E s) *
      (((c : stabilizer (G E s) x') : G E s) * ((mulSingle τ u⁻¹, 1) : G E s))) φ) ∂κ = 0 := by
  -- The mean is a bounded functional. On data with a fixed finite part it is invariant under the
  -- compact stabiliser at `τ`, so it is zero by `h_no_invariant_functional`; such data determine
  -- it.
  let S : Subgroup (G E s) := stabilizer (G E s) x'
  let w : G E s := (mulSingle τ u⁻¹, 1)
  let C : Subgroup S := (ConjAct.toConjAct w • maxCompact E s).subgroupOf S
  have hS : IsClosed (S : Set (G E s)) :=
    isClosed_singleton.preimage (f := fun h : G E s ↦ G.adeleMatrix h * x') (by fun_prop)
  have hC : IsCompact (C : Set S) := (isCompact_maxCompact.smul _).preimage_val
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  let A (c : C) : 𝒮 (Z.hom Y) →L[ℂ] ℂ := θ (Z.hom Y) ∘L pairWeil Z Y ν δ (1, k * (c * w))
  have hA (f : 𝒮 (Z.hom Y)) : Continuous fun c : C ↦ A c f := by
    simp only [A, ContinuousLinearMap.comp_apply]
    fun_prop
  have h_apply (f : 𝒮 (Z.hom Y)) : strongIntegral κ A f = ∫ c : C, A c f ∂κ :=
    strongIntegral_apply κ A (fun f' ↦ integrable_of_compactSpace (hA f')) f
  -- the functional `v ↦ mean (v ⊗ f)` on Fock space is zero
  have h_fock_zero (f : 𝒮 (Z.hom Y)) : strongIntegral κ A ∘L (Z.hom Y).integrated.flip f = 0 := by
    refine h_no_invariant_functional _ fun c hc hcx v ↦ ?_
    let p : G E s := w * (mulSingle τ c, 1) * w⁻¹
    have hpS : p ∈ S := by
      refine matrix_ext_𝔸 (fun τ' ↦ Matrix.map_mul.trans ?_) (Matrix.map_mul.trans ?_)
      · change (p.1 τ' : Matrix n n ℂ) * atRealPlace x' τ' = atRealPlace x' τ'
        obtain rfl | h_ne := eq_or_ne τ' τ
        · simp [p, w, hcx, Matrix.mul_assoc]
        · simp [p, w, h_ne]
      · have hp_fin : (G.adeleMatrix p).map Prod.snd = 1 := by ext; simp [p, w, mul_assoc]
        exact (congrArg (· * x'.map Prod.snd) hp_fin).trans (Matrix.one_mul _)
    have hpC : (⟨p, hpS⟩ : S) ∈ C := ⟨(mulSingle τ c, 1), ⟨by simpa, by simp⟩, rfl⟩
    -- the integral is unchanged when `c'` is replaced by `c' * p`
    have h_translate (f' : 𝒮 (Z.hom Y)) :
        ∫ c' : C, A (c' * ⟨⟨p, hpS⟩, hpC⟩) f' ∂κ = ∫ c' : C, A c' f' ∂κ :=
      integral_mul_right_eq_self (A · f') _
    simpa [← pairWeil_integrated_right ν δ, h_apply, A, p, rep_apply_apply, mul_assoc] using
      h_translate _
  have h_zero : strongIntegral κ A φ = 0 :=
    Space.map_eq_zero_of_map_integrated_eq_zero (Z.hom Y) (Space.projOn_empty _ φ) fun P y _ ↦
      DFunLike.congr_fun (h_fock_zero ((Z.hom Y).finHeisenbergOp y (Z.hom Y).vacElem))
        (polyVector _ P)
  simpa [h_apply, A] using h_zero

/-- Let the splitting `D` write `X` as the sum of two dual isotropic subspaces of rank `#b` and of
`Z`, orthogonal to both. The slice at `x'` (`D.homSlice`) is the map from data on `Hom(X, Y)` to
data on `Hom(Z, Y)` that takes the value `x'` on one of the two subspaces. An element `k` of the
stabiliser of `x'` in `U(Y)` commutes with it: on the slice it acts by the Weil representation of
the smaller pair `(Z, Y)`, with the character `ν` if `δ = ν υ ^ #b`, for `υ` the character
`upsilonU1` of the Weil data. -/
lemma New.Exchange.homSlice_pairWeil_stabilizer_mul {r : m → ℤˣ} {s : n → ℤˣ} {t : a → ℤˣ}
    {X : Space E m r} {Y : Space E n s} {Z : Space E a t} (D : X.Splitting Z b) {ν δ : AutChar E}
    (hδ : δ = ν * H.upsilonU1 ^ Fintype.card b) {x' : Matrix n b (𝔸 E)}
    (k : stabilizer (G E s) x') (g : G E r) (h : G E s) (f : 𝒮 (X.hom Y)) :
    D.homSlice Y x' (pairWeil X Y δ δ (g, k * h) f) =
      pairWeil Z Y ν δ (1, k) (D.homSlice Y x' (pairWeil X Y δ δ (g, h) f)) := by
  have hk : k.val⁻¹.adeleMatrix * x' = x' := k⁻¹.property
  simpa [← hδ, -coe_units_inv, hk, Prod.mk_one_one, rep_apply_apply] using
    D.homSlice_levi Y ν δ 1 1 k x' (pairWeil X Y δ δ (g, h) f)

/-- The spaces `X`, `Y`, `Z` are Hermitian over `E` with Weil data `H`: a splitting Hecke character
`υ`, whose restriction to the norm-one ideles is `H.upsilonU1`, and a scalar `H.j` of `E` with
`conj j = -j`. Let the splitting `D` write `X` as the sum of two dual isotropic subspaces of rank
`#b` and of `Z`, orthogonal to both. (a) The weights `μ τ` are less than the number of positive
signs of `Z`; `Y` has a positive sign, and `#b` more negative signs than `Z`. (b) `ν` has weight
`μ`, with any tame part `ψ`, and `δ = ν H.upsilonU1 ^ #b`. (c) `T` is invertible and, at some real
place, not of the form `-cᴴ c` (`RepresentedBy` fails). (d) The sum over the rational frames of the
absolute values of the terms of the unfolded theta integral is integrable (`HasIntegrableTerms`).
The theta integral `thetaIntegral X Y δ δ f` integrates the kernel of `f` over `[U(Y)]`, in the Weil
representation of `(X, Y)` in which `δ` is the character of `U(1)` for both spaces: the first fixes
the action of `U(Y)`, the second that of `U(X)`. Then `centerCoeff` at `H.j • T` of this function on
`U(X)`, its Fourier coefficient along the centre of the unipotent radical of `D`, vanishes at `g`.
-/
lemma New.Exchange.centreCoeff_eq_zero_of_not_representedBy {r : m → ℤˣ} {ν : AutChar E}
    {X : Space E m r} {s : n → ℤˣ} {Y : Space E n s} {t : a → ℤˣ} {Z : Space E a t}
    {D : X.Splitting Z b} {μ : InfinitePlace E → ℤ} {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
    {δ : AutChar E} {f : 𝒮 (X.hom Y)} {g : G E r} {T : Matrix b b E} [AutChar.HasWeight ν μ ψ]
    (i : n) (hμ : ∀ τ : InfinitePlace E, μ τ < negCount (-t)) (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s)
    (hδ : δ = ν * H.upsilonU1 ^ Fintype.card b) (hT_unit : IsUnit T)
    (hT_not_neg : ¬RepresentedBy (-1) (T.map toAdele)) (h_int : D.HasIntegrableTerms Y δ δ f g) :
    D.centerCoeff (H.j • T) (thetaIntegral X Y δ δ f) g = 0 := by
  -- If no rational frame has Gram matrix `T` the coefficient is an empty sum. Otherwise it is the
  -- integral of the term of one frame `x` modulo the rational stabiliser of `x`. The mean of the
  -- term over a compact subgroup `C` of the adelic stabiliser `S` gives an invariant functional
  -- on Fock space at a place `τ`, which is zero; so the integral vanishes.
  have h_integral : thetaIntegral X Y δ δ f =
      fun k ↦ ∫ h, pairTheta X Y δ δ f (k, h) * 1 ∂Y.quotMeasure := funext (by simp [thetaIntegral])
  rw [h_integral]
  obtain h_empty | ⟨x, rfl⟩ := isEmpty_or_nonempty {x : Matrix n b E | xᴴ * Y.J * x = T}
  · rw [D.centreCoeff_integral_eq_tsum h_int continuous_const T, tsum_empty]
  let x' : Matrix n b (𝔸 E) := Y.x⁻¹.val * x.map toAdele
  let S : Subgroup (G E s) := stabilizer (G E s) x'
  have hS : IsClosed (S : Set (G E s)) :=
    isClosed_singleton.preimage (f := fun h : G E s ↦ G.adeleMatrix h * x') (by fun_prop)
  have hΓS : Y.ratStabilizer x ≤ S := by
    rintro _ ⟨γ, hγ : (γ : Matrix n n E) * x = x, rfl⟩
    exact (Y.ratMap_mul_toAdele Y γ x).trans (by simp [x', hγ])
  have h_fixesLeft_one : Y.Γ.FixesLeft fun _ ↦ (1 : ℂ) := by simp
  -- a real place `τ` at which the Gram matrix is not negative, and the isometry `u` there
  obtain ⟨τ, hτ⟩ : ∃ τ : InfinitePlace E, ¬∃ c : Matrix b b ℂ,
      cᴴ * signMatrix (-1 : b → ℤˣ) * c = atRealPlace ((xᴴ * Y.J * x).map toAdele) τ :=
    not_forall.1 hT_not_neg
  rw [← gram_at_point_eq_map, ← gram_atRealPlace] at hτ
  obtain ⟨u, hu⟩ := exists_isometry_fock_functional_eq_zero τ (hμ τ) hs_pos h_negCount hτ
  -- `C` is the intersection of `S` with a conjugate of the maximal compact subgroup
  let w : G E s := (mulSingle τ u⁻¹, 1)
  let C : Subgroup S := (ConjAct.toConjAct w • maxCompact E s).subgroupOf S
  have hC : IsCompact (C : Set S) := (isCompact_maxCompact.smul _).preimage_val
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have : IsClosed (C : Set S) := hC.isClosed
  let κ : Measure C := (haar (Set.univ : Set C))⁻¹ • haar
  have : κ.IsMulRightInvariant := isMulRightInvariant_smul _
  -- as right translation by `C` keeps the Haar measure of `S`, it suffices that the term has mean
  -- zero over `C`
  have h_mean (k : S) (h : G E s) : ∫ c : C, D.thetaTerm Y δ δ f g x (↑(k * c) * h) ∂κ = 0 := by
    change ∫ c : C, θ _ (D.homSlice Y x' (pairWeil X Y δ δ (g, ↑(k * c) * h) f)) ∂κ = 0
    simp only [homSlice_pairWeil_stabilizer_mul D hδ]
    -- apply the vanishing of the mean over `k C w` to the datum transformed by `w⁻¹` and `h`
    simpa [w, rep_apply_apply, mul_assoc, Prod.mk_one_one] using
      integral_theta_pairWeil_stabilizer_eq_zero ν δ hu κ k
        (pairWeil Z Y ν δ (1, w⁻¹) (D.homSlice Y x' (pairWeil X Y δ δ (g, h) f)))
  have h_scale (k : C) : (haar : Measure S).map (· * (k : S)) = (1 : NNReal) • haar := by
    simp [haar_map_mul_right_of_isCompact hC]
  -- unfolding: the coefficient is the integral of the term modulo the rational stabiliser
  have h_unfold : D.centerCoeff (H.j • (xᴴ * Y.J * x))
        (fun k ↦ ∫ h, pairTheta X Y δ δ f (k, h) * 1 ∂Y.quotMeasure) g =
      ∫ h, D.thetaTerm Y δ δ f g x h * 1 ∂(Y.ratStabilizer x).quotMeasure :=
    (D.centreCoeff_eq_integral_ratStabilizer h_int continuous_const h_fixesLeft_one hT_unit).right
  rw [h_unfold]
  -- translation by `C` scales the measure by `d = 1`, while the mean is `a = 0` times the term
  exact integral_quotMeasure_eq_zero_of_mean volume
    (D.fixesLeft_thetaTerm_mul h_fixesLeft_one x) (by fun_prop [Splitting.thetaTerm]) hΓS κ
    (translator := fun _ c ↦ (c : S)) (fun _ ↦ measurable_subtypeVal) (d := 1) (a := 0)
    (h_scale := fun _ ↦ h_scale) zero_ne_one (h_mean := by simpa using h_mean)

end NonnegativeVanishing
end
end

section
/-!
# The difference in the exchange identity as an equivariant lift

This file is a step towards the identity between theta integrals over `U(V)` and `U(V')`, where
`rk W = rk V + rk V'`. The identity is taken for matched functions `Φ`, `Ψ` at the ramified places
of the tame character `𝔠`. This file defines the small side `New.Exchange.thetaSmall`. It proves
how `thetaLarge` and `thetaSmall` change under translation at the ramified places, and that both
are invariant under the integral points of `U(W)` that are trivial there. From this it shows that
the difference of the two sides is an equivariant lift.

## Main definitions and results

* `New.Exchange.thetaSmall`: the theta integral for `V'` of the datum `Ψ`.
* `New.Exchange.exists_isEquivariantLift_eq_thetaLarge_sub_smul`: the difference
  `thetaLarge Φ - c • thetaSmall Ψ` is a linear map of `Ψ` alone, on a `GL_n`-stable space, and is
  equivariant (`New.Exchange.IsEquivariantLift`).

Notions from other files:
* `thetaIntegral S T α β f`: the integral over `[U(T)]` of the theta kernel of the datum `f`.
* `thetaLarge W V 𝔠 v Φ`: the theta integral over `[U(V)]` of the datum `v ⊗ Φ`.
* `localChar P ξ k`: the character `t ↦ ξ t * |t| ^ (k / 2)` of the completions at `P`.
* `sameSectionPairs χ σ`: pairs `(Φ, Ψ)` of Schwartz–Bruhat functions on `a × n` and `n × b`
  matrices, `σ : b ⊕ a ≃ n`, whose values of `localSection χ` at the blocks of `k` differ by
  `χ (det k)`.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

@[expose] public section

namespace New.Exchange

open RingHom Matrix Pi WeilData SemilocalField Fintype SplitTameChar GeneralLinearGroup

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  {s : n → ℤˣ} {t : a → ℤˣ} {t' : b → ℤˣ} {μ : NumberField.InfinitePlace E → ℤ} (W : Space E n s)
  (V : Space E a t) (V' : Space E b t') (𝔠 : SplitTameChar E μ)

/-- The small side: the theta integral over `U(V)`, as a function on `U(W)`, of the datum with real
part `v` and component `y ↦ Ψ yᵀ`, read in the model at the conjugates of the ramified places of
`𝔠`. The two characters of `U(1)` are `ν υ ^ ⌊rk W / 2⌋` (`rankTwist`) and `υ ^ rk V`, where
`ν = 𝔠.character`. Here `υ` is the splitting character of the Weil data, restricted to the norm-one
ideles (`upsilonU1`). In the exchange identity it is applied to the space `V'`. -/
noncomputable abbrev thetaSmall
    (v : (Fock.isVacuum_realVac (ε := realSigns E (homSigns s t))).Model)
    (Ψ : Matrix n a (LocProd 𝔠.ramifiedPlaces) → ℂ) : G E s → ℂ :=
  thetaIntegral W V (rankTwist 𝔠.character n) (upsilonU1 ^ card a)
    (localDatum W V v (fun y : Matrix a n (LocProd 𝔠.ramifiedPlaces) ↦ Ψ yᵀ) 𝔠.readsAt.star)

/-- Polynomial growth of the theta kernel on `U(W)`, uniform on `U(V)` (`IsTargetBounded`), is kept
when the datum is moved by an element `k` of `U(V)`. -/
lemma IsTargetBounded.pairWeil_one_left {W : Space E n s} {V : Space E a t} {f : 𝒮 (W.hom V)}
    (hf : IsTargetBounded W V f) (α β : AutChar E) (k : G E t) :
    IsTargetBounded W V (pairWeil W V α β (1, k) f) := by
  obtain ⟨B, C, h_bound⟩ := hf
  refine ⟨B, C, fun α' β' g h ↦ ?_⟩
  -- the kernel at `(g, h)` becomes the kernel at `(g, h * k)`, times a scalar of modulus `1`
  have h_norm : ‖pairTheta W V α' β' (pairWeil W V α β (1, k) f) (g, h)‖ =
      ‖pairTheta W V α' β' f (g, h * k)‖ := by
    simp [pairTheta, pairWeil, rep_apply_apply, ← map_mul, Circle.norm_coe]
  exact h_norm.trans_le (h_bound α' β' g (h * k))

/-- The theta integral is homogeneous in the datum. -/
lemma thetaIntegral_smul (α β : AutChar E) (c : ℂ) (f : 𝒮 (W.hom V)) (x : G E s) :
    thetaIntegral W V α β (c • f) x = c * thetaIntegral W V α β f x := by
  simp [thetaIntegral, pairTheta, MeasureTheory.integral_const_mul]

/-- Let `π` be a ring map from the finite adeles of the CM field `E` to `F` that reads the
components at a set `A` of places (`ReadsAt`): `A` is disjoint from its conjugate, `π` has a
continuous additive section onto the `A`-part, and `π x` is integral exactly if `x` is so at `A`.
Let `φ` be Schwartz–Bruhat, vanishing outside some set `U`, and let `g ∈ U(W)`, `h ∈ U(V)` be finite
points supported on `A` and its conjugate. In the Weil representation (`pairWeil`), `(g, h)` moves
the datum of `φ` to that of `x ↦ φ (π h⁻¹ * x * π g)`. Here the datum (`localDatum`) is the vector
`v` of the Fock space `PairFock` at the infinite places, `φ` at `A` and the vacuum elsewhere. The
new datum is multiplied by `χ_W (det h) / χ_V (det g) * |det g| ^ (rk V / 2) / |det h| ^ (rk
W / 2)`. The determinants are taken on `A` (`detOn`) and `|·|` is `ideleAbs`.
`χ_W = α.spaceChar (rk W)` and `χ_V = β.spaceChar (rk V)`. -/
lemma ReadsAt.pairWeil_localDatum_of_mem_supportedOn {F : Type} [SemilocalField F]
    {A : Set (FinPlace E)} {π : 𝔸f E →+* F} (hπ : ReadsAt A π) (α β : AutChar E)
    (v : PairFock E s t) {U : Set (Matrix a n F)} {φ : Matrix a n F → ℂ}
    (hφ : φ ∈ schwartzBruhat U) {g : Gf E n} {h : Gf E a} (hg : g ∈ Gf.supportedOn n A)
    (hh : h ∈ Gf.supportedOn a A) :
    pairWeil W V α β ((1, g), 1, h) (localDatum W V v φ hπ) =
      ((α.spaceChar (card n)).val (detOn A h.val) / (β.spaceChar (card a)).val (detOn A g.val) *
          √(ideleAbs (detOn A g.val)) ^ card a / √(ideleAbs (detOn A h.val)) ^ card n : ℂ) •
        localDatum W V v
        (fun x : Matrix a n F ↦ φ (h⁻¹.val.val.map π * x * g.val.val.map π)) hπ := by
  rw [pairWeil_integrated_fin, pairWeil_schrodingerOp_of_mem_supportedOn hπ.disjoint_star
    (hΨ := hπ.isSchwartzBruhat hφ) hg hh]
  simp

/-- Let `𝔠` be a split tame character: a character `ν = 𝔠.character` of the norm-one ideles, tamely
ramified exactly at a finite set `S = 𝔠.ramifiedPlaces` of places disjoint from its conjugate. Let
`rk W` be even and let `k ∈ U(V)` be finite (`Gf`), supported at `S` and its conjugate, with
component `k_S` at `S`. Consider the datum `localDatum W V v Φ 𝔠.readsAt`: `v` at the infinite
places, the function `Φ` at `S` and the vacuum elsewhere. It lies in the Weil representation
`pairWeil` of `(W, V)` with both characters `ν⁻¹ υ ^ ⌊rk W / 2⌋` (`rankTwist`), `υ` being the
splitting character of the Weil data. Then `k⁻¹` moves it to the same datum with `x ↦ Φ (k_S * x)`
in place of `Φ`, times the value at `det k_S` of `t ↦ ν (t / t̄) |t| ^ (rk W / 2)` (`localChar`).
Here `Φ` is Schwartz–Bruhat on the matrices `x` of full row rank. -/
lemma pairWeil_inv_localDatum (hn : 2 ∣ card n) (v : PairFock E s t)
    {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ} (hΦ : Φ ∈ schwartzBruhat {x | HasLeftInv xᵀ})
    {k : Gf E a} (hk : k ∈ Gf.supportedOn a 𝔠.ramifiedPlaces) :
    pairWeil W V (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n) ((1, 1), 1, k⁻¹)
        (localDatum W V v Φ 𝔠.readsAt) =
      localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
        (atPlaces 𝔠.ramifiedPlaces k).val.det •
        localDatum W V v (fun x ↦ Φ ((atPlaces 𝔠.ramifiedPlaces k).val * x)) 𝔠.readsAt := by
  rw [𝔠.readsAt.pairWeil_localDatum_of_mem_supportedOn W V _ _ v hΦ (one_mem _) (inv_mem hk)]
  simp [spaceChar_rankTwist hn, atPlaces_star]

/-- Let `𝔠` be a split tame character, with character `ν` of the norm-one ideles and finite set `S`
of ramified places. Let `rk W = card b + rk V` (`σ`) be even, and let `χ` be the character
`t ↦ ν (t / t̄) |t| ^ (rk W / 2)` at `S` (`localChar`). Let `(Φ, Ψ)` be a same-section pair for `χ`
and `σ`: both are Schwartz–Bruhat on matrices of full rank, and for each invertible `k` the coset
sum `localSection χ` of `y ↦ Φ yᵀ` at the transposed rows `a` of `k⁻¹` is `χ (det k)` times that of
`Ψ` at the columns `b` of `k`. By `thetaLarge W V 𝔠 v Φ` is meant the function on `U(W)` that
integrates over `[U(V)]` the theta kernel of the datum `v` at the infinite places, `Φ` at `S`, the
vacuum elsewhere, both characters being `ν⁻¹ υ ^ ⌊rk W / 2⌋` for the splitting character `υ` of the
Weil data. Let `g ∈ U(W)` be finite, supported at `S` and its conjugate, with component `g_S` at
`S`. Then `thetaLarge` of `y ↦ χ (det g_S⁻¹) Φ (y g_S⁻¹)` at `x g` is that of `Φ` at `x` divided by
`(υ |·| ^ (1 / 2)) (det g_S) ^ card b`. -/
lemma thetaLarge_translate_mul (σ : b ⊕ a ≃ n) (hn : 2 ∣ card n) (v : PairFock E s t)
    {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ} {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hp : (Φ, Ψ) ∈ sameSectionPairs (localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)) σ)
    {g : Gf E n} (hg : g ∈ Gf.supportedOn n 𝔠.ramifiedPlaces) (x : G E s) :
    thetaLarge W V 𝔠 v
        (localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
          (atPlaces 𝔠.ramifiedPlaces g⁻¹).val.det •
          fun y : Matrix a n (LocProd 𝔠.ramifiedPlaces) ↦
            Φ (y * (atPlaces 𝔠.ramifiedPlaces g⁻¹).val)) (x * (1, g)) =
      thetaLarge W V 𝔠 v Φ x / localChar 𝔠.ramifiedPlaces υ 1 (atPlaces 𝔠.ramifiedPlaces g).val.det
        ^ card b := by
  obtain ⟨⟨h_sb, -⟩, -⟩ := sameSectionPairs.translate_mem _ σ hp (atPlaces 𝔠.ramifiedPlaces g⁻¹)
  have h_char : (rankTwist 𝔠.character⁻¹ n).spaceChar (card a) = 𝔠.character⁻¹.baseChange * υ ^ card
    b := by
    rw [← spaceChar_rankTwist (n := n) hn]
    simp [AutChar.spaceChar, ← card_congr σ, pow_add, mul_assoc, mul_comm (υ ^ card a)⁻¹]
  -- `pairWeil` undoes the translation; its scalar combines with the factor `χ (det g_S⁻¹)`
  let d : (𝔸 E)ˣ := detOn 𝔠.ramifiedPlaces g.val
  have h_scalar : (((𝔠.character⁻¹.baseChange * υ ^ card b).val d : ℂ)⁻¹ * √(ideleAbs d) ^ card a) *
      localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
        (atPlaces 𝔠.ramifiedPlaces g⁻¹).val.det =
        (localChar 𝔠.ramifiedPlaces υ 1 (atPlaces 𝔠.ramifiedPlaces g).val.det ^ card b)⁻¹ := by
    rw [localChar_det, localChar_det, ← card_congr σ]
    simp [mul_pow, zpow_add₀, field]
  rw [thetaLarge, ← thetaIntegral_pairWeil ((1, g), 1, 1),
    𝔠.readsAt.pairWeil_localDatum_of_mem_supportedOn W V _ _ v h_sb hg (one_mem _), h_char,
    div_eq_inv_mul (thetaLarge W V 𝔠 v Φ x), ← h_scalar, ← thetaIntegral_smul, mul_smul]
  simp [d, localDatum, atPlaces_star, ← Pi.smul_def, -smul_eq_mul, -localChar_det]

/-- By `thetaSmall W V' 𝔠 v' Ψ` is meant the function on `U(W)` that integrates over `[U(V')]` the
theta kernel of the datum `v'` at the infinite places and `y ↦ Ψ yᵀ` at the conjugates of the
ramified places `S` of `𝔠`; the space `V'` has rank `card b`. Let `g ∈ U(W)` be finite, supported at
`S` and its conjugate, with component `g_S` at `S`. If `y ↦ Ψ (g_S y)` is Schwartz–Bruhat, its
`thetaSmall` at `x g` is `thetaSmall Ψ` at `x` divided by `(υ |·| ^ (1 / 2)) (det g_S) ^ card b`,
where `υ` is the splitting Hecke character of the Weil data. -/
lemma thetaSmall_translate_mul (v' : PairFock E s t')
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {g : Gf E n} (hg : g ∈ Gf.supportedOn n 𝔠.ramifiedPlaces)
    (hΨ : (fun y : Matrix n b (LocProd 𝔠.ramifiedPlaces) ↦
      Ψ ((atPlaces 𝔠.ramifiedPlaces g).val * y)) ∈
      schwartzBruhat {y | HasLeftInv y}) (x : G E s) :
    thetaSmall W V' 𝔠 v' (fun y ↦ Ψ ((atPlaces 𝔠.ramifiedPlaces g).val * y)) (x * (1, g)) =
      thetaSmall W V' 𝔠 v' Ψ x / localChar 𝔠.ramifiedPlaces υ 1
        (atPlaces 𝔠.ramifiedPlaces g).val.det ^ card b := by
  have hg_star : g ∈ Gf.supportedOn n (star ⁻¹' (𝔠.ramifiedPlaces : Set (FinPlace E))) := by
    simp +contextual [Gf.mem_supportedOn.1 hg]
  -- `pairWeil` undoes the translation, up to a scalar in the determinant `d̄⁻¹` on the conjugates
  let d : (𝔸 E)ˣ := detOn 𝔠.ramifiedPlaces g.val
  have h_scalar : (((upsilonU1 ^ card b : AutChar E).spaceChar (card b)).val (star d⁻¹) : ℂ)⁻¹ *
      √(ideleAbs (star d⁻¹)) ^ card b =
        (localChar 𝔠.ramifiedPlaces υ 1 (atPlaces 𝔠.ramifiedPlaces g).val.det ^ card b)⁻¹ := by
    simp [AutChar.spaceChar, υ_star, sq, mul_pow, field]
  rw [thetaSmall, ← thetaIntegral_pairWeil ((1, g), 1, 1),
    𝔠.readsAt.star.pairWeil_localDatum_of_mem_supportedOn W V' _ _ v'
      hΨ.transpose_mem_schwartzBruhat hg_star (one_mem _),
    thetaIntegral_smul, detOn_preimage_star g, div_eq_inv_mul (thetaSmall W V' 𝔠 v' Ψ x),
      ← h_scalar]
  simp [d, thetaSmall, atPlaces_star, -coe_comp]

/-- For Schwartz–Bruhat `Φ`, `thetaLarge Φ` is right invariant under the integral points `k` of
`U(W)` that are trivial at the ramified places of `𝔠`. -/
lemma thetaLarge_mul_of_mem_stdLevel (v : PairFock E s t)
    {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat {x : Matrix a n (LocProd 𝔠.ramifiedPlaces) | HasLeftInv xᵀ})
    {k : Gf E n}
    (hk_int : k ∈ stdLevel E n) (hk_triv : k ∈ Gf.trivialOn n 𝔠.ramifiedPlaces) (x : G E s) :
    thetaLarge W V 𝔠 v Φ (x * (1, k)) = thetaLarge W V 𝔠 v Φ x := by
  have h_one : k.val.val.map (evalPlaces 𝔠.ramifiedPlaces) = 1 :=
    congrArg Units.val (atPlaces_eq_one_of_mem_trivialOn hk_triv)
  rw [thetaLarge, ← thetaIntegral_pairWeil ((1, k), 1, 1),
    𝔠.readsAt.pairWeil_localDatum_of_mem_stdLevel hΦ hk_int (one_mem _)]
  simp [rankTwist, character_detFin_eq_of_mem_stdLevel, atPlaces_eq_one_of_mem_trivialOn, h_one,
    hk_int, hk_triv]

/-- For Schwartz–Bruhat `Ψ`, `thetaSmall Ψ` is right invariant under the integral points `k` of
`U(W)` that are trivial at the ramified places of `𝔠`. -/
lemma thetaSmall_mul_of_mem_stdLevel (v' : PairFock E s t')
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhat {y | HasLeftInv y}) {k : Gf E n}
    (hk_int : k ∈ stdLevel E n) (hk_triv : k ∈ Gf.trivialOn n 𝔠.ramifiedPlaces) (x : G E s) :
    thetaSmall W V' 𝔠 v' Ψ (x * (1, k)) = thetaSmall W V' 𝔠 v' Ψ x := by
  rw [thetaSmall, ← thetaIntegral_pairWeil ((1, k), 1, 1),
    𝔠.readsAt.star.pairWeil_localDatum_of_mem_stdLevel hΨ.transpose_mem_schwartzBruhat hk_int
      (one_mem _)]
  simp [-coe_comp, rankTwist, character_detFin_eq_of_mem_stdLevel,
    atPlaces_eq_one_of_mem_trivialOn,
    atPlaces_star, hk_int, hk_triv]

/-- For `v'` with all moments finite, `thetaSmall` is linear on Schwartz–Bruhat functions. -/
lemma exists_linear_thetaSmall {v' : PairFock E s t'} (hv' : IsSchwartzVector v') :
    ∃ T : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ,
      ∀ Ψ ∈ schwartzBruhat {y | HasLeftInv y}, T Ψ = thetaSmall W V' 𝔠 v' Ψ := by
  -- `Λ` is linear and is the theta integral on data of polynomial growth
  obtain ⟨Λ, hΛ⟩ := exists_linear_thetaIntegral W V' (rankTwist 𝔠.character n) (upsilonU1 ^ card b)
  let D : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] 𝒮 (W.hom V') :=
    IsLinearMap.mk' (fun Ψ ↦ localDatum W V' v' (fun y ↦ Ψ yᵀ) 𝔠.readsAt.star)
      ⟨by simp [localDatum, ← add_def], by simp [localDatum, ← Pi.smul_def, -smul_eq_mul]⟩
  refine ⟨Λ ∘ₗ D, fun Ψ hΨ ↦ ?_⟩
  have h_bdd : IsTargetBounded W V' (localDatum W V' v' (fun y ↦ Ψ yᵀ) 𝔠.readsAt.star) :=
    𝔠.readsAt.star.isTargetBounded hv' hΨ.transpose_mem_schwartzBruhat
  rw [thetaSmall, ← hΛ h_bdd, LinearMap.comp_apply, IsLinearMap.mk'_apply]

/-- Let `rk W = rk V' + rk V` be even and `v` have all moments finite. Let `ν` be the character of
`𝔠`, `S` its ramified places, and let `thetaLarge W V 𝔠 v Φ` be the theta integral over `[U(V)]` of
the datum `v` at the infinite places and `Φ` at `S`, as a function on `U(W)`. A same-section pair
`(Φ, Ψ)` for `χ t = ν (t / t̄) |t| ^ (rk W / 2)` consists of Schwartz–Bruhat functions on `a × n`
and `n × b` matrices at `S` whose coset sums `localSection χ` at complementary blocks of each
invertible `k` differ by the factor `χ (det k)`. On these pairs `thetaLarge Φ` is a linear function
of `Ψ`. -/
lemma exists_linear_thetaLarge (σ : b ⊕ a ≃ n) (hn : 2 ∣ card n) {v : PairFock E s t}
    (hv : IsSchwartzVector v) :
    ∃ T : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ,
      ∀ (Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
        (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
        (Φ, Ψ) ∈ sameSectionPairs (localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)) σ →
          T Ψ = thetaLarge W V 𝔠 v Φ := by
  let ρ : AutChar E := rankTwist 𝔠.character⁻¹ n
  -- `Λ` is linear and is the theta integral on data of polynomial growth
  obtain ⟨Λ, hΛ⟩ := exists_linear_thetaIntegral W V ρ ρ
  let D : (Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] 𝒮 (W.hom V) :=
    IsLinearMap.mk' (localDatum W V v · 𝔠.readsAt)
      ⟨by simp [localDatum, ← add_def], by simp [localDatum, ← Pi.smul_def, -smul_eq_mul]⟩
  -- the theta integral does not see the action of `U(V)` on the datum
  have h_invariant (g : GL a (LocProd 𝔠.ramifiedPlaces))
      (Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (hΦ : Φ ∈ schwartzBruhat {x | HasLeftInv xᵀ}) :
      localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n) g.val.det • Λ
        (D fun x ↦ Φ (g.val * x)) = Λ (D Φ) := by
    obtain ⟨k, hk, rfl⟩ := 𝔠.exists_atPlaces_eq g
    have h_bdd : IsTargetBounded W V (D Φ) := 𝔠.readsAt.isTargetBounded hv hΦ
    have h_move : pairWeil W V ρ ρ ((1, 1), 1, k⁻¹) (D Φ) =
        localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
          (atPlaces 𝔠.ramifiedPlaces k).val.det •
          D fun x ↦ Φ ((atPlaces 𝔠.ramifiedPlaces k).val * x) :=
            pairWeil_inv_localDatum W V 𝔠 hn v hΦ hk
    ext x
    rw [← map_smul, ← h_move, hΛ h_bdd, Prod.mk_one_one,
      hΛ (h_bdd.pairWeil_one_left ρ ρ (1, k⁻¹)), thetaIntegral_pairWeil, mul_one]
  -- so `Λ (D Φ) = T Ψ` on same-section pairs, for a linear `T`
  obtain ⟨T, hT⟩ := sameSectionPairs.exists_linear_factor _ σ (Λ ∘ₗ D) h_invariant
  refine ⟨T, fun Φ Ψ hp ↦ (hT Φ Ψ hp).trans (hΛ ?_)⟩
  obtain ⟨⟨h_sb, -⟩, -⟩ := hp
  exact 𝔠.readsAt.isTargetBounded hv h_sb

/-- Let `𝔠` be a split tame character, with character `ν` of the norm-one ideles and finite set `S`
of ramified places, and let `υ` be the splitting Hecke character of the Weil data. Let
`rk W = rk V' + rk V` be even, `v`, `v'` real data with all moments finite, `c ∈ ℂ`. There are a
space `M` of functions on matrices at `S` and a linear map `𝒟` with (a) and (b). (a) `M` consists of
Schwartz–Bruhat functions and is stable under translation. `𝒟` maps `M` to automorphic functions on
`U(W)`. It is equivariant at `S` for the inverse of `υ ^ card b |·| ^ (card b / 2)` of the
determinant. It is invariant under the integral points elsewhere (`IsEquivariantLift`). (b) Let `Ψ`
be locally constant with a matched function `Φ`: both are supported on blocks of integral invertible
`k`, where their values differ by `𝔠.semilocalChar (det k)`, for the character
`𝔠.semilocalChar : t ↦ ν (t / t̄)` at `S`. Then `Ψ` lies in `M`, and
`𝒟 Ψ = thetaLarge Φ - c • thetaSmall Ψ`. -/
lemma exists_isEquivariantLift_eq_thetaLarge_sub_smul (σ : b ⊕ a ≃ n) (hn : 2 ∣ card n)
    {v : PairFock E s t}
    {v' : PairFock E s t'} (hv : IsSchwartzVector v) (hv' : IsSchwartzVector v') (c : ℂ) :
    ∃ (M : Submodule ℂ (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ))
      (𝒟 : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ),
      -- (a) `𝒟` is an equivariant map from `M` to automorphic functions
      IsEquivariantLift 𝔠 W M 𝒟 ∧
      -- (b) on the second member of a pair of matched functions it is the difference of the two
      -- sides
      ∀ {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
        {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ},
        IsLocallyConstant Ψ → AreMatched O σ 𝔠.semilocalChar Φ Ψ →
          Ψ ∈ M ∧ 𝒟 Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W V' 𝔠 v' Ψ := by
  -- Let `M` be the space of second members of same-section pairs `(Φ, Ψ)`. The theta integral of
  -- `Φ` for `V` depends only on `Ψ`, linearly; subtract `c` times the theta integral of `Ψ` for
  -- `V'`. The laws of `IsEquivariantLift` hold for each of the two integrals.
  let χ : MulChar (LocProd 𝔠.ramifiedPlaces) ℂ :=
    localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
  obtain ⟨T, hT⟩ := exists_linear_thetaLarge W V 𝔠 σ hn hv
  obtain ⟨T', hT'⟩ := exists_linear_thetaSmall W V' 𝔠 hv'
  have h_sb {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
      (hp : (Φ, Ψ) ∈ sameSectionPairs χ σ) : (Φ ∈ schwartzBruhat {x | HasLeftInv xᵀ}) ∧
        Ψ ∈ schwartzBruhat {y | HasLeftInv y} := (Submodule.mem_inf.1 hp).1
  have h_diff {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
      (hp : (Φ, Ψ) ∈ sameSectionPairs χ σ) :
      (T - c • T') Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W V' 𝔠 v' Ψ := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hT Φ Ψ hp, hT' Ψ (h_sb hp).right]
  refine ⟨(sameSectionPairs χ σ).map (.snd ℂ _ _), T - c • T', ⟨?_, ?_, ?_, ?_⟩,
    fun {Φ Ψ} hΨ ⟨h_left, h_right, h_eq⟩ ↦ ?_⟩
  · rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩
    exact (h_sb hp).right
  · -- both theta integrals are automorphic
    rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩
    obtain ⟨h_cont, h_inv⟩ : IsAutFunction W (thetaLarge W V 𝔠 v Φ) :=
      (𝔠.readsAt.isTargetBounded hv (h_sb hp).left).isAutFunction_thetaIntegral
    obtain ⟨h_cont', h_inv'⟩ : IsAutFunction W (thetaSmall W V' 𝔠 v' Ψ) :=
      (𝔠.readsAt.star.isTargetBounded hv'
        (h_sb hp).right.transpose_mem_schwartzBruhat).isAutFunction_thetaIntegral
    rw [LinearMap.snd_apply, h_diff hp]
    exact ⟨by fun_prop, fun γ hγ x ↦ by simp [h_inv γ hγ x, h_inv' γ hγ x]⟩
  · -- the translate of a same-section pair by the inverse of the component of `g` at
    -- `𝔠.ramifiedPlaces` is again a same-section pair
    rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩ g hg
    have hq : (χ (atPlaces 𝔠.ramifiedPlaces g⁻¹).val.det • fun x ↦
      Φ (x * (atPlaces 𝔠.ramifiedPlaces g⁻¹).val),
        fun y ↦ Ψ ((atPlaces 𝔠.ramifiedPlaces g).val * y)) ∈ sameSectionPairs χ σ := by
      simpa only [map_inv (atPlaces 𝔠.ramifiedPlaces), inv_inv] using
        sameSectionPairs.translate_mem χ σ hp (atPlaces 𝔠.ramifiedPlaces g⁻¹)
    refine ⟨⟨_, hq, rfl⟩, fun x ↦ ?_⟩
    simp only [LinearMap.snd_apply, h_diff hp, h_diff hq, Pi.sub_apply, Pi.smul_apply]
    rw [thetaSmall_translate_mul W V' 𝔠 v' hg (h_sb hq).right,
      thetaLarge_translate_mul W V 𝔠 σ hn v hp hg, sub_div, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  · rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩ k ⟨hk_int, hk_triv⟩ x
    simp only [LinearMap.snd_apply, h_diff hp, Pi.sub_apply, Pi.smul_apply]
    rw [thetaLarge_mul_of_mem_stdLevel W V 𝔠 v (h_sb hp).left hk_int hk_triv,
      thetaSmall_mul_of_mem_stdLevel W V' 𝔠 v' (h_sb hp).right hk_int hk_triv]
  · -- matched functions form a same-section pair: on integral units the factor `|·| ^ (n / 2)` of
    -- `χ` is `1`
    have h_char (k : GL n (LocProd 𝔠.ramifiedPlaces)) (hk : k ∈ intGL n O) :
      χ k.val.det = 𝔠.semilocalChar k.val.det := by
      obtain ⟨k, rfl⟩ := hk
      simp only [χ, ← val_det_apply, GeneralLinearGroup.map_det]
      simp [localChar_apply_of_isUnit]
    have h_match : (Φ, Ψ) ∈ sameSectionPairs χ σ :=
      AreMatched.mem_sameSectionPairs (𝔠.tameLocalChar _)
      ⟨h_left, h_right, fun k hk ↦ by rw [h_eq k hk, h_char k hk]⟩ hΨ
    exact ⟨⟨_, h_match, rfl⟩, h_diff h_match⟩

end New.Exchange
end
end

/-!
# Parabolic theta terms, equal ranks, and the exchange identity for the large triple

The theta kernel of the dual pair (U(X), U(V)) is unfolded along a splitting of X over W₁ with an
isotropic frame. It becomes a sum of terms `New.Space.Splitting.thetaTerm` indexed by rational
matrices. Take a standard datum v ⊗ Φ, with v real and Φ an explicit function at the finite places
A. Its terms are computed at points n(c, z) m(q, g) of the parabolic subgroup. They are expressed
through the theta functional `New.Exchange.thetaOnRealData` of the smaller pair (W₁, V). For
V = V' ⊕ W₁ this functional factors as a product. Let `𝔠` be a tamely ramified character,
`V = V' ⊕ W₁`, and `X` equal to `W₁` plus a hyperbolic space. Then the identity between the theta
integrals `New.Exchange.thetaLarge` and `New.Exchange.thetaSmall` for standard data follows from an
identity of periods over `[U W₁]`, under conditions on the rank of `W₁`, the signs and the data,
when `W₁` splits off a hyperbolic plane.

## Main definitions and results

* `New.Exchange.thetaTerm_eq_and_centreCoeff_eq_zero`: the terms are integrable
  (`hasIntegrableTerms_localDatum_of_eq_stdDatum`), each is an explicit factor times a value of
  `New.Exchange.thetaOnRealData` (`thetaTerm_localDatum_of_eq_stdDatum`), and the Fourier
  coefficient of the theta integral at `j • T` (`j` the purely imaginary element of the Weil data)
  vanishes if some signs represent the Gram matrices of all points with non-zero real slice but do
  not represent the matrix T (`centreCoeff_thetaIntegral_localDatum_eq_zero`).
* `New.Exchange.thetaOnRealData_boxProd_eq_mul`: on a product of real data, the functional of the
  datum built from a vector for (W₁, V') and a vector for (W₁, W₁) is the one for (W₁, V') times the
  theta kernel `New.pairTheta` of the pair (W₁, W₁).
* `New.Exchange.thetaLarge_eq_apply_one_of_even_rank`: if `W₁` has even rank and splits off a
  hyperbolic plane, the theta integral of `(W₁, W₁)` on the datum `χ⁻¹ ∘ det` is constant.
* `New.Exchange.RowColExchangeIdentity`: the two theta integrals are proportional on the standard
  data `New.stdRowDatum` and `New.stdColDatum`, with a condition on the size of the factor.
* `New.Exchange.IsPeriodIdentity`: the identity of periods over `[U W₁]` between real slices.
* `New.Exchange.exists_thetaLarge_eq_smul_of_isPeriodIdentity`,
  `New.Exchange.rowColExchangeIdentity_of_periods`: the identity for `V = V' ⊕ W₁`, where `X` is
  `W₁` plus a hyperbolic space, follows from an identity of periods over `[U W₁]`, for one character
  and for all characters, when `W₁` splits off a hyperbolic plane.

Notions from other files:
* `New.Space.integrated`: the bounded bilinear map (v, f) ↦ v ⊗ f = ∫ v(y) ϱ(y)f dy, for v in the
  Fock space, f in 𝒮(V), y over real vectors in Fock coordinates.
* `New.Exchange.IntegralFrame.stdDatum`: for a frame with blocks K, I, L and a function G, the
  function y ↦ G(y (K|I)) on integral y, and 0 elsewhere.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

@[expose] public section

/-!
## Terms of a standard datum at a point of the parabolic subgroup

`New.Exchange.namedVector` is the vector given by a function at the places A, read through π
(`New.Exchange.ReadsAt`), and the vacuum elsewhere. `New.Exchange.realSlice` is the slice of a real
datum for (X, V) at a point of Hom(isotropic frame, V), a real datum for (W₁, V).
-/

namespace New.Exchange

open Matrix WeilData MeasureTheory Space Splitting Fintype Prod SemilocalField

variable {E : Type} [Field E] [CMType E] [WeilData E] {n a b m : Type} [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m] {s : n → ℤˣ}
  {t : a → ℤˣ} {r : m → ℤˣ} {X : Space E m r} (W₁ : Space E n s) (D : X.Splitting W₁ b)
  (V : Space E a t)

/-- The functional v ↦ θ(ϱ(x) ω_{α,γ}(p) (v ⊗ F)) on real data v of the pair (W₁, V): the value of
the theta distribution θ at the Schwartz vector with real part v and
finite part given by a vector F, moved first by the Weil representation ω_{α,γ} = `pairWeil` with
characters α, γ at a point p of U(W₁) × U(V) and then by the Heisenberg translation ϱ by an adelic
matrix x. -/
noncomputable def thetaOnRealData (α γ : AutChar E) (F : 𝒮 (W₁.hom V)) (x : Matrix a n (𝔸 E))
    (p : G E s × G E t) :
    Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns s t))) →L[ℂ] ℂ :=
  θ (W₁.hom V) ∘L ϱ (W₁.hom V) (matrixToVec x) ∘L pairWeil W₁ V α γ p ∘L
    (integrated (W₁.hom V)).flip F

omit [WeilData E] in
/-- If at every infinite place `qᴴ T q` has the form `yᴴ diag(t') y` for some matrix `y`
(`RepresentedBy`), with `q` invertible, then so has `T`. -/
lemma RepresentedBy.of_conjTranspose_mul_mul {t' : b → ℤˣ} {T : Matrix b b (𝔸 E)} (q : GL b (𝔸 E))
    (h_rep : RepresentedBy t' (q.valᴴ * T * q.val)) : RepresentedBy t' T := by
  intro u
  obtain ⟨y, hy⟩ : ∃ y : Matrix b b ℂ,
      yᴴ * signMatrix t' * y = atRealPlace (q.valᴴ * T * q.val) u := h_rep u
  have h_inv : q⁻¹.valᴴ * (q.valᴴ * T * q.val) * q⁻¹.val = T := gram_inv_of_gram_eq rfl
  refine ⟨y * atRealPlace q⁻¹.val u, ?_⟩
  calc (y * atRealPlace q⁻¹.val u)ᴴ * signMatrix t' * (y * atRealPlace q⁻¹.val u)
      = (atRealPlace q⁻¹.val u)ᴴ * atRealPlace (q.valᴴ * T * q.val) u * atRealPlace q⁻¹.val u := by
        rw [gram_mul, hy]
    _ = (q⁻¹.valᴴ * (q.valᴴ * T * q.val) * q⁻¹.val).map (evalInf u) := by
        rw [Matrix.map_mul, Matrix.map_mul]
        rfl
    _ = atRealPlace T u := congrArg (fun M ↦ M.map (evalInf u)) h_inv

variable {W₁} in
/-- The real slice of `v` along `D` vanishes at every adelic matrix `x` whose Gram matrix for the
standard form with signs `t` is not represented by the signs `t'` at the infinite places. -/
def SlicesVanishOutside [IsBaseAdapted D] (t' : b → ℤˣ) (v : PairFock E r t) : Prop :=
  ∀ x : Matrix a b (𝔸 E), realSlice D V x v ≠ 0 → RepresentedBy t' (xᴴ * stdForm E t * x)

/-- Let the splitting `D` write `X` as `W₁` plus the spans of two dual isotropic frames; `D.k` is
one of the frames and `D.i` the embedding of `W₁`, as matrices over `E`, and `D.kAdelic`,
`D.iAdelic` are the same in the standard coordinates over the adeles. The point
`p = n(c, z) m(q, g)` of the parabolic subgroup of `D` maps the span of `(k | i)` to itself: the
coordinates `p⁻¹ X.x⁻¹ (k | i)` at `p`, times a block triangular matrix, give
`(D.kAdelic | D.iAdelic)`. Here `X.x` and `W₁.x` carry the forms of `X` and `W₁` to the standard
forms. -/
lemma coordMatrix_mul_fromBlocks_eq_fromCols (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E))
    (q : GL b (𝔸 E)) (g : G E s) :
    X.coordMatrix (D.radicalElement c z * D.levi (q, g)) (D.k.fromCols D.i) *
        fromBlocks q.val (cᴴ * stdForm E s * g.adeleMatrix) 0 (W₁.x.val * g.adeleMatrix) =
      D.kAdelic.fromCols D.iAdelic := by
  set p : G E r := D.radicalElement c z * D.levi (q, g)
  -- the frame times the triangular matrix is the image of the frame under `p`
  have h_image : X.x⁻¹.val * (D.k.fromCols D.i).map toAdele *
      fromBlocks q.val (cᴴ * stdForm E s * g.adeleMatrix) 0 (W₁.x.val * g.adeleMatrix) =
        p.adeleMatrix * D.kAdelic.fromCols D.iAdelic := by
    trans fromCols (D.kAdelic * q.val)
      (D.iAdelic * g.adeleMatrix + D.kAdelic * (cᴴ * stdForm E s * g.adeleMatrix))
    · simp [kAdelic, iAdelic, Space.ratMap, fromCols_map, fromCols_mul_fromBlocks,
        Matrix.mul_assoc, add_comm]
    · simp [p, G.adeleMatrix, G.ofMatrix, radicalElement, Splitting.levi, ↓mul_fromCols,
        Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul]
  rw [coordMatrix, Matrix.mul_assoc, h_image, ← Matrix.mul_assoc]
  simp [G.adeleMatrix]

section StandardDatum

variable {P : Finset (FinPlace E)} {A : Set (FinPlace E)} {π : 𝔸f E →+* LocProd P}
  [Nontrivial (LocProd P)] [IsBaseAdapted D] {Φ : Matrix a m (LocProd P) → ℂ}
  {Ω : Set (Matrix a m (LocProd P))} {v : PairFock E r t} {χ : MulChar (LocProd P) ℂ} {ε : ℂ}
  {N : Matrix (b ⊕ n) a (LocProd P)}

/-- Let D split X as W₁ plus a hyperbolic space with isotropic frame of size b. Let π map the finite
adeles onto the product `LocProd P` of the fields at a finite set P of places, reading the
components at the places A (`ReadsAt`), with O its subring of integral elements, and let (K I L) be
the image of the frame of D. Let v be a real Schwartz vector and
Φ(y) = ε 1_O(y) χ⁻¹(det (y (K|I) N)), for a number ε, a character χ and a fixed matrix N, be
Schwartz–Bruhat with support in a set Ω; here χ⁻¹ is `invOnUnits χ`, zero off the units of O. Then,
for any characters β, γ of the norm-one ideles in the Weil representation, the terms of the theta
kernel of v ⊗ Φ (vacuum at the other finite places) at n(c, z) m(q, g) are integrable over
[U(V)]. -/
lemma hasIntegrableTerms_localDatum_of_eq_stdDatum (hπ : ReadsAt A π) (β γ : AutChar E)
    (hΦ : Φ ∈ schwartzBruhat Ω)
    (hΦ_std : Φ = (adaptedFrame hπ D).stdDatum fun y : Matrix a (b ⊕ n) (LocProd P) ↦
      ε * invOnUnits χ (y * N).det)
    (hv : IsSchwartzVector v) (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (q : GL b (𝔸 E))
    (g : G E s) :
    D.HasIntegrableTerms V β γ (localDatum X V v Φ hπ)
      (D.radicalElement c z * D.levi (q, g)) := by
  -- `hasIntegrableTerms_integrated_schrodingerOp` asks that `y` times the frame `(k | i)` moved by
  -- the inverse of the point be right invertible (after `π`) where `Φ` is non-zero; there
  -- `det (y (K | I) N)` is a unit
  refine D.hasIntegrableTerms_integrated_schrodingerOp V β γ hπ.disjoint_star
    (hπ.isSchwartzBruhat hΦ) π hv fun y hy ↦ ?_
  let M : Matrix a a (LocProd P) :=
    (vecToMatrix y).map π * (D.kAdelic.fromCols D.iAdelic).map (π.comp (RingHom.snd _ _)) * N
  obtain ⟨-, d, -, h_det⟩ : IsIntegralUnit M.det := by
    refine by_contra fun h_not ↦ hy ?_
    simp only [M, fromCols_map] at h_not
    simp only [hΦ_std, IntegralFrame.stdDatum, invOnUnits, adaptedFrame, ite_eq_right h_not,
      mul_zero, ite_self]
  have h_inv : M * M⁻¹ = 1 := mul_nonsing_inv M (.of_mul_eq_one_right d h_det)
  -- the frame at the point enters `M`, so the right inverse is a triangular matrix times `N M⁻¹`
  simp only [M, ← coordMatrix_mul_fromBlocks_eq_fromCols W₁ D c z q g, Matrix.map_mul] at h_inv
  exact ⟨_, by simpa [← Matrix.mul_assoc] using congrArg transpose h_inv⟩

open scoped Classical in
omit [Nontrivial (LocProd P)] in
/-- Let π read the components at the places A, with O the integral elements of its target, let (K I
L) be the local frame adapted to D, and let Φ(y) = ε 1_O(y) χ⁻¹(det (y (K|I) N)), for a number ε, a
character χ and a fixed matrix N, be Schwartz–Bruhat with support in a set Ω; here χ⁻¹ is
`invOnUnits χ`, zero off the units of O. Let x' be the standard coordinates of a rational matrix x,
and x' q = `scaleIdele E` • Y, with `scaleIdele E` the normalising idele of the Weil data. Let υ be
the splitting Hecke character of the Weil data and `upsilonU1` its restriction to the norm-one
ideles, and put β' = β `upsilonU1`^b, where b is the size of the isotropic frame. At the point
(`D.radicalElement c z * D.levi (q, g)`, k), the term of x in the theta kernel of v ⊗ Φ with
characters β' and γ is the product of ψ(½ tr(z xᴴJx)) χ_V(det q)⁻¹ |det q|^(a/2), where J = `V.J` is
the form of V, a is the rank of V and χ_V = `γ.spaceChar a` is the Hecke character u ↦ γ(u/ū)
υ(u)^(-a);
* `vacuumFactor`, the non-zero constant in the formula for the slices of the vacuum, if y, the
finite part of k⁻¹Y, is integral, and 0 otherwise;
* `thetaOnRealData`, the theta functional θ(ϱ(translation) ω_{β,γ}(g, k) (· ⊗ finite vector)) of the
pair (W₁, V), at the translation x' cᴴ J_s (J_s the standard form of W₁), for the finite vector that
is the slice of Φ at y at the places A and the vacuum elsewhere (`namedVector`), evaluated at the
real slice of v at k⁻¹Y (`realSlice`: v restricted to the maps sending the isotropic frame `D.k` to
k⁻¹Y). -/
lemma thetaTerm_localDatum_of_eq_stdDatum (hπ : ReadsAt A π) {β β' : AutChar E} (γ : AutChar E)
    (hΦ : Φ ∈ schwartzBruhat Ω)
    (hΦ_std : Φ = (adaptedFrame hπ D).stdDatum fun y : Matrix a (b ⊕ n) (LocProd P) ↦
      ε * invOnUnits χ (y * N).det)
    (hβ' : β' = β * upsilonU1 ^ card b) (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E))
    {q : GL b (𝔸 E)} (g : G E s) {x : Matrix a b E} {x' Y : Matrix a b (𝔸 E)}
    (hx : V.x⁻¹.val * x.map toAdele = x') (hY : x' * q.val = scaleIdele E • Y) (k : G E t) :
    let y : Matrix a b (𝔸f E) := (k⁻¹.adeleMatrix * Y).map Prod.snd
    D.thetaTerm V β' γ (localDatum X V v Φ hπ) (D.radicalElement c z * D.levi (q, g)) x k =
      stdAddChar E (toAdele 2⁻¹ * (z * (xᴴ * V.J * x).map toAdele).trace) *
        (((γ.spaceChar (card a)).val q.det : ℂ)⁻¹ * √(ideleAbs q.det) ^ card a *
          ((if IsIntMatrix (Ô E) y then (vacuumFactor (isAdapted_homSource D V)).val else 0) *
            thetaOnRealData W₁ V β γ
              (namedVector W₁ V (fun y' : Matrix a n (LocProd P) ↦ if IsIntMatrix O y'
                then ε * invOnUnits χ (fromCols (y.map π) y' * N).det else 0) hπ)
              (x' * cᴴ * stdForm E s) (g, k) (realSlice D V (k⁻¹.adeleMatrix * Y) v))) := by
  -- The point is `(D.radicalElement c z, 1) * (D.levi (q, g), k)` and acts in two steps.
  have h_split : ((D.radicalElement c z * D.levi (q, g), k) : G E r × G E t) =
      (D.radicalElement c z, 1) * (D.levi (q, g), k) := by simp
  -- the radical gives the factor `stdAddChar` and the Heisenberg operator at `x' cᴴ (stdForm E s)`
  rw [Splitting.thetaTerm, hβ', h_split, ← rep_apply_apply, homSlice_radicalElement,
    gram_at_point_eq_map, hx]
  -- the Levi element gives the character, the modulus and the value at `k⁻¹ x' q`
  rw [homSlice_levi, k⁻¹.adeleMatrix.mul_assoc, hY, Matrix.mul_smul]
  -- the value of `v ⊗ Φ` there splits into the real slice of `v` and the finite slice of `Φ`
  rw [hπ.homSlice_localDatum D V hΦ _ _ fun w _ ↦ congrFun hΦ_std w]
  simp_rw [map_smul]
  rfl

/-- Let `π` read the components at the places `A` (`ReadsAt`), with O the integral elements of its
target, let (K I L) be the local frame `adaptedFrame hπ D`, let `v` be a Schwartz vector, and let
`Φ(y) = ε 1_O(y) χ⁻¹(det (y (K|I) N))`, for a number `ε`, a character `χ` and a fixed matrix `N`, be
Schwartz–Bruhat with support in a set `Ω`. Suppose that the signs `t'` represent, at the real
places, the Gram matrix of every `x` with non-zero real slice of `v`, but do not represent `T`. Then
the Fourier coefficient at `j • T` of the theta integral of `v ⊗ Φ` vanishes at
`D.radicalElement c z * D.levi (q, g)`. Here `j` is the purely imaginary element of the Weil data,
and `centerCoeff T F p` is the mean of ψ(tr TM) F(z(M) p) over adelic matrices M modulo rational
ones, with z(M) in the centre of the unipotent radical. -/
lemma centreCoeff_thetaIntegral_localDatum_eq_zero (hπ : ReadsAt A π) (β γ : AutChar E)
    (hΦ : Φ ∈ schwartzBruhat Ω)
    (hΦ_std : Φ = (adaptedFrame hπ D).stdDatum fun y : Matrix a (b ⊕ n) (LocProd P) ↦
      ε * invOnUnits χ (y * N).det)
    (hv : IsSchwartzVector v) (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (q : GL b (𝔸 E))
    (g : G E s) {t' : b → ℤˣ} {T : Matrix b b E} (hT : ¬RepresentedBy t' (T.map toAdele))
    (h_slice : SlicesVanishOutside D V t' v) :
    D.centerCoeff ((j : E) • T) (thetaIntegral X V β γ (localDatum X V v Φ hπ))
      (D.radicalElement c z * D.levi (q, g)) = 0 := by
  -- The coefficient is a sum over the `x` with Gram matrix `T`, and each term is zero.
  set f : 𝒮 (X.hom V) := localDatum X V v Φ hπ with hf
  set p : G E r := D.radicalElement c z * D.levi (q, g) with hp
  have h_int : D.HasIntegrableTerms V β γ f p :=
    hasIntegrableTerms_localDatum_of_eq_stdDatum W₁ D V hπ β γ hΦ hΦ_std hv c z q g
  have h_sum : D.centerCoeff ((j : E) • T) (thetaIntegral X V β γ f) p =
      ∑' x : {x : Matrix a b E | xᴴ * V.J * x = T},
        ∫ k : G E t, D.thetaTerm V β γ f p x.val k ∂V.quotMeasure := by
    unfold thetaIntegral
    simpa using D.centreCoeff_integral_eq_tsum h_int continuous_const T
  suffices h_terms : ∀ (x : {x : Matrix a b E | xᴴ * V.J * x = T}) (k : G E t),
      D.thetaTerm V β γ f p x.val k = 0 by simp [h_sum, h_terms]
  rintro ⟨x, hx⟩ k
  -- write `q = scaleIdele E • q'` and put `Y = x' q'`, with `x'` the standard coordinates of `x`
  obtain ⟨q', hq'⟩ : ∃ q' : GL b (𝔸 E), scaleIdele E • q' = q := MulAction.surjective _ q
  let Y : Matrix a b (𝔸 E) := V.x⁻¹.val * x.map toAdele * q'.val
  have hY : V.x⁻¹.val * x.map toAdele * q.val = scaleIdele E • Y := by
    subst hq'
    exact Matrix.mul_smul ..
  -- the Gram matrix of `k⁻¹ Y` is congruent to `T` by `q'`, so the real slice there is zero
  have h_gram : (k⁻¹.adeleMatrix * Y)ᴴ * stdForm E t * (k⁻¹.adeleMatrix * Y) =
      q'.valᴴ * T.map toAdele * q'.val := by
    rw [gram_mul, G.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix, gram_mul,
      gram_at_point_eq_map, hx]
  have h_zero : realSlice D V (k⁻¹.adeleMatrix * Y) v = 0 :=
    by_contra fun h_ne ↦ hT (.of_conjTranspose_mul_mul q'
      (by simpa only [h_gram] using h_slice _ h_ne))
  -- the term is a multiple of `thetaOnRealData` at that slice
  have hβ : β = β / upsilonU1 ^ card b * upsilonU1 ^ card b := (div_mul_cancel β _).symm
  rw [hf, hp, thetaTerm_localDatum_of_eq_stdDatum W₁ D V hπ γ hΦ hΦ_std hβ c z g rfl hY k, h_zero,
    map_zero, mul_zero, mul_zero, mul_zero]

end StandardDatum

open scoped Classical in
/-- Let D be an adapted splitting of X (signs r, indices m) over W₁ with isotropic frame of size b,
and V a space with signs t and rank a; `G E r`, `G E t` are their adelic unitary groups and
`PairFock E r t` the space of real data of the pair. Let π : 𝔸_f → `LocProd P` read the components
at the places A, with O the integral elements, let (K I L) be the local frame of D and χ a
multiplicative character of `LocProd P`. Let v be a Schwartz vector and let
Φ(y) = ε 1_O(y) χ⁻¹(det (y (K|I) N)), with a number ε and a fixed matrix N, be Schwartz–Bruhat with
support in a set Ω; here χ⁻¹ is `invOnUnits χ`, zero off the units of O. Put β' = β υ^b
(υ = `upsilonU1`), f = v ⊗ Φ and p = `D.radicalElement c z * D.levi (q, g)`; β', γ are the two
characters of the Weil representation of (X, V), and β, γ those left for (W₁, V).
(a) The terms of the theta kernel of f at p are integrable over [U(V)]; (b) with x' the standard
coordinates of x and x' q = `scaleIdele E` • Y, the term of x at k is ψ(½ tr(z xᴴJx)) χ_V(det q)⁻¹
|det q|^(a/2), χ_V = `γ.spaceChar a`, times `vacuumFactor` or 0 (as y, the finite part of k⁻¹Y, is
or is not integral), times the theta functional `thetaOnRealData` of (W₁, V) for the slice of Φ at y
with vacuum elsewhere (`namedVector`), evaluated at the real slice of v at k⁻¹Y; (c) if all x with
non-zero real slice have Gram matrix represented by the signs t' at the real places
(`SlicesVanishOutside`), and T is not, then the Fourier coefficient at `j • T` of the theta integral
of f vanishes at p (`j` is the purely imaginary element of the Weil data). -/
lemma thetaTerm_eq_and_centreCoeff_eq_zero {P : Finset (FinPlace E)} {A : Set (FinPlace E)}
    {π : 𝔸f E →+* LocProd P} [Nontrivial (LocProd P)] (hπ : ReadsAt A π) [IsBaseAdapted D]
    {Φ : Matrix a m (LocProd P) → ℂ} {Ω : Set (Matrix a m (LocProd P))} {v : PairFock E r t}
    {β β' : AutChar E} (γ : AutChar E) (χ : MulChar (LocProd P) ℂ) (ε : ℂ)
    (N : Matrix (b ⊕ n) a (LocProd P)) (hΦ : Φ ∈ schwartzBruhat Ω)
    (hΦ_std : Φ = (adaptedFrame hπ D).stdDatum fun y : Matrix a (b ⊕ n) (LocProd P) ↦
      ε * invOnUnits χ (y * N).det)
    (hv : IsSchwartzVector v) (hβ' : β' = β * upsilonU1 ^ card b)
    (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (q : GL b (𝔸 E)) (g : G E s) :
    let f : 𝒮 (X.hom V) := localDatum X V v Φ hπ
    let p : G E r := D.radicalElement c z * D.levi (q, g)
    -- (a)
    (D.HasIntegrableTerms V β' γ f p ∧
      -- (b)
      ∀ (x : Matrix a b E) (x' Y : Matrix a b (𝔸 E)),
        V.x⁻¹.val * x.map toAdele = x' → x' * q.val = scaleIdele E • Y → ∀ k : G E t,
        let y : Matrix a b (𝔸f E) := (k⁻¹.adeleMatrix * Y).map Prod.snd
        D.thetaTerm V β' γ f p x k =
          stdAddChar E (toAdele 2⁻¹ * (z * (xᴴ * V.J * x).map toAdele).trace) *
            (((γ.spaceChar (card a)).val q.det : ℂ)⁻¹ * √(ideleAbs q.det) ^ card a *
              ((if IsIntMatrix (Ô E) y then (vacuumFactor (isAdapted_homSource D V)).val else 0) *
                thetaOnRealData W₁ V β γ
                  (namedVector W₁ V (fun y' : Matrix a n (LocProd P) ↦ if IsIntMatrix O y'
                    then ε * invOnUnits χ (fromCols (y.map π) y' * N).det else 0) hπ)
                  (x' * cᴴ * stdForm E s) (g, k) (realSlice D V (k⁻¹.adeleMatrix * Y) v)))) ∧
    -- (c)
    ∀ (t' : b → ℤˣ) (T : Matrix b b E), ¬RepresentedBy t' (T.map toAdele) →
      SlicesVanishOutside D V t' v →
      D.centerCoeff ((j : E) • T) (thetaIntegral X V β' γ f) p = 0 := by
  exact ⟨⟨hasIntegrableTerms_localDatum_of_eq_stdDatum W₁ D V hπ β' γ hΦ hΦ_std hv c z q g,
      fun x x' Y hx hY ↦ thetaTerm_localDatum_of_eq_stdDatum W₁ D V hπ γ hΦ hΦ_std hβ' c z g hx hY⟩,
    fun t' T ↦ centreCoeff_thetaIntegral_localDatum_eq_zero W₁ D V hπ β' γ hΦ hΦ_std hv c z q g⟩

/-!
## A product formula for the theta functional on real data
-/

/-- Take the pair (W₁, V' ⊕ W₁), the datum built from a vector f for (W₁, V') and a vector F for
(W₁, W₁), the translation (c; 0), the point (g, u ⊕ l) and a product φ ⊗ v of real data. Here
`New.Exchange.thetaOnRealData` sends a real datum to θ(ϱ(translation) ω(point) (real datum ⊗ finite
vector)), with θ the theta distribution, ϱ the Heisenberg translation and ω the Weil representation
with the two given characters. With characters α, αβ it is a product of two factors. The first is
`New.Exchange.thetaOnRealData` for (W₁, V') with characters α, β at f, c, (g, u), φ. The second is
the theta kernel `New.pairTheta` of (W₁, W₁) with characters α, α at (g, l), for the datum v ⊗ F. -/
lemma thetaOnRealData_boxProd_eq_mul {E n b : Type} {s : n → ℤˣ} {t' : b → ℤˣ}
    [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype b] [DecidableEq b]
    {W₁ : Space E n s} (V' : Space E b t') (α β : AutChar E) (f : 𝒮 (W₁.hom V')) (F : 𝒮 (W₁.hom W₁))
    (c : Matrix b n (𝔸 E)) (g : G E s) (u : G E t') (φ : PairFock E s t') (v : PairFock E s s)
    (l : G E s) :
    thetaOnRealData W₁ (V'.sum W₁) α (α * β) (boxProd (homSigns_sum_target signs_comp_refl) f F)
        (fromRows c 0) (g, G.sum (u, l))
        (Fock.realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl)) φ v) =
      thetaOnRealData W₁ V' α β f c (g, u) φ *
        pairTheta W₁ W₁ α α (integrated (W₁.hom W₁) v F) (g, l) := by
  -- The datum is a product along `V'.sum W₁`, and `pairWeil`, the Heisenberg operator `ϱ` and `θ`
  -- act factor by factor; on the second factor the translation is by `0`.
  let box : 𝒮 (W₁.hom V') → 𝒮 (W₁.hom W₁) → 𝒮 (W₁.hom (V'.sum W₁)) :=
    (boxProd (homSigns_sum_target signs_comp_refl) · ·)
  have h_weil (f₁ : 𝒮 (W₁.hom V')) (f₂ : 𝒮 (W₁.hom W₁)) :
      pairWeil W₁ (V'.sum W₁) α (β * α) (g, G.sum (u, l)) (box f₁ f₂) =
        box (pairWeil W₁ V' α β (g, u) f₁) (pairWeil W₁ W₁ α α (g, l) f₂) :=
    pairWeil_boxProd_target (hs := rfl) (h_block := by simp) ..
  have h_heis (f₁ : 𝒮 (W₁.hom V')) (f₂ : 𝒮 (W₁.hom W₁)) :
      ϱ (W₁.hom (V'.sum W₁)) (matrixToVec (fromRows c 0)) (box f₁ f₂) =
        box (ϱ (W₁.hom V') (matrixToVec c) f₁) f₂ :=
    (rho_boxProd ..).trans (congrArg (box _) (Heisenberg.Rep.rho_zero_apply ..))
  simp only [thetaOnRealData, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rw [← boxProd_integrated, mul_comm α β, h_weil, h_heis, pairTheta]
  exact theta_boxProd_target (hs := rfl) (h_block := rfl) ..

end New.Exchange

/-!
## Equal ranks, and the exchange identity for the large triple from an identity of periods

`[U W]` is the quotient of the adelic unitary group of `W` by its rational points. Integrals over it
are taken against the measure `W.quotMeasure`.
-/

namespace New.Exchange

open Matrix WeilData MeasureTheory SemilocalField Fintype Space Splitting RingHom

variable {E : Type} [Field E] [CMType E] [WeilData E] {n a b m : Type} [Fintype n]
  [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : a → ℤˣ} {t' : b → ℤˣ} {r : m → ℤˣ} (X : Space E m r)
  {W₁ : Space E n s} {W : Space E a t} (D : X.Splitting W₁ b) (D₁ : W₁.Splitting W Unit)
  [IsBaseAdapted D] (V : Space E a t) (V' : Space E b t') {μ : NumberField.InfinitePlace E → ℤ}
  (𝔠 : SplitTameChar E μ)

/-- Equal ranks: let `W₁` have even rank and let the adapted splitting `D₁` split a hyperbolic plane
off `W₁`. For a tame character `𝔠`, the theta integral `thetaLarge` with both spaces equal to `W₁`,
on a real Schwartz vector `v` and the datum `χ⁻¹ ∘ det` at the ramified places
(`stdColDatum 𝔠.semilocalChar 1`), is constant on `U(W₁)`. -/
theorem thetaLarge_eq_apply_one_of_even_rank [IsBaseAdapted D₁] {v : PairFock E s s}
    (hn : 2 ∣ card n) (hv : IsSchwartzVector v) (g : G E s) :
    thetaLarge W₁ W₁ 𝔠 v (stdColDatum 𝔠.semilocalChar 1) g = thetaLarge W₁ W₁ 𝔠 v
      (stdColDatum 𝔠.semilocalChar 1) 1 := by
  -- The theta integral `F` is automorphic and right invariant at `𝔠.ramifiedPlaces` and under
  -- `stdLevel` off `𝔠.ramifiedPlaces`. Its constant term along `D₁` at `D₁.levi (u, x)` does not
  -- depend on `u`, so it is constant by `IsAutFunction.apply_eq_apply_one`.
  obtain ⟨d, hd⟩ : ∃ d : ℕ, card a = 2 * d := ⟨card a / 2, by grind [D₁.card_eq]⟩
  let σ : Empty ⊕ n ≃ n := .emptySum Empty n
  -- the constant term at `D₁.levi (u, x)` is a function `F₀` of `x` alone
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : G E t → ℂ, ∀ (u : (𝔸 E)ˣ) (x : G E t),
      planeConstantTerm 𝔠 W₁ D₁ σ v (0 : Matrix Empty a (LocProd 𝔠.ramifiedPlaces)) u x = F₀ x := by
    obtain ⟨C, -, h_plane⟩ :=
      exists_planeConstantTerm_eq_thetaLarge_cone D₁ D₁ σ (.emptySum Empty a) ⟨d, hd⟩ μ (z := d)
        (by omega)
    obtain ⟨γ, -, hγ⟩ := h_plane 𝔠
    exact ⟨_, fun u x ↦ hγ v hv 0 nofun u x (.inr rfl)⟩
  obtain ⟨M, 𝒟, h𝒟, h_diff⟩ :=
    exists_isEquivariantLift_eq_thetaLarge_sub_smul W₁ W₁ (stdSpace E Empty) 𝔠 σ hn hv
      Fock.isSchwartzVector_vacVector 0
  set F : G E s → ℂ := thetaLarge W₁ W₁ 𝔠 v (stdRowDatum σ 𝔠.semilocalChar 0) with hF
  obtain ⟨h_mem, h_val⟩ : stdColDatum 𝔠.semilocalChar 0 ∈ M ∧ 𝒟 (stdColDatum 𝔠.semilocalChar 0) =
    F := by
    simpa using h_diff (.of_discrete _) (areMatched_stdRowDatum_stdColDatum (s := 0) σ nofun)
  -- At `𝔠.ramifiedPlaces`, matrices with no column are all equal, and the factor is `1`.
  have h_on (k : Gf E n) (hk : k ∈ Gf.supportedOn n 𝔠.ramifiedPlaces) (x : G E s) :
    F (x * (1, k)) = F x := by
    obtain ⟨-, h_law⟩ := h𝒟.map_translate h_mem k hk
    simpa [h_val, fun y : Matrix n Empty (LocProd 𝔠.ramifiedPlaces) ↦
      Subsingleton.elim ((atPlaces 𝔠.ramifiedPlaces k).val * y) y] using h_law x
  have h_off : HasLevel F (stdLevel E n ⊓ Gf.trivialOn n 𝔠.ramifiedPlaces) := by
    simpa only [h_val] using h𝒟.invariant_off _ h_mem
  have h_aut : IsAutFunction W₁ F := by simpa only [h_val] using h𝒟.isAutFunction h_mem
  -- with no first block, the row datum of `F` is `stdColDatum 𝔠.semilocalChar 1` by definition
  change F g = F 1
  refine h_aut.apply_eq_apply_one D₁ 𝔠.nonempty h_on h_off (fun h_left ↦ ⟨F₀, fun u x ↦ ?_⟩) g
  -- If `F` is invariant under the radical, it equals its constant term.
  have h_scalar : GeneralLinearGroup.scalar Unit u.det = u := by ext : 2; simp
  simp [← hF₀ u.det x, planeConstantTerm, ← hF, h_left, h_scalar]

/-- The squared absolute value at `1` of the theta integral `thetaLarge` of the pair `(X, X)`, for
the real vector `v` and the datum `χ⁻¹ ∘ det` on integral invertible matrices, divided by `L_*(e)`
with `e` half the rank of `X`, rounded down. Here `L_*(e) = lValueProdInt 𝔠 e` is
`∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2` for `ν = 𝔠.character` and
`S = 𝔠.ramifiedPlaces`. -/
noncomputable def equalRankThetaRatio
    (v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns r r)))) : ℝ :=
  ‖thetaLarge X X 𝔠 v (stdColDatum 𝔠.semilocalChar 1) 1‖ ^ 2 / lValueProdInt 𝔠 (card m / 2)

/-- The exchange identity for standard data. The real vectors `v` and `y` are Schwartz vectors (all
weighted norms finite), and there is a real `C` such that for every tame character `𝔠` of weight `μ`
some `c : ℂ` satisfies (a) `C * ‖c‖ ^ 2 = L_*(rk V - rk X / 2) * ℓ 𝔠`, with the half rounded down,
and (b) for all integral `z`, the theta integral of `(X, V)` on `v` and the row datum of `z` is `c`
times the theta integral of `(X, V')` on `y` and the column datum of `z`. Here
`L_*(e) = lValueProdInt 𝔠 e` is `∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2` for `e ≥ 0`,
`ν = 𝔠.character`, `S = 𝔠.ramifiedPlaces`, and `L_*(-e) = L_*(e)⁻¹`. The row datum sends `x` to
`χ⁻¹ ∘ det` of the matrix with the rows of `z` and `x`, ordered by `σ`; the column datum sends `x`
to `χ⁻¹ (det (z x))`; both vanish unless `x` is integral and the determinant is a unit. No sign is
asked of `C`; by (a) it is positive as soon as `ℓ 𝔠 > 0` for one `𝔠`. -/
def RowColExchangeIdentity (μ : NumberField.InfinitePlace E → ℤ) (σ : b ⊕ a ≃ m)
    (v : PairFock E r t) (y : PairFock E r t') (ℓ : SplitTameChar E μ → ℝ) : Prop :=
  IsSchwartzVector v ∧ IsSchwartzVector y ∧
  ∃ C : ℝ, ∀ 𝔠 : SplitTameChar E μ, ∃ c : ℂ,
    -- (a) the size of the factor
    C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (card a - card m / 2) * ℓ 𝔠 ∧
    -- (b) the two theta integrals are proportional on standard data
    ∀ z : Matrix b m (LocProd 𝔠.ramifiedPlaces), IsIntMatrix O z →
      thetaLarge X V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar z) = c • thetaSmall X V' 𝔠 y
        (stdColDatum 𝔠.semilocalChar z)

omit [WeilData E] in
/-- The image in `U(V' ⊕ W₁)` of the group `W₁.Γ` of rational points of the second summand consists
of the rational points of the sum that fix the first block of columns `(1; 0)`. -/
lemma mem_map_sum_iff_fixes_cols (k : G E (t' ⊕ᵥ s)) :
    k ∈ W₁.Γ.map (G.sum.comp (MonoidHom.inr (G E t') (G E s))) ↔
      ∃ γ : U (V'.sum W₁).J,
        γ.val.val * fromRows (1 : Matrix b b E) (0 : Matrix n b E) = fromRows 1 0 ∧
        (V'.sum W₁).ratEmbed γ = k := by
  have h_fixes (γ : U (fromBlocks V'.J 0 0 W₁.J)) : (∃ w : U W₁.J, U.sum rfl (1, w) = γ) ↔
      γ.val.val * fromRows (1 : Matrix b b E) (0 : Matrix n b E) = fromRows 1 0 := by
    have h_cols : γ.val.val * fromRows (1 : Matrix b b E) (0 : Matrix n b E) =
        γ.val.val.toCols₁ := by ext; simp [Matrix.mul_apply, Matrix.one_apply]
    simpa only [h_cols] using New.U.mem_range_sum_right rfl V'.isUnit_J
  change _ ↔ ∃ γ : U (fromBlocks V'.J 0 0 W₁.J),
    γ.val.val * fromRows (1 : Matrix b b E) (0 : Matrix n b E) = fromRows 1 0 ∧
      (V'.sum W₁).ratEmbed γ = k
  rw [← exists_congr fun γ ↦ and_congr_left' (h_fixes γ)]
  simp [Γ, sum_ratEmbed, -Subtype.exists]

omit [WeilData E] [Fintype b] [DecidableEq b] in
/-- The finite part of `k⁻¹ Y` is the inverse of the finite component of `k` times the finite part
of `Y`. -/
lemma map_snd_adeleMatrix_inv_mul (k : G E t) (Y : Matrix a b (𝔸 E)) :
    (k⁻¹.adeleMatrix * Y).map Prod.snd =
      ((k.2⁻¹ : GL a (𝔸f E)) : Matrix a a (𝔸f E)) * Y.map Prod.snd :=
  Matrix.map_mul (f := RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))

/-- Let `Y k` be unitary at the finite places, with `k` in `GL_b(Ô E)`. Suppose that the finite part
of the inverse of `(y ⊕ y') (h, u)` maps the columns `(Y, 0)` to integral ones. Then some block
diagonal translate of `u` lies in `stdLevel`, the stabiliser of the standard lattice. -/
lemma exists_blockSumOne_mul_mem_stdLevel {Y : GL b (𝔸 E)} {k : GL b (𝔸f E)}
    (hk : k ∈ intGL b (Ô E))
    (hY : Y.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)) * k ∈ U 1) {y : G E t'}
    {y' : G E s} {h : GInf E (t' ⊕ᵥ s)} {u : U (1 : Matrix (b ⊕ n) (b ⊕ n) (𝔸f E))}
    (h_int : IsIntMatrix (Ô E) (((G.sum (y, y') * (h, u))⁻¹.adeleMatrix *
      fromRows Y.val (0 : Matrix n b (𝔸 E))).map Prod.snd)) :
    ∃ u₀ : U (1 : Matrix b b (𝔸f E)) × U (1 : Matrix n n (𝔸f E)),
      U.blockSumOne u₀ * u ∈ stdLevel E (b ⊕ n) := by
  -- Witt's theorem over `Ô E`: some `g₀ ∈ stdLevel` moves the first columns `Z` of `u⁻¹ w` to
  -- those of `1`, so `g₀ u⁻¹ w` lies in the second block.
  rw [map_snd_adeleMatrix_inv_mul] at h_int
  let Yk : Gf E b := ⟨Y.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)) * k, hY⟩
  let w : Gf E b × Gf E n := (y.2⁻¹ * Yk, y'.2⁻¹)
  let Z : Matrix (b ⊕ n) b (𝔸f E) := fun j i ↦ (u⁻¹ * U.blockSumOne w).val.val j (Sum.inl i)
  let Z₀ : Matrix (b ⊕ n) b (𝔸f E) := fromRows 1 0
  have hZ_int : IsIntMatrix (Ô E) Z := by
    simpa [Z, w, Yk, G.sum, U.sum, blockGL, IsIntMatrix, ← fromCols_fromRows_eq_fromBlocks,
      Matrix.mul_assoc, fromRows_map, fromCols_mul_fromRows] using h_int.mul hk.isIntMatrix
  have hZ_orth : Zᴴ * (1 : Matrix (b ⊕ n) (b ⊕ n) (𝔸f E)) * Z = 1 :=
    (congrArg toBlocks₁₁ (mem_unitaryGroupOf_iff.1 (u⁻¹ * U.blockSumOne w).prop)).trans
        (by simp [← fromBlocks_one])
  have hZ₀_int : IsIntMatrix (Ô E) Z₀ := by simp [Z₀, IsIntMatrix, ite_mem, Matrix.one_apply]
  have hZ₀_orth : Z₀ᴴ * (1 : Matrix (b ⊕ n) (b ⊕ n) (𝔸f E)) * Z₀ = 1 := by
    simp [Z₀, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  obtain ⟨g₀, hg₀, h_cols⟩ : ∃ g₀ ∈ stdLevel E (b ⊕ n), g₀.val.val * Z = Z₀ :=
    witt_Ô_of_orthonormal hZ_orth hZ₀_orth hZ_int hZ₀_int
  obtain ⟨w', hw'⟩ : ∃ w' : Gf E n, U.blockSumOne (1, w') = g₀ * (u⁻¹ * U.blockSumOne w) :=
    (New.U.mem_range_sum_right fromBlocks_one isUnit_one).mpr h_cols
  refine ⟨(1, w') / w, ?_⟩
  rwa [map_div, hw', ← mul_assoc, mul_div_cancel_right, inv_mul_cancel_right]

open scoped Classical in
/-- Let `x` in `GL_b(𝔸_f)` have integral entries. The vector of `𝒮(Hom(W₁, V' ⊕ W₁))` given at the
places `𝔠.ramifiedPlaces` by `y ↦ ε χ⁻¹(det ((x; 0) | y))` on integral `y` is `ε χ⁻¹(det x)` times
the product of the vacuum of `(W₁, V')` with the vector of the datum `χ⁻¹ ∘ det` of `(W₁, W₁)`. Here
`χ⁻¹` is `invOnUnits 𝔠.semilocalChar`, which vanishes off the units of `O`. -/
lemma namedVector_det_fromCols_eq_boxProd (ε : ℂ) {x : GL b (𝔸f E)} (hx : IsIntMatrix (Ô E) x.val) :
    namedVector W₁ (V'.sum W₁) (fun y : Matrix (b ⊕ n) n (LocProd 𝔠.ramifiedPlaces) ↦
      if IsIntMatrix O y then
        ε * invOnUnits 𝔠.semilocalChar (fromCols
          ((fromRows x.val 0).map (evalPlaces 𝔠.ramifiedPlaces)) y).det
        else 0) 𝔠.readsAt =
      (ε * invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces x.det)) •
        Space.boxProd (homSigns_sum_target signs_comp_refl) (W₁.hom V').vacElem
          (namedVector W₁ W₁ (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt) := by
  -- the determinant is block triangular and `invOnUnits 𝔠.semilocalChar` is multiplicative on `O`
  have h_det (y : Matrix (b ⊕ n) n (LocProd 𝔠.ramifiedPlaces)) (hy : IsIntMatrix O y.toRows₂) :
      invOnUnits 𝔠.semilocalChar (fromCols ((fromRows x.val 0).map (evalPlaces 𝔠.ramifiedPlaces))
        y).det =
        invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces x.val.det) * invOnUnits
          𝔠.semilocalChar y.toRows₂.det := by
    have h_blocks : fromCols ((fromRows x.val 0).map (evalPlaces 𝔠.ramifiedPlaces)) y =
        fromBlocks (x.val.map (evalPlaces 𝔠.ramifiedPlaces)) y.toRows₁ 0 y.toRows₂ := by
      ext (i | i) (j | j) <;> simp
    rw [h_blocks, det_fromBlocks_zero₂₁, ← invOnUnits_mul (evalPlaces_mem_O _ hx.det_mem)
      hy.det_mem, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [← (W₁.hom V').projOn_vacElem, ← schrodingerOp_boxIndicator 𝔠.readsAt.disjoint_star,
    boxProd_schrodingerOp _ 𝔠.readsAt.disjoint_star
      (hΨ' := 𝔠.readsAt.isSchwartzBruhat (stdColDatum_mem_schwartzBruhat _ .one)) rfl,
    smul_schrodingerOp, namedVector]
  congr with y
  -- both sides vanish unless the two blocks of rows of `y` are integral
  simp [mem_integralBox, IsIntMatrix, ← 𝔠.readsAt.mem_iff, stdColDatum, ← ite_and, mul_assoc]
  exact if_ctx_congr and_comm (fun ⟨h_int, _⟩ ↦ congrArg (ε * ·) (h_det _ h_int)) fun _ ↦ rfl

open scoped Classical in
/-- For `x` in `GL_b(𝔸f E)`, the vector named at the conjugates of the places `𝔠.ramifiedPlaces` by
the constant `χ⁻¹ (det x̄)` on integral matrices is that constant times the vacuum of `Hom(W₁, V')`.
This is the finite slice of the datum of the small side. -/
lemma namedVector_det_star_eq_vacElem (x : GL b (𝔸f E)) :
    namedVector W₁ V' (fun y : Matrix b n (LocProd 𝔠.ramifiedPlaces) ↦ if IsIntMatrix O y then
        invOnUnits 𝔠.semilocalChar (x.val.map
          ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E)))).det
        else 0) 𝔠.readsAt.star =
      invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces (star x.det)) •
        (W₁.hom V').vacElem := by
  set π : 𝔸f E →+* LocProd 𝔠.ramifiedPlaces :=
    (evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))
  have h_reads : ReadsAt (star ⁻¹' 𝔠.ramifiedPlaces) π := 𝔠.readsAt.star
  have h_det : (x.val.map π).det = evalPlaces 𝔠.ramifiedPlaces (star x.det) :=
    (π.map_det x.val).symm
  -- both sides are named by the same multiple of the indicator of the integral matrices
  rw [h_det, ← projOn_vacElem, ← schrodingerOp_boxIndicator h_reads.disjoint_star,
    smul_schrodingerOp, namedVector]
  congr with y
  have h_box : IsIntMatrix O ((vecToMatrix y).map π) ↔ y ∈ integralBox (b × n)
    (star ⁻¹' 𝔠.ramifiedPlaces) := by
    simp [IsIntMatrix, mem_integralBox, h_reads.mem_iff, vecToMatrix]
  simp only [Pi.smul_apply, boxIndicator, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact if_congr h_box rfl rfl

omit [WeilData E] in
/-- If `x` is integral and `x * k` is unitary for some `k` in `GL_b(Ô E)`, then `det x` is a unit at
every finite place. -/
lemma det_mem_idelesUnitOff_of_mul_mem {x k : GL b (𝔸f E)} (hk : k ∈ intGL b (Ô E))
    (hx : IsIntMatrix (Ô E) x.val) (hxk : x * k ∈ U 1) : x.det ∈ idelesUnitOff ∅ := by
  have h_mem : (⟨x * k, hxk⟩ : Gf E b) ∈ stdLevel E b := mem_stdLevel.2 (hx.mul hk.isIntMatrix)
  exact idelesUnitOff_empty.ge
    ⟨hx.det_mem, ((mul_mem_cancel_right hk).1 h_mem).isIntMatrix_inv.det_mem⟩

omit [WeilData E] in
/-- Let `𝔠` be a tame character, `χ` its component `semilocalChar` on the product `LocProd` of the
fields at its ramified places, read by `readsAt` there and by `readsAt.star`, through conjugation,
at the conjugate places. Let `D` be an adapted splitting; `adaptedFrame` is the image of its frames
(K I L) at these places, with `dualL` the L-block of the dual frame. Then the transpose of
`y ↦ χ⁻¹ (det (dualL y))` on integral `y` equals the datum `stdDatum` of the conjugate frame:
integral `y ↦ χ⁻¹ ∘ det` of the first block of columns of `y (K|I)`. -/
lemma stdColDatum_transpose_eq_stdDatum :
    (fun y : Matrix b m (LocProd 𝔠.ramifiedPlaces) ↦
      stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL yᵀ) =
      (adaptedFrame 𝔠.readsAt.star D).stdDatum fun y : Matrix b (b ⊕ n) (LocProd 𝔠.ramifiedPlaces) ↦
        1 * invOnUnits 𝔠.semilocalChar
          (y * fromRows (1 : Matrix b b (LocProd 𝔠.ramifiedPlaces))
            (0 : Matrix n b (LocProd 𝔠.ramifiedPlaces))).det := by
  classical
  -- the finite part of `stdForm E r` is `1`, so `dualL` is the conjugate transpose of the block `K`
  have h_block : (adaptedFrame 𝔠.readsAt D).dualLᵀ = (adaptedFrame 𝔠.readsAt.star D).K :=
    Matrix.ext fun i j ↦ congrArg (evalPlaces 𝔠.ramifiedPlaces)
      (show (D.lCoord j i).2 = star (D.kAdelic i j).2 by simp [lCoord, stdForm])
  funext y
  have h_det : ((adaptedFrame 𝔠.readsAt D).dualL * yᵀ).det =
      (y * (adaptedFrame 𝔠.readsAt.star D).K).det := by
    rw [← det_transpose, transpose_mul, transpose_transpose, h_block]
  rw [stdColDatum, IntegralFrame.stdDatum, h_det]
  exact if_congr forall_comm (by simp [fromCols_mul_fromRows]) rfl

omit [WeilData E] in
/-- The first block of columns of `V' ⊕ W₁` has Gram matrix the form of `V'`. -/
lemma gram_sum_fromRows_one_zero :
    (fromRows (1 : Matrix b b E) (0 : Matrix n b E))ᴴ * (V'.sum W₁).J *
      fromRows (1 : Matrix b b E) (0 : Matrix n b E) = V'.J := by
  simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows]

omit [IsBaseAdapted D] in
/-- Let `𝔠` be a tame character, `χ` its component `semilocalChar` at the places `𝔠.ramifiedPlaces`,
read through `𝔠.readsAt`. Let the splitting `D` split `X` as `W₁` plus a hyperbolic space, and let
`σ` order the rows of a square matrix made of `b` and `a` rows. Unfolded along `D`, the theta kernel
of `(X, V)` has one term `thetaTerm` for each rational matrix `x`, a function of `P` in `G E r` and
`k` in `G E t`. Take the characters `rankTwist 𝔠.character⁻¹ m = ν⁻¹ υ ^ ⌊rk X / 2⌋`
(`ν = 𝔠.character`, `υ` the splitting character of the Weil data) and any `γ`, and the datum
(`localDatum`) with real part `v` in the Fock space `PairFock`, the row datum `stdRowDatum` of an
integral matrix `z₀` at the ramified places, and the vacuum elsewhere. Then the term does not change
when `k` is multiplied on the right by a finite point `u` in `stdLevel`, the stabiliser of the
standard lattice. -/
lemma thetaTerm_stdRowDatum_mul_of_mem_stdLevel (σ : b ⊕ a ≃ m) {v : PairFock E r t} {γ : AutChar E}
    {z₀ : Matrix b m (LocProd 𝔠.ramifiedPlaces)} (hz₀ : IsIntMatrix O z₀) {u : Gf E a}
    (hu : u ∈ stdLevel E a) (P : G E r) (x : Matrix a b E) (k : G E t) :
    D.thetaTerm V (rankTwist 𝔠.character⁻¹ m) γ
      (localDatum X V v (stdRowDatum σ 𝔠.semilocalChar z₀) 𝔠.readsAt) P x
        (k * (1, u)) =
      D.thetaTerm V (rankTwist 𝔠.character⁻¹ m) γ
        (localDatum X V v (stdRowDatum σ 𝔠.semilocalChar z₀) 𝔠.readsAt) P x
        k := by
  have h_split : ((P, k * (1, u)) : G E r × G E t) = (P, k) * (1, (u : G E t)) := by simp
  rw [Splitting.thetaTerm, Splitting.thetaTerm, h_split, ← rep_apply_apply,
    pairWeil_stdRowDatum_eq_self σ hz₀ hu rfl]

open scoped Classical in
/-- The term at the rational matrix `(1; 0)` of the theta kernel of `(X, V' ⊕ W₁)` for the row
datum, assumed to be `ε` times the standard datum of the frame adapted to `D`. Let
`q = scaleIdele • V'.x * Y` and `γ = ν⁻¹ υ ^ ⌊rk X / 2⌋` (`rankTwist`, with `ν = 𝔠.character` and
`υ` the splitting character of the Weil data), and let `a` be the rank `card (b ⊕ n)` of `V' ⊕ W₁`.
At `(radicalElement c z * levi (q, g), k)`, whose first entry is the point n(c, z) m(q, g) of the
parabolic subgroup, the term is the product of
* `ψ(½ tr(z V'.J)) (γ.spaceChar a)(det q)⁻¹ |det q| ^ (a / 2)`;
* `vacuumFactor` if the finite part `y` of `k⁻¹ (Y; 0)` is integral at all finite places, and `0`
  otherwise;
* `thetaOnRealData`, the theta functional of `(W₁, V' ⊕ W₁)` for the finite slice of the datum at
  `y` with vacuum elsewhere (`namedVector`), moved by `(g, k)` and the translation by
  `(V'.x⁻¹; 0) cᴴ J_s`, evaluated at the real slice of `v` at `k⁻¹ (Y; 0)`. -/
lemma thetaTerm_stdRowDatum_eq {σ' : b ⊕ b ⊕ n ≃ m} (v : PairFock E r (t' ⊕ᵥ s)) {ε : ℂ}
    (h_std : stdRowDatum σ' 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL =
      (adaptedFrame 𝔠.readsAt D).stdDatum fun x :
        Matrix (b ⊕ n) (b ⊕ n) (LocProd 𝔠.ramifiedPlaces) ↦
        ε * invOnUnits 𝔠.semilocalChar x.det)
    (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (g : G E s) (Y : GL b (𝔸 E))
    (k : G E (t' ⊕ᵥ s)) {y : Matrix (b ⊕ n) b (𝔸f E)}
    (hy : (k⁻¹.adeleMatrix * fromRows Y.val (0 : Matrix n b (𝔸 E))).map Prod.snd = y) :
    let q : GL b (𝔸 E) := scaleIdele E • V'.x * Y
    let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
    D.thetaTerm (V'.sum W₁) γ γ
        (localDatum X (V'.sum W₁) v (stdRowDatum σ' 𝔠.semilocalChar
          (adaptedFrame 𝔠.readsAt D).dualL) 𝔠.readsAt)
        (D.radicalElement c z * D.levi (q, g)) (fromRows 1 0) k =
      stdAddChar E (toAdele 2⁻¹ * (z * V'.J.map toAdele).trace) *
        (((γ.spaceChar (card (b ⊕ n))).val q.det : ℂ)⁻¹ * √(ideleAbs q.det) ^ card (b ⊕ n) *
          ((if IsIntMatrix (Ô E) y then (vacuumFactor (isAdapted_homSource D (V'.sum W₁))).val
              else 0) *
            thetaOnRealData W₁ (V'.sum W₁) (rankTwist 𝔠.character⁻¹ n) γ
              (namedVector W₁ (V'.sum W₁)
                (fun y' : Matrix (b ⊕ n) n (LocProd 𝔠.ramifiedPlaces) ↦ if IsIntMatrix O y' then
                  ε * invOnUnits 𝔠.semilocalChar
                    (fromCols (y.map (evalPlaces 𝔠.ramifiedPlaces)) y').det else 0) 𝔠.readsAt)
              (fromRows V'.x.inv 0 * cᴴ * stdForm E s) (g, k)
              (realSlice D (V'.sum W₁) (k⁻¹.adeleMatrix * fromRows (m₂ := n) Y.val 0) v))) := by
  intro q γ
  subst hy
  -- the standard coordinates of the columns `(1, 0)`
  have h_coord : (V'.sum W₁).x⁻¹.val *
      (fromRows (1 : Matrix b b E) (0 : Matrix n b E)).map toAdele = fromRows V'.x.inv 0 := by
    simp [sum, blockGL, fromRows_map, fromBlocks_mul_fromRows]
  have h_scale : fromRows V'.x.inv (0 : Matrix n b (𝔸 E)) * q.val =
      scaleIdele E • fromRows Y.val (0 : Matrix n b (𝔸 E)) := by simp [q]
  simpa only [gram_sum_fromRows_one_zero, mul_one] using
    thetaTerm_localDatum_of_eq_stdDatum W₁ D (V'.sum W₁) 𝔠.readsAt γ (v := v) (N := 1) (β' := γ)
      (stdRowDatum_mem σ' 𝔠.semilocalChar) (by simpa using h_std) (rankTwist_eq_mul_of_splitting D)
        c z g
      h_coord h_scale k

open scoped Classical in
/-- The term at `1` of the small theta kernel, that of `(X, V')`. Its datum is the standard column
datum of the frame adapted to `D`, transposed, as `V'` indexes rows here, and read at the conjugates
of the ramified places through conjugation (`readsAt.star`). Let `q = scaleIdele E • V'.x * Y`, with
`scaleIdele E` the normalising idele of the Weil data. Let `υ` be the splitting Hecke character of
the Weil data and `upsilonU1` its restriction to the norm-one ideles, so that
`rankTwist ν m = ν upsilonU1 ^ ⌊card m / 2⌋`, and put `γ = upsilonU1 ^ b` with `b` the rank of `V'`.
The term at `(radicalElement c z * levi (q, g), k)` is the product of
* `ψ(½ tr(z V'.J)) χ_{V'}(det q)⁻¹ |det q| ^ (b / 2)`, where `χ_{V'} = γ.spaceChar b` is the Hecke
  character `u ↦ γ(u / ū) υ(u) ^ (-b)`;
* `vacuumFactor`, the non-zero constant in the formula for the slices of the vacuum, or `0`, as the
  finite part `y` of `k⁻¹ Y` is integral or not; `thetaOnRealData`, the theta functional of
  `(W₁, V')` moved by `(g, k)` and by the translation `V'.x⁻¹ cᴴ J_s`, for the finite slice of the
  datum at `y` with vacuum elsewhere (`namedVector`; on the slice variable `y₂` it is constant where
  `y₂` is integral), evaluated at the real slice of `v'` at `k⁻¹ Y`. -/
lemma thetaTerm_stdColDatum_eq (v' : PairFock E r t')
    (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (g : G E s) (Y : GL b (𝔸 E)) (k : G E t')
    {y : Matrix b b (𝔸f E)} (hy : (k⁻¹.adeleMatrix * Y.val).map Prod.snd = y) :
    let q : GL b (𝔸 E) := scaleIdele E • V'.x * Y
    let γ : AutChar E := upsilonU1 ^ card b
    D.thetaTerm V' (rankTwist 𝔠.character m) γ
        (localDatum X V' v' (fun w : Matrix b m (LocProd 𝔠.ramifiedPlaces) ↦
          stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL wᵀ) 𝔠.readsAt.star)
        (D.radicalElement c z * D.levi (q, g)) 1 k =
      stdAddChar E (toAdele 2⁻¹ * (z * V'.J.map toAdele).trace) *
        (((γ.spaceChar (card b)).val q.det : ℂ)⁻¹ * √(ideleAbs q.det) ^ card b *
          ((if IsIntMatrix (Ô E) y then (vacuumFactor (isAdapted_homSource D V')).val else 0) *
            thetaOnRealData W₁ V' (rankTwist 𝔠.character n) γ
              (namedVector W₁ V'
                (fun y₂ : Matrix b n (LocProd 𝔠.ramifiedPlaces) ↦ if IsIntMatrix O y₂ then
                  invOnUnits 𝔠.semilocalChar
                    (y.map ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E)))).det else 0)
                𝔠.readsAt.star)
              (V'.x⁻¹.val * cᴴ * stdForm E s) (g, k)
              (realSlice D V' (k⁻¹.adeleMatrix * Y.val) v'))) := by
  intro q γ
  subst hy
  have h_coord : V'.x⁻¹.val * (1 : Matrix b b E).map toAdele = V'.x⁻¹.val := by simp
  have h_scale : V'.x⁻¹.val * q.val = scaleIdele E • Y.val := by simp [q]
  simpa only [mul_one, conjTranspose_one, one_mul, fromCols_mul_fromRows, Matrix.mul_zero,
    add_zero] using
    thetaTerm_localDatum_of_eq_stdDatum W₁ D V' 𝔠.readsAt.star γ (v := v')
      (β' := rankTwist 𝔠.character m)
      (stdColDatum_mem_schwartzBruhat 𝔠.semilocalChar
        (adaptedFrame 𝔠.readsAt D).blockRelations.isIntMatrix_dualL).transpose_mem_schwartzBruhat
      (stdColDatum_transpose_eq_stdDatum X D 𝔠) (rankTwist_eq_mul_of_splitting D) c z g
      h_coord h_scale k

/-- The determinant of `B` read at the infinite places. -/
noncomputable def infiniteDet (B : GL b (𝔸 E)) : (NumberField.InfinitePlace E → ℂ)ˣ :=
  B.det.map (MonoidHom.fst (NumberField.InfinitePlace E → ℂ) (𝔸f E))

omit [WeilData E] in
/-- The component of `infiniteDet B` at `w` is the determinant of the component of `B` at `w`. -/
lemma infiniteDet_apply (B : GL b (𝔸 E)) (w : NumberField.InfinitePlace E) :
    (infiniteDet B).val w = (atRealPlace B.val w).det :=
  (evalInf w).map_det B.val

omit [WeilData E] in
/-- The determinant of an adelic matrix `B` is the product of its part at the infinite places and
the determinant of the finite part `x` of `B`. -/
lemma det_eq_realIdele_mul_finIdeleIncl {B : GL b (𝔸 E)} {x : GL b (𝔸f E)}
    (hx : B.val.map Prod.snd = x.val) : B.det = realIdele (infiniteDet B) * finIdeleIncl x.det := by
  ext : 2
  · simp [infiniteDet]
  · simp [← hx]

/-- The identity of periods over `[U W₁]` for a tame character `𝔠` of weight `μ` (an integer for
each infinite place) and real data `v` of `(X, V' ⊕ W₁)` and `v'` of `(X, V')`, with weight function
`ρ` and period `I₀`. For each real point `h` there is `p` in `U V' × U W₁` with the following
property for all invertible `B`, characters `β`, vectors `f`, matrices `x` and points `g`, `y`. Take
the slice of `v` at `(p h)⁻¹ (B, 0)`, where `p` is read at the infinite places, and move it by `p h`
in the real Weil representation `realPairWeil`, in which `p h` acts by its Fock operator times
`∏_w det ^ (⌊n / 2⌋ - μ w)`. Integrate over `u ∈ [U W₁]` its theta functional for the vector
`f ⊠ (χ⁻¹ ∘ det)` at `(x, 0)` and `(g, y ⊕ u)`, with characters `γ` and `γ β`. The result is
`ρ h * I₀ / (ν(z / z̄) |z|^(n/2))` times the theta functional for `f` at `x` and `(g, y)`, with
characters `γ` and `β`, of the slice of `v'` at `B`. Here `z` is the idele equal to `det B` at the
infinite places and to `1` at the finite places, `ν` is `𝔠.character`, `n` is the rank of `W₁`, and
`γ = rankTwist ν⁻¹ n` is `ν⁻¹ υ ^ ⌊n / 2⌋` with `υ` the splitting character of the Weil data. -/
def IsPeriodIdentity (v : PairFock E r (t' ⊕ᵥ s)) (v' : PairFock E r t')
    (ρ : GInf E (t' ⊕ᵥ s) → ℝ) (I₀ : ℂ) : Prop :=
  let γ : AutChar E := rankTwist 𝔠.character⁻¹ n
  ∀ h : GInf E (t' ⊕ᵥ s), ∃ p : G E t' × G E s,
    ∀ (B : GL b (𝔸 E)) (β : AutChar E) (f : 𝒮 (W₁.hom V')) (x : Matrix b n (𝔸 E)) (g : G E s)
      (y : G E t'),
      ∫ u : G E s, thetaOnRealData W₁ (V'.sum W₁) γ (γ * β)
          (Space.boxProd (homSigns_sum_target signs_comp_refl) f
            (namedVector W₁ W₁ (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt))
          (fromRows x 0) (g, G.sum (y, u))
          (realPairWeil (fun w : NumberField.InfinitePlace E ↦ card n / 2 - μ w) 0
            (1, (G.sum p).1 * h) (realSlice D (V'.sum W₁)
              (G.adeleMatrix ((G.sum p).1 * h, 1)⁻¹ * fromRows B.val (0 : Matrix n b (𝔸 E))) v))
          ∂W₁.quotMeasure =
        ρ h * I₀ / (𝔠.character.baseChange.val (realIdele (infiniteDet B)) *
            √(ideleAbs (realIdele (infiniteDet B))) ^ card n) *
          thetaOnRealData W₁ V' γ β f x (g, y) (realSlice D V' B v')

/-- `thetaOnRealData` is homogeneous in the vector `F`. -/
lemma thetaOnRealData_smul (α γ : AutChar E) (κ : ℂ) (F : 𝒮 (W₁.hom V)) (x : Matrix a n (𝔸 E))
    (p : G E s × G E t) (φ : PairFock E s t) :
    thetaOnRealData W₁ V α γ (κ • F) x p φ = κ * thetaOnRealData W₁ V α γ F x p φ := by
  simp [thetaOnRealData]

/-- Let `𝔠` be a tame character of weight `μ`, `ν = 𝔠.character` and `υ` the splitting character of
the Weil data; write `n` also for the rank of `W₁`. The functional `thetaOnRealData` sends a real
datum `φ` in the Fock space `PairFock` of `(W₁, V)` to `θ(ϱ(x) ω(g, k) (φ ⊗ F))`. Here `θ` is the
theta distribution, `ϱ` the Heisenberg translation by `x`, and `ω` the Weil representation of the
pair with characters `rankTwist 𝔠.character⁻¹ n = ν⁻¹ υ ^ ⌊n / 2⌋` and `γ`. For `w ∈ GInf`, a point
of the unitary group at the infinite places, let `(w, 1)` be the point of `G E t` equal to `w` at
the infinite places and to `1` at the finite places. Multiplying `k` on the right by `(w, 1)` has
the same effect as moving `φ` by `w` in the real Weil representation `realPairWeil`. There `w` acts
by its Fock operator times `∏_τ det (w τ) ^ (⌊n / 2⌋ - μ τ)`. -/
lemma thetaOnRealData_mul_real (γ : AutChar E) (F : 𝒮 (W₁.hom V)) (x : Matrix a n (𝔸 E))
    (g : G E s) (k : G E t) (w : GInf E t) (φ : PairFock E s t) :
    thetaOnRealData W₁ V (rankTwist 𝔠.character⁻¹ n) γ F x (g, k * (w, 1)) φ =
      thetaOnRealData W₁ V (rankTwist 𝔠.character⁻¹ n) γ F x (g, k)
        (realPairWeil (fun τ : NumberField.InfinitePlace E ↦ card n / 2 - μ τ) 0 (1, w) φ) := by
  have h_split : ((g, k * (w, 1)) : G E s × G E t) = (g, k) * (1, w, 1) := by simp
  simp only [h_split, thetaOnRealData, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ← rep_apply_apply, pairWeil_integrated_right, sub_eq_add_neg]
  rfl

omit [WeilData E] in
/-- The inverse of `(y ⊕ y') k` maps the columns `(Y, 0)` to `k⁻¹ (y⁻¹ Y, 0)`. -/
lemma adeleMatrix_inv_sum_mul_mul_fromRows (y : G E t') (y' : G E s) (k : G E (t' ⊕ᵥ s))
    (Y : Matrix b b (𝔸 E)) :
    (G.sum (y, y') * k)⁻¹.adeleMatrix * fromRows Y (0 : Matrix n b (𝔸 E)) =
      k⁻¹.adeleMatrix * fromRows (y⁻¹.adeleMatrix * Y) (0 : Matrix n b (𝔸 E)) := by
  simp [← map_inv, Matrix.mul_assoc, fromBlocks_mul_fromRows]

open scoped Classical in
/-- Let `D` split `X` as `W₁`, of even rank `n`, plus a hyperbolic space, let `lFrame` be the
L-block of the dual frame at the ramified places of `𝔠`, and let
`p = radicalElement c z * levi (q, g)` with `q = scaleIdele • V'.x * Y`, where the finite part of
`Y` times some `k ∈ GL_b(Ô E)` (`intGL`) is in the unitary group `U 1` of the form `1`. Let
`IsPeriodIdentity` hold: at every real point, the integral over `[U W₁]` (for `quotMeasure`) of the
theta functional of the moved slice of `v` is the weight `ρ` times the period `I₀`, divided by
`ν(ζ / ζ̄) |ζ| ^ (n / 2)` for the infinite part `ζ` of a determinant, times that of the slice of
`v'`; here `ν = 𝔠.character`. Let the row datum of `lFrame` be `ε` times the standard datum of the
frame. For a point `(gInf, u)` of `U (V' ⊕ W₁)` there is `k'` in `U V' × U W₁` such that the term at
`(1; 0)` of the large theta kernel at `p`, integrated over the translates of `k' (gInf, u)` by
`U V' × [U W₁]`, equals `ρ gInf * (κ₀ ε ν(d₀ / d̄₀) I₀)` times the integral over `U V'` of the term
at `1` of the small theta kernel; it is zero if no block diagonal translate `blockSumOne u₀ * u`
lies in `stdLevel`. The constants `d₀` and `κ₀` depend only on the spaces and `D`. -/
lemma exists_integral_thetaTerm_eq_of_periods {σ' : b ⊕ b ⊕ n ≃ m} {v : PairFock E r (t' ⊕ᵥ s)}
    {v' : PairFock E r t'} {ρ : GInf E (t' ⊕ᵥ s) → ℝ} {I₀ ε : ℂ} (hn : 2 ∣ card n)
    (h_period : IsPeriodIdentity X D V' 𝔠 v v' ρ I₀)
    (h_std : stdRowDatum σ' 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL =
      (adaptedFrame 𝔠.readsAt D).stdDatum fun x :
        Matrix (b ⊕ n) (b ⊕ n) (LocProd 𝔠.ramifiedPlaces) ↦
        ε * invOnUnits 𝔠.semilocalChar x.det)
    (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (g : G E s) {Y : GL b (𝔸 E)} {k : GL b (𝔸f E)}
    (hk : k ∈ intGL b (Ô E))
    (hY : Y.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)) * k ∈ U 1)
    (gInf : GInf E (t' ⊕ᵥ s)) (u : Gf E (b ⊕ n)) :
    let p : G E r := D.radicalElement c z * D.levi (scaleIdele E • V'.x * Y, g)
    let lFrame : Matrix b m (LocProd 𝔠.ramifiedPlaces) := (adaptedFrame 𝔠.readsAt D).dualL
    let d₀ : (𝔸 E)ˣ := (scaleIdele E • V'.x).det
    let κ₀ : ℂ := vacuumFactor (isAdapted_homSource D (V'.sum W₁)) /
      vacuumFactor (isAdapted_homSource D V') * √(ideleAbs d₀) ^ card n
    ∃ k' : G E t' × G E s,
      ∫ y : G E t', ∫ y' : G E s,
          D.thetaTerm (V'.sum W₁) (rankTwist 𝔠.character⁻¹ m) (rankTwist 𝔠.character⁻¹ m)
            (localDatum X (V'.sum W₁) v (stdRowDatum σ' 𝔠.semilocalChar lFrame) 𝔠.readsAt) p
              (fromRows 1 0)
            (G.sum (y, y') * (G.sum k' * (gInf, u))) ∂W₁.quotMeasure =
        (if ∃ u₀ : Gf E b × Gf E n, U.blockSumOne u₀ * u ∈ stdLevel E (b ⊕ n) then (ρ gInf : ℂ)
          else 0) * (κ₀ * ε * 𝔠.character.baseChange.val d₀ * I₀ *
            ∫ y : G E t', D.thetaTerm V' (rankTwist 𝔠.character m) (upsilonU1 ^ card b)
              (localDatum X V' v' (fun w : Matrix b m (LocProd 𝔠.ramifiedPlaces) ↦
                stdColDatum 𝔠.semilocalChar lFrame wᵀ)
                𝔠.readsAt.star) p 1 y) := by
  intro p lFrame d₀ κ₀
  obtain ⟨N, hN⟩ := hn
  have h_lFrame : IsIntMatrix O lFrame :=
    (adaptedFrame 𝔠.readsAt D).blockRelations.isIntMatrix_dualL
  split_ifs with hu
  swap
  · -- If `u` is not in `(U V' × U W₁) * stdLevel`, no lattice condition holds and all terms vanish.
    use 1
    simp only [p, lFrame, map_one, one_mul, thetaTerm_stdRowDatum_eq X D V' 𝔠 v h_std c z g Y _ rfl,
      ite_eq_right fun h_int ↦ hu (exists_blockSumOne_mul_mem_stdLevel hk hY h_int), zero_mul,
      mul_zero, integral_zero]
  -- Otherwise translate by `(δ₁, δ₂)` at infinity and `(u₁, u₂)` at the finite places; compare at
  -- each `y ∈ U V'`.
  obtain ⟨⟨δ₁, δ₂⟩, h_identity⟩ := h_period gInf
  obtain ⟨⟨u₁, u₂⟩, hu₀⟩ := hu
  let k' : G E t' × G E s := ((δ₁.1, u₁), (δ₂.1, u₂))
  use k'
  simp_rw [← integral_const_mul]
  congr with y
  -- `x` is the finite part of `B = y⁻¹ Y`
  let B : GL b (𝔸 E) := y⁻¹.toUnitary * Y
  let x : GL b (𝔸f E) := y.2⁻¹ * Y.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))
  -- The standard datum is fixed by `stdLevel`, so the finite part of the translate drops out.
  let w : G E (t' ⊕ᵥ s) := ((G.sum (δ₁, δ₂)).1 * gInf, 1)
  have h_translate (y' : G E s) : G.sum (y, y') * (G.sum k' * (gInf, u)) =
      G.sum (y, y') * w * (1, U.blockSumOne (u₁, u₂) * u) := by
    simp [w, k', G.sum]
  have h_fin_small : (y⁻¹.adeleMatrix * Y.val).map Prod.snd = x.val :=
    map_snd_adeleMatrix_inv_mul y Y.val
  have h_fin_large (y' : G E s) : ((G.sum (y, y') * w)⁻¹.adeleMatrix *
      fromRows Y.val (0 : Matrix n b (𝔸 E))).map Prod.snd = fromRows x.val 0 := by
    rw [map_snd_adeleMatrix_inv_mul]
    simp [w, G.sum, U.sum, x, blockGL, fromRows_map, fromBlocks_mul_fromRows]
  have h_int_iff : IsIntMatrix (Ô E) (fromRows x.val (0 : Matrix n b (𝔸f E))) ↔
      IsIntMatrix (Ô E) x.val := by simp [IsIntMatrix]
  simp_rw [h_translate, thetaTerm_stdRowDatum_mul_of_mem_stdLevel X D _ 𝔠 σ' h_lFrame hu₀, p,
    lFrame,
    fun y' : G E s ↦ thetaTerm_stdRowDatum_eq X D V' 𝔠 v h_std c z g Y _ (h_fin_large y'),
    thetaTerm_stdColDatum_eq X D V' 𝔠 v' c z g Y y h_fin_small, h_int_iff, integral_const_mul]
  -- Both terms vanish unless `x` is integral, and then `det x` is a unit.
  split_ifs with hx
  on_goal 2 => ring
  have det_unit : x.det ∈ idelesUnitOff ∅ :=
    det_mem_idelesUnitOff_of_mul_mem hk hx (by simp [x, mul_assoc, mul_mem, hY])
  -- The finite slices are multiples of the vector in `h_identity` and of the vacuum.
  rw [namedVector_det_fromCols_eq_boxProd V' 𝔠 ε hx, namedVector_det_star_eq_vacElem V' 𝔠 x,
    rankTwist_eq_mul_of_splitting D]
  -- Bring the integrand over `[U W₁]` into the form of `h_identity`: the real point `w` acts
  -- through the real slice.
  have h_slice (y' : G E s) : (G.sum (y, y') * w)⁻¹.adeleMatrix * fromRows (m₂ := n) Y.val 0 =
      w⁻¹.adeleMatrix * fromRows (m₂ := n) B.val 0 := adeleMatrix_inv_sum_mul_mul_fromRows ..
  simp_rw [h_slice, w, thetaOnRealData_mul_real, thetaOnRealData_smul, fromRows_mul,
    Matrix.zero_mul, integral_const_mul]
  rw [h_identity B]
  -- Compare the scalars: `det B = det Y / det y` splits into an infinite and a finite factor;
  -- `det y` is unitary and `det x` is a unit of `Ô E`, so both have absolute value `1`.
  have det_inf : realIdele (infiniteDet B) = B.det * (finIdeleIncl x.det)⁻¹ := eq_mul_inv_of_mul_eq
    (det_eq_realIdele_mul_finIdeleIncl (Matrix.map_mul (f := RingHom.snd _ _))).symm
  have det_y : y.toUnitary.val.det = Unitary.toUnits y.det := Units.ext rfl
  have abs_inf : ideleAbs (realIdele (infiniteDet B)) = ideleAbs Y.det := by
    rw [det_inf]
    simp [B, det_y, ideleAbs_eq_one_of_mem_unitary, ideleAbs_finIdeleIncl_eq_one det_unit]
  -- on a unit `ζ` of `Ô E`, `χ⁻¹ (ζ̄) = χ⁻¹ (ζ) * ν (ζ / ζ̄)`
  have cut_star : invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces x.det) *
    𝔠.character.baseChange.finPart x.det =
      invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces (star x.det)) :=
    eq_of_div_eq_one (𝔠.invOnUnits_mul_finPart_div_star_eq_one det_unit)
  -- the two functionals of `(W₁, V')` differ by the factor `ν (det y) ^ 2`
  have h_twist (β : AutChar E) (f : 𝒮 (W₁.hom V')) (c' : Matrix b n (𝔸 E)) (φ : PairFock E s t') :
      thetaOnRealData W₁ V' (rankTwist 𝔠.character n) β f c' (g, y) φ =
        (𝔠.character.val y.det : ℂ) ^ 2 * thetaOnRealData W₁ V' (rankTwist 𝔠.character⁻¹ n) β f c'
          (g, y) φ := by
    simp [thetaOnRealData, rankTwist, pairWeil, sq, mul_assoc]
  rw [abs_inf, det_inf, ← cut_star, h_twist]
  simp [HeckeChar.finPart, rankTwist, AutChar.spaceChar, AutChar.baseChange_toUnits, det_y, κ₀, hN,
    B, G.adeleMatrix, Matrix.mul_assoc]
  field (disch := simp)

/-- Let `D` split `X` as `W₁` plus a hyperbolic space, let `𝔠` be a tame character, let `v` be a
Schwartz vector in the real (Fock) data `PairFock` of `(X, V' ⊕ W₁)`, and take the row datum
`stdRowDatum` of the L-block of the dual frame of `D` at the ramified places of `𝔠`. At the point
`radicalElement c z * levi (q, g)` of the parabolic subgroup, (a) the terms of the large theta
kernel, that of `(X, V' ⊕ W₁)`, are integrable, and (b) the Fourier coefficient of `thetaLarge` at
`j • T`, with `j` the purely imaginary element of the Weil data, vanishes under two conditions: `T`
is not of the form `yᴴ diag(t') y` at some infinite place (`¬RepresentedBy`), while the Gram matrix
of every `x` at which the real slice of `v` is non-zero has this form at all infinite places. -/
lemma hasIntegrableTerms_and_centreCoeff_thetaLarge_eq_zero (σ' : b ⊕ b ⊕ n ≃ m)
    {v : PairFock E r (t' ⊕ᵥ s)} (hv : IsSchwartzVector v) (c : Matrix n b (𝔸 E))
    (z : Matrix b b (𝔸 E)) (q : GL b (𝔸 E)) (g : G E s) :
    let Φ : Matrix (b ⊕ n) m (LocProd 𝔠.ramifiedPlaces) → ℂ :=
      stdRowDatum σ' 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL
    let p : G E r := D.radicalElement c z * D.levi (q, g)
    D.HasIntegrableTerms (V'.sum W₁) (rankTwist 𝔠.character⁻¹ m) (rankTwist 𝔠.character⁻¹ m)
        (localDatum X (V'.sum W₁) v Φ 𝔠.readsAt) p ∧
      ∀ T : Matrix b b E, ¬RepresentedBy t' (T.map toAdele) →
        SlicesVanishOutside D (V'.sum W₁) t' v →
        D.centerCoeff ((j : E) • T) (thetaLarge X (V'.sum W₁) 𝔠 v Φ) p = 0 := by
  obtain ⟨ε, -, h_std⟩ := (adaptedFrame 𝔠.readsAt D).exists_stdRowDatum_eq_stdDatum
    (χ := 𝔠.semilocalChar) σ'
  obtain ⟨⟨h_int, -⟩, h_zero⟩ := thetaTerm_eq_and_centreCoeff_eq_zero W₁ D (V'.sum W₁) 𝔠.readsAt
    (rankTwist 𝔠.character⁻¹ m) 𝔠.semilocalChar ε 1 (stdRowDatum_mem σ' 𝔠.semilocalChar)
      (by simpa using h_std) hv
    (rankTwist_eq_mul_of_splitting (ν := 𝔠.character⁻¹) D) c z q g
  exact ⟨h_int, h_zero t'⟩

/-- Let `D` split `X` as `W₁` plus a hyperbolic space, `V'` have rank `b` and signs `t'`, and `𝔠` be
a tame character. Let `v'` be a Schwartz vector in the real (Fock) data `PairFock` of `(X, V')` and
take the column datum `stdColDatum` for the L-block `l` of the dual frame of `D`, used at the
conjugates of the ramified places. At the point `radicalElement c z * levi (q, g)`, (a) the terms of
the small theta kernel, that of `(X, V')`, are integrable, and (b) the Fourier coefficient of
`thetaSmall` at `j • T`, with `j` the purely imaginary element of the Weil data, vanishes if the
signs `t'` do not represent `T` at the infinite places. -/
lemma hasIntegrableTerms_and_centreCoeff_thetaSmall_eq_zero {v' : PairFock E r t'}
    (hv' : IsSchwartzVector v') (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (q : GL b (𝔸 E))
    (g : G E s) :
    let Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ :=
      stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL
    let p : G E r := D.radicalElement c z * D.levi (q, g)
    D.HasIntegrableTerms V' (rankTwist 𝔠.character m) (upsilonU1 ^ card b)
        (localDatum X V' v' (fun y : Matrix b m (LocProd 𝔠.ramifiedPlaces) ↦ Ψ yᵀ) 𝔠.readsAt.star) p
          ∧
      ∀ T : Matrix b b E, ¬RepresentedBy t' (T.map toAdele) →
        D.centerCoeff ((j : E) • T) (thetaSmall X V' 𝔠 v' Ψ) p = 0 := by
  obtain ⟨⟨h_int, -⟩, h_zero⟩ := thetaTerm_eq_and_centreCoeff_eq_zero W₁ D V' 𝔠.readsAt.star
    (upsilonU1 ^ card b) 𝔠.semilocalChar 1 (fromRows 1 0)
      (stdColDatum_mem_schwartzBruhat 𝔠.semilocalChar
      (adaptedFrame 𝔠.readsAt D).blockRelations.isIntMatrix_dualL).transpose_mem_schwartzBruhat
    (stdColDatum_transpose_eq_stdDatum X D 𝔠) hv' (rankTwist_eq_mul_of_splitting D) c z q g
  -- the Gram matrix of any `x` in `V'` is represented by `t'`
  exact ⟨h_int, fun T hT ↦ h_zero t' T hT fun x _ w ↦ ⟨atRealPlace x w, gram_atRealPlace x w⟩⟩

/-- Let the adapted splitting `D` split `X` as `W₁`, of even rank, plus a hyperbolic space, and let
`σ' : b ⊕ b ⊕ n ≃ m` order the rows of a row datum. Let `v`, `v'` be Schwartz vectors in the real
(Fock) data `PairFock` of `(X, V' ⊕ W₁)`, `(X, V')` and let `ρ ≥ 0` be nonzero near `1`. The real
class of `V'` consists of the matrices of the form `yᴴ diag(t') y` at every infinite place
(`RepresentedBy t'`). Suppose that the real slices of `v` vanish at the points with Gram matrix
outside this class, or that `t' = -1` and the signs `s` contain a `1` with at most half of them
(`negCount`) equal to `-1`. Then there is `K > 0` such that, for every tame character `𝔠` of weight
`μ` (`SplitTameChar`), if `IsPeriodIdentity` holds with weight `ρ` and period `I₀`, there is a
number `C` with `‖C‖ = K * ‖I₀‖` and the following property. At the point
`radicalElement c z * levi (q, g)` the Fourier coefficient at `j • T` of `thetaLarge`, the theta
integral of `(X, V' ⊕ W₁)` on `v` and the row datum `stdRowDatum σ'` of the frame
`(adaptedFrame 𝔠.readsAt D).dualL`, is `C` times that of `thetaSmall`, the one of `(X, V')` on `v'`
and the column datum `stdColDatum` of that frame, if `(T, q)` is a test pair for `V'`: (a) `T` is
the form of `V'` and `q` is `scaleIdele E` times a basis of a lattice that is self-dual for `T`, or
(b) `T` is invertible and outside the real class of `V'`. -/
lemma exists_centreCoeff_eq_mul_of_isPeriodIdentity {σ' : b ⊕ b ⊕ n ≃ m}
    {v : PairFock E r (t' ⊕ᵥ s)}
    {v' : PairFock E r t'} (hn : 2 ∣ card n) {ρ : GInf E (t' ⊕ᵥ s) → ℝ} (hρ₀ : 0 ≤ ρ)
    (hρ_ne_near_one : ∀ᶠ h : GInf E (t' ⊕ᵥ s) in nhds 1, ρ h ≠ 0) (hv : IsSchwartzVector v)
    (hv' : IsSchwartzVector v')
    (h_vanish_or_signs : SlicesVanishOutside D (V'.sum W₁) t' v ∨
      t' = -1 ∧ (∃ i : n, s i = 1) ∧ 2 * negCount s ≤ card n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (𝔠 : SplitTameChar E μ) (I₀ : ℂ), IsPeriodIdentity X D V' 𝔠 v v' ρ I₀ →
      ∃ C : ℂ, ‖C‖ = K * ‖I₀‖ ∧
      ∀ (T : Matrix b b E) (c : Matrix n b (𝔸 E)) (z : Matrix b b (𝔸 E)) (q : GL b (𝔸 E))
          (g : G E s), IsSelfDualTestPair V' T q →
        D.centerCoeff ((j : E) • T)
            (thetaLarge X (V'.sum W₁) 𝔠 v
              (stdRowDatum σ' 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL))
            (D.radicalElement c z * D.levi (q, g)) =
          C * D.centerCoeff ((j : E) • T)
            (thetaSmall X V' 𝔠 v' (stdColDatum 𝔠.semilocalChar (adaptedFrame 𝔠.readsAt D).dualL))
            (D.radicalElement c z * D.levi (q, g)) := by
  -- In case (a) each coefficient is the integral of one term of the theta kernel. The integral for
  -- the large side is unfolded in stages through `U V' × U W₁`, with the weight `ρ`, and the inner
  -- integral is computed by `exists_integral_thetaTerm_eq_of_periods`.
  classical
  -- the weight `ρ`, cut off at the finite places
  let ρ' : G E (t' ⊕ᵥ s) → ℂ := fun g ↦
    if ∃ u₀ : U 1 × U 1, U.blockSumOne u₀ * g.2 ∈ stdLevel E (b ⊕ n) then ρ g.1 else 0
  have hρ'_nonneg (g : G E (t' ⊕ᵥ s)) : 0 ≤ (ρ' g).re := by
    simpa [ρ', apply_ite Complex.re] using ite_nonneg (hρ₀ g.1) le_rfl
  have hρ'_ne : ∀ᶠ g : G E (t' ⊕ᵥ s) in nhds 1, (ρ' g).re ≠ 0 := by
    refine (hρ_ne_near_one.prod_nhds (isOpen_stdLevel.mem_nhds (one_mem _))).mono
      fun g ⟨hg_inf, hg_fin⟩ ↦ ?_
    unfold ρ'
    rwa [ite_eq_left ⟨1, by rwa [map_one, one_mul]⟩]
  -- `R ≠ 0` is the constant of unfolding in stages for `ρ'`
  obtain ⟨R, hR, h_stages⟩ := exists_integral_stages_eq_mul W₁.Γ volume volume volume G.sum
    G.isClosedEmbedding_sum ρ' hρ'_nonneg hρ'_ne
  let d₀ : (𝔸 E)ˣ := (scaleIdele E • V'.x).det
  let κ₀ : ℂ := vacuumFactor (isAdapted_homSource D (V'.sum W₁)) /
    vacuumFactor (isAdapted_homSource D V') * √(ideleAbs d₀) ^ card n
  refine ⟨‖R * κ₀‖, norm_pos_iff.2 (mul_ne_zero hR (by simp [κ₀])), fun 𝔠 I₀ h_period ↦ ?_⟩
  -- up to a constant `ε` of norm `1`, the row datum is the standard datum of the local frame of `D`
  obtain ⟨ε, hε, h_std⟩ := (adaptedFrame 𝔠.readsAt D).exists_stdRowDatum_eq_stdDatum
    (χ := 𝔠.semilocalChar) σ'
  refine ⟨R * (κ₀ * ε * 𝔠.character.baseChange.val d₀ * I₀),
    by simp [hε, mul_assoc, Circle.norm_coe],
    fun T c z q g hT ↦ ?_⟩
  obtain ⟨int_large, zero_large⟩ :=
    hasIntegrableTerms_and_centreCoeff_thetaLarge_eq_zero X D V' 𝔠 σ' hv c z q g
  obtain ⟨int_small, zero_small⟩ :=
    hasIntegrableTerms_and_centreCoeff_thetaSmall_eq_zero X D V' 𝔠 hv' c z q g
  obtain ⟨Y, k, hk, rfl, hY, rfl⟩ | ⟨h_unit, h_real⟩ := hT
  · -- At `V'.J` each coefficient is the integral of one term: that of `fromRows 1 0`, whose
    -- stabiliser is `W₁.Γ`, and that of `1`, whose stabiliser is trivial.
    obtain ⟨inv_large, integrable_large, coeff_large⟩ :=
      D.centreCoeff_eq_integral_stabilizer int_large continuous_const (by simp)
        (by simpa only [gram_sum_fromRows_one_zero] using V'.isUnit_J)
        (mem_map_sum_iff_fixes_cols V')
    obtain ⟨-, -, coeff_small⟩ := D.centreCoeff_eq_integral_stabilizer int_small continuous_const
      (by simp) (x₀ := 1) (S := ⊥) (by simp) (by simp [eq_comm])
    simp only [mul_one, conjTranspose_one, one_mul, quotMeasure_bot, gram_sum_fromRows_one_zero]
      at inv_large integrable_large coeff_large coeff_small
    -- Unfold the integral over `W₁.Γ \ U (V' ⊕ W₁)` in stages through `U V' × U W₁`.
    have h_unfold := h_stages _ (by unfold Splitting.thetaTerm; fun_prop) inv_large
      integrable_large _ fun ⟨h, u⟩ ↦
        exists_integral_thetaTerm_eq_of_periods X D V' 𝔠 hn h_period h_std c z g hk hY h u
    rw [← coeff_small, ← mul_assoc R] at h_unfold
    exact coeff_large.trans h_unfold
  · -- Outside the real class both coefficients vanish: for the large side either by the support
    -- of the slices or, when `t' = -1`, by the signs (`centreCoeff_eq_zero_of_not_representedBy`).
    rw [zero_small T h_real, mul_zero]
    obtain h_supp | ⟨ht', ⟨i, hi⟩, h_neg⟩ := h_vanish_or_signs
    · exact zero_large T h_real h_supp
    refine centreCoeff_eq_zero_of_not_representedBy (.inr i) (fun τ ↦ ?_) hi (by simp [ht'])
      (rankTwist_eq_mul_of_splitting D) h_unit (by rwa [← ht']) int_large
    obtain ⟨N, hN⟩ : ∃ N : ℕ, card n = 2 * N := hn
    suffices (N : ℤ) < negCount (-s) + μ τ by simpa [hN]
    linarith [negCount_neg_add s, 𝔠.weight_pos τ]

/-- Let `D` split `X` as `W₁` plus a hyperbolic space, where `W₁` has even rank, and let `D₁` split
`W₁` as `W` plus a hyperbolic plane. Let both splittings be adapted. Let `v`, `v'` be Schwartz
vectors in the real (Fock) data `PairFock` of `(X, V' ⊕ W₁)`, `(X, V')` and let `ρ ≥ 0` be nonzero
near `1`. Suppose that the real slices of `v` vanish at the points whose Gram matrix is not
represented by the signs `t'` of `V'`, or that `t' = -1` and the signs `s` of `W₁` contain a `1`
with at most half of them equal to `-1`. Then there is `K > 0` such that for every tame character
`𝔠` of weight `μ`, if `IsPeriodIdentity` holds with weight `ρ` and period `I₀`, then there is a
number `C` with `‖C‖ = K * ‖I₀‖` such that for every integral `z` at the ramified places the theta
integral `thetaLarge` of `(X, V' ⊕ W₁)` on `v` and the row datum `stdRowDatum σ' χ z` (`χ⁻¹ ∘ det`
of the rows of `z` and the variable, ordered by `σ'`, where `χ = 𝔠.semilocalChar`) is `C` times the
theta integral `thetaSmall` of `(X, V')` on `v'` and the column datum `x ↦ χ⁻¹ (det (z x))`. -/
lemma exists_thetaLarge_eq_smul_of_isPeriodIdentity [IsBaseAdapted D₁] {σ' : b ⊕ b ⊕ n ≃ m}
    {v : PairFock E r (t' ⊕ᵥ s)} {v' : PairFock E r t'} (hn : 2 ∣ card n)
    {ρ : GInf E (t' ⊕ᵥ s) → ℝ} (hρ₀ : 0 ≤ ρ)
    (hρ_ne_near_one : ∀ᶠ h : GInf E (t' ⊕ᵥ s) in nhds 1, ρ h ≠ 0)
    (hv : IsSchwartzVector v) (hv' : IsSchwartzVector v')
    (h_vanish_or_signs : SlicesVanishOutside D (V'.sum W₁) t' v ∨
      t' = -1 ∧ (∃ i : n, s i = 1) ∧ 2 * negCount s ≤ card n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (𝔠 : SplitTameChar E μ) (I₀ : ℂ), IsPeriodIdentity X D V' 𝔠 v v' ρ I₀ →
      ∃ C : ℂ, ‖C‖ = K * ‖I₀‖ ∧ ∀ z : Matrix b m (LocProd 𝔠.ramifiedPlaces), IsIntMatrix O z →
        thetaLarge X (V'.sum W₁) 𝔠 v (stdRowDatum σ' 𝔠.semilocalChar z) =
          C • thetaSmall X V' 𝔠 v' (stdColDatum 𝔠.semilocalChar z) := by
  -- The difference `𝒟` of the two sides is a linear map on data for `V'`. At one standard datum
  -- it vanishes at self-dual lattices (`exists_centreCoeff_eq_mul_of_isPeriodIdentity`);
  -- `IsEquivariantLift.apply_eq_zero_of_areMatched` then gives `𝒟 = 0` on all standard data.
  obtain ⟨K, hK, h_coeff⟩ :=
    exists_centreCoeff_eq_mul_of_isPeriodIdentity X D V' (μ := μ) (σ' := σ') hn hρ₀ hρ_ne_near_one
      hv hv'
      h_vanish_or_signs
  refine ⟨K, hK, fun 𝔠 I₀ h_period ↦ ?_⟩
  obtain ⟨C, hC, coeff_eq⟩ := h_coeff 𝔠 I₀ h_period
  have hm : 2 ∣ card m := (dvd_add hn (dvd_mul_right 2 _)).trans D.card_eq.symm.dvd
  obtain ⟨M, 𝒟, h_rep, h𝒟⟩ := exists_isEquivariantLift_eq_thetaLarge_sub_smul X (V'.sum W₁) V' 𝔠 σ'
    hm hv hv' C
  have 𝒟_std {z : Matrix b m (LocProd 𝔠.ramifiedPlaces)} (hz : IsIntMatrix O z) :
      stdColDatum 𝔠.semilocalChar z ∈ M ∧ 𝒟 (stdColDatum 𝔠.semilocalChar z) =
        thetaLarge X (V'.sum W₁) 𝔠 v (stdRowDatum σ' 𝔠.semilocalChar z) -
          C • thetaSmall X V' 𝔠 v' (stdColDatum 𝔠.semilocalChar z) :=
    h𝒟 (stdColDatum_mem_schwartzBruhat _ hz).1 (areMatched_stdRowDatum_stdColDatum σ' hz)
  refine ⟨C, hC, fun z hz ↦ sub_eq_zero.1 ?_⟩
  set z₀ : Matrix b m (LocProd 𝔠.ramifiedPlaces) := (adaptedFrame 𝔠.readsAt D).dualL
  have hz₀ : IsIntMatrix O z₀ := (adaptedFrame 𝔠.readsAt D).blockRelations.isIntMatrix_dualL
  obtain ⟨h_mem₀, h_diff₀⟩ := 𝒟_std hz₀
  rw [← (𝒟_std hz).right]
  refine h_rep.apply_eq_zero_of_areMatched D D₁ V' (fun T c y q g hT ↦ ?_) h_mem₀
    (stdColDatum_mem_schwartzBruhat _ hz).1 (areMatched_stdRowDatum_stdColDatum σ' hz)
  -- the coefficient of `𝒟` at `z₀` is the difference of the two sides of `coeff_eq`
  let F : G E r → ℂ := thetaLarge X (V'.sum W₁) 𝔠 v (stdRowDatum σ' 𝔠.semilocalChar z₀)
  let F' : G E r → ℂ := thetaSmall X V' 𝔠 v' (stdColDatum 𝔠.semilocalChar z₀)
  let p : G E r := D.radicalElement c y * D.levi (q, g)
  have hF : IsAutFunction X F :=
    (𝔠.readsAt.isTargetBounded hv (stdRowDatum_mem σ' 𝔠.semilocalChar)).isAutFunction_thetaIntegral
  have hF' : IsAutFunction X F' := (𝔠.readsAt.star.isTargetBounded hv'
    (stdColDatum_mem_schwartzBruhat 𝔠.semilocalChar hz₀).transpose_mem_schwartzBruhat
    ).isAutFunction_thetaIntegral
  calc D.centerCoeff ((j : E) • T) (𝒟 (stdColDatum 𝔠.semilocalChar z₀)) p
      = D.centerCoeff ((j : E) • T) F p - C * D.centerCoeff ((j : E) • T) F' p := by
        simpa only [h_diff₀, mul_one] using
          D.centreCoeff_mul_right_sub_smul hF hF' C 1 ((j : E) • T) p
    _ = 0 := sub_eq_zero.2 (coeff_eq T c y q g hT)

/-- Let the adapted splittings `D` and `D₁` split `X` as `W₁` plus a hyperbolic space and `W₁`, of
even rank, as `W` plus a hyperbolic plane. Let `V = V' ⊕ W₁`, let `v`, `v'` be Schwartz vectors in
the real (Fock) data `PairFock` of `(X, V)`, `(X, V')`, and let `ρ ≥ 0` be nonzero near `1`. Suppose
(a): for every tame character `𝔠` of weight `μ`, `IsPeriodIdentity` holds with weight `ρ` and period
`period 𝔠`. Suppose (b): either the real slices of `v` vanish at the points whose Gram matrix is not
represented by the signs `t'` of `V'`, or `t' = -1` and the signs `s` of `W₁` contain a `1` with at
most half of them equal to `-1`. Then `RowColExchangeIdentity` holds with
`ℓ 𝔠 = ‖period 𝔠‖ ^ 2 / L_*(n / 2)`: there is a real `C` such that for every `𝔠` some `c : ℂ` has
`C * ‖c‖ ^ 2 = L_*(rk V - rk X / 2) * ℓ 𝔠` and, for all integral `z`, the theta integral
`thetaLarge` of `(X, V)` on `v` and the row datum of `z` is `c` times the theta integral
`thetaSmall` of `(X, V')` on `v'` and the column datum `x ↦ χ⁻¹ (det (z x))`. Here `n` is the rank
of `W₁` and `L_*(e) = lValueProdInt 𝔠 e` is `∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2`
for `ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`. -/
lemma rowColExchangeIdentity_of_periods [IsBaseAdapted D₁] {σ' : b ⊕ b ⊕ n ≃ m}
    {v : PairFock E r (t' ⊕ᵥ s)} {v' : PairFock E r t'} (period : SplitTameChar E μ → ℂ)
    (hn : 2 ∣ card n) {ρ : GInf E (t' ⊕ᵥ s) → ℝ} (hρ₀ : 0 ≤ ρ)
    (hρ_ne_near_one : ∀ᶠ h : GInf E (t' ⊕ᵥ s) in nhds 1, ρ h ≠ 0) (hv : IsSchwartzVector v)
      (hv' : IsSchwartzVector v')
    (h_period : ∀ 𝔠 : SplitTameChar E μ, IsPeriodIdentity X D V' 𝔠 v v' ρ (period 𝔠))
    (h_vanish_or_signs : SlicesVanishOutside D (V'.sum W₁) t' v ∨
      t' = -1 ∧ (∃ i : n, s i = 1) ∧ 2 * negCount s ≤ card n) :
    RowColExchangeIdentity X (V'.sum W₁) V' μ σ' v v' fun 𝔠 : SplitTameChar E μ ↦
      ‖period 𝔠‖ ^ 2 / lValueProdInt 𝔠 (card n / 2) := by
  obtain ⟨K, hK, h_identity⟩ :=
    exists_thetaLarge_eq_smul_of_isPeriodIdentity X D D₁ V' (μ := μ) (σ' := σ') hn hρ₀
      hρ_ne_near_one hv hv'
      h_vanish_or_signs
  choose C hC h_eq using fun 𝔠 : SplitTameChar E μ ↦ h_identity 𝔠 (period 𝔠) (h_period 𝔠)
  refine ⟨hv, hv', K⁻¹ ^ 2, fun 𝔠 ↦ ⟨C 𝔠, ?_, h_eq 𝔠⟩⟩
  -- `K` cancels, and `card (b ⊕ n) - card m / 2 = card n / 2`
  have h_rank : (card (b ⊕ n) : ℤ) - card m / 2 = card n / 2 := by grind [card_sum, D.card_eq]
  rw [hC, h_rank]
  field [(lValueProdInt_pos 𝔠 (card n / 2)).ne']

end New.Exchange
