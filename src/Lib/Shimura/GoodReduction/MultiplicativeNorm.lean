module

public import Aesop.BuiltinRules
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Topology.UniformSpace.Uniformizable
public import Lib.Shimura.ComplexTheta.DimensionFormula
import Lib.General.Analysis.GaussianIntegral
import Lib.PadicComparison.Descent.TestCategory
import Lib.Shimura.GoodReduction.TorsionSizes
import Lib.Shimura.Uniformisation.HolomorphicFamilies
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.Integral
public import Lib.Shimura.ThetaModuli.PELThetaTori
import Lib.General.NumberTheory.SUnitsAndClassNumber
import Lib.General.Topology

section
/-!
# Hermitian tori with multiplications, Gauss sums and unfolding of the Poincaré kernel

Let `V / L` be a complex torus with multiplications `F` by a ring `R` with involution and a
polarising hermitian form `B`. The hypothesis `New.ThetaTori.IsHermitianAction` gives the
compatibilities between these data.

## Main definitions and results

* `New.ThetaTori.IsHermitianAction`: `B` is positive hermitian, its Riemann form is integral on `L`,
  `F (star a)` is adjoint to `F a`, and `star β = 1 - β`.
* `New.ThetaTori.IsHermitianAction.isAppellHumbert`: the canonical multiplier
  `New.ThetaTori.IsHermitianAction.multiplier` of `F β` gives Appell–Humbert data.
* `New.ThetaTori.IsHermitianAction.MulKernel`, `New.ThetaTori.IsHermitianAction.card_mulKernel`: the
  kernel `a⁻¹ L / L` of `a ≠ 0` on the torus has order `|det (F a)|²`.
* `New.ThetaTori.IsHermitianAction.normShift_sum_eq_char_smul`: averaging normalised translates over
  this kernel against a character gives an eigenvector.
* `New.ThetaTori.IsHermitianAction.sum_conj_pow_four_eq_sum_pow_four`: a quadratic Gauss sum over
  `κ⁻¹ L / L` has a real fourth power.
* `New.ThetaTori.IsHermitianAction.isSelfAdjoint_quotMean_pow`: the mean of `x ↦ K(c̄ x, c x)` times
  `conj (det c̄)` has a real fourth power; unfolding writes the mean as a Gauss sum times a Gaussian
  integral.

Notions from other files:
* `New.RealComplexForm.riemannForm`: The Riemann form of B: the alternating real form
  E(u, v) = Im(B(u,v) − B(v,u))/(2π).
* `New.ThetaTori.normalizedShift`: The twisted translation `New.RealComplexForm.thetaShift`,
  f ↦ (z ↦ exp(−B(x, z) − B(x, x)/2) f(z + x)), divided by the canonical multiplier at x.
* `New.IsAppellHumbert`: Appell–Humbert data: Re B is symmetric, and on L one has |χ| = 1 and
  χ(l + m) = χ(l)χ(m)·exp(πi E(m, l)), E the Riemann form of B.
* `New.ThetaTori.LatticeForm.poincareSeries`:
  K(x, y) = ∑_{l ∈ L} exp(B(x, y − x + l) − B(l,y) − B(l,l)/2)/χ(l), the sum of the terms
  `New.ThetaTori.LatticeForm.poincareTerm`.

## Relation to the literature

Known; see `Lib.Shimura.GoodReduction.MultiplicativeNorm` for sources.
-/

@[expose] public section

noncomputable section

section HermitianAction

open Complex ComplexConjugate QuotientAddGroup LinearMap LinearEquiv NeZero Algebra.IsAlgebraic

namespace New.ThetaTori

variable {V R : Type} [FinComplexSpace V] [CommRing R] [StarRing R]
  (L : Submodule ℤ V) (B : LatticeForm L) (F : R →+* V →L[ℂ] V)
  (β : R) [IsDomain R] [Module.Finite ℤ R]

/-! ### Hermitian data and invertibility of multiplications -/

/-- B : LatticeForm L is a positive definite hermitian form on V, ℂ-valued and ℂ-linear in its
second argument, with Riemann form integral on L, the action F of R on the finite-dimensional
complex space V (`FinComplexSpace V`) preserves L with ā adjoint to a, and β̄ = 1 − β. -/
structure IsHermitianAction where
  /-- Every multiplication `F a` maps the lattice `L` into itself. -/
  map_mem (a : R) : ∀ l ∈ L, F a l ∈ L
  /-- The form `B` is hermitian. -/
  conj_symm (x y : V) : B x y = conj (B y x)
  /-- The form `B` is positive definite. -/
  pos : ∀ x ≠ (0 : V), 0 < (B x x).re
  /-- The adjoint of `F a` for `B` is `F (star a)`. -/
  adjoint (a : R) (x y : V) : B (F a x) y = B x (F (star a) y)
  /-- The Riemann form of `B` takes integer values on `L`. -/
  riemannForm_integral : ∀ l ∈ L, ∀ m ∈ L, ∃ n : ℤ, B.riemannForm l m = n
  /-- The element `β` and its conjugate add up to `1`. -/
  star_eq_one_sub : star β = 1 - β

variable {L B F β} {x y : V} {f : V → ℂ} (h : IsHermitianAction L B F β) (a : R) [NeZero a]

/-- `star a` is nonzero when `a` is. -/
instance : NeZero (star a) := ⟨by simp [NeZero.ne a]⟩

omit [StarRing R] [IsDomain R] [Module.Finite ℤ R] in
/-- The multiplications `F r` and `F s` commute, as `R` is commutative. -/
lemma action_comm (r s : R) (x : V) : F r (F s x) = F s (F r x) := by
  simpa using DFunLike.congr_fun (congrArg F (mul_comm r s)) x

omit [StarRing R] in
/-- A nonzero element of the domain `R`, finite over `ℤ`, acts injectively on `V`. -/
lemma action_injective : (⇑(F a)).Injective := by
  -- `a` divides a nonzero integer `r`, and `F r` is multiplication by `r` on a complex space.
  obtain ⟨b, r, hr, hab⟩ := exists_smul_eq_mul ℤ 1 (NeZero.ne a)
  intro x y hxy
  have h_key : F (r • 1) (x - y) = F (a * b) (x - y) := by rw [hab]
  -- the left side is `r • (x - y)` and the right side is `F b (F a x - F a y) = 0`
  have h_smul : (r : ℂ) • (x - y) = 0 := by
    simpa [hxy, action_comm a, ← Int.cast_smul_eq_zsmul ℂ] using h_key
  exact sub_eq_zero.mp ((smul_eq_zero.mp h_smul).resolve_left (Int.cast_ne_zero.mpr hr))

omit [StarRing R] in
/-- A nonzero element of `R` acts invertibly on the finite-dimensional space `V`. -/
@[simp]
lemma action_isInvertible : (F a).IsInvertible :=
  ⟨(ofInjectiveEndo _ (action_injective a)).toContinuousLinearEquiv, rfl⟩

namespace IsHermitianAction

/-! ### Multiplier, normalised translations and kernels -/

/-- The canonical multiplier x ↦ exp(πi E(βx, x)) of the hermitian data, where E is the Riemann
form of B. The hermitian data only fix `B`, `F` and `β`. -/
@[simp]
abbrev multiplier (_ : IsHermitianAction L B F β) : V → ℂ := canonicalMultiplier B (F β)

/-- Normalised translation by x, acting on functions V → ℂ: the twisted translation
`New.RealComplexForm.thetaShift` for B, divided by exp(πi E(βx, x)), E the Riemann form of B. The
hermitian data only fix `B`, `F` and `β`. -/
@[simp]
abbrev normShift (_ : IsHermitianAction L B F β) : V → (V → ℂ) →ₗ[ℂ] V → ℂ :=
  normalizedShift B (F β)

variable (L F) in
/-- The lattice a⁻¹L: the additive subgroup of the vectors y of V with ay in L, where a acts
through F. -/
def divLattice (a : R) : AddSubgroup V :=
  L.toAddSubgroup.comap (F a).toAddMonoidHom

/-- The kernel a⁻¹L / L of multiplication by a on the torus V/L. The hermitian action
provides the finite quotient instance. -/
abbrev MulKernel (_ : IsHermitianAction L B F β) : Type :=
    divLattice L F a ⧸ L.toAddSubgroup.addSubgroupOf (divLattice L F a)

omit [StarRing R] [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
@[simp]
lemma map_divLattice_mem (z : divLattice L F a) : F a z ∈ L := z.prop

omit [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
/-- The chosen representative of a class in a⁻¹L / L lies in L only for the zero class. -/
lemma out_mem_iff_eq_zero (z : h.MulKernel a) : z.out.val ∈ L ↔ z = 0 := by
  conv_rhs => rw [← out_eq' z, eq_zero_iff]
  rfl

section

omit [IsDomain R] [Module.Finite ℤ R]

/-- For hermitian data `h` and the Riemann form `E` of `B`: `E(β u, w) = E(u, w) - E(u, β w)`, so
that `F β` behaves as one half of the identity. -/
lemma riemannForm_apply_beta_eq_sub (h : IsHermitianAction L B F β) (u w : V) :
    B.riemannForm (F β u) w = B.riemannForm u w - B.riemannForm u (F β w) := by
  -- Move `F β` across the form by adjointness, and use `star β = 1 - β`.
  simp [riemannForm, h.adjoint, h.star_eq_one_sub]
  ring

/-- For hermitian data `h`, the canonical multiplier of `F β` (`h.multiplier`) and `B` are
Appell–Humbert data (`New.IsAppellHumbert`). -/
lemma isAppellHumbert (h : IsHermitianAction L B F β) : IsAppellHumbert B h.multiplier := by
  grind [isAppellHumbert_canonicalMultiplier, riemannForm_apply_beta_eq_sub, IsHermitianAction,
    conj_re]

/-- Let `x` lie in the dual lattice of `B` (`E(x, l)` is an integer for `l ∈ L`, `E` the Riemann
form) and let `F (star a) y ∈ L`. Then the phase `exp (2πi E(F a x, y))` is `1`. -/
lemma riemannPhase_eq_one (h : IsHermitianAction L B F β) {a : R} (hx : x ∈ B.dualLattice)
    (hy : F (star a) y ∈ L) :
    B.riemannPhase (F a x) y = 1 := by
  -- By adjointness the exponent is `2πi` times the integer `B.riemannForm x (F (star a) y)`.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, B.riemannForm x (F (star a) y) = n := hx _ hy
  have h_adj : B.riemannForm (F a x) y = n := by grind [riemannForm_def, h.adjoint, star_star]
  simp [h_adj, mul_comm _ (n : ℂ)]

/-- For `u, w ∈ L` the normalised translations by `u` and `w` compose to that by `u + w`: on `L`
the phase in their composition law is `1`. -/
lemma normShift_normShift_of_mem (h : IsHermitianAction L B F β) {u w : V} (hu : u ∈ L)
    (hw : w ∈ L) (g : V → ℂ) : h.normShift u (h.normShift w g) = h.normShift (u + w) g := by
  rw [h.isAppellHumbert.normalizedShift_normalizedShift h.riemannForm_apply_beta_eq_sub,
    h.riemannPhase_eq_one (h.riemannForm_integral u hu) (h.map_mem _ w hw), one_smul]

/-- Let `f` be fixed by the normalised translations by `a l`, `l ∈ L`. For `z ∈ a⁻¹ L`, the chosen
representative of the class of `z` in `a⁻¹ L / L` gives the same translate of `f` as `z`. -/
lemma normShift_map_out (h : IsHermitianAction L B F β) {a : R}
    (hf : ∀ l ∈ L, h.normShift (F a l) f = f) (z : divLattice L F a) :
    h.normShift (F a ((z : h.MulKernel a).out : V)) f = h.normShift (F a (z : V)) f := by
  -- the representative is `z + l` with `l ∈ L`, and the translation by `a l` fixes `f`
  obtain ⟨l, hl⟩ : ∃ l : L.toAddSubgroup.addSubgroupOf (divLattice L F a),
      (z : h.MulKernel a).out = z + l := mk_out_eq_add (L.toAddSubgroup.addSubgroupOf _) z
  have hz_mem : F a (z : V) ∈ L := z.property
  have hl_mem : ((l : divLattice L F a) : V) ∈ L := l.property
  rw [hl, AddSubgroup.coe_add, map_add,
    ← normShift_normShift_of_mem h hz_mem (h.map_mem a _ hl_mem), hf _ hl_mem]

/-- The canonical multiplier written with `B` and `F (star β)`, without the Riemann form: it equals
`exp (B x (F (star β) x) - B x x / 2)`. -/
lemma multiplier_eq_exp (h : IsHermitianAction L B F β) :
    h.multiplier x = exp (B x (F (star β) x) - B x x / 2) := by
  grind [canonicalMultiplier, h.isAppellHumbert.sub_eq_riemannForm, h.star_eq_one_sub, h.adjoint]

/-- Hermitian data stay hermitian data when `B` is multiplied by a positive integer `m`. -/
lemma nsmul (h : IsHermitianAction L B F β) {m : ℕ} (hm : m ≠ 0) :
    IsHermitianAction L (m • B) F β := by
  refine ⟨h.map_mem, fun x y ↦ ?_, fun x hx ↦ ?_, fun a x y ↦ ?_,
    (h.isAppellHumbert.nsmul m).le_dualLattice, h.star_eq_one_sub⟩
  · -- `m • B` is hermitian
    simp [← h.conj_symm]
  · -- `m • B` is positive definite
    simp [hm.pos, h.pos x hx]
  · -- `F (star a)` is adjoint to `F a` for `m • B`
    simp [h.adjoint]

end

variable [IsFullRankLattice L]

include h

/-! ### Finite kernels and their eigenvectors -/

/-- For hermitian data `h` and a full-rank lattice `L`, the kernel `a⁻¹ L / L` of multiplication by
`a ≠ 0` has order `det (F a) * conj (det (F a))`. -/
lemma card_mulKernel : Nat.card (h.MulKernel a) = (F a).det * conj (F a).det :=
  relIndex_comap_eq_det_mul_conj_det (h.map_mem a) (action_injective a)

instance : Fintype (h.MulKernel a) :=
  -- The index is `|det (F a)|²`, which is not zero as `F a` is injective.
  AddSubgroup.fintypeOfIndexNeZero (ne_of_apply_ne _ ((h.card_mulKernel a).trans_ne
    (by simp [det_eq_zero_iff_ker_ne_bot, ker_eq_bot, action_injective])))

/-- Let `h` be hermitian data and `a ≠ 0`. Let `f` be fixed by the normalised translations by `a l`,
`l ∈ L`, let `ξ` be a character of the finite kernel `a⁻¹ L / L`, and let
`s = ∑_k ξ(−k) • (normalised translate of f by a k.out)`, where `k.out` is the chosen
representative of the class `k`; the terms do not depend on that choice. For `y ∈ a⁻¹ L`, the
normalised translation by `a y` multiplies `s` by `ξ(y)`. -/
lemma normShift_sum_eq_char_smul (hf : ∀ l ∈ L, h.normShift (F a l) f = f)
    (ξ : AddChar (h.MulKernel a) ℂ) (y : divLattice L F a) {s : V → ℂ}
    (hs : s = ∑ k : h.MulKernel a, ξ (-k) • h.normShift (F a k.out) f) :
    h.normShift (F a y) s = ξ y • s := by
  -- Reindex the sum by `k ↦ y + k` and compare term by term.
  rw [hs, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (.addLeft ↑y) _ _ fun k ↦ ?_
  -- `y + k.out` represents `y + k`; its translate is that by `k.out` followed by that by `y`.
  have h_class : ((y + k.out : divLattice L F a) : h.MulKernel a) = y + k := by simp
  have h_term : h.normShift (F a ((y : h.MulKernel a) + k).out) f =
      h.normShift (F a y) (h.normShift (F a k.out) f) := by
    rw [← h_class, normShift_map_out h hf, AddSubgroup.coe_add, map_add,
      normShift_normShift_of_mem h (map_divLattice_mem (L := L) (F := F) a y)
          (map_divLattice_mem (L := L) (F := F) a k.out)]
  change h.normShift (F a y) (ξ (-k) • h.normShift (F a k.out) f) =
    ξ y • ξ (-(y + k)) • h.normShift (F a ((y : h.MulKernel a) + k).out) f
  rw [h_term, _root_.map_smul, smul_smul, ← ξ.map_add_eq_mul, neg_add, add_neg_cancel_left]

end IsHermitianAction

end New.ThetaTori

end HermitianAction

/-!
## Gauss sums and the mean of the Poincaré kernel

Here `K = B.poincareSeries h.multiplier` is the Poincaré kernel for the multiplier
`h.multiplier`, and `New.quotMean` is the mean over `V / L` (total mass one).
-/

namespace New.ThetaTori.IsHermitianAction

open Complex ComplexConjugate Matrix Module MeasureTheory ComplexOrder QuotientAddGroup Fintype Fock

variable {V R : Type} [FinComplexSpace V] [CommRing R] [StarRing R]
  {L : Submodule ℤ V} {B : LatticeForm L} {F : R →+* V →L[ℂ] V} {β : R}
  (h : IsHermitianAction L B F β) {x y : V}

/-- The fourth power of a Gauss sum is real. Let `h` be hermitian data, `κ ≠ 0`, and let `q` be a
function on the finite group `κ⁻¹ L / L` with `q z = exp (B x (F r x))` for every lift `x ∈ κ⁻¹ L`
of `z`. Then the sums of `q` and of its complex conjugate have the same fourth power. -/
lemma sum_conj_pow_four_eq_sum_pow_four [IsFullRankLattice L] [IsDomain R] [Module.Finite ℤ R]
    {κ r : R} [NeZero κ] (q : h.MulKernel κ → ℂ)
    (hq : ∀ x : divLattice L F κ, q x = exp (B x (F r x))) :
    (∑ z : h.MulKernel κ, conj (q z)) ^ 4 = (∑ z : h.MulKernel κ, q z) ^ 4 := by
  -- With `N` the order of the group, `q z ^ N ^ 2 = 1`, so `conj (q z) = q z ^ (N ^ 2 - 1)`. Write
  -- `N ^ 2 - 1` as a sum of four squares; the quaternion matrix `M` with `M Mᵀ = N ^ 2 - 1`
  -- permutes the quadruples `p`, and it turns the product of the `q (p i)` into its
  -- `(N ^ 2 - 1)`-th power.
  set N : ℕ := card (h.MulKernel κ) with hN
  have q_pow (z : h.MulKernel κ) : q z ^ N ^ 2 = 1 := by
    obtain ⟨x, rfl⟩ := mk_surjective z
    -- Both `N • x` and `0` are lifts of `0`.
    have h_one : exp (B (N • x) (F r (N • x))) = 1 := by
      simpa [hN, hq, ← mk_zero] using (hq (N • x)).symm
    simpa [hq, sq, ← exp_nsmul, pow_mul] using h_one
  have q_conj (z : h.MulKernel κ) : conj (q z) = q z ^ (N ^ 2 - 1) := by
    -- `q z` is a root of unity, so its conjugate is its inverse `q z ^ (N ^ 2 - 1)`
    have h_mul : q z ^ (N ^ 2 - 1) * q z = 1 := by simpa [pow_sub_one_mul, hN] using q_pow z
    rw [← inv_eq_conj (norm_eq_one_of_pow_eq_one (q_pow z) (by simp [hN])),
      inv_eq_of_mul_eq_one_left h_mul]
  obtain ⟨a, b, c, d, h_sq⟩ := (N ^ 2 - 1).sum_four_squares
  let M : Matrix (Fin 4) (Fin 4) ℤ := !![(a : ℤ), b, c, d; -b, a, -d, c; -c, d, a, -b; -d, -c, b, a]
  -- On a group killed by `N`, `M Mᵀ = N ^ 2 - 1` acts as `-1`, so `-Mᵀ` is a right inverse of `M`.
  have M_surj : Function.Surjective fun p : Fin 4 → h.MulKernel κ ↦ M • p := by
    refine fun p ↦ ⟨-Mᵀ • p, funext fun j ↦ ?_⟩
    calc (M • -Mᵀ • p) j = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • -p j := by
          fin_cases j <;> simp [M, Fin.sum_univ_four] <;> module
      -- `↓`: rewrite by `h_sq` before simp takes the sum of squares apart
      _ = p j := by simp [↓h_sq, hN, sq, sub_nsmul, NeZero.one_le, mul_smul]
  have prod_M (p : Fin 4 → h.MulKernel κ) : ∏ i, q (p i) ^ (N ^ 2 - 1) = ∏ i, q ((M • p) i) := by
    obtain ⟨y, rfl⟩ := mk_surjective.comp_left p
    -- Expand both exponents; since `Mᵀ M = N ^ 2 - 1` as well, the mixed terms cancel.
    simp [← mk_zsmul, ← mk_add, hq, ← h_sq, ← Complex.exp_nsmul, ← exp_sum, M, Fin.sum_univ_four]
    grind
  simp only [q_conj, sum_pow, prod_M]
  exact Finset.sum_bijective (fun p ↦ M • p) (Finite.surjective_iff_bijective.mp M_surj)
    (by simp) (by simp)

include h

/-- For hermitian data `h` and `x, y ∈ L`, the number `B x y - B y x` lies in `2 π i ℤ`, so adding
it does not change an exponential: `s = t + B x y - B y x` gives `exp s = exp t`. -/
lemma exp_eq_of_mem_lattice {s t : ℂ} (hx : x ∈ L) (hy : y ∈ L) (hst : s = t + B x y - B y x) :
    exp s = exp t := by
  grind [exp_eq_exp_iff_exists_int, h.riemannForm_integral, h.isAppellHumbert.sub_eq_riemannForm,
    ofReal_intCast]

/-- For hermitian data `h`, the Poincaré kernel `K` (`B.poincareSeries h.multiplier`) under
translation of its first argument by a lattice vector `l`:
`K(x + l, y) = χ(l)⁻¹ exp (-(B l x + B l l / 2)) K(x, y)`, with `χ = h.multiplier`. -/
lemma poincareSeries_add (l : V) (hl : l ∈ L) :
    B.poincareSeries h.multiplier (x + l) y =
      (h.multiplier l)⁻¹ * exp (-(B l x + B l l / 2)) * B.poincareSeries h.multiplier x y := by
  -- Shift the summation index by `l`; each term then changes by the same factor.
  calc
    _ = ∑' m : L, B.poincareTerm h.multiplier (x + l) y (m + ⟨l, hl⟩) :=
      ((Equiv.addRight (⟨l, hl⟩ : L)).tsum_eq _).symm
    _ = ∑' m : L,
        (h.multiplier l)⁻¹ * exp (-(B l x + B l l / 2)) * B.poincareTerm h.multiplier x y m := by
      refine tsum_congr fun m ↦ ?_
      simp [ThetaTori.LatticeForm.poincareTerm, h.isAppellHumbert.semicharacter, hl, ← exp_add,
        field]
      -- what remains is an identity of exponents, with `B u v - B v u` written by the Riemann form
      grind [h.isAppellHumbert.sub_eq_riemannForm]
    _ = _ := tsum_mul_left

/-- For hermitian data `h`, the function `x ↦ K(ā (x + w), a (x + w))` is continuous and
`L`-periodic, where `K` is the Poincaré kernel and `ā = star a`. -/
lemma isContPeriodic_poincareSeries [IsFullRankLattice L] (a : R) (w : V) :
    IsContPeriodic L.toAddSubgroup fun x : V ↦
      B.poincareSeries h.multiplier (F (star a) (x + w)) (F a (x + w)) := by
  obtain ⟨-, h_cont, h_theta, -⟩ := h.isAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean
    h.pos
  refine ⟨by fun_prop, fun l hl x ↦ ?_⟩
  -- Both arguments move by lattice vectors: use `poincareSeries_add` in the first, the theta
  -- relation in the second. As `star a` is adjoint to `a`, the two factors of automorphy cancel.
  simp only [add_rotate l, map_add _ (x + w), h.poincareSeries_add, (h_theta _).2, h.map_mem _ l hl]
  simp [canonicalMultiplier, riemannForm, action_comm, h.adjoint, exp_neg, exp_add, field]

/-- For hermitian data `h` and `κ = c - star c`, let `α = star β * κ - c`. On `κ⁻¹ L` the number
`exp (B x (F (κ * α) x))` depends only on the class of `x` modulo `L`. -/
private lemma exp_mul_sub_eq_of_sub_mem {c κ : R} (hκ : κ = c - star c) (x : divLattice L F κ)
    (y : V) (hxy : (x : V) - y ∈ L) :
    exp (B x (F (κ * (star β * κ - c)) x)) = exp (B y (F (κ * (star β * κ - c)) y)) := by
  -- the two exponents differ by `B u v - B v u` for two lattice vectors `u`, `v`
  have h_mem : F (star β * κ - c) (F κ x - F (β * κ) ((x : V) - y)) ∈ L :=
    h.map_mem _ _ (sub_mem x.property (h.map_mem (β * κ) _ hxy))
  refine h.exp_eq_of_mem_lattice hxy h_mem ?_
  simp [hκ, h.adjoint, action_comm, h.star_eq_one_sub]
  ring

variable [IsFullRankLattice L] [IsDomain R] [Module.Finite ℤ R]

-- `seal Finset.sum` keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For hermitian data `h` and `κ = c - star c ≠ 0`, with `α = star β * κ - c`: the Poincaré
kernel `K(c̄ x, c x)` is the sum over `l ∈ L` of the Gauss sums
`∑ z, exp (B z (F (κ α) z)) * exp (B w (F (κ c) w))`, `w = l + x + z`, over representatives `z` of
`κ⁻¹ L / L`. -/
private lemma hasSum_poincareSeries_mulKernel {c κ : R} [NeZero κ] (hκ : κ = c - star c) (x : V) :
    HasSum (fun l : L ↦ ∑ z : h.MulKernel κ,
        exp (B z.out (F (κ * (star β * κ - c)) z.out)) *
          exp (B ((l : V) + x + z.out) (F (κ * c) ((l : V) + x + z.out))))
      (B.poincareSeries h.multiplier (F (star c) x) (F c x)) := by
  obtain ⟨h_summable, -, -, -, -⟩ := h.isAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean
    h.pos
  -- `(l, z) ↦ z.out + l` identifies `L × κ⁻¹ L / L` with `κ⁻¹ L` (representatives of the classes)
  let e_rep : L × h.MulKernel κ ≃ divLattice L F κ :=
    ((preimageMkEquivAddSubgroupProdSet (L.toAddSubgroup.addSubgroupOf (divLattice L F κ))
        Set.univ).trans
      (.prodCongr (L.toAddSubgroup.addSubgroupOfEquivOfLe (h.map_mem κ)).toEquiv
        (Equiv.Set.univ _))).symm.trans (Equiv.Set.univ _)
  -- and multiplication by `κ` identifies `κ⁻¹ L` with `L`
  let e_mul : divLattice L F κ ≃ L :=
    (LinearEquiv.ofInjectiveEndo _ (action_injective κ)).subtypeEquivOfSubtype
  -- the series of `K(c̄ x, c x)`, reindexed by `(l, z) ↦ κ (z.out + l)`, summed over the fibres
  have h_reindexed : HasSum (fun p : L × h.MulKernel κ ↦
      B.poincareTerm h.multiplier (F (star c) x) (F c x) (e_mul (e_rep p)))
      (B.poincareSeries h.multiplier (F (star c) x) (F c x)) :=
    (e_rep.trans e_mul).hasSum_iff.mpr (h_summable _ _).hasSum
  refine h_reindexed.prod_fiberwise fun l ↦ (hasSum_fintype _).congr_fun fun z ↦ ?_
  -- The term of index `κ w`, `w = z.out + l`, is `exp (B w (F (κ α) w)) * exp (B v (F (κ c) v))`,
  -- `v = w + x`: compare the exponents.
  change B.poincareTerm h.multiplier _ _ ⟨F κ (z.out + l), _⟩ = _
  -- `↓`: apply the class invariance of the Gauss factor before simp unfolds the exponentials
  simp [↓h.exp_mul_sub_eq_of_sub_mem hκ _ (z.out + l), ← exp_add, h.multiplier_eq_exp, ← exp_sub,
    hκ, h.adjoint, action_comm, ThetaTori.LatticeForm.poincareTerm]
  grind

/-- Let `h` say that `B` is a positive definite hermitian form whose Riemann form is integral on the
full-rank lattice `L`, and that `F` is an action of `R` preserving `L` with `F (star a)` adjoint to
`F a` and `star β = 1 - β`. Let `K(x, y) = ∑_{l ∈ L} exp(B(x, y - x + l) - B(l, y) - B(l,
l)/2) / χ(l)` be the Poincaré series of the Appell–Humbert data `h.isAppellHumbert`, and let
`κ = c - star c` be non-zero. Then the mean over `V / L` of `x ↦ K(c̄ x, c x)`, where `c̄ = star c`,
times the complex conjugate of the determinant of `F c̄` on `V`, has a real fourth power. -/
lemma isSelfAdjoint_quotMean_pow (c : R) {κ : R} [NeZero κ] (hκ : κ = c - star c) :
    IsSelfAdjoint
      ((quotMean L.toAddSubgroup
          (fun x : V ↦ B.poincareSeries h.multiplier (F (star c) x) (F c x)) *
        conj (F (star c)).det) ^ 4) := by
  -- Write the terms of the series as `l = κ z`, `z ∈ κ⁻¹ L`. Unfolding turns the mean into a Gauss
  -- sum over `h.MulKernel κ` times a Gaussian integral over `V`, divided by the covolume of `L`.
  -- The integral is `1 / conj (det (M κ) * det c̄)`, with `M κ` the matrix of `B x (κ y)`; the
  -- Gauss sum and `det (M κ)` have real fourth powers.
  borelize V
  -- `μ` is Lebesgue measure on `V` in the coordinates `e` of a basis `b`, divided by `π ^ dim V`.
  let b : Basis (Fin (finrank ℂ V)) ℂ V := finBasis ℂ V
  let e : (Fin (finrank ℂ V) → ℂ) ≃L[ℂ] V := b.equivFun.symm.toContinuousLinearEquiv
  let μ : Measure V := (normalizedVolume _).map e
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have : IsFiniteMeasure (L.toAddSubgroup.quotMeasure μ) :=
    isFiniteMeasure_addOrbitMeasure μ isCocompact_of_isFullRankLattice
  -- `M a` is the matrix of the form `(x, y) ↦ B x (a y)` in the basis `b`.
  let M (a : R) : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ :=
    (.pi (fun i ↦ B (b i)) ∘ₗ (F a).toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap).toMatrix'
  have M_adj (a : R) : (M a)ᴴ = M (star a) := by ext; simp [M, e, ← h.conj_symm, h.adjoint]
  have M_form (a : R) (x : Fin (finrank ℂ V) → ℂ) :
      star x ⬝ᵥ M a *ᵥ x = conj (B (F a (e x)) (e x)) := by
    simp [M, e, dotProduct, ← h.conj_symm]
  have M_mul : M (κ * star c) = M κ * (F (star c)).toMatrix b b := by
    -- `F (κ c̄) = F κ ∘ F c̄`, and the matrix of a composite is the product
    refine .trans ?_ (LinearMap.toMatrix'_mul ..)
    ext; simp [M, e]
  -- Since `κ c̄ + κ̄ c = κ̄ κ`, this hermitian form is `B (κ x) (κ x)`.
  have h_pos : ((M (κ * star c))ᴴ + (M (κ * star c))ᴴᴴ).PosDef := by
    refine .of_dotProduct_mulVec_pos (isHermitian_add_transpose_self _) fun x _ ↦ ?_
    have hx : F κ (e x) ≠ 0 := by simpa [map_eq_zero_iff, action_injective]
    refine (zero_lt_real.mpr (h.pos _ hx)).trans_eq ?_
    simp [re_eq_add_conj, h.adjoint, ← h.conj_symm, M_adj, M_form, hκ, add_mulVec]
    ring
  obtain ⟨h_det_M, h_det_c⟩ : (M κ).det ≠ 0 ∧ (F (star c)).det ≠ 0 := by
    simpa [M_mul, and_comm] using IsAccretive.det_ne_zero h_pos
  -- `M κ` is skew-hermitian, as `κ̄ = -κ`.
  have h_real : conj (M κ).det ^ 4 = (M κ).det ^ 4 := by
    have h_star : star κ = -κ := by rw [hκ, star_sub, star_star, neg_sub]
    have h_skew : (M κ)ᴴ = -M κ := by rw [M_adj, h_star]; ext; simp [M]
    have h_four : (M κ)ᴴ ^ 4 = M κ ^ 4 := by rw [h_skew, Even.neg_pow (by decide)]
    simpa [det_pow] using congrArg det h_four
  -- `g c` is the Gaussian, and `g α` below gives the terms of the Gauss sum.
  let g (a : R) (x : V) : ℂ := exp (B x (F (κ * a) x))
  have h_gauss : ∫ x, g c x ∂μ = (conj (M κ).det)⁻¹ * (conj (F (star c)).det)⁻¹ := by
    -- This is `integral_gauss` for `(M (κ * star c))ᴴ = -M (κ * c)`.
    refine .trans ?_ ((integral_gauss h_pos 0).trans (by simp [M_mul]))
    simp (disch := fun_prop) [μ, integral_map, g, ← h.conj_symm, M_adj, M_form, hκ]
  have h_gauss_ne : ∫ x, g c x ∂μ ≠ 0 := by simp [h_gauss, h_det_M, h_det_c]
  have h_intg (z : V) (c' : ℂ) : Integrable (fun x ↦ c' * g c (x + z)) μ :=
    ((Integrable.of_integral_ne_zero h_gauss_ne).comp_add_right z).const_mul c'
  let α : R := star β * κ - c
  have h_sum (x : V) : HasSum (fun l : L ↦ ∑ z : h.MulKernel κ, g α z.out * g c (l + x + z.out))
      (B.poincareSeries h.multiplier (F (star c) x) (F c x)) :=
    h.hasSum_poincareSeries_mulKernel hκ x
  -- Unfold: the mean of a sum over `L` is the integral over `V` divided by the covolume.
  rw [quotMean_tsum_eq_integral _ μ (integrable_finsetSum _ fun _ _ ↦ h_intg ..)
    (by simpa using h.isContPeriodic_poincareSeries c 0) h_sum]
  have h_sum_real :
      (∑ z : h.MulKernel κ, conj (g α z.out)) ^ 4 = (∑ z : h.MulKernel κ, g α z.out) ^ 4 :=
    -- on `κ⁻¹ L` the factor `g α` depends only on the class modulo `L`
    h.sum_conj_pow_four_eq_sum_pow_four (fun z ↦ g α z.out) fun x ↦
      h.exp_mul_sub_eq_of_sub_mem hκ _ x (eq_iff_sub_mem.mp (out_eq' (x : h.MulKernel κ)))
  -- Each translated Gaussian has the integral `h_gauss`, so the integral of the sum is the Gauss
  -- sum times that integral.
  have h_int_sum : ∫ x, ∑ z : h.MulKernel κ, g α z.out * g c (x + z.out) ∂μ =
      (∑ z : h.MulKernel κ, g α z.out) * ∫ x, g c x ∂μ := by
    rw [integral_finsetSum _ fun z _ ↦ h_intg z.out (g α z.out), Finset.sum_mul]
    simp [integral_const_mul, integral_add_right_eq_self (g c)]
  -- `conj (det c̄)` cancels; the covolume is real, and the Gauss sum and `det (M κ)` have real
  -- fourth powers.
  rw [h_int_sum, h_gauss, smul_mul_assoc, mul_assoc, inv_mul_cancel_right₀ (by simpa using h_det_c)]
  simp [IsSelfAdjoint, mul_pow, h_sum_real, h_real]

end New.ThetaTori.IsHermitianAction

end
end
end

/-!
# Good reduction of theta tori from shift bounds on kernels of multiplications

The file gives a criterion for the main condition of good reduction of a torus `V / L` with
multiplications `New.ThetaTori.IsHermitianAction`. The condition
(`New.ThetaTori.HasMultiplicativeNorm`) is that the sup norm of sizes of theta functions is
multiplicative at the valuation `v`. The tool is a shift bound: `A.HasShiftBound v w C` (`w` has
the constant `C` in degree `A`) says `φ y ^ 2 ≤ C * ⨆ x, φ x * φ (x + w)` for all sizes `φ` of theta
functions of degree `A` and all torsion points `y`. Constants are obtained on the kernels of
multiplications `c` and descend along `c`, which gives multiplicativity.

## Main definitions and results

* `New.ThetaTori.IsHermitianAction.hasShiftBound_one_of_ker`: under arithmetic conditions on `c`,
  its kernel has the constant `1`.
* `New.ThetaTori.IsHermitianAction.hasShiftBound_of_torsionAction`,
  `New.ThetaTori.IsHermitianAction.eventually_hasShiftBound`: a constant descends along `c`; some
  constant exists.
* `New.ThetaTori.IsHermitianAction.hasMultiplicativeNorm_of_frequently_hasShiftBound`: if such `c`
  have arbitrarily small inverses, `New.ThetaTori.HasMultiplicativeNorm` holds.
* `New.ThetaTori.hasMultiplicativeNorm_of_expanding`: the multiplicative norm from arithmetic
  conditions on `R`, `B` and `p`.
* `New.ThetaTori.ThetaTorus.hasGoodReduction_and_val_card_eq_one`: let `v` be a valuation on `ℂ`
  whose valuation ring receives `𝓞 E` compatibly with `Φ v₀`, over a prime that is good for `D`.
  Then a theta torus has good reduction for `v`, and the order of `D.dualTorsion` is a unit.

Notions from other files:
* `New.ThetaTori.IsHermitianAction.multiplier`: The canonical multiplier x ↦ exp(πi E(βx, x)) of the
  hermitian data, where E is the Riemann form of B.
* `New.ThetaTori.HasGoodReduction`: a polarisation whose dual lattice is mapped into the lattice by
  a `v`-unit, a level `r > 1` that is a `v`-unit, and a multiplicative sup norm of theta functions
  on the torsion points.

## Relation to the literature

Known result: Good reduction of unitary PEL abelian varieties, in analytic form without toric
degeneration. Suppose a torus with polarisation prime to p has non-unit multipliers that expand
arbitrarily, divide a power of p and are prime to their conjugates, and whose conjugates have unit
determinant on the Lie algebra. Then the supremum of a valuation of theta values at torsion points
is multiplicative. Source: K.-W. Lan, Elevators for degenerations of PEL structures, Math. Res.
Lett. 18 (2011); R. Kottwitz, Points on some Shimura varieties over finite fields, J. Amer. Math.
Soc. 5 (1992), §5 (division algebra case); for the CM case B. Conrad, Semistable reduction for
abelian varieties (notes), Prop. 6.3, after Serre and Tate, Ann. of Math. 88 (1968).
-/

@[expose] public section

/-!
## Shift bounds on kernels of multiplications and the multiplicative norm

Conventions: `h.normShift x` is translation of functions by `x` with the factor of automorphy of
`B`, divided by the multiplier `h.multiplier x`; `h.MulKernel c` is `c⁻¹ L / L`. The size
`New.ThetaTori.LatticeForm.sizeAt` of `f` at a torsion point `x` is `v (exp (-B x x / 2) * f x)`.
`New.ThetaTori.LatticeForm.sizes` is the set of sizes of theta functions of a given degree `B`, for
every multiplier `χ` such that `(B, χ)` is of ample type (`New.ThetaTori.IsAmpleType`:
Appell–Humbert data with positive Riemann form, `χ` of finite order on `L`).
-/

namespace New.ThetaTori.IsHermitianAction

open MeasureTheory Complex NNReal Function Finset LinearMap Ideal Filter FiniteDimensional

variable {V R : Type} [FinComplexSpace V] [CommRing R] [StarRing R] [IsDomain R]
  {L : Submodule ℤ V} {B : LatticeForm L} {F : R →+* V →L[ℂ] V} {f : V → ℂ}
  {β c d : R} [IsFullRankLattice L]
  (h : IsHermitianAction L B F β) {v : Valuation ℂ ℝ≥0} [NeZero c] [NeZero d] {A : LatticeForm L}

/-- The action of `a` on the points of `V` of finite order modulo `L`: `x ↦ F a x`, again of finite
order because `F a` preserves `L`. -/
abbrev torsionAction (a : R) (x : torsionPoints L) : torsionPoints L :=
  ⟨F a x, x.property.imp (by grind [IsHermitianAction])⟩

include h

/-! ### Normalised translations, sizes and torsion points -/

section

omit [IsDomain R] [IsFullRankLattice L]

/-- The commutator of the normalised translations by `x` and `y` is `exp (2 π i E(x, y))`, where
`E` is the Riemann form of `B`. -/
lemma normShift_comm (x y : V) :
    h.normShift x (h.normShift y f) = B.riemannPhase x y • h.normShift y (h.normShift x f) := by
  -- unfolded, both sides are the phase and two multipliers times `thetaShift y (thetaShift x f)`
  simp [normalizedShift, h.isAppellHumbert.thetaShift_comm x]
  module

lemma multiplier_sq (l : V) (hl : l ∈ L) : h.multiplier l ^ 2 = 1 :=
  h.isAppellHumbert.exp_riemannForm_pow_eq_one (nsmul_mem (h.map_mem β l hl) 1) (nsmul_mem hl 1)

lemma isAmpleType : IsAmpleType B h.multiplier where
  isAppellHumbert := h.isAppellHumbert
  isPosRiemann := isPosRiemann_of_re_pos h.pos
  finite_order := ⟨2, two_ne_zero, h.multiplier_sq⟩

/-- The size of `f` at the sum of torsion points `x` and `w` is the valuation of the value at `0` of
the normalised translate of `f` by `w` and then by `x`. -/
lemma sizeAt_add (x w : torsionPoints L) :
    B.sizeAt v f (x + w) = v (h.normShift x (h.normShift w f) 0) := by
  -- The normalising factors `h.multiplier x` and `h.multiplier w` have valuation 1 by
  -- `valuation_exp_riemannForm`.
  rw [← h.isAppellHumbert.sizeAt_thetaShift]
  simp [normalizedShift, LatticeForm.sizeAt,
    h.isAppellHumbert.valuation_exp_riemannForm (h.torsionAction β _), canonicalMultiplier]

lemma sizeAt_eq_normShift (x : torsionPoints L) : B.sizeAt v f x = v (h.normShift x f 0) := by
  simpa [normalizedShift, canonicalMultiplier] using h.sizeAt_add x 0

end

variable [Module.Finite ℤ R]

/-- A point `a` of `c⁻¹ L` (the vectors that `F c` maps into `L`) has finite order modulo `L`. -/
lemma mem_torsionPoints (a : divLattice L F c) : (a : V) ∈ torsionPoints L := by
  -- the index of `L` in `c⁻¹ L` is the order of the finite group `c⁻¹ L / L`
  exact ⟨L.toAddSubgroup.relIndex (divLattice L F c), (Nat.card_pos (α := h.MulKernel c)).ne',
    L.toAddSubgroup.nsmul_relIndex_mem a.prop⟩

/-- For `c ≠ 0`, multiplication by `c` maps the points of finite order modulo `L` onto
themselves. -/
lemma torsionAction_surjective (c : R) [NeZero c] : Surjective (h.torsionAction c) := by
  rintro ⟨y, n, hn, hy⟩
  -- The preimage is `x = (F c).inverse y`. Since `F c (n • x) = n • y ∈ L`, the point `n • x` is
  -- torsion by `mem_torsionPoints`, and hence so is `x`.
  have hnx : n • (F c).inverse y ∈ divLattice L F c := by simp_all [divLattice]
  obtain ⟨m, hm, hmx⟩ : ∃ m ≠ (0 : ℕ), m • n • (F c).inverse y ∈ L :=
    h.mem_torsionPoints ⟨n • (F c).inverse y, hnx⟩
  have hmnx : (m * n) • (F c).inverse y ∈ L := by rwa [mul_smul]
  exact ⟨⟨(F c).inverse y, m * n, mul_ne_zero hm hn, hmnx⟩, Subtype.ext (by simp)⟩

omit [IsFullRankLattice L] [NeZero d] in
/-- Let `d = star c`. Translating `f ∘ F c ∘ (F d)⁻¹` by `d w` gives the translate of `f` by `c w`,
composed with `F c ∘ (F d)⁻¹`. -/
lemma normShift_comp_inverse_eq (hd : star c = d) (w : V) (f : V → ℂ) :
    h.normShift (F d w) (f ∘ F c ∘ (F d).inverse) =
      h.normShift (F c w) f ∘ F c ∘ (F d).inverse := by
  ext
  simp [normalizedShift, riemannForm, h.adjoint, action_comm, ← hd, canonicalMultiplier,
    thetaShift_apply]

/-! ### The theta identity and the kernel of a multiplication -/

/-- The averaged pull-back along `c` and `d`: the operator sending `t : V → ℂ` to the sum, over the
classes `z` of `d⁻¹ L / L` (with chosen representatives `z.out`), of the normalised translates of
`t ∘ F c ∘ (F d)⁻¹` by `d z`. -/
private noncomputable def averagedPullback (c d : R) [NeZero d] : (V → ℂ) →ₗ[ℂ] V → ℂ :=
  (∑ z : h.MulKernel d, h.normShift (F d z.out)) ∘ₗ funLeft ℂ ℂ (F c ∘ (F d).inverse)

private lemma averagedPullback_apply {c d : R} [NeZero d] (t : V → ℂ) :
    h.averagedPullback c d t =
      (∑ z : h.MulKernel d, h.normShift (F d z.out)) (t ∘ F c ∘ (F d).inverse) :=
  rfl

/-- Let `d = star c`. The averaged pull-back of a theta function with the canonical multiplier is
again one. -/
private lemma averagedPullback_mem_thetaSpace (hd : star c = d) {t : V → ℂ}
    (ht : t ∈ B.thetaSpace h.multiplier) :
    h.averagedPullback c d t ∈ B.thetaSpace h.multiplier := by
  -- The pull-back `t ∘ F c ∘ (F d)⁻¹` is fixed by the normalised translations by `d L`, so a
  -- translation by `d x ∈ L` only permutes the terms of the sum over the kernel of `d`.
  obtain ⟨t_diff, t_fixed⟩ : Differentiable ℂ t ∧ ∀ l ∈ L, h.normShift l t = t :=
    mem_thetaSpace_iff_normalizedShift.mp ht
  have pullback_fixed (l : V) (hl : l ∈ L) :
      h.normShift (F d l) (t ∘ F c ∘ (F d).inverse) = t ∘ F c ∘ (F d).inverse := by
    rw [h.normShift_comp_inverse_eq hd l t, t_fixed _ (h.map_mem c l hl)]
  rw [mem_thetaSpace_iff_normalizedShift]
  constructor
  · simp [averagedPullback, normalizedShift, funLeft]
    fun_prop
  · refine (action_isInvertible (F := F) d).surjective.forall.mpr fun x hx ↦ ?_
    simpa [averagedPullback, funLeft] using
      h.normShift_sum_eq_char_smul d pullback_fixed 1 ⟨x, hx⟩ rfl

/-- Let `d = star c`, and let `c` and `d` act as the identity on the dual lattice modulo `L`. For
`a` in the dual lattice and a theta function `t` with the canonical multiplier, the averaged
pull-back of the normalised translate of `t` by `a` is the normalised translate by `a` of the
averaged pull-back of `t`. -/
private lemma averagedPullback_normShift_of_mem_dualLattice (hd : star c = d)
    (hc_dual : ∀ a ∈ B.dualLattice, F c a - a ∈ L) (hd_dual : ∀ a ∈ B.dualLattice, F d a - a ∈ L)
    {a : V} (ha : a ∈ B.dualLattice) {t : V → ℂ} (ht : t ∈ B.thetaSpace h.multiplier) :
    h.averagedPullback c d (h.normShift a t) = h.normShift a (h.averagedPullback c d t) := by
  -- On theta functions `normShift y` equals `normShift a` whenever `y - a ∈ L`, as for `y = c a`
  -- and `y = d a`. In between, `normShift (c a)` passes through the pull-back as `normShift (d a)`,
  -- which commutes with the terms of the sum.
  have shift_eq (y : V) (hy : y - a ∈ L) {s : V → ℂ} (hs : s ∈ B.thetaSpace h.multiplier) :
      h.normShift y s = h.normShift a s := by
    have s_fixed : h.normShift (y - a) s = s :=
      (mem_thetaSpace_iff_normalizedShift.mp hs).2 _ hy
    have phase : B.riemannPhase (F β a) (y - a) = 1 :=
      h.riemannPhase_eq_one ha (h.map_mem (star β) _ hy)
    calc h.normShift y s = h.normShift (a + (y - a)) s := by rw [add_sub_cancel]
      _ = h.normShift a (h.normShift (y - a) s) := by
        simp only [normShift, h.isAppellHumbert.normalizedShift_normalizedShift
          h.riemannForm_apply_beta_eq_sub,
          phase, one_smul]
      _ = h.normShift a s := by rw [s_fixed]
  have phase_one (z : h.MulKernel d) : B.riemannPhase (F d a) (F d z.out) = 1 := by
    refine h.riemannPhase_eq_one ha ?_
    rw [star_eq_iff_star_eq.mp hd]
    exact h.map_mem c _ (map_divLattice_mem (L := L) (F := F) d z.out)
  set s : V → ℂ := t ∘ F c ∘ (F d).inverse
  have pull : h.normShift (F c a) t ∘ F c ∘ (F d).inverse = h.normShift (F d a) s :=
    (h.normShift_comp_inverse_eq hd a t).symm
  have term_comm (z : h.MulKernel d) :
      h.normShift (F d z.out) (h.normShift (F d a) s) =
        h.normShift (F d a) (h.normShift (F d z.out) s) := by
    rw [h.normShift_comm (F d a), phase_one z, one_smul]
  calc h.averagedPullback c d (h.normShift a t)
    _ = h.averagedPullback c d (h.normShift (F c a) t) := by rw [shift_eq _ (hc_dual a ha) ht]
    _ = h.normShift (F d a) (h.averagedPullback c d t) := by
      rw [averagedPullback_apply, averagedPullback_apply, LinearMap.sum_apply, LinearMap.sum_apply,
        map_sum, pull]
      exact Finset.sum_congr rfl fun z _ ↦ term_comm z
    _ = h.normShift a (h.averagedPullback c d t) :=
      shift_eq _ (hd_dual a ha) (h.averagedPullback_mem_thetaSpace hd ht)

/-- Let `d = star c`, and let `c` and `d` act as the identity on the dual lattice modulo `L`. The
averaged pull-back acts on the theta functions with the canonical multiplier as a scalar. -/
private lemma exists_averagedPullback_eq_smul (hd : star c = d)
    (hc_dual : ∀ a ∈ B.dualLattice, F c a - a ∈ L) (hd_dual : ∀ a ∈ B.dualLattice, F d a - a ∈ L) :
    ∃ μ : ℂ, ∀ t ∈ B.thetaSpace h.multiplier, h.averagedPullback c d t = μ • t := by
  -- Schur's lemma: on theta functions the operator commutes with the twisted translations by the
  -- dual lattice, because `h.normShift a` is a non-zero multiple of the twisted translation by `a`.
  let Q : Module.End ℂ (B.thetaSpace h.multiplier) :=
    (h.averagedPullback c d).restrict fun _ ht ↦ h.averagedPullback_mem_thetaSpace hd ht
  have Q_commute : ∀ a : B.dualLattice, Commute (h.isAppellHumbert.thetaShiftEnd a) Q := by
    rintro ⟨a, ha⟩
    refine LinearMap.ext fun t ↦ Subtype.ext ?_
    change B.thetaShift a (h.averagedPullback c d t) = h.averagedPullback c d (B.thetaShift a t)
    have shift_eq_smul (s : V → ℂ) : h.normShift a s = (h.multiplier a)⁻¹ • B.thetaShift a s := rfl
    have multiplier_ne : (h.multiplier a)⁻¹ ≠ 0 := by simp [canonicalMultiplier]
    have scaled : (h.multiplier a)⁻¹ • h.averagedPullback c d (B.thetaShift a t) =
        (h.multiplier a)⁻¹ • B.thetaShift a (h.averagedPullback c d t) := by
      have commutes : h.averagedPullback c d (h.normShift a t) =
          h.normShift a (h.averagedPullback c d t) :=
        h.averagedPullback_normShift_of_mem_dualLattice hd hc_dual hd_dual ha t.prop
      rwa [shift_eq_smul, shift_eq_smul, map_smul] at commutes
    exact (smul_right_injective (V → ℂ) multiplier_ne scaled).symm
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, Q = μ • 1 :=
    h.isAppellHumbert.schur_lemma (hp := h.isAmpleType.isPosRiemann) Q_commute
  refine ⟨μ, fun t ht ↦ ?_⟩
  have Q_apply : Q ⟨t, ht⟩ = μ • ⟨t, ht⟩ := by
    rw [hμ, LinearMap.smul_apply, one_apply_eq_self]
  simpa [Q] using congrArg Subtype.val Q_apply

/-- Let `d = star c` with `c` and `d` non-zero, and let `c` and `d` act as the identity on the dual
lattice modulo `L`. There is a number `μ` such that (a) `μ` is the order of `d⁻¹ L / L` times the
mean over `V / L` of `x ↦ K(d x, c x)`, with `K` the Poincaré kernel (a sum over `L`, a theta
function with the canonical multiplier in its second variable, of mean `1` on the diagonal); (b) for
every theta function `t` with the canonical multiplier, the sum over `z ∈ d⁻¹ L / L` (with chosen
representatives `z.out`) of the normalised translates of `t ∘ F c ∘ (F d)⁻¹` by `d z` is `μ • t`. -/
lemma exists_sum_normShift_eq_smul (hd : star c = d)
    (hc_dual : ∀ a ∈ B.dualLattice, F c a - a ∈ L) (hd_dual : ∀ a ∈ B.dualLattice, F d a - a ∈ L) :
    ∃ μ : ℂ,
      (Nat.card (h.MulKernel d) : ℂ) *
          quotMean L.toAddSubgroup (fun x : V ↦ B.poincareSeries h.multiplier (F d x) (F c x)) =
          μ ∧
      ∀ t ∈ B.thetaSpace h.multiplier,
        (∑ z : h.MulKernel d, h.normShift (F d z.out)) (t ∘ F c ∘ (F d).inverse) = μ • t := by
  -- The averaged pull-back is a scalar `μ` on theta functions. Testing it on the Poincaré series
  -- and taking the mean over `V / L` computes `μ`.
  obtain ⟨μ, pullback_eq⟩ := h.exists_averagedPullback_eq_smul hd hc_dual hd_dual
  have identity (t : V → ℂ) (ht : t ∈ B.thetaSpace h.multiplier) :
      (∑ z : h.MulKernel d, h.normShift (F d z.out)) (t ∘ F c ∘ (F d).inverse) = μ • t :=
    pullback_eq t ht
  refine ⟨μ, ?_, identity⟩
  subst hd
  -- the kernel is a theta function of its second variable, with mean `(h.multiplier 0)⁻¹` on the
  -- diagonal
  obtain ⟨-, -, kern_mem, kern_mean, -⟩ :=
    h.isAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean h.pos
  set K : V → V → ℂ := B.poincareSeries h.multiplier
  let G : V → ℂ := fun x ↦ K (F (star c) x) (F c x)
  -- for `t = K (d x)`, at the point `d x`, the term `z` of the sum is `G (x + z)`
  have sum_G (x : V) :
      ∑ z : h.MulKernel (star c), G (x + z.out) = μ * K (F (star c) x) (F (star c) x) := by
    have term (z : h.MulKernel (star c)) :
        h.normShift (F (star c) z.out) (K (F (star c) x) ∘ F c ∘ (F (star c)).inverse)
          (F (star c) x) = G (x + z.out) := by
      simp [G, K, normalizedShift, h.poincareSeries_add, h.adjoint, mul_assoc, thetaShift_apply]
    simpa [term] using congrFun (identity _ (kern_mem (F (star c) x))) (F (star c) x)
  -- the mean of the diagonal does not change under pull-back along `d`
  have diag_pullback : quotMean L.toAddSubgroup (fun x ↦ K (F (star c) x) (F (star c) x)) =
      quotMean L.toAddSubgroup (fun x ↦ K x x) := by
    simpa using quotMean_comp L.toAddSubgroup (F (star c)) (h.isContPeriodic_poincareSeries 1 0)
      (h.map_mem _) (action_isInvertible _).surjective
  -- and `h.multiplier 0 = 1`
  have diag_mean : quotMean L.toAddSubgroup (fun x ↦ K x x) = 1 := by
    simpa [canonicalMultiplier] using kern_mean
  have G_periodic : IsContPeriodic L.toAddSubgroup G := by
    simpa [G, K] using h.isContPeriodic_poincareSeries c 0
  calc (Nat.card (h.MulKernel (star c)) : ℂ) * quotMean L.toAddSubgroup G
    _ = ∑ _ : h.MulKernel (star c), quotMean L.toAddSubgroup G := by simp
    _ = ∑ z : h.MulKernel (star c), quotMean L.toAddSubgroup fun x ↦ G (x + z.out) :=
      sum_congr rfl fun z _ ↦ (quotMean_translate G_periodic _).symm
    _ = quotMean L.toAddSubgroup fun x ↦ ∑ z : h.MulKernel (star c), G (x + z.out) :=
      (integral_finsetSum _ fun z _ ↦ (h.isContPeriodic_poincareSeries c z.out).integrable_out).symm
    _ = μ := by simp [sum_G, diag_pullback, diag_mean]

/-- Let `h` be a hermitian action of `R` on `V/L` (`B` positive definite hermitian with Riemann form
E integral on `L`, `F` preserving `L` with `star` giving adjoints, `star β = 1 - β`). Let `c` and
`d = star c` be coprime and non-zero, with `F d a - a ∈ L` for every `a` in the dual lattice of `B`.
Let `t` be a theta function of type (`B`, χ), where χ is the canonical multiplier x ↦ exp(πi E(βx,
x)), and let `z ≠ 0` lie in the kernel of `d` on `V/L`. Write `normShift x` for the twisted
translation by `x` divided by exp(πi E(βx, x)). Then the sum of
`normShift (F c k.out) (normShift (F c z.out) t)` over `k` in the kernel of `c` on `V/L` vanishes at
every point `x`. -/
lemma sum_normShift_eq_zero (hd : star c = d) (hd_dual : ∀ a ∈ B.dualLattice, F d a - a ∈ L)
    (hc : IsCoprime c d) {t : V → ℂ} (ht : t ∈ B.thetaSpace h.multiplier) {z : h.MulKernel d}
    (hz : z ≠ 0) (x : V) :
    ∑ k : h.MulKernel c, h.normShift (F c k.out) (h.normShift (F c z.out) t) x = 0 := by
  -- If the sum is not zero, then `c z` lies in the dual lattice, hence in `L`; as `d z ∈ L` and
  -- `c`, `d` are coprime, `z` lies in `L`, that is `z = 0`.
  subst hd
  by_contra hne
  have killed : F (star c) (F c z.out) ∈ L := by simp [action_comm _ c, h.map_mem]
  have t_periodic : ∀ l ∈ L, h.normShift l t = t := (mem_thetaSpace_iff_normalizedShift.mp ht).2
  have fixed (l : V) (hl : l ∈ L) :
      h.normShift (F c l) (h.normShift (F c z.out) t) = h.normShift (F c z.out) t := by
    rw [h.normShift_comm, h.riemannPhase_eq_one (h.riemannForm_integral l hl) killed, one_smul,
      t_periodic _ (h.map_mem _ _ hl)]
  -- Translation by `l ∈ L` fixes the sum (`normShift_sum_eq_char_smul`) and multiplies it by the
  -- commutator of `l` and `c z`. As the sum is not zero, the commutator is `1`: `c z` lies in the
  -- dual lattice.
  have dual_mem : F c z.out ∈ B.dualLattice := by
    intro l hl
    have sum_fixed : h.normShift l (∑ k : h.MulKernel c,
        h.normShift (F c k.out) (h.normShift (F c z.out) t)) =
          ∑ k : h.MulKernel c, h.normShift (F c k.out) (h.normShift (F c z.out) t) := by
      simpa using h.normShift_sum_eq_char_smul c fixed 1
        ⟨(F c).inverse l, by simpa [divLattice]⟩ rfl
    -- every term of the sum is the phase `B.riemannPhase (c k) (c z)` times
    -- `u = normShift (c z) t`, so the sum is a multiple of `u`, and translation by `l` multiplies
    -- `u` by `B.riemannPhase l (c z)`
    have sum_fixed' : ∀ y : V,
        B.riemannPhase l (F c z.out) * h.normShift (F c z.out) t y = h.normShift (F c z.out) t y ∨
          ∑ i : h.MulKernel c, B.riemannPhase (F c i.out) (F c z.out) = 0 := by
      simpa [← sum_mul, funext_iff, h.normShift_comm _ (F c z.out),
        mem_thetaSpace_iff_normalizedShift.mp ht, hl] using sum_fixed
    obtain ⟨h_sum_ne, h_val_ne⟩ :
        ∑ i : h.MulKernel c, B.riemannPhase (F c i.out) (F c z.out) ≠ 0 ∧
          h.normShift (F c z.out) t x ≠ 0 := by
      simpa [← sum_mul, mem_thetaSpace_iff_normalizedShift.mp ht, h.normShift_comm _ (F c z.out)]
        using hne
    have phase_mul : B.riemannPhase l (F c z.out) * h.normShift (F c z.out) t x =
        h.normShift (F c z.out) t x := (sum_fixed' x).resolve_right h_sum_ne
    have phase_eq_one : B.riemannPhase l (F c z.out) = 1 := (mul_eq_right₀ h_val_ne).mp phase_mul
    simpa [riemannForm_swap l, exp_neg, ← fourierChar_eq_one_iff, Circle.ext_iff] using phase_eq_one
  have h_dual_star : F (star c) (F c z.out) - F c z.out ∈ L := hd_dual _ dual_mem
  have cz_mem : F c z.out ∈ L := (L.sub_mem_iff_right killed).mp h_dual_star
  -- `z = a (c z) + b (star c z)` lies in `L`
  obtain ⟨a, b, hab⟩ : ∃ a b : R, a * c + b * star c = 1 := hc
  have comb : F (a * c + b * star c) z.out ∈ L := by
    simpa using add_mem (h.map_mem a _ cz_mem)
        (h.map_mem b _ (map_divLattice_mem (L := L) (F := F) _ z.out))
  have z_mem : (z.out : V) ∈ L := by simpa [hab] using comb
  exact hz ((h.out_mem_iff_eq_zero _ z).mp z_mem)

omit [IsDomain R] [IsFullRankLattice L] [Module.Finite ℤ R] in
/-- The Poincaré kernel `K` of the canonical multiplier (`ThetaTori.LatticeForm.poincareSeries`, a
sum of `ThetaTori.LatticeForm.poincareTerm` over the lattice) at `(c x, star c x)` is the complex
conjugate of its value at `(star c x, c x)`. -/
lemma poincareSeries_eq_conj_poincareSeries_star (c : R) (x : V) :
    B.poincareSeries h.multiplier (F c x) (F (star c) x) =
      starRingEnd ℂ (B.poincareSeries h.multiplier (F (star c) x) (F c x)) := by
  -- Conjugate term by term and substitute `l ↦ -l` in the sum over the lattice.
  simp only [ThetaTori.LatticeForm.poincareSeries, conj_tsum]
  rw [← tsum_comp_neg]
  refine tsum_congr fun l ↦ ?_
  rw [ThetaTori.LatticeForm.poincareTerm, ThetaTori.LatticeForm.poincareTerm, h.multiplier_eq_exp,
    h.multiplier_eq_exp]
  simp [← exp_sub, ← exp_conj]
  -- the exponents differ by `B x y - B y x` for lattice vectors, by adjointness and symmetry
  grind [h.exp_eq_of_mem_lattice l.prop (h.map_mem β _ l.prop), action_comm, adjoint, conj_symm]

/-- The theta identity. Let `d = star c` with `c` and `d` non-zero and `c ≠ d`, let `c` and `d` be
coprime, and let both act as the identity on the dual lattice modulo `L`. Then there is `μ` with
`μ ^ 8 = det (F d) ^ 8`, that is, `μ` is the determinant of `d` up to an eighth root of unity, such
that for every theta function `t` with the canonical multiplier the sum over `z ∈ d⁻¹ L / L` of the
normalised translates of `t ∘ F c ∘ (F d)⁻¹` by `d z` is `μ • t`. -/
lemma exists_theta_identity (hd : star c = d)
    (hc_dual : ∀ a ∈ B.dualLattice, F c a - a ∈ L) (hd_dual : ∀ a ∈ B.dualLattice, F d a - a ∈ L)
    (hc_ne_d : c ≠ d) (hc : IsCoprime c d) :
    ∃ μ : ℂ,
      μ ^ 8 = (F d).det ^ 8 ∧
      ∀ t ∈ B.thetaSpace h.multiplier,
        (∑ z : h.MulKernel d, h.normShift (F d z.out)) (t ∘ F c ∘ (F d).inverse) = μ • t := by
  -- The averaged pull-backs for `(c, star c)` and `(star c, c)` are the scalars `μ` and `ν`. The
  -- means give `ν = #(c⁻¹ L / L) * conj m` and `μ = δ * conj δ * m`, with `δ = det (star c)`;
  -- composing the two identities gives `conj m * μ = 1`, and `m * conj δ` has a real fourth power.
  have h_sub_ne : NeZero (c - d) := ⟨sub_ne_zero.mpr hc_ne_d⟩
  subst hd
  obtain ⟨μ, hμ, identity⟩ := h.exists_sum_normShift_eq_smul rfl hc_dual hd_dual
  obtain ⟨ν, hν, identity_star⟩ := h.exists_sum_normShift_eq_smul (star_star c) hd_dual hc_dual
  set K : V → V → ℂ := B.poincareSeries h.multiplier with hK
  set m : ℂ := quotMean L.toAddSubgroup fun x ↦ K (F (star c) x) (F c x) with hm
  set δ : ℂ := (F (star c)).det
  refine ⟨μ, ?_, identity⟩
  have ν_eq : ν = Fintype.card (h.MulKernel c) * starRingEnd ℂ m := by
    simp [← hν, hm, hK, h.poincareSeries_eq_conj_poincareSeries_star c, quotMean, integral_conj,
      Nat.card_eq_fintype_card]
  have μ_eq : μ = δ * starRingEnd ℂ δ * m := by rw [← hμ, h.card_mulKernel]
  -- Compose the two identities. In the double sum only the terms with `z = 0` survive.
  have conj_m_mul_μ : starRingEnd ℂ m * μ = 1 := by
    obtain ⟨t, ht, x, hx⟩ : ∃ t ∈ B.thetaSpace h.multiplier, ∃ x : V, t x ≠ 0 := by
      simpa [funext_iff] using
        h.isAppellHumbert.exists_mem_thetaSpace_ne_zero (hp := h.isAmpleType.isPosRiemann)
    have double_sum_eq :
        ∑ k : h.MulKernel c, ∑ z : h.MulKernel (star c),
            h.normShift (F c k.out) (h.normShift (F c z.out) t) x =
          ν * (μ * t x) := by
      have at_x : (∑ z : h.MulKernel c, h.normShift (F c z.out))
          ((μ • t) ∘ F (star c) ∘ (F c).inverse) x = ν * (μ * t x) :=
        congrFun (identity_star _ (Submodule.smul_mem _ μ ht)) x
      simpa [smul_smul, ← identity _ ht, h.normShift_comp_inverse_eq, mul_assoc] using at_x
    rw [sum_comm, Fintype.sum_eq_single 0 fun z hz ↦
      h.sum_normShift_eq_zero rfl hd_dual hc ht hz _] at double_sum_eq
    simpa [mem_thetaSpace_iff_normalizedShift.mp ht, h.map_mem, ν_eq, hx, field,
      out_mem_iff_eq_zero] using double_sum_eq.symm
  -- `μ = δ * a` with `a = m * conj δ`; `a * conj a = 1` and `a ^ 4` is real, so `a ^ 8 = 1`
  have conj_pow_four_eq : starRingEnd ℂ m ^ 4 * δ ^ 4 = (m * starRingEnd ℂ δ) ^ 4 := by
    simpa [IsSelfAdjoint, mul_pow] using h.isSelfAdjoint_quotMean_pow c rfl
  have a_mul_conj : m * starRingEnd ℂ δ * starRingEnd ℂ (m * starRingEnd ℂ δ) = 1 := by
    rw [← conj_m_mul_μ, μ_eq, map_mul, Complex.conj_conj]
    ring
  calc μ ^ 8
    _ = δ ^ 8 * ((m * starRingEnd ℂ δ) ^ 4 * (starRingEnd ℂ m ^ 4 * δ ^ 4)) := by
      rw [conj_pow_four_eq, μ_eq]
      ring
    _ = δ ^ 8 * (m * starRingEnd ℂ δ * starRingEnd ℂ (m * starRingEnd ℂ δ)) ^ 4 := by
      rw [map_mul, Complex.conj_conj]
      ring
    _ = δ ^ 8 := by rw [a_mul_conj, one_pow, mul_one]

omit h in
/-- Let `v` be a valuation on `ℂ` with values in `ℝ≥0`, let `p` be a prime and `ζ` a `p ^ n`-th root
of unity. Then `v (ζ - 1) ^ p ^ n ≤ v p`. -/
theorem _root_.Valuation.map_sub_one_pow_le_of_pow_eq_one {v : Valuation ℂ ℝ≥0} {p n : ℕ}
    (hp : p.Prime) {ζ : ℂ} (hζ : ζ ^ p ^ n = 1) : v (ζ - 1) ^ p ^ n ≤ v p := by
  -- In the valuation ring, the binomial theorem gives `ζ ^ p ^ n = 1 + (ζ - 1) ^ p ^ n + p * r`,
  -- so `p` divides `(ζ - 1) ^ p ^ n`.
  let ζ₀ : v.integer := ⟨ζ, (valuation_eq_one_of_pow_eq_one (pow_ne_zero n hp.ne_zero) hζ).le⟩
  have h_pow : ζ₀ ^ p ^ n = 1 := Subtype.ext (by simpa [ζ₀] using hζ)
  obtain ⟨r, hr⟩ : ∃ r : v.integer,
      (1 + (ζ₀ - 1)) ^ p ^ n = 1 ^ p ^ n + (ζ₀ - 1) ^ p ^ n + p * r :=
    ⟨_, add_pow_prime_pow_eq' hp 1 (ζ₀ - 1) n⟩
  have dvd : (p : v.integer) ∣ (ζ₀ - 1) ^ p ^ n := by
    rw [add_sub_cancel, h_pow, one_pow] at hr
    exact ⟨-r, by linear_combination -hr⟩
  simpa [ζ₀, Algebra.algebraMap_ofSubring] using (Valuation.integer.integers v).le_of_dvd dvd

omit h in
/-- If `S ≤ max (√T) (ρ * S)` in `ℝ≥0` with `ρ < 1`, then `S ^ 2 ≤ T`. -/
theorem _root_.NNReal.sq_le_of_le_max_sqrt_mul {S T ρ : ℝ≥0} (hρ : ρ < 1)
    (h_le : S ≤ max (NNReal.sqrt T) (ρ * S)) : S ^ 2 ≤ T := by
  rw [← NNReal.le_sqrt_iff_sq_le, ← not_lt]
  intro h_lt
  exact (max_lt h_lt (mul_lt_of_lt_one_left (pos_of_gt h_lt) hρ)).not_ge h_le

/-- Let `d = star c`, let `μ` be the scalar of the theta identity `identity`, let `f` be a theta
function with the canonical multiplier and let `c g ∈ L`. Write `T(x, y)` for the value at `0` of
the normalised translate of `f` by `x` and then by `y`. Then `μ` times the value at `0` of the
normalised translate of `f` by `d q` equals `μ * T(d g, d q)` minus the sum over `z ∈ d⁻¹ L / L`
(with chosen representatives `z.out`) of `(B.riemannPhase (c g) (c z) - 1) * T(c z, c q)`. -/
lemma mul_normShift_eq_mul_normShift_sub_sum (hd : star c = d) {μ : ℂ}
    (identity : ∀ t ∈ B.thetaSpace h.multiplier,
      (∑ z : h.MulKernel d, h.normShift (F d z.out)) (t ∘ F c ∘ (F d).inverse) = μ • t)
    {f : V → ℂ} (hf : f ∈ B.thetaSpace h.multiplier) {g : V} (hg : F c g ∈ L) (q : V) :
    μ * h.normShift (F d q) f 0 =
      μ * h.normShift (F d q) (h.normShift (F d g) f) 0 -
        ∑ z : h.MulKernel d, (B.riemannPhase (F c g) (F c z.out) - 1) *
          h.normShift (F c q) (h.normShift (F c z.out) f) 0 := by
  have plain : ∑ z : h.MulKernel d, h.normShift (F c q) (h.normShift (F c z.out) f) 0 =
      μ * h.normShift (F d q) f 0 := by
    simpa [h.normShift_comp_inverse_eq hd]
      using congrArg (fun s : V → ℂ ↦ h.normShift (F d q) s 0) (identity f hf)
  have moved : ∑ z : h.MulKernel d, B.riemannPhase (F c g) (F c z.out) *
      h.normShift (F c q) (h.normShift (F c z.out) f) 0 =
        μ * h.normShift (F d q) (h.normShift (F d g) f) 0 := by
    simpa [h.normShift_comp_inverse_eq hd, h.normShift_comm (F c g),
      mem_thetaSpace_iff_normalizedShift.mp hf, hg]
      using congrArg (fun s : V → ℂ ↦ h.normShift (F d q) (h.normShift (F d g) s) 0) (identity f hf)
  simp [← plain, ← moved, sub_mul]

/-- The constant `1` on the kernel of `c`. Let `c ≠ 0` and `d = star c` be distinct and coprime and
act as the identity on the dual lattice of `B` modulo `L`; let `p` be a prime with `v p < 1`, let
`det d` have valuation `1`, and let `B - A` have a positive Riemann form. Then every torsion point
`w` with `c w ∈ L` and `p ^ n w ∈ L` has the constant `1` in degree `A`, meaning
`(sup φ) ^ 2 ≤ ⨆ x, φ x * φ (x + w)` (`x` over torsion points) for the size function `φ`, taken with
`v`, of every twisted theta function of degree `A`. -/
lemma hasShiftBound_one_of_ker {A : LatticeForm L} {w : torsionPoints L} (hd : star c = d)
    (hc_dual : ∀ a ∈ B.dualLattice, F c a - a ∈ L) (hd_dual : ∀ a ∈ B.dualLattice, F d a - a ∈ L)
    (hc_ne_d : c ≠ d) {p n : ℕ} (hp : p.Prime) (hv : v p < 1) (h_det : v (F d).det = 1)
    (h_pos : IsPosRiemann (B + -A)) (hw : F c w ∈ L) (hc : IsCoprime c d)
    (hpw : p ^ n • (w : V) ∈ L) :
    A.HasShiftBound v w 1 := by
  -- By `LatticeForm.HasShiftBound.of_isPosRiemann_sub` it is enough to treat the size `φ` of a
  -- theta function `f` of degree `B`. Write `w ≡ d g` with `c g ∈ L`. Translating the theta
  -- identity by `d g` multiplies each term by a `p ^ n`-th root of unity, so the ultrametric
  -- inequality gives `φ y ≤ max (φ (y + w)) (ρ * iSup φ)` with `ρ < 1`, and the first term decides.
  refine .of_isPosRiemann_sub h.isAmpleType h_pos fun f hf y ↦ ?_
  obtain ⟨μ, hμ, identity⟩ := h.exists_theta_identity hd hc_dual hd_dual hc_ne_d hc
  have v_μ : v μ = 1 := by simpa [h_det] using congrArg v hμ
  have hφ : B.sizeAt v f ∈ B.sizes v := .of_mem_thetaSpace h.isAmpleType hf
  set φ : torsionPoints L → ℝ≥0 := B.sizeAt v f with φ_def
  have hP : p ^ n ≠ 0 := pow_ne_zero n hp.ne_zero
  -- `ρ` is the `p ^ n`-th root of `v p`
  let ρ : ℝ≥0 := (powOrderIso _ hP).symm (v p)
  have hρ : ρ < 1 := (powOrderIso _ hP).symm_apply_lt.mpr ((one_pow _).trans_gt hv)
  have v_sub_one {ζ : ℂ} (hζ : ζ ^ p ^ n = 1) : v (ζ - 1) ≤ ρ :=
    (OrderIso.le_symm_apply _).mpr (v.map_sub_one_pow_le_of_pow_eq_one hp hζ)
  obtain ⟨α, γ, hαγ⟩ : ∃ α γ : R, α * c + γ * d = 1 := hc
  let T : torsionPoints L → torsionPoints L := h.torsionAction d
  let g : torsionPoints L := h.torsionAction γ w
  -- `γ d = 1 - α c`, so `w - d g = α (c w)`, which lies in `L` as `c w` does
  have g_eq : (w : V) - T g ∈ L := by
    have h_apply : F d (F γ w) = (w : V) - F α (F c w) := by
      calc F d (F γ w)
        _ = F (γ * d) w := by
          rw [action_comm d γ]
          simp
        _ = F (1 - α * c) w := by rw [eq_sub_of_add_eq' hαγ]
        _ = (w : V) - F α (F c w) := by simp
    change (w : V) - F d (F γ w) ∈ L
    simpa only [T, g, torsionAction, h_apply, sub_sub_cancel] using h.map_mem α _ hw
  have g_mem : F c g ∈ L := by simpa [g, action_comm c] using h.map_mem _ _ hw
  have killed (z : h.MulKernel d) : F d (F c z.out) ∈ L := by simp [action_comm _ c, h.map_mem]
  have step (q : torsionPoints L) : φ (T q) ≤ max (φ (T q + w)) (ρ * iSup φ) := by
    let ζ (z : h.MulKernel d) : ℂ := B.riemannPhase (F c g) (F c z.out)
    have root (z : h.MulKernel d) : ζ z ^ p ^ n = 1 := by
      subst hd
      simpa [ζ, g, action_comm c, ← exp_nsmul, mul_left_comm] using
        h.riemannPhase_eq_one (h.riemannForm_integral _ (h.map_mem γ _ hpw)) (killed z)
    -- compare the identity translated by `d q` with the one translated by `d g` and then `d q`
    let E : ℂ := ∑ z, (ζ z - 1) * h.normShift (F c q) (h.normShift (F c z.out) f) 0
    have diff :
        μ * h.normShift (F d q) f 0 = μ * h.normShift (F d q) (h.normShift (F d g) f) 0 - E :=
      h.mul_normShift_eq_mul_normShift_sub_sum hd identity hf g_mem q
    have error : v E ≤ ρ * iSup φ := by
      refine v.map_sum_le fun z _ ↦ (v.map_mul _ _).trans_le (mul_le_mul' (v_sub_one (root z)) ?_)
      -- the term is the size of `f` at the torsion point `c q + c z`
      let cz : torsionPoints L := ⟨F c z.out, h.mem_torsionPoints (c := d) ⟨F c z.out, killed z⟩⟩
      calc v (h.normShift (F c q) (h.normShift (F c z.out) f) 0)
        _ = φ (h.torsionAction c q + cz) := (h.sizeAt_add (h.torsionAction c q) cz).symm
        _ ≤ iSup φ := le_iSup_of_mem_sizes hφ _
    have h_sub : ((T q + w : torsionPoints L) : V) - (T q + T g : torsionPoints L) ∈ L := by
      simpa using g_eq
    calc φ (T q)
      _ = v (μ * h.normShift (F d q) f 0) := by simp [φ_def, h.sizeAt_eq_normShift, v_μ, T]
      _ ≤ max (v (μ * h.normShift (F d q) (h.normShift (F d g) f) 0)) (ρ * iSup φ) := by
        grw [diff, v.map_sub, error]
      _ = max (φ (T q + w)) (ρ * iSup φ) := by
        rw [factorsThrough_mkQ_of_mem_sizes hφ (a := T q + w) (b := T q + T g)
            (SModEq.sub_mem.mpr h_sub), φ_def, h.sizeAt_add]
        simp [v_μ, T]
  -- Every torsion point is of the form `d q`, so `step` bounds the supremum; in the case
  -- `φ (T q) ≤ φ (T q + w)` use `φ (T q) ^ 2 ≤ φ (T q) * φ (T q + w)`.
  have sup_le : iSup φ ≤ max (NNReal.sqrt (⨆ x, φ x * φ (x + w))) (ρ * iSup φ) := by
    refine ciSup_le ((h.torsionAction_surjective d).forall.mpr fun q ↦ ?_)
    rcases le_max_iff.mp (step q) with hle | hle
    · grw [← le_max_left, le_sqrt_iff_sq_le,
      ← le_iSup_of_mem_sizes (mul_shift_mem_sizes hφ hφ w) (T q),
        ← hle, sq]
    · exact le_max_of_le_right hle
  calc φ y ^ 2
    _ ≤ iSup φ ^ 2 := by grw [le_iSup_of_mem_sizes hφ y]
    _ ≤ ⨆ x, φ x * φ (x + w) := NNReal.sq_le_of_le_max_sqrt_mul hρ sup_le
    _ = 1 * ⨆ x, φ x * φ (x + w) := (one_mul _).symm

variable {w : torsionPoints L}

/-! ### The contraction argument -/

omit [IsFullRankLattice L] in
/-- The pull-back `c^* B` of `B` along the action of `c ≠ 0` (the form `B.pullForm (F c)`) is again
a hermitian form for the action of `R`, with the same `β`. -/
private lemma isHermitianAction_pullForm : IsHermitianAction L (B.pullForm (F c)) F β := by
  refine ⟨h.map_mem, fun x y ↦ ?_, fun x hx ↦ ?_, fun a x y ↦ ?_, fun l hl m hm ↦ ?_,
    h.star_eq_one_sub⟩
  · simpa [pullForm_apply_apply] using h.conj_symm (F c x) (F c y)
  · simpa [pullForm_apply_apply] using
      h.pos (F c x) fun h0 ↦ hx (action_injective c (h0.trans (map_zero (F c)).symm))
  · simp only [pullForm_apply_apply]
    rw [action_comm, h.adjoint, action_comm]
  · simpa [riemannForm_def, pullForm_apply_apply] using
      h.riemannForm_integral _ (h.map_mem c l hl) _ (h.map_mem c m hm)

/-- Descent along `c ≠ 0`. Say that a torsion point `x` has the constant `C` in degree `A` (a form
on `V`) when `A.HasShiftBound v x C` holds: for the size function `φ` (taken with `v`) of every
twisted theta function of degree `A`, `(sup φ)² ≤ C · sup_y φ(y) φ(y + x)`, with `y` running over
the torsion points. Suppose the torsion points `y` with `c y ∈ L` have the constant `1` in every
degree, and `c^* B - A` has a positive Riemann form, where `c^* B` is the pull-back
`B.pullForm (F c)`; then for a torsion point `w`, if `c w` (that is `h.torsionAction c w`) has the
constant `D` in degree `B`, `w` has the constant `D / v (#(c⁻¹ L / L)) ^ 2` in degree `A`. -/
lemma hasShiftBound_of_torsionAction
    (h_ker : ∀ (A : LatticeForm L) (y : torsionPoints L), F c y ∈ L → A.HasShiftBound v y 1)
    (h_pos : IsPosRiemann (B.pullForm (F c) + -A)) {D : ℝ≥0}
    (h_cw : B.HasShiftBound v (h.torsionAction c w) D) :
    A.HasShiftBound v w (D * (v (Nat.card (h.MulKernel c)))⁻¹ ^ 2) := by
  classical
  -- As `c^* B - A` is positive, it is enough to bound the size `φ` of a theta function `t` of
  -- degree `c^* B`. Split `t ∘ c⁻¹` into eigensums `s ξ` for the characters `ξ` of the kernel of
  -- `c`. These are theta functions of degree `B`, so `h_cw` bounds each of them, and `h_ker`
  -- compares their sizes with `φ`.
  have h_pull : IsHermitianAction L (B.pullForm (F c)) F β := isHermitianAction_pullForm h
  refine .of_isPosRiemann_sub h_pull.isAmpleType h_pos fun t ht x ↦ ?_
  have t_diff : Differentiable ℂ t := (mem_thetaSpace_iff_normalizedShift.mp ht).left
  set φ : torsionPoints L → ℝ≥0 := LatticeForm.sizeAt v (B.pullForm (F c)) t with φ_def
  have hφ : φ ∈ LatticeForm.sizes v (B.pullForm (F c)) :=
    .of_mem_thetaSpace h_pull.isAmpleType ht
  have h_transl (a : V) (t : V → ℂ) :
      h.normShift (F c a) (t ∘ (F c).inverse) = h_pull.normShift a t ∘ (F c).inverse := by
    ext
    simp [normalizedShift, riemannForm, action_comm, canonicalMultiplier, thetaShift_apply]
  have h_fixed : ∀ l ∈ L, h.normShift (F c l) (t ∘ (F c).inverse) = t ∘ (F c).inverse := by
    grind [mem_thetaSpace_iff_normalizedShift.mp ht]
  -- The eigensum `s ξ` for a character `ξ` of the kernel of `c` has degree `B` and the multiplier
  -- `χ l = h.multiplier l * ξ (c⁻¹ l)`, of finite order.
  let s (ξ : AddChar (h.MulKernel c) ℂ) : V → ℂ :=
    ∑ k : h.MulKernel c, ξ (-k) • h.normShift (F c k.out) (t ∘ (F c).inverse)
  have hs_mem (ξ : AddChar (h.MulKernel c) ℂ) : B.sizeAt v (s ξ) ∈ B.sizes v := by
    let χ (l : V) : ℂ :=
      h.multiplier l * if hl : l ∈ L then ξ ⟦⟨(F c).inverse l, by simpa [divLattice]⟩⟧ else 1
    have h_ah : IsAppellHumbert B χ := by
      refine ⟨h.isAppellHumbert.re_symm, fun l hl ↦ ?_, fun l hl m hm ↦ ?_⟩
      · simp [χ, hl, h.isAppellHumbert.norm_eq_one l hl]
      · simp [χ, h.isAppellHumbert.semicharacter, field, hl, hm, ← ξ.map_add_eq_mul, mul_assoc,
          add_mem]
        -- the class of a sum is the sum of the classes, by definition of the quotient
        exact Or.inl (Or.inl rfl)
    have h_order : ∀ l ∈ L, χ l ^ (2 * Nat.card (h.MulKernel c)) = 1 := by
      simp +contextual [χ, mul_pow, pow_mul, h.multiplier_sq, ← ξ.map_nsmul_eq_pow]
    have h_ample : IsAmpleType B χ :=
      ⟨h_ah, h.isAmpleType.isPosRiemann, 2 * Nat.card (h.MulKernel c), by simp, h_order⟩
    refine .of_mem_thetaSpace h_ample ⟨?_, fun l hl z ↦ ?_⟩
    · simp only [normShift, normalizedShift, canonicalMultiplier, LinearMap.smul_apply, s]
      fun_prop
    -- translation by `l ∈ L` multiplies `s ξ` by `ξ (c⁻¹ l)`
    let y : divLattice L F c := ⟨(F c).inverse l, by simpa [divLattice]⟩
    have h_eigen_z : h.normShift (F c y) (s ξ) z = ξ y * s ξ z :=
      congrFun (h.normShift_sum_eq_char_smul c h_fixed ξ y rfl) z
    simpa [y, χ, normalizedShift, ← neg_add_rev, exp_neg, field, mul_right_comm _ (ξ _), hl,
      canonicalMultiplier, thetaShift_apply] using h_eigen_z
  -- The size of `s ξ` at `c y` is at most a maximum of the `φ (y + k)`, `k` in the kernel of `c`;
  -- these translations do not raise the norm of `φ · φ (· + w)`.
  set T : torsionPoints L → torsionPoints L := h.torsionAction c
  have hs_le (ξ : AddChar (h.MulKernel c) ℂ) (y : torsionPoints L) :
      B.sizeAt v (s ξ) (T y) * B.sizeAt v (s ξ) (T y + T w) ≤ ⨆ z, φ z * φ (z + w) := by
    simp only [h.sizeAt_eq_normShift, ← map_mul, s, map_sum, univ.sum_apply, sum_mul_sum]
    refine v.map_sum_le fun i _ ↦ v.map_sum_le fun j _ ↦ ?_
    let a : torsionPoints L := ⟨i.out, h.mem_torsionPoints i.out⟩
    let b : torsionPoints L := ⟨j.out, h.mem_torsionPoints j.out⟩
    have h_one : LatticeForm.HasShiftBound v (B.pullForm (F c) + B.pullForm (F c))
        (y + w + b - (y + a) - w) 1 :=
      h_ker _ _ (by simp [a, b, sub_sub, add_right_comm, sub_mem])
    refine (mul_le_iSup_of_hasShiftBound hφ hφ h_one).trans_eq' ?_
    simp [a, b, ← map_add, T, φ_def, h_transl, h_pull.sizeAt_add,
      valuation_eq_one_of_pow_eq_one (orderOf_pos ξ).ne', ← pow_apply ξ]
  have h_card_pos : 0 < v (Nat.card (h.MulKernel c)) := by simp [v.pos_iff]
  -- Take square roots and move the order of the kernel to the left.
  suffices h_main : φ x * v (Nat.card (h.MulKernel c)) ≤ NNReal.sqrt (D * ⨆ z, φ z * φ (z + w)) by
    rwa [← le_sqrt_iff_sq_le, mul_right_comm, sqrt_mul, sqrt_sq, le_mul_inv_iff₀ h_card_pos]
  -- The eigensums add up to the order of the kernel times `t ∘ c⁻¹`.
  calc φ x * v (Nat.card (h.MulKernel c))
    _ = v (∑ ξ, h.normShift (T x) (s ξ) 0) := by
      simp [s, T, φ_def, sum_comm, ← sum_mul, h_transl, mem_thetaSpace_iff_normalizedShift.mp ht,
        AddChar.sum_apply_eq_ite, field, h_pull.sizeAt_eq_normShift, out_mem_iff_eq_zero]
    _ ≤ NNReal.sqrt (D * ⨆ z, φ z * φ (z + w)) := by
      refine v.map_sum_le fun ξ _ ↦ ?_
      -- Each term is bounded by the hypothesis at `c w`; `c` is onto the torsion points.
      grw [← h.sizeAt_eq_normShift, le_sqrt_iff_sq_le, h_cw _ (hs_mem ξ),
        ← (h.torsionAction_surjective c).iSup_comp, ciSup_le' (hs_le ξ)]

/-- Let `h` be a hermitian action of `R` on `V/L`: `B` is positive definite hermitian with Riemann
form integral on the full lattice `L`, each `F a` preserves `L` with `F (star a)` adjoint to `F a`,
and `star β = 1 - β`. Here `A.HasShiftBound v y C` means that for the size function φ of every
twisted theta function of degree `A`, (sup φ)² ≤ `C` · sup_x φ(x) φ(x + `y`), with x over the
torsion points. Suppose that arbitrarily close to `0` there are continuous linear maps `e` with
`F c (e x) = x` for some `c ≠ 0` in `R`, such that `A.HasShiftBound v y 1` holds for every form `A`
and every torsion point `y` with `F c y ∈ L`; then for every torsion point `w`,
`B.HasShiftBound v w C` holds for all sufficiently large `C`. -/
lemma eventually_hasShiftBound
    (h_frequently : ∃ᶠ e : V →L[ℂ] V in nhds 0, ∃ c : R, c ≠ 0 ∧ (∀ x : V, F c (e x) = x) ∧
      ∀ (A : LatticeForm L) (y : torsionPoints L), F c y ∈ L → A.HasShiftBound v y 1) :
    ∀ᶠ C : ℝ≥0 in atTop, B.HasShiftBound v w C := by
  -- The evaluation forms `ev y` on the finite-dimensional space `Θ` of theta functions of type
  -- `(2 B, multiplier²)`, taken at the points `y` such that `2 y - w` has the constant `1` in
  -- degree `2 B`, have no common zero that is not a zero of `ev 0`. So `ev 0` is a finite
  -- combination of them, and the sizes of the coefficients give the constant.
  let Θ : Submodule ℂ (V → ℂ) := (2 • B).thetaSpace (h.multiplier ^ 2)
  have h_findim : FiniteDimensional ℂ Θ :=
    (h.isAppellHumbert.nsmul 2).finite_thetaSpace
      (hp := h.isAmpleType.isPosRiemann.nsmul two_ne_zero)
  let ev (x : V) : Θ →ₗ[ℂ] ℂ := proj 0 ∘ₗ ((2 • B).thetaShift x).domRestrict Θ
  let Y : Type := {y : torsionPoints L // (B + B).HasShiftBound v (y + y - w) 1}
  have h_ker : ⨅ y : Y, LinearMap.ker (ev y) ≤ LinearMap.ker (ev 0) := by
    intro f hf
    have hf_zero (y : Y) : (f : V → ℂ) y = 0 := by
      simpa [ev, thetaShift_apply] using (Submodule.mem_iInf _).mp hf y
    have hf_diff : Differentiable ℂ (f : V → ℂ) := f.property.1
    -- The midpoints of `w` and the points of the lattices `c⁻¹ L` lie in `Y`, and these lattices
    -- have arbitrarily small mesh.
    have hf_mid : (f : V → ℂ) ∘ midpoint ℝ (w : V) = 0 := by
      refine eq_zero_of_small_mesh (L := L) (hf_diff.continuous.comp (by fun_prop [midpoint]))
        (h_frequently.mono fun e ⟨c, hc_ne, h_inv, h_one⟩ ↦ ⟨F c, h_inv, fun z hz ↦ ?_⟩)
      have hc_inst : NeZero c := ⟨hc_ne⟩
      have h_sum : (w : V) + z ∈ torsionPoints L := add_mem w.property (h.mem_torsionPoints ⟨z, hz⟩)
      have mid_tors : midpoint ℝ (w : V) z ∈ torsionPoints L := by
        refine h_sum.imp' (fun n ↦ n * 2) fun n hn ↦ ?_
        simpa [two_smul, mul_smul] using hn
      let m : torsionPoints L := ⟨midpoint ℝ (w : V) z, mid_tors⟩
      exact hf_zero ⟨m, h_one _ _ (by simpa [m] using hz)⟩
    simpa [ev] using congrFun hf_mid (-w)
  obtain ⟨g, hg⟩ : ∃ g : Y →₀ ℂ, (g.sum fun y a ↦ a • ev y) = ev 0 :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (mem_span_of_iInf_ker_le_ker h_ker)
  filter_upwards [mem_atTop (g.support.sup (v ∘ g))] with C hC φ hφ x
  obtain @⟨χ, f, h_ample, hf⟩ := hφ
  have hφ : B.sizeAt v f ∈ B.sizes v := .of_mem_thetaSpace h_ample hf
  obtain ⟨hf_diff, hf_per⟩ : Differentiable ℂ f ∧
      ∀ l ∈ L, ∀ z : V, f (z + l) = χ l * Complex.exp (B l z + B l l / 2) * f z := hf
  -- `y ↦ f (x - y) f (x + y)` lies in `Θ` whatever the multiplier of `f`, and once normalised its
  -- size at `y` is `φ (x - y) φ (x + y)`, where `φ` is the size of `f`.
  have hP_mem : (fun y : V ↦ (-B x x).exp * f (x - y) * f (x + y)) ∈ Θ := by
    refine ⟨by fun_prop, fun l hl z ↦ ?_⟩
    have hf_back :
        f (x - z) = χ l * Complex.exp (B l (x - z - l) + B l l / 2) * f (x - z - l) := by
      rw [← hf_per l hl (x - z - l), sub_add_cancel]
    simp [← add_assoc, ← sub_sub, hf_back, hf_per, hl, exp_add, exp_sub, two_mul, field,
      h.multiplier_sq l hl]
  let P : Θ := ⟨fun y ↦ (-B x x).exp * f (x - y) * f (x + y), hP_mem⟩
  have hP (y : torsionPoints L) : v (ev y P) = B.sizeAt v f (x - y) * B.sizeAt v f (x + y) := by
    simp [LatticeForm.sizeAt, ev, P, ← map_mul, mul_mul_mul_comm _ (f _), ← exp_add, ← mul_assoc,
      thetaShift_apply]
    ring_nf
  calc B.sizeAt v f x ^ 2 = v (ev 0 P) := by simpa [sq] using (hP 0).symm
    _ = v (∑ y ∈ g.support, g y * ev y P) := by simp [← hg, Finsupp.sum]
    _ ≤ C * ⨆ z, B.sizeAt v f z * B.sizeAt v f (z + w) := by
      refine v.map_sum_le fun y hy ↦ ?_
      rw [map_mul, hP]
      exact mul_le_mul' ((le_sup hy).trans hC)
        (mul_le_iSup_of_hasShiftBound hφ hφ (by simpa using y.property))

/-- The contraction. Suppose that arbitrarily close to `0` there are linear maps `e` with (a) `e`
right inverse to the action `F c` of some `c ≠ 0` in `R`, and (b) every torsion point `y` with
`c y ∈ L` has the constant `1` in every degree (`A.HasShiftBound v y 1` for every form `A`: for the
size function `φ` of each twisted theta function of degree `A`, `(sup φ)² ≤ sup_x φ(x) φ(x + y)`
over torsion points `x`). Then `HasMultiplicativeNorm v L` holds: for any two forms and twisted
theta functions `f`, `g` of those degrees, the sup norm (with respect to `v`) of `f g` is the
product of the sup norms of `f` and `g`. -/
lemma hasMultiplicativeNorm_of_frequently_hasShiftBound
    (h_frequently : ∃ᶠ e : V →L[ℂ] V in nhds 0, ∃ c : R, c ≠ 0 ∧ (∀ x : V, F c (e x) = x) ∧
      ∀ (A : LatticeForm L) (y : torsionPoints L), F c y ∈ L → A.HasShiftBound v y 1) :
    HasMultiplicativeNorm v L := by
  -- Fix `c` so large that `c^* B - 2 B` is positive. It is enough to show that no torsion point
  -- distorts sizes: `A.HasShiftBound v w 1` for all `A` and `w`.
  have h_tendsto : Tendsto (fun e : V →L[ℂ] V ↦ pullForm e (B + B)) (nhds 0) (nhds 0) := by
    refine Continuous.tendsto' ?_ 0 0 (by aesop)
    simp only [continuous_clm_apply, pullForm_apply_apply, add_apply]
    fun_prop
  obtain ⟨e, ⟨c, hc_ne, hce, h_ker⟩, h_pos⟩ : ∃ e : V →L[ℂ] V,
      (∃ c : R, c ≠ 0 ∧ (∀ x : V, F c (e x) = x) ∧
        ∀ (A : LatticeForm L) (y : torsionPoints L), F c y ∈ L → A.HasShiftBound v y 1) ∧
      IsPosRiemann (B + -pullForm e (B + B)) :=
    (h_frequently.and_eventually
      (h_tendsto.eventually h.isAmpleType.isPosRiemann.eventually_add_neg)).exists
  have hc_inst : NeZero c := ⟨hc_ne⟩
  let C : ℝ≥0 := (v (Nat.card (h.MulKernel c)))⁻¹ ^ 2
  have h_const (w : torsionPoints L) (A : LatticeForm L) : A.HasShiftBound v w C := by
    obtain ⟨n, hn, hw⟩ : ∃ n : ℕ, n ≠ 0 ∧ n • (w : V) ∈ L := w.property
    -- It is enough to treat a degree `a • B` that exceeds `A`.
    obtain ⟨a, ha, h_exceeds⟩ := (h.isAmpleType.eventually_isPosRiemann_smul_sub A).exists
    have h_mul : IsHermitianAction L (a • B) F β := h.nsmul ha
    suffices h_aB : (a • B).HasShiftBound v w C from
      .of_isPosRiemann_sub h_mul.isAmpleType h_exceeds fun f hf ↦
        h_aB _ (.of_mem_thetaSpace h_mul.isAmpleType hf)
    -- Apply `LatticeForm.HasShiftBound.of_doubling` to the group `W` of `y` with `n • y ∈ L`: if
    -- some constant works on `W` and a constant `D` gives `D * C` in twice the degree, then `C`
    -- works on `W`.
    let W : Submodule ℤ (torsionPoints L) := L.comap (n • (torsionPoints L).subtype)
    refine LatticeForm.HasShiftBound.of_doubling (const W (a • B)) Subtype.val ?_ (fun D hD y ↦ ?_)
      ⟨w, hw⟩
    · -- Some constant works on `W`: each point has one by `eventually_hasShiftBound`, and `W` is
      -- finite modulo `L`.
      let consts (y : torsionPoints L) : Set ℝ≥0 := {D | (a • B).HasShiftBound v y D}
      have h_factors : (fun y : torsionPoints L ↦ consts y).FactorsThrough
          fun x : torsionPoints L ↦ L.mkQ x := by
        intro y y' h_eq
        have shift_eq (φ : torsionPoints L → ℝ≥0) (hφ : φ ∈ (a • B).sizes v)
            (z : torsionPoints L) : φ (z + y) = φ (z + y') :=
          factorsThrough_mkQ_of_mem_sizes hφ (by simpa using h_eq)
        exact Set.ext fun _ ↦ forall₂_congr fun φ hφ ↦ by simp only [shift_eq φ hφ]
      have h_fin : (Set.range fun y : W ↦ consts y).Finite :=
        finite_range_nsmul_torsion hn h_factors
      have h_mem : ⋂ y : W, consts y ∈ atTop :=
        (sInter_mem h_fin).mpr
          (Set.forall_mem_range.mpr fun y ↦ h_mul.eventually_hasShiftBound h_frequently)
      exact Set.nonempty_iInter.mp (nonempty_of_mem h_mem)
    · -- `c` keeps `W`, so a constant on `W` descends along `c` to twice the degree.
      have h_pos' : IsPosRiemann ((a • B).pullForm (F c) + -(a • B + a • B)) := by
        refine ⟨fun z ↦ ?_⟩
        simpa [riemannForm, action_injective c (hce _), map_eq_zero_iff, action_injective] using
          (h_pos.nsmul ha).riemannForm_pos (F c z)
      exact h_mul.hasShiftBound_of_torsionAction h_ker h_pos'
        (hD ⟨h.torsionAction c y, by simpa [W] using h.map_mem c _ y.property⟩)
  -- A constant valid in all degrees improves to `1`, by `LatticeForm.HasShiftBound.of_doubling` for
  -- the family of all degrees.
  have h_one (w : torsionPoints L) (A : LatticeForm L) : A.HasShiftBound v w 1 := by
    exact .of_doubling (fun A ↦ A) (fun _ ↦ w) ⟨C, h_const w⟩
      (fun D hD A ↦ by simpa using hD (A + A)) A
  -- One inequality is general; the other is `mul_le_iSup_of_hasShiftBound` with `w = 0`.
  intro A A' φ ψ hφ hψ
  refine (ciSup_mul_le_ciSup_mul_ciSup (bddAbove_of_mem_sizes hφ)
    (bddAbove_of_mem_sizes hψ)).antisymm (iSup_mul_iSup_le fun x y ↦ ?_)
  simpa using mul_le_iSup_of_hasShiftBound hφ hψ (h_one (y - x - 0) (A + A'))

/-- The multiplicative norm from expanding multiplications. Let `R`, a domain of characteristic zero
and finite over ℤ, act on `V / L` with the hermitian data `h`. Let `p` be a prime with `v p < 1`,
and let `n`, prime to `p`, map the dual lattice of `B` into `L`. Suppose every neighbourhood of `0`
holds a right inverse of `F c` for some `c ∈ R` that is not a unit, is prime to `star c`, divides a
power of `p` and has `v (det (F (star c))) = 1`. Then `V / L` has good reduction at `v` in analytic
form. For any degrees and any sizes φ, ψ of twisted theta functions f, g of those degrees, the sup
norm (on torsion points) of φψ, the size of fg, is the product of the sup norms. -/
lemma _root_.New.ThetaTori.hasMultiplicativeNorm_of_expanding [CharZero R] {n p : ℕ} (hn : ¬p ∣ n)
    (h_dual : ∀ a ∈ B.dualLattice, n • a ∈ L) (hp : p.Prime) (hv : v p < 1)
    (h_expand : ∃ᶠ e : V →L[ℂ] V in nhds 0, ∃ (c : R) (k : ℕ),
      (∀ x : V, F c (e x) = x) ∧
      ¬IsUnit c ∧ IsCoprime c (star c) ∧ c ∣ p ^ k ∧
      v (F (star c)).det = 1) :
    HasMultiplicativeNorm v L := by
  -- By `IsHermitianAction.hasMultiplicativeNorm_of_frequently_hasShiftBound` it is enough to show
  -- `HasShiftBound` with constant `1`, in any degree `A`, for the points `y` killed by `c`. Take
  -- `i ≡ n mod p` with `i • B - A` positive and apply `hasShiftBound_one_of_ker` to `i • B` and a
  -- power of `c`.
  refine h.hasMultiplicativeNorm_of_frequently_hasShiftBound
    (h_expand.mono fun e ⟨c, k, h_inv, h_nonunit, h_cop, h_dvd, h_det⟩ ↦ ?_)
  have hc_ne : c ≠ 0 := fun hc0 ↦ by simp [IsCoprime, hc0] at h_cop
  have hc_inst : NeZero c := ⟨hc_ne⟩
  refine ⟨c, hc_ne, h_inv, fun A y hy ↦ ?_⟩
  obtain ⟨i, hi, hi0, h_pos⟩ : ∃ i : ℕ, i ≡ n [MOD p] ∧ i ≠ 0 ∧ IsPosRiemann (i • B + -A) :=
    ((Nat.frequently_modEq hp.ne_zero n).and_eventually
      (h.isAmpleType.eventually_isPosRiemann_smul_sub A)).exists
  -- `n i` is prime to `p`, hence to `c`; so `c` is a unit of the finite ring `R / n i`, and
  -- `c ^ (j + 1) ≡ 1 mod n i` for some `j`.
  have hpi : ¬p ∣ n * i := hp.not_dvd_mul hn (mt (hi.dvd_iff dvd_rfl).mp hn)
  have h_cop_pow_p : IsCoprime ((p : R) ^ k) ((n * i : ℕ) : R) :=
    (hp.coprime_iff_not_dvd.mpr hpi).cast.pow_left
  have h_cop_ni : IsCoprime c (n * i) := by
    exact_mod_cast h_cop_pow_p.mono h_dvd dvd_rfl
  have h_finite : Finite (R ⧸ span {(n * i : R)}) := finiteQuotientOfFreeOfNeBot _ (by aesop)
  have h_unit : IsUnit (Ideal.Quotient.mk (span {(n * i : R)}) c) :=
    (h_cop_ni.map _).isUnit_of_dvd (by simp)
  obtain ⟨m, hm_pos, h_pow⟩ := h_unit.isOfFinOrder.exists_pow_eq_one
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one.mpr hm_pos
  have h_dvd_pow : (n * i : R) ∣ c ^ (j + 1) - 1 := mk_span_eq_iff_dvd_sub.mp h_pow
  have h_cop_pow : IsCoprime (c ^ (j + 1)) (star (c ^ (j + 1))) := by simpa using h_cop.pow
  -- A non-unit prime to its conjugate differs from it.
  have h_ne_star : c ^ (j + 1) ≠ star (c ^ (j + 1)) := by
    intro h_eq
    exact h_nonunit (by simpa using h_cop_pow.isUnit_of_dvd h_eq.dvd)
  -- `c ^ (j + 1) - 1` and its conjugate are multiples of `n i`, which maps the dual lattice of
  -- `i • B` into `L`.
  have h_tor (a : V) (ha : a ∈ (i • B).dualLattice) : n • i • a ∈ L :=
    h_dual _ (mem_dualLattice_nsmul.mp ha)
  have h_dual_of_dvd {u : R} (hu : (n * i : R) ∣ u - 1) :
      ∀ a ∈ (i • B).dualLattice, F u a - a ∈ L := by
    obtain ⟨t, ht⟩ := hu
    intro a ha
    simpa [eq_add_of_sub_eq ht] using h.map_mem t _ (h_tor a ha)
  have h_dvd_star : (n * i : R) ∣ star (c ^ (j + 1)) - 1 := by
    simpa using map_dvd starRingAut h_dvd_pow
  -- `p ^ k` is a multiple of `c`
  have hy_p : p ^ k • (y : V) ∈ L := by
    obtain ⟨r, hr⟩ := h_dvd
    have h_mem : F ((p ^ k : ℕ) : R) y ∈ L := by grind [action_comm, map_mem]
    simpa only [map_natCast, ContinuousLinearMap.natCast_apply] using h_mem
  have h_det_pow : v (LinearMap.det (F (star (c ^ (j + 1))) : V →ₗ[ℂ] V)) = 1 := by simp [h_det]
  exact (h.nsmul hi0).hasShiftBound_one_of_ker rfl
    (h_dual_of_dvd h_dvd_pow) (h_dual_of_dvd h_dvd_star) h_ne_star hp hv
    h_det_pow h_pos (by grind [map_mem]) h_cop_pow hy_p

end New.ThetaTori.IsHermitianAction

/-! ## Good reduction of a theta torus over a good prime -/

section ArcReduction

open NumberField IsLocalRing Valuation LinearMap Ideal IsPrime valuationSubring
  New.ThetaTori.PeriodMap

/-- The average `(x.automorphyForm + i^* x.automorphyForm) / 2` of the form of the theta torus `x`
over multiplication by `i` has the same Riemann form as `x.automorphyForm`. -/
private lemma New.ThetaTori.ThetaTorus.riemannForm_smul_add_pullForm {E : Type} [Field E]
    [CMBase E] {V : Type} [FinComplexSpace V] {D : PEL E} {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V) :
    riemannForm ((2⁻¹ : ℂ) • (x.automorphyForm + x.automorphyForm.pullForm (Complex.I • 1))) =
      x.automorphyForm.riemannForm := by
  ext
  simp [riemannForm, re_symm]
  ring

/-- The average `(x.automorphyForm + i^* x.automorphyForm) / 2` of the form of the theta torus `x`
over multiplication by `i` is a hermitian form for the action `x.intAction` of `𝓞 E`, with
`β = D.β`. -/
private lemma New.ThetaTori.ThetaTorus.isHermitianAction_smul_add_pullForm {E : Type} [Field E]
    [CMBase E] {V : Type} [FinComplexSpace V] {D : PEL E} {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V) :
    IsHermitianAction x.periodLattice ((2⁻¹ : ℂ) •
      (x.automorphyForm + x.automorphyForm.pullForm (Complex.I • 1)))
      x.intAction D.β where
  map_mem := x.intAction_mem_periodLattice
  conj_symm y z := by
    simpa [Complex.ext_iff, re_symm, add_comm] using x.re_symm (Complex.I • y) (Complex.I • z)
  pos y hy := by simpa [riemannForm, field] using x.isPosRiemann.riemannForm_pos y hy
  adjoint := by simp [← adjoint]
  riemannForm_integral := by
    rw [x.riemannForm_smul_add_pullForm]
    exact x.isAppellHumbert_periodLattice.le_dualLattice
  star_eq_one_sub := D.star_beta

/-- Let `ρ` map `𝓞 E` into the valuation ring of `v`, agreeing with `Φ v₀`, and let the prime of
`𝓞 E` below the maximal ideal of the valuation ring be good for `D`. Then the theta torus `x` has
good reduction for `v` (`New.ThetaTori.HasGoodReduction` for `x.automorphyForm`, `x.multiplier` and
`D.paddedNorm`), and the order of `D.dualTorsion` has valuation `1`. -/
lemma New.ThetaTori.ThetaTorus.hasGoodReduction_and_val_card_eq_one {E : Type} [Field E] [CMBase E]
    {V : Type} [FinComplexSpace V] {D : PEL E} {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V) {v : Valuation ℂ NNReal}
    {ρ : 𝓞 E →+* v.valuationSubring} (hρ : ∀ c : 𝓞 E, ρ c = Φ v₀ c.val)
    (hw : D.IsGoodAt (Ideal.comap ρ (maximalIdeal v.valuationSubring))) :
    HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm ∧ v (Nat.card D.dualTorsion) =
      1 := by
  -- Apply `hasMultiplicativeNorm_of_expanding` with `c = star a`, where `a` generates a high power
  -- of the second prime `w` that contains `p` and `β - b`, and is large at all complex embeddings.
  obtain ⟨⟨hr, hT⟩, p, b, hp, hp_mem, hb_mem, h_coprime, -, h_second⟩ := hw
  obtain ⟨w, hw_ne, hp_w, hb_w⟩ := h_second
  have v_eq_one {y : 𝓞 E} (hy : y ∉ comap ρ (maximalIdeal v.valuationSubring)) :
      v (Φ v₀ y.val) = 1 := by
    rw [← hρ]
    exact (integers v).one_of_isUnit (of_not_not hy)
  have hvT : v (Nat.card D.dualTorsion) = 1 := by simpa using v_eq_one hT
  have hvr : v D.paddedNorm = 1 := by simpa using v_eq_one hr
  have hvp : v p < 1 := by simpa [v.mem_maximalIdeal_iff] using hp_mem
  have hvβ : v (starRingEnd ℂ (Φ v₀ D.β.val) - b) = 1 := by
    simpa using v_eq_one (notMem_of_isCoprime_of_mem h_coprime hb_mem)
  -- As `w` is maximal and differs from the prime of `ρ`, some `t ∈ w` is a unit at `Φ v₀`.
  obtain ⟨t, ht_w, ht_not⟩ : ∃ t ∈ w.asIdeal, t ∉ comap ρ (maximalIdeal v.valuationSubring) :=
    Set.not_subset.mp fun h_le ↦ hw_ne (w.isMaximal.eq_of_le ne_top' h_le)
  -- The dual lattice lies over `D.dualTorsion`, so multiplying by `Nat.card D.dualTorsion` carries
  -- it into `x.periodLattice`.
  have h_tor : ∀ a ∈ x.automorphyForm.dualLattice, Nat.card D.dualTorsion • a ∈ x.periodLattice :=
    fun a ha ↦
    x.card_nsmul_mem_periodLattice (x.dualLattice_periodLattice.le ha)
  suffices h_norm : HasMultiplicativeNorm v x.periodLattice from
    ⟨{ x.hasGoodReduction_one with
       dual_torsion := ⟨Nat.card D.dualTorsion, hvT, h_tor⟩
       val_eq_one := hvr
       hasMultiplicativeNorm := h_norm }, hvT⟩
  -- Averaging `x.automorphyForm` over multiplication by `i` gives a hermitian form with the same
  -- Riemann form.
  let H : LatticeForm x.periodLattice := (2⁻¹ : ℂ) •
    (x.automorphyForm + x.automorphyForm.pullForm (Complex.I • 1))
  have hp_ndvd : ¬p ∣ Nat.card D.dualTorsion := fun h_dvd ↦ hT (mem_of_dvd _ h_dvd.natCast hp_mem)
  have h_dual_H : ∀ a ∈ H.dualLattice, Nat.card D.dualTorsion • a ∈ x.periodLattice := fun a ha ↦
    h_tor a (by grind [RealComplexForm.dualLattice, x.riemannForm_smul_add_pullForm])
  have h_herm : IsHermitianAction x.periodLattice H x.intAction D.β :=
    x.isHermitianAction_smul_add_pullForm
  refine hasMultiplicativeNorm_of_expanding h_herm hp_ndvd h_dual_H hp hvp ?_
  -- The inverse of `x.intAction c` is `complexMul` of a small vector, and `complexMul` is
  -- continuous at `0`.
  have h_cont : Continuous x.isPeriodMap.complexMul := by
    simp only [continuous_clm_apply, Variety.IsPeriodMap.complexMul_apply_apply]
    fun_prop
  refine (h_cont.tendsto' 0 _ (map_zero _)).frequently
    (Metric.nhds_basis_ball.frequently_iff.mpr fun r hr_pos ↦ ?_)
  obtain ⟨a, ⟨k, ha⟩, ha_unit, ha_large⟩ :
      ∃ a : 𝓞 E, (∃ k : ℕ, w.asIdeal ^ k = span {a}) ∧ ¬IsUnit a ∧ ∀ σ : E →+* ℂ, ‖σ a‖⁻¹ < r :=
    exists_pow_eq_span_inv_lt w.one_lt_q hr_pos
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    exact pow_ne_zero k w.ne_bot (by simpa [ha_zero] using ha)
  have dvd_pow {y : 𝓞 E} (hy : y ∈ w.asIdeal) : a ∣ y ^ k := by
    simpa [ha, mem_span_singleton] using pow_mem_pow hy k
  -- If `w` contains a unit at `σ`, then `a` divides a unit among `v`-integers, so it is a unit.
  have unit_at (σ : E →+* ℂ) {y : 𝓞 E} (hy : y ∈ w.asIdeal) (hvy : v (σ y) = 1) : v (σ a) = 1 := by
    obtain ⟨c, hc⟩ := dvd_pow hy
    have v_le (z : 𝓞 E) : v (σ z) ≤ 1 :=
      (integers (v.comap σ)).mem_of_integral (RingOfIntegers.isIntegral_coe z).tower_top
    have h_prod : 1 ≤ v (σ a) * v (σ c) := by
      simpa [hvy] using (congrArg (fun z : 𝓞 E ↦ v (σ z)) hc).le
    exact eq_one_of_one_le_mul_left (v_le a) (v_le c) h_prod
  have h_star_nonunit : ¬IsUnit (star a) := by simpa using ha_unit
  have h_star_dvd : star a ∣ (p : 𝓞 E) ^ k := by simpa using map_dvd starRingAut (dvd_pow hp_w)
  refine ⟨fun u ↦ (Φ u (star a))⁻¹, by simp [pi_norm_lt_iff, hr_pos, ha_large], star a, k, ?_,
    h_star_nonunit, ?_, h_star_dvd, ?_⟩
  · simp [intAction, ← x.realEquiv.eq_symm_apply, funext_iff, ha_ne]
  · -- `a` divides a power of `β - b`, and `star a` a power of its conjugate.
    have h_star : star a ∣ (star D.β - b) ^ k := by simpa using map_dvd starRingAut (dvd_pow hb_w)
    simpa using (h_coprime.pow.mono (dvd_pow hb_w) h_star).symm
  · -- In the standard form of the action the determinant is a product of powers of `Φ v₀ a` (a unit
    -- by `t`), its conjugate and `Φ u a`, `u ≠ v₀` (units by `β - b`, using `D.emb_beta_eq_of_ne`).
    obtain ⟨ε, hε⟩ := x.exists_std_equiv
    have h_v₀ : v (Φ v₀ a.val) = 1 := unit_at _ ht_w (v_eq_one ht_not)
    have h_conj : v (star (Φ v₀) a.val) = 1 := unit_at _ hb_w (by simpa)
    have h_other u (hu : u ≠ v₀) : v (Φ u a.val) = 1 :=
      unit_at _ hb_w (by simpa [D.emb_beta_eq_of_ne u hu])
    simpa [← det_conj _ ε, det_prodMap, piMap, det_pi, hε, h_v₀,
      Subtype.forall'.mp h_other] using Or.inl h_conj

end ArcReduction
