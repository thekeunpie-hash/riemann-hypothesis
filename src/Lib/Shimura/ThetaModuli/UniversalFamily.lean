module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PiTensorProduct
import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Lib.Shimura.ThetaModuli.PELThetaTori
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Lib.Shimura.Uniformisation.TorusModel
public import Lib.Adelic.Hecke.ClassSums
import Lib.General.Geometry.SerreTheorem
import Lib.Shimura.AbelianScheme.Pairings
import TauCeti.NumberTheory.NumberField.Countable
public import Lib.Shimura.IntegralModel.UniversalFamily
import Lib.General.Geometry.SmoothnessCriterion
import Lib.Shimura.Deformation.TangentBound
import Lib.Shimura.GoodReduction.MultiplicativeNorm
import Lib.Shimura.IntegralModel.BallImmersion

section
/-!
# Riemann's theta relation and the reduction of theta functions at a valuation

Theta functions `θ_s = x.thetaCoord s` (`s ∈ D.dualTorsion`) of a theta torus
`x : New.ThetaTori.ThetaTorus` and their reduction at a valuation `v` of `ℂ`.

* `New.ThetaTori.ThetaTorus.isCutOutAt_reduction`: under good reduction, the ideal of the reductions
  of all theta vectors `(θ_s z)_s` has the expected ranks and is cut out by the level points.
* `New.ThetaTori.ThetaTorus.riemann_relation`: Riemann's theta relation of degree `D.paddedNorm` in
  one variable.
* `New.ThetaTori.ThetaTorus.exists_forall_valuation_thetaCoord_zero_le`: each `s` is `u + (s - u)`
  with theta constants of largest valuation.
* `New.ThetaTori.ThetaTorus.IsRiemannTuple`, `New.paddingTuple`: the systems of coefficients
  used in Riemann's relation.

Conventions: `x.torsionLift s` is a chosen lift of the torsion class `s`, `x.latticeOver S` the
lattice over a group `S` of classes, `x.intAction a` multiplication by `a ∈ 𝓞 E`, `x.multiplier` the
multiplier χ of the `θ_s`, and e(t) = exp(2πi t); `IsIntegralCoords w p` says that `p` are integral
homogeneous coordinates of a complex vector `w`, one of them a unit.

Notions from other files:
* `New.ThetaTori.ThetaTorus`: a polarised period map to `V`, with reflection matrix `ℓ`, such that
  multiplication by `star a` is adjoint to multiplication by `a ∈ 𝓞 E` for the form
  `x.automorphyForm`. In suitable coordinates `a` acts on `V` diagonally, through the complex
  embeddings of `E`.
* `New.ThetaTori.PeriodMap.thetaCoord`: The theta coordinate `θ_t`, `t ∈ T`: the normalised
  translate (`New.ThetaTori.normalizedShift`) of
  `New.ThetaTori.PeriodMap.exists_generator_thetaSpace` by the chosen lift `a_t` of `t`.
* `New.RealComplexForm.thetaShift` B a: the twisted translation f ↦ (z ↦ exp(−B(a,z) − B(a,a)/2)
  f(z + a)).
* `New.ThetaTori.LatticeForm.thetaNorm`: the supremum over torsion points x of the sizes
  `New.ThetaTori.LatticeForm.sizeAt` v(exp(−B(x,x)/2) f(x)). `New.ThetaTori.HasGoodReduction` asks,
  for an ample type on the lattice L, that this norm be multiplicative, that r > 1 and v(r) = 1, and
  that some N with v(N) = 1 multiply the dual lattice into L.

## Relation to the literature

Known result: Normal generation of sections on abelian varieties, kept under good reduction. Only
degrees that are powers of one integer r are treated, over a rank-one valuation ring of the complex
numbers, where powers of the sup-norm ball of theta functions are the balls and reduction keeps the
ranks. No cohomology or vanishing theorem is used. Source: S. Koizumi, Theta relations and
projective normality of abelian varieties, Amer. J. Math. 98 (1976); T. Sekiguchi, J. Math. Soc.
Japan 29 (1977) for characteristic p; G. Kempf, Multiplication over abelian varieties, Amer. J.
Math. 110 (1988).

Known result: Riemann's theta relations. Here they are stated in one variable for the theta
coordinates of a PEL torus, with multipliers in the ring of integers of a CM field in place of the
matrix with entries ±1/2. They are proved by Schur orthogonality for the theta group. Source: C.-L.
Chai, Riemann's theta formula (2014), Theorem 1.2; A. Nagano, On Riemann type relations for theta
functions on bounded symmetric domains of type I, arXiv 2301.09243 (2023), Theorem 1.1; D. Mumford,
On the equations defining abelian varieties I, Invent. Math. 1 (1966) §3; G. Kempf, Linear systems
on abelian varieties, Amer. J. Math. 111 (1989) 65–94.
-/

@[expose] public section

noncomputable section

namespace New.ThetaTori.ThetaTorus

open Module Submodule NNReal Variety ThetaNull MvPolynomial Complex Function NumberField Finset
  Fintype thetaSpace Finite LatticeForm PeriodMap

attribute [local instance low] Fintype.ofFinite

variable {V E k K : Type} [FinComplexSpace V]
  {v : Valuation ℂ ℝ≥0} [Field E] [CMBase E]
  {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ}
  (x : ThetaTorus D g ℓ V) [Fintype K]
  (a : K → 𝓞 E) {μ μ' : K → D.dualTorsion} {w : V} {t : D.dualTorsion} (p : K → 𝓞 E × 𝓞 E)

/-- The ring of integers `𝓞 E` acts on the torsion group `D.dualTorsion`: the action of `𝓞 E` on
adelic torsion classes preserves `D.dualTorsion`. -/
instance : Module (𝓞 E) D.dualTorsion :=
  module ⟨_, by
    -- Move `a` across the form: it becomes `star a`, which preserves the kernel of `torsionClass`.
    rintro a ⟨y⟩ hy
    refine (D.mem_dualTorsion _).mpr fun z hz ↦ ?_
    simpa [xiForm, ↓star_smul] using
      (D.mem_dualTorsion y).mp hy (algebraMap E (𝔸f E) (star a) • z)
        (torsionClass.ker.smul_mem (star a) hz)⟩

/-! ### Systems of coefficients -/

/-- The pairs `p l = (a_l, b_l)` in `𝓞 E` satisfy `∑ ā_l a_l = r` and `∑ ā_l b_l = 0`, where
`r = D.paddedNorm` is the degree attached to the PEL datum `D` and `ā` is the complex conjugate
(`star`). -/
def IsRiemannTuple (D : PEL E) : Prop :=
  ∑ l : K, star (p l).1 * (p l).1 = D.paddedNorm ∧ ∑ l : K, star (p l).1 * (p l).2 = 0

/-- The family of coefficient pairs on two copies of the index set `K`: `(0, b_l)` on the first
copy, where `k l = (a_l, b_l)`, and `p l` on the second. -/
def doubledCoeffs (k : K → 𝓞 E × 𝓞 E) : K ⊕ K → 𝓞 E × 𝓞 E := Sum.elim (fun l ↦ (0, (k l).2)) p

/-! ### Products of theta functions and Riemann's relation -/

/-- The function `z ↦ ∏_k θ_{μ_k}(a_k z + b_k w)` on `V`, where `p k = (a_k, b_k)`, `θ_s` is the
theta coordinate `x.thetaCoord s` and `x.intAction a` is multiplication by `a ∈ 𝓞 E` on `V`. -/
def thetaProduct (μ : K → D.dualTorsion) (w z : V) : ℂ :=
  ∏ k : K, x.thetaCoord (μ k) (x.intAction (p k).1 z + x.intAction (p k).2 w)

/-- Let `p k = (a_k, b_k)` with `∑ ā_k a_k = r` and `∑ ā_k b_k = 0` (`hp`), let `∑ ā_k μ_k = t`
(`ht`), and let `y` lie in the lattice over `D.dualTorsion`. Write `x.thetaProduct p μ w` for the
function `z ↦ ∏_k θ_{μ_k}(a_k z + b_k w)`, where `θ_s` is `x.thetaCoord s`. If the twisted
translation (`New.RealComplexForm.thetaShift`) by `a_k u` sends `θ_{μ_k}` to
`χ(a_k u) e(⟨a_k y, μ_k⟩) θ_{μ'_k}` for every `k`, then the twisted translation by `u` for `r B`
sends `x.thetaProduct p μ w` to `χ(u)^r e(⟨y, t⟩)` times `x.thetaProduct p μ' w`. Here `χ` is
`x.multiplier`, and `e(⟨y, s⟩)` (`riemannPhase`) is `exp(2πi E(y, ·))` of the chosen lift of `s`,
with `E` the Riemann form of `B = x.automorphyForm`, and `r` is `D.paddedNorm`. -/
lemma thetaShift_thetaProduct {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D)
    (ht : ∑ k : K, star (p k).1 • μ k = t) {u y : V} (hy_mem : y ∈ x.latticeOver D.dualTorsion)
    (h_shift : ∀ k : K, x.automorphyForm.thetaShift (x.intAction (p k).1 u) (x.thetaCoord (μ k)) =
      (x.multiplier (x.intAction (p k).1 u) * x.automorphyForm.riemannPhase (x.intAction (p k).1 y)
        (x.torsionLift (μ k))) • x.thetaCoord (μ' k)) (z : V) :
    (D.paddedNorm • x.automorphyForm).thetaShift u (x.thetaProduct p μ w) z =
      x.multiplier u ^ D.paddedNorm * x.automorphyForm.riemannPhase y (x.torsionLift t) *
        x.thetaProduct p μ' w z := by
  -- Multiply the hypotheses `h_shift k` at `a z + b w` over all `k`; the exponents add up by four
  -- identities. `ht` holds for the lifts only modulo `x.periodLattice`, which pairs integrally
  -- with `y`.
  obtain ⟨hp_norm, hp_orth⟩ := hp
  have h_class : frameTorsionClass g (∑ k, star (p k).1 • ratLift g (μ k)) =
      frameTorsionClass g (ratLift g t) := by
    have h_coe_smul (a : 𝓞 E) (m : D.dualTorsion) :
        ((a • m : D.dualTorsion) : AdelicTorsion E D.Index) = a • (m : AdelicTorsion E D.Index) :=
          rfl
    simpa [map_smul, h_coe_smul] using congrArg Subtype.val ht
  have h_mem : ∑ k, x.intAction (star (p k).1) (x.torsionLift (μ k)) - x.torsionLift t ∈
      x.periodLattice := by
    have h_smul (c : 𝓞 E) (y : D.Index → E) :
        x.intAction c (x.periodPoint y) = x.periodPoint (c • y) := by
      simp [intAction, ← toRealVectors_smul]
    simp only [torsionLift, h_smul, ← map_sum]
    exact x.sub_mem_periodLattice_iff.mpr h_class
  obtain ⟨m, hm⟩ : ∃ m : ℤ, x.automorphyForm.riemannForm y
      (∑ k, x.intAction (star (p k).1) (x.torsionLift (μ k)) - x.torsionLift t) = m :=
    x.dualLattice_periodLattice.ge hy_mem _ h_mem
  -- Moving each coefficient across `x.automorphyForm` by adjunction turns `hp` into identities of
  -- sums.
  have h_norm (z : V) :
      ∑ k, x.automorphyForm u (x.intAction (star (p k).1) (x.intAction (p k).1 z)) = D.paddedNorm *
        x.automorphyForm u z := by
    simpa [map_sum, mul_sum, adjoint] using congrArg
      (fun c : 𝓞 E ↦ x.automorphyForm u (x.intAction c z)) hp_norm
  have h_orth : ∑ k, x.automorphyForm u (x.intAction (star (p k).1) (x.intAction (p k).2 w)) =
    0 := by
    simpa [map_sum, mul_sum, adjoint] using congrArg
      (fun c : 𝓞 E ↦ x.automorphyForm u (x.intAction c w)) hp_orth
  have h_chi : x.automorphyForm.riemannForm
    (x.intAction (D.rescaledBeta * ∑ k, star (p k).1 * (p k).1) u) u =
      x.automorphyForm.riemannForm (x.intAction (D.rescaledBeta * D.paddedNorm) u) u := by
        rw [hp_norm]
  -- `exp (π i r c) = exp (π i c) ^ r`, and `exp (2 π i m) = 1` drops out.
  have h_pow (c : ℂ) : cexp (Real.pi * I * (D.paddedNorm * c)) = cexp (Real.pi * I * c) ^
    D.paddedNorm := by
    simp [← exp_natCast_mul, mul_left_comm]
  have h_int (c : ℂ) : cexp (2 * Real.pi * I * (c + m)) = cexp (2 * Real.pi * I * c) := by
    simp [mul_add, exp_add, mul_comm _ (m : ℂ)]
  -- By adjunction and `h_chi` the multipliers give `χ(u) ^ r`; by `hm` the phases give
  -- `e(⟨y, t⟩)`, since `e(m) = 1`.
  have h_multiplier : ∏ k, x.multiplier (x.intAction (p k).1 u) = x.multiplier u ^
    D.paddedNorm := by
    simp [← ofReal_inj, riemannForm_def, mul_sum, mul_left_comm, adjoint, div_eq_inv_mul,
      canonicalMultiplier] at h_chi ⊢
    simp only [← mul_sum] at h_chi
    simp only [← exp_sum, ← mul_sum, h_chi, h_pow]
  have h_phase : ∏ k, x.automorphyForm.riemannPhase (x.intAction (p k).1 y) (x.torsionLift (μ k)) =
      x.automorphyForm.riemannPhase y (x.torsionLift t) := by
    simp [← ofReal_inj, sub_eq_iff_eq_add', map_sub, riemannForm_def,
      torsionLift, periodPoint, adjoint, div_eq_inv_mul] at hm ⊢
    simp only [← mul_sum] at hm
    simp only [← exp_sum, ← mul_sum, hm, h_int]
  -- The twisted translation of the product is the product of the twisted translations: their
  -- exponents add up by `h_norm` and `h_orth`.
  have h_translate : (D.paddedNorm • x.automorphyForm).thetaShift u (x.thetaProduct p μ w) z =
      ∏ k, x.automorphyForm.thetaShift (x.intAction (p k).1 u) (x.thetaCoord (μ k))
        (x.intAction (p k).1 z + x.intAction (p k).2 w) := by
    simp [adjoint, div_eq_inv_mul, thetaShift_apply, exp_add, exp_neg, thetaProduct]
    simp only [prod_mul_distrib, prod_inv_distrib, ← exp_sum, ← mul_sum, h_orth, h_norm, exp_zero,
      inv_one, one_mul, mul_left_comm (2⁻¹ : ℂ), add_right_comm]
  rw [h_translate, prod_congr rfl fun k _ ↦ congrFun (h_shift k) _]
  simp only [Pi.smul_apply, smul_eq_mul, thetaProduct, ← h_multiplier, ← h_phase, prod_mul_distrib]

/-- Translation by a rational point shifts the indices of a theta product. Let `y` be a rational
vector whose class `[y]` lies in `D.dualTorsion` (`hy`), let `u = x.periodPoint y` be its image in
`V`, and let `p` be a Riemann tuple (`hp`). Then the twisted translation by `u` for `r B` sends
`x.thetaProduct p μ w` to `χ(u)^r e(⟨β u, ∑ ā_k μ_k⟩)` times the product for `μ + a [y]`, where `χ`
is `x.multiplier`, `β = D.rescaledBeta ∈ 𝓞 E`, for which `β u` lies in
`x.latticeOver D.dualTorsion`, `p k = (a_k, b_k)`, `r = D.paddedNorm` and
`B = x.automorphyForm`. -/
lemma thetaShift_periodPoint_thetaProduct {y : D.Index → E}
    (hy : frameTorsionClass g y ∈ D.dualTorsion)
    {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D) (μ : K → D.dualTorsion) (z : V) :
    (D.paddedNorm • x.automorphyForm).thetaShift (x.periodPoint y) (x.thetaProduct p μ w) z =
      x.multiplier (x.periodPoint y) ^ D.paddedNorm *
        x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta (x.periodPoint y))
          (x.torsionLift ↑(∑ k : K, star (p k).1 • μ k)) *
        x.thetaProduct p (μ + (fun c : 𝓞 E × 𝓞 E ↦ c.1 • ⟨frameTorsionClass g y, hy⟩) ∘ p) w z := by
  -- Apply `thetaShift_thetaProduct` with `t = ∑ ā_k μ_k` itself (so `ht` is `rfl`) and the point
  -- `β u`, which lies in the lattice over `D.dualTorsion`.
  refine x.thetaShift_thetaProduct hp (t := ∑ k, star (p k).1 • μ k) rfl
    (x.intAction_rescaledBeta_mem_latticeOver le_rfl (x.mem_latticeOver.mpr hy)) (fun k ↦ ?_) z
  -- `a_k u` is the image of the rational vector `a_k • y`, whose class is `a_k [y]`; the theta law
  -- (`PeriodMap.thetaShift_thetaCoord`) for it gives the factor for `k`.
  have h_act : x.intAction (p k).1 (x.periodPoint y) = x.periodPoint ((p k).1 • y) := by
    simp [intAction, ← toRealVectors_smul]
  have h_class : frameTorsionClass g ((p k).1 • y) =
      (((p k).1 • ⟨frameTorsionClass g y, hy⟩ : D.dualTorsion) : AdelicTorsion E D.Index) :=
        map_smul ..
  rw [h_act]
  simpa [intAction, smul_comm (cmEmbedding (p k).1.val), add_comm, bicharacter] using
    x.thetaShift_thetaCoord h_class (μ k)

/-- Riemann's theta relation in one variable. Here x is a theta torus on V for the PEL datum `D`.
T = `D.dualTorsion` is the finite group of classes pairing trivially with all integral vectors, r =
`D.paddedNorm` ≥ 3, and T[r] = `D.rTorsion` is the r-torsion of T. For a tuple p = (a, b) with
values in 𝓞 E, `x.thetaProduct p μ w` is P(μ; z) = ∏_k θ_{μ_k}(a_k z + b_k w), where θ_s =
`x.thetaCoord s`.

Let p = (a, b) satisfy ∑ ā a = r, ∑ ā b = 0 (`hp`) and ∑ ā μ = t. Let q = (a', b') satisfy the same
with μ' in place of μ, and write P' for the product attached to q. Then |T| P'(μ'; 0) P(μ; z) = √[T
: T[r]] ∑_{s ∈ T} P(μ − a s; 0) P'(μ' + a' s; z), with both products taken at the same point w. -/
lemma riemann_relation {p : K → 𝓞 E × 𝓞 E} (hp : IsRiemannTuple p D)
    (ht : ∑ k : K, star (p k).1 • μ k = t) {q : K → 𝓞 E × 𝓞 E} (hq : IsRiemannTuple q D)
    (ht' : ∑ k : K, star (q k).1 • μ' k = t) [Fintype D.dualTorsion] (z : V) :
    Fintype.card D.dualTorsion * x.thetaProduct q μ' w 0 * x.thetaProduct p μ w z =
      (D.rTorsion.relIndex D.dualTorsion).sqrt *
        ∑ s : D.dualTorsion,
          x.thetaProduct p (μ - (fun c : 𝓞 E × 𝓞 E ↦ c.1 • s) ∘ p) w 0 *
            x.thetaProduct q (μ' + (fun c : 𝓞 E × 𝓞 E ↦ c.1 • s) ∘ q) w z := by
  -- Both products are theta functions of degree `r` for `x.latticeOver D.rTorsion`, whose dual
  -- lattice is `x.latticeOver D.dualTorsion`; apply Schur orthogonality over the lifts of
  -- `D.dualTorsion`.
  have hr : D.paddedNorm ≠ 0 := x.hasGoodReduction_one.one_lt.ne_bot
  have h_le : x.latticeOver D.rTorsion ≤ x.latticeOver D.lagrangian :=
    x.latticeOver_mono D.torsion_mem_lagrangian
  have h_dual : (D.paddedNorm • x.automorphyForm).dualLattice (L := x.latticeOver D.rTorsion) =
    x.latticeOver D.dualTorsion := by
    rw [← x.dualLattice_periodLattice]
    refine le_antisymm (dualLattice_nsmul_le hr fun _ ↦ (x.nsmul_mem_latticeOver hr).mp) ?_
    intro u hu l hl
    -- `r • l` lies in `x.periodLattice`, which pairs integrally with `u`.
    simpa using hu _ ((x.nsmul_mem_latticeOver hr).mpr hl)
  have h_discrete : DiscreteTopology (x.latticeOver D.rTorsion) :=
    x.discreteTopology_latticeOver_lagrangian.of_subset h_le
  have h_theta {p : K → 𝓞 E × 𝓞 E} {μ : K → D.dualTorsion} (hp : IsRiemannTuple p D)
      (hμ : ∑ k, star (p k).1 • μ k = t) :
      x.thetaProduct p μ w ∈
        (D.paddedNorm • x.automorphyForm).thetaSpace (L := x.latticeOver D.rTorsion) fun l ↦
          (x.multiplier ^ D.paddedNorm) l * x.automorphyForm.riemannPhase l (x.torsionLift t) := by
    have h_diff (s : D.dualTorsion) : Differentiable ℂ (x.thetaCoord s) :=
      (x.thetaCoord_mem_thetaSpace s).1
    refine ⟨by fun_prop [thetaProduct], fun l hl z ↦ ?_⟩
    -- Each factor is a theta function for `x.latticeOver D.lagrangian`, which contains the
    -- multiples of `l`.
    have h_mem (k : K) : x.intAction (p k).1 l ∈ x.latticeOver D.lagrangian := h_le <| by
      grind [=_ nsmul_mem_latticeOver, PEL.rTorsion, intAction_mem_periodLattice, =_ map_nsmul]
    simp only [Pi.pow_apply]
    rw [mul_right_comm,
      ← x.thetaShift_thetaProduct hp hμ (x.latticeOver_mono D.lagrangian_le_dualTorsion (h_le hl))
        fun k ↦
      thetaShift_of_mem (x.thetaCoord_mem_thetaSpace_lagrangian _) (h_mem k)]
    simp [field, thetaShift_apply, exp_add, exp_neg]
  let pt (s : D.dualTorsion) : (D.paddedNorm • x.automorphyForm).dualLattice
    (L := x.latticeOver D.rTorsion) :=
    ⟨x.torsionLift s, h_dual.ge (x.torsionLift_mem_latticeOver s)⟩
  -- Adding `u` permutes the lifts `pt s` modulo `x.latticeOver D.rTorsion`: `u` is the image of a
  -- rational vector `y`, and `s` goes to the class of `y` plus `s`.
  have h_perm (u : (D.paddedNorm • x.automorphyForm).dualLattice (L := x.latticeOver D.rTorsion)) :
      ∃ e : D.dualTorsion ≃ D.dualTorsion, ∀ s : D.dualTorsion,
        ↑(u + pt s - pt (e s)) ∈ x.latticeOver D.rTorsion := by
    obtain ⟨y, hy, hyu⟩ : ∃ y : D.Index → E,
      frameTorsionClass g y ∈ D.dualTorsion ∧ x.periodPoint y = u :=
      h_dual.le u.property
    use .addLeft ⟨_, hy⟩
    have h_class_zero (a : AdelicTorsion E D.Index) :
        frameTorsionClass g (y + ratLift g a - ratLift g (frameTorsionClass g y + a)) = 0 := by simp
    simp [pt, ← hyu, ← map_add, ← map_sub, torsionLift, h_class_zero]
  -- The Appell–Humbert datum of degree `r` for which both products are theta functions.
  have h_datum : IsAppellHumbert (L := x.latticeOver D.rTorsion) (D.paddedNorm • x.automorphyForm)
      fun l ↦ (x.multiplier ^ D.paddedNorm) l * x.automorphyForm.riemannPhase l (x.torsionLift t) :=
    ((x.isAppellHumbert_of_le h_le).nsmul _).mul_riemannPhase (x.torsionLift t) x.automorphyForm
  -- Schur orthogonality for the translates by the lifts `pt s`.
  have h_appell :
      ((D.rTorsion.relIndex D.dualTorsion).sqrt : ℂ) *
          ∑ s : D.dualTorsion, (D.paddedNorm • x.automorphyForm).thetaShift (-(pt s : V))
            (x.thetaProduct p μ w) 0 *
            (D.paddedNorm • x.automorphyForm).thetaShift (pt s) (x.thetaProduct q μ' w) z =
        Fintype.card D.dualTorsion * x.thetaProduct q μ' w 0 * x.thetaProduct p μ w z := by
    rw [← x.relIndex_latticeOver, ← h_dual]
    exact h_datum.sum_shift_mul_shift (hp := x.isPosRiemann.nsmul hr) D.dualTorsion pt h_perm
      ⟨_, h_theta hq ht'⟩ ⟨_, h_theta hp ht⟩ 0 z
  rw [← h_appell]
  congr with s
  -- The factors for `-s` and `s` cancel: the multiplier at the lift of `s`, written as an
  -- exponential, has `2 r`-th power `1` (`PeriodMap.riemannPhase_rescaledBeta_eq`).
  have h_phase : x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta (x.torsionLift s))
        (x.periodPoint (ratLift g s)) =
      x.automorphyForm.riemannPhase (x.periodPoint (ratLift g s))
        ((Nat.card D.dualTorsion / 2) • x.torsionLift s) :=
    x.riemannPhase_rescaledBeta_eq (x.torsionLift_mem_latticeOver s)
      (x.torsionLift_mem_latticeOver s) rfl
  have h_multiplier_sq :
      (cexp (Real.pi * I *
        (x.automorphyForm.riemannForm (x.intAction D.rescaledBeta
          (x.realEquiv (toRealVectors (ratLift g s))))
          (x.realEquiv (toRealVectors (ratLift g s))) : ℂ)) ^ D.paddedNorm) ^ 2 = 1 := by
    simpa [two_mul, add_mul, sq, torsionLift, periodPoint, canonicalMultiplier, exp_add, mul_pow]
      using congrArg (fun c : ℂ ↦ c ^ D.paddedNorm) h_phase
  have h_neg : -x.torsionLift s = x.periodPoint (-ratLift g s) := by simp [torsionLift, periodPoint]
  have h_neg_s : (⟨-s.val, neg_mem s.property⟩ : D.dualTorsion) = -s := rfl
  change (D.paddedNorm • x.automorphyForm).thetaShift (-x.torsionLift s) (x.thetaProduct p μ w) 0 *
      (D.paddedNorm • x.automorphyForm).thetaShift (x.torsionLift s) (x.thetaProduct q μ' w) z = _
  -- Translation by `∓` the lift of `s` shifts the indices (`thetaShift_periodPoint_thetaProduct`).
  rw [h_neg, torsionLift, x.thetaShift_periodPoint_thetaProduct (y := -ratLift g s) (by simp) hp,
    x.thetaShift_periodPoint_thetaProduct (y := ratLift g s) (by simp) hq]
  simp [ht, ht', field, sub_eq_add_neg, ← smul_neg, periodPoint, canonicalMultiplier, exp_neg,
    thetaProduct, h_neg_s, h_multiplier_sq]

/-- Let `θ_o(0)` have the largest valuation among the theta constants `θ_t(0)` (`ho`), and let that
valuation be at most those of `θ_{s-u}(0)` and `θ_{-u}(0)` (`h_best`). Then each of `θ_u(0)`,
`θ_{-u}(0)`, `θ_{s-u}(0)` has the largest valuation. -/
private lemma valuation_thetaCoord_le_of_le_inf {s u o : D.dualTorsion}
    (ho : ∀ t : D.dualTorsion, v (x.thetaCoord t 0) ≤ v (x.thetaCoord o 0))
    (h_best : v (x.thetaCoord o 0) ≤ v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)) :
    ∀ i ∈ [u, -u, s - u], ∀ t : D.dualTorsion, v (x.thetaCoord t 0) ≤ v (x.thetaCoord i 0) := by
  -- The symmetry `PeriodMap.exists_thetaCoord_sign_smul`, used twice at `0`, carries the bound
  -- from `-u` to `u`.
  obtain ⟨η, hη⟩ := x.exists_thetaCoord_sign_smul (-1)
  have h_symm (t : D.dualTorsion) : x.thetaCoord t 0 = η * x.thetaCoord (-t) 0 := by
    simpa using hη 0 t
  -- For `-u` and `s - u` the bound is `h_best` with `ho`.
  have h_rest : ∀ i ∈ [-u, s - u], ∀ t : D.dualTorsion,
    v (x.thetaCoord t 0) ≤ v (x.thetaCoord i 0) := by
    grind
  refine List.forall_mem_cons.mpr ⟨fun t ↦ ?_, h_rest⟩
  calc v (x.thetaCoord t 0) = v η * v (x.thetaCoord (-t) 0) := by rw [h_symm, map_mul]
    _ ≤ v η * v (x.thetaCoord (-u) 0) := by grw [ho (-t), h_best.trans inf_le_right]
    _ = v (x.thetaCoord u 0) := by rw [h_symm u, map_mul]

/-- The bound on the values of the size function in the proof of
`exists_forall_valuation_thetaCoord_zero_le`. Let `r = D.paddedNorm = k + 3` and `v |T| = 1` (`hv`),
let `θ_o(0) ≠ 0` have the largest valuation `top` among the theta constants (`ho`), and let `u`
maximise `min (v θ_{s-t}(0)) (v θ_{-t}(0))` over `t`, with maximum `best` (`hu`). If every
`v θ_t(z)` is at most `v (exp (B(z, z) / 2)) ρ` (`h_le`), `ρ` the norm of `θ_0`, then at each
torsion point `z` the product of the sizes (`New.ThetaTori.LatticeForm.sizeAt`) of `θ_s`,
`θ_{r o - s}` and `θ_0 ^ (k + 1)`, times `top`, is at most `best ρ ^ r`. The proof applies Riemann's
relation and the ultrametric inequality. Here `T = D.dualTorsion` and `B = x.automorphyForm`. -/
private lemma mul_sizeAt_le_inf_mul_thetaNorm_pow [Fintype D.dualTorsion] {s o u : D.dualTorsion}
    {k : ℕ} (hr_eq : D.paddedNorm = 2 + k + 1) (hv : v (Fintype.card D.dualTorsion) = 1)
    (ho : ∀ t : D.dualTorsion, v (x.thetaCoord t 0) ≤ v (x.thetaCoord o 0))
    (hu : ∀ t : D.dualTorsion, v (x.thetaCoord (s - t) 0) ⊓ v (x.thetaCoord (-t) 0) ≤
      v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0))
    (h_top : x.thetaCoord o 0 ≠ 0)
    (h_le : ∀ (t : D.dualTorsion) (z : torsionPoints x.periodLattice),
      v (x.thetaCoord t z) ≤ v (exp (x.automorphyForm z z / 2)) * x.automorphyForm.thetaNorm v
        (x.thetaCoord 0))
    (z : torsionPoints x.periodLattice) :
    v (x.thetaCoord o 0) *
        (x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
          (x.thetaCoord (D.paddedNorm • o - s)) *
          ((k + 1) • x.automorphyForm).sizeAt v (x.thetaCoord 0 ^ (k + 1))) z ≤
      (v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)) *
        x.automorphyForm.thetaNorm v (x.thetaCoord 0) ^ D.paddedNorm := by
  set top : ℝ≥0 := v (x.thetaCoord o 0)
  set best : ℝ≥0 := v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)
  set ρ : ℝ≥0 := x.automorphyForm.thetaNorm v (x.thetaCoord 0)
  set φ := x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
    (x.thetaCoord (D.paddedNorm • o - s)) *
    ((k + 1) • x.automorphyForm).sizeAt v (x.thetaCoord 0 ^ (k + 1))
  let κ : Type := Option (Fin 2 ⊕ Fin k)
  let μ : κ → D.dualTorsion := fun i ↦ i.elim (D.paddedNorm • o - s) (Sum.elim ![s, 0] 0)
  let oneZero : κ → 𝓞 E × 𝓞 E := const κ (1, 0)
  have h_one : IsRiemannTuple oneZero D := by simp [IsRiemannTuple, oneZero, κ, hr_eq]
  -- `|T| θ_o(0) ^ r P(μ; z) = √index ∑ t, P(μ - t; 0) θ_{o + t}(z) ^ r`, where `P(μ; ·)` is the
  -- product of the `θ_{μ i}`.
  have h_sum : ∑ i : κ, star (oneZero i).1 • μ i = ∑ i : κ, star (oneZero i).1 • const κ o i := by
    simp [oneZero, κ, μ, hr_eq]
  let term (t : D.dualTorsion) : ℂ :=
    x.thetaProduct oneZero (μ - (fun c : 𝓞 E × 𝓞 E ↦ c.1 • t) ∘ oneZero) 0 0 *
      x.thetaProduct oneZero (const κ o + (fun c : 𝓞 E × 𝓞 E ↦ c.1 • t) ∘ oneZero) 0 z
  have h_rel :
      (Fintype.card D.dualTorsion : ℂ) * x.thetaProduct oneZero (const κ o) 0 0 *
          x.thetaProduct oneZero μ 0 z = (D.rTorsion.relIndex D.dualTorsion).sqrt * ∑ t :
            D.dualTorsion, term t :=
    x.riemann_relation (w := 0) h_one h_sum h_one rfl z
  have h_bound :
      v (card D.dualTorsion * x.thetaProduct oneZero (const κ o) 0 0 * x.thetaProduct oneZero μ 0 z)
        ≤
        best * top ^ (k + 2) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^ D.paddedNorm := by
    -- Bound each term on the right of `h_rel` (ultrametric inequality): one constant is at most
    -- `best`, the others at most `top`. `v.leSubmodule c` is the set of `y` with `v y ≤ c`.
    rw [h_rel]
    suffices h_terms : ∑ t : D.dualTorsion, term t ∈
          v.leSubmodule (best * top ^ (k + 2) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^
            D.paddedNorm) from
      (v.leSubmodule _).smul_mem (Nat.cast (D.rTorsion.relIndex D.dualTorsion).sqrt) h_terms
    refine sum_mem fun t _ ↦ ?_
    have h_pair : v (x.thetaCoord (s - t) 0) * v (x.thetaCoord (-t) 0) ≤ best * top := by
      grw [← min_mul_max, hu t, max_le (ho (s - t)) (ho (-t))]
    calc v _ = v (x.thetaCoord (D.paddedNorm • o - s - t) 0) *
          (v (x.thetaCoord (s - t) 0) * v (x.thetaCoord (-t) 0) * v (x.thetaCoord (-t) 0) ^ k) *
          v (x.thetaCoord (o + t) z) ^ D.paddedNorm := by
            simp [term, oneZero, κ, μ, hr_eq, thetaProduct]
      _ ≤ top * (best * top * top ^ k) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^
        D.paddedNorm := by
        grw [h_pair, ho (D.paddedNorm • o - s - t), ho (-t), h_le]
      _ = _ := by ring
  -- Compare `h_bound` with the goal: with `e = v (exp (B(z, z) / 2))`, the product for `μ` has
  -- valuation `φ z * e ^ r`, and the constant factor has valuation `top ^ r`.
  have h_φ : φ z * v (exp (x.automorphyForm z z / 2)) ^ D.paddedNorm = v
    (x.thetaProduct oneZero μ 0 z) := by
    simp only [φ, Pi.mul_apply, sizeAt_pow, Pi.pow_apply]
    simp [sizeAt, thetaProduct, oneZero, κ, μ, hr_eq, thetaShift_apply, exp_neg, field, pow_add,
      mul_pow]
  have h_const :
      v ((Fintype.card D.dualTorsion : ℂ) * x.thetaProduct oneZero (const κ o) 0 0) = top ^
        D.paddedNorm := by
    simp [thetaProduct, oneZero, κ, hv, hr_eq, top]
  have h_e_pos : 0 < v (exp (x.automorphyForm z z / 2)) := by simp [Valuation.pos_iff, exp_ne_zero]
  have h_top_pos : 0 < top := by simpa [top, Valuation.pos_iff] using h_top
  refine le_of_mul_le_mul_left ?_ (mul_pos (pow_pos h_top_pos (k + 2))
    (pow_pos h_e_pos D.paddedNorm))
  calc top ^ (k + 2) * v (exp (x.automorphyForm z z / 2)) ^ D.paddedNorm * (top * φ z)
      = v ((Fintype.card D.dualTorsion : ℂ) * x.thetaProduct oneZero (const κ o) 0 0 *
          x.thetaProduct oneZero μ 0 z) := by
        rw [map_mul, h_const, ← h_φ, hr_eq]
        ring
    _ ≤ best * top ^ (k + 2) * (v (exp (x.automorphyForm z z / 2)) * ρ) ^ D.paddedNorm := h_bound
    _ = top ^ (k + 2) * v (exp (x.automorphyForm z z / 2)) ^ D.paddedNorm *
      (best * ρ ^ D.paddedNorm) := by ring

/-- Under good reduction at `v` (`h_good`, see `New.ThetaTori.HasGoodReduction`) and
`v |T| = 1` (`hv`), for every `s` in `T = D.dualTorsion` there is `u` such that each of the theta
constants `θ_u(0)`, `θ_{-u}(0)`, `θ_{s-u}(0)` has the largest valuation among all `θ_t(0)`. So `s`
is both a sum `u + (s - u)` and a difference `(s - u) - (-u)` of such indices. -/
lemma exists_forall_valuation_thetaCoord_zero_le (h_good : HasGoodReduction x.automorphyForm
  x.multiplier v D.paddedNorm) (hv : v (Nat.card D.dualTorsion) = 1)
    (s : D.dualTorsion) :
    ∃ u : D.dualTorsion, ∀ i ∈ [u, -u, s - u], ∀ t : D.dualTorsion,
      v (x.thetaCoord t 0) ≤ v (x.thetaCoord i 0) := by
  -- Let `top` be the largest of the `v (θ_t 0)`, taken at `o`, and `best` the largest of the minima
  -- of `v (θ_{s - t} 0)` and `v (θ_{-t} 0)`, taken at `u`. Riemann's relation for
  -- `θ_{r o - s} θ_s θ_0 ^ (r - 2)` and `θ_o ^ r`, with the multiplicative norm, gives
  -- `top ≤ best`. Here `r = D.paddedNorm`.
  cases nonempty_fintype D.dualTorsion
  obtain ⟨k, hr_eq⟩ : ∃ k : ℕ, D.paddedNorm = 2 + k + 1 :=
    Nat.exists_eq_add_of_lt D.three_le_paddedNorm
  obtain ⟨o, ho⟩ := exists_max fun t : D.dualTorsion ↦ v (x.thetaCoord t 0)
  obtain ⟨u, hu⟩ := exists_max fun t : D.dualTorsion ↦
    v (x.thetaCoord (s - t) 0) ⊓ v (x.thetaCoord (-t) 0)
  set top : ℝ≥0 := v (x.thetaCoord o 0)
  set best : ℝ≥0 := v (x.thetaCoord (s - u) 0) ⊓ v (x.thetaCoord (-u) 0)
  suffices h_best : top ≤ best from ⟨u, x.valuation_thetaCoord_le_of_le_inf ho h_best⟩
  -- All `x.thetaCoord t` have the same norm `ρ > 0`, and they do not all vanish at `0`.
  set ρ : ℝ≥0 := x.automorphyForm.thetaNorm v (x.thetaCoord 0)
  have hρ : 0 < ρ := h_good.thetaNorm_pos (x.thetaCoord_mem_thetaSpace 0) (x.thetaCoord_ne_zero 0)
  have h_top : x.thetaCoord o 0 ≠ 0 := fun h_zero ↦ x.thetaCoord_vector_ne_zero 0 <|
    funext fun t ↦ by simpa [top, h_zero] using ho t
  have h_size_mem (t : D.dualTorsion) : x.automorphyForm.sizeAt v (x.thetaCoord t) ∈
    x.automorphyForm.sizes v :=
    .of_mem_thetaSpace h_good.toIsAmpleType (x.thetaCoord_mem_thetaSpace t)
  have h_le (t : D.dualTorsion) (z : torsionPoints x.periodLattice) :
      v (x.thetaCoord t z) ≤ v (exp (x.automorphyForm z z / 2)) * ρ := by
    simpa [sizeAt, field, thetaNorm_thetaCoord, thetaShift_apply, exp_neg, Valuation.pos_iff] using
      le_iSup_of_mem_sizes (h_size_mem t) z
  -- The norm is multiplicative, so the size `φ` of the product has norm `ρ ^ r`.
  set φ := x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
    (x.thetaCoord (D.paddedNorm • o - s)) *
    ((k + 1) • x.automorphyForm).sizeAt v (x.thetaCoord 0 ^ (k + 1))
  have h_sz_mul : x.automorphyForm.sizeAt v (x.thetaCoord s) * x.automorphyForm.sizeAt v
    (x.thetaCoord (D.paddedNorm • o - s)) ∈
      (x.automorphyForm + x.automorphyForm).sizes v := by
    simpa [Pi.mul_def] using mul_shift_mem_sizes (h_size_mem s) (h_size_mem (D.paddedNorm • o - s))
      0
  have h_norm : iSup φ = ρ ^ D.paddedNorm := by
    rw [h_good.hasMultiplicativeNorm h_sz_mul
        (.of_mem_thetaSpace (h_good.nsmul k.succ_ne_zero) (pow (x.thetaCoord_mem_thetaSpace 0) _)),
      h_good.hasMultiplicativeNorm (h_size_mem _) (h_size_mem _)]
    grind [thetaNorm_pow, thetaNorm_thetaCoord]
  -- It suffices to bound the values of `φ`: take the supremum and cancel `ρ ^ r`.
  suffices h_value : ∀ z : torsionPoints x.periodLattice, top * φ z ≤ best * ρ ^ D.paddedNorm by
    have h_sup : top * ρ ^ D.paddedNorm ≤ best * ρ ^ D.paddedNorm := by
      simpa [h_norm] using mul_iSup_le h_value
    exact le_of_mul_le_mul_right h_sup (pow_pos hρ D.paddedNorm)
  exact x.mul_sizeAt_le_inf_mul_thetaNorm_pow hr_eq (by simpa using hv) ho hu h_top h_le

/-- Along a surjective ring map `φ : A →+* B`, every form of degree `d` over `B` is the image of a
form of degree `d` over `A`: mapping coefficients by `φ` is surjective on homogeneous
polynomials of degree `d`. -/
lemma surjective_map_homogeneous {σ A B : Type} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : Surjective φ) (d : ℕ) :
    Surjective fun f : homogeneousSubmodule σ A d ↦
      (⟨f.val.map φ, f.property.map φ⟩ : homogeneousSubmodule σ B d) := by
  rintro ⟨g, hg⟩
  -- Lift `g` coefficient by coefficient along a right inverse of `φ`.
  let f : MvPolynomial σ A := ∑ m ∈ g.support, monomial m (surjInv hφ (g.coeff m))
  have hf_hom : f ∈ homogeneousSubmodule σ A d :=
    sum_mem fun m hm ↦ isHomogeneous_monomial _ (hg.degree_eq_sum_deg_support hm).symm
  exact ⟨⟨f, hf_hom⟩, Subtype.ext (by simp [f, surjInv_eq])⟩

/-- A form `f` of degree `r ^ j` in the theta coordinates is small at the chart `c` if the theta
function `f(θ)` has norm (`New.ThetaTori.LatticeForm.thetaNorm` at `v` for `r ^ j • B`) below
`‖θ_c‖ ^ (r ^ j)`, the norm of `θ_c ^ (r ^ j)`. Here `r = D.paddedNorm` and
`B = x.automorphyForm`. -/
private def IsSmallForm (c : D.dualTorsion) (j : ℕ)
    (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) : Prop :=
  (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v
    (aeval x.thetaCoord (f : MvPolynomial D.dualTorsion v.valuationSubring)) <
    x.automorphyForm.thetaNorm v (x.thetaCoord c) ^ D.paddedNorm ^ j

/-- Under good reduction, the forms of degree `r ^ j` in the theta coordinates with integral
coefficients give exactly the norm ball of `θ_c ^ (r ^ j)`: the theta functions of `r ^ j • B` with
norm at most that of `θ_c ^ (r ^ j)` (`h_good.pow j` is good reduction for `r ^ j • B`). Here
`r = D.paddedNorm` and `B = x.automorphyForm`. -/
private lemma range_aeval_thetaCoord_eq_normBall
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    (c : D.dualTorsion) (j : ℕ) :
    ((aeval x.thetaCoord).toLinearMap.domRestrict
      (homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j))).range =
      HasGoodReduction.normBall (D.paddedNorm ^ j • x.automorphyForm)
        (x.multiplier ^ D.paddedNorm ^ j) v
        (x.thetaCoord c ^ D.paddedNorm ^ j) := by
  rw [LinearMap.range_domRestrict, map_homogeneousSubmodule_eq_formSpan,
    x.formSpan_eq_normBall v h_good]

/-- Smallness is read off from reductions at points that represent the dual lattice. Let `x` have
good reduction at `v` (`h_good`) and let `φ` map the valuation ring of `v` onto a field `k`. Let the
points `a b` represent the dual lattice of `r ^ j • B` modulo `x.periodLattice` (`ha`), and let
`p b` be integral coordinates of the theta vector at `a b` (`hp`). Then a form `f` of degree
`r ^ j` is small at `c` iff its reduction by `φ` vanishes at every point `φ ∘ p b`. Here
`r = D.paddedNorm` and `B = x.automorphyForm`. -/
private lemma isSmallForm_iff_forall_eval_map_eq_zero [Field k] {φ : v.valuationSubring →+* k}
    (hφ : Surjective φ) (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    (c : D.dualTorsion) (j : ℕ) {I : Type} {a : I → V} {p : I → D.dualTorsion → v.valuationSubring}
    (ha : ∀ u : (D.paddedNorm ^ j • x.automorphyForm).dualLattice, ∃ b : I,
      a b - u ∈ x.periodLattice)
    (hp : ∀ b : I, IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s (a b)) (p b))
    (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) :
    x.IsSmallForm c j f ↔ ∀ b : I, (f.val.map φ).eval (φ ∘ p b) = 0 := by
  let ev : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)
    →ₗ[v.valuationSubring] V → ℂ :=
    (aeval x.thetaCoord).toLinearMap.domRestrict
      (homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j))
  have h_max (y : v.valuationSubring) : φ y = 0 ↔ v y < 1 := by
    simp [← v.mem_maximalIdeal_iff, ← IsLocalRing.ker_eq_maximalIdeal φ hφ]
  -- By homogeneity the values of the forms at `p b` are integral coordinates of their values at
  -- `a b`; the power of a unit coordinate is a unit.
  have h_aff (b : I) : IsIntegralCoords (fun g ↦ ev g (a b)) fun g ↦ g.val.eval (p b) := by
    obtain ⟨s, hs_eq, i, hi_unit⟩ : ∃ s : ℂ,
      (∀ t : D.dualTorsion, (p b t : ℂ) = x.thetaCoord t (a b) / s) ∧
        ∃ i : D.dualTorsion, v (p b i) = 1 := hp b
    refine ⟨s ^ D.paddedNorm ^ j, fun g ↦ ?_, ⟨_, isHomogeneous_X_pow i _⟩, by simp [hi_unit]⟩
    simpa [ev, eval_eq, aeval_def, eval₂_eq, hs_eq, div_eq_inv_mul] using
      g.property.eval₂_const_mul (algebraMap ..) _ s⁻¹
  have h_ball : ev.range =
      HasGoodReduction.normBall (D.paddedNorm ^ j • x.automorphyForm)
        (x.multiplier ^ D.paddedNorm ^ j) v
        (x.thetaCoord c ^ D.paddedNorm ^ j) :=
    x.range_aeval_thetaCoord_eq_normBall h_good c j
  change (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v (ev f) < x.automorphyForm.thetaNorm v
    (x.thetaCoord c) ^ D.paddedNorm ^ j ↔ _
  simpa [thetaNorm_pow, ← h_max, map_eval] using
    (h_good.pow j).thetaNorm_lt_iff_coords (pow (x.thetaCoord_mem_thetaSpace c) _)
      (pow_ne_zero _ (x.thetaCoord_ne_zero c)) h_ball ha h_aff f

/-- Smallness is read off at the points of the chart `c`. Under good reduction (`h_good`), with
`φ` onto a field and `q z` integral coordinates of the theta vector at every `z ∈ V` (`hq`), a
form `f` of degree `r ^ j` is small at `c` iff its reduction vanishes at each point `φ ∘ q z`
whose coordinate `c` is nonzero. Here `r = D.paddedNorm`. -/
private lemma isSmallForm_iff_forall_eval_map_eq_zero_of_ne_zero [Field k]
    {φ : v.valuationSubring →+* k} (hφ : Surjective φ)
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    {q : V → D.dualTorsion → v.valuationSubring}
    (hq : ∀ z : V, IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s z) (q z))
      (c : D.dualTorsion) (j : ℕ)
    (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) :
    x.IsSmallForm c j f ↔ ∀ z : V, φ (q z c) ≠ 0 → (f.val.map φ).eval (φ ∘ q z) = 0 := by
  -- Multiplying `f` by `X c ^ e` to reach degree `r ^ (j + 1)` multiplies norm and radius by the
  -- same factor. In that degree all points of `V` may be used, and `X c ^ e` vanishes exactly
  -- where the coordinate `c` does.
  obtain ⟨e, he_pos, h_deg⟩ : ∃ e > 0, D.paddedNorm ^ (j + 1) = D.paddedNorm ^ j + e :=
    lt_iff_exists_add.mp (Nat.pow_lt_pow_succ (n := j) h_good.one_lt)
  have hρ : 0 < x.automorphyForm.thetaNorm v (x.thetaCoord c) :=
    h_good.thetaNorm_pos (x.thetaCoord_mem_thetaSpace c) (x.thetaCoord_ne_zero c)
  have h_hom : IsHomogeneous (f.val * X c ^ e) (D.paddedNorm ^ (j + 1)) := by
    simpa [h_deg] using f.property.mul (isHomogeneous_X_pow c e)
  let f' : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ (j + 1)) :=
    ⟨f.val * X c ^ e, h_hom⟩
  have h_mul : (D.paddedNorm ^ (j + 1) • x.automorphyForm).thetaNorm v
    (aeval x.thetaCoord (f.val * X c ^ e)) =
      (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v (aeval x.thetaCoord f.val) *
        x.automorphyForm.thetaNorm v (x.thetaCoord c) ^ e := by
    have h_mem_ball : aeval x.thetaCoord f.val ∈
        HasGoodReduction.normBall (D.paddedNorm ^ j • x.automorphyForm)
            (x.multiplier ^ D.paddedNorm ^ j) v
        (x.thetaCoord c ^ D.paddedNorm ^ j) :=
      (x.range_aeval_thetaCoord_eq_normBall h_good c j).le ⟨f, rfl⟩
    rw [map_mul, map_pow, aeval_X, h_deg, add_smul, ← thetaNorm_pow, LatticeForm.thetaNorm,
      sizeAt_mul]
    exact h_good.hasMultiplicativeNorm
      (.of_mem_thetaSpace (h_good.pow j).toIsAmpleType (Submodule.mem_inf.mp h_mem_ball).left)
      (.of_mem_thetaSpace (h_good.nsmul he_pos.ne') (pow (x.thetaCoord_mem_thetaSpace c) e))
  have h_small : x.IsSmallForm c (j + 1) f' ↔ x.IsSmallForm c j f := by
    simp_rw [IsSmallForm, f', h_mul, h_deg, pow_add, mul_lt_mul_iff_left₀ (pow_pos hρ e)]
  rw [← h_small, x.isSmallForm_iff_forall_eval_map_eq_zero hφ h_good c (j + 1)
    (fun u ↦ ⟨(u : V), by simp⟩) hq f']
  simp [f', he_pos.ne', or_iff_not_imp_right]

/-- Under good reduction at `v` (`h_good`), with `φ` onto a field `k`, `q z` integral coordinates of
the theta vector `(θ_s(z))_s` at every `z ∈ V` and `p l` those at the lift of each level point `l`:
if each `N l` has the coordinates `φ ∘ p l` at `t`, then `N` cuts out at `t` the reduced vectors
`φ ∘ q z` (`New.Variety.ThetaNull.IsCutOutAt`). That is: in all charts of the `N l` at `t` and each
chart `c`, the ideal of those vectors with `c`-coordinate ≠ 0, scaled to 1, satisfies
`IsCutOut D.paddedNorm D.exponentBound` with ranks `thetaRanks D.dualTorsion D.paddedNorm` (the
dimensions of the theta spaces of `r ^ j • x.automorphyForm`; for `j ≤ D.exponentBound` the level
points `D.levelTorsion` represent its dual lattice mod `x.periodLattice`) for the affine coordinates
of the `N l` at `t`. Here `r = D.paddedNorm`. -/
lemma isCutOutAt_reduction [Field k] {φ : v.valuationSubring →+* k} (hφ : Surjective φ)
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    {q : V → D.dualTorsion → v.valuationSubring}
      {p : D.levelTorsion → D.dualTorsion → v.valuationSubring}
    (hq_coords : ∀ z : V, IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s z) (q z))
    (hp_coords : ∀ l : D.levelTorsion,
      IsIntegralCoords (fun s : D.dualTorsion ↦ x.thetaCoord s (x.torsionLift l)) (p l))
    {S : AlgebraicGeometry.Scheme} {t : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ S}
    {N : D.levelTorsion → LineBundle S D.dualTorsion}
    (hN_coords : ∀ l : ↥D.levelTorsion, (N l).IsHomogeneousCoords t fun s : D.dualTorsion ↦
      φ (p l s)) :
    IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm) N t
      (Set.range fun z : V ↦ φ ∘ q z) := by
  -- In the chart `c` the forms of degree `r ^ j` vanishing at the reduced points are the small
  -- ones, so the ranks are those of the reduced norm balls and may be read at the level points.
  intro chart h_chart c
  have h_dual (j : ℕ) :
      (D.paddedNorm ^ j • x.automorphyForm).dualLattice = x.latticeOver
        (D.dualTorsion.comap (nsmulAddMonoidHom (D.paddedNorm ^ j))) := by
    ext u
    rw [mem_dualLattice_nsmul, x.dualLattice_periodLattice,
      x.nsmul_mem_latticeOver (pow_ne_zero j h_good.one_lt.ne_bot)]
  -- `J` is the ideal of the reduced points in the chart `c`.
  let J : Ideal (MvPolynomial D.dualTorsion k) :=
    ⨅ pt ∈ {pt ∈ Set.range (fun z : V ↦ φ ∘ q z) | pt c ≠ 0},
      RingHom.ker (MvPolynomial.eval fun s : D.dualTorsion ↦ pt s / pt c)
  have h_ideal (j : ℕ) (f : homogeneousSubmodule D.dualTorsion v.valuationSubring
    (D.paddedNorm ^ j)) :
      f.val.map φ ∈ J ↔ x.IsSmallForm c j f := by
    simp +contextual [J, x.isSmallForm_iff_forall_eval_map_eq_zero_of_ne_zero hφ h_good hq_coords,
      f.property.eval₂_const_mul, div_eq_inv_mul]
  have h_lift (d : ℕ) : Surjective fun f : homogeneousSubmodule D.dualTorsion v.valuationSubring d ↦
      (⟨f.val.map φ, f.property.map φ⟩ : homogeneousSubmodule D.dualTorsion k d) :=
    surjective_map_homogeneous hφ d
  refine ⟨by simp +contextual, fun j ↦ ?_, fun j hj ↦ ?_⟩
  · -- The rank is the dimension of the theta space, whose square is an index of lattices.
    let red : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j) →ₛₗ[φ]
      MvPolynomial D.dualTorsion k ⧸ J :=
      { toFun f := Ideal.Quotient.mk J (f.val.map φ)
        map_add' := by simp
        map_smul' c f := by
          have h_alg :
              algebraMap k (MvPolynomial D.dualTorsion k ⧸ J) (φ c) = Ideal.Quotient.mk J
                (C (φ c)) := rfl
          simp [Algebra.smul_def, h_alg] }
    have h_range : imageMod J (homogeneousSubmodule D.dualTorsion k (D.paddedNorm ^ j)) = span k
      (Set.range red) := by
      rw [← (imageMod ..).span_eq, map_coe, Set.image_eq_range, ← (h_lift _).range_comp]
      rfl
    have h_zero (f : homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j)) :
        red f = 0 ↔ (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v (aeval x.thetaCoord f.val) <
          (D.paddedNorm ^ j • x.automorphyForm).thetaNorm v
            (x.thetaCoord c ^ D.paddedNorm ^ j) := by
      rw [thetaNorm_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.trans (h_ideal j f)
    -- The rank is the dimension of the theta space of degree `r ^ j` ...
    have h_ball : ((aeval x.thetaCoord).toLinearMap.domRestrict
          (homogeneousSubmodule D.dualTorsion v.valuationSubring (D.paddedNorm ^ j))).range =
        HasGoodReduction.normBall (D.paddedNorm ^ j • x.automorphyForm)
            (x.multiplier ^ D.paddedNorm ^ j) v
        (x.thetaCoord c ^ D.paddedNorm ^ j) :=
      x.range_aeval_thetaCoord_eq_normBall h_good c j
    change finrank k (imageMod J (homogeneousSubmodule D.dualTorsion k (D.paddedNorm ^ j))) =
      thetaRanks D.dualTorsion D.paddedNorm j
    rw [h_range, (h_good.pow j).finrank_reduction_eq (pow (x.thetaCoord_mem_thetaSpace c) _)
      (pow_ne_zero _ (x.thetaCoord_ne_zero c)) h_ball hφ h_zero]
    -- ... whose square is the index of `x.periodLattice` in the dual lattice.
    rw [← Nat.sqrt_eq' (finrank ..),
      (h_good.pow j).finrank_thetaSpace_sq (hp := (h_good.pow j).isPosRiemann), h_dual,
      x.relIndex_latticeOver]
    simp [thetaRanks]
  · -- For `j ≤ D.exponentBound` the level points represent the dual lattice in degree `r ^ j`
    -- modulo `x.periodLattice`: its classes are killed by the level (`D.mem_torsionBy_level`).
    have h_repr : ∀ u : (D.paddedNorm ^ j • x.automorphyForm).dualLattice, ∃ l : D.levelTorsion,
        x.torsionLift l - u ∈ x.periodLattice := by
      rw [h_dual]
      rintro ⟨_, y, hy_class, rfl⟩
      use ⟨_, D.mem_torsionBy_level _ hj _ hy_class⟩
      simp [torsionLift, sub_mem_periodLattice_iff]
    intro f₀ hf₀
    -- `f₀` is the reduction of a form `f` over the valuation ring.
    obtain ⟨f, hf⟩ := h_lift (D.paddedNorm ^ j) ⟨f₀, hf₀⟩
    obtain rfl : f.val.map φ = f₀ := congrArg Subtype.val hf
    refine (h_ideal j f).trans
      ((x.isSmallForm_iff_forall_eval_map_eq_zero hφ h_good c j h_repr hp_coords f).trans ?_)
    -- The coordinates at `t` are those of `φ ∘ p b` divided by a nonzero one, the coordinate of the
    -- chart `chart b`.
    have h_unit (b : D.levelTorsion) : φ (p b (chart b)) ≠ 0 :=
      ((hN_coords b (chart b)).left.mp (h_chart b)).ne_zero
    simp [hN_coords _ _, h_unit, f.property.eval₂_const_mul, comp_def, mul_comm (φ _)]

/-- The family of coefficient pairs in `𝓞 E` consisting of `(1, 0)` twice (on the first copy of
`Bool`), `(c, 1)` and `(1, −c̄)` (at `true` and `false` of the second copy), and `(a l, 0)` for
every `l : K`. -/
def _root_.New.paddingTuple (c : 𝓞 E) : Bool ⊕ Bool ⊕ K → 𝓞 E × 𝓞 E :=
  Sum.elim (fun _ : Bool ↦ (1, 0)) (Sum.elim (fun b ↦ cond b (c, 1) (1, -star c)) fun l ↦ (a l, 0))

end New.ThetaTori.ThetaTorus

end
end
end

section
/-!
# Linear systems and theta families from dense complex points carrying theta tori

This file builds objects from their values at a dense family of complex points. A linear system is a
line bundle whose transition functions are the ratios `s j / s i`, that is, a map to projective
space. `New.Variety.ThetaNull.exists_isLinearSystem` extends coordinates given at a dense family `ξ`
of complex points of a reduced scheme (`New.IsSeparatingFamily`) to a linear system. It needs a
linear system `M` with homogeneous coordinates `m a` at each `ξ a`. It also needs each of `w`, `m`
to be locally a regular function times sums of the other. The result has the Picard class of `M`.
The second part builds a family of theta-embedded abelian schemes `New.ThetaFamily D` over a base
`S` from complex points `η k` of `S` that carry theta tori `x k`. The scheme `A` is the closure of
the theta points. The group law, the action and all identities extend from these points by density,
using Riemann's relation for theta functions.

## Main definitions and results

* `New.exists_isAbelianScheme`: group and module axioms pass from dense families of vector spaces to
  `A`.
* `New.Variety.exists_maps_of_riemann_relation`: the extension step along Riemann's relation.
* `New.Variety.exists_add_and_intAction`: the addition and the action of `𝓞 E` extend to `A`.
* `New.Variety.exists_isThetaStructure`: the theta law on base changes to local rings.
* `New.Variety.exists_thetaFamily_of_points`: the family exists, modelled on `x i` at each `η i`.
  The remaining lemmas of the second part are steps of its proof.

Notions from other files:
* `New.LineBundle.IsHomogeneousCoords`: a vector `v` gives homogeneous coordinates of a point `t`
  for a line bundle: `v j` is a unit exactly when `t` lands in chart `j`, and there the transitions
  from chart `j` are the ratios `v k / v j`.
* `New.LineBundle.IsLinearSystem`: a line bundle whose transitions are regular on their charts,
  vanish off them, and are homogeneous coordinates of every point of the chart.
* `New.PointFn.IsRegularOn`: a function `f` is regular on an open `U`: at points `t : Spec A → X`
  that land in `U`, its value commutes with all ring maps `φ : A → B`.
* `New.Variety.AllSpecializeTo S Q`: every point of `S` specialises to the image of a point over an
  algebraically closed field with the property `Q`.
* `New.ThetaTori.ThetaTorus.IsRiemannTuple`: coefficient tuples for Riemann's relation.

## Relation to the literature

Known; see `Lib.Shimura.ThetaModuli.UniversalFamily` for sources.
-/

@[expose] public section

/-! ## Linear systems from coordinates at dense points -/

section LinearSystemExtension

open AlgebraicGeometry New PointFn LineBundle Finset CategoryTheory

/-- The family `w` is a local combination of the family `m`: for every index `j` and every point
`s` of `Z` there are an open `U` containing `s`, indices `e : Q → J` and a function `c` regular
on `U` such that `w a j = c (ξ a) * ∑ q, m a (e q)` at every complex point `ξ a` that lands in `U`.
Here `w a` and `m a` are vectors of complex coordinates attached to the point `ξ a`. -/
def New.Variety.ThetaNull.IsLocalCombination {Z : Scheme} {J X : Type} (Q : Type*) [Fintype Q]
    (ξ : X → (Spec (CommRingCat.of ℂ) ⟶ Z)) (w m : X → J → ℂ) : Prop :=
  ∀ (j : J) (s : Z), ∃ U : Z.Opens, s ∈ U ∧ ∃ (e : Q → J) (c : PointFn Z), IsRegularOn c U ∧
    ∀ a : X, LandsIn (ξ a) U → c (CommRingCat.of ℂ) (ξ a) * ∑ q : Q, m a (e q) = w a j

/-- Let the points `ξ a` separate `Z`, with homogeneous coordinates `m a` for the linear system
`M`. If each of the families `w` and `m` is a local combination of the other, then the `w a` are
homogeneous coordinates of the `ξ a` for a linear system `N` in the class of `M`. -/
lemma New.Variety.ThetaNull.exists_isLinearSystem {Z : Scheme} {J X : Type} {Q : Type*}
    [Fintype J] [Fintype Q] {M : LineBundle Z J} {ξ : X → (Spec (CommRingCat.of ℂ) ⟶ Z)}
    {m w : X → J → ℂ} (hξ : IsSeparatingFamily ξ) (hM : M.IsLinearSystem)
    (hm : ∀ a : X, M.IsHomogeneousCoords (ξ a) (m a))
    (h_wm : IsLocalCombination Q ξ w m) (h_mw : IsLocalCombination Q ξ m w) :
    ∃ N : LineBundle Z J,
      N.IsLinearSystem ∧ (∀ a : X, N.IsHomogeneousCoords (ξ a) (w a)) ∧
        N.picClass = M.picClass := by
  -- Each `w · j` defines a section `σ j` of `M` on a finer cover. By `h_mw` these sections have
  -- no common zero, so they are the coordinates of a map `f` to projective space, and the
  -- pull-back of the hyperplane bundle along `f` is the required linear system.
  choose U hU e c hc h_sum using h_wm
  have h_cover (j : J) : ⨆ s : Z, U j s = ⊤ := top_unique fun s _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hU j s⟩
  -- `L` is `M` on the cover by the sets `M.opens k ⊓ ⨅ j, U j (s j)`.
  let L : LineBundle Z (J × (J → Z)) := M.mul (pi (fun j : J ↦ mk (U j) 1 (h_cover j)) ∅)
  have L_opens {A : CommRingCat} {t : Spec A ⟶ Z} (k : J × (J → Z)) :
      LandsIn t (L.opens k) ↔ LandsIn t (M.opens k.fst) ∧ ∀ j : J, LandsIn t (U j (k.snd j)) := by
    simp [L, landsIn_iInf]
  have L_transition (i k : J × (J → Z)) : L.transition i k = M.transition i.fst k.fst := by
    simp [L, LineBundle.mul]
  let σ (j : J) (k : J × (J → Z)) : PointFn Z :=
    c j (k.snd j) * ∑ q : Q, M.transition k.fst (e j (k.snd j) q)
  have σ_reg (j : J) (k : J × (J → Z)) : (σ j k).IsRegularOn (L.opens k) := by
    intro A B φ t ht
    obtain ⟨ht_M, ht_U⟩ := (L_opens k).mp ht
    have h_trans (l : J) :
        M.transition k.fst l B (Spec.map φ ≫ t) = φ (M.transition k.fst l A t) :=
      hM.isRegularOn_transition k.fst l φ t ht_M
    simp [σ, h_trans, hc j (k.snd j) φ t (ht_U j)]
  -- In the chart `k` the coordinate `m a k.fst` is nonzero and the transitions are ratios.
  have m_ne (k : J × (J → Z)) (a : X) (ha : LandsIn (ξ a) (L.opens k)) : m a k.fst ≠ 0 :=
    (((hm a).landsIn_iff_isUnit k.fst).mp ((L_opens k).mp ha).left).ne_zero
  have M_transition (k : J × (J → Z)) (l : J) (a : X) (ha : LandsIn (ξ a) (L.opens k)) :
      M.transition k.fst l (CommRingCat.of ℂ) (ξ a) = m a l / m a k.fst := by
    simpa [div_eq_mul_inv] using (hm a).transition_eq_mul_inverse (m_ne k a ha).isUnit l
  have σ_val (j : J) (k : J × (J → Z)) (a : X) (ha : LandsIn (ξ a) (L.opens k)) :
      σ j k (CommRingCat.of ℂ) (ξ a) = w a j / m a k.fst := by
    obtain ⟨-, ha_U⟩ := (L_opens k).mp ha
    simp [σ, M_transition k _ a ha, ← sum_div, ← mul_div_assoc, ← h_sum j _ a (ha_U j)]
  -- The local expressions `σ j k` are compatible because they are so at the points `ξ a`.
  have σ_section (j : J) : L.IsSection (σ j) := by
    refine ⟨σ_reg j, fun i k A t hi hk ↦ ?_⟩
    have h_agree (a : X) (ha : LandsIn (ξ a) (L.opens i ⊓ L.opens k)) :
        σ j i (CommRingCat.of ℂ) (ξ a) =
          (L.transition i k * σ j k) (CommRingCat.of ℂ) (ξ a) := by
      obtain ⟨ha_i, ha_k⟩ := landsIn_inf.mp ha
      simp [L_transition, M_transition, σ_val, m_ne, ha_i, ha_k, field]
    exact hξ.pointFn_ext ((σ_reg j i).mono inf_le_left)
      (((L.regular i k).mul (σ_reg j k)).mono (by simp)) h_agree A t (landsIn_inf.mpr ⟨hi, hk⟩)
  -- No common zero: near a point of `L.opens k`, the function `1` is a combination of the `σ j k`.
  have σ_ne (k : J × (J → Z)) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Z)
      (ht : LandsIn t (L.opens k)) : ∃ j : J, σ j k (CommRingCat.of K) t ≠ 0 := by
    obtain ⟨V, hV, e', c', hc', h_sum'⟩ := h_mw k.fst (t (IsLocalRing.closedPoint K))
    have h_reg : (c' * ∑ q : Q, σ (e' q) k).IsRegularOn (L.opens k ⊓ V) := by
      intro A B φ u hu
      obtain ⟨hu_L, hu_V⟩ := landsIn_inf.mp hu
      simp [hc' φ u hu_V, σ_reg _ k φ u hu_L]
    -- At `ξ a` the combination is `(c' * ∑ q, w a (e' q)) / m a k.fst`, and `h_sum'` says that the
    -- numerator is `m a k.fst`.
    have h_agree (a : X) (ha : LandsIn (ξ a) (L.opens k ⊓ V)) :
        (c' * ∑ q : Q, σ (e' q) k) (CommRingCat.of ℂ) (ξ a) = 1 := by
      obtain ⟨ha_L, ha_V⟩ := landsIn_inf.mp ha
      simpa [σ_val, ← sum_div, ← mul_div_assoc, m_ne, ha_L, div_eq_one_iff_eq] using h_sum' a ha_V
    have h_one : (c' * ∑ q : Q, σ (e' q) k) (CommRingCat.of K) t = 1 :=
      hξ.pointFn_ext (g := 1) h_reg (by simp [IsRegularOn]) h_agree _ t
        (landsIn_inf.mpr ⟨ht, landsIn_iff_mem.mpr hV⟩)
    by_contra! h_zero
    simp [h_zero] at h_one
  obtain ⟨f, h_class, h_coords⟩ :
      ∃ f : Z ⟶ ProjSpace J, L.picClass = ((ProjSpace.hyperplaneBundle J).pull f).picClass ∧
        ∀ (k : J × (J → Z)) (A : CommRingCat) (t : Spec A ⟶ Z), LandsIn t (L.opens k) →
          ((ProjSpace.hyperplaneBundle J).pull f).IsHomogeneousCoords t fun j : J ↦ σ j k A t :=
    L.exists_picClass_eq_pull_hyperplane (𝟙 Z) σ_section fun k K _ t ↦ σ_ne k K (t ≫ 𝟙 Z)
  refine ⟨_, ProjSpace.isLinearSystem_hyperplaneBundle.pull f, fun a ↦ ?_,
    by simpa [L] using h_class.symm⟩
  -- In a chart `k` containing `ξ a` the vector `w a / m a k.fst` gives coordinates; scale it by
  -- the unit `m a k.fst`.
  obtain ⟨k, hk⟩ := L.exists_landsIn (ξ a)
  have h_div : ((ProjSpace.hyperplaneBundle J).pull f).IsHomogeneousCoords (ξ a)
      fun j : J ↦ w a j / m a k.fst := by simpa only [σ_val _ k a hk] using h_coords k _ _ hk
  have h_scale : w a = m a k.fst • fun j : J ↦ w a j / m a k.fst :=
    funext fun j ↦ (mul_div_cancel₀ (w a j) (m_ne k a hk)).symm
  rw [h_scale]
  exact h_div.smul (m_ne k a hk).isUnit

end LinearSystemExtension

/-!
## Theta families from dense complex points carrying theta tori

Smoothness and the group axioms by density, the level coordinates of a theta torus, padding tuples,
and the extension of the group law and of the theta structure from the points `η i` to `A`.
-/

namespace New

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ThetaObject Obj LineBundle PointFn AddObj Variety ThetaNull Scheme ThetaTori ThetaTorus PeriodMap
  Category Over Spec IsLocalRing

attribute [local instance low] Fintype.ofFinite

variable {V ι κ : Type} [FinComplexSpace V] {S : Scheme} [IsReduced S] [IsLocallyNoetherian S]
  [Finite ι] {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)}

omit [Finite ι] in
/-- Homogeneous coordinates for a product of line bundles: if for each factor `l : K` the values
`θ k (w l)`, `k : ι`, are homogeneous coordinates of `t` for `M l`, then the products
`∏ l, θ (μ l) (w l)`, indexed by `μ : K → ι`, are homogeneous coordinates of `t` for the product
bundle `LineBundle.pi M`. Here `V` is any type. -/
lemma LineBundle.IsHomogeneousCoords.pi {K : Type} {X : Scheme} {t : Spec (CommRingCat.of ℂ) ⟶ X}
    {V : Sort*} [Fintype K] {M : K → LineBundle X ι} {θ : ι → V → ℂ} {w : K → V}
    (h : ∀ l : K, (M l).IsHomogeneousCoords t fun k : ι ↦ θ k (w l)) :
    (LineBundle.pi M).IsHomogeneousCoords t fun μ : K → ι ↦ ∏ l : K, θ (μ l) (w l) := by
  simp_all [IsHomogeneousCoords, landsIn_iInf, Finset.prod_ne_zero_iff, Finset.prod_mul_distrib]

open HasRingHomProperty MorphismProperty Hom in
omit [IsReduced S] in
/-- A flat proper commutative group scheme A over a locally noetherian S is smooth if every point of
S specialises to the image of a point over an algebraically closed field along which the fibre of A
is reduced. -/
lemma smooth_of_allSpecializeTo_isReduced {A : Over S} [AddObj A] [Flat A.hom] [IsProper A.hom]
    (h_reduced : AllSpecializeTo S fun t ↦ AlgebraicGeometry.IsReduced (Limits.pullback A.hom t)) :
    Smooth A.hom := by
  -- The smooth locus is open, so it suffices that every y specialises to a point x in it.
  let π : A.left ⟶ S := A.hom
  refine smoothLocus_eq_top_iff.mp (top_unique fun y _ ↦ ?_)
  obtain ⟨k, _, _, t, h_spec : π y ⤳ t (closedPoint k), h_red⟩ : ∃ (k : Type) (_ : Field k)
    (_ : IsAlgClosed k) (t : Spec (CommRingCat.of k) ⟶ S), π y ⤳ t (closedPoint k) ∧
    AlgebraicGeometry.IsReduced (Limits.pullback A.hom t) := h_reduced (π y)
  obtain ⟨x, hyx, hx⟩ : ∃ x : A.left, y ⤳ x ∧ π x = t (closedPoint k) :=
    π.isClosedMap.specializingMap h_spec
  refine hyx.mem_open π.smoothLocus.is_open' ?_
  -- The fibre along t is a reduced group over an algebraically closed field: its smooth locus is
  -- dense, hence non-empty, and translations spread smoothness to the whole group.
  have h_geom : Smooth (pullback.snd π t) := by
    have h_dense : Dense ((pullback.snd π t).smoothLocus : Set ↥(Limits.pullback π t)) :=
      (pullback.snd π t).dense_smoothLocus_of_perfectField
    -- The fibre is non-empty: it contains a point over `x`.
    have h_nonempty : Nonempty (pullback.snd π t).smoothLocus :=
      (h_dense.nonempty_iff.mpr (Pullback.exists_preimage_pullback x _ hx).nonempty).to_subtype
    refine (pullbackAddObj t).property_of_isOpenImmersion _ (Opens.ι _) h_nonempty ?_
    simp [π, ← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq]
  obtain ⟨U, hU, htU⟩ : ∃ V : S.Opens, IsAffineOpen V ∧ LandsIn t V := exists_isAffineOpen_landsIn t
  have hxU : π x ∈ U := by
    simpa only [hx] using landsIn_iff_mem.mp htU
  obtain ⟨W, hW, hxW, hWU⟩ : ∃ W : A.left.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ π ⁻¹ᵁ U :=
    exists_isAffineOpen_mem_and_subset (π.mem_preimage.mpr hxU)
  -- Smoothness descends from k to the residue field of the image of t.
  have h_fibre : Smooth ((hW.fromSpec ≫ π).fiberToSpecResidueField (t (closedPoint k))) := by
    -- `id (closedPoint k)`: in this form the surjectivity instance below is found.
    refine of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (isPullback_fiberToSpecResidueField_of_isPullback
        (.paste_vert (.of_hasPullback ..) (.of_hasPullback _ t)) (id (closedPoint k))).flip ?_ ?_
    · and_intros <;> infer_instance
    · exact of_isPullback (.of_hasPullback ..) (comp_mem _ _ _ inferInstance h_geom)
  -- Fibre criterion: Γ(U) → Γ(W) is flat, finitely presented, and has a smooth fibre through x.
  let : Algebra Γ(S, U) Γ(A.left, W) := (π.appLE U W hWU).hom'.toAlgebra
  have : Module.Flat Γ(S, U) Γ(A.left, W) := π.flat_appLE hU hW hWU
  have : Algebra.FinitePresentation Γ(S, U) Γ(A.left, W) := π.finitePresentation_appLE hU hW hWU
  let 𝔮 : Ideal Γ(A.left, W) := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  let 𝔭 : Ideal Γ(S, U) := 𝔮.under Γ(S, U)
  suffices Algebra.FormallySmooth 𝔭.ResidueField (𝔭.Fiber Γ(A.left, W)) from
    (formallySmooth_stalkMap_iff U hU W hW hWU hxW).mpr (.of_formallySmooth_fiber 𝔭 𝔮)
  -- Restate the fibre through Spec Γ(W) → Spec Γ(U), at the prime under the prime of x.
  have h_point :
      hU.fromSpec (Spec.map (π.appLE U W hWU) (hW.primeIdealOf ⟨x, hxW⟩)) = t (closedPoint k) := by
    -- `primeIdealOf` is a point of the prime spectrum, which is the carrier of `Spec Γ(A.left, W)`
    -- only after unfolding, so `Hom.comp_apply` is used as an equation.
    refine (Hom.comp_apply ..).symm.trans ?_
    rw [hU.SpecMap_appLE_fromSpec _ hW]
    refine (Hom.comp_apply ..).trans ?_
    rw [hW.fromSpec_primeIdealOf, hx]
  rw [← h_point, ← hU.SpecMap_appLE_fromSpec π hW hWU] at h_fibre
  -- The ring-theoretic fibre at that prime is isomorphic to it, so it is smooth.
  have h_alg_smooth : Algebra.Smooth 𝔭.ResidueField (𝔭.Fiber Γ(A.left, W)) :=
    RingHom.smooth_algebraMap.mp (Spec_iff.mp (of_isPullback
      (.paste_horiz (.of_horiz_isIso ⟨(fiberToSpecResidueFieldIso ..).inv.w⟩)
        (isPullback_fiberToSpecResidueField_of_isPullback (.of_horiz_isIso_mono ⟨id_comp _⟩)
          (Spec.map (π.appLE U W hWU) _))) h_fibre))
  exact h_alg_smooth.formallySmooth

/-- Group and module laws by density. Let `V` be a finite-dimensional complex space, `O` a
commutative ring and `S` reduced and locally noetherian with complex points `η i`, the finite
subfamily `η ∘ j` being dense. Let `A` be flat and proper over `S` with a reduced geometric fibre at
a specialisation of every point, and let maps `e i : V → A(η i)` be such that all points `e i z`
separate `A` and, for each `i`, the `e i v` separate the fibre of `A` over `η i`. If the addition,
the zero and the action `F i` of `O` on `V` extend to morphisms `m`, `o` and `f c` of `A`, then `A`
is an abelian scheme with an `O`-module structure, each `e i` is additive, and
`c • e i z = e i (F i c z)`. -/
lemma exists_isAbelianScheme (j : ι → κ) (hη : IsDenseFamily fun i : ι ↦ η (j i)) {O : Type}
    [CommRing O] {A : Over S} {e : ∀ i : κ, V → (Over.mk (η i) ⟶ A)}
    (he_sep : ∀ i : κ, IsSeparatingFamily fun v : V ↦ (lift (e i v) (𝟙 (Over.mk (η i)))).left)
    (h_sep : IsSeparatingFamily fun s : κ × V ↦ (e s.1 s.2).left) [Flat A.hom] [IsProper A.hom]
    (h_reduced : AllSpecializeTo S fun t ↦ IsReduced (pullback A.hom t))
    {f : O → (A ⟶ A)} {F : κ → O →+* V →L[ℂ] V}
    (hf : ∀ (d : O) (i : κ) (z : V), e i z ≫ f d = e i (F i d z))
    (m : A ⊗ A ⟶ A) (o : 𝟙_ (Over S) ⟶ A)
    (hm : ∀ (i : κ) (y z : V), e i (y + z) = lift (e i y) (e i z) ≫ m)
    (ho : ∀ i : κ, toUnit (Over.mk (η i)) ≫ o = e i 0) :
    ∃ (_ : IsAbelianScheme A) (_ : ModuleObj O A) (ε : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)),
      (e = fun (i : κ) (z : V) ↦ ε i z) ∧ ∀ (c : O) (i : κ) (z : V), c • e i z = e i (F i c z) := by
  -- Every axiom is an equality of morphisms out of A, A ⊗ A or A ⊗ A ⊗ A. The points e, their
  -- pairs and their triples separate these schemes, so each axiom reduces to the same law in V.
  -- `IsSeparatingFamily` is the conjunction of reducedness and density.
  have h_red : IsReduced A.left := And.left h_sep
  have h_pairs : IsSeparatingFamily fun z : (κ × V) × V ↦
      (lift (e z.1.1 z.2) (e z.1.1 z.1.2)).left :=
    h_sep.prod (y := fun s : κ × V ↦ e s.1 s.2) (e := fun s : κ × V ↦ e s.1) hη h_red
      fun s : κ × V ↦ (he_sep s.1).right
  have h_flat : Flat (A ⊗ A).hom := Flat.comp (pullback.fst ..) _
  have h_triples : IsSeparatingFamily fun z : ((κ × V) × V) × V ↦
      (lift (e z.1.1.1 z.2) (lift (e z.1.1.1 z.1.2) (e z.1.1.1 z.1.1.2))).left :=
    h_pairs.prod (y := fun s : (κ × V) × V ↦ lift (e s.1.1 s.2) (e s.1.1 s.1.2))
      (e := fun s : (κ × V) × V ↦ e s.1.1) hη h_red fun s : (κ × V) × V ↦ (he_sep s.1.1).right
  have h_left : (λ_ A).inv = lift (toUnit A) (𝟙 A) := by
    apply hom_ext
    · simp only [leftUnitor_inv_fst, lift_fst]
    · simp only [leftUnitor_inv_snd, lift_snd]
  have h_right : (ρ_ A).inv = lift (𝟙 A) (toUnit A) := by
    apply hom_ext
    · simp only [rightUnitor_inv_fst, lift_fst]
    · simp only [rightUnitor_inv_snd, lift_snd]
  let _ : AddGrpObj A :=
    { zero := o
      add := m
      neg := f (-1)
      zero_add := (λ_ A).inv_comp_eq_id.1 (h_sep.hom_ext (by simp [← hm, ho, ← assoc, h_left]))
      add_zero := (ρ_ A).inv_comp_eq_id.1 (h_sep.hom_ext (by simp [← hm, ho, ← assoc, h_right]))
      add_assoc :=
        (α_ A A A).inv_comp_eq.1 (h_triples.hom_ext (by simp [← hm, ← assoc, add_assoc]))
      left_neg := h_sep.hom_ext (by simp [← hm, ho, hf, ← assoc])
      right_neg := h_sep.hom_ext (by simp [← hm, ho, hf, ← assoc]) }
  let _ : AddObj A :=
    { add_comm := h_pairs.hom_ext (by simp +zetaDelta [← hm, ← assoc, AddMonObj.add, add_comm]) }
  have h_add (T : Over S) (x y : T ⟶ A) : x + y = lift x y ≫ m := rfl
  -- The endomorphisms f c are additive and depend on c as a ring action.
  have hf_hom (c : O) : IsAdditive (f c) :=
    isAdditive_of_universal (h_pairs.hom_ext (by simp [h_add, ← hm, hf, ← assoc]))
  have hf_add (c d : O) : f (c + d) = f c + f d :=
    h_sep.hom_ext (by simp [h_add, ← hm, hf, ← assoc])
  have hf_mul (c d : O) : f (c * d) = f d ≫ f c := h_sep.hom_ext (by simp [hf, ← assoc])
  have hf_one : f 1 = 𝟙 A := h_sep.hom_ext (by simp [hf])
  let module (T : Over S) : Module O (T ⟶ A) :=
    letI : SMul O (T ⟶ A) := ⟨fun c x ↦ x ≫ f c⟩
    Module.ofMinimalAxioms (fun c x y ↦ add_comp x y (f c))
      (fun c d x ↦ (x ≫= hf_add c d).trans (comp_add ..)) (fun c d x ↦ x ≫= hf_mul c d)
      fun x ↦ x ≫= hf_one
  let moduleObj : ModuleObj O A := { comp_smul _ _ _ := (assoc ..).symm }
  -- Multiplication by N ≠ 0 is f N. It sends e i (N⁻¹ • z) to e i z, so its closed image is dense.
  have h_onto (N : ℕ) (hN : N ≠ 0) : Surjective (N • 𝟙 A).left := by
    rw [← N.cast_smul_eq_nsmul O (𝟙 A)]
    have h_dense : IsDenseFamily fun s : κ × V ↦ (e s.1 s.2).left := And.right h_sep
    refine h_dense.surjective _ (fun z : κ × V ↦ (e z.1 ((N⁻¹ : ℂ) • z.2)).left) fun z ↦ ?_
    have h_comp_left :
        (e z.1 ((N⁻¹ : ℂ) • z.2) ≫ f N).left = (e z.1 (F z.1 N ((N⁻¹ : ℂ) • z.2))).left :=
      congrArg CommaMorphism.left (hf N z.1 ((N⁻¹ : ℂ) • z.2))
    refine h_comp_left.trans ?_
    simp [← N.cast_smul_eq_nsmul ℂ, hN]
  exact ⟨{ toSmooth := smooth_of_allSpecializeTo_isReduced h_reduced, nsmul_surjective := h_onto },
    moduleObj, fun i ↦ .mk' (e i) (hm i), rfl, hf⟩

section LevelCoordinates

variable {E : Type} [Field E] [CMBase E] {D : PEL E}

/-- The index `a` of the subgroup `D.dualTorsion` of level torsion does not vanish at the point `t`
of `S`: `c` gives a line bundle on `S` with charts indexed by `D.dualTorsion` for each level torsion
point, and for all `l k : D.dualTorsion` with `l + k = a` the point `t` lies in chart `k` of the
bundle `c l`. -/
def Variety.ThetaNull.IsNonvanishingIndex {S : Scheme}
    (c : D.levelTorsion → LineBundle S D.dualTorsion) (t : S) (a : D.dualTorsion) : Prop :=
  ∀ l k : D.dualTorsion, l + k = a → t ∈ (c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).opens k

/-- The fibre of the theta family `X` at the complex point `t` is modelled on the theta torus `x`:
it has a torus model (a uniformisation by `V` along `t` with theta coordinates) for the period map
of `x`, whose theta coordinates are the theta functions of `x`. -/
def ThetaFamily.IsModelledOn {S : Scheme} {τ : S ⟶ Spec (CommRingCat.of (𝓞 E))}
    (X : ThetaFamily D S τ) (t : Spec (CommRingCat.of ℂ) ⟶ S) {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V) : Prop :=
  ∃ m : TorusModel (X := X) t x.toPeriodMap, m.θ = fun z k ↦ x.thetaCoord k z

section Torus

variable {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V)

/-- Let `t` be a complex point of `S` at which, for each level torsion point `ω`, the theta values
of `x` at the lift of `ω` are homogeneous coordinates for the line bundle `c ω`. Then at `t` the
bundles `c ω` cut out the set of all theta vectors of `x`: in every choice of charts through `t`,
the rank conditions `thetaRanks` on the transition values define that set (`IsCutOutAt`). -/
lemma ThetaTori.ThetaTorus.isCutOutAt_range_thetaCoord {S : Scheme}
    {t : Spec (CommRingCat.of ℂ) ⟶ S} {c : D.levelTorsion → LineBundle S D.dualTorsion}
    (hx : ∀ ω : D.levelTorsion,
      (c ω).IsHomogeneousCoords t fun k : D.dualTorsion ↦ x.thetaCoord k (x.torsionLift ω)) :
    IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm) c t
      (Set.range fun (z : V) (k : D.dualTorsion) ↦ x.thetaCoord k z) := by
  -- For the trivial valuation on ℂ every theta vector is its own reduction.
  have h_le (z : ℂ) : (1 : Valuation ℂ NNReal) z ≤ 1 := Valuation.one_apply_le_one z
  have h_aff (z : V) :
      IsIntegralCoords (fun k : D.dualTorsion ↦ x.thetaCoord k z)
        fun k : D.dualTorsion ↦ ⟨x.thetaCoord k z, h_le _⟩ :=
    -- Scale by `1`; a theta value at `z` that is nonzero has valuation `1`.
    ⟨1, by simpa [funext_iff] using x.thetaCoord_vector_ne_zero z⟩
  exact x.isCutOutAt_reduction (φ := algebraMap ..) (fun z ↦ ⟨⟨z, h_le z⟩, rfl⟩)
    x.hasGoodReduction_one h_aff
    (fun ω : D.levelTorsion ↦ h_aff (x.torsionLift ω)) hx

/-- Translation by the lift to `V` of `l ∈ D.dualTorsion` shifts the index `k` of a theta function
of `x` by `l`, up to an exponential factor, the multiplier of `x` and the value at `k` of the
bicharacter (the additive character of `D.dualTorsion` attached to the lift of `l`). -/
lemma ThetaTori.ThetaTorus.thetaCoord_add_torsionLift (l k : D.dualTorsion) (z : V) :
    x.thetaCoord k (z + x.torsionLift l) =
      (x.automorphyForm (x.torsionLift l) z + x.automorphyForm (x.torsionLift l) (x.torsionLift l) /
        2).exp *
        (x.multiplier (x.torsionLift l) * x.bicharacter
          (torsionLift_mem_latticeOver x.toPeriodMap l) k *
          x.thetaCoord (l + k) z) := by
  -- This is the Heisenberg law for the period point of the representative of `l`, at `z`.
  have h_lift : x.periodPoint (ratLift g (l : AdelicTorsion E D.Index)) = x.torsionLift l := rfl
  simpa [thetaShift_apply, ← eq_inv_mul_iff_mul_eq₀, h_lift, ← Complex.exp_neg] using
    congrFun (x.thetaShift_thetaCoord (frameTorsionClass_ratLift (l : AdelicTorsion E D.Index)) k) z

/-- For `s` in `D.dualTorsion` outside the Lagrangian subgroup, the square of the bicharacter of `s`
(an additive character of `D.dualTorsion`) sums to zero over the Lagrangian, as it is a non-trivial
character there. -/
lemma ThetaTori.ThetaTorus.sum_bicharacter_sq_eq_zero
    [Fintype (D.lagrangian.addSubgroupOf D.dualTorsion)] {s : D.dualTorsion}
    (hs : s ∉ D.lagrangian.addSubgroupOf D.dualTorsion) :
    ∑ l : D.lagrangian.addSubgroupOf D.dualTorsion,
      x.bicharacter (torsionLift_mem_latticeOver x.toPeriodMap s) l ^ 2 =
      0 := by
  -- The square, restricted to the Lagrangian, is a non-trivial additive character there.
  let ψ : AddChar (D.lagrangian.addSubgroupOf D.dualTorsion) ℂ :=
    (x.bicharacter (torsionLift_mem_latticeOver x.toPeriodMap s) ^ 2).compAddMonoidHom
      (D.lagrangian.addSubgroupOf D.dualTorsion).subtype
  have h_nontrivial : ψ ≠ 0 := fun h_trivial ↦
    hs (x.mem_lagrangian_of_bicharacter_sq s (DFunLike.congr_fun h_trivial))
  change ∑ l : D.lagrangian.addSubgroupOf D.dualTorsion, ψ l = 0
  exact ψ.sum_eq_zero_iff_ne_zero.mpr h_nontrivial

/-- Let `b` be an integer. There is a nonzero `Y : V` on which `𝓞 E` acts through `ρ`, that is,
through the embedding `Φ v₀`, such that the map `w ↦ x.intAction (star β - b) w - ρ (β - b) • w`
takes its values in the line through `Y`: it is `w ↦ ξ w • Y` for a linear form `ξ`. -/
lemma ThetaTori.ThetaTorus.exists_eigenline (b : ℤ) {ρ : 𝓞 E →+* ℂ}
    (hρ : ∀ d : 𝓞 E, ρ d = Φ v₀ d.val) :
    ∃ Y : V, Y ≠ 0 ∧ (∀ d : 𝓞 E, x.intAction d Y = ρ d • Y) ∧
      ∃ ξ : V →ₗ[ℂ] ℂ, ∀ w : V, x.intAction (star D.β - b) w - ρ (D.β - b) • w = ξ w • Y := by
  -- Coordinates `ε` in which `d : 𝓞 E` acts diagonally: by `Φ v₀ d` on the first axis, by its
  -- conjugate on the second, and by `Φ w d` at each other place `w`.
  obtain ⟨ε, hε⟩ := x.exists_std_equiv
  have h_std (d : 𝓞 E) (z : V) : ε (x.intAction d z) =
      ((Φ v₀ d.val * (ε z).fst.fst, star (Φ v₀ d.val) • (ε z).fst.snd),
        fun w ↦ Φ w.val d.val • (ε z).snd w) := by
    -- `using!`: the last component comes out as `Pi.map` of the diagonal maps, which is the
    -- stated function only after unfolding.
    simpa using! LinearMap.congr_fun (hε d) (ε z)
  -- The line is the first coordinate axis; on the other coordinates `star β` acts by `Φ v₀ β`.
  refine ⟨ε.symm ((1, 0), 0), ?_, fun d ↦ ?_,
    Φ v₀ (star D.β.val - D.β) • .fst .. ∘ₗ .fst .. ∘ₗ ε.toLinearMap, fun w ↦ ?_⟩
  · simp [← ε.injective.eq_iff]
  · simp [hρ, ← ε.injective.eq_iff, h_std, map_smul, funext_iff]
  · simp +contextual [hρ, ← ε.injective.eq_iff, D.emb_beta_eq_of_ne, h_std, Prod.ext_iff, sub_mul,
      map_smul, funext_iff]

/-- Let `N` embed `A` in projective space over `S`, and let `e : V →+ A(t)` be an additive map to
the points of `A` over the complex point `t` whose coordinates for `N` are the theta vectors of `x`.
Then `e` vanishes on the period lattice of `x`. -/
lemma ThetaTori.ThetaTorus.map_eq_zero_of_mem_periodLattice {S : Scheme}
    {t : Spec (CommRingCat.of ℂ) ⟶ S} {A : Over S} [AddObj A] {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) {e : V →+ (Over.mk t ⟶ A)}
    (he_coords : ∀ z : V, N.IsHomogeneousCoords (e z).left fun k : D.dualTorsion ↦ x.thetaCoord k z)
    {l : V} (hl : l ∈ x.periodLattice) : e l = 0 := by
  -- The coordinates at `0 + l` are those at `0` times the factor of automorphy at the period `l`,
  -- which is nonzero; so they are also coordinates of `e 0`.
  have h_zero : N.IsHomogeneousCoords (e 0).left fun k : D.dualTorsion ↦
    x.thetaCoord k (0 + l) := by
    rw [funext fun k ↦ (x.thetaCoord_mem_thetaSpace k).2 l hl 0]
    exact (he_coords 0).smul (by simp [x.isAppellHumbert_periodLattice.ne_zero hl])
  -- Both points lie over `t` and have the same coordinates, so they are equal.
  have h_left : (e (0 + l)).left = (e 0).left :=
    hN.eq_of_isHomogeneousCoords (by simp) (he_coords (0 + l)) h_zero (N.exists_landsIn _)
  simpa using OverMorphism.ext h_left

end Torus

/-- The padding tuple of `a` and `d` (two pairs `(1, 0)`, the pairs `(d, 1)` and `(1, - star d)`,
and the pairs `(a l, 0)`) is a Riemann tuple for `D` when
`star d * d + 3 + ∑ l, star (a l) * a l = D.paddedNorm`. -/
lemma isRiemannTuple_paddingTuple {a : Fin (D.paddedNorm - 3) → 𝓞 E} {d : 𝓞 E}
    (ha : star d * d + 3 + ∑ l : Fin (D.paddedNorm - 3), star (a l) * a l = D.paddedNorm) :
    IsRiemannTuple (paddingTuple a d) D := by
  -- Both sums run over two pairs `(1, 0)`, the pairs `(d, 1)` and `(1, - star d)`, and the
  -- pairs `(a l, 0)`: the first is `D.paddedNorm` by `ha`, and in the second `star d - star d`
  -- cancels.
  simp [IsRiemannTuple, ← ha, paddingTuple]
  ring

lemma isRiemannTuple_paddingTuple_one_zero :
    IsRiemannTuple (paddingTuple (1 : Fin (D.paddedNorm - 3) → 𝓞 E) 0) D :=
  isRiemannTuple_paddingTuple (by simp [D.three_le_paddedNorm])

/-- Let `A` over `S` be a commutative group scheme with an action of `𝓞 E`, and `c` a class in
`Pic A.left` satisfying Riemann's relation: for all `d` and `a : Fin (D.paddedNorm - 3) → 𝓞 E` with
`d̄ d + 3 + ∑ ā_l a_l = D.paddedNorm`, and all `T`-points `y`, `z`, the pull-backs satisfy
`c(d y + z) + c(y - d̄ z) + ∑ c(a_l y) + c(0) = c(z) + c(-d̄ z) + c(y) + (D.paddedNorm - 3) c(y)`.
Then `c` satisfies the class laws `D.HasClassLaws`: (a) the parallelogram law;
(b) `⟨β x, y⟩ = ⟨x, (1 - β) y⟩` for the pairing `Pic.pairing`, where `β` is the integer of `D` with
`star β = 1 - β`; and (c) the pull-back of `c` along `y` is `⟨β y, y⟩` plus its pull-back along
`0`. -/
lemma PEL.hasClassLaws_of_riemann_relation {S : Scheme} {A : Over S} [AddObj A]
    [ModuleObj (𝓞 E) A] {c : Pic A.left}
    (h_riemann : ∀ (a : Fin (D.paddedNorm - 3) → 𝓞 E) (d : 𝓞 E),
      star d * d + 3 + ∑ l : Fin (D.paddedNorm - 3),
        star (a l) * a l = D.paddedNorm → ∀ (T : Over S) (y z : T ⟶ A),
        c.atPoint (d • y + z) + c.atPoint (y - star d • z) +
          ∑ l : Fin (D.paddedNorm - 3), c.atPoint (a l • y) +
            c.atPoint (0 : T ⟶ A) =
          c.atPoint z + c.atPoint (-(star d • z)) + c.atPoint y + (D.paddedNorm - 3) • c.atPoint
            y) :
    D.HasClassLaws c := by
  -- `a` and `b` are paddings of `1` and `β`.
  obtain ⟨a, -, ha⟩ := D.hasPadding_one
  obtain ⟨b, -, hb⟩ := D.hasPadding_beta
  -- Subtract the relation at `(y, 0)` for a `d'` of the same norm: the padding terms cancel.
  have h_diff {a : Fin (D.paddedNorm - 3) → 𝓞 E} {d' : 𝓞 E}
      (ha : star d' * d' + 3 + ∑ l : Fin (D.paddedNorm - 3), star (a l) * a l = D.paddedNorm)
        (d : 𝓞 E)
      (hd : star d * d = star d' * d') {T : Over S} (y z : T ⟶ A) :
      c.atPoint (d • y + z) + c.atPoint (y - star d • z) + 2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint (d' • y) + c.atPoint y + c.atPoint z + c.atPoint (-(star d • z)) := by
    have h_at_zero : c.atPoint (d' • y) + c.atPoint y +
          ∑ l : Fin (D.paddedNorm - 3), c.atPoint (a l • y) + c.atPoint (0 : T ⟶ A) =
        c.atPoint (0 : T ⟶ A) + c.atPoint (0 : T ⟶ A) + c.atPoint y + (D.paddedNorm - 3) • c.atPoint
          y := by
      simpa only [add_zero, smul_zero, sub_zero, neg_zero] using h_riemann a d' ha T y 0
    linear_combination (norm := abel) h_riemann a d (by rw [hd, ha]) T y z - h_at_zero
  refine ⟨fun T y z ↦ ?_, fun T y z ↦ ⟨?_, ?_⟩⟩
  · -- The parallelogram law is the case `d = -1`, `d' = 1` at the point `(z, y)`.
    have h_par : c.atPoint (y - z) + c.atPoint (y + z) + 2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint z + c.atPoint z + c.atPoint y + c.atPoint y := by
      simpa [neg_add_eq_sub, add_comm z y] using h_diff ha (-1) (by simp) z y
    linear_combination (norm := abel) h_par
  · -- Take `d = β` at `(y, z)` and `d = 1` at `(y, z - β • z)`. As `star β = 1 - β`, both
    -- relations contain the point `y - (z - β • z)`.
    have h_β : c.atPoint (D.β • y + z) + c.atPoint (y - (z - D.β • z)) +
          2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint (D.β • y) + c.atPoint y + c.atPoint z + c.atPoint (-(z - D.β • z)) := by
      simpa [D.star_beta, sub_smul] using h_diff hb D.β rfl y z
    have h_one : c.atPoint (y + (z - D.β • z)) + c.atPoint (y - (z - D.β • z)) +
          2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint y + c.atPoint y + c.atPoint (z - D.β • z) + c.atPoint (-(z - D.β • z)) := by
      simpa using h_diff ha 1 rfl y (z - D.β • z)
    simp only [Pic.pairing, sub_smul, one_smul]
    linear_combination (norm := abel) h_β - h_one
  · -- Take `d = -star β` at `(z, z)`: as `star β = 1 - β`, `-star β • z + z = β • z`.
    have h_ev : c.atPoint (D.β • z) + c.atPoint (z + D.β • z) + 2 • c.atPoint (0 : T ⟶ A) =
        c.atPoint (D.β • z) + c.atPoint z + c.atPoint z + c.atPoint (D.β • z) := by
      simpa [D.star_beta, sub_smul, add_comm z] using
        h_diff hb (-star D.β) (by simp [mul_comm]) z z
    rw [Pic.pairing, add_comm (D.β • z) z]
    linear_combination (norm := abel) -h_ev

variable {S : Scheme} {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)} {R : CommRingCat}
  {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
  {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V} {c : D.levelTorsion → LineBundle S D.dualTorsion}

/-- Suppose `c` attaches to each class `ω` in `D.levelTorsion` a linear system on `S` with charts
indexed by `D.dualTorsion`, whose homogeneous coordinates at each `η i` are the theta coordinates of
`x i` at the torsion lift of `ω`, and that for each point `t` and each `s : D.dualTorsion` some `a`
makes `a`, `-a` and `s - a` nonvanishing indices at `t` (`IsNonvanishingIndex c t a`: `t` lies in
the chart `k` of `c l` whenever `l + k = a`). Then the bicharacters of the theta tori are regular
functions near each point. A point `t` of `S` with values in a local ring lands in an open `W` with
regular functions `r l m`, whose value at each `η i` in `W` is the bicharacter of `x i` at the
torsion lift of `l`, evaluated at `m`. -/
lemma Variety.exists_isRegularOn_bicharacter
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    {B : Type} [CommRing B] [IsLocalRing B] (t : Spec (CommRingCat.of B) ⟶ S) :
    ∃ (W : S.Opens) (r : D.dualTorsion → D.dualTorsion → PointFn S), LandsIn t W ∧
      (∀ l m : D.dualTorsion, IsRegularOn (r l m) W) ∧
      ∀ (l m : D.dualTorsion) (i : κ), LandsIn (η i) W →
        r l m (CommRingCat.of ℂ) (η i) =
          (x i).bicharacter (torsionLift_mem_latticeOver (x i).toPeriodMap l) m := by
  -- `t` factors through the open set `W` where the coordinates chosen by `o` are units.
  choose o _ho ho_neg ho_sub using h_index (t (closedPoint B))
  let W : S.Opens :=
    ⨅ (l : D.dualTorsion) (m : D.dualTorsion),
      ((c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).mul (c 0)).opens (-o m - l, m - o m)
  have hW : LandsIn t W := (landsIn_iInf _).2 fun l ↦ (landsIn_iInf _).2 fun m ↦
    landsIn_iff_mem.2 ⟨ho_neg m l _ (by simp), ho_sub m 0 _ (by simp)⟩
  -- Write `X k l` for the coordinate `k` of `c l` and `o` for `o m`. The function is
  -- `X (m - o - l) l * X (-o) 0 / (X (-o - l) l * X (m - o) 0)`: by `thetaCoord_add_torsionLift`
  -- at `z = 0` the theta constants cancel.
  have h_cocycle (l m : D.dualTorsion) : ∃ r : PointFn S, IsRegularOn r W ∧ ∀ i : κ,
    LandsIn (η i) W →
      r (CommRingCat.of ℂ) (η i) =
        (x i).bicharacter (torsionLift_mem_latticeOver (x i).toPeriodMap l) m := by
    -- The product bundle of `c l` and `c 0`, and the chart of it that contains `W`.
    let M : LineBundle S (D.dualTorsion × D.dualTorsion) :=
      (c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).mul (c 0)
    have hW_le : W ≤ M.opens (-o m - l, m - o m) := (iInf_le _ l).trans (iInf_le _ m)
    have hM : M.IsLinearSystem := (hc _).mul (hc 0)
    refine ⟨M.transition (-o m - l, m - o m) (m - o m - l, -o m),
      (hM.isRegularOn_transition _ _).mono hW_le, fun i hi ↦ ?_⟩
    -- At `z = 0`, the shift by the lift of `l` turns the index `k` into `l + k`.
    have h_shift (k : D.dualTorsion) : (x i).thetaCoord k ((x i).torsionLift l) =
        ((x i).automorphyForm ((x i).torsionLift l) 0 +
            (x i).automorphyForm ((x i).torsionLift l) ((x i).torsionLift l) / 2).exp *
          ((x i).multiplier ((x i).torsionLift l) *
            (x i).bicharacter (torsionLift_mem_latticeOver (x i).toPeriodMap l) k *
            (x i).thetaCoord (l + k) 0) := by
      simpa only [zero_add] using (x i).thetaCoord_add_torsionLift l k 0
    -- By `hx` the transition is a ratio of theta constants; `h_shift` leaves the bicharacter.
    have hi_chart : LandsIn (η i) (M.opens (-o m - l, m - o m)) := hi.mono hW_le
    revert hi_chart
    simp +contextual [M, hx .., sub_eq_add_neg, field, h_shift, AddChar.map_add_eq_mul]
  choose r hr hr_val using h_cocycle
  exact ⟨W, r, hW, hr, hr_val⟩

variable {V κ : Type} [FinComplexSpace V] {E : Type} [Field E] [CMBase E] {D : PEL E} {S : Scheme}
  {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)} {R : CommRingCat} {g : κ → GL D.Index (𝔸f E)}
  {ℓ : κ → Matrix D.Index D.Index ℂ} {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V}
  {c : D.levelTorsion → LineBundle S D.dualTorsion}

/-- Riemann's relation has regular coefficients near every point `t` of `S`. Let `c` have
nonvanishing indices, let `#D.dualTorsion` be a unit in `R`, and let `p`, `q` be Riemann tuples (`q`
starting with `(1, 0), (1, 0)`). Then there are indices `μ' s` and a function `r` regular near `t`
with the following property at each `η i` near `t`. The theta product of `x i` (the product of theta
coordinates `θ_{μ l}(a_l z + b_l y)`) for the pairs `doubledCoeffs p q` (the `(0, b)` of `q`, then
`p`) is `r` times the sum over `s` of those for `doubledCoeffs q p` at `μ' s`. -/
lemma Variety.exists_isRegularOn_riemann_coefficient
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    {K : Type} [Fintype K] {p q : Bool ⊕ K → 𝓞 E × 𝓞 E} (π : S ⟶ Spec R)
    (hT : IsUnit (Nat.card D.dualTorsion : R)) (hp : IsRiemannTuple p D) (hq : IsRiemannTuple q D)
    (hq_inl : ∀ l : Bool, q (Sum.inl l) = (1, 0)) (μ : (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion)
      (t : S) :
    ∃ U : S.Opens, t ∈ U ∧ ∃ (μ' : D.dualTorsion → (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion)
      (r : PointFn S),
      IsRegularOn r U ∧ ∀ (i : κ) (y z : V), LandsIn (η i) U →
        r (CommRingCat.of ℂ) (η i) * ∑ s : D.dualTorsion,
          (x i).thetaProduct (doubledCoeffs q p) (μ' s) y z =
          (x i).thetaProduct (doubledCoeffs p q) μ y z := by
  -- The first two factors are theta constants. Replace their indices by `k - o` and `o`, where
  -- `k` makes the index sums in `riemann_relation` agree and these constants are units near `t`.
  let k : D.dualTorsion := ∑ l : Bool ⊕ K, star (p l).1 • μ (.inr l) -
    ∑ l : K, star (q (.inr l)).1 • μ (.inl (.inr l))
  obtain ⟨o, ho, -, ho_sub⟩ := h_index t k
  let ν : Bool ⊕ K → D.dualTorsion := Sum.elim (fun b ↦ cond b (k - o) o) (μ ∘ .inl ∘ .inr)
  let μ' (s : D.dualTorsion) : (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion :=
    Sum.elim (fun l ↦ μ (.inr l) - (p l).1 • s) fun l ↦ ν l + (q l).1 • s
  -- The coefficient `r` is the ratio of the old to the new constants, a transition of
  -- `c 0 ⊗ c 0`, times the coefficient `τ` of `riemann_relation`.
  let τ : Γ(S, ⊤) :=
    ↑(hT.map (toSpecΓ R ≫ π.appTop).hom).unit⁻¹ * ↑(D.rTorsion.relIndex D.dualTorsion).sqrt
  let M : LineBundle S (D.dualTorsion × D.dualTorsion) := (c 0).mul (c 0)
  let r : PointFn S :=
    M.transition (o, k - o) (μ (.inl (.inl true)), μ (.inl (.inl false))) * ofSection τ
  have hr : IsRegularOn r (M.opens (o, k - o) ⊓ ⊤) :=
    (((hc 0).mul (hc 0)).isRegularOn_transition _ _).mul (isRegularOn_ofSection τ)
  have ht_mem : t ∈ M.opens (o, k - o) ⊓ ⊤ := ⟨⟨ho 0 _ (by simp), ho_sub 0 _ (by simp)⟩, ⟨⟩⟩
  refine ⟨_, ht_mem, μ', r, hr, fun i y z hi ↦ ?_⟩
  have h_unit : (x i).thetaCoord o 0 ≠ 0 ∧ (x i).thetaCoord (k - o) 0 ≠ 0 := by
    simpa [M, hx ..] using hi
  have h_riemann := (x i).riemann_relation (w := y) hp rfl hq (μ := μ ∘ .inr) (μ' := ν)
    (by simp [ν, k, hq_inl]) z
  simp [ν, hq_inl, mul_assoc, thetaProduct] at h_riemann
  simp [r, M, ofSection_eq, hx .., h_unit, τ, ν, μ', hq_inl, mul_assoc, ← h_riemann,
    mul_left_comm ((x i).thetaCoord o 0)⁻¹, thetaProduct, doubledCoeffs]

/-- Maps of a projective scheme extend along Riemann's relation: if for each pair `(a, b)` of
`doubledCoeffs q p` the map `(z, y) ↦ a z + b y` of the tori extends to `ψ l : A ⊗ A ⟶ A`, then the
maps for `doubledCoeffs p q` extend to morphisms `G l`, and the pull-backs of `N` along the `G l`
and along the `ψ l` have products of the same class. -/
lemma Variety.exists_maps_of_riemann_relation
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    {K : Type} [Fintype K] {p q : Bool ⊕ K → 𝓞 E × 𝓞 E} (π : S ⟶ Spec R)
    (hT : IsUnit (Nat.card D.dualTorsion : R)) (hp : IsRiemannTuple p D) (hq : IsRiemannTuple q D)
    (hp_inl : ∀ l : Bool, p (Sum.inl l) = (1, 0)) (hq_inl : ∀ l : Bool, q (Sum.inl l) = (1, 0))
    {A : Over S} {N : LineBundle A.left D.dualTorsion} (hN : N.IsProjEmbedding A.hom)
    {e : ∀ i : κ, V → (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_pairs : IsSeparatingFamily fun s : (κ × V) × V ↦
      (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left)
    (ψ : (Bool ⊕ K) ⊕ Bool ⊕ K → (A ⊗ A ⟶ A))
    (hψ : ∀ (l : (Bool ⊕ K) ⊕ Bool ⊕ K) (i : κ) (y z : V), lift (e i z) (e i y) ≫ ψ l =
      e i ((x i).intAction (doubledCoeffs q p l).1 z + (x i).intAction (doubledCoeffs q p l).2 y)) :
    ∃ G : (Bool ⊕ K) ⊕ Bool ⊕ K → (A ⊗ A ⟶ A),
      (∀ (l : (Bool ⊕ K) ⊕ Bool ⊕ K) (i : κ) (y z : V), lift (e i z) (e i y) ≫ G l =
        e i ((x i).intAction (doubledCoeffs p q l).1 z +
          (x i).intAction (doubledCoeffs p q l).2 y)) ∧
      (pi fun l : (Bool ⊕ K) ⊕ Bool ⊕ K ↦ N.pull (G l).left).picClass =
        (pi fun l : (Bool ⊕ K) ⊕ Bool ⊕ K ↦ N.pull (ψ l).left).picClass := by
  have h_proper : IsProper A.hom := hN.isProper
  let comb (i : κ) (a : 𝓞 E × 𝓞 E) (z y : V) : V := (x i).intAction a.1 z + (x i).intAction a.2 y
  have hψ_coords (s : (κ × V) × V) (l : (Bool ⊕ K) ⊕ Bool ⊕ K) :
      (N.pull (ψ l).left).IsHomogeneousCoords (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left
        fun k : D.dualTorsion ↦ (x s.1.1).thetaCoord k
          (comb s.1.1 (doubledCoeffs q p l) s.2 s.1.2) := by
    rw [IsHomogeneousCoords.pull_iff, ← comp_left, hψ]
    exact he_coords s.1.1 _
  -- Each side is locally a regular combination of the other, so the side of `G` gives a linear
  -- system `M` as well.
  let w (a b : Bool ⊕ K → 𝓞 E × 𝓞 E) (s : (κ × V) × V) (μ : (Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion) :
    ℂ :=
    (x s.1.1).thetaProduct (doubledCoeffs a b) μ s.1.2 s.2
  have h_local {a b : Bool ⊕ K → 𝓞 E × 𝓞 E} (ha : IsRiemannTuple a D) (hb : IsRiemannTuple b D)
      (hb_inl : ∀ l, b (Sum.inl l) = (1, 0)) : IsLocalCombination D.dualTorsion
        (fun s : (κ × V) × V ↦ (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left) (w a b) (w b a) := by
    intro μ t
    obtain ⟨U, hU, μ', r, hr, h_sum⟩ :=
      exists_isRegularOn_riemann_coefficient hc hx h_index π hT ha hb hb_inl μ ((A ⊗ A).hom t)
    refine ⟨_, hU, μ', _, hr.pull (A ⊗ A).hom, fun s hs ↦ ?_⟩
    have h_base : (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left ≫ (A ⊗ A).hom = η s.1.1 := Over.w _
    rw [landsIn_preimage, h_base] at hs
    -- `↓`: `Over.w` must rewrite before `simp` unfolds the point `lift`.
    simpa [w, ↓Over.w] using h_sum s.1.1 s.1.2 s.2 hs
  obtain ⟨M, hM, hM_coords, hM_class⟩ :
      ∃ M : LineBundle (A ⊗ A).left ((Bool ⊕ K) ⊕ Bool ⊕ K → D.dualTorsion), IsLinearSystem M ∧
      (∀ s : (κ × V) × V,
        M.IsHomogeneousCoords (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left (w p q s)) ∧
      M.picClass = (pi fun l ↦ N.pull (ψ l).left).picClass :=
    exists_isLinearSystem he_pairs (.pi fun l ↦ hN.isLinearSystem.pull _)
      (fun s ↦ .pi (hψ_coords s)) (h_local hp hq hq_inl) (h_local hq hp hp_inl)
  -- `M` defines a map `G` into a power of `A`, which is embedded by the Segre product of `N`.
  obtain ⟨G, hG, hG_pull⟩ := he_pairs.exists_map_of_coords
    (p := fun s ↦ Pi.lift fun l ↦ e s.1.1 (comb s.1.1 (doubledCoeffs p q l) s.2 s.1.2))
    hM (isProjEmbedding_pi (Pi.π _) (fun _ ↦ hN) (Pi.hom_ext _ _)) hM_coords
    fun s ↦ .pi fun l ↦ by simpa [← comp_left, IsHomogeneousCoords.pull_iff] using he_coords _ _
  refine ⟨fun l ↦ G ≫ Pi.π _ l, fun l i y z ↦ ?_, ?_⟩
  · rw [← assoc, hG ((i, y), z), Pi.lift_comp_π]
  · rw [← hM_class, ← hG_pull]
    simp [← pull_comp, pull_pi]

/-- The first two pairs of a padding tuple are `(1, 0)`. -/
lemma paddingTuple_inl (a : Fin (D.paddedNorm - 3) → 𝓞 E) (d : 𝓞 E) (l : Bool) :
    paddingTuple a d (Sum.inl l) = (1, 0) := by
  simp [paddingTuple]
/-- The addition of `V` and the action of `𝓞 E` on the tori `x i` extend to `A`. Assume the linear
systems `c ω` have the theta values of `x i` at the torsion lifts as coordinates at `η i`, that
nonvanishing indices exist at every point of `S`, and that `#D.dualTorsion` is a unit in `R`. Let
`A` over `S` be embedded by `N`, and let `e i z` be points of `A` over `η i` whose homogeneous
coordinates are the theta functions of `x i` at `z` and whose pairs separate `A ⊗ A`. Let the zero
extend to a section `o` of `A`. Then there are a morphism `add : A ⊗ A ⟶ A` with `e i (y + z)` equal
to `add` applied to `(e i y, e i z)`, and for each `d : 𝓞 E` an endomorphism `f` of `A` with
`e i z ≫ f = e i ((x i).intAction d z)`, where `intAction d` is the action of `d` on the torus. -/
lemma Variety.exists_add_and_intAction
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    (π : S ⟶ Spec R) (hT : IsUnit (Nat.card D.dualTorsion : R)) {A : Over S}
      {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) {e : ∀ i : κ, V → (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_pairs : IsSeparatingFamily fun s : (κ × V) × V ↦
      (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left)
    {o : 𝟙_ (Over S) ⟶ A} (ho : ∀ i : κ, toUnit (Over.mk (η i)) ≫ o = e i 0) :
    (∃ add : A ⊗ A ⟶ A, ∀ (i : κ) (y z : V), e i (y + z) = lift (e i y) (e i z) ≫ add) ∧
      ∀ d : 𝓞 E, ∃ f : A ⟶ A, ∀ (i : κ) (z : V), e i z ≫ f = e i ((x i).intAction d z) := by
  classical
  -- `a` is a padding of `1`, and the `a l` span `𝓞 E`.
  obtain ⟨a, ha_span, ha⟩ : HasPadding E D.paddedNorm 1 := D.hasPadding_one
  have h_tuple : IsRiemannTuple (paddingTuple a (-1)) D :=
    isRiemannTuple_paddingTuple (by simp [← ha])
  -- For `d = -1` only the projections and zero are needed as `ψ`.
  let ψ (q : 𝓞 E × 𝓞 E) : A ⊗ A ⟶ A :=
    if q.1 = 1 then fst A A else if q.2 = 1 then snd A A else toUnit _ ≫ o
  let b := doubledCoeffs (paddingTuple (1 : Fin (D.paddedNorm - 3) → 𝓞 E) 0) (paddingTuple a (-1))
  have hψ : ∀ l i y z, lift (e i z) (e i y) ≫ ψ (b l) =
      e i ((x i).intAction (b l).1 z + (x i).intAction (b l).2 y) := by
    simp [b, ψ, ho, doubledCoeffs, paddingTuple]
  obtain ⟨G, hG, -⟩ := exists_maps_of_riemann_relation hc hx h_index π hT h_tuple
    isRiemannTuple_paddingTuple_one_zero (paddingTuple_inl a _) (paddingTuple_inl 1 0) hN
    he_coords he_pairs (fun l ↦ ψ (b l)) hψ
  -- The pairs `(1, 1)`, `(-1, 1)`, `(a l, 0)` give addition, subtraction and the action of `a l`.
  refine ⟨⟨G (.inr (.inr (.inl false))), by simp [hG, doubledCoeffs, paddingTuple]⟩, fun d ↦ ?_⟩
  have h_sub (i : κ) (y z : V) :
      lift (e i z) (e i y) ≫ G (.inr (.inr (.inl true))) = e i (y - z) := by
    simp [hG, sub_eq_neg_add, doubledCoeffs, paddingTuple]
  have h_act (l : Fin (D.paddedNorm - 3)) (i : κ) (z : V) :
      e i z ≫ lift (𝟙 A) (𝟙 A) ≫ G (.inr (.inr (.inr l))) = e i ((x i).intAction (a l) z) := by
    simp [hG, ← assoc, doubledCoeffs, paddingTuple]
  -- The `d` whose action extends to `A` contain `1` and are closed under subtraction, so they
  -- form a subgroup that contains the `a l`.
  let P : Set (𝓞 E) := {d | ∃ f : A ⟶ A, ∀ i z, e i z ≫ f = e i ((x i).intAction d z)}
  have hP_sub : ∀ d ∈ P, ∀ d' ∈ P, d + -d' ∈ P := by
    rintro d ⟨f, hf⟩ d' ⟨f', hf'⟩
    refine ⟨lift f' f ≫ G (.inr (.inr (.inl true))), fun i z ↦ ?_⟩
    simp [hf, hf', h_sub, ← assoc, ← sub_eq_add_neg]
  let O : AddSubgroup (𝓞 E) := .ofSub P ⟨1, 𝟙 A, by simp⟩ hP_sub
  have h_le : Submodule.span ℤ (Set.range a) ≤ O.toIntSubmodule :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun l ↦ ⟨_, h_act l⟩)
  exact ha_span.ge.trans h_le Submodule.mem_top

/-- Let the `c ω` be linear systems on `S` with the theta constants of `x i` at `ω` as coordinates
of `η i` and the index condition `h_index`, and let #`D.dualTorsion` be a unit in `R`. Let `A` over
`S` be a commutative group scheme with an action of `𝓞 E`, embedded by `N`. Let `e i` be additive
maps from `V` to the points of `A` over `η i` that respect the action (`he_smul`), whose homogeneous
coordinates are the theta functions of `x i` and whose pairs separate `A ⊗ A`. Then the class of `N`
satisfies `D.HasClassLaws`: the parallelogram law and the two pairing laws for `β`. -/
lemma Variety.hasClassLaws_picClass
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    (π : S ⟶ Spec R) (hT : IsUnit (Nat.card D.dualTorsion : R)) {A : Over S} [AddObj A]
    [ModuleObj (𝓞 E) A] {N : LineBundle A.left D.dualTorsion} (hN : N.IsProjEmbedding A.hom)
    {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_pairs : IsSeparatingFamily fun s : (κ × V) × V ↦
      (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left)
    (he_smul : ∀ (d : 𝓞 E) (i : κ) (z : V), d • e i z = e i ((x i).intAction d z)) :
    D.HasClassLaws N.picClass := by
  have h_proper : IsProper A.hom := hN.isProper
  refine D.hasClassLaws_of_riemann_relation fun a d ha T y z ↦ ?_
  -- With the group law every map `(z, y) ↦ q.1 z + q.2 y` exists, and the maps `G` of the
  -- extension step are of this form.
  let ψ (q : 𝓞 E × 𝓞 E) : A ⊗ A ⟶ A := q.1 • fst A A + q.2 • snd A A
  have hψ (q : 𝓞 E × 𝓞 E) (i : κ) (y z : V) : lift (e i z) (e i y) ≫ ψ q =
      e i ((x i).intAction q.1 z + (x i).intAction q.2 y) := by
    simp [ψ, he_smul, comp_add]
  obtain ⟨G, hG, hG_class⟩ := exists_maps_of_riemann_relation hc hx h_index π hT
    (isRiemannTuple_paddingTuple ha) isRiemannTuple_paddingTuple_one_zero (paddingTuple_inl a d)
    (paddingTuple_inl 1 0) hN (e := fun i z ↦ e i z) he_coords he_pairs
    (fun l ↦ ψ (doubledCoeffs (paddingTuple 1 0) (paddingTuple a d) l)) fun l ↦ hψ _
  have hGψ (l) : G l = ψ (doubledCoeffs (paddingTuple a d) (paddingTuple 1 0) l) :=
    he_pairs.hom_ext (by simp [hG, hψ])
  -- Pull the identity of classes back along the point `(y, z)` of `A ⊗ A`, keeping the relation
  -- in terms of `(q.1 • y + q.2 • z)` so cancellation runs over an abstract additive group.
  have h_lift_ψ (q : 𝓞 E × 𝓞 E) : lift y z ≫ ψ q = q.1 • y + q.2 • z := by
    simp [ψ, comp_add]
  have h_pi {ι : Type} [Fintype ι] (g : ι → (A ⊗ A ⟶ A)) :
      Pic.pull (lift y z).left (pi fun l : ι ↦ N.pull (g l).left).picClass =
        ∑ l : ι, N.picClass.atPoint (lift y z ≫ g l) := by
    simp [-lift_left, ← pull_comp, Pic.atPoint]
  let f (q : 𝓞 E × 𝓞 E) : Pic T.left := N.picClass.atPoint (q.1 • y + q.2 • z)
  have h_sum := congrArg (Pic.pull (lift y z).left) hG_class
  rw [h_pi, h_pi] at h_sum
  simp_rw [hGψ, h_lift_ψ] at h_sum
  have h_cancel {G : Type 1} [AddCommGroup G] (g : 𝓞 E × 𝓞 E → G)
      (h : ∑ l, g (doubledCoeffs (paddingTuple a d) (paddingTuple 1 0) l) =
           ∑ l, g (doubledCoeffs (paddingTuple 1 0) (paddingTuple a d) l)) :
      g (d, 1) + g (1, -star d) + ∑ l : Fin (D.paddedNorm - 3), g (a l, 0) + g (0, 0) =
        g (0, 1) + g (0, -star d) + g (1, 0) + (D.paddedNorm - 3) • g (1, 0) := by
    simp [doubledCoeffs, paddingTuple] at h
    linear_combination (norm := abel) h
  simpa only [f, one_smul, zero_smul, add_zero, zero_add, neg_smul, ← sub_eq_add_neg,
    zero_sub] using
    h_cancel f h_sum

/-- The theta law on base changes to local rings. Assume the following: the linear systems `c ω` on
`S` have, at the separating complex points `η i`, the theta coordinates of `x i` at lifts of `ω`;
they satisfy `h_index`; and `#D.dualTorsion` is a unit in `R`. Also `N` embeds the `𝓞 E`-group `A`
projectively with theta coordinates at the separating points `e i z`, and `σ` lifts the level
torsion. Then for a base change `T` of `A` along `t : Spec B ⟶ S`, `B` local, the pull-backs of `N`
and `σ` on `D.dualTorsion` form a theta structure (`IsThetaStructure`) for the Lagrangian, with some
characters `C s`. -/
lemma Variety.exists_isThetaStructure
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a))
    (π : S ⟶ Spec R) (hT : IsUnit (Nat.card D.dualTorsion : R))
    (hη_sep : IsSeparatingFamily fun i : κ ↦ (toUnit (Over.mk (η i))).left)
    {A : Over S} [AddObj A] [ModuleObj (𝓞 E) A] {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_coords : ∀ (i : κ) (z : V),
      N.IsHomogeneousCoords (e i z).left fun k : D.dualTorsion ↦ (x i).thetaCoord k z)
    (he_sep : IsSeparatingFamily fun s : κ × V ↦ (e s.1 s.2).left)
    {σ : D.levelTorsion →ₗ[𝓞 E] (𝟙_ (Over S) ⟶ A)} (hσ : ∀ (l : D.levelTorsion) (i : κ),
      toUnit (Over.mk (η i)) ≫ σ l = e i ((x i).torsionLift l))
    {B : Type} [CommRing B] [IsLocalRing B] (t : Spec (CommRingCat.of B) ⟶ S)
    {T : Over (Spec (CommRingCat.of B))} [AddObj T] [ModuleObj (𝓞 E) T]
    {q : (Over.map t).obj T ⟶ A} (hq : IsGroupBaseChange t (B := T) q) :
    ∃ C : D.dualTorsion → AddChar D.dualTorsion B,
      IsThetaStructure (D.lagrangian.addSubgroupOf D.dualTorsion)
      (.comp (hq.pullSection ∘ₗ σ) (AddSubgroup.inclusion D.dualTorsion_le_levelTorsion))
      (hN.isLinearSystem.pull q.left) C := by
  -- The bicharacters of the `x i` are the values of regular functions `r s m` near `t`.
  obtain ⟨W, r, hW, hr, hr_val⟩ := exists_isRegularOn_bicharacter hc hx h_index t
  -- Two functions regular on `W` that agree at the dense points `η i` agree at `t`.
  have h_ext {r₁ r₂ : PointFn S} (h₁ : IsRegularOn r₁ W) (h₂ : IsRegularOn r₂ W)
      (h : ∀ i, LandsIn (η i) W → r₁ (.of ℂ) (η i) = r₂ (.of ℂ) (η i)) :
      r₁ (.of B) t = r₂ (.of B) t :=
    hη_sep.pointFn_ext h₁ h₂ h _ t hW
  -- The value of `r s m` at `t` is again a character in `m`.
  have hC_zero (s : D.dualTorsion) : r s 0 (.of B) t = (1 : PointFn S) (.of B) t :=
    h_ext (hr s 0) (by simp [IsRegularOn]) (by simp +contextual [hr_val])
  have hC_add (s m m' : D.dualTorsion) : r s (m + m') (.of B) t = (r s m * r s m') (.of B) t :=
    h_ext (hr s (m + m')) (by simp +contextual [IsRegularOn, hr _ _ _])
      (by simp +contextual [hr_val, AddChar.map_add_eq_mul])
  let C (s : D.dualTorsion) : AddChar D.dualTorsion B :=
    .mk (fun m ↦ r s m (.of B) t) (hC_zero s) (hC_add s)
  -- The five conditions: the identity `C s (-m) = C m s`, the theta law, equal coordinates on the
  -- Lagrangian, the order of `D.dualTorsion` is a unit, and the vanishing sums off the Lagrangian.
  refine ⟨C, fun s m ↦ ?_, fun ε s ↦ ?_, fun s hs ↦ ?_, ?_, fun s hs ↦ ?_⟩
  · exact h_ext (hr s _) (hr m s) (by simp +contextual [hr_val, bicharacter_neg_eq_swap])
  · refine exists_isSectionLift_coordSection _ _ fun l m _ y hl hm ↦
      ⟨⟨(ε : ℤ) • l - s, ?_⟩, fun k ↦ ?_⟩
    · simp only [↓H0_smul, map_obj_left, coordSection, add_sub_cancel, smul_smul,
        Int.units_coe_mul_self, one_smul, pull_transition, PointFn.pull, landsIn_preimage.1 hl,
        N.transition_self, mul_one, AddChar.val_isUnit, IsUnit.map]
    -- The map `y ↦ ε y + σ s` of `T` is the base change of `(ε • 𝟙 A) ≫ tr`.
    let s' : D.levelTorsion := ⟨s, D.dualTorsion_le_levelTorsion s.property⟩
    let tr : A ⟶ A := translation (σ s')
    have h_comm : ((ε : ℤ) • 𝟙 T).left ≫ (translation (hq.pullSection (σ s'))).left ≫ q.left =
        q.left ≫ ((ε : ℤ) • 𝟙 A).left ≫ tr.left := by
      simpa [tr, ← hq.translation_comp, Int.cast_smul_eq_zsmul] using
        hq.smul_id_comp (ε : ℤ) =≫ tr.left
    have h_reg (m : D.dualTorsion) : (PointFn.pull A.hom (r s m) *
        N.transition l ((ε : ℤ) • (s + m))).IsRegularOn (A.hom ⁻¹ᵁ W ⊓ N.opens l) :=
      ((hr s m).pull A.hom).mul (hN.isLinearSystem.isRegularOn_transition l _)
    -- The sign `ε` acts on theta functions up to a constant `ρ i`.
    choose ρ h_neg using fun i ↦ (x i).exists_thetaCoord_sign_smul ε
    -- The law on `A`: at theta points it is `thetaCoord_add_torsionLift` and `h_neg`.
    have h_law : (PointFn.pull A.hom (r s k) * N.transition l ((ε : ℤ) • (s + k))) _ (y ≫ q.left) =
        (PointFn.pull A.hom (r s m) * N.transition l ((ε : ℤ) • (s + m)) *
          PointFn.pull (((ε : ℤ) • 𝟙 A) ≫ tr).left (N.transition m k)) _ (y ≫ q.left) := by
      refine he_sep.pointFn_ext ((h_reg k).mono inf_le_left) ((h_reg m).mul
        ((hN.isLinearSystem.isRegularOn_transition m k).pull (((ε : ℤ) • 𝟙 A) ≫ tr).left)) ?_ _ _ ?_
      · simp +contextual [hr_val, he_coords .., thetaCoord_add_torsionLift, h_neg, ← comp_left,
          field, tr, s', hσ, ← map_zsmul, ← map_add, comp_add, AddGrpObj.comp_zsmul]
      · simpa [tr, ← h_comm, LandsIn.comp, hW] using! ⟨hl, hm⟩
    -- `using!`: the coordinate sections of the pull-back of `N` are its transitions only up to
    -- unfolding `coordSection`.
    simpa [↓H0_smul, ← hr _ _ _ _ hW, C, tr, ← h_comm] using! h_law
  · -- On the Lagrangian the two sections have the same transitions: checked at the points `e i z`.
    exact H0_ext fun _ _ B' u hu ↦ he_sep.pointFn_ext
      (hN.isLinearSystem.isRegularOn_transition _ _) (hN.isLinearSystem.isRegularOn_transition _ _)
      (by simp +contextual [he_coords .., thetaCoord_eq_of_mem_lagrangian _ s hs]) B' _ hu
  · simpa using hT.map (preimage (t ≫ π)).hom
  · -- For `s` outside the Lagrangian the sum is zero at each `η i`.
    -- `using!`: the sum of the functions `r s l ^ 2` agrees with the sum of their values only up to
    -- unfolding.
    simpa using! h_ext (r₁ := ∑ l : D.lagrangian.addSubgroupOf D.dualTorsion, r s l ^ 2) (r₂ := 0)
      (by simp +contextual [IsRegularOn, hr _ _ _]) (by simp [IsRegularOn])
      fun i hi ↦ by simpa [hr_val _ _ _ hi] using! (x i).sum_bicharacter_sq_eq_zero hs

/-- Sections of `A` that restrict at each `η i` to `e i` of the lift of the level point are the
function of an `𝓞 E`-linear map `ς`, when the `e i` respect the action of `𝓞 E` and vanish on the
period lattices. -/
lemma Variety.exists_linearMap_coe_eq_of_comp_eq_torsionLift {E : Type} [Field E] [CMBase E]
    {D : PEL E} {S : Scheme} {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)}
    {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
    {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V}
    (hη_sep : IsSeparatingFamily fun i : κ ↦ (toUnit (Over.mk (η i))).left)
    {A : Over S} [AddObj A] [ModuleObj (𝓞 E) A] [IsSeparated A.hom]
    {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_smul : ∀ (d : 𝓞 E) (i : κ) (z : V), d • e i z = e i ((x i).intAction d z))
    (he_lattice : ∀ (i : κ) (l : V), l ∈ (x i).periodLattice → e i l = 0)
    {σ : D.levelTorsion → (𝟙_ (Over S) ⟶ A)} (hσ : ∀ (l : D.levelTorsion) (i : κ),
      toUnit (Over.mk (η i)) ≫ σ l = e i ((x i).torsionLift l)) :
    ∃ ς : D.levelTorsion →ₗ[𝓞 E] (𝟙_ (Over S) ⟶ A), ⇑ς = σ := by
  -- At each `η i` both sides are `e i` of lifts that differ by an element of the period lattice.
  have hσ_add (l m : D.levelTorsion) : σ (l + m) = σ l + σ m := by
    refine hη_sep.hom_ext fun i ↦ sub_eq_zero.1 ?_
    simp [hσ, PeriodMap.torsionLift, ← map_add, ← map_sub, comp_add]
    exact he_lattice i _ ⟨_, by simp, rfl⟩
  have hσ_smul (d : 𝓞 E) (l : D.levelTorsion) : σ (d • l) = d • σ l := by
    refine hη_sep.hom_ext fun i ↦ sub_eq_zero.1 ?_
    simp [hσ, he_smul, PeriodMap.torsionLift, intAction, ← toRealVectors_smul, ← map_sub]
    exact he_lattice i _ ⟨_, by simp, rfl⟩
  exact ⟨⟨⟨σ, hσ_add⟩, hσ_smul⟩, rfl⟩

/-- The points of `A` over a point `η` of `S`, seen as points of the fibre of `A` over `η`; the map
is `𝓞 E`-linear. -/
noncomputable def Variety.fibrePointMap {E : Type} [Field E] {S : Scheme}
    (A : Over S) [AddObj A] [ModuleObj (𝓞 E) A] (η : Spec (CommRingCat.of ℂ) ⟶ S) :
    (Over.mk η ⟶ A) →ₗ[𝓞 E] (𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ (Over.pullback η).obj A) :=
  ((isGroupBaseChange_counit (O := 𝓞 E) (A := A) η).pointEquiv (T := 𝟙_ _)).symm.toLinearMap

/-- The point of the fibre given by `fibrePointMap A η u` is the pair of `u` and the point `η`. -/
lemma Variety.fibrePointMap_left {E : Type} [Field E] {S : Scheme}
    {η : Spec (CommRingCat.of ℂ) ⟶ S} (A : Over S) [AddObj A] [ModuleObj (𝓞 E) A]
    (u : Over.mk η ⟶ A) :
    (fibrePointMap (E := E) A η u).left = (lift u (𝟙 (Over.mk η))).left :=
  -- `using!`: `fibrePointMap` is the pull-back lift only after unfolding `pointEquiv`.
  pullback.hom_ext (by simpa [pullback.lift_fst] using!
      (isGroupBaseChange_counit (O := 𝓞 E) (A := A) η).isPullback.lift_fst ..)
    (by simpa [pullback.lift_snd] using (fibrePointMap (E := E) A η u).w)

/-- The torus `x` uniformises the fibre of `A` over the complex point `η`: the fibre has a
uniformisation `u` with exponential map `e` followed by `fibrePointMap A η`, lattice the period
lattice of `x`, and the theta functions of `x` as theta coordinates of the pull-back of `N`; and
its relative dimension `d` is `abelianDim E D.Index`. -/
lemma Variety.exists_uniformisation_pullback_of_isSeparatingFamily {E : Type} [Field E] [CMBase E]
    {D : PEL E} {S : Scheme} {η : Spec (CommRingCat.of ℂ) ⟶ S} {g : GL D.Index (𝔸f E)}
    {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V)
    {A : Over S} [IsAbelianScheme A] [ModuleObj (𝓞 E) A] {N : LineBundle A.left D.dualTorsion}
    (hN : N.IsProjEmbedding A.hom) (h_par : N.picClass.ParallelogramLaw) {e : V →+ (Over.mk η ⟶ A)}
    (he_coords : ∀ z : V, N.IsHomogeneousCoords (e z).left fun k : D.dualTorsion ↦ x.thetaCoord k z)
    (he_fibre : IsSeparatingFamily fun z : V ↦ (lift (e z) (𝟙 (Over.mk η))).left)
    (he_lattice : ∀ l : V, l ∈ x.periodLattice → e l = 0)
    (d : ℕ) (h_smooth : SmoothOfRelativeDimension d ((Over.pullback η).obj A).hom) :
    ∃ u : Uniformisation ((Over.pullback η).obj A) V,
      HasThetaCoords u.lattice (atGeneric u.expMap) (N.pull ((mapPullbackAdj η).counit.app A).left)
        x.automorphyForm x.multiplier (flip x.thetaCoord) ∧
      u.expMap = .comp (fibrePointMap (E := E) A η) e ∧ u.lattice = x.periodLattice ∧
      d = abelianDim E D.Index := by
  have h_fibre := isGroupBaseChange_counit (O := 𝓞 E) (A := A) η
  refine x.exists_uniformisation_of_isSeparatingFamily d h_smooth
    (hN.of_isPullback h_fibre.isPullback) ?_ _ ?_
    ?_ ?_
  · -- the pull-back of `N` to the fibre satisfies the parallelogram law
    simp [Pic.ParallelogramLaw, ↓h_fibre.atPoint_picClass_pull, h_par _]
  · -- the points of `e` separate the fibre
    simpa [fibrePointMap_left] using he_fibre
  · -- the theta functions of `x` are homogeneous coordinates along `e`
    simp [fibrePointMap_left, he_coords, IsHomogeneousCoords.pull_iff]
  · -- `e` kills the period lattice
    simp +contextual [he_lattice]

end LevelCoordinates

omit [IsLocallyNoetherian S] in
/-- The signature condition for `A`: at every point `s` of `S` with values in a local ring there are
coordinates of `A` at `0` in which `𝓞 E` acts on the Lie algebra by matrices `m` with the signature
given by `β` and `b` (`HasSignature`). `Φ v₀` is the embedding of `E` into `ℂ` at the base place
`v₀`. -/
lemma Variety.exists_isLieChart_hasSignature (j : ι → κ) (hη : IsDenseFamily fun i : ι ↦ η (j i))
    {E : Type} [Field E] [CMBase E] {D : PEL E} {R : CommRingCat} {π : S ⟶ Spec R} {φ : 𝓞 E →+* R}
    (hη_base : ∀ (i : κ) (d : 𝓞 E), (preimage (η i ≫ π ≫ specMap φ)).hom d = Φ v₀ d.val)
    {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
    {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V} (hβ : IsUnit (φ (star D.β - D.β)))
    {A : Over S} [AddObj A] [ModuleObj (𝓞 E) A]
    (h_dim : SmoothOfRelativeDimension (abelianDim E D.Index) A.hom)
    {e : ∀ i : κ, V →+ (Over.mk (η i) ⟶ A)}
    (he_smul : ∀ (d : 𝓞 E) (i : κ) (z : V), d • e i z = e i ((x i).intAction d z))
    {u : ∀ i : κ, Uniformisation ((Over.pullback (η i)).obj A) V}
    (hu_e : ∀ i : κ, (u i).expMap = .comp (fibrePointMap (E := E) A (η i)) (e i))
    (b : ℤ) {B : CommRingCat} (s : Spec B ⟶ S) [IsLocalRing B] :
    ∃ (U : A.left.Opens) (z : Fin (abelianDim E D.Index) → Γ(A.left, U))
      (m : 𝓞 E → Matrix (Fin (abelianDim E D.Index)) (Fin (abelianDim E D.Index)) B),
      IsLieChart A (ι := Fin (abelianDim E D.Index)) s U z m ∧
      HasSignature (preimage (s ≫ π ≫ specMap φ)).hom (star D.β - b) (D.β - b) m := by
  -- Work over the stalk at the closed point of `s`; there `HasSignature` is checked at the dense
  -- points `η (j i)`, where it becomes a statement on the action on `V` (`hasSignature_iff`).
  rw [← Spec_stalkClosedPointTo_fromSpecStalk s]
  simp only [assoc, preimage_comp, preimage_map, CommRingCat.hom_comp]
  obtain ⟨U, z, m, h_jac⟩ :=
    exists_isLieChart (O := 𝓞 E) h_dim (S.fromSpecStalk (s (closedPoint _)))
  refine ⟨U, z, _, h_jac rfl, .of_points (stalk_eq_zero_of_dense hη) ?_ _ (.map _ ?_)⟩
  · rintro ⟨i, ψ, hψ⟩
    exact ((u _).hasSignature_iff (F := (x (j i)).intAction) (by simp [hu_e, ← he_smul])
      (h_jac hψ) (isGroupBaseChange_counit (O := 𝓞 E) (A := A) (η (j i)))
      (finrank_eq_abelianDim (x (j i)).realEquiv)).2
      ((x (j i)).exists_eigenline b fun d ↦ by simpa [← hψ] using hη_base (j i) d)
  · simpa [← assoc] using hβ.map (preimage (S.fromSpecStalk (s (closedPoint _)) ≫ π)).hom

unseal ThetaObject.groupScheme ThetaObject.toFamily in
/-- A theta family from dense complex points: if `S` is embedded by the linear systems `c ω` whose
coordinates at the complex points `η i` are the theta functions of the theta tori `x i`, then `S`
is, under the further hypotheses of the statement, the base of a theta family whose object at each
`η i` is modelled on `x i`. Here `S` is reduced and locally noetherian, `V` is a finite-dimensional
complex space, and `Φ v₀` is the embedding of `E` into `ℂ` at the base place `v₀`. -/
theorem Variety.exists_thetaFamily_of_points (j : ι → κ) (hη : IsDenseFamily fun i : ι ↦ η (j i))
    {E : Type} [Field E] [CMBase E] {D : PEL E} {R : CommRingCat} {π : S ⟶ Spec R}
    {φ : 𝓞 E →+* R} (hφ : Mono (specMap φ))
    (hη_base : ∀ (i : κ) (d : 𝓞 E), (preimage (η i ≫ π ≫ specMap φ)).hom d = Φ v₀ d.val)
    {g : κ → GL D.Index (𝔸f E)} {ℓ : κ → Matrix D.Index D.Index ℂ}
    {c : D.levelTorsion → LineBundle S D.dualTorsion} {x : ∀ k : κ, ThetaTorus D (g k) (ℓ k) V}
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem) [Fintype D.levelTorsion]
    (hπ : (LineBundle.pi c).IsProjEmbedding π)
    (hx : ∀ (i : κ) (ω : D.levelTorsion),
      (c ω).IsHomogeneousCoords (η i) fun k : D.dualTorsion ↦
        (x i).thetaCoord k ((x i).torsionLift ω))
    (hβ : IsUnit (φ (star D.β - D.β))) (hT : IsUnit (Nat.card D.dualTorsion : R))
    (h_closed : AllSpecializeTo S fun {k : Type} [Field k] (t : Spec (CommRingCat.of k) ⟶ S) ↦
      ∃ Z : Set (D.dualTorsion → k), IsCutOutAt D.paddedNorm D.exponentBound
        (thetaRanks D.dualTorsion D.paddedNorm) c t Z)
    (h_index : ∀ (t : S) (s : D.dualTorsion), ∃ a : D.dualTorsion,
      IsNonvanishingIndex c t a ∧ IsNonvanishingIndex c t (-a) ∧ IsNonvanishingIndex c t (s - a)) :
    ∃ X : ThetaFamily D S (π ≫ specMap φ), ∀ i : κ, X.IsModelledOn (η i) (x i) := by
  -- `A` is the closure of the theta points over `S`. Riemann's relation extends the maps
  -- `(z, y) ↦ a z + b y` from the theta points to `A ⊗ A`; this makes `A` an abelian scheme with
  -- an action of `𝓞 E` and gives the class identities. The other fields of `ThetaFamily` are
  -- mostly identities of regular functions, checked at the dense complex points.
  obtain ⟨A, N, e, h_closure⟩ : ∃ (A : Over S) (N : LineBundle A.left D.dualTorsion)
      (e : ∀ i, V → (Over.mk (η i) ⟶ A)), IsFlatClosure (fun i z k ↦ (x i).thetaCoord k z) N e :=
    exists_isFlatClosure j hη hc (Nat.le_of_lt D.three_le_paddedNorm) D.isCutDegree
      (fun i ↦ (x i).thetaCoord_vector_ne_zero)
      (fun i ↦ (x i).isCutOutAt_range_thetaCoord (hx i)) h_closed
  obtain ⟨hN, h_flat, he_coords, he_fibre, h_reduced, he_sep⟩ := h_closure
  replace he_fibre (i : κ) :
      IsSeparatingFamily fun z : V ↦ (lift (e i z) (𝟙 (Over.mk (η i)))).left := he_fibre i
  have h_proper : IsProper A.hom := hN.isProper
  have hη_sep : IsSeparatingFamily fun i : κ ↦ (toUnit (Over.mk (η i))).left :=
    ⟨(inferInstance : IsReduced S), hη.of_comp⟩
  have he_pairs :
      IsSeparatingFamily fun s : (κ × V) × V ↦ (lift (e s.1.1 s.2) (e s.1.1 s.1.2)).left :=
    he_sep.prod (y := fun s : κ × V ↦ e s.1 s.2) (e := fun s ↦ e s.1) hη he_sep.1
      fun s ↦ (he_fibre s.1).right
  -- The linear systems `c l` are the coordinates of sections `σ l` of `A`.
  have h_section (l : D.levelTorsion) : ∃ σ : 𝟙_ (Over S) ⟶ A,
      (∀ i : κ, toUnit (Over.mk (η i)) ≫ σ = e i ((x i).torsionLift l)) ∧ N.pull σ.left = c l :=
    hη_sep.exists_map_of_coords (hc l) hN (fun i ↦ hx i l) fun i ↦ he_coords i _
  choose σ hσ hσ_pull using h_section
  -- The group law and the action of `𝓞 E`; from here on the `e i` are homomorphisms.
  have h_zero (i : κ) : toUnit (Over.mk (η i)) ≫ σ 0 = e i 0 := by simp [hσ]
  obtain ⟨⟨add, h_add⟩, h_act⟩ :=
    exists_add_and_intAction hc hx h_index π hT hN he_coords he_pairs h_zero
  choose f hf using h_act
  obtain ⟨_, _, e, rfl, he_smul⟩ :=
    exists_isAbelianScheme j hη he_fibre he_sep h_reduced hf add (σ 0) h_add h_zero
  -- The `rfl` above replaced `e` by a family of additive maps; put the facts back in plain form.
  beta_reduce at he_coords he_fibre he_sep he_pairs hσ he_smul
  have h_class : D.HasClassLaws N.picClass :=
    hasClassLaws_picClass hc hx h_index π hT hN he_coords he_pairs he_smul
  have he_lattice (i : κ) (l : V) (hl : l ∈ (x i).periodLattice) : e i l = 0 :=
    (x i).map_eq_zero_of_mem_periodLattice hN (he_coords i) hl
  -- `σ` is linear: the lifts `(x i).torsionLift l` are linear in `l` modulo the lattice.
  obtain ⟨ς, rfl⟩ := exists_linearMap_coe_eq_of_comp_eq_torsionLift hη_sep he_smul he_lattice hσ
  -- `e i` uniformises the fibre over `η i`, and this forces the dimension.
  have h_unif (i : κ) := exists_uniformisation_pullback_of_isSeparatingFamily (x i) hN h_class.1
    (he_coords i)
    (he_fibre i) (he_lattice i)
  have h_dim : SmoothOfRelativeDimension (abelianDim E D.Index) A.hom := by
    refine smoothOfRelativeDimension_of_fibres he_sep.2 fun s d h_smooth ↦ ?_
    obtain ⟨-, -, -, -, hd⟩ := h_unif s.1 d h_smooth
    exact hd
  -- The fibre over `η i` is the base change of `A` along `η i`, so it has the same dimension.
  choose u hu_theta hu_e hu_L _ using fun i : κ ↦
    h_unif i _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (isGroupBaseChange_counit (O := 𝓞 E) (A := A) (η i)).isPullback h_dim)
  refine ⟨{ total := A, lineBundle := N, embeds := hN, levelPoints := ς, class_laws := h_class
            relative_dim := h_dim
            theta_law t T _ _ q hq :=
              exists_isThetaStructure hc hx h_index π hT hη_sep hN he_coords he_sep hσ t hq
            signature b _ s _ :=
              exists_isLieChart_hasSignature j hη hη_base hβ h_dim he_smul hu_e b s
            eq_of_level_coords_eq t t' h_base h_coord := ?ext }, fun i ↦ ?model⟩
  case ext =>
    -- The lists agree, so do the pull-backs of the product of the `c l`.
    exact hπ.ext (by simpa [← hσ_pull, pull_pi] using congrArg pi (funext h_coord))
      (hφ.right_cancellation _ _ h_base)
  case model =>
    refine ⟨⟨hη_base i, u i, _, _, hu_theta i, fun d w ↦ ?_, fun l ↦ ?_, hu_L i⟩, rfl⟩
    -- `using!`: the exponential map `u i` matches `fibrePointMap A (η i)` only up to unfolding.
    · simpa [hu_e, he_smul, intAction] using!
        (fibrePointMap (E := E) A (η i)).map_smul d (e i ((x i).realEquiv w))
    · simpa [hu_e] using! congr(fibrePointMap (E := E) A (η i) $(hσ l i))

end New
end
end

/-!
# Existence of the universal theta family over a smooth projective base

`New.Variety.ThetaNull.nonempty_universalFamily` shows, when `R` is a localization of `𝓞 E` at a
submonoid of non-zero-divisors and every maximal ideal of `R` lies over a good prime for `D`
(`IsGoodOver D R`), that the type `New.Variety.UniversalFamily D R` of universal objects is
nonempty. A universal object is a family of theta-embedded abelian schemes for the PEL data `D`
(`New.ThetaFamily`) over a projective `R`-scheme that is smooth of relative dimension
`card D.Index - 1`. Its fibres at a dense set of complex points are the theta tori
(`New.ThetaTori.ThetaTorus`) of all analytic families (`New.Variety.AnalyticFamily`). Its
uniformisations are holomorphic in the parameter and in the fibre.

The base is the reduced closure of the theta coordinates of the level points in a product of
projective spaces. `New.Variety.exists_thetaFamily_of_points` puts a family on it, using good
reduction at the level points. Smoothness comes from the immersion of the balls and the tangent
bound.

Notions from other files:
* `New.ThetaObject.TorusModel`: a model of a fibre of the family on the complex torus of a polarised
  period map, with its uniformisation and its theta functions `θ`.
* `LineBundle.IsHomogeneousCoords L t v`: `v` are homogeneous coordinates of the point `t` for `L`:
  `t` lies in the chart `j` of `L` exactly when `v j` is a unit, and there the transition function
  to the chart `k` is `v k / v j`. For a linear system (`IsLinearSystem`), the transition functions
  are regular on the charts and give homogeneous coordinates.
* `ReducedClosure`: the reduced Zariski closure `W` of a family of tuples of complex points in a
  product of schemes, with its complex points `point a`, which are dense.
* `PEL.IsGoodAt D w`: the prime `w` of `𝓞 E` is good for the data `D`: it contains neither
  `D.paddedNorm` nor the order of `D.dualTorsion`, and it contains a prime number `p` and `D.β - b`
  for an integer `b` with `D.β - b` coprime to `star D.β - b`, and two further conditions hold
  (see its definition).

## Relation to the literature

Known result: Moduli of abelian varieties by theta values via theta-null embedding and universal
family. Here the base is the closure of the theta values at the level points of PEL tori, not a
locus cut out by quartic relations; the family on it comes from
`New.Variety.exists_thetaFamily_of_points`. Source: D. Mumford, On the equations defining abelian
varieties II, Invent. Math. 3 (1967) 75-135; theta groups in part I, Invent. Math. 1 (1966) 287-354.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing RingHom New ThetaObject Obj
  LineBundle ThetaTori Over ProjSpace FaithfulSMul Ideal IsPrime PeriodMap And

noncomputable section

namespace New.Variety.ThetaNull

/-- The datum `D` is good at every closed point of `Spec R`: for each maximal ideal `m` of the
`𝓞 E`-subalgebra `R` of `E`, the datum `D` is good at the contraction of `m` to `𝓞 E`. -/
def IsGoodOver {E : Type} [Field E] [CMBase E] (D : PEL E) (R : Subalgebra (𝓞 E) E) : Prop :=
  ∀ m : Ideal R, m.IsMaximal → D.IsGoodAt (m.comap (algebraMap (𝓞 E) R))

/-- If the maximal ideals of the `𝓞 E`-subalgebra `R` of `E` lie over good primes, then `β̄ - β`
and the order of `D.dualTorsion` are units of `R`. -/
lemma isUnit_star_sub_and_card_of_isGoodOver {E : Type} [Field E] [CMBase E] {D : PEL E}
    {R : Subalgebra (𝓞 E) E} (hR_good : IsGoodOver D R) :
    IsUnit (algebraMap (𝓞 E) R (star D.β - D.β)) ∧ IsUnit (Nat.card D.dualTorsion : R) := by
  -- Otherwise the product lies in a maximal ideal `m`, whose contraction `w` to `𝓞 E` is good.
  refine IsUnit.mul_iff.mp (by_contra fun h_nonunit ↦ ?_)
  obtain ⟨m, hm, h_mem⟩ := exists_max_ideal_of_mem_nonunits h_nonunit
  obtain ⟨⟨-, hT⟩, p, b, -, -, hβ, h_coprime, -⟩ := hR_good m hm
  -- As `#T ∉ w`, the factor `β̄ - β` is in `m`; adding `β - b` puts `β̄ - b` in `w`, against
  -- coprimality.
  have h_diff : algebraMap (𝓞 E) R (star D.β - D.β) ∈ m :=
    (hm.isPrime.mem_or_mem h_mem).resolve_right (hT)
  have h_conj : star D.β - b ∈ m.comap (algebraMap (𝓞 E) R) := by
    simpa using add_mem h_diff hβ
  exact notMem_of_isCoprime_of_mem h_coprime hβ h_conj

/-- The charts of the bundles `c l`, for `l` in `D.dualTorsion` seen inside the larger
`D.levelTorsion` that indexes the level points, cover the point `t` in the pattern of the largest
theta constants: for each `s` there is `o` such that `t` lands in the chart `k` of `c l` whenever
`l + k` is `o`, `-o` or `s - o`. -/
def HasPeakCharts {E : Type} [Field E] [CMBase E] {D : PEL E} {S : Scheme} {A : CommRingCat}
    (c : D.levelTorsion → LineBundle S D.dualTorsion) (t : Spec A ⟶ S) : Prop :=
  ∀ s : D.dualTorsion, ∃ o : D.dualTorsion, ∀ l k : D.dualTorsion,
    l + k ∈ [o, -o, s - o] → LandsIn t ((c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).opens k)

/-- The peak pattern at the closed point of an arc. Let `x` have good reduction for `v`, with
`v (#T) = 1`. Let `p ω` be the theta coordinates of the level point `ω` of `x`, taken at its lift
`x.torsionLift ω` to `V`, divided by the nonzero coordinate `i ω`, and let their residues be
homogeneous coordinates, for `c ω`, of the closed point of `α`. Then the charts of the `c ω` cover
that point in the pattern of the largest theta constants (`New.Variety.ThetaNull.HasPeakCharts`). -/
private lemma hasPeakCharts_of_hasGoodReduction {E V : Type} [Field E] [CMBase E]
    [FinComplexSpace V] {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ}
    (x : ThetaTorus D g ℓ V) {v : Valuation ℂ NNReal}
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
      (hvT : v (Nat.card D.dualTorsion) = 1) {S : Scheme}
    {α : Spec (.of v.valuationSubring) ⟶ S} {c : D.levelTorsion → LineBundle S D.dualTorsion}
    (i : D.levelTorsion → D.dualTorsion) (p : D.levelTorsion → D.dualTorsion → v.valuationSubring)
    (h_ne : ∀ ω : D.levelTorsion, x.thetaCoord (i ω) (x.torsionLift ω) ≠ 0)
    (hp : ∀ (ω : D.levelTorsion) (j : D.dualTorsion),
      (p ω j : ℂ) = x.thetaCoord j (x.torsionLift ω) / x.thetaCoord (i ω) (x.torsionLift ω))
    (h_red : ∀ ω : D.levelTorsion,
      (c ω).IsHomogeneousCoords (specMap (residue v.valuationSubring) ≫ α)
        fun j : D.dualTorsion ↦ residue v.valuationSubring (p ω j)) :
    HasPeakCharts c (specMap (residue v.valuationSubring) ≫ α) := by
  intro s
  -- The theta constants at `o`, `-o` and `s - o` have the largest valuation.
  obtain ⟨o, ho⟩ := x.exists_forall_valuation_thetaCoord_zero_le h_good hvT s
  refine ⟨o, fun l k hk ↦ ?_⟩
  set ω : D.levelTorsion := ⟨l, D.dualTorsion_le_levelTorsion l.property⟩
  -- Up to a factor `e` that does not depend on `j`, the coordinate `j` of the level point `ω = l`
  -- has the size of the theta constant at `l + j`: the shift formula, evaluated at `0`, under `v`.
  let e : ℂ := Complex.exp (-(x.automorphyForm (x.torsionLift ω) (x.torsionLift ω) / 2))
  have h_law (j : D.dualTorsion) :
      v e * v (x.thetaCoord j (x.torsionLift ω)) = v (x.thetaCoord (l + j) 0) := by
    simpa [e, ω, thetaShift, valuation_multiplier_mul_bicharacter_eq_one, PeriodMap.torsionLift]
      using
      congrArg (fun f ↦ v (f 0)) (x.thetaShift_thetaCoord (frameTorsionClass_ratLift l.val) j)
  -- Hence the coordinate `k` is at least as large as the coordinate `i ω`, so that their quotient
  -- `p ω k` is a unit of the valuation ring.
  have h_le :
      v (x.thetaCoord (i ω) (x.torsionLift ω)) ≤ v (x.thetaCoord k (x.torsionLift ω)) := by
    rw [← mul_le_mul_iff_right₀ (a := v e) (by simp [e, pos_iff_ne_zero]), h_law, h_law]
    exact ho (l + k) hk (l + i ω)
  refine (h_red ω k).left.mpr ?_
  simpa [v.mem_maximalIdeal_iff, hp, one_le_div₀, h_ne, pos_iff_ne_zero] using h_le

/-- Good reduction along an arc. Let `α` be a map to `S` from the spectrum of the valuation ring of
`v`, where `ρ : 𝓞 E → v.valuationSubring` agrees with the complex embedding `Φ v₀` of `E` and the
prime of `𝓞 E` below the maximal ideal is good for `D`. Let each bundle `c ω` be a linear system,
and let the theta coordinates of the level point `ω` of `x` be homogeneous coordinates of the
generic point of `α` for `c ω`. Then at the closed point of `α` the bundles `c` cut out some set `Z`
(`New.Variety.ThetaNull.IsCutOutAt`): in each chart, the ideal of `Z` is cut out by the affine
coordinates there, with ranks `thetaRanks`. Also, their charts cover that point in the pattern of
the largest theta constants (`New.Variety.ThetaNull.HasPeakCharts`): for each `s` some `o` puts it
in chart `k` of `c l` whenever `l + k` is `o`, `-o` or `s - o`. -/
lemma exists_isCutOutAt_and_hasPeakCharts {E V : Type} [Field E] [CMBase E] [FinComplexSpace V]
    {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V)
    {v : Valuation ℂ NNReal} {ρ : 𝓞 E →+* v.valuationSubring} (hρ : ∀ c : 𝓞 E, ρ c = Φ v₀ c.val)
    (h_goodAt : D.IsGoodAt (comap ρ (maximalIdeal v.valuationSubring))) {S : Scheme}
    {α : Spec (.of v.valuationSubring) ⟶ S} {c : D.levelTorsion → LineBundle S D.dualTorsion}
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ ω : D.levelTorsion, (c ω).IsHomogeneousCoords (specMap v.valuationSubring.subtype ≫ α)
      fun j : D.dualTorsion ↦ x.thetaCoord j (x.torsionLift ω)) :
    (∃ Z : Set (D.dualTorsion → ResidueField v.valuationSubring),
      IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm) c
        (specMap (residue v.valuationSubring) ≫ α) Z) ∧
    HasPeakCharts c (specMap (residue v.valuationSubring) ≫ α) := by
  -- Over the local ring each level point lies in one chart `i ω`. Its transition functions `p ω`
  -- are integral coordinates of the theta vector and reduce to coordinates of the closed point.
  obtain ⟨h_good, hvT⟩ := x.hasGoodReduction_and_val_card_eq_one hρ h_goodAt
  choose i hi using fun ω : D.levelTorsion ↦ (c ω).exists_landsIn α
  let p (ω : D.levelTorsion) (j : D.dualTorsion) : v.valuationSubring :=
    (c ω).transition (i ω) j (.of _) α
  -- the complex point of the arc lands in the chart `i ω`, so its coordinate `i ω` is a unit
  have h_ne (ω : D.levelTorsion) : x.thetaCoord (i ω) (x.torsionLift ω) ≠ 0 :=
    ((hx ω (i ω)).left.mp ((hi ω).comp _)).ne_zero
  have hp (ω : D.levelTorsion) (j : D.dualTorsion) :
      (p ω j : ℂ) = x.thetaCoord j (x.torsionLift ω) / x.thetaCoord (i ω) (x.torsionLift ω) := by
    -- `p ω j`, seen in `ℂ`, is the transition function at the complex point of the arc
    have h_value :
        (c ω).transition (i ω) j (.of ℂ) (specMap v.valuationSubring.subtype ≫ α) = (p ω j : ℂ) :=
      (hc ω).isRegularOn_transition (i ω) j (CommRingCat.ofHom v.valuationSubring.subtype) α (hi ω)
    simp [← h_value, (hx ω (i ω)).right j (h_ne ω).isUnit, div_eq_mul_inv]
  have h_red (ω : D.levelTorsion) :
      (c ω).IsHomogeneousCoords (specMap (residue v.valuationSubring) ≫ α)
        fun j ↦ residue v.valuationSubring (p ω j) := by
    -- at the closed point the transition functions are the residues of `p ω`
    have h_value (j : D.dualTorsion) : residue v.valuationSubring (p ω j) =
        (c ω).transition (i ω) j (.of _) (specMap (residue v.valuationSubring) ≫ α) :=
      ((hc ω).isRegularOn_transition (i ω) j (CommRingCat.ofHom (residue _)) α (hi ω)).symm
    rw [funext h_value]
    exact (hc ω).isHomogeneousCoords_transition ((hi ω).comp _)
  -- Any theta vector is made integral by dividing by a coordinate `m z` of largest valuation.
  have h_max (z : V) : ∃ m : D.dualTorsion, ∀ t : D.dualTorsion,
    v (x.thetaCoord t z) ≤ v (x.thetaCoord m z) :=
    Finite.exists_max _
  choose m hm using h_max
  -- otherwise every coordinate has valuation at most `v 0 = 0`, so the theta vector is zero
  have hm_ne (z : V) : x.thetaCoord (m z) z ≠ 0 := fun h_zero ↦
    x.thetaCoord_vector_ne_zero z (by simpa [h_zero, funext_iff] using hm z)
  let q (z : V) (j : D.dualTorsion) : v.valuationSubring :=
    ⟨x.thetaCoord j z / x.thetaCoord (m z) z, by simp [div_le_one_of_le₀, hm]⟩
  have hq (z : V) : IsIntegralCoords (fun t : D.dualTorsion ↦ x.thetaCoord t z) (q z) :=
    ⟨x.thetaCoord (m z) z, fun j ↦ rfl, m z, by simp [q, hm_ne]⟩
  have hp_integral (ω : D.levelTorsion) :
      IsIntegralCoords (fun t : D.dualTorsion ↦ x.thetaCoord t (x.torsionLift ω)) (p ω) :=
    ⟨x.thetaCoord (i ω) (x.torsionLift ω), hp ω, i ω, by simp [hp, h_ne]⟩
  exact ⟨⟨_, x.isCutOutAt_reduction residue_surjective h_good hq hp_integral h_red⟩,
    hasPeakCharts_of_hasGoodReduction x h_good hvT i p h_ne hp h_red⟩
variable {E : Type} [Field E] [CMBase E] {D : PEL E} {R : Subalgebra (𝓞 E) E}

/-- A parameter is an analytic family together with a point of the space containing its domain. -/
abbrev FamilyParameter (D : PEL E) : Type := AnalyticFamily D × BallBase D.Index

/-- The theta torus of the family `a.1` at the point `a.2`. -/
abbrev FamilyParameter.torus (a : FamilyParameter D) :
    ThetaTorus D a.1.frame (a.1.reflection a.2) (BallFibre E D.Index) :=
  a.1.torus a.2

/-- The theta coordinates of the level point `ω` of the theta torus at the parameter `a`. -/
abbrev FamilyParameter.levelCoords (a : FamilyParameter D) (ω : D.levelTorsion)
    (j : D.dualTorsion) : ℂ :=
  a.torus.thetaCoord j (a.torus.torsionLift ω)

/-- For a parameter `a` and a level point `ω`, some complex point `t` of projective space over `R`
lies over the complex point `specOver R ℂ` of `Spec R` and has the theta coordinates of `ω` at `a`
as homogeneous coordinates for the hyperplane bundle. -/
lemma exists_isHomogeneousCoords_levelCoords (R : Subalgebra (𝓞 E) E) (ω : D.levelTorsion)
    (a : FamilyParameter D) :
    ∃ t : Spec (.of ℂ) ⟶ ProjSpace D.dualTorsion ⨯ Spec (.of R), t ≫ prod.snd = (specOver R ℂ).hom ∧
      ((hyperplaneBundle D.dualTorsion).pull prod.fst).IsHomogeneousCoords t (a.levelCoords ω) := by
  obtain ⟨j, hj⟩ : ∃ j : D.dualTorsion, a.levelCoords ω j ≠ 0 :=
    Function.ne_iff.mp (a.torus.thetaCoord_vector_ne_zero _)
  exact exists_isHomogeneousCoords (specOver R ℂ).hom hj.isUnit

/-- The complex point of projective space over `R` whose homogeneous coordinates are the theta
coordinates of the level point `ω` at the parameter `a`. -/
def levelPoint (R : Subalgebra (𝓞 E) E) (ω : D.levelTorsion) (a : FamilyParameter D) :
    specOver R ℂ ⟶ Over.mk (prod.snd : ProjSpace D.dualTorsion ⨯ Spec (.of R) ⟶ Spec (.of R)) :=
  homMk (exists_isHomogeneousCoords_levelCoords R ω a).choose
    (exists_isHomogeneousCoords_levelCoords R ω a).choose_spec.1

/-- The theta coordinates of the level point `ω` at `a` are homogeneous coordinates of
`levelPoint R ω a`. -/
lemma isHomogeneousCoords_levelPoint (ω : D.levelTorsion) (a : FamilyParameter D) :
    ((hyperplaneBundle D.dualTorsion).pull prod.fst).IsHomogeneousCoords (levelPoint R ω a).left
      (a.levelCoords ω) :=
  (exists_isHomogeneousCoords_levelCoords R ω a).choose_spec.2

/-- The reduced closure, in a product of projective spaces over `R` indexed by the level torsion,
of the theta coordinates of the level points at the parameters `y b`. -/
abbrev ThetaClosure [Fintype D.levelTorsion] (R : Subalgebra (𝓞 E) E) {B : Type}
    (y : B → FamilyParameter D) : Type 1 :=
  ReducedClosure fun (ω : D.levelTorsion) (b : B) ↦ levelPoint R ω (y b)

namespace ThetaClosure

section AnyParameters

variable [Fintype D.levelTorsion] {B : Type} {y : B → FamilyParameter D} (C : ThetaClosure R y)

/-- The hyperplane bundle of the factor `ω`, pulled back to the closure. -/
abbrev coordBundle (ω : D.levelTorsion) : LineBundle C.scheme.left D.dualTorsion :=
  ((hyperplaneBundle D.dualTorsion).pull prod.fst).pull (C.proj ω).left

/-- The complex point of the closure at the parameter `y b`. -/
abbrev complexPoint (b : B) : Spec (.of ℂ) ⟶ C.scheme.left := (C.point b).left

/-- The structure map of the closure to `Spec (𝓞 E)`. -/
abbrev toIntegers : C.scheme.left ⟶ Spec (.of (𝓞 E)) := C.scheme.hom ≫ specMap (algebraMap (𝓞 E) R)

lemma isLinearSystem_coordBundle (ω : D.levelTorsion) : (C.coordBundle ω).IsLinearSystem :=
  (isLinearSystem_hyperplaneBundle.pull _).pull _

/-- The theta coordinates of the level point `ω` at the parameter `y b` are homogeneous
coordinates of the complex point at `b` for the bundle of the factor `ω`. -/
lemma isHomogeneousCoords_complexPoint (b : B) (ω : D.levelTorsion) :
    (C.coordBundle ω).IsHomogeneousCoords (C.complexPoint b) ((y b).levelCoords ω) := by
  -- The bundle is pulled back along the projection to the factor `ω`, which sends the point at `b`
  -- to `levelPoint R ω (y b)`.
  rw [IsHomogeneousCoords.pull_iff, ← comp_left, C.point_comp_proj]
  exact isHomogeneousCoords_levelPoint ω (y b)

/-- The morphism `C.scheme.hom` has a projective embedding, obtained via `C.incl` into a product of
projective spaces. -/
instance hasProjEmbedding : HasProjEmbedding C.scheme.hom :=
  HasProjEmbedding.of_isClosedImmersion_pi C.incl (h := fun _ ↦ ⟨isProjEmbedding_projSpace⟩)

/-- The product of the bundles `C.coordBundle ω` over all `ω` embeds the closure in projective
space over `R`. -/
lemma isProjEmbedding_pi_coordBundle : (pi C.coordBundle).IsProjEmbedding C.scheme.hom :=
  isProjEmbedding_pi C.proj (fun _ ↦ isProjEmbedding_projSpace) C.hom_ext

variable [IsNoetherianRing R] {κ : Type} [Finite κ] {j : κ → B}

/-- Let `R` be a noetherian `𝓞 E`-subalgebra of the CM field `E`, with the PEL data `D` good at its
maximal ideals. If finitely many points `j i` are dense in the closure `C`, then every point `z`
specialises to the centre of an arc through one of them, and the arc lies over a good prime. -/
lemma exists_arc_isGoodAt (hR_good : IsGoodOver D R)
    (h_dense : IsDenseFamily fun i : κ ↦ C.complexPoint (j i)) (z : C.scheme.left) :
    ∃ (i : κ) (v : Valuation ℂ NNReal) (α : Spec (.of v.valuationSubring) ⟶ C.scheme.left),
      specMap v.valuationSubring.subtype ≫ α = C.complexPoint (j i) ∧
      z ⤳ α (closedPoint v.valuationSubring) ∧
      D.IsGoodAt
        ((maximalIdeal v.valuationSubring).comap (Spec.preimage (α ≫ C.toIntegers)).hom) := by
  -- By properness `z` specialises to a point `w` over a maximal ideal `m` of `R`.
  have h_noeth : IsLocallyNoetherian C.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian C.scheme.hom
  obtain ⟨m, hm, hzm⟩ := (C.scheme.hom z).asIdeal.exists_le_maximal (C.scheme.hom z).isPrime.ne_top
  obtain ⟨w, hzw, hw⟩ : ∃ w : C.scheme.left, z ⤳ w ∧ C.scheme.hom w = ⟨m, hm.isPrime⟩ :=
    C.scheme.hom.isClosedMap.specializingMap
      ((PrimeSpectrum.le_iff_specializes _ ⟨m, hm.isPrime⟩).mp hzm)
  -- An arc from one of the dense complex points `j i` has `w` as its closed point.
  obtain ⟨i, v, α, hα, rfl⟩ := exists_valuative_arc_of_isDenseFamily _ h_dense w
  refine ⟨i, v, α, hα, hzw, ?_⟩
  -- The ideal in question is the prime of `𝓞 E` below `m`.
  have h_ideal :
      (maximalIdeal v.valuationSubring).comap (Spec.preimage (α ≫ C.toIntegers)).hom =
        (C.scheme.hom (α (closedPoint v.valuationSubring))).asIdeal.comap (algebraMap (𝓞 E) R) :=
    congrArg (fun f ↦ (f (closedPoint _)).asIdeal) (Spec.map_preimage (α ≫ C.toIntegers))
  rw [h_ideal, hw]
  exact hR_good m hm

/-- The family `X` over the closure has the theta tori as fibres: at each point `b` there is a model
of the fibre on the torus at `y b` whose theta coordinates are those of the torus. -/
def HasThetaFibres (X : ThetaFamily D C.scheme.left C.toIntegers) : Prop :=
  ∀ b : B, X.IsModelledOn (C.complexPoint b) (y b).torus

/-- Let `R` be a noetherian `𝓞 E`-subalgebra of the CM field `E`, the localisation of `𝓞 E` at `M`,
with the PEL data `D` good at its maximal ideals. Let `C` be the reduced closure, in a product over
the level torsion of projective spaces over `R`, of the theta coordinates of the level points at the
parameters `y b`. If the complex points of `C` at finitely many parameters `y (j i)` are dense, then
there is a theta family `X` over `C` (via its structure map to `Spec 𝓞 E`) such that for every `b`
the fibre at the complex point `b` has a model on the theta torus at `y b` with the same theta
coordinates. -/
lemma exists_hasThetaFibres (M : Submonoid (𝓞 E)) [IsLocalization M R] (hR_good : IsGoodOver D R)
    (h_dense : IsDenseFamily fun i : κ ↦ C.complexPoint (j i)) :
    ∃ X : ThetaFamily D C.scheme.left C.toIntegers, C.HasThetaFibres X := by
  -- Apply `exists_thetaFamily_of_points`, using good reduction along the arcs `α z`, whose closed
  -- points are `t z`.
  have h_noeth : IsLocallyNoetherian C.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian C.scheme.hom
  have h_base (b : B) (c : 𝓞 E) :
      (Spec.preimage (C.complexPoint b ≫ C.toIntegers)).hom c = Φ v₀ c.val := by
    -- after unfolding, both sides are the embedding of `𝓞 E` in `ℂ` through `R`
    simp [complexPoint, toIntegers]
    rfl
  choose i v α hα h_spec h_good using C.exists_arc_isGoodAt hR_good h_dense
  let t (z : C.scheme.left) : Spec (.of (ResidueField (v z).valuationSubring)) ⟶ C.scheme.left :=
    specMap (residue (v z).valuationSubring) ≫ α z
  have h_red (z : C.scheme.left) :
      (∃ Z, IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm)
        C.coordBundle (t z) Z) ∧
        HasPeakCharts C.coordBundle (t z) := by
    refine exists_isCutOutAt_and_hasPeakCharts (y (j (i z))).torus ?_ (h_good z)
      C.isLinearSystem_coordBundle ?_
    · simpa [← hα z] using h_base (j (i z))
    · simpa only [hα z] using C.isHomogeneousCoords_complexPoint (j (i z))
  have h_closed (z : C.scheme.left) :
      z ⤳ t z (closedPoint (ResidueField (v z).valuationSubring)) := by
    have h_spec_z : z ⤳ α z (closedPoint (v z).valuationSubring) := h_spec z
    rwa [← comap_closedPoint (residue _)] at h_spec_z
  obtain ⟨hβ_unit, hT_unit⟩ := isUnit_star_sub_and_card_of_isGoodOver hR_good
  refine exists_thetaFamily_of_points j h_dense
    (IsPreimmersion.of_isLocalization M).instMonoScheme h_base C.isLinearSystem_coordBundle
    C.isProjEmbedding_pi_coordBundle C.isHomogeneousCoords_complexPoint hβ_unit hT_unit
    (fun z ↦ ⟨_, inferInstance, inferInstance, t z, h_closed z, (h_red z).left⟩) fun z s ↦ ?_
  -- A chart is open, so it holds `z` once it holds the closed point of the arc.
  obtain ⟨o, ho⟩ : ∃ o : D.dualTorsion, ∀ l k : D.dualTorsion, l + k ∈ [o, -o, s - o] →
      LandsIn (t z) ((C.coordBundle ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).opens k) :=
    (h_red z).right s
  have h_index (a : D.dualTorsion) (ha : a ∈ [o, -o, s - o]) :
    IsNonvanishingIndex C.coordBundle z a :=
    fun l k hk ↦ (h_closed z).mem_open (LineBundle.opens ..).isOpen
      (landsIn_iff_mem.mp (ho l k (by rwa [hk])))
  exact ⟨o, h_index o (by simp), h_index (-o) (by simp), h_index (s - o) (by simp)⟩

end AnyParameters

variable [Fintype D.levelTorsion] (C : ThetaClosure R (id : FamilyParameter D → FamilyParameter D))

/-- In an analytic family `F` the point of the closure depends holomorphically on the parameter. -/
lemma holomorphicAt_complexPoint {F : AnalyticFamily D} ⦃b : BallBase D.Index⦄ (hb : b ∈ F.domain) :
    HolomorphicAt (fun b' : BallBase D.Index ↦ C.complexPoint (F, b')) b := by
  -- After scaling by `u b' ≠ 0` the theta coordinates are analytic in `b'`.
  obtain ⟨u, hu, hu_ne⟩ := F.exists_analytic_thetaCoord hb
  -- The coordinates of the point at `b'` in the product of the bundles are the products over `ω`
  -- of the scaled theta coordinates of the level points `ω`.
  let coords (b' : BallBase D.Index) (k : D.levelTorsion → D.dualTorsion) : ℂ :=
    ∏ ω : D.levelTorsion, (u b' • FamilyParameter.levelCoords (F, b') ω) (k ω)
  have h_analytic (k : D.levelTorsion → D.dualTorsion) : AnalyticAt ℂ (fun b' ↦ coords b' k) b :=
    Finset.analyticAt_fun_prod _ fun ω _ ↦
      (hu ..).comp₂ analyticAt_id (F.analyticAt _ hb (toRealVectors (ratLift F.frame ω.val)))
  refine .of_isHomogeneousCoords C.isProjEmbedding_pi_coordBundle h_analytic
    (hu_ne.mono fun b' h_unit ↦ ?_) fun _ ↦ Over.w _
  exact .pi (w := (·)) fun ω ↦ (C.isHomogeneousCoords_complexPoint (F, b') ω).smul h_unit

/-- Let `m a` be a model of the fibre of `X` at the parameter `a` on the theta torus at `a`, whose
theta functions `(m a).θ` are those of the torus (`hθ`). Then for a point `b` of the domain of an
analytic family `F`, the uniformisations `(m (F, b')).uniformisation` of the fibres, followed by the
maps to the total space, are holomorphic in the parameter `b'` and the fibre variable together. -/
lemma holomorphicAt_uniformisation {X : ThetaFamily D C.scheme.left C.toIntegers}
    (m : ∀ a : FamilyParameter D, TorusModel (X := X) (C.complexPoint a) a.torus.toPeriodMap)
    (hθ : ∀ a : FamilyParameter D,
      (m a).θ = fun (z : BallFibre E D.Index) (μ : D.dualTorsion) ↦ a.torus.thetaCoord μ z)
    (F : AnalyticFamily D) (b : BallBase D.Index) (hb : b ∈ F.domain) (z : BallFibre E D.Index) :
    HolomorphicAt (fun q : BallBase D.Index × BallFibre E D.Index ↦
      atGeneric (m (F, q.1)).uniformisation.expMap q.2 ≫
        (ThetaObject.toFamily (X := X) (C.complexPoint (F, q.1))).left) (b, z) := by
  -- Both the theta coordinates on the fibre and the coordinates of the base point are holomorphic.
  obtain ⟨u, hu, hu_ne⟩ := F.exists_analytic_thetaCoord hb
  obtain ⟨q, hq, hq_lifts⟩ := (C.holomorphicAt_complexPoint hb).exists_isHomogeneousCoords
    C.isProjEmbedding_pi_coordBundle.isLinearSystem
  refine .of_isHomogeneousCoords (b := (specOver R ℂ).hom)
    (X.embeds.mul C.isProjEmbedding_pi_coordBundle)
    (fun _ ↦ (hu ..).mul ((hq _).comp analyticAt_fst))
    (((hq_lifts.and hu_ne).prod_inl_nhds _).mono fun w ⟨h_base, h_unit⟩ ↦ .mul ?_ ?_)
    fun _ ↦ by simp [complexPoint]
  · -- the bundle of a fibre is `X.lineBundle` pulled back along the map of the fibre to the total
    -- space
    simpa [hθ, lineBundle, IsHomogeneousCoords.pull_iff] using
      ((m _).hasThetaCoords.hasFieldCoords _).smul h_unit
  · simpa [IsHomogeneousCoords.pull_iff] using h_base

variable [IsDedekindDomain R] (M : Submonoid (𝓞 E)) [IsLocalization M R]

include M in
/-- Let `R` be a Dedekind domain, the localisation of `𝓞 E` at `M`, with `D` good at its maximal
ideals. Parameters `x = (F, b)` and `x'` whose moduli points `F.ballPoint 0 (b, 0)` are isomorphic
at level `D.level` (by `z`, which lies in the level group `levelGU D.Index D.level` and matches
their reflections) have the same point in the closure. -/
lemma point_eq_of_isLevelIso (hR_good : IsGoodOver D R) {x x' : FamilyParameter D}
    {z : GL D.Index E}
    (h_iso : (x.fst.ballPoint 0 (x.snd, 0) : ModuliPoint E D.Index 0).IsLevelIso
      (levelGU D.Index D.level) z (x'.fst.ballPoint 0 (x'.snd, 0))) :
    C.point x = C.point x' := by
  -- Compare the models of the two fibres in the family over the closure of these two parameters.
  obtain ⟨C'⟩ : Nonempty (ThetaClosure R ![x, x']) := inferInstance
  obtain ⟨X, hX⟩ := C'.exists_hasThetaFibres (j := id) M hR_good C'.isSeparatingFamily.right
  choose m _ using hX
  have h_eq : C'.point 0 = C'.point 1 := by
    -- `h_pt`: by the level isomorphism, the models `m 0` and `m 1` give the same point of the
    -- fibre power.
    have h_pt : pointOf _ _ = pointOf _ _ :=
      (ThetaFamily.IsPointOf.eq_iff (𝔪 := 1) ⟨m 0, rfl⟩ ⟨m 1, rfl⟩).mpr
        ⟨z, levelGU_inf_one.ge h_iso.mem_level, h_iso.reflection_eq, h_iso.sub_mem_lattice⟩
    -- The two points are the images in the base of one point of the fibre power.
    have h_base : C'.complexPoint 0 = C'.complexPoint 1 := by
      simpa only [pointOf_hom] using h_pt =≫ Over.hom _
    exact OverMorphism.ext h_base
  -- `C` and `C'` have the same factors, and the points of `C` are determined by their projections
  have h_proj (ω : D.levelTorsion) : C.point x ≫ C.proj ω = C.point x' ≫ C.proj ω := by
    simpa using h_eq =≫ C'.proj ω
  exact C.hom_ext h_proj

/-- The point `b` of the domain of `F` is generic: the point of the closure at `b` specialises to
the points at all parameters in the domain of `F`. -/
def IsGenericParameter (F : AnalyticFamily D) (b : BallBase D.Index) : Prop :=
  b ∈ F.domain ∧
    ∀ b' ∈ F.domain, C.complexPoint (F, b) (closedPoint ℂ) ⤳ C.complexPoint (F, b') (closedPoint ℂ)

include M in
/-- The generic points of finitely many analytic families are dense in the closure. -/
lemma exists_finite_isDenseFamily (hR_good : IsGoodOver D R) :
    ∃ (ι : Type) (_ : Finite ι) (a : ι → FamilyParameter D),
      (∀ i : ι, C.IsGenericParameter (a i).fst (a i).snd) ∧
      IsDenseFamily fun i : ι ↦ C.complexPoint (a i) := by
  -- Every moduli point is isomorphic at level `D.level` to a point of one of finitely many
  -- families.
  obtain ⟨ι, f, hι, h_rep⟩ := ModuliPoint.exists_finite_analyticFamily_isLevelIso D 0
    D.level_ne_zero
  choose b hb h_generic using fun i : ι ↦ exists_generic_member C.scheme.hom (f i).domain.isOpen
    (f i).isConnected C.holomorphicAt_complexPoint
  refine ⟨ι, hι, fun i ↦ (f i, b i), fun i ↦ ⟨hb i, h_generic i⟩, fun p ↦ ?_⟩
  refine C.isSeparatingFamily.right.induction_on p isClosed_closure fun x ↦ ?_
  obtain ⟨i, a, ha, z, h_iso⟩ := h_rep (x.fst.ballPoint 0 (x.snd, 0))
  have h_pt : C.point x = C.point (f i, a.1) :=
    C.point_eq_of_isLevelIso M hR_good (z := z) ⟨h_iso.mem_level, h_iso.reflection_eq, nofun⟩
  simpa [h_pt] using closure_mono (by simp) (h_generic i _ ha.1).mem_closure

/-- Let `X` have the theta tori as fibres and `a` be a generic parameter. Let `α` be an arc whose
generic point is the complex point at `a` and whose closed point lies over a prime good for `D`.
Then some open `U` through which `α` factors is smooth of relative dimension `card D.Index - 1`
over `Spec R`. -/
lemma exists_smooth_near_arc {X : ThetaFamily D C.scheme.left C.toIntegers}
    (hX : C.HasThetaFibres X)
    {a : FamilyParameter D} (ha : C.IsGenericParameter a.fst a.snd) {v : Valuation ℂ NNReal}
    {α : Spec (.of v.valuationSubring) ⟶ C.scheme.left}
    (hα : specMap v.valuationSubring.subtype ≫ α = C.complexPoint a)
    (h_good : D.IsGoodAt
      ((maximalIdeal v.valuationSubring).comap (Spec.preimage (α ≫ C.toIntegers)).hom)) :
    ∃ U : C.scheme.left.Opens, LandsIn α U ∧
      SmoothOfRelativeDimension (Fintype.card D.Index - 1) (U.ι ≫ C.scheme.hom) := by
  -- The family is an immersion at the generic point, and `card D.Index - 1` bounds the dimension
  -- of the tangent space at the closed point.
  obtain ⟨F, b⟩ := a
  obtain ⟨hb, h_generic⟩ := ha
  choose m hθ using hX
  have h_imm : IsHolomorphicImmersionAt (fun b' : BallBase D.Index ↦ C.complexPoint (F, b')) b :=
    F.isHolomorphicImmersionAt_of_holomorphicAt (fun b' ↦ m (F, b')) hb
      (C.holomorphicAt_uniformisation m hθ F b hb)
  -- near `b`, the points along `F` are specialisations of the point at `b` (`h_generic`)
  refine exists_landsIn_smoothOfRelativeDimension (ϑ := residue _) C.scheme.hom h_imm hα
    (fun _ ↦ Over.w _)
    (algebraMap_injective ..) ((F.domain.isOpen.eventually_mem hb).mono h_generic)
    fun _ τ h_reduction h_over ↦ ?_
  -- The model of the generic fibre extends along the arc, so
  -- `finrank_tangent_le_card_index_sub_one` applies.
  obtain ⟨m', -⟩ := (m (F, b)).exists_torusModel_of_isPullbackAlong hα
  refine finrank_tangent_le_card_index_sub_one h_reduction ?_ m'.fullStructure
    (m'.hasSpanningCoords_of_specMap_comp_eq (residue _) rfl) rfl ?_
  · simpa [← comap_ker, ker_residue, ThetaObject.baseHom] using h_good
  · simp [ThetaObject.baseHom, toIntegers, reassoc_of% h_over, comp_assoc]

end ThetaClosure

/-- Existence of the universal family. Let `R` be the localisation of `𝓞 E` at a submonoid of
non-zero-divisors, and let `D` be good (`New.PEL.IsGoodAt`) at the contraction to `𝓞 E` of every
maximal ideal of `R`. Then there is a theta family (an abelian scheme with `𝓞 E`-action, a line
bundle with point-separating coordinates and level points) over an `R`-scheme `S`, projective and
smooth of relative dimension `card D.Index - 1`. It comes with a dense set of complex points indexed
by pairs of an analytic family of tori `f` and a parameter `b`, at which the fibres are uniformised
by the tori, holomorphically in `b` on the domain of `f`. -/
theorem nonempty_universalFamily {M : Submonoid (𝓞 E)} [IsLocalization M R]
    (hM_le : M ≤ nonZeroDivisors (𝓞 E)) (hR_good : IsGoodOver D R) :
    Nonempty (UniversalFamily D R) := by
  -- The base is the closure `C` of the theta coordinates of the level points at all parameters.
  -- Finitely many generic points are dense in it, so it carries a family `X`. It is smooth near
  -- each of the arcs `α z`, and these neighbourhoods cover it.
  have : Finite D.levelTorsion := finite_torsionBy ⟨_, by simp [D.level_ne_zero]⟩
  let := Fintype.ofFinite D.levelTorsion
  have := IsLocalization.isDedekindDomain (𝓞 E) hM_le R
  obtain ⟨C⟩ : Nonempty (ThetaClosure (D := D) R id) := inferInstance
  obtain ⟨ι, hι, a, h_generic, h_dense⟩ := C.exists_finite_isDenseFamily M hR_good
  obtain ⟨X, hX⟩ := C.exists_hasThetaFibres M hR_good h_dense
  choose i v α hα h_spec h_good using C.exists_arc_isGoodAt hR_good h_dense
  choose U hU hU_smooth using fun z ↦
    C.exists_smooth_near_arc hX (h_generic (i z)) (hα z) (h_good z)
  choose m hθ using hX
  exact ⟨{
    isDedekindDomain := inferInstance, base := C.scheme, family := X
    hasProjEmbedding := C.hasProjEmbedding, obj := C.point, model := m
    holomorphic := C.holomorphicAt_uniformisation m hθ, dense := C.isSeparatingFamily.right
    smooth := HasRingHomProperty.instIsZariskiLocalAtSource.of_iSup_eq_top U
      (top_unique fun z _ ↦ le_iSup U z ((h_spec z).mem_open (U z).isOpen (hU z ⟨⟩)))
      hU_smooth }⟩

end New.Variety.ThetaNull

end
