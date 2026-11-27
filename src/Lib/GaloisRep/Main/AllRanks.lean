module

import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
public import Lib.ClassField.Avatar.HeckeBaseChange
public import Lib.SiegelWeil.RallisInner.Doubling
import Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic
import Lib.PadicComparison.Descent.TestCategory
import Lib.Shimura.Uniformisation.HolomorphicFamilies
import Lib.SiegelWeil.RallisInner.SharpData
import Lib.Weil.CompactLift.DefiniteThetaLift
import Lib.Weil.Unramified.HeckeTransfer
import Mathlib.Algebra.Order.Star.Int
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.Analysis.Normed.Ring.CompactMonoid
public import Lib.GaloisRep.Main.AttachedRepresentations
public import Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations
import Lib.Adelic.AutomorphicForms.HeckeEigenforms
import Lib.ClassField.Avatar.LocalGlobalCompatibility
import Lib.GaloisRep.Main.OddRank
import Lib.GaloisRep.Main.QuadraticStep
import Lib.General.LinearAlgebra.Eigenvalues
import Lib.General.NumberTheory.FrobeniusOrbits
import Lib.PadicHodge.Limit.TraceLimit

section
/-!
# Theta lift of an algebraic form to a larger definite unitary group and its Hecke polynomials

This file constructs the theta lift from the definite unitary group of rank n to that of rank n + s.
The lift is used to separate the Galois representation of a form from those of its lifts. The file
also records how the monic and the reciprocal normalisations of the Hecke polynomial are related.

## Main definitions and results

* `New.exists_theta_lift_heckePoly`: the theta lift of a nonzero form is a nonzero form whose Hecke
  polynomial at split places is the twisted old one times a string of linear factors.

Notions from other files:
* `New.AutChar.HasWeight`: `b.HasWeight c 1` says that `b u = ∏_v u_v ^ c v` whenever `u` has
  integral finite part.
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄.

## Relation to the literature

Known result: Theta lift to larger rank, the step that reduces even rank to odd rank. Here a
non-zero theta lift in the convergent range from definite U(n) to U(n+s), with s > n, replaces
endoscopic transfer. It keeps spherical places, and its Hecke polynomials are twisted and gain the
string of a character of U(1). Source: Blasius, Rogawski, Motives for Hilbert modular forms, Invent.
Math. 114 (1993) and Shin, Ann. of Math. 173 (2011) for the idea (endoscopic transfer to odd rank);
Harris, Soudry, Taylor, Invent. Math. 112 (1993) for theta lifts with a varying character.
-/

@[expose] public section

/-!
## The monic Hecke polynomial and the reciprocal one

The two normalisations of the Hecke polynomial at a place `w` agree: `New.heckePoly` (monic of
degree `n` if `t 0 = 1`) at `x ≠ 0` is `x ^ n` times the reciprocal one, `New.heckePolyEval`, at
`x⁻¹`.
-/

/-- At `x ≠ 0` the monic Hecke polynomial at the place `w`, with coefficients built from `t`, is
`x ^ n` times the reciprocal one, `heckePolyEval`, at `x⁻¹`, where `n = card n`:
`∑ (-1)^j q^(j choose 2) t j x^(n - j) = x^n ∑ (-x⁻¹)^j q^(j choose 2) t j`, with `q` the norm of
`w` and `j` running from `0` to `n`. -/
lemma New.eval_heckePoly {E n : Type*} [Field E] [NumberField E] [Fintype n] (w : FinPlace E)
    (t : ℕ → ℂ) {x : ℂ} (hx_ne : x ≠ 0) :
    (heckePoly w.q (Fintype.card n) t).eval x = x ^ Fintype.card n * heckePolyEval n w t x⁻¹ := by
  -- Term by term, `x ^ (n - j) = x ^ n * x⁻¹ ^ j` for `j ≤ n`.
  rw [heckePoly, heckePolyEval, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  simp [pow_sub₀ x hx_ne (Finset.mem_range_succ_iff.mp hj), neg_pow x⁻¹]
  ring

/-!
## Theta lift to a larger definite group and Hecke polynomials

`New.stdSpace E n` is the sum of `n` norm forms. `New.AlgForm n κ e` and `New.Space.forms` are
smooth algebraic forms of a given weight. `New.maxCompactAt n w` is the maximal compact subgroup at
`w` and `w̄`. `New.HasHeckePolyAt f w hw P` says that `f` is a spherical Hecke eigenform at the
split place `w` with Hecke polynomial `P`. For a character `b` of `U(1)`, `hb.toAlgebraic k j`
(`New.AutChar.HasWeight.toAlgebraic`) is the algebraic Hecke character
`b (x / x̄) υ ^ (-k) |x| ^ (j - k / 2)`. `New.heckeCoeff ψ ∅ w` is `ψ` at a uniformiser.
-/

namespace New

open NumberField Space SiegelWeil Fintype

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]

open Matrix Algebra Valued G Gf Polynomial AutChar Set Filter

/-- Let `x` be an integral matrix with `xᴴ * x = 0`, let `B` be a finite set of places with
`stdLevel E n ⊓ trivialOn n B ≤ H`, and let `N ≠ 0` have its principal level inside `H`. Let
`z = N⁻¹ • idem B'`, with `B'` the closure of `B` under conjugation, and let `b` be a character
of `U(1)` of weight `c`. Then an integral `g` such that `z * D i j` is integral for
`D = g⁻¹ - 1` lies in `H` and fixes, under the Weil representation, the vacuum translated by
`z • x`. -/
private lemma mem_inf_stabilizer_of_integral {m : Type} [Fintype m] [DecidableEq m]
    {H : Subgroup (Gf E n)} {b : AutChar E} {c : InfinitePlace E → ℤ} (hb : b.HasWeight c 1)
    {x : Matrix m n (𝔸f E)} (hx_int : ∀ (i : m) (j : n), x i j ∈ Ô E) (hx_iso : xᴴ * x = 0)
    {B : Finset (FinPlace E)} (hB_off : stdLevel E n ⊓ trivialOn n (B : Set (FinPlace E)) ≤ H)
    {N : ℕ} (hN : N ≠ 0) (hN_cong : (principalLevel n (N : 𝓞 E) : Set (Gf E n)) ⊆ H.carrier)
    (z : 𝔸f E) (hz : z = (N : E)⁻¹ • idem (SetLike.coe B).conjClosure)
    {g : Gf E n} {D : Matrix n n (𝔸f E)} (hD : (g.val.val)⁻¹ = D + 1) (hg : g ∈ stdLevel E n)
    (hzD : ∀ i j : n, z * D i j ∈ Ô E) :
    g ∈ H ⊓ (MulAction.stabilizer _
      (finHeisenbergOp ((stdSpace E n).hom (stdSpace E m)) (matrixToVec (z • x))
        (vacElem ((stdSpace E n).hom (stdSpace E m))) :
        𝒮 ((stdSpace E n).hom (stdSpace E m)))).comap
        ((pairWeil (stdSpace E n) (stdSpace E m) 1 b).comp
          (.prod (.inr (GInf E 1) (Gf E n)) 1)).toHomUnits := by
  constructor
  · -- The part of `g⁻¹` above `B` is congruent to `1` modulo `N`; it cancels that of `g`.
    have h_cut : componentOn n B g⁻¹ ∈ H := by
      refine hN_cong ⟨componentOn_mem_stdLevel (inv_mem hg), fun i j ↦ ⟨z * D i j, hzD i j, ?_⟩⟩
      -- `N` acts on the adeles through `E`; in that form `simp` computes the entry.
      change _ = (N : E) • (z * D i j)
      simp [hz, hN, hD, componentOn, U.cutAt, cutGL, sub_smul]
    refine (mul_mem_cancel_left h_cut).mp (hB_off ?_)
    simp_all [componentOn_mem_stdLevel, mul_mem]
  · -- `g` moves the translation by the integral `x * z • D`, with trivial phase as `xᴴ * x = 0`.
    have h_vac : finHeisenbergOp ((stdSpace E n).hom (stdSpace E m)) (matrixToVec (x * z • D))
        (vacElem _) = vacElem _ :=
      finHeisenbergOp_vacElem fun _ ↦ sum_mem (by simp [hx_int, hzD, mul_mem])
    refine (pairWeil_apply ..).trans (.trans ?_
      (congrArg (finHeisenbergOp _ (matrixToVec (z • x))) h_vac))
    -- The point `g` of the product group is `((1, g), 1, 1)`.
    have h_pt : ((MonoidHom.inr (GInf E (1 : n → ℤˣ)) (Gf E n)).prod 1) g =
        (((1, g), 1, 1) : G E (1 : n → ℤˣ) × G E (1 : m → ℤˣ)) := rfl
    -- The finite part of `onHom` acts on the translation as a Kronecker product (`G.onHom_snd`).
    rw [omega_finHeisenbergOp, ← map_smul, G.onHom_snd, kronecker_mulVec_eq_matrixToVec,
      vecToMatrix_matrixToVec,
      ← pairWeil_apply, h_pt, pairWeil_eq_smul_of_projOn_eq ⊤]
    · simp [hb.apply_det_eq_one, hg, hD, hx_iso, x.mul_add, Dᴴ.mul_assoc, add_comm,
        finHeisenbergOp_finHeisenbergOp]
    -- the three side conditions of `pairWeil_eq_smul_of_projOn_eq`
    all_goals simp [hg]

omit [WeilData E] in
/-- Let `z` be a finite adele, let `g` be integral at every place where `z` is integral (the places
off `{w | 1 < v (z w)}`), and let `D = g⁻¹ - 1`. If for an integral matrix `u` every entry
`z * D p j + ∑ k, u p k * D k j` is integral, then every entry of `D` is integral: at a place `w`,
a largest entry of a column of `D` that is not integral would force `z` to be integral at `w`. -/
private lemma mem_Ô_of_mul_add_sum_mem_Ô {z : 𝔸f E} {g : Gf E n}
    (hg : g ∈ localLevel n {w : FinPlace E | 1 < v (z w)}ᶜ) {D : Matrix n n (𝔸f E)}
    (hD_def : D = g⁻¹.val.val - 1) {u : n → n → 𝔸f E} (hu : ∀ p k : n, u p k ∈ Ô E)
    (h_int : ∀ p j : n, z * D p j + ∑ k : n, u p k * D k j ∈ Ô E) (i j : n) : D i j ∈ Ô E := by
  refine mem_Ô.mpr fun w ↦ ?_
  have : Nonempty n := ⟨i⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun i' : n ↦ v (D i' j w)
  refine (hp i).trans (le_of_not_gt fun h_big ↦ h_big.not_ge <| hD_def ▸ v.map_sub_le
    ((hg w ?_).isIntMatrix_inv p j) (mem_Ô.mp (by simp [Matrix.one_apply, ite_mem]) w))
  -- `O` is the set of adeles whose valuation at `w` is at most that of `D p j`.
  let O : AddSubgroup (𝔸f E) := (v.comap (evalAt w)).leAddSubgroup (v (D p j w))
  simpa [O, h_big.pos] using (O.add_mem_cancel_right (show ∑ k : n, u p k * D k j ∈ O from
    sum_mem fun k _ ↦ by simp [O, mul_le_of_le_one_of_le, mem_Ô.mp, hu, hp])).mp
    ((mem_Ô.mp (h_int p j) w).trans h_big.le)

/-- Let the row `ρ p` of `x` be the unit vector at `p`, let `g` be integral at every place where
the finite adele `z` is integral, and let `D = g⁻¹ - 1`. Unless `g` is integral with every
entry `z * D i j` integral, the Weil matrix coefficient at `g` of `F`, the vacuum translated by
`z • x`, is `0`. -/
private lemma weilMatrixCoeff_finHeisenbergOp_eq_zero {m : Type} [Fintype m] [DecidableEq m]
    {b : AutChar E} {x : Matrix m n (𝔸f E)} {ρ : n ↪ m} (hρ : ∀ i : n, x (ρ i) = Pi.single i 1)
    {z : 𝔸f E} {g : Gf E n} (hg : g ∈ localLevel n {w : FinPlace E | 1 < v (z w)}ᶜ)
    {F : 𝒮 ((stdSpace E n).hom (stdSpace E m))}
    (hF_def : F = finHeisenbergOp ((stdSpace E n).hom (stdSpace E m)) (matrixToVec (z • x))
      (vacElem ((stdSpace E n).hom (stdSpace E m))))
    {D : Matrix n n (𝔸f E)} (hD_def : D = g⁻¹.val.val - 1)
    (hg_not : ¬(g ∈ stdLevel E n ∧ ∀ i j : n, z * D i j ∈ Ô E)) :
    weilMatrixCoeff b F F g = 0 := by
  -- The coefficient at `g` is an average over integral `u` of terms that vanish unless
  -- `z • x * (g⁻¹ - 1) + u * g⁻¹` is integral, and that forces `g` and `z • D` to be integral.
  subst hF_def
  have hD : (g.val.val)⁻¹ = D + 1 := by simp [hD_def]
  -- Write `ω(g) vacElem` through the projection on vacua (`omega_vacElem`) and translate both
  -- vectors by `-z • x`, so that the left one is the vacuum.
  -- The point of the product group is `((1, g), 1, 1)`, the form that `onHom_fin` takes.
  have h_pt : (((1, g), 1) : G E (1 : n → ℤˣ) × G E (1 : m → ℤˣ)) = ((1, g), 1, 1) := rfl
  rw [weilMatrixCoeff, pairWeil_apply, h_pt, onHom_fin, omega_finHeisenbergOp, omega_vacElem,
    ← dataInner_finHeisenbergOp _ (-matrixToVec (z • x))]
  simp [finHeisenbergOp_finHeisenbergOp, mulVec_smul]
  -- `simp` leaves a product of scalars and an inner product; it is enough that the last vanishes:
  -- the inner product of the vacuum with a translate of `ω(g) P ω(g⁻¹)` of the vacuum.
  refine .inr (.inr (.inr ?_))
  change dataInner _ (vacElem _)
      (finHeisenbergOp _ (-(z • matrixToVec x) + _) (ω _ _ (projOn _ univ (ω _ _ (vacElem _))))) = 0
  -- The inner projection is a mean over integral `u`, so it is enough that each term vanishes
  -- (`map_projOn_eq_const`). The projection that fixes the left vacuum, moved to the right, kills
  -- translates of the vacuum by vectors that are not integral.
  rw [← projOn_vacElem (S := ⊤), dataInner_projOn]
  -- The three operators applied in turn are one composite `L`, the form of `map_projOn_eq_const`.
  rw [← ContinuousLinearMap.comp_apply (finHeisenbergOp _ _),
    ← ContinuousLinearMap.comp_apply (projOn _ ⊤),
    map_projOn_eq_const _ (projOn _ ⊤ ∘L finHeisenbergOp _ _ ∘L _) (c := 0), map_zero]
  simp [rep_apply_apply, stdLattice.mem_stdLattice, onHom_snd, Prod.mk_one_one,
    finHeisenbergOp_finHeisenbergOp, matrixToVec, projOn_finHeisenbergOp, mem_integralBox,
    Set.conjClosure, idem_univ]
  change ∀ u : m × n → 𝔸f E, (∀ (a : m) (b : n), u (a, b) ∈ Ô E) →
    (∀ (a : m) (b : n),
      -(z * x a b) +
          z * (kroneckerMap (fun y₁ y₂ ↦ y₁ * y₂) 1 (g.val.val)⁻¹ᵀ *ᵥ matrixToVec x) (a, b) +
        (kroneckerMap (fun y₁ y₂ ↦ y₁ * y₂) 1 (g.val.val)⁻¹ᵀ *ᵥ u) (a, b) ∈ Ô E) → _
  intro u hu h_int
  -- The condition at row `ρ p`, where `x` has the unit vector at `p`.
  replace h_int (p j : n) : z * D p j + ∑ k : n, u (ρ p, k) * D k j ∈ Ô E := by
    simpa [hρ, hD, hu, mulVec_eq_sum, sum_prod_type, mul_add, ← add_assoc, Pi.single_apply,
      matrixToVec, Matrix.one_apply, Finset.sum_add_distrib,
        add_mem_cancel_right] using h_int (ρ p) j
  -- `D` is integral, since `g⁻¹` is integral wherever `z` is
  have hD_int (i j : n) : D i j ∈ Ô E :=
    mem_Ô_of_mul_add_sum_mem_Ô (u := fun p k ↦ u (ρ p, k)) hg hD_def (fun p k ↦ hu (ρ p) k)
      h_int i j
  have hzD (i j : n) : z * D i j ∈ Ô E := by
    simpa (disch := simp [hu, hD_int, mul_mem, sum_mem]) [add_mem_cancel_right] using h_int i j
  have hg_int : g ∈ stdLevel E n := inv_mem_iff.mp <| mem_stdLevel.mpr <| by
    simp [hD, hD_int, Matrix.one_apply, ite_mem, add_mem_cancel_right]
  exact absurd ⟨hg_int, hzD⟩ hg_not

/-- Let `H` be an open subgroup of `Gf E n`, let `b` be a character of `U(1)` of weight `c` with
trivial tame part, and let `2 * card n ≤ card m`. Then there exist a set `S` of finite places
avoiding every `w` with `maxCompactAt n w ≤ H`, a Schwartz datum `F` on
`Hom(stdSpace E n, stdSpace E m)`, a level `J ≤ H` and a number `mass` such that `F` is sharp for
`b`, `S` and `J` (`IsSharp`). Sharpness means: `⟨F, F⟩ ≠ 0`; `F` lies in the finite part and is a
vacuum off `S` (fixed by the projection `projOn` on vacua at every set of places disjoint from `S`)
and clean (true here as all signs of the standard spaces are `1`); at finite points `g` integral off
`S`, the coefficient `⟨F, ω(g) F⟩` of the Weil action `ω` (built from `b`) is `⟨F, F⟩` on
`J ⊓ stdLevel E n` and zero elsewhere, where `stdLevel E n` is the stabiliser `K₀` of `Ô ^ n`; and
`mass` is the quotient of `⟨F, F⟩` by the index `[K₀ : J ⊓ K₀]`. -/
lemma exists_isSharp_of_two_mul_card_le {m : Type} [Fintype m] [DecidableEq m]
    {H : Subgroup (Gf E n)}
    (hH : IsOpen H.carrier) {b : AutChar E} {c : InfinitePlace E → ℤ} (hb : b.HasWeight c 1)
    (h_rank : 2 * card n ≤ card m) :
    ∃ S : Set (FinPlace E),
      (∀ w : FinPlace E, maxCompactAt n w ≤ H → w ∉ S) ∧
      ∃ F : 𝒮 ((stdSpace E n).hom (stdSpace E m)), ∃ J ≤ H, ∃ mass : ℂ,
        IsSharp (S := stdSpace E n) (T := stdSpace E m) b S F J mass := by
  classical
  -- The datum is the vacuum translated by `z • x`, with `x` an integral isotropic frame and `z`
  -- the inverse of a level `N` at the bad places `B` of `H` and their conjugates, zero elsewhere.
  -- `J` is its stabiliser in `H`, and `S` the set of places where `z` is not integral.
  -- The rows `ρ i` of `x` form the identity matrix.
  obtain ⟨x, hx_int, hx_iso, ρ, hρ⟩ := exists_integral_isotropic_frame (E := E) h_rank
  -- `H` contains the integral elements that are trivial at `B`, and those congruent to `1` mod `N`.
  obtain ⟨B, hB, hB_off⟩ := exists_inf_trivialOn_le hH
  obtain ⟨N, hN, hN_cong⟩ := exists_principalLevel_subset (hH.mem_nhds H.one_mem)
  let z : 𝔸f E := (N : E)⁻¹ • idem (SetLike.coe B).conjClosure
  let S : Set (FinPlace E) := {w | 1 < v (z w)}
  let F : 𝒮 ((stdSpace E n).hom (stdSpace E m)) :=
    finHeisenbergOp _ (matrixToVec (z • x)) (vacElem _)
  let J : Subgroup (Gf E n) := H ⊓ (MulAction.stabilizer _ F).comap
    ((pairWeil (stdSpace E n) (stdSpace E m) 1 b).comp
      (.prod (.inr (GInf E 1) (Gf E n)) 1)).toHomUnits
  -- Only the fields `vacuum_off` and `weilMatrixCoeff_eq` of `IsSharp` need an argument. Where
  -- `H` contains the maximal compact subgroup, `w` is not in `B`, so `z` is `0` there.
  refine ⟨S, fun w hw ↦ by simp [hB w hw, S, z, smul_def], F, J, inf_le_left,
    dataInner _ F F / stdLevelIndex J,
    { self_ne_zero := by simp [F, dataInner_finHeisenbergOp]
      mem_finitePart := finHeisenbergOp_mem_finitePart _ vacElem_mem_finitePart
      vacuum_off := fun A _ hA ↦ ?_
      weilMatrixCoeff_eq := fun g hg ↦ ?_
      mass_eq := rfl
      -- all signs of the standard spaces are `1`, so `F` is clean
      clean := fun _ ↦ by simp [IsClean] }⟩
  · -- Off `S` the translation is integral, so `F` is the vacuum there. The closure of `A` under
    -- conjugation is `A` together with its conjugate, and both are disjoint from `S`.
    have hz : idem A.conjClosure * z ∈ Ô E := by
      refine idem_mul_mem_Ô.mpr ?_
      rintro _ (h | h) <;> simpa [← v_star_apply, S, z] using hA.le_compl_left h
    simp [F, ← mul_assoc, hz, hx_int, matrixToVec, projOn_finHeisenbergOp, mem_integralBox, mul_mem]
  -- On `J`, which fixes `F`, the coefficient is constant.
  refine .symm (ite_eq_iff'.mpr ⟨fun hg_mem ↦ ?_, fun hg_not ↦ ?_⟩)
  · obtain ⟨⟨-, hg_fix⟩, -⟩ := hg_mem
    exact congrArg _ hg_fix.symm
  -- Off `J ⊓ stdLevel E n` it vanishes, since an integral `g` with `z • D` integral lies in `J`.
  let D : Matrix n n (𝔸f E) := g⁻¹.val.val - 1
  have hD : (g.val.val)⁻¹ = D + 1 := by simp [D]
  refine .symm (weilMatrixCoeff_finHeisenbergOp_eq_zero hρ hg rfl rfl fun ⟨hg_int, hzD⟩ ↦ ?_)
  exact hg_not
    ⟨mem_inf_stabilizer_of_integral hb hx_int hx_iso hB_off hN hN_cong z rfl hD hg_int hzD, hg_int⟩

omit [WeilData E] [DecidableEq n] in
/-- Let `t` and `t'` give the Hecke polynomials at `w` of ranks `card n` and `card n + s`, the
second of degree `card n + s`. Suppose that for all `X` their reciprocal polynomials `heckePolyEval`
satisfy `R' X = R (μ * X) * qPochhammer w.q s (ν * X)` (`qPochhammer w.q s Y` is a product over
`l < s` of factors linear in `q_w ^ l * Y`), where `R` is built from `t` and `R'` from `t'`, and let
`μ * a = 1` and `θ l = q_w ^ l * ν * a` for `l < s`. Then the second Hecke polynomial, with its
roots multiplied by `a`, is the first one times `∏ l < s, (X - θ l)`. -/
private lemma scaleRoots_heckePoly_eq (w : FinPlace E) {s : ℕ} {t t' : ℕ → ℂ} {μ ν a : ℂ}
    (θ : Fin s → ℂ)
    (h_deg : (heckePoly w.q (card (Fin (card n + s))) t').natDegree = card (Fin (card n + s)))
    (h_eigval : ∀ X : ℂ, heckePolyEval (Fin (card n + s)) w t' X =
      heckePolyEval n w t (μ * X) * qPochhammer w.q s (ν * X))
    (h_scale : μ * a = 1) (h_root : ∀ l : Fin s, θ l = w.q ^ (l : ℕ) * ν * a) :
    (heckePoly w.q (card (Fin (card n + s))) t').scaleRoots a =
      heckePoly w.q (card n) t * ∏ l : Fin s, (X - C (θ l)) := by
  have ha_ne : a ≠ 0 := right_ne_zero_of_mul_eq_one h_scale
  -- Compare the two polynomials at every `x ≠ 0`: there a Hecke polynomial is `x ^ n` times
  -- `heckePolyEval` at `x⁻¹`, and `h_eigval` at `a / x` splits the left side into the two factors.
  refine eq_of_infinite_eval_eq _ _ <|
    infinite_of_finite_compl ((eventually_cofinite_ne 0).mono fun x hx ↦ ?_)
  rw [eval_mul, eval_heckePoly w t hx, ← mul_div_cancel₀ x ha_ne, scaleRoots_eval_mul,
    eval_heckePoly w t' (div_ne_zero hx ha_ne), h_deg, ← mul_assoc,
    ← mul_pow, h_eigval, eval_prod, card_fin, pow_add, ← Fin.prod_const s, mul_mul_mul_comm,
    qPochhammer, Finset.prod_range, ← Finset.prod_mul_distrib, mul_div_cancel₀ x ha_ne, inv_div,
    mul_div_assoc', h_scale, one_div]
  -- What is left is one linear factor for each `l < s`.
  exact congrArg _ (Finset.prod_congr rfl fun l _ ↦ by simp [h_root, field])

omit [WeilData E] [DecidableEq n] in
/-- Let `c ≤ e`, `card n < s`, and let `κ'` agree with `κ` below `card n`, be `e - c` at `card n`
and `0` above. Then in rank `card n` the weight `(κ, e)` is also `(κ', c + κ' (card n))`, so a
parameter `l` of `(κ, e)` in rank `card n` and a parameter `l'` of `(κ', 0)` in rank `card n + s`
correspond. -/
private lemma paramsCorrespond_of_isHCParam {κ κ' : InfinitePlace E → ℕ → ℕ}
    {e c : InfinitePlace E → ℤ} {s : ℕ} (hc : c ≤ e)
    (hκ : κ' = fun (v : InfinitePlace E) (h : ℕ) ↦
      if h < card n then κ v h else if h = card n then (e v - c v).toNat else 0)
    (hs : card n < s) {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → Fin (card n + s) → ℤ}
    (hl : IsHCParam (n := n) κ e l) (hl' : IsHCParam (n := Fin (card n + s)) κ' 0 l') :
    ParamsCorrespond 0 c l l' 1 1 := by
  -- `hcParameter` reads `κ'` only at heights below `card n`, where it is `κ`, and
  -- `c + κ' (card n) = c + (e - c) = e`; so `l` is also a parameter of `(κ', c + κ' (card n))`.
  have h_hcParameter_eq (w : InfinitePlace E) (p : ℕ) :
      hcParameter κ' (fun τ ↦ c τ + (κ' τ (card n) : ℤ)) (card n) w p =
        hcParameter κ e (card n) w p := by
    have h_sum : (Finset.Ioo p (card n)).sum (κ' w) = (Finset.Ioo p (card n)).sum (κ w) :=
      Finset.sum_congr rfl fun h hh ↦ by grind
    have h_top : c w + (κ' w (card n) : ℤ) = e w := by grind [Pi.le_def]
    simp only [hcParameter, diagramWeight_apply, h_sum, h_top]
  have hl_weight : IsHCParam (n := n) κ' (fun τ ↦ c τ + (κ' τ (card n) : ℤ)) l := by
    simpa only [IsHCParam, h_hcParameter_eq] using hl
  have h_lift_weight : IsLiftWeight n (Fin (card n + s)) κ' c (fun τ ↦ c τ + (κ' τ (card n) : ℤ)) :=
    ⟨by grind [card_fin], by simp [hs.pos], rfl⟩
  exact (hl_weight.paramsCorrespond_iff h_lift_weight).mpr hl'

omit [DecidableEq n] in
/-- The scalars of the theta lift at the place `w` cancel: `q_w ^ s * frobValue 1 n w`, divided by
`b.frobValue (Fin (card n + s)) w` (scalars at `w` built from powers of `√q_w` and values at a
uniformiser) and multiplied by the value at `w` of the algebraic Hecke character
`hb.toAlgebraic s s`, is `1`. Here `b` is a character of `U(1)` of weight `c`. -/
private lemma frobValue_div_mul_heckeCoeff_eq_one {b : AutChar E} {c : InfinitePlace E → ℤ}
    (hb : b.HasWeight c 1) (s : ℕ) (w : FinPlace E) :
    w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w *
      heckeCoeff (hb.toAlgebraic s s).val.fst ∅ w = 1 := by
  simp [HasWeight.toAlgebraic, frobValue, w.coe_q_eq_sq_sqrt, w.ne_bot, HeckeChar.atUniformizer,
    heckeCoeff, AutChar.spaceChar, zpow_sub₀, zpow_mul (_ : ℂ), field]
  -- What is left is a rearrangement of powers of `√q_w` and of `υ` at a uniformiser.
  ring

/-- Rallis' inner product formula makes the theta lift injective on forms of level `J`. Let `b` be
a character of `U(1)` of weight `c`, `v` an edge from type `l` to type `l'` (`IsEdge`), `Ψ` sharp
for `b` and a level `J` (`IsSharp`), and `2 * card n < card n + s`. If the algebraic form of `y`
is not zero and is fixed by `J`, then the algebraic form of the lift of `y` by `v ⊗ Ψ` is not
zero. -/
private lemma toAlgForm_formLift_ne_zero {κ κ' : InfinitePlace E → ℕ → ℕ}
    {e c : InfinitePlace E → ℤ} {s : ℕ} {b : AutChar E} (hb : b.HasWeight c 1)
    {l : InfinitePlace E → n → ℤ} {l' : InfinitePlace E → Fin (card n + s) → ℤ}
    (hl : IsHCParam (n := n) κ e l) (hl' : IsHCParam (n := Fin (card n + s)) κ' 0 l')
    {v : Fock.fockSpace (realSigns E (homSigns 1 1))}
    (h_edge : IsEdge (realPairWeil 0 c) (typeKernel l 1) (typeKernel l' 1) v)
    (h_rank : 2 * card n < card (Fin (card n + s)))
    {S : Set (FinPlace E)} {Ψ : 𝒮 ((stdSpace E n).hom (stdSpace E (Fin (card n + s))))}
    {J : Subgroup (Gf E n)} {mass : ℂ} (h_sharp : IsSharp b S Ψ J mass)
    {y : (stdSpace E n).Form (typeKernel l 1)}
    (hJ : J ≤ rightStabilizer (toAlgForm (stdSpace E n) hl y).val)
    (hy_ne : (toAlgForm (stdSpace E n) hl y).val ≠ 0) :
    (toAlgForm (stdSpace E (Fin (card n + s))) hl'
      (formLift (pairThetaKer (stdSpace E n) (stdSpace E (Fin (card n + s))) 1 b)
        (typeKernel l 1) (typeKernel l' 1) (integrated _ v Ψ) y)).val ≠ 0 := by
  intro h_zero
  have hy_level : HasLevel y J := fun k hk ↦ by
    simp [← ofAlgForm_toAlgForm hl, algFormCoeff, hJ hk _]
  obtain ⟨A, -, h_rallis⟩ := rallis_inner_product_cosetTerm h_edge h_rank
  have hy : y = 0 := (h_rallis 1 b h_sharp y hy_level).1
    ((toAlgForm _ hl').map_eq_zero_iff.mp (Submodule.coe_eq_zero.mp h_zero))
  simp [hy] at hy_ne

omit [DecidableEq n] in
/-- Let `F ≠ 0` be a form of rank `card n + s` that is spherical at the split place `w`
(`star w ≠ w`), and on which the Hecke polynomial operator at `X` acts by `qPochhammer w.q s
(frobValue 1 n w * X) * heckePolyEval n w t (r * X)`, with `qPochhammer w.q s Y` a product over
`l < s` of factors linear in `q_w ^ l * Y`, where `r = q_w ^ s * frobValue 1 n w / b.frobValue (Fin
(card n + s)) w` and `b` is a character of `U(1)` of weight `c`. Then `F` has a Hecke polynomial `Q`
at `w` (`HasHeckePolyAt`), and `Q` with its roots multiplied by the value at `w` of
`hb.toAlgebraic s s` is `heckePoly w.q (card n) t` times `∏ l < s, (X - θ l)`, where `θ l` is the
value at `w` of `hb.toAlgebraic (card n + s) (s - l)`. -/
private lemma exists_hasHeckePolyAt_scaleRoots_eq {κ' : InfinitePlace E → ℕ → ℕ} {s : ℕ}
    {b : AutChar E} {c : InfinitePlace E → ℤ} (hb : b.HasWeight c 1) {w : FinPlace E}
    (hw : star w ≠ w) {t : ℕ → ℂ}
    {F : Gf E (Fin (card n + s)) → WeylIndex (Fin (card n + s)) κ' → ℂ} (hF_ne : F ≠ 0)
    (hF_sph : HasHeckePolynomial
      (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)) hw
      (fun X : ℂ ↦ qPochhammer w.q s (frobValue 1 n w * X) *
        heckePolyEval n w t (w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w * X))
      F) :
    ∃ Q : ℂ[X],
      HasHeckePolyAt F w hw Q ∧
      Q.scaleRoots (heckeCoeff (hb.toAlgebraic s s).val.fst ∅ w) =
        heckePoly w.q (card n) t *
          ∏ l : Fin s, (X - C (heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).val.fst ∅ w)) := by
  -- The operators `T_i` act on `F` by scalars `t' i`; these give its Hecke polynomial `Q`.
  obtain ⟨t', ht'⟩ : ∃ t' : ℕ → ℂ, ∀ i,
      heckeSplit (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ))
        hw i F = t' i • F :=
    (exists_heckeSplit_eq_smul _).imp fun _ h_all ↦ h_all F hF_sph
  obtain ⟨hF_spherical, hF_eigval⟩ := hF_sph
  have hF_eig : HasHeckePolyAt F w hw (heckePoly w.q (card (Fin (card n + s))) t') :=
    ⟨hF_spherical, t', rfl, ht'⟩
  -- Two expressions for the eigenvalue of the Hecke polynomial on `F ≠ 0`.
  have h_eigval (X : ℂ) : heckePolyEval (Fin (card n + s)) w t' X =
      heckePolyEval n w t (w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w * X) *
        qPochhammer w.q s (frobValue 1 n w * X) := by
    obtain ⟨-, hF_eigval'⟩ := hasHeckePolynomial_of_heckeSplit hF_spherical ht'
    rw [mul_comm, ← smul_left_inj hF_ne, ← hF_eigval X]
    exact (hF_eigval' X).symm
  refine ⟨_, hF_eig, ?_⟩
  -- The constants of `hasHeckePolynomial_formLift` are values of the algebraic characters.
  exact scaleRoots_heckePoly_eq w
    (fun l ↦ heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).val.fst ∅ w)
    (hF_eig.isMonicOfDegree hF_ne).natDegree_eq h_eigval
    (frobValue_div_mul_heckeCoeff_eq_one hb s w) (by
      intro l
      simp [HasWeight.toAlgebraic, frobValue, w.coe_q_eq_sq_sqrt, w.ne_bot, HeckeChar.atUniformizer,
        heckeCoeff, AutChar.spaceChar, zpow_add₀, zpow_sub₀, zpow_mul (_ : ℂ), field])

/-- Theta lift by `s > n` steps. Let `f ≠ 0` be a form of rank `n ≥ 1` and weight `(κ, e)`, and let
`b` be a character of `U(1)` of weight `c ≤ e` with trivial tame part (`b u = ∏ u_v^{c v}` for `u`
with integral finite part). Let `κ' v h` be `κ v h` for `h < n`, `e v - c v` for `h = n` and `0` for
`h > n`. There is a form `F` of rank `n + s` and weight `(κ', 0)` such that (a) `F ≠ 0`; (b) `F` is
fixed by `K_w` wherever `f` is; (c) at such a split `w`, if `f` has Hecke polynomial `P`, then `F`
has a Hecke polynomial `Q`, and `Q` with its roots multiplied by the value of `hb.toAlgebraic s s`
at `w` equals `P * ∏ l < s, (X - θ l)`, where `θ l` is the value of `hb.toAlgebraic (n + s) (s - l)`
at `w`. Here `hb.toAlgebraic` gives the algebraic Hecke characters `b(x/x̄) υ(x)^{−k} |x|^{j−k/2}`,
evaluated at a uniformiser at `w` (`heckeCoeff`). -/
lemma exists_theta_lift_heckePoly [Nonempty n] {κ κ' : InfinitePlace E → ℕ → ℕ}
    {e : InfinitePlace E → ℤ} {s : ℕ} {c : InfinitePlace E → ℤ} {b : AutChar E}
    (hb : b.HasWeight c 1) (hc : c ≤ e)
    (hκ : κ' = fun (v : InfinitePlace E) (h : ℕ) ↦
      if h < card n then κ v h else if h = card n then (e v - c v).toNat else 0)
    (f : AlgForm n κ e) (hf_ne : f.val ≠ 0) (hs : card n < s) :
    ∃ F ∈ (stdSpace E (Fin (card n + s))).forms (κ', 0),
      F ≠ 0 ∧
      ∀ {w : FinPlace E},
        f.val ∈ sphericalAt (rightRegular ℂ (Gf E n) (WeylIndex n κ → ℂ)) w →
        F ∈ sphericalAt
          (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)) w ∧
        ∀ {hw : star w ≠ w} {P : ℂ[X]},
          HasHeckePolyAt f.val w hw P →
          ∃ Q : ℂ[X],
            HasHeckePolyAt F w hw Q ∧
            Q.scaleRoots (heckeCoeff (hb.toAlgebraic s s).val.fst ∅ w) =
              P * ∏ l : Fin s,
                (X - C (heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).val.fst ∅ w)) := by
  -- `F` is the theta lift of `f` by the datum made of joint harmonics at infinity and a sharp
  -- finite datum. Rallis' formula shows `F ≠ 0`, and `hasHeckePolynomial_formLift` transfers the
  -- Hecke eigenvalues.
  obtain ⟨l, hl⟩ : ∃ l, IsHCParam (n := n) κ e l := ⟨_, isHCParam_hcParameter n κ e⟩
  obtain ⟨l', hl'⟩ : ∃ l', IsHCParam (n := Fin (card n + s)) κ' 0 l' :=
    ⟨_, isHCParam_hcParameter (Fin (card n + s)) κ' 0⟩
  have h_rank : 2 * card n < card (Fin (card n + s)) := by grind [card_fin]
  -- In rank `n` the weight `(κ, e)` is also `(κ', c + κ' (card n))`: the columns below `card n`
  -- agree, and `c + (e - c) = e`. So `l` and `l'` correspond (`paramsCorrespond_of_isHCParam`),
  -- which gives the datum at infinity: a Fock vector `v`, an edge from type `l` to type `l'`.
  obtain ⟨v, h_edge⟩ : ∃ v, IsEdge (realPairWeil 0 c) (typeKernel l 1) (typeKernel l' 1) v :=
    ⟨_, (paramsCorrespond_of_isHCParam hc hκ hs hl hl').isEdge_jointHarmonic⟩
  -- The finite datum `Ψ`: sharp for a level `J` that fixes `f` (a smooth form has an open
  -- stabiliser), with bad set `S` avoiding the places where `f` is spherical.
  obtain ⟨S, hS, Ψ, J, hJ, mass, h_sharp⟩ :=
    exists_isSharp_of_two_mul_card_le (H := rightStabilizer f.val)
      (Submodule.mem_inf.mp f.property).left hb h_rank.le
  -- `v ⊗ Ψ` is an arrow: it lifts forms of type `l` to forms of type `l'`.
  have h_arr : IsArrow (pairThetaKer (stdSpace E n) (stdSpace E (Fin (card n + s))) 1 b)
      (typeKernel l 1) (typeKernel l' 1) (integrated _ v Ψ) :=
    (h_edge.isArrow 1 b h_sharp.mem_finitePart).left
  -- Write `f` as the algebraic form attached to an adelic form `y`, and lift `y`.
  obtain ⟨y, rfl⟩ := (toAlgForm (stdSpace E n) hl).surjective f
  let y' : (stdSpace E (Fin (card n + s))).Form (typeKernel l' 1) :=
    formLift (pairThetaKer (stdSpace E n) (stdSpace E (Fin (card n + s))) 1 b) (typeKernel l 1)
      (typeKernel l' 1) (integrated _ v Ψ) y
  let F : Gf E (Fin (card n + s)) → WeylIndex (Fin (card n + s)) κ' → ℂ := (toAlgForm _ hl' y').val
  -- By Rallis' formula the lift is injective on forms of level `J`, as `2 * n < n + s`.
  have hF : F ≠ 0 := toAlgForm_formLift_ne_zero hb hl hl' h_edge h_rank h_sharp hJ hf_ne
  refine ⟨F, (toAlgForm _ hl' y').property, hF, fun {w} h_sph ↦ ?_⟩
  -- Where `f` is spherical, the datum is the vacuum.
  have h_le : maxCompactAt n w ≤ rightStabilizer ((stdSpace E n).toAlgForm hl y).val := by
    simpa [funext_iff, LE.le] using h_sph
  have h_vac : projOn _ {w} (integrated _ v Ψ) = integrated _ v Ψ :=
    h_sharp.vacuum_off {w} v (Set.disjoint_singleton_right.mpr (hS w h_le))
  refine ⟨fun k ↦ ?_, ?_⟩
  · -- `k` acts on the lift through the datum, and it fixes the vacuum at `w`.
    have h_transl :
        rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)
            (k : Gf E (Fin (card n + s))) F =
          (toAlgForm _ hl' ((stdSpace E (Fin (card n + s))).formRep (typeKernel l' 1) k y')).val :=
      congrArg Subtype.val (toAlgForm_formRep hl' k y').symm
    rw [h_transl, h_arr.formRep_formLift 1, pairWeil_eq_smul_of_projOn_eq _ h_vac]
    · simp [F, y', Prod.mk_one_one]
    -- the two side conditions of `pairWeil_eq_smul_of_projOn_eq`
    all_goals simp
  rintro hw P ⟨-, t, rfl, ht⟩
  -- The eigenvalue of the Hecke polynomial on `y` comes from the `t j`; on the lift it is
  -- rescaled and multiplied by `qPochhammer`, the factor of the `s` new steps.
  have hy_sph :
      HasHeckePolynomial ((stdSpace E n).formRep (typeKernel l 1)) hw (heckePolyEval n w t) y :=
    (hasHeckePolynomial_toAlgForm_iff _ hl).mp (hasHeckePolynomial_of_heckeSplit h_sph ht)
  have hF_sph : HasHeckePolynomial
      (rightRegular ℂ (Gf E (Fin (card n + s))) (WeylIndex (Fin (card n + s)) κ' → ℂ)) hw
      (fun X ↦ qPochhammer w.q s (frobValue 1 n w * X) *
        heckePolyEval n w t (w.q ^ s * frobValue 1 n w / b.frobValue (Fin (card n + s)) w * X))
      F :=
    (hasHeckePolynomial_toAlgForm_iff _ hl').mpr <| hasHeckePolynomial_formLift (card_fin _)
      (by simp [CharUnramifiedAt]) (hb.charUnramifiedAt rfl rfl) hw h_vac h_arr hy_sph
  exact exists_hasHeckePolyAt_scaleRoots_eq hb hw hF hF_sph

end New
end
end

/-!
# Isotypic spaces of eigenforms and attached Galois representations in every positive rank

This file treats algebraic modular forms on a definite unitary group and their attached Galois
representations. The statement `New.GaloisRep.SphericalCompat` asserts the existence of an attached
Galois representation and local–global compatibility at a place where the form is spherical.

## Overview of this theory

Let `ℓ` be a prime and `ι : ℂ ≃ ℚ̄_ℓ` a fixed isomorphism. Let `E` be a CM field with `New.WeilData`
(auxiliary adelic data). Let `f` be an eigenform of weight `κ`, with Hecke polynomials `P w` at
finite places `w`, on the unitary group of the standard definite hermitian space of rank `n ≥ 1`. A
continuous `r : Gal(Ω/E) → GL_n(ℚ̄_ℓ)` with non-degenerate trace form is `New.GaloisRep.Attached` to
`P` if, for each `ε > 0`, `det (X - r s)` is coefficientwise within `ε` of `ι(P w)` for most
Frobenii `s` at places `w` (`New.mostFrobenii`).

* `New.GaloisRep.sphericalCompat_std`: such an `r` exists. If `f` has maximal level at `w`, every
  such `r` is unramified or crystalline above `w`, with the Hodge–Tate jumps of `κ`; for split `w`
  the Hecke polynomial kills geometric Frobenius. `New.GaloisRep.Attached.trace_eq`: `P` determines
  `tr r`.
* `New.GaloisRep.Attached.local_global_of_eigencharacter`: let `w` be split (`w̄ ≠ w`) and `A` a
  place above it. Let `f` be a pro-`p` Iwahori eigenvector (`p` below `w`) with character
  `ξ = (ξᵢ)`, where `‖ξᵢ(ϖ)‖` is non-increasing for the uniformiser `ϖ`. Then `r` is of finite type
  at `A` (`New.GaloisRep.IsFiniteTypeAt`) and has the jumps of `κ`. Also `∏ (X - ι ξᵢ(x))` kills, in
  the sense of `New.GaloisRep.PolyKillsAt`, each `s` in the decomposition group with `s⁻¹` the
  `q^k`-th power on the residue field (`q` the residue cardinality, `k ≥ 0`). Here `x ∈ E_wˣ` has
  order `k` and local Artin symbol the class of `s`.
* `New.GaloisRep.Attached.isLabelledAt`: the first two conclusions also hold if `f` has a
  `New.HasProductLabel` at `w`. Then a polynomial built from the values of the label's tame
  characters kills each element of inertia, in the same sense.

These replace base change to `GL_n` (Labesse), Galois representations with local–global
compatibility (Shin, Chenevier–Harris, Barnet-Lamb–Gee–Geraghty–Taylor) and the local Langlands
correspondence. Local polynomials kill but need not be characteristic. No Weil–Deligne
representation is built.

Plan. `Lib.Shimura`: models of signature `(1, n - 1)`, the congruence relation and, for odd `n`,
eigenvalues of forms with a cuspidal type in cohomology. `Lib.Cohomology`: base change, fixed point
formula. `Lib.PadicComparison`: cohomology above `ℓ` is crystalline; Hodge classes give jumps.
`Main.SeedRepresentation` cuts it to rank `n` by `KillingPolynomials`. `Main.OddRank`: all forms by
`ℓ`-adic limits (`WeightCongruence`, `Pseudocharacter`, `Lib.PadicHodge.Limit`), then fields with
Weil data by `Main.QuadraticStep` and `BaseChange`. `Main.ThetaLift`, `Main.AllRanks`: two lifts to
rank `2n + 1`, then cancel characters. `LocalGlobal`: tame base change down to the spherical case.

## Main definitions and results

* `New.GaloisRep.sphericalCompat_std`: `New.GaloisRep.SphericalCompat` holds in every positive rank
  n. The proof lifts the eigenform to the odd rank 2n + 1 along two different characters and cancels
  the n + 1 extra characters from each of the two representations.
* `New.Patching.eigenformsAt`: forms spherical at `w` with given eigenvalues (no condition if `w` is
  not split).
* `New.Patching.Isotypic`: the isotypic spaces, each the `liminf` of the `New.Patching.eigenformsAt`
  over the places. They are kept by operators supported at one place
  (`New.Patching.Isotypic.map_mem`).
* `New.Patching.Isotypic.iSupIndep_val`: the isotypic spaces are independent.
* `New.Patching.Isotypic.galRep`, `New.Patching.Isotypic.attached_galRep`: a chosen Galois
  representation of an isotypic space, attached to its Hecke polynomials when the space is nonzero
  (`New.Patching.Isotypic.exists_attached`, `New.Patching.Isotypic.attached_galRep_of_exists`).

Notions from other files:
* `New.WeilData`: Weil data on a stably unramified E: ȷ in E with ȷ = −ȷ̄, Im τȷ > 0 for every τ in
  the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed integers Ô are
  self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at uniformisers of
  the places w with w = w̄.
* `New.AutChar.HasWeight μ e ψ`: the character μ of U(1)(𝔸) has weight e and tame part ψ, that is
  μ(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) when u has integral finite part. From it,
  `HasWeight.toAlgebraic k j` is the algebraic Hecke character μ(x/x̄) υ(x)^{−k} |x|^{j−k/2}, and
  `New.heckeCoeff χ ∅ w` is the value of a Hecke character χ at the chosen uniformiser of w.
* `New.IsTraceNondeg r`: the trace form on the span of the image of r is non-degenerate.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank`, `Lib.ClassField.Global.CMSplittingCharacters` and
`Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms` for sources.
-/

@[expose] public section

noncomputable section

/-!
## Attached Galois representations in every positive rank

The local clauses are `New.GaloisRep.IsGoodAt` (unramified or crystalline),
`New.GaloisRep.HasJumpsAt` (Hodge–Tate jumps) and `New.GaloisRep.PolyKillsAt` (a polynomial kills a
Weil element: `P(r s) = 0` if ℓ is a unit at `A`, else `P` kills the Weil pairs of `s` along each
local datum at `A`). `New.mostFrobenii` is the filter of most Frobenii of degree one; a
`FrobeniusDatum` `y` gives a place `y.place` and a Frobenius element `y.frob` at it, and
`mostFrobeniiAt E g` also lets `y.frob` tend to `g`.
-/

section SphericalAllRanks

open New NumberField Matrix Polynomial Filter Fintype Finset AlgHeckeChar AutChar Metric
  Units

/-- Let `E` be a CM field with Weil data, including a splitting character `υ`, and let `e` assign an
integer to each infinite place. Then there are two characters `μ 0`, `μ 1` of `U(1)(𝔸)` (norm-one
adeles, trivial on `E`) with trivial tame part and weights `c 0`, `c 1` such that: (a) `c i ≤ e` at
every infinite place; and (b) for all integers `k`, `j`, `j'` and every split finite place `w`, the
algebraic Hecke characters `toAlgebraic k j` from `μ 0` and `toAlgebraic k j'` from `μ 1` take
different values at the uniformiser of `w`. Here `toAlgebraic k j` from `μ` is
`x ↦ μ(x/x̄) υ(x)^{−k} |x|^{j−k/2}`. -/
lemma New.AutChar.exists_pair_heckeCoeff_ne {E : Type} [Field E] [CMType E] [WeilData E]
    (e : InfinitePlace E → ℤ) :
    ∃ (μ : Fin 2 → AutChar E) (c : Fin 2 → InfinitePlace E → ℤ)
        (h : ∀ i : Fin 2, (μ i).HasWeight (c i) 1),
      -- (a)
      (∀ {i : Fin 2} (v : InfinitePlace E), c i v ≤ e v) ∧
      -- (b)
      ∀ {w : FinPlace E} {k j j' : ℤ}, w.IsSplit →
        heckeCoeff ((h 0).toAlgebraic k j).character ∅ w ≠
          heckeCoeff ((h 1).toAlgebraic k j').character ∅ w := by
  -- The weights are multiples of the number of roots of unity, so that the characters exist; they
  -- differ by this number at one infinite place.
  let c (i : Fin 2) (v : InfinitePlace E) : ℤ :=
    -torsionOrder E * ((-e v).toNat + (if v = Classical.ofNonempty then i.val else 0))
  -- An integral `u` with `u ū = 1` is a root of unity, so `u ^ torsionOrder E = 1`.
  have h_exists (i : Fin 2) : ∃ μ : AutChar E, μ.HasWeight (c i) fun _ : FinPlace E ↦ 1 := by
    refine exists_hasWeight_of_prod_eq_one (S := ∅) (fun _ _ ↦ rfl) fun u hu ↦ ?_
    have hu_root : (u : E) ^ torsionOrder E = 1 := by simp_all [pow_torsionOrder_eq_one]
    simp [c, _root_.zpow_mul, ← map_pow, hu_root]
  choose μ hμ using h_exists
  refine ⟨μ, c, hμ, fun {i} v ↦ ?_, fun {w k j j'} hw h_val ↦ ?_⟩
  · simp only [c]
    nlinarith only [(-e v).self_le_toNat, torsionOrder_pos E]
  -- Comparing arguments in `h_val`, the quotient `μ 0 / μ 1` is trivial at `u = ϖ / star ϖ`.
  let u : unitary (𝔸 E) := divStar (locFullIdele w (uniformizer w))
  -- The value of the base change of `μ i` at `ϖ` is the value of `μ i` at `u`.
  have h_base (i : Fin 2) :
      (AutChar.baseChange (μ i)).val (finIdeleIncl (locIdele w (uniformizer w))) = (μ i).val u :=
    rfl
  have h_val_u : ((μ 0).val u : ℂ) = (μ 1).val u := by
    simpa [h_base, heckeCoeff, HasWeight.toAlgebraic, HeckeChar.finPart, abs_of_nonneg,
      Real.sqrt_eq_zero', Circle.norm_coe, zpow_ne_zero, (zero_lt_one.trans w.one_lt_q).ne'] using
      congrArg (fun a : ℂ ↦ a / ‖a‖) h_val
  have h_triv : (μ 0 * (μ 1)⁻¹).val u = 1 := mul_inv_eq_one.mpr (Circle.ext h_val_u)
  -- There are `n > 0` and `γ` with `u ^ n * γ` a unit at all finite places; the `n`-th power of the
  -- value at `u` is `∏ v, Φ v γ ^ (c 0 v - c 1 v)`, which is `Φ ofNonempty γ ^ torsionOrder E`.
  -- The archimedean part of `u` is `1 * star 1`.
  have hu_arch : u.val.1 = 1 := Unitary.coe_mul_star_self 1
  obtain ⟨n, hn_pos, γ, h_unit, h_pow⟩ : ∃ n > 0, ∃ γ : unitary E,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Valued.v ((u.val.2 ^ n * ↑γ) v) = 1) ∧
      (μ 0 * (μ 1)⁻¹).val u ^ n = ∏ v : InfinitePlace E, Φ v (γ : E) ^ (c 0 + -c 1) v :=
    ((hμ 0).mul (hμ 1).inv).exists_pow_eq_prod u hu_arch
  have hγ : (γ : E) ^ torsionOrder E = 1 := by
    rw [h_triv] at h_pow
    exact (Φ Classical.ofNonempty).injective (by simpa [c, mul_add] using h_pow.symm)
  -- So `γ` is a unit at `w`, whereas `u` has the valuation of a uniformiser there, `w` being split.
  have hγ_val : w.valuation E (γ : E) = 1 := by
    simpa [NeZero.ne] using congrArg (w.valuation E) hγ
  simpa [u, coe_divStar, locFullIdele, hw, ← map_inv, hγ_val, hn_pos.ne'] using h_unit w

/-- Let `r` be continuous with non-degenerate trace form, and let its trace be that of `ρ` minus the
traces of the one-dimensional representations `χ l`. Let `ρ` and every `χ l` be continuous and
unramified or crystalline at `A`, with jumps `J + ∑ l, j l` for `ρ` and `j l` for `χ l`. Then `r` is
unramified or crystalline at `A` and has the jumps `J`. Moreover, every polynomial `P` that kills
`s` at `A` for `ρ` and for every `χ l` kills it for `r` (`PolyKillsAt`: `P(r s) = 0` if ℓ is a unit
at `A`, and otherwise `P` kills the Weil pairs of `s` along each local datum at `A`). -/
lemma New.GaloisRep.isGoodAt_hasJumpsAt_of_trace_eq_sub {ℓ : ℕ} {E n m T : Type} [ThePrime ℓ]
    [PadicIso ℓ]
    [Field E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype T] {r : GalRep ℓ E n} {ρ : GalRep ℓ E m} {χ : T → GalRep ℓ E (Fin 1)}
    {A : ClosurePlace} {J : (E →+* ℂ) → Multiset ℤ} {j : T → (E →+* ℂ) → Multiset ℤ}
    (hr : Continuous r) (hr_nondeg : IsTraceNondeg r)
    (htr : ∀ g : Gal(Ω/E), (r g).val.trace = (ρ g).val.trace - ∑ l : T, (χ l g).val.trace)
    (hρ_cont : Continuous ρ) (hρ_good : IsGoodAt ρ A) (hρ_jumps : HasJumpsAt ρ A (J + ∑ l : T, j l))
    (hχ_cont : ∀ l : T, Continuous (χ l)) (hχ_good : ∀ l : T, IsGoodAt (χ l) A)
    (hχ_jumps : ∀ l : T, HasJumpsAt (χ l) A (j l)) :
    IsGoodAt r A ∧ HasJumpsAt r A J ∧
    ∀ (s : Gal(Ω/E)) (P : (PadicAlgCl ℓ)[X]), PolyKillsAt ρ A s P →
      (∀ l : T, PolyKillsAt (χ l) A s P) → PolyKillsAt r A s P := by
  -- Regard the trace subtraction as a finite linear combination in `IsTraceLimit`.
  -- The coefficients are `1` for `ρ` and `-1` for the characters. The filter `pure ()`
  -- makes convergence an equality; the limit representation is already given, not constructed.
  let a : Option T → PadicAlgCl ℓ := Option.elim' 1 (-1)
  let σ : Option T → Period.PadicRep Gal(Ω/E) ℓ := Option.elim' ⟨ρ⟩ fun l ↦ ⟨χ l⟩
  have hσ_jumps : ∀ i : Option T, HasJumpsAt (σ i).rep A (Option.elim' (J + ∑ l : T, j l) j i) :=
    Option.forall.mpr ⟨hρ_jumps, hχ_jumps⟩
  have h_limit : IsTraceLimit r A (pure ()) (fun _ ↦ a) fun _ ↦ σ :=
    { continuous_limit := hr
      isTraceNondeg := hr_nondeg
      continuous_approx := fun _ ↦ Option.forall.mpr ⟨hρ_cont, hχ_cont⟩
      isGoodAt_approx := fun _ ↦ Option.forall.mpr ⟨hρ_good, hχ_good⟩
      finite_or_hasJumpsAt := .inl inferInstance
      tendstoUniformly_trace := by simp +instances [tendstoUniformly_iff, htr, a, σ] }
  refine ⟨h_limit.isGoodAt, h_limit.jumpsRelAt (fun _ ↦ hσ_jumps) ?_, fun s P hρ_kill hχ_kill ↦ ?_⟩
  · -- The count of a jump in `J` is its count in `J + ∑ l, j l` minus its counts in the `j l`.
    simp +contextual [eq_comm, Multiset.count_sum', a]
  · -- All members of the family are killed by the same polynomial `P`.
    refine h_limit.polyKillsAt (n := P.natDegree + 1) (Q := fun _ _ ↦ P) (Nat.lt_add_one _)
      (fun _ _ ↦ Nat.lt_add_one _) (fun _ ↦ Option.forall.mpr ⟨hρ_kill, hχ_kill⟩) fun d ↦ ?_
    simp +instances [tendstoUniformly_iff, htr, mul_sub, mul_sum, a, σ]

/-- If `P` and `Q` kill `s` for `r` at `A`, so does `P + Q`. -/
private lemma New.GaloisRep.PolyKillsAt.add {ℓ : ℕ} {E n : Type} [ThePrime ℓ] [Field E]
    [EmbeddedNumberField E] [Fintype n] [DecidableEq n] {r : GalRep ℓ E n} {A : ClosurePlace}
    {s : Gal(Ω/E)} {P Q : (PadicAlgCl ℓ)[X]} (hP : PolyKillsAt r A s P) (hQ : PolyKillsAt r A s Q) :
    PolyKillsAt r A s (P + Q) := by
  grind [PolyKillsAt, Period.IsKilledBy, eval₂_add]

/-- If `P * a` and `P * b` kill `s` for `r` at `A`, and `a` and `b` are coprime, then `P` kills
`s`. -/
lemma New.GaloisRep.PolyKillsAt.of_mul_of_isCoprime {ℓ : ℕ} {E n : Type} [ThePrime ℓ] [Field E]
    [EmbeddedNumberField E] [Fintype n] [DecidableEq n] {r : GalRep ℓ E n} {A : ClosurePlace}
    {s : Gal(Ω/E)} {P a b : (PadicAlgCl ℓ)[X]} (ha : PolyKillsAt r A s (P * a))
    (hb : PolyKillsAt r A s (P * b)) (hab : IsCoprime a b) :
    PolyKillsAt r A s P := by
  obtain ⟨u, v, huv⟩ := hab
  -- Bézout cancels the auxiliary factors inside the ideal of annihilating polynomials.
  -- This argument does not require any of the polynomials to be characteristic.
  have hP_eq : P = P * a * u + P * b * v := by linear_combination -P * huv
  rw [hP_eq]
  exact (ha.of_dvd (dvd_mul_right _ u)).add (hb.of_dvd (dvd_mul_right _ v))

/-- Let `ρ`, of rank `card n + card T`, be attached to the polynomials `P w * ∏ l, (X - c l w)`.
Suppose that at most Frobenii `P w` is monic of degree `card n` (`hP_monic`) and `ιℓ (c l w)` is the
value of the continuous character `ψ l` at the Frobenius element (`hψ_val`). Along Frobenii
tending to `g`, minus the coefficient of degree `card n - 1` of `P w` (the sum of its roots) tends
to `tr ρ g - ∑ l, ψ l g`. -/
lemma New.GaloisRep.Attached.tendsto_trace_sub {ℓ : ℕ} {E n m T : Type} [ThePrime ℓ] [PadicIso ℓ]
    [Field E] [EmbeddedNumberField E] [Fintype n] [Nonempty n] [Fintype m] [DecidableEq m]
    [Nonempty m] [Fintype T] {P : FinPlace E → ℂ[X]} {c : T → FinPlace E → ℂ} {ρ : GalRep ℓ E m}
    {ψ : T → Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ}
    (hρ : Attached (P * fun w : FinPlace E ↦ ∏ l : T, (X - C (c l w))) ρ)
    (hcard : Fintype.card m = Fintype.card n + Fintype.card T) (hψ : ∀ l : T, Continuous (ψ l))
    (hP_monic : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (P y.place).IsMonicOfDegree (Fintype.card n))
    (hψ_val : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, ∀ l : T,
      (ψ l y.frob).val = ιℓ (c l y.place))
    (g : Gal(Ω/E)) :
    Tendsto (fun y : FrobeniusDatum E ↦ -ιℓ ((P y.place).coeff (Fintype.card n - 1)))
      (mostFrobeniiAt E g) (nhds ((ρ g).val.trace - ∑ l : T, (ψ l g).val)) := by
  -- `tr ρ g` is minus the coefficient of degree `card m - 1` of `det (X - ρ g)`, the limit of that
  -- coefficient of `P w * ∏ l, (X - c l w)`; this coefficient is additive for monic products.
  rw [trace_eq_neg_charpoly_coeff]
  let R (w : FinPlace E) : ℂ[X] := ∏ l : T, (X - C (c l w))
  have h_charpoly : Tendsto
      (fun y : FrobeniusDatum E ↦ ιℓ ((P y.place * R y.place).coeff (card m - 1)))
      (mostFrobeniiAt E g) (nhds ((ρ g).val.charpoly.coeff (card m - 1))) :=
    hρ.tendsto_charpoly_coeff g (card m - 1)
  have h_chars : Tendsto (fun y : FrobeniusDatum E ↦ ∑ l : T, (ψ l y.frob).val)
      (mostFrobeniiAt E g) (nhds (∑ l : T, (ψ l g).val)) :=
    tendsto_mostFrobeniiAt fun g : Gal(Ω/E) ↦ ∑ l : T, (ψ l g).val
  have h_coeff : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      -ιℓ ((P y.place * R y.place).coeff (card m - 1)) - ∑ l : T, (ψ l y.frob).val =
        -ιℓ ((P y.place).coeff (card n - 1)) := by
    filter_upwards [hP_monic, hψ_val] with y hy_monic hy_val
    have h_next : (P y.place * R y.place).nextCoeff =
        (P y.place).nextCoeff + (R y.place).nextCoeff :=
      hy_monic.monic.nextCoeff_mul (monic_prod_X_sub_C (fun l ↦ c l y.place) univ)
    -- `↓`: `prod_X_sub_C_nextCoeff` must act before `nextCoeff` is unfolded.
    simpa [R, hy_val, ↓prod_X_sub_C_nextCoeff, nextCoeff, hy_monic.monic.natDegree_mul,
      hy_monic.natDegree_eq, hcard, monic_prod_X_sub_C, sub_eq_iff_eq_add'] using
      congrArg (fun z : ℂ ↦ -ιℓ z) h_next
  exact (h_charpoly.neg.sub h_chars).congr' (mem_inf_of_left h_coeff)

/-- Let `ρ` be attached to `P * R`, where at most Frobenii `ιℓ (R w)` is `∏ l, (X - ψ l s)`, with
`s` the Frobenius element and `ψ l` continuous characters. A representation `r` with
non-degenerate trace form and trace `tr ρ - ∑ l, ψ l` is attached to `P`. -/
lemma New.GaloisRep.Attached.of_trace_sub {ℓ : ℕ} {E n m T : Type} [ThePrime ℓ] [PadicIso ℓ]
    [Field E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype T] {P R : FinPlace E → ℂ[X]} {ρ : GalRep ℓ E m} {r : GalRep ℓ E n}
    {ψ : T → Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ} (hρ : Attached (P * R) ρ) (hψ : ∀ l : T, Continuous (ψ l))
    (hr_nondeg : IsTraceNondeg r)
    (htr : ∀ g : Gal(Ω/E), (ρ g).val.trace - ∑ l : T, (ψ l g).val = (r g).val.trace)
    (hR : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (R y.place).map ιℓ.toRingHom = ∏ l : T, (X - C (ψ l y.frob).val)) :
    Attached P r := by
  -- `r` is continuous because its trace is.
  have hρ_cont : Continuous ρ := hρ.continuous
  have h_diff_cont : Continuous fun g : Gal(Ω/E) ↦ (ρ g).val.trace - ∑ l : T, (ψ l g).val := by
    fun_prop
  refine ⟨hr_nondeg.continuous_of_trace (h_diff_cont.congr htr), hr_nondeg, IsOpenMap.id,
    fun η hη ↦ ?_⟩
  filter_upwards [hρ.eventually_norm_coeff_le hη, hR] with y hy hRy
  -- Comparing traces of powers factors the characteristic polynomial of `ρ`.
  have h_trace_pow (k : ℕ) : ((ρ y.frob).val ^ k).trace =
      ((r y.frob).val ^ k).trace + ∑ l : T, (ψ l y.frob).val ^ k := by
    simpa [sub_eq_iff_eq_add] using htr (y.frob ^ k)
  have hchar :
      (ρ y.frob).val.charpoly = (r y.frob).val.charpoly * ∏ l : T, (X - C (ψ l y.frob).val) :=
    charpoly_eq_mul_of_trace_pow_add (ρ y.frob).val univ (fun l ↦ (ψ l y.frob).val) h_trace_pow
  -- Cancel the monic factor from the approximation for `ρ`.
  refine forall_eq.mpr
    (norm_coeff_le_of_mul_monic (monic_prod_X_sub_C (fun l ↦ (ψ l y.frob).val) univ) ?_)
  simpa [sub_mul, hchar, ← hRy] using hy

/-- Let `ρ 0`, `ρ 1` be attached to the polynomials `P w * ∏ l, (X - c i l w)`. Suppose that at most
Frobenii `P w` is monic of degree `card n` (`hP_monic`) and `ιℓ (c i l w)` is the value of the
continuous character `ψ i l` at the Frobenius element (`hψ_val`), and that no `ψ 0 l` equals a
`ψ 1 l'`. Then some representation of rank `card n` is attached to `P`, and every representation
`r` attached to `P` has trace `tr ρ i - ∑ l, ψ i l` for both `i`. -/
lemma New.GaloisRep.Attached.exists_attached_of_mul_prod {ℓ : ℕ} {E n m T : Type} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n]
    [Nonempty n] [Fintype m] [DecidableEq m] [Nonempty m] [Fintype T] {P : FinPlace E → ℂ[X]}
    {c : Fin 2 → T → FinPlace E → ℂ} {ρ : Fin 2 → GalRep ℓ E m}
    {ψ : Fin 2 → T → Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ}
    (hρ : ∀ i : Fin 2, Attached (P * fun w : FinPlace E ↦ ∏ l : T, (X - C (c i l w))) (ρ i))
    (hcard : Fintype.card m = Fintype.card n + Fintype.card T)
    (hψ : ∀ (i : Fin 2) (l : T), Continuous (ψ i l)) (hne : ∀ l l' : T, ψ 0 l ≠ ψ 1 l')
    (hP_monic : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (P y.place).IsMonicOfDegree (Fintype.card n))
    (hψ_val : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      ∀ (i : Fin 2) (l : T), (ψ i l y.frob).val = ιℓ (c i l y.place)) :
    (∃ r : GalRep ℓ E n, Attached P r) ∧
    ∀ r : GalRep ℓ E n, Attached P r → ∀ (i : Fin 2) (g : Gal(Ω/E)),
      (r g).val.trace = (ρ i g).val.trace - ∑ l : T, (ψ i l g).val := by
  -- Both `tr ρ i - ∑ l, ψ i l` are the limit of minus a coefficient of `P w`, so they agree, and
  -- cancelling the characters gives a representation with this trace.
  have htrace (g : Gal(Ω/E)) (i : Fin 2) :
      Tendsto (fun y : FrobeniusDatum E ↦ -ιℓ ((P y.place).coeff (Fintype.card n - 1)))
        (mostFrobeniiAt E g) (nhds ((ρ i g).val.trace - ∑ l : T, (ψ i l g).val)) :=
    (hρ i).tendsto_trace_sub hcard (hψ i) hP_monic (hψ_val.mono fun _ hy_val ↦ hy_val i) g
  obtain ⟨r₀, hnd, hr₀⟩ : ∃ r₀ : GalRep ℓ E n, IsTraceNondeg r₀ ∧
      ∀ g : Gal(Ω/E), (ρ 0 g).val.trace - ∑ l : T, (ψ 0 l g).val = (r₀ g).val.trace :=
    IsTraceNondeg.exists_cancel_chars hcard (fun i ↦ (hρ i).isTraceNondeg) hne
      fun i g ↦ eq_add_of_sub_eq (tendsto_nhds_unique (htrace g i) (htrace g 0))
  refine ⟨⟨r₀, (hρ 0).of_trace_sub (hψ 0) hnd hr₀ ?_⟩, fun r hr i g ↦ ?_⟩
  · filter_upwards [hψ_val] with y hy_val
    simp [hy_val, Polynomial.map_prod]
  · -- The trace of `r` is the same limit.
    rw [trace_eq_neg_charpoly_coeff]
    exact tendsto_nhds_unique (hr.tendsto_charpoly_coeff g (Fintype.card n - 1)).neg (htrace g i)

/-- Let `σ` be attached to `Q` and let `ν` be a continuous character. Suppose that at most Frobenii
`ν` takes the value `ιℓ (z w)`, `Q w` is monic of degree `card m`, and `Q w` with its roots
multiplied by `z w` is `P w`. Then the twist of `σ` by `ν` is attached to `P`. -/
lemma New.GaloisRep.Attached.twistByChar_of_scaleRoots_eq {ℓ : ℕ} {E m : Type} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [EmbeddedNumberField E] [Fintype m] [DecidableEq m]
    {P Q : FinPlace E → ℂ[X]} {z : FinPlace E → ℂ} {σ : GalRep ℓ E m}
    {ν : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ} (hσ : Attached Q σ) (hν : Continuous ν)
    (hev : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, (ν y.frob).val = ιℓ (z y.place) ∧
      (Q y.place).IsMonicOfDegree (Fintype.card m) ∧
      (Q y.place).scaleRoots (z y.place) = P y.place) :
    Attached P (twistByChar ν σ) := by
  have hσ_cont : Continuous σ := hσ.continuous
  refine ⟨.of_coeHom_comp (.smul (by fun_prop) (by fun_prop)), hσ.isTraceNondeg.twist ν,
    IsOpenMap.id, fun η hη ↦ ?_⟩
  filter_upwards [hσ.eventually_norm_coeff_le hη, hev] with y hy ⟨hν_val, hQ_monic, hQ_scale⟩
  -- Twisting scales the roots by the value of `ν`, of norm one, so each coefficient of the
  -- difference keeps its norm.
  have hν_norm : ‖(ν y.frob).val‖ = 1 :=
    ContinuousMonoidHom.norm_apply_eq_one_of_compactSpace ⟨ν, hν⟩ y.frob
  have hy_frob (i : ℕ) : ‖(σ y.frob).val.charpoly.coeff i - ιℓ ((Q y.place).coeff i)‖ ≤ η := by
    simpa [coeff_sub, coeff_map] using hy y.frob rfl i
  simpa [← hQ_scale, Units.smul_def, charpoly_smul_coeff, hQ_monic.natDegree_eq, ← hν_val,
    mul_comm (ιℓ _), ← mul_sub, hν_norm] using hy_frob

/-- Let `μ` be a character of `U(1)(𝔸)` with trivial tame part and weight `c ≤ κ.2`, and let `f` be
an eigenform of weight `κ` on the standard definite space of rank `card n`, with Hecke polynomials
`P`. Let `t > card n` with `card n + t` odd, and let `R v` be the product of the `X - z`, where `z`
runs over the values at the uniformiser of `v` of the `t` characters
`toAlgebraic (card n + t) (t - l)` made from `μ`. Some `ρ` of rank `card n + t` is attached to
`P * R`; and if `f` is spherical at `w`, then at every place `A` of `Ω` over `w`, `ρ` is unramified
or crystalline, has the jumps of `κ` in rank `card n` together with those of the `t` characters,
and for split `w`, where `f` has Hecke polynomial `Pw`, `ιℓ (Pw * R w)` kills every geometric
Frobenius element. -/
private lemma New.GaloisRep.exists_attached_mul_prod_X_sub_C {ℓ : ℕ} {E n : Type} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [EmbeddedNumberField E] [CMType E] [Fintype n]
    [DecidableEq n] [Nonempty n] [WeilData E] {μ : AutChar E} {c : InfinitePlace E → ℤ}
    (hμ : μ.HasWeight c 1) {P : FinPlace E → ℂ[X]} {κ : Weight E}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} (hc : c ≤ κ.2) (hf : f ∈ (stdSpace E n).forms κ)
    (hP : IsEigenform f P) (w : FinPlace E) (t : ℕ) (ht : card n < t) (ht_odd : Odd (card n + t)) :
    ∃ ρ : GalRep ℓ E (Fin (card n + t)),
      Attached (P * fun v : FinPlace E ↦ ∏ l : Fin t,
        (X - C (heckeCoeff (hμ.toAlgebraic (card n + t) (t - l)).val.1 ∅ v))) ρ ∧
      (f ∈ sphericalAt (rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ)) w →
        ∀ A : ValuationSubring Ω, IsPlaceOver A w →
          IsGoodAt ρ A ∧
          HasJumpsAt ρ A (jumps κ (card n) +
            ∑ l : Fin t, fun τ : E →+* ℂ ↦ {-(hμ.toAlgebraic (card n + t) (t - l)).val.2.toAdd τ}) ∧
          ∀ (hw : star w ≠ w) (Pw : ℂ[X]), HasHeckePolyAt f w hw Pw →
            ∀ s : Gal(Ω/E), IsFrob A w.q s⁻¹ →
              PolyKillsAt ρ A s ((Pw * ∏ l : Fin t,
                (X - C (heckeCoeff (hμ.toAlgebraic (card n + t) (t - l)).val.1 ∅ w))).map
                  ιℓ.toRingHom)) := by
  -- Lift `f` to rank `card n + t`; the lift has an attached representation `σ` since the rank is
  -- odd, and `ρ` is its twist by the avatar of `ν`.
  obtain ⟨hf_ne, hf_hecke⟩ := hP
  -- `ν` is the twisting character and `θ l` are the `t` extra characters.
  let ν : AlgHeckeChar E := hμ.toAlgebraic t t
  let θ (l : Fin t) : AlgHeckeChar E := hμ.toAlgebraic (card n + t) (t - l)
  let R (v : FinPlace E) : ℂ[X] := ∏ l : Fin t, (X - C (heckeCoeff (θ l).val.1 ∅ v))
  -- The theta lift `F ≠ 0` of rank `n + t`, spherical where `f` is (`hF_sph`). Its Hecke
  -- polynomials `Q` (`hQ`), with roots scaled by the value of `ν`, are `P * R` (`hQR`).
  choose! F hF hF₀ hF_sph Q hQ hQR using exists_theta_lift_heckePoly hμ hc rfl ⟨f, hf⟩ hf_ne ht
  have h_compat_odd : SphericalCompat (ℓ := ℓ) E (Fin (card n + t)) (card n + t) w :=
    sphericalCompat_of_odd ht_odd w
  have hF_eig : IsEigenform F fun v ↦ Q (w := v) (P := P v) :=
    ⟨hF₀, hf_hecke.mono fun v hv hv_prime ↦ (hv hv_prime).imp fun _ hv_poly ↦
      hQ hv_poly.left hv_poly⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : GalRep ℓ E (Fin (card n + t)),
      Attached (fun v ↦ Q (w := v) (P := P v)) σ :=
    h_compat_odd.exists_attached hF hF_eig
  let ρ : GalRep ℓ E (Fin (card n + t)) := twistByChar ν.avatar σ
  -- Twisting by `ν` scales the roots of `Q` by the value `z` of `ν`, which gives `P * R`.
  let z (v : FinPlace E) : ℂ := heckeCoeff ν.val.1 ∅ v
  have h_twist_data : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (ν.avatar y.frob).val = ιℓ (z y.place) ∧
      (Q (w := y.place) (P := P y.place)).IsMonicOfDegree (card (Fin (card n + t))) ∧
      (Q (w := y.place) (P := P y.place)).scaleRoots (z y.place) = (P * R) y.place := by
    filter_upwards [eventually_mostFrobenii hf_hecke fun y hy ↦ hy y.prime_q,
      eventually_avatar_frob (θ := ν)] with y ⟨_, hy_poly⟩ hy_avatar
    refine ⟨hy_avatar, ?_, hQR hy_poly.left hy_poly⟩
    simpa using (hQ hy_poly.left hy_poly).isMonicOfDegree hF₀
  refine ⟨ρ, hσ.twistByChar_of_scaleRoots_eq (continuous_avatar _) h_twist_data, fun hfK A hA ↦ ?_⟩
  -- The local clauses for `σ`, for the avatars of the characters made from `μ` (unramified at
  -- `w`), and for twists.
  have hσ_loc : IsCompatibleAt F (card n + t) w σ A :=
    h_compat_odd.isCompatibleAt hF hF_eig hσ (hF_sph hfK) hA
  choose hχ_good hχ_jumps hχ_kill using fun {a l : ℤ} ↦
    (avatarCompatAt_of_hasPrimitiveRoot5040 (ℓ := ℓ) _).isSphericalAbove_of_unramified
      (hμ.charUnramifiedAt_toAlgebraic rfl rfl a l) hA
  have h_twist_val (g : Gal(Ω/E)) : (ρ g).val = (ν.avatar g).val • (σ g).val := rfl
  obtain ⟨-, hρ_good, hρ_jumps, hρ_kill⟩ := localConditions_twist A h_twist_val
  have hc_le (v : InfinitePlace E) : c v ≤ κ.2 v := hc v
  refine ⟨hρ_good hσ_loc.isGoodAt hχ_good, ?_, fun hw Pw hPw s hs ↦ ?_⟩
  · -- The first `n` jumps of the lift, of weight `κ'`, shifted by the twist, are those of `κ`, the
    -- last `t` those of the characters `θ l`.
    let κ' : Weight E := (fun (v : InfinitePlace E) (h : ℕ) ↦ if h < card n then κ.1 v h
      else if h = card n then (κ.2 v - c v).toNat else 0, 0)
    have h_jumps_eq : (jumps κ (card n) + ∑ l : Fin t, fun τ : E →+* ℂ ↦
        ({-(θ l).val.2.toAdd τ} : Multiset ℤ)) = fun τ : E →+* ℂ ↦
        (jumps κ' (card n + t) τ).map fun v : ℤ ↦ v + -ν.val.2.toAdd τ := by
      funext τ
      simp [κ', θ, ν, jumps, HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, sum_ite, hc_le,
        ← range_val, ← sum_multiset_singleton, ← Multiset.coe_mapAddMonoidHom, sum_range,
        Fin.sum_univ_add]
      -- Both sides are now a sum over `Fin (card n)` plus a sum over `Fin t`; compare each.
      refine congrArg₂ (· + ·) (by grind) ?_
      -- The last `t` jumps match in the same order if `τ` is in the CM type, reversed otherwise.
      split
      · ring_nf
      · exact sum_equiv Fin.revPerm _ _ (by simp +arith)
    rw [h_jumps_eq]
    exact hρ_jumps hσ_loc.hasJumpsAt hχ_jumps
  · refine hρ_kill ((hσ_loc.polyKillsAt (hQ hPw.left hPw) hs).of_dvd ?_) (hχ_kill s hs)
    -- By `hQR`, `(Pw * R w)(z X)` is a power of `z` times `Q`, `z` the value of `ν`.
    have h_scale : (Q (w := w) (P := Pw)).scaleRoots (z w) = Pw * R w := hQR hPw.left hPw
    change (Q (w := w) (P := Pw)).map ιℓ.toRingHom ∣
      ((Pw * R w).map ιℓ.toRingHom).comp ((C.comp ιℓ.toRingHom) (z w) * X)
    rw [← h_scale, Polynomial.comp, eval₂_map, scaleRoots_eval₂_mul]
    exact dvd_mul_left _ _

/-- Let `E` be a CM field with Weil data (a primitive 5040th root of unity, an element ȷ, an idele α
and a splitting character υ), and let `n` be nonempty. Then `SphericalCompat E n (card n) w` holds:
for every eigenform `f` of weight `κ` on the standard definite unitary space of rank `card n`, with
Hecke polynomials `P`, some representation is attached to `P`. If `f` is spherical at `w` (fixed by
`K_w`), every representation attached to `P` satisfies `IsCompatibleAt` at each place of `Ω` over
`w`: it is unramified or crystalline there, has the jumps of `κ` in rank `card n`, and, if `w` is
split, `ιℓ` of the Hecke polynomial kills every geometric Frobenius.

A weak analogue of the Galois representations attached to conjugate self-dual cohomological cuspidal
representations of GL_n (Shin, Chenevier–Harris, Barnet-Lamb–Gee–Geraghty–Taylor): forms on definite
U(n), given Weil data, with local compatibility only at spherical places. -/
lemma New.GaloisRep.sphericalCompat_std {ℓ : ℕ} {E n : Type} [ThePrime ℓ] [PadicIso ℓ] [Field E]
    [EmbeddedNumberField E] [CMType E] [Fintype n] [DecidableEq n] [Nonempty n]
    [WeilData E] (w : FinPlace E) : SphericalCompat (ℓ := ℓ) E n (card n) w := by
  -- Lift `f` to the odd rank `n + t`, `t = n + 1`, along two characters `μ 0`, `μ 1`. After a twist
  -- the representation `ρ i` of the lift belongs to `P * R i`, `R i` the polynomial of `t`
  -- characters `ψ i l`. The two strings of characters are disjoint, so they can be cancelled.
  intro P κ f hf hP
  let t : ℕ := card n + 1
  obtain ⟨μ, c, hμ, hc_le, h_split_ne⟩ := exists_pair_heckeCoeff_ne κ.2
  -- `θ i l` are the `t` extra characters made from `μ i`, and `ψ i l` their `ℓ`-adic avatars.
  let θ (i : Fin 2) (l : Fin t) : AlgHeckeChar E := (hμ i).toAlgebraic (card n + t) (t - l)
  let ψ (i : Fin 2) (l : Fin t) : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ := (θ i l).avatar
  let R (i : Fin 2) (w : FinPlace E) : ℂ[X] := ∏ l : Fin t, (X - C (heckeCoeff (θ i l).val.1 ∅ w))
  choose ρ hρ hρ_loc using fun i : Fin 2 ↦
    exists_attached_mul_prod_X_sub_C (ℓ := ℓ) (hμ i) hc_le hf hP w t (Nat.lt_add_one _)
      ⟨card n, by omega⟩
  obtain ⟨hf_ne, hf_hecke⟩ := hP
  -- Most Frobenii lie at split places where `f` has the polynomial `P`, and there the avatars of
  -- the characters take the Hecke values.
  have hev_hecke : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      ∃ hw : star y.place ≠ y.place, HasHeckePolyAt f y.place hw (P y.place) :=
    eventually_mostFrobenii hf_hecke fun y hy ↦ hy y.prime_q
  have hev_avatar : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, ∀ (i : Fin 2) (l : Fin t),
      (ψ i l y.frob).val = ιℓ (heckeCoeff (θ i l).val.1 ∅ y.place) := by
    simp [ψ, eventually_avatar_frob]
  -- By `h_split_ne` the two strings differ at most Frobenii, and these Frobenii are dense, so no
  -- `ψ 0 l` equals a `ψ 1 l'` and both strings can be cancelled.
  have hne (l l' : Fin t) : ψ 0 l ≠ ψ 1 l' := by
    have h_differ : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, ψ 0 l y.frob ≠ ψ 1 l' y.frob := by
      filter_upwards [hev_hecke, hev_avatar] with y ⟨hw, _⟩ hy_avatar
      simpa [Units.ext_iff, hy_avatar] using h_split_ne hw
    exact DFunLike.ne_iff.mpr (dense_of_mostFrobenii h_differ).nonempty
  obtain ⟨h_exists, h_trace_r⟩ := Attached.exists_attached_of_mul_prod hρ (by simp)
    (fun _ _ ↦ continuous_avatar _) hne
    (hev_hecke.mono fun y ⟨_, hy_poly⟩ ↦ hy_poly.isMonicOfDegree hf_ne) hev_avatar
  refine ⟨h_exists, fun r hr hfK A hA ↦ ?_⟩
  -- The local clauses for the avatars of the characters made from `μ i`, unramified at `w`.
  choose hχ_good hχ_jumps hχ_kill using fun {i : Fin 2} {a l : ℤ} ↦
    (avatarCompatAt_of_hasPrimitiveRoot5040 (ℓ := ℓ) _).isSphericalAbove_of_unramified
      ((hμ i).charUnramifiedAt_toAlgebraic rfl rfl a l) hA
  let χ (i : Fin 2) (l : Fin t) : GalRep ℓ E (Fin 1) :=
    (GeneralLinearGroup.scalar (Fin 1)).comp (ψ i l)
  have hχ_cont (i : Fin 2) (l : Fin t) : Continuous (χ i l) := by
    refine .of_coeHom_comp (.matrix_diagonal ?_)
    simp only [Pi.constRingHom_eq_algebraMap]
    fun_prop
  choose hρ_good hρ_jumps hρ_kill using fun i : Fin 2 ↦ hρ_loc i hfK A hA
  -- The trace of `r` is `tr ρ i - ∑ l, ψ i l`, so the local clauses pass from `ρ i` to `r`.
  have h_trace_scalar (i : Fin 2) (g : Gal(Ω/E)) :
      (r g).val.trace = (ρ i g).val.trace - ∑ l : Fin t, (χ i l g).val.trace := by
    simp [h_trace_r r hr i g, χ, ψ]
  choose hr_good hr_jumps hr_kill using fun i : Fin 2 ↦
    isGoodAt_hasJumpsAt_of_trace_eq_sub (χ := χ i)
    hr.continuous hr.isTraceNondeg (h_trace_scalar i) (hρ i).continuous (hρ_good i) (hρ_jumps i)
    (hχ_cont i) (fun _ ↦ hχ_good) fun _ ↦ hχ_jumps
  refine ⟨hr_good 0, hr_jumps 0, fun hw Pw hPw s hs ↦ ?_⟩
  -- `Pw * R i` kills `s` for both `i`, and `R 0`, `R 1` are coprime at the split place `w`.
  have hkill (i : Fin 2) : PolyKillsAt r A s ((Pw * R i w).map ιℓ.toRingHom) := by
    refine hr_kill i s _ (hρ_kill i hw Pw hPw s hs) fun l ↦ (hχ_kill s hs).of_dvd ?_
    -- The value of `θ i l` is a root of `R i w`.
    simp [dvd_iff_isRoot, R, θ, eval_map, eval₂_finsetProd, prod_eq_zero (mem_univ l)]
  have hcop : IsCoprime (R 0 w) (R 1 w) := .prod_left fun l _ ↦ .prod_right fun l' _ ↦
    pairwise_coprime_X_sub_C Function.injective_id (h_split_ne hw)
  simp only [Polynomial.map_mul] at hkill
  exact (hkill 0).of_mul_of_isCoprime (hkill 1) (hcop.map (mapRingHom ιℓ.toRingHom))

end SphericalAllRanks

/-!
## Isotypic spaces of eigenforms and their Galois representations

Decomposition of algebraic modular forms on a definite unitary group by their Hecke eigenvalues at
almost all places. `V.forms κ` is the space of forms of weight `κ`, `V.formTranslation κ` the action
of the finite adelic group on it by right translation, and `New.heckeSplit` the Hecke operator
`T_{w,j}` at a split place `w`.
-/

namespace New.Patching

open NumberField Filter Submodule Set Gf GaloisRep Algebra Fintype

section

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]

/-- The valuation ring of `ℚ̄_ℓ`, as a new type. -/
def EllAdicIntegers : Type := intQpBar ℓ
  deriving CommRing, Algebra _ (PadicAlgCl ℓ)

/-- `EllAdicIntegers` maps to `ℂ` by the inverse of the fixed isomorphism `ιℓ : ℂ ≃ ℚ̄_ℓ`. -/
instance : Algebra EllAdicIntegers ℂ := (ιℓ.symm.toRingHom.domRestrict _).toAlgebra

/-- The isomorphism `ιℓ` takes the image in `ℂ` of an element of `EllAdicIntegers` to its image in
`ℚ̄_ℓ`. -/
lemma iota_ell_algebraMap (a : EllAdicIntegers) :
    ιℓ (algebraMap EllAdicIntegers ℂ a) = algebraMap EllAdicIntegers (PadicAlgCl ℓ) a :=
  ιℓ.right_inv _

/-- The `New.Patching.EllAdicIntegers`-algebra of complex-linear endomorphisms of W that map the
submodule M into itself. -/
def endPreserving {W : Type*} [AddCommGroup W] [Module ℂ W] [Module EllAdicIntegers W]
    [IsScalarTower EllAdicIntegers ℂ W] (M : Submodule EllAdicIntegers W) :
    Subalgebra EllAdicIntegers (Module.End ℂ W) where
  carrier := {T : Module.End ℂ W | ∀ f ∈ M, T f ∈ M}
  mul_mem' := by aesop
  add_mem' := by aesop
  algebraMap_mem' := by aesop

variable {E n : Type} [Field E] [CMType E] [Fintype n]
  [DecidableEq n] {V : Space E n 1} {κ : Weight E}

/-! ### Local eigenspaces and isotypic spaces -/

/-- The `New.Patching.EllAdicIntegers`-algebra of operators on forms generated by the right
translations by elements of G_f supported at w and w̄. -/
def localGroupAlgebra (w : FinPlace E) : Subalgebra EllAdicIntegers (V.forms κ →ₗ[ℂ] V.forms κ) :=
  adjoin EllAdicIntegers (V.formTranslation κ '' supportedOn n {w})

variable (V κ)

/-- The forms that, if `w` is split, are fixed by `maxCompactAt n w` and have `T_{w,j} f = t j • f`
for all `j`; all forms if `w` is not split. -/
def eigenformsAt (w : FinPlace E) (t : ℕ → ℂ) : Submodule ℂ (V.forms κ) :=
  ⨅ hw : w.IsSplit,
    sphericalAt (V.formTranslation κ) w ⊓
      ⨅ j : ℕ, (heckeSplit (V.formTranslation κ) hw j).eqLocus (t j • .id)

/-- Isotypic spaces. For a system `t` of eigenvalues at all places, take the space (possibly zero)
of forms that lie in `eigenformsAt V κ w (t w)` for all but finitely many `w`; `Isotypic V κ` is
the type of all these spaces. For `x : Isotypic V κ`, `x.val` is the space and
`x.heckeEigenvalues` a system that defines it. -/
def Isotypic : Type :=
  {x : Submodule ℂ (V.forms κ) //
    ∃ t : FinPlace E → ℕ → ℂ, ∀ f : V.forms κ,
      f ∈ x ↔ ∀ᶠ w : FinPlace E in cofinite, f ∈ eigenformsAt V κ w (t w)}

variable {V κ} {S : Finset (FinPlace E)} {a : V.forms κ →ₗ[ℂ] V.forms κ} {f : V.forms κ}
  {v w : FinPlace E} {t : ℕ → ℂ} (x : Isotypic V κ)

/-- An isotypic space `x` is cut out by some system `t` of Hecke eigenvalues: a form lies in `x`
exactly when it lies in `eigenformsAt V κ w (t w)` at all but finitely many places `w`. -/
lemma Isotypic.exists_heckeEigenvalues :
    ∃ t : FinPlace E → ℕ → ℂ, ∀ f : V.forms κ,
      f ∈ x.val ↔ ∀ᶠ w : FinPlace E in cofinite, f ∈ eigenformsAt V κ w (t w) :=
  x.prop

/-- A chosen system of Hecke eigenvalues, one sequence for each finite place, whose isotypic
space is x (`Isotypic.exists_heckeEigenvalues`). -/
abbrev Isotypic.heckeEigenvalues : FinPlace E → ℕ → ℂ := x.exists_heckeEigenvalues.choose

/-- The Hecke polynomial `heckePoly w.q (card n)` of the chosen eigenvalues of the isotypic space x
at w. -/
abbrev Isotypic.heckePolyAt (w : FinPlace E) : Polynomial ℂ :=
  heckePoly w.q (card n) (x.heckeEigenvalues w)

/-- A chosen representation `Gal(Ω/E) → GL_n(ℚ̄_ℓ)` attached to the Hecke polynomials of the
isotypic space x; arbitrary if none exists. -/
def Isotypic.galRep [Algebra E Ω] : Gal(Ω/E) →* GL n (PadicAlgCl ℓ) :=
  Classical.epsilon (Attached (n := n) x.heckePolyAt)

end

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type} [Field E] [CMType E]
  [Fintype n] [DecidableEq n] {V : Space E n 1} {κ : Weight E}
  {S : Finset (FinPlace E)} {a : V.forms κ →ₗ[ℂ] V.forms κ} {f : V.forms κ} {v w : FinPlace E}
  {t : ℕ → ℂ} {x : Isotypic V κ}

/-- The translation by an element `y` of `G_f` that is trivial at `w` commutes with every operator
`a` in the algebra generated by the translations supported at `w` and `w̄`. -/
lemma commute_of_mem_localGroupAlgebra (ha : a ∈ localGroupAlgebra w) {y : Gf E n}
    (hy : y ∈ trivialOn n {w}) :
    Commute (V.formTranslation κ y) a := by
  -- It suffices to check the generators, the translations by elements supported at `w` and `w̄`.
  refine commute_of_mem_adjoin_of_forall_mem_commute ha ?_
  rintro _ ⟨g, hg, rfl⟩
  exact (commute_supportedOn_trivialOn hg hy).symm.map (V.formTranslation κ)

/-- Let `w` be split and let `θ` map a group `G` to `GL_n` of the local field at `w`. For a
subgroup `K` and a set `s` of `G`, the Hecke operator of the indicator of `s`, for the translations
through `θ` and `ofSplitPlace hw`, lies in the algebra `localGroupAlgebra w`. -/
lemma heckeFun_mem_localGroupAlgebra {G : Type*} [Group G] (hw : w.IsSplit)
    (θ : G →* GL n (LocField w)) {K : Subgroup G} {s : Set G} :
    heckeFun (((V.formTranslation κ).comp (ofSplitPlace hw)).comp θ) K (indicator s 1) ∈
      localGroupAlgebra w := by
  -- The Hecke operator is a sum of translations by elements of the range of `ofSplitPlace hw`,
  -- which is `supportedOn n {w}`.
  refine finsum_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun q ↦ ?_
  by_cases hq : q.out ∈ s
  · -- the term is the translation by an element of the range of `ofSplitPlace hw`, a generator
    have h_gen : V.formTranslation κ (ofSplitPlace hw (θ q.out)) ∈ localGroupAlgebra w :=
      subset_adjoin ⟨_, ofSplitPlace_mem_supportedOn hw (θ q.out), rfl⟩
    simpa [hq] using h_gen
  · simp [hq]

private lemma mem_eigenformsAt_iff : f ∈ eigenformsAt V κ w t ↔ ∀ hw : w.IsSplit,
    f ∈ sphericalAt (V.formTranslation κ) w ∧
      ∀ j : ℕ, heckeSplit (V.formTranslation κ) hw j f = t j • f := by
  simp only [eigenformsAt, Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_eqLocus,
    LinearMap.smul_apply, LinearMap.id_apply]

/-- A form in `eigenformsAt V κ w t`, for a split place `w`, has the Hecke polynomial
`heckePoly w.q (card n) t` at `w`. -/
lemma hasHeckePolyAt_of_mem_eigenformsAt (hf_mem : f ∈ eigenformsAt V κ w t) (hw : star w ≠ w) :
    HasHeckePolyAt f.val w hw (heckePoly w.q (card n) t) := by
  -- At the split place `w`, `hf_mem` says that `f` is spherical and that `T_{w,j} f = t j • f`.
  obtain ⟨hf_sph, hf_eig⟩ := mem_eigenformsAt_iff.mp hf_mem hw
  exact (hasHeckePolyAt_iff hw).mpr ⟨hf_sph, t, rfl, hf_eig⟩

/-- A form lies in the isotypic space `x` exactly when, at all but finitely many places `w`, it lies
in `eigenformsAt V κ w` for the chosen eigenvalues `x.heckeEigenvalues w`. -/
lemma Isotypic.mem_iff_eventually :
    f ∈ x.val ↔ ∀ᶠ w : FinPlace E in cofinite, f ∈ eigenformsAt V κ w (x.heckeEigenvalues w) :=
  x.exists_heckeEigenvalues.choose_spec f

/-- An operator `a` in `localGroupAlgebra v`, the algebra generated by the translations supported at
one place `v` and its conjugate, maps the isotypic space `x` into itself. -/
lemma Isotypic.map_mem (ha : a ∈ localGroupAlgebra v) (hf : f ∈ x.val) : a f ∈ x.val := by
  rw [mem_iff_eventually] at hf ⊢
  -- at a place `w` away from `v`, the operator `a` commutes with the translations supported at `w`
  filter_upwards [eventually_notMem_star_notMem 1 {v}, hf] with w hw hfw
  have h_comm (g : Gf E n) (hg : g ∈ supportedOn n {w}) :
      a (V.formTranslation κ g f) = V.formTranslation κ g (a f) := by
    have hg_off : g ∈ trivialOn n {v} := by grind [mem_supportedOn, mem_trivialOn, star_star]
    exact (LinearMap.congr_fun (commute_of_mem_localGroupAlgebra ha hg_off).eq f).symm
  -- hence it keeps the vectors fixed by `maxCompactAt n w` and the eigenspaces of the `T_{w,j}`
  refine mem_eigenformsAt_iff.mpr fun hw_split ↦ ?_
  obtain ⟨hf_sph, hf_eig⟩ := mem_eigenformsAt_iff.mp hfw hw_split
  refine ⟨?_, fun j ↦ ?_⟩
  · -- `maxCompactAt n w` is supported at `w`, so its elements commute with `a` on `f`
    simp_all [← h_comm]
  · rw [← map_heckeSplit _ _ a h_comm, hf_eig j, map_smul]

/-- A nonzero form `f` in the isotypic space `x` is an eigenform for the Hecke polynomials
`x.heckePolyAt`. The hypothesis `HasPrimitiveRoot5040 E` (`E` contains a primitive 5040th root of
unity) makes every place of prime norm split. -/
lemma Isotypic.isEigenform [HasPrimitiveRoot5040 E] (hf : f ∈ x.val) (hf_ne : f ≠ 0) :
    IsEigenform f.val x.heckePolyAt := by
  exact ⟨by simpa using hf_ne, (mem_iff_eventually.mp hf).mono fun w hf_w hq_prime ↦
    ⟨isSplit_of_q_prime hq_prime, hasHeckePolyAt_of_mem_eigenformsAt hf_w _⟩⟩

/-- A nonzero form of maximal level off `S` that has Hecke polynomial `P w` at every split `w` with
`w, w̄ ∉ S` lies in some isotypic space. -/
lemma exists_isotypic_of_isSphericalOff {P : FinPlace E → Polynomial ℂ}
    (hf_sph : IsSphericalOff S f.val P) :
    ∃ x : Isotypic V κ, f ∈ x.val ∧ f ≠ 0 := by
  obtain ⟨hf_ne, -, h_eig⟩ := hf_sph
  -- `t w j` is the eigenvalue of `T_{w,j}` on `f`
  have h_sph_eig : ∀ (w : FinPlace E) (hw : star w ≠ w), w ∉ S → star w ∉ S →
      f ∈ sphericalAt (V.formTranslation κ) w ∧ ∃ t : ℕ → ℂ, P w = heckePoly w.q (card n) t ∧
        ∀ j : ℕ, heckeSplit (V.formTranslation κ) hw j f = t j • f :=
    fun w hw hwS hwS' ↦ (hasHeckePolyAt_iff hw).mp (h_eig w hw hwS hwS')
  choose! h_sph t h_poly h_val using h_sph_eig
  have h_ev : ∀ᶠ w in cofinite, f ∈ eigenformsAt V κ w (t w) := by
    filter_upwards [eventually_notMem_star_notMem 1 S] with w ⟨hwS, hwS', _⟩
    exact mem_eigenformsAt_iff.mpr fun hw_split ↦
      ⟨h_sph w hw_split hwS hwS', h_val w hw_split hwS hwS'⟩
  -- the forms with the eigenvalues `t w` at almost all `w` make up a subspace
  let U : Submodule ℂ (V.forms κ) :=
    .ofLinearComb {g : V.forms κ | ∀ᶠ w in cofinite, g ∈ eigenformsAt V κ w (t w)} ⟨0, by simp⟩
      fun g₁ hg₁ g₂ hg₂ c₁ c₂ ↦ (hg₁.out.and hg₂.out).mono fun _ ⟨hw₁, hw₂⟩ ↦
        add_mem (smul_mem _ c₁ hw₁) (smul_mem _ c₂ hw₂)
  exact ⟨⟨U, t, fun _ ↦ .rfl⟩, h_ev, by simpa using hf_ne⟩

/-! ### Independence and the attached Galois representation -/

/-- Let `s` be a set of isotypic subspaces of `V.forms κ`, where an isotypic subspace is one given
by a system of Hecke eigenvalues at all finite places: it consists of the forms that are eigenforms
with those eigenvalues at all but finitely many places. Then these subspaces are independent, so
their sum is direct. -/
lemma Isotypic.iSupIndep_val {s : Set (Isotypic V κ)} : iSupIndep fun x : s ↦ x.val.val := by
  -- Let a finite sum of forms `φ x ∈ x` vanish. At almost all places every `φ x` is an eigenform
  -- with the eigenvalues chosen for `x`. The joint eigenspaces of the Hecke operators at these
  -- places are independent, and the eigenvalues at these places determine `x`.
  refine (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr fun s' φ hφ_mem ↦ ?_
  let Good (w : FinPlace E) : Prop :=
    ∀ x ∈ s', φ x ∈ eigenformsAt V κ w (x.val.heckeEigenvalues w)
  have good_ev : ∀ᶠ w in cofinite, Good w :=
    s'.eventually_all.mpr fun x hx ↦ mem_iff_eventually.mp (hφ_mem x hx)
  -- `W`: the split places where every `φ x` lies in the chosen eigenspaces of `x`
  let W : Type := {w : FinPlace E // star w ≠ w ∧ Good w}
  let T (w : W) (j : ℕ) : Module.End ℂ (V.forms κ) :=
    heckeSplit (V.formTranslation κ) w.prop.left j
  have joint_indep : iSupIndep fun t : W → ℕ → ℂ ↦ ⨅ w, ⨅ j, (T w j).eigenspace (t w j) :=
    .iInf (fun (w : W) (t : ℕ → ℂ) ↦ ⨅ j, (T w j).eigenspace (t j)) fun w ↦
      .iInf (fun j ↦ (T w j).eigenspace) fun j ↦ (T w j).eigenspaces_iSupIndep
  let eigenvalues (x : s) (w : W) : ℕ → ℂ := x.val.heckeEigenvalues w.val
  -- the eigenvalues at the places of `W`, that is at almost all split places, determine `x`
  have h_inj : eigenvalues.Injective := by
    intro x y hxy
    have h_ev : ∀ᶠ w in cofinite,
        eigenformsAt V κ w (x.val.heckeEigenvalues w) =
          eigenformsAt V κ w (y.val.heckeEigenvalues w) := by
      refine good_ev.mono fun w hw ↦ iInf_congr fun hw_split ↦ ?_
      have h_eq : x.val.heckeEigenvalues w = y.val.heckeEigenvalues w :=
        congrFun hxy ⟨w, hw_split, hw⟩
      rw [h_eq]
    refine Subtype.ext (Subtype.ext (Submodule.ext fun g ↦ ?_))
    simp only [mem_iff_eventually]
    exact eventually_congr (h_ev.mono fun w hw ↦ by rw [hw])
  refine (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp (joint_indep.comp h_inj) s' φ ?_
  -- each `φ x` lies in the joint eigenspace of the `T_{w,j}` for the eigenvalues of `x`
  intro x hx
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Function.comp_apply]
  rintro ⟨w, hw_split, hw_good⟩
  exact (mem_eigenformsAt_iff.mp (hw_good x hx) hw_split).right

/-- If some representation is attached to the Hecke polynomials of the isotypic space `x`, then
the chosen `x.galRep` is attached to them. -/
lemma Isotypic.attached_galRep_of_exists [Algebra E Ω]
    (h_exists : ∃ r : GalRep ℓ E n, Attached x.heckePolyAt r) :
    Attached x.heckePolyAt x.galRep :=
  Classical.epsilon_spec h_exists

/-- If the isotypic space `x` on the standard definite space `V` holds a form `f ≠ 0`, then some
Galois representation is attached to the Hecke polynomials of `x`. Here `Ω` is the algebraic
closure of `ℚ`, an `E`-algebra, and a representation is a homomorphism `Gal(Ω/E) → GL_n(ℚ̄_ℓ)`. -/
lemma Isotypic.exists_attached [Algebra E Ω] [Nonempty n] [V.IsStd] [WeilData E] (hf : f ∈ x.val)
    (hf_ne : f ≠ 0) : ∃ r : GalRep ℓ E n, Attached x.heckePolyAt r := by
  -- `V` is the standard space and `f` an eigenform on it, so `sphericalCompat_std` gives an
  -- attached representation; its existence clause does not depend on the place, so any place
  -- will do
  exact (sphericalCompat_std Classical.ofNonempty).exists_attached
    (by simpa only [← Space.IsStd.eq_stdSpace V] using f.prop) (isEigenform hf hf_ne)

/-- If the isotypic space `x` on the standard definite space `V` holds a form `f ≠ 0`, then
`x.galRep` is attached to its Hecke polynomials. -/
lemma Isotypic.attached_galRep [Algebra E Ω] [Nonempty n] [V.IsStd] [WeilData E] (hf : f ∈ x.val)
    (hf_ne : f ≠ 0) : Attached x.heckePolyAt x.galRep :=
  attached_galRep_of_exists (Isotypic.exists_attached hf hf_ne)

end New.Patching

end
