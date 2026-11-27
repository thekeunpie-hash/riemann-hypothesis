module

import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
import TauCeti.LinearAlgebra.Pi
public import Lib.Shimura.Uniformisation.TorusModel
import Lib.Adelic.Adeles.StrongApproximation
import Lib.Base
import Lib.PadicComparison.Descent.TestCategory
import Lib.Shimura.HeckeTower.Model
import Lib.Shimura.Uniformisation.LieExponential
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.NumberTheory.NumberField.Countable
public import Lib.Shimura.IntegralModel.UniversalFamily
import Lib.General.Geometry.SerreTheorem
import Lib.Shimura.TraceFormula.DefiniteTrace

section
/-!
# Every full complex object is modelled on a point (g, ℓ)

From a complex point of a family of abelian schemes back to linear algebra: an object `x` over `ℂ`
with structure map `Φ v₀` (the complex embedding of `E` at the fixed infinite place `v₀`) on `𝓞 E`
and a full structure `e` (a trivialisation of all torsion, `New.ThetaObject.FullLevelStructure`) is
a complex torus described by an adelic frame `g` and a reflection `ℓ`.

* `New.Variety.exists_torusModel`: a polarised period map on `ℂ^d` for `(g, ℓ)` and a model of `x`
  on it whose torsion points are those of `e`, with `ℓ` a reflection.
* `New.Variety.exists_torusModel_of_isPeriodMap`: the same model on a given period map `Q` whose
  exponential lifts the torsion points of `e`; the frame is found from the Weil pairing of `e`.

`New.ThetaObject.TorusModel` is a model of `x` on a given polarised period map `Q`
(`New.ThetaTori.PeriodMap`). It is a uniformisation of `x.groupScheme` whose kernel is the period
lattice.

Notions from other files:
* `New.ψf`: the additive character of the finite adeles with ψ_f(x) = exp(2πi Tr_{E/ℚ}(a)) for any a
  in E with x − a integral. In the code `𝐞 t` is exp(2πi t).
* `New.ThetaObject.groupScheme`: The group scheme with O_E-action of an object x over S: the
  pull-back of the abelian scheme of the family along x : S → base.
* `New.ThetaObject.baseHom`: For an object x over Spec R, the ring homomorphism O_E → R induced by x
  and the structure morphism of the base of the family to Spec O_E.
* `New.ThetaObject`: An object of the family X over a scheme T: a morphism from T to the base of X.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` for sources.
-/

@[expose] public section

open CategoryTheory NumberField Matrix FourierTransform LinearMap BilinForm Complex OrzechProperty
  Submodule ContinuousLinearMap Circle RingOfIntegers Finset

namespace New.Variety

/- `x` is an object over `ℂ` of the family `X` over `Z`, and `e` is a full structure on it. -/
variable {E : Type} [Field E] [CMBase E] {D : PEL E} {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {x : ThetaObject X (AlgebraicGeometry.Spec ⟨ℂ⟩)} (e : x.FullLevelStructure)

/-- Let `u` uniformise `x.groupScheme`, with theta coordinates `θ` of type `(B, χ)` for
`x.lineBundle`, and let the torsion point of `e` at the class of `m *ᵥ y` be `u.expMap (Q y)` for
each `y` in `Eⁿ`. Then there is a unit `ε` (from the Weil pairing of `e`) such that on vectors of
`Eⁿ`, `𝐞` of the Riemann form of `B` pulled back by `Q` is `ψf` of the form `xiForm D.ξ`,
`(a, b) ↦ D.ξ · bᴴ a` on adelic vectors (`y` enters as `frameCoords 1 y`), with the matrix
`ε mᴴ m`. -/
lemma exists_fourierChar_riemannForm_eq_ψf_xiForm {V : Type} [FinComplexSpace V]
    {m : Matrix D.Index D.Index (𝔸f E)} (u : Uniformisation x.groupScheme V)
    (Q : RealVectors E D.Index ≃L[ℝ] V)
    (h_ev : ∀ y : D.Index → E,
      e.torsionPoint (torsionClass (m *ᵥ frameCoords 1 y)) = u.expMap (Q (toRealVectors y)))
    {B : ThetaTori.LatticeForm u.lattice} {χ : V → ℂ} {θ : V → D.dualTorsion → ℂ}
    (h_theta : HasThetaCoords u.lattice (atGeneric u.expMap) x.lineBundle B χ θ) :
    ∃ ε : (Ô ℚ)ˣ, ∀ y z : D.Index → E,
      𝐞 (LinearMap.BilinForm.congr Q.toLinearEquiv.symm B.riemannForm (toRealVectors y)
          (toRealVectors z)) =
        ψf E (xiForm D.ξ ((finAdeleIncl ℚ E ε • mᴴ * m) *ᵥ frameCoords 1 y) (frameCoords 1 z)) := by
  obtain ⟨ε, h_pair⟩ := e.weil_pairing 1
  refine ⟨ε, fun y z ↦ ?_⟩
  -- Take `N` with `N m y`, `N m z` integral and write `y = N y'`, `z = N z'`; then `N²` kills
  -- the classes of `m y'` and `m z'`.
  obtain ⟨N, hN, h_int⟩ := exists_forall_mul_mem_Ô (m *ᵥ frameCoords 1 y ⊕ᵥ m *ᵥ frameCoords 1 z)
  have hN_int : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  obtain ⟨y', rfl⟩ := DivisibleBy.surjective_smul (D.Index → E) ℤ hN_int y
  obtain ⟨z', rfl⟩ := DivisibleBy.surjective_smul (D.Index → E) ℤ hN_int z
  obtain ⟨hy', hz'⟩ :
      (N * N) • torsionClass (m *ᵥ frameCoords 1 y') = 0 ∧
      (N * N) • torsionClass (m *ᵥ frameCoords 1 z') = 0 := by
    simpa [← nsmul_eq_mul, smul_smul, ← torsionClass_eq_zero (n := D.Index), ← Pi.smul_def,
      mulVec_smul] using h_int
  -- lifts `Ty`, `Tz` of the translations by the two torsion points acting on sections of
  -- `x.lineBundle.pow (N * N)`
  obtain ⟨Ty, hTy⟩ := e.exists_isTranslationLift hy'
  obtain ⟨Tz, hTz⟩ := e.exists_isTranslationLift hz'
  -- the scalar by which `Ty` and `Tz` commute is the Weil pairing of the two classes
  obtain ⟨c, rfl, h_comm⟩ :=
    h_pair (N * N) (m *ᵥ frameCoords 1 y') (m *ᵥ frameCoords 1 z') hy' hz'
  specialize h_comm Ty Tz hTy hTz
  rw [h_ev] at hTy hTz
  -- the same scalar is the Riemann phase, by `lift_commutator_iff_weil_pairing`
  have h_phase : (ψf E (finAdeleIncl ℚ E ε *
        ((N * N : ℕ) * xiForm D.ξ (m *ᵥ frameCoords 1 y') (m *ᵥ frameCoords 1 z'))) : ℂ) =
      𝐞 ((N * N : ℕ) * B.riemannForm (Q (toRealVectors y')) (Q (toRealVectors z'))) := by
    simpa using (lift_commutator_iff_weil_pairing u h_theta hTy hTz).mp h_comm
  -- the factor `N²` is shared between the two arguments, and `mᴴ` moves across the form
  calc _ = 𝐞 ((N * N : ℕ) * B.riemannForm (Q (toRealVectors y')) (Q (toRealVectors z'))) := by
        simp [← nsmul_eq_mul]
    _ = ψf E (finAdeleIncl ℚ E ε * ((N * N : ℕ) *
          xiForm D.ξ (m *ᵥ frameCoords 1 y') (m *ᵥ frameCoords 1 z'))) := Circle.ext h_phase.symm
    _ = _ := by
        simp [star_trivial, xiForm, star_mulVec_dotProduct, ← nsmul_eq_mul, mul_left_comm,
          mulVec_smul, smul_mulVec]

/-- Let `R` be a real bilinear form on `(E ⊗ ℝ)ⁿ` and `M` an `n × n` matrix of finite adeles such
that `𝐞 (R y z) = ψf (ξ · zᴴ M y)` for all `y`, `z` in `Eⁿ`, where `ψf` is the standard additive
character of the finite adeles and `ξ = D.ξ`, with `Φ v₀ ξ` of zero real part and positive imaginary
part. Then `M` is the image of a matrix `β` over `E`, and `R` is the polarisation form of `β`,
namely `(y, z) ↦ Σ_v 2 Re(Φ_v(ξ) z_vᴴ Φ_v(β) y_v)` summed over the infinite places `v`. -/
lemma exists_map_eq_and_eq_polarisationForm_of_fourierChar_eq
    (R : LinearMap.BilinForm ℝ (RealVectors E D.Index)) (M : Matrix D.Index D.Index (𝔸f E))
    (h_weil : ∀ y z : D.Index → E,
      𝐞 (R (toRealVectors y) (toRealVectors z)) =
        ψf E (xiForm D.ξ (M *ᵥ frameCoords 1 y) (frameCoords 1 z))) :
    ∃ β : D.Index → D.Index → E, (of β).map (↑) = M ∧ R = polarisationForm D (of β) := by
  -- Values of `ψf` are `𝐞` of rational numbers, so `R` is rational on `Eⁿ`: `r z y` is the
  -- rational value of `R y z`.
  have h_rat (z y : D.Index → E) : ∃ q : ℚ, q = R (toRealVectors y) (toRealVectors z) := by
    obtain ⟨a, j, hj⟩ : ∃ (a : ℚ) (j : ℤ), R (toRealVectors y) (toRealVectors z) - a = j := by
      simp only [← fourierChar_eq_one_iff, AddChar.map_sub_eq_div, div_eq_one]
      exact ⟨_, h_weil y z⟩
    exact ⟨j + a, mod_cast (eq_add_of_sub_eq hj).symm⟩
  choose r hr using h_rat
  -- Trace duality: the `ℚ`-linear form `t ↦ R (ξ⁻¹ t e_j, e_i)` is `t ↦ tr (β i j * t)`.
  have h_dual (i j : D.Index) : ∃ c : E, ∀ t : E,
      Algebra.trace ℚ E (c * t) = r (Pi.single i 1) (Pi.single j (D.ξ⁻¹ * t)) := by
    let f : E →+ ℚ := AddMonoidHom.mk' (fun t ↦ r (Pi.single i 1) (Pi.single j (D.ξ⁻¹ * t)))
      (by simp [hr, mul_add, Pi.single_add, ← Rat.cast_inj (α := ℝ)])
    obtain ⟨c, hc⟩ := (toDual _ (traceForm_nondegenerate ℚ E)).surjective f.toRatLinearMap
    exact ⟨c, fun t ↦ by simpa [LinearMap.BilinForm.toDual_def, f] using LinearMap.congr_fun hc t⟩
  choose β h_tr using h_dual
  have hξ : D.ξ ≠ 0 := by
    obtain ⟨h_im_pos, -⟩ := D.xi_im_pos_and_re_eq_zero v₀
    exact ne_zero_of_map (ne_of_apply_ne im h_im_pos.ne')
  -- `ψf` separates adeles, and it is enough to test against the dense set of `t` in `E`.
  have hβ : (of β).map (↑) = M := by
    refine ext fun i j ↦ ?_
    have h_dense (t : E) :
        ψf E (algebraMap E (𝔸f E) t * (of β).map (↑) i j) =
          ψf E (algebraMap E (𝔸f E) t * M i j) := by
      simp [ψf_coe, ← map_mul, mul_comm t, xiForm, frameCoords, dotProduct, mulVec, apply_ite,
        mul_comm (M i j), ← mul_assoc, hξ, h_tr, hr, h_weil, Pi.single_apply]
    exact eq_of_forall_ψf_mul_eq (denseRange_algebraMap_finAdele.eq fun t ↦ h_dense t)
  -- By density take `y` in `Eⁿ`. By `h_weil`, `𝐞` of the linear form
  -- `R y - polarisationForm D β y` is `1` on the dense set `Eⁿ`, hence everywhere, so the form
  -- is `0`.
  have hR : R = polarisationForm D (of β) := by
    refine ext (isClosed_property denseRange_toRealVectors
      (R.eqLocus _).isClosed_of_finiteDimensional fun y ↦ ?_)
    refine sub_eq_zero.mp (eq_zero_of_forall_fourierChar_eq_one _ (denseRange_toRealVectors.eq ?_))
    simp [h_weil, ← hβ, 𝐞.map_sub_eq_div, ← ψf_coe, xiForm, frameCoords, dotProduct, mulVec]
  exact ⟨β, hβ, hR⟩

/-- Let `x` over `ℂ` have structure map `Φ v₀` on `𝓞 E` and full structure `e`, let `u` uniformise
`x.groupScheme` by `V`, and let `Q : (E ⊗ ℝ)ⁿ ≃ V` be a period map for `ℓ` (`i` acts as `i ℓ` at
`v₀`, as `i` elsewhere) with `u.expMap ∘ Q` `𝓞 E`-linear, sending `y` in `Eⁿ` to the torsion point
of `e` at the class of `m *ᵥ y`, and with `u.lattice` in `Q (Eⁿ)`. Then for some adelic frame `g`, a
polarised period map `Y` for `(g, ℓ)` on `V` has a model `M` of `x` with `e`'s torsion points. -/
lemma exists_torusModel_of_isPeriodMap
    (hρ : ∀ c : 𝓞 E, x.baseHom c = Φ v₀ c.val) {V : Type} [FinComplexSpace V]
    {ℓ : Matrix D.Index D.Index ℂ} {m : Matrix D.Index D.Index (𝔸f E)}
    (u : Uniformisation x.groupScheme V) (Q : RealVectors E D.Index ≃L[ℝ] V)
    (h_per : IsPeriodMap ℓ Q)
    (h_smul : ∀ (c : 𝓞 E) (w : RealVectors E D.Index),
      u.expMap (Q (cmEmbedding c.val • w)) = c • u.expMap (Q w))
    (h_ev : ∀ y : D.Index → E,
      e.torsionPoint (torsionClass (m *ᵥ frameCoords 1 y)) = u.expMap (Q (toRealVectors y)))
    (h_lat : ∀ z ∈ u.lattice, ∃ y : D.Index → E, Q (toRealVectors y) = z) :
    ∃ g : GL D.Index (𝔸f E), ∃ Y : ThetaTori.PeriodMap D g ℓ V, ∃ M : x.TorusModel Y,
      M.fullStructure.torsionPoint = e.torsionPoint := by
  -- Appell–Humbert: the coordinates of `x.lineBundle` are theta functions `θ` of a type `(B, χ)`
  -- with positive Riemann form; `R` is that form on `(E ⊗ ℝ)ⁿ`. The Weil pairing computes `R` on
  -- vectors of `Eⁿ` and shows that `R` is the polarisation form of a matrix `β` over `E` with
  -- image `M = ε mᴴ m`. Nondegeneracy makes `m` invertible, and `m⁻¹` is the frame.
  -- the parallelogram law, the first of the class laws of `x.lineBundle`
  obtain ⟨h_par, -⟩ := x.hasClassLaws
  obtain ⟨B, χ, θ, h_theta, h_pos⟩ := u.appell_humbert x.isProjEmbedding h_par
  obtain ⟨ε, h_weil⟩ := exists_fourierChar_riemannForm_eq_ψf_xiForm e u Q h_ev h_theta
  let R : LinearMap.BilinForm ℝ (RealVectors E D.Index) := congr Q.toLinearEquiv.symm B.riemannForm
  let M : Matrix D.Index D.Index (𝔸f E) := finAdeleIncl ℚ E ε • mᴴ * m
  obtain ⟨β, hβ, hR⟩ := exists_map_eq_and_eq_polarisationForm_of_fourierChar_eq R M h_weil
  -- The Riemann form is nondegenerate, so `β`, then `M` and its right factor `m`, are invertible.
  have hβ_inj : Function.Injective (of β).mulVec := by
    intro y z h_mulVec
    have h_eq : R (toRealVectors y) = R (toRealVectors z) :=
      ext (denseRange_toRealVectors.eq (by simp [hR, h_mulVec]))
    exact toRealVectors_injective
      (R.ker_eq_bot.mp (h_pos.nondegenerate.congr Q.toLinearEquiv.symm).ker_eq_bot h_eq)
  have hM : IsUnit M := by
    rw [← hβ]
    exact (mulVec_injective_iff_isUnit.mp hβ_inj).map (RingHom.mapMatrix _)
  obtain ⟨m, rfl⟩ : IsUnit m := isUnit_of_mul_isUnit_right hM
  -- `m⁻¹` is a frame for `β`, as `mᴴ (ε • 1) m = β`
  have h_gram : m.valᴴ * (finAdeleIncl ℚ E ε • 1) * m.val = (of β).map (algebraMap E (𝔸f E)) := by
    simp [hβ, M]
  replace h_ev (y : D.Index → E) :
      e.torsionPoint (frameTorsionClass m⁻¹ y) = u.expMap (Q (toRealVectors y)) := by
    simpa [frameCoords, frameTorsionClass] using h_ev y
  refine ⟨m⁻¹,
    { formMatrix := of β, realEquiv := Q, automorphyForm := B, isFrameFor := ⟨ε,
      gram_inv_of_gram_eq h_gram⟩
      isPeriodMap := h_per, re_symm := h_theta.isAppellHumbert.re_symm
      riemannForm_eq := congr_fun₂ hR, isPosRiemann := h_pos },
    { baseHom_eq := hρ, uniformisation := u, χ := χ, θ := θ, hasThetaCoords := h_theta
      equivariant := h_smul, level_eq := ?_, lattice_eq := ?_ }, ?_⟩
  · simp [e.levelPoints_eq, ThetaTori.PeriodMap.torsionLift, ← h_ev]
  · -- a vector of `u.lattice` is a `Q (toRealVectors y)` by `h_lat`, and `e.torsionPoint` is
    -- injective
    ext w
    suffices h_iff : u.expMap w = 0 ↔
        ∃ y : D.Index → E, u.expMap (Q (toRealVectors y)) = 0 ∧ Q (toRealVectors y) = w by
      simpa [mem_classLattice, ← e.injective.eq_iff, h_ev] using h_iff
    refine ⟨fun hw ↦ ?_, fun ⟨y, hy, hyw⟩ ↦ by rwa [← hyw]⟩
    obtain ⟨y, rfl⟩ := h_lat w ((u.eq_zero_iff w).mpr hw)
    exact ⟨y, hw, rfl⟩
  · ext
    simp [ThetaObject.TorusModel.fullStructure, ← h_ev]

/-- Let `u` uniformise `x.groupScheme` and let the real-linear map `P` lift the torsion points of
`e` on the vectors of `½ (𝓞 E)ⁿ`: for `y` in `Eⁿ` with `2 y` integral, `u.expMap (P y)` is the
torsion point of `e` at the class of `y`. Then `P (Eⁿ)` contains the lattice `u.lattice`. -/
lemma lattice_subset_range_of_expMap_eq_torsionPoint {V : Type} [FinComplexSpace V]
    (u : Uniformisation x.groupScheme V) (P : RealVectors E D.Index →ₗ[ℝ] V)
    (hP : ∀ y : D.Index → E,
      2 • y ∈ (frameTorsionClass 1).ker →
      u.expMap (P (toRealVectors y)) = e.torsionPoint (frameTorsionClass 1 y)) :
    ∀ z ∈ u.lattice, ∃ y : D.Index → E, P (toRealVectors y) = z := by
  let _ : Module ℚ V := .compHom V (algebraMap ℚ ℝ)
  -- `N` is the image of the lattice in `V` modulo the `ℚ`-subspace `P (Eⁿ)`
  let p : (D.Index → E) →ₗ[ℚ] V := (P.toAddMonoidHom.comp toRealVectors).toRatLinearMap
  let N : Submodule ℤ (V ⧸ p.range) := u.lattice.map (p.range.mkQ.restrictScalars ℤ)
  -- `N` is stable under `½`: half of a lattice vector maps to a `2`-torsion point
  -- `e.torsionPoint (frameTorsionClass 1 y)`
  have h_half : ∀ w ∈ N, (2⁻¹ : ℚ) • w ∈ N := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨a, rfl⟩ : ∃ a : V, (2 : ℚ) • a = z := MulAction.surjective₀ (two_ne_zero' ℚ) z
    have h_tors : 2 • u.expMap a = 0 := by
      rwa [two_smul, ← map_add, ← two_smul ℚ a, ← u.eq_zero_iff]
    obtain ⟨l, hl⟩ := x.exists_apply_eq_of_torsion e.injective (u.expMap a) ⟨2, two_ne_zero, h_tors⟩
    obtain ⟨y, rfl⟩ : ∃ y : D.Index → E, frameTorsionClass 1 y = l := frameTorsionClass_surjective l
    have h_two_y : 2 • y ∈ (frameTorsionClass 1).ker := by
      simp only [LinearMap.mem_ker, ← e.injective.eq_iff, map_nsmul, hl, h_tors, map_zero]
    -- `a - P y` lies in the lattice: both map to the same point, as `P` lifts it (`hP`)
    refine ⟨a - P (toRealVectors y), ?_, by simp [p]⟩
    exact (u.eq_zero_iff _).mpr (by rw [map_sub, hP y h_two_y, hl, sub_self])
  -- `N` is finitely generated and `½` is not integral over `ℤ`, so `N = 0`
  have hN : N = ⊥ := by
    by_contra hN
    obtain ⟨k, hk⟩ : ∃ k : ℤ, algebraMap ℤ ℚ k = 2⁻¹ := IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_smul_mem_submodule N hN .of_finite (2⁻¹ : ℚ) h_half)
    simpa using congrArg Rat.den hk
  simpa [N, p, Submodule.eq_bot_iff] using hN

/-- Let `u` uniformise `x.groupScheme` by `Fin (abelianDim E D.Index) → ℂ`, and let `d` be the real
basis of `E ⊗ ℝ` (as `InfinitePlace E → ℂ`) given by an integral basis of `E`. The action of
`𝓞 E` on `x.groupScheme` lifts through `u` to an `ℝ`-linear map `G` from `E ⊗ ℝ` to the
complex-linear maps of that space: `u.expMap (G c z) = c • u.expMap z` for `c` in `𝓞 E`. -/
lemma exists_expMap_apply_cmEmbedding_eq_smul
    (u : Uniformisation x.groupScheme (Fin (abelianDim E D.Index) → ℂ))
    (d : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ))
    (hd : ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 E), d i = cmEmbedding (basis E i).val) :
    ∃ G : (InfinitePlace E → ℂ) →ₗ[ℝ]
        (Fin (abelianDim E D.Index) → ℂ) →L[ℂ] Fin (abelianDim E D.Index) → ℂ,
      ∀ (c : 𝓞 E) (z : Fin (abelianDim E D.Index) → ℂ),
        u.expMap (G (cmEmbedding c) z) = c • u.expMap z := by
  -- lift each element of the integral basis to a linear map of `Fin (abelianDim E D.Index) → ℂ`,
  -- and extend `ℝ`-linearly
  have h_lift (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
      ∃ F : (Fin (abelianDim E D.Index) → ℂ) →L[ℂ] _, ∀ z : Fin (abelianDim E D.Index) → ℂ,
        u.expMap (F z) = basis E i • u.expMap z := by
    -- `using!`: holomorphy of the composite matches what `u.universal` asks only after unfolding
    -- `IsAddMonHom.addMonoidHom` and `HolomorphicAt`
    simpa using
      u.universal ((IsAddMonHom.addMonoidHom (basis E i • 𝟙 x.groupScheme) _).comp u.expMap)
        (by simpa only [atGeneric_eq] using! (u.immersive 0).1.comp_hom _)
  choose F hF using h_lift
  refine ⟨d.constr ℝ F, fun c z ↦ ?_⟩
  -- expand `c` in the integral basis: both sides are the same `ℤ`-combination over the basis
  rw [← (basis E).sum_repr c]
  -- the `↓` forms and `-zsmul_eq_mul` keep each coefficient a `ℤ`-multiple of `d i`, which
  -- `d.constr` sends to `F i`; with plain `sum_smul` the coefficients become products `↑r * d i`
  simp [← hd, hF, ↓sum_smul, -zsmul_eq_mul, ↓map_sum]

/-- Let `u` uniformise `x.groupScheme` by `V`, and let `Q : (E ⊗ ℝ)ⁿ ≃ V` be such that
`u.expMap ∘ Q` is `𝓞 E`-linear and lifts the torsion points of `e` on the vectors of `½ (𝓞 E)ⁿ`.
Then there is an adelic matrix `m` such that `u.expMap (Q y)` is the torsion point of `e` at the
class of `m *ᵥ y` for every `y` in `Eⁿ`. -/
lemma exists_matrix_torsionPoint_eq_expMap {V : Type} [FinComplexSpace V]
    (u : Uniformisation x.groupScheme V) (Q : RealVectors E D.Index ≃L[ℝ] V)
    (h_half : ∀ y : D.Index → E, 2 • y ∈ (frameTorsionClass 1).ker →
      u.expMap (Q (toRealVectors y)) = e.torsionPoint (frameTorsionClass 1 y))
    (h_smul : ∀ (c : 𝓞 E) (w : RealVectors E D.Index),
      u.expMap (Q (cmEmbedding c.val • w)) = c • u.expMap (Q w)) :
    ∃ m : Matrix D.Index D.Index (𝔸f E), ∀ y : D.Index → E,
      e.torsionPoint (torsionClass (m *ᵥ frameCoords 1 y)) = u.expMap (Q (toRealVectors y)) := by
  -- the points `u.expMap (Q y)` are torsion, so they are `e.torsionPoint (f y)`; `f` is
  -- `𝓞 E`-linear, so `f y` is the class of `m *ᵥ y` for an adelic matrix `m`
  have h_tors_pt (y : D.Index → E) :
      ∃ l : AdelicTorsion E D.Index, e.torsionPoint l = u.expMap (Q (toRealVectors y)) := by
    obtain ⟨k, hk, hky⟩ := exists_nsmul_adelicTorsion_eq_zero (frameTorsionClass 1 y)
    -- `-nsmul_eq_mul` keeps `k • y` a multiple by `k`, so that the linear maps pull `k` out
    exact x.exists_apply_eq_of_torsion e.injective _
      ⟨k, hk, by simpa [hky, -nsmul_eq_mul] using h_half (k • y)⟩
  choose f hf using h_tors_pt
  have hf_add (y y' : D.Index → E) : f (y + y') = f y + f y' := by
    simp [← e.injective.eq_iff, hf]
  have hf_smul (c : 𝓞 E) (y : D.Index → E) : f (c • y) = c • f y := by
    simp [← e.injective.eq_iff, hf, h_smul]
  obtain ⟨m, hm⟩ : ∃ m : Matrix D.Index D.Index (𝔸f E), ∀ y : D.Index → E,
      torsionClass (m *ᵥ frameCoords 1 y) = f y :=
    exists_matrix_torsionClass_eq ⟨⟨f, hf_add⟩, hf_smul⟩
  exact ⟨m, fun y ↦ by rw [hm, hf]⟩

/-- Let `u` uniformise `x.groupScheme` by `Fin (abelianDim E D.Index) → ℂ`, let `G` lift the action
of `𝓞 E` through `u`, and let `l j` lift the torsion point of `e` at the class of `e_j / 2`.
The real-linear map `P = ∑ j, (w ↦ G (w j) (2 l j))` lifts the torsion points of `e` on the
vectors of `½ (𝓞 E)ⁿ`: for `y` in `Eⁿ` with `2 y` integral, `u.expMap (P y)` is the torsion
point of `e` at the class of `y`. -/
lemma expMap_apply_toRealVectors_eq_torsionPoint_of_two_smul_mem_ker
    (u : Uniformisation x.groupScheme (Fin (abelianDim E D.Index) → ℂ))
    (G : (InfinitePlace E → ℂ) →ₗ[ℝ]
      (Fin (abelianDim E D.Index) → ℂ) →L[ℂ] Fin (abelianDim E D.Index) → ℂ)
    (hG : ∀ (c : 𝓞 E) (z : Fin (abelianDim E D.Index) → ℂ),
      u.expMap (G (cmEmbedding c) z) = c • u.expMap z)
    (l : D.Index → Fin (abelianDim E D.Index) → ℂ)
    (hl : ∀ j : D.Index,
      u.expMap (l j) = e.torsionPoint (frameTorsionClass 1 (Pi.single j 2⁻¹)))
    (y : D.Index → E) (hy : 2 • y ∈ (frameTorsionClass 1).ker) :
    u.expMap ((∑ j : D.Index, (coeLM ℝ).flip (2 • l j) ∘ₗ G ∘ₗ .proj j :
        RealVectors E D.Index →ₗ[ℝ] Fin (abelianDim E D.Index) → ℂ) (toRealVectors y)) =
      e.torsionPoint (frameTorsionClass 1 y) := by
  -- write `y = ∑ c j • e_j / 2` with `c j` integral
  have h_int : ∀ i : D.Index, ∃ c : 𝓞 E, (c : E) = 2 * y i := by
    simpa [ker_frameTorsionClass_one] using hy
  choose c hc using h_int
  have h_sum : y = ∑ j, c j • Pi.single j 2⁻¹ := by
    simp [funext_iff, Algebra.smul_def, hc, field, Pi.single_apply]
  simp [toRealVectors, hc, ← hG, ← hl, two_mul, congrArg (frameTorsionClass 1) h_sum]

/-- Let `u` uniformise `x.groupScheme` by `V = Fin (abelianDim E D.Index) → ℂ`. A real-linear map
`P` from `(E ⊗ ℝ)ⁿ` to `V` whose image of `Eⁿ` contains the lattice `u.lattice` is bijective: the
lattice spans `V`, and the two real dimensions agree. -/
lemma bijective_of_lattice_subset_range
    (u : Uniformisation x.groupScheme (Fin (abelianDim E D.Index) → ℂ))
    (P : RealVectors E D.Index →ₗ[ℝ] Fin (abelianDim E D.Index) → ℂ)
    (h_lat : ∀ z ∈ u.lattice, ∃ y : D.Index → E, P (toRealVectors y) = z) :
    Function.Bijective P := by
  have hP_onto : P.range = ⊤ := by
    -- the lattice spans `V` over `ℝ`
    refine eq_top_mono (span_le.mpr fun z hz ↦ ?_) (IsZLattice.span_top (K := ℝ) (L := u.lattice))
    obtain ⟨y, hy⟩ := h_lat z hz
    exact ⟨toRealVectors y, hy⟩
  have h_finrank : Module.finrank ℝ (RealVectors E D.Index) ≤
      Module.finrank ℝ (Fin (abelianDim E D.Index) → ℂ) := by
    simp [abelianDim.eq_1 E, mul_assoc, Module.finrank_pi_fintype]
  exact bijective_of_surjective_of_finrank_le P (range_eq_top.mp hP_onto) h_finrank

/-- Let `Q : (E ⊗ ℝ)ⁿ ≃ V` carry the action of `E ⊗ ℝ` on `(E ⊗ ℝ)ⁿ` to an action `G` on `V`, and
let `Q Y` be an eigenvector of `G` with eigenvalue `c v₀` for each `c`. Suppose that `Im Φ(β) ≠ 0`
for `β = D.β`, and that `G (star β) - Φ(β)` (through `x.baseHom`, which is `Φ v₀` on `𝓞 E`) sends
`Q w` to `(η ⬝ᵥ w_{v₀}) • Q Y` for a vector `η`. Then `Q` is a period map (`i` acts as `i ℓ` at
`v₀`, as `i` elsewhere) for the matrix `ℓ = (Y · v₀) η'ᵀ - 1`, where `η' = (I / Im Φ(β)) η`. -/
lemma isPeriodMap_vecMulVec_sub_one_of_sub_smul_eq
    (hρ : ∀ c : 𝓞 E, x.baseHom c = Φ v₀ c.val)
    {V : Type} [FinComplexSpace V] (G : (InfinitePlace E → ℂ) →ₗ[ℝ] V →L[ℂ] V)
    (Q : RealVectors E D.Index ≃L[ℝ] V)
    (hQ : ∀ (c : InfinitePlace E → ℂ) (w : RealVectors E D.Index), Q (c • w) = G c (Q w))
    (Y : RealVectors E D.Index) (hGY : ∀ c : InfinitePlace E → ℂ, G c (Q Y) = c v₀ • Q Y)
    (hβ : (Φ v₀ D.β.val).im ≠ 0) (η : D.Index → ℂ)
    (h_rank : ∀ w : RealVectors E D.Index,
      G (cmEmbedding (star D.β)) (Q w) - x.baseHom D.β • Q w = (η ⬝ᵥ (w · v₀)) • Q Y) :
    IsPeriodMap (vecMulVec (Y · v₀) ((Complex.I / (Φ v₀ D.β.val).im : ℂ) • η) - 1) Q := by
  refine fun w ↦ Q.eq_symm_apply.mp (ext fun j v ↦ ?_)
  -- Read `h_rank w` in coordinates, with `Φ(β) • Q w` split into real and imaginary parts: the
  -- terms with `Re Φ(β)` cancel, and dividing by `Im Φ(β) ≠ 0` solves for `Q⁻¹ (I • Q w)`.
  have h_single (a : ℂ) : a • Q Y = Q ((Pi.single v₀ a : InfinitePlace E → ℂ) • Y) := by
    simp [hQ, hGY]
  have h_coord :
      Q.symm (G (cmEmbedding (star D.β)) (Q w) - x.baseHom D.β • Q w) j v =
        Q.symm ((η ⬝ᵥ (w · v₀)) • Q Y) j v := by rw [h_rank w]
  by_cases hv : v = v₀
  · -- after `simp`, both sides are pairs of real linear equations in `Q⁻¹ (I • Q w) j v₀`
    simp [← hQ, h_single, hv, hρ, vecMulVec_mulVec, Complex.ext_iff,
      smul_eq_re_smul_add_im_smul (Φ v₀ _),
      sub_mulVec, smul_mulVec] at h_coord ⊢
    grind
  · -- away from `v₀` the same equations say `Q⁻¹ (I • Q w) j v = I • w j v`
    simp [D.emb_beta_eq_of_ne, ← hQ, h_single, hv, hρ, Complex.ext_iff,
      smul_eq_re_smul_add_im_smul (Φ v₀ _), sub_eq_zero] at h_coord ⊢
    grind

/-- Let `x` be an object over `ℂ` whose structure map on `𝓞 E` is `Φ v₀` (`hρ`), with full
structure `e`. Then there are an adelic frame `g`, a complex matrix `ℓ` and a dimension `d` such
that `x` has a model `m` on a polarised period map `Y` for `(g, ℓ)` on `ℂ^d`, whose torsion points
are those of `e`, and `ℓ` is a reflection: `ℓ = u wᵀ - 1` for vectors `u`, `w` with `w ⬝ᵥ u = 2`, so
`ℓ` fixes the line of `u` and is `-1` on the kernel of `w`. -/
lemma exists_torusModel
    (hρ : ∀ c : 𝓞 E, x.baseHom c = Φ v₀ c.val) :
    ∃ (g : GL D.Index (𝔸f E)) (ℓ : Matrix D.Index D.Index ℂ) (d : ℕ),
      ∃ Y : ThetaTori.PeriodMap D g ℓ (Fin d → ℂ), ∃ m : x.TorusModel Y,
      m.fullStructure.torsionPoint = e.torsionPoint ∧ IsReflection ℓ := by
  -- Uniformise `x.groupScheme` by `V = Fin (abelianDim E D.Index) → ℂ` and lift the action of `𝓞 E`
  -- to an action `G` of `E ⊗ ℝ` on `V`. The `2`-torsion points given by `e` define a
  -- `G`-equivariant isomorphism `Q : (E ⊗ ℝ)ⁿ → V`. By `X.signature`, the complex structure pulled
  -- back by `Q` is given by a reflection at `v₀`; then `exists_torusModel_of_isPeriodMap` gives the
  -- model.
  obtain ⟨u⟩ := x.isProjEmbedding.nonempty_uniformisation x.smoothOfRelativeDimension
  -- an integral basis of `E` is a real basis of `E ⊗ ℝ`
  obtain ⟨d, hd⟩ :
      ∃ d : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ),
        ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 E), d i = cmEmbedding (basis E i).val :=
    exists_mixedEquiv.imp' (mixedEmbedding.latticeBasis E).map (by aesop)
  have hβ : (Φ v₀ D.β.val).im ≠ 0 := by simpa [conj_eq_iff_im] using D.emb_star_beta_ne
  -- a Lie chart of `x.groupScheme` in which the signature condition `h_rk` holds
  obtain ⟨U, z_chart, m_chart, h_jac, h_rk⟩ := X.signature 0 x
  obtain ⟨G, hG⟩ := exists_expMap_apply_cmEmbedding_eq_smul u d hd
  -- `P` sends the `j`-th unit vector to twice a lift `l j` of the point `e.torsionPoint (e_j / 2)`
  choose l hl using fun j : D.Index ↦
    u.surjective (e.torsionPoint (frameTorsionClass 1 (Pi.single j 2⁻¹)))
  let P : RealVectors E D.Index →ₗ[ℝ] Fin (abelianDim E D.Index) → ℂ :=
    ∑ j, (coeLM ℝ).flip (2 • l j) ∘ₗ G ∘ₗ .proj j
  -- on vectors of `½ (𝓞 E)ⁿ`, `P` lifts the torsion points of `e`
  have hP := expMap_apply_toRealVectors_eq_torsionPoint_of_two_smul_mem_ker e u G hG l hl
  -- so `P (Eⁿ)` contains the lattice, and `P` is bijective
  have h_lat : ∀ z ∈ u.lattice, ∃ y : D.Index → E, P (toRealVectors y) = z :=
    lattice_subset_range_of_expMap_eq_torsionPoint e u P hP
  let Q : RealVectors E D.Index ≃L[ℝ] Fin (abelianDim E D.Index) → ℂ := (LinearEquiv.ofBijective P
    (bijective_of_lattice_subset_range u P h_lat)).toContinuousLinearEquiv
  have hG_mul : ∀ c c' : InfinitePlace E → ℂ, G (c * c') = G c * G c' := by
    refine G.map_mul_iff.mpr (ext_basis d d fun i j ↦ u.linear_ext ?_)
    simp [← map_mul, mul_smul, hd, hG]
  have hQ (c : InfinitePlace E → ℂ) (w : RealVectors E D.Index) : Q (c • w) = G c (Q w) := by
    simp [Q, P, hG_mul]
  -- the signature condition: `Q Y ≠ 0` is an eigenvector of `G` on `𝓞 E` (`hY_eigen`), and
  -- `G (star β) w - Φ(β) • w = ξ w • Q Y` for a linear form `ξ` on `V` (`hξ`); here `β = D.β`
  obtain ⟨Y, hY, hY_eigen, ξ, hξ⟩ := Q.surjective.exists.mp
    ((u.hasSignature_iff hG h_jac x.isGroupBaseChange (by simp) (ρ := x.baseHom)).mp h_rk)
  have hGY (c : InfinitePlace E → ℂ) : G c (Q Y) = c v₀ • Q Y := by
    rw [← d.sum_repr c]
    simp [sum_smul, mul_smul, hd, hY_eigen, hρ]
  let η (j : D.Index) : ℂ := ξ (Q (Pi.single j 1))
  -- apply `G (w k)` to `hξ` at the `k`-th unit vector and sum over `k`
  have h_rank (w : RealVectors E D.Index) :
      G (cmEmbedding (star D.β)) (Q w) - x.baseHom D.β • Q w = (η ⬝ᵥ (w · v₀)) • Q Y := by
    have h_sum :
        ∑ k, G (w k) (G (cmEmbedding (star D.β)) (Q (Pi.single k 1)) -
            x.baseHom D.β • Q (Pi.single k 1)) =
          ∑ k, G (w k) (ξ (Q (Pi.single k 1)) • Q Y) :=
      Finset.sum_congr rfl fun k _ ↦ congrArg (G (w k)) (by simpa using hξ (Q (Pi.single k 1)))
    simpa [η, hGY, ← hQ, smul_comm (w _), ← map_sum, ← smul_sum, smul_smul (ξ _),
      ← dotProduct.eq_1, ← pi_eq_sum_univ', ← sum_smul] using h_sum
  have h_smul (c : 𝓞 E) (w : RealVectors E D.Index) :
      u.expMap (Q (cmEmbedding c.val • w)) = c • u.expMap (Q w) := by simp [hQ, hG]
  -- `u.expMap ∘ Q` sends `y` to the torsion point of `e` at the class of `m *ᵥ y`
  obtain ⟨m, h_ev⟩ := exists_matrix_torsionPoint_eq_expMap e u Q hP h_smul
  -- the reflection fixes the line of `Y · v₀`; its linear form is a multiple of `η`
  let η' : D.Index → ℂ := (Complex.I / (Φ v₀ D.β.val).im : ℂ) • η
  have h_two : η' ⬝ᵥ (Y · v₀) = 2 := by
    -- `h_rank` at `Y` gives `η ⬝ᵥ (Y · v₀) = conj Φ(β) - Φ(β) = -2 * I * Im Φ(β)`
    have h_Y : Φ v₀ (star D.β.val) - Φ v₀ D.β.val = η ⬝ᵥ (Y · v₀) := by
      simpa [smul_left_inj, hGY, hρ, hY, ← sub_smul] using h_rank Y
    simp [η', ← h_Y, Complex.ext_iff, ← two_mul, field]
  have h_per : IsPeriodMap (vecMulVec (Y · v₀) η' - 1) Q :=
    isPeriodMap_vecMulVec_sub_one_of_sub_smul_eq hρ G Q hQ Y hGY hβ η h_rank
  obtain ⟨g, period, model, h_model⟩ := exists_torusModel_of_isPeriodMap e hρ u Q h_per h_smul h_ev
    h_lat
  exact ⟨g, _, abelianDim E D.Index, period, model, h_model, (Y · v₀), η', h_two, rfl⟩

end New.Variety
end
end

/-!
# Balls immerse; holomorphy, arcs and complex points of the covers

This file gives a local and global description of the covers
`New.Variety.UniversalFamily.GraphClosure`. These are reduced closures `C.scheme` of the complex
points `C.point a`. Here `a = (x, ℓ, P)` (`New.Variety.ModuliPoint`) is an adelic frame, a
reflection (1 on a line, −1 on a complement) and marked vectors.

* `New.Variety.AnalyticFamily.isHolomorphicImmersionAt_of_holomorphicAt`: let the objects `x b'`
  have models of the tori of an analytic family. Let `b` be in its domain. Suppose the uniformised
  points are holomorphic at `(b, z)` for every `z`. Then `x` is a holomorphic immersion at `b`.
* `New.Variety.ModuliPoint.exists_finite_analyticFamily_isLevelIso`: at each nonzero level, finitely
  many analytic families reach every point up to isomorphism.
* `New.Variety.UniversalFamily.isHolomorphicImmersionAt_datumPoint`,
  `New.Variety.UniversalFamily.GraphClosure.holomorphicAt_point`: the points of an analytic family
  depend holomorphically, and immersively, on the parameter.
* `New.Variety.UniversalFamily.GraphClosure.exists_arc`,
  `New.Variety.UniversalFamily.GraphClosure.exists_arc_centre_eq`: every point of `C.scheme`, and
  every complex point, is the centre of an arc of objects.
* `New.Variety.UniversalFamily.GraphClosure.point_surjective`: suppose some map `c` sends each
  `C.point a` to `U.datumPoint 1 a`. Then every complex point of `C.scheme` is some `C.point a`.

`New.HolomorphicAt φ w` says that regular functions pull back along `φ` to functions analytic at
`w`.

Notions from other files:
* `New.Variety.AnalyticFamily`: tori with a fixed frame over a domain `f.domain` in ℂⁿ⁻¹, with
  period maps `Q_b` analytic in `b`; the derivative of `Q` along `v` is ℂ-linear for the complex
  structure given by `Q_b` only if `v = 0` (`eq_zero_of_linear`).
* `New.Variety.ModuliPoint.act`: `a.act g α = (x g, ℓ, α i • P i)` for `a = (x, ℓ, P)`.
* `New.Variety.UniversalFamily.datumPoint`: for `a = (x, ℓ, P)`, a chosen complex point over `R` of
  the fibre power of the family: an object modelled on `(x, ℓ)`, with its non-zero `𝔪`-torsion
  points and the points `P`.

## Relation to the literature

Known; see `Lib.Shimura.IntegralModel.TowerExistence` and `Lib.Shimura.ThetaModuli.UniversalFamily`
for sources.
-/

@[expose] public section

open Filter in
/-- Let `g` be a function on a complex normed space whose derivative has the derivative `D₂` at
`w₀`. Suppose that, for all large `k`, the derivative of `g` at `w₀ + k⁻¹ • a` vanishes in the
direction `u + k⁻¹ • c`. Then the derivative of `g` at `w₀` sends `c` to `-D₂ a u`. -/
lemma fderiv_apply_eq_neg_of_eventually_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {g : F → ℂ} {D₂ : F →L[ℂ] F →L[ℂ] ℂ} {w₀ a u c : F}
    (hD₂ : HasFDerivAt (fderiv ℂ g) D₂ w₀)
    (h_zero : ∀ᶠ k : ℕ in atTop, fderiv ℂ g (w₀ + (k : ℂ)⁻¹ • a) (u + (k : ℂ)⁻¹ • c) = 0) :
    fderiv ℂ g w₀ c = -D₂ a u := by
  -- `δ t` is the derivative of `g` at `w₀ + t • a` in the direction `u + t • c`. It vanishes at
  -- `t = k⁻¹` for large `k`, so its derivative at `0` is zero.
  let δ (t : ℂ) : ℂ := fderiv ℂ g (w₀ + t • a) (u + t • c)
  have hδ : HasDerivAt δ (D₂ a u + fderiv ℂ g w₀ c) 0 :=
    ((hD₂.hasLineDerivAt a).clm_apply ((hasFDerivAt_id u).hasLineDerivAt c)).congr_deriv (by simp)
  -- Otherwise `δ` has no zero in a punctured neighbourhood of `0`.
  by_contra h_ne
  have h_ne_seq : ∀ᶠ k : ℕ in atTop, δ (↑k)⁻¹ ≠ 0 :=
    tendsto_natCast_atTop_cobounded
      (tendsto_inv₀_cobounded' (hδ.eventually_ne (by rwa [Ne, add_eq_zero_iff_eq_neg'])))
  exact h_zero.frequently h_ne_seq

namespace New.Variety

open CategoryTheory Over OverMorphism AlgebraicGeometry NumberField IsLocalRing ThetaObject Obj
  TorusModel Filter Cardinal IsGroupBaseChange LocallyOfFiniteType Set Submodule
  ModuliPoint

variable {E : Type} [Field E] [CMBase E] {D : PEL E}
  {R : Subalgebra (𝓞 E) E} {ν : ℕ} [NeZero ν] {U : UniversalFamily D R} {J : Type} [Finite J]
  {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}

/-- Two invertible finite adelic matrices that induce the same map on torsion classes are equal. -/
lemma eq_of_forall_torsionClass_mulVec_eq {A B : GL D.Index (𝔸f E)}
    (h_tors : ∀ w : D.Index → 𝔸f E, torsionClass (A.val.mulVec w) = torsionClass (B.val.mulVec w)) :
    A = B := by
  refine Units.ext (funext₂ fun k l ↦ sub_eq_zero.mp (eq_zero_of_forall_mul_integral fun a ↦ ?_))
  -- Compare the classes of the torsion points of `a` times the `l`-th basis vector.
  simpa [mul_comm, mul_sub] using torsionClass_eq_iff.mp (h_tors (Pi.single l a)) k

omit [NeZero ν] in
/-- Let `a`, `a'` be points and `g` an element of `GUPlus E D.Index`. Suppose `z` carries the
reflection of `a` to that of `a'` and the marked points of `a` to those of `a'`, and
`g⁻¹ = a'.frame⁻¹ * z * a.frame`. Then `z` is an isomorphism from `a.act g` to `a'` at every level
`K`: it matches reflections and marked points, and `a'.frame⁻¹ * z * (a.act g).frame ∈ K`. -/
lemma ModuliPoint.isLevelIso_act_of_inv_eq {a a' : ModuliPoint E D.Index ν} {g : GUPlus E D.Index}
    {z : GL D.Index E} (K : Subgroup (GL D.Index (𝔸f E)))
    (h_x : g.val⁻¹ = a'.frame⁻¹ * toFinGL z * a.frame)
      (h_refl : ratConj z a.reflection = a'.reflection)
    (h_P : ∀ j : Fin ν, a'.markedPoint j = realVecAction z (a.markedPoint j)) :
      (a.act g).IsLevelIso K z a' := by
  refine ⟨?_, by simpa [act] using h_refl, fun j ↦ by simp [act, h_P]⟩
  -- The level part `a'.frame⁻¹ * z * (a.frame * g)` is `g⁻¹ * g = 1`.
  change a'.frame⁻¹ * toFinGL z * (a.frame * g.val) ∈ K
  simp [← mul_assoc, ← h_x]

/-- Balls immerse. Let `f` be an analytic family of theta tori over `f.domain`, and `X` a theta
family (an abelian scheme with `𝓞 E`-action and theta coordinates) over `Z`. Let each `x b'` be a
complex point of `Z` with a model `m b'`, a uniformisation of the fibre of `X` at `x b'` by the
torus `f.torus b'`. Let `ψ (b', z)` be the image of `z` under this uniformisation, a complex point
of `X`. If `b ∈ f.domain` and `ψ` is holomorphic at every `(b, z)`, then `x` is a holomorphic
immersion at `b` as a family of complex points of `Z`: it is holomorphic there, and constant to
first order only in the direction `0`. -/
lemma AnalyticFamily.isHolomorphicImmersionAt_of_holomorphicAt {f : AnalyticFamily D} {Z : Scheme}
    {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))}
    {X : ThetaFamily D Z τ} {x : BallBase D.Index → ThetaObject X (Spec (CommRingCat.of ℂ))}
    (m : ∀ b : BallBase D.Index, (x b).TorusModel (f.torus b).toPeriodMap) {b : BallBase D.Index}
    (hb : b ∈ f.domain) :
    let ψ (q : BallBase D.Index × BallFibre E D.Index) :=
      atGeneric (m q.1).uniformisation.expMap q.2 ≫ (x q.1).toFamily.left
    (∀ z : BallFibre E D.Index, HolomorphicAt ψ (b, z)) → IsHolomorphicImmersionAt x b := by
  intro ψ h_hol
  refine ⟨?_, fun v hv ↦ ?_⟩
  · -- The point `x b'` of the base is the image of `ψ (b', 0)`.
    simpa [ψ] using ((h_hol 0).comp (g := fun b' ↦ (b', 0)) (by fun_prop)).comp_hom X.total.hom
  -- Let the base point be still in the direction `v`. Follow `y` along the family as
  -- `T y b' = Q_b' Q_b⁻¹ y`, with derivative `T' y` along `v`. By `f.eq_zero_of_linear` it is
  -- enough that `T'` commutes with `I`.
  let T (y : BallFibre E D.Index) (b' : BallBase D.Index) : BallFibre E D.Index :=
    (f.torus b').realEquiv ((f.torus b).realEquiv.symm y)
  let T' (y : BallFibre E D.Index) : BallFibre E D.Index := fderiv ℂ (T y) b v
  have h_an (w : RealVectors E D.Index) : AnalyticAt ℂ (fun b' ↦ (f.torus b').realEquiv w) b :=
    f.analyticAt b hb w
  -- The torsion sections `b' ↦ ψ (b', k⁻¹ • T l b')`, `l` in the lattice, are still: their `k`-th
  -- multiple is the zero section over the base point, and multiplication by `k` is an immersion.
  have h_torsion (l : BallFibre E D.Index) (hl : l ∈ (m b).uniformisation.lattice) (k : ℕ)
    (hk : k ≠ 0) :
      IsFirstOrderConst ψ (b, (k : ℂ)⁻¹ • T l b) (v, (k : ℂ)⁻¹ • T' l) := by
    have h_curve : HasFDerivAt (fun b' : BallBase D.Index ↦ (b', (k : ℂ)⁻¹ • T l b'))
        ((ContinuousLinearMap.id ℂ (BallBase D.Index)).prod ((k : ℂ)⁻¹ • fderiv ℂ (T l) b)) b :=
      (hasFDerivAt_id b).prodMk
        ((h_an ((f.torus b).realEquiv.symm l)).differentiableAt.hasFDerivAt.const_smul (k : ℂ)⁻¹)
    -- `T l b'` lies in the lattice of the member `b'`: the period maps carry the lattices onto
    -- each other.
    have h_lattice (b' : BallBase D.Index) : T l b' ∈ (m b').uniformisation.lattice := by
      simp_all [T, TorusModel.lattice_eq, mem_classLattice, (f.torus _).realEquiv.eq_symm_apply]
    -- So the `k`-th multiple of the section is the zero section over `x b'`.
    have h_mul_eq (b' : BallBase D.Index) :
        ψ (b', (k : ℂ)⁻¹ • T l b') ≫ (k • 𝟙 X.total).left = x b' ≫ (X.levelPoints 0).left := by
      simp_all [← (x _).isGroupBaseChange.nsmul_id_comp, ← comp_left_assoc, ← map_nsmul,
        ← Nat.cast_smul_eq_nsmul ℂ, ψ, ← (x _).isGroupBaseChange.pullSection_comp, comp_nsmul]
    have h_still :
        IsFirstOrderConst (fun b' ↦ ψ (b', (k : ℂ)⁻¹ • T l b') ≫ (k • 𝟙 X.total).left) b v := by
      simpa only [h_mul_eq, Category.assoc] using hv.comp_hom (X.levelPoints 0).left
    exact (h_hol _).isFirstOrderConst_of_nsmul X.relative_dim hk
      ((isJet_comp_iff h_curve ((h_hol _).comp_hom _)).mp h_still)
  -- On the fibre over `b`, `ψ` is a uniformisation, hence an immersion; so it is enough to test
  -- `T' (I • y) - I • T' y` on functions `r` regular near `ψ (b, 0)`.
  obtain ⟨-, h_fibre_still⟩ :=
    (m b).uniformisation.isHolomorphicImmersionAt_of_isPullback (x b).isGroupBaseChange.isPullback 0
  refine f.eq_zero_of_linear b hb v fun y ↦ sub_eq_zero.mp (h_fibre_still _ ?_)
  refine (isJet_comp_iff (hasFDerivAt_prodMk_right b 0) (h_hol 0)).mpr
    (isFirstOrderConst_iff.mpr fun U r hU ↦ ?_)
  -- `r ∘ ψ` is analytic at `(b, 0)`; `D₂` is its second derivative there.
  obtain ⟨h_near, h_analytic⟩ : (∀ᶠ w in nhds (b, 0), LandsIn (ψ w) U) ∧
      AnalyticAt ℂ (fun w ↦ PointFn.ofSection r (CommRingCat.of ℂ) (ψ w)) (b, 0) :=
    h_hol 0 (PointFn.isRegularOn_ofSection r) hU
  obtain ⟨D₂, hD₂⟩ := h_analytic.fderiv.differentiableAt
  set i : BallFibre E D.Index →L[ℂ] BallBase D.Index × BallFibre E D.Index := .inr ℂ _ _
  -- The derivative of `r ∘ ψ` along `T' y` is given by the second derivative `D₂`, linearly in `y`.
  have h_fderiv_T'_eq (y : BallFibre E D.Index) :
      fderiv ℂ (fun q ↦ PointFn.ofSection r _ (ψ q)) (b, 0) (i (T' y)) = -D₂ (i y) (v, 0) := by
    -- Both sides are real-linear in `y`, and the lattice spans.
    have h_span : y ∈ span ℝ ((m b).uniformisation.lattice : Set (BallFibre E D.Index)) := by
      simp [IsZLattice.span_top]
    induction h_span using span_induction with
    | mem l hl =>
      -- By `h_torsion`, the derivative of `r ∘ ψ` at `(b, k⁻¹ • l)` in the direction
      -- `(v, k⁻¹ • T' l)` vanishes for all large `k`.
      refine fderiv_apply_eq_neg_of_eventually_eq_zero hD₂ ?_
      have h_curve_lim : Tendsto (fun k : ℕ ↦ (b, (k : ℂ)⁻¹ • T l b)) atTop (nhds (b, 0)) :=
        tendsto_const_nhds.prodMk_nhds (tendsto_inv_atTop_nhds_zero_nat.zero_smul_const _)
      filter_upwards [eventually_ne_atTop 0, h_curve_lim.eventually h_near] with k hk h_in
      simpa [i, T] using isFirstOrderConst_iff.mp (h_torsion l hl k hk) U r h_in
    | zero => simp [T, T']
    | add y y' _ _ hy hy' =>
      -- `T'` is additive and real-linear, because the periods are.
      have h_T'_add : T' (y + y') = T' y + T' y' := by
        simp (disch := fun_prop) [T', T, fderiv_fun_add]
      simp only [h_T'_add, map_add, add_apply, neg_add, hy, hy']
    | smul a y _ hy =>
      have h_T'_smul : T' (a • y) = a • T' y := by
        simp (disch := fun_prop) [T', T, fderiv_fun_const_smul]
      simp [h_T'_smul, hy]
  -- The right side of `h_fderiv_T'_eq` is `ℂ`-linear in `y`.
  dsimp only [T, T'] at h_fderiv_T'_eq
  simp [h_fderiv_T'_eq]

/-- For `𝔪 ≠ 0` there are finitely many analytic families `f k`, `k : κ`, with this property: every
point `a : ModuliPoint E D.Index ν` is isomorphic at level `levelGU D.Index 𝔪`, by some
`z : GL D.Index E`, to a point `(f k).ballPoint 0 p` (the member of `f k` at `p.1`, with marked
points `p.2`) with `p.1` in the domain of `f k`. -/
lemma ModuliPoint.exists_finite_analyticFamily_isLevelIso (D : PEL E) (ν : ℕ) {𝔪 : 𝓞 E}
    (h𝔪 : 𝔪 ≠ 0) :
    ∃ (κ : Type) (f : κ → AnalyticFamily D),
      Finite κ ∧
      ∀ a : ModuliPoint E D.Index ν, ∃ k : κ, ∃ p ∈ (f k).domain.1 ×ˢ .univ, ∃ z : GL D.Index E,
        a.IsLevelIso (levelGU D.Index 𝔪) z ((f k).ballPoint 0 p) := by
  -- Index by the double cosets of the frames `a.frame`, and take the ball at a chosen point of
  -- each.
  let φ (a : ModuliPoint E D.Index ν) :
      DoubleCoset.Quotient
        ((toFinGL : GL D.Index E →* GL D.Index (𝔸f E)).range : Set (GL D.Index (𝔸f E)))
        (levelGU D.Index 𝔪 : Set (GL D.Index (𝔸f E))) :=
    DoubleCoset.mk toFinGL.range (levelGU D.Index 𝔪) a.frame
  -- For each coset `c`, a family through its chosen point meets every point with that frame.
  choose f hf using fun c : range φ ↦ exists_isBallFamily (rangeSplitting φ c)
  -- Signed frames meet finitely many double cosets.
  have h_finite : (range φ).Finite := by
    exact (finite_isSignedFrame_classes (isOpen_congruenceGL_span h𝔪)).subset <|
      range_subset_iff.mpr fun a ↦ ⟨a.frame, ⟨a.reflection, a.isSignedFrame⟩, rfl⟩
  refine ⟨range φ, f, h_finite, fun a ↦ ?_⟩
  -- The chosen point of the coset of `a` has the frame `toFinGL z * a.frame * k`; move `a` there.
  let c : range φ := ⟨φ a, a, rfl⟩
  obtain ⟨-, ⟨z, rfl⟩, k, hk, hz⟩ := (DoubleCoset.eq ..).mp (apply_rangeSplitting φ c).symm
  obtain ⟨hk_GU, -⟩ := Subgroup.mem_inf.mp hk
  let a' : ModuliPoint E D.Index ν :=
    { frame := toFinGL z * a.frame * k
      reflection := ratConj z a.reflection
      markedPoint := realVecAction z ∘ a.markedPoint
      isSignedFrame := a.isSignedFrame.mul z hk_GU
      isReflection := a.isReflection.conj _ }
  obtain ⟨p, hp, h_pt⟩ := (hf c).exists_ballPoint_eq a' hz.symm
  refine ⟨c, p, hp, z, ?_⟩
  -- `z` carries `a` to `a'`, with level part `k⁻¹`.
  rw [h_pt]
  simpa [a', isLevelIso_iff, mul_assoc]

/-- Let `f` be an analytic family and `P` marked vectors. The map sending a parameter `p` to the
point `U.datumPoint 𝔪 (f.ballPoint P p)` of the fibre power of the universal family `U` (the member
of `f` at `p`, with its non-zero `𝔪`-torsion points and the points `P` translated by `p.2`) is a
holomorphic immersion at every `p` whose base coordinate `p.1` lies in the domain of `f`. -/
lemma UniversalFamily.isHolomorphicImmersionAt_datumPoint {f : AnalyticFamily D}
    {P : Fin ν → RealVectors E D.Index} {𝔪 : nonZeroDivisors (𝓞 E)}
    (p : BallBase D.Index × (Fin ν → BallFibre E D.Index)) (hp : p.1 ∈ f.domain) :
    IsHolomorphicImmersionAt (fun q ↦ (U.datumPoint 𝔪 (f.ballPoint P q)).left) p := by
  obtain ⟨h_base_hol, h_base_imm⟩ : IsHolomorphicImmersionAt (fun b ↦ (U.obj (f, b)).left) p.1 :=
    f.isHolomorphicImmersionAt_of_holomorphicAt (U.model ⟨f, ·⟩) hp (U.holomorphic f _ hp)
  have h_an (w : RealVectors E D.Index) : ContDiffAt ℂ ⊤ (fun q ↦ (f.torus q.1).realEquiv w) p :=
    (f.analyticAt _ hp w).contDiffAt.fst''
  -- The uniformisation of the family at an analytic fibre coordinate `k` is holomorphic.
  have h_unif (k : BallBase D.Index × (Fin ν → BallFibre E D.Index) → BallFibre E D.Index)
      (hk : ContDiffAt ℂ ⊤ k p) :
      HolomorphicAt (fun q ↦ atGeneric (U.model (f, q.1)).uniformisation.expMap (k q) ≫
        (ThetaObject.toFamily (U.obj (f, q.1)).left).left) p :=
    (U.holomorphic f _ hp _).comp (v₀ := p) (g := fun q ↦ (q.1, k q))
      (ContDiffAt.analyticAt (by fun_prop))
  -- Describe the points by the models of the family `f`; holomorphy is tested on the projections
  -- to the factors of the fibre power.
  have h_hol : HolomorphicAt (fun q ↦ (U.datumPoint 𝔪 (f.ballPoint P q)).left) p := by
    simp_rw [← IsPointOf.eq_datumPoint (a := f.ballPoint P _) ⟨U.model (f, _), rfl⟩]
    refine HasGermAt.of_jointly_mono (fun l ↦ (Over.map U.base.hom).map (Limits.Pi.π _ l))
      (fun h_eq ↦ ext (fibrePower_ext_iff.mpr ⟨?_, fun l ↦ congrArg (·.left) (h_eq l)⟩)) ?_
      -- over the base point: `simp` leaves `Spec.map _ = ?b`, and `rfl` fixes the implicit `b`
      (by simp; rfl)
    · -- The projections separate points: there is at least one factor, and it sees the base.
      simpa using congrArg (·.left ≫ U.family.total.hom) (h_eq Classical.ofNonempty)
    · -- The torsion points and the marked points have analytic fibre coordinates.
      rintro (l | i)
      · -- `using!`: a torsion point is the exponential of its period only after unfolding.
        simpa using! h_unif
          (fun q ↦ (f.torus q.1).realEquiv (toRealVectors (ThetaTori.ratLift f.frame l.val.val)))
            (h_an _)
      · simpa [π] using h_unif (fun q ↦ q.2 i + (f.torus q.1).realEquiv (P i)) (by fun_prop)
  refine ⟨h_hol, fun (v, y) hv ↦ ?_⟩
  -- Project to the base to get `v = 0`, then to the `i`-th marked point to get `y i = 0`.
  have h_base_still : IsFirstOrderConst (fun b ↦ (U.obj (f, b)).left) p.1
      (ContinuousLinearMap.fst ℂ (BallBase D.Index) (Fin ν → BallFibre E D.Index) (v, y)) := by
    refine (isJet_comp_iff hasFDerivAt_fst h_base_hol).mp ?_
    simp_rw [← IsPointOf.eq_datumPoint (a := f.ballPoint P _) ⟨U.model (f, _), rfl⟩] at hv
    simpa using hv.comp_hom (U.family.fibrePower _).hom
  obtain rfl : v = 0 := h_base_imm v h_base_still
  suffices h_fibre_zero : ∀ i, y i = 0 by simpa [funext_iff] using h_fibre_zero
  intro i
  -- Along the fibre over `p.1`, the `i`-th marked point is still in the direction `y`.
  have h_fibre : IsFirstOrderConst
      (fun w ↦ (U.datumPoint 𝔪 (f.ballPoint P (p.1, w))).left ≫ U.family.proj (.inr i)) p.2 y := by
    simpa only [Category.assoc] using
      ((isJet_comp_iff (hasFDerivAt_prodMk_right p.1 p.2) h_hol).mpr hv).comp_hom
        (U.family.proj (.inr i))
  simp_rw [← IsPointOf.eq_datumPoint (a := f.ballPoint P _) ⟨U.model (f, _), rfl⟩] at h_fibre
  obtain ⟨h_fibre_hol, h_imm⟩ := (U.model
    (f, p.1)).uniformisation.isHolomorphicImmersionAt_of_isPullback
      (ThetaObject.isGroupBaseChange (X := U.family) _).isPullback
        (p.2 i + (f.torus p.1).realEquiv (P i))
  refine h_imm (y i) ((isJet_comp_iff
    ((hasFDerivAt_apply (𝕜 := ℂ) i p.2).add_const _) h_fibre_hol).mp ?_)
  simpa [π] using h_fibre

namespace UniversalFamily.GraphClosure

/-- Let `C` be the cover (the reduced closure of the points `C.point a`, whose component `j` is
`U.datumPoint (γ j).1 (a.act (γ j).2)`), `f` an analytic family and `P` marked vectors. The map
sending a parameter `p` to the complex point `C.point (f.ballPoint P p)` of `C` is holomorphic at
every `p` whose base coordinate `p.1` lies in the domain of `f`. -/
lemma holomorphicAt_point (C : U.GraphClosure γ ν) {f : AnalyticFamily D}
    (P : Fin ν → RealVectors E D.Index)
    (p : BallBase D.Index × (Fin ν → BallFibre E D.Index)) (hp : p.1 ∈ f.domain) :
    HolomorphicAt (fun q ↦ (C.point (f.ballPoint P q)).left) p := by
  -- Test on the components of the cover; each is given by a translated family, so
  -- `isHolomorphicImmersionAt_datumPoint` applies.
  refine .of_jointly_mono _ C.hom_ext (fun j ↦ ?_) fun q ↦ Over.w (C.point (f.ballPoint P q))
  -- The translate by `(γ j).2` of a point of `f` is the point of the translated family.
  have h_act (q : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      (f.ballPoint P q).act (γ j).2 = (f.heckeTranslate (γ j).2).ballPoint P q := by
    simp [act, AnalyticFamily.heckeTranslate, funext_iff]
  have h_component (q : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      (C.point (f.ballPoint P q)).left ≫ (ReducedClosure.proj C j).left =
        (U.datumPoint (γ j).1 ((f.heckeTranslate (γ j).2).ballPoint P q)).left := by
    rw [← comp_left, C.point_comp_proj, h_act]
  obtain ⟨h_hol, -⟩ := isHolomorphicImmersionAt_datumPoint (U := U) (𝔪 := (γ j).1)
    (f := f.heckeTranslate (γ j).2) (P := P) p hp
  simpa only [h_component] using h_hol

/-- Let `C` be the cover (the reduced closure of the points `C.point a`) and `z` a point of
`C.scheme`. There are a valuation subring `V` of `ℂ`, an arc `α : Spec V ⟶ C.scheme`, a point `b`
and a map `ρ` from the residue field of `z` to the residue field of `V` with two properties. (a) The
closed point of `α` is `z`, through `ρ`. (b) Whenever `C.point b ≫ u` is the point
`U.datumPoint 𝔪 a`, the composite of `α` and `u` is a point of the universal family for `a` at level
`𝔪`. -/
lemma exists_arc (C : U.GraphClosure γ ν) (z : C.scheme.left) :
    ∃ (V : ValuationSubring ℂ), ∃ (α : Spec (CommRingCat.of V) ⟶ C.scheme.left),
      ∃ (b : ModuliPoint E D.Index ν), ∃ (ρ : C.scheme.left.residueField z →+* ResidueField V),
      -- (a)
      specMap ρ ≫ C.scheme.left.fromSpecResidueField z = specMap (residue V) ≫ α ∧
      -- (b)
      ∀ {𝔪 : nonZeroDivisors (𝓞 E)}
        {u : C.scheme ⟶
          (Over.map U.base.hom).obj (ThetaFamily.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν))}
        {a : ModuliPoint E D.Index ν},
        C.point b ≫ u = U.datumPoint 𝔪 a → U.family.IsPointOf 𝔪 a (α ≫ u.left) := by
  have := U.isDedekindDomain
  have := isLocallyNoetherian C.scheme.hom
  -- At the level `𝔫` that determines the points `C.point a`, finitely many families `f k` meet all
  -- of them; in each, one point `C.point ((f k).ballPoint 0 (b k))` specialises to all points of
  -- the family.
  obtain ⟨𝔫, h_level⟩ := C.exists_level_point_eq
  obtain ⟨κ, f, hκ, h_meet⟩ := exists_finite_analyticFamily_isLevelIso D ν
    (nonZeroDivisors.coe_ne_zero 𝔫)
  -- In each family some member `b k` is generic: its point specialises to those of all members.
  choose b hb_mem hb using fun k ↦ exists_generic_member C.scheme.hom
    ((f k).domain.isOpen.prod isOpen_univ)
    ((f k).isConnected.prod isConnected_univ)
    fun p hp ↦ C.holomorphicAt_point 0 p (Set.mem_prod.1 hp).1
  have h_dense : IsDenseFamily fun k ↦ (C.point ((f k).ballPoint 0 (b k))).left := by
    intro w
    refine C.isSeparatingFamily.right.induction_on w isClosed_closure fun a ↦ ?_
    obtain ⟨k, q, hq, z_iso, h_rel⟩ := h_meet a
    simpa only [h_level h_rel] using
      (hb k q hq).mem_closed isClosed_closure (subset_closure (mem_range_self k))
  -- So an arc `α` starts at one of these points and has its centre at `z`.
  obtain ⟨k, V, α, h_start, rfl⟩ := New.exists_valuative_arc_of_isDenseFamily _ h_dense z
  -- The closed point of `V` is the image of the point of its residue field.
  have h_pt : (specMap (residue V.valuationSubring) ≫ α) (closedPoint _) = α (closedPoint _) :=
    congrArg α (PrimeSpectrum.comap_residue _ _)
  rw [← h_pt]
  refine ⟨_, α, (f k).ballPoint 0 (b k), _,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ _ (specMap _ ≫ α), ?_⟩
  intro 𝔪 u a h_u
  -- The generic point of `α ≫ u` is the point of `a`.
  refine .of_generic (?_ : U.family.IsPointOf 𝔪 a
    (specMap V.valuationSubring.subtype ≫ α ≫ u.left))
  rw [reassoc_of% h_start, ← comp_left, h_u]
  exact isPointOf_datumPoint

/-- Let `C` be the cover (the reduced closure of the points `C.point a`) and `t` a complex point of
`C.scheme` over `R`. There are a valuation subring `V` of `ℂ`, an arc `α : Spec V ⟶ C.scheme`, a
point `b` and a ring map `φ` from the residue field of `V` to `ℂ` with two properties. (a) The
closed point of `α`, seen through `φ`, is `t`. (b) Whenever `C.point b ≫ u` is the point
`U.datumPoint 𝔪 a`, the composite of `α` and `u` is a point of the universal family for `a` at level
`𝔪`. -/
lemma exists_arc_centre_eq (C : U.GraphClosure γ ν)
    (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))) ⟶ C.scheme) :
    ∃ (V : ValuationSubring ℂ), ∃ (α : Spec (CommRingCat.of V) ⟶ C.scheme.left),
      ∃ (b : ModuliPoint E D.Index ν), ∃ (φ : ResidueField V →+* ℂ),
      -- (a)
      specMap (φ.comp (residue V)) ≫ α = t.left ∧
      -- (b)
      ∀ {𝔪 : nonZeroDivisors (𝓞 E)} {u : C.scheme ⟶
          (Over.map U.base.hom).obj (ThetaFamily.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν))}
        {a : ModuliPoint E D.Index ν},
        C.point b ≫ u = U.datumPoint 𝔪 a → U.family.IsPointOf 𝔪 a (α ≫ u.left) := by
  -- Take an arc `α` over a valuation ring `V` centred at the image `s` of `t`. The residue field of
  -- `s` is countable, so `t` is the centre of `α` under an embedding `φ` of the residue field of
  -- `V`, whose cardinality is at most that of `ℂ`.
  obtain ⟨s, φ₀, hφ₀, h_countable⟩ := exists_countable_residue_point C.scheme.hom t.left
  obtain ⟨V, α, b, ρ, h_centre_ρ, h_arc⟩ := C.exists_arc s
  obtain ⟨φ, rfl⟩ := exists_ringHom_complex_extend ρ.injective φ₀.injective
    (mk_quotient_le.trans (mk_set_le _) : #(ResidueField V) ≤ #ℂ)
  -- Through `φ`, the closed point of `α` is that of the residue field of `s`, which is `t`.
  refine ⟨V, α, b, φ, ?_, h_arc⟩
  calc specMap (φ.comp (residue V)) ≫ α = specMap φ ≫ specMap (residue V) ≫ α := by
        simp [specMap]
    _ = specMap φ ≫ specMap ρ ≫ C.scheme.left.fromSpecResidueField s := by rw [h_centre_ρ]
    _ = t.left := by simpa [specMap] using hφ₀

/-- Let `C` be the graph closure for the pairs γ_j = (𝔪_j, g_j) and ν. Here `C.scheme` is the
reduced closure, in a product of fibre powers of the universal family `U`, of the tuples over j of
`U.datumPoint 𝔪_j (a.act g_j)`, and `C.point a` is its complex point for a point a = (x, ℓ, P) at
infinite level: an adelic matrix x, a reflection ℓ for which x is a signed frame, and marked
vectors P i in (E ⊗ ℝ)ⁿ.
Suppose a morphism `c` from `C.scheme` to the fibre power of the abelian scheme of `U` indexed by
the nonzero 1-torsion and `Fin ν` sends each `C.point a` to `U.datumPoint 1 a`, the chosen complex
point given by an object modelled on (x, ℓ) with the images of the P i. Then every complex point
over `R` of `C.scheme` is `C.point a` for some a. -/
lemma point_surjective (C : U.GraphClosure γ ν)
    {c : C.scheme ⟶
      (Over.map U.base.hom).obj (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
    (hc : ∀ a : ModuliPoint E D.Index ν, C.point a ≫ c = U.datumPoint 1 a) :
    C.point.Surjective := by
  -- Follow an arc from a point `C.point b` to `t`; at its centre the object has a model `(g, ℓ)`,
  -- and the isogenies between components identify `t` with `C.point (g, ℓ, P ∘ b.markedPoint)`.
  intro t
  obtain ⟨V, α, b, φ, h_centre, h_arc⟩ := C.exists_arc_centre_eq t
  -- Along the arc `α ≫ c` is the point of an object `y` with a model `e`.
  obtain @⟨y, V_y, h_V_y, Y_y, e, he⟩ := h_arc (hc b)
  -- Pull objects and full structures back to the centre; there `y` is modelled on some `(g, ℓ)`.
  choose x h_pb using fun y' : ThetaObject U.family (Spec (CommRingCat.of V)) ↦
    exists_isPullbackAlong (X := U.family) (specMap (φ.comp (residue V))) y'
  choose f hf using fun y' e' ↦ FullLevelStructure.exists_pullback (h_pb y') e'
  -- The structure map of `x y` on `𝓞 E` is that of `R` followed by the embedding `Φ v₀` in `ℂ`.
  have h_struct (r : 𝓞 E) : (x y).baseHom r = Φ v₀ r.val := by
    calc (x y).baseHom r = algebraMap R ℂ (algebraMap (𝓞 E) R r) := by
          have h_base : y ≫ U.base.hom = α ≫ C.scheme.hom := by simp [← c.w, reassoc_of% he]
          simp [baseHom, ← h_pb y, reassoc_of% h_centre, reassoc_of% h_base]
      -- The embedding of `R` in `ℂ` is `Φ v₀` by definition.
      _ = Φ v₀ r.val := rfl
  obtain ⟨g, ℓ, d, Y, m, hm, h_refl⟩ := exists_torusModel (f y e.fullStructure) h_struct
  have h_onto : m.π.Surjective := m.uniformisation.surjective.comp Y.realEquiv.surjective
  choose P hP using fun w : RealVectors E D.Index ↦
    h_onto ((h_pb y).isGroupBaseChange.pullSection (e.π w))
  -- The candidate is `(g, ℓ, P ∘ b.markedPoint)`; compare it with `t` on each component `i`.
  refine ⟨{ frame := g, reflection := ℓ, markedPoint := P ∘ b.markedPoint,
            isSignedFrame := ⟨_, Y.isSignedFrameFor⟩, isReflection := h_refl },
    C.hom_ext fun i ↦ ?_⟩
  -- `(γ i).2` is a frame for a positive scalar `μ`, an integer since `(γ i).2⁻¹` is integral.
  obtain ⟨⟨c₀, h_pos, h_frame⟩, h_inv_int⟩ :
      (γ i).2.val ∈ GU E D.Index ∧ ∀ k l : D.Index, (γ i).2.val⁻¹ k l ∈ Ô E :=
    (γ i).2.prop
  obtain ⟨μ, rfl⟩ := h_frame.exists_intCast_eq (γ i).2.prop
  lift μ to ℕ using mod_cast h_pos.le
  -- Along the arc an isogeny `χ` inducing `(γ i).2⁻¹` on torsion maps `y` to the component `y'`.
  -- Its pull-back `ψ` comes from a rational matrix `z` between the models.
  obtain @⟨y', V_y', h_V_y', Y_y', e', he'⟩ := h_arc (C.point_comp_proj b i)
  have h_refl_b : ratConj (1 : GL D.Index E) b.reflection = (b.act (γ i).2).reflection := by
    simp [ratConj, act]
  have h_level : (b.act (γ i).2).frame⁻¹ * toFinGL 1 * b.frame = (γ i).2.val⁻¹ := by simp [act]
  have h_scalar : IsScalarFrame (γ i).2.val⁻¹⁻¹ μ := by simpa using And.intro h_pos h_frame
  obtain ⟨hρ, χ, hχ_isog, hχ_lin, h_cls, h_tor, hχ⟩ :=
    exists_isogeny (μ := μ) 1 h_refl_b e e' h_level h_inv_int h_scalar
  obtain ⟨ψ, hψ_pt, hψ_lin, hψ_sec⟩ :=
    (h_pb y).isGroupBaseChange.exists_hom_baseChange (h_pb y').isGroupBaseChange (𝟙 _) χ
  have h_struct' (r : 𝓞 E) : (x y').baseHom r = Φ v₀ r.val := by
    simp [(h_pb _).baseHom_eq_comp, hρ, ← m.baseHom_eq]
  obtain ⟨g', ℓ', d', Y', m', hm', h_refl'⟩ := exists_torusModel (f y' e'.fullStructure) h_struct'
  have hψ_cls : (x y').lineBundle.picClass.pull ψ.left = μ • (x y).lineBundle.picClass := by
    -- Over the centre, `ψ` followed by the pull-back map of `y'` is the pull-back map of `y`
    -- followed by `χ`.
    have h_left : ψ.left ≫ (h_pb y').schemeMap.left = (h_pb y).schemeMap.left ≫ χ.left := by
      simpa [pointEquiv_apply] using congrArg Hom.left (hψ_pt (𝟙 _))
    rw [(h_pb _).lineBundle_eq_pull, (h_pb _).lineBundle_eq_pull, ← Pic.pull_picClass,
      ← Pic.pull_picClass, ← Pic.pull_comp, h_left, Pic.pull_comp, h_cls, map_nsmul]
  obtain ⟨z, hz_π, -, hz_ℓ⟩ := exists_matrix_of_hom m m' ψ (mod_cast h_pos.ne') hψ_cls
  -- Both descriptions of `ψ` on torsion agree, and torsion determines an adelic matrix.
  have h_matrix : (γ i).2.val⁻¹ = g'⁻¹ * toFinGL z * g := by
    refine eq_of_forall_torsionClass_mulVec_eq fun w ↦ m'.fullStructure.injective ?_
    refine .trans ?_ (torsionPoint_comp _ _ hz_π w)
    simp [hm, hm', hf, h_tor, hψ_sec]
  -- The component `i` of `t` is the point with frame `g'`, reflection `ℓ'` and the images under `z`
  -- of the marked vectors `P ∘ b.markedPoint`. By `z` it is isomorphic to the translate of our
  -- candidate by `(γ i).2`.
  have h_pt :
      U.family.IsPointOf (γ i).1
        ⟨g', ℓ', fun j ↦ realVecAction z (P (b.markedPoint j)), ⟨_, Y'.isSignedFrameFor⟩, h_refl'⟩
        (t ≫ ReducedClosure.proj C i).left := by
    refine ⟨m', ?_⟩
    rw [comp_left, ← reassoc_of% h_centre, he']
    -- `↓`: `hz_π` must rewrite before the other lemmas
    simp [fibrePower_ext_iff, ← (h_pb _).comp_toFamily, ↓← hz_π, pullSection_comp_assoc, act,
      hm', hf, hP, hψ_sec, hχ, h_pb]
  refine (C.point_comp_proj _ i).trans (ext ((isPointOf_datumPoint.eq_iff h_pt).mpr ⟨z, ?_⟩))
  exact isLevelIso_act_of_inv_eq _ h_matrix hz_ℓ fun j ↦ rfl

end UniversalFamily.GraphClosure

end New.Variety
