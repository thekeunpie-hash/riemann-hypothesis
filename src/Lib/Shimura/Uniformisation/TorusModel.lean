module

import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
public import Lib.Shimura.ThetaGroup
public import Lib.Shimura.Uniformisation.HolomorphicFamilies
import Lib.General.Analysis.HolomorphicIntegrals
public import Lib.General.Geometry.GeometricPoints
import Lib.PadicComparison.Descent.TestCategory
import Lib.Shimura.AbelianScheme.Pairings
import Lib.Shimura.ThetaNormality.NormalGeneration
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Valuation.Integral
public import Lib.Shimura.ThetaModuli.ThetaFamilyRigidity
import Lib.Adelic.Adeles.StrongApproximation
import Lib.Shimura.AbelianScheme.IsogenyFlatness
import Lib.Shimura.Uniformisation.BallModel
import Lib.Shimura.Uniformisation.LieExponential

section
/-!
# Uniformisations over an arc: theta coordinates, Weil pairing and extension of maps

Let `A` be an abelian scheme over an arc `O` (`New.ValuativeArc`, a valuation ring with fraction
field `ℂ`). Let `u : V / Λ ≅ A(O)` be a uniformisation (`New.Uniformisation`) with `Λ = u.lattice`,
and let `L` be a linear system whose coordinates are theta functions (`New.HasThetaCoords`).
Sections of `L` are read as functions on `V`. Lifts of translations then act by twisted
translations, and their commutators are given by the Weil pairing. With these tools, an additive map
`s' : V → A'(O)` that kills `Λ` and has theta coordinates is shown to come from a morphism `A ⟶ A'`
over `O`, not only over `ℂ`.

## Main definitions and results

* `New.Variety.isSeparatingFamily_atGeneric_of_surjective`: the complex points `New.atGeneric` of
  the sections are dense in `A`.
* `New.Variety.thetaEval`, `New.Variety.exists_theta_evaluation`: `H⁰(L)` embeds in the
  functions on `V`, and lifts of translations (`New.Variety.IsTranslationLift`) act by multiples
  of the twisted translations `New.RealComplexForm.thetaShift`.
* `New.Variety.lift_commutator_iff_weil_pairing`: the commutator of two lifts is given by the
  Riemann phase `New.RealComplexForm.riemannPhase`.
* `New.Variety.exists_sections_of_translation_stable`: one scalar puts a finite family of theta
  functions in a stable `O`-module. No orbit of the dual lattice consists only of common zeros.
* `New.Variety.exists_section_of_hasThetaCoords`: a section of `π : A' ⟶ A` through the points
  `s' z`.
* `New.Variety.exists_hom_of_hasThetaCoords`: a homomorphism `A ⟶ A'`, obtained from its graph in
  `A × A'`.

Notions from other files:
* `New.IsAbelianScheme`: a commutative group scheme A over S is abelian if it is smooth and proper
  over S and multiplication by every m ≠ 0 is surjective.
* `New.LineBundle.H0`: The R-module of global sections of L, for a scheme X over R; a section `r`
  has a component `r.val i` (a `New.PointFn`) in each chart `i`.
* `New.IsPosRiemann`: The Riemann form E of B is positive: E(u, iu) > 0 for every u ≠ 0.
* `New.Variety.IsTranslationLift`: The R-linear endomorphism Φ of H⁰(L) is pull-back along the
  translation t_z by the section z followed by some isomorphism t_z^*L ≅ L.

## Relation to the literature

Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre. Here
only maps of complex tori that multiply a theta polarisation by an integer are treated, where the
kernel of the polarisation is killed by a unit of the ring, over any valuation ring of the complex
numbers (not noetherian, any rank). The map and the identity of line bundle classes extend together,
and points extend by properness. Source: S. Bosch, W. Lütkebohmert, M. Raynaud, Néron Models (1990),
1.2/8 and 4.4/1; G. Faltings, C.-L. Chai, Degeneration of Abelian Varieties (1990), I.2.7; L.
Moret-Bailly, Pinceaux de variétés abéliennes, Astérisque 129 (1985), II.3.5.

See also `Lib.Shimura.IntegralModel.UniversalFamily` and `Lib.Shimura.Uniformisation.AppellHumbert`.
-/

@[expose] public section

namespace New.Variety

section SectionComponents

open CategoryTheory AlgebraicGeometry

variable {X : Scheme.{0}} {ι : Type} {L : LineBundle X ι} {R : Type} [CommRing R]
  [X.Over (Spec ⟨R⟩)]

private lemma _root_.New.LineBundle.H0.isSection_val (r : L.H0 R) : L.IsSection r.val :=
  r.prop.left

/-- A component `r.val i` of a global section vanishes at the points outside the chart `i`. -/
private lemma _root_.New.LineBundle.H0.val_eq_zero_of_not_landsIn (r : L.H0 R) (i : ι)
    (A : CommRingCat) (t : Spec A ⟶ X) (h_out : ¬LandsIn t (L.opens i)) : r.val i A t = 0 :=
  r.prop.right i A t h_out

/-- A frame of `L` is a unit at every point that lands in the chart `i`. -/
private lemma _root_.New.LineBundle.IsFrame.isUnit_apply {s : ι → PointFn X} (hs : L.IsFrame s)
    (i : ι) (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t (L.opens i)) : IsUnit (s i A t) :=
  hs.right i A t ht

end SectionComponents

/-! ## Sections along a uniformisation as theta functions -/

section ComplexComparison

open CategoryTheory AlgebraicGeometry Over ValuativeArc Function IsSchemeTheoreticallyDominant

variable {V ι κ : Type} [FinComplexSpace V]
  {O : Type} [CommRing O] [ValuativeArc O] {A : Over (Spec ⟨O⟩)}

/-- Let A be a smooth proper scheme over a valuation ring O with fraction field ℂ, and let
s : Z → (sections of A over O) be surjective. Then A is reduced and the complex points
`atGeneric s z` (the sections restricted to the generic point `Spec ℂ` of `Spec O`) are dense in
A. -/
lemma isSeparatingFamily_atGeneric_of_surjective [Smooth A.hom] [IsProper A.hom] {Z : Type}
    {s : Z → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
    (hs_surj : Function.Surjective s) :
    IsSeparatingFamily (atGeneric s) := by
  -- `A` is reduced because its generic fibre is reduced and scheme-theoretically dominant
  refine ⟨isReduced (Limits.pullback.fst A.hom genericPt), ?_⟩
  -- the generic point is dense in `Spec O`; `Spec ℂ` has a single point
  have h_dense :
      IsDenseFamily fun _ : Spec (.of ℂ) ↦ (genericPt : Spec (.of ℂ) ⟶ Spec (.of O)) := by
    -- `convert`: the two sides differ only in the point of the one-point space `Spec ℂ`
    convert (ValuativeArc.genericPt (O := O)).denseRange
    exact congrArg _ (by subsingleton)
  refine h_dense.of_fibres A.hom fun _ y hy ↦ ?_
  -- by the valuative criterion every complex point over `genericPt` comes from a section
  obtain ⟨z, hz⟩ := bijective_restrict_genericPt.surjective.comp hs_surj (homMk y hy)
  exact ⟨z, congrArg (fun g ↦ g.left) hz⟩

/-- If the linear system `L` is an embedding and has theta functions as coordinates along `s`, the
family of complex points of `s` is holomorphic. -/
lemma _root_.New.HasThetaCoords.holomorphicAt [Finite κ] {Λ : Submodule ℤ V}
    {s : V → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
    {L : LineBundle A.left κ} {B : ThetaTori.LatticeForm Λ} {χ : V → ℂ} {θ : V → κ → ℂ}
    (h : HasThetaCoords (ι := κ) (P := V) Λ (atGeneric s) L B χ θ) (hL : L.IsProjEmbedding A.hom)
    (z : V) :
    HolomorphicAt (atGeneric s) z := by
  -- the homogeneous coordinates `θ` of the points are entire functions
  refine .of_isHomogeneousCoords hL (fun i ↦ ?_) (.of_forall h.hasFieldCoords) fun _ ↦ Over.w _
  exact analyticAt_of_eventually_differentiableAt (.of_forall (h.mem_thetaSpace i).1)

section ThetaEval

variable {L : LineBundle A.left κ} {χ : V → ℂ} {θ : V → κ → ℂ} {Λ : Submodule ℤ V}
  {s : V → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
  {B : ThetaTori.LatticeForm Λ}

/-- For theta coordinates `θ` of `L` along `s`, a chart in which `θ z` does not vanish. -/
private noncomputable def thetaChart (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (z : V) : κ :=
  (h.hasFieldCoords z).exists_ne_zero.choose

/-- The theta function `θ z` does not vanish in the chart `thetaChart h z`. -/
private lemma apply_thetaChart_ne_zero (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (z : V) :
    θ z (thetaChart h z) ≠ 0 :=
  (h.hasFieldCoords z).exists_ne_zero.choose_spec

/-- Sections of `L` read as functions on `V`, for theta coordinates `θ` of `L` along `s`: a
section `r` goes to `z ↦ θ z i * r_i (s z)` for a chart `i` with `θ z i ≠ 0`. The value does not
depend on the chart (`New.Variety.thetaEval_eq_iff`). -/
@[no_expose]
noncomputable def thetaEval (h : HasThetaCoords Λ (atGeneric s) L B χ θ) : L.H0 O →ₗ[O] V → ℂ :=
  .pi fun z ↦ θ z (thetaChart h z) •
    { toFun r := r.val (thetaChart h z) (CommRingCat.of ℂ) (atGeneric s z)
      map_add' := by simp
      map_smul' := by simp [H0_smul, atGeneric, ValuativeArc.genericPt_eq, Algebra.smul_def] }

/-- `thetaEval h r` is the function `g` exactly when `r_i = g / θ_i` at each point `s z`, in each
chart `i` with `θ z i ≠ 0`. -/
lemma thetaEval_eq_iff (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (r : L.H0 O) (g : V → ℂ) :
    thetaEval h r = g ↔ ∀ (i : κ) (z : V),
      θ z i ≠ 0 → r.val i (CommRingCat.of ℂ) (atGeneric s z) = g z / θ z i := by
  -- the chart does not matter: `θ z i * r i = θ z j * r j` if `θ z i` and `θ z j` are not zero
  constructor
  · rintro rfl i z hi
    simp [thetaEval, (LineBundle.H0.isSection_val r).right i (thetaChart h z),
      h.hasFieldCoords .., field, apply_thetaChart_ne_zero h, hi]
  · -- at each `z` the value of `thetaEval h r` is read in the chart `thetaChart h z`
    intro h_val
    funext z
    simp [thetaEval, h_val _ z (apply_thetaChart_ne_zero h z), mul_div_cancel₀,
      apply_thetaChart_ne_zero h]

/-- `thetaEval h` sends the coordinate sections to the theta functions. -/
lemma thetaEval_coordSection (h : HasThetaCoords Λ (atGeneric s) L B χ θ) (i : κ) :
    thetaEval h (coordSection h.isLinearSystem i) = fun z : V ↦ θ z i := by
  simp +contextual [thetaEval_eq_iff, coordSection, h.hasFieldCoords .., field]

end ThetaEval

variable [IsAbelianScheme A]
  {L : LineBundle A.left κ} (u : Uniformisation A V) {B : ThetaTori.LatticeForm u.lattice}
  {χ : V → ℂ} {θ : V → κ → ℂ} (h : HasThetaCoords u.lattice (atGeneric u.expMap) L B χ θ)

/-- Along a uniformisation, `thetaEval h` is injective: the points `atGeneric u.expMap z` are
dense, so sections that agree there are equal. -/
lemma thetaEval_injective (h : HasThetaCoords u.lattice (atGeneric u.expMap) L B χ θ) :
    Function.Injective (thetaEval h) := by
  intro r r' hr
  -- in each chart `i` with `θ z i ≠ 0`, a section `s` has the value `thetaEval h s z / θ z i`
  have h_val (s : L.H0 O) : ∀ (i : κ) (z : V), θ z i ≠ 0 →
      s.val i (CommRingCat.of ℂ) (atGeneric u.expMap z) = thetaEval h s z / θ z i :=
    (thetaEval_eq_iff h s (thetaEval h s)).mp rfl
  refine H0_ext fun hi hi' ↦ (isSeparatingFamily_atGeneric_of_surjective u.surjective).pointFn_ext
    hi hi' ?_
  simp +contextual [h.hasFieldCoords .., h_val, hr]

/-- Along a uniformisation, a lift `Φ` of the translation by `u.expMap a` acts through
`thetaEval h` as a multiple of the shift `B.thetaShift a`. -/
lemma exists_thetaEval_eq_smul_thetaShift
    (h : HasThetaCoords u.lattice (atGeneric u.expMap) L B χ θ)
    (a : V) (Φ : Module.End O ↥(L.H0 O)) (hΦ : IsTranslationLift L (u.expMap a) Φ) :
    ∃ c : ℂ, ∀ r : ↥(L.H0 O), thetaEval h (Φ r) = c • B.thetaShift a (thetaEval h r) := by
  -- the frame `w` compares the coordinates `θ` of `L` with the shifted ones of its translate:
  -- by `riemannForm_eq_of_isFrame` it is a constant `c` times their quotient and an exponential
  -- factor, the one in `thetaShift`
  obtain ⟨w, hw, h_pull⟩ := hΦ
  obtain ⟨-, -, c, hc⟩ := h.riemannForm_eq_of_isFrame (h.pull_translate (u.atGeneric_add a)) hw
    u.holomorphicAt u.atGeneric_add_of_mem
  refine ⟨c, fun r ↦ (thetaEval_eq_iff h _ _).mpr fun i z hi ↦ ?_⟩
  simp [h_pull _ _ (thetaChart h (z + a)), hc, apply_thetaChart_ne_zero h, hi, ← u.atGeneric_add,
    thetaShift_apply, h.hasFieldCoords .., thetaEval, field]

/-- Let L have theta coordinates θ_i along s for a lattice Λ. Then r ↦ θ_i·r_i
(`New.Variety.thetaEval`) is an O-linear map from H⁰(L) to functions on V that sends the
coordinates to the θ_i. If Λ and s are the lattice and exponential map of a uniformisation, this
map is injective and sends lifts of translations to scalar multiples of
`New.RealComplexForm.thetaShift`. -/
lemma exists_theta_evaluation {Λ : Submodule ℤ V}
    {s : V → (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A)}
    {B : ThetaTori.LatticeForm Λ} (h : HasThetaCoords Λ (atGeneric s) L B χ θ) :
    ∃ T : L.H0 O →ₗ[O] V → ℂ,
      -- (a) `T r` is the function `g` with `r i = g / θ i` along the family
      (∀ (r : L.H0 O) (g : V → ℂ),
        T r = g ↔
          ∀ (i : κ) (z : V), θ z i ≠ 0 → r.val i (CommRingCat.of ℂ) (atGeneric s z) = g z / θ z i) ∧
      -- (b) the coordinates go to the theta functions
      (∀ i : κ, T (coordSection h.isLinearSystem i) = fun z : V ↦ θ z i) ∧
      -- (c) along a uniformisation `T` is injective and turns lifts of translations into multiples
      -- of shifts
      ∀ u : Uniformisation A V, Λ = u.lattice → s = u.expMap →
        Function.Injective T ∧
        ∀ (a : V) (Φ : Module.End O ↥(L.H0 O)),
          IsTranslationLift L (s a) Φ →
          ∃ c : ℂ, ∀ r : ↥(L.H0 O), T (Φ r) = c • B.thetaShift a (T r) := by
  refine ⟨thetaEval h, thetaEval_eq_iff h, thetaEval_coordSection h, ?_⟩
  rintro u rfl rfl
  exact ⟨thetaEval_injective u h, exists_thetaEval_eq_smul_thetaShift u h⟩

include h

/-- Weil pairing: let L have theta coordinates for B, and let Φ, Ψ lift to L^m the translations
by the images of a, b. Then ΦΨ = c·ΨΦ on all coordinates if and only if
c = exp(2πi m E(a,b)), E the Riemann form of B. -/
lemma lift_commutator_iff_weil_pairing {m : ℕ} {a b : V} {c : O}
    {Φ Ψ : Module.End O ↥((L.pow m).H0 O)}
    (hΦ : IsTranslationLift (L.pow m) (u.expMap a) Φ)
    (hΨ : IsTranslationLift (L.pow m) (u.expMap b) Ψ) :
    (∀ (l : (L.pow m).IsLinearSystem) (i : Fin m → κ),
        Φ (Ψ (coordSection l i)) = c • Ψ (Φ (coordSection l i))) ↔
      algebraMap O ℂ c = (m • B).riemannPhase a b := by
  -- Under the embedding `T` of sections into functions, `Φ` and `Ψ` act as multiples of the shifts
  -- by `a` and `b`, which commute up to the factor given by the Riemann form.
  let T : (L.pow m).H0 O →ₗ[O] V → ℂ := thetaEval (h.pow m)
  have hT_inj : Function.Injective T := thetaEval_injective u (h.pow m)
  obtain ⟨α, hα⟩ : ∃ α : ℂ, ∀ s : (L.pow m).H0 O, T (Φ s) = α • (m • B).thetaShift a (T s) :=
    exists_thetaEval_eq_smul_thetaShift u (h.pow m) a Φ hΦ
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, ∀ s : (L.pow m).H0 O, T (Ψ s) = β • (m • B).thetaShift b (T s) :=
    exists_thetaEval_eq_smul_thetaShift u (h.pow m) b Ψ hΨ
  have h_comm_T (s : (L.pow m).H0 O) : T (Φ (Ψ s)) = (m • B).riemannPhase a b • T (Ψ (Φ s)) := by
    simp [T, hα, hβ, (h.pow m).isAppellHumbert.thetaShift_comm a, funext_iff, field]
  constructor
  · intro h_comm
    -- compare the two factors on a coordinate `i` whose theta function does not vanish at `0`
    obtain ⟨i, hi⟩ := ((h.pow m).hasFieldCoords 0).exists_ne_zero
    set x : (L.pow m).H0 O := coordSection (h.pow m).isLinearSystem i
    have hx : T x ≠ 0 := (thetaEval_coordSection (h.pow m) i).trans_ne (ne_iff.mpr ⟨0, hi⟩)
    have h_ne : T (Ψ (Φ x)) ≠ 0 := by
      simpa [map_eq_zero_iff, hT_inj, hΨ.injective, hΦ.injective] using ne_zero_of_map hx
    have h_eq : algebraMap O ℂ c • T (Ψ (Φ x)) = T (Φ (Ψ x)) := by simp [x, h_comm]
    exact smul_left_injective ℂ h_ne (h_eq.trans (h_comm_T _))
  · -- if `c` is the Riemann phase, both sides agree after the injective `T`
    intro hc
    simp [← hT_inj.eq_iff, h_comm_T, ← hc]

/-- Let `L` have theta coordinates `θ` of type `(B, χ)` along `u`, `B` be positive, `n` a unit of
`O`, and `N` an `O`-module of sections of `L` containing the coordinate sections. Suppose that each
`a` in the dual lattice `B.dualLattice` has `n • a ∈ u.lattice` (`h_torsion`), and that the
translation by `a` has a lift that preserves `N` (`h_lift`). For finitely many theta functions `f_j`
(elements of `B.thetaSpace χ`, the space that also holds each coordinate `θ_k`) of type `(B, χ)`
with `f_i ≠ 0` there are `γ ≠ 0` and sections `r_j ∈ N` such that: (a) the `k`-th component of `r_j`
at the point `u.expMap z` is `γ f_j(z)/θ_k(z)` whenever `θ_k(z) ≠ 0`; (b) for every field-valued
point `t`, some component of some `r_j` is nonzero at some translate of `t` by `B.dualLattice`. -/
lemma exists_sections_of_translation_stable [Finite κ] [IsPosRiemann B] {n : ℕ}
    (hn : IsUnit (n : O)) {N : Submodule O (L.H0 O)}
    (h_torsion : ∀ a ∈ B.dualLattice, n • a ∈ u.lattice)
    (h_lift : ∀ a ∈ B.dualLattice,
      ∃ Φ : Module.End O ↥(L.H0 O), IsTranslationLift L (u.expMap a) Φ ∧ N ≤ N.comap Φ)
    (hN : ∀ k : κ, coordSection h.isLinearSystem k ∈ N) {f : ι → V → ℂ} [Finite ι]
    (hf : ∀ j : ι, f j ∈ B.thetaSpace χ) (i : ι) (hf_ne : f i ≠ 0) :
    ∃ γ ≠ (0 : CommRingCat.of ℂ), ∃ r : ι → N,
      -- (a)
      (∀ (j : ι) (k : κ) (z : V), θ z k ≠ 0 →
        (r j : L.H0 O).val k (CommRingCat.of ℂ) (atGeneric u.expMap z) = γ * f j z / θ z k) ∧
      -- (b)
      ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ A.left),
        ∃ a ∈ B.dualLattice, ∃ (j : ι) (k : κ),
          (r j : L.H0 O).val k ⟨K⟩ (t ≫ (translation (u.expMap a)).left) ≠ 0 := by
  -- Read sections as theta functions through `T`. By
  -- `IsAppellHumbert.exists_proportional_orbit_lattice` there is `γ` such that a module of sections
  -- stable under the lifts `Φ a` holds the coordinates iff it holds all `γ • f j`.
  -- Apply this to `N`, and to the sections that vanish on an orbit.
  let T : L.H0 O →ₗ[O] V → ℂ := thetaEval h
  have hT_iff (r : L.H0 O) (g : V → ℂ) : T r = g ↔ ∀ (k : κ) (z : V), θ z k ≠ 0 →
      r.val k (CommRingCat.of ℂ) (atGeneric u.expMap z) = g z / θ z k := thetaEval_eq_iff h r g
  have hT_coord (k : κ) : T (coordSection h.isLinearSystem k) = fun z : V ↦ θ z k :=
    thetaEval_coordSection h k
  have hT_inj : Function.Injective T := thetaEval_injective u h
  choose! Φ hΦ hΦN using h_lift
  -- each lift `Φ a` acts through `T` as a multiple `c a` of the shift
  have h_shift (a : V) (ha : a ∈ B.dualLattice) :
      ∃ c : ℂ, ∀ r : L.H0 O, T (Φ a r) = c • B.thetaShift a (T r) :=
    exists_thetaEval_eq_smul_thetaShift u h a (Φ a) (hΦ a ha)
  choose! c hc using h_shift
  -- A chart `p` that contains the section `u.expMap 0`.
  obtain ⟨p, hp_in⟩ := L.exists_landsIn (u.expMap 0).left
  have hθ : θ 0 p ≠ 0 := ((h.hasFieldCoords ..).1.1 (hp_in.comp _)).ne_zero
  have hc_unit (a : V) (ha : a ∈ B.dualLattice) : ∃ d : Oˣ, algebraMap O ℂ d = c a * c (-a) := by
    -- `Φ a * Φ (-a)` lifts the identity, so it multiplies by a frame `w`, whose value at the
    -- section `u.expMap 0` is a unit of `O`.
    obtain ⟨w, hw, h_mul⟩ := (hΦ a ha).mul (hΦ _ (neg_mem ha))
    refine ⟨(hw.isUnit_apply (p, p) _ (u.expMap 0).left (by simpa using hp_in)).unit, ?_⟩
    -- evaluate `Φ a (Φ (-a) x)`, for the coordinate `x` of the chart `p`, by `h_mul` and by `hc`
    let x : L.H0 O := coordSection h.isLinearSystem p
    have h_read : (Φ a (Φ (-a) x)).val p (CommRingCat.of ℂ) (atGeneric u.expMap 0) =
        T (Φ a (Φ (-a) x)) 0 / θ 0 p := (hT_iff _ _).mp rfl p 0 hθ
    have h_in : LandsIn (atGeneric u.expMap 0) (L.opens p) := hp_in.comp _
    have h_frame := h_mul x p p (CommRingCat.of ℂ) (atGeneric u.expMap 0) h_in
      (by simpa [← map_add] using h_in)
    -- `↓` (use before the subterms are simplified): without it the goal does not close
    simpa [x, ↓hT_coord, ↓hc, *, h.isAppellHumbert.thetaShift_thetaShift, coordSection, field,
      hw.1.1 _ _, L.transition_self, hp_in.comp, ValuativeArc.genericPt_eq, atGeneric,
      -map_zero] using h_frame.symm.trans h_read
  have h_coord_theta (k : κ) : (fun z : V ↦ θ z k) ∈ B.thetaSpace χ := h.mem_thetaSpace k
  have hp_ne : (⟨_, h_coord_theta p⟩ : B.thetaSpace χ) ≠ 0 := fun h0 ↦
    hθ (congrFun (congrArg Subtype.val h0) 0)
  obtain ⟨γ, hγ, h_scale⟩ := h.isAppellHumbert.exists_proportional_orbit_lattice
    (fun j ↦ ⟨f j, hf j⟩) (fun k ↦ ⟨_, h_coord_theta k⟩) i p c hn h_torsion (by simpa) hp_ne hc_unit
  have h_iff (M : Submodule O (L.H0 O)) (hM : ∀ a ∈ B.dualLattice, ∀ r ∈ M, Φ a r ∈ M) :
      (∀ k : κ, coordSection h.isLinearSystem k ∈ M) ↔
        ∀ j : ι, ∃ r ∈ M, ∀ (i : κ) (z : V), θ z i ≠ 0 →
          r.val i (CommRingCat.of ℂ) (atGeneric u.expMap z) = γ * f j z / θ z i := by
    have h_stable (a : V) (ha : a ∈ B.dualLattice) :
        ∀ x ∈ M.map T, c a • B.thetaShift a x ∈ M.map T :=
      fun _ ⟨r, hr, hx⟩ ↦ ⟨_, hM a ha r hr, by rw [hc a ha, hx]⟩
    simpa [← hT_coord, hT_inj.eq_iff, hT_iff, -Subtype.exists] using h_scale _ h_stable
  choose r hrN hr using (h_iff N hΦN).mp hN
  refine ⟨γ, hγ, fun j ↦ ⟨r j, hrN j⟩, hr, fun K _ t ↦ ?_⟩
  by_contra! h_zero
  -- `Z`, the sections that vanish on the orbit of `t`, is stable under the `Φ a`.
  let Z : Submodule O (L.H0 O) :=
    { carrier := {s | ∀ a ∈ B.dualLattice, ∀ i : κ,
        s.val i (CommRingCat.of K) (t ≫ (translation (u.expMap a)).left) = 0}
      add_mem' := by simp +contextual
      zero_mem' := by simp
      smul_mem' := by simp +contextual [H0_smul] }
  have hZ (b : V) (hb : b ∈ B.dualLattice) (s : L.H0 O) (hs : s ∈ Z) : Φ b s ∈ Z := by
    intro a ha i
    by_cases h_in : LandsIn (t ≫ (translation (u.expMap a)).left) (L.opens i)
    · obtain ⟨w, -, h_mul⟩ := hΦ b hb
      rw [h_mul s i _ _ _ h_in (L.exists_landsIn _).choose_spec]
      refine mul_eq_zero_of_right _ ?_
      simpa [← comp_left, add_assoc, comp_add] using hs (a + b) (add_mem ha hb) _
    · exact LineBundle.H0.val_eq_zero_of_not_landsIn (Φ b s) i _ _ h_in
  -- If `Z` held all `r j`, it would hold the coordinates; but they do not all vanish at `t`.
  obtain ⟨k, hk⟩ := L.exists_landsIn t
  have h_coord : coordSection h.isLinearSystem k ∈ Z :=
    (h_iff Z hZ).mpr (fun j ↦ ⟨r j, fun a ha ↦ h_zero a ha j, hr j⟩) k
  simpa [coordSection, L.transition_self, hk] using h_coord 0 (by simp) k

end ComplexComparison

/-!
## Extension of linear maps to sections and homomorphisms over an arc

`New.HasThetaCoords` says that the coordinates of a linear system at the complex points
`New.atGeneric` are theta functions of type `(B, χ)`. Standing hypotheses: `N` has such coordinates
along `u.expMap`, and the Riemann form of `B` is positive (an instance `IsPosRiemann B`). Further,
`n` is a unit of `O`, and every `a` in the dual lattice of `B` has `n • a ∈ u.lattice`, and the
translation by `u.expMap a` lifts to `N`. Also `s'` kills `u.lattice`, `A'` is proper over `O`, and
`M` is a projective embedding of `A'`.
-/

section ArcExtension

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Over Category LineBundle PointFn

variable {V ι κ O : Type} [FinComplexSpace V] [CommRing O] [ValuativeArc O]
  {A A' : Over (Spec ⟨O⟩)} [AddObj A']
  {s' : V →+ (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ A')} [Finite κ]
  [IsAbelianScheme A] [Finite ι]
  (u : Uniformisation A V) {N : LineBundle A.left ι} {B : ThetaTori.LatticeForm u.lattice}
  {χ : V → ℂ} {θ : V → ι → ℂ}
  (h : HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ) [IsPosRiemann B]
  (hs' : ∀ l ∈ u.lattice, s' l = 0) {n : ℕ} (hn : IsUnit (n : O))
  (h_tors_lift : ∀ a ∈ B.dualLattice,
    n • a ∈ u.lattice ∧ ∃ Φ : Module.End O ↥(N.H0 O), IsTranslationLift N (u.expMap a) Φ)
  [IsProper A'.hom] {M : LineBundle A'.left κ} (hM : M.IsProjEmbedding A'.hom)

include h hs' hn h_tors_lift hM

omit h hs' hn hM [IsPosRiemann B] [Finite ι] in
/-- The lift of a translation by a point of the dual lattice preserves the module of all
sections. -/
private lemma exists_isTranslationLift_top_of_dualLattice :
    ∀ a ∈ B.dualLattice, ∃ Φ : Module.End O ↥(N.H0 O),
      IsTranslationLift N (u.expMap a) Φ ∧
        (⊤ : Submodule O (N.H0 O)) ≤ (⊤ : Submodule O (N.H0 O)).comap Φ :=
  fun a ha ↦ (h_tors_lift a ha).right.imp fun _ hΦ ↦ ⟨hΦ, le_top⟩

/-- Assume the standing hypotheses from the section head (`h`, `IsPosRiemann B`, unit `n` with
`h_tors_lift`, `s'` killing `u.lattice`, `A'` proper, `hM`). Let `π : A' ⟶ A` be a homomorphism that
sends `s' z` to `u.expMap z`. Let the theta coordinates `f` of `M` along `s'` have the same type
`(B, χ)` as those of `N`. Let `ν^* π^* N ⊗ M ^ m` and `ν^* M ⊗ (π^* N) ^ m` have the same class,
where `ν` is multiplication by `n` on `A'` and `m = n ^ 2`. Then `π` has a section `e` that sends
`u.expMap z` to `s' z` and satisfies `[e^* M] = [N]`. -/
lemma exists_section_of_hasThetaCoords (π : A' ⟶ A) [IsAdditive π] {f : V → κ → ℂ}
    {ν : A'.left ⟶ A'.left} {m : ℕ} (hm : n ^ 2 = m) (h_lift : ∀ z : V, s' z ≫ π = u.expMap z)
    (hf : HasThetaCoords u.lattice (atGeneric s') M B χ f) (hν_def : (n • 𝟙 A').left = ν)
    (h_cls :
      (((N.pull π.left).pull ν).mul (M.pow m)).picClass =
        ((M.pull ν).mul ((N.pull π.left).pow m)).picClass) :
    ∃ e : A ⟶ A',
      -- (a) `e` extends the given points
      (∀ z : V, u.expMap z ≫ e = s' z) ∧
      -- (b) `e` pulls `M` back to `N`
      (M.pull e.left).picClass = N.picClass ∧
      -- (c) `e` is a section of `π`
      e ≫ π = 𝟙 A := by
  -- The coordinates `f` of `M`, scaled by `γ`, are sections `r j` of `N`. If they have no common
  -- zero, they define a linear system on `A` that agrees with `M` on the points of the
  -- uniformisation, hence a map `e`. Common zeros are excluded on the closure `Γ` of the `s' z`.
  have hν (z : V) : atGeneric s' ((n : V →L[ℂ] V) z) = atGeneric s' z ≫ ν := by
    simp [atGeneric, ← hν_def, comp_nsmul, ← comp_left]
  have hπ (z : V) : atGeneric u.expMap z = atGeneric s' z ≫ π.left := by simp [atGeneric, ← h_lift]
  -- `n` is a unit of the domain `O`, so `m = n ^ 2` is not `0`
  have hm0 : m ≠ 0 := hm.symm.trans_ne (pow_ne_zero 2 fun h0 ↦ by simp [h0] at hn)
  -- `w` is a frame of the quotient of the two bundles in `h_cls`: an isomorphism between them.
  obtain ⟨w, hw⟩ := picClass_eq_iff.mp h_cls
  obtain ⟨Γ, p, P, _, hP, hΓ⟩ : ∃ (Γ : Scheme) (p : Γ ⟶ A'.left) (P : V → (Spec (.of ℂ) ⟶ Γ)),
      IsClosedImmersion p ∧ (∀ z, P z ≫ p = atGeneric s' z) ∧ IsSeparatingFamily P :=
    exists_reduced_closure _
  have hA : IsSeparatingFamily (atGeneric u.expMap) :=
    isSeparatingFamily_atGeneric_of_surjective u.surjective
  -- `Γ → A` is proper and its image holds the dense points `atGeneric u.expMap z`
  have h_surj : AlgebraicGeometry.Surjective (p ≫ π.left) :=
    hA.2.surjective _ P fun z ↦ by rw [← Category.assoc, hP, ← hπ]
  -- a coordinate `i₀` of `M` whose theta function does not vanish at `0`
  obtain ⟨i₀, hi₀⟩ := (hf.hasFieldCoords 0).exists_ne_zero
  have hf_ne : (fun z : V ↦ f z i₀) ≠ 0 := ne_of_apply_ne (fun g ↦ g 0) hi₀
  -- Sections `r j` of `N` with value `γ * f z j / θ z i` at `u.expMap z` in chart `i` (`hr`), not
  -- all zero on the orbit of any field-valued point under the dual lattice (`h_orbit`).
  obtain ⟨γ, hγ, r, hr, h_orbit⟩ :=
    exists_sections_of_translation_stable (N := ⊤) u h hn (fun a ha ↦ (h_tors_lift a ha).left)
      (exists_isTranslationLift_top_of_dualLattice u h_tors_lift) (by simp) hf.mem_thetaSpace
      i₀ hf_ne
  -- Both sides of `h_cls` have theta coordinates along `s'`, so `w` at `s' z` is a constant `c`
  -- times their quotient `f (n • z) θ(z) ^ m / (θ (n • z) f(z) ^ m)` (`hw_val`).
  have hθ := h.pull 1 hπ fun _ ↦ id
  have hn_mem (l) (hl : l ∈ u.lattice) : (n : V →L[ℂ] V) l ∈ u.lattice := by
    simpa only [ContinuousLinearMap.natCast_apply, nsmul_eq_mul] using nsmul_mem hl n
  obtain ⟨-, -, c, hw_val⟩ :=
    ((hθ.pull _ hν hn_mem).mul (hf.pow _)).riemannForm_eq_of_isFrame
      ((hf.pull _ hν hn_mem).mul (hθ.pow _)) hw (hf.holomorphicAt hM)
      fun l hl ↦ atGeneric_add_of_map_eq_zero s' (hs' l hl)
  have h_nonzero (i : ι) (K : Type) [Field K] (ζ : Spec (.of K) ⟶ Γ)
      (hi : LandsIn (ζ ≫ p ≫ π.left) (N.opens i)) :
      ∃ j : κ, (r j : N.H0 O).val i (.of K) (ζ ≫ p ≫ π.left) ≠ 0 := by
    -- If all `r j` vanish at `ζ`, they vanish on its orbit, which `h_orbit` forbids.
    by_contra h_zero
    obtain ⟨z₀, hz₀, j, a, h_ne⟩ := h_orbit K (ζ ≫ p ≫ π.left)
    refine h_ne ?_
    wlog ha : LandsIn ((ζ ≫ p ≫ π.left) ≫ (translation (u.expMap z₀)).left) (N.opens a)
    · exact LineBundle.H0.val_eq_zero_of_not_landsIn (r j : N.H0 O) a _ _ ha
    -- `T` is the translation by `s' z₀`; `T ≫ ν = ν` because `n • z₀` lies in the lattice.
    obtain ⟨h_tors, -⟩ := h_tors_lift z₀ hz₀
    let T : A'.left ⟶ A'.left := (translation (s' z₀)).left
    have hTν : T ≫ ν = ν := by
      simp [T, ← hν_def, ← comp_nsmul _, ← map_nsmul, hs' _ h_tors, ← comp_left, comp_nsmul]
    have hT (x : V) : atGeneric s' x ≫ T = atGeneric s' (x + z₀) := by
      simp [T, atGeneric, ← comp_left, comp_add]
    have hTπ : π.left ≫ (translation (u.expMap z₀)).left = T ≫ π.left := by
      simp [T, h_lift, ← comp_left, comp_add, add_comp]
    let Q := M.mul (N.pull π.left)
    obtain ⟨⟨b, b₁, b', i'⟩, hb⟩ := (M.mul ((M.pull T).mul (Q.pull ν))).exists_landsIn (ζ ≫ p)
    have hr_reg (j : κ) := (LineBundle.H0.isSection_val (r j : N.H0 O)).left
    have hw_unit (x) := hw.isUnit_apply x (.of K)
    obtain ⟨h_lin, h_ah, h_mem, h_lifts⟩ := hf
    have hM_reg (i j : κ) : (M.transition i j).IsRegularOn (M.opens i) :=
      h_lin.isRegularOn_transition i j
    -- At `s' z` the function `φ b i j` is `(f j / f b) ^ m` times a factor that depends only on
    -- `n • z` modulo the lattice; this factor is invariant under `T`. This gives `key` at the
    -- points `P z`, hence on `Γ`.
    let φ (b : κ) (i : ι) (j : κ) : PointFn A'.left :=
      w ((i', fun _ ↦ b), b', fun _ ↦ i) * ((r j : N.H0 O).val i ^ m).pull π.left
    simp [IsFrame, IsSection, IsRegularOn, pow, landsIn_iInf] at hw
    simp only [IsRegularOn] at hr_reg hM_reg
    simp only [pow, mul_opens, pull_opens, pi_opens, inv_opens, landsIn_inf, landsIn_preimage,
      assoc, landsIn_iInf, isUnit_iff_ne_zero] at hw_unit
    simp only [IsHomogeneousCoords, isUnit_iff_ne_zero, ne_eq, Ring.inverse_eq_inv'] at h_lifts
    push Not at h_zero
    simp only [assoc, hTπ] at ha
    simp only [mul_opens, pull_opens, landsIn_inf, landsIn_preimage, assoc, Q] at hb
    have key : (φ b i b * (M.transition b₁ j ^ m).pull T).pull p _ ζ =
        (φ b₁ a j).pull (p ≫ T) _ ζ := by
      -- Both sides are regular on the open `U` of `Γ` and agree at the `P z` in it; `ζ` is in `U`.
      refine hΓ.pointFn_ext
        (U := p ⁻¹ᵁ (Q.opens (b, i) ⊓ T ⁻¹ᵁ Q.opens (b₁, a) ⊓ ν ⁻¹ᵁ Q.opens (b', i'))) ?_ ?_ ?_ _ ζ
        (by simp [Q, hi, ha, hb])
      · simp +contextual [Q, φ, hw, hr_reg, hM_reg, IsRegularOn]
      · simp +contextual [Q, φ, hw, hr_reg, hTν, reassoc_of% hTν, IsRegularOn]
      · simp +contextual [Q, φ, hw_val, hr, ← assoc, hP, hT, ← hν, h.hasFieldCoords .., h_lifts,
          ← hπ, (h.mem_thetaSpace _).2, (h_mem _).2, h_tors, h_ah.ne_zero,
          mul_pow, div_pow, field]
    -- At `ζ` the left side vanishes, and the right side is a unit times a power of `r j`.
    simpa [φ, hw_unit, h_zero, ha, hb, hi, hm0, hTπ, hTν, reassoc_of% hTν] using key
  -- The `r j` give a map `W` to projective space that pulls the hyperplane class back to `N`.
  obtain ⟨W, hW_cls, hW⟩ :=
    exists_picClass_eq_pull_hyperplane (p ≫ π.left)
      (fun j ↦ LineBundle.H0.isSection_val (r j : N.H0 O)) h_nonzero
  have h_lifts (z : V) :
      ((ProjSpace.hyperplaneBundle κ).pull W).IsHomogeneousCoords (atGeneric u.expMap z) (f z) := by
    obtain ⟨i, hi⟩ := (h.hasFieldCoords z).exists_ne_zero
    simpa [IsHomogeneousCoords, hr, hγ, hi, field] using hW i _ _
      ((h.hasFieldCoords ..).1.2 hi.isUnit)
  -- `u.expMap z` and `s' z` have the same coordinates `f z`, and `M` is an embedding.
  obtain ⟨e, he, heM⟩ :=
    hA.exists_map_of_coords (ProjSpace.isLinearSystem_hyperplaneBundle.pull W) hM h_lifts
      hf.hasFieldCoords
  have he' (z : V) : u.expMap z ≫ e = s' z := bijective_restrict_genericPt.injective (he z)
  exact ⟨e, he', by rw [heM, hW_cls],
    hA.hom_ext fun z ↦ by
      simp only [Category.assoc, reassoc_of% (he' z), h_lift, Category.comp_id]⟩

/-- Let `u` uniformise the abelian scheme `A` over `O`, and let `N` be a projective embedding of `A`
with theta coordinates of type `(B, χ)` along `u`, where `B` is positive. Let `n` be a unit of `O`
such that each `a` in `B.dualLattice` has `n • a ∈ u.lattice` and translation by `u.expMap a` lifts
to sections of `N`. Let `s'` be a homomorphism from `V` to the sections of a commutative group `A'`
proper over `O` that kills `u.lattice`, and let `M` be a projective embedding of `A'` with theta
coordinates of type `(μ • B, χ ^ μ)` along `s'`. If the classes of `N` and `M` obey the
parallelogram law (`ParallelogramLaw`; through `pull_nsmul_eq_sq_smul`, pulling back along
multiplication by `d` then multiplies the class by `d ^ 2`), then there is a homomorphism
`ψ : A ⟶ A'` that (a) sends `u.expMap z` to `s' z` for all `z`, and (b) satisfies
`ψ^* [M] = μ • [N]`. -/
lemma exists_hom_of_hasThetaCoords (hN : N.IsProjEmbedding A.hom)
    (hN_par : N.picClass.ParallelogramLaw) (hM_par : M.picClass.ParallelogramLaw) {μ : ℕ}
    {θ' : V → κ → ℂ} (h' : HasThetaCoords u.lattice (atGeneric s') M (μ • B) (χ ^ μ) θ') :
    ∃ ψ : A ⟶ A',
      IsAdditive ψ ∧
      -- (a)
      (∀ z : V, u.expMap z ≫ ψ = s' z) ∧
      -- (b)
      M.picClass.pull ψ.left = μ • N.picClass := by
  -- Apply `exists_section_of_hasThetaCoords` to the projection `A × A' → A`, the points
  -- `S z = (u.expMap z, s' z)`, the bundle `N ^ (μ + k)` on `A` and the embedding `M ⊠ N ^ k`, both
  -- of type `(μ + k) • B`. The section it gives is the graph of `ψ`.
  -- `μ + 1` and `μ + 2` differ by `1`, so they are not both in the maximal ideal of `O`.
  obtain ⟨k, hk, hμk⟩ : ∃ k ≠ 0, IsUnit (↑(μ + k) : O) := by
    by_contra! h_none
    simpa [← one_add_one_eq_two] using
      (IsLocalRing.maximalIdeal O).sub_mem (h_none 2 nofun) (h_none 1 nofun)
  have : NeZero (μ + k) := ⟨by omega⟩
  let S := AddMonoidHom.mk' (fun z ↦ lift (u.expMap z) (s' z)) fun a b ↦ by
    ext1 <;> simp [add_comp]
  let Q := (M.pull (snd A A').1).mul ((N.pow k).pull (fst A A').1)
  have hQ : Q.IsProjEmbedding ((fst A A').1 ≫ A.hom) :=
    (hM.of_isPullback (.flip (.of_hasPullback ..))).mul (hN.pow hk)
  have hQ_theta : HasThetaCoords u.lattice (atGeneric S) Q ((μ + k) • B) (χ ^ (μ + k))
      fun z i ↦ θ' z i.1 * ∏ a, θ z (i.2 a) := by
    rw [add_smul, pow_add]
    exact (h'.pull 1 (by simp [atGeneric, S, ← comp_left, -snd_left, -lift_left]) fun _ ↦ id).mul
      ((h.pow k).pull 1 (by simp [atGeneric, S, ← comp_left, -fst_left, -lift_left]) fun _ ↦ id)
  have hS (l) (hl : l ∈ u.lattice) : S l = 0 := by
    ext1 <;> simp [S, hs' l hl, (u.eq_zero_iff l).1 hl]
  -- The dual lattice of `(μ + k) • B` is carried into the lattice by `(μ + k) * n`, and its
  -- translations lift to `N ^ (μ + k)`: apply `h_tors_lift` to `(μ + k) • a`.
  have h_dual : ∀ a ∈ RealComplexForm.dualLattice ((μ + k) • B),
      ((μ + k) * n) • a ∈ u.lattice ∧ ∃ Φ, IsTranslationLift (N.pow (μ + k)) (u.expMap a) Φ := by
    clear * - h_tors_lift hN_par
    simp_all [exists_isTranslationLift_iff, ThetaTori.mem_dualLattice_nsmul, mul_nsmul,
      hN_par.nsmul_pairing_eq_pairing_nsmul, ← comp_nsmul, ← map_nsmul]
  -- By `pull_nsmul_eq_sq_smul`, pulling back along multiplication by `d` multiplies the classes of
  -- `N` and `M` by `d ^ 2`.
  let N' := (N.pow (μ + k)).pull (fst A A').1
  let ν (d : ℕ) := (d • 𝟙 (MonoidalCategoryStruct.tensorObj A A')).left
  have h_cls (d : ℕ) :
      ((N'.pull (ν d)).mul (Q.pow (d ^ 2))).picClass =
        ((Q.pull (ν d)).mul (N'.pow (d ^ 2))).picClass := by
    have hN_sq := congrArg (·.pull (fst A A').1) (pull_nsmul_eq_sq_smul hN_par d)
    have hM_sq := congrArg (·.pull (snd A A').1) (pull_nsmul_eq_sq_smul hM_par d)
    linear_combination (norm := (simp [Q, N', ν, ← Pic.pull_picClass, ← Pic.pull_comp, ← comp_left,
      nsmul_comp, comp_nsmul, sub_eq_zero, -fst_left, -snd_left]; module)) μ • hN_sq - hM_sq
  obtain ⟨e, he, he_cls, he_fst⟩ :=
    exists_section_of_hasThetaCoords u (h.pow _) hS (mod_cast hμk.mul hn) h_dual hQ (fst ..) rfl
      (by simp [S]) hQ_theta rfl (h_cls _)
  have hψ (z) : u.expMap z ≫ e ≫ snd A A' = s' z := by simp [reassoc_of% he, S]
  refine ⟨e ≫ snd .., isAdditive_of_universal ?_, hψ, by simpa [Q, add_smul, he_fst,
    ← Pic.pull_picClass, ← Pic.pull_comp, ← comp_left, -snd_left, -fst_left] using he_cls⟩
  -- Additivity can be checked on the dense family of sections of `A × A`.
  have : Smooth (MonoidalCategoryStruct.tensorObj A A).hom := by
    rw [tensorObj_hom]
    infer_instance
  refine (isSeparatingFamily_atGeneric_of_surjective
      (homEquivToProd.symm.surjective.comp (u.surjective.prodMap u.surjective))).hom_ext ?_
  simp [reassoc_of% comp_add, ← comp_add _, ← map_add, reassoc_of% he, S, comp_add]

end ArcExtension

end New.Variety
end
end

section
/-!
# Existence in Appell–Humbert: projective embeddings are given by theta functions

The existence half of the Appell–Humbert theorem, for a projective embedding N of a uniformised
group A(ℂ) = V/L whose class satisfies the parallelogram law.

* `New.Uniformisation.appell_humbert`: the coordinates of N are theta functions for some
  Appell–Humbert data (L, B, χ) with positive Riemann form.
* `New.exists_analyticAt_double_eq`, `New.exists_extension_double`, `New.induction_on_double`: the
  doubling equation near 0, and its continuation to the whole space by halving.

Idea: the parallelogram law gives a frame on A × A, and its values define a function c. After
multiplying c by exp q(z, z) for a suitable quadratic form q, the doubling equation
σ(2z) = σ(z)⁴c(z) is solved near 0 and continued to V by halving. Then σ trivialises the pullback of
N.

`New.Uniformisation` A V is a surjective homomorphism e = `u.expMap` : V → A(ℂ), holomorphic and
immersive, with kernel the lattice L = `u.lattice`. `New.HasThetaCoords` says that θ(z) gives
homogeneous coordinates of e(z), each θ_i a theta function of type (B, χ): entire, with
θ_i(z + l) = χ(l)·exp(B l z + B l l / 2)·θ_i(z) for l in L.

Notions from other files:
* `New.atGeneric`: For a family s of sections of A over Spec O, O a valuation ring of ℂ, the complex
  point of A given by s(z) at the generic point.
* `New.LineBundle.IsHomogeneousCoords`: v is a vector of homogeneous coordinates of the point t for
  L: t lands in U_j exactly when v_j is a unit, and then g_jk(t) = v_k/v_j.
* `New.IsAppellHumbert`: Re B is symmetric, and on L one has |χ| = 1 and χ(l + m) = χ(l)χ(m)·exp(πi
  E(m, l)), E the Riemann form of B.
* `New.IsPosRiemann`: The Riemann form E of B is positive: E(u, iu) > 0 for every u ≠ 0.
* `New.Pic.ParallelogramLaw`: The parallelogram law for a class c in Pic A:
  (x+y)^*c + (x−y)^*c + 2·0^*c = 2(x^*c + y^*c) in Pic T for all T-points x, y of A and all
  S-schemes T.

## Relation to the literature

Known result: Appell–Humbert theorem, a step in the complex uniformisation of PEL abelian varieties.
For a given uniformisation, this file proves the existence half, for a very ample class obeying the
parallelogram law. Source: J. S. Milne, Introduction to Shimura Varieties (2005/2017), Theorem 8.17
and Lemma 5.12; R. Kottwitz, Points on some Shimura varieties over finite fields, J. AMS 5 (1992)
§8; G. Shimura, On analytic families of polarized abelian varieties and automorphic functions, Ann.
Math. 78 (1963); A. Borel, Some finiteness properties of adele groups over number fields, Publ. IHES
16 (1963); D. Mumford, Abelian Varieties §§1–2; L. Breen, Fonctions thêta et théorème du cube, LNM
980 (1983).
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory Complex Over New LineBundle PointFn NormedAddGroup

/-- For `f` analytic at `0`, the equation `g (2z) = 4 g z + f z` has a solution analytic at `0`, up
to a quadratic form. -/
lemma New.exists_analyticAt_double_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : V → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ (g : V → ℂ) (q : V →L[ℂ] V →L[ℂ] ℂ),
      AnalyticAt ℂ g 0 ∧ ∀ᶠ z : V in nhds 0, g (z + z) = 4 * g z + f z + q z z := by
  obtain ⟨P, hP⟩ := hf
  -- In degree `n` the equation reads `(2 ^ n - 4) G n = P n`; for `n = 2`, `G 2 = 0` and `q`
  -- cancels `P 2`.
  let G : FormalMultilinearSeries ℂ V ℂ := fun n ↦ (2 ^ n - 4 : ℝ)⁻¹ • P n
  have h_ball : ∀ᶠ z : V in nhds 0, z ∈ Metric.eball 0 G.radius :=
    Metric.eball_mem_nhds _ <| hP.radius_pos.trans_le <| G.radius_le_of_le fun n ↦ by
      simpa [G, norm_smul] using
        mul_le_of_le_one_left (norm_nonneg _) (2 ^ n - 4 : ℤ).natAbs.cast_inv_le_one
  refine ⟨G.sum, -continuousMultilinearCurryFin1 ℂ V _ (P 2).curryRight,
    G.analyticOnNhd _ h_ball.self_of_nhds, ?_⟩
  filter_upwards [h_ball,
    ((by fun_prop : Continuous fun z : V ↦ z + z).tendsto' 0 0 (add_zero 0)).eventually h_ball,
    hP.eventually_hasSum] with z hz hz₂ hfz
  -- Summing over `n`, all terms except `n = 2` cancel against the inverse in `G n`.
  rw [eq_add_of_sub_eq <| ((G.hasSum hz₂).sub (((G.hasSum hz).mul_left 4).add hfz)).unique
    (hasSum_single 2 fun n hn ↦ by
      have h_ne : (2 : ℂ) ^ n ≠ 4 := mod_cast (Nat.pow_right_injective le_rfl).ne hn
      simp [← two_smul ℂ, (P _).map_smul_univ, G, fieldEq])]
  norm_num [G, add_comm,
    (by simp [funext_iff, Fin.forall_fin_two] : Fin.snoc (Fin.snoc 0 z) z = fun _ : Fin 2 ↦ z)]

/-- For `r > 0` and `‖z‖ ≥ r`, halving `z` lowers `⌊‖z‖ / r⌋₊`. -/
lemma New.floor_norm_half_div_lt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ}
    (hr : 0 < r) {z : V} (hz : ¬‖z‖ < r) :
    ⌊‖(2⁻¹ : ℂ) • z‖ / r⌋₊ < ⌊‖z‖ / r⌋₊ := by
  -- Halving divides `‖z‖ / r ≥ 1` by two, which lowers its floor.
  have h_le : r ≤ ‖z‖ := not_lt.1 hz
  grw [Nat.floor_lt, ← Nat.div_two_lt_floor]
  · rw [norm_smul, norm_inv, Complex.norm_ofNat, inv_mul_eq_div, div_right_comm]
  · exact (one_le_div hr).2 h_le
  · positivity

/-- Induction by doubling: a property that holds on the ball of radius `r > 0` around `0` and
passes from `z` to `z + z` holds on the whole space. -/
lemma New.induction_on_double {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ}
    (hr : 0 < r) {p : V → Prop} (h_small : ∀ z : V, ‖z‖ < r → p z)
    (h_double : ∀ z : V, p z → p (z + z)) (z : V) :
    p z := by
  induction z using (measure fun z : V ↦ ⌊‖z‖ / r⌋₊).wf.induction with
  | h z ih =>
    by_cases hz : ‖z‖ < r
    · exact h_small z hz
    · have h := h_double _ (ih _ (floor_norm_half_div_lt hr hz))
      rwa [← two_smul ℂ, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul] at h

/-- A solution of `σ (2z) = σ z ^ 4 * c z` on a ball around `0` extends to the whole space. -/
lemma New.exists_extension_double {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ}
    (hr : 0 < r) {σ₀ c : V → ℂ}
    (h₀ : ∀ z : V, ‖z‖ < r → ‖z + z‖ < r → σ₀ (z + z) = σ₀ z ^ 4 * c z) :
    ∃ σ : V → ℂ, (∀ z : V, ‖z‖ < r → σ z = σ₀ z) ∧ ∀ z : V, σ (z + z) = σ z ^ 4 * c z := by
  -- Outside the ball put `σ z = σ (z / 2) ^ 4 * c (z / 2)`, a recursion on `⌊‖z‖ / r⌋₊`.
  obtain ⟨σ, hσ⟩ : ∃ σ : V → ℂ, ∀ z : V,
      σ z = if ‖z‖ < r then σ₀ z else σ ((2⁻¹ : ℂ) • z) ^ 4 * c ((2⁻¹ : ℂ) • z) :=
    ⟨_, (measure fun z : V ↦ ⌊‖z‖ / r⌋₊).wf.fix_eq fun z F ↦ if hz : ‖z‖ < r then σ₀ z else
      F _ (floor_norm_half_div_lt hr hz) ^ 4 * c ((2⁻¹ : ℂ) • z)⟩
  refine ⟨σ, fun z hz ↦ by rw [hσ, ite_eq_left hz], fun z ↦ ?_⟩
  by_cases hz : ‖z + z‖ < r
  · have hz' : ‖z‖ < r := by linarith [(SameRay.refl z).norm_add, norm_nonneg z]
    rw [hσ (z + z), hσ z, ite_eq_left hz, ite_eq_left hz', h₀ z hz' hz]
  · rw [hσ (z + z), ite_eq_right hz, ← two_smul ℂ z, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]

/-- Let `Φ z` have no zero near `z`, with `Φ 0 / Φ z` analytic at `z` and `Φ 0 0 = 1`. Let `c`
have no zero, with `c 0 = 1` and `x ↦ c x * Φ (2a) (2x) / Φ a x ^ 4` analytic at `a`.
Then the doubling equation `σ (2z) = σ z ^ 4 * exp (q z z) * c z` holds for some bilinear form `q`
and some `σ` without zero such that `σ * Φ z` is analytic at `z`. -/
private lemma New.exists_analyticAt_mul_double_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {Φ : V → V → ℂ} {c : V → ℂ} (Φ_zero : Φ 0 0 = 1)
    (Φ_ne : ∀ z : V, ∀ᶠ w : V in nhds z, Φ z w ≠ 0)
    (Φ_an : ∀ z : V, AnalyticAt ℂ (fun w : V ↦ Φ 0 w / Φ z w) z)
    (c_zero : c 0 = 1) (c_ne : ∀ z : V, c z ≠ 0)
    (c_an : ∀ a : V, AnalyticAt ℂ (fun x : V ↦ c x * Φ (a + a) (x + x) / Φ a x ^ 4) a) :
    ∃ (σ : V → ℂ) (q : V →L[ℂ] V →L[ℂ] ℂ),
      (∀ z : V, σ z ≠ 0) ∧
      (∀ z : V, AnalyticAt ℂ (σ * Φ z) z) ∧
      ∀ z : V, σ (z + z) = σ z ^ 4 * (exp (q z z) * c z) := by
  -- Near `0`, `σ` is `exp g / Φ 0`, with `g` solving the logarithm of the doubling equation.
  let f (z : V) : ℂ := log (c z * Φ 0 (z + z) / Φ 0 z ^ 4)
  have hf : AnalyticAt ℂ f 0 := by
    have h_an : AnalyticAt ℂ (fun z : V ↦ c z * Φ 0 (z + z) / Φ 0 z ^ 4) 0 := by
      simpa only [add_zero] using c_an 0
    exact h_an.clog (by simp [c_zero, Φ_zero])
  obtain ⟨g, q, hg, hg_double⟩ := exists_analyticAt_double_eq hf
  obtain ⟨r, hr, h_small⟩ : ∃ r > 0, ∀ ⦃z : V⦄, ‖z‖ < r →
      Φ 0 z ≠ 0 ∧ AnalyticAt ℂ g z ∧ g (z + z) = 4 * g z + f z + q z z :=
    nhds_zero_basis_norm_lt.eventually_iff.1 ((Φ_ne 0).and (hg.eventually_analyticAt.and hg_double))
  -- The doubling equation holds there, so `σ` extends to `V`.
  obtain ⟨σ, hσ, σ_double⟩ : ∃ σ : V → ℂ, (∀ z : V, ‖z‖ < r → σ z = exp (g z) / Φ 0 z) ∧
      ∀ z : V, σ (z + z) = σ z ^ 4 * (exp (q z z) * c z) := by
    refine exists_extension_double hr fun z hz hz₂ ↦ ?_
    obtain ⟨h_ne, -, h_double⟩ := h_small hz
    obtain ⟨h_ne₂, -⟩ := h_small hz₂
    have h_arg : c z * Φ 0 (z + z) / Φ 0 z ^ 4 ≠ 0 :=
      div_ne_zero (mul_ne_zero (c_ne z) h_ne₂) (pow_ne_zero 4 h_ne)
    rw [h_double, exp_add, exp_add, show f z = log (c z * Φ 0 (z + z) / Φ 0 z ^ 4) from rfl,
      exp_log h_arg, div_pow, ← Nat.cast_ofNat (n := 4), exp_natCast_mul]
    field_simp [h_ne, h_ne₂]
    exact mul_comm _ _
  suffices σ_spec : ∀ z : V, σ z ≠ 0 ∧ AnalyticAt ℂ (σ * Φ z) z from
    ⟨σ, q, fun z ↦ (σ_spec z).1, fun z ↦ (σ_spec z).2, σ_double⟩
  refine induction_on_double hr (fun z hz ↦ ?_) fun x ⟨h_ne, h_an⟩ ↦ ?_
  · -- Inside the ball `σ * Φ z` is `exp g` divided by the analytic function `Φ 0 / Φ z`.
    obtain ⟨h_ne, hg_an, -⟩ := h_small hz
    have h_an : AnalyticAt ℂ (fun y : V ↦ exp (g y) / (Φ 0 y / Φ z y)) z :=
      hg_an.cexp.div (Φ_an z) (div_ne_zero h_ne (Φ_ne z).self_of_nhds)
    refine ⟨by rw [hσ z hz]; exact div_ne_zero (exp_ne_zero _) h_ne, h_an.congr ?_⟩
    filter_upwards [tendsto_norm (gt_mem_nhds hz)] with y (hy : ‖y‖ < r)
    rw [Pi.mul_apply, hσ y hy, div_div_eq_mul_div, div_mul_eq_mul_div]
  · -- By the doubling equation, `y ↦ (σ * Φ (2x)) (2y)` is a product of functions analytic at `x`.
    have q_an : AnalyticAt ℂ (fun y : V ↦ q y y) x :=
      (q.analyticAt_bilinear (x, x)).comp₂ analyticAt_id analyticAt_id
    have h_double : AnalyticAt ℂ (fun y : V ↦ (σ * Φ (x + x)) (y + y)) x := by
      refine (((h_an.pow 4).mul (c_an x)).mul q_an.cexp).congr ?_
      filter_upwards [Φ_ne x] with y hy
      simp only [Pi.pow_apply, Pi.mul_apply, Function.comp_apply]
      rw [σ_double y, mul_pow, mul_div_assoc', mul_right_comm (σ y ^ 4),
        ← mul_assoc (σ y ^ 4), mul_div_cancel_right₀ _ (pow_ne_zero 4 hy)]
      ring
    -- Compose with the halving map.
    have h_half : AnalyticAt ℂ (fun y : V ↦ (2⁻¹ : ℂ) • y) (x + x) :=
      analyticAt_const.smul analyticAt_id
    have h_id (y : V) : (2⁻¹ : ℂ) • y + (2⁻¹ : ℂ) • y = y := by
      rw [← two_smul ℂ, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]
    refine ⟨?_, ?_⟩
    · rw [σ_double]
      exact mul_ne_zero (pow_ne_zero 4 h_ne) (mul_ne_zero (exp_ne_zero _) (c_ne x))
    · exact (h_double.comp_of_eq h_half (by
        rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul])).congr
        (.of_forall fun y ↦ congrArg (σ * Φ (x + x)) (h_id y))

/-- Let `W` be entire on `V × V` without zero, and let `y ↦ W (2x, 2y) / W (x, y) ^ 4` be periodic
for the lattice `L`. Then the logarithmic derivative of `W` in the second variable is linear. -/
private lemma New.exists_linear_logDeriv_of_periodic {V : Type} [FinComplexSpace V]
    {L : Submodule ℤ V} [IsFullRankLattice L] {W : V × V → ℂ} (W_ne : ∀ u : V × V, W u ≠ 0)
    (W_an : ∀ u : V × V, AnalyticAt ℂ W u)
    (h_per : ∀ x y : V, ∀ l ∈ L,
      W (x + x, y + l + (y + l)) / W (x, y + l) ^ 4 = W (x + x, y + y) / W (x, y) ^ 4) :
    ∃ T : V × V →L[ℂ] V →L[ℂ] ℂ,
      ∀ x y : V, HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • T (x, y)) y := by
  let P (u : V × V) : V →L[ℂ] ℂ := (W u)⁻¹ • fderiv ℂ W u ∘L .inr ℂ V V
  have hP (x y : V) : HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • P (x, y)) y := by
    rw [smul_inv_smul₀ (W_ne _)]
    exact (W_an _).differentiableAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have P_double : ∀ u : V × V, P (u + u) = P u + P u := by
    rintro ⟨x, y⟩
    -- `R` is a theta function for `B = 0` and `χ = 1` without zero, hence constant.
    let R (z : V) : ℂ := W (x + x, z + z) / W (x, z) ^ 4
    have W_diff : Differentiable ℂ W := fun u ↦ (W_an u).differentiableAt
    have R_diff : Differentiable ℂ R := by
      have hR_eq : R = fun w : V ↦ W (x + x, w + w) * (W (x, w) ^ 4)⁻¹ :=
        funext fun _ ↦ div_eq_mul_inv _ _
      rw [hR_eq]
      exact fun z ↦
        (W_diff.differentiableAt.comp z ((differentiableAt_const (x + x)).prodMk
          (differentiableAt_id.add differentiableAt_id))).fun_mul
          (((W_diff.differentiableAt.comp z ((differentiableAt_const x).prodMk
            differentiableAt_id)).fun_pow 4).fun_inv (pow_ne_zero 4 (W_ne (x, z))))
    have R_mem : R ∈ RealComplexForm.thetaSpace (L := L) 1 0 :=
      ⟨R_diff, fun l hl z ↦ by simpa using h_per x z l hl⟩
    have h_data : IsAppellHumbert (L := L) 0 1 := by simp [isAppellHumbert_iff]
    obtain ⟨-, -, R_eq⟩ := h_data.eq_exp_of_ne_zero R_mem
      (fun z ↦ div_ne_zero (W_ne _) (pow_ne_zero 4 (W_ne _)))
    have h_const (z : V) : W (x + x, z + z) = R 0 * W (x, z) ^ 4 :=
      (div_eq_iff (pow_ne_zero 4 (W_ne _))).1 (by simpa using R_eq z)
    -- Differentiate both sides of `h_const` at `y`.
    have h_left : HasFDerivAt (fun z : V ↦ W (x + x, z + z))
        ((2 * W (x + x, y + y)) • P (x + x, y + y)) y := by
      have h_add : HasFDerivAt (fun z : V ↦ z + z) (.id ℂ V + .id ℂ V : V →L[ℂ] V) y :=
        (hasFDerivAt_id y).add (hasFDerivAt_id y)
      refine ((hP (x + x) (y + y)).comp y (f := fun z : V ↦ z + z) h_add).congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul, map_add]
      ring
    have h_right : HasFDerivAt (fun z : V ↦ W (x + x, z + z))
        ((2 * W (x + x, y + y)) • (P (x, y) + P (x, y))) y := by
      simp only [h_const]
      refine (((hP x y).pow 4).const_mul (R 0)).congr_fderiv ?_
      ext v
      simp only [smul_apply, add_apply, smul_eq_mul]
      ring
    exact smul_right_injective _ (mul_ne_zero two_ne_zero (W_ne _)) (h_left.unique h_right)
  -- A map that is differentiable at `0` and commutes with doubling is linear.
  have P_lin : ∀ u : V × V, P u = fderiv ℂ P 0 u :=
    eq_fderiv_of_double P
      (((W_an 0).differentiableAt.inv (W_ne 0)).smul
        ((W_an 0).fderiv.differentiableAt.clm_comp (differentiableAt_const _)))
      P_double
  exact ⟨fderiv ℂ P 0, fun x y ↦ by simpa only [← P_lin] using hP x y⟩

/-- Let `W` have no zero and a linear logarithmic derivative `T` in the second variable. A function
`g` without zero, differentiable at `0`, with
`g (x + y) * g (x - y) * W (l + x, y) = g x ^ 2 * W (x, y)` has constant logarithmic derivative. -/
private lemma New.exists_const_logDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {W : V × V → ℂ} {T : V × V →L[ℂ] V →L[ℂ] ℂ} {g : V → ℂ} {l : V} (W_ne : ∀ u : V × V, W u ≠ 0)
    (hT : ∀ x y : V, HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • T (x, y)) y)
    (g_ne : ∀ z : V, g z ≠ 0) (g_diff : DifferentiableAt ℂ g 0)
    (h_eq : ∀ x y : V, g (x + y) * g (x - y) * W (l + x, y) = g x ^ 2 * W (x, y)) :
    ∃ a : V →L[ℂ] ℂ, ∀ z : V, HasFDerivAt g (g z • a) z := by
  refine ⟨(g 0)⁻¹ • fderiv ℂ g 0 - T (l, 0), fun z ↦ ?_⟩
  -- Write `z = x + x` and differentiate `y ↦ g (x + y)` at `y = x`: the logarithmic derivative is
  -- `T (x, x) - T (l + x, x) + g' 0 / g 0`.
  obtain ⟨x, rfl⟩ : ∃ x : V, z = x + x :=
    ⟨(2⁻¹ : ℂ) • z, by rw [← two_smul ℂ, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]⟩
  refine (hasFDerivAt_comp_add_left x).1 ?_
  have g_add (y : V) : g (x + y) = g x ^ 2 * (W (x, y) * (W (l + x, y) * g (x - y))⁻¹) := by
    field_simp [W_ne, g_ne]
    linear_combination h_eq x y
  have g_sub : HasFDerivAt (fun y : V ↦ g (x - y)) (-fderiv ℂ g 0) x := by
    have g_zero : HasFDerivAt g (fderiv ℂ g 0) (x - x) := by
      simpa only [sub_self] using g_diff.hasFDerivAt
    exact (g_zero.comp x ((hasFDerivAt_id x).const_sub x)).congr_fderiv
      ((ContinuousLinearMap.comp_neg _ _).trans (by rw [ContinuousLinearMap.comp_id]))
  have T_add : T (l + x, x) = T (l, 0) + T (x, x) := by rw [← map_add, Prod.mk_add_mk, zero_add]
  have h_inv := (hasDerivAt_inv (mul_ne_zero (W_ne _) (g_ne _))).comp_hasFDerivAt x
    ((hT (l + x) x).mul g_sub)
  simp only [g_add]
  refine (((hT x x).mul h_inv).const_mul (g x ^ 2)).congr_fderiv ?_
  ext v
  simp only [smul_apply, add_apply, sub_apply, neg_apply, Function.comp_apply, Pi.mul_apply,
    smul_eq_mul, T_add, sub_self]
  have := W_ne (l + x, x)
  have := g_ne 0
  field_simp
  ring

/-- Let `σ` have no zero, satisfy `σ (2l) = σ l ^ 4 * exp (q l l)` on `L` for a bilinear form `q`,
and have the factor of automorphy `exp (B l z) * σ l / σ 0`, with `Re B` symmetric. Then `B` and
`l ↦ σ l / σ 0 / exp (B l l / 2)` are Appell–Humbert data. -/
private lemma New.isAppellHumbert_of_double_eq {V : Type*} [FinComplexSpace V] {L : Submodule ℤ V}
    {σ : V → ℂ} {q : V →L[ℂ] V →L[ℂ] ℂ} {B : RealComplexForm V} (σ_ne : ∀ z : V, σ z ≠ 0)
    (σ_double : ∀ l ∈ L, σ (l + l) = σ l ^ 4 * exp (q l l))
    (σ_add : ∀ l ∈ L, ∀ z : V, σ (z + l) = σ z * exp (B l z) * σ l / σ 0)
    (hB_symm : ∀ u v : V, (B u v).re = (B v u).re) :
    IsAppellHumbert (L := L) B fun l : V ↦ σ l / σ 0 / exp (B l l / 2) := by
  have exp_half (z : ℂ) : exp z = exp (z / 2) ^ 2 := by rw [sq, ← exp_add, add_halves]
  refine ⟨hB_symm, fun l hl ↦ ?_, fun l _ m hm ↦ ?_⟩
  · -- Compare the two formulas for `σ (2m)` at `m = 0`, `2l` and `l`, and eliminate `exp (q l l)`.
    have h_sq (m : V) (hm : m ∈ L) : σ m ^ 2 * σ 0 * exp (q m m) = exp (B m m) := by
      have h_two : σ m ^ 4 * exp (q m m) = σ m * exp (B m m) * σ m / σ 0 :=
        (σ_double m hm).symm.trans (σ_add m hm m)
      field_simp [σ_ne] at h_two
      linear_combination h_two
    have h_zero : σ 0 ^ 3 = 1 := by
      have h := h_sq 0 L.zero_mem
      simp only [map_zero, exp_zero, mul_one] at h
      linear_combination h
    have h_double : σ l ^ 8 * σ 0 * exp (q l l) ^ 6 = exp (B l l) ^ 4 := by
      have h_sq_double := h_sq (l + l) (L.add_mem hl hl)
      simp only [σ_double l hl, map_add, _root_.add_apply, exp_add] at h_sq_double
      linear_combination h_sq_double
    have h_four : σ l ^ 4 = exp (B l l) ^ 2 * σ 0 ^ 4 := by
      refine mul_right_cancel₀ (pow_ne_zero 4 (exp_ne_zero (B l l))) ?_
      calc σ l ^ 4 * exp (B l l) ^ 4
          = σ l ^ 4 * (σ l ^ 8 * σ 0 * exp (q l l) ^ 6) * (σ 0 ^ 3) ^ 3 := by
            rw [h_double, h_zero, one_pow, mul_one]
        _ = (σ l ^ 2 * σ 0 * exp (q l l)) ^ 6 * σ 0 ^ 4 := by ring
        _ = exp (B l l) ^ 2 * σ 0 ^ 4 * exp (B l l) ^ 4 := by
            rw [h_sq l hl]
            ring
    refine norm_eq_one_of_pow_eq_one ?_ four_ne_zero
    rw [div_pow, div_pow, h_four, exp_half (B l l)]
    field_simp [σ_ne]
  · have h_form : Real.pi * I * B.riemannForm m l = (B m l - B l m) / 2 := by
      apply Complex.ext
      · simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, zero_mul,
          sub_re, div_ofNat_re, hB_symm m l, zero_div]
      · simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, sub_im,
          div_ofNat_im, riemannForm_def]
        rw [zero_add, mul_comm 2 Real.pi, ← mul_div_assoc, mul_div_mul_left _ _ Real.pi_ne_zero]
    rw [h_form, σ_add m hm l, exp_half (B m l)]
    simp only [map_add, _root_.add_apply, add_div, sub_div, exp_add, exp_sub]
    field_simp [σ_ne]

/-- If theta functions of type (B, χ) are homogeneous coordinates of a projective embedding of a
uniformised group, then the Riemann form of B is positive. -/
private lemma New.Uniformisation.isPosRiemann_of_hasThetaCoords
    {A : Over (AlgebraicGeometry.Spec (CommRingCat.of ℂ))} [AddObj A] {ι V : Type}
    [FinComplexSpace V] (u : Uniformisation (O := ℂ) A V) {N : LineBundle A.left ι}
    (hN : IsProjEmbedding (ι := ι) N A.hom) {B : ThetaTori.LatticeForm u.lattice} {χ : V → ℂ}
    {θ : V → ι → ℂ} (h_theta : HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ) :
    IsPosRiemann B := by
  refine ⟨fun v hv ↦ not_le.1 fun h_le ↦ hv ?_⟩
  -- If the Riemann form is not positive at `v`, then `θ (t • v)` is a multiple of `θ 0`. As `N`
  -- separates points, `u.expMap` is constant on the line through `v`, so `v = 0`.
  have h_line (t : ℂ) : u.expMap (t • v) = u.expMap 0 := by
    have h_mult : θ (t • v) = (t * t * B v v / 2).exp • θ 0 := funext fun j ↦
      h_theta.isAppellHumbert.apply_smul_of_nonpos (hf := h_theta.mem_thetaSpace j) v h_le t
    exact OverMorphism.ext (hN.eq_of_isHomogeneousCoords
      ((u.expMap (t • v)).w.trans (u.expMap 0).w.symm)
      (by simpa only [h_mult, atGeneric_eq] using h_theta.hasFieldCoords (t • v))
      ((h_theta.hasFieldCoords 0).smul (exp_ne_zero _).isUnit) (N.exists_landsIn _))
  exact ContinuousLinearMap.toSpanSingleton_inj.1
    (u.linear_ext fun t : ℂ ↦ by
      rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_zero]
      exact h_line t)

/-- Let `e : V → G` be additive and zero on the lattice `L`. Let `Φ x x = 1`, with `Φ (e z) ∘ e` not
zero near `z` and `(Φ (e 0) / Φ (e z)) ∘ e` analytic at `z`. Let `C` have no zero, with `C 0 0 = 1`,
and let `C (e x) (e y)`, times `Φ` at `x - y` and `x + y` over `Φ²` at `x` and `y`, be analytic at
each `(a, b)`. Then some `σ` without zero, with `σ * Φ (e z) ∘ e` analytic at `z`, has a factor
of automorphy given by Appell–Humbert data. -/
private lemma New.exists_isAppellHumbert_of_analyticAt {V : Type} [FinComplexSpace V]
    {L : Submodule ℤ V} [IsFullRankLattice L] {G : Type*} [AddGroup G] {e : V →+ G}
    (hL : ∀ l ∈ L, e l = 0) {Φ C : G → G → ℂ} (Φ_self : ∀ x : G, Φ x x = 1)
    (Φ_ne : ∀ z : V, ∀ᶠ w : V in nhds z, Φ (e z) (e w) ≠ 0)
    (Φ_an : ∀ z : V, AnalyticAt ℂ (fun w : V ↦ Φ (e 0) (e w) / Φ (e z) (e w)) z)
    (C_zero : C 0 0 = 1) (C_ne : ∀ x y : G, C x y ≠ 0)
    (C_an : ∀ a b : V, AnalyticAt ℂ (fun ((x, y) : V × V) ↦
      C (e x) (e y) * Φ (e (a - b)) (e (x - y)) * Φ (e (a + b)) (e (x + y)) /
        (Φ (e a) (e x) * Φ (e b) (e y)) ^ 2) (a, b)) :
    ∃ (σ : V → ℂ) (B : RealComplexForm V),
      (∀ z : V, σ z ≠ 0) ∧
      (∀ z : V, AnalyticAt ℂ (fun w : V ↦ σ w * Φ (e z) (e w)) z) ∧
      (∀ l ∈ L, ∀ z : V, σ (z + l) = σ z * exp (B l z) * σ l / σ 0) ∧
      IsAppellHumbert (L := L) B fun l : V ↦ σ l / σ 0 / exp (B l l / 2) := by
  -- The diagonal of `C_an` gives `σ`, a solution of the doubling equation.
  obtain ⟨σ, q, σ_ne, σ_an, σ_double⟩ : ∃ (σ : V → ℂ) (q : V →L[ℂ] V →L[ℂ] ℂ),
      (∀ z : V, σ z ≠ 0) ∧ (∀ z : V, AnalyticAt ℂ (fun w : V ↦ σ w * Φ (e z) (e w)) z) ∧
      ∀ z : V, σ (z + z) = σ z ^ 4 * (exp (q z z) * C (e z) (e z)) := by
    refine exists_analyticAt_mul_double_eq (Φ := fun z w : V ↦ Φ (e z) (e w)) (Φ_self _) Φ_ne Φ_an
      (by simp [C_zero]) (fun _ ↦ C_ne _ _) fun a ↦ ?_
    refine ((C_an a a).comp₂ analyticAt_id analyticAt_id).congr (.of_forall fun x ↦ ?_)
    simp only [id, sub_self, Φ_self]
    ring
  -- `W` compares `C` with the trivialisation given by `σ`; it is entire and has no zero.
  let W : V × V → ℂ := fun (x, y) ↦ (σ x * σ y) ^ 2 * C (e x) (e y) / σ (x - y) / σ (x + y)
  have W_ne (u : V × V) : W u ≠ 0 :=
    div_ne_zero (div_ne_zero (mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (σ_ne _) (σ_ne _)))
      (C_ne _ _)) (σ_ne _)) (σ_ne _)
  have W_an : ∀ u : V × V, AnalyticAt ℂ W u := by
    rintro ⟨a, b⟩
    -- `W` is the function of `C_an` times `(σ * Φ)²` at `x` and `y`, divided by `σ * Φ` at `x - y`
    -- and `x + y`: the factors `Φ`, which are not zero near `(a, b)`, cancel.
    have h_num : AnalyticAt ℂ
        (fun (x, y) ↦ (σ x * Φ (e a) (e x) * (σ y * Φ (e b) (e y))) ^ 2) (a, b) :=
      (((σ_an a).comp_of_eq analyticAt_fst rfl).mul ((σ_an b).comp_of_eq analyticAt_snd rfl)).pow 2
    have h_den : AnalyticAt ℂ (fun (x, y) ↦ σ (x - y) * Φ (e (a - b)) (e (x - y)) *
        (σ (x + y) * Φ (e (a + b)) (e (x + y)))) (a, b) :=
      ((σ_an (a - b)).comp_of_eq (analyticAt_fst.sub analyticAt_snd) rfl).mul
        ((σ_an (a + b)).comp_of_eq (analyticAt_fst.add analyticAt_snd) rfl)
    refine (((C_an a b).mul h_num).div h_den (by
      dsimp only; rw [Φ_self, Φ_self, mul_one, mul_one]; exact mul_ne_zero (σ_ne _) (σ_ne _))).congr
      ?_
    filter_upwards [continuous_fst.continuousAt.eventually (Φ_ne a),
      continuous_snd.continuousAt.eventually (Φ_ne b),
      (continuous_fst.sub continuous_snd).continuousAt.eventually (Φ_ne (a - b)),
      (continuous_fst.add continuous_snd).continuousAt.eventually (Φ_ne (a + b))]
      with ⟨x, y⟩ hx hy hsub hadd
    dsimp only [W, Pi.div_apply, Pi.mul_apply]
    dsimp only [Pi.sub_apply, Pi.add_apply] at hx hy hsub hadd
    rw [show (σ x * Φ (e a) (e x) * (σ y * Φ (e b) (e y))) ^ 2 =
        (σ x * σ y) ^ 2 * (Φ (e a) (e x) * Φ (e b) (e y)) ^ 2 by ring,
      div_mul_eq_mul_div, ← mul_assoc,
      mul_div_cancel_right₀ _ (pow_ne_zero 2 (mul_ne_zero hx hy)),
      show σ (x - y) * Φ (e (a - b)) (e (x - y)) * (σ (x + y) * Φ (e (a + b)) (e (x + y))) =
        (σ (x - y) * σ (x + y)) * (Φ (e (a - b)) (e (x - y)) * Φ (e (a + b)) (e (x + y))) by ring,
      show C (e x) (e y) * Φ (e (a - b)) (e (x - y)) * Φ (e (a + b)) (e (x + y)) * (σ x * σ y) ^ 2 =
        ((σ x * σ y) ^ 2 * C (e x) (e y)) *
          (Φ (e (a - b)) (e (x - y)) * Φ (e (a + b)) (e (x + y))) by ring,
      mul_div_mul_right _ _ (mul_ne_zero hsub hadd), div_div]
  -- By `σ_double` and the parallelogram identity for `q`, the quotient `W (2x, 2y) / W (x, y) ^ 4`
  -- depends only on `e x` and `e y`.
  obtain ⟨T, hT⟩ : ∃ T : V × V →L[ℂ] V →L[ℂ] ℂ,
      ∀ x y : V, HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • T (x, y)) y := by
    have h_ratio (x z : V) :
        W (x + x, z + z) / W (x, z) ^ 4 =
          (C (e x) (e x) * C (e z) (e z)) ^ 2 * C (e (x + x)) (e (z + z)) /
            (C (e x) (e z) ^ 4 * C (e (x - z)) (e (x - z)) * C (e (x + z)) (e (x + z))) := by
      dsimp only [W]
      rw [add_sub_add_comm, add_add_add_comm, σ_double x, σ_double z, σ_double (x - z),
        σ_double (x + z)]
      have hq : exp (q x x) ^ 2 * exp (q z z) ^ 2 =
          exp (q (x - z) (x - z)) * exp (q (x + z) (x + z)) := by
        rw [← exp_natCast_mul, ← exp_natCast_mul, ← exp_add, ← exp_add]
        congr 1
        simp only [map_sub, map_add, sub_apply, add_apply, Nat.cast_ofNat]
        ring
      rw [show (σ x ^ 4 * (exp (q x x) * C (e x) (e x)) *
            (σ z ^ 4 * (exp (q z z) * C (e z) (e z)))) ^ 2 =
          (σ x * σ z) ^ 8 * (C (e x) (e x) * C (e z) (e z)) ^ 2 *
            (exp (q x x) ^ 2 * exp (q z z) ^ 2) by ring, hq]
      have := σ_ne x; have := σ_ne z; have := σ_ne (x - z); have := σ_ne (x + z)
      have := C_ne (e x) (e z); have := C_ne (e (x - z)) (e (x - z))
      have := C_ne (e (x + z)) (e (x + z))
      have := exp_ne_zero (q (x - z) (x - z)); have := exp_ne_zero (q (x + z) (x + z))
      field_simp
    refine exists_linear_logDeriv_of_periodic (L := L) W_ne W_an fun x y l hl ↦ ?_
    rw [h_ratio x (y + l), h_ratio x y]
    simp only [map_add, map_sub, hL l hl, add_zero]
  -- The factor of automorphy `σ (l + ·) / σ` has constant logarithmic derivative.
  have h_log (l : L) : ∃ a : V →L[ℂ] ℂ, ∀ z : V,
      HasFDerivAt (fun w : V ↦ σ (l + w) / σ w) ((σ (l + z) / σ z) • a) z := by
    obtain ⟨l, hl⟩ := l
    -- The factors `Φ` cancel in the quotient, so it is analytic.
    have h_an : AnalyticAt ℂ (fun w : V ↦ σ (l + w) / σ w) 0 :=
      (((σ_an (l + 0)).comp (analyticAt_const.add analyticAt_id)).div (σ_an 0)
        (by rw [Φ_self, mul_one]; exact σ_ne 0)).congr
        ((Φ_ne 0).mono fun w hw ↦ by
          dsimp only [Function.comp_def, Pi.div_apply]
          rw [map_add e l 0, map_add e l w, hL l hl, zero_add, zero_add]
          exact mul_div_mul_right _ _ hw)
    refine exists_const_logDeriv (l := l) W_ne hT (fun z ↦ div_ne_zero (σ_ne _) (σ_ne _))
      h_an.differentiableAt fun x y ↦ ?_
    dsimp only [W]
    rw [add_assoc l x y, add_sub_assoc l x y, map_add e l x, hL l hl, zero_add]
    have := σ_ne x; have := σ_ne (x + y); have := σ_ne (x - y)
    have := σ_ne (l + (x + y)); have := σ_ne (l + (x - y))
    field_simp
  obtain ⟨B, σ_add, hB_symm⟩ := exists_factor_of_automorphy (L := L) σ_ne h_log
  have σ_double_mem (l : V) (hl : l ∈ L) : σ (l + l) = σ l ^ 4 * exp (q l l) := by
    rw [σ_double, hL l hl, C_zero, mul_one]
  exact ⟨σ, B, σ_ne, σ_an, σ_add, isAppellHumbert_of_double_eq σ_ne σ_double_mem σ_add hB_symm⟩

/-- The existence half of the Appell–Humbert theorem. Let e : V → A(ℂ) be a uniformisation with
kernel L, and N a linear system that embeds A, whose class satisfies the parallelogram law
`New.Pic.ParallelogramLaw`. Then there are Appell–Humbert data (L, B, χ) with positive Riemann form
and theta functions θ_i of type (B, χ) such that θ(z) is a vector of homogeneous coordinates of e(z)
for N, for all z in V. -/
lemma New.Uniformisation.appell_humbert {A : Over (AlgebraicGeometry.Spec (CommRingCat.of ℂ))}
    [AddObj A] {ι V : Type} [Finite ι] [FinComplexSpace V] (u : Uniformisation (O := ℂ) A V)
    {N : LineBundle A.left ι} (hN : IsProjEmbedding (ι := ι) N A.hom)
    (h_par : N.picClass.ParallelogramLaw) :
    ∃ (B : ThetaTori.LatticeForm u.lattice) (χ : V → ℂ) (θ : V → ι → ℂ),
      HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ ∧ IsPosRiemann B := by
  -- The parallelogram law trivialises a bundle `X` on `A × A`, with values `C`. From it we build
  -- a trivialisation `σ` of the pullback of `N` to `V` whose factor of automorphy is given by
  -- Appell–Humbert data, and let `θ z` be `σ z` times the homogeneous coordinates of `e z` in the
  -- chart `J (e z)`. Positivity of the Riemann form follows for any theta coordinates.
  suffices h_coords : ∃ (B : ThetaTori.LatticeForm u.lattice) (χ : V → ℂ) (θ : V → ι → ℂ),
      HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ by
    obtain ⟨B, χ, θ, h_theta⟩ := h_coords
    exact ⟨B, χ, θ, h_theta, u.isPosRiemann_of_hasThetaCoords hN h_theta⟩
  obtain ⟨e, L, -, hL, h_imm, -⟩ := u
  dsimp at h_imm ⊢
  replace hL : ∀ l ∈ L, e l = 0 := fun l ↦ (hL l).1
  have h_hol (z : V) : HolomorphicAt (fun x : V ↦ (e x).1) z := (h_imm z).1
  -- `X = (p^* N ⊗ s^* N)² ⊗ ((p + s)^* N ⊗ (p - s)^* N)⁻¹` for the two projections `p`, `s`; by the
  -- parallelogram law it has a frame `w`, a section without zero.
  let p := fst A A
  let s := snd A A
  let X := (((N.pull p.1).mul (N.pull s.1)).pow 2).mul
    ((N.pull (p + s).1).mul (N.pull (p - s).1)).inv
  let ⟨w, (hw : X.IsFrame w)⟩ := picClass_eq_iff.1 (by simpa using! (h_par p s).symm)
  -- A chart `J x` of `N` at each point; `Φ x y` changes from the chart at `y` to the chart at `x`.
  have h_cover (x : ComplexPoint A) : ∃ i : ι, LandsIn x.1 (N.opens i) := N.exists_landsIn x.1
  choose J hJ using h_cover
  have h_lifts {x : ComplexPoint A} :
      N.IsHomogeneousCoords x.1 fun j ↦ N.transition (J x) j (.of ℂ) x.1 :=
    hN.isLinearSystem.isHomogeneousCoords_transition (hJ x)
  have hp_comp (x y : ComplexPoint A) : (lift x y).1 ≫ p.1 = x.1 := by rw [← comp_left, lift_fst]
  have hs_comp (x y : ComplexPoint A) : (lift x y).1 ≫ s.1 = y.1 := by rw [← comp_left, lift_snd]
  have hadd_comp (x y : ComplexPoint A) : (lift x y).1 ≫ (p + s).1 = (x + y).1 := by
    rw [← comp_left, AddMonObj.comp_add, lift_fst, lift_snd]
  have hsub_comp (x y : ComplexPoint A) : (lift x y).1 ≫ (p - s).1 = (x - y).1 := by
    rw [← comp_left, AddGrpObj.comp_sub, lift_fst, lift_snd]
  have h_in {x y : ComplexPoint A} :
      LandsIn (lift x y).1 (X.opens (fun _ ↦ (J x, J y), J (x + y), J (x - y))) :=
    landsIn_inf.2 ⟨(landsIn_iInf _).2 fun _ ↦ landsIn_inf.2
      ⟨landsIn_preimage.2 (hp_comp x y ▸ hJ x), landsIn_preimage.2 (hs_comp x y ▸ hJ y)⟩,
      landsIn_inf.2 ⟨landsIn_preimage.2 (hadd_comp x y ▸ hJ (x + y)),
        landsIn_preimage.2 (hsub_comp x y ▸ hJ (x - y))⟩⟩
  let Φ (x y : ComplexPoint A) : ℂ := N.transition (J y) (J x) (.of ℂ) y.1
  have Φ_self (x : ComplexPoint A) : Φ x x = 1 := N.transition_self _ _ _ (hJ _)
  have Φ_ne (z : V) : ∀ᶠ w : V in nhds z, Φ (e z) (e w) ≠ 0 :=
    (h_hol z (isRegularOn_ofSection 0) (hJ _)).1.mono (by simp [Φ, h_lifts _])
  have h_coord (j : ι) (z : V) :
      AnalyticAt ℂ (fun w : V ↦ N.transition (J (e w)) j (.of ℂ) (e w).1 / Φ (e z) (e w)) z :=
    (h_hol z (hN.isLinearSystem.isRegularOn_transition ..) (hJ _)).2.congr
      ((Φ_ne z).mono fun _ h ↦ ((h_lifts _).2 j h.isUnit).trans
        (by dsimp only [Φ]; rw [Ring.inverse_eq_inv', div_eq_mul_inv]))
  -- `C x y` is the value of the frame at `(x, y)`; in the fixed charts at `(a, b)` it is analytic.
  choose C hC using fun x y : ComplexPoint A ↦ hw.2 _ _ _ (h_in (x := x) (y := y))
  have h_inv {u v : ComplexPoint A} (hv : LandsIn v.1 (N.opens (J u))) :
      N.transition (J u) (J v) (.of ℂ) v.1 = (Φ u v)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      ((N.transition_trans (J v) (J u) (J v) (.of ℂ) v.1 (hJ v) hv (hJ v)).trans
        (N.transition_self (J v) (.of ℂ) v.1 (hJ v)))
  have C_an (a b : V) : AnalyticAt ℂ (fun (x, y) ↦
      C (e x) (e y) / C 0 0 * Φ (e (a - b)) (e (x - y)) * Φ (e (a + b)) (e (x + y)) /
        (Φ (e a) (e x) * Φ (e b) (e y)) ^ 2) (a, b) := by
    have h_pair : HolomorphicAt (fun u : V × V ↦ (lift (e u.1) (e u.2)).1) (a, b) :=
      ((h_hol _).comp analyticAt_fst).lift hN ((h_hol _).comp analyticAt_snd)
    obtain ⟨h_near, h_an⟩ := h_pair (hw.1.1 _) h_in
    refine (h_an.div_const (c := C 0 0)).congr (h_near.mono fun z hz ↦ ?_)
    refine (congrArg (· / (C 0 0 : ℂ)) (hw.1.2 _ _ _ _ hz h_in)).trans ?_
    -- the change of charts for `X` is the stated quotient of the changes of charts `Φ` for `N`
    have hz1 : LandsIn (e z.1).1 (N.opens (J (e a))) :=
      hp_comp _ _ ▸ landsIn_preimage.1 (landsIn_inf.1 ((landsIn_iInf _).1 (landsIn_inf.1 hz).1 0)).1
    have hz2 : LandsIn (e z.2).1 (N.opens (J (e b))) :=
      hs_comp _ _ ▸ landsIn_preimage.1 (landsIn_inf.1 ((landsIn_iInf _).1 (landsIn_inf.1 hz).1 0)).2
    simp only [X, mul_transition, pow, pi_transition, Fin.prod_univ_two]
    change (((N.transition (J (e a)) (J (e z.1)) (.of ℂ) ((lift (e z.1) (e z.2)).1 ≫ p.1) *
        N.transition (J (e b)) (J (e z.2)) (.of ℂ) ((lift (e z.1) (e z.2)).1 ≫ s.1)) *
        (N.transition (J (e a)) (J (e z.1)) (.of ℂ) ((lift (e z.1) (e z.2)).1 ≫ p.1) *
        N.transition (J (e b)) (J (e z.2)) (.of ℂ) ((lift (e z.1) (e z.2)).1 ≫ s.1)) *
        (N.transition (J (e z.1 + e z.2)) (J (e a + e b)) (.of ℂ)
          ((lift (e z.1) (e z.2)).1 ≫ (p + s).1) *
        N.transition (J (e z.1 - e z.2)) (J (e a - e b)) (.of ℂ)
          ((lift (e z.1) (e z.2)).1 ≫ (p - s).1))) *
        w (fun _ ↦ (J (e z.1), J (e z.2)), J (e z.1 + e z.2), J (e z.1 - e z.2)) (.of ℂ)
          (lift (e z.1) (e z.2)).1) / C 0 0 = _
    rw [hp_comp, hs_comp, hadd_comp, hsub_comp, h_inv hz1, h_inv hz2, ← hC]
    change (((Φ (e a) (e z.1))⁻¹ * (Φ (e b) (e z.2))⁻¹) *
        ((Φ (e a) (e z.1))⁻¹ * (Φ (e b) (e z.2))⁻¹) *
        (Φ (e a + e b) (e z.1 + e z.2) * Φ (e a - e b) (e z.1 - e z.2)) *
        (C (e z.1) (e z.2) : ℂ)) / C 0 0 = _
    rw [← map_add e a b, ← map_add e z.1 z.2, ← map_sub e a b, ← map_sub e z.1 z.2]
    simp only [div_eq_mul_inv]
    ring
  -- This gives a trivialisation `σ` whose factor of automorphy comes from Appell–Humbert data.
  obtain ⟨σ, B, σ_ne, σ_an, σ_add, h_data⟩ :=
    exists_isAppellHumbert_of_analyticAt (C := fun x y ↦ C x y / C 0 0) hL Φ_self Φ_ne
      (h_coord (J (e 0))) (div_self (C 0 0).ne_zero)
      (fun x y ↦ div_ne_zero (C x y).ne_zero (C 0 0).ne_zero) C_an
  let χ (l : V) : ℂ := σ l / σ 0 / exp (B l l / 2)
  let θ (z : V) : ι → ℂ := σ z • fun j ↦ N.transition (J (e z)) j (.of ℂ) (e z).1
  have θ_mem (j : ι) : (θ · j) ∈ RealComplexForm.thetaSpace (L := L) χ B := by
    refine ⟨fun z ↦
        (((σ_an z).mul (h_coord j z)).congr ((Φ_ne z).mono fun w hw ↦ ?_)).differentiableAt,
      fun l hl z ↦ ?_⟩
    · dsimp only [θ, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_div_assoc', mul_right_comm, mul_div_cancel_right₀ _ hw]
    · dsimp only [θ, χ, Pi.smul_apply, smul_eq_mul]
      rw [σ_add l hl z, map_add e z l, hL l hl, add_zero, exp_add, mul_comm (exp (B l z)),
        ← mul_assoc (σ l / σ 0 / _), div_mul_cancel₀ _ (exp_ne_zero (B l l / 2))]
      ring
  exact ⟨B, χ, θ, hN.isLinearSystem, h_data, θ_mem, fun z ↦ h_lifts.smul (σ_ne z).isUnit⟩
end
end

/-!
# Objects modelled on complex tori and their homomorphisms as rational matrices

This file models the objects of a PEL family `X` (`New.ThetaFamily`) over a valuation ring with
fraction field ℂ on complex tori `V` modulo a lattice given by a polarised period map. It then
describes homomorphisms of modelled objects by matrices `z ∈ GL_n(E)`.

## Main definitions and results

* `New.ThetaObject.TorusModel`: `y.groupScheme` is uniformised by `V` modulo that lattice, with
  theta coordinates.
* `New.ThetaTori.PeriodMap.exists_uniformisation_of_isSeparatingFamily`: a dense map given by theta
  functions is a uniformisation.
* `New.ThetaObject.TorusModel.fullStructure`: a model trivialises all torsion, compatibly with the
  Weil pairing. `New.ThetaObject.TorusModel.exists_unit_on_roots_of_unity` supplies the unit of Ẑ
  through which a ring homomorphism `O → ℂ` acts on roots of unity.
* `New.ThetaObject.TorusModel.exists_isTranslationLift_of_dualLattice` (with its parts
  `New.ThetaObject.TorusModel.card_nsmul_mem_of_mem_dualLattice` and
  `New.ThetaObject.TorusModel.exists_isTranslationLift_of_mem_dualLattice`),
  `New.ThetaObject.TorusModel.multiplier_eq_canonicalMultiplier`: translations by the dual lattice
  lift to `y.lineBundle`, and the multiplier of the theta coordinates is the canonical one.
* `New.ThetaObject.TorusModel.exists_matrix_of_hom`: a linear `ψ` of multiplier `μ ≠ 0` comes from a
  `z`.
* `New.ThetaObject.TorusModel.exists_isIsogenyOfMatrix`,
  `New.ThetaObject.TorusModel.exists_isogeny`: a `z` with `z ℓ z⁻¹ = ℓ'` and `g'⁻¹ z g` an integral
  similitude of multiplier `μ` gives an isogeny (`New.ThetaObject.TorusModel.IsIsogenyOfMatrix`);
  objects with models have the same map from `𝓞 E`
  (`New.ThetaObject.TorusModel.baseHom_eq_baseHom`).

Notions from other files:
* `New.ThetaTori.PeriodMap`: the linear part of a model: a real isomorphism Q from (E ⊗ ℝ)ⁿ onto V,
  a form β with frame g, and a form B on V whose Riemann form pulls back to
  `New.Variety.polarisationForm`.
* `New.Variety.frameCoords`: the map y ↦ g⁻¹y from Eⁿ to n-tuples of finite adeles.
* `New.Variety.realVecAction`: the action of a matrix A over E on (E ⊗ ℝ)ⁿ, through Φ_v(A) at the
  infinite place v.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` and `Lib.Shimura.ThetaModuli.UniversalFamily`
for sources.
-/

@[expose] public section

/-!
## Theta uniformisation, Weil pairing and canonical multiplier

Complex tori as models of the objects of a PEL family `X` (`New.ThetaFamily`). An object `y` over a
valuation ring `O` with fraction field ℂ (`New.ValuativeArc`) is an `O`-point of the base of `X`. It
carries an abelian scheme `y.groupScheme`, a linear system `y.lineBundle` and level points
`y.levelPoints`. A polarised period map (`New.ThetaTori.PeriodMap`) is an isomorphism
`Q : (E ⊗ ℝ)ⁿ ≃ V` with a form `B`. Its lattice consists of the `Q (toRealVectors z)` for `z ∈ Eⁿ`
with `g⁻¹ z` integral.
-/

namespace New

open CategoryTheory Complex LinearMap Submodule NumberField LineBundle Variety ThetaTori Set
  AlgebraicGeometry Polynomial AddChar IsIntegrallyClosed

variable {E : Type} [Field E] [CMBase E]
  {D : PEL E} {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {O : Type} [CommRing O] [ValuativeArc O] (y : ThetaObject X (Spec ⟨O⟩))
  {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} {V : Type} [FinComplexSpace V]
  (Y : PeriodMap D g ℓ V)

/-- The object `y` is modelled on the torus of the polarised period map `Y` onto `V`. The model is a
uniformisation of `y.groupScheme` by `V`. It is compatible with the action of `𝓞 E` and the level
points. Its kernel is the period lattice. Along it, `y.lineBundle` has theta coordinates. -/
structure ThetaObject.TorusModel where
  /-- The map `𝓞 E → O → ℂ` is the embedding `Φ v₀`. -/
  baseHom_eq (c : 𝓞 E) : algebraMap O ℂ (y.baseHom c) = Φ v₀ c.val
  /-- The uniformisation of `y.groupScheme` by `V`. -/
  uniformisation : Uniformisation y.groupScheme V
  /-- The multiplier of the theta coordinates. -/
  χ : V → ℂ
  /-- The theta coordinates, indexed by `D.dualTorsion`. -/
  θ : V → D.dualTorsion → ℂ
  /-- Along the uniformisation, `θ` are coordinates of `y.lineBundle` and theta functions of type
  `(B, χ)`. -/
  hasThetaCoords :
      HasThetaCoords uniformisation.lattice (atGeneric uniformisation.expMap) y.lineBundle
        Y.automorphyForm χ θ
  /-- The composite of `Q` and the uniformisation commutes with the action of `𝓞 E`. -/
  equivariant (c : 𝓞 E) (w : RealVectors E D.Index) :
      uniformisation.expMap (Y.realEquiv (cmEmbedding c.val • w)) = c • uniformisation.expMap
        (Y.realEquiv w)
  /-- The level points are the images of the chosen rational vectors. -/
  level_eq (l : D.levelTorsion) : y.levelPoints l = uniformisation.expMap (Y.torsionLift l)
  /-- The kernel of the uniformisation is the period lattice. -/
  lattice_eq : uniformisation.lattice = Y.periodLattice

/-- Let `A` be an abelian scheme over `ℂ` embedded in projective space by `N`, and let
`e : V → A(ℂ)` be additive with image dense in the reduced scheme `A`, killing `Y.periodLattice`,
along which `N` has theta coordinates `Y.thetaCoord` of type `(Y.automorphyForm, Y.multiplier)`. Let
`u` be a uniformisation of `A` by `W` along which `N` has theta coordinates of type `(B', χ')`, and
let `F : V → W` be complex linear with `u.expMap ∘ F = e`, pulling the Riemann form of `B'` back to
that of `Y.automorphyForm`. If a line bundle `M` has theta coordinates of type `(B', χ)` along `u`
and `χ ∘ F = Y.multiplier` on `Y.periodLattice`, then `χ = χ'` on `u.lattice`. -/
lemma ThetaTori.PeriodMap.multiplier_eq_of_pullback {A : Over (Spec (CommRingCat.of ℂ))} {W : Type}
    {N M : LineBundle A.left D.dualTorsion} {χ χ' : W → ℂ} {θ θ' : W → D.dualTorsion → ℂ}
    [IsAbelianScheme A] [FinComplexSpace W] (hN : IsProjEmbedding N A.hom)
    {e : V →+ ComplexPoint A} (h_sep : IsSeparatingFamily (atGeneric e))
    (hY : HasThetaCoords Y.periodLattice (atGeneric e) N Y.automorphyForm Y.multiplier
      (flip Y.thetaCoord))
    (h_kill : ∀ l ∈ Y.periodLattice, e l = 0)
    {u : Uniformisation A W} {B' : LatticeForm u.lattice}
    (hu : HasThetaCoords u.lattice (atGeneric u.expMap) N B' χ' θ')
    {F : V →L[ℂ] W} (hF : ∀ z : V, u.expMap (F z) = e z)
    (h_riem : RealComplexForm.riemannForm (B'.pullForm F) = Y.automorphyForm.riemannForm)
    (hM : HasThetaCoords (ι := D.dualTorsion) u.lattice (atGeneric u.expMap) M B' χ θ)
    (hχ : ∀ l ∈ Y.periodLattice, χ (F l) = Y.multiplier l) (l : W) (hl : l ∈ u.lattice) :
    χ l = χ' l := by
  -- The coordinates of `M`, pulled back by `F` and normalised, are sections of `N`; together they
  -- form a section of `N ⊗ M⁻¹`, which is a theta function `G` of type `(0, χ' / χ)` along `u`.
  -- Such a `G` is constant on lines through `0` and `G 0 ≠ 0`; so `χ' / χ` is `1` on `u.lattice`.
  have h_lifts (z : V) : N.IsHomogeneousCoords (e z).left fun i : D.dualTorsion ↦
    Y.thetaCoord i z :=
    hY.hasFieldCoords z
  have h_pull {M : LineBundle A.left D.dualTorsion} {χ : W → ℂ} {θ : W → D.dualTorsion → ℂ}
      (hM : HasThetaCoords (ι := D.dualTorsion) u.lattice (atGeneric u.expMap) M B' χ θ) :
      HasThetaCoords Y.periodLattice (fun z : V ↦ (e z).left) M (B'.pullForm F) (χ ∘ F)
        (θ ∘ F) := by
    -- `atGeneric_eq`, `comp_id` and `pull_id` are rewritten: the kernel is slow to unfold them.
    have h := hM.pull F (f := 𝟙 _) (e' := fun z ↦ (e z).left) (fun z ↦ by
      rw [Category.comp_id, atGeneric_eq]; exact congrArg Over.Hom.left (hF z))
      fun l hl ↦ by rw [u.eq_zero_iff, hF, h_kill l hl]
    rwa [LineBundle.pull_id] at h
  -- Evaluation along `e` sends sections of `N` to functions on `V`, and the coordinates to
  -- `Y.thetaCoord`.
  obtain ⟨ev, h_ev, h_ev_coord, -⟩ := exists_theta_evaluation hY
  -- The range of `ev` contains the translates of `Y.thetaCoord 0` by the dual lattice
  -- (`Y.thetaShift_thetaCoord`), so by irreducibility it contains every theta function of type
  -- `(Y.automorphyForm, Y.multiplier)`.
  have h_range : Y.automorphyForm.thetaSpace Y.multiplier ≤ ev.range := by
    refine Y.isAppellHumbert_periodLattice.thetaSpace_le_of_thetaShift_mem
      (Y.thetaCoord_mem_thetaSpace 0) (Y.thetaCoord_ne_zero 0) ev.range ?_
    rw [Y.dualLattice_periodLattice]
    rintro _ ⟨w, hw, rfl⟩
    change Y.automorphyForm.thetaShift (Y.periodPoint w) (Y.thetaCoord 0) ∈ ev.range
    rw [Y.thetaShift_thetaCoord (s := ⟨_, hw⟩) rfl 0]
    exact ev.range.smul_mem _ ⟨_, h_ev_coord _⟩
  -- The normalised pull-backs of the coordinates of `M` are such theta functions, so they come
  -- from sections `σ a` of `N`.
  let q (z : V) : ℂ := exp ((Y.automorphyForm z z - B'.pullForm F z z) / 2)
  have h_mem_range (a : D.dualTorsion) : (fun z : V ↦ q z * (θ ∘ F) z a) ∈ ev.range :=
    h_range <| (h_pull hM).isAppellHumbert.exp_mul_mem_thetaSpace Y.isAppellHumbert_periodLattice
      h_riem
      hχ ((h_pull hM).mem_thetaSpace a)
  choose σ hσ using h_mem_range
  have hσ_val (a i : D.dualTorsion) (z : V) (hz : Y.thetaCoord i z ≠ 0) :
      (σ a).val i (CommRingCat.of ℂ) (e z).left = q z * θ (F z) a / Y.thetaCoord i z :=
    (h_ev (σ a) _).mp (hσ a) i z hz
  -- By density of the points `e z`, the `σ a` transform in `a` by the cocycle of `M`; so they
  -- glue to a section of `N ⊗ M⁻¹`, given on `u` by a theta function `G` of type `(0, χ' / χ)`.
  have h_reg (p : D.dualTorsion × D.dualTorsion) :
    PointFn.IsRegularOn ((σ p.2).val p.1) ((N.mul M.inv).opens p) :=
    -- The components of a section are regular on their charts.
    ((σ p.2).prop.left.left p.1).mono inf_le_left
  have h_sec : (N.mul M.inv).IsSection fun p : D.dualTorsion × D.dualTorsion ↦ (σ p.2).val p.1 := by
    refine ⟨h_reg, fun p p' R x hp hp' ↦ h_sep.pointFn_ext ((h_reg p).mono (by order))
      (.mul (regular ..) (h_reg p')) ?_ R x (landsIn_inf.mpr ⟨landsIn_inf.mpr ⟨hp, hp'⟩, hp'⟩)⟩
    -- At the points `e z` both sides are computed from `hσ_val` and the coordinates of `N`, `M`.
    simp +contextual [h_lifts .., hσ_val, (h_pull hM).hasFieldCoords .., field]
  obtain ⟨G, hG, hG_val⟩ := hu.exists_theta_of_isSection hM h_sec (hu.holomorphicAt hN)
    fun l hl z p ↦ by rw [u.atGeneric_add_of_mem l hl z]
  -- `G` has no zero on the image of `F`: where `Y.thetaCoord i z` and `θ (F z) a` are nonzero, the
  -- value of `σ a` is nonzero by `hσ_val` and a multiple of `G (F z)` by `hG_val`.
  have hG_ne (z : V) : G (F z) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i : D.dualTorsion, Y.thetaCoord i z ≠ 0 := (h_lifts z).exists_ne_zero
    obtain ⟨a, ha⟩ : ∃ i : D.dualTorsion, (θ ∘ F) z i ≠ 0 :=
      ((h_pull hM).hasFieldCoords z).exists_ne_zero
    -- Both systems of coordinates are units exactly on the same chart `i`.
    have hi' : θ' (F z) i ≠ 0 := by
      obtain ⟨h_lands_iff, -⟩ := h_lifts z i
      obtain ⟨h_lands_iff', -⟩ := (h_pull hu).hasFieldCoords z i
      exact (h_lands_iff'.mp (h_lands_iff.mpr hi.isUnit)).ne_zero
    intro h_zero
    apply ha
    simpa [h_zero, hσ_val, hF, hi, q] using hG_val i a (F z) hi'
  -- The form `B' - B'` of `G` is zero, so `G` is constant on lines through `0`; its functional
  -- equation at `0` then forces the multiplier `χ' l / χ l` to be `1`.
  have hG_const : G l = G 0 := by
    simpa using
      (hu.isAppellHumbert.add hM.isAppellHumbert.neg).apply_smul_of_nonpos hG l (by simp) 1
  have hG_zero : G 0 ≠ 0 := by simpa using hG_ne 0
  obtain ⟨-, hG_shift⟩ : Differentiable ℂ G ∧ ∀ l ∈ u.lattice, ∀ z : W,
      G (z + l) = (χ' * χ⁻¹) l * Complex.exp ((B' + -B') l z + (B' + -B') l l / 2) * G z := hG
  simpa [hG_const, hG_zero, hM.isAppellHumbert.ne_zero hl, field, eq_comm] using hG_shift l hl 0

/-- Let `A` be an abelian scheme over `ℂ`, smooth of relative dimension `d`, embedded in projective
space by `N` whose class satisfies the parallelogram law. Let the homomorphism `e : V → A(ℂ)` have
dense image in `A` (with `A` reduced), kill `Y.periodLattice` and carry `Y.thetaCoord` as
homogeneous coordinates. Then there is a uniformisation `u` of `A` by `V` with (a) theta coordinates
`Y.thetaCoord` of type `(Y.automorphyForm, Y.multiplier)`, (b) map `e` and kernel `Y.periodLattice`;
and (c) `d = New.Variety.abelianDim E D.Index`, which is `|D.Index|` times the number of infinite
places of `E`. -/
lemma ThetaTori.PeriodMap.exists_uniformisation_of_isSeparatingFamily
    {A : Over (Spec (CommRingCat.of ℂ))}
    {N : LineBundle A.left D.dualTorsion} [IsAbelianScheme A] (d : ℕ)
    (h_smooth : SmoothOfRelativeDimension d A.hom) (hN : IsProjEmbedding N A.hom)
    (h_par : N.picClass.ParallelogramLaw)
    (e : V →+ ComplexPoint A) (h_sep : IsSeparatingFamily (atGeneric e))
    (h_lifts : ∀ z : V, N.IsHomogeneousCoords (e z).left fun i : D.dualTorsion ↦ Y.thetaCoord i z)
    (h_kill : ∀ l ∈ Y.periodLattice, e l = 0) :
    ∃ u : Uniformisation A V,
      HasThetaCoords u.lattice (atGeneric u.expMap) N Y.automorphyForm Y.multiplier
        (flip Y.thetaCoord) ∧
      u.expMap = e ∧
      u.lattice = Y.periodLattice ∧
      d = abelianDim E D.Index := by
  -- Take any uniformisation `u` of `A`, with theta coordinates of type `(B', χ')`, and the linear
  -- lift `F` of `e`. It pulls the Riemann form of `B'` back to that of `Y.automorphyForm`. The main
  -- step shows that a vector dual to `F Y.periodLattice` is dual to all of `u.lattice`; it follows
  -- that `F` is bijective and that `Y.periodLattice` is the kernel of `e = u.expMap ∘ F`, so `e` is
  -- itself a uniformisation.
  obtain ⟨u⟩ : Nonempty (Uniformisation A (Fin d → ℂ)) := hN.nonempty_uniformisation h_smooth
  have hY : HasThetaCoords Y.periodLattice (atGeneric e) N Y.automorphyForm Y.multiplier
    (flip Y.thetaCoord) :=
    .mk hN.isLinearSystem Y.isAppellHumbert_periodLattice Y.thetaCoord_mem_thetaSpace h_lifts
  obtain ⟨B', χ', θ', hu, h_pos⟩ := u.appell_humbert hN h_par
  obtain ⟨F, hF⟩ := u.universal e (hY.holomorphicAt hN 0)
  -- Along `e`, `N` now has two systems of theta coordinates; so their Riemann forms agree
  -- (`h_riem`), and so do their multipliers on `Y.periodLattice` (`hχ'`).
  have hF_mem : ∀ l ∈ Y.periodLattice, F l ∈ u.lattice := fun l hl ↦ by
    rw [u.eq_zero_iff, hF, h_kill l hl]
  have h_pull :
      HasThetaCoords Y.periodLattice (atGeneric e) N (B'.pullForm F) (χ' ∘ F) (θ' ∘ F) := by
    -- `atGeneric_eq`, `comp_id` and `pull_id` are rewritten: the kernel is slow to unfold them.
    have h := hu.pull F (f := 𝟙 _) (e' := atGeneric e) (fun z ↦ by
      rw [Category.comp_id, atGeneric_eq, atGeneric_eq]; exact congrArg Over.Hom.left (hF z)) hF_mem
    rwa [LineBundle.pull_id] at h
  -- `N ⊗ N⁻¹` has a frame, as the class of `N` is equal to itself.
  obtain ⟨w, h_frame⟩ := picClass_eq_iff.mp (rfl : N.picClass = N.picClass)
  obtain ⟨h_riem, hχ', -⟩ := h_pull.riemannForm_eq_of_isFrame hY h_frame (hY.holomorphicAt hN)
    fun l hl ↦ atGeneric_add_of_map_eq_zero e (h_kill l hl)
  -- Main step: the translate of `N` by `u.expMap b` has multiplier `χ' l * B'.riemannPhase l b`, so
  -- by `multiplier_eq_of_pullback` a vector dual to `F Y.periodLattice` is dual to `u.lattice`.
  have h_dual (b : Fin d → ℂ) (hb : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) b = 1)
      (l : Fin d → ℂ) (hl : l ∈ u.lattice) : B'.riemannPhase l b = 1 := by
    have h := Y.multiplier_eq_of_pullback hN h_sep hY h_kill hu hF h_riem
      (hu.pull_translate (u.atGeneric_add b))
      (fun l' hl' ↦ by rw [hb l' hl', mul_one]; exact hχ' l' hl') l hl
    exact mul_left_cancel₀ (hu.isAppellHumbert.ne_zero hl) (h.trans (mul_one _).symm)
  -- `F` is bijective: with `T b = B'.riemannForm (F ·) b`, the map `T ∘ F` is bijective since the
  -- pulled-back form is nondegenerate, and `T` is injective: the real subspace `ker T` pairs
  -- integrally, hence trivially, with `u.lattice`, which spans, and `B'.riemannForm` is
  -- nondegenerate.
  let T : (Fin d → ℂ) →ₗ[ℝ] V →ₗ[ℝ] ℝ := (B'.riemannForm ∘ₗ F.toLinearMap.restrictScalars ℝ).flip
  have h_nondeg : (RealComplexForm.riemannForm (B'.pullForm F)).Nondegenerate := by
    simpa only [h_riem] using Y.isPosRiemann.nondegenerate (L := Y.periodLattice)
  have hTF : Function.Bijective (T ∘ F) := (BilinForm.toDual _ h_nondeg.flip).bijective
  have hT : Function.Injective T := by
    rw [← ker_eq_bot, eq_bot_iff, ← h_pos.nondegenerate.flip.ker_eq_bot]
    refine le_ker_iff_comp_subtype_eq_zero.mpr
      (flip_inj (ext_on (IsZLattice.span_top (L := u.lattice)) fun l hl ↦ ?_))
    refine eq_zero_of_forall_fourierChar_eq_one _ fun ⟨b, hb⟩ ↦ ?_
    have hb_dual : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) b = 1 := fun l _ ↦ by
      have h0 : B'.riemannForm (F l) b = 0 := LinearMap.congr_fun (mem_ker.mp hb) l
      rw [RealComplexForm.riemannPhase, h0, map_zero_eq_one]
      rfl
    exact h_dual b hb_dual l hl
  let F_equiv : V ≃ₗ[ℂ] (Fin d → ℂ) := .ofBijective F.toLinearMap (.of_comp_left hTF hT)
  have he : ⇑e = u.expMap ∘ F_equiv := (funext hF).symm
  -- If `e z = 0` then `F z ∈ u.lattice` pairs integrally with `F y` for `y` in the dual of
  -- `Y.periodLattice`; so `z` pairs integrally with that dual, and `z ∈ Y.periodLattice`.
  have h_ker (z : V) (hz : e z = 0) : z ∈ Y.periodLattice := by
    have hFz_mem : F z ∈ u.lattice := by rw [u.eq_zero_iff, hF, hz]
    refine Y.isPosRiemann.isDualFamily.mem_of_forall_eq_one z fun y ↦ ?_
    have h_dual_y : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) (F y) = 1 := fun l hl ↦ by
      simpa [← h_riem, riemannForm_pullForm] using (Y.isPosRiemann.isDualFamily.periodic y).2 l hl 0
    rw [← h_riem]
    exact h_dual (F y) h_dual_y (F z) hFz_mem
  -- Immersivity and the universal property pass from `u.expMap` to `e` along the isomorphism `F`.
  have h_imm (z v : V) (hv : IsFirstOrderConst (atGeneric e) z v) : v = 0 := by
    obtain ⟨h_hol, h_only_zero⟩ := u.immersive (F z)
    rw [he] at hv
    have h_Fv : IsFirstOrderConst (atGeneric u.expMap) (F z) (F v) :=
      (isJet_comp_iff F.hasFDerivAt h_hol).mp hv
    exact F_equiv.ker.le (h_only_zero (F v) h_Fv)
  refine ⟨{ expMap := e
            lattice := Y.periodLattice
            surjective := by simpa only [he] using u.surjective.comp F_equiv.surjective
            eq_zero_iff := fun z ↦ ⟨h_kill z, h_ker z⟩
            immersive := fun z ↦ ⟨hY.holomorphicAt hN z, h_imm z⟩
            universal := fun γ hγ ↦ ?_ }, hY, rfl, rfl,
    by simp [← finrank_eq_abelianDim Y.realEquiv, F_equiv.finrank_eq]⟩
  obtain ⟨F', hF'⟩ := u.universal γ hγ
  refine ⟨F_equiv.symm.toContinuousLinearEquiv ∘L F', fun w ↦ ?_⟩
  simp [he, hF']

end New

namespace New.ThetaObject.TorusModel

open CategoryTheory Complex LinearMap Submodule NumberField LineBundle Variety ThetaTori Set
  AlgebraicGeometry Polynomial AddChar IsIntegrallyClosed

variable {E : Type} [Field E] [CMBase E]
  {D : PEL E} {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {O : Type} [CommRing O] [ValuativeArc O] {y : ThetaObject X (Spec ⟨O⟩)}
  {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} {V : Type} [FinComplexSpace V]
  {Y : PeriodMap D g ℓ V} (m : y.TorusModel Y)

/-! ### The full structure of a model -/

/-- The map `π` of a model `m` sends (E ⊗ ℝ)ⁿ to the sections of `y.groupScheme` over `O`. It is the
period map `Q` followed by the uniformisation. -/
noncomputable def π (w : RealVectors E D.Index) :
    MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of O))) ⟶ y.groupScheme :=
  m.uniformisation.expMap (Y.realEquiv w)

/-- A ring homomorphism `φ : O → ℂ` acts on roots of unity through a unit of Ẑ. Here `ψf E` is the
standard additive character of the finite adeles of `E`, whose values are roots of unity. There is
a unit `ε` of Ẑ such that each value `ψf E t` is the image of some `c ∈ O` with
`φ c = ψf E (t ε)`. -/
lemma exists_unit_on_roots_of_unity (φ : O →+* ℂ) :
    ∃ ε : (Ô ℚ)ˣ, ∀ t : 𝔸f E, ∃ c : O,
      algebraMap O ℂ c = ψf E t ∧ φ c = ψf E (t * finAdeleIncl ℚ E ε) := by
  -- Roots of unity are integral, so they lie in `O`: `ζ z` is the preimage of `z`.
  have : IsIntegrallyClosed O := (ValuationRing.integers O ℂ).isIntegrallyClosed
  have h_lift (z : ℂ) (hz : IsOfFinOrder z) : ∃ c : O, algebraMap O ℂ c = z :=
    isIntegral_iff (R := O).mp
      ((IsPrimitiveRoot.orderOf z).isIntegral (orderOf_pos_iff.mpr hz)).tower_top
  choose! ζ hζ using h_lift
  -- The sets `C t` of pairs `(ε, ε')` with `φ (ζ (ψf E t)) = ψf E (t ε)` and
  -- `ψf E (t ε ε') = ψf E t` are closed; by compactness of `Ẑ × Ẑ` it is enough to treat finitely
  -- many `t` at a time.
  let ι : 𝔸f ℚ →+* 𝔸f E := finAdeleIncl ℚ E
  let C (t : 𝔸f E) : Set (𝔸f ℚ × 𝔸f ℚ) :=
    {p : 𝔸f ℚ × 𝔸f ℚ |
      φ (ζ (ψf E t)) = ψf E (t * ι p.fst) ∧ ψf E (t * ι (p.fst * p.snd)) = ψf E t}
  have hC_closed (t : 𝔸f E) : IsClosed (C t) := by
    apply (isClosed_eq _ (.subtypeVal _)).and (isClosed_eq ..) <;> fun_prop
  have h_fin (U : Finset (𝔸f E)) : ((Ô ℚ : Set _) ×ˢ (Ô ℚ : Set _) ∩ ⋂ t ∈ U, C t).Nonempty := by
    -- All `ψf E t`, `t ∈ U`, are `N`-th roots of unity.
    obtain ⟨N, hN, hU⟩ := exists_forall_mul_mem_Ô fun t : U ↦ (t : 𝔸f E)
    have hN_ne : NeZero N := ⟨hN⟩
    have h_inj : Function.Injective (algebraMap O ℂ) := IsFractionRing.injective O ℂ
    obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω N := ⟨_, isPrimitiveRoot_exp N hN⟩
    have hω_alg : algebraMap O ℂ (ζ ω) = ω := hζ ω (hω.isOfFinOrder hN)
    have hζω : IsPrimitiveRoot (ζ ω) N := .of_map_of_injective (by rwa [hω_alg]) h_inj
    -- `φ (ζ ω)` is a root of the cyclotomic polynomial, so it and `ω` are powers of each other.
    have hφω : IsPrimitiveRoot (φ (ζ ω)) N := by
      rw [← isRoot_cyclotomic_iff, ← map_cyclotomic N φ]
      exact (hζω.isRoot_cyclotomic hN.pos).map φ
    obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hφω.pow_eq_one
    obtain ⟨l, -, hl⟩ := hφω.eq_pow_of_pow_eq_one hω.pow_eq_one
    refine ⟨(k, l), by simp, Set.mem_biInter fun t ht ↦ ?_⟩
    have ht_alg : algebraMap O ℂ (ζ (ψf E t)) = ψf E t := hζ _ (isOfFinOrder_ψf t)
    have ht_pow : ζ (ψf E t) ^ N = 1 := by
      apply h_inj
      simp [ht_alg, ← Circle.coe_pow, ← map_nsmul_eq_pow, ψf_eq_one_of_mem (hU ⟨t, ht⟩)]
    -- So `ζ (ψf E t)` is a power of `ζ ω`: `φ` acts on it as the `k`-th power, undone by `l`.
    obtain ⟨a, -, ha⟩ := hζω.eq_pow_of_pow_eq_one ht_pow
    have h_pow : ω ^ a = ψf E t := by rw [← hω_alg, ← map_pow, ha, ht_alg]
    have h_act : φ (ζ (ψf E t)) = ψf E t ^ k := by
      rw [← ha, map_pow, ← hk, pow_right_comm, h_pow]
    have h_undo : ((ψf E t : ℂ) ^ k) ^ l = ψf E t := by
      rw [← h_pow, pow_right_comm ω a k, hk, pow_right_comm, hl]
    refine ⟨?_, Circle.ext ?_⟩
    · change φ (ζ (ψf E t)) = ψf E (t * ι (k : 𝔸f ℚ))
      rw [map_natCast, ← nsmul_eq_mul', map_nsmul_eq_pow, Circle.coe_pow, h_act]
    · change (ψf E (t * ι ((k : 𝔸f ℚ) * (l : 𝔸f ℚ))) : ℂ) = ψf E t
      rw [map_mul ι, map_natCast, map_natCast, ← mul_assoc, ← nsmul_eq_mul', ← nsmul_eq_mul',
        map_nsmul_eq_pow, map_nsmul_eq_pow, Circle.coe_pow, Circle.coe_pow, h_undo]
  obtain ⟨⟨ε, ε'⟩, ⟨hε, hε'⟩, h_mem⟩ :=
    (isCompact_Ô.prod isCompact_Ô).inter_iInter_nonempty C hC_closed h_fin
  rw [Set.mem_iInter] at h_mem
  -- `ψf` separates finite adeles, so `ε * ε' = 1`.
  have h_unit : ε * ε' = 1 :=
    adeleMap_injective (algebraMap _ E) (eq_of_forall_ψf_mul_eq fun t ↦ by
      simpa [ι] using (h_mem t).right)
  exact ⟨.mkOfMulEqOne ⟨ε, hε⟩ ⟨ε', hε'⟩ (Subtype.ext h_unit), fun t ↦
    ⟨ζ (ψf E t), hζ (ψf E t) (isOfFinOrder_ψf t), (h_mem t).left⟩⟩

/-- Two rational vectors `a`, `b` give the same point of `y.groupScheme` (the images of their
periods under the uniformisation of the model `m`) exactly when their torsion classes g⁻¹a and g⁻¹b
in (𝔸_f / Ô)ⁿ agree. -/
lemma expMap_periodPoint_eq_iff (a b : D.Index → E) :
    m.uniformisation.expMap (Y.periodPoint a) = m.uniformisation.expMap (Y.periodPoint b) ↔
      Variety.frameTorsionClass g a = Variety.frameTorsionClass g b := by
  simpa [← m.lattice_eq, sub_eq_zero] using Y.sub_mem_periodLattice_iff (y := a) (z := b)

/-- The full structure of a model: the class of g⁻¹a in (𝔸_f / Ô)ⁿ, for a in Eⁿ, is sent to the
torsion section `expMap (Q (toRealVectors a))`, computed at the chosen rational lift `ratLift g` of
the class. -/
noncomputable def fullStructure : y.FullLevelStructure where
  torsionPoint :=
    { toFun x := m.uniformisation.expMap (Y.periodPoint (ratLift g x))
      map_add' := by
        simp only [← map_add, m.expMap_periodPoint_eq_iff, frameTorsionClass_ratLift,
          map_add (frameTorsionClass g), implies_true]
      map_smul' := by
        simp only [RingHom.id_apply, ← equivariant, ← toRealVectors_smul,
          m.expMap_periodPoint_eq_iff, frameTorsionClass_ratLift, map_smul, implies_true] }
  injective _ := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, m.expMap_periodPoint_eq_iff,
      frameTorsionClass_ratLift, imp_self, implies_true]
  levelPoints_eq := m.level_eq
  weil_pairing ι := by
    -- The frame `g` scales the form by a unit `a`, and `ι` acts on roots of unity through `ε`.
    obtain ⟨a, ha⟩ := Y.isFrameFor
    obtain ⟨ε, hε⟩ := exists_unit_on_roots_of_unity (E := E) ι
    refine ⟨a * ε, fun k s t hs ht ↦ ?_⟩
    obtain ⟨c, hc, hιc⟩ := hε (finAdeleIncl ℚ E a * (k * xiForm D.ξ s t))
    refine ⟨c, by simpa only [Units.val_mul, Subring.coe_mul, map_mul, mul_right_comm] using hιc,
      fun Φ Ψ hΦ hΨ ↦ (lift_commutator_iff_weil_pairing _ m.hasThetaCoords hΦ hΨ).2 ?_⟩
    -- It remains to see that `c` is `Real.fourierChar` of `polarisationForm` at `s'` and `k • t'`,
    -- where `s'`, `t'` are rational lifts of the classes of `s` and `t`.
    -- `fourierChar_polarisationForm` rewrites this through `ψf`.
    set s' := ratLift g (torsionClass s) with hs'
    set t' := ratLift g (torsionClass t) with ht'
    have h_repr :
        ψf E (finAdeleIncl ℚ E a * xiForm D.ξ (frameCoords g s') (frameCoords g (k • t'))) =
          Real.fourierChar (polarisationForm D Y.formMatrix (toRealVectors s')
            (toRealVectors (k • t'))) :=
      (fourierChar_polarisationForm ha s' (k • t')).symm
    -- Up to the main term, the form pairs integral vectors, on which `ψf` is trivial
    -- (`D.mem_dualTorsion`).
    have h_form (ξ : E) (v : D.Index → E) (w : D.Index → 𝔸f E) :
        xiForm ξ (frameCoords g v) (k • w) =
          k * xiForm ξ s t + xiForm ξ (k • s) (w - t) + xiForm ξ (frameCoords g v - s) (k • w) := by
      -- Expand the form by bilinearity; the identity is then one of the commutative ring `𝔸f E`.
      simp only [xiForm, star_sub, star_smul, star_trivial, dotProduct_sub, sub_dotProduct,
        smul_dotProduct, dotProduct_smul]
      ring
    simpa only [hc, hs', ht', coe_fourierChar_eq_exp, map_nsmul, LinearMap.smul_apply,
      Y.riemannForm_eq, polarisationForm_toRealVectors, map_smul_of_tower, h_form, mul_add,
      map_add_eq_mul, hs, zero_mem, map_sub, ← frameTorsionClass_apply, frameTorsionClass_ratLift,
      sub_self, (D.mem_dualTorsion _).1, (ψf_unit_mul_eq_one_iff _).2, mul_one, ht,
      Circle.ext_iff] using h_repr

/-- `New.ThetaObject.TorusModel.fullStructure` sends the class of g⁻¹z to the section at the period
of z for every z in Eⁿ, not only for the chosen representative of the class. -/
lemma torsionPoint_frameTorsionClass (z : D.Index → E) :
    m.fullStructure.torsionPoint (Variety.frameTorsionClass g z) =
      m.uniformisation.expMap (Y.periodPoint z) := by
  change m.uniformisation.expMap (Y.periodPoint (ratLift g (Variety.frameTorsionClass g z))) = _
  rw [m.expMap_periodPoint_eq_iff, frameTorsionClass_ratLift]

/-! ### The dual lattice and the multiplier of a model -/

/-- The order of `D.dualTorsion` kills the lattice dual to `m.uniformisation.lattice` (for the
Riemann form) modulo `m.uniformisation.lattice`. -/
lemma card_nsmul_mem_of_mem_dualLattice :
    ∀ b ∈ Y.automorphyForm.dualLattice (L := m.uniformisation.lattice),
      Nat.card D.dualTorsion • b ∈ m.uniformisation.lattice := by
  -- The dual lattice consists of the periods of the vectors `w` whose class lies in
  -- `D.dualTorsion`.
  rw [m.lattice_eq, Y.dualLattice_periodLattice]
  exact fun b hb ↦ Y.card_nsmul_mem_periodLattice hb

/-- Let `S` be the `O`-span of the coordinates of `y.lineBundle` and `b` a vector of the lattice
dual to `m.uniformisation.lattice` for the Riemann form. Then the translation by the section
`m.uniformisation.expMap b` has a lift `Φ` to the sections of `y.lineBundle` with `Φ S ⊆ S`. -/
lemma exists_isTranslationLift_of_mem_dualLattice :
    ∀ b ∈ Y.automorphyForm.dualLattice (L := m.uniformisation.lattice), ∃ Φ :
      Module.End O ↥(y.lineBundle.H0 O),
      IsTranslationLift y.lineBundle (m.uniformisation.expMap b) Φ ∧
      span O (Set.range (coordSection y.isProjEmbedding.isLinearSystem)) ∈ Φ.invtSubmodule := by
  -- The dual lattice consists of the periods of the vectors `w` whose class lies in
  -- `D.dualTorsion`.
  rw [m.lattice_eq, Y.dualLattice_periodLattice]
  rintro _ ⟨w, hw, rfl⟩
  -- The theta structure lifts translation by the level point of that class; the lift permutes
  -- the coordinates up to scalars, the cocycle chosen inside the theta structure.
  obtain ⟨Φ, h_lift, h_coord⟩ := y.isThetaStructure.theta_law 1 ⟨frameTorsionClass g w, hw⟩
  have h_point :
      y.levelPoints (AddSubgroup.inclusion D.dualTorsion_le_levelTorsion
        ⟨frameTorsionClass g w, hw⟩) =
        m.uniformisation.expMap (Y.periodPoint w) :=
    (m.fullStructure.levelPoints_eq _).trans (m.torsionPoint_frameTorsionClass w)
  refine ⟨Φ, by simpa [← h_point] using h_lift, span_le.mpr ?_⟩
  simp [h_coord, range_subset_iff, smul_mem, mem_span_of_mem]

/-- Let `S` be the `O`-span of the coordinates of `y.lineBundle` and `b` a vector of the lattice
dual to `m.uniformisation.lattice` for the Riemann form. Then `|D.dualTorsion| • b` lies in
`m.uniformisation.lattice`, and the translation by the section `m.uniformisation.expMap b` has a
lift `Φ` to the sections of `y.lineBundle` with `Φ S ⊆ S`. -/
lemma exists_isTranslationLift_of_dualLattice :
    ∀ b ∈ Y.automorphyForm.dualLattice (L := m.uniformisation.lattice),
      Nat.card D.dualTorsion • b ∈ m.uniformisation.lattice ∧
      ∃ Φ : Module.End O ↥(y.lineBundle.H0 O),
        IsTranslationLift y.lineBundle (m.uniformisation.expMap b) Φ ∧
        span O (Set.range (coordSection y.isProjEmbedding.isLinearSystem)) ∈ Φ.invtSubmodule :=
  fun b hb ↦
    ⟨m.card_nsmul_mem_of_mem_dualLattice b hb, m.exists_isTranslationLift_of_mem_dualLattice b hb⟩

private lemma intAction_apply (Y : PeriodMap D g ℓ V) (c : 𝓞 E) (v : V) :
    Y.intAction c v = Y.realEquiv (cmEmbedding c.val • Y.realEquiv.symm v) :=
  rfl

private lemma intAction_realEquiv (Y : PeriodMap D g ℓ V) (c : 𝓞 E) (w : RealVectors E D.Index) :
    Y.intAction c (Y.realEquiv w) = Y.realEquiv (cmEmbedding c.val • w) := by
  rw [intAction_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- Let `m` model the object `y` on the torus of the polarised period map `Y`. On the period lattice
`m.uniformisation.lattice`, the multiplier `m.χ` of the theta coordinates is χ(l) = exp(πi·e(βl,
l)). Here e is the Riemann form of B = `Y.automorphyForm`, and β = `D.β` ∈ `𝓞 E` acts on V through
`Y.intAction`, the action of `𝓞 E` transported through the period map. -/
lemma multiplier_eq_canonicalMultiplier (l : V) (hl : l ∈ m.uniformisation.lattice) :
    m.χ l = canonicalMultiplier Y.automorphyForm (Y.intAction D.β) l := by
  -- The bundles `N ⊗ N ⊗ β^* N` and `(β + 1)^* N` are isomorphic (the class law `y.hasClassLaws.2`
  -- at the identity of `y.groupScheme`), so their multipliers agree: `χ(l)² χ(βl) = χ(l + βl)`. The
  -- cocycle rule expands the right side as `χ(l) χ(βl) exp(πi e(βl, l))`; cancel `χ(l) χ(βl)`.
  let F : 𝓞 E →+* V →L[ℂ] V := Y.intAction
  have hF (c : 𝓞 E) : ∀ l ∈ m.uniformisation.lattice, F c l ∈ m.uniformisation.lattice := by
    simpa [m.lattice_eq] using Y.intAction_mem_periodLattice c
  -- `F c` lifts the action of `c` on `y.groupScheme`, read at the generic point.
  have h_generic (c : 𝓞 E) (v : V) :
      atGeneric m.uniformisation.expMap (F c v) =
        atGeneric m.uniformisation.expMap v ≫ (c • 𝟙 y.groupScheme).left := by
    obtain ⟨w, rfl⟩ := Y.realEquiv.surjective v
    have h_eq : m.uniformisation.expMap (F c (Y.realEquiv w)) =
        m.uniformisation.expMap (Y.realEquiv w) ≫ (c • 𝟙 y.groupScheme) := by
      rw [intAction_realEquiv, m.equivariant, ModuleObj.comp_smul, Category.comp_id]
    rw [atGeneric, atGeneric, ← Over.comp_left, Category.assoc, h_eq]
  have h_pull (c : 𝓞 E) : HasThetaCoords m.uniformisation.lattice
    (atGeneric m.uniformisation.expMap)
      (y.lineBundle.pull (c • 𝟙 y.groupScheme).left) (Y.automorphyForm.pullForm (F c)) (m.χ ∘ F c)
        (m.θ ∘ F c) :=
    m.hasThetaCoords.pull (F c) (h_generic c) (hF c)
  have h_cls :
      ((y.lineBundle.mul y.lineBundle).mul
          (y.lineBundle.pull (D.β • 𝟙 y.groupScheme).left)).picClass =
        (y.lineBundle.pull ((D.β + 1) • 𝟙 y.groupScheme).left).picClass := by
    -- `using!`, because the class law is stated with `Pic.atPoint`, a pullback by definition,
    -- and unfolding it leaves the terms at `0` that `atPoint_zero` would remove.
    simpa [Pic.pairing, add_smul, eq_sub_iff_add_eq] using! y.hasClassLaws.2 0 (𝟙 _)
  -- Isomorphic bundles with theta coordinates have the same multiplier on the lattice.
  obtain ⟨-, h_mult_on_L, -⟩ :=
    ((m.hasThetaCoords.mul m.hasThetaCoords).mul (h_pull _)).riemannForm_eq_of_isFrame (h_pull _)
      (picClass_eq_iff.mp h_cls).choose_spec m.uniformisation.holomorphicAt
      m.uniformisation.atGeneric_add_of_mem
  have h_mult : m.χ l * m.χ l * m.χ (F D.β l) = m.χ (F (D.β + 1) l) := h_mult_on_L l hl
  have h_add : m.χ (F (D.β + 1) l) = m.χ l * m.χ (F D.β l) * canonicalMultiplier Y.automorphyForm
    (F D.β) l := by
    simpa [F, add_comm l, canonicalMultiplier] using
      m.hasThetaCoords.isAppellHumbert.semicharacter l hl _ (hF D.β l hl)
  have h_ne : m.χ l * m.χ (F D.β l) ≠ 0 :=
    mul_ne_zero (m.hasThetaCoords.isAppellHumbert.ne_zero hl)
      (m.hasThetaCoords.isAppellHumbert.ne_zero (hF D.β l hl))
  have h_eq :
      m.χ l * m.χ (F D.β l) * m.χ l =
        m.χ l * m.χ (F D.β l) * canonicalMultiplier Y.automorphyForm (F D.β) l := by
    rw [← h_add, ← h_mult]
    ring
  exact mul_left_cancel₀ h_ne h_eq

end New.ThetaObject.TorusModel

/-!
## Homomorphisms of modelled objects and rational matrices

Objects `x`, `x'` over a valuation ring `O` with fraction field `ℂ` are modelled on the tori of
`(g, ℓ)` and `(g', ℓ')`, with `g`, `g'` adelic frames and `ℓ`, `ℓ'` complex matrices.
-/

namespace New.ThetaObject.TorusModel

open CategoryTheory AlgebraicGeometry NumberField Matrix Category LineBundle ThetaTori Variety
  LinearMap Function

variable {E : Type} [Field E] [CMBase E]
  {V V' : Type} [FinComplexSpace V] [FinComplexSpace V']
  {D : PEL E} {g g' : GL D.Index (𝔸f E)} {ℓ ℓ' : Matrix D.Index D.Index ℂ} {Z : Scheme}
  {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {O : Type} [CommRing O] [ValuativeArc O]
  {x x' : ThetaObject X (Spec ⟨O⟩)} {Y : PeriodMap D g ℓ V} {Y' : PeriodMap D g' ℓ' V'}

/-- If `ψ` carries `m.π w` to `m'.π (z w)` for all `w`, then it carries the torsion point of the
class of `y` in (𝔸_f / Ô)ⁿ to the torsion point of the class of `g'⁻¹ z g y` (with `toFinGL z` the
image of `z` over 𝔸_f), for every finite adelic vector `y`. -/
lemma torsionPoint_comp (m : x.TorusModel Y) (m' : x'.TorusModel Y') {z : GL D.Index E}
    {ψ : x.groupScheme ⟶ x'.groupScheme}
    (h_periods : ∀ w : RealVectors E D.Index, m.π w ≫ ψ = m'.π (realVecAction z.val w))
    (y : D.Index → 𝔸f E) :
    m.fullStructure.torsionPoint (torsionClass y) ≫ ψ =
      m'.fullStructure.torsionPoint (torsionClass ((g'⁻¹ * toFinGL z * g).val *ᵥ y)) := by
  -- Both sides are locally constant in `y`, so the set of good `y` is closed; by `h_periods` it
  -- contains the dense range of `frameCoords g`.
  refine denseRange_frameCoords (g := g).induction_on y ⟨?_⟩ fun w ↦ ?_
  · exact IsLocallyConstant.comp₂ isOpen_preimage_torsionClass
      (.comp_continuous isOpen_preimage_torsionClass (by fun_prop))
      (fun t t' ↦ m.fullStructure.torsionPoint t ≫ ψ = m'.fullStructure.torsionPoint t') {p | ¬p}
  · simpa [← torsionPoint_frameTorsionClass, frameTorsionClass_apply, frameCoords,
      LinearMap.compLeft, comp_def, RingHom.map_mulVec, π] using h_periods (toRealVectors w)

/-- Let `x`, `x'` be objects over `O` with torus models `m`, `m'` on the polarised period maps `Y`
(frame `g`, matrix `ℓ`) and `Y'` (frame `g'`, matrix `ℓ'`), with period maps `m.π`, `m'.π` from
`(E ⊗ ℝ)ⁿ`. Let `ψ : x.groupScheme ⟶ x'.groupScheme` be an `𝓞 E`-linear homomorphism that pulls the
Picard class of `x'.lineBundle` back to `μ ≠ 0` times that of `x.lineBundle`. Then `ψ` comes from
some `z ∈ GL_n(E)`: (a) `m.π w ≫ ψ = m'.π (z·w)` for all `w`; (b) with `Y.formMatrix` the matrix of
the form β of `Y` (not the element `D.β` of `𝓞 E`), `μ` times the polarisation form of
`Y.formMatrix` is the polarisation form of `zᴴ Y'.formMatrix z`; (c) `z ℓ z⁻¹ = ℓ'` (conjugation
through `Φ v₀`). -/
lemma exists_matrix_of_hom (m : x.TorusModel Y) (m' : x'.TorusModel Y')
    (ψ : x.groupScheme ⟶ x'.groupScheme) [hψ : IsLinear ψ] {μ : ℕ} (hμ : μ ≠ 0)
    (hψ_cls : x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass) :
    ∃ z : GL D.Index E,
      -- (a) `ψ` acts on periods by `z`
      (∀ w : RealVectors E D.Index, m.π w ≫ ψ = m'.π (realVecAction z w)) ∧
      -- (b) `z` pulls the form of `Y'` back to `μ` times the form of `Y`
      (∀ y w : RealVectors E D.Index,
        μ * polarisationForm D Y.formMatrix y w = polarisationForm D (z.valᴴ * Y'.formMatrix * z) y
          w) ∧
      -- (c) `z` carries `ℓ` to `ℓ'`
      ratConj z ℓ = ℓ' := by
  -- `ψ` lifts to a complex linear map `F` of the universal covers. `F` keeps rational points and
  -- commutes with `𝓞 E`, so it is given by a matrix `z` over `E`; the theta data give the forms.
  obtain ⟨F, hF : ∀ w : V, m'.uniformisation.expMap (F w) = m.uniformisation.expMap w ≫ ψ⟩ :=
    m'.uniformisation.universal ((IsAddMonHom.addMonoidHom ψ _).comp _)
      ((m.uniformisation.immersive 0).1.comp_hom _)
  -- Isomorphic bundles with theta coordinates have the same Riemann form
  -- (`riemannForm_eq_of_isFrame`); here `x.lineBundle ^ μ` and `ψ^* x'.lineBundle`.
  have hF_mem : ∀ l ∈ m.uniformisation.lattice, F l ∈ m'.uniformisation.lattice := fun l hl ↦
    (m'.uniformisation.eq_zero_iff (F l)).mpr <| by
      rw [hF, (m.uniformisation.eq_zero_iff l).mp hl]
      exact (IsAddMonHom.addMonoidHom ψ _).map_zero
  have h_cls : (x.lineBundle.pow μ).picClass = (x'.lineBundle.pull ψ.left).picClass := by
    simp [← Pic.pull_picClass, hψ_cls]
  have h_generic (w : V) :
      atGeneric m'.uniformisation.expMap (F w) = atGeneric m.uniformisation.expMap w ≫ ψ.left := by
    rw [atGeneric, atGeneric, ← Over.comp_left, assoc, hF]
  obtain ⟨_, h_frame⟩ := picClass_eq_iff.mp h_cls
  obtain ⟨h_riem, -⟩ :
      RealComplexForm.riemannForm (μ • Y.automorphyForm) = RealComplexForm.riemannForm
        (Y'.automorphyForm.pullForm F) ∧ _ :=
    (m.hasThetaCoords.pow μ).riemannForm_eq_of_isFrame (m'.hasThetaCoords.pull F h_generic hF_mem)
      h_frame m.uniformisation.holomorphicAt m.uniformisation.atGeneric_add_of_mem
  -- A rational point maps to a torsion point of `x'`, which is again a rational point.
  have h_rat (y : D.Index → E) :
      ∃ y', toRealVectors y' = Y'.realEquiv.symm (F (Y.realEquiv (toRealVectors y))) := by
    obtain ⟨k, hk, hky⟩ := exists_nsmul_adelicTorsion_eq_zero (frameTorsionClass g y)
    have h_ker : k • F (Y.realEquiv (toRealVectors y)) ∈ Y'.periodLattice := by
      rw [← m'.lattice_eq, m'.uniformisation.eq_zero_iff, map_nsmul, hF, ← nsmul_comp]
      have hy0 : k • m.uniformisation.expMap (Y.realEquiv (toRealVectors y)) = 0 := by
        rw [← m.torsionPoint_frameTorsionClass y, ← map_nsmul, hky, map_zero]
      rw [hy0]
      exact (IsAddMonHom.addMonoidHom ψ _).map_zero
    obtain ⟨y', -, hy'⟩ := (Y'.nsmul_mem_latticeOver hk).mp h_ker
    exact ⟨y', Y'.realEquiv.eq_symm_apply.mpr hy'⟩
  choose f hf using h_rat
  have h_lin (c : 𝓞 E) (w : RealVectors E D.Index) :
      F (Y.realEquiv (cmEmbedding (algebraMap (𝓞 E) E c) • w)) =
        Y'.realEquiv (cmEmbedding (algebraMap (𝓞 E) E c) • Y'.realEquiv.symm
          (F (Y.realEquiv w))) := by
    have h_comp : F ∘L Y.intAction c = Y'.intAction c ∘L F :=
      m'.uniformisation.linear_ext fun v ↦ by
        obtain ⟨u, rfl⟩ := Y.realEquiv.surjective v
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, intAction_realEquiv,
          hF, m.equivariant, IsLinear.smul_comp, ← hF, intAction_apply, m'.equivariant,
          ContinuousLinearEquiv.apply_symm_apply]
    have h := DFunLike.congr_fun h_comp (Y.realEquiv w)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, intAction_realEquiv,
      intAction_apply] at h
    exact h
  -- `f` is `𝓞 E`-linear, hence `E`-linear; rational points are dense, so its matrix gives `F`.
  obtain ⟨z, hz⟩ : ∃ z : Matrix D.Index D.Index E, ∀ w,
    F (Y.realEquiv w) = Y'.realEquiv (realVecAction z w) := by
    let f₀ : (D.Index → E) →ₗ[𝓞 E] D.Index → E :=
      { toFun := f
        map_add' a b := toRealVectors_injective <| by
          rw [map_add, hf, hf, hf, map_add, map_add, map_add, map_add]
        map_smul' c a := toRealVectors_injective <| by
          rw [RingHom.id_apply, toRealVectors_smul, hf, hf, toRealVectors_smul, h_lin,
            ContinuousLinearEquiv.symm_apply_apply] }
    refine ⟨toMatrix' (f₀.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E),
      denseRange_toRealVectors.eq fun y ↦ ?_⟩
    rw [realVecAction_toRealVectors, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix',
      LinearMap.extendScalarsOfIsLocalization_apply', LinearMap.coe_mk, AddHom.coe_mk, hf,
      ContinuousLinearEquiv.apply_symm_apply]
  -- `z` is invertible because it pulls a form back to the nondegenerate form of
  -- `μ • Y.automorphyForm`.
  have hz_inj : Injective z.mulVec := by
    intro a b hab
    obtain ⟨h_left_nondeg, -⟩ : (RealComplexForm.riemannForm
      (Y'.automorphyForm.pullForm F)).Nondegenerate := by
      simpa only [← h_riem] using (Y.isPosRiemann.nsmul hμ).nondegenerate (L := Y.periodLattice)
    -- `F (Y.realEquiv (a - b)) = 0` pairs to zero with everything.
    have h_pair_zero (v : V) :
        RealComplexForm.riemannForm (Y'.automorphyForm.pullForm F)
          (Y.realEquiv (toRealVectors a) - Y.realEquiv (toRealVectors b)) v = 0 := by
      simp [hz, hab, riemannForm_pullForm]
    exact toRealVectors_injective (Y.realEquiv.injective
      (sub_eq_zero.mp (h_left_nondeg _ h_pair_zero)))
  lift z to GL D.Index E using mulVec_injective_iff_isUnit.mp hz_inj
  -- `z` conjugates `ℓ` to `ℓ'` as `F` is complex linear.
  have h_periods (w : RealVectors E D.Index) : m.π w ≫ ψ = m'.π (realVecAction z w) := by
    simp [← hF, hz, π]
  refine ⟨z, h_periods, ?_, Y.isPeriodMap.ratConj_eq Y'.isPeriodMap F hz⟩
  -- (b) is `h_riem` read through `Y.riemannForm_eq` and `Y'.riemannForm_eq`.
  intro y w
  calc
    _ = RealComplexForm.riemannForm (μ • Y.automorphyForm) (Y.realEquiv y) (Y.realEquiv w) := by
      rw [map_nsmul, LinearMap.smul_apply, LinearMap.smul_apply, Y.riemannForm_eq, nsmul_eq_mul]
    _ = RealComplexForm.riemannForm (Y'.automorphyForm.pullForm F) (Y.realEquiv y)
      (Y.realEquiv w) := by rw [h_riem]
    _ = _ := by
      rw [riemannForm_pullForm, hz, hz, Y'.riemannForm_eq]
      -- `↓`: the map of the product `zᴴ β' z` is split before `simp` distributes it entrywise.
      simp [polarisationForm, ↓map_conjTranspose_mul_mul, dotProduct_mulVec, star_mulVec]

/-- Objects with models have the same map from `𝓞 E`: after the injective map `O → ℂ`, both are
the embedding `Φ v₀`. -/
lemma baseHom_eq_baseHom (m : x.TorusModel Y) (m' : x'.TorusModel Y') :
    x'.baseHom = x.baseHom :=
  RingHom.ext fun c ↦ IsFractionRing.injective O ℂ (by rw [m'.baseHom_eq, m.baseHom_eq])

/-- `ψ` is an `𝓞 E`-linear isogeny from `x` to `x'` of multiplier `μ` that acts on torsion by
the adelic matrix `k` and on periods by the rational matrix `z`. -/
structure IsIsogenyOfMatrix (m : x.TorusModel Y) (m' : x'.TorusModel Y') (z : GL D.Index E)
    (k : GL D.Index (𝔸f E)) (μ : ℕ) (ψ : x.groupScheme ⟶ x'.groupScheme) : Prop where
  /-- `ψ` is an isogeny. -/
  isIsogeny : IsIsogeny ψ
  /-- `ψ` commutes with the action of `𝓞 E`. -/
  isLinear : IsLinear ψ
  /-- `ψ` pulls the class of `x'.lineBundle` back to `μ` times that of `x.lineBundle`. -/
  pull_picClass : x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass
  /-- `ψ` sends the torsion point of the class of `y` to that of `k y`. -/
  torsionPoint_comp (y : D.Index → 𝔸f E) :
    m.fullStructure.torsionPoint (torsionClass y) ≫ ψ =
      m'.fullStructure.torsionPoint (torsionClass (k.val *ᵥ y))
  /-- `ψ` sends `m.π w` to `m'.π (z w)`. -/
  π_comp (w : RealVectors E D.Index) : m.π w ≫ ψ = m'.π (realVecAction z w)

/-- Let `x`, `x'` be objects over `O` with torus models `m`, `m'` on the polarised period maps `Y`
(frame `g`, matrix `ℓ`) and `Y'` (frame `g'`, matrix `ℓ'`). Let `z ∈ GL_n(E)` satisfy `z ℓ z⁻¹ = ℓ'`
(conjugation through `Φ v₀`), and let `k = g'⁻¹ z g` have entries in `Ô E` (the integral finite
adeles of `E`) with `IsScalarFrame k⁻¹ μ`, i.e. `μ > 0` and `μ (k⁻¹)ᴴ k⁻¹ = ε·1` for a unit `ε` of
`Ẑ`. Then some `ψ : x.groupScheme ⟶ x'.groupScheme` is an `𝓞 E`-linear isogeny from `x` to `x'` of
multiplier `μ`, acting by `k` on torsion and by `z` on periods. -/
lemma exists_isIsogenyOfMatrix (z : GL D.Index E) (hz : ratConj z ℓ = ℓ')
    (m : x.TorusModel Y) (m' : x'.TorusModel Y') {k : GL D.Index (𝔸f E)} {μ : ℕ}
    (hk : g'⁻¹ * toFinGL z * g = k) (hk_int : ∀ i j : D.Index, k i j ∈ Ô E)
    (hμ : IsScalarFrame k⁻¹ μ) :
    ∃ ψ : x.groupScheme ⟶ x'.groupScheme, IsIsogenyOfMatrix m m' z k μ ψ := by
  -- `z` defines a complex linear map `F` of the universal covers that respects the lattices and
  -- multiplies the type of the theta functions by `μ`; `exists_hom_of_hasThetaCoords` makes it a
  -- homomorphism `ψ`.
  subst hk
  have hQ : Function.Surjective Y.realEquiv := Y.realEquiv.surjective
  -- `F` is complex linear because `z` carries `ℓ` to `ℓ'`.
  have h_conj : z.map (Φ v₀) * ℓ = ℓ' * z.map (Φ v₀) := (z.map _).mul_inv_eq_iff_eq_mul.mp hz
  have h_rva (u : RealVectors E D.Index) (i : D.Index) (v : InfinitePlace E) :
      realVecAction z.val u i v = (z.val.map (Φ v) *ᵥ fun j ↦ u j v) i := by
    simp only [realVecAction, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Finset.sum_apply, Pi.mul_apply, Matrix.map_apply, RingHom.pi_apply]
  have hF_I (w : RealVectors E D.Index) :
      Y'.realEquiv (realVecAction z.val (Complex.I • fun (i : D.Index) (v : InfinitePlace E) ↦
          ((if v = v₀ then ℓ else 1) *ᵥ fun j ↦ w j v) i)) =
        Complex.I • Y'.realEquiv (realVecAction z.val w) := by
    rw [← Y'.isPeriodMap]
    refine congrArg Y'.realEquiv ?_
    funext i v
    rw [h_rva, Pi.smul_apply]
    change (z.val.map (Φ v) *ᵥ (Complex.I • ((if v = v₀ then ℓ else 1) *ᵥ fun j ↦ w j v))) i =
      Complex.I * ((if v = v₀ then ℓ' else 1) *ᵥ fun j ↦ realVecAction z.val w j v) i
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, mulVec_mulVec]
    have h_eq : z.val.map (Φ v) * (if v = v₀ then ℓ else 1) =
        (if v = v₀ then ℓ' else 1) * z.val.map (Φ v) := by
      split_ifs with hv
      · subst hv; exact h_conj
      · rw [Matrix.mul_one, Matrix.one_mul]
    rw [h_eq, ← mulVec_mulVec]
    congr 2
    funext j
    exact (h_rva w j v).symm
  let F_r : V →L[ℝ] V' :=
    Y.realEquiv.arrowCongr Y'.realEquiv (realVecAction z.val).toContinuousLinearMap
  have hF_r (w : RealVectors E D.Index) :
      F_r (Y.realEquiv w) = Y'.realEquiv (realVecAction z.val w) := by
    change Y'.realEquiv (realVecAction z.val (Y.realEquiv.symm (Y.realEquiv w))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  let F : V →L[ℂ] V' :=
    { F_r with
      map_smul' a v := by
        obtain ⟨w, rfl⟩ := hQ v
        change F_r (a • Y.realEquiv w) = a • F_r (Y.realEquiv w)
        rw [smul_eq_re_smul_add_im_smul a, smul_eq_re_smul_add_im_smul a, ← Y.isPeriodMap w,
          F_r.map_add, F_r.map_smul, F_r.map_smul, hF_r, hF_r, hF_I w] }
  have hF_Q (w : RealVectors E D.Index) :
      F (Y.realEquiv w) = Y'.realEquiv (realVecAction z.val w) := hF_r w
  -- `F` maps lattice to lattice because `g'⁻¹ z g` is integral.
  have h_lat : ∀ l ∈ m.uniformisation.lattice, F l ∈ m'.uniformisation.lattice := by
    intro l hl
    rw [m.lattice_eq, mem_classLattice] at hl
    obtain ⟨y, hy, rfl⟩ := hl
    have hP : toRealVectors y ∈ frameLattice g := by
      rw [frameLattice, Submodule.mem_toAddSubgroup, mem_classLattice]
      exact ⟨y, hy, rfl⟩
    have hPz := realVecAction_mem_frameLattice hk_int hP
    rw [frameLattice, Submodule.mem_toAddSubgroup, mem_classLattice] at hPz
    obtain ⟨y', hy', hy'_eq⟩ := hPz
    rw [m'.lattice_eq, mem_classLattice]
    exact ⟨y', hy', by rw [hF_Q, ← hy'_eq]; rfl⟩
  -- `z` pulls the form `Y'.formMatrix` back to `μ • Y.formMatrix`, by positivity and `hμ`
  -- (`conjTranspose_mul_mul_eq_smul`).
  have h_riem :
      RealComplexForm.riemannForm (Y'.automorphyForm.pullForm F) = RealComplexForm.riemannForm
        (μ • Y.automorphyForm) := by
    -- At `Y.realEquiv y`, `Y.realEquiv w` the left side is the polarisation form of `Y'.formMatrix`
    -- at `z y`, `z w`.
    refine LinearMap.ext₂ (hQ.forall.mpr fun y ↦ hQ.forall.mpr fun w ↦ ?_)
    -- `map_nsmul` is rewritten by name: `simp` first tries `map_smul` on `μ • Y.automorphyForm`
    -- and is slow to fail.
    rw [riemannForm_pullForm, hF_Q, hF_Q, Y'.riemannForm_eq, map_nsmul, LinearMap.smul_apply,
      LinearMap.smul_apply, Y.riemannForm_eq, nsmul_eq_mul]
    -- After `conjTranspose_mul_mul_eq_smul` both sides are sums over the infinite places, equal
    -- term by term.
    simp [← map_conjTranspose_mul_mul, vecMul_smul, map_smul', Finset.mul_sum,
      Y.isSignedFrameFor.conjTranspose_mul_mul_eq_smul Y'.isSignedFrameFor hμ, polarisationForm,
      dotProduct_mulVec, star_mulVec]
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  -- Both multipliers are canonical, `χ l = exp (π i e(β l, l))` with `e` the Riemann form and
  -- `β = D.β`, so `h_riem` compares them.
  have h_char : ∀ l ∈ m.uniformisation.lattice, (m'.χ ∘ F) l = (m.χ ^ μ) l := by
    intro l hl
    -- `F` commutes with the action of `D.β`, since `z` acts linearly over `E ⊗ ℝ`.
    have h_comm : Y'.intAction D.β (F l) = F (Y.intAction D.β l) := by
      obtain ⟨w, rfl⟩ := hQ l
      rw [hF_Q, intAction_realEquiv, intAction_realEquiv, hF_Q, (realVecAction z.val).map_smul]
    -- So `h_riem` at `β l`, `l` compares the two exponents.
    have h_form := LinearMap.congr_fun₂ h_riem (Y.intAction D.β l) l
    rw [riemannForm_pullForm, ← h_comm, map_nsmul, LinearMap.smul_apply, LinearMap.smul_apply,
      nsmul_eq_mul] at h_form
    simp [multiplier_eq_canonicalMultiplier _ _ hl,
      multiplier_eq_canonicalMultiplier _ _ (h_lat l hl), canonicalMultiplier, h_form,
      ← Complex.exp_natCast_mul, mul_left_comm]
  -- Pull the theta coordinates of `x'` back along `F`.
  have h_pull :
      HasThetaCoords m.uniformisation.lattice (fun v : V ↦ atGeneric m'.uniformisation.expMap (F v))
        x'.lineBundle (Y'.automorphyForm.pullForm F) (m'.χ ∘ F) (m'.θ ∘ F) := by
    -- `pull_id` is rewritten: the kernel is slow to unfold `x'.lineBundle.pull (𝟙 _)`.
    have h := m'.hasThetaCoords.pull F (fun _ ↦ .symm (comp_id _)) h_lat
    rwa [LineBundle.pull_id] at h
  -- Corrected by an exponential factor, they are theta coordinates of `x'.lineBundle` of type
  -- `(μ • Y.automorphyForm, m.χ ^ μ)`.
  obtain ⟨θ₀, h_coords⟩ : ∃ θ₀ : V → D.dualTorsion → ℂ, HasThetaCoords m.uniformisation.lattice
      (atGeneric (m'.uniformisation.expMap.comp F.toAddMonoidHom)) x'.lineBundle
        (μ • Y.automorphyForm) (m.χ ^ μ)
      θ₀ :=
    have h_AH : IsAppellHumbert (L := m.uniformisation.lattice) (μ • Y.automorphyForm) (m.χ ^ μ) :=
      m.hasThetaCoords.isAppellHumbert.nsmul μ
    ⟨_, h_pull.isLinearSystem, h_AH,
      fun i ↦ h_pull.isAppellHumbert.exp_mul_mem_thetaSpace h_AH h_riem h_char
        (h_pull.mem_thetaSpace i),
      fun w ↦ (m'.hasThetaCoords.hasFieldCoords (F w)).smul (by simp)⟩
  -- `F` sends the lattice of `m` into that of `m'`, which the uniformisation of `x'` kills.
  have h_kill : ∀ l ∈ m.uniformisation.lattice, m'.uniformisation.expMap (F l) = 0 :=
    fun l hl ↦ (m'.uniformisation.eq_zero_iff (F l)).mp (h_lat l hl)
  -- Translations by the dual lattice lift to `x.lineBundle`, so the theta coordinates give `ψ`.
  -- (Of `exists_isTranslationLift_of_dualLattice` only the lift is used, not its invariant span.)
  obtain ⟨ψ, h_add, hψ, h_cls⟩ :
      ∃ ψ : x.groupScheme ⟶ x'.groupScheme,
        IsAdditive ψ ∧
        (∀ v : V, m.uniformisation.expMap v ≫ ψ = m'.uniformisation.expMap (F v)) ∧
        x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass :=
    exists_hom_of_hasThetaCoords _ m.hasThetaCoords h_kill x.isThetaStructure.isUnit_card
      (fun b hb ↦ (m.exists_isTranslationLift_of_dualLattice b hb).imp_right
        fun ⟨Φ, hΦ, _⟩ ↦ ⟨Φ, hΦ⟩) x'.isProjEmbedding
      x.isProjEmbedding x.hasClassLaws.1 x'.hasClassLaws.1 h_coords
  have hψ_π (w : RealVectors E D.Index) : m.π w ≫ ψ = m'.π (realVecAction z w) := by
    simp [hF_Q, hψ, π]
  -- The image of `ψ` contains the dense set of sections of `x'`.
  have h_surj : AlgebraicGeometry.Surjective ψ.left :=
    (isSeparatingFamily_atGeneric_of_surjective m'.uniformisation.surjective).2.surjective _
      (atGeneric m.π ∘ realVecAction z⁻¹ ∘ Y'.realEquiv.symm)
      (by simp [atGeneric, ← Over.comp_left, hF_Q, hψ, π])
  have h_isog : IsIsogeny ψ := isIsogeny_of_locallyQuasiFinite ψ
    (locallyQuasiFinite_of_pull_picClass x.isProjEmbedding (Nat.cast_pos.mp hμ.left).ne' h_cls)
    h_surj
  -- Linearity is tested on the dense set of sections of `x`.
  have h_lin : IsLinear ψ := by
    refine ⟨fun c ↦ (isSeparatingFamily_atGeneric_of_surjective
      (m.uniformisation.surjective.comp hQ)).hom_ext fun w ↦ ?_⟩
    rw [assoc, assoc]
    refine congrArg (_ ≫ ·) ?_
    change m.uniformisation.expMap (Y.realEquiv w) ≫ (c • 𝟙 x.groupScheme) ≫ ψ =
      m.uniformisation.expMap (Y.realEquiv w) ≫ (c • ψ)
    rw [← assoc, ModuleObj.comp_smul, Category.comp_id, ← m.equivariant, hψ, hF_Q,
      (realVecAction z.val).map_smul, m'.equivariant, ← hF_Q, ← hψ, ← ModuleObj.comp_smul]
  exact ⟨ψ, h_isog, h_lin, h_cls, m.torsionPoint_comp m' hψ_π, hψ_π⟩

/-- Let `z ∈ GL_n(E)` satisfy `z ℓ z⁻¹ = ℓ'` (`hz`), and let `k = g'⁻¹ z g` have integral entries
with `IsScalarFrame k⁻¹ μ` (μ > 0 and `k⁻¹` is a frame for the scalar matrix μ). Then `x` and `x'`
have the same map from `𝓞 E`, and there is an `𝓞 E`-linear isogeny `ψ` that pulls the class of
`x'.lineBundle` back to `μ` times that of `x.lineBundle` and satisfies `ψ π = π' z`. It sends the
torsion point of the class of `y` to that of `k y`, for every finite adelic vector `y`. -/
lemma exists_isogeny (z : GL D.Index E) (hz : ratConj z ℓ = ℓ') (m : x.TorusModel Y)
    (m' : x'.TorusModel Y') {k : GL D.Index (𝔸f E)} {μ : ℕ} (hk : g'⁻¹ * toFinGL z * g = k)
    (hk_int : ∀ i j : D.Index, k i j ∈ Ô E) (hμ : IsScalarFrame k⁻¹ μ) :
    x'.baseHom = x.baseHom ∧
    ∃ ψ : x.groupScheme ⟶ x'.groupScheme,
      IsIsogeny ψ ∧ IsLinear ψ ∧
      -- (a) the multiplier is `μ`
      x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass ∧
      -- (b) `ψ` acts on torsion by `k`
      (∀ y : D.Index → 𝔸f E,
        m.fullStructure.torsionPoint (torsionClass y) ≫ ψ =
          m'.fullStructure.torsionPoint (torsionClass (k.val *ᵥ y))) ∧
      -- (c) `ψ` acts on periods by `z`
      ∀ w : RealVectors E D.Index, m.π w ≫ ψ = m'.π (realVecAction z w) := by
  obtain ⟨ψ, hψ⟩ := exists_isIsogenyOfMatrix z hz m m' hk hk_int hμ
  exact ⟨baseHom_eq_baseHom m m', ψ, hψ.isIsogeny, hψ.isLinear, hψ.pull_picClass,
    hψ.torsionPoint_comp, hψ.π_comp⟩

end New.ThetaObject.TorusModel
