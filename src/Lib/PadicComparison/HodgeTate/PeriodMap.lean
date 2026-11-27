module

import Mathlib.AlgebraicGeometry.PointsPi
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Algebra.Module.Compact
public import Lib.Cohomology.SmoothBaseChange
import Lib.Cohomology.Etale.DenseSubfunctors
import Lib.General.Geometry.PointsOfProperSchemes
import Lib.General.NumberTheory.CoefficientRings
import Lib.PadicComparison.Descent.TestCovers
public import Lib.Cohomology.Etale.EllAdicCohomology
public import Lib.PadicComparison.Primitive.PeriodCoefficients
public import Lib.PadicComparison.HodgeTate.Map
import Lib.PadicHodge.PeriodRings.DeRhamPeriods
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Lib.GaloisRep.Main.LocalConditions

section
/-!
# The primitive comparison theorem and finiteness of p-adic cohomology

This file concerns a proper scheme `Y` over `R` that is charted over an algebraic closure `Ω` of `ℚ`
(`New.Variety.IsCharted`). A p-adic test is a product of valuation rings over `O_C`, the integers of
`ℂ_p`, and `O^♭` is the tilt of `O_C`. The primitive comparison theorem compares the mod `p`
cohomology of `Y`, tensored with `O^♭`, with the cohomology of its points in p-adic tests with
tilted coefficients.

## Main definitions and results

* `New.Variety.finite_and_primitive_comparison`: let `Y` be proper over `R` and charted over `Ω`,
  and assume `IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))`. Then `Y_Ω` has flat base change and
  finite mod `p` cohomology, and the comparison map is bijective.
* `New.Variety.finite_padic_cohomology`: the cohomology with coefficients `ℤ_p` is finitely
  generated; hence `New.Variety.ellAdicCohom R Ω n`, which is `ℚ_p ⊗` this module, is
  finite-dimensional at `Y`.
* `New.Variety.ellAdicCohom.continuous_galoisAction`: the Galois action
  `New.Variety.ellAdicCohom.galoisAction` is continuous, tested on a vector and a linear map to
  `Q̄_p ^ N`. Modulo `p ^ k` a class is defined over finitely many elements of `Ω`, so it is fixed
  by an open subgroup.

Notions from other files:
* `New.Variety.genericTestOver`: The functor sending a p-adic test with ring R to R[1/p], a test
  over Ω with algebra structure through Ω → ℂ_p.
* `New.Variety.primitiveMap`: The natural map O^♭ ⊗ LC(Spec S[1/p], 𝔽_p) → S^♭ on p-adic tests S,
  with LC the locally constant functions; its source is `New.Variety.oFlatLocConst`.
* `New.Variety.HasFlatBaseChange` N: M ⊗ Hⁿ(N, Φ) → Hⁿ(N, M ⊗ Φ) is bijective for flat M.
* `New.Variety.testPoints`: For R → O_C, the functor sending an R-scheme X to the functor S ↦ X(S)
  of its points over R in p-adic tests.
* `New.Variety.H`: `H N F n` is Extⁿ(N, F) among functors to abelian groups; for
  `N = freeAb X = ℤ[X]` it is the cohomology Hⁿ(X, F). `testIncl ⋙ X` restricts `X` to test rings.

## Relation to the literature

Known result: Finiteness and Galois continuity of p-adic étale cohomology. The result is stated for
cohomology on test rings, not identified with étale cohomology, of proper schemes charted over an
algebraic closure of Q, with constant coefficients, where integral coefficients are the Witt vectors
of the mod p functions. Finiteness is lifted from finiteness modulo p, which comes from the
primitive comparison. Source: SGA 4, Exp. XIV (Artin), finiteness for proper morphisms; Scholze 2013
Thm 1.1; by duality, Zavyalov arXiv 2301.03821 Appl. 1.3.4.

See also `Lib.PadicComparison.HodgeTate.PeriodMap`.
-/

@[expose] public section

/-! ## The primitive comparison theorem and flat base change -/

namespace New.Variety

open CategoryTheory TensorProduct Functor Period AlgebraTensorModule AlgebraicGeometry TotalH
  Function PadicTest Abelian.Ext ConcreteCategory Comparison DirectSum ULift CommRingCat Over

variable {p : ℕ} [ThePrime p]
  {M : ModuleCat OFlat} {R : CommRingCat}
  (Ω : Type) [Field.{0} Ω] [Algebra R Ω] [Algebra Ω ℂ_[p]]

/-- The valuative criterion in a p-adic test `c`. Its ring `c.ProdRing` is the product of a
non-empty family of valuation rings (cells) with a ring map from O_C, and
`c.GenericRing = c.ProdRing[1/p]`. Let `Y` be proper over `R`, and make `Spec c.ProdRing` and
`Spec c.GenericRing` schemes over `R` by `a : Spec c.ProdRing ⟶ Spec R` and
`b : Spec c.GenericRing ⟶ Spec R`. The map `Spec c.GenericRing → Spec c.ProdRing` is a map over `R`:
`w` says that `b` is the restriction of `a`, and `r` is the trivial map of the one-point base of
`Over`, so `w` is `Spec.map (algebraMap c.ProdRing c.GenericRing) ≫ a = b ≫ 𝟙 _`. Then restriction
`Y(c.ProdRing) → Y(c.GenericRing)` of points over `R` is bijective. -/
lemma PadicTest.bijective_generic_points {Y : Over (Spec R)} [IsProper Y.hom] (c : PadicTest)
    {a b r w} :
    Bijective
      ((uliftYoneda.{1} Y).map
        (.op (X := .mk b) (Y := .mk a)
          ⟨Spec.map (ofHom (algebraMap c.ProdRing c.GenericRing)), r, w⟩)) := by
  have hY_compact : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  -- `Y` is separated: two points agree if they do after a jointly injective family of ring maps.
  have h_sep {C : CommRingCat} {J : Type} {K : J → CommRingCat} (f : ∀ j, C ⟶ K j)
      (hf : ∀ t : C, (∀ j, f j t = 0) → t = 0) {x y : Spec C ⟶ Y.left}
      (h : ∀ j, Spec.map (f j) ≫ x = Spec.map (f j) ≫ y) : x = y :=
    up.inj ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective f hf fun j ↦
      congrArg up (h j))
  refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
  · -- Injectivity: `c.ProdRing → c.GenericRing` is itself injective.
    have h_left : x.down.left = y.down.left :=
      h_sep (fun _ : Unit ↦ ofHom (algebraMap c.ProdRing c.GenericRing))
        (fun t ht ↦ c.eq_zero_of_algebraMap_genericRing t (ht ())) fun _ ↦ congrArg (·.down.left) h
    exact down_injective (OverMorphism.ext h_left)
  -- Surjectivity. As `p ≠ 0` in the cell `c.Cell i`, the projection extends to a map `φ i` from
  -- `c.GenericRing` to the fraction field of the cell.
  let π (i : c.Index) : CommRingCat.of c.ProdRing ⟶ CommRingCat.of (c.Cell i) :=
    CommRingCat.ofHom (Pi.evalRingHom c.Cell i)
  let j (i : c.Index) : CommRingCat.of (c.Cell i) ⟶ CommRingCat.of (FractionRing (c.Cell i)) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hp (i : c.Index) : IsUnit ((π i ≫ j i).hom p) := by
    simp [π, j, -map_natCast, IsCell.p_ne_zero]
  let φ (i : c.Index) : c.GenericRing →+* FractionRing (c.Cell i) :=
    IsLocalization.Away.lift (p : c.ProdRing) (hp i)
  have sq (i : c.Index) : CommSq (Spec.map (ofHom (φ i))) (Spec.map (j i))
      (Spec.map (ofHom (algebraMap c.ProdRing c.GenericRing))) (Spec.map (π i)) :=
    ⟨by simp [← Spec.map_comp, ← ofHom_comp, φ, π, j]⟩
  -- The valuative criterion extends the point `z` over `Frac (c.Cell i)` to the cell `c.Cell i`.
  have lift (i : c.Index) : ∃ l : Spec (CommRingCat.of (c.Cell i)) ⟶ Y.left,
      Spec.map (j i) ≫ l = Spec.map (ofHom (φ i)) ≫ z.down.left ∧
        l ≫ Y.hom = Spec.map (π i) ≫ a := by
    have h_val : ValuativeCriterion.Existence Y.hom :=
      (UniversallyClosed.eq_valuativeCriterion.le _ _ _ inferInstance).1
    -- the valuative square: the cell, its fraction field, `z` after `φ i` on top, `a` on the cell
    let S : ValuativeCommSq Y.hom :=
      { R := c.Cell i, K := FractionRing (c.Cell i)
        i₁ := Spec.map (ofHom (φ i)) ≫ z.down.left, i₂ := Spec.map (π i) ≫ a
        commSq := (sq i).horiz_comp ⟨z.down.w.trans w.symm⟩ }
    obtain ⟨⟨l⟩⟩ : S.commSq.HasLift := h_val S
    exact ⟨l.l, l.fac_left, l.fac_right⟩
  choose l hl_left hl_right using lift
  -- `Y` is quasi-compact, so the points `l i` come from a point `x` in the product `c.ProdRing`.
  have (i : c.Index) : IsLocalRing (CommRingCat.of (c.Cell i)) :=
    ValuationRing.isLocalRing (c.Cell i)
  obtain ⟨x, hx⟩ := pointsPi_surjective (CommRingCat.of <| c.Cell ·) Y.left l
  have hx_eq (i : c.Index) : Spec.map (π i) ≫ x = l i := congrFun hx i
  have hx_over : x ≫ Y.hom = a := by
    -- both sides are determined by their restrictions to the cells, where `hl_right` holds
    refine pointsPi_injective _ _ (funext fun i ↦ ?_)
    change Spec.map (π i) ≫ x ≫ Y.hom = Spec.map (π i) ≫ a
    rw [← Category.assoc, hx_eq, hl_right]
  -- The restriction of `x` to `c.GenericRing` and `z` agree after each `φ i`.
  refine ⟨⟨homMk x hx_over⟩,
    down_injective (OverMorphism.ext (h_sep (fun i ↦ ofHom (φ i)) (fun t ht ↦ ?_) fun i ↦ ?_))⟩
  · -- The `φ i` are jointly injective: up to a unit, `t` comes from some `r : c.ProdRing`.
    obtain ⟨r, u, rfl⟩ := exists_associated_localization t
    have hr : r = 0 := funext fun i ↦ by
      have h0 : φ i (algebraMap c.ProdRing c.GenericRing r * u) = 0 := ht i
      rw [map_mul, IsLocalization.Away.lift_eq, (u.isUnit.map (φ i)).mul_left_eq_zero] at h0
      exact IsFractionRing.injective (c.Cell i) (FractionRing (c.Cell i))
        (h0.trans (map_zero _).symm)
    rw [hr, RingHom.map_zero, zero_mul]
  · -- after `Spec (φ i)`, the restriction of `x` to `c.GenericRing` is `x` on the cell, that is
    -- `l i`, which extends `z`
    change Spec.map (ofHom (φ i)) ≫ Spec.map (ofHom (algebraMap c.ProdRing c.GenericRing)) ≫ x =
      Spec.map (ofHom (φ i)) ≫ z.down.left
    rw [(sq i).w_assoc, hx_eq, hl_left]

/-- For a scheme Y over R, the map Y(S) → Y(S[1/p]), natural in the p-adic test S; `he` says that
R → Ω → ℂ_p agrees with R → O_C → ℂ_p. -/
noncomputable def toGenericPoints [Algebra R OC]
    (he : ∀ r : R, algebraMap Ω ℂ_[p] (algebraMap R Ω r) = algebraMap R OC r) (Y : Over (Spec R)) :
    testPoints Y ⟶ genericTestOver Ω ⋙ ObjectProperty.ι _ ⋙ algPointsOf Ω R Y :=
  whiskerRight (H := genericAlg ⋙ restrictAlg Ω (ℂ_[p]) ⋙ restrictAlg R Ω)
    { app c :=
        CommAlg.homOfRingHom (algebraMap c.ProdRing c.GenericRing) fun r ↦
          (he r ▸ c.genericStructureMap_coe ((algebraMap R OC) r)).symm
      naturality := by
        intros
        ext
        exact (mapGeneric_algebraMap ..).symm }
    (algPointsOf R R Y)

/-- Let `Ω` be a field in which `ℓ` is invertible and `D` a compared theory on tests over `Ω`
(`New.Variety.ComparedTheory`). Then `D.IsFiniteLerayHirsch` (the classes `D.comparison` form a
Leray–Hirsch basis and the total cohomology is finite) holds for `ℤ[X] = freeAb X` iff it holds for
`ℤ[X] / ℤ[U]` (`relFreeAb`), where `U = offClosedFiber X` is the part of `X` away from the special
fibre. Over a field `U` does not count: the maximal ideal of `Ω` is zero, so `U` has points only
over the zero ring. -/
lemma ComparedTheory.isFiniteLerayHirsch_freeAb_iff_relFreeAb {ℓ : ℕ} {Ω : Type} {C : Type 1}
    [Field Ω] [InvertsPrime Ω ℓ]
    [Category.{0, 1} C] {g : C ⥤ TestOver Ω} (D : ComparedTheory g) {X : TestOver Ω ⥤ Type 1} :
    D.IsFiniteLerayHirsch (freeAb X) ↔ D.IsFiniteLerayHirsch (relFreeAb (offClosedFiber X)) := by
  -- `D.IsFiniteLerayHirsch` is a closed class: it holds at zero objects, and along a short exact
  -- sequence it passes between the middle and the quotient when it holds for the subobject
  obtain ⟨h_zero, h_ses⟩ := D.isClosedClass_isFiniteLerayHirsch
  -- The maximal ideal of `Ω` is zero, so `offClosedFiber X` has points only over the zero ring and
  -- does not count.
  have h_sub : D.IsFiniteLerayHirsch (freeAb (offClosedFiber X).toFunctor) := by
    -- The empty subfunctor is locally everything: a ring with a point `y` has no maximal ideal.
    refine (D.isFiniteLerayHirsch_iff_of_isCohomEquiv (freeAb.map (Subfunctor.ι ⊥))
      fun _ zar ↦ ?_).mp (h_zero _ (freeAb.hom_ext nofun))
    refine (zar (U := .whisker (Y := (offClosedFiber X).toFunctor) ⊥ _)
      fun _ y _ hm ↦ ?_).isCohomEquiv
    refine (hm.ne_top (eq_top_mono ?_ y.prop)).elim
    simp only [IdealFamily.ofMaximalIdeal, IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.map_le_iff_le_comap.2 bot_le
  obtain ⟨w, h_exact⟩ := relFreeAb.shortExact (offClosedFiber X)
  exact h_ses ⟨_, _, w⟩ h_exact h_sub

omit [ThePrime p] [Algebra Ω ℂ_[p]] in
/-- The points of a proper `Y` over `R` on tests over `Ω` have flat base change: the functor is
covered by affine pieces (`isAffinelyCovered_algPointsOf`). -/
lemma hasFlatBaseChange_algPointsOf (Y : Over (Spec R)) [IsProper Y.hom] :
    HasFlatBaseChange
      (freeAb (ObjectProperty.ι _ ⋙ algPointsOf Ω R Y) : AbFunctor (TestOver Ω)) :=
  (isAffinelyCovered_algPointsOf (·.property.isComparableRing) Y).hasFlatBaseChange

omit [ThePrime p] [Algebra Ω ℂ_[p]] in
/-- Flat base change for the points of `Y_Ω` on test rings, for `Y` proper over `R`. Restriction
from all test rings to tests over `Ω` is bijective on cohomology (`isBijective_algToBaseChange`)
and commutes with base change (`baseChangeMap_pull`), and on tests over `Ω` flat base change holds
by `hasFlatBaseChange_algPointsOf`. -/
lemma hasFlatBaseChange_geomPoints (Y : Over (Spec R)) [IsProper Y.hom] :
    HasFlatBaseChange (freeAb (testIncl ⋙ geomPoints R Ω Y)) := by
  -- the eight instance arguments of `HasFlatBaseChange` stay anonymous
  intro S T L _ _ _ _ _ _ _ _ Φ n
  exact (bijective_iff_of_comm_sq (baseChangeMap_pull (𝟙 _) _)
      (map_bijective bijective_id (isBijective_algToBaseChange Ω Y (moduleCoeff Φ) n))
      (by simpa using! isBijective_algToBaseChange ..)).2
    (hasFlatBaseChange_algPointsOf Ω Y ..)

/-- The functors `S ↦ Hom(O^♭, S^♭)` (maps of `O^♭`-algebras) and `S ↦ Hom(Ω, S[1/p])` (maps of
tests over `Ω`) on `p`-adic tests are isomorphic: each value is a single point, since `O^♭` and
`Ω` are initial. -/
noncomputable def tiltReprIsoGenericRepr [IsAbsIntegrallyClosedLocal Ω] :
    tilt ⋙ reprBy (.of OFlat OFlat) ≅ genericTestOver Ω ⋙ reprBy (.ofSelf Ω) :=
  -- at each test there is exactly one map of `O^♭`-algebras out of `O^♭`
  have h_init (A : PadicTest) : Bijective ((toUnit (tilt ⋙ reprBy (.of OFlat OFlat))).app A) :=
    ⟨fun _ _ _ ↦ congrArg ULift.up (CommAlgCat.hom_ext (by ext)), fun _ ↦ ⟨⟨structureMap⟩, rfl⟩⟩
  isoOfAppBijective _ h_init ≪≫ isoWhiskerLeft _
    (isoOfAppBijective _ pointMap_ofSelf_bijective).symm

/-- The locally constant functions on `Spec Ω`, tensored with `O^♭` (`oFlatLocConst` at the test
`Ω`), are `O^♭` itself: on the spectrum of a field the locally constant functions are
constant. -/
noncomputable def oFlatLocConstOfSelfIso [IsAbsIntegrallyClosedLocal Ω] :
    CommAlgCat.of OFlat OFlat ≅ (TestOver.toTest Ω ⋙ oFlatLocConst).obj (.ofSelf Ω) :=
  CommAlgCat.isoMk (.ofBijective _ (Algebra.TensorProduct.includeLeft_bijective
    ((bijective_const_of_isDomain (B := .of Ω)).of_comp_left up_injective)))

/-- Primitive comparison. Let `Ω` be algebraically closed with a map to `ℂ_p`, `Y` proper over `R`
and charted over `Ω` (`IsCharted`), and `M` an `O^♭`-module. Assume `ac`: for each perfect
`O^♭`-algebra `b`, the functor `S ↦ Hom(b, S^♭)` on p-adic tests, with coefficients `S ↦ S^♭ ⊗ M`,
has cohomology `b ⊗ M` in degree 0. Write `X` for the points of `Y_Ω` on test rings. Then (a) the
cohomology of `Y_Ω` commutes with flat extension of coefficients; (b) each `Hⁿ(Y_Ω, 𝔽_p)` is finite;
(c) if moreover `R` maps to `O_C` compatibly (`he`), then `primitiveMap ⊗ M` induces a bijection in
every degree, along `toGenericPoints` followed by `algToBaseChange` (points of `Y` over tests over
`Ω` taken as points of `Y_Ω`). Here `primitiveMap` is the natural map `O^♭ ⊗ LC(Spec S[1/p]) → S^♭`,
with `LC` the locally constant `𝔽_p`-valued functions. The bijection goes from the cohomology of
`Y_Ω` with coefficients `A ↦ O^♭ ⊗ LC(Spec A) ⊗ M` to that of `S ↦ Y(S)` on p-adic tests with
coefficients `S^♭ ⊗ M`. Only (c) uses the map `R → O_C`. -/
lemma finite_and_primitive_comparison [IsAlgClosed Ω]
    (ac : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))) (Y : Over (Spec R)) [IsCharted Y Ω]
    [IsProper Y.hom] :
    let X := testIncl ⋙ geomPoints R Ω Y
    -- (a)
    HasFlatBaseChange (freeAb X) ∧
    -- (b)
    (∀ n : ℕ, Finite (H (freeAb X) (locConstCoeff ⟨ZMod p⟩) n)) ∧
    -- (c)
    ∀ [Algebra R OC] (he : ∀ r : R, algebraMap Ω ℂ_[p] (algebraMap R Ω r) = algebraMap R OC r),
      CoeffCompBijective primitiveMap
        (freeAbMap (Y := X)
          (toGenericPoints Ω he Y ≫
            whiskerLeft (genericTestOver Ω) (whiskerLeft _ (algToBaseChange Ω Y))))
        (tensorCoeff M) := by
  -- The comparison `c` induced by `primitiveMap` is bijective iff a basis of `M` over `ZMod p`
  -- gives a bijective Leray–Hirsch map. This holds at the point `Ω`, so at `Y` by
  -- `ComparedTheory.mem_of_isClosedClass_of_isCharting`.
  have h_inverts : InvertsPrime Ω p :=
    InvertsPrime.mk (NeZero.nat_of_neZero (algebraMap Ω ℂ_[p])).out.isUnit
  let module_ZMod : Module (ZMod p) M := Module.restrictScalars (ZMod p) OFlat M
  -- `M ⊗[ZMod p] L ≅ (OFlat ⊗[ZMod p] L) ⊗[OFlat] M` for `L` the locally constant functions.
  let γ₀ : asModules (TestOver.toTest Ω ⋙ testIncl ⋙ locConstAlg) ⋙ tensorWith OFlat M ≅
      (TestOver.toTest Ω ⋙ oFlatLocConst) ⋙ tensorCoeff M :=
    NatIso.ofComponents
      (fun _ ↦ ((cancelBaseChange ..).symm ≪≫ₗ TensorProduct.comm ..).toModuleIso)
      fun _ ↦ ModuleCat.hom_ext (tmul_ext fun _ _ ↦ by rfl)
  let γ : moduleCoeff (asModules (TestOver.toTest Ω ⋙ testIncl ⋙ locConstAlg) ⋙ tensorWith _ M) ≅
      TestOver.toTest Ω ⋙ oFlatLocConst ⋙ moduleCoeff (tensorCoeff M) :=
    isoWhiskerRight γ₀ (moduleCoeff (𝟭 _))
  let b := Module.Free.chooseBasis (ZMod p) M
  let c : Comparison (TestOver.toTest Ω ⋙ oFlatLocConst ⋙ moduleCoeff (tensorCoeff M))
      (tiltTheory Ω M ac).functor :=
    ⟨genericTestOver Ω, whiskerRight primitiveMap (moduleCoeff _)⟩
  -- The tilted theory, with the classes `x ↦ b i ⊗ x` of degree zero. It and the locally
  -- constant theory satisfy the projective line formula.
  let θ (i : Module.Free.ChooseBasisIndex (ZMod p) M) :=
    mk₀ (whiskerLeft _ (tensorWith.mk _ (b i) _ ≫ γ.hom) ≫ c.coeffHom)
  have : FaithfulSMul Ω ℂ_[p] :=
    (faithfulSMul_iff_algebraMap_injective Ω ℂ_[p]).mpr (algebraMap Ω ℂ_[p]).injective
  let D : ComparedTheory (genericTestOver Ω) :=
    ⟨tiltTheory Ω M ac, _, θ, hasLineFormula_tiltTheory _ ac, hasLineFormula_locallyConstant Ω⟩
  have lh_iff {X : TestOver Ω ⥤ Type 1} {X' : PadicTest ⥤ Type 1}
      (hX : HasFlatBaseChange (freeAb X)) (u : X' ≅ c.functor ⋙ X) :
      IsLerayHirschBasis D.comparison (freeAb X) ↔ c.IsBijective (freeAbMap u.hom) := by
    -- By the basis `b`, flat base change and `γ`, the cohomology of `M ⊗ L` is a sum of copies
    -- of that of `L`.
    let E₀ : (_ →₀ TotalH (freeAb X) _) ≃+ TotalH (freeAb X) _ :=
      ((equivFinsuppOfBasisLeft b).symm ≪≫ₗ directSumRight ..).toAddEquiv.trans
        (congrAddEquiv fun n ↦
          .trans (.ofBijective _ (hX ..))
            (.ofBijective _ (H.push_bijective_of_isIso γ.isIso_hom n)))
    -- The `i`-th copy is mapped by pushing along `x ↦ b i ⊗ x` and `γ`.
    have hE (i : Module.Free.ChooseBasisIndex (ZMod p) M) (n : ℕ)
        (x : H (freeAb X)
          (moduleCoeff (asModules (TestOver.toTest Ω ⋙ testIncl ⋙ locConstAlg))) n) :
        E₀ (.single i (.of _ n x)) =
          TotalH.comp (.comp (.of _ n x) (.homClass (tensorWith.mk _ (b i) _)))
            (.homClass γ.hom) := by
      simp [E₀, ← lof_eq_of (ZMod p)]
      -- on the summand `n`: base change sends `b i ⊗ x` to the push of `x` along `x ↦ b i ⊗ x`,
      -- and pushing along a map is composing with its class (`of_comp_homClass`)
      simp only [lof_eq_of, of_comp_homClass, ← AddEquiv.coe_toAddMonoidHom, coe_congrAddEquiv,
        DirectSum.map_of]
      rfl
    -- `E` is `E₀` with its source written as the source of the Leray–Hirsch map of `D`.
    let E : (D.Index →₀ TotalH (freeAb X) Theory.locallyConstant.functor) ≃+ _ := E₀
    -- Under `E` the Leray–Hirsch map is restriction along `genericTestOver Ω` followed by
    -- `c.coeffHom`.
    have key : (lerayHirsch D.comparison (freeAb X)).toAddMonoidHom =
        (mapThenComp (restrictAlong (genericTestOver Ω)) (.homClass c.coeffHom)).comp
          E.toAddMonoidHom := by
      ext i n x : 3
      refine (lerayHirsch_single ..).trans (.trans ?_ congr(mapThenComp _ _ $(hE i n x)).symm)
      -- unfold `mapThenComp`: restrict the composite along `genericTestOver Ω`, then compose
      simp only [mapThenComp, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.flip_apply]
      rw [TotalH.map_comp_assoc, TotalH.map_comp_assoc]
      simp_rw [map_homClass, ← homClass_comp]
      rfl
    -- Pull-back along the isomorphism `u` is bijective, and so is `E`.
    have : IsIso (freeAbMap u.hom) := Functor.map_isIso freeAb u.hom
    exact (Iff.of_eq (congrArg (fun f : _ →+ _ ↦ Bijective f) key)).trans <|
      (E.bijective.of_comp_iff _).trans <|
        ((IsCohomEquiv.of_isIso
          (freeAbMap u.hom)).bijective_pullbackAlong.of_comp_iff' _).symm.trans
          bijective_totalH_iff_isBijective
  -- The point satisfies `D.IsFiniteLerayHirsch` (Leray–Hirsch and finiteness): `OFlat` and `Ω` are
  -- both initial, `ac` holds at `OFlat`, and the values of the two coefficients agree because the
  -- locally constant functions on `Spec Ω` are constant.
  have h_point : D.IsFiniteLerayHirsch (freeAb (reprBy (.ofSelf Ω))) := by
    let u : tilt ⋙ reprBy (.of OFlat OFlat) ≅ c.functor ⋙ reprBy (.ofSelf Ω) :=
      tiltReprIsoGenericRepr Ω
    have h_bij : c.IsBijective (freeAbMap u.hom) := by
      refine .transfer (ac _)
        (bijective_of_isIso ((moduleCoeff _).map (oFlatLocConstOfSelfIso Ω).hom)) fun A y x ↦ ?_
      -- Both sides are induced by a map of algebras out of the initial `OFlat`.
      let F := moduleCoeff (tensorCoeff M)
      have h_hom : y.down = (oFlatLocConstOfSelfIso Ω).hom ≫
          (TestOver.toTest Ω ⋙ oFlatLocConst).map (u.hom.app A y).down ≫ primitiveMap.app A :=
        CommAlgCat.isInitialSelf.hom_ext _ _
      exact (congrArg (fun f ↦ F.map f x) h_hom).trans
        ((F.map_comp_apply _ _ x).trans (F.map_comp_apply _ _ _))
    -- The cohomology of the point with coefficients `L` consists of the constants `ZMod p`.
    exact ⟨(lh_iff (hasFlatBaseChange_freeAb_reprBy _) u).2 h_bij,
      .of_surjective _ ((sectionEquiv ..).surjective.comp
        (bijective_const_of_isDomain (B := .of Ω)).2)⟩
  -- So on the charted `Y` the Leray–Hirsch map is bijective and the mod `p` cohomology is finite.
  obtain ⟨h_lh, h_fin⟩ :=
    D.mem_of_isClosedClass_of_isCharting D.isClosedClass_isFiniteLerayHirsch
      D.isFiniteLerayHirsch_freeAb_iff_relFreeAb
      (IsCharted.exists_isCharting (Y := Y) (k := Ω)) h_point
  -- So far `Y` lives on tests over `Ω`, where it has flat base change. Restriction from all
  -- tests to these is bijective on cohomology (`isBijective_algToBaseChange`), which carries over
  -- each claim.
  refine ⟨hasFlatBaseChange_geomPoints Ω Y, fun n ↦ ?_, fun he ↦ ?_⟩
  · -- Degree `n` embeds in the total cohomology, which is finite.
    have h_fin_n := h_fin.of_injective _ (of_injective n)
    exact (isBijective_algToBaseChange ..).finite_iff.2 h_fin_n
  · -- `toGenericPoints` is bijective by the valuative criterion.
    exact (isBijective_algToBaseChange Ω Y _).trans
      ((lh_iff (hasFlatBaseChange_algPointsOf Ω Y)
        (isoOfAppBijective (toGenericPoints Ω he Y) (·.bijective_generic_points))).1 h_lh)
      (freeAb.hom_ext fun _ _ ↦ rfl)

end New.Variety

/-! ## Finite generation of p-adic cohomology and continuity of the Galois action -/

section FiniteCohomology

open CategoryTheory ModuleCat.Algebra

namespace New.Variety

variable {p : ℕ} [ThePrime p]
  {R : CommRingCat} [Algebra R Ω]
  {Y : Over (AlgebraicGeometry.Spec R)} [IsCharted (R := R) Y Ω] [AlgebraicGeometry.IsProper Y.hom]

/-- For `Y` proper over `R` and charted over `Ω`, the cohomology `Hⁿ(Y_Ω, ℤ_p)`, computed on test
rings, is a finitely generated `ℤ_p`-module. -/
lemma finite_padic_cohomology (n : ℕ) :
    Module.Finite ℤ_[p] (H (freeAb (testIncl ⋙ geomPoints R Ω Y)) ellAdicCoeff n) := by
  -- The primitive comparison, after a choice of embedding of `Ω` in `ℂ_p`, gives the finiteness of
  -- `Hⁿ(Y_Ω, 𝔽_p)` (its acyclicity hypothesis is supplied for the zero module); finiteness
  -- modulo `p` lifts to `ℤ_p` by `finite_H_ellAdicCoeff`.
  have : Module.IsTorsionFree ℚ ℂ_[p] := DivisionSemiring.to_moduleIsTorsionFree
  let alg_Ω : Algebra Ω ℂ_[p] := (IsAlgClosed.lift : Ω →ₐ[ℚ] ℂ_[p]).toAlgebra
  obtain ⟨-, h_finite_mod_p, -⟩ :=
    finite_and_primitive_comparison Ω (isAcyclicOnPerfect_almostCoeff (N := Unit) (by simp)) Y
  exact finite_H_ellAdicCoeff (h_finite_mod_p n)

/-- For `Y` proper over `R` and charted over `Ω`, the `p`-adic cohomology `ℚ_p ⊗ Hⁿ(Y_Ω, ℤ_p)` is
finite-dimensional over `ℚ_p`. -/
instance {n : ℕ} : Module.Finite ℚ_[p] (ellAdicCohom R Ω n ⟨Y⟩) :=
  (finite_padic_cohomology n).base_change ℤ_[p] ℚ_[p] _

/-- Let `Y` be proper over `R` and charted over `Ω`, and `Gal(Ω/K)` the profinite Galois group of
`Ω` over a field `K`, acting `R`-linearly. For a class `x` in `Vⁿ(Y) = ℚ_p ⊗ Hⁿ(Y_Ω, ℤ_p)` and a
`ℚ_p`-linear map `l : Vⁿ(Y) → Q̄_p ^ N`, the map `g ↦ l (g x)` is continuous. -/
lemma ellAdicCohom.continuous_galoisAction (n : ℕ) (K : Type*) [Field K] [Algebra K Ω] [Algebra R K]
    [IsScalarTower R K Ω] [G : IsProGalois Gal(Ω/K) K Ω]
    (x : (ellAdicCohom R Ω n).obj (Opposite.op Y)) {N : ℕ}
    (l : ellAdicCohom R Ω n ⟨Y⟩ →ₗ[ℚ_[p]] Fin N → PadicAlgCl p) :
    Continuous fun g : Gal(Ω/K) ↦ l (galoisAction R Ω Gal(Ω/K) Y n g x) := by
  -- Reduce to a pure tensor `a ⊗ t` and to continuity at `g₀`: given a neighbourhood `U` of `0`,
  -- find an open subgroup of `g` with `L (g t - t) ∈ U`, where `L y = l (g₀ (a ⊗ y))`. The image of
  -- `L` is compact, so `p ^ k` maps it into `U`; and `g t - t` is divisible by `p ^ k` as soon as
  -- `g` fixes the finitely many elements of `Ω` over which `t` modulo `p ^ k` is defined.
  let M := H (freeAb (testIncl ⋙ geomPoints R Ω Y)) ellAdicCoeff n
  obtain ⟨S, hx⟩ : ∃ S : Finset (ℚ_[p] × M), x = ∑ i ∈ S, i.1 ⊗ₜ[ℤ_[p]] i.2 := x.exists_finset
  -- `l` after the action of `g` is additive, so the map is a sum of maps `g ↦ l (g (a ⊗ t))`.
  let toCohom : TensorProduct ℤ_[p] ℚ_[p] M →ₗ[ℚ_[p]] ellAdicCohom R Ω n ⟨Y⟩ := LinearMap.id
  have hx' : x = ∑ i ∈ S, toCohom (i.1 ⊗ₜ[ℤ_[p]] i.2) :=
    (congrArg toCohom hx).trans (map_sum toCohom _ S)
  rw [hx']
  simp_rw [map_sum]
  refine continuous_finsetSum S fun ⟨a, t⟩ _ ↦ continuous_iff_continuousAt.2 fun g₀ ↦ ?_
  refine tendsto_sub_nhds_zero_iff.1 fun U hU ↦ (map_mul_left_nhds_one _).ge (Filter.mem_map.2 ?_)
  let L : M →ₗ[ℤ_[p]] Fin N → PadicAlgCl p :=
    (l ∘ₗ galoisAction R Ω Gal(Ω/K) Y n g₀).restrictScalars ℤ_[p] ∘ₗ
      TensorProduct.mk ℤ_[p] ℚ_[p] M a
  -- `M` is finitely generated, so `L M` is compact, hence bounded.
  have h_bounded : Bornology.IsVonNBounded ℚ_[p] (Submodule.map L ⊤ : Set (Fin N → PadicAlgCl p)) :=
    (Submodule.isCompact_of_fg (.map L (finite_padic_cohomology n).fg_top)).isVonNBounded ℚ_[p]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Set.MapsTo ((p : ℚ_[p]) ^ k • ·) (Submodule.map L ⊤ : Set _) U :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one).eventually
      ((h_bounded hU).eventually_nhds_zero (mem_of_mem_nhds hU))).exists
  -- `q` is reduction modulo `p ^ k`: the sequence `0 → ℤ_p → ℤ_p → W_k(𝔽_p) → 0` is exact.
  obtain ⟨q, hq⟩ := exists_ellAdicCoeff_modShortExact_pow (ℓ := p) k
  -- The cohomology of `Y_Ω` with these coefficients is the colimit over the subalgebras generated
  -- by finite subsets `s` of `Ω`, so `t` modulo `p ^ k` is the pullback of a class `z` at some
  -- stage `s`. Take `g` in the intersection of the stabilisers of the elements of `s`.
  obtain ⟨s, z, hz⟩ :=
    ((isProperOver_pointsToBase Y.hom).isCohomContinuous.isFilteredColimit_adjoin _ Ω (𝟙 _) n).2
      (t.push _ q n)
  filter_upwards [s.eventually_all.mpr fun b _ ↦ (G.isOpen_stabilizer b).mem_nhds rfl] with g hg
  simp only [Set.mem_preimage, map_mul]
  -- `gt` is the integral class `g t`: the pullback of `t` along the automorphism `g` of `Y_Ω`.
  let g_hom : Under.mk (CommRingCat.ofHom (algebraMap R Ω)) ⟶
      Under.mk (CommRingCat.ofHom (algebraMap R Ω)) :=
    Under.homMk (CommRingCat.ofHom (MulSemiringAction.toAlgAut Gal(Ω/K) R Ω g : Ω →+* Ω))
      (CommRingCat.hom_ext (MulSemiringAction.toAlgAut Gal(Ω/K) R Ω g).toAlgHom.comp_algebraMap)
  let gt : M := H.map _ (freeAb.map (mapOnTests
    (baseChangeTransition (pointsToBase Y.hom) g_hom.right g_hom.w))) n t
  change L gt - L t ∈ U
  -- Pullback commutes with reduction, and `g` is the identity on the subalgebra generated by `s`.
  have h_red : H.push _ q n (gt - t) = 0 := by
    let F := (baseChangeFunctor (pointsToBase Y.hom) ⋙ onTests).rightOp ⋙
      cohomologyFunctor (locConstCoeff ⟨TruncatedWittVector p k (ZMod p)⟩) n ⟨freeAb⟩
    let ι_s := (Under.map (𝟙 R)).map (Algebra.adjoin R (s : Set Ω)).val.toUnder
    let g_hom' := (Under.map (𝟙 R)).map g_hom
    have h_fix : ι_s ≫ g_hom' = ι_s := by
      ext b
      exact (g.toAlgHom.restrictScalars R).adjoin_le_equalizer 1 hg b.property
    dsimp only [Functor.mapCocone_ι_app] at hz
    have h1 : H.push _ q n gt = F.map g_hom' (F.map ι_s z) :=
      (H.map_push _ q t).symm.trans (congrArg (F.map g_hom') hz.symm)
    have h2 : F.map g_hom' (F.map ι_s z) = F.map ι_s z := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, h_fix]
    rw [map_sub, sub_eq_zero]
    exact (h1.trans h2).trans hz
  obtain ⟨y, hy⟩ : ∃ y : M, ((p ^ k : ℕ) : ℤ_[p]) • y = gt - t :=
    hq.exists_smul_eq_of_push_eq_zero _ h_red
  -- apply `L` to `hy`; the scalar `p ^ k` of `ℤ_p` and that of `ℚ_p` both act as `p ^ k • ·`
  have h_eq : L gt - L t = (p : ℚ_[p]) ^ k • L y := by
    rw [← map_sub, ← hy, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [h_eq]
  exact hk (Submodule.mem_map_of_mem Submodule.mem_top)

end New.Variety

end FiniteCohomology
end
end

section
/-!
# The primitive comparison with period coefficients

The primitive comparison, passed from coefficients modulo `p` to period coefficients. For a `p`-adic
test `c` with ring `R`, let `L` be the ring of locally constant `𝔽_p`-valued functions on
`Spec R[1/p]` (for a test ring `A`, the same ring on `Spec A`; a `p`-adic test gives `A = R[1/p]`).
`New.Variety.primitiveMap` is the natural map of `O♭`-algebras from `O♭ ⊗ L` to the tilt `R♭`; on
`1 ⊗ L` it restricts to `locConstToTilt : L → R♭`, `ℓ ↦ primitiveMap (1 ⊗ ℓ)`. Let `S` be an
`A_inf`-algebra and `K` an `S`-algebra, and let `Ψ` be isomorphic (by `θ`) to the period
coefficients `c ↦ K ⊗ (S ⊗ W(R♭))^`, where `^` is `p`-adic completion.

* `New.Variety.primitivePeriodMap`: the natural map `K ⊗ W(L) → Ψ` induced by
  `New.Variety.primitiveMap`.
* `New.Variety.primitivePeriodMap_isBijective`: this map is bijective on cohomology under several
  conditions. `S` and `K` form a period ring pair, and `K` is flat over `S`. `N` and `N'` have flat
  base change. The cohomology of `N` with coefficients `ℤ_p` is finite over `ℤ_[p]`. The map that
  `New.Variety.primitiveMap` induces on the coefficients `b ↦ b ⊗ (O♭ ⊗ S) ⊗ 𝔪` is bijective on
  cohomology.
* `New.Variety.exists_primitive_period_comparison`: the same, in existential form.

Notions from other files:
* `New.Variety.CoeffCompBijective β α F`: the comparison of cohomology groups along `β` and `α` is
  bijective in every degree for the coefficients `F`.
* `New.Variety.HasFlatBaseChange N`: the cohomology of `N` commutes with flat extension of the
  coefficients.
* `New.Variety.IsPeriodRingPair`: `S` is `p`-torsion-free and `p`-complete, `p` divides the image of
  `ξ` in `S`, and `τ` is a unit in `K`.
* `New.Variety.almostCoeff`: for an `O♭`-module `N`, the functor `b ↦ b ⊗ N ⊗ 𝔪` on `O♭`-algebras,
  `𝔪` the maximal ideal of `O♭`.
* `New.Variety.oFlatLocConst`: the functor from test rings to `O♭`-algebras sending `A` to
  `O♭ ⊗_{𝔽_p} LC(A)`, `LC(A)` the locally constant functions `Spec A → 𝔽_p`.
* `New.Variety.ellAdicCoeff`: the coefficient `ℤ_ℓ` (here `ℓ = p`): a test ring `A` goes to the Witt
  vectors of the ring of locally constant functions `Spec A → 𝔽_ℓ`.

## Relation to the literature

Known; see `Lib.PadicComparison.HodgeTate.PeriodMap` for sources.
-/

@[expose] public section

namespace New.Variety

open CategoryTheory TensorProduct Functor Period PadicTest AlgebraTensorModule WittVector PadicInt
  ZMod Comparison

variable {p : ℕ} [ThePrime p] {S : Type} [CommRing S] [Algebra Ainf S] [Algebra ℤ_[p] S]
  [IsScalarTower ℤ_[p] Ainf S] (b : Type*) [CommRing b] [Algebra (ZMod p) b]
  (K : Type) [CommRing K] [Algebra S K] [Module.Flat S K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] S K] {Ψ : PadicTest ⥤ ModuleCat K}
  (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ)

/-- An `𝔽_p`-algebra `b` is a `ℤ_[p]`-algebra through reduction modulo `p`. -/
noncomputable local instance : Algebra ℤ_[p] b := .compHom _ (constantCoeff.comp (fromPadicInt p))

local instance : IsScalarTower ℤ_[p] (ZMod p) b := .of_compHom ..

/-- Let `q` and `π` be additive maps on `X` with kernel the multiples of `m`, and `q` onto. If
`π ∘ j` is a reduction modulo `m` (onto, with kernel the multiples of `m`), then so is `q ∘ j`. -/
lemma IsReductionMod.comp_of_exact_of_comp {W X Y Z : Type*} [SMul ℕ W] [AddCommGroup X]
    [AddCommGroup Y] [AddCommGroup Z] {m : ℕ} {q : X →+ Y} {π : X →+ Z} {j : W → X}
    (hq : IsReductionMod m q) (hπ : Function.Exact (fun x : X ↦ m • x) π)
    (hj : IsReductionMod m (π ∘ j)) :
    IsReductionMod m (q ∘ j) := by
  obtain ⟨hq_surj, hq_ker⟩ := hq
  obtain ⟨hj_surj, hj_ker⟩ := hj
  -- `q` and `π` have the same kernel, the multiples of `m`.
  have h_ker (x : X) : q x = 0 ↔ π x = 0 := (hq_ker x).trans (hπ x).symm
  refine ⟨fun y ↦ ?_, fun w ↦ (h_ker (j w)).trans (hj_ker w)⟩
  -- Write `y = q x`. Some `w` has `π (j w) = π x`, so `q` kills `j w - x` too.
  obtain ⟨x, rfl⟩ := hq_surj y
  obtain ⟨w, hw : π (j w) = π x⟩ := hj_surj (π x)
  have h_diff : q (j w - x) = 0 := (h_ker _).mpr (by simp [hw])
  exact ⟨w, by simpa [sub_eq_zero] using h_diff⟩

variable (p) in
/-- The functor from test rings to `ℤ_[p]`-algebras sending `A` to `W(L)`, where `L` is the ring
of locally constant functions `Spec A → 𝔽_p`. -/
noncomputable abbrev wittLocConst : TestRing ⥤ CommAlg ℤ_[p] :=
  (testIncl ⋙ locConstAlg) ⋙ wittFunctor ℤ_[p]

variable (S) in
/-- For a test ring `A`, with `L` the ring of locally constant functions `Spec A → 𝔽_p`, the
`ℤ_[p]`-algebra map `W(L) → W(O♭ ⊗ L) → S ⊗_{A_inf} W(O♭ ⊗ L)`, `w ↦ 1 ⊗ W(1 ⊗ –)(w)`. -/
noncomputable def wittIncludeRight (A : TestRing) :
    (wittLocConst p).obj A →ₐ[ℤ_[p]]
      (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S ⋙ restrictAlg ℤ_[p] S).obj A := by
  open Algebra.TensorProduct in
    refine ⟨includeRight.toRingHom.comp (map includeRight.toRingHom), fun z ↦ ?_⟩
    -- Compare Witt coordinates, which come from `ZMod p`.
    have h_coord :
        WittVector.map includeRight.toRingHom (algebraMap ℤ_[p] ((wittLocConst p).obj A) z) =
          algebraMap Ainf ((oFlatLocConst ⋙ wittFunctor).obj A) (algebraMap ℤ_[p] Ainf z) :=
      WittVector.ext fun _ ↦ (includeRight.commutes _).trans (congrArg _ (cast_id p _))
    refine .trans (congrArg (tmul _ 1) h_coord) ?_
    -- `z` reaches `S` through `A_inf`.
    exact (includeRight.commutes _).trans
      (congrArg (fun s : S ↦ s ⊗ₜ 1) (IsScalarTower.algebraMap_apply ℤ_[p] Ainf S z)).symm

variable (S) in
/-- The `S`-algebra map `S ⊗_{ℤ_p} W(L) → S ⊗_{A_inf} W(O♭ ⊗ L)`, natural in the test ring: the
extension of `wittIncludeRight` to `S`-algebras, its transpose under base change to `S`. -/
noncomputable def wittLocConstBaseChange :
    wittLocConst p ⋙ algBaseChange S ⟶ oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S :=
  (baseChangeTranspose (wittLocConst p) (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S)).symm
    (.mk fun A ↦ ConcreteCategory.ofHom (wittIncludeRight S A))

variable (S) in
/-- The map `S ⊗_{ℤ_p} W(L) → (S ⊗_{A_inf} W(O♭ ⊗ L))^` of `S`-modules, where `^` is the `p`-adic
completion: `wittLocConstBaseChange` followed by the map to the completion. -/
noncomputable def wittLocConstToPeriodAlg :
    asModules (wittLocConst p) ⋙ tensorWith S S ⟶ asModules (oFlatLocConst ⋙ periodAlg S) :=
  whiskerRight
    (wittLocConstBaseChange S ≫
      whiskerLeft (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S) (algCompletion.of S p))
    (asModules (𝟭 (CommAlg S)))

variable (p S) in
/-- The isomorphism `K ⊗_{ℤ_p} W(L) ≅ K ⊗_S (S ⊗_{ℤ_p} W(L))`, natural in the test ring. -/
noncomputable def wittLocConstCancelIso :
    asModules (wittLocConst p) ⋙ tensorWith K K ≅
      (asModules (wittLocConst p) ⋙ tensorWith S S) ⋙ tensorWith K K :=
  NatIso.ofComponents
    (fun A ↦ (cancelBaseChange ℤ_[p] S K K ((wittLocConst p).obj A)).symm.toModuleIso)
    fun _ ↦ ModuleCat.hom_ext (tmul_ext fun _ _ ↦ rfl)

variable (S) in
/-- The image `1 ⊗ w` of a Witt vector `w ∈ W(B)` in the `p`-adic completion of `S ⊗ W(B)`. -/
noncomputable abbrev wittToPeriodAlg (B : CommAlg OFlat) (w : WittVector p B) :
    (periodAlg S).obj B :=
  AdicCompletion.of (Ideal.span {(p : S ⊗[Ainf] wittFunctor.obj B)}) (S ⊗[Ainf] wittFunctor.obj B)
    (1 ⊗ₜ w)

/-- Let `θ` be an isomorphism from the functor `c ↦ K ⊗ (S ⊗ W(R♭))^` to `Ψ`, where `R` is the ring
of the test `c` and `^` is the `p`-adic completion. This is the natural map from `K ⊗ W(L)` to `Ψ`,
where `L` is the ring of locally constant `𝔽_p`-valued functions on `Spec R[1/p]`. It is the
composite `K ⊗ W(L) ≅ K ⊗ (S ⊗ W(L)) → K ⊗ (S ⊗ W(O♭ ⊗ L))^ → K ⊗ (S ⊗ W(R♭))^ ≅ Ψ c`, the
third map induced by `primitiveMap`. -/
noncomputable def primitivePeriodMap :
    genericTest ⋙ asModules (wittLocConst p) ⋙ tensorWith K K ⟶ Ψ :=
  whiskerLeft genericTest
      ((wittLocConstCancelIso p S K).hom ≫
        whiskerRight (wittLocConstToPeriodAlg S) (tensorWith K K)) ≫
    whiskerRight primitiveMap (asModules (periodAlg S) ⋙ tensorWith K K) ≫ θ.hom

omit [Module.Flat S K] in
/-- `primitivePeriodMap K θ` sends `a ⊗ x` to `θ (a ⊗ 1 ⊗ x')`, where `x'` is the image of `x`
under the map of Witt vectors induced by `locConstToTilt`, and `1 ⊗ x'` is taken in the completion
(`wittToPeriodAlg`). -/
lemma primitivePeriodMap_app_tmul (c : PadicTest) (a : K)
    (x : (wittLocConst p).obj (genericTest.obj c)) :
    (primitivePeriodMap K θ).app c (a ⊗ₜ x) =
      θ.hom.app c (a ⊗ₜ wittToPeriodAlg S (tilt.obj c)
        (WittVector.map (locConstToTilt.app c).hom.toRingHom x)) := by
  refine congrArg (fun y ↦ θ.hom.app c (a ⊗ₜ y)) ((adicMap_algebraMap ..).trans (congrArg _ ?_))
  exact congrArg₂ (tmul _) (mul_one 1) (ext fun _ ↦ one_smul OFlat _)

/-- For every test ring `A`, the `O♭`-algebra `O♭ ⊗_{𝔽_p} LC(A)` is perfect, and `pFlat` (the class
of `ξ` modulo `p`) is a non-zero-divisor on it. -/
lemma isPerfectTorsionFree_oFlatLocConst (A : TestRing) :
    IsPerfectTorsionFree (oFlatLocConst.obj A) := by
  -- A tensor product over `𝔽_p` of the perfect rings `O♭` and `LC(A)` is perfect.
  refine ⟨perfectRing_tensor (ZMod.natCast_self p) ⟨.of _ OFlat, inferInstance⟩
    ⟨_, perfectRing_locConstAlg _⟩, ?_⟩
  -- `O♭ ⊗ LC(A)` is torsion-free over the domain `O♭`, and `pFlat ≠ 0`.
  exact .of_ne_zero (M := _ ⊗ _) pFlat_ne_zero

/-- Let `S` be an `A_inf`-algebra, `A` a test ring and `L` the ring of locally constant functions
`Spec A → 𝔽_p`. The map `S ⊗ W(L) → S ⊗ W(O♭ ⊗ L)` (`wittLocConstBaseChange`) is bijective
modulo `p`: followed by a reduction `q` modulo `p` of the target (`IsReductionMod p q`: `q` onto,
with kernel the multiples of `p`), it is a reduction modulo `p` of the source. -/
lemma IsReductionMod.comp_wittLocConstBaseChange {p : ℕ} [ThePrime p] {S : Type} [CommRing S]
    [Algebra Ainf S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (A : TestRing)
    {Y : Type} [AddCommGroup Y]
    {q : (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S).obj A →+ Y} (hq : IsReductionMod p q) :
    IsReductionMod p (q ∘ (wittLocConstBaseChange S).app A) := by
  -- The zeroth Witt coordinates reduce the source to `S ⊗ B` and the target to `S ⊗ (O♭ ⊗ B)`,
  -- where `B` is the ring of locally constant functions; the isomorphism `E` identifies the two.
  have h_perfect : PerfectRing (oFlatLocConst.obj A) p :=
    (isPerfectTorsionFree_oFlatLocConst A).1
  let B : CommAlg (ZMod p) := locConstAlg.obj A.obj
  -- `g` takes the zeroth Witt coordinate.
  let g : (wittLocConst p).obj A →ₐ[ℤ_[p]] B :=
    ⟨constantCoeff, fun _ ↦ congrArg (algebraMap _ _) (cast_id p _)⟩
  let f : Ainf →ₗ[Ainf] OFlat := Algebra.linearMap Ainf OFlat
  have h_tower : IsScalarTower ℤ_[p] Ainf OFlat := .of_compHom ..
  have h_compatible : CompatibleSMul ℤ_[p] (ZMod p) OFlat B :=
    .of_algebraMap_surjective _ _ (ringHom_surjective _)
  have h_source : IsReductionMod p (g.toLinearMap.lTensor S) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree (ZMod p) _).left.lTensor
  have h_target : IsReductionMod p ((wittConstCoeff (oFlatLocConst.obj A)).lTensor S) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat _).left.lTensor
  -- `A_inf ⊗ B = O♭ ⊗ B` over `ℤ_[p]`, because `p` kills `B` and `f` is reduction modulo `p`.
  have hf_bij : Function.Bijective (rTensor ℤ_[p] B f) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat _).left.bijective_rTensor
      (f.restrictScalars ℤ_[p])
      (ZModModule.char_nsmul_eq_zero p)
  let E : S ⊗[ℤ_[p]] B ≃ₗ[S] S ⊗[Ainf] (OFlat ⊗[ZMod p] B) :=
    (cancelBaseChange ℤ_[p] Ainf S S B).symm ≪≫ₗ congr (.refl S S)
      (.ofBijective (rTensor ℤ_[p] B f) hf_bij ≪≫ₗ
        equivOfCompatibleSMul (ZMod p) ℤ_[p] Ainf OFlat B)
  -- The map followed by the reduction of the target is the reduction of the source followed by `E`.
  have h_square :
      (wittConstCoeff (oFlatLocConst.obj A)).baseChange S ∘ₗ
          ((wittLocConstBaseChange S).app A).hom.toLinearMap =
        E.toLinearMap ∘ₗ g.toLinearMap.baseChange S := by
    refine ext fun a x ↦ ?_
    -- On `a ⊗ x` both sides are pure tensors `s ⊗ (t ⊗ u)`; compare the factors.
    change _ ⊗ₜ (_ ⊗ₜ _) = _ ⊗ₜ (_ ⊗ₜ _)
    congr 1
    · simp
    · congr 1
      simp [f]
  -- `baseChange S` and `lTensor S` are the same function.
  have h_comp :
      (wittConstCoeff (oFlatLocConst.obj A)).lTensor S ∘ (wittLocConstBaseChange S).app A =
        E ∘ g.toLinearMap.lTensor S :=
    congrArg DFunLike.coe h_square
  exact hq.comp_of_exact_of_comp
    (π := ((wittConstCoeff (oFlatLocConst.obj A)).lTensor S).toAddMonoidHom) h_target.right
    (by
      rw [LinearMap.toAddMonoidHom_coe, h_comp]
      exact ⟨E.surjective.comp h_source.left, fun x ↦ E.map_eq_zero_iff.trans (h_source.right x)⟩)

/-- The primitive comparison with period coefficients. Let `p` be a prime, `(S, K)` a period ring
pair (`S` an `A_inf`-algebra, `K` a flat `S`-algebra), `θ` an isomorphism from
`c ↦ K ⊗ (S ⊗ W(R♭))^` to `Ψ : PadicTest ⥤ ModuleCat K`, and `α : N' ⟶ genericTest ⋙ N` the map that
compares cohomology over `p`-adic tests with cohomology over test rings. Suppose that `N` and `N'`
have flat base change, that each `H N ellAdicCoeff n` (the `n`-th cohomology of `N` with
coefficients `ℤ_p`) is finite over `ℤ_[p]`, and that `primitiveMap` is bijective on cohomology along
`α` for the coefficients `almostCoeff (O♭ ⊗ S)` (`CoeffCompBijective`). Then
`primitivePeriodMap K θ`, viewed by `ofModuleHom genericTest` as a map of coefficients, is bijective
on cohomology along `α`, in every degree. -/
lemma primitivePeriodMap_isBijective {p : ℕ} [ThePrime p] {S : Type} [CommRing S] [Algebra Ainf S]
    [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (K : Type) [CommRing K] [Algebra S K]
    [Module.Flat S K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] S K] {Ψ : PadicTest ⥤ ModuleCat K}
    (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) (hS : IsPeriodRingPair p S K)
    {N : AbFunctor TestRing} {N' : AbFunctor PadicTest} {α : N' ⟶ genericTest ⋙ N}
    (hN : HasFlatBaseChange N) (hN' : HasFlatBaseChange N')
    (h_finite : ∀ n : ℕ, Module.Finite ℤ_[p] (H N ellAdicCoeff n))
    (h_primitive : CoeffCompBijective primitiveMap α (almostCoeff (OFlat ⊗[Ainf] S))) :
    (ofModuleHom genericTest (primitivePeriodMap K θ)).IsBijective α := by
  -- The map is the composite of the isomorphism `wittLocConstCancelIso`, of
  -- `wittLocConstToPeriodAlg`, of the map induced by `primitiveMap`, and of `θ`. The second is
  -- bijective on cohomology because it is bijective modulo `p` and the cohomology is finite, the
  -- third by the hypothesis on `primitiveMap`.
  -- `S` is torsion-free over `ℤ_[p]`: a nonzero `t = u p ^ v` divides a power of `p`.
  have h_dvd_pow {t : ℤ_[p]} (ht : t ≠ 0) : t ∣ (p : ℤ_[p]) ^ t.valuation :=
    (unitCoeff_spec ht).dvd.trans (Units.mul_left_dvd.mpr dvd_rfl)
  have h_torsionFree : Module.IsTorsionFree ℤ_[p] S :=
    isTorsionFree_of_dvd_pow hS.isSMulRegular_natCast fun ht ↦ ⟨_, h_dvd_pow ht⟩
  have h_padic : IsCompleteTorsionFree ℤ_[p] :=
    { regular := .of_ne_zero NeZero.out
      complete := by
        rw [← maximalIdeal_eq_span_p]
        infer_instance }
  have h_witt (A : TestRing) : IsCompleteTorsionFree ((wittLocConst p).obj A) :=
    isCompleteTorsionFree_wittVector (ZMod p) (locConstAlg.obj A.obj)
  have h_period (A : TestRing) : IsCompleteTorsionFree ((oFlatLocConst ⋙ periodAlg S).obj A) :=
    isCompleteTorsionFree_completion
      (isSMulRegular_tensor_witt hS.regular (isPerfectTorsionFree_oFlatLocConst A))
  have h_mod (A : TestRing) {Y : Type} [AddCommGroup Y]
      (q : (asModules (oFlatLocConst ⋙ periodAlg S)).obj A →+ Y) (hq : IsReductionMod p q) :
      IsReductionMod p (q ∘ (wittLocConstToPeriodAlg S).app A) :=
    (IsReductionMod.comp_algebraMap hq).comp_wittLocConstBaseChange A
  -- The cohomology with coefficients `ℤ_p` has finite rank, by `h_finite`.
  have h_rank (n : ℕ) : Module.rank ℤ_[p] (H N ellAdicCoeff n) < Cardinal.aleph0 :=
    have : Module.Finite ℤ_[p] (H N ellAdicCoeff n) := h_finite n
    Module.rank_lt_aleph0 ℤ_[p] (H N ellAdicCoeff n)
  have h_completion :
      (ofModuleHom (Φ := asModules (wittLocConst p) ⋙ tensorWith S S) (𝟭 TestRing)
        (wittLocConstToPeriodAlg S)).IsBijective (𝟙 N) :=
    hN.isBijective_of_isReductionMod (Θ := wittLocConst p) h_padic hS.isCompleteTorsionFree h_witt
      irreducible_p (X := oFlatLocConst ⋙ periodAlg S) (wittLocConstToPeriodAlg S)
      (fun n _ ↦ h_rank n) h_period h_mod
  have h_completion_tensor :
      CoeffCompBijective (Ψ := asModules (wittLocConst p) ⋙ tensorWith S S) (φ := 𝟭 TestRing)
        (wittLocConstToPeriodAlg S) (𝟙 N) (tensorWith K K) :=
    (h_completion.baseChangeMap_bijective_iff hN).mp
      (hN S K K (asModules (oFlatLocConst ⋙ periodAlg S)))
  have h_primitive_tensor :
      CoeffCompBijective primitiveMap α (asModules (periodAlg S) ⋙ tensorWith K K) :=
    h_primitive.periodAlg_of_almostCoeff hN hS (fun G ↦ hN' S K K (tilt ⋙ G))
      isPerfectTorsionFree_oFlatLocConst isPerfectTorsionFree_tilt
  have h_composite :
      (ofModuleHom (Φ := (asModules (wittLocConst p) ⋙ tensorWith S S) ⋙ tensorWith K K) genericTest
        (whiskerLeft genericTest (whiskerRight (wittLocConstToPeriodAlg S) (tensorWith K K)) ≫
          whiskerRight primitiveMap (asModules (periodAlg S) ⋙ tensorWith K K))).IsBijective α :=
    -- `(… :)`: the composite of the two comparisons is this one only after unfolding.
    (h_completion_tensor.trans h_primitive_tensor rfl :)
  -- The isomorphisms `wittLocConstCancelIso` and `θ` do not affect bijectivity; the square
  -- commutes by the definition of `primitivePeriodMap`.
  refine (isBijective_iff_of_coeff_iso
    (whiskerRight (wittLocConstCancelIso p S K).hom (moduleCoeff (𝟭 (ModuleCat K))))
    (isoWhiskerRight θ (moduleCoeff (𝟭 (ModuleCat K)))).inv ?_).mpr h_composite
  exact (isoWhiskerRight θ (moduleCoeff (𝟭 (ModuleCat K)))).eq_comp_inv.mpr rfl

/-- The primitive comparison in existential form. For a period ring pair `(S, K)` and an isomorphism
`θ` from `c ↦ K ⊗ (S ⊗ W(R♭))^` to `Ψ : PadicTest ⥤ ModuleCat K` (`R` the ring of the test `c`),
there is a natural map `γ : K ⊗ W(L) → Ψ` (`L`: locally constant `Spec R[1/p] → 𝔽_p`) with
`γ (a ⊗ x) = θ (a ⊗ (1 ⊗ x'))`, `x'` the image of `x` under the Witt vector map of `locConstToTilt`;
`γ` is bijective on cohomology under the conditions of `primitivePeriodMap_isBijective`. -/
lemma exists_primitive_period_comparison {p : ℕ} [ThePrime p] {S : Type} [CommRing S]
    [Algebra Ainf S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (K : Type) [CommRing K]
    [Algebra S K] [Module.Flat S K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] S K]
    {Ψ : PadicTest ⥤ ModuleCat K} (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ)
    (hS : IsPeriodRingPair p S K) :
    ∃ γ : genericTest ⋙ asModules (wittLocConst p) ⋙ tensorWith K K ⟶ Ψ,
      (∀ (c : PadicTest) (a : K) (x : (wittLocConst p).obj (genericTest.obj c)),
        γ.app c (a ⊗ₜ x) =
          θ.hom.app c (a ⊗ₜ wittToPeriodAlg S (tilt.obj c)
            (WittVector.map (locConstToTilt.app c).hom.toRingHom x))) ∧
      ∀ {N : AbFunctor TestRing} {N' : AbFunctor PadicTest} {α : N' ⟶ genericTest ⋙ N},
        HasFlatBaseChange N → HasFlatBaseChange N' →
        (∀ n : ℕ, Module.Finite ℤ_[p] (H N ellAdicCoeff n)) →
        CoeffCompBijective primitiveMap α (almostCoeff (OFlat ⊗[Ainf] S)) →
        (ofModuleHom genericTest γ).IsBijective α :=
  ⟨primitivePeriodMap K θ, primitivePeriodMap_app_tmul K θ, primitivePeriodMap_isBijective K θ hS⟩

end New.Variety
end
end

section
/-!
# Galois twists and the weight of the Hodge–Tate map

An element `g` of `Gal(ℚ̄_p/ℚ_p)` twists a p-adic test `c` by precomposing its structure map
`O_C → R` with `g` (`New.Variety.PadicTest.twist`). The twist leaves the rings `R`, `K = R[1/p]` and
`B = W(R♭)[1/p] / (ker θ)²` unchanged. Write `μ = [ε] − 1` and `χ` for the cyclotomic character.
Suppose `g` fixes `E` and `New.Variety.restrictToPairs ξ` is the image under
`New.Variety.hodgeTateMap h` of a Hodge class defined over `E`, and that `χ(g⁻¹)` is the image in
ℚ̄_p of some `t : k`. Then the twist by `g` multiplies `New.Variety.restrictToPairs ξ` by
`χ(g⁻¹)^h`.

## Main definitions and results

* `New.Variety.thickeningOver.mulMu_twist`: the inclusion `ι : K → B` (multiplication by `μ`)
  changes by the cyclotomic character `χ(g⁻¹)` (`New.cyclotomicGp`), as `g⁻¹ μ ≡ χ(g⁻¹) μ` modulo
  `μ²`.
* `New.Variety.HodgeTatePair.galTwist`: the twist on pairs `(c, K^n)` (`New.Variety.HodgeTatePair`).
* `New.Variety.HodgeTatePair.contractionPow_galTwist`: the classes
  `New.Variety.HodgeTatePair.contractionPow` (the `h`-th power of the contraction class, then the
  projection to degree zero) are compatible with the twist.

Notions from other files:
* `New.Variety.PadicTest`: A p-adic test: a non-empty family of cells (`New.Variety.IsCell`) with a
  ring map from O_C to their product R.
* `New.Variety.thickeningOver.mulMu`: The additive map ι: K → B sending θ(x) to the class of μx,
  where μ = [ε] − 1.
* `New.Variety.HodgeTatePair`: A pair (S,M) of a p-adic test S and a free module M of finite rank
  over T = S[1/p]; `New.Variety.HodgeTatePair.pairAlg` sends it to B_{S,M} = B_S ×_T (T ⊕ M).
* `New.Variety.hodgeTateMap`: The map λ_h: restrict a Hodge class along B_{S,M} → T ⊕ M, apply the
  h-th power of the contraction class, and project ⋀M to degree zero.
* `New.Variety.restrictToPairs`: Restriction along B_{S,M} → T, from the cohomology of N(T) on
  p-adic tests S to that of N(B_{S,M}) on pairs. `New.Variety.PairRestrictBijective` says that it is
  bijective in all degrees.

## Relation to the literature

Known; see `Lib.PadicComparison.HodgeTate.PeriodMap` for sources.
-/

@[expose] public section

noncomputable section

namespace New.Variety

/-! ## Twisting p-adic tests, pairs and contraction classes -/

section GaloisTwist

open CategoryTheory Period PadicTest MulSemiringAction AddCommGrpCat TotalH

variable {p : ℕ} {k : Type} [Field k]

/-- The structure map `ℂ_p → R[1/p]` of the `g`-twist of a test `c` is `g` followed by the
structure map of `c`. -/
lemma PadicTest.genericStructureMap_twist [ThePrime p] (g : Gp p) (c : PadicTest) (z : ℂ_[p]) :
    (twist g c).genericStructureMap z = c.genericStructureMap (g • z) := by
  -- Ring maps out of the localization `ℂ_[p]` of `OC` at `p` are determined on `OC`.
  have h_eq : (twist g c).genericStructureMap =
      c.genericStructureMap.comp (toRingHom (Gp p) ℂ_[p] g) := by
    refine IsLocalization.ringHom_ext (.powers (p : OC)) ?_
    ext
    exact (genericStructureMap_coe ..).trans (c.genericStructureMap_coe _).symm
  exact RingHom.congr_fun h_eq z

/-- The lift of the `g`-twist of a test `c` to its thickening is `g` followed by the lift for `c`:
both lifts reduce to the structure map, and the lift is unique (`PadicTest.eq_uniqueLift`). -/
lemma PadicTest.uniqueLift_comp_eq_uniqueLift_twist [ThePrime p] (g : Gp p) (c : PadicTest) :
    c.uniqueLift.comp (g.toAlgHom.restrictScalars ℤ_[p]) = (PadicTest.twist g c).uniqueLift := by
  refine (PadicTest.twist g c).eq_uniqueLift _ fun z ↦ ?_
  rw [c.genericStructureMap_twist, UniformSpace.Completion.algEquiv_smul_coe]
  exact c.thickeningProj_uniqueLift (g z)

/-- For a `p`-adic test `c` with ring `R`, let `ι = mulMu` be the additive map from `K = R[1/p]` to
`B = W(R♭)[1/p]/(ker θ)²` sending `θ(x)` to the class of `μx`, where `μ = [ε] − 1`. For `g ∈ G_p`,
the `g`-twist of `c` has the same `K` and `B`, and `ι` of `c` at `t` equals `ι` of the twist at
`χ(g⁻¹) t`. Here `χ` is the cyclotomic character, and `χ(g⁻¹)` is mapped into `K` by the structure
map `ℂ_p → K`. -/
lemma thickeningOver.mulMu_twist [EmbeddedInQpBar p k] (g : Gp p) (c : PadicTest)
    (t : c.GenericRing) :
    mulMu c t = mulMu (PadicTest.twist g c)
        (c.genericStructureMap (algebraMap ℤ_[p] (PadicAlgCl p) (cyclotomicGp g⁻¹).val) * t) := by
  -- The ring `c.Thickening` is the same for `c` and its twist `c'`, but the structure map is
  -- twisted by `g`. So `μ` for `c` is `g⁻¹ • μ ≡ χ(g⁻¹) μ` for `c'`, modulo `μ²`, which is zero in
  -- `c'.Thickening`.
  let c' : PadicTest := PadicTest.twist g c
  obtain ⟨x, rfl⟩ : ∃ x : c.Thickening, c.thickeningProj x = t := c.thickeningProj_surjective t
  obtain ⟨a, ha⟩ : ∃ a : Ainf, g⁻¹ • mu - (cyclotomicGp g⁻¹ : ℤ_[p]) • mu = mu ^ 2 * a :=
    Lift.mu_sq_dvd_smul_mu_sub g⁻¹
  have h_tw (a : Ainf) :
      algebraMap Ainf c.Thickening (g • a) = algebraMap Ainf c'.Thickening a := by
    refine congrArg (algebraMap (WittVector p c.TiltRing) c.Thickening) ?_
    ext : 1
    exact (congrArg _ (pow_one _)).trans (tiltMap_comp ..).symm
  have h_mu : mu = g • ((cyclotomicGp g⁻¹).val • mu + mu ^ 2 * a) :=
    inv_smul_eq_iff.mp (eq_add_of_sub_eq' ha)
  have h_sq : algebraMap Ainf c'.Thickening mu ^ 2 = 0 :=
    c'.ker_thickeningProj_sq.le (Ideal.pow_mem_pow c'.thetaGeneric_mu 2)
  rw [mulMu_thickeningProj, h_mu, h_tw]
  -- Lift the scalar to the thickening and move it out of `mulMu`.
  let χ := (cyclotomicGp g⁻¹).val
  let z := algebraMap ℤ_[p] (PadicAlgCl p) χ
  let lift : c'.Thickening := c.uniqueLift z
  have h_proj : c'.thickeningProj lift = c.genericStructureMap z :=
    c.thickeningProj_uniqueLift z
  let m : c'.Thickening := mulMu c' (c'.thickeningProj x)
  have h_mu_scalar : mulMu c' (c.genericStructureMap z * c.thickeningProj x) =
      lift * m :=
    (congrArg (fun s : c'.GenericRing ↦ mulMu c' (s * c'.thickeningProj x)) h_proj.symm).trans
      (mulMu_proj_mul c' lift (c'.thickeningProj x))
  refine Eq.trans ?_ h_mu_scalar.symm
  refine Eq.trans ?_ (congrArg (fun y : c'.Thickening ↦ lift * y)
    (mulMu_thickeningProj c' x)).symm
  have h_lift : lift = algebraMap ℤ_[p] c'.Thickening χ :=
    c.uniqueLift.commutes χ
  rw [h_lift]
  simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, h_sq]
  -- what remains is associativity, in rings that agree only up to unfolding the twist
  exact mul_assoc _ _ _

/-- The natural map from `New.Variety.genericCoeff` after the `g`-twist to
`New.Variety.genericCoeff`. It is the identity on each `R[1/p]`. -/
def twistGenericCoeff [ThePrime p] (g : Gp p) :
    PadicTest.twist g ⋙ genericCoeff ⟶ genericCoeff where
  app c := ofHom (AddMonoidHom.id (ULift c.GenericRing))

/-- For `g` in the Galois group of `ℚ̄_p/ℚ_p`, the endofunctor of `New.Variety.HodgeTatePair`
twisting the structure map of the underlying test by `g` and keeping all other data. -/
def HodgeTatePair.galTwist [EmbeddedInQpBar p k] (g : Gp p) : HodgeTatePair ⥤ HodgeTatePair where
  obj X := ⟨PadicTest.twist g X.test, X.rank⟩
  map f := ⟨(PadicTest.twist g).map f.1, f.2⟩

/-- The identity of the exterior algebra of K^n, K = R[1/p], as a natural map from
`New.Variety.HodgeTatePair.formCoeff` to `New.Variety.HodgeTatePair.formCoeff` composed with the
g-twist. -/
def HodgeTatePair.twistForms [EmbeddedInQpBar p k] (g : Gp p) :
    formCoeff ⟶ galTwist g ⋙ formCoeff where
  app X := ofHom (AddMonoidHom.id (ULift
    (ExteriorAlgebra X.test.GenericRing ((toHodgeTest.obj X).Index → X.test.GenericRing))))

-- Unsealed, the closing `rfl` unfolds `contraction` instead of comparing its arguments.
seal contraction in
/-- The class `contractionPow h` is compatible with the `g`-twist. Restrict it along the twist of
pairs. Compose it with the identification `twistGenericCoeff g` of the coefficients. Then pull it
back along the identification `twistForms g` of the exterior algebras. The result is the class
`contractionPow h` itself. -/
lemma HodgeTatePair.contractionPow_galTwist [EmbeddedInQpBar p k] (g : Gp p) (h : ℕ) :
    pullbackAlong (twistForms g)
        (comp (TotalH.map (restrictAlong (galTwist g)) (contractionPow h))
          (TotalH.homClass (toTest.whiskerLeft (twistGenericCoeff g)))) =
      contractionPow h := by
  induction h with
  | zero =>
    -- both sides are the class of the projection to degree zero
    rw [contractionPow, map_homClass, pullbackAlong_pullbackAlong]
    -- The exterior algebras of `Index → baseAlg` and of `Index → X.test.GenericRing` carry
    -- the same module structure only up to unfolding, so `homClass_comp` matches only up to that.
    exact (homClass_comp ..).symm
  | succ h ih =>
    -- Move `twistForms g` past the class of the cocycle `contractionCocycle`, then use the
    -- induction hypothesis. The side goal, that `twistForms g` carries the twisted cocycle to
    -- `contractionCocycle`, holds by definition.
    rw [contractionPow, map_comp_assoc, Cocycle.map_cohomClass_restrict,
      ← comp_assoc_of_sq (contractionCocycle.cohomClass_naturality ..), ih]
    exact fun _ _ _ ↦ rfl

end GaloisTwist

/-! ## Galois action in weight h -/

section GaloisWeight

open CategoryTheory Functor TotalH HodgeTatePair

variable {p : ℕ} {k E : Type} [Field k] [EmbeddedInQpBar p k] {g : Gp p} [Field E] [Algebra E k]

/-- Let `g` in `Gal(ℚ̄_p/ℚ_p)` fix the subfield `E` of `k ⊆ ℚ̄_p`. Let `x` be a Hodge class of `N`
over `E`, meaning a degree-`q` Ext class from `(A, M) ↦ N(A ⊕ M)` to `(A, M) ↦ ⋀_A M`. Let `ξ` be a
degree-`n` class on `p`-adic tests `S` (families of valuation rings over O_C) with coefficients
`S[1/p]`, such that `hodgeTateMap h x.baseChange = restrictToPairs ξ`. Here `hodgeTateMap h` uses
the `h`-th power of the contraction class, and `restrictToPairs` is the restriction from tests to
pairs of a test and a free module. Let `t : k` map to the value of the cyclotomic character at
`g⁻¹`. Let `τ` be the identity of each ring `S[1/p]`, viewed as an `E`-algebra map from the ring of
`S` to that of its twist by `g`. Then the pull-back of `ξ` along the twist by `g`, `τ` and the
identification `twistGenericCoeff g` of the coefficients has the same image under `restrictToPairs`
as `t ^ h • ξ`. -/
theorem hodgeTateMap_galois_twist
    (hg : ∀ z : E, g (algebraMap k (PadicAlgCl p) (algebraMap E k z)) =
      algebraMap k (PadicAlgCl p) (algebraMap E k z))
    {N : AbFunctor (CommAlg E)} {q h n : ℕ} {x : HodgeH N q} {t : k}
    {ξ : H (genericOver ⋙ restrictAlg E k ⋙ N) genericCoeff n}
    (hξ : hodgeTateMap h x.baseChange = restrictToPairs ξ)
    (ht : algebraMap k (PadicAlgCl p) t = algebraMap ℤ_[p] (PadicAlgCl p) (cyclotomicGp g⁻¹).val) :
    let τ : genericOver ⋙ restrictAlg E k ⟶ PadicTest.twist g ⋙ genericOver ⋙ restrictAlg E k :=
      .mk fun (c : PadicTest) ↦
      CommAlg.homOfRingHom (.id c.GenericRing) fun (z : E) ↦
        ((c.genericStructureMap_twist g _).trans (congrArg c.genericStructureMap
          ((UniformSpace.Completion.algEquiv_smul_coe ..).trans (congrArg _ (hg z))))).symm
    restrictToPairs
        ((Comparison.of (PadicTest.twist g) (twistGenericCoeff g)).pull (whiskerRight τ N) n ξ :
        H (genericOver ⋙ restrictAlg E k ⋙ N) genericCoeff n) =
      restrictToPairs (t ^ h • ξ) := by
  -- The twist by `g`, combined with scaling the module of a pair by `t`, gives a map `T` over `E`
  -- from `pairAlg` to its twist. The claim is then a computation of Yoneda products: twisting moves
  -- past `contractionPow h` (`contractionPow_galTwist`) and turns into the scaling
  -- `HodgeTest.scaleModule t` (`pull_twist`).
  intro τ
  let φ : HodgeTest k ⥤ HodgeTest E := (HodgeTest.baseComparison (k := k) (E := E)).functor
  let σ : toHodgeTest ⋙ φ ⟶ galTwist g ⋙ toHodgeTest ⋙ φ :=
    toHodgeTest.whiskerLeft (HodgeTest.scaleModule t φ) ≫ .mk fun X ↦ ⟨τ X.test, .id⟩
  let B : HodgeTatePair ⥤ CommAlg E := (toHodgeTest ⋙ φ) ⋙ HodgeTest.sqZeroExt
  let S : B ⟶ galTwist g ⋙ B := whiskerRight σ HodgeTest.sqZeroExt
  -- The components of `T`: the identity on `thickeningOver` and `S` on the square-zero extension.
  -- They are `E`-linear because `g` fixes `E`.
  let A : HodgeTatePair ⥤ CommAlg E := pairAlg ⋙ restrictAlg E k
  let T₀ (X : HodgeTatePair) : A.obj X ⟶ (galTwist g ⋙ A).obj X := CommAlg.homOfRingHom
    ((RingHom.prodMap (.id _) (S X).hom.toRingHom).restrict _ _ (by tauto)) fun z ↦
      Subtype.ext (Prod.ext ((congrArg _ (hg z).symm).trans (DFunLike.congr_fun
        (PadicTest.uniqueLift_comp_eq_uniqueLift_twist g X.test) _)) ((S X).hom.commutes' z))
  have h_nat (X Y : HodgeTatePair) (f : X ⟶ Y) :
      A.map f ≫ T₀ Y = T₀ X ≫ (galTwist g ⋙ A).map f := by
    -- The factor `t` from `HodgeTest.scaleModule` is the factor `cyclotomicGp g⁻¹` by which the
    -- twist changes `mulMu` (`thickeningOver.mulMu_twist`).
    have h_scal (m : Fin X.rank → X.GenericRing) :
        Y.test.genericStructureMap (algebraMap ℤ_[p] (PadicAlgCl p) (cyclotomicGp g⁻¹).val) *
          (show Y.test.GenericRing from (f.snd m).1) = (f.snd (t • m)).1 := by
      rw [← ht, ← algebraMap_smul X.GenericRing, map_smulₛₗ, RingHom.coe_coe, AlgHom.commutes]
      rfl
    -- The map of thickenings induced by a map `u` of tests sends the class of `y` to the class of
    -- the image of `y` under the map of Witt vectors of the tilts, with `p` inverted. This does
    -- not involve the structure maps, so it is the same for `f` and for its twist.
    have h_can {c d : PadicTest} (u : c ⟶ d) (y : Localization.Away (p : WittVector p c.TiltRing)) :
        PadicTest.mapThickening u (Ideal.Quotient.mk _ y) =
          Ideal.Quotient.mk (RingHom.ker d.thetaGeneric ^ 2)
            (IsLocalization.map (Localization.Away (p : WittVector p d.TiltRing))
              (WittVector.map (p := p) (tiltMap u.toRingHom : c.TiltRing →+* d.TiltRing))
              (powers_le_comap_powers p _) y) :=
      rfl
    have h_map : ∀ b : X.test.Thickening, PadicTest.mapThickening f.1 b =
        PadicTest.mapThickening ((PadicTest.twist g).map f.1) b :=
      Ideal.Quotient.mk_surjective.forall.2 fun y ↦
        (h_can f.1 y).trans (h_can ((PadicTest.twist g).map f.1) y).symm
    -- first component: `h_map`, `mulMu` and `h_scal`; second component: `S` is natural
    ext z
    refine Subtype.ext (Prod.ext ?_ (ConcreteCategory.congr_hom (S.naturality f) _))
    exact congrArg₂ (fun b c : Y.test.Thickening ↦ b + c) (h_map _)
      ((thickeningOver.mulMu_twist g Y.test _).trans (congrArg _ (h_scal _)))
  -- Only the second component of `T` is used below.
  obtain ⟨T, hT⟩ : ∃ T : A ⟶ galTwist g ⋙ A,
      ∀ (X : HodgeTatePair) (x : A.obj X), (T X x).val.snd = S X x.val.snd :=
    ⟨⟨T₀, h_nat⟩, fun _ _ ↦ rfl⟩
  let y : H (A ⋙ N) (toHodgeTest ⋙ hodgeCoeff) q :=
    (Comparison.restrict toHodgeTest _).pull (whiskerRight toSqZero (restrictAlg E k ⋙ N)) q
      x.baseChange
  let α : TotalH (A ⋙ N) (galTwist g ⋙ A ⋙ N) := homClass (whiskerRight T N)
  let β : TotalH (galTwist g ⋙ scalarCoeff) scalarCoeff :=
    homClass (toTest.whiskerLeft (twistGenericCoeff g))
  let u : TotalH (galTwist g ⋙ formCoeff) scalarCoeff :=
    TotalH.comp (TotalH.map (restrictAlong (galTwist g)) (contractionPow h)) β
  let s : formCoeff ⟶ formCoeff := toHodgeTest.whiskerLeft (HodgeTest.scaleModule t hodgeCoeff)
  have h_tw : pullbackAlong (twistForms g) u = contractionPow h := contractionPow_galTwist g h
  -- The class `y` comes from the Hodge class `x` over `E`, so its twist along `T` is its scaling
  -- by `t`.
  have h_pull : TotalH.comp α (TotalH.map (restrictAlong (galTwist g)) y.toTotalH) =
      TotalH.comp y.toTotalH (homClass (s ≫ twistForms g)) := by
    refine pull_twist (Comparison.pull_trans _) σ (whiskerRight T N) (by ext; rfl) ?_
    ext : 2
    -- `using!`: the goal carries identity whiskerings `toHodgeTest.whiskerLeft (𝟙 _)` that `simp`
    -- does not remove; they unfold to `𝟙`
    simpa using! (N.map_commSq ⟨by ext; apply hT⟩).w
  -- Here `restrictToPairs ξ = TotalH.comp y.toTotalH (contractionPow h)` by `hξ`.
  calc
    _ = TotalH.comp α
        (TotalH.comp (TotalH.map (restrictAlong (galTwist g)) (restrictToPairs ξ)) β) := by
      -- The classes live over `(restrictAlong F).obj G` on one side and `F ⋙ G` on the other,
      -- which agree only up to unfolding, so `M` is given and the lemmas are applied by unification
      refine .trans ?_ ((pullbackAlong_of _).symm.trans (congrArg _
        ((of_comp_homClass (M := (restrictAlong (galTwist g)).obj _) _).symm.trans
          (congrArg (TotalH.comp · β) (map_of ..).symm))))
      simp [restrictToPairs, Comparison.pull, H.map, H.push, mapExactFunctor_mapExactFunctor,
        mapExtAddHom, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
      congr 3 with : 2
      exact (N.map_commSq ⟨by ext; apply congrArg TrivSqZeroExt.fst (hT ..)⟩).w.symm
    _ = TotalH.comp α (TotalH.comp (TotalH.map (restrictAlong (galTwist g)) y.toTotalH) u) := by
      rw [← hξ]
      exact congrArg _ (TotalH.map_comp_assoc ..)
    _ = TotalH.comp y.toTotalH (pullbackAlong (s ≫ twistForms g) u) := comp_assoc_of_sq h_pull _
    _ = TotalH.comp y.toTotalH (pullbackAlong s (contractionPow h)) := by
      rw [← pullbackAlong_pullbackAlong, h_tw]
    _ = restrictToPairs (t ^ h • ξ) := by
      -- scaling the module by `t` multiplies `contractionPow h` by `t ^ h`
      rw [restrictToPairs.map_smul, ← hξ, scaleModule_comp_contractionPow, comp_smul]
      rfl

end GaloisWeight

end New.Variety

end
end
end

/-!
# The period map for ℓ-adic cohomology on p-adic tests, and Hodge–Tate weights

This file compares the geometric cohomology `New.Variety.ellAdicCohom R Ω n` of an `R`-scheme `Y`
(`Ω` an `R`-algebra on which a group `Γ` acts by ring maps fixing the image of `R`), written
`V^n(Y)`, with the cohomology of the points of `Y` in `p`-adic tests. A vector has weight `h`
(`New.HasHodgeTateWeight`) if Galois acts on it by the `(-h)`-th power of the cyclotomic character.

## Main definitions and results

* `New.Variety.toTwistAlg`: the identity of a `p`-adic test as an `R`-algebra map to its Galois
  twist.
* `New.Variety.exists_period_map`: the period map is natural, Galois equivariant, and bijective for
  proper charted `Y`. It is the pull-back along the comparison of
  `New.Variety.exists_primitive_period_comparison`.
* `New.Variety.exists_hasHodgeTateWeight`: the value of the Hodge–Tate map on a Hodge class comes
  from a vector of weight `h`, naturally in maps to `Y`.

Notions from other files:
* `New.Variety.PadicTest`: A p-adic test c: a non-empty family of cells, whose product is the ring
  `c.ProdRing`, with a ring map from O_C, the integers of ℂ_p, to that product.
* `New.Variety.PadicTest.twist`: For g in G_p, the endofunctor of p-adic tests that keeps the ring
  and precomposes its structure map O_C → c.ProdRing with the action of g.

## Relation to the literature

Known result: The primitive comparison theorem and the period isomorphism. Here coefficients are
constant, schemes are proper and charted (`New.Variety.IsCharted`), cohomology is taken on test
rings, and the maximal ideal is put into the coefficients. The result is deduced from the duality
comparison on products of projective lines, without almost finiteness. Source: P. Scholze, p-adic
Hodge theory for rigid-analytic varieties, Forum Math. Pi 1 (2013), Thm 1.3 and 5.1; for the method,
B. Zavyalov, Poincaré duality in abstract 6-functor formalisms, arXiv 2301.03821, Thm 3.3.3 and
Appl. 1.3.4; Li–Reinecke–Zavyalov, arXiv 2410.08200, §6.4.

Known result: The Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. The target here
is cohomology on test rings, which is not identified with étale cohomology. Only the natural
multiplicative map into the part of weight h is built, from the torsor of lifts modulo the square of
the kernel of Fontaine's map, and bijectivity is not proved. Source: Scholze, p-adic Hodge theory
for rigid-analytic varieties, Forum Math. Pi 1 (2013), Cor. 1.8; the construction follows Bhatt, The
Hodge–Tate decomposition via perfectoid spaces, Arizona Winter School 2017, §3.4.
-/

@[expose] public section

/-!
## The period map on p-adic tests

The period map compares the geometric `p`-adic cohomology `New.Variety.ellAdicCohom R Ω n` of an
`R`-scheme `Y`, extended to a period ring `K`, with the cohomology of the points of `Y` in `p`-adic
tests (`New.Variety.PadicTest`, `New.Variety.testPoints`) with coefficients `Ψ`. Here `θ` identifies
`Ψ c` with `K ⊗_S (S ⊗_{A_inf} W(c^♭))^`, the hat denoting `p`-adic completion, for an
`A_inf`-algebra `S`.
-/

namespace New.Variety

open CategoryTheory TensorProduct Function AlgebraicGeometry Functor AlgebraTensorModule Period
  Comparison PadicTest ModuleCat.Algebra Module

variable {p : ℕ} [ThePrime p] {R : CommRingCat} [Algebra R OC] [Algebra R Ω]
  {e : Ω →+* PadicAlgCl p} (he : ∀ r : R, e (algebraMap R Ω r) = (algebraMap R OC r : ℂ_[p]))
  {S : Type} [CommRing S] [Algebra Ainf S]
  (K : Type) [CommRing K] [Algebra S K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] {Ψ : PadicTest ⥤ ModuleCat K}
  (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) (n : ℕ)
  {Γ : Type*} [Group Γ] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
  {j : Γ → Gp p} (hj : ∀ (g : Γ) (x : Ω), j g (e x) = e (g • x))

/-- The identity of a test is a map of `R`-algebras to its twist by `j g`. Here
`algFunctor ⋙ restrictAlg R OC` sends a test `c` to the ring `c.ProdRing`, made an `R`-algebra
through `R → O_C`. -/
noncomputable def toTwistAlg (g : Γ) :
    algFunctor ⋙ restrictAlg R OC ⟶ PadicTest.twist (j g) ⋙ algFunctor ⋙ restrictAlg R OC where
  -- `g` fixes the image of `R` in `Ω`, so `j g` fixes its image in `OC`.
  app c := CommAlg.homOfRingHom (RingHom.id ((algFunctor ⋙ restrictAlg R OC).obj c)) fun z ↦
    congrArg c.structureMap (Subtype.ext (by simp [← he, hj]))

/-- A point of `Y` in a test is a point of `Y` in the twist of the test by `j g`. -/
noncomputable def toTwistPoints (g : Γ) (Y : Over (Spec R)) :
    testPoints.obj Y ⟶ PadicTest.twist (j g) ⋙ testPoints.obj Y :=
  whiskerRight (toTwistAlg he hj g) (algPointsOf R R Y)

/-- `ℚ_p` is a localization of `ℤ_p`, so the two scalar actions on `K ⊗ M` agree. -/
instance (M : ModuleCat ℚ_[p]) : CompatibleSMul ℤ_[p] ℚ_[p] K M :=
  IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors _) ..

section

variable {K n}

/-- The element `θ (a ⊗ 1 ⊗ w)` of `Ψ c`, for `a` in `K` and a Witt vector `w` over the tilt of
the test `c`. -/
noncomputable abbrev periodTmul (c : PadicTest) (a : K) (w : WittVector p c.TiltRing) : Ψ.obj c :=
  θ.hom.app c (a ⊗ₜ AdicCompletion.of _ _ (1 ⊗ₜ w))

/-- The map of coefficients `β`, from the twist of `Ψ` by `g` to `Ψ`, acts as `σ` on the elements
`θ (a ⊗ 1 ⊗ w)`, where `w` is a Witt vector whose coordinates are fixed by Frobenius.
`moduleCoeff Ψ` is `Ψ` with values lifted by `ULift`, and `⟨_⟩` wraps an element of `Ψ c`. -/
def ActsAsOnFrobeniusFixed (g : Gp p) (β : PadicTest.twist g ⋙ moduleCoeff Ψ ⟶ moduleCoeff Ψ)
    (σ : K → K) : Prop :=
  ∀ (c : PadicTest) (a : K) (w : WittVector p c.TiltRing), (∀ i : ℕ, w.coeff i ^ p = w.coeff i) →
    β.app c ⟨periodTmul θ ((PadicTest.twist g).obj c) a w⟩ = ⟨periodTmul θ c (σ a) w⟩

/-- A `p`-adic period map: `K`-linear maps `J Y` from `K ⊗ V^n(Y)` to `H^n` of the points of `Y`
in tests, with coefficients `Ψ`, that are natural, Galois equivariant and bijective on proper
charted `Y`. Here `V^n(Y)` is the geometric `p`-adic cohomology `ellAdicCohom R Ω n` of `Y`. -/
structure IsPadicPeriodMap
    (J : ∀ Y : Over (Spec R), K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩ →ₗ[K]
      H (freeAb.obj (testPoints.obj Y)) (moduleCoeff Ψ) n) : Prop where
  /-- `J` commutes with the pull-back along `f : W ⟶ Y`. -/
  natural (W Y : Over (Spec R)) (f : W ⟶ Y) (x : K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩) :
    J W ((((ellAdicCohom R Ω n).map f.op).hom.restrictScalars ℤ_[p]).baseChange K x) =
      H.map (moduleCoeff Ψ) (freeAb.map (testPoints.map f)) n (J Y x)
  /-- `J` carries `σ ⊗ g` to the pull-back along `β` and the twist by `j g`, if `β` acts as `σ`. -/
  equivariant (Y : Over (Spec R)) (g : Γ) (σ : K →ₗ[ℤ_[p]] K)
    (β : PadicTest.twist (j g) ⋙ moduleCoeff Ψ ⟶ moduleCoeff Ψ)
    (hβ : ActsAsOnFrobeniusFixed θ (j g) β σ) (x : K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩) :
    J Y (TensorProduct.map σ
        ((ellAdicCohom.galoisAction R Ω Γ Y n g).restrictScalars ℤ_[p]) x) =
      (Comparison.of (PadicTest.twist (j g)) β).pull (freeAbMap (toTwistPoints he hj g Y)) n
        (J Y x)
  /-- `J Y` is bijective if `Y` is proper and charted over `Ω`. -/
  bijective (Y : Over (Spec R)) [IsCharted Y Ω] [IsProper Y.hom] : Bijective (J Y)

end

omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] in
/-- Let `γ` send `a ⊗ x` to `θ (a ⊗ 1 ⊗ w)`, where `w` is the Witt vector over the tilt obtained
from `x`, and let `β` act as `σ` on the elements `θ (a ⊗ 1 ⊗ w)` with `w` fixed by Frobenius
(`ActsAsOnFrobeniusFixed`). Then the comparison `x ↦ γ (σ a ⊗ x)` is the comparison
`x ↦ γ (a ⊗ x)` followed by `β`, since Witt vectors of locally constant `𝔽_p`-valued functions are
fixed by Frobenius. -/
private lemma coeffHom_eq_coeffHom_trans_of_actsAsOnFrobeniusFixed
    (γ : genericTest ⋙ asModules (wittLocConst p) ⋙ tensorWith K K ⟶ Ψ)
    (hγ : ∀ (c : PadicTest) (a : K) (x : (wittLocConst p).obj (genericTest.obj c)),
      γ.app c (a ⊗ₜ x) =
        θ.hom.app c (a ⊗ₜ wittToPeriodAlg S (tilt.obj c)
          (WittVector.map (locConstToTilt.app c).hom.toRingHom x)))
    {g : Gp p} {σ : K →ₗ[ℤ_[p]] K} {β : PadicTest.twist g ⋙ moduleCoeff Ψ ⟶ moduleCoeff Ψ}
    (hβ : ActsAsOnFrobeniusFixed θ g β σ) (a : K) :
    -- `cmp b` is the comparison `x ↦ γ (b ⊗ x)`
    let cmp (b : K) : Comparison ellAdicCoeff (moduleCoeff Ψ) :=
      ⟨genericTest, whiskerLeft genericTest (tensorWith.mk K b _) ≫ coeffMap γ⟩
    (cmp (σ a)).coeffHom = ((cmp a).trans (Comparison.of (PadicTest.twist g) β)).coeffHom := by
  intro cmp
  ext c ⟨w⟩
  let w' : WittVector p c.TiltRing := WittVector.map (locConstToTilt.app c).hom.toRingHom w
  have h_frob (i : ℕ) : w'.coeff i ^ p = w'.coeff i :=
    (map_pow ..).symm.trans (congrArg _ (LocallyConstant.ext fun _ ↦ ZMod.pow_card _))
  have h_acts : β.app c ⟨periodTmul θ ((PadicTest.twist g).obj c) a w'⟩ =
      ⟨periodTmul θ c (σ a) w'⟩ := hβ c a w' h_frob
  -- both sides are `θ (σ a ⊗ 1 ⊗ w')`: the left one by `hγ`, the right one by `hγ` and `hβ`
  have h_lhs : (cmp (σ a)).coeffHom.app c ⟨w⟩ = ⟨periodTmul θ c (σ a) w'⟩ :=
    congrArg ULift.up (hγ c (σ a) w)
  have h_rhs : ((cmp a).trans (Comparison.of (PadicTest.twist g) β)).coeffHom.app c ⟨w⟩ =
      β.app c ⟨periodTmul θ ((PadicTest.twist g).obj c) a w'⟩ :=
    congrArg (β.app c) (congrArg ULift.up (hγ (PadicTest.twist g c) a w))
  exact h_lhs.trans (h_rhs.trans h_acts).symm

/-- Let `(S, K)` be a period ring pair (`New.Variety.IsPeriodRingPair`: `S` is a `p`-torsion-free,
`p`-adically complete `A_inf`-algebra in which `p` divides `ξ`, and `τ` is a unit in `K`), with `K`
flat over `S`. Let `Ψ` be a functor from `p`-adic tests `B` to `K`-modules, identified by `θ` with
`K ⊗_S (p-adic completion of S ⊗_{A_inf} W(B^♭))`. Let `e : Ω →+* ℚ̄_p` agree with `R → O_C` on `R`,
and let `j : Γ → G_p` satisfy `j g (e x) = e (g • x)`. Then there are `K`-linear maps `J Y` from
`K ⊗ V^n(Y)` to `H^n` of `ℤ[Y(B)]` (the `R`-points of `Y` in tests), with coefficients `Ψ`, that
form a `p`-adic period map (`IsPadicPeriodMap`): natural in `Y`, Galois equivariant, and bijective
for proper charted `Y`. -/
lemma exists_period_map [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] [IsScalarTower ℤ_[p] S K]
    [Flat S K] (hS : IsPeriodRingPair p S K) :
    ∃ J : ∀ Y : Over (Spec R), K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩ →ₗ[K]
      H (freeAb.obj (testPoints.obj Y)) (moduleCoeff Ψ) n, IsPadicPeriodMap he θ hj J := by
  -- `J` is the composite of `K ⊗ V^n(Y) = K ⊗ H^n(Y_Ω, ℤ_p)`, the map `baseChangeMap` that moves
  -- `K` into the coefficients, and the pull-back along the primitive comparison `γ`.
  let E (Y : Over (Spec R)) :=
    equivOfCompatibleSMul ℚ_[p] ℤ_[p] K K (ellAdicCohom R Ω n ⟨Y⟩) ≪≫ₗ cancelBaseChange ..
  -- `γ : K ⊗ W(LC(Spec c[1/p], 𝔽_p)) → Ψ c` sends `a ⊗ w` to `θ (a ⊗ 1 ⊗ w)` (`hγ`); it is
  -- bijective on cohomology as soon as `primitiveMap` is modulo `p`, given flat base change
  -- and finiteness (`hγ_bij`).
  obtain ⟨γ, hγ, hγ_bij⟩ := exists_primitive_period_comparison K θ hS
  algebraize [(algebraMap _ ℂ_[p]).comp e]
  let α (Y : Over (Spec R)) :
      freeAb (testPoints Y) ⟶ genericTest ⋙ freeAb (testIncl ⋙ geomPoints R Ω Y) :=
    freeAbMap (toGenericPoints Ω he Y ≫ whiskerLeft _ (whiskerLeft _ (algToBaseChange Ω Y)))
  let J (Y : Over (Spec R)) : K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩ →ₗ[K]
      H (freeAb.obj (testPoints.obj Y)) (moduleCoeff Ψ) n :=
    pullₗ γ (α Y) n ∘ₗ
      baseChangeMap K K (freeAb.obj (testIncl ⋙ (geomPoints R Ω).obj Y))
        (asModules (wittLocConst p)) n ∘ₗ (E Y).toLinearMap
  -- On `a ⊗ x` the map `J` is the pull-back of `x` along the comparison `w ↦ γ (a ⊗ w)`.
  let cmp (a : K) : Comparison ellAdicCoeff (moduleCoeff Ψ) :=
    ⟨genericTest, whiskerLeft _ (tensorWith.mk K a _) ≫ coeffMap γ⟩
  have J_tmul (Y : Over (Spec R)) (a : K)
      (x : H (freeAb (testIncl ⋙ geomPoints R Ω Y)) ellAdicCoeff n) :
      J Y ((E Y).symm (a ⊗ₜ x)) = (cmp a).pull (α Y) n x := by
    -- `baseChangeMap` sends `a ⊗ x` to the push-forward of `x` along `w ↦ a ⊗ w`; pulling back
    -- along `γ` after that push-forward is pulling back along the composite `cmp a`.
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact (pull_push ⟨_, _⟩ (h := rfl) ..).trans (Abelian.Ext.comp_mk₀_id _)
  refine ⟨J, fun W Y f x ↦ ?_, fun Y g σ β hβ x ↦ ?_, fun Y _ _ ↦ ?_⟩
  · -- Naturality in `Y`, checked on pure tensors.
    obtain ⟨x, rfl⟩ := (E Y).symm.surjective x
    induction x with
    | add x y hx hy =>
      rw [LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, hx, hy, LinearMap.map_add,
        AddMonoidHom.map_add]
    | tmul a x =>
      rw [J_tmul]
      refine (J_tmul W a (x.map _ _ n)).trans (map_pull_eq_pull_map ?_ n x).symm
      exact freeAb.hom_ext fun _ _ ↦ by rfl
  · -- Equivariance, checked on pure tensors.
    obtain ⟨x, rfl⟩ := (E Y).symm.surjective x
    induction x with
    | add x y hx hy =>
      rw [LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, hx, hy, LinearMap.map_add,
        AddMonoidHom.map_add]
    | tmul a x =>
      refine (J_tmul Y (σ a) (x.map _ _ n)).trans ?_
      rw [J_tmul, pull_trans]
      -- Two steps. The two pull-backs are along the same comparison by `hβ`: Witt vectors of
      -- locally constant `𝔽_p`-valued functions are fixed by Frobenius.
      refine (congrArg (fun φ ↦ Comparison.pull ⟨_, φ⟩ _ n _)
        (coeffHom_eq_coeffHom_trans_of_actsAsOnFrobeniusFixed K θ γ hγ hβ a)).trans ?_
      -- And they are along the same map of points, as `e` is equivariant.
      refine (map_pull_eq_pull_map (a' := 𝟙 _) ((Category.id_comp _).trans (.symm ?_)) n
        x).symm.trans (H.map_id ..)
      refine freeAb.hom_ext fun c y ↦
        congrArg FreeAddCommGroup.of (baseChangeOf.ext (congrArg ULift.up ?_) fun z ↦ ?_)
      · apply Spec.map_comp_assoc (𝟙 _) (CommRingCat.ofHom (algebraMap c.ProdRing c.GenericRing))
      · -- `genericStructureMap_twist` matches the structure map of the twisted test only up to
        -- instances
        exact .symm ((c.genericStructureMap_twist (j g) _).trans (congrArg c.genericStructureMap
          ((UniformSpace.Completion.algEquiv_smul_coe ..).trans (congrArg _ (hj ..)))))
  · -- For `Y` proper and charted each of the three factors is bijective: `E Y` as a linear
    -- equivalence, `baseChangeMap` by flat base change, the pull-back by
    -- `finite_and_primitive_comparison`. The acyclicity hypothesis of the latter is almost descent,
    -- which applies since `p ∣ ξ` in `S`.
    obtain ⟨h_geo, -, h_prim⟩ :=
      finite_and_primitive_comparison Ω (isAcyclicOnPerfect_almostCoeff hS.pFlat_smul_eq_zero) Y
    have h_pts : HasFlatBaseChange (freeAb (testPoints Y)) := by
      apply (isAffinelyCovered_algPointsOf (ι := algFunctor) (fun c ↦ c.isTest.isComparableRing)
        Y).hasFlatBaseChange
    exact (hγ_bij h_geo h_pts finite_padic_cohomology (h_prim he) n).comp
      ((h_geo ..).comp (E Y).bijective)

end New.Variety

/-! ## Hodge–Tate weights of values of the Hodge–Tate map -/

section HodgeTateVectors

open CategoryTheory AlgebraicGeometry New Period IsScalarTower Variety PadicTest freeAb H
  PairRestrictBijective ModuleCat.Algebra
open scoped TensorProduct

/-- Let `Y`, `W` be proper over `R`, with `Y` smooth of relative dimension `d` and charted over `Ω`.
Let `E` be a field between `R` and `Ω` that is mapped to `k ⊆ ℚ̄_p`, and `A` a subring of `Ω`
containing the image of `R`. Let `e : Ω → ℚ̄_p` be a `p`-adic place embedding for `A` over `E`
(`New.GaloisRep.PadicPlaceEmbedding`) agreeing with `E → k → ℚ̄_p` on `E`, and `ε` a section of
`k → ℚ̄_p`. Take any `h` and a Hodge class `x` of degree `q` of `Y` over `E` (in Ext^q from
`(S, M) ↦ ℤ[Y(S ⊕ M)]` to `(S, M) ↦ ⋀_S M`). Then there are a vector `v` of `ℂ_p ⊗ V^(q+h)(Y)` and
an `ε`-semilinear map `Θ` from `ℂ_p ⊗ V^(q+h)(W)` to cohomology on pairs with coefficients `S[1/p]`
(`PairH`) such that: (a) `v` has Hodge–Tate weight `h` for the decomposition group of `A` in
`Gal(Ω/E)`; (b) `hodgeTateMap h (u^* x) = Θ (u^* v)` for all `u : W ⟶ Y`, where `hodgeTateMap h`
pulls back along `B_{S,M} → T ⊕ M` and applies the `h`-th power of the contraction class. -/
lemma New.Variety.exists_hasHodgeTateWeight {p h : ℕ} {R : CommRingCat} {E k : Type} [Field k]
    [Field E] [EmbeddedInQpBar p k] [Algebra R Ω] [Algebra R E] [Algebra E k] [Algebra E Ω]
    [IsScalarTower R E Ω] {Y : Over (Spec R)} [IsCharted Y Ω] [IsProper Y.hom] {A : ClosurePlace}
    [I : GaloisRep.PadicPlaceEmbedding E A p] (hR : ∀ r : R, algebraMap R Ω r ∈ A)
    (he_compat : ∀ x : E, algebraMap k (PadicAlgCl p) (algebraMap E k x) = I.e (algebraMap E Ω x))
    (d : ℕ) [SmoothOfRelativeDimension d Y.hom] (ε : PadicAlgCl p →+* k)
    (hε_section : ∀ z : PadicAlgCl p, algebraMap k (PadicAlgCl p) (ε z) = z)
    {W : Over (Spec R)} [IsProper W.hom] {q : ℕ}
    (x : HodgeH (freeAb.obj ((algPoints E R).obj Y)) q) :
    ∃ v : ℂ_[p] ⊗[ℤ_[p]] (ellAdicCohom R Ω (q + h)).obj ⟨Y⟩,
      ∃ Θ : ℂ_[p] ⊗[ℤ_[p]] (ellAdicCohom R Ω (q + h)).obj ⟨W⟩ →ₛₗ[ε]
        PairH (restrictAlg E k ⋙ freeAb.obj (algPointsOf E R W)),
      -- (a) `v` has Hodge–Tate weight `h` under the decomposition group of `A`
      HasHodgeTateWeight (ellAdicCohom.galoisAction R Ω (decompGroup Gal(Ω/E) A) Y (q + h)) h v ∧
      -- (b) `Θ` sends the pull-back of `v` along any `u` to `hodgeTateMap h` of the pull-back of
      -- `x`
      ∀ u : W ⟶ Y, hodgeTateMap h (x.map (freeAb.map ((algPoints E R).map u))).baseChange =
        Θ ((((ellAdicCohom R Ω (q + h)).map u.op).hom.restrictScalars ℤ_[p]).baseChange ℂ_[p]
          v) := by
  -- `hodgeTateMap h x` comes from a class `ξ` on `p`-adic tests. The period map `J` and the passage
  -- `B` to integral points have the same target, and `J Y` is bijective; `v` is defined by
  -- `J Y v = B Y ξ`.
  obtain ⟨e, ⟨rfl, hj⟩, _⟩ := I
  -- `θ` identifies the period algebra of a test `c` with `c[1/p]`, through Fontaine's map.
  obtain ⟨θ, hθ⟩ := exists_periodAlg_iso_genericAlg
  -- As `R` maps into the place `A`, the embedding `e` carries it into `OC`.
  algebraize [theta.comp (algebraMap ℤ_[p] _), (algebraMap E k).comp (algebraMap R E),
    (.codRestrict (.comp (algebraMap ..) (e.comp _)) _ (by simpa) : R →+* OC)]
  have := IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := OC) (A := ℂ_[p]) fun z ↦
    ((OC.toPadicIntAlgHom _).commutes z).symm
  -- `J Z'` maps `ℂ_p ⊗ V^(q+h)(Z')` to `H^(q+h)` of the points of `Z'` in tests `c`, with
  -- coefficients `c[1/p]`; it is natural in `Z'`, Galois equivariant, and bijective for `Z'`
  -- proper and charted.
  obtain ⟨J, J_nat, J_twist, J_bij⟩ :=
    exists_period_map (R := R) (fun _ ↦ rfl) _ θ (q + h) hj isPeriodRingPair_OC
  have h_compat (r : R) : algebraMap k ℂ_[p] (algebraMap R k r) = algebraMap R OC r := by
    have h_e : algebraMap k (PadicAlgCl p) (algebraMap E k (algebraMap R E r)) =
        e (algebraMap R Ω r) := by
      rw [he_compat, ← algebraMap_apply R E Ω r]
      -- `I.e` is `e`: the instance `I` was taken apart above
      rfl
    exact congrArg (algebraMap (PadicAlgCl p) ℂ_[p]) h_e
  -- By the valuative criterion, points over `c[1/p]` of a proper scheme extend uniquely to `c`.
  let B {n : ℕ} (Z' : Over (Spec R)) [IsProper Z'.hom] :
      H (genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R Z')) genericCoeff n ≃ₗ[k] _ :=
    .ofBijective (mapₗ ..)
      (IsCohomEquiv.of_bijective (p := toGenericPoints k h_compat Z')
        (fun c ↦ c.bijective_generic_points) n)
  -- `J` is `ℂ_[p]`-linear, hence semilinear along the section `ε` of `k → PadicAlgCl p`.
  have J_semi (Z' : Over (Spec R)) (z : PadicAlgCl p)
      (y : ℂ_[p] ⊗[ℤ_[p]] (ellAdicCohom R Ω (q + h)).obj ⟨Z'⟩) : J Z' (z • y) = ε z • J Z' y := by
    -- `ε z` acts on the target through its image in `ℂ_[p]`, which is the image of `z`
    have h_scalar : algebraMap k ℂ_[p] (ε z) = algebraMap (PadicAlgCl p) ℂ_[p] z :=
      congrArg (algebraMap (PadicAlgCl p) ℂ_[p]) (hε_section z)
    change J Z' (z • y) = algebraMap k ℂ_[p] (ε z) • J Z' y
    rw [h_scalar, ← (J Z').map_smul, _root_.algebraMap_smul]
  -- `Y` is smooth, so covered by étale charts.
  have h_den : PairRestrictBijective (restrictAlg E k ⋙ freeAb (algPointsOf E R Y)) := by
    apply (hasAtlas_algPointsOf d).isChartCovered.pairRestrictBijective
  obtain ⟨ξ, hξ⟩ : ∃ ξ : H (genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R Y))
      genericCoeff (q + h), hodgeTateMap h x.baseChange = restrictToPairs (n := q + h) ξ :=
    h_den.exists_hodgeTateMap_eq h _
  obtain ⟨v, hv⟩ := (J_bij Y).surjective (B Y ξ)
  -- `Θ` is `J W` followed by the inverse of `B W` and by `restrictToPairs`.
  refine ⟨v, restrictToPairs ∘ₛₗ (B W).symm.comp ⟨_, J_semi W⟩, fun g ↦ (J_bij Y).injective ?_,
    fun u ↦ ?_⟩
  · -- `J` turns the action of `g` into the pull-back along the twist of tests by `toGp g`. That
    -- pull-back commutes with `B` and multiplies `ξ` by the `h`-th power of the cyclotomic
    -- character of `(toGp g)⁻¹` (`hodgeTateMap_galois_twist`, `restrictToPairs` being injective).
    have h_fix (z : E) : toGp g (algebraMap k _ (algebraMap E k z)) =
        algebraMap k _ (algebraMap E k z) := by simp [he_compat, hj]
    calc
      _ = (Comparison.of _ (twistGenericCoeff (toGp g))).pull
          (freeAbMap (toTwistPoints (fun _ ↦ rfl) hj g Y)) (q + h) (J Y v) := by
        refine J_twist Y g _ (twistGenericCoeff _) (fun c a w _ ↦ ?_) v
        -- `hθ` and `genericStructureMap_twist` match the twisted test only up to instances
        exact (congrArg (fun t ↦ (twistGenericCoeff (toGp g)).app c ⟨t⟩)
          ((hθ ((PadicTest.twist (toGp g)).obj c) a w).trans
            (congrArg (· * _) (c.genericStructureMap_twist (toGp g) a)))).trans
              (congrArg ULift.up (hθ c _ w).symm)
      _ = B Y (ε (algebraMap _ _ (cyclotomicGp (toGp g)⁻¹).val) ^ h • ξ) := by
        -- `g` multiplies `ξ` by this scalar
        have h_weight := h_den.injective_restrictToPairs
          (hodgeTateMap_galois_twist h_fix hξ (hε_section _))
        rw [hv]
        refine (Comparison.map_pull_eq_pull_map (hom_ext fun c _ ↦ ?_) ..).symm.trans
          (congrArg (B Y) h_weight)
        -- The twist of points is compatible with passing to `c[1/p]`: functoriality of `Spec`.
        refine congrArg FreeAddCommGroup.of (congrArg ULift.up (Over.OverMorphism.ext ?_))
        exact
          (Spec.map_comp_assoc (CommRingCat.ofHom (algebraMap c.ProdRing c.GenericRing)) (𝟙 _)
            _).symm.trans
          (Spec.map_comp_assoc (𝟙 _) (CommRingCat.ofHom (algebraMap c.ProdRing c.GenericRing)) _)
      _ = J Y ((cyclotomicGp (toGp g) ^ (-h : ℤ)).val • v) := by
        simp [algebra_compatible_smul (PadicAlgCl p), J_semi, hv]
  · -- Naturality of `hodgeTateMap`, `restrictToPairs`, `J` and `B` in `u`.
    simp only [HodgeH.baseChange_map, hodgeTateMap_map, hξ, ← restrictToPairs_map, J_nat, hv,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_mk, LinearMap.coe_toAddHom]
    -- It remains that `B` commutes with the pull-back along `u`: `B` is `mapₗ` along the maps
    -- `toGenericPoints`, which are natural in the scheme.
    rw [(B W).symm_apply_eq.mpr]
    -- `τ Z'` is that map, typed with the source of `B Z'`, so that unification does not unfold `B`
    let τ (Z' : Over (Spec R)) : freeAb.obj (testPoints.obj Z') ⟶
        genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R Z') := by
      apply freeAb.map (toGenericPoints k h_compat Z')
    refine (map_comp _ (τ Y) ξ).symm.trans (.trans ?_ (map_comp (τ W) _ ξ))
    -- the two composite maps of points agree
    exact congrArg (H.map genericCoeff · (q + h) ξ) hom_ext

end HodgeTateVectors
