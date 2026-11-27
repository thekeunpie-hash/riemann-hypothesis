module

import Mathlib.Algebra.CharP.Pi
import Mathlib.RingTheory.DualNumber
public import Lib.Cohomology.Hodge.FixedPointFormula
public import Lib.Cohomology.PointClass.ProjectiveSpace
public import Lib.PadicComparison.HodgeTate.Map
public import Lib.Cohomology.ProjectiveLine.TiltedLineFormula

/-!
# The Hodge–Tate map does not kill point classes of the projective line and space

Let `k` be a field with an embedding in `ℚ̄_p`, and let `λ_h = New.Variety.hodgeTateMap h` be the
Hodge–Tate map of weight `h`, from Hodge cohomology to `p`-adic cohomology. We compute `λ₁` of the
symbol `[dT / T]` of the pair `(𝔸¹, 𝔸¹ ∖ 0)` through the extension `0 → T → Bˣ → Tˣ → 0`.

## Main definitions and results

* `New.Variety.thickeningOver.oneSubMu`, `New.Variety.thickeningOver.shortExact_oneSubMu`: the short
  exact sequence `0 → T → Bˣ → Tˣ → 0` whose first map is `t ↦ 1 - μ t`.
* `New.Variety.hodgeTateMap_symbolClass`: the image of `[dT / T]` comes from the product of the
  boundary class of the pair with the class of this extension.
* `New.Variety.projSpace.exists_hodgeTateMap_pointClass_line`: `λ₁` of the class of `[1 : 0]` in
  `ℙ¹` comes from a degree-two class `η` on `p`-adic tests such that `x ↦ x × η` is injective on
  functors with flat values.
* `New.Variety.projSpace.hodgeTateMap_pointClass_ne_zero`: the class of a point of `ℙ^d` has a
  nonzero image under the Hodge–Tate map of weight `d`.

Notions from other files:
* `New.Variety.PadicTest`: a `p`-adic test, a non-empty family of cells (`New.Variety.IsCell`) with
  a ring map from `O_C` to their product; `R` denotes its ring.
* `New.Variety.thickeningOver`: the functor sending a `p`-adic test with ring `R` to the `k`-algebra
  `B = W(R♭)[1/p] / (ker θ)²`. `New.Variety.genericOver` sends it to `T = R[1/p]`, and
  `New.Variety.thickeningOver.proj : B → T` is the projection; its kernel is `μ T`, `μ = [ε] - 1`.
* `New.Variety.hodgeTateMap`: `λ_h` sends a Hodge class to a class on Hodge–Tate pairs (a `p`-adic
  test with a finite free module `M` over `T`). It restricts along `B ×_T (T ⊕ M) → T ⊕ M`, applies
  the `h`-th power of the contraction class, and projects `⋀M` to degree zero.
  `New.Variety.restrictToPairs` maps cohomology on `p`-adic tests to the same target.
* `New.Variety.symbolClass`: the class `[dT / T]` in the Hodge cohomology of the pair
  `(𝔸^d, 𝔸^d ∖ 0)`.
* `New.Variety.pointClass`: the class of a `k`-point `z` in Hodge cohomology of degree `d`, the
  image of a chosen class with support `z` and multiplicity `1` at `z`. Projective space
  `New.Variety.projSpace k d` sends `A` to the unimodular vectors in `A ^ (d + 1)` modulo units.

## Relation to the literature

Known; see `Lib.Cohomology.PointClass.LinearIndependence` for sources.
-/

@[expose] public section

noncomputable section

/-!
## The Hodge–Tate map of the symbol [dT/T]

For a `p`-adic test with ring `R`, `T = R[1/p]` is `New.Variety.genericOver`, with additive group
`New.Variety.genericCoeff`.
-/

section KummerSymbol


namespace New.Variety

open CategoryTheory AddCommGrpCat TotalH thickeningOver

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k]

/-- A unimodular vector `v` of length one over a `k`-algebra `A` (an `A`-point of `𝔸¹ ∖ 0`) has a
unit as its only coordinate `v 0`. -/
lemma isUnit_of_unimodular_one {A : CommAlg k} (v : (unimodular (d := 1)).toFunctor.obj A) :
    IsUnit (v.val.down 0) := by
  simpa [unimodular, Set.range_unique] using v.prop

/-- The coordinate of `𝔸¹ ∖ 0` as a map to the multiplicative group: the morphism from `ℤ[𝔸¹ ∖ 0]`,
the free abelian group on the unimodular vectors of length one, to `A ↦ Aˣ` (written additively)
on `k`-algebras. It sends a generator `[v]` to the coordinate `v 0`, a unit by
`New.Variety.isUnit_of_unimodular_one`. -/
def Gm.ofCoord :
    freeAb (unimodular (k := k) (d := 1)).toFunctor ⟶ forget₂ (CommAlg k) CommRingCat ⋙ Gm :=
  freeAb.desc (fun _ v ↦ ⟨(isUnit_of_unimodular_one v).unit⟩) fun _ _ _ _ ↦ ext.2 rfl

/-- On `p`-adic tests with ring `R`, the morphism `t ↦ 1 - μ t` from the additive group of
`T = R[1/p]` (`New.Variety.genericCoeff`) to the units of `B = W(R♭)[1/p] / (ker θ)²`. Here `μ t` is
`New.Variety.thickeningOver.mulMu`, the product with `μ = [ε] - 1`. As `(μ s) * (μ t) = 0`, the
map sends sums to products, so its values are units. -/
def thickeningOver.oneSubMu :
    genericCoeff ⟶ thickeningOver ⋙ forget₂ (CommAlg k) CommRingCat ⋙ Gm where
  app c :=
    uliftFunctor.map <| ofHom <| MonoidHom.toAdditiveRight <| MonoidHom.toHomUnits
      { toFun t := 1 - mulMu c t.toAdd
        map_one' := by
          change 1 - mulMu c 0 = 1
          rw [map_zero, sub_zero]
        -- The product of two terms in the image of `mulMu` vanishes.
        map_mul' := by
          intro s t
          let x : genericOver.obj c := s.toAdd
          let y : genericOver.obj c := t.toAdd
          change 1 - mulMu c (x + y) = (1 - mulMu c x) * (1 - mulMu c y)
          have h_zero : mulMu c x * mulMu c y = 0 := by
            exact (mulMu_proj_mul c (mulMu c x) y).symm.trans
              (by rw [proj_mulMu, zero_mul, map_zero])
          rw [map_add, mul_sub, sub_mul, sub_mul, mul_one, one_mul, h_zero, sub_zero, sub_sub,
            mul_one] }
  naturality c d f := by
    refine ext fun t ↦ Gm.ext.2 (.symm ?_)
    change thickeningOver.map f (1 - mulMu c t.down) = 1 - mulMu d (genericOver.map f t.down)
    calc
      _ = thickeningOver.map f 1 - thickeningOver.map f (mulMu c t.down) :=
        map_sub _ _ _
      _ = _ := congrArg₂ (· - ·) (map_one _) (map_mulMu c d f t.down)

/-- On `p`-adic tests the sequence `0 → T → Bˣ → Tˣ → 0` is short exact: its first map is
`t ↦ 1 - μ t` (`New.Variety.thickeningOver.oneSubMu`), its second is induced on units by the
projection `New.Variety.thickeningOver.proj : B → T`, and `w` says that their composite is zero. -/
lemma thickeningOver.shortExact_oneSubMu :
    ∃ w : oneSubMu ≫ Functor.whiskerRight proj (forget₂ (CommAlg k) CommRingCat ⋙ Gm) = 0,
      ShortComplex.ShortExact
        ⟨oneSubMu, Functor.whiskerRight proj (forget₂ (CommAlg k) CommRingCat ⋙ Gm), w⟩ := by
  -- At each test `c` the additive sequence `0 → T → B → T → 0` of `mulMu` and `proj` is exact.
  choose h_surj h_inj h_exact using exact_mulMu_proj (k := k)
  refine shortExact_of_app (fun c ⟨s⟩ ⟨t⟩ h_eq ↦ ?_) (fun c ⟨u⟩ ↦ ?_) fun c ⟨u⟩ ↦ ?_
  · -- `1 - μ s = 1 - μ t` forces `s = t`.
    have h_app (x : (asModules PadicTest.genericAlg).obj c) :
        (show (thickeningOver.obj c)ˣ from ((oneSubMu.app c).hom ⟨x⟩).down).val =
          1 - mulMu c x := rfl
    have h_val := (h_app s).symm.trans ((Gm.ext.mp h_eq).trans (h_app t))
    exact congrArg ULift.up (h_inj c (sub_right_injective h_val))
  · -- Exactness applied to `1 - u`: the units with image `1` are those of the form `1 - mulMu t`.
    have hproj : proj c (1 - u.val) = 1 - proj c u.val :=
      (c.thickeningProj.map_sub 1 u.val).trans
      (congrArg (· - proj c u.val) c.thickeningProj.map_one)
    have h_one : proj c u.val = 1 ↔ ∃ t, 1 - mulMu c t = u.val := by
      calc
        _ ↔ proj c (1 - u.val) = 0 := by rw [hproj, sub_eq_zero]; exact eq_comm
        _ ↔ ∃ t, mulMu c t = 1 - u.val := h_exact c (1 - u.val)
        _ ↔ _ := exists_congr fun _ ↦ eq_comm.trans sub_eq_iff_comm
    constructor
    · intro h
      obtain ⟨t, ht⟩ := h_one.mp (Gm.ext.mp h)
      exact ⟨⟨t⟩, Gm.ext.mpr ht⟩
    · rintro ⟨⟨t⟩, ht⟩
      exact Gm.ext.mpr (h_one.mpr ⟨t, Gm.ext.mp ht⟩)
  · -- A lift `b` of the unit `u` is a unit, as the kernel has square zero.
    obtain ⟨b, hb⟩ : ∃ b : thickeningOver.obj c, proj c b = u.val := h_surj c u.val
    have h_unit : IsUnit b := (IsNilpotent.isUnit_quotient_mk_iff ⟨2, c.ker_thickeningProj_sq⟩).mp
      (.of_map (RingHom.quotientKerEquivOfSurjective (h_surj c)) _ ⟨u, hb.symm⟩)
    exact ⟨⟨h_unit.unit⟩, Gm.ext.mpr hb⟩

/-- Let `ω` be a form on `𝔸¹ ∖ 0` over Hodge tests that sends a point `a + m` to a one-form `w`
with `a • w = m`, so that `ω = dT / T` (such an `ω` is given by `New.Variety.symbolClass_one`). On
Hodge–Tate pairs, the pull-back of `ω` followed by one contraction
(`New.Variety.HodgeTatePair.contractionPow 1`) is the pull-back of the class of the extension
`0 → T → Bˣ → Tˣ → 0` (`New.Variety.thickeningOver.shortExact_oneSubMu`) along the coordinate
`New.Variety.Gm.ofCoord`. -/
private lemma pull_mk₀_comp_contractionPow_one_eq_pull_extClass_oneSubMu
    (ω : HodgeTest.sqZeroExt ⋙ freeAb.obj (unimodular (k := k) (d := 1)).toFunctor ⟶ hodgeCoeff)
    (hω : ∀ (c : HodgeTest k)
        (v : (unimodular (k := k) (d := 1)).toFunctor.obj (HodgeTest.sqZeroExt.obj c)),
      ∃ w : c.Index → c.baseAlg, (v.val.down 0).fst • w = (v.val.down 0).snd ∧
        ω.app c (FreeAddCommGroup.of v) = ⟨ExteriorAlgebra.ι c.baseAlg w⟩) :
    comp
        ((Comparison.restrict HodgeTatePair.toHodgeTest hodgeCoeff).pull
          (Functor.whiskerRight HodgeTatePair.toSqZero
            (freeAb.obj (unimodular (k := k) (d := 1)).toFunctor)) 0 (.mk₀ ω)).toTotalH
        (HodgeTatePair.contractionPow 1) =
      ((Comparison.restrict HodgeTatePair.toTest genericCoeff).pull
        (Functor.whiskerRight HodgeTatePair.toGeneric
          (freeAb.obj (unimodular (k := k) (d := 1)).toFunctor)) 1
        (H.map genericCoeff (genericOver.whiskerLeft Gm.ofCoord) 1
          shortExact_oneSubMu.2.extClass)).toTotalH := by
  -- Both sides are computed by explicit cocycles on pairs.
  let N : CommAlg k ⥤ AddCommGrpCat := freeAb.obj (unimodular (k := k) (d := 1)).toFunctor
  let α : HodgeTatePair.pairAlg ⋙ N ⟶ HodgeTatePair.toHodgeTest ⋙ hodgeCoeff :=
    Functor.whiskerRight HodgeTatePair.toSqZero N ≫ HodgeTatePair.toHodgeTest.whiskerLeft ω
  simp [Comparison.pull, H.map, H.push, Abelian.Ext.toTotalH, Functor.mapExtAddHom,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_extClass]
  -- The left side is `α` (the form `ω` on pairs), then one contraction, then the projection
  -- `HodgeTatePair.contractionPow 0` of `⋀ M` to degree zero; with `D` below it is the class of the
  -- cocycle `D` (the form `ω`, then contraction along `f`), followed by that projection.
  change TotalH.comp (TotalH.homClass α)
      (TotalH.comp HodgeTatePair.contractionCocycle.cohomClass (HodgeTatePair.contractionPow 0)) = _
  let D : Cocycle (HodgeTatePair.pairAlg ⋙ N) HodgeTatePair.formCoeff :=
    ⟨fun {c d} f ↦ α.app c ≫ HodgeTatePair.contractionCocycle.component f,
      -- `↓`: without it, simp leaves the naturality square of `α` open.
      by simp [Cocycle.cocycle_comp, ↓NatTrans.naturality_assoc]⟩
  -- `α` carries `D` to the contraction cocycle (`New.Variety.Cocycle.cohomClass_naturality`).
  have h_nat : D.cohomClass.comp (TotalH.homClass (𝟙 _)) =
      pullbackAlong α HodgeTatePair.contractionCocycle.cohomClass :=
    D.cohomClass_naturality _ α (𝟙 _) fun c d f ↦ (Category.comp_id _).symm
  rw [comp_assoc_of_eq h_nat.symm, comp_id]
  refine Eq.trans ?_ (pullbackAlong_of _)
  -- A unit of `B ×_T (T ⊕ M)` has a first component in `Bˣ`, which lifts its image in `Tˣ`. By
  -- `Cocycle.cohomClass_comp_eq_extClass` it remains to check that this is a lift, and that its
  -- failure to be natural in the pair is the cocycle `D`, carried into `Bˣ`.
  refine Cocycle.cohomClass_comp_eq_extClass _
    (shortExact_oneSubMu.2.map_of_exact (restrictAlong _)) _ _
    (fun _ ↦ Gm.ofCoord _ ≫ Gm.map (CommRingCat.ofHom (.pullbackFst ..))) (fun X ↦ ?_)
    fun X Y f ↦ hom_ext (FreeAddCommGroup.lift_ext _ _ fun ⟨⟨v⟩, hv⟩ ↦ ?_)
  · -- On a point `(b, t)` of `B ×_T (T ⊕ M)`, `proj b` is the first component of `t`.
    simp [← Functor.map_comp]
    congr with ⟨⟨b, t⟩, h_pullback⟩
    exact h_pullback
  · -- On the unit `v 0 = a + m`, `ω` takes the value `w` with `a • w = m`. The lift at `Y` is
    -- the image under `f` of the lift at `X`, times `1 + mulMu t` for the contraction `t` of `w`.
    let y : (unimodular (d := 1)).toFunctor.obj (HodgeTatePair.pairAlg.obj X) := ⟨⟨v⟩, hv⟩
    let q := HodgeTatePair.toSqZero.app X
    let z := ((unimodular (d := 1)).toFunctor.map q) y
    obtain ⟨w, hw_smul, hω_app⟩ := hω (HodgeTatePair.toHodgeTest.obj X) z
    simp [D, α, ← Functor.map_comp]
    erw [AddMonoidHom.add_apply]
    iterate 4 erw [AddMonoidHom.comp_apply]
    have h_map : (N.map q).hom (.of y) =
        FreeAddCommGroup.of (((unimodular (d := 1)).toFunctor.map q) y) := by
      change FreeAddCommGroup.map _ (.of y) = _
      exact FreeAddCommGroup.map_of_apply y
    erw [h_map]
    erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    erw [hω_app, ← sub_eq_iff_eq_add', freeAb.desc_of, Gm.ext]
    change _ *
      (1 - mulMu (HodgeTatePair.toTest.obj Y)
        (-ExteriorAlgebra.algebraMapInv (contraction f.2 (.ι _ w)))) = _ + _
    -- `mulMu` is linear over `B` (`mulMu_proj_mul`); `v 0 = (b, a + m)` with `proj b = a` (the
    -- fibre product condition) and `m = a • w` (`hw_smul`).
    let a : X.GenericRing := (v 0).val.2.fst
    let m : Fin X.rank → X.GenericRing := (v 0).val.2.snd
    let w' : Fin X.rank → X.GenericRing := w
    change a • w' = m at hw_smul
    erw [freeAb.desc_of]
    have h_proj : (proj.app Y.test) (thickeningOver.map f.fst (v 0).val.fst) =
        genericOver.map f.fst a :=
      (proj.naturality_apply f.fst (v 0).val.fst).trans
        (congrArg (genericOver.map f.fst) (v 0).property)
    rw [mul_one_sub]
    let b : thickeningOver.obj X.test := (v 0).val.1
    let b' := thickeningOver.map f.fst b
    change b' - b' * mulMu Y.test (-ExteriorAlgebra.algebraMapInv
      (contraction f.snd (.ι _ w'))) = b' + mulMu Y.test (f.snd m).fst
    rw [← mulMu_proj_mul, h_proj]
    let a' : Y.GenericRing := genericOver.map f.fst a
    change b' - mulMu Y.test (a' * -ExteriorAlgebra.algebraMapInv
      (contraction f.snd (.ι _ w'))) = b' + mulMu Y.test (f.snd m).fst
    rw [← hw_smul, map_smulₛₗ]
    -- After unfolding `contraction`, both sides read `f b + mulMu (f a * f w)`, through maps of
    -- pairs that agree by definition.
    simp [contraction]
    rfl

/-- The Hodge–Tate map on `[dT / T]` in dimension one: `λ₁ [dT / T]` is the image under
`New.Variety.restrictToPairs` of a degree-two class on `p`-adic tests. This class is the Yoneda
product of the boundary class of the pair `(𝔸¹, 𝔸¹ ∖ 0)` (the extension class of
`0 → ℤ[𝔸¹ ∖ 0] → ℤ[𝔸¹] → ℤ[𝔸¹] / ℤ[𝔸¹ ∖ 0] → 0`, restricted to tests) with the class of the
extension `0 → T → Bˣ → Tˣ → 0` of `New.Variety.thickeningOver.shortExact_oneSubMu`, pulled back
along the coordinate `New.Variety.Gm.ofCoord`. -/
lemma hodgeTateMap_symbolClass :
    hodgeTateMap 1 symbolClass =
      restrictToPairs
        (relFreeAb.shortExact unimodular
          |>.2
          |>.map_of_exact (restrictAlong genericOver)
          |>.extClass.comp
            (H.map genericCoeff (genericOver.whiskerLeft Gm.ofCoord) 1
              shortExact_oneSubMu.2.extClass)
            rfl) := by
  -- Both sides are boundaries for the pair `(𝔸¹, 𝔸¹ ∖ 0)`, so it suffices to compare two degree-one
  -- classes on `𝔸¹ ∖ 0`: the contraction of `ω = dT / T` and the class of the extension of units
  -- pulled back along `Gm.ofCoord`. `hθ` says that the symbol is the boundary of `ω`.
  obtain ⟨ω, hω, hθ⟩ := symbolClass_one k
  -- Compose the comparison on `𝔸¹ ∖ 0` with the boundary class of the pair, which commutes with
  -- restriction (`New.Variety.Comparison.pull_comp_restrictAlong`), on the Hodge side and on the
  -- side of tests. Up to `hθ`, `h_chain` is the goal with `hodgeTateMap` and `restrictToPairs`
  -- unfolded.
  have h_chain := (comp_assoc_of_eq
      (Comparison.pull_comp_restrictAlong (relFreeAb.shortExact unimodular).2.extClass (.mk₀ ω)
        (rfl : 1 + 0 = 1)) _).symm.trans
    ((congrArg _ (pull_mk₀_comp_contractionPow_one_eq_pull_extClass_oneSubMu ω hω)).trans
      (Comparison.pull_comp_restrictAlong (relFreeAb.shortExact unimodular).2.extClass _
        (rfl : 1 + 1 = 2)))
  simpa [hθ, Abelian.Ext.mapExactFunctor_extClass, hodgeTateMap, restrictToPairs] using! h_chain

end New.Variety

end KummerSymbol

/-!
## The point class of the projective line

`New.Variety.hodgeTateMap h` is the Hodge–Tate map `λ_h` on Hodge cohomology.
`New.Variety.pointClass d z` is the class of a `k`-point `z`, and `New.Variety.cup` is the external
product of classes.
-/

section LinePointClass


namespace New.Variety

open CategoryTheory MvPolynomial TotalH PadicTest Period PerfectLine thickeningOver CommAlgCat
  WittVector Functor freeAb NNRat

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k]

/-- For a `p`-adic test `c` with ring `R`, in `B = W(R♭)[1/p] / (ker θ)²` the Teichmüller lift of
`ε` (`Period.epsTilt`, mapped to the tilt `R♭`) is `1 + μ`, where `μ = mulMu c 1` is the image of
`[ε] - 1`. -/
lemma thickeningOver.teichmullerLift_epsTilt (c : PadicTest) :
    teichmullerLift c (algebraMap OFlat (tilt.obj c) Period.epsTilt) = 1 + mulMu c 1 := by
  -- `mulMu c 1` is the image of `mu = [ε] - 1`, so it remains to compare the two lifts of `ε`.
  -- The lift `[·]` commutes with the map `O♭ → R♭`, and `W(O♭) → B` is `W(O♭) → W(R♭) → B`.
  have h_lift : teichmullerLift (k := k) c (algebraMap OFlat (tilt.obj c) epsTilt) =
      algebraMap (WittVector p OFlat) c.Thickening (teichmuller p epsTilt) :=
    congrArg (algebraMap (WittVector p c.TiltRing) c.Thickening) (map_teichmuller ..).symm
  have h_mu : mulMu c (1 : genericOver.obj c) = algebraMap Ainf c.Thickening mu :=
    (congrArg (mulMu c) c.thickeningProj.map_one).symm.trans
      ((mulMu_thickeningProj c 1).trans (mul_one _))
  refine h_lift.trans (Eq.trans ?_ (congrArg (fun z : c.Thickening ↦ 1 + z) h_mu).symm)
  simp only [mu_eq, _root_.map_sub, map_one]
  let x : c.Thickening := algebraMap Ainf c.Thickening (teichmuller p epsTilt)
  change x = 1 + (x - 1)
  rw [add_comm, sub_add_cancel]

/-- Let `V` be covered by charts of dimension one (`New.Variety.IsChartCovered 1 V`) and `U` an
open subfunctor of `V`. Then restriction from `p`-adic tests to Hodge–Tate pairs is bijective
(`New.Variety.PairRestrictBijective`) on the cohomology of `relFreeAb U = ℤ[V] / ℤ[U]`. -/
lemma pairRestrictBijective_relFreeAb_of_isOpenSubfunctor {V : CommAlg k ⥤ Type 1}
    {U : Subfunctor V} [hV : IsChartCovered 1 V] (hU : IsOpenSubfunctor U) :
    PairRestrictBijective (relFreeAb U) := by
  -- Two out of three in the sequence `0 → ℤ[U] → ℤ[V] → relFreeAb U → 0`: the property holds for
  -- `ℤ[V]`, and for `ℤ[U]` since `U` is again covered by charts.
  have hU_charts : IsChartCovered 1 U.toFunctor := hV.comap U.ι (by simpa using hU)
  have h_closed : IsClosedClass fun N : CommAlg k ⥤ AddCommGrpCat ↦ PairRestrictBijective N :=
    (Comparison.restrict HodgeTatePair.toTest genericCoeff).isClosedClass HodgeTatePair.toGeneric
  exact (h_closed.right _ (relFreeAb.shortExact U).2 hU_charts.pairRestrictBijective).mp
    hV.pairRestrictBijective

/-- On the chart `0` of the projective line (the points `[1 : x]`), the coordinate `X` cuts out the
point `affinePoint 0 0 = [1 : 0]`: a map `α` from the chart's ring to a `k`-algebra `C` kills `X`
exactly when it sends the chart's point to `[1 : 0]` (`New.Variety.CutsOutLocus`). -/
lemma projSpace.cutsOutLocus_stdChart_zero_X :
    CutsOutLocus (projSpace k 1) (ComesFromPoints {affinePoint 0 0}) (stdChart k 1 0).point X := by
  -- The image of the chart's point under `α` is `[1 : α X]`, which is `[1 : 0]` iff `α X = 0`.
  intro C α
  simp [ComesFromPoints]
  -- Both sides of the equation are points `[v]`; compare them by cross products.
  change _ ↔ projSpace.mk _ _ = projSpace.mk _ _
  refine Iff.trans ?_ mk_eq_mk_iff_cross_mul.symm
  simp +contextual
  change Ideal.span (Set.range X) ≤ RingHom.ker α.hom ↔
    0 = α.hom (X 0) ∧ α.hom (X 0) = 0
  constructor
  · intro h
    have h₀ : α.hom (X 0) = 0 := Ideal.span_le.mp h ⟨0, rfl⟩
    exact ⟨h₀.symm, h₀⟩
  · rintro ⟨_, h₀⟩
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [Subsingleton.elim i 0]
    exact h₀

/-- The points of the chart `1` of the projective line (the points `[x : 1]`) avoid
`affinePoint 0 0 = [1 : 0]`: for every map `ψ` from the chart's ring to `A`, the image of the
chart's point is zero in `ℤ[ℙ¹] / ℤ[ℙ¹ ∖ [1 : 0]]` (`New.Variety.relFreeAb` of
`New.Variety.offPoints`). -/
lemma projSpace.relFreeAb_mk_stdChart_one_eq_zero (A : CommAlg k)
    (ψ : (stdChart k 1 1).coordRing ⟶ A) :
    relFreeAb.mk (offPoints {affinePoint 0 0})
      ((projSpace k 1).map ψ (stdChart k 1 1).point) = 0 := by
  -- At a field `K`, a point of the chart `1` has a unit as its coordinate `1`, and `[1 : 0]` has
  -- `0` there.
  refine relFreeAb.mk_eq_zero ((offPoints _).map ψ ?_)
  rintro K φ hK ⟨z, rfl, h_eq⟩
  have : Nontrivial K := hK.nontrivial
  simpa using (mk_mem_stdChart_iff ..).mp ⟨_, h_eq⟩

/-- There is a degree-two class `ξT` in the cohomology on `p`-adic tests with coefficients
`genericCoeff` (a test with ring R ↦ R[1/p]) of ℤ[ℙ¹]/ℤ[`offPoints {affinePoint 0 0}`] composed with
`genericOver`. It satisfies two conditions. First, `hodgeTateMap 1` of the class of the point
`affinePoint 0 0 = [1 : 0]` of `ℙ¹` is `restrictToPairs` of the image of `ξT` in the cohomology of
ℤ[ℙ¹]. Second, the pull-back of `ξT` to the chart `stdChart k 1 0` equals the pull-back, along the
identification of that chart with the pair `(𝔸¹, 𝔸¹ ∖ 0)`, of the product of the boundary class of
`0 → ℤ[𝔸¹ ∖ 0] → ℤ[𝔸¹] → ℤ[𝔸¹]/ℤ[𝔸¹ ∖ 0] → 0` with the pull-back along `Gm.ofCoord` of the
degree-one class of the extension of units `thickeningOver.shortExact_oneSubMu`. -/
lemma projSpace.exists_relative_point_class :
    ∃ ξT : H (genericOver ⋙ relFreeAb (offPoints {affinePoint 0 0})) genericCoeff 2,
      hodgeTateMap 1 (pointClass 1 (affinePoint (k := k) (d := 1) 0 0)) =
        restrictToPairs
          (H.map genericCoeff (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})))
            2 ξT) ∧
      H.map genericCoeff
          (genericOver.whiskerLeft (relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) 2 ξT =
        H.map genericCoeff
          (genericOver.whiskerLeft
            (relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2
          (relFreeAb.shortExact (unimodular (k := k) (d := 1))
            |>.2
            |>.map_of_exact (restrictAlong genericOver)
            |>.extClass.comp
              (H.map genericCoeff (genericOver.whiskerLeft Gm.ofCoord) 1
                shortExact_oneSubMu.2.extClass)
              rfl) := by
  -- The class of the point comes from a relative class `ξ` that equals `[dX / X]` on the chart.
  obtain ⟨ξ, ⟨h_cut, h_chart, hξ_local⟩, hξ_point⟩ :
      ∃ ξ : HodgeH (relFreeAb (offPoints {affinePoint 0 0})) 1,
        IsLocalSymbol ξ (stdChart k 1 0).point (ComesFromPoints {affinePoint 0 0}) X 1 ∧
        IsPointSum {affinePoint 0 0} 1 ξ :=
    (stdChart k 1 0).exists_isLocalSymbol cutsOutLocus_stdChart_zero_X
      ((mk_mem_stdChart_iff _).mpr isUnit_one)
  obtain ⟨ξT, hξ⟩ : ∃ ξT, hodgeTateMap 1 ξ = restrictToPairs (n := 1 + 1) ξT :=
    (pairRestrictBijective_relFreeAb_of_isOpenSubfunctor
      isOpenSubfunctor_offPoints).exists_hodgeTateMap_eq 1 ξ
  refine ⟨ξT, ?_, ?_⟩
  · -- `ξ` has multiplicity `1` at the point, so it maps to the point class.
    have h_point : HodgeH.map (relFreeAb.π _) ξ = pointClass 1 (affinePoint 0 0) :=
      hξ_point.map_eq_smul_pointClass.trans (one_smul k _)
    rw [← h_point, hodgeTateMap_map, hξ, restrictToPairs_map]
  · -- `restrictToPairs` is injective on the chart. By `hξ` and `hodgeTateMap_symbolClass`, it sends
    -- the two sides of the goal to `λ₁` of the two sides of `hξ_local`.
    apply (pairRestrictBijective_relFreeAb_of_isOpenSubfunctor
      (hV := .comap _ (EtaleChart.isOpenSubfunctor _))
      (isOpenSubfunctor_offPoints.preimage _)).injective_restrictToPairs
    apply_fun hodgeTateMap 1 at hξ_local
    rw [one_smul, hodgeTateMap_map, hodgeTateMap_map, hξ, hodgeTateMap_symbolClass] at hξ_local
    rw [restrictToPairs_map]
    exact hξ_local.trans (restrictToPairs_map _ _).symm

/-- The Teichmüller lift is natural in the test: for a map `f : c ⟶ d` of `p`-adic tests,
`thickeningOver.map f` sends `[x]` to `[tilt.map f x]`. -/
private lemma thickeningOver.teichmullerLift_map {c d : PadicTest} (f : c ⟶ d) (x : tilt.obj c) :
    teichmullerLift d (tilt.map f x) = thickeningOver.map f (teichmullerLift c x) := by
  -- `with_unfolding_all`: only then is `thickeningOver.map f` seen as a map of localizations,
  -- which sends `[x]` to `[tilt.map f x]` by `WittVector.map_teichmuller`.
  with_unfolding_all
    exact congr(.mk _ $(.symm ((IsLocalization.map_eq (powers_le_comap_powers ..) _).trans
      (congrArg _ (map_teichmuller ..)))))

/-- The Teichmüller coordinate. For a `p`-adic test with ring `R`, a point `t` of the perfect disc
over the tilt is an `O♭`-algebra map `O♭[ℚ≥0] → R♭` with coordinate `u = t (T ^ 1)`; it goes to the
Teichmüller lift `[u]`, a point of the affine line over `B = W(R♭)[1/p] / (ker θ)²`. -/
def teichmullerCoordinate : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ thickeningOver ⋙ affineSpace k 1 :=
  ⟨fun c ↦ ↾fun t ↦ ⟨fun _ ↦ teichmullerLift c (t.down.hom (.single 1 1))⟩, fun c d f ↦ by
    ext t
    exact congrArg (fun b ↦ ULift.up fun (_ : Fin 1) ↦ b) (teichmullerLift_map f _)⟩

/-- On a point of the torus `O♭[ℚ] → R♭`, the Teichmüller coordinates at `u` and at `u⁻¹` multiply
to `1`. -/
lemma teichmullerCoordinate_mul_inv (c : PadicTest) (t : monoidAlg ℚ ⟶ tilt c) :
    (teichmullerCoordinate (k := k) c ⟨discToTorus coeHom ≫ t⟩).down 0 *
      (teichmullerCoordinate (k := k) c ⟨discToTorus (-coeHom) ≫ t⟩).down 0 = 1 := by
  have h_coord (g : ℚ≥0 →+ ℚ) :
      (discToTorus g ≫ t).hom (AddMonoidAlgebra.single 1 1) =
        t.hom (AddMonoidAlgebra.single (g 1) 1) := by
    change t.hom (AddMonoidAlgebra.mapDomain g (AddMonoidAlgebra.single 1 1)) = _
    exact congrArg t.hom (AddMonoidAlgebra.mapDomain_single ..)
  let liftCoord := (teichmullerLift (k := k) c).comp t.hom.toMonoidHom
  let u : AddMonoidAlgebra OFlat ℚ := .single 1 1
  let v : AddMonoidAlgebra OFlat ℚ := .single (-1) 1
  have h_mul : u * v = 1 := by
    simp [u, v, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  change teichmullerLift c ((discToTorus coeHom ≫ t).hom (.single 1 1)) *
    teichmullerLift c ((discToTorus (-coeHom) ≫ t).hom (.single 1 1)) = 1
  calc
    _ = liftCoord u * liftCoord v :=
      congrArg₂ (· * ·) (congrArg (teichmullerLift (k := k) c) (h_coord coeHom))
        (congrArg (teichmullerLift (k := k) c) (h_coord (-coeHom)))
    _ = liftCoord (u * v) := (liftCoord.map_mul u v).symm
    _ = 1 := (congrArg liftCoord h_mul).trans liftCoord.map_one

/-- Followed by the projection `B → T = R[1/p]`, the Teichmüller coordinate does not change when the
point is twisted by `charTwist`, which multiplies `u` by `ε` or by `ε⁻¹`. -/
lemma teichmullerCoordinate_comp_proj_charTwist (c : PadicTest) (i : Bool)
    (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c) :
    (teichmullerCoordinate ≫ whiskerRight proj (affineSpace k 1)) c
        ⟨charTwist epsPow (cond i coeHom (-coeHom)) ≫ t.down⟩ =
      (teichmullerCoordinate ≫ whiskerRight proj (affineSpace k 1)) c t := by
  -- The twist multiplies `[u]` by `[ε ^ (±1)]`, and `[ε] = 1 + mulMu c 1` maps to `1` under `proj`.
  let θ : Multiplicative ℚ →* genericOver.obj c :=
    (proj (k := k) c).hom.toRingHom.toMonoidHom.comp
      ((teichmullerLift c).comp ((algebraMap OFlat _).toMonoidHom.comp epsPow))
  let g : ℚ≥0 →+ ℚ := cond i coeHom (-coeHom)
  let sign : Multiplicative ℚ := .ofAdd (g 1)
  have h_eps : sign ∈ θ.ker := by
    cases i <;> simp [θ, sign, g, teichmullerLift_epsTilt, proj_mulMu]
  have h_twist : (charTwist epsPow g ≫ t.down).hom
      (AddMonoidAlgebra.single 1 1) =
        algebraMap OFlat (tilt.obj c) (epsPow sign) * t.down.hom (.single 1 1) := by
    change t.down.hom (AddMonoidAlgebra.lift OFlat (AddMonoidAlgebra OFlat ℚ≥0) ℚ≥0
      (((algebraMap OFlat (AddMonoidAlgebra OFlat ℚ≥0)).toMonoidHom.comp
        (epsPow.comp g.toMultiplicative)) *
        AddMonoidAlgebra.of OFlat ℚ≥0) (AddMonoidAlgebra.of OFlat ℚ≥0 (.ofAdd 1))) = _
    simp only [AddMonoidAlgebra.lift_of, MonoidHom.mul_apply, _root_.map_mul]
    exact congrArg (fun z ↦ z * t.down.hom (.single 1 1)) (t.down.hom.commutes (epsPow sign))
  apply ULift.down_injective
  funext j
  change proj c (teichmullerLift c ((charTwist epsPow g ≫
    t.down).hom (.single 1 1))) = proj c (teichmullerLift c (t.down.hom (.single 1 1)))
  let F : tilt.obj c →* genericOver.obj c :=
    (proj (k := k) c).hom.toRingHom.toMonoidHom.comp (teichmullerLift c)
  refine (congrArg F h_twist).trans ((map_mul F _ _).trans ?_)
  change θ sign * proj c (teichmullerLift c (t.down.hom (.single 1 1))) = _
  rw [θ.mem_ker.mp h_eps, one_mul]

/-- The Teichmüller coordinate `A = New.Variety.teichmullerCoordinate` with its three properties:
(a) its formula, (b) `[u] [u⁻¹] = 1` on the torus, (c) invariance under `charTwist` after the
projection to `R[1/p]`. -/
lemma exists_teichmuller_coordinate :
    ∃ A : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ thickeningOver ⋙ affineSpace k 1,
      -- (a)
      (∀ (c : PadicTest) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c),
        A c t = ⟨fun (_ : Fin 1) ↦ teichmullerLift c (t.down.hom (AddMonoidAlgebra.single 1 1))⟩) ∧
      -- (b)
      (∀ (c : PadicTest) (t : monoidAlg ℚ ⟶ tilt c),
        (A c ⟨discToTorus coeHom ≫ t⟩).down 0 * (A c ⟨discToTorus (-coeHom) ≫ t⟩).down 0 = 1) ∧
      -- (c)
      ∀ (c : PadicTest) (i : Bool) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c),
        (A ≫ whiskerRight proj (affineSpace k 1)) c
            ⟨charTwist epsPow (cond i coeHom (-coeHom)) ≫ t.down⟩ =
          (A ≫ whiskerRight proj (affineSpace k 1)) c t :=
  ⟨teichmullerCoordinate, fun _ _ ↦ rfl, teichmullerCoordinate_mul_inv,
    teichmullerCoordinate_comp_proj_charTwist⟩

/-- If `one` is a unit for `mult`, that is, `x ↦ x ⊗ one` followed by `mult` is the identity of `F`,
then pulling the class `x ⊗ F` followed by `mult` back along `S ↦ S ⊗ one` recovers `x`. -/
lemma pullbackAlong_tensorPoint_comp_eq_self {N F : AbFunctor PadicTest} [HasFlatValues F]
    (x : TotalH N F) {one : freeAb (onePointFunctor PadicTest) ⟶ F} {mult : abTensor F F ⟶ F}
    (h_unit : tensorPoint one F ≫ mult = 𝟙 F) :
    pullbackAlong (tensorPoint one N)
      (TotalH.comp (TotalH.map (abTensor.flip F) x) (TotalH.homClass mult)) = x := by
  -- `S ↦ S ⊗ one` is natural in `S`, so the pull-back moves past `x`; then `h_unit` applies.
  calc
    _ = TotalH.comp (TotalH.map (𝟭 _) x) (pullbackAlong (tensorPoint one F) (.homClass mult)) :=
      (TotalH.comp_assoc_of_sq (naturality ..) _).symm
    _ = x := by
      rw [TotalH.map_id, ← homClass_comp, h_unit]
      exact comp_id

/-- The class on `p`-adic tests that `λ₁` gives on the symbol `[dT/T]`
(`New.Variety.hodgeTateMap_symbolClass`): the boundary class of the pair `(𝔸¹, 𝔸¹ ∖ 0)` times the
class of the extension `0 → T → Bˣ → Tˣ → 0` of `New.Variety.thickeningOver.shortExact_oneSubMu`,
pulled back along `New.Variety.Gm.ofCoord`. -/
private def unitsExtClass :
    H (genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))) genericCoeff 2 :=
  ((relFreeAb.shortExact (unimodular (k := k) (d := 1))).2.map_of_exact
      (restrictAlong genericOver)).extClass.comp
    (H.map _ (genericOver.whiskerLeft Gm.ofCoord) 1 shortExact_oneSubMu.2.extClass) rfl

/-- Let `s` be a section of the map of pairs induced by the coordinate of the chart `0` of `ℙ¹`
(`h_section`), and let `ξT` restrict on the chart `0` to the pull-back of
`New.Variety.unitsExtClass` along that coordinate (`h_compare`). If `j'` lifts `j` followed by `s`
and the inclusion of the chart (`hj'`), then the pull-back of `unitsExtClass` along `j` is the
pull-back along `j'` of the image of `ξT` in `ℤ[ℙ¹]`. -/
private lemma projSpace.map_unitsExtClass_eq_map_of_comp_eq {B : AbFunctor PadicTest}
    {s : relFreeAb (unimodular (k := k) (d := 1)) ⟶
      relFreeAb ((offPoints {affinePoint 0 0}).preimage (pointMap (stdChart k 1 0).point))}
    (h_section : s ≫ relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le =
      𝟙 (relFreeAb (unimodular (d := 1))))
    {ξT : H (genericOver ⋙ relFreeAb (offPoints {affinePoint 0 0})) genericCoeff 2}
    (h_compare :
      H.map genericCoeff
          (genericOver.whiskerLeft (relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) 2 ξT =
        H.map genericCoeff
          (genericOver.whiskerLeft
            (relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2 unitsExtClass)
    {j : B ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    {j' : B ⟶ genericOver ⋙ freeAb.obj (projSpace k 1)}
    (hj' : j' ≫ genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})) =
      j ≫ genericOver.whiskerLeft (s ≫ relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) :
    H.map genericCoeff j 2 unitsExtClass =
      H.map genericCoeff j' 2
        (H.map genericCoeff (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})))
          2 ξT) := by
  -- `r` is the inclusion of the chart; `s` is a section of the coordinate map, so `ξT` pulls back
  -- to `unitsExtClass` along `s ≫ r`.
  let r : relFreeAb _ ⟶ relFreeAb (offPoints {affinePoint 0 0}) :=
    relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl
  have h_local : H.map genericCoeff (genericOver.whiskerLeft (s ≫ r)) 2 ξT = unitsExtClass :=
    calc
      _ = H.map genericCoeff
          (genericOver.whiskerLeft
            (s ≫ relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2 unitsExtClass := by
        rw [whiskerLeft_comp, H.map_comp, h_compare]
        exact (H.map_comp ..).symm
      _ = unitsExtClass := by rw [h_section, whiskerLeft_id', H.map_id]
  calc
    _ = H.map genericCoeff (j ≫ genericOver.whiskerLeft (s ≫ r)) 2 ξT := by
      rw [H.map_comp, h_local]
    _ = H.map genericCoeff
          (j' ≫ genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0}))) 2 ξT := by
      rw [hj']
    _ = _ := H.map_comp ..

/-- The map `j` of a Toda cancellation lifts through the projective line. Let `A` be a natural map
from the perfect disc to the affine line over `B` whose values at `u` and `u⁻¹` multiply to `1` on
the torus (`hA_inv`), and let its image `a` in `R[1/p]` be invariant under the twists of the two
discs (`hA_twist`). Let `(j, y, ω)` cancel `New.Variety.unitsExtClass` in the sense of
`New.Variety.IsTodaCancellation`, for the gluing of the two discs and the map induced by `a`. Let
`ξT` be a class on tests relative to the complement of `[1 : 0]` whose restriction to the chart `0`
is the pull-back of `unitsExtClass` along the coordinate (`h_compare`). Then the pull-back of
`unitsExtClass` along `j` is the pull-back along some `j'` of the image of `ξT` in `ℤ[ℙ¹]`. -/
private lemma projSpace.exists_map_eq_map_of_isTodaCancellation
    (A : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ thickeningOver ⋙ affineSpace k 1)
    (hA_inv : ∀ (c : PadicTest) (t : monoidAlg ℚ ⟶ tilt c),
      (A c ⟨discToTorus coeHom ≫ t⟩).down 0 * (A c ⟨discToTorus (-coeHom) ≫ t⟩).down 0 = 1)
    (hA_twist :
      ∀ (c : PadicTest) (i : ULift.{1} Bool) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c),
        (A ≫ whiskerRight proj (affineSpace k 1)) c ⟨discTwist epsPow i ≫ t.down⟩ =
          (A ≫ whiskerRight proj (affineSpace k 1)) c t)
    {B K Z₀ : AbFunctor PadicTest} {ε : Z₀ ⟶ genericCoeff} {y : Z₀ ⟶ K} {ω : TotalH B K}
    {j : B ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    (h_toda : IsTodaCancellation gluing (oneSub (discTwist epsPow))
      ((projFirst ≫ freeAb.map (A ≫ whiskerRight proj (affineSpace k 1))) ≫
        genericOver.whiskerLeft (relFreeAb.π unimodular))
      unitsExtClass ε j y ω)
    (ξT : H (genericOver ⋙ relFreeAb (offPoints {affinePoint 0 0})) genericCoeff 2)
    (h_compare :
      H.map genericCoeff
          (genericOver.whiskerLeft (relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) 2 ξT =
        H.map genericCoeff
          (genericOver.whiskerLeft
            (relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2 unitsExtClass) :
    ∃ j' : B ⟶ genericOver ⋙ freeAb.obj (projSpace k 1),
      H.map genericCoeff j 2 unitsExtClass =
        H.map genericCoeff j' 2
          (H.map genericCoeff (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})))
            2 ξT) := by
  let a : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ genericOver ⋙ affineSpace k 1 := A ≫ whiskerRight proj _
  -- `hA_twist` stated for the let `a`, the form in which `simp` meets it below.
  have ha_twist (c : PadicTest) (i : ULift.{1} Bool) (t) :
      a c ⟨discTwist epsPow i ≫ t.down⟩ = a c t :=
    hA_twist c i t
  -- `φ` maps the disc `true` to the chart `0` and the disc `false` to the chart `1`.
  let T : affineSpace k 1 ⟶ reprBy (stdChart k 1 0).coordRing :=
    ⟨fun _ ↦ ↾fun v ↦ ⟨ofHom (aeval v.down)⟩,
      fun _ _ _ ↦ by ext; congrm ⟨ofHom $((comp_aeval ..).symm)⟩⟩
  let φ : twoDiscs ⟶ genericOver ⋙ projSpace k 1 :=
    sigma.desc fun i ↦ a ≫ whiskerLeft _ (T ≫ pointMap (stdChart k 1 (cond i.down 0 1)).point)
  -- A unit `v` gives a point `[1 : v]` other than `[1 : 0]`; `r` is the inclusion of the chart `0`.
  let s :
      relFreeAb unimodular ⟶
        relFreeAb ((offPoints {affinePoint 0 0}).preimage (pointMap (stdChart k 1 0).point)) :=
    relFreeAb.map T fun _ v hv ↦ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.ge _
      (.trans (congrArg _ (congrArg _ (funext (aeval_X _)))) hv)
  let r :
      relFreeAb ((offPoints {affinePoint 0 0}).preimage (pointMap (stdChart k 1 0).point)) ⟶
        relFreeAb (offPoints {affinePoint 0 0}) :=
    relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl
  let F := freeAb.map φ - origin ⟨false⟩ twoDiscs ≫ freeAb.map φ
  have hF (c : PadicTest) (u : twoDiscs.obj c) :
      (F.app c).hom (.of u) = .of (φ c u) -
        .of (φ c ⟨⟨false⟩, ⟨evalZero (tilt.obj c)⟩⟩) := by
    let z : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero (tilt.obj c)⟩⟩
    have ho : ((origin ⟨false⟩ twoDiscs).app c).hom (.of u) = .of z := freeAb.desc_of ..
    let m := ((freeAb.map φ).app c).hom
    let o := ((origin ⟨false⟩ twoDiscs).app c).hom
    change (m - m.comp o) (.of u) = _
    exact (AddMonoidHom.sub_apply m (m.comp o) _).trans
      (congrArg₂ (· - ·) (freeAb.map_of ..) ((congrArg m ho).trans (freeAb.map_of ..)))
  -- The map `x ↦ [φ x] - [∞]` on the discs, `∞` the image of the origin of the disc `false`, lifts
  -- `j` to `j'` with values in `freeAb (projSpace k 1)`.
  obtain ⟨j', hj'⟩ :
      ∃ j',
        j' ≫ genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})) =
          j ≫ genericOver.whiskerLeft (s ≫ r) := by
    refine h_toda.exists_lift F _ _
      (hom_ext ?_) (hom_ext fun c t ↦ ?_) (hom_ext ?_)
    · -- The two charts are glued along `u ↦ u⁻¹`.
      rintro c ⟨⟨_ | _⟩, t⟩
      · let u : (tiltPointsSum pointOrTorus).obj c := ⟨⟨false⟩, t⟩
        change (F.app c).hom ((gluing.app c).hom (.of u)) = 0
        let z : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero (tilt.obj c)⟩⟩
        let z' : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero _ ≫ t.down⟩⟩
        have h_origin : z' = z :=
          congrArg (fun f ↦ (⟨⟨false⟩, ⟨f⟩⟩ : twoDiscs.obj c)) (evalZero_comp t.down)
        refine (congrArg (F.app c).hom (gluing_apply_point c t)).trans ((hF c z').trans ?_)
        exact sub_eq_zero.mpr (congrArg (fun v ↦ FreeAddCommGroup.of (φ c v)) h_origin)
      · let u : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, t⟩
        let u₀ : twoDiscs.obj c := ⟨⟨false⟩, ⟨discToTorus (-coeHom) ≫ t.down⟩⟩
        let u₁ : twoDiscs.obj c := ⟨⟨true⟩, ⟨discToTorus coeHom ≫ t.down⟩⟩
        have h_eq : φ c u₀ = φ c u₁ := by
          change projSpace.mk _ _ = projSpace.mk _ _
          apply mk_eq_mk_iff_cross_mul.mpr
          let b₀ := a c u₀.snd
          let b₁ := a c u₁.snd
          have h_mul : b₁.down 0 * b₀.down 0 = 1 := by
            change proj c ((A c u₁.snd).down 0) * proj c ((A c u₀.snd).down 0) = 1
            exact ((_root_.map_mul (proj c).hom _ _).symm.trans
              (congrArg (proj c).hom (hA_inv c t.down))).trans (map_one _)
          let v₀ : Fin 2 → MvPolynomial (Fin 1) k :=
            Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 1) k) 1 1 X
          let v₁ : Fin 2 → MvPolynomial (Fin 1) k :=
            Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 1) k) 0 1 X
          change ∀ i j, aeval b₀.down (v₀ i) * aeval b₁.down (v₁ j) =
            aeval b₁.down (v₁ i) * aeval b₀.down (v₀ j)
          have hv₀ : v₀ 0 = X 0 :=
            Fin.insertNth_apply_succAbove (α := fun _ ↦ MvPolynomial (Fin 1) k) 1 1 X 0
          have hv₀' : v₀ 1 = 1 :=
            Fin.insertNth_apply_same (α := fun _ ↦ MvPolynomial (Fin 1) k) 1 1 X
          have hv₁ : v₁ 0 = 1 :=
            Fin.insertNth_apply_same (α := fun _ ↦ MvPolynomial (Fin 1) k) 0 1 X
          have hv₁' : v₁ 1 = X 0 :=
            Fin.insertNth_apply_succAbove (α := fun _ ↦ MvPolynomial (Fin 1) k) 0 1 X 0
          -- Two of the four cross products are trivial, and the other two are `h_mul`.
          simp only [Fin.forall_fin_two, hv₀, hv₀', hv₁, hv₁', map_one, aeval_X, mul_one, one_mul,
            true_and, and_true]
          exact ⟨(mul_comm _ _).trans h_mul, h_mul.symm⟩
        change (F.app c).hom ((gluing.app c).hom (.of u)) = 0
        refine (congrArg (F.app c).hom (gluing_apply_torus c t)).trans ?_
        refine (_root_.map_sub (F.app c).hom _ _).trans ?_
        refine (congrArg₂ (· - ·) (hF c u₀) (hF c u₁)).trans ?_
        rw [h_eq, sub_self]
    · -- `φ` is invariant under the twist, by `ha_twist`.
      let t' : twoDiscs.obj c := ⟨t.fst, ⟨discTwist epsPow t.fst ≫ t.snd.down⟩⟩
      have h_twist : ((oneSub (discTwist epsPow)).app c).hom (.of t) =
          .of t - .of t' := freeAb.desc_of ..
      have h_eq : φ c t = φ c t' := by
        exact congrArg ((T ≫ pointMap (stdChart k 1 (cond t.fst.down 0 1)).point)
          (genericOver.obj c)) (ha_twist c t.fst t.snd).symm
      change (F.app c).hom (((oneSub (discTwist epsPow)).app c).hom (.of t)) = 0
      refine (congrArg (F.app c).hom h_twist).trans ?_
      refine (_root_.map_sub (F.app c).hom _ _).trans ?_
      refine (congrArg₂ (· - ·) (hF c t) (hF c t')).trans ?_
      rw [h_eq, sub_self]
    · -- Modulo the complement of the point, `∞` and the whole disc `false` vanish.
      intro c u
      let Z : Subfunctor (projSpace k 1) := offPoints {affinePoint 0 0}
      let C := genericOver.obj c
      let P := (relFreeAb.π Z).app C
      let J := (relFreeAb.π (unimodular (k := k) (d := 1))).app C
      let z : twoDiscs.obj c := ⟨⟨false⟩, ⟨evalZero (tilt.obj c)⟩⟩
      have hz : relFreeAb.mk Z (φ c z) = 0 := relFreeAb_mk_stdChart_one_eq_zero C _
      change P.hom ((F.app c).hom (.of u)) =
        (r.app C).hom ((s.app C).hom (J.hom (((freeAb.map a).app c).hom
          (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom (.of u)))))
      refine (congrArg P.hom (hF c u)).trans ((_root_.map_sub P.hom _ _).trans ?_)
      change relFreeAb.mk Z (φ c u) - relFreeAb.mk Z (φ c z) = _
      rw [hz, sub_zero]
      let descend := (r.app C).hom.comp ((s.app C).hom.comp
        (J.hom.comp ((freeAb.map a).app c).hom))
      obtain ⟨⟨_ | _⟩, t⟩ := u
      · refine Eq.trans (relFreeAb_mk_stdChart_one_eq_zero C _) ?_
        symm
        refine (congrArg descend
          (projFirst_false (B := fun _ ↦ monoidAlg ℚ≥0) c t)).trans ?_
        exact map_zero descend
      · refine Eq.trans ?_ (congrArg
          descend
          (projFirst_true (B := fun _ ↦ monoidAlg ℚ≥0) c t)).symm
        have h_map : ((freeAb.map a).app c).hom (.of t) =
            FreeAddCommGroup.of (a c t) := freeAb.map_of ..
        exact (congrArg (fun x ↦ (r.app C).hom ((s.app C).hom (J.hom x))) h_map).symm
  -- `T` is a section of the coordinate map.
  have h_section : s ≫ relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le = 𝟙
    _ :=
    relFreeAb.hom_ext fun _ _ ↦ congrArg (relFreeAb.mk unimodular ⟨·⟩) (funext (aeval_X _))
  exact ⟨j', map_unitsExtClass_eq_map_of_comp_eq h_section h_compare hj'⟩

/-- Let `(j, y, ω)` cancel `New.Variety.unitsExtClass` in the sense of
`New.Variety.IsTodaCancellation`, for the gluing of the two perfect discs, where `ε` sends the point
to a unit for the multiplication of `R[1/p]` (`h_unit`). If the pull-back of `unitsExtClass` along
`j` is the pull-back of `η` along `j'` (`h_pull`), then for `N` with flat values and `x` in
`H^n(N, R[1/p])`, the product `x × η` vanishes only if `x = 0`. -/
private lemma eq_zero_of_cup_eq_zero_of_isTodaCancellation {B K : AbFunctor PadicTest}
    {q : freeAb twoDiscs ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    {ε : freeAb (onePointFunctor PadicTest) ⟶ genericCoeff}
    {j : B ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    {y : freeAb (onePointFunctor PadicTest) ⟶ K} {ω : TotalH B K}
    (h_toda : IsTodaCancellation gluing (oneSub (discTwist epsPow)) q unitsExtClass ε j y ω)
    (h_unit :
      tensorPoint ε genericCoeff ≫
          (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing =
        𝟙 genericCoeff)
    {η : H (genericOver ⋙ freeAb.obj (projSpace k 1)) genericCoeff 2}
    {j' : B ⟶ genericOver ⋙ freeAb.obj (projSpace k 1)}
    (h_pull : H.map genericCoeff j 2 unitsExtClass = H.map genericCoeff j' 2 η)
    {N : AbFunctor PadicTest} [HasFlatValues N] {n : ℕ} (x : H N genericCoeff n)
    (hx : cup (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing x η (add_comm 2 n) =
      0) :
    x = 0 := by
  -- Apply `h_toda` to `Φ = N ⊗ -` and `m`, the class `x ⊗ genericCoeff` followed by multiplication:
  -- its product with `j^* unitsExtClass` is the pull-back along `j'` of `x × η = 0`.
  let Φ : AbFunctor PadicTest ⥤ AbFunctor PadicTest := abTensor N
  let mult : abTensor genericCoeff genericCoeff ⟶ genericCoeff :=
    (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing
  let m : TotalH (Φ genericCoeff) genericCoeff :=
    TotalH.comp (TotalH.map (abTensor.flip genericCoeff) x.toTotalH) (.homClass mult)
  have h_zero :
      pullbackAlong (Φ.map j) (TotalH.comp (TotalH.map Φ unitsExtClass.toTotalH) m) = 0 :=
    calc
      _ = TotalH.comp (TotalH.map Φ (pullbackAlong j unitsExtClass.toTotalH)) m := by
        rw [TotalH.map_comp_assoc, map_homClass]
      _ = TotalH.comp (TotalH.map Φ (pullbackAlong j' η.toTotalH)) m := by
        rw [Abelian.Ext.toTotalH, Abelian.Ext.toTotalH, pullbackAlong_of, pullbackAlong_of, h_pull]
      _ = pullbackAlong (Φ.map j') (TotalH.comp (TotalH.map Φ η.toTotalH) m) := by
        rw [TotalH.map_comp_assoc, map_homClass]
      _ = pullbackAlong (Φ.map j') (cup mult x η (add_comm 2 n)).toTotalH :=
        congrArg _ ((comp_assoc_of_eq rfl _).trans (cup_of ..))
      _ = 0 := by
        rw [hx]
        exact (congrArg _ (map_zero _)).trans (map_zero _)
  -- Pulling `m` back along `S ↦ S ⊗ ε` recovers `x`, and by `h_toda` this pull-back is zero;
  -- `subsingleton_H_cokernel_gluing` gives the acyclicity of the cokernel of the gluing that it
  -- needs.
  have h_vanish : pullbackAlong (tensorPoint ε N) m = 0 :=
    (h_toda.pullbackAlong_comp_map_eq Φ (subsingleton_H_cokernel_gluing isCohomEquiv_gluing_generic
      N)
      (tensorPoint (𝟙 _) _) m 0 (h_zero.trans (map_zero _).symm)).trans (map_zero _)
  rw [pullbackAlong_tensorPoint_comp_eq_self x.toTotalH h_unit] at h_vanish
  exact DirectSum.of_injective n (h_vanish.trans (map_zero _).symm)

private lemma teichmullerCoordinate_cancel_twist (c : PadicTest)
    (t : monoidAlg ℚ ⟶ tilt.obj c) :
    (1 - mulMu c (1 : genericOver (k := k) |>.obj c)) *
        teichmullerLift c ((discToTorus NNRat.coeHom ≫ charTwist epsPow (AddMonoidHom.id ℚ) ≫ t).hom
          (AddMonoidAlgebra.single 1 1)) =
      teichmullerLift c ((discToTorus NNRat.coeHom ≫ t).hom (AddMonoidAlgebra.single 1 1)) := by
  let q : AddMonoidAlgebra OFlat ℚ := AddMonoidAlgebra.single 1 1
  let s : AddMonoidAlgebra OFlat ℚ≥0 := AddMonoidAlgebra.single 1 1
  have h_disc : (discToTorus NNRat.coeHom).hom s = q := by
    change AddMonoidAlgebra.mapDomain NNRat.coeHom s = q
    rw [AddMonoidAlgebra.mapDomain_single]
    rfl
  have h_twist : (charTwist epsPow (AddMonoidHom.id ℚ)).hom q =
      algebraMap OFlat (AddMonoidAlgebra OFlat ℚ) epsTilt * q := by
    change AddMonoidAlgebra.lift OFlat (AddMonoidAlgebra OFlat ℚ) ℚ
      (((algebraMap OFlat (AddMonoidAlgebra OFlat ℚ)).toMonoidHom.comp epsPow) *
        AddMonoidAlgebra.of OFlat ℚ) (AddMonoidAlgebra.of OFlat ℚ (.ofAdd 1)) = _
    rw [AddMonoidAlgebra.lift_of, MonoidHom.mul_apply, MonoidHom.comp_apply, epsPow_one]
    rfl
  change (1 - mulMu c _) * teichmullerLift c
      (t.hom ((charTwist epsPow (AddMonoidHom.id ℚ)).hom ((discToTorus NNRat.coeHom).hom s))) =
    teichmullerLift c (t.hom ((discToTorus NNRat.coeHom).hom s))
  rw [h_disc, h_twist, _root_.map_mul, t.hom.commutes, _root_.map_mul, teichmullerLift_epsTilt]
  let μ : thickeningOver (k := k) |>.obj c := mulMu c 1
  let u : thickeningOver (k := k) |>.obj c := teichmullerLift c (t.hom q)
  change (1 - μ) * ((1 + μ) * u) = u
  have h_sq : μ * μ = 0 := by
    change mulMu c 1 * mulMu c 1 = 0
    rw [← mulMu_proj_mul, proj_mulMu, zero_mul, map_zero]
  have h_cancel : (1 - μ) * (1 + μ) = 1 := by
    calc
      _ = 1 - μ * μ := by ring
      _ = 1 := by rw [h_sq, sub_zero]
  rw [← mul_assoc, h_cancel, one_mul]

/-- Let `k` be a field of characteristic `0` with an embedding in `ℚ̄_p`. There is a degree-two
cohomology class `η` of the functor `S ↦ ℤ[ℙ¹(S[1/p])]` on `p`-adic tests `S` (with ring `R`,
written `S[1/p] = R[1/p]`), with coefficients `S ↦ R[1/p]` (`genericCoeff`), such that the following
hold. (a) The Hodge–Tate map `hodgeTateMap 1` sends the class of the point `[1 : 0]` to
`restrictToPairs η`. (b) For every functor `N` from `p`-adic tests to abelian groups with flat
values and every `x` in the degree-`n` cohomology of `N` with coefficients `R[1/p]`, the cup product
of `x` and `η` (paired by multiplication in `R[1/p]`) vanishes only if `x = 0`. -/
lemma projSpace.exists_hodgeTateMap_pointClass_line :
    ∃ η : H (genericOver ⋙ freeAb.obj (projSpace k 1)) genericCoeff 2,
    -- (a)
    hodgeTateMap 1 (pointClass 1 (affinePoint (k := k) (d := 1) 0 0)) = restrictToPairs η ∧
    -- (b)
    ∀ {N : AbFunctor PadicTest} {n : ℕ} [HasFlatValues N] (x : H N genericCoeff n),
      cup (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing x η (add_comm 2 n) = 0 →
        x = 0 := by
  -- `hodgeTateMap 1` of the point comes from `unitsExtClass`; `exists_isTodaCancellation`, for two
  -- perfect discs mapping to the charts of `ℙ¹`, gives a map `j` along which `unitsExtClass` comes
  -- from `η`, and `x × η = 0` then forces `x = 0`.
  obtain ⟨ξT, h_point, h_compare⟩ := exists_relative_point_class (k := k)
  let η : H (genericOver ⋙ freeAb.obj (projSpace k 1)) genericCoeff 2 :=
    H.map _ (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0}))) 2 ξT
  refine ⟨η, h_point, fun {N n} _ x hx ↦ ?_⟩
  -- `A` sends `u` to `[u]`; its image `a` in `R[1/p]` is invariant under the twist `charTwist`.
  obtain ⟨A, hA, hA_inv, hA_twist⟩ := exists_teichmuller_coordinate (k := k)
  let a : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ genericOver ⋙ affineSpace k 1 := A ≫ whiskerRight proj _
  have ha_twist (c : PadicTest) (i : ULift.{1} Bool) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c) :
      a c ⟨discTwist epsPow i ≫ t.down⟩ = a c t := by
    obtain ⟨_ | _⟩ := i
    exacts [hA_twist c false t, hA_twist c true t]
  -- On the torus `[u]` is a unit, so a point of `unimodular` over `thickeningOver`; `W` kills the
  -- extra point of `pointOrTorus`.
  let torusPoint (c : PadicTest) (t : (tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
      (unimodular (d := 1)).toFunctor.obj (thickeningOver.obj c) :=
    ⟨A c ⟨discToTorus coeHom ≫ t.down⟩,
      span_eq_top_of_isUnit 0 (.of_mul_eq_one _ (hA_inv c t.down))⟩
  let W :
      freeAb (tiltPointsSum pointOrTorus) ⟶
        thickeningOver ⋙ freeAb (unimodular (k := k) (d := 1)).toFunctor :=
    projFirst ≫ desc (fun c t ↦ .of (torusPoint c t))
      fun _ _ f _ ↦ .symm congr(.of $(Subtype.ext (A.naturality_apply ..).symm))
  have h_W_false (c : PadicTest) (t : (tilt ⋙ reprBy (CommAlgCat.of OFlat OFlat)).obj c) :
      (W.app c).hom (.of (⟨⟨false⟩, t⟩ : (tiltPointsSum pointOrTorus).obj c)) = 0 := by
    let u : (tiltPointsSum pointOrTorus).obj c := ⟨⟨false⟩, t⟩
    change (FreeAddCommGroup.lift (fun t ↦ FreeAddCommGroup.of (torusPoint c t)))
      (((projFirst (B := pointOrTorus)).app c).hom (.of u)) = 0
    exact (congrArg (FreeAddCommGroup.lift (fun t ↦ FreeAddCommGroup.of (torusPoint c t)))
      (projFirst_false (B := pointOrTorus) c t)).trans (map_zero _)
  have h_W_true (c : PadicTest) (t : (tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
      (W.app c).hom (.of (⟨⟨true⟩, t⟩ : (tiltPointsSum pointOrTorus).obj c)) =
        .of (torusPoint c t) := by
    let u : (tiltPointsSum pointOrTorus).obj c := ⟨⟨true⟩, t⟩
    change (FreeAddCommGroup.lift (fun t ↦ FreeAddCommGroup.of (torusPoint c t)))
      (((projFirst (B := pointOrTorus)).app c).hom (.of u)) = _
    exact (congrArg (FreeAddCommGroup.lift (fun t ↦ FreeAddCommGroup.of (torusPoint c t)))
      (projFirst_true (B := pointOrTorus) c t)).trans (FreeAddCommGroup.lift_apply_of ..)
  -- `one` sends every point to the unit of `genericAlg`.
  let one {X : PadicTest ⥤ Type 1} : freeAb X ⟶ genericCoeff :=
    desc (fun c _ ↦ ⟨(1 : genericAlg c)⟩) fun _ _ _ _ ↦
      congrArg _ (map_one (genericAlg.map _).hom').symm
  let f : freeAb twoDiscs ⟶ genericOver ⋙ freeAb.obj (affineSpace k 1) :=
    projFirst ≫ freeAb.map a
  have h_f_false (c : PadicTest) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c) :
      (f.app c).hom (.of (⟨⟨false⟩, t⟩ : twoDiscs.obj c)) = 0 := by
    let u : twoDiscs.obj c := ⟨⟨false⟩, t⟩
    change ((freeAb.map a).app c).hom
      (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom (.of u)) = 0
    exact (congrArg ((freeAb.map a).app c).hom
      (projFirst_false (B := fun _ ↦ monoidAlg ℚ≥0) c t)).trans (map_zero _)
  have h_f_true (c : PadicTest) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c) :
      (f.app c).hom (.of (⟨⟨true⟩, t⟩ : twoDiscs.obj c)) =
        FreeAddCommGroup.of (a c t) := by
    let u : twoDiscs.obj c := ⟨⟨true⟩, t⟩
    change ((freeAb.map a).app c).hom
      (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom (.of u)) = _
    exact (congrArg ((freeAb.map a).app c).hom
      (projFirst_true (B := fun _ ↦ monoidAlg ℚ≥0) c t)).trans (freeAb.map_of ..)
  have h_origin : origin ⟨true⟩ ≫ oneSub (discTwist epsPow) = 0 := by
    refine freeAb.hom_ext fun c t ↦ ?_
    let z : twoDiscs.obj c := ⟨⟨true⟩, ⟨evalZero (tilt.obj c)⟩⟩
    let z' : twoDiscs.obj c :=
      ⟨⟨true⟩, ⟨discTwist epsPow ⟨true⟩ ≫ evalZero (tilt.obj c)⟩⟩
    have ho : ((origin ⟨true⟩).app c).hom (.of t) = .of z := freeAb.desc_of ..
    have hd : ((oneSub (discTwist epsPow)).app c).hom (.of z) = .of z - .of z' :=
      freeAb.desc_of ..
    have hz : z' = z := by
      exact congrArg (fun w ↦ (⟨⟨true⟩, ⟨w⟩⟩ : twoDiscs.obj c))
        (charTwist_comp_evalZero ..)
    change ((oneSub (discTwist epsPow)).app c).hom (((origin ⟨true⟩).app c).hom (.of t)) = 0
    erw [ho, hd, hz, sub_self]
  let κ : freeAb twoDiscs ⟶ genericCoeff := projFirst ≫ one
  have h_κ (c : PadicTest) (b : Bool) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c) :
      (κ.app c).hom (.of (⟨⟨b⟩, t⟩ : twoDiscs.obj c)) =
        if b then ⟨(1 : genericAlg c)⟩ else 0 := by
    let u : twoDiscs.obj c := ⟨⟨b⟩, t⟩
    change (one.app c).hom (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom (.of u)) = _
    cases b
    · exact (congrArg (one.app c).hom
        (projFirst_false (B := fun _ ↦ monoidAlg ℚ≥0) c t)).trans (map_zero _)
    · exact (congrArg (one.app c).hom
        (projFirst_true (B := fun _ ↦ monoidAlg ℚ≥0) c t)).trans (freeAb.desc_of ..)
  -- `exists_isTodaCancellation` for the gluing, with `δ`, `δ'` one minus the twist and `origin`
  -- that of the disc `true`; `h_toda` says that `j^* (unitsExtClass m) = 0` kills the pull-back of
  -- `m` along `one`.
  obtain ⟨B, K, j, y, ω, h_toda⟩ := by
    refine exists_isTodaCancellation (oneSub_comp_gluing epsPow) (origin ⟨true⟩)
      h_origin
      ((relFreeAb.shortExact unimodular).2.map_of_exact (restrictAlong _)) shortExact_oneSubMu.2
        (f := f)
      (α := (-W) ≫ whiskerLeft _ Gm.ofCoord) (κ := κ) (n := whiskerLeft _ Gm.ofCoord)
      (α₁ := (-W) ≫ whiskerRight proj _) (freeAb.hom_ext ?_) (freeAb.hom_ext ?_) (freeAb.hom_ext ?_)
        (freeAb.hom_ext ?_)
    · -- Both sides send a point `u` of the torus to `-[a u]`.
      intro c u
      let D := (freeAb.obj (unimodular (d := 1)).toFunctor).map (proj.app c)
      let I := (freeAb.map (unimodular (d := 1)).ι).app (genericOver.obj c)
      change I.hom (D.hom (((-W).app c).hom (.of u))) =
        (f.app c).hom ((gluing.app c).hom (.of u))
      erw [NatTrans.app_neg, AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply]
      obtain ⟨⟨_ | _⟩, t⟩ := u
      · erw [h_W_false, gluing_apply_point c t, h_f_false]
      · have h_D : D.hom (.of (torusPoint c t)) =
            FreeAddCommGroup.of (((unimodular (d := 1)).toFunctor.map (proj.app c))
                (torusPoint c t)) := by
          change FreeAddCommGroup.map _ (.of (torusPoint c t)) = _
          exact FreeAddCommGroup.map_of_apply _
        erw [h_W_true, gluing_apply_torus c t, _root_.map_sub, h_f_false, h_f_true, zero_sub,
          _root_.map_neg, _root_.map_neg, h_D, freeAb.map_of]
        rfl
    · -- `a` is invariant under the twist.
      intro c u
      let u' : twoDiscs.obj c := ⟨u.fst, ⟨discTwist epsPow u.fst ≫ u.snd.down⟩⟩
      have hd : ((oneSub (discTwist epsPow)).app c).hom (.of u) = .of u - .of u' :=
        freeAb.desc_of ..
      change (f.app c).hom (((oneSub (discTwist epsPow)).app c).hom (.of u)) = 0
      erw [hd, _root_.map_sub]
      obtain ⟨⟨_ | _⟩, t⟩ := u
      · erw [h_f_false, sub_zero]
      · erw [h_f_true, h_f_true, ha_twist, sub_self]
    · -- With `μ = mulMu c 1`, which has square zero:
      -- `(1 - μ) * [ε * u] = (1 - μ) * (1 + μ) * [u] = [u]`.
      intro c u
      let G := Gm.ofCoord.app (thickeningOver.obj c)
      let T := (oneSub (pointOrTorusTwist epsPow)).app c
      let u' : (tiltPointsSum pointOrTorus).obj c :=
        ⟨u.fst, ⟨pointOrTorusTwist epsPow u.fst ≫ u.snd.down⟩⟩
      have ht : T.hom (.of u) = .of u - .of u' := freeAb.desc_of ..
      change G.hom (((-W).app c).hom (T.hom (.of u))) =
        (oneSubMu.app c).hom ((κ.app c).hom ((gluing.app c).hom (.of u)))
      erw [NatTrans.app_neg, AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply, ht, _root_.map_sub, _root_.map_neg, _root_.map_sub, neg_sub]
      obtain ⟨⟨_ | _⟩, t⟩ := u
      · erw [h_W_false, gluing_apply_point c t, h_κ]
        rw [sub_self]
        change 0 = (oneSubMu.app c).hom 0
        exact (map_zero (oneSubMu.app c).hom).symm
      · let t' : (tilt ⋙ reprBy (monoidAlg ℚ)).obj c :=
          ⟨charTwist epsPow (AddMonoidHom.id ℚ) ≫ t.down⟩
        have h_W_twist : (W.app c).hom (.of u') = .of (torusPoint c t') :=
          h_W_true c t'
        erw [gluing_apply_torus c t, _root_.map_sub (κ.app c).hom, h_κ c false, h_κ c true,
          h_W_true c t, h_W_twist]
        apply neg_injective
        rw [neg_sub]
        let one_c : genericCoeff.obj c := ⟨(1 : genericAlg c)⟩
        change G.hom (.of (torusPoint c t)) - G.hom (.of (torusPoint c t')) =
          -((oneSubMu.app c).hom (0 - one_c))
        rw [zero_sub, _root_.map_neg, neg_neg]
        refine sub_eq_of_eq_add (Gm.ext.2 (.symm ?_))
        change (1 - mulMu c _) * _ = _
        erw [desc_of, desc_of, IsUnit.unit_spec, IsUnit.unit_spec]
        have h_coord (u : (tilt ⋙ reprBy (monoidAlg ℚ)).obj c) :
            (torusPoint c u).val.down 0 =
              teichmullerLift c ((discToTorus coeHom ≫ u.down).hom (.single 1 1)) :=
          congrArg (fun a ↦ a.down 0) (hA c ⟨discToTorus coeHom ≫ u.down⟩)
        rw [h_coord t', h_coord t]
        exact teichmullerCoordinate_cancel_twist c t.down
    · -- `Gm.ofCoord` commutes with `proj`.
      intro c u
      let e : (freeAb.obj (tiltPointsSum pointOrTorus)).obj c := .of u
      let v := ((-W).app c).hom e
      exact Gm.ofCoord.naturality_apply (proj.app c) v
  obtain ⟨j', h_pull⟩ :=
    exists_map_eq_map_of_isTodaCancellation A hA_inv ha_twist h_toda ξT h_compare
  -- The point goes to `1`, a unit for the multiplication of `R[1/p]`.
  have h_unit :
      tensorPoint (origin ⟨true⟩ ≫ projFirst ≫ one) genericCoeff ≫
          (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing =
        𝟙 genericCoeff := by
    ext c ⟨x⟩
    let o : twoDiscs.obj c := ⟨⟨true⟩, ⟨evalZero (tilt.obj c)⟩⟩
    have ho : ((origin ⟨true⟩).app c).hom (.of PUnit.unit) = .of o := freeAb.desc_of ..
    have h_one : (one.app c).hom (.of o.snd) = ⟨(1 : genericAlg c)⟩ := freeAb.desc_of ..
    let x' : genericAlg c := x
    let y : genericAlg c := ((one.app c).hom (((projFirst (B := fun _ ↦ monoidAlg ℚ≥0)).app c).hom
      (((origin ⟨true⟩).app c).hom (.of PUnit.unit)))).down
    change ULift.up (x' * y) = ULift.up x'
    have hy : y = 1 := by
      dsimp only [y]
      erw [ho, projFirst_true (B := fun _ ↦ monoidAlg ℚ≥0) c o.snd, h_one]
    rw [hy, mul_one]
  exact eq_zero_of_cup_eq_zero_of_isTodaCancellation h_toda h_unit h_pull x hx

end New.Variety

end LinePointClass

/-! ## Point classes of projective space -/

section ProjectivePointClass

open CategoryTheory Finset CartesianMonoidalCategory CommAlgCat Fin Polynomial


/-- All `k`-points of projective space have the same class: a global function takes the same value
at all of them. -/
lemma New.Variety.projSpace.pointClass_eq_pointClass_affinePoint {k : Type} [Field k] [CharZero k]
    {d : ℕ} (z : (projSpace k d).obj (of k k)) :
    pointClass d z = pointClass d (affinePoint 0 0 : (projSpace k d).obj (of k k)) := by
  obtain ⟨⟨u⟩, hu⟩ := z
  refine pointClass_eq_of_functions_eq fun g ↦ ?_
  -- `val x` is the value of `g` at a point `x`; it commutes with algebra maps.
  let val {A : CommAlg k} (x : (projSpace k d).obj A) : A := (g.app A x).down 0
  have val_map {A B : CommAlg k} (ψ : A ⟶ B) (x : (projSpace k d).obj A) (y : (projSpace k d).obj B)
      (hy : y = (projSpace k d).map ψ x) : val y = ψ (val x) := by
    subst hy
    exact congrArg (fun a ↦ a.down 0) (g.naturality_apply ψ x)
  by_cases h : ∃ j, u (succ j) ≠ 0
  swap
  · -- If all coordinates but the first vanish, the point is `affinePoint 0 0`.
    simp only [not_exists, not_not] at h
    refine val_map (𝟙 _) _ _ (mk_eq_mk_iff_cross_mul.mpr ?_)
    simp [forall_fin_succ, h]
  -- The line through the two points is covered by the `k[X]`-points `x = [X : u₁ : ⋯]` and
  -- `x' = [1 : u₁ X : ⋯]`, which agree over `k[X, X⁻¹]` after `X ↦ X⁻¹`.
  obtain ⟨j, hj⟩ := h
  have h_unit : IsUnit ((cons X (C ∘ u ∘ succ) : Fin (d + 1) → k[X]) j.succ) := by simpa using hj
  let x : (projSpace k d).obj (of k k[X]) :=
    mk (cons X (C ∘ u ∘ succ)) (span_eq_top_of_isUnit j.succ h_unit)
  let x' : (projSpace k d).obj (of k k[X]) := affinePoint 0 (monomial 1 ∘ u ∘ succ)
  have glue : toLaurent (val x) = LaurentPolynomial.invert (toLaurent (val x')) := by
    refine (val_map (ofHom toLaurentAlg) x _ (mk_eq_mk_iff_cross_mul.mpr ?_)).symm.trans
      (val_map (ofHom (LaurentPolynomial.invert.toAlgHom.comp toLaurentAlg)) x' _ rfl)
    simp [forall_fin_succ]
    grind
  -- `P(T) = Q(T⁻¹)` forces `P` and `Q` to be one constant.
  obtain ⟨c, val_x, val_x'⟩ : ∃ c : k, val x = C c ∧ val x' = C c :=
    eq_C_of_toLaurent_eq _ _ glue
  -- The first point is `x` at `X = u 0`, the second is `x'` at `X = 0`.
  have hx_eval : mk u hu = (projSpace k d).map (ofHom (aeval (u 0))) x :=
    mk_eq_mk_iff_cross_mul.mpr (by simp [forall_fin_succ])
  have hx'_eval : affinePoint 0 0 = (projSpace k d).map (ofHom (aeval (0 : k))) x' :=
    mk_eq_mk_iff_cross_mul.mpr (by simp [forall_fin_succ])
  calc
    val (mk u hu) = aeval (u 0) (val x) := val_map (ofHom (aeval (u 0))) x _ hx_eval
    _ = aeval 0 (val x') := by simp [val_x, val_x']
    _ = val (affinePoint 0 0) := (val_map (ofHom (aeval 0)) x' _ hx'_eval).symm

/-- Let `k` be a field of characteristic zero with an embedding in `ℚ̄_p`, and let `X` be a functor
on `k`-algebras with an atlas of dimension `d` (separated, with finitely many charts, each having
`d` étale coordinates, that together contain every field-valued point). For a `k`-point `z` of `X`,
the class `pointClass d z` of `z` in degree-`d` Hodge cohomology is killed by `hodgeTateMap l` for
every `l ≠ d`. -/
lemma New.Variety.hodgeTateMap_pointClass_eq_zero_of_ne {p : ℕ} {k : Type} [Field k]
    [EmbeddedInQpBar p k] {d l : ℕ}
    {X : CommAlg k ⥤ Type 1} [hX : HasAtlas d X] (z : X.obj (of k k)) (hl : l ≠ d) :
    hodgeTateMap l (pointClass (X := X) d z) = 0 := by
  -- By the fixed point formula for the identity and the constant map `z`, one class `x` has
  -- `HodgeH.scale t x = t ^ d • pointClass d z` for all `t`. Compare `t = 1` and `t = 2` under
  -- `hodgeTateMap l`, which turns `HodgeH.scale t` into `t ^ l` (`hodgeTateMap_scale`).
  obtain ⟨δ, hδ⟩ := exists_diagonal_map_scaledGraph_eq_sum_pointClass hX
  have h_coincidence : IsCoincidenceSet (𝟙 X) (constMap z) {z} := by
    simp [IsCoincidenceSet, ConstIfCoincident, constMap, map_map_structureMap (k := k)]
  have h_jacobian (t : k) (w : X.obj (of k k)) :
      HasJacobianRatio (E := k) (𝟙 X) (constMap z) d t (Matrix.scalar (Fin d) t).det w := by
    refine fun A _ ↦ ⟨.scalar _ t, rfl, fun _ _ γ _ _ hγ ↦ ?_⟩
    rw [A.eq_comp_of_map_point_eq _ (h_coincidence.1 _ hγ.symm)]
    simp
    -- The tangent vector of the constant map is zero.
    change _ - (0 : Fin d → k) = t • (_ - (0 : Fin d → k))
    simp only [sub_zero]
  let x : HodgeH (freeAb.obj X) d := HodgeH.map (freeAb.map (lift (𝟙 X) (constMap z))) δ.baseChange
  have h_scale_eq (t : k) : HodgeH.scale t x = t ^ d • pointClass d z :=
    by
      let g := freeAb.map (lift (𝟙 X) (constMap z))
      let S := HodgeTest.scaleModule t (HodgeTest.sqZeroExt ⋙ freeAb.obj X)
      let g' := HodgeTest.sqZeroExt.whiskerLeft g
      have h_graph : S ≫ g' = freeAb.map (scaledGraph t (𝟙 X) (constMap z)) := by
        change freeAb.map (HodgeTest.scaleModule t (HodgeTest.sqZeroExt ⋙ X)) ≫
          freeAb.map (HodgeTest.sqZeroExt.whiskerLeft (lift (𝟙 X) (constMap z))) = _
        rw [← freeAb.map_comp]
        congr 1
      have h_scale :
          HodgeH.scale t x = H.map hodgeCoeff (freeAb.map (scaledGraph t (𝟙 X) (constMap z))) d
            δ.baseChange := by
        change H.map hodgeCoeff S d (H.map hodgeCoeff g' d δ.baseChange) = _
        exact (H.map_comp ..).symm.trans
          (congrArg (fun f ↦ H.map hodgeCoeff f d δ.baseChange) h_graph)
      refine h_scale.trans ?_
      have h_sum := hδ _ _ _ t _ h_coincidence fun w _ ↦ h_jacobian t w
      exact h_sum.trans (by simp; rfl)
  have h_one : hodgeTateMap l x = hodgeTateMap l (pointClass d z) := by
    simpa [hodgeTateMap_scale] using congrArg (hodgeTateMap l) (h_scale_eq 1)
  have h_two : (2 : k) ^ l • hodgeTateMap l (pointClass d z) =
      (2 : k) ^ d • hodgeTateMap l (pointClass d z) := by
    simpa [hodgeTateMap_scale, h_one] using congrArg (hodgeTateMap l) (h_scale_eq 2)
  by_contra h_ne
  have h_pow_cast : ((2 ^ l : ℕ) : k) = (2 ^ d : ℕ) := by simpa [smul_left_inj h_ne] using h_two
  exact hl (Nat.pow_right_injective le_rfl (Nat.cast_injective h_pow_cast))

/-- In characteristic zero, let `z` be a `k`-point of `ℙ^d` and
`lineProductMap k d : ℙ^d × ℙ¹ → ℙ^(d+1)` the map sending `([v], [w 0 : w 1])` to the point with
coordinates `w 0 * ∑ i, v i` and `(w 1 - i * w 0) * v i`. Then the pull-back along this map of the
Hodge class of the point `affinePoint 0 0 = [1 : 0 : … : 0]` of `ℙ^(d+1)` is a positive multiple `n`
of the image in the Hodge cohomology of `ℤ[ℙ^d × ℙ¹]` of the cup product (exterior-algebra
multiplication) of the classes of `z` and of `[1 : 0]` in `ℙ¹`. -/
lemma New.Variety.projSpace.exists_map_pointClass_eq_nsmul_map_cup {k : Type} [Field k] [CharZero k]
    {d : ℕ} (z : (projSpace k d).obj (of k k)) :
    ∃ n ≠ (0 : ℕ),
      HodgeH.map (freeAb.map (lineProductMap k d)) (pointClass (d + 1) (affinePoint 0 0)) =
        n •
          HodgeH.map (freeAb.prod (projSpace k d) (projSpace k 1))
            (cup (exteriorAlg (k := k)).mulPairing (pointClass d z) (pointClass 1 (affinePoint 0 0))
              (add_comm 1 d)) := by
  classical
  let W : CommAlg k ⥤ Type 1 := MonoidalCategory.tensorObj (projSpace k d) (projSpace k 1)
  let y (j : Fin (d + 1)) : W.obj (of k k) := (affinePoint j 0, affinePoint 0 ![j])
  -- Over a local ring, a point of the fibre is one of the `y j`.
  have fibre {B : CommAlg k} {v : (projSpace k d).obj B} {u : (projSpace k 1).obj B}
      (e :
        (lineProductMap k d).app B (v, u) = (projSpace k d.succ).map structureMap (affinePoint 0 0))
      [IsLocalRing B] : ∃ j : Fin (d + 1), (v, u) = W.map structureMap (y j) := by
    induction v, u using Quot.induction_on₂
    refine exists_eq_map_affinePoint_of_mul_eq_zero _ _ fun i ↦ ?_
    simpa using mk_eq_mk_iff_cross_mul.mp e i.succ 0
  have coin :
      IsCoincidenceSet (constMap (affinePoint 0 0)) (lineProductMap k d) (univ.image y) := by
    refine ⟨fun (v, u) e ↦ ?_, forall_mem_image.mpr fun j _ ↦ ?_, fun B field (v, u) e ↦ ?_⟩
    · obtain ⟨j, hj⟩ := fibre e
      rw [hj, map_map_structureMap]
    · exact mk_eq_mk_iff_cross_mul.mpr (by simp [forall_fin_succ, Pi.single_apply])
    · let : Field B := field.toField
      exact exists_mem_image.mpr ((fibre e).imp fun j hj ↦ ⟨mem_univ j, hj⟩)
  refine ⟨#(univ.image y), by simp [Finset.ext_iff], ?_⟩
  -- The class pulls back to the sum of the classes of the points of the reduced fibre.
  rw [map_pointClass_eq_sum_of_isCoincidenceSet _ _ coin]
  -- The class of a point `(v, w)` is the product of the classes, which do not depend on the points.
  refine sum_eq_card_nsmul fun ⟨v, w⟩ _ ↦ ?_
  erw [← IsPointSum.cup_pointClass, pointClass_eq_pointClass_affinePoint v,
    pointClass_eq_pointClass_affinePoint w, pointClass_eq_pointClass_affinePoint z]

-- Keeps definitional checks from unfolding the Ext groups.
seal CategoryTheory.Abelian.Ext in
/-- Let `k` be a field of characteristic zero with an embedding in `ℚ̄_p`, and let `z` be a
`k`-point of projective `d`-space. The Hodge–Tate map `hodgeTateMap d` does not kill the class
`pointClass d z` of `z` in the degree-`d` Hodge cohomology of projective `d`-space. -/
lemma New.Variety.projSpace.hodgeTateMap_pointClass_ne_zero {p : ℕ} {k : Type} [Field k]
    [EmbeddedInQpBar p k] {d : ℕ} (z : (projSpace k d).obj (of k k)) :
    hodgeTateMap d (pointClass d z) ≠ 0 := by
  -- Induct on `d`, pulling the class of `affinePoint 0 0` back along `lineProductMap k d`; `η`
  -- lifts `hodgeTateMap 1` of the class of `[1 : 0]` (`hη`), and `x × η = 0` forces `x = 0`.
  obtain ⟨η, hη, η_reg⟩ := exists_hodgeTateMap_pointClass_line (k := k)
  -- The pull-back of the class of `affinePoint 0 0` is killed by `hodgeTateMap (d + 1)` exactly if
  -- the class of `z` is killed by `hodgeTateMap d`.
  have key_iff {d} (z : (projSpace k d).obj (of k k)) :
      hodgeTateMap (d + 1)
          (.map (freeAb.map (lineProductMap k d)) (pointClass (d + 1) (affinePoint 0 0))) = 0 ↔
        hodgeTateMap d (pointClass d z) = 0 := by
    obtain ⟨ξ, hξ⟩ : ∃ ξ, hodgeTateMap d (pointClass d z) = restrictToPairs (n := d + d) ξ :=
      IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq d (pointClass d z)
    obtain ⟨n, n_ne, hn⟩ := exists_map_pointClass_eq_nsmul_map_cup z
    -- Only the term `h = d` of the product formula survives; its coefficient is `± n * (d + 1)`.
    trans PairH.map (freeAb.prod (projSpace k d) (projSpace k 1))
      (HodgeTatePair.cross (restrictToPairs η) (restrictToPairs ξ)) = 0
    · erw [hn, map_nsmul, hodgeTateMap_map, hodgeTateMap_cup, sum_eq_single d _ (by simp)]
      · simp [n_ne, hξ, hη, ← Nat.cast_smul_eq_nsmul k]
        let y : PairH (abTensor (freeAb.obj (projSpace k d)) (freeAb.obj (projSpace k 1))) :=
          HodgeTatePair.cross (restrictToPairs η) (restrictToPairs ξ)
        change PairH.map (freeAb.prod (projSpace k d) (projSpace k 1)) ((↑d + 1 : k) • y) = 0 ↔
          PairH.map (freeAb.prod (projSpace k d) (projSpace k 1)) y = 0
        rw [LinearMap.map_smul]
        simp [Nat.cast_add_one_ne_zero]
      · intro h _ h_ne
        simp [hodgeTateMap_pointClass_eq_zero_of_ne z h_ne]
    rw [hξ]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    swap
    · rw [h, map_zero]
      exact map_zero (PairH.map (freeAb.prod (projSpace k d) (projSpace k 1)))
    -- The product comes from the product `x` of `ξ` and `η` on tests, and `η` is regular.
    let x :=
      cup (PadicTest.genericAlg ⋙ forget₂ _ (AlgCat ℂ_[p])).mulPairing ξ η (add_comm 2 (d + d))
    have restrictToPairs_x :
        restrictToPairs
            (N := (abTensor.obj (freeAb.obj (projSpace k d))).obj (freeAb.obj (projSpace k 1))) x =
        HodgeTatePair.cross (restrictToPairs η) (restrictToPairs ξ) := by
      let c := Comparison.restrict HodgeTatePair.toTest genericCoeff
      let F := HodgeTatePair.toTest ⋙ genericCoeff
      let μ : (abTensor.obj F).obj F ⟶ F := HodgeTatePair.toTest.whiskerLeft
        (PadicTest.genericAlg ⋙ forget₂ _ (AlgCat ℂ_[p])).mulPairing
      -- `abTensor_hom_ext` is given explicitly: `simp` is slow here.
      have pull_x := c.pull_cup (μ' := μ) (η := HodgeTatePair.toGeneric)
        (abTensor_hom_ext fun _ _ _ ↦ rfl) ξ η (add_comm 2 (d + d))
      exact (congrArg Abelian.Ext.toTotalH pull_x).trans (TotalH.cup_of μ ..).symm
    have x_zero : x = 0 := by
      let g := freeAb.prod (projSpace k d) (projSpace k 1)
      let q := genericOver.whiskerLeft g
      have : IsIso q := Functor.isIso_whiskerLeft _ _
      have h_inj := (IsCohomEquiv.of_isIso (F := genericCoeff) (α := q) (d + d + 2)).1
      have h_pull : restrictToPairs (H.map genericCoeff q _ x) = 0 :=
        (restrictToPairs_map g x).trans ((congrArg (PairH.map g) restrictToPairs_x).trans h)
      apply h_inj
      apply IsChartCovered.pairRestrictBijective.injective_restrictToPairs
      exact h_pull.trans ((congrArg restrictToPairs
        (map_zero (H.map genericCoeff q (d + d + 2)))).trans (map_zero restrictToPairs)).symm
    rw [η_reg (N := _ ⋙ freeAb.obj (projSpace k d)) ξ x_zero, map_zero]
  induction d with
  | succ d ih =>
    rw [pointClass_eq_pointClass_affinePoint z]
    intro h_zero
    have h_pullback_zero :
        hodgeTateMap (d + 1)
          (.map (freeAb.map (lineProductMap k d)) (pointClass (d + 1) (affinePoint 0 0))) = 0 := by
      rw [hodgeTateMap_map, h_zero, map_zero]
    exact ih (affinePoint 0 0) ((key_iff _).1 h_pullback_zero)
  | zero =>
    -- Here `lineProductMap k 0` has a section `σ`, so `key_iff` would give `η = 0`.
    intro h
    let σ : projSpace k 1 ⟶ MonoidalCategory.tensorObj (projSpace k 0) (projSpace k 1) :=
      lift (constMap (affinePoint 0 0)) (𝟙 _)
    have σ_mul : σ ≫ lineProductMap k 0 = 𝟙 _ := by
      ext _ ⟨⟩
      exact mk_eq_mk_iff_cross_mul.2 (by simp)
    have η_zero : η = 0 := by
      have h_pullback := congrArg (PairH.map (freeAb.map σ)) ((key_iff z).2 h)
      -- Since `σ` is a section, the left side is `hodgeTateMap 1` of the class of `[1 : 0]`, the
      -- restriction of `η`.
      erw [← hodgeTateMap_map, ← HodgeH.map_comp, ← freeAb.map_comp, σ_mul, freeAb.map_id, H.map_id,
        hη, map_zero,
        map_eq_zero_iff _ IsChartCovered.pairRestrictBijective.injective_restrictToPairs]
        at h_pullback
      exact h_pullback
    -- Then every class on tests vanishes, so the coefficients `genericCoeff` are zero; but `1 ≠ 0`
    -- at the test `T`.
    have id_zero : 𝟙 genericCoeff = 0 := by simpa [cup, η_zero] using η_reg (.mk₀ (𝟙 genericCoeff))
    let T : PadicTest := ⟨Unit, _, Pi.constRingHom ..⟩
    have h_one_eq_zero : algebraMap T.ProdRing T.GenericRing 1 = 0 :=
      congr(($(id_zero).app T ⟨algebraMap T.ProdRing T.GenericRing 1⟩).down)
    simpa using T.eq_zero_of_algebraMap_genericRing 1 h_one_eq_zero

end ProjectivePointClass

end
