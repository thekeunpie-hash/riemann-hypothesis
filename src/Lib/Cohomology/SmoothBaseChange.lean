module

public import Lib.Cohomology.ProperBaseChange.Theorem
import Lib.Cohomology.Etale.DenseSubfunctors
import Lib.Cohomology.ProjectiveLine.TiltedLineFormula
import Lib.PadicComparison.Descent.TestCovers
import Lib.PadicComparison.Duality.LineIntegration
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Unramified.LocalStructure
public import Lib.PadicComparison.Duality.GoodPairs

section
/-!
# The projective line formula for locally constant ℤ/ℓ coefficients

The projective line formula H(ℙ¹ × S) = H(S) ⊕ η H(S) (`New.Variety.TorsionCoeff.HasLineFormula`) is
proved for the theory `New.Variety.Theory.locallyConstant` of locally constant ℤ/ℓ-valued functions
on tests over an absolutely integrally closed valuation ring A, with ℓ invertible, that embeds into
ℂ_ℓ. Here H is total Ext of functors to abelian groups, η is the degree two class
`New.Variety.TorsionCoeff.cupClass`, and `New.Variety.lerayHirsch θ S` is the Leray–Hirsch map w ↦ Σ
θ_i · w_i of a family θ of classes; θ is a Leray–Hirsch basis at S
(`New.Variety.IsLerayHirschBasis`) when this map is bijective.

* `New.Variety.isLerayHirschBasis_lineBasis_of_basis`: the formula over a flat S follows from any
  family θ that contains η and is a Leray–Hirsch basis over S and over S ⊗ ℤ[ℙ¹].
* `New.Variety.hasLineFormula_of_lerayHirsch_ne_zero`: over a valuation ring A the formula holds as
  soon as η acts non-trivially on the point for one coefficient whose tests lie over the generic
  point of A.
* `New.Variety.hasLineFormula_locallyConstant`: the formula for a valuation ring A with an injective
  ring map to ℂ_ℓ.

The formula is reduced to algebraically closed fields k over A
(`New.Variety.hasUniversalPoints_structurePt`), where a Künneth basis contains η unless η · 1 = 0.
That vanishing would spread to the generic point of A; the tilted theory of
`New.Variety.hasLineFormula_tiltTheory` shows that it does not occur for A in ℂ_ℓ.

Notions from other files:
* `New.Variety.TestOver`: The category of tests over A: the commutative A-algebras that are reduced,
  absolutely integrally closed, and in which any a, b admit an idempotent e with a ∣ eb and
  b ∣ (1 − e)a.
* `New.Variety.TorsionCoeff`: A coefficient along g: a functor to abelian groups, killed by ℓ, with
  Zariski descent; a `New.Variety.Theory` is one that also behaves well on closed loci.
* `New.Variety.projLine`: The projective line as a functor on rings; `New.Variety.onePointFunctor`
  is the constant one-point functor and `New.Variety.reprBy A` the functor Hom(A, −).

## Relation to the literature

Known result: the projective line formula for ℤ/ℓ coefficients, where the degree two class is the
Chern class of O(1) given by the Kummer sequence. Here the formula H(ℙ¹ × S) = H(S) ⊕ η H(S) is
stated in Leray–Hirsch form for locally constant ℤ/ℓ coefficients on test rings; the tilted
coefficients serve only to show that η acts non-trivially. Source: SGA 4½ [Cycle]; SGA 5
(Jouanolou); Milne, Étale Cohomology; Scholze, p-adic Hodge theory for rigid-analytic varieties.
-/

@[expose] public section

noncomputable section

namespace New.Variety

open CategoryTheory MonoidalCategory ObjectProperty CommAlgCat TotalH Period Ideal Finsupp

variable {C : Type _} [Category C] {ℓ : ℕ} {A : Type} [CommRing A] {g : C ⥤ TestOver A}

section

variable [InvertsPrime A ℓ]

-- Keeps definitional checks from unfolding the Ext groups, their group structure, and `projLine`.
seal CategoryTheory.Abelian.Ext addCommGroupH projLine in
/-- The projective line formula over a coefficient `S` with flat values, from a family that contains
η. Let Θ be a theory along g and θ a family of classes on the points of ℙ¹ over g, of degrees `d`,
whose member `θ i` is η (`hθ_eta`). If θ is a Leray–Hirsch basis over `S` (`h_base`) and over
`S ⊗ ℤ[ℙ¹]` (`h_line`), then so is the family (1, η) = `New.Variety.TorsionCoeff.lineBasis`, that
is, the projective line formula holds over `S`. -/
lemma isLerayHirschBasis_lineBasis_of_basis (Θ : Theory g) {I : Type*} {S : AbFunctor C}
  [HasFlatValues S]
    {d : I → ℕ} (θ : ∀ i : I,
      H (restrictAlong (elementsProj (projLineAlong g)) Θ.functor)
        Θ.toTorsionCoeff.onElements.functor (d i))
    (i : I) (hθ_eta : (θ i).toTotalH = Θ.cupClass.toTotalH)
    (h_base : IsLerayHirschBasis θ S)
    (h_line : IsLerayHirschBasis θ ((abTensor.obj S).obj (freeAb (projLineAlong g)))) :
    IsLerayHirschBasis Θ.lineBasis S := by
  classical
  -- By `isLerayHirschBasis_lineBasis_of_injective` it suffices that the product with η is injective
  -- on `S`, and that `x` is such a product as soon as `hx` holds over the points of ℙ¹.
  refine isLerayHirschBasis_lineBasis_of_injective Θ (fun v w hvw ↦ ?_) fun x hx ↦ ?_
  · -- As `θ i` is η, the product `v · η` is the Leray–Hirsch image of the family with `v` at `i`.
    have h_single : lerayHirsch θ S (single i v) = lerayHirsch θ S (single i w) := by
      rw [lerayHirsch_single, lerayHirsch_single, hθ_eta, ← Θ.sliceEquiv_mulClass,
        ← Θ.sliceEquiv_mulClass, hvw]
    exact single_injective i (h_base.injective h_single)
  -- Expand `sliceEquiv x` in the basis θ; the coefficient at `i` is the preimage of `x`.
  obtain ⟨w, hw⟩ := h_base.surjective (sliceEquiv x)
  -- On ℙ¹ × ℙ¹ the product with η in the second factor commutes with each `θ j`, and `hx` turns
  -- the result into the image of the family with `x` at `i`.
  let r := Θ.mulClass (S := S) (etaClass g).toTotalH
  have h_prod :
      lerayHirsch θ ((abTensor.obj S).obj (freeAb (projLineAlong g))) (w.mapRange r r.map_zero) =
        lerayHirsch θ ((abTensor.obj S).obj (freeAb (projLineAlong g))) (single i x) := by
    refine (lerayHirsch_naturality θ r (fun _ _ ↦ Θ.mulClass_naturality ..) w).trans ?_
    rwa [lerayHirsch_single, map_restrictAlong_etaClass, hw, hθ_eta]
  -- By `h_line` the two families agree; their coefficients at `i` give the preimage `w i` of `x`.
  have h_coeff : w.mapRange r r.map_zero = single i x := h_line.injective h_prod
  have h_coeff_i : r (w i) = x := by
    have h_at := DFunLike.congr_fun h_coeff i
    rw [Finsupp.mapRange_apply, Finsupp.single_eq_same] at h_at
    exact h_at
  exact ⟨w i, h_coeff_i⟩

/-- For a test c over A, the class η · 1 with locally constant ℤ/ℓ coefficients L: η of
`New.Variety.Theory.locallyConstant` on the points of ℙ¹, pulled back along
`New.Variety.oneLocConst` (ℤ → L, 1 ↦ the constant 1) and then to the functor
(B, x ∈ ℙ¹(B)) ↦ Hom(c, B). It lies in H²(ℤ[Hom(c, −)], L) on the points of ℙ¹ over tests over A. -/
def etaOneClass (c : TestOver A) :=
  H.map _ (freeAb.map (toUnit (testOfPoint A projLine ⋙ reprBy c))) 2
    (H.map _ oneLocConst 2 Theory.locallyConstant.cupClass)

/-- Pull-back along a map of tests c → d over A sends `New.Variety.etaOneClass` c to
`New.Variety.etaOneClass` d. -/
lemma map_etaOneClass {c d : TestOver A} (φ : c ⟶ d) :
    H.map (locConstAlong (testOfPoint A projLine))
        (freeAb.map ((testOfPoint A projLine).whiskerLeft (reprMap φ))) 2 (etaOneClass c) =
      etaOneClass d :=
  H.map_map ..

/-- Pull a class x back along f, restrict it along φ, pull it back along α and compose with T. The
result is the restriction of x composed with T, pulled back along α followed by the restriction
of f. -/
lemma comp_restrict_pull_map {D D' : Type 1} [Category D] [Category D'] (φ : D' ⥤ D)
    {N N₁ F : AbFunctor D} {N' K : AbFunctor D'} (α : N' ⟶ (restrictAlong φ).obj N) (f : N ⟶ N₁)
    {n : ℕ} (x : H N₁ F n) (T : TotalH ((restrictAlong φ).obj F) K) :
    comp ((Comparison.restrict φ F).pull α n (H.map F f n x)).toTotalH T =
      pullbackAlong (α ≫ (restrictAlong φ).map f)
        (mapThenComp (restrictAlong φ) T x.toTotalH) := by
  -- Restriction along `φ` commutes with pull-back, and the coefficient map of the comparison is
  -- the identity.
  have h_map : (H.map F f n x).mapExactFunctor (restrictAlong φ) =
      H.map ((restrictAlong φ).obj F) ((restrictAlong φ).map f) n
        (x.mapExactFunctor (restrictAlong φ)) := by
    simp only [H.map, Abelian.Ext.precomp, Abelian.Ext.bilinearComp_apply_apply,
      Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  have h_pull : (Comparison.restrict φ F).pull α n (H.map F f n x) =
      H.map ((restrictAlong φ).obj F) (α ≫ (restrictAlong φ).map f) n
        (x.mapExactFunctor (restrictAlong φ)) := by
    rw [H.map_comp, ← h_map]
    exact congrArg (H.map ((restrictAlong φ).obj F) α n) (Abelian.Ext.comp_mk₀_id _)
  have h_total :
      (H.map ((restrictAlong φ).obj F) (α ≫ (restrictAlong φ).map f) n
        (x.mapExactFunctor (restrictAlong φ))).toTotalH =
      pullbackAlong (α ≫ (restrictAlong φ).map f) (TotalH.map (restrictAlong φ) x.toTotalH) := by
    rw [map_of, pullbackAlong_of]
  calc comp ((Comparison.restrict φ F).pull α n (H.map F f n x)).toTotalH T
      = comp (pullbackAlong (α ≫ (restrictAlong φ).map f)
          (TotalH.map (restrictAlong φ) x.toTotalH)) T := by
        rw [← h_total]
        exact congrArg (fun y : H N' ((restrictAlong φ).obj F) n ↦ comp y.toTotalH T) h_pull
    _ = pullbackAlong (α ≫ (restrictAlong φ).map f)
          (mapThenComp (restrictAlong φ) T x.toTotalH) := comp_assoc ..

-- Keeps definitional checks from unfolding the Ext groups, their group structure, and `projLine`.
seal CategoryTheory.Abelian.Ext addCommGroupH projLine in
/-- Let c be a test over A and u a map from the point to the functor d ↦ Hom(c, g(d)), that is, maps
c → g(d) natural in the object d of C. Let T be a class in total Ext from the locally constant
ℤ/ℓ coefficient to M, both restricted to the points of ℙ¹ over g. Pull `New.Variety.etaOneClass` c
back along u to the points of ℙ¹ over g and compose it with T. The result is T composed with
η = `New.Variety.TorsionCoeff.cupClass` of M, pulled back along `New.Variety.oneLocConst`. -/
lemma comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst {M : TorsionCoeff g}
    {T : TotalH
      (Functor.Elements.precomp g (ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙
        (Theory.locallyConstant.toTorsionCoeff.onElements
          (X := projLineAlong (𝟭 (TestOver A)))).functor)
      M.onElements.functor}
    {c : TestOver A} (u : onePointFunctor C ⟶ g ⋙ reprBy c) :
    comp
        ((Comparison.restrict (Functor.Elements.precomp g (ringOf (𝟭 (TestOver A)) ⋙ projLine))
            _).pull
          (freeAbMap ((elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine)).whiskerLeft u)) 2
          (etaOneClass c)).toTotalH
        T =
      pullbackAlong (oneLocConst (g := elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙ g))
        (comp T M.cupClass.toTotalH) := by
  -- `etaOneClass c` is η pulled back along a map `f`. By `comp_restrict_pull_map` the left side is
  -- `T` after the restriction of η, pulled back along a map from the point to `ℤ/ℓ`.
  let X : TestOver A ⥤ Type 1 := ringOf (𝟭 (TestOver A)) ⋙ projLine
  let f : freeAb (testOfPoint A projLine ⋙ reprBy c) ⟶ locConstAlong (testOfPoint A projLine) :=
    freeAb.map (toUnit (testOfPoint A projLine ⋙ reprBy c)) ≫ oneLocConst
  have h_eta : etaOneClass c = H.map _ f 2 Theory.locallyConstant.cupClass := (H.map_comp ..).symm
  -- The map from the point sends the generator to the constant 1, so it is `oneLocConst`.
  have h_one :
      freeAbMap ((elementsProj (g ⋙ X)).whiskerLeft u) ≫
          (restrictAlong (Functor.Elements.precomp g X)).map f =
        oneLocConst (g := elementsProj (g ⋙ X) ⋙ g) :=
    freeAb.hom_ext fun _ _ ↦ rfl
  -- `T` commutes with the product with η.
  have h_nat :
      mapThenComp (restrictAlong (Functor.Elements.precomp g X)) T
          (Theory.locallyConstant (A := A)).cupClass.toTotalH =
        comp T M.cupClass.toTotalH :=
    Theory.locallyConstant.onElements.etaAt_naturality (Functor.Elements.precomp g X)
      M.onElements T _
  rw [h_eta]
  refine (comp_restrict_pull_map (Functor.Elements.precomp g X) _ f _ T).trans ?_
  exact (congrArg _ h_nat).trans
    (congrArg (fun f ↦ pullbackAlong f (comp T M.cupClass.toTotalH)) h_one)

private lemma comparison_pull_zero {D D' : Type 1} [Category D] [Category D']
    {F : AbFunctor D} {F' : AbFunctor D'} (c : Comparison F F')
    {N : AbFunctor D} {N' : AbFunctor D'} (α : N' ⟶ c.functor ⋙ N) (n : ℕ) :
    c.pull α n 0 = 0 :=
  (c.pull α n).map_zero

-- Keeps definitional checks from unfolding the Ext groups, their group structure, and `projLine`.
seal CategoryTheory.Abelian.Ext addCommGroupH projLine in
/-- Let c be a test over A and u a map from the point to the functor d ↦ Hom(c, g(d)) that has
universal points for the restriction along g of the locally constant ℤ/ℓ coefficient. Suppose that
this restriction is a coefficient along g (`h_torsion`, `h_descent`) and that its class η, pulled
back along `New.Variety.oneLocConst`, is zero. Then `New.Variety.etaOneClass` c is zero. -/
lemma etaOneClass_eq_zero_of_hasUniversalPoints {c : TestOver A}
    {u : onePointFunctor C ⟶ g ⋙ reprBy c}
    (hu : (Comparison.restrict g Theory.locallyConstant.functor).HasUniversalPoints u)
    (h_torsion : ∀ (d : C) (x : (locConstAlong g).obj d), ℓ • x = 0)
    (h_descent : HasZariskiDescent (ringOf g) (locConstAlong g))
    (h_zero :
      pullbackAlong (oneLocConst (g := elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙ g))
        (TorsionCoeff.mk (locConstAlong g) h_torsion h_descent).cupClass.toTotalH = 0) :
    etaOneClass c = 0 := by
  -- By `comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst` for the identity class, the pull-back
  -- `P` along `u` sends `etaOneClass c` to η · 1, which is zero; and `P` is injective.
  let P := (Comparison.restrict (Functor.Elements.precomp g (ringOf (𝟭 (TestOver A)) ⋙ projLine))
      Theory.locallyConstant.onElements.functor).pull
    (freeAbMap (Y := testOfPoint A projLine ⋙ reprBy c)
      ((elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine)).whiskerLeft u)) 2
  let M : TorsionCoeff g := ⟨locConstAlong g, h_torsion, h_descent⟩
  have h_pull : (P (etaOneClass c)).toTotalH = 0 :=
    comp_id.symm.trans <|
      (comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst (M := M)
          (T := homClass (𝟙 M.onElements.functor)) u).trans <|
        (congrArg
          (pullbackAlong
            (oneLocConst (g := elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙ g)))
          pullbackAlong_id).trans h_zero
  have h_pull_two : P (etaOneClass c) = 0 :=
    DirectSum.of_injective 2 (h_pull.trans (DirectSum.of _ 2).map_zero.symm)
  have h_injective : Function.Injective P := (hu.on_elements.isBijective 2).injective
  exact h_injective (h_pull_two.trans (comparison_pull_zero ..).symm)

variable (A) (k : Type _) [Field k] [IsAlgClosed k] [Algebra A k]

/-! ### Tests over an algebraically closed field -/

/-- For an A-algebra k that is a field, the restriction of scalars functor from test k-algebras to
test A-algebras. -/
def TestOver.restrictScalars : TestOver k ⥤ TestOver A := lift _ (ι _ ⋙ restrictAlg ..) (·.property)

/-- On test k-algebras B, the map from the point to the functor B ↦ Hom_A(k, B) that picks the
structure map k → B. -/
def TestOver.structurePt :
    onePointFunctor (TestOver k) ⟶ restrictScalars A k ⋙ reprBy
      ⟨of A k, isTest_of_preValuationRing⟩ :=
  sectionMap
    { val B := ⟨⟨CommAlg.homOfRingHom (algebraMap k B.obj) (by tauto)⟩⟩
      property f := congr(⟨⟨$(by ext; apply f.hom.hom.commutes')⟩⟩) }

/-- For an algebraically closed field k over A, restriction of scalars from tests over k to tests
over A compares the point with the functor Hom_A(k, −) in the sense of
`New.Variety.Comparison.HasUniversalPoints`, for locally constant ℤ/ℓ-valued functions: an A-map y :
k → B makes B a test over k, universal for y, and the identity of B is bijective on coefficients. -/
lemma hasUniversalPoints_structurePt :
    (Comparison.restrict (TestOver.restrictScalars A k)
      Theory.locallyConstant.functor).HasUniversalPoints
      (TestOver.structurePt A k) := by
  -- A point `y` over `B` is an `A`-algebra map k → B; it makes `B` itself a `k`-algebra, and this
  -- algebra `B'`, with the identity of `B`, is the universal member.
  intro B y
  let φ : k →ₐ[A] B.obj := y.down.hom.hom
  let algebra_k_B : Algebra k B.obj := φ.toRingHom.toAlgebra
  let B' : TestOver k := ⟨of k B.obj, B.property⟩
  let s : B ⟶ (TestOver.restrictScalars A k).obj B' :=
    ⟨CommAlg.homOfRingHom (RingHom.id B.obj) fun x ↦ (φ.commutes x).symm⟩
  refine ⟨B', ⟨⟩, s, rfl, fun D z f e ↦ ?_, ?_⟩
  · -- By `e`, the ring map under `f` is `k`-linear; it is the only possible factorisation.
    have h_linear (x : k) : f.hom.hom (algebraMap k B.obj x) = algebraMap k D.obj x :=
      (congrArg (fun a ↦ a.down.hom.hom x) e).symm
    refine ⟨⟨CommAlg.homOfRingHom f.hom.hom.toRingHom h_linear⟩, ⟨rfl, rfl⟩, ?_⟩
    -- As `s` is the identity of `B`, another factorisation has the map of `f` underneath.
    rintro f'' ⟨-, h_comp⟩
    ext x
    exact congrArg (fun a ↦ a.hom.hom x) h_comp
  · -- On coefficients `s` acts as the identity of `B`.
    exact ConcreteCategory.bijective_of_isIso ((locConstCoeff _).map (𝟙 _))

end

/-! ### A valuation ring as a test over itself -/

section

variable (A) [IsAbsIntegrallyClosedLocal A] [PreValuationRing A]

/-- An absolutely integrally closed valuation ring as a test over itself. -/
abbrev TestOver.ofSelf : TestOver A where
  obj := of A A
  property := isTest_of_preValuationRing

variable {A} in
/-- A, seen as a test over itself, is initial among tests over A: for every test D over A, the point
map from Hom(A, D) to the one-point set is bijective. -/
lemma pointMap_ofSelf_bijective :
    AllBijective fun D : TestOver A ↦
      pointMap (Y := onePointFunctor (TestOver A)) (A := TestOver.ofSelf A) ⟨⟩ D := by
  -- As `A` is the initial `A`-algebra, its one map to `D` is the structure map of `D`.
  intro D
  refine ⟨fun f f' _ ↦ ULift.down_injective (InducedCategory.hom_ext ?_),
    fun _ ↦ ⟨ULift.up ⟨structureMap⟩, rfl⟩⟩
  ext

end

/-! ### The projective line formula over a valuation ring -/
-- Without the seal, unification unfolds these functors, Ext groups, and their group structure.
seal locConstCoeff projLine CategoryTheory.Abelian.Ext addCommGroupH in
/-- If every non-zero element of A is a unit in every test g(d) (so every g(d) lies over the generic
point of A) and `New.Variety.etaOneClass` vanishes at the residue field of A at its generic point
(`residueTest (TestOver.ofSelf A) ⊥`, with A seen as a test over itself), then y · η = 0 over the
points of ℙ¹ for every class y of M on the point; here y · η is the Leray–Hirsch map of (1,
η) = `New.Variety.TorsionCoeff.lineBasis` at (y at `false`, 0). -/
lemma lerayHirsch_lineBasis_single_false_eq_zero_of_etaOneClass_eq_zero {C : Type _} [Category C]
    {ℓ : ℕ} (A : Type) [CommRing A] {g : C ⥤ TestOver A} [InvertsPrime A ℓ] [PreValuationRing A]
    (hg : ∀ d : C, ∀ a ≠ (0 : A), IsUnit (algebraMap A (g d).obj a)) (M : TorsionCoeff g)
    (h_generic : etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) ⊥).right = 0)
    (y : TotalH (freeAb.obj (onePointFunctor C)) M.functor) :
    lerayHirsch M.lineBasis (freeAb (onePointFunctor C)) (Finsupp.single false y) = 0 := by
  -- The residue field at the generic point maps to every `g d`, naturally in `d`.
  let toTest (d : C) : (residueTest (TestOver.ofSelf A) ⊥).right ⟶ g.obj d :=
    ⟨ofHom (ResidueField.liftₐ _ structureMap.hom bot_le (hg d))⟩
  have h_natural {d d' : C} (f : d ⟶ d') : toTest d ≫ g.map f = toTest d' := by
    -- Both are `A`-algebra maps out of the residue field; such maps agree on the image of `A`.
    ext1
    refine congrArg ofHom (ResidueField.algHom_ext ?_)
    ext
  let u : onePointFunctor C ⟶ g ⋙ reprBy (residueTest (TestOver.ofSelf A) ⊥).right :=
    sectionMap ⟨fun d ↦ ULift.up (toTest d), fun f ↦ congrArg ULift.up (h_natural f)⟩
  -- Every class on the point is the value at 1 of some `T`
  -- (`pullbackAlong_oneLocConst_surjective`); then y · η is `etaOneClass` at the generic point,
  -- pulled back along `u`, composed with `T`.
  obtain ⟨T, rfl⟩ := M.pullbackAlong_oneLocConst_surjective y
  rw [lerayHirsch_single, map_comp_assoc, map_homClass]
  have h_one :
      (restrictAlong (elementsProj (projLineAlong g))).map (oneLocConst (g := g)) =
        oneLocConst (g := elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙ g) :=
    rfl
  let T' : TotalH
      (Functor.Elements.precomp g (ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙
        (Theory.locallyConstant.toTorsionCoeff.onElements
          (X := projLineAlong (𝟭 (TestOver A)))).functor)
      M.onElements.functor :=
    TotalH.map (restrictAlong (elementsProj (projLineAlong g))) T
  rw [h_one]
  change pullbackAlong
    (oneLocConst (g := elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙ g))
    (comp T' M.cupClass.toTotalH) = 0
  rw [← comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst (M := M) (T := T') u,
    h_generic, comparison_pull_zero]
  exact (congrArg (fun x ↦ comp x T') (DirectSum.of _ 2).map_zero).trans
    (DFunLike.congr_fun comp.map_zero T')

/-- If `New.Variety.etaOneClass` vanishes at a test k over A that is a field, then it vanishes at
the residue field of A at its generic point. -/
lemma etaOneClass_residueTest_bot_eq_zero {ℓ : ℕ} {A : Type} [CommRing A] [InvertsPrime A ℓ]
    [PreValuationRing A] {k : TestOver A} (k_field : IsField k.obj)
    (h_eta_k : etaOneClass (ℓ := ℓ) k = 0) :
    etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) ⊥).right = 0 := by
  let k_field_inst : Field k.obj := k_field.toField
  -- The map from `A` to `k` factors over the residue field at the prime `Q` under the zero ideal.
  let Q : PrimeSpectrum A := .comap (algebraMap A k.obj) ⊥
  let toK : (residueTest (TestOver.ofSelf A) Q).right ⟶ k :=
    ⟨ofHom (ResidueField.liftₐ _ structureMap.hom le_rfl
      fun a ha ↦ IsUnit.mk0 (algebraMap A k.obj a) ha)⟩
  -- Vanishing passes from `k` to `Q`, as pull-back between fields is injective.
  have h_eta_under : etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) Q).right = 0 :=
    (isDetectedAtPoints_projLine.isCohomEquiv_map_of_isField _ k toK
      (Field.toIsField (ResidueField _)) k_field 2).injective
      ((map_etaOneClass toK).trans (h_eta_k.trans (map_zero _).symm))
  -- Vanishing then passes to the generic point, as the vanishing locus is open.
  have h_open : IsOpen {P : PrimeSpectrum A |
      etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) P).right = 0} := by
    convert isDetectedAtPoints_projLine.isOpen_setOf_map_eq_zero
      (TestOver.ofSelf A) 2 (etaOneClass (TestOver.ofSelf A)) using 1
    ext P
    simp only [Set.mem_ofPred_eq, map_etaOneClass]
    rfl
  have h_specializes : (⊥ : PrimeSpectrum A) ⤳ Q := (PrimeSpectrum.le_iff_specializes ..).mp bot_le
  exact h_specializes.mem_open h_open h_eta_under

-- Keeps unification from unfolding these two functors and the group structure of the Ext groups.
seal locConstCoeff projLine addCommGroupH in
/-- Let A be a valuation ring that is an absolutely integrally closed local domain (not a separate
hypothesis: it is derived from the stated instances `PreValuationRing A` and `InvertsPrime A ℓ`)
with ℓ invertible, g a functor to tests over A, and M a coefficient along g. Suppose that (a) every
non-zero element of A is a unit in every test g(d), and (b) some y in total Ext(ℤ[pt], M) has
y · η ≠ 0 over the points of ℙ¹, where η is the degree-2 class of
`New.Variety.TorsionCoeff.lineBasis`. The product y · η is written as the Leray–Hirsch map of the
family (1, η) = `lineBasis` at the family with y at the index `false` and 0 at the other index. Then
the projective line formula holds for locally constant ℤ/ℓ-valued functions on tests over A: 1 and η
form a basis of H(ℙ¹ × S) over H(S) for every S. -/
lemma hasLineFormula_of_lerayHirsch_ne_zero {C : Type _} [Category C]
    {ℓ : ℕ} (A : Type) [CommRing A] {g : C ⥤ TestOver A} [InvertsPrime A ℓ] [PreValuationRing A]
    (hg : ∀ d : C, ∀ a ≠ (0 : A), IsUnit (algebraMap A (g d).obj a)) (M : TorsionCoeff g)
    (h_ne :
      ¬∀ y : TotalH (freeAb.obj (onePointFunctor C)) M.functor,
        lerayHirsch M.lineBasis (freeAb (onePointFunctor C)) (Finsupp.single false y) = 0) :
    (Theory.locallyConstant (A := A)).HasLineFormula := by
  classical
  -- Reduce to a test `k` over `A` that is a field, and then to the theory `Θ` on tests over `k`.
  -- There a Künneth basis contains η unless η · 1 = 0 over `k`; that vanishing would spread to the
  -- generic point of `A` and kill y · η for every class y of `M`, against `h_ne`.
  suffices h_field : ∀ k : TestOver A, IsField k.obj →
      IsLerayHirschBasis (Theory.locallyConstant (A := A)).lineBasis (freeAb (reprBy k)) from
    isLerayHirschBasis_of_reprBy fun c ↦
      isLerayHirschBasis_of_forall_isField isDetectedAtPoints_projLine fun k _ ↦ h_field k
  rintro ⟨k, k_test⟩ k_field
  let k_field_inst : Field k := k_field.toField
  have k_alg_closed : IsAlgClosed k := k_test.isAlgClosed
  have k_inverts : InvertsPrime k ℓ :=
    ⟨by simpa using (InvertsPrime.isUnit_prime (A := A) (ℓ := ℓ)).map (algebraMap A k)⟩
  let Θ : Theory (TestOver.restrictScalars A k ⋙ 𝟭 (TestOver A)) := {Theory.locallyConstant with}
  suffices h_point : IsLerayHirschBasis Θ.lineBasis (freeAb (onePointFunctor (TestOver k))) from
    (TorsionCoeff.HasLineFormula.bijective_iff_of_hasUniversalPoints (M' := Θ.toTorsionCoeff) _
      (hasUniversalPoints_structurePt A k)).mpr h_point
  have h_max_bot (c : TestOver k) : (IdealFamily.ofMaximalIdeal (A := k)).ideal c = ⊥ :=
    (congrArg (Ideal.map _) IsLocalRing.maximalIdeal_eq_bot).trans Ideal.map_bot
  -- Over `k` there is a Künneth basis `b`, valid at all tests as the maximal ideal of `k` is zero;
  -- it contains η if η · 1 ≠ 0.
  obtain ⟨b, h_eta_mem, hb⟩ :
      ∃ b : Set (Σ n : ℕ, H
          (restrictAlong (testOfPoint k projLine) (locConstAlong (𝟭 (TestOver k))))
          Theory.locallyConstant.onElements.functor n),
        (pullbackAlong oneLocConst Θ.cupClass.toTotalH ≠ 0 → ⟨2, Θ.cupClass⟩ ∈ b) ∧
        ∀ c : TestOver k, ⟨⟩ ∈ IdealFamily.ofMaximalIdeal.botLocus c →
          IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb (reprBy c)) :=
    exists_isLerayHirschBasis_of_isCohomDense
      Theory.locallyConstant.toTorsionCoeff.onElements isDetectedAtPoints_projLine
      (.of_top_le fun _d _x _hx ↦ h_max_bot _) ⟨2, Θ.cupClass⟩
  have h_basis_repr (c : TestOver k) :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb (reprBy c)) := hb c (h_max_bot c)
  -- It is a basis on the point, which `k` represents (as a test over itself).
  have h_basis_point :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb (onePointFunctor (TestOver k))) :=
    isClosedClass_isLerayHirschBasis.freeAb_of_bijective _ pointMap_ofSelf_bijective
      (h_basis_repr _)
  -- It is a basis on `projLinePow Unit` by dévissage from its affine cover.
  have h_basis_pow :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd)
        (freeAb (ringOf (𝟭 (TestOver k)) ⋙ projLinePow Unit)) :=
    -- `(… :)`: unifying with the expected type first runs out of heartbeats.
    isLerayHirschBasis_iff_allBijective_truncMap.mpr
      (isAffinelyCovered_projLinePow.devissage_bijective lerayHirsch.devissage fun c ↦
        isLerayHirschBasis_iff_allBijective_truncMap.mp (h_basis_repr c) :)
  -- This is moved along `projLinePow Unit` ≅ ℙ¹ and then along ℤ[ℙ¹] ≅ ℤ[pt] ⊗ ℤ[ℙ¹].
  let X : TestOver k ⥤ Type 1 := projLineAlong (TestOver.restrictScalars A k ⋙ 𝟭 (TestOver A))
  let ev : ringOf (𝟭 (TestOver k)) ⋙ projLinePow Unit ⟶ X := { app _ := ↾fun f ↦ f () }
  have h_ev : AllBijective fun c : TestOver k ↦ ev.app c := fun _ ↦ (Equiv.funUnique ..).bijective
  have h_basis_X : IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb X) :=
    isClosedClass_isLerayHirschBasis.freeAb_of_bijective ev h_ev h_basis_pow
  have h_basis_line :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd)
        ((abTensor.obj (freeAb (onePointFunctor (TestOver k)))).obj (freeAb X)) :=
    (isClosedClass_isLerayHirschBasis.iff_of_isIso
      (freeAb.map (λ_ X).inv ≫ freeAb.prod (onePointFunctor (TestOver k)) X)).mp h_basis_X
  -- If η · 1 = 0 over `k`, then `etaOneClass` vanishes at `k`, hence at the generic point of `A`.
  -- All `g d` lie over that point, so η kills every class of `M`, against `h_ne`.
  have h_eta_ne : pullbackAlong oneLocConst Θ.cupClass.toTotalH ≠ 0 := by
    intro h_eta_zero
    have h_eta_k : etaOneClass (ℓ := ℓ) ⟨k, k_test⟩ = 0 :=
      etaOneClass_eq_zero_of_hasUniversalPoints (hasUniversalPoints_structurePt A k)
        Θ.prime_smul_eq_zero Θ.zariski_descent h_eta_zero
    exact h_ne (lerayHirsch_lineBasis_single_false_eq_zero_of_etaOneClass_eq_zero A hg M
      (etaOneClass_residueTest_bot_eq_zero k_field h_eta_k))
  -- So η is a member of `b`.
  exact isLerayHirschBasis_lineBasis_of_basis Θ (fun i : b ↦ i.val.snd)
    ⟨⟨2, Θ.cupClass⟩, h_eta_mem h_eta_ne⟩ rfl h_basis_point h_basis_line

/-- Let `A` be a valuation ring (`PreValuationRing A`) that is local and absolutely integrally
closed, with ℓ invertible in it (`InvertsPrime A ℓ`), and that has an injective ring map to ℂ_ℓ. A
test over `A` is a commutative `A`-algebra whose underlying ring is a test ring. Then the theory
`Theory.locallyConstant`, which sends a test B over `A` to the locally constant functions Spec
B → ℤ/ℓ, satisfies the projective line formula: `1` and `η` form a basis of H(ℙ¹ × S) over H(S) for
every S. -/
lemma hasLineFormula_locallyConstant {ℓ : ℕ} (A : Type) [CommRing A] [InvertsPrime A ℓ]
    [PreValuationRing A] [Algebra A ℂ_[ℓ]] [FaithfulSMul A ℂ_[ℓ]] :
    (Theory.locallyConstant (A := A)).HasLineFormula := by
  -- Apply `hasLineFormula_of_lerayHirsch_ne_zero` to the tilted theory Θ with coefficients
  -- S ↦ S^♭ ⊗ N ⊗ 𝔪 (S^♭ the tilt of the test S), where N = O^♭/π and π = `pFlat`. If η killed
  -- all classes on the point, the line formula for Θ would make the cohomology of the point
  -- trivial; but it is N ⊗ 𝔪 = 𝔪/π𝔪, where π is not zero.
  let N : Type := OFlat ⧸ span {pFlat}
  have h_killed (x : N) : pFlat • x = 0 := by simp [N, Algebra.smul_def]
  have h_acyclic : IsAcyclicOnPerfect (moduleCoeff (almostCoeff N)) :=
    isAcyclicOnPerfect_almostCoeff h_killed
  let Θ : Theory (genericTestOver A) := tiltTheory A _ h_acyclic
  -- Non-zero elements of A are units in ℂ_ℓ, hence in the rings R[1/ℓ] of the ℓ-adic tests.
  have h_unit (a : A) (ha : a ≠ 0) : IsUnit (algebraMap A ℂ_[ℓ] a) := by simpa using ha
  refine hasLineFormula_of_lerayHirsch_ne_zero A
    (fun d a ha ↦ (h_unit a ha).map d.genericStructureMap)
    Θ.toTorsionCoeff fun h_eta ↦ ?_
  -- So all classes on the point are equal: their products with η agree, and the line formula for
  -- Θ makes the product with η injective.
  have h_line : IsLerayHirschBasis Θ.lineBasis (freeAb (onePointFunctor PadicTest)) :=
    hasLineFormula_tiltTheory ..
  have h_pt (v w : TotalH (freeAb (onePointFunctor PadicTest)) Θ.functor) : v = w :=
    single_injective false (h_line.injective ((h_eta v).trans (h_eta w).symm))
  -- The point is the functor Hom(O^♭, S^♭), as O^♭ is the initial O^♭-algebra.
  let O : CommAlg OFlat := of OFlat OFlat
  have h_point : IsCohomEquiv Θ.functor (freeAb.map (toUnit (PadicTest.tilt ⋙ reprBy O))) :=
    .of_bijective fun _ ↦ ⟨fun f f' _ ↦ ULift.down_injective (isInitialSelf.hom_ext f.down f'.down),
      fun _ ↦ ⟨ULift.up structureMap, rfl⟩⟩
  -- By acyclicity the cohomology of this functor is the value O^♭ ⊗ N ⊗ 𝔪 of the coefficient at
  -- O^♭; all its elements are equal.
  have h_classes : ∀ v w : TotalH (freeAb (PadicTest.tilt ⋙ reprBy O)) Θ.functor, v = w :=
    h_point.bijective_pullbackAlong.surjective.forall₂.mpr fun v w ↦ congrArg _ (h_pt v w)
  have h_sec (v w : moduleCoeff (almostCoeff N) O) : v = w :=
    (sectionEquiv _ O).injective ((h_acyclic O).bijective_totalH.injective (h_classes _ _))
  let π : MaxIdealFlat := ⟨pFlat, not_isUnit_pFlat⟩
  have h_zero : (1 : N) ⊗ₜ[OFlat] π = 0 :=
    (TensorProduct.lid OFlat _).symm.injective (ULift.up_injective (h_sec _ _))
  -- So π = π a with a in 𝔪; as π ≠ 0 this gives a = 1, which is not in 𝔪.
  have h_mem : π ∈ span {pFlat} • (⊤ : Submodule OFlat _) :=
    (LinearMap.ker_tensorProductMk _).le h_zero
  obtain ⟨a, ha_mem, ha_eq⟩ : ∃ a ∈ IsLocalRing.maximalIdeal OFlat, pFlat * a = pFlat := by
    rw [Submodule.mem_smul_top_iff, smul_eq_mul, mem_span_singleton_mul] at h_mem
    exact h_mem
  obtain rfl : a = 1 := mul_left_cancel₀ pFlat_ne_zero (ha_eq.trans (mul_one pFlat).symm)
  exact (IsLocalRing.mem_maximalIdeal 1).mp ha_mem isUnit_one

end New.Variety

end
end
end

/-!
# Charted varieties, and smooth base change from a valuation ring to its fraction field

From local charts to whole varieties, for cohomology computed on test rings.

* `New.Variety.algToBaseChange`, `New.Variety.isBijective_algToBaseChange`: the cohomology of the
  base change `Y_A` on all test rings agrees with that of `Y` on tests over `A`
  (`New.Variety.TestOver`).
* `New.Variety.ComparedTheory.mem_of_isClosedClass_of_isCharting`: a class of functors governed by
  `New.Variety.ComparedTheory.IsFiniteLerayHirsch` that contains the point contains every functor
  charted by pieces étale over tori (`New.Variety.IsCharting`).
* `New.Variety.isTestCohomEquiv_baseChangeTransition`: let `A` be a valuation ring of an algebraic
  closure `Ω` of `ℚ`, of residue characteristic `p ≠ ℓ`, and let `Y` be charted; then the mod `ℓ`
  cohomology of `Y_A` and of `Y_Ω` agree.

`D.IsFiniteLerayHirsch N` says that the cohomology of `N` with locally constant `ZMod ℓ`
coefficients is finite and computes that of the theory `D`. The functor
`relFreeAb (offClosedFiber X)` is `ℤ[X] / ℤ[U]`, where `U` consists of the points over the tests in
which the maximal ideal of `A` generates the unit ideal.

Notions from other files:
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to Z[Y], whose value at A is the
  free abelian group on Y(A).
* `New.Variety.IsClosedClass`: A closed class P of functors D → Ab: (a) P contains every zero
  functor N (written `𝟙 N = 0`); (b) for a short exact sequence 0 → X₁ → X₂ → X₃ → 0 with X₁ in P,
  the middle term X₂ is in P exactly when the quotient X₃ is.
* `New.Variety.geomPoints`: The functor of points of the base change `X ×_R Ω` of a scheme `X` over
  `R`.

## Relation to the literature

Known result: Smooth base change, with restriction to the generic fibre bijective on cohomology.
Here it is proved for schemes that are covered by finitely many pieces étale over tori and are not
assumed proper. The base is the valuation ring of a place above p of an algebraic closure of Q, the
coefficients are the constant F_ℓ with ℓ invertible, and the result is deduced from proper base
change and duality on products of projective lines. Source: Artin, SGA 4 Exp. XV 2.1, XVI 1.2
(1973); Stacks Project Tag 0EYQ; for the route through the class of the diagonal, Zavyalov, Poincaré
duality in abstract 6-functor formalisms (arXiv 2301.03821) and Li-Reinecke-Zavyalov (arXiv
2410.08200).
-/

@[expose] public section

namespace New.Variety

open CategoryTheory AlgebraicGeometry ObjectProperty Function Ideal nonZeroDivisors Algebra
  PrimeSpectrum CommRingCat Set Localization TensorProduct IsSmoothAt Comparison

section BaseChange

variable {R : CommRingCat} (A : Type) [CommRing A] [Algebra R A] (Y : Over (Spec R))

/-- For Y over R, the map sending a point of Y over R in an A-algebra c to the point of the base
change Y_A given by it and the structure map A → c. -/
noncomputable def algToBaseChange :
    algPointsOf A R Y ⟶ forget₂ (CommAlg A) CommRingCat ⋙ geomPoints R A Y where
  -- the point `y` together with the structure map `A → c`; the two are compatible over `R`
  app c :=
    ↾fun y ↦ ⟨(⟨y.1.1⟩, ⟨ofHom (algebraMap A c)⟩), congr(⟨$(Spec.homEquiv.eq_symm_apply.1 y.1.w)⟩)⟩
  naturality _ _ f := by
    ext
    exact baseChangeOf.ext rfl fun a ↦ (f.hom.commutes a).symm

/-- Let `Y` be over `Spec R` and `A` an `R`-algebra. For any coefficient `F` on test rings, the map
induced by `algToBaseChange`, from the cohomology of the base change `Y_A` to the cohomology of the
points of `Y` on tests over `A` (`New.Variety.TestOver`: test rings with an `A`-algebra structure),
is bijective in every degree. -/
lemma isBijective_algToBaseChange (F : AbFunctor TestRing) :
    (Comparison.restrict (TestOver.toTest A) F).IsBijective
      (freeAbMap (Y := testIncl ⋙ (geomPoints R A).obj Y)
        ((ι _).whiskerLeft (algToBaseChange A Y))) := by
  -- A point `y` of the base change over a test ring `c` includes a ring map `A → c`. The ring `c`
  -- with this algebra structure, with the point of `Y` given by `y`, is universal over `y`.
  refine Comparison.HasUniversalPoints.isBijective fun c y ↦ ?_
  -- The second component of `y`, a ring map `A → c`, makes `c` a test `B` over `A`.
  let algebra_c : Algebra A c.obj := y.val.2.down.hom'.toAlgebra
  let B : TestOver A := ⟨.of A c.obj, c.property⟩
  let x : (ι _ ⋙ algPointsOf A R Y).obj B :=
    ⟨Over.homMk _ (Spec.homEquiv.eq_symm_apply.2 congr($(y.property).down))⟩
  refine ⟨B, x, 𝟙 c, ?_, fun d z f hzf ↦ ?_, ?_⟩
  · -- The point `x` lies over `y`.
    refine Eq.trans ?_
      (ConcreteCategory.congr_hom ((testIncl ⋙ (geomPoints R A).obj Y).map_id c) y).symm
    rfl
  · -- The ring map of `f` is a map of `A`-algebras, by the second component of `hzf`.
    have h_commutes (a : A) : f.hom.hom (algebraMap A c.obj a) = algebraMap A d.obj a :=
      congr($(hzf).val.2.down.hom' a).symm
    let g : B ⟶ d := ⟨CommAlg.homOfRingHom _ h_commutes⟩
    -- It carries `x` to `z`, by the first component of `hzf`; it is unique, its ring map being
    -- `f`.
    refine ⟨g, ⟨congrArg _ (Over.OverMorphism.ext congr($(hzf).val.1.down).symm), rfl⟩, ?_⟩
    bound
  · -- On coefficients the comparison is the identity of `F c`.
    exact ConcreteCategory.bijective_of_isIso (F.map (𝟙 c))

end BaseChange

variable {C : Type _} [Category C] {ℓ : ℕ} {R : CommRingCat} {A : Type} [CommRing A]
  [Algebra R A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A} (D : ComparedTheory g)

/-- Let `A` be a valuation ring (`PreValuationRing`) and a `k`-algebra in which `ℓ` is a unit, `D` a
compared theory along `g`, and `P` a closed class of functors on tests over `A` that contains
`ℤ[Hom(A, -)]` and holds at `ℤ[Y]`, for each functor `Y` on tests over `A`, exactly when
`D.IsFiniteLerayHirsch` holds for `ℤ[Y] / ℤ[offClosedFibre Y]`. If the functor `X` on `k`-algebras
is charted by some `V` (`New.Variety.IsCharting`: `V` is Zariski locally all of `X`, and `ℤ[V]` lies
in every closed class containing `ℤ[Spec R]` for each chart `R` of `X` étale over a torus), then `P`
holds at `ℤ[X]`, restricted to tests over `A`. -/
lemma ComparedTheory.mem_of_isClosedClass_of_isCharting [PreValuationRing A]
    {P : TestOver A ⥤ Ab → Prop} (hP : IsClosedClass P)
    (h_iff : ∀ {X : TestOver A ⥤ Type 1},
      P (freeAb X) ↔ D.IsFiniteLerayHirsch (relFreeAb (offClosedFiber X)))
    {k : Type} [CommRing k] [Algebra k A] {X : CommAlg k ⥤ Type 1}
    (hV : ∃ V : Subfunctor X, IsCharting (k := k) V)
    (h_pt : P (freeAb (reprBy (TestOver.ofSelf A)))) :
    P (freeAb ((ι _ ⋙ restrictAlg k A) ⋙ X)) := by
  -- Reduce from `X` to `V`, from `V` to affine charts, from a chart to a finite cover by standard
  -- étale pieces; for these `ComparedTheory.isFiniteLerayHirsch_standard_etale` applies. `P` is
  -- local: by excision (`ComparedTheory.isFiniteLerayHirsch_iff_of_locally_bijective`) it passes
  -- from `U` to `Y` if `U` is locally all of `Y`.
  have of_cover {Y : TestOver A ⥤ Type 1} (U : Subfunctor Y)
      (hU : IsZariskiLocallyTop (ringOf (𝟭 _)) U)
      (h_mem : P (freeAb U.toFunctor)) : P (freeAb Y) := by
    -- A point of `U` lies in the range of `U.ι`.
    have h_cover : IsZariskiLocallyTop (ringOf (𝟭 _)) (.range U.ι ⊔ offClosedFiber Y) := by
      intro t y m hm
      refine (hU t y m hm).imp fun _ ↦ .imp_right fun h_in_U B f hf ↦ ?_
      simp [show Y.map f y ∈ U.obj B from h_in_U B f hf]
    have h_inj : IsZariskiLocallyTop (ringOf (𝟭 _)) (sameClassLocus U.ι (offClosedFiber Y)) :=
      isZariskiLocallyTop_sameClassLocus_of_injective _ _ fun _ ↦ Subtype.val_injective
    exact h_iff.2 ((D.isFiniteLerayHirsch_iff_of_locally_bijective U.ι h_cover h_inj).1
      (h_iff.1 h_mem))
  -- `V` is locally all of `X`, and `ℤ[V]` lies in every closed class that contains its charts.
  obtain ⟨V, hV_local, hV_charts⟩ := hV
  refine of_cover (V.whisker _) (hV_local.whisker _)
    (hV_charts _ (hP.comap (restrictAlong _)) fun chart _ ↦ ?_)
  -- On tests over `A` the chart is represented by its base change `B`, a smooth `A`-algebra.
  let B := CommAlgCat.of A (A ⊗[k] chart.coordRing)
  suffices hB : P (freeAb (testSpec A B)) from
    (hP.comap (restrictAlong (ι _))).freeAb_of_bijective
      (Y := restrictAlg k A ⋙ reprBy chart.coordRing) _
      (pointMap_algBaseChange_unit_bijective _) hB
  -- For each prime `x` there is `a x ∉ x` with `B[1/(a x)]` standard étale over the polynomial ring
  -- `S = MvPolynomial (Fin (d x)) A`; finitely many of the unit loci of the `a x` cover `Spec B`.
  -- `ha x : a x ∉ x`; `algebra_x`, `tower_x` make `Away (a x)` an algebra over the polynomial ring
  -- `MvPolynomial (Fin (d x)) A`, standard étale by `h_etale x`.
  choose a ha d algebra_x tower_x h_etale using fun x : PrimeSpectrum B ↦
    exists_isStandardEtale_mvPolynomial (R := A) (p := x.asIdeal)
  obtain ⟨s, hs⟩ :
      ∃ s : Finset (PrimeSpectrum B), ⋃ x ∈ s, (basicOpen (a x) : Set (PrimeSpectrum B)) = ⊤ :=
    CompactSpace.elim_nhds_subcover _ fun x ↦ isOpen_basicOpen.mem_nhds (ha x)
  -- Every `B[1/(a x * f)]` is again standard étale over `S`, so it is `(S[X]/E.f)[1/E.g]` for a
  -- standard étale pair `E`, and `S[X]` is again a polynomial ring over `A`.
  have h_piece (x : PrimeSpectrum B) (f : B) : P (freeAb (testUnitLocus (a x * f)).toFunctor) := by
    have h_etale_x : IsStandardEtale (MvPolynomial (Fin (d x)) A) (Away (a x)) := h_etale x
    obtain ⟨⟨E⟩⟩ :
        IsStandardEtale (MvPolynomial (Fin (d x)) A) (Away (algebraMap B (Away (a x)) f)) :=
      .of_isLocalizationAway (algebraMap B (Away (a x)) f)
    have h_std : P (freeAb (testUnitLocus (AdjoinRoot.mk E.f E.g)).toFunctor) :=
      h_iff.2 (D.isFiniteLerayHirsch_standard_etale
        (h_iff.1 (hP.freeAb_of_bijective _ pointMap_ofSelf_bijective h_pt)) _
        (MvPolynomial.finSuccEquiv A (d x)))
    -- Both unit loci are represented by localisations, and these are isomorphic over `A`.
    let iso := CommAlgCat.isoMk ((E.equivRing.trans E.equivAwayAdjoinRoot).restrictScalars A)
    let e : (testUnitLocus (AdjoinRoot.mk E.f E.g)).toFunctor ⟶
        (testUnitLocus (a x * f)).toFunctor :=
      (testUnitLocus.nonempty_iso_away _).some.inv ≫ (ι _).whiskerLeft (reprMap iso.hom) ≫
        (testUnitLocus.nonempty_iso_away _ _).some.hom
    exact (hP.iff_of_isIso (freeAb.map e)).1 h_std
  refine of_cover (⨆ x : s, testUnitLocus (a x)) (fun t φ m hm ↦ ?_) ?_
  · -- The prime of `B` below `m` misses `a x` for some `x ∈ s`.
    obtain ⟨x, hx, h_unit⟩ := iUnion₂_eq_univ_iff.1 hs (comap φ.down.hom'.toRingHom ⟨m, hm.isPrime⟩)
    refine ⟨_, h_unit, fun B' f hf ↦ ?_⟩
    -- After `f` the point lies in the unit locus of `a x`, one of the pieces of the union.
    aesop
  · -- Mayer–Vietoris (`IsClosedClass.freeAb_iSup`): the unit loci of the `a x * f` form a family
    -- that is closed under intersection, so `P` passes to finite unions.
    refine hP.freeAb_iSup (range fun y : PrimeSpectrum B × B ↦ testUnitLocus (a y.1 * y.2)) ?_ ?_
      fun x ↦ ⟨(x, 1), by simp⟩
    · exact Set.forall_mem_range.2 fun y ↦ h_piece y.1 y.2
    · rintro _ ⟨⟨x, f⟩, rfl⟩ _ ⟨⟨y, f'⟩, rfl⟩
      -- The unit locus of a product is the intersection of the unit loci.
      have h_inf : (testUnitLocus (a x * (f * a y * f')) : Subfunctor (testSpec A B)) =
          testUnitLocus (a x * f) ⊓ testUnitLocus (a y * f') := by
        simp [Subfunctor.ext_iff, funext_iff, Set.ext_iff, testUnitLocus, and_assoc]
      exact ⟨(x, f * a y * f'), h_inf⟩

/-- Let `A` be a valuation ring of `Ω` (a `ClosurePlace`) with the prime `p` in its maximal ideal.
Then `A` has rank one: for every nonzero `a ∈ A`, the maximal ideal lies in the radical of `(a)`. -/
private lemma maximalIdeal_le_radical_span {A : ClosurePlace} {p : ℕ} [Fact p.Prime]
    (hp : A.valuation p < 1) (a : A⁰) : IsLocalRing.maximalIdeal A ≤ radical (span {(a : A)}) := by
  -- `A` comes from `PadicAlgCl p`, whose valuation has rank one: a nonzero `a` divides a power of
  -- any nonunit.
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* PadicAlgCl p, (New.intQpBar p).comap j = A :=
    exists_comap_intQpBar_eq hp
  subst hj
  have h_int : (Valued.v.comap j).Integers ((New.intQpBar p).comap j) :=
    Valuation.integer.integers _
  -- A power of a value below one drops below any positive value. So a nonunit `b` (valuation
  -- below one) has a power `b ^ n` of valuation at most that of `a` (positive): `a ∣ b ^ n`.
  have h_pow_le {r s : NNReal} (hr : 0 < r) (hs : s < 1) : ∃ n : ℕ, s ^ n ≤ r :=
    (exists_pow_lt_of_lt_one hr hs).imp fun _ ↦ le_of_lt
  intro b
  simp +contextual [radical, mem_span_singleton, h_int.dvd_iff_le, isUnit_iff_dvd_one, h_pow_le]

/-- Let `A` be a valuation ring of `Ω` (a `ClosurePlace`) with the prime `p` in its maximal ideal,
and `ℓ` a unit in `A`. For a functor `X` on tests over `A`, restriction of the mod `ℓ` cohomology
from tests over `A` to tests over `Ω` (`New.Variety.TestOver.restrictScalars`) is bijective on
`ℤ[X]` exactly when `ℤ[X] / ℤ[offClosedFibre X]` has no cohomology. -/
private lemma isBijective_restrict_restrictScalars_iff {A : ClosurePlace} {p : ℕ} [Fact p.Prime]
    (hp : A.valuation p < 1) [InvertsPrime A ℓ] {X : TestOver A ⥤ Type 1} :
    (Comparison.restrict (TestOver.restrictScalars A Ω)
      (locConstAlong (𝟭 (TestOver A)))).IsBijective
        (𝟙 (TestOver.restrictScalars A Ω ⋙ freeAb X)) ↔
      ∀ n : ℕ,
        Subsingleton (H (relFreeAb (offClosedFiber X)) (locConstAlong (𝟭 (TestOver A))) n) := by
  let κ := Comparison.restrict (TestOver.restrictScalars A Ω) (locConstAlong (𝟭 (TestOver A)))
  -- In an `Ω`-algebra `p` is a unit, so every point of `X` over it lies in `offClosedFiber X`.
  let u : TestOver.restrictScalars A Ω ⋙ X ⟶ κ.functor ⋙ (offClosedFiber X).toFunctor :=
    { app c := ↾fun x ↦
        ⟨x, eq_top_of_isUnit_mem _ (mem_map_of_mem _ ((A.valuation_lt_one_iff p).2 hp))
          ((NeZero.ne (p : Ω)).isUnit.map (algebraMap Ω c.obj))⟩ }
  -- Conversely, if a test `c` carries a point of `offClosedFiber X`, nonzero elements of `A` are
  -- units in `c` (rank one), so `A → c` extends to `Ω` in exactly one way;
  -- `hasUniversalPoints_structurePt` gives the test `B` over `Ω` that is universal under `c`.
  have h_univ : κ.HasUniversalPoints u := fun c y ↦ by
    have h_unit (a : A⁰) : IsUnit (algebraMap A c.obj a) := by
      -- (the ring of `c` appears once as `c` and once as `(TestOver.toTest A).obj c`)
      have h := radical_eq_top.1 (eq_top_mono
        ((map_mono (maximalIdeal_le_radical_span hp a)).trans (map_radical_le _)) y.property)
      rw [← span_singleton_eq_top, ← Set.image_singleton (f := algebraMap A c.obj), ← map_span]
      exact h
    obtain ⟨B, x, s, -, h_uniq, h_bij⟩ :=
      hasUniversalPoints_structurePt A Ω c
        ⟨⟨CommAlg.homOfRingHom _ (IsLocalization.lift_eq h_unit)⟩⟩
    refine ⟨B, _, s, rfl, fun d z f h_zf ↦ ?_, h_bij⟩
    -- Two `A`-algebra maps out of the fraction field `Ω` agree, so the lift followed by `f` is the
    -- structure map of `d`; `g` is the factorisation that this gives.
    obtain ⟨g, ⟨-, hg_comp⟩, hg_uniq⟩ :=
      h_uniq d ⟨⟩ f congr(⟨⟨CommAlgCat.ofHom $(IsLocalization.algHom_ext A⁰ (by ext))⟩⟩)
    -- `h_zf` says that `z` is the image of `y` under `f`.
    obtain rfl : z = X.map f y.val := congrArg Subtype.val h_zf
    refine ⟨g, ⟨?_, hg_comp⟩, fun g' ⟨_, hg'_comp⟩ ↦ hg_uniq g' ⟨rfl, hg'_comp⟩⟩
    -- `X.map g (X.map s y) = X.map (s ≫ g) y = X.map f y = z`. What is left holds by definition:
    -- `(TestOver.restrictScalars A Ω ⋙ X).map g` is `X.map` of
    -- `(Comparison.restrict _ _).functor.map g`.
    rw [← hg_comp, X.map_comp_apply]
    rfl
  -- So `κ` is bijective on `X` iff `offClosedFiber X ⊆ X` is an equivalence iff the quotient is
  -- acyclic.
  calc κ.IsBijective (𝟙 (κ.functor ⋙ freeAb X))
    _ ↔ IsCohomEquiv (locConstAlong (𝟭 _)) (freeAb.map (offClosedFiber X).ι) := by
      refine (h_univ.isBijective.trans_iff (c := .id _) ?_).trans isCohomEquiv_iff_isBijective.symm
      -- `u` followed by the inclusion of `offClosedFiber X` is the identity
      exact freeAb.hom_ext fun _ _ ↦ rfl
    _ ↔ ∀ n, Subsingleton (H (relFreeAb (offClosedFiber X)) (locConstAlong (𝟭 _)) n) :=
      relFreeAb.isCohomEquiv_iff_subsingleton_rel _

/-- Let `ℓ` be prime and `A` a valuation ring of the algebraic closure `Ω` of `ℚ` (a `ClosurePlace`)
and an `R`-algebra, with a prime `p` in its maximal ideal and `ℓ` a unit. Suppose `Y` is charted
over `R` (`IsCharted`: its functor of points on `R`-algebras has a subfunctor `V` with
`IsCharting V`). Then pull-back `Hⁿ(Y_A, ℤ/ℓ) → Hⁿ(Y_Ω, ℤ/ℓ)` along `Y_Ω → Y_A` is bijective for all
`n`, where cohomology is computed on test rings with locally constant coefficients. -/
lemma isTestCohomEquiv_baseChangeTransition [ThePrime ℓ]
    {A : ClosurePlace} {p : ℕ} [Fact p.Prime] (hp : A.valuation p < 1)
    (hℓ : IsUnit (ℓ : A)) [Algebra R A] (Y : Over (Spec R)) [IsCharted Y R] :
    IsTestCohomEquiv ⟨ZMod ℓ⟩ (Y := geomPoints R A Y)
      (baseChangeTransition (pointsToBase Y.hom) (ofHom A.subtype) rfl) := by
  -- Compare the cohomology of tests over `A` with that of tests over `Ω` (the comparison `κ`). The
  -- functors on which `κ` is bijective form a class to which
  -- `ComparedTheory.mem_of_isClosedClass_of_isCharting` applies; it contains the point, hence `Y`.
  -- Then `isBijective_algToBaseChange` translates back to the base changes of `Y`.
  -- `h_inverts`, `algebra_Ω` and `h_faithful` serve as instances (for the theory of locally
  -- constant functions and for the line formula).
  have h_inverts : InvertsPrime A ℓ := .mk hℓ
  -- The line formula holds because `A ⊆ Ω` embeds in `ℂ_[ℓ]`.
  let algebra_Ω : Algebra Ω ℂ_[ℓ] :=
    ((algebraMap (PadicAlgCl ℓ) ℂ_[ℓ]).comp Classical.ofNonempty).toAlgebra
  have h_faithful : FaithfulSMul A ℂ_[ℓ] := A.faithfulSMul
  have h_line : (Theory.locallyConstant (A := A)).HasLineFormula := hasLineFormula_locallyConstant A
  -- With no comparison maps, `D.IsFiniteLerayHirsch N` says that `N` has no cohomology: the map
  -- from the empty direct sum to the cohomology is bijective.
  let D : ComparedTheory (𝟭 (TestOver A)) := ⟨Theory.locallyConstant, Empty, nofun, h_line, h_line⟩
  have h_acyclic (N : AbFunctor (TestOver A)) :
      (∀ n, Subsingleton (H N (locConstAlong (𝟭 _)) n)) ↔ D.IsFiniteLerayHirsch N := by
    constructor
    · -- The total cohomology is then trivial, so the empty direct sum maps bijectively onto it.
      intro h_sub
      exact ⟨Unique.bijective (B := TotalH N (locConstAlong _)), .of_subsingleton⟩
    · -- The empty direct sum maps onto the total cohomology, so it and each degree are trivial.
      rintro ⟨h_bij, -⟩ n
      have h_total : Subsingleton (TotalH N (locConstAlong (𝟭 _))) := h_bij.surjective.subsingleton
      exact (DirectSum.of_injective n).subsingleton
  let κ := Comparison.restrict (TestOver.restrictScalars A Ω) (locConstAlong (𝟭 _))
  have h_iff {X : TestOver A ⥤ Type 1} :
      κ.IsBijective (𝟙 (κ.functor ⋙ freeAb X)) ↔ D.IsFiniteLerayHirsch
        (relFreeAb (offClosedFiber X)) :=
    (isBijective_restrict_restrictScalars_iff hp).trans (h_acyclic _)
  -- The point: both `A` and `Ω` are domains, so both sides are the constants `ZMod ℓ`.
  have h_pt : κ.IsBijective (freeAbMap (𝟙 (κ.functor ⋙ reprBy (TestOver.ofSelf A)))) := by
    refine κ.isBijective_of_repr ⟨⟨structureMap⟩⟩
      (fun c ↦ ((pointMap_ofSelf_bijective _).of_comp_iff' _).1 (pointMap_ofSelf_bijective c)) ?_
    exact ((bijective_const_of_isDomain (B := .of A)).of_comp_iff _).1
      (bijective_const_of_isDomain (B := .of Ω))
  have h_cl : IsClosedClass fun N ↦ κ.IsBijective (𝟙 (κ.functor ⋙ N)) :=
    (κ.devissage (𝟭 _) (𝟙 _)).isClosedClass
  have h_Y : κ.IsBijective (𝟙 (κ.functor ⋙ freeAb
    ((ι _ ⋙ restrictAlg R A) ⋙ algPointsOf R R Y))) := by
    refine D.mem_of_isClosedClass_of_isCharting h_cl h_iff IsCharted.exists_isCharting ?_
    -- `freeAb` maps the identity to the identity.
    rwa [freeAbMap, freeAb.map_id] at h_pt
  -- Both `H(Y_A) → H(Y on tests over A) → H(Y on tests over Ω)` and `H(Y_Ω) → H(Y on tests over Ω)`
  -- are bijective, hence so is `H(Y_A) → H(Y_Ω)`.
  have h_A := isBijective_algToBaseChange A Y (locConstCoeff ⟨ZMod ℓ⟩)
  let algebra_R_Ω : Algebra R Ω := .compHom Ω (algebraMap R A)
  have h_Ω := isBijective_algToBaseChange Ω Y (locConstCoeff ⟨ZMod ℓ⟩)
  -- (`(… :)` elaborates the composite `H(Y_A) → H(Y on tests over Ω)` on its own.)
  refine IsBijective.eqv ((h_Ω.trans_iff ?_).1 (h_A.trans h_Y rfl :))
  exact freeAb.hom_ext fun _ _ ↦ rfl

end New.Variety
